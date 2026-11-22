import Mazurkiewicz.Condpor.Rmw.SC

/-!
# Read-modify-write accesses: the assumptions for the symbolic model

The algorithm runs with the model `M.sym S` (`M`-consistency and
satisfiability of the constraints). Reads and writes do not change the
constraints of a graph, so the two assumptions on `M` (`ExtensibleX`,
`ExclExtensible`) give the corresponding statements for `M.sym S`; for a
constraint evaluation one of the two outcomes is satisfiable.
-/

namespace Condpor

open Program

variable {P : XProgram} {M : Model} {S : Solver}

/-- A new read from the last write of its location. -/
theorem ExtensibleX.sym_ext_read (hM : ExtensibleX P M) {G : Graph} {e : TEv} {x : Loc}
    (hG : G.Wf) (hE : P.toProgram.Exec G) (hc : (M.sym S).cons G)
    (he : e ∈ P.toProgram.avail G) (hact : e.act = .read x) :
    (M.sym S).cons (G.addRead e (G.maxWrite x)) := by
  obtain ⟨hc1, hc2⟩ := Model.sym_cons_iff.mp hc
  refine Model.sym_cons_iff.mpr ⟨hM.ext_read G e x hG hE hc1 he hact, ?_⟩
  rw [Graph.F_addRead hG _ (hG.not_mem_of_idx_eq_cnt (idx_eq_of_mem_avail he))]
  exact hc2

/-- A new write that is not exclusive, placed last. -/
theorem ExtensibleX.sym_ext_write (hM : ExtensibleX P M) {G : Graph} {e : TEv}
    (hG : G.Wf) (hE : P.toProgram.Exec G) (hc : (M.sym S).cons G)
    (he : e ∈ P.toProgram.avail G) (hact : e.IsWrite)
    (hnx : P.ex e.tid (G.trace e.tid) = false) :
    (M.sym S).cons (G.addWrite e (G.maxWrite e.loc)) := by
  obtain ⟨hc1, hc2⟩ := Model.sym_cons_iff.mp hc
  refine Model.sym_cons_iff.mpr ⟨hM.ext_write G e hG hE hc1 he hact hnx, ?_⟩
  rw [Graph.F_addWrite hG _ (hG.not_mem_of_idx_eq_cnt (idx_eq_of_mem_avail he))]
  exact hc2

/-- A new exclusive write whose read reads from the last write, placed last. -/
theorem ExtensibleX.sym_ext_wex (hM : ExtensibleX P M) {G : Graph} {r e : TEv}
    (hG : G.Wf) (hE : P.toProgram.Exec G) (hc : (M.sym S).cons G) (hm : P.Mate G r e)
    (hrf : G.rf r = some (G.maxWrite e.loc)) :
    (M.sym S).cons (G.addWrite e (G.maxWrite e.loc)) := by
  obtain ⟨hc1, hc2⟩ := Model.sym_cons_iff.mp hc
  refine Model.sym_cons_iff.mpr ⟨hM.ext_wex G r e hG hE hc1 hm hrf, ?_⟩
  rw [Graph.F_addWrite hG _ (hG.not_mem_of_idx_eq_cnt (idx_eq_of_mem_avail hm.2.2.2.1))]
  exact hc2

/-- A new local event without outcome (generation, block, error). -/
theorem ExtensibleX.sym_ext_loc_none (hM : ExtensibleX P M) {G : Graph} {e : TEv}
    (hG : G.Wf) (hE : P.toProgram.Exec G) (hc : (M.sym S).cons G)
    (he : e ∈ P.toProgram.avail G) (hact : e.IsLocal) (hnc : ¬ e.IsCons) :
    (M.sym S).cons (G.addLoc e none) := by
  obtain ⟨hc1, hc2⟩ := Model.sym_cons_iff.mp hc
  refine Model.sym_cons_iff.mpr ⟨hM.ext_loc G e none hG hE hc1 he hact (by simp [hnc]), ?_⟩
  rw [Graph.F_addLoc_none (hG.not_mem_of_idx_eq_cnt (idx_eq_of_mem_avail he))]
  exact hc2

/-- For a constraint evaluation, one of the two outcomes is consistent. -/
theorem ExtensibleX.sym_ext_cons (hM : ExtensibleX P M) {G : Graph} {e : TEv} {φ : SExpr}
    (hG : G.Wf) (hE : P.toProgram.Exec G) (hc : (M.sym S).cons G)
    (he : e ∈ P.toProgram.avail G) (hact : e.act = .cons φ) :
    ∃ b, (M.sym S).cons (G.addLoc e (some b)) := by
  obtain ⟨hc1, hc2⟩ := Model.sym_cons_iff.mp hc
  have hne := hG.not_mem_of_idx_eq_cnt (idx_eq_of_mem_avail he)
  have hl : e.IsLocal := by simp [TEv.IsLocal, hact, Act.IsLocal]
  have hcs : e.IsCons := by simp [TEv.IsCons, hact, Act.IsCons]
  rcases S.sat_split φ hc2 with h | h
  · refine ⟨true, Model.sym_cons_iff.mpr ⟨hM.ext_loc G e _ hG hE hc1 he hl (by simp [hcs]), ?_⟩⟩
    rw [Graph.F_addLoc_cons true hne hact]
    exact h
  · refine ⟨false, Model.sym_cons_iff.mpr ⟨hM.ext_loc G e _ hG hE hc1 he hl (by simp [hcs]), ?_⟩⟩
    rw [Graph.F_addLoc_cons false hne hact]
    exact h

/-- Exclusive-write extensibility of `M` gives that of `M.sym S`. -/
theorem ExclExtensible.sym (hM : ExclExtensible P M) : ExclExtensible P (M.sym S) := by
  intro G r e s hG hE hc hm hrf hfree
  obtain ⟨hc1, hc2⟩ := Model.sym_cons_iff.mp hc
  obtain ⟨wp, hwp, hcons⟩ := hM G r e s hG hE hc1 hm hrf hfree
  refine ⟨wp, hwp, Model.sym_cons_iff.mpr ⟨hcons, ?_⟩⟩
  rw [Graph.F_addWrite hG _ (hG.not_mem_of_idx_eq_cnt (idx_eq_of_mem_avail hm.2.2.2.1))]
  exact hc2

/-- `SC` with atomicity and constraints is exclusive-write extensible. -/
theorem SC.exclExtensible_sym (P : XProgram) (S : Solver) :
    ExclExtensible P ((Model.atomic P SC).sym S) :=
  (SC.exclExtensible P).sym

end Condpor
