import Mazurkiewicz.Condpor.Rf.Complete

/-!
# The reads-from version: Theorem 5(b) and the explorer

* `ReachR.reaches_full`: every reached configuration reaches a full one.
* `exploreR`: the list of graphs that the reads-from version reports.
  `exploreR_spec`: for a bounded program and an extensible model, it lists,
  without repetition, exactly the canonical forms of the well-formed full
  executions that are consistent for some coherence order: one graph for
  every reads-from class.
* `mem_exploreR_iff_canon`: these are the canonical forms of the graphs that
  the explorer of `Explore.lean` lists; `exploreR_length_le`.
-/

namespace Condpor

open Program

variable {P : Program} {M : Model} {S : Solver} {τ : TieBreak S} {γ : CoChoice (M.sym S)}

/-! ### Theorem 5(b) -/

theorem canonCo_insert_of_not_write {E : Finset TEv} {e : TEv} (h : ¬ e.IsWrite) :
    canonCo (insert e E) = canonCo E := by
  funext x
  refine canonCo_congr (fun q hq => ?_)
  rw [Finset.mem_insert]
  constructor
  · rintro (rfl | hq')
    · obtain ⟨v, hv⟩ := hq
      exact absurd (by simp [TEv.IsWrite, hv, Act.IsWrite]) h
    · exact hq'
  · exact Or.inr

/-- From a reached configuration that is not full the algorithm takes a
non-revisit step. -/
theorem ReachR.exists_step (hM : M.Extensible) {c : Config}
    (hc : ReachR P (M.sym S) γ τ c) (hnf : ¬ P.Full c.abs) :
    ∃ e c', StepR P (M.sym S) γ τ c e .nr c' := by
  obtain ⟨hw, -, hcan, hcc, -⟩ := hc.sound
  obtain ⟨co, hWc, hMc⟩ := hcc
  obtain ⟨a, ha, -⟩ := exists_unique_isNext hnf
  have hidx := idx_eq_of_mem_avail ha.1
  have hidx' : a.idx = (c.abs.withCo co).cnt a.tid := hidx
  have hne : a ∉ c.abs.events := hw.1.not_mem_of_idx_eq_cnt hidx
  have hcan' : c.abs.co = canonCo c.abs.events := hcan
  rcases a.act.isRead_or_isWrite_or_isLocal with hk | hk | hk
  · have hact := TEv.IsRead.exists_act hk
    have hwt := Graph.maxWrite_isWriteTo hWc a.loc
    refine ⟨a, _, StepR.nr (StepL.read ⟨co, hWc, hMc⟩ ha hact hwt ?_) ?_⟩
    · rw [Config.addRead_abs]
      exact ⟨co, hWc.addRead hidx' hact hwt, Model.sym_ext_read hM hWc hMc hidx' hact⟩
    · rw [Config.addRead_abs]
      change c.abs.co = canonCo (insert a c.abs.events)
      rw [canonCo_insert_of_not_write (fun h => a.act.not_isRead_and_isWrite ⟨hk, h⟩)]
      exact hcan'
  · -- the canonical place of the new write
    have hXW : (c.abs.addWrite a .init).canon.Wf :=
      (hw.1.addWrite (wp := .init) hidx hk trivial).canon
    have haX : a ∈ (c.abs.addWrite a .init).canon.events := Finset.mem_insert_self _ _
    obtain ⟨wp, hwp, hco⟩ := Graph.remove_addWrite_co hXW haX hk
    have hrem : (c.abs.addWrite a .init).canon.remove {a} = c.abs := by
      change (c.abs.addWrite a .init).canon.restrict _ = _
      rw [Graph.canon_restrict]
      have : (c.abs.addWrite a .init).events \ {a} = c.abs.events := by
        change insert a c.abs.events \ {a} = c.abs.events
        rw [Finset.sdiff_singleton_eq_erase, Finset.erase_insert hne]
      change ((c.abs.addWrite a .init).restrict ((c.abs.addWrite a .init).events \ {a})).canon = _
      rw [this, Graph.restrict_addWrite hw.1 hne]
      exact hcan.canon_eq
    rw [hrem] at hwp hco
    have hX : c.abs.addWrite a wp = (c.abs.addWrite a .init).canon := by
      apply Graph.ext
      · rfl
      · rfl
      · rfl
      · exact hco
      · rfl
    have hwm := Graph.maxWrite_isWriteTo hWc a.loc
    have hcons : (M.sym S).rf.cons (c.abs.addWrite a wp) := by
      refine ⟨((c.abs.withCo co).addWrite a ((c.abs.withCo co).maxWrite a.loc)).co, ?_, ?_⟩
      · have h := hWc.addWrite hidx' hk hwm
        exact h
      · have h := Model.sym_ext_write hM hWc hMc hidx' hk
        exact h
    refine ⟨a, _, StepR.nr (StepL.write ⟨co, hWc, hMc⟩ ha hk hwp ?_) ?_⟩
    · rw [Config.addWrite_abs]
      exact hcons
    · rw [Config.addWrite_abs, hX]
      exact Graph.canon_isCanon _
  · have hcanL : ∀ o, (c.addLoc a o).abs.IsCanon := by
      intro o
      rw [Config.addLoc_abs]
      change c.abs.co = canonCo (insert a c.abs.events)
      rw [canonCo_insert_of_not_write hk.not_isWrite]
      exact hcan'
    by_cases hcs : a.IsCons
    · obtain ⟨φ, hφ⟩ := TEv.IsCons.exists_act hcs
      obtain ⟨b, hb⟩ := Model.sym_ext_cons hM hWc hMc hidx' hφ
      refine ⟨a, _, StepR.nr (StepL.sym (b := b) ⟨co, hWc, hMc⟩ ha hcs ?_) (hcanL _)⟩
      rw [Config.addLoc_abs]
      exact ⟨co, hWc.addLoc hidx' hk (by simp [hcs]), hb⟩
    · refine ⟨a, _, StepR.nr (StepL.loc ⟨co, hWc, hMc⟩ ha hk hcs ?_) (hcanL _)⟩
      rw [Config.addLoc_abs]
      exact ⟨co, hWc.addLoc hidx' hk (by simp [hcs]),
        Model.sym_ext_loc_none hM hWc hMc hidx' hk hcs⟩

/-- Theorem 5(b) for the reads-from version: every reached configuration of a
bounded program reaches a full one. -/
theorem ReachR.reaches_full {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible) {c : Config}
    (hc : ReachR P (M.sym S) γ τ c) :
    ∃ c', Relation.ReflTransGen (StepRf P (M.sym S) γ τ) c c' ∧ P.Full c'.abs := by
  have key : ∀ k (c : Config), ReachR P (M.sym S) γ τ c →
      n * P.threads.length - c.abs.events.card ≤ k →
      ∃ c', Relation.ReflTransGen (StepRf P (M.sym S) γ τ) c c' ∧ P.Full c'.abs := by
    intro k
    induction k with
    | zero =>
      intro c hc hk
      by_cases hf : P.Full c.abs
      · exact ⟨c, .refl, hf⟩
      · obtain ⟨e, c1, hs⟩ := hc.exists_step hM hf
        have hc1 : ReachR P (M.sym S) γ τ c1 := Relation.ReflTransGen.tail hc ⟨e, .nr, hs⟩
        have h1 := hc1.card_le hn
        have h2 := hs.nr_inv.1.card_nr hc.sound.1
        omega
    | succ k ih =>
      intro c hc hk
      by_cases hf : P.Full c.abs
      · exact ⟨c, .refl, hf⟩
      · obtain ⟨e, c1, hs⟩ := hc.exists_step hM hf
        have hc1 : ReachR P (M.sym S) γ τ c1 := Relation.ReflTransGen.tail hc ⟨e, .nr, hs⟩
        have h2 := hs.nr_inv.1.card_nr hc.sound.1
        obtain ⟨c', hc', hf'⟩ := ih c1 hc1 (by omega)
        exact ⟨c', Relation.ReflTransGen.head ⟨e, .nr, hs⟩ hc', hf'⟩
  exact key _ c hc (Nat.le_refl _)

/-! ### The explorer -/

/-- The configurations that `Visit` is called with from `c`: the canonical
forms of the choices of Algorithm 1 that are steps of the reads-from
version. The consistency check of `Visit` is the premise `M.rf.cons` of each
rule of `StepR`. -/
noncomputable def succsR (P : Program) (M : Model) (γ : CoChoice M) {S : Solver}
    (τ : TieBreak S) (c : Config) : List Config :=
  open Classical in
  ((cands P c).map Config.canon).dedup.filter (fun c' => decide (StepRf P M γ τ c c'))

/-- The graphs reported by `Visit` started at `c`, following the calls to
depth `f`. -/
noncomputable def exploreFromR (P : Program) (M : Model) (γ : CoChoice M) {S : Solver}
    (τ : TieBreak S) : ℕ → Config → List Graph
  | 0, _ => []
  | f + 1, c =>
    open Classical in
    if M.rf.cons c.abs then
      if P.nextC c = none then [c.abs] else (succsR P M γ τ c).flatMap (exploreFromR P M γ τ f)
    else []

/-- The graphs that the reads-from version reports for `P` under `M`, where
`n` bounds the number of events of a thread. -/
noncomputable def exploreR (P : Program) (M : Model) (γ : CoChoice M) {S : Solver}
    (τ : TieBreak S) (n : ℕ) : List Graph :=
  exploreFromR P M γ τ (P.bound n + 1) (Config.init P.mem)

theorem Config.canon_eq_of_isCanon {c : Config} (h : c.abs.IsCanon) : c.canon = c := by
  cases c
  simp only [Config.canon, Config.withCo]
  congr 1
  exact h.symm

theorem StepRf.mem_cands {c c' : Config} (hc : c.Wf) (h : StepRf P (M.sym S) γ τ c c') :
    c' ∈ (cands P c).map Config.canon := by
  obtain ⟨e, k, hs⟩ := h
  rw [List.mem_map]
  cases k with
  | nr =>
    obtain ⟨hl, hcan⟩ := hs.nr_inv
    exact ⟨c', mem_cands_of_step hc ⟨e, .nr, hl⟩, Config.canon_eq_of_isCanon hcan⟩
  | rv r =>
    obtain ⟨rfl, -, hnext, hw, hr, hract, -⟩ := hs.rv_inv
    refine ⟨c.revisit r e .init, ?_, rfl⟩
    unfold cands
    rw [(nextC_eq_some_iff hc).mpr hnext]
    obtain ⟨v, hv⟩ := hw.exists_act
    simp only [hv]
    exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨r, List.mem_filter.mpr ⟨hr, TEv.readsLoc_iff.mpr hract⟩,
        List.mem_map_of_mem (mem_writesOf.mpr trivial)⟩)

theorem mem_succsR {c c' : Config} (hc : c.Wf) :
    c' ∈ succsR P (M.sym S) γ τ c ↔ StepRf P (M.sym S) γ τ c c' := by
  classical
  unfold succsR
  rw [List.mem_filter, List.mem_dedup]
  constructor
  · rintro ⟨-, h⟩
    exact of_decide_eq_true h
  · intro h
    exact ⟨h.mem_cands hc, decide_eq_true h⟩

theorem succsR_nodup (c : Config) : (succsR P (M.sym S) γ τ c).Nodup := by
  classical
  exact (List.nodup_dedup _).filter _

theorem StepRf.not_full {c c' : Config} (h : StepRf P (M.sym S) γ τ c c') :
    ¬ P.Full c.abs := by
  obtain ⟨e, k, hs⟩ := h
  have hnext : P.IsNext c.abs e := by
    cases k with
    | nr => exact hs.nr_inv.1.nr_inv.2.1
    | rv r => exact hs.rv_inv.2.2.1
  intro hf
  rw [Full] at hf
  have := hnext.1
  rw [hf] at this
  cases this

/-- The bound on the length of the runs. -/
theorem terminatesR_bound {n : ℕ} (hn : P.Bounded n) (p : List Config) (c : Config)
    (hp : Maz.Path (StepRf P (M.sym S) γ τ) (Config.init P.mem) p c) :
    p.length ≤ P.bound n := by
  unfold Program.bound
  obtain ⟨p', rw, hp', hl⟩ := lift_pathR hp ∅
  rw [← hl]
  refine Maz.Path.length_le_of_bounded_measure (measureRW (n * P.threads.length)) _ ?_ ?_ hp'
  · intro x y hx hs
    exact StepRWR.measure_lt (K := n * P.threads.length) hx
      ((ReachRWR.reach hx).card_le hn) hs
  · intro x hx
    have hD1 := (ReachRWR.a21 hx).1
    have hcard := (ReachRWR.reach hx).card_le hn
    have hrw : x.2.card ≤ x.1.abs.events.card := by
      apply Finset.card_le_card
      intro w hw
      exact List.mem_toFinset.mpr (hD1 w hw)
    unfold measureRW
    have := Nat.mul_le_mul_right (n * P.threads.length + 1) (le_trans hrw hcard)
    omega

theorem mem_exploreFromR {c : Config} (hc : ReachR P (M.sym S) γ τ c) (f : ℕ) (G : Graph) :
    G ∈ exploreFromR P (M.sym S) γ τ f c ↔
      ∃ p c', Maz.Path (StepRf P (M.sym S) γ τ) c p c' ∧ p.length < f ∧ P.Full c'.abs ∧
        c'.abs = G := by
  induction f generalizing c with
  | zero =>
    simp only [exploreFromR, List.not_mem_nil, false_iff]
    rintro ⟨p, c', -, h, -⟩
    exact Nat.not_lt_zero _ h
  | succ f ih =>
    have hcw := hc.sound.1
    unfold exploreFromR
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc.sound.2.2.2.1)]
    by_cases hnx : P.nextC c = none
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hnx), List.mem_singleton]
      have hfull := (nextC_eq_none_iff hcw).mp hnx
      constructor
      · rintro rfl
        exact ⟨[], c, Maz.Path.nil c, Nat.succ_pos _, hfull, rfl⟩
      · rintro ⟨p, c', hp, -, -, rfl⟩
        cases hp with
        | nil => rfl
        | cons hstep _ => exact absurd hfull hstep.not_full
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hnx), List.mem_flatMap]
      constructor
      · rintro ⟨c1, hc1, hG⟩
        have hstep := (mem_succsR hcw).mp hc1
        obtain ⟨p, c', hp, hl, hfull, rfl⟩ := (ih (hc.tail hstep)).mp hG
        exact ⟨c1 :: p, c', Maz.Path.cons hstep hp, Nat.succ_lt_succ hl, hfull, rfl⟩
      · rintro ⟨p, c', hp, hl, hfull, rfl⟩
        cases hp with
        | nil => exact absurd ((nextC_eq_none_iff hcw).mpr hfull) hnx
        | @cons _ c1 _ p' hstep hrest =>
          exact ⟨c1, (mem_succsR hcw).mpr hstep,
            (ih (hc.tail hstep)).mpr ⟨p', c', hrest, Nat.lt_of_succ_lt_succ hl, hfull, rfl⟩⟩

theorem exploreFromR_nodup {c : Config} (hc : ReachR P (M.sym S) γ τ c) (f : ℕ) :
    (exploreFromR P (M.sym S) γ τ f c).Nodup := by
  induction f generalizing c with
  | zero => exact List.nodup_nil
  | succ f ih =>
    have hcw := hc.sound.1
    unfold exploreFromR
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc.sound.2.2.2.1)]
    by_cases hnx : P.nextC c = none
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hnx)]
      exact List.nodup_singleton _
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hnx)]
      refine List.nodup_flatMap.mpr
        ⟨fun c1 hc1 => ih (hc.tail ((mem_succsR hcw).mp hc1)), ?_⟩
      refine List.Pairwise.imp_of_mem (fun {c1 c2} h1 h2 hne => ?_) (succsR_nodup c)
      intro G hG1 hG2
      have hs1 := (mem_succsR hcw).mp h1
      have hs2 := (mem_succsR hcw).mp h2
      obtain ⟨p1, c1', hp1, -, -, hG1'⟩ := (mem_exploreFromR (hc.tail hs1) f G).mp hG1
      obtain ⟨p2, c2', hp2, -, -, hG2'⟩ := (mem_exploreFromR (hc.tail hs2) f G).mp hG2
      obtain ⟨q0, hq0⟩ := Maz.Path.of_reflTransGen hc
      have hfull1 := hq0.append (Maz.Path.cons hs1 hp1)
      have hfull2 := hq0.append (Maz.Path.cons hs2 hp2)
      have heq := path_uniqueR hfull1 hfull2 (hG1'.trans hG2'.symm)
      exact hne (List.cons.inj (List.append_cancel_left heq)).1

/-- The specification of the explorer of the reads-from version: for a
bounded program and a maximally extensible model, `exploreR` lists, without
repetition, exactly the canonical graphs that are well-formed full executions
of the program, consistent for some coherence order. -/
theorem exploreR_spec {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible) :
    (exploreR P (M.sym S) γ τ n).Nodup ∧
      ∀ G, G ∈ exploreR P (M.sym S) γ τ n ↔
        G.Wf ∧ P.Exec G ∧ (M.sym S).rf.cons G ∧ P.Full G ∧ G.IsCanon := by
  have h0 : ReachR P (M.sym S) γ τ (Config.init P.mem) := Relation.ReflTransGen.refl
  refine ⟨exploreFromR_nodup h0 _, fun G => ?_⟩
  unfold exploreR
  rw [mem_exploreFromR h0]
  constructor
  · rintro ⟨p, c', hp, -, hfull, rfl⟩
    obtain ⟨hw, -, hcan, hc, hE⟩ := (ReachR.sound (hp.reflTransGen : ReachR P (M.sym S) γ τ c'))
    exact ⟨hw.1, hE, hc, hfull, hcan⟩
  · rintro ⟨hW, hE, hc, hfull, hcan⟩
    obtain ⟨c, hreach, rfl⟩ := completeR_canon (γ := γ) (τ := τ) hn hM hW hE hcan hc hfull
    obtain ⟨p, hp⟩ := Maz.Path.of_reflTransGen hreach
    exact ⟨p, c, hp, Nat.lt_succ_of_le (terminatesR_bound hn p c hp), hfull, rfl⟩

/-- One graph for every reads-from class: every well-formed full execution
that is consistent for some coherence order agrees with exactly one listed
graph on everything but the coherence order. -/
theorem exploreR_classes {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible) {G : Graph}
    (hW : G.Wf) (hE : P.Exec G) (hc : (M.sym S).rf.cons G) (hF : P.Full G) :
    ∃! G', G' ∈ exploreR P (M.sym S) γ τ n ∧ G'.RfEq G := by
  have hspec := (exploreR_spec (γ := γ) (τ := τ) hn hM).2
  refine ⟨G.canon, ⟨(hspec _).mpr ⟨hW.canon, (Program.exec_withCo P _ _).mpr hE,
    (Model.rf_cons_congr (Graph.rfEq_canon G)).mp hc, hF, Graph.canon_isCanon G⟩,
    ⟨rfl, rfl, rfl, rfl⟩⟩, ?_⟩
  rintro G' ⟨hG', hrf⟩
  rw [← ((hspec G').mp hG').2.2.2.2.canon_eq]
  exact hrf.canon_eq

/-- The graphs of the reads-from version are the canonical forms of the
graphs of the Shasha-Snir version. -/
theorem mem_exploreR_iff_canon {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible)
    (τ' : TieBreak S) (G : Graph) :
    G ∈ exploreR P (M.sym S) γ τ n ↔ ∃ G' ∈ explore P (M.sym S) τ' n, G'.canon = G := by
  rw [(exploreR_spec (γ := γ) (τ := τ) hn hM).2]
  constructor
  · rintro ⟨hW, hE, ⟨co, hWc, hc⟩, hF, hcan⟩
    refine ⟨G.withCo co, ((explore_spec (τ := τ') hn hM).2 _).mpr ⟨hWc, hE, hc, hF⟩, ?_⟩
    rw [Graph.withCo_canon]
    exact hcan.canon_eq
  · rintro ⟨G', hG', rfl⟩
    obtain ⟨hW, hE, hc, hF⟩ := ((explore_spec (τ := τ') hn hM).2 _).mp hG'
    exact ⟨hW.canon, (Program.exec_withCo P _ _).mpr hE,
      (Model.rf_cons_congr (Graph.rfEq_canon G')).mp (Model.rf_cons_of_cons hW hc), hF,
      Graph.canon_isCanon G'⟩

/-- The reads-from version reports at most as many graphs as the Shasha-Snir
version. -/
theorem exploreR_length_le {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible) (τ' : TieBreak S) :
    (exploreR P (M.sym S) γ τ n).length ≤ (explore P (M.sym S) τ' n).length := by
  classical
  have h1 := (exploreR_spec (γ := γ) (τ := τ) hn hM).1
  have h2 := (explore_spec (τ := τ') hn hM).1
  rw [← List.toFinset_card_of_nodup h1, ← List.toFinset_card_of_nodup h2]
  have : (exploreR P (M.sym S) γ τ n).toFinset =
      (explore P (M.sym S) τ' n).toFinset.image Graph.canon := by
    ext G
    rw [List.mem_toFinset, mem_exploreR_iff_canon hn hM τ', Finset.mem_image]
    simp only [List.mem_toFinset]
  rw [this]
  exact Finset.card_image_le

end Condpor
