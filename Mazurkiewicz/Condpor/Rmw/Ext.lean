import Mazurkiewicz.Condpor.Rmw.Defs

/-!
# Read-modify-write accesses: the assumptions on the model

`ExtensibleX P M`: maximal extensibility (TruSt, Def. A.17) for a model with
atomicity, with its third clause: an exclusive write whose read reads from the
last write of the location may be placed last. `ExclExtensible P M`
(Def. A.19): an exclusive write whose read's source is not the source of the
read of a completed pair has a consistent place.

Both are stated for executions of the program and available events: the kind
of an event is defined through the program. The accepted `Model.Extensible`
asks that *every* write may be placed last; a model with atomicity does not
satisfy it.

`SC` with atomicity satisfies `ExtensibleX` (this file).
-/

namespace Condpor

open Program

/-- Maximal extensibility with exclusive writes (Def. A.17). -/
structure ExtensibleX (P : XProgram) (M : Model) : Prop where
  /-- a new read that reads from the last write of its location -/
  ext_read : ∀ (G : Graph) (e : TEv) (x : Loc), G.Wf → P.toProgram.Exec G → M.cons G →
    e ∈ P.toProgram.avail G → e.act = .read x → M.cons (G.addRead e (G.maxWrite x))
  /-- a new write that is not exclusive, placed last -/
  ext_write : ∀ (G : Graph) (e : TEv), G.Wf → P.toProgram.Exec G → M.cons G →
    e ∈ P.toProgram.avail G → e.IsWrite → P.ex e.tid (G.trace e.tid) = false →
    M.cons (G.addWrite e (G.maxWrite e.loc))
  /-- a new exclusive write whose read reads from the last write, placed last -/
  ext_wex : ∀ (G : Graph) (r e : TEv), G.Wf → P.toProgram.Exec G → M.cons G → P.Mate G r e →
    G.rf r = some (G.maxWrite e.loc) → M.cons (G.addWrite e (G.maxWrite e.loc))
  /-- a new event that is neither a read nor a write, with any outcome -/
  ext_loc : ∀ (G : Graph) (e : TEv) (o : Option Bool), G.Wf → P.toProgram.Exec G → M.cons G →
    e ∈ P.toProgram.avail G → e.IsLocal → (o.isSome ↔ e.IsCons) → M.cons (G.addLoc e o)

/-- Exclusive-write extensibility (Def. A.19): if the source of the read of a
prospective pair is not the source of the read of a completed pair, the write
has a consistent place. -/
def ExclExtensible (P : XProgram) (M : Model) : Prop :=
  ∀ (G : Graph) (r e : TEv) (s : Ev), G.Wf → P.toProgram.Exec G → M.cons G → P.Mate G r e →
    G.rf r = some s → (¬ ∃ r' w', P.RMW G r' w' ∧ G.rf r' = some s) →
    ∃ wp, G.IsWriteTo e.loc wp ∧ M.cons (G.addWrite e wp)

/-! ### Pairs of an extension by one event -/

section Ext

variable {P : XProgram} {G G' : Graph} {e : TEv}

/-- The completed pairs of an extension of `G` by the event `e` that keeps the
traces of the old events: the pairs of `G`, and possibly a pair with the write
`e`. -/
theorem XProgram.RMW.of_ext (hG : G.Wf) (hidx : e.idx = G.cnt e.tid)
    (hev : G'.events = insert e G.events)
    (htr : ∀ q ∈ G.events, G'.traceBefore q.tid q.idx = G.traceBefore q.tid q.idx)
    {r w : TEv} (h : P.RMW G' r w) :
    r ∈ G.events ∧ (P.IsEx G r) ∧ (P.RMW G r w ∨ (w = e ∧ e.IsWrite ∧ P.IsEx G' e)) := by
  obtain ⟨hr, hw, ht, hi, hrR, hwW, hrx, hwx⟩ := h
  rw [hev] at hr hw
  have hrG : r ∈ G.events := by
    rcases Finset.mem_insert.mp hr with rfl | hr'
    · exfalso
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · omega
      · have := hG.idx_lt_cnt hw'
        rw [ht, hi, ← hidx] at this
        omega
    · exact hr'
  have hrx' : P.IsEx G r := by
    unfold XProgram.IsEx at hrx ⊢
    rwa [htr r hrG] at hrx
  refine ⟨hrG, hrx', ?_⟩
  rcases Finset.mem_insert.mp hw with rfl | hw'
  · exact Or.inr ⟨rfl, hwW, hwx⟩
  · left
    refine ⟨hrG, hw', ht, hi, hrR, hwW, hrx', ?_⟩
    unfold XProgram.IsEx at hwx ⊢
    rwa [htr w hw'] at hwx

end Ext

namespace Graph

/-- Appending a write at the end of a coherence list keeps immediate
succession. -/
theorem ImmCo.of_append {G G' : Graph} {x : Loc} {s : Ev} {w e : TEv}
    (h : G.ImmCo x s w) (hco : G'.co x = G.co x ++ [e]) : G'.ImmCo x s w := by
  cases s with
  | init =>
    obtain ⟨l, hl⟩ := h
    exact ⟨l ++ [e], by rw [hco, hl]; rfl⟩
  | th p =>
    obtain ⟨l₁, l₂, hl⟩ := h
    exact ⟨l₁, l₂ ++ [e], by rw [hco, hl]; simp⟩

theorem ImmCo.of_co_eq {G G' : Graph} {x : Loc} {s : Ev} {w : TEv}
    (h : G.ImmCo x s w) (hco : G'.co x = G.co x) : G'.ImmCo x s w := by
  cases s with
  | init =>
    obtain ⟨l, hl⟩ := h
    exact ⟨l, by rw [hco, hl]⟩
  | th p =>
    obtain ⟨l₁, l₂, hl⟩ := h
    exact ⟨l₁, l₂, by rw [hco, hl]⟩

/-- A write appended at the end is the immediate successor of the last
write. -/
theorem immCo_maxWrite_append {G G' : Graph} {x : Loc} {e : TEv}
    (hco : G'.co x = G.co x ++ [e]) : G'.ImmCo x (G.maxWrite x) e := by
  unfold maxWrite
  cases h : (G.co x).getLast? with
  | none =>
    have h0 : G.co x = [] := List.getLast?_eq_none_iff.mp h
    exact ⟨[], by rw [hco, h0]; rfl⟩
  | some p =>
    obtain ⟨l₁, hl⟩ := List.getLast?_eq_some_iff.mp h
    exact ⟨l₁, [], by rw [hco, hl]; simp⟩

end Graph

/-! ### `SC` with atomicity is maximally extensible -/

/-- Atomicity of an extension that keeps the traces, the sources and the
coherence of the old events up to appending the new event, provided a newly
completed pair satisfies atomicity. -/
theorem XProgram.Atomic.of_ext {P : XProgram} {G G' : Graph} {e : TEv} (hG : G.Wf)
    (hat : P.Atomic G) (hidx : e.idx = G.cnt e.tid) (hev : G'.events = insert e G.events)
    (htr : ∀ q ∈ G.events, G'.traceBefore q.tid q.idx = G.traceBefore q.tid q.idx)
    (hrf : ∀ q ∈ G.events, G'.rf q = G.rf q)
    (hco : ∀ x, G'.co x = G.co x ∨ G'.co x = G.co x ++ [e])
    (hnew : ∀ r, P.RMW G' r e → ∀ s, G'.rf r = some s → G'.ImmCo e.loc s e) :
    P.Atomic G' := by
  intro r w hrw s hs
  obtain ⟨hrG, -, hcase⟩ := hrw.of_ext hG hidx hev htr
  rcases hcase with hold | ⟨rfl, -, -⟩
  · rw [hrf r hrG] at hs
    have h := hat r w hold s hs
    rcases hco w.loc with h1 | h1
    · exact h.of_co_eq h1
    · exact h.of_append h1
  · exact hnew r hrw s hs

theorem SC.extensibleX (P : XProgram) : ExtensibleX P (Model.atomic P SC) where
  ext_read := by
    intro G e x hG hE ⟨hc, hat⟩ he hact
    have hidx := idx_eq_of_mem_avail he
    have hne := hG.not_mem_of_idx_eq_cnt hidx
    have hw := Graph.maxWrite_isWriteTo hG x
    refine ⟨SC.extensible.ext_read G e x hG hc hidx hact, ?_⟩
    refine XProgram.Atomic.of_ext hG hat hidx rfl
      (fun q hq => Graph.traceBefore_addRead_le hG hidx hact hw q.tid
        (Nat.le_of_lt (hG.idx_lt_cnt hq)))
      (fun q hq => by
        have hqe : q ≠ e := fun h => hne (h ▸ hq)
        rw [Graph.addRead_rf]
        exact Function.update_of_ne hqe _ _)
      (fun _ => Or.inl rfl) ?_
    intro r hr
    exact absurd hr.2.2.2.2.2.1 (by simp [TEv.IsWrite, hact, Act.IsWrite])
  ext_write := by
    intro G e hG hE ⟨hc, hat⟩ he hw hnx
    have hidx := idx_eq_of_mem_avail he
    have hwp := Graph.maxWrite_isWriteTo hG e.loc
    refine ⟨SC.extensible.ext_write G e hG hc hidx hw, ?_⟩
    refine XProgram.Atomic.of_ext hG hat hidx rfl
      (fun q hq => Graph.traceBefore_addWrite_le hG hidx hw hwp q.tid
        (Nat.le_of_lt (hG.idx_lt_cnt hq)))
      (fun q _ => rfl)
      (fun x => by
        rw [Graph.addWrite_maxWrite_co_eq hG e x]
        by_cases hx : x = e.loc
        · exact Or.inr (by simp [hx])
        · exact Or.inl (by simp [hx])) ?_
    intro r hr
    exfalso
    have hx : P.IsEx (G.addWrite e (G.maxWrite e.loc)) e := hr.2.2.2.2.2.2.2
    unfold XProgram.IsEx at hx
    rw [Graph.traceBefore_addWrite_le hG hidx hw hwp e.tid (Nat.le_of_eq hidx)] at hx
    have : G.traceBefore e.tid e.idx = G.trace e.tid := by rw [hidx]; rfl
    rw [this, hnx] at hx
    cases hx
  ext_wex := by
    intro G r e hG hE ⟨hc, hat⟩ hm hrf
    obtain ⟨hrG, -, -, he, ht, hi, hw, -⟩ := hm
    have hidx := idx_eq_of_mem_avail he
    have hwp := Graph.maxWrite_isWriteTo hG e.loc
    refine ⟨SC.extensible.ext_write G e hG hc hidx hw, ?_⟩
    refine XProgram.Atomic.of_ext hG hat hidx rfl
      (fun q hq => Graph.traceBefore_addWrite_le hG hidx hw hwp q.tid
        (Nat.le_of_lt (hG.idx_lt_cnt hq)))
      (fun q _ => rfl)
      (fun x => by
        rw [Graph.addWrite_maxWrite_co_eq hG e x]
        by_cases hx : x = e.loc
        · exact Or.inr (by simp [hx])
        · exact Or.inl (by simp [hx])) ?_
    intro r' hr' s hs
    -- the read of the pair is `r`
    have hr'G : r' ∈ G.events :=
      (hr'.of_ext hG hidx rfl (fun q hq => Graph.traceBefore_addWrite_le hG hidx hw hwp q.tid
        (Nat.le_of_lt (hG.idx_lt_cnt hq)))).1
    have hrr : r' = r := by
      refine hG.idx_inj r' hr'G r hrG (hr'.2.2.1.symm.trans ht) ?_
      have := hr'.2.2.2.1
      omega
    subst hrr
    have hs' : G.rf r' = some s := hs
    rw [hrf] at hs'
    cases hs'
    exact Graph.immCo_maxWrite_append (Graph.addWrite_maxWrite_co hG e)
  ext_loc := by
    intro G e o hG hE ⟨hc, hat⟩ he hl ho
    have hidx := idx_eq_of_mem_avail he
    refine ⟨SC.extensible.ext_loc G e o hG hc hidx hl ho, ?_⟩
    refine XProgram.Atomic.of_ext hG hat hidx rfl
      (fun q hq => Graph.traceBefore_addLoc_le hG hidx hl ho q.tid
        (Nat.le_of_lt (hG.idx_lt_cnt hq)))
      (fun q _ => rfl) (fun _ => Or.inl rfl) ?_
    intro r hr
    exact absurd hr.2.2.2.2.2.1 hl.not_isWrite

end Condpor
