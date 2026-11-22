import Mazurkiewicz.Condpor.Rmw.Ext

/-!
# `SC` with atomicity is exclusive-write extensible

Def. A.19 for `SC`: the exclusive write `e` of a prospective pair `(r, e)` is
placed directly after the source `s` of `r` in coherence.

* The SC order stays acyclic for *every* prospective pair. The edges out of
  `e` go to the writes coherence-after `s`; the edges into `e` come from the
  events of the thread of `e`, from the writes up to `s` and from their reads.
  From each of these there is a nonempty path of `G` to every write
  coherence-after `s` (for the thread of `e`: through `r`, which reads from
  `s`; an edge otherwise). So a cycle
  through `e` gives a cycle of `G`.
* Atomicity needs the premise of Def. A.19: no completed pair has a read with
  source `s`. Then no completed pair is separated by the insertion.
-/

namespace Maz

open Relation

/-- Adding a vertex `e` keeps a relation acyclic if no old path leads from a
successor of `e` to a predecessor of `e`. -/
theorem Acyclic.of_insert {α : Type*} {r r' : α → α → Prop} {e : α} (hr : Acyclic r)
    (hsub : ∀ a b, r' a b → a ≠ e → b ≠ e → r a b) (hirr : ¬ r' e e)
    (hno : ∀ a b, a ≠ e → b ≠ e → r' a e → r' e b → ¬ ReflTransGen r b a) :
    Acyclic r' := by
  -- a path of `r'` from `x ≠ e`: old; or old up to `e`; or old, `e`, old
  have key : ∀ x y, x ≠ e → TransGen r' x y →
      (y ≠ e ∧ TransGen r x y) ∨
      (∃ a, a ≠ e ∧ ReflTransGen r x a ∧ r' a e ∧
        (y = e ∨ (y ≠ e ∧ ∃ b, b ≠ e ∧ r' e b ∧ ReflTransGen r b y))) := by
    intro x y hx h
    induction h with
    | @single y h =>
      by_cases hy : y = e
      · exact Or.inr ⟨x, hx, ReflTransGen.refl, hy ▸ h, Or.inl hy⟩
      · exact Or.inl ⟨hy, TransGen.single (hsub _ _ h hx hy)⟩
    | @tail c d _ hcd ih =>
      by_cases hd : d = e
      · rcases ih with ⟨hc, h1⟩ | ⟨a, ha, h1, h2, h3 | ⟨hc, b, hb, h4, h5⟩⟩
        · exact Or.inr ⟨c, hc, h1.to_reflTransGen, hd ▸ hcd, Or.inl hd⟩
        · rw [h3, hd] at hcd
          exact absurd hcd hirr
        · exact absurd h5 (hno c b hc hb (hd ▸ hcd) h4)
      · rcases ih with ⟨hc, h1⟩ | ⟨a, ha, h1, h2, h3 | ⟨hc, b, hb, h4, h5⟩⟩
        · exact Or.inl ⟨hd, h1.tail (hsub _ _ hcd hc hd)⟩
        · exact Or.inr ⟨a, ha, h1, h2, Or.inr ⟨hd, d, hd, h3 ▸ hcd, ReflTransGen.refl⟩⟩
        · exact Or.inr ⟨a, ha, h1, h2, Or.inr ⟨hd, b, hb, h4, h5.tail (hsub _ _ hcd hc hd)⟩⟩
  intro a ha
  by_cases hae : a = e
  · subst hae
    obtain ⟨c, hc, hca⟩ := TransGen.head'_iff.mp ha
    by_cases hce : c = a
    · exact hirr (hce ▸ hc)
    · rcases reflTransGen_iff_eq_or_transGen.mp hca with h | h
      · exact hce h.symm
      · rcases key c a hce h with ⟨h1, -⟩ | ⟨b, hb, h1, h2, -⟩
        · exact h1 rfl
        · exact hno b c hb hce h2 hc h1
  · rcases key a a hae ha with ⟨-, h1⟩ | ⟨b, hb, h1, h2, h3 | ⟨-, d, hd, h4, h5⟩⟩
    · exact hr a h1
    · exact hae h3
    · exact hno b d hb hd h2 h4 (h5.trans h1)

end Maz

namespace List

variable {α : Type*} [DecidableEq α]

/-- The new element is directly after `a`. -/
theorem exists_insertAfter_split {l : List α} {a x : α} (ha : a ∈ l) :
    ∃ l₁ l₂, l.insertAfter a x = l₁ ++ a :: x :: l₂ := by
  induction l with
  | nil => cases ha
  | cons b l ih =>
    by_cases hb : b = a
    · exact ⟨[], l, by simp [insertAfter, hb]⟩
    · obtain ⟨l₁, l₂, h⟩ := ih ((List.mem_cons.mp ha).resolve_left (Ne.symm hb))
      exact ⟨b :: l₁, l₂, by simp [insertAfter, hb, h]⟩

/-- An insertion keeps the first element. -/
theorem exists_insertAfter_cons (w : α) (l : List α) (a x : α) :
    ∃ l', (w :: l).insertAfter a x = w :: l' := by
  by_cases hw : w = a
  · exact ⟨x :: l, by simp [insertAfter, hw]⟩
  · exact ⟨l.insertAfter a x, by simp [insertAfter, hw]⟩

/-- An insertion after `a` does not separate two neighbours whose first is
not `a`. -/
theorem exists_insertAfter_adj {l₁ l₂ : List α} {p w a x : α} (hp : p ≠ a) :
    ∃ m₁ m₂, (l₁ ++ p :: w :: l₂).insertAfter a x = m₁ ++ p :: w :: m₂ := by
  induction l₁ with
  | nil =>
    obtain ⟨l', hl'⟩ := exists_insertAfter_cons w l₂ a x
    refine ⟨[], l', ?_⟩
    have h : (p :: w :: l₂).insertAfter a x = p :: (w :: l₂).insertAfter a x := by
      simp [insertAfter, hp]
    rw [List.nil_append, List.nil_append, h, hl']
  | cons b l₁ ih =>
    by_cases hb : b = a
    · exact ⟨b :: x :: l₁, l₂, by simp [insertAfter, hb]⟩
    · obtain ⟨m₁, m₂, h⟩ := ih
      exact ⟨b :: m₁, m₂, by simp [insertAfter, hb, h]⟩

end List

namespace Condpor

open Program

namespace Graph

variable {G : Graph}

theorem addWrite_co_init (G : Graph) (e : TEv) :
    (G.addWrite e .init).co e.loc = e :: G.co e.loc := by
  simp [addWrite]

theorem addWrite_co_th (G : Graph) (e p : TEv) :
    (G.addWrite e (.th p)).co e.loc = (G.co e.loc).insertAfter p e := by
  simp [addWrite]

/-- The old writes of the coherence lists after adding a write. -/
theorem addWrite_co_mem_old (e : TEv) (wp : Ev) {y : Loc} {q : TEv} (hqe : q ≠ e)
    (hq : q ∈ (G.addWrite e wp).co y) : q ∈ G.co y := by
  by_cases hy : y = e.loc
  · subst hy
    cases wp with
    | init =>
      rw [addWrite_co_init] at hq
      exact (List.mem_cons.mp hq).resolve_left hqe
    | th p =>
      rw [addWrite_co_th] at hq
      exact (List.mem_insertAfter.mp hq).resolve_left hqe
  · rwa [G.addWrite_co_of_ne e wp hy] at hq

/-- The order of the old writes is kept. -/
theorem addWrite_co_before_old (hG : G.Wf) {e : TEv} (he : e ∉ G.events) (wp : Ev) {y : Loc}
    {p q : TEv} (hpe : p ≠ e) (hqe : q ≠ e) (h : ((G.addWrite e wp).co y).Before p q) :
    (G.co y).Before p q := by
  have heco : e ∉ G.co y := fun h => he ((hG.co_mem y e).mp h).1
  by_cases hy : y = e.loc
  · subst hy
    cases wp with
    | init =>
      rw [addWrite_co_init] at h
      rcases (List.before_cons_iff_of_notMem heco).mp h with ⟨h1, -⟩ | h1
      · exact absurd h1 hpe
      · exact h1
    | th p' =>
      rw [addWrite_co_th] at h
      exact (List.before_insertAfter_old hpe hqe).mp h
  · rwa [G.addWrite_co_of_ne e wp hy] at h

/-- The steps of the SC order between old events after adding a write
anywhere in coherence. -/
theorem scStep_addWrite_old (hG : G.Wf) {e : TEv} {wp : Ev} (hidx : e.idx = G.cnt e.tid)
    {a b : Ev} (h : (G.addWrite e wp).scStep a b) (ha : a ≠ .th e) (hb : b ≠ .th e) :
    G.scStep a b := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  rcases h with h | h | h | ⟨q, q', y, rfl, rfl, hqm, hqact, hq'co, hrf⟩
  · exact Or.inl ((po_of_events_insert hG hidx rfl h).resolve_right hb)
  · exact ((porfStep_addWrite hG hidx (Or.inr h)).resolve_right hb).elim Or.inl
      (fun h' => Or.inr (Or.inl h'))
  · refine Or.inr (Or.inr (Or.inl ?_))
    cases b with
    | init => cases a <;> exact absurd h (by simp [coRel])
    | th q =>
      have hqe : q ≠ e := fun h' => hb (congrArg Ev.th h')
      cases a with
      | init =>
        obtain ⟨y, hy⟩ := h
        exact ⟨y, addWrite_co_mem_old e wp hqe hy⟩
      | th q' =>
        obtain ⟨y, hy⟩ := h
        exact ⟨y, addWrite_co_before_old hG he wp (fun h' => ha (congrArg Ev.th h')) hqe hy⟩
  · have hqe : q ≠ e := fun h' => ha (congrArg Ev.th h')
    have hq'e : q' ≠ e := fun h' => hb (congrArg Ev.th h')
    refine Or.inr (Or.inr (Or.inr ⟨q, q', y, rfl, rfl,
      (Finset.mem_insert.mp hqm).resolve_left hqe, hqact,
      addWrite_co_mem_old e wp hq'e hq'co, ?_⟩))
    rcases hrf with hrf | ⟨e'', hrf, hbef⟩
    · exact Or.inl hrf
    · have he'' : e'' ≠ e := fun h' => he (h' ▸ (hG.rf_source_mem hrf).2)
      exact Or.inr ⟨e'', hrf, addWrite_co_before_old hG he wp he'' hq'e hbef⟩

/-- The new write is in the coherence list of its location only. -/
theorem addWrite_co_loc_of_mem (hG : G.Wf) {e : TEv} (he : e ∉ G.events) (wp : Ev) {y : Loc}
    (h : e ∈ (G.addWrite e wp).co y) : y = e.loc := by
  by_contra hy
  rw [G.addWrite_co_of_ne e wp hy] at h
  exact he ((hG.co_mem y e).mp h).1

/-- The steps of the SC order out of the new write go to the writes
coherence-after its place. -/
theorem scStep_addWrite_out (hG : G.Wf) {e : TEv} {wp : Ev} (hidx : e.idx = G.cnt e.tid)
    (hact : e.IsWrite) (hwp : G.IsWriteTo e.loc wp) {b : Ev}
    (h : (G.addWrite e wp).scStep (.th e) b) : G.coRelAt e.loc wp b := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  have heco : e ∉ G.co e.loc := fun h => he ((hG.co_mem _ e).mp h).1
  rcases h with h | h | h | ⟨q, q', y, hq, rfl, -, hqact, -, -⟩
  · exact absurd h (not_po_of_events_insert hG hidx rfl b)
  · exact absurd (Or.inr h) (not_porfStep_addWrite_self hG hidx b)
  · cases b with
    | init => exact absurd h (by simp [coRel])
    | th w' =>
      obtain ⟨y, hy⟩ := h
      obtain rfl := addWrite_co_loc_of_mem hG he wp hy.1
      cases wp with
      | init =>
        rw [addWrite_co_init] at hy
        rcases (List.before_cons_iff_of_notMem heco).mp hy with ⟨-, h1⟩ | h1
        · exact h1
        · exact absurd h1.1 heco
      | th p =>
        rw [addWrite_co_th] at hy
        exact (List.before_insertAfter_new_left ((hG.co_mem _ p).mpr hwp) heco).mp hy
  · have hqe : q = e := (Ev.th.inj hq).symm
    rw [hqe] at hqact
    simp [TEv.IsWrite, hqact, Act.IsWrite] at hact

/-- The steps of the SC order into the new write. -/
theorem scStep_addWrite_in (hG : G.Wf) {e : TEv} {wp : Ev} (hidx : e.idx = G.cnt e.tid)
    (hwp : G.IsWriteTo e.loc wp) {a : Ev}
    (h : (G.addWrite e wp).scStep a (.th e)) (ha : a ≠ .th e) :
    a = .init ∨ (∃ q, a = .th q ∧ q ∈ G.events ∧ q.tid = e.tid) ∨
      (∃ q p, a = .th q ∧ wp = .th p ∧ (q = p ∨ (G.co e.loc).Before q p)) ∨
      (∃ q, a = .th q ∧ q ∈ G.events ∧ q.act = .read e.loc ∧
        (G.rf q = some .init ∨ ∃ e'' p, G.rf q = some (.th e'') ∧ wp = .th p ∧
          (e'' = p ∨ (G.co e.loc).Before e'' p))) := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  have heco : e ∉ G.co e.loc := fun h => he ((hG.co_mem _ e).mp h).1
  -- the writes before the new write
  have hbef : ∀ q, ((G.addWrite e wp).co e.loc).Before q e →
      ∃ p, wp = .th p ∧ (q = p ∨ (G.co e.loc).Before q p) := by
    intro q hq
    cases wp with
    | init =>
      rw [addWrite_co_init] at hq
      rcases (List.before_cons_iff_of_notMem heco).mp hq with ⟨-, h1⟩ | h1
      · exact absurd h1 heco
      · exact absurd h1.2.1 heco
    | th p =>
      rw [addWrite_co_th] at hq
      exact ⟨p, rfl, (List.before_insertAfter_new_right ((hG.co_mem _ p).mpr hwp) heco).mp hq⟩
  rcases h with h | ⟨q, hq, -, hrf⟩ | h | ⟨q, q', y, rfl, hq', hqm, hqact, hq'co, hrf⟩
  · cases a with
    | init => exact Or.inl rfl
    | th q =>
      obtain ⟨hqm, -, ht, -⟩ := h
      have hqe : q ≠ e := fun h' => ha (congrArg Ev.th h')
      exact Or.inr (Or.inl ⟨q, rfl, (Finset.mem_insert.mp hqm).resolve_left hqe, ht⟩)
  · rw [← Ev.th.inj hq] at hrf
    exact absurd (hG.rf_source_mem hrf).1 he
  · cases a with
    | init => exact Or.inl rfl
    | th q =>
      obtain ⟨y, hy⟩ := h
      obtain rfl := addWrite_co_loc_of_mem hG he wp hy.2.1
      obtain ⟨p, hp, h1⟩ := hbef q hy
      exact Or.inr (Or.inr (Or.inl ⟨q, p, rfl, hp, h1⟩))
  · rw [← Ev.th.inj hq'] at hq'co hrf
    obtain rfl := addWrite_co_loc_of_mem hG he wp hq'co
    have hqe : q ≠ e := fun h' => ha (congrArg Ev.th h')
    refine Or.inr (Or.inr (Or.inr ⟨q, rfl, (Finset.mem_insert.mp hqm).resolve_left hqe, hqact, ?_⟩))
    rcases hrf with hrf | ⟨e'', hrf, hb⟩
    · exact Or.inl hrf
    · obtain ⟨p, hp, h1⟩ := hbef e'' hb
      exact Or.inr ⟨e'', p, hrf, hp, h1⟩

/-- A write placed directly after the source `s` of the last event `r` of its
thread, a read of its location, keeps the SC order acyclic. -/
theorem scStep_addWrite_acyclic (hG : G.Wf) (hc : Maz.Acyclic G.scStep) {e r : TEv} {s : Ev}
    (hidx : e.idx = G.cnt e.tid) (hact : e.IsWrite) (hr : r ∈ G.events) (ht : e.tid = r.tid)
    (hi : e.idx = r.idx + 1) (hract : r.act = .read e.loc) (hrf : G.rf r = some s) :
    Maz.Acyclic (G.addWrite e s).scStep := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  have hwp : G.IsWriteTo e.loc s := by
    obtain ⟨w, hw, hw'⟩ := hG.rf_read r hr _ hract
    rw [hrf] at hw
    exact Option.some.inj hw ▸ hw'
  refine Maz.Acyclic.of_insert (e := .th e) hc
    (fun a b h ha hb => scStep_addWrite_old hG hidx h ha hb) ?_ ?_
  · intro h
    have := scStep_addWrite_out hG hidx hact hwp h
    cases s with
    | init => exact he ((hG.co_mem _ e).mp this).1
    | th p => exact he ((hG.co_mem _ e).mp this.2.1).1
  · intro a b ha hb hin hout hpath
    have hafter := scStep_addWrite_out hG hidx hact hwp hout
    -- `b` is a write of the location, coherence-after `s`
    obtain ⟨w', rfl, hw'co⟩ : ∃ w', b = .th w' ∧ w' ∈ G.co e.loc := by
      cases b with
      | init => cases s <;> exact absurd hafter (by simp [coRelAt])
      | th w' =>
        cases s with
        | init => exact ⟨w', rfl, hafter⟩
        | th p => exact ⟨w', rfl, hafter.2.1⟩
    suffices h : Relation.TransGen G.scStep a (.th w') from
      hc _ (Relation.TransGen.trans_right hpath h)
    -- `r` is from-read before `w'`
    have hfr : G.scStep (.th r) (.th w') := by
      refine Or.inr (Or.inr (Or.inr ⟨r, w', e.loc, rfl, rfl, hr, hract, hw'co, ?_⟩))
      cases s with
      | init => exact Or.inl hrf
      | th p => exact Or.inr ⟨p, hrf, hafter⟩
    rcases scStep_addWrite_in hG hidx hwp hin ha with rfl | ⟨q, rfl, hq, hqt⟩ |
      ⟨q, p, rfl, rfl, h1⟩ | ⟨q, rfl, hq, hqact, h1⟩
    · exact .single (Or.inr (Or.inr (Or.inl ⟨e.loc, hw'co⟩)))
    · by_cases hqr : q = r
      · exact hqr ▸ .single hfr
      · have hlt := hG.idx_lt_cnt hq
        rw [hqt, ← hidx, hi] at hlt
        have hne : q.idx ≠ r.idx := fun h' => hqr (hG.idx_inj q hq r hr (hqt.trans ht) h')
        have hpo : G.po (.th q) (.th r) := ⟨hq, hr, hqt.trans ht, by omega⟩
        exact .head (Or.inl hpo) (.single hfr)
    · refine .single (Or.inr (Or.inr (Or.inl ⟨e.loc, ?_⟩)))
      rcases h1 with rfl | h1
      · exact hafter
      · exact h1.trans hafter
    · refine .single (Or.inr (Or.inr (Or.inr ⟨q, w', e.loc, rfl, rfl, hq, hqact, hw'co, ?_⟩)))
      rcases h1 with h1 | ⟨e'', p, h1, rfl, h2⟩
      · exact Or.inl h1
      · refine Or.inr ⟨e'', h1, ?_⟩
        rcases h2 with rfl | h2
        · exact hafter
        · exact h2.trans hafter

/-- An insertion directly after `s` keeps the immediate successors of the
other writes. -/
theorem ImmCo.addWrite_of_ne {y : Loc} {s s' : Ev} {w : TEv} (h : G.ImmCo y s' w)
    (hne : s' ≠ s) (e : TEv) : (G.addWrite e s).ImmCo y s' w := by
  by_cases hy : y = e.loc
  · subst hy
    cases s with
    | init =>
      cases s' with
      | init => exact absurd rfl hne
      | th p' =>
        obtain ⟨l₁, l₂, hl⟩ := h
        exact ⟨e :: l₁, l₂, by rw [addWrite_co_init, hl]; rfl⟩
    | th p =>
      cases s' with
      | init =>
        obtain ⟨l, hl⟩ := h
        obtain ⟨l', hl'⟩ := List.exists_insertAfter_cons w l p e
        exact ⟨l', by rw [addWrite_co_th, hl, hl']⟩
      | th p' =>
        obtain ⟨l₁, l₂, hl⟩ := h
        have hpp : p' ≠ p := fun h' => hne (congrArg Ev.th h')
        obtain ⟨m₁, m₂, hm⟩ := List.exists_insertAfter_adj (l₁ := l₁) (l₂ := l₂) (w := w)
          (x := e) hpp
        exact ⟨m₁, m₂, by rw [addWrite_co_th, hl, hm]⟩
  · exact h.of_co_eq (G.addWrite_co_of_ne e s hy)

/-- The new write is the immediate successor of its place. -/
theorem immCo_addWrite (hG : G.Wf) (e : TEv) {s : Ev} (hwp : G.IsWriteTo e.loc s) :
    (G.addWrite e s).ImmCo e.loc s e := by
  cases s with
  | init => exact ⟨G.co e.loc, addWrite_co_init G e⟩
  | th p =>
    obtain ⟨l₁, l₂, h⟩ := List.exists_insertAfter_split (x := e) ((hG.co_mem _ p).mpr hwp)
    exact ⟨l₁, l₂, by rw [addWrite_co_th, h]⟩

end Graph

/-- The read of a prospective pair reads the location of the write. -/
theorem XProgram.Mate.read_act {P : XProgram} {G : Graph} (hE : P.toProgram.Exec G)
    {r e : TEv} (hm : P.Mate G r e) : r.act = .read e.loc := by
  obtain ⟨hrG, -, -, he, ht, hi, hw, hex⟩ := hm
  obtain ⟨-, hidx, hs⟩ := mem_avail_iff.mp he
  obtain ⟨v, hv⟩ := hw.exists_act
  rw [hv] at hs
  obtain ⟨u₀, a, hu, -, hs0⟩ := P.ex_write e.tid _ e.loc v hex hs
  have htr : G.trace e.tid = G.traceBefore e.tid r.idx ++ [(G.evAt e.tid r.idx).bind G.ret] := by
    unfold Graph.trace
    rw [← hidx, hi, Graph.traceBefore_succ]
  rw [htr] at hu
  obtain ⟨h1, -⟩ := List.append_inj' hu rfl
  have := hE.2 r hrG
  rw [← ht, h1, hs0] at this
  exact (Option.some.inj this).symm

/-- The two events of a completed pair of an execution access the same
location. (`RMW` does not ask it.) -/
theorem XProgram.RMW.read_act {P : XProgram} {G : Graph} (hE : P.toProgram.Exec G)
    {r w : TEv} (h : P.RMW G r w) : r.act = .read w.loc := by
  obtain ⟨hr, hw, ht, hi, -, hwW, -, hwx⟩ := h
  obtain ⟨v, hv⟩ := hwW.exists_act
  have hs := hE.2 w hw
  rw [hv] at hs
  obtain ⟨u₀, a, hu, -, hs0⟩ := P.ex_write w.tid _ w.loc v hwx hs
  rw [hi, Graph.traceBefore_succ] at hu
  obtain ⟨h1, -⟩ := List.append_inj' hu rfl
  have := hE.2 r hr
  rw [← ht, h1, hs0] at this
  exact (Option.some.inj this).symm

/-- Def. A.19 for `SC`: the write of a prospective pair is placed directly
after the source of its read. -/
theorem SC.exclExtensible (P : XProgram) : ExclExtensible P (Model.atomic P SC) := by
  intro G r e s hG hE ⟨hc, hat⟩ hm hrf hfree
  have hract := hm.read_act hE
  obtain ⟨hrG, -, -, he, ht, hi, hw, -⟩ := hm
  have hidx := idx_eq_of_mem_avail he
  have hwp : G.IsWriteTo e.loc s := by
    obtain ⟨w, hw1, hw2⟩ := hG.rf_read r hrG _ hract
    rw [hrf] at hw1
    exact Option.some.inj hw1 ▸ hw2
  refine ⟨s, hwp, Graph.scStep_addWrite_acyclic hG hc hidx hw hrG ht hi hract hrf, ?_⟩
  have htr : ∀ q ∈ G.events, (G.addWrite e s).traceBefore q.tid q.idx =
      G.traceBefore q.tid q.idx := fun q hq =>
    Graph.traceBefore_addWrite_le hG hidx hw hwp q.tid (Nat.le_of_lt (hG.idx_lt_cnt hq))
  intro r' w hrw s' hs'
  have hs'G : G.rf r' = some s' := hs'
  obtain ⟨hr'G, -, hcase⟩ := hrw.of_ext hG hidx rfl htr
  rcases hcase with hold | ⟨rfl, -, -⟩
  · exact (hat r' w hold s' hs'G).addWrite_of_ne
      (fun h' => hfree ⟨r', w, hold, by rw [← h']; exact hs'G⟩) _
  · have hrr : r' = r := by
      refine hG.idx_inj r' hr'G r hrG (hrw.2.2.1.symm.trans ht) ?_
      have := hrw.2.2.2.1
      omega
    rw [hrr, hrf] at hs'G
    cases hs'G
    exact Graph.immCo_addWrite hG _ hwp

end Condpor
