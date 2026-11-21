import Mazurkiewicz.Condpor.Rf.PrevTerm

/-!
# The reads-from version: completeness

Proposition A.28 (a backward step into a reached configuration is a step of
the algorithm), Lemma A.29 and Theorem A.30 of the TruSt appendix for the
reads-from version; Theorem 4 of ConDpor for it.

`RvData'` and its lemmas are `RvData` of `Complete.lean` with the hypothesis
"the configuration is reached" replaced by the facts that the proofs use
(well-formedness, the order extends `po`, the invariant, `Reach.bw_po_lt`),
and without a model; the proofs are the same text. They are applied to the
reached configuration with the coherence order that `MaxCompl` built, which
is not reached.
-/

namespace List

variable {α : Type*} [DecidableEq α]

/-- In a list without repetition, earlier elements are `Before` later ones. -/
theorem Nodup.pairwise_before {l : List α} (hl : l.Nodup) :
    l.Pairwise (fun u v => l.Before u v) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    obtain ⟨hat, ht⟩ := List.nodup_cons.mp hl
    refine List.Pairwise.cons (fun b hb => ?_) ((ih ht).imp (fun h => ?_))
    · exact before_cons_self hb (fun h => hat (h ▸ hb))
    · exact before_cons_of_before hat h

end List

namespace Condpor

open Program

variable {P : Program} {M : Model} {S : Solver} {τ : TieBreak S}

/-- The data of the revisit case of Proposition A.28, with the facts about `c`
that the proof uses in place of "`c` is reached": `RvData` of `Complete.lean`
for a configuration that need not be reached. `hs1` is (S1) of Proposition
A.23 for `X`. -/
structure RvData' (P : Program) {S : Solver} (τ : TieBreak S) (X : Graph)
    (c : Config) (a e : TEv) : Prop where
  hXW : X.Wf
  hXE : P.Exec X
  hXac : Maz.Acyclic X.porfStep
  hs1 : ∀ y ∈ P.avail X, ∀ m, X.IsMe m → ¬ nextLtEv (.th y) m
  hcW : c.Wf
  hcpo : c.PoLt
  hI : Inv P c
  hbw : ∀ {s q p : TEv}, c.Bw s q → c.abs.po (.th q) (.th p) → c.lt s p
  hs : PrevStep P τ X e (.rv a) c.abs

namespace RvData'

variable {X : Graph} {c : Config} {a e : TEv}

theorem me (D : RvData' P τ X c a e) : X.IsMe (.th a) := D.hs.rv_inv.1
theorem rf (D : RvData' P τ X c a e) : X.rf a = some (.th e) := D.hs.rv_inv.2.2.1
theorem lt (D : RvData' P τ X c a e) : nextLt a e := D.hs.rv_inv.2.2.2.1
theorem po (D : RvData' P τ X c a e) : ∀ b, X.porf (.th e) b ↔ b = .th a := D.hs.rv_inv.2.2.2.2.1
theorem mc (D : RvData' P τ X c a e) :
    MaxCompl P (τ.pref (X.remove {a, e}).F) (X.remove {a, e}) e c.abs :=
  D.hs.rv_inv.2.2.2.2.2

theorem pref (D : RvData' P τ X c a e) : (X.remove {a, e}).IsPrefixOf X :=
  (rv_remove D.hXW D.hXE D.me D.rf D.po).1
theorem av (D : RvData' P τ X c a e) : e ∈ P.avail (X.remove {a, e}) :=
  (rv_remove D.hXW D.hXE D.me D.rf D.po).2
theorem W0 (D : RvData' P τ X c a e) : (X.remove {a, e}).Wf := D.hXW.of_isPrefixOf D.pref
theorem E0 (D : RvData' P τ X c a e) : P.Exec (X.remove {a, e}) := D.hXE.of_isPrefixOf D.hXW D.pref
theorem WY (D : RvData' P τ X c a e) : c.abs.Wf := D.hcW.1

theorem sub (D : RvData' P τ X c a e) : (X.remove {a, e}).events ⊆ c.abs.events :=
  (D.mc.facts D.W0 D.E0 D.av).2.2.2.1
theorem rfY (D : RvData' P τ X c a e) :
    ∀ q ∈ (X.remove {a, e}).events, c.abs.rf q = (X.remove {a, e}).rf q :=
  (D.mc.facts D.W0 D.E0 D.av).2.2.2.2.2.2

theorem mem_old_iff (_D : RvData' P τ X c a e) {p : TEv} :
    p ∈ (X.remove {a, e}).events ↔ p ∈ X.events ∧ p ≠ a ∧ p ≠ e := by
  simp only [Graph.remove, Graph.restrict, Finset.mem_inter, Finset.mem_sdiff,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  tauto

theorem mem_order (_D : RvData' P τ X c a e) {p : TEv} : p ∈ c.order ↔ p ∈ c.abs.events :=
  List.mem_toFinset.symm

theorem e_mem (D : RvData' P τ X c a e) : e ∈ X.events := (D.hXW.rf_source_mem D.rf).2

theorem e_not_mem (D : RvData' P τ X c a e) : e ∉ c.abs.events :=
  not_mem_of_mem_avail D.WY D.mc.2.1

theorem e_idx (D : RvData' P τ X c a e) : e.idx = c.abs.cnt e.tid :=
  idx_eq_of_mem_avail D.mc.2.1

/-- The labels: `a` reads the location that `e` writes. -/
theorem acts (D : RvData' P τ X c a e) : ∃ x v, a.act = .read x ∧ e.act = .write x v := by
  have hr := D.hs.rv_inv.2.1
  obtain ⟨x, hx⟩ : ∃ x, a.act = .read x := ⟨_, TEv.IsRead.exists_act hr⟩
  obtain ⟨w, hw, hwt⟩ := D.hXW.rf_read a D.me.1 x hx
  rw [D.rf] at hw
  rw [← Option.some.inj hw] at hwt
  obtain ⟨-, v, hv⟩ := hwt
  exact ⟨x, v, hx, hv⟩

theorem e_write (D : RvData' P τ X c a e) : e.IsWrite := D.hXW.isWrite_of_src D.rf

theorem a_sink (D : RvData' P τ X c a e) (b : Ev) : ¬ X.porfStep (.th a) b :=
  fun h => D.me.2.1 b (Relation.TransGen.single h)

theorem tid_ne (D : RvData' P τ X c a e) : a.tid ≠ e.tid := by
  intro h
  have ha : a ∈ X.events := D.me.1
  rcases Nat.lt_trichotomy a.idx e.idx with h1 | h1 | h1
  · exact D.a_sink (.th e) (Or.inl ⟨ha, D.e_mem, h, h1⟩)
  · have := D.hXW.idx_inj a ha e D.e_mem h h1
    exact nextLt_irrefl e (this ▸ D.lt)
  · exact nextLt_irrefl _ (nextLt_trans (nextLt_of_poT ⟨h.symm, h1⟩) D.lt)

/-- The sources of the events other than `a` are old. -/
theorem src_old (D : RvData' P τ X c a e) {q : TEv} (hq : q ∈ X.events) (hqa : q ≠ a) (w : Ev)
    (hw : X.rf q = some w) : w ∈ Graph.evSet (X.events \ {a, e}) := by
  cases w with
  | init => trivial
  | th w' =>
    refine Finset.mem_sdiff.mpr ⟨(D.hXW.rf_source_mem hw).2, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun h => D.a_sink (.th q) (Or.inr ⟨q, rfl, hq, h ▸ hw⟩), fun h => ?_⟩
    have := (D.po (.th q)).mp (Relation.TransGen.single (Or.inr ⟨q, rfl, hq, h ▸ hw⟩))
    exact hqa (Ev.th.inj this)

/-- `a` is added by the completion. -/
theorem a_added (D : RvData' P τ X c a e) : a ∈ c.abs.events ∧ a ∉ (X.remove {a, e}).events := by
  have ha : a ∈ X.events := D.me.1
  have h0 : a ∉ (X.remove {a, e}).events := fun h => (D.mem_old_iff.mp h).2.1 rfl
  refine ⟨?_, h0⟩
  have hav : a ∈ P.avail (X.remove {a, e}) := by
    refine mem_avail_restrict D.hXW D.hXE ha (by simp) (fun q hq ht hi => ?_)
      (fun q hq _ hi w hw => D.src_old hq (fun h => Nat.lt_irrefl _ (h ▸ hi)) w hw) D.W0
    refine Finset.mem_sdiff.mpr ⟨hq, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => Nat.lt_irrefl _ (h ▸ hi), fun h => D.tid_ne (by rw [← ht, h])⟩
  rcases ComplStep.mem_or_avail D.W0 D.E0 D.av D.mc.1 hav with h | h
  · exact h
  · have hne : a ≠ e := fun h' => nextLt_irrefl e (h' ▸ D.lt)
    exact absurd (D.mc.2.2 a h hne) (fun h' => nextLt_irrefl _ (nextLt_trans h' D.lt))

/-- No added event is `<next`-before `a`. -/
theorem ge_a (D : RvData' P τ X c a e) {p : TEv} (hp : p ∈ c.abs.events)
    (hp0 : p ∉ (X.remove {a, e}).events) : ¬ nextLt p a := by
  obtain ⟨-, -, c2, -⟩ := ComplStep.order D.W0 D.E0 D.av D.mc.1
  obtain ⟨y, hy, hyp⟩ := c2 p hp hp0
  have hya : ¬ nextLt y a := by
    rcases rv_avail D.hXW D.hXE D.me D.rf D.po y hy with rfl | rfl | hyX
    · exact nextLt_irrefl _
    · exact fun h => nextLt_irrefl _ (nextLt_trans h D.lt)
    · exact D.hs1 y hyX _ D.me
  intro h
  rcases hyp with rfl | hyp
  · exact hya h
  · exact hya (nextLt_trans hyp h)

/-- A causal successor of an added event is added, and `<next`-after it. -/
theorem succ_added (D : RvData' P τ X c a e) {x y : TEv} (hx : x ∉ (X.remove {a, e}).events)
    (h : c.abs.porf (.th x) (.th y)) : y ∉ (X.remove {a, e}).events ∧ nextLt x y := by
  obtain ⟨-, -, -, c3, c4⟩ := ComplStep.order D.W0 D.E0 D.av D.mc.1
  exact ⟨fun hy => hx (D.W0.mem_of_porf (c4 _ _ h hy)).1, c3 x y hx h⟩

/-- An added event was inserted after every event that is `<next`-before it. -/
theorem not_lt_of_added (D : RvData' P τ X c a e) {v x : TEv} (hv : v ∈ c.abs.events)
    (hv0 : v ∉ (X.remove {a, e}).events) (hx : x ∈ c.order) (hlt : nextLt x v) :
    ¬ c.lt v x := by
  intro hlt'
  obtain ⟨s, q, hvs, hbw, hqx⟩ := D.hI.p2 x hx v (D.mem_order.mpr hv) hlt hlt'
  have hs : s ∉ (X.remove {a, e}).events ∧ (v = s ∨ nextLt v s) := by
    rcases hvs with rfl | h
    · exact ⟨hv0, Or.inl rfl⟩
    · exact ⟨(D.succ_added hv0 h).1, Or.inr (D.succ_added hv0 h).2⟩
  have hqm : q ∈ c.abs.events := D.mem_order.mp hbw.2.2.1
  have hsq : nextLt s q :=
    (D.succ_added hs.1 (Relation.TransGen.single (Or.inr ⟨q, rfl, hqm, hbw.1⟩))).2
  have hqv : nextLt q v := nextLt_trans hqx hlt
  rcases hs.2 with rfl | h
  · exact nextLt_irrefl _ (nextLt_trans hqv hsq)
  · exact nextLt_irrefl _ (nextLt_trans (nextLt_trans hqv h) hsq)

/-- On the added events the insertion order of `c` agrees with `<next`. -/
theorem lt_of_added (D : RvData' P τ X c a e) {u v : TEv} (hu : u ∈ c.order)
    (hv : v ∈ c.abs.events) (hv0 : v ∉ (X.remove {a, e}).events) (hlt : nextLt u v) :
    c.lt u v := by
  have hne : v ≠ u := fun h => nextLt_irrefl _ (h ▸ hlt)
  exact (List.Before.total (D.mem_order.mpr hv) hu hne).resolve_right
    (D.not_lt_of_added hv hv0 hu hlt)

/-- A causality path of `c.plus e` into `e` starts at an old event. -/
theorem plus_old (D : RvData' P τ X c a e) {p : TEv} (h : (c.plus e).porf (.th p) (.th e)) :
    p ∈ (X.remove {a, e}).events := by
  obtain ⟨-, -, -, -, c4⟩ := ComplStep.order D.W0 D.E0 D.av D.mc.1
  obtain ⟨u, hpu, hue⟩ := Relation.TransGen.tail'_iff.mp h
  rcases hue with hpo | ⟨q', hq', -, hrf'⟩
  swap
  · rw [← Ev.th.inj hq'] at hrf'
    have hnone : c.abs.rf e = none := D.WY.rf_none e (Or.inl D.e_not_mem)
    have hrf'' : c.abs.rf e = some u := hrf'
    rw [hnone] at hrf''
    cases hrf''
  cases u with
  | init => exact absurd hpu ((c.plus e).not_reach_init p)
  | th q =>
    obtain ⟨hqm, -, ht, hi⟩ := hpo
    have hqe : q ≠ e := fun h' => Nat.lt_irrefl _ (h' ▸ hi)
    have hqY : q ∈ c.abs.events := (Finset.mem_insert.mp hqm).resolve_left hqe
    have hq0 : q ∈ (X.remove {a, e}).events := by
      have hcnt := idx_eq_of_mem_avail D.av
      obtain ⟨q0, hq0, ht0, hi0⟩ := (D.W0.exists_idx_iff e.tid q.idx).mpr (hcnt ▸ hi)
      have : q0 = q := D.WY.idx_inj q0 (D.sub hq0) q hqY (ht0.trans ht.symm) hi0
      exact this ▸ hq0
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hpu with h' | h'
    · rw [← Ev.th.inj h']
      exact hq0
    · have hY : c.abs.porf (.th p) (.th q) := by
        rcases Maz.transGen_of_sink (r := c.abs.porfStep) (r' := (c.plus e).porfStep)
          (e := .th e) (fun _ _ h => Graph.porfStep_addWrite D.WY D.e_idx h)
          (Graph.not_porfStep_addWrite_self D.WY D.e_idx) h' with h1 | h1
        · exact h1
        · exact absurd (Ev.th.inj h1) hqe
      exact (D.W0.mem_of_porf (c4 _ _ hY hq0)).1

/-- A causality path of `X` from an old event into `e` is a path of
`c.plus e`. -/
theorem plus_of_X (D : RvData' P τ X c a e) {x : TEv} (h : X.porf (.th x) (.th e)) :
    (c.plus e).porf (.th x) (.th e) := by
  obtain ⟨u, hxu, hue⟩ := Relation.TransGen.tail'_iff.mp h
  rcases hue with hpo | ⟨q', hq', -, hrf'⟩
  swap
  · rw [← Ev.th.inj hq'] at hrf'
    exact (TEv.not_isRead_of_isWrite D.e_write (D.hXW.isRead_of_rf hrf')).elim
  cases u with
  | init => exact absurd hxu (X.not_reach_init x)
  | th q =>
    obtain ⟨hqm, -, ht, hi⟩ := hpo
    have hqe : q ≠ e := fun h' => Nat.lt_irrefl _ (h' ▸ hi)
    have hqa : q ≠ a := fun h' => D.a_sink (.th e) (Or.inl ⟨h' ▸ hqm, D.e_mem, h' ▸ ht, h' ▸ hi⟩)
    have hq0 : q ∈ (X.remove {a, e}).events := D.mem_old_iff.mpr ⟨hqm, hqa, hqe⟩
    have hlast : (c.plus e).porfStep (.th q) (.th e) :=
      Or.inl ⟨Finset.mem_insert_of_mem (D.sub hq0), Finset.mem_insert_self _ _, ht, hi⟩
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hxu with h' | h'
    · rw [Ev.th.inj h'] at hlast
      exact Relation.TransGen.single hlast
    · have h0 : (X.remove {a, e}).porf (.th x) (.th q) :=
        (Graph.porf_restrict_iff (rv_closed D.hXW D.me D.po) hq0).mpr h'
      have hY : c.abs.porf (.th x) (.th q) := Graph.porf_mono D.sub D.rfY h0
      have hP : (c.plus e).porf (.th x) (.th q) :=
        Graph.porf_mono (G := c.abs) (G' := c.plus e) (Finset.subset_insert _ _)
          (fun _ _ => rfl) hY
      exact hP.tail hlast

/-- One causality step of the graph of `c`, in terms of the insertion order:
it goes forward, or it is a backward `rf` edge; and a write with a backward
reader `u` is inserted before the target of a step from `u`. -/
theorem step_cases (D : RvData' P τ X c a e) {u u1 : TEv}
    (h : c.abs.porfStep (.th u) (.th u1)) :
    (c.lt u u1 ∨ c.Bw u u1) ∧ ∀ s, c.Bw s u → c.lt s u1 := by
  rcases h with hpo | ⟨q, hq, hqm, hrf⟩
  · exact ⟨Or.inl (D.hcpo u (D.mem_order.mpr hpo.1) u1 (D.mem_order.mpr hpo.2.1)
      hpo.2.2.1 hpo.2.2.2), fun s hbw => D.hbw hbw hpo⟩
  · rw [← Ev.th.inj hq] at hrf hqm
    have huw : u.IsWrite := D.WY.isWrite_of_src hrf
    have hne : u1 ≠ u := fun h' =>
      TEv.not_isRead_of_isWrite huw (h' ▸ D.WY.isRead_of_rf hrf)
    have hum : u ∈ c.order := D.mem_order.mpr (D.WY.rf_source_mem hrf).2
    refine ⟨?_, fun s hbw => (TEv.not_isRead_of_isWrite huw (D.WY.isRead_of_rf hbw.1)).elim⟩
    rcases List.Before.total (D.mem_order.mpr hqm) hum hne with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨hrf, h'⟩

/-- The proof of Proposition A.28, steps ⟨5⟩8-⟨5⟩16: an event with a
causality path to an event `y'` that is `<next`-before `a` and was inserted
before `a` was itself inserted before `a`. -/
theorem lt_a_of_path (D : RvData' P τ X c a e) {y' : TEv} (hlt : nextLt y' a)
    (hya : c.lt y' a) :
    ∀ b, c.abs.porf b (.th y') → ∀ u, b = .th u → c.lt u a ∧ ∀ s, c.Bw s u → c.lt s a := by
  intro b hb
  induction hb using Relation.TransGen.head_induction_on with
  | single hstep =>
    rintro u rfl
    obtain ⟨h1, h2⟩ := D.step_cases hstep
    refine ⟨?_, fun s hbw => Config.lt_trans (h2 s hbw) hya⟩
    rcases h1 with h1 | hbw
    · exact Config.lt_trans h1 hya
    · -- a backward `rf` edge into `y'`: (P6)
      have hu0 : u ∈ (X.remove {a, e}).events := by
        by_contra hu0
        have := (D.succ_added hu0 (Relation.TransGen.single hstep)).1
        have hy0 : y' ∈ (X.remove {a, e}).events := by
          by_contra hy0
          exact D.ge_a (D.mem_order.mp hya.2.1) hy0 hlt
        exact this hy0
      have hau : a ≠ u := fun h' => D.a_added.2 (h' ▸ hu0)
      have hay : a ≠ y' := fun h' => nextLt_irrefl _ (h' ▸ hlt)
      rcases D.hI.p6 u y' a hau hay hbw hlt (D.mem_order.mpr D.a_added.1) with h | h | h
      · exact absurd h (List.Before.asymm hya)
      · exact h
      · exact absurd hu0 (D.succ_added D.a_added.2 h).1
  | head hstep hrest ih =>
    rintro u rfl
    rename_i c1
    cases c1 with
    | init => exact absurd hstep (c.abs.not_porfStep_init _)
    | th u1 =>
      obtain ⟨ih1, ih2⟩ := ih u1 rfl
      obtain ⟨h1, h2⟩ := D.step_cases hstep
      refine ⟨?_, fun s hbw => Config.lt_trans (h2 s hbw) ih1⟩
      rcases h1 with h1 | hbw
      · exact Config.lt_trans h1 ih1
      · exact ih2 u hbw

/-- The proof of Proposition A.28, step ⟨2⟩2: the deleted events are the
events of `c` that are not in `X`. -/
theorem del_iff (D : RvData' P τ X c a e) (p : TEv) :
    c.Deleted a e p ↔ p ∈ c.abs.events ∧ p ∉ X.events := by
  constructor
  · rintro ⟨hpo, hap, hno⟩
    have hpY := D.mem_order.mp hpo
    refine ⟨hpY, fun hpX => ?_⟩
    have hpa : p ≠ a := (List.Before.ne hap)
    have hpe : p ≠ e := fun h => D.e_not_mem (h ▸ hpY)
    have hp0 : p ∈ (X.remove {a, e}).events := D.mem_old_iff.mpr ⟨hpX, hpa, hpe⟩
    have hap' : nextLt a p := (nextLt_total hpa).resolve_left
      (fun h => D.not_lt_of_added D.a_added.1 D.a_added.2 hpo h hap)
    have hnoX : ¬ (p = e ∨ X.porf (.th p) (.th e)) := by
      rintro (h | h)
      · exact hpe h
      · exact hno (D.plus_of_X h)
    -- an old event `y'` reached from `p`, `<next`-before `a`
    obtain ⟨y', hy0, hpy, hylt⟩ : ∃ y' ∈ (X.remove {a, e}).events,
        X.porf (.th p) (.th y') ∧ nextLt y' a := by
      obtain ⟨z, hz, hpz, hzmax⟩ :=
        Graph.exists_maximal_reach D.hXW D.hXac hpX
      by_cases hza : z = a
      · rw [hza] at hpz
        have hpa' : X.porf (.th p) (.th a) := hpz.resolve_left (Ne.symm hpa)
        obtain ⟨u, hpu, hua⟩ := Relation.TransGen.tail'_iff.mp hpa'
        rcases hua with hpo' | ⟨q', hq', -, hrf'⟩
        · cases u with
          | init => exact absurd hpu (X.not_reach_init p)
          | th q =>
            obtain ⟨hqm, -, ht, hi⟩ := hpo'
            have hqlt : nextLt q a := nextLt_of_poT ⟨ht, hi⟩
            have hqa : q ≠ a := fun h => nextLt_irrefl _ (h ▸ hqlt)
            have hpq : X.porf (.th p) (.th q) := by
              rcases Relation.reflTransGen_iff_eq_or_transGen.mp hpu with h' | h'
              · exact absurd (nextLt_trans ((Ev.th.inj h') ▸ hqlt) hap') (nextLt_irrefl _)
              · exact h'
            have hqe : q ≠ e := fun h => hnoX (Or.inr (h ▸ hpq))
            exact ⟨q, D.mem_old_iff.mpr ⟨hqm, hqa, hqe⟩, hpq, hqlt⟩
        · rw [← Ev.th.inj hq', D.rf] at hrf'
          rw [← Option.some.inj hrf'] at hpu
          rcases Relation.reflTransGen_iff_eq_or_transGen.mp hpu with h' | h'
          · exact absurd (Or.inl (Ev.th.inj h').symm) hnoX
          · exact absurd (Or.inr h') hnoX
      · have hzlt : nextLt z a := D.me.2.2 (.th z) hz hzmax (fun h => hza (Ev.th.inj h))
        have hze : z ≠ e := fun h => hzmax (.th a) (h ▸ (D.po _).mpr rfl)
        have hpz' : X.porf (.th p) (.th z) := by
          rcases hpz with h | h
          · exact absurd (nextLt_trans (h ▸ hzlt) hap') (nextLt_irrefl _)
          · exact h
        exact ⟨z, D.mem_old_iff.mpr ⟨hz, hza, hze⟩, hpz', hzlt⟩
    have hY : c.abs.porf (.th p) (.th y') :=
      Graph.porf_mono D.sub D.rfY
        ((Graph.porf_restrict_iff (rv_closed D.hXW D.me D.po) hy0).mpr hpy)
    have hyo : y' ∈ c.order := D.mem_order.mpr (D.sub hy0)
    have hya : c.lt y' a := by
      have hne : a ≠ y' := fun h => nextLt_irrefl _ (h ▸ hylt)
      exact (List.Before.total (D.mem_order.mpr D.a_added.1) hyo hne).resolve_right
        (D.not_lt_of_added D.a_added.1 D.a_added.2 hyo hylt)
    exact List.Before.asymm hap (D.lt_a_of_path hylt hya _ hY p rfl).1
  · rintro ⟨hpY, hpX⟩
    have hp0 : p ∉ (X.remove {a, e}).events := fun h => hpX (D.mem_old_iff.mp h).1
    have hpa : p ≠ a := fun h => hpX (h ▸ D.me.1)
    have hpo := D.mem_order.mpr hpY
    refine ⟨hpo, ?_, fun h => hp0 (D.plus_old h)⟩
    exact D.lt_of_added (D.mem_order.mpr D.a_added.1) hpY hp0
      ((nextLt_total hpa).resolve_left (D.ge_a hpY hp0))

/-- An added event that is `<next`-after `p` is not in `Previous(p, e)`. -/
theorem not_previous (D : RvData' P τ X c a e) {p q : TEv} (hpo : p ∈ c.order)
    (hq : q ∈ c.abs.events) (hq0 : q ∉ (X.remove {a, e}).events) (hlt : nextLt p q) :
    ¬ c.Previous p e (.th q) := by
  rintro ⟨-, (rfl | h) | h⟩
  · exact nextLt_irrefl _ hlt
  · exact List.Before.asymm h (D.lt_of_added hpo hq hq0 hlt)
  · exact hq0 (D.plus_old h)

/-- The events that the revisit keeps: the events of `c` that are in `X`. -/
theorem keep_iff (D : RvData' P τ X c a e) (p : TEv) :
    p ∈ c.keep a e ↔ p ∈ c.abs.events ∧ p ∈ X.events := by
  rw [Config.mem_keep_iff, D.del_iff, D.mem_order]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by_contra fun h => h2 ⟨h1, h⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h.2 h2⟩

/-- The context of the revisit of `a` by `e` in `c` is the context of the
backward step: the literals of `X` without `a` and `e`. -/
theorem ctx_eq (D : RvData' P τ X c a e) : c.ctx a e = (X.remove {a, e}).F := by
  have hres := (D.mc.facts D.W0 D.E0 D.av).2.2.2.2.1
  unfold Config.ctx
  refine Eq.trans ?_ (congrArg Graph.F hres).symm
  refine c.abs.F_restrict_congr (fun q hq hc => ⟨fun h => ?_, fun h => ?_⟩)
  · have hqX := ((D.keep_iff q).mp h).2
    refine D.mem_old_iff.mpr ⟨hqX, ?_, ?_⟩
    · rintro rfl
      exact hc.isLocal.not_isRead D.hs.rv_inv.2.1
    · rintro rfl
      exact D.e_not_mem hq
  · exact (D.keep_iff q).mpr ⟨hq, (D.mem_old_iff.mp h).1⟩

/-- The proof of Proposition A.28, step ⟨2⟩8: the deleted events and `a` are
maximally added. For a constraint evaluation: the events of `Previous` other
than the event are the events of the graph in which `MaxCompletion` added it
(`ComplStep.pol_added`), and the two contexts agree (`ctx_eq`). -/
theorem maxAdded (D : RvData' P τ X c a e) {p : TEv} (hp : c.Deleted a e p ∨ p = a) :
    c.IsMaximallyAdded τ (c.ctx a e) p e := by
  have hadd : p ∈ c.abs.events ∧ p ∉ (X.remove {a, e}).events := by
    rcases hp with h | rfl
    · obtain ⟨h1, h2⟩ := (D.del_iff p).mp h
      exact ⟨h1, fun h => h2 (D.mem_old_iff.mp h).1⟩
    · exact D.a_added
  obtain ⟨hpY, hp0⟩ := hadd
  have hpo := D.mem_order.mpr hpY
  have hap : p = a ∨ c.lt a p := by
    rcases hp with h | h
    · exact Or.inr h.2.1
    · exact Or.inl h
  have hco := ComplStep.co_order D.W0 D.E0 D.av D.mc.1 p hpY hp0
  -- an event of `X` without `a`, `e` is in `Previous`
  have hold : ∀ s ∈ (X.remove {a, e}).events, c.Previous p e (.th s) := by
    intro s hs0
    have hsY : s ∈ c.abs.events := D.sub hs0
    refine ⟨D.mem_order.mpr hsY, ?_⟩
    by_cases hpe : (c.plus e).porf (.th s) (.th e)
    · exact Or.inr hpe
    · left
      right
      have hsa : s ≠ a := fun h => D.a_added.2 (h ▸ hs0)
      have hnd : ¬ c.Deleted a e s := fun hd =>
        ((D.del_iff s).mp hd).2 (D.mem_old_iff.mp hs0).1
      have hsa' : c.lt s a := by
        rcases List.Before.total (D.mem_order.mpr D.a_added.1) (D.mem_order.mpr hsY)
          (Ne.symm hsa) with h | h
        · exact h
        · exact absurd ⟨D.mem_order.mpr hsY, h, hpe⟩ hnd
      rcases hap with rfl | h
      · exact hsa'
      · exact Config.lt_trans hsa' h
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨q, hprev, hrf⟩
    have hqm : q ∈ c.abs.events := (D.WY.rf_source_mem hrf).1
    obtain ⟨hq0, hlt⟩ :=
      D.succ_added hp0 (Relation.TransGen.single (Or.inr ⟨q, rfl, hqm, hrf⟩))
    exact D.not_previous hpo hqm hq0 hlt hprev
  · intro _
    by_cases hr : p.IsRead
    · obtain ⟨w, hw, hwt⟩ := D.WY.rf_read p hpY _ (TEv.IsRead.exists_act hr)
      have hw' : c.rf p = some w := hw
      refine ⟨w, fun _ => hw', fun h => absurd hr h, ?_, ?_⟩
      · cases w with
        | init => trivial
        | th s =>
          have hsY : s ∈ c.abs.events := hwt.1
          by_cases hs0 : s ∈ (X.remove {a, e}).events
          · exact hold s hs0
          · refine ⟨D.mem_order.mpr hsY, ?_⟩
            have hlt := (D.succ_added hs0
              (Relation.TransGen.single (Or.inr ⟨p, rfl, hpY, hw⟩))).2
            exact Or.inl (Or.inr (D.lt_of_added (D.mem_order.mpr hsY) hpY hp0 hlt))
      · rintro ⟨w', hprev, hcw⟩
        cases w' with
        | init => cases w <;> exact hcw
        | th w'' =>
          obtain ⟨hw0, hlt⟩ := hco w (fun _ => hw) (fun h => absurd hr h) w'' hcw
          have hwY : w'' ∈ c.abs.events := by
            cases w with
            | init => exact ((D.WY.co_mem _ _).mp hcw).1
            | th s => exact ((D.WY.co_mem _ _).mp hcw.2.1).1
          exact D.not_previous hpo hwY hw0 hlt hprev
    · refine ⟨.th p, fun h => absurd h hr, fun _ => rfl, ⟨hpo, Or.inl (Or.inl rfl)⟩, ?_⟩
      rintro ⟨w', hprev, hcw⟩
      cases w' with
      | init => exact hcw
      | th w'' =>
        obtain ⟨hw0, hlt⟩ := hco (.th p) (fun h => absurd h hr) (fun _ => rfl) w'' hcw
        have hwY : w'' ∈ c.abs.events := ((D.WY.co_mem _ _).mp hcw.2.1).1
        exact D.not_previous hpo hwY hw0 hlt hprev
  · intro φ hact
    classical
    rw [D.ctx_eq]
    unfold Config.prevF
    refine ComplStep.pol_added D.W0 D.E0 D.av D.mc.1 p hpY hp0 φ hact _ (fun q hq hc => ?_)
    rw [Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨-, hqp, hprev⟩
      by_cases hq0 : q ∈ (X.remove {a, e}).events
      · exact Or.inl hq0
      · right
        rcases nextLt_total hqp with h | h
        · exact h
        · exact absurd hprev (D.not_previous hpo hq hq0 h)
    · rintro (hq0 | hlt)
      · exact ⟨D.mem_order.mpr hq, fun h => hp0 (h ▸ hq0), hold q hq0⟩
      · have hqo := D.mem_order.mpr hq
        exact ⟨hqo, fun h => nextLt_irrefl _ (h ▸ hlt), hqo,
          Or.inl (Or.inr (D.lt_of_added hqo hpY hp0 hlt))⟩

/-- The proof of Proposition A.28, steps ⟨2⟩3-⟨2⟩6 and ⟨2⟩9: the revisit of
`a` by `e`, with `e` placed after its coherence predecessor in `X`, is a step
of Algorithm 1 from `c`, and it gives `X`. -/
theorem step (D : RvData' P τ X c a e) :
    ∃ wp, P.IsNext c.abs e ∧ e.IsWrite ∧ a ∈ c.order ∧ a.act = .read e.loc ∧
      ¬ (c.plus e).porf (.th a) (.th e) ∧
      (∀ p, (c.Deleted a e p ∨ p = a) → c.IsMaximallyAdded τ (c.ctx a e) p e) ∧
      (c.abs.restrict (c.keep a e)).IsWriteTo e.loc wp ∧ (c.revisit a e wp).abs = X := by
  obtain ⟨x, v, hax, hev⟩ := D.acts
  have hloc : e.loc = x := by simp [TEv.loc, hev, Act.loc]
  obtain ⟨wp, hwp, hco⟩ := Graph.remove_addWrite_co D.hXW D.e_mem D.e_write
  have hres := (D.mc.facts D.W0 D.E0 D.av).2.2.2.2.1
  have hkeep : ∀ p, p ∈ c.keep a e ↔ p ∈ c.abs.events ∧ p ∈ X.events := D.keep_iff
  have hold_keep : ∀ p ∈ (X.remove {a, e}).events, p ∈ c.keep a e := fun p hp =>
    (hkeep p).mpr ⟨D.sub hp, (D.mem_old_iff.mp hp).1⟩
  have hwr_old : ∀ p ∈ X.events, p.IsWrite → p ≠ e → p ∈ (X.remove {a, e}).events :=
    fun p hp hw hpe => D.mem_old_iff.mpr
      ⟨hp, fun h => TEv.not_isRead_of_isWrite (h ▸ hw) D.hs.rv_inv.2.1, hpe⟩
  -- the coherence lists of the kept part of `c` are those of `X` without `e`
  have hWco : (c.abs.restrict (c.keep a e)).co = (X.remove {e}).co := by
    funext y
    have h1 : (X.remove {a, e}).co y =
        (c.abs.co y).filter (fun b => b ∈ (X.remove {a, e}).events) :=
      congrArg (fun H : Graph => H.co y) hres
    have h2 : (X.remove {a, e}).co y = (X.co y).filter (fun b => decide (b ≠ e)) := by
      change (X.co y).filter (fun b => decide (b ∈ X.events \ {a, e})) = _
      apply List.filter_congr
      intro b hb
      obtain ⟨hbm, v', hv'⟩ := (D.hXW.co_mem y b).mp hb
      have hba : b ≠ a := by
        rintro rfl
        rw [hax] at hv'
        cases hv'
      simp [hbm, hba]
    have h3 : (c.abs.co y).filter (fun b => decide (b ∈ c.keep a e)) =
        (c.abs.co y).filter (fun b => decide (b ∈ (X.remove {a, e}).events)) := by
      apply List.filter_congr
      intro b hb
      obtain ⟨hbm, v', hv'⟩ := (D.WY.co_mem y b).mp hb
      have hiff : b ∈ c.keep a e ↔ b ∈ (X.remove {a, e}).events :=
        ⟨fun h => hwr_old b ((hkeep b).mp h).2 (by simp [TEv.IsWrite, hv', Act.IsWrite])
          (fun h' => D.e_not_mem (h' ▸ hbm)), hold_keep b⟩
      simp [hiff]
    rw [Graph.remove_singleton_co D.hXW]
    exact h3.trans (h1.symm.trans h2)
  -- the new graph is `X`
  have hG : ((c.abs.restrict (c.keep a e)).addWrite e wp).setRF a (.th e) = X := by
    apply Graph.ext
    · exact (congrArg Graph.mem hres).symm
    · change insert e (c.abs.events ∩ c.keep a e) = X.events
      ext p
      simp only [Finset.mem_insert, Finset.mem_inter, hkeep]
      constructor
      · rintro (rfl | ⟨-, -, h⟩)
        · exact D.e_mem
        · exact h
      · intro hpX
        by_cases hpe : p = e
        · exact Or.inl hpe
        · right
          by_cases hpa : p = a
          · rw [hpa]
            exact ⟨D.a_added.1, D.a_added.1, D.me.1⟩
          · have := D.sub (D.mem_old_iff.mpr ⟨hpX, hpa, hpe⟩)
            exact ⟨this, this, hpX⟩
    · funext q
      rw [Graph.setRF_rf, Graph.addWrite_rf]
      by_cases hqa : q = a
      · rw [hqa, Function.update_self, D.rf]
      · rw [Function.update_of_ne hqa]
        by_cases hq0 : q ∈ (X.remove {a, e}).events
        · have hqX := (D.mem_old_iff.mp hq0).1
          have hYq := D.rfY q hq0
          have hX0q : (X.remove {a, e}).rf q = X.rf q :=
            X.restrict_rf_of_source_kept hq0 (fun w hw => D.src_old hqX hqa w hw)
          have hWq : (c.abs.restrict (c.keep a e)).rf q = c.abs.rf q := by
            refine c.abs.restrict_rf_of_source_kept
              (Finset.mem_inter.mpr ⟨D.sub hq0, hold_keep q hq0⟩) (fun w hw => ?_)
            rw [hYq] at hw
            cases w with
            | init => trivial
            | th w' => exact hold_keep w' (D.W0.rf_source_mem hw).2
          rw [hWq, hYq, hX0q]
        · have hW : (c.abs.restrict (c.keep a e)).rf q = none := by
            refine c.abs.restrict_rf_of_not_mem (fun h => ?_)
            obtain ⟨hqY, hqk⟩ := Finset.mem_inter.mp h
            exact hq0 (D.mem_old_iff.mpr
              ⟨((hkeep q).mp hqk).2, hqa, fun h' => D.e_not_mem (h' ▸ hqY)⟩)
          rw [hW]
          by_cases hqX : q ∈ X.events
          · have hqe : q = e := by
              by_contra hqe
              exact hq0 (D.mem_old_iff.mpr ⟨hqX, hqa, hqe⟩)
            rw [hqe, D.hXW.rf_none e (Or.inr D.e_write.not_isRead)]
          · rw [D.hXW.rf_none q (Or.inl hqX)]
    · have h1 : ((c.abs.restrict (c.keep a e)).addWrite e wp).co =
          ((X.remove {e}).addWrite e wp).co := by
        simp only [Graph.addWrite]
        rw [hWco]
      exact h1.trans hco
    · funext q
      change (c.abs.restrict (c.keep a e)).pol q = X.pol q
      rw [Graph.restrict_pol]
      by_cases hq0 : q ∈ (X.remove {a, e}).events
      · have hqk : q ∈ c.abs.events ∩ c.keep a e :=
          Finset.mem_inter.mpr ⟨D.sub hq0, hold_keep q hq0⟩
        simp only [hqk, ↓reduceIte]
        have h1 : (X.remove {a, e}).pol q = c.abs.pol q := by
          rw [congrArg (fun H : Graph => H.pol q) hres]
          simp only [Graph.restrict_pol]
          have : q ∈ c.abs.events ∩ (X.remove {a, e}).events :=
            Finset.mem_inter.mpr ⟨D.sub hq0, hq0⟩
          simp only [this, ↓reduceIte]
        have h2 : (X.remove {a, e}).pol q = X.pol q := by
          change (X.restrict (X.events \ {a, e})).pol q = X.pol q
          rw [Graph.restrict_pol]
          have : q ∈ X.events ∩ (X.events \ {a, e}) := hq0
          simp only [this, ↓reduceIte]
        rw [← h1, h2]
      · -- `q` is not a constraint evaluation of `X`: no outcome on either side
        have hXq : X.pol q = none := by
          by_contra h
          obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h
          obtain ⟨hqX, hqc⟩ := D.hXW.pol_some hb
          refine hq0 (D.mem_old_iff.mpr ⟨hqX, ?_, ?_⟩)
          · rintro rfl
            exact hqc.isLocal.not_isRead D.hs.rv_inv.2.1
          · rintro rfl
            exact hqc.isLocal.not_isWrite D.e_write
        rw [hXq]
        by_cases hqk : q ∈ c.abs.events ∩ c.keep a e
        · simp only [hqk, ↓reduceIte]
          by_contra h
          obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h
          obtain ⟨hqY, hqc⟩ := D.WY.pol_some hb
          have hqX := ((hkeep q).mp (Finset.mem_inter.mp hqk).2).2
          refine hq0 (D.mem_old_iff.mpr ⟨hqX, ?_, ?_⟩)
          · rintro rfl
            exact hqc.isLocal.not_isRead D.hs.rv_inv.2.1
          · rintro rfl
            exact hqc.isLocal.not_isWrite D.e_write
        · simp only [hqk, ↓reduceIte]
  have hWT : (c.abs.restrict (c.keep a e)).IsWriteTo e.loc wp := by
    cases wp with
    | init => trivial
    | th p =>
      obtain ⟨hpm, hpw⟩ := hwp
      have hpm' : p ∈ X.events ∩ (X.events \ {e}) := hpm
      have hpX : p ∈ X.events := (Finset.mem_inter.mp hpm').1
      have hpe : p ≠ e := fun h =>
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hpm').2).2 (Finset.mem_singleton.mpr h)
      obtain ⟨v', hv'⟩ := hpw
      have hp0 := hwr_old p hpX (by simp [TEv.IsWrite, hv', Act.IsWrite]) hpe
      exact ⟨Finset.mem_inter.mpr ⟨D.sub hp0, hold_keep p hp0⟩, v', hv'⟩
  have habs : (c.revisit a e wp).abs = X := by
    rw [Config.revisit_abs]
    exact hG
  exact ⟨wp, D.mc.2, D.e_write, D.mem_order.mpr D.a_added.1, by rw [hloc]; exact hax,
    fun h => D.a_added.2 (D.plus_old h), fun p hp => D.maxAdded hp, hWT, habs⟩

/-- B5. The coherence order that `MaxCompl` builds: the order of the graph it
starts from, then the added writes in the insertion order of `c` (which is
`<next` on them). The added writes are the deleted writes. -/
theorem co_eq (D : RvData' P τ X c a e) (x : Loc) :
    c.abs.co x = (X.remove {a, e}).co x ++
      c.order.reverse.filter (fun d => @decide (c.Deleted a e d) (Classical.propDecidable _) &&
        d.writesTo x) := by
  classical
  have hres : X.remove {a, e} = c.abs.restrict (X.remove {a, e}).events :=
    (D.mc.facts D.W0 D.E0 D.av).2.2.2.2.1
  have hco := ComplStep.co_order D.W0 D.E0 D.av D.mc.1
  -- the deleted events are the added events
  have hdel : ∀ p, c.Deleted a e p → p ∈ c.abs.events ∧ p ∉ (X.remove {a, e}).events := by
    intro p hp
    obtain ⟨h1, h2⟩ := (D.del_iff p).mp hp
    exact ⟨h1, fun h => h2 (D.mem_old_iff.mp h).1⟩
  have hmemD : ∀ {q : TEv}, q ∈ c.order.reverse.filter
      (fun d => @decide (c.Deleted a e d) (Classical.propDecidable _) && d.writesTo x) ↔
      c.Deleted a e q ∧ ∃ v, q.act = .write x v := by
    intro q
    simp only [List.mem_filter, List.mem_reverse, Bool.and_eq_true, decide_eq_true_eq,
      TEv.writesTo_iff]
    exact ⟨fun h => h.2, fun h => ⟨h.1.1, h⟩⟩
  have hloc : ∀ {q : TEv}, (∃ v, q.act = .write x v) → q.loc = x ∧ ¬ q.IsRead := by
    rintro q ⟨v, hv⟩
    simp [TEv.loc, TEv.IsRead, hv, Act.loc, Act.IsRead]
  -- an added write is not coherence-before an old write, and two added writes
  -- are in coherence in their `<next` order
  have hadded : ∀ {v u : TEv}, c.Deleted a e v → (∃ w, v.act = .write x w) →
      (c.abs.co x).Before v u → u ∉ (X.remove {a, e}).events ∧ nextLt v u := by
    intro v u hv hvw hb
    obtain ⟨hvE, hv0⟩ := hdel v hv
    obtain ⟨hl, hnr⟩ := hloc hvw
    refine hco v hvE hv0 (.th v) (fun h => absurd h hnr) (fun _ => rfl) u ?_
    rw [hl]
    exact hb
  have hKco : (X.remove {a, e}).co x =
      (c.abs.co x).filter (fun q => q ∈ (X.remove {a, e}).events) := by
    conv_lhs => rw [hres]
    rfl
  refine List.Perm.eq_of_pairwise (le := fun u v => ¬ (c.abs.co x).Before v u) ?_ ?_ ?_ ?_
  · intro u v hu hv h1 h2
    by_contra hne
    have hv' : v ∈ c.abs.co x := by
      rcases List.mem_append.mp hv with h | h
      · rw [hKco] at h
        exact (List.mem_filter.mp h).1
      · obtain ⟨hd, hw⟩ := hmemD.mp h
        exact (D.WY.co_mem x v).mpr ⟨(hdel v hd).1, hw⟩
    rcases List.Before.total hu hv' hne with h | h
    · exact h2 h
    · exact h1 h
  · exact (List.Nodup.pairwise_before (D.WY.co_nodup x)).imp
      (fun h => List.Before.asymm h)
  · rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [hKco]
      exact ((List.Nodup.pairwise_before (D.WY.co_nodup x)).imp
        (fun h => List.Before.asymm h)).filter _
    · have hp0 := List.Nodup.pairwise_before D.hcW.2
      have hp1 : c.order.reverse.Pairwise (fun u v => c.order.Before v u) :=
        List.pairwise_reverse.mpr hp0
      refine (hp1.filter _).imp_of_mem ?_
      intro u v hu hv hlt hb
      obtain ⟨hud, huw⟩ := hmemD.mp hu
      obtain ⟨hvd, hvw⟩ := hmemD.mp hv
      obtain ⟨-, hnl⟩ := hadded hvd hvw hb
      have := D.lt_of_added (D.mem_order.mpr (hdel v hvd).1) (hdel u hud).1 (hdel u hud).2 hnl
      exact List.Before.asymm hlt this
    · intro u hu v hv hb
      obtain ⟨hvd, hvw⟩ := hmemD.mp hv
      exact (hadded hvd hvw hb).1 ((D.W0.co_mem x u).mp hu).1
  · refine (List.perm_ext_iff_of_nodup (D.WY.co_nodup x) ?_).mpr (fun q => ?_)
    · refine List.Nodup.append (D.W0.co_nodup x)
        ((List.nodup_reverse.mpr D.hcW.2).filter _) ?_
      intro q h1 h2
      exact (hdel q (hmemD.mp h2).1).2 ((D.W0.co_mem x q).mp h1).1
    · rw [List.mem_append, D.WY.co_mem x q, D.W0.co_mem x q, hmemD]
      constructor
      · rintro ⟨hq, hw⟩
        by_cases hq0 : q ∈ (X.remove {a, e}).events
        · exact Or.inl ⟨hq0, hw⟩
        · right
          refine ⟨(D.del_iff q).mpr ⟨hq, fun hqX => hq0 (D.mem_old_iff.mpr ⟨hqX, ?_, ?_⟩)⟩, hw⟩
          · rintro rfl
            obtain ⟨x', -, hax, -⟩ := D.acts
            obtain ⟨v, hv⟩ := hw
            rw [hax] at hv
            cases hv
          · rintro rfl
            exact D.e_not_mem hq
      · rintro (⟨hq, hw⟩ | ⟨hq, hw⟩)
        · exact ⟨D.sub hq, hw⟩
        · exact ⟨(hdel q hq).1, hw⟩

end RvData'

/-! ### A backward step into a reached configuration is a step -/

variable {γ : CoChoice (M.sym S)}

/-- `(G.rf ∩ >); G.po ⊆ <` for the reached configurations of the reads-from
version (`Reach.bw_po_lt`). -/
theorem ReachR.bw_po_lt {c : Config} (h : ReachR P (M.sym S) γ τ c) {s q p : TEv}
    (hbw : c.Bw s q) (hpo : c.abs.po (.th q) (.th p)) : c.lt s p := by
  obtain ⟨hw, hpoLt, -, hcons, -⟩ := h.sound
  obtain ⟨hqm, hpm, ht, hi⟩ := hpo
  have hqo : q ∈ c.order := List.mem_toFinset.mp hqm
  have hpo' : p ∈ c.order := List.mem_toFinset.mp hpm
  have hqp : c.lt q p := hpoLt q hqo p hpo' ht hi
  have hst1 : c.abs.porfStep (.th s) (.th q) := Or.inr ⟨q, rfl, hqm, hbw.1⟩
  have hst2 : c.abs.porfStep (.th q) (.th p) := Or.inl ⟨hqm, hpm, ht, hi⟩
  have hsp : c.abs.porf (.th s) (.th p) :=
    Relation.TransGen.trans (Relation.TransGen.single hst1) (Relation.TransGen.single hst2)
  have hps : p ≠ s := fun h' => (M.sym S).rf.porf_irrefl hw.1 hcons (.th s) (h' ▸ hsp)
  have hpq : p ≠ q := fun h' => List.Before.irrefl _ _ (h' ▸ hqp)
  rcases h.inv.p6 s q p hps hpq hbw (Or.inr (Or.inl ⟨ht, hi⟩)) hpo' with h1 | h1 | h1
  · exact absurd hqp (List.Before.asymm h1)
  · exact h1
  · exact absurd (Relation.TransGen.trans hsp h1) ((M.sym S).rf.porf_irrefl hw.1 hcons (.th s))

/-- Proposition A.28, the case of a non-revisit step. -/
theorem ReachR.step_of_prevStepR_nr {Gf X : Graph} {c : Config} {e : TEv}
    (hM : M.Extensible) (hGf : Gf.Wf) (hEf : P.Exec Gf) (hcan : Gf.IsCanon)
    (hcf : (M.sym S).rf.cons Gf) (hff : P.Full Gf)
    (hX : PrevReachR P γ τ Gf X) (hc : ReachR P (M.sym S) γ τ c)
    (hs : PrevStepR P γ τ X e .nr c.abs) :
    ∃ c', StepR P (M.sym S) γ τ c e .nr c' ∧ c'.abs = X := by
  obtain ⟨hXW, -, hXcan, hXc⟩ := PrevReachR.inv hM hGf hEf hcan hcf hX
  obtain ⟨-, -, -, hcc, -⟩ := hc.sound
  have hnext := PrevReachR.next_of_prevStep hM hGf hEf hcan hcf hff hX hs
  obtain ⟨hme, habs, -⟩ := hs.nr_inv
  have he : e ∈ X.events := hme.1
  have hsink : ∀ q, X.rf q ≠ some (.th e) := by
    intro q hq
    exact hme.2.1 (.th q)
      (Relation.TransGen.single (Or.inr ⟨q, rfl, (hXW.rf_source_mem hq).1, hq⟩))
  rcases e.act.isRead_or_isWrite_or_isLocal with hk | hw | hk
  · have hact := TEv.IsRead.exists_act hk
    obtain ⟨w, hrf, hwt⟩ := hXW.rf_read e he _ hact
    have hdec : (c.addRead e w).abs = X := by
      rw [Config.addRead_abs, habs]
      exact Graph.remove_addRead hXW he hact hrf hsink
    have hwt' : c.abs.IsWriteTo e.loc w := by
      rw [habs]
      cases w with
      | init => trivial
      | th w' =>
        refine ⟨Finset.mem_inter.mpr ⟨hwt.1, Finset.mem_sdiff.mpr ⟨hwt.1, ?_⟩⟩, hwt.2⟩
        rw [Finset.mem_singleton]
        rintro rfl
        obtain ⟨v, hv⟩ := hwt.2
        exact absurd (hact.symm.trans hv) (by simp)
    exact ⟨c.addRead e w, StepR.nr (StepL.read hcc hnext hact hwt' (hdec ▸ hXc))
      (by rw [hdec]; exact hXcan), hdec⟩
  · obtain ⟨wp, hwp, hco⟩ := Graph.remove_addWrite_co hXW he hw
    have hdec : (c.addWrite e wp).abs = X := by
      rw [Config.addWrite_abs, habs]
      apply Graph.ext
      · rfl
      · exact Graph.remove_singleton_insert he
      · funext q
        rw [Graph.addWrite_rf]
        by_cases hqe : q = e
        · rw [hqe, hXW.rf_none e (Or.inr hw.not_isRead)]
          exact X.restrict_rf_of_not_mem (by simp)
        · exact Graph.remove_singleton_rf hXW hqe (hsink q)
      · exact hco
      · exact Graph.remove_singleton_pol hXW (fun h => h.isLocal.not_isWrite hw)
    exact ⟨c.addWrite e wp, StepR.nr (StepL.write hcc hnext hw (habs ▸ hwp) (hdec ▸ hXc))
      (by rw [hdec]; exact hXcan), hdec⟩
  · have hdec : (c.addLoc e (X.pol e)).abs = X := by
      rw [Config.addLoc_abs, habs]
      exact Graph.remove_addLoc hXW he hk hsink
    by_cases hcs : e.IsCons
    · obtain ⟨b, hb⟩ := hXW.exists_pol he hcs
      rw [hb] at hdec
      exact ⟨_, StepR.nr (StepL.sym hcc hnext hcs (hdec ▸ hXc)) (by rw [hdec]; exact hXcan), hdec⟩
    · have hb : X.pol e = none := by
        by_contra h
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h
        exact hcs (hXW.pol_some hb).2
      rw [hb] at hdec
      exact ⟨_, StepR.nr (StepL.loc hcc hnext hk hcs (hdec ▸ hXc)) (by rw [hdec]; exact hXcan),
        hdec⟩

/-- Proposition A.28, the case of a revisit step. -/
theorem ReachR.step_of_prevStepR_rv {Gf X : Graph} {c : Config} {a e : TEv}
    (hM : M.Extensible) (hGf : Gf.Wf) (hEf : P.Exec Gf) (hcan : Gf.IsCanon)
    (hcf : (M.sym S).rf.cons Gf) (hff : P.Full Gf)
    (hX : PrevReachR P γ τ Gf X) (hc : ReachR P (M.sym S) γ τ c)
    (hs : PrevStepR P γ τ X e (.rv a) c.abs) :
    ∃ c', StepR P (M.sym S) γ τ c e (.rv a) c' ∧ c'.abs = X := by
  classical
  obtain ⟨hXW, hXE, hXcan, hXc⟩ := PrevReachR.inv hM hGf hEf hcan hcf hX
  obtain ⟨hcw, hcpo, hccan, hcc, -⟩ := hc.sound
  obtain ⟨hme, hr, hrf, hlt, hpo, H, hmc, hcH⟩ := hs.rv_inv
  obtain ⟨-, hWγ, hE0, hav⟩ := rv_removeR (γ := γ) hXW hXE hme hrf hpo
  obtain ⟨hHW, -, -, -, hresH, -, -⟩ := hmc.facts hWγ hE0 hav
  have hX'W := Graph.liftCo_wf (γ := γ) hXW hXE hme hr hrf hpo
  have hrem := Graph.liftCo_remove (γ := γ) hXW hXE hme hrf hpo
  have habsH : (c.withCo H.co).abs = H := by
    rw [Config.withCo_abs, hcH]
    rfl
  have hs' : PrevStep P τ (X.withCo (X.liftCo γ a e)) e (.rv a) (c.withCo H.co).abs := by
    rw [habsH]
    refine PrevStep.rv hme hr hrf hlt hpo ?_
    rw [hrem]
    exact hmc
  have D : RvData' P τ (X.withCo (X.liftCo γ a e)) (c.withCo H.co) a e :=
    { hXW := hX'W
      hXE := hXE
      hXac := (M.sym S).rf.porf_acyclic X hXW hXc
      hs1 := fun y hy m hm => PrevReachR.s1 hM hGf hEf hcan hcf hff hX hy hm
      hcW := ⟨habsH ▸ hHW, hcw.2⟩
      hcpo := hcpo
      hI := hc.inv.withCo _
      hbw := fun hb hp => hc.bw_po_lt hb hp
      hs := hs' }
  obtain ⟨wp, hnext, hw, hao, hact, hnp, hmax, -, habs⟩ := D.step
  -- B5: the order that `MaxCompl` built is the order of line 16
  have hkept : c.kept0 a e = (X.remove {a, e}).canon := by
    have h1 : c.abs.restrict (c.keep a e \ {a}) = (H.restrict (c.keep a e \ {a})).canon := by
      rw [hcH, Graph.canon_restrict]
    have h2 : H.restrict (c.keep a e \ {a}) = H.restrict (X.remove {a, e}).events := by
      refine hHW.restrict_congr ?_
      ext p
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · rintro ⟨hpH, hpk, hpa⟩
        have hpX : p ∈ X.events := ((D.keep_iff p).mp hpk).2
        have hpe : p ≠ e := fun h => D.e_not_mem (by rw [habsH, ← h]; exact hpH)
        exact ⟨hpH, D.mem_old_iff.mpr ⟨hpX, hpa, hpe⟩⟩
      · rintro ⟨hpH, hp0⟩
        obtain ⟨hpX, hpa, -⟩ := D.mem_old_iff.mp hp0
        exact ⟨hpH, (D.keep_iff p).mpr ⟨by rw [habsH]; exact hpH, hpX⟩, hpa⟩
    have h3 : H.restrict (X.remove {a, e}).events = γ.apply (X.remove {a, e}) := hresH.symm
    change c.abs.restrict (c.keep a e \ {a}) = _
    rw [h1, h2, h3]
    rfl
  have hstar : c.withCo H.co = c.star γ a e := by
    unfold Config.star
    congr 1
    funext x
    have h1 := D.co_eq x
    have h2 : ((X.withCo (X.liftCo γ a e)).remove {a, e}).co x = γ.co (c.kept0 a e) x := by
      rw [hrem, hkept]
      change γ.co (X.remove {a, e}) x =
        γ.co ((X.remove {a, e}).withCo (canonCo (X.remove {a, e}).events)) x
      rw [γ.congr]
    rw [h2] at h1
    exact h1
  have hmax' : ∀ p, (c.Deleted a e p ∨ p = a) →
      (c.star γ a e).IsMaximallyAdded τ (c.ctx a e) p e := by
    intro p hp
    have := hmax p hp
    rw [hstar] at this
    exact this
  have hres : (c.revisit a e .init).canon.abs = X := by
    have h1 : ((c.withCo H.co).revisit a e wp).abs.RfEq (c.revisit a e .init).abs :=
      ⟨rfl, rfl, rfl, rfl⟩
    rw [Config.canon_abs, ← h1.canon_eq, habs]
    exact hXcan.canon_eq
  exact ⟨_, StepR.rv hcc hnext hw hao hact hnp hmax' (by rw [hres]; exact hXc), hres⟩

/-- Proposition A.28: a backward step into the graph of a reached
configuration is matched by a step of the reads-from version from that
configuration, with the same event and kind. -/
theorem ReachR.step_of_prevStepR {Gf X : Graph} {c : Config} {e : TEv} {k : Kind}
    (hM : M.Extensible) (hGf : Gf.Wf) (hEf : P.Exec Gf) (hcan : Gf.IsCanon)
    (hcf : (M.sym S).rf.cons Gf) (hff : P.Full Gf)
    (hX : PrevReachR P γ τ Gf X) (hc : ReachR P (M.sym S) γ τ c)
    (hs : PrevStepR P γ τ X e k c.abs) :
    ∃ c', StepR P (M.sym S) γ τ c e k c' ∧ c'.abs = X := by
  cases k with
  | nr => exact ReachR.step_of_prevStepR_nr hM hGf hEf hcan hcf hff hX hc hs
  | rv a => exact ReachR.step_of_prevStepR_rv hM hGf hEf hcan hcf hff hX hc hs

/-- Lemma A.29. -/
theorem PrevReachR.reach {Gf X : Graph} (hM : M.Extensible) (hGf : Gf.Wf) (hEf : P.Exec Gf)
    (hcan : Gf.IsCanon) (hcf : (M.sym S).rf.cons Gf) (hff : P.Full Gf)
    (hX : PrevReachR P γ τ Gf X)
    (h0 : Relation.ReflTransGen (fun G G' => ∃ e k, PrevStepR P γ τ G e k G') X
      (Graph.init P.mem)) :
    ∃ c, ReachR P (M.sym S) γ τ c ∧ c.abs = X := by
  revert hX
  induction h0 using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _
    exact ⟨Config.init P.mem, Relation.ReflTransGen.refl, Config.init_abs _⟩
  | head hs _ ih =>
    intro hX
    obtain ⟨e, k, hs⟩ := hs
    obtain ⟨c, hc, habs⟩ := ih (hX.tail ⟨e, k, hs⟩)
    rw [← habs] at hs
    obtain ⟨c', hst, h'⟩ := ReachR.step_of_prevStepR hM hGf hEf hcan hcf hff hX hc hs
    exact ⟨c', hc.tail ⟨e, k, hst⟩, h'⟩

/-- Completeness for canonical graphs. -/
theorem completeR_canon {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible) {Gf : Graph}
    (hGf : Gf.Wf) (hEf : P.Exec Gf) (hcan : Gf.IsCanon) (hcf : (M.sym S).rf.cons Gf)
    (hff : P.Full Gf) : ∃ c, ReachR P (M.sym S) γ τ c ∧ c.abs = Gf :=
  PrevReachR.reach hM hGf hEf hcan hcf hff Relation.ReflTransGen.refl
    (PrevReachR.init hM hGf hEf hcan hcf hff hn)

/-- Theorem 4 for the reads-from version: the algorithm reaches every
well-formed full execution of a bounded program that is consistent for some
coherence order, up to the coherence order. -/
theorem completeR {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible) {Gf : Graph} (hGf : Gf.Wf)
    (hEf : P.Exec Gf) (hcf : (M.sym S).rf.cons Gf) (hff : P.Full Gf) :
    ∃ c, ReachR P (M.sym S) γ τ c ∧ c.abs.RfEq Gf := by
  obtain ⟨c, hc, habs⟩ := completeR_canon (γ := γ) (τ := τ) hn hM hGf.canon
    ((Program.exec_withCo P _ _).mpr hEf) (Graph.canon_isCanon Gf)
    ((Model.rf_cons_congr (Graph.rfEq_canon Gf)).mp hcf) hff
  refine ⟨c, hc, ?_⟩
  rw [habs]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Condpor
