import Mazurkiewicz.Condpor.Prev

/-!
# The backward steps reach the initial graph

Paper: Appendix A, Def. A.14 (second part), Lemma A.25, Proposition A.26.
Coq: `trust/Prev.v`, section `Terminate` (`Prev_step_RW`, `RV_hb_LR`, `RV_RV`,
`RV_in_Gf`, `RW_dec`, `G0_prev_Gf`).

Proposition A.26: from every well-formed, consistent, full execution `G_f` of
a bounded program, repeated backward steps reach the graph without thread
events. With completeness of one step (M8) this gives that Algorithm 1
reaches `G_f`.

How the text is read here.

* Def. A.14 lifts the backward step to pairs with a set `RW`. The graph that
  `Prev` returns carries `RW ∪ {e}`, where `e` is the revisiting write of a
  revisit step: `PrevStepRW`, with `Kind.rw` as for the forward step
  (Def. A.4). This is the orientation of the proofs of A.25 and A.26 and of
  Coq's `REVISIT_RW`. In the printed Def. A.14 the equation `G ⇝ G' ⇔
  Prev(G) = ⟨G', e, t⟩` has the two graphs the other way round than those
  proofs use them.
* Lemma A.25 says that `RW` strictly contains `RW'` for a revisit step, i.e.
  the revisiting write `e` of a backward revisit step from `G` is not yet in
  the set collected on the way from `G_f` to `G`: `PrevReachRW.a25`.
* The paper's proof of A.25 uses two facts about a graph `Ĝ` and an event `e`
  that was added back by `MaxCompletion`: `me(Ĝ)` is not `<next`-before `e`,
  and no causal successor of `e` is `<next`-before `e` (step ⟨2⟩9). The
  first follows from the second when `e` is in the graph
  (`Graph.NoEarlierSucc.me_ge`). The second, together with "or `e` is not in
  the graph", is `Graph.NoEarlierSucc`; it is kept by every backward step
  (`PrevStep.noEarlierSucc`) and fails for the revisiting write of a revisit
  step (`PrevStep.not_noEarlierSucc`). The induction here starts at the step
  where `e` was the revisiting write (after it `e` is not in the graph),
  in place of the paper's search for the first graph without `e`
  (⟨2⟩3-⟨2⟩8). The same argument gives that a revisiting write is an event
  of `G_f` (Coq's `RV_in_Gf`), which bounds `RW`.
* One claim in the paper's proof of A.25 is false as printed and is repaired
  here. Step ⟨3⟩2, case `t' = rv b` (⟨4⟩2, ⟨5⟩3) says that all events that
  `MaxCompletion` adds are `<next`-after `me(Ĝ) = b`. Example: thread 0 is
  `b = R x`, thread 1 is `p = W x 1`, and `b` reads from `p`. Then
  `me = b`; the backward revisit step removes `b` and `p`, and the completion
  adds `b` itself (reading the initial value) before it stops at `p`. What
  holds: no added event is `<next`-before `b`, and the added events are
  `<next`-increasing in the order of their addition (`ComplStep.order`). This
  is enough, since the tracked event `e` satisfies `e <next b`. The proof also
  uses, without saying so, that a causality path that ends in an old event
  runs through old events only (`ComplStep.order`, last clause).
* Proposition A.26 is stated in the form `PrevReach P τ G_f (Graph.init P.mem)`,
  for a bounded program. The proof is the paper's with its directions
  corrected: the paper's sketch says that `⟨|RW|, -|G.E|⟩` "strictly increases
  with each application and is bounded below", and step ⟨1⟩2 prints the
  comparison in the direction opposite to its two cases. Here the measure
  `|RW| * (K + 1) + (K - |G.E|)`, with `K` the bound on the number of events,
  increases with each backward step and is bounded above by `K * (K + 1) + K`,
  since `RW ⊆ G_f.E`; `Prev` is defined on every graph with a thread event
  (`exists_prevStep`).
* Left for the next milestones: that each backward step is matched by a step
  of Algorithm 1 (M8, with the facts on what `MaxCompletion` adds), and the
  converse with uniqueness (M9; `PrevStep.det` is the part already here).
-/

namespace Condpor

open Program

variable {P : Program} {M : Model} {S : Solver} {τ : TieBreak S}
  {p : Finset Lit → SExpr → Bool}

/-- A backward step on pairs with the set `RW` (Def. A.14). -/
def PrevStepRW (P : Program) {S : Solver} (τ : TieBreak S) (x y : Graph × Finset TEv) : Prop :=
  ∃ e k, PrevStep P τ x.1 e k y.1 ∧ y.2 = k.rw e x.2

/-- The pairs obtained from `⟨G_f, ∅⟩` by backward steps. -/
def PrevReachRW (P : Program) {S : Solver} (τ : TieBreak S) (Gf : Graph)
    (x : Graph × Finset TEv) : Prop :=
  Relation.ReflTransGen (PrevStepRW P τ) (Gf, ∅) x

/-- `e` is not in `G`, or no causal successor of `e` in `G` is `<next`-before
`e` (the proof of Lemma A.25, step ⟨2⟩9). -/
def Graph.NoEarlierSucc (G : Graph) (e : TEv) : Prop :=
  e ∉ G.events ∨ ∀ b, G.porf (.th e) (.th b) → ¬ nextLt b e

/-! ### Auxiliary facts: the maximal extension -/

namespace Graph

theorem Wf.mem_of_porf {G : Graph} (hG : G.Wf) {a b : Ev} (h : G.porf a b) :
    a ∈ evSet G.events ∧ b ∈ evSet G.events := by
  induction h with
  | single h => exact hG.mem_of_porfStep h
  | tail _ h ih => exact ⟨ih.1, (hG.mem_of_porfStep h).2⟩

theorem porfStep_addMax {G : Graph} (hG : G.Wf) {a : TEv} (hidx : a.idx = G.cnt a.tid)
    {x y : Ev} (h : (G.addMax p a).porfStep x y) : G.porfStep x y ∨ y = .th a := by
  rcases a.act.isRead_or_isWrite_or_isLocal with hk | hk | hk
  · rw [addMax_read (TEv.IsRead.exists_act hk)] at h
    exact porfStep_addRead hG hidx h
  · rw [addMax_write hk] at h
    exact porfStep_addWrite hG hidx h
  · obtain ⟨o, -, heq⟩ := addMax_local (G := G) (p := p) hk
    rw [heq] at h
    exact porfStep_addLoc hG hidx h

/-- The event added by the maximal extension has no causal successor. -/
theorem not_porfStep_addMax_self {G : Graph} (hG : G.Wf) {a : TEv}
    (hidx : a.idx = G.cnt a.tid) (b : Ev) : ¬ (G.addMax p a).porfStep (.th a) b := by
  rcases a.act.isRead_or_isWrite_or_isLocal with hk | hk | hk
  · rw [addMax_read (TEv.IsRead.exists_act hk)]
    exact not_porfStep_addRead_self hG hidx (maxWrite_isWriteTo hG _) b
  · rw [addMax_write hk]
    exact not_porfStep_addWrite_self hG hidx b
  · obtain ⟨o, -, heq⟩ := addMax_local (G := G) (p := p) hk
    rw [heq]
    exact not_porfStep_addLoc_self hG hidx b

theorem porf_addMax {G : Graph} (hG : G.Wf) {a : TEv} (hidx : a.idx = G.cnt a.tid)
    {x y : Ev} (h : (G.addMax p a).porf x y) : G.porf x y ∨ y = .th a :=
  Maz.transGen_of_sink (r := G.porfStep) (r' := (G.addMax p a).porfStep) (e := .th a)
    (fun _ _ h => porfStep_addMax hG hidx h) (not_porfStep_addMax_self hG hidx) h

theorem cnt_addMax_self {G : Graph} (hG : G.Wf) {a : TEv} (hidx : a.idx = G.cnt a.tid) :
    (G.addMax p a).cnt a.tid = G.cnt a.tid + 1 := by
  rcases a.act.isRead_or_isWrite_or_isLocal with hk | hk | hk
  · rw [addMax_read (TEv.IsRead.exists_act hk), cnt_addRead hG hidx]
    simp
  · rw [addMax_write hk, cnt_addWrite hG hidx]
    simp
  · obtain ⟨o, -, heq⟩ := addMax_local (G := G) (p := p) hk
    rw [heq, cnt_addLoc hG hidx]
    simp

theorem remove_singleton_events (G : Graph) (e : TEv) :
    (G.remove {e}).events = G.events.erase e := by
  ext q
  simp only [remove, restrict, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton,
    Finset.mem_erase]
  tauto

end Graph

/-- The available events after a maximal extension by the available event
`a`: other available events of the graph, or events `<next`-after `a`. -/
theorem Program.avail_addMax {G : Graph} (hG : G.Wf) {a : TEv} (ha : a ∈ P.avail G) {y : TEv}
    (hy : y ∈ P.avail (G.addMax p a)) : (y ∈ P.avail G ∧ y ≠ a) ∨ nextLt a y := by
  have hidx := idx_eq_of_mem_avail ha
  by_cases ht : y.tid = a.tid
  · right
    refine nextLt_of_poT ⟨ht.symm, ?_⟩
    have h1 := idx_eq_of_mem_avail hy
    rw [h1, ht, Graph.cnt_addMax_self hG hidx, ← hidx]
    exact Nat.lt_succ_self _
  · left
    have htr := Graph.trace_addMax_of_ne (p := p) hG hidx ht
    obtain ⟨h1, h2, h3⟩ := mem_avail_iff.mp hy
    refine ⟨mem_avail_iff.mpr ⟨h1, ?_, ?_⟩, fun h => ht (by rw [h])⟩
    · rw [← Graph.trace_length, ← htr, Graph.trace_length]
      exact h2
    · rw [← htr]
      exact h3

/-- The order in which `MaxCompletion` adds events. For a graph `G'` of the
loop started at `G`: an added event is `<next`-before every available event;
an available event, and an added event, is not `<next`-before every available
event of `G`; a causal successor of an added event is `<next`-after it; a
causality path that ends in `G` is a path of `G`. -/
theorem ComplStep.order {e : TEv} {G G' : Graph} (hG : G.Wf) (hE : P.Exec G)
    (he : e ∈ P.avail G) (h : Relation.ReflTransGen (ComplStep P p e) G G') :
    (∀ c ∈ G'.events, c ∉ G.events → ∀ y ∈ P.avail G', nextLt c y) ∧
    (∀ y' ∈ P.avail G', ∃ y ∈ P.avail G, y = y' ∨ nextLt y y') ∧
    (∀ c ∈ G'.events, c ∉ G.events → ∃ y ∈ P.avail G, y = c ∨ nextLt y c) ∧
    (∀ x c, x ∉ G.events → G'.porf (.th x) (.th c) → nextLt x c) ∧
    (∀ x y, G'.porf x y → y ∈ Graph.evSet G.events → G.porf x y) := by
  induction h with
  | refl =>
    exact ⟨fun c hc hc' => absurd hc hc', fun y' hy' => ⟨y', hy', Or.inl rfl⟩,
      fun c hc hc' => absurd hc hc', fun x c hx hp => absurd (hG.mem_of_porf hp).1 hx,
      fun x y hp _ => hp⟩
  | @tail G1 G2 hch hs ih =>
    obtain ⟨c1, c2', c2, c3, c4⟩ := ih
    obtain ⟨hW, hE1, he1, hsub, -, -, -⟩ := ComplStep.chain hG hE he hch
    obtain ⟨a, ha, hae, rfl⟩ := hs
    have hidx := idx_eq_of_mem_avail ha.1
    have hna := not_mem_of_mem_avail hW ha.1
    have hav : ∀ y ∈ P.avail (G1.addMax p a), (y ∈ P.avail G1 ∧ y ≠ a) ∨ nextLt a y :=
      fun y hy => avail_addMax hW ha.1 hy
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c hc hcG y hy
      rw [Graph.addMax_events] at hc
      rcases Finset.mem_insert.mp hc with hca | hc1
      · rw [hca]
        rcases hav y hy with ⟨hy1, hne⟩ | h
        · exact ha.2 y hy1 hne
        · exact h
      · rcases hav y hy with ⟨hy1, -⟩ | h
        · exact c1 c hc1 hcG y hy1
        · exact nextLt_trans (c1 c hc1 hcG a ha.1) h
    · intro y' hy'
      rcases hav y' hy' with ⟨hy1, -⟩ | h
      · exact c2' y' hy1
      · obtain ⟨y, hy, h'⟩ := c2' a ha.1
        refine ⟨y, hy, Or.inr ?_⟩
        rcases h' with h' | h'
        · rw [h']
          exact h
        · exact nextLt_trans h' h
    · intro c hc hcG
      rw [Graph.addMax_events] at hc
      rcases Finset.mem_insert.mp hc with hca | hc1
      · rw [hca]
        exact c2' a ha.1
      · exact c2 c hc1 hcG
    · intro x c hx hp
      rcases Graph.porf_addMax hW hidx hp with h | h
      · exact c3 x c hx h
      · obtain ⟨z, hz⟩ := Maz.exists_first_of_transGen hp
        have hxm : x ∈ (G1.addMax p a).events := ((hW.addMax hidx).mem_of_porfStep hz).1
        rw [Graph.addMax_events] at hxm
        rcases Finset.mem_insert.mp hxm with hxa | hx1
        · rw [hxa] at hz
          exact absurd hz (Graph.not_porfStep_addMax_self hW hidx z)
        · rw [Ev.th.inj h]
          exact c1 x hx1 hx a ha.1
    · intro x y hp hy
      rcases Graph.porf_addMax hW hidx hp with h | h
      · exact c4 x y h hy
      · rw [h] at hy
        exact absurd (hsub hy) hna

/-! ### Auxiliary facts: the graphs that a backward step restricts to -/

theorem nr_closed {G : Graph} {a : TEv} (hG : G.Wf) (hme : G.IsMe (.th a)) :
    Maz.PrefixClosed G.porfStep (Graph.evSet (G.events ∩ (G.events \ {a}))) := by
  refine Graph.remove_prefixClosed hG (fun q hq b hb => ?_)
  rw [Finset.mem_singleton.mp hq] at hb
  exact absurd (Relation.TransGen.single hb) (hme.2.1 b)

theorem rv_closed {G : Graph} {a e : TEv} (hG : G.Wf) (hme : G.IsMe (.th a))
    (hpo : ∀ b, G.porf (.th e) b ↔ b = .th a) :
    Maz.PrefixClosed G.porfStep (Graph.evSet (G.events ∩ (G.events \ {a, e}))) := by
  refine Graph.remove_prefixClosed hG (fun q hq b hb => ?_)
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact absurd (Relation.TransGen.single hb) (hme.2.1 b)
  · rw [Finset.mem_singleton.mp hq] at hb
    exact ⟨a, by simp, (hpo b).mp (Relation.TransGen.single hb)⟩

/-- The available events of `G \ {a, e}` in a revisit step: `a`, `e`, or
available events of `G`. -/
theorem rv_avail {G : Graph} {a e : TEv} (hG : G.Wf) (hE : P.Exec G) (hme : G.IsMe (.th a))
    (hrf : G.rf a = some (.th e)) (hpo : ∀ b, G.porf (.th e) b ↔ b = .th a) :
    ∀ y ∈ P.avail (G.remove {a, e}), y = a ∨ y = e ∨ y ∈ P.avail G := by
  intro y hy
  obtain ⟨hp, hav⟩ := rv_remove hG hE hme hrf hpo
  have hamax : ∀ b, ¬ G.porfStep (.th a) b := fun b h => hme.2.1 b (Relation.TransGen.single h)
  have ha : a ∈ G.events := hme.1
  by_cases hte : y.tid = e.tid
  · exact Or.inr (Or.inl (avail_tid_inj hy hav hte))
  -- the sources of the events of a thread other than that of `e` are kept
  have hsrc : ∀ q ∈ G.events, q ≠ a → ∀ w, G.rf q = some w →
      w ∈ Graph.evSet (G.events \ {a, e}) := by
    intro q hq hqa w hw
    cases w with
    | init => trivial
    | th w' =>
      refine Finset.mem_sdiff.mpr ⟨(hG.rf_source_mem hw).2, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => hamax (.th q) (Or.inr ⟨q, rfl, hq, h ▸ hw⟩), fun h => ?_⟩
      have := (hpo (.th q)).mp (Relation.TransGen.single (Or.inr ⟨q, rfl, hq, h ▸ hw⟩))
      exact hqa (Ev.th.inj this)
  by_cases hta : y.tid = a.tid
  · left
    have hae : a.tid ≠ e.tid := fun h => hte (hta.trans h)
    have hav' : a ∈ P.avail (G.remove {a, e}) := by
      refine mem_avail_restrict hG hE ha (by simp) (fun q hq ht hi => ?_)
        (fun q hq _ hi w hw => hsrc q hq (fun h => Nat.lt_irrefl _ (h ▸ hi)) w hw)
        (hG.of_isPrefixOf hp)
      refine Finset.mem_sdiff.mpr ⟨hq, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => Nat.lt_irrefl _ (h ▸ hi), fun h => hae (by rw [← ht, h])⟩
    exact avail_tid_inj hy hav' hta
  · right
    right
    have htr : (G.remove {a, e}).trace y.tid = G.trace y.tid := by
      refine Graph.trace_restrict_of_thread hG (fun q hq hqt => ?_)
        (fun q hq hqt w hw => hsrc q hq (fun h => hta (by rw [← hqt, h])) w hw)
      refine Finset.mem_sdiff.mpr ⟨hq, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hta (by rw [← hqt, h]), fun h => hte (by rw [← hqt, h])⟩
    obtain ⟨h1, h2, h3⟩ := mem_avail_iff.mp hy
    refine mem_avail_iff.mpr ⟨h1, ?_, ?_⟩
    · rw [← Graph.trace_length, ← htr, Graph.trace_length]
      exact h2
    · rw [← htr]
      exact h3

/-! ### Proofs -/

theorem PrevReachRW.reach {Gf : Graph} {x : Graph × Finset TEv} (h : PrevReachRW P τ Gf x) :
    PrevReach P τ Gf x.1 := by
  unfold PrevReachRW at h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨e, k, hs, -⟩ := hs
    exact ih.tail ⟨e, k, hs⟩

theorem PrevReach.exists_rw {Gf G : Graph} (h : PrevReach P τ Gf G) :
    ∃ rw, PrevReachRW P τ Gf (G, rw) := by
  induction h with
  | refl => exact ⟨∅, Relation.ReflTransGen.refl⟩
  | tail _ hs ih =>
    obtain ⟨e, k, hs⟩ := hs
    obtain ⟨rw, h⟩ := ih
    exact ⟨k.rw e rw, h.tail ⟨e, k, hs, rfl⟩⟩

/-- If no causal successor of the event `e` of `G` is `<next`-before `e`,
then `me(G)` is not `<next`-before `e`. -/
theorem Graph.NoEarlierSucc.me_ge {G : Graph} {e m : TEv} (hG : G.Wf)
    (hac : Maz.Acyclic G.porfStep) (he : e ∈ G.events) (h : G.NoEarlierSucc e)
    (hm : G.IsMe (.th m)) : ¬ nextLt m e := by
  classical
  have h2 := h.resolve_left (not_not.mpr he)
  -- a `porf`-maximal event `z` that is `e` or a causal successor of `e`
  let s : Finset Ev := (insert e (G.events.filter (fun b => G.porf (.th e) (.th b)))).image Ev.th
  have hs : ∀ z, z ∈ s ↔
      ∃ z', z = .th z' ∧ (z' = e ∨ (z' ∈ G.events ∧ G.porf (.th e) (.th z'))) := by
    intro z
    simp only [s, Finset.mem_image, Finset.mem_insert, Finset.mem_filter]
    constructor
    · rintro ⟨z', hz', rfl⟩
      exact ⟨z', rfl, hz'⟩
    · rintro ⟨z', rfl, hz'⟩
      exact ⟨z', hz', rfl⟩
  obtain ⟨z, hz, hzmax⟩ := hac.exists_maximal s ⟨.th e, (hs _).mpr ⟨e, rfl, Or.inl rfl⟩⟩
  obtain ⟨z', rfl, hz'⟩ := (hs _).mp hz
  have hreach : ∀ b, G.porfStep (.th z') b → G.porf (.th e) b := by
    intro b hb
    rcases hz' with rfl | ⟨-, hp⟩
    · exact Relation.TransGen.single hb
    · exact hp.tail hb
  have hzM : ∀ b, ¬ G.porf (.th z') b := by
    intro b hb
    obtain ⟨c, hc⟩ := Maz.exists_first_of_transGen hb
    cases c with
    | init => exact G.not_porfStep_init _ hc
    | th c' =>
      exact hzmax (.th c')
        ((hs _).mpr ⟨c', rfl, Or.inr ⟨(hG.mem_of_porfStep hc).2, hreach _ hc⟩⟩) hc
  have hzm : z' ∈ G.events := by
    rcases hz' with rfl | ⟨h, -⟩
    · exact he
    · exact h
  intro hlt
  by_cases hzeq : z' = m
  · rcases hz' with rfl | ⟨-, hp⟩
    · exact nextLt_irrefl _ (hzeq ▸ hlt)
    · exact h2 z' hp (hzeq ▸ hlt)
  · have hzlt : nextLt z' m := hm.2.2 (.th z') hzm hzM (fun h => hzeq (Ev.th.inj h))
    rcases hz' with rfl | ⟨-, hp⟩
    · exact nextLt_irrefl _ (nextLt_trans hzlt hlt)
    · exact h2 z' hp (nextLt_trans hzlt hlt)

/-- A backward step keeps `NoEarlierSucc e` (the proof of Lemma A.25, step
⟨3⟩2). The hypothesis `hs1` is (S1) of Proposition A.23 for `X`. -/
theorem PrevStep.noEarlierSucc {X Y : Graph} {e' e : TEv} {k : Kind} (hM : M.Extensible)
    (hX : X.Wf) (hE : P.Exec X) (hc : (M.sym S).cons X)
    (hs1 : ∀ y ∈ P.avail X, ∀ m, X.IsMe m → ¬ nextLtEv (.th y) m)
    (hs : PrevStep P τ X e' k Y) (h : X.NoEarlierSucc e) : Y.NoEarlierSucc e := by
  obtain ⟨hWY, -, -⟩ := hs.inv hM hX hE hc
  by_cases heY : e ∈ Y.events
  swap
  · exact Or.inl heY
  right
  intro c hpc hlt
  have hcY : c ∈ Y.events := (hWY.mem_of_porf hpc).2
  cases k with
  | nr =>
    obtain ⟨hme, rfl, -⟩ := hs.nr_inv
    have heX : e ∈ X.events := (Finset.mem_inter.mp heY).1
    exact h.resolve_left (not_not.mpr heX) c
      ((Graph.porf_restrict_iff (nr_closed hX hme) hcY).mp hpc) hlt
  | rv a =>
    obtain ⟨hme, hr, hrf, hlt', hpo, hmc⟩ := hs.rv_inv
    obtain ⟨hp, hav⟩ := rv_remove hX hE hme hrf hpo
    have hW0 := hX.of_isPrefixOf hp
    have hE0 := hE.of_isPrefixOf hX hp
    obtain ⟨-, -, c2, c3, c4⟩ := ComplStep.order hW0 hE0 hav hmc.1
    by_cases he0 : e ∈ (X.remove {a, e'}).events
    · have he0' : e ∈ X.events ∩ (X.events \ {a, e'}) := he0
      have heX : e ∈ X.events := (Finset.mem_inter.mp he0').1
      have hea : e ≠ a := fun h =>
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp he0').2).2 (by simp [h])
      by_cases hc0 : c ∈ (X.remove {a, e'}).events
      · have h0 : (X.remove {a, e'}).porf (.th e) (.th c) := c4 _ _ hpc hc0
        exact h.resolve_left (not_not.mpr heX) c
          ((Graph.porf_restrict_iff (rv_closed hX hme hpo) hc0).mp h0) hlt
      · obtain ⟨y, hy, hyc⟩ := c2 c hcY hc0
        have hya : ¬ nextLt y a := by
          rcases rv_avail hX hE hme hrf hpo y hy with rfl | rfl | hyX
          · exact nextLt_irrefl _
          · exact fun h => nextLt_irrefl _ (nextLt_trans h hlt')
          · exact hs1 y hyX _ hme
        have hea' : nextLt e a := (nextLt_total hea).resolve_right
          (h.me_ge hX ((M.sym S).porf_acyclic X hX hc) heX hme)
        have hca : nextLt c a := nextLt_trans hlt hea'
        rcases hyc with rfl | hyc
        · exact hya hca
        · exact hya (nextLt_trans hyc hca)
    · exact nextLt_irrefl _ (nextLt_trans (c3 e c he0 hpc) hlt)

/-- The revisiting write of a backward revisit step does not satisfy
`NoEarlierSucc`: the revisited read is a causal successor that is
`<next`-before it. -/
theorem PrevStep.not_noEarlierSucc {G G' : Graph} {a e : TEv} (hG : G.Wf)
    (hs : PrevStep P τ G e (.rv a) G') : ¬ G.NoEarlierSucc e := by
  obtain ⟨-, -, hrf, hlt, hpo, -⟩ := hs.rv_inv
  rintro (h | h)
  · exact h (hG.rf_source_mem hrf).2
  · exact h a ((hpo _).mpr rfl) hlt

/-- `NoEarlierSucc e` is kept along the backward steps from `G_f`. -/
theorem PrevReach.noEarlierSucc {Gf G G2 : Graph} {e : TEv} (hM : M.Extensible) (hGf : Gf.Wf)
    (hEf : P.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.Full Gf) (h1 : PrevReach P τ Gf G)
    (h2 : Relation.ReflTransGen (fun G G' => ∃ e k, PrevStep P τ G e k G') G G2)
    (h : G.NoEarlierSucc e) : G2.NoEarlierSucc e := by
  induction h2 with
  | refl => exact h
  | tail hch hs ih =>
    obtain ⟨e', k, hs⟩ := hs
    have hr : PrevReach P τ Gf _ := Relation.ReflTransGen.trans h1 hch
    obtain ⟨hW, hE, hc⟩ := PrevReach.inv hM hGf hEf hcf hr
    exact hs.noEarlierSucc hM hW hE hc
      (fun y hy m hm => PrevReach.s1 hM hGf hEf hcf hff hr hy hm) ih

/-- The revisiting write of a backward revisit step is an event of `G_f`. -/
theorem PrevReach.rv_mem {Gf G G' : Graph} {a e : TEv} (hM : M.Extensible) (hGf : Gf.Wf)
    (hEf : P.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.Full Gf) (h : PrevReach P τ Gf G)
    (hs : PrevStep P τ G e (.rv a) G') : e ∈ Gf.events := by
  by_contra he
  exact hs.not_noEarlierSucc (PrevReach.inv hM hGf hEf hcf h).1
    (PrevReach.noEarlierSucc hM hGf hEf hcf hff Relation.ReflTransGen.refl h (Or.inl he))

/-- Every write of `RW` is an event of `G_f` and satisfies `NoEarlierSucc`
in the current graph. -/
theorem PrevReachRW.inv {Gf : Graph} {x : Graph × Finset TEv} (hM : M.Extensible)
    (hGf : Gf.Wf) (hEf : P.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.Full Gf)
    (h : PrevReachRW P τ Gf x) : ∀ e ∈ x.2, x.1.NoEarlierSucc e ∧ e ∈ Gf.events := by
  unfold PrevReachRW at h
  induction h with
  | refl => exact fun e he => absurd he (by simp)
  | @tail x y hch hs ih =>
    obtain ⟨e', k, hs, hrw⟩ := hs
    have hr : PrevReach P τ Gf x.1 := PrevReachRW.reach hch
    obtain ⟨hW, hE, hc⟩ := PrevReach.inv hM hGf hEf hcf hr
    have keep : ∀ e, x.1.NoEarlierSucc e → y.1.NoEarlierSucc e := fun e he =>
      hs.noEarlierSucc hM hW hE hc
        (fun y hy m hm => PrevReach.s1 hM hGf hEf hcf hff hr hy hm) he
    intro e he
    rw [hrw] at he
    cases k with
    | nr => exact ⟨keep e (ih e he).1, (ih e he).2⟩
    | rv a =>
      rcases Finset.mem_insert.mp he with rfl | he
      · obtain ⟨hWY, -, -⟩ := hs.inv hM hW hE hc
        refine ⟨Or.inl ?_, PrevReach.rv_mem hM hGf hEf hcf hff hr hs⟩
        exact not_mem_of_mem_avail hWY hs.rv_inv.2.2.2.2.2.2.1
      · exact ⟨keep e (ih e he).1, (ih e he).2⟩

/-- The set `RW` consists of events of `G_f`. -/
theorem PrevReachRW.subset {Gf G : Graph} {rw : Finset TEv} (hM : M.Extensible) (hGf : Gf.Wf)
    (hEf : P.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.Full Gf) (h : PrevReachRW P τ Gf (G, rw)) :
    rw ⊆ Gf.events :=
  fun e he => (PrevReachRW.inv hM hGf hEf hcf hff h e he).2

/-- Lemma A.25: the revisiting write of a backward revisit step is not in the
set `RW` collected so far. -/
theorem PrevReachRW.a25 {Gf G G' : Graph} {rw : Finset TEv} {a e : TEv} (hM : M.Extensible)
    (hGf : Gf.Wf) (hEf : P.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.Full Gf)
    (h : PrevReachRW P τ Gf (G, rw)) (hs : PrevStep P τ G e (.rv a) G') : e ∉ rw := by
  intro he
  exact hs.not_noEarlierSucc (PrevReach.inv hM hGf hEf hcf (PrevReachRW.reach h)).1
    (PrevReachRW.inv hM hGf hEf hcf hff h e he).1

/-- Proposition A.26: from a well-formed, consistent, full execution of a
bounded program, the backward steps reach the graph without thread events. -/
theorem PrevReach.init {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible) {Gf : Graph}
    (hGf : Gf.Wf) (hEf : P.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.Full Gf) :
    PrevReach P τ Gf (Graph.init P.mem) := by
  let K := n * P.threads.length
  let f : Graph × Finset TEv → ℕ := fun x => x.2.card * (K + 1) + (K - x.1.events.card)
  have hK : ∀ x, PrevReachRW P τ Gf x → x.1.events.card ≤ K := fun x hx =>
    let ⟨hW, hE, _⟩ := PrevReach.inv hM hGf hEf hcf (PrevReachRW.reach hx)
    hE.card_le hW hn
  have hRW : ∀ x, PrevReachRW P τ Gf x → x.2.card ≤ K := fun x hx =>
    (Finset.card_le_card (fun e he => (PrevReachRW.inv hM hGf hEf hcf hff hx e he).2)).trans
      (hEf.card_le hGf hn)
  have hinc : ∀ x y, Relation.ReflTransGen (PrevStepRW P τ) (Gf, ∅) x → PrevStepRW P τ x y →
      f x < f y := by
    intro x y hx hxy
    have hy : PrevReachRW P τ Gf y := Relation.ReflTransGen.tail hx hxy
    have h1 := hK x hx
    have h2 := hK y hy
    obtain ⟨X, rwX⟩ := x
    obtain ⟨Y, rwY⟩ := y
    obtain ⟨e, k, hs, hrw⟩ := hxy
    simp only at hs hrw h1 h2
    simp only [f]
    cases k with
    | nr =>
      obtain ⟨hme, rfl, -⟩ := hs.nr_inv
      have he : e ∈ X.events := hme.1
      have hcard := Finset.card_erase_of_mem he
      have hpos : 0 < X.events.card := Finset.card_pos.mpr ⟨e, he⟩
      rw [hrw, Graph.remove_singleton_events]
      simp only [Kind.rw]
      omega
    | rv a =>
      have h25 : e ∉ rwX := PrevReachRW.a25 hM hGf hEf hcf hff hx hs
      rw [hrw]
      simp only [Kind.rw]
      rw [Finset.card_insert_of_notMem h25, Nat.add_mul, Nat.one_mul]
      omega
  have hbd : ∀ x, Relation.ReflTransGen (PrevStepRW P τ) (Gf, ∅) x → f x ≤ K * (K + 1) + K := by
    intro x hx
    have h1 := hRW x hx
    have h2 : x.2.card * (K + 1) ≤ K * (K + 1) := Nat.mul_le_mul_right _ h1
    simp only [f]
    omega
  obtain ⟨x, hx, hsink⟩ := Maz.exists_sink_of_bounded_measure f (K * (K + 1) + K) hinc hbd
  obtain ⟨hW, hE, hc⟩ := PrevReach.inv hM hGf hEf hcf (PrevReachRW.reach hx)
  have hemp : x.1.events = ∅ := by
    by_contra hne
    obtain ⟨e, k, G', hs⟩ :=
      exists_prevStep hn hW hE hc (Finset.nonempty_iff_ne_empty.mpr hne)
    exact hsink (G', k.rw e x.2) ⟨e, k, hs, rfl⟩
  have hinit : x.1 = Graph.init P.mem := by
    rw [← hE.1]
    exact hW.eq_init_of_events_eq_empty hemp
  rw [← hinit]
  exact PrevReachRW.reach hx

/-! ### Further facts on one backward step -/

/-- The revisiting write is not in the graph that a revisit step returns. -/
theorem PrevStep.rv_not_mem {G G' : Graph} {a e : TEv} (hG : G.Wf) (hE : P.Exec G)
    (hs : PrevStep P τ G e (.rv a) G') : e ∉ G'.events := by
  obtain ⟨hme, -, hrf, -, hpo, hmc⟩ := hs.rv_inv
  obtain ⟨hp, hav⟩ := rv_remove hG hE hme hrf hpo
  obtain ⟨hW, -, hnx, -⟩ := hmc.facts (hG.of_isPrefixOf hp) (hE.of_isPrefixOf hG hp) hav
  exact not_mem_of_mem_avail hW hnx.1

/-- A non-revisit backward step removes exactly its event. -/
theorem PrevStep.nr_events {G G' : Graph} {e : TEv} (hs : PrevStep P τ G e .nr G') :
    G.events = insert e G'.events ∧ e ∉ G'.events := by
  obtain ⟨hme, rfl, -⟩ := hs.nr_inv
  have he : e ∈ G.events := hme.1
  rw [Graph.remove_singleton_events]
  exact ⟨(Finset.insert_erase he).symm, Finset.notMem_erase e _⟩

/-- The graphs of the backward chain have at most `n * |threads|` events. -/
theorem PrevReach.card_le {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible) {Gf G : Graph}
    (hGf : Gf.Wf) (hEf : P.Exec Gf) (hcf : (M.sym S).cons Gf) (h : PrevReach P τ Gf G) :
    G.events.card ≤ n * P.threads.length := by
  obtain ⟨hW, hE, -⟩ := PrevReach.inv hM hGf hEf hcf h
  exact hE.card_le hW hn

end Condpor
