import Mazurkiewicz.Condpor.PrevTerm

/-!
ConDpor, Theorem 4 (Completeness): `complete`, for the model `M.sym S` (the
paper's `M_S`), any solver `S` and any tie-break `τ`, a bounded program and an
extensible underlying model `M`. The proof extends that of TruSt; the
references below (Section 4.3, Appendix A) are to the TruSt paper.

# Completeness

Paper: Section 4.3, Theorem 4.1 (completeness); Appendix A.6, Proposition
A.28, Lemma A.29, Theorem A.30. Coq: `trust/Complete.v` (`DelE`, `G'E`,
`IsMaximalDel`, `TruStPrev`, `TruSt_Complete`).

Theorem A.30: Algorithm 1 reaches every well-formed, consistent, full
execution of a bounded program under a maximally extensible model.

How the text is read here.

* Proposition A.28 in the paper: if `⟨∅, ∅⟩ ⇒* ⟨G, <⟩` and `G ⇝ G' ⇝* G_f`
  (that is, `Prev(G') = ⟨G, e, t⟩` and `G'` is obtained from `G_f` by backward
  steps), then `⟨G, <⟩ ⇒ ⟨G', <'⟩` with the same event and kind. Here the
  reached configuration is `c`, the paper's `G` is `c.abs`, and the paper's
  `G'` is `X`: `Reach.step_of_prevStep`. "For some `<'`" is: for some
  configuration `c'` with `c'.abs = X`.
* Lemma A.29 (`∅ ⇝* G ⇝* G_f` implies that `G` is reached) is
  `PrevReach.reach`; the hypothesis `∅ ⇝* G` is a chain of backward steps from
  `G` to the graph without thread events.
* Theorem A.30 is `complete`. Proposition A.28 and Lemma A.29 do not need the
  program to be bounded; Theorem A.30 does, through Proposition A.26.
* In the forward step that matches a backward step, a write is placed after
  its coherence predecessor in `X` (`Graph.remove_addWrite_co`).

The proof of the revisit case of Proposition A.28 (`RvData`). Notation: `Y`
is the graph of `c`, `<` its insertion order; in `X`, `me(X) = a` reads from
`e`; `X0 = X \ {a, e}`; `Y = MaxCompletion(X0, e)`; an event of `X0` is old,
an event of `Y` outside `X0` is added. The proof follows the paper's steps,
with these repairs, which are recorded in the plan.

* ⟨4⟩2 cites (P5) for "the events added when constructing `G` are
  `<next`-after `me(G') = a`". (P5) is about a configuration reached by
  Algorithm 1, and `G'` is not yet known to be one: that is what is being
  proved. The fact holds by (S1) of Proposition A.23 for `G'` and by the order
  in which `MaxCompletion` adds events (`RvData.ge_a`, from `ComplStep.order`
  and `rv_avail`); `a` itself is added, so the bound is not strict for `a`.
* ⟨2⟩8 cites (P3) for `IsMaximallyAdded`. (P3) is a property of a step of
  Algorithm 1 that is a revisit, and that this revisit is a step is what is
  being proved. Used instead: on the added events `<` agrees with `<next`
  (`RvData.lt_of_added`, from (P2) and the order of the completion: for an
  added `v` and `x <next v`, `x` was inserted before `v`,
  `RvData.not_lt_of_added`); `MaxCompletion` adds every event in the maximal
  way, and a write that is coherence-after the source of an added read, or
  after an added write, is added later (`ComplStep.co_order`); and an old
  source of an added read is in `Previous` by ⟨2⟩2 (`RvData.del_iff`). The
  paper prints `IsMaximallyAdded(G', p, e)`; the test is on the configuration
  `⟨G, <⟩` that the step starts from (the deleted events are not in `G'`).
* ⟨2⟩7 uses `G'.porf; [e] = (G + e).porf; [e]` without proof. Here: the
  thread predecessors of `e` are old, and a causality path from an added
  event never ends in an old event, so no added event (in particular `a`) is
  causally before `e` in `G + e` (`RvData.plus_old`).
* ⟨3⟩1: ⟨5⟩1 prints `<next ∪ >` where the hypothesis of (P2) is the
  intersection; ⟨5⟩5 prints `y ∉ G.E`, `z ∉ G.E` where `G'.E` is meant. In
  ⟨3⟩2, ⟨5⟩6 says "only `e` is removed"; `G` and `G'` differ also in the
  source of `a` and in the added events, and the step holds because the path
  avoids `a` and `e` and a path of `G'` between old events is a path of `G`.
* The clauses of Proposition A.22 that are used are (P2) and (P6), with
  `Reach.bw_po_lt` (the paper's ⟨5⟩13) and `PoLt`; (P1), (P3), (P4), (P5)
  are not used.
-/

namespace List

variable {α : Type*} [DecidableEq α]

/-- A list without repetition is itself without `e`, with `e` put back at the
front or after its predecessor. -/
theorem eq_cons_or_insertAfter_filter {l : List α} (hl : l.Nodup) {e : α} (he : e ∈ l) :
    l = e :: l.filter (fun b => decide (b ≠ e)) ∨
      ∃ p ∈ l, p ≠ e ∧ l = (l.filter (fun b => decide (b ≠ e))).insertAfter p e := by
  induction l with
  | nil => simp at he
  | cons b t ih =>
    obtain ⟨hbt, ht⟩ := List.nodup_cons.mp hl
    by_cases hbe : b = e
    · left
      subst hbe
      have hft : t.filter (fun x => decide (x ≠ b)) = t := by
        refine List.filter_eq_self.mpr (fun x hx => ?_)
        have hxb : x ≠ b := fun h => hbt (h ▸ hx)
        simpa using hxb
      rw [List.filter_cons_of_neg (by simp), hft]
    · right
      have het : e ∈ t := (List.mem_cons.mp he).resolve_left (Ne.symm hbe)
      have hf : (b :: t).filter (fun x => decide (x ≠ e)) =
          b :: t.filter (fun x => decide (x ≠ e)) := by
        exact List.filter_cons_of_pos (by simpa using hbe)
      rcases ih ht het with h | ⟨p, hp, hpe, h⟩
      · refine ⟨b, List.mem_cons_self, hbe, ?_⟩
        rw [hf]
        simp only [List.insertAfter, ↓reduceIte]
        rw [← h]
      · refine ⟨p, List.mem_cons_of_mem _ hp, hpe, ?_⟩
        have hbp : b ≠ p := fun h' => hbt (h' ▸ hp)
        rw [hf]
        simp only [List.insertAfter, hbp, ↓reduceIte]
        rw [← h]

end List

namespace Condpor

open Program

variable {P : Program} {M : Model} {S : Solver} {τ : TieBreak S}
  {ρ : Finset Lit → SExpr → Bool}

/-! ### A graph is rebuilt from the graph without a causally maximal event -/

namespace Graph

/-- The coherence lists of the graph without the write `e`. -/
theorem remove_singleton_co {X : Graph} (hX : X.Wf) (e : TEv) (x : Loc) :
    (X.remove {e}).co x = (X.co x).filter (fun b => decide (b ≠ e)) := by
  change (X.co x).filter (fun b => decide (b ∈ X.events \ {e})) = _
  apply List.filter_congr
  intro b hb
  have := ((hX.co_mem x b).mp hb).1
  simp [this]

/-- The write `e` of `X` can be put back into the coherence order of the
graph without `e`: after its coherence predecessor `wp`. -/
theorem remove_addWrite_co {X : Graph} (hX : X.Wf) {e : TEv} (he : e ∈ X.events)
    (hw : e.IsWrite) :
    ∃ wp, (X.remove {e}).IsWriteTo e.loc wp ∧ ((X.remove {e}).addWrite e wp).co = X.co := by
  obtain ⟨v, hv⟩ := hw.exists_act
  have hel : e ∈ X.co e.loc := (hX.co_mem _ _).mpr ⟨he, v, hv⟩
  have hother : ∀ x, x ≠ e.loc → (X.remove {e}).co x = X.co x := by
    intro x hx
    rw [remove_singleton_co hX]
    refine List.filter_eq_self.mpr (fun b hb => ?_)
    have : b ≠ e := by
      rintro rfl
      obtain ⟨-, v', hv'⟩ := (hX.co_mem x b).mp hb
      rw [hv] at hv'
      exact hx (by cases hv'; rfl)
    simpa using this
  rcases List.eq_cons_or_insertAfter_filter (hX.co_nodup e.loc) hel with h | ⟨p, hp, hpe, h⟩
  · refine ⟨.init, trivial, ?_⟩
    funext x
    by_cases hx : x = e.loc
    · rw [hx, addWrite_co_self, remove_singleton_co hX]
      exact h.symm
    · rw [addWrite_co_of_ne _ _ _ hx, hother x hx]
  · have hpm := (hX.co_mem _ _).mp hp
    refine ⟨.th p, ⟨?_, hpm.2⟩, ?_⟩
    · exact Finset.mem_inter.mpr ⟨hpm.1, Finset.mem_sdiff.mpr ⟨hpm.1, by simpa using hpe⟩⟩
    · funext x
      by_cases hx : x = e.loc
      · rw [hx, addWrite_co_self, remove_singleton_co hX]
        exact h.symm
      · rw [addWrite_co_of_ne _ _ _ hx, hother x hx]

/-- The sources in the graph without `e`, for the events other than the
readers of `e`. -/
theorem remove_singleton_rf {X : Graph} (hX : X.Wf) {e q : TEv} (hqe : q ≠ e)
    (hsrc : X.rf q ≠ some (.th e)) : (X.remove {e}).rf q = X.rf q := by
  by_cases hq : q ∈ X.events
  · refine X.restrict_rf_of_source_kept
      (Finset.mem_inter.mpr ⟨hq, Finset.mem_sdiff.mpr ⟨hq, by simpa using hqe⟩⟩) (fun w hw => ?_)
    cases w with
    | init => trivial
    | th w' =>
      refine Finset.mem_sdiff.mpr ⟨(hX.rf_source_mem hw).2, ?_⟩
      rw [Finset.mem_singleton]
      rintro rfl
      exact hsrc hw
  · rw [hX.rf_none q (Or.inl hq)]
    exact X.restrict_rf_of_not_mem (fun h => hq (Finset.mem_inter.mp h).1)

/-- Removing an event that is not a constraint evaluation keeps the outcomes. -/
theorem remove_singleton_pol {X : Graph} (hX : X.Wf) {e : TEv} (hnc : ¬ e.IsCons) :
    (X.remove {e}).pol = X.pol := by
  funext q
  change (X.restrict (X.events \ {e})).pol q = X.pol q
  rw [restrict_pol]
  by_cases hq : q ∈ X.events ∩ (X.events \ {e})
  · simp only [hq, ↓reduceIte]
  · simp only [hq, ↓reduceIte]
    symm
    by_contra h
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h
    obtain ⟨hqm, hqc⟩ := hX.pol_some hb
    apply hq
    refine Finset.mem_inter.mpr ⟨hqm, Finset.mem_sdiff.mpr ⟨hqm, ?_⟩⟩
    rw [Finset.mem_singleton]
    rintro rfl
    exact hnc hqc

/-- The literals of a restriction depend only on which constraint evaluations
are kept. -/
theorem F_restrict_congr (G : Graph) {s s' : Finset TEv}
    (h : ∀ q ∈ G.events, q.IsCons → (q ∈ s ↔ q ∈ s')) : (G.restrict s).F = (G.restrict s').F := by
  have key : ∀ s s' : Finset TEv, (∀ q ∈ G.events, q.IsCons → (q ∈ s → q ∈ s')) →
      (G.restrict s).F ⊆ (G.restrict s').F := by
    intro s s' h l hl
    obtain ⟨q, hq, hql⟩ := (mem_F _).mp hl
    have hq' : q ∈ G.events ∩ s := hq
    rw [G.lit_restrict hq'] at hql
    have hc : q.IsCons := by
      by_contra hn
      rw [G.lit_of_not_isCons hn] at hql
      cases hql
    have hq2 : q ∈ G.events ∩ s' :=
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hq').1,
        h q (Finset.mem_inter.mp hq').1 hc (Finset.mem_inter.mp hq').2⟩
    exact (mem_F _).mpr ⟨q, hq2, by rw [G.lit_restrict hq2]; exact hql⟩
  exact Finset.Subset.antisymm (key s s' (fun q hq hc => (h q hq hc).mp))
    (key s' s (fun q hq hc => (h q hq hc).mpr))

theorem remove_singleton_insert {X : Graph} {e : TEv} (he : e ∈ X.events) :
    insert e (X.remove {e}).events = X.events := by
  rw [remove_singleton_events]
  exact Finset.insert_erase he

/-- A graph is the graph without its read `e`, a causally maximal event,
with `e` added back with its source. -/
theorem remove_addRead {X : Graph} (hX : X.Wf) {e : TEv} {x : Loc} {w : Ev}
    (he : e ∈ X.events) (hact : e.act = .read x) (hrf : X.rf e = some w)
    (hsink : ∀ q, X.rf q ≠ some (.th e)) : (X.remove {e}).addRead e w = X := by
  apply Graph.ext
  · rfl
  · exact remove_singleton_insert he
  · funext q
    rw [addRead_rf]
    by_cases hqe : q = e
    · rw [hqe, Function.update_self, hrf]
    · rw [Function.update_of_ne hqe, remove_singleton_rf hX hqe (hsink q)]
  · funext y
    change (X.remove {e}).co y = X.co y
    rw [remove_singleton_co hX]
    refine List.filter_eq_self.mpr (fun b hb => ?_)
    have : b ≠ e := by
      rintro rfl
      obtain ⟨-, v, hv⟩ := (hX.co_mem y b).mp hb
      rw [hact] at hv
      cases hv
    simpa using this
  · exact remove_singleton_pol hX (by simp [TEv.IsCons, hact, Act.IsCons])

/-- A graph is the graph without its local event `e`, a causally maximal
event, with `e` added back with its outcome. -/
theorem remove_addLoc {X : Graph} (hX : X.Wf) {e : TEv} (he : e ∈ X.events) (hl : e.IsLocal)
    (hsink : ∀ q, X.rf q ≠ some (.th e)) : (X.remove {e}).addLoc e (X.pol e) = X := by
  apply Graph.ext
  · rfl
  · exact remove_singleton_insert he
  · funext q
    rw [addLoc_rf]
    by_cases hqe : q = e
    · rw [hqe, hX.rf_none e (Or.inr hl.not_isRead)]
      exact X.restrict_rf_of_not_mem (by simp)
    · exact remove_singleton_rf hX hqe (hsink q)
  · funext y
    change (X.remove {e}).co y = X.co y
    rw [remove_singleton_co hX]
    refine List.filter_eq_self.mpr (fun b hb => ?_)
    have : b ≠ e := by
      rintro rfl
      obtain ⟨-, v, hv⟩ := (hX.co_mem y b).mp hb
      exact hl.not_isWrite (by simp [hv, Act.IsWrite])
    simpa using this
  · funext q
    rw [addLoc_pol]
    by_cases hqe : q = e
    · rw [hqe, Function.update_self]
    · rw [Function.update_of_ne hqe]
      change (X.restrict (X.events \ {e})).pol q = X.pol q
      rw [restrict_pol]
      by_cases hq : q ∈ X.events
      · have : q ∈ X.events ∩ (X.events \ {e}) := by simp [hq, hqe]
        simp only [this, ↓reduceIte]
      · have : q ∉ X.events ∩ (X.events \ {e}) := fun h => hq (Finset.mem_inter.mp h).1
        simp only [this, ↓reduceIte]
        exact (hX.pol_none hq).symm

end Graph

/-! ### More facts on what `MaxCompletion` adds -/

/-- Coherence after a maximal extension: old pairs, or pairs into the new
event. -/
theorem Graph.coRelAt_addMax {G : Graph} (hG : G.Wf) {a : TEv} (ha : a ∉ G.events) {x : Loc}
    {u : Ev} {w : TEv} (h : (G.addMax ρ a).coRelAt x u (.th w)) :
    G.coRelAt x u (.th w) ∨ w = a := by
  rcases a.act.isRead_or_isWrite_or_isLocal with hk | hw | hk
  · rw [Graph.addMax_read (TEv.IsRead.exists_act hk)] at h
    exact Or.inl h
  · rw [Graph.addMax_write hw] at h
    have hna : a ∉ G.co x := fun h' => ha ((hG.co_mem x a).mp h').1
    by_cases hx : x = a.loc
    · have hco : (G.addWrite a (G.maxWrite a.loc)).co x = G.co x ++ [a] := by
        rw [Graph.addWrite_maxWrite_co_eq hG a x]
        simp [hx]
      cases u with
      | init =>
        have h' : w ∈ (G.addWrite a (G.maxWrite a.loc)).co x := h
        rw [hco] at h'
        rcases List.mem_append.mp h' with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (List.mem_singleton.mp h1)
      | th u' =>
        have h' : ((G.addWrite a (G.maxWrite a.loc)).co x).Before u' w := h
        rw [hco] at h'
        rcases (List.before_append_singleton_iff hna).mp h' with h1 | ⟨-, h1⟩
        · exact Or.inl h1
        · exact Or.inr h1
    · have hco : (G.addWrite a (G.maxWrite a.loc)).co x = G.co x := by
        rw [Graph.addWrite_maxWrite_co_eq hG a x]
        simp [hx]
      left
      cases u with
      | init =>
        have h' : w ∈ (G.addWrite a (G.maxWrite a.loc)).co x := h
        rw [hco] at h'
        exact h'
      | th u' =>
        have h' : ((G.addWrite a (G.maxWrite a.loc)).co x).Before u' w := h
        rw [hco] at h'
        exact h'
  · obtain ⟨o, -, heq⟩ := Graph.addMax_local (G := G) (p := ρ) hk
    rw [heq] at h
    exact Or.inl h

/-- An available event stays available in the loop of `MaxCompletion` until
it is added. -/
theorem ComplStep.mem_or_avail {e : TEv} {G G' : Graph} (hG : G.Wf) (hE : P.Exec G)
    (he : e ∈ P.avail G) (h : Relation.ReflTransGen (ComplStep P ρ e) G G') {y : TEv}
    (hy : y ∈ P.avail G) : y ∈ G'.events ∨ y ∈ P.avail G' := by
  induction h with
  | refl => exact Or.inr hy
  | @tail G1 G2 hch hs ih =>
    obtain ⟨hW, hE1, he1, -⟩ := ComplStep.chain hG hE he hch
    obtain ⟨a, ha, hae, rfl⟩ := hs
    rcases ih with h1 | h1
    · left
      rw [Graph.addMax_events]
      exact Finset.mem_insert_of_mem h1
    · by_cases hya : y = a
      · left
        rw [Graph.addMax_events, hya]
        exact Finset.mem_insert_self _ _
      · right
        have hidx := idx_eq_of_mem_avail ha.1
        have htid : y.tid ≠ a.tid := fun h => hya (avail_tid_inj h1 ha.1 h)
        have htr := Graph.trace_addMax_of_ne (p := ρ) hW hidx htid
        obtain ⟨ht, hi, hs'⟩ := mem_avail_iff.mp h1
        refine mem_avail_iff.mpr ⟨ht, ?_, ?_⟩
        · rw [← Graph.trace_length, htr, Graph.trace_length]
          exact hi
        · rw [htr]
          exact hs'

/-- `MaxCompletion` adds events in the maximal way, and this stays visible in
the graph it returns: a write that is coherence-after the source of an added
read, or after an added write, is itself added, and later. -/
theorem ComplStep.co_order {e : TEv} {G G' : Graph} (hG : G.Wf) (hE : P.Exec G)
    (he : e ∈ P.avail G) (h : Relation.ReflTransGen (ComplStep P ρ e) G G') :
    ∀ p ∈ G'.events, p ∉ G.events → ∀ e' : Ev,
      (p.IsRead → G'.rf p = some e') → (¬ p.IsRead → e' = .th p) →
      ∀ w, G'.coRelAt p.loc e' (.th w) → w ∉ G.events ∧ nextLt p w := by
  induction h with
  | refl => exact fun p hp hp' => absurd hp hp'
  | @tail G1 G2 hch hs ih =>
    obtain ⟨hW, hE1, he1, hsub, -⟩ := ComplStep.chain hG hE he hch
    obtain ⟨c1, -⟩ := ComplStep.order hG hE he hch
    obtain ⟨a, ha, hae, rfl⟩ := hs
    have hna := not_mem_of_mem_avail hW ha.1
    intro p hp hpG e' her henr w hco
    rw [Graph.addMax_events] at hp
    rcases Finset.mem_insert.mp hp with hpa | hp1
    · exfalso
      rw [hpa] at her henr hco
      rcases a.act.isRead_or_isWrite_or_isLocal with hk | hk | hk
      · have hact := TEv.IsRead.exists_act hk
        have he' := her hk
        rw [Graph.addMax_read hact, Graph.addRead_rf, Function.update_self] at he'
        rw [Graph.addMax_read hact, ← Option.some.inj he'] at hco
        have hco' : G1.coRelAt a.loc (G1.maxWrite a.loc) (.th w) := hco
        have hwm : w ∈ G1.co a.loc := by
          cases hmw : G1.maxWrite a.loc with
          | init =>
            rw [hmw] at hco'
            exact hco'
          | th m =>
            rw [hmw] at hco'
            exact hco'.2.1
        exact Graph.maxWrite_co_maximal hW a.loc (w := .th w) ((hW.co_mem a.loc w).mp hwm)
          ((G1.coRel_iff_exists _ _).mpr ⟨a.loc, hco'⟩)
      · rw [henr hk.not_isRead] at hco
        rcases Graph.coRelAt_addMax hW hna hco with h1 | h1
        · exact hna ((hW.co_mem _ _).mp h1.1).1
        · rw [h1] at hco
          exact List.Before.irrefl _ _ hco
      · rw [henr hk.not_isRead] at hco
        rcases Graph.coRelAt_addMax hW hna hco with h1 | h1
        · exact hna ((hW.co_mem _ _).mp h1.1).1
        · rw [h1] at hco
          exact List.Before.irrefl _ _ hco
    · have hpa : p ≠ a := fun h => hna (h ▸ hp1)
      have her1 : p.IsRead → G1.rf p = some e' := by
        intro hr
        rw [← Graph.addMax_rf_of_ne (p := ρ) G1 hpa]
        exact her hr
      rcases Graph.coRelAt_addMax hW hna hco with h1 | h1
      · exact ih p hp1 hpG e' her1 henr w h1
      · rw [h1]
        exact ⟨fun h => hna (hsub h), c1 p hp1 hpG a ha.1⟩

/-- The outcome of a constraint evaluation that `MaxCompletion` adds is the
choice for the literals of the graph in which it is added: the events of the
starting graph and the events added before it. -/
theorem ComplStep.pol_added {e : TEv} {G G' : Graph} (hG : G.Wf) (hE : P.Exec G)
    (he : e ∈ P.avail G) (h : Relation.ReflTransGen (ComplStep P ρ e) G G') :
    ∀ p ∈ G'.events, p ∉ G.events → ∀ φ, p.act = .cons φ → ∀ s : Finset TEv,
      (∀ q ∈ G'.events, q.IsCons → (q ∈ s ↔ q ∈ G.events ∨ nextLt q p)) →
      G'.pol p = some (ρ (G'.restrict s).F φ) := by
  induction h with
  | refl => exact fun p hp hp' => absurd hp hp'
  | @tail G1 G2 hch hs ih =>
    obtain ⟨hW, hE1, he1, hsub, -⟩ := ComplStep.chain hG hE he hch
    obtain ⟨c1, -⟩ := ComplStep.order hG hE he hch
    obtain ⟨a, ha, hae, rfl⟩ := hs
    have hna := not_mem_of_mem_avail hW ha.1
    intro p hp hpG φ hact s hs
    rw [Graph.addMax_events] at hp
    rcases Finset.mem_insert.mp hp with hpa | hp1
    · rw [hpa] at hact hs ⊢
      have hpol : (G1.addMax ρ a).pol a = some (ρ G1.F φ) := by
        rw [Graph.addMax_cons hact]
        simp
      have hF : ((G1.addMax ρ a).restrict s).F = G1.F := by
        have h1 := (G1.addMax ρ a).F_restrict_congr (s := s) (s' := G1.events)
          (fun q hq hc => by
            rw [hs q hq hc]
            rw [Graph.addMax_events] at hq
            rcases Finset.mem_insert.mp hq with hqa | hq1
            · rw [hqa]
              exact ⟨fun h => h.elim (fun h' => absurd (hsub h') hna)
                (fun h' => absurd h' (nextLt_irrefl _)), fun h => absurd h hna⟩
            · refine ⟨fun _ => hq1, fun _ => ?_⟩
              by_cases hqG : q ∈ G.events
              · exact Or.inl hqG
              · exact Or.inr (c1 q hq1 hqG a ha.1))
        rw [h1, Graph.restrict_addMax hW hna]
      rw [hpol, hF]
    · have hpa : p ≠ a := fun h => hna (h ▸ hp1)
      have hlt : nextLt p a := c1 p hp1 hpG a ha.1
      have ih' := ih p hp1 hpG φ hact s (fun q hq hc => hs q (by
        rw [Graph.addMax_events]
        exact Finset.mem_insert_of_mem hq) hc)
      have hF : ((G1.addMax ρ a).restrict s).F = (G1.restrict s).F := by
        have h1 := (G1.addMax ρ a).F_restrict_congr (s := s) (s' := G1.events ∩ s)
          (fun q hq hc => by
            rw [Graph.addMax_events] at hq
            rcases Finset.mem_insert.mp hq with hqa | hq1
            · rw [hqa]
              have hns : a ∉ s := by
                intro h
                have hq' : a ∈ (G1.addMax ρ a).events := by
                  rw [Graph.addMax_events]
                  exact Finset.mem_insert_self _ _
                rcases (hs a hq' (hqa ▸ hc)).mp h with h' | h'
                · exact hna (hsub h')
                · exact nextLt_irrefl _ (nextLt_trans hlt h')
              exact ⟨fun h => absurd h hns, fun h => absurd (Finset.mem_inter.mp h).2 hns⟩
            · exact ⟨fun h => Finset.mem_inter.mpr ⟨hq1, h⟩, fun h => (Finset.mem_inter.mp h).2⟩)
        rw [h1, ← Graph.restrict_restrict, Graph.restrict_addMax hW hna]
      rw [Graph.addMax_pol_of_ne G1 hpa, ih', hF]

/-! ### Proposition A.28, the case of a non-revisit step -/

theorem Reach.step_of_prevStep_nr {Gf X : Graph} {c : Config} {e : TEv}
    (hM : M.Extensible) (hGf : Gf.Wf) (hEf : P.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.Full Gf)
    (hX : PrevReach P τ Gf X) (hc : Reach P (M.sym S) τ c) (hs : PrevStep P τ X e .nr c.abs) :
    ∃ c', StepL P (M.sym S) τ c e .nr c' ∧ c'.abs = X := by
  obtain ⟨hXW, -, hXc⟩ := PrevReach.inv hM hGf hEf hcf hX
  obtain ⟨-, -, hcc, -⟩ := hc.sound
  have hnext := PrevReach.next_of_prevStep hM hGf hEf hcf hff hX hs
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
    exact ⟨c.addRead e w, StepL.read hcc hnext hact hwt' (hdec ▸ hXc), hdec⟩
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
    exact ⟨c.addWrite e wp, StepL.write hcc hnext hw (habs ▸ hwp) (hdec ▸ hXc), hdec⟩
  · have hdec : (c.addLoc e (X.pol e)).abs = X := by
      rw [Config.addLoc_abs, habs]
      exact Graph.remove_addLoc hXW he hk hsink
    by_cases hcs : e.IsCons
    · obtain ⟨b, hb⟩ := hXW.exists_pol he hcs
      rw [hb] at hdec
      exact ⟨_, StepL.sym hcc hnext hcs (hdec ▸ hXc), hdec⟩
    · have hb : X.pol e = none := by
        by_contra h
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h
        exact hcs (hXW.pol_some hb).2
      rw [hb] at hdec
      exact ⟨_, StepL.loc hcc hnext hk hcs (hdec ▸ hXc), hdec⟩

/-! ### Proposition A.28, the case of a revisit step: preparations -/

namespace Graph

/-- The source of a read is a write. -/
theorem Wf.isWrite_of_src {G : Graph} (hG : G.Wf) {q s : TEv} (h : G.rf q = some (.th s)) :
    s.IsWrite := by
  have hq := (hG.rf_source_mem h).1
  have hr : q.IsRead := by
    by_contra hn
    rw [hG.rf_none q (Or.inr hn)] at h
    cases h
  obtain ⟨w, hw, hwt⟩ := hG.rf_read q hq _ (TEv.IsRead.exists_act hr)
  rw [h] at hw
  rw [← Option.some.inj hw] at hwt
  obtain ⟨-, v, hv⟩ := hwt
  simp [TEv.IsWrite, hv, Act.IsWrite]

/-- From an event of a finite acyclic graph one reaches a causally maximal
event. -/
theorem exists_maximal_reach {G : Graph} (hG : G.Wf) (hac : Maz.Acyclic G.porfStep) {e : TEv}
    (he : e ∈ G.events) :
    ∃ z ∈ G.events, (z = e ∨ G.porf (.th e) (.th z)) ∧ ∀ b, ¬ G.porf (.th z) b := by
  classical
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
  refine ⟨z', ?_, ?_, ?_⟩
  · rcases hz' with rfl | ⟨h, -⟩
    · exact he
    · exact h
  · rcases hz' with rfl | ⟨-, h⟩
    · exact Or.inl rfl
    · exact Or.inr h
  · intro b hb
    obtain ⟨c, hc⟩ := Maz.exists_first_of_transGen hb
    cases c with
    | init => exact G.not_porfStep_init _ hc
    | th c' =>
      exact hzmax (.th c')
        ((hs _).mpr ⟨c', rfl, Or.inr ⟨(hG.mem_of_porfStep hc).2, hreach _ hc⟩⟩) hc

/-- No causality path leads from a thread event to `init`. -/
theorem not_reach_init (G : Graph) (p : TEv) :
    ¬ Relation.ReflTransGen G.porfStep (.th p) .init := by
  intro h
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, -, hc⟩
  · cases h
  · exact G.not_porfStep_init _ hc

end Graph

theorem TEv.not_isRead_of_isWrite {q : TEv} (hw : q.IsWrite) (hr : q.IsRead) : False :=
  hw.not_isRead hr

theorem Config.lt_trans {c : Config} {x y z : TEv} (h1 : c.lt x y) (h2 : c.lt y z) : c.lt x z :=
  List.Before.trans h2 h1

/-- The data of the revisit case of Proposition A.28: `c` is reached, and the
backward step from `X` is a revisit of `a` by `e` that returns the graph of
`c`. `hs1` is (S1) of Proposition A.23 for `X`. -/
structure RvData (P : Program) (M : Model) {S : Solver} (τ : TieBreak S) (X : Graph)
    (c : Config) (a e : TEv) : Prop where
  hXW : X.Wf
  hXE : P.Exec X
  hXc : (M.sym S).cons X
  hs1 : ∀ y ∈ P.avail X, ∀ m, X.IsMe m → ¬ nextLtEv (.th y) m
  hc : Reach P (M.sym S) τ c
  hs : PrevStep P τ X e (.rv a) c.abs

namespace RvData

variable {X : Graph} {c : Config} {a e : TEv}

theorem me (D : RvData P M τ X c a e) : X.IsMe (.th a) := D.hs.rv_inv.1
theorem rf (D : RvData P M τ X c a e) : X.rf a = some (.th e) := D.hs.rv_inv.2.2.1
theorem lt (D : RvData P M τ X c a e) : nextLt a e := D.hs.rv_inv.2.2.2.1
theorem po (D : RvData P M τ X c a e) : ∀ b, X.porf (.th e) b ↔ b = .th a := D.hs.rv_inv.2.2.2.2.1
theorem mc (D : RvData P M τ X c a e) :
    MaxCompl P (τ.pref (X.remove {a, e}).F) (X.remove {a, e}) e c.abs :=
  D.hs.rv_inv.2.2.2.2.2

theorem pref (D : RvData P M τ X c a e) : (X.remove {a, e}).IsPrefixOf X :=
  (rv_remove D.hXW D.hXE D.me D.rf D.po).1
theorem av (D : RvData P M τ X c a e) : e ∈ P.avail (X.remove {a, e}) :=
  (rv_remove D.hXW D.hXE D.me D.rf D.po).2
theorem W0 (D : RvData P M τ X c a e) : (X.remove {a, e}).Wf := D.hXW.of_isPrefixOf D.pref
theorem E0 (D : RvData P M τ X c a e) : P.Exec (X.remove {a, e}) := D.hXE.of_isPrefixOf D.hXW D.pref
theorem WY (D : RvData P M τ X c a e) : c.abs.Wf := D.hc.sound.1.1

theorem sub (D : RvData P M τ X c a e) : (X.remove {a, e}).events ⊆ c.abs.events :=
  (D.mc.facts D.W0 D.E0 D.av).2.2.2.1
theorem rfY (D : RvData P M τ X c a e) :
    ∀ q ∈ (X.remove {a, e}).events, c.abs.rf q = (X.remove {a, e}).rf q :=
  (D.mc.facts D.W0 D.E0 D.av).2.2.2.2.2.2

theorem mem_old_iff (_D : RvData P M τ X c a e) {p : TEv} :
    p ∈ (X.remove {a, e}).events ↔ p ∈ X.events ∧ p ≠ a ∧ p ≠ e := by
  simp only [Graph.remove, Graph.restrict, Finset.mem_inter, Finset.mem_sdiff,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  tauto

theorem mem_order (_D : RvData P M τ X c a e) {p : TEv} : p ∈ c.order ↔ p ∈ c.abs.events :=
  List.mem_toFinset.symm

theorem e_mem (D : RvData P M τ X c a e) : e ∈ X.events := (D.hXW.rf_source_mem D.rf).2

theorem e_not_mem (D : RvData P M τ X c a e) : e ∉ c.abs.events :=
  not_mem_of_mem_avail D.WY D.mc.2.1

theorem e_idx (D : RvData P M τ X c a e) : e.idx = c.abs.cnt e.tid :=
  idx_eq_of_mem_avail D.mc.2.1

/-- The labels: `a` reads the location that `e` writes. -/
theorem acts (D : RvData P M τ X c a e) : ∃ x v, a.act = .read x ∧ e.act = .write x v := by
  have hr := D.hs.rv_inv.2.1
  obtain ⟨x, hx⟩ : ∃ x, a.act = .read x := ⟨_, TEv.IsRead.exists_act hr⟩
  obtain ⟨w, hw, hwt⟩ := D.hXW.rf_read a D.me.1 x hx
  rw [D.rf] at hw
  rw [← Option.some.inj hw] at hwt
  obtain ⟨-, v, hv⟩ := hwt
  exact ⟨x, v, hx, hv⟩

theorem e_write (D : RvData P M τ X c a e) : e.IsWrite := D.hXW.isWrite_of_src D.rf

theorem a_sink (D : RvData P M τ X c a e) (b : Ev) : ¬ X.porfStep (.th a) b :=
  fun h => D.me.2.1 b (Relation.TransGen.single h)

theorem tid_ne (D : RvData P M τ X c a e) : a.tid ≠ e.tid := by
  intro h
  have ha : a ∈ X.events := D.me.1
  rcases Nat.lt_trichotomy a.idx e.idx with h1 | h1 | h1
  · exact D.a_sink (.th e) (Or.inl ⟨ha, D.e_mem, h, h1⟩)
  · have := D.hXW.idx_inj a ha e D.e_mem h h1
    exact nextLt_irrefl e (this ▸ D.lt)
  · exact nextLt_irrefl _ (nextLt_trans (nextLt_of_poT ⟨h.symm, h1⟩) D.lt)

/-- The sources of the events other than `a` are old. -/
theorem src_old (D : RvData P M τ X c a e) {q : TEv} (hq : q ∈ X.events) (hqa : q ≠ a) (w : Ev)
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
theorem a_added (D : RvData P M τ X c a e) : a ∈ c.abs.events ∧ a ∉ (X.remove {a, e}).events := by
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
theorem ge_a (D : RvData P M τ X c a e) {p : TEv} (hp : p ∈ c.abs.events)
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
theorem succ_added (D : RvData P M τ X c a e) {x y : TEv} (hx : x ∉ (X.remove {a, e}).events)
    (h : c.abs.porf (.th x) (.th y)) : y ∉ (X.remove {a, e}).events ∧ nextLt x y := by
  obtain ⟨-, -, -, c3, c4⟩ := ComplStep.order D.W0 D.E0 D.av D.mc.1
  exact ⟨fun hy => hx (D.W0.mem_of_porf (c4 _ _ h hy)).1, c3 x y hx h⟩

/-- An added event was inserted after every event that is `<next`-before it. -/
theorem not_lt_of_added (D : RvData P M τ X c a e) {v x : TEv} (hv : v ∈ c.abs.events)
    (hv0 : v ∉ (X.remove {a, e}).events) (hx : x ∈ c.order) (hlt : nextLt x v) :
    ¬ c.lt v x := by
  intro hlt'
  obtain ⟨s, q, hvs, hbw, hqx⟩ := D.hc.inv.p2 x hx v (D.mem_order.mpr hv) hlt hlt'
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
theorem lt_of_added (D : RvData P M τ X c a e) {u v : TEv} (hu : u ∈ c.order)
    (hv : v ∈ c.abs.events) (hv0 : v ∉ (X.remove {a, e}).events) (hlt : nextLt u v) :
    c.lt u v := by
  have hne : v ≠ u := fun h => nextLt_irrefl _ (h ▸ hlt)
  exact (List.Before.total (D.mem_order.mpr hv) hu hne).resolve_right
    (D.not_lt_of_added hv hv0 hu hlt)

/-- A causality path of `c.plus e` into `e` starts at an old event. -/
theorem plus_old (D : RvData P M τ X c a e) {p : TEv} (h : (c.plus e).porf (.th p) (.th e)) :
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
theorem plus_of_X (D : RvData P M τ X c a e) {x : TEv} (h : X.porf (.th x) (.th e)) :
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
theorem step_cases (D : RvData P M τ X c a e) {u u1 : TEv}
    (h : c.abs.porfStep (.th u) (.th u1)) :
    (c.lt u u1 ∨ c.Bw u u1) ∧ ∀ s, c.Bw s u → c.lt s u1 := by
  rcases h with hpo | ⟨q, hq, hqm, hrf⟩
  · exact ⟨Or.inl (D.hc.sound.2.1 u (D.mem_order.mpr hpo.1) u1 (D.mem_order.mpr hpo.2.1)
      hpo.2.2.1 hpo.2.2.2), fun s hbw => D.hc.bw_po_lt hbw hpo⟩
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
theorem lt_a_of_path (D : RvData P M τ X c a e) {y' : TEv} (hlt : nextLt y' a)
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
      rcases D.hc.inv.p6 u y' a hau hay hbw hlt (D.mem_order.mpr D.a_added.1) with h | h | h
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
theorem del_iff (D : RvData P M τ X c a e) (p : TEv) :
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
        Graph.exists_maximal_reach D.hXW ((M.sym S).porf_acyclic X D.hXW D.hXc) hpX
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
theorem not_previous (D : RvData P M τ X c a e) {p q : TEv} (hpo : p ∈ c.order)
    (hq : q ∈ c.abs.events) (hq0 : q ∉ (X.remove {a, e}).events) (hlt : nextLt p q) :
    ¬ c.Previous p e (.th q) := by
  rintro ⟨-, (rfl | h) | h⟩
  · exact nextLt_irrefl _ hlt
  · exact List.Before.asymm h (D.lt_of_added hpo hq hq0 hlt)
  · exact hq0 (D.plus_old h)

/-- The events that the revisit keeps: the events of `c` that are in `X`. -/
theorem keep_iff (D : RvData P M τ X c a e) (p : TEv) :
    p ∈ c.keep a e ↔ p ∈ c.abs.events ∧ p ∈ X.events := by
  rw [Config.mem_keep_iff, D.del_iff, D.mem_order]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by_contra fun h => h2 ⟨h1, h⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h.2 h2⟩

/-- The context of the revisit of `a` by `e` in `c` is the context of the
backward step: the literals of `X` without `a` and `e`. -/
theorem ctx_eq (D : RvData P M τ X c a e) : c.ctx a e = (X.remove {a, e}).F := by
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
theorem maxAdded (D : RvData P M τ X c a e) {p : TEv} (hp : c.Deleted a e p ∨ p = a) :
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
theorem step (D : RvData P M τ X c a e) :
    ∃ c', StepL P (M.sym S) τ c e (.rv a) c' ∧ c'.abs = X := by
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
  refine ⟨c.revisit a e wp, StepL.revisit D.hc.sound.2.2.1 D.mc.2 D.e_write
    (D.mem_order.mpr D.a_added.1) (by rw [hloc]; exact hax)
    (fun h => D.a_added.2 (D.plus_old h)) (fun p hp => D.maxAdded hp) hWT ?_, habs⟩
  rw [habs]
  exact D.hXc

end RvData

/-! ### Proposition A.28, Lemma A.29, Theorem A.30 -/

/-- The proof of Proposition A.28, step ⟨2⟩2: when the backward step from `X`
is a revisit of `a` by `e` and returns the graph of the reached configuration
`c`, the events that the revisit of `a` by `e` deletes from `c` are the events
of `c` that are not in `X`. -/
theorem Reach.deleted_iff_of_prevStep {Gf X : Graph} {c : Config} {a e : TEv}
    (hM : M.Extensible) (hGf : Gf.Wf) (hEf : P.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.Full Gf)
    (hX : PrevReach P τ Gf X) (hc : Reach P (M.sym S) τ c)
    (hs : PrevStep P τ X e (.rv a) c.abs) (p : TEv) :
    c.Deleted a e p ↔ p ∈ c.abs.events ∧ p ∉ X.events := by
  obtain ⟨hXW, hXE, hXc⟩ := PrevReach.inv hM hGf hEf hcf hX
  exact RvData.del_iff ⟨hXW, hXE, hXc,
    fun y hy m hm => PrevReach.s1 hM hGf hEf hcf hff hX hy hm, hc, hs⟩ p

/-- Proposition A.28, the case of a revisit step. -/
theorem Reach.step_of_prevStep_rv {Gf X : Graph} {c : Config} {a e : TEv}
    (hM : M.Extensible) (hGf : Gf.Wf) (hEf : P.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.Full Gf)
    (hX : PrevReach P τ Gf X) (hc : Reach P (M.sym S) τ c) (hs : PrevStep P τ X e (.rv a) c.abs) :
    ∃ c', StepL P (M.sym S) τ c e (.rv a) c' ∧ c'.abs = X := by
  obtain ⟨hXW, hXE, hXc⟩ := PrevReach.inv hM hGf hEf hcf hX
  exact RvData.step ⟨hXW, hXE, hXc,
    fun y hy m hm => PrevReach.s1 hM hGf hEf hcf hff hX hy hm, hc, hs⟩

/-- Proposition A.28: a backward step into the graph of a reached
configuration is matched by a step of Algorithm 1 from that configuration,
with the same event and kind. -/
theorem Reach.step_of_prevStep {Gf X : Graph} {c : Config} {e : TEv} {k : Kind}
    (hM : M.Extensible) (hGf : Gf.Wf) (hEf : P.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.Full Gf)
    (hX : PrevReach P τ Gf X) (hc : Reach P (M.sym S) τ c) (hs : PrevStep P τ X e k c.abs) :
    ∃ c', StepL P (M.sym S) τ c e k c' ∧ c'.abs = X := by
  cases k with
  | nr => exact Reach.step_of_prevStep_nr hM hGf hEf hcf hff hX hc hs
  | rv a => exact Reach.step_of_prevStep_rv hM hGf hEf hcf hff hX hc hs

/-- Lemma A.29: a graph of the backward chain from `G_f` from which the
backward steps reach the graph without thread events is the graph of a
reached configuration. -/
theorem PrevReach.reach {Gf X : Graph} (hM : M.Extensible) (hGf : Gf.Wf) (hEf : P.Exec Gf)
    (hcf : (M.sym S).cons Gf) (hff : P.Full Gf) (hX : PrevReach P τ Gf X)
    (h0 : Relation.ReflTransGen (fun G G' => ∃ e k, PrevStep P τ G e k G') X
      (Graph.init P.mem)) :
    ∃ c, Reach P (M.sym S) τ c ∧ c.abs = X := by
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
    obtain ⟨c', hst, h'⟩ := Reach.step_of_prevStep hM hGf hEf hcf hff hX hc hs
    exact ⟨c', hc.tail ⟨e, k, hst⟩, h'⟩

/-- Theorem A.30 (completeness): Algorithm 1 reaches every well-formed,
consistent, full execution of a bounded program. -/
theorem complete {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible) {Gf : Graph} (hGf : Gf.Wf)
    (hEf : P.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.Full Gf) :
    ∃ c, Reach P (M.sym S) τ c ∧ c.abs = Gf :=
  PrevReach.reach hM hGf hEf hcf hff Relation.ReflTransGen.refl
    (PrevReach.init hn hM hGf hEf hcf hff)

end Condpor
