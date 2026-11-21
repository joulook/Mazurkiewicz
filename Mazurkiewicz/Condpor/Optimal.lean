import Mazurkiewicz.Condpor.Complete

/-!
ConDpor, Theorem 5(a) (no two visited configurations with the same graph):
`path_unique`, `Reach.eq_of_abs_eq`, for the model `M.sym S`, any solver and
any tie-break. The proof extends that of TruSt; the references below are to
the TruSt paper.

# Optimality

Paper: Section 4.3, Theorem 4.2 (no duplicate exploration); Appendix A.7,
Proposition A.31, Theorem A.32. Coq: `trust/Optimal.v` (`PrevTruSt`,
`TruSt_Optimal_exec`, `TruSt_step_Optimapl`, `TruSt_Optimal`).

Theorem A.32: for every graph there is at most one run of Algorithm 1 from
the initial configuration that ends in it.

How the text is read here.

* Proposition A.31: a step of Algorithm 1 from a reached configuration is
  undone by the backward step, with the same event and kind:
  `Reach.prevStep_of_step`.
* A "production sequence" `σ` with `⟨∅, ∅⟩ ⇒^σ ⟨G, _⟩` is a path of the step
  relation from the initial configuration, `Maz.Path (Step P (M.sym S) τ)`; the list
  holds the configurations after each step. Theorem A.32 is `path_unique`:
  two such paths that end in configurations with the same graph are the same
  list of configurations. `Step` forgets the label of a step; on reached
  configurations the label is determined by the two configurations
  (`StepL.label_unique`).
* The last step of the paper's proof ("all configurations reached in the next
  step have different graph components") is `StepL.eq_of_abs_eq`, together
  with the equality of the labels from `Reach.pred_unique`.
* No hypothesis on the program (boundedness) or on the model (extensibility)
  is needed. Coq's `MaxCompletionG` obtains the completion from a general
  existence theorem that uses boundedness; here the completion is built from
  the finitely many deleted events.

The proof of Proposition A.31, with two repairs to the paper's proof that are
recorded in the plan.

* The case of a non-revisit step (the paper's ⟨1⟩3, ⟨2⟩3, ⟨3⟩1): the paper
  sets `a = e` (⟨4⟩1) and then uses `e >' a` and `⟨e, a⟩ ∈ G'.rf ∩ >' ∩ <next`
  with (P1). With `a = e` these are not meaningful, and the `rf` edge from
  the source to the newly added read goes forward in the insertion order, so
  (P1) does not apply. Here: if the revisit condition held for the added read
  `e` with source `w`, then `w` would be causally maximal in the graph before
  the step, so `w ≤next me` of that graph, and `e`, being available there, is
  not `<next`-before that `me` ((P5) of the step into that graph,
  `LastStep.p5b`); this contradicts `e <next w`.
* The case of a revisit of `r` by `e` (the paper's ⟨2⟩6, ⟨3⟩1-⟨3⟩7): the paper
  asserts that the events that differ are "exactly the events added by
  MaxCompletion, and in the precise way". Here this is proved: the events of
  `D = Del ∪ {r}` are added back one at a time in the insertion order of `c`,
  which on `D` is `<next` ((P3)). For a set `T ⊆ D` of still missing events
  that is closed under "inserted later, in `D`", with earliest element `d`:
  the missing events are closed under causal successors (line 25 excludes a
  backward reader of a deleted write); `d` is the next event (the other
  available events are later missing events, or are available in `c`, hence
  `e` or `<next`-after `e`, and `d <next e` by (P9), and by (P1) for `r`);
  and adding `d` in the maximal way gives the graph with `d`, since every
  event that is not missing is in `Previous(d, e)` and `d` is maximally
  added (lines 26-27).
* Clauses of Proposition A.22 used: (P1), (P3), (P4), (P9) for the step, and
  (P5) for the step into `c` (`LastStep`).
-/

namespace List

variable {α : Type*} [DecidableEq α]

/-- The last element of a filtered list: an element of it that is before no
other element of it. -/
theorem getLast?_filter_of_max {l : List α} {p : α → Bool} {s : α} (hl : l.Nodup)
    (hs : s ∈ l.filter p) (hmax : ∀ b ∈ l.filter p, ¬ l.Before s b) :
    (l.filter p).getLast? = some s := by
  have hne : l.filter p ≠ [] := List.ne_nil_of_mem hs
  rw [List.getLast?_eq_some_getLast hne]
  congr 1
  by_contra hms
  have hm : (l.filter p).getLast hne ∈ l.filter p := List.getLast_mem hne
  rcases Before.total hs hm (Ne.symm hms) with h | h
  · exact hmax _ hm (before_filter_iff.mp h).1
  · exact not_before_getLast (hl.filter _) hne s h

/-- Keeping one more element `d`, which is after all the kept elements, puts
`d` at the end of the filtered list. -/
theorem filter_eq_filter_append_singleton {l : List α} {p q : α → Bool} {d : α}
    (hl : l.Nodup) (hd : d ∈ l) (hp : ∀ b ∈ l, p b = true → l.Before b d)
    (hq : ∀ b ∈ l, q b = true ↔ (p b = true ∨ b = d)) :
    l.filter q = l.filter p ++ [d] := by
  induction l with
  | nil => simp at hd
  | cons h t ih =>
    obtain ⟨hht, ht⟩ := List.nodup_cons.mp hl
    by_cases hhd : h = d
    · subst hhd
      have hnp : ∀ b ∈ t, ¬ p b = true := by
        intro b hb hpb
        rcases before_cons_iff.mp (hp b (mem_cons_of_mem _ hb) hpb) with ⟨h1, -, -⟩ | ⟨-, h1, -⟩
        · exact hht (h1 ▸ hb)
        · exact h1 rfl
      have hph : ¬ p h = true := fun hph => Before.irrefl _ _ (hp h mem_cons_self hph)
      have hqt : ∀ b ∈ t, ¬ q b = true := by
        intro b hb hqb
        rcases (hq b (mem_cons_of_mem _ hb)).mp hqb with h1 | h1
        · exact hnp b hb h1
        · exact hht (h1 ▸ hb)
      have hqh : q h = true := (hq h mem_cons_self).mpr (Or.inr rfl)
      rw [filter_cons_of_pos hqh, filter_cons_of_neg hph, filter_eq_nil_iff.mpr hqt,
        filter_eq_nil_iff.mpr hnp]
      rfl
    · have hdt : d ∈ t := (mem_cons.mp hd).resolve_left (Ne.symm hhd)
      have ih' := ih ht hdt (fun b hb hpb => by
        rcases before_cons_iff.mp (hp b (mem_cons_of_mem _ hb) hpb) with ⟨h1, -, -⟩ | ⟨-, -, h1⟩
        · exact absurd (h1 ▸ hb) hht
        · exact h1) (fun b hb => hq b (mem_cons_of_mem _ hb))
      have hqh : q h = true ↔ p h = true := by
        rw [hq h mem_cons_self]
        exact ⟨fun h' => h'.resolve_right hhd, Or.inl⟩
      by_cases hph : p h = true
      · rw [filter_cons_of_pos (hqh.mpr hph), filter_cons_of_pos hph, ih']
        rfl
      · rw [filter_cons_of_neg (fun h' => hph (hqh.mp h')), filter_cons_of_neg hph, ih']

end List

namespace Condpor

open Program

variable {P : Program} {M : Model} {S : Solver} {τ : TieBreak S}

/-! ### Auxiliary facts on steps -/

theorem Config.eq_of_abs_order {c1 c2 : Config} (h : c1.abs = c2.abs)
    (ho : c1.order = c2.order) : c1 = c2 := by
  cases c1
  cases c2
  simp only [Config.abs, Graph.mk.injEq] at h
  obtain ⟨h1, -, h3, h4, h5⟩ := h
  simp only at ho
  subst h1 ho h3 h4 h5
  rfl

/-- The event of a step is in the configuration after the step. -/
theorem StepL.mem_order {c c' : Config} {e : TEv} {k : Kind} (h : StepL P (M.sym S) τ c e k c') :
    e ∈ c'.order := by
  cases k with
  | nr =>
    obtain ⟨-, -, hcase⟩ := h.nr_inv
    rcases hcase with ⟨x, w, -, -, rfl⟩ | ⟨wp, -, -, rfl⟩ | ⟨b, -, rfl⟩ | ⟨-, -, rfl⟩ <;>
      exact List.mem_cons_self
  | rv r =>
    obtain ⟨wp, rfl, -⟩ := h.rv_inv
    exact List.mem_cons_self

/-! ### Proposition A.31, the case of a non-revisit step -/

theorem Reach.prevStep_of_step_nr {c c' : Config} {e : TEv} (hc : Reach P (M.sym S) τ c)
    (hs : StepL P (M.sym S) τ c e .nr c') : PrevStep P τ c'.abs e .nr c.abs := by
  obtain ⟨hcw, hcpo, -, -⟩ := hc.sound
  have N := hs.nrFacts hcw
  have hme : c'.abs.IsMe (.th e) := (hc.a22 hs).p4
  have hW' : c'.abs.Wf := (hs.wf hcw hcpo).1
  have he : e ∉ c.abs.events := fun h => N.fresh (List.mem_toFinset.mp h)
  have hev : c'.abs.events = insert e c.abs.events := by
    change c'.order.toFinset = insert e c.order.toFinset
    rw [N.order, List.toFinset_cons]
  have hrem : c'.abs.remove {e} = c.abs := by
    obtain ⟨-, -, hcase⟩ := hs.nr_inv
    have hfin : c'.abs.events \ {e} = c.abs.events := by
      rw [hev, Finset.sdiff_singleton_eq_erase, Finset.erase_insert he]
    unfold Graph.remove
    rw [hfin]
    rcases hcase with ⟨x, w, -, -, rfl⟩ | ⟨wp, -, -, rfl⟩ | ⟨b, -, rfl⟩ | ⟨-, -, rfl⟩
    · rw [Config.addRead_abs]
      exact Graph.restrict_addRead hcw.1 he
    · rw [Config.addWrite_abs]
      exact Graph.restrict_addWrite hcw.1 he
    · rw [Config.addLoc_abs]
      exact Graph.restrict_addLoc hcw.1 he
    · rw [Config.addLoc_abs]
      exact Graph.restrict_addLoc hcw.1 he
  rw [← hrem]
  refine PrevStep.nr hme ?_
  rintro ⟨w, -, hrf, hlt, hpo⟩
  have hwe : w ≠ e := fun h => nextLt_irrefl _ (h ▸ hlt)
  have hwE : w ∈ c.abs.events := by
    have hw' : w ∈ c'.abs.events := (hW'.rf_source_mem hrf).2
    rw [hev] at hw'
    exact (Finset.mem_insert.mp hw').resolve_left hwe
  have hne : c.order ≠ [] := List.ne_nil_of_mem (List.mem_toFinset.mp hwE)
  obtain ⟨e0, k0, L⟩ := hc.lastStep hne
  have hwmax : ∀ b, ¬ c.abs.porf (.th w) b := by
    intro b hb
    have hb' : c'.abs.porf (.th w) b :=
      Graph.porf_mono (by rw [hev]; exact Finset.subset_insert _ _)
        (fun q hq => N.rf_old q (fun h => he (h ▸ hq))) hb
    rw [(hpo b).mp hb'] at hb
    exact he (hcw.1.mem_of_porf hb).2
  have hem : ¬ nextLt e (k0.me e0) := L.p5b e hs.nr_inv.2.1.1
  by_cases hwm : w = k0.me e0
  · exact hem (hwm ▸ hlt)
  · exact hem (nextLt_trans hlt
      (L.me.2.2 (.th w) hwE hwmax (fun h => hwm (Ev.th.inj h))))

/-- Proposition A.31, the case of a revisit step. -/
theorem Reach.prevStep_of_step_rv {c c' : Config} {e r : TEv} (hc : Reach P (M.sym S) τ c)
    (hs : StepL P (M.sym S) τ c e (.rv r) c') : PrevStep P τ c'.abs e (.rv r) c.abs := by
  classical
  obtain ⟨hcw, hcpo, -, hcE⟩ := hc.sound
  have A := hc.a22 hs
  obtain ⟨wp, rfl, H⟩ := hs.rvHyp hcw hcpo
  have hW := hcw.1
  have heE : e ∉ c.abs.events := fun h => H.fresh (List.mem_toFinset.mp h)
  have hrE : r ∈ c.abs.events := List.mem_toFinset.mpr H.hr
  have hrR : r.IsRead := by simp [TEv.IsRead, H.hract, Act.IsRead]
  have mo : ∀ {p : TEv}, p ∈ c.order ↔ p ∈ c.abs.events := List.mem_toFinset.symm
  -- `r <next e`, by (P1)
  have hre : nextLt r e :=
    (nextLt_total (Ne.symm H.w_ne_r)).resolve_right
      (A.p1 e r (H.bw_iff.mpr (Or.inl ⟨rfl, rfl⟩)))
  -- the set `D = Del ∪ {r}`
  let D : Finset TEv := c.abs.events.filter (fun p => c.Deleted r e p ∨ p = r)
  have mem_D : ∀ {p : TEv}, p ∈ D ↔ c.Deleted r e p ∨ p = r := by
    intro p
    simp only [D, Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · rintro (h | h)
      · exact ⟨mo.mp h.1, Or.inl h⟩
      · exact ⟨h ▸ hrE, Or.inr h⟩
  have hDE : ∀ d ∈ D, d ∈ c.abs.events := fun d hd => (Finset.mem_filter.mp hd).1
  have hDlt : ∀ d ∈ D, d = r ∨ c.lt r d := fun d hd =>
    (mem_D.mp hd).elim (fun h => Or.inr h.2.1) Or.inl
  have hDe : ∀ d ∈ D, nextLt d e := by
    intro d hd
    rcases mem_D.mp hd with h | rfl
    · have hde : d ≠ e := by
        rintro rfl
        exact H.fresh h.1
      exact (nextLt_total hde).resolve_right (A.p9 r rfl d h)
    · exact hre
  have hDnp : ∀ d ∈ D, ¬ (c.plus e).porf (.th d) (.th e) := by
    intro d hd
    rcases mem_D.mp hd with h | rfl
    · exact h.2.2
    · exact H.hnp
  have hD3 : ∀ x ∈ D, ∀ y ∈ D, c.lt x y → nextLt x y := fun x hx y hy =>
    (A.p3 r rfl x y (mem_D.mp hx) (mem_D.mp hy)).mp
  have hDmax : ∀ d ∈ D, c.IsMaximallyAdded τ (c.ctx r e) d e :=
    fun d hd => H.hmax d (mem_D.mp hd)
  -- a causal successor of an event of `D` is in `D`, and was inserted later
  have Sc : ∀ x ∈ D, ∀ y, c.abs.porfStep (.th x) (.th y) → y ∈ D ∧ c.lt x y := by
    intro x hx y hstep
    have hyo : y ∈ c.order := mo.mpr (hW.mem_of_porfStep hstep).2
    have hxo : x ∈ c.order := mo.mpr (hDE x hx)
    have hplus : (c.plus e).porfStep (.th x) (.th y) :=
      Graph.porfStep_mono (G := c.abs) (G' := c.plus e) (Finset.subset_insert _ _)
        (fun _ _ => rfl) hstep
    have key : c.lt x y → y ∈ D ∧ c.lt x y := by
      intro h
      refine ⟨mem_D.mpr (Or.inl ⟨hyo, ?_,
        fun hp => hDnp x hx (Relation.TransGen.head hplus hp)⟩), h⟩
      rcases hDlt x hx with rfl | h'
      · exact h
      · exact Config.lt_trans h' h
    rcases hstep with hpo | ⟨q, hq, hqm, hrf⟩
    · exact key (hcpo x hxo y hyo hpo.2.2.1 hpo.2.2.2)
    · rw [← Ev.th.inj hq] at hrf
      have hxw : x.IsWrite := hW.isWrite_of_src hrf
      have hne : y ≠ x := fun h' => TEv.not_isRead_of_isWrite hxw (h' ▸ hW.isRead_of_rf hrf)
      rcases List.Before.total hyo hxo hne with h | h
      · exact key h
      · exfalso
        have hxr : x ≠ r := fun h' => TEv.not_isRead_of_isWrite hxw (h' ▸ hrR)
        have hxd : c.Deleted r e x := (mem_D.mp hx).resolve_right hxr
        exact (H.hmax x (Or.inl hxd)).1 ⟨y, ⟨hyo, Or.inl (Or.inr h)⟩, hrf⟩
  -- an event outside `D` is in `Previous(d, e)` for every `d` in `D`
  have prevD : ∀ b ∈ c.abs.events, b ∉ D → ∀ d ∈ D, c.Previous d e (.th b) := by
    intro b hb hbD d hd
    refine ⟨mo.mpr hb, ?_⟩
    by_cases hp : (c.plus e).porf (.th b) (.th e)
    · exact Or.inr hp
    · left
      right
      have hbr : b ≠ r := fun h => hbD (mem_D.mpr (Or.inr h))
      have hnl : ¬ c.lt r b := fun h => hbD (mem_D.mpr (Or.inl ⟨mo.mpr hb, h, hp⟩))
      have hbr' : c.lt b r := (List.Before.total (mo.mpr hb) H.hr hbr).resolve_left hnl
      rcases hDlt d hd with rfl | h
      · exact hbr'
      · exact Config.lt_trans hbr' h
  -- upward-closed subsets of `D`
  let UC : Finset TEv → Prop := fun T => T ⊆ D ∧ ∀ d ∈ T, ∀ d' ∈ D, c.lt d d' → d' ∈ T
  have closed : ∀ T, UC T →
      Maz.PrefixClosed c.abs.porfStep (Graph.evSet (c.abs.events ∩ (c.abs.events \ T))) := by
    intro T hT x y hxy hy
    cases x with
    | init => trivial
    | th q =>
      have hq : q ∈ c.abs.events := (hW.mem_of_porfStep hxy).1
      refine Finset.mem_inter.mpr ⟨hq, Finset.mem_sdiff.mpr ⟨hq, fun hqT => ?_⟩⟩
      cases y with
      | init => exact c.abs.not_porfStep_init _ hxy
      | th y' =>
        obtain ⟨hy'D, hlt⟩ := Sc q (hT.1 hqT) y' hxy
        have hy' : y' ∈ c.abs.events ∩ (c.abs.events \ T) := hy
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hy').2).2 (hT.2 q hqT y' hy'D hlt)
  have srcT : ∀ T, UC T → ∀ q ∈ c.abs.events, q ∉ T → ∀ w, c.abs.rf q = some w →
      w ∈ Graph.evSet (c.abs.events \ T) := by
    intro T hT q hq hqT w hw
    cases w with
    | init => trivial
    | th w' =>
      have h1 : Ev.th w' ∈ Graph.evSet (c.abs.events ∩ (c.abs.events \ T)) :=
        closed T hT (Or.inr ⟨q, rfl, hq, hw⟩)
          (Finset.mem_inter.mpr ⟨hq, Finset.mem_sdiff.mpr ⟨hq, hqT⟩⟩)
      have h1' : w' ∈ c.abs.events ∩ (c.abs.events \ T) := h1
      exact (Finset.mem_inter.mp h1').2
  -- one round of the loop: add the earliest missing event
  have stepT : ∀ T, UC T → ∀ d ∈ T, (∀ d' ∈ T, ¬ c.lt d' d) →
      ComplStep P (τ.pref (c.abs.restrict (c.abs.events \ D)).F) e
        (c.abs.restrict (c.abs.events \ T))
        (c.abs.restrict (c.abs.events \ T.erase d)) ∧ UC (T.erase d) := by
    intro T hT d hdT hmin
    have hdD := hT.1 hdT
    have hdE := hDE d hdD
    have hWT : (c.abs.restrict (c.abs.events \ T)).Wf := hW.restrict (closed T hT)
    have hUC' : UC (T.erase d) := by
      refine ⟨fun x hx => hT.1 (Finset.mem_of_mem_erase hx), fun d1 hd1 d2 hd2 hlt => ?_⟩
      have hd1T := Finset.mem_of_mem_erase hd1
      refine Finset.mem_erase.mpr ⟨fun h => hmin d1 hd1T (h ▸ hlt), hT.2 d1 hd1T d2 hd2 hlt⟩
    refine ⟨?_, hUC'⟩
    -- the first missing event of a thread is available
    have availT : ∀ q0 ∈ T, (∀ q ∈ T, q.tid = q0.tid → ¬ q.idx < q0.idx) →
        q0 ∈ P.avail (c.abs.restrict (c.abs.events \ T)) := by
      intro q0 hq0 hq0min
      refine mem_avail_restrict hW hcE (hDE q0 (hT.1 hq0))
        (fun h => (Finset.mem_sdiff.mp h).2 hq0) (fun q hq ht hi => ?_)
        (fun q hq ht hi w hw => srcT T hT q hq (fun hqT => hq0min q hqT ht hi) w hw) hWT
      exact Finset.mem_sdiff.mpr ⟨hq, fun hqT => hq0min q hqT ht hi⟩
    have hdav : d ∈ P.avail (c.abs.restrict (c.abs.events \ T)) :=
      availT d hdT (fun q hqT ht hi =>
        hmin q hqT (hcpo q (mo.mpr (hDE q (hT.1 hqT))) d (mo.mpr hdE) ht hi))
    -- an event outside `T` is in `Previous(d, e)`
    have hprev : ∀ b ∈ c.abs.events, b ∉ T → c.Previous d e (.th b) := by
      intro b hb hbT
      by_cases hbD : b ∈ D
      · have hbd : b ≠ d := fun h => hbT (h ▸ hdT)
        have hnl : ¬ c.lt d b := fun h => hbT (hT.2 d hdT b hbD h)
        exact ⟨mo.mpr hb, Or.inl (Or.inr
          ((List.Before.total (mo.mpr hb) (mo.mpr hdE) hbd).resolve_left hnl))⟩
      · exact prevD b hb hbD d hdD
    -- the source of `d` is not missing
    have hsrcd : ∀ w', c.abs.rf d = some (.th w') → w' ∉ T := by
      intro w' hw' hwT
      exact hmin w' hwT (Sc w' (hT.1 hwT) d (Or.inr ⟨d, rfl, hdE, hw'⟩)).2
    have hins : c.abs.events \ T.erase d = insert d (c.abs.events \ T) := by
      ext p
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, not_and]
      constructor
      · rintro ⟨hp, hpT⟩
        by_cases hpd : p = d
        · exact Or.inl hpd
        · exact Or.inr ⟨hp, fun h => hpT hpd h⟩
      · rintro (rfl | ⟨hp, hpT⟩)
        · exact ⟨hdE, fun h _ => h rfl⟩
        · exact ⟨hp, fun _ h => hpT h⟩
    -- the sources of the other events
    have hrf_other : ∀ q, q ≠ d →
        (c.abs.restrict (insert d (c.abs.events \ T))).rf q =
          (c.abs.restrict (c.abs.events \ T)).rf q := by
      intro q hqd
      by_cases hq : q ∈ c.abs.events ∩ (c.abs.events \ T)
      · have hqE := (Finset.mem_inter.mp hq).1
        have hqT := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hq).2).2
        rw [c.abs.restrict_rf_of_source_kept hq (fun w hw => srcT T hT q hqE hqT w hw),
          c.abs.restrict_rf_of_source_kept
            (Finset.mem_inter.mpr ⟨hqE, Finset.mem_insert_of_mem (Finset.mem_inter.mp hq).2⟩)
            (fun w hw => Graph.evSet_mono (Finset.subset_insert _ _)
              (srcT T hT q hqE hqT w hw))]
      · rw [c.abs.restrict_rf_of_not_mem hq, c.abs.restrict_rf_of_not_mem]
        intro h
        obtain ⟨h1, h2⟩ := Finset.mem_inter.mp h
        exact hq (Finset.mem_inter.mpr ⟨h1, (Finset.mem_insert.mp h2).resolve_left hqd⟩)
    have hev : (c.abs.restrict (insert d (c.abs.events \ T))).events =
        insert d (c.abs.restrict (c.abs.events \ T)).events := by
      ext p
      simp only [Graph.restrict_events, Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨hp, rfl | h⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hp, h⟩
      · rintro (rfl | ⟨hp, h⟩)
        · exact ⟨hdE, Or.inl rfl⟩
        · exact ⟨hp, Or.inr h⟩
    refine ⟨d, ⟨hdav, fun y hy hyd => ?_⟩, fun h => nextLt_irrefl _ (h ▸ hDe d hdD), ?_⟩
    · -- `d` is the `<next`-least available event
      by_cases hex : ∃ q ∈ T, q.tid = y.tid
      · obtain ⟨q1, hq1, hq1t⟩ := hex
        obtain ⟨q0, hq0, hq0min⟩ := (T.filter (fun q => q.tid = y.tid)).exists_min_image
          TEv.idx ⟨q1, Finset.mem_filter.mpr ⟨hq1, hq1t⟩⟩
        obtain ⟨hq0T, hq0t⟩ := Finset.mem_filter.mp hq0
        have hq0av := availT q0 hq0T (fun q hqT ht hi =>
          Nat.not_lt.mpr (hq0min q (Finset.mem_filter.mpr ⟨hqT, ht.trans hq0t⟩)) hi)
        have hyq : y = q0 := avail_tid_inj hy hq0av hq0t.symm
        have hyT : y ∈ T := hyq ▸ hq0T
        have hlt : c.lt d y :=
          (List.Before.total (mo.mpr (hDE y (hT.1 hyT))) (mo.mpr hdE) hyd).resolve_right
            (hmin y hyT)
        exact hD3 d hdD y (hT.1 hyT) hlt
      · have hnone : ∀ q ∈ c.abs.events, q.tid = y.tid → q ∉ T :=
          fun q _ ht hqT => hex ⟨q, hqT, ht⟩
        have htr : (c.abs.restrict (c.abs.events \ T)).trace y.tid = c.abs.trace y.tid :=
          Graph.trace_restrict_of_thread hW
            (fun q hq ht => Finset.mem_sdiff.mpr ⟨hq, hnone q hq ht⟩)
            (fun q hq ht w hw => srcT T hT q hq (hnone q hq ht) w hw)
        obtain ⟨h1, h2, h3⟩ := mem_avail_iff.mp hy
        have hyY : y ∈ P.avail c.abs := by
          refine mem_avail_iff.mpr ⟨h1, ?_, ?_⟩
          · rw [← Graph.trace_length, ← htr, Graph.trace_length]
            exact h2
          · rw [← htr]
            exact h3
        by_cases hye : y = e
        · exact hye ▸ hDe d hdD
        · exact nextLt_trans (hDe d hdD) (H.hnext.2 y hyY hye)
    · -- the graph with `d` is the maximal extension by `d`
      rw [hins]
      have hpol_other : ∀ q, q ≠ d →
          (c.abs.restrict (insert d (c.abs.events \ T))).pol q =
            (c.abs.restrict (c.abs.events \ T)).pol q := by
        intro q hqd
        simp only [Graph.restrict_pol, Finset.mem_inter, Finset.mem_insert, hqd, false_or]
      have hpol_d : (c.abs.restrict (c.abs.events \ T)).pol d = none := by
        have : d ∉ c.abs.events ∩ (c.abs.events \ T) := fun h =>
          (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).2).2 hdT
        simp only [Graph.restrict_pol, this, ↓reduceIte]
      have hpol_d' : (c.abs.restrict (insert d (c.abs.events \ T))).pol d = c.abs.pol d := by
        have : d ∈ c.abs.events ∩ insert d (c.abs.events \ T) :=
          Finset.mem_inter.mpr ⟨hdE, Finset.mem_insert_self _ _⟩
        simp only [Graph.restrict_pol, this, ↓reduceIte]
      have hpol_nc : ¬ d.IsCons → (c.abs.restrict (insert d (c.abs.events \ T))).pol =
          (c.abs.restrict (c.abs.events \ T)).pol := by
        intro hnc
        funext q
        by_cases hqd : q = d
        · rw [hqd, hpol_d, hpol_d']
          by_contra h
          obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h
          exact hnc (hW.pol_some hb).2
        · exact hpol_other q hqd
      rcases d.act.isRead_or_isWrite_or_isLocal with hk | hw | hk
      · obtain ⟨x, hact⟩ : ∃ x, d.act = .read x := ⟨_, TEv.IsRead.exists_act hk⟩
        obtain ⟨e', he', -, -, hcomax⟩ := (hDmax d hdD).2.1 (fun hl => hl.not_isRead hk)
        have he'' : c.abs.rf d = some e' := he' hk
        have hloc : d.loc = x := by simp [TEv.loc, hact, Act.loc]
        rw [hloc] at hcomax
        have hnone : ∀ b ∈ (c.abs.co x).filter (fun b => decide (b ∈ c.abs.events \ T)),
            ¬ c.abs.coRelAt x e' (.th b) := by
          intro b hb hco
          obtain ⟨hb1, hb2⟩ := List.mem_filter.mp hb
          have hb2' : b ∈ c.abs.events \ T := by simpa using hb2
          exact hcomax ⟨.th b, hprev b (Finset.mem_sdiff.mp hb2').1
            (Finset.mem_sdiff.mp hb2').2, hco⟩
        have hmw : (c.abs.restrict (c.abs.events \ T)).maxWrite x = e' := by
          have hcoT : (c.abs.restrict (c.abs.events \ T)).co x =
              (c.abs.co x).filter (fun b => decide (b ∈ c.abs.events \ T)) := rfl
          unfold Graph.maxWrite
          rw [hcoT]
          cases e' with
          | init =>
            have hnil : (c.abs.co x).filter (fun b => decide (b ∈ c.abs.events \ T)) = [] :=
              List.eq_nil_iff_forall_not_mem.mpr
                (fun b hb => hnone b hb (List.mem_filter.mp hb).1)
            rw [hnil]
            rfl
          | th s0 =>
            obtain ⟨w, hw, hwt⟩ := hW.rf_read d hdE x hact
            rw [he''] at hw
            rw [← Option.some.inj hw] at hwt
            have hs0 : s0 ∈ (c.abs.co x).filter (fun b => decide (b ∈ c.abs.events \ T)) :=
              List.mem_filter.mpr ⟨(hW.co_mem x s0).mpr hwt, by
                simpa using Finset.mem_sdiff.mpr ⟨hwt.1, hsrcd s0 he''⟩⟩
            rw [List.getLast?_filter_of_max (hW.co_nodup x) hs0 (fun b hb => hnone b hb)]
        rw [Graph.addMax_read hact, hmw]
        apply Graph.ext
        · rfl
        · exact hev
        · funext q
          rw [Graph.addRead_rf]
          by_cases hqd : q = d
          · rw [hqd, Function.update_self, ← he'']
            refine c.abs.restrict_rf_of_source_kept
              (Finset.mem_inter.mpr ⟨hdE, Finset.mem_insert_self _ _⟩) (fun w hw => ?_)
            cases w with
            | init => trivial
            | th w' =>
              exact Finset.mem_insert_of_mem
                (Finset.mem_sdiff.mpr ⟨(hW.rf_source_mem hw).2, hsrcd w' hw⟩)
          · rw [Function.update_of_ne hqd]
            exact hrf_other q hqd
        · funext y
          change (c.abs.co y).filter (fun b => decide (b ∈ insert d (c.abs.events \ T))) =
            (c.abs.co y).filter (fun b => decide (b ∈ c.abs.events \ T))
          apply List.filter_congr
          intro b hb
          have hbd : b ≠ d := by
            rintro rfl
            obtain ⟨-, v, hv⟩ := (hW.co_mem y b).mp hb
            rw [hact] at hv
            cases hv
          simp [hbd]
        · exact hpol_nc (fun h => h.isLocal.not_isRead hk)
      · obtain ⟨e', -, he', -, hcomax⟩ := (hDmax d hdD).2.1 (fun hl => hl.not_isWrite hw)
        have he' := he' hw.not_isRead
        rw [he'] at hcomax
        rw [Graph.addMax_write hw]
        apply Graph.ext
        · rfl
        · exact hev
        · funext q
          rw [Graph.addWrite_rf]
          by_cases hqd : q = d
          · rw [hqd, c.abs.restrict_rf_of_not_mem
              (fun h => (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).2).2 hdT),
              ← hW.rf_none d (Or.inr hw.not_isRead)]
            refine c.abs.restrict_rf_of_source_kept
              (Finset.mem_inter.mpr ⟨hdE, Finset.mem_insert_self _ _⟩) (fun w hw' => ?_)
            rw [hW.rf_none d (Or.inr hw.not_isRead)] at hw'
            cases hw'
          · exact hrf_other q hqd
        · funext y
          rw [Graph.addWrite_maxWrite_co_eq hWT d y]
          have hdco : d ∈ c.abs.co d.loc := by
            obtain ⟨v', hv'⟩ := TEv.IsWrite.exists_act hw
            exact (hW.co_mem _ _).mpr ⟨hdE, v', hv'⟩
          by_cases hy : y = d.loc
          · rw [hy]
            simp only [↓reduceIte]
            change (c.abs.co d.loc).filter (fun b => decide (b ∈ insert d (c.abs.events \ T))) =
              (c.abs.co d.loc).filter (fun b => decide (b ∈ c.abs.events \ T)) ++ [d]
            refine List.filter_eq_filter_append_singleton (hW.co_nodup _) hdco
              (fun b hb hpb => ?_) (fun b hb => ?_)
            · have hb' : b ∈ c.abs.events \ T := by simpa using hpb
              have hbd : b ≠ d := fun h => (Finset.mem_sdiff.mp hb').2 (h ▸ hdT)
              refine (List.Before.total hb hdco hbd).resolve_right (fun hbef => ?_)
              exact hcomax ⟨.th b, hprev b (Finset.mem_sdiff.mp hb').1
                (Finset.mem_sdiff.mp hb').2, hbef⟩
            · simp only [decide_eq_true_eq, Finset.mem_insert]
              tauto
          · simp only [hy, ↓reduceIte]
            change (c.abs.co y).filter (fun b => decide (b ∈ insert d (c.abs.events \ T))) =
              (c.abs.co y).filter (fun b => decide (b ∈ c.abs.events \ T))
            apply List.filter_congr
            intro b hb
            have hbd : b ≠ d := by
              rintro rfl
              obtain ⟨-, v1, hv1⟩ := (hW.co_mem y b).mp hb
              obtain ⟨v2, hv2⟩ := TEv.IsWrite.exists_act hw
              rw [hv1] at hv2
              exact hy (by cases hv2; rfl)
            simp [hbd]
        · exact hpol_nc (fun h => h.isLocal.not_isWrite hw)
      · -- a local event is added with the outcome it has in `c`
        have hctx : c.ctx r e = (c.abs.restrict (c.abs.events \ D)).F := by
          unfold Config.ctx
          refine c.abs.F_restrict_congr (fun q hq hc => ?_)
          have hqr : q ≠ r := by
            rintro rfl
            exact hc.isLocal.not_isRead (by simp [H.hract, Act.IsRead])
          rw [Config.mem_keep_iff, Finset.mem_sdiff, mem_D]
          constructor
          · rintro ⟨-, h⟩
            exact ⟨hq, fun h' => h'.elim h hqr⟩
          · rintro ⟨-, h⟩
            exact ⟨mo.mpr hq, fun h' => h (Or.inl h')⟩
        have hprevF : c.prevF d e = (c.abs.restrict (c.abs.events \ T)).F := by
          unfold Config.prevF
          refine c.abs.F_restrict_congr (fun q hq hc => ?_)
          rw [Finset.mem_filter, List.mem_toFinset, Finset.mem_sdiff]
          constructor
          · rintro ⟨-, hqd, -, hle | hpf⟩
            · refine ⟨hq, fun hqT => ?_⟩
              rcases hle with h | h
              · exact hqd h
              · exact hmin q hqT h
            · exact ⟨hq, fun hqT => hDnp q (hT.1 hqT) hpf⟩
          · rintro ⟨-, hqT⟩
            exact ⟨mo.mpr hq, fun h => hqT (h ▸ hdT), hprev q hq hqT⟩
        have hpd : (c.abs.restrict (c.abs.events \ T)).addMax
            (τ.pref (c.abs.restrict (c.abs.events \ D)).F) d =
            (c.abs.restrict (c.abs.events \ T)).addLoc d (c.abs.pol d) := by
          by_cases hcs : d.IsCons
          · obtain ⟨φ, hφ⟩ := hcs.exists_act
            have hmc := (hDmax d hdD).2.2 φ hφ
            rw [hctx, hprevF] at hmc
            rw [Graph.addMax_cons hφ, show c.abs.pol d = c.pol d from rfl, hmc]
          · obtain ⟨o, ho, heq⟩ := Graph.addMax_local
              (G := c.abs.restrict (c.abs.events \ T))
              (p := (τ.pref (c.abs.restrict (c.abs.events \ D)).F)) hk
            have ho' : o = none := by
              cases o with
              | none => rfl
              | some b => exact absurd (ho.mp rfl) hcs
            have hpn : c.abs.pol d = none := by
              by_contra h
              obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h
              exact hcs (hW.pol_some hb).2
            rw [heq, ho', hpn]
        rw [hpd]
        apply Graph.ext
        · rfl
        · exact hev
        · funext q
          rw [Graph.addLoc_rf]
          by_cases hqd : q = d
          · rw [hqd, c.abs.restrict_rf_of_not_mem
              (fun h => (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).2).2 hdT),
              ← hW.rf_none d (Or.inr hk.not_isRead)]
            refine c.abs.restrict_rf_of_source_kept
              (Finset.mem_inter.mpr ⟨hdE, Finset.mem_insert_self _ _⟩) (fun w hw' => ?_)
            rw [hW.rf_none d (Or.inr hk.not_isRead)] at hw'
            cases hw'
          · exact hrf_other q hqd
        · funext y
          change (c.abs.co y).filter (fun b => decide (b ∈ insert d (c.abs.events \ T))) =
            (c.abs.co y).filter (fun b => decide (b ∈ c.abs.events \ T))
          apply List.filter_congr
          intro b hb
          have hbd : b ≠ d := by
            rintro rfl
            obtain ⟨-, v, hv⟩ := (hW.co_mem y b).mp hb
            exact hk.not_isWrite (by simp [hv, Act.IsWrite])
          simp [hbd]
        · funext q
          rw [Graph.addLoc_pol]
          by_cases hqd : q = d
          · rw [hqd, Function.update_self, hpol_d']
          · rw [Function.update_of_ne hqd]
            exact hpol_other q hqd
  -- the whole loop
  have chainT : ∀ (n : ℕ) (T : Finset TEv), T.card = n → UC T →
      Relation.ReflTransGen (ComplStep P (τ.pref (c.abs.restrict (c.abs.events \ D)).F) e)
        (c.abs.restrict (c.abs.events \ T)) c.abs := by
    intro n
    induction n with
    | zero =>
      intro T hcard _
      rw [Finset.card_eq_zero.mp hcard, Finset.sdiff_empty, hW.restrict_self]
    | succ n ih =>
      intro T hcard hT
      have hne : T.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨d, hdT, hdmax⟩ := T.exists_max_image (fun p => c.order.idxOf p) hne
      have hmin : ∀ d' ∈ T, ¬ c.lt d' d := fun d' hd' h =>
        Nat.not_lt.mpr (hdmax d' hd') h.2.2
      obtain ⟨hstep, hUC'⟩ := stepT T hT d hdT hmin
      exact Relation.ReflTransGen.head hstep
        (ih (T.erase d) (by rw [Finset.card_erase_of_mem hdT, hcard]; rfl) hUC')
  have hUCD : UC D := ⟨subset_rfl, fun _ _ d' hd' _ => hd'⟩
  -- the graph without `r` and `e`
  have hX0 : (c.revisit r e wp).abs.remove {r, e} = c.abs.restrict (c.abs.events \ D) := by
    have hkD : ∀ p, p ∈ c.abs.events → (p ∈ c.keep r e ∧ p ≠ r ↔ p ∉ D) := by
      intro p hp
      rw [Config.mem_keep_iff, mem_D]
      constructor
      · rintro ⟨⟨-, h1⟩, h2⟩
        exact fun h => h.elim h1 h2
      · intro h
        exact ⟨⟨mo.mpr hp, fun h' => h (Or.inl h')⟩, fun h' => h (Or.inr h')⟩
    have hmemX : ∀ p, p ∈ (c.revisit r e wp).abs.events \ {r, e} ↔
        p ∈ c.abs.events ∧ p ∉ D := by
      intro p
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or, H.events']
      constructor
      · rintro ⟨h | h, h1, h2⟩
        · exact absurd h h2
        · have hp := H.keep_mem_events h
          exact ⟨hp, (hkD p hp).mp ⟨h, h1⟩⟩
      · rintro ⟨hp, hpD⟩
        obtain ⟨h1, h2⟩ := (hkD p hp).mpr hpD
        exact ⟨Or.inr h1, h2, fun h => heE (h ▸ hp)⟩
    have hevX : ((c.revisit r e wp).abs.remove {r, e}).events =
        (c.abs.restrict (c.abs.events \ D)).events := by
      ext p
      change p ∈ (c.revisit r e wp).abs.events ∩ ((c.revisit r e wp).abs.events \ {r, e}) ↔
        p ∈ c.abs.events ∩ (c.abs.events \ D)
      rw [Finset.mem_inter, hmemX, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro ⟨-, h⟩
        exact ⟨h.1, h⟩
      · rintro ⟨-, h⟩
        exact ⟨(H.events').mpr (Or.inr ((hkD p h.1).mpr h.2).1), h⟩
    apply Graph.ext
    · rfl
    · exact hevX
    · funext q
      by_cases hq : q ∈ c.abs.events ∧ q ∉ D
      · obtain ⟨hqE, hqD⟩ := hq
        obtain ⟨hqK, hqr⟩ := (hkD q hqE).mpr hqD
        have hX'rf : (c.revisit r e wp).abs.rf q = c.abs.rf q := H.rf_kept hqK hqr
        have hsrc := srcT D hUCD q hqE hqD
        rw [c.abs.restrict_rf_of_source_kept
          (Finset.mem_inter.mpr ⟨hqE, Finset.mem_sdiff.mpr ⟨hqE, hqD⟩⟩) hsrc, ← hX'rf]
        refine (c.revisit r e wp).abs.restrict_rf_of_source_kept
          (Finset.mem_inter.mpr ⟨(H.events').mpr (Or.inr hqK), (hmemX q).mpr ⟨hqE, hqD⟩⟩)
          (fun w hw => ?_)
        rw [hX'rf] at hw
        cases w with
        | init => trivial
        | th w' =>
          have := hsrc _ hw
          exact (hmemX w').mpr (Finset.mem_sdiff.mp this)
      · have h1 : q ∉ c.abs.events ∩ (c.abs.events \ D) := fun h =>
          hq ⟨(Finset.mem_inter.mp h).1, (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).2).2⟩
        rw [c.abs.restrict_rf_of_not_mem h1]
        refine (c.revisit r e wp).abs.restrict_rf_of_not_mem (fun h => ?_)
        exact hq ((hmemX q).mp (Finset.mem_inter.mp h).2)
    · funext y
      have hXco : (c.revisit r e wp).abs.co y =
          ((c.abs.restrict (c.keep r e)).addWrite e wp).co y := by
        rw [Config.revisit_abs]
        rfl
      change ((c.revisit r e wp).abs.co y).filter
          (fun b => decide (b ∈ (c.revisit r e wp).abs.events \ {r, e})) =
        (c.abs.co y).filter (fun b => decide (b ∈ c.abs.events \ D))
      rw [hXco]
      have hpe : (fun b => decide (b ∈ (c.revisit r e wp).abs.events \ {r, e})) e = false := by
        simp
      have hbase : ((c.abs.restrict (c.keep r e)).co y).filter
          (fun b => decide (b ∈ (c.revisit r e wp).abs.events \ {r, e})) =
          (c.abs.co y).filter (fun b => decide (b ∈ c.abs.events \ D)) := by
        change ((c.abs.co y).filter (fun b => decide (b ∈ c.keep r e))).filter
          (fun b => decide (b ∈ (c.revisit r e wp).abs.events \ {r, e})) = _
        rw [List.filter_filter]
        apply List.filter_congr
        intro b hb
        have hbE := ((hW.co_mem y b).mp hb).1
        have h1 : b ∈ (c.revisit r e wp).abs.events \ {r, e} ↔ b ∈ c.abs.events ∧ b ∉ D :=
          hmemX b
        have h2 : b ∉ D → b ∈ c.keep r e := fun h => ((hkD b hbE).mpr h).1
        have h3 : b ∈ c.abs.events \ D ↔ b ∉ D := by
          rw [Finset.mem_sdiff]
          exact ⟨fun h => h.2, fun h => ⟨hbE, h⟩⟩
        by_cases hbD : b ∈ D
        · simp [h1, h3, hbD]
        · simp [h1, h3, hbD, h2 hbD, hbE]
      by_cases hy : y = e.loc
      · rw [hy, Graph.addWrite_co_self]
        rw [hy] at hbase
        cases wp with
        | init =>
          rw [List.filter_cons_of_neg (by simp)]
          exact hbase
        | th p0 =>
          refine Eq.trans ?_ hbase
          exact List.filter_insertAfter_of_neg
            (l := (c.abs.restrict (c.keep r e)).co e.loc) (a := p0) (x := e) hpe
      · rw [Graph.addWrite_co_of_ne _ _ _ hy]
        exact hbase
    · funext q
      change ((c.revisit r e wp).abs.restrict ((c.revisit r e wp).abs.events \ {r, e})).pol q =
        (c.abs.restrict (c.abs.events \ D)).pol q
      rw [Graph.restrict_pol, Graph.restrict_pol]
      by_cases hq : q ∈ c.abs.events ∧ q ∉ D
      · have h1 : q ∈ (c.revisit r e wp).abs.events ∩
            ((c.revisit r e wp).abs.events \ {r, e}) :=
          Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp ((hmemX q).mpr hq)).1, (hmemX q).mpr hq⟩
        have h2 : q ∈ c.abs.events ∩ (c.abs.events \ D) :=
          Finset.mem_inter.mpr ⟨hq.1, Finset.mem_sdiff.mpr hq⟩
        simp only [h1, h2, ↓reduceIte]
        exact Config.revisit_pol c r e wp ((hkD q hq.1).mpr hq.2).1 (mo.mpr hq.1)
      · have h1 : q ∉ (c.revisit r e wp).abs.events ∩
            ((c.revisit r e wp).abs.events \ {r, e}) :=
          fun h => hq ((hmemX q).mp (Finset.mem_inter.mp h).2)
        have h2 : q ∉ c.abs.events ∩ (c.abs.events \ D) := fun h =>
          hq ⟨(Finset.mem_inter.mp h).1, (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).2).2⟩
        simp only [h1, h2, ↓reduceIte]
  refine PrevStep.rv (hc.a22 hs).p4 hrR H.rf_r hre (fun b => ⟨fun h => H.w_out h, fun h => ?_⟩)
    ⟨hX0 ▸ chainT D.card D rfl hUCD, H.hnext⟩
  rw [h]
  exact Relation.TransGen.single
    (Or.inr ⟨r, rfl, (H.events').mpr (Or.inr H.r_keep), H.rf_r⟩)

/-! ### Proposition A.31 and Theorem A.32 -/

/-- Proposition A.31: `Prev` undoes a step of Algorithm 1 from a reached
configuration. -/
theorem Reach.prevStep_of_step {c c' : Config} {e : TEv} {k : Kind} (hc : Reach P (M.sym S) τ c)
    (hs : StepL P (M.sym S) τ c e k c') : PrevStep P τ c'.abs e k c.abs := by
  cases k with
  | nr => exact hc.prevStep_of_step_nr hs
  | rv r => exact hc.prevStep_of_step_rv hs

/-- Two steps from the same configuration with the same event and kind that
give the same graph give the same configuration. -/
theorem StepL.eq_of_abs_eq {c c1 c2 : Config} {e : TEv} {k : Kind}
    (h1 : StepL P (M.sym S) τ c e k c1) (h2 : StepL P (M.sym S) τ c e k c2)
    (h : c1.abs = c2.abs) : c1 = c2 := by
  cases k with
  | nr =>
    obtain ⟨-, -, hc1⟩ := h1.nr_inv
    obtain ⟨-, -, hc2⟩ := h2.nr_inv
    rcases hc1 with ⟨x, w, -, -, rfl⟩ | ⟨wp, -, -, rfl⟩ | ⟨b, -, rfl⟩ | ⟨-, -, rfl⟩ <;>
      rcases hc2 with ⟨x', w', -, -, rfl⟩ | ⟨wp', -, -, rfl⟩ | ⟨b', -, rfl⟩ | ⟨-, -, rfl⟩ <;>
      exact Config.eq_of_abs_order h rfl
  | rv r =>
    obtain ⟨wp1, rfl, -⟩ := h1.rv_inv
    obtain ⟨wp2, rfl, -⟩ := h2.rv_inv
    exact Config.eq_of_abs_order h rfl

/-- The graph before a step, its event and its kind are determined by the
graph after the step. -/
theorem Reach.pred_unique {c1 c2 c1' c2' : Config} {e1 e2 : TEv} {k1 k2 : Kind}
    (h1 : Reach P (M.sym S) τ c1) (h2 : Reach P (M.sym S) τ c2)
    (s1 : StepL P (M.sym S) τ c1 e1 k1 c1')
    (s2 : StepL P (M.sym S) τ c2 e2 k2 c2') (h : c1'.abs = c2'.abs) :
    c1.abs = c2.abs ∧ e1 = e2 ∧ k1 = k2 := by
  have p1 := h1.prevStep_of_step s1
  have p2 := h2.prevStep_of_step s2
  rw [h] at p1
  obtain ⟨he, hk, hG⟩ := p1.det p2
  exact ⟨hG, he, hk⟩

/-- The induction for Theorem A.32, on the length of the first run. -/
theorem path_unique_aux : ∀ (n : ℕ) (p1 p2 : List Config) (c1 c2 : Config), p1.length = n →
    Maz.Path (Step P (M.sym S) τ) (Config.init P.mem) p1 c1 →
    Maz.Path (Step P (M.sym S) τ) (Config.init P.mem) p2 c2 → c1.abs = c2.abs →
    p1 = p2 ∧ c1 = c2 := by
  -- a run that ends in the graph without events has no step
  have noev : ∀ (p : List Config) (c : Config),
      Maz.Path (Step P (M.sym S) τ) (Config.init P.mem) p c →
      p ≠ [] → c.abs.events ≠ ∅ := by
    intro p c hp hne
    obtain ⟨q, b, -, -, ⟨e, k, hs⟩⟩ := hp.exists_snoc hne
    exact Finset.ne_empty_of_mem (List.mem_toFinset.mpr hs.mem_order)
  have init_ev : (Config.init P.mem).abs.events = ∅ := by simp [Config.abs, Config.init]
  intro n
  induction n with
  | zero =>
    intro p1 p2 c1 c2 hl h1 h2 h
    have hp1 : p1 = [] := List.length_eq_zero_iff.mp hl
    subst hp1
    have hc1 : Config.init P.mem = c1 := Maz.Path.nil_iff.mp h1
    by_cases hp2 : p2 = []
    · subst hp2
      exact ⟨rfl, hc1.symm.trans (Maz.Path.nil_iff.mp h2)⟩
    · exact absurd (by rw [← h, ← hc1]; exact init_ev) (noev p2 c2 h2 hp2)
  | succ n ih =>
    intro p1 p2 c1 c2 hl h1 h2 h
    have hp1 : p1 ≠ [] := by
      intro h0
      rw [h0] at hl
      cases hl
    by_cases hp2 : p2 = []
    · subst hp2
      have hc2 : Config.init P.mem = c2 := Maz.Path.nil_iff.mp h2
      exact absurd (by rw [h, ← hc2]; exact init_ev) (noev p1 c1 h1 hp1)
    · obtain ⟨q1, b1, rfl, hq1, ⟨e1, k1, s1⟩⟩ := h1.exists_snoc hp1
      obtain ⟨q2, b2, rfl, hq2, ⟨e2, k2, s2⟩⟩ := h2.exists_snoc hp2
      obtain ⟨hb, he, hk⟩ := Reach.pred_unique hq1.reflTransGen hq2.reflTransGen s1 s2 h
      have hlen : q1.length = n := by simpa using hl
      obtain ⟨hq, hbb⟩ := ih q1 q2 b1 b2 hlen hq1 hq2 hb
      subst hq hbb he hk
      have hcc := s1.eq_of_abs_eq s2 h
      subst hcc
      exact ⟨rfl, rfl⟩

/-- On a reached configuration, the label of a step is determined by the
configuration it leads to. -/
theorem StepL.label_unique {c c' : Config} {e1 e2 : TEv} {k1 k2 : Kind} (hc : Reach P (M.sym S) τ c)
    (h1 : StepL P (M.sym S) τ c e1 k1 c') (h2 : StepL P (M.sym S) τ c e2 k2 c') :
    e1 = e2 ∧ k1 = k2 :=
  (Reach.pred_unique hc hc h1 h2 rfl).2

/-- Theorem A.32 (optimality): two runs of Algorithm 1 from the initial
configuration that end in the same graph are the same run. -/
theorem path_unique {p1 p2 : List Config} {c1 c2 : Config}
    (h1 : Maz.Path (Step P (M.sym S) τ) (Config.init P.mem) p1 c1)
    (h2 : Maz.Path (Step P (M.sym S) τ) (Config.init P.mem) p2 c2) (h : c1.abs = c2.abs) :
    p1 = p2 :=
  (path_unique_aux p1.length p1 p2 c1 c2 rfl h1 h2 h).1

/-- A reached configuration is determined by its graph. -/
theorem Reach.eq_of_abs_eq {c1 c2 : Config} (h1 : Reach P (M.sym S) τ c1)
    (h2 : Reach P (M.sym S) τ c2)
    (h : c1.abs = c2.abs) : c1 = c2 := by
  obtain ⟨p1, hp1⟩ := Maz.Path.of_reflTransGen h1
  obtain ⟨p2, hp2⟩ := Maz.Path.of_reflTransGen h2
  exact (path_unique_aux p1.length p1 p2 c1 c2 rfl hp1 hp2 h).2

end Condpor
