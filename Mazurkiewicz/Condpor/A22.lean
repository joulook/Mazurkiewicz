import Mazurkiewicz.Condpor.Invariants

/-!
# Proof of Proposition A.22

The paper proves Proposition A.22 by induction over the construction of the
configuration, by cases on the kind of the last step and of the step before it
(pp. 49:35-42). This file follows that proof, with one reorganization: the
case analyses of the paper for (P1) of a revisit (its steps ⟨5⟩4 and
⟨6⟩1-⟨6⟩3), for (P9), and for (P2) at the new event are replaced by one lemma,
`LastStep.witness`, together with Lemma A.20 (D3). The clauses proved are the
paper's.

* `NrFacts`, `RvHyp`: how the insertion order, the sources, causality and the
  available events change under a plain addition and under a revisit. These
  are the facts the paper uses without proof ("`G'.rf ∩ >' = G.rf ∩ >`",
  "`(G + e').porf; [e'] = G'.porf; [e']`", "every `porf` edge between events of
  `G'.E \\ {a', e'}` is preserved", "an event of `avail(G')` is in `avail(G)` or
  immediately `po`-after `e'`").
* `LastStep`, `Inv`: the induction hypothesis. `Inv c` holds the clauses (P1),
  (P2), (P6) for `c` and, if `c` is not the initial configuration, the facts
  about the step that led to `c` which the paper's induction uses.
* `Reach.a22`: the proposition.
-/

namespace Condpor

open Program

variable {P : Program} {M : Model}

private theorem ifPos {p : Prop} [Decidable p] {α : Type*} {a b : α} (h : p) :
    (if p then a else b) = a := by simp [h]

private theorem ifNeg {p : Prop} [Decidable p] {α : Type*} {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by simp [h]

/-! ### A plain addition -/

/-- What a step that is not a revisit does to a configuration. -/
structure NrFacts (P : Program) (c : Config) (e : TEv) (c' : Config) : Prop where
  /-- the new event is the newest -/
  order : c'.order = e :: c.order
  /-- and it is new -/
  fresh : e ∉ c.order
  /-- the sources of the old reads are unchanged -/
  rf_old : ∀ q, q ≠ e → c'.rf q = c.rf q
  /-- every causality step is an old one or ends in the new event -/
  step_sub : ∀ a b, c'.abs.porfStep a b → c.abs.porfStep a b ∨ b = .th e
  /-- the new event has no causality successor -/
  sink : ∀ b, ¬ c'.abs.porfStep (.th e) b
  /-- the available events of the other threads were available before -/
  avail_other : ∀ a ∈ P.avail c'.abs, a.tid ≠ e.tid → a ∈ P.avail c.abs
  /-- the available event of the thread of the new event is its successor -/
  avail_same : ∀ a ∈ P.avail c'.abs, a.tid = e.tid → a.idx = e.idx + 1

theorem StepL.nrFacts {c c' : Config} {e : TEv} (hc : c.Wf) (h : StepL P M τ c e .nr c') :
    NrFacts P c e c' := by
  obtain ⟨-, hnext, hcase⟩ := h.nr_inv
  have hidx := Program.idx_eq_of_mem_avail hnext.1
  have hfresh : e ∉ c.order := fun hm =>
    hc.1.not_mem_of_idx_eq_cnt hidx (List.mem_toFinset.mpr hm)
  have hloc : ∀ o : Option Bool, e.IsLocal → (o.isSome ↔ e.IsCons) →
      NrFacts P c e (c.addLoc e o) := by
    intro o hl ho
    refine ⟨rfl, hfresh, ?_, ?_, ?_, ?_, ?_⟩
    · intro q _
      rfl
    · intro a b hab
      rw [Config.addLoc_abs] at hab
      exact Graph.porfStep_addLoc hc.1 hidx hab
    · intro b hb
      rw [Config.addLoc_abs] at hb
      exact Graph.not_porfStep_addLoc_self hc.1 hidx b hb
    · intro a ha hne
      rw [Config.addLoc_abs] at ha
      obtain ⟨ht, hi, hs⟩ := Program.mem_avail_iff.mp ha
      rw [Graph.cnt_addLoc hc.1 hidx, ifNeg hne] at hi
      rw [Graph.trace_addLoc hc.1 hidx hl ho, ifNeg hne] at hs
      exact Program.mem_avail_iff.mpr ⟨ht, hi, hs⟩
    · intro a ha heq
      rw [Config.addLoc_abs] at ha
      obtain ⟨-, hi, -⟩ := Program.mem_avail_iff.mp ha
      rw [Graph.cnt_addLoc hc.1 hidx, ifPos heq, heq, ← hidx] at hi
      exact hi
  rcases hcase with ⟨x, w, hact, hw, rfl⟩ | ⟨wp, hwr, hwp, rfl⟩ | ⟨b, hcs, rfl⟩ |
    ⟨hl, hnc, rfl⟩
  rotate_left 2
  · exact hloc _ hcs.isLocal (iff_of_true rfl hcs)
  · exact hloc _ hl (iff_of_false (by simp) hnc)
  · refine ⟨rfl, hfresh, ?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      simp [Config.addRead, Config.abs, Function.update_of_ne hq]
    · intro a b hab
      rw [Config.addRead_abs] at hab
      exact Graph.porfStep_addRead hc.1 hidx hab
    · intro b hb
      rw [Config.addRead_abs] at hb
      exact Graph.not_porfStep_addRead_self hc.1 hidx hw b hb
    · intro a ha hne
      rw [Config.addRead_abs] at ha
      obtain ⟨ht, hi, hs⟩ := Program.mem_avail_iff.mp ha
      rw [Graph.cnt_addRead hc.1 hidx, ifNeg hne] at hi
      rw [Graph.trace_addRead hc.1 hidx hact hw, ifNeg hne] at hs
      exact Program.mem_avail_iff.mpr ⟨ht, hi, hs⟩
    · intro a ha heq
      rw [Config.addRead_abs] at ha
      obtain ⟨-, hi, -⟩ := Program.mem_avail_iff.mp ha
      rw [Graph.cnt_addRead hc.1 hidx, ifPos heq, heq, ← hidx] at hi
      exact hi
  · refine ⟨rfl, hfresh, ?_, ?_, ?_, ?_, ?_⟩
    · intro q _
      rfl
    · intro a b hab
      rw [Config.addWrite_abs] at hab
      exact Graph.porfStep_addWrite hc.1 hidx hab
    · intro b hb
      rw [Config.addWrite_abs] at hb
      exact Graph.not_porfStep_addWrite_self hc.1 hidx b hb
    · intro a ha hne
      rw [Config.addWrite_abs] at ha
      obtain ⟨ht, hi, hs⟩ := Program.mem_avail_iff.mp ha
      rw [Graph.cnt_addWrite hc.1 hidx, ifNeg hne] at hi
      rw [Graph.trace_addWrite hc.1 hidx hwr hwp, ifNeg hne] at hs
      exact Program.mem_avail_iff.mpr ⟨ht, hi, hs⟩
    · intro a ha heq
      rw [Config.addWrite_abs] at ha
      obtain ⟨-, hi, -⟩ := Program.mem_avail_iff.mp ha
      rw [Graph.cnt_addWrite hc.1 hidx, ifPos heq, heq, ← hidx] at hi
      exact hi

namespace NrFacts

variable {c c' : Config} {e : TEv}

/-- The insertion order after a plain addition. -/
theorem lt_iff (N : NrFacts P c e c') {a b : TEv} :
    c'.lt a b ↔ (b = e ∧ a ∈ c.order) ∨ c.lt a b := by
  unfold Config.lt
  rw [N.order]
  exact List.before_cons_iff_of_notMem N.fresh

theorem events_sub (N : NrFacts P c e c') : c.abs.events ⊆ c'.abs.events := by
  intro q hq
  have hq' : q ∈ c.order := List.mem_toFinset.mp hq
  refine List.mem_toFinset.mpr ?_
  rw [N.order]
  exact List.mem_cons_of_mem _ hq'

/-- A plain addition adds no pair to `G.rf ∩ >`. -/
theorem bw_iff (N : NrFacts P c e c') (hc : c.Wf) {s q : TEv} : c'.Bw s q ↔ c.Bw s q := by
  constructor
  · rintro ⟨hrf, hlt⟩
    rcases N.lt_iff.mp hlt with ⟨hse, hq⟩ | hlt'
    · exfalso
      have hqe : q ≠ e := fun h => N.fresh (h ▸ hq)
      rw [N.rf_old q hqe, hse] at hrf
      exact N.fresh (List.mem_toFinset.mp (hc.1.rf_source_mem hrf).2)
    · have hqe : q ≠ e := fun h => N.fresh (h ▸ hlt'.2.1)
      exact ⟨(N.rf_old q hqe) ▸ hrf, hlt'⟩
  · rintro ⟨hrf, hlt⟩
    have hqe : q ≠ e := fun h => N.fresh (h ▸ hlt.2.1)
    exact ⟨(N.rf_old q hqe).trans hrf, N.lt_iff.mpr (Or.inr hlt)⟩

/-- Old causality is kept. -/
theorem porf_mono (N : NrFacts P c e c') {a b : Ev} (h : c.abs.porf a b) : c'.abs.porf a b := by
  refine Graph.porf_mono N.events_sub ?_ h
  intro q hq
  exact N.rf_old q (fun h' => N.fresh (h' ▸ List.mem_toFinset.mp hq))

/-- Causality not ending in the new event is old. -/
theorem porf_old (N : NrFacts P c e c') {a b : Ev} (h : c'.abs.porf a b) (hb : b ≠ .th e) :
    c.abs.porf a b :=
  (Maz.transGen_of_sink N.step_sub N.sink h).resolve_right hb

/-- The new event is causally before nothing. -/
theorem porf_sink (N : NrFacts P c e c') (b : Ev) : ¬ c'.abs.porf (.th e) b := by
  intro h
  obtain ⟨x, hx⟩ := Maz.exists_first_of_transGen h
  exact N.sink x hx

end NrFacts

/-! ### A revisit -/

/-- The trace of a thread other than that of `r` does not depend on the source
of `r`. -/
theorem Graph.trace_setRF_of_ne (G : Graph) {r : TEv} {s : Ev} {t : Tid} (ht : t ≠ r.tid) :
    (G.setRF r s).trace t = G.trace t := by
  unfold Graph.trace Graph.traceBefore
  have hcnt : (G.setRF r s).cnt t = G.cnt t := rfl
  rw [hcnt]
  apply List.map_congr_left
  intro j _
  have hev : (G.setRF r s).evAt t j = G.evAt t j := rfl
  rw [hev]
  cases hq : G.evAt t j with
  | none => rfl
  | some q =>
    obtain ⟨-, hqt, -⟩ := Graph.evAt_eq_some_iff_spec hq
    exact G.ret_setRF_of_ne (fun h => ht (h ▸ hqt.symm))

/-- The premises of a revisit of the read `r` by the new write `w`, in a
well-formed configuration whose insertion order extends the program order. -/
structure RvHyp (P : Program) {S : Solver} (τ : TieBreak S) (c : Config) (r w : TEv) (wp : Ev) :
    Prop where
  hc : c.Wf
  hpo : c.PoLt
  hnext : P.IsNext c.abs w
  hw : w.IsWrite
  hr : r ∈ c.order
  hract : r.act = .read w.loc
  hnp : ¬ (c.plus w).porf (.th r) (.th w)
  hmax : ∀ e, (c.Deleted r w e ∨ e = r) → c.IsMaximallyAdded τ (c.ctx r w) e w
  hwp : (c.abs.restrict (c.keep r w)).IsWriteTo w.loc wp

theorem StepL.rvHyp {c c' : Config} {r w : TEv} (hc : c.Wf) (hpo : c.PoLt)
    (h : StepL P M τ c w (.rv r) c') : ∃ wp, c' = c.revisit r w wp ∧ RvHyp P τ c r w wp := by
  obtain ⟨wp, rfl, -, h1, h2, h3, h4, h5, h6, h7⟩ := h.rv_inv
  exact ⟨wp, rfl, hc, hpo, h1, h2, h3, h4, h5, h6, h7⟩

namespace RvHyp

variable {c : Config} {r w : TEv} {wp : Ev}

theorem hav (H : RvHyp P τ c r w wp) : w ∈ P.avail c.abs := H.hnext.1

theorem hidx (H : RvHyp P τ c r w wp) : w.idx = c.abs.cnt w.tid :=
  Program.idx_eq_of_mem_avail H.hav

theorem fresh (H : RvHyp P τ c r w wp) : w ∉ c.order := fun hm =>
  H.hc.1.not_mem_of_idx_eq_cnt H.hidx (List.mem_toFinset.mpr hm)

theorem hmaxD (H : RvHyp P τ c r w wp) :
    ∀ e, c.Deleted r w e → c.IsMaximallyAdded τ (c.ctx r w) e w :=
  fun e he => H.hmax e (Or.inl he)

theorem wf' (H : RvHyp P τ c r w wp) : (c.revisit r w wp).Wf :=
  Config.revisit_wf H.hc H.hpo H.hidx H.hw H.hr H.hract H.hmaxD H.hwp

theorem keep_sub (_ : RvHyp P τ c r w wp) {y : TEv} (hy : y ∈ c.keep r w) : y ∈ c.order :=
  ((Config.mem_keep_iff c r w y).mp hy).1

theorem r_keep (H : RvHyp P τ c r w wp) : r ∈ c.keep r w := Config.mem_keep_self H.hr

theorem w_ne_r (H : RvHyp P τ c r w wp) : w ≠ r := fun h => H.fresh (h ▸ H.hr)

theorem order' (_ : RvHyp P τ c r w wp) :
    (c.revisit r w wp).order = w :: c.order.filter (fun d => decide (d ∈ c.keep r w)) := rfl

theorem mem_order' (H : RvHyp P τ c r w wp) {y : TEv} :
    y ∈ (c.revisit r w wp).order ↔ y = w ∨ y ∈ c.keep r w := by
  rw [H.order', List.mem_cons, List.mem_filter]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨H.keep_sub h, by simpa using h⟩

/-- The insertion order after a revisit. -/
theorem lt_iff (H : RvHyp P τ c r w wp) {a b : TEv} :
    (c.revisit r w wp).lt a b ↔
      (b = w ∧ a ∈ c.keep r w) ∨ (c.lt a b ∧ a ∈ c.keep r w ∧ b ∈ c.keep r w) := by
  unfold Config.lt
  rw [H.order']
  have hw : w ∉ c.order.filter (fun d => decide (d ∈ c.keep r w)) :=
    fun h => H.fresh (List.mem_filter.mp h).1
  rw [List.before_cons_iff_of_notMem hw, List.before_filter_iff, List.mem_filter]
  simp only [decide_eq_true_eq]
  constructor
  · rintro (⟨h1, _, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h1, h3⟩
    · exact Or.inr ⟨h1, h3, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h1, H.keep_sub h2, h2⟩
    · exact Or.inr ⟨h1, h3, h2⟩

/-- The revisited read reads from the new write. -/
theorem rf_r (_ : RvHyp P τ c r w wp) : (c.revisit r w wp).rf r = some (.th w) := by
  simp [Config.revisit]

/-- The other kept reads keep their source. -/
theorem rf_kept (H : RvHyp P τ c r w wp) {q : TEv} (hq : q ∈ c.keep r w) (hqr : q ≠ r) :
    (c.revisit r w wp).rf q = c.rf q := by
  have hqm : q ∈ c.abs.events ∩ c.keep r w :=
    Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr (H.keep_sub hq), hq⟩
  have h1 : (c.revisit r w wp).rf q = (c.abs.restrict (c.keep r w)).rf q := by
    simp [Config.revisit, Function.update_of_ne hqr]
  rw [h1]
  exact c.abs.restrict_rf_of_source_kept hqm
    (fun s hs => Config.keep_sources H.hc H.hmaxD hqm hs)

/-- The events after a revisit. -/
theorem events' (H : RvHyp P τ c r w wp) {y : TEv} :
    y ∈ (c.revisit r w wp).abs.events ↔ y = w ∨ y ∈ c.keep r w :=
  List.mem_toFinset.trans H.mem_order'

/-- A source after a revisit: the read is `r`, or it is kept with the same
source. -/
theorem rf_some (H : RvHyp P τ c r w wp) {q : TEv} {s : Ev}
    (h : (c.revisit r w wp).rf q = some s) :
    (q = r ∧ s = .th w) ∨ (q ∈ c.keep r w ∧ q ≠ r ∧ c.rf q = some s) := by
  by_cases hqr : q = r
  · left
    rw [hqr, H.rf_r] at h
    exact ⟨hqr, (Option.some.inj h).symm⟩
  · right
    have hqm := (H.wf'.1.rf_source_mem h).1
    rcases H.events'.mp hqm with hqw | hqk
    · exfalso
      have h1 : (c.revisit r w wp).rf q = (c.abs.restrict (c.keep r w)).rf q := by
        simp [Config.revisit, Function.update_of_ne hqr]
      rw [h1, c.abs.restrict_rf_of_not_mem] at h
      · cases h
      · intro hm
        exact H.fresh (hqw ▸ List.mem_toFinset.mp (Finset.mem_inter.mp hm).1)
    · exact ⟨hqk, hqr, (H.rf_kept hqk hqr) ▸ h⟩

/-- `G'.rf ∩ >'` after a revisit: the new pair `⟨w, r⟩`, and the old pairs whose
read is kept and is not `r`. -/
theorem bw_iff (H : RvHyp P τ c r w wp) {s q : TEv} :
    (c.revisit r w wp).Bw s q ↔
      (s = w ∧ q = r) ∨ (c.Bw s q ∧ q ∈ c.keep r w ∧ q ≠ r) := by
  constructor
  · rintro ⟨hrf, hlt⟩
    rcases H.rf_some hrf with ⟨hq, hs⟩ | ⟨hqk, hqr, hrf'⟩
    · exact Or.inl ⟨(Ev.th.inj hs), hq⟩
    · right
      rcases H.lt_iff.mp hlt with ⟨hsw, _⟩ | ⟨hlt', _, _⟩
      · exfalso
        rw [hsw] at hrf'
        exact H.fresh (List.mem_toFinset.mp (H.hc.1.rf_source_mem hrf').2)
      · exact ⟨⟨hrf', hlt'⟩, hqk, hqr⟩
  · rintro (⟨hs, hq⟩ | ⟨⟨hrf, hlt⟩, hqk, hqr⟩)
    · rw [hs, hq]
      exact ⟨H.rf_r, H.lt_iff.mpr (Or.inl ⟨rfl, H.r_keep⟩)⟩
    · have hqm : q ∈ c.abs.events ∩ c.keep r w :=
        Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr (H.keep_sub hqk), hqk⟩
      have hsk : s ∈ c.keep r w := Config.keep_sources H.hc H.hmaxD hqm hrf
      exact ⟨(H.rf_kept hqk hqr).trans hrf, H.lt_iff.mpr (Or.inr ⟨hlt, hqk, hsk⟩)⟩

theorem keep_mem_events (H : RvHyp P τ c r w wp) {y : TEv} (hy : y ∈ c.keep r w) :
    y ∈ c.abs.events := List.mem_toFinset.mpr (H.keep_sub hy)

/-- The new write has no source. -/
theorem rf_w (H : RvHyp P τ c r w wp) (s : Ev) : (c.revisit r w wp).rf w ≠ some s := by
  intro h
  rcases H.rf_some h with ⟨hwr, -⟩ | ⟨hwk, -, -⟩
  · exact H.w_ne_r hwr
  · exact H.fresh (H.keep_sub hwk)

/-- A causality step into a kept event other than `r` is an old step. -/
theorem step_into_kept (H : RvHyp P τ c r w wp) {a : Ev} {y : TEv} (hy : y ∈ c.keep r w)
    (hyr : y ≠ r) (h : (c.revisit r w wp).abs.porfStep a (.th y)) :
    c.abs.porfStep a (.th y) := by
  rcases h with h | ⟨q, hq, -, hrf⟩
  · left
    cases a with
    | init => exact H.keep_mem_events hy
    | th x =>
      obtain ⟨hx, -, ht, hi⟩ := h
      rcases H.events'.mp hx with hxw | hxk
      · exfalso
        have hlt := H.hc.1.idx_lt_cnt (H.keep_mem_events hy)
        rw [hxw] at ht hi
        rw [← ht, ← H.hidx] at hlt
        omega
      · exact ⟨H.keep_mem_events hxk, H.keep_mem_events hy, ht, hi⟩
  · have hqy : q = y := (Ev.th.inj hq).symm
    rw [hqy] at hrf
    exact Or.inr ⟨y, rfl, H.keep_mem_events hy, (H.rf_kept hy hyr).symm.trans hrf⟩

/-- An old causality step between kept events, into an event other than `r`,
is a step after the revisit. -/
theorem step_of_kept (H : RvHyp P τ c r w wp) {a : Ev} {y : TEv} (hy : y ∈ c.keep r w)
    (hyr : y ≠ r) (ha : ∀ x, a = .th x → x ∈ c.keep r w) (h : c.abs.porfStep a (.th y)) :
    (c.revisit r w wp).abs.porfStep a (.th y) := by
  rcases h with h | ⟨q, hq, -, hrf⟩
  · left
    cases a with
    | init => exact H.events'.mpr (Or.inr hy)
    | th x => exact ⟨H.events'.mpr (Or.inr (ha x rfl)), H.events'.mpr (Or.inr hy), h.2.2⟩
  · have hqy : q = y := (Ev.th.inj hq).symm
    rw [hqy] at hrf
    exact Or.inr ⟨y, rfl, H.events'.mpr (Or.inr hy), (H.rf_kept hy hyr).trans hrf⟩

/-- The causality steps into the new write are those of `G + w`. -/
theorem step_into_w_iff (H : RvHyp P τ c r w wp) {a : Ev} :
    (c.revisit r w wp).abs.porfStep a (.th w) ↔ (c.plus w).porfStep a (.th w) := by
  constructor
  · rintro (h | ⟨q, hq, -, hrf⟩)
    · left
      cases a with
      | init => exact Finset.mem_insert_self _ _
      | th x =>
        obtain ⟨hx, -, ht, hi⟩ := h
        rcases H.events'.mp hx with hxw | hxk
        · rw [hxw] at hi
          exact absurd hi (Nat.lt_irrefl _)
        · exact ⟨Finset.mem_insert_of_mem (H.keep_mem_events hxk), Finset.mem_insert_self _ _,
            ht, hi⟩
    · have hqw : q = w := (Ev.th.inj hq).symm
      rw [hqw] at hrf
      exact absurd hrf (H.rf_w a)
  · rintro (h | ⟨q, hq, -, hrf⟩)
    · left
      cases a with
      | init => exact H.events'.mpr (Or.inl rfl)
      | th x =>
        obtain ⟨hx, -, ht, hi⟩ := h
        rcases Finset.mem_insert.mp hx with hxw | hxm
        · rw [hxw] at hi
          exact absurd hi (Nat.lt_irrefl _)
        · exact ⟨H.events'.mpr (Or.inr
            (Config.keep_thread H.hc H.hidx (List.mem_toFinset.mp hxm) ht)),
            H.events'.mpr (Or.inl rfl), ht, hi⟩
    · have hqw : q = w := (Ev.th.inj hq).symm
      rw [hqw] at hrf
      have hrf' : c.abs.rf w = some a := hrf
      exact absurd (List.mem_toFinset.mp (H.hc.1.rf_source_mem hrf').1) H.fresh

/-- After the revisit, the revisited read is causally before nothing. -/
theorem r_max (H : RvHyp P τ c r w wp) (b : Ev) : ¬ (c.revisit r w wp).abs.porf (.th r) b := by
  intro h
  obtain ⟨b1, hb1⟩ := Maz.exists_first_of_transGen h
  rcases hb1 with hpo | ⟨q, hq, -, hrf⟩
  · cases b1 with
    | init => exact hpo
    | th y =>
      obtain ⟨-, hy, ht, hi⟩ := hpo
      rcases H.events'.mp hy with hyw | hyk
      · rw [hyw] at ht hi
        have hst : (c.plus w).porfStep (.th r) (.th w) :=
          Or.inl ⟨Finset.mem_insert_of_mem (List.mem_toFinset.mpr H.hr),
            Finset.mem_insert_self _ _, ht, hi⟩
        exact H.hnp (Relation.TransGen.single hst)
      · have := Config.keep_last H.hpo H.hr H.hnp hyk ht.symm
        omega
  · rcases H.rf_some hrf with ⟨-, hs⟩ | ⟨-, -, hrf'⟩
    · exact H.w_ne_r (Ev.th.inj hs).symm
    · -- `r` would be the source of a read of `c`, hence a write
      have hrf'' : c.abs.rf q = some (.th r) := hrf'
      have hqm := (H.hc.1.rf_source_mem hrf'').1
      have hqr : q.IsRead := by
        by_contra hn
        rw [H.hc.1.rf_none q (Or.inr hn)] at hrf''
        cases hrf''
      obtain ⟨w', hw', hw''⟩ := H.hc.1.rf_read q hqm _ (TEv.IsRead.exists_act hqr)
      have heq : some (Ev.th r) = some w' := hrf''.symm.trans hw'
      cases heq
      obtain ⟨-, v, hv⟩ := hw''
      rw [H.hract] at hv
      cases hv

/-- After the revisit, the new write is causally before the revisited read
only. -/
theorem w_out (H : RvHyp P τ c r w wp) {b : Ev} (h : (c.revisit r w wp).abs.porf (.th w) b) :
    b = .th r := by
  have first : ∀ b1, (c.revisit r w wp).abs.porfStep (.th w) b1 → b1 = .th r := by
    intro b1 hb1
    rcases hb1 with hpo | ⟨q, hq, -, hrf⟩
    · cases b1 with
      | init => exact absurd hpo id
      | th y =>
        exfalso
        obtain ⟨-, hy, ht, hi⟩ := hpo
        rcases H.events'.mp hy with hyw | hyk
        · rw [hyw] at hi
          exact Nat.lt_irrefl _ hi
        · have hlt := H.hc.1.idx_lt_cnt (H.keep_mem_events hyk)
          rw [← ht, ← H.hidx] at hlt
          omega
    · rcases H.rf_some hrf with ⟨hq', -⟩ | ⟨-, -, hrf'⟩
      · rw [hq, hq']
      · have hrf'' : c.abs.rf q = some (.th w) := hrf'
        exact absurd (List.mem_toFinset.mp (H.hc.1.rf_source_mem hrf'').2) H.fresh
  obtain ⟨b1, hb1, hrest⟩ := Relation.TransGen.head'_iff.mp h
  have hb1r := first b1 hb1
  rw [hb1r] at hrest
  rcases Relation.ReflTransGen.cases_head hrest with h0 | ⟨b2, hb2, -⟩
  · exact h0.symm
  · exact absurd (Relation.TransGen.single hb2) (H.r_max b2)

/-- Causality into an event that is not deleted and is not `r` is kept by the
revisit (the paper: "every `porf` edge between events of `G'.E \\ {a', e'}` is
preserved", with Lemma A.20 (D2)). -/
theorem porf_kept (H : RvHyp P τ c r w wp) {x y : TEv} (hy : y ∈ c.order)
    (hny : ¬ c.Deleted r w y) (hyr : y ≠ r) (h : c.abs.porf (.th x) (.th y)) :
    (c.revisit r w wp).abs.porf (.th x) (.th y) := by
  have hyk : y ∈ c.keep r w := (Config.mem_keep_iff c r w y).mpr ⟨hy, hny⟩
  have key : ∀ a, Relation.TransGen c.abs.porfStep a (.th y) →
      Relation.TransGen (c.revisit r w wp).abs.porfStep a (.th y) := by
    intro a ha
    induction ha using Relation.TransGen.head_induction_on with
    | single h1 =>
      refine Relation.TransGen.single (H.step_of_kept hyk hyr ?_ h1)
      intro x' hx'
      rw [hx'] at h1
      have hnd := A20_step H.hc H.hpo H.hr H.hnp H.hmax h1 hy hny
      exact (Config.mem_keep_iff c r w x').mpr
        ⟨List.mem_toFinset.mp (H.hc.1.mem_of_porfStep h1).1, fun hd => hnd (Or.inl hd)⟩
    | @head a b h1 hrest ih =>
      cases b with
      | init => exact absurd h1 (c.abs.not_porfStep_init _)
      | th z =>
        have hz : z ∈ c.order := List.mem_toFinset.mp (H.hc.1.mem_of_porfStep h1).2
        have hzn : ¬ (c.Deleted r w z ∨ z = r) := fun hz' =>
          A20_D2 H.hc H.hpo H.hr H.hnp H.hmax hz' hy hny hrest
        have hzk : z ∈ c.keep r w :=
          (Config.mem_keep_iff c r w z).mpr ⟨hz, fun hd => hzn (Or.inl hd)⟩
        refine Relation.TransGen.head (H.step_of_kept hzk (fun h' => hzn (Or.inr h')) ?_ h1) ih
        intro x' hx'
        rw [hx'] at h1
        have hnd := A20_step H.hc H.hpo H.hr H.hnp H.hmax h1 hz (fun hd => hzn (Or.inl hd))
        exact (Config.mem_keep_iff c r w x').mpr
          ⟨List.mem_toFinset.mp (H.hc.1.mem_of_porfStep h1).1, fun hd => hnd (Or.inl hd)⟩
  exact key _ h

/-- `(G + w).porf; [w] = G'.porf; [w]` (the paper, proof of (P2)). -/
theorem porf_w_iff (H : RvHyp P τ c r w wp) {a : Ev} :
    (c.plus w).porf a (.th w) ↔ (c.revisit r w wp).abs.porf a (.th w) := by
  have hplus_sub : ∀ a b, (c.plus w).porfStep a b → c.abs.porfStep a b ∨ b = .th w :=
    fun a b h => Graph.porfStep_addWrite H.hc.1 H.hidx h
  have hplus_mono : ∀ a b, c.abs.porfStep a b → (c.plus w).porfStep a b :=
    fun a b h => Graph.porfStep_mono (G := c.abs) (G' := c.plus w)
      (Finset.subset_insert _ _) (fun _ _ => rfl) h
  constructor
  · intro h
    have key : ∀ a, Relation.TransGen (c.plus w).porfStep a (.th w) →
        Relation.TransGen (c.revisit r w wp).abs.porfStep a (.th w) := by
      intro a ha
      induction ha using Relation.TransGen.head_induction_on with
      | single h1 => exact Relation.TransGen.single (H.step_into_w_iff.mpr h1)
      | @head a b h1 hrest ih =>
        cases b with
        | init => exact absurd h1 ((c.plus w).not_porfStep_init _)
        | th z =>
          have hzw : z ≠ w := by
            intro hzw
            rw [hzw] at hrest
            obtain ⟨b1, hb1⟩ := Maz.exists_first_of_transGen hrest
            exact Graph.not_porfStep_addWrite_self H.hc.1 H.hidx b1 hb1
          have h1c : c.abs.porfStep a (.th z) :=
            (hplus_sub _ _ h1).resolve_right (fun h' => hzw (Ev.th.inj h'))
          have hz : z ∈ c.order := List.mem_toFinset.mp (H.hc.1.mem_of_porfStep h1c).2
          have hzk : z ∈ c.keep r w := Config.mem_keep_of_porf hz hrest
          have hzr : z ≠ r := fun h' => H.hnp (h' ▸ hrest)
          refine Relation.TransGen.head (H.step_of_kept hzk hzr ?_ h1c) ih
          intro x' hx'
          rw [hx'] at h1 h1c
          exact Config.mem_keep_of_porf (List.mem_toFinset.mp (H.hc.1.mem_of_porfStep h1c).1)
            (Relation.TransGen.head h1 hrest)
    exact key _ h
  · intro h
    have key : ∀ a, Relation.TransGen (c.revisit r w wp).abs.porfStep a (.th w) →
        Relation.TransGen (c.plus w).porfStep a (.th w) := by
      intro a ha
      induction ha using Relation.TransGen.head_induction_on with
      | single h1 => exact Relation.TransGen.single (H.step_into_w_iff.mp h1)
      | @head a b h1 hrest ih =>
        cases b with
        | init => exact absurd h1 ((c.revisit r w wp).abs.not_porfStep_init _)
        | th z =>
          have hzr : z ≠ r := fun h' => H.r_max _ (h' ▸ hrest)
          have hzw : z ≠ w := fun h' => H.w_ne_r (Ev.th.inj (H.w_out (h' ▸ hrest)))
          have hzk : z ∈ c.keep r w :=
            (H.events'.mp (H.wf'.1.mem_of_porfStep h1).2).resolve_left hzw
          exact Relation.TransGen.head (hplus_mono _ _ (H.step_into_kept hzk hzr h1)) ih
    exact key _ h

/-- The available events after a revisit (the paper, proof of (P5)): an event
available before, the successor of the new write, the successor of the
revisited read, or an event at the position of a deleted event. -/
theorem avail_cases (H : RvHyp P τ c r w wp) {a : TEv}
    (ha : a ∈ P.avail (c.revisit r w wp).abs) :
    a ∈ P.avail c.abs ∨ (a.tid = w.tid ∧ a.idx = w.idx + 1) ∨
      (a.tid = r.tid ∧ a.idx = r.idx + 1) ∨
      ∃ z, c.Deleted r w z ∧ z.tid = a.tid ∧ z.idx = a.idx := by
  obtain ⟨ht, hi, hs⟩ := Program.mem_avail_iff.mp ha
  rw [Config.revisit_abs] at hi hs
  have hR := Config.restrict_keep_wf H.hc H.hpo H.hmaxD
  have hcntK := Config.cnt_restrict_keep (r := r) H.hc H.hidx
  have hidx' : w.idx = (c.abs.restrict (c.keep r w)).cnt w.tid := by
    rw [hcntK]
    exact H.hidx
  have hcnt : ∀ t, (((c.abs.restrict (c.keep r w)).addWrite w wp).setRF r (.th w)).cnt t =
      if t = w.tid then (c.abs.restrict (c.keep r w)).cnt t + 1
      else (c.abs.restrict (c.keep r w)).cnt t :=
    fun t => Graph.cnt_addWrite (wp := wp) hR hidx' t
  rw [hcnt] at hi
  by_cases htw : a.tid = w.tid
  · right; left
    rw [ifPos htw, htw, hcntK, ← H.hidx] at hi
    exact ⟨htw, hi⟩
  · rw [ifNeg htw] at hi
    by_cases hall : ∀ q ∈ c.abs.events, q.tid = a.tid → q ∈ c.keep r w
    · have hcnt2 : (c.abs.restrict (c.keep r w)).cnt a.tid = c.abs.cnt a.tid :=
        Graph.cnt_restrict _ hall
      rw [hcnt2] at hi
      by_cases htr : a.tid = r.tid
      · right; right; left
        refine ⟨htr, ?_⟩
        have h1 := H.hc.1.idx_lt_cnt (List.mem_toFinset.mpr H.hr)
        have h2 : ¬ r.idx + 1 < c.abs.cnt r.tid := by
          intro hlt
          obtain ⟨q, hq, hqt, hqi⟩ := (H.hc.1.exists_idx_iff _ _).mpr hlt
          have hqk := hall q hq (hqt.trans htr.symm)
          have := Config.keep_last H.hpo H.hr H.hnp hqk hqt
          omega
        rw [htr] at hi
        omega
      · left
        refine Program.mem_avail_iff.mpr ⟨ht, hi, ?_⟩
        have htr' : (((c.abs.restrict (c.keep r w)).addWrite w wp).setRF r (.th w)).trace a.tid =
            c.abs.trace a.tid := by
          rw [Graph.trace_setRF_of_ne _ htr, Graph.trace_addWrite hR hidx' H.hw H.hwp,
            ifNeg htw]
          unfold Graph.trace
          rw [hcnt2]
          refine Graph.traceBefore_restrict_of_keep H.hc.1 (le_refl _)
            (fun q hq hqt _ => hall q hq hqt) ?_
          intro q hq hqt _ s hs'
          exact Config.keep_sources H.hc H.hmaxD
            (Finset.mem_inter.mpr ⟨hq, hall q hq hqt⟩) hs'
        rw [htr'] at hs
        exact hs
    · right; right; right
      push Not at hall
      obtain ⟨z0, hz0, hz0t, hz0k⟩ := hall
      have hle : (c.abs.restrict (c.keep r w)).cnt a.tid ≤ z0.idx := by
        by_contra hlt
        obtain ⟨q, hq, hqt, hqi⟩ := (hR.exists_idx_iff a.tid z0.idx).mpr (by omega)
        have hq' := Finset.mem_inter.mp hq
        have hqz : q = z0 := H.hc.1.idx_inj q hq'.1 z0 hz0 (hqt.trans hz0t.symm) hqi
        exact hz0k (hqz ▸ hq'.2)
      have hlt : (c.abs.restrict (c.keep r w)).cnt a.tid < c.abs.cnt a.tid := by
        have := H.hc.1.idx_lt_cnt hz0
        rw [hz0t] at this
        omega
      obtain ⟨zc, hzc, hzct, hzci⟩ := (H.hc.1.exists_idx_iff _ _).mpr hlt
      refine ⟨zc, ?_, hzct, hzci.trans hi.symm⟩
      by_contra hnd
      have hzk : zc ∈ c.keep r w :=
        (Config.mem_keep_iff c r w zc).mpr ⟨List.mem_toFinset.mp hzc, hnd⟩
      have hlt' := hR.idx_lt_cnt (e := zc) (Finset.mem_inter.mpr ⟨hzc, hzk⟩)
      rw [hzct, hzci] at hlt'
      omega

end RvHyp

/-! ### The induction hypothesis -/

/-- The facts about the step that led to `c`, adding `e` with kind `k`, which
the induction uses: `e` is the newest event, (P4), (P5), and for a revisit of
`a`: the new write is read by `a`, and every other event added after `a` is
causally before the new write. The fields `head` and `rv` are not clauses of
Proposition A.22: they are facts about a step that the paper uses "by
construction" (in its steps (P1) ⟨7⟩2 and (P2) ⟨5⟩6); they are proved for each
step in `inv_nr` and `inv_rv`. -/
structure LastStep (P : Program) (c : Config) (e : TEv) (k : Kind) : Prop where
  head : ∃ l, c.order = e :: l
  me : c.abs.IsMe (.th (k.me e))
  p5a : ∀ x ∈ c.order, nextLt x (k.me e) → ¬ c.lt (k.me e) x
  p5b : ∀ a ∈ P.avail c.abs, ¬ nextLt a (k.me e)
  rv : ∀ a, k = .rv a →
    c.Bw e a ∧ ∀ y ∈ c.order, c.lt a y → y ≠ e → c.abs.porf (.th y) (.th e)

/-- The invariant of reached configurations: (P1), (P2), (P6), and the facts
about the last step if there is one. -/
structure Inv (P : Program) (c : Config) : Prop where
  p1 : ∀ s q, c.Bw s q → ¬ nextLt s q
  p2 : ∀ x ∈ c.order, ∀ y ∈ c.order, nextLt x y → c.lt y x →
    ∃ s q, (y = s ∨ c.abs.porf (.th y) (.th s)) ∧ c.Bw s q ∧ nextLt q x
  p6 : ∀ s q p, p ≠ s → p ≠ q → c.Bw s q → nextLt q p → p ∈ c.order →
    c.lt p q ∨ c.lt s p ∨ c.abs.porf (.th p) (.th s)
  last : c.order = [] ∨ ∃ e k, LastStep P c e k

theorem Inv.lastOf {c : Config} (I : Inv P c) {y : TEv} (hy : y ∈ c.order) :
    ∃ e k, LastStep P c e k := by
  rcases I.last with h | h
  · rw [h] at hy
    cases hy
  · exact h

namespace LastStep

variable {c : Config} {e : TEv} {k : Kind}

/-- Every other event was added before the newest one. -/
theorem newest (L : LastStep P c e k) {y : TEv} (hy : y ∈ c.order) (hne : y ≠ e) :
    c.lt y e := by
  obtain ⟨l, hl⟩ := L.head
  unfold Config.lt
  rw [hl] at hy ⊢
  exact List.before_cons_self ((List.mem_cons.mp hy).resolve_left hne) (Ne.symm hne)

theorem me_mem (L : LastStep P c e k) : k.me e ∈ c.order := List.mem_toFinset.mp L.me.1

/-- An available event is `<next`-after `me` ((P5), second part, positively). -/
theorem me_lt_avail (L : LastStep P c e k) (hc : c.Wf) {a : TEv} (ha : a ∈ P.avail c.abs) :
    nextLt (k.me e) a := by
  have hne : k.me e ≠ a := fun h =>
    Program.not_mem_of_mem_avail hc.1 ha (h ▸ L.me.1)
  exact (Program.nextLt_total hne).resolve_right (L.p5b a ha)

/-- An event that is `<next`-after `me` is equal to, or causally before, a write
that was added after a read reading from it; and that read is `me` or
`<next`-before `me`. (The argument that the paper repeats in the proofs of
(P1), (P2) and (P9).) -/
theorem witness (L : LastStep P c e k) (I : Inv P c) {y : TEv} (hy : y ∈ c.order)
    (h : nextLt (k.me e) y) :
    ∃ s q, (y = s ∨ c.abs.porf (.th y) (.th s)) ∧ c.Bw s q ∧
      (q = k.me e ∨ nextLt q (k.me e)) := by
  cases k with
  | nr =>
    have hye : y ≠ e := fun h' => Program.nextLt_irrefl e (h' ▸ h)
    obtain ⟨s, q, h1, h2, h3⟩ := I.p2 e L.me_mem y hy h (L.newest hy hye)
    exact ⟨s, q, h1, h2, Or.inr h3⟩
  | rv a =>
    obtain ⟨hbw, hpf⟩ := L.rv a rfl
    have ha : a ∈ c.order := hbw.2.2.1
    have hya : y ≠ a := fun h' => Program.nextLt_irrefl a (h' ▸ h)
    rcases List.Before.total hy ha hya with hlt | hlt
    · by_cases hye : y = e
      · exact ⟨e, a, Or.inl hye, hbw, Or.inl rfl⟩
      · exact ⟨e, a, Or.inr (hpf y hy hlt hye), hbw, Or.inl rfl⟩
    · obtain ⟨s, q, h1, h2, h3⟩ := I.p2 a ha y hy h hlt
      exact ⟨s, q, h1, h2, Or.inr h3⟩

end LastStep

/-- If the read `q` is maximally added and reads from a write `s` that was
added after it, then `s` is causally before the new write (line 27). -/
theorem Config.porf_of_max_bw {c : Config} {q s w : TEv} {S : Solver} {τ : TieBreak S}
    {K : Finset Lit} (hc : c.Wf)
    (hmax : c.IsMaximallyAdded τ K q w) (hbw : c.Bw s q) :
    (c.plus w).porf (.th s) (.th w) := by
  obtain ⟨hrf, hlt⟩ := hbw
  have hqr : q.IsRead := by
    by_contra hn
    have hnone := hc.1.rf_none q (Or.inr hn)
    rw [show c.abs.rf q = c.rf q from rfl, hrf] at hnone
    cases hnone
  obtain ⟨e', he', -, hprev, -⟩ := hmax.2.1 (fun hl => hl.not_isRead hqr)
  have he' := he' hqr
  rw [hrf] at he'
  cases he'
  obtain ⟨-, hle | hpf⟩ := hprev
  · rcases hle with hsq | h
    · rw [hsq] at hlt
      exact absurd hlt (List.Before.irrefl _ _)
    · exact absurd hlt (List.Before.asymm h)
  · exact hpf

/-! ### A plain addition preserves the invariant -/

theorem inv_nr {c c' : Config} {e : TEv} (hc : c.Wf) (I : Inv P c)
    (hs : StepL P M τ c e .nr c') : Inv P c' ∧ LastStep P c' e .nr := by
  have N := hs.nrFacts hc
  have hnext : P.IsNext c.abs e := hs.nr_inv.2.1
  have hmemc' : ∀ y, y ∈ c'.order ↔ y = e ∨ y ∈ c.order := by
    intro y
    rw [N.order, List.mem_cons]
  have hP2 : ∀ x ∈ c'.order, ∀ y ∈ c'.order, nextLt x y → c'.lt y x →
      ∃ s q, (y = s ∨ c'.abs.porf (.th y) (.th s)) ∧ c'.Bw s q ∧ nextLt q x := by
    intro x _ y _ hxy hlt
    rcases N.lt_iff.mp hlt with ⟨hxe, hyo⟩ | hlt'
    · obtain ⟨e0, k0, L⟩ := I.lastOf hyo
      have hme : nextLt (k0.me e0) e := L.me_lt_avail hc hnext.1
      rw [hxe] at hxy ⊢
      obtain ⟨s, q, h1, h2, h3⟩ := L.witness I hyo (Program.nextLt_trans hme hxy)
      refine ⟨s, q, h1.imp id N.porf_mono, (N.bw_iff hc).mpr h2, ?_⟩
      rcases h3 with h3 | h3
      · rw [h3]
        exact hme
      · exact Program.nextLt_trans h3 hme
    · obtain ⟨s, q, h1, h2, h3⟩ := I.p2 x hlt'.1 y hlt'.2.1 hxy hlt'
      exact ⟨s, q, h1.imp id N.porf_mono, (N.bw_iff hc).mpr h2, h3⟩
  refine ⟨⟨?_, hP2, ?_, Or.inr ⟨e, .nr, ?_⟩⟩, ?_⟩
  · exact fun s q h => I.p1 s q ((N.bw_iff hc).mp h)
  · intro s q p hps hpq hbw hqp hp
    have hbw' := (N.bw_iff hc).mp hbw
    have hso : s ∈ c.order := hbw'.2.1
    rcases (hmemc' p).mp hp with hpe | hpo'
    · exact Or.inr (Or.inl (N.lt_iff.mpr (Or.inl ⟨hpe, hso⟩)))
    · rcases I.p6 s q p hps hpq hbw' hqp hpo' with h | h | h
      · exact Or.inl (N.lt_iff.mpr (Or.inr h))
      · exact Or.inr (Or.inl (N.lt_iff.mpr (Or.inr h)))
      · exact Or.inr (Or.inr (N.porf_mono h))
  all_goals
    refine ⟨⟨c.order, N.order⟩, ⟨?_, N.porf_sink, ?_⟩, ?_, ?_, ?_⟩
    · exact List.mem_toFinset.mpr ((hmemc' e).mpr (Or.inl rfl))
    · intro b hb hbmax hne
      cases b with
      | init => trivial
      | th x =>
        have hxo : x ∈ c'.order := List.mem_toFinset.mp hb
        have hxe : x ≠ e := fun h => hne (congrArg Ev.th h)
        have hxc : x ∈ c.order := ((hmemc' x).mp hxo).resolve_left hxe
        rcases Program.nextLt_total hxe with h | h
        · exact h
        · exfalso
          obtain ⟨s, q, h1, h2, -⟩ := hP2 e ((hmemc' e).mpr (Or.inl rfl)) x hxo h
            (N.lt_iff.mpr (Or.inl ⟨rfl, hxc⟩))
          rcases h1 with h1 | h1
          · have hq : q ∈ c'.abs.events := List.mem_toFinset.mpr h2.2.2.1
            have hst : c'.abs.porfStep (.th s) (.th q) := Or.inr ⟨q, rfl, hq, h2.1⟩
            exact hbmax (.th q) (h1 ▸ Relation.TransGen.single hst)
          · exact hbmax _ h1
    · intro x _ _ hlt
      rcases N.lt_iff.mp hlt with ⟨_, he⟩ | hlt'
      · exact N.fresh he
      · exact N.fresh hlt'.2.1
    · intro a ha hlt
      by_cases hat : a.tid = e.tid
      · have hi := N.avail_same a ha hat
        have hea : nextLt e a := Or.inr (Or.inl ⟨hat.symm, by omega⟩)
        exact Program.nextLt_irrefl _ (Program.nextLt_trans hea hlt)
      · have hac := N.avail_other a ha hat
        have hea : nextLt e a := hnext.2 a hac (fun h => hat (h ▸ rfl))
        exact Program.nextLt_irrefl _ (Program.nextLt_trans hea hlt)
    · intro a ha
      cases ha

/-! ### A revisit preserves the invariant -/

theorem inv_rv {c : Config} {r w : TEv} {wp : Ev} (I : Inv P c) (H : RvHyp P τ c r w wp) :
    Inv P (c.revisit r w wp) ∧ LastStep P (c.revisit r w wp) w (.rv r) ∧
      (∀ x y, (c.Deleted r w x ∨ x = r) → (c.Deleted r w y ∨ y = r) →
        (c.lt x y ↔ nextLt x y)) ∧
      (∀ d, c.Deleted r w d → ¬ nextLt w d) := by
  obtain ⟨e0, k0, L⟩ := I.lastOf H.hr
  have hmw : nextLt (k0.me e0) w := L.me_lt_avail H.hc H.hav
  have D3 : ∀ {x s q : TEv}, (c.Deleted r w x ∨ x = r) →
      (x = s ∨ c.abs.porf (.th x) (.th s)) → ¬ c.Bw s q :=
    fun hx hxs => A20_D3 H.hc H.hpo H.hr H.hnp H.hmax hx hxs
  have hDaMem : ∀ y, (c.Deleted r w y ∨ y = r) → y ∈ c.order := by
    rintro y (hy | hy)
    · exact hy.1
    · exact hy ▸ H.hr
  -- nothing in `D ∪ {r}` is `<next`-after `me`
  have keyD : ∀ y, (c.Deleted r w y ∨ y = r) → ¬ nextLt (k0.me e0) y := by
    intro y hy h
    obtain ⟨s, q, h1, h2, -⟩ := L.witness I (hDaMem y hy) h
    exact D3 hy h1 h2
  -- (P9)
  have hP9 : ∀ d, c.Deleted r w d → ¬ nextLt w d :=
    fun d hd h => keyD d (Or.inl hd) (Program.nextLt_trans hmw h)
  -- `r <next w`
  have hrw : nextLt r w := by
    rcases Program.nextLt_total (Ne.symm H.w_ne_r) with h | h
    · exact h
    · exact absurd (Program.nextLt_trans hmw h) (keyD r (Or.inr rfl))
  -- (P3)
  have hP3' : ∀ x y, (c.Deleted r w x ∨ x = r) → (c.Deleted r w y ∨ y = r) →
      nextLt x y → ¬ c.lt y x := by
    intro x y hx hy hxy hlt
    obtain ⟨s, q, h1, h2, -⟩ := I.p2 x (hDaMem x hx) y (hDaMem y hy) hxy hlt
    exact D3 hy h1 h2
  have hP3 : ∀ x y, (c.Deleted r w x ∨ x = r) → (c.Deleted r w y ∨ y = r) →
      (c.lt x y ↔ nextLt x y) := by
    intro x y hx hy
    constructor
    · intro hlt
      have hne : x ≠ y := fun h => List.Before.irrefl _ _ (h ▸ hlt)
      rcases Program.nextLt_total hne with h | h
      · exact h
      · exact absurd hlt (hP3' y x hy hx h)
    · intro hxy
      have hne : y ≠ x := fun h => Program.nextLt_irrefl _ (h ▸ hxy)
      rcases List.Before.total (hDaMem y hy) (hDaMem x hx) hne with h | h
      · exact h
      · exact absurd h (hP3' x y hx hy hxy)
  have hDaNext : ∀ q, (c.Deleted r w q ∨ q = r) → q = r ∨ nextLt r q := by
    rintro q (hq | hq)
    · exact Or.inr ((hP3 r q (Or.inr rfl) (Or.inl hq)).mp hq.2.1)
    · exact Or.inl hq
  have hbwr : (c.revisit r w wp).Bw w r := H.bw_iff.mpr (Or.inl ⟨rfl, rfl⟩)
  -- transport of a witness of (P2) from `c` to the new configuration
  have T : ∀ x y s q, (y = s ∨ c.abs.porf (.th y) (.th s)) → c.Bw s q → nextLt q x →
      ∃ s' q', (y = s' ∨ (c.revisit r w wp).abs.porf (.th y) (.th s')) ∧
        (c.revisit r w wp).Bw s' q' ∧ nextLt q' x := by
    intro x y s q h1 hbw hqx
    have hso : s ∈ c.order := hbw.2.1
    have hqo : q ∈ c.order := hbw.2.2.1
    have hsnd : ¬ c.Deleted r w s := fun hd => A20_D1 H.hc H.hmax hd hbw
    have hsr : s ≠ r := fun h => D3 (x := r) (Or.inr rfl) (Or.inl h.symm) hbw
    by_cases hq : c.Deleted r w q ∨ q = r
    · have hpw := Config.porf_of_max_bw H.hc (H.hmax q hq) hbw
      have hyw : (c.plus w).porf (.th y) (.th w) := by
        rcases h1 with h1 | h1
        · exact h1 ▸ hpw
        · exact Relation.TransGen.trans
            (Graph.porf_mono (G := c.abs) (G' := c.plus w) (Finset.subset_insert _ _)
              (fun _ _ => rfl) h1) hpw
      refine ⟨w, r, Or.inr (H.porf_w_iff.mp hyw), hbwr, ?_⟩
      rcases hDaNext q hq with h | h
      · exact h ▸ hqx
      · exact Program.nextLt_trans h hqx
    · have hqk : q ∈ c.keep r w :=
        (Config.mem_keep_iff c r w q).mpr ⟨hqo, fun hd => hq (Or.inl hd)⟩
      exact ⟨s, q, h1.imp id (H.porf_kept hso hsnd hsr),
        H.bw_iff.mpr (Or.inr ⟨hbw, hqk, fun h => hq (Or.inr h)⟩), hqx⟩
  -- a kept event that is not causally before `w` was added before `r`, or is `r`
  have hkeptLt : ∀ y, y ∈ c.keep r w → ¬ (c.plus w).porf (.th y) (.th w) → y ≠ r → c.lt y r := by
    intro y hyk hnpf hyr
    have hyo := H.keep_sub hyk
    have hnlt : ¬ c.lt r y := fun h => ((Config.mem_keep_iff c r w y).mp hyk).2 ⟨hyo, h, hnpf⟩
    rcases List.Before.total hyo H.hr hyr with h | h
    · exact absurd h hnlt
    · exact h
  -- (P2)
  have hP2 : ∀ x ∈ (c.revisit r w wp).order, ∀ y ∈ (c.revisit r w wp).order, nextLt x y →
      (c.revisit r w wp).lt y x →
      ∃ s q, (y = s ∨ (c.revisit r w wp).abs.porf (.th y) (.th s)) ∧
        (c.revisit r w wp).Bw s q ∧ nextLt q x := by
    intro x _ y _ hxy hlt
    rcases H.lt_iff.mp hlt with ⟨hxw, hyk⟩ | ⟨hlt', hyk, hxk⟩
    · rw [hxw] at hxy ⊢
      by_cases hpf : (c.plus w).porf (.th y) (.th w)
      · exact ⟨w, r, Or.inr (H.porf_w_iff.mp hpf), hbwr, hrw⟩
      · have hyr : y ≠ r := fun h =>
          Program.nextLt_irrefl _ (Program.nextLt_trans hrw (h ▸ hxy))
        have hlty := hkeptLt y hyk hpf hyr
        obtain ⟨s, q, h1, h2, h3⟩ := I.p2 r H.hr y (H.keep_sub hyk)
          (Program.nextLt_trans hrw hxy) hlty
        obtain ⟨s', q', h1', h2', h3'⟩ := T r y s q h1 h2 h3
        exact ⟨s', q', h1', h2', Program.nextLt_trans h3' hrw⟩
    · obtain ⟨s, q, h1, h2, h3⟩ := I.p2 x (H.keep_sub hxk) y (H.keep_sub hyk) hxy hlt'
      exact T x y s q h1 h2 h3
  refine ⟨⟨?_, hP2, ?_, Or.inr ⟨w, .rv r, ?_⟩⟩, ?_, hP3, hP9⟩
  · -- (P1)
    intro s q hbw hsq
    rcases H.bw_iff.mp hbw with ⟨hs, hq⟩ | ⟨h, -, -⟩
    · rw [hs, hq] at hsq
      exact Program.nextLt_irrefl _ (Program.nextLt_trans hrw hsq)
    · exact I.p1 s q h hsq
  · -- (P6)
    intro s q p hps hpq hbw hqp hp
    rcases H.bw_iff.mp hbw with ⟨hs, hq⟩ | ⟨hbw0, hqk, hqr⟩
    · rw [hs] at hps ⊢
      rw [hq] at hpq ⊢
      have hpk : p ∈ c.keep r w := (H.mem_order'.mp hp).resolve_left hps
      by_cases hpf : (c.plus w).porf (.th p) (.th w)
      · exact Or.inr (Or.inr (H.porf_w_iff.mp hpf))
      · exact Or.inl (H.lt_iff.mpr (Or.inr ⟨hkeptLt p hpk hpf hpq, hpk, H.r_keep⟩))
    · have hqm : q ∈ c.abs.events ∩ c.keep r w :=
        Finset.mem_inter.mpr ⟨H.keep_mem_events hqk, hqk⟩
      have hsk : s ∈ c.keep r w := Config.keep_sources H.hc H.hmaxD hqm hbw0.1
      have hsnd : ¬ c.Deleted r w s := ((Config.mem_keep_iff c r w s).mp hsk).2
      have hsr : s ≠ r := fun h => D3 (x := r) (Or.inr rfl) (Or.inl h.symm) hbw0
      rcases H.mem_order'.mp hp with hpw | hpk
      · exact Or.inr (Or.inl (H.lt_iff.mpr (Or.inl ⟨hpw, hsk⟩)))
      · rcases I.p6 s q p hps hpq hbw0 hqp (H.keep_sub hpk) with h | h | h
        · exact Or.inl (H.lt_iff.mpr (Or.inr ⟨h, hpk, hqk⟩))
        · exact Or.inr (Or.inl (H.lt_iff.mpr (Or.inr ⟨h, hsk, hpk⟩)))
        · exact Or.inr (Or.inr (H.porf_kept (H.keep_sub hsk) hsnd hsr h))
  all_goals
    refine ⟨⟨_, H.order'⟩, ⟨H.events'.mpr (Or.inr H.r_keep), H.r_max, ?_⟩, ?_, ?_, ?_⟩
    · -- (P4): `r` is `me`
      intro b hb hbmax hne
      cases b with
      | init => trivial
      | th x =>
        have hxr : x ≠ r := fun h => hne (congrArg Ev.th h)
        rcases H.events'.mp hb with hxw | hxk
        · exfalso
          have hst : (c.revisit r w wp).abs.porfStep (.th w) (.th r) :=
            Or.inr ⟨r, rfl, H.events'.mpr (Or.inr H.r_keep), H.rf_r⟩
          rw [hxw] at hbmax
          exact hbmax (.th r) (Relation.TransGen.single hst)
        · rcases Program.nextLt_total hxr with h | h
          · exact h
          · exfalso
            have hnpf : ¬ (c.plus w).porf (.th x) (.th w) :=
              fun hpf => hbmax _ (H.porf_w_iff.mp hpf)
            obtain ⟨s, q, h1, h2, h3⟩ := I.p2 r H.hr x (H.keep_sub hxk) h
              (hkeptLt x hxk hnpf hxr)
            obtain ⟨s', q', h1', h2', -⟩ := T r x s q h1 h2 h3
            rcases h1' with h1' | h1'
            · have hq : q' ∈ (c.revisit r w wp).abs.events :=
                List.mem_toFinset.mpr h2'.2.2.1
              have hst : (c.revisit r w wp).abs.porfStep (.th s') (.th q') :=
                Or.inr ⟨q', rfl, hq, h2'.1⟩
              exact hbmax (.th q') (h1' ▸ Relation.TransGen.single hst)
            · exact hbmax _ h1'
    · -- (P5), first part
      intro x _ hxr hlt
      rcases H.lt_iff.mp hlt with ⟨hxw, -⟩ | ⟨hlt', -, hxk⟩
      · rw [hxw] at hxr
        exact Program.nextLt_irrefl _ (Program.nextLt_trans hrw hxr)
      · obtain ⟨s, q, h1, h2, -⟩ := I.p2 x (H.keep_sub hxk) r H.hr hxr hlt'
        exact D3 (x := r) (Or.inr rfl) h1 h2
    · -- (P5), second part
      intro a ha hlt
      have hra : nextLt r a := by
        rcases H.avail_cases ha with hac | ⟨ht, hi⟩ | ⟨ht, hi⟩ | ⟨z, hz, hzt, hzi⟩
        · have haw : a ≠ w := fun h =>
            Program.not_mem_of_mem_avail H.wf'.1 ha (h ▸ H.events'.mpr (Or.inl rfl))
          exact Program.nextLt_trans hrw (H.hnext.2 a hac haw)
        · exact Program.nextLt_trans hrw (Or.inr (Or.inl ⟨ht.symm, by omega⟩))
        · exact Or.inr (Or.inl ⟨ht.symm, by omega⟩)
        · have hrz : nextLt r z := (hP3 r z (Or.inr rfl) (Or.inl hz)).mp hz.2.1
          rcases hrz with h | ⟨h1, h2⟩ | ⟨h1, h2, -⟩
          · exact Or.inl (hzt ▸ h)
          · exact Or.inr (Or.inl ⟨h1.trans hzt, hzi ▸ h2⟩)
          · exfalso
            have hrz' : r = z := H.hc.1.idx_inj r (List.mem_toFinset.mpr H.hr) z
              (List.mem_toFinset.mpr hz.1) h1 h2
            rw [← hrz'] at hz
            exact List.Before.irrefl _ _ hz.2.1
      exact Program.nextLt_irrefl _ (Program.nextLt_trans hra hlt)
    · -- the facts about a revisit
      intro a ha
      cases ha
      refine ⟨hbwr, fun y hy hlt hyw => ?_⟩
      rcases H.lt_iff.mp hlt with ⟨h, -⟩ | ⟨hlt', -, hyk⟩
      · exact absurd h hyw
      · refine H.porf_w_iff.mp ?_
        by_contra hnpf
        exact ((Config.mem_keep_iff c r w y).mp hyk).2 ⟨H.keep_sub hyk, hlt', hnpf⟩

/-! ### Proposition A.22 -/

/-- Every reached configuration satisfies the invariant. -/
theorem Reach.inv {c : Config} (h : Reach P M τ c) : Inv P c := by
  unfold Reach at h
  induction h with
  | refl =>
    refine ⟨?_, ?_, ?_, Or.inl rfl⟩
    · intro s q hbw
      exact absurd hbw.2.1 (by simp [Config.init])
    · intro x hx
      exact absurd hx (by simp [Config.init])
    · intro s q p _ _ _ _ hp
      exact absurd hp (by simp [Config.init])
  | @tail b c' hb hs ih =>
    have hbR : Reach P M τ b := hb
    obtain ⟨hw, hpo, -, -⟩ := hbR.sound
    obtain ⟨e, k, hs⟩ := hs
    cases k with
    | nr => exact (inv_nr hw ih hs).1
    | rv r =>
      obtain ⟨wp, rfl, H⟩ := hs.rvHyp hw hpo
      exact (inv_rv ih H).1

/-- Proposition A.22: the clauses hold for every step from a reached
configuration. -/
theorem Reach.a22 {c c' : Config} {e : TEv} {k : Kind}
    (h : Reach P M τ c) (hs : StepL P M τ c e k c') : A22 P c e k c' := by
  obtain ⟨hw, hpo, -, -⟩ := h.sound
  have I := h.inv
  cases k with
  | nr =>
    obtain ⟨I', L'⟩ := inv_nr hw I hs
    refine ⟨I'.p1, I'.p2, ?_, L'.me, L'.p5a, L'.p5b, I'.p6, ?_⟩
    · intro r hk
      cases hk
    · intro r hk
      cases hk
  | rv r =>
    obtain ⟨wp, rfl, H⟩ := hs.rvHyp hw hpo
    obtain ⟨I', L', hP3, hP9⟩ := inv_rv I H
    refine ⟨I'.p1, I'.p2, ?_, L'.me, L'.p5a, L'.p5b, I'.p6, ?_⟩
    · intro r' hk
      cases hk
      exact hP3
    · intro r' hk
      cases hk
      exact hP9

/-! ### Consequences used by the later proofs -/

/-- A reached configuration other than the initial one has a last step. -/
theorem Reach.lastStep {c : Config} (h : Reach P M τ c) (hne : c.order ≠ []) :
    ∃ e k, LastStep P c e k :=
  h.inv.last.resolve_left hne

/-- (P4) with Def. A.13: `me` of the configuration after a step. -/
theorem Reach.me_eq {c c' : Config} {e : TEv} {k : Kind} (h : Reach P M τ c)
    (hs : StepL P M τ c e k c') {a : Ev} (ha : c'.abs.IsMe a) : a = .th (k.me e) :=
  ha.unique (h.a22 hs).p4

/-- From (P3): a deleted event is `<next`-after the revisited read. -/
theorem A22.del_after_r {c c' : Config} {e r : TEv} (A : A22 P c e (.rv r) c') {d : TEv}
    (hd : c.Deleted r e d) : nextLt r d :=
  (A.p3 r rfl r d (Or.inr rfl) (Or.inl hd)).mp hd.2.1

/-- The deleted events are the events that are no longer in the configuration. -/
theorem RvHyp.deleted_iff {c : Config} {r w : TEv} {wp : Ev} (H : RvHyp P τ c r w wp)
    {y : TEv} : c.Deleted r w y ↔ y ∈ c.order ∧ y ∉ (c.revisit r w wp).order := by
  rw [H.mem_order', Config.mem_keep_iff]
  constructor
  · intro hd
    exact ⟨hd.1, fun h => h.elim (fun hw => H.fresh (hw ▸ hd.1)) (fun hk => hk.2 hd)⟩
  · rintro ⟨hy, hn⟩
    by_contra hnd
    exact hn (Or.inr ⟨hy, hnd⟩)

/-- `(G.rf ∩ >); G.po ⊆ <`: if a read reads from a write added after it, the
events after the read in its thread were added after that write (from (P6),
used in the paper's proof of Proposition A.28). -/
theorem Reach.bw_po_lt {c : Config} (h : Reach P M τ c) {s q p : TEv} (hbw : c.Bw s q)
    (hpo : c.abs.po (.th q) (.th p)) : c.lt s p := by
  obtain ⟨hw, hpoLt, hcons, -⟩ := h.sound
  obtain ⟨hqm, hpm, ht, hi⟩ := hpo
  have hqo : q ∈ c.order := List.mem_toFinset.mp hqm
  have hpo' : p ∈ c.order := List.mem_toFinset.mp hpm
  have hqp : c.lt q p := hpoLt q hqo p hpo' ht hi
  have hst1 : c.abs.porfStep (.th s) (.th q) := Or.inr ⟨q, rfl, hqm, hbw.1⟩
  have hst2 : c.abs.porfStep (.th q) (.th p) := Or.inl ⟨hqm, hpm, ht, hi⟩
  have hsp : c.abs.porf (.th s) (.th p) :=
    Relation.TransGen.trans (Relation.TransGen.single hst1) (Relation.TransGen.single hst2)
  have hps : p ≠ s := fun h' => M.porf_irrefl hw.1 hcons (.th s) (h' ▸ hsp)
  have hpq : p ≠ q := fun h' => List.Before.irrefl _ _ (h' ▸ hqp)
  rcases h.inv.p6 s q p hps hpq hbw (Or.inr (Or.inl ⟨ht, hi⟩)) hpo' with h1 | h1 | h1
  · exact absurd hqp (List.Before.asymm h1)
  · exact h1
  · exact absurd (Relation.TransGen.trans hsp h1) (M.porf_irrefl hw.1 hcons (.th s))

end Condpor
