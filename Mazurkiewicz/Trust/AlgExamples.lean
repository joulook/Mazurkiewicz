import Mazurkiewicz.Trust.Alg

/-!
# A revisit step of Algorithm 1, checked

The example of `Trust/Examples.lean`: thread `0` reads `x` and then writes
`y`; thread `1` writes `2` to `x`. After `r` and `d` have been added (the
configuration `C1`), the next event is the write `w`. We check, on the
definitions of `Trust/Alg.lean`:

* Def. A.6: exactly `d` is deleted when `w` revisits `r`;
* lines 23-27: `d` and `r` are maximally added;
* line 18: the resulting configuration has the order `[w, r]` and the graph
  `G2`, in which `r` reads from `w`;
* the step itself, `StepL.revisit`, under sequential consistency.
-/

namespace Trust

namespace Examples

open Graph

/-- The program: `a := x; y := 1 ∥ x := 2`. -/
def revProg : Program where
  threads := [0, 1]
  threads_nodup := by decide
  step := fun t u =>
    match t, u with
    | 0, [] => some (.read 0)
    | 0, [_] => some (.write 1 1)
    | 1, [] => some (.write 0 2)
    | _, _ => none
  mem := μ
  step_none := by
    intro t ht
    match t with
    | 0 | 1 => simp at ht
    | _ + 2 => rfl

theorem C1_abs : C1.abs = G1 := Graph.ext rfl (by decide) rfl rfl

theorem C1_wf : C1.Wf := ⟨C1_abs ▸ G1_wf, by decide⟩

/-- The only source in `C1` is `init`, for `r`. -/
theorem C1_rf (q : TEv) : C1.rf q = if q = r then some .init else none := by
  by_cases hq : q = r
  · subst hq
    decide
  · simp [C1, G1, Graph.addWrite, Graph.addRead, Graph.init, Function.update, hq]

theorem C1_plus : C1.plus w = G1w := by
  unfold Config.plus G1w
  rw [C1_abs]

/-- Def. A.6: `d` is deleted. -/
theorem C1_deleted_d : C1.Deleted r w d :=
  ⟨by decide, (by decide : ([d, r] : List TEv).Before d r),
    fun h => by rw [C1_plus] at h; cases porf_w h⟩

/-- The revisited read is not deleted. -/
theorem C1_not_deleted_r : ¬ C1.Deleted r w r := fun h => List.Before.irrefl _ _ h.2.1

/-- The events that remain are `r` alone. -/
theorem C1_keep : C1.keep r w = {r} := by
  ext q
  rw [Config.mem_keep_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hq, hnd⟩
    have hq' : q = d ∨ q = r := by simpa [C1] using hq
    rcases hq' with rfl | rfl
    · exact absurd C1_deleted_d hnd
    · rfl
  · rintro rfl
    exact ⟨by decide, C1_not_deleted_r⟩

/-- Lines 23-27 for the deleted write `d`. -/
theorem C1_max_d : C1.IsMaximallyAdded d w := by
  refine ⟨?_, .th d, rfl, ⟨by decide, Or.inl (Or.inl rfl)⟩, ?_⟩
  · rintro ⟨q, -, hq⟩
    rw [C1_rf] at hq
    split at hq <;> cases hq
  · rintro ⟨w', -, hco⟩
    cases w' with
    | init => exact hco
    | th q' =>
      have h : ([d] : List TEv).Before d q' := hco
      have hq' : q' = d := by simpa using h.2.1
      exact List.Before.irrefl _ _ (hq' ▸ h)

/-- Lines 23-27 for the revisited read `r`: its source `init` is the last
write to `x` among the previous events. -/
theorem C1_max_r : C1.IsMaximallyAdded r w := by
  refine ⟨?_, .init, (by decide : C1.rf r = some .init), trivial, ?_⟩
  · rintro ⟨q, -, hq⟩
    rw [C1_rf] at hq
    split at hq <;> cases hq
  · rintro ⟨w', -, hco⟩
    cases w' with
    | init => exact hco
    | th q' =>
      have h : q' ∈ ([] : List TEv) := hco
      cases h

/-- Line 18: the graph after the revisit is `G2`. -/
theorem C1_revisit_abs : (C1.revisit r w .init).abs = G2 := by
  rw [Config.revisit_abs, C1_keep, C1_abs]
  rfl

example : (C1.revisit r w .init).order = [w, r] := by
  unfold Config.revisit
  simp only [C1_keep]
  decide

/-! ### The step under sequential consistency -/

/-- `C1` is consistent under every maximally extensible model: it is built by
two maximal extensions. -/
theorem C1_cons (M : Model) (hM : M.Extensible) : M.cons C1.abs := by
  rw [C1_abs]
  have h0 : M.cons (Graph.init μ) := M.cons_init μ
  have w0 := Graph.init_wf μ
  have h1 : M.cons ((Graph.init μ).addRead r .init) :=
    hM.ext_read _ r 0 w0 h0 (by decide) rfl
  have w1 := w0.addRead (e := r) (x := 0) (w := .init) (by decide) rfl trivial
  exact hM.ext_write _ d w1 h1 (by decide) (by decide)

/-- `G2` as two maximal extensions of the initial graph. -/
theorem G2_eq : G2 = ((Graph.init μ).addWrite w .init).addRead r (.th w) := by
  have hrf : ∀ q, q ≠ r → (G1.restrict {r}).rf q = none := by
    intro q hq
    exact G1.restrict_rf_of_not_mem (by simp [hq])
  have hco : ∀ x, (G1.restrict {r}).co x = [] := by
    intro x
    rw [Graph.restrict_co, List.filter_eq_nil_iff]
    intro a ha
    have ham := ((G1_wf.co_mem x a).mp ha)
    have har : a ≠ r := by
      rintro rfl
      obtain ⟨v, hv⟩ := ham.2
      cases hv
    simp [har]
  apply Graph.ext
  · rfl
  · decide
  · funext q
    by_cases hq : q = r
    · subst hq
      simp [G2]
    · simp [G2, Function.update_of_ne hq, hrf q hq, Graph.init]
  · funext x
    by_cases hx : x = w.loc
    · subst hx
      change ((G1.restrict {r}).addWrite w .init).co w.loc =
        ((Graph.init μ).addWrite w .init).co w.loc
      rw [Graph.addWrite_co_self, Graph.addWrite_co_self, hco]
      rfl
    · change ((G1.restrict {r}).addWrite w .init).co x = ((Graph.init μ).addWrite w .init).co x
      rw [Graph.addWrite_co_of_ne _ _ _ hx, Graph.addWrite_co_of_ne _ _ _ hx, hco]
      rfl

theorem G2_cons (M : Model) (hM : M.Extensible) : M.cons G2 := by
  rw [G2_eq]
  have h0 : M.cons (Graph.init μ) := M.cons_init μ
  have w0 := Graph.init_wf μ
  have h1 : M.cons ((Graph.init μ).addWrite w .init) :=
    hM.ext_write _ w w0 h0 (by decide) (by decide)
  have w1 := w0.addWrite (e := w) (wp := .init) (by decide) (by decide) trivial
  exact hM.ext_read _ r 0 w1 h1 (by decide) rfl

/-- The next event of `C1` is the write `w`. -/
theorem C1_next : revProg.IsNext C1.abs w :=
  (Program.nextC_eq_some_iff C1_wf).mp (by decide)

/-- The revisit is a step of Algorithm 1 under sequential consistency
(`StepL.revisit`): from the configuration with order `[d, r]`, adding `w`
and revisiting `r`. -/
theorem C1_step : StepL revProg SC C1 w (.rv r) (C1.revisit r w .init) := by
  refine StepL.revisit (C1_cons SC SC.extensible) C1_next (by decide) (by decide) rfl ?_ ?_
    trivial ?_
  · intro h
    rw [C1_plus] at h
    cases porf_w h
  · rintro e (he | rfl)
    · have hed : e = d := by
        have hm : e ∈ C1.order := he.1
        have : e = d ∨ e = r := by simpa [C1] using hm
        rcases this with rfl | rfl
        · rfl
        · exact absurd he C1_not_deleted_r
      rw [hed]
      exact C1_max_d
    · exact C1_max_r
  · rw [C1_revisit_abs]
    exact G2_cons SC SC.extensible

/-! ### The whole run, and soundness applied to it -/

/-- `C1` is the initial configuration with `r` and then `d` added. -/
theorem C1_eq : ((Config.init μ).addRead r .init).addWrite d .init = C1 := rfl

/-- The first step: the read `r`, from `init`. -/
theorem step_r : StepL revProg SC (Config.init μ) r .nr ((Config.init μ).addRead r .init) := by
  have h0 : SC.cons (Config.init μ).abs := by
    rw [Config.init_abs]
    exact SC.cons_init μ
  refine StepL.read h0 ((Program.nextC_eq_some_iff (Config.init_wf μ)).mp (by decide)) rfl
    trivial ?_
  rw [Config.addRead_abs, Config.init_abs]
  exact SC.extensible.ext_read _ r 0 (Graph.init_wf μ) (SC.cons_init μ) (by decide) rfl

/-- The second step: the write `d`. -/
theorem step_d : StepL revProg SC ((Config.init μ).addRead r .init) d .nr C1 := by
  have hwf := step_r.wf (Config.init_wf μ) (Config.init_poLt μ)
  refine StepL.write step_r.cons ((Program.nextC_eq_some_iff hwf).mp (by decide)) (by decide)
    trivial ?_
  exact C1_cons SC SC.extensible

/-- Algorithm 1 reaches the configuration after the revisit. -/
theorem revisit_reach : Reach revProg SC (C1.revisit r w .init) :=
  ((Relation.ReflTransGen.refl.tail ⟨r, .nr, step_r⟩).tail ⟨d, .nr, step_d⟩).tail
    ⟨w, .rv r, C1_step⟩

/-- Soundness on this run: the reached graph `G2` is a well-formed,
SC-consistent execution of the program. -/
example : G2.Wf ∧ SC.cons G2 ∧ revProg.Exec G2 := by
  obtain ⟨hw, -, hc, hE⟩ := revisit_reach.sound
  have hw1 := hw.1
  rw [C1_revisit_abs] at hw1 hc hE
  exact ⟨hw1, hc, hE⟩

end Examples

end Trust
