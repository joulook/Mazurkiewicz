import Mazurkiewicz.Jmt.Stage

/-!
# Unjustified reads of the stages of a justification

A read of an execution is *unjustified* if its source does not happen before
it. This file proves that in a justification of `T` the unjustified reads of
the execution of stage `i` are exactly the unjustified reads of `T` committed
before stage `i`.

Two facts about executions of a program are hypotheses here, because the
abstract executions of `Jmt/Stage` do not include them: the initialization
key is not a read of `T`, and a committed key that is a read of `T` is a read
of the execution of its stage (whether a key is a read depends on the key
only).

Main statement:

* `Jmt.Justifies.unj_eq`: `unj (E (i + 1)) = unj T ∩ C i`.
-/

namespace Jmt

variable {Key Val : Type*}

/-- The unjustified reads of an execution: the reads whose source does not
happen before them. -/
def KExec.unj (E : KExec Key Val) : Set Key :=
  {r | ∃ w, E.rf r = some w ∧ ¬ E.hb w r}

variable {Ex : Set (KExec Key Val)} {init : Key}

/-- Commit sets grow. -/
theorem Justifies.mono_le {T : KExec Key Val} {n : ℕ} {E : ℕ → KExec Key Val}
    {C : ℕ → Set Key} (h : Justifies Ex init T n E C) :
    ∀ {i j : ℕ}, i ≤ j → j ≤ n → C i ⊆ C j := by
  intro i j hij
  induction hij with
  | refl => exact fun _ => subset_rfl
  | step _ ih => exact fun hj => (ih (by omega)).trans (h.mono _ (by omega))

/-- A committed key other than the initialization key is committed at some
stage. -/
theorem Justifies.commit_stage {T : KExec Key Val} {n : ℕ} {E : ℕ → KExec Key Val}
    {C : ℕ → Set Key} (h : Justifies Ex init T n E C) {r : Key} (hr : r ≠ init) :
    ∀ {i : ℕ}, r ∈ C i → ∃ j < i, r ∈ C (j + 1) ∧ r ∉ C j
  | 0, hi => by
    rw [h.c0] at hi
    exact absurd hi hr
  | i + 1, hi => by
    by_cases hc : r ∈ C i
    · obtain ⟨j, hj, h1, h2⟩ := h.commit_stage hr hc
      exact ⟨j, by omega, h1, h2⟩
    · exact ⟨i, by omega, hi, hc⟩

/-- The source in `T` of a committed read of `T` is committed, at the latest
together with the read's predecessor stage. -/
theorem Justifies.source_mem {T : KExec Key Val} {n : ℕ} {E : ℕ → KExec Key Val}
    {C : ℕ → Set Key} (h : Justifies Ex init T n E C) (hinit : T.rf init = none)
    (hrd : ∀ i < n, ∀ r ∈ C (i + 1), (T.rf r).isSome → ((E (i + 1)).rf r).isSome)
    {i : ℕ} (hi : i ≤ n) {r w : Key} (hr : r ∈ C i) (hw : T.rf r = some w) : w ∈ C i := by
  have hne : r ≠ init := by
    rintro rfl
    rw [hinit] at hw
    exact absurd hw (by simp)
  obtain ⟨j, hj, h1, h2⟩ := h.commit_stage hne hr
  have hjn : j < n := by omega
  obtain ⟨w0, hw0⟩ := Option.isSome_iff_exists.mp (hrd j hjn r h1 (by simp [hw]))
  obtain ⟨-, w', hw', hmem⟩ := h.j7 j hjn r h1 h2 w0 hw0
  rw [hw] at hw'
  cases hw'
  exact h.mono_le (by omega) hi hmem

/-- **Unjustified reads of a stage.** In a justification of `T`, the
unjustified reads of the execution of stage `i + 1` are the unjustified reads
of `T` in the commit set of stage `i`. -/
theorem Justifies.unj_eq {T : KExec Key Val} {n : ℕ} {E : ℕ → KExec Key Val}
    {C : ℕ → Set Key} (h : Justifies Ex init T n E C) (hinit : T.rf init = none)
    (hrd : ∀ i < n, ∀ r ∈ C (i + 1), (T.rf r).isSome → ((E (i + 1)).rf r).isSome)
    {i : ℕ} (hi : i < n) : (E (i + 1)).unj = T.unj ∩ C i := by
  ext r
  constructor
  · rintro ⟨w, hw, hnb⟩
    have hr : r ∈ C i := by
      by_contra hc
      exact hnb (h.j6 i hi r w hw hc)
    have hT : T.rf r = some w := by rw [← h.j5 i hi r hr]; exact hw
    have hwC : w ∈ C i := h.source_mem hinit hrd (by omega) hr hT
    refine ⟨⟨w, hT, fun hb => hnb ?_⟩, hr⟩
    exact (h.j2 i hi w (h.mono i hi hwC) r (h.mono i hi hr)).mpr hb
  · rintro ⟨⟨w, hT, hnb⟩, hr⟩
    have hwC : w ∈ C i := h.source_mem hinit hrd (by omega) hr hT
    refine ⟨w, by rw [h.j5 i hi r hr]; exact hT, fun hb => hnb ?_⟩
    exact (h.j2 i hi w (h.mono i hi hwC) r (h.mono i hi hr)).mp hb

/-- The unjustified reads of a justified execution are committed before the
last stage. -/
theorem Justifies.unj_subset {T : KExec Key Val} {n : ℕ} {E : ℕ → KExec Key Val}
    {C : ℕ → Set Key} (h : Justifies Ex init T n E C) (hinit : T.rf init = none)
    (hrd : ∀ i < n, ∀ r ∈ C (i + 1), (T.rf r).isSome → ((E (i + 1)).rf r).isSome) :
    T.unj ⊆ C (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := h.pos; omega⟩
  have := h.unj_eq hinit hrd (i := m) (by omega)
  rw [h.en] at this
  intro r hr
  have hr' : r ∈ T.unj ∩ C m := by rw [← this]; exact hr
  simpa using hr'.2

end Jmt
