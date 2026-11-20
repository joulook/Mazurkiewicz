import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Tactic.Linarith

/-!
# Finite sets of naturals
-/

/-- A finite set of naturals that is closed downwards is an initial segment. -/
theorem Finset.eq_range_of_downClosed {s : Finset ℕ} (h : ∀ i ∈ s, ∀ j < i, j ∈ s) :
    s = Finset.range s.card := by
  have hsub : s ⊆ Finset.range s.card := by
    intro i hi
    have hr : Finset.range (i + 1) ⊆ s := by
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Finset.mem_range.mp hj) with hlt | rfl
      · exact h i hi j hlt
      · exact hi
    have hc := Finset.card_le_card hr
    rw [Finset.card_range] at hc
    exact Finset.mem_range.mpr (by omega)
  exact Finset.eq_of_subset_of_card_le hsub (by simp)

example : ({0, 1, 2} : Finset ℕ) = Finset.range 3 := by decide
