import Mathlib.Order.Extension.Linear
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Finset.Fin

/-!
# Hitting and strong hitting on a poset

`pctdpor`, `testing.tex` (def:hitting, def:strong, fact:strong (1)) and
`depth.tex`, sec:static, as far as complete schedules are concerned:
lem:strong-exists, the characterisation of strong hitting in the proof of
prop:sh-eq, and the order-theoretic parts of thm:static (1) and (2).

How the text is read here.

* A schedule of a poset is a linear extension. It is given by its strict
  total order `α.lt` (`LinExt`), not by a list.
* Tuples are indexed from `0`.
* `PDir` is a directive on positions, read on complete schedules by
  lem:viol-order: `Sat α D` says that `α` does not p-violate `D`.
  Condition 1 of "p-guarantees" is about partial schedules and is not part of
  this file.
-/

namespace Pct

variable {X : Type} [PartialOrder X] {d : ℕ}

/-- A schedule of a poset: a strict total order that extends the order. -/
structure LinExt (X : Type) [PartialOrder X] where
  lt : X → X → Prop
  irrefl : ∀ x, ¬ lt x x
  trans : ∀ {x y z}, lt x y → lt y z → lt x z
  total : ∀ x y, lt x y ∨ x = y ∨ lt y x
  ext : ∀ {x y}, x < y → lt x y

/-- `x ≤_α y`. -/
def LinExt.le (α : LinExt X) (x y : X) : Prop := α.lt x y ∨ x = y

theorem LinExt.le_of_le (α : LinExt X) {x y : X} (h : x ≤ y) : α.le x y := by
  rcases eq_or_lt_of_le h with h | h
  · exact Or.inr h
  · exact Or.inl (α.ext h)

theorem LinExt.not_lt_of_le (α : LinExt X) {x y : X} (h : α.le x y) : ¬ α.lt y x := by
  rintro h'
  rcases h with h | rfl
  · exact α.irrefl _ (α.trans h h')
  · exact α.irrefl _ h'

/-- `α` hits the tuple (def:hitting). -/
def Hits (α : LinExt X) (a : Fin d → X) : Prop := ∀ i j, i < j → α.lt (a i) (a j)

/-- The tuple is admissible (def:hitting). -/
def Admissible (a : Fin d → X) : Prop := ∃ α : LinExt X, Hits α a

/-- `α` strongly hits the tuple (def:strong). -/
def StronglyHits (α : LinExt X) (x : Fin d → X) : Prop :=
  ∀ i y, α.le (x i) y → ∃ j, i ≤ j ∧ x j ≤ y

/-- The set `U_i` of lem:strong-exists. -/
def belowSet (x : Fin d → X) (i : Fin d) : Set X := {y | ∀ j, i ≤ j → ¬ x j ≤ y}

/-- Strong hitting says that `U_i` is before `x_i` (proof of prop:sh-eq). -/
theorem stronglyHits_iff (α : LinExt X) (x : Fin d → X) :
    StronglyHits α x ↔ ∀ i, ∀ y ∈ belowSet x i, α.lt y (x i) := by
  constructor
  · intro h i y hy
    rcases α.total y (x i) with h1 | h1 | h1
    · exact h1
    · obtain ⟨j, hij, hj⟩ := h i y (Or.inr h1.symm)
      exact absurd hj (hy j hij)
    · obtain ⟨j, hij, hj⟩ := h i y (Or.inl h1)
      exact absurd hj (hy j hij)
  · intro h i y hle
    by_contra hno
    have hy : y ∈ belowSet x i := fun j hij hj => hno ⟨j, hij, hj⟩
    exact α.not_lt_of_le hle (h i y hy)

/-- fact:strong (1): a schedule that strongly hits the last `d` entries of an
admissible tuple of `d + 1` entries hits the tuple. -/
theorem hits_of_stronglyHits_tail (α : LinExt X) (a : Fin (d + 1) → X)
    (hadm : Admissible a) (hs : StronglyHits α (fun i : Fin d => a i.succ)) : Hits α a := by
  obtain ⟨β, hβ⟩ := hadm
  intro i j hij
  by_contra hno
  have hle : α.le (a j) (a i) := by
    rcases α.total (a i) (a j) with h | h | h
    · exact absurd h hno
    · exact Or.inr h.symm
    · exact Or.inl h
  have hj0 : j ≠ 0 := fun h => by simp [h] at hij
  obtain ⟨j₀, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj0
  obtain ⟨j', hjj', hle'⟩ := hs j₀ (a i) hle
  have hlt : i < j'.succ := lt_of_lt_of_le hij (Fin.succ_le_succ_iff.mpr hjj')
  exact β.not_lt_of_le (β.le_of_le hle') (hβ i j'.succ hlt)

/-! ### lem:strong-exists -/

section Exists

open scoped Classical in
/-- The number of the block of `y`: the number of `i` with `y ∉ U_i`. -/
noncomputable def blockOf (x : Fin d → X) (y : X) : ℕ :=
  (Finset.univ.filter (fun i : Fin d => y ∉ belowSet x i)).card

open scoped Classical in
theorem blockOf_mono (x : Fin d → X) {y y' : X} (h : y ≤ y') :
    blockOf x y ≤ blockOf x y' := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, belowSet, Set.mem_ofPred_eq,
    not_forall, not_not] at hi ⊢
  obtain ⟨j, hij, hj⟩ := hi
  exact ⟨j, hij, hj.trans h⟩

open scoped Classical in
theorem blockOf_lt (x : Fin d → X) {i : Fin d} {y : X} (hy : y ∈ belowSet x i) :
    blockOf x y < blockOf x (x i) := by
  have h1 : blockOf x y ≤ i.val := by
    have : Finset.univ.filter (fun i' : Fin d => y ∉ belowSet x i') ⊆ Finset.Iio i := by
      intro i' hi'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, belowSet, Set.mem_ofPred_eq,
        not_forall, not_not] at hi'
      obtain ⟨j, hij, hj⟩ := hi'
      rw [Finset.mem_Iio]
      by_contra hge
      exact hy j ((not_lt.mp hge).trans hij) hj
    calc blockOf x y ≤ (Finset.Iio i).card := Finset.card_le_card this
      _ = i.val := Fin.card_Iio i
  have h2 : i.val + 1 ≤ blockOf x (x i) := by
    have : Finset.Iic i ⊆ Finset.univ.filter (fun i' : Fin d => x i ∉ belowSet x i') := by
      intro i' hi'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, belowSet, Set.mem_ofPred_eq,
        not_forall, not_not]
      exact ⟨i, Finset.mem_Iic.mp hi', le_refl _⟩
    calc i.val + 1 = (Finset.Iic i).card := (Fin.card_Iic i).symm
      _ ≤ blockOf x (x i) := Finset.card_le_card this
  omega

/-- The schedule of lem:strong-exists: the blocks in order, each block in
the order of a fixed linear extension. -/
noncomputable def blockExt (x : Fin d → X) : LinExt X where
  lt a b := blockOf x a < blockOf x b ∨
    (blockOf x a = blockOf x b ∧ toLinearExtension a < toLinearExtension b)
  irrefl a := by
    rintro (h | ⟨-, h⟩)
    · exact lt_irrefl _ h
    · exact lt_irrefl _ h
  trans := by
    rintro a b c (h | ⟨h, h'⟩) (k | ⟨k, k'⟩)
    · exact Or.inl (h.trans k)
    · exact Or.inl (k ▸ h)
    · exact Or.inl (h ▸ k)
    · exact Or.inr ⟨h.trans k, h'.trans k'⟩
  total a b := by
    rcases lt_trichotomy (blockOf x a) (blockOf x b) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases lt_trichotomy (toLinearExtension a) (toLinearExtension b) with k | k | k
      · exact Or.inl (Or.inr ⟨h, k⟩)
      · exact Or.inr (Or.inl k)
      · exact Or.inr (Or.inr (Or.inr ⟨h.symm, k⟩))
    · exact Or.inr (Or.inr (Or.inl h))
  ext := by
    intro a b hab
    rcases lt_or_eq_of_le (blockOf_mono x hab.le) with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h, lt_of_le_of_ne (toLinearExtension.monotone hab.le) ?_⟩
      intro e
      exact hab.ne e

/-- lem:strong-exists. The poset need not be finite. -/
theorem exists_stronglyHits (x : Fin d → X) : ∃ α : LinExt X, StronglyHits α x :=
  ⟨blockExt x, (stronglyHits_iff _ x).mpr (fun _ _ hy => Or.inl (blockOf_lt x hy))⟩

end Exists

/-! ### Directives on positions, read on complete schedules -/

/-- A directive on the elements of a poset. -/
structure PDir (X : Type) (d : ℕ) where
  A : Fin d → Set X
  b : Fin d → X
  b_inj : Function.Injective b

/-- The complete schedule `α` does not p-violate the directive
(lem:viol-order, for a schedule that emits every element). -/
def Sat (α : LinExt X) (D : PDir X d) : Prop :=
  ∀ i, (∀ c ∈ D.A i, c ≠ D.b i → α.lt c (D.b i)) ∧ ∀ j, j < i → α.lt (D.b j) (D.b i)

/-- thm:static (1), the order part: if some schedule does not p-violate the
directive, then no schedule that strongly hits its targets does. -/
theorem sat_of_stronglyHits {D : PDir X d} {α₀ α : LinExt X} (h₀ : Sat α₀ D)
    (hs : StronglyHits α D.b) : Sat α D := by
  intro i
  constructor
  · intro c hc hne
    by_contra hno
    have hle : α.le (D.b i) c := by
      rcases α.total c (D.b i) with h | h | h
      · exact absurd h hno
      · exact absurd h hne
      · exact Or.inl h
    obtain ⟨j, hij, hj⟩ := hs i c hle
    have h1 : α₀.lt c (D.b i) := (h₀ i).1 c hc hne
    have h2 : α₀.le (D.b i) (D.b j) := by
      rcases eq_or_lt_of_le hij with rfl | hlt
      · exact Or.inr rfl
      · exact Or.inl ((h₀ j).2 i hlt)
    have h3 : α₀.lt c (D.b j) := by
      rcases h2 with h2 | h2
      · exact α₀.trans h1 h2
      · exact h2 ▸ h1
    exact α₀.not_lt_of_le (α₀.le_of_le hj) h3
  · intro j hji
    by_contra hno
    have hle : α.le (D.b i) (D.b j) := by
      rcases α.total (D.b j) (D.b i) with h | h | h
      · exact absurd h hno
      · exact Or.inr h.symm
      · exact Or.inl h
    obtain ⟨l, hil, hl⟩ := hs i (D.b j) hle
    have hjl : j < l := lt_of_lt_of_le hji hil
    exact α₀.not_lt_of_le (α₀.le_of_le hl) ((h₀ l).2 j hjl)

/-- prop:sh-eq, first paragraph of the proof: `α` strongly hits `x` iff every
member of `U_i` other than `x_i` is before `x_i`. The directive that lists
the targets in the order of a strongly hitting schedule is
`exists_pguar_of_stronglyGuar` in `Static.lean`. -/
theorem stronglyHits_iff_sets (α : LinExt X) (x : Fin d → X) :
    StronglyHits α x ↔ ∀ i, ∀ c ∈ belowSet x i, c ≠ x i → α.lt c (x i) := by
  rw [stronglyHits_iff]
  constructor
  · intro h i c hc _
    exact h i c hc
  · intro h i c hc
    refine h i c hc ?_
    rintro rfl
    exact hc i le_rfl le_rfl

/-- The directive of thm:static (2) for a tuple of `d + 1` entries. -/
def chainDir (a : Fin (d + 1) → X) (ha : Function.Injective a) : PDir X d where
  A i := {a i.castSucc}
  b i := a i.succ
  b_inj := fun _ _ h => Fin.succ_injective _ (ha h)

/-- thm:static (2), the order part: a complete schedule does not p-violate
the directive of the tuple iff it hits the tuple. -/
theorem sat_chainDir_iff (α : LinExt X) (a : Fin (d + 1) → X) (ha : Function.Injective a) :
    Sat α (chainDir a ha) ↔ Hits α a := by
  constructor
  · intro h
    have step : ∀ i : Fin d, α.lt (a i.castSucc) (a i.succ) := by
      intro i
      refine (h i).1 _ rfl ?_
      intro e
      exact absurd (ha e) (Fin.castSucc_lt_succ).ne
    intro i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i₀, rfl⟩ | rfl
    · have hj0 : j ≠ 0 := fun e => by simp [e] at hij
      obtain ⟨j₀, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj0
      have hle : i₀ ≤ j₀ := Fin.castSucc_lt_succ_iff.mp hij
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact step i₀
      · exact α.trans (step i₀) ((h j₀).2 i₀ hlt)
    · exact absurd hij (not_lt.mpr (Fin.le_last j))
  · intro h i
    constructor
    · rintro c rfl -
      exact h _ _ Fin.castSucc_lt_succ
    · intro j hji
      exact h _ _ (Fin.succ_lt_succ_iff.mpr hji)

end Pct
