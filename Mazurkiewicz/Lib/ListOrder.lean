import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup

/-!
# The order given by positions in a list

`l.Before a b`: both `a` and `b` occur in `l`, and the first occurrence of `a`
is at an earlier position than the first occurrence of `b`.
(Coq: `total_order_from_list`, `trust/Util.v`.)

Two uses, with opposite readings:

* a coherence list `co x` is in coherence order, so `Before a b` says that `a`
  is coherence-before `b`;
* the order list of a configuration is newest first, so `Before a b` says that
  `a` was added *after* `b`.
-/

namespace List

variable {α : Type*} [DecidableEq α]

/-- `a` occurs in `l` at an earlier position than `b`. -/
def Before (l : List α) (a b : α) : Prop :=
  a ∈ l ∧ b ∈ l ∧ l.idxOf a < l.idxOf b

instance (l : List α) (a b : α) : Decidable (l.Before a b) := by
  unfold Before; infer_instance

theorem Before.irrefl (l : List α) (a : α) : ¬ l.Before a a :=
  fun h => Nat.lt_irrefl _ h.2.2

theorem Before.trans {l : List α} {a b c : α} (hab : l.Before a b) (hbc : l.Before b c) :
    l.Before a c :=
  ⟨hab.1, hbc.2.1, Nat.lt_trans hab.2.2 hbc.2.2⟩

theorem Before.ne {l : List α} {a b : α} (h : l.Before a b) : a ≠ b :=
  fun e => Before.irrefl l b (e ▸ h)

theorem Before.asymm {l : List α} {a b : α} (h : l.Before a b) : ¬ l.Before b a :=
  fun h' => Before.irrefl l a (h.trans h')

/-- The order is total on the members of the list. -/
theorem Before.total {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    l.Before a b ∨ l.Before b a := by
  rcases Nat.lt_trichotomy (l.idxOf a) (l.idxOf b) with h | h | h
  · exact Or.inl ⟨ha, hb, h⟩
  · exact absurd ((List.idxOf_inj ha).mp h) hne
  · exact Or.inr ⟨hb, ha, h⟩

theorem before_cons_self {l : List α} {a b : α} (hb : b ∈ l) (hne : a ≠ b) :
    (a :: l).Before a b := by
  refine ⟨mem_cons_self, mem_cons_of_mem _ hb, ?_⟩
  rw [idxOf_cons_self, idxOf_cons_ne _ hne]
  exact Nat.succ_pos _

theorem before_cons_of_before {l : List α} {a b c : α} (hc : c ∉ l) (h : l.Before a b) :
    (c :: l).Before a b := by
  obtain ⟨ha, hb, hlt⟩ := h
  have hca : c ≠ a := fun e => hc (e ▸ ha)
  have hcb : c ≠ b := fun e => hc (e ▸ hb)
  refine ⟨mem_cons_of_mem _ ha, mem_cons_of_mem _ hb, ?_⟩
  rw [idxOf_cons_ne _ hca, idxOf_cons_ne _ hcb]
  exact Nat.succ_lt_succ hlt

/-- Unfolding `Before` at a cons cell. -/
theorem before_cons_iff {l : List α} {a b c : α} :
    (c :: l).Before a b ↔ (c = a ∧ a ≠ b ∧ b ∈ l) ∨ (c ≠ a ∧ c ≠ b ∧ l.Before a b) := by
  unfold Before
  by_cases hca : c = a
  · subst hca
    by_cases hcb : c = b
    · subst hcb; simp
    · simp [idxOf_cons_ne _ hcb, hcb, Ne.symm hcb]
  · by_cases hcb : c = b
    · subst hcb
      simp [idxOf_cons_ne _ hca, hca]
    · simp [idxOf_cons_ne _ hca, idxOf_cons_ne _ hcb, hca, hcb, Ne.symm hca, Ne.symm hcb]

/-- The order of a list with a new first element. -/
theorem before_cons_iff_of_notMem {l : List α} {e a b : α} (he : e ∉ l) :
    (e :: l).Before a b ↔ (a = e ∧ b ∈ l) ∨ l.Before a b := by
  rw [before_cons_iff]
  constructor
  · rintro (⟨h1, _, h3⟩ | ⟨_, _, h3⟩)
    · exact Or.inl ⟨h1.symm, h3⟩
    · exact Or.inr h3
  · rintro (⟨h1, h2⟩ | h)
    · exact Or.inl ⟨h1.symm, fun hab => he (h1 ▸ hab ▸ h2), h2⟩
    · exact Or.inr ⟨fun h' => he (h' ▸ h.1), fun h' => he (h' ▸ h.2.1), h⟩

/-- Filtering keeps the order of the elements that are kept. -/
theorem before_filter_iff {l : List α} {p : α → Bool} {a b : α} :
    (l.filter p).Before a b ↔ l.Before a b ∧ p a = true ∧ p b = true := by
  induction l with
  | nil => simp [Before]
  | cons c l ih =>
    by_cases hc : p c = true
    · rw [filter_cons_of_pos hc, before_cons_iff, before_cons_iff, ih]
      constructor
      · rintro (⟨rfl, hne, hb⟩ | ⟨h1, h2, h3, h4, h5⟩)
        · exact ⟨Or.inl ⟨rfl, hne, (mem_filter.mp hb).1⟩, hc, (mem_filter.mp hb).2⟩
        · exact ⟨Or.inr ⟨h1, h2, h3⟩, h4, h5⟩
      · rintro ⟨(⟨rfl, hne, hb⟩ | ⟨h1, h2, h3⟩), h4, h5⟩
        · exact Or.inl ⟨rfl, hne, mem_filter.mpr ⟨hb, h5⟩⟩
        · exact Or.inr ⟨h1, h2, h3, h4, h5⟩
    · rw [filter_cons_of_neg hc, ih, before_cons_iff]
      constructor
      · rintro ⟨h3, h4, h5⟩
        exact ⟨Or.inr ⟨fun e => hc (e ▸ h4), fun e => hc (e ▸ h5), h3⟩, h4, h5⟩
      · rintro ⟨(⟨rfl, _, _⟩ | ⟨_, _, h3⟩), h4, h5⟩
        · exact absurd h4 hc
        · exact ⟨h3, h4, h5⟩

/-! ### Insertion after a given element

`l.insertAfter a x` puts `x` immediately after the first occurrence of `a`.
This is `SetCO` of Algorithm 1 on one coherence list, for a thread write `a`
of the list:

* placing `x` after `init` is `x :: l` (`init` is not in the list);
* placing `x` after the thread write `a ∈ l` is `l.insertAfter a x`.

If `a` does not occur, `x` is put at the end; this case is a fallback and is
not the `init` case. -/

/-- Insert `x` immediately after `a`. -/
def insertAfter : List α → α → α → List α
  | [], _, x => [x]
  | b :: l, a, x => if b = a then b :: x :: l else b :: insertAfter l a x

@[simp] theorem mem_insertAfter {l : List α} {a x y : α} :
    y ∈ l.insertAfter a x ↔ y = x ∨ y ∈ l := by
  induction l with
  | nil => simp [insertAfter]
  | cons b l ih =>
    unfold insertAfter
    split
    · simp only [mem_cons]; tauto
    · simp only [mem_cons, ih]; tauto

theorem Nodup.insertAfter {l : List α} {a x : α} (hl : l.Nodup) (hx : x ∉ l) :
    (l.insertAfter a x).Nodup := by
  induction l with
  | nil => simp [List.insertAfter]
  | cons b l ih =>
    have hb : b ∉ l := (nodup_cons.mp hl).1
    have hl' : l.Nodup := (nodup_cons.mp hl).2
    have hxb : x ≠ b := fun e => hx (e ▸ mem_cons_self)
    have hxl : x ∉ l := fun h => hx (mem_cons_of_mem _ h)
    unfold List.insertAfter
    split
    · refine nodup_cons.mpr ⟨?_, nodup_cons.mpr ⟨hxl, hl'⟩⟩
      simp only [mem_cons, not_or]
      exact ⟨Ne.symm hxb, hb⟩
    · refine nodup_cons.mpr ⟨?_, ih hl' hxl⟩
      simp only [mem_insertAfter, not_or]
      exact ⟨Ne.symm hxb, hb⟩

/-- The order of the old elements is unchanged. -/
theorem before_insertAfter_old {l : List α} {a x y z : α}
    (hy : y ≠ x) (hz : z ≠ x) :
    (l.insertAfter a x).Before y z ↔ l.Before y z := by
  induction l with
  | nil => simp [insertAfter, Before, hy, hz]
  | cons b l ih =>
    unfold insertAfter
    split
    · have h1 : x ≠ y := Ne.symm hy
      have h2 : x ≠ z := Ne.symm hz
      simp only [before_cons_iff, mem_cons]
      tauto
    · simp only [before_cons_iff, ih, mem_insertAfter]
      tauto

/-- The new element is after `a`. -/
theorem before_insertAfter_self {l : List α} {a x : α} (ha : a ∈ l) (hx : x ∉ l) :
    (l.insertAfter a x).Before a x := by
  have hax : a ≠ x := fun e => hx (e ▸ ha)
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    have hxb : x ≠ b := fun e => hx (e ▸ mem_cons_self)
    have hxl : x ∉ l := fun h => hx (mem_cons_of_mem _ h)
    unfold insertAfter
    split
    · next h => subst h; exact before_cons_iff.mpr (Or.inl ⟨rfl, hax, mem_cons_self⟩)
    · next h =>
      have ha' : a ∈ l := (mem_cons.mp ha).resolve_left (fun e => h e.symm)
      exact before_cons_iff.mpr (Or.inr ⟨h, Ne.symm hxb, ih ha' hxl⟩)

/-- The new element is before exactly the elements that `a` is before. -/
theorem before_insertAfter_new_left {l : List α} {a x z : α} (ha : a ∈ l) (hx : x ∉ l) :
    (l.insertAfter a x).Before x z ↔ l.Before a z := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    have hxb : x ≠ b := fun e => hx (e ▸ mem_cons_self)
    have hxl : x ∉ l := fun h => hx (mem_cons_of_mem _ h)
    unfold insertAfter
    split
    · next h =>
      subst h
      rw [before_cons_iff, before_cons_iff, before_cons_iff]
      constructor
      · rintro (⟨h1, _, _⟩ | ⟨_, h2, (⟨_, h4, h5⟩ | ⟨h3, _, _⟩)⟩)
        · exact absurd h1.symm hxb
        · exact Or.inl ⟨rfl, h2, h5⟩
        · exact absurd rfl h3
      · rintro (⟨_, h2, h3⟩ | ⟨h1, _, _⟩)
        · have hxz : x ≠ z := fun e => hxl (e ▸ h3)
          exact Or.inr ⟨Ne.symm hxb, h2, Or.inl ⟨rfl, hxz, h3⟩⟩
        · exact absurd rfl h1
    · next h =>
      have ha' : a ∈ l := (mem_cons.mp ha).resolve_left (fun e => h e.symm)
      rw [before_cons_iff, before_cons_iff, ih ha' hxl]
      constructor
      · rintro (⟨h1, _, _⟩ | ⟨_, h2, h3⟩)
        · exact absurd h1.symm hxb
        · exact Or.inr ⟨h, h2, h3⟩
      · rintro (⟨h1, _, _⟩ | ⟨_, h2, h3⟩)
        · exact absurd h1 h
        · exact Or.inr ⟨Ne.symm hxb, h2, h3⟩

/-- The elements before the new element are `a` and the elements before `a`. -/
theorem before_insertAfter_new_right {l : List α} {a x y : α} (ha : a ∈ l) (hx : x ∉ l) :
    (l.insertAfter a x).Before y x ↔ y = a ∨ l.Before y a := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    have hxb : x ≠ b := fun e => hx (e ▸ mem_cons_self)
    have hxl : x ∉ l := fun h => hx (mem_cons_of_mem _ h)
    unfold insertAfter
    split
    · next h =>
      subst h
      simp only [before_cons_iff, mem_cons]
      grind
    · next h =>
      have ha' : a ∈ l := (mem_cons.mp ha).resolve_left (fun e => h e.symm)
      simp only [before_cons_iff, ih ha' hxl, mem_insertAfter]
      grind

/-- The order after an insertion, all cases. (Coq: `into_rel`.) -/
theorem before_insertAfter_iff {l : List α} {a x y z : α} (ha : a ∈ l) (hx : x ∉ l) :
    (l.insertAfter a x).Before y z ↔
      (y ≠ x ∧ z ≠ x ∧ l.Before y z) ∨ (y = x ∧ l.Before a z) ∨
        (z = x ∧ (y = a ∨ l.Before y a)) := by
  have hax : a ≠ x := fun e => hx (e ▸ ha)
  by_cases hy : y = x
  · subst hy
    by_cases hz : z = y
    · subst hz
      have h1 : ¬ l.Before a z := fun h => hx h.2.1
      have h2 : ¬ l.Before z a := fun h => hx h.1
      simp [Before.irrefl, h1, h2, Ne.symm hax]
    · rw [before_insertAfter_new_left ha hx]; simp [hz]
  · by_cases hz : z = x
    · subst hz; rw [before_insertAfter_new_right ha hx]; simp [hy]
    · rw [before_insertAfter_old hy hz]; simp [hy, hz]

/-- Appending a new element at the end adds the pairs into the new element. -/
theorem before_append_singleton_iff {l : List α} {x y z : α} (hx : x ∉ l) :
    (l ++ [x]).Before y z ↔ l.Before y z ∨ (y ∈ l ∧ z = x) := by
  induction l with
  | nil =>
    have h : ¬ ([x] : List α).Before y z := by
      rw [before_cons_iff]
      rintro (⟨_, _, h⟩ | ⟨_, _, h⟩)
      · simp at h
      · exact absurd h.1 (by simp)
    have h' : ¬ ([] : List α).Before y z := fun h => absurd h.1 (by simp)
    simp [h, h']
  | cons b l ih =>
    have hxb : x ≠ b := fun e => hx (e ▸ mem_cons_self)
    have hxl : x ∉ l := fun h => hx (mem_cons_of_mem _ h)
    rw [cons_append, before_cons_iff, before_cons_iff, ih hxl]
    simp only [mem_append, mem_cons]
    grind

/-- In a list without repetition, nothing is after the last element. -/
theorem not_before_getLast {l : List α} (hl : l.Nodup) (hne : l ≠ []) (z : α) :
    ¬ l.Before (l.getLast hne) z := by
  induction l with
  | nil => exact absurd rfl hne
  | cons b l ih =>
    have hb : b ∉ l := (nodup_cons.mp hl).1
    have hl' : l.Nodup := (nodup_cons.mp hl).2
    by_cases hl0 : l = []
    · subst hl0
      rw [before_cons_iff]
      rintro (⟨_, _, h⟩ | ⟨_, _, h⟩)
      · simp at h
      · exact absurd h.1 (by simp)
    · rw [getLast_cons hl0, before_cons_iff]
      rintro (⟨h1, _, _⟩ | ⟨_, _, h3⟩)
      · exact hb (h1 ▸ getLast_mem hl0)
      · exact ih hl' hl0 h3

/-- Filtering out the inserted element undoes the insertion. -/
theorem filter_insertAfter_of_neg {l : List α} {p : α → Bool} {a x : α} (hx : p x = false) :
    (l.insertAfter a x).filter p = l.filter p := by
  induction l with
  | nil => simp [insertAfter, hx]
  | cons b l ih =>
    unfold insertAfter
    split
    · by_cases hb : p b = true
      · simp [hb, hx]
      · simp [hb, hx]
    · by_cases hb : p b = true
      · simp [hb, ih]
      · simp [hb, ih]

/-- Inserting after the last element of a list without repetition appends. -/
theorem insertAfter_getLast {l : List α} (hl : l.Nodup) (hne : l ≠ []) (x : α) :
    l.insertAfter (l.getLast hne) x = l ++ [x] := by
  induction l with
  | nil => exact absurd rfl hne
  | cons b l ih =>
    have hb : b ∉ l := (nodup_cons.mp hl).1
    have hl' : l.Nodup := (nodup_cons.mp hl).2
    by_cases hl0 : l = []
    · subst hl0
      simp [insertAfter]
    · have hbne : b ≠ l.getLast hl0 := fun e => hb (e ▸ getLast_mem hl0)
      rw [getLast_cons hl0]
      unfold insertAfter
      simp only [hbne, ↓reduceIte, ih hl' hl0, cons_append]

/-! ### Examples -/

example : ([3, 1, 2] : List ℕ).Before 3 2 := by decide
example : ¬ ([3, 1, 2] : List ℕ).Before 2 1 := by decide
-- with a repetition, the first occurrence counts
example : ([1, 2, 1] : List ℕ).Before 1 2 ∧ ¬ ([1, 2, 1] : List ℕ).Before 2 1 := by decide
example : ([1, 2, 3] : List ℕ).insertAfter 1 9 = [1, 9, 2, 3] := by decide
example : ([1, 2, 3] : List ℕ).insertAfter 2 9 = [1, 2, 9, 3] := by decide
example : ([1, 2, 3] : List ℕ).insertAfter 3 9 = [1, 2, 3, 9] := by decide
-- the fallback: the anchor does not occur
example : ([1, 2, 3] : List ℕ).insertAfter 7 9 = [1, 2, 3, 9] := by decide
-- `SetCO` after `init` on the coherence list `[1, 2]` is a cons, not `insertAfter`
example : ((9 : ℕ) :: [1, 2]).Before 9 1 := by decide

end List
