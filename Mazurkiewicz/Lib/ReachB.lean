import Mazurkiewicz.Lib.Rel
import Mazurkiewicz.Lib.Path
import Mathlib.Data.List.Perm.Subperm

/-!
# Computable reachability on a finite set of nodes

`reachN r nodes n a b`: there is a path of `r` from `a` to `b` with at least
one and at most `n` steps, through the nodes of the list. For a relation
whose edges end in `nodes`, and `n = nodes.length`, this is the transitive
closure (`reachN_iff`); `acyclicB` decides acyclicity (`acyclicB_iff`).

These functions are used to run the checks of the algorithm (causality,
consistency). They are simple, not efficient.
-/

namespace Maz

open Relation

variable {α : Type*}

/-- A path of at least one and at most `n` steps of `r` from `a` to `b`,
with intermediate states taken from `nodes`. -/
def reachN (r : α → α → Bool) (nodes : List α) : ℕ → α → α → Bool
  | 0, _, _ => false
  | n + 1, a, b => r a b || nodes.any (fun m => r a m && reachN r nodes n m b)

/-- No node of the list is on a cycle of at most `nodes.length` steps. -/
def acyclicB (r : α → α → Bool) (nodes : List α) : Bool :=
  nodes.all (fun a => !reachN r nodes nodes.length a a)

theorem reachN_iff_path (r : α → α → Bool) (nodes : List α)
    (hsupp : ∀ a b, r a b = true → b ∈ nodes) (n : ℕ) (a b : α) :
    reachN r nodes n a b = true ↔
      ∃ p, Path (fun x y => r x y = true) a p b ∧ p ≠ [] ∧ p.length ≤ n := by
  induction n generalizing a with
  | zero =>
    simp only [reachN, Bool.false_eq_true, false_iff]
    rintro ⟨p, -, hne, hl⟩
    exact hne (List.length_eq_zero_iff.mp (Nat.le_zero.mp hl))
  | succ n ih =>
    simp only [reachN, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro (h | ⟨m, -, hm, hrest⟩)
      · exact ⟨[b], Path.cons h (Path.nil b), by simp, by simp⟩
      · obtain ⟨q, hq, -, hl⟩ := (ih m).mp hrest
        exact ⟨m :: q, Path.cons hm hq, by simp, by simpa using hl⟩
    · rintro ⟨p, hp, hne, hl⟩
      cases hp with
      | nil => exact absurd rfl hne
      | @cons _ c _ q hac hq =>
        by_cases hq0 : q = []
        · subst hq0
          cases hq
          exact Or.inl hac
        · exact Or.inr ⟨c, hsupp a c hac, hac,
            (ih c).mpr ⟨q, hq, hq0, by simpa using hl⟩⟩

/-- A non-empty path gives the transitive closure. -/
theorem Path.transGen {r : α → α → Prop} {a b : α} {p : List α} (h : Path r a p b)
    (hne : p ≠ []) : TransGen r a b := by
  cases h with
  | nil => exact absurd rfl hne
  | cons hab hrest => exact TransGen.head' hab hrest.reflTransGen

/-- Every state of a path is the target of an edge. -/
theorem Path.mem_target {r : α → α → Prop} {a b : α} {p : List α} (h : Path r a p b) :
    ∀ x ∈ p, ∃ y, r y x := by
  induction h with
  | nil => simp
  | @cons a c _ q hac _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨a, hac⟩
    · exact ih x hx

/-- Reachability is witnessed by a path without repeated states. -/
theorem exists_nodup_path {r : α → α → Prop} {a b : α} (h : TransGen r a b) :
    ∃ p, Path r a p b ∧ p ≠ [] ∧ p.Nodup := by
  classical
  induction h using TransGen.head_induction_on with
  | single h => exact ⟨[_], Path.cons h (Path.nil _), by simp, by simp⟩
  | @head a c hac _ ih =>
    obtain ⟨q, hq, -, hnd⟩ := ih
    by_cases hc : c ∈ q
    · obtain ⟨q1, q2, rfl⟩ := List.append_of_mem hc
      refine ⟨c :: q2, Path.cons hac hq.split.2, by simp, ?_⟩
      exact hnd.sublist (List.sublist_append_right q1 (c :: q2))
    · exact ⟨c :: q, Path.cons hac hq, by simp, List.nodup_cons.mpr ⟨hc, hnd⟩⟩

/-- `reachN` with `nodes.length` steps is the transitive closure, for a
relation whose edges end in `nodes`. -/
theorem reachN_iff (r : α → α → Bool) (nodes : List α)
    (hsupp : ∀ a b, r a b = true → b ∈ nodes) (a b : α) :
    reachN r nodes nodes.length a b = true ↔ TransGen (fun x y => r x y = true) a b := by
  classical
  rw [reachN_iff_path r nodes hsupp]
  constructor
  · rintro ⟨p, hp, hne, -⟩
    exact hp.transGen hne
  · intro h
    obtain ⟨p, hp, hne, hnd⟩ := exists_nodup_path h
    refine ⟨p, hp, hne, (List.subperm_of_subset hnd (fun x hx => ?_)).length_le⟩
    obtain ⟨y, hy⟩ := hp.mem_target x hx
    exact hsupp y x hy

theorem acyclicB_iff (r : α → α → Bool) (nodes : List α)
    (hsupp : ∀ a b, r a b = true → b ∈ nodes) :
    acyclicB r nodes = true ↔ Acyclic (fun x y => r x y = true) := by
  unfold acyclicB
  simp only [List.all_eq_true, Bool.not_eq_true']
  constructor
  · intro h a ha
    have ham : a ∈ nodes := by
      cases ha with
      | single h' => exact hsupp _ _ h'
      | tail _ h' => exact hsupp _ _ h'
    have := h a ham
    rw [(reachN_iff r nodes hsupp a a).mpr ha] at this
    cases this
  · intro h a _
    by_contra hne
    exact h a ((reachN_iff r nodes hsupp a a).mp (by simpa using hne))

end Maz
