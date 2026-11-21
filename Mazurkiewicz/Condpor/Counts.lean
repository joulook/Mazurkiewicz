import Mazurkiewicz.Condpor.ExitC
import Mathlib.Data.List.Permutation

/-!
# The counts of Section 2.2.1 of the paper

"Naively, this program has 36 behaviors. There are 4! = 24 ways the accesses
to `x` and `y` can be interleaved. For half of those, the read of `y` reads 0,
whereas for the other half it reads the written symbolic value, which … may or
may not be 42."

The program is `w+sw+r+r` (Fig. 1). The statement here is about the orderings
of its four accesses, as lists; this development has no interleaving
semantics to which the orderings could be tied (the executions of the program
are the six graphs of `fig1_six`).

* `mem_orderings`, `orderings_nodup`, `orderings_length`: the list `orderings`
  has every permutation of the four accesses once, and there are 24;
* `orderings_read_first`: in 12 of them the read of `y` is before the write of
  `y` (it reads 0), in the other 12 after it;
* `behaviours_total`: one behaviour for each ordering of the first kind and
  two (`s = 42` or not) for each of the second: 36.
-/

namespace Condpor

/-- The four accesses of `w+sw+r+r`: the write of `x`, the write of `y`, the
read of `y`, the read of `x`. -/
inductive Acc
  | wx | wy | ry | rx
  deriving DecidableEq, Repr

/-- All ways to insert `a` into a list. -/
def insertions {α : Type} (a : α) : List α → List (List α)
  | [] => [[a]]
  | b :: l => (a :: b :: l) :: (insertions a l).map (b :: ·)

/-- The orderings of a list, computed by structural recursion. -/
def perms {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: l => (perms l).flatMap (insertions a)

/-- The four accesses, in some order. -/
def accs : List Acc := [Acc.wx, Acc.wy, Acc.ry, Acc.rx]

/-- The orderings of the four accesses. -/
def orderings : List (List Acc) := perms accs

/-- The read of `y` comes before the write of `y`. -/
def readFirst (l : List Acc) : Bool := l.idxOf Acc.ry < l.idxOf Acc.wy

/-- The number of behaviours of an ordering: one if the read of `y` reads the
initial value, two (the symbolic value is 42 or not) otherwise. -/
def behaviours (l : List Acc) : ℕ := if readFirst l then 1 else 2

theorem orderings_length : orderings.length = 24 := by decide

theorem orderings_nodup : orderings.Nodup := by decide

/-- `orderings` lists exactly the permutations of the four accesses. -/
theorem mem_orderings (l : List Acc) : l ∈ orderings ↔ l.Perm accs := by
  have h : ∀ l ∈ orderings, l.Perm accs := by decide
  refine ⟨h l, fun hl => ?_⟩
  have hsub : orderings.toFinset ⊆ accs.permutations.toFinset := by
    intro x hx
    exact List.mem_toFinset.mpr (List.mem_permutations.mpr (h x (List.mem_toFinset.mp hx)))
  have hnd : accs.Nodup := by decide
  have hcard : accs.permutations.toFinset.card ≤ orderings.toFinset.card := by
    rw [List.toFinset_card_of_nodup orderings_nodup,
      List.toFinset_card_of_nodup (List.nodup_permutations accs hnd), orderings_length,
      List.length_permutations]
    decide
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have : l ∈ accs.permutations.toFinset :=
    List.mem_toFinset.mpr (List.mem_permutations.mpr hl)
  rw [← heq] at this
  exact List.mem_toFinset.mp this

theorem orderings_read_first :
    (orderings.filter readFirst).length = 12 ∧
      (orderings.filter (fun l => !readFirst l)).length = 12 := by decide

theorem behaviours_total : (orderings.map behaviours).sum = 36 := by decide

/-! ### Fig. 1 once more -/

/-- The full executions of `w+sw+r+r`, read by the sources of their two reads
and the outcome of the constraint, are the six graphs of Fig. 1, each once. -/
theorem fig1_perm : ((exploreC fig1 eqOracleSe 3).map fig1Sig).Perm fig1Expected := by
  decide +kernel

end Condpor
