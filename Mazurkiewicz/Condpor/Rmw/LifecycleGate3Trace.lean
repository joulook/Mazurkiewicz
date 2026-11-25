import Mazurkiewicz.Condpor.Rmw.LifecycleSem

/-!
# Gate clause 3, part 1: Mazurkiewicz equivalence on lists of occurrences (LC2-c)

Pure list facts about `MEquiv` (the equivalence closure of `Swap`), independent of the
machine:

* `mequiv_iff_rtg`: since `Swap` is symmetric, `MEquiv` is the reflexive-transitive closure of
  `Swap`;
* congruences (`MEquiv.cons`, `MEquiv.append_left`), `MEquiv.perm`, `MEquiv.length_eq`;
* `mequiv_move`: a letter independent of every letter of `y₁` moves in front of `y₁`;
* `mequiv_cons_split` (Levi's lemma for one letter): if `a :: x` is equivalent to `y`, then
  `y = y₁ ++ a :: y₂` with every letter of `y₁` independent of `a` and `x` equivalent to
  `y₁ ++ y₂`. The intermediate lists of the equivalence are arbitrary lists, not runs.
-/

namespace Condpor

namespace Life

namespace Sem

open Relation

theorem Swap.symm' {x y : List Occ} (h : Swap x y) : Swap y x := by
  cases h with
  | swap u v a b hd => exact Swap.swap u v b a (fun h => hd h.symm)

theorem rtg_swap_symm {x y : List Occ} (h : ReflTransGen Swap x y) : ReflTransGen Swap y x := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ h ih => exact ReflTransGen.head h.symm' ih

/-- `MEquiv` is the reflexive-transitive closure of `Swap`. -/
theorem mequiv_iff_rtg {x y : List Occ} : MEquiv x y ↔ ReflTransGen Swap x y := by
  constructor
  · intro h
    induction h with
    | rel _ _ h => exact ReflTransGen.single h
    | refl => exact ReflTransGen.refl
    | symm _ _ _ ih => exact rtg_swap_symm ih
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    induction h with
    | refl => exact EqvGen.refl _
    | tail _ h ih => exact EqvGen.trans _ _ _ ih (EqvGen.rel _ _ h)

theorem MEquiv.refl' (x : List Occ) : MEquiv x x := EqvGen.refl _

theorem MEquiv.symm' {x y : List Occ} (h : MEquiv x y) : MEquiv y x := EqvGen.symm _ _ h

theorem MEquiv.trans' {x y z : List Occ} (h1 : MEquiv x y) (h2 : MEquiv y z) : MEquiv x z :=
  EqvGen.trans _ _ _ h1 h2

theorem mequiv_swap {a b : Occ} (h : ¬ Dep a b) (u v : List Occ) :
    MEquiv (u ++ a :: b :: v) (u ++ b :: a :: v) := EqvGen.rel _ _ (Swap.swap u v a b h)

/-- A map of lists that sends swaps to swaps preserves `MEquiv`. -/
theorem MEquiv.map {f : List Occ → List Occ} (hf : ∀ x y, Swap x y → Swap (f x) (f y))
    {x y : List Occ} (h : MEquiv x y) : MEquiv (f x) (f y) := by
  induction h with
  | rel _ _ h => exact EqvGen.rel _ _ (hf _ _ h)
  | refl => exact EqvGen.refl _
  | symm _ _ _ ih => exact EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact EqvGen.trans _ _ _ ih1 ih2

theorem MEquiv.append_left (p : List Occ) {x y : List Occ} (h : MEquiv x y) :
    MEquiv (p ++ x) (p ++ y) := by
  refine MEquiv.map (f := fun l => p ++ l) ?_ h
  intro x y hs
  cases hs with
  | swap u v a b hd =>
    have := Swap.swap (p ++ u) v a b hd
    simpa only [List.append_assoc] using this

theorem MEquiv.cons (a : Occ) {x y : List Occ} (h : MEquiv x y) : MEquiv (a :: x) (a :: y) :=
  MEquiv.append_left [a] h

theorem Swap.perm {x y : List Occ} (h : Swap x y) : x.Perm y := by
  cases h with
  | swap u v a b _ => exact List.Perm.append_left u (List.Perm.swap b a v)

theorem MEquiv.perm {x y : List Occ} (h : MEquiv x y) : x.Perm y := by
  induction h with
  | rel _ _ h => exact h.perm
  | refl => exact List.Perm.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem MEquiv.length_eq {x y : List Occ} (h : MEquiv x y) : x.length = y.length :=
  h.perm.length_eq

theorem MEquiv.eq_nil {x : List Occ} (h : MEquiv [] x) : x = [] :=
  List.eq_nil_of_length_eq_zero h.length_eq.symm

theorem Swap.split {z y : List Occ} (h : Swap z y) :
    ∃ u v c d, ¬ Dep c d ∧ z = u ++ c :: d :: v ∧ y = u ++ d :: c :: v := by
  cases h with
  | swap u v c d hcd => exact ⟨u, v, c, d, hcd, rfl, rfl⟩

/-- **Moving a letter forward** over letters independent of it. -/
theorem mequiv_move {a : Occ} {y₁ : List Occ} (h : ∀ b ∈ y₁, ¬ Dep a b) (y₂ : List Occ) :
    MEquiv (y₁ ++ a :: y₂) (a :: (y₁ ++ y₂)) := by
  induction y₁ with
  | nil => exact MEquiv.refl' _
  | cons b y₁ ih =>
    have h1 := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    have hb : ¬ Dep b a := fun hd => h b List.mem_cons_self hd.symm
    have h2 := mequiv_swap hb [] (y₁ ++ y₂)
    simp only [List.nil_append] at h2
    exact (h1.cons b).trans' (by simpa only [List.cons_append] using h2)

/-- **Levi's lemma for one letter.** -/
theorem mequiv_cons_split {a : Occ} {x y : List Occ} (h : MEquiv (a :: x) y) :
    ∃ y₁ y₂, y = y₁ ++ a :: y₂ ∧ (∀ b ∈ y₁, ¬ Dep a b) ∧ MEquiv x (y₁ ++ y₂) := by
  rw [mequiv_iff_rtg] at h
  induction h with
  | refl => exact ⟨[], x, rfl, by simp, MEquiv.refl' _⟩
  | tail _ hs ih =>
    obtain ⟨y₁, y₂, rfl, hind, hx⟩ := ih
    obtain ⟨u, v, c, d, hcd, hz', rfl⟩ := hs.split
    · rw [List.append_eq_append_iff] at hz'
      rcases hz' with ⟨a', rfl, h2⟩ | ⟨c', rfl, h2⟩
      · rw [List.cons_eq_append_iff] at h2
        rcases h2 with ⟨rfl, h3⟩ | ⟨w, rfl, rfl⟩
        · simp only [List.cons.injEq] at h3
          obtain ⟨rfl, rfl⟩ := h3
          refine ⟨y₁ ++ [d], v, by simp, ?_, by simpa using hx⟩
          intro b hb
          rcases List.mem_append.mp hb with hb | hb
          · exact hind b hb
          · rw [List.mem_singleton.mp hb]; exact hcd
        · refine ⟨y₁, w ++ d :: c :: v, by simp, hind, ?_⟩
          refine hx.trans' ?_
          have := mequiv_swap hcd (y₁ ++ w) v
          simpa only [List.append_assoc, List.cons_append] using this
      · rw [List.cons_eq_append_iff] at h2
        rcases h2 with ⟨rfl, h3⟩ | ⟨c'', rfl, h3⟩
        · simp only [List.cons.injEq] at h3
          obtain ⟨rfl, rfl⟩ := h3
          refine ⟨u ++ [d], v, by simp, ?_, by simpa using hx⟩
          intro b hb
          rcases List.mem_append.mp hb with hb | hb
          · exact hind b (by simpa using hb)
          · rw [List.mem_singleton.mp hb]; exact hcd
        · rw [List.cons_eq_append_iff] at h3
          rcases h3 with ⟨rfl, h4⟩ | ⟨w, rfl, rfl⟩
          · simp only [List.cons.injEq] at h4
            obtain ⟨rfl, rfl⟩ := h4
            refine ⟨u, c :: y₂, by simp, ?_, by simpa using hx⟩
            intro b hb
            exact hind b (by simp [hb])
          · refine ⟨u ++ d :: c :: w, y₂, by simp, ?_, ?_⟩
            · intro b hb
              apply hind b
              simp only [List.mem_append, List.mem_cons] at hb ⊢
              tauto
            · refine hx.trans' ?_
              have := mequiv_swap hcd u (w ++ y₂)
              simpa only [List.append_assoc, List.cons_append] using this

end Sem

end Life

end Condpor
