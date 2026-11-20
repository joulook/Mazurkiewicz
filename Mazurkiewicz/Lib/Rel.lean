import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Max

/-!
# Relations: restriction, prefix-closed sets, acyclicity

Generic lemmas on binary relations used by the TruSt development.
They replace the part of `lib/AuxRel.v` and `trust/Util.v` of the Coq
development that the Lean representation still needs.
-/

namespace Maz

variable {α : Type*}

open Relation

/-- `r` has no cycle. (Hahn: `acyclic r`.) -/
def Acyclic (r : α → α → Prop) : Prop := ∀ a, ¬ TransGen r a a

/-- The restriction of `r` to the set `s`. (Hahn: `⦗s⦘ ⨾ r ⨾ ⦗s⦘`.) -/
def Restrict (r : α → α → Prop) (s : Set α) : α → α → Prop :=
  fun a b => r a b ∧ a ∈ s ∧ b ∈ s

/-- `s` is closed under `r`-predecessors. With `r = po ∪ rf` this is
"`s` is `porf`-prefix-closed" (paper, Section 3.1). -/
def PrefixClosed (r : α → α → Prop) (s : Set α) : Prop :=
  ∀ ⦃a b⦄, r a b → b ∈ s → a ∈ s

theorem Acyclic.mono {r r' : α → α → Prop} (h : ∀ a b, r' a b → r a b)
    (hr : Acyclic r) : Acyclic r' :=
  fun a ha => hr a (TransGen.mono h a a ha)

theorem Acyclic.irrefl {r : α → α → Prop} (hr : Acyclic r) (a : α) : ¬ r a a :=
  fun h => hr a (TransGen.single h)

theorem restrict_le (r : α → α → Prop) (s : Set α) :
    ∀ a b, Restrict r s a b → r a b :=
  fun _ _ h => h.1

theorem transGen_restrict_le {r : α → α → Prop} {s : Set α} {a b : α}
    (h : TransGen (Restrict r s) a b) : TransGen r a b :=
  TransGen.mono (restrict_le r s) a b h

theorem Acyclic.restrict {r : α → α → Prop} (hr : Acyclic r) (s : Set α) :
    Acyclic (Restrict r s) :=
  hr.mono (restrict_le r s)

/-- A prefix-closed set is closed under predecessors of the transitive closure. -/
theorem PrefixClosed.transGen {r : α → α → Prop} {s : Set α} (hs : PrefixClosed r s) :
    PrefixClosed (TransGen r) s := by
  intro a b hab hb
  induction hab using TransGen.head_induction_on with
  | single h => exact hs h hb
  | head h _ ih => exact hs h ih

/-- On a prefix-closed set, restricting first or closing first is the same:
a path that ends in `s` stays in `s`. -/
theorem transGen_restrict_of_prefixClosed {r : α → α → Prop} {s : Set α}
    (hs : PrefixClosed r s) {a b : α} (hab : TransGen r a b) (hb : b ∈ s) :
    TransGen (Restrict r s) a b := by
  induction hab using TransGen.head_induction_on with
  | single h => exact TransGen.single ⟨h, hs h hb, hb⟩
  | @head a c h hcb ih =>
    have hc : c ∈ s := hs.transGen hcb hb
    exact TransGen.head ⟨h, hs h hc, hc⟩ ih

theorem transGen_restrict_iff {r : α → α → Prop} {s : Set α}
    (hs : PrefixClosed r s) {a b : α} (hb : b ∈ s) :
    TransGen (Restrict r s) a b ↔ TransGen r a b :=
  ⟨transGen_restrict_le, fun h => transGen_restrict_of_prefixClosed hs h hb⟩

/-- A path that starts at `e` has a first edge that starts at `e`. -/
theorem exists_first_of_transGen {r : α → α → Prop} {a b : α} (h : TransGen r a b) :
    ∃ c, r a c := by
  induction h using TransGen.head_induction_on with
  | single h => exact ⟨_, h⟩
  | head h _ _ => exact ⟨_, h⟩

/-- Paths of a relation whose new edges all end in a sink `e`: a path is a
path of the old relation, or ends in `e`. -/
theorem transGen_of_sink {r r' : α → α → Prop} {e : α}
    (hsub : ∀ a b, r' a b → r a b ∨ b = e) (hsink : ∀ b, ¬ r' e b) {a b : α}
    (h : TransGen r' a b) : TransGen r a b ∨ b = e := by
  induction h with
  | single h =>
    rcases hsub _ _ h with h | h
    · exact Or.inl (TransGen.single h)
    · exact Or.inr h
  | @tail c d _ hcd ih =>
    rcases ih with ih | ih
    · rcases hsub _ _ hcd with h | h
      · exact Or.inl (ih.tail h)
      · exact Or.inr h
    · exact absurd hcd (ih ▸ hsink d)

/-- Adding edges into a sink keeps a relation acyclic: if every edge of `r'`
is an edge of `r` or ends in `e`, and `e` has no outgoing `r'`-edge, then `r'`
is acyclic when `r` is. This is the argument for maximal extensibility: the
new event has no outgoing edge. -/
theorem Acyclic.of_sink {r r' : α → α → Prop} {e : α} (hr : Acyclic r)
    (hsub : ∀ a b, r' a b → r a b ∨ b = e) (hsink : ∀ b, ¬ r' e b) :
    Acyclic r' := by
  -- a path of `r'` is a path of `r` or ends in `e`
  have key : ∀ a b, TransGen r' a b → TransGen r a b ∨ b = e := by
    intro a b h
    induction h with
    | single h =>
      rcases hsub _ _ h with h | h
      · exact Or.inl (TransGen.single h)
      · exact Or.inr h
    | @tail c d _ hcd ih =>
      rcases ih with ih | ih
      · rcases hsub _ _ hcd with h | h
        · exact Or.inl (ih.tail h)
        · exact Or.inr h
      · exact absurd hcd (ih ▸ hsink d)
  intro a ha
  rcases key a a ha with h | h
  · exact hr a h
  · subst h
    obtain ⟨c, hc⟩ := exists_first_of_transGen ha
    exact hsink c hc

theorem PrefixClosed.mono {r r' : α → α → Prop} {s : Set α} (h : ∀ a b, r' a b → r a b)
    (hs : PrefixClosed r s) : PrefixClosed r' s :=
  fun _ _ hab hb => hs (h _ _ hab) hb

theorem prefixClosed_union_iff {r r' : α → α → Prop} {s : Set α} :
    PrefixClosed (fun a b => r a b ∨ r' a b) s ↔ PrefixClosed r s ∧ PrefixClosed r' s :=
  ⟨fun h => ⟨fun _ _ hab hb => h (Or.inl hab) hb, fun _ _ hab hb => h (Or.inr hab) hb⟩,
   fun h _ _ hab hb => hab.elim (fun hab => h.1 hab hb) (fun hab => h.2 hab hb)⟩

theorem Restrict.mono_set {r : α → α → Prop} {s s' : Set α} (h : s ⊆ s') {a b : α}
    (hab : Restrict r s a b) : Restrict r s' a b :=
  ⟨hab.1, h hab.2.1, h hab.2.2⟩

/-- The converse of an acyclic relation is acyclic. (Coq: `acyclic_transp`.) -/
theorem Acyclic.swap {r : α → α → Prop} (hr : Acyclic r) : Acyclic (Function.swap r) :=
  fun a ha => hr a (Relation.transGen_swap.mp ha)

/-- Two strict total orders on `s` that never disagree are equal on `s`.
(Coq: `total_eqv`, `trust/Util.v`.) -/
theorem restrict_eq_of_total {r t : α → α → Prop} {s : Set α}
    (h₂ : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → t a b ∨ t b a)
    (h₁ : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b ∨ r b a)
    (hi₁ : ∀ a ∈ s, ¬ r a a) (hi₂ : ∀ a ∈ s, ¬ t a a)
    (hno : ∀ a ∈ s, ∀ b ∈ s, ¬ (r a b ∧ t b a)) :
    Restrict r s = Restrict t s := by
  funext a b
  apply propext
  constructor
  · rintro ⟨hab, ha, hb⟩
    have hne : a ≠ b := fun e => hi₁ a ha (e ▸ hab)
    rcases h₂ a ha b hb hne with h | h
    · exact ⟨h, ha, hb⟩
    · exact absurd ⟨hab, h⟩ (hno a ha b hb)
  · rintro ⟨hab, ha, hb⟩
    have hne : a ≠ b := fun e => hi₂ a ha (e ▸ hab)
    rcases h₁ a ha b hb hne with h | h
    · exact ⟨h, ha, hb⟩
    · exact absurd ⟨h, hab⟩ (hno b hb a ha)

/-! ### Termination by a bounded measure

(Coq: `trust/TerminateGen.v`, `r_min_ex` and `r_terminate`.) -/

/-- If a measure increases along `r` on the states reachable from `a` and is
bounded there, then some reachable state has no successor. -/
theorem exists_sink_of_bounded_measure {r : α → α → Prop} {a : α} (f : α → ℕ) (B : ℕ)
    (hinc : ∀ x y, ReflTransGen r a x → r x y → f x < f y)
    (hbd : ∀ x, ReflTransGen r a x → f x ≤ B) :
    ∃ x, ReflTransGen r a x ∧ ∀ y, ¬ r x y := by
  have key : ∀ k x, ReflTransGen r a x → B - f x ≤ k → ∃ y, ReflTransGen r a y ∧ ∀ z, ¬ r y z := by
    intro k
    induction k with
    | zero =>
      intro x hx hk
      refine ⟨x, hx, fun z hz => ?_⟩
      have h1 := hinc x z hx hz
      have h2 := hbd z (hx.tail hz)
      omega
    | succ k ih =>
      intro x hx hk
      by_cases h : ∃ z, r x z
      · obtain ⟨z, hz⟩ := h
        have h1 := hinc x z hx hz
        exact ih z (hx.tail hz) (by omega)
      · exact ⟨x, hx, fun z hz => h ⟨z, hz⟩⟩
  exact key (B - f a) a ReflTransGen.refl le_rfl

/-- A non-empty finite set has a maximal element for an acyclic relation: an
element with no successor in the set. -/
theorem Acyclic.exists_maximal {r : α → α → Prop} (hr : Acyclic r) (s : Finset α)
    (hs : s.Nonempty) : ∃ a ∈ s, ∀ b ∈ s, ¬ r a b := by
  classical
  -- minimize the number of elements of `s` reachable from `a`
  let f : α → ℕ := fun a => (s.filter (fun c => TransGen r a c)).card
  obtain ⟨a, ha, hmin⟩ := s.exists_min_image f hs
  refine ⟨a, ha, fun b hb hab => ?_⟩
  have hsub : s.filter (fun c => TransGen r b c) ⊂ s.filter (fun c => TransGen r a c) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro c hc
      have hc' := Finset.mem_filter.mp hc
      exact Finset.mem_filter.mpr ⟨hc'.1, TransGen.head hab hc'.2⟩
    · intro heq
      have hb' : b ∈ s.filter (fun c => TransGen r a c) :=
        Finset.mem_filter.mpr ⟨hb, TransGen.single hab⟩
      rw [← heq] at hb'
      exact hr b (Finset.mem_filter.mp hb').2
  have hlt : f b < f a := Finset.card_lt_card hsub
  have hle : f a ≤ f b := hmin b hb
  omega

/-! ### Examples -/

example : Acyclic (fun a b : ℕ => a < b) := by
  intro a h
  have key : ∀ x y : ℕ, TransGen (fun a b : ℕ => a < b) x y → x < y := by
    intro x y hxy
    induction hxy with
    | single h => exact h
    | tail _ h ih => exact Nat.lt_trans ih h
  exact Nat.lt_irrefl a (key a a h)

example : ¬ Acyclic (fun a b : ℕ => a = 0 ∧ b = 0) :=
  fun h => h 0 (TransGen.single ⟨rfl, rfl⟩)

example : Restrict (fun a b : ℕ => a < b) {n | n ≤ 2} 1 2 := ⟨by decide, by decide, by decide⟩
example : ¬ Restrict (fun a b : ℕ => a < b) {n | n ≤ 2} 1 3 := fun h => absurd h.2.2 (by decide)

example : PrefixClosed (fun a b : ℕ => a < b) {n | n ≤ 2} :=
  fun _ _ hab hb => Nat.le_trans (Nat.le_of_lt hab) hb
example : ¬ PrefixClosed (fun a b : ℕ => a < b) {n | 1 ≤ n} :=
  fun h => absurd (h (show (0 : ℕ) < 1 by decide) (show (1 : ℕ) ≤ 1 by decide)) (by decide)

end Maz
