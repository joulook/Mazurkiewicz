import Mathlib.Logic.Relation
import Mathlib.Data.List.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Tauto

/-!
# Paths of a relation

`Maz.Path r a p b`: `p` lists the states visited after `a`, in order, and `b`
is the last of them (`b = a` if `p` is empty). Used to state optimality:
two runs of the algorithm that end in the same graph are the same run.

Relation to Coq (`trust/Path.v`): there the list holds the intermediate states
and excludes the endpoint, so Coq's `Path r a q b` is `Maz.Path r a (q ++ [b]) b`
here, and a path of zero steps exists only here.
-/

namespace Maz

variable {α : Type*}

open Relation

/-- A path of `r` from `a` to `b` through the states `p` (`p` ends with `b`). -/
inductive Path (r : α → α → Prop) : α → List α → α → Prop
  | nil (a : α) : Path r a [] a
  | cons {a b c : α} {p : List α} : r a b → Path r b p c → Path r a (b :: p) c

theorem Path.reflTransGen {r : α → α → Prop} {a b : α} {p : List α} (h : Path r a p b) :
    ReflTransGen r a b := by
  induction h with
  | nil => exact ReflTransGen.refl
  | cons h _ ih => exact ReflTransGen.head h ih

theorem Path.of_reflTransGen {r : α → α → Prop} {a b : α} (h : ReflTransGen r a b) :
    ∃ p, Path r a p b := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨[], Path.nil b⟩
  | head h _ ih => obtain ⟨p, hp⟩ := ih; exact ⟨_ :: p, Path.cons h hp⟩

theorem Path.append {r : α → α → Prop} {a b c : α} {p q : List α}
    (h₁ : Path r a p b) (h₂ : Path r b q c) : Path r a (p ++ q) c := by
  induction h₁ with
  | nil => simpa using h₂
  | cons h _ ih => exact Path.cons h (ih h₂)

theorem Path.snoc {r : α → α → Prop} {a b c : α} {p : List α}
    (h₁ : Path r a p b) (h₂ : r b c) : Path r a (p ++ [c]) c :=
  h₁.append (Path.cons h₂ (Path.nil c))

/-- A non-empty path ends with a last step. -/
theorem Path.exists_snoc {r : α → α → Prop} {a c : α} {p : List α}
    (h : Path r a p c) (hp : p ≠ []) :
    ∃ q b, p = q ++ [c] ∧ Path r a q b ∧ r b c := by
  induction h with
  | nil => exact absurd rfl hp
  | @cons a b c p hab hbc ih =>
    by_cases hp' : p = []
    · subst hp'
      cases hbc
      exact ⟨[], a, rfl, Path.nil a, hab⟩
    · obtain ⟨q, d, rfl, hq, hd⟩ := ih hp'
      exact ⟨b :: q, d, rfl, Path.cons hab hq, hd⟩

theorem Path.nil_iff {r : α → α → Prop} {a b : α} : Path r a [] b ↔ a = b :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ Path.nil a⟩

/-- The states of a path are reachable from its start and reach its end.
(Coq: `path_r_str`.) -/
theorem Path.mem_reflTransGen {r : α → α → Prop} {a b c : α} {p : List α}
    (h : Path r a p b) (hc : c ∈ p) : ReflTransGen r a c ∧ ReflTransGen r c b := by
  induction h with
  | nil => simp at hc
  | @cons a b' d p hab hbd ih =>
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨ReflTransGen.single hab, hbd.reflTransGen⟩
    · exact ⟨ReflTransGen.head hab (ih hc).1, (ih hc).2⟩

/-- Splitting a path at one of its states. (Coq: `cat_path`, `sub_path`.) -/
theorem Path.split {r : α → α → Prop} {a b c : α} {p q : List α}
    (h : Path r a (p ++ c :: q) b) : Path r a (p ++ [c]) c ∧ Path r c q b := by
  induction p generalizing a with
  | nil =>
    cases h with
    | cons hac hcb => exact ⟨Path.cons hac (Path.nil c), hcb⟩
  | cons d p ih =>
    cases h with
    | cons had hdb => exact ⟨Path.cons had (ih hdb).1, (ih hdb).2⟩

/-- The part of a path after one of its states. (Coq: `sub_path`.) -/
theorem Path.suffix {r : α → α → Prop} {a b c : α} {p q s : List α}
    (h : Path r a p b) (hp : a :: p = q ++ c :: s) : Path r c s b := by
  cases q with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact h
  | cons d q =>
    simp only [List.cons_append, List.cons.injEq] at hp
    obtain ⟨_, rfl⟩ := hp
    exact h.split.2

/-- Consecutive states of a path are related. (Coq: `path_neigb_rel`.) -/
theorem Path.adj {r : α → α → Prop} {a b x y : α} {p p₁ p₂ : List α}
    (h : Path r a p b) (hp : a :: p = p₁ ++ x :: y :: p₂) : r x y := by
  induction h generalizing p₁ with
  | nil =>
    cases p₁ with
    | nil => simp at hp
    | cons _ _ => simp at hp
  | @cons a b' d p hab hbd ih =>
    cases p₁ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hp
      obtain ⟨rfl, rfl, _⟩ := hp
      exact hab
    | cons e p₁ =>
      simp only [List.cons_append, List.cons.injEq] at hp
      exact ih hp.2

/-- A path from a state without `P` to a state with `P` crosses into `P` for a
last time. (Coq: `path_cont`.) -/
theorem Path.exists_cross {r : α → α → Prop} {P : α → Prop} {a b : α} {p : List α}
    (h : Path r a p b) (ha : ∃ z ∈ a :: p, ¬ P z) (hb : P b) :
    ∃ q x y s, a :: p = q ++ x :: y :: s ∧ r x y ∧ ¬ P x ∧ ∀ z ∈ y :: s, P z := by
  induction h with
  | nil =>
    obtain ⟨z, hz, hPz⟩ := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    exact absurd (hz ▸ hb) hPz
  | @cons a b' d p hab hbd ih =>
    by_cases hlater : ∃ z ∈ b' :: p, ¬ P z
    · obtain ⟨q, x, y, s, hq, hxy, hx, hs⟩ := ih hlater hb
      exact ⟨a :: q, x, y, s, by rw [hq]; rfl, hxy, hx, hs⟩
    · have hall : ∀ z ∈ b' :: p, P z := fun z hz => by
        by_contra hPz; exact hlater ⟨z, hz, hPz⟩
      obtain ⟨z, hz, hPz⟩ := ha
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨[], z, b', p, rfl, hab, hPz, hall⟩
      · exact absurd (hall z hz) hPz

/-- The reversed path, for the converse relation. (Coq: `Path_transp`.) -/
theorem Path.reverse {r : α → α → Prop} {a b : α} {p : List α} (h : Path r a p b) :
    Path (Function.swap r) b (a :: p).reverse.tail a := by
  induction h with
  | nil => exact Path.nil _
  | @cons a b' d p hab hbd ih =>
    have e : (a :: b' :: p).reverse.tail = (b' :: p).reverse.tail ++ [a] := by
      rw [List.reverse_cons, List.tail_append_of_ne_nil (by simp)]
    rw [e]
    exact ih.snoc hab

/-- A measure that increases along `r` on the reachable states and is bounded
by `B` there bounds the length of every path. (Coq: `r_terminate`.) -/
theorem Path.length_le_of_bounded_measure {r : α → α → Prop} {a₀ : α} (f : α → ℕ) (B : ℕ)
    (hinc : ∀ x y, ReflTransGen r a₀ x → r x y → f x < f y)
    (hbd : ∀ x, ReflTransGen r a₀ x → f x ≤ B)
    {p : List α} {b : α} (h : Path r a₀ p b) : p.length ≤ B := by
  have key : ∀ a p b, ReflTransGen r a₀ a → Path r a p b → f a + p.length ≤ f b := by
    intro a p b ha h
    induction h with
    | nil => simp
    | @cons a b' d p hab _ ih =>
      have h1 := hinc a b' ha hab
      have h2 := ih (ha.tail hab)
      simp only [List.length_cons]
      omega
  have h1 := key a₀ p b ReflTransGen.refl h
  have h2 := hbd b h.reflTransGen
  omega

/-! ### Examples -/

example : Path (fun a b : ℕ => b = a + 1) 0 [] 0 := Path.nil 0
example : Path (fun a b : ℕ => b = a + 1) 0 [1, 2] 2 :=
  Path.cons rfl (Path.cons rfl (Path.nil 2))
example : ¬ Path (fun a b : ℕ => b = a + 1) 0 [2] 2 := by
  intro h
  cases h with
  | cons h _ => exact absurd h (by decide)

end Maz
