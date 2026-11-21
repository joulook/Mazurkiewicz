import Mazurkiewicz.Induction.MaxStep

/-!
# Local states as future classes

`induction-popl`, `concepts.tex` sec:states: def:state, lem:state-wd,
lem:coarsest.

A sequential program is a function `p : List (Option Val) → Option Act`
(`P.step t` for a thread `t`); "undefined" is `none`, so "both undefined, or
both defined and equal" is equality in `Option Act`. No prefix-closed domain
is assumed (plan, decision D1): with values beyond an undefined point the
equivalence below can be finer than the paper's.
-/

namespace Trust

/-- A sequential program (def:program), without the domain conditions. -/
abbrev SeqProg := List (Option Val) → Option Act

/-- Future equivalence `u ≈_p u'` (def:state). -/
def FutEq (p : SeqProg) (u u' : List (Option Val)) : Prop := ∀ x, p (u ++ x) = p (u' ++ x)

/-- lem:state-wd: an equivalence relation. -/
theorem futEq_equivalence (p : SeqProg) : Equivalence (FutEq p) where
  refl := fun _ _ => rfl
  symm := fun h x => (h x).symm
  trans := fun h₁ h₂ x => (h₁ x).trans (h₂ x)

/-- lem:state-wd: a right congruence. -/
theorem FutEq.append {p : SeqProg} {u u' : List (Option Val)} (h : FutEq p u u')
    (v : List (Option Val)) : FutEq p (u ++ v) (u' ++ v) := by
  intro x
  rw [List.append_assoc, List.append_assoc]
  exact h (v ++ x)

def futSetoid (p : SeqProg) : Setoid (List (Option Val)) := ⟨FutEq p, futEq_equivalence p⟩

/-- The local states `St_p` (def:state). -/
def St (p : SeqProg) : Type := Quotient (futSetoid p)

namespace St

variable {p : SeqProg}

/-- The class `[u]_p`. -/
def mk (p : SeqProg) (u : List (Option Val)) : St p := Quotient.mk (futSetoid p) u

theorem mk_eq_mk {u u' : List (Option Val)} : mk p u = mk p u' ↔ FutEq p u u' :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- `act_p` (def:state); well defined by lem:state-wd. -/
def act (s : St p) : Option Act :=
  Quotient.liftOn s p (fun u u' h => by simpa using h [])

/-- `[u]_p · v` (def:state); well defined by lem:state-wd. -/
def app (s : St p) (v : Option Val) : St p :=
  Quotient.liftOn s (fun u => mk p (u ++ [v])) (fun _ _ h => mk_eq_mk.mpr (FutEq.append h [v]))

@[simp] theorem act_mk (u : List (Option Val)) : (mk p u).act = p u := rfl

@[simp] theorem app_mk (u : List (Option Val)) (v : Option Val) :
    (mk p u).app v = mk p (u ++ [v]) := rfl

/-- `s · v₁ ⋯ vₙ`. -/
def appList (s : St p) (x : List (Option Val)) : St p := x.foldl app s

@[simp] theorem appList_mk (u x : List (Option Val)) : (mk p u).appList x = mk p (u ++ x) := by
  unfold appList
  induction x generalizing u with
  | nil => simp
  | cons v x ih => rw [List.foldl_cons, app_mk, ih, List.append_assoc]; rfl

end St

/-- lem:coarsest: future equivalence is the coarsest deterministic notion of
state. -/
theorem futEq_of_state {p : SeqProg} {Z : Type*} (f : List (Option Val) → Z)
    (h1 : ∀ u u', f u = f u' → p u = p u')
    (h2 : ∀ u u', f u = f u' → ∀ v, f (u ++ [v]) = f (u' ++ [v]))
    {u u' : List (Option Val)} (h : f u = f u') : FutEq p u u' := by
  have key : ∀ x, f (u ++ x) = f (u' ++ x) := by
    intro x
    induction x using List.reverseRecOn with
    | nil => simpa using h
    | append_singleton x v ih =>
      rw [← List.append_assoc, ← List.append_assoc]
      exact h2 _ _ ih v
  exact fun x => h1 _ _ (key x)

end Trust
