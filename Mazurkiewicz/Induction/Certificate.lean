import Mazurkiewicz.Induction.Compose

/-!
# Summaries and certificates

`induction-popl`, `concepts.tex` sec:certificates: def:certificate,
thm:soundness, for plain programs.

How the text is read here.

* The alphabet `Tid × C_P` is `Tid` (no choice actions). `δ` is a function to
  `Option Q`. The operation `a^{𝔾_P}` is `apT P t` (`Induction/MaxStep.lean`),
  undefined outside `Exec_SC(P)`.
* The paper's `Q` is a finite set. `Certificate` allows any type of
  summaries; the paper's certificates are the instances with `[Finite Q]`.
  thm:soundness does not use finiteness.
* `δ̂` is `Certificate.run`; the head of a term is its last symbol.
* rem:readings (tree automata, Park induction) is not formalised.
-/

namespace Trust

open Program

/-- A certificate for `P` (def:certificate), with (C1) and (C2). -/
structure Certificate (P : Program) (Q : Type) where
  /-- the initial summary `q₀` -/
  q₀ : Q
  /-- the transition function `δ` -/
  δ : Q → Tid → Option Q
  /-- the concretization `γ` -/
  γ : Q → Set Graph
  /-- (C1) initiation -/
  init : Graph.init P.mem ∈ γ q₀
  /-- (C2) consecution -/
  cons : ∀ q t G, G ∈ γ q → ∀ G', apT P t G = some G' → ∃ q', δ q t = some q' ∧ G' ∈ γ q'

namespace Certificate

variable {P : Program} {Q : Type}

/-- `δ̂` (def:certificate). -/
def run (C : Certificate P Q) : List Tid → Option Q
  | [] => some C.q₀
  | t :: τ => (C.run τ).bind (fun q => C.δ q t)

/-- (C3): a certificate of safety for `Bad`. -/
def IsSafetyFor (C : Certificate P Q) (Bad : Set Graph) : Prop := ∀ q, Disjoint (C.γ q) Bad

/-! ### Statements -/

/-- thm:soundness, first part: for a valid term, `δ̂` is defined and the value
of the term is in its concretization. -/
theorem run_valt (C : Certificate P Q) {τ : List Tid} {G : Graph} (h : valt P τ = some G) :
    ∃ q, C.run τ = some q ∧ G ∈ C.γ q := by
  induction τ generalizing G with
  | nil =>
    cases h
    exact ⟨C.q₀, rfl, C.init⟩
  | cons t τ ih =>
    rw [valt_cons] at h
    obtain ⟨G₀, hG₀, hstep⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨q, hq, hmem⟩ := ih hG₀
    obtain ⟨q', hq', hmem'⟩ := C.cons q t G₀ hmem G hstep
    refine ⟨q', ?_, hmem'⟩
    change (C.run τ).bind (fun q => C.δ q t) = some q'
    rw [hq]
    exact hq'

/-- thm:soundness, second part: the reachable graphs are covered by the
summaries. -/
theorem greach_subset (C : Certificate P Q) {G : Graph} (h : GReach P SC G) :
    ∃ q, G ∈ C.γ q := by
  obtain ⟨τ, hτ⟩ := valt_range.mpr h
  obtain ⟨q, -, hq⟩ := C.run_valt hτ
  exact ⟨q, hq⟩

/-- thm:soundness, third part: a certificate of safety proves safety. -/
theorem safe (C : Certificate P Q) {Bad : Set Graph} (h : C.IsSafetyFor Bad) :
    Safe P SC Bad := by
  intro G hG
  obtain ⟨q, hq⟩ := C.greach_subset hG
  exact Set.disjoint_left.mp (h q) hq

end Certificate

end Trust
