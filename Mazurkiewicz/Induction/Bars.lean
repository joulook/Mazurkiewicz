import Mazurkiewicz.Induction.KInductive

/-!
# Bars

`induction-popl`, `cuts.tex`, sec:bars: def:bar, def:barinductive,
thm:barsound, prop:kbar, rem:bar-tight, for plain programs under SC.

How the text is read here.

* The witness form of `KInductive.lean`: for a graph `G` with `α G = b`, the
  program `Q_b` is `P.residual G.trace G.memOf`, and `b ⊙ H` is
  `α (G.comp H)`. The conditions are asked for every `G ∈ Exec_SC(P)` with
  `α G ∈ B`; no compositionality is assumed.
* A bar family is `Bar : A → Set Graph`, any sets; the paper's bar is the
  part of `Bar b` in `Reach_SC(Q_b)`. `boundary` and `DepthLe` are relative to
  the reachable graphs of a program.
* `BarInductive` is def:barinductive, with the condition `G_0^b ∉ Bar_b` of
  def:bar as part of it.
* `BarInductivePath` is weaker (not in the paper): (B2) only at the first
  graph in the bar of a derivation by maximal steps from `G_0^b`, (B3) only
  at the end of a derivation all of whose graphs are outside the bar.
  thm:barsound is proved for it (`barsound_path`); the proof splits on
  whether some graph of the derivation is in the bar. The paper's proof
  applies (B3) whenever the last graph is outside the bar.
-/

namespace Trust

open Program

variable {P : Program} {A : Type}

/-- The boundary `∂X` of a bar (def:bar), in the program `P'`. -/
def boundary (P' : Program) (X : Set Graph) : Set Graph :=
  {H | H ∈ X ∧ GReach P' SC H ∧ ∃ H' t, GReach P' SC H' ∧ H' ∉ X ∧ MStep P' t H' H}

/-- Depth at most `N` (def:bar). -/
def DepthLe (P' : Program) (X : Set Graph) (N : ℕ) : Prop :=
  ∀ H, GReach P' SC H → N + 1 ≤ H.size → H ∈ X

/-- `X` is closed under extension among the reachable graphs (rem:bar-tight). -/
def BarExtClosed (P' : Program) (X : Set Graph) : Prop :=
  ∀ H H', GReach P' SC H → GReach P' SC H' → H ∈ X → H.IsPrefixOf H' → H' ∈ X

/-- The last graph of a derivation by maximal steps from the initial graph
all of whose graphs are outside `X`. -/
inductive OutsidePath (P' : Program) (X : Set Graph) : Graph → Prop
  | init : Graph.init P'.mem ∉ X → OutsidePath P' X (Graph.init P'.mem)
  | step {H H' : Graph} {t : Tid} :
      OutsidePath P' X H → MStep P' t H H' → H' ∉ X → OutsidePath P' X H'

namespace Abstraction

variable (Abs : Abstraction P A)

/-- A bar-inductive set (def:barinductive, with `G_0^b ∉ Bar_b` of def:bar). -/
def BarInductive (Abad B : Set A) (Bar : A → Set Graph) : Prop :=
  Abs.α (Graph.init P.mem) ∈ B ∧ ∀ G, ExecSC P G → Abs.α G ∈ B →
    Graph.init G.memOf ∉ Bar (Abs.α G) ∧
    (∀ H ∈ boundary (P.residual G.trace G.memOf) (Bar (Abs.α G)), Abs.α (G.comp H) ∈ B) ∧
    (∀ H, GReach (P.residual G.trace G.memOf) SC H → H ∉ Bar (Abs.α G) →
      Abs.α (G.comp H) ∉ Abad)

/-- The path form: the conditions along the derivations that stay outside
the bar. -/
def BarInductivePath (Abad B : Set A) (Bar : A → Set Graph) : Prop :=
  Abs.α (Graph.init P.mem) ∈ B ∧ ∀ G, ExecSC P G → Abs.α G ∈ B →
    Graph.init G.memOf ∉ Bar (Abs.α G) ∧
    (∀ H H' t, OutsidePath (P.residual G.trace G.memOf) (Bar (Abs.α G)) H →
      MStep (P.residual G.trace G.memOf) t H H' → H' ∈ Bar (Abs.α G) →
      Abs.α (G.comp H') ∈ B) ∧
    (∀ H, OutsidePath (P.residual G.trace G.memOf) (Bar (Abs.α G)) H →
      Abs.α (G.comp H) ∉ Abad)

end Abstraction

/-! ### Derivations -/

/-- The initial graph is in `Exec_SC`. -/
theorem execSC_init (P' : Program) : ExecSC P' (Graph.init P'.mem) :=
  greach_iff.mp Relation.ReflTransGen.refl

/-- A derivation by maximal steps from the initial graph ends in a reachable
graph. -/
theorem MSteps.greach {P' : Program} {τ : List Tid} {H : Graph}
    (h : MSteps P' τ (Graph.init P'.mem) H) : GReach P' SC H :=
  greach_iff.mpr (MSteps.execSC (execSC_init P') h)

theorem OutsidePath.greach {P' : Program} {X : Set Graph} {H : Graph}
    (h : OutsidePath P' X H) : GReach P' SC H := by
  induction h with
  | init _ => exact Relation.ReflTransGen.refl
  | step _ hs _ _ => exact greach_iff.mpr hs.execSC_right

theorem OutsidePath.not_mem {P' : Program} {X : Set Graph} {H : Graph}
    (h : OutsidePath P' X H) : H ∉ X := by
  cases h with
  | init h0 => exact h0
  | step _ _ h' => exact h'

/-- A derivation from the initial graph stays outside `X`, or it has a first
graph in `X`. -/
theorem MSteps.outside_or_enter {P' : Program} {X : Set Graph}
    (h0 : Graph.init P'.mem ∉ X) {τ : List Tid} {H : Graph}
    (h : MSteps P' τ (Graph.init P'.mem) H) :
    OutsidePath P' X H ∨ ∃ τ₁ τ₂ H₁ H₂ t, τ = τ₂ ++ t :: τ₁ ∧ OutsidePath P' X H₁ ∧
      MStep P' t H₁ H₂ ∧ H₂ ∈ X ∧ MSteps P' τ₂ H₂ H := by
  induction τ generalizing H with
  | nil =>
    have : H = Graph.init P'.mem := h
    subst this
    exact Or.inl (.init h0)
  | cons t τ ih =>
    obtain ⟨Hm, hm, hs⟩ := h
    rcases ih hm with hout | ⟨τ₁, τ₂, H₁, H₂, t', rfl, hout, hs', hX, hrest⟩
    · by_cases hH : H ∈ X
      · exact Or.inr ⟨τ, [], Hm, H, t, rfl, hout, hs, hH, rfl⟩
      · exact Or.inl (.step hout hs hH)
    · exact Or.inr ⟨τ₁, t :: τ₂, H₁, H₂, t', rfl, hout, hs', hX, Hm, hrest, hs⟩

/-- prop:compose (2) along a derivation: a derivation of `P` from `G` is a
derivation of the residual program from its initial graph. -/
theorem msteps_resid {G G' : Graph} {τ : List Tid} (hG : ExecSC P G) (h : MSteps P τ G G') :
    ∃ H, MSteps (P.residual G.trace G.memOf) τ (Graph.init G.memOf) H ∧ G' = G.comp H := by
  induction τ generalizing G' with
  | nil =>
    refine ⟨Graph.init G.memOf, rfl, ?_⟩
    rw [Graph.comp_init hG.1]
    exact h
  | cons t τ ih =>
    obtain ⟨G₁, h₁, hs⟩ := h
    obtain ⟨H₁, hH₁, rfl⟩ := ih h₁
    have hH₁E : ExecSC (P.residual G.trace G.memOf) H₁ :=
      MSteps.execSC (execSC_init (P.residual G.trace G.memOf)) hH₁
    obtain ⟨H', hs', rfl⟩ := mstep_comp_inv hG hH₁E hs
    exact ⟨H', ⟨H₁, hH₁, hs'⟩, rfl⟩

/-- prop:compose (1) along a derivation. -/
theorem msteps_comp {G H H' : Graph} {τ : List Tid} (hG : ExecSC P G)
    (hH : GReach (P.residual G.trace G.memOf) SC H)
    (h : MSteps (P.residual G.trace G.memOf) τ H H') : MSteps P τ (G.comp H) (G.comp H') := by
  induction τ generalizing H' with
  | nil =>
    have : H' = H := h
    rw [this]
    rfl
  | cons t τ ih =>
    obtain ⟨H₁, h₁, hs⟩ := h
    have hH₁ : GReach (P.residual G.trace G.memOf) SC H₁ :=
      greach_iff.mpr (MSteps.execSC (greach_iff.mp hH) h₁)
    exact ⟨G.comp H₁, ih h₁, MStep.comp hG (greach_iff.mp (greach_comp hG hH₁).1) hs⟩

/-! ### thm:barsound -/

namespace Abstraction

variable (Abs : Abstraction P A)

/-- thm:barsound, for the path form. -/
theorem barsound_path {Bad : Set Graph} {Abad B : Set A} {Bar : A → Set Graph}
    (hdet : Abs.Determines Bad Abad) (hB : Abs.BarInductivePath Abad B Bar) :
    Safe P SC Bad := by
  have key : ∀ n (τ : List Tid), τ.length = n → ∀ G G', ExecSC P G → Abs.α G ∈ B →
      MSteps P τ G G' → Abs.α G' ∉ Abad := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro τ hlen G G' hG hα h
      obtain ⟨h0, h2, h3⟩ := hB.2 G hG hα
      obtain ⟨H, hH, rfl⟩ := msteps_resid hG h
      rcases MSteps.outside_or_enter (P' := P.residual G.trace G.memOf) h0 hH with
        hout | ⟨τ₁, τ₂, H₁, H₂, t, rfl, hout, hs, hX, hrest⟩
      · exact h3 H hout
      · have hH₂ : GReach (P.residual G.trace G.memOf) SC H₂ := greach_iff.mpr hs.execSC_right
        have hG₂ : ExecSC P (G.comp H₂) := greach_iff.mp (greach_comp hG hH₂).1
        refine ih τ₂.length ?_ τ₂ rfl (G.comp H₂) _ hG₂ (h2 H₁ H₂ t hout hs hX)
          (msteps_comp hG hH₂ hrest)
        rw [← hlen, List.length_append, List.length_cons]
        omega
  intro G' hG' hbad
  obtain ⟨τ, -, hτ⟩ := greach_iff_msteps.mp hG'
  exact key _ τ rfl _ G' (execSC_init P) hB.1 hτ ((hdet G' (greach_iff.mp hG')).mp hbad)

/-- A bar-inductive set satisfies the path form. -/
theorem BarInductive.path {Abad B : Set A} {Bar : A → Set Graph}
    (hB : Abs.BarInductive Abad B Bar) : Abs.BarInductivePath Abad B Bar := by
  refine ⟨hB.1, fun G hG hα => ?_⟩
  obtain ⟨h0, h2, h3⟩ := hB.2 G hG hα
  refine ⟨h0, fun H H' t hout hs hX => ?_, fun H hout => h3 H hout.greach hout.not_mem⟩
  exact h2 H' ⟨hX, greach_iff.mpr hs.execSC_right, H, t, hout.greach, hout.not_mem, hs⟩

/-- thm:barsound. -/
theorem barsound {Bad : Set Graph} {Abad B : Set A} {Bar : A → Set Graph}
    (hdet : Abs.Determines Bad Abad) (hB : Abs.BarInductive Abad B Bar) : Safe P SC Bad :=
  Abs.barsound_path hdet (BarInductive.path Abs hB)

end Abstraction

namespace Abstraction

variable (Abs : Abstraction P A)

/-- With a compositional abstraction, def:barinductive may be checked on one
graph for every realised `b ∈ B` (as lem:representatives). -/
theorem barInductive_iff_representatives (hcomp : Abs.Compositional) {Abad B : Set A}
    {Bar : A → Set Graph} :
    Abs.BarInductive Abad B Bar ↔
      Abs.α (Graph.init P.mem) ∈ B ∧ ∀ b ∈ B, Abs.Realised b → ∃ G, ExecSC P G ∧ Abs.α G = b ∧
        Graph.init G.memOf ∉ Bar b ∧
        (∀ H ∈ boundary (P.residual G.trace G.memOf) (Bar b), Abs.α (G.comp H) ∈ B) ∧
        (∀ H, GReach (P.residual G.trace G.memOf) SC H → H ∉ Bar b → Abs.α (G.comp H) ∉ Abad) := by
  constructor
  · rintro ⟨h1, h⟩
    refine ⟨h1, ?_⟩
    rintro b hb ⟨G, hG, rfl⟩
    exact ⟨G, hG, rfl, h G hG hb⟩
  · rintro ⟨h1, h⟩
    refine ⟨h1, fun G hG hα => ?_⟩
    obtain ⟨G₀, hG₀, hα₀, h0, h2, h3⟩ := h _ hα ⟨G, hG, rfl⟩
    have hres : P.residual G.trace G.memOf = P.residual G₀.trace G₀.memOf := by
      rw [← Abs.res_eq hG, ← Abs.res_eq hG₀, hα₀]
    have hmem : G.memOf = G₀.memOf := by
      rw [← (Abs.hconf G hG).2, ← (Abs.hconf G₀ hG₀).2, hα₀]
    rw [hres, hmem]
    refine ⟨h0, fun H hH => ?_, fun H hH hout => ?_⟩
    · rw [hcomp G G₀ hG hG₀ hα₀.symm H (hres ▸ hH.2.1)]
      exact h2 H hH
    · rw [hcomp G G₀ hG hG₀ hα₀.symm H (hres ▸ hH)]
      exact h3 H hH hout

end Abstraction

/-! ### rem:bar-tight -/

/-- A maximal step extends its graph. -/
theorem MStep.isPrefixOf {P' : Program} {t : Tid} {H H' : Graph} (h : MStep P' t H H') :
    H.IsPrefixOf H' := by
  obtain ⟨hW, hW', e, -, he, hev, hres, -⟩ := h
  exact isPrefixOf_of_insert hW hW' he hev hres

/-- For a bar closed under extension, a reachable graph outside the bar is
the end of a derivation outside the bar. -/
theorem outsidePath_of_extClosed {P' : Program} {X : Set Graph} (hX : BarExtClosed P' X)
    {H : Graph} (hH : GReach P' SC H) (hout : H ∉ X) : OutsidePath P' X H := by
  have key : ∀ (τ : List Tid) (H : Graph), MSteps P' τ (Graph.init P'.mem) H → H ∉ X →
      OutsidePath P' X H := by
    intro τ
    induction τ with
    | nil =>
      intro H h hout
      have : H = Graph.init P'.mem := h
      subst this
      exact .init hout
    | cons t τ ih =>
      rintro H ⟨Hm, hm, hs⟩ hout
      refine .step (ih Hm hm (fun hmX => hout ?_)) hs hout
      exact hX Hm H (MSteps.greach hm) (greach_iff.mpr hs.execSC_right) hmX hs.isPrefixOf
  obtain ⟨τ, -, hτ⟩ := greach_iff_msteps.mp hH
  exact key τ H hτ hout

namespace Abstraction

variable (Abs : Abstraction P A)

/-- rem:bar-tight: for bars closed under extension the path form is
def:barinductive. -/
theorem barInductive_iff_path {Abad B : Set A} {Bar : A → Set Graph}
    (hX : ∀ G, ExecSC P G → Abs.α G ∈ B →
      BarExtClosed (P.residual G.trace G.memOf) (Bar (Abs.α G))) :
    Abs.BarInductive Abad B Bar ↔ Abs.BarInductivePath Abad B Bar := by
  refine ⟨BarInductive.path Abs, fun hB => ⟨hB.1, fun G hG hα => ?_⟩⟩
  obtain ⟨h0, h2, h3⟩ := hB.2 G hG hα
  refine ⟨h0, ?_, fun H hH hout => h3 H (outsidePath_of_extClosed (hX G hG hα) hH hout)⟩
  rintro H ⟨hHX, -, H', t, hH', hout', hs⟩
  exact h2 H' H t (outsidePath_of_extClosed (hX G hG hα) hH' hout') hs hHX

end Abstraction

/-! ### The remark after def:bar -/

theorem DepthLe.size_le {P' : Program} {X : Set Graph} {N : ℕ} (hd : DepthLe P' X N)
    {H : Graph} (hH : GReach P' SC H) (hout : H ∉ X) : H.size ≤ N := by
  by_contra hlt
  exact hout (hd H hH (by omega))

theorem MStep.size {P' : Program} {t : Tid} {H H' : Graph} (h : MStep P' t H H') :
    H'.size = H.size + 1 := by
  obtain ⟨-, -, e, -, he, hev, -⟩ := h
  unfold Graph.size
  rw [hev, Finset.card_insert_of_notMem he]

theorem DepthLe.boundary_size_le {P' : Program} {X : Set Graph} {N : ℕ} (hd : DepthLe P' X N)
    {H : Graph} (hH : H ∈ boundary P' X) : H.size ≤ N + 1 := by
  obtain ⟨-, -, H', t, hH', hout', hs⟩ := hH
  have := hd.size_le hH' hout'
  rw [hs.size]
  omega

/-! ### prop:kbar -/

/-- The bar `B^K`: the graphs of size at least `K + 1`. -/
def barK (K : ℕ) : Set Graph := {H | K + 1 ≤ H.size}

theorem init_not_mem_barK {K : ℕ} (hK : 1 ≤ K) (μ : Loc → Val) : Graph.init μ ∉ barK K := by
  intro h
  have h' : K + 1 ≤ (Graph.init μ).size := h
  simp [Graph.size, Graph.init] at h'
  omega

theorem depthLe_barK (P' : Program) (K : ℕ) : DepthLe P' (barK K) K := fun _ _ h => h

theorem boundary_barK (P' : Program) {K : ℕ} (hK : 1 ≤ K) :
    boundary P' (barK K) = {H | GReach P' SC H ∧ H.size = K + 1} := by
  ext H
  constructor
  · rintro ⟨hX, hH, H', t, -, hout', hs⟩
    have h1 : K + 1 ≤ H.size := hX
    have h2 : ¬ K + 1 ≤ H'.size := hout'
    have := hs.size
    exact ⟨hH, by omega⟩
  · rintro ⟨hH, hsz⟩
    obtain ⟨τ, hlen, hτ⟩ := greach_iff_msteps.mp hH
    have hcard : H.events.card = K := by
      unfold Graph.size at hsz
      omega
    cases τ with
    | nil =>
      rw [List.length_nil] at hlen
      omega
    | cons t τ =>
      obtain ⟨H', hm, hs⟩ := hτ
      refine ⟨by change K + 1 ≤ H.size; omega, hH, H', t, MSteps.greach hm, ?_, hs⟩
      have := hs.size
      change ¬ K + 1 ≤ H'.size
      omega

namespace Abstraction

variable (Abs : Abstraction P A)

/-- prop:kbar: `B` is bar-inductive for the bars `B^K` iff it is
`K`-inductive. -/
theorem barInductive_barK_iff {Abad B : Set A} {K : ℕ} (hK : 1 ≤ K) :
    Abs.BarInductive Abad B (fun _ => barK K) ↔ Abs.KInductive Abad B K := by
  constructor
  · rintro ⟨h1, h⟩
    refine ⟨h1, fun G hG hα H hH => ?_⟩
    obtain ⟨-, h2, h3⟩ := h G hG hα
    refine ⟨fun hsz => h2 H ?_, fun hsz => h3 H hH ?_⟩
    · rw [boundary_barK _ hK]
      exact ⟨hH, hsz⟩
    · change ¬ K + 1 ≤ H.size
      omega
  · rintro ⟨h1, h⟩
    refine ⟨h1, fun G hG hα => ⟨init_not_mem_barK hK _, fun H hH => ?_, fun H hH hout => ?_⟩⟩
    · rw [boundary_barK _ hK] at hH
      exact ((h G hG hα) H hH.1).1 hH.2
    · have hout' : ¬ K + 1 ≤ H.size := hout
      exact ((h G hG hα) H hH).2 (by omega)

end Abstraction

end Trust
