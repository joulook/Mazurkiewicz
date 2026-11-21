import Mazurkiewicz.Induction.Certificate

/-!
# Compositional abstractions and `K`-inductive sets

`induction-popl`, `bridge.tex` sec:abstraction (def:abstraction,
def:kinductive, thm:ksound) and sec:reduction (lem:representatives,
def:obligation, thm:reduction, cor:finite), for plain programs under SC.

How the text is read here.

* def:abstraction: `α : Exec_SC(P) → A` with `conf : A → Conf_P` and
  `conf ∘ α = h`. Here `α` is a total function on graphs and every condition
  is guarded by `ExecSC`; `conf b` is given by traces `u b t` and a memory
  `μ b` (`Abstraction`), and `conf ∘ α = h` is `Abstraction.hconf`, asked on
  the listed threads. No choice of representatives is made.
* The residual program of `b` is `Abs.res b`; for `b = α(G)` it is the
  program `P_{h(G)}` (`Abstraction.res_eq`).
* `b ⊙ H` is not defined as an operation: where the paper writes `b ⊙ H` for a
  realised `b`, the statements speak of `α (G.comp H)` for a graph `G` with
  `α G = b`. For a compositional abstraction this does not depend on `G`
  (def:abstraction); the statements that do not need compositionality do not
  assume it.
* def:kinductive is stated in this form already in the paper ((K2), (K3)
  quantify over `G`), so thm:ksound needs no compositionality, as in the
  paper.
* lem:representatives: for a compositional abstraction, (K2) and (K3) hold
  iff they hold for one graph `G` per realised `b ∈ B`
  (`kinductive_iff_representatives`).
* def:obligation, thm:reduction: the obligation program is
  `(Abs.res b).trunc (fun _ => K)`; the obligation property is `oblBad`,
  written with a graph `G` with `α G = b`.
* cor:finite: only the soundness half (`safe_of_obligations`, and
  `safe_of_obligations_realised` with the obligations of the realised elements
  only); it needs neither finiteness nor effectiveness nor compositionality.
  Decidability is replaced by the executable procedure of
  `Induction/Check.lean`.
* The definitions and the equivalences make sense for `K = 0`; soundness
  (thm:ksound) needs `1 ≤ K`. thm:reduction is the equivalence
  (`reduction`); its last sentence, "in that case `P` is safe", is `ksound`.
-/

namespace Trust

open Program in
/-- Maximal steps along a concatenation of lists. -/
theorem MSteps.append {P : Program} {τ₁ τ₂ : List Tid} {G G'' : Graph} :
    MSteps P (τ₂ ++ τ₁) G G'' ↔ ∃ G', MSteps P τ₁ G G' ∧ MSteps P τ₂ G' G'' := by
  induction τ₂ generalizing G'' with
  | nil =>
    constructor
    · exact fun h => ⟨G'', h, rfl⟩
    · rintro ⟨G', h, rfl⟩
      exact h
  | cons t τ₂ ih =>
    constructor
    · rintro ⟨G₁, h₁, hs⟩
      obtain ⟨G', h, h'⟩ := ih.mp h₁
      exact ⟨G', h, G₁, h', hs⟩
    · rintro ⟨G', h, G₁, h', hs⟩
      exact ⟨G₁, ih.mpr ⟨G', h, h'⟩, hs⟩

/-- Maximal steps keep consistent executions. -/
theorem MSteps.execSC {P : Program} {τ : List Tid} {G G' : Graph} (hG : ExecSC P G)
    (h : MSteps P τ G G') : ExecSC P G' := by
  cases τ with
  | nil => exact h ▸ hG
  | cons t τ =>
    obtain ⟨G₁, -, hs⟩ := h
    exact hs.execSC_right

/-- A graph of size at most `K + 1` has at most `K` events of each thread. -/
theorem Graph.cnt_le_of_size {H : Graph} {K : ℕ} (h : H.size ≤ K + 1) (t : Tid) :
    H.cnt t ≤ K := by
  have h1 : H.cnt t ≤ H.events.card := Finset.card_filter_le _ _
  unfold Graph.size at h
  omega

open Program

/-- An abstraction of `P` (def:abstraction). -/
structure Abstraction (P : Program) (A : Type) where
  /-- the abstraction function -/
  α : Graph → A
  /-- representatives of the local states of `conf b` -/
  u : A → Tid → List (Option Val)
  /-- the memory of `conf b` -/
  μ : A → Loc → Val
  /-- `conf ∘ α = h` -/
  hconf : ∀ G, ExecSC P G →
    (∀ t ∈ P.threads, FutEq (P.step t) (u (α G) t) (G.trace t)) ∧ μ (α G) = G.memOf

namespace Abstraction

variable {P : Program} {A : Type} (Abs : Abstraction P A)

/-- The residual program `P_{conf(b)}`. -/
def res (b : A) : Program := P.residual (Abs.u b) (Abs.μ b)

/-- `b` is realised (def:abstraction). -/
def Realised (b : A) : Prop := ∃ G, ExecSC P G ∧ Abs.α G = b

/-- The abstraction is compositional (def:abstraction). -/
def Compositional : Prop :=
  ∀ G₁ G₂, ExecSC P G₁ → ExecSC P G₂ → Abs.α G₁ = Abs.α G₂ →
    ∀ H, GReach (P.residual G₁.trace G₁.memOf) SC H → Abs.α (G₁.comp H) = Abs.α (G₂.comp H)

/-- `Bad` is `α`-determined by `Abad` (def:abstraction). -/
def Determines (Bad : Set Graph) (Abad : Set A) : Prop :=
  ∀ G, ExecSC P G → (G ∈ Bad ↔ Abs.α G ∈ Abad)

/-- (K2) and (K3) of def:kinductive for one graph `G`. -/
def StepOK (Abad B : Set A) (K : ℕ) (G : Graph) : Prop :=
  ∀ H, GReach (P.residual G.trace G.memOf) SC H →
    (H.size = K + 1 → Abs.α (G.comp H) ∈ B) ∧ (H.size ≤ K → Abs.α (G.comp H) ∉ Abad)

/-- A `K`-inductive set (def:kinductive). -/
def KInductive (Abad B : Set A) (K : ℕ) : Prop :=
  Abs.α (Graph.init P.mem) ∈ B ∧ ∀ G, ExecSC P G → Abs.α G ∈ B → Abs.StepOK Abad B K G

/-- The obligation property `Bad^{b,K}` (def:obligation), for a graph `G`
with `α G = b`. -/
def oblBad (Abad B : Set A) (K : ℕ) (G : Graph) : Set Graph :=
  {H | (H.size = K + 1 ∧ Abs.α (G.comp H) ∉ B) ∨ (H.size ≤ K ∧ Abs.α (G.comp H) ∈ Abad)}

/-! ### Statements -/

/-- The residual program of `α(G)` is `P_{h(G)}`. -/
theorem res_eq {G : Graph} (hG : ExecSC P G) :
    Abs.res (Abs.α G) = P.residual G.trace G.memOf := by
  unfold res
  rw [(Abs.hconf G hG).2]
  exact Program.residual_eq_iff.mpr (Abs.hconf G hG).1

/-- The configuration `conf b`: the classes of the representatives on the
listed threads, the class of the empty trace elsewhere, and the memory. -/
def confAbs (b : A) : Conf P :=
  (fun t => St.mk (P.step t) (if t ∈ P.threads then Abs.u b t else []), Abs.μ b)

/-- `conf ∘ α = h` (def:abstraction). -/
theorem confAbs_eq {G : Graph} (hG : ExecSC P G) : Abs.confAbs (Abs.α G) = conf P G := by
  obtain ⟨h1, h2⟩ := Abs.hconf G hG
  refine Prod.ext (funext fun t => ?_) h2
  refine St.mk_eq_mk.mpr ?_
  by_cases ht : t ∈ P.threads
  · simp only [ht, ↓reduceIte]
    exact h1 t ht
  · simp only [ht, ↓reduceIte]
    rw [hG.trace_of_not_mem ht]
    exact (futEq_equivalence _).refl _

/-- thm:ksound. -/
theorem ksound {Bad : Set Graph} {Abad B : Set A} {K : ℕ} (hdet : Abs.Determines Bad Abad)
    (hK : 1 ≤ K) (hB : Abs.KInductive Abad B K) : Safe P SC Bad := by
  have key : ∀ n (τ : List Tid), τ.length = n → ∀ G G', ExecSC P G → Abs.α G ∈ B →
      MSteps P τ G G' → Abs.α G' ∉ Abad := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro τ hlen G G' hG hα h
      by_cases hlt : n < K
      · obtain ⟨H, hH, hsz, rfl⟩ := msteps_decomp hG h
        exact (hB.2 G hG hα H hH).2 (by omega)
      · have hsplit : τ = τ.take (n - K) ++ τ.drop (n - K) := (List.take_append_drop _ _).symm
        rw [hsplit] at h
        obtain ⟨G₁, h₁, h₂⟩ := MSteps.append.mp h
        have hlen₁ : (τ.drop (n - K)).length = K := by
          rw [List.length_drop, hlen]
          omega
        obtain ⟨H, hH, hsz, rfl⟩ := msteps_decomp hG h₁
        have hα₁ := (hB.2 G hG hα H hH).1 (by omega)
        refine ih (n - K) (by omega) (τ.take (n - K)) ?_ _ G' (MSteps.execSC hG h₁) hα₁ h₂
        rw [List.length_take, hlen]
        omega
  intro G hG
  obtain ⟨τ, -, hm⟩ := greach_iff_msteps.mp hG
  have h0 : ExecSC P (Graph.init P.mem) := ⟨Graph.init_wf _, exec_init P, SC.cons_init _⟩
  have := key _ τ rfl _ G h0 hB.1 hm
  exact fun hbad => this ((hdet G (greach_iff.mp hG)).mp hbad)

/-- lem:representatives: for a compositional abstraction, (K2) and (K3) may be
checked on one graph for each realised element of `B`. -/
theorem kinductive_iff_representatives (hcomp : Abs.Compositional) {Abad B : Set A} {K : ℕ} :
    (∀ G, ExecSC P G → Abs.α G ∈ B → Abs.StepOK Abad B K G) ↔
      ∀ b ∈ B, Abs.Realised b → ∃ G, ExecSC P G ∧ Abs.α G = b ∧ Abs.StepOK Abad B K G := by
  constructor
  · rintro h b hb ⟨G, hG, rfl⟩
    exact ⟨G, hG, rfl, h G hG hb⟩
  · intro h G hG hα
    obtain ⟨G₀, hG₀, hα₀, hok⟩ := h _ hα ⟨G, hG, rfl⟩
    have hres : P.residual G.trace G.memOf = P.residual G₀.trace G₀.memOf := by
      rw [← Abs.res_eq hG, ← Abs.res_eq hG₀, hα₀]
    intro H hH
    rw [hcomp G G₀ hG hG₀ hα₀.symm H hH]
    exact hok H (hres ▸ hH)

/-- The reachable graphs of the obligation program: the reachable graphs of
the residual program with at most `K` events per thread. -/
theorem greach_trunc_iff {Q : Program} {K : ℕ} {H : Graph} :
    GReach (Q.trunc (fun _ => K)) SC H ↔ GReach Q SC H ∧ ∀ t, H.cnt t ≤ K := by
  rw [greach_iff, greach_iff]
  constructor
  · rintro ⟨hW, hE, hc⟩
    obtain ⟨hE', hle⟩ := (Program.exec_trunc_iff hW _).mp hE
    exact ⟨⟨hW, hE', hc⟩, hle⟩
  · rintro ⟨⟨hW, hE, hc⟩, hle⟩
    exact ⟨hW, (Program.exec_trunc_iff hW _).mpr ⟨hE, hle⟩, hc⟩

/-- thm:reduction, for one graph: (K2) and (K3) at `G` hold iff the obligation
program of `α(G)` is safe for the obligation property. -/
theorem stepOK_iff_obligation {Abad B : Set A} {K : ℕ} {G : Graph} (hG : ExecSC P G) :
    Abs.StepOK Abad B K G ↔
      Safe ((Abs.res (Abs.α G)).trunc (fun _ => K)) SC (Abs.oblBad Abad B K G) := by
  rw [Abs.res_eq hG]
  constructor
  · intro hok H hH
    obtain ⟨h1, h2⟩ := hok H (greach_trunc_iff.mp hH).1
    rintro (⟨hsz, hb⟩ | ⟨hsz, hb⟩)
    · exact hb (h1 hsz)
    · exact h2 hsz hb
  · intro hsafe H hH
    refine ⟨fun hsz => ?_, fun hsz hb => ?_⟩
    · by_contra hb
      exact hsafe H (greach_trunc_iff.mpr ⟨hH, Graph.cnt_le_of_size (by omega)⟩)
        (Or.inl ⟨hsz, hb⟩)
    · exact hsafe H (greach_trunc_iff.mpr ⟨hH, Graph.cnt_le_of_size (by omega)⟩)
        (Or.inr ⟨hsz, hb⟩)

/-- thm:reduction: for a compositional abstraction and `α(G_init) ∈ B`, the
set `B` is `K`-inductive iff for every realised `b ∈ B` the obligation
program is safe for the obligation property (of one, equivalently every,
graph `G` with `α G = b`). -/
theorem reduction (hcomp : Abs.Compositional) {Abad B : Set A} {K : ℕ}
    (hinit : Abs.α (Graph.init P.mem) ∈ B) :
    Abs.KInductive Abad B K ↔
      ∀ b ∈ B, Abs.Realised b → ∃ G, ExecSC P G ∧ Abs.α G = b ∧
        Safe ((Abs.res b).trunc (fun _ => K)) SC (Abs.oblBad Abad B K G) := by
  unfold KInductive
  rw [Abs.kinductive_iff_representatives hcomp]
  constructor
  · rintro ⟨-, h⟩ b hb hr
    obtain ⟨G, hG, rfl, hok⟩ := h b hb hr
    exact ⟨G, hG, rfl, (Abs.stepOK_iff_obligation hG).mp hok⟩
  · intro h
    refine ⟨hinit, fun b hb hr => ?_⟩
    obtain ⟨G, hG, rfl, hsafe⟩ := h b hb hr
    exact ⟨G, hG, rfl, (Abs.stepOK_iff_obligation hG).mpr hsafe⟩

/-- cor:finite, soundness, with the obligations of the realised elements only:
if a function `f` computes `α (G.comp H)` from `α G` and `H` for the small
fragments, and for every graph `G` with `α G ∈ B` the obligation program of
`α G` is safe for the property written with `f`, then `P` is safe. -/
theorem safe_of_obligations_realised {Bad : Set Graph} {Abad B : Set A} {K : ℕ}
    (hdet : Abs.Determines Bad Abad) (hK : 1 ≤ K) (hinit : Abs.α (Graph.init P.mem) ∈ B)
    (f : A → Graph → A)
    (hf : ∀ G, ExecSC P G → Abs.α G ∈ B → ∀ H, GReach (P.residual G.trace G.memOf) SC H →
      H.size ≤ K + 1 → f (Abs.α G) H = Abs.α (G.comp H))
    (hobl : ∀ G, ExecSC P G → Abs.α G ∈ B →
      Safe ((Abs.res (Abs.α G)).trunc (fun _ => K)) SC
        {H | (H.size = K + 1 ∧ f (Abs.α G) H ∉ B) ∨ (H.size ≤ K ∧ f (Abs.α G) H ∈ Abad)}) :
    Safe P SC Bad := by
  refine Abs.ksound hdet hK ⟨hinit, fun G hG hα H hH => ?_⟩
  have hH' : H.size ≤ K + 1 → GReach ((Abs.res (Abs.α G)).trunc (fun _ => K)) SC H := by
    intro hsz
    rw [Abs.res_eq hG]
    exact greach_trunc_iff.mpr ⟨hH, Graph.cnt_le_of_size hsz⟩
  refine ⟨fun hsz => ?_, fun hsz hb => ?_⟩
  · by_contra hb
    refine hobl G hG hα H (hH' (by omega)) (Or.inl ⟨hsz, ?_⟩)
    rw [hf G hG hα H hH (by omega)]
    exact hb
  · refine hobl G hG hα H (hH' (by omega)) (Or.inr ⟨hsz, ?_⟩)
    rw [hf G hG hα H hH (by omega)]
    exact hb

/-- cor:finite, soundness: the same with the obligations of every `b ∈ B`,
realised or not, as the paper states it. -/
theorem safe_of_obligations {Bad : Set Graph} {Abad B : Set A} {K : ℕ}
    (hdet : Abs.Determines Bad Abad) (hK : 1 ≤ K) (hinit : Abs.α (Graph.init P.mem) ∈ B)
    (f : A → Graph → A)
    (hf : ∀ G, ExecSC P G → Abs.α G ∈ B → ∀ H, GReach (P.residual G.trace G.memOf) SC H →
      H.size ≤ K + 1 → f (Abs.α G) H = Abs.α (G.comp H))
    (hobl : ∀ b ∈ B, Safe ((Abs.res b).trunc (fun _ => K)) SC
      {H | (H.size = K + 1 ∧ f b H ∉ B) ∨ (H.size ≤ K ∧ f b H ∈ Abad)}) :
    Safe P SC Bad :=
  Abs.safe_of_obligations_realised hdet hK hinit f hf (fun _ _ hα => hobl _ hα)

/-! ### An instance -/

/-- The identity abstraction (ex:abstractions): `α = id`, with the traces and
the memory of the graph. -/
noncomputable def identity (P : Program) : Abstraction P Graph where
  α := id
  u := fun G => G.trace
  μ := fun G => G.memOf
  hconf := fun _ _ => ⟨fun _ _ => (futEq_equivalence _).refl _, rfl⟩

/-- The identity abstraction is compositional (ex:abstractions). -/
theorem identity_compositional (P : Program) : (identity P).Compositional := by
  intro G₁ G₂ _ _ h H _
  have h' : G₁ = G₂ := h
  rw [h']

end Abstraction

end Trust
