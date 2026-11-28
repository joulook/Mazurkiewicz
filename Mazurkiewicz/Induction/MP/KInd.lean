import Mazurkiewicz.Induction.MP.Instances

/-!
# Message passing: abstractions and `K`-inductive sets (milestone C6)

`induction-popl`, `mp.tex` def:mp-abstraction, the note mp:221, def:mp-kinductive,
thm:mp-reduction, and `p2p.tex` p2p:183-195, thm:p2p (1), for the one construction over a
setting `S : MPSetting Q` (plan `plan/ind/TRACK-C-PLAN.md`, milestone C6).

* `SAbs S A`: an abstraction `α` with, for every abstract value `b`, the local states `u b`
  and the seed words `W b`, such that on every consistent execution `G` the words fit (`hconf`:
  `u (α G)` is `FutEq` to the traces, `W (α G)` vanishes outside the threads, and some seeds
  `ρ` exist). `res b` is `Q_b`; `Realised`, `Determines` (α-determined), `ExtClosed`,
  `Compositional` (witness form: all seeds `ρ` allowed by `SeedOK`, for the fixed words
  `W b`).
* def:mp-kinductive: `StepOK`, `KInductive`; thm:mp-reduction (1): `ksound` (does not use the
  composition, so it needs none of `hms`, `hord`, `hP`, `hρ`); (2): `stepOK_iff_fragOK`
  (witness form, for one `G` and seeds `ρ`), `kinductive_iff_representatives` (over the
  realised values, for a compositional abstraction).
* Section 6: `asynAbs` (from `α`, `u`, a word `w b` with `↑(w (α G)) = pend(G)`),
  `CompositionalEnv` (mp:207-210: all pending enumerations with a common word),
  `compositionalEnv_imp`, `h_compositional_env` (the note mp:221: `h` is compositional; uses
  `hP : P.Tagged .asyn`).
* Section 7: `p2pAbs` (`W := w` with `w (α G) = pend_t(G)`, seeds `ρP2P G`),
  `h_compositional_p2p` (p2p:189). Astra's r1 counterexample to an `ord` not tied to `p2p`
  (pending `1, 2` of one sender reseeded in order `2, 1`; the residual reads `2`, the
  composition skips the unread `1`, violating (P1)) is excluded by `S.hord`.
* Helpers: `stepsN_add`, `execM_empty`, `StM.mk_eq_mk`, `FutEq.append`.
-/

namespace Must

namespace Ind

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]

/-! ### Helpers -/

omit [DecidableEq Q] [Membership Val Q] in
theorem StM.mk_eq_mk {p : List (Option Val) → Option (Lab Q)} {u u' : List (Option Val)} :
    StM.mk p u = StM.mk p u' ↔ FutEq p u u' :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

omit [DecidableEq Q] [Membership Val Q] in
theorem FutEq.append {p : List (Option Val) → Option (Lab Q)} {u u' : List (Option Val)}
    (h : FutEq p u u') (v : List (Option Val)) : FutEq p (u ++ v) (u' ++ v) := fun x => by
  rw [List.append_assoc, List.append_assoc]
  exact h (v ++ x)

/-- `a + b` steps split into `a` steps and `b` steps. -/
theorem stepsN_add {M : Model Q} {P : Program Q} {a : ℕ} :
    ∀ {b : ℕ} {G G' : Graph Q}, StepsN M P (a + b) G G' →
      ∃ G'', StepsN M P a G G'' ∧ StepsN M P b G'' G'
  | 0, _, G', h => ⟨G', h, rfl⟩
  | b + 1, _, _, h => by
    obtain ⟨G₁, h1, hs⟩ := h
    obtain ⟨G'', h2, h3⟩ := stepsN_add h1
    exact ⟨G'', h2, G₁, h3, hs⟩

/-- The empty graph is a consistent execution. -/
theorem execM_empty {M : Model Q} {P : Program Q} : ExecM M P Graph.empty :=
  ⟨fun e he => by simp [Graph.empty] at he, M.empty⟩

/-! ### Abstractions over a setting -/

/-- An abstraction for the construction over `S` (def:mp-abstraction, p2p:183-189): the
abstract value gives the local states `u b` and the seed words `W b`. -/
structure SAbs (S : MPSetting Q) (A : Type) where
  /-- the abstraction -/
  α : Graph Q → A
  /-- the local states of an abstract value -/
  u : A → Tid → List (Option Val)
  /-- the seed words of an abstract value -/
  W : A → Tid → List Msg
  /-- the states and words fit every consistent execution -/
  hconf : ∀ G, ExecM (Model.ofSet S.ms) S.P G →
    (∀ t ∈ S.P.threads, FutEq (S.P.step t) (u (α G) t) (G.trace t)) ∧
    (∀ t ∉ S.ts, W (α G) t = []) ∧ ∃ ρ, SeedOK G S.m (W (α G)) ρ S.ord

namespace SAbs

variable {S : MPSetting Q} {A : Type} (Abs : SAbs S A)

/-- `Q_b`: the fragment program of an abstract value. -/
def res (b : A) : Program Q := S.P.seedRes S.ι S.hι S.m (Abs.u b) (Abs.W b)

/-- `b` is the value of a consistent execution. -/
def Realised (b : A) : Prop := ∃ G, ExecM (Model.ofSet S.ms) S.P G ∧ Abs.α G = b

/-- `Bad` is α-determined by `Abad` (def:mp-abstraction). -/
def Determines (Bad : Set (Graph Q)) (Abad : Set A) : Prop :=
  ∀ G, ExecM (Model.ofSet S.ms) S.P G → (G ∈ Bad ↔ Abs.α G ∈ Abad)

/-- `Bad` is extension-closed (def:mp-abstraction). It does not depend on the abstraction; the
argument is there for the dot notation `Abs.ExtClosed`. -/
def ExtClosed (_Abs : SAbs S A) (Bad : Set (Graph Q)) : Prop :=
  ∀ G G', ExecM (Model.ofSet S.ms) S.P G → ExecM (Model.ofSet S.ms) S.P G' → G ∈ Bad →
    G.IsPrefixOf G' → G' ∈ Bad

/-- Compositionality in witness form: for the fixed words `W b` and all seeds allowed by
`SeedOK`. -/
def Compositional : Prop :=
  ∀ G₁ G₂ ρ₁ ρ₂, ExecM (Model.ofSet S.ms) S.P G₁ → ExecM (Model.ofSet S.ms) S.P G₂ →
    Abs.α G₁ = Abs.α G₂ →
    SeedOK G₁ S.m (Abs.W (Abs.α G₁)) ρ₁ S.ord → SeedOK G₂ S.m (Abs.W (Abs.α G₂)) ρ₂ S.ord →
    ∀ H, Frag (Model.ofSet S.ms) (Abs.res (Abs.α G₁)) (Abs.W (Abs.α G₁)) H →
      Abs.α (G₁.scomp H (Abs.W (Abs.α G₁)) ρ₁) = Abs.α (G₂.scomp H (Abs.W (Abs.α G₂)) ρ₂)

/-- (K2), (K3) of def:mp-kinductive at `G`. -/
def StepOK (Abad B : Set A) (K : ℕ) (G : Graph Q) : Prop :=
  (∀ G', StepsN (Model.ofSet S.ms) S.P K G G' → Abs.α G' ∈ B) ∧
    ∀ j < K, ∀ G', StepsN (Model.ofSet S.ms) S.P j G G' → Abs.α G' ∉ Abad

/-- def:mp-kinductive. -/
def KInductive (Abad B : Set A) (K : ℕ) : Prop :=
  Abs.α Graph.empty ∈ B ∧
    ∀ G, ExecM (Model.ofSet S.ms) S.P G → Abs.α G ∈ B → Abs.StepOK Abad B K G

/-- The conditions of thm:mp-reduction (2) for `G` and seeds `ρ`. -/
def FragOK (Abad B : Set A) (K : ℕ) (G : Graph Q) (ρ : Ev Q → Ev Q) : Prop :=
  ∀ H, Frag (Model.ofSet S.ms) (Abs.res (Abs.α G)) (Abs.W (Abs.α G)) H →
    (H.len S.ts (Abs.W (Abs.α G)) = K → Abs.α (G.scomp H (Abs.W (Abs.α G)) ρ) ∈ B) ∧
    (H.len S.ts (Abs.W (Abs.α G)) < K → Abs.α (G.scomp H (Abs.W (Abs.α G)) ρ) ∉ Abad)

/-- thm:mp-reduction (1), thm:p2p (1): a `K`-inductive set gives safety. -/
theorem ksound {Bad : Set (Graph Q)} {Abad B : Set A} {K : ℕ} (hK : 1 ≤ K)
    (hdet : Abs.Determines Bad Abad) (h : Abs.KInductive Abad B K) :
    Safe (Model.ofSet S.ms) S.P Bad := by
  have hB : ∀ j G', StepsN (Model.ofSet S.ms) S.P (j * K) Graph.empty G' → Abs.α G' ∈ B := by
    intro j
    induction j with
    | zero =>
      intro G' hG'
      rw [Nat.zero_mul] at hG'
      cases hG'
      exact h.1
    | succ j ih =>
      intro G' hG'
      rw [Nat.succ_mul] at hG'
      obtain ⟨G'', h1, h2⟩ := stepsN_add hG'
      exact (h.2 G'' (StepsN.execM execM_empty h1).1 (ih G'' h1)).1 G' h2
  intro G hr hbad
  have hE := mreach_iff.mp hr
  have hs : StepsN (Model.ofSet S.ms) S.P G.events.card Graph.empty G :=
    (stepsN_iff execM_empty).mpr ⟨hE, empty_isPrefixOf G, by simp [Graph.empty]⟩
  rw [← Nat.div_add_mod' G.events.card K] at hs
  obtain ⟨G'', h1, h2⟩ := stepsN_add hs
  have hG'' := (StepsN.execM execM_empty h1).1
  exact (h.2 G'' hG'' (hB _ G'' h1)).2 _ (Nat.mod_lt _ (by omega)) G h2
    ((hdet G hE).mp hbad)

/-- thm:mp-reduction (2), witness form: (K2), (K3) at `G` are the conditions on the fragments
of `Q_{α G}` composed with `G` by seeds `ρ`. -/
theorem stepOK_iff_fragOK {Abad B : Set A} {K : ℕ} {G : Graph Q} {ρ : Ev Q → Ev Q}
    (hG : ExecM (Model.ofSet S.ms) S.P G) (hρ : SeedOK G S.m (Abs.W (Abs.α G)) ρ S.ord) :
    Abs.StepOK Abad B K G ↔ Abs.FragOK Abad B K G ρ := by
  obtain ⟨hu, hW, -⟩ := Abs.hconf G hG
  have key := stepsN_iff_frag S hG hu hW hρ
  constructor
  · rintro ⟨h2, h3⟩ H hH
    refine ⟨fun hl => h2 _ ((key _ _).mpr ⟨H, hH, hl, rfl⟩), fun hl => ?_⟩
    exact h3 _ hl _ ((key _ _).mpr ⟨H, hH, rfl, rfl⟩)
  · intro h
    refine ⟨fun G' hG' => ?_, fun j hj G' hG' => ?_⟩
    · obtain ⟨H, hH, hl, rfl⟩ := (key _ _).mp hG'
      exact (h H hH).1 hl
    · obtain ⟨H, hH, hl, rfl⟩ := (key _ _).mp hG'
      exact (h H hH).2 (hl ▸ hj)

/-- thm:mp-reduction (2): for a compositional abstraction, `K`-inductivity is the condition on
one representative of every realised value. -/
theorem kinductive_iff_representatives {Abad B : Set A} {K : ℕ} (hcomp : Abs.Compositional)
    (h0 : Abs.α Graph.empty ∈ B) :
    Abs.KInductive Abad B K ↔ ∀ b ∈ B, Abs.Realised b →
      ∃ G ρ, ExecM (Model.ofSet S.ms) S.P G ∧ Abs.α G = b ∧ SeedOK G S.m (Abs.W b) ρ S.ord ∧
        Abs.FragOK Abad B K G ρ := by
  constructor
  · rintro ⟨-, h⟩ b hb ⟨G, hG, rfl⟩
    obtain ⟨-, -, ρ, hρ⟩ := Abs.hconf G hG
    exact ⟨G, ρ, hG, rfl, hρ, (Abs.stepOK_iff_fragOK hG hρ).mp (h G hG hb)⟩
  · intro h
    refine ⟨h0, fun G hG hb => ?_⟩
    obtain ⟨G₀, ρ₀, hG₀, hα, hρ₀, hok⟩ := h _ hb ⟨G, hG, rfl⟩
    obtain ⟨-, -, ρ, hρ⟩ := Abs.hconf G hG
    refine (Abs.stepOK_iff_fragOK hG hρ).mpr fun H hH => ?_
    rw [← hα] at hρ₀
    have hH₀ : Frag (Model.ofSet S.ms) (Abs.res (Abs.α G₀)) (Abs.W (Abs.α G₀)) H := by
      rw [hα]
      exact hH
    have hc := hcomp G₀ G ρ₀ ρ hG₀ hG hα hρ₀ hρ H hH₀
    have hk := hok H hH₀
    rw [hc, hα] at hk
    exact hk

end SAbs

/-! ### Section 6 -/

/-- The abstraction of Section 6 (def:mp-abstraction) as an `SAbs` of `envSetting`: the seed
word of `b` is `w b` on `ν`; seeds from a pending enumeration with that word. -/
def asynAbs (P : Program Q) (ν : Tid) (hν : ν ∉ P.threads) (hP : P.Tagged .asyn) {A : Type}
    (α : Graph Q → A) (u : A → Tid → List (Option Val)) (w : A → List Msg)
    (hconf : ∀ G, ExecM Model.asyn P G →
      (∀ t ∈ P.threads, FutEq (P.step t) (u (α G) t) (G.trace t)) ∧
        (↑(w (α G)) : Multiset Msg) = G.pendM) :
    SAbs (envSetting P ν hν hP) A where
  α := α
  u := u
  W := fun b => envW ν (w b)
  hconf G hG := by
    refine ⟨(hconf G hG).1, fun t ht => envW_nil fun h =>
      ht (List.mem_append_right _ (h ▸ List.mem_singleton_self _)), ?_⟩
    obtain ⟨σ, hσ, hw⟩ := pendEnum_of_pendM (hconf G hG).2
    refine ⟨ρEnv σ, ?_⟩
    rw [← hw]
    exact seedOK_env hG hP hσ

/-- Compositionality of Section 6 (mp:207-210): over all pending enumerations with a common
word. -/
def CompositionalEnv (P : Program Q) (ν : Tid) (hν : ν ∉ P.threads) {A : Type}
    (α : Graph Q → A) : Prop :=
  ∀ G₁ G₂ σ₁ σ₂, ExecM Model.asyn P G₁ → ExecM Model.asyn P G₂ → α G₁ = α G₂ →
    IsPendEnum G₁ σ₁ → IsPendEnum G₂ σ₂ → word σ₁ = word σ₂ →
    ∀ H, Frag Model.asyn (P.envRes ν hν G₁.trace (word σ₁)) (envW ν (word σ₁)) H →
      α (compEnv G₁ ν σ₁ H) = α (compEnv G₂ ν σ₂ H)

/-- The paper's compositionality implies the witness form. -/
theorem compositionalEnv_imp {P : Program Q} {ν : Tid} {hν : ν ∉ P.threads}
    {hP : P.Tagged .asyn} {A : Type} {α : Graph Q → A} {u : A → Tid → List (Option Val)}
    {w : A → List Msg}
    {hconf : ∀ G, ExecM Model.asyn P G →
      (∀ t ∈ P.threads, FutEq (P.step t) (u (α G) t) (G.trace t)) ∧
        (↑(w (α G)) : Multiset Msg) = G.pendM} :
    CompositionalEnv P ν hν α → (asynAbs P ν hν hP α u w hconf).Compositional := by
  intro hce G₁ G₂ ρ₁ ρ₂ hG₁ hG₂ hα hρ₁ hρ₂ H hH
  change α G₁ = α G₂ at hα
  obtain ⟨σ₁, hσ₁, hw₁, he₁⟩ := seedOK_env_enum (hν := hν) (w := w (α G₁)) hG₁ hP hρ₁
  obtain ⟨σ₂, hσ₂, hw₂, he₂⟩ := seedOK_env_enum (hν := hν) (w := w (α G₂)) hG₂ hP hρ₂
  change Frag Model.asyn (P.envRes ν hν (u (α G₁)) (w (α G₁))) (envW ν (w (α G₁))) H at hH
  change α (G₁.scomp H (envW ν (w (α G₁))) ρ₁) = α (G₂.scomp H (envW ν (w (α G₂))) ρ₂)
  have hres : P.envRes ν hν (u (α G₁)) (w (α G₁)) = P.envRes ν hν G₁.trace (w (α G₁)) :=
    seedRes_congr (hconf G₁ hG₁).1
  have hH' : Frag Model.asyn (P.envRes ν hν G₁.trace (word σ₁)) (envW ν (word σ₁)) H := by
    rw [hw₁, ← hres]
    exact hH
  have hH₂ : Frag Model.asyn (P.envRes ν hν (u (α G₁)) (w (α G₂))) (envW ν (w (α G₂))) H := by
    rw [← hα]
    exact hH
  rw [he₁ _ H hH, he₂ _ H hH₂]
  exact hce G₁ G₂ σ₁ σ₂ hG₁ hG₂ hα hσ₁ hσ₂ (by rw [hw₁, hw₂, hα]) H hH'

/-- The note mp:221: the configuration map `h` is compositional. -/
theorem h_compositional_env (P : Program Q) (ν : Tid) (hν : ν ∉ P.threads)
    (hP : P.Tagged .asyn) : CompositionalEnv P ν hν (hEnv P) := by
  intro G₁ G₂ σ₁ σ₂ hG₁ hG₂ hh hσ₁ hσ₂ hw H hH
  have hfut : ∀ t, FutEq (P.step t) (G₁.trace t) (G₂.trace t) := fun t =>
    StM.mk_eq_mk.mp (congrFun (congrArg Prod.fst hh) t)
  have hres : P.envRes ν hν G₁.trace (word σ₁) = P.envRes ν hν G₂.trace (word σ₂) := by
    rw [hw]
    exact seedRes_congr fun t _ => hfut t
  have hH₂ : Frag Model.asyn (P.envRes ν hν G₂.trace (word σ₂)) (envW ν (word σ₂)) H := by
    rw [← hres, ← hw]
    exact hH
  have hHw : H.Wf := Model.asyn.wf _ hH.1.2
  have hseed₁ := fun t j (hj : j < (envW ν (word σ₁) t).length) => frag_seedEv hH hj
  have hseed₂ := fun t j (hj : j < (envW ν (word σ₂) t).length) => frag_seedEv hH₂ hj
  have htr₁ := scomp_trace (Model.asyn.wf _ hG₁.2) hHw hH.2 hseed₁ (seedOK_env (ν := ν) hG₁ hP hσ₁)
  have htr₂ := scomp_trace (Model.asyn.wf _ hG₂.2) hHw hH₂.2 hseed₂
    (seedOK_env (ν := ν) hG₂ hP hσ₂)
  refine Prod.ext (funext fun t => ?_) ?_
  · change StM.mk (P.step t) ((compEnv G₁ ν σ₁ H).trace t) =
      StM.mk (P.step t) ((compEnv G₂ ν σ₂ H).trace t)
    unfold compEnv
    rw [htr₁, htr₂, ← hw]
    exact StM.mk_eq_mk.mpr ((hfut t).append _)
  · change (compEnv G₁ ν σ₁ H).pendM = (compEnv G₂ ν σ₂ H).pendM
    rw [(mp_compose_3 hν hP hG₁ hσ₁ hH).2.2.2, (mp_compose_3 hν hP hG₂ hσ₂ hH₂).2.2.2]

/-! ### Section 7 -/

/-- The abstraction of Section 7 (p2p:183-189) as an `SAbs` of a Section 7 setting: the seed
words are `w b`, with `w (α G) = pend_t(G)`; seeds `ρP2P G`. (The premise `hT` of the plan is
not needed: the canonical seeds satisfy `SeedOK … True`.) -/
def p2pAbs (S : MPSetting Q) (hS : S.ι = []) (_hT : S.ord) {A : Type} (α : Graph Q → A)
    (u : A → Tid → List (Option Val)) (w : A → Tid → List Msg)
    (hconf : ∀ G, ExecM (Model.ofSet S.ms) S.P G →
      (∀ t ∈ S.P.threads, FutEq (S.P.step t) (u (α G) t) (G.trace t)) ∧
        ∀ t, w (α G) t = G.pend t) :
    SAbs S A where
  α := α
  u := u
  W := w
  hconf G hG := by
    have hw : w (α G) = G.pend := funext (hconf G hG).2
    refine ⟨(hconf G hG).1, ?_, ρP2P G, ?_⟩
    · rw [hw]
      exact p2p_hW S hG
    · rw [hw]
      exact p2p_hρ S hS hG

/-- p2p:189: the configuration map `h` of Section 7 is compositional. -/
theorem h_compositional_p2p (S : MPSetting Q) (hS : S.ι = []) (hT : S.ord) :
    ∀ G₁ G₂, ExecM (Model.ofSet S.ms) S.P G₁ → ExecM (Model.ofSet S.ms) S.P G₂ →
      hP2P S.P G₁ = hP2P S.P G₂ →
      ∀ H, Frag (Model.ofSet S.ms) (S.P.p2pRes S.m G₁.trace G₁.pend) G₁.pend H →
        hP2P S.P (compP2P G₁ H) = hP2P S.P (compP2P G₂ H) := by
  intro G₁ G₂ hG₁ hG₂ hh H hH
  have hfut : ∀ t, FutEq (S.P.step t) (G₁.trace t) (G₂.trace t) := fun t =>
    StM.mk_eq_mk.mp (congrFun (congrArg Prod.fst hh) t)
  have hpend : G₁.pend = G₂.pend := congrArg Prod.snd hh
  have hH₂ : Frag (Model.ofSet S.ms) (S.P.p2pRes S.m G₂.trace G₂.pend) G₂.pend H := by
    have : S.P.p2pRes S.m G₁.trace G₁.pend = S.P.p2pRes S.m G₂.trace G₂.pend := by
      rw [hpend]
      exact seedRes_congr fun t _ => hfut t
    rw [← this, ← hpend]
    exact hH
  refine Prod.ext (funext fun t => ?_) (funext fun t => ?_)
  · change StM.mk (S.P.step t) ((compP2P G₁ H).trace t) =
      StM.mk (S.P.step t) ((compP2P G₂ H).trace t)
    rw [(p2p_compose_2 S hS hG₁ hH).2.2 t, (p2p_compose_2 S hS hG₂ hH₂).2.2 t, ← hpend]
    exact StM.mk_eq_mk.mpr ((hfut t).append _)
  · change (compP2P G₁ H).pend t = (compP2P G₂ H).pend t
    rw [(p2p_compose_1 S hS hT hG₁ hH).2.2.2.2.2 t, (p2p_compose_1 S hS hT hG₂ hH₂).2.2.2.2.2 t]

end Ind

end Must
