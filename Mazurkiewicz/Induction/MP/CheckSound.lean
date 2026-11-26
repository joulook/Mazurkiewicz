import Mazurkiewicz.Induction.MP.CheckRun

/-!
# Message passing: soundness and completeness of the check (milestone C8b, end theorem)

`induction-popl`, `mp.tex` thm:mp-reduction, thm:mp-terminal and para mp:329, `p2p.tex` thm:p2p,
for the executable check `CheckS` of `MP/CheckRun.lean` (plan `plan/ind/TRACK-C-PLAN.md`,
milestone C8b and Section 6).

* `CheckHyp`: the hypotheses of the end theorem (plan Section 6): a decision procedure `hc` of
  the model on `Supp` graphs, `hdet` (`Bad` α-determined by `abad`), `hext` (extension-closed),
  `hinit`, `hdisj`, `K ≥ 1`, and `hf` in witness form (`f` computes the abstract value of every
  composition with a fragment of length at most `K`, for every seeds `ρ`).
* `checkS_kinductive`: acceptance gives `K`-inductivity; `checkS_sound` (thm:mp-reduction (1)
  with thm:mp-terminal): acceptance gives safety; `checkS_sound_explicit`: the same with the
  hypotheses spelled out (the statement of plan Section 6); `checkS_accepts` (the analogue of
  cor:enum (2)): for realised values and a `K`-inductive set the check accepts for every large
  fuel.
* Instances: Section 6 `checkAsyn_kinductive`, `checkAsyn_sound`; Section 7
  `checkP2P_kinductive`, `checkP2P_sound`; rem:p2p-scope (i) `checkP2PAsyn_kinductive`,
  `checkP2PAsyn_sound`. Their `hf` is stated with the paper's compositions (`compEnv` over a
  pending enumeration with the word `w (α G)`, resp. `compP2P`) and reduced to `CheckHyp.hf` by
  the bridging lemmas `seedOK_env_enum`, `scomp_eq_compP2P` (C5).
* Assumed: `hc`, `P.Tagged m` (in the setting), `hdet`, `hext`, `hinit`, `hdisj`, `K ≥ 1`,
  `hf`, acceptance (which includes non-exhaustion of every run). Not assumed: boundedness of `P`,
  realisability, compositionality, `K`-inductivity, `P.threads ≠ []` (a program without threads
  has only the empty execution, `stepsN_of_threads_nil`), and no premise about Must: the
  enumerator is used through the R-claim (`runTerm_spec`, about the port's repaired explorer).
* The single claim about the explorer used: `runTerm_spec` (from `exploreM_spec_of_not_exhausted`
  and `term_iff_sem`): a run of the repaired explorer that reports no exhaustion reports exactly
  the terminal executions, without repetition.
-/

namespace Must

namespace Ind

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)]

/-- The hypotheses of the end theorem (plan Section 6). -/
structure CheckHyp (S : MPSetting Q) (consB : Graph Q → Bool) {A : Type} [DecidableEq A]
    (Abs : SAbs S A) (Bad : Set (Graph Q)) (abad : A → Bool) (B : List A) (K : ℕ)
    (f : A → Graph Q → A) : Prop where
  /-- a decision procedure of the model on `Supp` graphs -/
  hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ (Model.ofSet S.ms).cons H)
  /-- `Bad` is α-determined by `abad` -/
  hdet : ∀ G, ExecM (Model.ofSet S.ms) S.P G → (G ∈ Bad ↔ abad (Abs.α G) = true)
  /-- `Bad` is extension-closed -/
  hext : ∀ G G', ExecM (Model.ofSet S.ms) S.P G → ExecM (Model.ofSet S.ms) S.P G' →
    G ∈ Bad → G.IsPrefixOf G' → G' ∈ Bad
  /-- the initial value is in `B` -/
  hinit : Abs.α Graph.empty ∈ B
  /-- `B` and `abad` are disjoint -/
  hdisj : ∀ b ∈ B, abad b = false
  /-- `K ≥ 1` -/
  hK : 1 ≤ K
  /-- `f` computes the value of a composition, for every seeds -/
  hf : ∀ G, ExecM (Model.ofSet S.ms) S.P G → Abs.α G ∈ B →
    ∀ ρ, SeedOK G S.m (Abs.W (Abs.α G)) ρ S.ord →
    ∀ H, Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m G.trace (Abs.W (Abs.α G)))
        (Abs.W (Abs.α G)) H →
      H.len S.ts (Abs.W (Abs.α G)) ≤ K →
      f (Abs.α G) H = Abs.α (G.scomp H (Abs.W (Abs.α G)) ρ)

omit [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
/-- A program without threads takes no step. -/
theorem stepsN_of_threads_nil {M : Model Q} {P : Program Q} (hP : P.threads = []) {n : ℕ}
    {G G' : Graph Q} (h : StepsN M P n G G') : n = 0 ∧ G = G' := by
  induction n generalizing G' with
  | zero => exact ⟨rfl, h⟩
  | succ n _ =>
    obtain ⟨_, _, e, _, _, hop, _⟩ := h
    have := hop.1
    unfold Model.availM at this
    rw [hP] at this
    cases this

variable {S : MPSetting Q} {consB : Graph Q → Bool} {A : Type} [DecidableEq A]
  {Abs : SAbs S A} {Bad : Set (Graph Q)} {abad : A → Bool} {B : List A} {K : ℕ}
  {f : A → Graph Q → A} {T : Sel Q}

omit [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
/-- The tests of the check, with `hf`, are the conditions of thm:mp-terminal. -/
theorem checkOK_iff (h : CheckHyp S consB Abs Bad abad B K f) {G : Graph Q}
    (hG : ExecM (Model.ofSet S.ms) S.P G) (hb : Abs.α G ∈ B) {ρ : Ev Q → Ev Q}
    (hρ : SeedOK G S.m (Abs.W (Abs.α G)) ρ S.ord) {κ : Tid → ℕ}
    (hκ : Trust.IsBudget S.P.threads K κ) {F : Graph Q}
    (hF : Term (Model.ofSet S.ms) (Abs.budgetProg (Abs.α G) κ) F) :
    checkOK S B abad Abs.W f K (Abs.α G) F = true ↔
      (F.len S.ts (Abs.W (Abs.α G)) = K → Abs.α (G.scomp F (Abs.W (Abs.α G)) ρ) ∈ B) ∧
      (F.len S.ts (Abs.W (Abs.α G)) < K →
        abad (Abs.α (G.scomp F (Abs.W (Abs.α G)) ρ)) = false) := by
  obtain ⟨hu, -, -⟩ := Abs.hconf G hG
  obtain ⟨hFF, hFK, -⟩ := Abs.cover_frag ⟨G, hG, rfl⟩ hκ hF
  have hres : Abs.res (Abs.α G) = S.P.seedRes S.ι S.hι S.m G.trace (Abs.W (Abs.α G)) :=
    seedRes_congr hu
  have hFF' := hFF
  rw [hres] at hFF'
  have hfF := h.hf G hG hb ρ hρ F hFF' hFK
  unfold checkOK
  rw [hfF]
  by_cases hl : F.len S.ts (Abs.W (Abs.α G)) = K
  · rw [ite_eq_left hl, decide_eq_true_iff]
    exact ⟨fun h1 => ⟨fun _ => h1, fun h2 => absurd hl (Nat.ne_of_lt h2)⟩, fun h1 => h1.1 hl⟩
  · rw [ite_eq_right hl, Bool.not_eq_true']
    exact ⟨fun h1 => ⟨fun h2 => absurd h2 hl, fun _ => h1⟩,
      fun h1 => h1.2 (lt_of_le_of_ne hFK hl)⟩

/-- Acceptance gives `K`-inductivity (thm:mp-reduction (2), thm:mp-terminal). -/
theorem checkS_kinductive {fuel : ℕ} (h : CheckHyp S consB Abs Bad abad B K f)
    (hacc : (CheckS consB T fuel S B abad Abs.u Abs.W f K).1 = true) :
    Abs.KInductive {a | abad a = true} {a | a ∈ B} K := by
  rw [checkS_fst, Bool.and_eq_true] at hacc
  obtain ⟨htests, hexh⟩ := hacc
  have htests' := List.all_eq_true.mp htests
  have hexh' := List.all_eq_true.mp hexh
  refine ⟨h.hinit, fun G hG hb => ?_⟩
  have hb' : Abs.α G ∈ B := hb
  obtain ⟨-, -, ρ, hρ⟩ := Abs.hconf G hG
  by_cases hne : S.P.threads = []
  · refine ⟨fun G' hs => ?_, fun j _ G' hs => ?_⟩
    · have := (stepsN_of_threads_nil hne hs).1
      have := h.hK
      omega
    · obtain ⟨-, rfl⟩ := stepsN_of_threads_nil hne hs
      change ¬ abad (Abs.α G) = true
      rw [h.hdisj _ hb']
      exact Bool.false_ne_true
  · have hdet : Abs.Determines Bad {a | abad a = true} := h.hdet
    have hdisj : Disjoint {a | a ∈ B} {a | abad a = true} :=
      Set.disjoint_left.mpr fun a ha hab => by
        change abad a = true at hab
        rw [h.hdisj a ha] at hab
        exact Bool.false_ne_true hab
    refine (Abs.stepOK_iff_fragOK hG hρ).mpr
      ((Abs.fragOK_iff_term hne hdet h.hext hdisj hG hb hρ).mpr fun κ hκ F hF => ?_)
    have hx : (Abs.α G, runTerm consB T fuel (budgetProgOf S Abs.u Abs.W (Abs.α G) κ)) ∈
        checkRuns consB T fuel S B Abs.u Abs.W K := mem_checkRuns.mpr ⟨_, hb', κ, hκ, rfl⟩
    have hex := hexh' _ hx
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hex
    obtain ⟨-, hmem⟩ := runTerm_spec h.hc (trunc_bounded_sum _ _) hex
    have hok := List.all_eq_true.mp (htests' _ hx) F ((hmem F).mpr hF)
    obtain ⟨h1, h2⟩ := (checkOK_iff h hG hb' hρ hκ hF).mp hok
    refine ⟨h1, fun hl hab => ?_⟩
    change abad _ = true at hab
    rw [h2 hl] at hab
    exact Bool.false_ne_true hab

/-- Acceptance gives safety (the end theorem, plan Section 6). -/
theorem checkS_sound {fuel : ℕ} (h : CheckHyp S consB Abs Bad abad B K f)
    (hacc : (CheckS consB T fuel S B abad Abs.u Abs.W f K).1 = true) :
    Safe (Model.ofSet S.ms) S.P Bad :=
  Abs.ksound (Abad := {a | abad a = true}) h.hK h.hdet (checkS_kinductive h hacc)

omit [DecidableEq A] in
/-- The end theorem with the hypotheses spelled out (plan Section 6). -/
theorem checkS_sound_explicit (S : MPSetting Q) (consB : Graph Q → Bool)
    (hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ (Model.ofSet S.ms).cons H)) (T : Sel Q)
    {A : Type} [DecidableEq A] (Abs : SAbs S A)
    (Bad : Set (Graph Q)) (abad : A → Bool)
    (hdet : ∀ G, ExecM (Model.ofSet S.ms) S.P G → (G ∈ Bad ↔ abad (Abs.α G) = true))
    (hext : ∀ G G', ExecM (Model.ofSet S.ms) S.P G → ExecM (Model.ofSet S.ms) S.P G' →
      G ∈ Bad → G.IsPrefixOf G' → G' ∈ Bad)
    (B : List A) (hinit : Abs.α Graph.empty ∈ B) (hdisj : ∀ b ∈ B, abad b = false)
    (K : ℕ) (hK : 1 ≤ K) (f : A → Graph Q → A)
    (hf : ∀ G, ExecM (Model.ofSet S.ms) S.P G → Abs.α G ∈ B →
      ∀ ρ, SeedOK G S.m (Abs.W (Abs.α G)) ρ S.ord →
      ∀ H, Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m G.trace (Abs.W (Abs.α G)))
          (Abs.W (Abs.α G)) H →
        H.len S.ts (Abs.W (Abs.α G)) ≤ K →
        f (Abs.α G) H = Abs.α (G.scomp H (Abs.W (Abs.α G)) ρ))
    (fuel : ℕ) (hacc : (CheckS consB T fuel S B abad Abs.u Abs.W f K).1 = true) :
    Safe (Model.ofSet S.ms) S.P Bad :=
  checkS_sound ⟨hc, hdet, hext, hinit, hdisj, hK, hf⟩ hacc

/-- The analogue of cor:enum (2): for realised values and a `K`-inductive set, the check accepts
with every large fuel. -/
theorem checkS_accepts (h : CheckHyp S consB Abs Bad abad B K f)
    (hreal : ∀ b ∈ B, Abs.Realised b)
    (hkind : Abs.KInductive {a | abad a = true} {a | a ∈ B} K) :
    ∃ N, ∀ fuel, N ≤ fuel → (CheckS consB T fuel S B abad Abs.u Abs.W f K).1 = true := by
  obtain ⟨N, hN⟩ := checkS_fuel (B := B) (u := Abs.u) (W := Abs.W) (K := K) (T := T) h.hc
  refine ⟨N, fun fuel hfuel => ?_⟩
  rw [checkS_fst, Bool.and_eq_true]
  refine ⟨List.all_eq_true.mpr fun x hx => List.all_eq_true.mpr fun F hF => ?_, hN fuel hfuel⟩
  obtain ⟨b, hb, κ, hκ, rfl⟩ := mem_checkRuns.mp hx
  have hex := List.all_eq_true.mp (hN fuel hfuel) _ hx
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hex
  obtain ⟨-, hmem⟩ := runTerm_spec h.hc (trunc_bounded_sum _ _) hex
  have hT := (hmem F).mp hF
  obtain ⟨G, hG, rfl⟩ := hreal b hb
  obtain ⟨-, -, ρ, hρ⟩ := Abs.hconf G hG
  have hok := (Abs.stepOK_iff_fragOK hG hρ).mp (hkind.2 G hG hb)
  obtain ⟨hFF, -, -⟩ := Abs.cover_frag ⟨G, hG, rfl⟩ hκ hT
  obtain ⟨h1, h2⟩ := hok F hFF
  refine (checkOK_iff h hG hb hρ hκ hT).mpr ⟨h1, fun hl => ?_⟩
  have := h2 hl
  change ¬ abad _ = true at this
  exact Bool.not_eq_true _ ▸ this

/-! ### Instances -/

theorem hc_asyn : ∀ H : Graph Q, H.Supp →
    (Graph.consAsynB H = true ↔ (Model.asyn : Model Q).cons H) := fun _ hH =>
  (consAsynB_iff hH).trans Model.asyn_cons_iff.symm

theorem hc_p2p : ∀ H : Graph Q, H.Supp →
    (Graph.consAPB H = true ↔ (Model.p2p : Model Q).cons H) := fun _ hH =>
  (consAPB_iff hH).trans Model.p2p_cons_iff.symm

section Asyn

variable {P : Program Q} {ν : Tid} {hν : ν ∉ P.threads} {hP : P.Tagged .asyn}
  {α : Graph Q → A} {u : A → Tid → List (Option Val)} {w : A → List Msg}
  {hconf : ∀ G, ExecM Model.asyn P G →
    (∀ t ∈ P.threads, FutEq (P.step t) (u (α G) t) (G.trace t)) ∧
      (↑(w (α G)) : Multiset Msg) = G.pendM}

/-- The hypotheses of Section 6 give `CheckHyp`. -/
theorem checkHyp_asyn
    (hdet : ∀ G, ExecM Model.asyn P G → (G ∈ Bad ↔ abad (α G) = true))
    (hext : ∀ G G', ExecM Model.asyn P G → ExecM Model.asyn P G' → G ∈ Bad →
      G.IsPrefixOf G' → G' ∈ Bad)
    (hinit : α Graph.empty ∈ B) (hdisj : ∀ b ∈ B, abad b = false) (hK : 1 ≤ K)
    (hf : ∀ G, ExecM Model.asyn P G → α G ∈ B → ∀ σ, IsPendEnum G σ → word σ = w (α G) →
      ∀ H, Frag Model.asyn (P.envRes ν hν G.trace (word σ)) (envW ν (word σ)) H →
        H.len (P.threads ++ [ν]) (envW ν (word σ)) ≤ K → f (α G) H = α (compEnv G ν σ H)) :
    CheckHyp (envSetting P ν hν hP) Graph.consAsynB (asynAbs P ν hν hP α u w hconf) Bad abad B
      K f := by
  refine ⟨hc_asyn, hdet, hext, hinit, hdisj, hK, fun G hG hb ρ hρ H hH hl => ?_⟩
  obtain ⟨σ, hσ, hw, he⟩ := seedOK_env_enum (hν := hν) (w := w (α G)) hG hP hρ
  change f (α G) H = α (G.scomp H (envW ν (w (α G))) ρ)
  rw [he G.trace H hH]
  have hH' : Frag Model.asyn (P.envRes ν hν G.trace (word σ)) (envW ν (word σ)) H := by
    rw [hw]
    exact hH
  have hl' : H.len (P.threads ++ [ν]) (envW ν (word σ)) ≤ K := by
    rw [hw]
    exact hl
  exact hf G hG hb σ hσ hw H hH' hl'

/-- Section 6: acceptance gives `K`-inductivity. -/
theorem checkAsyn_kinductive
    (hdet : ∀ G, ExecM Model.asyn P G → (G ∈ Bad ↔ abad (α G) = true))
    (hext : ∀ G G', ExecM Model.asyn P G → ExecM Model.asyn P G' → G ∈ Bad →
      G.IsPrefixOf G' → G' ∈ Bad)
    (hinit : α Graph.empty ∈ B) (hdisj : ∀ b ∈ B, abad b = false) (hK : 1 ≤ K)
    (hf : ∀ G, ExecM Model.asyn P G → α G ∈ B → ∀ σ, IsPendEnum G σ → word σ = w (α G) →
      ∀ H, Frag Model.asyn (P.envRes ν hν G.trace (word σ)) (envW ν (word σ)) H →
        H.len (P.threads ++ [ν]) (envW ν (word σ)) ≤ K → f (α G) H = α (compEnv G ν σ H))
    (fuel : ℕ)
    (hacc : (CheckS Graph.consAsynB T fuel (envSetting P ν hν hP) B abad u
      (fun b => envW ν (w b)) f K).1 = true) :
    (asynAbs P ν hν hP α u w hconf).KInductive {a | abad a = true} {a | a ∈ B} K :=
  checkS_kinductive (checkHyp_asyn hdet hext hinit hdisj hK hf) hacc

/-- Section 6 (thm:mp-reduction, thm:mp-terminal, para mp:329): acceptance gives safety under
`asyn`. -/
theorem checkAsyn_sound (P : Program Q) (ν : Tid) (hν : ν ∉ P.threads) (hP : P.Tagged .asyn)
    (T : Sel Q) (α : Graph Q → A) (u : A → Tid → List (Option Val)) (w : A → List Msg)
    (hconf : ∀ G, ExecM Model.asyn P G →
      (∀ t ∈ P.threads, FutEq (P.step t) (u (α G) t) (G.trace t)) ∧
        (↑(w (α G)) : Multiset Msg) = G.pendM)
    (Bad : Set (Graph Q)) (abad : A → Bool)
    (hdet : ∀ G, ExecM Model.asyn P G → (G ∈ Bad ↔ abad (α G) = true))
    (hext : ∀ G G', ExecM Model.asyn P G → ExecM Model.asyn P G' → G ∈ Bad →
      G.IsPrefixOf G' → G' ∈ Bad)
    (B : List A) (hinit : α Graph.empty ∈ B) (hdisj : ∀ b ∈ B, abad b = false)
    (K : ℕ) (hK : 1 ≤ K) (f : A → Graph Q → A)
    (hf : ∀ G, ExecM Model.asyn P G → α G ∈ B → ∀ σ, IsPendEnum G σ → word σ = w (α G) →
      ∀ H, Frag Model.asyn (P.envRes ν hν G.trace (word σ)) (envW ν (word σ)) H →
        H.len (P.threads ++ [ν]) (envW ν (word σ)) ≤ K → f (α G) H = α (compEnv G ν σ H))
    (fuel : ℕ)
    (hacc : (CheckS Graph.consAsynB T fuel (envSetting P ν hν hP) B abad u
      (fun b => envW ν (w b)) f K).1 = true) :
    Safe Model.asyn P Bad :=
  checkS_sound (Abs := asynAbs P ν hν hP α u w hconf)
    (checkHyp_asyn hdet hext hinit hdisj hK hf) hacc

end Asyn

section P2P

variable {P : Program Q} {α : Graph Q → A} {u : A → Tid → List (Option Val)}
  {w : A → Tid → List Msg}

omit [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
/-- The hypotheses of Section 7 (for a setting with `ι = []`, `ord`) give `CheckHyp`. -/
theorem checkHyp_p2p (S : MPSetting Q) (hS : S.ι = []) (hT : S.ord) (consB : Graph Q → Bool)
    (hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ (Model.ofSet S.ms).cons H))
    {hconf : ∀ G, ExecM (Model.ofSet S.ms) S.P G →
      (∀ t ∈ S.P.threads, FutEq (S.P.step t) (u (α G) t) (G.trace t)) ∧
        ∀ t, w (α G) t = G.pend t}
    (hdet : ∀ G, ExecM (Model.ofSet S.ms) S.P G → (G ∈ Bad ↔ abad (α G) = true))
    (hext : ∀ G G', ExecM (Model.ofSet S.ms) S.P G → ExecM (Model.ofSet S.ms) S.P G' →
      G ∈ Bad → G.IsPrefixOf G' → G' ∈ Bad)
    (hinit : α Graph.empty ∈ B) (hdisj : ∀ b ∈ B, abad b = false) (hK : 1 ≤ K)
    (hf : ∀ G, ExecM (Model.ofSet S.ms) S.P G → α G ∈ B →
      ∀ H, Frag (Model.ofSet S.ms) (S.P.p2pRes S.m G.trace G.pend) G.pend H →
        H.len S.P.threads G.pend ≤ K → f (α G) H = α (compP2P G H)) :
    CheckHyp S consB (p2pAbs S hS hT α u w hconf) Bad abad B K f := by
  refine ⟨hc, hdet, hext, hinit, hdisj, hK, fun G hG hb ρ hρ H hH hl => ?_⟩
  have hw : w (α G) = G.pend := funext (hconf G hG).2
  change f (α G) H = α (G.scomp H (w (α G)) ρ)
  change SeedOK G S.m (w (α G)) ρ S.ord at hρ
  change Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m G.trace (w (α G))) (w (α G)) H at hH
  change H.len S.ts (w (α G)) ≤ K at hl
  rw [hw] at hρ hH hl ⊢
  rw [p2pRes_eq S hS] at hH
  have hρ' : SeedOK G S.m G.pend ρ True := hρ.weaken fun _ => hT
  rw [scomp_eq_compP2P S hS hG hρ' hH]
  have hts : S.ts = S.P.threads := by
    unfold MPSetting.ts
    rw [hS, List.append_nil]
  rw [hts] at hl
  exact hf G hG hb H hH hl

/-- Section 7: acceptance gives `K`-inductivity under `p2p`. -/
theorem checkP2P_kinductive (hP : P.Tagged .p2p)
    {hconf : ∀ G, ExecM Model.p2p P G →
      (∀ t ∈ P.threads, FutEq (P.step t) (u (α G) t) (G.trace t)) ∧ ∀ t, w (α G) t = G.pend t}
    (hdet : ∀ G, ExecM Model.p2p P G → (G ∈ Bad ↔ abad (α G) = true))
    (hext : ∀ G G', ExecM Model.p2p P G → ExecM Model.p2p P G' → G ∈ Bad → G.IsPrefixOf G' →
      G' ∈ Bad)
    (hinit : α Graph.empty ∈ B) (hdisj : ∀ b ∈ B, abad b = false) (hK : 1 ≤ K)
    (hf : ∀ G, ExecM Model.p2p P G → α G ∈ B →
      ∀ H, Frag Model.p2p (P.p2pRes .p2p G.trace G.pend) G.pend H →
        H.len P.threads G.pend ≤ K → f (α G) H = α (compP2P G H))
    (fuel : ℕ)
    (hacc : (CheckS Graph.consAPB T fuel (p2pSetting P hP) B abad u w f K).1 = true) :
    (p2pAbs (p2pSetting P hP) rfl trivial α u w hconf).KInductive {a | abad a = true}
      {a | a ∈ B} K :=
  checkS_kinductive (checkHyp_p2p (p2pSetting P hP) rfl trivial _ hc_p2p hdet hext hinit hdisj hK
    hf) hacc

/-- Section 7 (thm:p2p): acceptance gives safety under `p2p`. -/
theorem checkP2P_sound (P : Program Q) (hP : P.Tagged .p2p) (T : Sel Q)
    (α : Graph Q → A) (u : A → Tid → List (Option Val)) (w : A → Tid → List Msg)
    (hconf : ∀ G, ExecM Model.p2p P G →
      (∀ t ∈ P.threads, FutEq (P.step t) (u (α G) t) (G.trace t)) ∧ ∀ t, w (α G) t = G.pend t)
    (Bad : Set (Graph Q)) (abad : A → Bool)
    (hdet : ∀ G, ExecM Model.p2p P G → (G ∈ Bad ↔ abad (α G) = true))
    (hext : ∀ G G', ExecM Model.p2p P G → ExecM Model.p2p P G' → G ∈ Bad → G.IsPrefixOf G' →
      G' ∈ Bad)
    (B : List A) (hinit : α Graph.empty ∈ B) (hdisj : ∀ b ∈ B, abad b = false)
    (K : ℕ) (hK : 1 ≤ K) (f : A → Graph Q → A)
    (hf : ∀ G, ExecM Model.p2p P G → α G ∈ B →
      ∀ H, Frag Model.p2p (P.p2pRes .p2p G.trace G.pend) G.pend H →
        H.len P.threads G.pend ≤ K → f (α G) H = α (compP2P G H))
    (fuel : ℕ)
    (hacc : (CheckS Graph.consAPB T fuel (p2pSetting P hP) B abad u w f K).1 = true) :
    Safe Model.p2p P Bad :=
  checkS_sound (Abs := p2pAbs (p2pSetting P hP) rfl trivial α u w hconf)
    (checkHyp_p2p (p2pSetting P hP) rfl trivial _ hc_p2p hdet hext hinit hdisj hK hf) hacc

/-- rem:p2p-scope (i): acceptance gives `K`-inductivity for the Section 7 construction under
`asyn`. -/
theorem checkP2PAsyn_kinductive (hP : P.Tagged .asyn)
    {hconf : ∀ G, ExecM Model.asyn P G →
      (∀ t ∈ P.threads, FutEq (P.step t) (u (α G) t) (G.trace t)) ∧ ∀ t, w (α G) t = G.pend t}
    (hdet : ∀ G, ExecM Model.asyn P G → (G ∈ Bad ↔ abad (α G) = true))
    (hext : ∀ G G', ExecM Model.asyn P G → ExecM Model.asyn P G' → G ∈ Bad → G.IsPrefixOf G' →
      G' ∈ Bad)
    (hinit : α Graph.empty ∈ B) (hdisj : ∀ b ∈ B, abad b = false) (hK : 1 ≤ K)
    (hf : ∀ G, ExecM Model.asyn P G → α G ∈ B →
      ∀ H, Frag Model.asyn (P.p2pRes .asyn G.trace G.pend) G.pend H →
        H.len P.threads G.pend ≤ K → f (α G) H = α (compP2P G H))
    (fuel : ℕ)
    (hacc : (CheckS Graph.consAsynB T fuel (p2pAsynSetting P hP) B abad u w f K).1 = true) :
    (p2pAbs (p2pAsynSetting P hP) rfl trivial α u w hconf).KInductive {a | abad a = true}
      {a | a ∈ B} K :=
  checkS_kinductive (checkHyp_p2p (p2pAsynSetting P hP) rfl trivial _ hc_asyn hdet hext hinit
    hdisj hK hf) hacc

/-- rem:p2p-scope (i): acceptance gives safety for the Section 7 construction under `asyn`. -/
theorem checkP2PAsyn_sound (P : Program Q) (hP : P.Tagged .asyn) (T : Sel Q)
    (α : Graph Q → A) (u : A → Tid → List (Option Val)) (w : A → Tid → List Msg)
    (hconf : ∀ G, ExecM Model.asyn P G →
      (∀ t ∈ P.threads, FutEq (P.step t) (u (α G) t) (G.trace t)) ∧ ∀ t, w (α G) t = G.pend t)
    (Bad : Set (Graph Q)) (abad : A → Bool)
    (hdet : ∀ G, ExecM Model.asyn P G → (G ∈ Bad ↔ abad (α G) = true))
    (hext : ∀ G G', ExecM Model.asyn P G → ExecM Model.asyn P G' → G ∈ Bad → G.IsPrefixOf G' →
      G' ∈ Bad)
    (B : List A) (hinit : α Graph.empty ∈ B) (hdisj : ∀ b ∈ B, abad b = false)
    (K : ℕ) (hK : 1 ≤ K) (f : A → Graph Q → A)
    (hf : ∀ G, ExecM Model.asyn P G → α G ∈ B →
      ∀ H, Frag Model.asyn (P.p2pRes .asyn G.trace G.pend) G.pend H →
        H.len P.threads G.pend ≤ K → f (α G) H = α (compP2P G H))
    (fuel : ℕ)
    (hacc : (CheckS Graph.consAsynB T fuel (p2pAsynSetting P hP) B abad u w f K).1 = true) :
    Safe Model.asyn P Bad :=
  checkS_sound (Abs := p2pAbs (p2pAsynSetting P hP) rfl trivial α u w hconf)
    (checkHyp_p2p (p2pAsynSetting P hP) rfl trivial _ hc_asyn hdet hext hinit hdisj hK hf) hacc

end P2P

end Ind

end Must
