import Mazurkiewicz.Induction.MP.P2PDefs

/-!
# ex:p2p under `asyn`: the rejecting run, the count, an unsafe execution (milestone C10c)

`induction-popl`, `p2p.tex` ex:p2p (p2p:260-264), plan `plan/ind/TRACK-C-PLAN.md`, milestone
C10c. The program `pqa` (the machines of ex:p2p, tagged `.asyn`), the Section 6 setting
`envSetting pqa 0` (environment thread `ν = 0`), the Section 6 abstraction functions of
`MP/P2PDefs.lean` (pending messages as a multiset), `B = [(a₀, c₀, ∅)]`, `K = 6`; `CheckS` with
`Graph.consAsynB`, `Sel.least`, fuel `200`, evaluated in the kernel.

* `pqa_check6`: the check gives `(false, 11)`. `pqa_hex`: no run is exhausted. `pqa_fails`: some
  reported terminal execution fails its test (so the `false` comes from a test, not from
  exhaustion).
* `pqa_budgets`, `pqa_runs_ex`, `pqa_runs_len`, `pqa_counts`: the budgets in the order of
  `Trust.budgets`, `(κ 1, κ 2) = (0, 6), (1, 5), …, (6, 0)`, and the number of terminal
  executions of each budget program, `1, 1, 2, 2, 2, 2, 1` (in the paper's order
  `(6, 0), …, (0, 6)`: `1, 2, 2, 2, 2, 1, 1`).
  `pqa_count`: `11` is the number of terminal executions summed over the budgets (by
  `checkS_count`).
* `pqa_unsafe`: an explicit consistent execution under `asyn` with an error event (thread `2`
  reads `m₂ = (2, 2)` first, p2p:262-264); `pqa_not_safe`: `¬ Safe Model.asyn pqa BadErr`.
* The hypotheses of `checkAsyn_sound` hold for `pqa` with the Section 6 abstraction:
  `pqa_hconf`, `pqa_hdet`, `pqa_hext`, `pqa_hinit`, `pqa_hdisj`, `pqa_hf`. With them:
  `pqa_rejects_all_fuel` (the check rejects at every fuel, by `checkAsyn_sound` and
  `pqa_not_safe`) and `pqa_not_kinductive` (no set of values is `K`-inductive for any
  `K ≥ 1`, by `ksound` and `pqa_not_safe`).

What the `false` verdict proves and does not prove. With every run non-exhausted
(`pqa_hex`), `false` means that at least one terminal execution `F` of a budget program fails
its test (`pqa_fails`): `‖F‖ = K` and `f b F ∉ B`, or `‖F‖ < K` and `f b F ∈ Abad`. A rejection
alone does not prove that a program is unsafe: no theorem turns a failing test into an unsafe
execution. With non-exhaustion, the checker hypotheses (`CheckHyp`) and realisability of the
values of `B`, a failing test does refute `K`-inductivity of `B` (the proof of
`checkS_accepts` derives from realisability and `K`-inductivity that every reported terminal
execution passes; its fuel bound only serves to obtain non-exhaustion, which `pqa_hex` gives
directly). Here the stronger facts are proved outright: unsafety by `pqa_unsafe`, and from it
`pqa_rejects_all_fuel` and `pqa_not_kinductive`.
-/

namespace Must

namespace Ind

/-- The setting of C10c. -/
abbrev pqaS : MPSetting VPred := envSetting pqa 0 pqa_hν pqa_tagged

/-- The seed words of C10c. -/
abbrev pqaW (b : PQAVal) : Tid → List Msg := envW 0 (pqaWord b)

/-- The check of ex:p2p under `asyn`. -/
abbrev pqaCheck (K : ℕ) : Bool × ℕ :=
  CheckS Graph.consAsynB Sel.least 200 pqaS pqaB pqaAbad pqaU pqaW pqaF K

/-- p2p:260: under `asyn` the same check fails; eleven tests. -/
theorem pqa_check6 : pqaCheck 6 = (false, 11) := by decide +kernel

/-- No run of the check is exhausted. -/
theorem pqa_hex :
    (checkRuns Graph.consAsynB Sel.least 200 pqaS pqaB pqaU pqaW 6).all
      (fun x => !x.2.exhausted) = true := by decide +kernel

/-- Some reported terminal execution fails its test. -/
theorem pqa_fails :
    (checkRuns Graph.consAsynB Sel.least 200 pqaS pqaB pqaU pqaW 6).all
      (fun x => (x.2.reported.map Config.G).all (checkOK pqaS pqaB pqaAbad pqaW pqaF 6 x.1)) =
      false := by decide +kernel

/-- The budgets of size `6`, in the order of `Trust.budgets`. -/
theorem pqa_budgets : (Trust.budgets pqa.threads 6).map (fun κ => (κ 1, κ 2)) =
    [(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1), (6, 0)] := by decide +kernel

/-- The runs of the budget programs of `(a₀, c₀, ∅)` are not exhausted. -/
theorem pqa_runs_ex : ∀ κ ∈ Trust.budgets pqa.threads 6,
    (runTerm Graph.consAsynB Sel.least 200
      (budgetProgOf pqaS pqaU pqaW (.a0, .c0, 0) κ)).exhausted = false := by decide +kernel

/-- The number of reported executions per budget. -/
theorem pqa_runs_len :
    ((Trust.budgets pqa.threads 6).map fun κ => (runTerm Graph.consAsynB Sel.least 200
      (budgetProgOf pqaS pqaU pqaW (.a0, .c0, 0) κ)).reported.length) =
      [1, 1, 2, 2, 2, 2, 1] := by decide +kernel

/-- The number of terminal executions of each budget program (Lean order `(0, 6), …, (6, 0)`). -/
theorem pqa_counts :
    ((Trust.budgets pqa.threads 6).map fun κ =>
      {F | Term Model.asyn (budgetProgOf pqaS pqaU pqaW (.a0, .c0, 0) κ) F}.ncard) =
      [1, 1, 2, 2, 2, 2, 1] :=
  Eq.trans (List.map_congr_left fun κ hκ =>
    (length_reported_eq hc_asyn (trunc_bounded_sum _ _) (pqa_runs_ex κ hκ)).symm) pqa_runs_len

/-- The count `11` is the number of terminal executions summed over the budgets
(`checkS_count`). -/
theorem pqa_count :
    (pqaB.map fun b => ((Trust.budgets pqa.threads 6).map fun κ =>
      {F | Term Model.asyn (budgetProgOf pqaS pqaU pqaW b κ) F}.ncard).sum).sum = 11 :=
  (checkS_count (abad := pqaAbad) (f := pqaF) hc_asyn pqa_hex).symm.trans
    (congrArg Prod.snd pqa_check6)

/-! ### An unsafe execution -/

/-- Thread `1` sends `m₁ = (2, 1)` and `m₂ = (2, 2)`; thread `2` reads `m₂` first and then
performs its error action; `m₁` stays pending (p2p:262-264). -/
def pqaBadG : Graph VPred where
  events := {⟨1, 0, .send .asyn 2 1⟩, ⟨1, 1, .send .asyn 2 2⟩, ⟨2, 0, .recv ⟨.asyn, true⟩ .any⟩,
    ⟨2, 1, .error⟩}
  rf := fun e => if e = ⟨2, 0, .recv ⟨.asyn, true⟩ .any⟩ then some (.snd ⟨1, 1, .send .asyn 2 2⟩)
    else none
  nd := fun _ => none

/-- p2p:262-264: ex:p2p has an error under `asyn`. -/
theorem pqa_unsafe : ∃ G, ExecM Model.asyn pqa G ∧ G ∈ BadErr := by
  have hS : pqaBadG.Supp := by
    intro e he
    refine ⟨?_, rfl⟩
    change (if e = ⟨2, 0, .recv ⟨.asyn, true⟩ .any⟩ then _ else none) = none
    refine ite_eq_right ?_
    rintro rfl
    exact he (by decide)
  refine ⟨pqaBadG, ⟨by decide +kernel, (hc_asyn pqaBadG hS).mp (by decide +kernel)⟩,
    ⟨⟨2, 1, .error⟩, by decide, rfl⟩⟩

/-- ex:p2p is not safe under `asyn`. -/
theorem pqa_not_safe : ¬ Safe Model.asyn pqa BadErr := fun hs => by
  obtain ⟨G, hG, hb⟩ := pqa_unsafe
  exact hs G (mreach_iff.mpr hG) hb

/-! ### The hypotheses of `checkAsyn_sound` for `pqa` -/

theorem pqa_hconf : ∀ G, ExecM Model.asyn pqa G →
    (∀ t ∈ pqa.threads, FutEq (pqa.step t) (pqaU (pqaAlpha G) t) (G.trace t)) ∧
      (↑(pqaWord (pqaAlpha G)) : Multiset Msg) = G.pendM :=
  envAlpha_hconf (pqRepA_st .asyn) (pqRepC_st .asyn) Model.asyn

theorem pqa_hdet : ∀ G, ExecM Model.asyn pqa G →
    (G ∈ BadErr ↔ pqaAbad (pqaAlpha G) = true) := by
  intro G hG
  rw [pqProg_badErr (Model.asyn.wf _ hG.2) hG.1, pqaAbad, decide_eq_true_eq]
  exact Iff.rfl

theorem pqa_hext : ∀ G G', ExecM Model.asyn pqa G → ExecM Model.asyn pqa G' → G ∈ BadErr →
    G.IsPrefixOf G' → G' ∈ BadErr := fun _ _ _ _ hb hp => badErr_ext hb hp

theorem pqa_hinit : pqaAlpha Graph.empty ∈ pqaB := by decide +kernel

theorem pqa_hdisj : ∀ b ∈ pqaB, pqaAbad b = false := by decide +kernel

theorem pqa_hf {B : List PQAVal} {K : ℕ} :
    ∀ G, ExecM Model.asyn pqa G → pqaAlpha G ∈ B → ∀ σ, IsPendEnum G σ →
      word σ = pqaWord (pqaAlpha G) →
      ∀ H, Frag Model.asyn (pqa.envRes 0 pqa_hν G.trace (word σ)) (envW 0 (word σ)) H →
        H.len (pqa.threads ++ [0]) (envW 0 (word σ)) ≤ K →
        pqaF (pqaAlpha G) H = pqaAlpha (compEnv G 0 σ H) :=
  envF_hf (A := {b | b ∈ B}) (K := K) pqa_hν pqa_tagged

/-- The check rejects at every fuel (`checkAsyn_sound` and `pqa_not_safe`). -/
theorem pqa_rejects_all_fuel (fuel : ℕ) :
    (CheckS Graph.consAsynB Sel.least fuel pqaS pqaB pqaAbad pqaU pqaW pqaF 6).1 = false := by
  by_contra hne
  exact pqa_not_safe (checkAsyn_sound pqa 0 pqa_hν pqa_tagged Sel.least pqaAlpha pqaU pqaWord
    pqa_hconf BadErr pqaAbad pqa_hdet pqa_hext pqaB pqa_hinit pqa_hdisj 6 (by decide) pqaF
    pqa_hf fuel (Bool.eq_true_of_not_eq_false hne))

/-- The abstraction of C10c as an abstraction of Section 6. -/
abbrev pqaAbs : SAbs pqaS PQAVal :=
  asynAbs pqa 0 pqa_hν pqa_tagged pqaAlpha pqaU pqaWord pqa_hconf

/-- No set of values is `K`-inductive for `K ≥ 1` (`ksound` and `pqa_not_safe`); in particular
not `{(a₀, c₀, ∅)}` for `K = 6`. -/
theorem pqa_not_kinductive (B : Set PQAVal) {K : ℕ} (hK : 1 ≤ K) :
    ¬ pqaAbs.KInductive {a | pqaAbad a = true} B K := fun h =>
  pqa_not_safe (pqaAbs.ksound (Abad := {a | pqaAbad a = true}) hK pqa_hdet h)

end Ind

end Must
