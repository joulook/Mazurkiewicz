import Mazurkiewicz.Induction.MP.PingPongDefs

/-!
# ex:pingpong: the runs, `K`-inductivity, safety (milestone C9b)

`induction-popl`, `mp.tex` ex:pingpong, plan `plan/ind/TRACK-C-PLAN.md`, milestone C9b. The
check `CheckS` (C8a) under `envSetting pp 0` with `Graph.consAsynB`, `Sel.least`, fuel `200`,
seed words `envW 0 (ppWord b)`, evaluated in the kernel (`decide +kernel`).

* `pp_check5`: `{(a₀, c₀, ∅)}` with `K = 5` gives `(true, 6)`: six budgets of size `5`, one
  terminal execution each (mp:368-376), no run exhausted. `pp_kind5`: `{(a₀, c₀, ∅)}` is
  `5`-inductive (mp:364).
* `pp_check1`: `B₅` with `K = 1` gives `(true, 10)`: five values, two budgets of size `1`
  each, one terminal execution per run. `pp_kind1`: `B₅` is `1`-inductive (mp:355).
* `pp_safe`: no consistent execution of `pp` under `asyn` has an error event (mp:380-381).
-/

namespace Must

namespace Ind

/-- The check of ex:pingpong for the values `B` and the bound `K`. -/
abbrev ppCheck (B : List PPVal) (K : ℕ) : Bool × ℕ :=
  CheckS Graph.consAsynB Sel.least 200 (envSetting pp 0 pp_hν pp_tagged) B ppAbad ppU
    (fun b => envW 0 (ppWord b)) ppF K

/-- mp:368-380: six tests, all passing. -/
theorem pp_check5 : ppCheck ppB1 5 = (true, 6) := by decide +kernel

/-- `B₅`, `K = 1`: ten tests, all passing. -/
theorem pp_check1 : ppCheck ppB5 1 = (true, 10) := by decide +kernel

/-- The abstraction of ex:pingpong as an abstraction of Section 6. -/
abbrev ppAbs : SAbs (envSetting pp 0 pp_hν pp_tagged) PPVal :=
  asynAbs pp 0 pp_hν pp_tagged ppAlpha ppU ppWord pp_hconf

/-- mp:364: `{(a₀, c₀, ∅)}` is `5`-inductive. -/
theorem pp_kind5 : ppAbs.KInductive {a | ppAbad a = true} {a | a ∈ ppB1} 5 :=
  checkAsyn_kinductive (hconf := pp_hconf) pp_hdet pp_hext pp_hinit1 pp_hdisj1 (by decide)
    pp_hf 200 (congrArg Prod.fst pp_check5)

/-- mp:355: `B₅` is `1`-inductive. -/
theorem pp_kind1 : ppAbs.KInductive {a | ppAbad a = true} {a | a ∈ ppB5} 1 :=
  checkAsyn_kinductive (hconf := pp_hconf) pp_hdet pp_hext pp_hinit5 pp_hdisj5 le_rfl
    pp_hf 200 (congrArg Prod.fst pp_check1)

/-- mp:380-381: no execution of ex:pingpong, of any length, contains an error. -/
theorem pp_safe : Safe Model.asyn pp BadErr :=
  checkAsyn_sound pp 0 pp_hν pp_tagged Sel.least ppAlpha ppU ppWord pp_hconf BadErr ppAbad
    pp_hdet pp_hext ppB1 pp_hinit1 pp_hdisj1 5 (by decide) ppF pp_hf 200
    (congrArg Prod.fst pp_check5)

end Ind

end Must
