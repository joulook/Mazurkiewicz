import Mazurkiewicz.Induction.MP.P2PDefs

/-!
# ex:p2p under `p2p`: the run, `K`-inductivity, safety (milestone C10b)

`induction-popl`, `p2p.tex` ex:p2p (p2p:239-258), plan `plan/ind/TRACK-C-PLAN.md`, milestone
C10b. The check `CheckS` (C8a) under `p2pSetting pq` with `Graph.consAPB`, `Sel.least`, fuel
`200`, evaluated in the kernel (`decide +kernel`).

* `pq_check6`: `{(a₀, c₀, ε, ε)}` with `K = 6` gives `(true, 7)`: seven budgets of size `6`,
  one terminal execution each (p2p:243-252), no run exhausted.
* `pq_kind6`: `{(a₀, c₀, ε, ε)}` is `6`-inductive under `p2p` (p2p:239).
* `pq_safe`: no consistent execution of `pq` under `p2p` has an error event (p2p:257-258).
-/

namespace Must

namespace Ind

/-- The check of ex:p2p under `p2p`. -/
abbrev pqCheck (K : ℕ) : Bool × ℕ :=
  CheckS Graph.consAPB Sel.least 200 (p2pSetting pq pq_tagged) pqB pqAbad pqU pqW pqF K

/-- p2p:257: seven tests, all passing. -/
theorem pq_check6 : pqCheck 6 = (true, 7) := by decide +kernel

/-- The abstraction of ex:p2p as an abstraction of Section 7. -/
abbrev pqAbs : SAbs (p2pSetting pq pq_tagged) PQVal :=
  p2pAbs (p2pSetting pq pq_tagged) rfl trivial pqAlpha pqU pqW pq_hconf

/-- p2p:239: `{(a₀, c₀, ε, ε)}` is `6`-inductive under `p2p`. -/
theorem pq_kind6 : pqAbs.KInductive {a | pqAbad a = true} {a | a ∈ pqB} 6 :=
  checkP2P_kinductive (hconf := pq_hconf) pq_tagged pq_hdet pq_hext pq_hinit pq_hdisj (by decide)
    pq_hf 200 (congrArg Prod.fst pq_check6)

/-- p2p:257-258: the program has no error under `p2p`. -/
theorem pq_safe : Safe Model.p2p pq BadErr :=
  checkP2P_sound pq pq_tagged Sel.least pqAlpha pqU pqW pq_hconf BadErr pqAbad pq_hdet pq_hext
    pqB pq_hinit pq_hdisj 6 (by decide) pqF pq_hf 200 (congrArg Prod.fst pq_check6)

end Ind

end Must
