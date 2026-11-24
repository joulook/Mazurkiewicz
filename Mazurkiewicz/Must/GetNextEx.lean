import Mazurkiewicz.Must.CompleteM
import Mazurkiewicz.Must.AlgEx

/-!
# Examples of M7: `ProductionSequence` on `pFuel` and Example 4.1, the printed domain

Program `pFuel` (`Examples.lean`, threads in the order `T0, T1, T2`):
`T0: a = send(T1, 0)`, `T1: r = recv(); c = send(T0, 0)`, `T2: b = send(T1, 1)`.
Model `Model.p2p` decided by M2's `consAPB` (`AP`); tie-break `tieL` (least identity), which
satisfies Q9 (`hT`). Its two terminal graphs are `gA = {a, r ↦ a, c, b}` and
`gF = {a, b, r ↦ b, c}`.

* `prodSeq_gA`: `ProductionSequence(gA)` is four Case-1 calls; the configurations are
  `a`; `a, r ↦ a`; `a, r ↦ a, c`; `a, r ↦ a, c, b`.
* `prodSeq_gF`: `ProductionSequence(gF)`: Case 1 adds `a`; then `GetNext({a}, gF)` is Case 2
  (`r₀ = r`, `s₀ = b`, `G_p = PrefixExtension({a}, gF, b) = {a}`): the loop defers `r` (calling
  `GetNext({a}, MaxCompletion(G_p, [r]))`, Case 1: `r ↦ a`), defers `c` (`A = [r, c]`, Case 1),
  breaks at `b`; the revisit of `r` by `b` deletes `c` (`Deleted = {c}`, non-empty; `r ::
  delList = [r, c] = A`) and gives `G_n = {a, b, r ↦ b}`; Case 1 adds `c`. The production
  sequence is `a`; `a, r ↦ a`; `a, r ↦ a, c`; the revisit `a, r ↦ b, b`; `a, r ↦ b, b, c`
  (five steps, at most four events). `prodSeq_gF_spec`: the same through `getNext_spec`.
* Example 4.1 (`ex41`, threads `T3, T1, T2`, `T1: send(T3, 1)`, `T2: send(T3, 2)`,
  `T3: recv()`): `prodSeq_ex41_g1` (graph 1, three Case-1 calls) and `prodSeq_ex41_g2` (graph 2:
  Case 1, then Case 2 whose loop defers `R` and breaks at `send(T3, 2)`; the revisit has
  `Deleted = ∅`).
* `getNext_printed_domain_false` (fate row "Algorithm 2: claim ⟨1⟩1 on the printed domain"):
  program `pTwo` (`T0: send(T2, 0)`, `T1: send(T2, 1)`, model `asyn`): `∅ ⊏ {s1}` but
  `next_P(∅) = s0 ∉ {s1}`; `GetNext(∅, {s1})` has no result, and no sequence of algorithmic
  steps from `⟨∅, []⟩` reaches a `G'` with `∅ ⊏ G' ⊑ {s1}`, for every tie-break.
-/

namespace Must

namespace GetNextEx

open MustFast MustFast' Examples AlgEx Graph Relation

/-! ### Helpers (`p2p`, `AP`) -/

/-- Q9 for `tieL` and `p2p` (as `ReplayEx.hT`). -/
theorem hT : TieQ9 Model.p2p tieL := tieQ9_pick (M := Model.p2p) consAPB_iff_p2p .least

theorem nextP_of {P : Program VPred} {G : Graph VPred} {e : Ev VPred} (hS : G.Supp)
    (h : P.nextP AP G = some e) : Model.p2p.nextP P G = some e := by
  rw [← Model.nextP_eq _ consAPB_iff_p2p P hS]
  exact h

theorem pfx_of {P : Program VPred} {G G' : Graph VPred} (hS : G.Supp) (hS' : G'.Supp)
    (h : AP G' = true ∧ P.Exec G' ∧ G'.Closed G.events ∧
      G.key = (G'.restrict G.events).key) : Pfx Model.p2p P G G' :=
  Pfx.of_isPrefixOf ((consAPB_iff_p2p _ hS').mp h.1) h.2.1
    ⟨G.events, h.2.2.1, (eq_iff_key hS (hS'.restrict _)).mpr h.2.2.2⟩

/-- Case 1 with the source and outcome given. -/
theorem case1_at {P : Program VPred} {c : Config VPred} {Gt : Graph VPred} {e : Ev VPred}
    {src : Option (Src VPred)} {out : Option Val} (hd : CallDom Model.p2p P c Gt e)
    (hsrc : Gt.rf e = src) (hout : Gt.nd e = out)
    (hc1 : ∀ s, src = some (.snd s) → s ∈ c.G.events) :
    GetNext Model.p2p tieL P (.call c Gt) [c.add e src out] (c.add e src out) := by
  subst hsrc hout
  exact getNext_case1_of hd hc1

theorem ne_of_events {G G' : Graph VPred} (h : G.events ≠ G'.events) : G ≠ G' :=
  fun h' => h (h' ▸ rfl)

/-! ### The configurations and graphs of `pFuel` -/

/-- `a, r ↦ a, c, b`. -/
def y4 : Config VPred := y3.add fb none none
/-- The revisit of `r` by `b` in `y4`: `a, r ↦ b, b`. -/
def c4 : Config VPred := (y3.add fb none none).revisitCfg fr fb
/-- `a, r ↦ b, b, c`. -/
def c5 : Config VPred := c4.add fc none none

/-- `gA = {a, r ↦ a, c, b}`. -/
def gA : Graph VPred := y4.G
/-- `gF = {a, b, r ↦ b, c}`. -/
def gF : Graph VPred :=
  (((Graph.empty.addSend fa).addSend fb).addRecv fr (.snd fb)).addSend fc

/-- `G_p = PrefixExtension({a}, gF, b)`. -/
abbrev gP : Graph VPred := prefixExt y1.G gF fb
/-- `MaxCompletion(G_p, [r])`. -/
def X1 : Graph VPred := gP.add fr (some (.snd fa)) none
/-- `MaxCompletion(G_p, [r, c])`. -/
def X2 : Graph VPred := X1.add fc none none

theorem y4_supp : y4.G.Supp := y3_supp.add _ _ _
theorem gA_supp : gA.Supp := y4_supp
theorem gF_supp : gF.Supp := (((supp_empty.add _ _ _).add _ _ _).add _ _ _).add _ _ _
theorem c4_supp : c4.G.Supp := ((y3_supp.add _ _ _).setRF (by decide +kernel) _).restrict _
theorem c5_supp : c5.G.Supp := c4_supp.add _ _ _
theorem gP_supp : gP.Supp := gF_supp.restrict _
theorem X1_supp : X1.Supp := gP_supp.add _ _ _
theorem X2_supp : X2.Supp := X1_supp.add _ _ _

theorem reach_y : ReachM Model.p2p tieL pFuel y1 ∧ ReachM Model.p2p tieL pFuel y2 ∧
    ReachM Model.p2p tieL pFuel y3 := by
  have h0 : ReachM Model.p2p tieL pFuel .init := ReflTransGen.refl
  have h1 : ReachM Model.p2p tieL pFuel y1 :=
    h0.tail (stepM_of_hasSucc h0.sound y1_supp pFuel_checks.1)
  have h2 : ReachM Model.p2p tieL pFuel y2 :=
    h1.tail (stepM_of_hasSucc h1.sound y2_supp pFuel_checks.2.1)
  exact ⟨h1, h2, h2.tail (stepM_of_hasSucc h2.sound y3_supp pFuel_checks.2.2.1)⟩

theorem nexts : pFuel.nextP AP Graph.empty = some fa ∧ pFuel.nextP AP y1.G = some fr ∧
    pFuel.nextP AP y2.G = some fc ∧ pFuel.nextP AP y3.G = some fb ∧
    pFuel.nextP AP c4.G = some fc := by
  decide +kernel

/-! ### `ProductionSequence(gA)`: four Case-1 calls -/

theorem gA_facts : AP gA = true ∧ pFuel.Exec gA ∧ pFuel.Exec Graph.empty ∧
    fa ∈ gA.events ∧ fr ∈ gA.events ∧ fc ∈ gA.events ∧ fb ∈ gA.events ∧
    gA.rf fa = none ∧ gA.nd fa = none ∧ gA.rf fr = some (.snd fa) ∧ gA.nd fr = none ∧
    gA.rf fc = none ∧ gA.nd fc = none ∧ gA.rf fb = none ∧ gA.nd fb = none ∧
    fa ∈ y1.G.events := by
  decide +kernel

theorem gA_pfx1 : AP gA = true ∧ pFuel.Exec gA ∧ gA.Closed y1.G.events ∧
    y1.G.key = (gA.restrict y1.G.events).key := by
  decide +kernel

theorem gA_pfx2 : AP gA = true ∧ pFuel.Exec gA ∧ gA.Closed y2.G.events ∧
    y2.G.key = (gA.restrict y2.G.events).key := by
  decide +kernel

theorem gA_pfx3 : AP gA = true ∧ pFuel.Exec gA ∧ gA.Closed y3.G.events ∧
    y3.G.key = (gA.restrict y3.G.events).key := by
  decide +kernel

theorem gA_ne : Config.init.G.events ≠ gA.events ∧ y1.G.events ≠ gA.events ∧
    y2.G.events ≠ gA.events ∧ y3.G.events ≠ gA.events := by
  decide +kernel

/-- `ProductionSequence(gA)` from `⟨∅, []⟩`: `a`; `a, r ↦ a`; `a, r ↦ a, c`; `a, r ↦ a, c, b`. -/
theorem prodSeq_gA : ProdSeq Model.p2p tieL pFuel gA Config.init [y1, y2, y3, y4] y4 := by
  obtain ⟨h1, h2, h3⟩ := reach_y
  obtain ⟨n0, n1, n2, n3, -⟩ := nexts
  obtain ⟨hc, hE, -, ma, mr, mc, mb, ra, na, rr, nr, rc, nc, rb, nb, ay1⟩ := gA_facts
  have hcA : Model.p2p.cons gA := (consAPB_iff_p2p _ gA_supp).mp hc
  have s0 : GetNext Model.p2p tieL pFuel (.call Config.init gA) [y1] y1 :=
    case1_at ⟨Config.inv_init, Pfx.of_isPrefixOf hcA hE (Graph.empty_isPrefixOf _),
      nextP_of supp_empty n0, ma⟩ ra na (fun _ h => by cases h)
  have s1 : GetNext Model.p2p tieL pFuel (.call y1 gA) [y2] y2 :=
    case1_at ⟨h1.sound, pfx_of y1_supp gA_supp gA_pfx1, nextP_of y1_supp n1, mr⟩ rr nr
      (fun _ h => by cases h; exact ay1)
  have s2 : GetNext Model.p2p tieL pFuel (.call y2 gA) [y3] y3 :=
    case1_at ⟨h2.sound, pfx_of y2_supp gA_supp gA_pfx2, nextP_of y2_supp n2, mc⟩ rc nc
      (fun _ h => by cases h)
  have s3 : GetNext Model.p2p tieL pFuel (.call y3 gA) [y4] y4 :=
    case1_at ⟨h3.sound, pfx_of y3_supp gA_supp gA_pfx3, nextP_of y3_supp n3, mb⟩ rb nb
      (fun _ h => by cases h)
  obtain ⟨d0, d1, d2, d3⟩ := gA_ne
  exact .step (ne_of_events d0) s0 (.step (ne_of_events d1) s1 (.step (ne_of_events d2) s2
    (.step (ne_of_events d3) s3 (.done rfl))))

/-! ### `ProductionSequence(gF)`: Case 2 with a revisit deleting `c` -/

theorem gF_facts : AP gF = true ∧ pFuel.Exec gF ∧ fa ∈ gF.events ∧ fr ∈ gF.events ∧
    fc ∈ gF.events ∧ gF.rf fa = none ∧ gF.nd fa = none ∧ gF.rf fr = some (.snd fb) ∧
    gF.rf fc = none ∧ gF.nd fc = none ∧ fb ∉ y1.G.events := by
  decide +kernel

theorem gF_pfx1 : AP gF = true ∧ pFuel.Exec gF ∧ gF.Closed y1.G.events ∧
    y1.G.key = (gF.restrict y1.G.events).key := by
  decide +kernel

theorem gF_pfx4 : AP gF = true ∧ pFuel.Exec gF ∧ gF.Closed c4.G.events ∧
    c4.G.key = (gF.restrict c4.G.events).key := by
  decide +kernel

theorem X1_pfx : AP X1 = true ∧ pFuel.Exec X1 ∧ X1.Closed y1.G.events ∧
    y1.G.key = (X1.restrict y1.G.events).key := by
  decide +kernel

theorem X2_pfx : AP X2 = true ∧ pFuel.Exec X2 ∧ X2.Closed y2.G.events ∧
    y2.G.key = (X2.restrict y2.G.events).key := by
  decide +kernel

theorem avail_pfx : AP gP = true ∧ pFuel.Exec gP ∧ gP.Closed (availPrefix y3.G fb).events ∧
    (availPrefix y3.G fb).key = (gP.restrict (availPrefix y3.G fb).events).key := by
  decide +kernel

theorem loop_facts : fa ∈ gP.events ∧ tieL gP fr = some (fa.tid, fa.idx) ∧
    pFuel.nextEv gP fr.tid = some fr ∧ pFuel.nextEv X1 fc.tid = some fc ∧
    fr ∉ gP.events ∧ fc ∉ gP.events ∧ fr ≠ fb ∧ fc ≠ fb ∧ fr.IsRecvB ∧ ¬ fc.IsRecv ∧
    ¬ fc.IsND ∧ fr ∈ X1.events ∧ X1.rf fr = some (.snd fa) ∧ X1.nd fr = none ∧
    fc ∈ X2.events ∧ X2.rf fc = none ∧ X2.nd fc = none ∧ fa ∈ y1.G.events := by
  decide +kernel

theorem gF_ne : Config.init.G.events ≠ gF.events ∧ y1.G.events ≠ gF.events ∧
    c4.G.events ≠ gF.events ∧ c5.G.key = gF.key := by
  decide +kernel

/-- The revisit in `ProductionSequence(gF)`: `Deleted = {c}` (non-empty), and the replayed list
`r :: delList` is the deferred list `[r, c]`. -/
theorem revisit_facts : (y3.add fb none none).del fr fb = {fc} ∧
    fr :: (y3.add fb none none).delList fr fb = [fr, fc] := by
  decide +kernel

/-- `pFuel` is bounded: no thread performs more than two events. -/
theorem pFuel_bounded : pFuel.Bounded 2 := by
  intro t u hu
  obtain ⟨x, y, rest, rfl⟩ : ∃ x y rest, u = x :: y :: rest := by
    match u, hu with
    | [], h => exact absurd h (by simp)
    | [_], h => exact absurd h (by simp)
    | x :: y :: rest, _ => exact ⟨x, y, rest, rfl⟩
  rcases t with _ | _ | _ | t
  · simp [pFuel, ofCodes, codeStep, Code.run, sa]
  · cases x <;> simp [pFuel, ofCodes, codeStep, Code.run, sa, rb, branch]
  · simp [pFuel, ofCodes, codeStep, Code.run, sa]
  · simp [pFuel, ofCodes, codeStep, Code.run]

/-- `gF ∈ ⟦pFuel⟧`. -/
theorem gF_sem : Model.p2p.Sem pFuel gF := by
  have hc := (consAPB_iff_p2p _ gF_supp).mp gF_facts.1
  refine ⟨Model.p2p.wf _ hc, gF_facts.2.1, hc, ?_⟩
  unfold Model.FullM
  rw [← Model.p2p.availM_eq AP consAPB_iff_p2p pFuel gF_supp]
  decide +kernel

/-- The situation of Case 2 of `GetNext({a}, gF)`: `r₀ = r`, `s₀ = b`. -/
theorem ctx_y1 : Ctx Model.p2p pFuel y1 gF fr fb :=
  ⟨⟨reach_y.1.sound, pfx_of y1_supp gF_supp gF_pfx1, nextP_of y1_supp nexts.2.1,
    gF_facts.2.2.2.1⟩, gF_facts.2.2.2.2.2.2.2.1, gF_facts.2.2.2.2.2.2.2.2.2.2⟩

/-- `GetNext({a}, gF)` (Case 2): the loop defers `r` and `c` (two Case-1 calls with targets
`MaxCompletion(G_p, [r])` and `MaxCompletion(G_p, [r, c])`), breaks at `b`; the revisit of `r` by
`b` gives `c4` (graph `{a, b, r ↦ b}`). -/
theorem getNext_y1 : GetNext Model.p2p tieL pFuel (.call y1 gF) [y2, y3, c4] c4 := by
  obtain ⟨h1, h2, -⟩ := reach_y
  obtain ⟨-, n1, n2, n3, -⟩ := nexts
  obtain ⟨pa, htie, ne1, ne2, nrp, ncp, nrb, ncb, hB, hcR, hcN, mr1, rr1, nr1, mc2, rc2, nc2,
    ay1⟩ := loop_facts
  have hx := ctx_y1
  have hcP : Model.p2p.cons gP := hx.gp_right.cons
  have cs1 : CanonStep tieL pFuel gP fr X1 :=
    ⟨ne1, _, _, Canon.intro (fun _ => ⟨fa, pa, htie, rfl, rfl⟩)
      (fun h => absurd hB (Lab.not_isRecvB_of_isRecvNB h))
      (fun h => absurd (Lab.IsRecvB.isRecv hB) (Lab.IsND.not_isRecv h))
      (fun h => absurd (Lab.IsRecvB.isRecv hB) h), rfl⟩
  have cs2 : CanonStep tieL pFuel X1 fc X2 :=
    ⟨ne2, _, _, Canon.intro (fun h => absurd (Lab.IsRecvB.isRecv h) hcR)
      (fun h => absurd (Lab.IsRecvNB.isRecv h) hcR) (fun h => absurd h hcN)
      (fun _ _ => ⟨rfl, rfl⟩), rfl⟩
  have hmc1 : maxCompletion tieL pFuel gP ([] ++ [fr]) = some X1 :=
    (maxCompletion_eq_some_iff hT hcP).mpr (.cons cs1 (.nil X1))
  have hmc2 : maxCompletion tieL pFuel gP ([] ++ [fr] ++ [fc]) = some X2 :=
    (maxCompletion_eq_some_iff hT hcP).mpr (.cons cs1 (.cons cs2 (.nil X2)))
  have g1 : GetNext Model.p2p tieL pFuel (.call y1 X1) [y2] y2 :=
    case1_at ⟨h1.sound, pfx_of y1_supp X1_supp X1_pfx, nextP_of y1_supp n1, mr1⟩ rr1 nr1
      (fun _ h => by cases h; exact ay1)
  have g2 : GetNext Model.p2p tieL pFuel (.call y2 X2) [y3] y3 :=
    case1_at ⟨h2.sound, pfx_of y2_supp X2_supp X2_pfx, nextP_of y2_supp n2, mc2⟩ rc2 nc2
      (fun _ h => by cases h)
  have l3 : GetNext Model.p2p tieL pFuel (.loop gP fb y3 ([] ++ [fr] ++ [fc])) [] y3 :=
    .brk (nextP_of y3_supp n3) ⟨pfx_of (y3_supp.restrict _) gP_supp avail_pfx, Or.inr rfl⟩
  have l2 : GetNext Model.p2p tieL pFuel (.loop gP fb y2 ([] ++ [fr])) ([y3] ++ []) y3 :=
    .defer (nextP_of y2_supp n2) (fun h => h.2.elim ncp ncb) hmc2 g2 l3
  have l1 : GetNext Model.p2p tieL pFuel (.loop gP fb y1 []) ([y2] ++ ([y3] ++ [])) y3 :=
    .defer (nextP_of y1_supp n1) (fun h => h.2.elim nrp nrb) hmc1 g1 l2
  exact .case2 (nextP_of y1_supp n1) hx.not_test gF_facts.2.2.2.2.2.2.2.1 l1

/-- `ProductionSequence(gF)` from `⟨∅, []⟩`: `a`; `a, r ↦ a`; `a, r ↦ a, c`; the revisit of `r`
by `b` deleting `c`: `a, r ↦ b, b`; `a, r ↦ b, b, c`. -/
theorem prodSeq_gF : ProdSeq Model.p2p tieL pFuel gF Config.init [y1, y2, y3, c4, c5] c5 := by
  obtain ⟨hc, hE, ma, -, mc, ra, na, -, rc, nc, -⟩ := gF_facts
  have hcF : Model.p2p.cons gF := (consAPB_iff_p2p _ gF_supp).mp hc
  have s0 : GetNext Model.p2p tieL pFuel (.call Config.init gF) [y1] y1 :=
    case1_at ⟨Config.inv_init, Pfx.of_isPrefixOf hcF hE (Graph.empty_isPrefixOf _),
      nextP_of supp_empty nexts.1, ma⟩ ra na (fun _ h => by cases h)
  have s2 : GetNext Model.p2p tieL pFuel (.call c4 gF) [c5] c5 :=
    case1_at ⟨pFuel_revisit.2.sound, pfx_of c4_supp gF_supp gF_pfx4,
      nextP_of c4_supp nexts.2.2.2.2, mc⟩ rc nc (fun _ h => by cases h)
  obtain ⟨d0, d1, d4, k5⟩ := gF_ne
  exact .step (ne_of_events d0) s0 (.step (ne_of_events d1) getNext_y1
    (.step (ne_of_events d4) s2 (.done ((eq_iff_key c5_supp gF_supp).mpr k5))))

/-- The same production sequence through the general results: it is the unique one
(`ProdSeq.det` against `productionSequence_reaches`); its steps are `StepM` steps from
`⟨∅, []⟩` to `c5`, whose graph is `gF`; the second call satisfies the specification of `GetNext`
(`getNext_spec`): `{a} ⊏ c4.G ⊑ gF`, `r ∈ c4.G`, and its configurations keep the order prefix
`a, r` and the graph prefix `{a}`. -/
theorem prodSeq_gF_spec : StepSeq Model.p2p tieL pFuel Config.init [y1, y2, y3, c4, c5] c5 ∧
    c5.G = gF ∧ ReachM Model.p2p tieL pFuel c5 ∧
    CallSpec Model.p2p tieL pFuel y1 gF fr [y2, y3, c4] c4 := by
  obtain ⟨S, c', h1, h2, h3, h4⟩ := productionSequence_reaches hT pFuel_bounded gF_sem
  obtain ⟨rfl, rfl⟩ := prodSeq_gF.det h1
  exact ⟨h2, h3, h4, getNext_spec hT pFuel_bounded ctx_y1.dom getNext_y1⟩

/-! ### Example 4.1 (`ex41`, threads `T3, T1, T2`): both terminal graphs -/

/-- `S(T3,1); R <- S(T3,1); S(T3,2)` as reached by Case 1. -/
def x3' : Config VPred := x2.add abcS2 none none
/-- The revisit of `R` by `S(T3,2)` from `x2` (`Deleted = ∅`). -/
def x4' : Config VPred := (x2.add abcS2 none none).revisitCfg abcR abcS2

/-- `PrefixExtension({S(T3,1)}, graph 2, S(T3,2))`. -/
abbrev gQ : Graph VPred := prefixExt x1.G abcG2 abcS2
/-- `MaxCompletion(G_p, [R])`. -/
def Z1 : Graph VPred := gQ.add abcR (some (.snd abcS1)) none

theorem abcG1_supp : abcG1.Supp := ((supp_empty.add _ _ _).add _ _ _).add _ _ _
theorem abcG2_supp : abcG2.Supp := ((supp_empty.add _ _ _).add _ _ _).add _ _ _
theorem x3'_supp : x3'.G.Supp := x2_supp.add _ _ _
theorem x4'_supp : x4'.G.Supp := ((x2_supp.add _ _ _).setRF (by decide +kernel) _).restrict _
theorem gQ_supp : gQ.Supp := abcG2_supp.restrict _
theorem Z1_supp : Z1.Supp := gQ_supp.add _ _ _

theorem ex41_facts : ex41.nextP AP Graph.empty = some abcS1 ∧ ex41.nextP AP x1.G = some abcR ∧
    ex41.nextP AP x2.G = some abcS2 ∧ ex41.Exec abcG1 ∧ ex41.Exec abcG2 ∧
    abcG1.rf abcS1 = none ∧ abcG1.nd abcS1 = none ∧ abcG1.rf abcR = some (.snd abcS1) ∧
    abcG1.nd abcR = none ∧ abcG1.rf abcS2 = none ∧ abcG1.nd abcS2 = none ∧
    abcG2.rf abcS1 = none ∧ abcG2.nd abcS1 = none ∧ abcG2.rf abcR = some (.snd abcS2) ∧
    abcS1 ∈ abcG1.events ∧ abcR ∈ abcG1.events ∧ abcS2 ∈ abcG1.events ∧
    abcS1 ∈ abcG2.events ∧ abcR ∈ abcG2.events ∧ abcS1 ∈ x1.G.events ∧
    abcS2 ∉ x1.G.events := by
  decide +kernel

theorem ex41_pfx1 : AP abcG1 = true ∧ ex41.Exec abcG1 ∧ abcG1.Closed x1.G.events ∧
    x1.G.key = (abcG1.restrict x1.G.events).key := by
  decide +kernel

theorem ex41_pfx2 : AP abcG1 = true ∧ ex41.Exec abcG1 ∧ abcG1.Closed x2.G.events ∧
    x2.G.key = (abcG1.restrict x2.G.events).key := by
  decide +kernel

theorem ex41_pfx3 : AP abcG2 = true ∧ ex41.Exec abcG2 ∧ abcG2.Closed x1.G.events ∧
    x1.G.key = (abcG2.restrict x1.G.events).key := by
  decide +kernel

theorem ex41_pfxZ : AP Z1 = true ∧ ex41.Exec Z1 ∧ Z1.Closed x1.G.events ∧
    x1.G.key = (Z1.restrict x1.G.events).key := by
  decide +kernel

theorem ex41_pfxA : AP gQ = true ∧ ex41.Exec gQ ∧ gQ.Closed (availPrefix x2.G abcS2).events ∧
    (availPrefix x2.G abcS2).key = (gQ.restrict (availPrefix x2.G abcS2).events).key := by
  decide +kernel

theorem ex41_loop : abcS1 ∈ gQ.events ∧ tieL gQ abcR = some (abcS1.tid, abcS1.idx) ∧
    ex41.nextEv gQ abcR.tid = some abcR ∧ abcR ∉ gQ.events ∧ abcR ≠ abcS2 ∧ abcR.IsRecvB ∧
    abcR ∈ Z1.events ∧ Z1.rf abcR = some (.snd abcS1) ∧ Z1.nd abcR = none ∧
    (x2.add abcS2 none none).del abcR abcS2 = ∅ := by
  decide +kernel

theorem ex41_ne : Config.init.G.events ≠ abcG1.events ∧ x1.G.events ≠ abcG1.events ∧
    x2.G.events ≠ abcG1.events ∧ x3'.G.key = abcG1.key ∧ Config.init.G.events ≠ abcG2.events ∧
    x1.G.events ≠ abcG2.events ∧ x4'.G.key = abcG2.key := by
  decide +kernel

/-- Example 4.1, graph 1: `ProductionSequence` is three Case-1 calls. -/
theorem prodSeq_ex41_g1 :
    ProdSeq Model.p2p tieL ex41 abcG1 Config.init [x1, x2, x3'] x3' := by
  obtain ⟨n0, n1, n2, hE1, -, r1, d1, r2, d2, r3, d3, -, -, -, m1, m2, m3, -, -, a1, -⟩ :=
    ex41_facts
  have hc1 : Model.p2p.cons abcG1 := (consAPB_iff_p2p _ abcG1_supp).mp ex41_pfx1.1
  have hx1 := ex41_reach_x2
  have s0 : GetNext Model.p2p tieL ex41 (.call Config.init abcG1) [x1] x1 :=
    case1_at ⟨Config.inv_init, Pfx.of_isPrefixOf hc1 hE1 (Graph.empty_isPrefixOf _),
      nextP_of supp_empty n0, m1⟩ r1 d1 (fun _ h => by cases h)
  have hr1 : ReachM Model.p2p tieL ex41 x1 :=
    ReflTransGen.single (stepM_of_hasSucc Config.inv_init x1_supp ex41_succs.1)
  have s1 : GetNext Model.p2p tieL ex41 (.call x1 abcG1) [x2] x2 :=
    case1_at ⟨hr1.sound, pfx_of x1_supp abcG1_supp ex41_pfx1, nextP_of x1_supp n1, m2⟩ r2 d2
      (fun _ h => by cases h; exact a1)
  have s2 : GetNext Model.p2p tieL ex41 (.call x2 abcG1) [x3'] x3' :=
    case1_at ⟨hx1.sound, pfx_of x2_supp abcG1_supp ex41_pfx2, nextP_of x2_supp n2, m3⟩ r3 d3
      (fun _ h => by cases h)
  obtain ⟨e0, e1, e2, k3, -⟩ := ex41_ne
  exact .step (ne_of_events e0) s0 (.step (ne_of_events e1) s1 (.step (ne_of_events e2) s2
    (.done ((eq_iff_key x3'_supp abcG1_supp).mpr k3))))

/-- Example 4.1, graph 2: Case 1 adds `S(T3,1)`; `GetNext({S(T3,1)}, graph 2)` is Case 2
(`r₀ = R`, `s₀ = S(T3,2)`, `G_p = {S(T3,1)}`): the loop defers `R` (Case 1 with target
`MaxCompletion(G_p, [R])`: `R <- S(T3,1)`), breaks at `S(T3,2)`; the revisit of `R` by
`S(T3,2)` deletes nothing (`Deleted = ∅`) and gives graph 2. -/
theorem prodSeq_ex41_g2 :
    ProdSeq Model.p2p tieL ex41 abcG2 Config.init [x1, x2, x4'] x4' := by
  obtain ⟨n0, n1, n2, -, hE2, -, -, -, -, -, -, r1, d1, rR, -, -, -, m1, mR, -, ns⟩ :=
    ex41_facts
  obtain ⟨pa, htie, ne1, nrp, nrs, hB, mZ, rZ, dZ, -⟩ := ex41_loop
  have hc2 : Model.p2p.cons abcG2 := (consAPB_iff_p2p _ abcG2_supp).mp ex41_pfx3.1
  have hr1 : ReachM Model.p2p tieL ex41 x1 :=
    ReflTransGen.single (stepM_of_hasSucc Config.inv_init x1_supp ex41_succs.1)
  have s0 : GetNext Model.p2p tieL ex41 (.call Config.init abcG2) [x1] x1 :=
    case1_at ⟨Config.inv_init, Pfx.of_isPrefixOf hc2 hE2 (Graph.empty_isPrefixOf _),
      nextP_of supp_empty n0, m1⟩ r1 d1 (fun _ h => by cases h)
  have hx : Ctx Model.p2p ex41 x1 abcG2 abcR abcS2 :=
    ⟨⟨hr1.sound, pfx_of x1_supp abcG2_supp ex41_pfx3, nextP_of x1_supp n1, mR⟩, rR, ns⟩
  have cs : CanonStep tieL ex41 gQ abcR Z1 :=
    ⟨ne1, _, _, Canon.intro (fun _ => ⟨abcS1, pa, htie, rfl, rfl⟩)
      (fun h => absurd hB (Lab.not_isRecvB_of_isRecvNB h))
      (fun h => absurd (Lab.IsRecvB.isRecv hB) (Lab.IsND.not_isRecv h))
      (fun h => absurd (Lab.IsRecvB.isRecv hB) h), rfl⟩
  have hmc : maxCompletion tieL ex41 gQ ([] ++ [abcR]) = some Z1 :=
    (maxCompletion_eq_some_iff hT hx.gp_right.cons).mpr (.cons cs (.nil Z1))
  have g1 : GetNext Model.p2p tieL ex41 (.call x1 Z1) [x2] x2 :=
    case1_at ⟨hr1.sound, pfx_of x1_supp Z1_supp ex41_pfxZ, nextP_of x1_supp n1, mZ⟩ rZ dZ
      (fun _ h => by cases h; exact ex41_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  have l2 : GetNext Model.p2p tieL ex41 (.loop gQ abcS2 x2 ([] ++ [abcR])) [] x2 :=
    .brk (nextP_of x2_supp n2) ⟨pfx_of (x2_supp.restrict _) gQ_supp ex41_pfxA, Or.inr rfl⟩
  have l1 : GetNext Model.p2p tieL ex41 (.loop gQ abcS2 x1 []) ([x2] ++ []) x2 :=
    .defer (nextP_of x1_supp n1) (fun h => h.2.elim nrp nrs) hmc g1 l2
  have s1 : GetNext Model.p2p tieL ex41 (.call x1 abcG2) [x2, x4'] x4' :=
    .case2 (nextP_of x1_supp n1) hx.not_test rR l1
  obtain ⟨-, -, -, -, e0, e1, k4⟩ := ex41_ne
  exact .step (ne_of_events e0) s0 (.step (ne_of_events e1) s1
    (.done ((eq_iff_key x4'_supp abcG2_supp).mpr k4)))

/-! ### The printed domain of `GetNext` -/

/-- The fate-table witness for "Algorithm 2: claim ⟨1⟩1 on the printed domain" (`pTwo`, model
`asyn`, every tie-break). `∅ ⊏ {s1}` (both consistent executions), but `next_P(∅) = s0 ∉ {s1}`.
`GetNext(∅, {s1})` has no result (line 9 fails; line 12's `G_t.rf(r₀)` is undefined), and no
sequence of algorithmic steps from `⟨∅, []⟩` reaches a `G'` with `∅ ⊏ G' ⊑ {s1}` (P1 and P2
together): the first step adds `s0`, and the only such `G'` is `{s1}`. -/
theorem getNext_printed_domain_false (tie : Tie VPred) :
    SPfx Model.asyn pTwo Graph.empty gS1 ∧ Model.asyn.nextP pTwo Graph.empty = some s0 ∧
      s0 ∉ gS1.events ∧ (¬ ∃ S c', GetNext Model.asyn tie pTwo (.call Config.init gS1) S c') ∧
      ¬ ∃ S c', StepSeq Model.asyn tie pTwo Config.init S c' ∧
        SPfx Model.asyn pTwo Graph.empty c'.G ∧ Pfx Model.asyn pTwo c'.G gS1 := by
  obtain ⟨-, hc, hE, -⟩ := prefix_not_nrLe
  have hs0 : s0 ∉ gS1.events := by decide +kernel
  have hev : gS1.events = {s1} := by decide +kernel
  have hsp : SPfx Model.asyn pTwo Graph.empty gS1 :=
    ⟨Pfx.of_isPrefixOf hc hE (Graph.empty_isPrefixOf _), ne_of_events (by decide +kernel)⟩
  refine ⟨hsp, nextP_pTwo.1, hs0, ?_, ?_⟩
  · rintro ⟨S, c', h⟩
    cases h with
    | case1 hn _ hpf =>
      rw [show (Config.init : Config VPred).G = Graph.empty from rfl, nextP_pTwo.1] at hn
      cases hn
      exact hs0 (hpf.events_subset (Finset.mem_insert_self _ _))
    | case2 hn _ hs _ =>
      rw [show (Config.init : Config VPred).G = Graph.empty from rfl, nextP_pTwo.1] at hn
      cases hn
      have : gS1.rf s0 = none := by decide +kernel
      rw [this] at hs
      cases hs
  · rintro ⟨S, c', hS, hsp', hpf⟩
    have hsub : c'.G.events ⊆ {s1} := hev ▸ hpf.events_subset
    obtain ⟨-, x, hx, -⟩ := sPfx_iff_exists.mp hsp'
    have hxs : x = s1 := Finset.mem_singleton.mp (hsub hx)
    subst hxs
    have hr := hS.reachM ReflTransGen.refl
    rcases ReflTransGen.cases_tail hr with h | ⟨c₀, hr₀, hst⟩
    · rw [h] at hx
      simp [Config.init, Graph.empty] at hx
    · have hi₀ := ReachM.sound (M := Model.asyn) (tie := tie) (P := pTwo) hr₀
      cases hst with
      | @nr e src out ha =>
        have hn := ha.1
        have heG : e ∉ c₀.G.events :=
          hi₀.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv (nextEv_of_nextP hn))
        have hes : e = s1 := Finset.mem_singleton.mp (hsub (Finset.mem_insert_self _ _))
        have h0 : c₀.G.events = ∅ := Finset.eq_empty_of_forall_notMem fun x hx' => by
          have := Finset.mem_singleton.mp (hsub (Finset.mem_insert_of_mem hx'))
          exact heG (hes ▸ this ▸ hx')
        have hG0 : c₀.G = Graph.empty :=
          (eq_iff_key hi₀.wf.supp supp_empty).mpr (by simp [Graph.key, h0, Graph.empty])
        rw [hG0, nextP_pTwo.1, hes] at hn
        cases hn
      | @revisit e r _ _ hg _ =>
        have hrd : r ∉ (c₀.add e none none).del r e :=
          fun h => lt_irrefl _ (Config.mem_del.mp h).2.2.1
        have hr' := (Config.mem_revisitCfg_events).mpr ⟨hg.mem, hrd⟩
        have := Finset.mem_singleton.mp (hsub hr')
        subst this
        exact absurd hg.recv (by simp [Ev.IsRecv, Lab.IsRecv])

end GetNextEx

end Must

#print axioms Must.GetNextEx.prodSeq_gA
#print axioms Must.GetNextEx.pFuel_bounded
#print axioms Must.GetNextEx.gF_sem
#print axioms Must.GetNextEx.getNext_y1
#print axioms Must.GetNextEx.prodSeq_gF
#print axioms Must.GetNextEx.revisit_facts
#print axioms Must.GetNextEx.prodSeq_gF_spec
#print axioms Must.GetNextEx.prodSeq_ex41_g1
#print axioms Must.GetNextEx.prodSeq_ex41_g2
#print axioms Must.GetNextEx.getNext_printed_domain_false
