import Mazurkiewicz.Must.Complete
import Mazurkiewicz.Must.ReplayRev
import Mazurkiewicz.Must.AlgEx

/-!
# Examples of M5: the two replays, `revCond_iff_replay`, the bound of A.3 (b)

Programs of `Examples.lean` and `AlgEx.lean`; the model is `Model.p2p` with M2's `consAPB`
(`AP`), the tie-break `Sel.least.pick AP` (`tieL`, which satisfies Q9: `hT`).

* `p19_opus_rel` (p. 19, Opus's witness, restated over the relations of M5): from the kept graph
  `{k}`, the canonical replay (`Replay`) of the supplied list `r, d, a` gives `H₁ \ {s}`; the
  scheduler-following completion (`SchedStep`) until `s` is unique and gives `H₂ \ {s}`, a
  different graph.
* `p19_astra_rel` (Astra's witness): from the kept graph `{a, k}`, `next_P` is `q`, not the first
  supplied event `r`; both lists `r, q` and `q, r` replay to `H \ {s}` (same unordered graph,
  different insertion orders).
* `pFuel_replay`: `revCond_iff_replay_step` on the reachable revisit with `Deleted = {c}`: the
  base `{a}` is closed and the replay of `r, c` from it reproduces the configuration before `b`.
* `replay_without_closure`: the closure conjunct of `revCond_iff_replay` is necessary. In the
  reachable configuration `q ↦ d; r ⊥; d` (`asyn` events explored under `Model.p2p`) of
  `T0: q = recv_nb()`, `T1: r = recv_nb(); d = send(T0, 0)`, `T2: s = send(T1, 1)`, with `s`
  added, `Deleted = {d}` for the revisit of `r` by `s`; the replay of `r, d` from `H|K`
  reproduces `H \ {s}`, but `RevisitCondition(H, d, s)`
  fails (the kept `q` reads `d`) and `K` is not `porf`-closed.
* `nd_label_breaks_A15`: the fate-table witness for A.15 read with ND values in labels (the
  refutation is informal; the theorem proves the stated facts).
* `fruitless_unbounded`: without a bound (`Program.Bounded`), Theorem A.3 (b) fails: a thread
  that sends forever leaves the initial configuration fruitless, for every model.
-/

namespace Must

namespace ReplayEx

open MustFast MustFast' Examples AlgEx Graph Relation

/-- Q9 for `tieL` and `p2p`. -/
theorem hT : TieQ9 Model.p2p tieL := tieQ9_pick (M := Model.p2p) consAPB_iff_p2p .least

theorem ordMem_of {c : Config VPred} (h : c.order.toFinset = c.G.events) : c.OrdMem :=
  fun x => by rw [← h, List.mem_toFinset]

/-! ### p. 19, Opus's witness -/

theorem oH1_supp : oH1.G.Supp :=
  ((((AlgEx.supp_empty.add _ _ _).add _ _ _).add _ _ _).add _ _ _).add _ _ _

theorem oH2_supp : oH2.G.Supp :=
  ((((AlgEx.supp_empty.add _ _ _).add _ _ _).add _ _ _).add _ _ _).add _ _ _

theorem kept1_supp : (kept oH1 oR oS).G.Supp := oH1_supp.restrict _

theorem kept1_facts : (kept oH1 oR oS).order.toFinset = (kept oH1 oR oS).G.events ∧
    AP (kept oH1 oR oS).G = true := by
  decide +kernel

/-- The stop test of the completion: the revisiting send `s`. -/
abbrev stopS : Ev VPred → Bool := fun e => decide (e = oS)

/-- `p19_opus_rel`: from the kept graph `{k}`, the canonical replay of the supplied list
`r, d, a` gives `H₁ \ {s}`; the scheduler-following completion until `s` exists, is unique, and
gives `H₂ \ {s}`; the two graphs differ. -/
theorem p19_opus_rel :
    Replay tieL pOp (kept oH1 oR oS).G [oR, oD, oA] (oH1.G.remove {oS}) ∧
    (∃ G₂, ReflTransGen (SchedStep Model.p2p tieL pOp stopS) (kept oH1 oR oS).G G₂ ∧
      Model.p2p.nextP pOp G₂ = some oS ∧ G₂ = oH2.G.remove {oS}) ∧
    (∀ G₃, ReflTransGen (SchedStep Model.p2p tieL pOp stopS) (kept oH1 oR oS).G G₃ →
      (∀ X, ¬ SchedStep Model.p2p tieL pOp stopS G₃ X) → G₃ = oH2.G.remove {oS}) ∧
    oH2.G.remove {oS} ≠ oH1.G.remove {oS} := by
  obtain ⟨hord, hcB⟩ := kept1_facts
  have hcons : Model.p2p.cons (kept oH1 oR oS).G := (consAPB_iff_p2p _ kept1_supp).mp hcB
  have hp := p19_opus
  obtain ⟨-, -, -, hkey2, -, hrep, -, -, -, -, hstop⟩ := hp
  -- the replay
  have hrep1 : Replay tieL pOp (kept oH1 oR oS).G [oR, oD, oA] (oH1.G.remove {oS}) := by
    cases hr : replay AP .least pOp (kept oH1 oR oS) [oR, oD, oA] with
    | none => simp [hr] at hrep
    | some c' =>
      simp only [hr, Option.map_some, Option.some.injEq] at hrep
      obtain ⟨h1, -⟩ := replay_some (T := .least) (consB := AP) _ (ordMem_of hord) hr
      have hS := h1.supp kept1_supp
      rwa [(eq_iff_key hS (oH1_supp.restrict _)).mpr hrep] at h1
  -- the completion
  have hspec := schedComplete_spec (M := Model.p2p) (P := pOp) consAPB_iff_p2p hT stopS 10
    (kept oH1 oR oS) (ordMem_of hord) hcons
  cases hsc : schedComplete AP .least pOp stopS 10 (kept oH1 oR oS) with
  | full c' => simp [hsc, Completion.isStopped] at hstop
  | outOfFuel c' => simp [hsc, Completion.isStopped] at hstop
  | failed c' e' => simp [hsc, Completion.isStopped] at hstop
  | stopped c' =>
    rw [hsc] at hspec hkey2
    obtain ⟨hrun, e, he, hse⟩ := hspec
    have hS2 : c'.G.Supp := (Model.p2p.wf _ (schedRun_cons hT hrun hcons)).supp
    have hG2 : c'.G = oH2.G.remove {oS} :=
      (eq_iff_key hS2 (oH2_supp.restrict _)).mpr hkey2
    have heS : e = oS := of_decide_eq_true hse
    subst heS
    have hterm : ∀ X, ¬ SchedStep Model.p2p tieL pOp stopS c'.G X := by
      rintro X ⟨e', he', hs', -⟩
      rw [he, Option.some.injEq] at he'
      subst he'
      simp at hs'
    refine ⟨hrep1, ⟨c'.G, hrun, he, hG2⟩, fun G₃ h₃ ht₃ => ?_, ?_⟩
    · rw [← hG2]
      exact schedRun_unique hT h₃ hcons hrun ht₃ hterm
    · intro h
      have : (oH2.G.remove {oS}).key = (oH1.G.remove {oS}).key := by rw [h]
      revert this
      decide +kernel

/-! ### p. 19, Astra's witness -/

theorem aH_supp : aH.G.Supp :=
  ((((AlgEx.supp_empty.add _ _ _).add _ _ _).add _ _ _).add _ _ _).add _ _ _

theorem keptA_supp : (kept aH aR aS).G.Supp := aH_supp.restrict _

theorem keptA_ord : (kept aH aR aS).order.toFinset = (kept aH aR aS).G.events := by
  decide +kernel

theorem keptA_next : pAs.nextP AP (kept aH aR aS).G = some aQ := by
  decide +kernel

theorem keptA_rq : ((replay AP .least pAs (kept aH aR aS) [aR, aQ]).map (fun c => c.G.key)) =
    some (aH.G.remove {aS}).key := by
  decide +kernel

theorem keptA_qr : ((replay AP .least pAs (kept aH aR aS) [aQ, aR]).map (fun c => c.G.key)) =
    some (aH.G.remove {aS}).key := by
  decide +kernel

/-- `p19_astra_rel`: from the kept graph `{a, k}`, `next_P` is `q`, while the supplied list
starts with `r`; the canonical replays of `r, q` and of `q, r` both give `H \ {s}`: the same
unordered graph, built in different insertion orders. -/
theorem p19_astra_rel :
    Model.p2p.nextP pAs (kept aH aR aS).G = some aQ ∧ aQ ≠ aR ∧
    Replay tieL pAs (kept aH aR aS).G [aR, aQ] (aH.G.remove {aS}) ∧
    Replay tieL pAs (kept aH aR aS).G [aQ, aR] (aH.G.remove {aS}) := by
  have hord := keptA_ord
  have hn := keptA_next
  have h1 := keptA_rq
  have h2 := keptA_qr
  have hrel : ∀ l, ((replay AP .least pAs (kept aH aR aS) l).map (fun c => c.G.key)) =
      some (aH.G.remove {aS}).key → Replay tieL pAs (kept aH aR aS).G l (aH.G.remove {aS}) := by
    intro l hl
    cases hr : replay AP .least pAs (kept aH aR aS) l with
    | none => simp [hr] at hl
    | some c' =>
      simp only [hr, Option.map_some, Option.some.injEq] at hl
      obtain ⟨h, -⟩ := replay_some (T := .least) (consB := AP) _ (ordMem_of hord) hr
      rwa [(eq_iff_key (h.supp keptA_supp) (aH_supp.restrict _)).mpr hl] at h
  refine ⟨?_, by decide, hrel _ h1, hrel _ h2⟩
  rw [← Model.nextP_eq _ consAPB_iff_p2p pAs keptA_supp]
  exact hn

/-! ### `revCond_iff_replay` with a non-empty `Deleted` (`pFuel`) -/

theorem pFuel_reach_y3 : ReachM Model.p2p tieL pFuel y3 := by
  have h0 : ReachM Model.p2p tieL pFuel .init := ReflTransGen.refl
  have h1 : ReachM Model.p2p tieL pFuel y1 :=
    h0.tail (stepM_of_hasSucc h0.sound y1_supp pFuel_checks.1)
  have h2 : ReachM Model.p2p tieL pFuel y2 :=
    h1.tail (stepM_of_hasSucc h1.sound y2_supp pFuel_checks.2.1)
  exact h2.tail (stepM_of_hasSucc h2.sound y3_supp pFuel_checks.2.2.1)

theorem pFuel_delList : (y3.add fb none none).delList fr fb = [fc] := by decide +kernel

/-- `pFuel_replay`: at the reachable `y3 = a; r ↦ a; c` with `next_P = b`, the revisit of `r` by
`b` (`Deleted = {c}`) passes its guards, so by `revCond_iff_replay_step` the base `K = {a}` is
`porf`-closed and the canonical replay of `r, c` from `H|K` reproduces the graph of `y3`. -/
theorem pFuel_replay :
    (y3.add fb none none).del fr fb = {fc} ∧ (y3.add fb none none).delList fr fb = [fc] ∧
    (y3.add fb none none).G.Closed ((y3.add fb none none).base fr fb) ∧
    Replay tieL pFuel ((y3.add fb none none).G.restrict ((y3.add fb none none).base fr fb))
      [fr, fc] y3.G := by
  obtain ⟨-, -, -, hn, hg, -, hd⟩ := pFuel_checks
  have hG := revGuard_of_guardB hg
  have hn' : Model.p2p.nextP pFuel y3.G = some fb := by
    rw [← Model.nextP_eq _ consAPB_iff_p2p pFuel y3_supp]
    exact hn
  have h := (revCond_iff_replay_step hT pFuel_reach_y3.sound hn'
    (by simp [Ev.IsSend, Lab.IsSend]) hG.mem hG.recv hG.nporf).mp ⟨hG.cond, hG.cond_s⟩
  rw [pFuel_delList] at h
  exact ⟨hd, pFuel_delList, h⟩

/-! ### The closure conjunct is necessary -/

/-- `T0: q = recv_nb()`, `T1: r = recv_nb(); d = send(T0, 0)`, `T2: s = send(T1, 1)`. -/
def pNC : Program VPred := ofCodes [rnb, rnb (sa 0 0), sa 1 1]

/-- `q`. -/
abbrev nq : Ev VPred := ⟨0, 0, .recv ⟨.asyn, false⟩ .any⟩
/-- `r`. -/
abbrev nr : Ev VPred := ⟨1, 0, .recv ⟨.asyn, false⟩ .any⟩
/-- `d`. -/
abbrev nd' : Ev VPred := ⟨1, 1, .send .asyn 0 0⟩
/-- `s`. -/
abbrev ns : Ev VPred := ⟨2, 0, .send .asyn 1 1⟩

/-- `q ⊥`. -/
def w1 : Config VPred := Config.init.add nq (some .bot) none
/-- `q ⊥; r ⊥`. -/
def w2 : Config VPred := w1.add nr (some .bot) none
/-- `q ↦ d; r ⊥; d`: the revisit of `q` by `d` (empty `Deleted`). -/
def w3 : Config VPred := (w2.add nd' none none).revisitCfg nq nd'
/-- `H = q ↦ d; r ⊥; d; s`. -/
def wH : Config VPred := w3.add ns none none

theorem w1_supp : w1.G.Supp := AlgEx.supp_empty.add _ _ _
theorem w2_supp : w2.G.Supp := w1_supp.add _ _ _
theorem w3_supp : w3.G.Supp := ((w2_supp.add _ _ _).setRF (by decide +kernel) _).restrict _
theorem wH_supp : wH.G.Supp := w3_supp.add _ _ _

theorem pNC_checks : hasSucc (rep .least) pNC .init w1.order w1.G = true ∧
    hasSucc (rep .least) pNC w1 w2.order w2.G = true ∧
    pNC.nextP AP w2.G = some nd' ∧ guardB .least (w2.add nd' none none) nq nd' = true ∧
    AP ((w2.add nd' none none).revisitCfg nq nd').G = true ∧
    pNC.nextP AP w3.G = some ns ∧
    wH.del nr ns = {nd'} ∧ wH.delList nr ns = [nd'] ∧
    revCond (oracleQ9 AP .least) wH nd' ns = false ∧
    ¬ wH.G.Closed (wH.base nr ns) ∧
    pNC.nextEv (wH.G.restrict (wH.base nr ns)) nr.tid = some nr ∧
    pNC.nextEv ((wH.G.restrict (wH.base nr ns)).add nr (some .bot) none) nd'.tid = some nd' ∧
    (((wH.G.restrict (wH.base nr ns)).add nr (some .bot) none).add nd' none none).key =
      (wH.G.remove {ns}).key := by
  decide +kernel

theorem pNC_reach_w3 : ReachM Model.p2p tieL pNC w3 := by
  have h0 : ReachM Model.p2p tieL pNC .init := ReflTransGen.refl
  have h1 : ReachM Model.p2p tieL pNC w1 :=
    h0.tail (stepM_of_hasSucc h0.sound w1_supp pNC_checks.1)
  have h2 : ReachM Model.p2p tieL pNC w2 :=
    h1.tail (stepM_of_hasSucc h1.sound w2_supp pNC_checks.2.1)
  obtain ⟨-, -, hn, hg, hc, -⟩ := pNC_checks
  exact h2.tail (stepM_revisit_of_check w2_supp hn (by simp [Ev.IsSend, Lab.IsSend]) hg hc)

/-- `replay_without_closure` (the events are `asyn` events, explored under `Model.p2p`, which
imposes no condition beyond well-formedness on them): at the reachable `w3` with `next_P = s`,
for the revisit of `r` by `s` (`Deleted = {d}`), the canonical replay of `r, d` from `H|K`
reproduces `H \ {s}`, yet
`RevisitCondition(H, d, s)` fails and `K` is not `porf`-closed: the right-hand side of
`revCond_iff_replay` without its closure conjunct does not imply the left-hand side. -/
theorem replay_without_closure :
    ReachM Model.p2p tieL pNC w3 ∧ Model.p2p.nextP pNC w3.G = some ns ∧
    wH.del nr ns = {nd'} ∧ wH.delList nr ns = [nd'] ∧
    Replay tieL pNC (wH.G.restrict (wH.base nr ns)) (nr :: wH.delList nr ns) (wH.G.remove {ns}) ∧
    ¬ (∀ d ∈ insert nr (wH.del nr ns), RevCond tieL wH d ns) ∧
    ¬ wH.G.Closed (wH.base nr ns) := by
  obtain ⟨-, -, -, -, -, hn, hd, hdl, hrc, hcl, hn1, hn2, hkey⟩ := pNC_checks
  have hNB : nr.IsRecvNB := by simp [Ev.IsRecvNB, Lab.IsRecvNB]
  have hR : nr.IsRecv := by simp [Ev.IsRecv, Lab.IsRecv]
  have hS : ¬ nd'.IsRecv := by simp [Ev.IsRecv, Lab.IsRecv]
  have hN : ¬ nd'.IsND := by simp [Ev.IsND, Lab.IsND]
  have hfin : (((wH.G.restrict (wH.base nr ns)).add nr (some .bot) none).add nd' none none) =
      wH.G.remove {ns} :=
    (eq_iff_key (((wH_supp.restrict _).add _ _ _).add _ _ _) (wH_supp.restrict _)).mpr hkey
  refine ⟨pNC_reach_w3, ?_, hd, hdl, ?_, fun h => ?_, hcl⟩
  · rw [← Model.nextP_eq _ consAPB_iff_p2p pNC w3_supp]
    exact hn
  · rw [hdl]
    refine .cons ⟨hn1, _, _, Canon.intro (fun h => absurd h (Lab.not_isRecvB_of_isRecvNB hNB))
      (fun _ => ⟨rfl, rfl⟩) (fun h => absurd hR (Lab.IsND.not_isRecv h)) (fun h => absurd hR h),
      rfl⟩ (.cons ⟨hn2, _, _, Canon.intro (fun h => absurd (Lab.IsRecvB.isRecv h) hS)
      (fun h => absurd (Lab.IsRecvNB.isRecv h) hS) (fun h => absurd h hN)
      (fun _ _ => ⟨rfl, rfl⟩), rfl⟩ ?_)
    rw [hfin]
    exact .nil _
  · have := (revCond_iff .least wH nd' ns).mpr (h nd' (by rw [hd]; simp))
    rw [hrc] at this
    cases this

/-! ### Theorem A.3 (b) needs a bound -/

/-- A program whose thread `0` sends to thread `1` forever. -/
def pInf : Program VPred where
  threads := [0]
  nodup := List.nodup_singleton 0
  step := fun t _ => if t = 0 then some (.send .asyn 1 0) else none
  step_none := fun t ht => by
    have : t ≠ 0 := by simpa using ht
    simp [this]
  stop := fun t u l h hs => by
    by_cases ht : t = 0
    · simp only [ht, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact hs.elim
    · simp [ht] at h
  nd_ne := fun t u S h => by
    by_cases ht : t = 0
    · simp [ht] at h
    · simp [ht] at h

/-- `fruitless_unbounded`: `pInf` is bounded by no `n`, and for every model and tie-break every
graph has a next event, so the initial configuration (reachable) is fruitless. -/
theorem fruitless_unbounded (M : Model VPred) (tie : Tie VPred) :
    (∀ n, ¬ pInf.Bounded n) ∧ ReachM M tie pInf Config.init ∧ Fruitless M tie pInf Config.init := by
  refine ⟨fun n hb => ?_, ReflTransGen.refl, fun ⟨c', _, hn⟩ => ?_⟩
  · have := hb 0 (List.replicate n none) (by simp)
    simp [pInf] at this
  · have hmem : (⟨0, c'.G.cnt 0, .send .asyn 1 0⟩ : Ev VPred) ∈ M.availM pInf c'.G := by
      refine M.mem_availM_iff'.mpr ⟨0, by simp [pInf], ?_, Or.inl ?_⟩
      · simp [Program.nextEv, pInf]
      · simp [Ev.IsRecvB, Lab.IsRecvB]
    rw [Model.nextP_eq_none_iff] at hn
    unfold Model.FullM at hn
    rw [hn] at hmem
    simp at hmem

/-! ### A.15 with ND values in labels -/

/-- A program whose thread `0` performs one `ND_{0,1}` and terminates. -/
def pND : Program VPred where
  threads := [0]
  nodup := List.nodup_singleton 0
  step := fun t u => if t = 0 ∧ u = [] then some (.nd {0, 1}) else none
  step_none := fun t ht => by
    have : t ≠ 0 := by simpa using ht
    simp [this]
  stop := fun t u l h hs => by
    by_cases ht : t = 0 ∧ u = []
    · simp only [ht, and_self, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact hs.elim
    · simp [ht] at h
  nd_ne := fun t u S h => by
    by_cases ht : t = 0 ∧ u = []
    · simp only [ht, and_self, ↓reduceIte, Option.some.injEq, Lab.nd.injEq] at h
      subst h
      exact ⟨0, by simp⟩
    · simp [ht] at h

/-- The ND event of `pND`. -/
abbrev eND : Ev VPred := ⟨0, 0, .nd {0, 1}⟩

/-- `nd_label_breaks_A15` (fate row A.15, "F with ND values in labels"): read with the ND
outcome as part of the event (printed labels), the event `e@0` is available in `∅`, the
consistent execution `G' = {e@1}` extends `∅` and does not contain `e@0`, and `e` is not
available in `G'`. The refutation of printed A.15 is informal: it rests on the reading that the
outcome-labelled events `e@0` and `e@1` are distinct; the theorem proves only the stated facts.
With Q6 (the outcome is a graph component, not part of the label) `e` itself is in `G'`, and
A.15's premise fails. Every model. -/
theorem nd_label_breaks_A15 (M : Model VPred) :
    eND ∈ M.availM pND Graph.empty ∧ M.cons (Graph.empty.addND eND 1) ∧
    Graph.empty.IsPrefixOf (Graph.empty.addND eND 1) ∧
    (Graph.empty.addND eND 1).nd eND = some 1 ∧ eND ∈ (Graph.empty.addND eND 1).events ∧
    eND ∉ M.availM pND (Graph.empty.addND eND 1) := by
  have hcnt : (Graph.empty.addND eND 1).cnt 0 = 1 := by decide +kernel
  refine ⟨?_, M.ext_nd _ _ 1 M.empty rfl (by simp [Ev.IsND, Lab.IsND]) (by decide),
    Graph.empty_isPrefixOf _, by simp, by simp, fun h => ?_⟩
  · refine M.mem_availM_iff'.mpr ⟨0, by simp [pND], ?_, Or.inl (by simp [Ev.IsRecvB,
      Lab.IsRecvB])⟩
    simp [Program.nextEv, pND, Graph.trace, Graph.traceBefore, Graph.cnt, Graph.empty]
  · obtain ⟨t, ht, hn, -⟩ := M.mem_availM_iff'.mp h
    have ht0 : t = 0 := by simpa [pND] using ht
    subst ht0
    simp [Program.nextEv, pND, Graph.trace, Graph.traceBefore, hcnt] at hn

end ReplayEx

end Must

#print axioms Must.ReplayEx.hT
#print axioms Must.ReplayEx.p19_opus_rel
#print axioms Must.ReplayEx.p19_astra_rel
#print axioms Must.ReplayEx.pFuel_replay
#print axioms Must.ReplayEx.replay_without_closure
#print axioms Must.ReplayEx.fruitless_unbounded
#print axioms Must.ReplayEx.nd_label_breaks_A15
