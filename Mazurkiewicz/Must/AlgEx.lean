import Mazurkiewicz.Must.AlgCompute
import Mazurkiewicz.Must.EnumSpec
import Mazurkiewicz.Must.Examples

/-!
# Examples of M4: Example 4.1 as `StepM` steps, `⟦P⟧` of M2's examples, the orders of Q13

Programs and graphs of `Examples.lean` (`Examples.abc`, `ex41`, `abcG1`, `abcG2`); the model is
`Model.p2p` with M2's `consAPB` (`AP`), the tie-break `Sel.least` (`rep .least`).

* `stepM_of_hasSucc`: a successor found by M2's `stepM` (checked by `hasSucc`, by key and
  order) is a `StepM`-successor of a configuration satisfying the invariant.
* Example 4.1 (`ex41`, threads in the order `T3, T1, T2`): `ex41_reach1`, `ex41_reach2`: the
  two reported configurations are reached by `StepM` (the second through the revisit of the
  receive by `send(T3, 2)`), have no next event, and their graphs are in `⟦P⟧`
  (`reported_mem_sem`).
* `ex41_sem_iff`: `⟦ex41⟧` is exactly `{abcG1, abcG2}` (by `mem_semEnum_iff'` from M2's
  computation `ex41_sem`), so the two reported graphs are all of `⟦P⟧`.
* Q13 (`pTwo`: two threads, each one send; model `asyn`): `opLe_not_nrLe` (`OpLe ⊄ NrLe`),
  `prefix_not_nrLe` (`IsPrefixOf ⊄ NrLe`), `prefix_not_opLe` (`IsPrefixOf ⊄ OpLe` when the
  larger graph is consistent but not an execution of `P`).
-/

namespace Must

namespace AlgEx

open MustFast MustFast' Examples Graph

/-- A successor found by M2's `stepM` by order and key is a `StepM`-successor (`p2p`, `AP`). -/
theorem stepM_of_hasSucc {T : Sel VPred} {P : Program VPred} {c : Config VPred}
    (hi : c.Inv Model.p2p P) {o : List (Ev VPred)} {K : Graph VPred} (hK : K.Supp)
    (h : hasSucc (Variant.repaired AP T) P c o K = true) :
    StepM Model.p2p (T.pick AP) P c ⟨K, o⟩ := by
  obtain ⟨d, hd, hdk⟩ := List.any_eq_true.mp h
  obtain ⟨ho, hk⟩ := of_decide_eq_true hdk
  have hstep := ((stepM_iff_compute_p2p T P hi).2 d).mp hd
  have hG : d.G = K := (eq_iff_key (hstep.inv hi).wf.supp hK).mpr hk
  obtain ⟨dG, dO⟩ := d
  simp only at hG ho
  subst hG ho
  exact hstep

theorem supp_empty : (Graph.empty : Graph VPred).Supp := fun _ _ => ⟨rfl, rfl⟩

/-! ### Example 4.1 -/

/-- The tie-break. -/
abbrev tieL : Tie VPred := Sel.least.pick AP

/-- `S(T3,1)`. -/
def x1 : Config VPred := ⟨Graph.empty.addSend abcS1, [abcS1]⟩
/-- `S(T3,1); R <- S(T3,1)` (Q7: the receive is available once a send can be read). -/
def x2 : Config VPred := ⟨(Graph.empty.addSend abcS1).addRecv abcR (.snd abcS1), [abcS1, abcR]⟩
/-- `S(T3,1); R <- S(T3,1); S(T3,2)`: graph 1. -/
def x3 : Config VPred := ⟨abcG1, [abcS1, abcR, abcS2]⟩
/-- The revisit of `R` by `S(T3,2)`: `S(T3,1); R <- S(T3,2); S(T3,2)`: graph 2. -/
def x4 : Config VPred := ⟨abcG2, [abcS1, abcR, abcS2]⟩

theorem x1_supp : x1.G.Supp := supp_empty.add _ _ _
theorem x2_supp : x2.G.Supp := (supp_empty.add _ _ _).add _ _ _
theorem x3_supp : x3.G.Supp := ((supp_empty.add _ _ _).add _ _ _).add _ _ _
theorem x4_supp : x4.G.Supp := ((supp_empty.add _ _ _).add _ _ _).add _ _ _

theorem ex41_succs : hasSucc (rep .least) ex41 .init x1.order x1.G = true ∧
    hasSucc (rep .least) ex41 x1 x2.order x2.G = true ∧
    hasSucc (rep .least) ex41 x2 x3.order x3.G = true ∧
    hasSucc (rep .least) ex41 x2 x4.order x4.G = true ∧
    stepM AP (rep .least) ex41 x3 = none ∧ stepM AP (rep .least) ex41 x4 = none := by
  decide +kernel

theorem ex41_reach_x2 : ReachM Model.p2p tieL ex41 x2 := by
  have h0 : ReachM Model.p2p tieL ex41 .init := Relation.ReflTransGen.refl
  have h1 : ReachM Model.p2p tieL ex41 x1 :=
    h0.tail (stepM_of_hasSucc h0.sound x1_supp ex41_succs.1)
  exact h1.tail (stepM_of_hasSucc h1.sound x2_supp ex41_succs.2.1)

/-- Example 4.1, graph 1: reached by `StepM`, reported (no next event), in `⟦P⟧`. -/
theorem ex41_reach1 : ReachM Model.p2p tieL ex41 x3 ∧ Model.p2p.nextP ex41 x3.G = none ∧
    Model.p2p.Sem ex41 abcG1 := by
  have h3 : ReachM Model.p2p tieL ex41 x3 :=
    ex41_reach_x2.tail (stepM_of_hasSucc ex41_reach_x2.sound x3_supp ex41_succs.2.2.1)
  have hn : Model.p2p.nextP ex41 x3.G = none :=
    (stepM_iff_compute_p2p _ _ h3.sound).1.mp ex41_succs.2.2.2.2.1
  exact ⟨h3, hn, reported_mem_sem h3 hn⟩

/-- Example 4.1, graph 2: reached by `StepM` through the revisit, reported, in `⟦P⟧`. -/
theorem ex41_reach2 : ReachM Model.p2p tieL ex41 x4 ∧ Model.p2p.nextP ex41 x4.G = none ∧
    Model.p2p.Sem ex41 abcG2 := by
  have h4 : ReachM Model.p2p tieL ex41 x4 :=
    ex41_reach_x2.tail (stepM_of_hasSucc ex41_reach_x2.sound x4_supp ex41_succs.2.2.2.1)
  have hn : Model.p2p.nextP ex41 x4.G = none :=
    (stepM_iff_compute_p2p _ _ h4.sound).1.mp ex41_succs.2.2.2.2.2
  exact ⟨h4, hn, reported_mem_sem h4 hn⟩

/-- The step from `x2` to `x4` changes the source of a receive of `x2`. -/
theorem x2_x4_rf : x2.G.rf abcR ≠ x4.G.rf abcR := by decide +kernel

/-- The step from `x2` to `x4` is by the `revisit` constructor (`StepM.revisit_of_rf_ne`). -/
theorem x2_x4_revisit : ∃ e r, Model.p2p.nextP ex41 x2.G = some e ∧ e.IsSend ∧
    RevGuard tieL (x2.add e none none) r e ∧
    Model.p2p.cons ((x2.add e none none).revisitCfg r e).G ∧
    x4 = (x2.add e none none).revisitCfg r e :=
  (stepM_of_hasSucc ex41_reach_x2.sound x4_supp ex41_succs.2.2.2.1).revisit_of_rf_ne
    ex41_reach_x2.sound (by decide +kernel) (Ne.symm x2_x4_rf)

/-! ### Explicit revisit steps -/

/-- The guards of Q15, as a Boolean (with M2's `revCond`). -/
def guardB (T : Sel VPred) (H : Config VPred) (r s : Ev VPred) : Bool :=
  decide (r ∈ H.G.events ∧ r.IsRecv ∧ s.Matches r ∧ ¬ H.G.porf r s) &&
    decide (∀ d ∈ insert r (H.del r s), revCond (oracleQ9 AP T) H d s = true) &&
    revCond (oracleQ9 AP T) H s s

theorem revGuard_of_guardB {T : Sel VPred} {H : Config VPred} {r s : Ev VPred}
    (h : guardB T H r s = true) : RevGuard (T.pick AP) H r s := by
  unfold guardB at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := Bool.and_eq_true _ _ ▸ (Bool.and_eq_true _ _ ▸ h)
  obtain ⟨g1, g2, g3, g4⟩ := of_decide_eq_true h1
  exact ⟨g1, g2, g3, g4, fun d hd => (revCond_iff T H d s).mp (of_decide_eq_true h2 d hd),
    (revCond_iff T H s s).mp h3⟩

/-- A revisit step by the `revisit` constructor, from Boolean checks (`p2p`, `AP`). -/
theorem stepM_revisit_of_check {T : Sel VPred} {P : Program VPred} {c : Config VPred}
    {e r : Ev VPred} (hS : c.G.Supp) (hn : P.nextP AP c.G = some e) (hSe : e.IsSend)
    (hg : guardB T (c.add e none none) r e = true)
    (hc : AP ((c.add e none none).revisitCfg r e).G = true) :
    StepM Model.p2p (T.pick AP) P c ((c.add e none none).revisitCfg r e) := by
  have hG := revGuard_of_guardB hg
  refine .revisit ?_ hSe hG ?_
  · rw [← Model.nextP_eq _ consAPB_iff_p2p P hS]
    exact hn
  · exact (consAPB_iff_p2p _ (((hS.add _ _ _).setRF hG.mem _).restrict _)).mp hc

/-! ### A revisit with a non-empty `Deleted` (`pFuel`, plan Section 2b) -/

/-- `a = send(T1, 0)` of `T0`. -/
abbrev fa : Ev VPred := ⟨0, 0, .send .asyn 1 0⟩
/-- `r = recv()` of `T1`. -/
abbrev fr : Ev VPred := ⟨1, 0, .recv ⟨.asyn, true⟩ .any⟩
/-- `c = send(T0, 0)` of `T1`. -/
abbrev fc : Ev VPred := ⟨1, 1, .send .asyn 0 0⟩
/-- `b = send(T1, 1)` of `T2`. -/
abbrev fb : Ev VPred := ⟨2, 0, .send .asyn 1 1⟩

/-- `a`. -/
def y1 : Config VPred := ⟨Graph.empty.addSend fa, [fa]⟩
/-- `a; r ↦ a`. -/
def y2 : Config VPred := ⟨(Graph.empty.addSend fa).addRecv fr (.snd fa), [fa, fr]⟩
/-- `a; r ↦ a; c`. -/
def y3 : Config VPred := ⟨((Graph.empty.addSend fa).addRecv fr (.snd fa)).addSend fc, [fa, fr, fc]⟩

theorem y1_supp : y1.G.Supp := supp_empty.add _ _ _
theorem y2_supp : y2.G.Supp := (supp_empty.add _ _ _).add _ _ _
theorem y3_supp : y3.G.Supp := ((supp_empty.add _ _ _).add _ _ _).add _ _ _

theorem pFuel_checks : hasSucc (rep .least) pFuel .init y1.order y1.G = true ∧
    hasSucc (rep .least) pFuel y1 y2.order y2.G = true ∧
    hasSucc (rep .least) pFuel y2 y3.order y3.G = true ∧
    pFuel.nextP AP y3.G = some fb ∧ guardB .least (y3.add fb none none) fr fb = true ∧
    AP ((y3.add fb none none).revisitCfg fr fb).G = true ∧
    (y3.add fb none none).del fr fb = {fc} := by
  decide +kernel

/-- The revisit of `r` by `b` deleting `c` (`Deleted = {c}`, non-empty) is reached by `StepM`,
through the `revisit` constructor. -/
theorem pFuel_revisit : (y3.add fb none none).del fr fb = {fc} ∧
    ReachM Model.p2p tieL pFuel ((y3.add fb none none).revisitCfg fr fb) := by
  have h0 : ReachM Model.p2p tieL pFuel .init := Relation.ReflTransGen.refl
  have h1 : ReachM Model.p2p tieL pFuel y1 :=
    h0.tail (stepM_of_hasSucc h0.sound y1_supp pFuel_checks.1)
  have h2 : ReachM Model.p2p tieL pFuel y2 :=
    h1.tail (stepM_of_hasSucc h1.sound y2_supp pFuel_checks.2.1)
  have h3 : ReachM Model.p2p tieL pFuel y3 :=
    h2.tail (stepM_of_hasSucc h2.sound y3_supp pFuel_checks.2.2.1)
  obtain ⟨-, -, -, hn, hg, hc, hd⟩ := pFuel_checks
  exact ⟨hd, h3.tail (stepM_revisit_of_check y3_supp hn (by simp [Ev.IsSend, Lab.IsSend]) hg hc)⟩

/-! ### The consistency check of line 13 rejects a revisit (`p2p`) -/

/-- `T1: send_p2p(T3, 1); send_p2p(T3, 2)`, `T3: recv_p2p()`, threads in the order `T3, T0, T1,
T2`. -/
def pRej : Program VPred := (ofCodes [.done, sp 3 1 (sp 3 2), .done, rbp]).reorder [3, 0, 1, 2]
  (by decide)

/-- `send_p2p(T3, 1)`. -/
abbrev ra : Ev VPred := ⟨1, 0, .send .p2p 3 1⟩
/-- `send_p2p(T3, 2)`. -/
abbrev rb' : Ev VPred := ⟨1, 1, .send .p2p 3 2⟩
/-- `recv_p2p()`. -/
abbrev rR : Ev VPred := ⟨3, 0, .recv ⟨.p2p, true⟩ .any⟩

/-- `ra`. -/
def z1 : Config VPred := ⟨Graph.empty.addSend ra, [ra]⟩
/-- `ra; R ↦ ra`. -/
def z2 : Config VPred := ⟨(Graph.empty.addSend ra).addRecv rR (.snd ra), [ra, rR]⟩

theorem z1_supp : z1.G.Supp := supp_empty.add _ _ _
theorem z2_supp : z2.G.Supp := (supp_empty.add _ _ _).add _ _ _

theorem pRej_checks : hasSucc (rep .least) pRej .init z1.order z1.G = true ∧
    hasSucc (rep .least) pRej z1 z2.order z2.G = true ∧
    pRej.nextP AP z2.G = some rb' ∧ guardB .least (z2.add rb' none none) rR rb' = true ∧
    AP ((z2.add rb' none none).revisitCfg rR rb').G = false := by
  decide +kernel

/-- Line 13 filters: at the reachable `z2`, `next_P` is the second send, the guards of the
revisit of `R` by it hold, but the successor (`R` reads `2` while `1` stays unread before it in
`so`) is not `p2p`-consistent, so it is not a `StepM`-successor. -/
theorem pRej_rejected : ReachM Model.p2p tieL pRej z2 ∧
    Model.p2p.nextP pRej z2.G = some rb' ∧ RevGuard tieL (z2.add rb' none none) rR rb' ∧
    ¬ Model.p2p.cons ((z2.add rb' none none).revisitCfg rR rb').G ∧
    ¬ StepM Model.p2p tieL pRej z2 ((z2.add rb' none none).revisitCfg rR rb') := by
  have h0 : ReachM Model.p2p tieL pRej .init := Relation.ReflTransGen.refl
  have h1 : ReachM Model.p2p tieL pRej z1 :=
    h0.tail (stepM_of_hasSucc h0.sound z1_supp pRej_checks.1)
  have h2 : ReachM Model.p2p tieL pRej z2 :=
    h1.tail (stepM_of_hasSucc h1.sound z2_supp pRej_checks.2.1)
  obtain ⟨-, -, hn, hg, hc⟩ := pRej_checks
  have hG := revGuard_of_guardB hg
  have hnc : ¬ Model.p2p.cons ((z2.add rb' none none).revisitCfg rR rb').G := fun h => by
    have h' := (consAPB_iff_p2p _ (((z2_supp.add _ _ _).setRF hG.mem _).restrict _)).mpr h
    exact Bool.noConfusion (h'.symm.trans hc)
  refine ⟨h2, ?_, hG, hnc, fun hs => hnc (hs.inv h2.sound).cons⟩
  rw [← Model.nextP_eq _ consAPB_iff_p2p pRej z2_supp]
  exact hn

theorem ex41_not_truncated : semTruncated ex41 10 = false := by decide +kernel

/-- `⟦ex41⟧` is `{graph 1, graph 2}` (from M2's computation, by `mem_semEnum_iff'`). -/
theorem ex41_sem_iff {G : Graph VPred} (hS : G.Supp) :
    ex41.Sem AP G ↔ G.key = abcG1.key ∨ G.key = abcG2.key := by
  rw [← mem_semEnum_iff' AP 10 ex41_not_truncated hS]
  have hp := List.Perm.mem_iff (a := G.key) (of_decide_eq_true ex41_sem.1)
  simp only [List.mem_map, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  constructor
  · rintro ⟨c, hc, hk⟩
    rcases hp.mp ⟨c, hc, hk⟩ with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact hp.mpr (Or.inl h)
    · exact hp.mpr (Or.inr h)

/-! ### The orders of Q13 -/

/-- `T0: send(T2, 0)`, `T1: send(T2, 1)`. -/
def pTwo : Program VPred := ofCodes [sa 2 0, sa 2 1]

/-- The send of `T0`. -/
abbrev s0 : Ev VPred := ⟨0, 0, .send .asyn 2 0⟩
/-- The send of `T1`. -/
abbrev s1 : Ev VPred := ⟨1, 0, .send .asyn 2 1⟩

/-- `{s1}`. -/
def gS1 : Graph VPred := Graph.empty.add s1 none none
/-- `{s0}`. -/
def gS0 : Graph VPred := Graph.empty.add s0 none none
/-- `{s0, s1}`. -/
def gS01 : Graph VPred := gS0.add s1 none none

theorem gS0_supp : gS0.Supp := supp_empty.add _ _ _
theorem gS01_supp : gS01.Supp := gS0_supp.add _ _ _

theorem nextP_pTwo : Model.asyn.nextP pTwo Graph.empty = some s0 ∧
    Model.asyn.nextP pTwo gS0 = some s1 ∧ Model.asyn.nextP pTwo gS01 = none := by
  rw [← Model.nextP_eq _ consAsynB_iff_asyn pTwo supp_empty,
    ← Model.nextP_eq _ consAsynB_iff_asyn pTwo gS0_supp,
    ← Model.nextP_eq _ consAsynB_iff_asyn pTwo gS01_supp]
  decide +kernel

/-- A non-revisit step adding a send with `next_P = some e`. -/
theorem nrStep_eq {G G' : Graph VPred} {e : Ev VPred} (hn : Model.asyn.nextP pTwo G = some e)
    (hS : e.IsSend) (h : NrStepG Model.asyn pTwo G G') : G' = G.add e none none := by
  obtain ⟨e', src, out, ⟨hn', h⟩, rfl⟩ := h
  obtain rfl : e = e' := Option.some.inj (hn.symm.trans hn')
  rcases h with ⟨S, v, hl, -⟩ | ⟨hR, -⟩ | ⟨-, rfl, rfl, -⟩ | ⟨hL, -⟩
  · obtain ⟨m, d, v', hl'⟩ := (Lab.isSend_iff _).mp hS
    rw [hl'] at hl
    cases hl
  · exact absurd hR (Lab.IsSend.not_isRecv hS)
  · rfl
  · exact absurd hL (fun h => Lab.IsLoc.not_isRecv h (by
      obtain ⟨m, d, v', hl'⟩ := (Lab.isSend_iff _).mp hS
      simp [Ev.IsLoc, hl', Lab.IsLoc] at h))

/-- The graphs reachable from `∅` by non-revisit steps of `pTwo`: `∅`, `{s0}`, `{s0, s1}`. -/
theorem nrLe_pTwo {G : Graph VPred} (h : NrLe Model.asyn pTwo Graph.empty G) :
    G = Graph.empty ∨ G = gS0 ∨ G = gS01 := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hs ih =>
    rcases ih with rfl | rfl | rfl
    · exact Or.inr (Or.inl (nrStep_eq nextP_pTwo.1 (by simp [Ev.IsSend, Lab.IsSend]) hs))
    · exact Or.inr (Or.inr (nrStep_eq nextP_pTwo.2.1 (by simp [Ev.IsSend, Lab.IsSend]) hs))
    · obtain ⟨e, src, out, ⟨hn, -⟩, -⟩ := hs
      rw [nextP_pTwo.2.2] at hn
      cases hn

/-- `{s1}` is not reachable from `∅` by non-revisit steps (`next_P` adds `s0` first). -/
theorem not_nrLe_gS1 : ¬ NrLe Model.asyn pTwo Graph.empty gS1 := by
  intro h
  have hne : ∀ G : Graph VPred, G.events ≠ gS1.events → G ≠ gS1 := fun G h h' => h (h' ▸ rfl)
  rcases nrLe_pTwo h with h' | h' | h'
  · exact hne _ (by decide +kernel) h'.symm
  · exact hne _ (by decide +kernel) h'.symm
  · exact hne _ (by decide +kernel) h'.symm

/-- `{s1}` is reachable from `∅` by one operational step. -/
theorem opLe_gS1 : OpLe Model.asyn pTwo Graph.empty gS1 := by
  refine Relation.ReflTransGen.single ⟨s1, none, none, ⟨?_, ?_, ?_⟩, rfl⟩
  · rw [← Model.asyn_availM pTwo supp_empty]
    decide +kernel
  · exact Or.inr (Or.inr ⟨by simp [Ev.IsRecv, Lab.IsRecv], by simp [Ev.IsND, Lab.IsND], rfl, rfl⟩)
  · exact Model.asyn.ext_plain _ s1 Model.asyn.empty (by decide +kernel)
      (by simp [Ev.IsRecv, Lab.IsRecv]) (by simp [Ev.IsND, Lab.IsND])

/-- Q13: operational reachability does not imply non-revisit reachability. -/
theorem opLe_not_nrLe :
    OpLe Model.asyn pTwo Graph.empty gS1 ∧ ¬ NrLe Model.asyn pTwo Graph.empty gS1 :=
  ⟨opLe_gS1, not_nrLe_gS1⟩

/-- Q13: the causal-prefix order does not imply non-revisit reachability (`{s1}` is a
consistent execution of `pTwo` with prefix `∅`). -/
theorem prefix_not_nrLe :
    (Graph.empty : Graph VPred).IsPrefixOf gS1 ∧ Model.asyn.cons gS1 ∧ pTwo.Exec gS1 ∧
      ¬ NrLe Model.asyn pTwo Graph.empty gS1 :=
  ⟨empty_isPrefixOf _, (OpLe.isPrefixOf Model.asyn.empty opLe_gS1).2,
    OpLe.exec Model.asyn.empty (by simp [Program.Exec, Graph.empty]) opLe_gS1, not_nrLe_gS1⟩

/-- A consistent graph that is not an execution of `pTwo`: `T0` sends `7`. -/
def gBad : Graph VPred := Graph.empty.add ⟨0, 0, .send .asyn 2 7⟩ none none

/-- Q13: the causal-prefix order does not imply operational reachability when the larger graph is
not an execution of `P` (`isPrefixOf_opLe` needs that premise). -/
theorem prefix_not_opLe :
    (Graph.empty : Graph VPred).IsPrefixOf gBad ∧ Model.asyn.cons gBad ∧
      ¬ OpLe Model.asyn pTwo Graph.empty gBad := by
  refine ⟨empty_isPrefixOf _, Model.asyn.ext_plain _ _ Model.asyn.empty (by decide +kernel)
    (by simp [Ev.IsRecv, Lab.IsRecv]) (by simp [Ev.IsND, Lab.IsND]), fun h => ?_⟩
  have := OpLe.exec Model.asyn.empty (by simp [Program.Exec, Graph.empty]) h
  revert this
  decide +kernel

end AlgEx

end Must

#print axioms Must.AlgEx.stepM_of_hasSucc
#print axioms Must.AlgEx.ex41_reach1
#print axioms Must.AlgEx.ex41_reach2
#print axioms Must.AlgEx.x2_x4_revisit
#print axioms Must.AlgEx.stepM_revisit_of_check
#print axioms Must.AlgEx.pFuel_revisit
#print axioms Must.AlgEx.pRej_rejected
#print axioms Must.AlgEx.ex41_sem_iff
#print axioms Must.AlgEx.opLe_not_nrLe
#print axioms Must.AlgEx.prefix_not_nrLe
#print axioms Must.AlgEx.prefix_not_opLe
