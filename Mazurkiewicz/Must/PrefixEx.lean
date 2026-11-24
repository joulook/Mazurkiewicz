import Mazurkiewicz.Must.PrefixNext
import Mazurkiewicz.Must.AlgEx

/-!
# Examples of M6: `PrefixExtension`, `availPrefix`, both cases of Lemma A.14

Program `pNx` (threads in the order `T0, T1, T2`; model `Model.asyn`, decided by M2's
`consAsynB`):

`T0: r = recv_nb()`, `T1: y = send(T2, 5); s = send(T0, 1)`, `T2: z = send(T1, 9)`.

* `gT = {y, s, z, r ↦ s}`, `gB = {y, s, z, r ↦ ⊥}`: both consistent executions of `pNx`;
  `next_P(∅) = r`.
* Case 2 (`ex_case2`): `∅ ⊏ gT`, `e = r` reads `s ∉ ∅`; `PrefixExtension(∅, gT, s) = {y}`; the
  two operational steps give `G' = {y, s, r ↦ s} ⊑ gT`, `G' ≠ gT`; no `G''` with `r ∈ G''` lies
  strictly between `∅` and `G'`; no single operational step from `∅` adding `r` stays below `gT`
  (`ex_case2_no_case1`, `case1_iff`).
* Case 1 with source `⊥` (`ex_case1_bot`): `∅ → {r ↦ ⊥} ⊑ gB`. Case 1 with a source in `G_s`
  (`ex_case1_src`): `G_s = {y, s}`, `G_s → {y, s, r ↦ s} ⊑ gT`.
* `availPrefix` (`ex_availPrefix`): in `gT`, for an event of `T1` it is `{y, s}`, for `T2` `{z}`;
  for `T0` in `{y}` (no event of `T0`) it is the empty graph.
* The causal predecessors of `r` in `gT` (`ex_pred`): `{y, s}` = `availSet(∅, T0) ∪ {s} ∪
  gT.pred s`.
* Printed A.14's `GetSend(G_s, …)` (p. 30): the source of `r` in `G_s = ∅` is undefined
  (`ex_getSend_printed`, an illustration of the typing repair, not a witness of falsity); the
  repaired `GetSend(G_t, e)` is `s` (`ex_case2`). Printed line 12 of Algorithm 2 reads
  `GetSend(G_t, r)` with `r` unbound (`r₀` of line 11 is meant).
* Case 2 with `G_s ≠ ∅` (`ex_case2_nonempty`): `G_s = {z}`; `PrefixExtension({z}, gT, s) =
  {z, y}`; `G' = gT`; `s` is unread in `G_p + s` and `r` is the next event of `T0` in `G_p`.
* Case 1 with a blocking receive under `p2p` (`ex_case1_blocking`, program `pBl`:
  `T0: r = recv_b()` (p2p), `T1: send_p2p(T0, 1)`): `G_s = {s}`, `G_s → {s, r ↦ s} ⊑ G_t`; the
  blocking branch of `Pfx.step_of_next` (`Usable` through the source `s`) is used.

Printed statements of A.13/A.14 that needed a repair: only the typing of `GetSend` in A.14
(illustrated by `ex_getSend_printed`; no witness of falsity exists). A.13 holds as printed under
Definition A.4 (`prefixExt_existsUnique`, with weaker hypotheses); the minimality of A.14 holds
as printed (`revTarget_no_between`).
-/

namespace Must

namespace PrefixEx

open MustFast MustFast' Examples AlgEx Graph

/-- The program. -/
def pNx : Program VPred := ofCodes [rnb, sa 2 5 (sa 0 1), sa 1 9]

abbrev r : Ev VPred := ⟨0, 0, .recv ⟨.asyn, false⟩ .any⟩
abbrev y : Ev VPred := ⟨1, 0, .send .asyn 2 5⟩
abbrev s : Ev VPred := ⟨1, 1, .send .asyn 0 1⟩
abbrev z : Ev VPred := ⟨2, 0, .send .asyn 1 9⟩

/-- `{y}`. -/
def gY : Graph VPred := Graph.empty.addSend y
/-- `{y, s}`. -/
def gYS : Graph VPred := gY.addSend s
/-- `{y, s, r ↦ s}`. -/
def gYSR : Graph VPred := gYS.addRecv r (.snd s)
/-- `{y, s, z, r ↦ s}`. -/
def gT : Graph VPred := (gYS.addSend z).addRecv r (.snd s)
/-- `{y, s, z, r ↦ ⊥}`. -/
def gB : Graph VPred := (gYS.addSend z).addRecv r .bot
/-- `{r ↦ ⊥}`. -/
def gRB : Graph VPred := Graph.empty.addRecv r .bot
/-- `{z}`. -/
def gZ : Graph VPred := Graph.empty.addSend z

theorem gY_supp : gY.Supp := supp_empty.add _ _ _
theorem gYS_supp : gYS.Supp := gY_supp.add _ _ _
theorem gYSR_supp : gYSR.Supp := gYS_supp.add _ _ _
theorem gT_supp : gT.Supp := (gYS_supp.add _ _ _).add _ _ _
theorem gB_supp : gB.Supp := (gYS_supp.add _ _ _).add _ _ _
theorem gZ_supp : gZ.Supp := supp_empty.add _ _ _

theorem cons_of (G : Graph VPred) (hS : G.Supp) (h : G.consAsynB = true) : Model.asyn.cons G :=
  (consAsynB_iff_asyn G hS).mp h

theorem gT_facts : gT.consAsynB = true ∧ pNx.Exec gT ∧ gB.consAsynB = true ∧ pNx.Exec gB ∧
    gYS.consAsynB = true ∧ pNx.Exec gYS := by
  decide +kernel

theorem empty_exec : pNx.Exec Graph.empty := by simp [Program.Exec, Graph.empty]

theorem pfx_empty (G : Graph VPred) (hc : Model.asyn.cons G) (hE : pNx.Exec G) :
    Pfx Model.asyn pNx Graph.empty G :=
  Pfx.of_isPrefixOf hc hE (Graph.empty_isPrefixOf G)

theorem pfx_gT : Pfx Model.asyn pNx Graph.empty gT :=
  pfx_empty gT (cons_of _ gT_supp gT_facts.1) gT_facts.2.1

theorem pfx_gB : Pfx Model.asyn pNx Graph.empty gB :=
  pfx_empty gB (cons_of _ gB_supp gT_facts.2.2.1) gT_facts.2.2.2.1

theorem next_empty : Model.asyn.nextP pNx Graph.empty = some r := by
  rw [← Model.nextP_eq _ consAsynB_iff_asyn pNx supp_empty]
  decide +kernel

theorem next_gYS : Model.asyn.nextP pNx gYS = some r := by
  rw [← Model.nextP_eq _ consAsynB_iff_asyn pNx gYS_supp]
  decide +kernel

theorem sPfx_gT : SPfx Model.asyn pNx Graph.empty gT :=
  sPfx_iff_exists.mpr ⟨pfx_gT, r, by decide, by simp [Graph.empty]⟩

/-- An illustration of the typing repair of A.14 (not a witness of falsity; the first conjunct
holds by `rfl`). Printed A.14 calls `GetSend(G_s, G_t, e)`; `GetSend(G_s, e)` (Algorithm 2,
lines 24–25, first argument `G_s`) is undefined for the next event: here `∅.rf r = none`. The
repaired call is `GetSend(G_t, e) = G_t.rf(e) = s`. -/
theorem ex_getSend_printed : (Graph.empty : Graph VPred).rf r = none ∧ gT.rf r = some (.snd s) :=
  ⟨rfl, by decide⟩

/-- `PrefixExtension(∅, gT, s) = {y}`. -/
theorem ex_prefixExt : prefixExt Graph.empty gT s = gY :=
  (eq_iff_key (gT_supp.restrict _) gY_supp).mpr (by decide +kernel)

/-- Lemma A.14, Case 2, on `pNx`: `∅ ⊏ gT`, `next_P(∅) = r`, `r` reads `s ∉ ∅` in `gT`.
`G_p = {y}`; `{y} → {y, s} → {y, s, r ↦ s} = G'` are operational steps; `G' ⊑ gT`, `∅ ⊏ G'`,
`G' ≠ gT`, and no `G''` with `r ∈ G''.E` satisfies `∅ ⊏ G'' ⊏ G'`. -/
theorem ex_case2 :
    prefixExt Graph.empty gT s = gY ∧ revTarget Graph.empty gT s r = gYSR ∧
    OpAdd Model.asyn pNx gY s none none ∧
    OpAdd Model.asyn pNx gYS r (some (.snd s)) none ∧
    Pfx Model.asyn pNx gYSR gT ∧ SPfx Model.asyn pNx Graph.empty gYSR ∧ gYSR ≠ gT ∧
    ¬ ∃ G'', r ∈ G''.events ∧ SPfx Model.asyn pNx Graph.empty G'' ∧
      SPfx Model.asyn pNx G'' gYSR := by
  have hn := nextEv_of_nextP next_empty
  have hrT : r ∈ gT.events := by decide
  have h := next_prefix_case2 pfx_gT hn hrT ex_getSend_printed.2 (by simp [Graph.empty])
  have hrev : revTarget Graph.empty gT s r = gYSR := by
    unfold revTarget
    rw [ex_prefixExt]
    rfl
  rw [hrev, ex_prefixExt] at h
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := h
  refine ⟨ex_prefixExt, hrev, h1, h2, h3, h4, fun he => ?_, h5⟩
  have : gYSR.events = gT.events := by rw [he]
  revert this
  decide +kernel

/-- On `pNx`, no step from `∅` adding `r` stays below `gT` (Case 1 fails, Algorithm 2 line 9). -/
theorem ex_case2_no_case1 :
    ¬ ∃ src out, OpAdd₀ Model.asyn pNx Graph.empty r src out ∧
      Pfx Model.asyn pNx (Graph.empty.add r src out) gT := by
  rw [case1_iff pfx_gT (nextEv_of_nextP next_empty) (by decide)]
  intro h
  simpa [Graph.empty] using h s ex_getSend_printed.2

/-- Lemma A.14, Case 1 with source `⊥`, on `pNx`: `∅ → {r ↦ ⊥}` is an operational step and
`{r ↦ ⊥} ⊑ gB`. Via `next_prefix` (the first disjunct). -/
theorem ex_case1_bot :
    OpAdd Model.asyn pNx Graph.empty r (some .bot) none ∧ Pfx Model.asyn pNx gRB gB := by
  have hrB : r ∈ gB.events := by decide
  have hrf : gB.rf r = some .bot := by decide
  have hnd : gB.nd r = none := by decide
  have hsp : SPfx Model.asyn pNx Graph.empty gB :=
    sPfx_iff_exists.mpr ⟨pfx_gB, r, hrB, by simp [Graph.empty]⟩
  rcases next_prefix hsp next_empty hrB with ⟨-, h1, h2⟩ | ⟨s₀, hs, -⟩
  · rw [hrf, hnd] at h1 h2
    exact ⟨h1, h2⟩
  · rw [hrf] at hs
    cases hs

/-- Lemma A.14, Case 1 with the source in `G_s`, on `pNx`: `G_s = {y, s} ⊏ gT`,
`next_P(G_s) = r`, and `{y, s} → {y, s, r ↦ s} ⊑ gT`. -/
theorem ex_case1_src :
    OpAdd Model.asyn pNx gYS r (some (.snd s)) none ∧ Pfx Model.asyn pNx gYSR gT := by
  have hp : Pfx Model.asyn pNx gYS gT := by
    refine Pfx.of_isPrefixOf pfx_gT.cons' pfx_gT.exec' ⟨gYS.events, ?_, ?_⟩
    · decide +kernel
    · exact (eq_iff_key gYS_supp (gT_supp.restrict _)).mpr (by decide +kernel)
  have h := next_prefix_case1 hp (nextEv_of_nextP next_gYS) (by decide) (by
    intro s' hs'
    rw [ex_getSend_printed.2] at hs'
    cases hs'
    decide)
  rw [ex_getSend_printed.2, (by decide : gT.nd r = none)] at h
  exact h

/-- `availPrefix` (Definition A.6) on `gT`: `{y, s}` for an event of `T1` (last event `s`),
`{z}` for `T2`; for `T0` in `{y}`, which has no event of `T0`, the empty graph. -/
theorem ex_availPrefix :
    availPrefix gT y = gYS ∧ availPrefix gT z = gZ ∧ availPrefix gY r = Graph.empty := by
  refine ⟨(eq_iff_key (gT_supp.restrict _) gYS_supp).mpr (by decide +kernel),
    (eq_iff_key (gT_supp.restrict _) gZ_supp).mpr (by decide +kernel), ?_⟩
  exact availPrefix_eq_empty (Model.asyn.wf _ ((consAsynB_iff_asyn gY gY_supp).mp
    (by decide +kernel))) (by decide +kernel)

/-- The causal predecessors of `r` in `gT`: `{y, s}`, which is
`availSet(∅, T0) ∪ {s} ∪ gT.pred s` (`pred_next_of_src`). -/
theorem ex_pred :
    gT.pred r = {y, s} ∧ gT.pred r = Graph.empty.availSet r.tid ∪ insert s (gT.pred s) := by
  refine ⟨by decide +kernel, ?_⟩
  exact pred_next_of_src pfx_gT (by decide) (Model.idx_of_nextEv (nextEv_of_nextP next_empty))
    ex_getSend_printed.2

/-! ### Case 2 with a non-empty `G_s` -/

/-- `{z, y}`. -/
def gZY : Graph VPred := gZ.addSend y

theorem gZY_supp : gZY.Supp := gZ_supp.add _ _ _

/-- Lemma A.14, Case 2, with `G_s = {z} ≠ ∅`: `{z} ⊏ gT`, `next_P({z}) = r` reads `s ∉ {z}`;
`G_p = PrefixExtension({z}, gT, s) = {z, y}`; `s` is unread in `G_p + s`; `r` is the next event
of `T0` in `G_p`; the two operational steps give `G' = gT`; minimality. -/
theorem ex_case2_nonempty :
    gZ ≠ Graph.empty ∧ SPfx Model.asyn pNx gZ gT ∧ Model.asyn.nextP pNx gZ = some r ∧
    prefixExt gZ gT s = gZY ∧ s ∈ (gZY.addSend s).US ∧ pNx.nextEv gZY r.tid = some r ∧
    OpAdd Model.asyn pNx gZY s none none ∧ OpAdd Model.asyn pNx (gZY.addSend s) r (some (.snd s))
      none ∧ revTarget gZ gT s r = gT ∧
    ¬ ∃ G'', r ∈ G''.events ∧ SPfx Model.asyn pNx gZ G'' ∧ SPfx Model.asyn pNx G'' gT := by
  have hp : Pfx Model.asyn pNx gZ gT := by
    refine Pfx.of_isPrefixOf pfx_gT.cons' pfx_gT.exec' ⟨gZ.events, ?_, ?_⟩
    · decide +kernel
    · exact (eq_iff_key gZ_supp (gT_supp.restrict _)).mpr (by decide +kernel)
  have hnP : Model.asyn.nextP pNx gZ = some r := by
    rw [← Model.nextP_eq _ consAsynB_iff_asyn pNx gZ_supp]
    decide +kernel
  have hn := nextEv_of_nextP hnP
  have hrT : r ∈ gT.events := by decide
  have hs₀ : s ∉ gZ.events := by decide
  have hpe : prefixExt gZ gT s = gZY :=
    (eq_iff_key (gT_supp.restrict _) gZY_supp).mpr (by decide +kernel)
  have hrev : revTarget gZ gT s r = gT := by
    refine (eq_iff_key (((gT_supp.restrict _).add _ _ _).add _ _ _) gT_supp).mpr ?_
    decide +kernel
  have h := next_prefix_case2 hp hn hrT ex_getSend_printed.2 hs₀
  have hu := (case2_unread hp hn ex_getSend_printed.2).2
  have hne := case2_nextEv_e_Gp hp hn ex_getSend_printed.2
  rw [hpe] at h hu hne
  rw [hrev] at h
  obtain ⟨-, h1, h2, -, h4, h5⟩ := h
  refine ⟨fun he => ?_, h4, hnP, hpe, hu, hne, h1, h2, hrev, h5⟩
  have : gZ.events = (Graph.empty : Graph VPred).events := by rw [he]
  revert this
  decide +kernel

/-! ### Case 1 with a blocking receive under `p2p` -/

/-- `T0: r = recv_b()` (p2p), `T1: send_p2p(T0, 1)`. -/
def pBl : Program VPred := ofCodes [rbp, sp 0 1]

abbrev bR : Ev VPred := ⟨0, 0, .recv ⟨.p2p, true⟩ .any⟩
abbrev bS : Ev VPred := ⟨1, 0, .send .p2p 0 1⟩

/-- `{s}`. -/
def gBS : Graph VPred := Graph.empty.addSend bS
/-- `{s, r ↦ s}`. -/
def gBT : Graph VPred := gBS.addRecv bR (.snd bS)

theorem gBS_supp : gBS.Supp := supp_empty.add _ _ _
theorem gBT_supp : gBT.Supp := gBS_supp.add _ _ _

/-- Lemma A.14, Case 1, with a blocking receive under `p2p`: `G_s = {s} ⊏ G_t = {s, r ↦ s}`,
`next_P(G_s) = r` (blocking), the source `s` of `r` in `G_t` is in `G_s`, and `G_s → G_t` is an
operational step adding `r` reading `s` (availability of `r` through the consistent source `s`:
the blocking branch of `Pfx.step_of_next`); `G_s + r ⊑ G_t`. -/
theorem ex_case1_blocking :
    bR.IsRecvB ∧ SPfx Model.p2p pBl gBS gBT ∧ Model.p2p.nextP pBl gBS = some bR ∧
    OpAdd Model.p2p pBl gBS bR (some (.snd bS)) none ∧
    Pfx Model.p2p pBl (gBS.add bR (some (.snd bS)) none) gBT ∧
    gBS.add bR (some (.snd bS)) none = gBT := by
  have hcT : Model.p2p.cons gBT := (consAPB_iff_p2p gBT gBT_supp).mp (by decide +kernel)
  have hET : pBl.Exec gBT := by decide +kernel
  have hp : Pfx Model.p2p pBl gBS gBT := by
    refine Pfx.of_isPrefixOf hcT hET ⟨gBS.events, ?_, ?_⟩
    · decide +kernel
    · exact (eq_iff_key gBS_supp (gBT_supp.restrict _)).mpr (by decide +kernel)
  have hnP : Model.p2p.nextP pBl gBS = some bR := by
    rw [← Model.nextP_eq _ consAPB_iff_p2p pBl gBS_supp]
    decide +kernel
  have hrf : gBT.rf bR = some (.snd bS) := by decide
  have h := next_prefix_case1 hp (nextEv_of_nextP hnP) (by decide) (by
    intro s' hs'
    rw [hrf] at hs'
    cases hs'
    decide)
  rw [hrf, (by decide : gBT.nd bR = none)] at h
  exact ⟨by decide, sPfx_iff_exists.mpr ⟨hp, bR, by decide, by decide⟩, hnP, h.1, h.2, rfl⟩

end PrefixEx

end Must

#print axioms Must.PrefixEx.ex_getSend_printed
#print axioms Must.PrefixEx.ex_prefixExt
#print axioms Must.PrefixEx.ex_case2
#print axioms Must.PrefixEx.ex_case2_no_case1
#print axioms Must.PrefixEx.ex_case1_bot
#print axioms Must.PrefixEx.ex_case1_src
#print axioms Must.PrefixEx.ex_availPrefix
#print axioms Must.PrefixEx.ex_pred
#print axioms Must.PrefixEx.ex_case2_nonempty
#print axioms Must.PrefixEx.ex_case1_blocking
