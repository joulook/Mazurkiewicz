import Mazurkiewicz.Must.ModelMbox
import Mazurkiewicz.Must.GraphEx

/-!
# Witnesses of Section 3 (fate table rows marked M3)

Paper: Sections 3.1–3.2.1. Plan: Section 3 (fate table), decisions Q1, Q4, Q5, Q11. Receive
predicates are `VPred`; threads `T1, T2, T3` are `1, 2, 3`. Checks are by `decide` on the
decision procedures `consAsynB`, `consAPB`, `consCDB` and the conditions `BC` (through `wfD_iff`,
`consAPB_iff`, `consCDB_iff` on graphs with `Supp`), or by explicit proofs.

* `skip_asyn`, `skip_p2p`, `skip_cd`, `skip_mbox`: the predicate-sensitive regression examples
  of Definitions 3.4–3.7 (`M0-astra.md` item 7).
* `ex31_cd`: Example 3.1 under p2p and under cd.
* `mbox_printed_fifo`: Definition 3.7 as printed accepts a FIFO reversal; `mbox` (Q5) rejects it.
* `cd_restrict_differs`: the restriction sentence of Section 3.2 (p. 13) differs from
  Definition 3.8 (global `porf`, Q4); `gD_restrict_wfExceptContig`: the raw restriction is a
  graph of the printed Definition 3.3 (every `Wf` clause but `idx_contig`).
* `prefix_printed_po_false`: prefix-closedness fails for p2p under the printed `po` (any strict
  partial order); the graph is excluded by Q1.
* `ce_printed_false`: conditional extensibility as printed fails for every model (it rests on
  the missing destination in `S_vals(e)`); `ce_printed_dst_false` (model mismatch) and
  `ce_printed_match_false` (a `po`-maximal receive that is not the next event; depends on Q1).
* `thin_air_rejected`: a graph with a causal cycle is inconsistent in every model.
* `recvB_not_addable`, `recvNB_needs_bot`: the 3.2.1 sentence "all events apart from blocking
  receives can always be added": false for blocking receives, and for a non-blocking receive the
  addition may need `⊥` (the `⊥` case of Q11). The positive statement is
  `Model.exists_add_of_not_recvB`.
-/

namespace Must

namespace ModelEx

open Graph Model Relation

/-- The empty graph has `Supp`. -/
theorem supp_empty : (empty : Graph VPred).Supp := (empty_wf (Q := VPred)).supp

/-- `Supp` of a graph built by additions from the empty graph. -/
macro "supp_add" : tactic =>
  `(tactic| repeat (first | exact supp_empty | apply Supp.add))

/-- `MboxOrd`, with its quantifiers over the events of the graph (decidable). -/
theorem mboxOrd_of_fin {G : Graph VPred} {L : Ev VPred → Ev VPred → Prop}
    (h1 : ∀ a ∈ G.events, a.SendOf .mbox → ¬ L a a)
    (h2 : ∀ a ∈ G.events, ∀ b ∈ G.events, ∀ c ∈ G.events, a.SendOf .mbox → b.SendOf .mbox →
      c.SendOf .mbox → L a b → L b c → L a c)
    (h3 : ∀ a ∈ G.events, ∀ b ∈ G.events, a.SendOf .mbox → b.SendOf .mbox → a ≠ b →
      L a b ∨ L b a)
    (h4 : ∀ a ∈ G.events, ∀ b ∈ G.events, a.SendOf .mbox → b.SendOf .mbox → G.porf a b →
      L a b) : G.MboxOrd L :=
  ⟨fun a ha => h1 a ha.1 ha.2, fun a b c ha hb hc => h2 a ha.1 b hb.1 c hc.1 ha.2 hb.2 hc.2,
    fun a b ha hb => h3 a ha.1 b hb.1 ha.2 hb.2, fun a b ha hb => h4 a ha.1 b hb.1 ha.2 hb.2⟩

/-- A relation along which a natural-number rank increases is acyclic. -/
theorem acyclic_of_rank {α : Type} {r : α → α → Prop} (f : α → ℕ)
    (h : ∀ x y, r x y → f x < f y) : Maz.Acyclic r := by
  have key : ∀ x y, TransGen r x y → f x < f y := by
    intro x y hxy
    induction hxy with
    | single h' => exact h _ _ h'
    | tail _ h' ih => exact ih.trans (h _ _ h')
  exact fun a ha => lt_irrefl _ (key a a ha)

/-! ### Predicate-sensitive regression examples (Definitions 3.4–3.7) -/

/-- `T1: a = send_m(T2, 0)` -/
abbrev ea (m : Comm) : Ev VPred := ⟨1, 0, .send m 2 0⟩
/-- `T1: b = send_m(T2, 1)` -/
abbrev eb (m : Comm) : Ev VPred := ⟨1, 1, .send m 2 1⟩
/-- `T2: r = recv_m(p)` -/
abbrev er (m : Comm) (p : VPred) : Ev VPred := ⟨2, 0, .recv ⟨m, true⟩ p⟩
/-- `T2: q = recv_m(p)` -/
abbrev eq' (m : Comm) (p : VPred) : Ev VPred := ⟨2, 1, .recv ⟨m, true⟩ p⟩

/-- `r` (predicate `p`) reads `b`; `a` is unread. -/
abbrev skip1 (m : Comm) (p : VPred) : Graph VPred :=
  ((empty.addSend (ea m)).addSend (eb m)).addRecv (er m p) (.snd (eb m))

/-- `r` (predicate `p`) reads `b`, then `q` (predicate `p'`) reads `a`. -/
abbrev skip2 (m : Comm) (p p' : VPred) : Graph VPred :=
  (skip1 m p).addRecv (eq' m p') (.snd (ea m))

/-- `{1}` -/
abbrev p1 : VPred := .fin {1}
/-- `{0}` -/
abbrev p0 : VPred := .fin {0}
/-- `{0, 1}` -/
abbrev p01 : VPred := .fin {0, 1}

/-- `Supp` of `skip1`. -/
theorem supp_skip1 (m : Comm) (p : VPred) : (skip1 m p).Supp := by supp_add
/-- `Supp` of `skip2`. -/
theorem supp_skip2 (m : Comm) (p p' : VPred) : (skip2 m p p').Supp := by supp_add

/-- Definition 3.4 (p. 13: "consistent under asyn ... if it is well-formed"): `asyn` accepts the
four graphs. -/
theorem skip_asyn : asyn.cons (skip1 .asyn p1) ∧ asyn.cons (skip1 .asyn p01) ∧
    asyn.cons (skip2 .asyn p1 p0) ∧ asyn.cons (skip2 .asyn .any .any) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine asyn_cons_iff.mpr ((consAsynB_iff ?_).mp (by decide +kernel))
  · exact supp_skip1 _ _
  · exact supp_skip1 _ _
  · exact supp_skip2 _ _ _
  · exact supp_skip2 _ _ _

/-- Definition 3.5, p. 13: "(b) `[US]; G.so|dst; G.rf ∩ mval` is empty, and (c)
`G.po; G.rf⁻¹; (G.so|dst; G.rf ∩ mval)` is irreflexive"; "condition (b) precludes graphs where a
receive `r` reads from a send `s` and there exists an unread send `s'` po-before `s` that matches
`r`'s predicate". The conditions are predicate-sensitive (`∩ mval`): skipping the unread `a` is
consistent when `a` does not match `r` (`{1}`), not when it does (`{0, 1}`); reading `b` before
`a` is consistent when `a` does not match `r`, not when it does (any value). -/
theorem skip_p2p : p2p.cons (skip1 .p2p p1) ∧ ¬ p2p.cons (skip1 .p2p p01) ∧
    p2p.cons (skip2 .p2p p1 p0) ∧ ¬ p2p.cons (skip2 .p2p .any .any) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact p2p_cons_iff.mpr ((consAPB_iff (supp_skip1 _ _)).mp (by decide +kernel))
  · rw [p2p_cons_iff, ← consAPB_iff (supp_skip1 _ _)]
    decide +kernel
  · exact p2p_cons_iff.mpr ((consAPB_iff (supp_skip2 _ _ _)).mp (by decide +kernel))
  · rw [p2p_cons_iff, ← consAPB_iff (supp_skip2 _ _ _)]
    decide +kernel

/-- Definition 3.6 (p. 13: (b), (c) "assuming that `so ≜ [S^cd]; porf; [S^cd]`"): the same four
graphs with `cd` events, the same verdicts. -/
theorem skip_cd : cd.cons (skip1 .cd p1) ∧ ¬ cd.cons (skip1 .cd p01) ∧
    cd.cons (skip2 .cd p1 p0) ∧ ¬ cd.cons (skip2 .cd .any .any) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (consCDB_iff (supp_skip1 _ _)).mp (by decide +kernel)
  · rw [← consCDB_iff (supp_skip1 _ _)]
    decide +kernel
  · exact (consCDB_iff (supp_skip2 _ _ _)).mp (by decide +kernel)
  · rw [← consCDB_iff (supp_skip2 _ _ _)]
    decide +kernel

/-- The order `a < b` on the two sends. -/
def ordAB (x y : Ev VPred) : Prop := x = ea .mbox ∧ y = eb .mbox

instance : DecidableRel ordAB := fun x y => by
  unfold ordAB
  infer_instance

/-- Definition 3.7 repaired by Q5 (p. 13 prints (b), (c) "for some `so` total over
`G.E^mbox × G.E^mbox`"): the same four graphs with `mbox` events, the same verdicts. -/
theorem skip_mbox : mbox.cons (skip1 .mbox p1) ∧ ¬ mbox.cons (skip1 .mbox p01) ∧
    mbox.cons (skip2 .mbox p1 p0) ∧ ¬ mbox.cons (skip2 .mbox .any .any) := by
  refine ⟨?_, fun h => ?_, ?_, fun h => ?_⟩
  · refine mbox_cons_iff.mpr ⟨(wfD_iff (supp_skip1 _ _)).mp (by decide +kernel), ordAB,
      mboxOrd_of_fin (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel), by decide +kernel⟩
  · exact absurd (mbox_bc_porf h) (by decide +kernel)
  · refine mbox_cons_iff.mpr ⟨(wfD_iff (supp_skip2 _ _ _)).mp (by decide +kernel), ordAB,
      mboxOrd_of_fin (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel), by decide +kernel⟩
  · exact absurd (mbox_bc_porf h) (by decide +kernel)

/-! ### Example 3.1 under p2p and cd -/

/-- A blocking cd receive accepting every value. -/
abbrev rcd : Lab VPred := .recv ⟨.cd, true⟩ .any
/-- `T1: send_cd(T3, 1)` -/
abbrev c10 : Ev VPred := ⟨1, 0, .send .cd 3 1⟩
/-- `T1: send_cd(T2, 2)` -/
abbrev c11 : Ev VPred := ⟨1, 1, .send .cd 2 2⟩
/-- `T2: recv_cd()` -/
abbrev d20 : Ev VPred := ⟨2, 0, rcd⟩
/-- `T2: send_cd(T3, 3)` -/
abbrev c21 : Ev VPred := ⟨2, 1, .send .cd 3 3⟩
/-- `T3: recv_cd()` (first) -/
abbrev d30 : Ev VPred := ⟨3, 0, rcd⟩
/-- `T3: recv_cd()` (second) -/
abbrev d31 : Ev VPred := ⟨3, 1, rcd⟩

/-- The common part of the two graphs of Example 3.1 with `cd` events. -/
abbrev ex31cdBase : Graph VPred :=
  (((empty.addSend c10).addSend c11).addRecv d20 (.snd c11)).addSend c21

/-- Example 3.1, graph 1, `cd`: `T3` reads `1`, then `3`. -/
abbrev ex31cdA : Graph VPred := (ex31cdBase.addRecv d30 (.snd c10)).addRecv d31 (.snd c21)

/-- Example 3.1, graph 2, `cd`: `T3` reads `3`, then `1`. -/
abbrev ex31cdB : Graph VPred := (ex31cdBase.addRecv d30 (.snd c21)).addRecv d31 (.snd c10)

/-- Example 3.1: both graphs are p2p-consistent; with `cd` events, graph 2 is inconsistent
("there is a `porf` path between the two sends to `T3`, but the messages are received in the
opposite order", p. 14). -/
theorem ex31_cd : p2p.cons GraphEx.ex31a ∧ p2p.cons GraphEx.ex31b ∧ cd.cons ex31cdA ∧
    ¬ cd.cons ex31cdB := by
  have hA : GraphEx.ex31a.Supp := GraphEx.ex31a_wf.supp
  have hB : GraphEx.ex31b.Supp := GraphEx.ex31b_wf.supp
  have hA' : ex31cdA.Supp := by supp_add
  have hB' : ex31cdB.Supp := by supp_add
  refine ⟨p2p_cons_iff.mpr ((consAPB_iff hA).mp (by decide +kernel)),
    p2p_cons_iff.mpr ((consAPB_iff hB).mp (by decide +kernel)),
    (consCDB_iff hA').mp (by decide +kernel), ?_⟩
  rw [← consCDB_iff hB']
  decide +kernel

/-! ### Definition 3.7 as printed: `mbox_printed_fifo` -/

/-- A blocking mailbox receive accepting every value. -/
abbrev rmb : Lab VPred := .recv ⟨.mbox, true⟩ .any
/-- `T1: f1 = send_mbox(T2, 1)` -/
abbrev f1 : Ev VPred := ⟨1, 0, .send .mbox 2 1⟩
/-- `T1: f2 = send_mbox(T2, 2)` -/
abbrev f2 : Ev VPred := ⟨1, 1, .send .mbox 2 2⟩
/-- `T2: g1 = recv_mbox()` -/
abbrev g1 : Ev VPred := ⟨2, 0, rmb⟩
/-- `T2: g2 = recv_mbox()` -/
abbrev g2 : Ev VPred := ⟨2, 1, rmb⟩

/-- `T2` receives `2`, then `1`: a FIFO reversal. -/
abbrev gFifo : Graph VPred :=
  (((empty.addSend f1).addSend f2).addRecv g1 (.snd f2)).addRecv g2 (.snd f1)

/-- Definition 3.7 as printed (p. 13): well-formed, and (b), (c) "for some `so` total over
`G.E^mbox × G.E^mbox`", read as a strict total order on the mailbox events (sends and receives)
of the graph, with no further constraint. -/
def PrintedMbox (G : Graph VPred) : Prop :=
  G.Wf ∧ ∃ so : Ev VPred → Ev VPred → Prop,
    (∀ a ∈ G.events, a.lab.model? = some .mbox → ¬ so a a) ∧
    (∀ a ∈ G.events, ∀ b ∈ G.events, ∀ c ∈ G.events, a.lab.model? = some .mbox →
      b.lab.model? = some .mbox → c.lab.model? = some .mbox → so a b → so b c → so a c) ∧
    (∀ a ∈ G.events, ∀ b ∈ G.events, a.lab.model? = some .mbox → b.lab.model? = some .mbox →
      a ≠ b → so a b ∨ so b a) ∧
    G.BC so

/-- The order `f2 < f1 < g1 < g2`. -/
abbrev ordF : List (Ev VPred) := [f2, f1, g1, g2]

/-- The order of `ordF`. -/
def soF (x y : Ev VPred) : Prop := x ∈ ordF ∧ y ∈ ordF ∧ ordF.idxOf x < ordF.idxOf y

instance : DecidableRel soF := fun x y => by
  unfold soF
  infer_instance

/-- Definition 3.7 as printed accepts the FIFO reversal `gFifo` (with `so = f2 < f1 < g1 < g2`).
`PrintedMbox` takes the strongest reading of the stated order property ("total over
`G.E^mbox × G.E^mbox`": a strict total order); no reading of that property requires `so` to
extend causality, which is what Q5 adds;
`mbox` (Q5: the order contains `porf` between mailbox sends, so `f1 < f2`) rejects it. `gFifo`
is well-formed (consistent under `asyn`). -/
theorem mbox_printed_fifo : PrintedMbox gFifo ∧ ¬ mbox.cons gFifo ∧ asyn.cons gFifo := by
  have hS : gFifo.Supp := by supp_add
  have hW : gFifo.Wf := (wfD_iff hS).mp (by decide +kernel)
  refine ⟨⟨hW, soF, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩,
    fun h => absurd (mbox_bc_porf h) (by decide +kernel), asyn_cons_iff.mpr hW⟩

/-! ### Section 3.2, p. 13, the restriction sentence: `cd_restrict_differs` -/

/-- `T1: s1 = send_cd(T3, 1)` -/
abbrev k1 : Ev VPred := ⟨1, 0, .send .cd 3 1⟩
/-- `T1: a = send_asyn(T2, 0)` -/
abbrev ka : Ev VPred := ⟨1, 1, .send .asyn 2 0⟩
/-- `T2: b = recv_asyn()` -/
abbrev kb : Ev VPred := ⟨2, 0, .recv ⟨.asyn, true⟩ .any⟩
/-- `T2: s2 = send_cd(T3, 2)` -/
abbrev k2 : Ev VPred := ⟨2, 1, .send .cd 3 2⟩
/-- `T3: r1 = recv_cd()` -/
abbrev kr1 : Ev VPred := ⟨3, 0, rcd⟩
/-- `T3: r2 = recv_cd()` -/
abbrev kr2 : Ev VPred := ⟨3, 1, rcd⟩

/-- `s1 po a rf b po s2`; `T3` reads `s2`, then `s1` (`M0-opus.md` D4, `M0-astra.md` item 13). -/
abbrev gD : Graph VPred :=
  (((((empty.addSend k1).addSend ka).addRecv kb (.snd ka)).addSend k2).addRecv kr1
    (.snd k2)).addRecv kr2 (.snd k1)

/-- The `cd` events of `gD`. -/
abbrev Ecd : Finset (Ev VPred) := {k1, k2, kr1, kr2}

/-- `s2` as the first event of `T2`. -/
abbrev k2' : Ev VPred := ⟨2, 0, .send .cd 3 2⟩

/-- The `cd` events of `gD`, with `T2` renumbered from `0` (Q1). -/
abbrev gDcd : Graph VPred :=
  (((empty.addSend k1).addSend k2').addRecv kr1 (.snd k2')).addRecv kr2 (.snd k1)

/-- p. 13: "a graph `G` is consistent if for every communication model `M`, the restriction of
`G` to events of `M` satisfies the corresponding consistency predicate". This differs from
Definition 3.8 (global `porf`, Q4): `gD` is not `cd`-consistent (`s1 porf s2` through the `asyn`
events), but conditions (b), (c) of `cd` hold on the restriction of `gD` to its `cd` events
(whose `porf` does not order `s1`, `s2`). The raw restriction has an index gap in `T2` (it is not
well-formed under Q1); its renumbering `gDcd` is `cd`-consistent. -/
theorem cd_restrict_differs :
    gD.Wf ∧ ¬ cd.cons gD ∧ ¬ comb.cons gD ∧ gD.porf k1 k2 ∧
      ¬ (gD.restrict Ecd).porf k1 k2 ∧ (gD.restrict Ecd).BC (gD.restrict Ecd).soCD ∧
      ¬ (gD.restrict Ecd).Wf ∧ cd.cons gDcd := by
  have hS : gD.Supp := by supp_add
  have hS' : gDcd.Supp := by supp_add
  have hncd : ¬ cd.cons gD := by
    rw [← consCDB_iff hS]
    decide +kernel
  refine ⟨(wfD_iff hS).mp (by decide +kernel), hncd,
    fun h => hncd (ConsOf.anti (ms' := (· = .cd)) (fun _ _ => trivial) h),
    by decide +kernel, by decide +kernel, by decide +kernel, ?_,
    (consCDB_iff hS').mp (by decide +kernel)⟩
  rw [← wfD_iff (hS.restrict _)]
  decide +kernel

/-- The clauses of `Wf` other than `idx_contig`: a graph in the sense of the printed
Definitions 3.2, 3.3 (unique identities, `rf` well-formed, no causal cycle), without the
contiguity of indices that Q1 adds. -/
structure WfExceptContig (G : Graph VPred) : Prop where
  /-- an event is determined by its thread and index -/
  idx_inj : ∀ e ∈ G.events, ∀ e' ∈ G.events, e.tid = e'.tid → e.idx = e'.idx → e = e'
  /-- `rf` is defined exactly on the receives of the graph -/
  rf_isSome : ∀ e, (G.rf e).isSome ↔ e ∈ G.events ∧ e.IsRecv
  /-- only non-blocking receives read `⊥` -/
  rf_bot : ∀ r, G.rf r = some .bot → r.IsRecvNB
  /-- a source is an event of the graph -/
  rf_mem : ∀ r s, G.rf r = some (.snd s) → s ∈ G.events
  /-- a send is read at most once -/
  rf_once : ∀ r r' s, G.rf r = some (.snd s) → G.rf r' = some (.snd s) → r = r'
  /-- a source matches its receive -/
  rf_match : ∀ r s, G.rf r = some (.snd s) → s.Matches r
  /-- `nd` is defined exactly on the ND events of the graph -/
  nd_isSome : ∀ e, (G.nd e).isSome ↔ e ∈ G.events ∧ e.IsND
  /-- an outcome is in the set of its label -/
  nd_mem : ∀ e v, G.nd e = some v → v ∈ e.ndSet
  /-- no causal cycle -/
  porf_irrefl : ∀ a, ¬ G.porf a a

/-- The restriction of a well-formed graph to a set containing the sources of its kept
receives satisfies every clause of `Wf` except `idx_contig`. -/
theorem wfExceptContig_restrict {G : Graph VPred} (hG : G.Wf) {E : Finset (Ev VPred)}
    (hrf : ∀ r ∈ G.events ∩ E, G.SrcIn E r) : WfExceptContig (G.restrict E) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e1 h1 e2 h2
    exact hG.idx_inj e1 (Finset.mem_inter.mp h1).1 e2 (Finset.mem_inter.mp h2).1
  · intro e1
    rw [restrict_rf, restrict_events, Finset.mem_inter]
    by_cases h : e1 ∈ E
    · simp [h, hG.rf_isSome]
    · simp [h]
  · exact fun r1 h1 => hG.rf_bot r1 (restrict_rf_eq_some h1).1
  · intro r1 s h1
    obtain ⟨h1, hE⟩ := restrict_rf_eq_some h1
    have hr := Finset.mem_inter.mpr ⟨(hG.rf_some h1).1, hE⟩
    exact Finset.mem_inter.mpr ⟨hG.rf_mem _ _ h1, srcIn_iff.mp (hrf r1 hr) s h1⟩
  · exact fun r1 r2 s h1 h2 =>
      hG.rf_once _ _ _ (restrict_rf_eq_some h1).1 (restrict_rf_eq_some h2).1
  · exact fun r1 s h1 => hG.rf_match _ _ (restrict_rf_eq_some h1).1
  · intro e1
    rw [restrict_nd, restrict_events, Finset.mem_inter]
    by_cases h : e1 ∈ E
    · simp [h, hG.nd_isSome]
    · simp [h]
  · exact fun e1 v h1 => hG.nd_mem e1 v (restrict_nd_eq_some h1).1
  · exact fun a h => hG.porf_irrefl a (porf_restrict_le E h)

/-- The restriction of `gD` to its `cd` events is a graph in the sense of the printed
Definitions 3.2, 3.3: every clause of `Wf` holds except `idx_contig` (Q1). -/
theorem gD_restrict_wfExceptContig : WfExceptContig (gD.restrict Ecd) := by
  have hS : gD.Supp := by supp_add
  exact wfExceptContig_restrict ((wfD_iff hS).mp (by decide +kernel)) (by decide +kernel)

/-! ### Prefix-closedness with the printed `po`: `prefix_printed_po_false` -/

/-- `T1: a = send_p2p(T2, 0)` -/
abbrev pa : Ev VPred := ⟨1, 0, .send .p2p 2 0⟩
/-- `T1: b = send_p2p(T2, 1)` -/
abbrev pb : Ev VPred := ⟨1, 1, .send .p2p 2 1⟩
/-- `T2: r = recv_p2p()` -/
abbrev pr : Ev VPred := ⟨2, 0, GraphEx.rb⟩
/-- `T2: q = recv_p2p()` -/
abbrev pq : Ev VPred := ⟨2, 1, GraphEx.rb⟩

/-- `r` reads `b`, `q` reads `a`. -/
abbrev gP : Graph VPred :=
  (((empty.addSend pa).addSend pb).addRecv pr (.snd pb)).addRecv pq (.snd pa)

/-- A printed program order (Definition 3.2 (2): a strict partial order): `a < b` only; the
receives `r`, `q` of `T2` are unordered. -/
def po0 (x y : Ev VPred) : Prop := x = pa ∧ y = pb

instance : DecidableRel po0 := fun x y => by
  unfold po0
  infer_instance

/-- Causality steps with the printed program order. -/
def stepP (x y : Ev VPred) : Prop := po0 x y ∨ gP.rfRel x y

instance : DecidableRel stepP := fun x y => by
  unfold stepP
  infer_instance

/-- The set kept: `q` removed. -/
abbrev E0 : Finset (Ev VPred) := {pa, pb, pr}

/-- A rank increasing along `stepP`. -/
def rankP (x : Ev VPred) : ℕ := if x = pr then 2 else if x = pa then 0 else 1

/-- p. 14: "Restricting a consistent graph to a porf-prefix-closed subset of its events preserves
consistency", with Definition 3.2 (2), p. 12: "`po` ... is a strict partial order on events".
False for p2p (`M0-astra.md` item 10): `gP` with the program order `po0`
is p2p-consistent as printed (`po0` a strict partial order on the events, no causal cycle, (b),
(c) with `so = [S^p2p]; po0; [S^p2p]`); `E0` is closed under `po0 ∪ rf`; on the restriction to
`E0` condition (b) fails (`a` is now unread, `a so b`, `b rf r`, `a` matches `r`). Under Q1 the
two receives of `T2` are ordered (`r po q`) and `gP` itself is not p2p-consistent. -/
theorem prefix_printed_po_false :
    gP.Wf ∧ (∀ x, ¬ po0 x x) ∧ (∀ x y z, po0 x y → po0 y z → po0 x z) ∧
      (∀ x y, po0 x y → x ∈ gP.events ∧ y ∈ gP.events) ∧ Maz.Acyclic stepP ∧
      gP.CondB (soP2PWith po0) ∧ gP.CondCWith po0 (soP2PWith po0) ∧
      (∀ x y, stepP x y → y ∈ E0 → x ∈ E0) ∧
      ¬ (gP.restrict E0).CondB (soP2PWith po0) ∧ ¬ p2p.cons gP := by
  have hS : gP.Supp := by supp_add
  have hW : gP.Wf := (wfD_iff hS).mp (by decide +kernel)
  have hmem : ∀ x y, stepP x y → x ∈ gP.events ∧ y ∈ gP.events := by
    rintro x y (⟨rfl, rfl⟩ | ⟨hy, hrf⟩)
    · decide +kernel
    · exact ⟨hW.rf_mem y x hrf, hy⟩
  have hfin : ∀ x ∈ gP.events, ∀ y ∈ gP.events, stepP x y →
      rankP x < rankP y ∧ (y ∈ E0 → x ∈ E0) := by decide +kernel
  refine ⟨hW, fun x ⟨h1, h2⟩ => ?_, fun x y z ⟨_, h1⟩ ⟨h2, _⟩ => ?_,
    fun x y h => hmem x y (Or.inl h),
    acyclic_of_rank rankP fun x y h => (hfin x (hmem x y h).1 y (hmem x y h).2 h).1,
    by decide +kernel, by decide +kernel,
    fun x y h => (hfin x (hmem x y h).1 y (hmem x y h).2 h).2, by decide +kernel, ?_⟩
  · rw [h1] at h2
    exact absurd h2 (by decide)
  · rw [h1] at h2
    exact absurd h2 (by decide)
  · rw [p2p_cons_iff, ← consAPB_iff hS]
    decide +kernel

/-! ### Conditional extensibility as printed: `ce_printed_false` -/

/-- 3.2.1 Conditional Extensibility as printed (p. 14): for a graph `G` and a `G.po`-maximal
`e ∈ G.E` with `consistent(G \ {e})`, either (i) `e ∉ R` and `consistent(G)`, (ii) `e ∈ R` and
`consistent(G')` for some `G'` equal to `G` apart from the `rf` of `e`, or (iii) `e ∈ R^b` and
for all `s ∈ G.S_vals(e)` there is `r' ≠ e` with `G.rf(r') = s`. -/
def PrintedCE (cons : Graph VPred → Prop) : Prop :=
  ∀ (G : Graph VPred) (e : Ev VPred), e ∈ G.events → (∀ b ∈ G.events, ¬ G.po e b) →
    cons (G.remove {e}) →
    (¬ e.IsRecv ∧ cons G) ∨ (e.IsRecv ∧ ∃ x, cons { G with rf := Function.update G.rf e x }) ∨
    (e.IsRecvB ∧ ∀ s ∈ G.S, s.ValMatches e → ∃ r' ∈ G.events, r' ≠ e ∧ G.rf r' = some (.snd s))

/-- `T2: s = send(T3, 1)` -/
abbrev cs : Ev VPred := ⟨2, 0, .send .p2p 3 1⟩
/-- `T1: r = recv()`, blocking -/
abbrev cr : Ev VPred := ⟨1, 0, GraphEx.rb⟩

/-- `s`, and `r` with some source (here `⊥`; the printed (ii) ranges over all sources). -/
abbrev gC : Graph VPred := (empty.addSend cs).addRecv cr .bot

/-- Printed conditional extensibility fails for every model (`M0-opus.md` D6): in `gC`, `r` is
`po`-maximal and `gC \ {r} = {s}` is consistent; (i) fails (`r` is a receive), (ii) fails (`r`
has no well-formed source: `⊥` is excluded for a blocking receive, `s` goes to `T3`), (iii) fails
(`s ∈ G.S_vals(r)` is unread). The witness rests on the missing destination in the printed
`S_vals(e)`, a notational omission (the subscript convention `S_t` of p. 12 suggests it was
meant). Stronger witnesses: `ce_printed_dst_false` (destination added, model missing) and
`ce_printed_match_false` (fully matching reading, depends on Q1). The repair Q11 quantifies over
the sends to `tid r` of the model of `r` (`Model.ext_recvB`). -/
theorem ce_printed_false (M : Model VPred) : ¬ PrintedCE M.cons := by
  intro h
  have hrem : gC.remove {cr} = empty.addSend cs := by
    have h1 : (gC.remove {cr}).Supp := by
      unfold Graph.remove
      exact Supp.restrict (by supp_add) _
    have h2 : (empty.addSend cs : Graph VPred).Supp := by supp_add
    exact (eq_iff_key h1 h2).mpr (by decide +kernel)
  have hcons : M.cons (gC.remove {cr}) := by
    rw [hrem]
    exact M.ext_plain _ _ M.empty (by decide) (by decide) (by decide)
  rcases h gC cr (by decide) (by decide +kernel) hcons with ⟨hR, -⟩ | ⟨-, x, hx⟩ | ⟨-, hall⟩
  · exact hR (by decide)
  · have hW := M.wf _ hx
    have hx' : ({ gC with rf := Function.update gC.rf cr x } : Graph VPred).rf cr = x := by
      simp
    rcases x with _ | _ | s
    · have := (hW.rf_isSome cr).mpr ⟨by decide, by decide⟩
      rw [hx'] at this
      exact absurd this (by decide)
    · exact absurd (hW.rf_bot cr hx') (by decide)
    · have hno : ∀ s ∈ gC.events, ¬ s.Matches cr := by decide
      exact hno s (hW.rf_mem cr s hx') (hW.rf_match cr s hx')
  · have hno : ¬ ∃ r' ∈ gC.events, r' ≠ cr ∧ gC.rf r' = some (.snd cs) := by decide +kernel
    exact hno (hall cs (by decide) (by decide))

/-- Printed conditional extensibility with clause (iii) over a given set of sends:
`sv G s e` says that `s` is quantified for the receive `e`. -/
def PrintedCEWith (sv : Graph VPred → Ev VPred → Ev VPred → Prop)
    (cons : Graph VPred → Prop) : Prop :=
  ∀ (G : Graph VPred) (e : Ev VPred), e ∈ G.events → (∀ b ∈ G.events, ¬ G.po e b) →
    cons (G.remove {e}) →
    (¬ e.IsRecv ∧ cons G) ∨ (e.IsRecv ∧ ∃ x, cons { G with rf := Function.update G.rf e x }) ∨
    (e.IsRecvB ∧ ∀ s ∈ G.S, sv G s e → ∃ r' ∈ G.events, r' ≠ e ∧ G.rf r' = some (.snd s))

/-- `T2: send_cd(T1, 1)` -/
abbrev ms : Ev VPred := ⟨2, 0, .send .cd 1 1⟩

/-- `s` (cd, to `T1`) and the p2p blocking receive `r` of `T1` with some source (here `⊥`). -/
abbrev gM : Graph VPred := (empty.addSend ms).addRecv cr .bot

/-- Printed conditional extensibility with the destination added to `S_vals(e)` (sends to
`tid e` whose value satisfies `vals e`) still fails for every model: in `gM` the only send goes
to `T1` with a matching value but has model `cd`, the receive is `p2p`; (ii) has no well-formed
source, (iii) fails because `s` is unread. -/
theorem ce_printed_dst_false (M : Model VPred) :
    ¬ PrintedCEWith (fun _ s e => s.lab.dst? = some e.tid ∧ s.ValMatches e) M.cons := by
  intro h
  have hrem : gM.remove {cr} = empty.addSend ms := by
    have h1 : (gM.remove {cr}).Supp := by
      unfold Graph.remove
      exact Supp.restrict (by supp_add) _
    have h2 : (empty.addSend ms : Graph VPred).Supp := by supp_add
    exact (eq_iff_key h1 h2).mpr (by decide +kernel)
  have hcons : M.cons (gM.remove {cr}) := by
    rw [hrem]
    exact M.ext_plain _ _ M.empty (by decide) (by decide) (by decide)
  rcases h gM cr (by decide) (by decide +kernel) hcons with ⟨hR, -⟩ | ⟨-, x, hx⟩ | ⟨-, hall⟩
  · exact hR (by decide)
  · have hW := M.wf _ hx
    have hx' : ({ gM with rf := Function.update gM.rf cr x } : Graph VPred).rf cr = x := by
      simp
    rcases x with _ | _ | s
    · have := (hW.rf_isSome cr).mpr ⟨by decide, by decide⟩
      rw [hx'] at this
      exact absurd this (by decide)
    · exact absurd (hW.rf_bot cr hx') (by decide)
    · have hno : ∀ s ∈ gM.events, ¬ s.Matches cr := by decide
      exact hno s (hW.rf_mem cr s hx') (hW.rf_match cr s hx')
  · have hno : ¬ ∃ r' ∈ gM.events, r' ≠ cr ∧ gM.rf r' = some (.snd ms) := by decide +kernel
    exact hno (hall ms (by decide) (by decide))

/-- `T1: send_p2p(T3, 0)`, index `0` -/
abbrev g0 : Ev VPred := ⟨1, 0, .send .p2p 3 0⟩
/-- `T2: send_p2p(T1, 1)` -/
abbrev gs : Ev VPred := ⟨2, 0, .send .p2p 1 1⟩
/-- `T1: recv_p2p()`, blocking, index `2` -/
abbrev gr2 : Ev VPred := ⟨1, 2, GraphEx.rb⟩

/-- `T1` has events with indices `0` and `2`: the receive `r` is `po`-maximal but not the next
event of its thread. -/
abbrev gN : Graph VPred := ((empty.addSend g0).addSend gs).addRecv gr2 .bot

/-- Printed conditional extensibility with the fully matching reading of clause (iii) (sends
matching `e` in destination, value and model) fails for every model, under Q1: in `gN` the
receive `r` is `po`-maximal and `gN \ {r}` is consistent, but `r` is not the next event of `T1`
(index `2`, no index `1`), so no choice of its source gives a well-formed graph (Q1 requires
contiguous indices: `idx_contig`), and the matching send `s` is unread. The printed premise "a
`G.po`-maximal event" does not say that `G` is a legal fresh extension of `G \ {e}`
(`M0-astra.md` item 11); Q11 quantifies over fresh events. -/
theorem ce_printed_match_false (M : Model VPred) :
    ¬ PrintedCEWith (fun _ s e => s.Matches e) M.cons := by
  intro h
  have hrem : gN.remove {gr2} = (empty.addSend g0).addSend gs := by
    have h1 : (gN.remove {gr2}).Supp := by
      unfold Graph.remove
      exact Supp.restrict (by supp_add) _
    have h2 : ((empty.addSend g0).addSend gs : Graph VPred).Supp := by supp_add
    exact (eq_iff_key h1 h2).mpr (by decide +kernel)
  have hcons : M.cons (gN.remove {gr2}) := by
    rw [hrem]
    exact M.ext_plain _ _ (M.ext_plain _ _ M.empty (by decide) (by decide) (by decide))
      (by decide) (by decide) (by decide)
  rcases h gN gr2 (by decide) (by decide +kernel) hcons with ⟨hR, -⟩ | ⟨-, x, hx⟩ | ⟨-, hall⟩
  · exact hR (by decide)
  · have hW := M.wf _ hx
    have hmem : gr2 ∈ gN.events := by decide
    obtain ⟨e', he', ht, hi⟩ := hW.idx_contig gr2 hmem 1 (by decide)
    have hno : ∀ e' ∈ gN.events, ¬ (e'.tid = gr2.tid ∧ e'.idx = 1) := by decide
    exact hno e' he' ⟨ht, hi⟩
  · have hno : ¬ ∃ r' ∈ gN.events, r' ≠ gr2 ∧ gN.rf r' = some (.snd gs) := by decide +kernel
    exact hno (hall gs (by decide) (by decide))

/-! ### No thin air; events that can be added -/

/-- No "Out-of-Thin-Air" (p. 14: "given a graph `G` with `consistent(G)`, then `G.porf` is
irreflexive"; proved for every model, `Model.porf_irrefl`): the causal cycle of `GraphEx.cyc` is
inconsistent in every model. -/
theorem thin_air_rejected (M : Model VPred) : ¬ M.cons GraphEx.cyc :=
  fun h => GraphEx.not_wf_cyc (M.wf _ h)

/-- `T1: recv()`, blocking -/
abbrev rB0 : Ev VPred := ⟨1, 0, GraphEx.rb⟩
/-- `T1: try_recv()`, non-blocking -/
abbrev rNB0 : Ev VPred := ⟨1, 0, GraphEx.rnb⟩

/-- p. 14: "all events apart from blocking receives can always be added in a consistent
manner" (the positive part: `Model.exists_add_of_not_recvB`). A blocking receive cannot always be
added: on the (consistent) empty graph no source
(none, `⊥`, or a send) makes its addition consistent, in any model. -/
theorem recvB_not_addable (M : Model VPred) :
    M.cons empty ∧ ∀ src out, ¬ M.cons (empty.add rB0 src out) := by
  refine ⟨M.empty, fun src out h => ?_⟩
  have hW := M.wf _ h
  have hrf : (empty.add rB0 src out).rf rB0 = src := by simp
  rcases src with _ | _ | s
  · have := (hW.rf_isSome rB0).mpr ⟨by simp, by decide⟩
    rw [hrf] at this
    exact absurd this (by decide)
  · exact absurd (hW.rf_bot rB0 hrf) (by decide)
  · have hs := hW.rf_mem rB0 s hrf
    rw [add_events] at hs
    have hno : ∀ s ∈ insert rB0 (Graph.empty : Graph VPred).events, ¬ s.Matches rB0 := by
      decide
    exact hno s hs (hW.rf_match rB0 s hrf)

/-- A non-blocking receive can be added to the empty graph only with `⊥`, in any model. This
shows that the `⊥` source is necessary in this case; it does not refute printed clause (ii),
which only asks for some consistent source (here `⊥`). What the printed conditions lack is the
contract that `⊥` always works (`Model.ext_bot`), used by the canonical replay. -/
theorem recvNB_needs_bot (M : Model VPred) :
    M.cons (empty.addRecv rNB0 .bot) ∧ ∀ s, ¬ M.cons (empty.addRecv rNB0 (.snd s)) := by
  refine ⟨M.ext_bot _ _ M.empty (by decide) (by decide), fun s h => ?_⟩
  have hW := M.wf _ h
  have hrf : (empty.addRecv rNB0 (.snd s)).rf rNB0 = some (.snd s) := by simp
  have hs := hW.rf_mem rNB0 s hrf
  rw [add_events] at hs
  have hno : ∀ s ∈ insert rNB0 (Graph.empty : Graph VPred).events, ¬ s.Matches rNB0 := by
    decide
  exact hno s hs (hW.rf_match rNB0 s hrf)

end ModelEx

end Must

#print axioms Must.ModelEx.skip_asyn
#print axioms Must.ModelEx.skip_p2p
#print axioms Must.ModelEx.skip_cd
#print axioms Must.ModelEx.skip_mbox
#print axioms Must.ModelEx.ex31_cd
#print axioms Must.ModelEx.mbox_printed_fifo
#print axioms Must.ModelEx.cd_restrict_differs
#print axioms Must.ModelEx.gD_restrict_wfExceptContig
#print axioms Must.ModelEx.prefix_printed_po_false
#print axioms Must.ModelEx.ce_printed_false
#print axioms Must.ModelEx.ce_printed_dst_false
#print axioms Must.ModelEx.ce_printed_match_false
#print axioms Must.ModelEx.thin_air_rejected
#print axioms Must.ModelEx.recvB_not_addable
#print axioms Must.ModelEx.recvNB_needs_bot
