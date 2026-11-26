import Mazurkiewicz.Induction.MP.Steps

/-!
# Message passing: steps under `asyn` and `p2p`, def:p2p, lem:terminal (2) (milestone C1b)

`induction-popl`, `mp.tex` (lem:mp-step, lem:terminal (2)) and `p2p.tex` (def:p2p,
lem:p2p-model, lem:p2p-step), for the graphs, programs and models of the Must port (plan
`plan/ind/TRACK-C-PLAN.md`, milestone C1b).

* lem:mp-step (`asyn_step`), lem:p2p-step (`p2p_step`): the steps from a consistent execution,
  by the kind of the next label of a thread. The `p2p` receive case excludes a source with an
  unread `so|dst`-earlier send that the receive accepts (`Graph.SoDst`, `Ev.ValMatches` of the
  port; on a `p2p` receive this is the paper's `so` and `⋈`).
* def:p2p as printed (`Graph.soPaper`, `Graph.P1`, `Graph.P2`, `MP/Defs.lean`) is the port's
  `Model.p2p` on graphs whose sends are all tagged `p2p` (`p2p_cons_iff_paper`). The premise is
  needed: with two `asyn` sends of thread 1 to thread 2, the second read first by an `asyn`
  receive, `Model.p2p.cons` holds (the port's `so` relates `p2p` sends only) and `P1` fails.
* lem:p2p-model is `Model.p2p` itself (its fields `empty`, `prefixClosed`, `wf`, the last
  giving (A1) by `Graph.Wf.porf_irrefl`); nothing new is stated.
* lem:terminal (2), on raw graphs: `FullRaw` (a full execution in the sense of def:exec, no
  consistency), `Graph.WfExceptBot` (every clause of `Graph.Wf` except `rf_bot`, which is
  def:asyn (i)), `botEv`, `botExt` (`G^⊥`: every stuck thread of the program gets its blocking
  receive reading `⊥`); `botExt_graph`, `botExt_full`, `botExt_restrict`, `botExt_incons`.
-/

namespace Must

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]

namespace Graph

/-- Every clause of well-formedness (`Graph.Wf`) except `rf_bot` (only non-blocking receives
read `⊥`, def:asyn (i)): the graphs of def:graph. -/
structure WfExceptBot (G : Graph Q) : Prop where
  /-- an event is determined by its thread and index -/
  idx_inj : ∀ e ∈ G.events, ∀ e' ∈ G.events, e.tid = e'.tid → e.idx = e'.idx → e = e'
  /-- the indices of a thread are contiguous from `0` -/
  idx_contig : ∀ e ∈ G.events, ∀ i < e.idx, ∃ e' ∈ G.events, e'.tid = e.tid ∧ e'.idx = i
  /-- `rf` is defined exactly on the receives of the graph -/
  rf_isSome : ∀ e, (G.rf e).isSome ↔ e ∈ G.events ∧ e.IsRecv
  /-- a source is an event of the graph -/
  rf_mem : ∀ r s, G.rf r = some (.snd s) → s ∈ G.events
  /-- a send is read at most once -/
  rf_once : ∀ r r' s, G.rf r = some (.snd s) → G.rf r' = some (.snd s) → r = r'
  /-- a source matches its receive: destination, value, model -/
  rf_match : ∀ r s, G.rf r = some (.snd s) → s.Matches r
  /-- `nd` is defined exactly on the ND events of the graph -/
  nd_isSome : ∀ e, (G.nd e).isSome ↔ e ∈ G.events ∧ e.IsND
  /-- an outcome is in the set of its label -/
  nd_mem : ∀ e v, G.nd e = some v → v ∈ e.ndSet
  /-- no causal cycle -/
  porf_irrefl : ∀ a, ¬ G.porf a a

end Graph

namespace Ind

variable {M : Model Q} {P : Program Q} {G G' : Graph Q}

/-! ### Steps, for a model given by its receive condition -/

/-- The steps from a consistent execution, for a model whose receive steps reading a send are
described by `ok`. -/
theorem opStepG_iff_of (hG : ExecM M P G) (ok : Ev Q → Ev Q → Prop)
    (hrecv : ∀ (e s : Ev Q), e.idx = G.cnt e.tid →
      (M.cons (G.addRecv e (.snd s)) ↔ s ∈ G.US ∧ s.Matches e ∧ ok s e)) :
    OpStepG M P G G' ↔ ∃ t ∈ P.threads, ∃ l, P.step t (G.trace t) = some l ∧
      ((¬ l.IsRecv ∧ ¬ l.IsND ∧ G' = G.add ⟨t, G.cnt t, l⟩ none none) ∨
       (l.IsND ∧ ∃ v ∈ l.ndSet, G' = G.addND ⟨t, G.cnt t, l⟩ v) ∨
       (∃ s ∈ G.US, s.Matches ⟨t, G.cnt t, l⟩ ∧ ok s ⟨t, G.cnt t, l⟩ ∧
          G' = G.addRecv ⟨t, G.cnt t, l⟩ (.snd s)) ∨
       (l.IsRecvNB ∧ G' = G.addRecv ⟨t, G.cnt t, l⟩ .bot)) := by
  have hc := hG.2
  constructor
  · rintro ⟨e, src, out, ⟨hav, hadm, hce⟩, rfl⟩
    obtain ⟨t, ht, hn, -⟩ := M.mem_availM_iff'.mp hav
    have hidx := Model.idx_of_nextEv hn
    unfold Program.nextEv at hn
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hn
    refine ⟨t, ht, l, hl, ?_⟩
    rcases hadm with ⟨hR, rfl, rfl | ⟨s, -, rfl⟩⟩ | ⟨hN, rfl, v, hv, rfl⟩ | ⟨hR, hN, rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inr ⟨(M.wf _ hce).rf_bot ⟨t, G.cnt t, l⟩ (by simp), rfl⟩))
    · obtain ⟨hU, hm, hok⟩ := (hrecv _ s hidx).mp hce
      exact Or.inr (Or.inr (Or.inl ⟨s, hU, hm, hok, rfl⟩))
    · exact Or.inr (Or.inl ⟨hN, v, hv, rfl⟩)
    · exact Or.inl ⟨hR, hN, rfl⟩
  · rintro ⟨t, ht, l, hl, h⟩
    have hn : P.nextEv G t = some ⟨t, G.cnt t, l⟩ := by simp [Program.nextEv, hl]
    have hidx : (⟨t, G.cnt t, l⟩ : Ev Q).idx = G.cnt (⟨t, G.cnt t, l⟩ : Ev Q).tid := rfl
    have hav : ∀ e, P.nextEv G t = some e → M.Usable G e → e ∈ M.availM P G :=
      fun e h1 h2 => M.mem_availM_iff'.mpr ⟨t, ht, h1, h2⟩
    rcases h with ⟨hR, hN, rfl⟩ | ⟨hN, v, hv, rfl⟩ | ⟨s, hU, hm, hok, rfl⟩ | ⟨hNB, rfl⟩
    · exact ⟨_, _, _, ⟨hav _ hn (Or.inl fun hB => hR (Lab.IsRecvB.isRecv hB)),
        Or.inr (Or.inr ⟨hR, hN, rfl, rfl⟩), M.ext_plain _ _ hc hidx hR hN⟩, rfl⟩
    · exact ⟨_, _, _, ⟨hav _ hn (Or.inl fun hB => Lab.IsND.not_isRecv hN (Lab.IsRecvB.isRecv hB)),
        Or.inr (Or.inl ⟨hN, rfl, v, hv, rfl⟩), M.ext_nd _ _ v hc hidx hN hv⟩, rfl⟩
    · have hce := (hrecv _ s hidx).mpr ⟨hU, hm, hok⟩
      exact ⟨_, _, _, ⟨hav _ hn (Or.inr ⟨s, G.US_subset_S hU, hce⟩),
        Or.inl ⟨hm.isRecv, rfl, Or.inr ⟨s, G.US_subset_S hU, rfl⟩⟩, hce⟩, rfl⟩
    · exact ⟨_, _, _, ⟨hav _ hn (Or.inl (Lab.not_isRecvB_of_isRecvNB hNB)),
        Or.inl ⟨Lab.IsRecvNB.isRecv hNB, rfl, Or.inl rfl⟩, M.ext_bot _ _ hc hidx hNB⟩, rfl⟩

/-- lem:mp-step: the steps under `asyn` from a consistent execution. -/
theorem asyn_step (hG : ExecM Model.asyn P G) :
    OpStepG Model.asyn P G G' ↔ ∃ t ∈ P.threads, ∃ l, P.step t (G.trace t) = some l ∧
      ((¬ l.IsRecv ∧ ¬ l.IsND ∧ G' = G.add ⟨t, G.cnt t, l⟩ none none) ∨
       (l.IsND ∧ ∃ v ∈ l.ndSet, G' = G.addND ⟨t, G.cnt t, l⟩ v) ∨
       (∃ s ∈ G.US, s.Matches ⟨t, G.cnt t, l⟩ ∧ G' = G.addRecv ⟨t, G.cnt t, l⟩ (.snd s)) ∨
       (l.IsRecvNB ∧ G' = G.addRecv ⟨t, G.cnt t, l⟩ .bot)) := by
  have hGw : G.Wf := Model.asyn.wf _ hG.2
  rw [opStepG_iff_of hG (fun _ _ => True) fun e s hidx => ?_]
  · simp only [true_and]
  · constructor
    · intro h
      exact ⟨(Model.asyn.src_of_cons hG.2 hidx h).1, (Model.asyn.src_of_cons hG.2 hidx h).2,
        trivial⟩
    · rintro ⟨hU, hm, -⟩
      exact Model.asyn_cons_iff.mpr (hGw.addRecv hidx hU hm)

omit [DecidableEq Q] in
/-- On a well-formed graph, a send `so|dst`-before the source of a receive (the port's
`Graph.SoDst`) that accepts the value matches the receive. -/
theorem matches_of_soDst (hG : G.Wf) {s' s r : Ev Q} (hso : G.SoDst s' s)
    (hrf : G.rf r = some (.snd s)) (hv : s'.ValMatches r) : s'.Matches r := by
  have hm := hG.rf_match r s hrf
  obtain ⟨-, hR, hd, -, hmod⟩ := Ev.matches_iff.mp hm
  refine Ev.matches_iff.mpr ⟨hso.2.1, hR, ?_, hv, ?_⟩
  · rw [← Model.dstOf_eq, hso.2.2.2.2.2, Model.dstOf_eq, hd]
  · rw [hso.1, ← hso.2.2.1, hmod]

/-- lem:p2p-step: the steps under `p2p` from a consistent execution. A receive may read an
unread matching send `s` only if no unread send `so|dst`-before `s` accepts its value. -/
theorem p2p_step (hG : ExecM Model.p2p P G) :
    OpStepG Model.p2p P G G' ↔ ∃ t ∈ P.threads, ∃ l, P.step t (G.trace t) = some l ∧
      ((¬ l.IsRecv ∧ ¬ l.IsND ∧ G' = G.add ⟨t, G.cnt t, l⟩ none none) ∨
       (l.IsND ∧ ∃ v ∈ l.ndSet, G' = G.addND ⟨t, G.cnt t, l⟩ v) ∨
       (∃ s ∈ G.US, s.Matches ⟨t, G.cnt t, l⟩ ∧
          (∀ s' ∈ G.US, ¬ (G.SoDst s' s ∧ s'.ValMatches ⟨t, G.cnt t, l⟩)) ∧
          G' = G.addRecv ⟨t, G.cnt t, l⟩ (.snd s)) ∨
       (l.IsRecvNB ∧ G' = G.addRecv ⟨t, G.cnt t, l⟩ .bot)) := by
  have hGw : G.Wf := Model.p2p.wf _ hG.2
  refine opStepG_iff_of hG (fun s e => ∀ s' ∈ G.US, ¬ (G.SoDst s' s ∧ s'.ValMatches e))
    fun e s hidx => ⟨fun h => ?_, fun ⟨hU, hm, hok⟩ => ?_⟩
  · obtain ⟨hU, hm⟩ := Model.p2p.src_of_cons hG.2 hidx h
    refine ⟨hU, hm, fun s' hs' ⟨hso, hv⟩ => ?_⟩
    obtain ⟨-, hb, -⟩ := Model.p2p_cons_iff.mp h
    have he := hGw.not_mem_of_idx_eq_cnt hidx
    have hsG : s ∈ G.events := ((G.mem_US).mp hU).1
    have hss : s' ≠ s := fun h' => lt_irrefl s.idx (h' ▸ hso.2.2.2.2.1.2.2.2)
    have hsrc : ∀ x, some (Src.snd s) = some (.snd x) → x ∈ G.events := fun x hx => by
      cases hx
      exact hsG
    have hU' : s' ∈ (G.addRecv e (.snd s)).US :=
      (hGw.mem_US_add hidx hsrc).mpr (Or.inr ⟨hs', fun h' => hss (by cases h'; rfl)⟩)
    refine hb s' hU' s (Finset.mem_insert_of_mem hsG) e (Finset.mem_insert_self _ _)
      ⟨⟨hso.1, hso.2.1, hso.2.2.1, hso.2.2.2.1, ?_, hso.2.2.2.2.2⟩, by simp, hv⟩
    exact ⟨Finset.mem_insert_of_mem hso.2.2.2.2.1.1, Finset.mem_insert_of_mem hsG,
      hso.2.2.2.2.1.2.2⟩
  · have hW' := hGw.addRecv hidx hU hm
    have hbc : G.BC G.soP2P := (show Graph.ConsOf (· = Comm.p2p) G from hG.2).2.1 rfl
    have hsrc : ∀ x, some (Src.snd s) = some (.snd x) → x ∈ G.events := fun x hx => by
      cases hx
      exact ((G.mem_US).mp hU).1
    change Graph.ConsOf (· = Comm.p2p) (G.addRecv e (.snd s))
    refine ⟨hW', fun _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    refine hGw.bc_add hidx hW' hbc (fun a ha b hb ⟨x, y, z⟩ => ⟨x, y, po_add_of_mem ha hb z⟩)
      (fun b _ ⟨_, _, z⟩ => hGw.not_po_add_left hidx b z) ?_
    intro s₀ hs₀ s' hs' _ hso hd hv
    cases hs₀
    refine hok s' hs' ⟨⟨hso.1.2, hso.1.1, hso.2.1.2, hso.2.1.1, hso.2.2, ?_⟩, hv⟩
    rw [Model.dstOf_eq, Model.dstOf_eq]
    exact hd

/-! ### def:p2p as printed -/

/-- def:p2p (`so`, (P1), (P2) as printed) is the port's `Model.p2p`, on graphs whose sends are
all tagged `p2p`. Without the premise the statement is false (Opus r2 N1): thread 1 sends
`asyn (2,1)` then `asyn (2,2)`, thread 2 `asyn`-receives the second first; `Model.p2p.cons`
holds and `P1` fails. -/
theorem p2p_cons_iff_paper (hT : G.SendsTagged .p2p) :
    Model.p2p.cons G ↔ G.Wf ∧ G.P1 ∧ G.P2 := by
  rw [Model.p2p_cons_iff]
  have hso : ∀ s' s, G.soPaper s' s → G.SoDst s' s := fun s' s h =>
    ⟨hT s' h.1 h.2.2.1, h.2.2.1, hT s h.2.1 h.2.2.2.1, h.2.2.2.1, ⟨h.1, h.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.2⟩, h.2.2.2.2.2.1⟩
  have hso' : ∀ s' s, G.SoDst s' s → G.soPaper s' s := fun s' s h =>
    ⟨h.2.2.2.2.1.1, h.2.2.2.2.1.2.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1.2.2.1, h.2.2.2.2.2,
      h.2.2.2.2.1.2.2.2⟩
  constructor
  · rintro ⟨hW, hb, hc⟩
    refine ⟨hW, fun s' hs' s r h1 h2 hm => ?_, fun r r' s s' h0 h1 h2 h3 hm => ?_⟩
    · exact hb s' hs' s h1.2.1 r (hW.rf_some h2).1 ⟨hso s' s h1, h2, hm.valMatches⟩
    · exact hc r h0.1 r' h0.2.1 s' h2.1 s h2.2.1 ⟨h0, h1, hso s' s h2, h3, hm.valMatches⟩
  · rintro ⟨hW, h1, h2⟩
    refine ⟨hW, fun s' hs' s _ r _ ⟨ha, hb, hv⟩ => ?_,
      fun r _ q _ s' _ s _ ⟨ha, hb, hc, hd, hv⟩ => ?_⟩
    · exact h1 s' hs' s r (hso' s' s ha) hb (matches_of_soDst hW ha hb hv)
    · exact h2 r q s s' ha hb (hso' s' s hc) hd (matches_of_soDst hW hc hd hv)

/-! ### lem:terminal (2) -/

/-- A full execution of `P` (def:exec, prelim:313-319): an execution in which no thread has a
next label. No consistency. -/
def FullRaw (P : Program Q) (G : Graph Q) : Prop := P.Exec G ∧ ∀ t, P.step t (G.trace t) = none

/-- The event `r_t` of lem:terminal (2): the next event of `t`. -/
noncomputable def botEv (P : Program Q) (G : Graph Q) (t : Tid) : Ev Q :=
  ⟨t, G.cnt t, (P.step t (G.trace t)).getD .block⟩

/-- The events `r_t` of the stuck threads of the program. -/
noncomputable def botSet (P : Program Q) (G : Graph Q) : Finset (Ev Q) :=
  open Classical in (P.threads.toFinset.filter fun t => Stuck P G t).image (botEv P G)

/-- `G^⊥` (lem:terminal (2)): `G` with `r_t` reading `⊥`, for every stuck thread `t` of the
program. -/
noncomputable def botExt (P : Program Q) (G : Graph Q) : Graph Q where
  events := G.events ∪ botSet P G
  rf := fun e => if e ∈ botSet P G then some .bot else G.rf e
  nd := G.nd

theorem mem_botSet {e : Ev Q} :
    e ∈ botSet P G ↔ ∃ t ∈ P.threads, Stuck P G t ∧ e = botEv P G t := by
  unfold botSet
  simp only [Finset.mem_image, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨t, ⟨ht, hs⟩, rfl⟩
    exact ⟨t, ht, hs, rfl⟩
  · rintro ⟨t, ht, hs, rfl⟩
    exact ⟨t, ⟨ht, hs⟩, rfl⟩

omit [DecidableEq Q] [Membership Val Q] in
theorem botEv_lab {t : Tid} {l : Lab Q} (hl : P.step t (G.trace t) = some l) :
    (botEv P G t).lab = l := by
  simp [botEv, hl]

/-- The facts on `r_t` used below. -/
theorem botSet_props (hG : G.Wf) {e : Ev Q} (he : e ∈ botSet P G) :
    e ∉ G.events ∧ e.idx = G.cnt e.tid ∧ e.IsRecvB ∧ e.tid ∈ P.threads ∧ Stuck P G e.tid ∧
      P.step e.tid (G.trace e.tid) = some e.lab := by
  obtain ⟨t, ht, hs, rfl⟩ := mem_botSet.mp he
  obtain ⟨l, hl, hB, -⟩ := id hs
  have hidx : (botEv P G t).idx = G.cnt (botEv P G t).tid := rfl
  refine ⟨hG.not_mem_of_idx_eq_cnt hidx, hidx, ?_, ht, hs, ?_⟩
  · change (botEv P G t).lab.IsRecvB
    rw [botEv_lab hl]
    exact hB
  · change P.step t (G.trace t) = some (botEv P G t).lab
    rw [botEv_lab hl]
    exact hl

theorem botExt_mem {e : Ev Q} : e ∈ (botExt P G).events ↔ e ∈ G.events ∨ e ∈ botSet P G :=
  Finset.mem_union

theorem botExt_rf_of_not_mem {e : Ev Q} (he : e ∉ botSet P G) : (botExt P G).rf e = G.rf e := by
  simp [botExt, he]

theorem botExt_rf_of_mem {e : Ev Q} (he : e ∈ botSet P G) : (botExt P G).rf e = some .bot := by
  simp [botExt, he]

/-- The values returned before the index `G.cnt t` agree. -/
theorem botExt_retAt (hG : G.Wf) {t : Tid} {j : ℕ} (hj : j < G.cnt t) :
    (botExt P G).retAt t j = G.retAt t j := by
  refine (retAt_congr (fun x h1 h2 => ?_) (fun x hx h1 h2 => ?_)).symm
  · rw [botExt_mem]
    refine ⟨Or.inl, fun h => h.resolve_right fun hb => ?_⟩
    have := (botSet_props hG hb).2.1
    rw [h1] at this
    omega
  · have hb : x ∉ botSet P G := fun hb => (botSet_props hG hb).1 hx
    exact ⟨(botExt_rf_of_not_mem hb).symm, rfl⟩

theorem botExt_traceBefore (hG : G.Wf) {t : Tid} {i : ℕ} (hi : i ≤ G.cnt t) :
    (botExt P G).traceBefore t i = G.traceBefore t i :=
  traceBefore_congr fun j hj => botExt_retAt hG (by omega)

open Classical in
/-- The events of thread `t` in `G^⊥`. -/
theorem botExt_cnt (hG : G.Wf) (t : Tid) :
    (botExt P G).cnt t = G.cnt t + if t ∈ P.threads ∧ Stuck P G t then 1 else 0 := by
  classical
  have hdisj : Disjoint (G.events.filter fun e => e.tid = t)
      ((botSet P G).filter fun e => e.tid = t) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    exact (botSet_props hG (Finset.mem_filter.mp h2).1).1 (Finset.mem_filter.mp h1).1
  have hB : ((botSet P G).filter fun e => e.tid = t) =
      if t ∈ P.threads ∧ Stuck P G t then {botEv P G t} else ∅ := by
    ext e
    rw [Finset.mem_filter, mem_botSet]
    split_ifs with h
    · rw [Finset.mem_singleton]
      constructor
      · rintro ⟨⟨t', -, -, rfl⟩, rfl⟩
        rfl
      · rintro rfl
        exact ⟨⟨t, h.1, h.2, rfl⟩, rfl⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      rintro ⟨t', ht', hs', rfl⟩ rfl
      exact h ⟨ht', hs'⟩
  unfold cnt
  change ((G.events ∪ botSet P G).filter fun e => e.tid = t).card = _
  rw [Finset.filter_union, Finset.card_union_of_disjoint hdisj, hB]
  split_ifs <;> simp

/-- The trace of a stuck thread in `G^⊥`: its trace in `G`, then `⊥`. -/
theorem botExt_trace_stuck (hG : G.Wf) {t : Tid} (ht : t ∈ P.threads) (hs : Stuck P G t) :
    (botExt P G).trace t = G.trace t ++ [none] := by
  have hb : botEv P G t ∈ botSet P G := mem_botSet.mpr ⟨t, ht, hs, rfl⟩
  have hlast : (botExt P G).retAt t (G.cnt t) = none := by
    have hf : (botExt P G).events.filter (fun e => e.tid = t ∧ e.idx = G.cnt t) =
        {botEv P G t} := by
      ext e
      rw [Finset.mem_filter, botExt_mem, Finset.mem_singleton]
      constructor
      · rintro ⟨h | h, h1, h2⟩
        · have := hG.idx_lt_cnt h
          rw [h1, h2] at this
          omega
        · obtain ⟨t', -, -, rfl⟩ := mem_botSet.mp h
          cases h1
          rfl
      · rintro rfl
        exact ⟨Or.inr hb, rfl, rfl⟩
    unfold retAt
    rw [hf, Finset.sup_singleton]
    simp [ret, botExt_rf_of_mem hb, encR, decR]
  unfold trace
  rw [botExt_cnt hG]
  split_ifs with h
  swap
  · exact absurd ⟨ht, hs⟩ h
  unfold traceBefore
  rw [List.range_succ, List.map_append]
  change (botExt P G).traceBefore t (G.cnt t) ++ _ = _
  rw [botExt_traceBefore hG le_rfl]
  simp [hlast, traceBefore]

/-- The trace of any other thread in `G^⊥` is its trace in `G`. -/
theorem botExt_trace_of_not (hG : G.Wf) {t : Tid} (h : ¬ (t ∈ P.threads ∧ Stuck P G t)) :
    (botExt P G).trace t = G.trace t := by
  unfold trace
  rw [botExt_cnt hG]
  split_ifs
  rw [Nat.add_zero, botExt_traceBefore hG le_rfl]

/-- lem:terminal (2): `G^⊥` is an execution graph (def:graph: well-formed except that blocking
receives may read `⊥`). -/
theorem botExt_graph (hT : Term Model.asyn P G) : (botExt P G).WfExceptBot := by
  have hG : G.Wf := Model.asyn.wf _ (mreach_iff.mp hT.1).2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he e' he' ht hi
    rw [botExt_mem] at he he'
    rcases he with he | he <;> rcases he' with he' | he'
    · exact hG.idx_inj e he e' he' ht hi
    · have h1 := hG.idx_lt_cnt he
      have h2 := (botSet_props hG he').2.1
      rw [ht, hi] at h1
      omega
    · have h1 := hG.idx_lt_cnt he'
      have h2 := (botSet_props hG he).2.1
      rw [← ht, ← hi] at h1
      omega
    · obtain ⟨t, -, -, rfl⟩ := mem_botSet.mp he
      obtain ⟨t', -, -, rfl⟩ := mem_botSet.mp he'
      cases ht
      rfl
  · intro e he i hi
    rw [botExt_mem] at he
    rcases he with he | he
    · obtain ⟨e', he', h1, h2⟩ := hG.idx_contig e he i hi
      exact ⟨e', botExt_mem.mpr (Or.inl he'), h1, h2⟩
    · rw [(botSet_props hG he).2.1] at hi
      obtain ⟨e', he', h1, h2⟩ := (hG.exists_idx_iff _ _).mpr hi
      exact ⟨e', botExt_mem.mpr (Or.inl he'), h1, h2⟩
  · intro e
    by_cases hb : e ∈ botSet P G
    · rw [botExt_rf_of_mem hb]
      simp only [Option.isSome_some, true_iff]
      exact ⟨botExt_mem.mpr (Or.inr hb), Lab.IsRecvB.isRecv (botSet_props hG hb).2.2.1⟩
    · rw [botExt_rf_of_not_mem hb, hG.rf_isSome, botExt_mem]
      simp [hb]
  · intro r s h
    by_cases hb : r ∈ botSet P G
    · rw [botExt_rf_of_mem hb] at h
      cases h
    · rw [botExt_rf_of_not_mem hb] at h
      exact botExt_mem.mpr (Or.inl (hG.rf_mem _ _ h))
  · intro r r' s h h'
    by_cases hb : r ∈ botSet P G
    · rw [botExt_rf_of_mem hb] at h
      cases h
    · by_cases hb' : r' ∈ botSet P G
      · rw [botExt_rf_of_mem hb'] at h'
        cases h'
      · rw [botExt_rf_of_not_mem hb] at h
        rw [botExt_rf_of_not_mem hb'] at h'
        exact hG.rf_once _ _ _ h h'
  · intro r s h
    by_cases hb : r ∈ botSet P G
    · rw [botExt_rf_of_mem hb] at h
      cases h
    · rw [botExt_rf_of_not_mem hb] at h
      exact hG.rf_match _ _ h
  · intro e
    change (G.nd e).isSome ↔ _
    rw [hG.nd_isSome, botExt_mem]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inl h1, h2⟩
    · rintro ⟨h1 | h1, h2⟩
      · exact ⟨h1, h2⟩
      · exact absurd h2 (Lab.IsRecv.not_isND (Lab.IsRecvB.isRecv (botSet_props hG h1).2.2.1))
  · exact hG.nd_mem
  · -- the events `r_t` are sinks; every other step is a step of `G`
    have hstep : ∀ a b, (botExt P G).porfStep a b → a ∉ botSet P G ∧
        (b ∈ botSet P G ∨ G.porfStep a b) := by
      intro a b h
      rcases h with ⟨ha, hb, ht, hi⟩ | ⟨hb, hrf⟩
      · rw [botExt_mem] at ha hb
        have haB : a ∉ botSet P G := by
          intro haB
          have h1 := (botSet_props hG haB).2.1
          rcases hb with hb | hb
          · have := hG.idx_lt_cnt hb
            rw [← ht] at this
            omega
          · have := (botSet_props hG hb).2.1
            rw [← ht] at this
            omega
        refine ⟨haB, ?_⟩
        rcases hb with hb | hb
        · exact Or.inr (Or.inl ⟨ha.resolve_right haB, hb, ht, hi⟩)
        · exact Or.inl hb
      · have hbB : b ∉ botSet P G := fun h => by
          rw [botExt_rf_of_mem h] at hrf
          cases hrf
        rw [botExt_rf_of_not_mem hbB] at hrf
        have haG := hG.rf_mem _ _ hrf
        refine ⟨fun h => (botSet_props hG h).1 haG, Or.inr (Or.inr ⟨?_, hrf⟩)⟩
        exact (botExt_mem.mp hb).resolve_right hbB
    have hpath : ∀ a b, (botExt P G).porf a b → a ∉ botSet P G ∧
        (b ∈ botSet P G ∨ G.porf a b) := by
      intro a b h
      induction h with
      | single h =>
        obtain ⟨h1, h2⟩ := hstep _ _ h
        exact ⟨h1, h2.imp_right TransGen.single⟩
      | tail _ h ih =>
        obtain ⟨h1, h2⟩ := hstep _ _ h
        refine ⟨ih.1, ?_⟩
        rcases h2 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr ((ih.2.resolve_left h1).tail h2)
    intro a h
    obtain ⟨h1, h2⟩ := hpath a a h
    exact hG.porf_irrefl a (h2.resolve_left h1)

/-- lem:terminal (2): `G^⊥` is a full execution of the program. -/
theorem botExt_full (hT : Term Model.asyn P G) : FullRaw P (botExt P G) := by
  have hE := mreach_iff.mp hT.1
  have hG : G.Wf := Model.asyn.wf _ hE.2
  have hst := (term_iff_stuck hE).mp hT
  refine ⟨fun x hx => ?_, fun t => ?_⟩
  · rcases botExt_mem.mp hx with hx | hx
    · rw [botExt_traceBefore hG (hG.idx_lt_cnt hx).le]
      exact hE.1 x hx
    · obtain ⟨-, hidx, -, -, -, hl⟩ := botSet_props hG hx
      rw [hidx, botExt_traceBefore hG le_rfl]
      exact hl
  · by_cases h : t ∈ P.threads ∧ Stuck P G t
    · rw [botExt_trace_stuck hG h.1 h.2]
      obtain ⟨l, hl, hB, -⟩ := h.2
      refine P.stop t _ l hl ?_
      cases l <;> simp_all [Lab.IsRecvB, Lab.Stops]
    · rw [botExt_trace_of_not hG h]
      by_cases ht : t ∈ P.threads
      · have hs : ¬ Stuck P G t := fun hs => h ⟨ht, hs⟩
        by_contra hne
        exact hs (hst t ht (Option.isSome_iff_ne_none.mpr hne))
      · have h0 : G.cnt t = 0 := by
          unfold cnt
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro x hx hxt
          exact ht (hxt ▸ hG.tid_mem_threads hE.1 hx)
        unfold trace traceBefore
        rw [h0]
        exact P.step_none t ht

/-- lem:terminal (2): `G = G^⊥|G.E`. -/
theorem botExt_restrict (hT : Term Model.asyn P G) : (botExt P G).restrict G.events = G := by
  have hG : G.Wf := Model.asyn.wf _ (mreach_iff.mp hT.1).2
  apply Graph.ext
  · ext e
    rw [restrict_events, Finset.mem_inter, botExt_mem]
    exact ⟨fun h => h.2, fun h => ⟨Or.inl h, h⟩⟩
  · funext e
    rw [restrict_rf]
    by_cases he : e ∈ G.events
    · have hb : e ∉ botSet P G := fun hb => (botSet_props hG hb).1 he
      simp only [he, ↓reduceIte, botExt_rf_of_not_mem hb]
    · simp only [he, ↓reduceIte, hG.rf_none (Or.inl he)]
  · funext e
    rw [restrict_nd]
    by_cases he : e ∈ G.events
    · simp only [he, ↓reduceIte]
      rfl
    · simp only [he, ↓reduceIte, hG.nd_none (Or.inl he)]

/-- lem:terminal (2): `G` extended by the receive `r_t` of a stuck thread reading `⊥` is not
`asyn`-consistent. -/
theorem botExt_incons (hT : Term Model.asyn P G) {t : Tid} (ht : t ∈ P.threads)
    (hs : Stuck P G t) :
    ¬ Model.asyn.cons ((botExt P G).restrict (insert (botEv P G t) G.events)) := by
  have hG : G.Wf := Model.asyn.wf _ (mreach_iff.mp hT.1).2
  have hb : botEv P G t ∈ botSet P G := mem_botSet.mpr ⟨t, ht, hs, rfl⟩
  intro hc
  have hW := Model.asyn.wf _ hc
  have hrf : ((botExt P G).restrict (insert (botEv P G t) G.events)).rf (botEv P G t) =
      some .bot := by
    simp only [restrict_rf, Finset.mem_insert_self, ↓reduceIte, botExt_rf_of_mem hb]
  exact Lab.not_isRecvB_of_isRecvNB (hW.rf_bot _ hrf) (botSet_props hG hb).2.2.1

end Ind

end Must
