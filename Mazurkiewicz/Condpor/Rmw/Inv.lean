import Mazurkiewicz.Condpor.Rmw.Sym
import Mazurkiewicz.Condpor.Prev

/-!
# Read-modify-write accesses: the invariants (P7) and (P8)

Proposition A.22 of TruSt, clauses (P7) and (P8), for every model:

* (P7) a pending exclusive read of a reached configuration is `me`;
* (P8) and then the next event is its mate.

Both are proved together by induction over the run, from the accepted
invariant (`Inv`, `LastStep`). At a revisit of `a` by `w` the point is that a
kept read other than `a` does not lose its successor in its thread
(`RvHyp.succ_not_deleted`); the argument uses (P2) of the configuration before
the step and Lemma A.20 (D3), and does not use that the read is exclusive.
-/

namespace Condpor

open Program

/-- The source of a read is not a read. -/
theorem Graph.Wf.not_isRead_of_rf {G : Graph} (hG : G.Wf) {e q : TEv}
    (h : G.rf e = some (.th q)) : ¬ q.IsRead := by
  intro hq
  have he := (hG.rf_source_mem h).1
  have her : e.IsRead := by
    by_contra hn
    rw [hG.rf_none e (Or.inr hn)] at h
    cases h
  obtain ⟨w, hw, hwt⟩ := hG.rf_read e he _ her.exists_act
  rw [h] at hw
  cases hw
  obtain ⟨-, v, hv⟩ := hwt
  simp [TEv.IsRead, Act.IsRead, hv] at hq

/-- A causality path out of a read goes through its successor in its thread. -/
theorem Graph.porf_of_read_succ {G : Graph} (hG : G.Wf) {q m : TEv} (hq : q.IsRead)
    (hm : m ∈ G.events) (ht : m.tid = q.tid) (hi : m.idx = q.idx + 1) {b : Ev}
    (h : G.porf (.th q) b) : b = .th m ∨ G.porf (.th m) b := by
  obtain ⟨z, hz, hzb⟩ := Relation.TransGen.head'_iff.mp h
  rcases hz with hpo | ⟨e, -, -, hrf⟩
  · cases z with
    | init => exact absurd hpo (by simp [Graph.po])
    | th z' =>
      obtain ⟨-, hz'm, htz, hiz⟩ := hpo
      by_cases hzm : z' = m
      · subst hzm
        rcases Relation.reflTransGen_iff_eq_or_transGen.mp hzb with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
      · have hne : m.idx ≠ z'.idx := fun h' =>
          hzm (hG.idx_inj z' hz'm m hm (htz.symm.trans ht.symm) h'.symm)
        have hpo' : G.po (.th m) (.th z') := ⟨hm, hz'm, ht.trans htz, by omega⟩
        exact Or.inr (Relation.TransGen.head' (Or.inl hpo') hzb)
  · exact absurd hq (hG.not_isRead_of_rf hrf)

variable {P : XProgram} {M : Model} {S : Solver} {τ : TieBreak S}

/-- At a revisit of `a` by `w`, a kept read other than `a` keeps its successor
in its thread. -/
theorem RvHyp.succ_not_deleted {c : Config} {a w : TEv} {wp : Ev}
    (H : RvHyp P.toProgram τ c a w wp) (I : Inv P.toProgram c) {q m : TEv}
    (hqk : q ∈ c.keep a w) (hqa : q ≠ a) (hq : q.IsRead) (hm : m ∈ c.order)
    (ht : m.tid = q.tid) (hi : m.idx = q.idx + 1) : ¬ c.Deleted a w m := by
  intro hd
  obtain ⟨hqo, hqnd⟩ := (Config.mem_keep_iff c a w q).mp hqk
  have hW := H.hc.1
  have hqm : q ∈ c.abs.events := List.mem_toFinset.mpr hqo
  have hmm : m ∈ c.abs.events := List.mem_toFinset.mpr hm
  have haM : a ∈ c.abs.events := List.mem_toFinset.mpr H.hr
  -- `q` is not causally before `w`: its successor would be
  have hplusWf : (c.plus w).Wf := hW.addWrite H.hidx H.hw trivial
  have hnp : ¬ (c.plus w).porf (.th q) (.th w) := by
    intro hp
    rcases Graph.porf_of_read_succ hplusWf hq (Finset.mem_insert_of_mem hmm) ht hi hp with h | h
    · refine H.fresh ?_
      rw [Ev.th.inj h]
      exact hm
    · exact hd.2.2 h
  -- so `q` was added before `a`
  have hlt : c.lt q a := by
    rcases List.Before.total hqo H.hr hqa with h | h
    · exact absurd ⟨hqo, h, hnp⟩ hqnd
    · exact h
  -- `a <next q`
  have hnx : nextLt a q := by
    rcases Program.nextLt_total hqa with h | h
    · exfalso
      have hma : nextLt m a := by
        rcases h with h1 | ⟨h1, h2⟩ | ⟨h1, h2, -⟩
        · refine Or.inl ?_
          rw [ht]
          exact h1
        · have hne : m ≠ a := fun h' => List.Before.irrefl _ _ (h' ▸ hd.2.1)
          have hne' : m.idx ≠ a.idx := fun h' => hne (hW.idx_inj m hmm a haM (ht.trans h1) h')
          have hlt' : c.lt m a := H.hpo m hm a H.hr (ht.trans h1) (by omega)
          exact absurd hd.2.1 (List.Before.asymm hlt')
        · exact absurd (hW.idx_inj q hqm a haM h1 h2) hqa
      obtain ⟨s, p, h1, h2, -⟩ := I.p2 m hm a H.hr hma hd.2.1
      exact A20_D3 H.hc H.hpo H.hr H.hnp H.hmax (Or.inr rfl) h1 h2
    · exact h
  obtain ⟨s, p, h1, h2, -⟩ := I.p2 a H.hr q hqo hnx hlt
  refine A20_D3 H.hc H.hpo H.hr H.hnp H.hmax (x := m) (Or.inl hd) ?_ h2
  rcases h1 with h1 | h1
  · exfalso
    have hrf : c.abs.rf p = some (.th s) := h2.1
    exact hW.not_isRead_of_rf hrf (h1 ▸ hq)
  · rcases Graph.porf_of_read_succ hW hq hmm ht hi h1 with h | h
    · exact Or.inl (Ev.th.inj h).symm
    · exact Or.inr h

/-- For well-formed graphs that both contain the read `q`: a prospective pair
of `G'` is one of `G` if the thread of `q` has the same trace in both and the
write is available in `G`. -/
theorem XProgram.Mate.of_trace_eq {G G' : Graph} (hG : G.Wf) (hG' : G'.Wf) {q m : TEv}
    (hm : P.Mate G' q m) (hq : q ∈ G.events) (hav : m ∈ P.toProgram.avail G)
    (htr : G'.trace q.tid = G.trace q.tid) : P.Mate G q m := by
  obtain ⟨hq', hqR, hqx, -, hmt, hmi, hmW, hmx⟩ := hm
  refine ⟨hq, hqR, ?_, hav, hmt, hmi, hmW, ?_⟩
  · unfold XProgram.IsEx at hqx ⊢
    rw [G'.traceBefore_eq_take _ (Nat.le_of_lt (hG'.idx_lt_cnt hq')), htr] at hqx
    rw [G.traceBefore_eq_take _ (Nat.le_of_lt (hG.idx_lt_cnt hq))]
    exact hqx
  · rw [hmt] at hmx ⊢
    rw [← htr]
    exact hmx

/-- A step that is not a revisit keeps the traces of the other threads. -/
theorem StepL.nr_trace_ne {Q : Program} {c c' : Config} {e : TEv} (hc : c.Wf)
    (h : StepL Q M τ c e .nr c') {t : Tid} (ht : t ≠ e.tid) :
    c'.abs.trace t = c.abs.trace t := by
  obtain ⟨-, hnext, hcase⟩ := h.nr_inv
  have hidx := idx_eq_of_mem_avail hnext.1
  rcases hcase with ⟨x, w, hact, hw, rfl⟩ | ⟨wp, hw, hwp, rfl⟩ | ⟨b, hcs, rfl⟩ | ⟨hl, hnc, rfl⟩
  · rw [Config.addRead_abs, Graph.trace_addRead hc.1 hidx hact hw]
    simp [ht]
  · rw [Config.addWrite_abs, Graph.trace_addWrite hc.1 hidx hw hwp]
    simp [ht]
  · obtain ⟨φ, hφ⟩ := hcs.exists_act
    have hl : e.IsLocal := by simp [TEv.IsLocal, hφ, Act.IsLocal]
    rw [Config.addLoc_abs, Graph.trace_addLoc hc.1 hidx hl (by simp [hcs])]
    simp [ht]
  · rw [Config.addLoc_abs, Graph.trace_addLoc hc.1 hidx hl (by simp [hnc])]
    simp [ht]

/-- The ordering lemma of the plan (2.1), in place of the adjacency of the two
events of a pair in `<next` (Def. A.7): an available event other than the mate
that is `<next`-after the read is `<next`-after the mate (it is in a later
thread). -/
theorem XProgram.Mate.next_lt {G : Graph} {q m y : TEv} (hm : P.Mate G q m)
    (hy : y ∈ P.toProgram.avail G) (hne : y ≠ m) (h : nextLt q y) : nextLt m y := by
  obtain ⟨-, -, -, hma, hmt, -, -, -⟩ := hm
  have htne : y.tid ≠ m.tid := fun h' => hne (avail_tid_inj hy hma h')
  rcases h with h1 | ⟨h1, -⟩ | ⟨h1, -, -⟩
  · refine Or.inl ?_
    rw [hmt]
    exact h1
  · exact absurd (h1.symm.trans hmt.symm) htne
  · exact absurd (h1.symm.trans hmt.symm) htne

/-- `q` is pending: it is an exclusive read, the last event of its thread, and
the thread continues with an exclusive write. All conditions are on the trace
of the thread, so the statement applies as it is to a graph in which the
source of `q` was changed (`Graph.setRF`): there the read may be pending or
not, according to the value it now returns. -/
theorem XProgram.pending_iff {G : Graph} {q : TEv} :
    P.Pending G q ↔ q ∈ G.events ∧ q.IsRead ∧ P.IsEx G q ∧ q.tid ∈ P.threads ∧
      G.cnt q.tid = q.idx + 1 ∧ P.ex q.tid (G.trace q.tid) = true ∧
      ∃ a, P.step q.tid (G.trace q.tid) = some a ∧ a.IsWrite := by
  constructor
  · rintro ⟨m, hq, hqR, hqx, hma, hmt, hmi, hmW, hmx⟩
    obtain ⟨h1, h2, h3⟩ := mem_avail_iff.mp hma
    rw [hmt] at h1 h2 h3 hmx
    exact ⟨hq, hqR, hqx, h1, by omega, hmx, m.act, h3, hmW⟩
  · rintro ⟨hq, hqR, hqx, h1, h2, h3, a, h4, h5⟩
    exact ⟨⟨q.tid, q.idx + 1, a⟩, hq, hqR, hqx,
      mem_avail_iff.mpr ⟨h1, h2.symm, h4⟩, rfl, rfl, h5, h3⟩

/-- Changing the source of `r` does not change the next events of the other
threads. -/
theorem Program.nextOf_setRF_of_ne (Q : Program) (G : Graph) {r : TEv} {s : Ev} {t : Tid}
    (ht : t ≠ r.tid) : Q.nextOf (G.setRF r s) t = Q.nextOf G t := by
  unfold Program.nextOf
  rw [Graph.trace_setRF_of_ne G ht]
  rfl

/-- If `me` is a pending read, its mate is the next event. -/
theorem LastStep.isNext_mate {c : Config} {e : TEv} {k : Kind}
    (L : LastStep P.toProgram c e k) (hc : c.Wf) {q m : TEv} (hq : q = k.me e)
    (hm : P.Mate c.abs q m) : P.toProgram.IsNext c.abs m := by
  refine ⟨hm.2.2.2.1, fun y hy hne => ?_⟩
  have h := L.me_lt_avail hc hy
  rw [← hq] at h
  exact hm.next_lt hy hne h

/-- Proposition A.22, (P7) and (P8): in a reached configuration, the read of a
prospective pair is `me`, and its write is the next event. -/
theorem Rmw.pending {c : Config} (h : Reach P.toProgram M τ c) :
    ∀ {q m : TEv}, P.Mate c.abs q m →
      c.abs.IsMe (.th q) ∧ P.toProgram.IsNext c.abs m := by
  unfold Reach at h
  induction h with
  | refl =>
    intro q m hm
    have := hm.1
    rw [Config.init_abs] at this
    simp [Graph.init] at this
  | @tail b c' hb hs ih =>
    intro q m hm
    have hbR : Reach P.toProgram M τ b := hb
    have hcR : Reach P.toProgram M τ c' := hb.tail hs
    obtain ⟨hw, hpo, -, -⟩ := hbR.sound
    obtain ⟨hw', -, -, -⟩ := hcR.sound
    have I := hbR.inv
    obtain ⟨e, k, hs⟩ := hs
    suffices hqe : q = k.me e ∧ LastStep P.toProgram c' e k from
      ⟨hqe.1 ▸ hqe.2.me, hqe.2.isNext_mate hw' hqe.1 hm⟩
    have hm' := hm
    obtain ⟨hqG, hqR, -, hma, hmt, hmi, -, -⟩ := hm
    cases k with
    | nr =>
      obtain ⟨-, L'⟩ := inv_nr hw I hs
      refine ⟨?_, L'⟩
      by_contra hqe
      have hqe' : q ≠ e := hqe
      have N := hs.nrFacts hw
      have hqo : q ∈ b.order := by
        have : q ∈ c'.order := List.mem_toFinset.mp hqG
        rw [N.order] at this
        exact (List.mem_cons.mp this).resolve_left hqe'
      have heG : e ∈ c'.abs.events :=
        List.mem_toFinset.mpr (by rw [N.order]; exact List.mem_cons_self)
      have hte : q.tid ≠ e.tid := by
        intro hte
        have h1 := N.avail_same m hma (hmt.trans hte)
        exact hqe' (hw'.1.idx_inj q hqG e heG hte (by omega))
      have hmb : m ∈ P.toProgram.avail b.abs :=
        N.avail_other m hma (fun h' => hte (hmt.symm.trans h'))
      have hMate := XProgram.Mate.of_trace_eq hw.1 hw'.1 hm' (List.mem_toFinset.mpr hqo) hmb
        (hs.nr_trace_ne hw hte)
      have hme : m = e := Program.isNext_unique (ih hMate).2 hs.nr_inv.2.1
      exact hte (hmt.symm.trans (congrArg TEv.tid hme))
    | rv a =>
      obtain ⟨wp, rfl, H⟩ := hs.rvHyp hw hpo
      obtain ⟨-, L', -, -⟩ := inv_rv I H
      refine ⟨?_, L'⟩
      by_contra hqa
      have hqa' : q ≠ a := hqa
      have hqe : q ≠ e := by
        intro h'
        rw [h'] at hqR
        have hW := H.hw
        cases hact : e.act <;>
          simp [TEv.IsRead, TEv.IsWrite, hact, Act.IsRead, Act.IsWrite] at hqR hW
      have hqk : q ∈ b.keep a e := (H.events'.mp hqG).resolve_left hqe
      obtain ⟨hqo, hqnd⟩ := (Config.mem_keep_iff b a e q).mp hqk
      have heG : e ∈ (b.revisit a e wp).abs.events := H.events'.mpr (Or.inl rfl)
      have haG : a ∈ (b.revisit a e wp).abs.events := H.events'.mpr (Or.inr H.r_keep)
      have hD2 : ∀ {x : TEv}, (b.Deleted a e x ∨ x = a) → ¬ b.abs.porf (.th x) (.th q) :=
        fun hx => A20_D2 H.hc H.hpo H.hr H.hnp H.hmax hx hqo hqnd
      rcases H.avail_cases hma with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨z, hz, hzt, hzi⟩
      · -- the mate was available before the step: the pair is a pair of `b`
        have hmne : m ≠ e := fun h' => Program.not_mem_of_mem_avail hw'.1 hma (h' ▸ heG)
        have htw : q.tid ≠ e.tid := fun h' => hmne (avail_tid_inj h H.hav (hmt.trans h'))
        have hmcnt := idx_eq_of_mem_avail hma
        have hmcntb := idx_eq_of_mem_avail h
        have hta : q.tid ≠ a.tid := by
          intro h'
          have h3 := hw'.1.idx_lt_cnt haG
          rw [← h', ← hmt, ← hmcnt, hmi] at h3
          have hne : a.idx ≠ q.idx := fun h4 => hqa' (hw'.1.idx_inj q hqG a haG h' h4.symm)
          have hpo' : b.abs.po (.th a) (.th q) :=
            ⟨List.mem_toFinset.mpr H.hr, List.mem_toFinset.mpr hqo, h'.symm, by omega⟩
          exact hD2 (Or.inr rfl) (Relation.TransGen.single (Or.inl hpo'))
        have hall : ∀ z ∈ b.abs.events, z.tid = q.tid → z ∈ b.keep a e := by
          intro z hz hzt
          by_contra hzk
          have hzd : b.Deleted a e z := by
            by_contra hnd
            exact hzk ((Config.mem_keep_iff b a e z).mpr ⟨List.mem_toFinset.mp hz, hnd⟩)
          have h3 := hw.1.idx_lt_cnt hz
          rw [hzt, ← hmt, ← hmcntb, hmi] at h3
          have hzq : z ≠ q := fun h4 => hzk (h4 ▸ hqk)
          have hne : z.idx ≠ q.idx := fun h4 =>
            hzq (hw.1.idx_inj z hz q (List.mem_toFinset.mpr hqo) hzt h4)
          have hpo' : b.abs.po (.th z) (.th q) :=
            ⟨hz, List.mem_toFinset.mpr hqo, hzt, by omega⟩
          exact hD2 (Or.inl hzd) (Relation.TransGen.single (Or.inl hpo'))
        have hR := Config.restrict_keep_wf H.hc H.hpo H.hmaxD
        have hidx' : e.idx = (b.abs.restrict (b.keep a e)).cnt e.tid := by
          rw [Config.cnt_restrict_keep (r := a) H.hc H.hidx]
          exact H.hidx
        have htr : (b.revisit a e wp).abs.trace q.tid = b.abs.trace q.tid := by
          rw [Config.revisit_abs, Graph.trace_setRF_of_ne _ hta,
            Graph.trace_addWrite hR hidx' H.hw H.hwp]
          simp only [htw, ite_false]
          exact Graph.trace_restrict_of_thread hw.1 hall (fun z hz hzt s hs' =>
            Config.keep_sources H.hc H.hmaxD (Finset.mem_inter.mpr ⟨hz, hall z hz hzt⟩) hs')
        have hMate := XProgram.Mate.of_trace_eq hw.1 hw'.1 hm' (List.mem_toFinset.mpr hqo) h htr
        exact hmne (Program.isNext_unique (ih hMate).2 H.hnext)
      · exact hqe (hw'.1.idx_inj q hqG e heG (hmt.symm.trans h1) (by omega))
      · exact hqa' (hw'.1.idx_inj q hqG a haG (hmt.symm.trans h1) (by omega))
      · exact H.succ_not_deleted I hqk hqa' hqR hz.1 (hzt.trans hmt) (hzi.trans hmi) hz

end Condpor
