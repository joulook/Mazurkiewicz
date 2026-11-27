import Mazurkiewicz.Condpor.Rmw.LifecycleGate2Fin

/-!
# Gate clause 2, part 3g: the end of the replay (LC2-b, continuation 3)

`FCtx P n c l s g`: a terminal-valid `c`, a run list `l`, a state `s` with `SInv` whose builder
list is `l`.

* `FCtx.thread`: per listed thread, no occurrence is enabled, and the events of the thread in
  `c` are the builder's ones and its synthetic ones `synE` (none, or a read and a `block`
  forming a final wait, the last event of the thread). By status: new: the start-read of `c`
  returned `0` (it is followed by `block`), so the thread is not started; running: the next
  compiled action is a read followed by `block` in `c`, which only a `lock` with value `1` or
  a `join` with value `1` can give; the read is final, so the lock is held by another thread,
  resp. the target is started and not ended; ended, erred, stopped: no compiled step left.
* **`g2Final : G2Final`**, then **`g2Replay : G2Replay`** and **`gate2 : Gate2`**.
-/

namespace Condpor

namespace Life

namespace Sem

open _root_.List Targets

variable {P : LProg} {n : ℕ}

theorem TState.ready_act (st : Tid → Loc) (me : Tid) (ops : List TOp) (h : Loc → ℕ) :
    (⟨ops, h, .ready⟩ : TState).act st me ≠ none ∧
      (⟨ops, h, .ready⟩ : TState).act st me ≠ some .block := by
  cases ops with
  | nil => simp [TState.act]
  | cons c tl => cases c <;> simp only [TState.act] <;> (try split_ifs) <;> simp

/-- The context at the end of the replay. -/
structure FCtx (P : LProg) (n : ℕ) (c : Config) (l : List TEv) (s : MState) (g : GB) : Prop where
  hT : TermValid P n c
  hl : RunList P (lifeSys P n) c.abs l
  hI : SInv P n s g
  hgl : g.L = l

namespace FCtx

variable {c : Config} {l : List TEv} {s : MState} {g : GB}

theorem hF (h : FCtx P n c l s g) : Frag P := frag_of_fragB h.hT.1
theorem hn (h : FCtx P n c l s g) : adequateB P n = true := h.hT.2.1
theorem hc (h : FCtx P n c l s g) : c.Wf := h.hT.2.2.1
theorem hG (h : FCtx P n c l s g) : c.abs.Wf := h.hT.2.2.1.1
theorem hE (h : FCtx P n c l s g) : (lifeSys P n).toProgram.Exec c.abs := h.hT.2.2.2.1
theorem hfu (h : FCtx P n c l s g) : (lifeSys P n).toProgram.Full c.abs := h.hT.2.2.2.2.2.1

theorem hpre (h : FCtx P n c l s g) : l = g.L ++ [] := by rw [h.hgl, append_nil]

theorem trEq (h : FCtx P n c l s g) (t : Tid) : tr P g t = c.abs.traceBefore t (g.cnt t) :=
  tr_eq h.hI.ok h.hG h.hl.sub h.hpre h.hE.1 t

theorem memL (h : FCtx P n c l s g) (q : TEv) :
    q ∈ g.L ↔ q ∈ c.abs.events ∧ ¬ IsTail P c.abs q := by
  rw [h.hgl]; exact h.hl.mem q

theorem inL_of_lt (h : FCtx P n c l s g) {q : TEv} (hq : q ∈ c.abs.events)
    (hi : q.idx < g.cnt q.tid) : q ∈ g.L := by
  obtain ⟨q', hq', h1, h2⟩ := h.hI.ok.present q.tid q.idx hi
  have := h.hG.idx_inj q' ((h.memL q').mp hq').1 q hq h1 h2
  rwa [this] at hq'

theorem cnt_le (h : FCtx P n c l s g) (t : Tid) : g.cnt t ≤ c.abs.cnt t := by
  by_contra hlt
  obtain ⟨q, hq, h1, h2⟩ := h.hI.ok.present t (c.abs.cnt t) (by omega)
  have := (h.hG.exists_idx_iff t (c.abs.cnt t)).mp ⟨q, ((h.memL q).mp hq).1, h1, h2⟩
  omega

/-- A compiled step after the builder's values: the graph has the event at the next index. -/
theorem at_cnt (h : FCtx P n c l s g) {t : Tid} {a : Act}
    (hs : (lifeSys P n).toProgram.step t (tr P g t) = some a) :
    ∃ q ∈ c.abs.events, q.tid = t ∧ q.idx = g.cnt t ∧ q.act = a := by
  by_cases hlt : g.cnt t < c.abs.cnt t
  · obtain ⟨q, hq, h1, h2⟩ := (h.hG.exists_idx_iff t (g.cnt t)).mpr hlt
    have := h.hE.2 q hq
    rw [h1, h2, ← h.trEq, hs] at this
    exact ⟨q, hq, h1, h2, (Option.some.inj this).symm⟩
  · have heq : c.abs.cnt t = g.cnt t := by have := h.cnt_le t; omega
    have hfull := (Program.full_iff.mp h.hfu) t (step_some hs).2.2.2
    unfold Graph.trace at hfull
    rw [heq, ← h.trEq, hs] at hfull
    cases hfull

/-- No compiled step after the builder's values: the thread has no other event. -/
theorem no_at_cnt (h : FCtx P n c l s g) {t : Tid}
    (hs : (lifeSys P n).toProgram.step t (tr P g t) = none) :
    ∀ q ∈ c.abs.events, q.tid = t → q ∈ g.L := by
  intro q hq hqt
  by_contra hn'
  have hge : g.cnt t ≤ q.idx := by
    by_contra hlt; exact hn' (h.inL_of_lt hq (by rw [hqt]; omega))
  obtain ⟨q', hq', h1, h2⟩ : ∃ q' ∈ c.abs.events, q'.tid = t ∧ q'.idx = g.cnt t := by
    rcases Nat.lt_or_ge (g.cnt t) q.idx with hl | hl
    · obtain ⟨q', hq', h1, h2⟩ := h.hG.idx_contig q hq (g.cnt t) hl
      exact ⟨q', hq', h1.trans hqt, h2⟩
    · exact ⟨q, hq, hqt, by omega⟩
  have := h.hE.2 q' hq'
  rw [h1, h2, ← h.trEq, hs] at this
  cases this

/-- The event at the next index is the read of a final wait. -/
theorem tail_at (h : FCtx P n c l s g) {q : TEv} (hq : q ∈ c.abs.events)
    (hqi : q.idx = g.cnt q.tid) :
    ∃ b x, WaitPair c.abs q b x ∧ P.isData x = false ∧
      ∀ q' ∈ c.abs.events, q'.tid = q.tid → q'.idx ≤ b.idx := by
  have hnL : q ∉ g.L := fun h' => by have := h.hI.ok.lt_cnt q h'; omega
  have htail : IsTail P c.abs q := by
    by_contra hn'; exact hnL ((h.memL q).mpr ⟨hq, hn'⟩)
  obtain ⟨p, b, x, hw, hx, hqe | hqe⟩ := htail
  · subst hqe
    refine ⟨b, x, hw, hx, fun q' hq' ht' => ?_⟩
    exact idx_le_block h.hE hw.2.1 hw.2.2.2.2.2 hq' (ht'.trans hw.2.2.1.symm)
  · subst hqe
    exfalso
    have hp : p ∈ g.L := h.inL_of_lt hw.1 (by rw [← hw.2.2.1]; have := hw.2.2.2.1; omega)
    exact ((h.memL p).mp hp).2 ⟨p, q, x, hw, hx, Or.inl rfl⟩

theorem maxWrite_eq (h : FCtx P n c l s g) (x : Loc) : c.abs.maxWrite x = g.last x := by
  have h1 : c.abs.co x = g.co x := by
    rw [h.hl.sub.co_eq h.hG x, h.hI.ok.co x, h.hgl]
  unfold Graph.maxWrite GB.last
  rw [h1]
  cases (g.co x).getLast? <;> rfl

/-- The value read by a final wait is the one of the builder's last write. -/
theorem ret_tail (h : FCtx P n c l s g) {q b : TEv} {x : Loc} (hw : WaitPair c.abs q b x)
    (hd : P.isData x = false) (hlast : ∀ q' ∈ c.abs.events, q'.tid = q.tid → q'.idx ≤ b.idx) :
    c.abs.ret q = some (valE P x (g.last x)) := by
  have hl' : ∀ q' ∈ c.abs.events, q'.tid = b.tid → q'.idx ≤ b.idx :=
    fun q' hq' ht' => hlast q' hq' (ht'.trans hw.2.2.1)
  have hrf := tail_final h.hT hw hd hl'
  unfold Graph.ret
  rw [hw.2.2.2.2.1]
  simp only
  rw [hrf, h.maxWrite_eq, valE_eq h.hE.1]
  rfl

/-- The events of a thread with a final wait `q`, `b` at the next index. -/
theorem cover (h : FCtx P n c l s g) {t : Tid} {q b : TEv} (hqt : q.tid = t)
    (hqi : q.idx = g.cnt t) (hbt : b.tid = t) (hbi : b.idx = g.cnt t + 1)
    (hq : q ∈ c.abs.events) (hb : b ∈ c.abs.events)
    (hlast : ∀ q' ∈ c.abs.events, q'.tid = t → q'.idx ≤ b.idx) :
    ∀ e ∈ c.abs.events, e.tid = t → e ∈ g.L ∨ e ∈ [q, b] := by
  intro e he het
  rcases Nat.lt_or_ge e.idx (g.cnt t) with hlt | hge
  · exact Or.inl (h.inL_of_lt he (by rw [het]; exact hlt))
  · right
    have hle := hlast e he het
    simp only [mem_cons, not_mem_nil, or_false]
    rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · left; exact h.hG.idx_inj e he q hq (het.trans hqt.symm) (by omega)
    · right; exact h.hG.idx_inj e he b hb (het.trans hbt.symm) (by omega)

/-- **The end of one thread.** -/
theorem thread (h : FCtx P n c l s g) {t : Tid} (ht : t ∈ P.threads) :
    next P s t = none ∧
      (∀ q ∈ c.abs.events, q.tid = t → q ∈ g.L ∨ q ∈ synE P s (g.cnt t) t) ∧
      (synE P s (g.cnt t) t = [] ∨ ∃ p b x, synE P s (g.cnt t) t = [p, b] ∧
        WaitPair c.abs p b x ∧ P.isData x = false ∧
        ∀ q ∈ c.abs.events, q.tid = t → q.idx ≤ b.idx) := by
  have hI := h.hI
  have hrel := hI.rel t ht
  unfold TRel at hrel
  cases hs : s.status t
  case term =>
    rw [hs] at hrel
    have hnone := h.no_at_cnt (step_none_of_tab (n := n) hrel)
    refine ⟨by simp [next, hs], fun q hq hqt => Or.inl (hnone q hq hqt), Or.inl ?_⟩
    simp [synE, hs]
  case erred =>
    rw [hs] at hrel
    have hnone := h.no_at_cnt (step_none_of_stopped (n := n) hrel)
    refine ⟨by simp [next, hs], fun q hq hqt => Or.inl (hnone q hq hqt), Or.inl ?_⟩
    simp [synE, hs]
  case stopped =>
    rw [hs] at hrel
    have hnone := h.no_at_cnt (step_none_of_stopped (n := n) hrel)
    refine ⟨by simp [next, hs], fun q hq hqt => Or.inl (hnone q hq hqt), Or.inl ?_⟩
    simp [synE, hs]
  case new =>
    rw [hs] at hrel
    obtain ⟨hu, -, -⟩ := hrel
    have hr : P.isRoot t = false := Bool.eq_false_iff.mpr (fun h' => hI.newRoot t h' hs)
    have hc0 : g.cnt t = 0 := by
      have := congrArg List.length hu
      simp only [tr, length_map, length_nil] at this
      rw [hI.ok.thr_length] at this
      exact this
    have hstep : (lifeSys P n).toProgram.step t (tr P g t) = some (.read (P.st t)) := by
      rw [hu]; exact step_of_lifeTab h.hn ht (by simp [stopped]) (lifeTab_nil hr)
    obtain ⟨q, hq, hqt, hqi, hqa⟩ := h.at_cnt hstep
    obtain ⟨b, x, hw, hxd, hlast⟩ := h.tail_at hq (by rw [hqt]; exact hqi)
    rw [hqt] at hlast
    have hx : x = P.st t := by
      have := hw.2.2.2.2.1; rw [hqa] at this; cases this; rfl
    subst hx
    have hret := h.ret_tail hw hxd (by rw [hqt]; exact hlast)
    -- the value read is `0`
    have hb0 : lifeTab P t [c.abs.ret q] = some .block := by
      have := (step_some (h.hE.2 b hw.2.1)).1
      rw [hw.2.2.2.2.2] at this
      rw [hw.2.2.1, hw.2.2.2.1, traceBefore_succ_ev h.hG hq, hqt, hqi, hc0] at this
      simpa [Graph.traceBefore] using this
    have hv0 : c.abs.ret q = some 0 := by
      by_contra hne
      rw [lifeTab_cons hr hne] at hb0
      exact (TState.ready_act P.st t (P.code t) (fun _ => 0)).2 hb0
    rw [hret] at hv0
    have hsd : s.started t = false := by
      have hv := hI.vLife t ht
      rw [Option.some.inj hv0] at hv
      by_contra hne
      rw [Bool.not_eq_false] at hne
      revert hv
      simp only [hne, ↓reduceIte]
      split_ifs <;> simp
    have hsyn : synE P s (g.cnt t) t = [q, b] := by
      simp only [synE, hs]
      congr 1
      · exact TEv.eq_of hqt.symm hqi.symm hqa.symm
      · congr 1
        exact TEv.eq_of (hw.2.2.1.trans hqt).symm (by rw [hw.2.2.2.1, hqi]) hw.2.2.2.2.2.symm
    refine ⟨by simp [next, hs, hsd], ?_, Or.inr ⟨q, b, P.st t, hsyn, hw, hxd, hlast⟩⟩
    rw [hsyn]
    exact h.cover hqt hqi (hw.2.2.1.trans hqt) (by rw [hw.2.2.2.1, hqi]) hq hw.2.1 hlast
  case running =>
    rw [hs] at hrel
    obtain ⟨hst, hb⟩ := hrel
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp
      (TState.ready_act P.st t (s.rest t) (holdsM s t)).1
    have hstep : (lifeSys P n).toProgram.step t (tr P g t) = some a :=
      step_of_lifeTab h.hn ht hst (by rw [lifeTab_of_bodyAt hb, ha])
    obtain ⟨q, hq, hqt, hqi, hqa⟩ := h.at_cnt hstep
    obtain ⟨b, x, hw, hxd, hlast⟩ := h.tail_at hq (by rw [hqt]; exact hqi)
    rw [hqt] at hlast
    have hax : a = .read x := by rw [← hqa]; exact hw.2.2.2.2.1
    rw [hax] at ha
    have hret := h.ret_tail hw hxd (by rw [hqt]; exact hlast)
    have hblock : (TState.next ⟨s.rest t, holdsM s t, .ready⟩
        (some (valE P x (g.last x)))).act P.st t = some .block := by
      have := (step_some (h.hE.2 b hw.2.1)).1
      rw [hw.2.2.2.2.2, hw.2.2.1, hw.2.2.2.1, traceBefore_succ_ev h.hG hq, hqt, hqi,
        ← h.trEq, hret, lifeTab_of_bodyAt (bodyAt_append hb _)] at this
      exact this
    have hbt : b.tid = t := hw.2.2.1.trans hqt
    have hbi : b.idx = g.cnt t + 1 := by rw [hw.2.2.2.1, hqi]
    have hcov := h.cover hqt hqi hbt hbi hq hw.2.1 hlast
    have hpair : ∀ y, x = y → [(⟨t, g.cnt t, .read y⟩ : TEv), ⟨t, g.cnt t + 1, .block⟩] = [q, b] :=
      fun y hy => by
        subst hy
        congr 1
        · exact TEv.eq_of hqt.symm hqi.symm (hqa.trans hax).symm
        · congr 1; exact TEv.eq_of hbt.symm hbi.symm hw.2.2.2.2.2.symm
    cases hr : s.rest t with
    | nil => rw [hr] at ha; simp [TState.act] at ha
    | cons op tl =>
      rw [hr] at ha hblock
      have hcall := callOk_head h.hF hI ht (by rw [hr]; rfl)
      cases op
      case lock y =>
        by_cases h0 : holdsM s t y = 0
        · have hxy : x = y := by simp [TState.act, h0] at ha; exact ha.symm
          subst hxy
          have hv : valE P x (g.last x) ≠ 0 := by
            intro hv0
            simp [TState.next, TState.act, h0, hv0] at hblock
          have hlk : P.isLock x = true := by simpa [callOk] using hcall
          have hcnt : s.count x ≠ 0 := by
            intro hc0; rw [hI.vLock x hlk, hc0] at hv; exact hv rfl
          have hheld : s.heldB t x = false := by
            cases hh : s.heldB t x
            · rfl
            · have := heldB_iff_holdsM.mp hh; omega
          have hsyn : synE P s (g.cnt t) t = [q, b] := by
            rw [show synE P s (g.cnt t) t = [⟨t, g.cnt t, .read x⟩, ⟨t, g.cnt t + 1, .block⟩] by
              simp [synE, hs, hr, hheld, hcnt]]
            exact hpair x rfl
          refine ⟨?_, by rw [hsyn]; exact hcov, Or.inr ⟨q, b, x, hsyn, hw, hxd, hlast⟩⟩
          simp [next, hs, hr, hheld, hcnt]
        · simp [TState.act, h0] at ha
      case join u =>
        have hxu : x = P.st u := by simp [TState.act] at ha; exact ha.symm
        subst hxu
        have hv1 : valE P (P.st u) (g.last (P.st u)) = 1 := by
          by_contra hne
          have hne' : some (valE P (P.st u) (g.last (P.st u))) ≠ some 1 :=
            fun h' => hne (Option.some.inj h')
          simp only [TState.next, hne', ↓reduceIte] at hblock
          exact (TState.ready_act P.st t tl (holdsM s t)).2 hblock
        have hu : u ∈ P.threads := by
          simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at hcall; exact hcall.1.1
        have hv := hI.vLife u hu
        rw [hv1] at hv
        have hsu : s.started u = true := by
          cases hsu : s.started u
          · rw [hsu] at hv; simp at hv
          · rfl
        have hterm : s.status u ≠ .term := by
          intro ht'; rw [hsu, ht'] at hv; simp at hv
        have hj : s.joinOkB u = false := by
          cases hj : s.joinOkB u
          · rfl
          · rcases joinOkB_eq_true.mp hj with ⟨-, h2⟩ | h2
            · rw [hsu] at h2; cases h2
            · exact absurd h2 hterm
        have hsyn : synE P s (g.cnt t) t = [q, b] := by
          rw [show synE P s (g.cnt t) t =
              [⟨t, g.cnt t, .read (P.st u)⟩, ⟨t, g.cnt t + 1, .block⟩] by
            simp [synE, hs, hr, hj]]
          exact hpair (P.st u) rfl
        refine ⟨?_, by rw [hsyn]; exact hcov, Or.inr ⟨q, b, P.st u, hsyn, hw, hxd, hlast⟩⟩
        simp [next, hs, hr, hj]
      case tryLock y k =>
        exfalso
        by_cases h0 : holdsM s t y = 0
        · have hxy : x = y := by simp [TState.act, h0] at ha; exact ha.symm
          subst hxy
          by_cases hv0 : valE P x (g.last x) = 0
          · simp [TState.next, TState.act, h0, hv0] at hblock
          · simp only [TState.next, h0, ↓reduceIte, Option.some.injEq, hv0] at hblock
            exact (TState.ready_act P.st t _ _).2 hblock
        · simp [TState.act, h0] at ha
      case unlock y =>
        exfalso
        simp only [TState.act] at ha
        split_ifs at ha <;> simp at ha
      case rd y =>
        exfalso
        exact (TState.ready_act P.st t tl (holdsM s t)).2 (by simpa [TState.next] using hblock)
      case wr y v => simp [TState.act] at ha
      case start u => simp [TState.act] at ha
      case assume y v =>
        exfalso
        have hxy : x = y := by simp [TState.act] at ha; exact ha.symm
        subst hxy
        have : P.isData x = true := by simpa [callOk] using hcall
        rw [hxd] at this; cases this

end FCtx

theorem before_prefix {A B : List TEv} {a b : TEv} (h : A.Before a b) : (A ++ B).Before a b :=
  ⟨mem_append_left _ h.1, mem_append_left _ h.2.1, by
    rw [idxOf_append_of_mem h.1, idxOf_append_of_mem h.2.1]; exact h.2.2⟩

theorem not_before_of_getLast {m : List TEv} (hn : m.Nodup) {z y : TEv}
    (hz : m.getLast? = some z) : ¬ m.Before z y := by
  obtain ⟨ys, rfl⟩ := getLast?_eq_some_iff.mp hz
  intro hb
  have hzys : z ∉ ys := fun h' => (nodup_append.mp hn).2.2 z h' z (mem_singleton_self z) rfl
  have h1 : (ys ++ [z]).idxOf z = ys.length := by
    rw [idxOf_append_of_notMem hzys]; simp
  have h2 := hb.2.2
  rw [h1] at h2
  rcases mem_append.mp hb.2.1 with hy | hy
  · rw [idxOf_append_of_mem hy] at h2
    have := idxOf_lt_length_of_mem hy
    omega
  · rw [mem_singleton.mp hy] at h2; omega

theorem maxWrite_init {G : Graph} {x : Loc} (h : G.maxWrite x = .init) : G.co x = [] := by
  unfold Graph.maxWrite at h
  cases hl : (G.co x).getLast? with
  | none => exact getLast?_eq_none_iff.mp hl
  | some e => rw [hl] at h; cases h

theorem maxWrite_th {G : Graph} {x : Loc} {e : TEv} (h : G.maxWrite x = .th e) :
    (G.co x).getLast? = some e := by
  unfold Graph.maxWrite at h
  cases hl : (G.co x).getLast? with
  | none => rw [hl] at h; cases h
  | some e' => rw [hl] at h; cases h; rfl

/-- No SC edge leaves the read of a final wait, except po to its `block`. -/
theorem final_read_out {G : Graph} (hG : G.Wf) {p b y : TEv} {x : Loc} (hw : WaitPair G p b x)
    (hrf : G.rf p = some (G.maxWrite x))
    (hlast : ∀ q ∈ G.events, q.tid = p.tid → q.idx ≤ b.idx)
    (h : G.scStep (.th p) (.th y)) : y = b := by
  obtain ⟨hp, hb, hbt, hbi, hpx, -⟩ := hw
  rcases h with h | h | h | h
  · obtain ⟨-, hy, hty, hlt⟩ := h
    have := hlast y hy hty.symm
    exact hG.idx_inj y hy b hb (hty.symm.trans hbt.symm) (by omega)
  · exfalso
    obtain ⟨e, he, heE, hrf'⟩ := h
    cases he
    obtain ⟨w, hw', hwt⟩ := hG.rf_read y heE _ (TEv.IsRead.exists_act (e := y) (by
      by_contra hn; rw [hG.rf_none y (Or.inr hn)] at hrf'; cases hrf'))
    rw [hrf'] at hw'; cases hw'
    obtain ⟨-, v, hv⟩ := hwt
    rw [hpx] at hv; cases hv
  · exfalso
    obtain ⟨z, hz⟩ := h
    obtain ⟨-, v, hv⟩ := (hG.co_mem z p).mp hz.1
    rw [hpx] at hv; cases hv
  · exfalso
    obtain ⟨e, e', z, he, he', -, hez, hco, hsrc⟩ := h
    cases he; cases he'
    rw [hpx] at hez; cases hez
    rcases hsrc with hs | ⟨e'', hs, hbf⟩
    · rw [hrf] at hs
      rw [maxWrite_init (Option.some.inj hs)] at hco
      cases hco
    · rw [hrf] at hs
      exact not_before_of_getLast (hG.co_nodup x) (maxWrite_th (Option.some.inj hs)) hbf

/-- **Gate clause 2, part 3.2: the end of the replay.** -/
theorem g2Final : G2Final := by
  intro P n c l hT hl rs s hs hI hgl
  have h : FCtx P n c l s (rs.foldl (emit P) GB.empty) := ⟨hT, hl, hI, hgl⟩
  have hmax : Maximal P s := fun o ho => by
    have := (h.thread (enabled_tid_mem ho)).1
    rw [next_of_enabled ho] at this; cases this
  have hok := runCfg_ok h.hF ⟨hs, hmax⟩
  refine ⟨hmax, ?_⟩
  have hnd := hok.nodup
  rw [finalizeE_L] at hnd ⊢
  generalize hgg : rs.foldl (emit P) GB.empty = g at h hnd
  -- the synthetic events
  have hsyn : ∀ q ∈ P.threads.flatMap (fun t => synE P s (g.cnt t) t), ∃ p b x,
      (q = p ∨ q = b) ∧ WaitPair c.abs p b x ∧ P.isData x = false ∧
      (∀ q' ∈ c.abs.events, q'.tid = p.tid → q'.idx ≤ b.idx) ∧
      ∃ X Y, g.L ++ P.threads.flatMap (fun t => synE P s (g.cnt t) t) = X ++ p :: b :: Y := by
    intro q hq
    obtain ⟨t, ht, hqt⟩ := mem_flatMap.mp hq
    rcases (h.thread ht).2.2 with he | ⟨p, b, x, he, hw, hxd, hlast⟩
    · rw [he] at hqt; cases hqt
    · rw [he] at hqt
      obtain ⟨ts1, ts2, hts⟩ := append_of_mem ht
      have hpt : p.tid = t := by
        have : p ∈ synE P s (g.cnt t) t := by rw [he]; simp
        unfold synE at this
        split at this
        · simp only [mem_cons, not_mem_nil, or_false] at this; rcases this with rfl | rfl <;> rfl
        · split at this
          · split_ifs at this
            · simp only [mem_cons, not_mem_nil, or_false] at this
              rcases this with rfl | rfl <;> rfl
            · cases this
          · split_ifs at this
            · simp only [mem_cons, not_mem_nil, or_false] at this
              rcases this with rfl | rfl <;> rfl
            · cases this
          · cases this
        · cases this
      refine ⟨p, b, x, by simpa using hqt, hw, hxd, by rw [hpt]; exact hlast, ?_⟩
      refine ⟨g.L ++ ts1.flatMap (fun t => synE P s (g.cnt t) t),
        ts2.flatMap (fun t => synE P s (g.cnt t) t), ?_⟩
      rw [hts, flatMap_append, flatMap_cons, he]
      simp
  refine ⟨⟨hnd, ?_, ?_, ?_⟩, ?_⟩
  · intro q hq
    rcases mem_append.mp hq with hq | hq
    · exact ((h.memL q).mp hq).1
    · obtain ⟨p, b, x, hpb, hw, -⟩ := hsyn q hq
      rcases hpb with rfl | rfl; exacts [hw.1, hw.2.1]
  · intro q hq hw
    exact mem_append_left _ (h.hgl ▸ h.hl.sub.writes q hq hw)
  · intro a ha b hb hab
    rcases mem_append.mp ha with ha' | ha'
    · rcases mem_append.mp hb with hb' | hb'
      · have := h.hl.sub.fwd a (h.hgl ▸ ha') b (h.hgl ▸ hb') hab
        rw [← h.hgl] at this
        exact before_prefix this
      · exact before_append_of_mem hnd ha' hb'
    · obtain ⟨p, b', x, hpb, hw, hxd, hlast, X, Y, hXY⟩ := hsyn a ha'
      rcases hpb with rfl | rfl
      · have hrf := tail_final hT hw hxd (fun q hq ht' => hlast q hq (ht'.trans hw.2.2.1))
        have hbb := final_read_out h.hG hw hrf hlast hab
        subst hbb
        rw [hXY] at hnd ⊢
        exact ⟨by simp, by simp, by rw [idxOf_imm X hnd]; omega⟩
      · exfalso
        obtain ⟨-, hbE, htid, hlt⟩ := scStep_out_block h.hG hw.2.2.2.2.2 hab
        have := hlast b hbE (htid.symm.trans hw.2.2.1)
        omega
  · intro q hq
    have ht := (step_some (h.hE.2 q hq)).2.2.2
    rcases (h.thread ht).2.1 q hq rfl with h1 | h1
    · exact mem_append_left _ h1
    · exact mem_append_right _ (mem_flatMap.mpr ⟨q.tid, ht, h1⟩)

/-- **Gate clause 2, part 3: the replay.** -/
theorem g2Replay : G2Replay := g2Replay_of_parts g2Steps g2Final

/-- **Gate clause 2.** Every terminal-valid full graph of `lifeSys` is the graph of a maximal
run of the machine. -/
theorem gate2 : Gate2 := gate2_of_parts g2Lin g2Adj g2Replay

end Sem

end Life

end Condpor
