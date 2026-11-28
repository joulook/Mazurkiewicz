import Mazurkiewicz.Condpor.Rmw.LifecycleGate2Step

/-!
# Gate clause 2, part 3e: the enabled occurrence emits the next events (LC2-b, cont. 3)

For an enabled occurrence `o` of the thread of the next event `e` of the run list:

* `new_step`: the events that `emit` appends carry the compiled steps after the builder's
  values (from `ExecT` of the new builder, `SInv.thread`); so the first one is `e`;
* for `acq`/`tryAcq` the second appended event is the exclusive write after `e` in the graph,
  `e` and it form a completed pair, adjacent in the run list; for `asmStop` the second one is
  the `block` after `e`, an assumption pair, adjacent in the run list;
* **`Ctx.emit`**: `emit P g o` appends exactly the next one or two events of the run list.
-/

namespace Condpor

namespace Life

namespace Sem

open _root_.List

variable {P : LProg} {n : ℕ}

theorem TEv.eq_of {a b : TEv} (h1 : a.tid = b.tid) (h2 : a.idx = b.idx) (h3 : a.act = b.act) :
    a = b := by
  cases a; cases b; simp_all

theorem split_eq {l A B A' B' : List TEv} {e : TEv} (hn : l.Nodup) (h1 : l = A ++ e :: B)
    (h2 : l = A' ++ e :: B') : B = B' := by
  have hA : e ∉ A := by
    rw [h1] at hn; exact fun h => (nodup_append.mp hn).2.2 e h e mem_cons_self rfl
  have hA' : e ∉ A' := by
    rw [h2] at hn; exact fun h => (nodup_append.mp hn).2.2 e h e mem_cons_self rfl
  have hlen : A.length = A'.length := by
    have := congrArg (List.idxOf e) (h1.symm.trans h2)
    rw [idxOf_append_of_notMem hA, idxOf_append_of_notMem hA', idxOf_cons_self] at this
    simpa using this
  have := (append_inj (h1.symm.trans h2) hlen).2
  exact (cons.inj this).2

/-- The builder keeps the values of its old events. -/
theorem retG_prefix {g g' : GB} (hg : g.Ok) (hg' : g'.Ok) {news : List TEv}
    (hL : g'.L = g.L ++ news) {e : TEv} (he : e ∈ g.L) : retG P g' e = retG P g e := by
  unfold retG
  split
  next x hact =>
    have hr : isReadB e = true := isReadB_iff.mpr (by simp [TEv.IsRead, hact, Act.IsRead])
    rw [hg'.rf e, hg.rf e, hL, pre_append_of_mem' he]
    simp [he, hr]
  next => rfl

/-- The appended events carry the compiled steps after the builder's values. -/
theorem new_step {g g' : GB} (hg : g.Ok) (hg' : g'.Ok) (hx : ExecT P n g') {news : List TEv}
    (hL : g'.L = g.L ++ news) {t : Tid} (hnt : ∀ e ∈ news, e.tid = t) {j : ℕ}
    (hj : j < news.length) :
    (lifeSys P n).toProgram.step t (tr P g t ++ (news.take j).map (retG P g')) =
      some (news[j]).act := by
  have hthr : thr g' t = thr g t ++ news := by
    unfold thr
    rw [hL, filter_append]
    congr 1
    exact filter_eq_self.mpr (fun a ha => by simp [hnt a ha])
  have htr : tr P g' t = tr P g t ++ news.map (retG P g') := by
    unfold tr
    rw [hthr, map_append]
    congr 1
    exact map_congr_left (fun e he => retG_prefix hg hg' hL (mem_filter.mp he).1)
  have hlen : (tr P g t).length = (thr g t).length := by simp [tr]
  have hlt : (thr g t).length + j < (thr g' t).length := by rw [hthr, length_append]; omega
  have hget : (thr g' t)[(thr g t).length + j]'hlt = news[j] := by
    simp only [hthr]
    rw [getElem_append_right (by omega)]
    simp
  have h := hx t ((thr g t).length + j) hlt
  rw [hget, htr, ← hlen, take_length_add_append, ← map_take] at h
  exact h

theorem L_readLast (g : GB) (t : Tid) (x : Loc) :
    (g.readLast t x).L = g.L ++ [g.ev t (.read x)] := by
  simp [GB.readLast, GB.read, GB.L, GB.push]

theorem L_write (g : GB) (t : Tid) (x : Loc) (v : Val) :
    (g.write t x v).L = g.L ++ [g.ev t (.write x v)] := by
  simp [GB.write, GB.L, GB.push]

theorem L_loc0 (g : GB) (t : Tid) (a : Act) : (g.loc0 t a).L = g.L ++ [g.ev t a] := by
  simp [GB.loc0, GB.L, GB.push]

theorem ev_readLast (g : GB) (t : Tid) (x : Loc) (b : Act) :
    (g.readLast t x).ev t b = ⟨t, g.cnt t + 1, b⟩ := by
  simp [GB.readLast, GB.read, GB.ev, GB.push]

theorem ex_read {t : Tid} {u : List (Option Val)} {x : Loc}
    (h : (lifeSys P n).toProgram.step t u = some (.read x)) :
    (lifeSys P n).ex t u = lifeFlag P t u := by
  change exFlag (lifeSys P n).toProgram.step (lifeFlag P) t u = _
  unfold exFlag
  rw [h]

theorem ex_write {t : Tid} {u : List (Option Val)} {x : Loc} {v : Val} {w : Option Val}
    (h : (lifeSys P n).toProgram.step t (u ++ [w]) = some (.write x v)) (hw : w.isSome) :
    (lifeSys P n).ex t (u ++ [w]) = (lifeFlag P t (u ++ [w]) && lifeFlag P t u &&
      decide ((lifeSys P n).toProgram.step t u = some (.read x))) := by
  change exFlag (lifeSys P n).toProgram.step (lifeFlag P) t (u ++ [w]) = _
  unfold exFlag
  rw [h]
  obtain ⟨w', rfl⟩ := Option.isSome_iff_exists.mp hw
  simp [Bool.and_assoc]

/-- The occurrences that emit one event. -/
def Occ.single : Occ → Bool
  | .acq _ _ | .tryAcq _ _ _ | .asmStop _ _ _ => false
  | _ => true

theorem emit_single_L (g : GB) {o : Occ} (ho : o.single = true) :
    ∃ a, (emit P g o).L = g.L ++ [g.ev o.tid a] := by
  cases o <;> simp_all [Occ.single, emit, L_readLast, L_write, L_loc0, Occ.tid]

theorem L_acq (g : GB) (t : Tid) (x : Loc) :
    ((g.readLast t x).write t x 1).L =
      g.L ++ [g.ev t (.read x), ⟨t, g.cnt t + 1, .write x 1⟩] := by
  rw [L_write, L_readLast, ev_readLast]; simp

theorem L_asm (g : GB) (t : Tid) (x : Loc) :
    ((g.readLast t x).loc0 t .block).L = g.L ++ [g.ev t (.read x), ⟨t, g.cnt t + 1, .block⟩] := by
  rw [L_loc0, L_readLast, ev_readLast]; simp

theorem retG_acq {g : GB} (hg : g.Ok) (t : Tid) (x : Loc) :
    retG P ((g.readLast t x).write t x 1) (g.ev t (.read x)) = some (valE P x (g.last x)) := by
  rw [(retG_write (P := P) (g := g.readLast t x) t x 1).1 _ (by rw [L_readLast]; simp)]
  exact (retG_readLast hg t x).2

theorem retG_asm {g : GB} (hg : g.Ok) (t : Tid) (x : Loc) :
    retG P ((g.readLast t x).loc0 t .block) (g.ev t (.read x)) = some (valE P x (g.last x)) := by
  rw [(retG_loc0 (P := P) (g := g.readLast t x) t .block (by simp [Act.IsLocal])).1 _
    (by rw [L_readLast]; simp)]
  exact (retG_readLast hg t x).2

namespace Ctx

variable {c : Config} {l rest : List TEv} {s : MState} {g : GB} {e : TEv}

theorem ev_eq (h : Ctx P n c l s g e rest) {a : Act} (ha : e.act = a) : g.ev e.tid a = e :=
  TEv.eq_of rfl h.idx.symm ha.symm

theorem notMemL (h : Ctx P n c l s g e rest) : e ∉ g.L := by
  have hn := h.hl.sub.nodup
  rw [h.hpre] at hn
  exact fun h' => (nodup_append.mp hn).2.2 e h' e mem_cons_self rfl

/-- One appended event. -/
theorem single {o : Occ} (h : Ctx P n c l s g e rest) (ho : Enabled P s o)
    {a : Act} (hL : (emit P g o).L = g.L ++ [g.ev e.tid a]) :
    ∃ pre rest', (emit P g o).L = g.L ++ pre ∧ e :: rest = pre ++ rest' ∧ pre ≠ [] := by
  obtain ⟨hx, -, -⟩ := h.hI.thread h.hF h.hn ho
  have h0 := new_step h.hI.ok (emit_ok P h.hI.ok o) hx hL (t := e.tid)
    (fun e' he' => by rw [mem_singleton.mp he']; rfl) (j := 0) (by simp)
  simp only [take_zero, map_nil, append_nil, getElem_cons_zero, GB.ev] at h0
  rw [h.step] at h0
  have hev : g.ev e.tid a = e := h.ev_eq (Option.some.inj h0)
  exact ⟨[e], rest, by rw [hL, hev], rfl, by simp⟩

/-- Two appended events: a read of `x` and the next event of the thread. -/
theorem double {o : Occ} (h : Ctx P n c l s g e rest) (ho : Enabled P s o)
    {x : Loc} {a : Act}
    (hL : (emit P g o).L = g.L ++ [g.ev e.tid (.read x), ⟨e.tid, g.cnt e.tid + 1, a⟩])
    (hv : retG P (emit P g o) (g.ev e.tid (.read x)) = some (valE P x (g.last x)))
    (hadj : ∀ e2 ∈ c.abs.events, e2.tid = e.tid → e2.idx = e.idx + 1 → e2.act = a →
      e.act = .read x → ∃ l₁ l₂, l = l₁ ++ e :: e2 :: l₂) :
    ∃ pre rest', (emit P g o).L = g.L ++ pre ∧ e :: rest = pre ++ rest' ∧ pre ≠ [] := by
  obtain ⟨hx, -, -⟩ := h.hI.thread h.hF h.hn ho
  have hnt : ∀ e' ∈ [g.ev e.tid (.read x), (⟨e.tid, g.cnt e.tid + 1, a⟩ : TEv)], e'.tid = e.tid :=
    fun e' he' => by
      simp only [mem_cons, not_mem_nil, or_false] at he'
      rcases he' with rfl | rfl <;> rfl
  have h0 := new_step h.hI.ok (emit_ok P h.hI.ok o) hx hL hnt (j := 0) (by simp)
  simp only [take_zero, map_nil, append_nil, getElem_cons_zero, GB.ev] at h0
  rw [h.step] at h0
  have hea : e.act = .read x := Option.some.inj h0
  have hev : g.ev e.tid (.read x) = e := h.ev_eq hea
  have h1 := new_step h.hI.ok (emit_ok P h.hI.ok o) hx hL hnt (j := 1) (by simp)
  simp only [take_add_one, take_zero, getElem_cons_zero, getElem?_cons_zero, Option.toList_some,
    nil_append, map_cons, map_nil, getElem_cons_succ] at h1
  rw [hv, ← h.ret_read hea, ← h.trace, ← traceBefore_succ_ev h.hG h.heG] at h1
  obtain ⟨e2, he2, h2t, h2i, h2a⟩ := next_in_G h.hG h.hE h.hfu h.heG h1
  have hev2 : (⟨e.tid, g.cnt e.tid + 1, a⟩ : TEv) = e2 :=
    TEv.eq_of h2t.symm (by rw [h2i, h.idx]) h2a.symm
  obtain ⟨l₁, l₂, hl⟩ := hadj e2 he2 h2t h2i h2a hea
  have hrest := split_eq h.hl.sub.nodup h.hpre hl
  refine ⟨[e, e2], l₂, by rw [hL, hev, hev2], by rw [hrest]; rfl, by simp⟩

/-- **The enabled occurrence emits the next events of the run list.** -/
theorem emit (h : Ctx P n c l s g e rest) {o : Occ} (ho : Enabled P s o) (hot : o.tid = e.tid) :
    ∃ pre rest', (emit P g o).L = g.L ++ pre ∧ e :: rest = pre ++ rest' ∧ pre ≠ [] := by
  have hI := h.hI
  cases hs1 : o.single
  · cases ho
    case acq t x ht hs hc hh hf =>
      simp only [Occ.tid] at hot; subst hot
      obtain ⟨-, hb⟩ := trel_running (hI.rel e.tid ht) hs
      rw [rest_cons hc] at hb
      have h0 : holdsM s e.tid x = 0 := holdsM_zero hh
      have hlk : P.isLock x = true := by simpa [callOk] using callOk_head h.hF hI ht hc
      have hv0 : valE P x (g.last x) = 0 := by rw [hI.vLock x hlk, hf]; rfl
      refine h.double (.acq ht hs hc hh hf) (L_acq g e.tid x) (retG_acq hI.ok e.tid x) ?_
      intro e2 he2 h2t h2i h2a hea
      refine h.hl.rmw e e2 ⟨h.heG, he2, h2t, h2i, by simp [TEv.IsRead, hea, Act.IsRead],
        by simp [TEv.IsWrite, h2a, Act.IsWrite], ?_, ?_⟩
      · change (lifeSys P n).ex e.tid (c.abs.traceBefore e.tid e.idx) = true
        rw [h.trace, ex_read (h.step.trans (by rw [hea])), lifeFlag_of_bodyAt hb]
        simp [TState.isEx, h0]
      · change (lifeSys P n).ex e2.tid (c.abs.traceBefore e2.tid e2.idx) = true
        have htr2 : c.abs.traceBefore e2.tid e2.idx = tr P g e.tid ++ [some 0] := by
          rw [h2t, h2i, traceBefore_succ_ev h.hG h.heG, h.trace, h.ret_read hea, hv0]
        have hstep2 := h.hE.2 e2 he2
        rw [htr2, h2a, h2t] at hstep2
        rw [htr2, h2t, ex_write hstep2 rfl, lifeFlag_of_bodyAt (bodyAt_append hb _),
          lifeFlag_of_bodyAt hb]
        simp [TState.isEx, TState.next, h0, h.step, hea]
    case tryAcq t x k ht hs hc hh hf =>
      simp only [Occ.tid] at hot; subst hot
      obtain ⟨-, hb⟩ := trel_running (hI.rel e.tid ht) hs
      rw [rest_cons hc] at hb
      have h0 : holdsM s e.tid x = 0 := holdsM_zero hh
      have hlk : P.isLock x = true := by simpa [callOk] using callOk_head h.hF hI ht hc
      have hv0 : valE P x (g.last x) = 0 := by rw [hI.vLock x hlk, hf]; rfl
      refine h.double (.tryAcq ht hs hc hh hf) (L_acq g e.tid x) (retG_acq hI.ok e.tid x) ?_
      intro e2 he2 h2t h2i h2a hea
      refine h.hl.rmw e e2 ⟨h.heG, he2, h2t, h2i, by simp [TEv.IsRead, hea, Act.IsRead],
        by simp [TEv.IsWrite, h2a, Act.IsWrite], ?_, ?_⟩
      · change (lifeSys P n).ex e.tid (c.abs.traceBefore e.tid e.idx) = true
        rw [h.trace, ex_read (h.step.trans (by rw [hea])), lifeFlag_of_bodyAt hb]
        simp [TState.isEx, h0]
      · change (lifeSys P n).ex e2.tid (c.abs.traceBefore e2.tid e2.idx) = true
        have htr2 : c.abs.traceBefore e2.tid e2.idx = tr P g e.tid ++ [some 0] := by
          rw [h2t, h2i, traceBefore_succ_ev h.hG h.heG, h.trace, h.ret_read hea, hv0]
        have hstep2 := h.hE.2 e2 he2
        rw [htr2, h2a, h2t] at hstep2
        rw [htr2, h2t, ex_write hstep2 rfl, lifeFlag_of_bodyAt (bodyAt_append hb _),
          lifeFlag_of_bodyAt hb]
        simp [TState.isEx, TState.next, h0, h.step, hea]
    case asmStop t x v ht hs hc hv =>
      simp only [Occ.tid] at hot; subst hot
      have hd : P.isData x = true := by simpa [callOk] using callOk_head h.hF hI ht hc
      refine h.double (.asmStop ht hs hc hv) (L_asm g e.tid x) (retG_asm hI.ok e.tid x) ?_
      intro e2 he2 h2t h2i h2a hea
      exact h.hl.asm e e2 ⟨x, ⟨h.heG, he2, h2t, h2i, hea, h2a⟩, hd⟩
    all_goals simp [Occ.single] at hs1
  · obtain ⟨a, ha⟩ := emit_single_L (P := P) g hs1
    rw [hot] at ha
    exact h.single ho ha

end Ctx

/-- **Gate clause 2, one replay step.** -/
theorem g2Step : G2Step := by
  intro P n c l hT hl rs s e rest hs hpre
  have hI := SInv.steps (frag_of_fragB hT.1) hT.2.1 hs
  have h : Ctx P n c l s (rs.foldl (emit P) GB.empty) e rest := ⟨hT, hl, hI, hpre⟩
  obtain ⟨o, ho, hot⟩ := h.enabled
  obtain ⟨pre, rest', h1, h2, h3⟩ := h.emit ho hot
  exact ⟨o, pre, rest', ho, h1, h2, h3⟩

/-- **The replay of a run list.** -/
theorem g2Steps : G2Steps := g2Steps_of_step g2Step

end Sem

end Life

end Condpor
