import Mazurkiewicz.Condpor.Rmw.LifecycleGate2Next

/-!
# Gate clause 2, part 3d: the thread of the next event can step (LC2-b, continuation 3)

`Ctx P n c l s g e rest`: a terminal-valid `c`, a run list `l`, a state `s` with `SInv` and
builder `g`, and `l = g.L ++ e :: rest`.

* `next_in_G`: if the compiled step after an event's trace is defined, the full graph has the
  next event of its thread, with that label;
* `Ctx.ret_read`: the next event reads the value of the builder's last write;
* **`Ctx.enabled`**: the thread of `e` has an enabled occurrence. Otherwise it is new and not
  started, or at a disabled `lock` or `join`, or ended or stopped; in the first three cases `e`
  would be the read of a tail pair (the value read is `0`, `1`, `1`, and the next compiled
  action is `block`); in the last ones it would have no compiled step.
-/

namespace Condpor

namespace Life

namespace Sem

open _root_.List

variable {P : LProg} {n : ℕ} {G : Graph}

/-- The trace before the next index of an event. -/
theorem traceBefore_succ_ev (hG : G.Wf) {e : TEv} (he : e ∈ G.events) :
    G.traceBefore e.tid (e.idx + 1) = G.traceBefore e.tid e.idx ++ [G.ret e] := by
  rw [Graph.traceBefore_succ, Graph.evAt_eq_some_of_inj hG.idx_inj he]
  rfl

/-- In a full execution, a defined compiled step after an event gives the next event. -/
theorem next_in_G (hG : G.Wf) (hE : (lifeSys P n).toProgram.Exec G)
    (hfu : (lifeSys P n).toProgram.Full G) {e : TEv} (he : e ∈ G.events) {a : Act}
    (h : (lifeSys P n).toProgram.step e.tid (G.traceBefore e.tid (e.idx + 1)) = some a) :
    ∃ e2 ∈ G.events, e2.tid = e.tid ∧ e2.idx = e.idx + 1 ∧ e2.act = a := by
  have hlt : e.idx < G.cnt e.tid := (hG.exists_idx_iff _ _).mp ⟨e, he, rfl, rfl⟩
  by_cases h2 : e.idx + 1 < G.cnt e.tid
  · obtain ⟨e2, he2, h1, h2'⟩ := (hG.exists_idx_iff _ _).mpr h2
    have := hE.2 e2 he2
    rw [h1, h2', h] at this
    exact ⟨e2, he2, h1, h2', (Option.some.inj this).symm⟩
  · have hc : G.cnt e.tid = e.idx + 1 := by omega
    have hfull := (Program.full_iff.mp hfu) e.tid (step_some h).2.2.2
    unfold Graph.trace at hfull
    rw [hc, h] at hfull
    cases hfull

/-- The context of one replay step. -/
structure Ctx (P : LProg) (n : ℕ) (c : Config) (l : List TEv) (s : MState) (g : GB) (e : TEv)
    (rest : List TEv) : Prop where
  hT : TermValid P n c
  hl : RunList P (lifeSys P n) c.abs l
  hI : SInv P n s g
  hpre : l = g.L ++ e :: rest

namespace Ctx

variable {c : Config} {l rest : List TEv} {s : MState} {g : GB} {e : TEv}

theorem hF (h : Ctx P n c l s g e rest) : Frag P := frag_of_fragB h.hT.1
theorem hn (h : Ctx P n c l s g e rest) : adequateB P n = true := h.hT.2.1
theorem hG (h : Ctx P n c l s g e rest) : c.abs.Wf := h.hT.2.2.1.1
theorem hE (h : Ctx P n c l s g e rest) : (lifeSys P n).toProgram.Exec c.abs := h.hT.2.2.2.1
theorem hfu (h : Ctx P n c l s g e rest) : (lifeSys P n).toProgram.Full c.abs :=
  h.hT.2.2.2.2.2.1

theorem hel (h : Ctx P n c l s g e rest) : e ∈ l := by rw [h.hpre]; simp
theorem heG (h : Ctx P n c l s g e rest) : e ∈ c.abs.events := h.hl.sub.sub e h.hel

theorem idx (h : Ctx P n c l s g e rest) : e.idx = g.cnt e.tid :=
  (next_idx h.hI.ok h.hG h.hE h.hl h.hpre).1

theorem step (h : Ctx P n c l s g e rest) :
    (lifeSys P n).toProgram.step e.tid (tr P g e.tid) = some e.act :=
  next_act h.hI.ok h.hG h.hE h.hl h.hpre

theorem ht (h : Ctx P n c l s g e rest) : e.tid ∈ P.threads := (step_some h.step).2.2.2

theorem trace (h : Ctx P n c l s g e rest) :
    c.abs.traceBefore e.tid e.idx = tr P g e.tid := by
  rw [h.idx, tr_eq h.hI.ok h.hG h.hl.sub h.hpre h.hE.1]

/-- The next event reads the value of the builder's last write. -/
theorem ret_read (h : Ctx P n c l s g e rest) {x : Loc} (hx : e.act = .read x) :
    c.abs.ret e = some (valE P x (g.last x)) := by
  unfold Graph.ret
  rw [hx]
  simp only
  rw [next_rf h.hI.ok h.hG h.hl h.hpre hx, valE_eq h.hE.1]
  rfl

/-- The next event is not the read of a wait pair at a non-data location. -/
theorem not_tail_read (h : Ctx P n c l s g e rest) {x : Loc} (hx : e.act = .read x)
    (hd : P.isData x = false)
    (hb : (lifeSys P n).toProgram.step e.tid (c.abs.traceBefore e.tid (e.idx + 1)) =
      some .block) : False := by
  obtain ⟨e2, he2, h1, h2, h3⟩ := next_in_G h.hG h.hE h.hfu h.heG hb
  exact ((h.hl.mem e).mp h.hel).2 ⟨e, e2, x, ⟨h.heG, he2, h1, h2, hx, h3⟩, hd, Or.inl rfl⟩

/-- A read of the next event whose value `v` makes the compiled body block. -/
theorem block_after (h : Ctx P n c l s g e rest) {x : Loc} (hx : e.act = .read x)
    {st : TState} (hst : stopped (lifeTab P) e.tid (tr P g e.tid) = false)
    (hb : BodyAt P e.tid (tr P g e.tid) st) (ha : st.act P.st e.tid = some (.read x))
    (hnb : (st.next (some (valE P x (g.last x)))).act P.st e.tid = some .block) :
    (lifeSys P n).toProgram.step e.tid (c.abs.traceBefore e.tid (e.idx + 1)) = some .block := by
  rw [traceBefore_succ_ev h.hG h.heG, h.trace, h.ret_read hx]
  have hb1 := bodyAt_append hb (some (valE P x (g.last x)))
  refine step_of_lifeTab h.hn h.ht ?_ ?_
  · rw [stopped_append, hst, lifeTab_of_bodyAt hb, ha]; rfl
  · rw [lifeTab_of_bodyAt hb1, hnb]

/-- **The thread of the next event has an enabled occurrence.** -/
theorem enabled (h : Ctx P n c l s g e rest) : ∃ o, Enabled P s o ∧ o.tid = e.tid := by
  have hI := h.hI
  have ht := h.ht
  obtain ⟨htab, hst, -, -⟩ := step_some h.step
  cases hnx : next P s e.tid with
  | some o => exact ⟨o, enabled_of_next ht hnx, next_tid hnx⟩
  | none =>
    exfalso
    have hrel := hI.rel e.tid ht
    unfold TRel at hrel
    cases hs : s.status e.tid with
    | new =>
      rw [hs] at hrel
      obtain ⟨hu, -, -⟩ := hrel
      have hr : P.isRoot e.tid = false :=
        Bool.eq_false_iff.mpr (fun h' => hI.newRoot e.tid h' hs)
      have hsd : s.started e.tid = false := by
        unfold next at hnx; rw [hs] at hnx
        cases hsd : s.started e.tid
        · rfl
        · rw [hsd] at hnx; cases hnx
      rw [hu, lifeTab_nil hr] at htab
      have hx : e.act = .read (P.st e.tid) := (Option.some.inj htab).symm
      have hv : valE P (P.st e.tid) (g.last (P.st e.tid)) = 0 := by
        rw [hI.vLife e.tid ht, hsd]; rfl
      refine h.not_tail_read hx (h.hF.isData_st ht) ?_
      rw [traceBefore_succ_ev h.hG h.heG, h.trace, h.ret_read hx, hv, hu]
      refine step_of_lifeTab h.hn ht (by simp [stopped, lifeTab_nil hr, isStop]) ?_
      simp [lifeTab, hr]
    | running =>
      rw [hs] at hrel
      obtain ⟨hst', hb⟩ := hrel
      rcases next_none_running hs hnx with ⟨x, hc, hh, hcnt⟩ | ⟨u, hc, hj⟩
      · rw [rest_cons hc] at hb
        have h0 : holdsM s e.tid x = 0 := holdsM_zero hh
        have hlk : P.isLock x = true := by simpa [callOk] using callOk_head h.hF hI ht hc
        have ha : (⟨.lock x :: (s.rest e.tid).tail, holdsM s e.tid, .ready⟩ : TState).act
            P.st e.tid = some (.read x) := by simp [TState.act, h0]
        rw [lifeTab_of_bodyAt hb, ha] at htab
        have hx : e.act = .read x := (Option.some.inj htab).symm
        have hv : valE P x (g.last x) = 1 := by rw [hI.vLock x hlk]; simp [hcnt]
        refine h.not_tail_read hx (by simp [LProg.isData, hlk]) (h.block_after hx hst' hb ha ?_)
        rw [hv]; simp [TState.next, TState.act, h0]
      · rw [rest_cons hc] at hb
        have hcall := callOk_head h.hF hI ht hc
        have hu : u ∈ P.threads := by
          simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at hcall; exact hcall.1.1
        have ha : (⟨.join u :: (s.rest e.tid).tail, holdsM s e.tid, .ready⟩ : TState).act
            P.st e.tid = some (.read (P.st u)) := by simp [TState.act]
        rw [lifeTab_of_bodyAt hb, ha] at htab
        have hx : e.act = .read (P.st u) := (Option.some.inj htab).symm
        have hsu : s.started u = true := by
          by_contra hn'
          have hnew : s.status u = .new := by
            by_contra hne; exact hn' (hI.minv.started_of u hne)
          rw [Bool.not_eq_true] at hn'
          have := joinOkB_eq_true.mpr (Or.inl ⟨hnew, hn'⟩)
          rw [hj] at this; cases this
        have hterm : s.status u ≠ .term := fun h' => by
          have := joinOkB_eq_true.mpr (Or.inr h')
          rw [hj] at this; cases this
        have hv : valE P (P.st u) (g.last (P.st u)) = 1 := by
          rw [hI.vLife u hu, hsu]; simp [hterm]
        refine h.not_tail_read hx (h.hF.isData_st hu) (h.block_after hx hst' hb ha ?_)
        rw [hv]; simp [TState.next, TState.act]
    | term =>
      rw [hs] at hrel
      rw [hrel] at htab; cases htab
    | erred =>
      rw [hs] at hrel
      rw [hrel] at hst; cases hst
    | stopped =>
      rw [hs] at hrel
      rw [hrel] at hst; cases hst

end Ctx

end Sem

end Life

end Condpor
