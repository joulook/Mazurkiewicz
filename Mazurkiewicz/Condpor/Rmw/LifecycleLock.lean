import Mazurkiewicz.Condpor.Rmw.LifecycleLemmas
import Mazurkiewicz.Condpor.Rmw.LockMutex

/-!
# Thread lifecycle: the lock invariant (LC1, round 2)

The supporting invariant of §4 (draft 4.2) on locks: for a program of the fragment and a
well-formed execution `G` of `lifeSys P n` that is SC-consistent and atomic, the value of a
lock location `l` (the value of its coherence-maximal write, or the initial `0`) is `0` iff
no thread's compiled hold count for `l` after its trace is positive (`lock_value_iff`).

* `holdsOf P t u l`: the hold count of `l` of thread `t` after its trace `u`: the count of
  the body state; `0` for a non-root thread whose start-read returned `0` or that has no
  event.
* `lifeSys_lockLike`: the writes of `l` behave as acquires and releases (`LockLike` of
  `LockMutex.lean`); with `LockLike.alternates` the coherence order of `l` alternates
  between an acquire by a thread and its release by that thread (`lifeSys_mutex`).

Hypotheses: `Frag P`, `G.Wf`, `Exec`, `SC.cons G` and atomicity (`(lifeSys P n).Atomic G`),
i.e. `(Model.atomic (lifeSys P n) SC).cons G`. Fullness is not needed.
-/

namespace Condpor

namespace Life

open Program

variable {P : LProg} {n : ℕ}

/-- The compiled hold count of `l` of thread `t` after the trace `u`. -/
def holdsOf (P : LProg) (t : Tid) (u : List (Option Val)) (l : Loc) : ℕ :=
  if P.isRoot t then (tState (P.code t) u).holds l
  else
    match u with
    | [] => 0
    | v :: rest => if v = some 0 then 0 else (tState (P.code t) rest).holds l

/-! ### The body and the lock -/

/-! #### Steps of a body that need no fragment -/

section bodyFree

variable {t : Tid} {l : Loc}

/-- One step that is not a release keeps a positive hold count. -/
theorem holds_next_pos {s : TState} (hs : Inv P t s) {v : Option Val} (h : 0 < s.holds l)
    (hna : s.act P.st t ≠ some (.write l 0)) : 0 < (s.next v).holds l := by
  obtain ⟨hops, -⟩ := hs
  rcases s with ⟨ops, holds, ph⟩
  cases ph with
  | acquire l' =>
    simp only [TState.next]
    by_cases hll : l' = l
    · subst hll; simp
    · simpa [Function.update_of_ne (Ne.symm hll)] using h
  | blocking => exact h
  | done => exact h
  | ready =>
    cases ops with
    | nil => exact h
    | cons c rest =>
      cases c with
      | lock l' =>
        simp only [TState.next]
        split_ifs with h0
        · exact h
        · exact h
        · by_cases hll : l' = l
          · subst hll; simp
          · simpa [Function.update_of_ne (Ne.symm hll)] using h
      | tryLock l' k =>
        simp only [TState.next]
        split_ifs with h0
        · exact h
        · exact h
        · by_cases hll : l' = l
          · subst hll; simp
          · simpa [Function.update_of_ne (Ne.symm hll)] using h
      | unlock l' =>
        simp only [TState.next]
        split_ifs with h0
        · exact h
        · by_cases hll : l' = l
          · subst hll
            have h1 : holds l' ≠ 1 := by
              intro h1
              apply hna
              simp [TState.act, h1]
            simp
            omega
          · simpa [Function.update_of_ne (Ne.symm hll)] using h
      | rd x => exact h
      | wr x v' => exact h
      | start u => exact h
      | join u => simp only [TState.next]; split_ifs <;> exact h
      | assume x w => simp only [TState.next]; split_ifs <;> exact h

/-- After the write of an acquire the hold count is `1`. -/
theorem holds_after_acquire {s : TState} (hp : s.phase = .acquire l) (v : Option Val) :
    (s.next v).holds l = 1 := by
  rcases s with ⟨ops, holds, ph⟩
  simp only at hp
  subst hp
  simp [TState.next]

/-- The phase `acquire l` is entered only by an acquire read of `l` that returned `0`. -/
theorem acquire_of_next {s : TState} {v : Option Val} (h : (s.next v).phase = .acquire l)
    (hs : s.phase ≠ .acquire l) :
    s.phase = .ready ∧ s.holds l = 0 ∧ v = some 0 ∧
      ((∃ rest, s.ops = .lock l :: rest) ∨ ∃ k rest, s.ops = .tryLock l k :: rest) := by
  rcases s with ⟨ops, holds, ph⟩
  cases ph with
  | acquire l' => simp [TState.next] at h
  | blocking => simp [TState.next] at h
  | done => simp [TState.next] at h
  | ready =>
    cases ops with
    | nil => simp [TState.next] at h
    | cons c rest =>
      cases c with
      | lock l' =>
        simp only [TState.next] at h
        split_ifs at h with h0 hv
        simp only [TPhase.acquire.injEq] at h
        subst h
        exact ⟨rfl, h0, hv, Or.inl ⟨rest, rfl⟩⟩
      | tryLock l' k =>
        simp only [TState.next] at h
        split_ifs at h with h0 hv
        simp only [TPhase.acquire.injEq] at h
        subst h
        exact ⟨rfl, h0, hv, Or.inr ⟨k, rest, rfl⟩⟩
      | unlock l' => simp only [TState.next] at h; split_ifs at h
      | join u => simp only [TState.next] at h; split_ifs at h
      | assume x w => simp only [TState.next] at h; split_ifs at h
      | rd x => simp [TState.next] at h
      | wr x v' => simp [TState.next] at h
      | start u => simp [TState.next] at h

theorem act_of_phase_acquire {s : TState} (h : s.phase = .acquire l) :
    s.act P.st t = some (.write l 1) := by
  rcases s with ⟨o, hd, p⟩
  simp only at h
  subst h
  rfl


end bodyFree


section body

variable (hF : Frag P) {t : Tid} (ht : t ∈ P.threads) {l : Loc} (hl : P.isLock l = true)
include hF ht hl

/-- The writes of a lock location by a body: the write of an acquire (`1`), or the release
by a holder of count `1` (`0`). -/
theorem act_write_lock {s : TState} (hs : Inv P t s) {v : Val}
    (ha : s.act P.st t = some (.write l v)) :
    (s.phase = .acquire l ∧ v = 1) ∨ (s.phase = .ready ∧ s.holds l = 1 ∧ v = 0) := by
  obtain ⟨hops, -⟩ := hs
  rcases s with ⟨ops, holds, ph⟩
  cases ph with
  | acquire l' =>
    simp only [TState.act, Option.some.injEq, Act.write.injEq] at ha
    obtain ⟨h1, h2⟩ := ha
    subst h1
    exact Or.inl ⟨rfl, h2.symm⟩
  | blocking => simp [TState.act] at ha
  | done => simp [TState.act] at ha
  | ready =>
    cases ops with
    | nil =>
      simp only [TState.act, Option.some.injEq, Act.write.injEq] at ha
      rw [← ha.1, hF.st_not_lock t ht] at hl
      cases hl
    | cons c rest =>
      have hok := hF.calls t ht c (hops c (by simp))
      cases c with
      | lock l' => simp only [TState.act] at ha; split_ifs at ha <;> simp at ha
      | tryLock l' k => simp only [TState.act] at ha; split_ifs at ha <;> simp at ha
      | unlock l' =>
        simp only [TState.act] at ha
        split_ifs at ha with h0 h1
        · simp at ha
        · simp only [Option.some.injEq, Act.write.injEq] at ha
          obtain ⟨h2, h3⟩ := ha
          subst h2
          exact Or.inr ⟨rfl, h1, h3.symm⟩
        · simp at ha
      | rd x => simp [TState.act] at ha
      | wr x v' =>
        simp only [TState.act, Option.some.injEq, Act.write.injEq] at ha
        have : P.isData x = true := by simpa [callOk] using hok
        rw [ha.1] at this
        simp [LProg.isData, hl] at this
      | start u =>
        simp only [TState.act, Option.some.injEq, Act.write.injEq] at ha
        simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        rw [← ha.1, hF.st_not_lock u hok.1.1] at hl
        cases hl
      | join u => simp [TState.act] at ha
      | assume x w => simp [TState.act] at ha

/-- One step: if the body holds `l` afterwards, it has just written its acquire, or it
held `l` before and the step was not the release write. -/
theorem holds_next {s : TState} (hs : Inv P t s) {v : Option Val}
    (h : 0 < (s.next v).holds l) :
    s.phase = .acquire l ∨ (0 < s.holds l ∧ s.act P.st t ≠ some (.write l 0)) := by
  obtain ⟨hops, -⟩ := hs
  rcases s with ⟨ops, holds, ph⟩
  cases ph with
  | acquire l' =>
    by_cases hll : l' = l
    · exact Or.inl (by rw [hll])
    · right
      simp only [TState.next] at h
      rw [Function.update_of_ne (Ne.symm hll)] at h
      exact ⟨h, by simp [TState.act, hll]⟩
  | blocking => exact Or.inr ⟨h, by simp [TState.act]⟩
  | done => exact Or.inr ⟨h, by simp [TState.act]⟩
  | ready =>
    right
    cases ops with
    | nil =>
      refine ⟨h, ?_⟩
      simp only [TState.act, ne_eq, Option.some.injEq, Act.write.injEq, not_and]
      intro h'
      rw [← h', hF.st_not_lock t ht] at hl
      cases hl
    | cons c rest =>
      have hok := hF.calls t ht c (hops c (by simp))
      cases c with
      | lock l' =>
        simp only [TState.next] at h
        by_cases h0 : holds l' = 0
        · simp only [h0, ↓reduceIte] at h
          refine ⟨by split_ifs at h <;> exact h, by simp [TState.act, h0]⟩
        · simp only [h0, ↓reduceIte] at h
          refine ⟨?_, by simp [TState.act, h0]⟩
          by_cases hll : l' = l
          · subst hll; simp at h ⊢; omega
          · rwa [Function.update_of_ne (Ne.symm hll)] at h
      | tryLock l' k =>
        simp only [TState.next] at h
        by_cases h0 : holds l' = 0
        · simp only [h0, ↓reduceIte] at h
          refine ⟨by split_ifs at h <;> exact h, by simp [TState.act, h0]⟩
        · simp only [h0, ↓reduceIte] at h
          refine ⟨?_, by simp [TState.act, h0]⟩
          by_cases hll : l' = l
          · subst hll; simp at h ⊢; omega
          · rwa [Function.update_of_ne (Ne.symm hll)] at h
      | unlock l' =>
        simp only [TState.next] at h
        by_cases h0 : holds l' = 0
        · simp only [h0, ↓reduceIte] at h
          exact ⟨h, by simp [TState.act, h0]⟩
        · simp only [h0, ↓reduceIte] at h
          by_cases hll : l' = l
          · subst hll
            rw [Function.update_self] at h
            have h1 : holds l' ≠ 1 := by omega
            exact ⟨by change 0 < holds l'; omega, by simp [TState.act, h0, h1]⟩
          · rw [Function.update_of_ne (Ne.symm hll)] at h
            refine ⟨h, ?_⟩
            by_cases h1 : holds l' = 1
            · simp [TState.act, h1, hll]
            · simp [TState.act, h0, h1]
      | rd x => exact ⟨by simpa [TState.next] using h, by simp [TState.act]⟩
      | wr x v' =>
        refine ⟨by simpa [TState.next] using h, ?_⟩
        simp only [TState.act, ne_eq, Option.some.injEq, Act.write.injEq, not_and]
        intro hx
        have : P.isData x = true := by simpa [callOk] using hok
        rw [hx] at this
        simp [LProg.isData, hl] at this
      | start u =>
        refine ⟨by simpa [TState.next] using h, ?_⟩
        simp only [TState.act, ne_eq, Option.some.injEq, Act.write.injEq, not_and]
        intro hx
        simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        rw [← hx, hF.st_not_lock u hok.1.1] at hl
        cases hl
      | join u =>
        simp only [TState.next] at h
        refine ⟨by split_ifs at h <;> exact h, by simp [TState.act]⟩
      | assume x w =>
        simp only [TState.next] at h
        refine ⟨by split_ifs at h <;> exact h, by simp [TState.act]⟩

/-- A body that holds `l` after a trace entered `acquire l` at an earlier position and has
not written a release since. -/
theorem tState_holds_pos (u : List (Option Val)) (h : 0 < (tState (P.code t) u).holds l) :
    ∃ j < u.length, (tState (P.code t) (u.take j)).phase = .acquire l ∧
      ∀ k, j < k → k < u.length →
        (tState (P.code t) (u.take k)).act P.st t ≠ some (.write l 0) := by
  induction u using List.reverseRecOn with
  | nil => simp [tState, TState.init] at h
  | append_singleton u v ih =>
    rw [tState_append] at h
    rcases holds_next hF ht hl (inv_tState hF ht u) h with hacq | ⟨hpos, hact⟩
    · refine ⟨u.length, by simp, by simpa using hacq, fun k h1 h2 => ?_⟩
      simp only [List.length_append, List.length_singleton] at h2
      omega
    · obtain ⟨j, hj, hjp, hbet⟩ := ih hpos
      refine ⟨j, by simp; omega, ?_, fun k h1 h2 => ?_⟩
      · rw [List.take_append_of_le_length (Nat.le_of_lt hj)]
        exact hjp
      · simp only [List.length_append, List.length_singleton] at h2
        by_cases hk : k < u.length
        · rw [List.take_append_of_le_length (Nat.le_of_lt hk)]
          exact hbet k h1 hk
        · have hku : k = u.length := by omega
          rw [hku, List.take_append_of_le_length le_rfl, List.take_length]
          exact hact

omit hl in
/-- A positive hold count stays positive along an extension without a release write. -/
theorem tState_holds_persist (u w : List (Option Val)) (h : 0 < (tState (P.code t) u).holds l)
    (hno : ∀ k, u.length ≤ k → k < (u ++ w).length →
      (tState (P.code t) ((u ++ w).take k)).act P.st t ≠ some (.write l 0)) :
    0 < (tState (P.code t) (u ++ w)).holds l := by
  induction w using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton w v ih =>
    rw [← List.append_assoc] at hno ⊢
    rw [tState_append]
    have ih' := ih (fun k h1 h2 => by
      have := hno k h1 (by simp at h2 ⊢; omega)
      rwa [List.take_append_of_le_length (Nat.le_of_lt h2)] at this)
    apply holds_next_pos (inv_tState hF ht _) ih'
    have := hno (u ++ w).length (by simp) (by simp)
    rwa [List.take_append_of_le_length le_rfl, List.take_length] at this

end body

/-! ### The body inside the trace -/

/-- The part of a trace before the body: empty for a root; for a non-root thread, the value
of its start-read, which is not `0`. -/
def BodyPre (P : LProg) (t : Tid) (pre : List (Option Val)) : Prop :=
  (P.isRoot t = true ∧ pre = []) ∨ (P.isRoot t = false ∧ ∃ v0, pre = [v0] ∧ v0 ≠ some 0)

theorem BodyPre.tab {t : Tid} {pre : List (Option Val)} (h : BodyPre P t pre)
    (X : List (Option Val)) : lifeTab P t (pre ++ X) = (tState (P.code t) X).act P.st t := by
  rcases h with ⟨hr, rfl⟩ | ⟨hr, v0, rfl, hv⟩
  · simp [lifeTab_root hr]
  · simp [lifeTab_cons hr hv]

theorem BodyPre.flag {t : Tid} {pre : List (Option Val)} (h : BodyPre P t pre)
    (X : List (Option Val)) : lifeFlag P t (pre ++ X) = (tState (P.code t) X).isEx := by
  rcases h with ⟨hr, rfl⟩ | ⟨hr, v0, rfl, hv⟩
  · simp [lifeFlag, hr]
  · simp [lifeFlag, hr, hv]

theorem BodyPre.holds {t : Tid} {pre : List (Option Val)} (h : BodyPre P t pre)
    (X : List (Option Val)) (l : Loc) :
    holdsOf P t (pre ++ X) l = (tState (P.code t) X).holds l := by
  rcases h with ⟨hr, rfl⟩ | ⟨hr, v0, rfl, hv⟩
  · simp [holdsOf, hr]
  · simp [holdsOf, hr, hv]

theorem BodyPre.length_le {t : Tid} {pre : List (Option Val)} (h : BodyPre P t pre) :
    pre.length ≤ 1 := by
  rcases h with ⟨-, rfl⟩ | ⟨-, v0, rfl, -⟩ <;> simp

/-- A positive hold count comes from a body trace. -/
theorem holdsOf_pos {t : Tid} {T : List (Option Val)} {l : Loc} (h : 0 < holdsOf P t T l) :
    ∃ pre B, BodyPre P t pre ∧ T = pre ++ B ∧ 0 < (tState (P.code t) B).holds l := by
  unfold holdsOf at h
  by_cases hr : P.isRoot t = true
  · simp only [hr, ↓reduceIte] at h
    exact ⟨[], T, Or.inl ⟨hr, rfl⟩, rfl, h⟩
  · have hr' : P.isRoot t = false := by simpa using hr
    simp only [hr', Bool.false_eq_true, ↓reduceIte] at h
    cases T with
    | nil => simp at h
    | cons v rest =>
      by_cases hv : v = some 0
      · simp [hv] at h
      · simp only [hv, ↓reduceIte] at h
        exact ⟨[v], rest, Or.inr ⟨hr', v, rfl, hv⟩, rfl, h⟩

/-! ### Graph level -/

section graph

variable {G : Graph}

theorem mem_lock (hF : Frag P) {l : Loc} (hl : P.isLock l = true) : lifeMem P l = 0 := by
  unfold lifeMem
  have : P.roots.any (fun r => decide (P.st r = l)) = false := by
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨r, hr, hrl⟩ := List.any_eq_true.mp h
    simp only [decide_eq_true_eq] at hrl
    rw [← hrl, hF.st_not_lock r (hF.roots_sub r hr)] at hl
    cases hl
  simp [this]

/-- A write of a lock by thread `t`: the trace of `t` has a body part. -/
theorem bodyPre_of_write (hG : G.Wf) (hE : (lifeSys P n).toProgram.Exec G) {e : TEv}
    (he : e ∈ G.events) {x : Loc} {v : Val} (hact : e.act = .write x v) :
    ∃ pre, BodyPre P e.tid pre ∧ pre.length ≤ e.idx ∧ (G.trace e.tid).take pre.length = pre := by
  by_cases hr : P.isRoot e.tid = true
  · exact ⟨[], Or.inl ⟨hr, rfl⟩, Nat.zero_le _, by simp⟩
  · have hr' : P.isRoot e.tid = false := by simpa using hr
    have h1 : 1 ≤ e.idx := by
      by_contra h0
      have h0' : e.idx = 0 := by omega
      obtain ⟨e1, -, -⟩ := ev_tab hE he
      rw [h0', show G.traceBefore e.tid 0 = [] by simp [Graph.traceBefore], lifeTab_nil hr',
        hact] at e1
      cases e1
    obtain ⟨r0, hr0, ht0, hi0, -, rest, htr⟩ := start_read hG hE he hr' h1
    have hv0 : G.ret r0 ≠ some 0 := by
      intro h0
      obtain ⟨h1', h2'⟩ := start_wait_events hG hE hr0 (by rw [ht0]; exact hr') hi0 h0 he ht0.symm
      rw [h2' (by omega)] at hact
      cases hact
    refine ⟨[G.ret r0], Or.inr ⟨hr', _, rfl, hv0⟩, by simp; omega, ?_⟩
    have hc := hG.idx_lt_cnt he
    rw [List.length_singleton, ← Graph.traceBefore_eq_take G e.tid (by omega),
      ← traceBefore_take G e.tid h1, htr]
    simp

/-- The trace before position `i` (at or after the body starts) is the part before the
body and a prefix of the body. -/
theorem trace_split {t : Tid} {pre : List (Option Val)}
    (hpre : (G.trace t).take pre.length = pre) {i : ℕ} (h1 : pre.length ≤ i)
    (h2 : i ≤ G.cnt t) :
    G.traceBefore t i = pre ++ ((G.trace t).drop pre.length).take (i - pre.length) := by
  have hl : pre.length ≤ (G.trace t).length := by rw [Graph.trace_length]; omega
  rw [Graph.traceBefore_eq_take G t h2]
  conv_lhs => rw [← List.take_append_drop pre.length (G.trace t), hpre]
  rw [List.take_append, List.take_of_length_le h1]

/-- The action of an event at or after the start of the body is the body's action. -/
theorem act_body (hE : (lifeSys P n).toProgram.Exec G) {t : Tid} {pre : List (Option Val)}
    (hb : BodyPre P t pre) (hpre : (G.trace t).take pre.length = pre) {q : TEv}
    (hq : q ∈ G.events) (hqt : q.tid = t) (hq1 : pre.length ≤ q.idx) (hG : G.Wf) :
    (tState (P.code t) (((G.trace t).drop pre.length).take (q.idx - pre.length))).act P.st t =
      some q.act := by
  obtain ⟨h, -, -⟩ := ev_tab hE hq
  rw [hqt, trace_split hpre hq1 (by rw [← hqt]; exact Nat.le_of_lt (hG.idx_lt_cnt hq)),
    hb.tab] at h
  exact h

/-- The body trace grows by the value of each body event. -/
theorem body_take_succ (hG : G.Wf) {t : Tid} {pre : List (Option Val)}
    (hpre : (G.trace t).take pre.length = pre) {q : TEv} (hq : q ∈ G.events) (hqt : q.tid = t)
    (hq1 : pre.length ≤ q.idx) :
    ((G.trace t).drop pre.length).take (q.idx + 1 - pre.length) =
      ((G.trace t).drop pre.length).take (q.idx - pre.length) ++ [G.ret q] := by
  have hc : q.idx < G.cnt t := hqt ▸ hG.idx_lt_cnt hq
  have h1 := trace_split hpre (by omega : pre.length ≤ q.idx + 1) (by omega)
  have h2 := trace_split hpre hq1 (by omega)
  have h3 := Graph.traceBefore_succ G t q.idx
  rw [h1, h2, Graph.evAt_eq_some_of_inj' hG.idx_inj hq hqt rfl] at h3
  simpa using h3

section lock

variable (hF : Frag P) (hG : G.Wf) (hE : (lifeSys P n).toProgram.Exec G) {l : Loc}
  (hl : P.isLock l = true)
include hF hG hE hl

/-- **The writes of a lock behave as a lock** (`LockLike`), in an atomic execution. -/
theorem lifeSys_lockLike (hat : (lifeSys P n).Atomic G) : LockLike G l := by
  -- the body view of a write of `l`
  have view : ∀ w ∈ G.co l, ∃ v pre, w.act = .write l v ∧ BodyPre P w.tid pre ∧
      pre.length ≤ w.idx ∧ (G.trace w.tid).take pre.length = pre ∧ w ∈ G.events ∧
      w.tid ∈ P.threads ∧
      (tState (P.code w.tid) (((G.trace w.tid).drop pre.length).take (w.idx - pre.length))).act
        P.st w.tid = some (.write l v) := by
    intro w hw
    obtain ⟨hwE, v, hv⟩ := (hG.co_mem l w).mp hw
    obtain ⟨pre, hb, hle, hpre⟩ := bodyPre_of_write hG hE hwE hv
    refine ⟨v, pre, hv, hb, hle, hpre, hwE, (ev_tab hE hwE).2.2, ?_⟩
    rw [act_body hE hb hpre hwE rfl hle hG, hv]
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, pre, hv, -, -, -, -, ht, ha⟩ := view w hw
    rw [valAt_th hv]
    rcases act_write_lock hF ht hl (inv_tState hF ht _) ha with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  · intro w hw hw1
    obtain ⟨v, pre, hv, hb, hle, hpre, hwE, ht, ha⟩ := view w hw
    rw [valAt_th hv] at hw1
    subst hw1
    set B := (G.trace w.tid).drop pre.length with hB
    have hph : (tState (P.code w.tid) (B.take (w.idx - pre.length))).phase = .acquire l := by
      rcases act_write_lock hF ht hl (inv_tState hF ht _) ha with ⟨h1, -⟩ | ⟨-, -, h1⟩
      · exact h1
      · cases h1
    -- the read before the write
    have hj : pre.length < w.idx := by
      by_contra h
      have : w.idx - pre.length = 0 := by omega
      rw [this] at hph
      simp [tState, TState.init] at hph
    obtain ⟨r, hr, hrt, hri⟩ := hG.idx_contig w hwE (w.idx - 1) (by omega)
    have hri' : w.idx = r.idx + 1 := by omega
    have hsucc := body_take_succ hG hpre hr hrt (by omega)
    rw [← hri', ← hB] at hsucc
    rw [hsucc, tState_append] at hph
    set S' := tState (P.code w.tid) (B.take (r.idx - pre.length)) with hS'
    have hne : S'.phase ≠ .acquire l := by
      intro h'
      rcases hs : S' with ⟨o, h, p⟩
      rw [hs] at h' hph
      simp only at h'
      subst h'
      simp [TState.next] at hph
    obtain ⟨hready, h0, hret, hops⟩ := acquire_of_next hph hne
    have hSact : S'.act P.st w.tid = some (.read l) := by
      rcases hops with ⟨rest, hops⟩ | ⟨k, rest, hops⟩
      · rw [act_ready_cons hready hops]; simp [TState.act, h0]
      · rw [act_ready_cons hready hops]; simp [TState.act, h0]
    have hSex : S'.isEx = true := by
      rcases hops with ⟨rest, hops⟩ | ⟨k, rest, hops⟩
      · simp [TState.isEx, hready, hops, h0]
      · simp [TState.isEx, hready, hops, h0]
    have hract : r.act = .read l := by
      have := act_body hE hb hpre hr hrt (by omega) hG
      rw [← hS', hSact] at this
      exact (Option.some.inj this).symm
    -- traces and flags
    have htr_r : G.traceBefore w.tid r.idx = pre ++ B.take (r.idx - pre.length) :=
      trace_split hpre (by omega) (by have := hG.idx_lt_cnt hr; rw [hrt] at this; omega)
    have htr_w : G.traceBefore w.tid w.idx = pre ++ B.take (w.idx - pre.length) :=
      trace_split hpre hle (Nat.le_of_lt (hG.idx_lt_cnt hwE))
    have hstep_r := hE.2 r hr
    rw [hrt, hract] at hstep_r
    have hstep_w := hE.2 w hwE
    rw [hv] at hstep_w
    have hflag_r : lifeFlag P w.tid (G.traceBefore w.tid r.idx) = true := by
      rw [htr_r, hb.flag, ← hS']; exact hSex
    have hflag_w : lifeFlag P w.tid (G.traceBefore w.tid w.idx) = true := by
      rw [htr_w, hb.flag, hsucc, tState_append, ← hS']
      simp [TState.isEx, hph]
    have hlast : G.traceBefore w.tid w.idx = G.traceBefore w.tid r.idx ++ [some 0] := by
      rw [htr_w, htr_r, hsucc, ← hret]; simp
    have hrmw : (lifeSys P n).RMW G r w := by
      refine ⟨hr, hwE, hrt.symm, hri', by simp [TEv.IsRead, hract, Act.IsRead],
        by simp [TEv.IsWrite, hv, Act.IsWrite], ?_, ?_⟩
      · change exFlag (lifeSys P n).toProgram.step (lifeFlag P) r.tid
          (G.traceBefore r.tid r.idx) = true
        rw [hrt]
        unfold exFlag
        rw [hstep_r]
        exact hflag_r
      · change exFlag (lifeSys P n).toProgram.step (lifeFlag P) w.tid
          (G.traceBefore w.tid w.idx) = true
        unfold exFlag
        rw [hstep_w, hflag_w]
        rw [hlast]
        simp only [List.getLast?_concat, List.dropLast_concat, Bool.true_and]
        rw [hstep_r, hflag_r]
        simp
    obtain ⟨s, hs, -⟩ := hG.rf_read r hr l hract
    have hloc : w.loc = l := by simp [TEv.loc, hv, Act.loc]
    refine ⟨s, hloc ▸ hat r w hrmw s hs, ?_⟩
    have : G.ret r = some (G.valAt l s) := by
      unfold Graph.ret
      rw [hract, hs]
      rfl
    rw [this] at hret
    exact Option.some.inj hret
  · intro w hw hw0
    obtain ⟨v, pre, hv, hb, hle, hpre, hwE, ht, ha⟩ := view w hw
    rw [valAt_th hv] at hw0
    subst hw0
    set B := (G.trace w.tid).drop pre.length
    have hholds : (tState (P.code w.tid) (B.take (w.idx - pre.length))).holds l = 1 := by
      rcases act_write_lock hF ht hl (inv_tState hF ht _) ha with ⟨-, h1⟩ | ⟨-, h1, -⟩
      · cases h1
      · exact h1
    obtain ⟨j, hj, hjp, hbet⟩ := tState_holds_pos hF ht hl _ (by rw [hholds]; exact Nat.one_pos)
    have hlenB : (B.take (w.idx - pre.length)).length = w.idx - pre.length := by
      simp only [List.length_take, B, List.length_drop, Graph.trace_length]
      have := hG.idx_lt_cnt hwE
      omega
    rw [hlenB] at hj hbet
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hj)] at hjp
    obtain ⟨a, haE, hat', hai⟩ := hG.idx_contig w hwE (j + pre.length) (by omega)
    have haact : a.act = .write l 1 := by
      have := act_body hE hb hpre haE hat' (by omega) hG
      rw [hai, Nat.add_sub_cancel] at this
      rw [act_of_phase_acquire hjp] at this
      exact (Option.some.inj this).symm
    refine ⟨a, (hG.co_mem l a).mpr ⟨haE, 1, haact⟩, valAt_th haact, hat', by omega, ?_⟩
    intro w' hw' hw'0 hw't ⟨h1, h2⟩
    obtain ⟨hw'E, v', hv'⟩ := (hG.co_mem l w').mp hw'
    rw [valAt_th hv'] at hw'0
    subst hw'0
    have := act_body hE hb hpre hw'E hw't (by omega) hG
    rw [hv'] at this
    refine hbet (w'.idx - pre.length) (by omega) (by omega) ?_
    rw [List.take_take, Nat.min_eq_left (by omega)]
    exact this

/-- **Mutual exclusion**: the coherence order of a lock alternates between an acquire (`1`)
by a thread and the release (`0`) by that thread, starting with an acquire. -/
theorem lifeSys_mutex (hc : (Model.atomic (lifeSys P n) SC).cons G) :
    ∀ i (hi : i < (G.co l).length),
      (i % 2 = 0 → G.valAt l (.th (G.co l)[i]) = 1) ∧
      (i % 2 = 1 → G.valAt l (.th (G.co l)[i]) = 0 ∧
        ∃ hi' : i - 1 < (G.co l).length, (G.co l)[i].tid = (G.co l)[i - 1].tid) :=
  (lifeSys_lockLike hF hG hE hl hc.2).alternates hG hc.1

/-- **The lock invariant** (§4, draft 4.2): the value of a lock location (that of its
coherence-maximal write, or the initial `0`) is `0` iff no thread's compiled hold count of
it after its trace is positive. -/
theorem lock_value_iff (hc : (Model.atomic (lifeSys P n) SC).cons G) :
    G.valAt l (G.maxWrite l) = 0 ↔ ∀ t ∈ P.threads, holdsOf P t (G.trace t) l = 0 := by
  have hsc : Maz.Acyclic G.scStep := hc.1
  have halt := lifeSys_mutex hF hG hE hl hc
  have hnd := hG.co_nodup l
  constructor
  · intro h0 t ht
    by_contra hpos
    obtain ⟨pre, B, hb, hT, hB⟩ := holdsOf_pos (Nat.pos_of_ne_zero hpos)
    obtain ⟨j, hj, hjp, hbet⟩ := tState_holds_pos hF ht hl B hB
    have hpre : (G.trace t).take pre.length = pre := by rw [hT]; simp
    have hBd : (G.trace t).drop pre.length = B := by rw [hT]; simp
    have hcnt : G.cnt t = pre.length + B.length := by rw [← Graph.trace_length, hT]; simp
    obtain ⟨a, haE, hat, hai⟩ := (hG.exists_idx_iff t (pre.length + j)).mpr (by omega)
    have haact : a.act = .write l 1 := by
      have := act_body hE hb hpre haE hat (by omega) hG
      rw [hai, hBd, show pre.length + j - pre.length = j by omega,
        act_of_phase_acquire hjp] at this
      exact (Option.some.inj this).symm
    have haco : a ∈ G.co l := (hG.co_mem l a).mpr ⟨haE, 1, haact⟩
    have hi := List.idxOf_lt_length_of_mem haco
    have hLi : (G.co l)[(G.co l).idxOf a] = a := List.getElem_idxOf hi
    have hval1 : G.valAt l (.th a) = 1 := valAt_th haact
    have heven : (G.co l).idxOf a % 2 = 0 := by
      by_contra hodd
      have := ((halt _ hi).2 (by omega)).1
      rw [hLi, hval1] at this
      cases this
    have hlast : (G.co l).idxOf a + 1 = (G.co l).length := by
      by_contra hne
      have hi1 : (G.co l).idxOf a + 1 < (G.co l).length := by omega
      obtain ⟨hv0, hi', htid⟩ := (halt _ hi1).2 (by omega)
      simp only [Nat.add_sub_cancel] at htid
      rw [hLi] at htid
      have hw'co : (G.co l)[(G.co l).idxOf a + 1] ∈ G.co l := List.getElem_mem hi1
      have hbef : (G.co l).Before a (G.co l)[(G.co l).idxOf a + 1] := by
        have := (List.before_getElem_iff hnd hi hi1).mpr (Nat.lt_succ_self _)
        rwa [hLi] at this
      generalize (G.co l)[(G.co l).idxOf a + 1] = w' at hv0 htid hw'co hbef
      obtain ⟨hw'E, v', hv'⟩ := (hG.co_mem l w').mp hw'co
      rw [valAt_th hv'] at hv0
      subst hv0
      rcases Nat.lt_trichotomy w'.idx a.idx with hlt | heq | hgt
      · exact Graph.not_before_of_po hG hsc hw'co haco htid hlt hbef
      · have := hG.idx_inj w' hw'E a haE htid heq
        rw [this, haact] at hv'
        simp at hv'
      · have hk := act_body hE hb hpre hw'E (htid.trans hat) (by omega) hG
        rw [hBd, hv'] at hk
        have hw'c : w'.idx < G.cnt t := by
          have := hG.idx_lt_cnt hw'E
          rwa [htid, hat] at this
        exact hbet (w'.idx - pre.length) (by omega) (by omega) hk
    have hmw : G.maxWrite l = .th a := by
      unfold Graph.maxWrite
      rw [List.getLast?_eq_getElem?, show (G.co l).length - 1 = (G.co l).idxOf a by omega,
        List.getElem?_eq_getElem hi, hLi]
    rw [hmw, hval1] at h0
    cases h0
  · intro hall
    by_contra hne0
    by_cases hemp : G.co l = []
    · apply hne0
      unfold Graph.maxWrite
      rw [hemp]
      simp [Graph.valAt, mem_eq hE, mem_lock hF hl]
    · have hk : (G.co l).length - 1 < (G.co l).length := by
        have := List.length_pos_of_ne_nil hemp
        omega
      have hmw : G.maxWrite l = .th (G.co l)[(G.co l).length - 1] := by
        unfold Graph.maxWrite
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hk]
      have hlastEq : (G.co l)[(G.co l).length - 1] = (G.co l).getLast hemp :=
        (List.getLast_eq_getElem hemp).symm
      generalize ha : (G.co l)[(G.co l).length - 1] = a at hmw hlastEq
      have haco : a ∈ G.co l := by rw [← ha]; exact List.getElem_mem hk
      have hva : G.valAt l (.th a) ≠ 0 := by rw [← hmw]; exact hne0
      have heven : ((G.co l).length - 1) % 2 = 0 := by
        by_contra hodd
        have := ((halt _ hk).2 (by omega)).1
        rw [ha] at this
        exact hva this
      have hv1 := (halt _ hk).1 heven
      rw [ha] at hv1
      obtain ⟨haE, v, hv⟩ := (hG.co_mem l a).mp haco
      rw [valAt_th hv] at hv1
      subst hv1
      have ht : a.tid ∈ P.threads := (ev_tab hE haE).2.2
      obtain ⟨pre, hb, hle, hpre⟩ := bodyPre_of_write hG hE haE hv
      set B := (G.trace a.tid).drop pre.length with hB
      have hcnt : G.cnt a.tid = pre.length + B.length := by
        rw [hB, List.length_drop, Graph.trace_length]
        have := hG.idx_lt_cnt haE
        omega
      have hact := act_body hE hb hpre haE rfl hle hG
      rw [← hB, hv] at hact
      have hph : (tState (P.code a.tid) (B.take (a.idx - pre.length))).phase = .acquire l := by
        rcases act_write_lock hF ht hl (inv_tState hF ht _) hact with ⟨h1, -⟩ | ⟨-, -, h1⟩
        · exact h1
        · cases h1
      have hsucc := body_take_succ hG hpre haE rfl hle
      rw [← hB] at hsucc
      have h1 : 0 < (tState (P.code a.tid) (B.take (a.idx + 1 - pre.length))).holds l := by
        rw [hsucc, tState_append, holds_after_acquire hph]
        exact Nat.one_pos
      have hpers := tState_holds_persist hF ht (B.take (a.idx + 1 - pre.length))
        (B.drop (a.idx + 1 - pre.length)) h1 (by
          intro k hk1 hk2 hrel
          rw [List.take_append_drop] at hk2 hrel
          rw [List.length_take] at hk1
          obtain ⟨w', hw'E, hw't, hw'i⟩ :=
            (hG.exists_idx_iff a.tid (pre.length + k)).mpr (by omega)
          have hk3 := act_body hE hb hpre hw'E hw't (by omega) hG
          rw [← hB, hw'i, show pre.length + k - pre.length = k by omega, hrel] at hk3
          have hw'a : w'.act = .write l 0 := (Option.some.inj hk3).symm
          have hw'co : w' ∈ G.co l := (hG.co_mem l w').mpr ⟨hw'E, 0, hw'a⟩
          have hne : a ≠ w' := by intro h; rw [← h, hv] at hw'a; simp at hw'a
          have hlt : a.idx < w'.idx := by
            have := Nat.min_le_left (a.idx + 1 - pre.length) B.length
            omega
          rcases List.Before.total haco hw'co hne with hab | hba
          · rw [hlastEq] at hab
            exact List.not_before_getLast hnd hemp _ hab
          · exact Graph.not_before_of_po hG hsc haco hw'co hw't.symm hlt hba)
      rw [List.take_append_drop] at hpers
      have hT : G.trace a.tid = pre ++ B := by
        rw [hB]
        conv_lhs => rw [← List.take_append_drop pre.length (G.trace a.tid), hpre]
      have := hall a.tid ht
      rw [hT, hb.holds] at this
      omega

end lock

end graph

end Life

end Condpor
