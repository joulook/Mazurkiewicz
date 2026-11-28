import Mazurkiewicz.Condpor.Rmw.LifecycleGateEmit
import Mazurkiewicz.Condpor.Rmw.LifecycleLock

/-!
# Gate clause 1: the simulation invariant (LC2-b, part 6)

`SInv P n s g` relates a machine state `s` reached by a run and the builder `g` of that run:

* `ok`, `minv`, `exec`: `GB.Ok`, `MInv`, `ExecT`;
* `noStart`: once a non-root thread is started, no thread has a `start` of it left;
* `newRoot`: roots are never new;
* `lockInv`;
* `vData`, `vLock`, `vLife`: the value of the last write of a data, lock, lifecycle location
  is the data memory, `count ≠ 0`, the lifecycle status (0 not started, 1 started, 2 ended);
* `rel`: per listed thread `TRel`: new: no event yet, the code untouched, no lock owned;
  running: not stopped, and the compiled body state after its values is
  `⟨rest, holdsM, ready⟩`; terminated: no compiled action left; erred or assume-stopped:
  stopped.

`sinv_init`: it holds initially.
-/

namespace Condpor

namespace Life

namespace Sem

variable {P : LProg}


/-- The compiled body state after the values `u` of thread `t` is `st` (for a non-root thread,
after a start-read that did not return `0`). -/
def BodyAt (P : LProg) (t : Tid) (u : List (Option Val)) (st : TState) : Prop :=
  if P.isRoot t then tState (P.code t) u = st
  else ∃ v w, u = v :: w ∧ v ≠ some 0 ∧ tState (P.code t) w = st

theorem lifeTab_of_bodyAt {t : Tid} {u : List (Option Val)} {st : TState}
    (h : BodyAt P t u st) : lifeTab P t u = st.act P.st t := by
  unfold BodyAt at h
  split_ifs at h with hr
  · rw [lifeTab_root hr, h]
  · obtain ⟨v, w, rfl, hv, hw⟩ := h
    rw [lifeTab_cons (by simpa using hr) hv, hw]

theorem bodyAt_append {t : Tid} {u : List (Option Val)} {st : TState} (h : BodyAt P t u st)
    (v : Option Val) : BodyAt P t (u ++ [v]) (st.next v) := by
  unfold BodyAt at h ⊢
  split_ifs at h ⊢ with hr
  · rw [tState_append, h]
  · obtain ⟨v0, w, rfl, hv, hw⟩ := h
    exact ⟨v0, w ++ [v], rfl, hv, by rw [tState_append, hw]⟩

/-- The relation between a thread of the machine and its values in the graph. -/
def TRel (P : LProg) (s : MState) (t : Tid) (u : List (Option Val)) : Prop :=
  match s.status t with
  | .new => u = [] ∧ s.rest t = P.code t ∧ ∀ l, s.owner l ≠ some t
  | .running => stopped (lifeTab P) t u = false ∧ BodyAt P t u ⟨s.rest t, holdsM s t, .ready⟩
  | .term => lifeTab P t u = none
  | _ => stopped (lifeTab P) t u = true

/-- The simulation invariant. -/
structure SInv (P : LProg) (n : ℕ) (s : MState) (g : GB) : Prop where
  ok : g.Ok
  minv : MInv P s g
  exec : ExecT P n g
  noStart : ∀ u, ∀ t ∈ P.threads, s.started u = true → P.isRoot u = false →
    TOp.start u ∉ s.rest t
  newRoot : ∀ t, P.isRoot t = true → s.status t ≠ .new
  lockInv : LockInv s
  vData : ∀ x, P.isData x = true → valE P x (g.last x) = s.mem x
  vLock : ∀ l, P.isLock l = true → valE P l (g.last l) = if s.count l = 0 then 0 else 1
  vLife : ∀ t ∈ P.threads, valE P (P.st t) (g.last (P.st t)) =
    if s.started t then (if s.status t = .term then 2 else 1) else 0
  rel : ∀ t ∈ P.threads, TRel P s t (tr P g t)

theorem tr_empty (t : Tid) : tr P GB.empty t = [] := by simp [tr, thr, GB.L, GB.empty]

theorem sinv_init (hF : Frag P) (n : ℕ) : SInv P n (MState.init P) GB.empty where
  ok := ok_empty
  minv := minv_init P
  exec := by intro t j h; simp [thr, GB.L, GB.empty] at h
  noStart := by
    intro u t _ h hr
    have h' : P.isRoot u = true := h
    rw [h'] at hr; cases hr
  newRoot := by intro t hr; simp [MState.init, hr]
  lockInv := lockInv_init
  vData := by intro x _; simp [GB.last, GB.empty, valE, MState.init]
  vLock := by intro l hl; simp [GB.last, GB.empty, valE, MState.init, mem_lock hF hl]
  vLife := by
    intro t ht
    simp only [GB.last, GB.empty, List.getLast?_nil, valE, MState.init, hF.mem_st ht]
    by_cases hr : P.isRoot t = true <;> simp [hr]
  rel := by
    intro t ht
    rw [tr_empty]
    unfold TRel
    by_cases hr : P.isRoot t = true
    · simp only [MState.init, hr, ↓reduceIte]
      refine ⟨by simp [stopped], ?_⟩
      simp only [BodyAt, hr, ↓reduceIte, tState, List.foldl_nil, TState.init]
      congr 1
    · simp only [MState.init, hr, Bool.false_eq_true, ↓reduceIte]
      simp

end Sem

end Life

end Condpor

namespace Condpor

namespace Life

namespace Sem

variable {P : LProg} {n : ℕ} {s : MState} {g : GB}

/-! ### One compiled event of a running thread -/

theorem run1 (hn : adequateB P n = true) {t : Tid} (ht : t ∈ P.threads) {st : TState} {a : Act}
    (hst : stopped (lifeTab P) t (tr P g t) = false) (hb : BodyAt P t (tr P g t) st)
    (ha : st.act P.st t = some a) : (lifeSys P n).toProgram.step t (tr P g t) = some a :=
  step_of_lifeTab hn ht hst (by rw [lifeTab_of_bodyAt hb, ha])

theorem after1 {g' : GB} {t : Tid} {st : TState} {a : Act} {v : Option Val}
    (htr : tr P g' t = tr P g t ++ [v]) (hst : stopped (lifeTab P) t (tr P g t) = false)
    (hb : BodyAt P t (tr P g t) st) (ha : st.act P.st t = some a) :
    BodyAt P t (tr P g' t) (st.next v) ∧
      stopped (lifeTab P) t (tr P g' t) = isStop (some a) := by
  rw [htr]
  refine ⟨bodyAt_append hb v, ?_⟩
  rw [stopped_append, hst, lifeTab_of_bodyAt hb, ha]
  simp

theorem trel_running {t : Tid} {u : List (Option Val)} (h : TRel P s t u)
    (hs : s.status t = .running) :
    stopped (lifeTab P) t u = false ∧ BodyAt P t u ⟨s.rest t, holdsM s t, .ready⟩ := by
  unfold TRel at h; rw [hs] at h; exact h

theorem tr_self {g' : GB} {t : Tid} {v : Option Val}
    (h : ∀ t', tr P g' t' = tr P g t' ++ (if t = t' then [v] else [])) :
    tr P g' t = tr P g t ++ [v] := by simpa using h t

theorem tr_other {g' : GB} {t : Tid} {v : Option Val}
    (h : ∀ t', tr P g' t' = tr P g t' ++ (if t = t' then [v] else [])) {t' : Tid} (hne : t' ≠ t) :
    tr P g' t' = tr P g t' := by simpa [Ne.symm hne] using h t'

/-- The head call of a running thread, with the remaining calls. -/
theorem rest_cons {t : Tid} {c : TOp} (h : (s.rest t).head? = some c) :
    s.rest t = c :: (s.rest t).tail := by
  obtain ⟨r, hr⟩ := List.head?_eq_some_iff.mp h
  rw [hr]; rfl

end Sem

end Life

end Condpor
