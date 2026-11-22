import Mazurkiewicz.Condpor.Rmw.Instances

/-!
# Locks: `lock`, `tryLock`, `unlock`, repeated calls by the holder

A lock is a location with the values `0` (free) and `1` (held). A thread is a
list of calls; for each lock it has a hold count, a function of its trace.

* `lock L`, count `0`: an exclusive read of `L`; on `0` an exclusive write of
  `1`; otherwise the thread blocks. Count `> 0`: a local step.
* `tryLock L k`, count `0`: an exclusive read of `L`; on `0` an exclusive write
  of `1` (success); otherwise no write, and the next `k` calls are skipped
  (failure). Count `> 0`: a local step (success).
* `unlock L`, count `0`: `error`. Count `1`: a write of `0`. Count `> 1`: a
  local step.

`lockSys` is the program with exclusive accesses of a family of threads. The
theorems of `Condpor/Rmw/` hold for it as instances (`lockSys_explore`,
`lockSys_blocked_of_fruitless`).
-/

namespace Condpor

open Program

/-- A call of a thread. -/
inductive LOp where
  /-- acquire, blocking -/
  | lock (l : Loc)
  /-- acquire if free; on failure skip the next `k` calls -/
  | tryLock (l : Loc) (k : ℕ)
  /-- release -/
  | unlock (l : Loc)
  /-- a plain read -/
  | rd (x : Loc)
  /-- a plain write -/
  | wr (x : Loc) (v : Val)
  /-- the evaluation of the constraint `s = k` -/
  | ev (s k : ℕ)
  deriving DecidableEq, Repr

/-- What the thread does next, apart from the remaining calls. -/
inductive LPhase where
  /-- the next call -/
  | ready
  /-- the exclusive write of an acquire whose read returned `0` -/
  | acquire (l : Loc)
  /-- the read of `lock` returned a held state -/
  | blocking
  deriving DecidableEq, Repr

/-- The state of a thread: remaining calls, hold counts, phase. -/
structure LState where
  ops : List LOp
  holds : Loc → ℕ
  phase : LPhase

/-- The next action of a thread in a state. -/
def LState.act (s : LState) : Option Act :=
  match s.phase with
  | .acquire l => some (.write l 1)
  | .blocking => some .block
  | .ready =>
    match s.ops with
    | [] => none
    | .lock l :: _ => if s.holds l = 0 then some (.read l) else some (.gen 0)
    | .tryLock l _ :: _ => if s.holds l = 0 then some (.read l) else some (.gen 0)
    | .unlock l :: _ =>
      if s.holds l = 0 then some .error
      else if s.holds l = 1 then some (.write l 0) else some (.gen 0)
    | .rd x :: _ => some (.read x)
    | .wr x v :: _ => some (.write x v)
    | .ev a k :: _ => some (.cons (fEq a k))

/-- The next action is exclusive: the read of an acquire, or its write. -/
def LState.isEx (s : LState) : Bool :=
  match s.phase with
  | .acquire _ => true
  | .blocking => false
  | .ready =>
    match s.ops with
    | .lock l :: _ => decide (s.holds l = 0)
    | .tryLock l _ :: _ => decide (s.holds l = 0)
    | _ => false

/-- The state after the action of the state returned `v`. -/
def LState.next (s : LState) (v : Option Val) : LState :=
  match s.phase with
  | .acquire l => ⟨s.ops, Function.update s.holds l 1, .ready⟩
  | .blocking => s
  | .ready =>
    match s.ops with
    | [] => s
    | .lock l :: rest =>
      if s.holds l = 0 then
        (if v = some 0 then ⟨rest, s.holds, .acquire l⟩ else ⟨rest, s.holds, .blocking⟩)
      else ⟨rest, Function.update s.holds l (s.holds l + 1), .ready⟩
    | .tryLock l k :: rest =>
      if s.holds l = 0 then
        (if v = some 0 then ⟨rest, s.holds, .acquire l⟩ else ⟨rest.drop k, s.holds, .ready⟩)
      else ⟨rest, Function.update s.holds l (s.holds l + 1), .ready⟩
    | .unlock l :: rest =>
      if s.holds l = 0 then ⟨rest, s.holds, .ready⟩
      else ⟨rest, Function.update s.holds l (s.holds l - 1), .ready⟩
    | _ :: rest => ⟨rest, s.holds, .ready⟩

/-- The state of the thread with the calls `ops` after the trace `u`. -/
def lockState (ops : List LOp) (u : List (Option Val)) : LState :=
  u.foldl LState.next ⟨ops, fun _ => 0, .ready⟩

/-- The table of next actions of a family of threads. -/
def lsTab (code : Tid → List LOp) (t : Tid) (u : List (Option Val)) : Option Act :=
  (lockState (code t) u).act

/-- The table of flags. -/
def lsFlag (code : Tid → List LOp) (t : Tid) (u : List (Option Val)) : Bool :=
  (lockState (code t) u).isEx

/-- The program of the threads `threads` with the calls `code`, cut at `n`
actions per thread. -/
def lockSys (threads : List Tid) (hnd : threads.Nodup) (code : Tid → List LOp) (n : ℕ) :
    XProgram :=
  mkXProg threads hnd (lsTab code) (lsFlag code) (fun _ => 0) n

/-! ### The theorems for lock programs -/

/-- The computed explorer lists, without repetition, exactly the well-formed
full executions of a lock program that are SC-consistent and atomic. -/
theorem lockSys_explore (threads : List Tid) (hnd : threads.Nodup) (code : Tid → List LOp)
    (n : ℕ) :
    (exploreAt (lockSys threads hnd code n) eqOracleSe n).Nodup ∧
      ∀ G, G ∈ exploreAt (lockSys threads hnd code n) eqOracleSe n ↔
        G.Wf ∧ (lockSys threads hnd code n).toProgram.Exec G ∧
          ((Model.atomic (lockSys threads hnd code n) SC).sym EqSem.solver).cons G ∧
          (lockSys threads hnd code n).toProgram.Full G :=
  exploreAt_spec eqOracleSe (mkXProg_bounded _ _ _ _ _ _)

/-- Completeness for a lock program, any solver and tie-break. -/
theorem lockSys_complete {S : Solver} {τ : TieBreak S} (threads : List Tid)
    (hnd : threads.Nodup) (code : Tid → List LOp) (n : ℕ) {Gf : Graph} (hGf : Gf.Wf)
    (hEf : (lockSys threads hnd code n).toProgram.Exec Gf)
    (hcf : ((Model.atomic (lockSys threads hnd code n) SC).sym S).cons Gf)
    (hff : (lockSys threads hnd code n).toProgram.Full Gf) :
    ∃ c, Reach (lockSys threads hnd code n).toProgram
      ((Model.atomic (lockSys threads hnd code n) SC).sym S) τ c ∧ c.abs = Gf :=
  Rmw.complete_sc (mkXProg_bounded _ _ _ _ _ _) hGf hEf hcf hff

/-- No graph of a lock program is reached twice. -/
theorem lockSys_eq_of_abs_eq {S : Solver} {τ : TieBreak S} (threads : List Tid)
    (hnd : threads.Nodup) (code : Tid → List LOp) (n : ℕ) {c1 c2 : Config}
    (h1 : Reach (lockSys threads hnd code n).toProgram
      ((Model.atomic (lockSys threads hnd code n) SC).sym S) τ c1)
    (h2 : Reach (lockSys threads hnd code n).toProgram
      ((Model.atomic (lockSys threads hnd code n) SC).sym S) τ c2)
    (h : c1.abs = c2.abs) : c1 = c2 :=
  Rmw.eq_of_abs_eq h1 h2 h

/-- A reached configuration of a lock program from which no full
configuration is reachable has no step. -/
theorem lockSys_blocked_of_fruitless {S : Solver} {τ : TieBreak S} (threads : List Tid)
    (hnd : threads.Nodup) (code : Tid → List LOp) (n : ℕ) {c : Config}
    (hc : Reach (lockSys threads hnd code n).toProgram
      ((Model.atomic (lockSys threads hnd code n) SC).sym S) τ c)
    (hfr : ¬ ∃ c', Relation.ReflTransGen (Step (lockSys threads hnd code n).toProgram
      ((Model.atomic (lockSys threads hnd code n) SC).sym S) τ) c c' ∧
      (lockSys threads hnd code n).toProgram.Full c'.abs) :
    ¬ ∃ c1, Step (lockSys threads hnd code n).toProgram
      ((Model.atomic (lockSys threads hnd code n) SC).sym S) τ c c1 :=
  Rmw.blocked_of_fruitless (mkXProg_bounded _ _ _ _ _ _) (SC.extensibleX _)
    (SC.exclExtensible _) hc hfr

end Condpor
