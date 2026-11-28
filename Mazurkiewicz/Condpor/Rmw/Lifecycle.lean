import Mazurkiewicz.Condpor.Rmw.TargetsFast

/-!
# Thread lifecycle: `start`, finish, `join` as memory accesses (LC1)

The encoding of `plan/condpor/lean/monitors/LIFECYCLE-DESIGN.md` (draft 4.2), §2-§4. A
lifecycle program (`LProg`) is compiled to an `XProgram` with `mkXProg`; nothing of
`Program`, `XProgram`, the graphs or the explorer changes.

* Locations have three roles: the lock locations `P.locks`, the lifecycle locations
  `P.st t` of the threads (values `0` new, `1` started, `2` finished), and the data
  locations (all others). The fragment check requires `st` injective on the threads and
  disjoint from the locks; a data location is one that is neither.
* Calls (`TOp`): `lock`, `tryLock`, `unlock`, `rd`, `wr` as in `Locks.lean` (no constraint
  evaluation `ev`), `start t` (a write of `1` to `st t`), `join t` (a read of `st t`; on
  `1` the thread blocks), `assume x v` (a read of `x`; on a value other than `v` the thread
  blocks).
* A non-root thread begins with the *start-read* of its own `st t`; on `0` it blocks. Every
  thread whose code is exhausted writes `2` to its `st t` (the finish write). Initial
  memory: `1` on the lifecycle location of a root, `0` elsewhere (data and locks too).
* `fragB`: the supported fragment (§2.2), a `Bool`. The single-start rule is checked on
  control paths (`maxStarts`); `maxStarts_eq_count` shows that, since a `tryLock` that
  succeeds continues with all calls, the maximum over paths is the number of `start u`
  calls of the list.
* `lifeSys`, the explorer theorems for it (`lifeSys_explore` and the others, the proof
  terms of `lockSys_explore`): they speak of the compiled program only, not of Java.
* `adequateB` (`n ≥ 2·|code t| + 3`) and `lifeSys_noCut`: under an adequate bound no
  thread of a full graph is cut (proved; it needs neither the fragment nor `Exec`).
* The classifier of §3 (`lifeClass`, `lifeCounts`) and the lock signature (`lockSig`).
* The lemmas of §4 for a program of the fragment and a well-formed, SC-consistent execution
  (section `Lemmas`).

Not formalised here: the machine and the gate theorem of §5 (LC2), any statement about
Java or JMC.
-/

namespace Condpor

namespace Life

open Program Targets

/-! ### Programs -/

/-- A call of a thread. -/
inductive TOp where
  /-- acquire, blocking -/
  | lock (l : Loc)
  /-- acquire if free; on failure skip the next `k` calls -/
  | tryLock (l : Loc) (k : ℕ)
  /-- release -/
  | unlock (l : Loc)
  /-- a plain read (on a lock location: a query) -/
  | rd (x : Loc)
  /-- a plain write -/
  | wr (x : Loc) (v : Val)
  /-- start a thread -/
  | start (t : Tid)
  /-- wait for a thread to finish (returns at once if it is not started) -/
  | join (t : Tid)
  /-- continue only if `x` holds `v` -/
  | assume (x : Loc) (v : Val)
  deriving DecidableEq, Repr

/-- A lifecycle program: threads, the root threads (running from the start), the lock
locations, the lifecycle location of each thread, and the calls of each thread. -/
structure LProg where
  threads : List Tid
  nodup : threads.Nodup
  roots : List Tid
  locks : List Loc
  st : Tid → Loc
  code : Tid → List TOp

namespace LProg

variable (P : LProg)

/-- `x` is the lifecycle location of a thread of the program. -/
def isSt (x : Loc) : Bool := P.threads.any (fun t => decide (P.st t = x))

/-- `x` is a lock location. -/
def isLock (x : Loc) : Bool := decide (x ∈ P.locks)

/-- `x` is a data location: neither a lock nor a lifecycle location. -/
def isData (x : Loc) : Bool := !P.isLock x && !P.isSt x

/-- `t` is a root thread. -/
def isRoot (t : Tid) : Bool := decide (t ∈ P.roots)

end LProg

/-! ### The compiled table -/

/-- What the thread does next, apart from the remaining calls. -/
inductive TPhase where
  /-- the next call, or the finish write if there is none -/
  | ready
  /-- the exclusive write of an acquire whose read returned `0` -/
  | acquire (l : Loc)
  /-- the read of a `lock`, `join` or `assume` returned a blocking value -/
  | blocking
  /-- the finish write is done -/
  | done
  deriving DecidableEq, Repr

/-- The state of a thread body: remaining calls, hold counts, phase. -/
structure TState where
  ops : List TOp
  holds : Loc → ℕ
  phase : TPhase

/-- The next action of the body of thread `me` (lifecycle locations `st`). -/
def TState.act (st : Tid → Loc) (me : Tid) (s : TState) : Option Act :=
  match s.phase with
  | .acquire l => some (.write l 1)
  | .blocking => some .block
  | .done => none
  | .ready =>
    match s.ops with
    | [] => some (.write (st me) 2)
    | .lock l :: _ => if s.holds l = 0 then some (.read l) else some (.gen 0)
    | .tryLock l _ :: _ => if s.holds l = 0 then some (.read l) else some (.gen 0)
    | .unlock l :: _ =>
      if s.holds l = 0 then some .error
      else if s.holds l = 1 then some (.write l 0) else some (.gen 0)
    | .rd x :: _ => some (.read x)
    | .wr x v :: _ => some (.write x v)
    | .start u :: _ => some (.write (st u) 1)
    | .join u :: _ => some (.read (st u))
    | .assume x _ :: _ => some (.read x)

/-- The next action is exclusive: the read of an acquire, or its write. -/
def TState.isEx (s : TState) : Bool :=
  match s.phase with
  | .acquire _ => true
  | .ready =>
    match s.ops with
    | .lock l :: _ => decide (s.holds l = 0)
    | .tryLock l _ :: _ => decide (s.holds l = 0)
    | _ => false
  | _ => false

/-- The state after the action of the state returned `v`. -/
def TState.next (s : TState) (v : Option Val) : TState :=
  match s.phase with
  | .acquire l => ⟨s.ops, Function.update s.holds l 1, .ready⟩
  | .blocking => s
  | .done => s
  | .ready =>
    match s.ops with
    | [] => ⟨[], s.holds, .done⟩
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
    | .join _ :: rest =>
      if v = some 1 then ⟨rest, s.holds, .blocking⟩ else ⟨rest, s.holds, .ready⟩
    | .assume _ w :: rest =>
      if v = some w then ⟨rest, s.holds, .ready⟩ else ⟨rest, s.holds, .blocking⟩
    | _ :: rest => ⟨rest, s.holds, .ready⟩

/-- The initial state of a body. -/
def TState.init (ops : List TOp) : TState := ⟨ops, fun _ => 0, .ready⟩

/-- The state of the body with the calls `ops` after the trace `u`. -/
def tState (ops : List TOp) (u : List (Option Val)) : TState :=
  u.foldl TState.next (TState.init ops)

/-- The compiled table of next actions: a non-root thread first reads its lifecycle
location (the start-read) and blocks on `0`; then the body; then the finish write. -/
def lifeTab (P : LProg) (t : Tid) (u : List (Option Val)) : Option Act :=
  if P.isRoot t then (tState (P.code t) u).act P.st t
  else
    match u with
    | [] => some (.read (P.st t))
    | v :: rest =>
      if v = some 0 then (if rest = [] then some .block else none)
      else (tState (P.code t) rest).act P.st t

/-- The table of exclusive flags: the reads and writes of acquires; the start-read is
not exclusive. -/
def lifeFlag (P : LProg) (t : Tid) (u : List (Option Val)) : Bool :=
  if P.isRoot t then (tState (P.code t) u).isEx
  else
    match u with
    | [] => false
    | v :: rest => if v = some 0 then false else (tState (P.code t) rest).isEx

/-- The initial memory: `1` on the lifecycle location of a root, `0` elsewhere. -/
def lifeMem (P : LProg) (x : Loc) : Val :=
  if P.roots.any (fun r => decide (P.st r = x)) then 1 else 0

/-- The compiled program, cut at `n` actions per thread. -/
def lifeSys (P : LProg) (n : ℕ) : XProgram :=
  mkXProg P.threads P.nodup (lifeTab P) (lifeFlag P) (lifeMem P) n

/-! ### The supported fragment (§2.2) -/

/-- The roles of the locations of one call of thread `t`: lock calls on lock locations;
`rd` not on a lifecycle location; `wr` and `assume` on data locations; `start`/`join` of
a declared non-root thread other than `t`. -/
def callOk (P : LProg) (t : Tid) : TOp → Bool
  | .lock l => P.isLock l
  | .tryLock l _ => P.isLock l
  | .unlock l => P.isLock l
  | .rd x => !P.isSt x
  | .wr x _ => P.isData x
  | .assume x _ => P.isData x
  | .start u => decide (u ∈ P.threads) && !P.isRoot u && decide (u ≠ t)
  | .join u => decide (u ∈ P.threads) && !P.isRoot u && decide (u ≠ t)

/-- The largest number of `start u` calls on a control path of a call list, with fuel
(a failed `tryLock l k` skips `k` calls). -/
def maxStartsF (u : Tid) : ℕ → List TOp → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | f + 1, c :: rest =>
    (if c = .start u then 1 else 0) +
      (match c with
        | .tryLock _ k => max (maxStartsF u f rest) (maxStartsF u f (rest.drop k))
        | _ => maxStartsF u f rest)

/-- The largest number of `start u` calls on a control path of `ops`. -/
def maxStarts (u : Tid) (ops : List TOp) : ℕ := maxStartsF u ops.length ops

/-- The fragment of §2.2. -/
def fragB (P : LProg) : Bool :=
  P.roots.all (fun r => decide (r ∈ P.threads)) &&
  decide (P.threads.map P.st).Nodup &&
  P.threads.all (fun t => !P.isLock (P.st t)) &&
  P.threads.all (fun t => (P.code t).all (callOk P t)) &&
  P.threads.all (fun u =>
    decide ((P.threads.filter (fun t => (P.code t).contains (.start u))).length ≤ 1) &&
    P.threads.all (fun t => decide (maxStarts u (P.code t) ≤ 1)))

/-! #### The rules of the fragment, one by one

`fragChecks` lists the twelve rules of §2.2 separately (`fragB_eq`: `fragB` is their
conjunction), so that a rejected program can be shown to break exactly one rule. -/

/-- Per call: lock calls name a lock location. -/
def chkLockLoc (P : LProg) : TOp → Bool
  | .lock l | .tryLock l _ | .unlock l => P.isLock l
  | _ => true

/-- Per call: `rd` is not of a lifecycle location. -/
def chkRd (P : LProg) : TOp → Bool
  | .rd x => !P.isSt x
  | _ => true

/-- Per call: `wr` writes a data location. -/
def chkWr (P : LProg) : TOp → Bool
  | .wr x _ => P.isData x
  | _ => true

/-- Per call: `assume` reads a data location. -/
def chkAsm (P : LProg) : TOp → Bool
  | .assume x _ => P.isData x
  | _ => true

/-- Per call: the target of `start`/`join` is a declared thread. -/
def chkDecl (P : LProg) : TOp → Bool
  | .start u | .join u => decide (u ∈ P.threads)
  | _ => true

/-- Per call: the target of `start`/`join` is not a root. -/
def chkNotRoot (P : LProg) : TOp → Bool
  | .start u | .join u => !P.isRoot u
  | _ => true

/-- Per call of thread `t`: the target of `start`/`join` is not `t`. -/
def chkNotSelf (t : Tid) : TOp → Bool
  | .start u | .join u => decide (u ≠ t)
  | _ => true

theorem callOk_eq (P : LProg) (t : Tid) (c : TOp) :
    callOk P t c = (chkLockLoc P c && chkRd P c && chkWr P c && chkAsm P c && chkDecl P c &&
      chkNotRoot P c && chkNotSelf t c) := by
  cases c <;> simp [callOk, chkLockLoc, chkRd, chkWr, chkAsm, chkDecl, chkNotRoot, chkNotSelf,
    Bool.and_assoc]

/-- The twelve rules of §2.2, in this order: (1) roots are declared threads; (2) `st` is
injective on the threads; (3) no `st` is a lock location; (4) lock calls on lock locations;
(5) no `rd` of a lifecycle location; (6) `wr` on data; (7) `assume` on data; (8) `start`
/`join` targets declared; (9) targets not roots; (10) targets not the caller; (11) at most
one thread whose code starts a given thread; (12) at most one `start u` on a control path.
-/
def fragChecks (P : LProg) : List Bool :=
  let calls := fun (f : Tid → TOp → Bool) => P.threads.all (fun t => (P.code t).all (f t))
  [P.roots.all (fun r => decide (r ∈ P.threads)),
    decide (P.threads.map P.st).Nodup,
    P.threads.all (fun t => !P.isLock (P.st t)),
    calls (fun _ => chkLockLoc P), calls (fun _ => chkRd P), calls (fun _ => chkWr P),
    calls (fun _ => chkAsm P), calls (fun _ => chkDecl P), calls (fun _ => chkNotRoot P),
    calls chkNotSelf,
    P.threads.all (fun u =>
      decide ((P.threads.filter (fun t => (P.code t).contains (.start u))).length ≤ 1)),
    P.threads.all (fun u => P.threads.all (fun t => decide (maxStarts u (P.code t) ≤ 1)))]

theorem fragB_eq (P : LProg) : fragB P = (fragChecks P).all id := by
  rw [Bool.eq_iff_iff]
  simp only [fragB, fragChecks, callOk_eq, List.all_cons, List.all_nil, id, Bool.and_true,
    Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    exact ⟨h1, h2, h3, fun t ht c hc => (h4 t ht c hc).1.1.1.1.1.1,
      fun t ht c hc => (h4 t ht c hc).1.1.1.1.1.2, fun t ht c hc => (h4 t ht c hc).1.1.1.1.2,
      fun t ht c hc => (h4 t ht c hc).1.1.1.2, fun t ht c hc => (h4 t ht c hc).1.1.2,
      fun t ht c hc => (h4 t ht c hc).1.2, fun t ht c hc => (h4 t ht c hc).2,
      fun u hu => (h5 u hu).1, fun u hu => (h5 u hu).2⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, fun t ht c hc => ⟨⟨⟨⟨⟨⟨h4 t ht c hc, h5 t ht c hc⟩,
      h6 t ht c hc⟩, h7 t ht c hc⟩, h8 t ht c hc⟩, h9 t ht c hc⟩, h10 t ht c hc⟩⟩,
      fun u hu => ⟨h11 u hu, h12 u hu⟩⟩

/-- The adequate bound of §2.4. -/
def adequateB (P : LProg) (n : ℕ) : Bool :=
  P.threads.all (fun t => decide (2 * (P.code t).length + 3 ≤ n))

theorem maxStartsF_eq_count (u : Tid) (f : ℕ) (ops : List TOp) (hf : ops.length ≤ f) :
    maxStartsF u f ops = ops.count (.start u) := by
  induction f generalizing ops with
  | zero =>
    have : ops = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hf)
    subst this
    rfl
  | succ f ih =>
    cases ops with
    | nil => rfl
    | cons c rest =>
      have hr : rest.length ≤ f := by simp at hf; omega
      have hd : ∀ k, (rest.drop k).length ≤ f := fun k => by
        simp only [List.length_drop]; omega
      unfold maxStartsF
      rw [List.count_cons]
      cases c with
      | tryLock l k =>
        dsimp only
        rw [ih _ hr, ih _ (hd k)]
        have hle : (rest.drop k).count (.start u) ≤ rest.count (.start u) :=
          (List.drop_sublist k rest).count_le _
        simp only [reduceCtorEq, ↓reduceIte, beq_iff_eq, Nat.zero_add]
        omega
      | start v =>
        rw [ih _ hr]
        by_cases hv : v = u
        · subst hv; simp; omega
        · simp [hv]
      | lock _ => rw [ih _ hr]; simp
      | unlock _ => rw [ih _ hr]; simp
      | rd _ => rw [ih _ hr]; simp
      | wr _ _ => rw [ih _ hr]; simp
      | join _ => rw [ih _ hr]; simp
      | assume _ _ => rw [ih _ hr]; simp

/-- The path check counts the `start u` calls: the path that makes every `tryLock`
succeed contains all calls. -/
theorem maxStarts_eq_count (u : Tid) (ops : List TOp) :
    maxStarts u ops = ops.count (.start u) :=
  maxStartsF_eq_count u _ ops le_rfl

/-! ### The explorer theorems for lifecycle programs (§2.3) -/

/-- The computed explorer lists, without repetition, exactly the well-formed full
executions of the compiled program that are SC-consistent and atomic. -/
theorem lifeSys_explore (P : LProg) (n : ℕ) :
    (exploreAt (lifeSys P n) eqOracleSe n).Nodup ∧
      ∀ G, G ∈ exploreAt (lifeSys P n) eqOracleSe n ↔
        G.Wf ∧ (lifeSys P n).toProgram.Exec G ∧
          ((Model.atomic (lifeSys P n) SC).sym EqSem.solver).cons G ∧
          (lifeSys P n).toProgram.Full G :=
  exploreAt_spec eqOracleSe (mkXProg_bounded _ _ _ _ _ _)

/-- Completeness for the compiled program, any solver and tie-break. -/
theorem lifeSys_complete {S : Solver} {τ : TieBreak S} (P : LProg) (n : ℕ) {Gf : Graph}
    (hGf : Gf.Wf) (hEf : (lifeSys P n).toProgram.Exec Gf)
    (hcf : ((Model.atomic (lifeSys P n) SC).sym S).cons Gf)
    (hff : (lifeSys P n).toProgram.Full Gf) :
    ∃ c, Reach (lifeSys P n).toProgram ((Model.atomic (lifeSys P n) SC).sym S) τ c ∧
      c.abs = Gf :=
  Rmw.complete_sc (mkXProg_bounded _ _ _ _ _ _) hGf hEf hcf hff

/-- No graph of the compiled program is reached twice. -/
theorem lifeSys_eq_of_abs_eq {S : Solver} {τ : TieBreak S} (P : LProg) (n : ℕ)
    {c1 c2 : Config}
    (h1 : Reach (lifeSys P n).toProgram ((Model.atomic (lifeSys P n) SC).sym S) τ c1)
    (h2 : Reach (lifeSys P n).toProgram ((Model.atomic (lifeSys P n) SC).sym S) τ c2)
    (h : c1.abs = c2.abs) : c1 = c2 :=
  Rmw.eq_of_abs_eq h1 h2 h

/-- A reached configuration of the compiled program from which no full configuration is
reachable has no step. -/
theorem lifeSys_blocked_of_fruitless {S : Solver} {τ : TieBreak S} (P : LProg) (n : ℕ)
    {c : Config}
    (hc : Reach (lifeSys P n).toProgram ((Model.atomic (lifeSys P n) SC).sym S) τ c)
    (hfr : ¬ ∃ c', Relation.ReflTransGen (Step (lifeSys P n).toProgram
      ((Model.atomic (lifeSys P n) SC).sym S) τ) c c' ∧ (lifeSys P n).toProgram.Full c'.abs) :
    ¬ ∃ c1, Step (lifeSys P n).toProgram ((Model.atomic (lifeSys P n) SC).sym S) τ c c1 :=
  Rmw.blocked_of_fruitless (mkXProg_bounded _ _ _ _ _ _) (SC.extensibleX _)
    (SC.exclExtensible _) hc hfr

/-! ### The adequate bound: no thread is cut -/

/-- The number of actions a body state can still perform before it stops or ends. -/
def TState.pot (s : TState) : ℕ :=
  match s.phase with
  | .ready => 2 * s.ops.length + 1
  | .acquire _ => 2 * s.ops.length + 2
  | .blocking => 1
  | .done => 0

theorem TState.isStop_act_or_pot (st : Tid → Loc) (me : Tid) (s : TState) (v : Option Val)
    (a : Act) (ha : s.act st me = some a) :
    a = .block ∨ a = .error ∨ (s.next v).pot + 1 ≤ s.pot := by
  rcases s with ⟨ops, holds, ph⟩
  cases ph with
  | acquire l => right; right; simp [TState.next, TState.pot]
  | blocking => left; simp [TState.act] at ha; exact ha.symm
  | done => simp [TState.act] at ha
  | ready =>
    cases ops with
    | nil => right; right; simp [TState.next, TState.pot]
    | cons c rest =>
      cases c with
      | lock l =>
        right; right
        simp only [TState.next, TState.pot]
        split_ifs <;> simp <;> omega
      | tryLock l k =>
        right; right
        simp only [TState.next, TState.pot]
        split_ifs <;> simp <;> omega
      | unlock l =>
        by_cases h0 : holds l = 0
        · right; left; simp [TState.act, h0] at ha; exact ha.symm
        · right; right
          simp only [TState.next, TState.pot, h0, ↓reduceIte]
          simp; omega
      | join u =>
        right; right
        simp only [TState.next, TState.pot]
        split_ifs <;> simp <;> omega
      | assume x w =>
        right; right
        simp only [TState.next, TState.pot]
        split_ifs <;> simp <;> omega
      | rd x => right; right; simp [TState.next, TState.pot]; omega
      | wr x v => right; right; simp [TState.next, TState.pot]; omega
      | start u => right; right; simp [TState.next, TState.pot]; omega

theorem TState.act_none_next (st : Tid → Loc) (me : Tid) (s : TState) (v : Option Val)
    (h : s.act st me = none) : (s.next v).act st me = none := by
  rcases s with ⟨ops, holds, ph⟩
  cases ph with
  | done => simpa [TState.next] using h
  | ready => cases ops with
    | nil => simp [TState.act] at h
    | cons c rest => cases c <;> simp [TState.act] at h <;> split_ifs at h
  | acquire l => simp [TState.act] at h
  | blocking => simp [TState.act] at h

theorem TState.pot_pos (st : Tid → Loc) (me : Tid) (s : TState) (h : s.act st me ≠ none) :
    1 ≤ s.pot := by
  rcases s with ⟨ops, holds, ph⟩
  cases ph with
  | done => exact absurd (by simp [TState.act]) h
  | ready => simp [TState.pot]
  | acquire l => simp [TState.pot]
  | blocking => simp [TState.pot]

theorem tState_append (ops : List TOp) (u : List (Option Val)) (v : Option Val) :
    tState ops (u ++ [v]) = (tState ops u).next v := by
  simp [tState, List.foldl_append]

theorem stopped_append {f : Tid → List (Option Val) → Option Act} {t : Tid}
    {u : List (Option Val)} {v : Option Val} :
    stopped f t (u ++ [v]) = (stopped f t u || isStop (f t u)) := by
  unfold stopped
  rw [List.length_append, List.length_singleton, List.range_succ, List.any_append]
  have h1 : ((List.range u.length).any fun i => isStop (f t ((u ++ [v]).take i))) =
      (List.range u.length).any fun i => isStop (f t (u.take i)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_range]
    constructor
    · rintro ⟨i, hi, h⟩
      refine ⟨i, hi, ?_⟩
      rwa [List.take_append_of_le_length (by omega)] at h
    · rintro ⟨i, hi, h⟩
      refine ⟨i, hi, ?_⟩
      rwa [List.take_append_of_le_length (by omega)]
  rw [h1]
  simp

/-- Along any trace on which the body has not stopped, it has performed at most `pot`
of its initial state actions, or it has ended. -/
theorem tState_pot (st : Tid → Loc) (me : Tid) (ops : List TOp) (u : List (Option Val))
    (hs : ∀ i < u.length, isStop ((tState ops (u.take i)).act st me) = false) :
    (tState ops u).act st me = none ∨ u.length + (tState ops u).pot ≤ 2 * ops.length + 1 := by
  induction u using List.reverseRecOn with
  | nil => right; simp [tState, TState.init, TState.pot, List.foldl]
  | append_singleton u v ih =>
    have hs' : ∀ i < u.length, isStop ((tState ops (u.take i)).act st me) = false := by
      intro i hi
      have := hs i (by simp; omega)
      rwa [List.take_append_of_le_length (by omega)] at this
    have hlast := hs u.length (by simp)
    rw [List.take_append_of_le_length le_rfl, List.take_length] at hlast
    rw [tState_append]
    rcases ih hs' with h | h
    · left; exact TState.act_none_next st me _ v h
    · cases ha : (tState ops u).act st me with
      | none => left; exact TState.act_none_next st me _ v ha
      | some a =>
        rcases TState.isStop_act_or_pot st me _ v a ha with rfl | rfl | hp
        · rw [ha] at hlast; simp [isStop] at hlast
        · rw [ha] at hlast; simp [isStop] at hlast
        · right; simp; omega

/-- The compiled table of a thread that has not stopped and still has an action has
performed fewer than `2·|code t| + 2` actions. -/
theorem lifeTab_length (P : LProg) (t : Tid) (u : List (Option Val))
    (hs : stopped (lifeTab P) t u = false) (hd : lifeTab P t u ≠ none) :
    u.length ≤ 2 * (P.code t).length + 1 := by
  unfold stopped at hs
  have hs' : ∀ i < u.length, isStop (lifeTab P t (u.take i)) = false := by
    intro i hi
    by_contra h
    have : (List.range u.length).any (fun i => isStop (lifeTab P t (u.take i))) = true :=
      List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, by simpa using h⟩
    rw [this] at hs
    cases hs
  by_cases hr : P.isRoot t = true
  · have hd' : (tState (P.code t) u).act P.st t ≠ none := by
      simpa [lifeTab, hr] using hd
    have hs2 : ∀ i < u.length, isStop ((tState (P.code t) (u.take i)).act P.st t) = false :=
      fun i hi => by simpa [lifeTab, hr] using hs' i hi
    rcases tState_pot P.st t (P.code t) u hs2 with h | h
    · exact absurd h hd'
    · have := TState.pot_pos P.st t _ hd'
      omega
  · cases u with
    | nil => simp
    | cons v rest =>
      by_cases hv : v = some 0
      · cases rest with
        | nil => simp
        | cons w rest =>
          have h1 := hs' 1 (by simp)
          simp [lifeTab, hr, hv, isStop] at h1
      · have hd' : (tState (P.code t) rest).act P.st t ≠ none := by
          simpa [lifeTab, hr, hv] using hd
        have hs2 : ∀ i < rest.length,
            isStop ((tState (P.code t) (rest.take i)).act P.st t) = false := by
          intro i hi
          have := hs' (i + 1) (by simp; omega)
          simpa [lifeTab, hr, hv] using this
        rcases tState_pot P.st t (P.code t) rest hs2 with h | h
        · exact absurd h hd'
        · have := TState.pot_pos P.st t _ hd'
          simp
          omega

/-- A thread is *cut* in a graph if it has not stopped (`block` or `error`) and the
unbounded compiled table still has an action for its trace. -/
def CutAt (P : LProg) (u : List (Option Val)) (t : Tid) : Prop :=
  stopped (lifeTab P) t u = false ∧ lifeTab P t u ≠ none

/-- **No cut under an adequate bound.** In a full graph of `lifeSys P n` with
`adequateB P n`, no thread of the program is cut. -/
theorem lifeSys_noCut (P : LProg) {n : ℕ} (hn : adequateB P n = true) {G : Graph}
    (hf : (lifeSys P n).toProgram.Full G) {t : Tid} (ht : t ∈ P.threads) :
    ¬ CutAt P (G.trace t) t := by
  rintro ⟨hs, hd⟩
  have hstep := (Program.full_iff.mp hf) t ht
  have hlen := lifeTab_length P t _ hs hd
  have hb : 2 * (P.code t).length + 3 ≤ n := by
    have := List.all_eq_true.mp hn t ht
    simpa using this
  simp only [lifeSys, mkXProg, mkProg] at hstep
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by simp [ht, hs]; omega))] at hstep
  exact hd hstep

/-! ### The classifier (§3) -/

/-- The kind of a `block`, from its po-predecessor `p` and the roles of locations. -/
inductive Kind where
  | lockW | startW | joinW | asm
  /-- not in the table of §3: impossible on a well-formed execution of a program of the
  fragment (`lifeClass_ne_odd`); outside the fragment it occurs (`outsideAsmSt_class`), and a
  `block` can also be misclassified (`outsideLockAsm_class`) -/
  | odd
  deriving DecidableEq, Repr

/-- The kind of the read `p` that precedes a `block` of thread `t`. -/
def kindOf (P : LProg) (c : Config) (t : Tid) (p : TEv) : Kind :=
  match p.act with
  | .read x =>
    if P.isLock x && decide (c.abs.ret p ≠ some 0) then .lockW
    else if decide (x = P.st t) && decide (c.abs.ret p = some 0) then .startW
    else if P.threads.any (fun u => decide (u ≠ t ∧ P.st u = x)) &&
        decide (c.abs.ret p = some 1) then .joinW
    else if P.isData x then .asm
    else .odd
  | _ => .odd

/-- The wait of thread `t`, if its last event is a `block`: kind and finality (the
predecessor reads the coherence-maximal write of its location). -/
def waitOf (P : LProg) (c : Config) (t : Tid) : Option (Kind × Bool) :=
  match (thEvents c t).getLast? with
  | some b =>
    if b.act = .block then
      match b.idx, c.evAt t (b.idx - 1) with
      | 0, _ => some (.odd, false)
      | _ + 1, some p => some (kindOf P c t p, finalB c p)
      | _ + 1, none => some (.odd, false)
    else none
  | none => none

/-- The classes of §3, with `odd` for a graph outside the kind table. -/
inductive LCls where
  | cut | exploration | error | blocked | deadlock | complete | odd
  deriving DecidableEq, Repr

/-- The stop-aware cut check on a configuration. -/
def cutB (P : LProg) (c : Config) (t : Tid) : Bool :=
  !stopped (lifeTab P) t (c.trace t) && (lifeTab P t (c.trace t)).isSome

/-- The class of a full configuration, first match: cut, odd, exploration, error,
blocked, deadlock, complete. -/
def lifeClass (P : LProg) (c : Config) : LCls :=
  let ws := P.threads.filterMap (waitOf P c)
  if P.threads.any (cutB P c) then .cut
  else if ws.any (fun w => decide (w.1 = .odd)) then .odd
  else if ws.any (fun w => decide (w.1 ≠ .asm) && !w.2) then .exploration
  else if c.order.any (fun e => decide (e.act = .error)) then .error
  else if ws.any (fun w => decide (w.1 = .asm)) then .blocked
  else if ws.any (fun w => decide (w.1 = .lockW ∨ w.1 = .joinW)) then .deadlock
  else .complete

/-- Counts per class: (cut, exploration, error, blocked, deadlock, complete, odd). -/
def lifeCounts (P : LProg) (l : List Config) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let k := fun (x : LCls) => (l.filter (fun c => decide (lifeClass P c = x))).length
  (k .cut, k .exploration, k .error, k .blocked, k .deadlock, k .complete, k .odd)

/-- The class counts of the graphs of the explorer. -/
def lifeReport (P : LProg) (n : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  lifeCounts P (exploreCfgAtF (lifeSys P n) n)

/-- Under an adequate bound, no listed graph is classified `cut`. -/
theorem lifeClass_ne_cut (P : LProg) {n : ℕ} (hn : adequateB P n = true) {c : Config}
    (hc : c ∈ exploreCfgAtF (lifeSys P n) n) : lifeClass P c ≠ .cut := by
  obtain ⟨hr, hf⟩ := mem_exploreCfgAtF _ n hc
  have hw := hr.sound.1
  intro h
  unfold lifeClass at h
  by_cases h1 : P.threads.any (cutB P c) = true
  swap
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    split_ifs at h
  obtain ⟨t, ht, hcut⟩ := List.any_eq_true.mp h1
  apply lifeSys_noCut P hn hf ht
  rw [← Config.trace_eq c hw t]
  simp only [cutB, Bool.and_eq_true, Bool.not_eq_true', Option.isSome_iff_ne_none] at hcut
  exact hcut

/-! ### The lock signature (§4) -/

/-- A normalised source of a read, as a list of numbers: `[]` for `init`; for a thread
write, its thread, the code of its label and the number of events of the writer with that
label up to it. -/
def srcName (c : Config) : Option Ev → List ℕ
  | some (.th w) =>
    [w.tid, w.act.code.1, w.act.code.2.1, w.act.code.2.2,
      ((thEvents c w.tid).filter (fun e => decide (e.idx ≤ w.idx ∧ e.act = w.act))).length]
  | _ => []

/-- The signature of one lock `l` (the projection of `opus-life-d1/proj.py` for lock
`0`): the acquiring threads in coherence order, and per thread the sources of its reads of
`l`. -/
def lockSig1 (ts : List Tid) (c : Config) (l : Loc) : List ℕ × List (List (List ℕ)) :=
  (((c.co l).filter (fun w => decide (w.act = .write l 1))).map TEv.tid,
    ts.map (fun t => ((thEvents c t).filter (fun e => decide (e.act = .read l))).map
      (fun e => srcName c (c.rf e))))

/-- The signature for several locks: the list of the one-lock signatures. -/
def lockSig (ts : List Tid) (locks : List Loc) (c : Config) :
    List (List ℕ × List (List (List ℕ))) :=
  locks.map (lockSig1 ts c)

/-- The number of distinct signatures of the graphs of a class. -/
def sigCount (P : LProg) (l : List Config) (x : LCls) : ℕ :=
  ((l.filter (fun c => decide (lifeClass P c = x))).map (lockSig P.threads P.locks)).dedup.length

/-- Signature counts of the terminal-valid classes: (error, blocked, deadlock, complete). -/
def sigCounts (P : LProg) (l : List Config) : ℕ × ℕ × ℕ × ℕ :=
  (sigCount P l .error, sigCount P l .blocked, sigCount P l .deadlock, sigCount P l .complete)

/-- What a target states, as a list of numbers: the number of full graphs; the class
counts cut, exploration, error, blocked, deadlock, complete, odd; the signature counts
error, blocked, deadlock, complete. -/
def lifeTarget (P : LProg) (n : ℕ) : List ℕ :=
  let l := exploreCfgAtF (lifeSys P n) n
  let c := lifeCounts P l
  let g := sigCounts P l
  [l.length, c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2.1, c.2.2.2.2.2.2,
    g.1, g.2.1, g.2.2.1, g.2.2.2]

/-- The listed configurations are the graphs of the proved explorer: their number, the
head of `lifeTarget`, is the number of well-formed full SC-consistent atomic executions
(`lifeSys_explore`). -/
theorem lifeTarget_head (P : LProg) (n : ℕ) :
    (lifeTarget P n).headD 0 = (exploreAt (lifeSys P n) eqOracleSe n).length := by
  simp only [lifeTarget, List.headD_cons, ← exploreCfgAtF_abs, List.length_map]

end Life

end Condpor
