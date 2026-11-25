import Mazurkiewicz.Condpor.Rmw.Lifecycle

/-!
# Thread lifecycle: an independent machine for the source programs (LC2-a)

The machine of `plan/condpor/lean/monitors/LIFECYCLE-DESIGN.md` (draft 4.2), §5, for the
source programs `LProg` / `TOp` of `Lifecycle.lean`. It does not use the lifecycle
locations `st` as memory, the compiled table `lifeTab`, or "no next compiled action": the
only things it takes from `Lifecycle.lean` are the program text (`LProg`), the location
roles (`isLock`, `isRoot`), the initial memory `lifeMem` (for the data memory and for the
graph), and, in the run-to-graph map only, the names `st t` of the lifecycle locations.

* State (`MState`): per thread a status (`new`, `running`, `term`, `erred`, `stopped` =
  assume-stopped), a started flag and the remaining calls (the program counter as a
  suffix of the code); per lock an owner and a count; the data memory.
* Transition occurrences (`Occ`): a step of one thread with its outcome (first or reentrant
  acquire, `tryLock` succeeded / failed / reentrant, release / reentrant unlock / error,
  lock query or data read, assume continued or stopped, …).
* `Enabled P s o` (relational, one constructor per row of the table of §5), `eff s o`
  (the effect column) and `Step P s o s' := Enabled P s o ∧ s' = eff s o`; executable:
  `next P s t` (the enabled occurrence of thread `t`, if any) and `enabledL P s`;
  `enabled_iff`: they agree.
* Footprints `fp` on resources `lock L` / `data x` / `life t`, `Dep`, `MEquiv`.
* Run to graph (`emit`, `finalize`, `runCfg`): chronological, event identifiers (thread,
  position in the thread), `rf` = the last earlier write to the location (else `init`),
  `co` = run order of the writes, synthetic final events by exclusive cases on the status.
* Final-state class `mclass`.
* Executable enumeration of the maximal runs (`runsF`, `machRuns`).
* Gate clauses of §5 as propositions (`Gate1`, `Gate2`, `Gate3`), not proved here.
-/

namespace Condpor

namespace Life

namespace Sem

open Targets

/-! ### Machine state -/

/-- The status of a thread. -/
inductive Status where
  /-- not yet running (a non-root thread before its `begin`) -/
  | new
  | running
  /-- terminated: `end` executed -/
  | term
  /-- an `unlock` of a lock it does not hold -/
  | erred
  /-- an `assume` whose value did not hold -/
  | stopped
  deriving DecidableEq, Repr

/-- The machine state. -/
@[ext]
structure MState where
  status : Tid → Status
  started : Tid → Bool
  /-- the remaining calls of each thread (the program counter, as a suffix of the code) -/
  rest : Tid → List TOp
  /-- the owner of each lock -/
  owner : Loc → Option Tid
  /-- the hold count of each lock -/
  count : Loc → ℕ
  /-- the data memory -/
  mem : Loc → Val

/-- The initial state: roots running (and started), the others new and not started; every
lock free with count `0`; data memory the compiled program's initial memory. -/
def MState.init (P : LProg) : MState where
  status := fun t => if P.isRoot t then .running else .new
  started := fun t => P.isRoot t
  rest := P.code
  owner := fun _ => none
  count := fun _ => 0
  mem := lifeMem P

namespace MState

variable (s : MState)

/-- Thread `t` holds lock `l`: it is the owner and the count is positive. -/
def heldB (t : Tid) (l : Loc) : Bool := decide (s.owner l = some t) && decide (0 < s.count l)

/-- A `join u` may return: `u` is new and not started, or terminated. -/
def joinOkB (u : Tid) : Bool :=
  (decide (s.status u = .new) && !s.started u) || decide (s.status u = .term)

/-- Advance the program counter of `t` to `r`. -/
def adv (t : Tid) (r : List TOp) : MState := { s with rest := Function.update s.rest t r }

/-- Set the status of `t`. -/
def setSt (t : Tid) (x : Status) : MState := { s with status := Function.update s.status t x }

end MState

/-! ### Transition occurrences -/

/-- A transition occurrence: a whole-call step of a thread, with its outcome. -/
inductive Occ where
  /-- a started new thread begins -/
  | begin (t : Tid)
  /-- `lock l`, first acquire (the lock was free) -/
  | acq (t : Tid) (l : Loc)
  /-- `lock l`, reentrant -/
  | reacq (t : Tid) (l : Loc)
  /-- `tryLock l k`, succeeded (the lock was free) -/
  | tryAcq (t : Tid) (l : Loc) (k : ℕ)
  /-- `tryLock l k`, failed (held by another thread): skip `k` calls -/
  | tryFail (t : Tid) (l : Loc) (k : ℕ)
  /-- `tryLock l k`, reentrant -/
  | tryRe (t : Tid) (l : Loc) (k : ℕ)
  /-- `unlock l`, count above `1` -/
  | unlockRe (t : Tid) (l : Loc)
  /-- `unlock l`, count `1`: the lock becomes free -/
  | release (t : Tid) (l : Loc)
  /-- `unlock l` of a lock not held: error -/
  | unlockErr (t : Tid) (l : Loc)
  /-- `rd l` of a lock location: a query -/
  | query (t : Tid) (l : Loc)
  /-- `rd x` of a data location -/
  | rd (t : Tid) (x : Loc)
  /-- `wr x v` -/
  | wr (t : Tid) (x : Loc) (v : Val)
  /-- `assume x v`, the value held: continue -/
  | asmOk (t : Tid) (x : Loc) (v : Val)
  /-- `assume x v`, the value did not hold: assume-stopped -/
  | asmStop (t : Tid) (x : Loc) (v : Val)
  /-- `start u` -/
  | start (t : Tid) (u : Tid)
  /-- `join u`, returning -/
  | join (t : Tid) (u : Tid)
  /-- `end`: the code is exhausted -/
  | fin (t : Tid)
  deriving DecidableEq, Repr

/-- The thread of an occurrence. -/
def Occ.tid : Occ → Tid
  | .begin t | .acq t _ | .reacq t _ | .tryAcq t _ _ | .tryFail t _ _ | .tryRe t _ _
  | .unlockRe t _ | .release t _ | .unlockErr t _ | .query t _ | .rd t _ | .wr t _ _
  | .asmOk t _ _ | .asmStop t _ _ | .start t _ | .join t _ | .fin t => t

/-! ### Enabledness (the table of §5) and effect -/

/-- The occurrence `o` is enabled in `s` (one constructor per row of the table of §5).
Every call step and `end` require status `running` and the call at the program counter;
`begin` requires status `new` and started. -/
inductive Enabled (P : LProg) (s : MState) : Occ → Prop
  | begin {t : Tid} (ht : t ∈ P.threads) (hs : s.status t = .new) (h : s.started t = true) :
      Enabled P s (.begin t)
  | acq {t : Tid} {l : Loc} (ht : t ∈ P.threads) (hs : s.status t = .running)
      (hc : (s.rest t).head? = some (.lock l)) (hh : s.heldB t l = false) (hf : s.count l = 0) :
      Enabled P s (.acq t l)
  | reacq {t : Tid} {l : Loc} (ht : t ∈ P.threads)
      (hs : s.status t = .running) (hc : (s.rest t).head? = some (.lock l))
      (hh : s.heldB t l = true) :
      Enabled P s (.reacq t l)
  | tryAcq {t : Tid} {l : Loc} {k : ℕ} (ht : t ∈ P.threads)
      (hs : s.status t = .running) (hc : (s.rest t).head? = some (.tryLock l k))
      (hh : s.heldB t l = false) (hf : s.count l = 0) :
      Enabled P s (.tryAcq t l k)
  | tryFail {t : Tid} {l : Loc} {k : ℕ} (ht : t ∈ P.threads)
      (hs : s.status t = .running) (hc : (s.rest t).head? = some (.tryLock l k))
      (hh : s.heldB t l = false) (hf : s.count l ≠ 0) :
      Enabled P s (.tryFail t l k)
  | tryRe {t : Tid} {l : Loc} {k : ℕ} (ht : t ∈ P.threads)
      (hs : s.status t = .running) (hc : (s.rest t).head? = some (.tryLock l k))
      (hh : s.heldB t l = true) :
      Enabled P s (.tryRe t l k)
  | unlockRe {t : Tid} {l : Loc} (ht : t ∈ P.threads)
      (hs : s.status t = .running) (hc : (s.rest t).head? = some (.unlock l))
      (hh : s.heldB t l = true)
      (h1 : 1 < s.count l) :
      Enabled P s (.unlockRe t l)
  | release {t : Tid} {l : Loc} (ht : t ∈ P.threads)
      (hs : s.status t = .running) (hc : (s.rest t).head? = some (.unlock l))
      (hh : s.heldB t l = true)
      (h1 : s.count l = 1) :
      Enabled P s (.release t l)
  | unlockErr {t : Tid} {l : Loc} (ht : t ∈ P.threads)
      (hs : s.status t = .running) (hc : (s.rest t).head? = some (.unlock l))
      (hh : s.heldB t l = false) :
      Enabled P s (.unlockErr t l)
  | query {t : Tid} {l : Loc} (ht : t ∈ P.threads)
      (hs : s.status t = .running) (hc : (s.rest t).head? = some (.rd l)) (hl : P.isLock l = true) :
      Enabled P s (.query t l)
  | rd {t : Tid} {x : Loc} (ht : t ∈ P.threads)
      (hs : s.status t = .running) (hc : (s.rest t).head? = some (.rd x))
      (hl : P.isLock x = false) :
      Enabled P s (.rd t x)
  | wr {t : Tid} {x : Loc} {v : Val} (ht : t ∈ P.threads)
      (hs : s.status t = .running) (hc : (s.rest t).head? = some (.wr x v)) :
      Enabled P s (.wr t x v)
  | asmOk {t : Tid} {x : Loc} {v : Val} (ht : t ∈ P.threads)
      (hs : s.status t = .running) (hc : (s.rest t).head? = some (.assume x v)) (hv : s.mem x = v) :
      Enabled P s (.asmOk t x v)
  | asmStop {t : Tid} {x : Loc} {v : Val} (ht : t ∈ P.threads)
      (hs : s.status t = .running) (hc : (s.rest t).head? = some (.assume x v)) (hv : s.mem x ≠ v) :
      Enabled P s (.asmStop t x v)
  | start {t u : Tid} (ht : t ∈ P.threads)
      (hs : s.status t = .running) (hc : (s.rest t).head? = some (.start u)) :
      Enabled P s (.start t u)
  | join {t u : Tid} (ht : t ∈ P.threads)
      (hs : s.status t = .running) (hc : (s.rest t).head? = some (.join u))
      (hj : s.joinOkB u = true) :
      Enabled P s (.join t u)
  | fin {t : Tid} (ht : t ∈ P.threads) (hs : s.status t = .running) (hc : s.rest t = []) :
      Enabled P s (.fin t)

/-- The effect of an occurrence (the effect column of the table of §5). -/
def eff (s : MState) : Occ → MState
  | .begin t => s.setSt t .running
  | .acq t l | .tryAcq t l _ =>
    { s.adv t (s.rest t).tail with
      owner := Function.update s.owner l (some t), count := Function.update s.count l 1 }
  | .reacq t l | .tryRe t l _ =>
    { s.adv t (s.rest t).tail with count := Function.update s.count l (s.count l + 1) }
  | .tryFail t _ k => s.adv t ((s.rest t).tail.drop k)
  | .unlockRe t l =>
    { s.adv t (s.rest t).tail with count := Function.update s.count l (s.count l - 1) }
  | .release t l =>
    { s.adv t (s.rest t).tail with
      owner := Function.update s.owner l none, count := Function.update s.count l 0 }
  | .unlockErr t _ => s.setSt t .erred
  | .query t _ | .rd t _ | .asmOk t _ _ | .join t _ => s.adv t (s.rest t).tail
  | .wr t x v => { s.adv t (s.rest t).tail with mem := Function.update s.mem x v }
  | .asmStop t _ _ => s.setSt t .stopped
  | .start t u => { s.adv t (s.rest t).tail with started := Function.update s.started u true }
  | .fin t => s.setSt t .term

/-- A step: an enabled occurrence and its effect. -/
def Step (P : LProg) (s : MState) (o : Occ) (s' : MState) : Prop := Enabled P s o ∧ s' = eff s o

/-- The executable enabledness: the enabled occurrence of thread `t`, if any. -/
def next (P : LProg) (s : MState) (t : Tid) : Option Occ :=
  match s.status t with
  | .new => if s.started t then some (.begin t) else none
  | .running =>
    match (s.rest t).head? with
    | none => some (.fin t)
    | some (.lock l) =>
      if s.heldB t l then some (.reacq t l)
      else if s.count l = 0 then some (.acq t l) else none
    | some (.tryLock l k) =>
      if s.heldB t l then some (.tryRe t l k)
      else if s.count l = 0 then some (.tryAcq t l k) else some (.tryFail t l k)
    | some (.unlock l) =>
      if s.heldB t l then (if 1 < s.count l then some (.unlockRe t l) else some (.release t l))
      else some (.unlockErr t l)
    | some (.rd x) => if P.isLock x then some (.query t x) else some (.rd t x)
    | some (.wr x v) => some (.wr t x v)
    | some (.assume x v) => if s.mem x = v then some (.asmOk t x v) else some (.asmStop t x v)
    | some (.start u) => some (.start t u)
    | some (.join u) => if s.joinOkB u then some (.join t u) else none
  | _ => none

/-- The enabled occurrences, in the order of the threads. -/
def enabledL (P : LProg) (s : MState) : List Occ := P.threads.filterMap (next P s)

/-! ### Footprints and dependency -/

/-- Resources. -/
inductive Res where
  | lock (l : Loc)
  | data (x : Loc)
  | life (t : Tid)
  deriving DecidableEq, Repr

/-- The footprint of an occurrence: resources with `true` for a write, `false` for a
read (the table of §5). -/
def fp : Occ → List (Res × Bool)
  | .begin t => [(.life t, false)]
  | .acq _ l | .tryAcq _ l _ => [(.lock l, false), (.lock l, true)]
  | .reacq _ _ | .tryRe _ _ _ | .unlockRe _ _ | .unlockErr _ _ => []
  | .tryFail _ l _ => [(.lock l, false)]
  | .release _ l => [(.lock l, true)]
  | .query _ l => [(.lock l, false)]
  | .rd _ x | .asmOk _ x _ | .asmStop _ x _ => [(.data x, false)]
  | .wr _ x _ => [(.data x, true)]
  | .start _ u => [(.life u, true)]
  | .join _ u => [(.life u, false)]
  | .fin t => [(.life t, true)]

/-- Two occurrences are dependent: same thread, or they share a resource that at least one
of them writes. -/
def Dep (a b : Occ) : Prop :=
  a.tid = b.tid ∨ ∃ p ∈ fp a, ∃ q ∈ fp b, p.1 = q.1 ∧ (p.2 = true ∨ q.2 = true)

instance (a b : Occ) : Decidable (Dep a b) := by unfold Dep; infer_instance

theorem Dep.symm {a b : Occ} (h : Dep a b) : Dep b a := by
  rcases h with h | ⟨p, hp, q, hq, h1, h2⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨q, hq, p, hp, h1.symm, h2.symm⟩

/-- One swap of two adjacent independent occurrences. -/
inductive Swap : List Occ → List Occ → Prop
  | swap (u v : List Occ) (a b : Occ) (h : ¬ Dep a b) : Swap (u ++ a :: b :: v) (u ++ b :: a :: v)

/-- Mazurkiewicz equivalence of runs: the least equivalence closed under swapping adjacent
independent occurrences. -/
def MEquiv : List Occ → List Occ → Prop := Relation.EqvGen Swap

/-! ### Runs -/

/-- `Steps P s rs s'`: the run `rs` (chronological) leads from `s` to `s'`. -/
inductive Steps (P : LProg) : MState → List Occ → MState → Prop
  | nil (s : MState) : Steps P s [] s
  | cons {s s1 s2 : MState} {o : Occ} {rs : List Occ} (h : Step P s o s1)
      (hr : Steps P s1 rs s2) : Steps P s (o :: rs) s2

/-- No occurrence is enabled. -/
def Maximal (P : LProg) (s : MState) : Prop := ∀ o, ¬ Enabled P s o

/-- A maximal run from the initial state, ending in `s`. -/
def MaxRun (P : LProg) (rs : List Occ) (s : MState) : Prop :=
  Steps P (MState.init P) rs s ∧ Maximal P s

/-! ### Run to graph -/

/-- The graph under construction: the events (newest first), `rf`, `co` (run order of the
writes), and the number of events of each thread. -/
structure GB where
  order : List TEv
  rf : TEv → Option Ev
  co : Loc → List TEv
  cnt : Tid → ℕ

namespace GB

/-- Nothing emitted. -/
def empty : GB := ⟨[], fun _ => none, fun _ => [], fun _ => 0⟩

variable (g : GB)

/-- The last write to `x` so far, else `init`. -/
def last (x : Loc) : Ev :=
  match (g.co x).getLast? with
  | some w => .th w
  | none => .init

/-- The next event of thread `t`, with label `a`. -/
def ev (t : Tid) (a : Act) : TEv := ⟨t, g.cnt t, a⟩

/-- Add the event `e` of thread `e.tid`. -/
def push (e : TEv) : GB :=
  { g with order := e :: g.order, cnt := Function.update g.cnt e.tid (g.cnt e.tid + 1) }

/-- Emit a read of `x` from `src`. -/
def read (t : Tid) (x : Loc) (src : Ev) : GB :=
  let e := g.ev t (.read x)
  { g.push e with rf := fun e' => if e' = e then some src else g.rf e' }

/-- Emit a read of `x` from the last write to `x`. -/
def readLast (t : Tid) (x : Loc) : GB := g.read t x (g.last x)

/-- Emit a write of `v` to `x`, last in the coherence order of `x`. -/
def write (t : Tid) (x : Loc) (v : Val) : GB :=
  let e := g.ev t (.write x v)
  { g.push e with co := Function.update g.co x (g.co x ++ [e]) }

/-- Emit an event without location (`gen 0`, `block`, `error`). -/
def loc0 (t : Tid) (a : Act) : GB := g.push (g.ev t a)

end GB

/-- The events emitted by an occurrence (the compiled events of the call, §2.1). -/
def emit (P : LProg) (g : GB) : Occ → GB
  | .begin t => g.readLast t (P.st t)
  | .acq t l | .tryAcq t l _ => (g.readLast t l).write t l 1
  | .reacq t _ | .tryRe t _ _ | .unlockRe t _ => g.loc0 t (.gen 0)
  | .tryFail t l _ => g.readLast t l
  | .release t l => g.write t l 0
  | .unlockErr t _ => g.loc0 t .error
  | .query t l => g.readLast t l
  | .rd t x | .asmOk t x _ => g.readLast t x
  | .wr t x v => g.write t x v
  | .asmStop t x _ => (g.readLast t x).loc0 t .block
  | .start t u => g.write t (P.st u) 1
  | .join t u => g.readLast t (P.st u)
  | .fin t => g.write t (P.st t) 2

/-- The synthetic final events of thread `t`, by exclusive cases on its status: a new thread
emits `read (st t) ← init; block`; a running thread at a disabled `lock l` emits the read of
`l` from the last write of `l` and `block`; a running thread at a disabled `join u` emits
the read of `st u` from the last write of `st u` and `block`; otherwise nothing. -/
def synth (P : LProg) (s : MState) (g : GB) (t : Tid) : GB :=
  match s.status t with
  | .new => (g.read t (P.st t) .init).loc0 t .block
  | .running =>
    match s.rest t with
    | .lock l :: _ =>
      if !s.heldB t l && decide (s.count l ≠ 0) then (g.readLast t l).loc0 t .block else g
    | .join u :: _ => if !s.joinOkB u then (g.readLast t (P.st u)).loc0 t .block else g
    | _ => g
  | _ => g

/-- The final graph: the synthetic events of every thread added. -/
def finalize (P : LProg) (g : GB) (s : MState) : GB := P.threads.foldl (synth P s) g

/-- A built graph as a configuration (memory `lifeMem P`, no constraint evaluations). -/
def GB.toCfg (P : LProg) (g : GB) : Config := ⟨lifeMem P, g.order, g.rf, g.co, fun _ => none⟩

/-- The graph of the run `rs` that ends in `s`. -/
def runCfg (P : LProg) (rs : List Occ) (s : MState) : Config :=
  (finalize P (rs.foldl (emit P) GB.empty) s).toCfg P

/-! ### Final-state class (gate clause 1) -/

/-- The machine classes. -/
inductive MCls where
  | error | blocked | deadlock | complete
  deriving DecidableEq, Repr

/-- The classes of §3 that the machine classes name. -/
def MCls.toL : MCls → LCls
  | .error => .error
  | .blocked => .blocked
  | .deadlock => .deadlock
  | .complete => .complete

/-- A running thread at a disabled `lock` or `join`. -/
def atDisabled (s : MState) (t : Tid) : Bool :=
  decide (s.status t = .running) &&
    match s.rest t with
    | .lock l :: _ => !s.heldB t l && decide (s.count l ≠ 0)
    | .join u :: _ => !s.joinOkB u
    | _ => false

/-- The class of a final state: some thread erred: error; else some thread assume-stopped:
blocked; else some running thread at a disabled `lock` or `join`: deadlock; else
complete. -/
def mclass (P : LProg) (s : MState) : MCls :=
  if P.threads.any (fun t => decide (s.status t = .erred)) then .error
  else if P.threads.any (fun t => decide (s.status t = .stopped)) then .blocked
  else if P.threads.any (atDisabled s) then .deadlock
  else .complete

/-! ### Enumeration of the maximal runs -/

/-- Depth-first enumeration with fuel: the graph and class at every maximal state reached. -/
def runsF (P : LProg) : ℕ → MState → GB → List (Config × MCls)
  | 0, _, _ => []
  | f + 1, s, g =>
    match enabledL P s with
    | [] => [((finalize P g s).toCfg P, mclass P s)]
    | os => os.flatMap (fun o => runsF P f (eff s o) (emit P g o))

/-- Enough fuel: every step consumes one unit of `|code t| + 2` of some thread. -/
def fuel (P : LProg) : ℕ := (P.threads.map (fun t => (P.code t).length + 2)).sum + 1

/-- The graphs and classes of all maximal runs. -/
def machRuns (P : LProg) : List (Config × MCls) := runsF P (fuel P) (MState.init P) GB.empty

/-! ### Gate clauses (§5), stated, not proved in LC2-a -/

/-- Clause 1: the graph of every maximal run is a well-formed full execution of `lifeSys`,
SC-consistent and atomic, and its class is the one given by the final machine state (so it
is terminal-valid: neither cut nor exploration). -/
def Gate1 : Prop :=
  ∀ (P : LProg) (n : ℕ), fragB P = true → adequateB P n = true →
    ∀ rs s, MaxRun P rs s →
      (runCfg P rs s).Wf ∧ (lifeSys P n).toProgram.Exec (runCfg P rs s).abs ∧
        ((Model.atomic (lifeSys P n) SC).sym EqSem.solver).cons (runCfg P rs s).abs ∧
        (lifeSys P n).toProgram.Full (runCfg P rs s).abs ∧
        lifeClass P (runCfg P rs s) = (mclass P s).toL

/-- Clause 2: every terminal-valid full graph of `lifeSys` is the graph of a maximal run. -/
def Gate2 : Prop :=
  ∀ (P : LProg) (n : ℕ), fragB P = true → adequateB P n = true →
    ∀ c : Config, c.Wf → (lifeSys P n).toProgram.Exec c.abs →
      ((Model.atomic (lifeSys P n) SC).sym EqSem.solver).cons c.abs →
      (lifeSys P n).toProgram.Full c.abs →
      lifeClass P c ≠ .cut → lifeClass P c ≠ .exploration →
      ∃ rs s, MaxRun P rs s ∧ (runCfg P rs s).abs = c.abs

/-- Clause 3: two maximal runs have the same graph iff they are Mazurkiewicz-equivalent. -/
def Gate3 : Prop :=
  ∀ P : LProg, fragB P = true →
    ∀ rs₁ s₁ rs₂ s₂, MaxRun P rs₁ s₁ → MaxRun P rs₂ s₂ →
      ((runCfg P rs₁ s₁).abs = (runCfg P rs₂ s₂).abs ↔ MEquiv rs₁ rs₂)

/-! ### Comparison with `lifeSys`: a canonical serialization -/

/-- The serialization of a graph over the threads `ts`: per thread, its events by index,
each with its `rf` value; then, for every location written (the write locations of that
list, without repetition by `List.dedup`, a function of the list), its coherence order. -/
abbrev Ser := List (List (TEv × Option Ev)) × List (Loc × List TEv)

instance : DecidableEq Ser :=
  inferInstanceAs (DecidableEq (List (List (TEv × Option Ev)) × List (Loc × List TEv)))

/-- The serialization of a configuration. -/
def ser (ts : List Tid) (c : Config) : Ser :=
  let evs := ts.map (fun t => (thEvents c t).map (fun e => (e, c.rf e)))
  let locs := (evs.flatten.filterMap (fun p => match p.1.act with
    | .write x _ => some x
    | _ => none)).dedup
  (evs, locs.map (fun x => (x, c.co x)))

/-- The machine side: serializations of the graphs of all maximal runs with their classes,
without repetition. -/
def machSide (P : LProg) : List (Ser × LCls) :=
  ((machRuns P).map (fun p => (ser P.threads p.1, p.2.toL))).dedup

/-- `lifeSys` is terminal-valid on a configuration: neither cut nor exploration. -/
def termValid (P : LProg) (c : Config) : Bool :=
  decide (lifeClass P c ≠ .cut) && decide (lifeClass P c ≠ .exploration)

/-- The `lifeSys` side: serializations of the terminal-valid graphs of the explorer with
their `lifeClass`. -/
def lifeSide (P : LProg) (n : ℕ) : List (Ser × LCls) :=
  ((exploreCfgAtF (lifeSys P n) n).filter (termValid P)).map
    (fun c => (ser P.threads c, lifeClass P c))

/-- Equality as sets. -/
def sameSet {α : Type} [DecidableEq α] (a b : List α) : Bool := a.all (· ∈ b) && b.all (· ∈ a)

/-- Counts per class (error, blocked, deadlock, complete). -/
def clsCounts (l : List (Ser × LCls)) : List ℕ :=
  [.error, .blocked, .deadlock, .complete].map
    (fun k => (l.filter (fun p => decide (p.2 = k))).length)

/-- What a comparison states: the two sides are equal as sets; the class counts of the
machine side (deduplicated) and of the `lifeSys` side, and the number of distinct
serializations on the `lifeSys` side (equal to its length: the serialization separates its
graphs). -/
def cmp (P : LProg) (n : ℕ) : Bool × List ℕ × List ℕ × ℕ :=
  let m := machSide P
  let l := lifeSide P n
  (sameSet m l, clsCounts m, clsCounts l, l.dedup.length)

/-! ### A merged enumeration, for larger programs

`runsM` explores the runs layer by layer (a layer = the states after the same number of
steps) and keeps one representative of the pairs (machine state, graph so far) with the same
key `keyOf`. The key consists of the serialization of the graph so far and the state on
the threads, the lock locations and the locations named by calls; the rest of the state does
not change along a run (owner, count only change on locks named by lock calls, the memory only
on `wr` locations). Its graphs are those of `runsF` when the key determines all future
graphs; that is not proved here: the theorem `machSideM_small` in `LifecycleSemCheck.lean` compares
`machSideM` with `machSide` by kernel evaluation on the programs where both evaluate. -/

/-- The locations named by the calls of the program. -/
def callLocs (P : LProg) : List Loc :=
  (P.threads.flatMap (fun t => (P.code t).filterMap (fun c => match c with
    | .lock l | .tryLock l _ | .unlock l | .rd l | .wr l _ | .assume l _ => some l
    | _ => none))).dedup

/-- The key of a pair (state, graph so far). -/
def keyOf (P : LProg) (s : MState) (g : GB) :
    Ser × List (Status × Bool × List TOp) × List (Option Tid × ℕ × Val) :=
  (ser P.threads (g.toCfg P), P.threads.map (fun t => (s.status t, s.started t, s.rest t)),
    (callLocs P).map (fun l => (s.owner l, s.count l, s.mem l)))

/-- Keep the first pair of every key. -/
def dedupKey (P : LProg) (l : List (MState × GB)) : List (MState × GB) :=
  (l.foldl (fun (acc : List (MState × GB) × List _) p =>
    let k := keyOf P p.1 p.2
    if k ∈ acc.2 then acc else (p :: acc.1, k :: acc.2)) ([], [])).1

/-- Layer by layer, with fuel. -/
def runsM (P : LProg) : ℕ → List (MState × GB) → List (Config × MCls)
  | 0, _ => []
  | f + 1, fr =>
    (fr.filter (fun p => (enabledL P p.1).isEmpty)).map
        (fun p => ((finalize P p.2 p.1).toCfg P, mclass P p.1)) ++
      runsM P f (dedupKey P (fr.flatMap (fun p =>
        (enabledL P p.1).map (fun o => (eff p.1 o, emit P p.2 o)))))

/-- The machine side by the merged enumeration. -/
def machSideM (P : LProg) : List (Ser × LCls) :=
  ((runsM P (fuel P) [(MState.init P, GB.empty)]).map (fun p => (ser P.threads p.1, p.2.toL))).dedup

/-- `cmp` with the merged enumeration. -/
def cmpM (P : LProg) (n : ℕ) : Bool × List ℕ × List ℕ × ℕ :=
  let m := machSideM P
  let l := lifeSide P n
  (sameSet m l, clsCounts m, clsCounts l, l.dedup.length)

end Sem

end Life

end Condpor
