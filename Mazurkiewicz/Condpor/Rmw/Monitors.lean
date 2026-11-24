import Mazurkiewicz.Condpor.Rmw.Locks

/-!
# Monitors: `wait`, `notify`, `notifyAll`, `signal`, returns without notification

A monitor is a location. Its value is `1` (held) or `2 * code σ` (free), where
`σ` lists, for the wait set number `i` of the monitor (number `0` for
`Object.wait`, one number for each condition of a lock), a component
`(c, a, T, S, W)`:

* `c`: the number of notification generations;
* `a`: the value of `c` at the last `notifyAll` (`0` if none);
* `T`: the numbers of the notifications of `notify` not yet consumed,
  increasing;
* `S`: the waiters chosen by `signal` that have not returned yet;
* `W`: the waiters that return by a notification only, in order of entry, each
  with its entry number (the value of `c` when it waited).

The owner of the monitor has `σ` (it read it when it acquired) and writes it
when it releases. `notify`, `signal` and `notifyAll` are local steps of the
owner. `notify` issues a notification iff some waiter of `W` has none: which
waiter takes it is decided by the race for the monitor. `signal` chooses the
first waiter of `W` without one. The wait set `0` is notified by `notify`
only, a wait set `i > 0` by `signal` only: the call `notify l i` of a thread
is the one or the other.

`wait` first decides how it returns, by the evaluation of constraints on fresh
symbols while the thread has budget (`kt` time-outs for a timed wait, `ks`
spurious returns for any wait): timed out, spuriously, or by a notification.
Then it writes the release, entering `W` in the last case only, and reads the
monitor exclusively: it proceeds (exclusive write of `1`) if the value is free
and, in the last case, it has a notification; otherwise it blocks.

Local steps of a thread (a nested `lock` or `unlock`, `notify`, `signal`,
`notifyAll`) are `gen 0` events of the graph: they have no counterpart in a
graph of memory accesses and do not change the number of graphs. A call
without holding the monitor is an `error` event, which ends the thread.
-/

namespace Condpor

open Program

/-! ### The component of a wait set -/

/-- `(c, a, T, S, W)`. -/
structure WComp where
  c : ℕ
  a : ℕ
  T : List ℕ
  S : List Tid
  W : List (Tid × ℕ)
  deriving DecidableEq, Repr

namespace WComp

/-- The component of a wait set never used. -/
def init : WComp := ⟨0, 0, [], [], []⟩

/-- The entry number of `t` (`0` if `t` does not wait). -/
def entry (k : WComp) (t : Tid) : ℕ :=
  match k.W.find? (fun w => w.1 = t) with
  | some w => w.2
  | none => 0

/-- The waiters without a `notifyAll` and without a `signal`, in order of
entry. -/
def pending (k : WComp) : List (Tid × ℕ) :=
  k.W.filter (fun w => k.a ≤ w.2 ∧ w.1 ∉ k.S)

/-- `wait` of `t`. -/
def wait (k : WComp) (t : Tid) : WComp := { k with W := k.W ++ [(t, k.c)] }

/-- `notify`: a notification is issued iff some waiter has none. -/
def notify (k : WComp) : WComp :=
  if k.T.length < k.pending.length then { k with c := k.c + 1, T := k.T ++ [k.c + 1] } else k

/-- `signal`: the first waiter without a notification is chosen. -/
def signal (k : WComp) : WComp :=
  match k.pending.head? with
  | some w => { k with S := k.S ++ [w.1] }
  | none => k

/-- `notifyAll`. -/
def notifyAll (k : WComp) : WComp := { k with c := k.c + 1, a := k.c + 1, T := [], S := [] }

/-- The waiters without `t`. -/
def drop (k : WComp) (t : Tid) : List (Tid × ℕ) := k.W.filter (fun w => w.1 ≠ t)

/-- The return of the waiter `t`, if it has a notification: by `notifyAll`,
by `signal`, or by the least notification of `notify` after its entry. -/
def exitN (k : WComp) (t : Tid) : Option WComp :=
  if k.entry t < k.a then some { k with W := k.drop t }
  else if t ∈ k.S then some { k with S := k.S.erase t, W := k.drop t }
  else
    match (k.T.filter (fun j => k.entry t < j)).head? with
    | some j => some { k with T := k.T.erase j, W := k.drop t }
    | none => none

end WComp

/-! ### The code of a monitor state -/

/-- The list of numbers of a component. -/
def WComp.flat (k : WComp) : List ℕ :=
  [k.c, k.a, k.T.length] ++ k.T ++ [k.S.length] ++ k.S ++ [k.W.length] ++
    k.W.flatMap (fun w => [w.1, w.2])

/-- The pairs of a list of numbers. -/
def unflatPairs : ℕ → List ℕ → List (Tid × ℕ) × List ℕ
  | 0, l => ([], l)
  | n + 1, t :: g :: l => ((t, g) :: (unflatPairs n l).1, (unflatPairs n l).2)
  | _ + 1, l => ([], l)

/-- The component at the head of a list of numbers, and the rest. -/
def WComp.unflat : List ℕ → WComp × List ℕ
  | c :: a :: nT :: l =>
    match l.drop nT with
    | nS :: l' =>
      match l'.drop nS with
      | nW :: l'' =>
        (⟨c, a, l.take nT, l'.take nS, (unflatPairs nW l'').1⟩, (unflatPairs nW l'').2)
      | [] => (⟨c, a, l.take nT, l'.take nS, []⟩, [])
    | [] => (⟨c, a, l.take nT, [], []⟩, [])
  | _ => (WComp.init, [])

/-- The components of a list of numbers. -/
def unflatAll : ℕ → List ℕ → List WComp
  | 0, _ => []
  | n + 1, l => (WComp.unflat l).1 :: unflatAll n (WComp.unflat l).2

/-- The number of a list of numbers: each `n` is `n` digits `1` and a digit
`0`, the first number in the lowest digits, under a leading `1`. -/
def listCode : List ℕ → ℕ
  | [] => 1
  | n :: l => (listCode l * 2) * 2 ^ n + (2 ^ n - 1)

/-- The list of a number, with `fuel` steps. -/
def listDecode : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | fuel + 1, m, acc =>
    if m ≤ 1 then []
    else if m % 2 = 1 then listDecode fuel (m / 2) (acc + 1)
    else acc :: listDecode fuel (m / 2) 0

/-- A monitor state: the components of its wait sets. -/
abbrev Sig := List WComp

/-- The code of a monitor state; the state without components has the code
`0`. -/
def sigCode (σ : Sig) : ℕ :=
  if σ = [] then 0 else listCode (σ.length :: σ.flatMap WComp.flat)

/-- The monitor state of a code. -/
def sigDecode (m : ℕ) : Sig :=
  match listDecode (m + 1) m 0 with
  | n :: l => unflatAll n l
  | [] => []

/-- The component `i`. -/
def Sig.get (σ : Sig) (i : ℕ) : WComp := σ.getD i WComp.init

/-- The state with the component `i` replaced. -/
def Sig.put (σ : Sig) (i : ℕ) (k : WComp) : Sig :=
  (σ ++ List.replicate (i + 1 - σ.length) WComp.init).set i k

/-! ### Threads -/

/-- A call of a thread. -/
inductive MOp where
  | lock (l : Loc)
  | tryLock (l : Loc) (k : ℕ)
  | unlock (l : Loc)
  /-- wait on the wait set `i` of the monitor `l` -/
  | wait (l : Loc) (i : ℕ)
  /-- the same with a positive time; on a time-out skip the next `k` calls -/
  | waitT (l : Loc) (i : ℕ) (k : ℕ)
  /-- `Object.notify` on the wait set `0`; `Condition.signal` on a wait set
  `i > 0` -/
  | notify (l : Loc) (i : ℕ)
  | notifyAll (l : Loc) (i : ℕ)
  | rd (x : Loc)
  | wr (x : Loc) (v : Val)
  /-- the evaluation of the constraint `s = k` on the symbol `s` of the program -/
  | ev (s k : ℕ)
  deriving DecidableEq, Repr

/-- What the thread does next, apart from the remaining calls. -/
inductive MPhase where
  | ready
  /-- the exclusive write of an acquire; the hold count becomes `h` -/
  | acquire (l : Loc) (h : ℕ)
  | blocking
  /-- a wait that has not timed out: the choice of a spurious return, if any -/
  | spur (l : Loc) (i : ℕ)
  /-- the release write of a wait; `b`: it returns without notification -/
  | release (l : Loc) (i : ℕ) (b : Bool)
  /-- the exclusive read of a waiter; `h`: its hold count before the wait -/
  | waiting (l : Loc) (i : ℕ) (b : Bool) (h : ℕ)
  deriving DecidableEq, Repr

/-- The state of a thread. `ks`: the spurious returns it may still choose;
`kt`: the time-outs it may still choose; `nch`: the number of its choices. -/
structure MState where
  tid : Tid
  ops : List MOp
  holds : Loc → ℕ
  sig : Loc → Sig
  phase : MPhase
  ks : ℕ
  kt : ℕ
  nch : ℕ

/-- The symbol of the choice number `n` of the thread `t`: odd. The symbol
`s` of the program is `2 * s`. -/
def choiceSym (t : Tid) (n : ℕ) : ℕ := 2 * Nat.pair t n + 1

/-- The value of a free monitor with the state `σ`. -/
def freeVal (σ : Sig) : Val := 2 * sigCode σ

/-- The release write of a wait. -/
def MState.waitWrite (s : MState) (l : Loc) (i : ℕ) (b : Bool) : Act :=
  if b then .write l (freeVal (s.sig l))
  else .write l (freeVal ((s.sig l).put i (((s.sig l).get i).wait s.tid)))

/-- The action of a wait that has not timed out. -/
def MState.spurAct (s : MState) (l : Loc) (i : ℕ) : Act :=
  if 0 < s.ks then .cons (fEq (choiceSym s.tid s.nch) 1) else s.waitWrite l i false

/-- The state after `spurAct` returned `v`. -/
def MState.spurNext (s : MState) (l : Loc) (i : ℕ) (v : Option Val) : MState :=
  if 0 < s.ks then
    (if v = some 1 then
      { s with phase := .release l i true, ks := s.ks - 1, nch := s.nch + 1 }
    else { s with phase := .release l i false, nch := s.nch + 1 })
  else
    { s with holds := Function.update s.holds l 0, phase := .waiting l i false (s.holds l) }

/-- The next action of a thread in a state. -/
def MState.act (s : MState) : Option Act :=
  match s.phase with
  | .acquire l _ => some (.write l 1)
  | .blocking => some .block
  | .spur l i => some (s.spurAct l i)
  | .release l i b => some (s.waitWrite l i b)
  | .waiting l _ _ _ => some (.read l)
  | .ready =>
    match s.ops with
    | [] => none
    | .lock l :: _ => if s.holds l = 0 then some (.read l) else some (.gen 0)
    | .tryLock l _ :: _ => if s.holds l = 0 then some (.read l) else some (.gen 0)
    | .unlock l :: _ =>
      if s.holds l = 0 then some .error
      else if s.holds l = 1 then some (.write l (freeVal (s.sig l))) else some (.gen 0)
    | .wait l i :: _ => if s.holds l = 0 then some .error else some (s.spurAct l i)
    | .waitT l i _ :: _ =>
      if s.holds l = 0 then some .error
      else if 0 < s.kt then some (.cons (fEq (choiceSym s.tid s.nch) 1))
      else some (s.spurAct l i)
    | .notify l _ :: _ => if s.holds l = 0 then some .error else some (.gen 0)
    | .notifyAll l _ :: _ => if s.holds l = 0 then some .error else some (.gen 0)
    | .rd x :: _ => some (.read x)
    | .wr x v :: _ => some (.write x v)
    | .ev a k :: _ => some (.cons (fEq (2 * a) k))

/-- The next action is exclusive. -/
def MState.isEx (s : MState) : Bool :=
  match s.phase with
  | .acquire _ _ => true
  | .waiting _ _ _ _ => true
  | .blocking => false
  | .spur _ _ => false
  | .release _ _ _ => false
  | .ready =>
    match s.ops with
    | .lock l :: _ => decide (s.holds l = 0)
    | .tryLock l _ :: _ => decide (s.holds l = 0)
    | _ => false

/-- The state after a local step on the component `i` of `l`. -/
def MState.local (s : MState) (rest : List MOp) (l : Loc) (i : ℕ) (f : WComp → WComp) :
    MState :=
  if s.holds l = 0 then { s with ops := rest }
  else
    { s with ops := rest,
             sig := Function.update s.sig l ((s.sig l).put i (f ((s.sig l).get i))) }

/-- The state after the action of the state returned `v`. -/
def MState.next (s : MState) (v : Option Val) : MState :=
  match s.phase with
  | .acquire l h => { s with holds := Function.update s.holds l h, phase := .ready }
  | .blocking => s
  | .spur l i => s.spurNext l i v
  | .release l i b =>
    { s with holds := Function.update s.holds l 0, phase := .waiting l i b (s.holds l) }
  | .waiting l i b h =>
    match v with
    | some x =>
      if x % 2 = 0 then
        (if b then
          { s with sig := Function.update s.sig l (sigDecode (x / 2)), phase := .acquire l h }
        else
          match ((sigDecode (x / 2)).get i).exitN s.tid with
          | some k =>
            { s with sig := Function.update s.sig l ((sigDecode (x / 2)).put i k),
                     phase := .acquire l h }
          | none => { s with phase := .blocking })
      else { s with phase := .blocking }
    | none => { s with phase := .blocking }
  | .ready =>
    match s.ops with
    | [] => s
    | .lock l :: rest =>
      if s.holds l = 0 then
        (match v with
          | some x =>
            if x % 2 = 0 then
              { s with ops := rest, sig := Function.update s.sig l (sigDecode (x / 2)),
                       phase := .acquire l 1 }
            else { s with ops := rest, phase := .blocking }
          | none => { s with ops := rest, phase := .blocking })
      else { s with ops := rest, holds := Function.update s.holds l (s.holds l + 1) }
    | .tryLock l k :: rest =>
      if s.holds l = 0 then
        (match v with
          | some x =>
            if x % 2 = 0 then
              { s with ops := rest, sig := Function.update s.sig l (sigDecode (x / 2)),
                       phase := .acquire l 1 }
            else { s with ops := rest.drop k }
          | none => { s with ops := rest.drop k })
      else { s with ops := rest, holds := Function.update s.holds l (s.holds l + 1) }
    | .unlock l :: rest =>
      if s.holds l = 0 then { s with ops := rest }
      else { s with ops := rest, holds := Function.update s.holds l (s.holds l - 1) }
    | .wait l i :: rest =>
      if s.holds l = 0 then { s with ops := rest }
      else MState.spurNext { s with ops := rest } l i v
    | .waitT l i k :: rest =>
      if s.holds l = 0 then { s with ops := rest }
      else if 0 < s.kt then
        (if v = some 1 then
          { s with ops := rest.drop k, phase := .release l i true, kt := s.kt - 1,
                   nch := s.nch + 1 }
        else { s with ops := rest, phase := .spur l i, nch := s.nch + 1 })
      else MState.spurNext { s with ops := rest } l i v
    | .notify l i :: rest =>
      s.local rest l i (if i = 0 then WComp.notify else WComp.signal)
    | .notifyAll l i :: rest => s.local rest l i WComp.notifyAll
    | _ :: rest => { s with ops := rest }

/-- The state of the thread `t` with the calls `ops` and the budgets `K`
(spurious returns) and `K'` (time-outs) after the trace `u`. -/
def monState (t : Tid) (ops : List MOp) (K K' : ℕ) (u : List (Option Val)) : MState :=
  u.foldl MState.next ⟨t, ops, fun _ => 0, fun _ => [], .ready, K, K', 0⟩

/-- The table of next actions of a family of threads. -/
def msTab (code : Tid → List MOp) (K K' : ℕ) (t : Tid) (u : List (Option Val)) :
    Option Act :=
  (monState t (code t) K K' u).act

/-- The table of flags. -/
def msFlag (code : Tid → List MOp) (K K' : ℕ) (t : Tid) (u : List (Option Val)) : Bool :=
  (monState t (code t) K K' u).isEx

/-- The program of the threads `threads` with the calls `code`, at most `K`
spurious returns and `K'` time-outs per thread, cut at `n` actions per
thread. -/
def monSys (threads : List Tid) (hnd : threads.Nodup) (code : Tid → List MOp) (K K' n : ℕ) :
    XProgram :=
  mkXProg threads hnd (msTab code K K') (msFlag code K K') (fun _ => 0) n

/-! ### The theorems for monitor programs -/

/-- The computed explorer lists, without repetition, exactly the well-formed
full executions of a monitor program that are SC-consistent and atomic. -/
theorem monSys_explore (threads : List Tid) (hnd : threads.Nodup) (code : Tid → List MOp)
    (K K' n : ℕ) :
    (exploreAt (monSys threads hnd code K K' n) eqOracleSe n).Nodup ∧
      ∀ G, G ∈ exploreAt (monSys threads hnd code K K' n) eqOracleSe n ↔
        G.Wf ∧ (monSys threads hnd code K K' n).toProgram.Exec G ∧
          ((Model.atomic (monSys threads hnd code K K' n) SC).sym EqSem.solver).cons G ∧
          (monSys threads hnd code K K' n).toProgram.Full G :=
  exploreAt_spec eqOracleSe (mkXProg_bounded _ _ _ _ _ _)

/-- Completeness for a monitor program, any solver and tie-break. -/
theorem monSys_complete {S : Solver} {τ : TieBreak S} (threads : List Tid)
    (hnd : threads.Nodup) (code : Tid → List MOp) (K K' n : ℕ) {Gf : Graph} (hGf : Gf.Wf)
    (hEf : (monSys threads hnd code K K' n).toProgram.Exec Gf)
    (hcf : ((Model.atomic (monSys threads hnd code K K' n) SC).sym S).cons Gf)
    (hff : (monSys threads hnd code K K' n).toProgram.Full Gf) :
    ∃ c, Reach (monSys threads hnd code K K' n).toProgram
      ((Model.atomic (monSys threads hnd code K K' n) SC).sym S) τ c ∧ c.abs = Gf :=
  Rmw.complete_sc (mkXProg_bounded _ _ _ _ _ _) hGf hEf hcf hff

/-- No graph of a monitor program is reached twice. -/
theorem monSys_eq_of_abs_eq {S : Solver} {τ : TieBreak S} (threads : List Tid)
    (hnd : threads.Nodup) (code : Tid → List MOp) (K K' n : ℕ) {c1 c2 : Config}
    (h1 : Reach (monSys threads hnd code K K' n).toProgram
      ((Model.atomic (monSys threads hnd code K K' n) SC).sym S) τ c1)
    (h2 : Reach (monSys threads hnd code K K' n).toProgram
      ((Model.atomic (monSys threads hnd code K K' n) SC).sym S) τ c2)
    (h : c1.abs = c2.abs) : c1 = c2 :=
  Rmw.eq_of_abs_eq h1 h2 h

/-- A reached configuration of a monitor program from which no full
configuration is reachable has no step. -/
theorem monSys_blocked_of_fruitless {S : Solver} {τ : TieBreak S} (threads : List Tid)
    (hnd : threads.Nodup) (code : Tid → List MOp) (K K' n : ℕ) {c : Config}
    (hc : Reach (monSys threads hnd code K K' n).toProgram
      ((Model.atomic (monSys threads hnd code K K' n) SC).sym S) τ c)
    (hfr : ¬ ∃ c', Relation.ReflTransGen (Step (monSys threads hnd code K K' n).toProgram
      ((Model.atomic (monSys threads hnd code K K' n) SC).sym S) τ) c c' ∧
      (monSys threads hnd code K K' n).toProgram.Full c'.abs) :
    ¬ ∃ c1, Step (monSys threads hnd code K K' n).toProgram
      ((Model.atomic (monSys threads hnd code K K' n) SC).sym S) τ c c1 :=
  Rmw.blocked_of_fruitless (mkXProg_bounded _ _ _ _ _ _) (SC.extensibleX _)
    (SC.exclExtensible _) hc hfr

end Condpor
