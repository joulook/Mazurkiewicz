import Lean.Data.Json
import Mazurkiewicz.Condpor.Rmw.LifecycleEx

/-!
# Export of the lifecycle targets for JMC (S8L-c step c0)

A script, not a library module: it is not imported by `Mazurkiewicz.lean`, the lakefile or
`Audit.lean`, and it states no theorem. Run it from the repository root with

```
LIFECYCLE_EXPORT_DIR=<dir> [LIFECYCLE_EXPORT_ONLY=name1,name2] \
  lake env lean scripts/LifecycleExport.lean
```

For each program below it evaluates, by the interpreter, the explorer `exploreCfgAtF
(lifeSys P n) n` of `Lifecycle.lean` at the program's bound `n` (the bound of its target
theorem; checked equal to `bnd P`), and writes `<dir>/<name>.json` with

* the program metadata: declared threads, roots, lock locations, the lifecycle location map
  `st`, the data locations (the locations of `rd`/`wr`/`assume` calls that are neither lock
  nor lifecycle locations), the bound, the code of each thread;
* every terminal-valid configuration (class neither `cut` nor `exploration`, as
  `LifecycleSem.termValid`) with its `lifeClass`, computed on the configuration itself,
  before any projection, and its full graph: per thread its events by index with label,
  exclusive flag (`lifeFlag` of the trace before the event), `rf` source and the value read;
  per written location its coherence order (the location
  list of `LifecycleSem.ser`: the write locations in thread/index order, without
  repetition).

Check (fails loudly, the script then ends with an error): the vector computed from the
explored list in the shape of `lifeTarget` (full graphs; class counts cut, exploration,
error, blocked, deadlock, complete, odd; signature counts error, blocked, deadlock,
complete) equals the vector of the program's target theorem, copied below with its source;
`fragB P` and `adequateB P n` hold; the exported configurations have exactly the class
counts error, blocked, deadlock, complete, odd of that vector; every exported event's label
is the compiled table's action `lifeTab` for the trace before it.

The tryjoin, chain, diamond and J7 programs are not exported: they are not theorems and their
interpreter runs take from 23 minutes to more than 2 hours
(`tmp/rmw-review/lc1-external/*.log`).
-/

open Lean Condpor Life Targets

namespace LifeExport

/-- A program to export: name, program, bound, the `lifeTarget` vector of its theorem and
where that theorem is. -/
structure Item where
  name : String
  prog : LProg
  n : Nat
  expect : List Nat
  thm : String

/-- The small Lean targets of `S8Lc-DESIGN.md` §6.3, with the numbers of their theorems. -/
def items : List Item := [
  ⟨"startNoJoin", startNoJoin, 5, [2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    "LifecycleEx.lean startNoJoin_target"⟩,
  ⟨"startJoin", startJoin, 7, [3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    "LifecycleEx.lean startJoin_target"⟩,
  ⟨"neverStarted", neverStarted, 9, [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    "LifecycleEx.lean neverStarted_target"⟩,
  ⟨"joinThenStart", joinThenStart, 9, [3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    "LifecycleEx.lean joinThenStart_target"⟩,
  ⟨"raceJoin", raceJoin, 7, [8, 0, 5, 0, 0, 0, 3, 0, 0, 0, 0, 1],
    "LifecycleEx.lean raceJoin_target"⟩,
  ⟨"errStale", errStale, 7, [2, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    "LifecycleEx.lean errStale_target"⟩,
  ⟨"errTwo", errTwo, 7, [4, 0, 3, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    "LifecycleEx.lean errTwo_target"⟩,
  ⟨"queryData", queryData, 9, [4, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 3],
    "LifecycleEx.lean queryData_target"⟩,
  ⟨"asmRead", asmRead, 9, [4, 0, 2, 0, 1, 0, 1, 0, 0, 1, 0, 1],
    "LifecycleEx.lean asmRead_target"⟩,
  ⟨"asmLockRd", asmLockRd, 7, [1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0],
    "LifecycleEx.lean asmLockRd_target"⟩,
  ⟨"lockAcross", lockAcross, 15, [2, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0],
    "LifecycleEx.lean lockAcross_target"⟩,
  ⟨"joinErr", joinErr, 7, [2, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    "LifecycleEx.lean joinErr_target"⟩,
  ⟨"workerStarts", workerStarts, 9, [8, 0, 6, 0, 0, 0, 2, 0, 0, 0, 0, 1],
    "LifecycleEx.lean workerStarts_target"⟩,
  ⟨"pubVis", pubVis, 11, [3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    "LifecycleEx.lean pubVis_target"⟩,
  ⟨"rptJoin", rptJoin, 9, [3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    "LifecycleEx.lean rptJoin_target"⟩,
  ⟨"nsHeld", nsHeld, 5, [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    "LifecycleEx.lean nsHeld_target"⟩,
  ⟨"nsHeld2", nsHeld2, 7, [2, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0],
    "LifecycleEx.lean nsHeld2_target"⟩,
  ⟨"queryTry", queryTry, 11, [8, 0, 2, 0, 0, 0, 6, 0, 0, 0, 0, 6],
    "LifecycleEx.lean queryTry_target"⟩,
  ⟨"errFinal", errFinal, 13, [8, 0, 7, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    "LifecycleEx.lean errFinal_target"⟩,
  ⟨"asmFinal", asmFinal, 9, [4, 0, 3, 0, 1, 0, 0, 0, 0, 1, 0, 0],
    "LifecycleEx.lean asmFinal_target"⟩,
  ⟨"joinCycle", joinCycle, 7, [7, 0, 5, 0, 0, 1, 1, 0, 0, 0, 1, 1],
    "LifecycleEx.lean joinCycle_target"⟩,
  ⟨"joinUnderLock", joinUnderLock, 11, [5, 0, 3, 0, 0, 1, 1, 0, 0, 0, 1, 1],
    "LifecycleEx.lean joinUnderLock_target"⟩,
  ⟨"twoStarters", twoStarters, 7, [10, 0, 8, 0, 0, 0, 2, 0, 0, 0, 0, 1],
    "LifecycleEx.lean twoStarters_target"⟩,
  ⟨"lateJoin", lateJoin, 11, [5, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    "LifecycleCheck1.lean lateJoin_target"⟩,
  ⟨"reTry", reTry, 15, [8, 0, 5, 0, 0, 0, 3, 0, 0, 0, 0, 3],
    "LifecycleCheck1.lean reTry_target"⟩,
  ⟨"twoJoin", twoJoin, 9, [25, 0, 21, 0, 0, 0, 4, 0, 0, 0, 0, 1],
    "LifecycleCheck1.lean twoJoin_target"⟩,
  ⟨"twoFail", twoFail, 11, [12, 0, 5, 0, 0, 0, 7, 0, 0, 0, 0, 7],
    "LifecycleCheck1.lean twoFail_target"⟩,
  ⟨"asmStale", asmStale, 13, [11, 0, 8, 0, 2, 0, 1, 0, 0, 2, 0, 1],
    "LifecycleCheck1.lean asmStale_target"⟩,
  ⟨"lmin3", lmin3, 13, [15, 0, 13, 0, 0, 0, 2, 0, 0, 0, 0, 2],
    "LifecycleCheck1.lean lmin3_target"⟩,
  ⟨"lmin3e", lmin3e, 11, [16, 0, 13, 0, 0, 0, 3, 0, 0, 0, 0, 3],
    "LifecycleCheck1.lean lmin3e_target"⟩,
  ⟨"creator", creator, 15, [16, 0, 14, 0, 0, 0, 2, 0, 0, 0, 0, 2],
    "LifecycleCheck1.lean creator_target"⟩,
  ⟨"chain2", chain2, 11, [17, 0, 14, 0, 0, 0, 3, 0, 0, 0, 0, 2],
    "LifecycleCheck1.lean chain2_target"⟩,
  ⟨"lowChild", lowChild, 13, [44, 0, 38, 0, 0, 0, 6, 0, 0, 0, 0, 6],
    "LifecycleCheck2.lean lowChild_target"⟩,
  ⟨"dl2", dl2, 11, [17, 0, 14, 0, 0, 1, 2, 0, 0, 0, 1, 2],
    "LifecycleCheck3.lean dl2_target"⟩,
  ⟨"tryjoin2", tryjoin2, 11, [28, 0, 21, 0, 0, 0, 7, 0, 0, 0, 0, 6],
    "LifecycleCheck3.lean tryjoin2_target"⟩,
  ⟨"dl2j", dl2j, 15, [48, 0, 45, 0, 0, 1, 2, 0, 0, 0, 1, 2],
    "LifecycleCheck4.lean dl2j_target"⟩,
  ⟨"diamondB", diamondB, 15, [64, 0, 58, 0, 0, 0, 6, 0, 0, 0, 0, 2],
    "LifecycleCheck5.lean diamondB_target"⟩,
  ⟨"j7b", j7b, 15, [42, 0, 38, 0, 0, 0, 4, 0, 0, 0, 0, 1],
    "LifecycleCheck6.lean j7b_target"⟩
]

def clsName : LCls → String
  | .cut => "cut" | .exploration => "exploration" | .error => "error"
  | .blocked => "blocked" | .deadlock => "deadlock" | .complete => "complete" | .odd => "odd"

def natJ (n : Nat) : Json := Json.num (JsonNumber.fromNat n)

def actJ : Act → Json
  | .read x => Json.mkObj [("kind", Json.str "read"), ("loc", natJ x)]
  | .write x v => Json.mkObj [("kind", Json.str "write"), ("loc", natJ x), ("val", natJ v)]
  | .gen s => Json.mkObj [("kind", Json.str "gen"), ("sym", natJ s)]
  | .cons φ => Json.mkObj [("kind", Json.str "cons"), ("sym", natJ φ)]
  | .block => Json.mkObj [("kind", Json.str "block")]
  | .error => Json.mkObj [("kind", Json.str "error")]

def opJ : TOp → Json
  | .lock l => Json.mkObj [("op", Json.str "lock"), ("loc", natJ l)]
  | .tryLock l k => Json.mkObj [("op", Json.str "tryLock"), ("loc", natJ l), ("skip", natJ k)]
  | .unlock l => Json.mkObj [("op", Json.str "unlock"), ("loc", natJ l)]
  | .rd x => Json.mkObj [("op", Json.str "rd"), ("loc", natJ x)]
  | .wr x v => Json.mkObj [("op", Json.str "wr"), ("loc", natJ x), ("val", natJ v)]
  | .start t => Json.mkObj [("op", Json.str "start"), ("thread", natJ t)]
  | .join t => Json.mkObj [("op", Json.str "join"), ("thread", natJ t)]
  | .assume x v => Json.mkObj [("op", Json.str "assume"), ("loc", natJ x), ("val", natJ v)]

/-- A reference to a thread event. -/
def refJ (e : TEv) : Json := Json.mkObj [("thread", natJ e.tid), ("idx", natJ e.idx)]

def srcJ : Option Ev → Json
  | some .init => Json.str "init"
  | some (.th w) => refJ w
  | none => Json.null

/-- The value read from a source (initial memory for `init`). -/
def srcVal (c : Config) (x : Loc) : Option Ev → Option Nat
  | some .init => some (c.mem x)
  | some (.th w) => match w.act with
    | .write _ v => some v
    | _ => none
  | none => none

/-- One event with its label, its exclusive flag (`lifeFlag` of the thread's trace before it),
and for a read its `rf` source and the value read. -/
def evJ (P : LProg) (c : Config) (u : List (Option Val)) (e : TEv) : Json :=
  let ex := lifeFlag P e.tid (u.take e.idx)
  match e.act with
  | .read x =>
    Json.mkObj [("idx", natJ e.idx), ("act", actJ e.act), ("excl", Json.bool ex),
      ("rf", srcJ (c.rf e)),
      ("rval", match srcVal c x (c.rf e) with | some v => natJ v | none => Json.null)]
  | _ => Json.mkObj [("idx", natJ e.idx), ("act", actJ e.act), ("excl", Json.bool ex)]

/-- The table check of one thread: every event's label is the compiled table's action for
the trace before it (`lifeTab`). -/
def tabOk (P : LProg) (c : Config) (t : Tid) : Bool :=
  let u := c.trace t
  (thEvents c t).all (fun e => decide (lifeTab P t (u.take e.idx) = some e.act))

/-- The full graph of a configuration of `P` (the shape of `LifecycleSem.ser`): events per
thread, coherence per written location. -/
def graphJ (P : LProg) (c : Config) : Json :=
  let ts := P.threads
  let evs := ts.map (fun t => (t, thEvents c t))
  let locs := ((evs.map Prod.snd).flatten.filterMap (fun e => match e.act with
    | .write x _ => some x
    | _ => none)).dedup
  Json.mkObj [
    ("threads", Json.arr (evs.map (fun p =>
      Json.arr (p.2.map (evJ P c (c.trace p.1))).toArray)).toArray),
    ("co", Json.arr (locs.map (fun x => Json.mkObj [("loc", natJ x),
      ("order", Json.arr ((c.co x).map refJ).toArray)])).toArray)]

/-- The locations of the data calls that are data locations. -/
def dataLocs (P : LProg) : List Loc :=
  ((P.threads.map P.code).flatten.filterMap (fun o => match o with
    | .rd x | .wr x _ | .assume x _ => if P.isData x then some x else none
    | _ => none)).dedup.mergeSort (· ≤ ·)

def natsJ (l : List Nat) : Json := Json.arr (l.map natJ).toArray

/-- The `lifeTarget` vector computed from an explored list (the definition of
`lifeTarget` with the list bound once). -/
def targetOf (P : LProg) (l : List Config) : List Nat :=
  let c := lifeCounts P l
  let g := sigCounts P l
  [l.length, c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2.1, c.2.2.2.2.2.2,
    g.1, g.2.1, g.2.2.1, g.2.2.2]

def countCls (l : List (Config × LCls)) (k : LCls) : Nat :=
  (l.filter (fun p => decide (p.2 = k))).length

def fail (msg : String) : IO α := throw (IO.userError s!"LifecycleExport FAILED: {msg}")

def runItem (dir : System.FilePath) (it : Item) : IO Unit := do
  let P := it.prog
  let t0 ← IO.monoMsNow
  unless fragB P do fail s!"{it.name}: fragB is false"
  unless adequateB P it.n do fail s!"{it.name}: bound {it.n} not adequate"
  unless it.n == bnd P do fail s!"{it.name}: bound {it.n} differs from bnd = {bnd P}"
  let l := exploreCfgAtF (lifeSys P it.n) it.n
  let tgt := targetOf P l
  unless tgt == it.expect do
    fail s!"{it.name}: computed {tgt} but {it.thm} states {it.expect}"
  let cls := l.map (fun c => (c, lifeClass P c))
  let tv := cls.filter (fun p => decide (p.2 ≠ .cut) && decide (p.2 ≠ .exploration))
  -- positions of `lifeTarget`: 3 error, 4 blocked, 5 deadlock, 6 complete, 7 odd
  let want := [it.expect[3]!, it.expect[4]!, it.expect[5]!, it.expect[6]!, it.expect[7]!]
  let got := [LCls.error, .blocked, .deadlock, .complete, .odd].map (countCls tv)
  unless got == want do
    fail s!"{it.name}: exported class counts {got} differ from the theorem's {want}"
  unless tv.all (fun p => P.threads.all (tabOk P p.1)) do
    fail s!"{it.name}: an exported event differs from the compiled table lifeTab"
  let cfgs := tv.map (fun p => Json.mkObj [("class", Json.str (clsName p.2)),
    ("graph", graphJ P p.1)])
  let j := Json.mkObj [
    ("name", Json.str it.name),
    ("theorem", Json.str it.thm),
    ("threads", natsJ P.threads),
    ("roots", natsJ P.roots),
    ("locks", natsJ P.locks),
    ("st", Json.arr (P.threads.map (fun t =>
      Json.mkObj [("thread", natJ t), ("loc", natJ (P.st t))])).toArray),
    ("data", natsJ (dataLocs P)),
    ("bound", natJ it.n),
    ("code", Json.arr (P.threads.map (fun t =>
      Json.arr ((P.code t).map opJ).toArray)).toArray),
    ("lifeTarget", natsJ tgt),
    ("lifeTargetPositions", Json.arr ((["full", "cut", "exploration", "error", "blocked",
      "deadlock", "complete", "odd", "sigError", "sigBlocked", "sigDeadlock", "sigComplete"].map Json.str).toArray)),
    ("counts", Json.mkObj [("error", natJ got[0]!), ("blocked", natJ got[1]!),
      ("deadlock", natJ got[2]!), ("complete", natJ got[3]!), ("odd", natJ got[4]!)]),
    ("configurations", Json.arr cfgs.toArray)]
  IO.FS.writeFile (dir / s!"{it.name}.json") (j.pretty 100 ++ "\n")
  let t1 ← IO.monoMsNow
  IO.println s!"OK {it.name} n={it.n} lifeTarget={tgt} exported={tv.length} ms={t1 - t0}"

def main : IO Unit := do
  let some d ← IO.getEnv "LIFECYCLE_EXPORT_DIR" | fail "LIFECYCLE_EXPORT_DIR is not set"
  let only ← IO.getEnv "LIFECYCLE_EXPORT_ONLY"
  let sel := match only with
    | some s => items.filter (fun (it : Item) => (s.splitOn ",").contains it.name)
    | none => items
  if sel.isEmpty then fail "no program selected"
  IO.FS.createDirAll d
  for it in sel do
    runItem d it
  IO.println s!"DONE {sel.length} programs"

end LifeExport

#eval LifeExport.main
