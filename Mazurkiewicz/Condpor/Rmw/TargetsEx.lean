import Mazurkiewicz.Condpor.Rmw.TargetsFast

/-!
# Reference outputs for JMC (gate S8L): programs, listings, witnesses

The programs of the groups "plain locks", "tryLock", "queries" and "solver
formula" of `plan/condpor/lean/monitors/JMC-DESIGN-opus.md` (C.6), each in
both thread orders (`fwd`: the code as written, thread `0` first; `rev`: the
list of threads reversed). Programs that are already defined in `LocksEx.lean`
or `LocksEx3.lean` are used in the forward order as they are defined there
(`progT0`, `progT4`, `progT7`-`progT15`, `progT17`); `codeOf_spec` checks that
their code is the listed one.

`writeAll dir` writes the JSON files (no side effect at build time; it is run
with `#eval` from a separate file). Everything it prints is computed by
`exploreCfgAtF` (equal to `exploreCfgAt P oracleC n`, whose graphs are
`exploreAt P eqOracleSe n`: `exploreCfgAtF_abs`) and `visitAtF` (reached
configurations: `mem_visitAtF`). The printing itself is not verified.
-/

set_option linter.style.longLine false

namespace Condpor

namespace Targets

open Program

/-! ### Programs -/

/-- The code of thread `t` from a list of threads. -/
def codeOf (l : List (List LOp)) : Tid → List LOp := fun t => l.getD t []

/-- The lock program with the threads `0, …, k-1` of the list. -/
def mkL (l : List (List LOp)) (n : ℕ) : XProgram :=
  lockSys (List.range l.length) List.nodup_range (codeOf l) n

/-- A program of the table. -/
structure Spec where
  name : String
  code : List (List LOp)
  n : ℕ
  /-- the existing definition used for the forward order, if any -/
  fwd : Option (String × XProgram)
  /-- proved counts for the forward order: theorem, total, without a blocked thread -/
  proved : List (String × ℕ × ℕ)
  /-- why `n` -/
  cutWhy : String

open LOp in
def L1c : List (List LOp) := [[lock 0, unlock 0], [lock 0, unlock 0]]
open LOp in
def L2c : List (List LOp) := [[lock 0, unlock 0], [lock 0, unlock 0], [lock 0, unlock 0]]
open LOp in
def L3c : List (List LOp) := [[lock 0, unlock 0], [lock 0]]
open LOp in
def L5c : List (List LOp) :=
  [[lock 0, lock 1, unlock 1, unlock 0], [lock 1, lock 0, unlock 0, unlock 1]]
open LOp in
def L7c : List (List LOp) := [[lock 0, lock 0, unlock 0, unlock 0], [lock 0, unlock 0]]
open LOp in
def L8c : List (List LOp) :=
  [[lock 0, wr 1 1, unlock 0], [lock 0, rd 1, unlock 0], [rd 1]]
open LOp in
def L4c : List (List LOp) := [[lock 0, unlock 0], [tryLock 0 0], [lock 0, unlock 0]]
open LOp in
def L9c : List (List LOp) := [[lock 0, rd 0, unlock 0], [rd 0], [lock 0, unlock 0]]
open LOp in
def L9bc : List (List LOp) := [[lock 0, unlock 0], [rd 0], [lock 0, unlock 0]]
open LOp in
def L10c : List (List LOp) :=
  [[lock 0, ev 0 1, wr 1 1, unlock 0], [lock 0, rd 1, unlock 0]]

/-- `tryLock; unlock if true`. -/
def tu : List LOp := [.tryLock 0 1, .unlock 0]
def lu : List LOp := [.lock 0, .unlock 0]

def T7c : List (List LOp) := [tu, tu, tu]
def T8c : List (List LOp) := [lu, lu, tu]
def T9c : List (List LOp) := [lu, tu, tu]
def T10c : List (List LOp) := [lu ++ lu, tu ++ tu]
def T11c : List (List LOp) := [tu ++ tu, tu, lu]
def T12c : List (List LOp) := [tu ++ lu, lu]
def T13c : List (List LOp) := [tu ++ tu, tu ++ tu]
def T14c : List (List LOp) := [lu ++ lu, tu ++ tu ++ tu]
def T15c : List (List LOp) := [lu, lu, tu ++ tu]

/-- The existing definitions have the listed code on their threads. -/
theorem codeOf_spec :
    (∀ t ∈ [0, 1], codeT0 t = codeOf L1c t) ∧ (∀ t ∈ [0, 1], codeT17 t = codeOf L3c t) ∧
    (∀ t ∈ [0, 1], codeT4 t = codeOf L7c t) ∧ (∀ t ∈ [0, 1, 2], codeT7 t = codeOf T7c t) ∧
    (∀ t ∈ [0, 1, 2], codeT8 t = codeOf T8c t) ∧ (∀ t ∈ [0, 1, 2], codeT9 t = codeOf T9c t) ∧
    (∀ t ∈ [0, 1], codeT10 t = codeOf T10c t) ∧ (∀ t ∈ [0, 1, 2], codeT11 t = codeOf T11c t) ∧
    (∀ t ∈ [0, 1], codeT12 t = codeOf T12c t) ∧ (∀ t ∈ [0, 1], codeT13 t = codeOf T13c t) ∧
    (∀ t ∈ [0, 1], codeT14 t = codeOf T14c t) ∧ (∀ t ∈ [0, 1, 2], codeT15 t = codeOf T15c t) :=
  by decide

def specs : List Spec := [
  ⟨"L1", L1c, 6, some ("progT0", progT0), [("lockT0", 4, 2)],
    "as in progT0; longest non-block prefix 3, a blocked thread has 1 or 2 events"⟩,
  ⟨"L2", L2c, 6, none, [], "3 per call (convention of LocksEx); longest non-block prefix 3"⟩,
  ⟨"L3", L3c, 6, some ("progT17", progT17), [("lockT17", 3, 1)],
    "as in progT17; longest non-block prefix 3"⟩,
  ⟨"L5", L5c, 12, none, [], "3 per call; longest non-block prefix 6"⟩,
  ⟨"L7", L7c, 6, some ("progT4", progT4), [("lockT4", 4, 2)],
    "as in progT4; longest non-block prefix 5 (RX, WX, G, G, W)"⟩,
  ⟨"L8", L8c, 9, none, [], "3 per call; longest non-block prefix 4"⟩,
  ⟨"L4", L4c, 6, none, [], "3 per call; longest non-block prefix 3"⟩,
  ⟨"T7", T7c, 9, some ("progT7", progT7), [("lockT7", 21, 21), ("lockT7_execs", 21, 21)],
    "as in progT7; longest non-block prefix 3"⟩,
  ⟨"T8", T8c, 9, some ("progT8", progT8), [("lockT8", 21, 10), ("lockT8_execs", 21, 10)],
    "as in progT8; longest non-block prefix 3"⟩,
  ⟨"T9", T9c, 9, some ("progT9", progT9), [("lockT9", 21, 15), ("lockT9_execs", 21, 15)],
    "as in progT9; longest non-block prefix 3"⟩,
  ⟨"T10", T10c, 12, some ("progT10", progT10), [("lockT10", 21, 15)],
    "as in progT10; longest non-block prefix 6"⟩,
  ⟨"T11", T11c, 12, some ("progT11", progT11), [("lockT11", 62, 44)],
    "as in progT11; longest non-block prefix 6"⟩,
  ⟨"T12", T12c, 9, some ("progT12", progT12), [("lockT12", 8, 4)],
    "as in progT12; longest non-block prefix 6"⟩,
  ⟨"T13", T13c, 12, some ("progT13", progT13), [("lockT13", 26, 26)],
    "as in progT13; longest non-block prefix 6"⟩,
  ⟨"T14", T14c, 15, some ("progT14", progT14), [("lockT14", 48, 35)],
    "as in progT14; longest non-block prefix 9"⟩,
  ⟨"T15", T15c, 12, some ("progT15", progT15), [("lockT15", 62, 30)],
    "as in progT15; longest non-block prefix 6"⟩,
  ⟨"L9", L9c, 9, none, [], "3 per call; longest non-block prefix 4"⟩,
  ⟨"L9b", L9bc, 9, none, [], "3 per call; longest non-block prefix 3"⟩,
  ⟨"L10", L10c, 12, none, [], "3 per call; longest non-block prefix 5"⟩]

/-- The program and code of a specification in an order. -/
def Spec.prog (s : Spec) (rev : Bool) : XProgram :=
  if rev then mkL s.code.reverse s.n
  else match s.fwd with
    | some (_, P) => P
    | none => mkL s.code s.n

def Spec.codeIn (s : Spec) (rev : Bool) : List (List LOp) := if rev then s.code.reverse else s.code

def Spec.leanDef (s : Spec) (rev : Bool) : String :=
  if rev then s!"Condpor.Targets.mkL {s.name}c.reverse {s.n}"
  else match s.fwd with
    | some (nm, _) => s!"Condpor.{nm}"
    | none => s!"Condpor.Targets.mkL {s.name}c {s.n}"

/-! ### Locations -/

def opLockLoc : LOp → Option Loc
  | .lock l => some l | .tryLock l _ => some l | .unlock l => some l | _ => none

def opLoc : LOp → Option Loc
  | .lock l => some l | .tryLock l _ => some l | .unlock l => some l
  | .rd x => some x | .wr x _ => some x | .ev _ _ => none

def lockLocs (code : List (List LOp)) : List Loc :=
  ((code.flatten.filterMap opLockLoc).dedup).mergeSort (· ≤ ·)

def allLocs (code : List (List LOp)) : List Loc :=
  ((code.flatten.filterMap opLoc).dedup).mergeSort (· ≤ ·)

/-! ### Queries by the holder (design I.6) -/

/-- Thread `t` holds the lock `x` before its event number `i` (its hold count,
from its code and trace). -/
def holdsAt (code : List (List LOp)) (c : Config) (t : Tid) (i : ℕ) (x : Loc) : Bool :=
  decide (0 < (lockState (codeOf code t) (c.traceBeforeC t i)).holds x)

/-- `e` is a read of a lock location made while its thread holds that lock (a
`rd l` by the holder: Lean emits it, MODEL §3 does not). -/
def isHolderQuery (code : List (List LOp)) (locks : List Loc) (c : Config) (e : TEv) : Bool :=
  match e.act with
  | .read x => decide (x ∈ locks) && holdsAt code c e.tid e.idx x
  | _ => false

/-- The source of the holder's query `e` of `x` is its own thread's last write
of `x` before it, and that write is exclusive (`WX`). -/
def holderSrcOkB (P : XProgram) (c : Config) (e : TEv) (x : Loc) : Bool :=
  match c.rf e with
  | some (.th q) =>
    decide (((thEvents c e.tid).filter
      (fun q' => decide (q'.idx < e.idx) && q'.writesTo x)).getLast? = some q) &&
      P.ex q.tid (c.traceBeforeC q.tid q.idx)
  | _ => false

/-- Every holder's query of the configuration reads its own thread's `WX`. -/
def holderOkB (P : XProgram) (code : List (List LOp)) (locks : List Loc) (c : Config) : Bool :=
  c.order.all (fun e => !isHolderQuery code locks c e || holderSrcOkB P c e e.act.loc)

/-- The number of holder's queries of the configuration. -/
def holderCount (code : List (List LOp)) (locks : List Loc) (c : Config) : ℕ :=
  (c.order.filter (isHolderQuery code locks c)).length

/-! ### JSON -/

def jStr (s : String) : String := "\"" ++ s ++ "\""

def jList (l : List String) : String := "[" ++ ",".intercalate l ++ "]"

def jId (p : ℕ × ℕ) : String := s!"[{p.1},{p.2}]"

def jBool (b : Bool) : String := if b then "true" else "false"

def opStr : LOp → String
  | .lock l => s!"lock {l}"
  | .tryLock l k => s!"tryLock {l} {k}"
  | .unlock l => s!"unlock {l}"
  | .rd x => s!"rd {x}"
  | .wr x v => s!"wr {x} {v}"
  | .ev s k => s!"ev {s} {k}"

def kindName : ℕ → String
  | 0 => "R" | 1 => "W" | 2 => "RX" | 3 => "WX" | 4 => "C" | 5 => "B" | 6 => "E" | _ => "G"

/-- A value at location `x`: `held`/`free` at a lock location, else the number. -/
def jVal (locks : List Loc) (x : Loc) (v : ℕ) : String :=
  if x ∈ locks then (if v = 1 then jStr "held" else if v = 0 then jStr "free" else toString v)
  else toString v

def jEv (locks : List Loc) (hq : List (ℕ × ℕ)) (e : REv) : String :=
  let mem := e.kind ≤ 3
  let base := s!"\"t\":{e.t},\"i\":{e.i},\"a\":{jStr (kindName e.kind)}," ++
    s!"\"loc\":{if mem then toString e.loc else "null"}," ++
    s!"\"val\":{if mem then jVal locks e.loc e.val else "null"}"
  let rf := match e.rf with
    | some none => ",\"rf\":\"init\""
    | some (some p) => s!",\"rf\":{jId p}"
    | none => ""
  let cs := if e.kind = 4 then
      s!",\"phi\":{e.phi},\"sym\":{e.phi / 1000},\"k\":{e.phi % 1000},\"out\":{jBool (e.val = 1)}"
    else ""
  let hqs := if e.kind = 0 ∧ e.loc ∈ locks then
      s!",\"holderQuery\":{jBool ((e.t, e.i) ∈ hq)}" else ""
  "{" ++ base ++ rf ++ cs ++ hqs ++ "}"

def jGraphBody (locks : List Loc) (hq : List (ℕ × ℕ)) (g : RGraph) : String :=
  s!"\"events\":{jList (g.evs.map (jEv locks hq))}," ++
  s!"\"order\":{jList (g.order.map jId)}," ++
  s!"\"co\":{jList (g.co.map (fun p => "{" ++ s!"\"loc\":{p.1},\"writes\":{jList (p.2.map jId)}" ++ "}"))}," ++
  s!"\"blocked\":{jList (g.blocked.map toString)}"

def jGraph (locks : List Loc) (hq : List (ℕ × ℕ)) (k : ℕ) (g : RGraph) : String :=
  "{" ++ s!"\"id\":{k},\"class\":{jStr g.cls.name}," ++ jGraphBody locks hq g ++ "}"

def jCounts (cc : ℕ × ℕ × ℕ × ℕ × ℕ) : String :=
  let (a, b, c, d, e) := cc
  s!"\"complete\":{a},\"dropped\":{b},\"bound\":{c},\"deadlock\":{d},\"exploration\":{e}," ++
    s!"\"total\":{a + b + c + d + e}"

/-! ### One program in one order -/

structure Run where
  spec : Spec
  rev : Bool
  cfgs : List Config
  graphs : List RGraph
  counts : ℕ × ℕ × ℕ × ℕ × ℕ
  cutOk : Bool
  countsN1 : ℕ × ℕ × ℕ × ℕ × ℕ
  dead : ℕ
  /-- the listings at `n + 1` are a permutation of those at `n` -/
  permN1 : Bool
  /-- the listings at `n + 1` are those at `n`, in the same order -/
  sameN1 : Bool
  /-- the holder's queries of each configuration -/
  hqs : List (List (ℕ × ℕ))
  holderOk : Bool
  holderN : ℕ

def runSpec (s : Spec) (rev : Bool) : Run :=
  let P := s.prog rev
  let code := s.codeIn rev
  let ts := List.range code.length
  let cfgs := exploreCfgAtF P s.n
  let P1 := mkL code (s.n + 1)
  let locks := lockLocs code
  let gs := cfgs.map (rawOf P ts (allLocs code))
  let cfgs1 := exploreCfgAtF P1 (s.n + 1)
  let gs1 := cfgs1.map (rawOf P1 ts (allLocs code))
  ⟨s, rev, cfgs, gs, classCounts ts cfgs,
    cfgs.all (cutOkB (codeOf code) ts), classCounts ts cfgs1,
    (deadAtF P s.n).length, gs1.isPerm gs, gs1 == gs,
    cfgs.map (fun c => (c.order.filter (isHolderQuery code locks c)).reverse.map evId),
    cfgs.all (holderOkB P code locks), (cfgs.map (holderCount code locks)).sum⟩

def orderName (rev : Bool) : String := if rev then "rev" else "fwd"

def jProgram (r : Run) : String :=
  let code := r.spec.codeIn r.rev
  let locks := lockLocs code
  "{" ++ s!"\"program\":{jStr r.spec.name},\"order\":{jStr (orderName r.rev)}," ++
  s!"\"threads\":{code.length},\"n\":{r.spec.n}," ++
  s!"\"code\":{jList (code.map (fun th => jList (th.map (fun o => jStr (opStr o)))))}," ++
  s!"\"lockLocs\":{jList (locks.map toString)}," ++
  s!"\"fieldLocs\":{jList (((allLocs code).filter (· ∉ locks)).map toString)}," ++
  s!"\"leanDef\":{jStr (r.spec.leanDef r.rev)}," ++
  s!"\"graphs\":{jList ((List.range r.graphs.length).zip (r.graphs.zip r.hqs) |>.map (fun p => jGraph locks p.2.2 p.1 p.2.1))}" ++
  "}"

def jCountsOrder (r : Run) : String :=
  "{" ++ jCounts r.counts ++ s!",\"cutOk\":{jBool r.cutOk}," ++
    s!"\"sameCountsAtNplus1\":{jBool (r.counts == r.countsN1)}," ++
    s!"\"sameGraphsAtNplus1\":{jBool r.permN1},\"sameListAtNplus1\":{jBool r.sameN1}," ++
    s!"\"holderQueries\":{r.holderN},\"holderQueriesReadOwnWX\":{jBool r.holderOk}," ++
    s!"\"deadAt\":{r.dead}" ++ "}"

def jO1 (f b : Run) : String :=
  let s := f.spec
  let pr := s.proved.map (fun (nm, tot, nb) =>
    "{" ++ s!"\"theorem\":{jStr ("Condpor." ++ nm)},\"total\":{tot},\"withoutBlocked\":{nb}," ++
      s!"\"matches\":{jBool (tot == f.graphs.length && nb == f.counts.1)}" ++ "}")
  "{" ++ s!"\"program\":{jStr s.name},\"n\":{s.n},\"threads\":{s.code.length}," ++
  s!"\"cutWhy\":{jStr s.cutWhy}," ++
  s!"\"fwd\":{jCountsOrder f},\"rev\":{jCountsOrder b},\"provedFwd\":{jList pr}" ++ "}"

/-! ### Witnesses -/

/-- A successor with its kind, in the order of `succsAtF`. -/
inductive SKind
  | read (src : Ev) | place (after : Ev) | revisit (r : TEv) (after : Ev) | loc (o : Option Bool)

/-- `succsAtF` with the kind of each successor. -/
def succsAnn (P : XProgram) (O : Oracle τ) (c : Config) : List (SKind × Config) :=
  match P.nextC c with
  | none => []
  | some e =>
    match e.act with
    | .read x =>
      ((writesOf c.order x).filter (fun w => consXF P O (c.addRead e w))).map
        (fun w => (.read w, c.addRead e w))
    | .write x _ =>
      ((writesOf c.order x).filter (fun wp => consXF P O (c.addWrite e wp))).map
          (fun wp => (.place wp, c.addWrite e wp)) ++
        (c.order.filter (fun r => r.readsLoc x)).flatMap (fun r =>
          if revisitOKBF c O.prefB r e then
            ((writesOf (c.order.filter (fun d => decide (d ∈ keepCF c r e))) x).filter
              (fun wp => consXF P O (revisitCF c r e wp))).map
              (fun wp => (.revisit r wp, revisitCF c r e wp))
          else [])
    | .cons _ =>
      ([true, false].filter (fun b => consXF P O (c.addLoc e (some b)))).map
        (fun b => (.loc (some b), c.addLoc e (some b)))
    | _ => if consXF P O (c.addLoc e none) then [(.loc none, c.addLoc e none)] else []

theorem succsAnn_snd (P : XProgram) (O : Oracle τ) (c : Config) :
    (succsAnn P O c).map Prod.snd = succsAt P O c := by
  rw [← succsAtF_eq]
  rcases h : P.nextC c with _ | e
  · simp only [succsAnn, succsAtF, h, List.map_nil]
  · simp only [succsAnn, succsAtF, h]
    cases e.act <;> simp [List.map_flatMap, apply_ite, List.map_map, Function.comp_def]

def jEvRef : Ev → String
  | .init => jStr "init"
  | .th q => jId (evId q)

def jSKind : SKind → String
  | .read s => s!"\"kind\":\"read\",\"rf\":{jEvRef s}"
  | .place a => s!"\"kind\":\"place\",\"after\":{jEvRef a}"
  | .revisit r a => s!"\"kind\":\"revisit\",\"read\":{jId (evId r)},\"after\":{jEvRef a}"
  | .loc none => "\"kind\":\"local\""
  | .loc (some b) => s!"\"kind\":\"outcome\",\"out\":{jBool b}"

def jRej : Rej → String
  | .porf => "{\"pred\":\"porf\"}"
  | .maxA d => "{" ++ s!"\"pred\":\"L5a\",\"d\":{jId (evId d)}" ++ "}"
  | .maxB d => "{" ++ s!"\"pred\":\"L5b\",\"d\":{jId (evId d)}" ++ "}"
  | .maxC d => "{" ++ s!"\"pred\":\"L5c\",\"d\":{jId (evId d)}" ++ "}"

/-- The listing of a configuration that is not (necessarily) full, with its
next event. -/
def jCfg (P : XProgram) (ts : List Tid) (locs locks : List Loc) (c : Config) : String :=
  let g := rawOf P ts locs c
  let nx := match P.nextC c with
    | none => "null"
    | some e =>
      let ex := P.ex e.tid (c.trace e.tid)
      let (k, x, v) : ℕ × ℕ × ℕ := match e.act with
        | .read x => (if ex then 2 else 0, x, 0)
        | .write x v => (if ex then 3 else 1, x, v)
        | .cons φ => (4, 0, φ)
        | .block => (5, 0, 0)
        | .error => (6, 0, 0)
        | .gen _ => (7, 0, 0)
      "{" ++ s!"\"t\":{e.tid},\"i\":{e.idx},\"a\":{jStr (kindName k)}," ++
        s!"\"loc\":{if k ≤ 3 then toString x else "null"}," ++
        s!"\"val\":{if k = 1 ∨ k = 3 then jVal locks x v else "null"}" ++ "}"
  "{" ++ jGraphBody locks [] g ++ s!",\"next\":{nx}" ++ "}"

/-- The witness file of the configuration `c` of a program in an order. -/
def jWitness (wname descr : String) (s : Spec) (rev : Bool) (c : Config) : String :=
  let P := s.prog rev
  let code := s.codeIn rev
  let ts := List.range code.length
  let locs := allLocs code
  let locks := lockLocs code
  let ann := succsAnn P oracleC c
  let okSuccs := decide ((ann.map (fun p => rawOf P ts locs p.2)) =
    ((succsAtF P oracleC c).map (rawOf P ts locs)))
  let succ := ann.map (fun p => "{" ++ jSKind p.1 ++ s!",\"config\":{jCfg P ts locs locks p.2}" ++ "}")
  let cands : List String := match P.nextC c with
    | some e =>
      match e.act with
      | .write x _ =>
        (c.order.reverse.filter (fun r => r.readsLoc x)).map (fun r =>
          let rej := revDiagF oracleC c r e
          let ok := rej.isEmpty
          let pl := (writesOf (c.order.filter (fun d => decide (d ∈ keepCF c r e))) x).map
            (fun wp => "{" ++ s!"\"after\":{jEvRef wp},\"consistent\":{jBool (consXF P oracleC (revisitCF c r e wp))}" ++ "}")
          "{" ++ s!"\"read\":{jId (evId r)},\"passes\":{jBool ok},\"failing\":{jList (rej.map jRej)}," ++
            s!"\"tested\":{jList ((testedEventsF c r e).map (fun d => jId (evId d)))}," ++
            s!"\"placements\":{if ok then jList pl else "[]"}" ++ "}")
      | _ => []
    | none => []
  let fwdPl : List String := match P.nextC c with
    | some e =>
      match e.act with
      | .write x _ => (writesOf c.order x).map (fun wp =>
          "{" ++ s!"\"after\":{jEvRef wp},\"consistent\":{jBool (consXF P oracleC (c.addWrite e wp))}" ++ "}")
      | .read x => (writesOf c.order x).map (fun w =>
          "{" ++ s!"\"rf\":{jEvRef w},\"consistent\":{jBool (consXF P oracleC (c.addRead e w))}" ++ "}")
      | _ => []
    | none => []
  "{" ++ s!"\"witness\":{jStr wname},\"description\":{jStr descr},\"program\":{jStr s.name}," ++
  s!"\"order\":{jStr (orderName rev)},\"n\":{s.n}," ++
  s!"\"code\":{jList (code.map (fun th => jList (th.map (fun o => jStr (opStr o)))))}," ++
  s!"\"lockLocs\":{jList (locks.map toString)},\"leanDef\":{jStr (s.leanDef rev)}," ++
  s!"\"config\":{jCfg P ts locs locks c}," ++
  s!"\"successors\":{jList succ},\"successorsMatchSuccsAt\":{jBool okSuccs}," ++
  s!"\"forwardCandidates\":{jList fwdPl}," ++
  s!"\"revisitCandidates\":{jList cands}" ++ "}"

/-- The next write and its accepted revisit candidates with a consistent
placement. -/
def nextWrite (P : XProgram) (c : Config) : Option (TEv × Loc × Val) :=
  match P.nextC c with
  | some e => match e.act with
    | .write x v => some (e, x, v)
    | _ => none
  | none => none

def acceptedReads (P : XProgram) (c : Config) (e : TEv) (x : Loc) : List TEv :=
  (c.order.filter (fun r => r.readsLoc x)).filter (fun r =>
    revisitOKBF c oracleC.prefB r e &&
      (writesOf (c.order.filter (fun d => decide (d ∈ keepCF c r e))) x).any
        (fun wp => consXF P oracleC (revisitCF c r e wp)))

/-- The read is the blocking read of a blocked thread. -/
def isBlockedRead (c : Config) (r : TEv) : Bool :=
  blockedB c r.tid && decide (blockingRead c r.tid = some r)

/-- W1: a release revisits a blocked acquire read. -/
def isW1 (P : XProgram) (locks : List Loc) (c : Config) : Bool :=
  match nextWrite P c with
  | some (e, x, v) => decide (x ∈ locks) && decide (v = 0) &&
      (acceptedReads P c e x).any (isBlockedRead c)
  | none => false

/-- W2: an accepted revisit after which a thread below the writer has an
available event (a pending completion). -/
def isW2 (P : XProgram) (c : Config) : Bool :=
  match nextWrite P c with
  | some (e, _, _) =>
    (succsAnn P oracleC c).any (fun p => match p.1 with
      | .revisit _ _ => (P.availC p.2).any (fun a => decide (a.tid < e.tid))
      | _ => false)
  | none => false

/-- W3: two blocked reads of one held write; one of them is revisited. -/
def isW3 (P : XProgram) (locks : List Loc) (c : Config) : Bool :=
  match nextWrite P c with
  | some (e, x, _) =>
    let bl := (c.order.filter (fun r => r.readsLoc x)).filter (isBlockedRead c)
    decide (x ∈ locks) &&
      bl.any (fun r1 => bl.any (fun r2 => decide (r1 ≠ r2) && decide (c.rf r1 = c.rf r2))) &&
      (acceptedReads P c e x).any (fun r => bl.contains r)
  | none => false

/-- W5: a revisit candidate whose tested events contain a constraint
evaluation with outcome `b`. -/
def isW5 (P : XProgram) (b : Bool) (c : Config) : Bool :=
  match nextWrite P c with
  | some (e, x, _) =>
    (c.order.filter (fun r => r.readsLoc x)).any (fun r =>
      !plusPorfBF c e (.th r) (.th e) &&
      (testedEventsF c r e).any (fun d => (match d.act with
        | .cons _ => true
        | _ => false) && decide (c.pol d = some b)))
  | none => false

/-! ### Writing the files -/


/-- Write the program files of the programs `names` (all if empty) into `dir`,
their `O1` objects into `frag/<P>.json`, and the witnesses if `wits`. -/
def writeAll (dir frag : System.FilePath) (names : List String) (wits : Bool) :
    IO Unit := do
  IO.FS.createDirAll dir
  IO.FS.createDirAll frag
  for s in specs.filter (fun s => names.isEmpty || names.contains s.name) do
    let t0 ← IO.monoMsNow
    let f := runSpec s false
    IO.FS.writeFile (dir / s!"{s.name}-fwd.json") (jProgram f ++ "\n")
    let b := runSpec s true
    IO.FS.writeFile (dir / s!"{s.name}-rev.json") (jProgram b ++ "\n")
    IO.FS.writeFile (frag / s!"{s.name}.json") (jO1 f b)
    IO.eprintln s!"{s.name}: fwd {repr f.counts} cut {f.cutOk} n+1 {f.counts == f.countsN1} {f.permN1} {f.sameN1} hq {f.holderN} {f.holderOk} dead {f.dead}; rev {repr b.counts} cut {b.cutOk} n+1 {b.counts == b.countsN1} {b.permN1} {b.sameN1} hq {b.holderN} {b.holderOk} dead {b.dead}; {(← IO.monoMsNow) - t0} ms"
  if !wits then return
  -- witnesses
  let wit : List (String × String × String × Bool × (XProgram → List Loc → Config → Bool)) := [
    ("W1", "retained-read revisit: a release write revisits a blocked acquire read", "L1", false,
      fun P locks c => isW1 P locks c),
    ("W2", "pending completion: an accepted revisit leaves a thread below the writer with an available event", "L1", false,
      fun P _ c => isW2 P c),
    ("W3", "blocked reads: two blocked acquire reads of one held write, one of them revisited", "L2", false,
      fun P locks c => isW3 P locks c),
    ("W5a", "formula maximality: a revisit candidate whose tested (deleted) events contain the ev with outcome true", "L10", false,
      fun P _ c => isW5 P true c),
    ("W5b", "formula maximality: a revisit candidate whose tested (deleted) events contain the ev with outcome false", "L10", false,
      fun P _ c => isW5 P false c)]
  for (wn, descr, pn, rev, pred) in wit do
    let some s := specs.find? (·.name == pn) | IO.eprintln s!"{wn}: no program {pn}"
    let P := s.prog rev
    let locks := lockLocs (s.codeIn rev)
    match (visitAtF P s.n).find? (pred P locks) with
    | some c =>
      IO.FS.writeFile (dir / s!"{wn}.json") (jWitness wn descr s rev c ++ "\n")
      IO.eprintln s!"{wn}: found in {pn} {orderName rev}"
    | none => IO.eprintln s!"{wn}: NOT FOUND in {pn} {orderName rev}"

/-- `O1-counts.json` from the fragments of all programs, in the order of `specs`. -/
def mergeO1 (dir frag : System.FilePath) : IO Unit := do
  let mut l : List String := []
  for s in specs do
    l := l ++ [← IO.FS.readFile (frag / s!"{s.name}.json")]
  IO.FS.writeFile (dir / "O1-counts.json") ("[\n" ++ ",\n".intercalate l ++ "\n]\n")

end Targets

end Condpor
