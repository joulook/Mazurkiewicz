/-!
# Must, executable core on arrays (no Mathlib)

Plan: `plan/must/lean/LEAN-PLAN.md`, milestone M2. This file imports only the Lean core, so
that the D21 search (`Must/Search.lean`) compiles to a standalone executable. It contains:

* the program syntax `Code` (a finite tree of actions) and its denotation `Code.run`, a
  function from the trace of returned values to the next label or to termination (`none`);
* configurations `FC` (an array of events in insertion order, each with its source and its
  outcome), consistency `cons` for `asyn` and `p2p` (Definitions 3.4, 3.5, decisions Q1–Q4),
  availability and `next_P` (Q7), the successor function `succs` of Algorithm 1 with the
  repairs Q9, Q12, Q15, its depth-first explorer with fuel, and an independent enumerator of
  `⟦P⟧` (Q8).

The reference definitions on `Graph` are in `Must/Program.lean` … `Must/Enum.lean`; this file is
the same algorithm on a fast representation, and `Must/CrossCheck.lean` checks that both give
the same results (`CrossCheck.agree`).

Representation. An event is identified by `(tid, idx)` (Q1). `src = none`: not a receive;
`src = some none`: the receive reads `⊥`; `src = some (some (t, i))`: it reads the send `(t, i)`.
`out = some v`: the outcome of an ND event. In every configuration built here the events of a
thread occur in the array in the order of their indices (the insertion order contains `po`).

ND sets. `Code.nd v vs ks kd` offers `ND_S` with `S = {v} ∪ vs`: a program cannot offer an ND
action with an empty set (unrepresentable).
-/

namespace MustFast

/-! ### Labels and programs -/

/-- The communication models of the executable core. -/
inductive Model
  | asyn
  | p2p
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A receive predicate: every value, or a finite list of values. -/
inductive FPred
  | any
  | only (vs : List Nat)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Membership of a value in a predicate. -/
def FPred.mem : FPred → Nat → Bool
  | .any, _ => true
  | .only vs, v => vs.contains v

/-- Labels: `R_⟨m, b⟩(p)`, `S_m(dst, v)`, `ND_S` (`S` a list without repetition, sorted),
`B`, `error`. -/
inductive FLab
  | recv (m : Model) (blocking : Bool) (p : FPred)
  | send (m : Model) (dst v : Nat)
  | nd (vs : List Nat)
  | block
  | error
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A thread: a finite tree of actions.

* `send m dst v k`: send, then `k`;
* `recv m b p ks kd kb`: receive (`b`: blocking); after the value `v` continue with the entry of
  `v` in `ks`, or `kd` if there is none; after `⊥` continue with `kb` (a blocking receive
  that returns `⊥` ends the thread, 3.3);
* `nd v vs ks kd`: `ND_S`, `S = {v} ∪ vs`, continuation per outcome as for receives;
* `block`, `error`: end the thread (3.3, Q8). -/
inductive Code
  | done
  | send (m : Model) (dst v : Nat) (k : Code)
  | recv (m : Model) (b : Bool) (p : FPred) (ks : List (Nat × Code)) (kd kb : Code)
  | nd (v : Nat) (vs : List Nat) (ks : List (Nat × Code)) (kd : Code)
  | block
  | error
  deriving Inhabited

/-- Insert into a sorted list without repetition. -/
def insSorted (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => if a < b then a :: b :: l else if a == b then b :: l else b :: insSorted a l

/-- Sorted list without repetition (structural, so that the kernel evaluates it). -/
def sortDedup (l : List Nat) : List Nat := l.foldr insSorted []

/-- The continuation after the value `v`. -/
def branch (ks : List (Nat × Code)) (kd : Code) (v : Nat) : Code := (ks.lookup v).getD kd

/-- The denotation of a thread: the next label after a trace, `none` = terminated. -/
def Code.run : Code → List (Option Nat) → Option FLab
  | .done, _ => none
  | .send m d v _, [] => some (.send m d v)
  | .send _ _ _ k, _ :: tr => k.run tr
  | .recv m b p _ _ _, [] => some (.recv m b p)
  | .recv _ b _ ks kd kb, x :: tr =>
    match x with
    | some v => (branch ks kd v).run tr
    | none => if b then none else kb.run tr
  | .nd v vs _ _, [] => some (.nd (sortDedup (v :: vs)))
  | .nd _ _ ks kd, x :: tr =>
    match x with
    | some w => (branch ks kd w).run tr
    | none => none
  | .block, [] => some .block
  | .error, [] => some .error
  | .block, _ :: _ => none
  | .error, _ :: _ => none

/-- A program: one code per thread, threads `0, …, n - 1`. -/
structure FProg where
  /-- the code of each thread -/
  codes : Array Code
  deriving Inhabited

/-! ### Events and configurations -/

/-- An event with its source (receives) and outcome (ND). -/
structure FE where
  tid : Nat
  idx : Nat
  lab : FLab
  src : Option (Option (Nat × Nat)) := none
  out : Option Nat := none
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A configuration: the events in insertion order. -/
abbrev FC := Array FE

/-- The identity of an event. -/
@[inline] def FE.id (e : FE) : Nat × Nat := (e.tid, e.idx)

def FE.isSend (e : FE) : Bool := match e.lab with | .send .. => true | _ => false
def FE.isRecv (e : FE) : Bool := match e.lab with | .recv .. => true | _ => false
def FE.isRecvB (e : FE) : Bool := match e.lab with | .recv _ b _ => b | _ => false

/-- The position of the event with identity `id`. -/
def posOf (c : FC) (id : Nat × Nat) : Option Nat :=
  c.findIdx? (fun e => e.tid == id.1 && e.idx == id.2)

/-- The value carried by a send label. -/
def sendVal : FLab → Option Nat
  | .send _ _ v => some v
  | _ => none

/-- The value returned by an event (Section 2b): a receive the value of its source or `⊥`, an
ND event its outcome, the other events `⊥`. -/
def ret (c : FC) (e : FE) : Option Nat :=
  match e.src with
  | some (some id) =>
    match posOf c id with
    | some j => sendVal c[j]!.lab
    | none => none
  | some none => none
  | none => e.out

/-- The number of events of thread `t`. -/
def cnt (c : FC) (t : Nat) : Nat := c.foldl (fun n e => if e.tid == t then n + 1 else n) 0

/-- The trace of thread `t`. -/
def trace (c : FC) (t : Nat) : List (Option Nat) :=
  (c.toList.filter (fun e => e.tid == t)).map (ret c)

/-- The next event of thread `t`, if it has not terminated. -/
def nextOf (P : FProg) (c : FC) (t : Nat) : Option FE :=
  match (P.codes.getD t .done).run (trace c t) with
  | none => none
  | some l => some { tid := t, idx := cnt c t, lab := l }

/-! ### Causality -/

/-- The positions of the direct causal predecessors of each event: its `po`-predecessor and its
real source. -/
def direct (c : FC) : Array (List Nat) :=
  c.map fun e =>
    let p := if e.idx == 0 then [] else (posOf c (e.tid, e.idx - 1)).toList
    let r := match e.src with
      | some (some id) => (posOf c id).toList
      | _ => []
    p ++ r

/-- For each event, the bit mask of its strict causal predecessors (`porf`). -/
def predMasks (c : FC) : Array Nat := Id.run do
  let d := direct c
  let mut m : Array Nat := d.map (fun l => l.foldl (fun a j => a ||| (1 <<< j)) 0)
  for _ in [0:c.size] do
    for i in [0:c.size] do
      let v := d[i]!.foldl (fun a j => a ||| m[j]!) m[i]!
      m := m.set! i v
  return m

/-- `porf a b` for positions, from the masks. -/
@[inline] def porfM (m : Array Nat) (a b : Nat) : Bool := (m[b]!).testBit a

/-! ### Consistency (Definitions 3.3–3.5, Q1–Q4) -/

/-- The send `s` matches the receive `r`: destination, value, model. -/
def matchesL (s : FLab) (r : FE) : Bool :=
  match s, r.lab with
  | .send m d v, .recv m' _ p => d == r.tid && p.mem v && m == m'
  | _, _ => false

/-- Well-formedness (Definition 3.3 with Q1–Q3, Q6). -/
def wfB (c : FC) : Bool := Id.run do
  let n := c.size
  for i in [0:n] do
    let e := c[i]!
    -- unique identity
    for j in [i+1:n] do
      if c[j]!.tid == e.tid && c[j]!.idx == e.idx then return false
    -- contiguous indices
    for k in [0:e.idx] do
      if !(c.any (fun e' => e'.tid == e.tid && e'.idx == k)) then return false
    -- sources
    match e.lab, e.src with
    | .recv _ b _, some none => if b then return false
    | .recv _ _ _, some (some id) =>
      match posOf c id with
      | some j => if !(matchesL c[j]!.lab e) then return false
      | none => return false
    | .recv _ _ _, none => return false
    | _, some _ => return false
    | _, none => pure ()
    -- outcomes
    match e.lab, e.out with
    | .nd vs, some v => if !(vs.contains v) then return false
    | .nd _, none => return false
    | _, some _ => return false
    | _, none => pure ()
    -- read once
    match e.src with
    | some (some id) =>
      for j in [i+1:n] do
        if c[j]!.src == some (some id) then return false
    | _ => pure ()
  -- no causal cycle
  let m := predMasks c
  for i in [0:n] do
    if porfM m i i then return false
  return true

/-- The send at position `j` is read by some receive. -/
def isRead (c : FC) (id : Nat × Nat) : Bool := c.any (fun e => e.src == some (some id))

/-- The `p2p` conditions (b) and (c) of Definition 3.5, `so = [S^p2p]; po; [S^p2p]`, on the
whole graph (Q4). -/
def p2pB (c : FC) : Bool := Id.run do
  for s' in c do
    match s'.lab with
    | .send .p2p d' v' =>
      for s in c do
        match s.lab with
        | .send .p2p d _ =>
          if s'.tid == s.tid && s'.idx < s.idx && d' == d then
            for r in c do
              if r.src == some (some s.id) then
                match r.lab with
                | .recv _ _ p =>
                  if p.mem v' then
                    -- (b): `s'` unread
                    if !(isRead c s'.id) then return false
                    -- (c): `s'` read by a `po`-successor of `r`
                    for q in c do
                      if q.src == some (some s'.id) && q.tid == r.tid && r.idx < q.idx then
                        return false
                | _ => pure ()
        | _ => pure ()
    | _ => pure ()
  return true

/-- Consistency for `asyn` and `p2p` events (Definition 3.8 with Q4): well-formed and the
`p2p` conditions; for a graph without `p2p` sends this is `consistent_asyn`. -/
def consAP (c : FC) : Bool := wfB c && p2pB c

/-! ### Variants of the algorithm -/

/-- The tie-breaks (Q9): the least identity, the greatest identity; depending on the context,
the least if the context has an even number of events and the greatest otherwise; depending on
the receive, the least if `tid + idx` of the receive is even and the greatest otherwise. -/
inductive TieK
  | least
  | greatest
  | parity
  | recv
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The oracle of line 22: `tie` of Q9 on `(H|Previous) \ {e}` (`q9`); the current source
(`cur`); the least consistent unread send of `H|Previous` with `e` in it (`unread`). The last
two violate Q9 (`oracle_dup`, `oracle_missed`). -/
inductive OrcK
  | q9
  | cur
  | unread
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A variant of the algorithm. -/
structure Var where
  /-- the tie-break -/
  tie : TieK := .least
  /-- the oracle -/
  orc : OrcK := .q9
  /-- printed `next_P` (ii): no receive is added without a matching unread send of any model -/
  printedNext : Bool := false
  /-- printed lines 11/13: `s ∈ Deleted`, `SetRF(G|E \ Deleted, r, s)` -/
  literal : Bool := false
  deriving Inhabited

/-- Lexicographic order on identities. -/
@[inline] def idLe (a b : Nat × Nat) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)

/-- The selection of a tie-break among candidate identities, in a context of `n` events, for
the receive `e`. -/
def select (k : TieK) (n : Nat) (e : FE) (ids : List (Nat × Nat)) : Option (Nat × Nat) :=
  let least := ids.foldl (fun o a => match o with
    | none => some a | some b => if idLe a b then some a else some b) none
  let greatest := ids.foldl (fun o a => match o with
    | none => some a | some b => if idLe b a then some a else some b) none
  match k with
  | .least => least
  | .greatest => greatest
  | .parity => if n % 2 == 0 then least else greatest
  | .recv => if (e.tid + e.idx) % 2 == 0 then least else greatest

/-- The consistent sources of the receive `e` added to `X`. -/
def cands (cons : FC → Bool) (X : FC) (e : FE) : List (Nat × Nat) :=
  (X.toList.filter (fun s => s.isSend && cons (X.push { e with src := some (some s.id) }))).map
    FE.id

/-- `tie(X, e)` (Q9). -/
def tie (cons : FC → Bool) (k : TieK) (X : FC) (e : FE) : Option (Nat × Nat) :=
  select k X.size e (cands cons X e)

/-! ### Availability and scheduling (Q7) -/

/-- A next event is usable: not a blocking receive, or one with a consistent source. -/
def usable (cons : FC → Bool) (c : FC) (e : FE) : Bool :=
  if e.isRecvB then (cands cons c e).length > 0 else true

/-- The printed condition (ii): a receive is added only if an unread send to its thread with a
matching value (of any model) exists. -/
def usablePrinted (c : FC) (e : FE) : Bool :=
  match e.lab with
  | .recv _ _ p => c.any (fun s => match s.lab with
      | .send _ d v => d == e.tid && p.mem v && !(isRead c s.id)
      | _ => false)
  | _ => true

/-- `next_P`: the first usable next event in thread order (`order`). -/
def nextP (cons : FC → Bool) (V : Var) (P : FProg) (order : List Nat) (c : FC) : Option FE :=
  order.findSome? fun t =>
    match nextOf P c t with
    | some e => if (if V.printedNext then usablePrinted c e else usable cons c e) then some e
      else none
    | none => none

/-- No event is available (`availM = ∅`, Q7). -/
def fullM (cons : FC → Bool) (P : FProg) (c : FC) : Bool :=
  (List.range P.codes.size).all fun t =>
    match nextOf P c t with
    | some e => !(usable cons c e)
    | none => true

/-! ### The revisit condition (Section 2b) -/

/-- The positions of `Previous` for the event at `x`, the send at the last position `l`:
`{e' | e' ≤_H x ∨ (e', s) ∈ porf}`. -/
def prevPos (m : Array Nat) (n x : Nat) : List Nat :=
  (List.range n).filter (fun j => j ≤ x || porfM m j (n - 1))

/-- The oracle on `Y = H|Previous`, `e` at position `px` of `Y`. -/
def oracle (cons : FC → Bool) (V : Var) (Y : FC) (px : Nat) : Option (Nat × Nat) :=
  let e := Y[px]!
  match V.orc with
  | .q9 =>
    let X := (Y.toList.eraseIdx px).toArray
    tie cons V.tie X e
  | .cur =>
    match e.src with
    | some (some id) => some id
    | _ => none
  | .unread =>
    let ids := (Y.toList.filter (fun s => s.isSend && !(isRead Y s.id) &&
      cons (Y.set! px { e with src := some (some s.id) }))).map FE.id
    select .least Y.size e ids

/-- `RevisitCondition(H, e, s)`, `e` at position `x`, `s` the last event of `H`. -/
def revCond (cons : FC → Bool) (V : Var) (H : FC) (m : Array Nat) (x : Nat) : Bool :=
  let e := H[x]!
  let prev := prevPos m H.size x
  match e.lab with
  | .recv _ false _ => e.src == some none
  | .nd vs => e.out == vs.head?
  | .recv _ true _ =>
    let Y : FC := (prev.map (fun j => H[j]!)).toArray
    match prev.findIdx? (· == x) with
    | some px =>
      match oracle cons V Y px with
      | some id => e.src == some (some id)
      | none => false
    | none => false
  | _ => prev.all (fun j => H[j]!.src != some (some e.id))

/-! ### The successor function (Algorithm 1 with Q7, Q9, Q12, Q15) -/

/-- A step label, for printing paths. -/
inductive StepK
  | add (e : FE)
  | revisit (r s : Nat × Nat) (deleted : List (Nat × Nat))
  deriving Repr, Inhabited

/-- The revisits by the send `s`, just added as the last event of `H`. -/
def revisits (cons : FC → Bool) (V : Var) (H : FC) : List (StepK × FC) :=
  let n := H.size
  let l := n - 1
  let s := H[l]!
  let m := predMasks H
  (List.range l).filterMap fun pr =>
    let r := H[pr]!
    if r.isRecv && matchesL s.lab r && !(porfM m pr l) then
      let del := (List.range l).filter (fun j => pr < j && !(porfM m j l))
      let guard := (pr :: del).all (revCond cons V H m) && revCond cons V H m l
      if guard then
        let keep := (List.range l).filter (fun j => !(del.contains j))
        let G' : FC := if V.literal then
            -- `SetRF(G|E \ Deleted, r, s)` with `s ∈ Deleted`
            (keep.map (fun j => if j == pr then { H[j]! with src := some (some s.id) }
              else H[j]!)).toArray
          else
            (keep.map (fun j => if j == pr then { H[j]! with src := some (some s.id) }
              else H[j]!)).toArray.push s
        if cons G' then some (.revisit r.id s.id (del.map (fun j => H[j]!.id)), G') else none
      else none
    else none

/-- All successors of a configuration (`StepM`); `none` if `next_P` is `⊥`. -/
def succs (cons : FC → Bool) (V : Var) (P : FProg) (order : List Nat) (c : FC) :
    Option (List (StepK × FC)) :=
  match nextP cons V P order c with
  | none => none
  | some e =>
    some <| match e.lab with
    | .nd vs => vs.map (fun v => let e' := { e with out := some v }; (.add e', c.push e'))
    | .recv _ _ _ =>
      let xs : List (Option (Nat × Nat)) :=
        ((c.toList.filter FE.isSend).map (fun s => some s.id)) ++ [none]
      xs.filterMap fun x =>
        let e' := { e with src := some x }
        let c' := c.push e'
        if cons c' then some (.add e', c') else none
    | .send _ _ _ =>
      let H := c.push e
      (if cons H then [(.add e, H)] else []) ++ revisits cons V H
    | _ => [(.add e, c.push e)]

/-! ### Keys -/

/-- A code of an event, for keys. -/
def FE.code (e : FE) : List Nat :=
  let lab : List Nat := match e.lab with
    | .recv m b p => [0, if m == .asyn then 0 else 1, if b then 1 else 0] ++
        (match p with | .any => [0] | .only vs => 1 :: vs)
    | .send m d v => [1, if m == .asyn then 0 else 1, d, v]
    | .nd vs => 2 :: vs
    | .block => [3]
    | .error => [4]
  let src : List Nat := match e.src with
    | none => [0]
    | some none => [1]
    | some (some (t, i)) => [2, t, i]
  let out : List Nat := match e.out with
    | none => [0]
    | some v => [1, v]
  [e.tid, e.idx, lab.length] ++ lab ++ src ++ out

/-- Lexicographic order on lists of naturals. -/
def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: l, b :: l' => a < b || (a == b && lexLe l l')

/-- The key of a configuration: its events with sources and outcomes, sorted by identity (the
unordered graph; insertion order forgotten). -/
def key (c : FC) : List (List Nat) :=
  (c.toList.map FE.code).mergeSort lexLe

/-- Lexicographic order on keys. -/
def keyLe : List (List Nat) → List (List Nat) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: l, b :: l' => (lexLe a b && !(lexLe b a)) || (a == b && keyLe l l')

/-! ### The explorer -/

/-- The state of the explorer. -/
structure St where
  /-- remaining fuel -/
  fuel : Nat
  /-- visited configurations -/
  visited : Nat := 0
  /-- configurations with `next_P ≠ ⊥` and no successor -/
  dead : Nat := 0
  /-- the greatest depth -/
  maxDepth : Nat := 0
  /-- the greatest number of events -/
  maxEvents : Nat := 0
  /-- the keys of the reported graphs, with multiplicity -/
  reports : Array (List (List Nat)) := #[]
  /-- fuel exhausted -/
  exhausted : Bool := false
  /-- paths to the graph `target` -/
  paths : Array (List StepK) := #[]
  /-- the keys of the visited configurations (if `keepSeen`) -/
  seen : Array (List (List Nat)) := #[]
  /-- keep the keys of the visited configurations -/
  keepSeen : Bool := false
  /-- the visited configurations (if `keepCfg`) -/
  seenFC : Array FC := #[]
  /-- keep the visited configurations -/
  keepCfg : Bool := false
  deriving Inhabited

/-- `Visit`, depth-first; `n` bounds the depth, `st.fuel` the number of visits; `path` is the
reversed list of steps from the initial configuration, `target` a key whose paths are kept. -/
def dfs (cons : FC → Bool) (V : Var) (P : FProg) (order : List Nat)
    (target : Option (List (List Nat))) : Nat → Nat → List StepK → FC → St → St
  | 0, _, _, _, st => { st with exhausted := true }
  | n + 1, d, path, c, st =>
    if st.fuel == 0 then { st with exhausted := true } else
    let st : St := { st with
      fuel := st.fuel - 1
      visited := st.visited + 1
      maxDepth := max st.maxDepth d
      maxEvents := max st.maxEvents c.size
      seen := if st.keepSeen then st.seen.push (key c) else st.seen
      seenFC := if st.keepCfg then st.seenFC.push c else st.seenFC }
    match succs cons V P order c with
    | none =>
      let k := key c
      let st := { st with reports := st.reports.push k }
      if target == some k then { st with paths := st.paths.push path.reverse } else st
    | some [] => { st with dead := st.dead + 1 }
    | some l =>
      l.foldl (fun st (sk, c') => dfs cons V P order target n (d + 1) (sk :: path) c' st) st

/-- Run the explorer from the empty configuration. -/
def explore (cons : FC → Bool) (V : Var) (P : FProg) (order : List Nat) (fuel : Nat)
    (target : Option (List (List Nat)) := none) (keepSeen : Bool := false)
    (keepCfg : Bool := false) : St :=
  dfs cons V P order target fuel 0 [] #[] { fuel := fuel, keepSeen := keepSeen, keepCfg := keepCfg }

/-- The number of visits of a configuration with the key of an earlier visited one; `none` if
the run did not keep the visited keys (`keepSeen = false`). -/
def repeats (st : St) : Option Nat :=
  let s := st.seen.toList.mergeSort keyLe
  let rec go : List (List (List Nat)) → Nat
    | a :: b :: t => (if a == b then 1 else 0) + go (b :: t)
    | _ => 0
  if st.keepSeen then some (go s) else none

/-! ### The enumerator of `⟦P⟧` (independent of the algorithm) -/

/-- All one-event extensions by the next event of some thread, with every source (and `⊥`),
every ND outcome; well-formedness checks only. -/
def extend (P : FProg) (c : FC) : List FC :=
  (List.range P.codes.size).flatMap fun t =>
    match nextOf P c t with
    | none => []
    | some e =>
      match e.lab with
      | .nd vs => vs.map (fun v => c.push { e with out := some v })
      | .recv _ _ _ =>
        let xs : List (Option (Nat × Nat)) :=
          ((c.toList.filter FE.isSend).map (fun s => some s.id)) ++ [none]
        xs.filterMap fun x =>
          let c' := c.push { e with src := some x }
          if wfB c' then some c' else none
      | _ => [c.push e]

/-- Sort by key and remove duplicates. -/
def dedupKeyed (l : List (List (List Nat) × FC)) : List (List (List Nat) × FC) :=
  let s := l.mergeSort (fun a b => keyLe a.1 b.1)
  let rec go : List (List (List Nat) × FC) → List (List (List Nat) × FC)
    | a :: b :: t => if a.1 == b.1 then go (a :: t) else a :: go (b :: t)
    | l => l
  go s

/-- The executions, level by level (graphs with `k` events), deduplicated by key; `levels`
bounds the number of events. Returns all well-formed executions with at most `levels` events,
and `true` if some execution with `levels` events still has an extension (truncation). -/
def allExecsT (P : FProg) (levels : Nat) : List (List (List Nat) × FC) × Bool := Id.run do
  let mut cur : List (List (List Nat) × FC) := [(key #[], #[])]
  let mut all := cur
  for _ in [0:levels] do
    let nxt := dedupKeyed (cur.flatMap (fun (_, c) => (extend P c).map (fun c' => (key c', c'))))
    if nxt.isEmpty then return (all, false)
    all := all ++ nxt
    cur := nxt
  return (all, cur.any (fun (_, c) => !(extend P c).isEmpty))

/-- The executions with at most `levels` events. -/
def allExecs (P : FProg) (levels : Nat) : List (List (List Nat) × FC) := (allExecsT P levels).1

/-- `⟦P⟧` (Q8): consistent executions with `availM = ∅`, and the truncation flag. -/
def semT (cons : FC → Bool) (P : FProg) (levels : Nat) :
    List (List (List Nat) × FC) × Bool :=
  let (a, t) := allExecsT P levels
  (a.filter (fun (_, c) => cons c && fullM cons P c), t)

/-- `⟦P⟧` (Q8), without the truncation flag. -/
def sem (cons : FC → Bool) (P : FProg) (levels : Nat) : List (List (List Nat) × FC) :=
  (semT cons P levels).1

/-- The greatest number of actions on a path of a code. -/
partial def Code.depth : Code → Nat
  | .done => 0
  | .send _ _ _ k => k.depth + 1
  | .recv _ _ _ ks kd kb => ((kd :: kb :: ks.map (·.2)).map Code.depth).foldl max 0 + 1
  | .nd _ _ ks kd => ((kd :: ks.map (·.2)).map Code.depth).foldl max 0 + 1
  | .block | .error => 1

/-- A bound on the number of events of an execution: the sum of the depths of the codes. -/
def FProg.bound (P : FProg) : Nat := P.codes.foldl (fun n c => n + c.depth) 0

/-! ### Comparison -/

/-- The outcome of comparing an exploration with `⟦P⟧`. -/
structure Cmp where
  /-- graphs of `⟦P⟧` not reported -/
  missed : List (List (List Nat))
  /-- reported graphs not in `⟦P⟧` -/
  extra : List (List (List Nat))
  /-- graphs reported more than once, with multiplicity -/
  dups : List (List (List Nat) × Nat)
  /-- fuel exhausted -/
  exhausted : Bool
  /-- configurations with `next_P ≠ ⊥` and no successor -/
  dead : Nat
  /-- visits of a configuration `≈` an earlier visited one (`none`: not counted) -/
  repeats : Option Nat
  /-- the enumeration of `⟦P⟧` was truncated -/
  truncated : Bool
  deriving Inhabited

/-- Success: every graph of `⟦P⟧` reported exactly once and nothing else, no fuel exhaustion,
no dead end, no repeated visit (counted), no truncated enumeration. -/
def Cmp.ok (c : Cmp) : Bool :=
  c.missed.isEmpty && c.extra.isEmpty && c.dups.isEmpty && !c.exhausted && c.dead == 0 &&
    c.repeats == some 0 && !c.truncated

/-- Compare reported keys with the keys of `⟦P⟧`. -/
def compare (st : St) (semKeys : List (List (List Nat))) (truncated : Bool) : Cmp :=
  let rs := st.reports.toList.mergeSort keyLe
  let rec counts : List (List (List Nat)) → List (List (List Nat) × Nat)
    | [] => []
    | a :: t =>
      match counts t with
      | (b, k) :: u => if a == b then (b, k + 1) :: u else (a, 1) :: (b, k) :: u
      | [] => [(a, 1)]
  let cs := counts rs
  { missed := semKeys.filter (fun k => !(cs.any (fun p => p.1 == k)))
    extra := (cs.filter (fun p => !(semKeys.contains p.1))).map (·.1)
    dups := cs.filter (fun p => p.2 > 1)
    exhausted := st.exhausted
    dead := st.dead
    repeats := repeats st
    truncated := truncated }

/-! ### Printing -/

def Model.str : Model → String | .asyn => "asyn" | .p2p => "p2p"
def FPred.str : FPred → String | .any => "*" | .only vs => toString vs

def FLab.str : FLab → String
  | .recv m b p => s!"R{if b then "b" else "nb"}_{m.str}({p.str})"
  | .send m d v => s!"S_{m.str}(T{d},{v})"
  | .nd vs => s!"ND{vs}"
  | .block => "B"
  | .error => "error"

def FE.str (e : FE) : String :=
  let s := match e.src with
    | none => ""
    | some none => " <- bot"
    | some (some (t, i)) => s!" <- ({t},{i})"
  let o := match e.out with
    | none => ""
    | some v => s!" = {v}"
  s!"({e.tid},{e.idx}) {e.lab.str}{s}{o}"

def fcStr (c : FC) : String := String.intercalate "; " (c.toList.map FE.str)

/-- A key printed as a graph. -/
def keyStr (k : List (List Nat)) : String := toString k

partial def Code.str : Code → String
  | .done => "end"
  | .send m d v k => s!"send_{m.str}(T{d},{v}); {k.str}"
  | .recv m b p ks kd kb =>
    let bs := ks.map (fun (v, k) => toString v ++ " => " ++ k.str)
    let bot := if b then [] else ["bot => " ++ kb.str]
    let kind := if b then "b" else "nb"
    "recv" ++ kind ++ "_" ++ m.str ++ "(" ++ p.str ++ ") [" ++
      String.intercalate " | " (bs ++ ["_ => " ++ kd.str] ++ bot) ++ "]"
  | .nd v vs ks kd =>
    let bs := ks.map (fun (v, k) => toString v ++ " => " ++ k.str)
    "nd" ++ toString (sortDedup (v :: vs)) ++ " [" ++
      String.intercalate " | " (bs ++ ["_ => " ++ kd.str]) ++ "]"
  | .block => "block"
  | .error => "error"

def FProg.str (P : FProg) : String :=
  String.intercalate "\n"
    ((List.range P.codes.size).map (fun t => s!"  T{t}: {(P.codes.getD t .done).str}"))

def StepK.str : StepK → String
  | .add e => s!"add {e.str}"
  | .revisit r s d => s!"revisit ({r.1},{r.2}) by ({s.1},{s.2}), deleting {d}"

def pathStr (p : List StepK) : String := String.intercalate "\n      " (p.map StepK.str)

end MustFast
