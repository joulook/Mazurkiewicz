import Mazurkiewicz.Must.Fast

/-!
# The D21 search

Plan: `plan/must/lean/LEAN-PLAN.md`, Section 4 (open obligation D21), Section 6 risk 1, row M2.

For every program of a finite grammar, every order of its threads, and the tie-breaks least,
greatest, parity (context-dependent) and recv (receive-dependent) (`MustFast.TieK`), the
explorer of `Must/Fast.lean` is compared with the enumerator of `⟦P⟧`. Success (`Cmp.ok`): the
sets of unordered terminal graphs are equal, each graph is reported exactly once, the search
completes within the fuel, no configuration with `next_P ≠ ⊥` lacks a successor (dead end), no
configuration `≈` an earlier visited one is visited (repeated visit), and the enumeration of
`⟦P⟧` is not truncated (bound: the sum of the depths of the codes, `FProg.bound`).

## The grammar `G(T, L, N, models, branching, nd)`

* `T` threads `0, …, T - 1`; every thread has at least one action; at most `N` action nodes in
  the whole program (a branching action counts once, each continuation counts its own nodes);
  every path of a thread has at most `L` actions.
* Values `{0, 1}`.
* `send_m(t, v)`: `m ∈ models`, `t < T` (sending to oneself included), `v ∈ {0, 1}`.
* `recv` with attributes `⟨m, b⟩`, `m ∈ models`, blocking or non-blocking, predicate `*`, `{0}`
  or `{1}`; continuation: one for all outcomes, or (if `branching`) one per outcome: for `*`
  one for `0` and one for `1`, for `{v}` one for `v`; for non-blocking receives also a
  separate one for `⊥`; branches with equal continuations are not generated twice.
* `nd{0,1}` (if `nd`): one continuation, or (if `branching`) one per outcome.
* `block` and `error` are not generated.
* Only programs with a receive and with a send to a thread that has a receive are checked.

`main` takes `T L N models branching nd [variant] [start stride]` (`models`: `a`, `p`, `ap`;
`branching`, `nd`: `0`/`1`; `variant`: `q9` (default, the repaired algorithm), `lit`, `cur`,
`unread`, `pnext` (the printed variants, which must fail); `start stride`: check the programs
with number `≡ start (mod stride)`). `#eval main ["3", "2", "3", "a", "0", "0"]` runs it in Lean.

A run also counts runs with a configuration `≈` an earlier visited one (Theorem 4.1 (a)) and
runs with a configuration with `next_P ≠ ⊥` and no successor.

## Results (2026-11-24, round 2: four tie-breaks, failure on dead ends, repeated visits and
truncation; this machine, `/usr/bin/time`, 6 parallel slices each)

| row | grammar | program checks | runs | wall per slice | max RSS | result |
|---|---|---|---|---|---|---|
| 1 | `3 3 4 a 1 1` | 95 238 | 2 285 712 | 11 s | 31 MB | no difference |
| 2 | `3 3 4 p 1 1` | 95 238 | 2 285 712 | 12 s | 31 MB | no difference |
| 3 | `3 3 4 ap 1 1` | 1 354 824 | 32 515 776 | 245 s | 165 MB | no difference |
| 4 | `3 3 5 a 1 1` | 6 031 278 | 144 750 672 | 1048 s | 184 MB | no difference |
| 5 | `3 3 5 p 1 1` | 6 031 278 | 144 750 672 | 956 s | 184 MB | no difference |
| 6 | `4 2 5 a 0 0` | 1 645 440 | 157 962 240 | 1137 s | 9 MB | no difference |
| 7 | `4 2 5 p 0 0` | 1 645 440 | 157 962 240 | 1324 s | 9 MB | no difference |

The rows overlap (a program of a smaller row is again a program of a larger one); the total,
16 898 736, counts program checks, not distinct programs. Every run had no dead end and no
repeated visit. Coverage limits: mixed `asyn`/`p2p` programs only up to `N = 4` (row 3); the
four-thread rows have neither branching nor ND; no `block`/`error`, `cd`/`mbox`, three or more
values, or longer paths. The printed variants fail at once: `lit`, `unread`, `pnext` on
`3 2 3 a 0 0`, `cur` on `4 1 4 a 0 0`. Round 1 (three tie-breaks, dead ends and repeated visits
counted but not failures, repeated visits not counted on rows 1, 2, 4, 5): same rows, no
difference, no dead end.
-/

namespace MustFast

/-- The parameters of the grammar. -/
structure Gram where
  threads : Nat
  maxLen : Nat
  maxNodes : Nat
  models : List Model
  branching : Bool
  nd : Bool
  deriving Inhabited

/-- The predicates of receives. -/
def preds : List FPred := [.any, .only [0], .only [1]]

/-- The values. -/
def vals : List Nat := [0, 1]

/-- Codes of depth `≤ d` with at most `b` nodes, with their number of nodes. -/
def gen (g : Gram) : Nat → Nat → List (Code × Nat)
  | 0, _ => [(.done, 0)]
  | _, 0 => [(.done, 0)]
  | d + 1, b + 1 =>
    let sub := gen g d b
    let subB (k : Nat) := sub.filter (fun p => p.2 ≤ k)
    let sends := g.models.flatMap fun m => (List.range g.threads).flatMap fun t =>
      vals.flatMap fun v => sub.map fun (k, n) => (Code.send m t v k, n + 1)
    let recvs := g.models.flatMap fun m => [true, false].flatMap fun blk => preds.flatMap fun p =>
      let uni := sub.map fun (k, n) => (Code.recv m blk p [] k k, n + 1)
      let br : List (Code × Nat) := if !g.branching then [] else
        match p with
        | .any =>
          -- continuation for 0 and for 1 (and for ⊥ if non-blocking)
          sub.flatMap fun (k0, n0) => (subB (b - n0)).flatMap fun (k1, n1) =>
            if blk then
              (if n0 == n1 && k0.str == k1.str then []
               else [(Code.recv m blk p [(0, k0)] k1 .done, n0 + n1 + 1)])
            else (subB (b - n0 - n1)).filterMap fun (kb, nb) =>
              if n0 == n1 && k0.str == k1.str && k1.str == kb.str then none
              else some (Code.recv m blk p [(0, k0)] k1 kb, n0 + n1 + nb + 1)
        | _ =>
          if blk then [] else
          sub.flatMap fun (k0, n0) => (subB (b - n0)).filterMap fun (kb, nb) =>
            if n0 == nb && k0.str == kb.str then none
            else some (Code.recv m blk p [] k0 kb, n0 + nb + 1)
      uni ++ br
    let nds : List (Code × Nat) := if !g.nd then [] else
      let uni := sub.map fun (k, n) => (Code.nd 0 [1] [] k, n + 1)
      let br : List (Code × Nat) := if !g.branching then [] else
        sub.flatMap fun (k0, n0) => (subB (b - n0)).filterMap fun (k1, n1) =>
          if n0 == n1 && k0.str == k1.str then none
          else some (Code.nd 0 [1] [(0, k0)] k1, n0 + n1 + 1)
      uni ++ br
    [(.done, 0)] ++ sends ++ recvs ++ nds

/-- Facts about a code: it receives; the destinations of its sends. -/
partial def Code.facts : Code → Bool × List Nat
  | .done | .block | .error => (false, [])
  | .send _ t _ k => let (r, ds) := k.facts; (r, t :: ds)
  | .recv _ _ _ ks kd kb =>
    let fs := (kd :: kb :: ks.map (·.2)).map Code.facts
    (true, fs.flatMap (·.2))
  | .nd _ _ ks kd =>
    let fs := (kd :: ks.map (·.2)).map Code.facts
    (fs.any (·.1), fs.flatMap (·.2))

/-- The program is worth checking: some thread receives, and some send goes to such a thread. -/
def useful (cs : List Code) : Bool :=
  let fs := cs.map Code.facts
  let recvT := (List.range cs.length).filter (fun t => (fs.getD t (false, [])).1)
  !recvT.isEmpty && fs.any (fun f => f.2.any (fun d => recvT.contains d))

/-- The codes of one thread with exactly `n` nodes. -/
def codesExact (g : Gram) (n : Nat) : List Code :=
  ((gen g g.maxLen g.maxNodes).filter (fun p => p.2 == n)).map (·.1)

/-- The compositions `(n₁, …, n_T)` with `nᵢ ≥ 1` and sum at most `N`. -/
def comps : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | k + 1, b => (List.range b).flatMap fun i =>
      (comps k (b - (i + 1))).map ((i + 1) :: ·)

/-- All programs of the grammar, as a list (for small grammars). -/
def programs (g : Gram) : List (List Code) :=
  let tables := (List.range (g.maxNodes + 1)).map (codesExact g)
  let rec prod : List (List Code) → List (List Code)
    | [] => [[]]
    | a :: t => a.flatMap fun c => (prod t).map (c :: ·)
  ((comps g.threads g.maxNodes).flatMap fun c => prod (c.map (tables.getD · []))).filter useful

/-- Insert `a` at every position. -/
def insAll (a : Nat) : List Nat → List (List Nat)
  | [] => [[a]]
  | b :: l => (a :: b :: l) :: (insAll a l).map (b :: ·)

/-- All permutations of a list. -/
def perms : List Nat → List (List Nat)
  | [] => [[]]
  | a :: l => (perms l).flatMap (insAll a)

/-! ### The check of one program -/

/-- The result of checking one program. -/
structure Res where
  /-- runs (orders × tie-breaks) -/
  runs : Nat := 0
  /-- visited configurations over all runs -/
  visited : Nat := 0
  /-- the greatest number of visits of one run -/
  maxVisited : Nat := 0
  /-- the greatest size of `⟦P⟧` -/
  maxSem : Nat := 0
  /-- runs with a configuration with `next_P ≠ ⊥` and no successor -/
  deadRuns : Nat := 0
  /-- the first failure, printed -/
  fail : Option String := none
  /-- runs with a repeated visit (a configuration `≈` an earlier visited one) -/
  repeatRuns : Nat := 0
  /-- the first such run, printed -/
  firstRepeat : Option String := none
  deriving Inhabited

def tieStr : TieK → String
  | .least => "least" | .greatest => "greatest" | .parity => "parity" | .recv => "recv"

/-- A printed configuration from a key. -/
def semStr (s : List (List (List Nat) × FC)) (k : List (List Nat)) : String :=
  match s.find? (fun p => p.1 == k) with
  | some (_, c) => fcStr c
  | none => keyStr k

/-- Check one program under every order and the four tie-breaks. The enumeration bound is
`FProg.bound + 1` (the sum of the depths of the codes); a truncated enumeration is a failure,
as are a dead end and a repeated visit (`Cmp.ok`). -/
def check (base : Var) (fuel : Nat) (cs : List Code) (acc : Res) : Res := Id.run do
  let P : FProg := ⟨cs.toArray⟩
  let (s, trunc) := semT consAP P (P.bound + 1)
  let semKeys := s.map (·.1)
  let mut r := { acc with maxSem := max acc.maxSem s.length }
  for order in perms (List.range cs.length) do
    for k in [TieK.least, .greatest, .parity, .recv] do
      let V := { base with tie := k }
      let st := explore consAP V P order fuel none true
      let c := compare st semKeys trunc
      let rp := (repeats st).getD 0
      if rp > 0 then
        r := { r with repeatRuns := r.repeatRuns + 1 }
        if r.firstRepeat.isNone then
          let msg := s!"program:\n{P.str}\norder: {order}\ntie: {tieStr k}\nrepeated visits {rp}"
          r := { r with firstRepeat := some msg }
      r := { r with
        runs := r.runs + 1
        visited := r.visited + st.visited
        maxVisited := max r.maxVisited st.visited
        deadRuns := r.deadRuns + (if st.dead > 0 then 1 else 0) }
      if !c.ok && r.fail.isNone then
        let hdr := s!"COUNTEREXAMPLE\nprogram:\n{P.str}\norder: {order}\ntie: {tieStr k}\n" ++
          s!"visited {st.visited}, |sem| {s.length}, reported {st.reports.size}, " ++
          s!"fuel exhausted {c.exhausted}, dead ends {c.dead}, repeated visits {c.repeats}, " ++
          s!"enumeration truncated {c.truncated}\n"
        let mis := c.missed.map (fun k => s!"  missed: {semStr s k}")
        let ext := c.extra.map (fun k => s!"  extra (not in sem): {keyStr k}")
        let dup := c.dups.map fun (k, n) =>
          let st' := explore consAP V P order fuel (some k)
          let ps := st'.paths.toList.map (fun p => "    path:\n      " ++ pathStr p)
          s!"  reported {n} times: {semStr s k}\n" ++ String.intercalate "\n" ps
        r := { r with fail := some (hdr ++ String.intercalate "\n" (mis ++ ext ++ dup)) }
  return r

/-- Parse the models argument. -/
def parseModels : String → List Model
  | "a" => [.asyn]
  | "p" => [.p2p]
  | _ => [.asyn, .p2p]

/-- Parse the variant argument. -/
def parseVar : String → Var
  | "lit" => { literal := true }
  | "cur" => { orc := .cur }
  | "unread" => { orc := .unread }
  | "pnext" => { printedNext := true }
  | _ => {}

/-- Iterate `k` over the products of the arrays; `k` returns `false` to stop. -/
partial def prodIO (ls : List (Array Code)) (pre : List Code) (k : List Code → IO Bool) :
    IO Bool :=
  match ls with
  | [] => k pre.reverse
  | a :: t => do
    for c in a do
      if !(← prodIO t (c :: pre) k) then return false
    return true

/-- Run the search over the programs with number `≡ start (mod stride)`; returns the number of
programs checked and the result; `count`: only count. -/
def search (g : Gram) (base : Var) (start stride : Nat) (count : Bool := false)
    (progress : Bool := false) : IO (Nat × Res) := do
  let tables : Array (Array Code) :=
    (List.range (g.maxNodes + 1)).toArray.map (fun n => (codesExact g n).toArray)
  let r ← IO.mkRef ({} : Res)
  let k ← IO.mkRef 0
  let i ← IO.mkRef 0
  let t0 ← IO.monoMsNow
  for c in comps g.threads g.maxNodes do
    let ls := c.map (fun n => tables.getD n #[])
    let go ← prodIO ls [] fun cs => do
      if !(useful cs) then return true
      let n ← i.modifyGet (fun n => (n, n + 1))
      if n % stride != start then return true
      k.modify (· + 1)
      if count then return true
      let r' := check base 1000000 cs (← r.get)
      r.set r'
      let kk ← k.get
      if progress && kk % 5000 == 0 then
        let t1 ← IO.monoMsNow
        IO.eprintln s!"  {kk} programs, {r'.runs} runs, {(t1 - t0) / 1000} s"
      return r'.fail.isNone
    if !go then break
  return (← k.get, ← r.get)

/-- A summary line. -/
def summary (g : Gram) (n : Nat) (r : Res) (countOnly : Bool := false) : String :=
  s!"grammar T={g.threads} L={g.maxLen} N={g.maxNodes} models={g.models.map Model.str} " ++
  s!"branching={g.branching} nd={g.nd}: programs {n}, runs {r.runs}, visited {r.visited}, " ++
  s!"max visited/run {r.maxVisited}, max |sem| {r.maxSem}, runs with dead ends {r.deadRuns}, " ++
  s!"runs with a repeated visit {r.repeatRuns}\n" ++
  (match r.firstRepeat with | none => "" | some f => "first repeated visit:\n" ++ f ++ "\n") ++
  (if countOnly then "COUNT ONLY (nothing checked)" else
    match r.fail with | none => "RESULT: no difference" | some f => "RESULT:\n" ++ f)

end MustFast

open MustFast in
/-- `search T L N models branching nd [variant [start stride]]`; variant `count` only counts. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | t :: l :: n :: ms :: br :: nd :: rest =>
    let g : Gram := {
      threads := t.toNat!
      maxLen := l.toNat!
      maxNodes := n.toNat!
      models := parseModels ms
      branching := br == "1"
      nd := nd == "1" }
    let (vs, start, stride) := match rest with
      | [v] => (v, 0, 1)
      | [v, a, b] => (v, a.toNat!, b.toNat!)
      | _ => ("q9", 0, 1)
    let t0 ← IO.monoMsNow
    let (k, r) ← search g (parseVar vs) start stride (vs == "count") true
    let t1 ← IO.monoMsNow
    IO.println s!"slice {start} mod {stride}, variant {vs}"
    IO.println (summary g k r (vs == "count"))
    IO.println s!"time {(t1 - t0) / 1000} s"
    return 0
  | _ =>
    IO.println "usage: search T L N models(a|p|ap) branching(0|1) nd(0|1) [variant [start stride]]"
    return 1
