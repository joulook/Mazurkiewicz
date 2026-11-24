import Mazurkiewicz.Must.Examples
import Mazurkiewicz.Must.Search

/-!
# The fast engine against the reference definitions

`Must/Fast.lean` (used by the D21 search) and `Program.lean` … `Enum.lean` (on `Graph`) implement
the same explorer and enumerator twice. `agree cs` runs both on the program `cs` under every
order of its threads (`agreeOrders`: every `k`-th order) and eight variants: the repaired
algorithm with the four tie-breaks, and the printed variants `lit`, `cur`, `unread`, `pnext`.
For each run it requires:

* the `Config` invariant on every visited and reported reference configuration (`invB`: the
  order has no repetition, its elements are the events, it contains `po`), checked before the
  conversion `toFC` (which reads the order);
* neither run exhausted its fuel;
* the sequence of visited configurations equal, with insertion orders (`seen`, `seenFC`);
* the reported graphs equal with multiplicity, the dead-end and repeated-visit counts equal;
* at every visited configuration, the ordered list of successors equal (with insertion orders);

and, per program, the enumerated `⟦P⟧` and its truncation flag equal.

Shared by both layers, so not tested by this check: `MustFast.Code.run` (the program), the
choice of the tie-break and of the variants, keys. All results here are `#eval`s, not theorems
(`decide +kernel` on `agree` does not finish in reasonable time).

Samples of the searched grammars (2026-11-24, `lake env lean` on scratch files with
`#eval (ps.length, (ps.filter (fun cs => !agree cs)).map …)`, `ps := sampleProgs g k`, every
`k`-th program in the order of `Search.lean`), no disagreement:

| grammar | `k` | programs | wall |
|---|---|---|---|
| `3 3 4 a 1 1` | 1000 | 96 | 179 s |
| `3 3 4 p 1 1` | 1000 | 96 | 215 s |
| `3 3 4 ap 1 1` | 1000 | 1355 | 3450 s |
| `3 3 5 a 1 1` | 10000 | 604 | 3032 s |
| `3 3 5 p 1 1` | 10000 | 604 | 2876 s |
| `4 2 5 a 0 0` | 10000 | 165 | 3105 s |
| `4 2 5 p 0 0` | 10000 | 165 | 3153 s |

(The `3 3 5` and `4 2 5` rows are sampled at 1/10000, not 1/1000: at about 5 s per program in
the interpreter, 1/1000 would take 3 to 8 hours each.) Round 1 (weaker check, repaired
algorithm only, three tie-breaks): all of `G(2,3,3,a,1,1)` and `G(2,2,3,p,1,1)`, every 5th of
`G(3,1,3,ap,0,0)`, no disagreement. The evaluations of this file take about 16 minutes.
-/

namespace Must

namespace CrossCheck

open MustFast MustFast' Examples

/-- A model of `Must/Event.lean` in the core (`cd`, `mbox` do not occur). -/
def toModel : Comm → MustFast.Model
  | .p2p => .p2p
  | _ => .asyn

/-- A label in the core. A finite predicate becomes the sorted list `ndList s`: the predicates
`.only vs` of the compared programs must have sorted lists without repetition (all codes here
and in the search grammar do), since keys and `FE` equality compare the lists. -/
def toFLab : Lab VPred → FLab
  | .recv a p => .recv (toModel a.model) a.blocking
      (match p with | .any => .any | .fin s => .only (ndList s))
  | .send m d v => .send (toModel m) d v
  | .nd S => .nd (ndList S)
  | .block => .block
  | .error => .error

/-- A configuration in the core. -/
def toFC (c : Config VPred) : FC :=
  (c.order.map fun e =>
    ({ tid := e.tid, idx := e.idx, lab := toFLab e.lab
       src := (c.G.rf e).map (fun x => match x with
         | .bot => none
         | .snd s => some (s.tid, s.idx))
       out := c.G.nd e } : FE)).toArray

/-- The variants compared. -/
inductive VarK
  | rep (k : TieK)
  | lit
  | cur
  | unread
  | pnext

/-- The selection of the reference layer for a tie-break of the core. -/
def sel : TieK → Sel VPred
  | .least => .least
  | .greatest => .greatest
  | .parity => .parity
  | .recv => .byRecv

/-- The variant in the reference layer. -/
def refVar : VarK → Variant VPred
  | .rep k => rep (sel k)
  | .lit => litV
  | .cur => curV
  | .unread => unreadV
  | .pnext => pnextV

/-- The variant in the core. -/
def fastVar : VarK → Var
  | .rep k => { tie := k }
  | .lit => { literal := true }
  | .cur => { orc := .cur }
  | .unread => { orc := .unread }
  | .pnext => { printedNext := true }

/-- The eight variants. -/
def allVars : List VarK :=
  [.rep .least, .rep .greatest, .rep .parity, .rep .recv, .lit, .cur, .unread, .pnext]

/-- The `Config` invariant: the order has no repetition, its elements are the events of the
graph, and it contains `po`. -/
def invB (c : Config VPred) : Bool :=
  decide (c.order.Nodup ∧ c.order.toFinset = c.G.events ∧
    ∀ a ∈ c.order, ∀ b ∈ c.order, a.tid = b.tid → a.idx < b.idx →
      c.order.idxOf a < c.order.idxOf b)

/-- The successors of a configuration in both layers, with insertion orders. -/
def succAgree (v : VarK) (P : Program VPred) (F : FProg) (c : Config VPred) : Bool :=
  ((stepM AP (refVar v) P c).map (fun l => l.map toFC)) ==
    ((succs consAP (fastVar v) F P.threads (toFC c)).map (fun l => l.map (·.2)))

/-- Both layers agree on one order and variant. -/
def agreeRun (F : FProg) (P : Program VPred) (v : VarK) : Bool :=
  let r := explore AP (refVar v) P 100000
  let st := MustFast.explore consAP (fastVar v) F P.threads 100000 none true true
  !r.exhausted && !st.exhausted &&
  (r.seen ++ r.reported).all invB &&
  r.seen.map toFC == st.seenFC.toList &&
  (r.reported.map (fun c => MustFast.key (toFC c))).mergeSort keyLe ==
    st.reports.toList.mergeSort keyLe &&
  r.dead == st.dead && some (repeatedVisits r) == repeats st &&
  r.seen.all (succAgree v P F)

/-- Both layers agree on the program `cs`, every `k`-th order of its threads. -/
def agreeOrders (k : ℕ) (cs : List Code) : Bool :=
  let P := ofCodes cs
  let F : FProg := ⟨cs.toArray⟩
  let lv := F.bound + 1
  let semR := ((semEnum AP P lv).map (fun c => MustFast.key (toFC c))).mergeSort keyLe
  let (sF, tF) := MustFast.semT consAP F lv
  semR == (sF.map (·.1)).mergeSort keyLe && semTruncated P lv == tF && !tF &&
  (P.orders.zipIdx.filter (fun p => p.2 % k == 0)).all fun (P', _) =>
    allVars.all (agreeRun F P')

/-- Both layers agree on the program `cs`. -/
def agree (cs : List Code) : Bool := agreeOrders 1 cs

/-- Every `k`-th program of a grammar, in the order of `Search.lean` (streamed). -/
def sampleProgs (g : Gram) (k : ℕ) : List (List Code) :=
  let tables := (List.range (g.maxNodes + 1)).map (codesExact g)
  let rec go : List (List Code) → List Code → ℕ × List (List Code) → ℕ × List (List Code)
    | [], pre, (n, acc) =>
      if useful pre.reverse then (n + 1, if n % k == 0 then pre.reverse :: acc else acc)
      else (n, acc)
    | a :: t, pre, st => a.foldl (fun st c => go t (c :: pre) st) st
  ((comps g.threads g.maxNodes).foldl
    (fun st c => go (c.map (tables.getD · [])) [] st) (0, [])).2.reverse

/-- The programs of `Examples.lean`. -/
def exPrograms : List (List Code) :=
  [[Code.done, sp 3 1 (sp 2 2), rbp (sp 3 3), rbp rbp], [.done, ex32code],
  [.done, ex32code, sp 1 1 (sp 1 2)], [.done, sa 3 1, sa 3 2, rb],
  [sa 1 0, rb, sa 1 1], [.done, sp 3 1, sp 3 2, rbp, sp 3 3], [.done, rnb], [.done, rbp, sa 1 1],
  [sa 1 0, rb (sa 0 0), sa 1 1], [rnb, rb, sa 1 1, sa 1 2 (sa 0 9)],
  [sa 2 0, rb, rb, sa 1 0 (sa 2 1)]]

/-- Example 4.3, complete (five threads and the empty thread `0`). -/
def ex43code : List Code := [.done, sa 1 0 rb, sa 4 1, sa 4 2, rb, sa 1 42]

/-- Targeted programs: revisits with non-empty deletions; competing sends of one thread;
selective `p2p` receives skipping an earlier send (inversions); ND-dependent continuations. -/
def targeted : List (List Code) :=
  [ -- deletions
    [sa 1 0, rb (rb (sa 0 1)), sa 1 1, sa 1 2],
    [sa 1 0, rb (sa 2 0), rb (sa 1 1)],
    [rnb (sa 1 0), rb (sa 0 1), sa 1 2 (sa 0 3)],
    -- competing sends of one thread
    [.done, sa 2 1 (sa 2 2), rb rb],
    [.done, sp 2 1 (sp 2 2), rbp rbp],
    [.done, sp 2 1 (sp 2 2), rbp, sp 2 3],
    -- selective p2p inversions
    [.done, sp 2 0 (sp 2 1),
      .recv .p2p true (.only [1]) [] (.recv .p2p true (.only [0]) [] .done .done) .done],
    [.done, sp 2 0 (sp 2 1), .recv .p2p false (.only [1]) [] rbp rbp],
    [.done, sp 2 0 (sp 2 1), .recv .p2p true (.only [1]) [] .done .done, sp 2 1],
    -- ND-dependent continuations
    [.nd 0 [1] [(0, sa 1 0)] (sa 1 1), .recv .asyn true (.only [1]) [] (sa 0 5) .done, sa 1 1],
    [.nd 0 [1] [(0, rb)] (sa 1 0), .recv .asyn false .any [(0, sa 0 1)] .done (sa 0 2)],
    [.done, ex32code, sp 1 1 (sp 1 2), sp 1 2]]

/- `true` -/
#eval (exPrograms ++ targeted).all agree

/- Example 4.3 complete, every 30th of its 720 orders (24 orders × 8 variants): `true` -/
#eval agreeOrders 30 ex43code

/-- The D21 check of `Search.lean` (every order, four tie-breaks) on the examples and the
targeted programs, Example 4.3 complete (720 orders): number of runs, and `true` if no
difference (with the round-2 criterion: no dead end, no repeated visit, no truncation). -/
def exD21 : ℕ × Bool :=
  let r := (exPrograms ++ targeted ++ [ex43code]).foldl (fun r cs => check {} 100000 cs r) {}
  (r.runs, r.fail.isNone)

/- `(4416, true)` -/
#eval exD21

end CrossCheck

end Must
