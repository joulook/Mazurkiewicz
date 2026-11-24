import Mazurkiewicz.Must.Enum
import Mazurkiewicz.Must.GraphEx

/-!
# Computed examples and the witnesses of the fate table (M2)

Paper: Examples 3.1, 3.2, 4.1, 4.2, 4.3; Section 3.3 (`⟦P⟧`), Algorithm 1, p. 19. Plan:
Section 3, rows marked M2; readings `M0-astra.md` 15, 16, 19, 20, 23; `M0-opus.md` D6, D8, D10,
D13, D14; `PLAN-r1-opus.md`, `PLAN-r1-astra.md` (p. 19, lines 11/13); `PLAN-r3-astra.md` (fuel).

Programs are lists of `MustFast.Code`; thread `t` runs code number `t` (`ofCodes`), threads in
the order `0, 1, …` unless `reorder`ed. Where the paper numbers threads from `T1`, code `0` is
an empty thread, so that thread `Ti` is `i`. Consistency is `Graph.consAPB` (`asyn` and `p2p`,
`AP`). Every theorem is proved by `decide +kernel` on the reference functions of
`Program.lean` … `Enum.lean`; the `#eval` lines print the same computations (outputs recorded
in the comments).

Each `ok` below means (`CmpR.ok`): the explorer completed within the fuel, the set of unordered
terminal graphs it reports equals the set enumerated by `semEnum`, each reported exactly once,
no visited configuration with `next_P ≠ ⊥` has no successor, no configuration `≈` an earlier
one is visited, and the enumeration is not truncated at the level bound.
-/

namespace Must

namespace Examples

open MustFast MustFast'

/-! ### Notation -/

/-- Consistency for `asyn` and `p2p`. -/
abbrev AP : Graph VPred → Bool := Graph.consAPB

/-- A blocking `asyn` receive accepting every value, then `k`. -/
def rb (k : Code := .done) : Code := .recv .asyn true .any [] k .done
/-- A non-blocking `asyn` receive accepting every value, then `k` (also after `⊥`). -/
def rnb (k : Code := .done) : Code := .recv .asyn false .any [] k k
/-- An `asyn` send. -/
def sa (d v : Nat) (k : Code := .done) : Code := .send .asyn d v k
/-- A `p2p` send. -/
def sp (d v : Nat) (k : Code := .done) : Code := .send .p2p d v k
/-- A blocking `p2p` receive accepting every value, then `k`. -/
def rbp (k : Code := .done) : Code := .recv .p2p true .any [] k .done

/-- The repaired algorithm with a tie-break. -/
abbrev rep (T : Sel VPred) : Variant VPred := Variant.repaired AP T

/-- Explorer and enumerator agree (see the module docstring). -/
def okWith (V : Variant VPred) (P : Program VPred) (fuel levels : ℕ) : Bool :=
  (compareR (explore AP V P fuel) (semEnum AP P levels) (semTruncated P levels)).ok

/-- The reported graphs are, up to order, the given graphs (by key). -/
def reportsAre (V : Variant VPred) (P : Program VPred) (fuel : ℕ) (gs : List (Graph VPred)) :
    Bool :=
  decide (((explore AP V P fuel).reported.map (fun c => c.G.key)).Perm (gs.map Graph.key))

/-- The enumerated `⟦P⟧` is, up to order, the given graphs (by key). -/
def semIs (P : Program VPred) (levels : ℕ) (gs : List (Graph VPred)) : Bool :=
  decide (((semEnum AP P levels).map (fun c => c.G.key)).Perm (gs.map Graph.key))

/-- The number of visits of configurations with the key of `g`. -/
def visitsOf (V : Variant VPred) (P : Program VPred) (fuel : ℕ) (g : Graph VPred) : ℕ :=
  ((explore AP V P fuel).seen.filter (fun c => decide (c.G.key = g.key))).length

/-- A configuration with the order and key of `c` is visited. -/
def visited (V : Variant VPred) (P : Program VPred) (fuel : ℕ) (c : Config VPred) : Bool :=
  (explore AP V P fuel).seen.any (fun d => decide (d.order = c.order ∧ d.G.key = c.G.key))

/-- A successor of `c` (by `stepM`) has the order `o` and the key of `g`. -/
def hasSucc (V : Variant VPred) (P : Program VPred) (c : Config VPred) (o : List (Ev VPred))
    (g : Graph VPred) : Bool :=
  ((stepM AP V P c).getD []).any (fun d => decide (d.order = o ∧ d.G.key = g.key))

/-- A summary: visited configurations, reported graphs, `|⟦P⟧|`, agreement, dead ends, repeated
visits, depth, events. -/
def summary (V : Variant VPred) (P : Program VPred) (fuel levels : ℕ) : String :=
  let r := explore AP V P fuel
  let s := semEnum AP P levels
  let c := compareR r s (semTruncated P levels)
  s!"visited {r.visited}, reported {r.reported.length}, |sem| {s.length}, ok {c.ok}, " ++
  s!"missed {c.missed.length}, extra {c.extra.length}, dups {c.dups.length}, dead {r.dead}, " ++
  s!"repeated visits {repeatedVisits r}, depth {r.maxDepth}, events {r.maxEvents}"

/-! ### Printing -/

def vpStr : VPred → String
  | .any => "*"
  | .fin s => toString (ndList s)

def commStr : Comm → String
  | .asyn => "asyn" | .p2p => "p2p" | .cd => "cd" | .mbox => "mbox"

def labStr : Lab VPred → String
  | .recv a p => s!"R{if a.blocking then "b" else "nb"}_{commStr a.model}({vpStr p})"
  | .send m d v => s!"S_{commStr m}(T{d},{v})"
  | .nd S => s!"ND{ndList S}"
  | .block => "B"
  | .error => "error"

def evStr (G : Graph VPred) (e : Ev VPred) : String :=
  let s := match G.rf e with
    | some .bot => " <- bot"
    | some (.snd x) => s!" <- ({x.tid},{x.idx})"
    | none => ""
  let o := match G.nd e with
    | some v => s!" = {v}"
    | none => ""
  s!"({e.tid},{e.idx}) {labStr e.lab}{s}{o}"

/-- A configuration in insertion order. -/
def cfgStr (c : Config VPred) : String := String.intercalate "; " (c.order.map (evStr c.G))

/-! ### Example 3.1 -/

/-- `T1: send(T3, 1); send(T2, 2)`, `T2: recv(); send(T3, 3)`, `T3: recv(); recv()`, `p2p`. -/
def ex31 : Program VPred := ofCodes [.done, sp 3 1 (sp 2 2), rbp (sp 3 3), rbp rbp]

/-- Its `p2p`-consistent graphs are the two graphs of the paper, `GraphEx.ex31a` (`T3` reads
`1`, then `3`) and `GraphEx.ex31b` (`3`, then `1`); the explorer reports exactly these. -/
theorem ex31_sem : semIs ex31 10 [GraphEx.ex31a, GraphEx.ex31b] = true ∧
    reportsAre (rep .least) ex31 1000 [GraphEx.ex31a, GraphEx.ex31b] = true := by decide +kernel

theorem ex31_ok : okWith (rep .least) ex31 1000 10 = true ∧
    okWith (rep .byRecv) ex31 1000 10 = true := by decide +kernel

/- `visited 9, reported 2, |sem| 2, ok true, missed 0, extra 0, dups 0, dead 0,
repeated visits 0, depth 6, events 6` -/
#eval summary (rep .least) ex31 1000 10
/- The two graphs:
`(1,0) S_p2p(T3,1); (1,1) S_p2p(T2,2); (2,0) Rb_p2p(*) <- (1,1); (2,1) S_p2p(T3,3);
 (3,0) Rb_p2p(*) <- (1,0); (3,1) Rb_p2p(*) <- (2,1)` and the same with `T3` reading `(2,1)`
first, then `(1,0)`. -/
#eval (semEnum AP ex31 10).map cfgStr

/-! ### Example 3.2 -/

/-- `T1: a := recv_p2p(x ∈ {1, 2}); b := nondet({0, 1}); send_p2p(T1, a + b)` (p. 15). -/
def ex32code : Code :=
  .recv .p2p true (.only [1, 2])
    [(1, .nd 0 [1] [(0, sp 1 1)] (sp 1 2)), (2, .nd 0 [1] [(0, sp 1 2)] (sp 1 3))] .done .done

def ex32 : Program VPred := ofCodes [.done, ex32code]

/-- The transition system of the paper, as the trace function: the label after each trace; the
payload of the send is `a + b`, so it depends on the ND outcome. -/
theorem ex32_lts :
    ex32.step 1 [] = some (.recv ⟨.p2p, true⟩ (.fin {1, 2})) ∧
    ex32.step 1 [some 1] = some (.nd {0, 1}) ∧
    ex32.step 1 [some 2] = some (.nd {0, 1}) ∧
    ex32.step 1 [some 1, some 0] = some (.send .p2p 1 1) ∧
    ex32.step 1 [some 1, some 1] = some (.send .p2p 1 2) ∧
    ex32.step 1 [some 2, some 0] = some (.send .p2p 1 2) ∧
    ex32.step 1 [some 2, some 1] = some (.send .p2p 1 3) ∧
    ex32.step 1 [some 1, some 0, none] = none ∧
    ex32.step 1 [none] = none := by decide +kernel

/-- Alone, the receive has no source: `⟦P⟧` is the empty graph. -/
theorem ex32_sem : (semEnum AP ex32 10).map (fun c => c.order.length) = [0] := by decide +kernel

theorem ex32_ok : okWith (rep .least) ex32 1000 10 = true := by decide +kernel

/-- With a second thread `T2: send_p2p(T1, 1); send_p2p(T1, 2)`. -/
def ex32ctx : Program VPred := ofCodes [.done, ex32code, sp 1 1 (sp 1 2)]

/-- `p2p`: `T1` reads `1` (reading `2` first leaves the earlier matching `1` unread,
Definition 3.5 (b)); the two ND outcomes give the sends `S(T1, 1)` and `S(T1, 2)`. -/
theorem ex32ctx_sem : (semEnum AP ex32ctx 10).map cfgStr =
    ["(2,0) S_p2p(T1,1); (1,0) Rb_p2p([1, 2]) <- (2,0); (1,1) ND[0, 1] = 0; " ++
      "(1,2) S_p2p(T1,1); (2,1) S_p2p(T1,2)",
     "(2,0) S_p2p(T1,1); (1,0) Rb_p2p([1, 2]) <- (2,0); (1,1) ND[0, 1] = 1; " ++
      "(1,2) S_p2p(T1,2); (2,1) S_p2p(T1,2)"] := by decide +kernel

theorem ex32ctx_ok : okWith (rep .least) ex32ctx 1000 10 = true := by decide +kernel

/- `visited 9, reported 2, |sem| 2, ok true, …, depth 5, events 5` -/
#eval summary (rep .least) ex32ctx 1000 10

/-! ### Examples 4.1, 4.2: `A + B + C` -/

/-- `T1: send(T3, 1)`, `T2: send(T3, 2)`, `T3: recv()`. -/
def abc : Program VPred := ofCodes [.done, sa 3 1, sa 3 2, rb]

/-- Example 4.1: `T3` first (order `T3, T1, T2`). -/
def ex41 : Program VPred := abc.reorder [3, 0, 1, 2] (by decide)

/-- Example 4.2: `T1`, `T3` before `T2`. -/
def ex42 : Program VPred := abc.reorder [0, 1, 3, 2] (by decide)

/-- The sends of `A + B + C`. -/
abbrev abcS1 : Ev VPred := ⟨1, 0, .send .asyn 3 1⟩
abbrev abcS2 : Ev VPred := ⟨2, 0, .send .asyn 3 2⟩
abbrev abcR : Ev VPred := ⟨3, 0, .recv ⟨.asyn, true⟩ .any⟩

/-- Graph 1 of Examples 4.1, 4.2: the receive reads `1`. -/
def abcG1 : Graph VPred := ((Graph.empty.addSend abcS1).addSend abcS2).addRecv abcR (.snd abcS1)
/-- Graph 2: the receive reads `2`. -/
def abcG2 : Graph VPred := ((Graph.empty.addSend abcS1).addSend abcS2).addRecv abcR (.snd abcS2)

theorem ex41_sem : semIs ex41 10 [abcG1, abcG2] = true ∧
    reportsAre (rep .least) ex41 1000 [abcG1, abcG2] = true ∧
    reportsAre (rep .least) ex42 1000 [abcG1, abcG2] = true := by decide +kernel
theorem ex41_ok : okWith (rep .least) ex41 1000 10 = true := by decide +kernel
theorem ex42_ok : okWith (rep .least) ex42 1000 10 = true := by decide +kernel

/- Example 4.1, visited configurations in order: `∅`; `S(T3,1)` (the receive of `T3` is not
available at `∅`); `S(T3,1); R <- S(T3,1)` (Q7 wakes the receive at the first usable send; the
paper's schedule adds both sends first); `… ; S(T3,2)`; the revisit `S(T3,1); R <- S(T3,2);
S(T3,2)`. -/
#eval (explore AP (rep .least) ex41 1000).seen.map cfgStr
/- `visited 5, reported 2, |sem| 2, ok true, …` (4.1 and 4.2) -/
#eval summary (rep .least) ex41 1000 10
#eval summary (rep .least) ex42 1000 10

/-! ### Example 4.3 -/

/-- `T1: send(T1, 0); recv()`, `T2: send(T4, 1)`, `T3: send(T4, 2)`, `T4: recv()`,
`T5: send(T1, 42)`, left to right. -/
def ex43 : Program VPred := ofCodes [.done, sa 1 0 rb, sa 4 1, sa 4 2, rb, sa 1 42]

theorem ex43_sem : (semEnum AP ex43 10).length = 4 := by decide +kernel

/-- Each of the four terminal graphs is reported once. -/
theorem ex43_ok : okWith (rep .least) ex43 1000 10 = true ∧
    okWith (rep .byRecv) ex43 1000 10 = true := by decide +kernel

/-- Graph D of the paper: the revisit of `T1`'s receive by `send(T1, 42)`, keeping the events
added before the receive and the `porf`-prefix of the send: `S(T1,0); R <- S(T1,42); S(T1,42)`.
It is an intermediate configuration (not terminal: `T2`, `T3`, `T4` remain). -/
def ex43D : Graph VPred :=
  ((Graph.empty.addSend ⟨1, 0, .send .asyn 1 0⟩).addSend ⟨5, 0, .send .asyn 1 42⟩).addRecv
    ⟨1, 1, .recv ⟨.asyn, true⟩ .any⟩ (.snd ⟨5, 0, .send .asyn 1 42⟩)

/-- Graph D is visited exactly once, and it is not terminal. -/
theorem ex43_D : visitsOf (rep .least) ex43 1000 ex43D = 1 ∧
    (semEnum AP ex43 10).all (fun c => decide (c.G.key ≠ ex43D.key)) = true := by
  decide +kernel

/- `visited 14, reported 4, |sem| 4, ok true, missed 0, extra 0, dups 0, dead 0,
repeated visits 0, depth 9, events 6` -/
#eval summary (rep .least) ex43 1000 10

/-! ### `sem_printed_extra` (Section 3.3, `M0-opus.md` D8, `M0-astra.md` 15) -/

/-- `G'` is a full execution of `P` (Section 3.3): an execution after which every thread has
terminated. -/
def _root_.Must.Program.FullExec (P : Program VPred) (G : Graph VPred) : Prop :=
  P.Exec G ∧ ∀ t ∈ P.threads, P.step t (G.trace t) = none

/-- The printed `⟦P⟧`: consistent, and a full execution, or the restriction of a full
execution `G'` to its events such that adding any missing event of `G'` (with its source and
outcome in `G'`) is inconsistent. -/
def _root_.Must.Program.SemPrinted (P : Program VPred) (G : Graph VPred) : Prop :=
  AP G = true ∧ (P.FullExec G ∨ ∃ G', P.FullExec G' ∧ G = G'.restrict G.events ∧
    ∀ e ∈ G'.events \ G.events, AP (G.add e (G'.rf e) (G'.nd e)) = false)

/-- `T1: recv_b()`, `T2: send(T1, 1)`. -/
def pExtra : Program VPred := ofCodes [.done, rb, sa 1 1]

/-- The send. -/
abbrev sExtra : Ev VPred := ⟨2, 0, .send .asyn 1 1⟩
/-- The receive. -/
abbrev rExtra : Ev VPred := ⟨1, 0, .recv ⟨.asyn, true⟩ .any⟩

/-- `G = {s}`. -/
def gExtra : Graph VPred := Graph.empty.addSend sExtra
/-- `G' = {s, r ↦ ⊥}`: a full execution (not well-formed). -/
def gExtraFull : Graph VPred := gExtra.addRecv rExtra .bot

/-- `sem_printed_extra`: `{s}` is in the printed `⟦P⟧` (via `G' = {s, r ↦ ⊥}`), but not in
`⟦P⟧` of Q8: the receive is available. -/
theorem sem_printed_extra :
    pExtra.SemPrinted gExtra ∧ ¬ pExtra.Sem AP gExtra := by
  have hS : gExtra.Supp := Graph.Supp.add (fun _ _ => ⟨rfl, rfl⟩) _ _ _
  refine ⟨⟨by decide +kernel, Or.inr ⟨gExtraFull, ⟨by decide +kernel, by decide +kernel⟩, ?_,
    by decide +kernel⟩⟩, ?_⟩
  · have hS' : (gExtraFull.restrict gExtra.events).Supp :=
      (Graph.Supp.add hS _ _ _).restrict _
    exact (Graph.eq_iff_key hS hS').mpr (by decide +kernel)
  · rw [← pExtra.semD_iff AP hS]
    decide +kernel

/-! ### `revisit_printed_drops_send` (Q15; `PLAN-r1-astra.md`) -/

/-- `T0: send(T1, 0)`, `T1: recv()`, `T2: send(T1, 1)`. -/
def pLit : Program VPred := ofCodes [sa 1 0, rb, sa 1 1]

/-- The literal lines 11/13 (`s ∈ Deleted`, `SetRF(G|E \ Deleted, r, s)`). -/
abbrev litV : Variant VPred := { rep .least with literal := true }

/-- `revisit_printed_drops_send`: the literal lines 11/13 miss the graph `r ↦ s`; Q15 reports
both graphs. -/
theorem revisit_printed_drops_send :
    (compareR (explore AP litV pLit 100) (semEnum AP pLit 10) false).missed.map cfgStr =
      ["(0,0) S_asyn(T1,0); (2,0) S_asyn(T1,1); (1,0) Rb_asyn(*) <- (2,0)"] ∧
    okWith (rep .least) pLit 100 10 = true := by decide +kernel

/-! ### `oracle_missed`, `oracle_dup` (Q9; `M0-astra.md` 19, `M0-opus.md` D13) -/

/-- `T1: send(T3, 1)`, `T2: send(T3, 2)`, `T3: recv_b()`, `T4: send(T3, 3)`, `p2p`, schedule
`a, b, r, c`. -/
def pOrc : Program VPred := ofCodes [.done, sp 3 1, sp 3 2, rbp, sp 3 3]

/-- The current source as the oracle. -/
abbrev curV : Variant VPred := { rep .least with orc := oracleCur }
/-- The least consistent unread send of `H|Previous` (with `r` reading its source). -/
abbrev unreadV : Variant VPred := { rep .least with orc := oracleUnread AP }

/-- `oracle_dup`: with the current source as the oracle, the graph `r ↦ c` is reported twice
(from the branches `r ↦ a` and `r ↦ b`), and it is the only duplicate. -/
theorem oracle_dup :
    ((compareR (explore AP curV pOrc 100) (semEnum AP pOrc 10) false).dups.map
      (fun p => (cfgStr p.1, p.2))) =
      [("(1,0) S_p2p(T3,1); (2,0) S_p2p(T3,2); (3,0) Rb_p2p(*) <- (4,0); (4,0) S_p2p(T3,3)", 2)] ∧
    (compareR (explore AP curV pOrc 100) (semEnum AP pOrc 10) false).missed = [] := by
  decide +kernel

/-- `oracle_missed`: with the unread send of `H|Previous` as the oracle, both branches fail the
revisit condition and `r ↦ c` is missed. -/
theorem oracle_missed :
    ((compareR (explore AP unreadV pOrc 100) (semEnum AP pOrc 10) false).missed.map cfgStr) =
      ["(1,0) S_p2p(T3,1); (2,0) S_p2p(T3,2); (4,0) S_p2p(T3,3); (3,0) Rb_p2p(*) <- (4,0)"] := by
  decide +kernel

/-- With Q9's tie-break the three graphs are reported once each. -/
theorem oracle_q9 : okWith (rep .least) pOrc 100 10 = true ∧ (semEnum AP pOrc 10).length = 3 ∧
    okWith (rep .byRecv) pOrc 100 10 = true := by
  decide +kernel

/-! ### `try_recv_lost`, `cross_model_fruitless` (printed `next_P` (ii); Astra 16, D10) -/

/-- The printed scheduler. -/
abbrev pnextV : Variant VPred := { rep .least with next := fun P G => P.nextPrinted G }

/-- `T1: try_recv()` alone. -/
def pTry : Program VPred := ofCodes [.done, rnb]

/-- `try_recv_lost`: with the printed (ii) the receive is never added: `∅` is reported (not in
`⟦P⟧`), `{r ↦ ⊥}` is missed. With Q7 the explorer agrees with `⟦P⟧`. -/
theorem try_recv_lost :
    (compareR (explore AP pnextV pTry 100) (semEnum AP pTry 10) false).missed.map cfgStr =
      ["(1,0) Rnb_asyn(*) <- bot"] ∧
    (compareR (explore AP pnextV pTry 100) (semEnum AP pTry 10) false).extra.map cfgStr = [""] ∧
    okWith (rep .least) pTry 100 10 = true := by decide +kernel

/-- `T1: recv_b^p2p()`, `T2: send_asyn(T1, 1)`. -/
def pCross : Program VPred := ofCodes [.done, rbp, sa 1 1]

/-- `cross_model_fruitless`: with the printed (ii) the receive is added at `{s}` (a "message"
of another model), both branches are inconsistent: a configuration without successor, and
`{s}`, the only graph of `⟦P⟧`, is missed. With Q7: reported. -/
theorem cross_model_fruitless :
    (explore AP pnextV pCross 100).dead = 1 ∧
    (compareR (explore AP pnextV pCross 100) (semEnum AP pCross 10) false).missed.map cfgStr =
      ["(2,0) S_asyn(T1,1)"] ∧
    okWith (rep .least) pCross 100 10 = true := by decide +kernel

/-! ### `tid_tie` (A.3's `min_tid`; D14 (b)) -/

/-- `T1: send(T2, 1); send(T2, 2)`, `T2: recv_b()`. -/
def gTid : Graph VPred := (Graph.empty.addSend ⟨1, 0, .send .asyn 2 1⟩).addSend
  ⟨1, 1, .send .asyn 2 2⟩

/-- The receive. -/
abbrev rTid : Ev VPred := ⟨2, 0, .recv ⟨.asyn, true⟩ .any⟩

/-- `tid_tie`: two consistent sources with the same thread: `min_tid` is not a function; the
tie-breaks choose by identity `(tid, idx)`. -/
theorem tid_tie :
    (gTid.cands AP rTid).card = 2 ∧ (gTid.cands AP rTid).image Ev.tid = {1} ∧
    Sel.least.pick AP gTid rTid = some (1, 0) ∧ Sel.greatest.pick AP gTid rTid = some (1, 1) := by
  decide +kernel

/-! ### The fuel example (`PLAN-r3-astra.md`) -/

/-- `T0: a = send(T1, 0)`, `T1: r = recv(); c = send(T0, 0)`, `T2: b = send(T1, 1)`. -/
def pFuel : Program VPred := ofCodes [sa 1 0, rb (sa 0 0), sa 1 1]

/-- A path of five steps (`a; r ↦ a; c; revisit of r by b deleting c; c`), while every execution
has at most four events. -/
theorem fuel_path :
    (explore AP (rep .least) pFuel 100).maxDepth = 5 ∧
    (allExecs pFuel 10 [.init]).all (fun c => c.order.length ≤ 4) = true ∧
    okWith (rep .least) pFuel 100 10 = true := by decide +kernel

/-! ### The two counterexamples to p. 19 -/

/-! Opus (`PLAN-r1-opus.md`): `asyn`, order `T0 < T1 < T2 < T3`, least tie-break,
`T0: r = recv_nb()`, `T1: a = recv_b()`, `T2: d = send(T1, 1)`, `T3: k = send(T1, 2);
s = send(T0, 9)`. -/

def pOp : Program VPred := ofCodes [rnb, rb, sa 1 1, sa 1 2 (sa 0 9)]

abbrev oR : Ev VPred := ⟨0, 0, .recv ⟨.asyn, false⟩ .any⟩
abbrev oA : Ev VPred := ⟨1, 0, .recv ⟨.asyn, true⟩ .any⟩
abbrev oD : Ev VPred := ⟨2, 0, .send .asyn 1 1⟩
abbrev oK : Ev VPred := ⟨3, 0, .send .asyn 1 2⟩
abbrev oS : Ev VPred := ⟨3, 1, .send .asyn 0 9⟩

/-- `H₁ = r⊥, d, a ↦ d, k, s` (insertion order). -/
def oH1 : Config VPred :=
  ((((Config.init.add oR (some .bot) none).add oD none none).add oA (some (.snd oD)) none).add
    oK none none).add oS none none

/-- The configuration before `s` in `H₁`: `r⊥, d, a ↦ d, k`. -/
def oC1 : Config VPred :=
  (((Config.init.add oR (some .bot) none).add oD none none).add oA (some (.snd oD)) none).add
    oK none none

/-- The configuration before `s` in `H₂`: `r⊥, d, a ↦ k, k`. -/
def oC2 : Config VPred :=
  (((Config.init.add oR (some .bot) none).add oD none none).add oA (some (.snd oK)) none).add
    oK none none

/-- `H₂ = r⊥, d, a ↦ k, k, s`: the revisit of `a` by `k`, then `s`. -/
def oH2 : Config VPred :=
  ((((Config.init.add oR (some .bot) none).add oD none none).add oA (some (.snd oK)) none).add
    oK none none).add oS none none

/-- The guard of the revisit of `r` by `s` (`Deleted ∪ {r}` and `s`). -/
def guard (H : Config VPred) (r s : Ev VPred) : Bool :=
  let del := H.G.events.filter (fun d => d ≠ s ∧ H.pos r < H.pos d ∧ ¬ H.G.porf d s)
  decide (∀ d ∈ insert r del, revCond (oracleQ9 AP .least) H d s = true) &&
    revCond (oracleQ9 AP .least) H s s

/-- The kept graph `K` of the revisit of `r` by `s` from `H`, as a configuration. -/
def kept (H : Config VPred) (r s : Ev VPred) : Config VPred :=
  let del := H.G.events.filter (fun d => d ≠ s ∧ H.pos r < H.pos d ∧ ¬ H.G.porf d s)
  let K := H.G.events \ insert r (insert s del)
  ⟨H.G.restrict K, H.order.filter (fun d => decide (d ∈ K))⟩

/-- `p19_opus`: the revisit condition holds on `H₁` and fails on `H₂`; `H₁` and `H₂` have the
same kept graph `{k}`; the scheduler-following completion from `{k}` until `s` is `H₂` without
`s` (as an unordered graph), not `H₁` without `s`; the canonical replay of the supplied list
`r, d, a` from `{k}` is `H₁` without `s`. The final graph `{r ↦ s, k, s}` is reported once.
Both source configurations (before and after adding `s`) are visited; the revisit successor
`r ↦ s, k, s` is a successor of the configuration before `s` in `H₁`, not of the one in `H₂`;
the completion ends at the stop test. -/
theorem p19_opus :
    guard oH1 oR oS = true ∧ guard oH2 oR oS = false ∧
    (kept oH1 oR oS).G.key = (kept oH2 oR oS).G.key ∧
    (schedComplete AP .least pOp (fun e => decide (e = oS)) 10 (kept oH1 oR oS)).cfg.G.key =
      (oH2.G.remove {oS}).key ∧
    (schedComplete AP .least pOp (fun e => decide (e = oS)) 10 (kept oH1 oR oS)).cfg.G.key ≠
      (oH1.G.remove {oS}).key ∧
    ((replay AP .least pOp (kept oH1 oR oS) [oR, oD, oA]).map (fun c => c.G.key)) =
      some (oH1.G.remove {oS}).key ∧
    okWith (rep .least) pOp 1000 10 = true ∧
    (visited (rep .least) pOp 1000 oC1 ∧ visited (rep .least) pOp 1000 oH1 ∧
      visited (rep .least) pOp 1000 oC2 ∧ visited (rep .least) pOp 1000 oH2) = true ∧
    hasSucc (rep .least) pOp oC1 [oR, oK, oS] (oH1.G.revisit oR oS {oD, oA}) = true ∧
    hasSucc (rep .least) pOp oC2 [oR, oK, oS] (oH1.G.revisit oR oS {oD, oA}) = false ∧
    (schedComplete AP .least pOp (fun e => decide (e = oS)) 10 (kept oH1 oR oS)).isStopped :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/- The two configurations and the completion from `{k}` (in insertion order):
`H₁`: `(0,0) Rnb_asyn(*) <- bot; (2,0) S_asyn(T1,1); (1,0) Rb_asyn(*) <- (2,0); (3,0) S_asyn(T1,2);
(3,1) S_asyn(T0,9)`;
completion: `(3,0) S_asyn(T1,2); (0,0) Rnb_asyn(*) <- bot; (1,0) Rb_asyn(*) <- (3,0);
(2,0) S_asyn(T1,1)` (= `H₂` without `s` as an unordered graph). -/
#eval (cfgStr oH1, cfgStr (schedComplete AP .least pOp (fun e => decide (e = oS)) 10
  (kept oH1 oR oS)).cfg)

/-! Astra (`PLAN-r1-astra.md`): `asyn`, order `T0 < T1 < T2 < T3`, blocking receives,
`T0: a = send(T2, 0)`, `T1: q = recv()`, `T2: r = recv()`, `T3: k = send(T1, 0);
s = send(T2, 1)`. -/

def pAs : Program VPred := ofCodes [sa 2 0, rb, rb, sa 1 0 (sa 2 1)]

abbrev aA : Ev VPred := ⟨0, 0, .send .asyn 2 0⟩
abbrev aQ : Ev VPred := ⟨1, 0, .recv ⟨.asyn, true⟩ .any⟩
abbrev aR : Ev VPred := ⟨2, 0, .recv ⟨.asyn, true⟩ .any⟩
abbrev aK : Ev VPred := ⟨3, 0, .send .asyn 1 0⟩
abbrev aS : Ev VPred := ⟨3, 1, .send .asyn 2 1⟩

/-- `H = a; r ↦ a; k; q ↦ k; s`, the configuration of the explorer when `s` is added. -/
def aH : Config VPred :=
  ((((Config.init.add aA none none).add aR (some (.snd aA)) none).add aK none none).add aQ
    (some (.snd aK)) none).add aS none none

/-- The configuration before `s`: `a; r ↦ a; k; q ↦ k`. -/
def aC : Config VPred :=
  (((Config.init.add aA none none).add aR (some (.snd aA)) none).add aK none none).add aQ
    (some (.snd aK)) none

/-- `p19_astra`: the revisit of `r` by `s` passes its guard on `H` (`Deleted = {q}`, kept
`{a, k}`); the canonical replay of the supplied list `r, q` from `{a, k}` gives `a, k, r, q`;
the scheduler-following completion from `{a, k}` until `s` takes `q` before `r` (`a, k, q, r`):
the same unordered graph, a different insertion order. Explorer and `⟦P⟧` agree (2 graphs, 8
visits). The configurations before and after adding `s` are visited, and the revisit
successor `a; r ↦ s; k; s` is a successor of the first. -/
theorem p19_astra :
    guard aH aR aS = true ∧
    (kept aH aR aS).order = [aA, aK] ∧
    ((replay AP .least pAs (kept aH aR aS) [aR, aQ]).map (fun c => c.order)) =
      some [aA, aK, aR, aQ] ∧
    (schedComplete AP .least pAs (fun e => decide (e = aS)) 10 (kept aH aR aS)).cfg.order =
      [aA, aK, aQ, aR] ∧
    (schedComplete AP .least pAs (fun e => decide (e = aS)) 10 (kept aH aR aS)).cfg.G.key =
      (aH.G.remove {aS}).key ∧
    okWith (rep .least) pAs 1000 10 = true ∧ (semEnum AP pAs 10).length = 2 ∧
    (explore AP (rep .least) pAs 1000).visited = 8 ∧
    (visited (rep .least) pAs 1000 aC && visited (rep .least) pAs 1000 aH) = true ∧
    hasSucc (rep .least) pAs aC [aA, aR, aK, aS] (aH.G.revisit aR aS {aQ}) = true ∧
    (schedComplete AP .least pAs (fun e => decide (e = aS)) 10 (kept aH aR aS)).isStopped :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/-! ### Operational steps (`opSteps`, A.2) -/

/-- Every successor of the algorithm that adds one event at the end of the order and leaves the
sources and outcomes of the old events unchanged (every successor but a revisit) is an
operational step, on every configuration visited in
Examples 4.3 and p. 19 (Opus). -/
def plainSuccsAreOp (P : Program VPred) : Bool :=
  (explore AP (rep .least) P 1000).seen.all fun c =>
    ((stepM AP (rep .least) P c).getD []).all fun d =>
      !(decide (d.order.length = c.order.length + 1 ∧ d.order.take c.order.length = c.order ∧
        (d.G.restrict c.G.events).key = c.G.key)) ||
      (opSteps AP P c).any (fun o => decide (o.order = d.order ∧ o.G.key = d.G.key))

theorem plain_succs_op : plainSuccsAreOp ex43 = true ∧ plainSuccsAreOp pOp = true := by
  decide +kernel

/-- At `∅` of `A + B + C` the operational steps are the two sends (the receive has no
source). -/
theorem opSteps_abc : (opSteps AP abc Config.init).map cfgStr =
    ["(1,0) S_asyn(T3,1)", "(2,0) S_asyn(T3,2)"] := by decide +kernel

end Examples

end Must

/-! ### Axioms -/

#print axioms Must.Graph.wfD_iff
#print axioms Must.Graph.consAPB_iff
#print axioms Must.Sel.pick_spec
#print axioms Must.Sel.pick_isSome
#print axioms Must.Graph.Wf.retAt_eq
#print axioms Must.Examples.ex31_ok
#print axioms Must.Examples.ex32_lts
#print axioms Must.Examples.ex43_ok
#print axioms Must.Examples.sem_printed_extra
#print axioms Must.Examples.revisit_printed_drops_send
#print axioms Must.Examples.oracle_dup
#print axioms Must.Examples.oracle_missed
#print axioms Must.Examples.try_recv_lost
#print axioms Must.Examples.cross_model_fruitless
#print axioms Must.Examples.tid_tie
#print axioms Must.Examples.fuel_path
#print axioms Must.Examples.p19_opus
#print axioms Must.Examples.p19_astra
#print axioms Must.Examples.ex43_D
#print axioms Must.Examples.plain_succs_op
#print axioms Must.Sel.pick_congr
#print axioms Must.minVal_eq_head
