import Mazurkiewicz.Must.Exec

/-!
# Algorithm 1 as a successor function, and its explorer

Paper: Algorithm 1 (lines 1–22), Section 4. Plan: decisions Q7, Q9, Q12, Q15, Section 2b
(`RevisitCondition`, explorer's fuel contract), Section 3 rows "Algorithm 1", "printed line
11/13", "printed oracle contract", "printed `next_P` (ii)".

* `Oracle`: the function of line 22 on `H|Previous` and the receive. `oracleQ9 T` is Q9's
  `tie((H|Previous) \ {e}, e)`; `oracleCur` (the current source) and `oracleUnread` (the least
  consistent unread send of `H|Previous`, in which `e` still reads its source) violate Q9.
* `Config.prev H e s`: `Previous = {e' | e' ≤_H e ∨ (e', s) ∈ H.porf}`. `revCond`:
  `RevisitCondition(H, e, s)` of Section 2b (line 21: `∀ q ∈ Previous ∩ R. rf q ≠ e`).
* `Variant`: the scheduler (`Program.nextP`, or the printed condition (ii) `nextPrinted`), the
  oracle, and `literal` (printed lines 11/13: `s ∈ Deleted`, `SetRF(G|E \ Deleted, r, s)`).
* `revisitsOf`, `stepM`: all successors of a configuration (Q15 for the revisit; error and
  block are ordinary events, Q12); `none` when `next_P` is `⊥`. A revisit successor is kept
  only if it is consistent (line 13, `VisitIfConsistent`, listed in Q15's addendum: for
  `asyn` it is implied by the guard, for `p2p` it filters).
* `explore`: depth-first search with a separate fuel, decremented at every visited
  configuration; it returns the reported configurations with multiplicity, the visited
  configurations in visiting order (`seen`), the number of configurations with `next_P ≠ ⊥`
  and no successor (`dead`), the greatest depth and number of events, and whether the fuel was
  exhausted.
-/

namespace Must

variable {Q : Type} [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)]

/-- An oracle for line 22, on `H|Previous` and the receive. -/
abbrev Oracle (Q : Type) := Graph Q → Ev Q → Option (Tid × ℕ)

/-- Q9: `tie((H|Previous) \ {e}, e)`. -/
def oracleQ9 (cons : Graph Q → Bool) (T : Sel Q) : Oracle Q :=
  fun Y e => T.pick cons (Y.remove {e}) e

/-- The current source of `e` (violates Q9). -/
def oracleCur : Oracle Q := fun Y e =>
  match Y.rf e with
  | some (.snd s) => some (s.tid, s.idx)
  | _ => none

/-- The least consistent unread send of `H|Previous`, computed with `e` still reading its source
(violates Q9: the current source counts as read). -/
def oracleUnread (cons : Graph Q → Bool) : Oracle Q := fun Y e =>
  (Sel.least.sel Y e ((Y.US.filter (fun s => cons (Y.setRF e (.snd s)) = true)).image Ev.idL)).map
    ofLex

/-- The printed condition (ii) on `next_P`: a receive is added only if an unread send to its
thread with a matching value (of any model) exists. -/
def Program.UsablePrinted (G : Graph Q) (e : Ev Q) : Prop :=
  ¬ e.IsRecv ∨ ∃ s ∈ G.US, Graph.dstOf s.lab = some e.tid ∧ s.ValMatches e

instance (G : Graph Q) (e : Ev Q) : Decidable (Program.UsablePrinted G e) := by
  unfold Program.UsablePrinted
  infer_instance

/-- `next_P` with the printed condition (ii). -/
def Program.nextPrinted (P : Program Q) (G : Graph Q) : Option (Ev Q) :=
  (P.threads.filterMap fun t =>
    (P.nextEv G t).filter (fun e => decide (Program.UsablePrinted G e))).head?

/-- A variant of the algorithm. -/
structure Variant (Q : Type) where
  /-- the scheduler -/
  next : Program Q → Graph Q → Option (Ev Q)
  /-- the oracle of line 22 -/
  orc : Oracle Q
  /-- printed lines 11/13 -/
  literal : Bool := false

/-- The repaired algorithm: `next_P` of Q7, `tie` of Q9, revisit of Q15. -/
def Variant.repaired (cons : Graph Q → Bool) (T : Sel Q) : Variant Q :=
  ⟨fun P G => P.nextP cons G, oracleQ9 cons T, false⟩

namespace Config

/-- `Previous` of `e` for the revisiting send `s`. -/
def prev (H : Config Q) (e s : Ev Q) : Finset (Ev Q) :=
  H.G.events.filter (fun d => H.pos d ≤ H.pos e ∨ H.G.porf d s)

end Config

/-- `RevisitCondition(H, e, s)` (Section 2b). -/
def revCond (orc : Oracle Q) (H : Config Q) (e s : Ev Q) : Bool :=
  if e.IsRecvNB then decide (H.G.rf e = some .bot)
  else if e.IsND then decide (H.G.nd e = minVal e.ndSet)
  else if e.IsRecvB then
    match orc (H.G.restrict (H.prev e s)) e with
    | some id => decide (∃ s' ∈ Graph.srcOf (H.G.rf e), (s'.tid, s'.idx) = id)
    | none => false
  else decide (∀ q ∈ H.prev e s, q.IsRecv → H.G.rf q ≠ some (.snd e))

/-- The revisits by the send `s`, the last event of `H` (Q15; `literal`: printed lines 11/13). -/
def revisitsOf (cons : Graph Q → Bool) (V : Variant Q) (H : Config Q) (s : Ev Q) :
    List (Config Q) :=
  (H.order.filter (fun r => decide (r.IsRecv ∧ s.Matches r ∧ ¬ H.G.porf r s))).filterMap fun r =>
    let del := H.G.events.filter (fun d => d ≠ s ∧ H.pos r < H.pos d ∧ ¬ H.G.porf d s)
    if decide (∀ d ∈ insert r del, revCond V.orc H d s = true) && revCond V.orc H s s
    then
      let c' : Config Q := if V.literal then
          ⟨(H.G.restrict (H.G.events \ insert s del)).setRF r (.snd s),
            H.order.filter (fun d => decide (d ∉ insert s del))⟩
        else ⟨H.G.revisit r s del, H.order.filter (fun d => decide (d ∉ del ∧ d ≠ s)) ++ [s]⟩
      if cons c'.G then some c' else none
    else none

/-- All successors of `c` (Algorithm 1); `none` iff `next_P` is `⊥` (line 4). -/
def stepM (cons : Graph Q → Bool) (V : Variant Q) (P : Program Q) (c : Config Q) :
    Option (List (Config Q)) :=
  match V.next P c.G with
  | none => none
  | some e => some <|
    match e.lab with
    | .nd S => (ndList S).map (fun v => c.add e none (some v))
    | .recv _ _ =>
      (((c.order.filter (fun d : Ev Q => decide d.IsSend)).map Src.snd) ++ [Src.bot]).filterMap
        fun x =>
        let c' := c.add e (some x) none
        if cons c'.G then some c' else none
    | .send _ _ _ =>
      let H := c.add e none none
      (if cons H.G then [H] else []) ++ revisitsOf cons V H e
    | _ => [c.add e none none]

/-- The result of an exploration. -/
structure Result (Q : Type) where
  /-- remaining fuel -/
  fuel : ℕ
  /-- the reported configurations, with multiplicity -/
  reported : List (Config Q) := []
  /-- visited configurations -/
  visited : ℕ := 0
  /-- configurations with `next_P ≠ ⊥` and no successor -/
  dead : ℕ := 0
  /-- greatest depth -/
  maxDepth : ℕ := 0
  /-- greatest number of events -/
  maxEvents : ℕ := 0
  /-- fuel exhausted -/
  exhausted : Bool := false
  /-- the visited configurations, in visiting order -/
  seen : List (Config Q) := []

/-- `Visit`, depth-first; the first argument bounds the depth, `fuel` the number of visits. -/
def dfs (cons : Graph Q → Bool) (V : Variant Q) (P : Program Q) :
    ℕ → ℕ → Config Q → Result Q → Result Q
  | 0, _, _, r => { r with exhausted := true }
  | n + 1, d, c, r =>
    if r.fuel = 0 then { r with exhausted := true } else
    let r : Result Q := { r with
      fuel := r.fuel - 1
      visited := r.visited + 1
      maxDepth := max r.maxDepth d
      maxEvents := max r.maxEvents c.order.length
      seen := r.seen ++ [c] }
    match stepM cons V P c with
    | none => { r with reported := r.reported ++ [c] }
    | some [] => { r with dead := r.dead + 1 }
    | some l => l.foldl (fun r c' => dfs cons V P n (d + 1) c' r) r

/-- The explorer from the empty configuration with `fuel` visits. -/
def explore (cons : Graph Q → Bool) (V : Variant Q) (P : Program Q) (fuel : ℕ) : Result Q :=
  dfs cons V P fuel 0 .init { fuel := fuel }

end Must
