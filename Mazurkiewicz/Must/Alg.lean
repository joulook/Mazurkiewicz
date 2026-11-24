import Mazurkiewicz.Must.Model
import Mazurkiewicz.Must.ExploreC

/-!
# Algorithm 1 as a relation over a model (milestone M4)

Paper: Section 4, Algorithm 1; Appendix A.2 (operational steps), A.4 (algorithmic steps),
Definitions A.4, A.7. Plan: `plan/must/lean/LEAN-PLAN.md`, decisions Q7, Q9, Q12, Q13, Q15,
Section 2b (`RevisitCondition`), the addendum (consistency check of the revisit successor; the
insertion order does not contain `rf` after a revisit).

Every definition is over a model `M : Model Q` (M3), a program `P` and, for the revisit, a
tie-break `tie : Tie Q` (Q9; only its value is used, its properties are the predicate `TieQ9`).
A program that uses several communication models is explored under `Model.comb` (Definition 3.8
with Q4); `Model.p2p` applies no condition to `cd` and `mbox` events.

* `Model.nextP`, `Model.FullM`, `Model.Sem`: `next_P` (the head of `Model.availM`, Q7), `full`
  (Definition A.7), `⟦P⟧` (Q8), for the model.
* `Config.Inv M P c`: the configuration invariant: the insertion order is duplicate-free, lists
  exactly the events of the graph and contains `po` (as `Pairwise (¬ po⁻¹)`); the graph is
  well-formed, an execution of `P`, and `M`-consistent. It does not say that a source precedes
  its reader: after a revisit the revisited receive precedes its new source.
* `RevCond tie H e s`: `RevisitCondition(H, e, s)` (Section 2b; line 22 with Q9:
  `tie((H|Previous) \ {e}, e)`).
* `Config.del H r s` (Q15: `Deleted`), `Config.revisitCfg H r s` (Q15: the successor, order
  `Restrict(<_H, K ∪ {r}) ++ [s]`), `RevGuard tie H r s` (the guards of Q15).
* `NrAdd M P G e src out`: a non-revisit step of Algorithm 1 adds `e = next_P(G)` with source
  `src` and outcome `out` (lines 6, 7, 9, 14, Q12); `StepM`: a non-revisit step or a revisit
  (lines 10–13 with Q15, including the consistency check of line 13); `ReachM`: reachability
  from the empty configuration.
* `OpAdd`, `OpStep`, `OpStepG` (A.2 with Q7): an available event with an admissible source or
  outcome and a consistent result. The receive rule of A.2 has no consistency premise; here
  every operational step has one (it is implied by Q11 except for a receive reading a send).
-/

namespace Must

open Graph

variable {Q : Type} [DecidableEq Q] [Membership Val Q]

/-! ### Scheduler and `⟦P⟧` of a model -/

namespace Model

variable (M : Model Q) (P : Program Q)

/-- `next_P G` (Q7): the first available event in thread order, `none` (`⊥`) iff none. -/
noncomputable def nextP (G : Graph Q) : Option (Ev Q) := (M.availM P G).head?

/-- `full(G)` (Definition A.7): no available event. -/
def FullM (G : Graph Q) : Prop := M.availM P G = []

/-- `⟦P⟧` for the model (Q8): well-formed consistent executions of `P` with no available
event. -/
def Sem (G : Graph Q) : Prop := G.Wf ∧ P.Exec G ∧ M.cons G ∧ M.FullM P G

variable {M P}

theorem nextP_eq_none_iff {G : Graph Q} : M.nextP P G = none ↔ M.FullM P G :=
  List.head?_eq_none_iff

theorem mem_availM_of_nextP {G : Graph Q} {e : Ev Q} (h : M.nextP P G = some e) :
    e ∈ M.availM P G := by
  unfold nextP at h
  exact List.mem_of_mem_head? h

/-- M2's scheduler for a Boolean test that agrees with `cons` on graphs with `Supp` is the
model's, on graphs with `Supp`. -/
theorem nextP_eq (cons : Graph Q → Bool)
    (hc : ∀ H : Graph Q, H.Supp → (cons H = true ↔ M.cons H)) (P : Program Q) {G : Graph Q}
    (hS : G.Supp) : P.nextP cons G = M.nextP P G := by
  unfold Program.nextP nextP
  rw [M.availM_eq cons hc P hS]

/-- M2's `⟦P⟧` for a Boolean test that agrees with `cons` on graphs with `Supp` is the
model's, on graphs with `Supp`. -/
theorem sem_iff (cons : Graph Q → Bool)
    (hc : ∀ H : Graph Q, H.Supp → (cons H = true ↔ M.cons H)) (P : Program Q) {G : Graph Q}
    (hS : G.Supp) : P.Sem cons G ↔ M.Sem P G := by
  unfold Program.Sem Sem Program.FullM FullM
  rw [M.availM_eq cons hc P hS, hc G hS]

end Model

/-! ### The configuration invariant -/

/-- The configuration invariant (plan row M4). -/
structure Config.Inv (M : Model Q) (P : Program Q) (c : Config Q) : Prop where
  /-- no event is inserted twice -/
  nodup : c.order.Nodup
  /-- the insertion order lists exactly the events of the graph -/
  mem : ∀ e, e ∈ c.order ↔ e ∈ c.G.events
  /-- the insertion order contains `po` -/
  po : c.order.Pairwise (fun a b => ¬ c.G.po b a)
  /-- the graph is well-formed -/
  wf : c.G.Wf
  /-- the graph is an execution of `P` -/
  exec : P.Exec c.G
  /-- the graph is consistent -/
  cons : M.cons c.G

/-! ### Tie-breaks and the revisit condition -/

/-- A tie-break (Q9): `tie(X, e)`, the identity `(tid, idx)` of a source of the receive `e` in
the graph `X`, or `none`. -/
abbrev Tie (Q : Type) := Graph Q → Ev Q → Option (Tid × ℕ)

/-- Q9 for a model, on graphs with `Supp`: the tie-break returns a consistent source, and
returns one whenever one exists. Equality on equal unordered graphs: `tie` is a function of the
graph, so it is equal on graphs equal as Lean values; on graphs with `Supp` this is equality as
unordered graphs (`Graph.eq_iff_key`), and every graph `tie` is applied to by `RevCond` has `Supp`
when `H.G` has (restrictions and removals of graphs with `Supp` have `Supp`). -/
def TieQ9 (M : Model Q) (tie : Tie Q) : Prop :=
  (∀ X e id, X.Supp → tie X e = some id →
    ∃ s ∈ X.S, M.cons (X.addRecv e (.snd s)) ∧ (s.tid, s.idx) = id) ∧
  (∀ X e, X.Supp → (∃ s ∈ X.S, M.cons (X.addRecv e (.snd s))) → (tie X e).isSome)

/-- `RevisitCondition(H, e, s)` (Section 2b), with `Previous = H.prev e s` and line 22 read with
Q9 as `tie((H|Previous) \ {e}, e)`. -/
def RevCond (tie : Tie Q) (H : Config Q) (e s : Ev Q) : Prop :=
  if e.IsRecvNB then H.G.rf e = some .bot
  else if e.IsND then H.G.nd e = minVal e.ndSet
  else if e.IsRecvB then
    ∃ s', H.G.rf e = some (.snd s') ∧
      tie ((H.G.restrict (H.prev e s)).remove {e}) e = some (s'.tid, s'.idx)
  else ∀ q ∈ H.prev e s, q.IsRecv → H.G.rf q ≠ some (.snd e)

namespace Config

/-- `Deleted` of Q15: the events inserted after `r`, other than `s`, that are not causally
before `s`. -/
def del (H : Config Q) (r s : Ev Q) : Finset (Ev Q) :=
  H.G.events.filter (fun d => d ≠ s ∧ H.pos r < H.pos d ∧ ¬ H.G.porf d s)

/-- The revisit successor of Q15: `r` reads `s`, `Deleted` is removed, the order is the old
order restricted to the kept events and `r`, followed by `s`. -/
def revisitCfg (H : Config Q) (r s : Ev Q) : Config Q :=
  ⟨H.G.revisit r s (H.del r s), H.order.filter (fun d => decide (d ∉ H.del r s ∧ d ≠ s)) ++ [s]⟩

end Config

/-- The guards of the revisit of `r` by the send `s` (Q15), all evaluated on `H`. -/
structure RevGuard (tie : Tie Q) (H : Config Q) (r s : Ev Q) : Prop where
  /-- `r` is an event of `H` -/
  mem : r ∈ H.G.events
  /-- `r` is a receive -/
  recv : r.IsRecv
  /-- `s` matches `r`: destination, value, model -/
  smatch : s.Matches r
  /-- `r` is not causally before `s` -/
  nporf : ¬ H.G.porf r s
  /-- `RevisitCondition(H, e', s)` for `e' ∈ Deleted ∪ {r}` -/
  cond : ∀ d ∈ insert r (H.del r s), RevCond tie H d s
  /-- `RevisitCondition(H, s, s)` -/
  cond_s : RevCond tie H s s

/-! ### Steps -/

/-- A non-revisit step of Algorithm 1 adds `e = next_P(G)` with `src`, `out`: an ND event with
every outcome of its set (line 6); a receive with a send of the graph or `⊥`, if consistent
(line 7); a send, if consistent (line 9); block or error as they are (line 14, Q12). -/
def NrAdd (M : Model Q) (P : Program Q) (G : Graph Q) (e : Ev Q) (src : Option (Src Q))
    (out : Option Val) : Prop :=
  M.nextP P G = some e ∧
    ((∃ S v, e.lab = .nd S ∧ v ∈ S ∧ src = none ∧ out = some v) ∨
     (e.IsRecv ∧ out = none ∧ (src = some .bot ∨ ∃ s ∈ G.S, src = some (.snd s)) ∧
        M.cons (G.add e src out)) ∨
     (e.IsSend ∧ src = none ∧ out = none ∧ M.cons (G.add e src out)) ∨
     (e.IsLoc ∧ src = none ∧ out = none))

/-- The algorithmic step (Algorithm 1 with Q7, Q9, Q12, Q15): a non-revisit step, or the revisit
of a receive `r` by the send `e = next_P` just added (lines 10–13), visited if consistent. -/
inductive StepM (M : Model Q) (tie : Tie Q) (P : Program Q) : Config Q → Config Q → Prop
  /-- a non-revisit step -/
  | nr {c : Config Q} {e : Ev Q} {src : Option (Src Q)} {out : Option Val} :
      NrAdd M P c.G e src out → StepM M tie P c (c.add e src out)
  /-- a revisit -/
  | revisit {c : Config Q} {e r : Ev Q} :
      M.nextP P c.G = some e → e.IsSend → RevGuard tie (c.add e none none) r e →
      M.cons ((c.add e none none).revisitCfg r e).G →
      StepM M tie P c ((c.add e none none).revisitCfg r e)

/-- Reachability by algorithmic steps from the empty configuration. -/
def ReachM (M : Model Q) (tie : Tie Q) (P : Program Q) (c : Config Q) : Prop :=
  Relation.ReflTransGen (StepM M tie P) Config.init c

/-- An admissible source and outcome for `e` (A.2): a receive with a send of the graph or `⊥`,
an ND event with an outcome of its set, the other events with none. -/
def Adm (G : Graph Q) (e : Ev Q) (src : Option (Src Q)) (out : Option Val) : Prop :=
  (e.IsRecv ∧ out = none ∧ (src = some .bot ∨ ∃ s ∈ G.S, src = some (.snd s))) ∨
  (e.IsND ∧ src = none ∧ ∃ v ∈ e.ndSet, out = some v) ∨
  (¬ e.IsRecv ∧ ¬ e.IsND ∧ src = none ∧ out = none)

/-- An operational step (A.2 with Q7) adds an available event with an admissible source and
outcome; the result is consistent. The consistency premise is a strengthening of the printed A.2
(p. 29: the Receive rule has no consistency premise). It is acceptable for paths to a consistent
endpoint because every intermediate graph of such a path is a `porf`-closed restriction of the
endpoint, hence consistent by prefix-closedness; that statement (`OpLe₀` to a consistent
endpoint gives `OpLe`) is an M5 obligation, not proved here, so A.10/A.11 must not be read off
this definition. The unpremised relation is `OpAdd₀`. -/
def OpAdd (M : Model Q) (P : Program Q) (G : Graph Q) (e : Ev Q) (src : Option (Src Q))
    (out : Option Val) : Prop :=
  e ∈ M.availM P G ∧ Adm G e src out ∧ M.cons (G.add e src out)

/-- The printed operational step (A.2 with Q7), without a consistency premise. -/
def OpAdd₀ (M : Model Q) (P : Program Q) (G : Graph Q) (e : Ev Q) (src : Option (Src Q))
    (out : Option Val) : Prop :=
  e ∈ M.availM P G ∧ Adm G e src out

/-- The printed operational step on graphs. -/
def OpStepG₀ (M : Model Q) (P : Program Q) (G G' : Graph Q) : Prop :=
  ∃ e src out, OpAdd₀ M P G e src out ∧ G' = G.add e src out

/-- An operational step on configurations (the event is appended to the order). -/
def OpStep (M : Model Q) (P : Program Q) (c c' : Config Q) : Prop :=
  ∃ e src out, OpAdd M P c.G e src out ∧ c' = c.add e src out

/-- An operational step on graphs. -/
def OpStepG (M : Model Q) (P : Program Q) (G G' : Graph Q) : Prop :=
  ∃ e src out, OpAdd M P G e src out ∧ G' = G.add e src out

/-- A non-revisit step on graphs. -/
def NrStepG (M : Model Q) (P : Program Q) (G G' : Graph Q) : Prop :=
  ∃ e src out, NrAdd M P G e src out ∧ G' = G.add e src out

end Must

#print axioms Must.Model.nextP_eq_none_iff
#print axioms Must.Model.mem_availM_of_nextP
#print axioms Must.Model.nextP_eq
#print axioms Must.Model.sem_iff
