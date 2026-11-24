import Mazurkiewicz.Must.Program
import Mazurkiewicz.Must.Cons
import Mathlib.Data.Prod.Lex

/-!
# Availability, `⟦P⟧`, configurations, tie-breaks, the two replays

Paper: Section 3.3 (`⟦P⟧`), Section 4 (`next_P`, insertion order, `GetConsTiebreaker`),
A.3/A.5 (`MaxCompletion`). Plan: decisions Q7, Q8, Q9, Q10, Section 2b.

Throughout, `cons : Graph Q → Bool` is the consistency test (for `asyn`, `p2p`:
`Graph.consAPB`).

* `Usable cons G e`: `e` is not a blocking receive, or it has a consistent source
  (`∃ s ∈ G.S, cons (G.addRecv e (.snd s))`). `availM cons P G`: the next events of the threads
  (in thread order) that are usable (Q7); non-blocking receives are always available.
  `nextP`: the first of them (the least in thread order; `none` iff `availM = []`). `FullM`.
* `Sem cons P G` (Q8): well-formed, an execution of `P`, consistent, `availM = []`; and its
  decision procedure `SemD` (with `WfD`; equal on graphs with `Supp`).
* `Config`: a graph and its insertion order, a list of its events. `Config.add`: an
  operational step adds the next event of a thread with its source and outcome at the end of the
  order; `opSteps`: all operational steps (A.2) from a configuration.
* `Sel`, `Tie` (Q9): a tie-break chooses among the identities `(tid, idx)` (Q1) of the
  consistent sources of `e` in a graph `X`; it is a function of `X` and `e`, so it is equal on
  equal (unordered) graphs; it may depend on the receive; its choice is a consistent source
  whenever one exists, and only then (`Sel.pick_spec`, `Sel.pick_isSome`). The four tie-breaks
  of the search: `Sel.least`, `Sel.greatest`, `Sel.parity` (least if `X` has an even number of
  events, else greatest), `Sel.byRecv` (least if `tid + idx` of the receive is even, else
  greatest).
* `canonAdd` (Q10 (i), A.3): add an event with its canonical outcome: blocking receive ↦ the
  tie-break's source, non-blocking receive ↦ `⊥`, ND ↦ `min S`, others ↦ themselves; `none` if
  the event is not the next event of its thread in `P` or a blocking receive has no consistent
  source. `replay`: canonical replay of a supplied list (`MaxCompletion(G, A)`).
* `schedComplete` (Q10 (ii)): add `next_P` with its canonical outcome until `next_P` is `⊥` or
  satisfies a stop test; the result (`Completion`) distinguishes these two ends from fuel
  exhaustion and from a failed canonical addition. The two replays are different
  (`Examples.lean`, the p. 19 witnesses).
-/

namespace Must

variable {Q : Type} [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)]

/-- The elements of a finite set of values in increasing order (structural, so that the kernel
evaluates it). -/
def ndList (S : Finset Val) : List Val := (List.range (S.sup id + 1)).filter (· ∈ S)

theorem mem_ndList {S : Finset Val} {v : Val} : v ∈ ndList S ↔ v ∈ S := by
  unfold ndList
  rw [List.mem_filter, List.mem_range, decide_eq_true_iff]
  exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_of_le (Finset.le_sup (f := id) h), h⟩⟩

/-! ### Availability and `⟦P⟧` -/

namespace Program

variable (cons : Graph Q → Bool) (P : Program Q)

/-- The next event `e` can be added (Q7): it is not a blocking receive, or it has a consistent
source. -/
def Usable (G : Graph Q) (e : Ev Q) : Prop :=
  ¬ e.IsRecvB ∨ ∃ s ∈ G.S, cons (G.addRecv e (.snd s)) = true

instance (G : Graph Q) (e : Ev Q) : Decidable (Usable cons G e) := by
  unfold Usable
  infer_instance

/-- `availM G`: the usable next events, in thread order (Q7). -/
def availM (G : Graph Q) : List (Ev Q) :=
  P.threads.filterMap fun t => (P.nextEv G t).filter (fun e => decide (Usable cons G e))

/-- `next_P G`: the first available event in thread order; `none` (`⊥`) iff none is available. -/
def nextP (G : Graph Q) : Option (Ev Q) := (P.availM cons G).head?

/-- `G` is full: no event is available. -/
def FullM (G : Graph Q) : Prop := P.availM cons G = []

instance (G : Graph Q) : Decidable (P.FullM cons G) := by
  unfold FullM
  infer_instance

/-- `⟦P⟧` (Q8): well-formed consistent executions of `P` with `availM = ∅`. -/
def Sem (G : Graph Q) : Prop := G.Wf ∧ P.Exec G ∧ cons G = true ∧ P.FullM cons G

/-- `⟦P⟧`, with the decidable form of well-formedness. -/
def SemD (G : Graph Q) : Prop := G.WfD ∧ P.Exec G ∧ cons G = true ∧ P.FullM cons G

instance (G : Graph Q) : Decidable (P.SemD cons G) := by
  unfold SemD
  infer_instance

omit [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
theorem semD_iff {G : Graph Q} (hS : G.Supp) : P.SemD cons G ↔ P.Sem cons G := by
  unfold SemD Sem
  rw [Graph.wfD_iff hS]

omit [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
theorem nextP_eq_none_iff {G : Graph Q} : P.nextP cons G = none ↔ P.FullM cons G := by
  unfold nextP FullM
  exact List.head?_eq_none_iff

end Program

/-! ### Configurations -/

/-- A configuration: a graph and its insertion order. -/
structure Config (Q : Type) where
  /-- the graph -/
  G : Graph Q
  /-- the insertion order: the events of `G` in the order they were added -/
  order : List (Ev Q)

namespace Config

/-- The initial configuration. -/
def init : Config Q := ⟨.empty, []⟩

/-- Add `e` with source `src` and outcome `out` at the end of the insertion order. -/
def add (c : Config Q) (e : Ev Q) (src : Option (Src Q)) (out : Option Val) : Config Q :=
  ⟨c.G.add e src out, c.order ++ [e]⟩

/-- The position of `e` in the insertion order. -/
def pos (c : Config Q) (e : Ev Q) : ℕ := c.order.idxOf e

/-- The event with identity `(t, i)` in the insertion order. -/
def byId (c : Config Q) (id : Tid × ℕ) : Option (Ev Q) :=
  c.order.find? (fun e => e.tid = id.1 ∧ e.idx = id.2)

/-- Two configurations are the same up to the insertion order (`≈`): equal keys. -/
def Approx (c c' : Config Q) : Prop := c.G.key = c'.G.key

instance (c c' : Config Q) : Decidable (Approx c c') := by
  unfold Approx
  infer_instance

end Config

/-! ### Operational steps (A.2) -/

/-- The operational steps from `c` (A.2 with Q7): an available event, a receive with every send
that keeps the graph consistent and with `⊥` (non-blocking only, by consistency), an ND event
with every outcome of its set, the other events as they are. -/
def opSteps (cons : Graph Q → Bool) (P : Program Q) (c : Config Q) : List (Config Q) :=
  (P.availM cons c.G).flatMap fun e =>
    match e.lab with
    | .recv _ _ =>
      (((c.order.filter (fun d : Ev Q => decide d.IsSend)).map Src.snd) ++ [Src.bot]).filterMap
        fun x =>
          let c' := c.add e (some x) none
          if cons c'.G then some c' else none
    | .nd S => (ndList S).map (fun v => c.add e none (some v))
    | _ => [c.add e none none]

/-! ### Tie-breaks (Q9) -/

/-- The identity of an event, in the lexicographic order. -/
def Ev.idL (e : Ev Q) : Lex (ℕ × ℕ) := toLex (e.tid, e.idx)

/-- The consistent sources of the receive `e` in `X`. -/
def Graph.cands (cons : Graph Q → Bool) (X : Graph Q) (e : Ev Q) : Finset (Ev Q) :=
  X.S.filter (fun s => cons (X.addRecv e (.snd s)) = true)

/-- A selection among the identities of the candidates, depending on the context graph and on
the receive (Q9 allows both): a candidate whenever there is one. -/
structure Sel (Q : Type) where
  /-- the selection -/
  sel : Graph Q → Ev Q → Finset (Lex (ℕ × ℕ)) → Option (Lex (ℕ × ℕ))
  /-- it selects an element -/
  mem : ∀ X e I x, sel X e I = some x → x ∈ I
  /-- it selects something from a non-empty set -/
  isSome : ∀ X e I, I.Nonempty → (sel X e I).isSome

namespace Sel

/-- `WithTop α` as an option. -/
def ofTop {α : Type} (x : WithTop α) : Option α := x

/-- `WithBot α` as an option. -/
def ofBot {α : Type} (x : WithBot α) : Option α := x

/-- The least identity. -/
def least : Sel Q where
  sel := fun _ _ I => ofTop I.min
  mem := fun _ _ I x h => by
    cases hm : I.min with
    | top => simp [ofTop, hm] at h
    | coe y =>
      have : ofTop I.min = some y := by rw [hm]; rfl
      rw [this, Option.some.injEq] at h
      subst h
      exact Finset.mem_of_min hm
  isSome := fun _ _ I hI => by
    obtain ⟨y, hy⟩ := Finset.min_of_nonempty hI
    have : ofTop I.min = some y := by rw [hy]; rfl
    rw [this]
    rfl

/-- The greatest identity. -/
def greatest : Sel Q where
  sel := fun _ _ I => ofBot I.max
  mem := fun _ _ I x h => by
    cases hm : I.max with
    | bot => simp [ofBot, hm] at h
    | coe y =>
      have : ofBot I.max = some y := by rw [hm]; rfl
      rw [this, Option.some.injEq] at h
      subst h
      exact Finset.mem_of_max hm
  isSome := fun _ _ I hI => by
    obtain ⟨y, hy⟩ := Finset.max_of_nonempty hI
    have : ofBot I.max = some y := by rw [hy]; rfl
    rw [this]
    rfl

/-- Choose between two selections by a test on the context and the receive. -/
def ite (p : Graph Q → Ev Q → Bool) (A B : Sel Q) : Sel Q where
  sel := fun X e I => if p X e then A.sel X e I else B.sel X e I
  mem := fun X e I x h => by
    split_ifs at h
    · exact A.mem X e I x h
    · exact B.mem X e I x h
  isSome := fun X e I hI => by
    split_ifs
    · exact A.isSome X e I hI
    · exact B.isSome X e I hI

/-- Depending on the context: the least identity if the graph has an even number of events,
the greatest otherwise. -/
def parity : Sel Q := ite (fun X _ => decide (X.events.card % 2 = 0)) least greatest

/-- Depending on the receive: the least identity if `tid + idx` of the receive is even, the
greatest otherwise. -/
def byRecv : Sel Q := ite (fun _ e => decide ((e.tid + e.idx) % 2 = 0)) least greatest

end Sel

/-- A tie-break (Q9): `tie(X, e)`, the identity of a consistent source of `e` in `X`. -/
def Sel.pick (T : Sel Q) (cons : Graph Q → Bool) (X : Graph Q) (e : Ev Q) : Option (Tid × ℕ) :=
  (T.sel X e ((X.cands cons e).image Ev.idL)).map ofLex

omit [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
/-- Q9: a tie-break is equal on graphs equal as unordered graphs (equal keys), for graphs with
`Supp` (every well-formed graph and every restriction of one). A selection receives the raw
graph; on graphs without `Supp` it could read `rf`, `nd` outside the events. -/
theorem Sel.pick_congr (T : Sel Q) (cons : Graph Q → Bool) {X X' : Graph Q} (hX : X.Supp)
    (hX' : X'.Supp) (h : X.key = X'.key) (e : Ev Q) : T.pick cons X e = T.pick cons X' e := by
  rw [(Graph.eq_iff_key hX hX').mpr h]

omit [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
/-- Q9: the tie-break returns a consistent source. -/
theorem Sel.pick_spec (T : Sel Q) (cons : Graph Q → Bool) {X : Graph Q} {e : Ev Q}
    {id : Tid × ℕ} (h : T.pick cons X e = some id) :
    ∃ s ∈ X.S, cons (X.addRecv e (.snd s)) = true ∧ (s.tid, s.idx) = id := by
  unfold pick at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (T.mem _ _ _ _ hx)
  obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
  exact ⟨s, hs1, hs2, rfl⟩

omit [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
/-- Q9: the tie-break returns a source whenever a consistent one exists. -/
theorem Sel.pick_isSome (T : Sel Q) (cons : Graph Q → Bool) {X : Graph Q} {e : Ev Q}
    (h : ∃ s ∈ X.S, cons (X.addRecv e (.snd s)) = true) : (T.pick cons X e).isSome := by
  obtain ⟨s, hs, hc⟩ := h
  unfold pick
  have : ((X.cands cons e).image Ev.idL).Nonempty :=
    ⟨s.idL, Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨hs, hc⟩, rfl⟩⟩
  simpa using T.isSome X e _ this

/-! ### The two replays (Q10) -/

/-- The least element of a finite set of values. -/
def minVal (S : Finset Val) : Option Val := Sel.ofTop S.min

/-- The least element is the head of the increasing list. -/
theorem minVal_eq_head (S : Finset Val) : minVal S = (ndList S).head? := by
  unfold minVal ndList
  rw [List.head?_filter]
  rcases S.eq_empty_or_nonempty with rfl | hS
  · rw [List.find?_eq_none.mpr (by simp)]
    rfl
  · have hm : S.min = ↑(S.min' hS) := (Finset.coe_min' hS).symm
    have : Sel.ofTop S.min = some (S.min' hS) := by rw [hm]; rfl
    rw [this]
    symm
    rw [List.find?_range_eq_some]
    refine ⟨by simpa using S.min'_mem hS, ?_, fun j hj => ?_⟩
    · exact List.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) (S.min'_mem hS)))
    · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      exact fun h => absurd hj (not_lt.mpr (S.min'_le j h))

/-- Add `e` with its canonical outcome (Q10 (i)); `none` if `e` is not the next event of its
thread in `P`, or a blocking receive without a consistent source. -/
def canonAdd (cons : Graph Q → Bool) (T : Sel Q) (P : Program Q) (c : Config Q) (e : Ev Q) :
    Option (Config Q) :=
  if P.nextEv c.G e.tid ≠ some e then none else
  match e.lab with
  | .recv a _ =>
    if a.blocking then
      match T.pick cons c.G e with
      | some id =>
        match c.byId id with
        | some s => some (c.add e (some (.snd s)) none)
        | none => none
      | none => none
    else some (c.add e (some .bot) none)
  | .nd S =>
    match minVal S with
    | some v => some (c.add e none (some v))
    | none => none
  | _ => some (c.add e none none)

/-- Canonical replay of a supplied list (Q10 (i), `MaxCompletion(G, A)`). -/
def replay (cons : Graph Q → Bool) (T : Sel Q) (P : Program Q) :
    Config Q → List (Ev Q) → Option (Config Q)
  | c, [] => some c
  | c, e :: l =>
    match canonAdd cons T P c e with
    | some c' => replay cons T P c' l
    | none => none

/-- The end of a scheduler-following completion. -/
inductive Completion (Q : Type)
  /-- `next_P` is `⊥` -/
  | full (c : Config Q)
  /-- `next_P` satisfies the stop test -/
  | stopped (c : Config Q)
  /-- the fuel is exhausted -/
  | outOfFuel (c : Config Q)
  /-- the canonical addition of `next_P` failed -/
  | failed (c : Config Q) (e : Ev Q)

/-- The configuration reached. -/
def Completion.cfg : Completion Q → Config Q
  | .full c | .stopped c | .outOfFuel c | .failed c _ => c

/-- The completion ended at the stop test. -/
def Completion.isStopped : Completion Q → Bool
  | .stopped _ => true
  | _ => false

/-- Scheduler-following completion (Q10 (ii)): add `next_P` with its canonical outcome until
`next_P` is `⊥` or satisfies `stop`, at most `fuel` events; the result says how it ended. -/
def schedComplete (cons : Graph Q → Bool) (T : Sel Q) (P : Program Q) (stop : Ev Q → Bool) :
    ℕ → Config Q → Completion Q
  | 0, c => .outOfFuel c
  | n + 1, c =>
    match P.nextP cons c.G with
    | none => .full c
    | some e =>
      if stop e then .stopped c else
      match canonAdd cons T P c e with
      | some c' => schedComplete cons T P stop n c'
      | none => .failed c e

end Must
