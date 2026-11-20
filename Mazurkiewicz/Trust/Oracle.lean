import Mazurkiewicz.Trust.Budget

/-!
# An independent oracle for the explorer

A test, not a theorem. The oracle computes the SC behaviours of a program in
the operational way: it runs every interleaving of the threads on a memory
and records, for each event, what determines the execution graph: for a read
the write it read from, for a write the previous write to its location. It
uses `Program.step` only; it does not use `avail`, `next`, `Step`, execution
graphs or the consistency predicate.

The explorer's graphs are turned into the same form (`sigOf`, from the
configurations that the explorer reaches) and the two sets are compared on
the example programs (`#guard agree …`).

`exploreCfgC` is `exploreC` returning configurations instead of graphs;
`exploreCfgC_abs` proves that its graphs are those of `exploreC`.
-/

namespace Trust

open Program

/-- A graph of a program in a form that can be compared: for every thread in
the order of the program, its events in order, each with its source (a read)
or its coherence predecessor (a write). -/
abbrev Sig := List (TEv × Ev)

/-! ### The oracle: interleavings on a memory -/

/-- A state of the sequential execution: the traces of the threads, the
memory with the last writer of each location, and the record so far. -/
structure OState where
  traces : Tid → List (Option Val)
  mem : Loc → Val × Ev
  record : Sig

/-- Thread `t` performs its next action, if it has one. -/
def oStep (P : Program) (s : OState) (t : Tid) : Option OState :=
  match P.step t (s.traces t) with
  | none => none
  | some (.read x) =>
    let e : TEv := ⟨t, (s.traces t).length, .read x⟩
    some ⟨Function.update s.traces t (s.traces t ++ [some (s.mem x).1]), s.mem,
      s.record ++ [(e, (s.mem x).2)]⟩
  | some (.write x v) =>
    let e : TEv := ⟨t, (s.traces t).length, .write x v⟩
    some ⟨Function.update s.traces t (s.traces t ++ [none]),
      Function.update s.mem x (v, .th e), s.record ++ [(e, (s.mem x).2)]⟩

/-- The record, with the events grouped by thread. -/
def canon (P : Program) (r : Sig) : Sig :=
  P.threads.flatMap (fun t => r.filter (fun p => decide (p.1.tid = t)))

/-- All runs with at most `fuel` steps: `some` record for a run that ends
with no thread enabled, `none` for a run that is cut off. -/
def oRuns (P : Program) : ℕ → OState → List (Option Sig)
  | 0, s =>
    if P.threads.all (fun t => (oStep P s t).isNone) then [some (canon P s.record)]
    else [none]
  | fuel + 1, s =>
    if P.threads.all (fun t => (oStep P s t).isNone) then [some (canon P s.record)]
    else P.threads.flatMap (fun t =>
      match oStep P s t with
      | none => []
      | some s' => oRuns P fuel s')

/-- The SC behaviours of `P` by interleaving, without repetition; `none` if
some run needs more than `n` events of each thread (the bound `n` is too
small for the program). -/
def oracle (P : Program) (n : ℕ) : Option (List Sig) :=
  let runs := oRuns P (n * P.threads.length) ⟨fun _ => [], fun x => (P.mem x, .init), []⟩
  if runs.all Option.isSome then some (runs.filterMap id).dedup else none

/-! ### The explorer, returning configurations -/

/-- `exploreFromC`, returning the configurations. -/
def exploreCfgFromC (P : Program) : ℕ → Config → List Config
  | 0, _ => []
  | f + 1, c =>
    if c.consC then
      if P.nextC c = none then [c] else (succsC P c).flatMap (exploreCfgFromC P f)
    else []

/-- `exploreC`, returning the configurations. -/
def exploreCfgC (P : Program) (n : ℕ) : List Config :=
  exploreCfgFromC P (P.bound n + 1) (Config.init P.mem)

theorem exploreCfgFromC_abs (P : Program) (f : ℕ) (c : Config) :
    (exploreCfgFromC P f c).map Config.abs = exploreFromC P f c := by
  induction f generalizing c with
  | zero => rfl
  | succ f ih =>
    unfold exploreCfgFromC exploreFromC
    split
    · split
      · rfl
      · rw [List.map_flatMap]
        exact List.flatMap_congr (fun c1 _ => ih c1)
    · rfl

/-- The graphs of the configurations are the graphs that `exploreC` lists. -/
theorem exploreCfgC_abs (P : Program) (n : ℕ) :
    (exploreCfgC P n).map Config.abs = exploreC P n :=
  exploreCfgFromC_abs P _ _

/-- The write before `e` in a coherence list, `init` if `e` is first. -/
def coPredOf (l : List TEv) (e : TEv) : Ev :=
  match l.idxOf e with
  | 0 => .init
  | k + 1 => .th (l.getD k e)

/-- The comparable form of the graph of a configuration. -/
def sigOf (P : Program) (c : Config) : Sig :=
  P.threads.flatMap (fun t =>
    (List.range (c.cnt t)).filterMap (fun i =>
      (c.evAt t i).map (fun e =>
        (e, match e.act with
            | .read _ => (c.rf e).getD .init
            | .write x _ => coPredOf (c.co x) e))))

/-- The explorer and the oracle give the same set of graphs, and the explorer
lists as many graphs as the oracle has behaviours. `false` if the bound `n`
is too small for the oracle. (For the explorer the bound must satisfy
`P.Bounded n`; the records are those of well-formed configurations.) -/
def agree (P : Program) (n : ℕ) : Bool :=
  let ex := (exploreCfgC P n).map (sigOf P)
  match oracle P n with
  | none => false
  | some orc =>
    ex.all (fun s => decide (s ∈ orc)) && orc.all (fun s => decide (s ∈ ex)) &&
      decide (ex.length = orc.length)

namespace Examples

set_option linter.hashCommand false

#guard agree wwrr 2
#guard agree wwrrRev 2
#guard agree rww 2
#guard agree rwwSeq 2
#guard agree revProg 2
#guard agree copy 2
#guard agree emptyP 0
#guard agree (wwrr.trunc (fun _ => 1)) 1
#guard ((oracle wwrr 2).map List.length) == some 4
#guard ((oracle rww 2).map List.length) == some 6
-- a bound that is too small is detected
#guard !agree wwrr 0
#guard !agree rww 0

end Examples

end Trust
