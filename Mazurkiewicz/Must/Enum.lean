import Mazurkiewicz.Must.ExploreC

/-!
# An enumerator of `⟦P⟧`, independent of the algorithm

Plan: row M2 ("an independent enumerator of `⟦P⟧`").

* `extendE P c`: every one-event extension of `c` by the next event of some thread of `P`: a
  receive with every send of the graph and with `⊥`, an ND event with every outcome, the other
  events as they are; an extension is kept iff it is well-formed (`WfD`). No consistency test
  and no availability test on the way (pruning by consistency would assume prefix-closedness,
  M3).
* `allExecs P levels`: the executions with at most `levels` events, level by level, each level
  deduplicated by `key`.
* `semEnum cons P levels`: those in `⟦P⟧` (`SemD`: well-formed, execution, consistent,
  `availM = ∅`).
* `semTruncated`: an execution with `levels` events still has an extension.

Not proved here (obligation for M3/M4, `mem_semEnum_iff`): for a program `P`, a consistency
`cons` and `levels` with `∀ H, H.Wf → P.Exec H → H.events.card ≤ levels`,
`(∃ c ∈ semEnum cons P levels, c.G.key = G.key) ↔ P.Sem cons G` for every graph `G` with
`Supp`; and the form used by the computations, with the hypothesis
`semTruncated P levels = false` in place of the bound. Soundness (`→`) follows from
`semD_iff` once every enumerated configuration is shown to have `Supp` and to satisfy
`Exec`; completeness (`←`) by a linear extension of `porf` on `G`:
each of its prefixes is a well-formed execution obtained by `extendE` from the previous one, and
deduplication by key is harmless because `extendE` depends on the unordered graph only (up to
the order of its result). The `decide` theorems and the search use `semEnum` with a level bound
and check that it is not truncated (`semTruncated`), so "explorer = `⟦P⟧`" there means
"explorer = `semEnum`".
* `compareR`: the reported configurations of an exploration against `semEnum`, by `key`:
  missed graphs, reported graphs outside `⟦P⟧`, graphs reported more than once; with the
  fuel, dead-end, repeated-visit and truncation counters, all part of `CmpR.ok`.
-/

namespace Must

variable {Q : Type} [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)]

/-- The one-event extensions by the next event of a thread, with well-formedness checks only. -/
def extendE (P : Program Q) (c : Config Q) : List (Config Q) :=
  P.threads.flatMap fun t =>
    match P.nextEv c.G t with
    | none => []
    | some e =>
      match e.lab with
      | .nd S => (ndList S).map (fun v => c.add e none (some v))
      | .recv _ _ =>
        (((c.order.filter (fun d : Ev Q => decide d.IsSend)).map Src.snd) ++ [Src.bot]).filterMap
          fun x =>
            let c' := c.add e (some x) none
            if decide c'.G.WfD then some c' else none
      | _ => [c.add e none none]

/-- Keep the first configuration of each key. -/
def dedupKey (l : List (Config Q)) : List (Config Q) :=
  l.foldl (fun acc c => if acc.any (fun c' => decide (c'.G.key = c.G.key)) then acc else acc ++ [c])
    []

/-- All executions with at most `levels` events, deduplicated by key. -/
def allExecs (P : Program Q) : ℕ → List (Config Q) → List (Config Q)
  | 0, cur => cur
  | n + 1, cur =>
    let nxt := dedupKey (cur.flatMap (extendE P))
    if nxt.isEmpty then cur else cur ++ allExecs P n nxt

/-- `⟦P⟧`, enumerated. -/
def semEnum (cons : Graph Q → Bool) (P : Program Q) (levels : ℕ) : List (Config Q) :=
  (allExecs P levels [.init]).filter (fun c => decide (P.SemD cons c.G))

/-- The executions with exactly `levels` events (the last level), deduplicated by key; empty if
the enumeration ends earlier. -/
def frontier (P : Program Q) : ℕ → List (Config Q) → List (Config Q)
  | 0, cur => cur
  | n + 1, cur =>
    let nxt := dedupKey (cur.flatMap (extendE P))
    if nxt.isEmpty then [] else frontier P n nxt

/-- The enumeration with at most `levels` events is truncated: an execution of the last level
has an extension. -/
def semTruncated (P : Program Q) (levels : ℕ) : Bool :=
  !((frontier P levels [.init]).flatMap (extendE P)).isEmpty

/-- The number of visits of a configuration `≈` an earlier visited one (Theorem 4.1 (a) asks
for none). -/
def repeatedVisits (r : Result Q) : ℕ := r.seen.length - (dedupKey r.seen).length

/-- The comparison of an exploration with `⟦P⟧`. -/
structure CmpR (Q : Type) where
  /-- graphs of `⟦P⟧` not reported -/
  missed : List (Config Q)
  /-- reported graphs outside `⟦P⟧` -/
  extra : List (Config Q)
  /-- graphs reported more than once, with multiplicity -/
  dups : List (Config Q × ℕ)
  /-- fuel exhausted -/
  exhausted : Bool
  /-- configurations with `next_P ≠ ⊥` and no successor -/
  dead : ℕ
  /-- repeated visits -/
  repeats : ℕ
  /-- the enumeration was truncated -/
  truncated : Bool

/-- Success: every graph of `⟦P⟧` reported exactly once and nothing else, search completed, no
dead end, no repeated visit, enumeration not truncated. -/
def CmpR.ok (c : CmpR Q) : Bool :=
  c.missed.isEmpty && c.extra.isEmpty && c.dups.isEmpty && !c.exhausted && c.dead == 0 &&
    c.repeats == 0 && !c.truncated

/-- Compare by key. -/
def compareR (r : Result Q) (sem : List (Config Q)) (truncated : Bool) : CmpR Q :=
  let cnt (c : Config Q) : ℕ := (r.reported.filter (fun c' => decide (c'.G.key = c.G.key))).length
  { missed := sem.filter (fun c => cnt c = 0)
    extra := (dedupKey r.reported).filter
      (fun c => !(sem.any (fun c' => decide (c'.G.key = c.G.key))))
    dups := ((dedupKey r.reported).map (fun c => (c, cnt c))).filter (fun p => p.2 > 1)
    exhausted := r.exhausted
    dead := r.dead
    repeats := repeatedVisits r
    truncated := truncated }

end Must
