import Mazurkiewicz.Condpor.Rmw.LifecycleGateClass

/-!
# Gate clause 2: the decomposition (LC2-b, continuation; not proved)

`Gate2` reduced to three stated propositions, in this order:

1. `G2Lin` (graph theory, independent of lifecycle programs): a well-formed SC-consistent
   graph has a linearization of its events along which every `po ∪ rf ∪ co ∪ fr` edge goes
   forward.
2. `G2Adj`: for a terminal-valid graph of `lifeSys`, a linearization can be chosen in which
   the write of every completed exclusive pair comes right after its read (atomicity: no write
   to the location in between; the events in between are moved past).
3. `G2Replay`: such a linearization is replayed on the machine: there is a maximal run whose
   graph is the given one (calls grouped by the compiled table, `Enabled` at each step by the
   LC1 lemmas, maximality from the final waits).

`gate2_of_parts : G2Lin → G2Adj → G2Replay → Gate2` (proved).
-/

namespace Condpor

namespace Life

namespace Sem

/-- A linearization of the events of `G`: no repetition, exactly the events, every SC edge
between thread events forward. -/
def IsLin (G : Graph) (L : List TEv) : Prop :=
  L.Nodup ∧ (∀ e, e ∈ L ↔ e ∈ G.events) ∧ ∀ a b, G.scStep (.th a) (.th b) → L.Before a b

/-- The terminal-valid configurations of `lifeSys` (the hypotheses of `Gate2`). -/
def TermValid (P : LProg) (n : ℕ) (c : Config) : Prop :=
  fragB P = true ∧ adequateB P n = true ∧ c.Wf ∧ (lifeSys P n).toProgram.Exec c.abs ∧
    ((Model.atomic (lifeSys P n) SC).sym EqSem.solver).cons c.abs ∧
    (lifeSys P n).toProgram.Full c.abs ∧ lifeClass P c ≠ .exploration

/-- Remaining 1: well-formed SC graphs have linearizations. -/
def G2Lin : Prop := ∀ G : Graph, G.Wf → SC.cons G → ∃ L, IsLin G L

/-- Remaining 2: for terminal-valid graphs, a linearization with adjacent exclusive pairs. -/
def G2Adj : Prop :=
  ∀ P n c, TermValid P n c → (∃ L, IsLin c.abs L) →
    ∃ L, IsLin c.abs L ∧ ∀ r w, (lifeSys P n).RMW c.abs r w → ∃ l₁ l₂, L = l₁ ++ r :: w :: l₂

/-- Remaining 3: the replay. -/
def G2Replay : Prop :=
  ∀ P n c, TermValid P n c →
    (∃ L, IsLin c.abs L ∧ ∀ r w, (lifeSys P n).RMW c.abs r w → ∃ l₁ l₂, L = l₁ ++ r :: w :: l₂) →
    ∃ rs s, MaxRun P rs s ∧ (runCfg P rs s).abs = c.abs

/-- **Gate clause 2 from its parts.** -/
theorem gate2_of_parts (h1 : G2Lin) (h2 : G2Adj) (h3 : G2Replay) : Gate2 := by
  intro P n hf hn c hw he hc hfu hex
  have hT : TermValid P n c := ⟨hf, hn, hw, he, hc, hfu, hex⟩
  have hsc : SC.cons c.abs := (Model.atomic_cons_iff.mp (Model.sym_cons_iff.mp hc).1).1
  exact h3 P n c hT (h2 P n c hT (h1 c.abs hw.1 hsc))

end Sem

end Life

end Condpor
