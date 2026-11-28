import Mazurkiewicz.Condpor.Rmw.LifecycleGateRun

/-!
# Gate clause 1: what is proved and what remains (LC2-b)

`Gate1` (`LifecycleSem.lean`) is the conjunction, for a fragment program, an adequate bound
and a maximal run, of: `Wf`, `Exec`, SC ∧ atomic ∧ satisfiable, `Full`, class. Proved:
`Wf`, SC and satisfiability (`runCfg_wf_sc`). Remaining, stated as propositions (not proved):

1. `G1Exec`: every event carries the compiled action after its thread's earlier values.
2. `G1Full`: no thread has a next compiled action.
3. `G1Atomic`: every completed exclusive pair writes right after its read's source.
4. `G1Class`: `lifeClass` of the graph is the class of the final state.

`gate1_of_parts`: the four give `Gate1`. Parts 1 and 2 are proved in `LifecycleGateFinal.lean`
(`g1Exec`, `g1Full`); parts 3 and 4 remain open.
-/

namespace Condpor

namespace Life

namespace Sem

/-- Remaining part 1 of gate clause 1. -/
def G1Exec : Prop :=
  ∀ (P : LProg) (n : ℕ), fragB P = true → adequateB P n = true → ∀ rs s, MaxRun P rs s →
    (lifeSys P n).toProgram.Exec (runCfg P rs s).abs

/-- Remaining part 2 of gate clause 1. -/
def G1Full : Prop :=
  ∀ (P : LProg) (n : ℕ), fragB P = true → adequateB P n = true → ∀ rs s, MaxRun P rs s →
    (lifeSys P n).toProgram.Full (runCfg P rs s).abs

/-- Remaining part 3 of gate clause 1. -/
def G1Atomic : Prop :=
  ∀ (P : LProg) (n : ℕ), fragB P = true → adequateB P n = true → ∀ rs s, MaxRun P rs s →
    (lifeSys P n).Atomic (runCfg P rs s).abs

/-- Remaining part 4 of gate clause 1. -/
def G1Class : Prop :=
  ∀ (P : LProg) (n : ℕ), fragB P = true → adequateB P n = true → ∀ rs s, MaxRun P rs s →
    lifeClass P (runCfg P rs s) = (mclass P s).toL

/-- **Gate clause 1 from its remaining parts.** -/
theorem gate1_of_parts (h1 : G1Exec) (h2 : G1Full) (h3 : G1Atomic) (h4 : G1Class) : Gate1 := by
  intro P n hf hn rs s hr
  obtain ⟨hw, hsc, hsat⟩ := runCfg_wf_sc (frag_of_fragB hf) hr
  exact ⟨hw, h1 P n hf hn rs s hr,
    Model.sym_cons_iff.mpr ⟨Model.atomic_cons_iff.mpr ⟨hsc, h3 P n hf hn rs s hr⟩, hsat⟩,
    h2 P n hf hn rs s hr, h4 P n hf hn rs s hr⟩

end Sem

end Life

end Condpor
