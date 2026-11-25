import Mazurkiewicz.Condpor.Rmw.LifecycleGate2Tr

/-!
# Gate clause 2, part 3: the replay, decomposed (LC2-b, continuation 3)

`G2Replay` from two stated parts (`g2Replay_of_parts`, proved) and the run list
(`exists_runList`, proved):

1. `G2Steps`: the machine replays a run list `l` of a terminal-valid graph: some run from the
   initial state ends in a state `s` with `SInv` whose builder list is exactly `l`.
2. `G2Final`: after such a run the state is maximal, and the final builder list (`l` and the
   synthetic events of `finalize`) is a sub-linearization containing every event of the graph.

Then the graph of the run is the given graph (`abs_eq_of_subLin`).
-/

namespace Condpor

namespace Life

namespace Sem

/-- Remaining 3.1: the machine replays a run list. -/
def G2Steps : Prop :=
  ∀ P n c l, TermValid P n c → RunList P (lifeSys P n) c.abs l →
    ∃ rs s, Steps P (MState.init P) rs s ∧ SInv P n s (rs.foldl (emit P) GB.empty) ∧
      (rs.foldl (emit P) GB.empty).L = l

/-- Remaining 3.2: at the end of the replay the state is maximal and `finalize` adds exactly
the tail events, after all others. -/
def G2Final : Prop :=
  ∀ P n c l, TermValid P n c → RunList P (lifeSys P n) c.abs l →
    ∀ rs s, Steps P (MState.init P) rs s → SInv P n s (rs.foldl (emit P) GB.empty) →
      (rs.foldl (emit P) GB.empty).L = l →
      Maximal P s ∧ SubLin c.abs (finalize P (rs.foldl (emit P) GB.empty) s).L ∧
        ∀ e ∈ c.abs.events, e ∈ (finalize P (rs.foldl (emit P) GB.empty) s).L

/-- Remaining 3.1.1: one step of the replay. If the run so far built a proper prefix of the
run list, some enabled occurrence emits the next events of the list (one or two). -/
def G2Step : Prop :=
  ∀ P n c l, TermValid P n c → RunList P (lifeSys P n) c.abs l →
    ∀ rs s e rest, Steps P (MState.init P) rs s → l = (rs.foldl (emit P) GB.empty).L ++ e :: rest →
      ∃ o pre rest', Enabled P s o ∧
        (emit P (rs.foldl (emit P) GB.empty) o).L = (rs.foldl (emit P) GB.empty).L ++ pre ∧
        e :: rest = pre ++ rest' ∧ pre ≠ []

theorem steps_snoc2 {P : LProg} {s s1 s2 : MState} {rs : List Occ} {o : Occ}
    (h : Steps P s rs s1) (h2 : Step P s1 o s2) : Steps P s (rs ++ [o]) s2 := by
  induction h with
  | nil s => exact .cons h2 (.nil _)
  | cons h _ ih => exact .cons h (ih h2)

/-- **The replay of a run list from the one-step part.** -/
theorem g2Steps_of_step (h : G2Step) : G2Steps := by
  intro P n c l hT hl
  have hF := frag_of_fragB hT.1
  have hn := hT.2.1
  suffices ∀ k rs s, Steps P (MState.init P) rs s → ∀ rest,
      l = (rs.foldl (emit P) GB.empty).L ++ rest → rest.length ≤ k →
      ∃ rs s, Steps P (MState.init P) rs s ∧ (rs.foldl (emit P) GB.empty).L = l by
    obtain ⟨rs, s, hs, hL⟩ := this l.length [] _ (.nil _) l (by simp [GB.L, GB.empty]) le_rfl
    exact ⟨rs, s, hs, SInv.steps hF hn hs, hL⟩
  intro k
  induction k with
  | zero =>
    intro rs s hs rest hl0 hk
    have : rest = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hk)
    subst this
    exact ⟨rs, s, hs, by simpa using hl0.symm⟩
  | succ k ih =>
    intro rs s hs rest hl0 hk
    cases rest with
    | nil => exact ⟨rs, s, hs, by simpa using hl0.symm⟩
    | cons e rest =>
      obtain ⟨o, pre, rest', hen, hemit, hsplit, hne⟩ := h P n c l hT hl rs s e rest hs hl0
      have hs' := steps_snoc2 hs ⟨hen, rfl⟩
      refine ih (rs ++ [o]) _ hs' rest' ?_ ?_
      · rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hemit, hl0, hsplit,
          List.append_assoc]
      · have h1 := congrArg List.length hsplit
        simp only [List.length_cons, List.length_append] at h1 hk
        have : pre.length ≠ 0 := fun h0 => hne (List.eq_nil_of_length_eq_zero h0)
        omega

/-- **The replay from its parts.** -/
theorem g2Replay_of_parts (h1 : G2Steps) (h2 : G2Final) : G2Replay := by
  intro P n c hT ⟨L, hL, hadj⟩
  have hT' := hT
  obtain ⟨hf, -, hw, hE, -, -, -⟩ := hT'
  have hG : c.abs.Wf := hw.1
  obtain ⟨l, hl⟩ := exists_runList (P := P) (X := lifeSys P n) hG hL hadj
  obtain ⟨rs, s, hs, hI, hL'⟩ := h1 P n c l hT hl
  obtain ⟨hmax, hsub, hall⟩ := h2 P n c l hT hl rs s hs hI hL'
  have hr : MaxRun P rs s := ⟨hs, hmax⟩
  refine ⟨rs, s, hr, ?_⟩
  exact abs_eq_of_subLin (runCfg_ok (frag_of_fragB hf) hr) hG hsub hall hE.1
    (pol_none_of_exec hw hE)

end Sem

end Life

end Condpor
