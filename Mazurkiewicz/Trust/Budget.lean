import Mazurkiewicz.Trust.ExploreC

/-!
# Budgets

`induction-popl`, `dpor.tex`, def:budget and lem:budget: the truncation
`P|κ` of a program by a budget `κ : Tid → ℕ` lets thread `t` perform at most
`κ t` events.

* `Program.trunc`: the truncated program (def:budget).
* `Program.exec_trunc_iff`: lem:budget (1), an execution of `P|κ` is an
  execution of `P` with at most `κ t` events of each thread `t`; and
  `Program.trunc_bounded`.
* `Program.full_trunc_iff`: lem:budget (2); `Program.Exec.full_trunc_cnt`:
  every execution `H` of `P` is a full execution of `P|cnt(H)`.
* lem:budget (3) is `Program.Exec.of_isPrefixOf` (`Trust/Program.lean`).
* `exploreC_trunc_spec`: the explorer on a truncated program, for an
  arbitrary program `P` (no boundedness hypothesis on `P`).

The lemma is stated here for well-formed graphs.
-/

namespace Trust

open Program

namespace Program

variable (P : Program)

/-- The truncation `P|κ` (`dpor.tex`, def:budget): thread `t` stops after
`κ t` events. -/
def trunc (κ : Tid → ℕ) : Program where
  threads := P.threads
  threads_nodup := P.threads_nodup
  step := fun t u => if u.length < κ t then P.step t u else none
  mem := P.mem
  step_none := by
    intro t ht
    split
    · exact P.step_none t ht
    · rfl

variable {P}

theorem trunc_step_eq_some {κ : Tid → ℕ} {t : Tid} {u : List (Option Val)} {a : Act} :
    (P.trunc κ).step t u = some a ↔ u.length < κ t ∧ P.step t u = some a := by
  unfold trunc
  simp only
  split <;> simp_all

theorem trunc_step_eq_none {κ : Tid → ℕ} {t : Tid} {u : List (Option Val)} :
    (P.trunc κ).step t u = none ↔ κ t ≤ u.length ∨ P.step t u = none := by
  unfold trunc
  simp only
  split
  · rename_i h
    exact ⟨Or.inr, fun h' => h'.resolve_left (Nat.not_le.mpr h)⟩
  · rename_i h
    exact ⟨fun _ => Or.inl (Nat.le_of_not_lt h), fun _ => rfl⟩

/-- The truncation by a budget below `n` is bounded by `n`. -/
theorem trunc_bounded {κ : Tid → ℕ} {n : ℕ} (hκ : ∀ t, κ t ≤ n) : (P.trunc κ).Bounded n := by
  intro t u hu
  exact trunc_step_eq_none.mpr (Or.inl ((hκ t).trans hu))

/-- In a well-formed graph, "thread `t` has at most `κ t` events" in terms of
the indices of the events. -/
theorem cnt_le_iff {G : Graph} (hG : G.Wf) (κ : Tid → ℕ) :
    (∀ t, G.cnt t ≤ κ t) ↔ ∀ e ∈ G.events, e.idx < κ e.tid := by
  constructor
  · intro h e he
    exact Nat.lt_of_lt_of_le (hG.idx_lt_cnt he) (h e.tid)
  · intro h t
    by_contra hlt
    obtain ⟨e, he, ht, hi⟩ := (hG.exists_idx_iff t (κ t)).mpr (Nat.lt_of_not_le hlt)
    have := h e he
    rw [ht, hi] at this
    exact Nat.lt_irrefl _ this

/-- lem:budget (1): the executions of `P|κ` are the executions of `P` within
the budget. -/
theorem exec_trunc_iff {G : Graph} (hG : G.Wf) (κ : Tid → ℕ) :
    (P.trunc κ).Exec G ↔ P.Exec G ∧ ∀ t, G.cnt t ≤ κ t := by
  rw [cnt_le_iff hG]
  unfold Exec
  constructor
  · rintro ⟨hm, h⟩
    refine ⟨⟨hm, fun e he => (trunc_step_eq_some.mp (h e he)).2⟩, fun e he => ?_⟩
    have := (trunc_step_eq_some.mp (h e he)).1
    rwa [Graph.traceBefore_length] at this
  · rintro ⟨⟨hm, h⟩, hk⟩
    refine ⟨hm, fun e he => trunc_step_eq_some.mpr ⟨?_, h e he⟩⟩
    rw [Graph.traceBefore_length]
    exact hk e he

/-- lem:budget (2): an execution of `P|κ` is full iff every thread has used
its budget or has terminated in `P`. -/
theorem full_trunc_iff {G : Graph} (hG : G.Wf) {κ : Tid → ℕ} (hE : (P.trunc κ).Exec G) :
    (P.trunc κ).Full G ↔
      ∀ t ∈ P.threads, G.cnt t = κ t ∨ P.step t (G.trace t) = none := by
  have hle := ((exec_trunc_iff hG κ).mp hE).2
  rw [full_iff]
  refine forall_congr' (fun t => forall_congr' (fun _ => ?_))
  rw [trunc_step_eq_none, Graph.trace_length]
  exact or_congr ⟨fun h => Nat.le_antisymm (hle t) h, fun h => Nat.le_of_eq h.symm⟩ Iff.rfl

/-- lem:budget (2), second part: an execution of `P` is a full execution of
the truncation of `P` by its own count. -/
theorem Exec.full_trunc_cnt {G : Graph} (hG : G.Wf) (hE : P.Exec G) :
    (P.trunc G.cnt).Exec G ∧ (P.trunc G.cnt).Full G := by
  have hE' : (P.trunc G.cnt).Exec G := (exec_trunc_iff hG _).mpr ⟨hE, fun _ => Nat.le_refl _⟩
  exact ⟨hE', (full_trunc_iff hG hE').mpr (fun _ _ => Or.inl rfl)⟩

end Program

/-- The explorer on a truncated program, for an arbitrary program `P`: with a
budget `κ` below `n`, `exploreC (P.trunc κ) n` lists, without repetition,
exactly the well-formed, SC-consistent executions of `P` within the budget
in which every thread has used its budget or has terminated. -/
theorem exploreC_trunc_spec (P : Program) {κ : Tid → ℕ} {n : ℕ} (hκ : ∀ t, κ t ≤ n) :
    (exploreC (P.trunc κ) n).Nodup ∧
      ∀ G, G ∈ exploreC (P.trunc κ) n ↔
        G.Wf ∧ P.Exec G ∧ (∀ t, G.cnt t ≤ κ t) ∧ SC.cons G ∧
          ∀ t ∈ P.threads, G.cnt t = κ t ∨ P.step t (G.trace t) = none := by
  obtain ⟨hnd, hmem⟩ := exploreC_spec (Program.trunc_bounded (P := P) hκ)
  refine ⟨hnd, fun G => ?_⟩
  rw [hmem]
  constructor
  · rintro ⟨hW, hE, hc, hF⟩
    obtain ⟨hE', hle⟩ := (Program.exec_trunc_iff hW κ).mp hE
    exact ⟨hW, hE', hle, hc, (Program.full_trunc_iff hW hE).mp hF⟩
  · rintro ⟨hW, hE, hle, hc, hF⟩
    have hE' := (Program.exec_trunc_iff hW κ).mpr ⟨hE, hle⟩
    exact ⟨hW, hE', hc, (Program.full_trunc_iff hW hE').mpr hF⟩

namespace Examples

set_option linter.hashCommand false

-- `w+w+rr` with one event per thread: the third thread stops after its read of `x`
#guard (exploreC (wwrr.trunc (fun _ => 1)) 1).length == 2
-- with no event for the reader: one graph
#guard (exploreC (wwrr.trunc (fun t => if t = 2 then 0 else 1)) 1).length == 1
-- a budget above the program changes nothing
#guard (exploreC (wwrr.trunc (fun _ => 5)) 5).length == 4

end Examples

end Trust
