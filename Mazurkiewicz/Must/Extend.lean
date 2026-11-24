import Mazurkiewicz.Must.Replay
import Mathlib.Data.Finset.Prod

/-!
# Consistent extension, finite completion, Theorem A.3 (b) (milestone M5)

Paper: Appendix A.1 (Definition A.2, Theorem A.3 (b)), Definition A.7 (`full`). Plan: decisions
Q8, Q10 (ii), Q13, fate row "Thm 4.1/A.3 (b)" (R: every reached configuration reaches a member
of `⟦P⟧` by non-revisit steps), plan row M5 (`ReachM.reaches_full`, `completion_congr`).

Hypotheses, stated where used: a bounded program (`Program.Bounded n`: no thread performs more
than `n` events); ND labels with non-empty sets (the field `Program.nd_ne` of every program).
`fruitless_unbounded` shows that the bound is needed.

* `NrStep M P`: a non-revisit step of Algorithm 1 on configurations (the constructor `StepM.nr`).
* `exists_nrAdd`: on a configuration with the invariant, the event `next_P` has a non-revisit
  step (every model; Q7, Q11, `Program.nd_ne`).
* `card_le_of_bounded`: an execution of a program bounded by `n` has at most `|threads| · n`
  events.
* `Config.Inv.reaches_full`, `ReachM.reaches_full`: from every configuration with the invariant
  (every reachable one) a configuration without next event, whose graph is in `⟦P⟧`, is reached by
  non-revisit steps. `ReachM.not_fruitless`: Theorem A.3 (b), repaired (no early exit, Q12).
* `SchedStep M tie P` (Q10 (ii)): add `next_P` with its canonical source and outcome;
  `Completes M tie P G G_f`: a scheduler-following path from `G` to a full graph.
  `completion_exists` (bounded program), `completion_unique`, and `completion_congr`: two
  configurations equal up to the insertion order (`≈`) complete to the same full graph.
* `SchedStep.nrStep`, `schedRun_nrSteps` (for M9): a scheduler run from a configuration with the
  invariant lifts to non-revisit steps of Algorithm 1.

Every result holds for every model `M` (and every tie-break with `TieQ9` where `tie` occurs).
-/

namespace Must

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q} {tie : Tie Q}

/-! ### Non-revisit steps always exist -/

/-- A non-revisit step of Algorithm 1 on configurations. -/
def NrStep (M : Model Q) (P : Program Q) (c c' : Config Q) : Prop :=
  ∃ e src out, NrAdd M P c.G e src out ∧ c' = c.add e src out

theorem NrStep.stepM {c c' : Config Q} (h : NrStep M P c c') : StepM M tie P c c' := by
  obtain ⟨e, src, out, h, rfl⟩ := h
  exact .nr h

/-- On a configuration with the invariant, the event `next_P` has a non-revisit successor
(Q7 for receives, Q11, and the non-empty sets of ND labels). -/
theorem exists_nrAdd {c : Config Q} (hc : c.Inv M P) {e : Ev Q} (hn : M.nextP P c.G = some e) :
    ∃ src out, NrAdd M P c.G e src out := by
  have he := Model.mem_availM_of_nextP hn
  obtain ⟨t, -, ht, hu⟩ := M.mem_availM_iff'.mp he
  have hidx := Model.idx_of_nextEv ht
  unfold Program.nextEv at ht
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp ht
  cases l with
  | recv a vals =>
    cases hb : a.blocking with
    | true =>
      have hB : (⟨t, c.G.cnt t, .recv a vals⟩ : Ev Q).IsRecvB := by
        simp [Ev.IsRecvB, Lab.IsRecvB, hb]
      obtain ⟨s, hs, hcs⟩ := hu.resolve_left (not_not.mpr hB)
      exact ⟨_, _, hn, Or.inr (Or.inl ⟨trivial, rfl, Or.inr ⟨s, hs, rfl⟩, hcs⟩)⟩
    | false =>
      have hNB : (⟨t, c.G.cnt t, .recv a vals⟩ : Ev Q).IsRecvNB := by
        simp [Ev.IsRecvNB, Lab.IsRecvNB, hb]
      exact ⟨_, _, hn, Or.inr (Or.inl ⟨trivial, rfl, Or.inl rfl,
        M.ext_bot _ _ hc.cons hidx hNB⟩)⟩
  | send m d v =>
    exact ⟨_, _, hn, Or.inr (Or.inr (Or.inl ⟨trivial, rfl, rfl,
      M.ext_plain _ _ hc.cons hidx (by simp [Ev.IsRecv, Lab.IsRecv])
        (by simp [Ev.IsND, Lab.IsND])⟩))⟩
  | nd S =>
    obtain ⟨v, hv⟩ := P.nd_ne _ _ S hl
    exact ⟨_, _, hn, Or.inl ⟨S, v, rfl, hv, rfl, rfl⟩⟩
  | block => exact ⟨_, _, hn, Or.inr (Or.inr (Or.inr ⟨trivial, rfl, rfl⟩))⟩
  | error => exact ⟨_, _, hn, Or.inr (Or.inr (Or.inr ⟨trivial, rfl, rfl⟩))⟩

/-! ### The size of an execution of a bounded program -/

omit [DecidableEq Q] in
/-- An execution of a program in which no thread performs more than `n` events has at most
`|threads| · n` events. -/
theorem card_le_of_bounded {G : Graph Q} (hG : G.Wf) (hE : P.Exec G) {n : ℕ}
    (hb : P.Bounded n) : G.events.card ≤ P.threads.length * n := by
  classical
  have hinj : Set.InjOn (fun x : Ev Q => (x.tid, x.idx)) (G.events : Set (Ev Q)) := by
    intro x hx y hy hxy
    simp only [Prod.mk.injEq] at hxy
    exact hG.idx_inj x hx y hy hxy.1 hxy.2
  have hsub : G.events.image (fun x : Ev Q => (x.tid, x.idx)) ⊆
      P.threads.toFinset ×ˢ Finset.range n := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_product.mpr ⟨List.mem_toFinset.mpr (hG.tid_mem_threads hE hx),
      Finset.mem_range.mpr ?_⟩
    by_contra hge
    have h1 := hE x hx
    rw [hb x.tid _ (by simpa [traceBefore] using not_lt.mp hge)] at h1
    cases h1
  calc G.events.card = (G.events.image (fun x : Ev Q => (x.tid, x.idx))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (P.threads.toFinset ×ˢ Finset.range n).card := Finset.card_le_card hsub
    _ = P.threads.toFinset.card * n := by rw [Finset.card_product, Finset.card_range]
    _ ≤ P.threads.length * n := Nat.mul_le_mul_right _ (List.toFinset_card_le _)

/-! ### Finite completion by non-revisit steps -/

/-- From a configuration with the invariant of a bounded program, a configuration without next
event is reached by non-revisit steps; its graph is in `⟦P⟧`. -/
theorem Config.Inv.reaches_full {n : ℕ} (hb : P.Bounded n) :
    ∀ (k : ℕ) (c : Config Q), c.Inv M P → P.threads.length * n - c.G.events.card = k →
      ∃ c', ReflTransGen (NrStep M P) c c' ∧ c'.Inv M P ∧ M.nextP P c'.G = none := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro c hc hk
    cases hn : M.nextP P c.G with
    | none => exact ⟨c, ReflTransGen.refl, hc, hn⟩
    | some e =>
      obtain ⟨src, out, ha⟩ := exists_nrAdd hc hn
      obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hn
      have hc' : (c.add e src out).Inv M P := hc.add ht (ha.cons hc)
      have heG := hc.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht)
      have hcard : (c.add e src out).G.events.card = c.G.events.card + 1 := by
        simp only [Config.add, add_events]
        exact Finset.card_insert_of_notMem heG
      have hle := card_le_of_bounded hc'.wf hc'.exec hb
      obtain ⟨c', h1, h2⟩ := ih _ (by omega) (c.add e src out) hc' rfl
      exact ⟨c', ReflTransGen.head ⟨e, src, out, ha, rfl⟩ h1, h2⟩

/-- `ReachM.reaches_full` (plan row M5; Theorem A.3 (b) repaired): for a bounded program, from
every reachable configuration a reachable configuration without next event is reached by
non-revisit steps, and its graph is in `⟦P⟧`. Every model, every tie-break. -/
theorem ReachM.reaches_full {n : ℕ} (hb : P.Bounded n) {c : Config Q} (h : ReachM M tie P c) :
    ∃ c', ReflTransGen (NrStep M P) c c' ∧ ReachM M tie P c' ∧ M.nextP P c'.G = none ∧
      M.Sem P c'.G := by
  obtain ⟨c', h1, -, h3⟩ := h.sound.reaches_full hb _ c rfl
  have hr : ReachM M tie P c' := h.trans (h1.lift id (fun _ _ hs => NrStep.stepM hs))
  exact ⟨c', h1, hr, h3, reported_mem_sem hr h3⟩

/-- Theorem A.3 (b), repaired (fate row: no early exit): for a bounded program, no reachable
configuration is fruitless (Definition A.2). Every model, every tie-break. -/
theorem ReachM.not_fruitless {n : ℕ} (hb : P.Bounded n) {c : Config Q} (h : ReachM M tie P c) :
    ¬ Fruitless M tie P c := by
  obtain ⟨c', h1, -, h3, -⟩ := h.reaches_full hb
  exact fun hf => hf ⟨c', h1.lift id (fun _ _ hs => NrStep.stepM hs), h3⟩

/-! ### Scheduler-following completion (Q10 (ii)) -/

/-- A step of the scheduler-following completion that stops at `stop` (Q10 (ii)): add
`e = next_P(G)`, with `stop e = false`, with its canonical source and outcome. -/
def SchedStep (M : Model Q) (tie : Tie Q) (P : Program Q) (stop : Ev Q → Bool)
    (G G' : Graph Q) : Prop :=
  ∃ e, M.nextP P G = some e ∧ stop e = false ∧ CanonStep tie P G e G'

/-- `G` completes to the full graph `G_f` by scheduler-following canonical steps. -/
def Completes (M : Model Q) (tie : Tie Q) (P : Program Q) (G G_f : Graph Q) : Prop :=
  ReflTransGen (SchedStep M tie P fun _ => false) G G_f ∧ M.FullM P G_f

variable {G G' G₁ G₂ : Graph Q}

/-- A scheduler step keeps consistency (Lemma A.11 for the canonical choice). -/
theorem SchedStep.cons (hT : TieQ9 M tie) {stop : Ev Q → Bool} (h : SchedStep M tie P stop G G')
    (hG : M.cons G) : M.cons G' := by
  obtain ⟨e, -, -, hs⟩ := h
  exact hs.cons hT hG

/-- A run of scheduler steps keeps consistency. -/
theorem schedRun_cons (hT : TieQ9 M tie) {stop : Ev Q → Bool}
    (h : ReflTransGen (SchedStep M tie P stop) G G') (hG : M.cons G) : M.cons G' := by
  induction h with
  | refl => exact hG
  | tail _ hs ih => exact hs.cons hT ih

/-- Scheduler steps are deterministic on well-formed graphs. -/
theorem SchedStep.det {stop : Ev Q → Bool} (hG : G.Wf) (h₁ : SchedStep M tie P stop G G₁)
    (h₂ : SchedStep M tie P stop G G₂) : G₁ = G₂ := by
  obtain ⟨e, he, -, hs⟩ := h₁
  obtain ⟨e', he', -, hs'⟩ := h₂
  rw [he] at he'
  cases he'
  exact hs.det hG hs'

/-- A scheduler step exists exactly when `next_P` is some event not stopped at, on a consistent
graph (A.10). -/
theorem exists_schedStep (hT : TieQ9 M tie) {stop : Ev Q → Bool} (hG : M.cons G) {e : Ev Q}
    (hn : M.nextP P G = some e) (hs : stop e = false) : ∃ G', SchedStep M tie P stop G G' := by
  have he := Model.mem_availM_of_nextP hn
  obtain ⟨src, out, hc⟩ := Canon.exists hT hG he
  obtain ⟨t, -, ht, -⟩ := M.mem_availM_iff'.mp he
  have het : t = e.tid := by
    unfold Program.nextEv at ht
    obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.mp ht
    rfl
  exact ⟨_, e, hn, hs, het ▸ ht, src, out, hc, rfl⟩

/-- Two scheduler runs from the same consistent graph that both end where no scheduler step is
possible end at the same graph. -/
theorem schedRun_unique (hT : TieQ9 M tie) {stop : Ev Q → Bool}
    (h₁ : ReflTransGen (SchedStep M tie P stop) G G₁) (hG : M.cons G)
    (h₂ : ReflTransGen (SchedStep M tie P stop) G G₂)
    (ht₁ : ∀ X, ¬ SchedStep M tie P stop G₁ X) (ht₂ : ∀ X, ¬ SchedStep M tie P stop G₂ X) :
    G₁ = G₂ := by
  induction h₁ using ReflTransGen.head_induction_on generalizing G₂ with
  | refl =>
    rcases ReflTransGen.cases_head h₂ with h | ⟨X, hX, -⟩
    · exact h
    · exact absurd hX (ht₁ X)
  | head hs hr ih =>
    rename_i a b
    rcases ReflTransGen.cases_head h₂ with h | ⟨X, hX, hr₂⟩
    · subst h
      exact absurd hs (ht₂ _)
    · rw [hs.det (M.wf _ hG) hX] at ih
      exact ih (hX.cons hT hG) hr₂ ht₂

/-- A full graph has no scheduler step. -/
theorem not_schedStep_of_full {stop : Ev Q → Bool} (hf : M.FullM P G) (X : Graph Q) :
    ¬ SchedStep M tie P stop G X := by
  rintro ⟨e, he, -⟩
  rw [Model.nextP_eq_none_iff.mpr hf] at he
  cases he

/-- `completion_exists`: for a bounded program, every consistent execution completes to a full
graph by scheduler-following canonical steps, and the result is in `⟦P⟧`. -/
theorem completion_exists (hT : TieQ9 M tie) {n : ℕ} (hb : P.Bounded n) :
    ∀ (k : ℕ) (G : Graph Q), M.cons G → P.Exec G → P.threads.length * n - G.events.card = k →
      ∃ G_f, Completes M tie P G G_f ∧ M.Sem P G_f := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro G hG hE hk
    cases hn : M.nextP P G with
    | none =>
      have hf := Model.nextP_eq_none_iff.mp hn
      exact ⟨G, ⟨ReflTransGen.refl, hf⟩, M.wf _ hG, hE, hG, hf⟩
    | some e =>
      obtain ⟨G', hs⟩ := exists_schedStep (stop := fun _ => false) hT hG hn rfl
      obtain ⟨e', -, -, hcs⟩ := id hs
      have hG' := hcs.cons hT hG
      have hE' := hcs.exec (M.wf _ hG) hE
      have hcard : G'.events.card = G.events.card + 1 := by
        obtain ⟨hn', src, out, -, rfl⟩ := hcs
        rw [add_events]
        exact Finset.card_insert_of_notMem
          ((M.wf _ hG).not_mem_of_idx_eq_cnt (Model.idx_of_nextEv hn'))
      have hle := card_le_of_bounded (M.wf _ hG') hE' hb
      obtain ⟨G_f, ⟨h1, h2⟩, h3⟩ := ih _ (by omega) G' hG' hE' rfl
      exact ⟨G_f, ⟨ReflTransGen.head hs h1, h2⟩, h3⟩

/-- `completion_unique`: the full graph a consistent graph completes to is unique. -/
theorem completion_unique (hT : TieQ9 M tie) (hG : M.cons G) (h₁ : Completes M tie P G G₁)
    (h₂ : Completes M tie P G G₂) : G₁ = G₂ :=
  schedRun_unique hT h₁.1 hG h₂.1 (not_schedStep_of_full h₁.2) (not_schedStep_of_full h₂.2)

/-- `completion_congr` (plan row M5, for A.3 (a)): two configurations equal up to the insertion
order (`≈`, equal keys) whose graphs have `Supp` (every configuration with the invariant) and are
consistent complete to the same full graph. -/
theorem completion_congr (hT : TieQ9 M tie) {c c' : Config Q} (hS : c.G.Supp) (hS' : c'.G.Supp)
    (hA : c.Approx c') (hc : M.cons c.G) (h₁ : Completes M tie P c.G G₁)
    (h₂ : Completes M tie P c'.G G₂) : G₁ = G₂ := by
  rw [← (Config.approx_iff hS hS').mp hA] at h₂
  exact completion_unique hT hc h₁ h₂

/-- For two reachable configurations equal up to the insertion order of a bounded program, the
canonical completion exists and is the same full graph, a member of `⟦P⟧`. -/
theorem ReachM.completion_congr (hT : TieQ9 M tie) {n : ℕ} (hb : P.Bounded n) {c c' : Config Q}
    (h : ReachM M tie P c) (h' : ReachM M tie P c') (hA : c.Approx c') :
    ∃ G_f, Completes M tie P c.G G_f ∧ Completes M tie P c'.G G_f ∧ M.Sem P G_f := by
  obtain ⟨G_f, h1, h2⟩ := completion_exists hT hb _ c.G h.sound.cons h.sound.exec rfl
  have hG : c.G = c'.G := (Config.approx_iff h.sound.wf.supp h'.sound.wf.supp).mp hA
  exact ⟨G_f, h1, hG ▸ h1, h2⟩

/-! ### Scheduler steps are non-revisit steps (for M9) -/

/-- A scheduler step from the graph of a configuration with the invariant is a non-revisit step
of Algorithm 1 (`NrAdd`) with the canonical source and outcome. -/
theorem SchedStep.nrStep (hT : TieQ9 M tie) {stop : Ev Q → Bool} {c : Config Q}
    (hc : c.Inv M P) (h : SchedStep M tie P stop c.G G') :
    ∃ c', NrStep M P c c' ∧ c'.G = G' ∧ c'.Inv M P := by
  obtain ⟨e, hn, -, hs⟩ := h
  have hidx := hs.idx
  have hcons := hs.cons hT hc.cons
  obtain ⟨-, src, out, hcan, rfl⟩ := hs
  have hadd : NrAdd M P c.G e src out := by
    refine ⟨hn, ?_⟩
    rcases Lab.cases_lab e.lab with hR | hS | hN | hL
    · rcases hcan.adm hT hc.wf with ⟨_, h2, h3⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inr (Or.inl ⟨hR, h2, h3, hcons⟩)
      · exact absurd hR (Lab.IsND.not_isRecv h)
      · exact absurd hR h
    · obtain ⟨rfl, rfl⟩ := hcan.other (Lab.IsSend.not_isRecv hS) (Lab.IsSend.not_isND hS)
      exact Or.inr (Or.inr (Or.inl ⟨hS, rfl, rfl, hcons⟩))
    · obtain ⟨rfl, v, hv, rfl⟩ := hcan.nd hN
      obtain ⟨S, hSl⟩ := (Lab.isND_iff e.lab).mp hN
      have hset : e.ndSet = S := by simp [Ev.ndSet, hSl, Lab.ndSet]
      exact Or.inl ⟨S, v, hSl, hset ▸ minVal_mem hv, rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := hcan.other (Lab.IsLoc.not_isRecv hL) (Lab.IsLoc.not_isND hL)
      exact Or.inr (Or.inr (Or.inr ⟨hL, rfl, rfl⟩))
  obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hn
  exact ⟨c.add e src out, ⟨e, src, out, hadd, rfl⟩, rfl, hc.add ht hcons⟩

/-- A run of scheduler steps from the graph of a configuration with the invariant lifts to a run
of non-revisit steps (hence of `StepM` steps) of Algorithm 1. -/
theorem schedRun_nrSteps (hT : TieQ9 M tie) {stop : Ev Q → Bool} {c : Config Q}
    (hc : c.Inv M P) (h : ReflTransGen (SchedStep M tie P stop) c.G G') :
    ∃ c', ReflTransGen (NrStep M P) c c' ∧ c'.G = G' ∧ c'.Inv M P := by
  induction h with
  | refl => exact ⟨c, ReflTransGen.refl, rfl, hc⟩
  | tail _ hs ih =>
    obtain ⟨c₁, h1, rfl, hi⟩ := ih
    obtain ⟨c₂, h2, h3, h4⟩ := hs.nrStep hT hi
    exact ⟨c₂, h1.tail h2, h3, h4⟩

end Must

#print axioms Must.exists_nrAdd
#print axioms Must.card_le_of_bounded
#print axioms Must.Config.Inv.reaches_full
#print axioms Must.ReachM.reaches_full
#print axioms Must.ReachM.not_fruitless
#print axioms Must.SchedStep.det
#print axioms Must.exists_schedStep
#print axioms Must.schedRun_unique
#print axioms Must.completion_exists
#print axioms Must.completion_unique
#print axioms Must.completion_congr
#print axioms Must.ReachM.completion_congr
#print axioms Must.SchedStep.nrStep
#print axioms Must.schedRun_nrSteps
