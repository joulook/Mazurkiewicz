import Mazurkiewicz.Must.PrefixNext
import Mazurkiewicz.Must.Extend

/-!
# Algorithm 2 (`ProductionSequence`, `GetNext`) as a relation (milestone M7)

Paper: Appendix A.6, Definition A.5 (`MaxCompletion(G, A)`), Algorithm 2 (p. 31). Plan:
`plan/must/lean/LEAN-PLAN.md`, Section 2b (`GetNext`), fate rows "Algorithm 2" and A.16, the
addendum after the M6 review.

* `StepSeq M tie P c S c'`: `S` is a sequence of algorithmic steps (`StepM`) from `c`, given by
  the list of the configurations it visits; `c'` is the last one.
* `maxCompletion tie P G A` (Definition A.5, Q10 (i)): the graph reached from `G` by the canonical
  replay of `A` (M5's `Replay`), if it exists and is unique; `none` is `⊥`. On a consistent `G`
  it is exactly the replay (`maxCompletion_eq_some_iff`); `G ⊑ MaxCompletion(G, A)`
  (`maxCompletion_pfx`), consistency, `maxCompletion_snoc` (a list extended by an event that is
  available after the replay of the list stays legal), `Replay.events`.
* `GetNext M tie P t S c'` (Algorithm 2, repaired): one relation over tasks `t`. A task
  `call c Gt` is `GetNext(G_s, G_t)` with `G_s = c.G` and the insertion order of `c`; a task
  `loop Gp s₀ c A` is the loop of lines 15–21 with `G = c.G`, `G_p = Gp` and the deferred list
  `A`. The output is the list `S` of configurations visited (line 23's `S ++ [s₀@− ⇒rv r₀]`) and
  the last configuration.
  - `case1`: line 9, the printed test `∃ t = next_P(G_s)@p. G_s →t G' ∧ G' ⊑ G_t`, with the
    printed (unpremised) operational step `OpAdd₀`;
  - `case2`: lines 10–14, 22–23, with `s₀ := G_t.rf(r₀)` (repaired line 12) and `G_p :=
    PrefixExtension(G_s, G_t, s₀)`; the result is the revisit successor (Q15) of the loop's last
    configuration with `s₀` added: its graph is `G_n` (`GetNextRev.lean`);
  - `brk`, `good`, `defer`: lines 15–21; `LoopTest` is the test of line 16.
  There is no constructor for a loop whose `next_P` is `⊥` and none for a `MaxCompletion` that is
  `⊥`: on the domain neither occurs (`CompleteM.lean`).
* `GetNext.det`: the relation is functional (no hypothesis).
* `ProdSeq M tie P Gf c S c'` (lines 1–7): iterate `GetNext(G, G_f)` while `G ≠ G_f`.
* General facts used later: `opAdd_nrAdd` (an operational step adding `next_P` is a non-revisit
  step of Algorithm 1), `exists_avail_of_sPfx` (`G ⊏ F` has an available event of `F`), list
  facts on positions.

Every definition and result holds for every model `M`; `TieQ9 M tie` is a hypothesis where
stated.
-/

namespace Must

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q} {tie : Tie Q}

/-! ### Sequences of algorithmic steps -/

/-- `S` is a sequence of algorithmic steps from `c` (the configurations visited); `c'` is the
last configuration, `c` for the empty sequence. -/
inductive StepSeq (M : Model Q) (tie : Tie Q) (P : Program Q) :
    Config Q → List (Config Q) → Config Q → Prop
  /-- no step -/
  | nil (c : Config Q) : StepSeq M tie P c [] c
  /-- a step, then a sequence -/
  | cons {c d c' : Config Q} {S : List (Config Q)} :
      StepM M tie P c d → StepSeq M tie P d S c' → StepSeq M tie P c (d :: S) c'

namespace StepSeq

variable {c c₁ c₂ d : Config Q} {S S₁ S₂ : List (Config Q)}

theorem append (h₁ : StepSeq M tie P c S₁ c₁) (h₂ : StepSeq M tie P c₁ S₂ c₂) :
    StepSeq M tie P c (S₁ ++ S₂) c₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons hs _ ih => exact .cons hs (ih h₂)

theorem single (h : StepM M tie P c d) : StepSeq M tie P c [d] d := .cons h (.nil d)

theorem reflTransGen (h : StepSeq M tie P c S c₁) : ReflTransGen (StepM M tie P) c c₁ := by
  induction h with
  | nil => exact .refl
  | cons hs _ ih => exact .head hs ih

/-- Every configuration of a sequence of algorithmic steps from a configuration with the
invariant has the invariant. -/
theorem inv (h : StepSeq M tie P c S c₁) (hc : c.Inv M P) :
    c₁.Inv M P ∧ ∀ d ∈ S, d.Inv M P := by
  induction h with
  | nil => exact ⟨hc, fun _ h => absurd h List.not_mem_nil⟩
  | cons hs _ ih =>
    obtain ⟨h1, h2⟩ := ih (hs.inv hc)
    refine ⟨h1, fun d hd => ?_⟩
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hs.inv hc
    · exact h2 d hd

/-- A sequence of algorithmic steps from a reachable configuration ends in a reachable one. -/
theorem reachM (h : StepSeq M tie P c S c₁) (hc : ReachM M tie P c) : ReachM M tie P c₁ :=
  hc.trans h.reflTransGen

end StepSeq

/-! ### `MaxCompletion` (Definition A.5) -/

/-- `MaxCompletion(G, A)` (Definition A.5, Q10 (i)): "the execution `G'` such that
`G ⇝^{A₁} ⋯ ⇝^{A_N} G'`, if such an execution exists", read as the graph reached from `G` by the
canonical replay of the list `A` when there is exactly one; `none` is `⊥`. -/
noncomputable def maxCompletion (tie : Tie Q) (P : Program Q) (G : Graph Q) (A : List (Ev Q)) :
    Option (Graph Q) :=
  haveI := Classical.propDecidable (∃! X, Replay tie P G A X)
  if h : ∃! X, Replay tie P G A X then some h.exists.choose else none

variable {G X Y : Graph Q} {A : List (Ev Q)} {e : Ev Q}

omit [Membership Val Q] in
/-- `MaxCompletion(G, A)` is a canonical replay of `A`. -/
theorem maxCompletion_replay (h : maxCompletion tie P G A = some X) : Replay tie P G A X := by
  unfold maxCompletion at h
  split at h
  · next hu =>
    cases h
    exact hu.exists.choose_spec
  · cases h

omit [Membership Val Q] in
/-- A unique canonical replay is `MaxCompletion`. -/
theorem maxCompletion_of_unique (hu : ∃! X, Replay tie P G A X) (h : Replay tie P G A X) :
    maxCompletion tie P G A = some X := by
  unfold maxCompletion
  split
  · next hu' => exact congrArg some (hu'.unique hu'.exists.choose_spec h)
  · next hn => exact absurd hu hn

/-- On a consistent graph, `MaxCompletion(G, A) = X` iff `X` is the canonical replay of `A`. -/
theorem maxCompletion_eq_some_iff (hT : TieQ9 M tie) (hG : M.cons G) :
    maxCompletion tie P G A = some X ↔ Replay tie P G A X :=
  ⟨maxCompletion_replay, fun h =>
    maxCompletion_of_unique ⟨X, h, fun _ hZ => replay_det hT hG hZ h⟩ h⟩

omit [Membership Val Q] in
/-- `MaxCompletion(G, []) = G`. -/
theorem maxCompletion_nil : maxCompletion tie P G [] = some G :=
  maxCompletion_of_unique ⟨G, .nil G, fun _ hY => by cases hY; rfl⟩ (.nil G)

omit [Membership Val Q] in
/-- Canonical replay of a list extended by one event. -/
theorem Replay.snoc (h : Replay tie P G A X) (hs : CanonStep tie P X e Y) :
    Replay tie P G (A ++ [e]) Y := by
  induction h with
  | nil => exact .cons hs (.nil _)
  | cons h₁ _ ih => exact .cons h₁ (ih hs)

omit [Membership Val Q] in
/-- The events of a canonical replay: the events of the start and the listed events. -/
theorem Replay.events (h : Replay tie P G A X) : X.events = G.events ∪ A.toFinset := by
  induction h with
  | nil => simp
  | cons hs _ ih =>
    obtain ⟨-, src, out, -, rfl⟩ := hs
    rw [ih, add_events, List.toFinset_cons]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto

/-- A canonical step from a consistent execution is a step of `⊑`. -/
theorem CanonStep.pfx (hT : TieQ9 M tie) (hG : M.cons G) (hE : P.Exec G)
    (h : CanonStep tie P G e X) : Pfx M P G X := by
  have hc := h.cons hT hG
  have hx := h.exec (M.wf _ hG) hE
  obtain ⟨src, out, hop, -, rfl⟩ := (canonStep_iff_maxStep₀ hT hG hE).mp h
  exact pfx_iff_opLe₀.mpr ⟨hG, hc, hx, ReflTransGen.single ⟨e, src, out, hop, rfl⟩⟩

/-- Canonical replay from a consistent execution gives a consistent execution above it:
`G ⊑ MaxCompletion(G, A)`. -/
theorem Replay.pfx (hT : TieQ9 M tie) (hG : M.cons G) (hE : P.Exec G)
    (h : Replay tie P G A X) : Pfx M P G X := by
  induction h with
  | nil => exact Pfx.refl hG hE
  | cons hs _ ih =>
    have h1 := hs.pfx hT hG hE
    exact h1.trans (ih h1.cons' h1.exec')

/-- `G_p ⊑ MaxCompletion(G_p, A)` (the A.16 invariant LI2's graph is above `G_p`); in particular
`MaxCompletion(G_p, A)` is a consistent execution. -/
theorem maxCompletion_pfx (hT : TieQ9 M tie) (hG : M.cons G) (hE : P.Exec G)
    (h : maxCompletion tie P G A = some X) : Pfx M P G X :=
  (maxCompletion_replay h).pfx hT hG hE

/-- Legality of the evolving deferred list (A.16 ⟨6⟩2): if `MaxCompletion(G, A) = X` and `e` is
available in `X`, then `MaxCompletion(G, A ++ [e])` is `X` with `e` added canonically. -/
theorem maxCompletion_snoc (hT : TieQ9 M tie) (hG : M.cons G) (hE : P.Exec G)
    (h : maxCompletion tie P G A = some X) (he : e ∈ M.availM P X) :
    ∃ Y, maxCompletion tie P G (A ++ [e]) = some Y ∧ CanonStep tie P X e Y ∧ Pfx M P X Y := by
  have hX := maxCompletion_pfx hT hG hE h
  obtain ⟨src, out, hc⟩ := Canon.exists hT hX.cons' he
  have hs : CanonStep tie P X e (X.add e src out) := ⟨nextEv_of_mem_availM he, src, out, hc, rfl⟩
  refine ⟨_, (maxCompletion_eq_some_iff hT hG).mpr ((maxCompletion_replay h).snoc hs), hs,
    hs.pfx hT hX.cons' hX.exec'⟩

/-! ### Algorithm 2 -/

/-- The tasks of Algorithm 2: a call `GetNext(G_s, G_t)` from a configuration, or the loop of
lines 15–21 (with `G_p`, `s₀`, the current configuration and the deferred list `A`). -/
inductive Task (Q : Type)
  /-- `GetNext(c.G, Gt)` from the configuration `c` -/
  | call (c : Config Q) (Gt : Graph Q)
  /-- the loop of lines 15–21 at `G = c.G` with `G_p`, `s₀`, and `A` -/
  | loop (Gp : Graph Q) (s₀ : Ev Q) (c : Config Q) (A : List (Ev Q))

/-- The test of line 16: `availPrefix(G, e) ⊑ G_p ∧ e ∈ G_p.E ∪ {s₀}`. -/
def LoopTest (M : Model Q) (P : Program Q) (Gp : Graph Q) (s₀ : Ev Q) (G : Graph Q) (e : Ev Q) :
    Prop :=
  Pfx M P (availPrefix G e) Gp ∧ (e ∈ Gp.events ∨ e = s₀)

/-- Algorithm 2's `GetNext` (p. 31), repaired (plan, fate rows "Algorithm 2" and A.16), as a
relation over tasks; see the module docstring. -/
inductive GetNext (M : Model Q) (tie : Tie Q) (P : Program Q) :
    Task Q → List (Config Q) → Config Q → Prop
  /-- line 9: an operational step adding `next_P(G_s)` stays below `G_t` -/
  | case1 {c : Config Q} {Gt : Graph Q} {e : Ev Q} {src : Option (Src Q)} {out : Option Val} :
      M.nextP P c.G = some e → OpAdd₀ M P c.G e src out → Pfx M P (c.G.add e src out) Gt →
      GetNext M tie P (.call c Gt) [c.add e src out] (c.add e src out)
  /-- lines 10–14, 22–23: `r₀ = next_P(G_s)`, `s₀ = G_t.rf(r₀)`, the loop from `G_s` with
  `G_p = PrefixExtension(G_s, G_t, s₀)` and `A = []`, then the revisit of `r₀` by `s₀` -/
  | case2 {c : Config Q} {Gt : Graph Q} {r₀ s₀ : Ev Q} {S : List (Config Q)} {c₁ : Config Q} :
      M.nextP P c.G = some r₀ →
      (¬ ∃ src out, OpAdd₀ M P c.G r₀ src out ∧ Pfx M P (c.G.add r₀ src out) Gt) →
      Gt.rf r₀ = some (.snd s₀) →
      GetNext M tie P (.loop (prefixExt c.G Gt s₀) s₀ c []) S c₁ →
      GetNext M tie P (.call c Gt) (S ++ [(c₁.add s₀ none none).revisitCfg r₀ s₀])
        ((c₁.add s₀ none none).revisitCfg r₀ s₀)
  /-- line 17: `e = s₀` passes the test of line 16: break -/
  | brk {Gp : Graph Q} {s₀ : Ev Q} {c : Config Q} {A : List (Ev Q)} :
      M.nextP P c.G = some s₀ → LoopTest M P Gp s₀ c.G s₀ →
      GetNext M tie P (.loop Gp s₀ c A) [] c
  /-- lines 16, 20, 21: `e ≠ s₀` passes the test; `GetNext(G, MaxCompletion(G_p, A))` -/
  | good {Gp : Graph Q} {s₀ : Ev Q} {c : Config Q} {A : List (Ev Q)} {e : Ev Q} {X : Graph Q}
      {S₁ : List (Config Q)} {c₁ : Config Q} {S₂ : List (Config Q)} {c₂ : Config Q} :
      M.nextP P c.G = some e → e ≠ s₀ → LoopTest M P Gp s₀ c.G e →
      maxCompletion tie P Gp A = some X →
      GetNext M tie P (.call c X) S₁ c₁ → GetNext M tie P (.loop Gp s₀ c₁ A) S₂ c₂ →
      GetNext M tie P (.loop Gp s₀ c A) (S₁ ++ S₂) c₂
  /-- lines 18–21: `e` fails the test: `A ← A ++ e`; `GetNext(G, MaxCompletion(G_p, A))` -/
  | defer {Gp : Graph Q} {s₀ : Ev Q} {c : Config Q} {A : List (Ev Q)} {e : Ev Q} {X : Graph Q}
      {S₁ : List (Config Q)} {c₁ : Config Q} {S₂ : List (Config Q)} {c₂ : Config Q} :
      M.nextP P c.G = some e → ¬ LoopTest M P Gp s₀ c.G e →
      maxCompletion tie P Gp (A ++ [e]) = some X →
      GetNext M tie P (.call c X) S₁ c₁ → GetNext M tie P (.loop Gp s₀ c₁ (A ++ [e])) S₂ c₂ →
      GetNext M tie P (.loop Gp s₀ c A) (S₁ ++ S₂) c₂

/-- `GetNext` is functional: a task has at most one result (no hypothesis). -/
theorem GetNext.det {t : Task Q} {S₁ S₂ : List (Config Q)} {c₁ c₂ : Config Q}
    (h₁ : GetNext M tie P t S₁ c₁) (h₂ : GetNext M tie P t S₂ c₂) : S₁ = S₂ ∧ c₁ = c₂ := by
  induction h₁ generalizing S₂ c₂ with
  | case1 hn hop hpf =>
    cases h₂ with
    | case1 hn' _ hpf' =>
      rw [hn] at hn'
      cases hn'
      obtain ⟨rfl, rfl⟩ := case1_unique hpf
      obtain ⟨rfl, rfl⟩ := case1_unique hpf'
      exact ⟨rfl, rfl⟩
    | case2 hn' hnt _ _ =>
      rw [hn] at hn'
      cases hn'
      exact absurd ⟨_, _, hop, hpf⟩ hnt
  | case2 hn hnt hs _ ih =>
    cases h₂ with
    | case1 hn' hop hpf =>
      rw [hn] at hn'
      cases hn'
      exact absurd ⟨_, _, hop, hpf⟩ hnt
    | case2 hn' _ hs' hl' =>
      rw [hn] at hn'
      cases hn'
      rw [hs] at hs'
      cases hs'
      obtain ⟨rfl, rfl⟩ := ih hl'
      exact ⟨rfl, rfl⟩
  | brk hn ht =>
    cases h₂ with
    | brk => exact ⟨rfl, rfl⟩
    | good hn' hne =>
      rw [hn] at hn'
      cases hn'
      exact absurd rfl hne
    | defer hn' hnt =>
      rw [hn] at hn'
      cases hn'
      exact absurd ht hnt
  | good hn hne ht hX _ _ ih₁ ih₂ =>
    cases h₂ with
    | brk hn' =>
      rw [hn] at hn'
      cases hn'
      exact absurd rfl hne
    | good hn' _ _ hX' h₁' h₂' =>
      rw [hn] at hn'
      cases hn'
      rw [hX] at hX'
      cases hX'
      obtain ⟨rfl, rfl⟩ := ih₁ h₁'
      obtain ⟨rfl, rfl⟩ := ih₂ h₂'
      exact ⟨rfl, rfl⟩
    | defer hn' hnt =>
      rw [hn] at hn'
      cases hn'
      exact absurd ht hnt
  | defer hn hnt hX _ _ ih₁ ih₂ =>
    cases h₂ with
    | brk hn' ht =>
      rw [hn] at hn'
      cases hn'
      exact absurd ht hnt
    | good hn' _ ht =>
      rw [hn] at hn'
      cases hn'
      exact absurd ht hnt
    | defer hn' _ hX' h₁' h₂' =>
      rw [hn] at hn'
      cases hn'
      rw [hX] at hX'
      cases hX'
      obtain ⟨rfl, rfl⟩ := ih₁ h₁'
      obtain ⟨rfl, rfl⟩ := ih₂ h₂'
      exact ⟨rfl, rfl⟩

/-- `ProductionSequence(G_f)` (Algorithm 2, lines 1–7) from a configuration: while `G ≠ G_f`,
`⟨G, S'⟩ ← GetNext(G, G_f)`, `S ← S ++ S'`. -/
inductive ProdSeq (M : Model Q) (tie : Tie Q) (P : Program Q) (Gf : Graph Q) :
    Config Q → List (Config Q) → Config Q → Prop
  /-- line 4: `G = G_f` -/
  | done {c : Config Q} : c.G = Gf → ProdSeq M tie P Gf c [] c
  /-- lines 5, 6 -/
  | step {c : Config Q} {S₁ : List (Config Q)} {c₁ : Config Q} {S₂ : List (Config Q)}
      {c₂ : Config Q} :
      c.G ≠ Gf → GetNext M tie P (.call c Gf) S₁ c₁ → ProdSeq M tie P Gf c₁ S₂ c₂ →
      ProdSeq M tie P Gf c (S₁ ++ S₂) c₂

/-- `ProductionSequence` is functional. -/
theorem ProdSeq.det {Gf : Graph Q} {c : Config Q} {S₁ S₂ : List (Config Q)} {c₁ c₂ : Config Q}
    (h₁ : ProdSeq M tie P Gf c S₁ c₁) (h₂ : ProdSeq M tie P Gf c S₂ c₂) :
    S₁ = S₂ ∧ c₁ = c₂ := by
  induction h₁ generalizing S₂ c₂ with
  | done h =>
    cases h₂ with
    | done => exact ⟨rfl, rfl⟩
    | step hne => exact absurd h hne
  | step hne hg _ ih =>
    cases h₂ with
    | done h => exact absurd h hne
    | step _ hg' hp' =>
      obtain ⟨rfl, rfl⟩ := hg.det hg'
      obtain ⟨rfl, rfl⟩ := ih hp'
      exact ⟨rfl, rfl⟩

/-! ### General facts -/

/-- An operational step adding `next_P(G)` is a non-revisit step of Algorithm 1. -/
theorem opAdd_nrAdd {src : Option (Src Q)} {out : Option Val} (hn : M.nextP P G = some e)
    (h : OpAdd M P G e src out) : NrAdd M P G e src out := by
  obtain ⟨-, hadm, hc⟩ := h
  refine ⟨hn, ?_⟩
  rcases hadm with ⟨hR, rfl, hsrc⟩ | ⟨hN, rfl, v, hv, rfl⟩ | ⟨hR, hN, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨hR, rfl, hsrc, hc⟩)
  · obtain ⟨S, hS⟩ := (Lab.isND_iff e.lab).mp hN
    refine Or.inl ⟨S, v, hS, ?_, rfl, rfl⟩
    simpa [Ev.ndSet, hS, Lab.ndSet] using hv
  · rcases Lab.cases_lab e.lab with h | h | h | h
    · exact absurd h hR
    · exact Or.inr (Or.inr (Or.inl ⟨h, rfl, rfl, hc⟩))
    · exact absurd h hN
    · exact Or.inr (Or.inr (Or.inr ⟨h, rfl, rfl⟩))

/-- A graph with an available event has a next event. -/
theorem nextP_isSome_of_mem {y : Ev Q} (h : y ∈ M.availM P G) : ∃ e, M.nextP P G = some e := by
  unfold Model.nextP
  cases hl : M.availM P G with
  | nil => rw [hl] at h; exact absurd h List.not_mem_nil
  | cons a l => exact ⟨a, rfl⟩

/-- `G ⊏ F` has an available event that is an event of `F` (a `porf`-minimal event of `F` not
in `G`). -/
theorem exists_avail_of_sPfx {F : Graph Q} (h : SPfx M P G F) :
    ∃ y ∈ F.events, y ∉ G.events ∧ y ∈ M.availM P G := by
  have hp := h.1
  have hF := hp.wf'
  obtain ⟨-, x, hxF, hxG⟩ := sPfx_iff_exists.mp h
  obtain ⟨y, hyU, hmin⟩ := exists_min_of_strict (F.events \ G.events) (fun a b => F.porf a b)
    (fun a _ => hF.porf_irrefl a) (fun _ _ _ _ _ _ h1 h2 => porf_trans h1 h2)
    ⟨x, Finset.mem_sdiff.mpr ⟨hxF, hxG⟩⟩
  obtain ⟨hyF, hyG⟩ := Finset.mem_sdiff.mp hyU
  have hpre : ∀ a, F.porf a y → a ∈ G.events := fun a ha => by
    by_contra haG
    exact hmin a (Finset.mem_sdiff.mpr ⟨(hF.mem_of_porf ha).1, haG⟩) ha
  have hn : P.nextEv G y.tid = some y := by
    rw [hp.eq_restrict]
    refine nextEv_restrict hF hp.exec' hyF hyG (fun a ha => hpre a (TransGen.single (Or.inl ha)))
      (fun b hb hpo => hyG ?_)
    have := (closed_iff_porf F G.events).mp hp.closed (TransGen.single (Or.inl hpo))
      (Finset.mem_inter.mpr ⟨hpo.2.1, hb⟩)
    exact (Finset.mem_inter.mp this).2
  have hn' : P.nextEv G y.tid = some y := hn
  exact ⟨y, hyF, hyG, (hp.step_of_next hyF hn' fun a ha => hpre a (TransGen.single ha)).1.1⟩

/-! ### Positions in an insertion order -/

/-- In a duplicate-free list `p ++ [r] ++ q`, an element `x` lies after `r` iff it is neither in
`p` nor `r`. -/
theorem idxOf_lt_iff_of_prefix {α : Type} [DecidableEq α] {l p : List α} {r x : α}
    (hnd : l.Nodup) (hp : p ++ [r] <+: l) (hx : x ∈ l) :
    l.idxOf r < l.idxOf x ↔ x ∉ p ∧ x ≠ r := by
  obtain ⟨q, rfl⟩ := hp
  have hnd' := hnd
  rw [List.append_assoc, List.nodup_append] at hnd'
  have hrp : r ∉ p := fun h => hnd'.2.2 r h r (by simp) rfl
  have hr : (p ++ [r] ++ q).idxOf r = p.length := by
    rw [List.append_assoc, List.idxOf_append_of_notMem hrp, List.singleton_append,
      List.idxOf_cons_self, Nat.add_zero]
  rw [hr]
  by_cases hxp : x ∈ p
  · rw [List.append_assoc, List.idxOf_append_of_mem hxp]
    have := List.idxOf_lt_length_of_mem hxp
    simp only [hxp, not_true_eq_false, false_and, iff_false, not_lt]
    exact this.le
  · rw [List.append_assoc, List.idxOf_append_of_notMem hxp]
    by_cases hxr : x = r
    · subst hxr
      simp
    · simp only [hxp, not_false_eq_true, ne_eq, hxr, and_self, iff_true]
      rw [List.singleton_append, List.idxOf_cons_ne _ (Ne.symm hxr)]
      omega

end Must

#print axioms Must.StepSeq.append
#print axioms Must.StepSeq.inv
#print axioms Must.maxCompletion_replay
#print axioms Must.maxCompletion_of_unique
#print axioms Must.maxCompletion_eq_some_iff
#print axioms Must.maxCompletion_nil
#print axioms Must.Replay.snoc
#print axioms Must.Replay.events
#print axioms Must.CanonStep.pfx
#print axioms Must.Replay.pfx
#print axioms Must.maxCompletion_pfx
#print axioms Must.maxCompletion_snoc
#print axioms Must.GetNext.det
#print axioms Must.ProdSeq.det
#print axioms Must.opAdd_nrAdd
#print axioms Must.nextP_isSome_of_mem
#print axioms Must.exists_avail_of_sPfx
#print axioms Must.idxOf_lt_iff_of_prefix
