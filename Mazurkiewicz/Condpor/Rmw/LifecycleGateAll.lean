import Mazurkiewicz.Condpor.Rmw.LifecycleGate3
import Mazurkiewicz.Condpor.Rmw.LifecycleGateClass
import Mazurkiewicz.Condpor.Rmw.LifecycleGate2Final

/-!
# The gate of LC2: all three clauses, and the corollaries

* **`gate : Gate1 ∧ Gate2 ∧ Gate3`**.
* **`graphs_eq`** / **`graphs_set_eq`** (from gate clauses 1 and 2): for a fragment program
  and an adequate bound, the graphs of the maximal runs of the machine are exactly the graphs
  (`abs`) of the terminal-valid full configurations of `lifeSys` (the hypotheses of `Gate2`,
  `Hyp`).
* `lifeClass_congr`: `lifeClass` depends only on `abs` for well-formed configurations; hence
  `cfg_iff` (per configuration), `exploration_not_run`.
* `explorer_termValid`, `hyp_graph_explored`: the explorer side.
* **`graphs_mequiv`** (from gate clauses 1 and 3): for maximal runs, same graph iff
  Mazurkiewicz-equivalent, and each such graph is terminal-valid.

The corollaries after `gate` were first written by the reviewer of LC2-b2 (scratch, not part of
the repository); they are moved here unchanged except for the statement forms.
-/

namespace Condpor

namespace Life

namespace Sem

open Targets

/-- **The gate of LC2.** -/
theorem gate : Gate1 ∧ Gate2 ∧ Gate3 := ⟨gate1, gate2, gate3⟩

/-- The hypotheses of `Gate2` on a configuration (terminal-valid full configuration of
`lifeSys`). -/
def Hyp (P : LProg) (n : ℕ) (c : Config) : Prop :=
  c.Wf ∧ (lifeSys P n).toProgram.Exec c.abs ∧
    ((Model.atomic (lifeSys P n) SC).sym EqSem.solver).cons c.abs ∧
    (lifeSys P n).toProgram.Full c.abs ∧ lifeClass P c ≠ .exploration

theorem MCls.toL_ne_exploration (m : MCls) : m.toL ≠ .exploration := by cases m <;> simp [MCls.toL]

/-- Corollary, existential form: graphs of maximal runs = graphs of configurations satisfying
the Gate2 hypotheses. -/
theorem graphs_eq (P : LProg) (n : ℕ) (hf : fragB P = true) (hn : adequateB P n = true)
    (G : Graph) :
    (∃ rs s, MaxRun P rs s ∧ (runCfg P rs s).abs = G) ↔ (∃ c, Hyp P n c ∧ c.abs = G) := by
  constructor
  · rintro ⟨rs, s, hr, rfl⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := gate1 P n hf hn rs s hr
    exact ⟨_, ⟨h1, h2, h3, h4, by rw [h5]; exact MCls.toL_ne_exploration _⟩, rfl⟩
  · rintro ⟨c, ⟨h1, h2, h3, h4, h5⟩, rfl⟩
    exact gate2 P n hf hn c h1 h2 h3 h4 h5

/-! lifeClass depends only on the graph, for well-formed configurations -/

theorem evAt_congr {c c' : Config} (hc : c.Wf) (hc' : c'.Wf) (h : c.abs = c'.abs) (t : Tid)
    (i : ℕ) :
    c.evAt t i = c'.evAt t i := by
  rw [Config.evAt_eq c hc, Config.evAt_eq c' hc', h]

theorem cnt_congr {c c' : Config} (hc : c.Wf) (hc' : c'.Wf) (h : c.abs = c'.abs) (t : Tid) :
    c.cnt t = c'.cnt t := by
  rw [Config.cnt_eq c hc, Config.cnt_eq c' hc', h]

theorem thEvents_congr {c c' : Config} (hc : c.Wf) (hc' : c'.Wf) (h : c.abs = c'.abs) (t : Tid) :
    thEvents c t = thEvents c' t := by
  unfold thEvents
  rw [cnt_congr hc hc' h]
  congr 1
  funext i
  exact evAt_congr hc hc' h t i

theorem lifeClass_congr {P : LProg} {c c' : Config} (hc : c.Wf) (hc' : c'.Wf) (h : c.abs = c'.abs) :
    lifeClass P c = lifeClass P c' := by
  have hrf : c.rf = c'.rf := congrArg Graph.rf h
  have hco : c.co = c'.co := congrArg Graph.co h
  have hcut : cutB P c = cutB P c' := by
    funext t; unfold cutB; rw [Config.trace_eq c hc, Config.trace_eq c' hc', h]
  have hw : waitOf P c = waitOf P c' := by
    funext t
    unfold waitOf kindOf finalB coMax
    rw [thEvents_congr hc hc' h, h, hrf, hco]
    simp only [evAt_congr hc hc' h]
  have herr : c.order.any (fun e => decide (e.act = .error)) =
      c'.order.any (fun e => decide (e.act = .error)) := by
    have hm : ∀ e, e ∈ c.order ↔ e ∈ c'.order := fun e => by
      have := congrArg (fun G => e ∈ G.events) h
      simpa [Config.abs] using this
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, hm]
  unfold lifeClass
  rw [hcut, hw, herr]

/-- Corollary, per configuration: a well-formed configuration has the graph of a maximal run
iff it satisfies the Gate2 hypotheses. -/
theorem cfg_iff (P : LProg) (n : ℕ) (hf : fragB P = true) (hn : adequateB P n = true)
    (c : Config) (hc : c.Wf) :
    (∃ rs s, MaxRun P rs s ∧ (runCfg P rs s).abs = c.abs) ↔ Hyp P n c := by
  constructor
  · rintro ⟨rs, s, hr, he⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := gate1 P n hf hn rs s hr
    refine ⟨hc, he ▸ h2, he ▸ h3, he ▸ h4, ?_⟩
    rw [← lifeClass_congr h1 hc he, h5]; exact MCls.toL_ne_exploration _
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact gate2 P n hf hn c h1 h2 h3 h4 h5

/-- tightness: an exploration-class well-formed configuration is never the graph of a maximal run -/
theorem exploration_not_run (P : LProg) (n : ℕ) (hf : fragB P = true) (hn : adequateB P n = true)
    (c : Config) (hc : c.Wf) (hx : lifeClass P c = .exploration) :
    ¬ ∃ rs s, MaxRun P rs s ∧ (runCfg P rs s).abs = c.abs := fun h =>
  ((cfg_iff P n hf hn c hc).mp h).2.2.2.2 hx

/-- every explorer configuration that is not exploration satisfies TermValid -/
theorem explorer_termValid {P : LProg} {n : ℕ} (hf : fragB P = true) (hn : adequateB P n = true)
    {c : Config} (hm : c ∈ exploreCfgAtF (lifeSys P n) n) (hx : lifeClass P c ≠ .exploration) :
    TermValid P n c := by
  obtain ⟨hr, hfu⟩ := Targets.mem_exploreCfgAtF _ n hm
  obtain ⟨hw, -, hcons, hE⟩ := hr.sound
  exact ⟨hf, hn, hw, hE, hcons, hfu, hx⟩

/-- Gate2's generality: any configuration with the hypotheses has a graph the explorer lists -/
theorem hyp_graph_explored {P : LProg} {n : ℕ} {c : Config} (h : Hyp P n c) :
    c.abs ∈ exploreAt (lifeSys P n) eqOracleSe n :=
  ((lifeSys_explore P n).2 c.abs).mpr ⟨h.1.1, h.2.1, h.2.2.1, h.2.2.2.1⟩


/-- **The graphs of the maximal runs are the terminal-valid full graphs**, as sets. -/
theorem graphs_set_eq (P : LProg) (n : ℕ) (hf : fragB P = true) (hn : adequateB P n = true) :
    {G : Graph | ∃ rs s, MaxRun P rs s ∧ (runCfg P rs s).abs = G} =
      {G : Graph | ∃ c, Hyp P n c ∧ c.abs = G} :=
  Set.ext (graphs_eq P n hf hn)

/-- **Maximal runs, graphs and traces**: for maximal runs, the same graph iff
Mazurkiewicz-equivalent; and the graph of each is a terminal-valid full graph of `lifeSys`. -/
theorem graphs_mequiv (P : LProg) (n : ℕ) (hf : fragB P = true) (hn : adequateB P n = true)
    {rs₁ rs₂ : List Occ} {s₁ s₂ : MState} (h₁ : MaxRun P rs₁ s₁) (h₂ : MaxRun P rs₂ s₂) :
    ((runCfg P rs₁ s₁).abs = (runCfg P rs₂ s₂).abs ↔ MEquiv rs₁ rs₂) ∧
      ∃ c, Hyp P n c ∧ c.abs = (runCfg P rs₁ s₁).abs :=
  ⟨gate3 P hf rs₁ s₁ rs₂ s₂ h₁ h₂, (graphs_eq P n hf hn _).mp ⟨rs₁, s₁, h₁, rfl⟩⟩

end Sem

end Life

end Condpor
