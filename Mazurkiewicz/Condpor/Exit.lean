import Mazurkiewicz.Condpor.Optimal

/-!
# No wasted exploration, and the exit at an erroneous graph

* Theorem 5(b) of the paper: the algorithm never visits a graph that cannot
  lead to a full execution. `Reach.reaches_full`: from every reached
  configuration of a bounded program the algorithm reaches a full one, by
  non-revisit steps (`Reach.exists_step`: a read reads from the last write, a
  write goes last, a constraint evaluation gets a satisfiable outcome).
* Algorithm 1 exits at the first erroneous graph. The relation `Reach` has no
  such exit; Theorems 4 and 5 are about `Reach`. `ReachX` is the relation in
  which no step starts from an erroneous configuration (it may end in one).
  `ErrPred` is an error predicate that is monotone on prefixes, as the paper
  assumes; `ErrPred.label`: the graph has an `error` event.
  - `reachX_of_reach`: if no configuration of `ReachX` is erroneous, then
    `ReachX = Reach`: without an error the exit changes nothing.
  - `exists_reachX_err`: if some consistent execution of the program is
    erroneous, `ReachX` contains an erroneous configuration: the algorithm
    with exit finds an error.
-/

namespace Condpor

open Program

variable {P : Program} {M : Model} {S : Solver} {τ : TieBreak S}

/-! ### Theorem 5(b) -/

/-- From a reached configuration that is not full the algorithm takes a
non-revisit step. -/
theorem Reach.exists_step (hM : M.Extensible) {c : Config} (hc : Reach P (M.sym S) τ c)
    (hnf : ¬ P.Full c.abs) : ∃ e c', StepL P (M.sym S) τ c e .nr c' := by
  obtain ⟨hw, -, hcc, -⟩ := hc.sound
  obtain ⟨a, ha, -⟩ := exists_unique_isNext hnf
  have hidx := idx_eq_of_mem_avail ha.1
  rcases a.act.isRead_or_isWrite_or_isLocal with hk | hk | hk
  · have hact := TEv.IsRead.exists_act hk
    refine ⟨a, _, StepL.read hcc ha hact (Graph.maxWrite_isWriteTo hw.1 _) ?_⟩
    rw [Config.addRead_abs]
    exact Model.sym_ext_read hM hw.1 hcc hidx hact
  · refine ⟨a, _, StepL.write hcc ha hk (Graph.maxWrite_isWriteTo hw.1 _) ?_⟩
    rw [Config.addWrite_abs]
    exact Model.sym_ext_write hM hw.1 hcc hidx hk
  · by_cases hcs : a.IsCons
    · obtain ⟨φ, hφ⟩ := TEv.IsCons.exists_act hcs
      obtain ⟨b, hb⟩ := Model.sym_ext_cons hM hw.1 hcc hidx hφ
      exact ⟨a, _, StepL.sym (b := b) hcc ha hcs (by rw [Config.addLoc_abs]; exact hb)⟩
    · exact ⟨a, _, StepL.loc hcc ha hk hcs (by
        rw [Config.addLoc_abs]
        exact Model.sym_ext_loc_none hM hw.1 hcc hidx hk hcs)⟩

/-- A non-revisit step adds one event. -/
theorem StepL.card_nr {M : Model} {c c' : Config} {e : TEv} (hc : c.Wf)
    (h : StepL P M τ c e .nr c') : c'.abs.events.card = c.abs.events.card + 1 := by
  have N := h.nrFacts hc
  change c'.order.toFinset.card = c.order.toFinset.card + 1
  rw [N.order, List.toFinset_cons, Finset.card_insert_of_notMem]
  exact fun hm => N.fresh (List.mem_toFinset.mp hm)

/-- Theorem 5(b): every reached configuration of a bounded program reaches a
full one. -/
theorem Reach.reaches_full {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible) {c : Config}
    (hc : Reach P (M.sym S) τ c) :
    ∃ c', Relation.ReflTransGen (Step P (M.sym S) τ) c c' ∧ P.Full c'.abs := by
  have key : ∀ k (c : Config), Reach P (M.sym S) τ c →
      n * P.threads.length - c.abs.events.card ≤ k →
      ∃ c', Relation.ReflTransGen (Step P (M.sym S) τ) c c' ∧ P.Full c'.abs := by
    intro k
    induction k with
    | zero =>
      intro c hc hk
      by_cases hf : P.Full c.abs
      · exact ⟨c, .refl, hf⟩
      · obtain ⟨e, c1, hs⟩ := hc.exists_step hM hf
        have hc1 : Reach P (M.sym S) τ c1 := Relation.ReflTransGen.tail hc ⟨e, .nr, hs⟩
        obtain ⟨hw1, -, -, hE1⟩ := hc1.sound
        have h1 := hE1.card_le hw1.1 hn
        have h2 := hs.card_nr hc.sound.1
        omega
    | succ k ih =>
      intro c hc hk
      by_cases hf : P.Full c.abs
      · exact ⟨c, .refl, hf⟩
      · obtain ⟨e, c1, hs⟩ := hc.exists_step hM hf
        have hc1 : Reach P (M.sym S) τ c1 := Relation.ReflTransGen.tail hc ⟨e, .nr, hs⟩
        have h2 := hs.card_nr hc.sound.1
        obtain ⟨c', hc', hf'⟩ := ih c1 hc1 (by omega)
        exact ⟨c', Relation.ReflTransGen.head ⟨e, .nr, hs⟩ hc', hf'⟩
  exact key _ c hc (Nat.le_refl _)

/-! ### Prefixes and full extensions -/

/-- A prefix of a prefix is a prefix. -/
theorem Graph.IsPrefixOf.trans {G₁ G₂ G₃ : Graph} (h₁₂ : G₁.IsPrefixOf G₂)
    (h₂₃ : G₂.IsPrefixOf G₃) : G₁.IsPrefixOf G₃ := by
  obtain ⟨s₁, hs₁, rfl⟩ := h₁₂
  obtain ⟨s₂, hs₂, rfl⟩ := h₂₃
  refine ⟨s₂ ∩ s₁, ?_, G₃.restrict_restrict s₂ s₁⟩
  intro a b hab hb
  have hb' : b ∈ Graph.evSet (G₃.events ∩ s₂) := by
    cases b with
    | init => trivial
    | th q =>
      have hq : q ∈ G₃.events ∩ (s₂ ∩ s₁) := hb
      simp only [Finset.mem_inter] at hq
      exact Finset.mem_inter.mpr ⟨hq.1, hq.2.1⟩
  have hb1 : b ∈ Graph.evSet ((G₃.restrict s₂).events ∩ s₁) := by
    cases b with
    | init => trivial
    | th q =>
      have hq : q ∈ G₃.events ∩ (s₂ ∩ s₁) := hb
      simp only [Finset.mem_inter] at hq
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hq.1, hq.2.1⟩, hq.2.2⟩
  have h2 : (G₃.restrict s₂).porf a b :=
    (Graph.porf_restrict_iff hs₂ hb').mpr (Relation.TransGen.single hab)
  have ha := hs₁.transGen h2 hb1
  cases a with
  | init => trivial
  | th q =>
    have hq : q ∈ (G₃.restrict s₂).events ∩ s₁ := ha
    simp only [Graph.restrict_events, Finset.mem_inter] at hq
    exact Finset.mem_inter.mpr ⟨hq.1.1, Finset.mem_inter.mpr ⟨hq.1.2, hq.2⟩⟩

/-- A consistent execution that is not full has a consistent extension by its
next event, of which it is a prefix. -/
theorem exists_ext (hM : M.Extensible) {G : Graph} (hG : G.Wf) (hE : P.Exec G)
    (hc : (M.sym S).cons G) (hnf : ¬ P.Full G) :
    ∃ G1 : Graph, G1.Wf ∧ P.Exec G1 ∧ (M.sym S).cons G1 ∧ G.IsPrefixOf G1 ∧
      G1.events.card = G.events.card + 1 := by
  obtain ⟨a, ha, -⟩ := exists_unique_isNext hnf
  have hidx := idx_eq_of_mem_avail ha.1
  have hna := not_mem_of_mem_avail hG ha.1
  have hcard : ∀ G1 : Graph, G1.events = insert a G.events →
      G1.events.card = G.events.card + 1 := fun G1 h => by
    rw [h, Finset.card_insert_of_notMem hna]
  rcases a.act.isRead_or_isWrite_or_isLocal with hk | hk | hk
  · have hact := TEv.IsRead.exists_act hk
    have hwt := Graph.maxWrite_isWriteTo hG a.loc
    exact ⟨_, hG.addRead hidx hact hwt, hE.addRead hG ha.1 hact hwt,
      Model.sym_ext_read hM hG hc hidx hact, hG.isPrefixOf_addRead hidx, hcard _ rfl⟩
  · have hwt := Graph.maxWrite_isWriteTo hG a.loc
    exact ⟨_, hG.addWrite hidx hk hwt, hE.addWrite hG ha.1 hk hwt,
      Model.sym_ext_write hM hG hc hidx hk, hG.isPrefixOf_addWrite hidx, hcard _ rfl⟩
  · by_cases hcs : a.IsCons
    · obtain ⟨φ, hφ⟩ := TEv.IsCons.exists_act hcs
      obtain ⟨b, hb⟩ := Model.sym_ext_cons hM hG hc hidx hφ
      exact ⟨_, hG.addLoc hidx hk (iff_of_true rfl hcs),
        hE.addLoc hG ha.1 hk (iff_of_true rfl hcs), hb, hG.isPrefixOf_addLoc hidx, hcard _ rfl⟩
    · exact ⟨_, hG.addLoc hidx hk (iff_of_false (by simp) hcs),
        hE.addLoc hG ha.1 hk (iff_of_false (by simp) hcs),
        Model.sym_ext_loc_none hM hG hc hidx hk hcs, hG.isPrefixOf_addLoc hidx, hcard _ rfl⟩

/-- A consistent execution of a bounded program is a prefix of a full one. -/
theorem exists_full_extension {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible) {G : Graph}
    (hG : G.Wf) (hE : P.Exec G) (hc : (M.sym S).cons G) :
    ∃ Gf : Graph, Gf.Wf ∧ P.Exec Gf ∧ (M.sym S).cons Gf ∧ P.Full Gf ∧ G.IsPrefixOf Gf := by
  have key : ∀ k (G : Graph), G.Wf → P.Exec G → (M.sym S).cons G →
      n * P.threads.length - G.events.card ≤ k →
      ∃ Gf : Graph, Gf.Wf ∧ P.Exec Gf ∧ (M.sym S).cons Gf ∧ P.Full Gf ∧ G.IsPrefixOf Gf := by
    intro k
    induction k with
    | zero =>
      intro G hG hE hc hk
      by_cases hf : P.Full G
      · exact ⟨G, hG, hE, hc, hf, hG.isPrefixOf_refl⟩
      · obtain ⟨G1, hG1, hE1, -, -, hcard⟩ := exists_ext hM hG hE hc hf
        have h1 := hE1.card_le hG1 hn
        omega
    | succ k ih =>
      intro G hG hE hc hk
      by_cases hf : P.Full G
      · exact ⟨G, hG, hE, hc, hf, hG.isPrefixOf_refl⟩
      · obtain ⟨G1, hG1, hE1, hc1, hp1, hcard⟩ := exists_ext hM hG hE hc hf
        obtain ⟨Gf, h1, h2, h3, h4, h5⟩ := ih G1 hG1 hE1 hc1 (by omega)
        exact ⟨Gf, h1, h2, h3, h4, hp1.trans h5⟩
  exact key _ G hG hE hc (Nat.le_refl _)

/-! ### The exit at an erroneous graph -/

/-- An error predicate, monotone on prefixes: if a prefix of a graph is
erroneous then so is the graph. -/
structure ErrPred where
  /-- the graph is erroneous -/
  isErr : Graph → Prop
  /-- monotonicity -/
  mono : ∀ {G G' : Graph}, G.Wf → G'.IsPrefixOf G → isErr G' → isErr G

/-- The graph has an `error` event. -/
def ErrPred.label : ErrPred where
  isErr := fun G => ∃ e ∈ G.events, e.act = .error
  mono := by
    rintro G G' - ⟨s, -, rfl⟩ ⟨e, he, hact⟩
    exact ⟨e, (Finset.mem_inter.mp he).1, hact⟩

/-- A step of the algorithm with exit: no step from an erroneous
configuration. -/
def StepX (E : ErrPred) (P : Program) (M : Model) {S : Solver} (τ : TieBreak S)
    (c c' : Config) : Prop :=
  ¬ E.isErr c.abs ∧ Step P M τ c c'

/-- The configurations that the algorithm with exit reaches. -/
def ReachX (E : ErrPred) (P : Program) (M : Model) {S : Solver} (τ : TieBreak S)
    (c : Config) : Prop :=
  Relation.ReflTransGen (StepX E P M τ) (Config.init P.mem) c

variable {E : ErrPred}

theorem ReachX.reach {M : Model} {c : Config} (h : ReachX E P M τ c) : Reach P M τ c := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.tail ih hs.2

/-- Without an erroneous configuration, the exit changes nothing. -/
theorem reachX_of_reach {M : Model} (hno : ∀ c, ReachX E P M τ c → ¬ E.isErr c.abs)
    {c : Config} (hc : Reach P M τ c) : ReachX E P M τ c := by
  induction hc with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.tail ih ⟨hno _ ih, hs⟩

/-- If some consistent execution of a bounded program is erroneous, the
algorithm with exit reaches an erroneous configuration. -/
theorem exists_reachX_err {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible) {G : Graph}
    (hG : G.Wf) (hE : P.Exec G) (hc : (M.sym S).cons G) (herr : E.isErr G) :
    ∃ c, ReachX E P (M.sym S) τ c ∧ E.isErr c.abs := by
  by_contra hne
  have hno : ∀ c, ReachX E P (M.sym S) τ c → ¬ E.isErr c.abs :=
    fun c hc he => hne ⟨c, hc, he⟩
  obtain ⟨Gf, hGf, hEf, hcf, hff, hp⟩ := exists_full_extension hn hM hG hE hc
  obtain ⟨c, hcr, hcabs⟩ := complete (τ := τ) hn hM hGf hEf hcf hff
  exact hno c (reachX_of_reach hno hcr) (hcabs ▸ E.mono hGf hp herr)

/-- The reading of Theorem 4 for the algorithm with exit: either it reaches an
erroneous configuration, or it visits every full consistent execution. -/
theorem complete_exit {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible) :
    (∃ c, ReachX E P (M.sym S) τ c ∧ E.isErr c.abs) ∨
    ∀ Gf : Graph, Gf.Wf → P.Exec Gf → (M.sym S).cons Gf → P.Full Gf →
      ∃ c, ReachX E P (M.sym S) τ c ∧ c.abs = Gf := by
  by_cases h : ∃ c, ReachX E P (M.sym S) τ c ∧ E.isErr c.abs
  · exact Or.inl h
  · right
    intro Gf hGf hEf hcf hff
    obtain ⟨c, hcr, hcabs⟩ := complete (τ := τ) hn hM hGf hEf hcf hff
    exact ⟨c, reachX_of_reach (fun c hc he => h ⟨c, hc, he⟩) hcr, hcabs⟩

end Condpor
