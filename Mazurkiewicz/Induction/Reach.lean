import Mazurkiewicz.Trust.Budget
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Finite.Lattice

/-!
# The transition system on execution graphs

`induction-popl`, `prelim.tex` sec:lts (def:step, prop:reach-exec,
def:safety) and `concepts.tex` sec:fixpoint (def:F, lem:finite-branching,
prop:lfp, cor:stabilisation, def:invariant, prop:rule), for plain programs:
the labels are read and write labels (plan `plan/ind/LEAN-PLAN.md`,
Section 2).

How the text is read here.

* A graph of the paper is a well-formed `Graph`. Sets of graphs are
  `Set Graph`, over all (raw) graphs. The step relation, `GReach`, the values
  of `post` and `stepF` and the iterates contain well-formed graphs only;
  a property `Bad` and an invariant candidate `X` may contain others. This is
  harmless: `X ∩ {G | G.Wf}` is again an invariant, and safety does not look
  at the malformed members of `Bad`.
* def:step: `G → G'` if `G'.E = G.E ⊎ {e}`, `G = G'|G.E`, `G'` is an execution
  of `P` and is consistent. The union is disjoint: `e ∉ G.events`.
* `|G|` counts the initialization event: `Graph.size`.
* `Reach_M(P)` is `GReach P M`; `post`, `F` are `post P M`, `stepF P M` on
  `Set Graph`.
* prop:lfp is proved directly (the reachable graphs are a fixpoint of `F`
  and lie below every pre-fixpoint), not through ω-continuity
  (lem:finite-branching (iii) is still stated: `stepF_mono`, `post_iUnion`,
  and `stepF_iUnion` for a non-empty family; it fails for the empty family).
* lem:finite-branching (ii) and cor:stabilisation speak of finite sets of
  graphs: `Set.Finite`.
* prop:bounded-decidable is not formalised (plan, "not formalised").
-/

namespace Trust

open Program

variable {P : Program} {M : Model}

/-- `|G|`: the number of events, with the initialization event. -/
def Graph.size (G : Graph) : ℕ := G.events.card + 1

/-- `G ∈ Exec_SC(P)`: a well-formed, SC-consistent execution of `P`. -/
def ExecSC (P : Program) (G : Graph) : Prop := G.Wf ∧ P.Exec G ∧ SC.cons G

/-- A step `G →_{P,M} G'` (def:step). -/
def GStep (P : Program) (M : Model) (G G' : Graph) : Prop :=
  G.Wf ∧ G'.Wf ∧ ∃ e, e ∉ G.events ∧ G'.events = insert e G.events ∧
    G = G'.restrict G.events ∧ P.Exec G' ∧ M.cons G'

/-- `Reach_M(P)` (def:step). -/
def GReach (P : Program) (M : Model) (G : Graph) : Prop :=
  Relation.ReflTransGen (GStep P M) (Graph.init P.mem) G

/-- `post_{P,M}(X)` (def:step). -/
def post (P : Program) (M : Model) (X : Set Graph) : Set Graph :=
  {G' | ∃ G ∈ X, GStep P M G G'}

/-- The reachability operator `F(X) = {G_init} ∪ post(X)` (def:F). -/
def stepF (P : Program) (M : Model) (X : Set Graph) : Set Graph :=
  {Graph.init P.mem} ∪ post P M X

/-- `P` is safe for `Bad` under `M` (def:safety). -/
def Safe (P : Program) (M : Model) (Bad : Set Graph) : Prop :=
  ∀ G, GReach P M G → G ∉ Bad

/-- An inductive invariant (def:invariant): `F(X) ⊆ X`. -/
def IsInvariant (P : Program) (M : Model) (X : Set Graph) : Prop :=
  stepF P M X ⊆ X

/-! ### One step -/

/-- A well-formed graph with one event less, obtained by restriction, is a
prefix. -/
theorem isPrefixOf_of_insert {G G' : Graph} {e : TEv} (hG : G.Wf) (hG' : G'.Wf)
    (he : e ∉ G.events) (hev : G'.events = insert e G.events)
    (hres : G = G'.restrict G.events) : G.IsPrefixOf G' := by
  refine ⟨G.events, ?_, hres⟩
  have hsub : G.events ⊆ G'.events := by
    rw [hev]
    exact Finset.subset_insert _ _
  intro a b hab hb
  cases a with
  | init => trivial
  | th q =>
    have hq : q ∈ G'.events := (hG'.mem_of_porfStep hab).1
    cases b with
    | init => exact absurd hab (G'.not_porfStep_init _)
    | th b' =>
      have hb' : b' ∈ G.events := (Finset.mem_inter.mp hb).2
      have hqe : q ≠ e := by
        rintro rfl
        rcases hab with hpo | ⟨r, hr, -, hrf⟩
        · obtain ⟨-, -, ht, hi⟩ := hpo
          obtain ⟨e'', he'', ht'', hi''⟩ := hG.idx_contig b' hb' _ hi
          have := hG'.idx_inj e'' (hsub he'') q hq (ht''.trans ht.symm) hi''
          exact he (this ▸ he'')
        · rw [← Ev.th.inj hr] at hrf
          have hread : b'.IsRead := hG'.isRead_of_rf hrf
          obtain ⟨x, hx⟩ : ∃ x, b'.act = .read x := by
            cases hact : b'.act with
            | read x => exact ⟨x, rfl⟩
            | write x v => simp [TEv.IsRead, hact, Act.IsRead] at hread
          obtain ⟨w, hw, -⟩ := hG.rf_read b' hb' x hx
          have h1 : G.rf b' = (G'.restrict G.events).rf b' := congrArg (fun H => H.rf b') hres
          rw [G'.restrict_rf_of_mem (Finset.mem_inter.mpr ⟨hsub hb', hb'⟩), hrf] at h1
          simp only [he, ↓reduceIte] at h1
          rw [h1] at hw
          cases hw
      rw [hev] at hq
      have hqG := (Finset.mem_insert.mp hq).resolve_left hqe
      exact Finset.mem_inter.mpr ⟨hsub hqG, hqG⟩

/-- The form of a step: the new event is available, and the new graph is the
old one with the event added as a read with some source, or as a write at
some place of the coherence order. -/
theorem step_cases {G G' : Graph} {e : TEv} (hG : G.Wf) (hG' : G'.Wf) (he : e ∉ G.events)
    (hev : G'.events = insert e G.events) (hres : G = G'.restrict G.events)
    (hE : P.Exec G') :
    e ∈ P.avail G ∧
      ((∃ x w, e.act = .read x ∧ G.IsWriteTo x w ∧ G' = G.addRead e w) ∨
       (∃ wp, e.IsWrite ∧ G.IsWriteTo e.loc wp ∧ G' = G.addWrite e wp)) := by
  have hp := isPrefixOf_of_insert hG hG' he hev hres
  obtain ⟨s, hs, hres'⟩ := hp
  have he' : e ∈ G'.events := by
    rw [hev]
    exact Finset.mem_insert_self _ _
  have hsub : G.events ⊆ G'.events := by
    rw [hev]
    exact Finset.subset_insert _ _
  have hGE : G'.events \ {e} = G.events := by
    rw [hev, Finset.sdiff_singleton_eq_erase, Finset.erase_insert he]
  have hrem : G'.remove {e} = G := by
    unfold Graph.remove
    rw [hGE]
    exact hres.symm
  have hof : ∀ q ∈ G'.events, q ≠ e → q ∈ G.events := by
    intro q hq hqe
    rw [hev] at hq
    exact (Finset.mem_insert.mp hq).resolve_left hqe
  -- the sources of the events of `G` are in `G`
  have hsrcG : ∀ q ∈ G.events, ∀ w, G'.rf q = some w → w ∈ Graph.evSet G.events :=
    fun q hq w hw => (rf_of_restrict_eq hG hG' hres hq hw).2
  -- no event reads from `e`
  have hsink : ∀ q, G'.rf q ≠ some (.th e) := by
    intro q hq
    have hqm := (hG'.rf_source_mem hq).1
    by_cases hqe : q = e
    · rw [hqe] at hq
      exact TEv.not_isRead_of_isWrite (hG'.isWrite_of_src hq) (hG'.isRead_of_rf hq)
    · exact he (hsrcG q (hof q hqm hqe) _ hq)
  have hav : e ∈ P.avail G := by
    have h := mem_avail_restrict (P := P) (s := G.events) hG' hE he' he
      (fun q hq _ hi => hof q hq (fun h => Nat.lt_irrefl _ (h ▸ hi)))
      (fun q hq _ hi w hw => hsrcG q (hof q hq (fun h => Nat.lt_irrefl _ (h ▸ hi))) w hw)
      (hres ▸ hG)
    rwa [← hres] at h
  refine ⟨hav, ?_⟩
  cases hact : e.act with
  | read x =>
    left
    obtain ⟨w, hrf, hwt⟩ := hG'.rf_read e he' x hact
    refine ⟨x, w, rfl, ?_, ?_⟩
    · cases w with
      | init => trivial
      | th q =>
        refine ⟨hof q hwt.1 ?_, hwt.2⟩
        rintro rfl
        obtain ⟨v, hv⟩ := hwt.2
        rw [hact] at hv
        cases hv
    · rw [← hrem]
      exact (Graph.remove_addRead hG' he' hact hrf hsink).symm
  | write x v =>
    right
    have hw : e.IsWrite := by simp [TEv.IsWrite, hact, Act.IsWrite]
    obtain ⟨wp, hwp, hco⟩ := Graph.remove_addWrite_co hG' he' hw
    refine ⟨wp, hw, hrem ▸ hwp, ?_⟩
    rw [← hrem]
    symm
    apply Graph.ext
    · rfl
    · exact Graph.remove_singleton_insert he'
    · funext q
      rw [Graph.addWrite_rf]
      by_cases hqe : q = e
      · rw [hqe, hG'.rf_none e (Or.inr hw)]
        exact G'.restrict_rf_of_not_mem (by simp)
      · exact Graph.remove_singleton_rf hG' hqe (hsink q)
    · exact hco

/-! ### Reachability -/



/-- The remark after def:step: the old graph of a step is a prefix of the new
one. (`step_cases` gives the form of the new graph.) -/
theorem GStep.prefix {G G' : Graph} (h : GStep P M G G') : G.IsPrefixOf G' := by
  obtain ⟨hG, hG', e, he, hev, hres, -, -⟩ := h
  exact isPrefixOf_of_insert hG hG' he hev hres

/-- A prefix of a prefix is a prefix (used in cor:full, cor:compose). -/
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

/-- prop:reach-exec: the reachable graphs are the consistent executions. -/
theorem greach_iff {G : Graph} : GReach P M G ↔ G.Wf ∧ P.Exec G ∧ M.cons G := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨Graph.init_wf _, exec_init P, M.cons_init _⟩
    | tail _ hs _ =>
      obtain ⟨-, hG', e, -, -, -, hE, hc⟩ := hs
      exact ⟨hG', hE, hc⟩
  · rintro ⟨hG, hE, hc⟩
    have hb := hE.built hG (M.porf_acyclic G hG hc)
    clear hG hE
    induction hb with
    | init => exact Relation.ReflTransGen.refl
    | @step G₀ G' e hb₀ hG' hav hev hres ih =>
      have hG₀ := hb₀.exec.1
      have he := not_mem_of_mem_avail hG₀ hav
      have hE' : P.Exec G' := (Built.step hb₀ hG' hav hev hres).exec.2
      have hc₀ : M.cons G₀ :=
        M.prefix_closed G' G₀ hG' hc (isPrefixOf_of_insert hG₀ hG' he hev hres)
      exact (ih hc₀).tail ⟨hG₀, hG', e, he, hev, hres, hE', hc⟩

theorem greach_sc_iff {G : Graph} : GReach P SC G ↔ ExecSC P G :=
  greach_iff

/-- The reachable graphs are the consistent built graphs. (lem:built itself is
in the port: (1) `Built.exec`, (2) `Exec.built`, (3) is the definition of
`Program.Full` with `Program.full_iff`.) -/
theorem greach_iff_built {G : Graph} : GReach P M G ↔ P.Built G ∧ M.cons G := by
  rw [greach_iff]
  constructor
  · rintro ⟨hG, hE, hc⟩
    exact ⟨hE.built hG (M.porf_acyclic G hG hc), hc⟩
  · rintro ⟨hb, hc⟩
    exact ⟨hb.exec.1, hb.exec.2, hc⟩

/-- lem:finite-branching (i). -/
theorem GStep.size {G G' : Graph} (h : GStep P M G G') : G'.size = G.size + 1 := by
  obtain ⟨-, -, e, he, hev, -⟩ := h
  unfold Graph.size
  rw [hev, Finset.card_insert_of_notMem he]

/-- lem:finite-branching (ii). -/
theorem post_singleton_finite (P : Program) (M : Model) (G : Graph) :
    (post P M {G}).Finite := by
  classical
  let cand : Finset Ev := insert .init (G.events.image Ev.th)
  have hcand : ∀ x w, G.IsWriteTo x w → w ∈ cand := by
    intro x w hw
    cases w with
    | init => exact Finset.mem_insert_self _ _
    | th q => exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hw.1)
  let S : Finset (TEv × Ev) := (P.avail G).toFinset ×ˢ cand
  refine Set.Finite.subset (((Finset.finite_toSet S).image (fun p => G.addRead p.1 p.2)).union
    ((Finset.finite_toSet S).image (fun p => G.addWrite p.1 p.2))) ?_
  rintro G' ⟨G₀, hG₀, hG, hG', e, he, hev, hres, hE, -⟩
  rw [Set.mem_singleton_iff] at hG₀
  subst hG₀
  obtain ⟨hav, hcase⟩ := step_cases hG hG' he hev hres hE
  rcases hcase with ⟨x, w, -, hw, rfl⟩ | ⟨wp, -, hwp, rfl⟩
  · left
    exact ⟨(e, w), Finset.mem_coe.mpr (Finset.mem_product.mpr
      ⟨List.mem_toFinset.mpr hav, hcand x w hw⟩), rfl⟩
  · right
    exact ⟨(e, wp), Finset.mem_coe.mpr (Finset.mem_product.mpr
      ⟨List.mem_toFinset.mpr hav, hcand _ wp hwp⟩), rfl⟩

/-- lem:finite-branching (iii), monotonicity. -/
theorem stepF_mono (P : Program) (M : Model) : Monotone (stepF P M) := by
  intro X Y hXY G hG
  rcases hG with h | ⟨G₀, hG₀, hs⟩
  · exact Or.inl h
  · exact Or.inr ⟨G₀, hXY hG₀, hs⟩

/-- lem:finite-branching (iii), continuity: `post` commutes with unions. -/
theorem post_iUnion (P : Program) (M : Model) {ι : Type*} (X : ι → Set Graph) :
    post P M (⋃ i, X i) = ⋃ i, post P M (X i) := by
  ext G'
  simp only [post, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨G, ⟨i, hi⟩, hs⟩
    exact ⟨i, G, hi, hs⟩
  · rintro ⟨i, G, hi, hs⟩
    exact ⟨G, ⟨i, hi⟩, hs⟩

/-- lem:finite-branching (iii), continuity of `F`, for a non-empty family. -/
theorem stepF_iUnion (P : Program) (M : Model) {ι : Type*} [Nonempty ι] (X : ι → Set Graph) :
    stepF P M (⋃ i, X i) = ⋃ i, stepF P M (X i) := by
  unfold stepF
  rw [post_iUnion, Set.union_iUnion]

/-- prop:lfp, first part: `Fⁿ(∅)` is the set of reachable graphs of size at
most `n`. -/
theorem stepF_iterate (P : Program) (M : Model) (n : ℕ) :
    (stepF P M)^[n] ∅ = {G | GReach P M G ∧ G.size ≤ n} := by
  induction n with
  | zero =>
    ext G
    simp [Graph.size]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    ext G
    constructor
    · rintro (h | ⟨G₀, ⟨hr, hsz⟩, hs⟩)
      · rw [Set.mem_singleton_iff] at h
        subst h
        exact ⟨Relation.ReflTransGen.refl, by simp [Graph.size, Graph.init]⟩
      · exact ⟨hr.tail hs, by rw [hs.size]; exact Nat.succ_le_succ hsz⟩
    · rintro ⟨hr, hsz⟩
      rcases Relation.ReflTransGen.cases_tail hr with h | ⟨G₀, hr₀, hs⟩
      · exact Or.inl h
      · refine Or.inr ⟨G₀, ⟨hr₀, ?_⟩, hs⟩
        have := hs.size
        omega

/-- prop:lfp, second part: `Reach = ⋃ₙ Fⁿ(∅)`. -/
theorem greach_eq_iUnion (P : Program) (M : Model) :
    {G | GReach P M G} = ⋃ n, (stepF P M)^[n] ∅ := by
  ext G
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, stepF_iterate]
  exact ⟨fun h => ⟨G.size, h, Nat.le_refl _⟩, fun ⟨_, h, _⟩ => h⟩

/-- prop:lfp, third part: `Reach = lfp F`. -/
theorem greach_eq_lfp (P : Program) (M : Model) :
    {G | GReach P M G} = OrderHom.lfp ⟨stepF P M, stepF_mono P M⟩ := by
  apply le_antisymm
  · intro G hG
    induction hG with
    | refl =>
      rw [← OrderHom.map_lfp]
      exact Or.inl rfl
    | tail _ hs ih =>
      rw [← OrderHom.map_lfp]
      exact Or.inr ⟨_, ih, hs⟩
  · apply OrderHom.lfp_le
    rintro G (h | ⟨G₀, hr, hs⟩)
    · rw [Set.mem_singleton_iff] at h
      subst h
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail hr hs

/-- Every iterate is a finite set (proof of cor:stabilisation). -/
theorem stepF_iterate_finite (P : Program) (M : Model) (n : ℕ) :
    ((stepF P M)^[n] ∅).Finite := by
  induction n with
  | zero => exact Set.finite_empty
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine (Set.finite_singleton _).union ?_
    have : post P M ((stepF P M)^[n] ∅) = ⋃ G ∈ (stepF P M)^[n] ∅, post P M {G} := by
      ext G'
      simp only [post, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_singleton_iff]
      constructor
      · rintro ⟨G, hG, hs⟩
        exact ⟨G, hG, G, rfl, hs⟩
      · rintro ⟨G, hG, G₀, rfl, hs⟩
        exact ⟨G₀, hG, hs⟩
    rw [this]
    exact Set.Finite.biUnion ih (fun G _ => post_singleton_finite P M G)

/-- cor:stabilisation: the iterates stabilise iff `Reach` is finite. -/
theorem stabilises_iff (P : Program) (M : Model) :
    (∃ n, (stepF P M)^[n + 1] ∅ = (stepF P M)^[n] ∅) ↔ {G | GReach P M G}.Finite := by
  constructor
  · rintro ⟨n, hn⟩
    have hstab : ∀ m, (stepF P M)^[n + m] ∅ = (stepF P M)^[n] ∅ := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        have hn' := hn
        rw [Function.iterate_succ_apply'] at hn'
        rw [← Nat.add_assoc, Function.iterate_succ_apply', ih]
        exact hn'
    have : {G | GReach P M G} = (stepF P M)^[n] ∅ := by
      rw [greach_eq_iUnion]
      apply le_antisymm
      · intro G hG
        obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hG
        rw [← hstab m]
        exact Monotone.monotone_iterate_of_le_map (stepF_mono P M) (Set.empty_subset _)
          (Nat.le_add_left m n) hm
      · exact Set.subset_iUnion (fun n => (stepF P M)^[n] ∅) n
    rw [this]
    exact stepF_iterate_finite P M n
  · intro hfin
    obtain ⟨n, hn⟩ := Set.Finite.bddAbove (Set.Finite.image Graph.size hfin)
    refine ⟨n, ?_⟩
    rw [stepF_iterate, stepF_iterate]
    ext G
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨h.1, hn ⟨G, h.1, rfl⟩⟩, fun h => ⟨h.1, Nat.le_succ_of_le h.2⟩⟩

/-- cor:stabilisation, second sentence: a bounded program has finitely many
reachable graphs. -/
theorem greach_finite_of_bounded {n : ℕ} (hn : P.Bounded n) (M : Model) :
    {G | GReach P M G}.Finite := by
  refine (stepF_iterate_finite P M (n * P.threads.length + 1)).subset (fun G hG => ?_)
  rw [stepF_iterate]
  obtain ⟨hW, hE, -⟩ := greach_iff.mp hG
  exact ⟨hG, Nat.succ_le_succ (hE.card_le hW hn)⟩

/-- prop:rule: `P` is safe for `Bad` iff some inductive invariant is disjoint
from `Bad`. -/
theorem safe_iff_invariant (P : Program) (M : Model) (Bad : Set Graph) :
    Safe P M Bad ↔ ∃ X, IsInvariant P M X ∧ Disjoint X Bad := by
  constructor
  · intro h
    refine ⟨{G | GReach P M G}, ?_, Set.disjoint_left.mpr (fun G hG => h G hG)⟩
    rintro G (h' | ⟨G₀, hr, hs⟩)
    · rw [Set.mem_singleton_iff] at h'
      subst h'
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail hr hs
  · rintro ⟨X, hX, hdisj⟩ G hG
    have : G ∈ X := by
      induction hG with
      | refl => exact hX (Or.inl rfl)
      | tail _ hs ih => exact hX (Or.inr ⟨_, ih, hs⟩)
    exact Set.disjoint_left.mp hdisj this

/-! ### Instances -/

namespace Examples

/-- The full graph `G3` of the checked run of the port is reachable by steps. -/
example : GReach revProg SC G3 :=
  greach_iff.mpr ⟨G3_facts.1, G3_facts.2.1, G3_facts.2.2.1⟩

/-- Its program has finitely many reachable graphs, so the iterates of `F`
stabilise. -/
example : ∃ n, (stepF revProg SC)^[n + 1] ∅ = (stepF revProg SC)^[n] ∅ :=
  (stabilises_iff revProg SC).mpr (greach_finite_of_bounded revProg_bounded SC)

end Examples

end Trust
