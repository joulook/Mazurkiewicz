import Mazurkiewicz.Condpor.Exit

/-!
# The prefix order and `GetNext` (Section 4.2)

The paper, after Theorems 4 and 5: for `G_s ⊑ G_t`, a procedure
`GetNext(G_s, G_t)` "returns the (minimal, unique and nonempty) sequence of
algorithmic steps `S` with which `G_s` reaches a graph `G` such that
`G_s ⊑ G ⊑ G_t`", and `S` does not revisit events of `G_s`; "calling
`GetNext` in a fixpoint yields the desired result".

Here `⊑` is `Graph.IsPrefixOf`. What is proved:

* `opLe_iff_isPrefixOf`: on well-formed executions without a causality cycle,
  `IsPrefixOf` is the order by operational steps (`OpLe`), the definition of
  the proof document that the paper builds on. `NrLe.opLe`: the order as the
  paper prints it (non-revisit steps of the algorithm, `NrLe`) is contained
  in it; `nrLe_fails` (file `GetNextEx.lean`): properly.
* `Reach.prefix_pred`: a reached graph that is a proper prefix of the graph
  after a step is a prefix of the graph before the step.
* `Reach.path_of_prefix`: a reached configuration whose graph is a prefix of
  the graph of a reached configuration `c_t` is on the path to `c_t`, and its
  graph is a prefix of every later graph of that path.
* `Reach.exists_seg`, `Seg.unique`: the claims about `GetNext(G_s, G_t)`: a
  unique minimal nonempty sequence of steps from `G_s` to a graph between
  `G_s` and `G_t`, which revisits no event of `G_s`.
* `Reach.segChain`, `SegChain.unique`, `getNext_fixpoint`: "calling `GetNext`
  in a fixpoint" leads from the initial configuration to every execution of
  `⟦P⟧`, in at most as many rounds as it has events, along the only path.

What is not proved, and how the statements differ from the text.

* `GetNext` is not defined as a recursive procedure, and Theorems 4 and 5 are
  not proved again from it. The statements above are derived from the
  backward steps of `Prev.lean`: `Reach.prefix_pred` uses (P5) and
  `Reach.prevStep_of_step`, and `getNext_fixpoint` uses `complete`. They are
  a description of the exploration, not a second proof of its correctness.
  Theorem 5(b) is `Reach.reaches_full`, not a consequence of these.
* The target `G_t` is the graph of a reached configuration (every graph of
  `⟦P⟧` is one).
* `G_s ≠ G_t` is required ("nonempty" needs it), and the end of the segment
  extends `G_s` strictly.
-/

namespace Condpor

open Program

variable {P : Program} {M : Model} {S : Solver} {τ : TieBreak S}

/-! ### Facts on prefixes -/

namespace Graph

/-- The restriction depends only on the events that are kept. -/
theorem Wf.restrict_congr {G : Graph} (hG : G.Wf) {s s' : Finset TEv}
    (h : G.events ∩ s = G.events ∩ s') : G.restrict s = G.restrict s' := by
  have hmem : ∀ q ∈ G.events, (q ∈ s ↔ q ∈ s') := by
    intro q hq
    constructor
    · intro hs
      exact (Finset.mem_inter.mp (h ▸ Finset.mem_inter.mpr ⟨hq, hs⟩)).2
    · intro hs
      exact (Finset.mem_inter.mp (h.symm ▸ Finset.mem_inter.mpr ⟨hq, hs⟩)).2
  apply Graph.ext
  · rfl
  · exact h
  · funext e
    by_cases he : e ∈ G.events ∩ s
    · have he' : e ∈ G.events ∩ s' := h ▸ he
      rw [G.restrict_rf_of_mem he, G.restrict_rf_of_mem he']
      cases hrf : G.rf e with
      | none => rfl
      | some w =>
        cases w with
        | init => rfl
        | th w0 =>
          have hw0 : w0 ∈ G.events := (hG.rf_source_mem hrf).2
          by_cases h1 : w0 ∈ s
          · simp [h1, (hmem w0 hw0).mp h1]
          · simp [h1, (hmem w0 hw0).not.mp h1]
    · have he' : e ∉ G.events ∩ s' := h ▸ he
      rw [G.restrict_rf_of_not_mem he, G.restrict_rf_of_not_mem he']
  · funext x
    simp only [restrict_co]
    apply List.filter_congr
    intro a ha
    have haE : a ∈ G.events := ((hG.co_mem x a).mp ha).1
    simp [hmem a haE]
  · funext e
    simp only [restrict_pol, h]

/-- A set closed under causal predecessors is closed under `porf`. -/
theorem prefixClosed_porf {G : Graph} {s : Set Ev} (hs : Maz.PrefixClosed G.porfStep s)
    {a b : Ev} (h : G.porf a b) (hb : b ∈ s) : a ∈ s := by
  induction h using Relation.TransGen.head_induction_on with
  | single h => exact hs h hb
  | head h _ ih => exact hs h ih

/-- Of two prefixes of a graph, one whose events are among the events of the
other is a prefix of the other. -/
theorem IsPrefixOf.of_subset {X Y K : Graph} (hX : X.Wf) (hY : Y.IsPrefixOf X)
    (hK : K.IsPrefixOf X) (hsub : Y.events ⊆ K.events) : Y.IsPrefixOf K := by
  obtain ⟨s, hs, rfl⟩ := hY
  obtain ⟨t, ht, rfl⟩ := hK
  have hsub' : X.events ∩ s ⊆ X.events ∩ t := hsub
  have heq : X.events ∩ (t ∩ (X.events ∩ s)) = X.events ∩ s := by
    ext q
    simp only [Finset.mem_inter]
    constructor
    · exact fun h => h.2.2
    · exact fun h => ⟨h.1, (Finset.mem_inter.mp (hsub' (Finset.mem_inter.mpr h))).2, h⟩
  refine ⟨X.events ∩ s, ?_, ?_⟩
  · intro a b hab hb
    have hb' : b ∈ evSet (X.events ∩ s) := by
      cases b with
      | init => trivial
      | th q =>
        have : q ∈ (X.restrict t).events ∩ (X.events ∩ s) := hb
        exact (Finset.mem_inter.mp this).2
    have hbt : b ∈ evSet (X.events ∩ t) := evSet_mono hsub' hb'
    have hXab : X.porf a b :=
      (porf_restrict_iff ht hbt).mp (Relation.TransGen.single hab)
    have ha : a ∈ evSet (X.events ∩ s) := prefixClosed_porf hs hXab hb'
    cases a with
    | init => trivial
    | th q =>
      have hq : q ∈ X.events ∩ s := ha
      exact Finset.mem_inter.mpr ⟨hsub' hq, hq⟩
  · rw [restrict_restrict, hX.restrict_congr heq]

/-- A well-formed restriction that keeps the sources of its reads is a
prefix. -/
theorem isPrefixOf_of_restrict_eq {Z K : Graph} (hZ : Z.Wf) (hK : K.Wf)
    (h : K = Z.restrict K.events) (hrf : ∀ q ∈ K.events, Z.rf q = K.rf q) :
    K.IsPrefixOf Z := by
  have hsub : K.events ⊆ Z.events := by
    intro q hq
    have : q ∈ (Z.restrict K.events).events := h ▸ hq
    exact (Finset.mem_inter.mp this).1
  refine ⟨K.events, ?_, h⟩
  intro a b hab hb
  cases b with
  | init => exact absurd hab (Z.not_porfStep_init a)
  | th q =>
    have hq : q ∈ K.events := (Finset.mem_inter.mp (show q ∈ Z.events ∩ K.events from hb)).2
    cases a with
    | init => trivial
    | th p =>
      rcases hab with hpo | ⟨q', hq', hq'm, hq'rf⟩
      · obtain ⟨hpZ, -, ht, hi⟩ := hpo
        obtain ⟨p', hp', hp't, hp'i⟩ := hK.idx_contig q hq p.idx hi
        have : p' = p := hZ.idx_inj p' (hsub hp') p hpZ (hp't.trans ht.symm) hp'i
        exact Finset.mem_inter.mpr ⟨hpZ, this ▸ hp'⟩
      · cases hq'
        have hKrf : K.rf q = some (.th p) := (hrf q hq) ▸ hq'rf
        have hp : p ∈ K.events := (hK.rf_source_mem hKrf).2
        exact Finset.mem_inter.mpr ⟨hsub hp, hp⟩

end Graph

/-! ### The key lemma -/

/-- In a reached configuration, every event of a larger graph `X` outside the
configuration is `<next`-after `me` of the configuration: the first missing
event of its thread is available, and no available event is `<next`-before
`me` (P5). -/
theorem LastStep.lt_of_not_mem {c : Config} {e0 : TEv} {k0 : Kind} (L : LastStep P c e0 k0)
    (hcw : c.Wf) {X : Graph} (hXW : X.Wf) (hXE : P.Exec X) {s : Finset TEv}
    (hs : Maz.PrefixClosed X.porfStep (Graph.evSet (X.events ∩ s)))
    (hY : c.abs = X.restrict s) {q : TEv} (hq : q ∈ X.events) (hqs : q ∉ s) :
    nextLt (k0.me e0) q := by
  classical
  -- the first event of the thread of `q` outside `s`
  let T : Finset TEv := X.events.filter (fun p => p ∉ s ∧ p.tid = q.tid)
  obtain ⟨q0, hq0, hmin⟩ := T.exists_min_image TEv.idx ⟨q, Finset.mem_filter.mpr ⟨hq, hqs, rfl⟩⟩
  obtain ⟨hq0X, hq0s, hq0t⟩ := Finset.mem_filter.mp hq0
  have hkeep : ∀ p ∈ X.events, p.tid = q0.tid → p.idx < q0.idx → p ∈ s := by
    intro p hp ht hi
    by_contra hps
    exact Nat.not_lt.mpr (hmin p (Finset.mem_filter.mpr ⟨hp, hps, ht.trans hq0t⟩)) hi
  have hYW : (X.restrict s).Wf := hXW.restrict hs
  have hav : q0 ∈ P.avail (X.restrict s) := by
    refine mem_avail_restrict hXW hXE hq0X hq0s hkeep (fun p hp ht hi w hw => ?_) hYW
    have hps : p ∈ X.events ∩ s := Finset.mem_inter.mpr ⟨hp, hkeep p hp ht hi⟩
    exact Graph.evSet_mono Finset.inter_subset_right
      (hs (Or.inr ⟨p, rfl, hp, hw⟩) hps)
  have h1 : nextLt (k0.me e0) q0 := L.me_lt_avail hcw (hY ▸ hav)
  by_cases hqq : q0 = q
  · exact hqq ▸ h1
  · have hle : q0.idx ≤ q.idx := hmin q (Finset.mem_filter.mpr ⟨hq, hqs, rfl⟩)
    have hne : q0.idx ≠ q.idx := fun h => hqq (hXW.idx_inj q0 hq0X q hq hq0t h)
    exact nextLt_trans h1 (nextLt_of_poT ⟨hq0t, by omega⟩)

/-- The key lemma. Let `c` and `d` be reached, and `d ⇒ d'`. If the graph of
`c` is a prefix of the graph of `d'` and differs from it, it is a prefix of
the graph of `d`. -/
theorem Reach.prefix_pred {c d d' : Config} {e : TEv} {k : Kind}
    (hc : Reach P (M.sym S) τ c) (hd : Reach P (M.sym S) τ d)
    (hs : StepL P (M.sym S) τ d e k d') (hp : c.abs.IsPrefixOf d'.abs)
    (hne : c.abs ≠ d'.abs) : c.abs.IsPrefixOf d.abs := by
  classical
  have hd' : Reach P (M.sym S) τ d' := Relation.ReflTransGen.tail hd ⟨e, k, hs⟩
  obtain ⟨hcw, -, -, -⟩ := hc.sound
  obtain ⟨hdw, -, -, hdE⟩ := hd.sound
  obtain ⟨hXw, -, hXc, hXE⟩ := hd'.sound
  have hXW := hXw.1
  have hac : Maz.Acyclic d'.abs.porfStep := (M.sym S).porf_acyclic _ hXW hXc
  have hprev := hd.prevStep_of_step hs
  obtain ⟨s, hsc, hY⟩ := hp
  have hYev : c.abs.events = d'.abs.events ∩ s := by rw [hY]; rfl
  -- an event of the larger graph outside the prefix
  obtain ⟨b, hbX, hbs⟩ : ∃ b ∈ d'.abs.events, b ∉ s := by
    by_contra hall
    push Not at hall
    apply hne
    rw [hY, hXW.restrict_congr (s' := d'.abs.events), hXW.restrict_self]
    ext q
    simp only [Finset.mem_inter, and_self]
    exact ⟨fun h => h.1, fun h => ⟨h, hall q h⟩⟩
  -- `me` of the larger graph is outside the prefix, and so is the source of a
  -- revisited read
  have hout : ∀ a, d'.abs.IsMe (.th a) → a ∉ s ∧
      ∀ w, d'.abs.rf a = some (.th w) → nextLt a w →
        (∀ x, d'.abs.porf (.th w) x ↔ x = .th a) → w ∉ s := by
    intro a hme
    by_cases hnil : c.order = []
    · have hemp : d'.abs.events ∩ s = ∅ := by
        rw [← hYev]
        change c.order.toFinset = ∅
        rw [hnil]
        rfl
      have key : ∀ q ∈ d'.abs.events, q ∉ s := fun q hq hqs =>
        Finset.notMem_empty q (hemp ▸ Finset.mem_inter.mpr ⟨hq, hqs⟩)
      exact ⟨key a hme.1, fun w hw _ _ => key w (hXW.rf_source_mem hw).2⟩
    · obtain ⟨e0, k0, L⟩ := hc.lastStep hnil
      have hlt : ∀ q ∈ d'.abs.events, q ∉ s → nextLt (k0.me e0) q :=
        fun q hq hqs => L.lt_of_not_mem hcw hXW hXE hsc hY hq hqs
      have hmY : c.abs.IsMe (.th (k0.me e0)) := L.me
      -- a `porf`-maximal event of the prefix is not `<next`-after its `me`
      have hle : ∀ z ∈ d'.abs.events, z ∈ s → (∀ x, ¬ c.abs.porf (.th z) x) →
          ¬ nextLt (k0.me e0) z := by
        intro z hzX hzs hzmax hlt'
        have hzY : z ∈ c.abs.events := hYev ▸ Finset.mem_inter.mpr ⟨hzX, hzs⟩
        by_cases hzm : z = k0.me e0
        · exact nextLt_irrefl _ (hzm ▸ hlt')
        · have := hmY.2.2 (.th z) hzY hzmax (fun h => hzm (Ev.th.inj h))
          exact nextLt_irrefl _ (nextLt_trans hlt' this)
      -- `porf` of the prefix is `porf` of the graph
      have hporf : ∀ {x y : Ev}, c.abs.porf x y → d'.abs.porf x y := by
        intro x y hxy
        rw [hY] at hxy
        have hy : y ∈ Graph.evSet (d'.abs.events ∩ s) :=
          ((hXW.restrict hsc).mem_of_porf hxy).2
        exact (Graph.porf_restrict_iff hsc hy).mp hxy
      have ha : a ∉ s := by
        intro has
        obtain ⟨b', hb'X, hb'r, hb'max⟩ := Graph.exists_maximal_reach hXW hac hbX
        have hb's : b' ∉ s := by
          intro h
          rcases hb'r with rfl | hr
          · exact hbs h
          · have : Ev.th b ∈ Graph.evSet (d'.abs.events ∩ s) :=
              Graph.prefixClosed_porf hsc hr (Finset.mem_inter.mpr ⟨hb'X, h⟩)
            have this' : b ∈ d'.abs.events ∩ s := this
            exact hbs (Finset.mem_inter.mp this').2
        have hb'a : b' ≠ a := fun h => hb's (h ▸ has)
        have h1 : nextLt b' a := hme.2.2 (.th b') hb'X hb'max (fun h => hb'a (Ev.th.inj h))
        have h2 : nextLt (k0.me e0) b' := hlt b' hb'X hb's
        exact hle a hme.1 has (fun x hx => hme.2.1 x (hporf hx)) (nextLt_trans h2 h1)
      refine ⟨ha, fun w hw hlt' hsucc hws => ?_⟩
      have hwX : w ∈ d'.abs.events := (hXW.rf_source_mem hw).2
      have hwmax : ∀ x, ¬ c.abs.porf (.th w) x := by
        intro x hx
        have hxa : x = .th a := (hsucc x).mp (hporf hx)
        have : Ev.th a ∈ Graph.evSet c.abs.events := by
          rw [← hxa]
          exact (hcw.1.mem_of_porf hx).2
        have ha' : a ∈ d'.abs.events ∩ s := hYev ▸ this
        exact ha (Finset.mem_inter.mp ha').2
      exact hle w hwX hws hwmax (nextLt_trans (hlt a hme.1 ha) hlt')
  cases k with
  | nr =>
    obtain ⟨hme, hG', -⟩ := hprev.nr_inv
    obtain ⟨hpre, -, -⟩ := nr_remove hXW hXE hme
    rw [hG']
    refine Graph.IsPrefixOf.of_subset hXW ⟨s, hsc, hY⟩ hpre ?_
    intro q hq
    have hq' : q ∈ d'.abs.events ∩ s := hYev ▸ hq
    have hqa : q ≠ e := fun h => (hout e hme).1 (h ▸ (Finset.mem_inter.mp hq').2)
    simp only [Graph.remove, Graph.restrict_events, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_singleton]
    exact ⟨(Finset.mem_inter.mp hq').1, (Finset.mem_inter.mp hq').1, hqa⟩
  | rv a =>
    obtain ⟨hme, -, hrf, hlt, hsucc, hmc⟩ := hprev.rv_inv
    obtain ⟨hpre, hav⟩ := rv_remove hXW hXE hme hrf hsucc
    have hKW : (d'.abs.remove {a, e}).Wf := hXW.of_isPrefixOf hpre
    have hKE : P.Exec (d'.abs.remove {a, e}) := hXE.of_isPrefixOf hXW hpre
    obtain ⟨hZW, -, -, -, hres, -, hrfeq⟩ := hmc.facts hKW hKE hav
    have h1 : c.abs.IsPrefixOf (d'.abs.remove {a, e}) := by
      refine Graph.IsPrefixOf.of_subset hXW ⟨s, hsc, hY⟩ hpre ?_
      intro q hq
      have hq' : q ∈ d'.abs.events ∩ s := hYev ▸ hq
      obtain ⟨has, hes⟩ := hout a hme
      have hqa : q ≠ a := fun h => has (h ▸ (Finset.mem_inter.mp hq').2)
      have hqe : q ≠ e := fun h => hes e hrf hlt hsucc (h ▸ (Finset.mem_inter.mp hq').2)
      simp only [Graph.remove, Graph.restrict_events, Finset.mem_inter, Finset.mem_sdiff,
        Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(Finset.mem_inter.mp hq').1, (Finset.mem_inter.mp hq').1, hqa, hqe⟩
    exact h1.trans (Graph.isPrefixOf_of_restrict_eq hZW hKW hres hrfeq)

/-! ### On the path -/

namespace Graph

/-- A prefix with all the events of the graph is the graph. -/
theorem IsPrefixOf.eq_of_subset {Y X : Graph} (hX : X.Wf) (h : Y.IsPrefixOf X)
    (hsub : X.events ⊆ Y.events) : Y = X := by
  obtain ⟨s, -, rfl⟩ := h
  rw [hX.restrict_congr (s' := X.events), hX.restrict_self]
  ext q
  simp only [Finset.mem_inter, and_self]
  exact ⟨fun h => h.1, fun h => ⟨h, (Finset.mem_inter.mp (hsub h)).2⟩⟩

theorem IsPrefixOf.events_subset {Y X : Graph} (h : Y.IsPrefixOf X) : Y.events ⊆ X.events := by
  obtain ⟨s, -, rfl⟩ := h
  exact Finset.inter_subset_left

/-- A proper prefix has fewer events. -/
theorem IsPrefixOf.card_lt {Y X : Graph} (hX : X.Wf) (h : Y.IsPrefixOf X) (hne : Y ≠ X) :
    Y.events.card < X.events.card := by
  refine Finset.card_lt_card ⟨h.events_subset, fun hsub => hne (h.eq_of_subset hX hsub)⟩

end Graph

/-- G-3. A reached configuration `c` whose graph is a prefix of the graph of
a reached configuration `c_t` is on the path to `c_t`, and its graph is a
prefix of the graph of every configuration of the path from `c` to `c_t`. -/
theorem Reach.path_of_prefix {c ct : Config} (hc : Reach P (M.sym S) τ c)
    (ht : Reach P (M.sym S) τ ct) (hp : c.abs.IsPrefixOf ct.abs) :
    ∃ p, Maz.Path (Step P (M.sym S) τ) c p ct ∧ ∀ d ∈ p, c.abs.IsPrefixOf d.abs := by
  obtain ⟨p0, hp0⟩ := Maz.Path.of_reflTransGen ht
  suffices H : ∀ (n : ℕ) (p0 : List Config) (ct : Config), p0.length = n →
      Maz.Path (Step P (M.sym S) τ) (Config.init P.mem) p0 ct → c.abs.IsPrefixOf ct.abs →
      ∃ p, Maz.Path (Step P (M.sym S) τ) c p ct ∧ ∀ d ∈ p, c.abs.IsPrefixOf d.abs from
    H _ p0 ct rfl hp0 hp
  intro n
  induction n with
  | zero =>
    intro p0 ct hlen hpath hpre
    have hnil : p0 = [] := List.length_eq_zero_iff.mp hlen
    subst hnil
    have hct : Config.init P.mem = ct := Maz.Path.nil_iff.mp hpath
    subst hct
    have hev : c.abs.events = ∅ := by
      have := hpre.events_subset
      rw [Config.init_abs] at this
      exact Finset.subset_empty.mp this
    have habs : c.abs = (Config.init P.mem).abs := by
      rw [Config.init_abs, hc.sound.1.1.eq_init_of_events_eq_empty hev, hc.sound.2.2.2.1]
    have := hc.eq_of_abs_eq Relation.ReflTransGen.refl habs
    subst this
    exact ⟨[], Maz.Path.nil _, by simp⟩
  | succ n ih =>
    intro p0 ct hlen hpath hpre
    have htr : Reach P (M.sym S) τ ct := hpath.reflTransGen
    by_cases heq : c.abs = ct.abs
    · have := hc.eq_of_abs_eq htr heq
      subst this
      exact ⟨[], Maz.Path.nil _, by simp⟩
    · have hne : p0 ≠ [] := by
        intro h
        rw [h] at hlen
        cases hlen
      obtain ⟨q, b, rfl, hq, e, k, hs⟩ := hpath.exists_snoc hne
      have hb : Reach P (M.sym S) τ b := hq.reflTransGen
      have hpb := hc.prefix_pred hb hs hpre heq
      have hql : q.length = n := by simpa using hlen
      obtain ⟨p, hp, hall⟩ := ih q b hql hq hpb
      refine ⟨p ++ [ct], hp.snoc ⟨e, k, hs⟩, fun d hd => ?_⟩
      rcases List.mem_append.mp hd with h | h
      · exact hall d h
      · rw [List.mem_singleton.mp h]
        exact hpre

/-! ### `GetNext` -/

/-- No step of the path `p` from `c` revisits a read of `c`. -/
def NoRevisitOf (P : Program) (M : Model) {S : Solver} (τ : TieBreak S) (c : Config)
    (p : List Config) : Prop :=
  ∀ l1 l2 d d' e r, c :: p = l1 ++ d :: d' :: l2 → StepL P M τ d e (.rv r) d' → r ∉ c.order

/-- `p` is a segment from `c` towards `Gt`, ending in `c'`: a nonempty path
of the algorithm from `c` to a configuration whose graph extends that of `c`
strictly and is a prefix of `Gt`, with no such configuration strictly inside
and no revisit of a read of `c`. This is what the paper says of the result
of `GetNext(G_s, G_t)`. -/
structure Seg (P : Program) (M : Model) {S : Solver} (τ : TieBreak S) (Gt : Graph)
    (c : Config) (p : List Config) (c' : Config) : Prop where
  path : Maz.Path (Step P M τ) c p c'
  nonempty : p ≠ []
  ext : c.abs.IsPrefixOf c'.abs
  strict : c.abs ≠ c'.abs
  le : c'.abs.IsPrefixOf Gt
  minimal : ∀ d ∈ p.dropLast, ¬ d.abs.IsPrefixOf Gt
  norev : NoRevisitOf P M τ c p

/-- The first state with `Q` on a nonempty path that ends in a state with
`Q`. -/
theorem _root_.Maz.Path.exists_first {α : Type*} {r : α → α → Prop} {Q : α → Prop} {a b : α}
    {p : List α} (h : Maz.Path r a p b) (hne : p ≠ []) (hb : Q b) :
    ∃ p1 p2 m, p = p1 ++ p2 ∧ Maz.Path r a p1 m ∧ Maz.Path r m p2 b ∧ p1 ≠ [] ∧ Q m ∧
      ∀ d ∈ p1.dropLast, ¬ Q d := by
  classical
  induction h with
  | nil => exact absurd rfl hne
  | @cons a x b p hax hxb ih =>
    by_cases hx : Q x
    · exact ⟨[x], p, x, rfl, Maz.Path.cons hax (Maz.Path.nil x), hxb, by simp, hx, by simp⟩
    · have hp : p ≠ [] := by
        rintro rfl
        cases hxb
        exact hx hb
      obtain ⟨p1, p2, m, rfl, h1, h2, hne1, hm, hmin⟩ := ih hp hb
      refine ⟨x :: p1, p2, m, rfl, Maz.Path.cons hax h1, h2, by simp, hm, fun d hd => ?_⟩
      rw [List.dropLast_cons_of_ne_nil hne1] at hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hx
      · exact hmin d hd

/-- A nonempty path ends in its last state. -/
theorem _root_.Maz.Path.mem_of_ne_nil {α : Type*} {r : α → α → Prop} {a b : α} {p : List α}
    (h : Maz.Path r a p b) (hne : p ≠ []) : p.getLast hne = b := by
  induction h with
  | nil => exact absurd rfl hne
  | @cons a x b p hax hxb ih =>
    by_cases hp : p = []
    · subst hp
      cases hxb
      rfl
    · rw [List.getLast_cons hp]
      exact ih hp

/-- A revisit changes the source of the revisited read to the new write, so a
graph that is a prefix before and after the step does not contain the read. -/
theorem StepL.rv_not_mem_of_prefix {c d d' : Config} {e r : TEv}
    (hd : Reach P (M.sym S) τ d) (hs : StepL P (M.sym S) τ d e (.rv r) d')
    (h1 : c.abs.IsPrefixOf d.abs) (h2 : c.abs.IsPrefixOf d'.abs) : r ∉ c.order := by
  intro hr
  obtain ⟨hdw, hdpo, -, -⟩ := hd.sound
  obtain ⟨wp, rfl, H⟩ := hs.rvHyp hdw hdpo
  have hd'W : (d.revisit r e wp).Wf := H.wf'
  -- in the prefix, `r` has its source of the graph after the step
  obtain ⟨s, hsc, hY⟩ := h2
  have hrY : r ∈ c.abs.events := List.mem_toFinset.mpr hr
  have hrs : r ∈ (d.revisit r e wp).abs.events ∩ s := by
    rw [hY] at hrY
    exact hrY
  have hsrc : Ev.th e ∈ Graph.evSet ((d.revisit r e wp).abs.events ∩ s) :=
    hsc (Or.inr ⟨r, rfl, (Finset.mem_inter.mp hrs).1, H.rf_r⟩) hrs
  have heY : e ∈ c.abs.events := by
    rw [hY]
    exact hsrc
  exact H.fresh (List.mem_toFinset.mp (h1.events_subset heY))

/-- G-4, existence. -/
theorem Reach.exists_seg {c ct : Config} (hc : Reach P (M.sym S) τ c)
    (ht : Reach P (M.sym S) τ ct) (hp : c.abs.IsPrefixOf ct.abs) (hne : c.abs ≠ ct.abs) :
    ∃ p c', Seg P (M.sym S) τ ct.abs c p c' ∧ Reach P (M.sym S) τ c' ∧
      ∃ p2, Maz.Path (Step P (M.sym S) τ) c' p2 ct := by
  obtain ⟨π, hπ, hall⟩ := hc.path_of_prefix ht hp
  have hπne : π ≠ [] := by
    rintro rfl
    exact hne (congrArg Config.abs (Maz.Path.nil_iff.mp hπ))
  have htW := ht.sound.1.1
  obtain ⟨p1, p2, m, rfl, h1, h2, hne1, hm, hmin⟩ :=
    hπ.exists_first (Q := fun d => d.abs.IsPrefixOf ct.abs) hπne htW.isPrefixOf_refl
  have hmr : Reach P (M.sym S) τ m := Relation.ReflTransGen.trans hc h1.reflTransGen
  have hmem : m ∈ p1 := by
    rw [← h1.mem_of_ne_nil hne1]
    exact List.getLast_mem hne1
  have hcm : c.abs.IsPrefixOf m.abs := hall m (List.mem_append_left _ hmem)
  refine ⟨p1, m, ⟨h1, hne1, hcm, ?_, hm, hmin, ?_⟩, hmr, p2, h2⟩
  · -- strict: otherwise `c = m`, and the path to `c` followed by `p1` is a
    -- second path to `c`
    intro heq
    have hcm' : c = m := hc.eq_of_abs_eq hmr heq
    subst hcm'
    obtain ⟨p0, hp0⟩ := Maz.Path.of_reflTransGen hc
    have := path_unique hp0 (hp0.append h1) rfl
    have : p1 = [] := by simpa using this
    exact hne1 this
  · intro l1 l2 d d' e r hsplit hs
    -- `d` and `d'` are `c` or on the path, so `c.abs` is a prefix of both
    have hcW := hc.sound.1
    have hin : ∀ x ∈ c :: p1, c.abs.IsPrefixOf x.abs ∧ Reach P (M.sym S) τ x := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hcW.1.isPrefixOf_refl, hc⟩
      · exact ⟨hall x (List.mem_append_left _ hx),
          Relation.ReflTransGen.trans hc (h1.mem_reflTransGen hx).1⟩
    have hd : d ∈ c :: p1 := by rw [hsplit]; simp
    have hd' : d' ∈ c :: p1 := by rw [hsplit]; simp
    exact hs.rv_not_mem_of_prefix (hin d hd).2 (hin d hd).1 (hin d' hd').1

/-- G-4, uniqueness: two segments from `c` towards the graph of a reached
configuration are equal. -/
theorem Seg.unique {c ct c1 c2 : Config} {p1 p2 : List Config}
    (hc : Reach P (M.sym S) τ c) (ht : Reach P (M.sym S) τ ct)
    (h1 : Seg P (M.sym S) τ ct.abs c p1 c1) (h2 : Seg P (M.sym S) τ ct.abs c p2 c2) :
    p1 = p2 ∧ c1 = c2 := by
  obtain ⟨p0, hp0⟩ := Maz.Path.of_reflTransGen hc
  have hr1 : Reach P (M.sym S) τ c1 := Relation.ReflTransGen.trans hc h1.path.reflTransGen
  have hr2 : Reach P (M.sym S) τ c2 := Relation.ReflTransGen.trans hc h2.path.reflTransGen
  obtain ⟨q1, hq1, -⟩ := hr1.path_of_prefix ht h1.le
  obtain ⟨q2, hq2, -⟩ := hr2.path_of_prefix ht h2.le
  have hu := path_unique ((hp0.append h1.path).append hq1) ((hp0.append h2.path).append hq2) rfl
  have hu' : p1 ++ q1 = p2 ++ q2 := by simpa [List.append_assoc] using hu
  -- the shorter of the two is a prefix of the other, and ends inside it
  have key : ∀ {a b : List Config} {qa qb : List Config} {ca cb : Config},
      Seg P (M.sym S) τ ct.abs c a ca → Seg P (M.sym S) τ ct.abs c b cb →
      a ++ qa = b ++ qb → a.length ≤ b.length → a = b := by
    intro a b qa qb ca cb ha hb hab hlen
    obtain ⟨t, rfl⟩ : ∃ t, b = a ++ t := by
      have := List.prefix_of_prefix_length_le (List.prefix_append a qa)
        (hab ▸ List.prefix_append b qb) hlen
      obtain ⟨t, ht⟩ := this
      exact ⟨t, ht.symm⟩
    by_cases htn : t = []
    · simp [htn]
    · exfalso
      have hca : ca ∈ (a ++ t).dropLast := by
        rw [List.dropLast_append_of_ne_nil htn]
        refine List.mem_append_left _ ?_
        rw [← ha.path.mem_of_ne_nil ha.nonempty]
        exact List.getLast_mem ha.nonempty
      exact hb.minimal ca hca ha.le
  have hp : p1 = p2 := by
    rcases Nat.le_total p1.length p2.length with h | h
    · exact key h1 h2 hu' h
    · exact (key h2 h1 hu'.symm h).symm
  subst hp
  refine ⟨rfl, ?_⟩
  rw [← h1.path.mem_of_ne_nil h1.nonempty, ← h2.path.mem_of_ne_nil h1.nonempty]

/-! ### The fixpoint -/

/-- `m` segments towards `Gt` lead from `c` to `c'`; `π` is the concatenation
of their paths. -/
inductive SegChain (P : Program) (M : Model) {S : Solver} (τ : TieBreak S) (Gt : Graph) :
    Config → ℕ → List Config → Config → Prop
  | refl (c : Config) : SegChain P M τ Gt c 0 [] c
  | step {c c' c'' : Config} {p q : List Config} {m : ℕ} :
      Seg P M τ Gt c p c' → SegChain P M τ Gt c' m q c'' →
      SegChain P M τ Gt c (m + 1) (p ++ q) c''

/-- The concatenation of the segments is a path of the algorithm. -/
theorem SegChain.path {Gt : Graph} {c c' : Config} {m : ℕ} {π : List Config}
    (h : SegChain P M τ Gt c m π c') : Maz.Path (Step P M τ) c π c' := by
  induction h with
  | refl c => exact Maz.Path.nil c
  | step hs _ ih => exact hs.path.append ih

/-- G-5. From a reached configuration whose graph is a prefix of the graph of
a reached configuration `c_t`, the segments towards that graph lead to `c_t`;
there are at most as many as missing events. -/
theorem Reach.segChain {c ct : Config} (hc : Reach P (M.sym S) τ c)
    (ht : Reach P (M.sym S) τ ct) (hp : c.abs.IsPrefixOf ct.abs) :
    ∃ m π, SegChain P (M.sym S) τ ct.abs c m π ct ∧
      m ≤ ct.abs.events.card - c.abs.events.card := by
  suffices H : ∀ (n : ℕ) (c : Config), ct.abs.events.card - c.abs.events.card = n →
      Reach P (M.sym S) τ c → c.abs.IsPrefixOf ct.abs →
      ∃ m π, SegChain P (M.sym S) τ ct.abs c m π ct ∧ m ≤ n from H _ c rfl hc hp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hn hc hp
    by_cases heq : c.abs = ct.abs
    · have := hc.eq_of_abs_eq ht heq
      subst this
      exact ⟨0, [], SegChain.refl _, Nat.zero_le _⟩
    · obtain ⟨p, c', hseg, hc', -⟩ := hc.exists_seg ht hp heq
      have hlt : c.abs.events.card < c'.abs.events.card :=
        hseg.ext.card_lt hc'.sound.1.1 hseg.strict
      have hle : c'.abs.events.card ≤ ct.abs.events.card :=
        Finset.card_le_card hseg.le.events_subset
      obtain ⟨m, π, hm, hmle⟩ := ih (ct.abs.events.card - c'.abs.events.card) (by omega) c' rfl
        hc' hseg.le
      exact ⟨m + 1, p ++ π, SegChain.step hseg hm, by omega⟩

/-- Two chains of segments from a reached configuration towards the graph of
a reached configuration, with the same end, are equal. -/
theorem SegChain.unique {c ct z : Config} {m1 m2 : ℕ} {π1 π2 : List Config}
    (hc : Reach P (M.sym S) τ c) (ht : Reach P (M.sym S) τ ct)
    (h1 : SegChain P (M.sym S) τ ct.abs c m1 π1 z)
    (h2 : SegChain P (M.sym S) τ ct.abs c m2 π2 z) : m1 = m2 ∧ π1 = π2 := by
  -- a chain with a segment does not return to its start
  have nocycle : ∀ {c : Config} {m : ℕ} {π : List Config}, Reach P (M.sym S) τ c →
      SegChain P (M.sym S) τ ct.abs c (m + 1) π c → False := by
    intro c m π hc h
    obtain ⟨p0, hp0⟩ := Maz.Path.of_reflTransGen hc
    cases h with
    | step hs hrest =>
      have := path_unique hp0 (hp0.append (hs.path.append hrest.path)) rfl
      have h' := congrArg List.length this
      simp only [List.length_append] at h'
      exact hs.nonempty (List.length_eq_zero_iff.mp (by omega))
  induction h1 generalizing m2 π2 with
  | refl c =>
    cases h2 with
    | refl => exact ⟨rfl, rfl⟩
    | step hs hrest => exact (nocycle hc (SegChain.step hs hrest)).elim
  | @step c c' c'' p q m hs hrest ih =>
    cases h2 with
    | refl => exact (nocycle hc (SegChain.step hs hrest)).elim
    | step hs' hrest' =>
      obtain ⟨rfl, rfl⟩ := Seg.unique hc ht hs hs'
      have hc' : Reach P (M.sym S) τ c' := Relation.ReflTransGen.trans hc hs.path.reflTransGen
      obtain ⟨rfl, rfl⟩ := ih hc' hrest'
      exact ⟨rfl, rfl⟩

/-- G-5 for an execution of `⟦P⟧`: "calling `GetNext` in a fixpoint" from the
initial configuration leads to it, in at most as many rounds as it has
events; the concatenation of the segments is the only path of the algorithm
to it. -/
theorem getNext_fixpoint {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible) {Gf : Graph}
    (hGf : Gf.Wf) (hEf : P.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.Full Gf) :
    ∃ cf m π, Reach P (M.sym S) τ cf ∧ cf.abs = Gf ∧
      SegChain P (M.sym S) τ Gf (Config.init P.mem) m π cf ∧ m ≤ Gf.events.card ∧
      ∀ π' c', Maz.Path (Step P (M.sym S) τ) (Config.init P.mem) π' c' → c'.abs = Gf →
        π' = π := by
  obtain ⟨cf, hcf', rfl⟩ := complete (τ := τ) hn hM hGf hEf hcf hff
  have h0 : Reach P (M.sym S) τ (Config.init P.mem) := Relation.ReflTransGen.refl
  have hpre : (Config.init P.mem).abs.IsPrefixOf cf.abs := by
    rw [Config.init_abs, ← hEf.1]
    exact Graph.init_isPrefixOf _
  obtain ⟨m, π, hm, hle⟩ := h0.segChain hcf' hpre
  exact ⟨cf, m, π, hcf', rfl, hm, le_trans hle (Nat.sub_le _ _),
    fun π' c' hπ' hc' => path_unique hπ' hm.path hc'⟩

/-! ### The prefix order by steps

In the proof document of the paper's reference for this framework, `G ⊑ G'`
iff `G'` is obtained from `G` by operational steps: add an available event, a
read with any source, a write at any place. For well-formed executions this
is `IsPrefixOf`. The ConDpor paper prints "non-revisit steps of the
algorithm" instead; that order is smaller (`NrLe`). -/

/-- An operational step: `G'` extends `G` by one available event. A read
gets any source and a write any place. The step is not written as the three
updates `addRead`, `addWrite`, `addLoc`: `G'` is any well-formed graph with
the new event whose restriction to the old events is `G` (so the old sources,
the order of the old writes and the old outcomes are kept). The three updates
are such steps (`OpStep.addRead`, `OpStep.addWrite`, `OpStep.addLoc`); the
converse is not stated. -/
def OpStep (P : Program) (G G' : Graph) : Prop :=
  G'.Wf ∧ ∃ e ∈ P.avail G, G'.events = insert e G.events ∧ G = G'.restrict G.events

/-- The prefix order by operational steps. -/
def OpLe (P : Program) (G G' : Graph) : Prop := Relation.ReflTransGen (OpStep P) G G'

theorem OpStep.isPrefixOf {G G' : Graph} (hG : G.Wf) (h : OpStep P G G') : G.IsPrefixOf G' := by
  obtain ⟨hG', e, -, hev, hres⟩ := h
  refine Graph.isPrefixOf_of_restrict_eq hG' hG hres (fun q hq => ?_)
  cases hrf : G'.rf q with
  | none =>
    have h1 : G.rf q = (G'.restrict G.events).rf q := congrArg (fun g => g.rf q) hres
    have hq' : q ∈ G'.events ∩ G.events :=
      Finset.mem_inter.mpr ⟨hev ▸ Finset.mem_insert_of_mem hq, hq⟩
    rw [h1, G'.restrict_rf_of_mem hq', hrf]
  | some w => exact ((rf_of_restrict_eq hG hG' hres hq hrf).1).symm

/-- The three updates of the algorithm are operational steps. -/
theorem OpStep.addRead {G : Graph} (hG : G.Wf) {e : TEv} {x : Loc} {w : Ev}
    (he : e ∈ P.avail G) (hact : e.act = .read x) (hw : G.IsWriteTo x w) :
    OpStep P G (G.addRead e w) := by
  have hidx := idx_eq_of_mem_avail he
  have hne := hG.not_mem_of_idx_eq_cnt hidx
  exact ⟨hG.addRead hidx hact hw, e, he, rfl, (Graph.restrict_addRead hG hne).symm⟩

theorem OpStep.addWrite {G : Graph} (hG : G.Wf) {e : TEv} {wp : Ev}
    (he : e ∈ P.avail G) (hact : e.IsWrite) (hwp : G.IsWriteTo e.loc wp) :
    OpStep P G (G.addWrite e wp) := by
  have hidx := idx_eq_of_mem_avail he
  have hne := hG.not_mem_of_idx_eq_cnt hidx
  exact ⟨hG.addWrite hidx hact hwp, e, he, rfl, (Graph.restrict_addWrite hG hne).symm⟩

theorem OpStep.addLoc {G : Graph} (hG : G.Wf) {e : TEv} {o : Option Bool}
    (he : e ∈ P.avail G) (hact : e.IsLocal) (ho : o.isSome ↔ e.IsCons) :
    OpStep P G (G.addLoc e o) := by
  have hidx := idx_eq_of_mem_avail he
  have hne := hG.not_mem_of_idx_eq_cnt hidx
  exact ⟨hG.addLoc hidx hact ho, e, he, rfl, (Graph.restrict_addLoc hG hne).symm⟩

theorem OpLe.isPrefixOf {G G' : Graph} (hG : G.Wf) (h : OpLe P G G') :
    G.IsPrefixOf G' ∧ G'.Wf := by
  induction h with
  | refl => exact ⟨hG.isPrefixOf_refl, hG⟩
  | tail _ hs ih => exact ⟨ih.1.trans (hs.isPrefixOf ih.2), hs.1⟩

/-- A prefix of a well-formed execution without a causality cycle is below
it in the order by operational steps. -/
theorem OpLe.of_isPrefixOf {Y X : Graph} (hX : X.Wf) (hE : P.Exec X)
    (hac : Maz.Acyclic X.porfStep) (hp : Y.IsPrefixOf X) : OpLe P Y X := by
  classical
  suffices H : ∀ (n : ℕ) (X : Graph), X.events.card - Y.events.card = n → X.Wf → P.Exec X →
      Maz.Acyclic X.porfStep → Y.IsPrefixOf X → OpLe P Y X from H _ X rfl hX hE hac hp
  intro n
  induction n with
  | zero =>
    intro X hn hX hE hac hp
    have hle := Finset.card_le_card hp.events_subset
    have hsub : X.events ⊆ Y.events := by
      by_contra hns
      have := Finset.card_lt_card ⟨hp.events_subset, hns⟩
      omega
    rw [hp.eq_of_subset hX hsub]
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro X hn hX hE hac hp
    obtain ⟨b, hbX, hbY⟩ : ∃ b ∈ X.events, b ∉ Y.events := by
      by_contra hall
      push Not at hall
      have : Y.events.card = X.events.card :=
        le_antisymm (Finset.card_le_card hp.events_subset) (Finset.card_le_card hall)
      omega
    obtain ⟨z, hzX, hzr, hzmax⟩ := Graph.exists_maximal_reach hX hac hbX
    obtain ⟨s, hsc, hY⟩ := hp
    have hYev : Y.events = X.events ∩ s := by rw [hY]; rfl
    have hzY : z ∉ Y.events := by
      intro h
      rcases hzr with rfl | hr
      · exact hbY h
      · have : Ev.th b ∈ Graph.evSet (X.events ∩ s) :=
          Graph.prefixClosed_porf hsc hr (hYev ▸ h)
        have this' : b ∈ X.events ∩ s := this
        exact hbY (hYev ▸ this')
    have hmax' : ∀ x, ¬ X.porfStep (.th z) x := fun x hx => hzmax x (Relation.TransGen.single hx)
    have hEv : X.events ∩ X.events.erase z = X.events.erase z :=
      Finset.inter_eq_right.mpr (Finset.erase_subset _ _)
    have hpre : Maz.PrefixClosed X.porfStep (Graph.evSet (X.events ∩ X.events.erase z)) := by
      intro a b hab _
      rw [hEv]
      cases a with
      | init => trivial
      | th q =>
        have hq := (hX.mem_of_porfStep hab).1
        refine Finset.mem_erase.mpr ⟨?_, hq⟩
        intro hqe
        rw [hqe] at hab
        exact hmax' _ hab
    have hX0 : (X.restrict (X.events.erase z)).Wf := hX.restrict hpre
    have hpre0 : (X.restrict (X.events.erase z)).IsPrefixOf X := ⟨_, hpre, rfl⟩
    have hE0 : P.Exec (X.restrict (X.events.erase z)) := hE.of_isPrefixOf hX hpre0
    have hac0 : Maz.Acyclic (X.restrict (X.events.erase z)).porfStep := by
      intro a haa
      have ham : a ∈ Graph.evSet (X.events ∩ X.events.erase z) := by
        obtain ⟨c, _, hca⟩ := Relation.TransGen.tail'_iff.mp haa
        exact (hX0.mem_of_porfStep hca).2
      exact hac a ((Graph.porf_restrict_iff hpre ham).mp haa)
    have hevs : (X.restrict (X.events.erase z)).events = X.events.erase z := hEv
    have hYsub : Y.events ⊆ (X.restrict (X.events.erase z)).events := by
      intro q hq
      rw [hevs]
      refine Finset.mem_erase.mpr ⟨fun h => hzY (h ▸ hq), ?_⟩
      rw [hYev] at hq
      exact (Finset.mem_inter.mp hq).1
    have hY0 : Y.IsPrefixOf (X.restrict (X.events.erase z)) :=
      Graph.IsPrefixOf.of_subset hX ⟨s, hsc, hY⟩ hpre0 hYsub
    have hcard : (X.restrict (X.events.erase z)).events.card - Y.events.card = n := by
      rw [hevs, Finset.card_erase_of_mem hzX]
      omega
    have h0 := ih _ hcard hX0 hE0 hac0 hY0
    refine Relation.ReflTransGen.tail h0 ⟨hX, z, ?_, ?_, ?_⟩
    · refine mem_avail_restrict hX hE hzX (fun h => (Finset.mem_erase.mp h).1 rfl)
        (fun q hq _ hi => Finset.mem_erase.mpr ⟨fun h => by rw [h] at hi; omega, hq⟩)
        (fun q hq _ _ w hw => ?_) hX0
      cases w with
      | init => trivial
      | th w0 =>
        have hstep : X.porfStep (.th w0) (.th q) := Or.inr ⟨q, rfl, hq, hw⟩
        refine Finset.mem_erase.mpr ⟨?_, (hX.mem_of_porfStep hstep).1⟩
        intro hwe
        rw [hwe] at hstep
        exact hmax' _ hstep
    · rw [hevs]
      exact (Finset.insert_erase hzX).symm
    · rw [hevs]

/-- G-1: on well-formed executions without a causality cycle, the order by
operational steps is the prefix order. -/
theorem opLe_iff_isPrefixOf {Y X : Graph} (hY : Y.Wf) (hX : X.Wf) (hE : P.Exec X)
    (hac : Maz.Acyclic X.porfStep) : OpLe P Y X ↔ Y.IsPrefixOf X :=
  ⟨fun h => (h.isPrefixOf hY).1, OpLe.of_isPrefixOf hX hE hac⟩

/-- The order as the paper prints it: some configuration with graph `G`
reaches some configuration with graph `G'` by non-revisit steps of the
algorithm. -/
def NrLe (P : Program) (M : Model) {S : Solver} (τ : TieBreak S) (G G' : Graph) : Prop :=
  ∃ c c', c.abs = G ∧ c'.abs = G' ∧
    Relation.ReflTransGen (fun c c' => ∃ e, StepL P M τ c e .nr c') c c'

/-- A non-revisit step is an operational step. -/
theorem StepL.opStep {c c' : Config} {e : TEv} (hc : c.abs.Wf) (h : StepL P M τ c e .nr c') :
    OpStep P c.abs c'.abs := by
  obtain ⟨-, hnext, hcase⟩ := h.nr_inv
  rcases hcase with ⟨x, w, hact, hw, rfl⟩ | ⟨wp, hact, hwp, rfl⟩ | ⟨b, hact, rfl⟩ | ⟨hl, hnc, rfl⟩
  · rw [Config.addRead_abs]
    exact OpStep.addRead hc hnext.1 hact hw
  · rw [Config.addWrite_abs]
    exact OpStep.addWrite hc hnext.1 hact hwp
  · rw [Config.addLoc_abs]
    exact OpStep.addLoc hc hnext.1 hact.isLocal (by simp [hact])
  · rw [Config.addLoc_abs]
    exact OpStep.addLoc hc hnext.1 hl (by simp [hnc])

/-- The printed order is contained in the prefix order. -/
theorem NrLe.opLe {G G' : Graph} (hG : G.Wf) (h : NrLe P M τ G G') : OpLe P G G' := by
  obtain ⟨c, c', rfl, rfl, hsteps⟩ := h
  have key : OpLe P c.abs c'.abs ∧ c'.abs.Wf := by
    induction hsteps with
    | refl => exact ⟨Relation.ReflTransGen.refl, hG⟩
    | tail _ hs ih =>
      obtain ⟨e, hs⟩ := hs
      have hop := hs.opStep ih.2
      exact ⟨Relation.ReflTransGen.tail ih.1 hop, hop.1⟩
  exact key.1

end Condpor
