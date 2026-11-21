import Mazurkiewicz.Condpor.Rf.Canon
import Mazurkiewicz.Condpor.Optimal

/-!
# The reads-from version of the algorithm

TruSt, Section 4.2, Algorithm 2, with the symbolic events of ConDpor ("our
algorithm works both under the Shasha-Snir and the reads-from equivalence
partitioning … the required changes can be adapted from [TruSt]").

The configurations are those of `Alg.lean` with a canonical coherence order
(`Rf/Canon.lean`); consistency is `M.rf`: some coherence order makes the graph
`M`-consistent. A step `StepR`:

* `nr`: a non-revisit step of `Alg.lean` for the model `M.rf` whose result is
  canonical. For a write this leaves one successor (`VisitCOs` "boils down to
  a `Visit` call"): the consistency check does not see the place of the
  write, and one place is canonical.
* `rv`: the revisit of the read `r` by the new write `w`. The deleted events
  and `r` must be maximally added in the sense of `Alg.lean`, for the
  coherence order of line 16 of Algorithm 2 (`Config.star`): the order that
  `γ` (`GetConsCO`) chooses for the kept events, followed by the deleted
  writes in insertion order. The result is the canonical form of the result
  of `Alg.lean`.

Difference from the printed line 16: `γ` is applied to the kept events
*without* `r`. With `r`, the chosen order may depend on the source that `r`
has before the revisit, which the graph after the revisit does not contain,
and one graph is visited twice (plan, Section 3.2).
-/

namespace Condpor

open Program

variable {P : Program} {M : Model} {S : Solver} {τ : TieBreak S} {γ : CoChoice M}

/-! ### Consistency does not depend on coherence -/

theorem Graph.RfEq.withCo_eq {G G' : Graph} (h : G.RfEq G') (co : Loc → List TEv) :
    G.withCo co = G'.withCo co := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  apply Graph.ext
  · exact h1
  · exact h2
  · exact h3
  · rfl
  · exact h4

theorem Model.rf_cons_congr {G G' : Graph} (h : G.RfEq G') : M.rf.cons G ↔ M.rf.cons G' := by
  constructor
  · rintro ⟨co, hW, hc⟩
    exact ⟨co, h.withCo_eq co ▸ hW, h.withCo_eq co ▸ hc⟩
  · rintro ⟨co, hW, hc⟩
    exact ⟨co, (h.withCo_eq co).symm ▸ hW, (h.withCo_eq co).symm ▸ hc⟩

/-! ### The coherence order of line 16 -/

namespace Config

/-- The graph of the kept events without the revisited read. -/
noncomputable def kept0 (c : Config) (r w : TEv) : Graph :=
  c.abs.restrict (c.keep r w \ {r})

/-- The configuration with the coherence order of line 16 of Algorithm 2 for
the revisit of `r` by `w`: the order chosen for the kept events without `r`,
then the deleted writes in insertion order. -/
noncomputable def starCo (γ : CoChoice M) (c : Config) (r w : TEv) (x : Loc) : List TEv :=
  open Classical in
  γ.co (c.kept0 r w) x ++
    c.order.reverse.filter (fun d => decide (c.Deleted r w d) && d.writesTo x)

@[inherit_doc starCo]
noncomputable def star (γ : CoChoice M) (c : Config) (r w : TEv) : Config :=
  c.withCo (c.starCo γ r w)

@[simp] theorem star_order (c : Config) (r w : TEv) : (c.star γ r w).order = c.order := rfl
@[simp] theorem star_rf (c : Config) (r w : TEv) : (c.star γ r w).rf = c.rf := rfl
@[simp] theorem star_pol (c : Config) (r w : TEv) : (c.star γ r w).pol = c.pol := rfl

theorem star_rfEq (c : Config) (r w : TEv) : (c.star γ r w).abs.RfEq c.abs := ⟨rfl, rfl, rfl, rfl⟩

/-- Line 25 of Algorithm 1 for the deleted events gives: the source of every
kept read is kept. (`Config.keep_sources`, from line 25 alone.) -/
theorem keep_sources' {c : Config} {r w : TEv} (hc : c.Wf)
    (h25 : ∀ e, c.Deleted r w e → ¬ ∃ q, c.Previous e w (.th q) ∧ c.rf q = some (.th e))
    {q : TEv} (hq : q ∈ c.abs.events ∩ c.keep r w) {s : Ev} (hs : c.abs.rf q = some s) :
    s ∈ Graph.evSet (c.keep r w) := by
  cases s with
  | init => trivial
  | th s0 =>
    have hqo : q ∈ c.order := List.mem_toFinset.mp (Finset.mem_inter.mp hq).1
    have hs0 : s0 ∈ c.order := List.mem_toFinset.mp (hc.1.rf_source_mem hs).2
    have hnd : ¬ c.Deleted r w q := ((Config.mem_keep_iff c r w q).mp (Finset.mem_inter.mp hq).2).2
    change s0 ∈ c.keep r w
    rw [Config.mem_keep_iff]
    refine ⟨hs0, fun hd => ?_⟩
    refine h25 s0 hd ⟨q, ⟨hqo, ?_⟩, hs⟩
    by_cases hpf : (c.plus w).porf (.th q) (.th w)
    · exact Or.inr hpf
    · left
      have hnlt : ¬ c.lt r q := fun h => hnd ⟨hqo, h, hpf⟩
      have hr : r ∈ c.order := hd.2.1.2.1
      by_cases hqr : q = r
      · exact Or.inr (hqr ▸ hd.2.1)
      · rcases List.Before.total hqo hr hqr with h | h
        · exact absurd h hnlt
        · exact Or.inr (List.Before.trans hd.2.1 h)

/-- The kept events without `r` are closed under causal predecessors. -/
theorem kept0_closed {c : Config} {r w : TEv} (hc : c.Wf) (hpo : c.PoLt) (hr : r ∈ c.order)
    (hrR : r.IsRead) (hnp : ¬ (c.plus w).porf (.th r) (.th w))
    (h25 : ∀ e, c.Deleted r w e → ¬ ∃ q, c.Previous e w (.th q) ∧ c.rf q = some (.th e)) :
    Maz.PrefixClosed c.abs.porfStep (Graph.evSet (c.abs.events ∩ (c.keep r w \ {r}))) := by
  intro a b hab hb
  cases b with
  | init => exact absurd hab (c.abs.not_porfStep_init a)
  | th q =>
    have hq : q ∈ c.abs.events ∩ (c.keep r w \ {r}) := hb
    obtain ⟨hqE, hqk⟩ := Finset.mem_inter.mp hq
    obtain ⟨hqk, hqr⟩ := Finset.mem_sdiff.mp hqk
    have hqk' : q ∈ c.abs.events ∩ c.keep r w := Finset.mem_inter.mpr ⟨hqE, hqk⟩
    cases a with
    | init => trivial
    | th p =>
      rcases hab with hpo' | ⟨q', hq', -, hrf⟩
      · have hp : p ∈ c.abs.events ∩ c.keep r w :=
          Config.keep_po_closed hpo hpo' hqk'
        refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hp).1,
          Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hp).2, ?_⟩⟩
        intro hpr
        have hpr' : p = r := Finset.mem_singleton.mp hpr
        have := Config.keep_last hpo hr hnp hqk (hpr' ▸ hpo'.2.2.1).symm
        have hlt := hpo'.2.2.2
        rw [hpr'] at hlt
        omega
      · cases hq'
        have hp := keep_sources' hc h25 hqk' hrf
        have hpE : p ∈ c.abs.events := (hc.1.rf_source_mem hrf).2
        refine Finset.mem_inter.mpr ⟨hpE, Finset.mem_sdiff.mpr ⟨hp, ?_⟩⟩
        intro hpr
        have hpr' : p = r := Finset.mem_singleton.mp hpr
        exact TEv.not_isRead_of_isWrite (hc.1.isWrite_of_src hrf) (hpr' ▸ hrR)

theorem kept0_wf {c : Config} {r w : TEv} (hc : c.Wf) (hpo : c.PoLt) (hr : r ∈ c.order)
    (hrR : r.IsRead) (hnp : ¬ (c.plus w).porf (.th r) (.th w))
    (h25 : ∀ e, c.Deleted r w e → ¬ ∃ q, c.Previous e w (.th q) ∧ c.rf q = some (.th e)) :
    (c.kept0 r w).Wf :=
  hc.1.restrict (kept0_closed hc hpo hr hrR hnp h25)

/-- B2: the configuration with the order of line 16 is well-formed. -/
theorem star_wf {c : Config} {r w : TEv} (hc : c.Wf) (hrR : r.IsRead)
    (hK : (c.kept0 r w).Wf) : (c.star γ r w).Wf := by
  classical
  have hγ := γ.wf (c.kept0 r w) hK
  refine ⟨hc.1.withCo (co := c.starCo γ r w) (fun x e => ?_) (fun x => ?_), hc.2⟩
  · simp only [starCo, List.mem_append, List.mem_filter, List.mem_reverse, Bool.and_eq_true,
      decide_eq_true_eq, TEv.writesTo_iff]
    have h1 : e ∈ γ.co (c.kept0 r w) x ↔
        e ∈ (c.kept0 r w).events ∧ ∃ v, e.act = .write x v := hγ.co_mem x e
    rw [h1]
    constructor
    · rintro (⟨he, hw⟩ | ⟨he, -, hw⟩)
      · exact ⟨(Finset.mem_inter.mp he).1, hw⟩
      · exact ⟨List.mem_toFinset.mpr he, hw⟩
    · rintro ⟨he, hw⟩
      have heo : e ∈ c.order := List.mem_toFinset.mp he
      by_cases hd : c.Deleted r w e
      · exact Or.inr ⟨heo, hd, hw⟩
      · left
        refine ⟨Finset.mem_inter.mpr ⟨he, Finset.mem_sdiff.mpr
          ⟨(Config.mem_keep_iff c r w e).mpr ⟨heo, hd⟩, ?_⟩⟩, hw⟩
        intro her
        have her' : e = r := Finset.mem_singleton.mp her
        obtain ⟨v, hv⟩ := hw
        rw [her'] at hv
        simp [TEv.IsRead, hv, Act.IsRead] at hrR
  · unfold starCo
    refine List.Nodup.append (hγ.co_nodup x) ((List.nodup_reverse.mpr hc.2).filter _) ?_
    intro e he1 he2
    have h1 : e ∈ (c.kept0 r w).events := ((hγ.co_mem x e).mp he1).1
    have hk : e ∈ c.keep r w := (Finset.mem_sdiff.mp (Finset.mem_inter.mp h1).2).1
    have hd : c.Deleted r w e := by
      have := (List.mem_filter.mp he2).2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    exact ((Config.mem_keep_iff c r w e).mp hk).2 hd

end Config

/-! ### The algorithm -/

/-- A step of the reads-from version, labelled with the added event and the
kind of the step. `M` is the model with coherence (the theorems take
`M = M₀.sym S`); the algorithm checks `M.rf`. `γ` is `GetConsCO`. -/
inductive StepR (P : Program) (M : Model) (γ : CoChoice M) {S : Solver} (τ : TieBreak S) :
    Config → TEv → Kind → Config → Prop
  /-- a plain addition whose result is canonical -/
  | nr {c c' : Config} {e : TEv} :
      StepL P M.rf τ c e .nr c' → c'.abs.IsCanon → StepR P M γ τ c e .nr c'
  /-- the next event is a write that revisits a read -/
  | rv {c : Config} {w r : TEv} :
      M.rf.cons c.abs → P.IsNext c.abs w → w.IsWrite → r ∈ c.order → r.act = .read w.loc →
      ¬ (c.plus w).porf (.th r) (.th w) →
      (∀ e, (c.Deleted r w e ∨ e = r) →
        (c.star γ r w).IsMaximallyAdded τ (c.ctx r w) e w) →
      M.rf.cons (c.revisit r w .init).canon.abs →
      StepR P M γ τ c w (.rv r) (c.revisit r w .init).canon

/-- A step of the reads-from version. -/
def StepRf (P : Program) (M : Model) (γ : CoChoice M) {S : Solver} (τ : TieBreak S)
    (c c' : Config) : Prop := ∃ e k, StepR P M γ τ c e k c'

/-- The configurations that the reads-from version reaches. -/
def ReachR (P : Program) (M : Model) (γ : CoChoice M) {S : Solver} (τ : TieBreak S)
    (c : Config) : Prop :=
  Relation.ReflTransGen (StepRf P M γ τ) (Config.init P.mem) c

theorem StepR.rv_inv {c c' : Config} {w r : TEv} (h : StepR P M γ τ c w (.rv r) c') :
    c' = (c.revisit r w .init).canon ∧ M.rf.cons c.abs ∧ P.IsNext c.abs w ∧ w.IsWrite ∧
      r ∈ c.order ∧ r.act = .read w.loc ∧ ¬ (c.plus w).porf (.th r) (.th w) ∧
      (∀ e, (c.Deleted r w e ∨ e = r) →
        (c.star γ r w).IsMaximallyAdded τ (c.ctx r w) e w) ∧
      M.rf.cons (c.revisit r w .init).canon.abs := by
  cases h with
  | rv h0 h1 h2 h3 h4 h5 h6 h7 => exact ⟨rfl, h0, h1, h2, h3, h4, h5, h6, h7⟩

theorem StepR.nr_inv {c c' : Config} {e : TEv} (h : StepR P M γ τ c e .nr c') :
    StepL P M.rf τ c e .nr c' ∧ c'.abs.IsCanon := by
  cases h with
  | nr h1 h2 => exact ⟨h1, h2⟩

/-- A revisit of the reads-from version from `c` is a revisit of `Alg.lean`
from `c` with the coherence order of line 16, for the model `M.rf`; the
result of the former is the canonical form of the result of the latter. -/
theorem StepR.lift {c c' : Config} {w r : TEv} (hc : c.Wf) (hpo : c.PoLt)
    (h : StepR P M γ τ c w (.rv r) c') :
    (c.star γ r w).Wf ∧
      StepL P M.rf τ (c.star γ r w) w (.rv r) ((c.star γ r w).revisit r w .init) ∧
      c' = ((c.star γ r w).revisit r w .init).canon := by
  obtain ⟨rfl, h0, h1, h2, h3, h4, h5, h6, h7⟩ := h.rv_inv
  have hrR : r.IsRead := by simp [TEv.IsRead, h4, Act.IsRead]
  have h25 : ∀ e, c.Deleted r w e → ¬ ∃ q, c.Previous e w (.th q) ∧ c.rf q = some (.th e) :=
    fun e he => (h6 e (Or.inl he)).1
  have hK := Config.kept0_wf hc hpo h3 hrR h5 h25
  have hsW : (c.star γ r w).Wf := Config.star_wf hc hrR hK
  refine ⟨hsW, StepL.revisit h0 h1 h2 h3 h4 h5 h6 trivial ?_, rfl⟩
  exact (Model.rf_cons_congr ⟨rfl, rfl, rfl, rfl⟩).mp h7

/-- Soundness: every reached configuration is well-formed and canonical, its
insertion order extends the program order, and its graph is an execution of
the program that is consistent for some coherence order. -/
theorem ReachR.sound {c : Config} (h : ReachR P M γ τ c) :
    c.Wf ∧ c.PoLt ∧ c.abs.IsCanon ∧ M.rf.cons c.abs ∧ P.Exec c.abs := by
  unfold ReachR at h
  induction h with
  | refl =>
    refine ⟨Config.init_wf _, Config.init_poLt _, ?_, ?_, ?_⟩
    · rw [Config.init_abs]
      funext x
      simp [Graph.init, canonCo]
    · rw [Config.init_abs]
      exact M.rf.cons_init _
    · rw [Config.init_abs]
      exact Program.exec_init P
  | tail _ hs ih =>
    obtain ⟨hw, hpo, _, _, hE⟩ := ih
    obtain ⟨e, k, hs⟩ := hs
    cases k with
    | nr =>
      obtain ⟨hl, hcan⟩ := hs.nr_inv
      exact ⟨hl.wf hw hpo, hl.poLt hw hpo, hcan, hl.cons, hl.exec hw hpo hE⟩
    | rv r =>
      obtain ⟨hsW, hl, rfl⟩ := hs.lift hw hpo
      have hw' := hl.wf hsW hpo
      have hpo' := hl.poLt hsW hpo
      refine ⟨⟨hw'.1.canon, hw'.2⟩, hpo', ?_,
        (Model.rf_cons_congr (Graph.rfEq_canon _)).mp hl.cons, ?_⟩
      · rw [Config.canon_abs]
        exact Graph.canon_isCanon _
      · rw [Config.canon_abs]
        exact (Program.exec_withCo P _ _).mpr (hl.exec hsW hpo hE)

end Condpor
