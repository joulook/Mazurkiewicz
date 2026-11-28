import Mazurkiewicz.Jmt.Lazy

/-!
# Exploration of lazy states

This file defines the *candidates* and the *parent* of a lazy state and
proves that exploring lazy steps only along parents visits every reachable
lazy state exactly once.

A candidate of `l'` is a reachable lazy state `l` with a lazy step `l ⇝ l'`.
Its batch is `unj(l'.E) \ unj(l.E)`, its obligations agree with those of `l'`
on `unj(l.E)`, and its frozen edges are among those of `l'`
(`IsCand.unj_eq`, `IsCand.obl_eq`, `IsCand.Z_subset`). The obligation map of
`LState` is total, while in a lazy state of the paper it is defined on the
unjustified reads only; lazy states, lazy steps and reachability do not depend
on the values outside the unjustified reads (`LStep.congr_src`,
`LStep.congr_tgt`, `LReach.congr`).

A parent function is specified abstractly (`IsParent`): its value at `l'` is a
candidate of `l'`, and it is defined whenever `l'` has a candidate.
`lparent` is the parent of the paper: for a fixed well-order on triples
`(B, E, Z)`, the candidate with the least triple whose obligation map is that
of `l'` (`lparent_isParent`, `lparent_least`).

Termination needs finitely many unjustified reads; as in `Jmt.lazy`, this
comes from `KExec.Regular` executions.

Main statements:

* `Jmt.IsParent.lreach_iff`: a lazy state that is not initial is reachable iff
  its parent is defined.
* `Jmt.IsCand.ncard_lt`, `Jmt.IsParent.wf`, `Jmt.IsParent.iterate_init`: the
  parent has fewer unjustified reads, and iterating the parent from a
  reachable state ends in an initial state.
* `Jmt.IsParent.visit_iff`: the visited states are the reachable states.
* `Jmt.VisitPath.unique`, `Jmt.IsParent.lreach_iff_existsUnique`: each
  reachable state is visited along exactly one path from an initial state.
* `Jmt.IsParent.valid_iff_visit`: the executions of the visited states are the
  valid executions.
-/

namespace Jmt

open Set

variable {Key Val : Type*} {Ex : Set (KExec Key Val)} {init : Key}

/-! ## Lazy steps -/

/-- The batch of a lazy step is determined by its source and target:
`B = unj(E⁺) \ unj(E)`. -/
theorem LStep.batch_eq {l l' : LState Key Val} {B : Set Key} (h : LStep Ex init l l' B) :
    B = l'.E.unj \ l.E.unj := by
  rw [h.unj_eq, Set.union_sdiff_left]
  exact h.disj.symm.sdiff_eq_left.symm

/-- The unjustified reads of the source of a lazy step: `unj(E) = unj(E⁺) \ B`. -/
theorem LStep.unj_src {l l' : LState Key Val} {B : Set Key} (h : LStep Ex init l l' B) :
    l.E.unj = l'.E.unj \ B := by
  rw [h.unj_eq, Set.union_sdiff_right]
  exact h.disj.sdiff_eq_left.symm

/-- The batch of a lazy step consists of unjustified reads of the target. -/
theorem LStep.batch_subset {l l' : LState Key Val} {B : Set Key}
    (h : LStep Ex init l l' B) : B ⊆ l'.E.unj := by
  rw [h.unj_eq]
  exact Set.subset_union_right

/-- The unjustified reads of the source of a lazy step are a proper subset of
those of the target. -/
theorem LStep.unj_ssubset {l l' : LState Key Val} {B : Set Key}
    (h : LStep Ex init l l' B) : l.E.unj ⊂ l'.E.unj := by
  rw [h.unj_eq]
  refine Set.ssubset_iff_subset_ne.2 ⟨Set.subset_union_left, fun he => ?_⟩
  obtain ⟨r, hr⟩ := h.ne
  have hr' : r ∈ l.E.unj := by rw [he]; exact Or.inr hr
  exact Set.disjoint_left.1 h.disj hr' hr

/-- The frozen edges of the source of a lazy step are frozen edges of the
target, by (F8) along the chain of stage steps. -/
theorem LStep.Z_subset {l l' : LState Key Val} {B : Set Key} (h : LStep Ex init l l' B) :
    l.Z ⊆ l'.Z := by
  obtain ⟨k, σ, h0, -, -, -, hlast, hsteps⟩ := h.chain
  have hz : ∀ j ≤ k + 2, l.Z ⊆ (σ j).Z := by
    intro j hj
    induction j with
    | zero => rw [h0]
    | succ j ih =>
      rw [(hsteps j (by omega)).f8]
      exact (ih (by omega)).trans Set.subset_union_left
  have := hz (k + 2) le_rfl
  rwa [hlast] at this

/-- A lazy state with unjustified reads, in particular a lazy state that is
the target of a lazy step, is not initial. -/
theorem LStep.not_isLInit {l l' : LState Key Val} {B : Set Key}
    (h : LStep Ex init l l' B) : ¬ IsLInit Ex init l' := by
  rintro ⟨-, hu, -⟩
  obtain ⟨r, hr⟩ := h.ne
  have := h.batch_subset hr
  rw [hu] at this
  exact this

/-- A reachable lazy state is a lazy state. -/
theorem LReach.isLazy {l : LState Key Val} (h : LReach Ex init l) : IsLazy Ex init l := by
  obtain ⟨l₀, h₀, hst⟩ := h
  cases hst with
  | refl => exact h₀.1
  | tail _ hstep =>
    obtain ⟨B, hB⟩ := hstep
    exact hB.tgt

/-- The unjustified reads of a lazy state are actions of its execution. -/
theorem IsLazy.unj_subset {l : LState Key Val} (h : IsLazy Ex init l) : l.E.unj ⊆ l.E.A :=
  KExec.unj_subset_lazyK.trans h.stage.act

/-! ## The obligations outside the unjustified reads do not matter -/

/-- The commit set depends on the obligations of the unjustified reads only. -/
theorem KExec.lazyK_congr {E : KExec Key Val} {θ θ' : Key → Key} (hθ : Set.EqOn θ θ' E.unj) :
    E.lazyK init θ = E.lazyK init θ' := by
  unfold KExec.lazyK
  rw [hθ.image_eq]

/-- Being a lazy state depends on the obligations of the unjustified reads
only. -/
theorem IsLazy.congr {l : LState Key Val} (h : IsLazy Ex init l) {θ' : Key → Key}
    (hθ : Set.EqOn l.θ θ' l.E.unj) : IsLazy Ex init ⟨l.E, θ', l.Z⟩ where
  obl_mem r hr := by
    change θ' r ∈ l.E.A
    rw [← hθ hr]
    exact h.obl_mem r hr
  stage := by
    have hK : LState.K init ⟨l.E, θ', l.Z⟩ = l.K init := (KExec.lazyK_congr hθ).symm
    change IsStage Ex init ⟨l.E, LState.K init ⟨l.E, θ', l.Z⟩, LState.K init ⟨l.E, θ', l.Z⟩, l.Z⟩
    rw [hK]
    exact h.stage

/-- Being an initial lazy state depends on the obligations of the
unjustified reads only. -/
theorem IsLInit.congr {l : LState Key Val} (h : IsLInit Ex init l) {θ' : Key → Key}
    (hθ : Set.EqOn l.θ θ' l.E.unj) : IsLInit Ex init ⟨l.E, θ', l.Z⟩ :=
  ⟨h.1.congr hθ, h.2.1, h.2.2⟩

/-- A lazy step depends on the obligations of the source only on its
unjustified reads. -/
theorem LStep.congr_src {l l' : LState Key Val} {B : Set Key} (h : LStep Ex init l l' B)
    {θ' : Key → Key} (hθ : Set.EqOn l.θ θ' l.E.unj) : LStep Ex init ⟨l.E, θ', l.Z⟩ l' B := by
  have hK : LState.K init ⟨l.E, θ', l.Z⟩ = l.K init := (KExec.lazyK_congr hθ).symm
  have hK1 : lazyK1 init l.E θ' l'.E B = lazyK1 init l.E l.θ l'.E B := by
    unfold lazyK1
    rw [← KExec.lazyK_congr hθ]
  refine
    { src := h.src.congr hθ
      tgt := h.tgt
      ne := h.ne
      batch := ?_
      unj_eq := h.unj_eq
      disj := h.disj
      rf_mem := h.rf_mem
      obl_old := fun r hr => (h.obl_old r hr).trans (hθ hr)
      obl_new := h.obl_new
      chain := ?_ }
  · dsimp only
    rw [hK]
    exact h.batch
  · dsimp only
    rw [hK, hK1]
    exact h.chain

/-- A lazy step depends on the obligations of the target only on its
unjustified reads. -/
theorem LStep.congr_tgt {l l' : LState Key Val} {B : Set Key} (h : LStep Ex init l l' B)
    {θ' : Key → Key} (hθ : Set.EqOn l'.θ θ' l'.E.unj) : LStep Ex init l ⟨l'.E, θ', l'.Z⟩ B where
  src := h.src
  tgt := h.tgt.congr hθ
  ne := h.ne
  batch := h.batch
  unj_eq := h.unj_eq
  disj := h.disj
  rf_mem := h.rf_mem
  obl_old r hr := (hθ (by rw [h.unj_eq]; exact Or.inl hr)).symm.trans (h.obl_old r hr)
  obl_new r hr := by
    change l.E.rf r = some (θ' r)
    rw [← hθ (h.batch_subset hr)]
    exact h.obl_new r hr
  chain := h.chain

/-- Reachability depends on the obligations of the unjustified reads only. -/
theorem LReach.congr {l : LState Key Val} (h : LReach Ex init l) {θ' : Key → Key}
    (hθ : Set.EqOn l.θ θ' l.E.unj) : LReach Ex init ⟨l.E, θ', l.Z⟩ := by
  obtain ⟨l₀, h₀, hst⟩ := h
  cases hst with
  | refl => exact ⟨_, h₀.congr hθ, Relation.ReflTransGen.refl⟩
  | tail hac hcb =>
    obtain ⟨B, hB⟩ := hcb
    exact ⟨l₀, h₀, hac.tail ⟨B, hB.congr_tgt hθ⟩⟩

/-! ## Candidates -/

/-- `l` is a *candidate* of `l'` with batch `B` (`def:lazy-parent`): there
is a lazy step `l ⇝ l'` with batch `B`, and `l` is reachable from an initial
lazy state. The remaining conditions of the paper's definition follow from the
lazy step: `IsCand.batch_subset`, `IsCand.unj_eq`, `IsCand.obl_eq` and
`IsCand.Z_subset`. -/
def IsCand (Ex : Set (KExec Key Val)) (init : Key) (l' l : LState Key Val) (B : Set Key) :
    Prop :=
  LStep Ex init l l' B ∧ LReach Ex init l

section Cand

variable {l l' : LState Key Val} {B : Set Key}

/-- The batch of a candidate is a nonempty set of unjustified reads of `l'`. -/
theorem IsCand.batch_subset (h : IsCand Ex init l' l B) : B.Nonempty ∧ B ⊆ l'.E.unj :=
  ⟨h.1.ne, h.1.batch_subset⟩

/-- The unjustified reads of a candidate: `unj(l.E) = unj(l'.E) \ B`. -/
theorem IsCand.unj_eq (h : IsCand Ex init l' l B) : l.E.unj = l'.E.unj \ B :=
  h.1.unj_src

/-- The obligations of a candidate are those of `l'` on `unj(l.E)`. -/
theorem IsCand.obl_eq (h : IsCand Ex init l' l B) : Set.EqOn l.θ l'.θ l.E.unj :=
  fun r hr => (h.1.obl_old r hr).symm

/-- The frozen edges of a candidate are frozen edges of `l'`. -/
theorem IsCand.Z_subset (h : IsCand Ex init l' l B) : l.Z ⊆ l'.Z :=
  h.1.Z_subset

/-- The batch of a candidate is determined by the candidate. -/
theorem IsCand.batch_eq (h : IsCand Ex init l' l B) : B = l'.E.unj \ l.E.unj :=
  h.1.batch_eq

/-- An initial lazy state has no candidate. -/
theorem IsLInit.not_isCand (h : IsLInit Ex init l') : ¬ IsCand Ex init l' l B :=
  fun hc => hc.1.not_isLInit h

/-- A candidate with the obligations replaced by those of `l'` is a
candidate. This is the candidate of the paper's definition, whose obligation
map is the restriction of that of `l'`. -/
theorem IsCand.congr (h : IsCand Ex init l' l B) : IsCand Ex init l' ⟨l.E, l'.θ, l.Z⟩ B :=
  ⟨h.1.congr_src h.obl_eq, h.2.congr h.obl_eq⟩

/-- A candidate has fewer unjustified reads: `unj(l.E) ⊂ unj(l'.E)`. -/
theorem IsCand.unj_ssubset (h : IsCand Ex init l' l B) : l.E.unj ⊂ l'.E.unj :=
  h.1.unj_ssubset

/-- A candidate has fewer unjustified reads, counted. The hypothesis `hreg`
(executions of the program are `Regular`) makes the set of unjustified reads
of `l'` finite. -/
theorem IsCand.ncard_lt (hreg : ∀ E ∈ Ex, E.Regular) (h : IsCand Ex init l' l B) :
    l.E.unj.ncard < l'.E.unj.ncard :=
  Set.ncard_lt_ncard h.unj_ssubset
    ((hreg _ h.1.tgt.stage.ex).finite.subset h.1.tgt.unj_subset)

/-- A lazy state that is not initial is reachable iff it has a candidate. -/
theorem lreach_iff_exists_isCand (hl : ¬ IsLInit Ex init l') :
    LReach Ex init l' ↔ ∃ l B, IsCand Ex init l' l B := by
  constructor
  · rintro ⟨l₀, h₀, hst⟩
    cases hst with
    | refl => exact absurd h₀ hl
    | tail hac hcb =>
      obtain ⟨B, hB⟩ := hcb
      exact ⟨_, B, hB, l₀, h₀, hac⟩
  · rintro ⟨l, B, hB, l₀, h₀, hst⟩
    exact ⟨l₀, h₀, hst.tail ⟨B, hB⟩⟩

end Cand

/-! ## Parents -/

/-- `parent` is a *parent function* (`def:lazy-parent`, with the choice among
the candidates left abstract): its value at `l'` is a candidate of `l'`, and
it is defined whenever `l'` has a candidate. In particular it is undefined at
the initial lazy states (`IsParent.eq_none_of_isLInit`). `lparent` is a parent
function that chooses the least triple `(B, E, Z)`, as in the paper. -/
structure IsParent (Ex : Set (KExec Key Val)) (init : Key)
    (parent : LState Key Val → Option (LState Key Val)) : Prop where
  cand : ∀ {l' l : LState Key Val}, parent l' = some l → ∃ B, IsCand Ex init l' l B
  defined : ∀ {l' l : LState Key Val} {B : Set Key}, IsCand Ex init l' l B →
    (parent l').isSome

section Parent

variable {parent : LState Key Val → Option (LState Key Val)}

/-- The parent is defined iff there is a candidate. -/
theorem IsParent.isSome_iff (hp : IsParent Ex init parent) (l' : LState Key Val) :
    (parent l').isSome ↔ ∃ l B, IsCand Ex init l' l B := by
  constructor
  · intro h
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨B, hB⟩ := hp.cand hl
    exact ⟨l, B, hB⟩
  · rintro ⟨l, B, hB⟩
    exact hp.defined hB

/-- The parent of an initial lazy state is undefined. -/
theorem IsParent.eq_none_of_isLInit (hp : IsParent Ex init parent) {l' : LState Key Val}
    (h : IsLInit Ex init l') : parent l' = none := by
  cases hpl : parent l' with
  | none => rfl
  | some l =>
    obtain ⟨B, hB⟩ := hp.cand hpl
    exact absurd hB h.not_isCand

/-- **Exploration of lazy states**, first claim (`prop:lazy-explore`). A lazy
state that is not initial is reachable iff its parent is defined. -/
theorem IsParent.lreach_iff (hp : IsParent Ex init parent) {l' : LState Key Val}
    (hl : ¬ IsLInit Ex init l') : LReach Ex init l' ↔ (parent l').isSome :=
  (lreach_iff_exists_isCand hl).trans (hp.isSome_iff l').symm

/-- The same claim without excluding the initial states: a state is reachable
iff it is initial or its parent is defined. -/
theorem IsParent.lreach_iff' (hp : IsParent Ex init parent) (l' : LState Key Val) :
    LReach Ex init l' ↔ IsLInit Ex init l' ∨ (parent l').isSome := by
  by_cases hl : IsLInit Ex init l'
  · exact ⟨fun _ => Or.inl hl, fun _ => ⟨l', hl, Relation.ReflTransGen.refl⟩⟩
  · rw [hp.lreach_iff hl]
    exact ⟨Or.inr, fun h => h.resolve_left hl⟩

/-- The parent has fewer unjustified reads (`hreg` as in `IsCand.ncard_lt`). -/
theorem IsParent.ncard_lt (hp : IsParent Ex init parent) (hreg : ∀ E ∈ Ex, E.Regular)
    {l l' : LState Key Val} (h : parent l' = some l) : l.E.unj.ncard < l'.E.unj.ncard := by
  obtain ⟨B, hB⟩ := hp.cand h
  exact hB.ncard_lt hreg

/-- The relation "`l` is the parent of `l'`" is well-founded: iterating the
parent terminates. -/
theorem IsParent.wf (hp : IsParent Ex init parent) (hreg : ∀ E ∈ Ex, E.Regular) :
    WellFounded (fun l l' : LState Key Val => parent l' = some l) :=
  Subrelation.wf (fun h => hp.ncard_lt hreg h) (measure fun l : LState Key Val =>
    l.E.unj.ncard).wf

/-- Iterating the parent from a reachable lazy state reaches, after at most
`|unj(l.E)|` steps, an initial lazy state, whose parent is undefined. -/
theorem IsParent.iterate_init (hp : IsParent Ex init parent) (hreg : ∀ E ∈ Ex, E.Regular) :
    ∀ {l : LState Key Val}, LReach Ex init l → ∃ n ≤ l.E.unj.ncard, ∃ l₀,
      (fun o => Option.bind o parent)^[n] (some l) = some l₀ ∧ IsLInit Ex init l₀ ∧
        parent l₀ = none := by
  suffices H : ∀ N, ∀ l : LState Key Val, l.E.unj.ncard = N → LReach Ex init l →
      ∃ n ≤ l.E.unj.ncard, ∃ l₀, (fun o => Option.bind o parent)^[n] (some l) = some l₀ ∧
        IsLInit Ex init l₀ ∧ parent l₀ = none from fun {l} hl => H _ l rfl hl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro l hN hl
  by_cases hi : IsLInit Ex init l
  · exact ⟨0, Nat.zero_le _, l, rfl, hi, hp.eq_none_of_isLInit hi⟩
  · obtain ⟨p, hpl⟩ := Option.isSome_iff_exists.1 ((hp.lreach_iff hi).1 hl)
    obtain ⟨B, hB⟩ := hp.cand hpl
    have hlt := hB.ncard_lt hreg
    obtain ⟨n, hn, l₀, hit, h₀, hn₀⟩ := ih _ (hN ▸ hlt) p rfl hB.2
    refine ⟨n + 1, by omega, l₀, ?_, h₀, hn₀⟩
    rw [Function.iterate_succ_apply]
    simpa [hpl] using hit

end Parent

/-! ## The parent of the paper: the least candidate -/

/-- The triples `(B, E, Z)` such that `⟨E, θ', Z⟩` is a candidate of `l'` with
batch `B`, where `θ'` is the obligation map of `l'`. -/
def candTriples (Ex : Set (KExec Key Val)) (init : Key) (l' : LState Key Val) :
    Set (Set Key × KExec Key Val × Set (Key × Key)) :=
  {t | IsCand Ex init l' ⟨t.2.1, l'.θ, t.2.2⟩ t.1}

/-- The least element of a nonempty set of triples for a well-order `r`. -/
noncomputable def candMin
    (r : Set Key × KExec Key Val × Set (Key × Key) →
      Set Key × KExec Key Val × Set (Key × Key) → Prop)
    [IsWellOrder _ r] {S : Set (Set Key × KExec Key Val × Set (Key × Key))}
    (h : S.Nonempty) : Set Key × KExec Key Val × Set (Key × Key) :=
  (IsWellOrder.wf (r := r)).min S h

open Classical in
/-- The parent of the paper (`def:lazy-parent`): for a well-order `r` on the
triples `(B, E, Z)`, the candidate of `l'` with the least triple, with the
obligations of `l'`; undefined if `l'` has no candidate. The paper fixes a
total order; a well-order makes the least triple exist when there are
infinitely many candidates (one exists on every type, `WellOrderingRel`). -/
noncomputable def lparent (Ex : Set (KExec Key Val)) (init : Key)
    (r : Set Key × KExec Key Val × Set (Key × Key) →
      Set Key × KExec Key Val × Set (Key × Key) → Prop)
    [IsWellOrder _ r] (l' : LState Key Val) : Option (LState Key Val) :=
  if h : (candTriples Ex init l').Nonempty then
    some ⟨(candMin r h).2.1, l'.θ, (candMin r h).2.2⟩
  else none

section LParent

variable {r : Set Key × KExec Key Val × Set (Key × Key) →
    Set Key × KExec Key Val × Set (Key × Key) → Prop} [IsWellOrder _ r]

/-- The least element belongs to the set. -/
theorem candMin_mem {S : Set (Set Key × KExec Key Val × Set (Key × Key))}
    (h : S.Nonempty) : candMin r h ∈ S :=
  (IsWellOrder.wf (r := r)).min_mem S h

/-- No element of the set is below the least element. -/
theorem candMin_least {S : Set (Set Key × KExec Key Val × Set (Key × Key))}
    (h : S.Nonempty) {t : Set Key × KExec Key Val × Set (Key × Key)} (ht : t ∈ S) :
    ¬ r t (candMin r h) :=
  (IsWellOrder.wf (r := r)).not_lt_min S ht

/-- `lparent` is a parent function. -/
theorem lparent_isParent : IsParent Ex init (lparent Ex init r) where
  cand := by
    intro l' l h
    unfold lparent at h
    split_ifs at h with hne
    obtain rfl := Option.some.inj h
    exact ⟨_, candMin_mem hne⟩
  defined := by
    intro l' l B hc
    have hne : (candTriples Ex init l').Nonempty := ⟨(B, l.E, l.Z), hc.congr⟩
    unfold lparent
    split_ifs
    rfl

/-- `lparent` is the candidate with the least triple: its obligations are
those of `l'`, it is a candidate with batch `unj(l'.E) \ unj(p.E)`, and no
candidate of `l'` has a triple below its triple. -/
theorem lparent_least {l' p l : LState Key Val} {B : Set Key}
    (hp : lparent Ex init r l' = some p) (hc : IsCand Ex init l' l B) :
    p.θ = l'.θ ∧ IsCand Ex init l' p (l'.E.unj \ p.E.unj) ∧
      ¬ r (B, l.E, l.Z) (l'.E.unj \ p.E.unj, p.E, p.Z) := by
  unfold lparent at hp
  split_ifs at hp with hne
  obtain rfl := Option.some.inj hp
  have hmem : candMin r hne ∈ candTriples Ex init l' := candMin_mem hne
  have hB : (candMin r hne).1 = l'.E.unj \ (candMin r hne).2.1.unj := hmem.batch_eq
  refine ⟨rfl, ?_, ?_⟩
  · rw [← hB]
    exact hmem
  · rw [← hB]
    exact candMin_least hne hc.congr

end LParent

/-! ## Visiting the lazy states -/

/-- The lazy states visited by the exploration procedure of
`prop:lazy-explore`: it starts from every initial lazy state and continues from
a visited `p` with every `l` such that `p ⇝ l` and `parent l = p`. -/
inductive Visit (Ex : Set (KExec Key Val)) (init : Key)
    (parent : LState Key Val → Option (LState Key Val)) : LState Key Val → Prop
  | init {l : LState Key Val} : IsLInit Ex init l → Visit Ex init parent l
  | step {p l : LState Key Val} {B : Set Key} : Visit Ex init parent p → LStep Ex init p l B →
      parent l = some p → Visit Ex init parent l

/-- `VisitPath parent l ps`: the exploration visits `l` along the path `ps`,
listed from `l` back to an initial lazy state; each state of `ps` is the
parent of the one before it, with a lazy step between them. -/
inductive VisitPath (Ex : Set (KExec Key Val)) (init : Key)
    (parent : LState Key Val → Option (LState Key Val)) :
    LState Key Val → List (LState Key Val) → Prop
  | init {l : LState Key Val} : IsLInit Ex init l → VisitPath Ex init parent l [l]
  | step {p l : LState Key Val} {B : Set Key} {ps : List (LState Key Val)} :
      VisitPath Ex init parent p ps → LStep Ex init p l B → parent l = some p →
      VisitPath Ex init parent l (l :: ps)

section Visit

variable {parent : LState Key Val → Option (LState Key Val)}

/-- A visited state is visited along a path. -/
theorem visit_iff_exists_visitPath {l : LState Key Val} :
    Visit Ex init parent l ↔ ∃ ps, VisitPath Ex init parent l ps := by
  constructor
  · intro h
    induction h with
    | init h => exact ⟨_, VisitPath.init h⟩
    | step _ hs hpl ih =>
      obtain ⟨ps, hps⟩ := ih
      exact ⟨_, VisitPath.step hps hs hpl⟩
  · rintro ⟨ps, h⟩
    induction h with
    | init h => exact Visit.init h
    | step _ hs hpl ih => exact Visit.step ih hs hpl

/-- A visited state is reachable (for every function `parent`). -/
theorem Visit.lreach {l : LState Key Val} (h : Visit Ex init parent l) : LReach Ex init l := by
  induction h with
  | init h => exact ⟨_, h, Relation.ReflTransGen.refl⟩
  | step _ hs _ ih =>
    obtain ⟨l₀, h₀, hst⟩ := ih
    exact ⟨l₀, h₀, hst.tail ⟨_, hs⟩⟩

/-- **Exploration of lazy states**, second claim: the visited states are the
reachable states (`hreg` as in `IsCand.ncard_lt`). -/
theorem IsParent.visit_iff (hp : IsParent Ex init parent) (hreg : ∀ E ∈ Ex, E.Regular)
    (l : LState Key Val) : Visit Ex init parent l ↔ LReach Ex init l := by
  refine ⟨Visit.lreach, ?_⟩
  suffices H : ∀ N, ∀ l : LState Key Val, l.E.unj.ncard = N → LReach Ex init l →
      Visit Ex init parent l from H _ l rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro l hN hl
  by_cases hi : IsLInit Ex init l
  · exact Visit.init hi
  · obtain ⟨p, hpl⟩ := Option.isSome_iff_exists.1 ((hp.lreach_iff hi).1 hl)
    obtain ⟨B, hB⟩ := hp.cand hpl
    exact Visit.step (ih _ (hN ▸ hB.ncard_lt hreg) p rfl hB.2) hB.1 hpl

/-- In a visit of `l` through a lazy step, the predecessor is `parent l` and
the batch is `unj(l.E) \ unj(p.E)`; an initial state is not visited through
a lazy step. -/
theorem visit_step_unique {p l : LState Key Val} {B : Set Key} (hs : LStep Ex init p l B)
    (hpl : parent l = some p) :
    ¬ IsLInit Ex init l ∧ parent l = some p ∧ B = l.E.unj \ p.E.unj :=
  ⟨hs.not_isLInit, hpl, hs.batch_eq⟩

/-- **Exploration of lazy states**, uniqueness: a state is visited along at
most one path. -/
theorem VisitPath.unique {l : LState Key Val} {ps qs : List (LState Key Val)}
    (h : VisitPath Ex init parent l ps) (h' : VisitPath Ex init parent l qs) : ps = qs := by
  induction h generalizing qs with
  | init hi =>
    cases h' with
    | init _ => rfl
    | step _ hs _ => exact absurd hi hs.not_isLInit
  | step _ hs hpl ih =>
    cases h' with
    | init hi => exact absurd hi hs.not_isLInit
    | step hq _ hql =>
      rw [hpl] at hql
      obtain rfl := Option.some.inj hql
      rw [ih hq]

/-- **Exploration of lazy states**, "visits every reachable lazy state exactly
once": a lazy state is reachable iff the exploration visits it along exactly
one path (`hreg` as in `IsCand.ncard_lt`). -/
theorem IsParent.lreach_iff_existsUnique (hp : IsParent Ex init parent)
    (hreg : ∀ E ∈ Ex, E.Regular) (l : LState Key Val) :
    LReach Ex init l ↔ ∃! ps, VisitPath Ex init parent l ps := by
  rw [← hp.visit_iff hreg, visit_iff_exists_visitPath]
  constructor
  · rintro ⟨ps, h⟩
    exact ⟨ps, h, fun qs h' => h'.unique h⟩
  · rintro ⟨ps, h, -⟩
    exact ⟨ps, h⟩

/-- **Exploration of lazy states**, last claim: the executions of the visited
states are the valid executions. The hypotheses are those of `Jmt.lazy`. -/
theorem IsParent.valid_iff_visit (hp : IsParent Ex init parent)
    (hinit : ∀ E ∈ Ex, E.rf init = none) (hreg : ∀ E ∈ Ex, E.Regular)
    (hkind : ∀ E ∈ Ex, ∀ E' ∈ Ex, ∀ r ∈ E'.A, (E.rf r).isSome → (E'.rf r).isSome)
    (T : KExec Key Val) :
    Valid Ex init T ↔ ∃ (θ : Key → Key) (Z : Set (Key × Key)),
      Visit Ex init parent ⟨T, θ, Z⟩ := by
  rw [lazy hinit hreg hkind T]
  simp only [hp.visit_iff hreg]

end Visit

end Jmt
