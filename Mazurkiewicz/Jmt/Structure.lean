import Mazurkiewicz.Jmt.NoSo
import Mathlib.Data.Set.Card
import Mathlib.Order.WellFoundedSet

/-!
# Stage states: reachable executions are valid; one step condition is redundant

Two statements on the stage states of `Jmt/Stage`.

* `Jmt.Reach.valid`: the execution of every reachable stage state is valid.
  The remaining actions are committed one per stage, a happens-before-minimal
  one first. This needs that an execution has finitely many actions, that its
  happens-before relation is a strict partial order, and that the source of a
  read is an action (`KExec.Regular`).
* `Jmt.Reach'.valid`: the same for the transition system without the
  condition (F3) on the synchronization order, if the keys of synchronization
  actions form a set `V` such that a read in `V` reads a happens-before-earlier
  write, a read outside `V` reads a write outside `V`, and the synchronization
  order relates keys of `V` only (`SyncSet`). So (F3) does not change the set
  of valid executions (`Jmt.valid_iff_reach'`), and neither does the condition
  (J3) of justifications (`Jmt.valid'_iff_valid`).
* `Jmt.valid_iff_exists_reach`, `Jmt.Justifies.stage_valid`: the valid
  executions are the executions of reachable states; every stage execution of
  a justification is valid.
-/

namespace Jmt

variable {Key Val : Type*} {Ex : Set (KExec Key Val)} {init : Key}

/-- Properties of an execution used to commit its remaining actions one at a
time. -/
structure KExec.Regular (E : KExec Key Val) : Prop where
  finite : E.A.Finite
  hb_irrefl : ∀ a, ¬ E.hb a a
  hb_trans : ∀ a b c, E.hb a b → E.hb b c → E.hb a c
  rf_mem : ∀ r w, E.rf r = some w → w ∈ E.A

/-- A reachable state followed by a step is reachable. -/
theorem Reach.step {s t : State Key Val} (hs : Reach Ex init s) (hst : Step Ex init s t) :
    Reach Ex init t := by
  obtain ⟨n, σ, hpath, rfl⟩ := hs
  refine ⟨n + 1, fun i => if i ≤ n then σ i else t, ⟨?_, ?_⟩, ?_⟩
  · simpa using hpath.1
  · intro i hi
    by_cases h : i + 1 ≤ n
    · have h' : i ≤ n := by omega
      simp only [h, h', ite_true]
      exact hpath.2 i (by omega)
    · have e : i = n := by omega
      subst e
      simpa using hst
  · simp

/-- A set of actions of a regular execution that is not empty has a
happens-before-minimal element. -/
theorem KExec.Regular.exists_min {E : KExec Key Val} (h : E.Regular) {S : Set Key}
    (hS : S ⊆ E.A) (hne : S.Nonempty) : ∃ a ∈ S, ∀ b ∈ S, ¬ E.hb b a := by
  have : IsStrictOrder Key E.hb :=
    { irrefl := h.hb_irrefl
      trans := h.hb_trans }
  have hwf : S.WellFoundedOn E.hb := (h.finite.subset hS).wellFoundedOn
  obtain ⟨x, hx⟩ := hne
  obtain ⟨⟨a, ha⟩, -, hmin⟩ := WellFounded.has_min hwf Set.univ ⟨⟨x, hx⟩, trivial⟩
  exact ⟨a, ha, fun b hb hba => hmin ⟨b, hb⟩ trivial hba⟩

/-- The step that commits one more action `a`, happens-before-minimal among
the actions that are not committed. -/
theorem Step.commit_one {s : State Key Val} (hs : IsStage Ex init s) (hreg : s.E.Regular)
    {a : Key} (ha : a ∈ s.E.A) (hac : a ∉ s.commit)
    (hmin : ∀ b ∈ s.E.A \ s.commit, ¬ s.E.hb b a) :
    Step Ex init s ⟨s.E, s.commit, insert a s.commit, s.Z ∪ s.E.frz (insert a s.commit)⟩ where
  src := hs
  tgt :=
    { ex := hs.ex
      init_mem := hs.sub hs.init_mem
      sub := Set.subset_insert _ _
      act := Set.insert_subset ha hs.act
      i1 := fun r w hw hr => hs.i1 r w hw (fun hmem => hr (hs.sub hmem))
      i2 := by
        intro r hr hr' w hw
        have hra : r = a := by
          rcases hr with h | h
          · exact h
          · exact absurd h hr'
        subst hra
        have hhb : s.E.hb w r := hs.i1 r w hw (fun hmem => hac (hs.sub hmem))
        by_contra hwc
        exact hmin w ⟨hreg.rf_mem r w hw, hwc⟩ hhb
      i3 := by
        rintro p (hp | hp)
        · exact hs.i3 p hp
        · exact s.E.frz_sw _ hp }
  before_eq := rfl
  f2 := fun _ _ _ _ => Iff.rfl
  f3 := fun _ _ _ _ => Iff.rfl
  f4 := fun _ _ => rfl
  f5 := fun _ _ => rfl
  f7 := fun r hr hr' w hw => ⟨w, hw, hs.i2 r hr hr' w hw⟩
  f8 := rfl

theorem IsPath.isStage_last {n : ℕ} {σ : ℕ → State Key Val} (h : IsPath Ex init n σ) :
    IsStage Ex init (σ n) :=
  h.isStage n le_rfl

theorem Reach.isStage {s : State Key Val} (h : Reach Ex init s) : IsStage Ex init s := by
  obtain ⟨n, σ, hpath, rfl⟩ := h
  exact hpath.isStage_last

/-- **Reachable executions are valid.** -/
theorem Reach.valid (hreg : ∀ E ∈ Ex, E.Regular) :
    ∀ {s : State Key Val}, Reach Ex init s → Valid Ex init s.E := by
  suffices H : ∀ k, ∀ s : State Key Val, Reach Ex init s → (s.E.A \ s.commit).ncard = k →
      Valid Ex init s.E from fun {s} hs => H _ s hs rfl
  intro k
  induction k with
  | zero =>
    intro s hs hk
    have hst := hs.isStage
    have hfin : (s.E.A \ s.commit).Finite := (hreg _ hst.ex).finite.sdiff
    have hempty : s.E.A \ s.commit = ∅ := (Set.ncard_eq_zero hfin).1 hk
    have hc : s.commit = s.E.A :=
      Set.Subset.antisymm hst.act (Set.sdiff_eq_empty.1 hempty)
    refine (forward s.E).2 ⟨s.before, s.Z, ?_⟩
    have e : (⟨s.E, s.before, s.E.A, s.Z⟩ : State Key Val) = s := by
      cases s
      simp only at hc
      simp [hc]
    rw [e]
    exact hs
  | succ k ih =>
    intro s hs hk
    have hst := hs.isStage
    have hR := hreg _ hst.ex
    have hfin : (s.E.A \ s.commit).Finite := hR.finite.sdiff
    have hne : (s.E.A \ s.commit).Nonempty := by
      rw [← Set.ncard_pos hfin]
      omega
    obtain ⟨a, ha, hmin⟩ := hR.exists_min Set.sdiff_subset hne
    have hstep := Step.commit_one hst hR ha.1 ha.2 hmin
    have hreach := hs.step hstep
    have e : s.E.A \ insert a s.commit = (s.E.A \ s.commit) \ {a} := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have hcard : (s.E.A \ insert a s.commit).ncard = k := by
      rw [e, Set.ncard_sdiff_singleton_of_mem ha, hk]
      rfl
    exact ih ⟨s.E, s.commit, insert a s.commit, s.Z ∪ s.E.frz (insert a s.commit)⟩ hreach hcard

/-- The valid executions are the executions of the reachable stage states. -/
theorem valid_iff_exists_reach (hreg : ∀ E ∈ Ex, E.Regular) (T : KExec Key Val) :
    Valid Ex init T ↔ ∃ s, Reach Ex init s ∧ s.E = T := by
  constructor
  · intro h
    obtain ⟨B, Z, hr⟩ := (forward T).1 h
    exact ⟨_, hr, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact hs.valid hreg

/-- Every stage execution of a justification is valid. -/
theorem Justifies.stage_valid (hreg : ∀ E ∈ Ex, E.Regular) {T : KExec Key Val} {n : ℕ}
    {E : ℕ → KExec Key Val} {C : ℕ → Set Key} (h : Justifies Ex init T n E C) {i : ℕ}
    (hi : i < n) : Valid Ex init (E (i + 1)) := by
  have hpath := h.isPath
  have hreach : Reach Ex init (pathOf E C (i + 1)) :=
    ⟨i + 1, pathOf E C, ⟨hpath.1, fun j hj => hpath.2 j (by omega)⟩, rfl⟩
  exact hreach.valid hreg

/-! ## The conditions (F3) and (J3) -/

theorem Justifies.justifies' {T : KExec Key Val} {n : ℕ} {E : ℕ → KExec Key Val}
    {C : ℕ → Set Key} (h : Justifies Ex init T n E C) : Justifies' Ex init T n E C :=
  ⟨h.pos, h.ex, h.c0, h.mono, h.cn, h.en, h.j1, h.j2, h.j4, h.j5, h.j6, h.j7, h.j8⟩

theorem Step.step' {s t : State Key Val} (h : Step Ex init s t) : Step' Ex init s t :=
  ⟨h.src, h.tgt, h.before_eq, h.f2, h.f4, h.f5, h.f7, h.f8⟩

theorem Reach.reach' {s : State Key Val} (h : Reach Ex init s) : Reach' Ex init s := by
  obtain ⟨n, σ, hpath, rfl⟩ := h
  exact ⟨n, σ, ⟨hpath.1, fun i hi => (hpath.2 i hi).step'⟩, rfl⟩

/-- The properties of a set `V` of keys that make (F3) redundant. They hold
for the set of keys of synchronization actions if these are the accesses to
volatile locations. -/
structure SyncSet (Ex : Set (KExec Key Val)) (init : Key) (V : Set Key) : Prop where
  init_not_mem : init ∉ V
  /-- a read in `V` reads a happens-before-earlier write -/
  hb_of_mem : ∀ E ∈ Ex, ∀ r ∈ V, ∀ w, E.rf r = some w → E.hb w r
  /-- a read outside `V` reads a write outside `V` -/
  source_not_mem : ∀ E ∈ Ex, ∀ r, r ∉ V → ∀ w, E.rf r = some w → w ∉ V
  /-- the synchronization order relates keys of `V` only -/
  so_mem : ∀ E ∈ Ex, ∀ a b, E.so a b → a ∈ V ∧ b ∈ V

section F3

variable {V : Set Key} {n : ℕ} {σ : ℕ → State Key Val}

/-- The frozen edges of the path with the keys of `V` removed from all commit
sets. -/
def zsV (V : Set Key) (σ : ℕ → State Key Val) : ℕ → Set (Key × Key)
  | 0 => ∅
  | i + 1 => zsV V σ i ∪ (σ (i + 1)).E.frz ((σ (i + 1)).commit \ V)

/-- The path with the keys of `V` removed from all commit sets. -/
def strip (V : Set Key) (σ : ℕ → State Key Val) (i : ℕ) : State Key Val :=
  ⟨(σ i).E, (σ i).before \ V, (σ i).commit \ V, zsV V σ i⟩

theorem IsPath'.zsV_sub (h : IsPath' Ex init n σ) : ∀ i ≤ n, zsV V σ i ⊆ (σ i).Z
  | 0, _ => Set.empty_subset _
  | i + 1, hi => by
    rw [(h.2 i (by omega)).f8]
    exact Set.union_subset_union (h.zsV_sub i (by omega))
      ((σ (i + 1)).E.frz_mono Set.sdiff_subset)

theorem IsPath'.strip_isStage (hV : SyncSet Ex init V) (h : IsPath' Ex init n σ) {i : ℕ}
    (hi : i ≤ n) : IsStage Ex init (strip V σ i) := by
  have hst := h.isStage i hi
  exact
    { ex := hst.ex
      init_mem := ⟨hst.init_mem, hV.init_not_mem⟩
      sub := Set.sdiff_subset_sdiff_left hst.sub
      act := Set.sdiff_subset.trans hst.act
      i1 := by
        intro r w hw hr
        by_cases hrb : r ∈ (σ i).before
        · have hrV : r ∈ V := by
            by_contra hrV
            exact hr ⟨hrb, hrV⟩
          exact hV.hb_of_mem _ hst.ex r hrV w hw
        · exact hst.i1 r w hw hrb
      i2 := by
        intro r hr hr' w hw
        have hrb : r ∉ (σ i).before := fun hmem => hr' ⟨hmem, hr.2⟩
        exact ⟨hst.i2 r hr.1 hrb w hw, hV.source_not_mem _ hst.ex r hr.2 w hw⟩
      i3 := fun p hp => hst.i3 p (h.zsV_sub i hi hp) }

theorem singleton_sdiff {a : Key} (h : a ∉ V) : ({a} : Set Key) \ V = {a} := by
  ext x
  constructor
  · exact fun hx => hx.1
  · intro hx
    exact ⟨hx, fun hv => h ((Set.mem_singleton_iff.1 hx) ▸ hv)⟩

/-- With the keys of `V` removed, a path without (F3) is a path. -/
theorem IsPath'.strip_isPath (hV : SyncSet Ex init V) (h : IsPath' Ex init n σ) :
    IsPath Ex init n (strip V σ) := by
  refine ⟨⟨h.strip_isStage hV (Nat.zero_le n), ?_, ?_, rfl⟩, ?_⟩
  · change (σ 0).before \ V = {init}
    rw [h.1.2.1, singleton_sdiff hV.init_not_mem]
  · change (σ 0).commit \ V = {init}
    rw [h.1.2.2.1, singleton_sdiff hV.init_not_mem]
  · intro i hi
    have hstep := h.2 i hi
    exact
      { src := h.strip_isStage hV (by omega)
        tgt := h.strip_isStage hV (by omega)
        before_eq := by
          change (σ (i + 1)).before \ V = (σ i).commit \ V
          rw [hstep.before_eq]
        f2 := fun a ha b hb => hstep.f2 a ha.1 b hb.1
        f3 := by
          intro a ha b _
          constructor
          · exact fun hso => absurd (hV.so_mem _ hstep.tgt.ex a b hso).1 ha.2
          · exact fun hso => absurd (hV.so_mem _ hstep.src.ex a b hso).1 ha.2
        f4 := fun a ha => hstep.f4 a ha.1
        f5 := fun a ha => hstep.f5 a ha.1
        f7 := by
          intro r hr hr' w hw
          have hrb : r ∉ (σ i).before := fun hmem => hr' ⟨hmem, hr.2⟩
          obtain ⟨w', hw', hmem⟩ := hstep.f7 r hr.1 hrb w hw
          exact ⟨w', hw', hmem, hV.source_not_mem _ hstep.tgt.ex r hr.2 w' hw'⟩
        f8 := rfl }

/-- **(F3) is redundant for validity.** The execution of a state that is
reachable without (F3) is valid. -/
theorem Reach'.valid (hreg : ∀ E ∈ Ex, E.Regular) (hV : SyncSet Ex init V)
    {s : State Key Val} (h : Reach' Ex init s) : Valid Ex init s.E := by
  obtain ⟨n, σ, hpath, rfl⟩ := h
  have hreach : Reach Ex init (strip V σ n) := ⟨n, strip V σ, hpath.strip_isPath hV, rfl⟩
  exact hreach.valid hreg

/-- An execution is valid iff an accepting state with this execution is
reachable without (F3). -/
theorem valid_iff_reach' (hreg : ∀ E ∈ Ex, E.Regular) (hV : SyncSet Ex init V)
    (T : KExec Key Val) : Valid Ex init T ↔ ∃ B Z, Reach' Ex init ⟨T, B, T.A, Z⟩ := by
  constructor
  · intro h
    obtain ⟨B, Z, hr⟩ := (forward T).1 h
    exact ⟨B, Z, hr.reach'⟩
  · rintro ⟨B, Z, hr⟩
    exact hr.valid hreg hV

/-- **(J3) is redundant.** Removing the condition on the synchronization
order from justifications does not change the valid executions. -/
theorem valid'_iff_valid (hreg : ∀ E ∈ Ex, E.Regular) (hV : SyncSet Ex init V)
    (T : KExec Key Val) : Valid' Ex init T ↔ Valid Ex init T := by
  constructor
  · intro h
    obtain ⟨B, Z, hr⟩ := (forward' T).1 h
    exact hr.valid hreg hV
  · rintro ⟨n, E, C, h⟩
    exact ⟨n, E, C, h.justifies'⟩

end F3

end Jmt
