import Mazurkiewicz.Jmt.Stage

/-!
# Justifications and stage states without the synchronization order

The definitions and the forward-form theorem of `Jmt/Stage`, with the
condition (J3) removed from justifications and the condition (F3) removed from
steps. Primed names are the counterparts of the names of `Jmt/Stage`; the
proofs are the same with the two conditions left out.

Main statement: `Jmt.forward'`.
-/

namespace Jmt

variable {Key Val : Type*}

/-- `E 1, C 1, …, E n, C n` is a justification of `T`, with `C 0 = {init}`.
Stage `i + 1` (for `i < n`) has execution `E (i + 1)`, commit set `C (i + 1)`
and previous commit set `C i`. The fields `j1`–`j8` are the conditions
(J1), (J2), (J4)–(J8); the numbering is that of JLS §17.4.8. -/
structure Justifies' (Ex : Set (KExec Key Val)) (init : Key) (T : KExec Key Val)
    (n : ℕ) (E : ℕ → KExec Key Val) (C : ℕ → Set Key) : Prop where
  pos : 0 < n
  ex : ∀ i < n, E (i + 1) ∈ Ex
  c0 : C 0 = {init}
  mono : ∀ i < n, C i ⊆ C (i + 1)
  cn : C n = T.A
  en : E n = T
  j1 : ∀ i < n, C (i + 1) ⊆ (E (i + 1)).A
  j2 : ∀ i < n, ∀ a ∈ C (i + 1), ∀ b ∈ C (i + 1), (E (i + 1)).hb a b ↔ T.hb a b
  j4 : ∀ i < n, ∀ a ∈ C (i + 1), (E (i + 1)).val a = T.val a
  j5 : ∀ i < n, ∀ a ∈ C i, (E (i + 1)).rf a = T.rf a
  j6 : ∀ i < n, ∀ r w, (E (i + 1)).rf r = some w → r ∉ C i → (E (i + 1)).hb w r
  j7 : ∀ i < n, ∀ r ∈ C (i + 1), r ∉ C i → ∀ w, (E (i + 1)).rf r = some w →
    w ∈ C i ∧ ∃ w', T.rf r = some w' ∧ w' ∈ C i
  j8 : ∀ i < n, ∀ j, i ≤ j → j < n →
    ∀ p ∈ (E (i + 1)).frz (C (i + 1)), (E (j + 1)).sw p.1 p.2

/-- The justified execution is an execution of the program. -/
theorem Justifies'.mem {Ex : Set (KExec Key Val)} {init : Key} {T : KExec Key Val} {n : ℕ}
    {E : ℕ → KExec Key Val} {C : ℕ → Set Key} (h : Justifies' Ex init T n E C) : T ∈ Ex := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := h.pos; omega⟩
  exact h.en ▸ h.ex m (by omega)

/-- `T` is valid: it has a justification. -/
def Valid' (Ex : Set (KExec Key Val)) (init : Key) (T : KExec Key Val) : Prop :=
  ∃ n E C, Justifies' Ex init T n E C

/-- A step between stage states, with the conditions (F2), (F4)–(F8). -/
structure Step' (Ex : Set (KExec Key Val)) (init : Key) (s t : State Key Val) : Prop where
  src : IsStage Ex init s
  tgt : IsStage Ex init t
  before_eq : t.before = s.commit
  f2 : ∀ a ∈ s.commit, ∀ b ∈ s.commit, t.E.hb a b ↔ s.E.hb a b
  f4 : ∀ a ∈ s.commit, t.E.val a = s.E.val a
  f5 : ∀ a ∈ s.before, t.E.rf a = s.E.rf a
  f7 : ∀ r ∈ s.commit, r ∉ s.before → ∀ w, s.E.rf r = some w →
    ∃ w', t.E.rf r = some w' ∧ w' ∈ s.before
  f8 : t.Z = s.Z ∪ t.E.frz t.commit

/-- `σ 0, …, σ n` is a path of stage states from an initial state. -/
def IsPath' (Ex : Set (KExec Key Val)) (init : Key) (n : ℕ) (σ : ℕ → State Key Val) : Prop :=
  IsInit Ex init (σ 0) ∧ ∀ i < n, Step' Ex init (σ i) (σ (i + 1))

/-- The reachable stage states. -/
def Reach' (Ex : Set (KExec Key Val)) (init : Key) (t : State Key Val) : Prop :=
  ∃ n σ, IsPath' Ex init n σ ∧ σ n = t

variable {Ex : Set (KExec Key Val)} {init : Key}

theorem Justifies'.init_mem {T : KExec Key Val} {n : ℕ} {E : ℕ → KExec Key Val}
    {C : ℕ → Set Key} (h : Justifies' Ex init T n E C) : ∀ i ≤ n, init ∈ C i
  | 0, _ => by rw [h.c0]; rfl
  | i + 1, hi => h.mono i (by omega) (h.init_mem i (by omega))

theorem Justifies'.isStage {T : KExec Key Val} {n : ℕ} {E : ℕ → KExec Key Val}
    {C : ℕ → Set Key} (h : Justifies' Ex init T n E C) {i : ℕ} (hi : i < n) :
    IsStage Ex init (pathOf E C (i + 1)) where
  ex := h.ex i hi
  init_mem := h.init_mem i (by omega)
  sub := h.mono i hi
  act := h.j1 i hi
  i1 := h.j6 i hi
  i2 := fun r hr hr' w hw => (h.j7 i hi r hr hr' w hw).1
  i3 := by
    intro p hp
    obtain ⟨k, hk, hp⟩ := mem_zs hp
    exact h.j8 k (by omega) i (by omega) hi p hp

theorem Justifies'.isPath {T : KExec Key Val} {n : ℕ} {E : ℕ → KExec Key Val}
    {C : ℕ → Set Key} (h : Justifies' Ex init T n E C) : IsPath' Ex init n (pathOf E C) := by
  have h0 : IsStage Ex init (pathOf E C 0) :=
    { ex := h.ex 0 h.pos
      init_mem := h.init_mem 0 (by omega)
      sub := subset_rfl
      act := (h.mono 0 h.pos).trans (h.j1 0 h.pos)
      i1 := h.j6 0 h.pos
      i2 := fun r hr hr' => absurd hr hr'
      i3 := fun p hp => absurd hp (Set.notMem_empty p) }
  refine ⟨⟨h0, h.c0, h.c0, rfl⟩, ?_⟩
  intro i hi
  cases i with
  | zero =>
    exact
      { src := h0
        tgt := h.isStage hi
        before_eq := rfl
        f2 := fun _ _ _ _ => Iff.rfl
        f4 := fun _ _ => rfl
        f5 := fun _ _ => rfl
        f7 := fun r hr hr' => absurd hr hr'
        f8 := rfl }
  | succ i =>
    have hi' : i < n := by omega
    exact
      { src := h.isStage hi'
        tgt := h.isStage hi
        before_eq := rfl
        f2 := fun a ha b hb =>
          (h.j2 (i + 1) hi a (h.mono _ hi ha) b (h.mono _ hi hb)).trans (h.j2 i hi' a ha b hb).symm
        f4 := fun a ha =>
          (h.j4 (i + 1) hi a (h.mono _ hi ha)).trans (h.j4 i hi' a ha).symm
        f5 := fun a ha =>
          (h.j5 (i + 1) hi a (h.mono _ hi' ha)).trans (h.j5 i hi' a ha).symm
        f7 := by
          intro r hr hr' w hw
          obtain ⟨-, w', hw', hmem⟩ := h.j7 i hi' r hr hr' w hw
          exact ⟨w', (h.j5 (i + 1) hi r hr).trans hw', hmem⟩
        f8 := rfl }

section Path

variable {n : ℕ} {σ : ℕ → State Key Val}

theorem IsPath'.isStage (h : IsPath' Ex init n σ) : ∀ i ≤ n, IsStage Ex init (σ i)
  | 0, _ => h.1.1
  | i + 1, hi => (h.2 i (by omega)).tgt

theorem IsPath'.before_eq (h : IsPath' Ex init n σ) {i : ℕ} (hi : i < n) :
    (σ (i + 1)).before = (σ i).commit :=
  (h.2 i hi).before_eq

theorem IsPath'.commit_step (h : IsPath' Ex init n σ) {i : ℕ} (hi : i < n) :
    (σ i).commit ⊆ (σ (i + 1)).commit := by
  have := (h.2 i hi).tgt.sub
  rwa [h.before_eq hi] at this

theorem IsPath'.commit_mono (h : IsPath' Ex init n σ) {i : ℕ} :
    ∀ k, i + k ≤ n → (σ i).commit ⊆ (σ (i + k)).commit
  | 0, _ => subset_rfl
  | k + 1, hk => (h.commit_mono k (by omega)).trans (h.commit_step (i := i + k) (by omega))

theorem IsPath'.hb_chain (h : IsPath' Ex init n σ) {i : ℕ} {a b : Key}
    (ha : a ∈ (σ i).commit) (hb : b ∈ (σ i).commit) :
    ∀ k, i + k ≤ n → ((σ (i + k)).E.hb a b ↔ (σ i).E.hb a b)
  | 0, _ => Iff.rfl
  | k + 1, hk =>
    ((h.2 (i + k) (by omega)).f2 a (h.commit_mono k (by omega) ha) b
      (h.commit_mono k (by omega) hb)).trans (h.hb_chain ha hb k (by omega))

theorem IsPath'.val_chain (h : IsPath' Ex init n σ) {i : ℕ} {a : Key}
    (ha : a ∈ (σ i).commit) :
    ∀ k, i + k ≤ n → (σ (i + k)).E.val a = (σ i).E.val a
  | 0, _ => rfl
  | k + 1, hk =>
    ((h.2 (i + k) (by omega)).f4 a (h.commit_mono k (by omega) ha)).trans
      (h.val_chain ha k (by omega))

/-- A read committed before stage `i + 1` keeps the source it has there. -/
theorem IsPath'.rf_chain (h : IsPath' Ex init n σ) {i : ℕ} {a : Key}
    (ha : a ∈ (σ i).commit) :
    ∀ k, i + 1 + k ≤ n → (σ (i + 1 + k)).E.rf a = (σ (i + 1)).E.rf a
  | 0, _ => rfl
  | k + 1, hk => by
    have hstep := h.2 (i + 1 + k) (by omega)
    have hmem : a ∈ (σ (i + 1 + k)).before := by
      have e : i + 1 + k = (i + k) + 1 := by omega
      rw [e, h.before_eq (by omega)]
      exact h.commit_mono k (by omega) ha
    exact (hstep.f5 a hmem).trans (h.rf_chain ha k (by omega))

theorem IsPath'.z_mono (h : IsPath' Ex init n σ) {i : ℕ} :
    ∀ k, i + k ≤ n → (σ i).Z ⊆ (σ (i + k)).Z
  | 0, _ => subset_rfl
  | k + 1, hk => by
    have e : (σ (i + (k + 1))).Z = (σ (i + k)).Z ∪ _ := (h.2 (i + k) (by omega)).f8
    rw [e]
    exact (h.z_mono k (by omega)).trans Set.subset_union_left

theorem IsPath'.before_mem (h : IsPath' Ex init n σ) {i : ℕ} (hi : i < n) {a : Key} :
    a ∈ (σ (i + 1)).before ↔ a ∈ (σ i).commit := by
  rw [h.before_eq hi]

/-- The stages of a path to an accepting state justify its execution. -/
theorem IsPath'.justifies (h : IsPath' Ex init (n + 1) σ)
    (hacc : (σ (n + 1)).commit = (σ (n + 1)).E.A) :
    Justifies' Ex init (σ (n + 1)).E (n + 1) (fun i => (σ i).E) (fun i => (σ i).commit) where
  pos := by omega
  ex := fun i hi => (h.isStage (i + 1) (by omega)).ex
  c0 := h.1.2.2.1
  mono := fun i hi => h.commit_step hi
  cn := hacc
  en := rfl
  j1 := fun i hi => (h.isStage (i + 1) (by omega)).act
  j2 := by
    intro i hi a ha b hb
    obtain ⟨k, hk⟩ : ∃ k, n + 1 = i + 1 + k := ⟨n - i, by omega⟩
    have := h.hb_chain ha hb k (by omega)
    rw [← hk] at this
    exact this.symm
  j4 := by
    intro i hi a ha
    obtain ⟨k, hk⟩ : ∃ k, n + 1 = i + 1 + k := ⟨n - i, by omega⟩
    have := h.val_chain ha k (by omega)
    rw [← hk] at this
    exact this.symm
  j5 := by
    intro i hi a ha
    obtain ⟨k, hk⟩ : ∃ k, n + 1 = i + 1 + k := ⟨n - i, by omega⟩
    have := h.rf_chain ha k (by omega)
    rw [← hk] at this
    exact this.symm
  j6 := by
    intro i hi r w hw hr
    exact (h.isStage (i + 1) (by omega)).i1 r w hw (fun hmem => hr ((h.before_mem hi).1 hmem))
  j7 := by
    intro i hi r hr hr' w hw
    have hst := h.isStage (i + 1) (by omega)
    have hw' : w ∈ (σ i).commit :=
      (h.before_mem hi).1 (hst.i2 r hr (fun hmem => hr' ((h.before_mem hi).1 hmem)) w hw)
    refine ⟨hw', ?_⟩
    rcases Nat.lt_or_ge (i + 1) (n + 1) with hlt | hge
    · obtain ⟨w', hrf, hmem⟩ := (h.2 (i + 1) hlt).f7 r hr
        (fun hmem => hr' ((h.before_mem hi).1 hmem)) w hw
      obtain ⟨k, hk⟩ : ∃ k, n + 1 = i + 1 + 1 + k := ⟨n - (i + 1), by omega⟩
      have hch := h.rf_chain (i := i + 1) hr k (by omega)
      rw [← hk] at hch
      exact ⟨w', hch.trans hrf, (h.before_mem hi).1 hmem⟩
    · have e : i = n := by omega
      subst e
      exact ⟨w, hw, hw'⟩
  j8 := by
    intro i hi j hij hj p hp
    have hz : p ∈ (σ (i + 1)).Z := by
      rw [(h.2 i hi).f8]
      exact Or.inr hp
    obtain ⟨k, hk⟩ : ∃ k, j + 1 = i + 1 + k := ⟨j - i, by omega⟩
    have hz' := h.z_mono (i := i + 1) k (by omega) hz
    rw [← hk] at hz'
    exact (h.isStage (j + 1) (by omega)).i3 p hz'

end Path

/-- **Forward form without the synchronization order.** An execution is valid iff an accepting
stage state with this execution is reachable. -/
theorem forward' (T : KExec Key Val) :
    Valid' Ex init T ↔ ∃ B Z, Reach' Ex init ⟨T, B, T.A, Z⟩ := by
  constructor
  · rintro ⟨n, E, C, h⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := h.pos; omega⟩
    refine ⟨C m, zs E C (m + 1), m + 1, pathOf E C, h.isPath, ?_⟩
    simp only [pathOf, h.en, h.cn]
  · rintro ⟨B, Z, n, σ, hpath, hlast⟩
    cases n with
    | zero =>
      obtain ⟨hst, hb, hc, hz⟩ := hpath.1
      rw [hlast] at hst hb hc hz
      simp only at hb hc hz
      refine ⟨1, fun _ => T, fun _ => {init}, ?_⟩
      exact
        { pos := by omega
          ex := fun _ _ => hst.ex
          c0 := rfl
          mono := fun _ _ => subset_rfl
          cn := hc.symm
          en := rfl
          j1 := fun _ _ => hc ▸ hst.act
          j2 := fun _ _ _ _ _ _ => Iff.rfl
          j4 := fun _ _ _ _ => rfl
          j5 := fun _ _ _ _ => rfl
          j6 := fun _ _ r w hw hr => hst.i1 r w hw (hb ▸ hr)
          j7 := fun _ _ r hr hr' => absurd hr hr'
          j8 := fun _ _ _ _ _ p hp => T.frz_sw _ hp }
    | succ n =>
      have hE : (σ (n + 1)).E = T := by rw [hlast]
      have hA : (σ (n + 1)).commit = (σ (n + 1)).E.A := by rw [hlast]
      have := hpath.justifies hA
      rw [hE] at this
      exact ⟨_, _, _, this⟩

end Jmt
