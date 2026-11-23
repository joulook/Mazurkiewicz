import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# Justifications and stage states (Java memory model, causality)

The causality requirements of the Java memory model (JLS §17.4.8) define the
valid executions of a program by *justifications*: sequences of executions
with growing sets of committed actions. This file states justifications on an
abstract notion of execution and proves that they are equivalent to
reachability in a transition system of *stage states*, which does not mention
the execution being justified.

Executions are abstract here. An execution is given by its actions and by its
reads-from map, written values, happens-before, synchronization order and
synchronizes-with relation, all on *keys* (the identity of an action across
executions). A program is represented by its set `Ex` of executions. Nothing
is assumed about how executions arise from a program or about consistency.

Main statements:

* `Jmt.forward`: an execution has a justification iff an accepting stage
  state with this execution is reachable.
-/

namespace Jmt

variable {Key Val : Type*}

/-- An execution, with all components transported to keys.

`rf r = some w` says that `r` is a read and reads from `w`; `val w = some v`
that `w` writes `v`. `ssw` are the *sufficient synchronization edges*
(synchronizes-with edges that are immediate happens-before edges and not
program-order edges); only `ssw ⊆ sw` is used.

A set `Ex` of such records models the executions of a program if, for each of
them, (1) `rf r = none` exactly when `r` is not a read of the execution, and
`val a = none` exactly when `a` is not a write other than the initialization;
(2) whether a key is a read or a write depends on the key only; (3) reads are
actions. These facts are not part of the structure, and no statement of this
file needs them. They make the two existence statements in `Justifies.j7` and
`Step.f7` agree with the paper, where the source of a committed read is
assumed to exist. -/
structure KExec (Key Val : Type*) where
  /-- the actions -/
  A : Set Key
  /-- the source of a read -/
  rf : Key → Option Key
  /-- the value of a write -/
  val : Key → Option Val
  /-- happens-before (strict) -/
  hb : Key → Key → Prop
  /-- synchronization order -/
  so : Key → Key → Prop
  /-- synchronizes-with -/
  sw : Key → Key → Prop
  /-- sufficient synchronization edges -/
  ssw : Key → Key → Prop
  ssw_sw : ∀ x y, ssw x y → sw x y

/-- The sufficient synchronization edges `(x, y)` that the commit set `C`
*freezes*: `y` is, or happens before, a committed action. -/
def KExec.frz (E : KExec Key Val) (C : Set Key) : Set (Key × Key) :=
  {p | E.ssw p.1 p.2 ∧ ∃ z ∈ C, p.2 = z ∨ E.hb p.2 z}

theorem KExec.frz_mono (E : KExec Key Val) {C D : Set Key} (h : C ⊆ D) :
    E.frz C ⊆ E.frz D := by
  rintro p ⟨hs, z, hz, hyz⟩
  exact ⟨hs, z, h hz, hyz⟩

theorem KExec.frz_sw (E : KExec Key Val) (C : Set Key) {p : Key × Key}
    (h : p ∈ E.frz C) : E.sw p.1 p.2 :=
  E.ssw_sw _ _ h.1

/-- `E 1, C 1, …, E n, C n` is a justification of `T`, with `C 0 = {init}`.
Stage `i + 1` (for `i < n`) has execution `E (i + 1)`, commit set `C (i + 1)`
and previous commit set `C i`. The fields `j1`–`j8` are the conditions
(J1)–(J8); the numbering is that of JLS §17.4.8. -/
structure Justifies (Ex : Set (KExec Key Val)) (init : Key) (T : KExec Key Val)
    (n : ℕ) (E : ℕ → KExec Key Val) (C : ℕ → Set Key) : Prop where
  pos : 0 < n
  ex : ∀ i < n, E (i + 1) ∈ Ex
  c0 : C 0 = {init}
  mono : ∀ i < n, C i ⊆ C (i + 1)
  cn : C n = T.A
  en : E n = T
  j1 : ∀ i < n, C (i + 1) ⊆ (E (i + 1)).A
  j2 : ∀ i < n, ∀ a ∈ C (i + 1), ∀ b ∈ C (i + 1), (E (i + 1)).hb a b ↔ T.hb a b
  j3 : ∀ i < n, ∀ a ∈ C (i + 1), ∀ b ∈ C (i + 1), (E (i + 1)).so a b ↔ T.so a b
  j4 : ∀ i < n, ∀ a ∈ C (i + 1), (E (i + 1)).val a = T.val a
  j5 : ∀ i < n, ∀ a ∈ C i, (E (i + 1)).rf a = T.rf a
  j6 : ∀ i < n, ∀ r w, (E (i + 1)).rf r = some w → r ∉ C i → (E (i + 1)).hb w r
  j7 : ∀ i < n, ∀ r ∈ C (i + 1), r ∉ C i → ∀ w, (E (i + 1)).rf r = some w →
    w ∈ C i ∧ ∃ w', T.rf r = some w' ∧ w' ∈ C i
  j8 : ∀ i < n, ∀ j, i ≤ j → j < n →
    ∀ p ∈ (E (i + 1)).frz (C (i + 1)), (E (j + 1)).sw p.1 p.2

/-- The justified execution is an execution of the program. -/
theorem Justifies.mem {Ex : Set (KExec Key Val)} {init : Key} {T : KExec Key Val} {n : ℕ}
    {E : ℕ → KExec Key Val} {C : ℕ → Set Key} (h : Justifies Ex init T n E C) : T ∈ Ex := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := h.pos; omega⟩
  exact h.en ▸ h.ex m (by omega)

/-- `T` is valid: it has a justification. -/
def Valid (Ex : Set (KExec Key Val)) (init : Key) (T : KExec Key Val) : Prop :=
  ∃ n E C, Justifies Ex init T n E C

/-- A stage state `(E, C', C, Z)`: an execution, the set committed before the
current stage (`before`), the set committed now (`commit`), and the frozen
edges. -/
structure State (Key Val : Type*) where
  E : KExec Key Val
  before : Set Key
  commit : Set Key
  Z : Set (Key × Key)

/-- Well-formedness of a stage state, with the conditions (I1)–(I3). -/
structure IsStage (Ex : Set (KExec Key Val)) (init : Key) (s : State Key Val) : Prop where
  ex : s.E ∈ Ex
  init_mem : init ∈ s.before
  sub : s.before ⊆ s.commit
  act : s.commit ⊆ s.E.A
  i1 : ∀ r w, s.E.rf r = some w → r ∉ s.before → s.E.hb w r
  i2 : ∀ r ∈ s.commit, r ∉ s.before → ∀ w, s.E.rf r = some w → w ∈ s.before
  i3 : ∀ p ∈ s.Z, s.E.sw p.1 p.2

/-- An initial stage state. -/
def IsInit (Ex : Set (KExec Key Val)) (init : Key) (s : State Key Val) : Prop :=
  IsStage Ex init s ∧ s.before = {init} ∧ s.commit = {init} ∧ s.Z = ∅

/-- A step between stage states, with the conditions (F2)–(F8). -/
structure Step (Ex : Set (KExec Key Val)) (init : Key) (s t : State Key Val) : Prop where
  src : IsStage Ex init s
  tgt : IsStage Ex init t
  before_eq : t.before = s.commit
  f2 : ∀ a ∈ s.commit, ∀ b ∈ s.commit, t.E.hb a b ↔ s.E.hb a b
  f3 : ∀ a ∈ s.commit, ∀ b ∈ s.commit, t.E.so a b ↔ s.E.so a b
  f4 : ∀ a ∈ s.commit, t.E.val a = s.E.val a
  f5 : ∀ a ∈ s.before, t.E.rf a = s.E.rf a
  f7 : ∀ r ∈ s.commit, r ∉ s.before → ∀ w, s.E.rf r = some w →
    ∃ w', t.E.rf r = some w' ∧ w' ∈ s.before
  f8 : t.Z = s.Z ∪ t.E.frz t.commit

/-- `σ 0, …, σ n` is a path of stage states from an initial state. -/
def IsPath (Ex : Set (KExec Key Val)) (init : Key) (n : ℕ) (σ : ℕ → State Key Val) : Prop :=
  IsInit Ex init (σ 0) ∧ ∀ i < n, Step Ex init (σ i) (σ (i + 1))

/-- The reachable stage states. -/
def Reach (Ex : Set (KExec Key Val)) (init : Key) (t : State Key Val) : Prop :=
  ∃ n σ, IsPath Ex init n σ ∧ σ n = t

variable {Ex : Set (KExec Key Val)} {init : Key}

/-! ## From a justification to a path -/

/-- The frozen edges accumulated up to stage `i`. -/
def zs (E : ℕ → KExec Key Val) (C : ℕ → Set Key) : ℕ → Set (Key × Key)
  | 0 => ∅
  | i + 1 => zs E C i ∪ (E (i + 1)).frz (C (i + 1))

theorem mem_zs {E : ℕ → KExec Key Val} {C : ℕ → Set Key} {p : Key × Key} :
    ∀ {i : ℕ}, p ∈ zs E C i → ∃ k < i, p ∈ (E (k + 1)).frz (C (k + 1))
  | 0, h => by simp [zs] at h
  | i + 1, h => by
    rcases h with h | h
    · obtain ⟨k, hk, hp⟩ := mem_zs h
      exact ⟨k, by omega, hp⟩
    · exact ⟨i, by omega, h⟩

/-- The path of stage states of a justification. -/
def pathOf (E : ℕ → KExec Key Val) (C : ℕ → Set Key) : ℕ → State Key Val
  | 0 => ⟨E 1, C 0, C 0, ∅⟩
  | i + 1 => ⟨E (i + 1), C i, C (i + 1), zs E C (i + 1)⟩

theorem Justifies.init_mem {T : KExec Key Val} {n : ℕ} {E : ℕ → KExec Key Val}
    {C : ℕ → Set Key} (h : Justifies Ex init T n E C) : ∀ i ≤ n, init ∈ C i
  | 0, _ => by rw [h.c0]; rfl
  | i + 1, hi => h.mono i (by omega) (h.init_mem i (by omega))

theorem Justifies.isStage {T : KExec Key Val} {n : ℕ} {E : ℕ → KExec Key Val}
    {C : ℕ → Set Key} (h : Justifies Ex init T n E C) {i : ℕ} (hi : i < n) :
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

theorem Justifies.isPath {T : KExec Key Val} {n : ℕ} {E : ℕ → KExec Key Val}
    {C : ℕ → Set Key} (h : Justifies Ex init T n E C) : IsPath Ex init n (pathOf E C) := by
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
        f3 := fun _ _ _ _ => Iff.rfl
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
        f3 := fun a ha b hb =>
          (h.j3 (i + 1) hi a (h.mono _ hi ha) b (h.mono _ hi hb)).trans (h.j3 i hi' a ha b hb).symm
        f4 := fun a ha =>
          (h.j4 (i + 1) hi a (h.mono _ hi ha)).trans (h.j4 i hi' a ha).symm
        f5 := fun a ha =>
          (h.j5 (i + 1) hi a (h.mono _ hi' ha)).trans (h.j5 i hi' a ha).symm
        f7 := by
          intro r hr hr' w hw
          obtain ⟨-, w', hw', hmem⟩ := h.j7 i hi' r hr hr' w hw
          exact ⟨w', (h.j5 (i + 1) hi r hr).trans hw', hmem⟩
        f8 := rfl }

/-! ## From a path to a justification -/

section Path

variable {n : ℕ} {σ : ℕ → State Key Val}

theorem IsPath.isStage (h : IsPath Ex init n σ) : ∀ i ≤ n, IsStage Ex init (σ i)
  | 0, _ => h.1.1
  | i + 1, hi => (h.2 i (by omega)).tgt

theorem IsPath.before_eq (h : IsPath Ex init n σ) {i : ℕ} (hi : i < n) :
    (σ (i + 1)).before = (σ i).commit :=
  (h.2 i hi).before_eq

theorem IsPath.commit_step (h : IsPath Ex init n σ) {i : ℕ} (hi : i < n) :
    (σ i).commit ⊆ (σ (i + 1)).commit := by
  have := (h.2 i hi).tgt.sub
  rwa [h.before_eq hi] at this

theorem IsPath.commit_mono (h : IsPath Ex init n σ) {i : ℕ} :
    ∀ k, i + k ≤ n → (σ i).commit ⊆ (σ (i + k)).commit
  | 0, _ => subset_rfl
  | k + 1, hk => (h.commit_mono k (by omega)).trans (h.commit_step (i := i + k) (by omega))

theorem IsPath.hb_chain (h : IsPath Ex init n σ) {i : ℕ} {a b : Key}
    (ha : a ∈ (σ i).commit) (hb : b ∈ (σ i).commit) :
    ∀ k, i + k ≤ n → ((σ (i + k)).E.hb a b ↔ (σ i).E.hb a b)
  | 0, _ => Iff.rfl
  | k + 1, hk =>
    ((h.2 (i + k) (by omega)).f2 a (h.commit_mono k (by omega) ha) b
      (h.commit_mono k (by omega) hb)).trans (h.hb_chain ha hb k (by omega))

theorem IsPath.so_chain (h : IsPath Ex init n σ) {i : ℕ} {a b : Key}
    (ha : a ∈ (σ i).commit) (hb : b ∈ (σ i).commit) :
    ∀ k, i + k ≤ n → ((σ (i + k)).E.so a b ↔ (σ i).E.so a b)
  | 0, _ => Iff.rfl
  | k + 1, hk =>
    ((h.2 (i + k) (by omega)).f3 a (h.commit_mono k (by omega) ha) b
      (h.commit_mono k (by omega) hb)).trans (h.so_chain ha hb k (by omega))

theorem IsPath.val_chain (h : IsPath Ex init n σ) {i : ℕ} {a : Key}
    (ha : a ∈ (σ i).commit) :
    ∀ k, i + k ≤ n → (σ (i + k)).E.val a = (σ i).E.val a
  | 0, _ => rfl
  | k + 1, hk =>
    ((h.2 (i + k) (by omega)).f4 a (h.commit_mono k (by omega) ha)).trans
      (h.val_chain ha k (by omega))

/-- A read committed before stage `i + 1` keeps the source it has there. -/
theorem IsPath.rf_chain (h : IsPath Ex init n σ) {i : ℕ} {a : Key}
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

theorem IsPath.z_mono (h : IsPath Ex init n σ) {i : ℕ} :
    ∀ k, i + k ≤ n → (σ i).Z ⊆ (σ (i + k)).Z
  | 0, _ => subset_rfl
  | k + 1, hk => by
    have e : (σ (i + (k + 1))).Z = (σ (i + k)).Z ∪ _ := (h.2 (i + k) (by omega)).f8
    rw [e]
    exact (h.z_mono k (by omega)).trans Set.subset_union_left

theorem IsPath.before_mem (h : IsPath Ex init n σ) {i : ℕ} (hi : i < n) {a : Key} :
    a ∈ (σ (i + 1)).before ↔ a ∈ (σ i).commit := by
  rw [h.before_eq hi]

/-- The stages of a path to an accepting state justify its execution. -/
theorem IsPath.justifies (h : IsPath Ex init (n + 1) σ)
    (hacc : (σ (n + 1)).commit = (σ (n + 1)).E.A) :
    Justifies Ex init (σ (n + 1)).E (n + 1) (fun i => (σ i).E) (fun i => (σ i).commit) where
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
  j3 := by
    intro i hi a ha b hb
    obtain ⟨k, hk⟩ : ∃ k, n + 1 = i + 1 + k := ⟨n - i, by omega⟩
    have := h.so_chain ha hb k (by omega)
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

/-- **Forward form of justification.** An execution is valid iff an accepting
stage state with this execution is reachable. -/
theorem forward (T : KExec Key Val) :
    Valid Ex init T ↔ ∃ B Z, Reach Ex init ⟨T, B, T.A, Z⟩ := by
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
          j3 := fun _ _ _ _ _ _ => Iff.rfl
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
