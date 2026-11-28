import Mazurkiewicz.Pct.Basic
import Mazurkiewicz.Pct.Static

/-!
# The position labelling and the order word

`pctdpor`, `depth.tex`, sec:labellings: lem:position, def:positions (the
order word) and lem:viol-order. This file connects the operational notions
of `Basic.lean` (`Labelling`, `names`, `Directive.PViolates`) to the order
criterion `Viol` that `Static.lean` takes as a definition.

How the text is read here.

* The position labelling is taken in the form stated in the proof of
  lem:family-determined: the step of `t` after `S` has the name `(t, i)`,
  with `i` the number of steps of `t` in `S`, if `i ≥ 1` and `t :: S` is a
  schedule, and no name otherwise (`posNext`). This form refers to the
  schedule set only.
* For an arbitrary prefix-closed schedule set this function is **not** an
  event labelling: Stability fails if a step of another thread disables `t`
  (`Q = {ε, 1, 1 1, 1 2}`, `S = 1`, `t = 1`, `t' = 2`), and BackStability
  fails if it enables `t`. `Prog.Local` is the property that is used: a step
  of another thread neither enables nor disables a thread that has started.
  It holds for `Sched(P)` for every program `P` (also for a thread that has
  not started), where the enabledness of `t` depends on the trace of `t`
  only; this is proved in `Program.lean` (`Program.sched_local`,
  `Program.cons_cons_mem_sched_iff`). `posLab Q hQ` is the labelling
  of lem:position for a local `Q`.
* `cntLab Q` leaves the condition "`t :: S` is a schedule" out. It is a
  strict labelling for every prefix-closed `Q`, and it emits the same names
  as `posLab` in every schedule of `Q` (`names_posLab_eq_cntLab`), because
  emission only looks at steps that are taken. As `cntLab_strict` holds for
  every prefix-closed `Q`, uses of "the position labelling is strict" do not
  need `Local`.
* Both are instances of `Labelling.IsPos`: on the steps of `Q` the name is
  `(t, i)` as above. Everything after the two definitions is proved for an
  arbitrary labelling with `IsPos`.
* lem:position, second part (`mem_names_iff`): `(t, i)` is emitted in `S`
  iff `1 ≤ i` and `i < count t S`. The step of `t` that emits `(t, i)` is
  the step with index `i` of `t` (indices from `0`), so `t` has taken at
  least `i + 1` steps.
* def:positions: `ord S` is the list of the positions emitted by the steps
  of `S`, the latest at the head. It is defined from the thread sequence,
  not from events; the first step of a thread (its start event in `P⁺`)
  contributes nothing.
* lem:viol-order: `pviolates_iff_viol`, with the right-hand side `Viol
  (ord S) D.toPDir` of `Static.lean`; `pviolates_iff` is the same statement
  with `Viol` unfolded, and `pviolates_posLab_iff` the instance for
  `posLab`.

Not formalised here, and given by `Program.lean`: programs, the start-event
transformation `P⁺` on schedules, that `Sched(P⁺)` is local
(`Program.sched_plus_local`), that every thread's first step is its start
event (`Program.plus_act_of_notMem`), that the length of the trace of `t`
after `S` is `count t S` (`Program.length_tr`), that `P_t` is defined on
that trace iff `t :: S` is a schedule (`Program.cons_mem_sched`,
`Program.posNext_sched`), and, for bounded static programs, the set `Pos_P`
(`Pos`) and the order word as a word over it (`ordP`,
`Prog.HasLen.map_name_ordP`). `Q` is any prefix-closed schedule set (local,
for `posLab`), which is more general than `Sched(P⁺)`.

Still not formalised: execution graphs and events, the reading "`G_S` has an
event of thread `t` with index `i`" of lem:position, lem:ord-graph, and
`Pos_P` for programs that branch. The name type `Tid × ℕ` also contains the
pairs with index `0`, which are never emitted; the text's name set excludes
them.
-/

namespace Pct

/-! ### Local schedule sets -/

/-- A step of another thread neither enables nor disables a thread that has
taken a step. This is what Stability and BackStability of the position
labelling need (lem:position); it holds for `Sched(P)` and `Sched(P⁺)`
(`Program.sched_local`, `Program.sched_plus_local` in `Program.lean`). -/
def Prog.Local (Q : Prog) : Prop :=
  ∀ ⦃S : Sched⦄ ⦃t t' : Tid⦄, t' :: S ∈ Q.mem → t' ≠ t → t ∈ S →
    (t :: t' :: S ∈ Q.mem ↔ t :: S ∈ Q.mem)

/-! ### The position labelling (lem:position) -/

open Classical in
/-- The `nxt` function of the position labelling (lem:position, in the form
of the proof of lem:family-determined): `(t, i)` with `i` the number of
steps of `t` in `S`, if `i ≥ 1` and `t` is enabled after `S`. -/
noncomputable def posNext (Q : Prog) (S : Sched) (t : Tid) : Option (Tid × ℕ) :=
  if 1 ≤ S.count t ∧ t :: S ∈ Q.mem then some (t, S.count t) else none

/-- Unfolding of `posNext` (lem:position). -/
theorem posNext_eq_some {Q : Prog} {S : Sched} {t : Tid} {a : Tid × ℕ} :
    posNext Q S t = some a ↔ 1 ≤ S.count t ∧ t :: S ∈ Q.mem ∧ a = (t, S.count t) := by
  unfold posNext
  split_ifs with h
  · simp only [Option.some.injEq]
    exact ⟨fun e => ⟨h.1, h.2, e.symm⟩, fun e => e.2.2.symm⟩
  · simp only [false_iff]
    exact fun e => h ⟨e.1, e.2.1⟩

/-- The position labelling of a local schedule set (lem:position). -/
noncomputable def posLab (Q : Prog) (hQ : Q.Local) : Labelling Q (Tid × ℕ) where
  thr a := a.1
  next := posNext Q
  affinity := by
    intro S t a _ hn
    obtain ⟨-, -, rfl⟩ := posNext_eq_some.mp hn
    rfl
  stability := by
    intro S t t' a h hn hne
    obtain ⟨hc, hm, rfl⟩ := posNext_eq_some.mp hn
    have ht : t ∈ S := List.count_pos_iff.mp hc
    rw [posNext_eq_some, List.count_cons_of_ne hne]
    exact ⟨hc, (hQ h hne ht).mpr hm, rfl⟩
  uniqueness := by
    intro S₁ S₂ t a _ h₁ h₂
    obtain ⟨-, -, rfl⟩ := posNext_eq_some.mp h₁
    obtain ⟨-, -, e⟩ := posNext_eq_some.mp h₂
    have e' : S₁.count t = (S₂ ++ S₁).count t := (Prod.mk.inj e).2
    rw [List.count_append] at e'
    exact List.count_eq_zero.mp (by omega)
  notFirst := by
    intro t
    simp [posNext]

/-- `posLab` unfolded. -/
theorem posLab_next {Q : Prog} (hQ : Q.Local) (S : Sched) (t : Tid) :
    (posLab Q hQ).next S t = posNext Q S t := rfl

/-- `thr (t, i) = t` (lem:position). -/
@[simp] theorem posLab_thr {Q : Prog} (hQ : Q.Local) (a : Tid × ℕ) :
    (posLab Q hQ).thr a = a.1 := rfl

/-- lem:position: the position labelling is strict. -/
theorem posLab_strict {Q : Prog} (hQ : Q.Local) : (posLab Q hQ).Strict where
  started := by
    intro S t a _ hn
    exact List.count_pos_iff.mp (posNext_eq_some.mp hn).1
  backStability := by
    intro S t t' a h hn hne
    obtain ⟨hc, hm, rfl⟩ := posNext_eq_some.mp hn
    rw [List.count_cons_of_ne hne] at hc ⊢
    have ht : t ∈ S := List.count_pos_iff.mp hc
    exact posNext_eq_some.mpr ⟨hc, (hQ h hne ht).mp hm, rfl⟩

/-- The position labelling without the enabledness condition: `(t, i)` with
`i` the number of steps of `t` in `S`, if `i ≥ 1`. It is a labelling for
every prefix-closed schedule set and emits the same names as the labelling
of lem:position (`names_posLab_eq_cntLab`). -/
def cntLab (Q : Prog) : Labelling Q (Tid × ℕ) where
  thr a := a.1
  next S t := if 1 ≤ S.count t then some (t, S.count t) else none
  affinity := by
    intro S t a _ hn
    split_ifs at hn
    obtain rfl := Option.some.inj hn
    rfl
  stability := by
    intro S t t' a _ hn hne
    rw [List.count_cons_of_ne hne]
    exact hn
  uniqueness := by
    intro S₁ S₂ t a _ h₁ h₂
    split_ifs at h₁ h₂
    have e : (S₂ ++ S₁).count t = S₁.count t :=
      (Prod.mk.inj (Option.some.inj (h₂.trans h₁.symm))).2
    rw [List.count_append] at e
    exact List.count_eq_zero.mp (by omega)
  notFirst := by
    intro t
    simp

/-- `cntLab` is strict (lem:position, without the enabledness condition). -/
theorem cntLab_strict (Q : Prog) : (cntLab Q).Strict where
  started := by
    intro S t a _ hn
    have hn' : (if 1 ≤ S.count t then some (t, S.count t) else none) = some a := hn
    split_ifs at hn' with hc
    exact List.count_pos_iff.mp hc
  backStability := by
    intro S t t' a _ hn hne
    have hn' : (if 1 ≤ (t' :: S).count t then some (t, (t' :: S).count t) else none) = some a :=
      hn
    rw [List.count_cons_of_ne hne] at hn'
    exact hn'

namespace Labelling

variable {Q : Prog} (E : Labelling Q (Tid × ℕ))

/-- The labelling names the steps of `Q` as the position labelling does
(lem:position): the step of `t` after `S` has the name `(t, count t S)` if
`t` has taken a step in `S`, and no name otherwise. -/
def IsPos : Prop :=
  ∀ ⦃S : Sched⦄ ⦃t : Tid⦄, t :: S ∈ Q.mem →
    E.next S t = if 1 ≤ S.count t then some (t, S.count t) else none

end Labelling

/-- The labelling of lem:position names the steps of `Q` by positions. -/
theorem posLab_isPos {Q : Prog} (hQ : Q.Local) : (posLab Q hQ).IsPos := by
  intro S t h
  rw [posLab_next]
  unfold posNext
  by_cases hc : 1 ≤ S.count t
  · rw [ite_eq_left ⟨hc, h⟩, ite_eq_left hc]
  · rw [ite_eq_right (fun k => hc k.1), ite_eq_right hc]

/-- `cntLab` names the steps of `Q` by positions. -/
theorem cntLab_isPos (Q : Prog) : (cntLab Q).IsPos := fun _ _ _ => rfl

/-! ### The order word (def:positions) -/

/-- The order word of a schedule (def:positions), the latest position at the
head: the step of `t` after `S` contributes `(t, count t S)` unless it is
the first step of `t`. -/
def ord : Sched → List (Tid × ℕ)
  | [] => []
  | t :: S => if 1 ≤ S.count t then (t, S.count t) :: ord S else ord S

/-- The order word of the empty schedule. -/
@[simp] theorem ord_nil : ord [] = [] := rfl

/-- Unfolding of `ord` at a step. -/
theorem ord_cons (t : Tid) (S : Sched) :
    ord (t :: S) = if 1 ≤ S.count t then (t, S.count t) :: ord S else ord S := rfl

/-- def:positions: the position `(t, i)` occurs in `ord S` iff `1 ≤ i` and
`t` has taken more than `i` steps in `S`. -/
theorem mem_ord_iff {S : Sched} {t : Tid} {i : ℕ} :
    (t, i) ∈ ord S ↔ 1 ≤ i ∧ i < S.count t := by
  induction S with
  | nil => simp
  | cons u S ih =>
    rw [ord_cons]
    by_cases hut : u = t
    · subst hut
      rw [List.count_cons_self]
      by_cases hc : 1 ≤ S.count u
      · rw [ite_eq_left hc, List.mem_cons, ih, Prod.mk.injEq]
        constructor
        · rintro (⟨-, rfl⟩ | h) <;> omega
        · intro h
          by_cases e : i = S.count u
          · exact Or.inl ⟨rfl, e⟩
          · exact Or.inr (by omega)
      · rw [ite_eq_right hc, ih]
        omega
    · rw [List.count_cons_of_ne hut]
      by_cases hc : 1 ≤ S.count u
      · rw [ite_eq_left hc, List.mem_cons, ih, Prod.mk.injEq]
        exact ⟨fun h => h.resolve_left (fun k => hut k.1.symm), Or.inr⟩
      · rw [ite_eq_right hc, ih]

/-- lem:position, second part: for a labelling by positions, `(t, i)` is
emitted in `S` iff `1 ≤ i` and `t` has taken more than `i` steps in `S`
(the step that emits `(t, i)` is the step with index `i` of `t`). -/
theorem Labelling.IsPos.mem_names_iff {Q : Prog} {E : Labelling Q (Tid × ℕ)} (hE : E.IsPos)
    {S : Sched} (h : S ∈ Q.mem) {t : Tid} {i : ℕ} :
    (t, i) ∈ E.names S ↔ 1 ≤ i ∧ i < S.count t := by
  induction S with
  | nil => simp
  | cons u S ih =>
    have hstep : (t, i) ∈ {a | E.next S u = some a} ↔ 1 ≤ S.count u ∧ u = t ∧ S.count u = i := by
      change E.next S u = some (t, i) ↔ _
      rw [hE h]
      by_cases hc : 1 ≤ S.count u
      · rw [ite_eq_left hc, Option.some.injEq, Prod.mk.injEq]
        exact ⟨fun k => ⟨hc, k⟩, fun k => k.2⟩
      · rw [ite_eq_right hc]
        simp only [reduceCtorEq, false_iff]
        exact fun k => hc k.1
    rw [E.names_cons h, Set.mem_union, ih (Q.tail_mem h), hstep]
    by_cases hut : u = t
    · subst hut
      rw [List.count_cons_self]
      constructor
      · rintro (h | ⟨h, -, rfl⟩) <;> omega
      · intro h
        by_cases e : S.count u = i
        · exact Or.inr ⟨by omega, rfl, e⟩
        · exact Or.inl (by omega)
    · rw [List.count_cons_of_ne hut]
      exact ⟨fun k => k.resolve_right (fun k' => hut k'.2.1), Or.inl⟩

/-- lem:position, second part, for the labelling of lem:position. -/
theorem mem_names_posLab {Q : Prog} (hQ : Q.Local) {S : Sched} (h : S ∈ Q.mem) {t : Tid}
    {i : ℕ} : (t, i) ∈ (posLab Q hQ).names S ↔ 1 ≤ i ∧ i < S.count t :=
  (posLab_isPos hQ).mem_names_iff h

/-- lem:position and def:positions: the names emitted in `S` are the
positions that occur in `ord S`. -/
theorem Labelling.IsPos.mem_names_iff_mem_ord {Q : Prog} {E : Labelling Q (Tid × ℕ)}
    (hE : E.IsPos) {S : Sched} (h : S ∈ Q.mem) {x : Tid × ℕ} : x ∈ E.names S ↔ x ∈ ord S := by
  obtain ⟨t, i⟩ := x
  rw [hE.mem_names_iff h, mem_ord_iff]

/-- The labelling of lem:position and `cntLab` emit the same names in every
schedule of `Q`. -/
theorem names_posLab_eq_cntLab {Q : Prog} (hQ : Q.Local) {S : Sched} (h : S ∈ Q.mem) :
    (posLab Q hQ).names S = (cntLab Q).names S := by
  ext x
  rw [(posLab_isPos hQ).mem_names_iff_mem_ord h, (cntLab_isPos Q).mem_names_iff_mem_ord h]

/-- def:positions: `ord S'` is a prefix of `ord S` for a prefix `S'` of `S`
(a suffix of the lists, as the latest element is at the head). -/
theorem ord_suffix {S S' : Sched} (hs : S' <:+ S) : ord S' <:+ ord S := by
  induction S with
  | nil => rw [List.suffix_nil.mp hs]
  | cons t S ih =>
    rcases List.suffix_cons_iff.mp hs with rfl | hs'
    · exact List.suffix_refl _
    · rw [ord_cons]
      split_ifs
      · exact (ih hs').trans (List.suffix_cons _ _)
      · exact ih hs'

/-- def:positions: every prefix of `ord S` is `ord S'` for a prefix `S'` of
`S`. -/
theorem exists_ord_eq_of_suffix {S : Sched} {s : List (Tid × ℕ)} (hs : s <:+ ord S) :
    ∃ S', S' <:+ S ∧ ord S' = s := by
  induction S with
  | nil => exact ⟨[], List.suffix_refl _, (List.suffix_nil.mp hs).symm⟩
  | cons t S ih =>
    by_cases hc : 1 ≤ S.count t
    · rw [ord_cons, ite_eq_left hc] at hs
      rcases List.suffix_cons_iff.mp hs with rfl | hs'
      · exact ⟨t :: S, List.suffix_refl _, by rw [ord_cons, ite_eq_left hc]⟩
      · obtain ⟨S', h, e⟩ := ih hs'
        exact ⟨S', h.trans (List.suffix_cons _ _), e⟩
    · rw [ord_cons, ite_eq_right hc] at hs
      obtain ⟨S', h, e⟩ := ih hs
      exact ⟨S', h.trans (List.suffix_cons _ _), e⟩

/-- def:positions: `ord S` lists the positions without repetition. -/
theorem ord_nodup (S : Sched) : (ord S).Nodup := by
  induction S with
  | nil => exact List.nodup_nil
  | cons t S ih =>
    rw [ord_cons]
    split_ifs
    · refine List.nodup_cons.mpr ⟨fun hm => ?_, ih⟩
      have := (mem_ord_iff.mp hm).2
      omega
    · exact ih

/-- def:positions and lem:viol-order (the step of its proof): for `x ≠ y`,
`x` occurs before `y` in `ord S` iff `y` occurs in `ord S` and every prefix
of `S` whose order word contains `y` also contains `x`. -/
theorem before_ord_iff {S : Sched} {x y : Tid × ℕ} (hxy : x ≠ y) :
    Before (ord S) x y ↔ y ∈ ord S ∧ ∀ S', S' <:+ S → y ∈ ord S' → x ∈ ord S' := by
  induction S with
  | nil =>
    constructor
    · intro h
      exact (not_before_nil h).elim
    · rintro ⟨h, -⟩
      simp at h
  | cons t S ih =>
    by_cases hc : 1 ≤ S.count t
    · have hz : (t, S.count t) ∉ ord S := fun hm => by
        have := (mem_ord_iff.mp hm).2
        omega
      have ho : ord (t :: S) = (t, S.count t) :: ord S := by rw [ord_cons, ite_eq_left hc]
      rw [ho, before_cons_iff]
      constructor
      · rintro (⟨e, hx⟩ | hb)
        · refine ⟨List.mem_cons.mpr (Or.inl e.symm), fun S' hs hy => ?_⟩
          rcases List.suffix_cons_iff.mp hs with rfl | hs'
          · rw [ho]
            exact List.mem_cons_of_mem _ hx
          · rw [← e] at hy
            exact absurd ((ord_suffix hs').subset hy) hz
        · obtain ⟨hy, hall⟩ := ih.mp hb
          refine ⟨List.mem_cons_of_mem _ hy, fun S' hs hy' => ?_⟩
          rcases List.suffix_cons_iff.mp hs with rfl | hs'
          · rw [ho]
            exact List.mem_cons_of_mem _ hb.mem_left
          · exact hall S' hs' hy'
      · rintro ⟨hy, hall⟩
        rcases List.mem_cons.mp hy with e | hy'
        · have hx : x ∈ ord (t :: S) := hall _ (List.suffix_refl _) (by rw [ho]; exact hy)
          rw [ho] at hx
          rcases List.mem_cons.mp hx with e' | hx'
          · exact absurd (e'.trans e.symm) hxy
          · exact Or.inl ⟨e.symm, hx'⟩
        · exact Or.inr (ih.mpr ⟨hy', fun S' hs => hall S' (hs.trans (List.suffix_cons _ _))⟩)
    · have ho : ord (t :: S) = ord S := by rw [ord_cons, ite_eq_right hc]
      rw [ho, ih]
      refine and_congr_right fun _ => ⟨fun hall S' hs hy => ?_, fun hall S' hs =>
        hall S' (hs.trans (List.suffix_cons _ _))⟩
      rcases List.suffix_cons_iff.mp hs with rfl | hs'
      · rw [ho] at hy ⊢
        exact hall S (List.suffix_refl _) hy
      · exact hall S' hs' hy

/-- lem:viol-order, the step of its proof: for a target `y` that occurs in
`ord S` and `x ≠ y`, `x` does not occur before `y` iff some prefix of `S`
has `y` and not `x` in its order word. -/
theorem not_before_ord_iff {S : Sched} {x y : Tid × ℕ} (hxy : x ≠ y) (hy : y ∈ ord S) :
    ¬ Before (ord S) x y ↔ ∃ S', S' <:+ S ∧ y ∈ ord S' ∧ x ∉ ord S' := by
  rw [before_ord_iff hxy]
  constructor
  · intro h
    by_contra hno
    exact h ⟨hy, fun S' hs hy' => by_contra fun hx => hno ⟨S', hs, hy', hx⟩⟩
  · rintro ⟨S', hs, hy', hx⟩ ⟨-, hall⟩
    exact hx (hall S' hs hy')

/-- def:positions and lem:position: `x` occurs before `y` in the order word
iff `y` is emitted in `S` and every prefix of `S` that emits `y` has emitted
`x` (for `x ≠ y`). -/
theorem Labelling.IsPos.before_ord_iff_names {Q : Prog} {E : Labelling Q (Tid × ℕ)}
    (hE : E.IsPos) {S : Sched} (h : S ∈ Q.mem) {x y : Tid × ℕ} (hxy : x ≠ y) :
    Before (ord S) x y ↔ y ∈ E.names S ∧ ∀ S', S' <:+ S → y ∈ E.names S' → x ∈ E.names S' := by
  rw [before_ord_iff hxy, hE.mem_names_iff_mem_ord h]
  refine and_congr_right fun _ => forall_congr' fun S' => forall_congr' fun hs => ?_
  rw [hE.mem_names_iff_mem_ord (Q.suffix_mem h hs), hE.mem_names_iff_mem_ord (Q.suffix_mem h hs)]

/-! ### Violation and order (lem:viol-order) -/

/-- A directive read as a directive on positions in the sense of
`Hitting.lean` and `Static.lean` (the labelling is not part of either
structure). -/
def Directive.toPDir {L : Type} {d : ℕ} (D : Directive L d) : PDir L d where
  A := D.A
  b := D.b
  b_inj := D.b_inj

/-- lem:viol-order: for a labelling by positions and a schedule `S` of `Q`,
`S` p-violates `D` iff the order word of `S` violates `D` in the sense of
`Static.lean`. -/
theorem Labelling.IsPos.pviolates_iff_viol {Q : Prog} {E : Labelling Q (Tid × ℕ)}
    (hE : E.IsPos) {d : ℕ} (D : Directive (Tid × ℕ) d) {S : Sched} (h : S ∈ Q.mem) :
    D.PViolates E S ↔ Viol (ord S) D.toPDir := by
  have hnm : ∀ {S'}, S' <:+ S → ∀ x, x ∈ E.names S' ↔ x ∈ ord S' := fun hs _ =>
    hE.mem_names_iff_mem_ord (Q.suffix_mem h hs)
  constructor
  · rintro ⟨S', hs, ⟨i, a, haA, hb, ha⟩ | ⟨i, j, hij, hb, ha⟩⟩
    · rw [hnm hs] at hb ha
      have hne : a ≠ D.b i := fun e => ha (e ▸ hb)
      have hbS : D.b i ∈ ord S := (ord_suffix hs).subset hb
      exact ⟨i, hbS, Or.inl ⟨a, haA, hne, (not_before_ord_iff hne hbS).mpr ⟨S', hs, hb, ha⟩⟩⟩
    · rw [hnm hs] at hb ha
      have hne : D.b i ≠ D.b j := fun e => ha (e ▸ hb)
      have hbS : D.b j ∈ ord S := (ord_suffix hs).subset hb
      exact ⟨j, hbS, Or.inr ⟨i, hij, (not_before_ord_iff hne hbS).mpr ⟨S', hs, hb, ha⟩⟩⟩
  · rintro ⟨i, hbS, ⟨c, hcA, hne, hnb⟩ | ⟨j, hji, hnb⟩⟩
    · obtain ⟨S', hs, hb, hc⟩ := (not_before_ord_iff hne hbS).mp hnb
      refine ⟨S', hs, Or.inl ⟨i, c, hcA, ?_, ?_⟩⟩
      · exact (hnm hs _).mpr hb
      · exact fun k => hc ((hnm hs _).mp k)
    · have hne : D.b j ≠ D.b i := fun e => (ne_of_lt hji) (D.b_inj e)
      obtain ⟨S', hs, hb, hc⟩ := (not_before_ord_iff hne hbS).mp hnb
      refine ⟨S', hs, Or.inr ⟨j, i, hji, ?_, ?_⟩⟩
      · exact (hnm hs _).mpr hb
      · exact fun k => hc ((hnm hs _).mp k)

/-- lem:viol-order, with the criterion written out: `S` p-violates `D` iff
some target `b_i` occurs in `ord S` and some `c ∈ A_i \ {b_i}` or some
earlier target `b_j`, `j < i`, does not occur before `b_i` in `ord S`. -/
theorem Labelling.IsPos.pviolates_iff {Q : Prog} {E : Labelling Q (Tid × ℕ)}
    (hE : E.IsPos) {d : ℕ} (D : Directive (Tid × ℕ) d) {S : Sched} (h : S ∈ Q.mem) :
    D.PViolates E S ↔
      ∃ i, D.b i ∈ ord S ∧ ((∃ c ∈ D.A i, c ≠ D.b i ∧ ¬ Before (ord S) c (D.b i)) ∨
        ∃ j, j < i ∧ ¬ Before (ord S) (D.b j) (D.b i)) :=
  hE.pviolates_iff_viol D h

/-- lem:viol-order for the labelling of lem:position. -/
theorem pviolates_posLab_iff {Q : Prog} (hQ : Q.Local) {d : ℕ} (D : Directive (Tid × ℕ) d)
    {S : Sched} (h : S ∈ Q.mem) :
    D.PViolates (posLab Q hQ) S ↔
      ∃ i, D.b i ∈ ord S ∧ ((∃ c ∈ D.A i, c ≠ D.b i ∧ ¬ Before (ord S) c (D.b i)) ∨
        ∃ j, j < i ∧ ¬ Before (ord S) (D.b j) (D.b i)) :=
  (posLab_isPos hQ).pviolates_iff D h

/-- lem:viol-order for `cntLab`, for every prefix-closed schedule set. -/
theorem pviolates_cntLab_iff (Q : Prog) {d : ℕ} (D : Directive (Tid × ℕ) d)
    {S : Sched} (h : S ∈ Q.mem) :
    D.PViolates (cntLab Q) S ↔ Viol (ord S) D.toPDir :=
  (cntLab_isPos Q).pviolates_iff_viol D h

end Pct
