import Mazurkiewicz.Pct.Hitting

/-!
# Partial schedules of a finite poset and p-guarantees

`pctdpor`, `depth.tex`, sec:static, the parts that concern partial schedules:
lem:static-cond1, thm:static (1) and (2), and direction `≥` of prop:sh-eq,
for an arbitrary finite poset in place of `(Pos_P, <)`.

How the text is read here.

* A partial schedule is a list of distinct elements, the latest element at
  the head, in which every element comes after all smaller elements
  (`PSched`). It stands for the order word `ord(S)` of a schedule `S` of a
  static program; a step of a thread that emits no position is not
  represented. This is this file's reading: lem:static-sched covers complete
  schedules only, and the text does not state that the order words of the
  partial schedules of a static `P⁺` are exactly the `PSched` lists of
  `(Pos_P, <)`. The proofs of lem:static-cond1 and of condition 1 in
  thm:static (2) use this fact silently ("its step emits a position
  `c' ≤ c` that does not occur in `ord(S)`").
* The names of a directive are elements of the poset (`PDir X d`), that is,
  positions. The text allows other names in `A_i` and `b_i`. A directive
  with a name that is not a position never p-guarantees a bug: condition 1
  gives a complete schedule that does not p-violate it, and that schedule
  does not emit all targets. So the restriction loses nothing; this argument
  is not formalised.
* `Viol s D` is the right-hand side of lem:viol-order, taken as the
  definition of "`s` p-violates `D`". The operational definition of
  p-violation and lem:viol-order itself are in `Position.lean`
  (`Labelling.IsPos.pviolates_iff_viol`).
* A complete partial schedule is the same thing as a `LinExt`
  (`LinExt.ofSched`, `exists_sched_of_linExt`; lem:static-sched read on the
  poset), and on complete schedules `¬ Viol` is `Sat` of `Hitting.lean`
  (`viol_complete_iff`).
* A bug is a set `B` of lists; it stands for the set of the order words of
  the complete schedules of `\widehat{B}`. For a graph bug this reading needs
  that membership of a complete schedule in `\widehat{B}` depends only on its
  order word (lem:ord-graph, `G_α` is well defined), which is not formalised.
  `PGuar D B` is "`D` p-guarantees `B`" (conditions 1 and 2), without the
  requirement that the schedules of condition 2 emit all targets: as the
  names are positions, every complete schedule emits them.
* `Viol` is a predicate on the whole list, while the text asks for a
  violating prefix; `viol_cons` (a violation persists under a step) is what
  makes the two agree, and `not_viol_cons_of_not_target` is lem:emission (3)
  read on lists.

Not formalised: programs, static programs (def:static), the map `ord` from schedules of a
static program to these lists (`Position.lean` defines `ord` on thread
sequences only),
lem:static-sched for programs, the depths `hdep`, `shdep`, `pdep` as numbers
(only the implications between the guarantees are proved), and direction `≤`
of prop:sh-eq as a statement about depths (it is `stronglyGuar_of_pguar`,
and `stronglyGuar_of_pguar_linExt` for the quantification over schedules
`α` of the poset).
-/

namespace Pct

variable {X : Type} [PartialOrder X] {d : ℕ}

/-! ### Partial schedules -/

/-- A partial schedule of the poset, the latest element at the head: the
elements are distinct and every element comes after all smaller ones. This
is this file's reading of the order words of the partial schedules of a
static program (def:static); lem:static-sched states it for complete
schedules only, and lem:static-cond1 and thm:static (2) use the partial
version without stating it. -/
def PSched : List X → Prop
  | [] => True
  | x :: s => PSched s ∧ x ∉ s ∧ ∀ y, y < x → y ∈ s

/-- The partial schedule contains every element (a complete schedule). -/
def Complete (s : List X) : Prop := ∀ x, x ∈ s

/-- `x` occurs before `y` in `s` (both occur; the head is the latest). -/
def Before : List X → X → X → Prop
  | [], _, _ => False
  | z :: s, x, y => (z = y ∧ x ∈ s) ∨ Before s x y

/-- The empty list is a partial schedule. -/
theorem psched_nil : PSched ([] : List X) := trivial

/-- Unfolding of `PSched` at a step. -/
theorem psched_cons {x : X} {s : List X} :
    PSched (x :: s) ↔ PSched s ∧ x ∉ s ∧ ∀ y, y < x → y ∈ s := Iff.rfl

omit [PartialOrder X] in
/-- Nothing occurs in the empty schedule. -/
theorem not_before_nil {x y : X} : ¬ Before ([] : List X) x y := id

omit [PartialOrder X] in
/-- Unfolding of `Before` at a step. -/
theorem before_cons_iff {z x y : X} {s : List X} :
    Before (z :: s) x y ↔ (z = y ∧ x ∈ s) ∨ Before s x y := Iff.rfl

omit [PartialOrder X] in
/-- A step with an element other than `y` does not change what is before
`y`. -/
theorem before_cons_of_ne {z x y : X} {s : List X} (h : z ≠ y) :
    Before (z :: s) x y ↔ Before s x y := by
  rw [before_cons_iff]
  exact ⟨fun k => k.resolve_left (fun k' => h k'.1), Or.inr⟩

omit [PartialOrder X] in
/-- The earlier element of `Before` occurs. -/
theorem Before.mem_left {s : List X} {x y : X} (h : Before s x y) : x ∈ s := by
  induction s with
  | nil => exact (not_before_nil h).elim
  | cons z s ih =>
    rcases before_cons_iff.mp h with ⟨-, h⟩ | h
    · exact List.mem_cons_of_mem _ h
    · exact List.mem_cons_of_mem _ (ih h)

omit [PartialOrder X] in
/-- The later element of `Before` occurs. -/
theorem Before.mem_right {s : List X} {x y : X} (h : Before s x y) : y ∈ s := by
  induction s with
  | nil => exact (not_before_nil h).elim
  | cons z s ih =>
    rcases before_cons_iff.mp h with ⟨e, -⟩ | h
    · exact List.mem_cons.mpr (Or.inl e.symm)
    · exact List.mem_cons_of_mem _ (ih h)

/-- A partial schedule has no repetition. -/
theorem PSched.nodup {s : List X} (hs : PSched s) : s.Nodup := by
  induction s with
  | nil => exact List.nodup_nil
  | cons z s ih =>
    obtain ⟨hs', hz, -⟩ := psched_cons.mp hs
    exact List.nodup_cons.mpr ⟨hz, ih hs'⟩

/-- `Before` is irreflexive on a partial schedule. -/
theorem PSched.before_irrefl {s : List X} (hs : PSched s) (x : X) : ¬ Before s x x := by
  induction s with
  | nil => exact not_before_nil
  | cons z s ih =>
    obtain ⟨hs', hz, -⟩ := psched_cons.mp hs
    intro h
    rcases before_cons_iff.mp h with ⟨e, hx⟩ | h
    · rw [e] at hz
      exact hz hx
    · exact ih hs' h

/-- `Before` is transitive on a partial schedule. -/
theorem PSched.before_trans {s : List X} (hs : PSched s) {x y z : X}
    (h : Before s x y) (k : Before s y z) : Before s x z := by
  induction s with
  | nil => exact (not_before_nil h).elim
  | cons w s ih =>
    obtain ⟨hs', hw, -⟩ := psched_cons.mp hs
    rcases before_cons_iff.mp h with ⟨e, hx⟩ | h
    · have hy : y ∈ s := by
        rcases before_cons_iff.mp k with ⟨-, hy⟩ | k
        · exact hy
        · exact k.mem_left
      rw [e] at hw
      exact absurd hy hw
    · rcases before_cons_iff.mp k with ⟨e, -⟩ | k
      · exact before_cons_iff.mpr (Or.inl ⟨e, h.mem_left⟩)
      · exact before_cons_iff.mpr (Or.inr (ih hs' h k))

omit [PartialOrder X] in
/-- Two elements that occur are equal or one is before the other. -/
theorem before_total {s : List X} {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    Before s x y ∨ x = y ∨ Before s y x := by
  induction s with
  | nil => simp at hx
  | cons w s ih =>
    rcases List.mem_cons.mp hx with ex | hx
    · rcases List.mem_cons.mp hy with ey | hy
      · exact Or.inr (Or.inl (ex.trans ey.symm))
      · exact Or.inr (Or.inr (before_cons_iff.mpr (Or.inl ⟨ex.symm, hy⟩)))
    · rcases List.mem_cons.mp hy with ey | hy
      · exact Or.inl (before_cons_iff.mpr (Or.inl ⟨ey.symm, hx⟩))
      · rcases ih hx hy with h | h | h
        · exact Or.inl (before_cons_iff.mpr (Or.inr h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (before_cons_iff.mpr (Or.inr h)))

/-- In a partial schedule a smaller element is before a larger one that
occurs. -/
theorem PSched.before_of_lt {s : List X} (hs : PSched s) {x y : X} (h : x < y)
    (hy : y ∈ s) : Before s x y := by
  induction s with
  | nil => simp at hy
  | cons w s ih =>
    obtain ⟨hs', -, hdown⟩ := psched_cons.mp hs
    rcases List.mem_cons.mp hy with e | hy
    · refine before_cons_iff.mpr (Or.inl ⟨e.symm, hdown x ?_⟩)
      rw [← e]
      exact h
    · exact before_cons_iff.mpr (Or.inr (ih hs' hy))

/-- Among the elements of a partial schedule `l` that do not occur in `s`,
there is a first one in `l` (the position `c` in the proof of
lem:static-cond1). -/
theorem PSched.exists_first_missing {l : List X} (hl : PSched l) (s : List X)
    (h : ∃ c ∈ l, c ∉ s) : ∃ m ∈ l, m ∉ s ∧ ∀ x, Before l x m → x ∈ s := by
  induction l with
  | nil =>
    obtain ⟨c, hc, -⟩ := h
    simp at hc
  | cons z l ih =>
    obtain ⟨hl', hz, -⟩ := psched_cons.mp hl
    by_cases h' : ∃ c ∈ l, c ∉ s
    · obtain ⟨m, hm, hms, hmin⟩ := ih hl' h'
      refine ⟨m, List.mem_cons_of_mem _ hm, hms, fun x hx => ?_⟩
      rcases before_cons_iff.mp hx with ⟨e, -⟩ | hx
      · rw [e] at hz
        exact absurd hm hz
      · exact hmin x hx
    · have hall : ∀ c ∈ l, c ∈ s := fun c hc => by
        by_contra hcs
        exact h' ⟨c, hc, hcs⟩
      obtain ⟨c, hc, hcs⟩ := h
      have hzs : z ∉ s := by
        rcases List.mem_cons.mp hc with e | hc
        · rw [← e]
          exact hcs
        · exact absurd (hall c hc) hcs
      refine ⟨z, List.mem_cons.mpr (Or.inl rfl), hzs, fun x hx => hall x ?_⟩
      rcases before_cons_iff.mp hx with ⟨-, hx⟩ | hx
      · exact hx
      · exact hx.mem_left

/-! ### Complete partial schedules and linear extensions -/

/-- The schedule of a complete partial schedule: its strict order is
`Before s` (lem:static-sched, first half, read on the poset). -/
def LinExt.ofSched (s : List X) (hs : PSched s) (hc : Complete s) : LinExt X where
  lt := Before s
  irrefl := hs.before_irrefl
  trans := fun h k => hs.before_trans h k
  total := fun x y => before_total (hc x) (hc y)
  ext := fun {_ y} h => hs.before_of_lt h (hc y)

/-- Two schedules with the same strict order are equal. (`LinExt.ext` is
the name of a field of `LinExt`.) -/
theorem LinExt.eq_of_lt {α β : LinExt X} (h : ∀ x y, α.lt x y ↔ β.lt x y) : α = β := by
  cases α with
  | mk lt₁ _ _ _ _ =>
    cases β with
    | mk lt₂ _ _ _ _ =>
      have e : lt₁ = lt₂ := funext fun x => funext fun y => propext (h x y)
      subst e
      rfl

/-- A partial schedule that can be extended while a property holds reaches a
complete partial schedule with the property (the iteration "from the empty
schedule" in the proofs of thm:static (1) and lem:static-sched). -/
theorem exists_complete_of_step [Finite X] (P : List X → Prop) (h0 : P [])
    (hstep : ∀ s, PSched s → P s → ¬ Complete s → ∃ x, PSched (x :: s) ∧ P (x :: s)) :
    ∃ s, PSched s ∧ Complete s ∧ P s := by
  have := Fintype.ofFinite X
  have key : ∀ n : ℕ, (∃ s, PSched s ∧ Complete s ∧ P s) ∨
      ∃ s, PSched s ∧ P s ∧ s.length = n := by
    intro n
    induction n with
    | zero => exact Or.inr ⟨[], psched_nil, h0, rfl⟩
    | succ n ih =>
      rcases ih with h | ⟨s, hs, hP, hl⟩
      · exact Or.inl h
      · by_cases hc : Complete s
        · exact Or.inl ⟨s, hs, hc, hP⟩
        · obtain ⟨x, hxs, hxP⟩ := hstep s hs hP hc
          exact Or.inr ⟨x :: s, hxs, hxP, by simp [hl]⟩
  rcases key (Fintype.card X + 1) with h | ⟨s, hs, -, hl⟩
  · exact h
  · have := hs.nodup.length_le_card
    omega

/-- A nonempty set has a first element in a schedule of a finite poset. -/
theorem LinExt.exists_min [Finite X] (α : LinExt X) (S : Set X) (hS : S.Nonempty) :
    ∃ m ∈ S, ∀ x ∈ S, ¬ α.lt x m := by
  have : IsTrans X α.lt := ⟨fun _ _ _ => α.trans⟩
  have : Std.Irrefl α.lt := ⟨α.irrefl⟩
  have wf : WellFounded α.lt := Finite.wellFounded_of_trans_of_irrefl α.lt
  exact wf.has_min S hS

/-- Every schedule of a finite poset is the order of a complete partial
schedule (lem:static-sched, second half, read on the poset). -/
theorem exists_sched_of_linExt [Finite X] (α : LinExt X) :
    ∃ s : List X, PSched s ∧ Complete s ∧ ∀ x y, Before s x y ↔ α.lt x y := by
  have step : ∀ s : List X, PSched s →
      ((∀ x ∈ s, ∀ y, α.lt y x → y ∈ s) ∧ ∀ x y, y ∈ s → (Before s x y ↔ α.lt x y)) →
      ¬ Complete s → ∃ m, PSched (m :: s) ∧
        ((∀ x ∈ m :: s, ∀ y, α.lt y x → y ∈ m :: s) ∧
          ∀ x y, y ∈ m :: s → (Before (m :: s) x y ↔ α.lt x y)) := by
    rintro s hs ⟨hdown, hiff⟩ hc
    have hne : ({x | x ∉ s} : Set X).Nonempty := by
      by_contra h
      apply hc
      intro x
      by_contra hx
      exact h ⟨x, hx⟩
    obtain ⟨m, hm, hmin⟩ := α.exists_min _ hne
    have hm' : m ∉ s := hm
    have hlow : ∀ y, α.lt y m → y ∈ s := fun y hy => by
      by_contra hys
      exact hmin y hys hy
    refine ⟨m, psched_cons.mpr ⟨hs, hm', fun y hy => hlow y (α.ext hy)⟩, ?_, ?_⟩
    · intro x hx y hy
      rcases List.mem_cons.mp hx with hxm | hx
      · rw [hxm] at hy
        exact List.mem_cons_of_mem _ (hlow y hy)
      · exact List.mem_cons_of_mem _ (hdown x hx y hy)
    · intro x y hy
      rw [before_cons_iff]
      rcases List.mem_cons.mp hy with hym | hy
      · rw [hym]
        constructor
        · rintro (⟨-, hx⟩ | h)
          · rcases α.total x m with h | h | h
            · exact h
            · rw [h] at hx
              exact absurd hx hm'
            · exact absurd (hdown x hx m h) hm'
          · exact absurd h.mem_right hm'
        · intro h
          exact Or.inl ⟨rfl, hlow x h⟩
      · constructor
        · rintro (⟨e, -⟩ | h)
          · rw [← e] at hy
            exact absurd hy hm'
          · exact (hiff x y hy).mp h
        · intro h
          exact Or.inr ((hiff x y hy).mpr h)
  obtain ⟨s, hs, hc, -, hiff⟩ := exists_complete_of_step
    (fun s : List X => (∀ x ∈ s, ∀ y, α.lt y x → y ∈ s) ∧
      ∀ x y, y ∈ s → (Before s x y ↔ α.lt x y))
    ⟨fun x hx => by simp at hx, fun x y hy => by simp at hy⟩ step
  exact ⟨s, hs, hc, fun x y => hiff x y (hc y)⟩

/-- Every schedule of a finite poset is `LinExt.ofSched` of a complete
partial schedule (lem:static-sched, second half, read on the poset). -/
theorem exists_ofSched_eq [Finite X] (α : LinExt X) :
    ∃ s, ∃ (hs : PSched s) (hc : Complete s), LinExt.ofSched s hs hc = α := by
  obtain ⟨s, hs, hc, hiff⟩ := exists_sched_of_linExt α
  exact ⟨s, hs, hc, LinExt.eq_of_lt hiff⟩

/-! ### p-violation and p-guarantee -/

/-- `s` p-violates the directive. This is the right-hand side of
lem:viol-order, taken as the definition: some target `b_i` occurs in `s` and
some member of `(A_i \ {b_i}) ∪ {b_j | j < i}` does not occur before it. -/
def Viol (s : List X) (D : PDir X d) : Prop :=
  ∃ i, D.b i ∈ s ∧ ((∃ c ∈ D.A i, c ≠ D.b i ∧ ¬ Before s c (D.b i)) ∨
    ∃ j, j < i ∧ ¬ Before s (D.b j) (D.b i))

omit [PartialOrder X] in
/-- lem:viol-order, negated: `s` does not p-violate the directive iff before
every target that occurs come the other members of its set and the earlier
targets. -/
theorem not_viol_iff {s : List X} {D : PDir X d} :
    ¬ Viol s D ↔ ∀ i, D.b i ∈ s →
      (∀ c ∈ D.A i, c ≠ D.b i → Before s c (D.b i)) ∧
        ∀ j, j < i → Before s (D.b j) (D.b i) := by
  constructor
  · intro h i hi
    refine ⟨fun c hc hne => ?_, fun j hj => ?_⟩
    · by_contra hno
      exact h ⟨i, hi, Or.inl ⟨c, hc, hne, hno⟩⟩
    · by_contra hno
      exact h ⟨i, hi, Or.inr ⟨j, hj, hno⟩⟩
  · rintro h ⟨i, hi, ⟨c, hc, hne, hno⟩ | ⟨j, hj, hno⟩⟩
    · exact hno ((h i hi).1 c hc hne)
    · exact hno ((h i hi).2 j hj)

/-- A violation persists under a step of a partial schedule. This makes
`Viol`, a predicate on the whole list, a reading of "some prefix violates
the directive" (def:pviolates). -/
theorem viol_cons {x : X} {s : List X} {D : PDir X d} (hx : PSched (x :: s))
    (hv : Viol s D) : Viol (x :: s) D := by
  obtain ⟨-, hxs, -⟩ := psched_cons.mp hx
  obtain ⟨i, hi, h⟩ := hv
  have hne : x ≠ D.b i := fun e => hxs (by rw [e]; exact hi)
  refine ⟨i, List.mem_cons_of_mem _ hi, ?_⟩
  rcases h with ⟨c, hc, hcne, hno⟩ | ⟨j, hj, hno⟩
  · exact Or.inl ⟨c, hc, hcne, fun hb => hno ((before_cons_of_ne hne).mp hb)⟩
  · exact Or.inr ⟨j, hj, fun hb => hno ((before_cons_of_ne hne).mp hb)⟩

omit [PartialOrder X] in
/-- lem:emission (3), read on lists: a step whose element is not a target
creates no violation. -/
theorem not_viol_cons_of_not_target {x : X} {s : List X} {D : PDir X d}
    (hx : ∀ i, D.b i ≠ x) (hv : ¬ Viol s D) : ¬ Viol (x :: s) D := by
  rintro ⟨i, hi, h⟩
  have hne : x ≠ D.b i := fun e => hx i e.symm
  have hi' : D.b i ∈ s := (List.mem_cons.mp hi).resolve_left (hx i)
  apply hv
  refine ⟨i, hi', ?_⟩
  rcases h with ⟨c, hc, hcne, hno⟩ | ⟨j, hj, hno⟩
  · exact Or.inl ⟨c, hc, hcne, fun hb => hno ((before_cons_of_ne hne).mpr hb)⟩
  · exact Or.inr ⟨j, hj, fun hb => hno ((before_cons_of_ne hne).mpr hb)⟩

/-- lem:viol-order for a complete schedule: it does not p-violate the
directive iff its order satisfies `Sat`. -/
theorem viol_complete_iff {s : List X} (hs : PSched s) (hc : Complete s) (D : PDir X d) :
    ¬ Viol s D ↔ Sat (LinExt.ofSched s hs hc) D := by
  rw [not_viol_iff]
  exact ⟨fun h i => h i (hc _), fun h i _ => h i⟩

/-- Condition 1 of "p-guarantees" (def:pviolates): a partial schedule that
is not complete and does not p-violate the directive has a step after which
it still does not. -/
def Cond1 (D : PDir X d) : Prop :=
  ∀ s, PSched s → ¬ Viol s D → ¬ Complete s → ∃ x, PSched (x :: s) ∧ ¬ Viol (x :: s) D

/-- Condition 2 of "p-guarantees" (def:pviolates): every complete schedule
that does not p-violate the directive is in the bug. -/
def Cond2 (D : PDir X d) (B : Set (List X)) : Prop :=
  ∀ s, PSched s → Complete s → ¬ Viol s D → s ∈ B

/-- The directive p-guarantees the bug (def:pviolates, conditions 1 and 2). -/
def PGuar (D : PDir X d) (B : Set (List X)) : Prop := Cond1 D ∧ Cond2 D B

/-- lem:static-cond1: if some complete schedule does not p-violate the
directive, then the directive satisfies condition 1. -/
theorem cond1_of_complete {D : PDir X d} {s₀ : List X} (h₀ : PSched s₀)
    (hc₀ : Complete s₀) (hv₀ : ¬ Viol s₀ D) : Cond1 D := by
  intro s hs hv hc
  rw [not_viol_iff] at hv₀ hv
  have hex : ∃ c ∈ s₀, c ∉ s := by
    by_contra h
    apply hc
    intro x
    by_contra hx
    exact h ⟨x, hc₀ x, hx⟩
  obtain ⟨m, -, hms, hmin⟩ := h₀.exists_first_missing s hex
  refine ⟨m, psched_cons.mpr ⟨hs, hms, fun y hy => hmin y (h₀.before_of_lt hy (hc₀ m))⟩, ?_⟩
  rw [not_viol_iff]
  intro i hi
  have key : ∀ r, Before s₀ r (D.b i) → (D.b i ∈ s → Before s r (D.b i)) →
      Before (m :: s) r (D.b i) := by
    intro r h0 h1
    rcases List.mem_cons.mp hi with e | hi'
    · rw [e] at h0
      exact before_cons_iff.mpr (Or.inl ⟨e.symm, hmin r h0⟩)
    · exact before_cons_iff.mpr (Or.inr (h1 hi'))
  exact ⟨fun c hc' hne => key c ((hv₀ i (hc₀ _)).1 c hc' hne) (fun hb => (hv i hb).1 c hc' hne),
    fun j hj => key (D.b j) ((hv₀ i (hc₀ _)).2 j hj) (fun hb => (hv i hb).2 j hj)⟩

/-- Condition 1, applied from the empty schedule, gives a complete schedule
that does not p-violate the directive (first step of the proof of
thm:static (1)). -/
theorem exists_complete_of_cond1 [Finite X] {D : PDir X d} (h : Cond1 D) :
    ∃ s, PSched s ∧ Complete s ∧ ¬ Viol s D := by
  refine exists_complete_of_step (fun s => ¬ Viol s D) ?_ h
  rintro ⟨i, hi, -⟩
  simp at hi

/-- thm:static (1): if the directive p-guarantees the bug, then every
complete schedule that strongly hits its targets is in the bug. -/
theorem stronglyGuar_of_pguar [Finite X] {D : PDir X d} {B : Set (List X)}
    (h : PGuar D B) :
    ∀ s (hs : PSched s) (hc : Complete s),
      StronglyHits (LinExt.ofSched s hs hc) D.b → s ∈ B := by
  intro s hs hc hstrong
  obtain ⟨s₀, hs₀, hc₀, hv₀⟩ := exists_complete_of_cond1 h.1
  have h₀ : Sat (LinExt.ofSched s₀ hs₀ hc₀) D := (viol_complete_iff hs₀ hc₀ D).mp hv₀
  exact h.2 s hs hc ((viol_complete_iff hs hc D).mpr (sat_of_stronglyHits h₀ hstrong))

/-- thm:static (1), quantified over the schedules of the poset as in the
text: if the directive p-guarantees the bug, then every schedule `α` that
strongly hits its targets is the order of a complete partial schedule in
the bug. -/
theorem stronglyGuar_of_pguar_linExt [Finite X] {D : PDir X d} {B : Set (List X)}
    (h : PGuar D B) (α : LinExt X) (hα : StronglyHits α D.b) :
    ∃ s, ∃ (hs : PSched s) (hc : Complete s), LinExt.ofSched s hs hc = α ∧ s ∈ B := by
  obtain ⟨s, hs, hc, e⟩ := exists_ofSched_eq α
  refine ⟨s, hs, hc, e, stronglyGuar_of_pguar h s hs hc ?_⟩
  rw [e]
  exact hα

/-- thm:static (2): if the tuple guarantees the bug (some complete schedule
hits it, and every complete schedule that hits it is in the bug), then the
directive of the tuple p-guarantees the bug. -/
theorem pguar_chainDir {B : Set (List X)} (a : Fin (d + 1) → X)
    (ha : Function.Injective a)
    (hadm : ∃ s, ∃ (hs : PSched s) (hc : Complete s), Hits (LinExt.ofSched s hs hc) a)
    (hB : ∀ s (hs : PSched s) (hc : Complete s), Hits (LinExt.ofSched s hs hc) a → s ∈ B) :
    PGuar (chainDir a ha) B := by
  obtain ⟨s₀, hs₀, hc₀, hit₀⟩ := hadm
  refine ⟨cond1_of_complete hs₀ hc₀ ?_, ?_⟩
  · exact (viol_complete_iff hs₀ hc₀ _).mpr ((sat_chainDir_iff _ a ha).mpr hit₀)
  · intro s hs hc hv
    exact hB s hs hc ((sat_chainDir_iff _ a ha).mp ((viol_complete_iff hs hc _).mp hv))

/-- The entries of an injective tuple can be listed in the order of a
schedule (the re-indexing of the targets in the proof of prop:sh-eq). -/
theorem exists_reindex (α : LinExt X) (x : Fin d → X) (hx : Function.Injective x) :
    ∃ σ : Fin d ≃ Fin d, ∀ i j, i < j → α.lt (x (σ i)) (x (σ j)) := by
  classical
  let F : Fin d → Finset (Fin d) := fun i => Finset.univ.filter (fun k => α.lt (x k) (x i))
  have hF : ∀ i k, k ∈ F i ↔ α.lt (x k) (x i) := fun i k => by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
  have hlt : ∀ i j, α.lt (x i) (x j) → (F i).card < (F j).card := by
    intro i j h
    apply Finset.card_lt_card
    refine ⟨fun k hk => ?_, fun hsub => ?_⟩
    · exact (hF j k).mpr (α.trans ((hF i k).mp hk) h)
    · exact α.irrefl _ ((hF i i).mp (hsub ((hF j i).mpr h)))
  have hbound : ∀ i, (F i).card < d := by
    intro i
    have h1 : (F i).card < (Finset.univ : Finset (Fin d)).card := by
      apply Finset.card_lt_card
      refine ⟨Finset.subset_univ _, fun hsub => ?_⟩
      exact α.irrefl _ ((hF i i).mp (hsub (Finset.mem_univ i)))
    simpa using h1
  let r : Fin d → Fin d := fun i => ⟨(F i).card, hbound i⟩
  have hr : ∀ i j, α.lt (x i) (x j) → r i < r j := fun i j h =>
    Fin.mk_lt_mk.mpr (hlt i j h)
  have hinj : Function.Injective r := by
    intro i j hij
    by_contra hne
    rcases α.total (x i) (x j) with h | h | h
    · exact absurd hij (hr i j h).ne
    · exact hne (hx h)
    · exact absurd hij (hr j i h).ne'
  let e : Fin d ≃ Fin d := Equiv.ofBijective r (Finite.injective_iff_bijective.mp hinj)
  refine ⟨e.symm, fun i j hij => ?_⟩
  rcases α.total (x (e.symm i)) (x (e.symm j)) with h | h | h
  · exact h
  · exact absurd (e.symm.injective (hx h)) hij.ne
  · have h2 : e (e.symm j) < e (e.symm i) := hr _ _ h
    rw [e.apply_symm_apply, e.apply_symm_apply] at h2
    exact absurd h2 (lt_asymm hij)

/-- prop:sh-eq, direction `≥`: if the tuple strongly guarantees the bug,
then some directive of the same size p-guarantees it. Its targets are the
entries of the tuple in the order of a strongly hitting schedule, and the
target `x i` has the set `belowSet x i`. -/
theorem exists_pguar_of_stronglyGuar [Finite X] {B : Set (List X)} (x : Fin d → X)
    (hx : Function.Injective x)
    (hB : ∀ s (hs : PSched s) (hc : Complete s),
      StronglyHits (LinExt.ofSched s hs hc) x → s ∈ B) :
    ∃ D : PDir X d, PGuar D B := by
  obtain ⟨α₀, hα₀⟩ := exists_stronglyHits x
  obtain ⟨σ, hσ⟩ := exists_reindex α₀ x hx
  obtain ⟨s₀, hs₀, hc₀, hiff⟩ := exists_sched_of_linExt α₀
  refine ⟨⟨fun i => belowSet x (σ i), fun i => x (σ i), hx.comp σ.injective⟩,
    cond1_of_complete hs₀ hc₀ ?_, ?_⟩
  · rw [not_viol_iff]
    intro i _
    exact ⟨fun c hc hne =>
        (hiff _ _).mpr ((stronglyHits_iff_sets α₀ x).mp hα₀ (σ i) c hc hne),
      fun j hj => (hiff _ _).mpr (hσ j i hj)⟩
  · intro s hs hc hv
    apply hB s hs hc
    rw [stronglyHits_iff_sets]
    intro i c hci hne
    rw [not_viol_iff] at hv
    obtain ⟨k, rfl⟩ := σ.surjective i
    exact (hv k (hc _)).1 c hci hne

end Pct
