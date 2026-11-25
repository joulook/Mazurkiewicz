import Mazurkiewicz.Pct.Program

/-!
# Free steps

`pctdpor`, `bounds.tex`, sec:lower-strict: lem:free (Free steps) and the
schedule part of the proof of prop:lower-strict (1). Everything is proved for
an arbitrary event labelling; `Labelling.Strict` is not used.

How the text is read here.

* lem:free, the definitions. `Directive.ParkedAt D E S t i`: `t` is enabled
  after `S` and its next name is the target `b i` ("parked at `i`").
  `Directive.Parked D E S t`: parked at some `i`. `Directive.FreeStep D E S t`
  is "`S · t` is a free step": `t :: S` is a schedule, and `t` is not parked
  after `S`, or every enabled thread is parked after `S` and no enabled
  thread is parked at an index below that of `t`. "The index of `t`" is
  read as "every index at which `t` is parked"; there is at most one, as
  the targets are distinct (`ParkedAt.index_eq`). `Directive.Free D E S` is
  "all steps of `S` are free": the empty schedule, closed under free steps.
  The definitions do not mention a bug; the text states them inside the
  lemma, under the hypothesis that `D` p-guarantees `B`.
* lem:free, the two cases of the proof. `not_pviolates_cons_of_not_target`:
  a step of an enabled thread whose next name is no target (or which has no
  next name) creates no p-violation; this is lem:emission (3) and needs no
  p-guarantee. `PGuarantees.not_pviolates_cons_of_least`: if every enabled
  thread is parked, the step of the thread parked at the least index creates
  no p-violation; this uses condition 1, lem:emission (1) and (2), clause 2
  of def:directive and Affinity, as in the text.
* lem:free, the statements. `PGuarantees.not_pviolates_freeStep` is the
  first claim, `PGuarantees.not_pviolates_free` the induction on prefixes,
  and `PGuarantees.mem_of_free_complete` the last claim: a complete schedule
  all of whose steps are free is in `B`; `PGuarantees.psatisfies_of_free`
  adds that it emits every target.
* Existence, not stated in the text: `exists_freeStep` (after every partial
  schedule some step is free; no hypothesis on `D`; its proof picks the
  thread parked at the least index, the choice of prop:lower-strict (2),
  part (e)), `Free.exists_complete` (in a bounded program every schedule
  with free steps only extends to a complete one) and
  `PGuarantees.exists_free_complete_mem`. The proof of prop:lower-strict
  does not use these statements.
* The remark after lem:free. `ParkedAt.thr_eq`: only `thr (b i)` can be
  parked at `i`. `freeStep_of_not_thr`, `free_of_forall_not_thr`: the steps
  of threads that are the thread of no target are free.
  `freeStep_of_en_subset`: a step of the only enabled thread is free.
* prop:lower-strict (1), the schedule part ("Let `S₀` be a schedule in which
  `t` does not occur and every other thread has finished, and let `S` be
  `S₀` followed by all steps of `t` ... `S ∈ B`"):
  `Prog.HasLen.mem_of_thr_last` for a schedule set with thread lengths and
  a directive all of whose targets belong to one thread `t`, and
  `Prog.HasLen.mem_of_thr_last_one` for a directive of size 1, where
  `t = thr (b 0)`. As the latest step is at the head, the schedule is
  `List.replicate m t ++ S₀`. `Prog.HasLen.free_of_thr_last`: all steps
  of this schedule are free (no p-guarantee is needed for this).
  `free_append_replicate` and `Free.append_replicate` are the same step for
  an arbitrary schedule set, with the hypothesis that only `t` is enabled
  while `t` runs.

Not formalised: "to advance a thread" and the claim that a parked thread
stays parked while other threads move (the remark after lem:free); the rest
of prop:lower-strict (1), that is, the bug `B_{b'}`, the directive `D'`,
the equality of the families for `sdep` and `pdep`, and the use of
lem:ord-graph (bugs are sets of schedules here, not sets of graphs);
prop:lower-strict (2) and (3); ex:strict-static; the hitting numbers and
the price.
-/

namespace Pct

namespace Directive

variable {Q : Prog} {L : Type} {d : ℕ}

/-! ### Parked threads and free steps (lem:free, the definitions) -/

/-- After `S`, thread `t` is parked at `i`: it is enabled and its next name
is the target `b i` (lem:free). -/
def ParkedAt (D : Directive L d) (E : Labelling Q L) (S : Sched) (t : Tid) (i : Fin d) : Prop :=
  t :: S ∈ Q.mem ∧ E.next S t = some (D.b i)

/-- After `S`, thread `t` is parked (lem:free). -/
def Parked (D : Directive L d) (E : Labelling Q L) (S : Sched) (t : Tid) : Prop :=
  ∃ i, D.ParkedAt E S t i

/-- `S` followed by `t` is a free step (lem:free). -/
def FreeStep (D : Directive L d) (E : Labelling Q L) (S : Sched) (t : Tid) : Prop :=
  t :: S ∈ Q.mem ∧
    (¬ D.Parked E S t ∨
      ((∀ u, u :: S ∈ Q.mem → D.Parked E S u) ∧
        ∀ i, D.ParkedAt E S t i → ∀ u j, D.ParkedAt E S u j → i ≤ j))

/-- All steps of `S` are free (lem:free). -/
inductive Free (D : Directive L d) (E : Labelling Q L) : Sched → Prop
  | nil : Free D E []
  | cons {S : Sched} {t : Tid} : Free D E S → D.FreeStep E S t → Free D E (t :: S)

theorem FreeStep.mem {D : Directive L d} {E : Labelling Q L} {S : Sched} {t : Tid}
    (h : D.FreeStep E S t) : t :: S ∈ Q.mem :=
  h.1

theorem Free.mem {D : Directive L d} {E : Labelling Q L} {S : Sched} (h : D.Free E S) :
    S ∈ Q.mem := by
  cases h with
  | nil => exact Q.nil_mem
  | cons _ hs => exact hs.1

/-- A prefix of a schedule with free steps only has free steps only. -/
theorem Free.suffix {D : Directive L d} {E : Labelling Q L} {S S' : Sched} (h : D.Free E S)
    (hs : S' <:+ S) : D.Free E S' := by
  induction h with
  | nil => rw [List.suffix_nil.mp hs]; exact Free.nil
  | cons hf hstep ih =>
    rcases List.suffix_cons_iff.mp hs with rfl | hs'
    · exact hf.cons hstep
    · exact ih hs'

/-- A thread is parked at one index at most. -/
theorem ParkedAt.index_eq {D : Directive L d} {E : Labelling Q L} {S : Sched} {t : Tid}
    {i j : Fin d} (hi : D.ParkedAt E S t i) (hj : D.ParkedAt E S t j) : i = j :=
  D.b_inj (Option.some.inj (hi.2.symm.trans hj.2))

/-- The remark after lem:free: only `thr (b i)` can be parked at `i`. -/
theorem ParkedAt.thr_eq {D : Directive L d} {E : Labelling Q L} {S : Sched} {t : Tid}
    {i : Fin d} (h : D.ParkedAt E S t i) : E.thr (D.b i) = t :=
  E.affinity (Q.tail_mem h.1) h.2

/-! ### The two cases of lem:free -/

/-- lem:free, first case: a step of an enabled thread whose next name is not
a target creates no p-violation (lem:emission (3)). -/
theorem not_pviolates_cons_of_not_target (D : Directive L d) (E : Labelling Q L) {S : Sched}
    {t : Tid} (h : t :: S ∈ Q.mem) (hS : ¬ D.PViolates E S)
    (hn : ∀ i, E.next S t ≠ some (D.b i)) : ¬ D.PViolates E (t :: S) := by
  rw [pviolates_cons]
  rintro (hv | hv)
  · exact hS hv
  · obtain ⟨i, hi⟩ :=
      D.next_target_of_violates E h (fun hv' => hS ⟨S, List.suffix_refl _, hv'⟩) hv
    exact hn i hi

/-- lem:free, second case: if every enabled thread is parked, the step of
the thread parked at the least index creates no p-violation. -/
theorem PGuarantees.not_pviolates_cons_of_least {D : Directive L d} {E : Labelling Q L}
    {B : Set Sched} (hg : D.PGuarantees E B) {S : Sched} {t : Tid} {i : Fin d}
    (hS : ¬ D.PViolates E S) (hall : ∀ u, u :: S ∈ Q.mem → D.Parked E S u)
    (ht : D.ParkedAt E S t i) (hmin : ∀ u j, D.ParkedAt E S u j → i ≤ j) :
    ¬ D.PViolates E (t :: S) := by
  have hSQ : S ∈ Q.mem := Q.tail_mem ht.1
  obtain ⟨t', ht', hv⟩ := hg.cond1 S ⟨hSQ, t, ht.1⟩ hS
  obtain ⟨j, hj⟩ := hall t' ht'
  rcases (hmin t' j hj).eq_or_lt with rfl | hlt
  · rw [← ht.thr_eq, hj.thr_eq]
    exact hv
  · refine absurd ⟨t' :: S, List.suffix_refl _, Or.inr ⟨i, j, hlt, ?_, ?_⟩⟩ hv
    · rw [E.names_cons ht']
      exact Or.inr hj.2
    · rw [E.names_cons ht']
      rintro (hm | hm)
      · exact E.next_not_mem_names hSQ ht.2 hm
      · have hm' : E.next S t' = some (D.b i) := hm
        rw [hj.2] at hm'
        exact hlt.ne' (D.b_inj (Option.some.inj hm'))

/-! ### lem:free -/

/-- lem:free: a free step after a schedule that does not p-violate `D` gives
a schedule that does not p-violate `D`. -/
theorem PGuarantees.not_pviolates_freeStep {D : Directive L d} {E : Labelling Q L}
    {B : Set Sched} (hg : D.PGuarantees E B) {S : Sched} {t : Tid}
    (hS : ¬ D.PViolates E S) (hf : D.FreeStep E S t) : ¬ D.PViolates E (t :: S) := by
  obtain ⟨hm, hnp | ⟨hall, hmin⟩⟩ := hf
  · exact D.not_pviolates_cons_of_not_target E hm hS fun i hi => hnp ⟨i, hm, hi⟩
  · obtain ⟨i, hi⟩ := hall t hm
    exact hg.not_pviolates_cons_of_least hS hall hi (hmin i hi)

/-- lem:free, the induction: a schedule all of whose steps are free does not
p-violate `D`. -/
theorem PGuarantees.not_pviolates_free {D : Directive L d} {E : Labelling Q L}
    {B : Set Sched} (hg : D.PGuarantees E B) {S : Sched} (hf : D.Free E S) :
    ¬ D.PViolates E S := by
  induction hf with
  | nil => exact D.not_pviolates_nil E
  | cons _ hstep ih => exact hg.not_pviolates_freeStep ih hstep

/-- lem:free, the last claim: a complete schedule all of whose steps are free
is in `B`. -/
theorem PGuarantees.mem_of_free_complete {D : Directive L d} {E : Labelling Q L}
    {B : Set Sched} (hg : D.PGuarantees E B) {S : Sched} (hf : D.Free E S)
    (hc : Q.Complete S) : S ∈ B :=
  (hg.cond2 S hc (hg.not_pviolates_free hf)).2

/-- A complete schedule all of whose steps are free p-satisfies `D`. -/
theorem PGuarantees.psatisfies_of_free {D : Directive L d} {E : Labelling Q L}
    {B : Set Sched} (hg : D.PGuarantees E B) {S : Sched} (hf : D.Free E S)
    (hc : Q.Complete S) : D.PSatisfies E S :=
  (hg.cond2 S hc (hg.not_pviolates_free hf)).1

/-! ### Existence of free steps -/

/-- After a partial schedule some step is free. -/
theorem exists_freeStep (D : Directive L d) (E : Labelling Q L) {S : Sched}
    (hp : Q.Partial S) : ∃ t, D.FreeStep E S t := by
  by_cases h : ∃ u, u :: S ∈ Q.mem ∧ ¬ D.Parked E S u
  · obtain ⟨u, hu, hnp⟩ := h
    exact ⟨u, hu, Or.inl hnp⟩
  · have hall : ∀ u, u :: S ∈ Q.mem → D.Parked E S u := fun u hu =>
      by_contra fun hnp => h ⟨u, hu, hnp⟩
    obtain ⟨-, t₀, ht₀⟩ := hp
    obtain ⟨i₀, hi₀⟩ := hall t₀ ht₀
    obtain ⟨m, ⟨t, ht⟩, hmin⟩ :=
      wellFounded_lt.has_min {i : Fin d | ∃ u, D.ParkedAt E S u i} ⟨i₀, t₀, hi₀⟩
    refine ⟨t, ht.1, Or.inr ⟨hall, fun i hi u j hj => ?_⟩⟩
    rw [hi.index_eq ht]
    exact not_lt.mp (hmin j ⟨u, hj⟩)

/-- In a bounded program a schedule all of whose steps are free extends to a
complete schedule all of whose steps are free. -/
theorem Free.exists_complete {D : Directive L d} {E : Labelling Q L} {k : ℕ}
    (hk : Q.Bounded k) {S : Sched} (hf : D.Free E S) :
    ∃ S', S <:+ S' ∧ D.Free E S' ∧ Q.Complete S' := by
  obtain ⟨n, hn⟩ : ∃ n, n = k - S.length := ⟨_, rfl⟩
  induction n generalizing S with
  | zero =>
    refine ⟨S, List.suffix_refl _, hf, hf.mem, fun t ht => ?_⟩
    have := hk _ ht
    rw [List.length_cons] at this
    omega
  | succ n ih =>
    by_cases hc : Q.Complete S
    · exact ⟨S, List.suffix_refl _, hf, hc⟩
    · obtain ⟨t, ht⟩ : ∃ t, t :: S ∈ Q.mem := by
        by_contra hne
        exact hc ⟨hf.mem, fun t ht => hne ⟨t, ht⟩⟩
      obtain ⟨u, hu⟩ := D.exists_freeStep E ⟨hf.mem, t, ht⟩
      obtain ⟨S', hs, hf', hc'⟩ := ih (hf.cons hu) (by rw [List.length_cons]; omega)
      exact ⟨S', (List.suffix_cons _ _).trans hs, hf', hc'⟩

/-- In a bounded program a p-guaranteed bug contains a complete schedule all
of whose steps are free. -/
theorem PGuarantees.exists_free_complete_mem {D : Directive L d} {E : Labelling Q L}
    {B : Set Sched} (hg : D.PGuarantees E B) {k : ℕ} (hk : Q.Bounded k) :
    ∃ S, D.Free E S ∧ Q.Complete S ∧ S ∈ B := by
  obtain ⟨S, -, hf, hc⟩ := (Free.nil : D.Free E []).exists_complete hk
  exact ⟨S, hf, hc, hg.mem_of_free_complete hf hc⟩

/-! ### Threads that are never parked, and the only enabled thread -/

/-- A step of a thread that is the thread of no target is free. -/
theorem freeStep_of_not_thr (D : Directive L d) (E : Labelling Q L) {S : Sched} {t : Tid}
    (h : t :: S ∈ Q.mem) (ht : ∀ i, E.thr (D.b i) ≠ t) : D.FreeStep E S t :=
  ⟨h, Or.inl fun ⟨i, hi⟩ => ht i hi.thr_eq⟩

/-- A schedule in which no thread of a target moves has free steps only. -/
theorem free_of_forall_not_thr (D : Directive L d) (E : Labelling Q L) {S : Sched}
    (h : S ∈ Q.mem) (hS : ∀ u ∈ S, ∀ i, E.thr (D.b i) ≠ u) : D.Free E S := by
  induction S with
  | nil => exact Free.nil
  | cons u S ih =>
    exact (ih (Q.tail_mem h) fun v hv => hS v (List.mem_cons_of_mem _ hv)).cons
      (D.freeStep_of_not_thr E h (hS u List.mem_cons_self))

/-- A step of the only enabled thread is free. -/
theorem freeStep_of_en_subset (D : Directive L d) (E : Labelling Q L) {S : Sched} {t : Tid}
    (h : t :: S ∈ Q.mem) (hen : ∀ u, u :: S ∈ Q.mem → u = t) : D.FreeStep E S t := by
  by_cases hp : D.Parked E S t
  · refine ⟨h, Or.inr ⟨fun u hu => hen u hu ▸ hp, fun i hi u j hj => ?_⟩⟩
    have hut := hen u hj.1
    subst hut
    exact (hi.index_eq hj).le
  · exact ⟨h, Or.inl hp⟩

/-- Steps of `t` while only `t` is enabled are free. -/
theorem Free.append_replicate {D : Directive L d} {E : Labelling Q L} {S₀ : Sched} {t : Tid}
    (hf : D.Free E S₀) {m : ℕ} (hm : List.replicate m t ++ S₀ ∈ Q.mem)
    (hen : ∀ j < m, ∀ u, u :: (List.replicate j t ++ S₀) ∈ Q.mem → u = t) :
    D.Free E (List.replicate m t ++ S₀) := by
  induction m with
  | zero => simpa using hf
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append] at hm ⊢
    exact (ih (Q.tail_mem hm) fun j hj => hen j (Nat.lt_succ_of_lt hj)).cons
      (D.freeStep_of_en_subset E hm (hen m (Nat.lt_succ_self m)))

/-- prop:lower-strict (1), the schedule part, for an arbitrary schedule set:
let every target belong to thread `t`, let `t` not occur in `S₀`, and let
only `t` be enabled while `t` takes `m` steps after `S₀`. Then all steps of
`S₀` followed by `m` steps of `t` are free. -/
theorem free_append_replicate (D : Directive L d) (E : Labelling Q L) {t : Tid}
    (ht : ∀ i, E.thr (D.b i) = t) {S₀ : Sched} (h0 : t ∉ S₀) {m : ℕ}
    (hm : List.replicate m t ++ S₀ ∈ Q.mem)
    (hen : ∀ j < m, ∀ u, u :: (List.replicate j t ++ S₀) ∈ Q.mem → u = t) :
    D.Free E (List.replicate m t ++ S₀) :=
  (D.free_of_forall_not_thr E (Q.suffix_mem hm (List.suffix_append _ _))
    fun u hu i hi => h0 (by rw [← ht i, hi]; exact hu)).append_replicate hm hen

end Directive

/-! ### prop:lower-strict (1), the schedule part -/

section HasLen

variable {Q : Prog} {L : Type} {d : ℕ} {len : Tid → ℕ}

/-- prop:lower-strict (1), the schedule part: let `Q` have thread lengths
and let every target of `D` belong to thread `t`. A complete schedule that
consists of a schedule `S₀` without steps of `t` followed by steps of `t`
only has free steps only. -/
theorem Prog.HasLen.free_of_thr_last (hQ : Q.HasLen len) (D : Directive L d)
    (E : Labelling Q L) {t : Tid} (ht : ∀ i, E.thr (D.b i) = t) {S₀ : Sched} (h0 : t ∉ S₀)
    {m : ℕ} (hc : Q.Complete (List.replicate m t ++ S₀)) :
    D.Free E (List.replicate m t ++ S₀) := by
  refine D.free_append_replicate E ht h0 hc.1 fun j hj u hu => ?_
  by_contra hut
  have hjm : List.replicate j t ++ S₀ <:+ List.replicate m t ++ S₀ := by
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hj.le
    rw [Nat.add_comm, List.replicate_add, List.append_assoc]
    exact List.suffix_append _ _
  have h1 := (hQ (Q.suffix_mem hc.1 hjm) u).mp hu
  have h2 := (hQ.complete_iff.mp hc).2 u
  have hz : ∀ c, List.count u (List.replicate c t) = 0 := fun c =>
    List.count_eq_zero.mpr fun hmem => hut (List.eq_of_mem_replicate hmem)
  rw [List.count_append, hz] at h1 h2
  omega

/-- prop:lower-strict (1), the schedule part: let `Q` have thread lengths,
let `D` p-guarantee `B`, and let every target of `D` belong to thread `t`.
Every complete schedule that runs the other threads first, in any
interleaving, and then `t` is in `B`. -/
theorem Prog.HasLen.mem_of_thr_last (hQ : Q.HasLen len) {D : Directive L d}
    {E : Labelling Q L} {B : Set Sched} (hg : D.PGuarantees E B) {t : Tid}
    (ht : ∀ i, E.thr (D.b i) = t) {S₀ : Sched} (h0 : t ∉ S₀) {m : ℕ}
    (hc : Q.Complete (List.replicate m t ++ S₀)) : List.replicate m t ++ S₀ ∈ B :=
  hg.mem_of_free_complete (hQ.free_of_thr_last D E ht h0 hc) hc

/-- prop:lower-strict (1), the schedule part, at depth 1: if a directive
with one target `b` p-guarantees `B`, every complete schedule that runs the
threads other than `thr b` first, in any interleaving, and then `thr b` is
in `B`. -/
theorem Prog.HasLen.mem_of_thr_last_one (hQ : Q.HasLen len) {D : Directive L 1}
    {E : Labelling Q L} {B : Set Sched} (hg : D.PGuarantees E B) {S₀ : Sched}
    (h0 : E.thr (D.b 0) ∉ S₀) {m : ℕ}
    (hc : Q.Complete (List.replicate m (E.thr (D.b 0)) ++ S₀)) :
    List.replicate m (E.thr (D.b 0)) ++ S₀ ∈ B :=
  hQ.mem_of_thr_last hg (fun i => by rw [Subsingleton.elim i 0]) h0 hc

end HasLen

end Pct
