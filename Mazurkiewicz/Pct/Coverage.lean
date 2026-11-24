import Mazurkiewicz.Pct.Directed
import Mathlib.Data.Set.Finite.Lemmas

/-!
# The coverage theorem for the prefix reading

`pctdpor`, `depth.tex`, thm:coverage, in its deterministic form: for every
initial order `ρ` that gives the thread of the first target the lowest
initial priority there are change points `ℓ j`, one for each target `D.b j`
with `1 ≤ j`, all between `1` and the bound on the length of schedules, such
that every run of RandS with these parameters that reaches a complete
schedule ends in the bug.

How the text is read here.

* `RandStep k` is one iteration of alg:rands with change points `k j`
  (`1 ≤ j`; the text's `k_j` gives the priority `d - j`). If several `j`
  have the same change point, the loop of the text leaves the priority of
  the largest such `j`; so does `RandStep`. `IsMaxEn` allows any enabled
  thread of maximal priority; in the runs considered the priorities are
  pairwise different.
* `Prog` contains the empty schedule (a non-empty prefix-closed set); the
  size `d ≥ 1` of a directive is the field `pos` of `Hyp`; a bug is any set
  of schedules, and only its schedules in `Q` matter.
* `DStep` is `DirStep` from a state that satisfies the invariant;
  `DStep.rightUnique` is the determinism of the directed run.
* `coupling` is the claim in the proof of thm:coverage that RandS with
  `k = ℓ` goes through the states of the directed run.
* `ell_ne_zero` is "at least once" of lem:lower-once.
* `coverage` also states that RandS with these parameters reaches a complete
  schedule. `hmax` follows from finitely many enabled threads
  (`exists_isMaxEn`).
* The probability `1/(n k^(d-1))` is not stated in this file. What remains:
  RandS as a function of a permutation of the `n` threads and of
  `k ∈ [K]^(d-1)`; an injective `ρ` on all identifiers from a permutation;
  the count of the `(n-1)!` permutations that put the thread of the first
  target last, each with the tuple `ℓ`.
-/

namespace Pct

open Function Relation

variable {Q : Prog} {L : Type} {d : ℕ}
variable {E : Labelling Q L} {D : Directive L d} {ρ : Tid → ℕ} {B : Set Sched}

/-- One iteration of alg:rands. -/
def RandStep (Q : Prog) (d : ℕ) (k : Fin d → ℕ) (x y : Sched × (Tid → ℕ)) : Prop :=
  ∃ t, IsMaxEn Q x.2 x.1 t ∧ y.1 = t :: x.1 ∧
    (((∀ j : Fin d, 1 ≤ j.val → k j ≠ x.1.length + 1) ∧ y.2 = x.2) ∨
     (∃ j : Fin d, 1 ≤ j.val ∧ k j = x.1.length + 1 ∧ y.2 = update x.2 t (d - j.val) ∧
        ∀ j' : Fin d, 1 ≤ j'.val → k j' = x.1.length + 1 → j'.val ≤ j.val))

/-- The states of RandS with initial order `ρ` and change points `k`. -/
def RandReach (Q : Prog) (d : ℕ) (ρ : Tid → ℕ) (k : Fin d → ℕ) : Sched × (Tid → ℕ) → Prop :=
  ReflTransGen (RandStep Q d k) ([], fun t => d + ρ t)

/-- An iteration of the directed run from a state that satisfies the invariant. -/
def DStep (E : Labelling Q L) (D : Directive L d) (ρ : Tid → ℕ) (x y : St d) : Prop :=
  Inv E D ρ x ∧ DirStep E D x y

/-- The states of the directed run. -/
def DirReach (E : Labelling Q L) (D : Directive L d) (ρ : Tid → ℕ) : St d → Prop :=
  ReflTransGen (DStep E D ρ) (St.init d ρ)

/-- The hypotheses of thm:coverage on the labelling, the directive and `ρ`. -/
structure Hyp (E : Labelling Q L) (D : Directive L d) (ρ : Tid → ℕ) (B : Set Sched) : Prop where
  strict : E.Strict
  inj : Injective ρ
  pos : 0 < d
  first : ρ (E.thr (D.b ⟨0, pos⟩)) = 0
  guar : D.PGuarantees E B

theorem DStep.inv (H : Hyp E D ρ B) {x y : St d} (h : DStep E D ρ x y) : Inv E D ρ y :=
  h.1.step H.strict H.inj H.pos H.first H.guar h.2

theorem DirReach.inv (H : Hyp E D ρ B) {x : St d} (h : DirReach E D ρ x) : Inv E D ρ x := by
  induction h with
  | refl => exact Inv.init
  | tail _ hbc _ => exact hbc.inv H

theorem DStep.rightUnique (hρ : Injective ρ) {x y y' : St d}
    (h : DStep E D ρ x y) (h' : DStep E D ρ x y') : y = y' := by
  obtain ⟨hx, t, ht, hS, hc⟩ := h
  obtain ⟨-, t', ht', hS', hc'⟩ := h'
  have htt : t = t' := hx.distinct hρ (le_antisymm (ht'.2 t ht.1) (ht.2 t' ht'.1))
  subst htt
  rcases hc with ⟨j, hj1, hnj, hp, hl⟩ | ⟨hno, hp, hl⟩ <;>
    rcases hc' with ⟨j', hj1', hnj', hp', hl'⟩ | ⟨hno', hp', hl'⟩
  · have hjj : j = j' := D.b_inj (Option.some.inj (hnj.symm.trans hnj'))
    subst hjj
    exact St.ext (hS.trans hS'.symm) (hp.trans hp'.symm) (hl.trans hl'.symm)
  · exact absurd hnj (hno' j hj1)
  · exact absurd hnj' (hno j' hj1')
  · exact St.ext (hS.trans hS'.symm) (hp.trans hp'.symm) (hl.trans hl'.symm)

theorem DStep.suffix {x y : St d} (h : DStep E D ρ x y) : x.S <:+ y.S := by
  obtain ⟨-, t, -, hS, -⟩ := h
  rw [hS]
  exact List.suffix_cons _ _

theorem dreach_suffix {x y : St d} (h : ReflTransGen (DStep E D ρ) x y) : x.S <:+ y.S := by
  induction h with
  | refl => exact List.suffix_refl _
  | tail _ hbc ih => exact ih.trans hbc.suffix

theorem dreach_ell {x y : St d} (h : ReflTransGen (DStep E D ρ) x y) {j : Fin d}
    (hj : x.ℓ j ≠ 0) : y.ℓ j = x.ℓ j := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => rw [← ih, hbc.1.ell_persist hbc.2 (ih ▸ hj)]

/-- Two states of the directed run: the one with a complete schedule is
reached from the other. -/
theorem dreach_to_complete (hρ : Injective ρ) {x z : St d} (hx : DirReach E D ρ x)
    (hz : DirReach E D ρ z) (hc : Q.Complete z.S) : ReflTransGen (DStep E D ρ) x z := by
  have hru : Relator.RightUnique (DStep E D ρ) := fun _ _ _ h h' => h.rightUnique hρ h'
  rcases ReflTransGen.total_of_right_unique hru hx hz with h | h
  · exact h
  · rcases ReflTransGen.cases_head h with rfl | ⟨w, hzw, -⟩
    · exact ReflTransGen.refl
    · obtain ⟨-, t, ht, -, -⟩ := hzw
      exact absurd ht.1 (hc.2 t)

/-- Backward stability over several steps of other threads. -/
theorem Labelling.Strict.backStability_append (hE : E.Strict) {S U : Sched} {t : Tid} {a : L}
    (h : U ++ S ∈ Q.mem) (hn : E.next (U ++ S) t = some a) (ht : t ∉ U) :
    E.next S t = some a := by
  induction U with
  | nil => simpa using hn
  | cons u U ih =>
    have hu : u ≠ t := fun e => ht (by simp [e])
    exact ih (Q.tail_mem h) (hE.backStability h hn hu) (fun m => ht (List.mem_cons_of_mem _ m))

/-- "At least once" of lem:lower-once. -/
theorem Inv.ell_ne_zero (hE : E.Strict) {x : St d} (hx : Inv E D ρ x) {j : Fin d}
    (hj1 : 1 ≤ j.val) (hb : D.b j ∈ E.names x.S) : x.ℓ j ≠ 0 := by
  intro h0
  obtain ⟨u, S', hs, he⟩ := hb
  have hQ : u :: S' ∈ Q.mem := Q.suffix_mem hx.q hs
  have hn : E.next S' u = some (D.b j) := (E.emitStep_iff hQ).mp he
  have hmem : u ∈ S' := hE.started (Q.tail_mem hQ) hn
  obtain ⟨U, S₀, rfl, hU⟩ := List.eq_append_cons_of_mem hmem
  have hn₀ : E.next (u :: S₀) u = some (D.b j) :=
    hE.backStability_append (Q.tail_mem hQ) hn hU
  have hs₀ : u :: S₀ <:+ x.S :=
    ((List.suffix_append U (u :: S₀)).trans (List.suffix_cons u _)).trans hs
  exact hx.unrecd j hj1 h0 u S₀ hs₀ hn₀

/-- Two suffixes of a list that have the same length are equal. -/
theorem suffix_eq_of_length {α : Type} {l₁ l₂ l : List α} (h₁ : l₁ <:+ l) (h₂ : l₂ <:+ l)
    (hlen : l₁.length = l₂.length) : l₁ = l₂ := by
  rcases List.suffix_or_suffix_of_suffix h₁ h₂ with h | h
  · exact h.eq_of_length hlen
  · exact (h.eq_of_length hlen.symm).symm

/-- A lowering of the directed run at a step is recorded in the change
points of the complete run, and conversely. -/
theorem lower_iff (H : Hyp E D ρ B) {z : St d} (hz : DirReach E D ρ z) (hc : Q.Complete z.S)
    {x y : St d} (hx : DirReach E D ρ x) (hxy : DStep E D ρ x y) {t : Tid}
    (ht : IsMaxEn Q x.p x.S t) (j : Fin d) (hj1 : 1 ≤ j.val) :
    z.ℓ j = x.S.length + 1 ↔ E.next (t :: x.S) t = some (D.b j) := by
  have hxinv := hx.inv H
  have hy : DirReach E D ρ y := ReflTransGen.tail hx hxy
  have hyz := dreach_to_complete H.inj hy hz hc
  obtain ⟨-, t', ht', hyS, hc'⟩ := hxy
  have htt : t' = t := hxinv.distinct H.inj (le_antisymm (ht.2 t' ht'.1) (ht'.2 t ht.1))
  subst htt
  constructor
  · intro hl
    have hne : z.ℓ j ≠ 0 := by omega
    obtain ⟨u, S₀, hsuf, hlen, hn⟩ := (hz.inv H).recd j hne
    have hsuf' : t' :: x.S <:+ z.S := hyS ▸ dreach_suffix hyz
    have heq : u :: S₀ = t' :: x.S :=
      suffix_eq_of_length hsuf hsuf' (by simp only [List.length_cons]; omega)
    obtain ⟨rfl, rfl⟩ := List.cons.inj heq
    exact hn
  · intro hn
    rcases hc' with ⟨j₀, -, hnj, -, hl⟩ | ⟨hno, -, -⟩
    · have hjj : j₀ = j := D.b_inj (Option.some.inj (hnj.symm.trans hn))
      subst hjj
      have : y.ℓ j₀ = x.S.length + 1 := by rw [hl, update_self]
      rw [← this]
      exact dreach_ell hyz (by omega)
    · exact absurd hn (hno j hj1)

/-- The states of the directed run are states of RandS with the change
points of the complete run. -/
theorem coupling_conv (H : Hyp E D ρ B) {z : St d} (hz : DirReach E D ρ z)
    (hc : Q.Complete z.S) {x : St d} (hx : DirReach E D ρ x) :
    RandReach Q d ρ z.ℓ (x.S, x.p) := by
  induction hx with
  | refl => exact ReflTransGen.refl
  | tail hx hxy ih =>
    rename_i x y
    refine ReflTransGen.tail ih ?_
    obtain ⟨hxinv, t, ht, hyS, hcase⟩ := id hxy
    have key := fun j hj1 => lower_iff H hz hc hx hxy ht j hj1
    refine ⟨t, ht, hyS, ?_⟩
    rcases hcase with ⟨j₀, hj1, hnj, hp, -⟩ | ⟨hno, hp, -⟩
    · refine Or.inr ⟨j₀, hj1, (key j₀ hj1).mpr hnj, hp, fun j' hj1' hk => ?_⟩
      have := (key j' hj1').mp hk
      rw [D.b_inj (Option.some.inj (this.symm.trans hnj))]
    · exact Or.inl ⟨fun j hj1 hk => hno j hj1 ((key j hj1).mp hk), hp⟩

/-- RandS with the change points of the directed run goes through the states
of the directed run. -/
theorem coupling (H : Hyp E D ρ B) {z : St d} (hz : DirReach E D ρ z) (hc : Q.Complete z.S)
    {s : Sched × (Tid → ℕ)} (hs : RandReach Q d ρ z.ℓ s) :
    ∃ x, DirReach E D ρ x ∧ x.S = s.1 ∧ x.p = s.2 := by
  induction hs with
  | refl => exact ⟨St.init d ρ, ReflTransGen.refl, rfl, rfl⟩
  | tail _ hstep ih =>
    rename_i s s'
    obtain ⟨x, hx, hxS, hxp⟩ := ih
    obtain ⟨t, ht, hS', hcase⟩ := hstep
    have hxinv := hx.inv H
    rw [← hxS, ← hxp] at ht
    rw [← hxS] at hS' hcase
    rw [← hxp] at hcase
    have key : ∀ (y : St d), DStep E D ρ x y → ∀ j : Fin d, 1 ≤ j.val →
        (z.ℓ j = x.S.length + 1 ↔ E.next (t :: x.S) t = some (D.b j)) :=
      fun y hxy j hj1 => lower_iff H hz hc hx hxy ht j hj1
    by_cases hex : ∃ j : Fin d, 1 ≤ j.val ∧ E.next (t :: x.S) t = some (D.b j)
    · obtain ⟨j₀, hj1, hnj⟩ := hex
      let y : St d := ⟨t :: x.S, update x.p t (d - j₀.val), update x.ℓ j₀ (x.S.length + 1)⟩
      have hxy : DStep E D ρ x y := ⟨hxinv, t, ht, rfl, Or.inl ⟨j₀, hj1, hnj, rfl, rfl⟩⟩
      refine ⟨y, ReflTransGen.tail hx hxy, hS'.symm, ?_⟩
      rcases hcase with ⟨hno, -⟩ | ⟨j, hj1', hk, hp, -⟩
      · exact absurd ((key y hxy j₀ hj1).mpr hnj) (hno j₀ hj1)
      · have hn := (key y hxy j hj1').mp hk
        have hjj : j = j₀ := D.b_inj (Option.some.inj (hn.symm.trans hnj))
        rw [hp, hjj]
    · let y : St d := ⟨t :: x.S, x.p, x.ℓ⟩
      have hno : ∀ j : Fin d, 1 ≤ j.val → E.next (t :: x.S) t ≠ some (D.b j) :=
        fun j hj1 hn => hex ⟨j, hj1, hn⟩
      have hxy : DStep E D ρ x y := ⟨hxinv, t, ht, rfl, Or.inr ⟨hno, rfl, rfl⟩⟩
      refine ⟨y, ReflTransGen.tail hx hxy, hS'.symm, ?_⟩
      rcases hcase with ⟨-, hp⟩ | ⟨j, hj1', hk, -, -⟩
      · exact hp.symm
      · exact absurd ((key y hxy j hj1').mp hk) (hno j hj1')

/-- With finitely many enabled threads there is one of maximal priority. -/
theorem exists_isMaxEn (p : Tid → ℕ) {S : Sched} (hfin : (Q.en S).Finite)
    (hen : ∃ t, t :: S ∈ Q.mem) : ∃ t, IsMaxEn Q p S t := by
  obtain ⟨t, ht, hmax⟩ := Set.exists_max_image (Q.en S) p hfin hen
  exact ⟨t, ht, fun u hu => hmax u hu⟩

/-- The directed run reaches a complete schedule. -/
theorem exists_complete {K : ℕ} (hK : Q.Bounded K)
    (hmax : ∀ (p : Tid → ℕ) (S : Sched), (∃ t, t :: S ∈ Q.mem) → ∃ t, IsMaxEn Q p S t)
    (H : Hyp E D ρ B) : ∀ (n : ℕ) (x : St d), DirReach E D ρ x → K - x.S.length ≤ n →
    ∃ z, DirReach E D ρ z ∧ Q.Complete z.S := by
  intro n
  induction n with
  | zero =>
    intro x hx hlen
    refine ⟨x, hx, (hx.inv H).q, fun t ht => ?_⟩
    have := hK _ ht
    simp only [List.length_cons] at this
    omega
  | succ n ih =>
    intro x hx hlen
    by_cases hen : ∃ t, t :: x.S ∈ Q.mem
    · obtain ⟨t, ht⟩ := hmax x.p x.S hen
      have hxinv := hx.inv H
      have hstep : ∃ y, DirStep E D x y ∧ y.S = t :: x.S := by
        by_cases hex : ∃ j : Fin d, 1 ≤ j.val ∧ E.next (t :: x.S) t = some (D.b j)
        · obtain ⟨j₀, hj1, hnj⟩ := hex
          exact ⟨⟨t :: x.S, update x.p t (d - j₀.val), update x.ℓ j₀ (x.S.length + 1)⟩,
            ⟨t, ht, rfl, Or.inl ⟨j₀, hj1, hnj, rfl, rfl⟩⟩, rfl⟩
        · exact ⟨⟨t :: x.S, x.p, x.ℓ⟩,
            ⟨t, ht, rfl, Or.inr ⟨fun j hj1 hn => hex ⟨j, hj1, hn⟩, rfl, rfl⟩⟩, rfl⟩
      obtain ⟨y, hxy, hyS⟩ := hstep
      refine ih y (ReflTransGen.tail hx ⟨hxinv, hxy⟩) ?_
      rw [hyS]
      simp only [List.length_cons]
      omega
    · exact ⟨x, hx, (hx.inv H).q, fun t ht => hen ⟨t, ht⟩⟩

/-- thm:coverage, deterministic form. `K` bounds the length of the schedules;
`hmax` holds when the program has finitely many threads. -/
theorem coverage {K : ℕ} (hK : Q.Bounded K)
    (hmax : ∀ (p : Tid → ℕ) (S : Sched), (∃ t, t :: S ∈ Q.mem) → ∃ t, IsMaxEn Q p S t)
    (H : Hyp E D ρ B) :
    ∃ ℓ : Fin d → ℕ, (∀ j : Fin d, 1 ≤ j.val → 1 ≤ ℓ j ∧ ℓ j ≤ K) ∧
      (∀ j j' : Fin d, 1 ≤ j.val → 1 ≤ j'.val → ℓ j = ℓ j' → j = j') ∧
      (∃ s, RandReach Q d ρ ℓ s ∧ Q.Complete s.1) ∧
      ∀ s, RandReach Q d ρ ℓ s → Q.Complete s.1 → s.1 ∈ B := by
  obtain ⟨z, hz, hc⟩ := exists_complete hK hmax H (K - (St.init d ρ).S.length) (St.init d ρ)
    ReflTransGen.refl le_rfl
  have hzinv := hz.inv H
  have hsat := (H.guar.cond2 z.S hc hzinv.nv).1
  have hrec : ∀ j : Fin d, 1 ≤ j.val → ∃ u S₀, u :: S₀ <:+ z.S ∧ z.ℓ j = S₀.length + 1 ∧
      E.next (u :: S₀) u = some (D.b j) :=
    fun j hj1 => hzinv.recd j (hzinv.ell_ne_zero H.strict hj1 (hsat.2 j))
  refine ⟨z.ℓ, ?_, ?_, ⟨(z.S, z.p), coupling_conv H hz hc hz, hc⟩, ?_⟩
  · intro j hj1
    obtain ⟨u, S₀, hsuf, hlen, -⟩ := hrec j hj1
    have h1 := hsuf.length_le
    have h2 := hK _ hzinv.q
    simp only [List.length_cons] at h1
    omega
  · intro j j' hj1 hj1' hl
    obtain ⟨u, S₀, hsuf, hlen, hn⟩ := hrec j hj1
    obtain ⟨u', S₀', hsuf', hlen', hn'⟩ := hrec j' hj1'
    have heq : u :: S₀ = u' :: S₀' :=
      suffix_eq_of_length hsuf hsuf' (by simp only [List.length_cons]; omega)
    obtain ⟨rfl, rfl⟩ := List.cons.inj heq
    exact D.b_inj (Option.some.inj (hn.symm.trans hn'))
  · intro s hs hcs
    obtain ⟨x, hx, hxS, -⟩ := coupling H hz hc hs
    have hxinv := hx.inv H
    rw [← hxS] at hcs ⊢
    exact (H.guar.cond2 x.S hcs hxinv.nv).2

end Pct
