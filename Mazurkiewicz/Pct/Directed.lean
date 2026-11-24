import Mazurkiewicz.Pct.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relation
import Mathlib.Order.Basic
import Mathlib.Data.Fin.Basic

/-!
# The directed run and its invariant

`pctdpor`, `depth.tex`, sec:coverage: alg:dirs and lem:prio-of-target,
lem:low-prio, lem:no-violation, the first half of lem:lower-once.

How the text is read here.

* Targets are `D.b j` for `j : Fin d`, counted from `0`: the text's `b_{j+1}`.
  Lowering number `j` of the text gives the priority `d - j` to the thread
  whose next name is `D.b j`, for `1 ≤ j`.
* `ρ : Tid → ℕ` is injective and the initial priority of `t` is `d + ρ t`;
  the text's permutation is `ρ + 1`. The hypothesis of the proof of
  thm:coverage is `ρ (thr (b 0)) = 0`.
* A state of the run is `St`: the schedule, the priorities, and for every
  `j` the length `ℓ j` of the schedule at which lowering number `j` was
  executed, `0` if it has not been executed. `DirStep` is one iteration of
  alg:dirs. The guard `p[t] ≠ d - i` of line 8 is left out: without it the
  assignment writes the value that is already there.
* `Inv` is the invariant of the run; its fields are the statements of the
  lemmas: `nv` is lem:no-violation, `tg` is lem:prio-of-target, `lo` is
  lem:low-prio, `distinct` is the remark that different threads have
  different priorities, `ell_persist` is "at most once" of lem:lower-once.
-/

namespace Pct

open Function

variable {Q : Prog} {L : Type} {d : ℕ}

/-- `t` is an enabled thread of maximal priority. -/
def IsMaxEn (Q : Prog) (p : Tid → ℕ) (S : Sched) (t : Tid) : Prop :=
  t :: S ∈ Q.mem ∧ ∀ u, u :: S ∈ Q.mem → p u ≤ p t

/-- A state of the directed run. -/
@[ext] structure St (d : ℕ) where
  S : Sched
  p : Tid → ℕ
  ℓ : Fin d → ℕ

/-- The initial state for the initial order `ρ`. -/
def St.init (d : ℕ) (ρ : Tid → ℕ) : St d := ⟨[], fun t => d + ρ t, fun _ => 0⟩

/-- One iteration of alg:dirs. -/
def DirStep (E : Labelling Q L) (D : Directive L d) (x y : St d) : Prop :=
  ∃ t, IsMaxEn Q x.p x.S t ∧ y.S = t :: x.S ∧
    ((∃ j : Fin d, 1 ≤ j.val ∧ E.next (t :: x.S) t = some (D.b j) ∧
        y.p = update x.p t (d - j.val) ∧ y.ℓ = update x.ℓ j (x.S.length + 1)) ∨
     ((∀ j : Fin d, 1 ≤ j.val → E.next (t :: x.S) t ≠ some (D.b j)) ∧ y.p = x.p ∧ y.ℓ = x.ℓ))

/-- The invariant of the directed run. -/
structure Inv (E : Labelling Q L) (D : Directive L d) (ρ : Tid → ℕ) (x : St d) : Prop where
  q : x.S ∈ Q.mem
  nv : ¬ D.PViolates E x.S
  hi : ∀ t, d ≤ x.p t → x.p t = d + ρ t
  lo : ∀ t, x.p t < d → ∃ j : Fin d, 1 ≤ j.val ∧ x.p t = d - j.val ∧ E.thr (D.b j) = t ∧
    (D.b j ∈ E.names x.S ∨ E.next x.S t = some (D.b j))
  tg : ∀ t j, E.next x.S t = some (D.b j) → x.p t = d - j.val
  recd : ∀ j, x.ℓ j ≠ 0 → ∃ u S₀, u :: S₀ <:+ x.S ∧ x.ℓ j = S₀.length + 1 ∧
    E.next (u :: S₀) u = some (D.b j)
  unrecd : ∀ j : Fin d, 1 ≤ j.val → x.ℓ j = 0 → ∀ u S₀, u :: S₀ <:+ x.S →
    E.next (u :: S₀) u ≠ some (D.b j)

variable {E : Labelling Q L} {D : Directive L d} {ρ : Tid → ℕ} {B : Set Sched}

/-- Different threads have different priorities. -/
theorem Inv.distinct {x : St d} (hx : Inv E D ρ x) (hρ : Injective ρ) {u u' : Tid}
    (h : x.p u = x.p u') : u = u' := by
  by_cases hu : d ≤ x.p u
  · have h1 := hx.hi u hu
    have h2 := hx.hi u' (h ▸ hu)
    exact hρ (by omega)
  · have hu' : x.p u' < d := by omega
    obtain ⟨j, hj1, hpj, hthr, -⟩ := hx.lo u (by omega)
    obtain ⟨j', hj1', hpj', hthr', -⟩ := hx.lo u' hu'
    have hjj : j = j' := Fin.ext (by have := j.isLt; have := j'.isLt; omega)
    rw [← hthr, ← hthr', hjj]

theorem Inv.init : Inv E D ρ (St.init d ρ) where
  q := Q.nil_mem
  nv := D.not_pviolates_nil E
  hi := fun _ _ => rfl
  lo := fun t h => by
    have h' : d + ρ t < d := h
    omega
  tg := fun t j h => by simp [St.init, E.notFirst] at h
  recd := fun j h => by simp [St.init] at h
  unrecd := fun j _ _ u S₀ hs => by simp [St.init] at hs

/-- The step of the thread of maximal priority creates no violation
(lem:no-violation). -/
theorem Inv.not_violates_step {x : St d} (hx : Inv E D ρ x) (hρ : Injective ρ)
    (hg : D.PGuarantees E B) {t : Tid} (ht : IsMaxEn Q x.p x.S t) :
    ¬ D.Violates E (t :: x.S) := by
  obtain ⟨htQ, hmax⟩ := ht
  intro hv
  have hSnv : ¬ D.Violates E x.S := fun h => hx.nv ⟨_, List.suffix_refl _, h⟩
  obtain ⟨i, hi⟩ := D.next_target_of_violates E htQ hSnv hv
  have hbi : D.b i ∉ E.names x.S := E.next_not_mem_names hx.q hi
  have hpt : x.p t = d - i.val := hx.tg t i hi
  obtain ⟨t', ht'Q, ht'nv⟩ := hg.cond1 x.S ⟨hx.q, t, htQ⟩ hx.nv
  have hne : t' ≠ t := by
    rintro rfl
    exact ht'nv ((D.pviolates_cons E).mpr (Or.inr hv))
  have hlt : x.p t' < x.p t :=
    lt_of_le_of_ne (hmax t' ht'Q) (fun e => hne (hx.distinct hρ e))
  obtain ⟨j, hj1, hpj, -, hor⟩ := hx.lo t' (by omega)
  have hij : i < j := by
    have := i.isLt; have := j.isLt
    exact Fin.lt_def.mpr (by omega)
  rcases hor with hin | hnx
  · exact hSnv (Or.inr ⟨i, j, hij, hin, hbi⟩)
  · apply ht'nv
    rw [D.pviolates_cons E]
    refine Or.inr (Or.inr ⟨i, j, hij, ?_, ?_⟩)
    · rw [E.names_cons ht'Q]
      exact Or.inr hnx
    · rw [E.names_cons ht'Q]
      rintro (h | h)
      · exact hbi h
      · have h' : E.next x.S t' = some (D.b i) := h
        rw [hnx] at h'
        exact absurd (D.b_inj (Option.some.inj h')) (Fin.ne_of_gt hij)

/-- The invariant is preserved by an iteration. -/
theorem Inv.step {x y : St d} (hx : Inv E D ρ x) (hE : E.Strict) (hρ : Injective ρ)
    (hd : 0 < d) (h0 : ρ (E.thr (D.b ⟨0, hd⟩)) = 0)
    (hg : D.PGuarantees E B) (hxy : DirStep E D x y) : Inv E D ρ y := by
  obtain ⟨t, ht, hS, hcase⟩ := hxy
  have htQ : t :: x.S ∈ Q.mem := ht.1
  have hnv' : ¬ D.Violates E (t :: x.S) := hx.not_violates_step hρ hg ht
  have hmono : E.names x.S ⊆ E.names (t :: x.S) := E.names_mono (List.suffix_cons _ _)
  have hemit : ∀ a, E.next x.S t = some a → a ∈ E.names (t :: x.S) := by
    intro a ha
    rw [E.names_cons htQ]
    exact Or.inr ha
  -- the priorities of the other threads are unchanged
  have hP1 : ∀ u, u ≠ t → y.p u = x.p u := by
    intro u hu
    rcases hcase with ⟨j, -, -, hp, -⟩ | ⟨-, hp, -⟩
    · rw [hp, update_of_ne hu]
    · rw [hp]
  refine ⟨hS ▸ htQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- nv
    rw [hS, D.pviolates_cons E]
    rintro (h | h)
    · exact hx.nv h
    · exact hnv' h
  · -- hi
    intro u hu
    by_cases hut : u = t
    · subst hut
      rcases hcase with ⟨j, hj1, -, hp, -⟩ | ⟨-, hp, -⟩
      · rw [hp, update_self] at hu
        omega
      · rw [hp] at hu ⊢
        exact hx.hi u hu
    · rw [hP1 u hut] at hu ⊢
      exact hx.hi u hu
  · -- lo
    intro u hu
    rw [hS]
    by_cases hut : u = t
    · subst hut
      rcases hcase with ⟨j, hj1, hnj, hp, -⟩ | ⟨-, hp, -⟩
      · exact ⟨j, hj1, by rw [hp, update_self], E.affinity htQ hnj, Or.inr hnj⟩
      · rw [hp] at hu ⊢
        obtain ⟨j, hj1, hpj, hthr, hor⟩ := hx.lo u hu
        refine ⟨j, hj1, hpj, hthr, Or.inl ?_⟩
        rcases hor with h | h
        · exact hmono h
        · exact hemit _ h
    · rw [hP1 u hut] at hu ⊢
      obtain ⟨j, hj1, hpj, hthr, hor⟩ := hx.lo u hu
      refine ⟨j, hj1, hpj, hthr, ?_⟩
      rcases hor with h | h
      · exact Or.inl (hmono h)
      · exact Or.inr (E.stability htQ h (Ne.symm hut))
  · -- tg
    intro u j hn
    rw [hS] at hn
    by_cases hut : u = t
    · subst hut
      rcases hcase with ⟨j₀, hj1, hnj, hp, -⟩ | ⟨hno, hp, -⟩
      · rw [hnj] at hn
        rw [hp, update_self, D.b_inj (Option.some.inj hn)]
      · have hj0 : j.val = 0 := by
          by_contra hne
          exact hno j (by omega) hn
        have hjeq : j = ⟨0, hd⟩ := Fin.ext hj0
        rw [hp, hj0]
        have hthr : E.thr (D.b j) = u := E.affinity htQ hn
        by_cases hge : d ≤ x.p u
        · have := hx.hi u hge
          rw [← hthr, hjeq, h0] at this
          rw [← hthr, hjeq]
          omega
        · exfalso
          obtain ⟨j', hj1', -, -, hor⟩ := hx.lo u (by omega)
          have hin : D.b j' ∈ E.names (u :: x.S) := by
            rcases hor with h | h
            · exact hmono h
            · exact hemit _ h
          have hout : D.b j ∉ E.names (u :: x.S) := E.next_not_mem_names htQ hn
          exact hnv' (Or.inr ⟨j, j', Fin.lt_def.mpr (by omega), hin, hout⟩)
    · have := hx.tg u j (hE.backStability htQ hn (Ne.symm hut))
      rw [hP1 u hut, this]
  · -- rec
    intro j hj
    rw [hS]
    rcases hcase with ⟨j₀, -, hnj, -, hl⟩ | ⟨-, -, hl⟩
    · by_cases hjj : j = j₀
      · subst hjj
        exact ⟨t, x.S, List.suffix_refl _, by rw [hl, update_self], hnj⟩
      · rw [hl, update_of_ne hjj] at hj ⊢
        obtain ⟨u, S₀, hs, hlen, hn⟩ := hx.recd j hj
        exact ⟨u, S₀, hs.trans (List.suffix_cons _ _), hlen, hn⟩
    · rw [hl] at hj ⊢
      obtain ⟨u, S₀, hs, hlen, hn⟩ := hx.recd j hj
      exact ⟨u, S₀, hs.trans (List.suffix_cons _ _), hlen, hn⟩
  · -- unrec
    intro j hj1 hj0 u S₀ hs
    rw [hS] at hs
    rcases List.suffix_cons_iff.mp hs with heq | hs'
    · obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      rcases hcase with ⟨j₀, -, hnj, -, hl⟩ | ⟨hno, -, -⟩
      · intro hn
        rw [hnj] at hn
        have hjj : j₀ = j := D.b_inj (Option.some.inj hn)
        rw [hl, ← hjj, update_self] at hj0
        omega
      · exact hno j hj1
    · have hxl : x.ℓ j = 0 := by
        rcases hcase with ⟨j₀, -, -, -, hl⟩ | ⟨-, -, hl⟩
        · by_cases hjj : j = j₀
          · rw [hl, hjj, update_self] at hj0
            omega
          · rwa [hl, update_of_ne hjj] at hj0
        · rwa [hl] at hj0
      exact hx.unrecd j hj1 hxl u S₀ hs'

/-- "At most once" of lem:lower-once: a recorded length is not overwritten. -/
theorem Inv.ell_persist {x y : St d} (hx : Inv E D ρ x) (hxy : DirStep E D x y)
    {j : Fin d} (hj : x.ℓ j ≠ 0) : y.ℓ j = x.ℓ j := by
  obtain ⟨t, ht, hS, hcase⟩ := hxy
  rcases hcase with ⟨j₀, -, hnj, -, hl⟩ | ⟨-, -, hl⟩
  · by_cases hjj : j = j₀
    · exfalso
      subst hjj
      obtain ⟨u, S₀, ⟨U, hU⟩, -, hn⟩ := hx.recd j hj
      have hQ₀ : u :: S₀ ∈ Q.mem := Q.suffix_mem hx.q ⟨U, hU⟩
      have hut : u = t := by
        rw [← E.affinity hQ₀ hn, E.affinity ht.1 hnj]
      subst hut
      have hmem : (u :: U) ++ (u :: S₀) ∈ Q.mem := by
        have := ht.1
        rw [← hU] at this
        simpa using this
      have hn' : E.next ((u :: U) ++ (u :: S₀)) u = some (D.b j) := by
        have := hnj
        rw [← hU] at this
        simpa using this
      exact E.uniqueness hmem hn hn' (by simp)
    · rw [hl, update_of_ne hjj]
  · rw [hl]

end Pct
