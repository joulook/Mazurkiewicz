import Mazurkiewicz.Condpor.A22
import Mazurkiewicz.Lib.Path

/-!
# Termination: Lemma A.21 and Theorem A.27

Paper: Appendix A, Def. A.4, A.5, Lemma A.21 and Theorem A.27. Coq:
`trust/Terminate.v` (`TruSt_RW_prop`, `TruSt_RW_l`, `TruSt_wf`).

* `StepRW`, `ReachRW`: the transition of Def. A.4 on configurations with the
  set `RW` of the writes that were added by a revisit step.
* `Config.IsR c w`: `w` has a read that reads from it and was added before it
  (`[w]; (G.rf ∩ >) ≠ ∅`). Def. A.5: `R(G, <, RW)` is the set of the `w ∈ RW`
  with `IsR`, and `NR(G, <, RW)` the rest of `RW`.
* `ReachRW.a21`: Lemma A.21. (D1) `RW ⊆ G.E`; (D2) every write of `NR` is
  causally before a write of `R`.
* `terminates`: Theorem A.27 in the paper's form: for a bounded program there
  is a bound on the length of the runs of the algorithm. `step_wellFounded`:
  the form used to define the explorer.

A remark on the paper's proof of Lemma A.21, step ⟨4⟩3 of the revisit case:
it states `NR(G', <', RW') = NR(G, <, RW)`. This is not so in general: a write
of `R` whose only backward reader is deleted, or is revisited again, is in
`NR` afterwards. The lemma holds nevertheless: by line 27 of Algorithm 1 such
a write is causally before the new write, which is in `R` of the new
configuration. The proof here uses this.

Example: thread 0 is `R x`; thread 1 is `W x 1; W x 2`. `W x 1` revisits `R x`,
then `W x 2` revisits it again. After the second revisit `W x 1` has no
backward reader: it has moved from `R` to `NR`, and it is `po`-before
`W x 2`, which is in `R`.
-/

namespace Condpor

variable {P : Program} {M : Model} {S : Solver} {τ : TieBreak S}

/-- `[w]; (G.rf ∩ >) ≠ ∅`: some read that was added before `w` reads from `w`. -/
def Config.IsR (c : Config) (w : TEv) : Prop := ∃ q, c.Bw w q

/-- The set `RW` after a step (Def. A.4): the added event joins it in a
revisit step. -/
def Kind.rw (e : TEv) (rw : Finset TEv) : Kind → Finset TEv
  | .nr => rw
  | .rv _ => insert e rw

/-- A step on configurations with the set `RW` (Def. A.4). -/
def StepRW (P : Program) (M : Model) {S : Solver} (τ : TieBreak S)
    (x y : Config × Finset TEv) : Prop :=
  ∃ e k, StepL P M τ x.1 e k y.1 ∧ y.2 = k.rw e x.2

/-- The configurations with `RW` reached from `⟨∅, ∅, ∅⟩`. -/
def ReachRW (P : Program) (M : Model) {S : Solver} (τ : TieBreak S)
    (x : Config × Finset TEv) : Prop :=
  Relation.ReflTransGen (StepRW P M τ) (Config.init P.mem, ∅) x

/-- The projection of a reached configuration with `RW` is reached. -/
theorem ReachRW.reach {x : Config × Finset TEv} (h : ReachRW P M τ x) : Reach P M τ x.1 := by
  unfold ReachRW at h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨e, k, hs, -⟩ := hs
    exact ih.tail ⟨e, k, hs⟩

/-- Every reached configuration is the projection of one with `RW`. -/
theorem Reach.exists_rw {c : Config} (h : Reach P M τ c) : ∃ rw, ReachRW P M τ (c, rw) := by
  unfold Reach at h
  induction h with
  | refl => exact ⟨∅, Relation.ReflTransGen.refl⟩
  | tail _ hs ih =>
    obtain ⟨rw, hrw⟩ := ih
    obtain ⟨e, k, hs⟩ := hs
    exact ⟨k.rw e rw, hrw.tail ⟨e, k, hs, rfl⟩⟩

/-- Lemma A.21 for a pair. -/
theorem ReachRW.a21_aux {x : Config × Finset TEv} (h : ReachRW P M τ x) :
    (∀ w ∈ x.2, w ∈ x.1.order) ∧
    (∀ w ∈ x.2, ¬ x.1.IsR w → ∃ w' ∈ x.2, x.1.IsR w' ∧ x.1.abs.porf (.th w) (.th w')) := by
  have hreach := h
  unfold ReachRW at h
  induction h with
  | refl => exact ⟨fun w hw => absurd hw (by simp), fun w hw => absurd hw (by simp)⟩
  | @tail b y hb hs ih =>
    obtain ⟨hD1, hD2⟩ := ih hb
    have hbR : Reach P M τ b.1 := ReachRW.reach hb
    obtain ⟨hw, hpo, -, -⟩ := hbR.sound
    obtain ⟨c, rw⟩ := b
    obtain ⟨c', rw'⟩ := y
    obtain ⟨e, k, hs, hrw⟩ := hs
    simp only at hs hrw hD1 hD2 hw hpo ⊢
    subst hrw
    cases k with
    | nr =>
      have N := hs.nrFacts hw
      refine ⟨fun w hw' => ?_, fun w hw' hnr => ?_⟩
      · rw [N.order]
        exact List.mem_cons_of_mem _ (hD1 w hw')
      · have hnr' : ¬ c.IsR w := fun ⟨q, hq⟩ => hnr ⟨q, (N.bw_iff hw).mpr hq⟩
        obtain ⟨w', hw'm, ⟨q', hq'⟩, hpf⟩ := hD2 w hw' hnr'
        exact ⟨w', hw'm, ⟨q', (N.bw_iff hw).mpr hq'⟩, N.porf_mono hpf⟩
    | rv r =>
      obtain ⟨wp, rfl, H⟩ := hs.rvHyp hw hpo
      -- a write of `R` is not deleted (D1 of Lemma A.20)
      have hRnd : ∀ s q, c.Bw s q → ¬ c.Deleted r e s := fun s q hbw hd =>
        A20_D1 H.hc H.hmax hd hbw
      have hRne : ∀ s q, c.Bw s q → s ≠ r := fun s q hbw h' =>
        A20_D3 H.hc H.hpo H.hr H.hnp H.hmax (x := r) (Or.inr rfl) (Or.inl h'.symm) hbw
      -- the writes of `RW` are kept
      have hkept : ∀ w ∈ rw, w ∈ c.keep r e := by
        intro w hw'
        rw [Config.mem_keep_iff]
        refine ⟨hD1 w hw', fun hd => ?_⟩
        by_cases hR : c.IsR w
        · obtain ⟨q, hq⟩ := hR
          exact hRnd w q hq hd
        · obtain ⟨w', hw'm, ⟨q', hq'⟩, hpf⟩ := hD2 w hw' hR
          exact A20_D2 H.hc H.hpo H.hr H.hnp H.hmax (Or.inl hd) (hD1 w' hw'm)
            (hRnd w' q' hq') hpf
      have heR : (c.revisit r e wp).IsR e := ⟨r, H.bw_iff.mpr (Or.inl ⟨rfl, rfl⟩)⟩
      -- a write of `R` stays in `R`, or becomes causally before the new write
      have lift : ∀ s q, c.Bw s q →
          (c.revisit r e wp).IsR s ∨ (c.revisit r e wp).abs.porf (.th s) (.th e) := by
        intro s q hbw
        by_cases hq : c.Deleted r e q ∨ q = r
        · exact Or.inr (H.porf_w_iff.mp (Config.porf_of_max_bw H.hc (H.hmax q hq) hbw))
        · have hqk : q ∈ c.keep r e :=
            (Config.mem_keep_iff c r e q).mpr ⟨hbw.2.2.1, fun hd => hq (Or.inl hd)⟩
          exact Or.inl ⟨q, H.bw_iff.mpr (Or.inr ⟨hbw, hqk, fun h' => hq (Or.inr h')⟩)⟩
      refine ⟨fun w hw' => ?_, fun w hw' hnr => ?_⟩
      · rcases Finset.mem_insert.mp hw' with hwe | hwm
        · exact H.mem_order'.mpr (Or.inl hwe)
        · exact H.mem_order'.mpr (Or.inr (hkept w hwm))
      · rcases Finset.mem_insert.mp hw' with hwe | hwm
        · exact absurd (hwe ▸ heR) hnr
        · by_cases hR : c.IsR w
          · obtain ⟨q, hq⟩ := hR
            rcases lift w q hq with h1 | h1
            · exact absurd h1 hnr
            · exact ⟨e, Finset.mem_insert_self _ _, heR, h1⟩
          · obtain ⟨w', hw'm, ⟨q', hq'⟩, hpf⟩ := hD2 w hwm hR
            have hpf' : (c.revisit r e wp).abs.porf (.th w) (.th w') :=
              H.porf_kept (hD1 w' hw'm) (hRnd w' q' hq') (hRne w' q' hq') hpf
            rcases lift w' q' hq' with h1 | h1
            · exact ⟨w', Finset.mem_insert_of_mem hw'm, h1, hpf'⟩
            · exact ⟨e, Finset.mem_insert_self _ _, heR, Relation.TransGen.trans hpf' h1⟩

/-- Lemma A.21. (D1): `RW ⊆ G.E`. (D2): every write of `RW` without a backward
reader is causally before a write of `RW` with one. -/
theorem ReachRW.a21 {c : Config} {rw : Finset TEv} (h : ReachRW P M τ (c, rw)) :
    (∀ w ∈ rw, w ∈ c.order) ∧
    (∀ w ∈ rw, ¬ c.IsR w → ∃ w' ∈ rw, c.IsR w' ∧ c.abs.porf (.th w) (.th w')) := by
  exact h.a21_aux

/-- The measure of Theorem A.27, `⟨|RW|, |G.E|⟩` in the lexicographic order,
as one number, for graphs with at most `K` thread events. -/
def measureRW (K : ℕ) (x : Config × Finset TEv) : ℕ :=
  x.2.card * (K + 1) + x.1.abs.events.card

/-- The measure increases with every step from a reached configuration, if
the graphs have at most `K` thread events. (Theorem A.27, step ⟨1⟩1.) -/
theorem StepRW.measure_lt {x y : Config × Finset TEv} {K : ℕ} (hx : ReachRW P M τ x)
    (hK : x.1.abs.events.card ≤ K) (hs : StepRW P M τ x y) : measureRW K x < measureRW K y := by
  have hD1 := hx.a21_aux.1
  obtain ⟨hw, -, -, -⟩ := hx.reach.sound
  obtain ⟨c, rw⟩ := x
  obtain ⟨c', rw'⟩ := y
  obtain ⟨e, k, hs, hrw⟩ := hs
  simp only at hs hrw hD1 hw hK
  subst hrw
  have hfresh : e ∉ c.order := (hs.order hw).1
  unfold measureRW
  cases k with
  | nr =>
    have N := hs.nrFacts hw
    have hev : c'.abs.events = insert e c.abs.events := by
      ext q
      simp [Config.abs, N.order]
    have hcard : c'.abs.events.card = c.abs.events.card + 1 := by
      have hne : e ∉ c.abs.events := fun h => hfresh (List.mem_toFinset.mp h)
      rw [hev]
      exact Finset.card_insert_of_notMem hne
    simp only [Kind.rw]
    omega
  | rv r =>
    have hrw : e ∉ rw := fun h => hfresh (hD1 e h)
    simp only [Kind.rw]
    rw [Finset.card_insert_of_notMem hrw, Nat.succ_mul]
    omega

/-- A run of the algorithm lifts to a run on configurations with `RW`, of the
same length. -/
theorem lift_path {c0 c : Config} {p : List Config} (h : Maz.Path (Step P M τ) c0 p c) :
    ∀ rw0, ∃ p' rw, Maz.Path (StepRW P M τ) (c0, rw0) p' (c, rw) ∧ p'.length = p.length := by
  induction h with
  | nil a => exact fun rw0 => ⟨[], rw0, Maz.Path.nil _, rfl⟩
  | @cons a b c p hab _ ih =>
    intro rw0
    obtain ⟨e, k, hs⟩ := hab
    obtain ⟨p', rw, hp', hl⟩ := ih (k.rw e rw0)
    exact ⟨(b, k.rw e rw0) :: p', rw, Maz.Path.cons ⟨e, k, hs, rfl⟩ hp', by simp [hl]⟩

/-- A reached configuration of a program bounded by `n` has at most
`n * |threads|` thread events. -/
theorem Reach.card_le {c : Config} (h : Reach P M τ c) {n : ℕ} (hn : P.Bounded n) :
    c.abs.events.card ≤ n * P.threads.length := by
  obtain ⟨hw, -, -, hE⟩ := h.sound
  exact hE.card_le hw.1 hn

/-- Theorem A.27 (termination): for a bounded program, the runs of Algorithm 1
have bounded length. -/
theorem terminates {n : ℕ} (hn : P.Bounded n) :
    ∃ B, ∀ (p : List Config) (c : Config),
      Maz.Path (Step P M τ) (Config.init P.mem) p c → p.length ≤ B := by
  refine ⟨(n * P.threads.length) * (n * P.threads.length + 1) + n * P.threads.length, ?_⟩
  intro p c hp
  obtain ⟨p', rw, hp', hl⟩ := lift_path hp ∅
  rw [← hl]
  refine Maz.Path.length_le_of_bounded_measure (measureRW (n * P.threads.length)) _ ?_ ?_ hp'
  · intro x y hx hs
    exact StepRW.measure_lt (K := n * P.threads.length) hx ((ReachRW.reach hx).card_le hn) hs
  · intro x hx
    have hD1 := (ReachRW.a21_aux hx).1
    have hcard := (ReachRW.reach hx).card_le hn
    have hrw : x.2.card ≤ x.1.abs.events.card := by
      apply Finset.card_le_card
      intro w hw
      exact List.mem_toFinset.mpr (hD1 w hw)
    unfold measureRW
    have := Nat.mul_le_mul_right (n * P.threads.length + 1) (le_trans hrw hcard)
    omega

/-- Termination as well-foundedness: there is no infinite run from a reached
configuration. -/
theorem step_wellFounded {n : ℕ} (hn : P.Bounded n) :
    WellFounded (fun c' c : Config => Reach P M τ c ∧ Step P M τ c c') := by
  obtain ⟨B, hB⟩ := terminates (M := M) hn
  have key : ∀ k (c : Config) (p : List Config),
      Maz.Path (Step P M τ) (Config.init P.mem) p c → B - p.length ≤ k →
      Acc (fun c' c : Config => Reach P M τ c ∧ Step P M τ c c') c := by
    intro k
    induction k with
    | zero =>
      intro c p hp hk
      refine Acc.intro _ (fun c' hc' => ?_)
      have := hB _ _ (hp.snoc hc'.2)
      simp only [List.length_append, List.length_singleton] at this
      omega
    | succ k ih =>
      intro c p hp hk
      refine Acc.intro _ (fun c' hc' => ?_)
      have hlen := hB _ _ (hp.snoc hc'.2)
      simp only [List.length_append, List.length_singleton] at hlen
      refine ih c' (p ++ [c']) (hp.snoc hc'.2) ?_
      simp only [List.length_append, List.length_singleton]
      omega
  refine WellFounded.intro (fun c => ?_)
  by_cases hc : Reach P M τ c
  · obtain ⟨p, hp⟩ := Maz.Path.of_reflTransGen hc
    exact key B c p hp (Nat.sub_le _ _)
  · exact Acc.intro _ (fun c' hc' => absurd hc'.1 hc)

/-- For a reached configuration with `RW` of a bounded program: `RW` is no
larger than the set of events, which is bounded. -/
theorem ReachRW.card_le {c : Config} {rw : Finset TEv} (h : ReachRW P M τ (c, rw)) {n : ℕ}
    (hn : P.Bounded n) :
    rw.card ≤ c.abs.events.card ∧ c.abs.events.card ≤ n * P.threads.length := by
  refine ⟨Finset.card_le_card (fun w hw => ?_), (ReachRW.reach h).card_le hn⟩
  exact List.mem_toFinset.mpr (h.a21.1 w hw)

end Condpor
