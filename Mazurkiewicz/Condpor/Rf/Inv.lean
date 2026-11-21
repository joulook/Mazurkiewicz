import Mazurkiewicz.Condpor.Rf.Alg

/-!
# The reads-from version: invariants and termination

Proposition A.22, Lemma A.21 and Theorem A.27 of the TruSt appendix for the
steps of `Rf/Alg.lean`. The clauses of these statements speak of the
insertion order, `rf`, `porf` and the available events, not of coherence. A
non-revisit step is a step of `Alg.lean`, and a revisit step from `c` is a
step of `Alg.lean` from `c` with the coherence order of line 16
(`StepR.lift`), so the accepted proofs for one step apply; the inductions
over runs are repeated.
-/

namespace Condpor

open Program

variable {P : Program} {M : Model} {S : Solver} {τ : TieBreak S} {γ : CoChoice M}

/-! ### The invariant does not depend on coherence -/

theorem LastStep.withCo {c : Config} {e : TEv} {k : Kind} (L : LastStep P c e k)
    (co : Loc → List TEv) : LastStep P (c.withCo co) e k :=
  ⟨L.head, L.me, L.p5a, L.p5b, L.rv⟩

theorem Inv.withCo {c : Config} (I : Inv P c) (co : Loc → List TEv) : Inv P (c.withCo co) :=
  ⟨I.p1, I.p2, I.p6, I.last.imp id (fun ⟨e, k, L⟩ => ⟨e, k, L.withCo co⟩)⟩

/-- The premises of a revisit, for the configuration with the order of line
16. -/
theorem StepR.rvHyp {c c' : Config} {w r : TEv} (hc : c.Wf) (hpo : c.PoLt)
    (h : StepR P M γ τ c w (.rv r) c') :
    RvHyp P τ (c.star γ r w) r w .init ∧ c' = ((c.star γ r w).revisit r w .init).canon := by
  obtain ⟨hsW, -, hc'⟩ := h.lift hc hpo
  obtain ⟨-, -, h1, h2, h3, h4, h5, h6, -⟩ := h.rv_inv
  exact ⟨⟨hsW, hpo, h1, h2, h3, h4, h5, h6, trivial⟩, hc'⟩

/-- Every reached configuration satisfies the invariant. -/
theorem ReachR.inv {c : Config} (h : ReachR P M γ τ c) : Inv P c := by
  unfold ReachR at h
  induction h with
  | refl =>
    refine ⟨?_, ?_, ?_, Or.inl rfl⟩
    · intro s q hbw
      exact absurd hbw.2.1 (by simp [Config.init])
    · intro x hx
      exact absurd hx (by simp [Config.init])
    · intro s q p _ _ _ _ hp
      exact absurd hp (by simp [Config.init])
  | @tail b c' hb hs ih =>
    have hbR : ReachR P M γ τ b := hb
    obtain ⟨hw, hpo, -, -, -⟩ := hbR.sound
    obtain ⟨e, k, hs⟩ := hs
    cases k with
    | nr => exact (inv_nr hw ih hs.nr_inv.1).1
    | rv r =>
      obtain ⟨H, rfl⟩ := hs.rvHyp hw hpo
      exact (inv_rv (ih.withCo _) H).1.withCo _

/-- Proposition A.22 for the steps of the reads-from version. -/
theorem ReachR.a22 {c c' : Config} {e : TEv} {k : Kind}
    (h : ReachR P M γ τ c) (hs : StepR P M γ τ c e k c') : A22 P c e k c' := by
  obtain ⟨hw, hpo, -, -, -⟩ := h.sound
  have I := h.inv
  cases k with
  | nr =>
    obtain ⟨I', L'⟩ := inv_nr hw I hs.nr_inv.1
    refine ⟨I'.p1, I'.p2, ?_, L'.me, L'.p5a, L'.p5b, I'.p6, ?_⟩
    · intro r hk
      cases hk
    · intro r hk
      cases hk
  | rv r =>
    obtain ⟨H, rfl⟩ := hs.rvHyp hw hpo
    obtain ⟨I', L', hP3, hP9⟩ := inv_rv (I.withCo _) H
    refine ⟨I'.p1, I'.p2, ?_, L'.me, L'.p5a, L'.p5b, I'.p6, ?_⟩
    · intro r' hk
      cases hk
      exact hP3
    · intro r' hk
      cases hk
      exact hP9

theorem ReachR.lastStep {c : Config} (h : ReachR P M γ τ c) (hne : c.order ≠ []) :
    ∃ e k, LastStep P c e k :=
  h.inv.last.resolve_left hne

theorem ReachR.me_eq {c c' : Config} {e : TEv} {k : Kind} (h : ReachR P M γ τ c)
    (hs : StepR P M γ τ c e k c') {a : Ev} (ha : c'.abs.IsMe a) : a = .th (k.me e) :=
  ha.unique (h.a22 hs).p4

theorem ReachR.step {c c' : Config} (h : ReachR P M γ τ c) (hs : StepRf P M γ τ c c') :
    ReachR P M γ τ c' := Relation.ReflTransGen.tail h hs

/-! ### Termination -/

/-- A step on configurations with the set `RW` (Def. A.4). -/
def StepRWR (P : Program) (M : Model) (γ : CoChoice M) {S : Solver} (τ : TieBreak S)
    (x y : Config × Finset TEv) : Prop :=
  ∃ e k, StepR P M γ τ x.1 e k y.1 ∧ y.2 = k.rw e x.2

/-- The configurations with `RW` reached from `⟨∅, ∅, ∅⟩`. -/
def ReachRWR (P : Program) (M : Model) (γ : CoChoice M) {S : Solver} (τ : TieBreak S)
    (x : Config × Finset TEv) : Prop :=
  Relation.ReflTransGen (StepRWR P M γ τ) (Config.init P.mem, ∅) x

theorem ReachRWR.reach {x : Config × Finset TEv} (h : ReachRWR P M γ τ x) :
    ReachR P M γ τ x.1 := by
  unfold ReachRWR at h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨e, k, hs, -⟩ := hs
    exact ih.tail ⟨e, k, hs⟩

theorem ReachR.exists_rw {c : Config} (h : ReachR P M γ τ c) :
    ∃ rw, ReachRWR P M γ τ (c, rw) := by
  unfold ReachR at h
  induction h with
  | refl => exact ⟨∅, Relation.ReflTransGen.refl⟩
  | tail _ hs ih =>
    obtain ⟨rw, hrw⟩ := ih
    obtain ⟨e, k, hs⟩ := hs
    exact ⟨k.rw e rw, hrw.tail ⟨e, k, hs, rfl⟩⟩

/-- Lemma A.21. (D1): `RW ⊆ G.E`. (D2): every write of `RW` without a backward
reader is causally before a write of `RW` with one. -/
theorem ReachRWR.a21 {x : Config × Finset TEv} (h : ReachRWR P M γ τ x) :
    (∀ w ∈ x.2, w ∈ x.1.order) ∧
    (∀ w ∈ x.2, ¬ x.1.IsR w → ∃ w' ∈ x.2, x.1.IsR w' ∧ x.1.abs.porf (.th w) (.th w')) := by
  have hreach := h
  unfold ReachRWR at h
  induction h with
  | refl => exact ⟨fun w hw => absurd hw (by simp), fun w hw => absurd hw (by simp)⟩
  | @tail b y hb hs ih =>
    obtain ⟨hD1, hD2⟩ := ih hb
    have hbR : ReachR P M γ τ b.1 := ReachRWR.reach hb
    obtain ⟨hw, hpo, -, -, -⟩ := hbR.sound
    obtain ⟨c, rw⟩ := b
    obtain ⟨c', rw'⟩ := y
    obtain ⟨e, k, hs, hrw⟩ := hs
    simp only at hs hrw hD1 hD2 hw hpo ⊢
    subst hrw
    cases k with
    | nr =>
      have hs := hs.nr_inv.1
      have N := hs.nrFacts hw
      refine ⟨fun w hw' => ?_, fun w hw' hnr => ?_⟩
      · rw [N.order]
        exact List.mem_cons_of_mem _ (hD1 w hw')
      · have hnr' : ¬ c.IsR w := fun ⟨q, hq⟩ => hnr ⟨q, (N.bw_iff hw).mpr hq⟩
        obtain ⟨w', hw'm, ⟨q', hq'⟩, hpf⟩ := hD2 w hw' hnr'
        exact ⟨w', hw'm, ⟨q', (N.bw_iff hw).mpr hq'⟩, N.porf_mono hpf⟩
    | rv r =>
      obtain ⟨H, rfl⟩ := hs.rvHyp hw hpo
      change (∀ w ∈ insert e rw, w ∈ ((c.star γ r e).revisit r e Ev.init).order) ∧
        (∀ w ∈ insert e rw, ¬ ((c.star γ r e).revisit r e Ev.init).IsR w →
          ∃ w' ∈ insert e rw, ((c.star γ r e).revisit r e Ev.init).IsR w' ∧
            ((c.star γ r e).revisit r e Ev.init).abs.porf (.th w) (.th w'))
      have hD1 : ∀ w ∈ rw, w ∈ (c.star γ r e).order := hD1
      have hD2 : ∀ w ∈ rw, ¬ (c.star γ r e).IsR w →
          ∃ w' ∈ rw, (c.star γ r e).IsR w' ∧ (c.star γ r e).abs.porf (.th w) (.th w') := hD2
      -- a write of `R` is not deleted (D1 of Lemma A.20)
      have hRnd : ∀ s q, (c.star γ r e).Bw s q → ¬ (c.star γ r e).Deleted r e s := fun s q hbw hd =>
        A20_D1 H.hc H.hmax hd hbw
      have hRne : ∀ s q, (c.star γ r e).Bw s q → s ≠ r := fun s q hbw h' =>
        A20_D3 H.hc H.hpo H.hr H.hnp H.hmax (x := r) (Or.inr rfl) (Or.inl h'.symm) hbw
      -- the writes of `RW` are kept
      have hkept : ∀ w ∈ rw, w ∈ (c.star γ r e).keep r e := by
        intro w hw'
        rw [Config.mem_keep_iff]
        refine ⟨hD1 w hw', fun hd => ?_⟩
        by_cases hR : (c.star γ r e).IsR w
        · obtain ⟨q, hq⟩ := hR
          exact hRnd w q hq hd
        · obtain ⟨w', hw'm, ⟨q', hq'⟩, hpf⟩ := hD2 w hw' hR
          exact A20_D2 H.hc H.hpo H.hr H.hnp H.hmax (Or.inl hd) (hD1 w' hw'm)
            (hRnd w' q' hq') hpf
      have heR : ((c.star γ r e).revisit r e Ev.init).IsR e := ⟨r, H.bw_iff.mpr (Or.inl ⟨rfl, rfl⟩)⟩
      -- a write of `R` stays in `R`, or becomes causally before the new write
      have lift : ∀ s q, (c.star γ r e).Bw s q →
          ((c.star γ r e).revisit r e Ev.init).IsR s ∨
            ((c.star γ r e).revisit r e Ev.init).abs.porf (.th s) (.th e) := by
        intro s q hbw
        by_cases hq : (c.star γ r e).Deleted r e q ∨ q = r
        · exact Or.inr (H.porf_w_iff.mp (Config.porf_of_max_bw H.hc (H.hmax q hq) hbw))
        · have hqk : q ∈ (c.star γ r e).keep r e :=
            (Config.mem_keep_iff c r e q).mpr ⟨hbw.2.2.1, fun hd => hq (Or.inl hd)⟩
          exact Or.inl ⟨q, H.bw_iff.mpr (Or.inr ⟨hbw, hqk, fun h' => hq (Or.inr h')⟩)⟩
      refine ⟨fun w hw' => ?_, fun w hw' hnr => ?_⟩
      · rcases Finset.mem_insert.mp hw' with hwe | hwm
        · exact H.mem_order'.mpr (Or.inl hwe)
        · exact H.mem_order'.mpr (Or.inr (hkept w hwm))
      · rcases Finset.mem_insert.mp hw' with hwe | hwm
        · exact absurd (hwe ▸ heR) hnr
        · by_cases hR : (c.star γ r e).IsR w
          · obtain ⟨q, hq⟩ := hR
            rcases lift w q hq with h1 | h1
            · exact absurd h1 hnr
            · exact ⟨e, Finset.mem_insert_self _ _, heR, h1⟩
          · obtain ⟨w', hw'm, ⟨q', hq'⟩, hpf⟩ := hD2 w hwm hR
            have hpf' : ((c.star γ r e).revisit r e Ev.init).abs.porf (.th w) (.th w') :=
              H.porf_kept (hD1 w' hw'm) (hRnd w' q' hq') (hRne w' q' hq') hpf
            rcases lift w' q' hq' with h1 | h1
            · exact ⟨w', Finset.mem_insert_of_mem hw'm, h1, hpf'⟩
            · exact ⟨e, Finset.mem_insert_self _ _, heR, Relation.TransGen.trans hpf' h1⟩

/-- The measure increases with every step from a reached configuration, if
the graphs have at most `K` thread events. -/
theorem StepRWR.measure_lt {x y : Config × Finset TEv} {K : ℕ} (hx : ReachRWR P M γ τ x)
    (hK : x.1.abs.events.card ≤ K) (hs : StepRWR P M γ τ x y) :
    measureRW K x < measureRW K y := by
  have hD1 := hx.a21.1
  obtain ⟨hw, hpo, -, -, -⟩ := hx.reach.sound
  obtain ⟨c, rw⟩ := x
  obtain ⟨c', rw'⟩ := y
  obtain ⟨e, k, hs, hrw⟩ := hs
  simp only at hs hrw hD1 hw hpo hK
  subst hrw
  unfold measureRW
  cases k with
  | nr =>
    have hs := hs.nr_inv.1
    have hfresh : e ∉ c.order := (hs.order hw).1
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
    obtain ⟨H, rfl⟩ := hs.rvHyp hw hpo
    have hfresh : e ∉ c.order := H.fresh
    have hrw : e ∉ rw := fun h => hfresh (hD1 e h)
    simp only [Kind.rw]
    rw [Finset.card_insert_of_notMem hrw, Nat.succ_mul]
    omega

theorem lift_pathR {c0 c : Config} {p : List Config}
    (h : Maz.Path (StepRf P M γ τ) c0 p c) :
    ∀ rw0, ∃ p' rw, Maz.Path (StepRWR P M γ τ) (c0, rw0) p' (c, rw) ∧
      p'.length = p.length := by
  induction h with
  | nil a => exact fun rw0 => ⟨[], rw0, Maz.Path.nil _, rfl⟩
  | @cons a b c p hab _ ih =>
    intro rw0
    obtain ⟨e, k, hs⟩ := hab
    obtain ⟨p', rw, hp', hl⟩ := ih (k.rw e rw0)
    exact ⟨(b, k.rw e rw0) :: p', rw, Maz.Path.cons ⟨e, k, hs, rfl⟩ hp', by simp [hl]⟩

theorem ReachR.card_le {c : Config} (h : ReachR P M γ τ c) {n : ℕ} (hn : P.Bounded n) :
    c.abs.events.card ≤ n * P.threads.length := by
  obtain ⟨hw, -, -, -, hE⟩ := h.sound
  exact hE.card_le hw.1 hn

/-- Termination: for a bounded program, the runs of the reads-from version
have bounded length. -/
theorem terminatesR {n : ℕ} (hn : P.Bounded n) :
    ∃ B, ∀ (p : List Config) (c : Config),
      Maz.Path (StepRf P M γ τ) (Config.init P.mem) p c → p.length ≤ B := by
  refine ⟨(n * P.threads.length) * (n * P.threads.length + 1) + n * P.threads.length, ?_⟩
  intro p c hp
  obtain ⟨p', rw, hp', hl⟩ := lift_pathR hp ∅
  rw [← hl]
  refine Maz.Path.length_le_of_bounded_measure (measureRW (n * P.threads.length)) _ ?_ ?_ hp'
  · intro x y hx hs
    exact StepRWR.measure_lt (K := n * P.threads.length) hx
      ((ReachRWR.reach hx).card_le hn) hs
  · intro x hx
    have hD1 := (ReachRWR.a21 hx).1
    have hcard := (ReachRWR.reach hx).card_le hn
    have hrw : x.2.card ≤ x.1.abs.events.card := by
      apply Finset.card_le_card
      intro w hw
      exact List.mem_toFinset.mpr (hD1 w hw)
    unfold measureRW
    have := Nat.mul_le_mul_right (n * P.threads.length + 1) (le_trans hrw hcard)
    omega

end Condpor
