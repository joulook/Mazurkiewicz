import Mazurkiewicz.Condpor.Rmw.Complete
import Mazurkiewicz.Condpor.Exit

/-!
# Read-modify-write accesses: fruitless configurations are blocked; the exit

Theorem A.33 of TruSt (the form that Theorem 5(b) of ConDpor takes with
read-modify-write accesses), for bounded programs and a model with
`ExtensibleX` and `ExclExtensible`: a reached configuration from which no
full configuration is reachable has no step. Equivalently (`Rmw.reaches_full`): a
reached configuration that has a step reaches a full one.

The proof is not the printed one (a "deepest" counterexample and a
contradiction). It is an induction along the runs, which terminate
(`step_wellFounded`), with one lemma (`Reach.exists_live_step`): a reached
configuration that has a step has a successor that is full or has a step.
The successor is chosen by the kind of the next event `e`:

* a read: `e` reads the last write. If its mate is the next event, it is
  placed last (Def. A.17, third clause).
* an exclusive write: the given step. After a plain addition of a write there
  is no pending read. After a revisit of `a` the only pending read is `a`,
  which reads the new write; no completed pair reads it, and Def. A.19 gives a
  place for the mate of `a`.
* any other event: the maximal addition; there is no pending read after it.

The exit (`Exit.lean`): "a consistent execution is a prefix of a full one" is
false with atomicity. The error statements are for an erroneous graph that is
a prefix of a full consistent execution.
-/

namespace Condpor

open Program

variable {P : XProgram} {M : Model} {S : Solver} {τ : TieBreak S}

/-- From a reached configuration that is not full the algorithm takes a
non-revisit step, if the read of a prospective pair whose write is the next
event reads the last write, or its source is not read by the read of a
completed pair. -/
theorem Reach.exists_stepX (hM : ExtensibleX P M) (hX : ExclExtensible P M) {c : Config}
    (hc : Reach P.toProgram (M.sym S) τ c) (hnf : ¬ P.toProgram.Full c.abs)
    (H : ∀ r e, P.toProgram.IsNext c.abs e → P.Mate c.abs r e →
      c.abs.rf r = some (c.abs.maxWrite e.loc) ∨
      ∀ s, c.abs.rf r = some s → ¬ ∃ r' w', P.RMW c.abs r' w' ∧ c.abs.rf r' = some s) :
    ∃ e c', StepL P.toProgram (M.sym S) τ c e .nr c' := by
  obtain ⟨hw, -, hcc, hE⟩ := hc.sound
  obtain ⟨a, ha, -⟩ := exists_unique_isNext hnf
  rcases a.act.isRead_or_isWrite_or_isLocal with hk | hk | hk
  · have hact := TEv.IsRead.exists_act hk
    refine ⟨a, _, StepL.read hcc ha hact (Graph.maxWrite_isWriteTo hw.1 _) ?_⟩
    rw [Config.addRead_abs]
    exact hM.sym_ext_read hw.1 hE hcc ha.1 hact
  · by_cases hex : P.ex a.tid (c.abs.trace a.tid) = true
    · obtain ⟨r, hr⟩ := XProgram.exists_mate hw.1 hE ha.1 hk hex
      rcases H r a ha hr with h | h
      · refine ⟨a, _, StepL.write hcc ha hk (Graph.maxWrite_isWriteTo hw.1 _) ?_⟩
        rw [Config.addWrite_abs]
        exact hM.sym_ext_wex hw.1 hE hcc hr h
      · obtain ⟨s, hs, -⟩ := hw.1.rf_read r hr.1 _ (hr.read_act hE)
        obtain ⟨wp, hwp, hcons⟩ := (hX.sym (S := S)) c.abs r a s hw.1 hE hcc hr hs (h s hs)
        refine ⟨a, _, StepL.write hcc ha hk hwp ?_⟩
        rw [Config.addWrite_abs]
        exact hcons
    · refine ⟨a, _, StepL.write hcc ha hk (Graph.maxWrite_isWriteTo hw.1 _) ?_⟩
      rw [Config.addWrite_abs]
      exact hM.sym_ext_write hw.1 hE hcc ha.1 hk (by simpa using hex)
  · by_cases hcs : a.IsCons
    · obtain ⟨φ, hφ⟩ := TEv.IsCons.exists_act hcs
      obtain ⟨b, hb⟩ := hM.sym_ext_cons hw.1 hE hcc ha.1 hφ
      exact ⟨a, _, StepL.sym (b := b) hcc ha hcs (by rw [Config.addLoc_abs]; exact hb)⟩
    · exact ⟨a, _, StepL.loc hcc ha hk hcs (by
        rw [Config.addLoc_abs]
        exact hM.sym_ext_loc_none hw.1 hE hcc ha.1 hk hcs)⟩

/-- After a step that is a revisit, or that adds an event other than a read,
or that adds a read of the last write, the configuration is full or has a
step. -/
theorem Reach.step_after (hM : ExtensibleX P M) (hX : ExclExtensible P M) {c c' : Config}
    {e : TEv} {k : Kind} (hc : Reach P.toProgram (M.sym S) τ c)
    (hs : StepL P.toProgram (M.sym S) τ c e k c') (hnf : ¬ P.toProgram.Full c'.abs)
    (hmax : k = .nr → e.IsRead → c'.abs.rf e = some (c'.abs.maxWrite e.loc)) :
    ∃ e' c3, StepL P.toProgram (M.sym S) τ c' e' .nr c3 := by
  have hc' : Reach P.toProgram (M.sym S) τ c' := hc.tail ⟨e, k, hs⟩
  obtain ⟨hw', -, -, hE'⟩ := hc'.sound
  refine hc'.exists_stepX hM hX hnf (fun r e' _ hm => ?_)
  have hre : Ev.th r = .th (k.me e) := hc.me_eq hs (Rmw.pending hc' hm).1
  cases k with
  | nr =>
    left
    have hr : r = e := Ev.th.inj hre
    subst hr
    have hloc : r.loc = e'.loc := by
      have := hm.read_act hE'
      simp [TEv.loc, this, Act.loc]
    rw [← hloc]
    exact hmax rfl hm.2.1
  | rv a =>
    right
    have hr : r = a := Ev.th.inj hre
    subst hr
    obtain ⟨hw, hpo, -, -⟩ := hc.sound
    obtain ⟨wp, rfl, H⟩ := hs.rvHyp hw hpo
    intro s hs' ⟨r', w', hrw, hrf'⟩
    have hse : s = .th e := by
      have h1 : (c.revisit r e wp).rf r = some s := hs'
      rw [H.rf_r] at h1
      exact (Option.some.inj h1).symm
    subst hse
    have hrf'' : (c.revisit r e wp).rf r' = some (.th e) := hrf'
    rcases H.rf_some hrf'' with ⟨h1, -⟩ | ⟨-, -, h3⟩
    · subst h1
      obtain ⟨-, hw'm, hw't, hw'i, -⟩ := hrw
      obtain ⟨-, -, -, hma, hmt, hmi, -, -⟩ := hm
      have h4 := hw'.1.idx_lt_cnt hw'm
      have h5 := idx_eq_of_mem_avail hma
      rw [hw't, ← hmt, ← h5] at h4
      omega
    · have h4 : c.abs.rf r' = some (.th e) := h3
      exact H.fresh (List.mem_toFinset.mp (hw.1.rf_source_mem h4).2)

/-- A reached configuration that has a step has a successor that is full or
has a step. -/
theorem Reach.exists_live_step (hM : ExtensibleX P M) (hX : ExclExtensible P M)
    {c c1 : Config} (hc : Reach P.toProgram (M.sym S) τ c)
    (h : Step P.toProgram (M.sym S) τ c c1) :
    ∃ c2, Step P.toProgram (M.sym S) τ c c2 ∧
      (P.toProgram.Full c2.abs ∨ ∃ c3, Step P.toProgram (M.sym S) τ c2 c3) := by
  obtain ⟨e, k, hs⟩ := h
  obtain ⟨hw, -, hcc, hE⟩ := hc.sound
  have hnext : P.toProgram.IsNext c.abs e := by
    cases k with
    | nr => exact hs.nr_inv.2.1
    | rv a =>
      obtain ⟨wp, -, -, h, -⟩ := hs.rv_inv
      exact h
  have fin : ∀ {c2 : Config} {k2 : Kind}, StepL P.toProgram (M.sym S) τ c e k2 c2 →
      (k2 = .nr → e.IsRead → c2.abs.rf e = some (c2.abs.maxWrite e.loc)) →
      ∃ c2, Step P.toProgram (M.sym S) τ c c2 ∧
        (P.toProgram.Full c2.abs ∨ ∃ c3, Step P.toProgram (M.sym S) τ c2 c3) := by
    intro c2 k2 hs2 hmax
    refine ⟨c2, ⟨e, k2, hs2⟩, ?_⟩
    by_cases hf : P.toProgram.Full c2.abs
    · exact Or.inl hf
    · obtain ⟨e', c3, h3⟩ := hc.step_after hM hX hs2 hf hmax
      exact Or.inr ⟨c3, e', .nr, h3⟩
  rcases e.act.isRead_or_isWrite_or_isLocal with hk | hk | hk
  · have hact := TEv.IsRead.exists_act hk
    refine fin (StepL.read hcc hnext hact (Graph.maxWrite_isWriteTo hw.1 _) (by
      rw [Config.addRead_abs]
      exact hM.sym_ext_read hw.1 hE hcc hnext.1 hact)) (fun _ _ => ?_)
    rw [Config.addRead_abs]
    simp [Graph.addRead_rf, Graph.maxWrite]
  · have hnr : ¬ e.IsRead := fun hr => Act.not_isRead_and_isWrite e.act ⟨hr, hk⟩
    by_cases hex : P.ex e.tid (c.abs.trace e.tid) = true
    · exact fin hs (fun _ hr => absurd hr hnr)
    · exact fin (StepL.write hcc hnext hk (Graph.maxWrite_isWriteTo hw.1 _) (by
        rw [Config.addWrite_abs]
        exact hM.sym_ext_write hw.1 hE hcc hnext.1 hk (by simpa using hex)))
        (fun _ hr => absurd hr hnr)
  · have hnr : ¬ e.IsRead := fun hr => hk.not_isRead hr
    by_cases hcs : e.IsCons
    · obtain ⟨φ, hφ⟩ := TEv.IsCons.exists_act hcs
      obtain ⟨b, hb⟩ := hM.sym_ext_cons hw.1 hE hcc hnext.1 hφ
      exact fin (StepL.sym (b := b) hcc hnext hcs (by rw [Config.addLoc_abs]; exact hb))
        (fun _ hr => absurd hr hnr)
    · exact fin (StepL.loc hcc hnext hk hcs (by
        rw [Config.addLoc_abs]
        exact hM.sym_ext_loc_none hw.1 hE hcc hnext.1 hk hcs)) (fun _ hr => absurd hr hnr)

/-- A reached configuration of a bounded program that is full or has a step
reaches a full configuration. -/
theorem Rmw.reaches_full {n : ℕ} (hn : P.toProgram.Bounded n) (hM : ExtensibleX P M)
    (hX : ExclExtensible P M) {c : Config} (hc : Reach P.toProgram (M.sym S) τ c)
    (hlive : P.toProgram.Full c.abs ∨ ∃ c1, Step P.toProgram (M.sym S) τ c c1) :
    ∃ c', Relation.ReflTransGen (Step P.toProgram (M.sym S) τ) c c' ∧
      P.toProgram.Full c'.abs := by
  refine (step_wellFounded (M := M.sym S) (τ := τ) hn).induction
    (C := fun c => Reach P.toProgram (M.sym S) τ c →
      (P.toProgram.Full c.abs ∨ ∃ c1, Step P.toProgram (M.sym S) τ c c1) →
      ∃ c', Relation.ReflTransGen (Step P.toProgram (M.sym S) τ) c c' ∧
        P.toProgram.Full c'.abs) c ?_ hc hlive
  intro c ih hc h
  rcases h with hf | ⟨c1, h1⟩
  · exact ⟨c, .refl, hf⟩
  · obtain ⟨c2, h2, hgood⟩ := hc.exists_live_step hM hX h1
    obtain ⟨c', hc', hf'⟩ := ih c2 ⟨hc, h2⟩ (hc.tail h2) hgood
    exact ⟨c', Relation.ReflTransGen.head h2 hc', hf'⟩

/-- Theorem A.33: a reached configuration of a bounded program from which no
full configuration is reachable (a fruitless one) has no step (is blocked). -/
theorem Rmw.blocked_of_fruitless {n : ℕ} (hn : P.toProgram.Bounded n)
    (hM : ExtensibleX P M) (hX : ExclExtensible P M) {c : Config}
    (hc : Reach P.toProgram (M.sym S) τ c)
    (hfr : ¬ ∃ c', Relation.ReflTransGen (Step P.toProgram (M.sym S) τ) c c' ∧
      P.toProgram.Full c'.abs) :
    ¬ ∃ c1, Step P.toProgram (M.sym S) τ c c1 :=
  fun h => hfr (Rmw.reaches_full hn hM hX hc (Or.inr h))

/-- A necessary condition for a reached configuration that is not full and
has no step: the next event is the write of a prospective pair whose read has
the source of the read of a completed pair. -/
theorem Rmw.collision_of_blocked (hM : ExtensibleX P M) (hX : ExclExtensible P M)
    {c : Config} (hc : Reach P.toProgram (M.sym S) τ c) (hnf : ¬ P.toProgram.Full c.abs)
    (hb : ¬ ∃ c1, Step P.toProgram (M.sym S) τ c c1) :
    ∃ r e r' w' s, P.toProgram.IsNext c.abs e ∧ P.Mate c.abs r e ∧ c.abs.rf r = some s ∧
      P.RMW c.abs r' w' ∧ c.abs.rf r' = some s := by
  by_contra hne
  obtain ⟨e, c', hs⟩ := hc.exists_stepX hM hX hnf (fun r e hn hm =>
    Or.inr (fun s hs ⟨r', w', hrw, hrf⟩ => hne ⟨r, e, r', w', s, hn, hm, hs, hrw, hrf⟩))
  exact hb ⟨c', e, .nr, hs⟩

/-- Without exclusive accesses, a reached configuration that is not full has
a non-revisit step (Def. A.19 is not needed). -/
theorem Reach.exists_step_of_no_ex (hM : ExtensibleX P M) (hno : ∀ t u, P.ex t u = false)
    {c : Config} (hc : Reach P.toProgram (M.sym S) τ c) (hnf : ¬ P.toProgram.Full c.abs) :
    ∃ e c', StepL P.toProgram (M.sym S) τ c e .nr c' := by
  obtain ⟨hw, -, hcc, hE⟩ := hc.sound
  obtain ⟨a, ha, -⟩ := exists_unique_isNext hnf
  rcases a.act.isRead_or_isWrite_or_isLocal with hk | hk | hk
  · have hact := TEv.IsRead.exists_act hk
    refine ⟨a, _, StepL.read hcc ha hact (Graph.maxWrite_isWriteTo hw.1 _) ?_⟩
    rw [Config.addRead_abs]
    exact hM.sym_ext_read hw.1 hE hcc ha.1 hact
  · refine ⟨a, _, StepL.write hcc ha hk (Graph.maxWrite_isWriteTo hw.1 _) ?_⟩
    rw [Config.addWrite_abs]
    exact hM.sym_ext_write hw.1 hE hcc ha.1 hk (hno _ _)
  · by_cases hcs : a.IsCons
    · obtain ⟨φ, hφ⟩ := TEv.IsCons.exists_act hcs
      obtain ⟨b, hb⟩ := hM.sym_ext_cons hw.1 hE hcc ha.1 hφ
      exact ⟨a, _, StepL.sym (b := b) hcc ha hcs (by rw [Config.addLoc_abs]; exact hb)⟩
    · exact ⟨a, _, StepL.loc hcc ha hk hcs (by
        rw [Config.addLoc_abs]
        exact hM.sym_ext_loc_none hw.1 hE hcc ha.1 hk hcs)⟩

/-- Theorem 5(b) as printed, for a program without exclusive accesses: every
reached configuration reaches a full one. -/
theorem Rmw.reaches_full_of_no_ex {n : ℕ} (hn : P.toProgram.Bounded n)
    (hM : ExtensibleX P M) (hno : ∀ t u, P.ex t u = false)
    {c : Config} (hc : Reach P.toProgram (M.sym S) τ c) :
    ∃ c', Relation.ReflTransGen (Step P.toProgram (M.sym S) τ) c c' ∧
      P.toProgram.Full c'.abs := by
  refine (step_wellFounded (M := M.sym S) (τ := τ) hn).induction
    (C := fun c => Reach P.toProgram (M.sym S) τ c →
      ∃ c', Relation.ReflTransGen (Step P.toProgram (M.sym S) τ) c c' ∧
        P.toProgram.Full c'.abs) c ?_ hc
  intro c ih hc
  by_cases hf : P.toProgram.Full c.abs
  · exact ⟨c, .refl, hf⟩
  · obtain ⟨e, c1, hs⟩ := hc.exists_step_of_no_ex hM hno hf
    have h1 : Step P.toProgram (M.sym S) τ c c1 := ⟨e, .nr, hs⟩
    obtain ⟨c', hc', hf'⟩ := ih c1 ⟨hc, h1⟩ (hc.tail h1)
    exact ⟨c', Relation.ReflTransGen.head h1 hc', hf'⟩

/-! ### The exit at an erroneous graph -/

variable {E : ErrPred}

/-- If an erroneous graph is a prefix of a full consistent execution of a
bounded program, the algorithm with exit reaches an erroneous configuration. -/
theorem Rmw.exists_reachX_err {n : ℕ} (hn : P.toProgram.Bounded n) (hM : ExtensibleX P M)
    {G Gf : Graph} (hGf : Gf.Wf) (hEf : P.toProgram.Exec Gf) (hcf : (M.sym S).cons Gf)
    (hff : P.toProgram.Full Gf) (hp : G.IsPrefixOf Gf) (herr : E.isErr G) :
    ∃ c, ReachX E P.toProgram (M.sym S) τ c ∧ E.isErr c.abs := by
  by_contra hne
  have hno : ∀ c, ReachX E P.toProgram (M.sym S) τ c → ¬ E.isErr c.abs :=
    fun c hc he => hne ⟨c, hc, he⟩
  obtain ⟨c, hcr, hcabs⟩ := Rmw.complete (τ := τ) hn hM hGf hEf hcf hff
  exact hno c (reachX_of_reach hno hcr) (hcabs ▸ E.mono hGf hp herr)

/-- If a full consistent execution of a bounded program is erroneous, the
algorithm with exit reaches an erroneous configuration. -/
theorem Rmw.exists_reachX_err_full {n : ℕ} (hn : P.toProgram.Bounded n)
    (hM : ExtensibleX P M) {Gf : Graph} (hGf : Gf.Wf) (hEf : P.toProgram.Exec Gf)
    (hcf : (M.sym S).cons Gf) (hff : P.toProgram.Full Gf) (herr : E.isErr Gf) :
    ∃ c, ReachX E P.toProgram (M.sym S) τ c ∧ E.isErr c.abs := by
  by_contra hne
  have hno : ∀ c, ReachX E P.toProgram (M.sym S) τ c → ¬ E.isErr c.abs :=
    fun c hc he => hne ⟨c, hc, he⟩
  obtain ⟨c, hcr, hcabs⟩ := Rmw.complete (τ := τ) hn hM hGf hEf hcf hff
  exact hno c (reachX_of_reach hno hcr) (hcabs ▸ herr)

/-- The reading of Theorem 4 for the algorithm with exit: either it reaches an
erroneous configuration, or it visits every full consistent execution. -/
theorem Rmw.complete_exit {n : ℕ} (hn : P.toProgram.Bounded n) (hM : ExtensibleX P M) :
    (∃ c, ReachX E P.toProgram (M.sym S) τ c ∧ E.isErr c.abs) ∨
    ∀ Gf : Graph, Gf.Wf → P.toProgram.Exec Gf → (M.sym S).cons Gf → P.toProgram.Full Gf →
      ∃ c, ReachX E P.toProgram (M.sym S) τ c ∧ c.abs = Gf := by
  by_cases h : ∃ c, ReachX E P.toProgram (M.sym S) τ c ∧ E.isErr c.abs
  · exact Or.inl h
  · right
    intro Gf hGf hEf hcf hff
    obtain ⟨c, hcr, hcabs⟩ := Rmw.complete (τ := τ) hn hM hGf hEf hcf hff
    exact ⟨c, reachX_of_reach (fun c hc he => h ⟨c, hc, he⟩) hcr, hcabs⟩

end Condpor
