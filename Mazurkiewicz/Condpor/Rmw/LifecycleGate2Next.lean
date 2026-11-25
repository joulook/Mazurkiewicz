import Mazurkiewicz.Condpor.Rmw.LifecycleGate2Replay

/-!
# Gate clause 2, part 3c: the next event of the run list (LC2-b, continuation 3)

Facts about an execution `G` of `lifeSys` and about the next event `e` of a run list after a
builder prefix:

* `step_some`: a compiled step that is defined is the table entry, the thread has not stopped,
  and the bound is not reached;
* `idx_le_block`: no event of a thread comes after a `block` of it;
* `next_idx`: the next event `e` has index `g.cnt e.tid`, and every earlier event of its
  thread is in the builder;
* `next_act`: its label is the compiled step after the builder's values of its thread.
-/

namespace Condpor

namespace Life

namespace Sem

open _root_.List

variable {P : LProg} {n : ℕ} {G : Graph}

theorem step_some {t : Tid} {u : List (Option Val)} {a : Act}
    (h : (lifeSys P n).toProgram.step t u = some a) :
    lifeTab P t u = some a ∧ stopped (lifeTab P) t u = false ∧ u.length < n ∧ t ∈ P.threads := by
  simp only [lifeSys, mkXProg, mkProg] at h
  split_ifs at h with hc
  simp only [not_or, not_le, not_not, Bool.not_eq_true] at hc
  exact ⟨h, hc.2.2, hc.1, hc.2.1⟩

theorem traceBefore_take (t : Tid) {i j : ℕ} (h : j ≤ i) :
    (G.traceBefore t i).take j = G.traceBefore t j := by
  unfold Graph.traceBefore
  rw [← map_take, take_range, Nat.min_eq_left h]

theorem traceBefore_length (t : Tid) (i : ℕ) : (G.traceBefore t i).length = i := by
  simp [Graph.traceBefore]

/-- No event of a thread comes after one of its `block`s. -/
theorem idx_le_block (hE : (lifeSys P n).toProgram.Exec G) {b e : TEv} (hb : b ∈ G.events)
    (hbb : b.act = .block) (he : e ∈ G.events) (ht : e.tid = b.tid) : e.idx ≤ b.idx := by
  by_contra hlt
  have h1 := (step_some (hE.2 e he)).2.1
  have h2 := (step_some (hE.2 b hb)).1
  rw [hbb] at h2
  have : stopped (lifeTab P) e.tid (G.traceBefore e.tid e.idx) = true := by
    unfold stopped
    refine List.any_eq_true.mpr ⟨b.idx, ?_, ?_⟩
    · rw [List.mem_range, traceBefore_length]; omega
    · rw [traceBefore_take _ (by omega), ht, h2]; rfl
  rw [h1] at this; cases this

theorem pre_append_cons_self {A B : List TEv} {e : TEv} (h : e ∉ A) : pre (A ++ e :: B) e = A := by
  unfold pre
  induction A with
  | nil => simp
  | cons b A ih =>
    have hb : b ≠ e := fun h' => h (h' ▸ mem_cons_self)
    simp only [cons_append, takeWhile_cons, ne_eq, hb, not_false_eq_true, decide_true]
    rw [ih (fun h' => h (mem_cons_of_mem _ h'))]
    simp

/-- An event of a run list is not a tail event, nor before one in its thread. -/
theorem not_tail_before {X : XProgram} {l : List TEv} (hG : G.Wf)
    (hE : (lifeSys P n).toProgram.Exec G) (hl : RunList P X G l) {e q : TEv} (he : e ∈ l)
    (ht : q.tid = e.tid) (hi : q.idx < e.idx) : ¬ IsTail P G q := by
  rintro ⟨p, b, x, hw, hx, hqe⟩
  have heG := hl.sub.sub e he
  have heb : e.idx ≤ b.idx := idx_le_block hE hw.2.1 hw.2.2.2.2.2 heG
    (by rw [← ht]; rcases hqe with rfl | rfl; exacts [hw.2.2.1.symm, rfl])
  have hbe : b.idx ≤ e.idx := by rcases hqe with rfl | rfl <;> have := hw.2.2.2.1 <;> omega
  have hEB : e = b := hG.idx_inj e heG b hw.2.1
    (by rcases hqe with rfl | rfl; exacts [ht.symm.trans hw.2.2.1.symm, ht.symm]) (by omega)
  exact ((hl.mem e).mp he).2 ⟨p, b, x, hw, hx, Or.inr hEB⟩

/-- **The next event** of the run list after the builder prefix: its index is the builder's
count of its thread, and the earlier events of its thread are in the builder. -/
theorem next_idx {X : XProgram} {l rest : List TEv} {g : GB} (hg : g.Ok) (hG : G.Wf)
    (hE : (lifeSys P n).toProgram.Exec G) (hl : RunList P X G l) {e : TEv}
    (hpre : l = g.L ++ e :: rest) :
    e.idx = g.cnt e.tid ∧ ∀ q ∈ G.events, q.tid = e.tid → q.idx < e.idx → q ∈ g.L := by
  have hel : e ∈ l := by rw [hpre]; simp
  have heG := hl.sub.sub e hel
  have heL : e ∉ g.L := by
    have hn := hl.sub.nodup
    rw [hpre] at hn
    exact fun h => (nodup_append.mp hn).2.2 e h e mem_cons_self rfl
  have hbefore : ∀ q ∈ G.events, q.tid = e.tid → q.idx < e.idx → q ∈ g.L := by
    intro q hq ht hi
    have hql : q ∈ l := (hl.mem q).mpr ⟨hq, not_tail_before hG hE hl hel ht hi⟩
    have hb := hl.sub.fwd q hql e hel (Or.inl ⟨hq, heG, ht, hi⟩)
    have := mem_pre_of_before hl.sub.nodup hb
    rwa [hpre, pre_append_cons_self heL] at this
  refine ⟨?_, hbefore⟩
  rcases Nat.lt_trichotomy e.idx (g.cnt e.tid) with h | h | h
  · obtain ⟨q, hq, h1, h2⟩ := hg.present e.tid e.idx h
    have hqG : q ∈ G.events := hl.sub.sub q (by rw [hpre]; exact mem_append_left _ hq)
    exact absurd (hG.idx_inj q hqG e heG h1 h2 ▸ hq) heL
  · exact h
  · obtain ⟨q, hq, h1, h2⟩ := hG.idx_contig e heG (g.cnt e.tid) h
    have := hg.lt_cnt q (hbefore q hq h1 (by omega))
    rw [h1, h2] at this
    omega

/-- The label of the next event is the compiled step after the builder's values. -/
theorem next_act {X : XProgram} {l rest : List TEv} {g : GB} (hg : g.Ok) (hG : G.Wf)
    (hE : (lifeSys P n).toProgram.Exec G) (hl : RunList P X G l) {e : TEv}
    (hpre : l = g.L ++ e :: rest) :
    (lifeSys P n).toProgram.step e.tid (tr P g e.tid) = some e.act := by
  have hel : e ∈ l := by rw [hpre]; simp
  have h := hE.2 e (hl.sub.sub e hel)
  rwa [(next_idx hg hG hE hl hpre).1, ← tr_eq hg hG hl.sub hpre hE.1] at h

/-- The builder's `last` is the last write of its list. -/
theorem GB.Ok.last_eq {g : GB} (hg : g.Ok) (x : Loc) : g.last x = lastW g.L x := by
  unfold GB.last lastW
  rw [hg.co x]
  cases (g.L.filter (writesB x)).getLast? <;> rfl

/-- The value the next event reads in `G` is the one of the builder's `last`. -/
theorem next_rf {X : XProgram} {l rest : List TEv} {g : GB} (hg : g.Ok) (hG : G.Wf)
    (hl : RunList P X G l) {e : TEv} (hpre : l = g.L ++ e :: rest) {x : Loc}
    (hx : e.act = .read x) : G.rf e = some (g.last x) := by
  have hel : e ∈ l := by rw [hpre]; simp
  have heL : e ∉ g.L := by
    have hn := hl.sub.nodup
    rw [hpre] at hn
    exact fun h => (nodup_append.mp hn).2.2 e h e mem_cons_self rfl
  rw [hl.sub.rf_eq hG hel hx, hpre, pre_append_cons_self heL, hg.last_eq]

end Sem

end Life

end Condpor
