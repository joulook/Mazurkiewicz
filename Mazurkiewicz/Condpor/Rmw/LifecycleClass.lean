import Mazurkiewicz.Condpor.Rmw.LifecycleLemmas

/-!
# Thread lifecycle: the classifier and the lemmas (LC1, round 2)

The classifier `lifeClass` of §3 works on configurations; the lemmas of §4 on graphs. For a
well-formed configuration `c` whose graph is an execution of `lifeSys P n` with
`fragB P = true`:

* `waitOf_kind`: the wait of a thread is computed from the read that lemma 7 gives, and its
  kind is one of `lockW`, `startW`, `joinW`, `asm` (`kindOf_of_kinds`).
* `lifeClass_ne_odd`: the class is never `odd`. (Outside the fragment it can be, and a
  `block` can be misclassified: `outsideAsmSt`, `outsideLockAsm` in `LifecycleEx.lean`.)
* `lifeClass_not_exploration_iff` (no hypothesis on the program): for a class that is
  neither `cut` nor `odd`, "not exploration" is "every lock, start and join wait is final".
* `finalB_iff`: finality on the configuration is `rf = maxWrite` on its graph.
* `lifeClass_ne_cut_of_full`: a well-formed full configuration under an adequate bound is not
  classified `cut`.
* `lc_lemma8_terminal`: lemma 8 as designed, through `lifeClass`: in a full graph under an
  adequate bound that is not exploration (hence terminal-valid, by
  `lifeClass_ne_cut_of_full`), a thread whose start-read
  returned `0` has no write of its lifecycle location (in particular no start write), and
  its events are exactly the start-read `read (st t)` of value `0` and a `block`.
-/

namespace Condpor

namespace Life

open Program Targets

variable {P : LProg} {n : ℕ}

/-! ### Events of a thread in a configuration -/

theorem mem_of_evAt {c : Config} {t : Tid} {i : ℕ} {b : TEv} (h : c.evAt t i = some b) :
    b ∈ c.abs.events ∧ b.tid = t ∧ b.idx = i := by
  have hp := List.find?_some h
  have hm := List.mem_of_find?_eq_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨List.mem_toFinset.mpr hm, hp.1, hp.2⟩

theorem mem_of_thEvents {c : Config} {t : Tid} {b : TEv} (h : b ∈ thEvents c t) :
    b ∈ c.abs.events ∧ b.tid = t := by
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp h
  obtain ⟨h1, h2, -⟩ := mem_of_evAt hi
  exact ⟨h1, h2⟩

theorem evAt_of_mem {c : Config} (hc : c.Wf) {p : TEv} (hp : p ∈ c.abs.events) {t : Tid}
    (ht : p.tid = t) {i : ℕ} (hi : p.idx = i) : c.evAt t i = some p := by
  rw [Config.evAt_eq c hc]
  exact Graph.evAt_eq_some_of_inj' hc.1.idx_inj hp ht hi

/-- Finality on a configuration is `rf = maxWrite` on its graph. -/
theorem finalB_iff (c : Config) (r : TEv) :
    finalB c r = true ↔ c.abs.rf r = some (c.abs.maxWrite r.act.loc) := by
  unfold finalB coMax Graph.maxWrite
  simp only [decide_eq_true_eq]
  rfl

/-! ### The kind of a wait -/

/-- The kinds of lemma 7 are the rows of the kind table. -/
theorem kindOf_of_kinds (hF : Frag P) {c : Config} {t : Tid} (ht : t ∈ P.threads) {p : TEv}
    {i : ℕ} {x : Loc} (hact : p.act = .read x) (hk : BlockKinds P t i x (c.abs.ret p)) :
    (i = 0 ∧ kindOf P c t p = .startW) ∨ kindOf P c t p = .lockW ∨
      kindOf P c t p = .joinW ∨ kindOf P c t p = .asm := by
  rcases hk with ⟨hi, -, hx, hv⟩ | ⟨hl, hv⟩ | ⟨w, hw, hwt, -, hx, hv⟩ | hd
  · subst hx
    left
    refine ⟨hi, ?_⟩
    simp [kindOf, hact, hF.st_not_lock t ht, hv]
  · right; left
    simp [kindOf, hact, hl, hv]
  · subst hx
    right; right; left
    have hne : P.st w ≠ P.st t := fun h => hwt (hF.st_inj w hw t ht h)
    have hany : P.threads.any (fun u => decide (u ≠ t ∧ P.st u = P.st w)) = true :=
      List.any_eq_true.mpr ⟨w, hw, by simp [hwt]⟩
    have h1 : (P.isLock (P.st w) && decide (c.abs.ret p ≠ some 0)) = false := by
      simp [hF.st_not_lock w hw]
    have h2 : (decide (P.st w = P.st t) && decide (c.abs.ret p = some 0)) = false := by
      simp [hne]
    have h3 : (P.threads.any (fun u => decide (u ≠ t ∧ P.st u = P.st w)) &&
        decide (c.abs.ret p = some 1)) = true := by
      rw [hany]; simp [hv]
    simp only [kindOf, hact, h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
  · right; right; right
    have hl : P.isLock x = false := by
      simp only [LProg.isData, Bool.and_eq_true, Bool.not_eq_true'] at hd
      exact hd.1
    have hs : P.isSt x = false := by
      simp only [LProg.isData, Bool.and_eq_true, Bool.not_eq_true'] at hd
      exact hd.2
    have hxt : x ≠ P.st t := fun h => by rw [h, hF.isSt_st ht] at hs; cases hs
    have hany : P.threads.any (fun u => decide (u ≠ t ∧ P.st u = x)) = false := by
      rw [Bool.eq_false_iff]
      intro h'
      obtain ⟨u, hu, hu'⟩ := List.any_eq_true.mp h'
      simp only [decide_eq_true_eq] at hu'
      rw [← hu'.2, hF.isSt_st hu] at hs
      cases hs
    have h1 : (P.isLock x && decide (c.abs.ret p ≠ some 0)) = false := by simp [hl]
    have h2 : (decide (x = P.st t) && decide (c.abs.ret p = some 0)) = false := by simp [hxt]
    have h3 : (P.threads.any (fun u => decide (u ≠ t ∧ P.st u = x)) &&
        decide (c.abs.ret p = some 1)) = false := by
      rw [hany]; simp
    simp only [kindOf, hact, h1, h2, h3, hd, Bool.false_eq_true, ↓reduceIte]

/-- The wait of a thread of a fragment execution: its `block`, the read before it (the read
of lemma 7), and a kind that is not `odd`. -/
theorem waitOf_kind (hF : Frag P) {c : Config} (hc : c.Wf)
    (hE : (lifeSys P n).toProgram.Exec c.abs) {t : Tid} {w : Kind × Bool}
    (h : waitOf P c t = some w) :
    ∃ b ∈ c.abs.events, b.tid = t ∧ b.act = .block ∧ ∃ p ∈ c.abs.events, p.tid = t ∧
      p.idx + 1 = b.idx ∧ w = (kindOf P c t p, finalB c p) ∧ w.1 ≠ .odd := by
  unfold waitOf at h
  split at h
  next b hb =>
    have hbm := mem_of_thEvents (List.mem_of_getLast? hb)
    split_ifs at h with hblk
    obtain ⟨p, hp, hpt, hpi, x, hpa, hk⟩ := lc_lemma7 hF hc.1 hE hbm.1 hblk
    have ht : t ∈ P.threads := hbm.2 ▸ (ev_tab hE hbm.1).2.2
    rw [hbm.2] at hpt hk
    have hev : c.evAt t (b.idx - 1) = some p := evAt_of_mem hc hp hpt (by omega)
    have hbi : b.idx = p.idx + 1 := hpi.symm
    rw [hev] at h
    rw [hbi] at h
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨b, hbm.1, hbm.2, hblk, p, hp, hpt, hpi, rfl, ?_⟩
    rcases kindOf_of_kinds hF ht hpa hk with ⟨-, h⟩ | h | h | h <;> simp [h]
  next => cases h

/-! ### The class -/

/-- **`lifeClass` is never `odd`** on a well-formed configuration whose graph is an
execution of a program of the fragment. -/
theorem lifeClass_ne_odd (hF : Frag P) {c : Config} (hc : c.Wf)
    (hE : (lifeSys P n).toProgram.Exec c.abs) : lifeClass P c ≠ .odd := by
  have hno : ((P.threads.filterMap (waitOf P c)).any (fun w => decide (w.1 = .odd))) =
      false := by
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨w, hw, hwo⟩ := List.any_eq_true.mp h
    obtain ⟨t, -, ht⟩ := List.mem_filterMap.mp hw
    obtain ⟨-, -, -, -, -, -, -, -, -, hk⟩ := waitOf_kind hF hc hE ht
    exact hk (by simpa using hwo)
  unfold lifeClass
  simp only [hno]
  split_ifs <;> simp_all

/-- **The classifier and the finality of the waits**: for a class that is neither `cut`
nor `odd`, it is not `exploration` iff every lock, start and join wait (every wait whose
kind is not `asm`) is final. -/
theorem lifeClass_not_exploration_iff {c : Config} (hcut : lifeClass P c ≠ .cut)
    (hodd : lifeClass P c ≠ .odd) :
    lifeClass P c ≠ .exploration ↔
      ∀ t ∈ P.threads, ∀ k f, waitOf P c t = some (k, f) → k ≠ .asm → f = true := by
  have hc1 : P.threads.any (cutB P c) = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact hcut (by unfold lifeClass; simp [h])
  have hc2 : ((P.threads.filterMap (waitOf P c)).any (fun w => decide (w.1 = .odd))) =
      false := by
    rw [Bool.eq_false_iff]
    intro h
    exact hodd (by unfold lifeClass; simp [hc1, h])
  have hiff : ((P.threads.filterMap (waitOf P c)).any
      (fun w => decide (w.1 ≠ .asm) && !w.2)) = false ↔
      ∀ t ∈ P.threads, ∀ k f, waitOf P c t = some (k, f) → k ≠ .asm → f = true := by
    rw [Bool.eq_false_iff]
    constructor
    · intro h t ht k f hw hk
      by_contra hf
      apply h
      have hf' : f = false := by simpa using hf
      refine List.any_eq_true.mpr ⟨(k, f), List.mem_filterMap.mpr ⟨t, ht, hw⟩, ?_⟩
      simp [hk, hf']
    · intro h h'
      obtain ⟨w, hw, hwe⟩ := List.any_eq_true.mp h'
      obtain ⟨t, ht, hwt⟩ := List.mem_filterMap.mp hw
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hwe
      have := h t ht w.1 w.2 hwt hwe.1
      rw [hwe.2] at this
      cases this
  rw [← hiff]
  unfold lifeClass
  simp only [hc1, hc2, Bool.false_eq_true, ↓reduceIte]
  by_cases h3 : ((P.threads.filterMap (waitOf P c)).any
      (fun w => decide (w.1 ≠ .asm) && !w.2)) = true
  · simp only [h3, ↓reduceIte, ne_eq, not_true_eq_false, Bool.true_eq_false, iff_self]
  · have h3' : ((P.threads.filterMap (waitOf P c)).any
        (fun w => decide (w.1 ≠ .asm) && !w.2)) = false := by simpa using h3
    simp only [h3', Bool.false_eq_true, ↓reduceIte, iff_true]
    split_ifs <;> simp

/-! ### Lemma 8 through the classifier -/

/-- A well-formed configuration whose graph is full under an adequate bound is not classified
`cut` (the proof of `lifeClass_ne_cut`, for any well-formed configuration). -/
theorem lifeClass_ne_cut_of_full (hn : adequateB P n = true) {c : Config} (hc : c.Wf)
    (hf : (lifeSys P n).toProgram.Full c.abs) : lifeClass P c ≠ .cut := by
  intro h
  unfold lifeClass at h
  by_cases h1 : P.threads.any (cutB P c) = true
  swap
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    split_ifs at h
  obtain ⟨t, ht, hcut⟩ := List.any_eq_true.mp h1
  apply lifeSys_noCut P hn hf ht
  rw [← Config.trace_eq c hc t]
  simp only [cutB, Bool.and_eq_true, Bool.not_eq_true', Option.isSome_iff_ne_none] at hcut
  exact hcut

/-- **Lemma 8 as designed**: in a full graph under an adequate bound whose class is not
`exploration` (a terminal-valid graph: not `cut` by `lifeClass_ne_cut_of_full`), a non-root
thread whose start-read returned `0` (a start wait) has no write of its lifecycle location,
in particular no start write, and its events are exactly that start-read `read (st t)` and a
`block` after it. -/
theorem lc_lemma8_terminal (hF : Frag P) {c : Config} (hc : c.Wf)
    (hE : (lifeSys P n).toProgram.Exec c.abs) (hfull : (lifeSys P n).toProgram.Full c.abs)
    (hn : adequateB P n = true) (hexp : lifeClass P c ≠ .exploration) {r0 : TEv}
    (hr0 : r0 ∈ c.abs.events)
    (hr : P.isRoot r0.tid = false) (h0i : r0.idx = 0) (hv : c.abs.ret r0 = some 0) :
    (∀ e ∈ c.abs.events, ∀ v, e.act ≠ .write (P.st r0.tid) v) ∧ r0.act = .read (P.st r0.tid) ∧
      ∃ b ∈ c.abs.events, b.tid = r0.tid ∧ b.idx = 1 ∧ b.act = .block ∧
        ∀ e ∈ c.abs.events, e.tid = r0.tid → e = r0 ∨ e = b := by
  have hG := hc.1
  have hcut : lifeClass P c ≠ .cut := lifeClass_ne_cut_of_full hn hc hfull
  have ht : r0.tid ∈ P.threads := (ev_tab hE hr0).2.2
  have hn2 : 2 ≤ n := by
    have := List.all_eq_true.mp hn r0.tid ht
    simp at this
    omega
  have hact : r0.act = .read (P.st r0.tid) := by
    obtain ⟨e1, -, -⟩ := ev_tab hE hr0
    rw [h0i, show c.abs.traceBefore r0.tid 0 = [] by simp [Graph.traceBefore],
      lifeTab_nil hr] at e1
    exact (Option.some.inj e1).symm
  obtain ⟨b, hb, hbt, hbi, hba⟩ := lc_lemma8_block hG hE hfull hn2 hr0 hr h0i hv
  have hev : ∀ e ∈ c.abs.events, e.tid = r0.tid → e = r0 ∨ e = b := by
    intro e he het
    have h1 := start_wait_events hG hE hr0 hr h0i hv he het
    rcases Nat.lt_or_ge e.idx 1 with h | h
    · exact Or.inl (hG.idx_inj e he r0 hr0 het (by omega))
    · exact Or.inr (hG.idx_inj e he b hb (het.trans hbt.symm) (by omega))
  -- the wait of the thread
  have hcnt : c.cnt r0.tid = 2 := by
    rw [Config.cnt_eq c hc]
    have h1 : 1 < c.abs.cnt r0.tid := (hG.exists_idx_iff _ _).mp ⟨b, hb, hbt, hbi⟩
    have h2 : ¬ 2 < c.abs.cnt r0.tid := by
      intro h2
      obtain ⟨e, he, het, hei⟩ := (hG.exists_idx_iff _ _).mpr h2
      rcases hev e he het with rfl | rfl <;> omega
    omega
  have hth : thEvents c r0.tid = [r0, b] := by
    unfold thEvents
    rw [hcnt]
    simp [List.range_succ, evAt_of_mem hc hr0 rfl h0i, evAt_of_mem hc hb hbt hbi]
  have hkind : kindOf P c r0.tid r0 = .startW := by
    simp [kindOf, hact, hF.st_not_lock r0.tid ht, hv]
  have hwait : waitOf P c r0.tid = some (.startW, finalB c r0) := by
    unfold waitOf
    rw [hth]
    simp [hba, hbi, evAt_of_mem hc hr0 rfl h0i, hkind]
  have hfin : finalB c r0 = true :=
    (lifeClass_not_exploration_iff hcut (lifeClass_ne_odd hF hc hE)).mp hexp r0.tid ht _ _
      hwait (by decide)
  rw [finalB_iff, hact] at hfin
  obtain ⟨hnw, -⟩ := lc_lemma8 hF hG hE hr0 hr h0i hv hfin
  exact ⟨hnw, hact, b, hb, hbt, hbi, hba, hev⟩

end Life

end Condpor
