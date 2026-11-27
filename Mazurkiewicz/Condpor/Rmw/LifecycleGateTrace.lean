import Mazurkiewicz.Condpor.Rmw.LifecycleGate1

/-!
# Gate clause 1: `Exec` and `Full` reduced to the emitted traces (LC2-b, part 4)

For an `Ok` builder, the events of thread `t` in time order are `thr g t` (their indices are
`0, 1, …`), the values they return are `tr P g t`, and the trace of `t` in the graph before
index `i` is `(tr P g t).take i` (`traceBefore_eq`). Hence:

* `exec_of_execT`: the graph is an execution of `lifeSys P n` iff every event of `thr g t`
  carries the compiled step after the values of the earlier events (`ExecT`);
* `full_of_tr`: it is full iff every thread has no compiled step after `tr P g t`;
* `ExecT.push`: `ExecT` survives adding an event whose label is the compiled step.

`G1Sim` (stated, not proved) is what remains of `G1Exec` and `G1Full`: the final builder of
a maximal run satisfies `ExecT` and no thread has a next compiled step.
`g1Exec_full_of_sim : G1Sim → G1Exec ∧ G1Full`.
-/

namespace Condpor

namespace Life

namespace Sem

open List

variable {P : LProg}

/-- The events of thread `t`, in time order. -/
def thr (g : GB) (t : Tid) : List TEv := g.L.filter (fun e => decide (e.tid = t))

/-- The value of a write for location `x`, with the initial memory `lifeMem P`. -/
def valE (P : LProg) (x : Loc) : Ev → Val
  | .init => lifeMem P x
  | .th w => match w.act with
    | .write _ v => v
    | _ => 0

/-- The value returned by an event of the builder. -/
def retG (P : LProg) (g : GB) (e : TEv) : Option Val :=
  match e.act with
  | .read x => (g.rf e).map (valE P x)
  | _ => none

/-- The values returned by the events of thread `t`, in time order. -/
def tr (P : LProg) (g : GB) (t : Tid) : List (Option Val) := (thr g t).map (retG P g)

theorem ret_eq (g : GB) (e : TEv) : (g.toCfg P).abs.ret e = retG P g e := by
  have hv : ∀ x, (g.toCfg P).abs.valAt x = valE P x := fun x => by funext w; cases w <;> rfl
  unfold Graph.ret retG
  cases e.act with
  | read x => exact congrArg (fun f => Option.map f (g.rf e)) (hv x)
  | cons φ => simp [GB.toCfg, Config.abs]
  | _ => rfl

theorem GB.Ok.thr_length {g : GB} (hg : g.Ok) (t : Tid) : (thr g t).length = g.cnt t := by
  have := congrArg List.length (hg.thrIdx t)
  simpa [thr] using this

theorem GB.Ok.thr_idx {g : GB} (hg : g.Ok) {t : Tid} {j : ℕ} (h : j < (thr g t).length) :
    ((thr g t)[j]).idx = j := by
  have h1 := hg.thrIdx t
  have h2 : ((thr g t).map TEv.idx)[j]'(by simpa using h) = j := by
    unfold thr; simp only [h1, getElem_range]
  simpa using h2

theorem GB.Ok.thr_mem {g : GB} {t : Tid} {j : ℕ} (h : j < (thr g t).length) :
    (thr g t)[j] ∈ g.L ∧ ((thr g t)[j]).tid = t := by
  have h1 : (thr g t)[j] ∈ g.L.filter (fun e => decide (e.tid = t)) := getElem_mem h
  have h2 := mem_filter.mp h1
  exact ⟨h2.1, by simpa using h2.2⟩

theorem GB.Ok.cnt_eq {g : GB} (hg : g.Ok) (t : Tid) : (g.toCfg P).abs.cnt t = g.cnt t := by
  have hw := (hg.wf P).1
  have key : ∀ i, i < (g.toCfg P).abs.cnt t ↔ i < g.cnt t := by
    intro i
    rw [← hw.exists_idx_iff t i]
    constructor
    · rintro ⟨e, he, rfl, rfl⟩
      exact hg.lt_cnt e ((GB.mem_events P).mp he)
    · intro hi
      obtain ⟨e, he, h1, h2⟩ := hg.present t i hi
      exact ⟨e, (GB.mem_events P).mpr he, h1, h2⟩
  apply Nat.le_antisymm
  · by_contra hc; exact absurd ((key _).mp (by omega)) (lt_irrefl _)
  · by_contra hc; exact absurd ((key _).mpr (by omega)) (lt_irrefl _)

theorem GB.Ok.evAt_thr {g : GB} (hg : g.Ok) {t : Tid} {j : ℕ} (h : j < (thr g t).length) :
    (g.toCfg P).abs.evAt t j = some (thr g t)[j] := by
  have hw := (hg.wf P).1
  obtain ⟨hm, ht⟩ := GB.Ok.thr_mem h
  have := Graph.evAt_eq_some_of_inj hw.idx_inj ((GB.mem_events P).mpr hm)
  rwa [ht, hg.thr_idx h] at this

/-- The trace of thread `t` in the graph before index `i` is the prefix of `tr`. -/
theorem GB.Ok.traceBefore_eq {g : GB} (hg : g.Ok) {t : Tid} {i : ℕ}
    (hi : i ≤ (thr g t).length) :
    (g.toCfg P).abs.traceBefore t i = (tr P g t).take i := by
  unfold Graph.traceBefore tr
  apply List.ext_getElem
  · simp; omega
  · intro j h1 h2
    simp only [length_map, length_range] at h1
    simp only [getElem_map, getElem_range, getElem_take]
    rw [hg.evAt_thr (by omega)]
    simp [ret_eq]

/-- Every event of thread `t` carries the compiled step after the earlier values. -/
def ExecT (P : LProg) (n : ℕ) (g : GB) : Prop :=
  ∀ t j (h : j < (thr g t).length),
    (lifeSys P n).toProgram.step t ((tr P g t).take j) = some ((thr g t)[j]).act

theorem GB.Ok.thr_of_mem (P : LProg) {g : GB} (hg : g.Ok) {e : TEv} (he : e ∈ g.L) :
    ∃ h : e.idx < (thr g e.tid).length, (thr g e.tid)[e.idx] = e := by
  have hl : e.idx < (thr g e.tid).length := by rw [hg.thr_length]; exact hg.lt_cnt e he
  refine ⟨hl, ?_⟩
  have hw := (hg.wf P).1
  obtain ⟨hm, ht⟩ := GB.Ok.thr_mem hl
  exact hw.idx_inj _ ((GB.mem_events P).mpr hm) _ ((GB.mem_events P).mpr he) ht
    (hg.thr_idx hl)

theorem exec_of_execT {g : GB} (hg : g.Ok) {n : ℕ} (h : ExecT P n g) :
    (lifeSys P n).toProgram.Exec (g.toCfg P).abs := by
  refine ⟨rfl, ?_⟩
  intro e he
  rw [GB.mem_events] at he
  obtain ⟨hl, hthr⟩ := hg.thr_of_mem P he
  rw [hg.traceBefore_eq hl.le]
  have := h e.tid e.idx hl
  rw [hthr] at this
  exact this

theorem full_of_tr {g : GB} (hg : g.Ok) {n : ℕ}
    (h : ∀ t ∈ P.threads, (lifeSys P n).toProgram.step t (tr P g t) = none) :
    (lifeSys P n).toProgram.Full (g.toCfg P).abs := by
  rw [Program.full_iff]
  intro t ht
  rw [Graph.trace, hg.cnt_eq, ← hg.thr_length, hg.traceBefore_eq le_rfl,
    take_of_length_le (by simp [tr])]
  exact h t ht

/-! ### `ExecT` under adding an event -/

theorem thr_append {g g' : GB} {e : TEv} (hL : g'.L = g.L ++ [e]) (t : Tid) :
    thr g' t = thr g t ++ (if e.tid = t then [e] else []) := by
  unfold thr; rw [hL, filter_append]; split_ifs with h <;> simp [h]

/-- `ExecT` after adding the event `e` of thread `t` with the compiled step as label, when
the old events return the same values. -/
theorem ExecT.push {n : ℕ} {g g' : GB} {t : Tid} {a : Act} (h : ExecT P n g)
    (hL : g'.L = g.L ++ [g.ev t a]) (hret : ∀ e ∈ g.L, retG P g' e = retG P g e)
    (hs : (lifeSys P n).toProgram.step t (tr P g t) = some a) : ExecT P n g' := by
  have htr : ∀ t', tr P g' t' = tr P g t' ++
      (if (g.ev t a).tid = t' then [retG P g' (g.ev t a)] else []) := by
    intro t'
    unfold tr
    rw [thr_append hL, map_append]
    congr 1
    · exact map_congr_left (fun e he => hret e (mem_filter.mp he).1)
    · split_ifs <;> rfl
  intro t' j hj
  have hth := thr_append hL t'
  have hlen : (tr P g t').length = (thr g t').length := by simp [tr]
  rw [getElem_of_eq hth, htr]
  by_cases hjl : j < (thr g t').length
  · rw [getElem_append_left hjl, take_append_of_le_length (by omega)]
    exact h t' j hjl
  · have ht' : (g.ev t a).tid = t' := by
      by_contra hne; rw [hth] at hj; simp [hne] at hj; omega
    have hj' : j = (thr g t').length := by rw [hth] at hj; simp [ht'] at hj; omega
    subst hj'
    simp only [ht', ↓reduceIte]
    rw [getElem_append_right (le_refl _)]
    simp only [Nat.sub_self, getElem_singleton]
    rw [← hlen, take_left' rfl]
    simp only [GB.ev] at ht'
    subst ht'
    exact hs

/-! ### What remains of `G1Exec` and `G1Full` -/

/-- Remaining: the final builder of a maximal run of a fragment program satisfies `ExecT`,
and no thread has a next compiled step after its values. -/
def G1Sim : Prop :=
  ∀ (P : LProg) (n : ℕ), fragB P = true → adequateB P n = true → ∀ rs s, MaxRun P rs s →
    ExecT P n (finalize P (rs.foldl (emit P) GB.empty) s) ∧
      ∀ t ∈ P.threads,
        (lifeSys P n).toProgram.step t (tr P (finalize P (rs.foldl (emit P) GB.empty) s) t) = none

theorem g1Exec_full_of_sim (h : G1Sim) : G1Exec ∧ G1Full := by
  constructor
  · intro P n hf hn rs s hr
    exact exec_of_execT (runCfg_ok (frag_of_fragB hf) hr) (h P n hf hn rs s hr).1
  · intro P n hf hn rs s hr
    exact full_of_tr (runCfg_ok (frag_of_fragB hf) hr) (h P n hf hn rs s hr).2

end Sem

end Life

end Condpor
