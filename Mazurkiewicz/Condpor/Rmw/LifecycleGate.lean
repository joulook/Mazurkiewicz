import Mazurkiewicz.Condpor.Rmw.LifecycleSemLemmas
import Mazurkiewicz.Condpor.Rmw.LifecycleClass

/-!
# Thread lifecycle machine: the comparison, restated on graphs (LC2-b, part 1)

* `abs_eq_of_ser_eq`: two well-formed configurations with the same memory, no constraint
  evaluation and all events in the threads `ts` have the same graph iff the same `ser ts`.
* `mem_runsM`: every output of the merged enumeration from the initial frontier is the graph
  and the class of a maximal run (no claim that the key determines the future).
* `cmpM_spec`: what a `cmpM` theorem gives: every terminal-valid explorer configuration has
  the serialization and the class of a maximal run (one inclusion).
-/

namespace Condpor

namespace Life

namespace Sem

open Targets

variable {P : LProg}

/-! ### Serialization separates well-formed graphs -/

theorem mem_thEvents_iff {c : Config} (hc : c.Wf) {t : Tid} {e : TEv} :
    e ∈ thEvents c t ↔ e ∈ c.abs.events ∧ e.tid = t := by
  refine ⟨mem_of_thEvents, ?_⟩
  rintro ⟨he, rfl⟩
  unfold thEvents
  refine List.mem_filterMap.mpr ⟨e.idx, List.mem_range.mpr ?_, evAt_of_mem hc he rfl rfl⟩
  rw [Config.cnt_eq c hc]
  exact hc.1.idx_lt_cnt he

/-- A well-formed configuration without constraint evaluations has `pol = none`. -/
theorem pol_none_of_wf {c : Config} (hc : c.Wf) (hn : ∀ e ∈ c.abs.events, ¬ e.IsCons) (e : TEv) :
    c.pol e = none := by
  have h := hc.1.pol_isSome e
  cases hp : c.pol e with
  | none => rfl
  | some b =>
    have : (c.abs.pol e).isSome := by simp [Config.abs, hp]
    exact absurd (h.mp this).2 (hn e (h.mp this).1)

/-- The written locations of a serialized event list (as in `ser`). -/
def writeLocs (evs : List (List (TEv × Option Ev))) : List Loc :=
  (evs.flatten.filterMap (fun p => match p.1.act with
    | .write x _ => some x
    | _ => none)).dedup

theorem ser_eq (ts : List Tid) (c : Config) : ser ts c =
    (ts.map (fun t => (thEvents c t).map (fun e => (e, c.rf e))),
      (writeLocs (ts.map (fun t => (thEvents c t).map (fun e => (e, c.rf e))))).map
        (fun x => (x, c.co x))) := rfl

/-- **Equal serializations, equal graphs.** -/
theorem abs_eq_of_ser_eq {ts : List Tid} {c1 c2 : Config} (h1 : c1.Wf) (h2 : c2.Wf)
    (hm : c1.mem = c2.mem) (hp : c1.pol = c2.pol)
    (ht1 : ∀ e ∈ c1.abs.events, e.tid ∈ ts) (ht2 : ∀ e ∈ c2.abs.events, e.tid ∈ ts)
    (hs : ser ts c1 = ser ts c2) : c1.abs = c2.abs := by
  rw [ser_eq, ser_eq] at hs
  simp only [Prod.mk.injEq] at hs
  obtain ⟨he, hco⟩ := hs
  -- the per-thread lists agree
  have hth : ∀ t ∈ ts, thEvents c1 t = thEvents c2 t ∧
      ∀ e ∈ thEvents c1 t, c1.rf e = c2.rf e := by
    intro t ht
    have := congrArg (fun L => L.map (List.map Prod.fst)) he
    simp only [List.map_map] at this
    have h1' := List.map_inj_left.mp this t ht
    simp only [Function.comp_apply, List.map_map, Function.comp_def, List.map_id'] at h1'
    refine ⟨h1', fun e hm1 => ?_⟩
    have h2' := List.map_inj_left.mp he t ht
    have hm2 : (e, c1.rf e) ∈ (thEvents c2 t).map (fun e => (e, c2.rf e)) := by
      rw [← h2']; exact List.mem_map.mpr ⟨e, hm1, rfl⟩
    obtain ⟨e', -, he'⟩ := List.mem_map.mp hm2
    simp only [Prod.mk.injEq] at he'
    rw [← he'.2, he'.1]
  have hev : ∀ e, e ∈ c1.abs.events ↔ e ∈ c2.abs.events := by
    intro e
    constructor
    · intro h
      have hm1 := (mem_thEvents_iff h1).mpr ⟨h, rfl⟩
      rw [(hth e.tid (ht1 e h)).1] at hm1
      exact ((mem_thEvents_iff h2).mp hm1).1
    · intro h
      have hm1 := (mem_thEvents_iff h2).mpr ⟨h, rfl⟩
      rw [← (hth e.tid (ht2 e h)).1] at hm1
      exact ((mem_thEvents_iff h1).mp hm1).1
  have hevs : c1.abs.events = c2.abs.events := Finset.ext hev
  have hrf : c1.rf = c2.rf := by
    funext e
    by_cases h : e ∈ c1.abs.events
    · exact (hth e.tid (ht1 e h)).2 e ((mem_thEvents_iff h1).mpr ⟨h, rfl⟩)
    · have e1 := h1.1.rf_none e (Or.inl h)
      have e2 := h2.1.rf_none e (Or.inl (by rwa [← hev]))
      simpa [Config.abs] using e1.trans e2.symm
  -- coherence
  have hco' : c1.co = c2.co := by
    funext x
    have hx : ∀ c : Config, c.Wf → (∀ e ∈ c.abs.events, e.tid ∈ ts) → c.co x ≠ [] →
        x ∈ writeLocs (ts.map (fun t => (thEvents c t).map (fun e => (e, c.rf e)))) := by
      intro c hc hct hne
      obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨hwe, v, hwa⟩ := (hc.1.co_mem x w).mp hw
      rw [writeLocs, List.mem_dedup, List.mem_filterMap]
      refine ⟨(w, c.rf w), ?_, by simp [hwa]⟩
      rw [List.mem_flatten]
      exact ⟨_, List.mem_map.mpr ⟨w.tid, hct w hwe, rfl⟩, List.mem_map.mpr
        ⟨w, (mem_thEvents_iff hc).mpr ⟨hwe, rfl⟩, rfl⟩⟩
    rw [he] at hco
    by_cases hx1 : x ∈ writeLocs (ts.map (fun t => (thEvents c2 t).map (fun e => (e, c2.rf e))))
    · have := List.map_inj_left.mp hco x hx1
      simpa using this
    · have e1 : c1.co x = [] := by
        by_contra hne; exact hx1 (he ▸ hx c1 h1 ht1 hne)
      have e2 : c2.co x = [] := by
        by_contra hne; exact hx1 (hx c2 h2 ht2 hne)
      rw [e1, e2]
  apply Graph.ext
  · exact hm
  · exact hevs
  · exact hrf
  · exact hco'
  · exact hp

/-! ### Provenance of the merged enumeration -/

theorem Steps.snoc {s s1 s2 : MState} {rs : List Occ} {o : Occ} (h : Steps P s rs s1)
    (h2 : Step P s1 o s2) : Steps P s (rs ++ [o]) s2 := by
  induction h with
  | nil s => exact .cons h2 (.nil _)
  | cons h _ ih => exact .cons h (ih h2)

theorem mem_foldl_dedup {l : List (MState × GB)} {acc : List (MState × GB) × List
    (Ser × List (Status × Bool × List TOp) × List (Option Tid × ℕ × Val))} {p : MState × GB}
    (h : p ∈ (l.foldl (fun (acc : List (MState × GB) × List _) p =>
      let k := keyOf P p.1 p.2
      if k ∈ acc.2 then acc else (p :: acc.1, k :: acc.2)) acc).1) : p ∈ acc.1 ∨ p ∈ l := by
  induction l generalizing acc with
  | nil => exact Or.inl h
  | cons a l ih =>
    rcases ih h with h | h
    · simp only at h
      split_ifs at h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr List.mem_cons_self
        · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_dedupKey {l : List (MState × GB)} {p : MState × GB} (h : p ∈ dedupKey P l) :
    p ∈ l := by
  rcases mem_foldl_dedup h with h | h
  · simp at h
  · exact h

/-- **Provenance of `runsM`**: from a frontier of pairs reached by runs, every output is the
graph and the class of a maximal run. -/
theorem mem_runsM {f : ℕ} {fr : List (MState × GB)}
    (hfr : ∀ p ∈ fr, ∃ rs, Steps P (MState.init P) rs p.1 ∧ p.2 = rs.foldl (emit P) GB.empty)
    {x : Config × MCls} (h : x ∈ runsM P f fr) :
    ∃ rs s, MaxRun P rs s ∧ x = (runCfg P rs s, mclass P s) := by
  induction f generalizing fr with
  | zero => simp [runsM] at h
  | succ f ih =>
    unfold runsM at h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
      obtain ⟨hp1, hp2⟩ := List.mem_filter.mp hp
      obtain ⟨rs, hr, hg⟩ := hfr p hp1
      refine ⟨rs, p.1, ⟨hr, maximal_iff.mpr (List.isEmpty_iff.mp hp2)⟩, ?_⟩
      simp [runCfg, hg]
    · refine ih ?_ h
      intro q hq
      obtain ⟨p, hp, hq⟩ := List.mem_flatMap.mp (mem_dedupKey hq)
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hq
      obtain ⟨rs, hr, hg⟩ := hfr p hp
      exact ⟨rs ++ [o], hr.snoc ⟨mem_enabledL.mp ho, rfl⟩, by simp [hg]⟩

theorem mem_machSideM {x : Ser × LCls} (h : x ∈ machSideM P) :
    ∃ rs s, MaxRun P rs s ∧ x = (ser P.threads (runCfg P rs s), (mclass P s).toL) := by
  unfold machSideM at h
  rw [List.mem_dedup] at h
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
  obtain ⟨rs, s, hr, rfl⟩ := mem_runsM (fun p hp => by
    simp only [List.mem_singleton] at hp
    exact ⟨[], hp ▸ .nil _, by simp [hp]⟩) hy
  exact ⟨rs, s, hr, rfl⟩

/-- **What a `cmpM` theorem gives**: every terminal-valid configuration of the explorer has
the serialization and the class of the graph of a maximal run. -/
theorem cmpM_spec {n : ℕ} (h : (cmpM P n).1 = true) :
    ∀ c ∈ exploreCfgAtF (lifeSys P n) n, termValid P c = true → ∃ rs s, MaxRun P rs s ∧
      ser P.threads (runCfg P rs s) = ser P.threads c ∧ (mclass P s).toL = lifeClass P c := by
  simp only [cmpM, sameSet, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  intro c hc hv
  have hl : (ser P.threads c, lifeClass P c) ∈ lifeSide P n :=
    List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, hv⟩, rfl⟩
  obtain ⟨rs, s, hr, he⟩ := mem_machSideM (h.2 _ hl)
  simp only [Prod.mk.injEq] at he
  exact ⟨rs, s, hr, he.1.symm, he.2.symm⟩

end Sem

end Life

end Condpor
