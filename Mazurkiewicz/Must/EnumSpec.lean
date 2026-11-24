import Mazurkiewicz.Must.AlgSound
import Mazurkiewicz.Must.Enum

/-!
# The enumerator lists exactly `⟦P⟧` (`mem_semEnum_iff`)

Plan: the obligation deferred from M2 (`Enum.lean` docstring), moved to the M4 row by the M2 and
M3 reviews. For a Boolean consistency `cons` (M2's `Program.Sem cons`; no model needed).

* `lvl P n`: the `n`-th level of the enumeration (`lvl 0 = [init]`, each level the
  deduplicated one-event extensions of the previous one). Every enumerated configuration has
  `Supp` and an order listing its events (`Good`).
* `mem_lvl_of_exec`: every well-formed execution of `P` with `n` events is, up to its insertion
  order, a configuration of `lvl P n` (induction on `n`, removing a `porf`-maximal event:
  `Graph.Wf.remove_max_*`, `AlgSound.lean`).
* `mem_semEnum_iff`: with the bound `∀ H, H.Wf → P.Exec H → H.events.card ≤ levels`, for every
  graph `G` with `Supp`, `(∃ c ∈ semEnum cons P levels, c.G.key = G.key) ↔ P.Sem cons G`.
* `bound_of_not_truncated` and `mem_semEnum_iff'`: the same with the hypothesis
  `semTruncated P levels = false`, the flag checked by the computations of M2.
-/

namespace Must

open Graph

variable {Q : Type} [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)]

/-- An enumerated configuration: `rf`, `nd` vanish outside the events, and the order lists
exactly the events. -/
def Config.Good (c : Config Q) : Prop := c.G.Supp ∧ ∀ x, x ∈ c.order ↔ x ∈ c.G.events

omit [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
theorem Config.good_init : (Config.init : Config Q).Good :=
  ⟨fun e _ => by simp [Config.init, Graph.empty], by simp [Config.init, Graph.empty]⟩

omit [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
theorem Config.Good.add {c : Config Q} (h : c.Good) (e : Ev Q) (src : Option (Src Q))
    (out : Option Val) : (c.add e src out).Good := by
  refine ⟨h.1.add e src out, fun x => ?_⟩
  simp only [Config.add, List.mem_append, List.mem_singleton, add_events, Finset.mem_insert, h.2]
  exact or_comm

/-! ### One-event extensions -/

/-- An extension adds one event. -/
theorem exists_of_mem_extendE {P : Program Q} {c c' : Config Q} (h : c' ∈ extendE P c) :
    ∃ e src out, c' = c.add e src out := by
  unfold extendE at h
  obtain ⟨t, -, h⟩ := List.mem_flatMap.mp h
  split at h
  · simp at h
  · split at h
    · obtain ⟨v, -, rfl⟩ := List.mem_map.mp h
      exact ⟨_, _, _, rfl⟩
    · obtain ⟨x, -, h⟩ := List.mem_filterMap.mp h
      dsimp only at h
      split_ifs at h
      cases h
      exact ⟨_, _, _, rfl⟩
    · rw [List.mem_singleton] at h
      exact ⟨_, _, _, h⟩

theorem Config.Good.extendE {P : Program Q} {c c' : Config Q} (h : c.Good)
    (hc : c' ∈ extendE P c) : c'.Good := by
  obtain ⟨e, src, out, rfl⟩ := exists_of_mem_extendE hc
  exact h.add e src out

/-! ### Deduplication -/

/-- The step of `dedupKey`. -/
abbrev dedupStep (acc : List (Config Q)) (c : Config Q) : List (Config Q) :=
  if acc.any (fun c' => decide (c'.G.key = c.G.key)) then acc else acc ++ [c]

omit [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
theorem mem_foldl_dedup {x : Config Q} :
    ∀ (l acc : List (Config Q)), x ∈ l.foldl dedupStep acc → x ∈ acc ∨ x ∈ l
  | [], _, h => Or.inl h
  | c :: l, acc, h => by
    rcases mem_foldl_dedup l _ h with h | h
    · unfold dedupStep at h
      split_ifs at h
      · exact Or.inl h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_singleton.mp h ▸ List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ h)

omit [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
theorem exists_foldl_dedup :
    ∀ (l acc : List (Config Q)) (x : Config Q), x ∈ acc ∨ x ∈ l →
      ∃ y ∈ l.foldl dedupStep acc, y.G.key = x.G.key
  | [], _, x, h => ⟨x, by simpa using h, rfl⟩
  | c :: l, acc, x, h => by
    have hsub : ∀ y ∈ acc, y ∈ dedupStep acc c := fun y hy => by
      unfold dedupStep
      split_ifs
      · exact hy
      · exact List.mem_append_left _ hy
    rcases h with h | h
    · exact exists_foldl_dedup l _ x (Or.inl (hsub x h))
    · rcases List.mem_cons.mp h with rfl | h
      · by_cases ha : acc.any (fun c' => decide (c'.G.key = x.G.key)) = true
        · obtain ⟨y, hy, hk⟩ := List.any_eq_true.mp ha
          obtain ⟨z, hz, hzk⟩ := exists_foldl_dedup l _ y (Or.inl (hsub y hy))
          exact ⟨z, hz, hzk.trans (of_decide_eq_true hk)⟩
        · refine exists_foldl_dedup l _ x (Or.inl ?_)
          simp only [dedupStep, ha, Bool.false_eq_true, ↓reduceIte]
          exact List.mem_append_right _ (List.mem_singleton_self _)
      · exact exists_foldl_dedup l _ x (Or.inr h)

omit [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
theorem mem_of_mem_dedupKey {l : List (Config Q)} {x : Config Q} (h : x ∈ dedupKey l) :
    x ∈ l := by
  unfold dedupKey at h
  simpa using mem_foldl_dedup l [] h

omit [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
theorem exists_mem_dedupKey {l : List (Config Q)} {x : Config Q} (h : x ∈ l) :
    ∃ y ∈ dedupKey l, y.G.key = x.G.key :=
  exists_foldl_dedup l [] x (Or.inr h)

/-! ### Levels -/

/-- The levels of the enumeration. -/
def lvl (P : Program Q) : ℕ → List (Config Q)
  | 0 => [.init]
  | n + 1 => dedupKey ((lvl P n).flatMap (extendE P))

variable {P : Program Q}

theorem good_of_mem_flatMap {cur : List (Config Q)} (hcur : ∀ c ∈ cur, c.Good) {c : Config Q}
    (h : c ∈ dedupKey (cur.flatMap (extendE P))) : c.Good := by
  obtain ⟨d, hd, hc⟩ := List.mem_flatMap.mp (mem_of_mem_dedupKey h)
  exact (hcur d hd).extendE hc

theorem good_of_mem_lvl : ∀ {n} {c : Config Q}, c ∈ lvl P n → c.Good
  | 0, c, h => by
    rw [lvl, List.mem_singleton] at h
    exact h ▸ Config.good_init
  | _ + 1, _, h => good_of_mem_flatMap (fun _ hd => good_of_mem_lvl hd) h

theorem good_of_mem_allExecs : ∀ (n : ℕ) (cur : List (Config Q)), (∀ c ∈ cur, c.Good) →
    ∀ c ∈ allExecs P n cur, c.Good
  | 0, cur, hcur, c, h => hcur c h
  | n + 1, cur, hcur, c, h => by
    unfold allExecs at h
    dsimp only at h
    split_ifs at h
    · exact hcur c h
    · rcases List.mem_append.mp h with h | h
      · exact hcur c h
      · exact good_of_mem_allExecs n _ (fun _ hd => good_of_mem_flatMap hcur hd) c h

theorem lvl_nil {k : ℕ} (h : lvl P k = []) : ∀ m, lvl P (k + m) = []
  | 0 => h
  | m + 1 => by
    rw [← Nat.add_assoc, lvl, lvl_nil h m]
    rfl

/-- The enumeration from level `i` contains the next `n` levels. -/
theorem mem_allExecs_of_mem_lvl : ∀ (n i j : ℕ), j ≤ n → ∀ c ∈ lvl P (i + j),
    c ∈ allExecs P n (lvl P i)
  | 0, i, j, hj, c, h => by
    rw [Nat.le_zero.mp hj] at h
    exact h
  | n + 1, i, j, hj, c, h => by
    unfold allExecs
    dsimp only
    have hnx : dedupKey ((lvl P i).flatMap (extendE P)) = lvl P (i + 1) := rfl
    rw [hnx]
    rcases j with _ | j
    · split_ifs
      · exact h
      · exact List.mem_append_left _ h
    · have h' : c ∈ lvl P (i + 1 + j) := by rwa [Nat.add_right_comm, Nat.add_assoc]
      split_ifs with he
      · rw [lvl_nil (List.isEmpty_iff.mp he) j] at h'
        simp at h'
      · exact List.mem_append_right _ (mem_allExecs_of_mem_lvl n (i + 1) j (by omega) c h')

/-- The frontier is the last level. -/
theorem frontier_eq : ∀ (n i : ℕ), frontier P n (lvl P i) = lvl P (i + n)
  | 0, _ => rfl
  | n + 1, i => by
    unfold frontier
    dsimp only
    have hnx : dedupKey ((lvl P i).flatMap (extendE P)) = lvl P (i + 1) := rfl
    rw [hnx]
    split_ifs with he
    · rw [show i + (n + 1) = i + 1 + n by omega, lvl_nil (List.isEmpty_iff.mp he) n]
    · rw [frontier_eq n (i + 1), Nat.add_right_comm, Nat.add_assoc]

/-! ### Completeness of the levels -/

omit [DecidableEq Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
/-- A well-formed graph without events is the empty graph. -/
theorem Graph.Wf.eq_empty {G : Graph Q} (hG : G.Wf) (h : G.events = ∅) : G = Graph.empty :=
  hG.ext Graph.empty_wf (by rw [h]; rfl) (by simp [h]) (by simp [h])

/-- Extending the configuration of `G` without a `porf`-maximal event `m` by `m` with its source
and outcome is one of the enumerated extensions. -/
theorem mem_extendE_of_max {G : Graph Q} (hG : G.Wf) (hE : P.Exec G) {m : Ev Q}
    (hm : m ∈ G.events) (hmax : ∀ b, ¬ G.porfStep m b) {c : Config Q} (hc : c.Good)
    (hcG : c.G = G.remove {m}) : c.add m (G.rf m) (G.nd m) ∈ extendE P c := by
  have hnext : P.nextEv c.G m.tid = some m := hcG ▸ hG.nextEv_remove_max hE hm hmax
  have hback : c.G.add m (G.rf m) (G.nd m) = G := hcG ▸ hG.add_remove hm
  unfold extendE
  refine List.mem_flatMap.mpr ⟨m.tid, hG.tid_mem_threads hE hm, ?_⟩
  rw [hnext]
  simp only
  split
  next S hl =>
    have hN : m.IsND := by simp [Ev.IsND, hl, Lab.IsND]
    obtain ⟨v, hv⟩ := hG.exists_nd hm hN
    have hv' : v ∈ S := by simpa [Ev.ndSet, hl, Lab.ndSet] using hG.nd_mem m v hv
    rw [hG.rf_none (Or.inr (Lab.IsND.not_isRecv hN)), hv]
    exact List.mem_map.mpr ⟨v, mem_ndList.mpr hv', rfl⟩
  next a vals hl =>
    have hR : m.IsRecv := by simp [Ev.IsRecv, hl, Lab.IsRecv]
    obtain ⟨x, hx⟩ := hG.exists_rf hm hR
    have hnd : G.nd m = none := hG.nd_none (Or.inr (Lab.IsRecv.not_isND hR))
    rw [hx, hnd]
    have hwf : (c.add m (some x) none).G.WfD := by
      rw [wfD_iff ((hc.add m _ _).1)]
      change (c.G.add m (some x) none).Wf
      rw [← hx, ← hnd, hback]
      exact hG
    refine List.mem_filterMap.mpr ⟨x, ?_, by simp [hwf]⟩
    cases x with
    | bot => exact List.mem_append_right _ (List.mem_singleton_self _)
    | snd s =>
      refine List.mem_append_left _ (List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩)
      · have hsG := hG.rf_mem _ _ hx
        have hse : s ≠ m := by
          rintro rfl
          exact Lab.IsSend.not_isRecv (hG.rf_match _ _ hx).isSend hR
        refine (hc.2 s).mpr ?_
        rw [hcG]
        exact mem_remove_single.mpr ⟨hsG, hse⟩
      · exact decide_eq_true (hG.rf_match _ _ hx).isSend
  next l h1 h2 =>
    have hR : ¬ m.IsRecv := fun h => by
      obtain ⟨a, vals, h'⟩ := (Lab.isRecv_iff _).mp h
      exact h2 a vals h'
    have hN : ¬ m.IsND := fun h => by
      obtain ⟨S, h'⟩ := (Lab.isND_iff _).mp h
      exact h1 S h'
    rw [hG.rf_none (Or.inr hR), hG.nd_none (Or.inr hN)]
    exact List.mem_singleton_self _

/-- Every well-formed execution of `P` with `n` events is the graph of a configuration of the
`n`-th level. -/
theorem mem_lvl_of_exec : ∀ (n : ℕ) {G : Graph Q}, G.Wf → P.Exec G → G.events.card = n →
    ∃ c ∈ lvl P n, c.G = G
  | 0, G, hG, _, hn => ⟨.init, List.mem_singleton_self _,
      (hG.eq_empty (Finset.card_eq_zero.mp hn)).symm⟩
  | n + 1, G, hG, hE, hn => by
    have hne : G.events.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨m, hm, hmax⟩ := hG.exists_porf_max hne
    have hstep : ∀ b, ¬ G.porfStep m b := fun b hb =>
      hmax b (hG.mem_of_porfStep hb).2 (Relation.TransGen.single hb)
    have hcard : (G.remove {m}).events.card = n := by
      have : (G.remove {m}).events = G.events.erase m := by
        ext x
        rw [mem_remove_single, Finset.mem_erase]
        tauto
      rw [this, Finset.card_erase_of_mem hm, hn]
      rfl
    obtain ⟨c, hc, hcG⟩ := mem_lvl_of_exec n (hG.remove_max_wf hstep)
      (Graph.Wf.remove_max_exec hE hstep) hcard
    have hgood := good_of_mem_lvl hc
    have hext := mem_extendE_of_max hG hE hm hstep hgood hcG
    obtain ⟨y, hy, hk⟩ := exists_mem_dedupKey (List.mem_flatMap.mpr ⟨c, hc, hext⟩)
    refine ⟨y, hy, ?_⟩
    have hback : (c.add m (G.rf m) (G.nd m)).G = G := by
      change c.G.add m (G.rf m) (G.nd m) = G
      rw [hcG]
      exact hG.add_remove hm
    rw [← hback]
    exact (eq_iff_key (good_of_mem_lvl (n := n + 1) hy).1 (hgood.add _ _ _).1).mpr hk

omit [DecidableEq Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
/-- A well-formed execution with at least `k` events has a prefix with exactly `k` events that
is a well-formed execution. -/
theorem exists_exec_card (d k : ℕ) {G : Graph Q} (hG : G.Wf) (hE : P.Exec G)
    (hn : G.events.card = k + d) : ∃ G' : Graph Q, G'.Wf ∧ P.Exec G' ∧ G'.events.card = k := by
  classical
  induction d generalizing G with
  | zero => exact ⟨G, hG, hE, hn⟩
  | succ d ih =>
    have hne : G.events.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨m, hm, hmax⟩ := hG.exists_porf_max hne
    have hstep : ∀ b, ¬ G.porfStep m b := fun b hb =>
      hmax b (hG.mem_of_porfStep hb).2 (Relation.TransGen.single hb)
    have hcard : (G.remove {m}).events.card = k + d := by
      have : (G.remove {m}).events = G.events.erase m := by
        ext x
        rw [mem_remove_single, Finset.mem_erase]
        tauto
      rw [this, Finset.card_erase_of_mem hm, hn]
      rfl
    exact ih (hG.remove_max_wf hstep) (Graph.Wf.remove_max_exec hE hstep) hcard

/-! ### `mem_semEnum_iff` -/

/-- Soundness of the enumerator: an enumerated configuration is in `⟦P⟧`. -/
theorem sem_of_mem_semEnum {cons : Graph Q → Bool} {levels : ℕ} {c : Config Q}
    (h : c ∈ semEnum cons P levels) : P.Sem cons c.G := by
  unfold semEnum at h
  obtain ⟨h1, h2⟩ := List.mem_filter.mp h
  have hg := good_of_mem_allExecs levels [.init]
    (fun d hd => (List.mem_singleton.mp hd) ▸ Config.good_init) c h1
  exact (P.semD_iff cons hg.1).mp (of_decide_eq_true h2)

/-- `mem_semEnum_iff` (M2 obligation): with a bound on the number of events of the well-formed
executions of `P`, the enumerator lists exactly `⟦P⟧`, up to the insertion order. -/
theorem mem_semEnum_iff (cons : Graph Q → Bool) (levels : ℕ)
    (hb : ∀ H : Graph Q, H.Wf → P.Exec H → H.events.card ≤ levels) {G : Graph Q}
    (hS : G.Supp) :
    (∃ c ∈ semEnum cons P levels, c.G.key = G.key) ↔ P.Sem cons G := by
  constructor
  · rintro ⟨c, hc, hk⟩
    have hsem := sem_of_mem_semEnum hc
    rwa [(eq_iff_key hsem.1.supp hS).mpr hk] at hsem
  · intro hsem
    obtain ⟨c, hc, hcG⟩ := mem_lvl_of_exec G.events.card hsem.1 hsem.2.1 rfl
    have hall : c ∈ allExecs P levels [.init] :=
      mem_allExecs_of_mem_lvl levels 0 _ (hb G hsem.1 hsem.2.1) c (by rwa [Nat.zero_add])
    refine ⟨c, List.mem_filter.mpr ⟨hall, decide_eq_true ?_⟩, by rw [hcG]⟩
    rw [hcG]
    exact (P.semD_iff cons hS).mpr hsem

/-- If the enumeration is not truncated at `levels`, every well-formed execution of `P` has at
most `levels` events. -/
theorem bound_of_not_truncated {levels : ℕ} (ht : semTruncated P levels = false) :
    ∀ H : Graph Q, H.Wf → P.Exec H → H.events.card ≤ levels := by
  intro H hH hE
  by_contra hlt
  push Not at hlt
  obtain ⟨H', hH', hE', hc'⟩ := exists_exec_card (H.events.card - (levels + 1)) (levels + 1)
    hH hE (by omega)
  obtain ⟨c, hc, -⟩ := mem_lvl_of_exec (levels + 1) hH' hE' hc'
  have hne : ((lvl P levels).flatMap (extendE P)) ≠ [] := by
    intro h
    have : lvl P (levels + 1) = [] := by
      change dedupKey ((lvl P levels).flatMap (extendE P)) = []
      rw [h]
      rfl
    rw [this] at hc
    simp at hc
  unfold semTruncated at ht
  rw [show frontier P levels [.init] = lvl P levels by
    rw [show ([.init] : List (Config Q)) = lvl P 0 from rfl, frontier_eq, Nat.zero_add]] at ht
  simp only [Bool.not_eq_false', List.isEmpty_iff] at ht
  exact hne ht

/-- `mem_semEnum_iff` with the flag checked by the computations: if the enumeration is not
truncated at `levels`, it lists exactly `⟦P⟧`. -/
theorem mem_semEnum_iff' (cons : Graph Q → Bool) (levels : ℕ)
    (ht : semTruncated P levels = false) {G : Graph Q} (hS : G.Supp) :
    (∃ c ∈ semEnum cons P levels, c.G.key = G.key) ↔ P.Sem cons G :=
  mem_semEnum_iff cons levels (bound_of_not_truncated ht) hS

end Must

#print axioms Must.mem_lvl_of_exec
#print axioms Must.sem_of_mem_semEnum
#print axioms Must.mem_semEnum_iff
#print axioms Must.bound_of_not_truncated
#print axioms Must.mem_semEnum_iff'
