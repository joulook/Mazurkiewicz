import Mazurkiewicz.Condpor.Explore
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Permutation
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

/-!
# The counts of Section 2.1

The paper's motivating example: `n` concurrent pushes to a timestamped stack,
followed by a pop. ConDpor explores `2^(n-1)` executions, also with `k`
pushes per thread.

The paper gives no program text. The model here (`tsProg n k`, `n, k ≥ 1`):

* thread `i`, `1 ≤ i ≤ n`, generates `k` symbolic timestamps, one for each
  push; the stack itself is not modelled (the paper assumes no contention on
  it);
* thread `0`, the pop, evaluates `n - 1` constraints `φ_2, …, φ_n`; `φ_i`
  says that the top timestamp of thread `i` is larger than the top timestamps
  of the threads `1, …, i - 1` (the scan for the largest timestamp; a scan
  would compare with the current maximum, a formula that depends on the
  earlier outcomes; `φ_i` is the same condition without that dependence).
  The programs have no join, so the pop is a thread; it has no memory access,
  so its position relative to the pushes does not matter;
* in the semantics `tsSem`, an assignment gives each thread an increasing
  sequence of timestamps ("symbolic values in the same thread are linearly
  ordered").

`ts_executions`: the program has exactly `2^(n-1)` full consistent
executions; `ts_explore_length`: so the explorer of Algorithm 1 lists
`2^(n-1)` graphs.
-/

namespace Condpor

open Program

/-! ### The program -/

/-- The action of thread `t` at index `i`. The formula of the comparison for
thread `i + 2` has code `i + 2`; the symbol of push `i` of thread `t` has code
`t * (k + 1) + i`. -/
def tsAct (n k : ℕ) (t i : ℕ) : Option Act :=
  if t = 0 then (if i < n - 1 then some (.cons (i + 2)) else none)
  else if t ≤ n then (if i < k then some (.gen (t * (k + 1) + i)) else none)
  else none

/-- `n` threads with `k` pushes each, and the pop. -/
def tsProg (n k : ℕ) : Program where
  threads := List.range (n + 1)
  threads_nodup := List.nodup_range
  step := fun t u => tsAct n k t u.length
  mem := fun _ => 0
  step_none := by
    intro (t : ℕ) ht
    have h1 : n + 1 ≤ t := by simpa using ht
    have h2 : ¬ t = 0 := by omega
    have h3 : ¬ t ≤ n := by omega
    change tsAct n k t 0 = none
    simp [tsAct, h2, h3]
  stop := by
    intro t u h
    exfalso
    unfold tsAct at h
    rcases h with h | h <;> split_ifs at h <;> cases h

theorem tsProg_bounded (n k : ℕ) : (tsProg n k).Bounded (max k (n - 1)) := by
  intro t u hu
  have h1 : ¬ u.length < n - 1 := by omega
  have h2 : ¬ u.length < k := by omega
  simp [tsProg, tsAct, h1, h2]

theorem tsAct_not_rw {n k t i : ℕ} {a : Act} (h : tsAct n k t i = some a) :
    ¬ a.IsRead ∧ ¬ a.IsWrite ∧ (a.IsCons ↔ t = 0) := by
  unfold tsAct at h
  split_ifs at h with h1 h2 h3 h4
  · cases h
    simp [Act.IsRead, Act.IsWrite, Act.IsCons, h1]
  · cases h
    simp [Act.IsRead, Act.IsWrite, Act.IsCons, h1]

/-! ### The semantics -/

/-- Assignments: for every thread an increasing sequence of timestamps
(numbered from `0`; the top one after `k` pushes has number `k - 1`). The
formula with code `i` holds iff the top timestamp of thread `i` is larger than
those of the threads `1, …, i - 1`. The formulas speak of these per-thread
timestamps directly: the codes of the generated symbols are not decoded. -/
def tsSem (k : ℕ) : Sem where
  Asg := {a : ℕ → ℕ → ℕ // ∀ i, StrictMono (a i)}
  inh := ⟨⟨fun _ j => j, fun _ => strictMono_id⟩⟩
  holds := fun a (φ : ℕ) => ∀ j : ℕ, 1 ≤ j → j < φ → a.1 j (k - 1) < a.1 φ (k - 1)

/-- S-1: every assignment of outcomes to the comparisons is satisfiable. -/
theorem tsSem_all_outcomes (k : ℕ) (b : ℕ → Bool) :
    ∃ a : (tsSem k).Asg, ∀ i : ℕ, 2 ≤ i → ((tsSem k).holds a i ↔ b i = true) := by
  let rank : ℕ → ℕ := fun i => if b i = true then i + 1 else 0
  have hrank : ∀ i, rank i ≤ i + 1 := by
    intro i
    simp only [rank]
    split_ifs <;> omega
  refine ⟨⟨fun i j => rank i + j, fun i x y h => Nat.add_lt_add_left h _⟩, fun i hi => ?_⟩
  constructor
  · intro h
    by_contra hb
    have h1 : rank 1 + (k - 1) < rank i + (k - 1) := h 1 le_rfl (by omega)
    have hr0 : rank i = 0 := by simp [rank, hb]
    omega
  · intro hb j _ hj
    have hri : rank i = i + 1 := by simp [rank, hb]
    have hrj := hrank j
    change rank j + (k - 1) < rank i + (k - 1)
    omega

/-! ### The executions -/

section Exec

variable (n k : ℕ)

/-- The events: thread `t` has the events that `tsAct` gives. -/
def tsEvents : Finset TEv :=
((Finset.range (n + 1)) ×ˢ (Finset.range (k + n))).biUnion
    (fun p => ((tsAct n k p.1 p.2).map (fun a => (⟨p.1, p.2, a⟩ : TEv))).toFinset)

theorem mem_tsEvents {e : TEv} : e ∈ tsEvents n k ↔ tsAct n k e.tid e.idx = some e.act := by
  simp only [tsEvents, Finset.mem_biUnion, Finset.mem_product, Finset.mem_range,
    Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Prod.exists]
  constructor
  · rintro ⟨t, i, -, a, ha, rfl⟩
    exact ha
  · intro h
    refine ⟨e.tid, e.idx, ?_, e.act, h, rfl⟩
    unfold tsAct at h
    split_ifs at h with h1 h2 h3 h4 <;> constructor <;> omega

/-- The graph with outcome `b i` for the comparison number `i`. -/
def tsGraph (b : Fin (n - 1) → Bool) : Graph where
  mem := fun _ => 0
  events := tsEvents n k
  rf := fun _ => none
  co := fun _ => []
  pol := fun e =>
    if h : e ∈ tsEvents n k ∧ e.tid = 0 ∧ e.idx < n - 1 then some (b ⟨e.idx, h.2.2⟩) else none

end Exec

variable {n k : ℕ}

theorem tsEvents_cons {e : TEv} (he : e ∈ tsEvents n k) :
    e.IsCons ↔ e.tid = 0 ∧ e.idx < n - 1 := by
  have h := (mem_tsEvents n k).mp he
  constructor
  · intro hc
    have ht := (tsAct_not_rw h).2.2.mp hc
    refine ⟨ht, ?_⟩
    unfold tsAct at h
    by_contra hlt
    simp only [ht, hlt, ↓reduceIte] at h
    cases h
  · rintro ⟨ht, -⟩
    exact (tsAct_not_rw h).2.2.mpr ht

theorem tsGraph_wf (b : Fin (n - 1) → Bool) : (tsGraph n k b).Wf where
  idx_inj := by
    intro e he e' he' ht hi
    have h1 := (mem_tsEvents n k).mp he
    have h2 := (mem_tsEvents n k).mp he'
    rw [ht, hi, h2] at h1
    obtain ⟨t, i, a⟩ := e
    obtain ⟨t', i', a'⟩ := e'
    simp only at ht hi h1
    subst ht hi
    cases h1
    rfl
  idx_contig := by
    intro e he i hi
    have h := (mem_tsEvents n k).mp he
    unfold tsAct at h
    split_ifs at h with h1 h2 h3 h4
    · exact ⟨⟨e.tid, i, .cons (i + 2)⟩, (mem_tsEvents n k).mpr (by
        simp [tsAct, h1, show i < n - 1 by omega]), rfl, rfl⟩
    · exact ⟨⟨e.tid, i, .gen (e.tid * (k + 1) + i)⟩, (mem_tsEvents n k).mpr (by
        simp [tsAct, h1, h3, show i < k by omega]), rfl, rfl⟩
  rf_read := by
    intro e he x hact
    have h := (mem_tsEvents n k).mp he
    exact absurd (by simp [hact, Act.IsRead]) (tsAct_not_rw h).1
  rf_none := fun _ _ => rfl
  co_mem := by
    intro x e
    constructor
    · intro h
      cases h
    · rintro ⟨he, v, hact⟩
      have h := (mem_tsEvents n k).mp he
      exact absurd (by simp [hact, Act.IsWrite]) (tsAct_not_rw h).2.1
  co_nodup := fun _ => List.nodup_nil
  pol_isSome := by
    intro e
    simp only [tsGraph]
    constructor
    · intro h
      split_ifs at h with h1
      · exact ⟨h1.1, (tsEvents_cons h1.1).mpr h1.2⟩
      · cases h
    · rintro ⟨he, hc⟩
      simp [he, (tsEvents_cons he).mp hc]

/-- A graph without reads and writes is sequentially consistent. -/
theorem sc_of_no_rw {G : Graph} (hrf : ∀ e, G.rf e = none) (hco : ∀ x, G.co x = []) :
    SC.cons G := by
  have hstep : ∀ a b, G.scStep a b → G.po a b := by
    rintro a b (h | ⟨e, -, -, h⟩ | h | ⟨e, e', x, -, -, -, -, h, -⟩)
    · exact h
    · rw [hrf] at h
      cases h
    · cases a <;> cases b <;> simp [Graph.coRel, hco, List.Before] at h
    · rw [hco] at h
      cases h
  let rk : Ev → ℕ := fun a => match a with | .init => 0 | .th e => e.idx + 1
  have hrk : ∀ a b, G.po a b → rk a < rk b := by
    intro a b h
    cases a with
    | init =>
      cases b with
      | init => exact absurd h (by simp [Graph.po])
      | th e => exact Nat.succ_pos _
    | th e =>
      cases b with
      | init => exact absurd h (by simp [Graph.po])
      | th e' => exact Nat.succ_lt_succ h.2.2.2
  have htr : ∀ a b, Relation.TransGen G.scStep a b → rk a < rk b := by
    intro a b h
    induction h with
    | single h => exact hrk _ _ (hstep _ _ h)
    | tail _ h ih => exact lt_trans ih (hrk _ _ (hstep _ _ h))
  intro a ha
  exact lt_irrefl _ (htr a a ha)

theorem tsAct_mono {t i i' : ℕ} {a : Act} (h : tsAct n k t i = some a) (hi : i' ≤ i) :
    ∃ a', tsAct n k t i' = some a' := by
  unfold tsAct at h ⊢
  split_ifs at h with h1 h2 h3 h4
  · exact ⟨.cons (i' + 2), by simp [h1, show i' < n - 1 by omega]⟩
  · exact ⟨.gen (t * (k + 1) + i'), by simp [h1, h3, show i' < k by omega]⟩

theorem tsGraph_exec (b : Fin (n - 1) → Bool) : (tsProg n k).Exec (tsGraph n k b) := by
  refine ⟨rfl, fun e he => ?_⟩
  change tsAct n k e.tid (Graph.traceBefore _ e.tid e.idx).length = some e.act
  rw [show (Graph.traceBefore (tsGraph n k b) e.tid e.idx).length = e.idx by
    simp [Graph.traceBefore]]
  exact (mem_tsEvents n k).mp he

theorem tsGraph_full (b : Fin (n - 1) → Bool) : (tsProg n k).Full (tsGraph n k b) := by
  rw [full_iff]
  intro t _
  change tsAct n k t (Graph.trace _ t).length = none
  rw [Graph.trace_length]
  by_contra hne
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hne
  have he : (⟨t, (tsGraph n k b).cnt t, a⟩ : TEv) ∈ (tsGraph n k b).events :=
    (mem_tsEvents n k).mpr ha
  exact lt_irrefl _ ((tsGraph_wf b).idx_lt_cnt he)

theorem tsGraph_cons (b : Fin (n - 1) → Bool) :
    (SC.sym (tsSem k).solver).cons (tsGraph n k b) := by
  refine Model.sym_cons_iff.mpr ⟨sc_of_no_rw (fun _ => rfl) (fun _ => rfl), ?_⟩
  obtain ⟨m, hm⟩ := tsSem_all_outcomes k
    (fun i => if h : i - 2 < n - 1 then b ⟨i - 2, h⟩ else false)
  refine ⟨m, ?_⟩
  rintro ⟨φ, o⟩ hl
  obtain ⟨e, he, hlit⟩ := (Graph.mem_F _).mp hl
  obtain ⟨hact, hpol⟩ := (Graph.lit_eq_some_iff _ e φ o).mp hlit
  have hc : e.IsCons := by simp [TEv.IsCons, hact, Act.IsCons]
  obtain ⟨ht, hi⟩ := (tsEvents_cons he).mp hc
  have hact' := (mem_tsEvents n k).mp he
  simp only [tsAct, ht, hi, ↓reduceIte, hact, Option.some.injEq, Act.cons.injEq] at hact'
  have hpol' : (tsGraph n k b).pol e = some (b ⟨e.idx, hi⟩) := by
    simp only [tsGraph]
    rw [dite_eq_left_of_eq_true (eq_true ⟨he, ht, hi⟩)]
  rw [hpol] at hpol'
  cases hpol'
  subst hact'
  rw [hm (e.idx + 2) (by omega)]
  simp [hi]

/-- A full execution of the program is the graph of its outcomes. -/
theorem tsGraph_of_exec {G : Graph} (hG : G.Wf) (hE : (tsProg n k).Exec G)
    (hF : (tsProg n k).Full G) :
    G = tsGraph n k (fun i => (G.pol ⟨0, i, .cons (i + 2)⟩).getD false) := by
  have hact : ∀ e ∈ G.events, tsAct n k e.tid e.idx = some e.act := by
    intro e he
    have := hE.2 e he
    change tsAct n k e.tid (Graph.traceBefore _ e.tid e.idx).length = some e.act at this
    rwa [show (Graph.traceBefore G e.tid e.idx).length = e.idx by simp [Graph.traceBefore]]
      at this
  have hev : G.events = tsEvents n k := by
    ext e
    rw [mem_tsEvents]
    refine ⟨hact e, fun h => ?_⟩
    have hlt : e.idx < G.cnt e.tid := by
      by_contra hge
      obtain ⟨a', ha'⟩ := tsAct_mono h (Nat.not_lt.mp hge)
      have ht : e.tid ∈ (tsProg n k).threads := by
        change e.tid ∈ List.range (n + 1)
        rw [List.mem_range]
        unfold tsAct at h
        split_ifs at h <;> omega
      have := (full_iff.mp hF) e.tid ht
      change tsAct n k e.tid (G.trace e.tid).length = none at this
      rw [Graph.trace_length, ha'] at this
      cases this
    obtain ⟨e', he', ht', hi'⟩ := (hG.exists_idx_iff e.tid e.idx).mpr hlt
    have h' := hact e' he'
    rw [ht', hi', h] at h'
    obtain ⟨t, i, a⟩ := e
    obtain ⟨t', i', a'⟩ := e'
    simp only at ht' hi' h'
    subst ht' hi'
    cases h'
    exact he'
  apply Graph.ext
  · exact hE.1
  · exact hev
  · funext e
    by_cases he : e ∈ G.events
    · exact hG.rf_none e (Or.inr (tsAct_not_rw (hact e he)).1)
    · exact hG.rf_none e (Or.inl he)
  · funext x
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e he
    obtain ⟨heE, v, hv⟩ := (hG.co_mem x e).mp he
    exact (tsAct_not_rw (hact e heE)).2.1 (by simp [hv, Act.IsWrite])
  · funext e
    simp only [tsGraph]
    by_cases hc : e ∈ tsEvents n k ∧ e.tid = 0 ∧ e.idx < n - 1
    · rw [dite_eq_left_of_eq_true (eq_true hc)]
      have heG : e ∈ G.events := hev ▸ hc.1
      have hcons : e.IsCons := (tsEvents_cons hc.1).mpr hc.2
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp ((hG.pol_isSome e).mpr ⟨heG, hcons⟩)
      have ha := hact e heG
      simp only [tsAct, hc.2.1, hc.2.2, ↓reduceIte, Option.some.injEq] at ha
      have hee : e = ⟨0, e.idx, .cons (e.idx + 2)⟩ := by
        obtain ⟨t, i, a⟩ := e
        simp only at ha hc ⊢
        rw [← ha, hc.2.1]
      rw [← hee, ho]
      rfl
    · rw [dite_eq_right_of_eq_false (eq_false hc)]
      by_cases heG : e ∈ G.events
      · have hnc : ¬ e.IsCons := fun h => hc ⟨hev ▸ heG, (tsEvents_cons (hev ▸ heG)).mp h⟩
        by_contra hne
        obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hne
        exact hnc (hG.pol_some ho).2
      · exact hG.pol_none heG

theorem tsGraph_injective : Function.Injective (tsGraph n k) := by
  intro b b' h
  funext i
  have he : (⟨0, i.1, .cons (i.1 + 2)⟩ : TEv) ∈ tsEvents n k :=
    (mem_tsEvents n k).mpr (by simp [tsAct, i.2])
  have hp : ∀ c : Fin (n - 1) → Bool,
      (tsGraph n k c).pol ⟨0, i.1, .cons (i.1 + 2)⟩ = some (c i) := by
    intro c
    simp [tsGraph, he, i.2]
  have h1 := congrArg (fun G => G.pol ⟨0, i.1, .cons (i.1 + 2)⟩) h
  simp only [hp] at h1
  exact Option.some.inj h1

/-- S-2. The program has exactly `2^(n-1)` full consistent executions: one
for every vector of outcomes of the `n - 1` comparisons. -/
theorem ts_executions (n k : ℕ) : ∃ l : List Graph, l.Nodup ∧ l.length = 2 ^ (n - 1) ∧
    ∀ G, G ∈ l ↔ G.Wf ∧ (tsProg n k).Exec G ∧ (SC.sym (tsSem k).solver).cons G ∧
      (tsProg n k).Full G := by
  refine ⟨(Finset.univ : Finset (Fin (n - 1) → Bool)).toList.map (tsGraph n k),
    (Finset.nodup_toList _).map tsGraph_injective, by simp, fun G => ?_⟩
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨tsGraph_wf b, tsGraph_exec b, tsGraph_cons b, tsGraph_full b⟩
  · rintro ⟨hW, hE, -, hF⟩
    exact ⟨_, (tsGraph_of_exec hW hE hF).symm⟩

/-- S-2 for the algorithm: with any tie-break, the explorer of Algorithm 1
lists `2^(n-1)` graphs for the program. -/
theorem ts_explore_length (n k : ℕ) (τ : TieBreak (tsSem k).solver) :
    (explore (tsProg n k) (SC.sym (tsSem k).solver) τ (max k (n - 1))).length = 2 ^ (n - 1) := by
  obtain ⟨l, hnd, hlen, hmem⟩ := ts_executions n k
  obtain ⟨hnd', hmem'⟩ := explore_spec (τ := τ) (tsProg_bounded n k) SC.extensible
  rw [← hlen]
  exact ((List.perm_ext_iff_of_nodup hnd' hnd).mpr
    (fun G => (hmem' G).trans (hmem G).symm)).length_eq

/-! ### DPOR with a shared counter: `n!` orderings

The paper: an enumerative model uses a shared counter for the timestamps, and
"these shared accesses to the counter make pure DPOR explore `n!` orderings
among the pushes". The programs have no atomic fetch-and-increment; in
`ctrProg n` each of the `n` threads performs one write to the counter. The
program models the orderings of the accesses, not the values of the counter.
The count is for the Shasha-Snir explorer, which distinguishes the coherence
orders of the writes. -/

/-- The action of thread `t` at index `i`: one write to location `0`. -/
def ctrAct (n : ℕ) (t i : ℕ) : Option Act :=
  if t < n ∧ i = 0 then some (.write 0 (t + 1)) else none

/-- `n` threads, each with one access to the counter. -/
def ctrProg (n : ℕ) : Program where
  threads := List.range n
  threads_nodup := List.nodup_range
  step := fun t u => ctrAct n t u.length
  mem := fun _ => 0
  step_none := by
    intro (t : ℕ) ht
    have h1 : ¬ t < n := by simpa using ht
    change ctrAct n t 0 = none
    simp [ctrAct, h1]
  stop := by
    intro t u h
    exfalso
    unfold ctrAct at h
    rcases h with h | h <;> split_ifs at h <;> cases h

theorem ctrProg_bounded (n : ℕ) : (ctrProg n).Bounded 1 := by
  intro t u hu
  have h1 : ¬ u.length = 0 := by omega
  change ctrAct n t u.length = none
  simp [ctrAct, h1]

/-- The events: one write for each thread. -/
def ctrEvents (n : ℕ) : Finset TEv :=
  (Finset.range n).image (fun t => (⟨t, 0, .write 0 (t + 1)⟩ : TEv))

theorem mem_ctrEvents {e : TEv} : e ∈ ctrEvents n ↔ ctrAct n e.tid e.idx = some e.act := by
  simp only [ctrEvents, Finset.mem_image, Finset.mem_range, ctrAct]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simp [ht]
  · intro h
    split_ifs at h with h1
    obtain ⟨t, i, a⟩ := e
    simp only at h1 h
    obtain ⟨h1, rfl⟩ := h1
    cases h
    exact ⟨t, h1, rfl⟩

theorem ctrEvents_card (n : ℕ) : (ctrEvents n).card = n := by
  rw [ctrEvents, Finset.card_image_of_injective _ (fun a b h => by simpa using h),
    Finset.card_range]

theorem ctrEvents_act {e : TEv} (he : e ∈ ctrEvents n) :
    e.idx = 0 ∧ e.act = .write 0 (e.tid + 1) := by
  have h := mem_ctrEvents.mp he
  unfold ctrAct at h
  split_ifs at h with h1
  exact ⟨h1.2, (Option.some.inj h).symm⟩

/-- The graph in which the accesses to the counter are ordered as in `l`. -/
def ctrGraph (n : ℕ) (l : List TEv) : Graph where
  mem := fun _ => 0
  events := ctrEvents n
  rf := fun _ => none
  co := fun x => if x = 0 then l else []
  pol := fun _ => none

/-- `l` is an ordering of the accesses. -/
def IsOrdering (n : ℕ) (l : List TEv) : Prop := l.Nodup ∧ ∀ e, e ∈ l ↔ e ∈ ctrEvents n

theorem ctrGraph_wf {l : List TEv} (hl : IsOrdering n l) : (ctrGraph n l).Wf where
  idx_inj := by
    intro e he e' he' ht _
    obtain ⟨h1, h2⟩ := ctrEvents_act he
    obtain ⟨h1', h2'⟩ := ctrEvents_act he'
    obtain ⟨t, i, a⟩ := e
    obtain ⟨t', i', a'⟩ := e'
    simp only at ht h1 h2 h1' h2'
    subst ht h1 h1' h2 h2'
    rfl
  idx_contig := by
    intro e he i hi
    rw [(ctrEvents_act he).1] at hi
    exact absurd hi (Nat.not_lt_zero _)
  rf_read := by
    intro e he x hact
    rw [(ctrEvents_act he).2] at hact
    cases hact
  rf_none := fun _ _ => rfl
  co_mem := by
    intro x e
    simp only [ctrGraph]
    by_cases hx : x = 0
    · subst hx
      simp only [↓reduceIte]
      rw [hl.2 e]
      exact ⟨fun h => ⟨h, _, (ctrEvents_act h).2⟩, fun h => h.1⟩
    · simp only [hx, ↓reduceIte]
      constructor
      · intro h
        cases h
      · rintro ⟨he, v, hv⟩
        rw [(ctrEvents_act he).2] at hv
        cases hv
        exact absurd rfl hx
  co_nodup := by
    intro x
    simp only [ctrGraph]
    split_ifs
    · exact hl.1
    · exact List.nodup_nil
  pol_isSome := by
    intro e
    simp only [ctrGraph]
    constructor
    · intro h
      cases h
    · rintro ⟨he, hc⟩
      rw [TEv.IsCons, (ctrEvents_act he).2] at hc
      exact absurd hc (by simp [Act.IsCons])

theorem ctrGraph_exec (l : List TEv) : (ctrProg n).Exec (ctrGraph n l) := by
  refine ⟨rfl, fun e he => ?_⟩
  change ctrAct n e.tid (Graph.traceBefore _ e.tid e.idx).length = some e.act
  rw [show (Graph.traceBefore (ctrGraph n l) e.tid e.idx).length = e.idx by
    simp [Graph.traceBefore]]
  exact mem_ctrEvents.mp he

theorem ctrGraph_full {l : List TEv} (hl : IsOrdering n l) : (ctrProg n).Full (ctrGraph n l) := by
  rw [full_iff]
  intro t _
  change ctrAct n t (Graph.trace _ t).length = none
  rw [Graph.trace_length]
  by_contra hne
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hne
  have he : (⟨t, (ctrGraph n l).cnt t, a⟩ : TEv) ∈ (ctrGraph n l).events :=
    mem_ctrEvents.mpr ha
  exact lt_irrefl _ ((ctrGraph_wf hl).idx_lt_cnt he)

theorem ctrGraph_sc (n : ℕ) (l : List TEv) : SC.cons (ctrGraph n l) := by
  let rk : Ev → ℕ := fun a => match a with | .init => 0 | .th e => l.idxOf e + 1
  have hrk : ∀ a b, (ctrGraph n l).scStep a b → rk a < rk b := by
    rintro a b (h | ⟨e, -, -, h⟩ | h | ⟨e, e', x, -, -, he, hact, -⟩)
    · cases a with
      | init =>
        cases b with
        | init => exact absurd h (by simp [Graph.po])
        | th e => exact Nat.succ_pos _
      | th e =>
        cases b with
        | init => exact absurd h (by simp [Graph.po])
        | th e' =>
          obtain ⟨he, he', -, hi⟩ := h
          rw [(ctrEvents_act he).1, (ctrEvents_act he').1] at hi
          exact absurd hi (Nat.lt_irrefl _)
    · cases h
    · cases a with
      | init =>
        cases b with
        | init => exact absurd h (by simp [Graph.coRel])
        | th e => exact Nat.succ_pos _
      | th e =>
        cases b with
        | init => exact absurd h (by simp [Graph.coRel])
        | th e' =>
          obtain ⟨x, hx⟩ := h
          simp only [ctrGraph] at hx
          split_ifs at hx
          · exact Nat.succ_lt_succ hx.2.2
          · exact absurd hx.1 (by simp)
    · rw [(ctrEvents_act he).2] at hact
      cases hact
  have htr : ∀ a b, Relation.TransGen (ctrGraph n l).scStep a b → rk a < rk b := by
    intro a b h
    induction h with
    | single h => exact hrk _ _ h
    | tail _ h ih => exact lt_trans ih (hrk _ _ h)
  intro a ha
  exact lt_irrefl _ (htr a a ha)

theorem ctrGraph_cons (S : Solver) (n : ℕ) (l : List TEv) :
    (SC.sym S).cons (ctrGraph n l) := by
  refine Model.sym_cons_iff.mpr ⟨ctrGraph_sc n l, ?_⟩
  have : (ctrGraph n l).F = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro lit hlit
    obtain ⟨e, -, he⟩ := (Graph.mem_F _).mp hlit
    rw [Graph.lit_of_pol_none _ rfl] at he
    cases he
  rw [this]
  exact S.sat_empty

/-- A full execution of the program is the graph of the order of its
accesses. -/
theorem ctrGraph_of_exec {G : Graph} (hG : G.Wf) (hE : (ctrProg n).Exec G)
    (hF : (ctrProg n).Full G) : IsOrdering n (G.co 0) ∧ G = ctrGraph n (G.co 0) := by
  have hact : ∀ e ∈ G.events, ctrAct n e.tid e.idx = some e.act := by
    intro e he
    have := hE.2 e he
    change ctrAct n e.tid (Graph.traceBefore _ e.tid e.idx).length = some e.act at this
    rwa [show (Graph.traceBefore G e.tid e.idx).length = e.idx by simp [Graph.traceBefore]]
      at this
  have hev : G.events = ctrEvents n := by
    ext e
    rw [mem_ctrEvents]
    refine ⟨hact e, fun h => ?_⟩
    have h0 : e.tid < n ∧ e.idx = 0 := by
      unfold ctrAct at h
      split_ifs at h with h1
      exact h1
    have hlt : e.idx < G.cnt e.tid := by
      by_contra hge
      have hc : G.cnt e.tid = 0 := by omega
      have := (full_iff.mp hF) e.tid (by
        change e.tid ∈ List.range n
        exact List.mem_range.mpr h0.1)
      change ctrAct n e.tid (G.trace e.tid).length = none at this
      rw [Graph.trace_length, hc] at this
      rw [h0.2] at h
      rw [h] at this
      cases this
    obtain ⟨e', he', ht', hi'⟩ := (hG.exists_idx_iff e.tid e.idx).mpr hlt
    have h' := hact e' he'
    rw [ht', hi', h] at h'
    obtain ⟨t, i, a⟩ := e
    obtain ⟨t', i', a'⟩ := e'
    simp only at ht' hi' h'
    subst ht' hi'
    cases h'
    exact he'
  have hwr : ∀ e ∈ G.events, e.act = .write 0 (e.tid + 1) :=
    fun e he => (ctrEvents_act (hev ▸ he)).2
  refine ⟨⟨hG.co_nodup 0, fun e => ?_⟩, ?_⟩
  · rw [hG.co_mem 0 e, ← hev]
    exact ⟨fun h => h.1, fun h => ⟨h, _, hwr e h⟩⟩
  apply Graph.ext
  · exact hE.1
  · exact hev
  · funext e
    by_cases he : e ∈ G.events
    · refine hG.rf_none e (Or.inr ?_)
      rw [TEv.IsRead, hwr e he]
      simp [Act.IsRead]
    · exact hG.rf_none e (Or.inl he)
  · funext x
    simp only [ctrGraph]
    split_ifs with hx
    · rw [hx]
    · apply List.eq_nil_iff_forall_not_mem.mpr
      intro e he
      obtain ⟨heE, v, hv⟩ := (hG.co_mem x e).mp he
      rw [hwr e heE] at hv
      cases hv
      exact hx rfl
  · funext e
    by_contra hne
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hne
    obtain ⟨he, hc⟩ := hG.pol_some ho
    rw [TEv.IsCons, hwr e he] at hc
    exact absurd hc (by simp [Act.IsCons])

/-- S-4 for one access per thread: the program has exactly `n!` full
SC-consistent executions, one for every ordering of the accesses. -/
theorem ctr_executions (n : ℕ) (S : Solver) : ∃ l : List Graph, l.Nodup ∧
    l.length = n.factorial ∧
    ∀ G, G ∈ l ↔ G.Wf ∧ (ctrProg n).Exec G ∧ (SC.sym S).cons G ∧ (ctrProg n).Full G := by
  have hord : ∀ l, l ∈ (ctrEvents n).toList.permutations ↔ IsOrdering n l := by
    intro l
    rw [List.mem_permutations]
    constructor
    · intro h
      exact ⟨h.nodup_iff.mpr (Finset.nodup_toList _), fun e => by
        rw [h.mem_iff, Finset.mem_toList]⟩
    · rintro ⟨hnd, hmem⟩
      exact (List.perm_ext_iff_of_nodup hnd (Finset.nodup_toList _)).mpr
        (fun e => by rw [hmem, Finset.mem_toList])
  refine ⟨(ctrEvents n).toList.permutations.map (ctrGraph n), ?_, ?_, fun G => ?_⟩
  · refine (List.nodup_permutations _ (Finset.nodup_toList _)).map_on ?_
    intro l _ l' _ h
    have := congrArg (fun G => G.co 0) h
    simpa [ctrGraph] using this
  · rw [List.length_map, List.length_permutations, Finset.length_toList, ctrEvents_card]
  · simp only [List.mem_map]
    constructor
    · rintro ⟨l, hl, rfl⟩
      have hl' := (hord l).mp hl
      exact ⟨ctrGraph_wf hl', ctrGraph_exec l, ctrGraph_cons S n l, ctrGraph_full hl'⟩
    · rintro ⟨hW, hE, -, hF⟩
      obtain ⟨hl, hG⟩ := ctrGraph_of_exec hW hE hF
      exact ⟨G.co 0, (hord _).mpr hl, hG.symm⟩

/-- S-4 for the algorithm: the explorer of Algorithm 1 lists `n!` graphs. -/
theorem ctr_explore_length (n : ℕ) {S : Solver} (τ : TieBreak S) :
    (explore (ctrProg n) (SC.sym S) τ 1).length = n.factorial := by
  obtain ⟨l, hnd, hlen, hmem⟩ := ctr_executions n S
  obtain ⟨hnd', hmem'⟩ := explore_spec (τ := τ) (ctrProg_bounded n) SC.extensible
  rw [← hlen]
  exact ((List.perm_ext_iff_of_nodup hnd' hnd).mpr
    (fun G => (hmem' G).trans (hmem G).symm)).length_eq

/-! ### Counting interleavings

"If each thread pushed `k` times … DPOR would explore `(kn)!/(k!)^n`": the
number of interleavings of `n` sequences of length `k`. -/

section Interleavings

variable {α : Type*}

/-- The interleavings of two sequences. -/
def shuffle : List α → List α → List (List α)
  | [], ys => [ys]
  | x :: xs, [] => [x :: xs]
  | x :: xs, y :: ys =>
    (shuffle xs (y :: ys)).map (x :: ·) ++ (shuffle (x :: xs) ys).map (y :: ·)

theorem length_shuffle : ∀ xs ys : List α,
    (shuffle xs ys).length = (xs.length + ys.length).choose xs.length
  | [], ys => by simp [shuffle]
  | x :: xs, [] => by simp [shuffle]
  | x :: xs, y :: ys => by
    rw [shuffle, List.length_append, List.length_map, List.length_map,
      length_shuffle xs (y :: ys), length_shuffle (x :: xs) ys]
    simp only [List.length_cons]
    rw [show xs.length + 1 + (ys.length + 1) = (xs.length + ys.length + 1) + 1 by omega,
      Nat.choose_succ_succ,
      show xs.length + (ys.length + 1) = xs.length + ys.length + 1 by omega,
      show xs.length + 1 + ys.length = xs.length + ys.length + 1 by omega]

theorem length_of_mem_shuffle : ∀ (xs ys : List α) {w : List α}, w ∈ shuffle xs ys →
    w.length = xs.length + ys.length
  | [], ys, w, h => by
    simp only [shuffle, List.mem_singleton] at h
    simp [h]
  | x :: xs, [], w, h => by
    simp only [shuffle, List.mem_singleton] at h
    simp [h]
  | x :: xs, y :: ys, w, h => by
    rw [shuffle, List.mem_append, List.mem_map, List.mem_map] at h
    rcases h with ⟨w', hw', rfl⟩ | ⟨w', hw', rfl⟩
    · rw [List.length_cons, length_of_mem_shuffle xs (y :: ys) hw']
      simp only [List.length_cons]
      omega
    · rw [List.length_cons, length_of_mem_shuffle (x :: xs) ys hw']
      simp only [List.length_cons]
      omega

/-- The interleavings of a list of sequences. -/
def interleavings : List (List α) → List (List α)
  | [] => [[]]
  | l :: L => (interleavings L).flatMap (shuffle l)

theorem length_of_mem_interleavings : ∀ (L : List (List α)) {w : List α},
    w ∈ interleavings L → w.length = (L.map List.length).sum
  | [], w, h => by
    simp only [interleavings, List.mem_singleton] at h
    simp [h]
  | l :: L, w, h => by
    rw [interleavings, List.mem_flatMap] at h
    obtain ⟨w', hw', hw⟩ := h
    rw [length_of_mem_shuffle l w' hw, length_of_mem_interleavings L hw']
    simp

theorem length_interleavings_cons (l : List α) (L : List (List α)) :
    (interleavings (l :: L)).length =
      (l.length + (L.map List.length).sum).choose l.length * (interleavings L).length := by
  rw [interleavings, List.length_flatMap]
  have : ∀ w ∈ interleavings L, (shuffle l w).length =
      (l.length + (L.map List.length).sum).choose l.length := by
    intro w hw
    rw [length_shuffle, length_of_mem_interleavings L hw]
  rw [List.map_congr_left this, List.map_const', List.sum_replicate_nat, Nat.mul_comm]

/-- S-3. The number of interleavings of `n` sequences of length `k`, times
`(k!)^n`, is `(kn)!`: the number is `(kn)!/(k!)^n`. -/
theorem length_interleavings_mul (k : ℕ) : ∀ L : List (List α), (∀ l ∈ L, l.length = k) →
    (interleavings L).length * k.factorial ^ L.length = (k * L.length).factorial
  | [], _ => by simp [interleavings]
  | l :: L, h => by
    have hl : l.length = k := h l List.mem_cons_self
    have hL : ∀ l' ∈ L, l'.length = k := fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have ih := length_interleavings_mul k L hL
    have hsum : (L.map List.length).sum = k * L.length := by
      rw [List.map_congr_left hL, List.map_const', List.sum_replicate_nat, Nat.mul_comm]
    have key := Nat.add_choose_mul_factorial_mul_factorial (k * L.length) k
    rw [length_interleavings_cons, hl, hsum, List.length_cons, pow_succ, Nat.mul_succ,
      ← key, ← ih, Nat.add_comm k (k * L.length)]
    ring

theorem length_interleavings_div (k : ℕ) (L : List (List α)) (h : ∀ l ∈ L, l.length = k) :
    (interleavings L).length = (k * L.length).factorial / k.factorial ^ L.length := by
  rw [← length_interleavings_mul k L h]
  exact (Nat.mul_div_cancel _ (pow_pos (Nat.factorial_pos k) _)).symm

/-- S-3 for one access per thread: `n!` orderings. -/
theorem length_interleavings_singletons (L : List (List α)) (h : ∀ l ∈ L, l.length = 1) :
    (interleavings L).length = L.length.factorial := by
  have := length_interleavings_mul 1 L h
  simpa using this

end Interleavings

/-- S-5. "A pure concolic approach would first serialize the pushes and then
solve the symbolic constraints … leading to `n! · 2^(n-1)` executions": the
number of pairs of an ordering of the `n` pushes and a vector of outcomes of
the `n - 1` comparisons. (No such algorithm is defined here; this is the
count.) -/
theorem ct_count (n : ℕ) (L : List (List ℕ)) (hL : L.length = n) (h : ∀ l ∈ L, l.length = 1) :
    ((interleavings L) ×ˢ (Finset.univ : Finset (Fin (n - 1) → Bool)).toList).length =
      n.factorial * 2 ^ (n - 1) := by
  rw [List.length_product, length_interleavings_singletons L h, hL]
  simp

end Condpor
