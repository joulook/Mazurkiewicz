import Mazurkiewicz.Condpor.Rmw.LifecycleSem

/-!
# Thread lifecycle machine: first lemmas (LC2-a)

* `enabled_iff_next`, `mem_enabledL`, `step_iff`: the relational and the executable
  enabledness agree.
* `step_det` (the successor is a function of the occurrence) and `enabled_tid_unique` (a
  thread has at most one enabled occurrence).
* `LockInv` ("count `> 0` iff an owner is set"), preserved by every step (`Step.lockInv`,
  `Steps.lockInv`); owner uniqueness as hold counts (`holdsM_unique`) and the
  lock-value relation in machine terms (`count_eq_zero_iff`).
* `commute`: two adjacent independent occurrences commute on machine states (both orders
  enabled, the same state).
-/

namespace Condpor

namespace Life

namespace Sem

open Targets

variable {P : LProg} {s s1 s2 : MState} {o o1 o2 : Occ}

/-! ### Relational and executable enabledness -/

theorem enabled_tid_mem (h : Enabled P s o) : o.tid ∈ P.threads := by
  cases h <;> assumption

theorem next_of_enabled (h : Enabled P s o) : next P s o.tid = some o := by
  cases h <;> simp_all [next, Occ.tid]

theorem next_tid {t : Tid} (h : next P s t = some o) : o.tid = t := by
  unfold next at h
  split at h
  · split_ifs at h; cases h; rfl
  · split at h <;> (try split_ifs at h) <;> cases h <;> rfl
  · cases h

theorem enabled_of_next {t : Tid} (ht : t ∈ P.threads) (h : next P s t = some o) :
    Enabled P s o := by
  unfold next at h
  split at h
  · split_ifs at h with h1; cases h; exact .begin ht ‹_› h1
  · split at h <;> (try split_ifs at h) <;> cases h <;>
      first
      | exact .fin ht ‹_› (List.head?_eq_none_iff.mp ‹_›)
      | constructor <;> first | assumption | (simp_all [MState.heldB]; omega) | simp_all
  · cases h

/-- The relational enabledness is the executable one. -/
theorem enabled_iff_next : Enabled P s o ↔ ∃ t ∈ P.threads, next P s t = some o :=
  ⟨fun h => ⟨o.tid, enabled_tid_mem h, next_of_enabled h⟩,
    fun ⟨_, ht, h⟩ => enabled_of_next ht h⟩

theorem mem_enabledL : o ∈ enabledL P s ↔ Enabled P s o := by
  rw [enabled_iff_next, enabledL, List.mem_filterMap]

/-- A step is an enabled occurrence of the executable list and its effect. -/
theorem step_iff : Step P s o s1 ↔ o ∈ enabledL P s ∧ s1 = eff s o := by
  rw [mem_enabledL]; rfl

/-- The maximal states are those with an empty list of enabled occurrences. -/
theorem maximal_iff : Maximal P s ↔ enabledL P s = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  exact forall_congr' fun o => not_congr mem_enabledL.symm

/-! ### The enumeration lists maximal runs -/

/-- **Soundness of the enumeration**: every listed pair is the graph and the class of a run
from `s` to a maximal state, with the graph built from `g`. -/
theorem mem_runsF {f : ℕ} {g : GB} {x : Config × MCls} (h : x ∈ runsF P f s g) :
    ∃ rs s', Steps P s rs s' ∧ Maximal P s' ∧
      x = ((finalize P (rs.foldl (emit P) g) s').toCfg P, mclass P s') := by
  induction f generalizing s g with
  | zero => simp [runsF] at h
  | succ f ih =>
    unfold runsF at h
    split at h
    next he =>
      simp only [List.mem_singleton] at h
      exact ⟨[], s, .nil s, maximal_iff.mpr he, by simpa using h⟩
    next =>
      obtain ⟨o, ho, hx⟩ := List.mem_flatMap.mp h
      obtain ⟨rs, s', hr, hm, rfl⟩ := ih hx
      exact ⟨o :: rs, s', .cons ⟨mem_enabledL.mp ho, rfl⟩ hr, hm, by simp⟩

/-- Every pair of `machRuns` is the graph and the class of a maximal run. -/
theorem mem_machRuns {x : Config × MCls} (h : x ∈ machRuns P) :
    ∃ rs s, MaxRun P rs s ∧ x = (runCfg P rs s, mclass P s) := by
  obtain ⟨rs, s, hr, hm, rfl⟩ := mem_runsF h
  exact ⟨rs, s, ⟨hr, hm⟩, rfl⟩

/-- The potential of a thread: what it can still do. -/
def potT (s : MState) (t : Tid) : ℕ :=
  match s.status t with
  | .new => (s.rest t).length + 2
  | .running => (s.rest t).length + 1
  | _ => 0

/-- The potential of a state. -/
def pot (P : LProg) (s : MState) : ℕ := (P.threads.map (potT s)).sum

theorem pos_of_head {l : List TOp} {a : TOp} (h : l.head? = some a) : 0 < l.length := by
  cases l <;> simp_all

theorem potT_step (h : Enabled P s o) :
    potT (eff s o) o.tid < potT s o.tid ∧ ∀ t ≠ o.tid, potT (eff s o) t = potT s t := by
  cases h
  all_goals
    (try have hp := pos_of_head (by assumption))
    simp_all [potT, eff, MState.adv, MState.setSt, Occ.tid]
    try omega

theorem sum_lt_of {l : List Tid} {f g : Tid → ℕ} (hle : ∀ t, f t ≤ g t) {t0 : Tid}
    (h0 : t0 ∈ l) (hlt : f t0 < g t0) : (l.map f).sum < (l.map g).sum := by
  induction l with
  | nil => cases h0
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h0 with rfl | h
    · have h2 : (l.map f).sum ≤ (l.map g).sum := List.sum_le_sum (fun t _ => hle t)
      omega
    · have := ih h
      have := hle a
      omega

theorem pot_step (h : Enabled P s o) : pot P (eff s o) < pot P s := by
  obtain ⟨h1, h2⟩ := potT_step h
  refine sum_lt_of (fun t => ?_) (enabled_tid_mem h) h1
  by_cases ht : t = o.tid
  · subst ht; exact h1.le
  · exact (h2 t ht).le

/-- **Completeness of the enumeration**: with fuel above the potential, every run to a
maximal state is listed. -/
theorem runsF_complete {f : ℕ} {g : GB} {rs : List Occ} {s' : MState} (h : Steps P s rs s')
    (hm : Maximal P s') (hf : pot P s < f) :
    ((finalize P (rs.foldl (emit P) g) s').toCfg P, mclass P s') ∈ runsF P f s g := by
  induction h generalizing f g with
  | nil s =>
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    unfold runsF
    rw [maximal_iff.mp hm]
    simp
  | @cons s s1 s2 o rs hs hr ih =>
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have ho : o ∈ enabledL P s := mem_enabledL.mpr hs.1
    have hp := pot_step hs.1
    rw [← hs.2] at hp
    unfold runsF
    split
    next he => rw [he] at ho; cases ho
    next =>
      refine List.mem_flatMap.mpr ⟨o, ho, ?_⟩
      rw [← hs.2]
      exact ih hm (by omega)

theorem pot_init_lt (P : LProg) : pot P (MState.init P) < fuel P := by
  unfold pot fuel
  have : ((P.threads.map (potT (MState.init P))).sum) ≤
      (P.threads.map (fun t => (P.code t).length + 2)).sum :=
    List.sum_le_sum (fun t _ => by
      simp only [potT, MState.init]
      split_ifs <;> simp)
  omega

/-- **The enumeration is exactly the maximal runs**: a pair is listed iff it is the graph
and the class of a maximal run. -/
theorem mem_machRuns_iff {x : Config × MCls} :
    x ∈ machRuns P ↔ ∃ rs s, MaxRun P rs s ∧ x = (runCfg P rs s, mclass P s) := by
  refine ⟨mem_machRuns, ?_⟩
  rintro ⟨rs, s, ⟨hr, hm⟩, rfl⟩
  exact runsF_complete hr hm (pot_init_lt P)

/-! ### Determinism -/

/-- The successor state is determined by the occurrence. -/
theorem step_det (h1 : Step P s o s1) (h2 : Step P s o s2) : s1 = s2 := h1.2.trans h2.2.symm

/-- A thread has at most one enabled occurrence. -/
theorem enabled_tid_unique (h1 : Enabled P s o1) (h2 : Enabled P s o2) (h : o1.tid = o2.tid) :
    o1 = o2 := by
  have e1 := next_of_enabled h1
  have e2 := next_of_enabled h2
  rw [h, e2] at e1
  exact (Option.some.inj e1).symm

/-! ### The lock invariant -/

/-- Count positive iff an owner is set. (At most one owner holds by construction: the owner
is a function of the lock.) -/
def LockInv (s : MState) : Prop := ∀ l, 0 < s.count l ↔ (s.owner l).isSome

theorem lockInv_init : LockInv (MState.init P) := by
  intro l; simp [MState.init]

/-- Every step preserves the lock invariant. -/
theorem Step.lockInv (h : Step P s o s1) (hs : LockInv s) : LockInv s1 := by
  obtain ⟨e, rfl⟩ := h
  intro l'
  have := hs l'
  cases e <;>
    simp only [eff, MState.adv, MState.setSt, MState.heldB, Function.update_apply,
      Bool.and_eq_true, decide_eq_true_eq, Bool.and_eq_false_imp] at * <;>
    (try split_ifs) <;> subst_vars <;> simp_all

theorem Steps.lockInv {rs : List Occ} (h : Steps P s rs s1) (hs : LockInv s) : LockInv s1 := by
  induction h with
  | nil => exact hs
  | cons h _ ih => exact ih (h.lockInv hs)

/-- The hold count of thread `t` on lock `l`: the count if `t` is the owner, else `0`. -/
def holdsM (s : MState) (t : Tid) (l : Loc) : ℕ := if s.owner l = some t then s.count l else 0

/-- **Owner uniqueness**: at most one thread has a positive hold count on a lock. -/
theorem holdsM_unique {t1 t2 : Tid} {l : Loc} (h1 : 0 < holdsM s t1 l) (h2 : 0 < holdsM s t2 l) :
    t1 = t2 := by
  unfold holdsM at h1 h2
  split_ifs at h1 h2 with e1 e2 <;> first | omega | exact Option.some.inj (e1.symm.trans e2)

/-- Under the invariant, a lock is free (count `0`) iff no thread has a positive hold
count. -/
theorem count_eq_zero_iff (hs : LockInv s) (l : Loc) :
    s.count l = 0 ↔ ∀ t, holdsM s t l = 0 := by
  constructor
  · intro h t; simp [holdsM, h]
  · intro h
    by_contra h0
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp ((hs l).mp (Nat.pos_of_ne_zero h0))
    exact h0 (by simpa [holdsM, ht] using h t)

theorem heldB_iff_holdsM {t : Tid} {l : Loc} : s.heldB t l = true ↔ 0 < holdsM s t l := by
  unfold MState.heldB holdsM
  split_ifs with h <;> simp [h]

/-! ### What a comparison means -/

/-- **Meaning of `cmp`**: if the first component of `cmp P n` is `true`, the serializations
with classes of the graphs of the maximal runs and those of the terminal-valid explorer
graphs (with `lifeClass`) are the same set. -/
theorem cmp_spec {n : ℕ} (h : (cmp P n).1 = true) :
    (∀ rs s, MaxRun P rs s → ∃ c ∈ exploreCfgAtF (lifeSys P n) n, termValid P c = true ∧
      ser P.threads c = ser P.threads (runCfg P rs s) ∧ lifeClass P c = (mclass P s).toL) ∧
    (∀ c ∈ exploreCfgAtF (lifeSys P n) n, termValid P c = true → ∃ rs s, MaxRun P rs s ∧
      ser P.threads (runCfg P rs s) = ser P.threads c ∧ (mclass P s).toL = lifeClass P c) := by
  simp only [cmp, sameSet, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro rs s hr
    have hm : (ser P.threads (runCfg P rs s), (mclass P s).toL) ∈ machSide P := by
      unfold machSide
      rw [List.mem_dedup]
      exact List.mem_map.mpr ⟨_, mem_machRuns_iff.mpr ⟨rs, s, hr, rfl⟩, rfl⟩
    obtain ⟨c, hc, he⟩ := List.mem_map.mp (h1 _ hm)
    obtain ⟨hc1, hc2⟩ := List.mem_filter.mp hc
    simp only [Prod.mk.injEq] at he
    exact ⟨c, hc1, hc2, he.1, he.2⟩
  · intro c hc hv
    have hl : (ser P.threads c, lifeClass P c) ∈ lifeSide P n :=
      List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, hv⟩, rfl⟩
    have := h2 _ hl
    unfold machSide at this
    rw [List.mem_dedup] at this
    obtain ⟨x, hx, he⟩ := List.mem_map.mp this
    obtain ⟨rs, s, hr, rfl⟩ := mem_machRuns_iff.mp hx
    simp only [Prod.mk.injEq] at he
    exact ⟨rs, s, hr, he.1, he.2⟩

/-! ### Commutation of independent occurrences -/

theorem heldB_eq_true {t : Tid} {l : Loc} :
    s.heldB t l = true ↔ s.owner l = some t ∧ 0 < s.count l := by
  simp [MState.heldB]

theorem heldB_eq_false {t : Tid} {l : Loc} :
    s.heldB t l = false ↔ (s.owner l = some t → s.count l = 0) := by
  simp [MState.heldB]

theorem heldB_mk {st : Tid → Status} {sd : Tid → Bool} {r : Tid → List TOp}
    {ow : Loc → Option Tid} {c : Loc → ℕ} {m : Loc → Val} {t : Tid} {l : Loc} :
    (MState.mk st sd r ow c m).heldB t l = (decide (ow l = some t) && decide (0 < c l)) := rfl

theorem joinOkB_mk {st : Tid → Status} {sd : Tid → Bool} {r : Tid → List TOp}
    {ow : Loc → Option Tid} {c : Loc → ℕ} {m : Loc → Val} {u : Tid} :
    (MState.mk st sd r ow c m).joinOkB u =
      ((decide (st u = .new) && !sd u) || decide (st u = .term)) := rfl

theorem joinOkB_eq_true {u : Tid} :
    s.joinOkB u = true ↔ (s.status u = .new ∧ s.started u = false) ∨ s.status u = .term := by
  simp [MState.joinOkB]

/-- The constructor index of an occurrence. -/
def Occ.kind : Occ → ℕ
  | .begin _ => 0 | .acq _ _ => 1 | .reacq _ _ => 2 | .tryAcq _ _ _ => 3
  | .tryFail _ _ _ => 4 | .tryRe _ _ _ => 5 | .unlockRe _ _ => 6 | .release _ _ => 7
  | .unlockErr _ _ => 8 | .query _ _ => 9 | .rd _ _ => 10 | .wr _ _ _ => 11
  | .asmOk _ _ _ => 12 | .asmStop _ _ _ => 13 | .start _ _ => 14 | .join _ _ => 15
  | .fin _ => 16

theorem Occ.kind_lt (o : Occ) : o.kind < 17 := by cases o <;> simp [Occ.kind]

/-- Both orders enabled, the same state. -/
def CommAt (P : LProg) (s : MState) (o1 o2 : Occ) : Prop :=
  Enabled P s o2 ∧ Enabled P (eff s o2) o1 ∧ eff (eff s o2) o1 = eff (eff s o1) o2

theorem indep_facts (hd : ¬ Dep o1 o2) :
    o1.tid ≠ o2.tid ∧ ∀ p ∈ fp o1, ∀ q ∈ fp o2, (p.1 = q.1 ∨ q.1 = p.1) →
      p.2 = false ∧ q.2 = false := by
  refine ⟨fun h => hd (Or.inl h), ?_⟩
  intro p hp q hq h
  have h' : p.1 = q.1 := h.elim id Eq.symm
  have h2 : ¬ (p.2 = true ∨ q.2 = true) := fun h2 => hd (Or.inr ⟨p, hp, q, hq, h', h2⟩)
  simpa using h2

/-- The case analysis on the second occurrence, for a fixed first one. -/
macro "comm_tac" hd:ident e2:ident : tactic => `(tactic| (
  obtain ⟨ht, hf⟩ := indep_facts $hd
  have ht' := Ne.symm ht
  cases $e2:ident <;>
    simp only [fp, Occ.tid, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Res.lock.injEq, Res.data.injEq, Res.life.injEq, reduceCtorEq,
      false_implies, true_implies, and_true, true_and, and_self, Bool.true_eq_false,
      imp_false, IsEmpty.forall_iff, implies_true, not_or, not_false_eq_true] at ht ht' hf <;>
    simp only [CommAt, eff, MState.adv, MState.setSt, heldB_mk, joinOkB_mk,
      Function.update_apply, ite_true, ite_false, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_false_iff_not, Bool.and_eq_false_imp, Bool.or_eq_true, Bool.not_eq_true',
      List.tail_cons, true_and, and_true, not_false_eq_true, ne_eq, lt_self_iff_false,
      not_true_eq_false, false_and, and_false, false_or, or_false] at * <;>
    (try casesm* _ ∧ _) <;>
    simp_all only [CommAt, eff, MState.adv, MState.setSt, heldB_mk, joinOkB_mk,
      Function.update_apply, ite_true, ite_false, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_false_iff_not, Bool.and_eq_false_imp, Bool.or_eq_true, Bool.not_eq_true',
      List.tail_cons, true_and, and_true, not_false_eq_true, ne_eq, lt_self_iff_false,
      not_true_eq_false, false_and, and_false, false_or, or_false] <;>
    (try split_ifs at *) <;> (try subst_vars) <;> (try casesm* _ ∧ _) <;>
    (try simp_all only [reduceCtorEq, false_and,
      and_false, false_or, or_false, Option.some.injEq, not_true_eq_false]) <;>
    (repeat' apply And.intro) <;>
    first
    | (constructor <;> first
        | assumption
        | (simp_all [heldB_eq_true, heldB_eq_false, joinOkB_eq_true, Function.update_apply]; done)
        | (simp only [heldB_mk, joinOkB_mk, Function.update_apply]; split_ifs <;>
            simp_all [heldB_eq_true, heldB_eq_false, joinOkB_eq_true]; done)
        | omega
        | (simp only [heldB_eq_true, heldB_eq_false] at *; omega)
        | (simp only [heldB_mk, Function.update_apply] at *; split_ifs <;>
            simp only [heldB_eq_true, heldB_eq_false] at * <;> omega)
        )
    | (ext x <;> simp only [Function.update_apply] <;> split_ifs <;> (try subst_vars) <;>
        first | rfl | contradiction | omega | (simp_all; done))
    | (simp_all [heldB_eq_true, heldB_eq_false]; done)))

theorem comm_begin (e1 : Enabled P s o1) (e2 : Enabled P (eff s o1) o2) (hd : ¬ Dep o1 o2)
    (hk : o1.kind = 0) : CommAt P s o1 o2 := by
  cases e1 <;> simp [Occ.kind] at hk
  comm_tac hd e2

theorem comm_acq (e1 : Enabled P s o1) (e2 : Enabled P (eff s o1) o2) (hd : ¬ Dep o1 o2)
    (hk : o1.kind = 1) : CommAt P s o1 o2 := by
  cases e1 <;> simp [Occ.kind] at hk
  comm_tac hd e2

theorem comm_reacq (e1 : Enabled P s o1) (e2 : Enabled P (eff s o1) o2) (hd : ¬ Dep o1 o2)
    (hk : o1.kind = 2) : CommAt P s o1 o2 := by
  cases e1 <;> simp [Occ.kind] at hk
  comm_tac hd e2

theorem comm_tryAcq (e1 : Enabled P s o1) (e2 : Enabled P (eff s o1) o2) (hd : ¬ Dep o1 o2)
    (hk : o1.kind = 3) : CommAt P s o1 o2 := by
  cases e1 <;> simp [Occ.kind] at hk
  comm_tac hd e2

theorem comm_tryFail (e1 : Enabled P s o1) (e2 : Enabled P (eff s o1) o2) (hd : ¬ Dep o1 o2)
    (hk : o1.kind = 4) : CommAt P s o1 o2 := by
  cases e1 <;> simp [Occ.kind] at hk
  comm_tac hd e2

theorem comm_tryRe (e1 : Enabled P s o1) (e2 : Enabled P (eff s o1) o2) (hd : ¬ Dep o1 o2)
    (hk : o1.kind = 5) : CommAt P s o1 o2 := by
  cases e1 <;> simp [Occ.kind] at hk
  comm_tac hd e2

theorem comm_unlockRe (e1 : Enabled P s o1) (e2 : Enabled P (eff s o1) o2) (hd : ¬ Dep o1 o2)
    (hk : o1.kind = 6) : CommAt P s o1 o2 := by
  cases e1 <;> simp [Occ.kind] at hk
  comm_tac hd e2

theorem comm_release (e1 : Enabled P s o1) (e2 : Enabled P (eff s o1) o2) (hd : ¬ Dep o1 o2)
    (hk : o1.kind = 7) : CommAt P s o1 o2 := by
  cases e1 <;> simp [Occ.kind] at hk
  comm_tac hd e2

theorem comm_unlockErr (e1 : Enabled P s o1) (e2 : Enabled P (eff s o1) o2) (hd : ¬ Dep o1 o2)
    (hk : o1.kind = 8) : CommAt P s o1 o2 := by
  cases e1 <;> simp [Occ.kind] at hk
  comm_tac hd e2

theorem comm_query (e1 : Enabled P s o1) (e2 : Enabled P (eff s o1) o2) (hd : ¬ Dep o1 o2)
    (hk : o1.kind = 9) : CommAt P s o1 o2 := by
  cases e1 <;> simp [Occ.kind] at hk
  comm_tac hd e2

theorem comm_rd (e1 : Enabled P s o1) (e2 : Enabled P (eff s o1) o2) (hd : ¬ Dep o1 o2)
    (hk : o1.kind = 10) : CommAt P s o1 o2 := by
  cases e1 <;> simp [Occ.kind] at hk
  comm_tac hd e2

theorem comm_wr (e1 : Enabled P s o1) (e2 : Enabled P (eff s o1) o2) (hd : ¬ Dep o1 o2)
    (hk : o1.kind = 11) : CommAt P s o1 o2 := by
  cases e1 <;> simp [Occ.kind] at hk
  comm_tac hd e2

theorem comm_asmOk (e1 : Enabled P s o1) (e2 : Enabled P (eff s o1) o2) (hd : ¬ Dep o1 o2)
    (hk : o1.kind = 12) : CommAt P s o1 o2 := by
  cases e1 <;> simp [Occ.kind] at hk
  comm_tac hd e2

theorem comm_asmStop (e1 : Enabled P s o1) (e2 : Enabled P (eff s o1) o2) (hd : ¬ Dep o1 o2)
    (hk : o1.kind = 13) : CommAt P s o1 o2 := by
  cases e1 <;> simp [Occ.kind] at hk
  comm_tac hd e2

theorem comm_start (e1 : Enabled P s o1) (e2 : Enabled P (eff s o1) o2) (hd : ¬ Dep o1 o2)
    (hk : o1.kind = 14) : CommAt P s o1 o2 := by
  cases e1 <;> simp [Occ.kind] at hk
  comm_tac hd e2

theorem comm_join (e1 : Enabled P s o1) (e2 : Enabled P (eff s o1) o2) (hd : ¬ Dep o1 o2)
    (hk : o1.kind = 15) : CommAt P s o1 o2 := by
  cases e1 <;> simp [Occ.kind] at hk
  comm_tac hd e2

theorem comm_fin (e1 : Enabled P s o1) (e2 : Enabled P (eff s o1) o2) (hd : ¬ Dep o1 o2)
    (hk : o1.kind = 16) : CommAt P s o1 o2 := by
  cases e1 <;> simp [Occ.kind] at hk
  comm_tac hd e2

/-- **Commutation**: if `o1` then `o2` is a run from `s` and the two are independent, then
`o2` then `o1` is a run from `s` to the same state. -/
theorem commute (h1 : Step P s o1 s1) (h2 : Step P s1 o2 s2) (hd : ¬ Dep o1 o2) :
    ∃ s1', Step P s o2 s1' ∧ Step P s1' o1 s2 := by
  obtain ⟨e1, rfl⟩ := h1
  obtain ⟨e2, rfl⟩ := h2
  suffices h : CommAt P s o1 o2 from ⟨eff s o2, ⟨h.1, rfl⟩, h.2.1, h.2.2.symm⟩
  by_cases h0 : o1.kind = 0
  · exact comm_begin e1 e2 hd h0
  by_cases h1 : o1.kind = 1
  · exact comm_acq e1 e2 hd h1
  by_cases h2 : o1.kind = 2
  · exact comm_reacq e1 e2 hd h2
  by_cases h3 : o1.kind = 3
  · exact comm_tryAcq e1 e2 hd h3
  by_cases h4 : o1.kind = 4
  · exact comm_tryFail e1 e2 hd h4
  by_cases h5 : o1.kind = 5
  · exact comm_tryRe e1 e2 hd h5
  by_cases h6 : o1.kind = 6
  · exact comm_unlockRe e1 e2 hd h6
  by_cases h7 : o1.kind = 7
  · exact comm_release e1 e2 hd h7
  by_cases h8 : o1.kind = 8
  · exact comm_unlockErr e1 e2 hd h8
  by_cases h9 : o1.kind = 9
  · exact comm_query e1 e2 hd h9
  by_cases h10 : o1.kind = 10
  · exact comm_rd e1 e2 hd h10
  by_cases h11 : o1.kind = 11
  · exact comm_wr e1 e2 hd h11
  by_cases h12 : o1.kind = 12
  · exact comm_asmOk e1 e2 hd h12
  by_cases h13 : o1.kind = 13
  · exact comm_asmStop e1 e2 hd h13
  by_cases h14 : o1.kind = 14
  · exact comm_start e1 e2 hd h14
  by_cases h15 : o1.kind = 15
  · exact comm_join e1 e2 hd h15
  exact comm_fin e1 e2 hd (by have := o1.kind_lt; omega)

end Sem

end Life

end Condpor
