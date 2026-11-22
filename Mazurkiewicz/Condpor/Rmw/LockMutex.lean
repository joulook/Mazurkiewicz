import Mazurkiewicz.Condpor.Rmw.Locks

/-!
# Locks: mutual exclusion

A theorem about graphs (`LockLike.alternates`): if the writes of a location
`l` behave as acquires (value `1`) and releases (value `0`) of a lock, then in
every well-formed graph with an acyclic SC order the coherence list of `l`
alternates between an acquire by a thread and the release by the same thread,
starting with an acquire.

`lockSys_lockLike`, `lockSys_mutex`: every well-formed, SC-consistent, atomic
execution of a lock program (`lockSys`) satisfies it for a lock location that
no plain write of the program names.

`LockLike G l`:
* (h1) every write to `l` has value `0` or `1`;
* (h2) a write of `1` is the immediate coherence successor of a write of value
  `0` (atomicity of the acquire, whose read returned `0`);
* (h3) a write of `0` by a thread has an earlier write of `1` by that thread
  with no write of `0` by the thread between them.
-/

namespace Condpor

open Program

/-- The position of an element of a list without repetition. -/
theorem List.idxOf_getElem_of_nodup {α : Type*} [DecidableEq α] {l : List α} (h : l.Nodup)
    {i : ℕ} (hi : i < l.length) : l.idxOf l[i] = i := by
  have hm : l[i] ∈ l := List.getElem_mem hi
  have hlt : l.idxOf l[i] < l.length := List.idxOf_lt_length_of_mem hm
  exact h.getElem_inj_iff.mp (List.getElem_idxOf hlt)

/-- Positions and `Before` in a list without repetition. -/
theorem List.before_getElem_iff {α : Type*} [DecidableEq α] {l : List α} (h : l.Nodup)
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length) : l.Before l[i] l[j] ↔ i < j := by
  unfold List.Before
  rw [List.idxOf_getElem_of_nodup h hi, List.idxOf_getElem_of_nodup h hj]
  exact ⟨fun h' => h'.2.2, fun h' => ⟨List.getElem_mem hi, List.getElem_mem hj, h'⟩⟩

/-- The writes of `l` behave as the acquires and releases of a lock. -/
structure LockLike (G : Graph) (l : Loc) : Prop where
  h1 : ∀ w ∈ G.co l, G.valAt l (.th w) = 0 ∨ G.valAt l (.th w) = 1
  h2 : ∀ w ∈ G.co l, G.valAt l (.th w) = 1 → ∃ s, G.ImmCo l s w ∧ G.valAt l s = 0
  h3 : ∀ w ∈ G.co l, G.valAt l (.th w) = 0 →
    ∃ a ∈ G.co l, G.valAt l (.th a) = 1 ∧ a.tid = w.tid ∧ a.idx < w.idx ∧
      ∀ w' ∈ G.co l, G.valAt l (.th w') = 0 → w'.tid = w.tid →
        ¬ (a.idx < w'.idx ∧ w'.idx < w.idx)

namespace Graph

variable {G : Graph} {l : Loc}

/-- The SC order: an earlier event of a thread is not coherence-after a later
one. -/
theorem not_before_of_po (hG : G.Wf) (hc : Maz.Acyclic G.scStep) {a b : TEv}
    (ha : a ∈ G.co l) (hb : b ∈ G.co l) (ht : a.tid = b.tid) (hi : a.idx < b.idx) :
    ¬ (G.co l).Before b a := by
  intro hba
  have haE := ((hG.co_mem l a).mp ha).1
  have hbE := ((hG.co_mem l b).mp hb).1
  have h1 : G.scStep (.th a) (.th b) := Or.inl ⟨haE, hbE, ht, hi⟩
  have h2 : G.scStep (.th b) (.th a) := Or.inr (Or.inr (Or.inl ⟨l, hba⟩))
  exact hc _ (Relation.TransGen.head h1 (Relation.TransGen.single h2))

/-- The immediate coherence predecessor of the element at position `i`. -/
theorem ImmCo.pred (hG : G.Wf) {s : Ev} {i : ℕ} (hi : i < (G.co l).length)
    (h : G.ImmCo l s (G.co l)[i]) :
    (i = 0 ∧ s = .init) ∨ ∃ hi' : i - 1 < (G.co l).length, 0 < i ∧ s = .th (G.co l)[i - 1] := by
  have hnd := hG.co_nodup l
  generalize hw : (G.co l)[i] = w at h
  cases s with
  | init =>
    left
    obtain ⟨l', hl'⟩ := h
    refine ⟨?_, rfl⟩
    have h0 : 0 < (G.co l).length := by rw [hl']; simp
    have h1 : (G.co l)[0] = w := by simp [hl']
    exact (hnd.getElem_inj_iff.mp (h1.trans hw.symm)).symm
  | th p =>
    right
    obtain ⟨l₁, l₂, hl⟩ := h
    have hlen : l₁.length + 1 < (G.co l).length := by rw [hl]; simp
    have h1 : (G.co l)[l₁.length + 1] = w := by simp [hl]
    have hi1 : l₁.length + 1 = i := hnd.getElem_inj_iff.mp (h1.trans hw.symm)
    have hp : (G.co l)[l₁.length]'(by omega) = p := by simp [hl]
    subst hi1
    exact ⟨by omega, by omega, by simp [hp]⟩

end Graph

/-- Mutual exclusion: the coherence list of a lock alternates between an
acquire (value `1`) and the release (value `0`) by the same thread. -/
theorem LockLike.alternates {G : Graph} {l : Loc} (hG : G.Wf) (hc : Maz.Acyclic G.scStep)
    (h : LockLike G l) :
    ∀ i (hi : i < (G.co l).length),
      (i % 2 = 0 → G.valAt l (.th (G.co l)[i]) = 1) ∧
      (i % 2 = 1 → G.valAt l (.th (G.co l)[i]) = 0 ∧
        ∃ hi' : i - 1 < (G.co l).length, (G.co l)[i].tid = (G.co l)[i - 1].tid) := by
  have hnd := hG.co_nodup l
  -- the contradiction for a release whose acquire is not its neighbour
  have key : ∀ (i j : ℕ) (hi : i < (G.co l).length) (hj : j + 1 < (G.co l).length),
      j + 1 < i →
      G.valAt l (.th (G.co l)[j + 1]) = 0 → (G.co l)[j + 1].tid = (G.co l)[j].tid →
      (G.co l)[j].tid = (G.co l)[i].tid → (G.co l)[j].idx < (G.co l)[i].idx →
      (∀ w' ∈ G.co l, G.valAt l (.th w') = 0 → w'.tid = (G.co l)[i].tid →
        ¬ ((G.co l)[j].idx < w'.idx ∧ w'.idx < (G.co l)[i].idx)) → False := by
    intro i j hi hj hji hv ht1 ht2 hidx hno
    have hmi := List.getElem_mem hi
    have hmj := List.getElem_mem (show j < (G.co l).length by omega)
    have hmj1 := List.getElem_mem hj
    have hEi := ((hG.co_mem l _).mp hmi).1
    have hEj := ((hG.co_mem l _).mp hmj).1
    have hEj1 := ((hG.co_mem l _).mp hmj1).1
    rcases Nat.lt_trichotomy (G.co l)[j + 1].idx (G.co l)[j].idx with h1 | h1 | h1
    · exact Graph.not_before_of_po hG hc hmj1 hmj ht1 h1
        ((List.before_getElem_iff hnd _ _).mpr (Nat.lt_succ_self j))
    · have := hG.idx_inj _ hEj1 _ hEj ht1 h1
      have := hnd.getElem_inj_iff.mp this
      omega
    · rcases Nat.lt_trichotomy (G.co l)[j + 1].idx (G.co l)[i].idx with h2 | h2 | h2
      · exact hno _ hmj1 hv (ht1.trans ht2) ⟨h1, h2⟩
      · have := hG.idx_inj _ hEj1 _ hEi (ht1.trans ht2) h2
        have := hnd.getElem_inj_iff.mp this
        omega
      · exact Graph.not_before_of_po hG hc hmi hmj1 (ht1.trans ht2).symm h2
          ((List.before_getElem_iff hnd _ _).mpr hji)
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hmi := List.getElem_mem hi
    -- the acquire of a release at position `i`, as a position
    have acq : G.valAt l (.th (G.co l)[i]) = 0 →
        ∃ j, ∃ hj : j < (G.co l).length, j < i ∧ G.valAt l (.th (G.co l)[j]) = 1 ∧
          (G.co l)[j].tid = (G.co l)[i].tid ∧ (G.co l)[j].idx < (G.co l)[i].idx ∧
          ∀ w' ∈ G.co l, G.valAt l (.th w') = 0 → w'.tid = (G.co l)[i].tid →
            ¬ ((G.co l)[j].idx < w'.idx ∧ w'.idx < (G.co l)[i].idx) := by
      intro hv
      obtain ⟨a, ha, hva, hta, hia, hno⟩ := h.h3 _ hmi hv
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      refine ⟨j, hj, ?_, hva, hta, hia, hno⟩
      by_contra hji
      have hne : j ≠ i := by
        intro hji'
        subst hji'
        omega
      exact Graph.not_before_of_po hG hc ha hmi hta hia
        ((List.before_getElem_iff hnd _ _).mpr (by omega))
    -- a release at position `i` whose acquire is at position `j < i`: `j = i - 1`
    have rel : G.valAt l (.th (G.co l)[i]) = 0 →
        0 < i ∧ ∃ hi' : i - 1 < (G.co l).length, (G.co l)[i].tid = (G.co l)[i - 1].tid ∧
          (i - 1) % 2 = 0 := by
      intro hv
      obtain ⟨j, hj, hji, hva, hta, hia, hno⟩ := acq hv
      have hjeven : j % 2 = 0 := by
        by_contra hodd
        have := ((ih j hji hj).2 (by omega)).1
        rw [this] at hva
        exact Nat.zero_ne_one hva
      by_cases hjn : j + 1 = i
      · subst hjn
        exact ⟨by omega, by simpa using hj, by simpa using hta.symm, by simpa using hjeven⟩
      · exfalso
        have hj1 : j + 1 < (G.co l).length := by omega
        obtain ⟨hv1, hi', ht1⟩ := (ih (j + 1) (by omega) hj1).2 (by omega)
        exact key i j hi hj1 (by omega) hv1 (by simpa using ht1) hta hia hno
    constructor
    · intro heven
      rcases h.h1 _ hmi with hv | hv
      · obtain ⟨hpos, hi', -, hpar⟩ := rel hv
        omega
      · exact hv
    · intro hodd
      rcases h.h1 _ hmi with hv | hv
      · obtain ⟨hpos, hi', ht, -⟩ := rel hv
        exact ⟨hv, hi', ht⟩
      · exfalso
        obtain ⟨s, hs, hs0⟩ := h.h2 _ hmi hv
        rcases Graph.ImmCo.pred hG hi hs with ⟨h0, -⟩ | ⟨hi', hpos, rfl⟩
        · omega
        · have := (ih (i - 1) (by omega) hi').1 (by omega)
          rw [this] at hs0
          exact Nat.zero_ne_one hs0.symm

/-! ### The machine of a thread -/

namespace LState

theorem next_ops_subset (s : LState) (v : Option Val) :
    ∀ op ∈ (s.next v).ops, op ∈ s.ops := by
  intro op hop
  unfold LState.next at hop
  cases hph : s.phase with
  | acquire l => simpa [hph] using hop
  | blocking => simpa [hph] using hop
  | ready =>
    cases hops : s.ops with
    | nil => simp [hph, hops] at hop
    | cons o rest =>
      cases o with
      | lock l =>
        simp only [hph, hops] at hop
        split at hop
        · split at hop <;> exact List.mem_cons_of_mem _ hop
        · exact List.mem_cons_of_mem _ hop
      | tryLock l k =>
        simp only [hph, hops] at hop
        split at hop
        · split at hop
          · exact List.mem_cons_of_mem _ hop
          · exact List.mem_cons_of_mem _ (List.mem_of_mem_drop hop)
        · exact List.mem_cons_of_mem _ hop
      | unlock l =>
        simp only [hph, hops] at hop
        split at hop <;> exact List.mem_cons_of_mem _ hop
      | rd x =>
        simp only [hph, hops] at hop
        exact List.mem_cons_of_mem _ hop
      | wr x v' =>
        simp only [hph, hops] at hop
        exact List.mem_cons_of_mem _ hop
      | ev a k =>
        simp only [hph, hops] at hop
        exact List.mem_cons_of_mem _ hop

/-- The phase `acquire l` is entered only by a successful acquire read. -/
theorem acquire_of_next {s : LState} {v : Option Val} {l : Loc}
    (h : (s.next v).phase = .acquire l) (hs : s.phase ≠ .acquire l) :
    s.phase = .ready ∧ s.holds l = 0 ∧ v = some 0 ∧
      ∃ rest, s.ops = .lock l :: rest ∨ ∃ k, s.ops = .tryLock l k :: rest := by
  unfold LState.next at h
  cases hph : s.phase with
  | acquire l' => simp [hph] at h
  | blocking =>
    simp only [hph] at h
    cases h
  | ready =>
    cases hops : s.ops with
    | nil =>
      simp only [hph, hops] at h
      cases h
    | cons o rest =>
      cases o with
      | lock l' =>
        simp only [hph, hops] at h
        by_cases h0 : s.holds l' = 0
        · by_cases hv : v = some 0
          · simp only [h0, hv, ite_true] at h
            have hl : l' = l := by cases h; rfl
            subst hl
            exact ⟨rfl, h0, hv, rest, Or.inl rfl⟩
          · simp [h0, hv] at h
        · simp [h0] at h
      | tryLock l' k =>
        simp only [hph, hops] at h
        by_cases h0 : s.holds l' = 0
        · by_cases hv : v = some 0
          · simp only [h0, hv, ite_true] at h
            have hl : l' = l := by cases h; rfl
            subst hl
            exact ⟨rfl, h0, hv, rest, Or.inr ⟨k, rfl⟩⟩
          · simp [h0, hv] at h
        · simp [h0] at h
      | unlock l' =>
        simp only [hph, hops] at h
        split at h <;> cases h
      | rd x => simp [hph, hops] at h
      | wr x v' => simp [hph, hops] at h
      | ev a k => simp [hph, hops] at h

/-- The writes of a thread to a location that no plain write names. -/
theorem act_write {s : LState} {l : Loc} {v : Val} (h : s.act = some (.write l v))
    (hpriv : ∀ v', LOp.wr l v' ∉ s.ops) :
    (s.phase = .acquire l ∧ v = 1) ∨
      (s.phase = .ready ∧ s.holds l = 1 ∧ v = 0 ∧ ∃ rest, s.ops = .unlock l :: rest) := by
  unfold LState.act at h
  cases hph : s.phase with
  | acquire l' =>
    simp only [hph] at h
    cases h
    exact Or.inl ⟨rfl, rfl⟩
  | blocking => simp [hph] at h
  | ready =>
    cases hops : s.ops with
    | nil => simp [hph, hops] at h
    | cons o rest =>
      cases o with
      | lock l' =>
        simp only [hph, hops] at h
        split at h <;> cases h
      | tryLock l' k =>
        simp only [hph, hops] at h
        split at h <;> cases h
      | unlock l' =>
        simp only [hph, hops] at h
        by_cases h0 : s.holds l' = 0
        · simp [h0] at h
        · by_cases h1 : s.holds l' = 1
          · simp only [h1, ite_true] at h
            simp only [show (1 : ℕ) ≠ 0 from Nat.one_ne_zero, ite_false] at h
            cases h
            exact Or.inr ⟨rfl, h1, rfl, rest, rfl⟩
          · simp [h0, h1] at h
      | rd x => simp [hph, hops] at h
      | wr x v' =>
        simp only [hph, hops] at h
        cases h
        exact absurd (by rw [hops]; exact List.mem_cons_self) (hpriv v)
      | ev a k => simp [hph, hops] at h

end LState

theorem lockState_snoc (ops : List LOp) (u : List (Option Val)) (v : Option Val) :
    lockState ops (u ++ [v]) = (lockState ops u).next v := by
  simp [lockState, List.foldl_append]

theorem lockState_ops_subset (ops : List LOp) (u : List (Option Val)) :
    ∀ op ∈ (lockState ops u).ops, op ∈ ops := by
  induction u using List.reverseRecOn with
  | nil => exact fun op h => h
  | append_singleton u v ih =>
    intro op hop
    rw [lockState_snoc] at hop
    exact ih op (LState.next_ops_subset _ v op hop)

/-- One step of the machine: if the thread holds `l` afterwards, it has just
acquired it, or it held it before and the step was not a release write. -/
theorem LState.holds_next {s : LState} {v : Option Val} {l : Loc}
    (hpriv : ∀ v', LOp.wr l v' ∉ s.ops) (h : 0 < (s.next v).holds l) :
    s.phase = .acquire l ∨ (0 < s.holds l ∧ s.act ≠ some (.write l 0)) := by
  unfold LState.next at h
  unfold LState.act
  cases hph : s.phase with
  | acquire l' =>
    simp only [hph] at h
    by_cases hl : l' = l
    · exact Or.inl (by rw [hl])
    · right
      rw [Function.update_of_ne (Ne.symm hl)] at h
      refine ⟨h, ?_⟩
      simp
  | blocking =>
    simp only [hph] at h
    exact Or.inr ⟨h, by simp⟩
  | ready =>
    right
    cases hops : s.ops with
    | nil =>
      simp only [hph, hops] at h
      exact ⟨h, by simp⟩
    | cons o rest =>
      cases o with
      | lock l' =>
        simp only [hph, hops] at h
        by_cases h0 : s.holds l' = 0
        · simp only [h0, ite_true] at h
          refine ⟨by split at h <;> exact h, by simp [h0]⟩
        · simp only [h0, ite_false] at h
          refine ⟨?_, by simp [h0]⟩
          by_cases hl : l' = l
          · rw [← hl]
            omega
          · rwa [Function.update_of_ne (Ne.symm hl)] at h
      | tryLock l' k =>
        simp only [hph, hops] at h
        by_cases h0 : s.holds l' = 0
        · simp only [h0, ite_true] at h
          refine ⟨by split at h <;> exact h, by simp [h0]⟩
        · simp only [h0, ite_false] at h
          refine ⟨?_, by simp [h0]⟩
          by_cases hl : l' = l
          · rw [← hl]
            omega
          · rwa [Function.update_of_ne (Ne.symm hl)] at h
      | unlock l' =>
        simp only [hph, hops] at h
        by_cases h0 : s.holds l' = 0
        · simp only [h0, ite_true] at h
          exact ⟨h, by simp [h0]⟩
        · simp only [h0, ite_false] at h
          by_cases hl : l' = l
          · subst hl
            rw [Function.update_self] at h
            refine ⟨by omega, ?_⟩
            have h1 : s.holds l' ≠ 1 := by omega
            simp [h0, h1]
          · rw [Function.update_of_ne (Ne.symm hl)] at h
            refine ⟨h, ?_⟩
            by_cases h1 : s.holds l' = 1
            · simp [h1, hl]
            · simp [h0, h1]
      | rd x =>
        simp only [hph, hops] at h
        exact ⟨h, by simp⟩
      | wr x v' =>
        simp only [hph, hops] at h
        refine ⟨h, ?_⟩
        intro heq
        simp only [Option.some.injEq, Act.write.injEq] at heq
        exact hpriv v' (by rw [hops, heq.1]; exact List.mem_cons_self)
      | ev a k =>
        simp only [hph, hops] at h
        exact ⟨h, by simp⟩

/-- A thread that holds `l` after a trace acquired it at an earlier position
and has not written a release since. -/
theorem lockState_holds_pos (ops : List LOp) (l : Loc) (hpriv : ∀ v', LOp.wr l v' ∉ ops) :
    ∀ u : List (Option Val), 0 < (lockState ops u).holds l →
      ∃ j, j < u.length ∧ (lockState ops (u.take j)).phase = .acquire l ∧
        ∀ k, j < k → k < u.length → (lockState ops (u.take k)).act ≠ some (.write l 0) := by
  intro u
  induction u using List.reverseRecOn with
  | nil =>
    intro h
    simp [lockState] at h
  | append_singleton u v ih =>
    intro h
    rw [lockState_snoc] at h
    have hp : ∀ v', LOp.wr l v' ∉ (lockState ops u).ops :=
      fun v' hm => hpriv v' (lockState_ops_subset ops u _ hm)
    rcases LState.holds_next hp h with hacq | ⟨hpos, hact⟩
    · refine ⟨u.length, by simp, by simpa using hacq, fun k h1 h2 => ?_⟩
      simp only [List.length_append, List.length_singleton] at h2
      omega
    · obtain ⟨j, hj, hjp, hbet⟩ := ih hpos
      refine ⟨j, by simp; omega, ?_, fun k h1 h2 => ?_⟩
      · rw [List.take_append_of_le_length (Nat.le_of_lt hj)]
        exact hjp
      · simp only [List.length_append, List.length_singleton] at h2
        by_cases hk : k < u.length
        · rw [List.take_append_of_le_length (Nat.le_of_lt hk)]
          exact hbet k h1 hk
        · have hku : k = u.length := by omega
          rw [hku, List.take_left']
          · exact hact
          · rfl

/-! ### Lock programs satisfy `LockLike` -/

section Sys

variable {threads : List Tid} {hnd : threads.Nodup} {code : Tid → List LOp} {n : ℕ}

/-- A step of the program is the action of the machine. -/
theorem lockSys_step {t : Tid} {u : List (Option Val)} {a : Act}
    (h : (lockSys threads hnd code n).toProgram.step t u = some a) :
    (lockState (code t) u).act = some a := by
  unfold lockSys mkXProg mkProg at h
  simp only at h
  split at h
  · cases h
  · exact h

/-- The trace before position `j ≤ i` is a prefix of the trace before `i`. -/
theorem Graph.traceBefore_take (G : Graph) (t : Tid) {i j : ℕ} (h : j ≤ i) :
    (G.traceBefore t i).take j = G.traceBefore t j := by
  unfold Graph.traceBefore
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

variable {G : Graph}

/-- The action of an event of an execution is the action of the machine of
its thread after the trace before it. -/
theorem lockSys_act (hE : (lockSys threads hnd code n).toProgram.Exec G) {e : TEv}
    (he : e ∈ G.events) :
    (lockState (code e.tid) (G.traceBefore e.tid e.idx)).act = some e.act :=
  lockSys_step (hE.2 e he)

/-- The state after an event. -/
theorem lockSys_state_succ (hG : G.Wf) {e : TEv} (he : e ∈ G.events) :
    lockState (code e.tid) (G.traceBefore e.tid (e.idx + 1)) =
      (lockState (code e.tid) (G.traceBefore e.tid e.idx)).next (G.ret e) := by
  rw [Graph.traceBefore_succ, lockState_snoc, hG.evAt_eq_some he]
  rfl

/-- In an atomic execution of a lock program, a location that no plain write
names behaves as a lock. -/
theorem lockSys_lockLike (hG : G.Wf) (hE : (lockSys threads hnd code n).toProgram.Exec G)
    (hat : (lockSys threads hnd code n).Atomic G) {l : Loc}
    (hpriv : ∀ t v, LOp.wr l v ∉ code t) : LockLike G l := by
  have hp : ∀ (t : Tid) (u : List (Option Val)) (v' : Val),
      LOp.wr l v' ∉ (lockState (code t) u).ops :=
    fun t u v' hm => hpriv t v' (lockState_ops_subset _ u _ hm)
  have hval : ∀ {w : TEv} {v : Val}, w.act = .write l v → G.valAt l (.th w) = v := by
    intro w v hv
    simp [Graph.valAt, hv]
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨hwE, v, hv⟩ := (hG.co_mem l w).mp hw
    have ha := lockSys_act hE hwE
    rw [hv] at ha
    rw [hval hv]
    rcases LState.act_write ha (hp _ _) with ⟨-, rfl⟩ | ⟨-, -, rfl, -⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  · intro w hw hw1
    obtain ⟨hwE, v, hv⟩ := (hG.co_mem l w).mp hw
    rw [hval hv] at hw1
    subst hw1
    have ha := lockSys_act hE hwE
    rw [hv] at ha
    have hph : (lockState (code w.tid) (G.traceBefore w.tid w.idx)).phase = .acquire l := by
      rcases LState.act_write ha (hp _ _) with ⟨h1, -⟩ | ⟨-, -, h1, -⟩
      · exact h1
      · exact absurd h1 Nat.one_ne_zero
    -- the event before `w` in its thread
    obtain ⟨i, hwi⟩ : ∃ i, w.idx = i + 1 := by
      cases hwi : w.idx with
      | zero =>
        rw [hwi] at hph
        simp [Graph.traceBefore, lockState] at hph
      | succ i => exact ⟨i, rfl⟩
    obtain ⟨r, hr, hrt, hri⟩ := hG.idx_contig w hwE i (by omega)
    have hsucc := lockSys_state_succ (code := code) hG hr
    rw [hrt, hri, ← hwi] at hsucc
    rw [hsucc] at hph
    have hne : (lockState (code w.tid) (G.traceBefore w.tid i)).phase ≠ .acquire l := by
      intro h'
      unfold LState.next at hph
      simp [h'] at hph
    obtain ⟨hready, h0, hret, rest, hops⟩ := LState.acquire_of_next hph hne
    -- the read
    have hract : r.act = .read l := by
      have := lockSys_act hE hr
      rw [hrt, hri] at this
      unfold LState.act at this
      rcases hops with hops | ⟨k, hops⟩
      · simp only [hready, hops, h0, ite_true] at this
        exact (Option.some.inj this).symm
      · simp only [hready, hops, h0, ite_true] at this
        exact (Option.some.inj this).symm
    have hexr : (lockState (code w.tid) (G.traceBefore w.tid i)).isEx = true := by
      unfold LState.isEx
      rcases hops with hops | ⟨k, hops⟩
      · simp [hready, hops, h0]
      · simp [hready, hops, h0]
    have hexw : (lockState (code w.tid) (G.traceBefore w.tid (i + 1))).isEx = true := by
      rw [← hwi, hsucc]
      unfold LState.isEx
      simp [hph]
    have hstepr := hE.2 r hr
    rw [hrt, hri, hract] at hstepr
    have hstepw := hE.2 w hwE
    rw [hv] at hstepw
    have htr : G.traceBefore w.tid w.idx = G.traceBefore w.tid i ++ [some 0] := by
      rw [hwi, Graph.traceBefore_succ]
      have := hG.evAt_eq_some hr
      rw [hrt, hri] at this
      rw [this]
      exact congrArg (fun x => G.traceBefore w.tid i ++ [x]) hret
    have hrmw : (lockSys threads hnd code n).RMW G r w := by
      refine ⟨hr, hwE, hrt.symm, by omega, by simp [TEv.IsRead, hract, Act.IsRead],
        by simp [TEv.IsWrite, hv, Act.IsWrite], ?_, ?_⟩
      · change exFlag (lockSys threads hnd code n).toProgram.step (lsFlag code) r.tid
          (G.traceBefore r.tid r.idx) = true
        rw [hrt, hri]
        unfold exFlag
        rw [hstepr]
        exact hexr
      · change exFlag (lockSys threads hnd code n).toProgram.step (lsFlag code) w.tid
          (G.traceBefore w.tid w.idx) = true
        unfold exFlag
        rw [hstepw]
        have hfl : lsFlag code w.tid (G.traceBefore w.tid w.idx) = true := by
          unfold lsFlag
          rw [hwi]
          exact hexw
        rw [hfl, htr]
        simp only [List.getLast?_concat, List.dropLast_concat, Bool.true_and]
        rw [hstepr]
        simpa [lsFlag] using hexr
    obtain ⟨s, hs, -⟩ := hG.rf_read r hr l hract
    have hloc : w.loc = l := by simp [TEv.loc, hv, Act.loc]
    refine ⟨s, hloc ▸ hat r w hrmw s hs, ?_⟩
    have : G.ret r = some (G.valAt l s) := by
      unfold Graph.ret
      rw [hract, hs]
      rfl
    rw [this] at hret
    exact Option.some.inj hret
  · intro w hw hw0
    obtain ⟨hwE, v, hv⟩ := (hG.co_mem l w).mp hw
    rw [hval hv] at hw0
    subst hw0
    have ha := lockSys_act hE hwE
    rw [hv] at ha
    have hholds : (lockState (code w.tid) (G.traceBefore w.tid w.idx)).holds l = 1 := by
      rcases LState.act_write ha (hp _ _) with ⟨-, h1⟩ | ⟨-, h1, -, -⟩
      · exact absurd h1.symm Nat.one_ne_zero
      · exact h1
    obtain ⟨j, hj, hjp, hbet⟩ := lockState_holds_pos (code w.tid) l (hpriv w.tid)
      (G.traceBefore w.tid w.idx) (by rw [hholds]; exact Nat.one_pos)
    rw [Graph.traceBefore_length] at hj hbet
    rw [Graph.traceBefore_take G w.tid (Nat.le_of_lt hj)] at hjp
    obtain ⟨a, haE, hat', hai⟩ := hG.idx_contig w hwE j hj
    have haact : a.act = .write l 1 := by
      have := lockSys_act hE haE
      rw [hat', hai] at this
      unfold LState.act at this
      simp only [hjp] at this
      exact (Option.some.inj this).symm
    refine ⟨a, (hG.co_mem l a).mpr ⟨haE, 1, haact⟩, hval haact, hat', by omega, ?_⟩
    intro w' hw' hw'0 hw't ⟨h1, h2⟩
    obtain ⟨hw'E, v', hv'⟩ := (hG.co_mem l w').mp hw'
    rw [hval hv'] at hw'0
    subst hw'0
    have := lockSys_act hE hw'E
    rw [hw't, hv'] at this
    refine hbet w'.idx (by omega) h2 ?_
    rw [Graph.traceBefore_take G w.tid (Nat.le_of_lt h2)]
    exact this

/-- Mutual exclusion for lock programs: in every well-formed, SC-consistent,
atomic execution, the writes of a lock location that no plain write names
alternate in coherence order between an acquire (value `1`) by a thread and
the release (value `0`) by the same thread, starting with an acquire.

"Mutual exclusion" is this alternation of the writes of the lock. Not stated
here: that the events of two critical sections do not interleave in the SC
order (it follows from the alternation, the program order and the acyclicity
of the SC order); anything about a thread that ends, blocks or is cut while
it holds the lock (the last acquire may have no release); fairness; that the
lock is released eventually. A `tryLock` by a thread that does not hold the
lock succeeds exactly if its read returned `0`; by the holder it succeeds
without a read (both by the definition of the machine). -/
theorem lockSys_mutex (hG : G.Wf) (hE : (lockSys threads hnd code n).toProgram.Exec G)
    (hc : (Model.atomic (lockSys threads hnd code n) SC).cons G) {l : Loc}
    (hpriv : ∀ t v, LOp.wr l v ∉ code t) :
    ∀ i (hi : i < (G.co l).length),
      (i % 2 = 0 → G.valAt l (.th (G.co l)[i]) = 1) ∧
      (i % 2 = 1 → G.valAt l (.th (G.co l)[i]) = 0 ∧
        ∃ hi' : i - 1 < (G.co l).length, (G.co l)[i].tid = (G.co l)[i - 1].tid) :=
  (lockSys_lockLike hG hE hc.2 hpriv).alternates hG hc.1

end Sys

end Condpor
