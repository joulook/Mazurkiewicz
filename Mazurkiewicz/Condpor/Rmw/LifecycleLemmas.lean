import Mazurkiewicz.Condpor.Rmw.Lifecycle

/-!
# Thread lifecycle: the lemmas of §4 (LC1)

For a program `P` of the fragment (`fragB P = true`) and a graph `G` that is a well-formed
execution of `lifeSys P n` (any `n`) and SC-consistent (`SC.cons G`, acyclicity of
`po ∪ rf ∪ co ∪ fr`; atomicity and satisfiability are not needed):

* `lc_lemma1_nonroot`, `lc_lemma1_root`: the coherence order of `st t` is a prefix of
  `[start, finish]` (non-root), of `[finish]` (root).
* `lc_lemma2`: a non-root thread with an event after the start-read other than its
  start-wait `block` has its start-read reading the start write.
* `lc_lemma3`: a join read of `2` reads the finish write of its target; the target's other
  events are po-before it, the joiner's later events porf-after it.
* `lc_lemma4`: a read of value `0` of a lifecycle location reads `init` (so does a join
  read of `0`); with `st_write_val` (every write of a lifecycle location writes `1` or `2`)
  this is the invariant "only `init` gives a lifecycle location the value `0`".
* `lc_lemma5`: every event of a non-root thread other than its start-read and start-wait
  `block` (its body events and its finish) is `porf`-after a start write of `st t`.
* `lc_lemma6`: a join read of `1` reads a start write of its target.
* `lc_lemma7`: every `block` directly follows, in po, a read; the read and its value are
  one of the four rows of the kind table of §3 (start-read of value `0` at index `0`; lock
  read of a value other than `0`; join read of `1`; read of a data location).
* `lc_lemma8`: a start-read of value `0` that reads the coherence-maximal write (a final
  start wait) belongs to a thread whose lifecycle location has no write at all (never
  started) and whose events are the start-read and, at index `1`, a `block`; in a full
  graph with `2 ≤ n` the `block` exists.
* `start_unique`, `finish_unique`: at most one start write and one finish write per
  lifecycle location (from the static single-start rule and the compiled table).
-/

namespace Condpor

namespace Life

open Program

variable {P : LProg}

/-! ### The fragment, unpacked -/

/-- The fragment as propositions. -/
structure Frag (P : LProg) : Prop where
  roots_sub : ∀ r ∈ P.roots, r ∈ P.threads
  st_inj : ∀ t ∈ P.threads, ∀ u ∈ P.threads, P.st t = P.st u → t = u
  st_not_lock : ∀ t ∈ P.threads, P.isLock (P.st t) = false
  calls : ∀ t ∈ P.threads, ∀ c ∈ P.code t, callOk P t c = true
  one_starter : ∀ u ∈ P.threads, ∀ t₁ ∈ P.threads, ∀ t₂ ∈ P.threads,
    TOp.start u ∈ P.code t₁ → TOp.start u ∈ P.code t₂ → t₁ = t₂
  one_start : ∀ u ∈ P.threads, ∀ t ∈ P.threads, (P.code t).count (.start u) ≤ 1

theorem eq_of_length_le_one {α : Type*} {l : List α} (h : l.length ≤ 1) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  match l, h with
  | [], _ => simp at ha
  | [x], _ => simp only [List.mem_singleton] at ha hb; rw [ha, hb]
  | _ :: _ :: _, h => simp at h

theorem frag_of_fragB (h : fragB P = true) : Frag P := by
  simp only [fragB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, fun t ht u hu e => List.inj_on_of_nodup_map h2 ht hu e, h3, h4, ?_, ?_⟩
  · intro u hu t₁ h₁ t₂ h₂ c₁ c₂
    have := (h5 u hu).1
    exact eq_of_length_le_one this (List.mem_filter.mpr ⟨h₁, by simpa using c₁⟩)
      (List.mem_filter.mpr ⟨h₂, by simpa using c₂⟩)
  · intro u hu t ht
    have := (h5 u hu).2 t ht
    rwa [maxStarts_eq_count] at this

theorem Frag.isSt_st (_hF : Frag P) {w : Tid} (hw : w ∈ P.threads) : P.isSt (P.st w) = true :=
  List.any_eq_true.mpr ⟨w, hw, by simp⟩

theorem Frag.isData_st (hF : Frag P) {w : Tid} (hw : w ∈ P.threads) :
    P.isData (P.st w) = false := by
  simp [LProg.isData, hF.isSt_st hw]

/-- The initial value of a lifecycle location: `1` for a root, `0` otherwise. -/
theorem Frag.mem_st (hF : Frag P) {w : Tid} (hw : w ∈ P.threads) :
    lifeMem P (P.st w) = if P.isRoot w then 1 else 0 := by
  unfold lifeMem
  by_cases hr : P.isRoot w = true
  · have : P.roots.any (fun r => decide (P.st r = P.st w)) = true :=
      List.any_eq_true.mpr ⟨w, by simpa [LProg.isRoot] using hr, by simp⟩
    simp [this, hr]
  · have : P.roots.any (fun r => decide (P.st r = P.st w)) = false := by
      rw [Bool.eq_false_iff]
      intro h'
      obtain ⟨r, hr', he⟩ := List.any_eq_true.mp h'
      have := hF.st_inj r (hF.roots_sub r hr') w hw (by simpa using he)
      subst this
      exact hr (by simpa [LProg.isRoot] using hr')
    simp [this, hr]

/-! ### The compiled program -/

theorem step_eq (P : LProg) (n : ℕ) (t : Tid) (u : List (Option Val)) :
    (lifeSys P n).toProgram.step t u =
      if n ≤ u.length ∨ t ∉ P.threads ∨ stopped (lifeTab P) t u = true then none
      else lifeTab P t u := rfl

theorem step_some {n : ℕ} {t : Tid} {u : List (Option Val)} {a : Act}
    (h : (lifeSys P n).toProgram.step t u = some a) :
    lifeTab P t u = some a ∧ stopped (lifeTab P) t u = false ∧ t ∈ P.threads := by
  rw [step_eq] at h
  split_ifs at h with hc
  simp only [not_or, not_le, not_not, Bool.not_eq_true] at hc
  exact ⟨h, hc.2.2, hc.2.1⟩

theorem stopped_false_iff {f : Tid → List (Option Val) → Option Act} {t : Tid}
    {u : List (Option Val)} :
    stopped f t u = false ↔ ∀ i < u.length, isStop (f t (u.take i)) = false := by
  unfold stopped
  simp [List.any_eq_false]

section graph

variable {n : ℕ} {G : Graph}

theorem ev_tab (hE : (lifeSys P n).toProgram.Exec G) {e : TEv} (he : e ∈ G.events) :
    lifeTab P e.tid (G.traceBefore e.tid e.idx) = some e.act ∧
      stopped (lifeTab P) e.tid (G.traceBefore e.tid e.idx) = false ∧ e.tid ∈ P.threads :=
  step_some (hE.2 e he)

theorem traceBefore_take (G : Graph) (t : Tid) {i j : ℕ} (hij : i ≤ j) :
    (G.traceBefore t j).take i = G.traceBefore t i := by
  unfold Graph.traceBefore
  rw [← List.map_take, List.take_range, Nat.min_eq_left hij]

/-- The trace before a later event extends the trace before an earlier one by the value
of the earlier event. -/
theorem traceBefore_split (hG : G.Wf) {e f : TEv} (he : e ∈ G.events) (_htid : f.tid = e.tid)
    (hlt : e.idx < f.idx) :
    ∃ w, G.traceBefore e.tid f.idx = G.traceBefore e.tid e.idx ++ G.ret e :: w := by
  have h1 := traceBefore_take G e.tid (Nat.succ_le_of_lt hlt)
  rw [Graph.traceBefore_succ, hG.evAt_eq_some he] at h1
  refine ⟨(G.traceBefore e.tid f.idx).drop (e.idx + 1), ?_⟩
  conv_lhs => rw [← List.take_append_drop (e.idx + 1) (G.traceBefore e.tid f.idx), h1]
  simp

end graph

/-! ### The body: invariant and actions -/

/-- The invariant of a body state of thread `t`: its calls are calls of `t`, and a pending
acquire is of a lock location. -/
structure Inv (P : LProg) (t : Tid) (s : TState) : Prop where
  ops_sub : ∀ c ∈ s.ops, c ∈ P.code t
  acq : ∀ l, s.phase = .acquire l → P.isLock l = true

theorem inv_init (t : Tid) : Inv P t (TState.init (P.code t)) :=
  ⟨fun _ h => h, fun l h => by simp [TState.init] at h⟩

theorem inv_next (hF : Frag P) {t : Tid} (ht : t ∈ P.threads) {s : TState} (hs : Inv P t s)
    (v : Option Val) : Inv P t (s.next v) := by
  obtain ⟨hops, hacq⟩ := hs
  rcases s with ⟨ops, holds, ph⟩
  cases ph with
  | acquire l => exact ⟨hops, fun l' h => by simp [TState.next] at h⟩
  | blocking => exact ⟨hops, hacq⟩
  | done => exact ⟨hops, hacq⟩
  | ready =>
    cases ops with
    | nil => exact ⟨by simp [TState.next], fun l h => by simp [TState.next] at h⟩
    | cons c rest =>
      have hc := hops c (by simp)
      have hrest : ∀ x ∈ rest, x ∈ P.code t := fun x hx => hops x (by simp [hx])
      have hdrop : ∀ k, ∀ x ∈ rest.drop k, x ∈ P.code t :=
        fun k x hx => hrest x (List.mem_of_mem_drop hx)
      have hok := hF.calls t ht c hc
      cases c with
      | lock l =>
        simp only [TState.next]
        split_ifs
        · exact ⟨hrest, fun l' h => by
            simp only [TPhase.acquire.injEq] at h; subst h; simpa [callOk] using hok⟩
        · exact ⟨hrest, fun l' h => by simp at h⟩
        · exact ⟨hrest, fun l' h => by simp at h⟩
      | tryLock l k =>
        simp only [TState.next]
        split_ifs
        · exact ⟨hrest, fun l' h => by
            simp only [TPhase.acquire.injEq] at h; subst h; simpa [callOk] using hok⟩
        · exact ⟨hdrop k, fun l' h => by simp at h⟩
        · exact ⟨hrest, fun l' h => by simp at h⟩
      | unlock l =>
        simp only [TState.next]
        split_ifs
        · exact ⟨hrest, fun l' h => by simp at h⟩
        · exact ⟨hrest, fun l' h => by simp at h⟩
      | join u =>
        simp only [TState.next]
        split_ifs
        · exact ⟨hrest, fun l' h => by simp at h⟩
        · exact ⟨hrest, fun l' h => by simp at h⟩
      | assume x w =>
        simp only [TState.next]
        split_ifs
        · exact ⟨hrest, fun l' h => by simp at h⟩
        · exact ⟨hrest, fun l' h => by simp at h⟩
      | rd x => exact ⟨hrest, fun l' h => by simp [TState.next] at h⟩
      | wr x v => exact ⟨hrest, fun l' h => by simp [TState.next] at h⟩
      | start u => exact ⟨hrest, fun l' h => by simp [TState.next] at h⟩

theorem inv_tState (hF : Frag P) {t : Tid} (ht : t ∈ P.threads) (u : List (Option Val)) :
    Inv P t (tState (P.code t) u) := by
  induction u using List.reverseRecOn with
  | nil => exact inv_init t
  | append_singleton u v ih => rw [tState_append]; exact inv_next hF ht ih v

/-- A write of a lifecycle location by a body: a start (value `1`, of a declared non-root
thread other than the writer) or the finish of the writer (value `2`, all calls done). -/
theorem act_write_st (hF : Frag P) {t : Tid} (ht : t ∈ P.threads) {s : TState}
    (hs : Inv P t s) {x : Loc} {v : Val} (ha : s.act P.st t = some (.write x v)) {w : Tid}
    (hw : w ∈ P.threads) (hx : x = P.st w) :
    (v = 1 ∧ s.phase = .ready ∧ s.ops.head? = some (.start w) ∧ P.isRoot w = false ∧ w ≠ t) ∨
      (v = 2 ∧ w = t ∧ s.phase = .ready ∧ s.ops = []) := by
  obtain ⟨hops, hacq⟩ := hs
  rcases s with ⟨ops, holds, ph⟩
  cases ph with
  | acquire l =>
    simp only [TState.act, Option.some.injEq, Act.write.injEq] at ha
    have := hacq l rfl
    rw [ha.1, hx, hF.st_not_lock w hw] at this
    cases this
  | blocking => simp [TState.act] at ha
  | done => simp [TState.act] at ha
  | ready =>
    cases ops with
    | nil =>
      simp only [TState.act, Option.some.injEq, Act.write.injEq] at ha
      obtain ⟨h1, h2⟩ := ha
      right
      exact ⟨h2.symm, (hF.st_inj t ht w hw (h1.trans hx)).symm, rfl, rfl⟩
    | cons c rest =>
      have hok := hF.calls t ht c (hops c (by simp))
      cases c with
      | lock l => simp only [TState.act] at ha; split_ifs at ha <;> simp at ha
      | tryLock l k => simp only [TState.act] at ha; split_ifs at ha <;> simp at ha
      | unlock l =>
        simp only [TState.act] at ha
        split_ifs at ha <;> simp only [Option.some.injEq, Act.write.injEq, reduceCtorEq] at ha
        have : P.isLock l = true := by simpa [callOk] using hok
        rw [ha.1, hx, hF.st_not_lock w hw] at this
        cases this
      | rd y => simp [TState.act] at ha
      | wr y v' =>
        simp only [TState.act, Option.some.injEq, Act.write.injEq] at ha
        have : P.isData y = true := by simpa [callOk] using hok
        rw [ha.1, hx, hF.isData_st hw] at this
        cases this
      | start u =>
        simp only [TState.act, Option.some.injEq, Act.write.injEq] at ha
        obtain ⟨h1, h2⟩ := ha
        simp only [callOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hok
        have hu := hF.st_inj u hok.1.1 w hw (h1.trans hx)
        subst hu
        left
        exact ⟨h2.symm, rfl, rfl, hok.1.2, hok.2⟩
      | join u => simp [TState.act] at ha
      | assume y w' => simp [TState.act] at ha

/-- A read of a lifecycle location by a body: a join of a declared non-root thread other
than the reader. -/
theorem act_read_st (hF : Frag P) {t : Tid} (ht : t ∈ P.threads) {s : TState}
    (hs : Inv P t s) {x : Loc} (ha : s.act P.st t = some (.read x)) {w : Tid}
    (hw : w ∈ P.threads) (hx : x = P.st w) :
    P.isRoot w = false ∧ w ≠ t ∧ s.phase = .ready ∧ s.ops.head? = some (.join w) := by
  obtain ⟨hops, hacq⟩ := hs
  rcases s with ⟨ops, holds, ph⟩
  cases ph with
  | acquire l => simp [TState.act] at ha
  | blocking => simp [TState.act] at ha
  | done => simp [TState.act] at ha
  | ready =>
    cases ops with
    | nil => simp [TState.act] at ha
    | cons c rest =>
      have hok := hF.calls t ht c (hops c (by simp))
      cases c with
      | lock l =>
        simp only [TState.act] at ha
        split_ifs at ha <;> simp only [Option.some.injEq, Act.read.injEq, reduceCtorEq] at ha
        have : P.isLock l = true := by simpa [callOk] using hok
        rw [ha, hx, hF.st_not_lock w hw] at this
        cases this
      | tryLock l k =>
        simp only [TState.act] at ha
        split_ifs at ha <;> simp only [Option.some.injEq, Act.read.injEq, reduceCtorEq] at ha
        have : P.isLock l = true := by simpa [callOk] using hok
        rw [ha, hx, hF.st_not_lock w hw] at this
        cases this
      | unlock l => simp only [TState.act] at ha; split_ifs at ha <;> simp at ha
      | rd y =>
        simp only [TState.act, Option.some.injEq, Act.read.injEq] at ha
        have : P.isSt y = false := by simpa [callOk] using hok
        rw [ha, hx, hF.isSt_st hw] at this
        cases this
      | wr y v' => simp [TState.act] at ha
      | start u => simp [TState.act] at ha
      | join u =>
        simp [TState.act] at ha
        simp only [callOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hok
        have hu := hF.st_inj u hok.1.1 w hw (ha.trans hx)
        subst hu
        exact ⟨hok.1.2, hok.2, rfl, rfl⟩
      | assume y w' =>
        simp only [TState.act, Option.some.injEq, Act.read.injEq] at ha
        have : P.isData y = true := by simpa [callOk] using hok
        rw [ha, hx, hF.isData_st hw] at this
        cases this

/-! ### The wrapper -/

/-- The body trace of a trace: the trace of a root, the trace without the start-read
otherwise. -/
def bodyOf (P : LProg) (t : Tid) (u : List (Option Val)) : List (Option Val) :=
  if P.isRoot t then u else u.tail

/-- The cases of the compiled table. -/
theorem lifeTab_cases {t : Tid} {u : List (Option Val)} {a : Act} (h : lifeTab P t u = some a) :
    (P.isRoot t = false ∧ u = [] ∧ a = .read (P.st t)) ∨
      (P.isRoot t = false ∧ u = [some 0] ∧ a = .block) ∨
      ((P.isRoot t = true ∨ (P.isRoot t = false ∧ ∃ v rest, u = v :: rest ∧ v ≠ some 0)) ∧
        (tState (P.code t) (bodyOf P t u)).act P.st t = some a) := by
  unfold lifeTab at h
  by_cases hr : P.isRoot t = true
  · simp only [hr, ↓reduceIte] at h
    exact Or.inr (Or.inr ⟨Or.inl hr, by simpa [bodyOf, hr] using h⟩)
  · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h
    have hr' : P.isRoot t = false := by simpa using hr
    cases u with
    | nil => simp at h; exact Or.inl ⟨hr', rfl, h.symm⟩
    | cons v rest =>
      by_cases hv : v = some 0
      · simp only [hv, ↓reduceIte] at h
        split_ifs at h with hrest
        · simp at h; subst hrest hv; exact Or.inr (Or.inl ⟨hr', rfl, h.symm⟩)
      · simp only [hv, ↓reduceIte] at h
        exact Or.inr (Or.inr ⟨Or.inr ⟨hr', v, rest, rfl, hv⟩, by simpa [bodyOf, hr'] using h⟩)

/-- A write of the compiled table is a write of the body, and the table on any extension of
the trace is the body on the extended body trace. -/
theorem lifeTab_write {t : Tid} {u : List (Option Val)} {x : Loc} {v : Val}
    (h : lifeTab P t u = some (.write x v)) :
    (tState (P.code t) (bodyOf P t u)).act P.st t = some (.write x v) ∧
      ∀ w, lifeTab P t (u ++ w) = (tState (P.code t) (bodyOf P t u ++ w)).act P.st t := by
  rcases lifeTab_cases h with ⟨-, -, h'⟩ | ⟨-, -, h'⟩ | ⟨hc, h'⟩
  · cases h'
  · cases h'
  · refine ⟨h', fun w => ?_⟩
    rcases hc with hr | ⟨hr, v0, rest, rfl, hv⟩
    · simp [lifeTab, bodyOf, hr]
    · simp [lifeTab, bodyOf, hr, hv]

theorem foldl_next_done (w : List (Option Val)) (s : TState) (hs : s.phase = .done) :
    w.foldl TState.next s = s := by
  induction w generalizing s with
  | nil => rfl
  | cons v w ih =>
    rw [List.foldl_cons]
    have : s.next v = s := by
      rcases s with ⟨ops, holds, ph⟩
      simp only at hs
      subst hs
      rfl
    rw [this, ih s hs]

theorem tState_append_list (ops : List TOp) (u w : List (Option Val)) :
    tState ops (u ++ w) = w.foldl TState.next (tState ops u) := by
  simp [tState, List.foldl_append]

/-- After the finish write the table has no action. -/
theorem lifeTab_after_finish (hF : Frag P) {t : Tid} (ht : t ∈ P.threads)
    {u : List (Option Val)} (h : lifeTab P t u = some (.write (P.st t) 2)) (v : Option Val)
    (w : List (Option Val)) : lifeTab P t (u ++ v :: w) = none := by
  obtain ⟨h1, h2⟩ := lifeTab_write h
  rw [h2]
  rcases act_write_st hF ht (inv_tState hF ht _) h1 ht rfl with
    ⟨h3, -⟩ | ⟨-, -, hph, hops⟩
  · cases h3
  · rw [tState_append_list, List.foldl_cons]
    set s := tState (P.code t) (bodyOf P t u)
    have hd : (s.next v).phase = .done := by
      rcases hs : s with ⟨ops, holds, ph⟩
      rw [hs] at hph hops
      simp only at hph hops
      subst hph hops
      rfl
    rw [foldl_next_done w _ hd]
    rcases hs : s.next v with ⟨ops, holds, ph⟩
    rw [hs] at hd
    simp only at hd
    subst hd
    rfl

/-! ### The number of `start u` calls left -/

theorem count_next_le (u : Tid) (s : TState) (v : Option Val) :
    (s.next v).ops.count (.start u) ≤ s.ops.count (.start u) := by
  rcases s with ⟨ops, holds, ph⟩
  cases ph with
  | acquire l => simp [TState.next]
  | blocking => simp [TState.next]
  | done => simp [TState.next]
  | ready =>
    cases ops with
    | nil => simp [TState.next]
    | cons c rest =>
      have h1 : rest.count (.start u) ≤ (c :: rest).count (.start u) := by
        rw [List.count_cons]; omega
      have h2 : ∀ k, (rest.drop k).count (.start u) ≤ (c :: rest).count (.start u) :=
        fun k => le_trans ((List.drop_sublist k rest).count_le _) h1
      cases c <;> simp only [TState.next] <;> (try split_ifs) <;>
        first | exact h1 | exact h2 _

theorem count_foldl_le (u : Tid) (w : List (Option Val)) (s : TState) :
    (w.foldl TState.next s).ops.count (.start u) ≤ s.ops.count (.start u) := by
  induction w generalizing s with
  | nil => exact le_rfl
  | cons v w ih => exact le_trans (ih _) (count_next_le u s v)

/-- The start write `start u` uses up the only `start u` call. -/
theorem count_next_start (u : Tid) (s : TState) (v : Option Val) (hph : s.phase = .ready)
    (hh : s.ops.head? = some (.start u)) :
    (s.next v).ops.count (.start u) + 1 = s.ops.count (.start u) := by
  rcases s with ⟨ops, holds, ph⟩
  simp only at hph hh
  subst hph
  cases ops with
  | nil => simp at hh
  | cons c rest =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    simp [TState.next]

/-! ### Blocking in the body -/

theorem act_block {st : Tid → Loc} {me : Tid} {s : TState} (h : s.act st me = some .block) :
    s.phase = .blocking := by
  rcases s with ⟨ops, holds, ph⟩
  cases ph with
  | blocking => rfl
  | acquire l => simp [TState.act] at h
  | done => simp [TState.act] at h
  | ready =>
    cases ops with
    | nil => simp [TState.act] at h
    | cons c rest =>
      cases c <;> simp only [TState.act] at h <;> (try split_ifs at h) <;> simp at h

theorem next_blocking {s : TState} {v : Option Val} (h : (s.next v).phase = .blocking)
    (hs : s.phase ≠ .blocking) :
    s.phase = .ready ∧
      ((∃ l rest, s.ops = .lock l :: rest ∧ s.holds l = 0 ∧ v ≠ some 0) ∨
        (∃ w rest, s.ops = .join w :: rest ∧ v = some 1) ∨
        (∃ x w rest, s.ops = .assume x w :: rest ∧ v ≠ some w)) := by
  rcases s with ⟨ops, holds, ph⟩
  cases ph with
  | blocking => exact absurd rfl hs
  | acquire l => simp [TState.next] at h
  | done => simp [TState.next] at h
  | ready =>
    refine ⟨rfl, ?_⟩
    cases ops with
    | nil => simp [TState.next] at h
    | cons c rest =>
      cases c <;> simp only [TState.next] at h <;> (try split_ifs at h) <;> simp_all

/-- The kinds of a `block` (the rows of the kind table of §3): the start-read of value `0`
at index `0` of a non-root thread; a lock read of a value other than `0`; a join read of
`1` of a declared non-root thread other than the reader; a read of a data location. -/
def BlockKinds (P : LProg) (t : Tid) (i : ℕ) (x : Loc) (v : Option Val) : Prop :=
  (i = 0 ∧ P.isRoot t = false ∧ x = P.st t ∧ v = some 0) ∨
    (P.isLock x = true ∧ v ≠ some 0) ∨
    (∃ w ∈ P.threads, w ≠ t ∧ P.isRoot w = false ∧ x = P.st w ∧ v = some 1) ∨
    P.isData x = true

theorem act_ready_cons {st : Tid → Loc} {me : Tid} {s : TState} {c : TOp} {rest : List TOp}
    (hp : s.phase = .ready) (ho : s.ops = c :: rest) :
    s.act st me = TState.act st me ⟨c :: rest, s.holds, .ready⟩ := by
  rcases s with ⟨o, h, p⟩
  simp only at hp ho
  subst hp ho
  rfl

/-- The call that a body `block` comes from, in the body state `s` just before the read
of value `v` of location `x`: a `lock x` of a free lock read as held, a `join w` of a
declared non-root thread `w ≠ t` read as `1`, or an `assume x w` of a data location read
as a value other than `w`. -/
def BlockSrc (P : LProg) (t : Tid) (s : TState) (x : Loc) (v : Option Val) : Prop :=
  s.phase = .ready ∧
    ((∃ rest, s.ops = .lock x :: rest ∧ s.holds x = 0 ∧ P.isLock x = true ∧ v ≠ some 0) ∨
      (∃ w rest, s.ops = .join w :: rest ∧ x = P.st w ∧ w ∈ P.threads ∧ w ≠ t ∧
        P.isRoot w = false ∧ v = some 1) ∨
      (∃ w rest, s.ops = .assume x w :: rest ∧ P.isData x = true ∧ v ≠ some w))

theorem BlockSrc.kinds {t : Tid} {s : TState} {x : Loc} {v : Option Val}
    (h : BlockSrc P t s x v) :
    (P.isLock x = true ∧ v ≠ some 0) ∨
      (∃ w ∈ P.threads, w ≠ t ∧ P.isRoot w = false ∧ x = P.st w ∧ v = some 1) ∨
      P.isData x = true := by
  rcases h.2 with ⟨-, -, -, h1, h2⟩ | ⟨w, -, -, h1, h2, h3, h4, h5⟩ | ⟨-, -, -, h1, -⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr (Or.inl ⟨w, h2, h3, h4, h1, h5⟩)
  · exact Or.inr (Or.inr h1)

/-- A `block` of a body follows the read of a `lock`, `join` or `assume` call. -/
theorem tState_block (hF : Frag P) {t : Tid} (ht : t ∈ P.threads) (u : List (Option Val))
    (hs : ∀ i < u.length, isStop ((tState (P.code t) (u.take i)).act P.st t) = false)
    (hb : (tState (P.code t) u).act P.st t = some .block) :
    ∃ u' v x, u = u' ++ [v] ∧ (tState (P.code t) u').act P.st t = some (.read x) ∧
      BlockSrc P t (tState (P.code t) u') x v := by
  have hph := act_block hb
  rcases List.eq_nil_or_concat u with rfl | ⟨u', v, rfl⟩
  · simp [tState, TState.init] at hph
  · simp only [List.concat_eq_append] at hs hb hph ⊢
    rw [tState_append] at hph
    set s := tState (P.code t) u' with hsdef
    have hns : s.phase ≠ .blocking := by
      intro h
      have h1 := hs u'.length (by simp)
      rw [List.take_append_of_le_length le_rfl, List.take_length, ← hsdef] at h1
      have : s.act P.st t = some .block := by
        rcases hs' : s with ⟨ops, holds, ph⟩
        rw [hs'] at h
        simp only at h
        subst h
        rfl
      rw [this] at h1
      simp [isStop] at h1
    have hinv := inv_tState hF ht u'
    rw [← hsdef] at hinv
    obtain ⟨hrd, hc⟩ := next_blocking hph hns
    refine ⟨u', v, ?_⟩
    rcases hc with ⟨l, rest, hops, hh, hv⟩ | ⟨w, rest, hops, hv⟩ | ⟨x, w, rest, hops, hv⟩
    · have hok := hF.calls t ht (.lock l) (hinv.ops_sub (.lock l) (by rw [hops]; simp))
      refine ⟨l, rfl, ?_, hrd, Or.inl ⟨rest, hops, hh, by simpa [callOk] using hok, hv⟩⟩
      rw [← hsdef, act_ready_cons hrd hops]
      simp [TState.act, hh]
    · have hok := hF.calls t ht (.join w) (hinv.ops_sub (.join w) (by rw [hops]; simp))
      simp only [callOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hok
      refine ⟨P.st w, rfl, ?_, hrd,
        Or.inr (Or.inl ⟨w, rest, hops, rfl, hok.1.1, hok.2, hok.1.2, hv⟩)⟩
      rw [← hsdef, act_ready_cons hrd hops]
      simp [TState.act]
    · have hok := hF.calls t ht (.assume x w) (hinv.ops_sub (.assume x w) (by rw [hops]; simp))
      refine ⟨x, rfl, ?_, hrd, Or.inr (Or.inr ⟨w, rest, hops, by simpa [callOk] using hok, hv⟩)⟩
      rw [← hsdef, act_ready_cons hrd hops]
      simp [TState.act]

theorem lifeTab_root {t : Tid} (hr : P.isRoot t = true) (u : List (Option Val)) :
    lifeTab P t u = (tState (P.code t) u).act P.st t := by
  simp [lifeTab, hr]

theorem lifeTab_nil {t : Tid} (hr : P.isRoot t = false) :
    lifeTab P t [] = some (.read (P.st t)) := by
  simp [lifeTab, hr]

theorem lifeTab_cons {t : Tid} (hr : P.isRoot t = false) {v : Option Val} (hv : v ≠ some 0)
    (u : List (Option Val)) : lifeTab P t (v :: u) = (tState (P.code t) u).act P.st t := by
  simp [lifeTab, hr, hv]

/-- A `block` of the compiled table follows a read of one of the four kinds. -/
theorem lifeTab_block (hF : Frag P) {t : Tid} (ht : t ∈ P.threads) {u : List (Option Val)}
    (h : lifeTab P t u = some .block) (hs : stopped (lifeTab P) t u = false) :
    ∃ u' v x, u = u' ++ [v] ∧ lifeTab P t u' = some (.read x) ∧
      BlockKinds P t u'.length x v := by
  have hs' := stopped_false_iff.mp hs
  rcases lifeTab_cases h with ⟨-, -, h'⟩ | ⟨hr, rfl, -⟩ | ⟨hc, h'⟩
  · cases h'
  · exact ⟨[], some 0, P.st t, rfl, lifeTab_nil hr, Or.inl ⟨rfl, hr, rfl, rfl⟩⟩
  · rcases hc with hr | ⟨hr, v0, rest, rfl, hv0⟩
    · have hb : (tState (P.code t) u).act P.st t = some .block := by
        simpa [bodyOf, hr] using h'
      have hsb : ∀ i < u.length, isStop ((tState (P.code t) (u.take i)).act P.st t) = false :=
        fun i hi => by rw [← lifeTab_root hr]; exact hs' i hi
      obtain ⟨u', v, x, rfl, hrd, hk⟩ := tState_block hF ht u hsb hb
      exact ⟨u', v, x, rfl, by rw [lifeTab_root hr]; exact hrd, Or.inr hk.kinds⟩
    · have hb : (tState (P.code t) rest).act P.st t = some .block := by
        simpa [bodyOf, hr] using h'
      have hsb : ∀ i < rest.length,
          isStop ((tState (P.code t) (rest.take i)).act P.st t) = false := by
        intro i hi
        have := hs' (i + 1) (by simp; omega)
        rwa [List.take_succ_cons, lifeTab_cons hr hv0] at this
      obtain ⟨u', v, x, rfl, hrd, hk⟩ := tState_block hF ht rest hsb hb
      exact ⟨v0 :: u', v, x, rfl, by rw [lifeTab_cons hr hv0]; exact hrd, Or.inr hk.kinds⟩

/-- The body state of thread `t` after the trace `u`. -/
def bodyState (P : LProg) (t : Tid) (u : List (Option Val)) : TState :=
  tState (P.code t) (bodyOf P t u)

/-- A `block` of the compiled table, with its provenance: the start wait, or the block of
the call at the head of the body state before the read (`BlockSrc`), whose state after
the read is the state of the block; the flag of the read is the body's. -/
theorem lifeTab_block_src (hF : Frag P) {t : Tid} (ht : t ∈ P.threads) {u : List (Option Val)}
    (h : lifeTab P t u = some .block) (hs : stopped (lifeTab P) t u = false) :
    ∃ u' v x, u = u' ++ [v] ∧ lifeTab P t u' = some (.read x) ∧
      ((u' = [] ∧ P.isRoot t = false ∧ x = P.st t ∧ v = some 0) ∨
        (BlockSrc P t (bodyState P t u') x v ∧
          bodyState P t (u' ++ [v]) = (bodyState P t u').next v ∧
          lifeFlag P t u' = (bodyState P t u').isEx)) := by
  have hs' := stopped_false_iff.mp hs
  rcases lifeTab_cases h with ⟨-, -, h'⟩ | ⟨hr, rfl, -⟩ | ⟨hc, h'⟩
  · cases h'
  · exact ⟨[], some 0, P.st t, rfl, lifeTab_nil hr, Or.inl ⟨rfl, hr, rfl, rfl⟩⟩
  · rcases hc with hr | ⟨hr, v0, rest, rfl, hv0⟩
    · have hb : (tState (P.code t) u).act P.st t = some .block := by
        simpa [bodyOf, hr] using h'
      have hsb : ∀ i < u.length, isStop ((tState (P.code t) (u.take i)).act P.st t) = false :=
        fun i hi => by rw [← lifeTab_root hr]; exact hs' i hi
      obtain ⟨u', v, x, rfl, hrd, hk⟩ := tState_block hF ht u hsb hb
      refine ⟨u', v, x, rfl, by rw [lifeTab_root hr]; exact hrd, Or.inr ⟨?_, ?_, ?_⟩⟩
      · simpa [bodyState, bodyOf, hr] using hk
      · simp [bodyState, bodyOf, hr, tState_append]
      · simp [bodyState, bodyOf, lifeFlag, hr]
    · have hb : (tState (P.code t) rest).act P.st t = some .block := by
        simpa [bodyOf, hr] using h'
      have hsb : ∀ i < rest.length,
          isStop ((tState (P.code t) (rest.take i)).act P.st t) = false := by
        intro i hi
        have := hs' (i + 1) (by simp; omega)
        rwa [List.take_succ_cons, lifeTab_cons hr hv0] at this
      obtain ⟨u', v, x, rfl, hrd, hk⟩ := tState_block hF ht rest hsb hb
      refine ⟨v0 :: u', v, x, rfl, by rw [lifeTab_cons hr hv0]; exact hrd, Or.inr ⟨?_, ?_, ?_⟩⟩
      · simpa [bodyState, bodyOf, hr] using hk
      · simp [bodyState, bodyOf, hr, tState_append]
      · simp [bodyState, bodyOf, lifeFlag, hr, hv0]

/-! ### The end of a body -/

theorem act_none_done {st : Tid → Loc} {me : Tid} {s : TState} (h : s.act st me = none) :
    s.phase = .done := by
  rcases s with ⟨ops, holds, ph⟩
  cases ph with
  | done => rfl
  | acquire l => simp [TState.act] at h
  | blocking => simp [TState.act] at h
  | ready =>
    cases ops with
    | nil => simp [TState.act] at h
    | cons c rest =>
      cases c <;> simp only [TState.act] at h <;> (try split_ifs at h) <;> simp at h

theorem next_done {s : TState} {v : Option Val} (h : (s.next v).phase = .done)
    (hs : s.phase ≠ .done) : s.phase = .ready ∧ s.ops = [] := by
  rcases s with ⟨ops, holds, ph⟩
  cases ph with
  | done => exact absurd rfl hs
  | acquire l => simp [TState.next] at h
  | blocking => simp [TState.next] at h
  | ready =>
    refine ⟨rfl, ?_⟩
    cases ops with
    | nil => rfl
    | cons c rest =>
      cases c <;> simp only [TState.next] at h <;> (try split_ifs at h) <;> simp at h

/-- A body that has ended performed its finish write at an earlier position. -/
theorem tState_finish_of_done (st : Tid → Loc) (me : Tid) (ops : List TOp)
    (u : List (Option Val)) (h : (tState ops u).phase = .done) :
    ∃ i < u.length, (tState ops (u.take i)).act st me = some (.write (st me) 2) := by
  induction u using List.reverseRecOn with
  | nil => simp [tState, TState.init] at h
  | append_singleton u v ih =>
    rw [tState_append] at h
    by_cases hd : (tState ops u).phase = .done
    · obtain ⟨i, hi, hact⟩ := ih hd
      exact ⟨i, by simp; omega, by rw [List.take_append_of_le_length (by omega)]; exact hact⟩
    · obtain ⟨hr, ho⟩ := next_done h hd
      refine ⟨u.length, by simp, ?_⟩
      rw [List.take_append_of_le_length le_rfl, List.take_length]
      rcases hs : tState ops u with ⟨ops', holds', ph'⟩
      rw [hs] at hr ho
      simp only at hr ho
      subst hr ho
      rfl

/-! ### Graph-level lemmas -/

section graph

variable {n : ℕ} {G : Graph}

theorem mem_eq (hE : (lifeSys P n).toProgram.Exec G) : G.mem = lifeMem P := hE.1

theorem valAt_th {x : Loc} {s : TEv} {v : Val} (hsa : s.act = .write x v) :
    G.valAt x (.th s) = v := by
  simp [Graph.valAt, hsa]

theorem po_th {e e' : TEv} (he : e ∈ G.events) (he' : e' ∈ G.events) (ht : e.tid = e'.tid)
    (hi : e.idx < e'.idx) : G.po (.th e) (.th e') := ⟨he, he', ht, hi⟩

theorem rfRel_th {e : TEv} {w : Ev} (he : e ∈ G.events) (h : G.rf e = some w) :
    G.rfRel w (.th e) := ⟨e, rfl, he, h⟩

/-- A read with its source and value. -/
theorem ret_read (hG : G.Wf) {e : TEv} (he : e ∈ G.events) {x : Loc}
    (hact : e.act = .read x) :
    ∃ w, G.rf e = some w ∧ G.IsWriteTo x w ∧ G.ret e = some (G.valAt x w) := by
  obtain ⟨w, hw, hw'⟩ := hG.rf_read e he x hact
  exact ⟨w, hw, hw', by simp [Graph.ret, hact, hw]⟩

/-- Writes of a lifecycle location: a start (value `1`, by a thread whose code has the
`start` call, of a non-root thread other than the writer), or the finish of the owner
(value `2`). -/
theorem write_st (hF : Frag P) (hE : (lifeSys P n).toProgram.Exec G) {e : TEv}
    (he : e ∈ G.events) {x : Loc} {v : Val} (hact : e.act = .write x v) {w : Tid}
    (hw : w ∈ P.threads) (hx : x = P.st w) :
    (v = 1 ∧ TOp.start w ∈ P.code e.tid ∧ P.isRoot w = false ∧ w ≠ e.tid) ∨
      (v = 2 ∧ w = e.tid) := by
  obtain ⟨h1, -, ht⟩ := ev_tab hE he
  rw [hact] at h1
  have hb := (lifeTab_write h1).1
  rcases act_write_st hF ht (inv_tState hF ht _) hb hw hx with
    ⟨h2, -, h3, h4, h5⟩ | ⟨h2, h3, -⟩
  · exact Or.inl ⟨h2, (inv_tState hF ht _).ops_sub _ (List.mem_of_mem_head? h3), h4, h5⟩
  · exact Or.inr ⟨h2, h3⟩

/-- Every write of a lifecycle location writes `1` or `2`. -/
theorem st_write_val (hF : Frag P) (hE : (lifeSys P n).toProgram.Exec G) {e : TEv}
    (he : e ∈ G.events) {w : Tid} (hw : w ∈ P.threads) {v : Val}
    (hact : e.act = .write (P.st w) v) : v = 1 ∨ v = 2 := by
  rcases write_st hF hE he hact hw rfl with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

/-- A read of the lifecycle location of another thread is a join read: its target is not a
root. -/
theorem read_st_other (hF : Frag P) (hE : (lifeSys P n).toProgram.Exec G) {e : TEv}
    (he : e ∈ G.events) {w : Tid} (hw : w ∈ P.threads) (hact : e.act = .read (P.st w))
    (hne : e.tid ≠ w) : P.isRoot w = false := by
  obtain ⟨h1, -, ht⟩ := ev_tab hE he
  rw [hact] at h1
  rcases lifeTab_cases h1 with ⟨-, -, h'⟩ | ⟨-, -, h'⟩ | ⟨-, h'⟩
  · simp only [Act.read.injEq] at h'
    exact absurd (hF.st_inj _ hw _ ht h').symm hne
  · cases h'
  · exact (act_read_st hF ht (inv_tState hF ht _) h' hw rfl).1

/-- **Lemma 4** (and the invariant "only `init` gives a lifecycle location the value
`0`"): a read of value `0` of a lifecycle location reads `init`. -/
theorem lc_lemma4 (hF : Frag P) (hG : G.Wf) (hE : (lifeSys P n).toProgram.Exec G) {e : TEv}
    (he : e ∈ G.events) {w : Tid} (hw : w ∈ P.threads) (hact : e.act = .read (P.st w))
    (hv : G.ret e = some 0) : G.rf e = some .init := by
  obtain ⟨src, hs, hsw, hr⟩ := ret_read hG he hact
  cases src with
  | init => exact hs
  | th s =>
    obtain ⟨hsm, v, hsa⟩ := hsw
    rw [hv] at hr
    rw [valAt_th hsa] at hr
    have hv0 : v = 0 := (Option.some.inj hr).symm
    rcases st_write_val hF hE hsm hw hsa with h | h <;> rw [hv0] at h <;>
      exact absurd h (by decide)

/-- **Lemma 6**: a join read of `1` reads a start write of its target. -/
theorem lc_lemma6 (hF : Frag P) (hG : G.Wf) (hE : (lifeSys P n).toProgram.Exec G) {j : TEv}
    (hj : j ∈ G.events) {w : Tid} (hw : w ∈ P.threads) (hact : j.act = .read (P.st w))
    (hne : j.tid ≠ w) (hv : G.ret j = some 1) :
    ∃ s ∈ G.events, G.rf j = some (.th s) ∧ s.act = .write (P.st w) 1 ∧
      TOp.start w ∈ P.code s.tid := by
  have hr := read_st_other hF hE hj hw hact hne
  obtain ⟨src, hs, hsw, hret⟩ := ret_read hG hj hact
  cases src with
  | init =>
    rw [hv] at hret
    simp [Graph.valAt, mem_eq hE, hF.mem_st hw, hr] at hret
  | th s =>
    obtain ⟨hsm, v, hsa⟩ := hsw
    rw [hv] at hret
    rw [valAt_th hsa] at hret
    have hv1 : v = 1 := (Option.some.inj hret).symm
    subst hv1
    rcases write_st hF hE hsm hsa hw rfl with ⟨-, hc, -⟩ | ⟨h, -⟩
    · exact ⟨s, hsm, hs, hsa, hc⟩
    · exact absurd h (by decide)

/-- The finish write is the last event of its thread. -/
theorem finish_last (hF : Frag P) (hG : G.Wf) (hE : (lifeSys P n).toProgram.Exec G)
    {f : TEv} (hf : f ∈ G.events) (hact : f.act = .write (P.st f.tid) 2) {e : TEv}
    (he : e ∈ G.events) (ht : e.tid = f.tid) : e.idx ≤ f.idx := by
  by_contra hlt
  obtain ⟨w, hw⟩ := traceBefore_split hG hf ht (Nat.lt_of_not_le hlt)
  obtain ⟨h1, -, htm⟩ := ev_tab hE hf
  rw [hact] at h1
  obtain ⟨h2, -, -⟩ := ev_tab hE he
  rw [ht, hw, lifeTab_after_finish hF htm h1] at h2
  cases h2

/-- **Lemma 3**: a join read of `2` reads the finish write of its target; the other events
of the target are po-before the finish, the later events of the joiner porf-after it. -/
theorem lc_lemma3 (hF : Frag P) (hG : G.Wf) (hE : (lifeSys P n).toProgram.Exec G) {j : TEv}
    (hj : j ∈ G.events) {w : Tid} (hw : w ∈ P.threads) (hact : j.act = .read (P.st w))
    (hv : G.ret j = some 2) :
    ∃ f ∈ G.events, G.rf j = some (.th f) ∧ f.act = .write (P.st w) 2 ∧ f.tid = w ∧
      (∀ e ∈ G.events, e.tid = w → e ≠ f → G.po (.th e) (.th f)) ∧
      ∀ e ∈ G.events, e.tid = j.tid → j.idx < e.idx → G.porf (.th f) (.th e) := by
  obtain ⟨src, hs, hsw, hret⟩ := ret_read hG hj hact
  cases src with
  | init =>
    rw [hv] at hret
    simp only [Graph.valAt, mem_eq hE, hF.mem_st hw] at hret
    split_ifs at hret <;> simp at hret
  | th f =>
    obtain ⟨hfm, v, hfa⟩ := hsw
    rw [hv] at hret
    rw [valAt_th hfa] at hret
    have hv2 : v = 2 := (Option.some.inj hret).symm
    subst hv2
    have hft : w = f.tid := by
      rcases write_st hF hE hfm hfa hw rfl with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h (by decide)
      · exact h
    refine ⟨f, hfm, hs, hfa, hft.symm, fun e he het hne => ?_, fun e he het hlt => ?_⟩
    · have hle := finish_last hF hG hE hfm (by rw [← hft]; exact hfa) he (het.trans hft)
      have hlt : e.idx < f.idx := by
        rcases Nat.lt_or_eq_of_le hle with h | h
        · exact h
        · exact absurd (hG.idx_inj e he f hfm (het.trans hft) h) hne
      exact po_th he hfm (het.trans hft) hlt
    · exact Relation.TransGen.head (Or.inr (rfRel_th hj hs))
        (Relation.TransGen.single (Or.inl (po_th hj he het.symm hlt)))

/-- The first event of a non-root thread is its start-read, and its value heads the trace
before any later event. -/
theorem start_read (hG : G.Wf) (hE : (lifeSys P n).toProgram.Exec G) {e : TEv}
    (he : e ∈ G.events) (hr : P.isRoot e.tid = false) (h1 : 1 ≤ e.idx) :
    ∃ r0 ∈ G.events, r0.tid = e.tid ∧ r0.idx = 0 ∧ r0.act = .read (P.st e.tid) ∧
      ∃ rest, G.traceBefore e.tid e.idx = G.ret r0 :: rest := by
  obtain ⟨r0, hr0, ht, hi⟩ := hG.idx_contig e he 0 (by omega)
  obtain ⟨hx, -, -⟩ := ev_tab hE hr0
  have h0 : G.traceBefore r0.tid r0.idx = [] := by rw [hi]; simp [Graph.traceBefore]
  rw [h0, ht, lifeTab_nil hr] at hx
  obtain ⟨w, hw⟩ := traceBefore_split hG hr0 ht.symm (by omega : r0.idx < e.idx)
  rw [hi, ht] at hw
  refine ⟨r0, hr0, ht, hi, (Option.some.inj hx).symm, w, ?_⟩
  rw [hw]
  simp [Graph.traceBefore]

/-- The events of a non-root thread whose start-read returned `0`: the start-read and, at
index `1`, a `block`. -/
theorem start_wait_events (hG : G.Wf) (hE : (lifeSys P n).toProgram.Exec G) {r0 : TEv}
    (hr0 : r0 ∈ G.events) (hr : P.isRoot r0.tid = false) (h0i : r0.idx = 0)
    (hv : G.ret r0 = some 0) {e : TEv} (he : e ∈ G.events) (het : e.tid = r0.tid) :
    e.idx ≤ 1 ∧ (e.idx = 1 → e.act = .block) := by
  by_cases h1 : e.idx = 0
  · omega
  · rw [← het] at hr
    obtain ⟨r1, hr1, ht1, hi1, -, rest, htr⟩ := start_read hG hE he hr (by omega)
    have hr01 : r1 = r0 := hG.idx_inj r1 hr1 r0 hr0 (ht1.trans het) (hi1.trans h0i.symm)
    subst hr01
    obtain ⟨hte, -, -⟩ := ev_tab hE he
    rw [htr, hv] at hte
    simp only [lifeTab, hr, Bool.false_eq_true, ↓reduceIte] at hte
    split_ifs at hte with hrest
    · have hl := Graph.traceBefore_length G e.tid e.idx
      rw [htr, hrest] at hl
      simp at hl hte
      exact ⟨by omega, fun _ => hte.symm⟩

/-- **Lemma 2**: a non-root thread with an event after its start-read other than its
start-wait `block` has its start-read reading a start write (by another thread). -/
theorem lc_lemma2 (hF : Frag P) (hG : G.Wf) (hsc : SC.cons G)
    (hE : (lifeSys P n).toProgram.Exec G) {e : TEv} (he : e ∈ G.events)
    (hr : P.isRoot e.tid = false) (h1 : 1 ≤ e.idx) (hnb : ¬ (e.idx = 1 ∧ e.act = .block)) :
    ∃ r0 ∈ G.events, r0.tid = e.tid ∧ r0.idx = 0 ∧ r0.act = .read (P.st e.tid) ∧
      ∃ s ∈ G.events, G.rf r0 = some (.th s) ∧ s.act = .write (P.st e.tid) 1 ∧
        s.tid ≠ e.tid ∧ TOp.start e.tid ∈ P.code s.tid := by
  obtain ⟨r0, hr0, ht, hi, hact, rest, htr⟩ := start_read hG hE he hr h1
  obtain ⟨-, -, htm⟩ := ev_tab hE he
  refine ⟨r0, hr0, ht, hi, hact, ?_⟩
  have hv0 : G.ret r0 ≠ some 0 := by
    intro h0
    have := start_wait_events hG hE hr0 (by rw [ht]; exact hr) hi h0 he ht.symm
    exact hnb ⟨by omega, this.2 (by omega)⟩
  obtain ⟨src, hs, hsw, hret⟩ := ret_read hG hr0 hact
  cases src with
  | init =>
    exfalso
    apply hv0
    rw [hret]
    simp [Graph.valAt, mem_eq hE, hF.mem_st htm, hr]
  | th s =>
    obtain ⟨hsm, v, hsa⟩ := hsw
    rcases write_st hF hE hsm hsa htm rfl with ⟨hv1, hst, -, hne⟩ | ⟨-, hts⟩
    · subst hv1
      exact ⟨s, hsm, hs, hsa, fun h => hne h.symm, hst⟩
    · exfalso
      have hsi : s.idx ≠ 0 := by
        intro h
        have := hG.idx_inj s hsm r0 hr0 (by rw [← hts, ht]) (by rw [h, hi])
        rw [this, hact] at hsa
        cases hsa
      have hac : Maz.Acyclic G.scStep := hsc
      apply hac (.th r0)
      exact Relation.TransGen.head (Or.inl (po_th hr0 hsm (ht.trans hts) (by omega)))
        (Relation.TransGen.single (Or.inr (Or.inl (rfRel_th hr0 hs))))

/-- **Lemma 5**: every event of a non-root thread other than its start-read and start-wait
`block` (its body events and its finish write) is porf-after a start write of `st t`. -/
theorem lc_lemma5 (hF : Frag P) (hG : G.Wf) (hsc : SC.cons G)
    (hE : (lifeSys P n).toProgram.Exec G) {e : TEv} (he : e ∈ G.events)
    (hr : P.isRoot e.tid = false) (h1 : 1 ≤ e.idx) (hnb : ¬ (e.idx = 1 ∧ e.act = .block)) :
    ∃ s ∈ G.events, s.act = .write (P.st e.tid) 1 ∧ G.porf (.th s) (.th e) := by
  obtain ⟨r0, hr0, ht, hi, -, s, hs, hrf, hsa, -, -⟩ := lc_lemma2 hF hG hsc hE he hr h1 hnb
  exact ⟨s, hs, hsa, Relation.TransGen.head (Or.inr (rfRel_th hr0 hrf))
    (Relation.TransGen.single (Or.inl (po_th hr0 he ht (by omega))))⟩

/-- **Lemma 7**: every `block` directly follows, in po, a read of one of the four kinds
of §3. -/
theorem lc_lemma7 (hF : Frag P) (hG : G.Wf) (hE : (lifeSys P n).toProgram.Exec G) {b : TEv}
    (hb : b ∈ G.events) (hact : b.act = .block) :
    ∃ p ∈ G.events, p.tid = b.tid ∧ p.idx + 1 = b.idx ∧ ∃ x, p.act = .read x ∧
      BlockKinds P b.tid p.idx x (G.ret p) := by
  obtain ⟨h1, hs, ht⟩ := ev_tab hE hb
  rw [hact] at h1
  obtain ⟨u', v, x, hu, hrd, hk⟩ := lifeTab_block hF ht h1 hs
  have hl : u'.length + 1 = b.idx := by
    have := congrArg List.length hu
    simp [Graph.traceBefore_length] at this
    omega
  obtain ⟨p, hp, hpt, hpi⟩ := hG.idx_contig b hb u'.length (by omega)
  have htake : G.traceBefore b.tid p.idx = u' := by
    rw [hpi, ← traceBefore_take G b.tid (by omega : u'.length ≤ b.idx), hu]
    simp
  obtain ⟨hp1, -, -⟩ := ev_tab hE hp
  rw [hpt, htake, hrd] at hp1
  have hv : v = G.ret p := by
    have h2 := Graph.traceBefore_succ G b.tid u'.length
    rw [hl, hu, ← hpi, htake, Graph.evAt_eq_some_of_inj' hG.idx_inj hp hpt rfl] at h2
    simpa using h2
  refine ⟨p, hp, hpt, by omega, x, (Option.some.inj hp1).symm, ?_⟩
  rw [← hv, hpi]
  exact hk

theorem isEx_of_flag (hE : (lifeSys P n).toProgram.Exec G) {p : TEv} (hp : p ∈ G.events)
    {x : Loc} (hact : p.act = .read x)
    (hf : lifeFlag P p.tid (G.traceBefore p.tid p.idx) = true) : (lifeSys P n).IsEx G p := by
  have hs := hE.2 p hp
  rw [hact] at hs
  change exFlag (lifeSys P n).toProgram.step (lifeFlag P) p.tid (G.traceBefore p.tid p.idx) = true
  unfold exFlag
  rw [hs]
  exact hf

/-- **Lemma 7, with provenance**: every `block` directly follows, in po, a read `p` that
is either the start-read of value `0` at index `0` (a start wait), or the read of the call
at the head of the body state before `p` (`BlockSrc`: a `lock`, a `join` or an `assume`
of that thread), in which case the body state of the `block` is the state after that
call with the value of `p`, and in the lock case `p` is exclusive. -/
theorem lc_lemma7_src (hF : Frag P) (hG : G.Wf) (hE : (lifeSys P n).toProgram.Exec G)
    {b : TEv} (hb : b ∈ G.events) (hact : b.act = .block) :
    ∃ p ∈ G.events, p.tid = b.tid ∧ p.idx + 1 = b.idx ∧ ∃ x, p.act = .read x ∧
      ((p.idx = 0 ∧ P.isRoot b.tid = false ∧ x = P.st b.tid ∧ G.ret p = some 0) ∨
        (BlockSrc P b.tid (bodyState P b.tid (G.traceBefore b.tid p.idx)) x (G.ret p) ∧
          bodyState P b.tid (G.traceBefore b.tid b.idx) =
            (bodyState P b.tid (G.traceBefore b.tid p.idx)).next (G.ret p) ∧
          (P.isLock x = true → (lifeSys P n).IsEx G p))) := by
  obtain ⟨h1, hs, ht⟩ := ev_tab hE hb
  rw [hact] at h1
  obtain ⟨u', v, x, hu, hrd, hk⟩ := lifeTab_block_src hF ht h1 hs
  have hl : u'.length + 1 = b.idx := by
    have := congrArg List.length hu
    simp [Graph.traceBefore_length] at this
    omega
  obtain ⟨p, hp, hpt, hpi⟩ := hG.idx_contig b hb u'.length (by omega)
  have htake : G.traceBefore b.tid p.idx = u' := by
    rw [hpi, ← traceBefore_take G b.tid (by omega : u'.length ≤ b.idx), hu]
    simp
  obtain ⟨hp1, -, -⟩ := ev_tab hE hp
  rw [hpt, htake, hrd] at hp1
  have hv : v = G.ret p := by
    have h2 := Graph.traceBefore_succ G b.tid u'.length
    rw [hl, hu, ← hpi, htake, Graph.evAt_eq_some_of_inj' hG.idx_inj hp hpt rfl] at h2
    simpa using h2
  have hpa : p.act = .read x := (Option.some.inj hp1).symm
  refine ⟨p, hp, hpt, by omega, x, hpa, ?_⟩
  rcases hk with ⟨h0, hr, hx, hv0⟩ | ⟨hsrc, hnext, hflag⟩
  · left
    refine ⟨by rw [hpi, h0]; rfl, hr, hx, by rw [← hv]; exact hv0⟩
  · right
    rw [htake, ← hv]
    refine ⟨hsrc, by rw [hu]; exact hnext, fun hl' => ?_⟩
    apply isEx_of_flag hE hp hpa
    rw [hpt, htake, hflag]
    obtain ⟨hph, hc⟩ := hsrc
    rcases hc with ⟨rest, hops, hh, -, -⟩ | ⟨w, rest, -, hx, hw, -⟩ | ⟨w, rest, -, hd, -⟩
    · simp [TState.isEx, hph, hops, hh]
    · rw [hx, hF.st_not_lock w hw] at hl'
      cases hl'
    · simp [LProg.isData, hl'] at hd

/-- At most one finish write per lifecycle location. -/
theorem finish_unique (hF : Frag P) (hG : G.Wf) (hE : (lifeSys P n).toProgram.Exec G)
    {f₁ f₂ : TEv} (h₁ : f₁ ∈ G.events) (h₂ : f₂ ∈ G.events) {w : Tid} (hw : w ∈ P.threads)
    (ha₁ : f₁.act = .write (P.st w) 2) (ha₂ : f₂.act = .write (P.st w) 2) : f₁ = f₂ := by
  have ht₁ : w = f₁.tid := by
    rcases write_st hF hE h₁ ha₁ hw rfl with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h (by decide)
    · exact h
  have ht₂ : w = f₂.tid := by
    rcases write_st hF hE h₂ ha₂ hw rfl with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h (by decide)
    · exact h
  have hle₁ := finish_last hF hG hE h₁ (by rw [← ht₁]; exact ha₁) h₂ (ht₂.symm.trans ht₁)
  have hle₂ := finish_last hF hG hE h₂ (by rw [← ht₂]; exact ha₂) h₁ (ht₁.symm.trans ht₂)
  exact hG.idx_inj f₁ h₁ f₂ h₂ (ht₁.symm.trans ht₂) (by omega)

/-- Two start writes of `st w` by one thread are impossible: the code of the starter has at
most one `start w` call, and the compiled body uses it up. -/
theorem not_two_starts (hF : Frag P) (hG : G.Wf) (hE : (lifeSys P n).toProgram.Exec G)
    {s₁ s₂ : TEv} (h₁ : s₁ ∈ G.events) (h₂ : s₂ ∈ G.events) (htid : s₂.tid = s₁.tid)
    (hlt : s₁.idx < s₂.idx) {w : Tid} (hw : w ∈ P.threads)
    (ha₁ : s₁.act = .write (P.st w) 1) (ha₂ : s₂.act = .write (P.st w) 1) : False := by
  obtain ⟨rest, hsplit⟩ := traceBefore_split hG h₁ htid hlt
  obtain ⟨e₁, -, ht⟩ := ev_tab hE h₁
  obtain ⟨e₂, -, -⟩ := ev_tab hE h₂
  rw [ha₁] at e₁
  rw [ha₂, htid, hsplit] at e₂
  obtain ⟨b₁, hext⟩ := lifeTab_write e₁
  rw [hext, tState_append_list, List.foldl_cons] at e₂
  set S := tState (P.code s₁.tid) (bodyOf P s₁.tid (G.traceBefore s₁.tid s₁.idx)) with hS
  have hinv : Inv P s₁.tid S := inv_tState hF ht _
  rcases act_write_st hF ht hinv b₁ hw rfl with ⟨-, hph, hh, -, -⟩ | ⟨h, -⟩
  swap
  · exact absurd h (by decide)
  have hc1 := count_next_start w S (G.ret s₁) hph hh
  have hc0 : S.ops.count (.start w) ≤ 1 := by
    have h := count_foldl_le w (bodyOf P s₁.tid (G.traceBefore s₁.tid s₁.idx))
      (TState.init (P.code s₁.tid))
    have h' := hF.one_start w hw s₁.tid ht
    exact le_trans h h'
  have hc2 := count_foldl_le w rest (S.next (G.ret s₁))
  set S₂ := rest.foldl TState.next (S.next (G.ret s₁))
  have hinv₂ : Inv P s₁.tid S₂ := by
    have := inv_tState hF ht (bodyOf P s₁.tid (G.traceBefore s₁.tid s₁.idx) ++ G.ret s₁ :: rest)
    rwa [tState_append_list, List.foldl_cons] at this
  rcases act_write_st hF ht hinv₂ e₂ hw rfl with ⟨-, -, hh₂, -, -⟩ | ⟨h, -⟩
  swap
  · exact absurd h (by decide)
  have hpos : 0 < S₂.ops.count (.start w) :=
    List.count_pos_iff.mpr (List.mem_of_mem_head? hh₂)
  omega

/-- At most one start write per lifecycle location (the static single-start rule). -/
theorem start_unique (hF : Frag P) (hG : G.Wf) (hE : (lifeSys P n).toProgram.Exec G)
    {s₁ s₂ : TEv} (h₁ : s₁ ∈ G.events) (h₂ : s₂ ∈ G.events) {w : Tid} (hw : w ∈ P.threads)
    (ha₁ : s₁.act = .write (P.st w) 1) (ha₂ : s₂.act = .write (P.st w) 1) : s₁ = s₂ := by
  have hc₁ : TOp.start w ∈ P.code s₁.tid := by
    rcases write_st hF hE h₁ ha₁ hw rfl with ⟨-, h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (by decide)
  have hc₂ : TOp.start w ∈ P.code s₂.tid := by
    rcases write_st hF hE h₂ ha₂ hw rfl with ⟨-, h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (by decide)
  have htid : s₁.tid = s₂.tid :=
    hF.one_starter w hw _ (ev_tab hE h₁).2.2 _ (ev_tab hE h₂).2.2 hc₁ hc₂
  by_contra hne
  have hidx : s₁.idx ≠ s₂.idx := fun h => hne (hG.idx_inj _ h₁ _ h₂ htid h)
  rcases Nat.lt_or_gt_of_ne hidx with hlt | hlt
  · exact not_two_starts hF hG hE h₁ h₂ htid.symm hlt hw ha₁ ha₂
  · exact not_two_starts hF hG hE h₂ h₁ htid hlt hw ha₂ ha₁

/-- The elements of the coherence order of a lifecycle location: start writes (of a
non-root thread) and finish writes (of the owner). -/
theorem co_st_mem (hF : Frag P) (hE : (lifeSys P n).toProgram.Exec G) (hG : G.Wf) {w : Tid}
    (hw : w ∈ P.threads) {e : TEv} (he : e ∈ G.co (P.st w)) :
    e ∈ G.events ∧ ((e.act = .write (P.st w) 1 ∧ P.isRoot w = false) ∨
      (e.act = .write (P.st w) 2 ∧ e.tid = w)) := by
  obtain ⟨hm, v, ha⟩ := (hG.co_mem _ e).mp he
  refine ⟨hm, ?_⟩
  rcases write_st hF hE hm ha hw rfl with ⟨h1, -, h3, -⟩ | ⟨h1, h2⟩
  · subst h1; exact Or.inl ⟨ha, h3⟩
  · subst h1; exact Or.inr ⟨ha, h2.symm⟩

/-- A finish write of a non-root thread has a start-read before it that reads a start
write. -/
theorem finish_has_start (hF : Frag P) (hG : G.Wf) (hsc : SC.cons G)
    (hE : (lifeSys P n).toProgram.Exec G) {t : Tid} (hr : P.isRoot t = false) {f : TEv}
    (hf : f ∈ G.events) (hact : f.act = .write (P.st t) 2) (hft : f.tid = t) :
    ∃ r0 ∈ G.events, r0.tid = t ∧ r0.idx < f.idx ∧
      ∃ s ∈ G.events, G.rf r0 = some (.th s) ∧ s.act = .write (P.st t) 1 := by
  have h1 : 1 ≤ f.idx := by
    by_contra h0
    have h0' : f.idx = 0 := by omega
    obtain ⟨e1, -, -⟩ := ev_tab hE hf
    rw [h0', hft, show G.traceBefore t 0 = [] by simp [Graph.traceBefore], lifeTab_nil hr,
      hact] at e1
    cases e1
  obtain ⟨r0, hr0, ht, hi, -, s, hs, hrf, hsa, -⟩ :=
    lc_lemma2 hF hG hsc hE hf (by rw [hft]; exact hr) h1 (by rw [hact]; simp)
  rw [hft] at ht hsa
  exact ⟨r0, hr0, ht, by omega, s, hs, hrf, hsa⟩

/-- **Lemma 1 (non-root)**: the coherence order of `st t` is a prefix of
`[start, finish]`. -/
theorem lc_lemma1_nonroot (hF : Frag P) (hG : G.Wf) (hsc : SC.cons G)
    (hE : (lifeSys P n).toProgram.Exec G) {t : Tid} (ht : t ∈ P.threads)
    (hr : P.isRoot t = false) :
    G.co (P.st t) = [] ∨ (∃ s, G.co (P.st t) = [s] ∧ s.act = .write (P.st t) 1) ∨
      ∃ s f, G.co (P.st t) = [s, f] ∧ s.act = .write (P.st t) 1 ∧
        f.act = .write (P.st t) 2 ∧ f.tid = t := by
  have hnd := hG.co_nodup (P.st t)
  have hm : ∀ e ∈ G.co (P.st t), e ∈ G.events ∧ ((e.act = .write (P.st t) 1) ∨
      (e.act = .write (P.st t) 2 ∧ e.tid = t)) := fun e he => by
    obtain ⟨h1, h2⟩ := co_st_mem hF hE hG ht he
    exact ⟨h1, h2.imp (fun h => h.1) id⟩
  -- two elements of the same kind are equal
  have hsame : ∀ a ∈ G.co (P.st t), ∀ b ∈ G.co (P.st t), a ≠ b →
      (a.act = .write (P.st t) 1 ∧ b.act = .write (P.st t) 2 ∧ b.tid = t) ∨
        (a.act = .write (P.st t) 2 ∧ a.tid = t ∧ b.act = .write (P.st t) 1) := by
    intro a ha b hb hab
    obtain ⟨ham, ha'⟩ := hm a ha
    obtain ⟨hbm, hb'⟩ := hm b hb
    rcases ha' with ha1 | ⟨ha2, hat⟩ <;> rcases hb' with hb1 | ⟨hb2, hbt⟩
    · exact absurd (start_unique hF hG hE ham hbm ht ha1 hb1) hab
    · exact Or.inl ⟨ha1, hb2, hbt⟩
    · exact Or.inr ⟨ha2, hat, hb1⟩
    · exact absurd (finish_unique hF hG hE ham hbm ht ha2 hb2) hab
  -- a finish needs a start, which is in the coherence order too
  have hstart : ∀ f ∈ G.co (P.st t), f.act = .write (P.st t) 2 → f.tid = t →
      ∃ r0 ∈ G.events, r0.tid = t ∧ r0.idx < f.idx ∧
        ∃ s ∈ G.co (P.st t), G.rf r0 = some (.th s) ∧ s.act = .write (P.st t) 1 := by
    intro f hf ha hft
    obtain ⟨r0, hr0, h0t, h0i, s, hs, hrf, hsa⟩ :=
      finish_has_start hF hG hsc hE hr (hm f hf).1 ha hft
    exact ⟨r0, hr0, h0t, h0i, s, (hG.co_mem _ s).mpr ⟨hs, 1, hsa⟩, hrf, hsa⟩
  have hac : Maz.Acyclic G.scStep := hsc
  match hco : G.co (P.st t) with
  | [] => exact Or.inl rfl
  | [a] =>
    rcases (hm a (by rw [hco]; simp)).2 with ha1 | ⟨ha2, hat⟩
    · exact Or.inr (Or.inl ⟨a, rfl, ha1⟩)
    · exfalso
      obtain ⟨-, -, -, -, s, hs, -, hsa⟩ := hstart a (by rw [hco]; simp) ha2 hat
      rw [hco] at hs
      simp only [List.mem_singleton] at hs
      rw [hs, ha2] at hsa
      simp at hsa
  | [a, b] =>
    rw [hco] at hnd
    have hab : a ≠ b := by simpa using hnd
    rcases hsame a (by rw [hco]; simp) b (by rw [hco]; simp) hab with
      ⟨ha1, hb2, hbt⟩ | ⟨ha2, hat, hb1⟩
    · exact Or.inr (Or.inr ⟨a, b, rfl, ha1, hb2, hbt⟩)
    · exfalso
      obtain ⟨r0, hr0, h0t, h0i, s, hs, hrf, hsa⟩ := hstart a (by rw [hco]; simp) ha2 hat
      have hsb : s = b := start_unique hF hG hE (hm s hs).1 (hm b (by rw [hco]; simp)).1 ht
        hsa hb1
      subst hsb
      have hbef : (G.co (P.st t)).Before a s := by
        rw [hco]; exact List.before_cons_self (by simp) hab
      have hco' : G.coRel (.th a) (.th s) := ⟨P.st t, hbef⟩
      apply hac (.th a)
      exact Relation.TransGen.head (Or.inr (Or.inr (Or.inl hco')))
        (Relation.TransGen.head (Or.inr (Or.inl (rfRel_th hr0 hrf)))
          (Relation.TransGen.single (Or.inl (po_th hr0 (hm a (by rw [hco]; simp)).1
            (h0t.trans hat.symm) h0i))))
  | a :: b :: c :: rest =>
    exfalso
    rw [hco] at hnd
    have hab : a ≠ b := by intro h; simp [h] at hnd
    have hac' : a ≠ c := by intro h; simp [h] at hnd
    have hbc : b ≠ c := by intro h; simp [h] at hnd
    have ha : a ∈ G.co (P.st t) := by rw [hco]; simp
    have hb : b ∈ G.co (P.st t) := by rw [hco]; simp
    have hc : c ∈ G.co (P.st t) := by rw [hco]; simp
    rcases hsame a ha b hb hab with ⟨ha1, hb2, -⟩ | ⟨ha2, -, hb1⟩ <;>
      rcases hsame a ha c hc hac' with ⟨_, hc2, -⟩ | ⟨_, -, hc1⟩
    · exact hbc (finish_unique hF hG hE (hm b hb).1 (hm c hc).1 ht hb2 hc2)
    · rw [ha1] at *; simp_all
    · rw [ha2] at *; simp_all
    · exact hbc (start_unique hF hG hE (hm b hb).1 (hm c hc).1 ht hb1 hc1)

/-- **Lemma 1 (root)**: the coherence order of `st t` of a root is a prefix of
`[finish]`. -/
theorem lc_lemma1_root (hF : Frag P) (hG : G.Wf) (hE : (lifeSys P n).toProgram.Exec G)
    {t : Tid} (ht : t ∈ P.threads) (hr : P.isRoot t = true) :
    G.co (P.st t) = [] ∨ ∃ f, G.co (P.st t) = [f] ∧ f.act = .write (P.st t) 2 ∧ f.tid = t := by
  have hm : ∀ e ∈ G.co (P.st t), e ∈ G.events ∧ e.act = .write (P.st t) 2 ∧ e.tid = t :=
    fun e he => by
      obtain ⟨h1, h2⟩ := co_st_mem hF hE hG ht he
      rcases h2 with ⟨-, h⟩ | h
      · rw [hr] at h; cases h
      · exact ⟨h1, h⟩
  have hnd := hG.co_nodup (P.st t)
  match hco : G.co (P.st t) with
  | [] => exact Or.inl rfl
  | [a] =>
    obtain ⟨-, h1, h2⟩ := hm a (by rw [hco]; simp)
    exact Or.inr ⟨a, rfl, h1, h2⟩
  | a :: b :: rest =>
    exfalso
    rw [hco] at hnd
    have hab : a ≠ b := by intro h; simp [h] at hnd
    obtain ⟨ham, ha2, -⟩ := hm a (by rw [hco]; simp)
    obtain ⟨hbm, hb2, -⟩ := hm b (by rw [hco]; simp)
    exact hab (finish_unique hF hG hE ham hbm ht ha2 hb2)

/-- **Lemma 8**: a final start wait (a start-read of value `0` reading the
coherence-maximal write of its location) belongs to a thread that is never started: its
lifecycle location has no write at all, and every event of the thread is the start-read or,
at index `1`, a `block`. (That the `block` exists is `lc_lemma8_block`.) -/
theorem lc_lemma8 (hF : Frag P) (hG : G.Wf) (hE : (lifeSys P n).toProgram.Exec G) {r0 : TEv}
    (hr0 : r0 ∈ G.events) (hr : P.isRoot r0.tid = false) (h0i : r0.idx = 0)
    (hv : G.ret r0 = some 0) (hfin : G.rf r0 = some (G.maxWrite (P.st r0.tid))) :
    (∀ e ∈ G.events, ∀ v, e.act ≠ .write (P.st r0.tid) v) ∧
      ∀ e ∈ G.events, e.tid = r0.tid → e.idx ≤ 1 ∧ (e.idx = 1 → e.act = .block) := by
  obtain ⟨e1, -, ht⟩ := ev_tab hE hr0
  rw [h0i, show G.traceBefore r0.tid 0 = [] by simp [Graph.traceBefore], lifeTab_nil hr] at e1
  have hact : r0.act = .read (P.st r0.tid) := (Option.some.inj e1).symm
  have hinit := lc_lemma4 hF hG hE hr0 ht hact hv
  rw [hinit] at hfin
  have hco : G.co (P.st r0.tid) = [] := by
    unfold Graph.maxWrite at hfin
    cases hl : (G.co (P.st r0.tid)).getLast? with
    | none => exact List.getLast?_eq_none_iff.mp hl
    | some e => rw [hl] at hfin; cases hfin
  refine ⟨fun e he v ha => ?_, fun e he het => start_wait_events hG hE hr0 hr h0i hv he het⟩
  have := (hG.co_mem _ e).mpr ⟨he, v, ha⟩
  rw [hco] at this
  cases this

/-- **Lemma 8, existence of the `block`**: in a full graph with `2 ≤ n`, a non-root
thread whose start-read returned `0` has its `block` at index `1`. -/
theorem lc_lemma8_block (hG : G.Wf) (hE : (lifeSys P n).toProgram.Exec G)
    (hfull : (lifeSys P n).toProgram.Full G) (hn : 2 ≤ n) {r0 : TEv} (hr0 : r0 ∈ G.events)
    (hr : P.isRoot r0.tid = false) (h0i : r0.idx = 0) (hv : G.ret r0 = some 0) :
    ∃ b ∈ G.events, b.tid = r0.tid ∧ b.idx = 1 ∧ b.act = .block := by
  have ht := (ev_tab hE hr0).2.2
  by_cases h2 : 1 < G.cnt r0.tid
  · obtain ⟨b, hb, hbt, hbi⟩ := (hG.exists_idx_iff r0.tid 1).mpr h2
    exact ⟨b, hb, hbt, hbi, (start_wait_events hG hE hr0 hr h0i hv hb hbt).2 hbi⟩
  · exfalso
    have hc1 : G.cnt r0.tid = 1 := by
      have := hG.idx_lt_cnt hr0
      rw [h0i] at this
      omega
    have htr : G.trace r0.tid = [some 0] := by
      unfold Graph.trace
      rw [hc1, Graph.traceBefore_succ, Graph.evAt_eq_some_of_inj' hG.idx_inj hr0 rfl h0i]
      simp [Graph.traceBefore, hv]
    have hs := (Program.full_iff.mp hfull) r0.tid ht
    rw [htr, step_eq] at hs
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by
      simp only [List.length_singleton, not_or, not_le, not_not, Bool.not_eq_true]
      refine ⟨by omega, ht, ?_⟩
      simp [stopped, lifeTab, hr, isStop]))] at hs
    simp [lifeTab, hr] at hs

/-- Supporting invariant (part): the target of a final join wait (a join read of `1` that
reads the coherence-maximal write) is started and not finished. (That it is blocked or
erred in a full graph under an adequate bound is `final_join_target_full`.) -/
theorem final_join_target (hF : Frag P) (hG : G.Wf) (hsc : SC.cons G)
    (hE : (lifeSys P n).toProgram.Exec G) {j : TEv} (hj : j ∈ G.events) {w : Tid}
    (hw : w ∈ P.threads) (hact : j.act = .read (P.st w)) (hne : j.tid ≠ w)
    (hv : G.ret j = some 1) (hfin : G.rf j = some (G.maxWrite (P.st w))) :
    (∃ s ∈ G.events, s.act = .write (P.st w) 1) ∧
      ∀ f ∈ G.events, f.act ≠ .write (P.st w) 2 := by
  obtain ⟨s, hs, hrf, hsa, -⟩ := lc_lemma6 hF hG hE hj hw hact hne hv
  refine ⟨⟨s, hs, hsa⟩, fun f hf hfa => ?_⟩
  have hr := read_st_other hF hE hj hw hact hne
  have hlast : (G.co (P.st w)).getLast? = some s := by
    rw [hrf] at hfin
    unfold Graph.maxWrite at hfin
    cases hl : (G.co (P.st w)).getLast? with
    | none => rw [hl] at hfin; cases hfin
    | some e => rw [hl] at hfin; cases hfin; rfl
  have hfco : f ∈ G.co (P.st w) := (hG.co_mem _ f).mpr ⟨hf, 2, hfa⟩
  rcases lc_lemma1_nonroot hF hG hsc hE hw hr with h | ⟨s', h, -⟩ | ⟨s', f', h, -, hf'a, -⟩
  · rw [h] at hfco; cases hfco
  · rw [h] at hlast hfco
    simp only [List.getLast?_singleton, Option.some.injEq, List.mem_singleton] at hlast hfco
    subst hlast hfco
    rw [hsa] at hfa
    simp at hfa
  · rw [h] at hlast
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hlast
    subst hlast
    rw [hsa] at hf'a
    simp at hf'a

/-- **Supporting invariant**: in a full graph under an adequate bound, the target of a
final join wait is started, not finished, and its last event is a `block` or an
`error`. -/
theorem final_join_target_full (hF : Frag P) (hG : G.Wf) (hsc : SC.cons G)
    (hE : (lifeSys P n).toProgram.Exec G) (hfull : (lifeSys P n).toProgram.Full G)
    (hn : adequateB P n = true) {j : TEv} (hj : j ∈ G.events) {w : Tid} (hw : w ∈ P.threads)
    (hact : j.act = .read (P.st w)) (hne : j.tid ≠ w) (hv : G.ret j = some 1)
    (hfin : G.rf j = some (G.maxWrite (P.st w))) :
    (∃ s ∈ G.events, s.act = .write (P.st w) 1) ∧ (∀ f ∈ G.events, f.act ≠ .write (P.st w) 2) ∧
      ∃ e ∈ G.events, e.tid = w ∧ (e.act = .block ∨ e.act = .error) ∧
        ∀ e' ∈ G.events, e'.tid = w → e'.idx ≤ e.idx := by
  obtain ⟨hstart, hnofin⟩ := final_join_target hF hG hsc hE hj hw hact hne hv hfin
  refine ⟨hstart, hnofin, ?_⟩
  have hr := read_st_other hF hE hj hw hact hne
  have hcut := lifeSys_noCut P hn hfull hw
  have hlen := Graph.trace_length G w
  by_cases hst : stopped (lifeTab P) w (G.trace w) = true
  · unfold stopped at hst
    obtain ⟨i, hi, hstop⟩ := List.any_eq_true.mp hst
    rw [List.mem_range, hlen] at hi
    obtain ⟨e, he, het, hei⟩ := (hG.exists_idx_iff w i).mpr hi
    obtain ⟨he1, -, -⟩ := ev_tab hE he
    rw [het, hei, Graph.traceBefore_eq_take G w (Nat.le_of_lt hi)] at he1
    rw [he1] at hstop
    have hba : e.act = .block ∨ e.act = .error := by
      cases hea : e.act <;> simp [hea, isStop] at hstop ⊢
    refine ⟨e, he, het, hba, fun e' he' het' => ?_⟩
    by_contra hlt
    obtain ⟨-, hs', -⟩ := ev_tab hE he'
    rw [het'] at hs'
    have hs'' := stopped_false_iff.mp hs' i (by rw [Graph.traceBefore_length]; omega)
    rw [traceBefore_take G w (by omega), Graph.traceBefore_eq_take G w (Nat.le_of_lt hi),
      he1] at hs''
    rcases hba with h | h <;> simp [h, isStop] at hs''
  · exfalso
    have hnone : lifeTab P w (G.trace w) = none := by
      by_contra hsome
      exact hcut ⟨by simpa using hst, hsome⟩
    cases htr : G.trace w with
    | nil => rw [htr, lifeTab_nil hr] at hnone; cases hnone
    | cons v rest =>
      by_cases hv0 : v = some 0
      · rw [htr, hv0] at hnone hst
        cases rest with
        | nil => simp [lifeTab, hr] at hnone
        | cons v' rest' =>
          apply hst
          unfold stopped
          exact List.any_eq_true.mpr ⟨1, by simp, by simp [lifeTab, hr, isStop]⟩
      · rw [htr, lifeTab_cons hr hv0] at hnone
        obtain ⟨i, hi, hfa⟩ := tState_finish_of_done P.st w (P.code w) rest (act_none_done hnone)
        have hic : i + 1 < G.cnt w := by rw [← hlen, htr]; simp; omega
        obtain ⟨f, hf, hft, hfi⟩ := (hG.exists_idx_iff w (i + 1)).mpr hic
        obtain ⟨hf1, -, -⟩ := ev_tab hE hf
        rw [hft, hfi, Graph.traceBefore_eq_take G w (Nat.le_of_lt hic), htr, List.take_succ_cons,
          lifeTab_cons hr hv0, hfa] at hf1
        exact hnofin f hf (Option.some.inj hf1).symm

end graph

end Life

end Condpor
