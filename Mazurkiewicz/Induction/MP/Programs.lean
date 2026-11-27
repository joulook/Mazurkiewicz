import Mazurkiewicz.Induction.MP.Steps

/-!
# Message passing: residual programs with seeds, fragments, truncation (milestone C2)

`induction-popl`, `mp.tex` def:env (`env_w`, `P_{s,w}`, `Z_w`, `Frag`, `‖H‖`, the note
mp:97) and `p2p.tex` def:p2p-frag (`w ▷ p`, `P_{s,w}`, `Z_w`, fragments, the note p2p:101);
`dpor.tex` def:budget (`Q_b|κ`) and lem:budget (1), (3) for the port's programs (plan
`plan/ind/TRACK-C-PLAN.md`, milestone C2).

* `prefixStep m w p` is `w ▷ p`: the sends of the word `w` (model `m`), then `p` on the rest of
  the trace. With `p` nowhere defined it is `env_w` (`prefixStep_env`).
* `Program.seedRes P ι hι m u W` is `P_{s,w}` for both sections: a thread of `P` runs the seeds
  `W t`, then its residual after `u t`; an idle thread of `ι` runs its seeds only.
  `seedRes_congr`: it depends on the local states only (lem:residual (2)).
* `Program.trunc R κ` (guarded by `t ∈ R.threads`) is `Q|κ`; `trunc_bounded`,
  `exec_trunc_iff` (lem:budget (1)), `exec_of_isPrefixOf` (lem:budget (3)).
* `seedGraph ts m W` is `Z_w`; `seedCard`, `Graph.len` (`‖H‖`); `Frag M R W H` (`H` a
  consistent execution of `R` containing the seeds). Notes mp:97, p2p:101: `frag_seed` (`Z_w`
  is a fragment), `seed_isPrefixOf` (a prefix of every fragment); `frag_cnt_idle` (an idle
  thread performs exactly its seeds), `frag_seedEv`.
* Helper: `sendsGraph_cons`: a graph of fresh sends without sources is consistent in every
  model (from `Model.empty` and `Model.ext_plain`).
-/

namespace Must

open Graph Relation

open Ind in
/-- `w ▷ p` (def:p2p-frag; `env_w` of def:env for `p` nowhere defined): the sends of `w`, then
`p` on the rest of the trace. -/
def Ind.prefixStep {Q : Type} (m : Comm) (w : List Msg) (p : List (Option Val) → Option (Lab Q))
    (x : List (Option Val)) : Option (Lab Q) :=
  match w[x.length]? with
  | some (d, v) => some (.send m d v)
  | none => p (x.drop w.length)

namespace Ind

variable {Q : Type}

theorem prefixStep_of_lt {m : Comm} {w : List Msg} {p : List (Option Val) → Option (Lab Q)}
    {x : List (Option Val)} (h : x.length < w.length) :
    prefixStep m w p x = some (.send m (w[x.length]'h).1 (w[x.length]'h).2) := by
  unfold prefixStep
  rw [List.getElem?_eq_getElem h]

theorem prefixStep_of_le {m : Comm} {w : List Msg} {p : List (Option Val) → Option (Lab Q)}
    {x : List (Option Val)} (h : w.length ≤ x.length) :
    prefixStep m w p x = p (x.drop w.length) := by
  unfold prefixStep
  rw [List.getElem?_eq_none h]

/-- def:env: `env_w`. -/
theorem prefixStep_env {m : Comm} {w : List Msg} (x : List (Option Val)) :
    prefixStep m w (fun _ => none) x =
      (w[x.length]?).map (fun dv : Msg => (Lab.send m dv.1 dv.2 : Lab Q)) := by
  unfold prefixStep
  rcases w[x.length]? with _ | ⟨d, v⟩ <;> rfl

/-- A label of `w ▷ p` is a send of `w` or a label of `p`. -/
theorem prefixStep_cases {m : Comm} {w : List Msg} {p : List (Option Val) → Option (Lab Q)}
    {x : List (Option Val)} {l : Lab Q} (h : prefixStep m w p x = some l) :
    (x.length < w.length ∧ l.IsSend) ∨ (w.length ≤ x.length ∧ p (x.drop w.length) = some l) := by
  rcases Nat.lt_or_ge x.length w.length with hl | hl
  · rw [prefixStep_of_lt hl] at h
    cases h
    exact Or.inl ⟨hl, trivial⟩
  · rw [prefixStep_of_le hl] at h
    exact Or.inr ⟨hl, h⟩

theorem seedLab_isSend {m : Comm} {W : Tid → List Msg} {t j : ℕ} (hj : j < (W t).length) :
    (seedLab m W t j : Lab Q).IsSend := by
  unfold seedLab
  rw [List.getElem?_eq_getElem hj]
  trivial

end Ind

open Ind

namespace Program

variable {Q : Type}

/-- `P_{s,w}` (def:env, def:p2p-frag): thread `t` of `P` runs `W t ▷ P_t(u t ++ ·)`, an idle
thread of `ι` runs `W t ▷ ⊥`. -/
def seedRes (P : Program Q) (ι : List Tid) (hι : (P.threads ++ ι).Nodup) (m : Comm)
    (u : Tid → List (Option Val)) (W : Tid → List Msg) : Program Q where
  threads := P.threads ++ ι
  nodup := hι
  step t x := if t ∈ P.threads then prefixStep m (W t) (fun y => P.step t (u t ++ y)) x
    else if t ∈ ι then prefixStep m (W t) (fun _ => none) x else none
  step_none t ht := by
    have h1 : t ∉ P.threads := fun h => ht (List.mem_append_left _ h)
    have h2 : t ∉ ι := fun h => ht (List.mem_append_right _ h)
    simp [h1, h2]
  stop t x l h hs := by
    have hns : ∀ {l : Lab Q}, l.IsSend → ¬ l.Stops := fun {l} h1 h2 => by
      cases l <;> simp_all [Lab.IsSend, Lab.Stops]
    by_cases h1 : t ∈ P.threads
    · simp only [h1, ↓reduceIte] at h ⊢
      rcases prefixStep_cases h with ⟨-, hS⟩ | ⟨hl, hp⟩
      · exact absurd hs (hns hS)
      · have hl' : (W t).length ≤ (x ++ [none]).length := by simp; omega
        rw [prefixStep_of_le hl', List.drop_append_of_le_length hl, ← List.append_assoc]
        exact P.stop t _ l hp hs
    · by_cases h2 : t ∈ ι
      · simp only [h1, h2, ↓reduceIte] at h ⊢
        rcases prefixStep_cases h with ⟨-, hS⟩ | ⟨-, hp⟩
        · exact absurd hs (hns hS)
        · cases hp
      · simp [h1, h2] at h
  nd_ne t x S h := by
    by_cases h1 : t ∈ P.threads
    · simp only [h1, ↓reduceIte] at h
      rcases prefixStep_cases h with ⟨-, hS⟩ | ⟨-, hp⟩
      · cases hS
      · exact P.nd_ne t _ S hp
    · by_cases h2 : t ∈ ι
      · simp only [h1, h2, ↓reduceIte] at h
        rcases prefixStep_cases h with ⟨-, hS⟩ | ⟨-, hp⟩
        · cases hS
        · cases hp
      · simp [h1, h2] at h

/-- `Q|κ` (def:budget), guarded by the listed threads. -/
def trunc (R : Program Q) (κ : Tid → ℕ) : Program Q where
  threads := R.threads
  nodup := R.nodup
  step t x := if t ∈ R.threads ∧ x.length < κ t then R.step t x else none
  step_none t ht := by simp [ht]
  stop t x l h hs := by
    by_cases hc : t ∈ R.threads ∧ x.length < κ t
    · simp only [hc, and_self, ↓reduceIte] at h
      simp [R.stop t x l h hs]
    · simp [hc] at h
  nd_ne t x S h := by
    by_cases hc : t ∈ R.threads ∧ x.length < κ t
    · simp only [hc, and_self, ↓reduceIte] at h
      exact R.nd_ne t x S h
    · simp [hc] at h

end Program

namespace Ind

variable {Q : Type} [DecidableEq Q] [Membership Val Q]

/-! ### Truncation -/

omit [DecidableEq Q] [Membership Val Q] in
/-- A truncation by `κ ≤ n` on the listed threads is bounded by `n`. Without the guard
`t ∈ R.threads` false (Astra C2): an unlisted thread with a send after a trace of length 1,
`κ t = 2`, `n = 1`. -/
theorem trunc_bounded {R : Program Q} {κ : Tid → ℕ} {n : ℕ} (h : ∀ t ∈ R.threads, κ t ≤ n) :
    (R.trunc κ).Bounded n := by
  intro t u hu
  change (if t ∈ R.threads ∧ u.length < κ t then R.step t u else none) = none
  by_cases ht : t ∈ R.threads
  · have := h t ht
    simp only [show ¬ (t ∈ R.threads ∧ u.length < κ t) from fun h' => by have := h'.2; omega,
      ↓reduceIte]
  · simp only [show ¬ (t ∈ R.threads ∧ u.length < κ t) from fun h' => ht h'.1, ↓reduceIte]

omit [DecidableEq Q] [Membership Val Q] in
theorem traceBefore_length (G : Graph Q) (t : Tid) (i : ℕ) : (G.traceBefore t i).length = i := by
  simp [traceBefore]

omit [DecidableEq Q] in
/-- lem:budget (1): the executions of `R|κ` are the executions of `R` with at most `κ t`
events in every thread. -/
theorem exec_trunc_iff {R : Program Q} {κ : Tid → ℕ} {H : Graph Q} (hH : H.Wf) :
    (R.trunc κ).Exec H ↔ R.Exec H ∧ ∀ t, H.cnt t ≤ κ t := by
  have key : ∀ e ∈ H.events, (R.trunc κ).step e.tid (H.traceBefore e.tid e.idx) =
      if e.tid ∈ R.threads ∧ e.idx < κ e.tid then R.step e.tid (H.traceBefore e.tid e.idx)
      else none := fun e _ => by
    change (if _ then _ else _) = _
    rw [traceBefore_length]
  constructor
  · intro h
    have hc : ∀ e ∈ H.events, e.tid ∈ R.threads ∧ e.idx < κ e.tid ∧
        R.step e.tid (H.traceBefore e.tid e.idx) = some e.lab := by
      intro e he
      have := h e he
      rw [key e he] at this
      split_ifs at this with hc
      · exact ⟨hc.1, hc.2, this⟩
    refine ⟨fun e he => (hc e he).2.2, fun t => ?_⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨e, he, ht, hi⟩ := (hH.exists_idx_iff t (κ t)).mpr hlt
    have := (hc e he).2.1
    rw [ht, hi] at this
    exact lt_irrefl _ this
  · rintro ⟨h, hk⟩ e he
    have hc : e.tid ∈ R.threads ∧ e.idx < κ e.tid :=
      ⟨hH.tid_mem_threads h he, lt_of_lt_of_le (hH.idx_lt_cnt he) (hk e.tid)⟩
    rw [key e he]
    simp only [hc, and_self, ↓reduceIte]
    exact h e he

/-- lem:budget (3): a prefix of an execution is an execution. (The well-formedness premise of
the plan is not needed.) -/
theorem exec_of_isPrefixOf {R : Program Q} {G G' : Graph Q} (hE : R.Exec G') (_hG' : G'.Wf)
    (hp : G.IsPrefixOf G') : R.Exec G := by
  obtain ⟨E, hE', rfl⟩ := hp
  refine R.exec_of_agree hE fun x hx => ?_
  rw [restrict_events, Finset.mem_inter] at hx
  refine ⟨hx.1, fun y h1 h2 => ⟨?_, fun hy => ?_⟩⟩
  · rw [restrict_events, Finset.mem_inter]
    refine ⟨fun hy => ⟨hy, ?_⟩, fun h => h.1⟩
    have := hE' (Or.inl ⟨hy, hx.1, h1, h2⟩) (Finset.mem_coe.mpr (Finset.mem_inter.mpr hx))
    exact (Finset.mem_inter.mp (Finset.mem_coe.mp this)).2
  · have := hE' (Or.inl ⟨hy, hx.1, h1, h2⟩) (Finset.mem_coe.mpr (Finset.mem_inter.mpr hx))
    have hyE := (Finset.mem_inter.mp (Finset.mem_coe.mp this)).2
    simp [hyE]

/-! ### Residual programs with seeds -/

omit [DecidableEq Q] [Membership Val Q] in
/-- lem:residual (2): `P_{s,w}` depends on the local states only. -/
theorem seedRes_congr {P : Program Q} {ι : List Tid} {hι : (P.threads ++ ι).Nodup} {m : Comm}
    {u u' : Tid → List (Option Val)} {W : Tid → List Msg}
    (h : ∀ t ∈ P.threads, FutEq (P.step t) (u t) (u' t)) :
    P.seedRes ι hι m u W = P.seedRes ι hι m u' W := by
  have hs : (P.seedRes ι hι m u W).step = (P.seedRes ι hι m u' W).step := by
    funext t x
    change (if t ∈ P.threads then _ else _) = (if t ∈ P.threads then _ else _)
    by_cases ht : t ∈ P.threads
    · simp only [ht, ↓reduceIte]
      unfold prefixStep
      rcases (W t)[x.length]? with _ | ⟨d, v⟩
      · exact h t ht _
      · rfl
    · simp only [ht, ↓reduceIte]
  unfold Program.seedRes at hs ⊢
  congr 1

/-! ### Seed graphs and fragments -/

/-- `Z_w` (def:env, def:p2p-frag): the seed events of the threads `ts`, without sources. -/
def seedGraph (ts : List Tid) (m : Comm) (W : Tid → List Msg) : Graph Q where
  events := (ts.toFinset).biUnion fun t => (Finset.range (W t).length).image (seedEv m W t)
  rf := fun _ => none
  nd := fun _ => none

omit [DecidableEq Q] [Membership Val Q] in
/-- The number of seeds. -/
def seedCard (ts : List Tid) (W : Tid → List Msg) : ℕ := (ts.map fun t => (W t).length).sum

end Ind

/-- `‖H‖`: the events of `H` beyond the seeds. -/
def Graph.len {Q : Type} (H : Graph Q) (ts : List Tid) (W : Tid → List Msg) : ℕ :=
  H.events.card - seedCard ts W

namespace Ind

variable {Q : Type} [DecidableEq Q] [Membership Val Q]

/-- A fragment (def:env, def:p2p-frag): a consistent execution of `R` that contains the
seeds. -/
def Frag (M : Model Q) (R : Program Q) (W : Tid → List Msg) (H : Graph Q) : Prop :=
  ExecM M R H ∧ ∀ t, (W t).length ≤ H.cnt t

omit [Membership Val Q] in
theorem mem_seedGraph {ts : List Tid} {m : Comm} {W : Tid → List Msg} {e : Ev Q} :
    e ∈ (seedGraph ts m W).events ↔
      e.tid ∈ ts ∧ e.idx < (W e.tid).length ∧ e = seedEv m W e.tid e.idx := by
  simp only [seedGraph, Finset.mem_biUnion, List.mem_toFinset, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro ⟨t, ht, j, hj, rfl⟩
    exact ⟨ht, hj, rfl⟩
  · rintro ⟨ht, hj, he⟩
    exact ⟨e.tid, ht, e.idx, hj, he.symm⟩

omit [DecidableEq Q] in
/-- A graph of sends without sources, with contiguous indices, is well-formed. -/
theorem sendsGraph_wf {E : Finset (Ev Q)} (hS : ∀ e ∈ E, ¬ e.IsRecv ∧ ¬ e.IsND)
    (hinj : ∀ e ∈ E, ∀ e' ∈ E, e.tid = e'.tid → e.idx = e'.idx → e = e')
    (hcon : ∀ e ∈ E, ∀ i < e.idx, ∃ e' ∈ E, e'.tid = e.tid ∧ e'.idx = i) :
    (⟨E, fun _ => none, fun _ => none⟩ : Graph Q).Wf := by
  have hpo : ∀ a b, TransGen (⟨E, fun _ => none, fun _ => none⟩ : Graph Q).porfStep a b →
      a.idx < b.idx := by
    intro a b h
    induction h with
    | single h =>
      rcases h with ⟨-, -, -, h⟩ | ⟨-, h⟩
      · exact h
      · cases h
    | tail _ h ih =>
      rcases h with ⟨-, -, -, h⟩ | ⟨-, h⟩
      · exact ih.trans h
      · cases h
  refine ⟨hinj, hcon, fun e => ?_, fun r h => (by cases h), fun r s h => (by cases h),
    fun r r' s h => (by cases h), fun r s h => (by cases h), fun e => ?_,
    fun e v h => (by cases h), fun a h => lt_irrefl _ (hpo a a h)⟩
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
    exact fun he => (hS e he).1
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
    exact fun he => (hS e he).2

/-- A graph of sends without sources, with contiguous indices, is consistent in every model. -/
theorem sendsGraph_cons (M : Model Q) :
    ∀ (n : ℕ) (E : Finset (Ev Q)), E.card = n → (∀ e ∈ E, ¬ e.IsRecv ∧ ¬ e.IsND) →
    (∀ e ∈ E, ∀ e' ∈ E, e.tid = e'.tid → e.idx = e'.idx → e = e') →
    (∀ e ∈ E, ∀ i < e.idx, ∃ e' ∈ E, e'.tid = e.tid ∧ e'.idx = i) →
    M.cons ⟨E, fun _ => none, fun _ => none⟩ := by
  intro n
  induction n with
  | zero =>
    intro E hE _ _ _
    rw [Finset.card_eq_zero.mp hE]
    exact M.empty
  | succ n ih =>
    intro E hE hS hinj hcon
    have hne : E.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e, he, hmax⟩ := Finset.exists_max_image E Ev.idx hne
    set E' := E.erase e with hE'
    have hS' : ∀ x ∈ E', ¬ x.IsRecv ∧ ¬ x.IsND := fun x hx => hS x (Finset.mem_of_mem_erase hx)
    have hinj' : ∀ x ∈ E', ∀ x' ∈ E', x.tid = x'.tid → x.idx = x'.idx → x = x' :=
      fun x hx x' hx' => hinj x (Finset.mem_of_mem_erase hx) x' (Finset.mem_of_mem_erase hx')
    have hcon' : ∀ x ∈ E', ∀ i < x.idx, ∃ x' ∈ E', x'.tid = x.tid ∧ x'.idx = i := by
      intro x hx i hi
      obtain ⟨x', hx', h1, h2⟩ := hcon x (Finset.mem_of_mem_erase hx) i hi
      refine ⟨x', Finset.mem_erase.mpr ⟨fun h => ?_, hx'⟩, h1, h2⟩
      have := hmax x (Finset.mem_of_mem_erase hx)
      rw [h] at h2
      omega
    have hc' := ih E' (by rw [Finset.card_erase_of_mem he]; omega) hS' hinj' hcon'
    have hw' := sendsGraph_wf hS' hinj' hcon'
    have hidx : e.idx = (⟨E', fun _ => none, fun _ => none⟩ : Graph Q).cnt e.tid := by
      refine eq_of_forall_lt_iff fun i => ?_
      rw [← hw'.exists_idx_iff e.tid i]
      constructor
      · intro hi
        obtain ⟨x, hx, h1, h2⟩ := hcon e he i hi
        exact ⟨x, Finset.mem_erase.mpr ⟨fun h => by rw [h] at h2; omega, hx⟩, h1, h2⟩
      · rintro ⟨x, hx, h1, rfl⟩
        have hle := hmax x (Finset.mem_of_mem_erase hx)
        rcases Nat.lt_or_ge x.idx e.idx with h | h
        · exact h
        · exact absurd (hinj x (Finset.mem_of_mem_erase hx) e he h1 (by omega))
            (Finset.mem_erase.mp hx).1
    have heq : (⟨E, fun _ => none, fun _ => none⟩ : Graph Q) =
        (⟨E', fun _ => none, fun _ => none⟩ : Graph Q).add e none none := by
      apply Graph.ext
      · change E = insert e E'
        rw [hE', Finset.insert_erase he]
      · funext x
        simp
      · funext x
        simp
    rw [heq]
    exact M.ext_plain _ e hc' hidx (hS e he).1 (hS e he).2

omit [Membership Val Q] in
theorem seedGraph_props {ts : List Tid} {m : Comm} {W : Tid → List Msg} :
    (∀ e ∈ (seedGraph ts m W : Graph Q).events, ¬ e.IsRecv ∧ ¬ e.IsND) ∧
    (∀ e ∈ (seedGraph ts m W : Graph Q).events, ∀ e' ∈ (seedGraph ts m W : Graph Q).events,
      e.tid = e'.tid → e.idx = e'.idx → e = e') ∧
    (∀ e ∈ (seedGraph ts m W : Graph Q).events, ∀ i < e.idx,
      ∃ e' ∈ (seedGraph ts m W : Graph Q).events, e'.tid = e.tid ∧ e'.idx = i) := by
  refine ⟨fun e he => ?_, fun e he e' he' ht hi => ?_, fun e he i hi => ?_⟩
  · obtain ⟨-, hj, he⟩ := mem_seedGraph.mp he
    have hS : e.IsSend := by rw [he]; exact seedLab_isSend hj
    exact ⟨Lab.IsSend.not_isRecv hS, Lab.IsSend.not_isND hS⟩
  · rw [(mem_seedGraph.mp he).2.2, (mem_seedGraph.mp he').2.2, ht, hi]
  · obtain ⟨ht, hj, -⟩ := mem_seedGraph.mp he
    exact ⟨seedEv m W e.tid i, mem_seedGraph.mpr ⟨ht, by simp [seedEv]; omega, rfl⟩, rfl, rfl⟩

theorem seedGraph_wf {ts : List Tid} {m : Comm} {W : Tid → List Msg} :
    (seedGraph ts m W : Graph Q).Wf :=
  sendsGraph_wf seedGraph_props.1 seedGraph_props.2.1 seedGraph_props.2.2

theorem seedGraph_cnt {ts : List Tid} {m : Comm} {W : Tid → List Msg}
    (hW : ∀ t ∉ ts, W t = []) (t : Tid) : (seedGraph ts m W : Graph Q).cnt t = (W t).length := by
  have key := (seedGraph_wf (Q := Q) (ts := ts) (m := m) (W := W)).exists_idx_iff t
  have hiff : ∀ i, i < (seedGraph ts m W : Graph Q).cnt t ↔ i < (W t).length := by
    intro i
    rw [← key]
    constructor
    · rintro ⟨e, he, rfl, rfl⟩
      exact (mem_seedGraph.mp he).2.1
    · intro hi
      by_cases ht : t ∈ ts
      · exact ⟨seedEv m W t i, mem_seedGraph.mpr ⟨ht, hi, rfl⟩, rfl, rfl⟩
      · rw [hW t ht] at hi
        simp at hi
  exact eq_of_forall_lt_iff hiff

variable {M : Model Q} {P : Program Q} {ι : List Tid} {hι : (P.threads ++ ι).Nodup} {m : Comm}
  {u : Tid → List (Option Val)} {W : Tid → List Msg} {H : Graph Q}

/-- Notes mp:97, p2p:101: `Z_w` is a fragment (of length `0`). -/
theorem frag_seed (hW : ∀ t ∉ P.threads ++ ι, W t = []) :
    Frag M (P.seedRes ι hι m u W) W (seedGraph (P.threads ++ ι) m W) := by
  refine ⟨⟨fun e he => ?_, sendsGraph_cons M _ _ rfl seedGraph_props.1 seedGraph_props.2.1
    seedGraph_props.2.2⟩, fun t => (seedGraph_cnt hW t).ge⟩
  obtain ⟨ht, hj, he⟩ := mem_seedGraph.mp he
  have hl : ((seedGraph (P.threads ++ ι) m W : Graph Q).traceBefore e.tid e.idx).length <
      (W e.tid).length := by rw [traceBefore_length]; exact hj
  change (if e.tid ∈ P.threads then _ else _) = _
  have hlab : e.lab = seedLab m W e.tid e.idx := by rw [he]; rfl
  rw [hlab]
  unfold seedLab
  rw [List.getElem?_eq_getElem hj]
  split_ifs with h1 h2
  · rw [prefixStep_of_lt hl]
    simp [traceBefore_length]
  · rw [prefixStep_of_lt hl]
    simp [traceBefore_length]
  · exact absurd (List.mem_append.mp ht) (by tauto)

/-- The event `(t, j)` of a fragment, for a seed position `j`, is the seed event. -/
theorem frag_seedEv (hH : Frag M (P.seedRes ι hι m u W) W H) {t : Tid} {j : ℕ}
    (hj : j < (W t).length) : seedEv m W t j ∈ H.events := by
  have hw := M.wf _ hH.1.2
  obtain ⟨e, he, rfl, rfl⟩ := (hw.exists_idx_iff t j).mpr (lt_of_lt_of_le hj (hH.2 t))
  have hE := hH.1.1 e he
  have hl : (H.traceBefore e.tid e.idx).length < (W e.tid).length := by
    rw [traceBefore_length]; exact hj
  change (if e.tid ∈ P.threads then _ else _) = _ at hE
  have hlab : e.lab = seedLab m W e.tid e.idx := by
    unfold seedLab
    rw [List.getElem?_eq_getElem hj]
    split_ifs at hE with h1 h2
    · rw [prefixStep_of_lt hl] at hE
      simpa [traceBefore_length] using hE.symm
    · rw [prefixStep_of_lt hl] at hE
      simpa [traceBefore_length] using hE.symm
  have : e = seedEv m W e.tid e.idx := by
    rcases e with ⟨t, i, l⟩
    change l = seedLab m W t i at hlab
    subst hlab
    rfl
  rw [← this]
  exact he

/-- Notes mp:97, p2p:101: `Z_w` is a prefix of every fragment. (The premise `hW` of the plan
is not needed: `Z_w` contains only seeds of the listed threads.) -/
theorem seed_isPrefixOf (_hW : ∀ t ∉ P.threads ++ ι, W t = [])
    (hH : Frag M (P.seedRes ι hι m u W) W H) :
    (seedGraph (P.threads ++ ι) m W).IsPrefixOf H := by
  have hw := M.wf _ hH.1.2
  have hsub : ∀ x ∈ (seedGraph (P.threads ++ ι) m W : Graph Q).events, x ∈ H.events := by
    intro x hx
    obtain ⟨-, hj, hx⟩ := mem_seedGraph.mp hx
    rw [hx]
    exact frag_seedEv hH hj
  refine isPrefixOf_of seedGraph_wf hw hsub (fun a b hab hb => ?_) (fun x hx => ?_)
    (fun x hx => ?_)
  · have hb := Finset.mem_inter.mp (Finset.mem_coe.mp hb)
    obtain ⟨-, hj, hbe⟩ := mem_seedGraph.mp hb.2
    rcases hab with ⟨ha, -, ht, hi⟩ | ⟨-, hrf⟩
    · have hj' : a.idx < (W a.tid).length := by rw [ht]; omega
      have haS : seedEv m W a.tid a.idx ∈ (seedGraph (P.threads ++ ι) m W : Graph Q).events :=
        mem_seedGraph.mpr ⟨ht ▸ (mem_seedGraph.mp hb.2).1, hj', rfl⟩
      have := hw.idx_inj a ha _ (hsub _ haS) rfl rfl
      rw [this]
      exact Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨hsub _ haS, haS⟩)
    · have hR := (hw.rf_match _ _ hrf).isRecv
      have hS : b.IsSend := by rw [hbe]; exact seedLab_isSend hj
      exact absurd hR (Lab.IsSend.not_isRecv hS)
  · have hS := seedGraph_props.1 x hx
    exact (hw.rf_none (Or.inr hS.1)).symm
  · have hS := seedGraph_props.1 x hx
    exact (hw.nd_none (Or.inr hS.2)).symm

/-- def:env: an idle thread performs exactly its seeds in a fragment. -/
theorem frag_cnt_idle (hH : Frag M (P.seedRes ι hι m u W) W H) {t : Tid} (ht : t ∈ ι)
    (hν : t ∉ P.threads) : H.cnt t = (W t).length := by
  have hw := M.wf _ hH.1.2
  refine le_antisymm ?_ (hH.2 t)
  by_contra hlt
  push Not at hlt
  obtain ⟨e, he, rfl, hi⟩ := (hw.exists_idx_iff t (W t).length).mpr hlt
  have hE := hH.1.1 e he
  change (if e.tid ∈ P.threads then _ else _) = _ at hE
  have hl : (W e.tid).length ≤ (H.traceBefore e.tid e.idx).length := by
    rw [traceBefore_length, hi]
  simp only [hν, ht, ↓reduceIte, prefixStep_of_le hl] at hE
  cases hE

end Ind

end Must
