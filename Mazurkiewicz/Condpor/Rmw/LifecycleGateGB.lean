import Mazurkiewicz.Condpor.Rmw.LifecycleSemLemmas
import Mazurkiewicz.Lib.ListOrder

/-!
# Thread lifecycle machine: the graph builder is well-formed and SC (LC2-b, part 2)

Machine-independent facts about the graph builder `GB`. The chronological list `g.L` (oldest
first) and the invariant `GB.Ok`:

* events have fresh identifiers, contiguous per thread, increasing in time per thread;
* every read reads the last write to its location that is earlier in `g.L` (else `init`);
* `co x` is the list of the writes to `x` in the order of `g.L`;
* no constraint evaluation.

`GB.Ok` holds for `GB.empty` and is preserved by `readLast`, `write`, `loc0` and by a read
from `init` of a location without writes (`ok_read_init`). An `Ok` builder gives a
well-formed configuration (`GB.Ok.wf`) whose graph is SC-consistent (`GB.Ok.sc`): every
`po`, `rf`, `co`, `fr` edge goes forward in `g.L`.
-/

namespace Condpor

namespace Life

namespace Sem

open List

/-- The events of the builder, oldest first. -/
def GB.L (g : GB) : List TEv := g.order.reverse

/-- `e` writes `x`. -/
def writesB (x : Loc) (e : TEv) : Bool :=
  match e.act with
  | .write y _ => decide (y = x)
  | _ => false

/-- `e` is a read. -/
def isReadB (e : TEv) : Bool :=
  match e.act with
  | .read _ => true
  | _ => false

/-- The last write to `x` in `l`, else `init`. -/
def lastW (l : List TEv) (x : Loc) : Ev :=
  match (l.filter (writesB x)).getLast? with
  | some w => .th w
  | none => .init

/-- The events before `e` in `L`. -/
def pre (L : List TEv) (e : TEv) : List TEv := L.takeWhile (fun a => decide (a ≠ e))

/-- The invariant of the graph builder. -/
structure GB.Ok (g : GB) : Prop where
  nodup : g.L.Nodup
  lt_cnt : ∀ e ∈ g.L, e.idx < g.cnt e.tid
  present : ∀ t i, i < g.cnt t → ∃ e ∈ g.L, e.tid = t ∧ e.idx = i
  mono : ∀ a b, g.L.Before a b → a.tid = b.tid → a.idx < b.idx
  rf : ∀ e, g.rf e = if e ∈ g.L ∧ isReadB e = true then some (lastW (pre g.L e) e.act.loc)
    else none
  co : ∀ x, g.co x = g.L.filter (writesB x)
  noCons : ∀ e ∈ g.L, ¬ e.IsCons
  thrIdx : ∀ t, (g.L.filter (fun e => decide (e.tid = t))).map TEv.idx = List.range (g.cnt t)

/-! ### List lemmas -/

theorem pre_append_of_mem {L : List TEv} {e a : TEv} (h : a ∈ L) :
    pre (L ++ [e]) a = pre L a := by
  unfold pre
  induction L with
  | nil => cases h
  | cons b L ih =>
    by_cases hb : b = a
    · subst hb; simp
    · simp only [cons_append, takeWhile_cons, ne_eq, hb, not_false_eq_true, decide_true]
      rw [ih ((mem_cons.mp h).resolve_left (Ne.symm hb))]

theorem pre_append_self {L : List TEv} {e : TEv} (h : e ∉ L) : pre (L ++ [e]) e = L := by
  unfold pre
  induction L with
  | nil => simp
  | cons b L ih =>
    have hb : b ≠ e := fun h' => h (h' ▸ mem_cons_self)
    simp only [cons_append, takeWhile_cons, ne_eq, hb, not_false_eq_true, decide_true]
    rw [ih (fun h' => h (mem_cons_of_mem _ h'))]
    simp

theorem pre_split {L : List TEv} {e : TEv} (h : e ∈ L) :
    ∃ post, L = pre L e ++ e :: post := by
  unfold pre
  induction L with
  | nil => cases h
  | cons b L ih =>
    by_cases hb : b = e
    · subst hb; exact ⟨L, by simp⟩
    · obtain ⟨post, hp⟩ := ih ((mem_cons.mp h).resolve_left (Ne.symm hb))
      refine ⟨post, ?_⟩
      simp only [takeWhile_cons, ne_eq, hb, not_false_eq_true, decide_true]
      exact congrArg _ hp

theorem pre_sublist (L : List TEv) (e : TEv) : (pre L e) <+ L := takeWhile_sublist _

/-! ### Preservation -/

theorem ok_empty : GB.empty.Ok where
  nodup := by simp [GB.L, GB.empty]
  lt_cnt := by simp [GB.L, GB.empty]
  present := by simp [GB.empty]
  mono := fun a b h => absurd h.1 (by simp [GB.L, GB.empty])
  rf := by simp [GB.L, GB.empty]
  co := by simp [GB.L, GB.empty]
  noCons := by simp [GB.L, GB.empty]
  thrIdx := by simp [GB.L, GB.empty]

theorem GB.L_push (g : GB) (e : TEv) : (g.push e).L = g.L ++ [e] := by
  simp [GB.L, GB.push]

theorem GB.Ok.not_mem_ev {g : GB} (hg : g.Ok) (t : Tid) (a : Act) : g.ev t a ∉ g.L := by
  intro h
  have := hg.lt_cnt _ h
  simp [GB.ev] at this

/-- The structural part of the invariant after adding a fresh event. -/
theorem GB.Ok.push_struct {g : GB} (hg : g.Ok) (t : Tid) (a : Act) :
    (g.push (g.ev t a)).L.Nodup ∧
      (∀ e ∈ (g.push (g.ev t a)).L, e.idx < (g.push (g.ev t a)).cnt e.tid) ∧
      (∀ t' i, i < (g.push (g.ev t a)).cnt t' →
        ∃ e ∈ (g.push (g.ev t a)).L, e.tid = t' ∧ e.idx = i) ∧
      (∀ x y, (g.push (g.ev t a)).L.Before x y → x.tid = y.tid → x.idx < y.idx) := by
  have hn := hg.not_mem_ev t a
  rw [GB.L_push]
  refine ⟨nodup_append.mpr ⟨hg.nodup, nodup_singleton _, ?_⟩, ?_, ?_, ?_⟩
  · intro x hx y hy; rw [mem_singleton] at hy; subst hy; exact fun h => hn (h ▸ hx)
  · intro e he
    rcases mem_append.mp he with he | he
    · have := hg.lt_cnt e he
      simp only [GB.push, GB.ev, Function.update_apply]
      split_ifs with h
      · rw [h] at this; omega
      · exact this
    · simp only [mem_singleton] at he; subst he; simp [GB.push, GB.ev]
  · intro t' i hi
    simp only [GB.push, GB.ev, Function.update_apply] at hi
    split_ifs at hi with h
    · subst h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · obtain ⟨e, he, h1, h2⟩ := hg.present _ i hi
        exact ⟨e, mem_append_left _ he, h1, h2⟩
      · exact ⟨g.ev _ a, by simp, rfl, by simp [GB.ev, hi]⟩
    · obtain ⟨e, he, h1, h2⟩ := hg.present t' i hi
      exact ⟨e, mem_append_left _ he, h1, h2⟩
  · intro x y h hxy
    rcases (before_append_singleton_iff hn).mp h with h | ⟨hx, rfl⟩
    · exact hg.mono x y h hxy
    · have := hg.lt_cnt x hx
      simp only [GB.ev] at hxy ⊢
      rw [hxy] at this
      exact this

theorem GB.Ok.push_thrIdx {g : GB} (hg : g.Ok) (t : Tid) (a : Act) (t' : Tid) :
    ((g.push (g.ev t a)).L.filter (fun e => decide (e.tid = t'))).map TEv.idx =
      List.range ((g.push (g.ev t a)).cnt t') := by
  rw [GB.L_push, filter_append, map_append, hg.thrIdx t']
  simp only [GB.push, GB.ev, Function.update_apply]
  by_cases h : t = t'
  · subst h; simp [range_succ]
  · simp [h, Ne.symm h]

theorem lastW_append_nonwrite {L : List TEv} {e : TEv} {x : Loc} (h : writesB x e = false) :
    lastW (L ++ [e]) x = lastW L x := by
  simp [lastW, filter_append, h]

/-- Adding a read of `x` from the last write to `x`. -/
theorem GB.Ok.readLast {g : GB} (hg : g.Ok) (t : Tid) (x : Loc) : (g.readLast t x).Ok := by
  obtain ⟨h1, h2, h3, h4⟩ := hg.push_struct t (.read x)
  have hn := hg.not_mem_ev t (.read x)
  have hL : (g.readLast t x).L = g.L ++ [g.ev t (.read x)] := GB.L_push g _
  refine ⟨hL ▸ h1, hL ▸ h2, hL ▸ h3, hL ▸ h4, ?_, ?_, ?_, hg.push_thrIdx _ _⟩
  · intro e
    rw [hL]
    simp only [GB.readLast, GB.read]
    by_cases he : e = g.ev t (.read x)
    · subst he
      rw [pre_append_self hn]
      simp [isReadB, GB.ev, GB.last, lastW, hg.co x, Act.loc]
      rfl
    · simp only [he, ↓reduceIte]
      rw [hg.rf e]
      by_cases hm : e ∈ g.L
      · rw [pre_append_of_mem hm]; simp [hm]
      · simp [hm, he]
  · intro y
    rw [hL, filter_append]
    simp [GB.readLast, GB.read, GB.push, hg.co y, writesB, GB.ev]
  · intro e he
    rw [hL] at he
    rcases mem_append.mp he with he | he
    · exact hg.noCons e he
    · rw [mem_singleton] at he; subst he; simp [GB.ev, TEv.IsCons, Act.IsCons]

/-- Adding a read of `x` from `init`, when `x` has no write. -/
theorem GB.Ok.read_init {g : GB} (hg : g.Ok) (t : Tid) (x : Loc) (hx : g.co x = []) :
    (g.read t x .init).Ok := by
  have : g.last x = .init := by simp [GB.last, hx]
  have h := hg.readLast t x
  simp only [GB.readLast, this] at h
  exact h

/-- Adding a write of `v` to `x`, last in the coherence order. -/
theorem GB.Ok.write {g : GB} (hg : g.Ok) (t : Tid) (x : Loc) (v : Val) : (g.write t x v).Ok := by
  obtain ⟨h1, h2, h3, h4⟩ := hg.push_struct t (.write x v)
  have hn := hg.not_mem_ev t (.write x v)
  have hL : (g.write t x v).L = g.L ++ [g.ev t (.write x v)] := GB.L_push g _
  refine ⟨hL ▸ h1, hL ▸ h2, hL ▸ h3, hL ▸ h4, ?_, ?_, ?_, hg.push_thrIdx _ _⟩
  · intro e
    rw [hL]
    simp only [GB.write, GB.push]
    rw [hg.rf e]
    by_cases he : e = g.ev t (.write x v)
    · subst he; simp [isReadB, GB.ev]
    · by_cases hm : e ∈ g.L
      · rw [pre_append_of_mem hm]; simp [hm]
      · simp [hm, he]
  · intro y
    rw [hL, filter_append]
    simp only [GB.write, GB.push, Function.update_apply, hg.co]
    by_cases hy : y = x
    · subst hy; simp [writesB, GB.ev]
    · simp [hy, writesB, GB.ev, Ne.symm hy]
  · intro e he
    rw [hL] at he
    rcases mem_append.mp he with he | he
    · exact hg.noCons e he
    · rw [mem_singleton] at he; subst he; simp [GB.ev, TEv.IsCons, Act.IsCons]

/-- Adding an event without location and not a constraint evaluation. -/
theorem GB.Ok.loc0 {g : GB} (hg : g.Ok) (t : Tid) (a : Act) (hr : a.IsLocal) (hc : ¬ a.IsCons) :
    (g.loc0 t a).Ok := by
  obtain ⟨h1, h2, h3, h4⟩ := hg.push_struct t a
  have hn := hg.not_mem_ev t a
  have hL : (g.loc0 t a).L = g.L ++ [g.ev t a] := GB.L_push g _
  have hrd : isReadB (g.ev t a) = false := by
    cases a <;> simp_all [isReadB, GB.ev, Act.IsLocal]
  have hwr : ∀ y, writesB y (g.ev t a) = false := by
    intro y; cases a <;> simp_all [writesB, GB.ev, Act.IsLocal]
  refine ⟨hL ▸ h1, hL ▸ h2, hL ▸ h3, hL ▸ h4, ?_, ?_, ?_, hg.push_thrIdx _ _⟩
  · intro e
    rw [hL]
    simp only [GB.loc0, GB.push]
    rw [hg.rf e]
    by_cases he : e = g.ev t a
    · subst he; simp [hn, hrd]
    · by_cases hm : e ∈ g.L
      · rw [pre_append_of_mem hm]; simp [hm]
      · simp [hm, he]
  · intro y
    rw [hL, filter_append]
    simp [GB.loc0, GB.push, hg.co y, hwr y]
  · intro e he
    rw [hL] at he
    rcases mem_append.mp he with he | he
    · exact hg.noCons e he
    · rw [mem_singleton] at he; subst he; exact hc

/-! ### Well-formedness and SC -/

theorem GB.mem_events {g : GB} (P : LProg) {e : TEv} : e ∈ (g.toCfg P).abs.events ↔ e ∈ g.L := by
  simp [GB.toCfg, Config.abs, GB.L]

theorem writesB_iff {x : Loc} {e : TEv} : writesB x e = true ↔ ∃ v, e.act = .write x v := by
  unfold writesB
  split <;> simp_all

theorem isReadB_iff {e : TEv} : isReadB e = true ↔ e.IsRead := by
  unfold isReadB TEv.IsRead Act.IsRead
  split <;> simp_all

theorem lastW_isWriteTo {g : GB} (P : LProg) (l : List TEv) (hl : l ⊆ g.L) (x : Loc) :
    (g.toCfg P).abs.IsWriteTo x (lastW l x) := by
  unfold lastW
  split
  next w hw =>
    have hm := mem_of_getLast? hw
    obtain ⟨hm1, hm2⟩ := mem_filter.mp hm
    exact ⟨(GB.mem_events P).mpr (hl hm1), writesB_iff.mp hm2⟩
  next => trivial

/-- **An `Ok` builder gives a well-formed configuration.** -/
theorem GB.Ok.wf {g : GB} (hg : g.Ok) (P : LProg) : (g.toCfg P).Wf := by
  have hev := fun e => (GB.mem_events (g := g) P (e := e))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e he e' he' ht hi
    rw [hev] at he he'
    by_contra hne
    rcases Before.total he he' hne with h | h
    · have := hg.mono e e' h ht; omega
    · have := hg.mono e' e h ht.symm; omega
  · intro e he i hi
    rw [hev] at he
    obtain ⟨e', he', h1, h2⟩ := hg.present e.tid i (by have := hg.lt_cnt e he; omega)
    exact ⟨e', (hev e').mpr he', h1, h2⟩
  · intro e he x hx
    rw [hev] at he
    have hr : isReadB e = true := isReadB_iff.mpr (by simp [TEv.IsRead, hx, Act.IsRead])
    refine ⟨_, ?_, lastW_isWriteTo P (pre g.L e) (pre_sublist _ _).subset x⟩
    simp only [GB.toCfg, Config.abs]
    rw [hg.rf e, ite_eq_left_of_eq_true _ _ (eq_true ⟨he, hr⟩), hx]
    rfl
  · intro e he
    simp only [GB.toCfg, Config.abs]
    rw [hg.rf e, ite_eq_right_of_eq_false _ _ (eq_false ?_)]
    rintro ⟨h1, h2⟩
    rcases he with he | he
    · exact he ((hev e).mpr h1)
    · exact he (isReadB_iff.mp h2)
  · intro x e
    simp only [GB.toCfg, Config.abs]
    rw [hg.co x, mem_filter, writesB_iff, ← hev]
    rfl
  · intro x
    simp only [GB.toCfg, Config.abs]
    rw [hg.co x]
    exact hg.nodup.filter _
  · intro e
    simp only [GB.toCfg, Config.abs, Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
    intro he
    exact hg.noCons e ((hev e).mp he)
  · simpa [GB.toCfg, GB.L] using hg.nodup

/-- The order in which the edges of an `Ok` builder go: `init` first, then `g.L`. -/
def GB.Fwd (g : GB) : Ev → Ev → Prop
  | .init, .th e => e ∈ g.L
  | .th e, .th e' => g.L.Before e e'
  | _, .init => False

theorem GB.Fwd.trans {g : GB} {a b c : Ev} (h1 : g.Fwd a b) (h2 : g.Fwd b c) : g.Fwd a c := by
  cases a <;> cases b <;> cases c <;> simp only [GB.Fwd] at h1 h2 ⊢
  · exact h2.2.1
  · exact h1.trans h2

theorem GB.Fwd.irrefl {g : GB} (a : Ev) : ¬ g.Fwd a a := by
  cases a <;> simp [GB.Fwd, Before.irrefl]

theorem before_append_of_mem {l1 l2 : List TEv} (hn : (l1 ++ l2).Nodup) {a b : TEv}
    (ha : a ∈ l1) (hb : b ∈ l2) : (l1 ++ l2).Before a b := by
  have hb1 : b ∉ l1 := fun h => (nodup_append.mp hn).2.2 _ h _ hb rfl
  refine ⟨mem_append_left _ ha, mem_append_right _ hb, ?_⟩
  rw [idxOf_append_of_mem ha, idxOf_append_of_notMem hb1]
  have := idxOf_lt_length_of_mem ha
  omega

theorem before_of_pre {L : List TEv} (hL : L.Nodup) {e w : TEv} (he : e ∈ L) (hw : w ∈ pre L e) :
    L.Before w e := by
  obtain ⟨post, hp⟩ := pre_split he
  rw [hp] at hL ⊢
  exact before_append_of_mem hL hw mem_cons_self

/-- A write to `x` that is coherence-after the source of the read `e` of `x` comes after `e`. -/
theorem fr_fwd {L : List TEv} (hL : L.Nodup) {e e' : TEv} {x : Loc} (he : e ∈ L)
    (hne : writesB x e = false) (he' : e' ∈ L.filter (writesB x))
    (hs : lastW (pre L e) x = .init ∨
      ∃ w, lastW (pre L e) x = .th w ∧ (L.filter (writesB x)).Before w e') :
    L.Before e e' := by
  obtain ⟨post, hp⟩ := pre_split he
  have hfl : L.filter (writesB x) = (pre L e).filter (writesB x) ++ post.filter (writesB x) := by
    conv_lhs => rw [hp]
    simp [filter_append, hne]
  have hnd : (L.filter (writesB x)).Nodup := hL.filter _
  have hin : e' ∈ post := by
    rw [hfl] at he'
    rcases mem_append.mp he' with h | h
    · exfalso
      rcases hs with hs | ⟨w, hw, hb⟩
      · unfold lastW at hs
        split at hs
        · cases hs
        next hn => rw [getLast?_eq_none_iff] at hn; rw [hn] at h; cases h
      · unfold lastW at hw
        split at hw
        next w' hw' =>
          cases hw
          obtain ⟨l1, hl1⟩ := getLast?_eq_some_iff.mp hw'
          rw [hfl, hl1] at hb hnd
          rw [hl1] at h
          rcases mem_append.mp h with h | h
          · have := before_append_of_mem (l1 := l1) (l2 := [w] ++ post.filter (writesB x))
              (a := e') (b := w)
              (by simpa [append_assoc] using hnd) h (by simp)
            rw [← append_assoc] at this
            exact this.asymm hb
          · rw [mem_singleton] at h; subst h; exact Before.irrefl _ _ hb
        · cases hw
    · exact (mem_filter.mp h).1
  rw [hp] at hL ⊢
  have := before_append_of_mem (l1 := pre L e ++ [e]) (l2 := post) (a := e) (by simpa using hL)
    (by simp) hin
  simpa using this

/-- **An `Ok` builder gives an SC-consistent graph.** -/
theorem GB.Ok.sc {g : GB} (hg : g.Ok) (P : LProg) : SC.cons (g.toCfg P).abs := by
  have hev := fun e => (GB.mem_events (g := g) P (e := e))
  have hstep : ∀ a b, (g.toCfg P).abs.scStep a b → g.Fwd a b := by
    intro a b h
    rcases h with h | h | h | h
    · -- po
      cases a <;> cases b <;> simp only [Graph.po] at h
      · exact (hev _).mp h
      · obtain ⟨h1, h2, h3, h4⟩ := h
        rw [hev] at h1 h2
        rename_i e e'
        have hne : e ≠ e' := fun h => by subst h; omega
        rcases Before.total h1 h2 hne with hb | hb
        · exact hb
        · have := hg.mono _ _ hb h3.symm; omega
    · -- rf
      obtain ⟨e, rfl, he, hr⟩ := h
      rw [hev] at he
      simp only [GB.toCfg, Config.abs] at hr
      rw [hg.rf e] at hr
      split_ifs at hr with hc
      cases hr
      unfold lastW
      split
      next w hw =>
        exact before_of_pre hg.nodup he (mem_filter.mp (mem_of_getLast? hw)).1
      next => exact he
    · -- co
      cases a <;> cases b <;> simp only [Graph.coRel] at h
      · obtain ⟨x, hx⟩ := h
        simp only [GB.toCfg, Config.abs] at hx
        rw [hg.co x] at hx
        exact (mem_filter.mp hx).1
      · obtain ⟨x, hx⟩ := h
        simp only [GB.toCfg, Config.abs] at hx
        rw [hg.co x] at hx
        exact (before_filter_iff.mp hx).1
    · -- fr
      obtain ⟨e, e', x, rfl, rfl, he, hact, he', hsrc⟩ := h
      rw [hev] at he
      simp only [GB.toCfg, Config.abs] at he' hsrc
      have hrd : isReadB e = true := by simp [isReadB, hact]
      rw [hg.rf e, ite_eq_left_of_eq_true _ _ (eq_true ⟨he, hrd⟩), hact] at hsrc
      simp only [Act.loc, Option.some.injEq] at hsrc
      have hs : lastW (pre g.L e) x = .init ∨
          ∃ w, lastW (pre g.L e) x = .th w ∧ (g.L.filter (writesB x)).Before w e' := by
        rcases hsrc with h | ⟨w, hw, hb⟩
        · exact Or.inl h
        · exact Or.inr ⟨w, hw, by rw [← hg.co x]; exact hb⟩
      rw [hg.co x] at he'
      exact fr_fwd hg.nodup he (by simp [writesB, hact]) he' hs
  have key : ∀ a b, Relation.TransGen (g.toCfg P).abs.scStep a b → g.Fwd a b := by
    intro a b h
    induction h with
    | single h => exact hstep _ _ h
    | tail _ h ih => exact ih.trans (hstep _ _ h)
  intro a h
  exact GB.Fwd.irrefl a (key a a h)

end Sem

end Life

end Condpor
