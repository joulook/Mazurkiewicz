import Mazurkiewicz.Condpor.Rmw.LifecycleGate3Bwd

/-!
# Gate clause 3, part 4: what a graph determines about the order of a run (LC2-c)

For a builder with the invariant `GB.Ok` (events oldest first in `L`, `rf` = the last earlier
write, `co` = the writes in `L` order):

* `pre` lemmas (`pre_antisymm`, `pre_total`, `pre_filter`, `pre_append_not_mem`, …);
* `wr_before_rd`: a write `e` of `x` is before a read `f` of `x` iff the source of `f` is `e` or
  a `co`-later write than `e` — a condition on `rf` and `co` only (`RdBef`);
* **`order_conflict`**: two `Ok` builders with the same events, `rf`, `co` order every pair of
  conflicting events (same location, at least one write) in the same way;
* the events emitted by an occurrence (`evs`, `emit_L`), by a list of occurrences
  (`foldl_emit_L`), and by `finalize` (`finalize_L`: reads and local events only).
-/

namespace Condpor

namespace Life

namespace Sem

open _root_.List

variable {P : LProg}

/-! ### `pre` -/

theorem pre_cons_self (e : TEv) (B : List TEv) : pre (e :: B) e = [] := by simp [pre]

theorem pre_cons_ne {a e : TEv} (h : a ≠ e) (B : List TEv) : pre (a :: B) e = a :: pre B e := by
  simp [pre, h]

theorem pre_append_not_mem {A B : List TEv} {e : TEv} (h : e ∉ A) :
    pre (A ++ B) e = A ++ pre B e := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    have ha : a ≠ e := fun h' => h (h' ▸ mem_cons_self)
    rw [cons_append, pre_cons_ne ha, ih (fun h' => h (mem_cons_of_mem _ h')), cons_append]

theorem pre_append_mem {A B : List TEv} {e : TEv} (h : e ∈ A) : pre (A ++ B) e = pre A e := by
  induction A with
  | nil => cases h
  | cons a A ih =>
    by_cases ha : a = e
    · subst ha; rw [cons_append, pre_cons_self, pre_cons_self]
    · rw [cons_append, pre_cons_ne ha, pre_cons_ne ha,
        ih ((mem_cons.mp h).resolve_left (Ne.symm ha))]

theorem mem_pre {L : List TEv} {e f : TEv} (h : e ∈ pre L f) : e ∈ L ∧ e ≠ f := by
  induction L with
  | nil => simp [pre] at h
  | cons a L ih =>
    by_cases ha : a = f
    · rw [ha, pre_cons_self] at h; cases h
    · rw [pre_cons_ne ha] at h
      rcases mem_cons.mp h with rfl | h
      · exact ⟨mem_cons_self, ha⟩
      · exact ⟨mem_cons_of_mem _ (ih h).1, (ih h).2⟩

theorem pre_antisymm {L : List TEv} {e f : TEv} (h1 : e ∈ pre L f) (h2 : f ∈ pre L e) : False := by
  by_cases hf : f ∈ L
  · obtain ⟨post, hp⟩ := pre_split hf
    generalize hP : pre L f = P1 at hp h1
    subst hp
    rw [pre_append_mem h1] at h2
    have h3 := (mem_pre h2).1
    rw [← hP] at h3
    exact (mem_pre h3).2 rfl
  · exact hf (mem_pre h2).1

theorem pre_total {L : List TEv} {e f : TEv} (he : e ∈ L) (hf : f ∈ L) (hne : e ≠ f)
    (h : f ∉ pre L e) : e ∈ pre L f := by
  obtain ⟨post, hp⟩ := pre_split he
  generalize pre L e = P1 at hp h
  subst hp
  rw [pre_append_not_mem h, pre_cons_ne hne]
  exact mem_append_right _ mem_cons_self

theorem pre_filter (L : List TEv) {p : TEv → Bool} {e f : TEv} (he : p e = true)
    (hf : p f = true) : e ∈ pre L f ↔ e ∈ pre (L.filter p) f := by
  induction L with
  | nil => simp [pre]
  | cons a L ih =>
    by_cases haf : a = f
    · subst haf
      rw [filter_cons_of_pos hf, pre_cons_self, pre_cons_self]
    · by_cases hpa : p a = true
      · rw [filter_cons_of_pos hpa, pre_cons_ne haf, pre_cons_ne haf, mem_cons, mem_cons, ih]
      · rw [filter_cons_of_neg hpa, pre_cons_ne haf, mem_cons, ← ih]
        constructor
        · rintro (rfl | h)
          · exact absurd he hpa
          · exact h
        · exact Or.inr

/-- In a prefix `W` of a list without repetition, membership is "at or before the last
element of `W`". -/
theorem mem_prefix_iff {W c : List TEv} (hW : W <+: c) (hc : c.Nodup) (e : TEv) :
    e ∈ W ↔ ∃ w, W.getLast? = some w ∧ (e = w ∨ e ∈ pre c w) := by
  rcases eq_nil_or_concat W with rfl | ⟨W', w, rfl⟩
  · simp
  · obtain ⟨R, hR⟩ := hW
    subst hR
    rw [concat_eq_append] at hc ⊢
    have hw : w ∉ W' := by
      intro h
      have := (nodup_append.mp (nodup_append.mp hc).1).2.2
      exact this w h w (mem_singleton_self w) rfl
    have hp : pre (W' ++ [w] ++ R) w = W' := by
      rw [append_assoc, pre_append_not_mem hw, singleton_append, pre_cons_self, append_nil]
    simp only [getLast?_concat, Option.some.injEq, exists_eq_left', hp, mem_append,
      mem_singleton]
    tauto

/-! ### Facts of an `Ok` builder -/

theorem GB.Ok.rf_of_mem {g : GB} (hg : g.Ok) {e : TEv} (he : e ∈ g.L) (hr : isReadB e = true) :
    g.rf e = some (lastW (pre g.L e) e.act.loc) := by
  simp only [hg.rf e, he, hr, and_self, ite_true]

theorem GB.Ok.last_eqW {g : GB} (hg : g.Ok) (x : Loc) : g.last x = lastW g.L x := by
  unfold GB.last lastW; rw [hg.co x]
  cases (filter (writesB x) g.L).getLast? <;> rfl

theorem GB.Ok.uniq {g : GB} (hg : g.Ok) (P : LProg) {e e' : TEv} (he : e ∈ g.L) (he' : e' ∈ g.L)
    (ht : e.tid = e'.tid) (hi : e.idx = e'.idx) : e = e' :=
  (hg.wf P).1.idx_inj e ((GB.mem_events P).mpr he) e' ((GB.mem_events P).mpr he') ht hi

theorem lastW_append_nowrite {A C : List TEv} {x : Loc} (h : ∀ c ∈ C, writesB x c = false) :
    lastW (A ++ C) x = lastW A x := by
  unfold lastW
  have h0 : filter (writesB x) C = [] := filter_eq_nil_iff.mpr (fun c hc => by simp [h c hc])
  rw [filter_append, h0, append_nil]

/-- A read whose builder list is `A ++ e :: B` reads from the last write of `A`. -/
theorem GB.Ok.rf_split {h : GB} (ho : h.Ok) {A B : List TEv} {e : TEv} {x : Loc}
    (hL : h.L = A ++ e :: B) (he : e ∉ A) (hr : e.act = .read x) :
    h.rf e = some (lastW A x) := by
  have hm : e ∈ h.L := by rw [hL]; exact mem_append_right _ mem_cons_self
  rw [ho.rf_of_mem hm (by simp [isReadB, hr]), hL, pre_append_not_mem he, pre_cons_self,
    append_nil, hr]
  simp [Act.loc]

/-! ### The order of conflicting events -/

/-- The write `e` of `x` is at or before the source of `f` in `co`. -/
def RdBef (rf : TEv → Option Ev) (co : Loc → List TEv) (x : Loc) (e f : TEv) : Prop :=
  ∃ w, rf f = some (.th w) ∧ (e = w ∨ e ∈ pre (co x) w)

theorem wr_before_rd {g : GB} (hg : g.Ok) {e f : TEv} {x : Loc} {v : Val}
    (he : e.act = .write x v) (hf : f ∈ g.L) (hfr : f.act = .read x) :
    e ∈ pre g.L f ↔ RdBef g.rf g.co x e f := by
  have hrf := hg.rf_of_mem hf (by simp [isReadB, hfr])
  rw [hfr] at hrf
  simp only [Act.loc] at hrf
  have hW : (pre g.L f).filter (writesB x) <+: g.co x := by
    rw [hg.co x]; exact (takeWhile_prefix _).filter _
  have hnd : (g.co x).Nodup := by rw [hg.co]; exact hg.nodup.filter _
  have hew : writesB x e = true := by simp [writesB, he]
  have h1 : e ∈ pre g.L f ↔ e ∈ (pre g.L f).filter (writesB x) := by
    rw [mem_filter]; exact ⟨fun h => ⟨h, hew⟩, fun h => h.1⟩
  rw [h1, mem_prefix_iff hW hnd, RdBef, hrf]
  unfold lastW
  cases (filter (writesB x) (pre g.L f)).getLast? <;> simp

/-- Two events conflict: the same location, at least one of them a write. -/
def Conf (e f : TEv) : Prop :=
  ∃ x, ((∃ v, e.act = .write x v) ∧ (∃ w, f.act = .write x w)) ∨
    ((∃ v, e.act = .write x v) ∧ f.act = .read x) ∨ (e.act = .read x ∧ ∃ v, f.act = .write x v)

/-- **Conflicting events are ordered by the graph.** -/
theorem order_conflict {h1 h2 : GB} (o1 : h1.Ok) (o2 : h2.Ok) (hmem : ∀ e, e ∈ h1.L ↔ e ∈ h2.L)
    (hrf : h1.rf = h2.rf) (hco : h1.co = h2.co) {e f : TEv} (hc : Conf e f) (he : e ∈ h1.L)
    (hf : f ∈ h1.L) (h1b : e ∈ pre h1.L f) (h2b : f ∈ pre h2.L e) : False := by
  obtain ⟨x, ⟨⟨v, hev⟩, ⟨w, hfw⟩⟩ | ⟨⟨v, hev⟩, hfr⟩ | ⟨her, ⟨v, hfw⟩⟩⟩ := hc
  · have hwe : writesB x e = true := by simp [writesB, hev]
    have hwf : writesB x f = true := by simp [writesB, hfw]
    rw [pre_filter _ hwe hwf, ← o1.co x, hco, o2.co x, ← pre_filter _ hwe hwf] at h1b
    exact pre_antisymm h1b h2b
  · rw [wr_before_rd o1 hev hf hfr, hrf, hco, ← wr_before_rd o2 hev ((hmem f).mp hf) hfr] at h1b
    exact pre_antisymm h1b h2b
  · rw [wr_before_rd o2 hfw ((hmem e).mp he) her, ← hrf, ← hco,
      ← wr_before_rd o1 hfw he her] at h2b
    exact pre_antisymm h1b h2b

/-! ### Events emitted -/

/-- The label of the event of a primitive. -/
def Prim.act : Prim → Act
  | .rd _ x => .read x
  | .wr _ x v => .write x v
  | .z _ a => a

/-- The events of a list of primitives of thread `t`, from index `k`. -/
def evsF (t : Tid) : ℕ → List Prim → List TEv
  | _, [] => []
  | k, p :: ps => ⟨t, k, p.act⟩ :: evsF t (k + 1) ps

/-- The events of an occurrence emitted when its thread has `k` events. -/
def evs (P : LProg) (o : Occ) (k : ℕ) : List TEv := evsF o.tid k (prims P o)

theorem ap_L (g : GB) (p : Prim) : (g.ap p).L = g.L ++ [⟨p.tid, g.cnt p.tid, p.act⟩] := by
  cases p <;> simp [GB.ap, GB.readLast, GB.read, GB.write, GB.loc0, GB.push, GB.L, GB.ev,
    Prim.tid, Prim.act]

theorem ap_cnt (g : GB) (p : Prim) :
    (g.ap p).cnt = Function.update g.cnt p.tid (g.cnt p.tid + 1) := by
  cases p <;> rfl

theorem foldl_ap_L (t : Tid) : ∀ (ps : List Prim) (g : GB), (∀ p ∈ ps, p.tid = t) →
    (ps.foldl GB.ap g).L = g.L ++ evsF t (g.cnt t) ps ∧
      (ps.foldl GB.ap g).cnt = Function.update g.cnt t (g.cnt t + ps.length) := by
  intro ps
  induction ps with
  | nil => intro g _; simp [evsF]
  | cons p ps ih =>
    intro g h
    have hp := h p mem_cons_self
    obtain ⟨h1, h2⟩ := ih (g.ap p) (fun q hq => h q (mem_cons_of_mem _ hq))
    simp only [foldl_cons, h1, h2, ap_L, ap_cnt, hp, Function.update_self, evsF, length_cons,
      append_assoc, singleton_append, Function.update_idem]
    refine ⟨trivial, ?_⟩
    congr 1
    omega

theorem emit_L (P : LProg) (g : GB) (o : Occ) :
    (emit P g o).L = g.L ++ evs P o (g.cnt o.tid) ∧
      (emit P g o).cnt = Function.update g.cnt o.tid (g.cnt o.tid + (prims P o).length) := by
  rw [emit_eq_prims]
  exact foldl_ap_L o.tid _ g (prims_tid P o)

theorem mem_evsF {t : Tid} : ∀ {k : ℕ} {ps : List Prim} {e : TEv}, e ∈ evsF t k ps →
    e.tid = t ∧ k ≤ e.idx := by
  intro k ps
  induction ps generalizing k with
  | nil => intro e h; cases h
  | cons p ps ih =>
    intro e h
    rcases mem_cons.mp h with rfl | h
    · exact ⟨rfl, le_refl _⟩
    · have := ih h; exact ⟨this.1, by omega⟩

theorem mem_evs {o : Occ} {k : ℕ} {e : TEv} (h : e ∈ evs P o k) : e.tid = o.tid ∧ k ≤ e.idx :=
  mem_evsF h

theorem evs_head (P : LProg) (o : Occ) (k : ℕ) :
    ∃ p ps, prims P o = p :: ps ∧ evs P o k = ⟨o.tid, k, p.act⟩ :: evsF o.tid (k + 1) ps := by
  cases o <;> exact ⟨_, _, rfl, rfl⟩

theorem emit_cnt_other (P : LProg) (g : GB) {o : Occ} {t : Tid} (ht : o.tid ≠ t) :
    (emit P g o).cnt t = g.cnt t := by
  rw [(emit_L P g o).2, Function.update_of_ne (Ne.symm ht)]

theorem foldl_emit_cnt_other (P : LProg) {t : Tid} : ∀ (ys : List Occ) (g : GB),
    (∀ c ∈ ys, c.tid ≠ t) → (ys.foldl (emit P) g).cnt t = g.cnt t := by
  intro ys
  induction ys with
  | nil => intro g _; rfl
  | cons c ys ih =>
    intro g h
    rw [foldl_cons, ih _ (fun c' hc => h c' (mem_cons_of_mem _ hc)),
      emit_cnt_other P g (h c mem_cons_self)]

/-- The events emitted by a list of occurrences. -/
theorem foldl_emit_L (P : LProg) : ∀ (ys : List Occ) (g : GB), ∃ E,
    (ys.foldl (emit P) g).L = g.L ++ E ∧ (∀ e ∈ E, ∃ c ∈ ys, e.tid = c.tid) ∧
      (∀ c ∈ ys, ∃ k, ∀ e ∈ evs P c k, e ∈ E) := by
  intro ys
  induction ys with
  | nil => intro g; exact ⟨[], by simp, by simp, by simp⟩
  | cons c ys ih =>
    intro g
    obtain ⟨E, h1, h2, h3⟩ := ih (emit P g c)
    refine ⟨evs P c (g.cnt c.tid) ++ E, ?_, ?_, ?_⟩
    · rw [foldl_cons, h1, (emit_L P g c).1, append_assoc]
    · intro e he
      rcases mem_append.mp he with he | he
      · exact ⟨c, mem_cons_self, (mem_evs he).1⟩
      · obtain ⟨c', hc', h'⟩ := h2 e he
        exact ⟨c', mem_cons_of_mem _ hc', h'⟩
    · intro c' hc'
      rcases mem_cons.mp hc' with rfl | hc'
      · exact ⟨_, fun e he => mem_append_left _ he⟩
      · obtain ⟨k, hk⟩ := h3 c' hc'
        exact ⟨k, fun e he => mem_append_right _ (hk e he)⟩

theorem L_read (g : GB) (t : Tid) (x : Loc) (src : Ev) :
    (g.read t x src).L = g.L ++ [g.ev t (.read x)] := by
  simp [GB.read, GB.push, GB.L]

theorem L_loc0W (g : GB) (t : Tid) (a : Act) : (g.loc0 t a).L = g.L ++ [g.ev t a] := by
  simp [GB.loc0, GB.push, GB.L]

theorem synth_LW (P : LProg) (s : MState) (g : GB) (t : Tid) :
    ∃ S, (synth P s g t).L = g.L ++ S := by
  unfold synth
  split
  · exact ⟨_, by rw [L_loc0W, L_read, append_assoc]⟩
  · split
    · split_ifs
      · exact ⟨_, by rw [L_loc0W, GB.readLast, L_read, append_assoc]⟩
      · exact ⟨[], by simp⟩
    · split_ifs
      · exact ⟨_, by rw [L_loc0W, GB.readLast, L_read, append_assoc]⟩
      · exact ⟨[], by simp⟩
    · exact ⟨[], by simp⟩
  · exact ⟨[], by simp⟩

theorem finalize_L_co (P : LProg) (s : MState) (g : GB) :
    (∃ S, (finalize P g s).L = g.L ++ S) ∧ (finalize P g s).co = g.co := by
  unfold finalize
  suffices ∀ (l : List Tid) (g : GB), (∃ S, (l.foldl (synth P s) g).L = g.L ++ S) ∧
      (l.foldl (synth P s) g).co = g.co from this _ g
  intro l
  induction l with
  | nil => intro g; exact ⟨⟨[], by simp⟩, rfl⟩
  | cons t l ih =>
    intro g
    obtain ⟨⟨S, h1⟩, h2⟩ := ih (synth P s g t)
    obtain ⟨S', h3⟩ := synth_LW P s g t
    refine ⟨⟨S' ++ S, ?_⟩, ?_⟩
    · rw [foldl_cons, h1, h3, append_assoc]
    · rw [foldl_cons, h2, synth_co]

/-- `finalize` adds no write. -/
theorem finalize_nowrite (P : LProg) (s : MState) {g : GB} (hg : g.Ok)
    (hf : (finalize P g s).Ok) : ∃ S, (finalize P g s).L = g.L ++ S ∧
      ∀ e ∈ S, ∀ x, writesB x e = false := by
  obtain ⟨⟨S, hS⟩, hco⟩ := finalize_L_co P s g
  refine ⟨S, hS, fun e he x => ?_⟩
  have h1 := hf.co x
  rw [hco, hg.co x, hS, filter_append] at h1
  have h2 : S.filter (writesB x) = [] := by
    have := congrArg length h1
    simp only [length_append] at this
    exact length_eq_zero_iff.mp (by omega)
  have := filter_eq_nil_iff.mp h2 e he
  simpa using this

end Sem

end Life

end Condpor
