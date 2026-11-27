import Mazurkiewicz.Condpor.Rmw.LifecycleGateLast

/-!
# Gate clause 1: the events of a thread after the synthetic events (LC2-b, continuation)

`thr_finalize`: in the final builder, the events of thread `t` and their sources are those
of `synth P s g1 t`, where `g1` agrees with the run's builder `g` on `t`'s events, sources,
count and coherence.
-/

namespace Condpor

namespace Life

namespace Sem

variable {P : LProg} {s : MState}

/-- What another thread's synthetic events leave unchanged. -/
def Same (g g' : GB) (t : Tid) : Prop :=
  thr g' t = thr g t ∧ (∀ e, e.tid = t → g'.rf e = g.rf e) ∧ g'.cnt t = g.cnt t ∧ g'.co = g.co

theorem Same.refl (g : GB) (t : Tid) : Same g g t := ⟨rfl, fun _ _ => rfl, rfl, rfl⟩

theorem Same.trans {g g' g'' : GB} {t : Tid} (h1 : Same g g' t) (h2 : Same g' g'' t) :
    Same g g'' t :=
  ⟨h2.1.trans h1.1, fun e he => (h2.2.1 e he).trans (h1.2.1 e he), h2.2.2.1.trans h1.2.2.1,
    h2.2.2.2.trans h1.2.2.2⟩

theorem same_read (g : GB) {t t' : Tid} (h : t' ≠ t) (x : Loc) (src : Ev) :
    Same g (g.read t' x src) t := by
  refine ⟨by rw [thr_read]; simp [h], fun e he => ?_, by simp [GB.read, GB.push, GB.ev,
    Ne.symm h], rfl⟩
  have : e ≠ g.ev t' (.read x) := fun h' => h (by rw [← he, h']; rfl)
  simp [GB.read, GB.push, this]

theorem same_loc0 (g : GB) {t t' : Tid} (h : t' ≠ t) (a : Act) : Same g (g.loc0 t' a) t :=
  ⟨by rw [thr_loc0]; simp [h], fun _ _ => rfl, by simp [GB.loc0, GB.push, GB.ev,
    Ne.symm h], rfl⟩

theorem same_synth (P : LProg) (s : MState) (g : GB) {t t' : Tid} (h : t' ≠ t) :
    Same g (synth P s g t') t := by
  unfold synth
  split
  · exact (same_read g h _ _).trans (same_loc0 _ h _)
  · split
    · split_ifs
      · exact (same_read g h _ _).trans (same_loc0 _ h _)
      · exact Same.refl g t
    · split_ifs
      · exact (same_read g h _ _).trans (same_loc0 _ h _)
      · exact Same.refl g t
    · exact Same.refl g t
  · exact Same.refl g t

theorem same_fold (P : LProg) (s : MState) {t : Tid} :
    ∀ (l : List Tid) (g : GB), t ∉ l → Same g (l.foldl (synth P s) g) t := by
  intro l
  induction l with
  | nil => intro g _; exact Same.refl g t
  | cons t' l ih =>
    intro g h
    simp only [List.foldl_cons]
    exact (same_synth P s g (fun h' : t' = t => h (by rw [h']; exact List.mem_cons_self))).trans
      (ih _ (fun h' => h (List.mem_cons_of_mem _ h')))

/-- The final builder, for one thread. -/
theorem thr_finalize (P : LProg) (s : MState) (g : GB) {t : Tid} (ht : t ∈ P.threads) :
    ∃ g1, Same g g1 t ∧ Same (synth P s g1 t) (finalize P g s) t := by
  obtain ⟨l1, l2, hl⟩ := List.append_of_mem ht
  have hnd := P.nodup
  rw [hl] at hnd
  have h1 : t ∉ l1 := fun h => by
    have := List.nodup_append.mp hnd
    exact this.2.2 t h t List.mem_cons_self rfl
  have h2 : t ∉ l2 := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
  refine ⟨l1.foldl (synth P s) g, same_fold P s l1 g h1, ?_⟩
  unfold finalize
  rw [hl, List.foldl_append, List.foldl_cons]
  exact same_fold P s l2 _ h2

end Sem

end Life

end Condpor

namespace Condpor

namespace Life

namespace Sem

open Targets

variable {P : LProg} {s : MState}

theorem filterMap_range_eq {l : List TEv} {f : ℕ → Option TEv}
    (h : ∀ j (hj : j < l.length), f j = some l[j]) : (List.range l.length).filterMap f = l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.filterMap_append]
    have h1 : (List.range l.length).filterMap f = l := ih (fun j hj => by
      rw [h j (by simp; omega), List.getElem_append_left hj])
    have h2 := h l.length (by simp)
    rw [List.getElem_append_right (le_refl _)] at h2
    simp [h1, h2]

theorem thEvents_eq {g : GB} (hg : g.Ok) (t : Tid) : thEvents (g.toCfg P) t = thr g t := by
  have hw := hg.wf P
  unfold thEvents
  rw [Config.cnt_eq _ hw, hg.cnt_eq, ← hg.thr_length]
  exact filterMap_range_eq (fun j hj => by rw [Config.evAt_eq _ hw, hg.evAt_thr hj])

/-- The wait of a thread whose events end with `r; block`. -/
theorem waitOf_block {g : GB} (hg : g.Ok) {t : Tid} {pre : List TEv} {r b : TEv}
    (h : thr g t = pre ++ [r, b]) (hb : b.act = .block) :
    waitOf P (g.toCfg P) t = some (kindOf P (g.toCfg P) t r, finalB (g.toCfg P) r) := by
  have hw := hg.wf P
  have hlen : (thr g t).length = pre.length + 2 := by rw [h]; simp
  have hbi : b.idx = pre.length + 1 := by
    have := hg.thr_idx (t := t) (j := pre.length + 1) (by omega)
    rw [← this]; congr 1; simp [h]
  have hr : (g.toCfg P).evAt t pre.length = some r := by
    rw [Config.evAt_eq _ hw, hg.evAt_thr (by omega)]; simp [h]
  unfold waitOf
  rw [thEvents_eq hg, h]
  simp only [List.getLast?_append, List.getLast?_cons_cons, List.getLast?_singleton,
    Option.some_or, hb, ↓reduceIte, hbi, Nat.add_sub_cancel, hr]

/-- No wait for a thread whose last event is not `block`. -/
theorem waitOf_none {g : GB} (hg : g.Ok) {t : Tid} {pre : List TEv} {e : TEv}
    (h : thr g t = pre ++ [e]) (he : e.act ≠ .block) : waitOf P (g.toCfg P) t = none := by
  unfold waitOf
  rw [thEvents_eq hg, h]
  simp [he]

end Sem

end Life

end Condpor
