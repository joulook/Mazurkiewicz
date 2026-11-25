import Mazurkiewicz.Condpor.Rmw.LifecycleGateFinal

/-!
# Gate clause 1: atomicity (LC2-b, continuation)

`AInv P n g`: every write of thread `t` whose compiled flag is exclusive follows, in its
thread, a read whose source is the coherence predecessor of the write (`ImmCoG`).
It holds initially, is preserved by steps (`AInv.step`) and by the synthetic events, and
gives atomicity (`atomic_of_ainv`). `g1Atomic : G1Atomic`.
-/

namespace Condpor

namespace Life

namespace Sem

variable {P : LProg} {n : ℕ} {s : MState} {g : GB}

/-- `w` is the immediate coherence successor of `src` at `x` in the builder. -/
def ImmCoG (g : GB) (x : Loc) : Ev → TEv → Prop
  | .init, w => ∃ l, g.co x = w :: l
  | .th p, w => ∃ l₁ l₂, g.co x = l₁ ++ p :: w :: l₂

theorem ImmCoG.mono {g g' : GB} {x : Loc} {src : Ev} {w : TEv}
    (hco : ∃ l', g'.co x = g.co x ++ l') (h : ImmCoG g x src w) : ImmCoG g' x src w := by
  obtain ⟨l', hl'⟩ := hco
  cases src with
  | init => obtain ⟨l, hl⟩ := h; exact ⟨l ++ l', by rw [hl', hl]; rfl⟩
  | th p => obtain ⟨l₁, l₂, hl⟩ := h; exact ⟨l₁, l₂ ++ l', by rw [hl', hl]; simp⟩

/-- The atomicity invariant. -/
def AInv (P : LProg) (n : ℕ) (g : GB) : Prop :=
  ∀ t (pre : List TEv) (w : TEv) (post : List TEv), thr g t = pre ++ w :: post → w.IsWrite →
    (lifeSys P n).ex t (pre.map (retG P g)) = true →
    ∃ r pre', pre = pre' ++ [r] ∧ ∃ src, g.rf r = some src ∧ ImmCoG g w.act.loc src w

theorem ainv_empty : AInv P n GB.empty := by
  intro t pre w post h
  simp [thr, GB.L, GB.empty] at h

theorem snoc_eq_append_cons {l pre post : List TEv} {e w : TEv}
    (h : l ++ [e] = pre ++ w :: post) :
    (post = [] ∧ w = e ∧ pre = l) ∨ ∃ post', post = post' ++ [e] ∧ l = pre ++ w :: post' := by
  rcases List.eq_nil_or_concat post with rfl | ⟨post', b, rfl⟩
  · left
    have := List.append_inj' h rfl
    simp only [List.cons.injEq, and_true] at this
    exact ⟨rfl, this.2.symm, this.1.symm⟩
  · right
    rw [List.concat_eq_append, ← List.cons_append, ← List.append_assoc] at h
    have := List.append_inj' h rfl
    simp only [List.cons.injEq, and_true] at this
    exact ⟨post', by rw [this.2, List.concat_eq_append], this.1⟩

/-- `AInv` under adding an event. -/
theorem AInv.push {g g' : GB} (hA : AInv P n g) {t : Tid} {a : Act}
    (hL : g'.L = g.L ++ [g.ev t a]) (hrf : ∀ e ∈ g.L, g'.rf e = g.rf e)
    (hco : ∀ x, ∃ l', g'.co x = g.co x ++ l') (hret : ∀ e ∈ g.L, retG P g' e = retG P g e)
    (hnew : (g.ev t a).IsWrite → (lifeSys P n).ex t (tr P g t) = true →
      ∃ r pre', thr g t = pre' ++ [r] ∧ ∃ src, g'.rf r = some src ∧
        ImmCoG g' (g.ev t a).act.loc src (g.ev t a)) : AInv P n g' := by
  intro t' pre w post h hw hex
  have hsub : ∀ l : List TEv, l ⊆ thr g t' → l.map (retG P g') = l.map (retG P g) :=
    fun l hl => List.map_congr_left (fun e he => hret e (List.mem_filter.mp (hl he)).1)
  rw [thr_append hL] at h
  by_cases htt : (g.ev t a).tid = t'
  · simp only [htt, ↓reduceIte] at h
    rcases snoc_eq_append_cons h with ⟨rfl, rfl, rfl⟩ | ⟨post', rfl, h'⟩
    · rw [hsub _ (List.Subset.refl _)] at hex
      simp only [GB.ev] at htt
      subst htt
      exact hnew hw (by simpa [tr] using hex)
    · have hpre : pre ⊆ thr g t' := by rw [h']; exact List.subset_append_left _ _
      rw [hsub _ hpre] at hex
      obtain ⟨r, pre', hp, src, hr, hi⟩ := hA t' pre w post' h' hw hex
      refine ⟨r, pre', hp, src, ?_, hi.mono (hco _)⟩
      rw [hrf r (List.mem_filter.mp (hpre (by rw [hp]; simp))).1]; exact hr
  · simp only [htt, ↓reduceIte, List.append_nil] at h
    have hpre : pre ⊆ thr g t' := by rw [h]; exact List.subset_append_left _ _
    rw [hsub _ hpre] at hex
    obtain ⟨r, pre', hp, src, hr, hi⟩ := hA t' pre w post h hw hex
    refine ⟨r, pre', hp, src, ?_, hi.mono (hco _)⟩
    rw [hrf r (List.mem_filter.mp (hpre (by rw [hp]; simp))).1]; exact hr

theorem AInv.read (hA : AInv P n g) (hg : g.Ok) (t : Tid) (x : Loc) (src : Ev) :
    AInv P n (g.read t x src) := by
  have hn := hg.not_mem_ev t (.read x)
  refine hA.push (GB.L_push g _) (fun e he => ?_) (fun x => ⟨[], by simp [GB.read, GB.push]⟩)
    (retG_read hg t x src).1 (fun hw => by simp [GB.ev, TEv.IsWrite, Act.IsWrite] at hw)
  have : e ≠ g.ev t (.read x) := fun h => hn (h ▸ he)
  simp [GB.read, GB.push, this]

theorem AInv.loc0 (hA : AInv P n g) {t : Tid} {a : Act} (ha : a.IsLocal) :
    AInv P n (g.loc0 t a) :=
  hA.push (GB.L_push g _) (fun _ _ => rfl) (fun x => ⟨[], by simp [GB.loc0, GB.push]⟩)
    (retG_loc0 t a ha).1 (fun hw => absurd hw (by
      cases a <;> simp_all [GB.ev, TEv.IsWrite, Act.IsWrite, Act.IsLocal]))

theorem write_co (g : GB) (t : Tid) (x : Loc) (v : Val) (y : Loc) :
    ∃ l', (g.write t x v).co y = g.co y ++ l' := by
  by_cases h : y = x
  · subst h; exact ⟨[g.ev t (.write y v)], by simp [GB.write, GB.push]⟩
  · exact ⟨[], by simp [GB.write, GB.push, h]⟩

theorem AInv.write_noex (hA : AInv P n g) {t : Tid} {x : Loc} {v : Val}
    (hex : (lifeSys P n).ex t (tr P g t) = false) : AInv P n (g.write t x v) :=
  hA.push (GB.L_push g _) (fun _ _ => rfl) (write_co g t x v)
    (retG_write t x v).1 (fun _ h => by rw [hex] at h; cases h)

/-- The write of an acquire pair, right after its read. -/
theorem AInv.write_acq (hA : AInv P n g) {t : Tid} {l : Loc} {v : Val} {r : TEv}
    {pre : List TEv} (hthr : thr g t = pre ++ [r]) (hr : g.rf r = some (g.last l)) :
    AInv P n (g.write t l v) := by
  refine hA.push (GB.L_push g _) (fun _ _ => rfl) (write_co g t l v) (retG_write t l v).1
    (fun _ _ => ⟨r, pre, hthr, g.last l, by simpa [GB.write, GB.push] using hr, ?_⟩)
  simp only [GB.ev, Act.loc]
  unfold GB.last
  cases hc : (g.co l).getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff] at hc
    exact ⟨[], by simp [GB.write, GB.push, hc, GB.ev]⟩
  | some p =>
    obtain ⟨l₁, hl₁⟩ := List.getLast?_eq_some_iff.mp hc
    exact ⟨l₁, [], by simp [GB.write, GB.push, hl₁, GB.ev]⟩

theorem lifeFlag_of_bodyAt {t : Tid} {u : List (Option Val)} {st : TState}
    (h : BodyAt P t u st) : lifeFlag P t u = st.isEx := by
  unfold BodyAt at h
  unfold lifeFlag
  split_ifs at h ⊢ with hr
  · rw [h]
  · obtain ⟨v, w, rfl, hv, hw⟩ := h
    simp [hv, hw]

theorem ex_false_of_flag {t : Tid} {u : List (Option Val)} (h : lifeFlag P t u = false) :
    (lifeSys P n).ex t u = false := by
  change exFlag _ (lifeFlag P) t u = false
  unfold exFlag
  split <;> simp [h]

theorem noex_of_running (hI : SInv P n s g) {t : Tid} (ht : t ∈ P.threads)
    (hs : s.status t = .running) (hx : (⟨s.rest t, holdsM s t, .ready⟩ : TState).isEx = false) :
    (lifeSys P n).ex t (tr P g t) = false := by
  obtain ⟨-, hb⟩ := trel_running (hI.rel t ht) hs
  exact ex_false_of_flag (by rw [lifeFlag_of_bodyAt hb, hx])

/-- **`AInv` is preserved by steps.** -/
theorem AInv.step (hI : SInv P n s g) (hA : AInv P n g) {o : Occ} (he : Enabled P s o) :
    AInv P n (emit P g o) := by
  have hg := hI.ok
  have hb : Act.block.IsLocal := by simp [Act.IsLocal]
  cases he
  case acq t l ht hs hc hh hf =>
    change AInv P n ((g.read t l (g.last l)).write t l 1)
    have h1 := hA.read hg t l (g.last l)
    exact h1.write_acq (pre := thr g t) (r := g.ev t (.read l))
      (thr_append (GB.L_push g _) t |>.trans (by simp [GB.ev]))
      (by simp [GB.read, GB.push, GB.ev, GB.last])
  case tryAcq t l k ht hs hc hh hf =>
    change AInv P n ((g.read t l (g.last l)).write t l 1)
    have h1 := hA.read hg t l (g.last l)
    exact h1.write_acq (pre := thr g t) (r := g.ev t (.read l))
      (thr_append (GB.L_push g _) t |>.trans (by simp [GB.ev]))
      (by simp [GB.read, GB.push, GB.ev, GB.last])
  case release t l ht hs hc hh h1 =>
    exact hA.write_noex (noex_of_running hI ht hs (by rw [rest_cons hc]; rfl))
  case wr t x v ht hs hc =>
    exact hA.write_noex (noex_of_running hI ht hs (by rw [rest_cons hc]; rfl))
  case start t u ht hs hc =>
    exact hA.write_noex (noex_of_running hI ht hs (by rw [rest_cons hc]; rfl))
  case fin t ht hs hc =>
    exact hA.write_noex (noex_of_running hI ht hs (by rw [hc]; rfl))
  case asmStop t x v ht hs hc hv =>
    exact (hA.read hg t x (g.last x)).loc0 hb
  case reacq => exact hA.loc0 (by simp [Act.IsLocal])
  case tryRe => exact hA.loc0 (by simp [Act.IsLocal])
  case unlockRe => exact hA.loc0 (by simp [Act.IsLocal])
  case unlockErr => exact hA.loc0 (by simp [Act.IsLocal])
  all_goals exact hA.read hg _ _ _

theorem AInv.steps (hF : Frag P) (hn : adequateB P n = true) {rs : List Occ}
    (hr : Steps P (MState.init P) rs s) : AInv P n (rs.foldl (emit P) GB.empty) := by
  suffices ∀ s0 g0, SInv P n s0 g0 → AInv P n g0 → Steps P s0 rs s →
      AInv P n (rs.foldl (emit P) g0) from this _ _ (sinv_init hF n) ainv_empty hr
  intro s0 g0 hI hA h
  clear hr
  induction h generalizing g0 with
  | nil => exact hA
  | cons h _ ih => exact ih _ (hI.step hF hn h) (hA.step hI h.1)

theorem AInv.synthStep (hA : AInv P n g) (hg : g.Ok) (t : Tid) : AInv P n (synth P s g t) := by
  have hb : Act.block.IsLocal := by simp [Act.IsLocal]
  unfold synth
  split
  · exact (hA.read hg _ _ _).loc0 hb
  · split
    · split_ifs
      · exact (hA.read hg _ _ _).loc0 hb
      · exact hA
    · split_ifs
      · exact (hA.read hg _ _ _).loc0 hb
      · exact hA
    · exact hA
  · exact hA

theorem AInv.final (hA : AInv P n g) (hg : g.Ok)
    (hnew : ∀ t ∈ P.threads, s.status t = .new → g.co (P.st t) = []) :
    AInv P n (finalize P g s) := by
  unfold finalize
  suffices ∀ (l : List Tid) (g : GB), g.Ok → AInv P n g →
      (∀ t ∈ l, s.status t = .new → g.co (P.st t) = []) → AInv P n (l.foldl (synth P s) g) from
    this _ g hg hA hnew
  intro l
  induction l with
  | nil => intro g _ hA _; exact hA
  | cons t l ih =>
    intro g hg hA h
    refine ih _ (synth_ok P s hg t (h t List.mem_cons_self)) (hA.synthStep hg t) ?_
    intro t' ht' hn
    rw [synth_co]
    exact h t' (List.mem_cons_of_mem _ ht') hn

/-- **An `Ok` builder with `AInv` gives an atomic graph.** -/
theorem atomic_of_ainv (hg : g.Ok) (hA : AInv P n g) : (lifeSys P n).Atomic (g.toCfg P).abs := by
  intro r w hrw src hsrc
  obtain ⟨hr, hw, htid, hidx, -, hwW, -, hwx⟩ := hrw
  rw [GB.mem_events] at hr hw
  obtain ⟨hlw, hthw⟩ := hg.thr_of_mem P hw
  obtain ⟨hlr, hthr⟩ := hg.thr_of_mem P hr
  have hsplit : thr g w.tid = (thr g w.tid).take w.idx ++ w :: (thr g w.tid).drop (w.idx + 1) := by
    conv_lhs => rw [← List.take_append_drop w.idx (thr g w.tid)]
    rw [List.drop_eq_getElem_cons hlw, hthw]
  have hex : (lifeSys P n).ex w.tid (((thr g w.tid).take w.idx).map (retG P g)) = true := by
    have : ((thr g w.tid).take w.idx).map (retG P g) = (tr P g w.tid).take w.idx := by
      simp [tr, List.map_take]
    rw [this, ← hg.traceBefore_eq hlw.le]
    exact hwx
  obtain ⟨r', pre', hp, src', hr', hi⟩ := hA w.tid _ w _ hsplit hwW hex
  -- `r'` is the event before `w`, that is `r`
  have hr'eq : r' = r := by
    have hlen : ((thr g w.tid).take w.idx).length = w.idx := by simp; omega
    have h1 : ((thr g w.tid).take w.idx)[w.idx - 1]'(by omega) = r' := by
      simp only [hp]
      rw [List.getElem_append_right (by simp [hp] at hlen; omega)]
      simp [hp] at hlen; simp [show w.idx - 1 - pre'.length = 0 by omega]
    rw [List.getElem_take] at h1
    rw [← h1]
    have : w.idx - 1 = r.idx := by omega
    simp only [this]
    simp only [htid]
    exact hthr
  subst hr'eq
  simp only [GB.toCfg, Config.abs] at hsrc
  rw [hr'] at hsrc
  cases hsrc
  exact hi

/-- **Gate clause 1, atomicity part.** -/
theorem g1Atomic : G1Atomic := by
  intro P n hf hn rs s hr
  have hF := frag_of_fragB hf
  have hm := (minv_init P).steps hF hr.1
  refine atomic_of_ainv (runCfg_ok hF hr) ((AInv.steps hF hn hr.1).final
    (foldl_emit_ok P ok_empty rs) ?_)
  intro t ht hnw
  refine hm.life t ht ?_
  cases h : s.started t
  · rfl
  · exact absurd (Enabled.begin ht hnw h) (hr.2 _)

end Sem

end Life

end Condpor
