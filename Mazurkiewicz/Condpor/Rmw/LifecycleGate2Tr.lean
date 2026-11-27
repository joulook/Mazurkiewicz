import Mazurkiewicz.Condpor.Rmw.LifecycleGate2Run

/-!
# Gate clause 2, part 3b: the builder along a run list (LC2-b, continuation 3)

For an `Ok` builder whose list `g.L` is a prefix of a sub-linearization `l` of `G`:

* `retG_eq`: the values the builder returns are those of `G` (`SubLin.rf_eq`);
* `tr_eq`: the values of thread `t` in the builder are the trace of `t` in `G` before index
  `g.cnt t`;
* `abs_eq_of_subLin`: if `g.L` itself is a sub-linearization of `G` with all events of `G`,
  the builder's graph is `G` (given the memory and `pol = none`);
* `step_not_cons`: `lifeSys` never emits a constraint evaluation, so `pol = none` on its
  executions (`pol_none_of_exec`).
-/

namespace Condpor

namespace Life

namespace Sem

open _root_.List

variable {P : LProg} {G : Graph}

theorem pre_append_of_mem' {A B : List TEv} {e : TEv} (h : e ∈ A) : pre (A ++ B) e = pre A e := by
  unfold pre
  induction A with
  | nil => cases h
  | cons b A ih =>
    by_cases hb : b = e
    · subst hb; simp
    · simp only [cons_append, takeWhile_cons, ne_eq, hb, not_false_eq_true, decide_true]
      rw [ih ((mem_cons.mp h).resolve_left (Ne.symm hb))]

theorem valE_eq (hmem : G.mem = lifeMem P) (x : Loc) : G.valAt x = valE P x := by
  funext w
  cases w with
  | init => simp [Graph.valAt, valE, hmem]
  | th w => rfl

/-- The builder returns the values of `G` on its events. -/
theorem retG_eq {g : GB} {l rest : List TEv} (hg : g.Ok) (hG : G.Wf) (hl : SubLin G l)
    (hpre : l = g.L ++ rest) (hmem : G.mem = lifeMem P) {e : TEv} (he : e ∈ g.L) :
    retG P g e = G.ret e := by
  have hel : e ∈ l := hpre ▸ mem_append_left _ he
  unfold retG Graph.ret
  cases hact : e.act with
  | read x =>
    have hr : isReadB e = true := isReadB_iff.mpr (by simp [TEv.IsRead, hact, Act.IsRead])
    rw [hg.rf e, ite_eq_left_iff.mpr (fun h => absurd ⟨he, hr⟩ h), hl.rf_eq hG hel hact, hpre,
      pre_append_of_mem' he, hact]
    simp [valE_eq hmem]; rfl
  | cons φ => exact absurd (by simp [TEv.IsCons, hact, Act.IsCons]) (hg.noCons e he)
  | write _ _ => rfl
  | gen _ => rfl
  | block => rfl
  | error => rfl

/-- The values of a thread in the builder are its trace in `G`. -/
theorem tr_eq {g : GB} {l rest : List TEv} (hg : g.Ok) (hG : G.Wf) (hl : SubLin G l)
    (hpre : l = g.L ++ rest) (hmem : G.mem = lifeMem P) (t : Tid) :
    tr P g t = G.traceBefore t (g.cnt t) := by
  unfold tr Graph.traceBefore
  apply ext_getElem
  · simp [hg.thr_length]
  · intro j h1 h2
    simp only [length_map] at h1
    simp only [getElem_map, getElem_range]
    obtain ⟨hm, ht⟩ := GB.Ok.thr_mem h1
    have hmG : (thr g t)[j] ∈ G.events := hl.sub _ (hpre ▸ mem_append_left _ hm)
    rw [Graph.evAt_eq_some_of_inj' hG.idx_inj hmG ht (hg.thr_idx h1), Option.bind_some,
      retG_eq hg hG hl hpre hmem hm]

/-- An `Ok` builder whose list is a sub-linearization of `G` with all its events builds `G`. -/
theorem abs_eq_of_subLin {g : GB} (hg : g.Ok) (hG : G.Wf) (hl : SubLin G g.L)
    (hall : ∀ e ∈ G.events, e ∈ g.L) (hmem : G.mem = lifeMem P) (hpol : ∀ e, G.pol e = none) :
    (g.toCfg P).abs = G := by
  ext1
  · exact hmem.symm
  · ext e
    exact (GB.mem_events P).trans ⟨hl.sub e, hall e⟩
  · funext e
    change g.rf e = G.rf e
    rw [hg.rf e]
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      rw [hl.rf_eq hG h1 (isReadB_iff.mp h2).exists_act]
    · symm
      apply hG.rf_none
      by_cases he : e ∈ G.events
      · right; intro hr; exact h ⟨hall e he, isReadB_iff.mpr hr⟩
      · left; exact he
  · funext x
    change g.co x = G.co x
    rw [hg.co x, hl.co_eq hG x]
  · funext e
    change none = G.pol e
    rw [hpol]

/-! ### No constraint evaluations -/

theorem TState.act_not_cons (st : Tid → Loc) (me : Tid) (s : TState) {a : Act}
    (h : s.act st me = some a) : ¬ a.IsCons := by
  rcases s with ⟨ops, holds, ph⟩
  cases ph with
  | acquire l => simp only [TState.act, Option.some.injEq] at h; subst h; simp [Act.IsCons]
  | blocking => simp only [TState.act, Option.some.injEq] at h; subst h; simp [Act.IsCons]
  | done => simp only [TState.act, reduceCtorEq] at h
  | ready =>
    cases ops with
    | nil => simp only [TState.act, Option.some.injEq] at h; subst h; simp [Act.IsCons]
    | cons c rest =>
      cases c <;> simp only [TState.act] at h <;> (try split_ifs at h) <;>
        (cases h; simp [Act.IsCons])

theorem lifeTab_not_cons {t : Tid} {u : List (Option Val)} {a : Act}
    (h : lifeTab P t u = some a) : ¬ a.IsCons := by
  unfold lifeTab at h
  split_ifs at h with hr
  · exact TState.act_not_cons _ _ _ h
  · cases u with
    | nil => cases h; simp [Act.IsCons]
    | cons v rest =>
      simp only at h
      split_ifs at h
      · cases h; simp [Act.IsCons]
      · exact TState.act_not_cons _ _ _ h

theorem step_not_cons {n : ℕ} {t : Tid} {u : List (Option Val)} {a : Act}
    (h : (lifeSys P n).toProgram.step t u = some a) : ¬ a.IsCons := by
  simp only [lifeSys, mkXProg, mkProg] at h
  split_ifs at h
  exact lifeTab_not_cons h

theorem pol_none_of_exec {n : ℕ} {c : Config} (hc : c.Wf) (hE : (lifeSys P n).toProgram.Exec c.abs)
    (e : TEv) : c.abs.pol e = none := by
  cases hp : c.abs.pol e with
  | none => rfl
  | some b =>
    have h := (hc.1.pol_isSome e).mp (by simp [hp])
    exact absurd h.2 (step_not_cons (hE.2 e h.1))

end Sem

end Life

end Condpor
