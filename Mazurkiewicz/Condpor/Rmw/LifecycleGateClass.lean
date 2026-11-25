import Mazurkiewicz.Condpor.Rmw.LifecycleGateCls
import Mazurkiewicz.Condpor.Rmw.LifecycleClass

/-!
# Gate clause 1: the class (LC2-b, continuation)

`waitOf_final`: the wait of each thread in the graph of a maximal run, by machine status
(new: a final start wait; running: a final lock or join wait; assume-stopped: an assumption
block; terminated, erred: none). `g1Class : G1Class`, and `gate1 : Gate1`.
-/

namespace Condpor

namespace Life

namespace Sem

open Targets

variable {P : LProg} {n : ℕ} {s : MState}

/-- What the wait of a thread is, by machine status. -/
def WaitSpec (s : MState) (t : Tid) (w : Option (Kind × Bool)) : Prop :=
  match s.status t with
  | .new => w = some (.startW, true)
  | .running => w = some (.lockW, true) ∨ w = some (.joinW, true)
  | .stopped => ∃ f, w = some (.asm, f)
  | _ => w = none

theorem kind_read {g : GB} {t : Tid} {r : TEv} {x : Loc} (hr : r.act = .read x) :
    kindOf P (g.toCfg P) t r =
      if P.isLock x && decide ((g.rf r).map (valE P x) ≠ some 0) then .lockW
      else if decide (x = P.st t) && decide ((g.rf r).map (valE P x) = some 0) then .startW
      else if P.threads.any (fun u => decide (u ≠ t ∧ P.st u = x)) &&
          decide ((g.rf r).map (valE P x) = some 1) then .joinW
      else if P.isData x then .asm
      else .odd := by
  unfold kindOf
  rw [hr]
  simp only [ret_eq, retG, hr]

theorem finalB_eq {g : GB} {r : TEv} :
    finalB (g.toCfg P) r = decide (g.rf r = some (g.last r.act.loc)) :=
  rfl

theorem waitOf_final (hF : Frag P) (hn : adequateB P n = true) {rs : List Occ}
    (hr : MaxRun P rs s) {t : Tid} (ht : t ∈ P.threads) :
    WaitSpec s t (waitOf P (runCfg P rs s) t) := by
  set g := rs.foldl (emit P) GB.empty with hgdef
  have hI : SInv P n s g := SInv.steps hF hn hr.1
  have hL : LInv P s g := LInv.steps (n := n) hF hn hr.1
  have hgf : (finalize P g s).Ok := runCfg_ok hF hr
  obtain ⟨g1, hs1, hs2⟩ := thr_finalize P s g ht
  have hrel := hI.rel t ht
  have hlast := hL.last t
  change WaitSpec s t (waitOf P ((finalize P g s).toCfg P) t)
  have hthr : thr (finalize P g s) t = thr (synth P s g1 t) t := hs2.1
  have hrf : ∀ e, e.tid = t → (finalize P g s).rf e = (synth P s g1 t).rf e := hs2.2.1
  have hco : (finalize P g s).co = g.co := hs2.2.2.2.trans ((synth_co P s g1 t).trans hs1.2.2.2)
  have hlastf : ∀ x, (finalize P g s).last x = g.last x := fun x => by simp [GB.last, hco]
  have hlast1 : ∀ x, g1.last x = g.last x := fun x => by simp [GB.last, hs1.2.2.2]
  have hnext : next P s t = none := by
    cases h : next P s t with
    | none => rfl
    | some o => exact absurd (enabled_of_next ht h) (hr.2 o)
  unfold TRel at hrel
  unfold LRel at hlast
  unfold WaitSpec
  cases hs : s.status t <;> simp only [hs] at hrel hlast ⊢
  · -- new
    obtain ⟨hu, -, -⟩ := hrel
    have hthr0 : thr g t = [] := by simpa [tr] using hu
    have hr0 : P.isRoot t = false := by
      cases h' : P.isRoot t
      · rfl
      · exact absurd hs (hI.newRoot t h')
    have hco0 : g.co (P.st t) = [] := by
      refine hI.minv.life t ht ?_
      cases h : s.started t
      · rfl
      · exact absurd (Enabled.begin ht hs h) (hr.2 _)
    have hsyn : synth P s g1 t = (g1.read t (P.st t) .init).loc0 t .block := by simp [synth, hs]
    have hfin : thr (finalize P g s) t =
        [] ++ [g1.ev t (.read (P.st t)), (g1.read t (P.st t) .init).ev t .block] := by
      rw [hthr, hsyn, thr_loc0, thr_read, hs1.1, hthr0]; simp
    rw [waitOf_block hgf hfin rfl]
    have hrr : (finalize P g s).rf (g1.ev t (.read (P.st t))) = some .init := by
      rw [hrf _ rfl, hsyn]; simp [GB.loc0, GB.push, GB.read]
    rw [kind_read (x := P.st t) rfl, finalB_eq, hrr]
    simp [valE, hF.mem_st ht, hr0, hF.st_not_lock t ht, GB.last, hco, hco0, GB.ev, Act.loc]
  · -- running
    obtain ⟨-, -⟩ := hrel
    rcases next_none_running hs hnext with ⟨l, hc, hh, hf⟩ | ⟨u, hc, hj⟩
    · left
      have hsyn : synth P s g1 t = (g1.read t l (g1.last l)).loc0 t .block := by
        unfold synth; rw [hs]; dsimp only; rw [rest_cons hc]; simp [hh, hf, GB.readLast]
      have hfin : thr (finalize P g s) t =
          thr g t ++ [g1.ev t (.read l), (g1.read t l (g1.last l)).ev t .block] := by
        rw [hthr, hsyn, thr_loc0, thr_read, hs1.1]; simp
      rw [waitOf_block hgf hfin rfl]
      have hrr : (finalize P g s).rf (g1.ev t (.read l)) = some (g.last l) := by
        rw [hrf _ rfl, hsyn, ← hlast1]; simp [GB.loc0, GB.push, GB.read]
      have hl : P.isLock l = true := by simpa [callOk] using callOk_head hF hI ht hc
      have hv : valE P l (g.last l) = 1 := by
        rw [hI.vLock l hl, ite_eq_right_of_eq_false _ _ (eq_false hf)]
      rw [kind_read (x := l) rfl, finalB_eq, hrr]
      simp [hl, hv, hlastf, GB.ev, Act.loc]
    · right
      have hsyn : synth P s g1 t = (g1.read t (P.st u) (g1.last (P.st u))).loc0 t .block := by
        unfold synth; rw [hs]; dsimp only; rw [rest_cons hc]; simp [hj, GB.readLast]
      have hfin : thr (finalize P g s) t = thr g t ++
          [g1.ev t (.read (P.st u)), (g1.read t (P.st u) (g1.last (P.st u))).ev t .block] := by
        rw [hthr, hsyn, thr_loc0, thr_read, hs1.1]; simp
      rw [waitOf_block hgf hfin rfl]
      have hrr : (finalize P g s).rf (g1.ev t (.read (P.st u))) = some (g.last (P.st u)) := by
        rw [hrf _ rfl, hsyn, ← hlast1]; simp [GB.loc0, GB.push, GB.read]
      have hok := callOk_head hF hI ht hc
      simp only [callOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hok
      obtain ⟨⟨hu, -⟩, hut⟩ := hok
      have hv : valE P (P.st u) (g.last (P.st u)) = 1 := by
        rw [hI.vLife u hu]
        simp only [MState.joinOkB, Bool.or_eq_false_iff, Bool.and_eq_false_imp,
          decide_eq_true_eq, decide_eq_false_iff_not] at hj
        have hsu : s.started u = true := by
          cases h' : s.started u
          · have : s.status u ≠ .new := fun h'' => by simp_all
            rw [hI.minv.started_of u this] at h'; cases h'
          · rfl
        simp [hsu, hj.2]
      have hany : P.threads.any (fun u' => decide (u' ≠ t ∧ P.st u' = P.st u)) = true :=
        List.any_eq_true.mpr ⟨u, hu, by simp [hut]⟩
      rw [kind_read (x := P.st u) rfl, finalB_eq, hrr, hany]
      simp [hv, hF.st_not_lock u hu, hlastf, GB.ev, Act.loc]
  · -- terminated
    obtain ⟨pre, e, he, hne⟩ := hlast
    have hsyn : synth P s g1 t = g1 := by simp [synth, hs]
    exact waitOf_none hgf (by rw [hthr, hsyn, hs1.1, he]) hne
  · -- erred
    obtain ⟨pre, e, he, hne⟩ := hlast
    have hsyn : synth P s g1 t = g1 := by simp [synth, hs]
    exact waitOf_none hgf (by rw [hthr, hsyn, hs1.1, he]) (by rw [hne]; simp)
  · -- assume-stopped
    obtain ⟨pre, r, b, x, he, hra, hx, hb⟩ := hlast
    have hsyn : synth P s g1 t = g1 := by simp [synth, hs]
    rw [waitOf_block hgf (by rw [hthr, hsyn, hs1.1, he]) hb]
    refine ⟨finalB ((finalize P g s).toCfg P) r, ?_⟩
    rw [kind_read hra]
    have hxl : P.isLock x = false := by
      simp only [LProg.isData, Bool.and_eq_true, Bool.not_eq_true'] at hx; exact hx.1
    have hxs : P.isSt x = false := by
      simp only [LProg.isData, Bool.and_eq_true, Bool.not_eq_true'] at hx; exact hx.2
    have h1 : x ≠ P.st t := fun h => by rw [h, hF.isSt_st ht] at hxs; cases hxs
    have h2 : P.threads.any (fun u => decide (u ≠ t ∧ P.st u = x)) = false := by
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨u, hu, hu'⟩ := List.any_eq_true.mp h
      simp only [decide_eq_true_eq] at hu'
      rw [← hu'.2, hF.isSt_st hu] at hxs; cases hxs
    rw [h2]
    simp [hxl, h1, hx]

theorem any_filterMap {α β : Type} (l : List α) (g : α → Option β) (f : β → Bool) :
    (l.filterMap g).any f = l.any (fun a => (g a).any f) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons, List.any_cons]
    cases g a <;> simp [ih]

theorem L_read_loc0 (g : GB) (t : Tid) (x : Loc) (src : Ev) :
    ((g.read t x src).loc0 t .block).L =
      g.L ++ [g.ev t (.read x), (g.read t x src).ev t .block] := by
  simp [GB.L, GB.loc0, GB.read, GB.push]

theorem synth_L (P : LProg) (s : MState) (g : GB) (t : Tid) :
    ∃ l, (synth P s g t).L = g.L ++ l ∧ ∀ e ∈ l, e.act ≠ .error := by
  unfold synth
  split
  · exact ⟨_, L_read_loc0 _ _ _ _, by simp [GB.ev]⟩
  · split
    · split_ifs
      · exact ⟨_, L_read_loc0 _ _ _ _, by simp [GB.ev]⟩
      · exact ⟨[], by simp, by simp⟩
    · split_ifs
      · exact ⟨_, L_read_loc0 _ _ _ _, by simp [GB.ev]⟩
      · exact ⟨[], by simp, by simp⟩
    · exact ⟨[], by simp, by simp⟩
  · exact ⟨[], by simp, by simp⟩

theorem finalize_L (P : LProg) (s : MState) (g : GB) :
    ∃ l, (finalize P g s).L = g.L ++ l ∧ ∀ e ∈ l, e.act ≠ .error := by
  unfold finalize
  suffices ∀ (ts : List Tid) (g : GB), ∃ l, (ts.foldl (synth P s) g).L = g.L ++ l ∧
      ∀ e ∈ l, e.act ≠ .error from this _ g
  intro ts
  induction ts with
  | nil => intro g; exact ⟨[], by simp, by simp⟩
  | cons t ts ih =>
    intro g
    obtain ⟨l1, h1, h1'⟩ := synth_L P s g t
    obtain ⟨l2, h2, h2'⟩ := ih (synth P s g t)
    refine ⟨l1 ++ l2, by simp [List.foldl_cons, h2, h1], fun e he => ?_⟩
    rcases List.mem_append.mp he with he | he
    · exact h1' e he
    · exact h2' e he

/-- **Gate clause 1, the class part.** -/
theorem g1Class : G1Class := by
  intro P n hf hn rs s hr
  have hF := frag_of_fragB hf
  set g := rs.foldl (emit P) GB.empty with hgdef
  have hI : SInv P n s g := SInv.steps hF hn hr.1
  have hL : LInv P s g := LInv.steps (n := n) hF hn hr.1
  have hw := (runCfg_wf_sc hF hr).1
  have hfull := g1Full P n hf hn rs s hr
  have hnc := lifeClass_ne_cut_of_full hn hw hfull
  have hws := fun t (ht : t ∈ P.threads) => waitOf_final (n := n) hF hn hr ht
  have hnext : ∀ t ∈ P.threads, next P s t = none := fun t ht => by
    cases h : next P s t with
    | none => rfl
    | some o => exact absurd (enabled_of_next ht h) (hr.2 o)
  -- per-thread values
  have key : ∀ (f : Kind × Bool → Bool) (q : Tid → Bool),
      (∀ t ∈ P.threads, (waitOf P (runCfg P rs s) t).any f = q t) →
      ((P.threads.filterMap (waitOf P (runCfg P rs s))).any f) = P.threads.any q := by
    intro f q h
    rw [any_filterMap]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    exact ⟨fun ⟨t, ht, h'⟩ => ⟨t, ht, (h t ht) ▸ h'⟩,
      fun ⟨t, ht, h'⟩ => ⟨t, ht, (h t ht).symm ▸ h'⟩⟩
  have hodd := key (fun w => decide (w.1 = .odd)) (fun _ => false) (fun t ht => by
    have := hws t ht; unfold WaitSpec at this
    split at this <;> (try rcases this with h | h) <;>
      simp_all)
  have hexp := key (fun w => decide (w.1 ≠ .asm) && !w.2) (fun _ => false) (fun t ht => by
    have := hws t ht; unfold WaitSpec at this
    split at this <;> (try rcases this with h | h) <;>
      simp_all)
  have hblk := key (fun w => decide (w.1 = .asm)) (fun t => decide (s.status t = .stopped))
    (fun t ht => by
      have := hws t ht; unfold WaitSpec at this
      split at this <;> (try rcases this with h | h) <;>
        simp_all)
  have hdl := key (fun w => decide (w.1 = .lockW ∨ w.1 = .joinW)) (atDisabled s) (fun t ht => by
    have := hws t ht
    unfold WaitSpec at this
    unfold atDisabled
    cases hs : s.status t <;> simp only [hs] at this
    case running =>
      rcases next_none_running hs (hnext t ht) with ⟨l, hc, hh, hf'⟩ | ⟨u, hc, hj⟩
      · rw [rest_cons hc]; rcases this with h | h <;> simp [h, hh, hf']
      · rw [rest_cons hc]; rcases this with h | h <;> simp [h, hj]
    case stopped => obtain ⟨f, h⟩ := this; simp [h]
    all_goals simp [this])
  have herr : (runCfg P rs s).order.any (fun e => decide (e.act = .error)) =
      P.threads.any (fun t => decide (s.status t = .erred)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, decide_eq_true_eq]
    obtain ⟨l, hl, hl'⟩ := finalize_L P s g
    constructor
    · rintro ⟨e, he, hea⟩
      have he' : e ∈ (finalize P g s).L := by simp only [GB.L, List.mem_reverse]; exact he
      rw [hl] at he'
      rcases List.mem_append.mp he' with he' | he'
      · have hst := hL.err e he' hea
        obtain ⟨hlen, -⟩ := hI.ok.thr_of_mem P he'
        have hex := hI.exec e.tid e.idx hlen
        have hmem : e.tid ∈ P.threads := by
          by_contra hn'
          simp [lifeSys, mkXProg, mkProg, hn'] at hex
        exact ⟨e.tid, hmem, hst⟩
      · exact absurd hea (hl' e he')
    · rintro ⟨t, ht, hst⟩
      have := hL.last t
      unfold LRel at this
      rw [hst] at this
      obtain ⟨pre, e, he, hea⟩ := this
      refine ⟨e, ?_, hea⟩
      have hm' : e ∈ thr g t := by rw [he]; simp
      have hm : e ∈ g.L := (List.mem_filter.mp hm').1
      have : e ∈ (finalize P g s).L := by rw [hl]; exact List.mem_append_left _ hm
      simp only [GB.L, List.mem_reverse] at this
      exact this
  have hcut : P.threads.any (cutB P (runCfg P rs s)) = false := by
    by_contra hc
    have hc' : P.threads.any (cutB P (runCfg P rs s)) = true := by simpa using hc
    apply hnc
    unfold lifeClass
    simp only [hc', ↓reduceIte]
  have hf0 : (P.threads.any fun _ => false) = false := by simp
  unfold lifeClass mclass
  simp only [hcut, hodd, hexp, herr, hblk, hdl, hf0, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> rfl

/-- **Gate clause 1.** -/
theorem gate1 : Gate1 := gate1_of_parts g1Exec g1Full g1Atomic g1Class

end Sem

end Life

end Condpor
