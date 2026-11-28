import Mazurkiewicz.Condpor.Rmw.LifecycleGate3Next

/-!
# Gate clause 3, part 6: maximal runs with the same graph are equivalent (LC2-c)

Under the simulation invariant `SInv` (fragment program, adequate bound `n`):

* **`key`**: if `a :: x'` and `y` are maximal runs from `s` with the same graph, then
  `y = y₁ ++ a :: y₂` with every occurrence of `y₁` independent of `a`. The first occurrence
  of the thread of `a` in `y` is `a` (`next_same`: the state of the thread is unchanged by
  the other threads, and the value read first is the same in both graphs — its `rf` is
  recorded); and an occurrence of `y₁` dependent on `a` would have an event conflicting with
  an event of `a` in the opposite order in the two graphs (`order_conflict`).
* **`fwd_core`**: by induction on the first run, moving `a` to the front of `y` (`run_move`).
-/

namespace Condpor

namespace Life

namespace Sem

open _root_.List

variable {P : LProg} {n : ℕ}

/-! ### Runs of the other threads -/

theorem started_mono {s : MState} {o : Occ} (he : Enabled P s o) {u : Tid}
    (h : s.started u = true) : (eff s o).started u = true := by
  cases he <;> simp only [eff, MState.adv, MState.setSt, Function.update_apply] <;>
    (try split_ifs) <;> simp_all

theorem steps_other {s s' : MState} {ys : List Occ} {t : Tid} (h : Steps P s ys s')
    (hy : ∀ c ∈ ys, c.tid ≠ t) :
    s'.status t = s.status t ∧ s'.rest t = s.rest t ∧ holdsM s' t = holdsM s t ∧
      (s.started t = true → s'.started t = true) := by
  induction h with
  | nil => exact ⟨rfl, rfl, rfl, id⟩
  | cons h1 _ ih =>
    obtain ⟨he, rfl⟩ := h1
    obtain ⟨a1, a2, a3, a4⟩ := ih (fun c hc => hy c (mem_cons_of_mem _ hc))
    have hne : _ ≠ _ := Ne.symm (hy _ mem_cons_self)
    obtain ⟨b1, b2, b3, -⟩ := eff_other he hne
    exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, fun h => a4 (started_mono he h)⟩

theorem SInv.steps' (hF : Frag P) (hn : adequateB P n = true) {s s' : MState} {g : GB}
    {ys : List Occ} (hI : SInv P n s g) (h : Steps P s ys s') :
    SInv P n s' (ys.foldl (emit P) g) := by
  induction h generalizing g with
  | nil => exact hI
  | cons h _ ih => exact ih (hI.step hF hn h)

theorem final_ok (hF : Frag P) {s s1 : MState} {g : GB} {x : List Occ} (hI : SInv P n s g)
    (h : Steps P s x s1) (hm : Maximal P s1) : (finalize P (x.foldl (emit P) g) s1).Ok := by
  have hmi := hI.minv.steps hF h
  refine finalize_ok P s1 (foldl_emit_ok P hI.ok x) ?_
  intro t ht hnw
  refine hmi.life t ht ?_
  cases h : s1.started t
  · rfl
  · exact absurd (Enabled.begin ht hnw h) (hm _)

theorem geq_parts {g1 g2 : GB} (h : (g1.toCfg P).abs = (g2.toCfg P).abs) :
    (∀ e, e ∈ g1.L ↔ e ∈ g2.L) ∧ g1.rf = g2.rf ∧ g1.co = g2.co := by
  refine ⟨fun e => ?_, congrArg Graph.rf h, congrArg Graph.co h⟩
  rw [← GB.mem_events P, ← GB.mem_events P, h]

theorem split_first (t : Tid) : ∀ y : List Occ, (∀ c ∈ y, c.tid ≠ t) ∨
    ∃ y₁ b y₂, y = y₁ ++ b :: y₂ ∧ (∀ c ∈ y₁, c.tid ≠ t) ∧ b.tid = t := by
  intro y
  induction y with
  | nil => exact Or.inl (by simp)
  | cons c y ih =>
    by_cases hc : c.tid = t
    · exact Or.inr ⟨[], c, y, rfl, by simp, hc⟩
    · rcases ih with h | ⟨y₁, b, y₂, rfl, h1, h2⟩
      · exact Or.inl (fun c' hc' => (mem_cons.mp hc').elim (fun h' => h' ▸ hc) (h c'))
      · refine Or.inr ⟨c :: y₁, b, y₂, rfl, fun c' hc' => ?_, h2⟩
        exact (mem_cons.mp hc').elim (fun h' => h' ▸ hc) (h1 c')

/-- The builder list of a run and its finalization: the events of the first occurrence come
right after the start. -/
theorem final_L_cons (P : LProg) (g : GB) (a : Occ) (x : List Occ) (s : MState) :
    ∃ R, (finalize P ((a :: x).foldl (emit P) g) s).L = g.L ++ (evs P a (g.cnt a.tid) ++ R) := by
  obtain ⟨E, hE, -, -⟩ := foldl_emit_L P x (emit P g a)
  obtain ⟨⟨S, hS⟩, -⟩ := finalize_L_co P s (x.foldl (emit P) (emit P g a))
  refine ⟨E ++ S, ?_⟩
  rw [foldl_cons, hS, hE, (emit_L P g a).1]
  simp only [append_assoc]

theorem evs_not_mem {g : GB} (hg : g.Ok) {o : Occ} {e : TEv} (he : e ∈ evs P o (g.cnt o.tid)) :
    e ∉ g.L := by
  intro h
  have h1 := hg.lt_cnt e h
  obtain ⟨h2, h3⟩ := mem_evs he
  rw [h2] at h1
  omega

theorem fp_prims (P : LProg) (o : Occ) :
    ∀ r ∈ fp o, ∃ p ∈ prims P o, p.acc = some (resLoc P r.1, r.2) := by
  cases o <;> simp [prims, Prim.acc, fp, resLoc]

theorem mem_evsF_of {t : Tid} : ∀ {k : ℕ} {ps : List Prim} {p : Prim}, p ∈ ps →
    ∃ e ∈ evsF t k ps, e.act = p.act := by
  intro k ps
  induction ps generalizing k with
  | nil => intro p h; cases h
  | cons q ps ih =>
    intro p h
    rcases mem_cons.mp h with rfl | h
    · exact ⟨_, mem_cons_self, rfl⟩
    · obtain ⟨e, he, h'⟩ := ih (k := k + 1) h
      exact ⟨e, mem_cons_of_mem _ he, h'⟩

theorem conf_of_acc {p q : Prim} {x : Loc} {b₁ b₂ : Bool} (h1 : p.acc = some (x, b₁))
    (h2 : q.acc = some (x, b₂)) (hb : b₁ = true ∨ b₂ = true) {e f : TEv} (he : e.act = p.act)
    (hf : f.act = q.act) : Conf e f := by
  cases p <;> cases q <;> simp only [Prim.acc, Option.some.injEq, Prod.mk.injEq,
    reduceCtorEq] at h1 h2 <;> simp only [Prim.act] at he hf <;>
    obtain ⟨rfl, rfl⟩ := h1 <;> obtain ⟨h2, rfl⟩ := h2 <;> subst h2 <;>
    simp only [Bool.false_eq_true, or_self] at hb <;>
    first
    | exact ⟨_, Or.inl ⟨⟨_, he⟩, ⟨_, hf⟩⟩⟩
    | exact ⟨_, Or.inr (Or.inl ⟨⟨_, he⟩, hf⟩)⟩
    | exact ⟨_, Or.inr (Or.inr ⟨he, ⟨_, hf⟩⟩)⟩

theorem steps_okOcc (hF : Frag P) {s s' : MState} {ys : List Occ} (hs : Suf P s)
    (h : Steps P s ys s') : ∀ c ∈ ys, OkOcc P c := by
  induction h with
  | nil => intro c hc; cases hc
  | cons h1 _ ih =>
    intro c hc
    rcases mem_cons.mp hc with rfl | hc
    · exact okOcc_of_enabled hF hs h1.1
    · exact ih (hs.step h1) c hc

/-! ### The first occurrence -/

/-- The value read first by the thread of `a` is the same in both runs. -/
theorem value_agree {Fx Fy g g' : GB} (o1 : Fx.Ok) (o2 : Fy.Ok)
    (hmem : ∀ e, e ∈ Fx.L ↔ e ∈ Fy.L) (hrf : Fx.rf = Fy.rf) (hg : g.Ok) (hg' : g'.Ok)
    {a : Occ} {Rx R : List TEv} (hLx : Fx.L = g.L ++ (evs P a (g.cnt a.tid) ++ Rx))
    (hLy : Fy.L = g'.L ++ R) (hcnt : g'.cnt a.tid = g.cnt a.tid)
    (hR : ∀ e ∈ R, e.tid = a.tid → e.idx = g.cnt a.tid → ∀ z, ∀ f ∈ pre R e, writesB z f = false)
    {s : MState} (hnext : next P s a.tid = some a) :
    ∀ z, dloc P s a.tid = some z → g.last z = g'.last z := by
  intro z hz
  obtain ⟨ps, hps⟩ := first_read hnext hz
  set e : TEv := ⟨a.tid, g.cnt a.tid, .read z⟩ with hedef
  have hea : evs P a (g.cnt a.tid) = e :: evsF a.tid (g.cnt a.tid + 1) ps := by
    unfold evs; rw [hps]; rfl
  have hex : e ∉ g.L := evs_not_mem hg (o := a) (by rw [hea]; exact mem_cons_self)
  have hrx : Fx.rf e = some (lastW g.L z) := by
    refine o1.rf_split (A := g.L) (B := evsF a.tid (g.cnt a.tid + 1) ps ++ Rx) ?_ hex rfl
    rw [hLx, hea]; simp
  have hey : e ∈ Fy.L := (hmem e).mp (by rw [hLx, hea]; simp)
  have hey' : e ∉ g'.L := by
    intro h
    have := hg'.lt_cnt e h
    simp [hedef, hcnt] at this
  have heR : e ∈ R := by
    rw [hLy] at hey
    exact (mem_append.mp hey).resolve_left hey'
  have hry : Fy.rf e = some (lastW g'.L z) := by
    have hloc : e.act.loc = z := rfl
    rw [o2.rf_of_mem hey (by simp [isReadB, hedef]), hloc, hLy, pre_append_not_mem hey',
      lastW_append_nowrite (fun f hf => hR e heR rfl rfl z f hf)]
  rw [hrf, hry, Option.some.injEq] at hrx
  rw [hg.last_eqW, hg'.last_eqW]
  cases hrx' : lastW g.L z <;> simp_all

/-- An occurrence of the other threads before `a` in `y` is independent of `a`. -/
theorem indep_prefix {Fx Fy g g' : GB} (o1 : Fx.Ok) (o2 : Fy.Ok)
    (hmem : ∀ e, e ∈ Fx.L ↔ e ∈ Fy.L) (hrf : Fx.rf = Fy.rf) (hco : Fx.co = Fy.co)
    (hg' : g'.Ok) {a : Occ} {Rx R : List TEv} {E1 : List TEv} {y₁ : List Occ}
    (hLx : Fx.L = g.L ++ (evs P a (g.cnt a.tid) ++ Rx))
    (hLy : Fy.L = g'.L ++ (evs P a (g.cnt a.tid) ++ R)) (hcnt : g'.cnt a.tid = g.cnt a.tid)
    (hE1 : g'.L = g.L ++ E1) (hE1c : ∀ c ∈ y₁, ∃ k, ∀ e ∈ evs P c k, e ∈ E1)
    (hy1t : ∀ c ∈ y₁, c.tid ≠ a.tid) : ∀ c ∈ y₁, ¬ Dep a c := by
  intro c hcy hd
  rcases hd with hd | ⟨r₁, hr₁, r₂, hr₂, hr, hw⟩
  · exact hy1t c hcy hd.symm
  obtain ⟨pa, hpa, hpa'⟩ := fp_prims P a r₁ hr₁
  obtain ⟨pc, hpc, hpc'⟩ := fp_prims P c r₂ hr₂
  obtain ⟨k, hk⟩ := hE1c c hcy
  obtain ⟨ea, hea, hea'⟩ := mem_evsF_of (t := a.tid) (k := g.cnt a.tid) hpa
  obtain ⟨ec, hec, hec'⟩ := mem_evsF_of (t := c.tid) (k := k) hpc
  have hecE : ec ∈ E1 := hk ec hec
  rw [hr] at hpa'
  have hconf : Conf ea ec := conf_of_acc hpa' hpc' hw hea' hec'
  have hnd' := hg'.nodup
  rw [hE1] at hnd'
  have hecg : ec ∉ g.L := fun h => (nodup_append.mp hnd').2.2 ec h ec hecE rfl
  have heca : ec ∉ evs P a (g.cnt a.tid) := by
    intro h
    exact hy1t c hcy ((mem_evsF hec).1.symm.trans (mem_evs h).1)
  have hecy : ec ∈ Fy.L := by rw [hLy, hE1]; simp [hecE]
  have hecx : ec ∈ Fx.L := (hmem ec).mpr hecy
  have heax : ea ∈ Fx.L := by rw [hLx]; exact mem_append_right _ (mem_append_left _ hea)
  have h1b : ea ∈ pre Fx.L ec := by
    rw [hLx, ← append_assoc, pre_append_not_mem (by simp [hecg, heca])]
    exact mem_append_left _ (mem_append_right _ hea)
  have hea_g' : ea ∉ g'.L := by
    intro h
    have h1 := hg'.lt_cnt ea h
    have h2 := mem_evsF hea
    rw [h2.1, hcnt] at h1
    omega
  have h2b : ec ∈ pre Fy.L ea := by
    rw [hLy, pre_append_not_mem hea_g', hE1]
    exact mem_append_left _ (mem_append_right _ hecE)
  exact order_conflict o1 o2 hmem hrf hco hconf heax hecx h1b h2b

/-- **Key lemma.** -/
theorem key (hF : Frag P) (hn : adequateB P n = true) {s : MState} {g : GB} (hI : SInv P n s g)
    {a : Occ} {x' : List Occ} {s1 : MState} (hx : Steps P s (a :: x') s1) (hm1 : Maximal P s1)
    {y : List Occ} {s2 : MState} (hy : Steps P s y s2) (hm2 : Maximal P s2)
    (hG : ((finalize P ((a :: x').foldl (emit P) g) s1).toCfg P).abs =
      ((finalize P (y.foldl (emit P) g) s2).toCfg P).abs) :
    ∃ y₁ y₂, y = y₁ ++ a :: y₂ ∧ ∀ b ∈ y₁, ¬ Dep a b := by
  have o1 := final_ok hF hI hx hm1
  have o2 := final_ok hF hI hy hm2
  obtain ⟨hmem, hrf, hco⟩ := geq_parts hG
  have ha : Enabled P s a := by cases hx with | cons h _ => exact h.1
  have ht : a.tid ∈ P.threads := enabled_tid_mem ha
  have hnext : next P s a.tid = some a := next_of_enabled ha
  obtain ⟨Rx, hLx⟩ := final_L_cons P g a x' s1
  rcases split_first a.tid y with hyt | ⟨y₁, b, y₂, rfl, hy1t, hbt⟩
  · -- no occurrence of the thread: it would be enabled at the end
    exfalso
    have hI' : SInv P n s2 (y.foldl (emit P) g) := hI.steps' hF hn hy
    obtain ⟨h1, h2, h3, h4⟩ := steps_other hy hyt
    have hcnt := foldl_emit_cnt_other P y g hyt
    obtain ⟨S, hS, hw⟩ := finalize_nowrite P s2 hI'.ok o2
    have hv := value_agree o1 o2 hmem hrf hI.ok hI'.ok hLx hS hcnt
      (fun e _ _ _ z f hf => hw f (mem_pre hf).1 z) hnext
    have hnx := next_same hF hI hI' ht h1 h2 h3 h4 (fun z hz => by rw [hv z hz]) hnext
    exact hm2 _ (enabled_of_next ht hnx)
  · obtain ⟨s', hy1, hs2⟩ := Steps.append_inv hy
    obtain ⟨s'', hb, hy2⟩ : ∃ s'', Step P s' b s'' ∧ Steps P s'' y₂ s2 := by
      cases hs2 with
      | cons hb hr => exact ⟨_, hb, hr⟩
    set g' := y₁.foldl (emit P) g with hg'def
    have hI' : SInv P n s' g' := hI.steps' hF hn hy1
    obtain ⟨h1, h2, h3, h4⟩ := steps_other hy1 hy1t
    have hcnt : g'.cnt a.tid = g.cnt a.tid := foldl_emit_cnt_other P y₁ g hy1t
    obtain ⟨R2, hR2⟩ := final_L_cons P g' b y₂ s2
    have hLy : (finalize P ((y₁ ++ b :: y₂).foldl (emit P) g) s2).L =
        g'.L ++ (evs P b (g'.cnt b.tid) ++ R2) := by rw [foldl_append]; exact hR2
    obtain ⟨q, qs, -, heb⟩ := evs_head P b (g'.cnt b.tid)
    have hbmem : (⟨b.tid, g'.cnt b.tid, q.act⟩ : TEv) ∈
        (finalize P ((y₁ ++ b :: y₂).foldl (emit P) g) s2).L := by rw [hLy, heb]; simp
    have hR : ∀ e ∈ evs P b (g'.cnt b.tid) ++ R2, e.tid = a.tid → e.idx = g.cnt a.tid →
        ∀ z, ∀ f ∈ pre (evs P b (g'.cnt b.tid) ++ R2) e, writesB z f = false := by
      intro e he het hei z f hf
      have hey : e ∈ (finalize P ((y₁ ++ b :: y₂).foldl (emit P) g) s2).L := by
        rw [hLy]; exact mem_append_right _ he
      have := o2.uniq P hey hbmem (by rw [het, hbt]) (by rw [hei, ← hcnt, hbt])
      rw [heb, this, cons_append, pre_cons_self] at hf
      cases hf
    have hv := value_agree o1 o2 hmem hrf hI.ok hI'.ok hLx hLy hcnt hR hnext
    have hnx := next_same hF hI hI' ht h1 h2 h3 h4 (fun z hz => by rw [hv z hz]) hnext
    have hba : b = a := by
      have := next_of_enabled hb.1
      rw [hbt, hnx] at this
      exact (Option.some.inj this).symm
    subst hba
    refine ⟨y₁, y₂, rfl, ?_⟩
    obtain ⟨E1, hE1, -, hE1c⟩ := foldl_emit_L P y₁ g
    have hLy' : (finalize P ((y₁ ++ b :: y₂).foldl (emit P) g) s2).L =
        g'.L ++ (evs P b (g.cnt b.tid) ++ R2) := by rw [hLy, hcnt]
    exact indep_prefix o1 o2 hmem hrf hco hI'.ok hLx hLy' hcnt hE1 hE1c hy1t

/-- **Maximal runs with the same graph are equivalent** (from a state with the invariant). -/
theorem fwd_core (hF : Frag P) (hn : adequateB P n = true) :
    ∀ (x : List Occ) (s : MState) (g : GB), SInv P n s g → ∀ s1 y s2, Steps P s x s1 →
      Maximal P s1 → Steps P s y s2 → Maximal P s2 →
      ((finalize P (x.foldl (emit P) g) s1).toCfg P).abs =
        ((finalize P (y.foldl (emit P) g) s2).toCfg P).abs → MEquiv x y := by
  intro x
  induction x with
  | nil =>
    intro s g _ s1 y s2 hx hm1 hy _ _
    cases hx
    cases hy with
    | nil => exact MEquiv.refl' _
    | cons hb _ => exact absurd hb.1 (hm1 _)
  | cons a x' ih =>
    intro s g hI s1 y s2 hx hm1 hy hm2 hG
    obtain ⟨y₁, y₂, rfl, hind⟩ := key hF hn hI hx hm1 hy hm2 hG
    obtain ⟨hmv, heq⟩ := run_move hF y₁ s s2 g hI.minv.suffix hind hy
    cases hx with
    | cons ha hr =>
      cases hmv with
      | cons ha' hr' =>
        rw [step_det ha' ha] at hr'
        have hG' : ((finalize P (x'.foldl (emit P) (emit P g a)) s1).toCfg P).abs =
            ((finalize P ((y₁ ++ y₂).foldl (emit P) (emit P g a)) s2).toCfg P).abs :=
          hG.trans ((heq.finalize P s2).abs P)
        have := ih _ _ (hI.step hF hn ha) s1 (y₁ ++ y₂) s2 hr hm1 hr' hm2 hG'
        exact (this.cons a).trans' (mequiv_move hind y₂).symm'

end Sem

end Life

end Condpor
