import Mazurkiewicz.Condpor.Rmw.LifecycleGate3Comm

/-!
# Gate clause 3, part 3: equivalent maximal runs have the same graph (LC2-c)

* `prims_comm`: lists of primitives of different threads, pairwise without conflict, commute.
* `OkRes`, `resLoc`, `resLoc_inj`, `OkOcc`, `okOcc_of_enabled`: the roles of the resources of
  an enabled occurrence (fragment program, remaining calls suffixes of the code); on them the
  location map is injective.
* `emit_comm`: two independent occurrences with role-respecting resources commute on the
  builder up to `GB.Eqv`.
* `run_move`, `bwd_core`, **`gate3_bwd`** (direction ⇐ of `Gate3`).
-/

namespace Condpor

namespace Life

namespace Sem

variable {P : LProg}

/-! ### Lists of primitives -/

theorem prim_comm_list (g : GB) {p : Prim} {qs : List Prim}
    (h : ∀ q ∈ qs, p.tid ≠ q.tid ∧ NoConf p q) :
    (qs.foldl GB.ap (g.ap p)).Eqv ((qs.foldl GB.ap g).ap p) := by
  induction qs generalizing g with
  | nil => exact GB.Eqv.refl _
  | cons q qs ih =>
    simp only [List.foldl_cons]
    have h1 := h q List.mem_cons_self
    refine ((prim_comm g h1.1 h1.2).foldl_ap qs).trans ?_
    exact ih (g.ap q) (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))

theorem prims_comm (g : GB) {ps qs : List Prim}
    (h : ∀ p ∈ ps, ∀ q ∈ qs, p.tid ≠ q.tid ∧ NoConf p q) :
    (qs.foldl GB.ap (ps.foldl GB.ap g)).Eqv (ps.foldl GB.ap (qs.foldl GB.ap g)) := by
  induction ps generalizing g with
  | nil => exact GB.Eqv.refl _
  | cons p ps ih =>
    simp only [List.foldl_cons]
    refine (ih (g.ap p) (fun p' hp' => h p' (List.mem_cons_of_mem _ hp'))).trans ?_
    exact (prim_comm_list g (h p List.mem_cons_self)).foldl_ap ps

/-! ### Roles of resources -/

/-- The role of a resource: a lock location; a data location (neither a lock nor a lifecycle
location); the lifecycle location of a thread of the program. -/
def OkRes (P : LProg) : Res → Prop
  | .lock l => P.isLock l = true
  | .data x => P.isLock x = false ∧ P.isSt x = false
  | .life t => t ∈ P.threads

/-- The location of a resource. -/
def resLoc (P : LProg) : Res → Loc
  | .lock l => l
  | .data x => x
  | .life t => P.st t

theorem resLoc_inj (hF : Frag P) {r₁ r₂ : Res} (h₁ : OkRes P r₁) (h₂ : OkRes P r₂)
    (h : resLoc P r₁ = resLoc P r₂) : r₁ = r₂ := by
  cases r₁ <;> cases r₂ <;> simp only [OkRes, resLoc] at h₁ h₂ h
  · rw [h]
  · rw [h] at h₁; rw [h₁] at h₂; cases h₂.1
  · rw [h] at h₁; rw [hF.st_not_lock _ h₂] at h₁; cases h₁
  · rw [h] at h₁; rw [h₂] at h₁; cases h₁.1
  · rw [h]
  · rw [h, hF.isSt_st h₂] at h₁; cases h₁.2
  · rw [← h] at h₂; rw [hF.st_not_lock _ h₁] at h₂; cases h₂
  · rw [← h, hF.isSt_st h₁] at h₂; cases h₂.2
  · rw [hF.st_inj _ h₁ _ h₂ h]

/-- Every resource of the occurrence has its role. -/
def OkOcc (P : LProg) (o : Occ) : Prop := ∀ r ∈ fp o, OkRes P r.1

/-- The remaining calls are suffixes of the code. -/
def Suf (P : LProg) (s : MState) : Prop := ∀ t, s.rest t <:+ P.code t

theorem Suf.init (P : LProg) : Suf P (MState.init P) := fun _ => List.suffix_refl _

theorem Suf.step {s s1 : MState} {o : Occ} (hs : Suf P s) (h : Step P s o s1) : Suf P s1 := by
  obtain ⟨he, rfl⟩ := h
  exact fun t => (rest_suffix he t).trans (hs t)

theorem Suf.steps {s s1 : MState} {rs : List Occ} (hs : Suf P s) (h : Steps P s rs s1) :
    Suf P s1 := by
  induction h with
  | nil => exact hs
  | cons h _ ih => exact ih (hs.step h)

/-- Unfold the membership in a footprint. -/
macro "fp_simp " h:ident : tactic =>
  `(tactic| simp only [fp, List.mem_cons, List.not_mem_nil, or_false] at $h:ident)

theorem okOcc_of_enabled (hF : Frag P) {s : MState} (hs : Suf P s) {o : Occ}
    (he : Enabled P s o) : OkOcc P o := by
  have hok : ∀ {t c}, t ∈ P.threads → (s.rest t).head? = some c → callOk P t c = true :=
    fun ht hc => hF.calls _ ht _ ((hs _).subset (List.mem_of_mem_head? hc))
  intro r hr
  cases he with
  | begin ht => simp only [fp, List.mem_singleton] at hr; subst hr; exact ht
  | acq ht _ hc => have := hok ht hc; fp_simp hr; rcases hr with rfl | rfl <;> exact this
  | reacq => simp [fp] at hr
  | tryAcq ht _ hc =>
    have := hok ht hc; fp_simp hr; rcases hr with rfl | rfl <;> exact this
  | tryFail ht _ hc => have := hok ht hc; fp_simp hr; subst hr; exact this
  | tryRe => simp [fp] at hr
  | unlockRe => simp [fp] at hr
  | release ht _ hc => have := hok ht hc; fp_simp hr; subst hr; exact this
  | unlockErr => simp [fp] at hr
  | query _ _ _ hl => fp_simp hr; subst hr; exact hl
  | rd ht _ hc hl =>
    have := hok ht hc; fp_simp hr; subst hr
    simp only [callOk, Bool.not_eq_true'] at this
    exact ⟨hl, this⟩
  | wr ht _ hc =>
    have := hok ht hc; fp_simp hr; subst hr
    simp only [callOk, LProg.isData, Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this
  | asmOk ht _ hc =>
    have := hok ht hc; fp_simp hr; subst hr
    simp only [callOk, LProg.isData, Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this
  | asmStop ht _ hc =>
    have := hok ht hc; fp_simp hr; subst hr
    simp only [callOk, LProg.isData, Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this
  | start ht _ hc =>
    have := hok ht hc; fp_simp hr; subst hr
    simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1
  | join ht _ hc =>
    have := hok ht hc; fp_simp hr; subst hr
    simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1
  | fin ht => simp only [fp, List.mem_singleton] at hr; subst hr; exact ht

/-- Every access of a primitive of `o` is an entry of the footprint, mapped to its location. -/
theorem prims_acc (P : LProg) (o : Occ) :
    ∀ p ∈ prims P o, ∀ x b, p.acc = some (x, b) → ∃ r ∈ fp o, resLoc P r.1 = x ∧ r.2 = b := by
  cases o <;> simp [prims, Prim.acc, fp, resLoc]

/-- **Independent occurrences commute on the builder.** -/
theorem emit_comm (hF : Frag P) (g : GB) {a b : Occ} (ha : OkOcc P a) (hb : OkOcc P b)
    (hd : ¬ Dep a b) : (emit P (emit P g a) b).Eqv (emit P (emit P g b) a) := by
  rw [emit_eq_prims P (emit P g a), emit_eq_prims P g a, emit_eq_prims P (emit P g b),
    emit_eq_prims P g b]
  refine prims_comm g ?_
  intro p hp q hq
  refine ⟨?_, ?_⟩
  · rw [prims_tid P a p hp, prims_tid P b q hq]
    exact fun h => hd (Or.inl h)
  · intro x b₁ b₂ h1 h2
    obtain ⟨r₁, hr₁, hx₁, hb₁⟩ := prims_acc P a p hp x b₁ h1
    obtain ⟨r₂, hr₂, hx₂, hb₂⟩ := prims_acc P b q hq x b₂ h2
    have hr := resLoc_inj hF (ha r₁ hr₁) (hb r₂ hr₂) (hx₁.trans hx₂.symm)
    by_contra hc
    apply hd
    refine Or.inr ⟨r₁, hr₁, r₂, hr₂, hr, ?_⟩
    subst hb₁ hb₂
    cases h₁ : r₁.2 <;> cases h₂ : r₂.2 <;> simp_all

/-! ### Moving an occurrence forward in a run -/

theorem Steps.append_inv {s s2 : MState} {x y : List Occ} (h : Steps P s (x ++ y) s2) :
    ∃ s1, Steps P s x s1 ∧ Steps P s1 y s2 := by
  induction x generalizing s with
  | nil => exact ⟨s, Steps.nil s, h⟩
  | cons o x ih =>
    cases h with
    | cons h1 hr =>
      obtain ⟨s1, h2, h3⟩ := ih hr
      exact ⟨s1, Steps.cons h1 h2, h3⟩

theorem Steps.det {s s1 s2 : MState} {x : List Occ} (h1 : Steps P s x s1) (h2 : Steps P s x s2) :
    s1 = s2 := by
  induction h1 with
  | nil => cases h2; rfl
  | cons h hr ih =>
    cases h2 with
    | cons h' hr' => rw [step_det h' h] at hr'; exact ih hr'

/-- **Moving an occurrence forward**: if `a` is independent of every occurrence of `y₁`, the run
`y₁ ++ a :: y₂` can be reordered into the run `a :: (y₁ ++ y₂)`, to the same state, with an
equivalent builder. -/
theorem run_move (hF : Frag P) {a : Occ} {y₂ : List Occ} :
    ∀ (y₁ : List Occ) (s s2 : MState) (g : GB), Suf P s → (∀ b ∈ y₁, ¬ Dep a b) →
      Steps P s (y₁ ++ a :: y₂) s2 →
      Steps P s (a :: (y₁ ++ y₂)) s2 ∧
        ((y₁ ++ a :: y₂).foldl (emit P) g).Eqv ((a :: (y₁ ++ y₂)).foldl (emit P) g) := by
  intro y₁
  induction y₁ with
  | nil => intro s s2 g _ _ h; exact ⟨h, GB.Eqv.refl _⟩
  | cons b y₁ ih =>
    intro s s2 g hs hind h
    cases h with
    | cons hb hr =>
      rename_i s'
      obtain ⟨h1, h2⟩ := ih s' s2 (emit P g b) (hs.step hb)
        (fun c hc => hind c (List.mem_cons_of_mem _ hc)) hr
      cases h1 with
      | cons ha hr2 =>
        have hab : ¬ Dep b a := fun hd => hind b List.mem_cons_self hd.symm
        obtain ⟨s1', hs1, hs2⟩ := commute hb ha hab
        refine ⟨Steps.cons hs1 (Steps.cons hs2 hr2), ?_⟩
        refine h2.trans ?_
        simp only [List.foldl_cons, List.cons_append]
        exact (emit_comm hF g (okOcc_of_enabled hF hs hb.1)
          (okOcc_of_enabled hF (hs.step hb) ha.1) hab).foldl_emit P _

/-- **Equivalent runs** from a state reach the same state with equivalent builders. -/
theorem bwd_core (hF : Frag P) :
    ∀ (x y : List Occ) (s s1 s2 : MState) (g : GB), Suf P s → MEquiv x y →
      Steps P s x s1 → Steps P s y s2 →
      s1 = s2 ∧ (x.foldl (emit P) g).Eqv (y.foldl (emit P) g) := by
  intro x
  induction x with
  | nil =>
    intro y s s1 s2 g _ he h1 h2
    have hy := he.eq_nil
    subst hy
    cases h1; cases h2
    exact ⟨rfl, GB.Eqv.refl _⟩
  | cons a x ih =>
    intro y s s1 s2 g hs he h1 h2
    obtain ⟨y₁, y₂, rfl, hind, hx⟩ := mequiv_cons_split he
    obtain ⟨h3, h4⟩ := run_move hF y₁ s s2 g hs hind h2
    cases h1 with
    | cons ha hr =>
      cases h3 with
      | cons ha' hr' =>
        rw [step_det ha' ha] at hr'
        obtain ⟨e1, e2⟩ := ih _ _ s1 s2 (emit P g a) (hs.step ha) hx hr hr'
        exact ⟨e1, e2.trans h4.symm⟩

/-- **Gate clause 3, direction ⇐**: two `MEquiv` maximal runs have the same graph. -/
theorem gate3_bwd {P : LProg} (hf : fragB P = true) {rs₁ rs₂ : List Occ} {s₁ s₂ : MState}
    (h₁ : MaxRun P rs₁ s₁) (h₂ : MaxRun P rs₂ s₂) (he : MEquiv rs₁ rs₂) :
    (runCfg P rs₁ s₁).abs = (runCfg P rs₂ s₂).abs := by
  obtain ⟨hs, hg⟩ := bwd_core (frag_of_fragB hf) rs₁ rs₂ _ s₁ s₂ GB.empty (Suf.init P) he h₁.1 h₂.1
  subst hs
  exact (hg.finalize P s₁).abs P

end Sem

end Life

end Condpor
