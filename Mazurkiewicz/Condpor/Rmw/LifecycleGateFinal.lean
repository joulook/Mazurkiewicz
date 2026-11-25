import Mazurkiewicz.Condpor.Rmw.LifecycleGatePres

/-!
# Gate clause 1: `Exec` and `Full` (LC2-b, part 9)

* `SInv.steps`: `SInv` along a run from the initial state.
* `next_none_running`: at a maximal state a running thread is at a disabled `lock` or `join`.
* `synth_spec`: the synthetic events of a thread at a maximal state carry the compiled steps,
  and afterwards the thread has no compiled step left.
* `g1Sim`: `G1Sim` is proved, hence `G1Exec` and `G1Full` (`g1Exec`, `g1Full`).
-/

namespace Condpor

namespace Life

namespace Sem

variable {P : LProg} {n : ℕ} {s : MState} {g : GB}

theorem SInv.steps (hF : Frag P) (hn : adequateB P n = true) {rs : List Occ}
    (hr : Steps P (MState.init P) rs s) : SInv P n s (rs.foldl (emit P) GB.empty) := by
  suffices ∀ s0 g0, SInv P n s0 g0 → Steps P s0 rs s → SInv P n s (rs.foldl (emit P) g0) from
    this _ _ (sinv_init hF n) hr
  intro s0 g0 hI h
  clear hr
  induction h generalizing g0 with
  | nil => exact hI
  | cons h _ ih => exact ih _ (hI.step hF hn h)

theorem step_none_of_stopped {t : Tid} {u : List (Option Val)}
    (h : stopped (lifeTab P) t u = true) : (lifeSys P n).toProgram.step t u = none := by
  simp [lifeSys, mkXProg, mkProg, h]

theorem step_none_of_tab {t : Tid} {u : List (Option Val)} (h : lifeTab P t u = none) :
    (lifeSys P n).toProgram.step t u = none := by
  simp only [lifeSys, mkXProg, mkProg]
  split_ifs <;> simp_all

/-- At a maximal state a running thread is at a disabled `lock` or a disabled `join`. -/
theorem next_none_running {t : Tid} (hs : s.status t = .running) (h : next P s t = none) :
    (∃ l, (s.rest t).head? = some (.lock l) ∧ s.heldB t l = false ∧ s.count l ≠ 0) ∨
      ∃ u, (s.rest t).head? = some (.join u) ∧ s.joinOkB u = false := by
  unfold next at h
  rw [hs] at h
  simp only at h
  split at h
  · cases h
  · next l hl => split_ifs at h with h1 h2; exact Or.inl ⟨l, hl, by simpa using h1, h2⟩
  · split_ifs at h
  · split_ifs at h
  · split_ifs at h
  · cases h
  · split_ifs at h
  · cases h
  · next u hu => split_ifs at h with h1; exact Or.inr ⟨u, hu, by simpa using h1⟩

/-- The synthetic events of one thread at a maximal state. -/
theorem synth_spec (hF : Frag P) (hn : adequateB P n = true) {g0 : GB} (hI : SInv P n s g0)
    (hmax : Maximal P s) {g : GB} (hg : g.Ok) (hex : ExecT P n g) (hlast : g.co = g0.co)
    {t : Tid} (ht : t ∈ P.threads) (htr : tr P g t = tr P g0 t) :
    ExecT P n (synth P s g t) ∧ (synth P s g t).Ok ∧ (synth P s g t).co = g.co ∧
      (∀ t', t' ≠ t → tr P (synth P s g t) t' = tr P g t') ∧
      (lifeSys P n).toProgram.step t (tr P (synth P s g t) t) = none := by
  have hlast' : ∀ x, g.last x = g0.last x := fun x => by simp [GB.last, hlast]
  have hrel := hI.rel t ht
  rw [← htr] at hrel
  have hnext : next P s t = none := by
    cases h : next P s t with
    | none => rfl
    | some o => exact absurd (enabled_of_next ht h) (hmax o)
  have hb : Act.block.IsLocal := by simp [Act.IsLocal]
  unfold TRel at hrel
  cases hs : s.status t <;> simp only [hs] at hrel
  · -- new: never started
    obtain ⟨hu, -, -⟩ := hrel
    have hr : P.isRoot t = false := by
      cases h' : P.isRoot t
      · rfl
      · exact absurd hs (hI.newRoot t h')
    have hsyn : synth P s g t = (g.read t (P.st t) .init).loc0 t .block := by
      simp [synth, hs]
    rw [hsyn]
    have hst : stopped (lifeTab P) t (tr P g t) = false := by rw [hu]; rfl
    obtain ⟨he1, htr1⟩ := emit_read (src := .init) hg hex
      (step_of_lifeTab hn ht hst (by rw [hu, lifeTab_nil hr]))
    have hv : valE P (P.st t) .init = 0 := by simp [valE, hF.mem_st ht, hr]
    rw [hv] at htr1
    have hu1 : tr P (g.read t (P.st t) .init) t = [some 0] := by rw [tr_self htr1, hu]; rfl
    have hst1 : stopped (lifeTab P) t (tr P (g.read t (P.st t) .init) t) = false := by
      rw [hu1]; simp [stopped, lifeTab_nil hr, isStop]
    have hblk : lifeTab P t [some 0] = some .block := by simp [lifeTab, hr]
    obtain ⟨he2, htr2⟩ := emit_loc0 (a := .block) he1 hb
      (step_of_lifeTab hn ht hst1 (by rw [hu1, hblk]))
    refine ⟨he2, ((hg.read_init _ _ ?_).loc0 _ _ hb (by simp [Act.IsCons])), ?_, ?_, ?_⟩
    · rw [hlast]
      refine hI.minv.life t ht ?_
      cases h : s.started t
      · rfl
      · exact absurd (Enabled.begin ht hs h) (hmax _)
    · simp [GB.loc0, GB.push, GB.read]
    · intro t' h'; rw [tr_other htr2 h', tr_other htr1 h']
    · apply step_none_of_stopped
      rw [tr_self htr2, hu1, stopped_append, hblk]
      simp [isStop]
  · -- running: at a disabled `lock` or `join`
    obtain ⟨hst, hbd⟩ := hrel
    rcases next_none_running hs hnext with ⟨l, hc, hh, hf⟩ | ⟨u, hc, hj⟩
    · have hsyn : synth P s g t = (g.read t l (g.last l)).loc0 t .block := by
        unfold synth; rw [hs]; dsimp only; rw [rest_cons hc]; simp [hh, hf, GB.readLast]
      rw [hsyn]
      rw [rest_cons hc] at hbd
      have h0 : holdsM s t l = 0 := holdsM_zero hh
      have hl : P.isLock l = true := by simpa [callOk] using callOk_head hF hI ht hc
      have ha1 : (⟨.lock l :: (s.rest t).tail, holdsM s t, .ready⟩ : TState).act P.st t =
          some (.read l) := by simp [TState.act, h0]
      obtain ⟨he1, htr1⟩ := emit_read (src := g.last l) hg hex (run1 hn ht hst hbd ha1)
      have hv : valE P l (g.last l) = 1 := by
        rw [hlast', hI.vLock l hl, ite_eq_right_of_eq_false _ _ (eq_false hf)]
      rw [hv] at htr1
      obtain ⟨hb1, hst1⟩ := after1 (tr_self htr1) hst hbd ha1
      have hst1' : stopped (lifeTab P) t (tr P (g.read t l (g.last l)) t) = false := by
        rw [hst1]; rfl
      have ha2 : (TState.next ⟨.lock l :: (s.rest t).tail, holdsM s t, .ready⟩ (some 1)).act
          P.st t = some .block := by simp [TState.next, TState.act, h0]
      obtain ⟨he2, htr2⟩ := emit_loc0 (a := .block) he1 hb (run1 hn ht hst1' hb1 ha2)
      obtain ⟨-, hst2⟩ := after1 (tr_self htr2) hst1' hb1 ha2
      refine ⟨he2, (hg.readLast _ _).loc0 _ _ hb (by simp [Act.IsCons]), ?_, ?_, ?_⟩
      · simp [GB.loc0, GB.push, GB.read]
      · intro t' h'; rw [tr_other htr2 h', tr_other htr1 h']
      · exact step_none_of_stopped (by rw [hst2]; rfl)
    · have hsyn : synth P s g t = (g.read t (P.st u) (g.last (P.st u))).loc0 t .block := by
        unfold synth; rw [hs]; dsimp only; rw [rest_cons hc]; simp [hj, GB.readLast]
      rw [hsyn]
      rw [rest_cons hc] at hbd
      have hu : u ∈ P.threads := by
        have := callOk_head hF hI ht hc
        simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.1.1
      have ha1 : (⟨.join u :: (s.rest t).tail, holdsM s t, .ready⟩ : TState).act P.st t =
          some (.read (P.st u)) := by simp [TState.act]
      obtain ⟨he1, htr1⟩ := emit_read (src := g.last (P.st u)) hg hex (run1 hn ht hst hbd ha1)
      have hv : valE P (P.st u) (g.last (P.st u)) = 1 := by
        rw [hlast', hI.vLife u hu]
        simp only [MState.joinOkB, Bool.or_eq_false_iff, Bool.and_eq_false_imp,
          decide_eq_true_eq, decide_eq_false_iff_not] at hj
        have hsu : s.started u = true := by
          cases h' : s.started u
          · have : s.status u ≠ .new := fun h'' => by simp_all
            rw [hI.minv.started_of u this] at h'; cases h'
          · rfl
        simp [hsu, hj.2]
      rw [hv] at htr1
      obtain ⟨hb1, hst1⟩ := after1 (tr_self htr1) hst hbd ha1
      have hst1' :
          stopped (lifeTab P) t (tr P (g.read t (P.st u) (g.last (P.st u))) t) = false := by
        rw [hst1]; rfl
      have ha2 : (TState.next ⟨.join u :: (s.rest t).tail, holdsM s t, .ready⟩ (some 1)).act
          P.st t = some .block := by simp [TState.next, TState.act]
      obtain ⟨he2, htr2⟩ := emit_loc0 (a := .block) he1 hb (run1 hn ht hst1' hb1 ha2)
      obtain ⟨-, hst2⟩ := after1 (tr_self htr2) hst1' hb1 ha2
      refine ⟨he2, (hg.readLast _ _).loc0 _ _ hb (by simp [Act.IsCons]), ?_, ?_, ?_⟩
      · simp [GB.loc0, GB.push, GB.read]
      · intro t' h'; rw [tr_other htr2 h', tr_other htr1 h']
      · exact step_none_of_stopped (by rw [hst2]; rfl)
  · -- term
    have hsyn : synth P s g t = g := by simp [synth, hs]
    rw [hsyn]
    exact ⟨hex, hg, rfl, fun _ _ => rfl, step_none_of_tab hrel⟩
  · have hsyn : synth P s g t = g := by simp [synth, hs]
    rw [hsyn]
    exact ⟨hex, hg, rfl, fun _ _ => rfl, step_none_of_stopped hrel⟩
  · have hsyn : synth P s g t = g := by simp [synth, hs]
    rw [hsyn]
    exact ⟨hex, hg, rfl, fun _ _ => rfl, step_none_of_stopped hrel⟩

theorem finalize_spec (hF : Frag P) (hn : adequateB P n = true) {g0 : GB} (hI : SInv P n s g0)
    (hmax : Maximal P s) :
    ExecT P n (finalize P g0 s) ∧
      ∀ t ∈ P.threads, (lifeSys P n).toProgram.step t (tr P (finalize P g0 s) t) = none := by
  suffices ∀ (l : List Tid), l.Nodup → (∀ t ∈ l, t ∈ P.threads) → ∀ g : GB, g.Ok →
      ExecT P n g → g.co = g0.co → (∀ t ∈ l, tr P g t = tr P g0 t) →
      ExecT P n (l.foldl (synth P s) g) ∧
        (∀ t ∈ l, (lifeSys P n).toProgram.step t (tr P (l.foldl (synth P s) g) t) = none) ∧
        (∀ t, t ∉ l → tr P (l.foldl (synth P s) g) t = tr P g t) by
    obtain ⟨h1, h2, -⟩ :=
      this P.threads P.nodup (fun _ h => h) g0 hI.ok hI.exec rfl (fun _ _ => rfl)
    exact ⟨h1, h2⟩
  intro l
  induction l with
  | nil => intro _ _ g _ hex _ _; exact ⟨hex, by simp, fun _ _ => rfl⟩
  | cons t l ih =>
    intro hnd hl g hg hex hco htr
    have ht := hl t List.mem_cons_self
    obtain ⟨he1, hg1, hco1, htr1, hst1⟩ :=
      synth_spec hF hn hI hmax hg hex hco ht (htr t List.mem_cons_self)
    have htn : t ∉ l := (List.nodup_cons.mp hnd).1
    obtain ⟨h1, h2, h3⟩ := ih (List.nodup_cons.mp hnd).2
      (fun t' h => hl t' (List.mem_cons_of_mem _ h)) _ hg1 he1 (hco1.trans hco) (fun t' h => by
        rw [htr1 t' (fun h' => htn (h' ▸ h)), htr t' (List.mem_cons_of_mem _ h)])
    simp only [List.foldl_cons]
    refine ⟨h1, ?_, ?_⟩
    · intro t' h'
      rcases List.mem_cons.mp h' with rfl | h'
      · rw [h3 _ htn]; exact hst1
      · exact h2 t' h'
    · intro t' h'
      rw [h3 t' (fun h'' => h' (List.mem_cons_of_mem _ h''))]
      exact htr1 t' (fun h'' => h' (h'' ▸ List.mem_cons_self))

/-- **`G1Sim` holds.** -/
theorem g1Sim : G1Sim := by
  intro P n hf hn rs s hr
  have hF := frag_of_fragB hf
  exact finalize_spec hF hn (SInv.steps hF hn hr.1) hr.2

/-- **Gate clause 1, `Exec` part.** -/
theorem g1Exec : G1Exec := (g1Exec_full_of_sim g1Sim).1

/-- **Gate clause 1, `Full` part.** -/
theorem g1Full : G1Full := (g1Exec_full_of_sim g1Sim).2

end Sem

end Life

end Condpor
