import Mazurkiewicz.Condpor.Rmw.LifecycleGateSim

/-!
# Gate clause 1: the stepping thread (LC2-b, part 7)

`SInv.thread`: under `SInv`, the events an enabled occurrence emits carry the compiled steps
(`ExecT`), the other threads' values do not change, and the stepping thread is related to
its new state.
-/

namespace Condpor

namespace Life

namespace Sem

variable {P : LProg} {n : ℕ} {s : MState} {g : GB}

theorem callOk_head (hF : Frag P) (hI : SInv P n s g) {t : Tid} (ht : t ∈ P.threads) {c : TOp}
    (hc : (s.rest t).head? = some c) : callOk P t c = true :=
  hF.calls t ht _ (hI.minv.head_mem hc)

theorem holdsM_zero {t : Tid} {l : Loc} (h : s.heldB t l = false) : holdsM s t l = 0 := by
  unfold holdsM
  split_ifs with h1
  · rw [heldB_eq_false] at h; exact h h1
  · rfl

theorem holdsM_count {t : Tid} {l : Loc} (h : s.heldB t l = true) : holdsM s t l = s.count l := by
  rw [heldB_eq_true] at h
  simp [holdsM, h.1]

/-- The stepping thread: emitted events carry the compiled steps; the other threads' values do
not change; the thread is related to its new state. -/
theorem SInv.thread (hF : Frag P) (hn : adequateB P n = true) (hI : SInv P n s g) {o : Occ}
    (he : Enabled P s o) :
    ExecT P n (emit P g o) ∧ (∀ t', t' ≠ o.tid → tr P (emit P g o) t' = tr P g t') ∧
      TRel P (eff s o) o.tid (tr P (emit P g o) o.tid) := by
  cases he
  case begin t ht hs h =>
    have hrel := hI.rel t ht
    unfold TRel at hrel
    rw [hs] at hrel
    obtain ⟨hu, hrest, hown⟩ := hrel
    have hr : P.isRoot t = false := by
      cases h' : P.isRoot t
      · rfl
      · exact absurd hs (hI.newRoot t h')
    have hst : stopped (lifeTab P) t (tr P g t) = false := by rw [hu]; rfl
    have hs1 : (lifeSys P n).toProgram.step t (tr P g t) = some (.read (P.st t)) :=
      step_of_lifeTab hn ht hst (by rw [hu, lifeTab_nil hr])
    obtain ⟨he1, htr1⟩ := emit_read (src := g.last (P.st t)) hI.ok hI.exec hs1
    have hv : valE P (P.st t) (g.last (P.st t)) = 1 := by rw [hI.vLife t ht, h, hs]; rfl
    rw [hv] at htr1
    have hem : emit P g (.begin t) = g.read t (P.st t) (g.last (P.st t)) := rfl
    rw [hem]
    refine ⟨he1, fun t' h' => tr_other htr1 h', ?_⟩
    simp only [Occ.tid]
    unfold TRel
    have : (eff s (.begin t)).status t = .running := by simp [eff, MState.setSt]
    rw [this]
    dsimp only
    rw [tr_self htr1, hu]
    refine ⟨by simp [stopped, lifeTab_nil hr, isStop], ?_⟩
    simp only [BodyAt, hr, Bool.false_eq_true, ↓reduceIte]
    refine ⟨some 1, [], by simp, by simp, ?_⟩
    simp only [tState, List.foldl_nil, TState.init, eff, MState.setSt]
    rw [hrest]
    congr 1
    funext l
    simp [holdsM, hown l]
  case acq t l ht hs hc hh hf =>
    obtain ⟨hst, hb⟩ := trel_running (hI.rel t ht) hs
    rw [rest_cons hc] at hb
    have h0 : holdsM s t l = 0 := holdsM_zero hh
    have hl : P.isLock l = true := by simpa [callOk] using callOk_head hF hI ht hc
    have ha1 : (⟨.lock l :: (s.rest t).tail, holdsM s t, .ready⟩ : TState).act P.st t =
        some (.read l) := by simp [TState.act, h0]
    obtain ⟨he1, htr1⟩ := emit_read (src := g.last l) hI.ok hI.exec (run1 hn ht hst hb ha1)
    have hv : valE P l (g.last l) = 0 := by rw [hI.vLock l hl, hf]; rfl
    rw [hv] at htr1
    obtain ⟨hb1, hst1⟩ := after1 (tr_self htr1) hst hb ha1
    have hst1' : stopped (lifeTab P) t (tr P (g.read t l (g.last l)) t) = false := by
      rw [hst1]; rfl
    have ha2 : (TState.next ⟨.lock l :: (s.rest t).tail, holdsM s t, .ready⟩ (some 0)).act
        P.st t = some (.write l 1) := by simp [TState.next, TState.act, h0]
    obtain ⟨he2, htr2⟩ := emit_write he1 (run1 hn ht hst1' hb1 ha2)
    obtain ⟨hb2, hst2⟩ := after1 (tr_self htr2) hst1' hb1 ha2
    have hem : emit P g (.acq t l) = (g.read t l (g.last l)).write t l 1 := rfl
    rw [hem]
    refine ⟨he2, fun t' h' => by rw [tr_other htr2 h', tr_other htr1 h'], ?_⟩
    unfold TRel
    have : (eff s (.acq t l)).status t = .running := hs
    simp only [Occ.tid, this]
    refine ⟨by rw [hst2]; rfl, ?_⟩
    convert hb2 using 1
    simp only [TState.next, h0, ↓reduceIte, TState.mk.injEq]
    refine ⟨by simp [eff, MState.adv], ?_, trivial⟩
    funext l'
    simp only [holdsM, eff, MState.adv, Function.update_apply]
    split_ifs <;> simp_all
  case tryAcq t l k ht hs hc hh hf =>
    obtain ⟨hst, hb⟩ := trel_running (hI.rel t ht) hs
    rw [rest_cons hc] at hb
    have h0 : holdsM s t l = 0 := holdsM_zero hh
    have hl : P.isLock l = true := by simpa [callOk] using callOk_head hF hI ht hc
    have ha1 : (⟨.tryLock l k :: (s.rest t).tail, holdsM s t, .ready⟩ : TState).act P.st t =
        some (.read l) := by simp [TState.act, h0]
    obtain ⟨he1, htr1⟩ := emit_read (src := g.last l) hI.ok hI.exec (run1 hn ht hst hb ha1)
    have hv : valE P l (g.last l) = 0 := by rw [hI.vLock l hl, hf]; rfl
    rw [hv] at htr1
    obtain ⟨hb1, hst1⟩ := after1 (tr_self htr1) hst hb ha1
    have hst1' : stopped (lifeTab P) t (tr P (g.read t l (g.last l)) t) = false := by
      rw [hst1]; rfl
    have ha2 : (TState.next ⟨.tryLock l k :: (s.rest t).tail, holdsM s t, .ready⟩ (some 0)).act
        P.st t = some (.write l 1) := by simp [TState.next, TState.act, h0]
    obtain ⟨he2, htr2⟩ := emit_write he1 (run1 hn ht hst1' hb1 ha2)
    obtain ⟨hb2, hst2⟩ := after1 (tr_self htr2) hst1' hb1 ha2
    have hem : emit P g (.tryAcq t l k) = (g.read t l (g.last l)).write t l 1 := rfl
    rw [hem]
    refine ⟨he2, fun t' h' => by rw [tr_other htr2 h', tr_other htr1 h'], ?_⟩
    unfold TRel
    have : (eff s (.tryAcq t l k)).status t = .running := hs
    simp only [Occ.tid, this]
    refine ⟨by rw [hst2]; rfl, ?_⟩
    convert hb2 using 1
    simp only [TState.next, h0, ↓reduceIte, TState.mk.injEq]
    refine ⟨by simp [eff, MState.adv], ?_, trivial⟩
    funext l'
    simp only [holdsM, eff, MState.adv, Function.update_apply]
    split_ifs <;> simp_all
  case tryFail t l k ht hs hc hh hf =>
    obtain ⟨hst, hb⟩ := trel_running (hI.rel t ht) hs
    rw [rest_cons hc] at hb
    have h0 : holdsM s t l = 0 := holdsM_zero hh
    have hl : P.isLock l = true := by simpa [callOk] using callOk_head hF hI ht hc
    have ha1 : (⟨.tryLock l k :: (s.rest t).tail, holdsM s t, .ready⟩ : TState).act P.st t =
        some (.read l) := by simp [TState.act, h0]
    obtain ⟨he1, htr1⟩ := emit_read (src := g.last l) hI.ok hI.exec (run1 hn ht hst hb ha1)
    have hv : valE P l (g.last l) = 1 := by
      rw [hI.vLock l hl, ite_eq_right_of_eq_false _ _ (eq_false hf)]
    rw [hv] at htr1
    obtain ⟨hb1, hst1⟩ := after1 (tr_self htr1) hst hb ha1
    have hem : emit P g (.tryFail t l k) = g.read t l (g.last l) := rfl
    rw [hem]
    refine ⟨he1, fun t' h' => by rw [tr_other htr1 h'], ?_⟩
    unfold TRel
    have : (eff s (.tryFail t l k)).status t = .running := hs
    simp only [Occ.tid, this]
    refine ⟨by rw [hst1]; rfl, ?_⟩
    convert hb1 using 1
    simp only [TState.next, h0, ↓reduceIte, Option.some.injEq, one_ne_zero, TState.mk.injEq]
    exact ⟨by simp [eff, MState.adv], rfl, trivial⟩
  case reacq t l ht hs hc hh =>
    obtain ⟨hst, hb⟩ := trel_running (hI.rel t ht) hs
    rw [rest_cons hc] at hb
    have hown := (heldB_eq_true.mp hh).1
    have hpos := (heldB_eq_true.mp hh).2
    have h0 : holdsM s t l = s.count l := holdsM_count hh
    have ha1 : (⟨.lock l :: (s.rest t).tail, holdsM s t, .ready⟩ : TState).act P.st t =
        some (.gen 0) := by simp [TState.act, h0]; omega
    obtain ⟨he1, htr1⟩ := emit_loc0 (a := .gen 0) hI.exec (by simp [Act.IsLocal])
      (run1 hn ht hst hb ha1)
    obtain ⟨hb1, hst1⟩ := after1 (tr_self htr1) hst hb ha1
    have hem : emit P g (.reacq t l) = g.loc0 t (.gen 0) := rfl
    rw [hem]
    refine ⟨he1, fun t' h' => by rw [tr_other htr1 h'], ?_⟩
    unfold TRel
    have : (eff s (.reacq t l)).status t = .running := hs
    simp only [Occ.tid, this]
    refine ⟨by rw [hst1]; rfl, ?_⟩
    convert hb1 using 1
    have hne : holdsM s t l ≠ 0 := by omega
    simp only [TState.next, hne, ↓reduceIte, TState.mk.injEq]
    refine ⟨by simp [eff, MState.adv], ?_, trivial⟩
    funext l'
    simp only [holdsM, eff, MState.adv, Function.update_apply]
    split_ifs <;> simp_all
  case tryRe t l k ht hs hc hh =>
    obtain ⟨hst, hb⟩ := trel_running (hI.rel t ht) hs
    rw [rest_cons hc] at hb
    have hown := (heldB_eq_true.mp hh).1
    have hpos := (heldB_eq_true.mp hh).2
    have h0 : holdsM s t l = s.count l := holdsM_count hh
    have ha1 : (⟨.tryLock l k :: (s.rest t).tail, holdsM s t, .ready⟩ : TState).act P.st t =
        some (.gen 0) := by simp [TState.act, h0]; omega
    obtain ⟨he1, htr1⟩ := emit_loc0 (a := .gen 0) hI.exec (by simp [Act.IsLocal])
      (run1 hn ht hst hb ha1)
    obtain ⟨hb1, hst1⟩ := after1 (tr_self htr1) hst hb ha1
    have hem : emit P g (.tryRe t l k) = g.loc0 t (.gen 0) := rfl
    rw [hem]
    refine ⟨he1, fun t' h' => by rw [tr_other htr1 h'], ?_⟩
    unfold TRel
    have : (eff s (.tryRe t l k)).status t = .running := hs
    simp only [Occ.tid, this]
    refine ⟨by rw [hst1]; rfl, ?_⟩
    convert hb1 using 1
    have hne : holdsM s t l ≠ 0 := by omega
    simp only [TState.next, hne, ↓reduceIte, TState.mk.injEq]
    refine ⟨by simp [eff, MState.adv], ?_, trivial⟩
    funext l'
    simp only [holdsM, eff, MState.adv, Function.update_apply]
    split_ifs <;> simp_all
  case unlockRe t l ht hs hc hh h1 =>
    obtain ⟨hst, hb⟩ := trel_running (hI.rel t ht) hs
    rw [rest_cons hc] at hb
    have hown := (heldB_eq_true.mp hh).1
    have h0 : holdsM s t l = s.count l := holdsM_count hh
    have ha1 : (⟨.unlock l :: (s.rest t).tail, holdsM s t, .ready⟩ : TState).act P.st t =
        some (.gen 0) := by
      have e1 : ¬ s.count l = 0 := by omega
      have e2 : ¬ s.count l = 1 := by omega
      simp [TState.act, h0, e1, e2]
    obtain ⟨he1, htr1⟩ := emit_loc0 (a := .gen 0) hI.exec (by simp [Act.IsLocal])
      (run1 hn ht hst hb ha1)
    obtain ⟨hb1, hst1⟩ := after1 (tr_self htr1) hst hb ha1
    have hem : emit P g (.unlockRe t l) = g.loc0 t (.gen 0) := rfl
    rw [hem]
    refine ⟨he1, fun t' h' => by rw [tr_other htr1 h'], ?_⟩
    unfold TRel
    have : (eff s (.unlockRe t l)).status t = .running := hs
    simp only [Occ.tid, this]
    refine ⟨by rw [hst1]; rfl, ?_⟩
    convert hb1 using 1
    have hne : holdsM s t l ≠ 0 := by omega
    simp only [TState.next, hne, ↓reduceIte, TState.mk.injEq]
    refine ⟨by simp [eff, MState.adv], ?_, trivial⟩
    funext l'
    simp only [holdsM, eff, MState.adv, Function.update_apply]
    split_ifs <;> simp_all
  case release t l ht hs hc hh h1 =>
    obtain ⟨hst, hb⟩ := trel_running (hI.rel t ht) hs
    rw [rest_cons hc] at hb
    have hown := (heldB_eq_true.mp hh).1
    have h0 : holdsM s t l = s.count l := holdsM_count hh
    have ha1 : (⟨.unlock l :: (s.rest t).tail, holdsM s t, .ready⟩ : TState).act P.st t =
        some (.write l 0) := by simp [TState.act, h0, h1]
    obtain ⟨he1, htr1⟩ := emit_write hI.exec (run1 hn ht hst hb ha1)
    obtain ⟨hb1, hst1⟩ := after1 (tr_self htr1) hst hb ha1
    have hem : emit P g (.release t l) = g.write t l 0 := rfl
    rw [hem]
    refine ⟨he1, fun t' h' => by rw [tr_other htr1 h'], ?_⟩
    unfold TRel
    have : (eff s (.release t l)).status t = .running := hs
    simp only [Occ.tid, this]
    refine ⟨by rw [hst1]; rfl, ?_⟩
    convert hb1 using 1
    have hne : holdsM s t l ≠ 0 := by omega
    simp only [TState.next, hne, ↓reduceIte, TState.mk.injEq]
    refine ⟨by simp [eff, MState.adv], ?_, trivial⟩
    funext l'
    simp only [holdsM, eff, MState.adv, Function.update_apply]
    split_ifs <;> simp_all
  case unlockErr t l ht hs hc hh =>
    obtain ⟨hst, hb⟩ := trel_running (hI.rel t ht) hs
    rw [rest_cons hc] at hb
    have h0 : holdsM s t l = 0 := holdsM_zero hh
    have ha1 : (⟨.unlock l :: (s.rest t).tail, holdsM s t, .ready⟩ : TState).act P.st t =
        some .error := by simp [TState.act, h0]
    obtain ⟨he1, htr1⟩ := emit_loc0 (a := .error) hI.exec (by simp [Act.IsLocal])
      (run1 hn ht hst hb ha1)
    obtain ⟨-, hst1⟩ := after1 (tr_self htr1) hst hb ha1
    have hem : emit P g (.unlockErr t l) = g.loc0 t .error := rfl
    rw [hem]
    refine ⟨he1, fun t' h' => by rw [tr_other htr1 h'], ?_⟩
    unfold TRel
    have : (eff s (.unlockErr t l)).status t = .erred := by simp [eff, MState.setSt]
    simp only [Occ.tid, this]
    rw [hst1]; rfl
  case query t l ht hs hc hl =>
    obtain ⟨hst, hb⟩ := trel_running (hI.rel t ht) hs
    rw [rest_cons hc] at hb
    have ha1 : (⟨.rd l :: (s.rest t).tail, holdsM s t, .ready⟩ : TState).act P.st t =
        some (.read l) := by simp [TState.act]
    obtain ⟨he1, htr1⟩ := emit_read (src := g.last l) hI.ok hI.exec (run1 hn ht hst hb ha1)
    obtain ⟨hb1, hst1⟩ := after1 (tr_self htr1) hst hb ha1
    have hem : emit P g (.query t l) = g.read t l (g.last l) := rfl
    rw [hem]
    refine ⟨he1, fun t' h' => by rw [tr_other htr1 h'], ?_⟩
    unfold TRel
    have : (eff s (.query t l)).status t = .running := hs
    simp only [Occ.tid, this]
    refine ⟨by rw [hst1]; rfl, ?_⟩
    convert hb1 using 1
    simp only [TState.next, TState.mk.injEq]
    exact ⟨by simp [eff, MState.adv], rfl, trivial⟩
  case rd t x ht hs hc hl =>
    obtain ⟨hst, hb⟩ := trel_running (hI.rel t ht) hs
    rw [rest_cons hc] at hb
    have ha1 : (⟨.rd x :: (s.rest t).tail, holdsM s t, .ready⟩ : TState).act P.st t =
        some (.read x) := by simp [TState.act]
    obtain ⟨he1, htr1⟩ := emit_read (src := g.last x) hI.ok hI.exec (run1 hn ht hst hb ha1)
    obtain ⟨hb1, hst1⟩ := after1 (tr_self htr1) hst hb ha1
    have hem : emit P g (.rd t x) = g.read t x (g.last x) := rfl
    rw [hem]
    refine ⟨he1, fun t' h' => by rw [tr_other htr1 h'], ?_⟩
    unfold TRel
    have : (eff s (.rd t x)).status t = .running := hs
    simp only [Occ.tid, this]
    refine ⟨by rw [hst1]; rfl, ?_⟩
    convert hb1 using 1
    simp only [TState.next, TState.mk.injEq]
    exact ⟨by simp [eff, MState.adv], rfl, trivial⟩
  case wr t x v ht hs hc =>
    obtain ⟨hst, hb⟩ := trel_running (hI.rel t ht) hs
    rw [rest_cons hc] at hb
    have ha1 : (⟨.wr x v :: (s.rest t).tail, holdsM s t, .ready⟩ : TState).act P.st t =
        some (.write x v) := by simp [TState.act]
    obtain ⟨he1, htr1⟩ := emit_write hI.exec (run1 hn ht hst hb ha1)
    obtain ⟨hb1, hst1⟩ := after1 (tr_self htr1) hst hb ha1
    have hem : emit P g (.wr t x v) = g.write t x v := rfl
    rw [hem]
    refine ⟨he1, fun t' h' => by rw [tr_other htr1 h'], ?_⟩
    unfold TRel
    have : (eff s (.wr t x v)).status t = .running := hs
    simp only [Occ.tid, this]
    refine ⟨by rw [hst1]; rfl, ?_⟩
    convert hb1 using 1
    simp only [TState.next, TState.mk.injEq]
    exact ⟨by simp [eff, MState.adv], rfl, trivial⟩
  case asmOk t x v ht hs hc hv =>
    obtain ⟨hst, hb⟩ := trel_running (hI.rel t ht) hs
    rw [rest_cons hc] at hb
    have hd : P.isData x = true := by simpa [callOk] using callOk_head hF hI ht hc
    have ha1 : (⟨.assume x v :: (s.rest t).tail, holdsM s t, .ready⟩ : TState).act P.st t =
        some (.read x) := by simp [TState.act]
    obtain ⟨he1, htr1⟩ := emit_read (src := g.last x) hI.ok hI.exec (run1 hn ht hst hb ha1)
    rw [hI.vData x hd, hv] at htr1
    obtain ⟨hb1, hst1⟩ := after1 (tr_self htr1) hst hb ha1
    have hem : emit P g (.asmOk t x v) = g.read t x (g.last x) := rfl
    rw [hem]
    refine ⟨he1, fun t' h' => by rw [tr_other htr1 h'], ?_⟩
    unfold TRel
    have : (eff s (.asmOk t x v)).status t = .running := hs
    simp only [Occ.tid, this]
    refine ⟨by rw [hst1]; rfl, ?_⟩
    convert hb1 using 1
    simp only [TState.next, ↓reduceIte, TState.mk.injEq]
    exact ⟨by simp [eff, MState.adv], rfl, trivial⟩
  case asmStop t x v ht hs hc hv =>
    obtain ⟨hst, hb⟩ := trel_running (hI.rel t ht) hs
    rw [rest_cons hc] at hb
    have hd : P.isData x = true := by simpa [callOk] using callOk_head hF hI ht hc
    have ha1 : (⟨.assume x v :: (s.rest t).tail, holdsM s t, .ready⟩ : TState).act P.st t =
        some (.read x) := by simp [TState.act]
    obtain ⟨he1, htr1⟩ := emit_read (src := g.last x) hI.ok hI.exec (run1 hn ht hst hb ha1)
    rw [hI.vData x hd] at htr1
    obtain ⟨hb1, hst1⟩ := after1 (tr_self htr1) hst hb ha1
    have hst1' : stopped (lifeTab P) t (tr P (g.read t x (g.last x)) t) = false := by
      rw [hst1]; rfl
    have ha2 : (TState.next ⟨.assume x v :: (s.rest t).tail, holdsM s t, .ready⟩
        (some (s.mem x))).act P.st t = some .block := by simp [TState.next, TState.act, hv]
    obtain ⟨he2, htr2⟩ := emit_loc0 (a := .block) he1 (by simp [Act.IsLocal])
      (run1 hn ht hst1' hb1 ha2)
    obtain ⟨-, hst2⟩ := after1 (tr_self htr2) hst1' hb1 ha2
    have hem : emit P g (.asmStop t x v) = (g.read t x (g.last x)).loc0 t .block := rfl
    rw [hem]
    refine ⟨he2, fun t' h' => by rw [tr_other htr2 h', tr_other htr1 h'], ?_⟩
    unfold TRel
    have : (eff s (.asmStop t x v)).status t = .stopped := by simp [eff, MState.setSt]
    simp only [Occ.tid, this]
    rw [hst2]; rfl
  case start t u ht hs hc =>
    obtain ⟨hst, hb⟩ := trel_running (hI.rel t ht) hs
    rw [rest_cons hc] at hb
    have ha1 : (⟨.start u :: (s.rest t).tail, holdsM s t, .ready⟩ : TState).act P.st t =
        some (.write (P.st u) 1) := by simp [TState.act]
    obtain ⟨he1, htr1⟩ := emit_write hI.exec (run1 hn ht hst hb ha1)
    obtain ⟨hb1, hst1⟩ := after1 (tr_self htr1) hst hb ha1
    have hem : emit P g (.start t u) = g.write t (P.st u) 1 := rfl
    rw [hem]
    refine ⟨he1, fun t' h' => by rw [tr_other htr1 h'], ?_⟩
    unfold TRel
    have : (eff s (.start t u)).status t = .running := hs
    simp only [Occ.tid, this]
    refine ⟨by rw [hst1]; rfl, ?_⟩
    convert hb1 using 1
    simp only [TState.next, TState.mk.injEq]
    exact ⟨by simp [eff, MState.adv], rfl, trivial⟩
  case join t u ht hs hc hj =>
    obtain ⟨hst, hb⟩ := trel_running (hI.rel t ht) hs
    rw [rest_cons hc] at hb
    have hu : u ∈ P.threads := by
      have := callOk_head hF hI ht hc
      simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1.1
    have ha1 : (⟨.join u :: (s.rest t).tail, holdsM s t, .ready⟩ : TState).act P.st t =
        some (.read (P.st u)) := by simp [TState.act]
    obtain ⟨he1, htr1⟩ := emit_read (src := g.last (P.st u)) hI.ok hI.exec
      (run1 hn ht hst hb ha1)
    have hv1 : valE P (P.st u) (g.last (P.st u)) ≠ 1 := by
      rw [hI.vLife u hu]
      rw [joinOkB_eq_true] at hj
      rcases hj with ⟨h1, h2⟩ | h1
      · simp [h2]
      · have := hI.minv.started_of u (by rw [h1]; simp)
        simp [this, h1]
    obtain ⟨hb1, hst1⟩ := after1 (tr_self htr1) hst hb ha1
    have hem : emit P g (.join t u) = g.read t (P.st u) (g.last (P.st u)) := rfl
    rw [hem]
    refine ⟨he1, fun t' h' => by rw [tr_other htr1 h'], ?_⟩
    unfold TRel
    have : (eff s (.join t u)).status t = .running := hs
    simp only [Occ.tid, this]
    refine ⟨by rw [hst1]; rfl, ?_⟩
    convert hb1 using 1
    simp only [TState.next, Option.some.injEq, hv1, ↓reduceIte, TState.mk.injEq]
    exact ⟨by simp [eff, MState.adv], rfl, trivial⟩
  case fin t ht hs hc =>
    obtain ⟨hst, hb⟩ := trel_running (hI.rel t ht) hs
    rw [hc] at hb
    have ha1 : (⟨[], holdsM s t, .ready⟩ : TState).act P.st t = some (.write (P.st t) 2) := by
      simp [TState.act]
    obtain ⟨he1, htr1⟩ := emit_write hI.exec (run1 hn ht hst hb ha1)
    obtain ⟨hb1, -⟩ := after1 (tr_self htr1) hst hb ha1
    have hem : emit P g (.fin t) = g.write t (P.st t) 2 := rfl
    rw [hem]
    refine ⟨he1, fun t' h' => by rw [tr_other htr1 h'], ?_⟩
    unfold TRel
    have : (eff s (.fin t)).status t = .term := by simp [eff, MState.setSt]
    simp only [Occ.tid, this]
    rw [lifeTab_of_bodyAt hb1]
    simp [TState.next, TState.act]

end Sem

end Life

end Condpor
