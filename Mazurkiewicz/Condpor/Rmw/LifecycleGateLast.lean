import Mazurkiewicz.Condpor.Rmw.LifecycleGateAtom

/-!
# Gate clause 1: the last events of finished threads (LC2-b, continuation)

`LInv P s g`: an `error` event belongs to an erred thread; the events of an erred thread end
with `error`, of an assume-stopped thread with `read x; block` (`x` data), of a terminated
thread with an event that is not `block`. Preserved by steps (`LInv.step`).
-/

namespace Condpor

namespace Life

namespace Sem

variable {P : LProg} {n : ℕ} {s : MState} {g : GB}

/-- The last events of a thread, by status. -/
def LRel (P : LProg) (s : MState) (t : Tid) (l : List TEv) : Prop :=
  match s.status t with
  | .erred => ∃ pre e, l = pre ++ [e] ∧ e.act = .error
  | .stopped => ∃ pre r b x, l = pre ++ [r, b] ∧ r.act = .read x ∧ P.isData x = true ∧
      b.act = .block
  | .term => ∃ pre e, l = pre ++ [e] ∧ e.act ≠ .block
  | _ => True

/-- The last-events invariant. -/
structure LInv (P : LProg) (s : MState) (g : GB) : Prop where
  err : ∀ e ∈ g.L, e.act = .error → s.status e.tid = .erred
  last : ∀ t, LRel P s t (thr g t)

theorem linv_init : LInv P (MState.init P) GB.empty where
  err := by simp [GB.L, GB.empty]
  last := by
    intro t
    unfold LRel
    simp only [MState.init]
    split_ifs <;> trivial

theorem thr_read (g : GB) (t t' : Tid) (x : Loc) (src : Ev) :
    thr (g.read t x src) t' = thr g t' ++ (if t = t' then [g.ev t (.read x)] else []) := by
  rw [thr_append (g' := g.read t x src) (GB.L_push g _)]; rfl

theorem thr_write (g : GB) (t t' : Tid) (x : Loc) (v : Val) :
    thr (g.write t x v) t' = thr g t' ++ (if t = t' then [g.ev t (.write x v)] else []) := by
  rw [thr_append (g' := g.write t x v) (GB.L_push g _)]; rfl

theorem thr_loc0 (g : GB) (t t' : Tid) (a : Act) :
    thr (g.loc0 t a) t' = thr g t' ++ (if t = t' then [g.ev t a] else []) := by
  rw [thr_append (g' := g.loc0 t a) (GB.L_push g _)]; rfl

theorem L_emit (P : LProg) (g : GB) (o : Occ) :
    ∃ l, (emit P g o).L = g.L ++ l ∧ ∀ e ∈ l, e.tid = o.tid ∧
      (e.act = .error → o = .unlockErr o.tid (match o with | .unlockErr _ l => l | _ => 0)) := by
  cases o <;>
    simp [emit, GB.L, GB.readLast, GB.read, GB.write, GB.loc0, GB.push, GB.ev, Occ.tid]

theorem LInv.step (hF : Frag P) (hI : SInv P n s g) (hL : LInv P s g) {o : Occ}
    (he : Enabled P s o) : LInv P (eff s o) (emit P g o) := by
  refine ⟨?_, ?_⟩
  · intro e hme hea
    obtain ⟨l, hl, hl'⟩ := L_emit P g o
    rw [hl] at hme
    rcases List.mem_append.mp hme with hme | hme
    · have h0 := hL.err e hme hea
      by_cases ht : e.tid = o.tid
      · rw [ht] at h0 ⊢
        cases he <;> simp_all [Occ.tid]
      · rw [(eff_other he ht).1]; exact h0
    · obtain ⟨h1, h2⟩ := hl' e hme
      have := h2 hea
      rw [h1]
      cases he <;> simp_all [eff, MState.setSt, Occ.tid]
  · intro t
    by_cases ht : t = o.tid
    · subst ht
      cases he
      case unlockErr t l ht hs hc hh =>
        unfold LRel
        have : (eff s (.unlockErr t l)).status t = .erred := by simp [eff, MState.setSt]
        simp only [Occ.tid, this]
        change ∃ pre e, thr (g.loc0 t .error) t = pre ++ [e] ∧ e.act = .error
        exact ⟨thr g t, g.ev t .error, by simp [thr_loc0], rfl⟩
      case asmStop t x v ht hs hc hv =>
        unfold LRel
        have : (eff s (.asmStop t x v)).status t = .stopped := by simp [eff, MState.setSt]
        simp only [Occ.tid, this]
        have hd : P.isData x = true := by simpa [callOk] using callOk_head hF hI ht hc
        change ∃ pre r b x', thr ((g.read t x (g.last x)).loc0 t .block) t = pre ++ [r, b] ∧
          r.act = .read x' ∧ P.isData x' = true ∧ b.act = .block
        exact ⟨thr g t, g.ev t (.read x), (g.read t x (g.last x)).ev t .block, x,
          by simp [thr_loc0, thr_read], rfl, hd, rfl⟩
      case fin t ht hs hc =>
        unfold LRel
        have : (eff s (.fin t)).status t = .term := by simp [eff, MState.setSt]
        simp only [Occ.tid, this]
        change ∃ pre e, thr (g.write t (P.st t) 2) t = pre ++ [e] ∧ e.act ≠ .block
        exact ⟨thr g t, g.ev t (.write (P.st t) 2), by simp [thr_write], by simp [GB.ev]⟩
      all_goals
        unfold LRel
        simp [eff, MState.adv, MState.setSt, Occ.tid, *]
    · -- another thread: same status, same events
      have hthr : thr (emit P g o) t = thr g t := by
        obtain ⟨l, hl, hl'⟩ := L_emit P g o
        have h0 : l.filter (fun e => decide (e.tid = t)) = [] :=
          List.filter_eq_nil_iff.mpr (fun e he => by simp [(hl' e he).1, Ne.symm ht])
        unfold thr; rw [hl, List.filter_append, h0, List.append_nil]
      have := hL.last t
      unfold LRel at this ⊢
      rw [(eff_other he ht).1, hthr]
      exact this

theorem LInv.steps (hF : Frag P) (hn : adequateB P n = true) {rs : List Occ}
    (hr : Steps P (MState.init P) rs s) : LInv P s (rs.foldl (emit P) GB.empty) := by
  suffices ∀ s0 g0, SInv P n s0 g0 → LInv P s0 g0 → Steps P s0 rs s →
      LInv P s (rs.foldl (emit P) g0) from this _ _ (sinv_init hF n) linv_init hr
  intro s0 g0 hI hL h
  clear hr
  induction h generalizing g0 with
  | nil => exact hL
  | cons h _ ih =>
    obtain ⟨he, rfl⟩ := h
    exact ih _ (hI.step hF hn ⟨he, rfl⟩) (hL.step hF hI he)

end Sem

end Life

end Condpor
