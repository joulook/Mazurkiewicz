import Mazurkiewicz.Condpor.Rmw.LifecycleGate2Emit

/-!
# Gate clause 2, part 3f: synthetic events and final waits (LC2-b, continuation 3)

* `synE P s k t`: the synthetic events that `synth` adds for thread `t` when the builder has
  `k` events of `t`; `finalizeE_L`: `finalize` appends them thread by thread.
* `waitOf_of_last`: the wait of a thread whose last event is a `block` after the read `p`.
* `tail_final`: in a terminal-valid graph, the read of a wait pair at a non-data location
  whose `block` is the last event of its thread reads the coherence-maximal write (not
  exploration; the kind of such a read is never `asm`).
-/

namespace Condpor

namespace Life

namespace Sem

open _root_.List Targets

variable {P : LProg} {n : ℕ}

/-- The synthetic events of thread `t` (by the cases of `synth`), with `k` events so far. -/
def synE (P : LProg) (s : MState) (k : ℕ) (t : Tid) : List TEv :=
  match s.status t with
  | .new => [⟨t, k, .read (P.st t)⟩, ⟨t, k + 1, .block⟩]
  | .running =>
    match s.rest t with
    | .lock l :: _ =>
      if !s.heldB t l && decide (s.count l ≠ 0) then [⟨t, k, .read l⟩, ⟨t, k + 1, .block⟩]
      else []
    | .join u :: _ =>
      if !s.joinOkB u then [⟨t, k, .read (P.st u)⟩, ⟨t, k + 1, .block⟩] else []
    | _ => []
  | _ => []

theorem L_read_block (g : GB) (t : Tid) (x : Loc) (src : Ev) :
    ((g.read t x src).loc0 t .block).L =
      g.L ++ [⟨t, g.cnt t, .read x⟩, ⟨t, g.cnt t + 1, .block⟩] := by
  simp [GB.read, GB.loc0, GB.L, GB.push, GB.ev]

theorem cnt_read_block (g : GB) (t : Tid) (x : Loc) (src : Ev) {t' : Tid} (h : t' ≠ t) :
    ((g.read t x src).loc0 t .block).cnt t' = g.cnt t' := by
  simp [GB.read, GB.loc0, GB.push, GB.ev, h]

theorem synthE_L (s : MState) (g : GB) (t : Tid) :
    (synth P s g t).L = g.L ++ synE P s (g.cnt t) t := by
  unfold synth synE
  cases hs : s.status t
  case new => exact L_read_block g t (P.st t) .init
  case running =>
    dsimp only
    cases hr : s.rest t with
    | nil => simp
    | cons c tl =>
      cases c
      case lock l =>
        dsimp only
        split_ifs
        · exact L_read_block g t _ _
        · simp
      case join u =>
        dsimp only
        split_ifs
        · exact L_read_block g t _ _
        · simp
      all_goals simp
  all_goals simp

theorem synth_cnt (s : MState) (g : GB) (t : Tid) {t' : Tid} (h : t' ≠ t) :
    (synth P s g t).cnt t' = g.cnt t' := by
  unfold synth
  cases hs : s.status t
  case new => exact cnt_read_block g t _ _ h
  case running =>
    dsimp only
    cases hr : s.rest t with
    | nil => rfl
    | cons c tl =>
      cases c
      case lock l =>
        dsimp only
        split_ifs
        · exact cnt_read_block g t _ _ h
        · rfl
      case join u =>
        dsimp only
        split_ifs
        · exact cnt_read_block g t _ _ h
        · rfl
      all_goals rfl
  all_goals rfl

theorem foldl_synthE_L (s : MState) :
    ∀ (ts : List Tid) (g : GB), ts.Nodup →
      (ts.foldl (synth P s) g).L = g.L ++ ts.flatMap (fun t => synE P s (g.cnt t) t)
  | [], g, _ => by simp
  | t :: ts, g, hn => by
    rw [foldl_cons, foldl_synthE_L s ts _ (nodup_cons.mp hn).2, synthE_L, flatMap_cons,
      append_assoc]
    congr 2
    refine flatMap_congr (fun t' ht' => ?_)
    have hne : t' ≠ t := fun h => (nodup_cons.mp hn).1 (h ▸ ht')
    rw [synth_cnt s g t hne]

theorem finalizeE_L (s : MState) (g : GB) :
    (finalize P g s).L = g.L ++ P.threads.flatMap (fun t => synE P s (g.cnt t) t) :=
  foldl_synthE_L s P.threads g P.nodup

/-! ### Final waits -/

/-- The wait of a thread whose last event is a `block` after the read `p`. -/
theorem waitOf_of_last {c : Config} (hc : c.Wf) {t : Tid} {p b : TEv}
    (hb : b ∈ c.abs.events) (hbt : b.tid = t) (hblk : b.act = .block)
    (hlast : ∀ q ∈ c.abs.events, q.tid = t → q.idx ≤ b.idx) (hp : p ∈ c.abs.events)
    (hpt : p.tid = t) (hpi : b.idx = p.idx + 1) :
    waitOf P c t = some (kindOf P c t p, finalB c p) := by
  have hcnt : c.cnt t = b.idx + 1 := by
    rw [Config.cnt_eq c hc]
    have h1 : b.idx < c.abs.cnt t := (hc.1.exists_idx_iff t b.idx).mp ⟨b, hb, hbt, rfl⟩
    by_contra hne
    obtain ⟨q, hq, hqt, hqi⟩ := (hc.1.exists_idx_iff t (b.idx + 1)).mpr (by omega)
    have := hlast q hq hqt
    omega
  have hth : thEvents c t = (range b.idx).filterMap (c.evAt t) ++ [b] := by
    unfold thEvents
    rw [hcnt, range_succ, filterMap_append]
    simp [evAt_of_mem hc hb hbt rfl]
  unfold waitOf
  rw [hth, getLast?_concat]
  simp only [hblk, ite_true]
  rw [hpi]
  simp only [Nat.add_sub_cancel, evAt_of_mem hc hp hpt rfl]

theorem kindOf_ne_asm {c : Config} {t : Tid} {p : TEv} {x : Loc} (hx : p.act = .read x)
    (hd : P.isData x = false) : kindOf P c t p ≠ .asm := by
  unfold kindOf
  rw [hx]
  simp only
  split_ifs <;> simp_all

/-- **Final waits.** In a terminal-valid graph the read of a wait pair at a non-data location,
whose `block` is the last event of its thread, reads the coherence-maximal write. -/
theorem tail_final {c : Config} (hT : TermValid P n c) {p b : TEv} {x : Loc}
    (hw : WaitPair c.abs p b x) (hd : P.isData x = false)
    (hlast : ∀ q ∈ c.abs.events, q.tid = b.tid → q.idx ≤ b.idx) :
    c.abs.rf p = some (c.abs.maxWrite x) := by
  obtain ⟨hf, hn, hc, hE, -, hfu, hex⟩ := hT
  have hF := frag_of_fragB hf
  obtain ⟨hp, hb, hbt, hbi, hpx, hbb⟩ := hw
  have hwait := waitOf_of_last (P := P) hc hb rfl hbb hlast hp hbt.symm hbi
  have ht : b.tid ∈ P.threads := (step_some (hE.2 b hb)).2.2.2
  have hfin := (lifeClass_not_exploration_iff (lifeClass_ne_cut_of_full hn hc hfu)
    (lifeClass_ne_odd hF hc hE)).mp hex b.tid ht _ _ hwait (kindOf_ne_asm hpx hd)
  have := (finalB_iff c p).mp hfin
  rwa [hpx] at this

end Sem

end Life

end Condpor
