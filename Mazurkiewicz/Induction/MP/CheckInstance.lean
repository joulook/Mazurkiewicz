import Mazurkiewicz.Induction.MP.CheckSound

/-!
# Message passing: a proved instance of the end theorem `checkP2P_sound`

A small instance of the Section 7 end theorem with every hypothesis proved (from the Opus
review of C8, plan `plan/ind/TRACK-C-PLAN.md`, milestone C8b): thread `0` sends `5` to thread
`1`; thread `1` receives a value `v` (blocking, `.p2p`, any value) and performs `error` iff
`v ≠ 5`. Unlike the smoke test of `MP/CheckRun.lean` (an evaluation test only), the check here
is turned into safety by `checkP2P_sound`.

* `ciProg`, `ciProg_tagged`; the abstraction `ciAlpha` (traces of threads `0`, `1` and
  `pend_0`), `ciU`, `ciW`, `ciF`; `ciBad` (thread `1` has performed two events: its second
  event can only be the error), `ciAbad`; the values `ciB = [b₀, b₁, b₂]`.
* The hypotheses of `checkP2P_sound`: `ciProg_tagged`, `ci_hconf`, `ci_hdet`, `ci_hext`,
  `ci_hinit`, `ci_hdisj`, `ci_hf` (by `p2p_compose_1`, `p2p_compose_2`).
* `ci_check : CheckS … ciB … 1 = (true, 6)` (`decide +kernel`); `ci_kind`: `ciB` is
  `1`-inductive; `ci_safe : Safe Model.p2p ciProg ciBad`.
-/

namespace Must

namespace Ind

namespace CheckInst

open Graph

/-- The receive of thread `1`. -/
abbrev rbP : Lab VPred := .recv ⟨.p2p, true⟩ .any

/-- Thread `0` sends `5` to thread `1`; thread `1` receives `v` and fails iff `v ≠ 5`. -/
def ciStep : Tid → List (Option Val) → Option (Lab VPred)
  | 0, [] => some (.send .p2p 1 5)
  | 1, [] => some rbP
  | 1, [some v] => if v = 5 then none else some .error
  | _, _ => none

/-- The program of the instance. -/
def ciProg : Program VPred where
  threads := [0, 1]
  nodup := by decide
  step := ciStep
  step_none t ht := by
    match t with
    | 0 => simp at ht
    | 1 => simp at ht
    | n + 2 => rfl
  stop t u l h hs := by
    unfold ciStep at h
    split at h <;> (try split at h) <;> (try cases h) <;> simp_all [Lab.Stops, ciStep]
  nd_ne t u S h := by
    unfold ciStep at h
    split at h <;> (try split at h) <;> cases h

theorem ciProg_tagged : ciProg.Tagged .p2p := by
  intro t u l h
  change ciStep t u = some l at h
  unfold ciStep at h
  split at h <;> (try split at h) <;> (try cases h) <;> simp [Lab.model?]

theorem ci_send_tid {t : Tid} {x : List (Option Val)} {l : Lab VPred}
    (h : ciStep t x = some l) (hs : l.IsSend) : t = 0 := by
  unfold ciStep at h
  split at h <;> (try split at h) <;> (try cases h) <;> simp_all [Lab.IsSend]

theorem ci_pend_eq_nil {G : Graph VPred} (hGw : G.Wf) {t : Tid} (h : ∀ s ∈ G.US, s.tid ≠ t) :
    G.pend t = [] := by
  rw [hGw.pend_eq]
  have : G.unreadSeq t = [] := List.eq_nil_iff_forall_not_mem.mpr fun s hs =>
    h s ((mem_unreadSeq hGw).mp hs).1 ((mem_unreadSeq hGw).mp hs).2
  rw [this]
  rfl

/-! ### The abstraction -/

/-- The abstract values: the traces of threads `0`, `1` and the pending messages of `0`. -/
abbrev CIVal := List (Option Val) × List (Option Val) × List Msg

/-- `α`. -/
def ciAlpha (G : Graph VPred) : CIVal := (G.trace 0, G.trace 1, G.pend 0)

/-- The local states of a value. -/
def ciU (b : CIVal) (t : Tid) : List (Option Val) :=
  if t = 0 then b.1 else if t = 1 then b.2.1 else []

/-- The seed words of a value. -/
def ciW (b : CIVal) (t : Tid) : List Msg := if t = 0 then b.2.2 else []

/-- `b ⊙ H` (lem:p2p-compose (1), (2)). -/
def ciF (b : CIVal) (H : Graph VPred) : CIVal :=
  (b.1 ++ (H.trace 0).drop (ciW b 0).length, b.2.1 ++ (H.trace 1).drop (ciW b 1).length,
    H.pend 0)

/-- `Bad`: thread `1` has performed two events. -/
def ciBad : Set (Graph VPred) := {G | 2 ≤ (G.trace 1).length}

/-- `Abad`. -/
def ciAbad (b : CIVal) : Bool := decide (2 ≤ b.2.1.length)

/-! ### The hypotheses -/

theorem ci_pend1 {G : Graph VPred} (hG : ExecM Model.p2p ciProg G) : G.pend 1 = [] := by
  refine ci_pend_eq_nil ((Model.p2p (Q := VPred)).wf _ hG.2) fun s hs h => ?_
  obtain ⟨hsG, hS, -⟩ := (G.mem_US).mp hs
  have := ci_send_tid (hG.1 s hsG) hS
  rw [h] at this
  cases this

theorem ci_hconf : ∀ G, ExecM Model.p2p ciProg G →
    (∀ t ∈ ciProg.threads, FutEq (ciProg.step t) (ciU (ciAlpha G) t) (G.trace t)) ∧
      ∀ t, ciW (ciAlpha G) t = G.pend t := fun G hG => by
  refine ⟨fun t ht => ?_, fun t => ?_⟩
  · have h01 : t = 0 ∨ t = 1 := by simpa [ciProg] using ht
    have : ciU (ciAlpha G) t = G.trace t := by rcases h01 with rfl | rfl <;> rfl
    rw [this]
    exact fun _ => rfl
  · by_cases ht : t = 0
    · subst ht
      rfl
    · simp only [ciW, ht, ↓reduceIte]
      by_cases h1 : t = 1
      · subst h1
        exact (ci_pend1 hG).symm
      · exact (pend_nil ((Model.p2p (Q := VPred)).wf _ hG.2) hG.1
          (by change t ∉ [0, 1]; simp [ht, h1])).symm

theorem ci_hdet : ∀ G, ExecM Model.p2p ciProg G → (G ∈ ciBad ↔ ciAbad (ciAlpha G) = true) :=
  fun G _ => by
    change 2 ≤ (G.trace 1).length ↔ decide (2 ≤ (G.trace 1).length) = true
    exact decide_eq_true_iff.symm

theorem ci_hext : ∀ G G', ExecM Model.p2p ciProg G → ExecM Model.p2p ciProg G' →
    G ∈ ciBad → G.IsPrefixOf G' → G' ∈ ciBad := fun G G' _ _ hb hp => by
  change 2 ≤ (G'.trace 1).length
  change 2 ≤ (G.trace 1).length at hb
  unfold Graph.trace at hb ⊢
  rw [traceBefore_length] at hb ⊢
  exact le_trans hb (cnt_le_of_isPrefixOf hp 1)

theorem ci_hf (B : List CIVal) (K : ℕ) : ∀ G, ExecM Model.p2p ciProg G → ciAlpha G ∈ B →
    ∀ H, Frag Model.p2p (ciProg.p2pRes .p2p G.trace G.pend) G.pend H →
      H.len ciProg.threads G.pend ≤ K → ciF (ciAlpha G) H = ciAlpha (compP2P G H) := by
  intro G hG _ H hH _
  have h2 := (p2p_compose_2 (p2pSetting ciProg ciProg_tagged) rfl hG hH).2.2
  have h1 := (p2p_compose_1 (p2pSetting ciProg ciProg_tagged) rfl trivial hG hH).2.2.2.2.2
  unfold ciAlpha ciF
  rw [h2 0, h2 1, h1 0]
  simp [ciW, ci_pend1 hG]

/-! ### The values, the run, the end theorem -/

/-- The values: nothing done; the send done; the receive done. -/
def ciB : List CIVal := [([], [], []), ([none], [], [(1, 5)]), ([none], [some 5], [])]

theorem ci_hinit : ciAlpha Graph.empty ∈ ciB := by decide +kernel

theorem ci_hdisj : ∀ b ∈ ciB, ciAbad b = false := by decide

/-- The run: accepted, six tests. -/
theorem ci_check : CheckS Graph.consAPB Sel.least 100 (p2pSetting ciProg ciProg_tagged) ciB
    ciAbad ciU ciW ciF 1 = (true, 6) := by decide +kernel

/-- `ciB` is `1`-inductive. -/
theorem ci_kind : (p2pAbs (p2pSetting ciProg ciProg_tagged) rfl trivial ciAlpha ciU ciW
    ci_hconf).KInductive {a | ciAbad a = true} {a | a ∈ ciB} 1 :=
  checkP2P_kinductive (hconf := ci_hconf) ciProg_tagged ci_hdet ci_hext ci_hinit ci_hdisj le_rfl
    (ci_hf ciB 1) 100 (congrArg Prod.fst ci_check)

/-- The end theorem on this instance: thread `1` never performs a second event (its error). -/
theorem ci_safe : Safe Model.p2p ciProg ciBad :=
  checkP2P_sound ciProg ciProg_tagged Sel.least ciAlpha ciU ciW ci_hconf ciBad ciAbad ci_hdet
    ci_hext ciB ci_hinit ci_hdisj 1 le_rfl ciF (ci_hf ciB 1) 100 (congrArg Prod.fst ci_check)

end CheckInst

end Ind

end Must
