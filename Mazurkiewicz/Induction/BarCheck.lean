import Mazurkiewicz.Induction.Bars

/-!
# Checking a bar-inductive set

`induction-popl`, `cuts.tex`, cor:barfinite, for plain programs under SC.

* `safe_of_bar_obligations`: the soundness half of cor:barfinite, with the
  paper's two tests on the reachable graphs of size at most `N + 1` of the
  programs `Q^b`.
* `CheckBar` (not in the paper, which states decidability): an executable,
  sound, bounded checker. For every `b ∈ B` it rejects if the initial graph
  of `Q^b` is in the bar; otherwise it traverses, depth-first, the
  derivations by maximal steps of `Q^b` from the initial graph, on
  configurations, with fuel `N`: at a graph outside the bar it tests
  `f b H ∉ Abad`; a successor in the bar is tested for `f b H' ∈ B` and not
  extended; a graph outside the bar that has a successor and no fuel is
  rejected. It returns the verdict and the number of visited graphs (one per
  graph of a visited derivation; a graph reached by two derivations is
  counted twice). In an accepting run this is the number of tests; a graph
  rejected for lack of fuel is counted without a test.
* `checkBar_sound`: acceptance gives the path form of a bar-inductive set
  (`Abstraction.BarInductivePath`), hence safety. No depth hypothesis.
-/

namespace Trust

open Program

variable {P : Program} {A : Type}

/-! ### cor:barfinite, soundness half -/

namespace Abstraction

variable (Abs : Abstraction P A)

/-- cor:barfinite, the soundness half. -/
theorem safe_of_bar_obligations {Bad : Set Graph} {Abad B : Set A} {Bar : A → Set Graph} {N : ℕ}
    (hdet : Abs.Determines Bad Abad) (hinit : Abs.α (Graph.init P.mem) ∈ B)
    (h0 : ∀ b ∈ B, Graph.init (Abs.μ b) ∉ Bar b)
    (hd : ∀ b ∈ B, DepthLe (Abs.res b) (Bar b) N)
    (f : A → Graph → A)
    (hf : ∀ G, ExecSC P G → Abs.α G ∈ B → ∀ H, GReach (P.residual G.trace G.memOf) SC H →
      H.size ≤ N + 1 → f (Abs.α G) H = Abs.α (G.comp H))
    (hobl : ∀ b ∈ B, ∀ H, GReach (Abs.res b) SC H → H.size ≤ N + 1 →
      (H ∈ boundary (Abs.res b) (Bar b) → f b H ∈ B) ∧ (H ∉ Bar b → f b H ∉ Abad)) :
    Safe P SC Bad := by
  refine Abs.barsound (Bar := Bar) hdet ⟨hinit, fun G hG hα => ?_⟩
  have hres := Abs.res_eq hG
  have hμ : Abs.μ (Abs.α G) = G.memOf := (Abs.hconf G hG).2
  rw [← hres, ← hμ]
  refine ⟨h0 _ hα, fun H hH => ?_, fun H hH hout => ?_⟩
  · have hsz := (hd _ hα).boundary_size_le hH
    rw [← hf G hG hα H (hres ▸ hH.2.1) hsz]
    exact ((hobl _ hα) H hH.2.1 hsz).1 hH
  · have hsz : H.size ≤ N + 1 := Nat.le_succ_of_le ((hd _ hα).size_le hH hout)
    rw [← hf G hG hα H (hres ▸ hH) hsz]
    exact ((hobl _ hα) H hH hsz).2 hout

end Abstraction

/-! ### Maximal steps on configurations -/

/-- The maximal extension of a configuration by the event `e`. -/
def Config.addMaxC (c : Config) (e : TEv) : Config :=
  match e.act with
  | .read x => c.addRead e (c.abs.maxWrite x)
  | .write _ _ => c.addWrite e (c.abs.maxWrite e.loc)

theorem Config.addMaxC_abs (c : Config) (e : TEv) : (c.addMaxC e).abs = c.abs.addMax e := by
  unfold Config.addMaxC Graph.addMax
  cases e.act with
  | read x => exact Config.addRead_abs c e _
  | write x v => exact Config.addWrite_abs c e _

theorem Config.addMaxC_order (c : Config) (e : TEv) : (c.addMaxC e).order = e :: c.order := by
  unfold Config.addMaxC
  cases e.act <;> rfl

theorem Config.addMaxC_wf {c : Config} (hc : c.Wf) {e : TEv} (hidx : e.idx = c.abs.cnt e.tid) :
    (c.addMaxC e).Wf := by
  refine ⟨?_, ?_⟩
  · rw [Config.addMaxC_abs]
    exact hc.1.addMax hidx
  · rw [Config.addMaxC_order]
    refine List.nodup_cons.mpr ⟨fun h => ?_, hc.2⟩
    exact hc.1.not_mem_of_idx_eq_cnt hidx (List.mem_toFinset.mpr h)

/-- The maximal step of thread `t`, computed. -/
def stepC (Q : Program) (c : Config) (t : Tid) : Option Config :=
  (Q.step t (c.trace t)).map (fun a => c.addMaxC ⟨t, c.cnt t, a⟩)

/-- The configurations after one maximal step. -/
def succC (Q : Program) (c : Config) : List Config := Q.threads.filterMap (stepC Q c)

theorem mstep_of_stepC {Q : Program} {c c' : Config} {t : Tid} (hc : c.Wf)
    (hE : ExecSC Q c.abs) (ht : t ∈ Q.threads) (h : stepC Q c t = some c') :
    MStep Q t c.abs c'.abs ∧ c'.Wf := by
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
  have hidx : (⟨t, c.cnt t, a⟩ : TEv).idx = c.abs.cnt (⟨t, c.cnt t, a⟩ : TEv).tid :=
    Config.cnt_eq c hc t
  refine ⟨mstep_iff.mpr ⟨hE, ⟨t, c.cnt t, a⟩, mem_avail_iff.mpr ⟨ht, hidx, ?_⟩, rfl,
    Config.addMaxC_abs c _⟩, Config.addMaxC_wf hc hidx⟩
  rw [← Config.trace_eq c hc]
  exact ha

theorem stepC_of_mstep {Q : Program} {c : Config} {t : Tid} {H' : Graph} (hc : c.Wf)
    (h : MStep Q t c.abs H') : ∃ c', c' ∈ succC Q c ∧ c'.abs = H' := by
  obtain ⟨a, ht, ha, rfl⟩ := h.new_event
  refine ⟨c.addMaxC ⟨t, c.cnt t, a⟩, List.mem_filterMap.mpr ⟨t, ht, ?_⟩, ?_⟩
  · unfold stepC
    rw [Config.trace_eq c hc, ha]
    rfl
  · rw [Config.addMaxC_abs, Config.cnt_eq c hc]

theorem mem_succC {Q : Program} {c c' : Config} (hc : c.Wf) (hE : ExecSC Q c.abs)
    (h : c' ∈ succC Q c) : ∃ t, MStep Q t c.abs c'.abs ∧ c'.Wf := by
  obtain ⟨t, ht, hs⟩ := List.mem_filterMap.mp h
  exact ⟨t, mstep_of_stepC hc hE ht hs⟩

/-! ### The traversal -/

/-- A fold that collects a conjunction and a count. -/
def foldAnd {α : Type} (g : α → Bool × ℕ) (l : List α) (a : Bool × ℕ) : Bool × ℕ :=
  l.foldl (fun acc x => ((g x).1 && acc.1, acc.2 + (g x).2)) a

theorem foldAnd_fst {α : Type} (g : α → Bool × ℕ) (l : List α) (a : Bool × ℕ) :
    (foldAnd g l a).1 = (l.all (fun x => (g x).1) && a.1) := by
  unfold foldAnd
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, List.all_cons]
    cases (g x).1 <;> cases l.all (fun x => (g x).1) <;> cases a.1 <;> rfl

theorem foldAnd_true {α : Type} {g : α → Bool × ℕ} {l : List α} {a : Bool × ℕ}
    (h : (foldAnd g l a).1 = true) : a.1 = true ∧ ∀ x ∈ l, (g x).1 = true := by
  rw [foldAnd_fst, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.2, h.1⟩

/-- The traversal from a configuration outside the bar, with fuel `n`:
`ok3` is the test outside the bar, `ok2` the test on entering it. -/
def visit (Q : Program) (barB ok3 ok2 : Graph → Bool) : ℕ → Config → Bool × ℕ
  | 0, c => if (succC Q c).isEmpty then (ok3 c.abs, 1) else (false, 1)
  | n + 1, c =>
    foldAnd (fun c' => if barB c'.abs then (ok2 c'.abs, 1) else visit Q barB ok3 ok2 n c')
      (succC Q c) (ok3 c.abs, 1)

/-- The procedure: for every `b ∈ B`, the initial graph of `Q^b` is outside
the bar and the traversal with fuel `N` succeeds. -/
def CheckBar [DecidableEq A] (P : Program) (B : List A) (abad : A → Bool)
    (u : A → Tid → List (Option Val)) (μ : A → Loc → Val) (f : A → Graph → A)
    (barB : A → Graph → Bool) (N : ℕ) : Bool × ℕ :=
  foldAnd (fun b =>
    if barB b (Graph.init (μ b)) then (false, 0)
    else visit (P.residual (u b) (μ b)) (barB b) (fun H => !abad (f b H))
      (fun H => decide (f b H ∈ B)) N (Config.init (μ b))) B (true, 0)

/-- `H` is reached from `H₀` by maximal steps whose targets are outside `X`. -/
inductive OutFrom (Q : Program) (X : Set Graph) : Graph → Graph → Prop
  | refl (H : Graph) : OutFrom Q X H H
  | head {H H₁ H₂ : Graph} {t : Tid} :
      MStep Q t H H₁ → H₁ ∉ X → OutFrom Q X H₁ H₂ → OutFrom Q X H H₂

theorem OutFrom.tail {Q : Program} {X : Set Graph} {H₀ H H' : Graph} {t : Tid}
    (h : OutFrom Q X H₀ H) (hs : MStep Q t H H') (hout : H' ∉ X) : OutFrom Q X H₀ H' := by
  induction h with
  | refl H => exact .head hs hout (.refl _)
  | head hs₁ hout₁ _ ih => exact .head hs₁ hout₁ (ih hs)

theorem OutsidePath.outFrom {Q : Program} {X : Set Graph} {H : Graph}
    (h : OutsidePath Q X H) : OutFrom Q X (Graph.init Q.mem) H := by
  induction h with
  | init _ => exact .refl _
  | step _ hs hout ih => exact ih.tail hs hout

/-- What an accepting traversal has tested. -/
theorem visit_spec (Q : Program) (barB ok3 ok2 : Graph → Bool) (n : ℕ) :
    ∀ c : Config, (visit Q barB ok3 ok2 n c).1 = true → c.Wf → ExecSC Q c.abs →
      ∀ H, OutFrom Q {H | barB H = true} c.abs H →
        ok3 H = true ∧ H.size ≤ c.abs.size + n ∧
          ∀ t H', MStep Q t H H' → barB H' = true →
            ok2 H' = true ∧ H'.size ≤ c.abs.size + n := by
  induction n with
  | zero =>
    intro c hv hc hE H hH
    have hemp : (succC Q c).isEmpty = true ∧ ok3 c.abs = true := by
      unfold visit at hv
      cases hs : (succC Q c).isEmpty with
      | true => rw [hs] at hv; exact ⟨rfl, hv⟩
      | false => rw [hs] at hv; cases hv
    have hno : ∀ t H', ¬ MStep Q t c.abs H' := by
      intro t H' hs
      obtain ⟨c', hc', -⟩ := stepC_of_mstep hc hs
      rw [List.isEmpty_iff.mp hemp.1] at hc'
      cases hc'
    cases hH with
    | refl => exact ⟨hemp.2, Nat.le_refl _, fun t H' hs _ => absurd hs (hno t H')⟩
    | head hs _ _ => exact absurd hs (hno _ _)
  | succ n ih =>
    intro c hv hc hE H hH
    unfold visit at hv
    obtain ⟨h3, hall⟩ := foldAnd_true hv
    cases hH with
    | refl =>
      refine ⟨h3, Nat.le_add_right _ _, fun t H' hs hbar => ?_⟩
      obtain ⟨c', hc', rfl⟩ := stepC_of_mstep hc hs
      have := hall c' hc'
      rw [ite_eq_left_of_eq_true _ _ (eq_true hbar)] at this
      have hsz := hs.size
      exact ⟨this, by omega⟩
    | head hs hout hrest =>
      obtain ⟨c', hc', rfl⟩ := stepC_of_mstep hc hs
      have hv' := hall c' hc'
      have hnb : ¬ (barB c'.abs = true) := hout
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnb)] at hv'
      obtain ⟨t', hs', hW'⟩ := mem_succC hc hE hc'
      obtain ⟨r3, rsz, r2⟩ := ih c' hv' hW' hs'.execSC_right H hrest
      have hsz := hs.size
      refine ⟨r3, by omega, fun t H' hst hbar => ?_⟩
      obtain ⟨q2, qsz⟩ := r2 t H' hst hbar
      exact ⟨q2, by omega⟩

namespace Abstraction

variable (Abs : Abstraction P A)

/-- An accepting run of `CheckBar` gives a bar-inductive set in the path form. -/
theorem checkBar_path [DecidableEq A] {abad : A → Bool} {B : List A}
    (hinit : Abs.α (Graph.init P.mem) ∈ B) (f : A → Graph → A) {barB : A → Graph → Bool} {N : ℕ}
    (hf : ∀ G, ExecSC P G → Abs.α G ∈ B → ∀ H, GReach (P.residual G.trace G.memOf) SC H →
      H.size ≤ N + 1 → f (Abs.α G) H = Abs.α (G.comp H))
    (hacc : (CheckBar P B abad Abs.u Abs.μ f barB N).1 = true) :
    Abs.BarInductivePath {a | abad a = true} {a | a ∈ B} (fun b => {H | barB b H = true}) := by
  refine ⟨hinit, fun G hG hα => ?_⟩
  have hres : P.residual (Abs.u (Abs.α G)) (Abs.μ (Abs.α G)) = P.residual G.trace G.memOf :=
    Abs.res_eq hG
  have hμ : Abs.μ (Abs.α G) = G.memOf := (Abs.hconf G hG).2
  have hb := (foldAnd_true hacc).2 (Abs.α G) hα
  have hroot : barB (Abs.α G) (Graph.init (Abs.μ (Abs.α G))) = false := by
    cases h : barB (Abs.α G) (Graph.init (Abs.μ (Abs.α G))) with
    | false => rfl
    | true => simp only [h, ite_true] at hb; cases hb
  simp only [hroot, Bool.false_eq_true, ite_false] at hb
  have hspec := visit_spec _ _ _ _ N _ hb (Config.init_wf _)
    (by rw [Config.init_abs]; exact execSC_init (P.residual (Abs.u (Abs.α G)) (Abs.μ (Abs.α G))))
  rw [Config.init_abs] at hspec
  have hsz0 : (Graph.init (Abs.μ (Abs.α G))).size = 1 := by simp [Graph.size, Graph.init]
  rw [hsz0, hres, hμ] at hspec
  rw [hμ] at hroot
  refine ⟨by simpa using hroot, fun H H' t hout hs hbar => ?_, fun H hout => ?_⟩
  · obtain ⟨-, -, h2⟩ := hspec H hout.outFrom
    obtain ⟨hok, hsz⟩ := h2 t H' hs hbar
    have := hf G hG hα H' (greach_iff.mpr hs.execSC_right) (by omega)
    rw [← this]
    exact of_decide_eq_true hok
  · obtain ⟨hok, hsz, -⟩ := hspec H hout.outFrom
    have := hf G hG hα H hout.greach (by omega)
    rw [← this]
    simpa using hok

/-- Soundness of `CheckBar`. -/
theorem checkBar_sound [DecidableEq A] {Bad : Set Graph} {abad : A → Bool}
    (hdet : Abs.Determines Bad {a | abad a = true}) {B : List A}
    (hinit : Abs.α (Graph.init P.mem) ∈ B) (f : A → Graph → A) {barB : A → Graph → Bool} {N : ℕ}
    (hf : ∀ G, ExecSC P G → Abs.α G ∈ B → ∀ H, GReach (P.residual G.trace G.memOf) SC H →
      H.size ≤ N + 1 → f (Abs.α G) H = Abs.α (G.comp H))
    (hacc : (CheckBar P B abad Abs.u Abs.μ f barB N).1 = true) : Safe P SC Bad :=
  Abs.barsound_path hdet (Abs.checkBar_path hinit f hf hacc)

end Abstraction

end Trust
