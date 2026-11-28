import Mazurkiewicz.Induction.MP.Machines

/-!
# ex:pingpong: program, abstraction, hypotheses (milestone C9a)

`induction-popl`, `mp.tex` ex:pingpong (mp:337-382), plan `plan/ind/TRACK-C-PLAN.md`,
milestone C9a. Threads `1`, `2`; environment thread `ν = 0`; all labels tagged `.asyn`; every
receive set is `VPred.any`.

* Thread `1` (`ppA`): `a₀` (send `1` to thread `2`; `a₁` on `⊥`), `a₁` (blocking receive; `a₀`
  on a value). Thread `2` (`ppC`): `c₀` (blocking receive; `c₁` on a value), `c₁` (non-blocking
  receive; `c₂` on `⊥`, `c_e` on a value), `c₂` (send `1` to thread `1`; `c₀` on `⊥`), `c_e`
  (error). All other cases go to `†` (no action). `pp`: the trace-function program (not
  bounded, not `ofCodes`).
* The abstraction `α = h` (`ppAlpha`): the two states and `pend(G)` as a multiset; `abad`
  (`ppAbad`): thread `2` in `†`; the representatives `ppU` (`a₀ ↦ []`, `a₁ ↦ [⊥]`, `c₀ ↦ []`,
  `c₁ ↦ [1]`, `c₂ ↦ [1, ⊥]`, `c_e ↦ [1, 1]`, `† ↦ [0]` resp. `[⊥]`); the seed word `ppWord`
  (sorted pending messages); `ppF` (`b ⊙ H`).
* The sets `ppB1 = [(a₀, c₀, ∅)]` and `ppB5` (`B₅` of mp:355).
* Hypotheses of `checkAsyn_sound`: `pp_hν`, `pp_tagged`, `pp_hconf`, `pp_hdet` (thread `2` in
  `†` iff an error event, by `badErr_iff`), `pp_hext`, `pp_hinit1`, `pp_hinit5`, `pp_hdisj1`,
  `pp_hdisj5`, `pp_hf` (by `mp_compose_2`, `mp_compose_3`, through `envF_hf`).
-/

namespace Must

namespace Ind

/-! ### The machines -/

/-- The states of thread `1`. -/
inductive PA
  | a0
  | a1
  | dead
  deriving DecidableEq, Repr

/-- The states of thread `2`. -/
inductive PC
  | c0
  | c1
  | c2
  | ce
  | dead
  deriving DecidableEq, Repr

/-- The actions of thread `1`. -/
def ppAAct : PA → Option (Lab VPred)
  | .a0 => some (.send .asyn 2 1)
  | .a1 => some (.recv ⟨.asyn, true⟩ .any)
  | .dead => none

/-- The transitions of thread `1`. -/
def ppANext : PA → Option Val → PA
  | .a0, none => .a1
  | .a1, some _ => .a0
  | _, _ => .dead

/-- The actions of thread `2`. -/
def ppCAct : PC → Option (Lab VPred)
  | .c0 => some (.recv ⟨.asyn, true⟩ .any)
  | .c1 => some (.recv ⟨.asyn, false⟩ .any)
  | .c2 => some (.send .asyn 1 1)
  | .ce => some .error
  | .dead => none

/-- The transitions of thread `2`. -/
def ppCNext : PC → Option Val → PC
  | .c0, some _ => .c1
  | .c1, none => .c2
  | .c1, some _ => .ce
  | .c2, none => .c0
  | _, _ => .dead

/-- Thread `1` of ex:pingpong. -/
def ppA : Mach VPred PA where
  s0 := .a0
  dead := .dead
  act := ppAAct
  next := ppANext
  act_dead := rfl
  next_dead _ := rfl
  stops s l h hs := by
    cases s <;> simp only [ppAAct, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      first | rfl | exact absurd hs id
  no_nd s S := by cases s <;> simp [ppAAct]

/-- Thread `2` of ex:pingpong. -/
def ppC : Mach VPred PC where
  s0 := .c0
  dead := .dead
  act := ppCAct
  next := ppCNext
  act_dead := rfl
  next_dead _ := rfl
  stops s l h hs := by
    cases s <;> simp only [ppCAct, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      first | rfl | exact absurd hs Bool.false_ne_true | exact absurd hs id
  no_nd s S := by cases s <;> simp [ppCAct]

/-- ex:pingpong: threads `[1, 2]`. -/
def pp : Program VPred := Mach.prog 1 2 (by decide) ppA ppC

theorem pp_threads : pp.threads = [1, 2] := rfl

/-- The environment thread is not a thread of the program. -/
theorem pp_hν : (0 : Tid) ∉ pp.threads := by decide

/-- Every label of `pp` is tagged `.asyn`. -/
theorem pp_tagged : pp.Tagged .asyn := by
  refine Mach.prog_tagged .asyn (fun s l h => ?_) (fun s l h => ?_)
  · cases s <;> simp only [ppA, ppAAct, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      simp [Lab.model?]
  · cases s <;> simp only [ppC, ppCAct, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      simp [Lab.model?]

/-! ### The abstraction -/

/-- The abstract values: states of the threads `1`, `2` and the pending messages. -/
abbrev PPVal := PA × PC × Multiset Msg

/-- `α = h` (def:mp-abstraction). -/
def ppAlpha (G : Graph VPred) : PPVal := envAlpha 1 2 ppA ppC G

/-- Representative traces of the states of thread `1`. -/
def ppRepA : PA → List (Option Val)
  | .a0 => []
  | .a1 => [none]
  | .dead => [some 0]

/-- Representative traces of the states of thread `2`. -/
def ppRepC : PC → List (Option Val)
  | .c0 => []
  | .c1 => [some 1]
  | .c2 => [some 1, none]
  | .ce => [some 1, some 1]
  | .dead => [none]

theorem ppRepA_st (s : PA) : ppA.st (ppRepA s) = s := by cases s <;> rfl

theorem ppRepC_st (s : PC) : ppC.st (ppRepC s) = s := by cases s <;> rfl

/-- The local states of an abstract value. -/
def ppU (b : PPVal) : Tid → List (Option Val) := repU 1 2 ppRepA ppRepC b

/-- The seed word of an abstract value. -/
def ppWord (b : PPVal) : List Msg := envWord b

/-- `b ⊙ H`. -/
def ppF (b : PPVal) (H : Graph VPred) : PPVal := envF 1 2 ppA ppC b H

/-- `Abad`: thread `2` in `†`. -/
def ppAbad (b : PPVal) : Bool := decide (b.2.1 = .dead)

/-- The request `p = (2, 1)`. -/
def ppReq : Msg := (2, 1)

/-- The reply `q = (1, 1)`. -/
def ppRep : Msg := (1, 1)

/-- `{(a₀, c₀, ∅)}` (mp:364). -/
def ppB1 : List PPVal := [(.a0, .c0, 0)]

/-- `B₅` (mp:355). -/
def ppB5 : List PPVal :=
  [(.a0, .c0, 0), (.a1, .c0, {ppReq}), (.a1, .c1, 0), (.a1, .c2, 0), (.a1, .c0, {ppRep})]

/-! ### The hypotheses of `checkAsyn_sound` -/

theorem pp_hconf : ∀ G, ExecM Model.asyn pp G →
    (∀ t ∈ pp.threads, FutEq (pp.step t) (ppU (ppAlpha G) t) (G.trace t)) ∧
      (↑(ppWord (ppAlpha G)) : Multiset Msg) = G.pendM :=
  envAlpha_hconf ppRepA_st ppRepC_st Model.asyn

/-- The invariant of mp:351: an execution has an error event iff thread `2` is in `†`. -/
theorem pp_hdet : ∀ G, ExecM Model.asyn pp G → (G ∈ BadErr ↔ ppAbad (ppAlpha G) = true) := by
  intro G hG
  have h := badErr_iff (Model.asyn.wf _ hG.2) hG.1
    (fun s => by cases s <;> simp [ppA, ppAAct])
    (fun s l r hs ha hn hv => by
      cases s <;> simp only [ppC, ppCAct, Option.some.injEq, reduceCtorEq] at ha <;> subst ha <;>
        cases r <;> simp_all [ppC, ppCNext, ValOK, Lab.IsSend, Lab.IsRecvB])
    (by decide : ppC.s0 ≠ ppC.dead)
  rw [h, ppAbad, decide_eq_true_eq]
  exact Iff.rfl

theorem pp_hext : ∀ G G', ExecM Model.asyn pp G → ExecM Model.asyn pp G' → G ∈ BadErr →
    G.IsPrefixOf G' → G' ∈ BadErr := fun _ _ _ _ hb hp => badErr_ext hb hp

theorem pp_hinit1 : ppAlpha Graph.empty ∈ ppB1 := by decide +kernel

theorem pp_hinit5 : ppAlpha Graph.empty ∈ ppB5 := by decide +kernel

theorem pp_hdisj1 : ∀ b ∈ ppB1, ppAbad b = false := by decide +kernel

theorem pp_hdisj5 : ∀ b ∈ ppB5, ppAbad b = false := by decide +kernel

/-- `hf` (lem:mp-compose (2), (3)). -/
theorem pp_hf {B : List PPVal} {K : ℕ} :
    ∀ G, ExecM Model.asyn pp G → ppAlpha G ∈ B → ∀ σ, IsPendEnum G σ →
      word σ = ppWord (ppAlpha G) →
      ∀ H, Frag Model.asyn (pp.envRes 0 pp_hν G.trace (word σ)) (envW 0 (word σ)) H →
        H.len (pp.threads ++ [0]) (envW 0 (word σ)) ≤ K →
        ppF (ppAlpha G) H = ppAlpha (compEnv G 0 σ H) :=
  envF_hf (A := {b | b ∈ B}) (K := K) pp_hν pp_tagged

end Ind

end Must
