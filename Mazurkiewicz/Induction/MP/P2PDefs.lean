import Mazurkiewicz.Induction.MP.Machines

/-!
# ex:p2p: programs, abstractions, hypotheses (milestone C10a)

`induction-popl`, `p2p.tex` ex:p2p (p2p:225-265), plan `plan/ind/TRACK-C-PLAN.md`, milestone
C10a. Threads `1`, `2`; every receive set is `VPred.any`.

* Thread `1` (`pqA m`): `a₀` (send `1` to thread `2`), `a₁` (send `2` to thread `2`), `a₂`
  (blocking receive; `a₀` on a value). Thread `2` (`pqC m`): `c₀` (blocking receive; `c₁` on
  `1`, `c_e` on another value), `c₁` (blocking receive; `c₂` on `2`, `c_e` on another value),
  `c₂` (send `0` to thread `1`), `c_e` (error); all other cases `†`. One constructor
  `pqProg m` parameterised by the tag `m`: `pq = pqProg .p2p` (Section 7), `pqa = pqProg .asyn`
  (Section 6, environment thread `ν = 0`).
* Section 7 (`pq`, `p2pSetting`): `α = h` (`pqAlpha`: the states and `pend_1(G)`, `pend_2(G)`),
  `pqU`, `pqW`, `pqF`, `pqAbad`, `pqB = [(a₀, c₀, ε, ε)]`; the hypotheses of `checkP2P_sound`:
  `pq_tagged`, `pq_hconf`, `pq_hdet`, `pq_hext`, `pq_hinit`, `pq_hdisj`, `pq_hf`.
* Section 6 (`pqa`, `envSetting pqa 0`): `pqa_tagged`, `pqa_hν` and the abstraction functions
  `pqaAlpha` (multiset pending), `pqaU`, `pqaWord`, `pqaF`, `pqaAbad`, `pqaB = [(a₀, c₀, ∅)]`,
  used by C10c (`P2PAsynExample.lean`), which also proves the hypotheses of `checkAsyn_sound`
  for them.
-/

namespace Must

namespace Ind

/-! ### The machines -/

/-- The states of thread `1`. -/
inductive QA
  | a0
  | a1
  | a2
  | dead
  deriving DecidableEq, Repr

/-- The states of thread `2`. -/
inductive QC
  | c0
  | c1
  | c2
  | ce
  | dead
  deriving DecidableEq, Repr

/-- The actions of thread `1`, tagged `m`. -/
def pqAAct (m : Comm) : QA → Option (Lab VPred)
  | .a0 => some (.send m 2 1)
  | .a1 => some (.send m 2 2)
  | .a2 => some (.recv ⟨m, true⟩ .any)
  | .dead => none

/-- The transitions of thread `1`. -/
def pqANext : QA → Option Val → QA
  | .a0, none => .a1
  | .a1, none => .a2
  | .a2, some _ => .a0
  | _, _ => .dead

/-- The actions of thread `2`, tagged `m`. -/
def pqCAct (m : Comm) : QC → Option (Lab VPred)
  | .c0 => some (.recv ⟨m, true⟩ .any)
  | .c1 => some (.recv ⟨m, true⟩ .any)
  | .c2 => some (.send m 1 0)
  | .ce => some .error
  | .dead => none

/-- The transitions of thread `2`: fail unless the first value is `1` and the second `2`. -/
def pqCNext : QC → Option Val → QC
  | .c0, some v => if v = 1 then .c1 else .ce
  | .c1, some v => if v = 2 then .c2 else .ce
  | .c2, none => .c0
  | _, _ => .dead

/-- Thread `1` of ex:p2p. -/
def pqA (m : Comm) : Mach VPred QA where
  s0 := .a0
  dead := .dead
  act := pqAAct m
  next := pqANext
  act_dead := rfl
  next_dead _ := rfl
  stops s l h hs := by
    cases s <;> simp only [pqAAct, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      first | rfl | exact absurd hs id
  no_nd s S := by cases s <;> simp [pqAAct]

/-- Thread `2` of ex:p2p. -/
def pqC (m : Comm) : Mach VPred QC where
  s0 := .c0
  dead := .dead
  act := pqCAct m
  next := pqCNext
  act_dead := rfl
  next_dead _ := rfl
  stops s l h hs := by
    cases s <;> simp only [pqCAct, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      first | rfl | exact absurd hs id
  no_nd s S := by cases s <;> simp [pqCAct]

/-- ex:p2p with the tag `m`: threads `[1, 2]`. -/
def pqProg (m : Comm) : Program VPred := Mach.prog 1 2 (by decide) (pqA m) (pqC m)

/-- ex:p2p under `p2p` (Section 7). -/
abbrev pq : Program VPred := pqProg .p2p

/-- ex:p2p under `asyn` (Section 6). -/
abbrev pqa : Program VPred := pqProg .asyn

theorem pqProg_tagged (m : Comm) : (pqProg m).Tagged m := by
  refine Mach.prog_tagged m (fun s l h => ?_) (fun s l h => ?_)
  · cases s <;> simp only [pqA, pqAAct, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      simp [Lab.model?]
  · cases s <;> simp only [pqC, pqCAct, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      simp [Lab.model?]

theorem pq_tagged : pq.Tagged .p2p := pqProg_tagged .p2p

theorem pqa_tagged : pqa.Tagged .asyn := pqProg_tagged .asyn

theorem pqa_hν : (0 : Tid) ∉ pqa.threads := by decide

/-! ### Common parts of the abstractions -/

/-- Representative traces of the states of thread `1`. -/
def pqRepA : QA → List (Option Val)
  | .a0 => []
  | .a1 => [none]
  | .a2 => [none, none]
  | .dead => [some 0]

/-- Representative traces of the states of thread `2`. -/
def pqRepC : QC → List (Option Val)
  | .c0 => []
  | .c1 => [some 1]
  | .c2 => [some 1, some 2]
  | .ce => [some 0]
  | .dead => [none]

theorem pqRepA_st (m : Comm) (s : QA) : (pqA m).st (pqRepA s) = s := by cases s <;> rfl

theorem pqRepC_st (m : Comm) (s : QC) : (pqC m).st (pqRepC s) = s := by cases s <;> rfl

/-- ex:p2p (p2p:236): an execution has an error event iff thread `2` is in `†`. -/
theorem pqProg_badErr {m : Comm} {G : Graph VPred} (hG : G.Wf) (hE : (pqProg m).Exec G) :
    G ∈ BadErr ↔ (pqC m).st (G.trace 2) = .dead :=
  badErr_iff hG hE
    (fun s => by cases s <;> simp [pqA, pqAAct])
    (fun s l r hs ha hn hv => by
      cases s <;> simp only [pqC, pqCAct, Option.some.injEq, reduceCtorEq] at ha <;> subst ha <;>
        cases r <;> simp_all [pqC, pqCNext, ValOK, Lab.IsSend, Lab.IsRecvB] <;> split at hn <;>
          cases hn)
    (by simp [pqC])

/-! ### Section 7: `pq` under `p2p` -/

/-- The abstract values: the states and `pend_1`, `pend_2`. -/
abbrev PQVal := QA × QC × List Msg × List Msg

/-- Decidable equality of the abstract values (spelled out: instance search does not find it for
this four-fold product). -/
instance : DecidableEq PQVal :=
  @instDecidableEqProd _ _ (inferInstance : DecidableEq QA)
    (@instDecidableEqProd _ _ (inferInstance : DecidableEq QC)
      (@instDecidableEqProd _ _ (inferInstance : DecidableEq (List Msg))
        (inferInstance : DecidableEq (List Msg))))

/-- `α = h` of Section 7. -/
def pqAlpha (G : Graph VPred) : PQVal := p2pAlpha 1 2 (pqA .p2p) (pqC .p2p) G

/-- The local states of an abstract value. -/
def pqU (b : PQVal) : Tid → List (Option Val) := repU 1 2 pqRepA pqRepC b

/-- The seed words of an abstract value. -/
def pqW (b : PQVal) : Tid → List Msg := p2pWords 1 2 b

/-- `b ⊙ H` of Section 7. -/
def pqF (b : PQVal) (H : Graph VPred) : PQVal := p2pF 1 2 (pqA .p2p) (pqC .p2p) b H

/-- `Abad`: thread `2` in `†`. -/
def pqAbad (b : PQVal) : Bool := decide (b.2.1 = .dead)

/-- `{(a₀, c₀, ε, ε)}` (p2p:239). -/
def pqB : List PQVal := [(.a0, .c0, [], [])]

theorem pq_hconf : ∀ G, ExecM Model.p2p pq G →
    (∀ t ∈ pq.threads, FutEq (pq.step t) (pqU (pqAlpha G) t) (G.trace t)) ∧
      ∀ t, pqW (pqAlpha G) t = G.pend t :=
  p2pAlpha_hconf (pqRepA_st .p2p) (pqRepC_st .p2p) Model.p2p

theorem pq_hdet : ∀ G, ExecM Model.p2p pq G → (G ∈ BadErr ↔ pqAbad (pqAlpha G) = true) := by
  intro G hG
  rw [pqProg_badErr (Model.p2p.wf _ hG.2) hG.1, pqAbad, decide_eq_true_eq]
  exact Iff.rfl

theorem pq_hext : ∀ G G', ExecM Model.p2p pq G → ExecM Model.p2p pq G' → G ∈ BadErr →
    G.IsPrefixOf G' → G' ∈ BadErr := fun _ _ _ _ hb hp => badErr_ext hb hp

theorem pq_hinit : pqAlpha Graph.empty ∈ pqB := by decide +kernel

theorem pq_hdisj : ∀ b ∈ pqB, pqAbad b = false := by decide +kernel

/-- `hf` of Section 7 (lem:p2p-compose (1), (2)). -/
theorem pq_hf {K : ℕ} :
    ∀ G, ExecM Model.p2p pq G → pqAlpha G ∈ pqB →
      ∀ H, Frag Model.p2p (pq.p2pRes .p2p G.trace G.pend) G.pend H →
        H.len pq.threads G.pend ≤ K → pqF (pqAlpha G) H = pqAlpha (compP2P G H) :=
  p2pF_hf (A := {b | b ∈ pqB}) (K := K) (p2pSetting pq pq_tagged) rfl trivial

/-! ### Section 6: `pqa` under `asyn` (the abstraction used in `P2PAsynExample.lean`) -/

/-- The abstract values of Section 6: the states and `pend(G)`. -/
abbrev PQAVal := QA × QC × Multiset Msg

/-- `α = h` of Section 6. -/
def pqaAlpha (G : Graph VPred) : PQAVal := envAlpha 1 2 (pqA .asyn) (pqC .asyn) G

/-- The local states of an abstract value. -/
def pqaU (b : PQAVal) : Tid → List (Option Val) := repU 1 2 pqRepA pqRepC b

/-- The seed word of an abstract value (sorted pending messages). -/
def pqaWord (b : PQAVal) : List Msg := envWord b

/-- `b ⊙ H` of Section 6. -/
def pqaF (b : PQAVal) (H : Graph VPred) : PQAVal := envF 1 2 (pqA .asyn) (pqC .asyn) b H

/-- `Abad`: thread `2` in `†`. -/
def pqaAbad (b : PQAVal) : Bool := decide (b.2.1 = .dead)

/-- `{(a₀, c₀, ∅)}`. -/
def pqaB : List PQAVal := [(.a0, .c0, 0)]

end Ind

end Must
