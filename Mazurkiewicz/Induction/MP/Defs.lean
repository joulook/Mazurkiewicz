import Mazurkiewicz.Must.ModelComb
import Mazurkiewicz.Must.Alg
import Mazurkiewicz.Must.Cons
import Mathlib.Data.Nat.Pairing

/-!
# Message passing: foundational definitions (Track C, milestone C0)

`induction-popl`, `mp.tex` and `p2p.tex`: the objects of Sections 6 and 7 that every later
file of Track C uses (plan `plan/ind/TRACK-C-PLAN.md`, Section 4 and milestone C0). The
graphs, labels, programs and models are those of the Must port (`Must/`).

* Messages, def:pending: `Msg`, `msgOf`; `Graph.pendM` is `pend(G)`; `IsPendEnum`, `word`
  are a pending enumeration and its word.
* def:p2p-frag: `Graph.pend G t` is `pend_t(G)`, the messages of the unread sends of `t` in
  index order. It is computable: the unread send at `(t, i)` is read through a code
  `Graph.sendCodeAt` (a `Finset.sup`, as `Graph.retAt` of the port); without an unread send at
  `(t, i)` the code is `0` and the position is skipped; on a malformed graph with several
  unread sends at `(t, i)` the largest code is taken (defined, not meaningful). On well-formed
  graphs it agrees with the event-valued selectors `Graph.unreadEvAt`, `Graph.unreadSeq`,
  `Graph.unreadAt` (`Graph.Wf.pend_eq`), which are noncomputable and used in proofs only.
* def:p2p: `Graph.soPaper` (`so` as printed: all sends, same thread and destination, smaller
  index), `Graph.P1`, `Graph.P2`.
* Tags: `Program.Tagged P m` (every send and receive label of `P` has model `m`),
  `Graph.SendsTagged`, `sendsTagged_of_exec`.
* Local states (def:state, copied from `Induction/States.lean` for the port's labels):
  `FutEq`, `futSetoid`, `StM`, `StM.mk`; the functions `h` of def:mp-abstraction (`hEnv`) and
  of def:p2p-frag (`hP2P`), proof-only.
* `ExecM M P G` is `G ∈ Exec_M(P)`; `BadErr` the graphs with an error event.
* def:env, def:p2p-frag (seeds): `envW` (`env_w`: the word `w` on the environment thread),
  `seedLab`, `seedEv` (the `j`-th seed event of thread `t` for the words `W`).
* `MPSetting`: one construction for Sections 6 and 7 (plan Section 4.1): the set of models
  `ms`, the order flag `ord`, the tag `m`, the program `P`, the idle seed threads `ι`; the
  three settings `envSetting` (Section 6), `p2pSetting` (Section 7), `p2pAsynSetting`
  (rem:p2p-scope (i)).

Namespaces: the definitions used with dot notation on the port's types are in `Must.Graph`,
`Must.Program`; the others in `Must.Ind`.
-/

namespace Must

variable {Q : Type} [DecidableEq Q]

/-! ### Messages -/

namespace Ind

/-- A message `(t, v)`: destination and value (def:pending). The model is not part of the
message; it is fixed by `Program.Tagged`. -/
abbrev Msg := Tid × Val

/-- The message of a send event (def:pending); `none` for the other events. -/
def msgOf (e : Ev Q) : Option Msg :=
  match e.lab with
  | .send _ d v => some (d, v)
  | _ => none

/-- The code of an optional message: `none ↦ 0`, `(d, v) ↦ pair d v + 1`. -/
def encM : Option Msg → ℕ
  | none => 0
  | some (d, v) => Nat.pair d v + 1

/-- The inverse of `encM`. -/
def decM : ℕ → Option Msg
  | 0 => none
  | n + 1 => some (Nat.unpair n)

omit [DecidableEq Q] in
theorem decM_encM (x : Option Msg) : decM (encM x) = x := by
  rcases x with _ | ⟨d, v⟩
  · rfl
  · simp [encM, decM, Nat.unpair_pair]

end Ind

open Ind

/-! ### Tags -/

/-- Every send and receive label of `P` has the model `m` (plan Section 4.2: the tag of the
program; labels of the paper carry no model). -/
def Program.Tagged (P : Program Q) (m : Comm) : Prop :=
  ∀ t u l, P.step t u = some l → l.model? = none ∨ l.model? = some m

/-- Every send of `G` has the model `m`. -/
def Graph.SendsTagged (G : Graph Q) (m : Comm) : Prop :=
  ∀ e ∈ G.events, e.IsSend → e.lab.model? = some m

namespace Ind

omit [DecidableEq Q] in
/-- The sends of an execution of a program tagged by `m` have the model `m`. -/
theorem sendsTagged_of_exec {P : Program Q} {G : Graph Q} {m : Comm} (hP : P.Tagged m)
    (hE : P.Exec G) : G.SendsTagged m := by
  intro e he hs
  rcases hP _ _ _ (hE e he) with h | h
  · obtain ⟨m', d, v, hl⟩ := (Lab.isSend_iff e.lab).mp hs
    rw [hl] at h
    cases h
  · exact h

end Ind

namespace Graph

/-! ### `so` and (P1), (P2) as printed (def:p2p) -/

/-- `G.so` of def:p2p: sends of `G` (of any model) with the same thread and the same
destination, the first with the smaller index. -/
def soPaper (G : Graph Q) (a b : Ev Q) : Prop :=
  a ∈ G.events ∧ b ∈ G.events ∧ a.IsSend ∧ b.IsSend ∧ a.tid = b.tid ∧
    Graph.dstOf a.lab = Graph.dstOf b.lab ∧ a.idx < b.idx

variable [Membership Val Q]

/-- (P1) of def:p2p. -/
def P1 (G : Graph Q) : Prop :=
  ∀ s' ∈ G.US, ∀ s r, G.soPaper s' s → G.rf r = some (.snd s) → ¬ s'.Matches r

/-- (P2) of def:p2p. -/
def P2 (G : Graph Q) : Prop :=
  ∀ r r' s s', G.po r r' → G.rf r' = some (.snd s') → G.soPaper s' s →
    G.rf r = some (.snd s) → ¬ s'.Matches r

end Graph

/-! ### Pending messages -/

namespace Graph

/-- `pend(G)` (def:pending): the multiset of the messages of the unread sends. -/
def pendM (G : Graph Q) : Multiset Msg := G.US.val.filterMap msgOf

/-- The code of the message of the unread send `(t, i)` of `G`; `0` if there is none. -/
def sendCodeAt (G : Graph Q) (t i : ℕ) : ℕ :=
  (G.events.filter fun e => e.tid = t ∧ e.idx = i ∧ e ∈ G.US).sup fun e => encM (msgOf e)

/-- `pend_t(G)` (def:p2p-frag): the messages of the unread sends of `t`, in index order.
Computable. -/
def pend (G : Graph Q) (t : Tid) : List Msg :=
  (List.range (G.cnt t)).filterMap fun i => decM (G.sendCodeAt t i)

/-- The unread send `(t, i)` of `G`, if there is one (specification only). -/
noncomputable def unreadEvAt (G : Graph Q) (t i : ℕ) : Option (Ev Q) :=
  open Classical in
  if h : ∃ e ∈ G.US, e.tid = t ∧ e.idx = i then some (Classical.choose h) else none

/-- The unread sends of `t`, in index order (specification only). -/
noncomputable def unreadSeq (G : Graph Q) (t : Tid) : List (Ev Q) :=
  (List.range (G.cnt t)).filterMap (G.unreadEvAt t)

/-- `s^t_{j+1}`: the `j`-th unread send of `t`, from `0` (specification only). -/
noncomputable def unreadAt (G : Graph Q) (t j : ℕ) : Option (Ev Q) := (G.unreadSeq t)[j]?

variable [Membership Val Q] {G : Graph Q}

/-- On a well-formed graph the code at the identity of an unread send is the code of its
message. -/
theorem Wf.sendCodeAt_eq (hG : G.Wf) {e : Ev Q} (he : e ∈ G.US) :
    G.sendCodeAt e.tid e.idx = encM (msgOf e) := by
  have hf : (G.events.filter fun e' => e'.tid = e.tid ∧ e'.idx = e.idx ∧ e' ∈ G.US) = {e} := by
    ext e'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2, h3, -⟩
      exact hG.idx_inj e' h1 e ((G.mem_US).mp he).1 h2 h3
    · rintro rfl
      exact ⟨((G.mem_US).mp he).1, rfl, rfl, he⟩
  unfold sendCodeAt
  rw [hf, Finset.sup_singleton]

/-- Without an unread send at `(t, i)` the code is `0`. (The well-formedness premise of the
plan is not needed; it is kept for the dot notation.) -/
theorem Wf.sendCodeAt_zero (_hG : G.Wf) {t i : ℕ} (h : ∀ e ∈ G.US, ¬ (e.tid = t ∧ e.idx = i)) :
    G.sendCodeAt t i = 0 := by
  have hf : (G.events.filter fun e => e.tid = t ∧ e.idx = i ∧ e ∈ G.US) = ∅ := by
    ext e
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    exact fun _ h1 h2 h3 => h e h3 ⟨h1, h2⟩
  unfold sendCodeAt
  rw [hf, Finset.sup_empty]
  rfl

/-- On a well-formed graph the selector at the identity of an unread send is that send. -/
theorem Wf.unreadEvAt_eq (hG : G.Wf) {e : Ev Q} (he : e ∈ G.US) :
    G.unreadEvAt e.tid e.idx = some e := by
  have hex : ∃ e' ∈ G.US, e'.tid = e.tid ∧ e'.idx = e.idx := ⟨e, he, rfl, rfl⟩
  unfold unreadEvAt
  split
  · next h =>
    obtain ⟨h1, h2, h3⟩ := Classical.choose_spec h
    exact congrArg some (hG.idx_inj _ ((G.mem_US).mp h1).1 e ((G.mem_US).mp he).1 h2 h3)
  · exact absurd hex ‹_›

/-- Agreement of the computable `pend` with the event-valued selectors, on well-formed
graphs. -/
theorem Wf.pend_eq (hG : G.Wf) (t : Tid) : G.pend t = (G.unreadSeq t).filterMap msgOf := by
  unfold pend unreadSeq
  rw [List.filterMap_filterMap]
  refine List.filterMap_congr fun i _ => ?_
  by_cases hex : ∃ e ∈ G.US, e.tid = t ∧ e.idx = i
  · obtain ⟨e, he, rfl, rfl⟩ := hex
    rw [hG.sendCodeAt_eq he, hG.unreadEvAt_eq he, decM_encM]
    rfl
  · have h0 : G.sendCodeAt t i = 0 := hG.sendCodeAt_zero fun e he h => hex ⟨e, he, h⟩
    have hn : G.unreadEvAt t i = none := by
      unfold unreadEvAt
      split
      · exact absurd ‹_› hex
      · rfl
    rw [h0, hn]
    rfl

end Graph

namespace Ind

/-! ### Pending enumerations, words, seeds -/

/-- A pending enumeration of `G` (def:pending): every unread send exactly once. -/
def IsPendEnum (G : Graph Q) (σ : List (Ev Q)) : Prop := σ.Nodup ∧ ∀ s, s ∈ σ ↔ s ∈ G.US

/-- `word(σ)` (def:pending). -/
def word (σ : List (Ev Q)) : List Msg := σ.filterMap msgOf

/-- `env_w` (def:env): the word `w` on the environment thread `ν`, nothing elsewhere. -/
def envW (ν : Tid) (w : List Msg) : Tid → List Msg := fun t => if t = ν then w else []

/-- The label of the `j`-th seed event of thread `t` for the words `W`: the send of the `j`-th
message, `block` after the last. -/
def seedLab (m : Comm) (W : Tid → List Msg) (t j : ℕ) : Lab Q :=
  match (W t)[j]? with
  | some (d, v) => .send m d v
  | none => .block

/-- The `j`-th seed event of thread `t` for the words `W`. -/
def seedEv (m : Comm) (W : Tid → List Msg) (t j : ℕ) : Ev Q := ⟨t, j, seedLab m W t j⟩

/-! ### Local states -/

/-- Two traces of a sequential program are equivalent if every continuation gives the same
next label (def:state; `Induction/States.lean` for the port's labels). -/
def FutEq (p : List (Option Val) → Option (Lab Q)) (u u' : List (Option Val)) : Prop :=
  ∀ x, p (u ++ x) = p (u' ++ x)

/-- The setoid of `FutEq`. -/
def futSetoid (p : List (Option Val) → Option (Lab Q)) : Setoid (List (Option Val)) :=
  ⟨FutEq p, ⟨fun _ _ => rfl, fun h x => (h x).symm, fun h₁ h₂ x => (h₁ x).trans (h₂ x)⟩⟩

/-- The local states of a sequential program (def:state). -/
def StM (p : List (Option Val) → Option (Lab Q)) : Type := Quotient (futSetoid p)

/-- The local state of a trace. -/
def StM.mk (p : List (Option Val) → Option (Lab Q)) (u : List (Option Val)) : StM p :=
  Quotient.mk (futSetoid p) u

variable [Membership Val Q]

/-- `G ∈ Exec_M(P)`: a consistent execution of `P`. -/
def ExecM (M : Model Q) (P : Program Q) (G : Graph Q) : Prop := P.Exec G ∧ M.cons G

omit [Membership Val Q] in
/-- The graphs with an error event (`Bad_err`). -/
def BadErr : Set (Graph Q) := {G | ∃ e ∈ G.events, e.lab = .error}

/-! ### Settings -/

/-- One construction for Sections 6 and 7 (plan Section 4.1). -/
structure MPSetting (Q : Type) [DecidableEq Q] [Membership Val Q] where
  /-- the set of communication models -/
  ms : Comm → Prop
  /-- neither `cd` nor `mbox` -/
  hms : ¬ ms .cd ∧ ¬ ms .mbox
  /-- seeds keep their sender and index order -/
  ord : Prop
  /-- under `p2p` the order is kept -/
  hord : ms .p2p → ord
  /-- the one tag of the program -/
  m : Comm
  /-- the program -/
  P : Program Q
  /-- the program is tagged by `m` -/
  hP : P.Tagged m
  /-- idle threads that carry seeds -/
  ι : List Tid
  /-- the threads and the idle threads are distinct -/
  hι : (P.threads ++ ι).Nodup

/-- The threads of a setting: the threads of the program, then the idle seed threads. -/
def MPSetting.ts (S : MPSetting Q) : List Tid := S.P.threads ++ S.ι

omit [DecidableEq Q] [Membership Val Q] in
theorem nodup_env (P : Program Q) {ν : Tid} (hν : ν ∉ P.threads) : (P.threads ++ [ν]).Nodup :=
  List.nodup_append.mpr ⟨P.nodup, List.nodup_singleton ν, by
    intro a ha b hb h
    rw [List.mem_singleton] at hb
    subst hb h
    exact hν ha⟩

omit [DecidableEq Q] [Membership Val Q] in
theorem nodup_nil (P : Program Q) : (P.threads ++ []).Nodup := by
  rw [List.append_nil]
  exact P.nodup

/-- Section 6: model `asyn`, no order, one idle environment thread `ν`. -/
def envSetting (P : Program Q) (ν : Tid) (hν : ν ∉ P.threads) (hP : P.Tagged .asyn) :
    MPSetting Q :=
  ⟨(· = .asyn), by simp, False, by simp, .asyn, P, hP, [ν], nodup_env P hν⟩

/-- Section 7: model `p2p`, ordered seeds on the threads of the program. -/
def p2pSetting (P : Program Q) (hP : P.Tagged .p2p) : MPSetting Q :=
  ⟨(· = .p2p), by simp, True, fun _ => trivial, .p2p, P, hP, [], nodup_nil P⟩

/-- rem:p2p-scope (i): the construction of Section 7 under `asyn`. -/
def p2pAsynSetting (P : Program Q) (hP : P.Tagged .asyn) : MPSetting Q :=
  ⟨(· = .asyn), by simp, True, fun _ => trivial, .asyn, P, hP, [], nodup_nil P⟩

omit [Membership Val Q] in
/-- `h` of def:mp-abstraction: local states and `pend(G)`. Proof-only. -/
def hEnv (P : Program Q) (G : Graph Q) : ((t : Tid) → StM (P.step t)) × Multiset Msg :=
  (fun t => StM.mk (P.step t) (G.trace t), G.pendM)

omit [Membership Val Q] in
/-- `h` of def:p2p-frag: local states and `pend_t(G)` for every `t`. Proof-only. -/
def hP2P (P : Program Q) (G : Graph Q) : ((t : Tid) → StM (P.step t)) × (Tid → List Msg) :=
  (fun t => StM.mk (P.step t) (G.trace t), G.pend)

/-! ### Evaluation check -/

/-- Thread `0` sends `5` and `7` to thread `1`; thread `1` receives the first. -/
private def evalG : Graph VPred where
  events := {⟨0, 0, .send .asyn 1 5⟩, ⟨0, 1, .send .asyn 1 7⟩, ⟨1, 0, .recv ⟨.asyn, true⟩ .any⟩}
  rf := fun e => if e = ⟨1, 0, .recv ⟨.asyn, true⟩ .any⟩ then some (.snd ⟨0, 0, .send .asyn 1 5⟩)
    else none
  nd := fun _ => none

example : evalG.pend 0 = [(1, 7)] ∧ evalG.pend 1 = [] := by decide +kernel

example : decide (evalG.pendM = {(1, 7)}) = true := by decide +kernel

end Ind

end Must
