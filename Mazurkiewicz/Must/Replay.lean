import Mazurkiewicz.Must.Avail

/-!
# Canonical replay of a list, maximal steps, Lemmas A.10, A.11 (milestone M5)

Paper: Appendix A.3 (maximal steps), Definition A.5 (`MaxCompletion(G, A)`), Definition A.8
(`extensible`), Lemmas A.10, A.11 (p. 30). Plan: decisions Q9, Q10 (i), Q11, Section 2b;
reviews `M4-r1-opus.md` §5, `M4-r1-astra.md` 5 (the maximal steps are built on the unpremised
operational step `OpAdd₀`, so A.11 is a consequence of Axiom 2, not of a premise).

* `Canon tie G e src out` (Q10 (i)): the canonical source and outcome of `e` in `G`: a blocking
  receive reads the send of `G` whose identity `tie G e` returns, a non-blocking receive reads
  `⊥`, an ND event has outcome `min S`, every other event has neither.
* `CanonStep tie P G e G'`: `e` is the next event of its thread in `G` and `G'` adds it with its
  canonical source and outcome. `Replay tie P G l G'`: canonical replay of the supplied list
  `l` (`MaxCompletion(G, l)`, Q10 (i)).
* `MaxStep₀ M tie P G e G'` (A.3): an unpremised operational step (`OpAdd₀`) with the canonical
  source and outcome; `MaxStep` the same on the premised step `OpAdd`. `MaxChain`: a sequence of
  `MaxStep₀` along a list (Definition A.5).
* `Canon.cons` (Axiom 2 with Q9): adding the next event of a thread with its canonical source
  and outcome to a consistent graph gives a consistent graph. Hence A.11 (`maxStep₀_cons`), and
  the two readings of A.3 coincide on consistent graphs (`maxStep_iff_maxStep₀`).
* A.10 (`extensible`): every available event of a consistent graph has a maximal step.
* `replay_det`, `Replay.cons`, `Replay.exec`, `replay_exists` (existence under `Legal`: each
  listed event is available after the canonical replay of the earlier ones), `legal_iff`,
  `replay_iff_maxChain` (Q10 (i) is A.5's `MaxCompletion` on consistent executions).

Hypotheses: a model `M`, a tie-break `tie` with `TieQ9 M tie`, a program `P` (whose ND labels
have non-empty sets: the field `Program.nd_ne`). Every result holds for every model.
-/

namespace Must

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q} {tie : Tie Q}

/-! ### The least value -/

theorem minVal_mem {S : Finset Val} {v : Val} (h : minVal S = some v) : v ∈ S := by
  unfold minVal at h
  cases hm : S.min with
  | top => simp [Sel.ofTop, hm] at h
  | coe y =>
    have : Sel.ofTop S.min = some y := by rw [hm]; rfl
    rw [this, Option.some.injEq] at h
    subst h
    exact Finset.mem_of_min hm

theorem minVal_isSome {S : Finset Val} (h : S.Nonempty) : ∃ v, minVal S = some v := by
  obtain ⟨y, hy⟩ := Finset.min_of_nonempty h
  exact ⟨y, by unfold minVal; rw [hy]; rfl⟩

/-! ### Canonical source and outcome -/

/-- The canonical source and outcome of `e` in `G` (Q10 (i)). -/
def Canon (tie : Tie Q) (G : Graph Q) (e : Ev Q) (src : Option (Src Q)) (out : Option Val) :
    Prop :=
  if e.IsRecvB then
    ∃ s ∈ G.events, tie G e = some (s.tid, s.idx) ∧ src = some (.snd s) ∧ out = none
  else if e.IsRecvNB then src = some .bot ∧ out = none
  else if e.IsND then src = none ∧ ∃ v, minVal e.ndSet = some v ∧ out = some v
  else src = none ∧ out = none

/-- Add the next event `e` of its thread with its canonical source and outcome. -/
def CanonStep (tie : Tie Q) (P : Program Q) (G : Graph Q) (e : Ev Q) (G' : Graph Q) : Prop :=
  P.nextEv G e.tid = some e ∧ ∃ src out, Canon tie G e src out ∧ G' = G.add e src out

/-- Canonical replay of a supplied list (Q10 (i), Definition A.5's `MaxCompletion(G, l)`). -/
inductive Replay (tie : Tie Q) (P : Program Q) : Graph Q → List (Ev Q) → Graph Q → Prop
  /-- the empty list -/
  | nil (G : Graph Q) : Replay tie P G [] G
  /-- the head is added canonically, then the tail is replayed -/
  | cons {G G₁ G' : Graph Q} {e : Ev Q} {l : List (Ev Q)} :
      CanonStep tie P G e G₁ → Replay tie P G₁ l G' → Replay tie P G (e :: l) G'

/-- A maximal step (A.3, repaired by Q9, Q10 (i)): an unpremised operational step (`OpAdd₀`)
with the canonical source and outcome. -/
def MaxStep₀ (M : Model Q) (tie : Tie Q) (P : Program Q) (G : Graph Q) (e : Ev Q)
    (G' : Graph Q) : Prop :=
  ∃ src out, OpAdd₀ M P G e src out ∧ Canon tie G e src out ∧ G' = G.add e src out

/-- A maximal step on the premised operational step `OpAdd`. -/
def MaxStep (M : Model Q) (tie : Tie Q) (P : Program Q) (G : Graph Q) (e : Ev Q)
    (G' : Graph Q) : Prop :=
  ∃ src out, OpAdd M P G e src out ∧ Canon tie G e src out ∧ G' = G.add e src out

/-- `G ⇝^{e₁} ⋯ ⇝^{eₙ} G'` for the list `[e₁, …, eₙ]` (Definition A.5). -/
inductive MaxChain (M : Model Q) (tie : Tie Q) (P : Program Q) :
    Graph Q → List (Ev Q) → Graph Q → Prop
  /-- the empty list -/
  | nil (G : Graph Q) : MaxChain M tie P G [] G
  /-- a maximal step, then the rest -/
  | cons {G G₁ G' : Graph Q} {e : Ev Q} {l : List (Ev Q)} :
      MaxStep₀ M tie P G e G₁ → MaxChain M tie P G₁ l G' → MaxChain M tie P G (e :: l) G'

/-- Definition A.8: `e` is extensible in `G` if a maximal step adds it. -/
def Extensible (M : Model Q) (tie : Tie Q) (P : Program Q) (G : Graph Q) (e : Ev Q) : Prop :=
  ∃ G', MaxStep₀ M tie P G e G'

/-! ### Facts on `Canon` -/

variable {G G' : Graph Q} {e : Ev Q} {src : Option (Src Q)} {out : Option Val}

omit [DecidableEq Q] [Membership Val Q] in
theorem Canon.recvB (h : Canon tie G e src out) (hB : e.IsRecvB) :
    ∃ s ∈ G.events, tie G e = some (s.tid, s.idx) ∧ src = some (.snd s) ∧ out = none := by
  unfold Canon at h
  simpa [hB] using h

omit [DecidableEq Q] [Membership Val Q] in
theorem Canon.recvNB (h : Canon tie G e src out) (hNB : e.IsRecvNB) :
    src = some .bot ∧ out = none := by
  unfold Canon at h
  simpa [hNB, Lab.not_isRecvB_of_isRecvNB hNB] using h

omit [DecidableEq Q] [Membership Val Q] in
theorem Canon.nd (h : Canon tie G e src out) (hN : e.IsND) :
    src = none ∧ ∃ v, minVal e.ndSet = some v ∧ out = some v := by
  have h1 : ¬ e.IsRecvB := fun h' => Lab.IsND.not_isRecv hN (Lab.IsRecvB.isRecv h')
  have h2 : ¬ e.IsRecvNB := fun h' => Lab.IsND.not_isRecv hN (Lab.IsRecvNB.isRecv h')
  unfold Canon at h
  simpa [h1, h2, hN] using h

omit [DecidableEq Q] [Membership Val Q] in
theorem Canon.other (h : Canon tie G e src out) (hR : ¬ e.IsRecv) (hN : ¬ e.IsND) :
    src = none ∧ out = none := by
  have h1 : ¬ e.IsRecvB := fun h' => hR (Lab.IsRecvB.isRecv h')
  have h2 : ¬ e.IsRecvNB := fun h' => hR (Lab.IsRecvNB.isRecv h')
  unfold Canon at h
  simpa [h1, h2, hN] using h

omit [DecidableEq Q] [Membership Val Q] in
/-- Introduction of `Canon`, by cases on the label. -/
theorem Canon.intro
    (hB : e.IsRecvB → ∃ s ∈ G.events, tie G e = some (s.tid, s.idx) ∧ src = some (.snd s) ∧
      out = none)
    (hNB : e.IsRecvNB → src = some .bot ∧ out = none)
    (hN : e.IsND → src = none ∧ ∃ v, minVal e.ndSet = some v ∧ out = some v)
    (hO : ¬ e.IsRecv → ¬ e.IsND → src = none ∧ out = none) : Canon tie G e src out := by
  unfold Canon
  split_ifs with h1 h2 h3
  · exact hB h1
  · exact hNB h2
  · exact hN h3
  · refine hO (fun hR => ?_) h3
    rcases Lab.IsRecv.recvB_or_recvNB hR with h | h
    · exact h1 h
    · exact h2 h

/-- The send chosen by a tie-break with Q9 is the send of the graph with that identity. -/
theorem TieQ9.send_mem (hT : TieQ9 M tie) (hG : G.Wf) {s : Ev Q} (hs : s ∈ G.events)
    (ht : tie G e = some (s.tid, s.idx)) : s ∈ G.S ∧ M.cons (G.addRecv e (.snd s)) := by
  obtain ⟨s', hs', hc, hid⟩ := hT.1 G e _ hG.supp ht
  rw [Prod.mk.injEq] at hid
  have := hG.idx_inj s' ((Graph.mem_S _).mp hs').1 s hs hid.1 hid.2
  subst this
  exact ⟨hs', hc⟩

omit [DecidableEq Q] in
/-- The canonical source and outcome are unique in a well-formed graph. -/
theorem Canon.unique (hG : G.Wf) {src' : Option (Src Q)} {out' : Option Val}
    (h : Canon tie G e src out) (h' : Canon tie G e src' out') : src = src' ∧ out = out' := by
  rcases Lab.cases_lab e.lab with hR | hS | hN | hL
  · rcases Lab.IsRecv.recvB_or_recvNB hR with hB | hNB
    · obtain ⟨s, hs, ht, rfl, rfl⟩ := h.recvB hB
      obtain ⟨s', hs', ht', rfl, rfl⟩ := h'.recvB hB
      rw [ht, Option.some.injEq, Prod.mk.injEq] at ht'
      rw [hG.idx_inj s hs s' hs' ht'.1 ht'.2]
      exact ⟨rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := h.recvNB hNB
      obtain ⟨rfl, rfl⟩ := h'.recvNB hNB
      exact ⟨rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := h.other (Lab.IsSend.not_isRecv hS) (Lab.IsSend.not_isND hS)
    obtain ⟨rfl, rfl⟩ := h'.other (Lab.IsSend.not_isRecv hS) (Lab.IsSend.not_isND hS)
    exact ⟨rfl, rfl⟩
  · obtain ⟨rfl, v, hv, rfl⟩ := h.nd hN
    obtain ⟨rfl, v', hv', rfl⟩ := h'.nd hN
    rw [hv] at hv'
    exact ⟨rfl, hv'⟩
  · obtain ⟨rfl, rfl⟩ := h.other (Lab.IsLoc.not_isRecv hL) (Lab.IsLoc.not_isND hL)
    obtain ⟨rfl, rfl⟩ := h'.other (Lab.IsLoc.not_isRecv hL) (Lab.IsLoc.not_isND hL)
    exact ⟨rfl, rfl⟩

/-- Axiom 2 (conditional extensibility, Q11) with Q9: adding the next event of a thread with its
canonical source and outcome to a consistent graph gives a consistent graph. -/
theorem Canon.cons (hT : TieQ9 M tie) (hG : M.cons G) (hidx : e.idx = G.cnt e.tid)
    (h : Canon tie G e src out) : M.cons (G.add e src out) := by
  have hGw := M.wf _ hG
  by_cases hR : e.IsRecv
  · rcases Lab.IsRecv.recvB_or_recvNB hR with hB | hNB
    · obtain ⟨s, hs, ht, rfl, rfl⟩ := h.recvB hB
      exact (TieQ9.send_mem hT hGw hs ht).2
    · obtain ⟨rfl, rfl⟩ := h.recvNB hNB
      exact M.ext_bot G e hG hidx hNB
  · by_cases hN : e.IsND
    · obtain ⟨rfl, v, hv, rfl⟩ := h.nd hN
      exact M.ext_nd G e v hG hidx hN (minVal_mem hv)
    · obtain ⟨rfl, rfl⟩ := h.other hR hN
      exact M.ext_plain G e hG hidx hR hN

/-- A canonical source and outcome are admissible (A.2). -/
theorem Canon.adm (hT : TieQ9 M tie) (hG : G.Wf) (h : Canon tie G e src out) :
    Adm G e src out := by
  by_cases hR : e.IsRecv
  · rcases Lab.IsRecv.recvB_or_recvNB hR with hB | hNB
    · obtain ⟨s, hs, ht, rfl, rfl⟩ := h.recvB hB
      have hsS : s ∈ G.S := (TieQ9.send_mem hT hG hs ht).1
      exact Or.inl ⟨hR, rfl, Or.inr ⟨s, hsS, rfl⟩⟩
    · obtain ⟨rfl, rfl⟩ := h.recvNB hNB
      exact Or.inl ⟨hR, rfl, Or.inl rfl⟩
  · by_cases hN : e.IsND
    · obtain ⟨rfl, v, hv, rfl⟩ := h.nd hN
      exact Or.inr (Or.inl ⟨hN, rfl, v, minVal_mem hv, rfl⟩)
    · obtain ⟨rfl, rfl⟩ := h.other hR hN
      exact Or.inr (Or.inr ⟨hR, hN, rfl, rfl⟩)

/-- On a consistent graph, a canonical source and outcome exist for every available event (Q11
for receives through `Usable` and Q9; a non-empty set for an ND event, `Program.nd_ne`). -/
theorem Canon.exists (hT : TieQ9 M tie) (hG : M.cons G) (he : e ∈ M.availM P G) :
    ∃ src out, Canon tie G e src out := by
  have hGw := M.wf _ hG
  obtain ⟨t, -, hn, hu⟩ := M.mem_availM_iff'.mp he
  by_cases hR : e.IsRecv
  · rcases Lab.IsRecv.recvB_or_recvNB hR with hB | hNB
    · have hex : ∃ s ∈ G.S, M.cons (G.addRecv e (.snd s)) := hu.resolve_left (not_not.mpr hB)
      obtain ⟨id, hid⟩ := Option.isSome_iff_exists.mp (hT.2 G e hGw.supp hex)
      obtain ⟨s, hs, -, rfl⟩ := hT.1 G e id hGw.supp hid
      exact ⟨_, _, Canon.intro (fun _ => ⟨s, ((Graph.mem_S _).mp hs).1, hid, rfl, rfl⟩)
        (fun h => absurd hB (Lab.not_isRecvB_of_isRecvNB h)) (fun h => absurd hR
          (Lab.IsND.not_isRecv h)) (fun h => absurd hR h)⟩
    · exact ⟨_, _, Canon.intro (fun h => absurd h (Lab.not_isRecvB_of_isRecvNB hNB))
        (fun _ => ⟨rfl, rfl⟩) (fun h => absurd hR (Lab.IsND.not_isRecv h)) (fun h => absurd hR h)⟩
  · by_cases hN : e.IsND
    · obtain ⟨S, hS⟩ := (Lab.isND_iff e.lab).mp hN
      have hne : S.Nonempty := by
        unfold Program.nextEv at hn
        obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hn
        have hS' : l = .nd S := hS
        exact P.nd_ne _ _ S (hS' ▸ hl)
      have hset : e.ndSet = S := by simp [Ev.ndSet, hS, Lab.ndSet]
      obtain ⟨v, hv⟩ := minVal_isSome hne
      exact ⟨_, _, Canon.intro (fun h => absurd (Lab.IsRecvB.isRecv h) hR)
        (fun h => absurd (Lab.IsRecvNB.isRecv h) hR) (fun _ => ⟨rfl, v, hset ▸ hv, rfl⟩)
        (fun _ h => absurd hN h)⟩
    · exact ⟨_, _, Canon.intro (fun h => absurd (Lab.IsRecvB.isRecv h) hR)
        (fun h => absurd (Lab.IsRecvNB.isRecv h) hR) (fun h => absurd h hN)
        (fun _ _ => ⟨rfl, rfl⟩)⟩

/-! ### Maximal steps: Lemmas A.10, A.11 -/

/-- Lemma A.11 (Maximal consistency), from Axiom 2 with Q9: a maximal step (on the unpremised
operational step) from a consistent graph gives a consistent graph. -/
theorem maxStep₀_cons (hT : TieQ9 M tie) (hG : M.cons G) (h : MaxStep₀ M tie P G e G') :
    M.cons G' := by
  obtain ⟨src, out, ⟨hav, -⟩, hc, rfl⟩ := h
  obtain ⟨t, -, ht, -⟩ := M.mem_availM_iff'.mp hav
  exact hc.cons hT hG (Model.idx_of_nextEv ht)

/-- Lemma A.11 as printed: `G∅ ⊑ G ⇝ G'` (here `∅ →* G` with unpremised steps) and `G`
consistent give `G'` consistent. The premise `∅ →* G` is not used. -/
theorem maxStep₀_cons' (hT : TieQ9 M tie) (_h₀ : OpLe₀ M P Graph.empty G) (hG : M.cons G)
    (h : MaxStep₀ M tie P G e G') : M.cons G' :=
  maxStep₀_cons hT hG h

/-- On a consistent graph the two readings of A.3 (on `OpAdd₀` and on the premised `OpAdd`)
coincide. -/
theorem maxStep_iff_maxStep₀ (hT : TieQ9 M tie) (hG : M.cons G) :
    MaxStep M tie P G e G' ↔ MaxStep₀ M tie P G e G' := by
  constructor
  · rintro ⟨src, out, ⟨h1, h2, -⟩, hc, rfl⟩
    exact ⟨src, out, ⟨h1, h2⟩, hc, rfl⟩
  · intro h
    have hc' := maxStep₀_cons hT hG h
    obtain ⟨src, out, ⟨h1, h2⟩, hc, rfl⟩ := h
    exact ⟨src, out, ⟨h1, h2, hc'⟩, hc, rfl⟩

/-- Lemma A.10 (Extensibility): every available event of a consistent graph is extensible
(Definition A.8), with a consistent result. -/
theorem extensible (hT : TieQ9 M tie) (hG : M.cons G) (he : e ∈ M.availM P G) :
    ∃ G', MaxStep₀ M tie P G e G' ∧ M.cons G' := by
  obtain ⟨src, out, hc⟩ := Canon.exists hT hG he
  have h : MaxStep₀ M tie P G e (G.add e src out) :=
    ⟨src, out, ⟨he, hc.adm hT (M.wf _ hG)⟩, hc, rfl⟩
  exact ⟨_, h, maxStep₀_cons hT hG h⟩

/-- Lemma A.10 as printed: for `G ⊒ G∅` (`∅ →* G`, `G` consistent) and `e ∈ avail(G)`,
`extensible(G, e)`. The premise `∅ →* G` is not used. -/
theorem extensible' (hT : TieQ9 M tie) (_h₀ : OpLe₀ M P Graph.empty G) (hG : M.cons G)
    (he : e ∈ M.availM P G) : Extensible M tie P G e :=
  let ⟨G', h, _⟩ := extensible hT hG he
  ⟨G', h⟩

/-! ### Canonical steps and replay -/

omit [DecidableEq Q] in
/-- The thread of the next event of an execution is a thread of `P`. -/
theorem tid_mem_of_nextEv (hG : G.Wf) (hE : P.Exec G) {t : Tid} (hn : P.nextEv G t = some e) :
    t ∈ P.threads := by
  by_contra ht
  unfold Program.nextEv at hn
  obtain ⟨l, hl, -⟩ := Option.map_eq_some_iff.mp hn
  rcases Nat.eq_zero_or_pos (G.cnt t) with h0 | hpos
  · simp [trace, h0, traceBefore, P.step_none _ ht] at hl
  · obtain ⟨y, hy, hyt, hyi⟩ := (hG.exists_idx_iff t 0).mpr hpos
    have := hE y hy
    rw [hyt, hyi] at this
    simp [traceBefore, P.step_none _ ht] at this

omit [Membership Val Q] in
/-- A canonical step adds a fresh event. -/
theorem CanonStep.idx (h : CanonStep tie P G e G') : e.idx = G.cnt e.tid :=
  Model.idx_of_nextEv h.1

/-- A canonical step keeps consistency. -/
theorem CanonStep.cons (hT : TieQ9 M tie) (hG : M.cons G) (h : CanonStep tie P G e G') :
    M.cons G' := by
  have hidx := h.idx
  obtain ⟨-, src, out, hc, rfl⟩ := h
  exact hc.cons hT hG hidx

/-- A canonical step keeps executions of `P`. -/
theorem CanonStep.exec (hG : G.Wf) (hE : P.Exec G) (h : CanonStep tie P G e G') : P.Exec G' := by
  obtain ⟨hn, src, out, -, rfl⟩ := h
  exact P.exec_add hE hG hn src out

/-- Canonical steps are deterministic on well-formed graphs. -/
theorem CanonStep.det (hG : G.Wf) {G₁ G₂ : Graph Q} (h₁ : CanonStep tie P G e G₁)
    (h₂ : CanonStep tie P G e G₂) : G₁ = G₂ := by
  obtain ⟨-, src, out, hc, rfl⟩ := h₁
  obtain ⟨-, src', out', hc', rfl⟩ := h₂
  obtain ⟨rfl, rfl⟩ := hc.unique hG hc'
  rfl

/-- On a consistent execution, a canonical step is a maximal step (A.3) and conversely. -/
theorem canonStep_iff_maxStep₀ (hT : TieQ9 M tie) (hG : M.cons G) (hE : P.Exec G) :
    CanonStep tie P G e G' ↔ MaxStep₀ M tie P G e G' := by
  have hGw := M.wf _ hG
  constructor
  · rintro ⟨hn, src, out, hc, rfl⟩
    refine ⟨src, out, ⟨?_, hc.adm hT hGw⟩, hc, rfl⟩
    refine M.mem_availM_iff'.mpr ⟨e.tid, tid_mem_of_nextEv hGw hE hn, hn, ?_⟩
    by_cases hB : e.IsRecvB
    · obtain ⟨s, hs, ht, -⟩ := hc.recvB hB
      exact Or.inr ⟨s, TieQ9.send_mem hT hGw hs ht⟩
    · exact Or.inl hB
  · rintro ⟨src, out, ⟨hav, -⟩, hc, rfl⟩
    obtain ⟨t, -, ht, -⟩ := M.mem_availM_iff'.mp hav
    have het : t = e.tid := by
      unfold Program.nextEv at ht
      obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.mp ht
      rfl
    exact ⟨het ▸ ht, src, out, hc, rfl⟩

variable {l : List (Ev Q)}

/-- Canonical replay keeps consistency (Lemma A.11 along a list). -/
theorem Replay.consistent (hT : TieQ9 M tie) (h : Replay tie P G l G') (hG : M.cons G) :
    M.cons G' := by
  induction h with
  | nil => exact hG
  | cons hs _ ih => exact ih (hs.cons hT hG)

/-- Canonical replay from a consistent execution gives a consistent execution. -/
theorem Replay.exec (hT : TieQ9 M tie) (h : Replay tie P G l G') (hG : M.cons G)
    (hE : P.Exec G) : P.Exec G' := by
  induction h with
  | nil => exact hE
  | cons hs _ ih => exact ih (hs.cons hT hG) (hs.exec (M.wf _ hG) hE)

omit [Membership Val Q] in
/-- Canonical replay keeps `Supp`. -/
theorem Replay.supp (h : Replay tie P G l G') (hG : G.Supp) : G'.Supp := by
  induction h with
  | nil => exact hG
  | cons hs _ ih =>
    obtain ⟨-, src, out, -, rfl⟩ := hs
    exact ih (hG.add _ _ _)

/-- `replay_det`: canonical replay from a consistent graph is deterministic. `TieQ9` and a
consistent start are sufficient, not necessary: a single step is deterministic on every
well-formed graph (`CanonStep.det`); the hypotheses keep every intermediate graph well-formed. -/
theorem replay_det (hT : TieQ9 M tie) (hG : M.cons G) {G₁ G₂ : Graph Q}
    (h₁ : Replay tie P G l G₁) (h₂ : Replay tie P G l G₂) : G₁ = G₂ := by
  induction h₁ generalizing G₂ with
  | nil => cases h₂; rfl
  | cons hs _ ih =>
    cases h₂ with
    | cons hs' hr' =>
      rw [hs.det (M.wf _ hG) hs'] at ih
      exact ih (hs'.cons hT hG) hr'

/-- Legality of a list for canonical replay from `G` (Definition A.5, "if such an execution
exists"): each listed event is available after the canonical replay of the earlier ones. -/
def Legal (M : Model Q) (tie : Tie Q) (P : Program Q) : Graph Q → List (Ev Q) → Prop
  | _, [] => True
  | G, e :: l => e ∈ M.availM P G ∧ ∀ G', CanonStep tie P G e G' → Legal M tie P G' l

/-- `replay_exists`: from a consistent graph, a legal list has a canonical replay, and its
result is consistent. -/
theorem replay_exists (hT : TieQ9 M tie) (hG : M.cons G) (h : Legal M tie P G l) :
    ∃ G', Replay tie P G l G' ∧ M.cons G' := by
  induction l generalizing G with
  | nil => exact ⟨G, .nil G, hG⟩
  | cons e l ih =>
    obtain ⟨he, hl⟩ := h
    obtain ⟨src, out, hc⟩ := Canon.exists hT hG he
    obtain ⟨t, -, ht, -⟩ := M.mem_availM_iff'.mp he
    have het : t = e.tid := by
      unfold Program.nextEv at ht
      obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.mp ht
      rfl
    have hs : CanonStep tie P G e (G.add e src out) := ⟨het ▸ ht, src, out, hc, rfl⟩
    obtain ⟨G', hr, hc'⟩ := ih (hs.cons hT hG) (hl _ hs)
    exact ⟨G', .cons hs hr, hc'⟩

/-- From a consistent execution, a list is legal iff it has a canonical replay. -/
theorem legal_iff (hT : TieQ9 M tie) (hG : M.cons G) (hE : P.Exec G) :
    Legal M tie P G l ↔ ∃ G', Replay tie P G l G' := by
  constructor
  · intro h
    obtain ⟨G', h, -⟩ := replay_exists hT hG h
    exact ⟨G', h⟩
  · rintro ⟨G', h⟩
    induction h with
    | nil => trivial
    | cons hs hr ih =>
      refine ⟨?_, fun G'' hs' => ?_⟩
      · obtain ⟨-, -, ⟨hav, -⟩, -⟩ := (canonStep_iff_maxStep₀ hT hG hE).mp hs
        exact hav
      · rw [← hs.det (M.wf _ hG) hs']
        exact ih (hs.cons hT hG) (hs.exec (M.wf _ hG) hE)

/-- On a consistent execution, canonical replay (Q10 (i)) is Definition A.5's chain of maximal
steps. -/
theorem replay_iff_maxChain (hT : TieQ9 M tie) (hG : M.cons G) (hE : P.Exec G) :
    Replay tie P G l G' ↔ MaxChain M tie P G l G' := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil _
    | cons hs _ ih =>
      exact .cons ((canonStep_iff_maxStep₀ hT hG hE).mp hs)
        (ih (hs.cons hT hG) (hs.exec (M.wf _ hG) hE))
  · intro h
    induction h with
    | nil => exact .nil _
    | cons hs _ ih =>
      have hs' := (canonStep_iff_maxStep₀ hT hG hE).mpr hs
      exact .cons hs' (ih (hs'.cons hT hG) (hs'.exec (M.wf _ hG) hE))

end Must

#print axioms Must.minVal_mem
#print axioms Must.Canon.unique
#print axioms Must.Canon.cons
#print axioms Must.Canon.adm
#print axioms Must.Canon.exists
#print axioms Must.maxStep₀_cons
#print axioms Must.maxStep₀_cons'
#print axioms Must.maxStep_iff_maxStep₀
#print axioms Must.extensible
#print axioms Must.extensible'
#print axioms Must.tid_mem_of_nextEv
#print axioms Must.CanonStep.det
#print axioms Must.canonStep_iff_maxStep₀
#print axioms Must.Replay.consistent
#print axioms Must.Replay.exec
#print axioms Must.replay_det
#print axioms Must.Replay.supp
#print axioms Must.replay_exists
#print axioms Must.legal_iff
#print axioms Must.replay_iff_maxChain
