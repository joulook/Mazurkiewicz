import Mazurkiewicz.Must.Graph

/-!
# Operations on Must graphs

Paper: Section 3.1 (`G|E`, `G \ E`, prefixes), Algorithm 1 (`SetRF`, additions of events).
Plan: `plan/must/lean/LEAN-PLAN.md`, decisions Q2, Q3, Q6.

* `restrict E` keeps the events of `E`, and `rf`, `nd` on them, unchanged: a kept receive keeps
  its source, also `⊥`, also a removed send (then the result is not well-formed; it is
  well-formed for a `porf`-closed `E`, `Wf.restrict`). Outside `E`, `rf` and `nd` are `none`.
* `remove S := restrict (events \ S)`.
* `add e src out` adds the event `e` with its source `src` and outcome `out` (Q2: a receive is
  added together with its source; the paper's `G + e` without a source is not a graph value).
  `addSend`, `addRecv`, `addND`, `addLoc` are its instances. `Wf.add` and its corollaries need `e`
  to be the next event of its thread (`e.idx = G.cnt e.tid`).
* `setRF r x` changes the source of the receive `r` to `x`.
* `IsPrefixOf G' G`: `G'` is the restriction of `G` to a `porf`-closed set.
-/

namespace Must

open Relation

/-- Paths of a relation `r'` whose edges are edges of `r` or the edge `(s, t)`: a path of `r`, or
an `r`-path to `s` followed by the edge and an `r`-path from `t`. -/
theorem transGen_of_edge {α : Type*} {r r' : α → α → Prop} {s t : α}
    (hsub : ∀ a b, r' a b → r a b ∨ (a = s ∧ b = t)) {a b : α} (h : TransGen r' a b) :
    TransGen r a b ∨ (ReflTransGen r a s ∧ ReflTransGen r t b) := by
  induction h with
  | single h =>
    rcases hsub _ _ h with h | ⟨rfl, rfl⟩
    · exact Or.inl (TransGen.single h)
    · exact Or.inr ⟨ReflTransGen.refl, ReflTransGen.refl⟩
  | @tail c d _ hcd ih =>
    rcases hsub _ _ hcd with h | ⟨rfl, rfl⟩
    · rcases ih with ih | ⟨h1, h2⟩
      · exact Or.inl (ih.tail h)
      · exact Or.inr ⟨h1, h2.tail h⟩
    · rcases ih with ih | ⟨h1, -⟩
      · exact Or.inr ⟨ih.to_reflTransGen, ReflTransGen.refl⟩
      · exact Or.inr ⟨h1, ReflTransGen.refl⟩

namespace Graph

variable {Q : Type} [DecidableEq Q] (G : Graph Q)

/-! ### Definitions -/

/-- The restriction `G|E`. -/
def restrict (E : Finset (Ev Q)) : Graph Q where
  events := G.events ∩ E
  rf := fun e => if e ∈ E then G.rf e else none
  nd := fun e => if e ∈ E then G.nd e else none

/-- The removal `G \ S`. -/
def remove (S : Finset (Ev Q)) : Graph Q := G.restrict (G.events \ S)

/-- `G'` is a prefix of `G`: the restriction of `G` to a `porf`-closed set. -/
def IsPrefixOf (G' G : Graph Q) : Prop := ∃ E, G.Closed E ∧ G' = G.restrict E

/-- Add the event `e` with source `src` and outcome `out`. -/
def add (e : Ev Q) (src : Option (Src Q)) (out : Option Val) : Graph Q where
  events := insert e G.events
  rf := Function.update G.rf e src
  nd := Function.update G.nd e out

/-- Add the send `e`. -/
abbrev addSend (e : Ev Q) : Graph Q := G.add e none none

/-- Add the receive `e` with source `x` (a send, or `⊥`). -/
abbrev addRecv (e : Ev Q) (x : Src Q) : Graph Q := G.add e (some x) none

/-- Add the ND event `e` with outcome `v`. -/
abbrev addND (e : Ev Q) (v : Val) : Graph Q := G.add e none (some v)

/-- Add the block or error event `e`. -/
abbrev addLoc (e : Ev Q) : Graph Q := G.add e none none

/-- Change the source of the receive `r` to `x` (`SetRF`). -/
def setRF (r : Ev Q) (x : Src Q) : Graph Q where
  events := G.events
  rf := Function.update G.rf r (some x)
  nd := G.nd

@[simp] theorem restrict_events (E : Finset (Ev Q)) : (G.restrict E).events = G.events ∩ E := rfl
@[simp] theorem restrict_rf (E : Finset (Ev Q)) (e : Ev Q) :
    (G.restrict E).rf e = if e ∈ E then G.rf e else none := rfl
@[simp] theorem restrict_nd (E : Finset (Ev Q)) (e : Ev Q) :
    (G.restrict E).nd e = if e ∈ E then G.nd e else none := rfl
@[simp] theorem add_events (e : Ev Q) (src : Option (Src Q)) (out : Option Val) :
    (G.add e src out).events = insert e G.events := rfl
@[simp] theorem add_rf (e : Ev Q) (src : Option (Src Q)) (out : Option Val) :
    (G.add e src out).rf = Function.update G.rf e src := rfl
@[simp] theorem add_nd (e : Ev Q) (src : Option (Src Q)) (out : Option Val) :
    (G.add e src out).nd = Function.update G.nd e out := rfl
@[simp] theorem setRF_events (r : Ev Q) (x : Src Q) : (G.setRF r x).events = G.events := rfl
@[simp] theorem setRF_rf (r : Ev Q) (x : Src Q) :
    (G.setRF r x).rf = Function.update G.rf r (some x) := rfl
@[simp] theorem setRF_nd (r : Ev Q) (x : Src Q) : (G.setRF r x).nd = G.nd := rfl

variable {G}

theorem restrict_rf_eq_some {E : Finset (Ev Q)} {e : Ev Q} {x : Src Q}
    (h : (G.restrict E).rf e = some x) : G.rf e = some x ∧ e ∈ E := by
  by_cases he : e ∈ E
  · simp only [restrict_rf, he, ↓reduceIte] at h
    exact ⟨h, he⟩
  · simp only [restrict_rf, he, ↓reduceIte] at h
    cases h

theorem restrict_nd_eq_some {E : Finset (Ev Q)} {e : Ev Q} {v : Val}
    (h : (G.restrict E).nd e = some v) : G.nd e = some v ∧ e ∈ E := by
  by_cases he : e ∈ E
  · simp only [restrict_nd, he, ↓reduceIte] at h
    exact ⟨h, he⟩
  · simp only [restrict_nd, he, ↓reduceIte] at h
    cases h

/-! ### Restriction: causality -/

/-- A causality step of a restriction is a causality step of the graph. -/
theorem porfStep_restrict_le (E : Finset (Ev Q)) {a b : Ev Q}
    (h : (G.restrict E).porfStep a b) : G.porfStep a b := by
  rcases h with ⟨ha, hb, ht, hi⟩ | ⟨hb, hrf⟩
  · exact Or.inl ⟨(Finset.mem_inter.mp ha).1, (Finset.mem_inter.mp hb).1, ht, hi⟩
  · exact Or.inr ⟨(Finset.mem_inter.mp hb).1, (restrict_rf_eq_some hrf).1⟩

theorem porf_restrict_le (E : Finset (Ev Q)) {a b : Ev Q} (h : (G.restrict E).porf a b) :
    G.porf a b :=
  TransGen.mono (fun _ _ => porfStep_restrict_le E) a b h

/-- On a closed set, the causality steps of the restriction are the restricted steps. -/
theorem porfStep_restrict_eq {E : Finset (Ev Q)} (hE : G.Closed E) :
    (G.restrict E).porfStep = Maz.Restrict G.porfStep (↑(G.events ∩ E) : Set (Ev Q)) := by
  funext a b
  apply propext
  constructor
  · intro h
    have h' := porfStep_restrict_le E h
    have hb : b ∈ G.events ∩ E := by
      rcases h with ⟨-, hb, -⟩ | ⟨hb, -⟩ <;> exact hb
    exact ⟨h', hE h' (Finset.mem_coe.mpr hb), Finset.mem_coe.mpr hb⟩
  · rintro ⟨h, ha, hb⟩
    have ha := Finset.mem_coe.mp ha
    have hb := Finset.mem_coe.mp hb
    rcases h with ⟨-, -, ht, hi⟩ | ⟨-, hrf⟩
    · exact Or.inl ⟨ha, hb, ht, hi⟩
    · refine Or.inr ⟨hb, ?_⟩
      simp only [restrict_rf, (Finset.mem_inter.mp hb).2, ↓reduceIte]
      exact hrf

/-- `porf` of a restriction to a closed set is the restriction of `porf`. -/
theorem porf_restrict_iff {E : Finset (Ev Q)} (hE : G.Closed E) {a b : Ev Q}
    (hb : b ∈ G.events ∩ E) : (G.restrict E).porf a b ↔ G.porf a b := by
  unfold porf
  rw [porfStep_restrict_eq hE]
  exact Maz.transGen_restrict_iff hE (Finset.mem_coe.mpr hb)

/-! ### Restriction: well-formedness and unread sends -/

variable [Membership Val Q]

/-- Restriction to a set closed under `po`-predecessors that keeps the source of every kept
receive is well-formed. -/
theorem Wf.restrict_of (hG : G.Wf) {E : Finset (Ev Q)}
    (hpo : ∀ a b, G.po a b → b ∈ E → a ∈ E)
    (hrf : ∀ r ∈ G.events ∩ E, ∀ s, G.rf r = some (.snd s) → s ∈ E) :
    (G.restrict E).Wf := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e1 h1 e2 h2
    exact hG.idx_inj e1 (Finset.mem_inter.mp h1).1 e2 (Finset.mem_inter.mp h2).1
  · intro e1 h1 i hi
    obtain ⟨h1G, h1E⟩ := Finset.mem_inter.mp h1
    obtain ⟨e', he', ht, hi'⟩ := hG.idx_contig e1 h1G i hi
    exact ⟨e', Finset.mem_inter.mpr ⟨he', hpo e' e1 ⟨he', h1G, ht, by omega⟩ h1E⟩, ht, hi'⟩
  · intro e1
    rw [restrict_rf, restrict_events, Finset.mem_inter]
    by_cases h : e1 ∈ E
    · simp [h, hG.rf_isSome]
    · simp [h]
  · intro r1 h1
    exact hG.rf_bot r1 (restrict_rf_eq_some h1).1
  · intro r1 s h1
    obtain ⟨h1, hE⟩ := restrict_rf_eq_some h1
    exact Finset.mem_inter.mpr ⟨hG.rf_mem _ _ h1,
      hrf r1 (Finset.mem_inter.mpr ⟨(hG.rf_some h1).1, hE⟩) s h1⟩
  · intro r1 r2 s h1 h2
    exact hG.rf_once _ _ _ (restrict_rf_eq_some h1).1 (restrict_rf_eq_some h2).1
  · intro r1 s h1
    exact hG.rf_match _ _ (restrict_rf_eq_some h1).1
  · intro e1
    rw [restrict_nd, restrict_events, Finset.mem_inter]
    by_cases h : e1 ∈ E
    · simp [h, hG.nd_isSome]
    · simp [h]
  · intro e1 v h1
    exact hG.nd_mem e1 v (restrict_nd_eq_some h1).1
  · intro a h
    exact hG.porf_irrefl a (porf_restrict_le E h)

/-- Restriction to a `porf`-closed set is well-formed. -/
theorem Wf.restrict (hG : G.Wf) {E : Finset (Ev Q)} (hE : G.Closed E) : (G.restrict E).Wf := by
  refine hG.restrict_of (fun a b hab hb => ?_) (fun r hr s hs => ?_)
  · have hb' : b ∈ G.events ∩ E := Finset.mem_inter.mpr ⟨hab.2.1, hb⟩
    exact (Finset.mem_inter.mp (hE (Or.inl hab) (Finset.mem_coe.mpr hb'))).2
  · exact (Finset.mem_inter.mp (hE (Or.inr ⟨(Finset.mem_inter.mp hr).1, hs⟩)
      (Finset.mem_coe.mpr hr))).2

omit [Membership Val Q] in
/-- The unread sends of a restriction: the kept sends read by no kept receive. -/
theorem mem_US_restrict {E : Finset (Ev Q)} {s : Ev Q} :
    s ∈ (G.restrict E).US ↔
      s ∈ G.events ∩ E ∧ s.IsSend ∧ ∀ r ∈ G.events ∩ E, G.rf r ≠ some (.snd s) := by
  rw [mem_US, restrict_events]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall₂_congr fun r hr => ?_))
  simp only [restrict_rf, (Finset.mem_inter.mp hr).2, ↓reduceIte]

omit [Membership Val Q] in
/-- A kept unread send stays unread. -/
theorem US_restrict_of_mem {E : Finset (Ev Q)} {s : Ev Q} (hs : s ∈ G.US) (hE : s ∈ E) :
    s ∈ (G.restrict E).US := by
  obtain ⟨h1, h2, h3⟩ := (G.mem_US).mp hs
  exact mem_US_restrict.mpr ⟨Finset.mem_inter.mpr ⟨h1, hE⟩, h2,
    fun r hr => h3 r (Finset.mem_inter.mp hr).1⟩

/-- A kept send whose reader is removed becomes unread. -/
theorem Wf.mem_US_restrict_of_reader (hG : G.Wf) {E : Finset (Ev Q)} {s r : Ev Q}
    (hs : s ∈ E) (hr : G.rf r = some (.snd s)) (hrE : r ∉ E) : s ∈ (G.restrict E).US := by
  refine mem_US_restrict.mpr ⟨Finset.mem_inter.mpr ⟨hG.rf_mem _ _ hr, hs⟩,
    (hG.rf_match _ _ hr).isSend, fun r' hr' h => ?_⟩
  have := hG.rf_once _ _ _ h hr
  subst this
  exact hrE (Finset.mem_inter.mp hr').2

/-! ### Restriction: algebra and prefixes -/

/-- A restriction to a superset of the events changes nothing. -/
theorem Wf.restrict_of_subset (hG : G.Wf) {E : Finset (Ev Q)} (h : G.events ⊆ E) :
    G.restrict E = G := by
  apply Graph.ext
  · rw [restrict_events]
    exact Finset.inter_eq_left.mpr h
  · funext e
    rw [restrict_rf]
    split_ifs with he
    · rfl
    · exact (hG.rf_none (Or.inl (fun h' => he (h h')))).symm
  · funext e
    rw [restrict_nd]
    split_ifs with he
    · rfl
    · exact (hG.nd_none (Or.inl (fun h' => he (h h')))).symm

theorem Wf.restrict_self (hG : G.Wf) : G.restrict G.events = G :=
  hG.restrict_of_subset (subset_refl _)

omit [Membership Val Q] in
theorem restrict_restrict (G : Graph Q) (E E' : Finset (Ev Q)) :
    (G.restrict E).restrict E' = G.restrict (E ∩ E') := by
  apply Graph.ext
  · simp [Finset.inter_assoc]
  · funext e
    by_cases h1 : e ∈ E <;> by_cases h2 : e ∈ E' <;> simp [h1, h2]
  · funext e
    by_cases h1 : e ∈ E <;> by_cases h2 : e ∈ E' <;> simp [h1, h2]

theorem Wf.of_isPrefixOf {G' : Graph Q} (hG : G.Wf) (h : G'.IsPrefixOf G) : G'.Wf := by
  obtain ⟨E, hE, rfl⟩ := h
  exact hG.restrict hE

omit [Membership Val Q] in
theorem IsPrefixOf.events_subset {G' : Graph Q} (h : G'.IsPrefixOf G) :
    G'.events ⊆ G.events := by
  obtain ⟨E, -, rfl⟩ := h
  exact Finset.inter_subset_left

/-- `IsPrefixOf` is reflexive on well-formed graphs. -/
theorem Wf.isPrefixOf_refl (hG : G.Wf) : G.IsPrefixOf G := by
  refine ⟨G.events, fun a b h _ => ?_, hG.restrict_self.symm⟩
  have ha := (hG.mem_of_porfStep h).1
  exact Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨ha, ha⟩)

omit [Membership Val Q] in
/-- `IsPrefixOf` is transitive. -/
theorem IsPrefixOf.trans {G₁ G₂ G₃ : Graph Q} (h₁ : G₁.IsPrefixOf G₂) (h₂ : G₂.IsPrefixOf G₃) :
    G₁.IsPrefixOf G₃ := by
  obtain ⟨E₂, hE₂, rfl⟩ := h₂
  obtain ⟨E₁, hE₁, rfl⟩ := h₁
  refine ⟨E₂ ∩ E₁, fun a b hab hb => ?_, restrict_restrict G₃ E₂ E₁⟩
  have hb := Finset.mem_coe.mp hb
  simp only [Finset.mem_inter] at hb
  have hb₂ : b ∈ G₃.events ∩ E₂ := Finset.mem_inter.mpr ⟨hb.1, hb.2.1⟩
  have ha₂ := Finset.mem_coe.mp (hE₂ hab (Finset.mem_coe.mpr hb₂))
  have hab' : (G₃.restrict E₂).porfStep a b := by
    rw [porfStep_restrict_eq hE₂]
    exact ⟨hab, Finset.mem_coe.mpr ha₂, Finset.mem_coe.mpr hb₂⟩
  have hb₁ : b ∈ (G₃.restrict E₂).events ∩ E₁ :=
    Finset.mem_inter.mpr ⟨hb₂, hb.2.2⟩
  have ha₁ := Finset.mem_coe.mp (hE₁ hab' (Finset.mem_coe.mpr hb₁))
  rw [restrict_events, Finset.mem_inter] at ha₁
  exact Finset.mem_coe.mpr (Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp ha₂).1, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ha₂).2, ha₁.2⟩⟩)

/-- `IsPrefixOf` is antisymmetric on well-formed graphs (for ordinary equality). -/
theorem IsPrefixOf.antisymm {G' : Graph Q} (hG : G.Wf) (h₁ : G'.IsPrefixOf G)
    (h₂ : G.IsPrefixOf G') : G' = G := by
  have hsub := h₂.events_subset
  obtain ⟨E, -, rfl⟩ := h₁
  refine hG.restrict_of_subset (fun e he => ?_)
  exact (Finset.mem_inter.mp (hsub he)).2

omit [Membership Val Q] in
/-- The empty graph is a prefix of every graph. -/
theorem empty_isPrefixOf (G : Graph Q) : (empty : Graph Q).IsPrefixOf G := by
  refine ⟨∅, fun a b _ hb => ?_, ?_⟩
  · simp at hb
  · apply Graph.ext
    · simp [empty]
    · funext e
      simp [empty]
    · funext e
      simp [empty]

/-! ### Removal -/

/-- Removing a set closed under causal successors leaves a closed set. -/
theorem Wf.remove_closed (hG : G.Wf) {S : Finset (Ev Q)}
    (hS : ∀ q ∈ S, ∀ b, G.porfStep q b → b ∈ S) : G.Closed (G.events \ S) := by
  intro a b hab hb
  have hb := Finset.mem_coe.mp hb
  have ha := (hG.mem_of_porfStep hab).1
  refine Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨ha, Finset.mem_sdiff.mpr ⟨ha, fun haS => ?_⟩⟩)
  exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hb).2).2 (hS a haS b hab)

theorem Wf.remove (hG : G.Wf) {S : Finset (Ev Q)} (hS : ∀ q ∈ S, ∀ b, G.porfStep q b → b ∈ S) :
    (G.remove S).Wf :=
  hG.restrict (hG.remove_closed hS)

theorem Wf.remove_isPrefixOf (hG : G.Wf) {S : Finset (Ev Q)}
    (hS : ∀ q ∈ S, ∀ b, G.porfStep q b → b ∈ S) : (G.remove S).IsPrefixOf G :=
  ⟨G.events \ S, hG.remove_closed hS, rfl⟩

/-! ### Additions: causality -/

omit [DecidableEq Q] in
/-- An event of the graph in the thread of the next event `e` has a smaller index. -/
theorem Wf.idx_lt_of_idx_eq_cnt (hG : G.Wf) {e b : Ev Q} (hidx : e.idx = G.cnt e.tid)
    (hb : b ∈ G.events) (ht : b.tid = e.tid) : b.idx < e.idx := by
  have := hG.idx_lt_cnt hb
  rw [ht] at this
  omega

variable {e : Ev Q} {src : Option (Src Q)} {out : Option Val}

/-- A causality step of `G.add e src out` is a step of `G` or ends in `e`. -/
theorem Wf.porfStep_add_cases (hG : G.Wf) (hidx : e.idx = G.cnt e.tid) {a b : Ev Q}
    (h : (G.add e src out).porfStep a b) : G.porfStep a b ∨ b = e := by
  rcases h with ⟨ha, hb, ht, hi⟩ | ⟨hb, hrf⟩
  · rw [add_events, Finset.mem_insert] at ha hb
    rcases hb with hb | hb
    · exact Or.inr hb
    · rcases ha with ha | ha
      · subst ha
        have := hG.idx_lt_of_idx_eq_cnt hidx hb ht.symm
        omega
      · exact Or.inl (Or.inl ⟨ha, hb, ht, hi⟩)
  · by_cases h : b = e
    · exact Or.inr h
    · rw [add_events, Finset.mem_insert] at hb
      rw [add_rf, Function.update_of_ne h] at hrf
      exact Or.inl (Or.inr ⟨hb.resolve_left h, hrf⟩)

/-- The causality steps of `G` are steps of `G.add e src out`. -/
theorem Wf.porfStep_add_of_porfStep (hG : G.Wf) (hidx : e.idx = G.cnt e.tid) {a b : Ev Q}
    (h : G.porfStep a b) : (G.add e src out).porfStep a b := by
  have he := hG.not_mem_of_idx_eq_cnt hidx
  rcases h with ⟨ha, hb, ht, hi⟩ | ⟨hb, hrf⟩
  · exact Or.inl ⟨Finset.mem_insert_of_mem ha, Finset.mem_insert_of_mem hb, ht, hi⟩
  · have hne : b ≠ e := fun h => he (h ▸ hb)
    exact Or.inr ⟨Finset.mem_insert_of_mem hb, by rw [add_rf, Function.update_of_ne hne]; exact hrf⟩

/-- The new event, the next of its thread with a source in the graph, has no outgoing causality
step. -/
theorem Wf.not_porfStep_add_left (hG : G.Wf) (hidx : e.idx = G.cnt e.tid)
    (hsrc : ∀ s, src = some (.snd s) → s ∈ G.events) (b : Ev Q) :
    ¬ (G.add e src out).porfStep e b := by
  have he := hG.not_mem_of_idx_eq_cnt hidx
  rintro (⟨-, hb, ht, hi⟩ | ⟨hb, hrf⟩)
  · rw [add_events, Finset.mem_insert] at hb
    rcases hb with hb | hb
    · subst hb
      omega
    · have := hG.idx_lt_of_idx_eq_cnt hidx hb ht.symm
      omega
  · by_cases h : b = e
    · rw [h, add_rf, Function.update_self] at hrf
      exact he (hsrc e hrf)
    · rw [add_rf, Function.update_of_ne h] at hrf
      exact he (hG.rf_mem _ _ hrf)

/-- The new event has no outgoing `porf` edge. For a receive added last: it has only incoming
edges. -/
theorem Wf.not_porf_add_left (hG : G.Wf) (hidx : e.idx = G.cnt e.tid)
    (hsrc : ∀ s, src = some (.snd s) → s ∈ G.events) (b : Ev Q) :
    ¬ (G.add e src out).porf e b := fun h => by
  obtain ⟨c, hc⟩ := Maz.exists_first_of_transGen h
  exact hG.not_porfStep_add_left hidx hsrc c hc

/-- `porf` of `G.add e src out` between two events other than the target `e` is `porf` of `G`. -/
theorem Wf.porf_add_iff (hG : G.Wf) (hidx : e.idx = G.cnt e.tid)
    (hsrc : ∀ s, src = some (.snd s) → s ∈ G.events) {a b : Ev Q} (hb : b ≠ e) :
    (G.add e src out).porf a b ↔ G.porf a b := by
  constructor
  · intro h
    exact (Maz.transGen_of_sink (r' := (G.add e src out).porfStep) (e := e)
      (fun _ _ => hG.porfStep_add_cases hidx)
      (hG.not_porfStep_add_left hidx hsrc) h).resolve_right hb
  · exact TransGen.mono (fun _ _ => hG.porfStep_add_of_porfStep hidx) a b

/-- The causality steps into the new event: `po` from its thread, `rf` from its source. -/
theorem Wf.porfStep_add_right_iff (hG : G.Wf) (hidx : e.idx = G.cnt e.tid) {a : Ev Q} :
    (G.add e src out).porfStep a e ↔ (a ∈ G.events ∧ a.tid = e.tid) ∨ src = some (.snd a) := by
  constructor
  · rintro (⟨ha, -, ht, hi⟩ | ⟨-, hrf⟩)
    · rw [add_events, Finset.mem_insert] at ha
      rcases ha with ha | ha
      · subst ha
        omega
      · exact Or.inl ⟨ha, ht⟩
    · rw [add_rf, Function.update_self] at hrf
      exact Or.inr hrf
  · rintro (⟨ha, ht⟩ | hs)
    · exact Or.inl ⟨Finset.mem_insert_of_mem ha, Finset.mem_insert_self _ _, ht,
        hG.idx_lt_of_idx_eq_cnt hidx ha ht⟩
    · exact Or.inr ⟨Finset.mem_insert_self _ _, by rw [add_rf, Function.update_self]; exact hs⟩

/-! ### Additions: well-formedness -/

/-- Adding the next event of a thread keeps the graph well-formed when the source and outcome
fit the label: a source exactly for a receive, `⊥` only for a non-blocking receive, a real
source an unread matching send of the graph; an outcome exactly for an ND event, in its set. -/
theorem Wf.add (hG : G.Wf) (hidx : e.idx = G.cnt e.tid)
    (hsrc : src.isSome ↔ e.IsRecv)
    (hbot : src = some .bot → e.IsRecvNB)
    (hsnd : ∀ s, src = some (.snd s) → s ∈ G.US ∧ s.Matches e)
    (hout : out.isSome ↔ e.IsND)
    (hval : ∀ v, out = some v → v ∈ e.ndSet) :
    (G.add e src out).Wf := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  have hsrcG : ∀ s, src = some (.snd s) → s ∈ G.events :=
    fun s hs => ((G.mem_US).mp (hsnd s hs).1).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e1 h1 e2 h2 ht hi
    rw [add_events, Finset.mem_insert] at h1 h2
    rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
    · rfl
    · have := hG.idx_lt_of_idx_eq_cnt hidx h2 ht.symm
      omega
    · have := hG.idx_lt_of_idx_eq_cnt hidx h1 ht
      omega
    · exact hG.idx_inj _ h1 _ h2 ht hi
  · intro e1 h1 i hi
    rw [add_events, Finset.mem_insert] at h1
    rcases h1 with rfl | h1
    · rw [hidx] at hi
      obtain ⟨e', he', ht, hi'⟩ := (hG.exists_idx_iff _ _).mpr hi
      exact ⟨e', Finset.mem_insert_of_mem he', ht, hi'⟩
    · obtain ⟨e', he', ht, hi'⟩ := hG.idx_contig e1 h1 i hi
      exact ⟨e', Finset.mem_insert_of_mem he', ht, hi'⟩
  · intro e1
    by_cases h : e1 = e
    · subst h
      simp [hsrc]
    · rw [add_rf, Function.update_of_ne h, hG.rf_isSome, add_events, Finset.mem_insert]
      simp [h]
  · intro r1 h1
    by_cases h : r1 = e
    · rw [h, add_rf, Function.update_self] at h1
      rw [h]
      exact hbot h1
    · rw [add_rf, Function.update_of_ne h] at h1
      exact hG.rf_bot r1 h1
  · intro r1 s h1
    by_cases h : r1 = e
    · rw [h, add_rf, Function.update_self] at h1
      exact Finset.mem_insert_of_mem (hsrcG s h1)
    · rw [add_rf, Function.update_of_ne h] at h1
      exact Finset.mem_insert_of_mem (hG.rf_mem _ _ h1)
  · intro r1 r2 s h1 h2
    have key : ∀ r', r' ≠ e → G.rf r' = some (.snd s) → src = some (.snd s) → False :=
      fun r' _ h' hs => ((G.mem_US).mp (hsnd s hs).1).2.2 r' (hG.rf_some h').1 h'
    by_cases ha : r1 = e <;> by_cases hb : r2 = e
    · rw [ha, hb]
    · rw [ha, add_rf, Function.update_self] at h1
      rw [add_rf, Function.update_of_ne hb] at h2
      exact (key r2 hb h2 h1).elim
    · rw [hb, add_rf, Function.update_self] at h2
      rw [add_rf, Function.update_of_ne ha] at h1
      exact (key r1 ha h1 h2).elim
    · rw [add_rf, Function.update_of_ne ha] at h1
      rw [add_rf, Function.update_of_ne hb] at h2
      exact hG.rf_once _ _ _ h1 h2
  · intro r1 s h1
    by_cases h : r1 = e
    · rw [h, add_rf, Function.update_self] at h1
      rw [h]
      exact (hsnd s h1).2
    · rw [add_rf, Function.update_of_ne h] at h1
      exact hG.rf_match _ _ h1
  · intro e1
    by_cases h : e1 = e
    · subst h
      simp [hout]
    · rw [add_nd, Function.update_of_ne h, hG.nd_isSome, add_events, Finset.mem_insert]
      simp [h]
  · intro e1 v h1
    by_cases h : e1 = e
    · rw [h, add_nd, Function.update_self] at h1
      rw [h]
      exact hval v h1
    · rw [add_nd, Function.update_of_ne h] at h1
      exact hG.nd_mem e1 v h1
  · exact Maz.Acyclic.of_sink hG.acyclic (fun _ _ => hG.porfStep_add_cases hidx)
      (hG.not_porfStep_add_left hidx hsrcG)

/-- Adding a send as the next event of its thread. -/
theorem Wf.addSend (hG : G.Wf) (hidx : e.idx = G.cnt e.tid) (hs : e.IsSend) :
    (G.addSend e).Wf :=
  hG.add hidx (by simp [Lab.IsSend.not_isRecv hs]) (by simp) (by simp)
    (by simp [Lab.IsSend.not_isND hs]) (by simp)

/-- Adding a block or error event as the next event of its thread. -/
theorem Wf.addLoc (hG : G.Wf) (hidx : e.idx = G.cnt e.tid) (hl : e.IsLoc) :
    (G.addLoc e).Wf :=
  hG.add hidx (by simp [Lab.IsLoc.not_isRecv hl]) (by simp) (by simp)
    (by simp [Lab.IsLoc.not_isND hl]) (by simp)

/-- Adding an ND event `ND_S` as the next event of its thread, with an outcome in `S`. -/
theorem Wf.addND (hG : G.Wf) (hidx : e.idx = G.cnt e.tid) {S : Finset Val}
    (hl : e.lab = .nd S) {v : Val} (hv : v ∈ S) : (G.addND e v).Wf := by
  have hN : e.IsND := by simp [Ev.IsND, hl, Lab.IsND]
  refine hG.add hidx (by simp [Lab.IsND.not_isRecv hN]) (by simp) (by simp) (by simp [hN]) ?_
  intro w hw
  cases hw
  simpa [Ev.ndSet, hl, Lab.ndSet] using hv

/-- Adding a receive as the next event of its thread, reading an unread matching send. -/
theorem Wf.addRecv (hG : G.Wf) (hidx : e.idx = G.cnt e.tid) {s : Ev Q} (hs : s ∈ G.US)
    (hm : s.Matches e) : (G.addRecv e (.snd s)).Wf := by
  have hR : e.IsRecv := hm.isRecv
  refine hG.add hidx (by simp [hR]) (by simp) ?_ (by simp [Lab.IsRecv.not_isND hR]) (by simp)
  intro s' hs'
  cases hs'
  exact ⟨hs, hm⟩

/-- Adding a non-blocking receive as the next event of its thread, reading `⊥`. -/
theorem Wf.addRecv_bot (hG : G.Wf) (hidx : e.idx = G.cnt e.tid) (hnb : e.IsRecvNB) :
    (G.addRecv e .bot).Wf := by
  have hR : e.IsRecv := Lab.IsRecvNB.isRecv hnb
  exact hG.add hidx (by simp [hR]) (fun _ => hnb) (by simp) (by simp [Lab.IsRecv.not_isND hR])
    (by simp)

omit [Membership Val Q] in
/-- The number of events of a thread after adding the next event of a thread. -/
theorem cnt_add (he : e ∉ G.events) (t : Tid) :
    (G.add e src out).cnt t = if e.tid = t then G.cnt t + 1 else G.cnt t := by
  unfold cnt
  rw [add_events, Finset.filter_insert]
  by_cases ht : e.tid = t
  · simp only [ht, ↓reduceIte]
    exact Finset.card_insert_of_notMem (by simp [he])
  · simp only [ht, ↓reduceIte]

/-- The unread sends after an addition: the new event if it is a send, and the old unread sends
other than the new source. -/
theorem Wf.mem_US_add (hG : G.Wf) (hidx : e.idx = G.cnt e.tid)
    (hsrc : ∀ s, src = some (.snd s) → s ∈ G.events) {s' : Ev Q} :
    s' ∈ (G.add e src out).US ↔ (s' = e ∧ e.IsSend) ∨ (s' ∈ G.US ∧ src ≠ some (.snd s')) := by
  have he := hG.not_mem_of_idx_eq_cnt hidx
  rw [mem_US, mem_US, add_events]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [Finset.mem_insert] at h1
    rcases h1 with rfl | h1
    · exact Or.inl ⟨rfl, h2⟩
    · refine Or.inr ⟨⟨h1, h2, fun r hr => ?_⟩, ?_⟩
      · have hne : r ≠ e := fun h => he (h ▸ hr)
        have := h3 r (Finset.mem_insert_of_mem hr)
        rwa [add_rf, Function.update_of_ne hne] at this
      · have := h3 e (Finset.mem_insert_self _ _)
        rwa [add_rf, Function.update_self] at this
  · rintro (⟨rfl, hs⟩ | ⟨⟨h1, h2, h3⟩, h4⟩)
    · refine ⟨Finset.mem_insert_self _ _, hs, fun r hr h => ?_⟩
      by_cases hre : r = s'
      · rw [hre, add_rf, Function.update_self] at h
        exact he (hsrc _ h)
      · rw [add_rf, Function.update_of_ne hre] at h
        exact he (hG.rf_mem _ _ h)
    · refine ⟨Finset.mem_insert_of_mem h1, h2, fun r hr h => ?_⟩
      by_cases hre : r = e
      · rw [hre, add_rf, Function.update_self] at h
        exact h4 h
      · rw [add_rf, Function.update_of_ne hre] at h
        rw [Finset.mem_insert] at hr
        exact h3 r (hr.resolve_left hre) h

/-- Removing the event just added gives back the graph. -/
theorem Wf.remove_add (hG : G.Wf) (hidx : e.idx = G.cnt e.tid) :
    (G.add e src out).remove {e} = G := by
  have he := hG.not_mem_of_idx_eq_cnt hidx
  have hset : ∀ q, q ∈ insert e G.events \ {e} ↔ q ∈ G.events := by
    intro q
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h | h, hne⟩
      · exact absurd h hne
      · exact h
    · intro h
      exact ⟨Or.inr h, fun hq => he (hq ▸ h)⟩
  apply Graph.ext
  · ext q
    simp only [Must.Graph.remove, restrict_events, add_events, Finset.mem_inter, hset]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨Finset.mem_insert_of_mem h, h⟩
  · funext q
    simp only [Must.Graph.remove, restrict_rf, add_events, hset, add_rf]
    split_ifs with hq
    · exact Function.update_of_ne (fun h : q = e => he (h ▸ hq)) _ _
    · exact (hG.rf_none (Or.inl hq)).symm
  · funext q
    simp only [Must.Graph.remove, restrict_nd, add_events, hset, add_nd]
    split_ifs with hq
    · exact Function.update_of_ne (fun h : q = e => he (h ▸ hq)) _ _
    · exact (hG.nd_none (Or.inl hq)).symm

/-! ### Changing a source -/

variable {r : Ev Q} {x : Src Q}

omit [Membership Val Q] in
/-- A causality step after `setRF r x` is a step of `G` or the new edge. -/
theorem porfStep_setRF_cases {a b : Ev Q} (h : (G.setRF r x).porfStep a b) :
    G.porfStep a b ∨ (x = .snd a ∧ b = r) := by
  rcases h with hpo | ⟨hb, hrf⟩
  · exact Or.inl (Or.inl hpo)
  · by_cases h : b = r
    · rw [h, setRF_rf, Function.update_self] at hrf
      exact Or.inr ⟨Option.some.inj hrf, h⟩
    · rw [setRF_rf, Function.update_of_ne h] at hrf
      exact Or.inl (Or.inr ⟨hb, hrf⟩)

/-- Changing the source of a receive `r` of the graph keeps the graph well-formed when the new
source is `⊥` for a non-blocking `r`, or a matching send of the graph read by no other receive
and not causally after `r`. -/
theorem Wf.setRF (hG : G.Wf) (hr : r ∈ G.events)
    (hbot : x = .bot → r.IsRecvNB)
    (hsnd : ∀ s, x = .snd s → s ∈ G.events ∧ s.Matches r ∧
      (∀ r' ∈ G.events, r' ≠ r → G.rf r' ≠ some (.snd s)) ∧ ¬ G.porf r s) :
    (G.setRF r x).Wf := by
  have hR : r.IsRecv := by
    cases x with
    | bot => exact Lab.IsRecvNB.isRecv (hbot rfl)
    | snd s => exact (hsnd s rfl).2.1.isRecv
  refine ⟨hG.idx_inj, hG.idx_contig, ?_, ?_, ?_, ?_, ?_, hG.nd_isSome, hG.nd_mem, ?_⟩
  · intro e1
    by_cases h : e1 = r
    · subst h
      simp [hr, hR]
    · rw [setRF_rf, Function.update_of_ne h, hG.rf_isSome, setRF_events]
  · intro r1 h1
    by_cases h : r1 = r
    · rw [h, setRF_rf, Function.update_self] at h1
      rw [h]
      exact hbot (Option.some.inj h1)
    · rw [setRF_rf, Function.update_of_ne h] at h1
      exact hG.rf_bot r1 h1
  · intro r1 s h1
    by_cases h : r1 = r
    · rw [h, setRF_rf, Function.update_self] at h1
      exact (hsnd s (Option.some.inj h1)).1
    · rw [setRF_rf, Function.update_of_ne h] at h1
      exact hG.rf_mem _ _ h1
  · intro r1 r2 s h1 h2
    have key : ∀ r', r' ≠ r → G.rf r' = some (.snd s) → x = .snd s → False :=
      fun r' hne h' hs => (hsnd s hs).2.2.1 r' (hG.rf_some h').1 hne h'
    by_cases ha : r1 = r <;> by_cases hb : r2 = r
    · rw [ha, hb]
    · rw [ha, setRF_rf, Function.update_self] at h1
      rw [setRF_rf, Function.update_of_ne hb] at h2
      exact (key r2 hb h2 (Option.some.inj h1)).elim
    · rw [hb, setRF_rf, Function.update_self] at h2
      rw [setRF_rf, Function.update_of_ne ha] at h1
      exact (key r1 ha h1 (Option.some.inj h2)).elim
    · rw [setRF_rf, Function.update_of_ne ha] at h1
      rw [setRF_rf, Function.update_of_ne hb] at h2
      exact hG.rf_once _ _ _ h1 h2
  · intro r1 s h1
    by_cases h : r1 = r
    · rw [h, setRF_rf, Function.update_self] at h1
      rw [h]
      exact (hsnd s (Option.some.inj h1)).2.1
    · rw [setRF_rf, Function.update_of_ne h] at h1
      exact hG.rf_match _ _ h1
  · intro a ha
    cases x with
    | bot =>
      refine hG.porf_irrefl a (TransGen.mono (fun c d h => ?_) a a ha)
      rcases porfStep_setRF_cases h with h | ⟨h, -⟩
      · exact h
      · cases h
    | snd s =>
      obtain ⟨-, hm, -, hns⟩ := hsnd s rfl
      have hsub : ∀ c d, (G.setRF r (.snd s)).porfStep c d → G.porfStep c d ∨ (c = s ∧ d = r) :=
        fun c d h => (porfStep_setRF_cases h).imp id (fun h => ⟨(Src.snd.inj h.1).symm, h.2⟩)
      rcases transGen_of_edge hsub ha with h | ⟨h1, h2⟩
      · exact hG.porf_irrefl a h
      · rcases reflTransGen_iff_eq_or_transGen.mp (h2.trans h1) with h | h
        · subst h
          exact Lab.IsSend.not_isRecv hm.isSend hR
        · exact hns h

end Graph

end Must
