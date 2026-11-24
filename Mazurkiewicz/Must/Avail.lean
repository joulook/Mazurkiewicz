import Mazurkiewicz.Must.AlgSound

/-!
# Unpremised operational steps, Lemmas A.9, A.12, A.15 (milestone M5)

Paper: Appendix A.2 (operational steps), Definition A.4 (`⊑`), Lemmas A.9, A.12, A.15 (p. 30).
Plan: `plan/must/lean/LEAN-PLAN.md`, decisions Q7, Q13, Section 2b ("operational prefix",
A.15); the M5 obligation recorded at M4 (`LOG.md`).

* `Graph.SrcMem G`: every real source of `G` is an event of `G`. With `Supp` it is invariant
  under the printed operational steps `OpStepG₀` (`OpLe₀.supp_srcMem`).
* `OpStepG₀.back`: a printed step `X →₀ Y` from a graph with `Supp` and `SrcMem` into a
  consistent `Y` removes nothing: `X = Y \ {e}` with `e` `porf`-maximal in `Y`, so `X` is
  consistent by prefix-closedness and the step is a premised step `OpStepG`.
* `OpLe₀.opLe` (the M5 obligation): `M.cons G → M.cons G' → OpLe₀ M P G G' → OpLe M P G G'`;
  `opLe_iff_opLe₀`: between consistent graphs the two readings of `→*` coincide.
* A.9 (`ReachM.opLe_empty`): a reachable configuration is an operational extension of `∅`.
* A.12 (`cons_of_opLe₀`): on an unpremised path `∅ →* G →* G'`, consistency of `G'` gives
  consistency of `G` (Axiom 1).
* A.15 (`availM_stable`): an available event stays available in every consistent execution that
  extends the graph as a causal prefix and does not contain the event; for a blocking receive the
  witness send stays unread (a reader is a receive of the same thread). Uses Q7
  (`Model.mem_availM_iff`). `availM_stable_opLe₀`: the same for an unpremised operational path.

All results hold for every model `M`.
-/

namespace Must

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q}

namespace Graph

/-- Every real source is an event of the graph. -/
def SrcMem (G : Graph Q) : Prop := ∀ r s, G.rf r = some (.snd s) → s ∈ G.events

omit [DecidableEq Q] [Membership Val Q] in
theorem supp_empty_graph : (empty : Graph Q).Supp := fun _ _ => ⟨rfl, rfl⟩

omit [DecidableEq Q] [Membership Val Q] in
theorem srcMem_empty : (empty : Graph Q).SrcMem := fun _ _ h => by simp [empty] at h

omit [DecidableEq Q] in
theorem Wf.srcMem {G : Graph Q} (hG : G.Wf) : G.SrcMem := hG.rf_mem

omit [Membership Val Q] in
/-- A graph with `Supp` is its restriction to a superset of its events. -/
theorem Supp.restrict_of_subset {G : Graph Q} (hG : G.Supp) {E : Finset (Ev Q)}
    (h : G.events ⊆ E) : G.restrict E = G := by
  rw [← hG.normalize_eq]
  apply Graph.ext
  · simp only [normalize, restrict_events, Finset.inter_self]
    exact Finset.inter_eq_left.mpr h
  · funext x
    by_cases hx : x ∈ G.events
    · simp [normalize, hx, h hx]
    · simp [normalize, hx]
  · funext x
    by_cases hx : x ∈ G.events
    · simp [normalize, hx, h hx]
    · simp [normalize, hx]

omit [Membership Val Q] in
/-- Restrictions of a graph with `Supp` to sets that agree on its events are equal. -/
theorem Supp.restrict_congr {G : Graph Q} (hG : G.Supp) {E E' : Finset (Ev Q)}
    (h : ∀ x ∈ G.events, x ∈ E ↔ x ∈ E') : G.restrict E = G.restrict E' := by
  apply Graph.ext
  · ext x
    simp only [restrict_events, Finset.mem_inter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (h x h1).mp h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (h x h1).mpr h2⟩⟩
  · funext x
    by_cases hx : x ∈ G.events
    · simp only [restrict_rf, h x hx]
    · simp [(hG x hx).1]
  · funext x
    by_cases hx : x ∈ G.events
    · simp only [restrict_nd, h x hx]
    · simp [(hG x hx).2]

end Graph

/-! ### Unpremised operational steps -/

variable {G G' X Y : Graph Q} {e : Ev Q} {src : Option (Src Q)} {out : Option Val}

omit [DecidableEq Q] [Membership Val Q] in
/-- An admissible real source is an event of the graph. -/
theorem Adm.src_mem (h : Adm G e src out) {s : Ev Q} (hs : src = some (.snd s)) :
    s ∈ G.events := by
  rcases h with ⟨-, -, h | ⟨s', hs', h⟩⟩ | ⟨-, h, -⟩ | ⟨-, -, h, -⟩
  · rw [hs] at h
    cases h
  · rw [hs] at h
    cases h
    exact (Graph.mem_S _).mp hs' |>.1
  · rw [hs] at h
    cases h
  · rw [hs] at h
    cases h

/-- `Supp` and `SrcMem` are invariant under printed operational steps. -/
theorem OpStepG₀.supp_srcMem (h : OpStepG₀ M P X Y) (hS : X.Supp) (hM : X.SrcMem) :
    Y.Supp ∧ Y.SrcMem := by
  obtain ⟨e, src, out, ⟨-, hadm⟩, rfl⟩ := h
  refine ⟨hS.add e src out, fun r s hr => ?_⟩
  rw [add_events]
  by_cases hre : r = e
  · rw [hre, add_rf, Function.update_self] at hr
    exact Finset.mem_insert_of_mem (hadm.src_mem hr)
  · rw [add_rf, Function.update_of_ne hre] at hr
    exact Finset.mem_insert_of_mem (hM r s hr)

/-- `Supp` and `SrcMem` along printed operational paths. -/
theorem OpLe₀.supp_srcMem (h : OpLe₀ M P G G') (hS : G.Supp) (hM : G.SrcMem) :
    G'.Supp ∧ G'.SrcMem := by
  induction h with
  | refl => exact ⟨hS, hM⟩
  | tail _ hs ih => exact hs.supp_srcMem ih.1 ih.2

/-- A printed operational step into a consistent graph, from a graph with `Supp` and `SrcMem`,
adds a fresh event that is `porf`-maximal in the result; the source graph is the result without
it, hence consistent (Axiom 1), and the step is a premised operational step. -/
theorem OpStepG₀.back (h : OpStepG₀ M P X Y) (hS : X.Supp) (hM : X.SrcMem) (hY : M.cons Y) :
    M.cons X ∧ OpStepG M P X Y := by
  obtain ⟨e, src, out, ⟨hav, hadm⟩, rfl⟩ := h
  have hYw := M.wf _ hY
  obtain ⟨t, -, ht, -⟩ := M.mem_availM_iff'.mp hav
  have hidx := Model.idx_of_nextEv ht
  have he : e ∉ X.events := by
    intro hx
    have hev : (X.add e src out).events = X.events := by
      rw [add_events, Finset.insert_eq_of_mem hx]
    have hlt := hYw.idx_lt_cnt (Finset.mem_insert_self e X.events)
    have hc : (X.add e src out).cnt e.tid = X.cnt e.tid := by
      unfold Graph.cnt
      rw [hev]
    omega
  have hmax : ∀ b, ¬ (X.add e src out).porfStep e b := by
    rintro b (⟨-, hb, ht', hi⟩ | ⟨hb, hrf⟩)
    · have hlt := hYw.idx_lt_cnt hb
      simp only [cnt_add he, ht', ↓reduceIte] at hlt
      rw [ht'] at hidx
      omega
    · by_cases hbe : b = e
      · rw [hbe, add_rf, Function.update_self] at hrf
        exact he (hadm.src_mem hrf)
      · rw [add_rf, Function.update_of_ne hbe] at hrf
        exact he (hM b e hrf)
  have hX : (X.add e src out).remove {e} = X := by
    unfold Graph.remove
    rw [restrict_add_of_not_mem (by simp), hS.restrict_of_subset]
    intro x hx
    simp only [add_events, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨Or.inr hx, fun h => he (h ▸ hx)⟩
  have hcl := hYw.remove_closed (S := {e}) fun q hq b hb => by
    rw [Finset.mem_singleton] at hq
    subst hq
    exact absurd hb (hmax b)
  have hX' : M.cons X := by
    have := M.prefixClosed _ _ hY hcl
    rwa [← Graph.remove, hX] at this
  exact ⟨hX', e, src, out, ⟨hav, hadm, hY⟩, rfl⟩

/-- The M5 obligation recorded at M4, in its strong form: a printed operational path from a
graph with `Supp` and `SrcMem` into a consistent graph is a premised operational path, and its
source is consistent. -/
theorem OpLe₀.opLe_of_supp (h : OpLe₀ M P G G') (hS : G.Supp) (hM : G.SrcMem) :
    M.cons G' → OpLe M P G G' ∧ M.cons G := by
  induction h with
  | refl => exact fun hc => ⟨ReflTransGen.refl, hc⟩
  | tail h₁ hs ih =>
    intro hc
    obtain ⟨hS', hM'⟩ := OpLe₀.supp_srcMem h₁ hS hM
    obtain ⟨hX, hst⟩ := hs.back hS' hM' hc
    obtain ⟨ih1, ih2⟩ := ih hX
    exact ⟨ih1.tail hst, ih2⟩

/-- The M5 obligation recorded at M4: `M.cons G → M.cons G' → OpLe₀ M P G G' → OpLe M P G G'`.
Unpremised operational paths between consistent graphs are premised ones. -/
theorem OpLe₀.opLe (hG : M.cons G) (hG' : M.cons G') (h : OpLe₀ M P G G') : OpLe M P G G' :=
  (OpLe₀.opLe_of_supp h (M.wf _ hG).supp (M.wf _ hG).srcMem hG').1

/-- Between consistent graphs, operational reachability with and without the consistency
premise of each step coincide. -/
theorem opLe_iff_opLe₀ (hG : M.cons G) (hG' : M.cons G') : OpLe M P G G' ↔ OpLe₀ M P G G' :=
  ⟨OpLe.opLe₀, fun h => OpLe₀.opLe hG hG' h⟩

/-- Between consistent graphs, the larger an execution of `P`, unpremised operational
reachability is the causal-prefix order (Section 2b, "operational prefix"). -/
theorem opLe₀_iff_isPrefixOf (hG : M.cons G) (hG' : M.cons G') (hE' : P.Exec G') :
    OpLe₀ M P G G' ↔ G.IsPrefixOf G' :=
  (opLe_iff_opLe₀ hG hG').symm.trans (opLe_iff_isPrefixOf hG hG' hE')

/-! ### Lemmas A.9 and A.12 -/

/-- Lemma A.9 (Algorithmic well-formedness): a configuration reached by algorithmic steps is an
operational extension of `∅` (`G∅ ⊑ G`, Definition A.4: both graphs consistent executions and
`∅ →* G`, here with premised steps). Every model, every tie-break. -/
theorem ReachM.opLe_empty {tie : Tie Q} {c : Config Q} (h : ReachM M tie P c) :
    M.cons Graph.empty ∧ M.cons c.G ∧ P.Exec c.G ∧ OpLe M P Graph.empty c.G :=
  ⟨M.empty, h.sound.cons, h.sound.exec,
    isPrefixOf_opLe h.sound.cons h.sound.exec (Graph.empty_isPrefixOf _)⟩

/-- Lemma A.9 with the printed (unpremised) operational steps. -/
theorem ReachM.opLe₀_empty {tie : Tie Q} {c : Config Q} (h : ReachM M tie P c) :
    OpLe₀ M P Graph.empty c.G :=
  OpLe.opLe₀ (h.opLe_empty).2.2.2

/-- Lemma A.12 (Prefix closedness), with the printed operational steps. Under Definition A.4
(`⊑` relates consistent executions only) the printed lemma is tautological; here `→*` is
unpremised. Reading the first graph of the printed `G ⊑ G ⊑ G′` as `G∅` is an editorial
repair. On a path
`∅ →* G →* G'`, consistency of `G'` gives consistency of `G` (from Axiom 1). -/
theorem cons_of_opLe₀ (h₁ : OpLe₀ M P Graph.empty G) (h₂ : OpLe₀ M P G G') (hc : M.cons G') :
    M.cons G := by
  obtain ⟨hS, hM⟩ := OpLe₀.supp_srcMem h₁ Graph.supp_empty_graph Graph.srcMem_empty
  exact (OpLe₀.opLe_of_supp h₂ hS hM hc).2

/-! ### Lemma A.15 -/

omit [DecidableEq Q] in
/-- Every identity `(t, j)` with `j < G.cnt t` is the identity of an event of `G`. -/
theorem Graph.Wf.exists_of_lt_cnt (hG : G.Wf) {t : Tid} {j : ℕ} (hj : j < G.cnt t) :
    ∃ y ∈ G.events, y.tid = t ∧ y.idx = j :=
  (hG.exists_idx_iff t j).mpr hj

/-- In a causal-prefix extension `G'` of `G` that is a well-formed execution, a thread whose next
event `e` in `G` is not in `G'` has the same events in `G'` as in `G`. -/
theorem thread_eq_of_not_mem (hG : G.Wf) (hG' : G'.Wf) (hE' : P.Exec G')
    (hp : G.IsPrefixOf G') {t : Tid} (hn : P.nextEv G t = some e) (heG' : e ∉ G'.events)
    {x : Ev Q} (hx : x ∈ G'.events) (hxt : x.tid = t) : x ∈ G.events := by
  have hsub := hp.events_subset
  have hidx := Model.idx_of_nextEv hn
  have het : e.tid = t := by
    unfold Program.nextEv at hn
    obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.mp hn
    rfl
  by_contra hxG
  have hge : G.cnt t ≤ x.idx := by
    by_contra hlt
    obtain ⟨y, hy, hyt, hyi⟩ := hG.exists_of_lt_cnt (not_le.mp hlt)
    exact hxG (hG'.idx_inj y (hsub hy) x hx (hyt.trans hxt.symm) hyi ▸ hy)
  obtain ⟨x0, hx0, hx0t, hx0i⟩ : ∃ x0 ∈ G'.events, x0.tid = t ∧ x0.idx = G.cnt t := by
    rcases Nat.lt_or_eq_of_le hge with h | h
    · obtain ⟨x0, h1, h2, h3⟩ := hG'.idx_contig x hx _ h
      exact ⟨x0, h1, h2.trans hxt, h3⟩
    · exact ⟨x, hx, hxt, h.symm⟩
  have htr : G'.traceBefore t (G.cnt t) = G.trace t := by
    unfold trace
    refine traceBefore_congr fun j hj => (retAt_congr (fun y h1 h2 => ?_)
      (fun y hy h1 h2 => ?_)).symm
    · refine ⟨fun h => hsub h, fun h => ?_⟩
      obtain ⟨y', hy', h1', h2'⟩ := hG.exists_of_lt_cnt (h2 ▸ hj : y.idx < G.cnt t)
      rwa [← hG'.idx_inj y' (hsub hy') y h (h1'.trans h1.symm) h2']
    · exact ⟨(hp.rf_eq hy).symm ▸ rfl, (hp.nd_eq hy).symm ▸ rfl⟩
  have hl := hE' x0 hx0
  rw [hx0t, hx0i, htr] at hl
  unfold Program.nextEv at hn
  rw [hl] at hn
  simp only [Option.map_some, Option.some.injEq] at hn
  apply heG'
  rw [← hn]
  convert hx0 using 1
  cases x0
  simp_all

/-- Lemma A.15 (Event availability), repaired (plan Section 2b): for consistent graphs `G`, `G'`
with `G` a causal prefix of `G'` and `G'` an execution of `P`, an event available in `G` and not
in `G'` is available in `G'`. For a blocking receive, its unread matching send stays unread: a
reader in `G'` is a receive of the destination thread, which has no events outside `G`. Uses Q7
(`Model.mem_availM_iff`). Every model. -/
theorem availM_stable (hG : M.cons G) (hG' : M.cons G') (hE' : P.Exec G')
    (hp : G.IsPrefixOf G') (he : e ∈ M.availM P G) (heG' : e ∉ G'.events) :
    e ∈ M.availM P G' := by
  have hGw := M.wf _ hG
  have hG'w := M.wf _ hG'
  have hsub := hp.events_subset
  obtain ⟨t, ht, hn, hu⟩ := (M.mem_availM_iff hG).mp he
  have het : e.tid = t := by
    unfold Program.nextEv at hn
    obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.mp hn
    rfl
  have hthr := fun {x : Ev Q} (hx : x ∈ G'.events) (hxt : x.tid = t) =>
    thread_eq_of_not_mem hGw hG'w hE' hp hn heG' hx hxt
  have hcnt : G'.cnt t = G.cnt t := by
    unfold Graph.cnt
    congr 1
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨hthr h1 h2, h2⟩, fun ⟨h1, h2⟩ => ⟨hsub h1, h2⟩⟩
  have htr : G'.trace t = G.trace t := by
    unfold trace
    rw [hcnt]
    refine traceBefore_congr fun j hj => (retAt_congr (fun y h1 h2 => ?_)
      (fun y hy h1 h2 => ?_)).symm
    · exact ⟨fun h => hsub h, fun h => hthr h h1⟩
    · exact ⟨(hp.rf_eq hy).symm ▸ rfl, (hp.nd_eq hy).symm ▸ rfl⟩
  have hn' : P.nextEv G' t = some e := by
    unfold Program.nextEv at hn ⊢
    rw [htr, hcnt]
    exact hn
  refine (M.mem_availM_iff hG').mpr ⟨t, ht, hn', ?_⟩
  rcases hu with hu | ⟨s, hs, hm⟩
  · exact Or.inl hu
  · refine Or.inr ⟨s, ?_, hm⟩
    obtain ⟨hs1, hs2, hs3⟩ := (G.mem_US).mp hs
    refine (G'.mem_US).mpr ⟨hsub hs1, hs2, fun q hq hrf => ?_⟩
    have hmq := hG'w.rf_match _ _ hrf
    obtain ⟨m1, v1, h1⟩ := hm.dst
    obtain ⟨m2, v2, h2⟩ := hmq.dst
    have hqt : q.tid = t := by
      have h12 := h1.symm.trans h2
      simp only [Lab.send.injEq] at h12
      rw [← h12.2.1, het]
    have hqG := hthr hq hqt
    exact hs3 q hqG (by rw [hp.rf_eq hqG]; exact hrf)

/-- Lemma A.15 for an unpremised operational path between consistent graphs. -/
theorem availM_stable_opLe₀ (hG : M.cons G) (hE : P.Exec G) (hG' : M.cons G')
    (h : OpLe₀ M P G G') (he : e ∈ M.availM P G) (heG' : e ∉ G'.events) :
    e ∈ M.availM P G' := by
  have h' := OpLe₀.opLe hG hG' h
  exact availM_stable hG hG' (h'.exec hG hE) (h'.isPrefixOf hG).1 he heG'

end Must

#print axioms Must.OpStepG₀.back
#print axioms Must.OpLe₀.opLe_of_supp
#print axioms Must.OpLe₀.opLe
#print axioms Must.opLe_iff_opLe₀
#print axioms Must.opLe₀_iff_isPrefixOf
#print axioms Must.ReachM.opLe_empty
#print axioms Must.ReachM.opLe₀_empty
#print axioms Must.cons_of_opLe₀
#print axioms Must.thread_eq_of_not_mem
#print axioms Must.availM_stable
#print axioms Must.availM_stable_opLe₀
