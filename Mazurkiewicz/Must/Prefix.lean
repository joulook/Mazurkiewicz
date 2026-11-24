import Mazurkiewicz.Must.ReplayRev

/-!
# The operational prefix order `⊑` and its strict part `⊏` (milestone M6)

Paper: Definition A.4 (p. 30): for consistent executions `G`, `G'`, `G ⊑ G' ≜ G →* G'`; `⊏` is
used in Lemmas A.13, A.14, A.15, A.16 without a definition, read as `⊑` and `≠`. Plan:
`plan/must/lean/LEAN-PLAN.md`, Section 2b ("operational prefix"), decision Q13.

* `Pfx M P G G'` (`G ⊑ G'`): `G`, `G'` are `M`-consistent executions of `P` and `G` is the
  restriction of `G'` to a `porf`-closed set. By `pfx_iff_opLe` and `pfx_iff_opLe₀` this is
  Definition A.4 with premised or with printed (unpremised) operational steps.
* `SPfx M P G G'` (`G ⊏ G'`): `G ⊑ G'` and `G ≠ G'`; equivalently `G ⊑ G'` and `|G.E| < |G'.E|`
  (`sPfx_iff_card`), or `G ⊑ G'` and some event of `G'` is not in `G` (`sPfx_iff_exists`).
* Order facts: `Pfx.refl`, `Pfx.trans`, `Pfx.antisymm`; `sPfx_irrefl`, `SPfx.trans_pfx`,
  `Pfx.trans_sPfx`, `SPfx.trans`, `SPfx.card_lt`.
* `Pfx.of_between`: two prefixes of a common graph, the events of one contained in those of the
  other, are related by `⊑`. `Pfx.eq_of_events_eq`: a prefix of a graph is determined by its
  events.
* Closure tools: `Graph.closed_union`, `Graph.closed_insert` (adding an event all of whose
  causal steps come from the set), `Graph.closed_of_agree` (transfer of closedness from a graph
  `F` to a graph `H` that contains the events of the set in `F` with the sources of `F`),
  `Graph.closed_of_sub` (the events of a well-formed `X` contained in `H` with the sources of
  `X`), `Graph.Wf.closed_of_restrict_wf` (`H.Closed K` from well-formedness of `H|K`). These are
  the forms in which M7 discharges the conjunct `H.G.Closed K` of `revCond_iff_replay`.

All results hold for every model `M` and every program `P`.
-/

namespace Must

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q}

/-! ### Closure tools -/

namespace Graph

omit [Membership Val Q] in
/-- A union of closed sets is closed. -/
theorem closed_union {G : Graph Q} {A B : Finset (Ev Q)} (hA : G.Closed A) (hB : G.Closed B) :
    G.Closed (A ∪ B) := by
  intro a b hab hb
  have hb := Finset.mem_coe.mp hb
  rw [Finset.mem_inter, Finset.mem_union] at hb
  rcases hb with ⟨hbG, hbA | hbB⟩
  · have h := Finset.mem_inter.mp
      (Finset.mem_coe.mp (hA hab (Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨hbG, hbA⟩))))
    exact Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨h.1, Finset.mem_union_left _ h.2⟩)
  · have h := Finset.mem_inter.mp
      (Finset.mem_coe.mp (hB hab (Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨hbG, hbB⟩))))
    exact Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨h.1, Finset.mem_union_right _ h.2⟩)

/-- Adding to a closed set an event whose causal steps all come from the set keeps it closed. -/
theorem closed_insert {G : Graph Q} (hG : G.Wf) {A : Finset (Ev Q)} (hA : G.Closed A) {e : Ev Q}
    (he : ∀ a, G.porfStep a e → a ∈ A) : G.Closed (insert e A) := by
  intro a b hab hb
  have hb := Finset.mem_inter.mp (Finset.mem_coe.mp hb)
  have ha := (hG.mem_of_porfStep hab).1
  rcases Finset.mem_insert.mp hb.2 with rfl | hbA
  · exact Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨ha, Finset.mem_insert_of_mem (he a hab)⟩)
  · have h := Finset.mem_inter.mp
      (Finset.mem_coe.mp (hA hab (Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨hb.1, hbA⟩))))
    exact Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨ha, Finset.mem_insert_of_mem h.2⟩)

/-- Transfer of closedness. Let `K` be `porf`-closed in a well-formed `F`. If every event of `H`
in `K` is an event of `F`, and every event of `F` in `K` is an event of `H` with the source it has
in `F`, then `K` is `porf`-closed in a well-formed `H`. No order of insertion is involved: `po` is
determined by the identities, `rf` by the sources. -/
theorem closed_of_agree {H F : Graph Q} (hH : H.Wf) (hF : F.Wf) {K : Finset (Ev Q)}
    (hK : F.Closed K) (hHF : ∀ x ∈ H.events ∩ K, x ∈ F.events)
    (hFH : ∀ x ∈ F.events ∩ K, x ∈ H.events ∧ H.rf x = F.rf x) : H.Closed K := by
  intro a b hab hb
  have hb := Finset.mem_coe.mp hb
  have hbF : b ∈ F.events ∩ K := Finset.mem_inter.mpr ⟨hHF b hb, (Finset.mem_inter.mp hb).2⟩
  have haFK : a ∈ F.events ∩ K := by
    rcases hab with ⟨ha, -, ht, hi⟩ | ⟨-, hrf⟩
    · obtain ⟨a', ha', hat, hai⟩ := hF.idx_contig b (Finset.mem_inter.mp hbF).1 a.idx hi
      have ha'K := Finset.mem_coe.mp (hK (Or.inl ⟨ha', (Finset.mem_inter.mp hbF).1, hat,
        hai ▸ hi⟩) (Finset.mem_coe.mpr hbF))
      have h1 := (hFH a' ha'K).1
      have : a' = a := hH.idx_inj a' h1 a ha (hat.trans ht.symm) hai
      rwa [this] at ha'K
    · rw [(hFH b hbF).2] at hrf
      exact Finset.mem_coe.mp (hK (Or.inr ⟨(Finset.mem_inter.mp hbF).1, hrf⟩)
        (Finset.mem_coe.mpr hbF))
  exact Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨(hFH a haFK).1, (Finset.mem_inter.mp haFK).2⟩)

/-- Converse of `Wf.restrict`: if the restriction of a well-formed `H` to `K` is well-formed,
then `K` is `porf`-closed in `H` (a kept event keeps its thread predecessors by `idx_contig`, and
its source by `rf_mem`). This discharges `H.Closed K` from well-formedness of `H|K`. -/
theorem Wf.closed_of_restrict_wf {H : Graph Q} (hH : H.Wf) {K : Finset (Ev Q)}
    (hK : (H.restrict K).Wf) : H.Closed K := by
  intro a b hab hb
  have hb := Finset.mem_coe.mp hb
  refine Finset.mem_coe.mpr ?_
  rcases hab with ⟨ha, -, ht, hi⟩ | ⟨-, hrf⟩
  · obtain ⟨a', ha', hat, hai⟩ := hK.idx_contig b hb a.idx hi
    have ha'H := (Finset.mem_inter.mp ha').1
    rwa [hH.idx_inj a' ha'H a ha (hat.trans ht.symm) hai] at ha'
  · have h : (H.restrict K).rf b = some (.snd a) := by
      rw [restrict_rf, ite_eq_left_iff.mpr (fun h => absurd (Finset.mem_inter.mp hb).2 h)]
      exact hrf
    exact hK.rf_mem b a h

/-- A well-formed graph `X` whose events are events of a well-formed `H` with the same sources
has a `porf`-closed event set in `H`. -/
theorem closed_of_sub {H X : Graph Q} (hH : H.Wf) (hX : X.Wf)
    (h : ∀ x ∈ X.events, x ∈ H.events ∧ H.rf x = X.rf x) : H.Closed X.events := by
  refine closed_of_agree hH hX (fun a b hab hb => ?_) (fun x hx => (Finset.mem_inter.mp hx).2)
    (fun x hx => h x (Finset.mem_inter.mp hx).2)
  have ha := (hX.mem_of_porfStep hab).1
  exact Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨ha, ha⟩)

omit [Membership Val Q] in
/-- A prefix of a graph with `Supp` is the restriction of that graph to the prefix's events. -/
theorem IsPrefixOf.eq_restrict {G G' : Graph Q} (hG' : G'.Supp) (h : G.IsPrefixOf G') :
    G = G'.restrict G.events := by
  obtain ⟨E, -, rfl⟩ := h
  rw [restrict_events]
  exact hG'.restrict_congr fun x hx => by simp [hx]

omit [Membership Val Q] in
/-- Two prefixes `X`, `Y` of a graph `F` with `Supp`, with `X.E ⊆ Y.E`: `X` is a prefix of
`Y`. -/
theorem IsPrefixOf.of_between {X Y F : Graph Q} (hF : F.Supp) (hX : X.IsPrefixOf F)
    (hY : Y.IsPrefixOf F) (hsub : X.events ⊆ Y.events) : X.IsPrefixOf Y := by
  have hXr := hX.eq_restrict hF
  have hcl := hX.closed_events
  obtain ⟨EY, -, rfl⟩ := hY
  refine ⟨X.events, fun a b hab hb => ?_, ?_⟩
  · have hb := Finset.mem_inter.mp (Finset.mem_coe.mp hb)
    have hb1 := Finset.mem_inter.mp hb.1
    have h := Finset.mem_inter.mp (Finset.mem_coe.mp (hcl (porfStep_restrict_le EY hab)
      (Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨hb1.1, hb.2⟩))))
    exact Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨hsub h.2, h.2⟩)
  · rw [restrict_restrict]
    refine hXr.trans (hF.restrict_congr fun x _ =>
      ⟨fun h => ?_, fun h => (Finset.mem_inter.mp h).2⟩)
    have h' := hsub h
    rw [restrict_events, Finset.mem_inter] at h'
    exact Finset.mem_inter.mpr ⟨h'.2, h⟩

end Graph

omit [Membership Val Q] in
/-- A prefix of an execution of `P` is an execution of `P`. -/
theorem Program.exec_of_isPrefixOf {G G' : Graph Q} (hE : P.Exec G') (hp : G.IsPrefixOf G') :
    P.Exec G := by
  obtain ⟨E, hE', rfl⟩ := hp
  refine Program.exec_restrict hE fun a b hab hb => ?_
  have := Finset.mem_coe.mp (hE' (Or.inl hab)
    (Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨hab.2.1, hb⟩)))
  exact (Finset.mem_inter.mp this).2

/-! ### `⊑` and `⊏` -/

/-- `G ⊑ G'` (Definition A.4, plan Section 2b): `G`, `G'` are `M`-consistent executions of `P`
and `G` is the restriction of `G'` to a `porf`-closed set. -/
structure Pfx (M : Model Q) (P : Program Q) (G G' : Graph Q) : Prop where
  /-- `G` is consistent -/
  cons : M.cons G
  /-- `G` is an execution of `P` -/
  exec : P.Exec G
  /-- `G'` is consistent -/
  cons' : M.cons G'
  /-- `G'` is an execution of `P` -/
  exec' : P.Exec G'
  /-- `G` is a causal prefix of `G'` -/
  pre : G.IsPrefixOf G'

/-- `G ⊏ G'`: `G ⊑ G'` and `G ≠ G'`. -/
def SPfx (M : Model Q) (P : Program Q) (G G' : Graph Q) : Prop := Pfx M P G G' ∧ G ≠ G'

variable {G G' G'' X Y : Graph Q}

/-- A causal prefix of a consistent execution is below it. -/
theorem Pfx.of_isPrefixOf (hc : M.cons G') (hE : P.Exec G') (hp : G.IsPrefixOf G') :
    Pfx M P G G' :=
  ⟨M.cons_of_isPrefixOf hc hp, Program.exec_of_isPrefixOf hE hp, hc, hE, hp⟩

/-- Definition A.4 with premised operational steps. -/
theorem pfx_iff_opLe :
    Pfx M P G G' ↔ M.cons G ∧ M.cons G' ∧ P.Exec G' ∧ OpLe M P G G' := by
  constructor
  · intro h
    exact ⟨h.cons, h.cons', h.exec', (opLe_iff_isPrefixOf h.cons h.cons' h.exec').mpr h.pre⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact Pfx.of_isPrefixOf h2 h3 ((opLe_iff_isPrefixOf h1 h2 h3).mp h4)

/-- Definition A.4 with the printed (unpremised) operational steps. -/
theorem pfx_iff_opLe₀ :
    Pfx M P G G' ↔ M.cons G ∧ M.cons G' ∧ P.Exec G' ∧ OpLe₀ M P G G' := by
  constructor
  · intro h
    exact ⟨h.cons, h.cons', h.exec', (opLe₀_iff_isPrefixOf h.cons h.cons' h.exec').mpr h.pre⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact Pfx.of_isPrefixOf h2 h3 ((opLe₀_iff_isPrefixOf h1 h2 h3).mp h4)

theorem Pfx.wf (h : Pfx M P G G') : G.Wf := M.wf _ h.cons

theorem Pfx.wf' (h : Pfx M P G G') : G'.Wf := M.wf _ h.cons'

theorem Pfx.events_subset (h : Pfx M P G G') : G.events ⊆ G'.events := h.pre.events_subset

theorem Pfx.closed (h : Pfx M P G G') : G'.Closed G.events := h.pre.closed_events

theorem Pfx.rf_eq (h : Pfx M P G G') {x : Ev Q} (hx : x ∈ G.events) : G.rf x = G'.rf x :=
  h.pre.rf_eq hx

theorem Pfx.nd_eq (h : Pfx M P G G') {x : Ev Q} (hx : x ∈ G.events) : G.nd x = G'.nd x :=
  h.pre.nd_eq hx

theorem Pfx.eq_restrict (h : Pfx M P G G') : G = G'.restrict G.events :=
  h.pre.eq_restrict h.wf'.supp

theorem Pfx.refl (hc : M.cons G) (hE : P.Exec G) : Pfx M P G G :=
  ⟨hc, hE, hc, hE, (M.wf _ hc).isPrefixOf_refl⟩

theorem Pfx.trans (h₁ : Pfx M P G G') (h₂ : Pfx M P G' G'') : Pfx M P G G'' :=
  ⟨h₁.cons, h₁.exec, h₂.cons', h₂.exec', h₁.pre.trans h₂.pre⟩

theorem Pfx.antisymm (h₁ : Pfx M P G G') (h₂ : Pfx M P G' G) : G = G' :=
  IsPrefixOf.antisymm h₁.wf' h₁.pre h₂.pre

/-- A prefix that has all the events of the larger graph is the larger graph. -/
theorem Pfx.eq_of_subset (h : Pfx M P G G') (hs : G'.events ⊆ G.events) : G = G' := by
  have hw := h.wf'
  obtain ⟨E, -, rfl⟩ := h.pre
  exact hw.restrict_of_subset fun x hx => (Finset.mem_inter.mp (hs hx)).2

/-- Two prefixes of `F`, the events of the first among those of the second, are related by
`⊑`. -/
theorem Pfx.of_between {F : Graph Q} (hX : Pfx M P X F) (hY : Pfx M P Y F)
    (hsub : X.events ⊆ Y.events) : Pfx M P X Y :=
  ⟨hX.cons, hX.exec, hY.cons, hY.exec, IsPrefixOf.of_between hX.wf'.supp hX.pre hY.pre hsub⟩

/-- A prefix of `F` is determined by its events. -/
theorem Pfx.eq_of_events_eq {F : Graph Q} (hX : Pfx M P X F) (hY : Pfx M P Y F)
    (h : X.events = Y.events) : X = Y := by
  rw [hX.eq_restrict, hY.eq_restrict, h]

theorem SPfx.pfx (h : SPfx M P G G') : Pfx M P G G' := h.1

theorem SPfx.ne (h : SPfx M P G G') : G ≠ G' := h.2

/-- `⊏` is irreflexive. -/
theorem sPfx_irrefl : ¬ SPfx M P G G := fun h => h.2 rfl

/-- `⊏` strictly increases the number of events. -/
theorem SPfx.card_lt (h : SPfx M P G G') : G.events.card < G'.events.card :=
  IsPrefixOf.card_lt h.1.wf' h.1.pre h.2

/-- `G ⊏ G'` iff `G ⊑ G'` with strictly fewer events. -/
theorem sPfx_iff_card : SPfx M P G G' ↔ Pfx M P G G' ∧ G.events.card < G'.events.card :=
  ⟨fun h => ⟨h.1, h.card_lt⟩, fun h => ⟨h.1, fun he => by rw [he] at h; exact lt_irrefl _ h.2⟩⟩

/-- `G ⊏ G'` iff `G ⊑ G'` and `G'` has an event outside `G`. -/
theorem sPfx_iff_exists :
    SPfx M P G G' ↔ Pfx M P G G' ∧ ∃ x ∈ G'.events, x ∉ G.events := by
  constructor
  · rintro ⟨h, hne⟩
    refine ⟨h, ?_⟩
    by_contra hall
    exact hne (h.eq_of_subset fun x hx => by_contra fun hxG => hall ⟨x, hx, hxG⟩)
  · rintro ⟨h, x, hx, hxG⟩
    exact ⟨h, fun he => hxG (he ▸ hx)⟩

theorem SPfx.trans_pfx (h₁ : SPfx M P G G') (h₂ : Pfx M P G' G'') : SPfx M P G G'' := by
  refine ⟨h₁.1.trans h₂, fun he => h₁.2 ?_⟩
  subst he
  exact h₁.1.antisymm h₂

theorem Pfx.trans_sPfx (h₁ : Pfx M P G G') (h₂ : SPfx M P G' G'') : SPfx M P G G'' := by
  refine ⟨h₁.trans h₂.1, fun he => h₂.2 ?_⟩
  subst he
  exact h₂.1.antisymm h₁

theorem SPfx.trans (h₁ : SPfx M P G G') (h₂ : SPfx M P G' G'') : SPfx M P G G'' :=
  h₁.trans_pfx h₂.1

/-- `⊏` is asymmetric. -/
theorem SPfx.asymm (h : SPfx M P G G') : ¬ SPfx M P G' G :=
  fun h' => sPfx_irrefl (h.trans h')

end Must

#print axioms Must.Graph.closed_union
#print axioms Must.Graph.closed_insert
#print axioms Must.Graph.closed_of_agree
#print axioms Must.Graph.Wf.closed_of_restrict_wf
#print axioms Must.Graph.closed_of_sub
#print axioms Must.Graph.IsPrefixOf.eq_restrict
#print axioms Must.Graph.IsPrefixOf.of_between
#print axioms Must.Program.exec_of_isPrefixOf
#print axioms Must.Pfx.of_isPrefixOf
#print axioms Must.pfx_iff_opLe
#print axioms Must.pfx_iff_opLe₀
#print axioms Must.Pfx.trans
#print axioms Must.Pfx.antisymm
#print axioms Must.Pfx.eq_of_subset
#print axioms Must.Pfx.of_between
#print axioms Must.Pfx.eq_of_events_eq
#print axioms Must.sPfx_irrefl
#print axioms Must.SPfx.card_lt
#print axioms Must.sPfx_iff_card
#print axioms Must.sPfx_iff_exists
#print axioms Must.SPfx.trans_pfx
#print axioms Must.Pfx.trans_sPfx
#print axioms Must.SPfx.trans
#print axioms Must.SPfx.asymm
