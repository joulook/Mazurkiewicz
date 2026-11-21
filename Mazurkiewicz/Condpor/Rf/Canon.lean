import Mazurkiewicz.Condpor.Explore
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Pairing

/-!
# Graphs without a coherence order

The reads-from version of the algorithm (TruSt, Section 4.2, Algorithm 2)
works on graphs that do not record the coherence order. Here such a graph is
a graph of the development whose coherence order is *canonical*: for every
location, the thread writes sorted by a fixed total order on events. Two
graphs that agree on everything but coherence (`RfEq`) have the same
canonical form.

* `Model.rf M`: consistency of a graph without coherence: some coherence
  order makes it `M`-consistent.
* `CoChoice M`: a function that chooses such an order (the paper's
  `GetConsCO`), as a function of the graph without its coherence order.
* `Config.star γ c r w`: the configuration `c` with the coherence order of
  line 16 of Algorithm 2 for the revisit of `r` by `w`: the order that `γ`
  chooses for the kept events without `r`, followed by the deleted writes in
  insertion order. (TruSt computes the order on the kept events *with* `r`;
  see the plan, row D-rfco, for why that depends on the old source of `r`.)
-/

namespace Condpor

/-! ### A total order on events -/

/-- An injective code of thread events. -/
def TEv.key (e : TEv) : ℕ :=
  Nat.pair e.tid (Nat.pair e.idx (Nat.pair e.act.code.1 (Nat.pair e.act.code.2.1 e.act.code.2.2)))

theorem TEv.key_injective : Function.Injective TEv.key := by
  rintro ⟨t, i, a⟩ ⟨t', i', a'⟩ h
  simp only [TEv.key, Nat.pair_eq_pair] at h
  obtain ⟨rfl, rfl, h1, h2, h3⟩ := h
  have : a = a' := Act.code_injective (Prod.ext h1 (Prod.ext h2 h3))
  rw [this]

/-- The order of the canonical coherence lists. -/
def keyLe (a b : TEv) : Prop := a.key ≤ b.key

instance : DecidableRel keyLe := fun a b => inferInstanceAs (Decidable (a.key ≤ b.key))
instance : IsTrans TEv keyLe := ⟨fun _ _ _ => Nat.le_trans⟩
instance : Std.Antisymm keyLe := ⟨fun _ _ h1 h2 => TEv.key_injective (Nat.le_antisymm h1 h2)⟩
instance : Std.Total keyLe := ⟨fun a b => Nat.le_total a.key b.key⟩

/-- The canonical coherence list of location `x` for the events `E`. -/
def canonCo (E : Finset TEv) (x : Loc) : List TEv :=
  (E.filter (fun e => e.writesTo x = true)).sort keyLe

theorem mem_canonCo {E : Finset TEv} {x : Loc} {e : TEv} :
    e ∈ canonCo E x ↔ e ∈ E ∧ ∃ v, e.act = .write x v := by
  simp [canonCo, Finset.mem_sort, TEv.writesTo_iff]

theorem canonCo_nodup (E : Finset TEv) (x : Loc) : (canonCo E x).Nodup := Finset.sort_nodup _ _

theorem canonCo_pairwise (E : Finset TEv) (x : Loc) : (canonCo E x).Pairwise keyLe :=
  Finset.pairwise_sort _ _

/-- A sorted list without repetition with the elements of the canonical list
is the canonical list. -/
theorem eq_canonCo {E : Finset TEv} {x : Loc} {l : List TEv} (hp : l.Pairwise keyLe)
    (hnd : l.Nodup) (hmem : ∀ e, e ∈ l ↔ e ∈ E ∧ ∃ v, e.act = .write x v) : l = canonCo E x :=
  List.Perm.eq_of_pairwise' hp (canonCo_pairwise E x)
    ((List.perm_ext_iff_of_nodup hnd (canonCo_nodup E x)).mpr
      (fun e => by rw [hmem, mem_canonCo]))

theorem canonCo_filter (E s : Finset TEv) (x : Loc) :
    (canonCo E x).filter (fun e => e ∈ s) = canonCo (E ∩ s) x := by
  refine eq_canonCo ((canonCo_pairwise E x).filter _) ((canonCo_nodup E x).filter _) (fun e => ?_)
  simp only [List.mem_filter, mem_canonCo, decide_eq_true_eq, Finset.mem_inter]
  tauto

theorem canonCo_congr {E E' : Finset TEv} {x : Loc}
    (h : ∀ e, (∃ v, e.act = .write x v) → (e ∈ E ↔ e ∈ E')) : canonCo E x = canonCo E' x := by
  refine eq_canonCo (canonCo_pairwise E x) (canonCo_nodup E x) (fun e => ?_)
  rw [mem_canonCo]
  constructor
  · rintro ⟨he, hw⟩
    exact ⟨(h e hw).mp he, hw⟩
  · rintro ⟨he, hw⟩
    exact ⟨(h e hw).mpr he, hw⟩

/-! ### Replacing the coherence order -/

namespace Graph

/-- `G` with the coherence order `co`. -/
def withCo (G : Graph) (co : Loc → List TEv) : Graph := ⟨G.mem, G.events, G.rf, co, G.pol⟩

/-- The canonical form of `G`. -/
def canon (G : Graph) : Graph := G.withCo (canonCo G.events)

/-- The coherence order of `G` is canonical. -/
def IsCanon (G : Graph) : Prop := G.co = canonCo G.events

/-- `G` and `G'` agree on everything but the coherence order: the same graph
under the reads-from partitioning. -/
def RfEq (G G' : Graph) : Prop :=
  G.mem = G'.mem ∧ G.events = G'.events ∧ G.rf = G'.rf ∧ G.pol = G'.pol

@[simp] theorem withCo_mem (G : Graph) (co : Loc → List TEv) : (G.withCo co).mem = G.mem := rfl
@[simp] theorem withCo_events (G : Graph) (co : Loc → List TEv) :
    (G.withCo co).events = G.events := rfl
@[simp] theorem withCo_rf (G : Graph) (co : Loc → List TEv) : (G.withCo co).rf = G.rf := rfl
@[simp] theorem withCo_co (G : Graph) (co : Loc → List TEv) : (G.withCo co).co = co := rfl
@[simp] theorem withCo_pol (G : Graph) (co : Loc → List TEv) : (G.withCo co).pol = G.pol := rfl
@[simp] theorem withCo_withCo (G : Graph) (co co' : Loc → List TEv) :
    (G.withCo co).withCo co' = G.withCo co' := rfl
@[simp] theorem withCo_self (G : Graph) : G.withCo G.co = G := rfl

@[simp] theorem canon_events (G : Graph) : G.canon.events = G.events := rfl
@[simp] theorem canon_rf (G : Graph) : G.canon.rf = G.rf := rfl
@[simp] theorem canon_pol (G : Graph) : G.canon.pol = G.pol := rfl
@[simp] theorem canon_mem (G : Graph) : G.canon.mem = G.mem := rfl

theorem canon_isCanon (G : Graph) : G.canon.IsCanon := rfl

theorem IsCanon.canon_eq {G : Graph} (h : G.IsCanon) : G.canon = G := by
  unfold canon
  rw [← h]
  rfl

@[simp] theorem withCo_canon (G : Graph) (co : Loc → List TEv) : (G.withCo co).canon = G.canon :=
  rfl

theorem rfEq_canon (G : Graph) : G.RfEq G.canon := ⟨rfl, rfl, rfl, rfl⟩

theorem RfEq.canon_eq {G G' : Graph} (h : G.RfEq G') : G.canon = G'.canon := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  apply Graph.ext
  · exact h1
  · exact h2
  · exact h3
  · change canonCo G.events = canonCo G'.events
    rw [h2]
  · exact h4

theorem rfEq_iff_canon_eq {G G' : Graph} : G.RfEq G' ↔ G.canon = G'.canon := by
  refine ⟨RfEq.canon_eq, fun h => ?_⟩
  have h1 : G.canon.mem = G'.canon.mem := by rw [h]
  have h2 : G.canon.events = G'.canon.events := by rw [h]
  have h3 : G.canon.rf = G'.canon.rf := by rw [h]
  have h4 : G.canon.pol = G'.canon.pol := by rw [h]
  exact ⟨h1, h2, h3, h4⟩

/-- Replacing the coherence order by lists of the writes keeps
well-formedness. -/
theorem Wf.withCo {G : Graph} (hG : G.Wf) {co : Loc → List TEv}
    (hmem : ∀ x e, e ∈ co x ↔ e ∈ G.events ∧ ∃ v, e.act = .write x v)
    (hnd : ∀ x, (co x).Nodup) : (G.withCo co).Wf where
  idx_inj := hG.idx_inj
  idx_contig := hG.idx_contig
  rf_read := hG.rf_read
  rf_none := hG.rf_none
  co_mem := hmem
  co_nodup := hnd
  pol_isSome := hG.pol_isSome

theorem Wf.canon {G : Graph} (hG : G.Wf) : G.canon.Wf :=
  hG.withCo (fun _ _ => mem_canonCo) (fun x => canonCo_nodup G.events x)

theorem withCo_restrict (G : Graph) (co : Loc → List TEv) (s : Finset TEv) :
    (G.withCo co).restrict s = (G.restrict s).withCo (fun x => (co x).filter (fun e => e ∈ s)) :=
  rfl

theorem canon_restrict (G : Graph) (s : Finset TEv) :
    G.canon.restrict s = (G.restrict s).canon := by
  rw [canon, withCo_restrict]
  unfold canon
  congr 1
  funext x
  exact canonCo_filter G.events s x

theorem IsCanon.restrict {G : Graph} (h : G.IsCanon) (s : Finset TEv) : (G.restrict s).IsCanon := by
  have := canon_restrict G s
  rw [h.canon_eq] at this
  rw [this]
  exact canon_isCanon _

@[simp] theorem withCo_porfStep (G : Graph) (co : Loc → List TEv) :
    (G.withCo co).porfStep = G.porfStep := rfl

@[simp] theorem withCo_porf (G : Graph) (co : Loc → List TEv) : (G.withCo co).porf = G.porf := rfl

@[simp] theorem withCo_F (G : Graph) (co : Loc → List TEv) : (G.withCo co).F = G.F := rfl

@[simp] theorem withCo_trace (G : Graph) (co : Loc → List TEv) (t : Tid) :
    (G.withCo co).trace t = G.trace t := rfl

@[simp] theorem withCo_cnt (G : Graph) (co : Loc → List TEv) (t : Tid) :
    (G.withCo co).cnt t = G.cnt t := rfl

theorem isPrefixOf_withCo {G' G : Graph} (co : Loc → List TEv) (h : G'.IsPrefixOf G) :
    ∃ co', (G'.withCo co').IsPrefixOf (G.withCo co) := by
  obtain ⟨s, hs, rfl⟩ := h
  exact ⟨fun x => (co x).filter (fun e => e ∈ s), s, hs, (withCo_restrict G co s).symm⟩

end Graph

theorem Program.avail_withCo (P : Program) (G : Graph) (co : Loc → List TEv) :
    P.avail (G.withCo co) = P.avail G := rfl

theorem Program.exec_withCo (P : Program) (G : Graph) (co : Loc → List TEv) :
    P.Exec (G.withCo co) ↔ P.Exec G := Iff.rfl

/-! ### Consistency without a coherence order -/

/-- Consistency of a graph without its coherence order: some coherence order
makes it `M`-consistent. -/
def Model.rf (M : Model) : Model where
  cons := fun G => ∃ co, (G.withCo co).Wf ∧ M.cons (G.withCo co)
  cons_init := fun μ => ⟨fun _ => [], Graph.init_wf μ, M.cons_init μ⟩
  porf_acyclic := fun G _ ⟨co, hW, hc⟩ => M.porf_acyclic (G.withCo co) hW hc
  prefix_closed := by
    rintro G G' - ⟨co, hW, hc⟩ ⟨s, hs, rfl⟩
    have hp : ((G.withCo co).restrict s).IsPrefixOf (G.withCo co) := ⟨s, hs, rfl⟩
    exact ⟨fun x => (co x).filter (fun e => e ∈ s), hW.of_isPrefixOf hp,
      M.prefix_closed _ _ hW hc hp⟩

theorem Model.rf_cons_iff {M : Model} {G : Graph} :
    M.rf.cons G ↔ ∃ co, (G.withCo co).Wf ∧ M.cons (G.withCo co) := Iff.rfl

theorem Model.rf_cons_of_cons {M : Model} {G : Graph} (hG : G.Wf) (hc : M.cons G) :
    M.rf.cons G := ⟨G.co, hG, hc⟩

theorem Model.rf_cons_withCo {M : Model} {G : Graph} (co : Loc → List TEv) :
    M.rf.cons (G.withCo co) ↔ M.rf.cons G := Iff.rfl

/-- A choice of a coherence order (the paper's `GetConsCO`): a function of the
graph without its coherence order that returns a coherence order, one for
which the graph is consistent if there is one. -/
structure CoChoice (M : Model) where
  /-- the chosen order -/
  co : Graph → Loc → List TEv
  /-- it is a coherence order of the graph -/
  wf : ∀ G : Graph, G.Wf → (G.withCo (co G)).Wf
  /-- the graph is consistent with it, if with any -/
  cons : ∀ G : Graph, G.Wf → M.rf.cons G → M.cons (G.withCo (co G))
  /-- it does not depend on the coherence order of the argument -/
  congr : ∀ (G : Graph) (c : Loc → List TEv), co (G.withCo c) = co G

/-- There is a choice for every model. -/
noncomputable def CoChoice.classical (M : Model) : CoChoice M where
  co := fun G => open Classical in
    if h : ∃ co, (G.withCo co).Wf ∧ M.cons (G.withCo co) then h.choose else canonCo G.events
  wf := by
    intro G hG
    by_cases h : ∃ co, (G.withCo co).Wf ∧ M.cons (G.withCo co)
    · simp only [h, ↓reduceDIte]
      exact h.choose_spec.1
    · simp only [h, ↓reduceDIte]
      exact hG.canon
  cons := by
    intro G _ h
    have h' : ∃ co, (G.withCo co).Wf ∧ M.cons (G.withCo co) := h
    simp only [h', ↓reduceDIte]
    exact h'.choose_spec.2
  congr := fun _ _ => rfl

/-- The graph with the chosen order. -/
def CoChoice.apply {M : Model} (γ : CoChoice M) (G : Graph) : Graph := G.withCo (γ.co G)

/-! ### Configurations -/

namespace Config

/-- `c` with the coherence order `co`. -/
def withCo (c : Config) (co : Loc → List TEv) : Config := ⟨c.mem, c.order, c.rf, co, c.pol⟩

@[simp] theorem withCo_abs (c : Config) (co : Loc → List TEv) :
    (c.withCo co).abs = c.abs.withCo co := rfl
@[simp] theorem withCo_order (c : Config) (co : Loc → List TEv) :
    (c.withCo co).order = c.order := rfl
@[simp] theorem withCo_rf (c : Config) (co : Loc → List TEv) : (c.withCo co).rf = c.rf := rfl
@[simp] theorem withCo_pol (c : Config) (co : Loc → List TEv) : (c.withCo co).pol = c.pol := rfl

/-- The canonical form of `c`. -/
def canon (c : Config) : Config := c.withCo (canonCo c.order.toFinset)

@[simp] theorem canon_abs (c : Config) : c.canon.abs = c.abs.canon := rfl
@[simp] theorem canon_order (c : Config) : c.canon.order = c.order := rfl

end Config

end Condpor
