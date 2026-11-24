import Mazurkiewicz.Must.Model

/-!
# The four models and their combination (Definitions 3.4–3.8, Q4, Q5)

Paper: Section 3.2, Definitions 3.4–3.8; Section 3.2.1. Plan: decisions Q4, Q5, Q11.

* `ConsOf ms G` (Definition 3.8 for the models of `ms`, Q4): `G` is well-formed, and for each
  model of `ms` among `p2p`, `cd`, `mbox`, conditions (b), (c) hold with its order:
  `soP2P G` (`[S^p2p]; po; [S^p2p]`), `soCD G` (`[S^cd]; porf; [S^cd]`), and for `mbox` some
  `L` with `MboxOrd G L` (Q5). `po` and `porf` are those of the whole graph (global causality).
  `asyn` has no condition beyond well-formedness (Definition 3.4).
* `Model.ofSet ms`: the model interface for `ConsOf ms`, all fields proved once for every `ms`
  (`consOf_empty`, `Wf.consOf_restrict`, `ConsOf.add_plain`, `ConsOf.ext_recv`).
* Instances: `Model.single m` for one model `m` (`asyn`, `p2p`, `cd`, `mbox`) and `comb`
  (all four models, Definition 3.8 with Q4). The named theorems `*_prefixClosed`, `*_condExt`,
  `*_condExt_recv` are these instances of the general ones.
* `ConsOf.ext_recv` is stronger than the interface's `ext_recvB`: it holds for every receive,
  blocking or not. The proof reads an `so`-minimal unread matching send (`M0-astra.md` item 12).
* Agreement with M2: `asyn_cons_iff` (`ConsAsyn`), `p2p_cons_iff` (`ConsAP`), and
  `asyn_availM`, `p2p_availM`: M2's `availM` with `consAsynB`, `consAPB` is the interface's
  (`cd_availM`: the same for `consCDB`).
* `comb_cons_iff_used`: Definition 3.8 "for each model M used": `comb` is well-formedness and the
  condition of every model of which the graph has an event.
* `consCDB`: a decision procedure for `cd` (`consCDB_iff`); `mbox_bc_porf`: a decidable necessary
  condition for `mbox` (the order `porf` between mailbox sends).
-/

namespace Must

namespace Graph

open Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]

/-- Definition 3.8 for the models of `ms` (Q4, Q5): well-formed, and conditions (b), (c) of each
model of `ms` with global `po`, `porf`. -/
def ConsOf (ms : Comm → Prop) (G : Graph Q) : Prop :=
  G.Wf ∧ (ms .p2p → G.BC G.soP2P) ∧ (ms .cd → G.BC G.soCD) ∧
    (ms .mbox → ∃ L, G.MboxOrd L ∧ G.BC (soMbox L))

/-- The union of the orders of the three models (for an order `L` of `mbox`). -/
def soAll (G : Graph Q) (L : Ev Q → Ev Q → Prop) (a b : Ev Q) : Prop :=
  G.soP2P a b ∨ G.soCD a b ∨ soMbox L a b

/-- `L` extended by the new event `e` as greatest element. -/
def extOrd (G : Graph Q) (e : Ev Q) (L : Ev Q → Ev Q → Prop) (a b : Ev Q) : Prop :=
  (L a b ∧ a ∈ G.events ∧ b ∈ G.events) ∨ (a ∈ G.events ∧ b = e)

variable {G : Graph Q}

/-! ### The orders -/

omit [DecidableEq Q] [Membership Val Q] in
/-- An order of a model relates sends of the same model. -/
theorem soAll_model {L : Ev Q → Ev Q → Prop} {a b : Ev Q} (h : G.soAll L a b) :
    a.IsSend ∧ a.lab.model? = b.lab.model? := by
  rcases h with ⟨ha, hb, -⟩ | ⟨ha, hb, -⟩ | ⟨ha, hb, -⟩ <;> exact ⟨ha.1, ha.2.trans hb.2.symm⟩

omit [DecidableEq Q] [Membership Val Q] in
/-- `po` is transitive. -/
theorem po_trans {a b c : Ev Q} (h1 : G.po a b) (h2 : G.po b c) : G.po a c :=
  ⟨h1.1, h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.trans h2.2.2.2⟩

omit [DecidableEq Q] in
/-- The union of the orders is irreflexive on the events. -/
theorem Wf.soAll_irrefl (hG : G.Wf) {L : Ev Q → Ev Q → Prop}
    (hLi : ∀ a, G.MboxSend a → ¬ L a a) {a : Ev Q} (ha : a ∈ G.events) : ¬ G.soAll L a a := by
  rintro (⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨h1, -, h⟩)
  · exact lt_irrefl _ h.2.2.2
  · exact hG.porf_irrefl a h
  · exact hLi a ⟨ha, h1⟩ h

omit [DecidableEq Q] [Membership Val Q] in
/-- The union of the orders is transitive on the events. -/
theorem soAll_trans {L : Ev Q → Ev Q → Prop}
    (hLt : ∀ a b c, G.MboxSend a → G.MboxSend b → G.MboxSend c → L a b → L b c → L a c)
    {a b c : Ev Q} (ha : a ∈ G.events) (hb : b ∈ G.events) (hc : c ∈ G.events)
    (h1 : G.soAll L a b) (h2 : G.soAll L b c) : G.soAll L a c := by
  rcases h1 with ⟨ha1, hb1, h1⟩ | ⟨ha1, hb1, h1⟩ | ⟨ha1, hb1, h1⟩ <;>
    rcases h2 with ⟨hb2, hc2, h2⟩ | ⟨hb2, hc2, h2⟩ | ⟨hb2, hc2, h2⟩
  · exact Or.inl ⟨ha1, hc2, po_trans h1 h2⟩
  all_goals first
    | exact Or.inr (Or.inl ⟨ha1, hc2, porf_trans h1 h2⟩)
    | exact Or.inr (Or.inr ⟨ha1, hc2, hLt a b c ⟨ha, ha1⟩ ⟨hb, hb1⟩ ⟨hc, hc2⟩ h1 h2⟩)
    | exact Comm.noConfusion (Option.some.inj (hb1.2.symm.trans hb2.2))

/-! ### Restriction -/

/-- The empty graph satisfies (b), (c) for every order. -/
theorem bc_empty (so : Ev Q → Ev Q → Prop) : (empty : Graph Q).BC so :=
  ⟨fun s' hs' => absurd ((mem_US _).mp hs').1 (by simp [empty]),
    fun r hr => absurd hr (by simp [empty])⟩

/-- The empty graph is consistent. -/
theorem consOf_empty (ms : Comm → Prop) : ConsOf ms (empty : Graph Q) := by
  refine ⟨empty_wf, fun _ => bc_empty _, fun _ => bc_empty _,
    fun _ => ⟨fun _ _ => False, ⟨?_, ?_, ?_, ?_⟩, bc_empty _⟩⟩ <;>
    simp [MboxSend, empty]

/-- Prefix-closedness, for every set of models. -/
theorem Wf.consOf_restrict {ms : Comm → Prop} (h : ConsOf ms G) {E : Finset (Ev Q)}
    (hE : G.Closed E) : ConsOf ms (G.restrict E) := by
  have hG := h.1
  refine ⟨hG.restrict hE, fun hm => ?_, fun hm => ?_, fun hm => ?_⟩
  · exact (hG.bc_restrict hE (h.2.1 hm)).mono
      fun a _ b _ ⟨x, y, z⟩ => ⟨x, y, (po_restrict_iff.mp z).1⟩
  · exact (hG.bc_restrict hE (h.2.2.1 hm)).mono
      fun a _ b _ ⟨x, y, z⟩ => ⟨x, y, porf_restrict_le E z⟩
  · obtain ⟨L, hL, hb⟩ := h.2.2.2 hm
    have hms : ∀ a, (G.restrict E).MboxSend a → G.MboxSend a :=
      fun a ⟨ha, h'⟩ => ⟨(Finset.mem_inter.mp ha).1, h'⟩
    refine ⟨L, ⟨fun a ha => hL.irrefl a (hms a ha),
      fun a b c ha hb hc => hL.trans a b c (hms a ha) (hms b hb) (hms c hc),
      fun a b ha hb => hL.total a b (hms a ha) (hms b hb),
      fun a b ha hb hab => hL.porf a b (hms a ha) (hms b hb) (porf_restrict_le E hab)⟩,
      hG.bc_restrict hE hb⟩

/-! ### Extension -/

variable {e : Ev Q} {src : Option (Src Q)} {out : Option Val}

/-- The extension of an order of `mbox` by a new event is an order of `mbox` of the
extension. -/
theorem Wf.mboxOrd_add (hG : G.Wf) (hidx : e.idx = G.cnt e.tid) (hG' : (G.add e src out).Wf)
    {L : Ev Q → Ev Q → Prop} (hL : G.MboxOrd L) : (G.add e src out).MboxOrd (G.extOrd e L) := by
  have he := hG.not_mem_of_idx_eq_cnt hidx
  have hsrc : ∀ s, src = some (.snd s) → s ∈ G.events :=
    fun s hs => ((G.mem_US).mp (hG.src_of_add hidx hG' hs).1).1
  have hmem : ∀ a, a ∈ (G.add e src out).events → a ≠ e → a ∈ G.events := fun a ha hae => by
    rw [add_events, Finset.mem_insert] at ha
    exact ha.resolve_left hae
  have hms : ∀ a, (G.add e src out).MboxSend a → a ≠ e → G.MboxSend a :=
    fun a ha hae => ⟨hmem a ha.1 hae, ha.2⟩
  refine ⟨fun a ha => ?_, fun a b c ha hb hc => ?_, fun a b ha hb hne => ?_,
    fun a b ha hb hab => ?_⟩
  · rintro (⟨h, haG, -⟩ | ⟨haG, hae⟩)
    · exact hL.irrefl a ⟨haG, ha.2⟩ h
    · exact he (hae ▸ haG)
  · rintro (⟨h1, haG, hbG⟩ | ⟨haG, hbe⟩) (⟨h2, hbG', hcG⟩ | ⟨hbG', hce⟩)
    · exact Or.inl ⟨hL.trans a b c ⟨haG, ha.2⟩ ⟨hbG, hb.2⟩ ⟨hcG, hc.2⟩ h1 h2, haG, hcG⟩
    · exact Or.inr ⟨haG, hce⟩
    · exact absurd (hbe ▸ hbG') he
    · exact absurd (hbe ▸ hbG') he
  · by_cases hae : a = e
    · have hbe : b ≠ e := fun h' => hne (hae.trans h'.symm)
      exact Or.inr (Or.inr ⟨hmem b hb.1 hbe, hae⟩)
    · by_cases hbe : b = e
      · exact Or.inl (Or.inr ⟨hmem a ha.1 hae, hbe⟩)
      · rcases hL.total a b (hms a ha hae) (hms b hb hbe) hne with h | h
        · exact Or.inl (Or.inl ⟨h, hmem a ha.1 hae, hmem b hb.1 hbe⟩)
        · exact Or.inr (Or.inl ⟨h, hmem b hb.1 hbe, hmem a ha.1 hae⟩)
  · by_cases hbe : b = e
    · have hae : a ≠ e := by
        intro h'
        rw [h', hbe] at hab
        exact hG'.porf_irrefl e hab
      exact Or.inr ⟨hmem a ha.1 hae, hbe⟩
    · have h' := (hG.porf_add_iff hidx hsrc hbe).mp hab
      obtain ⟨haG, hbG⟩ := hG.mem_of_porf h'
      exact Or.inl ⟨hL.porf a b ⟨haG, ha.2⟩ ⟨hbG, hb.2⟩ h', haG, hbG⟩

/-- Consistency survives the addition of the next event of a thread when the extension is
well-formed and a new source has no predecessor, in the union of the orders, among the unread
sends matching the new receive in destination and value. -/
theorem Wf.consOf_add {ms : Comm → Prop} (hG : G.Wf) (hidx : e.idx = G.cnt e.tid)
    (hG' : (G.add e src out).Wf) (hp : ms .p2p → G.BC G.soP2P) (hc : ms .cd → G.BC G.soCD)
    {L : Ev Q → Ev Q → Prop} (hm : ms .mbox → G.MboxOrd L ∧ G.BC (soMbox L))
    (hmin : ∀ s₀, src = some (.snd s₀) → ∀ s' ∈ G.US, s' ≠ s₀ → G.soAll L s' s₀ →
      s'.lab.dst? = s₀.lab.dst? → s'.ValMatches e → False) :
    ConsOf ms (G.add e src out) := by
  have he := hG.not_mem_of_idx_eq_cnt hidx
  have hsrc : ∀ s, src = some (.snd s) → s ∈ G.events :=
    fun s hs => ((G.mem_US).mp (hG.src_of_add hidx hG' hs).1).1
  refine ⟨hG', fun h => ?_, fun h => ?_, fun h => ?_⟩
  · refine hG.bc_add hidx hG' (hp h) (fun a ha b hb ⟨x, y, z⟩ => ⟨x, y, po_add_of_mem ha hb z⟩)
      (fun b _ ⟨_, _, z⟩ => hG.not_po_add_left hidx b z)
      (fun s₀ hs s' hU hne hso hd hv => hmin s₀ hs s' hU hne (Or.inl hso) hd hv)
  · refine hG.bc_add hidx hG' (hc h) (fun a _ b hb ⟨x, y, z⟩ => ?_)
      (fun b _ ⟨_, _, z⟩ => hG.not_porf_add_left hidx hsrc b z)
      (fun s₀ hs s' hU hne hso hd hv => hmin s₀ hs s' hU hne (Or.inr (Or.inl hso)) hd hv)
    exact ⟨x, y, (hG.porf_add_iff hidx hsrc (fun h' => he (h' ▸ hb))).mp z⟩
  · obtain ⟨hL, hb⟩ := hm h
    refine ⟨G.extOrd e L, hG.mboxOrd_add hidx hG' hL, hG.bc_add hidx hG' hb ?_ ?_
      (fun s₀ hs s' hU hne hso hd hv => hmin s₀ hs s' hU hne (Or.inr (Or.inr hso)) hd hv)⟩
    · rintro a _ b hb ⟨x, y, (⟨z, -, -⟩ | ⟨-, hbe⟩)⟩
      · exact ⟨x, y, z⟩
      · exact absurd (hbe ▸ hb) he
    · rintro b _ ⟨-, -, (⟨-, h', -⟩ | ⟨h', -⟩)⟩ <;> exact he h'

/-- An order of `mbox` (when `mbox` is among the models) with the two properties used for
the choice of a minimal source. -/
theorem ConsOf.exists_ord {ms : Comm → Prop} (h : ConsOf ms G) :
    ∃ L : Ev Q → Ev Q → Prop, (ms .mbox → G.MboxOrd L ∧ G.BC (soMbox L)) ∧
      (∀ a, G.MboxSend a → ¬ L a a) ∧
      (∀ a b c, G.MboxSend a → G.MboxSend b → G.MboxSend c → L a b → L b c → L a c) := by
  by_cases hm : ms .mbox
  · obtain ⟨L, hL, hb⟩ := h.2.2.2 hm
    exact ⟨L, fun _ => ⟨hL, hb⟩, hL.irrefl, hL.trans⟩
  · exact ⟨fun _ _ => False, fun h' => absurd h' hm, fun _ _ h' => h',
      fun _ _ _ _ _ _ h' => h'.elim⟩

/-- Extension by a fresh event without a real source (send, block, error, ND, a receive reading
`⊥`), for every set of models. -/
theorem ConsOf.add_plain {ms : Comm → Prop} (h : ConsOf ms G) (hidx : e.idx = G.cnt e.tid)
    (hG' : (G.add e src out).Wf) (hsrc : ∀ s, src ≠ some (.snd s)) :
    ConsOf ms (G.add e src out) := by
  obtain ⟨L, hL, -, -⟩ := h.exists_ord
  exact h.1.consOf_add hidx hG' h.2.1 h.2.2.1 hL (fun s₀ hs => absurd hs (hsrc s₀))

/-- Conditional extensibility for a fresh receive (blocking or not), for every set of models:
an `so`-minimal unread matching send is a consistent source; if there is no unread matching
send, every matching send is read. -/
theorem ConsOf.ext_recv {ms : Comm → Prop} (h : ConsOf ms G) (hidx : e.idx = G.cnt e.tid)
    (hR : e.IsRecv) :
    (∃ s ∈ G.S, ConsOf ms (G.addRecv e (.snd s))) ∨
      (∀ s ∈ G.S, s.Matches e → ∃ r ∈ G.events, G.rf r = some (.snd s)) := by
  classical
  obtain ⟨L, hL, hLi, hLt⟩ := h.exists_ord
  let U := G.US.filter (fun s => s.Matches e)
  rcases U.eq_empty_or_nonempty with hU | hU
  · refine Or.inr fun s hs hm => ?_
    by_contra hno
    push Not at hno
    have hsU : s ∈ U :=
      Finset.mem_filter.mpr ⟨(G.mem_US).mpr ⟨((G.mem_S).mp hs).1, ((G.mem_S).mp hs).2, hno⟩, hm⟩
    rw [hU] at hsU
    exact absurd hsU (Finset.notMem_empty s)
  · have hUG : ∀ x ∈ U, x ∈ G.events := fun x hx => ((G.mem_US).mp (Finset.mem_filter.mp hx).1).1
    obtain ⟨s₀, hs₀, hmin⟩ := exists_min_of_strict U (G.soAll L)
      (fun a ha => h.1.soAll_irrefl hLi (hUG a ha))
      (fun a ha b hb c hc => soAll_trans hLt (hUG a ha) (hUG b hb) (hUG c hc)) hU
    obtain ⟨hs₀U, hs₀m⟩ := Finset.mem_filter.mp hs₀
    refine Or.inl ⟨s₀, G.US_subset_S hs₀U, ?_⟩
    refine h.1.consOf_add hidx (h.1.addRecv hidx hs₀U hs₀m) h.2.1 h.2.2.1 hL ?_
    intro s₁ hs₁ s' hU' _ hso hd hv
    simp only [Option.some.injEq, Src.snd.injEq] at hs₁
    subst hs₁
    have hm' : s'.Matches e := Ev.matches_iff.mpr ⟨((G.mem_US).mp hU').2.1, hR,
      hd.trans hs₀m.dst?, hv, (soAll_model hso).2.trans hs₀m.model⟩
    exact hmin s' (Finset.mem_filter.mpr ⟨hU', hm'⟩) hso

/-! ### Comparison of sets of models -/

omit [DecidableEq Q] [Membership Val Q] in
/-- A condition (b), (c) for an order on sends of a model that the graph does not use holds. -/
theorem bc_of_noSend [DecidableEq Q] [Membership Val Q] {m : Comm} {so : Ev Q → Ev Q → Prop}
    (hno : ∀ a ∈ G.events, ¬ a.SendOf m) (hso : ∀ a b, so a b → a.SendOf m) : G.BC so :=
  ⟨fun s' hs' _ _ _ _ ⟨h, _⟩ => hno s' ((G.mem_US).mp hs').1 (hso _ _ h),
    fun _ _ _ _ s' hs' _ _ ⟨_, _, h, _⟩ => hno s' hs' (hso _ _ h)⟩

/-- Fewer models, fewer conditions. -/
theorem ConsOf.anti {ms ms' : Comm → Prop} (hle : ∀ m, ms' m → ms m) (h : ConsOf ms G) :
    ConsOf ms' G :=
  ⟨h.1, fun hm => h.2.1 (hle _ hm), fun hm => h.2.2.1 (hle _ hm),
    fun hm => h.2.2.2 (hle _ hm)⟩

/-- The condition of a model that the graph does not use holds. -/
theorem consOf_of_unused {m : Comm} (hG : G.Wf)
    (hno : ∀ a ∈ G.events, a.lab.model? ≠ some m) : ConsOf (· = m) G := by
  have hno' : ∀ a ∈ G.events, ¬ a.SendOf m := fun a ha h => hno a ha h.2
  refine ⟨hG, fun hm => ?_, fun hm => ?_, fun hm => ?_⟩
  · subst hm
    exact bc_of_noSend hno' fun _ _ h => h.1
  · subst hm
    exact bc_of_noSend hno' fun _ _ h => h.1
  · subst hm
    refine ⟨fun _ _ => False, ⟨fun _ _ h => h, fun _ _ _ _ _ _ h => h.elim,
      fun a _ ha => absurd ha.2 (hno' a ha.1), fun a _ ha => absurd ha.2 (hno' a ha.1)⟩,
      bc_of_noSend hno' fun _ _ h => h.1⟩

end Graph

/-! ### The model interface -/

namespace Model

open Graph

variable {Q : Type} [DecidableEq Q] [Membership Val Q]

/-- The model of the set of communication models `ms` (Definition 3.8 restricted to `ms`). -/
def ofSet (ms : Comm → Prop) : Model Q where
  cons := ConsOf ms
  wf := fun _ h => h.1
  empty := consOf_empty ms
  prefixClosed := fun _ _ h hE => Wf.consOf_restrict h hE
  ext_plain := fun G e h hidx hR hN =>
    h.add_plain hidx (h.1.add hidx (by simp [hR]) (by simp) (by simp) (by simp [hN]) (by simp))
      (by simp)
  ext_nd := fun G e v h hidx hN hv =>
    h.add_plain hidx (h.1.add hidx (by simp [Lab.IsND.not_isRecv hN]) (by simp) (by simp)
      (by simp [hN]) (fun w hw => by cases hw; exact hv)) (by simp)
  ext_bot := fun G e h hidx hNB =>
    h.add_plain hidx (h.1.addRecv_bot hidx hNB) (by simp)
  ext_recvB := fun G e h hidx hB => h.ext_recv hidx (Lab.IsRecvB.isRecv hB)

/-- The model of one communication model. -/
def single (m : Comm) : Model Q := ofSet (· = m)

/-- `asyn` (Definition 3.4). -/
def asyn : Model Q := single .asyn

/-- `p2p` (Definition 3.5). Its consistency ignores `cd` and `mbox` events (no condition is
imposed on them); programs that mix models are explored under `comb`. -/
def p2p : Model Q := single .p2p

/-- `cd` (Definition 3.6). -/
def cd : Model Q := single .cd

/-- `mbox` (Definition 3.7 repaired by Q5). -/
def mbox : Model Q := single .mbox

/-- The combination of the four models (Definition 3.8, Q4). -/
def comb : Model Q := ofSet (fun _ => True)

/-! #### Prefix-closedness and conditional extensibility, by instance -/

/-- Prefix-closedness of a consistency predicate (3.2.1, for the repaired prefix notion). -/
def PrefixClosed (cons : Graph Q → Prop) : Prop :=
  ∀ G E, cons G → G.Closed E → cons (G.restrict E)

/-- Conditional extensibility (Q11) of a consistency predicate. -/
def CondExt (cons : Graph Q → Prop) : Prop :=
  (∀ G (e : Ev Q), cons G → e.idx = G.cnt e.tid → ¬ e.IsRecv → ¬ e.IsND →
    cons (G.add e none none)) ∧
  (∀ G (e : Ev Q) v, cons G → e.idx = G.cnt e.tid → e.IsND → v ∈ e.ndSet →
    cons (G.addND e v)) ∧
  (∀ G (e : Ev Q), cons G → e.idx = G.cnt e.tid → e.IsRecvNB → cons (G.addRecv e .bot)) ∧
  (∀ G (e : Ev Q), cons G → e.idx = G.cnt e.tid → e.IsRecvB →
    (∃ s ∈ G.S, cons (G.addRecv e (.snd s))) ∨
      (∀ s ∈ G.S, s.Matches e → ∃ r ∈ G.events, G.rf r = some (.snd s)))

/-- Conditional extensibility for every receive (blocking or not): stronger than the receive
clause of `CondExt`. -/
def CondExtRecv (cons : Graph Q → Prop) : Prop :=
  ∀ G (e : Ev Q), cons G → e.idx = G.cnt e.tid → e.IsRecv →
    (∃ s ∈ G.S, cons (G.addRecv e (.snd s))) ∨
      (∀ s ∈ G.S, s.Matches e → ∃ r ∈ G.events, G.rf r = some (.snd s))

/-- Prefix-closedness of a model. -/
theorem prefixClosed' (M : Model Q) : PrefixClosed M.cons := M.prefixClosed

/-- Conditional extensibility (Q11) of a model. -/
theorem condExt (M : Model Q) : CondExt M.cons :=
  ⟨M.ext_plain, M.ext_nd, M.ext_bot, M.ext_recvB⟩

/-- Conditional extensibility of `ofSet ms` for every receive. -/
theorem ofSet_condExt_recv (ms : Comm → Prop) : CondExtRecv (ofSet (Q := Q) ms).cons :=
  fun _ _ h hidx hR => ConsOf.ext_recv h hidx hR

/-- Prefix-closedness of `asyn`. -/
theorem asyn_prefixClosed : PrefixClosed (asyn (Q := Q)).cons := asyn.prefixClosed'
/-- Prefix-closedness of `p2p`. -/
theorem p2p_prefixClosed : PrefixClosed (p2p (Q := Q)).cons := p2p.prefixClosed'
/-- Prefix-closedness of `cd`. -/
theorem cd_prefixClosed : PrefixClosed (cd (Q := Q)).cons := cd.prefixClosed'
/-- Prefix-closedness of `mbox`. -/
theorem mbox_prefixClosed : PrefixClosed (mbox (Q := Q)).cons := mbox.prefixClosed'
/-- Prefix-closedness of the combination. -/
theorem comb_prefixClosed : PrefixClosed (comb (Q := Q)).cons := comb.prefixClosed'

/-- Conditional extensibility (Q11) of `asyn`. -/
theorem asyn_condExt : CondExt (asyn (Q := Q)).cons := asyn.condExt
/-- Conditional extensibility (Q11) of `p2p`. -/
theorem p2p_condExt : CondExt (p2p (Q := Q)).cons := p2p.condExt
/-- Conditional extensibility (Q11) of `cd`. -/
theorem cd_condExt : CondExt (cd (Q := Q)).cons := cd.condExt
/-- Conditional extensibility (Q11) of `mbox`. -/
theorem mbox_condExt : CondExt (mbox (Q := Q)).cons := mbox.condExt
/-- Conditional extensibility (Q11) of the combination. -/
theorem comb_condExt : CondExt (comb (Q := Q)).cons := comb.condExt

/-- Conditional extensibility of `asyn` for every receive. -/
theorem asyn_condExt_recv : CondExtRecv (asyn (Q := Q)).cons := ofSet_condExt_recv _
/-- Conditional extensibility of `p2p` for every receive. -/
theorem p2p_condExt_recv : CondExtRecv (p2p (Q := Q)).cons := ofSet_condExt_recv _
/-- Conditional extensibility of `cd` for every receive. -/
theorem cd_condExt_recv : CondExtRecv (cd (Q := Q)).cons := ofSet_condExt_recv _
/-- Conditional extensibility of `mbox` for every receive. -/
theorem mbox_condExt_recv : CondExtRecv (mbox (Q := Q)).cons := ofSet_condExt_recv _
/-- Conditional extensibility of the combination for every receive. -/
theorem comb_condExt_recv : CondExtRecv (comb (Q := Q)).cons := ofSet_condExt_recv _

/-- No "Out-of-Thin-Air" for the combination. Paper, p. 14: "(No “Out-of-Thin-Air” is
satisfied by default)". -/
theorem comb_porf_irrefl {G : Graph Q} (h : comb.cons G) (a : Ev Q) : ¬ G.porf a a :=
  comb.porf_irrefl h a

/-! #### The predicates of the instances -/

/-- `asyn` is M2's `ConsAsyn` (well-formedness). -/
theorem asyn_cons_iff {G : Graph Q} : asyn.cons G ↔ G.ConsAsyn := by
  simp [asyn, single, ofSet, ConsOf, ConsAsyn]

/-- `cd`: well-formed, (b), (c) with `[S^cd]; porf; [S^cd]`. -/
theorem cd_cons_iff {G : Graph Q} : cd.cons G ↔ G.Wf ∧ G.BC G.soCD := by
  simp [cd, single, ofSet, ConsOf]

/-- `mbox`: well-formed, (b), (c) for an order of Q5. -/
theorem mbox_cons_iff {G : Graph Q} :
    mbox.cons G ↔ G.Wf ∧ ∃ L, G.MboxOrd L ∧ G.BC (soMbox L) := by
  simp [mbox, single, ofSet, ConsOf]

/-- The combination: well-formed, the conditions of `p2p`, `cd`, `mbox`. -/
theorem comb_cons_iff {G : Graph Q} :
    comb.cons G ↔ G.Wf ∧ G.BC G.soP2P ∧ G.BC G.soCD ∧ ∃ L, G.MboxOrd L ∧ G.BC (soMbox L) := by
  simp [comb, ofSet, ConsOf]

/-- Definition 3.8, "`consistent_M(G)` for each model `M` used": `comb` is well-formedness and
the condition of every model of which `G` has an event. -/
theorem comb_cons_iff_used {G : Graph Q} :
    comb.cons G ↔ G.Wf ∧ ∀ m, (∃ a ∈ G.events, a.lab.model? = some m) → (single m).cons G := by
  constructor
  · intro h
    exact ⟨h.1, fun m _ => ConsOf.anti (ms' := (· = m)) (fun _ _ => trivial) h⟩
  · rintro ⟨hG, hall⟩
    have key : ∀ m, ConsOf (· = m) G := fun m => by
      by_cases hu : ∃ a ∈ G.events, a.lab.model? = some m
      · exact hall m hu
      · push Not at hu
        exact consOf_of_unused hG hu
    exact ⟨hG, fun _ => (key .p2p).2.1 rfl, fun _ => (key .cd).2.2.1 rfl,
      fun _ => (key .mbox).2.2.2 rfl⟩

/-- `mbox` implies (b), (c) for `porf` between mailbox sends (decidable). -/
theorem mbox_bc_porf {G : Graph Q} (h : mbox.cons G) :
    G.BC (fun a b => a.SendOf .mbox ∧ b.SendOf .mbox ∧ G.porf a b) := by
  obtain ⟨-, L, hL, hb⟩ := mbox_cons_iff.mp h
  exact hb.mono fun a ha b hb' ⟨x, y, z⟩ => ⟨x, y, hL.porf a b ⟨ha, x⟩ ⟨hb', y⟩ z⟩

/-! #### Agreement with M2 (`Cons.lean`, `Exec.lean`) -/

omit [DecidableEq Q] [Membership Val Q] in
/-- M2's `dstOf` is `Lab.dst?`. -/
theorem dstOf_eq (l : Lab Q) : Graph.dstOf l = l.dst? := by
  cases l <;> rfl

/-- `p2p` is M2's `ConsAP` (Definition 3.5 with global `po`). -/
theorem p2p_cons_iff {G : Graph Q} : p2p.cons G ↔ G.ConsAP := by
  have hb : G.P2Pb ↔ G.CondB G.soP2P := by
    unfold P2Pb CondB SoDst soP2P soP2PWith Ev.SendOf
    simp only [dstOf_eq]
    constructor <;> intro h s' hs' s hs r hr hh <;> apply h s' hs' s hs r hr <;> tauto
  have hc : G.P2Pc ↔ G.CondC G.soP2P := by
    unfold P2Pc CondC CondCWith SoDst soP2P soP2PWith Ev.SendOf
    simp only [dstOf_eq]
    constructor <;> intro h r hr q hq s' hs' s hs hh <;> apply h r hr q hq s' hs' s hs <;> tauto
  simp only [p2p, single, ofSet, ConsOf, ConsAP, BC, hb, hc]
  simp

variable [∀ (v : Val) (q : Q), Decidable (v ∈ q)]

/-- M2's `availM` with `consAsynB` is the availability of `asyn`, on graphs with `Supp`. -/
theorem asyn_availM (P : Program Q) {G : Graph Q} (hS : G.Supp) :
    P.availM Graph.consAsynB G = asyn.availM P G :=
  asyn.availM_eq _ (fun _ hH => (consAsynB_iff hH).trans asyn_cons_iff.symm) P hS

/-- M2's `availM` with `consAPB` is the availability of `p2p`, on graphs with `Supp`. -/
theorem p2p_availM (P : Program Q) {G : Graph Q} (hS : G.Supp) :
    P.availM Graph.consAPB G = p2p.availM P G :=
  p2p.availM_eq _ (fun _ hH => (consAPB_iff hH).trans p2p_cons_iff.symm) P hS

/-- M2's `Usable` with `consAPB` is the `p2p` availability; on a `p2p`-consistent graph it is
"not a blocking receive, or an unread matching send exists" (Q7). -/
theorem p2p_usable_iff {G : Graph Q} {e : Ev Q} (hG : p2p.cons G) (hidx : e.idx = G.cnt e.tid) :
    Program.Usable Graph.consAPB G e ↔ ¬ e.IsRecvB ∨ ∃ s ∈ G.US, s.Matches e :=
  (p2p.usable_congr _ (fun _ hH => (consAPB_iff hH).trans p2p_cons_iff.symm)
    (p2p.wf G hG).supp e).trans (p2p.usable_iff hG hidx)

/-- M2's `Usable` with `consAsynB`, on an `asyn`-consistent graph (Q7). -/
theorem asyn_usable_iff {G : Graph Q} {e : Ev Q} (hG : asyn.cons G)
    (hidx : e.idx = G.cnt e.tid) :
    Program.Usable Graph.consAsynB G e ↔ ¬ e.IsRecvB ∨ ∃ s ∈ G.US, s.Matches e :=
  (asyn.usable_congr _ (fun _ hH => (consAsynB_iff hH).trans asyn_cons_iff.symm)
    (asyn.wf G hG).supp e).trans (asyn.usable_iff hG hidx)

/-- `cd`, computed. -/
def consCDB (G : Graph Q) : Bool := decide (G.WfD ∧ G.BC G.soCD)

/-- `consCDB` decides `cd` on graphs with `Supp`. -/
theorem consCDB_iff {G : Graph Q} (hS : G.Supp) : consCDB G = true ↔ cd.cons G := by
  rw [consCDB, decide_eq_true_iff, wfD_iff hS, cd_cons_iff]

/-- M2's `availM` with `consCDB` is the availability of `cd`, on graphs with `Supp`. -/
theorem cd_availM (P : Program Q) {G : Graph Q} (hS : G.Supp) :
    P.availM consCDB G = cd.availM P G :=
  cd.availM_eq _ (fun _ hH => consCDB_iff hH) P hS

end Model

end Must

#print axioms Must.Graph.consOf_empty
#print axioms Must.Graph.Wf.consOf_restrict
#print axioms Must.Graph.Wf.consOf_add
#print axioms Must.Graph.Wf.mboxOrd_add
#print axioms Must.Graph.ConsOf.add_plain
#print axioms Must.Graph.ConsOf.ext_recv
#print axioms Must.Model.ofSet
#print axioms Must.Model.asyn_prefixClosed
#print axioms Must.Model.p2p_prefixClosed
#print axioms Must.Model.cd_prefixClosed
#print axioms Must.Model.mbox_prefixClosed
#print axioms Must.Model.comb_prefixClosed
#print axioms Must.Model.asyn_condExt
#print axioms Must.Model.p2p_condExt
#print axioms Must.Model.cd_condExt
#print axioms Must.Model.mbox_condExt
#print axioms Must.Model.comb_condExt
#print axioms Must.Model.asyn_condExt_recv
#print axioms Must.Model.p2p_condExt_recv
#print axioms Must.Model.cd_condExt_recv
#print axioms Must.Model.mbox_condExt_recv
#print axioms Must.Model.comb_condExt_recv
#print axioms Must.Model.comb_porf_irrefl
#print axioms Must.Model.asyn_cons_iff
#print axioms Must.Model.p2p_cons_iff
#print axioms Must.Model.comb_cons_iff_used
#print axioms Must.Model.mbox_bc_porf
#print axioms Must.Model.asyn_availM
#print axioms Must.Model.p2p_availM
#print axioms Must.Model.cd_availM
#print axioms Must.Model.asyn_usable_iff
#print axioms Must.Model.p2p_usable_iff
#print axioms Must.Model.consCDB_iff
