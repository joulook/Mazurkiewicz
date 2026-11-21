import Mazurkiewicz.Condpor.Rf.Explore
import Mazurkiewicz.Condpor.Examples

/-!
# The reads-from version: instances

By `exploreR_spec` the reads-from version reports one graph for every
reads-from class of full executions. The classes of the executions that the
computed explorer of `ExploreC.lean` lists are counted by a signature of a
graph: its events with their sources and outcomes (`Graph.sig`).

* `exploreR_length_sig`: the number of graphs that the reads-from version
  reports is the number of signatures of the graphs of the Shasha-Snir
  version; for SC it is computed (`exploreR_length_sc`).
* TruSt's `r+w+w` (Section 4.2, Fig. 10): 3 against 6. The programs of Fig. 1
  and Example 1 of ConDpor.
-/

namespace Condpor

open Program

variable {P : Program} {M : Model} {S : Solver} {τ : TieBreak S} {γ : CoChoice (M.sym S)}

/-- The events of a graph in a fixed order (insertion sort, which the kernel
evaluates). -/
def Graph.evList (G : Graph) : List TEv :=
  Quot.liftOn G.events.val (List.insertionSort keyLe) (fun a b h =>
    List.Perm.eq_of_pairwise' (r := keyLe) (List.pairwise_insertionSort _ a)
      (List.pairwise_insertionSort _ b)
      ((List.perm_insertionSort _ a).trans (h.trans (List.perm_insertionSort _ b).symm)))

theorem Graph.mem_evList (G : Graph) {e : TEv} : e ∈ G.evList ↔ e ∈ G.events := by
  unfold Graph.evList
  generalize G.events = s
  rcases s with ⟨m, hm⟩
  induction m using Quot.inductionOn with
  | _ l => exact List.mem_insertionSort _

/-- The signature of a graph: its events in a fixed order, with their sources
and outcomes. -/
def Graph.sig (G : Graph) : List (TEv × Option Ev × Option Bool) :=
  G.evList.map (fun e => (e, G.rf e, G.pol e))

theorem Graph.sig_canon (G : Graph) : G.canon.sig = G.sig := rfl

/-- Well-formed graphs with the same memory and signature agree on everything
but coherence. -/
theorem Graph.rfEq_of_sig {G G' : Graph} (hG : G.Wf) (hG' : G'.Wf) (hm : G.mem = G'.mem)
    (h : G.sig = G'.sig) : G.RfEq G' := by
  have hev : G.events = G'.events := by
    have h1 := congrArg (List.map Prod.fst) h
    simp only [Graph.sig, List.map_map] at h1
    have h2 : G.evList = G'.evList := by
      simpa [Function.comp_def] using h1
    ext e
    rw [← G.mem_evList, h2, G'.mem_evList]
  have hpt : ∀ e ∈ G.events, G.rf e = G'.rf e ∧ G.pol e = G'.pol e := by
    intro e he
    have hmem : (e, G.rf e, G.pol e) ∈ G.sig :=
      List.mem_map.mpr ⟨e, G.mem_evList.mpr he, rfl⟩
    rw [h] at hmem
    obtain ⟨e', -, he'⟩ := List.mem_map.mp hmem
    simp only [Prod.mk.injEq] at he'
    obtain ⟨rfl, h1, h2⟩ := he'
    exact ⟨h1.symm, h2.symm⟩
  refine ⟨hm, hev, ?_, ?_⟩
  · funext e
    by_cases he : e ∈ G.events
    · exact (hpt e he).1
    · rw [hG.rf_none e (Or.inl he), hG'.rf_none e (Or.inl (hev ▸ he))]
  · funext e
    by_cases he : e ∈ G.events
    · exact (hpt e he).2
    · rw [hG.pol_none he, hG'.pol_none (hev ▸ he)]

/-- The number of graphs that the reads-from version reports is the number of
signatures of the graphs that the Shasha-Snir version reports. -/
theorem exploreR_length_sig {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible) (τ' : TieBreak S) :
    (exploreR P (M.sym S) γ τ n).length =
      ((explore P (M.sym S) τ' n).map Graph.sig).dedup.length := by
  classical
  obtain ⟨hnd, hspec⟩ := exploreR_spec (γ := γ) (τ := τ) hn hM
  have hmap : ((explore P (M.sym S) τ' n).map Graph.sig).toFinset =
      (explore P (M.sym S) τ' n).toFinset.image Graph.sig := by
    ext s
    simp
  rw [← List.card_toFinset, hmap, ← List.toFinset_card_of_nodup hnd]
  have himg : (explore P (M.sym S) τ' n).toFinset.image Graph.sig =
      (exploreR P (M.sym S) γ τ n).toFinset.image Graph.sig := by
    ext s
    simp only [Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨G', hG', rfl⟩
      exact ⟨G'.canon, (mem_exploreR_iff_canon hn hM τ' _).mpr ⟨G', hG', rfl⟩, rfl⟩
    · rintro ⟨G, hG, rfl⟩
      obtain ⟨G', hG', rfl⟩ := (mem_exploreR_iff_canon hn hM τ' G).mp hG
      exact ⟨G', hG', rfl⟩
  rw [himg]
  refine (Finset.card_image_of_injOn ?_).symm
  intro G hG G' hG' hs
  obtain ⟨hW, hE, -, -, hcan⟩ := (hspec G).mp (List.mem_toFinset.mp hG)
  obtain ⟨hW', hE', -, -, hcan'⟩ := (hspec G').mp (List.mem_toFinset.mp hG')
  have := (Graph.rfEq_of_sig hW hW' (hE.1.trans hE'.1.symm) hs).canon_eq
  rw [hcan.canon_eq, hcan'.canon_eq] at this
  exact this

/-- For SC and a computed oracle, the number is computed. -/
theorem exploreR_length_sc {S : Solver} {τ τ' : TieBreak S} (γ : CoChoice (SC.sym S))
    (O : Oracle τ') {n : ℕ} (hn : P.Bounded n) :
    (exploreR P (SC.sym S) γ τ n).length = ((exploreC P O n).map Graph.sig).dedup.length := by
  rw [exploreC_eq P O]
  exact exploreR_length_sig hn SC.extensible τ'

/-! ### `r+w+w` -/

/-- `a := x ‖ x := 1 ‖ x := 2` (TruSt, Section 3.5 and Fig. 10). -/
def rwwTab : Tid → List (Option Val) → Option Act
  | 0, [] => some (.read 0)
  | 1, [] => some (.write 0 1)
  | 2, [] => some (.write 0 2)
  | _, _ => none

/-- The program `r+w+w`. -/
def rwwProg : Program := mkProg [0, 1, 2] (by decide) rwwTab (fun _ => 0) 1

theorem rww_sigs : ((exploreC rwwProg eqOracleSe 1).map Graph.sig).dedup.length = 3 := by
  decide +kernel

theorem rww_co : (exploreC rwwProg eqOracleSe 1).length = 6 := by decide +kernel

/-- R-7. On `r+w+w` the reads-from version reports 3 graphs, for every choice
of coherence orders and every tie-break; the Shasha-Snir version reports 6. -/
theorem rww_three (γ : CoChoice (SC.sym EqSem.solver)) (τ : TieBreak EqSem.solver) :
    (exploreR rwwProg (SC.sym EqSem.solver) γ τ 1).length = 3 ∧
      (explore rwwProg (SC.sym EqSem.solver) (TieBreak.se EqSem.solver) 1).length = 6 := by
  refine ⟨?_, ?_⟩
  · rw [exploreR_length_sc (P := rwwProg) γ eqOracleSe (mkProg_bounded _ _ _ _ _)]
    exact rww_sigs
  · rw [← exploreC_eq rwwProg eqOracleSe]
    exact rww_co

/-! ### Fig. 1 and Example 1 of ConDpor -/

theorem fig1_sigs : ((exploreC fig1 eqOracleSe 3).map Graph.sig).dedup.length = 6 := by
  decide +kernel

theorem ex1_sigs : ((exploreC ex1 eqOracleSe 4).map Graph.sig).dedup.length = 4 := by
  decide +kernel

/-- On the programs of Fig. 1 and Example 1 no two executions differ only in
coherence: the reads-from version reports 6 and 4 graphs, as the Shasha-Snir
version. -/
theorem fig1_ex1_rf (γ : CoChoice (SC.sym EqSem.solver)) (τ : TieBreak EqSem.solver) :
    (exploreR fig1 (SC.sym EqSem.solver) γ τ 3).length = 6 ∧
      (exploreR ex1 (SC.sym EqSem.solver) γ τ 4).length = 4 := by
  refine ⟨?_, ?_⟩
  · rw [exploreR_length_sc (P := fig1) γ eqOracleSe (mkProg_bounded _ _ _ _ _)]
    exact fig1_sigs
  · rw [exploreR_length_sc (P := ex1) γ eqOracleSe (mkProg_bounded _ _ _ _ _)]
    exact ex1_sigs

end Condpor
