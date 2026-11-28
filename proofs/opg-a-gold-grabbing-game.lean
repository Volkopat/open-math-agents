import OMAStatements.S_opg_a_gold_grabbing_game
import Mathlib

namespace GoldGrabbing

open OMA.S_opg_a_gold_grabbing_game Finset

private def gameValue {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (gold : Fin n → ℕ)
    (s : Finset (Fin n)) : ℤ :=
  if h : (leafMoves G s).attach.Nonempty then
    (leafMoves G s).attach.sup' h fun v => (gold v.val : ℤ) - gameValue G gold (s.erase v.val)
  else 0
termination_by s.card
decreasing_by
  exact card_erase_lt_of_mem (mem_filter.mp v.property).1

private def candidate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (gold : Fin n → ℕ)
    (s : Finset (Fin n)) (v : Fin n) : ℤ :=
  (gold v : ℤ) - gameValue G gold (s.erase v)

private theorem candidate_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gold : Fin n → ℕ) (s : Finset (Fin n)) {v : Fin n} (hv : v ∈ leafMoves G s) :
    candidate G gold s v ≤ gameValue G gold s := by
  have hs : (leafMoves G s).attach.Nonempty := ⟨⟨v,hv⟩,mem_attach _ _⟩
  rw [gameValue,dif_pos hs]
  exact le_sup' (f := fun a : {v // v ∈ leafMoves G s} => candidate G gold s a.val)
    (mem_attach _ ⟨v,hv⟩)

private theorem maximum_candidate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gold : Fin n → ℕ) (s : Finset (Fin n)) (hs : (leafMoves G s).Nonempty) :
    ((leafMoves G s).filter (fun v => candidate G gold s v = gameValue G gold s)).Nonempty := by
  obtain ⟨v,hv,hmax⟩ := (leafMoves G s).exists_max_image (candidate G gold s) hs
  refine ⟨v,mem_filter.mpr ⟨hv,le_antisymm (candidate_le G gold s hv) ?_⟩⟩
  have hAttached : (leafMoves G s).attach.Nonempty := ⟨⟨v,hv⟩,mem_attach _ _⟩
  rw [gameValue,dif_pos hAttached]
  apply sup'_le
  intro a _
  exact hmax a.val a.property

private def bestPolicy {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gold : Fin n → ℕ) : Policy G :=
  fun s h =>
    let options := (leafMoves G s).filter (fun v => candidate G gold s v = gameValue G gold s)
    let hn := maximum_candidate G gold s h
    ⟨options.min' hn,(mem_filter.mp (min'_mem options hn)).1⟩

private theorem best_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gold : Fin n → ℕ) (s : Finset (Fin n)) (hs : (leafMoves G s).Nonempty) :
    candidate G gold s (bestPolicy G gold s hs).val = gameValue G gold s :=
  (mem_filter.mp (min'_mem _ (maximum_candidate G gold s hs))).2

private theorem score_bounds {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gold : Fin n → ℕ) (q : Policy G) (s : Finset (Fin n)) :
    playScore G gold s q (bestPolicy G gold) ≤ gameValue G gold s ∧
      gameValue G gold s ≤ playScore G gold s (bestPolicy G gold) q := by
  refine Finset.strongInductionOn s ?_
  intro s ih
  by_cases h : (leafMoves G s).Nonempty
  · let a := q s h
    let b := bestPolicy G gold s h
    have ha : a.val ∈ s := (mem_filter.mp a.property).1
    have hb : b.val ∈ s := (mem_filter.mp b.property).1
    have ha' := (ih (s.erase a.val) (erase_ssubset ha)).2
    have hb' := (ih (s.erase b.val) (erase_ssubset hb)).1
    have hA := candidate_le G gold s a.property
    have hB := best_eq G gold s h
    constructor
    · rw [playScore,dif_pos h]
      change (gold a.val : ℤ) - playScore G gold (s.erase a.val) (bestPolicy G gold) q ≤ _
      unfold candidate at hA
      omega
    · rw [playScore,dif_pos h]
      change _ ≤ (gold b.val : ℤ) - playScore G gold (s.erase b.val) q (bestPolicy G gold)
      change candidate G gold s b.val = _ at hB
      unfold candidate at hB
      omega
  · have hAttach : ¬ (leafMoves G s).attach.Nonempty := by
      rintro ⟨v,_⟩
      exact h ⟨v.val,v.property⟩
    rw [playScore,dif_neg h,gameValue,dif_neg hAttach,playScore,dif_neg h]
    exact ⟨le_rfl,le_rfl⟩

private def valueFromSmaller {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gold : Fin n → ℕ) (lookup : Finset (Fin n) → ℤ) (s : Finset (Fin n)) : ℤ :=
  if h : (leafMoves G s).attach.Nonempty then
    (leafMoves G s).attach.sup' h fun v => (gold v.val : ℤ) - lookup (s.erase v.val)
  else 0

private theorem value_from_lookup {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gold : Fin n → ℕ) (lookup : Finset (Fin n) → ℤ) (s : Finset (Fin n))
    (hl : ∀ v ∈ leafMoves G s, lookup (s.erase v) = gameValue G gold (s.erase v)) :
    valueFromSmaller G gold lookup s = gameValue G gold s := by
  rw [valueFromSmaller,gameValue]
  split
  · rename_i h
    congr 1
    funext v
    rw [hl v.val v.property]
  · rfl

private def stateTable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gold : Fin n → ℕ) (todo : List (Finset (Fin n))) (known : Finset (Fin n) → ℤ) :
    Finset (Fin n) → ℤ :=
  match todo with
  | [] => known
  | s :: remaining =>
    stateTable G gold remaining (Function.update known s (valueFromSmaller G gold known s))

private theorem state_table_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gold : Fin n → ℕ) (todo : List (Finset (Fin n))) (known : Finset (Fin n) → ℤ)
    (hsorted : todo.Pairwise (fun a b => a.card ≤ b.card))
    (hknown : ∀ s ∉ todo, known s = gameValue G gold s) :
    ∀ s, stateTable G gold todo known s = gameValue G gold s := by
  induction todo generalizing known with
  | nil => intro s; exact hknown s (by simp)
  | cons first todo ih =>
    obtain ⟨hFirst,hTail⟩ := List.pairwise_cons.mp hsorted
    have hValue : valueFromSmaller G gold known first = gameValue G gold first := by
      apply value_from_lookup
      intro v hv
      have hsmaller : (first.erase v).card < first.card :=
        card_erase_lt_of_mem (mem_filter.mp hv).1
      apply hknown
      intro hm
      rcases List.mem_cons.mp hm with he | ht
      · exact (ne_of_lt hsmaller) (congrArg Finset.card he)
      · exact (not_le_of_gt hsmaller) (hFirst _ ht)
    rw [stateTable]
    apply ih _ hTail
    intro s hs
    by_cases h : s = first
    · subst s
      simp [hValue]
    · rw [Function.update_of_ne h]
      apply hknown
      simp [h,hs]

private def configurations (n : ℕ) : List (Finset (Fin n)) :=
  ((List.finRange n).sublists.map List.toFinset).mergeSort (fun a b => decide (a.card ≤ b.card))

private theorem configurations_all {n : ℕ} (s : Finset (Fin n)) : s ∈ configurations n := by
  unfold configurations
  rw [List.mem_mergeSort]
  let xs := (List.finRange n).filter fun a => a ∈ s
  apply List.mem_map.mpr
  refine ⟨xs,List.mem_sublists.mpr List.filter_sublist,?_⟩
  ext x
  simp [xs]

private theorem configurations_sorted (n : ℕ) :
    (configurations n).Pairwise (fun a b => a.card ≤ b.card) := by
  unfold configurations
  have hSorted := List.pairwise_mergeSort (le := fun a b : Finset (Fin n) => decide (a.card ≤ b.card))
    (fun a b c hab hbc => by simpa using (Nat.le_trans (by simpa using hab) (by simpa using hbc)))
    (fun a b => by simpa using Nat.le_total a.card b.card)
    ((List.finRange n).sublists.map List.toFinset)
  simpa using hSorted

/-- The table evaluates each remaining subset in order of its cardinality. -/
private def optimalTable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gold : Fin n → ℕ) : Finset (Fin n) → ℤ := stateTable G gold (configurations n) (fun _ => 0)

private theorem optimal_table_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gold : Fin n → ℕ) (s : Finset (Fin n)) : optimalTable G gold s = gameValue G gold s :=
  state_table_correct G gold _ _ (configurations_sorted n)
    (fun k hk => (hk (configurations_all k)).elim) s


private theorem graph_has_legal_leaf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hg : G.IsAcyclic) (s : Finset (Fin n)) (hs : s.Nonempty) :
    (leafMoves G s).Nonempty := by
  classical
  obtain ⟨u,hu⟩ := hs
  let H := G.induce (s : Set (Fin n))
  let component := H.connectedComponentMk ⟨u,hu⟩
  let J := H.induce component.supp
  let root : component.supp := ⟨⟨u,hu⟩,SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  have hJ : J.IsTree := ⟨(component.maximal_connected_induce_supp).1,(hg.induce _).induce _⟩
  have hLeaf : ∃ x : component.supp, J.degree x ≤ 1 := by
    by_cases hS : Subsingleton ↥component.supp
    · let _ : Subsingleton ↥component.supp := hS
      have hEmpty : J.neighborFinset root = ∅ := by
        ext v
        rw [Subsingleton.elim v root]
        simp
      refine ⟨root,?_⟩
      rw [SimpleGraph.degree,hEmpty]
      simp
    · let _ : Nontrivial ↥component.supp := not_subsingleton_iff_nontrivial.mp hS
      obtain ⟨x,hx⟩ := hJ.exists_vert_degree_one_of_nontrivial
      exact ⟨x,hx.le⟩
  obtain ⟨x,hx⟩ := hLeaf
  have hInside : H.neighborSet x.val ⊆ component.supp :=
    fun z hz => component.mem_supp_of_adj_mem_supp x.property hz
  have hDegrees : J.degree x = H.degree x.val :=
    H.degree_induce_of_neighborSet_subset hInside
  have hMap : ((H.neighborFinset x.val).map (Function.Embedding.subtype fun v : Fin n => v ∈ s)) =
      s.filter (G.Adj x.val.val) := by
    ext v
    constructor
    · intro hv
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hv
      rw [SimpleGraph.mem_neighborFinset] at ha
      refine Finset.mem_filter.mpr ⟨a.property,?_⟩
      change G.Adj x.val.val a.val at ha
      exact ha
    · intro hv
      obtain ⟨hS,hAdj⟩ := Finset.mem_filter.mp hv
      refine Finset.mem_map.mpr ⟨⟨v,hS⟩,?_,rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      change G.Adj x.val.val v
      exact hAdj
  have hCard : (s.filter (G.Adj x.val.val)).card = H.degree x.val := by
    rw [←hMap,Finset.card_map,SimpleGraph.degree]
  rw [hDegrees] at hx
  exact ⟨x.val.val,mem_filter.mpr ⟨x.val.property,by rw [hCard]; exact hx⟩⟩

private theorem table_options_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gold : Fin n → ℕ) (s : Finset (Fin n)) :
    (leafMoves G s).filter (fun v =>
      (gold v : ℤ) - optimalTable G gold (s.erase v) = optimalTable G gold s) =
    (leafMoves G s).filter (fun v => candidate G gold s v = gameValue G gold s) := by
  ext v
  rw [mem_filter,mem_filter,candidate,optimal_table_correct,optimal_table_correct]

private theorem min_congr {n : ℕ} {A B : Finset (Fin n)} (h : A = B)
    (hA : A.Nonempty) (hB : B.Nonempty) : A.min' hA = B.min' hB := by
  subst B
  rfl

private def tablePolicy {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gold : Fin n → ℕ) : Policy G :=
  fun s hs =>
    let options := (leafMoves G s).filter (fun v =>
      (gold v : ℤ) - optimalTable G gold (s.erase v) = optimalTable G gold s)
    have hn : options.Nonempty := by
      dsimp only [options]
      rw [table_options_eq]
      exact maximum_candidate G gold s hs
    ⟨options.min' hn,(mem_filter.mp (min'_mem options hn)).1⟩

private theorem table_policy_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gold : Fin n → ℕ) : tablePolicy G gold = bestPolicy G gold := by
  funext s hs
  apply Subtype.ext
  have he := table_options_eq G gold s
  have hBest := maximum_candidate G gold s hs
  have hTable : ((leafMoves G s).filter (fun v =>
      (gold v : ℤ) - optimalTable G gold (s.erase v) = optimalTable G gold s)).Nonempty := by
    rw [he]
    exact hBest
  exact min_congr he hTable hBest

theorem optimal_strategies : OptimalStrategies := by
  intro n G _ hTree gold
  refine ⟨tablePolicy G gold,fun q s => ⟨graph_has_legal_leaf G hTree.2 s,?_⟩⟩
  rw [table_policy_eq]
  have hp := score_bounds G gold (bestPolicy G gold) s
  have he : playScore G gold s (bestPolicy G gold) (bestPolicy G gold) = gameValue G gold s :=
    le_antisymm hp.1 hp.2
  rw [he]
  exact score_bounds G gold q s

end GoldGrabbing

theorem OMA.solution : type_of% @OMA.S_opg_a_gold_grabbing_game.main := by
  exact GoldGrabbing.optimal_strategies
