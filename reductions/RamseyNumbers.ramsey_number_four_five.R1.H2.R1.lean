import OMAReductions.R_RamseyNumbers_ramsey_number_four_five_R1
import Mathlib

/-! The degree-ten gluing problem separates into neighborhoods with a
vertex of degree one or two and neighborhoods with all degrees three or
four. The R(3,4) bound also limits each row of the crossing adjacency matrix. -/
open SimpleGraph Finset RamseyNumbers
namespace RamseyTenDegree
open OMA.R_RamseyNumbers_ramsey_number_four_five_R1

open Classical in
theorem inside_bounds (G : SimpleGraph (Fin 24)) (T : Finset (Fin 24)) (hT : T.card = 10)
    (noTri : ∀ S ⊆ T, ¬ G.IsNClique 3 S) (noInd : Gᶜ.CliqueFree 5)
    (v : Fin 24) (hv : v ∈ T) :
    1 ≤ (T.filter (G.Adj v)).card ∧ (T.filter (G.Adj v)).card ≤ 4 := by
  classical
  refine ⟨?_,?_⟩
  · by_contra hpos
    have zero : (T.filter (G.Adj v)).card = 0 := by omega
    have noNeighbor {x : Fin 24} (hx : x ∈ T) : ¬ G.Adj v x := by
      intro adj
      have hz := card_pos.mpr (show (T.filter (G.Adj v)).Nonempty from
        ⟨x,mem_filter.mpr ⟨hx,adj⟩⟩)
      omega
    have n : (T.erase v).card = 9 := by rw [card_erase_of_mem hv,hT]
    obtain ⟨f,hf⟩ := Function.Embedding.exists_of_card_le_finset
      (α:=Fin 9) (s:=T.erase v) (by rw [Fintype.card_fin,n])
    let Q := G.comap f
    let e : Q ↪g G := SimpleGraph.Embedding.comap f G
    let ec : Qᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv e
    have loc {S : Finset (Fin 9)} {x : Fin 24} (hx : x ∈ S.map f) : x ∈ T.erase v := by
      obtain ⟨i,_,rfl⟩ := mem_map.mp hx
      exact hf ⟨i,rfl⟩
    apply nine_works Q
    constructor
    · intro S hS
      exact noTri (S.map f) (fun x hx ↦ mem_of_mem_erase (loc hx)) (map_clique e hS)
    · intro S hS
      have q := map_clique ec hS
      apply noInd _ (q.insert (a:=v) ?_)
      intro x hx
      have p := mem_erase.mp (loc hx)
      exact (G.compl_adj v x).mpr ⟨p.1.symm,noNeighbor p.2⟩
  · by_contra h
    have five : 5 ≤ (T.filter (G.Adj v)).card := by omega
    obtain ⟨S,sub,size⟩ := exists_subset_card_eq five
    apply noInd S
    refine ⟨?_,size⟩
    intro x hx y hy ne
    have hx' := mem_filter.mp (sub hx)
    have hy' := mem_filter.mp (sub hy)
    refine (G.compl_adj x y).mpr ⟨ne,?_⟩
    intro edge
    have two : G.IsNClique 2 {x,y} := by
      refine ⟨?_,by simp [ne]⟩
      rw [Finset.coe_insert,Finset.coe_singleton]
      exact isClique_pair.mpr (fun _ ↦ edge)
    have all : ∀ z ∈ ({x,y} : Finset (Fin 24)), G.Adj v z := by
      intro z hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx'.2
      · exact hy'.2
    refine noTri (insert v {x,y}) ?_ (two.insert all)
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hv
    · exact hx'.1
    · exact hy'.1

open Classical in
theorem crossing_bound (G : SimpleGraph (Fin 24)) (T : Finset (Fin 24))
    (noK : G.CliqueFree 4) (outside : ∀ S, Disjoint S T → ¬ Gᶜ.IsNClique 4 S)
    (v : Fin 24) : ((univ \ T).filter (G.Adj v)).card ≤ 8 := by
  classical
  let N := (univ \ T).filter (G.Adj v)
  change N.card ≤ 8
  by_contra hx
  have nine : 9 ≤ N.card := by omega
  obtain ⟨f,hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α:=Fin 9) (s:=N) (by simpa only [Fintype.card_fin] using nine)
  let Q := G.comap f
  let e : Q ↪g G := SimpleGraph.Embedding.comap f G
  let ec : Qᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv e
  have loc {S : Finset (Fin 9)} {x : Fin 24} (hx : x ∈ S.map f) : x ∈ N := by
    obtain ⟨i,_,rfl⟩ := mem_map.mp hx
    exact hf ⟨i,rfl⟩
  apply nine_works Q
  constructor
  · intro S hS
    have q := map_clique e hS
    exact noK _ (q.insert (a:=v) (fun x hx ↦ (mem_filter.mp (loc hx)).2))
  · intro S hS
    apply outside (S.map f) ?_ (map_clique ec hS)
    exact Finset.disjoint_left.mpr fun x hs ht ↦
      (mem_sdiff.mp (mem_filter.mp (loc hs)).1).2 ht

end RamseyTenDegree

namespace OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H2_R1
open RamseyTenDegree

open Classical in
/-- A putative neighborhood with a vertex of internal degree one or two. -/
def H1 : Prop := ∀ (G : SimpleGraph (Fin 24)), G.CliqueFree 4 → Gᶜ.CliqueFree 5 →
  ∀ T : Finset (Fin 24), T.card = 10 →
  (∀ S ⊆ T, ¬ G.IsNClique 3 S) → (∀ S, Disjoint S T → ¬ Gᶜ.IsNClique 4 S) →
  (∀ v ∈ T, 1 ≤ (T.filter (G.Adj v)).card ∧ (T.filter (G.Adj v)).card ≤ 4) →
  (∀ v ∈ T, ((univ \ T).filter (G.Adj v)).card ≤ 8) →
  (∃ v ∈ T, (T.filter (G.Adj v)).card = 1 ∨ (T.filter (G.Adj v)).card = 2) → False

open Classical in
/-- A putative neighborhood of minimum internal degree at least three. -/
def H2 : Prop := ∀ (G : SimpleGraph (Fin 24)), G.CliqueFree 4 → Gᶜ.CliqueFree 5 →
  ∀ T : Finset (Fin 24), T.card = 10 →
  (∀ S ⊆ T, ¬ G.IsNClique 3 S) → (∀ S, Disjoint S T → ¬ Gᶜ.IsNClique 4 S) →
  (∀ v ∈ T, ((univ \ T).filter (G.Adj v)).card ≤ 8) →
  (∀ v ∈ T, 3 ≤ (T.filter (G.Adj v)).card ∧ (T.filter (G.Adj v)).card ≤ 4) → False

theorem main : H1 → H2 → OMA.R_RamseyNumbers_ramsey_number_four_five_R1.H2 := by
  classical
  intro low high G noK noInd T hT
  by_contra contrary
  have noTri : ∀ S ⊆ T, ¬ G.IsNClique 3 S := fun S hS hs ↦ contrary (Or.inl ⟨S,hS,hs⟩)
  have out : ∀ S, Disjoint S T → ¬ Gᶜ.IsNClique 4 S :=
    fun S hd hs ↦ contrary (Or.inr ⟨S,hd,hs⟩)
  have inside (v : Fin 24) (hv : v ∈ T) := inside_bounds G T hT noTri noInd v hv
  have cross (v : Fin 24) (_hv : v ∈ T) := crossing_bound G T noK out v
  by_cases found : ∃ v ∈ T, (T.filter (G.Adj v)).card = 1 ∨ (T.filter (G.Adj v)).card = 2
  · exact low G noK noInd T hT noTri out inside cross found
  · apply high G noK noInd T hT noTri out cross
    intro v hv
    have a := inside v hv
    have b : ¬ ((T.filter (G.Adj v)).card = 1 ∨ (T.filter (G.Adj v)).card = 2) :=
      fun h ↦ found ⟨v,hv,h⟩
    omega

end OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H2_R1
