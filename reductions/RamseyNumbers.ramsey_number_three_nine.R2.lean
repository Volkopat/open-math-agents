import FormalConjectures.Wikipedia.RamseyNumbers
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic

/-!
Reduction RamseyNumbers.ramsey_number_three_nine.R2.
Credit: @sturdy4days. The lower-bound witness and search follow #1435 and
#660. The two initial neighborhood counting lemmas follow @physbuzz in #9042. The smaller
edge bounds follow the classical minimum Ramsey graph tables of Goedgebeur
and Radziszowski; the 22-vertex bound is weakened to 59.
-/


/-! Kalbfleisch’s 35-vertex graph, from Brendan McKay’s combinatorial data
collection, https://users.cecs.anu.edu.au/~bdm/data/r39_35.g6 (CC BY 4.0).
The 35 neighborhood masks and soundness argument were contributed by @VinnyMo
in open-math-agents #1435. The clique
search adapts the verifier in open-math-agents reduction #660 for R(3,6),
with an additional bound on the number of remaining vertices. -/
open SimpleGraph
namespace OMA.Ramsey35

lemma exclude_search {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (cert : (Nat.rec (motive := fun _ => List (Fin n) → Bool) (fun _ => true)
      (fun j rec vs => if vs.length < j+1 then false else vs.any fun v => rec (vs.filter fun w => decide (v < w ∧ G.Adj v w)))
      k (List.finRange n)) = false) : G.CliqueFree k := by
  let search := Nat.rec (motive := fun _ => List (Fin n) → Bool) (fun _ => true)
    (fun j rec vs => if vs.length < j+1 then false else vs.any fun v => rec (vs.filter fun w => decide (v < w ∧ G.Adj v w)))
  have found (j : ℕ) (vs : List (Fin n)) (s : Finset (Fin n)) (hs : G.IsNClique j s)
      (hsub : ∀ x ∈ s, x ∈ vs) : search j vs = true := by
    induction j generalizing vs s with
    | zero => rfl
    | succ j ih =>
      have hne : s.Nonempty := Finset.card_pos.mp (by rw [hs.card_eq]; omega)
      let v := s.min' hne
      have hv : v ∈ s := s.min'_mem hne
      have hslen : s.card ≤ vs.length :=
        (Finset.card_le_card (show s ⊆ vs.toFinset from fun x hx => List.mem_toFinset.mpr (hsub x hx))).trans
          (List.toFinset_card_le vs)
      have hh : ¬ vs.length < j+1 := by rw [hs.card_eq] at hslen; omega
      change (if vs.length < j+1 then false else vs.any _) = true
      rw [if_neg hh]
      apply List.any_eq_true.mpr
      refine ⟨v, hsub v hv, ih _ (s.erase v) (hs.erase_of_mem hv) ?_⟩
      intro w hw
      obtain ⟨hne, hw⟩ := Finset.mem_erase.mp hw
      exact List.mem_filter.mpr ⟨hsub w hw, decide_eq_true
        ⟨lt_of_le_of_ne (s.min'_le _ hw) hne.symm, hs.isClique hv hw hne.symm⟩⟩
  intro s hs
  have yes := found k (List.finRange n) s hs (by simp)
  change search k (List.finRange n) = false at cert
  simp_all


set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem lower_witness : ∃ G : SimpleGraph (Fin 35), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 9 := by
  let rows : Array ℕ := #[0x1fe, 0x2c5080201, 0x4a2c04001, 0x532101001, 0x2a4820401, 0x349200801, 0x558042001, 0x320330001, 0x4c04c8001, 0x20868c02, 0x402614210, 0x84192220, 0x48076008, 0x201609840, 0x110189404, 0xe016300, 0x11809c80, 0x413001290, 0x207001340, 0x2a804902, 0x49804888, 0x948024a0, 0x11c002504, 0x100390214, 0x20172022, 0x400e840c, 0x400648812, 0x80589060, 0x200634048, 0x4108029c, 0x22101162, 0x108200916, 0x80c040e8, 0x4100420b2, 0x20402054c]
  let G : SimpleGraph (Fin 35) := {
    Adj := fun u v => u ≠ v ∧ rows[min u.val v.val]!.testBit (max u.val v.val) = true
    symm := ⟨fun {u v} h => ⟨h.1.symm, by simpa only [min_comm v.val u.val,max_comm v.val u.val] using h.2⟩⟩
    loopless := ⟨fun u h => h.1 rfl⟩ }
  let : DecidableRel G.Adj := fun u v => inferInstanceAs
    (Decidable (u ≠ v ∧ rows[min u.val v.val]!.testBit (max u.val v.val) = true))
  refine ⟨G,exclude_search G 3 ?_,exclude_search Gᶜ 9 ?_⟩
  · decide +kernel +revert
  · let scan := Nat.rec (motive := fun _ => List (Fin 35) → Bool) (fun _ => true)
      (fun j rec vs => if vs.length < j+1 then false else
        vs.any fun v => rec (vs.filter fun w => decide (v < w ∧ Gᶜ.Adj v w)))
    change (if (List.finRange 35).length<9 then false else
      (List.finRange 35).any fun v => scan 8 ((List.finRange 35).filter fun w => decide (v<w ∧ Gᶜ.Adj v w)))=false
    rw [if_neg (by decide),List.any_eq_false]
    intro v _
    fin_cases v <;> decide +kernel +revert

end OMA.Ramsey35

/- Verbatim previously merged counting lemmas from open-math-agents PR 9042. -/
open SimpleGraph Finset
namespace RamseyDeficiency
theorem removed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ht : G.CliqueFree 3) (v : Fin n) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set (Fin n))
    D.edgeFinset.card+(∑ i ∈ N, G.degree i) ≤ G.edgeFinset.card := by
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set (Fin n))
  let U : Finset (Fin n) := univ
  let W (X Y : Finset (Fin n)) := ∑ i ∈ X, ∑ j ∈ Y, (if G.Adj i j then 1 else 0 : ℕ)
  have flip (X Y) : W X Y = W Y X := by
    unfold W
    rw [Finset.sum_comm]
    simp only [G.adj_comm]
  have partition (X Y) : W X Y + W Xᶜ Y = W U Y := Finset.sum_add_sum_compl X _
  have total (X) : W X U=∑ i ∈ X, G.degree i := by
    simp [W,U,SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
  have vanish : W N N=0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    have un : ¬G.Adj a b := fun adj => G.isIndepSet_neighborSet_of_triangleFree ht v
      ((G.mem_neighborFinset _ _).mp ha) ((G.mem_neighborFinset _ _).mp hb) adj.ne adj
    simp [un]
  have inside : B ⊆ Nᶜ := fun i hi => Finset.mem_compl.mpr fun h =>
    ((Gᶜ.mem_neighborFinset _ _).mp hi).2 ((G.mem_neighborFinset _ _).mp h)
  have inc (X Y Z : Finset (Fin n)) (sub : X ⊆ Y) : W X Z ≤ W Y Z :=
    Finset.sum_le_sum_of_subset_of_nonneg sub (by intros; omega)
  have le : W B B ≤ W Nᶜ Nᶜ :=
    (inc B Nᶜ B inside).trans ((flip Nᶜ B) ▸ inc B Nᶜ Nᶜ inside)
  have db : W B B = 2*D.edgeFinset.card := by
    calc
      W B B = ∑ i : B, ∑ j ∈ B, (if G.Adj i.val j then 1 else 0 : ℕ) :=
        (Finset.sum_coe_sort B _).symm
      _ = ∑ i : B, ∑ j : B, (if D.Adj i j then 1 else 0 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (Finset.sum_coe_sort B (fun j => if G.Adj i.val j then 1 else 0)).symm
      _ = ∑ i : B, D.degree i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
        exact Finset.sum_boole (R:=ℕ) (D.Adj i) univ
      _ = _ := D.sum_degrees_eq_twice_card_edges
  have p1 := partition N U
  have p2 := partition N N
  have p3 := partition N Nᶜ
  have f1 := flip Nᶜ U
  have f2 := flip N U
  have f3 := flip Nᶜ N
  have a := total N
  have b := total U
  have all : (∑ i ∈ U,G.degree i) = 2*G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  change D.edgeFinset.card+(∑ i ∈ N,G.degree i)≤G.edgeFinset.card
  omega

theorem sum_neighbor_degrees {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∑ v, ∑ w ∈ G.neighborFinset v, G.degree w) = ∑ v, G.degree v ^ 2 := by
  simp only [SimpleGraph.neighborFinset_eq_filter,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  calc
    (∑ v, if G.Adj v w then G.degree w else 0) =
        ∑ v ∈ univ.filter (G.Adj w), G.degree w := by
          rw [Finset.sum_filter]
          simp only [G.adj_comm]
    _ = G.degree w^2 := by
      rw [← G.neighborFinset_eq_filter,Finset.sum_const,G.card_neighborFinset_eq_degree,nsmul_eq_mul,pow_two]
      norm_cast



end RamseyDeficiency

namespace RamseyDeficiency
open Finset SimpleGraph

/-- Restrict the anti-neighbourhood of v to any m of its vertices. An
independent k-set in the restriction would extend by v. -/
theorem extract_anti {n m k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tri : G.CliqueFree 3) (ind : Gᶜ.CliqueFree (k+1)) (v : Fin n)
    (enough : m≤Gᶜ.degree v) :
    let D := G.induce ((Gᶜ.neighborFinset v : Finset (Fin n)) : Set (Fin n))
    ∃ (K : SimpleGraph (Fin m)) (_ : DecidableRel K.Adj),
      K.CliqueFree 3 ∧ Kᶜ.CliqueFree k ∧ K.edgeFinset.card≤D.edgeFinset.card := by
  classical
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set (Fin n))
  have card : m ≤ Fintype.card B := by rw [Fintype.card_coe]; exact enough
  obtain ⟨f,_⟩ := Function.Embedding.exists_of_card_le_finset (α:=Fin m) (s:=(univ : Finset B)) (by simpa using card)
  let K := D.comap f
  let e : K ↪g D := SimpleGraph.Embedding.comap f D
  let into : D ↪g G := SimpleGraph.Embedding.comap (Function.Embedding.subtype (· ∈ B)) G
  let all : K ↪g G := e.trans into
  have transport := Fintype.card_le_of_embedding e.toCopy.mapEdgeSet
  rw [K.card_edgeSet,D.card_edgeSet] at transport
  refine ⟨K,inferInstance,CliqueFree.comap all.isContained tri,?_,transport⟩
  intro S cl
  have mapped : Gᶜ.IsNClique k (S.map all.toEmbedding) := by
    refine ⟨?_,(card_map _).trans cl.card_eq⟩
    intro x hx y hy ne
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    exact (SimpleGraph.Embedding.complEquiv all).map_adj_iff.mpr
      (cl.isClique ha hb (fun h => ne (congrArg all h)))
  apply ind _ (mapped.insert (a:=v) ?_)
  intro w hw
  obtain ⟨i,_,rfl⟩ := mem_map.mp hw
  exact (Gᶜ.mem_neighborFinset _ _).mp (f i).property

/-- In any hypothetical 36-vertex counterexample, some 27-vertex induced
subgraph is (3,8)-Ramsey and has at most 80 edges. -/
theorem sparse_anti (G : SimpleGraph (Fin 36)) [DecidableRel G.Adj]
    (tri : G.CliqueFree 3) (ind : Gᶜ.CliqueFree 9) :
    ∃ (K : SimpleGraph (Fin 27)) (_ : DecidableRel K.Adj),
       K.CliqueFree 3 ∧ Kᶜ.CliqueFree 8 ∧ K.edgeFinset.card≤80 := by
  classical
  have cap (v : Fin 36) : G.degree v ≤ 8 := by
    by_contra! bad
    apply ind.mono bad (G.neighborFinset v)
    refine ⟨?_,rfl⟩
    rw [G.coe_neighborFinset,G.isClique_compl]
    exact G.isIndepSet_neighborSet_of_triangleFree tri v
  let D (v : Fin 36) := G.induce ((Gᶜ.neighborFinset v : Finset (Fin 36)) : Set (Fin 36))
  have good : ∃ v, (D v).edgeFinset.card≤80 := by
    by_contra! none
    have point (v : Fin 36) : 81+(∑ w∈G.neighborFinset v,G.degree w) ≤ G.edgeFinset.card :=
      le_trans (Nat.add_le_add_right (none v) _) (removed G tri v)
    have total := Finset.sum_le_sum (s:=(univ : Finset (Fin 36))) (fun v _ => point v)
    rw [Finset.sum_add_distrib,sum_neighbor_degrees] at total
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at total
    have numerical (v : Fin 36) : 18*G.degree v ≤ 80+G.degree v^2 := by
      have gap : 0≤(8-(G.degree v : ℤ)) := by have hv := cap v; omega
      have product := mul_nonneg gap (show 0≤10-(G.degree v : ℤ) by omega)
      zify
      nlinarith
    have lower := Finset.sum_le_sum (s:=(univ : Finset (Fin 36))) (fun v _ => numerical v)
    rw [← Finset.mul_sum,G.sum_degrees_eq_twice_card_edges,Finset.sum_add_distrib] at lower
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at lower
    omega
  obtain ⟨v,edges⟩ := good
  have size : 27≤Gᶜ.degree v := by rw [G.degree_compl,Fintype.card_fin]; have := cap v; omega
  obtain ⟨K,dec,triK,indK,le⟩ := extract_anti (k:=8) G tri ind v size
  exact ⟨K,dec,triK,indK,le.trans edges⟩

end RamseyDeficiency

namespace RamseyDeficiency
open Finset SimpleGraph

/-- Deleting a vertex removes at least the incident edges counted by its degree. -/
theorem delete_edge_budget {n : ℕ} (G : SimpleGraph (Fin (n+1))) [DecidableRel G.Adj]
    (v : Fin (n+1)) : (G.comap v.succAboveEmb).edgeFinset.card+G.degree v ≤ G.edgeFinset.card := by
  classical
  let f := v.succAboveEmb
  let H := G.comap f
  let S := H.edgeFinset.map f.sym2Map
  have sub : S ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨xy,hxy,rfl⟩ := Finset.mem_map.mp he
    induction xy using Sym2.inductionOn with
    | _ i j =>
      exact G.mem_edgeFinset.mpr (show G.Adj (f i) (f j) from H.mem_edgeSet.mp (H.mem_edgeFinset.mp hxy))
  have apart : Disjoint S (G.incidenceFinset v) := by
    apply Finset.disjoint_left.mpr
    intro e he hv
    obtain ⟨xy,_,rfl⟩ := Finset.mem_map.mp he
    induction xy using Sym2.inductionOn with
    | _ i j =>
      have touch : v ∈ s(f i,f j) := ((G.mem_incidenceFinset v _).mp hv).2
      rcases Sym2.mem_iff.mp touch with left|right
      · exact Fin.succAbove_ne v i left.symm
      · exact Fin.succAbove_ne v j right.symm
  have bound := Finset.card_le_card (Finset.union_subset sub (G.incidenceFinset_subset v))
  rw [Finset.card_union_of_disjoint apart, G.card_incidenceFinset_eq_degree] at bound
  simpa only [S,H,f,Finset.card_map] using bound

/-- Average an exact-order edge bound across every one-vertex deletion. -/
theorem delete_average {a b n e : ℕ}
    (prev : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], H.CliqueFree a → Hᶜ.CliqueFree b → e≤H.edgeFinset.card)
    (G : SimpleGraph (Fin (n+1))) [DecidableRel G.Adj] (tri : G.CliqueFree a) (ind : Gᶜ.CliqueFree b) :
    (n+1)*e+2*G.edgeFinset.card≤(n+1)*G.edgeFinset.card := by
  classical
  have each (v : Fin (n+1)) : e+G.degree v≤G.edgeFinset.card := by
    let f := v.succAboveEmb
    let H := G.comap f
    let emb : H ↪g G := SimpleGraph.Embedding.comap f G
    have min := prev H (CliqueFree.comap emb.isContained tri)
      (CliqueFree.comap (SimpleGraph.Embedding.complEquiv emb).isContained ind)
    exact (Nat.add_le_add_right min _).trans (delete_edge_budget G v)
  have sum := Finset.sum_le_sum (s:=univ) (fun v _ => each v)
  rw [Finset.sum_add_distrib,G.sum_degrees_eq_twice_card_edges] at sum
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using sum

theorem propagate22 (small : (∀ (J : SimpleGraph (Fin 22)) [DecidableRel J.Adj], J.CliqueFree 3 → Jᶜ.CliqueFree 7 → 59≤J.edgeFinset.card)) :
    (∀ (J : SimpleGraph (Fin 23)) [DecidableRel J.Adj], J.CliqueFree 3 → Jᶜ.CliqueFree 7 → 65≤J.edgeFinset.card) ∧ (∀ (J : SimpleGraph (Fin 24)) [DecidableRel J.Adj], J.CliqueFree 3 → Jᶜ.CliqueFree 7 → 71≤J.edgeFinset.card) ∧ (∀ (J : SimpleGraph (Fin 25)) [DecidableRel J.Adj], J.CliqueFree 3 → Jᶜ.CliqueFree 7 → 78≤J.edgeFinset.card) ∧ (∀ (J : SimpleGraph (Fin 26)) [DecidableRel J.Adj], J.CliqueFree 3 → Jᶜ.CliqueFree 7 → 85≤J.edgeFinset.card) := by
  have next {n e k : ℕ} (h : (∀ (J : SimpleGraph (Fin n)) [DecidableRel J.Adj], J.CliqueFree 3 → Jᶜ.CliqueFree 7 → e≤J.edgeFinset.card))
      (round : ∀ z : ℕ, (n+1)*e+2*z≤(n+1)*z → k≤z) : (∀ (J : SimpleGraph (Fin (n+1))) [DecidableRel J.Adj], J.CliqueFree 3 → Jᶜ.CliqueFree 7 → k≤J.edgeFinset.card) :=
    fun G _ tri ind => round _ (delete_average h G tri ind)
  have a := next (k:=65) small (by omega)
  have b := next (k:=71) a (by omega)
  have c := next (k:=78) b (by omega)
  exact ⟨a,b,c,next c (by omega)⟩

end RamseyDeficiency

namespace RamseyDeficiency
open Finset SimpleGraph

/-- Deletion averaging at orders 23 through 26 removes the need for a
separate 23-vertex Ramsey-number premise. -/
theorem min_four_of_small (G : SimpleGraph (Fin 27)) [DecidableRel G.Adj]
    (tri : G.CliqueFree 3) (ind : Gᶜ.CliqueFree 8) (edges : G.edgeFinset.card≤80)
    (bound : ∀ (n : ℕ),19≤n→n≤22→∀ (D : SimpleGraph (Fin n)) [DecidableRel D.Adj],
      D.CliqueFree 3 → Dᶜ.CliqueFree 7 → (if n=22 then 59 else if n=21 then 51 else if n=20 then 44 else 37)≤D.edgeFinset.card) :
    ∀ v,4≤G.degree v := by
  classical
  let lo (d : ℕ) := ([85,78,71,65,59,51,44,37] : List ℕ)[d]!
  let cost (d : ℕ) := ([41,29,19,12,7,2,0,0] : List ℕ)[d]!
  obtain ⟨h23,h24,h25,h26⟩ := propagate22 (bound 22 (by decide) (by decide))
  have densities (d : ℕ) (hd : d≤7) : (∀ (J : SimpleGraph (Fin (26-d))) [DecidableRel J.Adj], J.CliqueFree 3 → Jᶜ.CliqueFree 7 → (lo d)≤J.edgeFinset.card) := by
    interval_cases d
    · exact h26
    · exact h25
    · exact h24
    · exact h23
    · exact bound 22 (by decide) (by decide)
    · exact bound 21 (by decide) (by decide)
    · exact bound 20 (by decide) (by decide)
    · exact bound 19 (by decide) (by decide)
  have cap (v : Fin 27) : G.degree v≤7 := by
    by_contra! bad
    apply ind.mono bad (G.neighborFinset v)
    refine ⟨?_,rfl⟩
    rw [G.coe_neighborFinset,G.isClique_compl]
    exact G.isIndepSet_neighborSet_of_triangleFree tri v
  have localBound (v : Fin 27) : lo (G.degree v)+(∑ w∈G.neighborFinset v,G.degree w)≤G.edgeFinset.card := by
    obtain ⟨K,dec,tk,ik,le⟩ := extract_anti (m:=26-G.degree v) (k:=7) G tri ind v (by rw [G.degree_compl,Fintype.card_fin])
    have small := @densities (G.degree v) (cap v) K dec tk ik
    exact le_trans (Nat.add_le_add_right (small.trans le) _) (removed G tri v)
  have affine (d : ℕ) (hd : d≤7) : 44+6*d+cost d≤d^2+lo d := by interval_cases d <;> decide
  have total : (∑ v,cost (G.degree v))≤12 := by
    have top := Finset.sum_le_sum (s:=(univ : Finset (Fin 27))) (fun v _ => localBound v)
    have bottom := Finset.sum_le_sum (s:=(univ : Finset (Fin 27))) (fun v _ => affine _ (cap v))
    rw [Finset.sum_add_distrib,sum_neighbor_degrees] at top
    simp only [Finset.sum_add_distrib,←Finset.mul_sum,G.sum_degrees_eq_twice_card_edges,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at bottom top
    omega
  have single (v : Fin 27) : cost (G.degree v)≤12 :=
    (Finset.single_le_sum (f:=fun x => cost (G.degree x)) (fun _ _ => Nat.zero_le _) (mem_univ v)).trans total
  intro v
  by_contra! bad
  have d3 : G.degree v=3 := by
    have bound := single v
    interval_cases h : G.degree v <;> simp_all [cost]
  have nb (w : Fin 27) (adj : w∈G.neighborFinset v) : 6≤G.degree w := by
    have ne : v≠w := (G.mem_neighborFinset v w).mp adj |>.ne
    have cost2 := Finset.sum_le_sum_of_subset_of_nonneg (s:=({v,w} : Finset (Fin 27))) (t:=univ)
      (f:=fun x => cost (G.degree x)) (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    have bound : 12+cost (G.degree w)≤12 := by simpa [ne,d3,cost] using cost2.trans total
    by_contra! tooLow
    interval_cases h : G.degree w <;> simp_all [cost]
  have six : (∑ _w∈G.neighborFinset v,(6:ℕ)) ≤ ∑ w∈G.neighborFinset v,G.degree w := Finset.sum_le_sum nb
  have many : 18≤∑ w∈G.neighborFinset v,G.degree w := by simpa [d3] using six
  have low := localBound v
  rw [d3,show lo 3=65 by rfl] at low
  omega

end RamseyDeficiency

namespace Ramsey39

/-- Every 27-vertex degree histogram satisfying the four deficiency bounds
and having at most 80 edges belongs to one of two explicitly bounded families. -/
theorem histograms {a4 a5 a6 a7 e : Nat}
    (vertices : a4+a5+a6+a7=27)
    (degrees : 4*a4+5*a5+6*a6+7*a7=2*e)
    (deficiency : (16+59)*a4+(25+51)*a5+(36+44)*a6+(49+37)*a7≤27*e)
    (edges : e≤80) :
    e=80 ∧
      ((a4=0 ∧ a7≤4 ∧ a5=2+a7 ∧ a6=25-2*a7) ∨
       (a4=1 ∧ a7≤2 ∧ a5=a7 ∧ a6=26-2*a7)) := by
  omega

end Ramsey39

namespace Ramsey39
open SimpleGraph Finset
open scoped Classical

/-- Group any sum by the four permitted degrees of its vertices. -/
theorem class_sum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (range : ∀ v,4≤G.degree v ∧ G.degree v≤7) (S : Finset (Fin n)) (f : ℕ→ℕ) :
    let a (d : ℕ) := (S.filter (fun v => G.degree v=d)).card
    (∑ v ∈ S, f (G.degree v))=f 4*a 4+f 5*a 5+f 6*a 6+f 7*a 7 := by
  intro a
  have one (v : Fin n) : f (G.degree v) =
      (if G.degree v=4 then f 4 else 0)+(if G.degree v=5 then f 5 else 0)+
      (if G.degree v=6 then f 6 else 0)+(if G.degree v=7 then f 7 else 0) := by
    obtain h|h|h|h : G.degree v=4 ∨ G.degree v=5 ∨ G.degree v=6 ∨ G.degree v=7 := by
      have := range v
      omega
    all_goals simp [h]
  simpa [a,Finset.sum_add_distrib,Finset.sum_ite,Nat.mul_comm] using Finset.sum_congr (s₁:=S) (s₂:=S) rfl (fun v _ => one v)

theorem four_degree_data (G : SimpleGraph (Fin 27)) [DecidableRel G.Adj]
    (tri : G.CliqueFree 3) (ind : Gᶜ.CliqueFree 8) (min : ∀ v,4≤G.degree v) (edges : G.edgeFinset.card≤80)
    (bound : ∀ (n : ℕ),19≤n→n≤22→∀ (D : SimpleGraph (Fin n)) [DecidableRel D.Adj],
      D.CliqueFree 3 → Dᶜ.CliqueFree 7 → (if n=22 then 59 else if n=21 then 51 else if n=20 then 44 else 37)≤D.edgeFinset.card) :
    let a (d : ℕ) := (univ.filter fun v => G.degree v=d).card
    let low (d : ℕ) := if d=4 then 59 else if d=5 then 51 else if d=6 then 44 else 37
    (∀ v,low (G.degree v)+(∑ w∈G.neighborFinset v,G.degree w)≤G.edgeFinset.card) ∧
    (∀ v,4≤G.degree v ∧ G.degree v≤7) ∧ G.edgeFinset.card=80 ∧
      ((a 4=0 ∧ a 7≤4 ∧ a 5=2+a 7 ∧ a 6=25-2*a 7) ∨
       (a 4=1 ∧ a 7≤2 ∧ a 5=a 7 ∧ a 6=26-2*a 7)) := by
  intro a low
  have range (v : Fin 27) : 4≤G.degree v ∧ G.degree v≤7 := by
    refine ⟨min v,?_⟩
    by_contra! h
    apply ind.mono h (G.neighborFinset v)
    refine ⟨?_,rfl⟩
    rw [G.coe_neighborFinset,G.isClique_compl]
    exact G.isIndepSet_neighborSet_of_triangleFree tri v
  have localBound (v : Fin 27) : low (G.degree v)+(∑ w∈G.neighborFinset v,G.degree w)≤G.edgeFinset.card := by
    have r := range v
    have card := G.degree_compl v
    rw [Fintype.card_fin] at card
    let n := Gᶜ.degree v
    obtain ⟨D,dD,tD,iD,sub⟩ := RamseyDeficiency.extract_anti G tri ind v (m:=n) le_rfl
    let := dD
    have lo := bound n (by dsimp [n]; omega) (by dsimp [n]; omega) D tD iD
    have eq : (if n=22 then 59 else if n=21 then 51 else if n=20 then 44 else 37)=low (G.degree v) := by
      dsimp [low,n]
      split_ifs <;> omega
    rw [eq] at lo
    have rem := RamseyDeficiency.removed G tri v
    omega
  have total := Finset.sum_le_sum (s:=univ) (fun v _ => localBound v)
  rw [Finset.sum_add_distrib,RamseyDeficiency.sum_neighbor_degrees] at total
  have lhs : (∑ v,low (G.degree v)) + (∑ v,G.degree v^2) =
      ∑ v, (fun d => low d+d^2) (G.degree v) := (Finset.sum_add_distrib ..).symm
  rw [lhs,class_sum G range univ (fun d => low d + d^2)] at total
  have vertices := class_sum G range univ (fun _ => 1)
  have degrees := class_sum G range univ id
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,one_mul] at vertices
  simp only [id_eq,G.sum_degrees_eq_twice_card_edges] at degrees
  refine ⟨localBound,range,histograms (a4:=a 4) (a5:=a 5) (a6:=a 6) (a7:=a 7) vertices.symm degrees.symm ?_ edges⟩
  simpa [low,a,Nat.mul_comm,add_comm] using total

end Ramsey39

namespace Ramsey39
open SimpleGraph Finset
open scoped Classical

/-- A degree-four vertex would be unique, and at most two of its four
neighbours could have degree five. The 22-point deletion then exceeds budget. -/
theorem profile (G : SimpleGraph (Fin 27)) [DecidableRel G.Adj] (tri : G.CliqueFree 3)
    (ind : Gᶜ.CliqueFree 8) (min : ∀ v,4≤G.degree v) (edges : G.edgeFinset.card≤80)
    (bound : ∀ (n : ℕ),19≤n→n≤22→∀ (D : SimpleGraph (Fin n)) [DecidableRel D.Adj],
      D.CliqueFree 3 → Dᶜ.CliqueFree 7 → (if n=22 then 59 else if n=21 then 51 else if n=20 then 44 else 37)≤D.edgeFinset.card) :
    let a (d : ℕ) := (univ.filter fun v => G.degree v=d).card
    let low (d : ℕ) := if d=4 then 59 else if d=5 then 51 else if d=6 then 44 else 37
    (∀ v,low (G.degree v)+(∑ w∈G.neighborFinset v,G.degree w)≤80) ∧
    (∀ v,5≤G.degree v ∧ G.degree v≤7) ∧ G.edgeFinset.card=80 ∧
    (a 4=0 ∧ a 7≤4 ∧ a 5=2+a 7 ∧ a 6=25-2*a 7) := by
  intro a low
  obtain ⟨localBound,range,nb,cases⟩ := four_degree_data G tri ind min edges bound
  refine ⟨fun v => (localBound v).trans edges,?_⟩
  suffices a 4=0 ∧ a 7≤4 ∧ a 5=2+a 7 ∧ a 6=25-2*a 7 by
    refine ⟨fun v => ⟨?_,(range v).2⟩,nb,this⟩
    by_contra! bad
    have h4 : G.degree v=4 := by have := (range v).1; omega
    have h : v∈univ.filter (fun w => G.degree w=4) := by simp [h4]
    have pos := Finset.card_pos.mpr ⟨v,h⟩
    change 0<a 4 at pos
    omega
  rcases cases with yes|⟨ha,h7,h5,_⟩
  · exact yes
  exfalso
  let L := univ.filter (fun w => G.degree w=4)
  have cL : L.card=1 := ha
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0<L.card by omega)
  have deg := (Finset.mem_filter.mp hv).2
  let N := G.neighborFinset v
  let b (d : ℕ) := (N.filter (fun w => G.degree w=d)).card
  have b4 : b 4=0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨nw,dw⟩ := Finset.mem_filter.mp hw
    have inL : w∈L := Finset.mem_filter.mpr ⟨mem_univ _,dw⟩
    have eq := Finset.card_le_one_iff.mp (show L.card≤1 by omega) hv inL
    exact ((G.mem_neighborFinset _ _).mp nw).ne eq
  have b5 : b 5≤a 5 := Finset.card_le_card (Finset.filter_subset_filter _ (subset_univ N))
  have sz := class_sum G range N (fun _ => 1)
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,one_mul] at sz
  change N.card=b 4+b 5+b 6+b 7 at sz
  have sn : N.card=4 := deg
  have sums := class_sum G range N id
  change (∑ w∈N,G.degree w)=4*b 4+5*b 5+6*b 6+7*b 7 at sums
  have lo := localBound v
  rw [deg] at lo
  change 59+(∑ w∈N,G.degree w)≤G.edgeFinset.card at lo
  change a 5=a 7 at h5
  change a 7≤2 at h7
  omega

end Ramsey39

/- Vertex-row restriction from the public Ramsey reduction in PR 9042. -/
namespace Ramsey39
open SimpleGraph Finset
lemma lift_card {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hi : Gᶜ.CliqueFree 8) (S : Finset (Gᶜ.neighborFinset v))
    (cl : ((G.induce ((Gᶜ.neighborFinset v : Finset V) : Set V))ᶜ).IsClique S) :
    S.card ≤ 6 := by
  classical
  let B := Gᶜ.neighborFinset v
  let f : B ↪ V := Function.Embedding.subtype _
  have free : Gᶜ.IsClique (S.map f) := by
    intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    exact ⟨hxy,(cl ha hb (fun h => hxy (congrArg f h))).2⟩
  have hv : v ∉ S.map f := by
    intro hm
    obtain ⟨b,_,eq⟩ := mem_map.mp hm
    exact ((Gᶜ.mem_neighborFinset _ _).mp b.2).ne eq.symm
  have ext : Gᶜ.IsClique (insert v (S.map f)) := free.insert (by
    intro b hb _
    obtain ⟨i,_,rfl⟩ := mem_map.mp hb
    exact (Gᶜ.mem_neighborFinset _ _).mp i.2)
  have lim : (insert v (S.map f)).card < 8 := lt_of_not_ge (fun h =>
    hi.mono h _ ⟨by simpa only [Finset.coe_insert] using ext,rfl⟩)
  rw [card_insert_of_notMem hv,card_map] at lim
  omega

theorem neighborhood_data {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 8) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set V)
    let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
    D.CliqueFree 3 ∧ Dᶜ.CliqueFree 7 ∧
      (∀ i, Dᶜ.IsClique (A i)) ∧
      (∀ (J : Finset N) (S : Finset B), Dᶜ.IsClique S → (∀ a ∈ J, Disjoint (A a) S) → J.card+S.card≤7) ∧
      N.card + (∑ a, (A a).card) ≤ ∑ a ∈ N, G.degree a := by
  classical
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set V)
  let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
  let f : B ↪ V := Function.Embedding.subtype _
  let g : N ↪ V := Function.Embedding.subtype _
  let em : D ↪g G := SimpleGraph.Embedding.comap f G
  have nd (a : N) := (G.mem_neighborFinset v a.val).mp a.2
  have bd (a : B) := (Gᶜ.mem_neighborFinset v a.val).mp a.2
  have split (a : N) (b : B) : a.val≠b.val := fun eq => (bd b).2 (eq ▸ nd a)
  have nr (a b : N) : ¬G.Adj a.val b.val := by
    intro h
    exact G.isIndepSet_neighborSet_of_triangleFree ht v (nd a) (nd b) h.ne h
  change D.CliqueFree 3 ∧ Dᶜ.CliqueFree 7 ∧ (∀ i, Dᶜ.IsClique (A i)) ∧ _ ∧ _
  refine ⟨CliqueFree.comap em.isContained ht,?_,?_,?_,?_⟩
  · intro S hS
    have h := lift_card G v hi S hS.isClique
    have eq := hS.card_eq
    omega
  · intro i a ha b hb hne
    refine ⟨hne,?_⟩
    intro h
    exact G.isIndepSet_neighborSet_of_triangleFree ht i.val (mem_filter.mp ha).2 (mem_filter.mp hb).2
      (Subtype.val_injective.ne hne) h
  · intro J S cl dis
    let X := J.map g
    let Y := S.map f
    have apart : Disjoint X Y := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨a,_,rfl⟩ := mem_map.mp hx
      obtain ⟨b,_,eq⟩ := mem_map.mp hy
      exact split a b eq.symm
    have sx : Gᶜ.IsClique X := by
      intro u hu w hw hne
      obtain ⟨a,_,rfl⟩ := mem_map.mp hu
      obtain ⟨b,_,rfl⟩ := mem_map.mp hw
      exact ⟨hne,nr a b⟩
    have sy : Gᶜ.IsClique Y := by
      intro u hu w hw hne
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hw
      exact ⟨hne,(cl ha hb (fun h => hne (congrArg f h))).2⟩
    have cross (u : V) (hu : u∈X) (w : V) (hw : w∈Y) : Gᶜ.Adj u w := by
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hw
      exact ⟨split a b,fun h => Finset.disjoint_left.mp (dis a ha) (mem_filter.mpr ⟨mem_univ _,h⟩) hb⟩
    have full : Gᶜ.IsClique (X ∪ Y) := by
      intro u hu w hw hne
      rcases hu with hu|hu <;> rcases hw with hw|hw
      · exact sx hu hw hne
      · exact cross _ hu _ hw
      · exact (cross _ hw _ hu).symm
      · exact sy hu hw hne
    have lim : (X ∪ Y).card < 8 := lt_of_not_ge (fun h =>
      hi.mono h _ ⟨by simpa only [Finset.coe_union] using full,rfl⟩)
    rw [card_union_of_disjoint apart,card_map,card_map] at lim
    omega
  · have each (a : N) : 1 + (A a).card ≤ G.degree a.val := by
      let Y := (A a).map f
      have nv : v ∉ Y := by
        rintro mem
        obtain ⟨b,_,eq⟩ := mem_map.mp mem
        exact (bd b).1 eq.symm
      have sub : insert v Y ⊆ G.neighborFinset a.val := by
        intro w hw
        rcases mem_insert.mp hw with rfl|mem
        · exact (G.mem_neighborFinset _ _).mpr (nd a).symm
        · obtain ⟨b,hb,rfl⟩ := mem_map.mp mem
          exact (G.mem_neighborFinset _ _).mpr (mem_filter.mp hb).2
      have le := card_le_card sub
      rw [card_insert_of_notMem nv,card_map,G.card_neighborFinset_eq_degree] at le
      omega
    have total := Finset.sum_le_sum (s := (univ : Finset N)) (fun a _ => each a)
    change N.card + (∑ a : N,(A a).card) ≤ ∑ a ∈ N,G.degree a
    rw [← Finset.sum_coe_sort N (fun i => G.degree i)]
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.mul_one,
      Fintype.card_coe,Nat.cast_id] using total



end Ramsey39

namespace RamseyDeficiency
open Finset SimpleGraph

/-- The neighbors of a neighbor of the root all lie in the antineighborhood,
apart from the root itself. -/
theorem row_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ht : G.CliqueFree 3) (v : Fin n) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let A (i : N) := (univ : Finset B).filter (fun x => G.Adj i.val x.val)
    ∀ i : N, (A i).card+1=G.degree i.val := by
  intro N B A i
  let f : B ↪ Fin n := ⟨Subtype.val,Subtype.val_injective⟩
  have root := (G.mem_neighborFinset ..).mp i.property
  have eq : (A i).map f=(G.neighborFinset i.val).erase v := by
    ext y
    constructor
    · intro h
      obtain ⟨x,hx,rfl⟩ := mem_map.mp h
      exact mem_erase.mpr ⟨((Gᶜ.mem_neighborFinset ..).mp x.property).ne.symm,
        (G.mem_neighborFinset ..).mpr (mem_filter.mp hx).2⟩
    · intro h
      obtain ⟨ne,ha⟩ := mem_erase.mp h
      have adj := (G.mem_neighborFinset ..).mp ha
      have notAdj : ¬G.Adj v y := fun hit =>
        G.isIndepSet_neighborSet_of_triangleFree ht v root hit adj.ne adj
      exact mem_map.mpr ⟨⟨y,(Gᶜ.mem_neighborFinset ..).mpr ⟨ne.symm,notAdj⟩⟩,
        mem_filter.mpr ⟨mem_univ _,adj⟩,rfl⟩
  rw [←card_map (f:=f) (s:=A i),eq,card_erase_add_one ((G.mem_neighborFinset ..).mpr root.symm)]
  rfl

theorem removed_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ht : G.CliqueFree 3) (v : Fin n) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set (Fin n))
    D.edgeFinset.card+(∑ i ∈ N, G.degree i) = G.edgeFinset.card := by
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set (Fin n))
  let U : Finset (Fin n) := univ
  let W (X Y : Finset (Fin n)) := ∑ i ∈ X, ∑ j ∈ Y, (if G.Adj i j then 1 else 0 : ℕ)
  have flip (X Y) : W X Y = W Y X := by
    unfold W
    rw [Finset.sum_comm]
    simp only [G.adj_comm]
  have partition (X Y) : W X Y + W Xᶜ Y = W U Y := Finset.sum_add_sum_compl X _
  have total (X) : W X U=∑ i ∈ X, G.degree i := by
    simp [W,U,SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
  have vanish : W N N=0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    have un : ¬G.Adj a b := fun adj => G.isIndepSet_neighborSet_of_triangleFree ht v
      ((G.mem_neighborFinset _ _).mp ha) ((G.mem_neighborFinset _ _).mp hb) adj.ne adj
    simp [un]
  have complement : Nᶜ=insert v B := by
    ext x
    by_cases h : x=v
    · subst x
      simp [N]
    · simp only [N,B,mem_compl,mem_insert,G.mem_neighborFinset,Gᶜ.mem_neighborFinset,SimpleGraph.compl_adj]; tauto
  have absent : v∉B := by simp [B]
  have drop {Z : Finset (Fin n)} (isolated : ∀ j∈Z,¬G.Adj v j) : W Nᶜ Z=W B Z := by
    rw [complement]
    simp [W,sum_insert absent]
    exact fun x hx => isolated x hx
  have outside : ∀ j∈Nᶜ,¬G.Adj v j := fun j hj adj => (mem_compl.mp hj) ((G.mem_neighborFinset ..).mpr adj)
  have outB : ∀ j∈B,¬G.Adj v j := fun j hj => ((Gᶜ.mem_neighborFinset ..).mp hj).2
  have exactCut : W Nᶜ Nᶜ=W B B := (drop outside).trans ((flip B Nᶜ).trans (drop outB))
  have db : W B B = 2*D.edgeFinset.card := by
    calc
      W B B = ∑ i : B, ∑ j ∈ B, (if G.Adj i.val j then 1 else 0 : ℕ) :=
        (Finset.sum_coe_sort B _).symm
      _ = ∑ i : B, ∑ j : B, (if D.Adj i j then 1 else 0 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (Finset.sum_coe_sort B (fun j => if G.Adj i.val j then 1 else 0)).symm
      _ = ∑ i : B, D.degree i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
        exact Finset.sum_boole (R:=ℕ) (D.Adj i) univ
      _ = _ := D.sum_degrees_eq_twice_card_edges
  have p1 := partition N U
  have p2 := partition N N
  have p3 := partition N Nᶜ
  have f1 := flip Nᶜ U
  have f2 := flip N U
  have f3 := flip Nᶜ N
  have a := total N
  have b := total U
  have all : (∑ i ∈ U,G.degree i) = 2*G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  change D.edgeFinset.card+(∑ i ∈ N,G.degree i)=G.edgeFinset.card
  omega

end RamseyDeficiency

namespace RamseyDeficiency
open Finset SimpleGraph

set_option maxHeartbeats 800000 in
/-- With degrees 5,6,7, failure of a 51-edge antineighborhood forces every
low-degree vertex to have exactly two low neighbors and a 52-edge remainder. -/
theorem extreme_seed_or_four (G : SimpleGraph (Fin 27)) [DecidableRel G.Adj]
    (tri : G.CliqueFree 3) (edges : G.edgeFinset.card=80)
    (lo : ∀ u,5≤G.degree u) (hi : ∀ u,G.degree u≤7) :
    let A (v : Fin 27) := (G.induce (Gᶜ.neighborFinset v : Set (Fin 27))).edgeFinset.card
    let D (j : ℕ) := univ.filter (fun u : Fin 27 => G.degree u=j)
    (∀ v,G.degree v=5 → 51≤A v) → (∀ v,G.degree v=6 → 44≤A v) → (∀ v,G.degree v=7 → 37≤A v) →
    (∃ v,G.degree v=5 ∧ A v=51) ∨
    ((D 5).card=4 ∧ ∀ v∈D 5, (G.neighborFinset v ∩ D 5).card=2 ∧
      (G.neighborFinset v ∩ D 7).card=0 ∧ A v=52) := by
  intro A D five six seven
  classical
  by_cases seed : ∃ v,G.degree v=5 ∧ A v=51
  · exact Or.inl seed
  right
  let N := G.neighborFinset
  let P (j : ℕ) (v : Fin 27) := N v ∩ D j
  let σ (v : Fin 27) := ∑ w∈N v,G.degree w
  let b := (D 5).card
  have rem (v) : A v+σ v≤80 := by simpa only [edges] using removed G tri v
  have no (v) (low : G.degree v=5) : 52≤A v := by
    have bd := five v low
    have ne : A v≠51 := fun e => seed ⟨v,low,e⟩
    omega
  have point (v) : σ v+6+(if G.degree v=5 then 1 else 0)≤7*G.degree v := by
    have h := rem v
    have min := lo v
    have max := hi v
    by_cases a : G.degree v=5
    · have := no v a
      simp [a]
      omega
    by_cases c : G.degree v=6
    · have := six v c
      simp [c]
      omega
    have d : G.degree v=7 := by omega
    have := seven v d
    simp [d]
    omega
  have identity (v) : G.degree v^2+42=13*G.degree v+2*(if G.degree v=5 then 1 else 0) := by
    have min := lo v
    have max := hi v
    have cases : G.degree v=5 ∨ G.degree v=6 ∨ G.degree v=7 := by omega
    rcases cases with e|e|e <;> simp [e]
  have weighted := Finset.sum_le_sum (s:=(univ : Finset (Fin 27))) (fun v _ => point v)
  have moments := Finset.sum_congr (s₁:=(univ : Finset (Fin 27))) rfl (fun v _ => identity v)
  have total : ∑ v,G.degree v=160 := by rw [G.sum_degrees_eq_twice_card_edges,edges]
  have indic : (∑ v : Fin 27,if G.degree v=5 then 1 else 0)=b :=
    Finset.sum_boole (R:=ℕ) _ _
  simp only [σ,N,Finset.sum_add_distrib,←Finset.mul_sum,sum_neighbor_degrees,total,indic,sum_const,
    card_univ,Fintype.card_fin,nsmul_eq_mul] at weighted moments
  have small : b≤4 := by omega
  have count (j : ℕ) (v) : (∑ w∈N v,if G.degree w=j then 1 else 0)=(P j v).card := by
    have eq : (N v).filter (fun w => G.degree w=j)=P j v := by
      ext w
      simp [P,D]
    exact (Finset.sum_boole (R:=ℕ) _ _).trans (congrArg Finset.card eq)
  have local_id (v) : σ v+(P 5 v).card=6*G.degree v+(P 7 v).card := by
    have per (w : Fin 27) : G.degree w+(if G.degree w=5 then 1 else 0)=6+(if G.degree w=7 then 1 else 0) := by
      have min := lo w
      have max := hi w
      split <;> split <;> omega
    have h := Finset.sum_congr (s₁:=N v) rfl (fun w _ => per w)
    simp only [Finset.sum_add_distrib,sum_const,nsmul_eq_mul,count] at h
    simpa only [σ,N,G.card_neighborFinset_eq_degree,Nat.cast_id,Nat.mul_comm 6] using h
  have two (v) (low : v∈D 5) : 2≤(P 5 v).card := by
    have deg := (mem_filter.mp low).2
    have a := no v deg
    have e := rem v
    have h := local_id v
    omega
  have pairwise (v w : Fin 27) (adj : G.Adj v w) : Disjoint (P 5 v) (P 5 w) := by
    apply Finset.disjoint_left.mpr
    intro z hv hw
    have vz : G.Adj v z := (G.mem_neighborFinset ..).mp (mem_inter.mp hv).1
    have wz : G.Adj w z := (G.mem_neighborFinset ..).mp (mem_inter.mp hw).1
    exact G.isIndepSet_neighborSet_of_triangleFree tri z vz.symm wz.symm adj.ne adj
  have bounded (v) (low : v∈D 5) : (P 5 v).card+2≤b := by
    obtain ⟨w,hw⟩ := Finset.card_pos.mp (by have := two v low; omega : 0<(P 5 v).card)
    have lowW := (mem_inter.mp hw).2
    have dis := pairwise v w ((G.mem_neighborFinset ..).mp (mem_inter.mp hw).1)
    have bound : (P 5 v ∪ P 5 w).card≤b := card_le_card (union_subset inter_subset_right inter_subset_right)
    rw [card_union_of_disjoint dis] at bound
    have := two w lowW
    omega
  have existsLow : (D 5).Nonempty := by
    by_contra! empty
    have lower (v : Fin 27) : 6≤G.degree v := by
      have h := lo v
      have neg : G.degree v≠5 := fun e => by
        have hmem : v∈D 5 := mem_filter.mpr ⟨mem_univ _,e⟩
        simp [empty] at hmem
      omega
    have all := Finset.sum_le_sum (s:=(univ : Finset (Fin 27))) (fun v _ => lower v)
    simp [total] at all
  obtain ⟨v,hv⟩ := existsLow
  have lower := two v hv
  have upper := bounded v hv
  refine ⟨by omega,?_⟩
  intro x hx
  have l := two x hx
  have u := bounded x hx
  have d := (mem_filter.mp hx).2
  have a := no x d
  have e := rem x
  have h := local_id x
  change (P 5 x).card=2 ∧ (P 7 x).card=0 ∧ A x=52
  omega

end RamseyDeficiency

namespace RamseyDeficiency
open Finset SimpleGraph

/-- In a four-vertex set inducing a 2-regular graph, every vertex has an
opposite vertex sharing its two neighbors in the set. -/
theorem opposite_vertex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Finset (Fin n)) (size : D.card=4)
    (two : ∀ v∈D, (G.neighborFinset v ∩ D).card=2)
    (v : Fin n) (hv : v∈D) :
    ∃ w ∈ D, w ∈ Gᶜ.neighborFinset v ∧
      (G.neighborFinset w ∩ D) = (G.neighborFinset v ∩ D) := by
  classical
  let N := fun x => G.neighborFinset x ∩ D
  have hN (x) : N x ⊆ D := inter_subset_right
  have self (x) : x∉N x := by simp [N]
  have sub : insert v (N v) ⊆ D := insert_subset hv (hN _)
  have cardRest : (D \ insert v (N v)).card = 1 := by
    rw [card_sdiff_of_subset sub,card_insert_of_notMem (self _),size]
    rw [show (N v).card=2 from two v hv]
  obtain ⟨w,hw⟩ := card_pos.mp (by omega : 0 < (D \ insert v (N v)).card)
  obtain ⟨hw,notmem⟩ := mem_sdiff.mp hw
  have ne : w≠v := fun e => notmem (mem_insert.mpr (Or.inl e))
  have noadj : ¬ G.Adj v w := fun adj => notmem (mem_insert.mpr (.inr
      (mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr adj,hw⟩)))
  refine ⟨w,hw,(Gᶜ.mem_neighborFinset ..).mpr ⟨ne.symm,noadj⟩,?_⟩
  let rest := D \ ({v,w} : Finset (Fin n))
  have both : ({v,w} : Finset (Fin n)) ⊆ D := insert_subset hv (singleton_subset_iff.mpr hw)
  have count : rest.card=2 := by simp [rest,card_sdiff_of_subset both,ne.symm,size]
  have eq (x) (hx : x∈D) (miss : ∀ z∈N x, z≠v ∧ z≠w) : N x=rest := by
    apply eq_of_subset_of_card_le _ (by rw [count,show (N x).card=2 from two x hx])
    intro z hz
    exact mem_sdiff.mpr ⟨hN _ hz,by simpa using miss z hz⟩
  have hV : N v=rest := eq v hv fun z hz => by
    have adj := (G.mem_neighborFinset ..).mp (mem_inter.mp hz).1
    exact ⟨adj.ne.symm,fun e => noadj (e ▸ adj)⟩
  have hW : N w=rest := eq w hw fun z hz => by
    have adj := (G.mem_neighborFinset ..).mp (mem_inter.mp hz).1
    exact ⟨fun e => noadj (e ▸ adj.symm), adj.ne.symm⟩
  exact hW.trans hV.symm

/-- The 52-edge alternative has a degree-five vertex outside the root and its
neighbors that loses at least two neighbors on passing to the antineighborhood. -/
theorem seed_51_or_52_low (G : SimpleGraph (Fin 27)) [DecidableRel G.Adj]
    (tri : G.CliqueFree 3) (edges : G.edgeFinset.card=80)
    (lo : ∀ u,5≤G.degree u) (hi : ∀ u,G.degree u≤7) :
    let H (v : Fin 27) := G.induce (Gᶜ.neighborFinset v : Set (Fin 27))
    (∀ v,G.degree v=5 → 51≤(H v).edgeFinset.card) →
    (∀ v,G.degree v=6 → 44≤(H v).edgeFinset.card) →
    (∀ v,G.degree v=7 → 37≤(H v).edgeFinset.card) →
    ∃ v, G.degree v=5 ∧ ((H v).edgeFinset.card=51 ∨
      ((H v).edgeFinset.card=52 ∧ ∃ w, (H v).degree w≤3)) := by
  intro H five six seven
  classical
  rcases extreme_seed_or_four G tri edges lo hi five six seven with first|⟨size,four⟩
  · obtain ⟨v,hv,seed⟩ := first
    exact ⟨v,hv,Or.inl seed⟩
  let D := univ.filter (fun x : Fin 27 => G.degree x=5)
  change D.card=4 at size
  obtain ⟨v,hv⟩ := card_pos.mp (by omega : 0<D.card)
  have two (x) (hx : x∈D) := (four x hx).1
  obtain ⟨w,hw,anti,equal⟩ := opposite_vertex G D size two v hv
  refine ⟨v,(mem_filter.mp hv).2,Or.inr ⟨(four v hv).2.2,⟨⟨w,anti⟩,?_⟩⟩⟩
  let B := Gᶜ.neighborFinset v
  let x : (B : Set (Fin 27)) := ⟨w,anti⟩
  have card : (H v).degree x=(G.neighborFinset w ∩ B).card := by
    have h := congrArg Finset.card (G.map_neighborFinset_induce (s:=(B : Set (Fin 27))) x)
    simp only [Finset.card_map,Finset.toFinset_coe,SimpleGraph.card_neighborFinset_eq_degree] at h
    convert h using 1
    congr 1
    exact Subsingleton.elim _ _
  have dis : Disjoint (G.neighborFinset w ∩ B) (G.neighborFinset w ∩ D) := by
    rw [equal]
    apply Finset.disjoint_left.mpr
    intro z hz nz
    exact ((Gᶜ.mem_neighborFinset ..).mp (mem_inter.mp hz).2).2
      ((G.mem_neighborFinset ..).mp (mem_inter.mp nz).1)
  have bound := card_le_card (union_subset (inter_subset_left (s₂:=B))
      (inter_subset_left (s₁:=G.neighborFinset w) (s₂:=D)))
  rw [card_union_of_disjoint dis,two w hw,G.card_neighborFinset_eq_degree,(mem_filter.mp hw).2] at bound
  change (H v).degree x ≤ 3
  omega

end RamseyDeficiency

namespace Ramsey39
open SimpleGraph Finset
open scoped Classical

theorem focused21 (G : SimpleGraph (Fin 27)) [DecidableRel G.Adj] (tri : G.CliqueFree 3)
    (ind : Gᶜ.CliqueFree 8) (min : ∀ v,4≤G.degree v) (edges : G.edgeFinset.card≤80)
    (bound : ∀ (n : ℕ),19≤n→n≤22→∀ (D : SimpleGraph (Fin n)) [DecidableRel D.Adj],
      D.CliqueFree 3 → Dᶜ.CliqueFree 7 → (if n=22 then 59 else if n=21 then 51 else if n=20 then 44 else 37)≤D.edgeFinset.card) :
    ∃ v : Fin 27, let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let K := G.induce (B : Set (Fin 27))
    let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
    Fintype.card B=21 ∧ Fintype.card N=5 ∧ K.CliqueFree 3 ∧ Kᶜ.CliqueFree 7 ∧
    (K.edgeFinset.card=51 ∨ (K.edgeFinset.card=52 ∧ ∃ w,K.degree w≤3)) ∧
    (∀ i,4≤(A i).card ∧ (A i).card≤6 ∧ Kᶜ.IsClique (A i)) ∧
    K.edgeFinset.card+5+(∑ i,(A i).card)=80 ∧
    ∀ S : Finset B,Kᶜ.IsClique S →
      ((univ : Finset N).filter (fun i => Disjoint (A i) S)).card+S.card≤7 := by
  classical
  obtain ⟨_,range,nb,_⟩ := profile G tri ind min edges bound
  let H (w : Fin 27) := G.induce ((Gᶜ.neighborFinset w : Finset (Fin 27)) : Set (Fin 27))
  have lower (w : Fin 27) :
      (if G.degree w=5 then 51 else if G.degree w=6 then 44 else 37)≤(H w).edgeFinset.card := by
    let n := Gᶜ.degree w
    have h := G.degree_compl w
    rw [Fintype.card_fin] at h
    have r := range w
    obtain ⟨D,dD,tD,iD,sub⟩ := RamseyDeficiency.extract_anti G tri ind w (m:=n) le_rfl
    let := dD
    have lo := bound n (by dsimp [n]; omega) (by dsimp [n]; omega) D tD iD
    change D.edgeFinset.card≤(H w).edgeFinset.card at sub
    apply le_trans _ sub
    dsimp [n] at lo
    split_ifs at lo ⊢ <;> omega
  obtain ⟨v,dv,seed⟩ := RamseyDeficiency.seed_51_or_52_low G tri nb
    (fun w => (range w).1) (fun w => (range w).2)
    (fun w dw => by simpa [dw] using lower w)
    (fun w dw => by simpa [dw] using lower w)
    (fun w dw => by simpa [dw] using lower w)
  refine ⟨v,?_⟩
  intro N B K A
  obtain ⟨t,i,rows,covers,_⟩ := neighborhood_data G v tri ind
  have cN : Fintype.card N=5 := (Fintype.card_coe _).trans dv
  have cB : Fintype.card B=21 := by
    rw [Fintype.card_coe]
    change Gᶜ.degree v=21
    rw [G.degree_compl,Fintype.card_fin,dv]
  have rem := RamseyDeficiency.removed_eq G tri v
  change K.edgeFinset.card+(∑ w∈N,G.degree w)=G.edgeFinset.card at rem
  have each (w : N) : (A w).card+1=G.degree w.val := RamseyDeficiency.row_card G tri v w
  refine ⟨cB,cN,t,i,seed,?_,?_,?_⟩
  · intro w
    have d := range w.val
    have h := each w
    exact ⟨by omega,by omega,rows w⟩
  · have total := Finset.sum_congr (s₁:=univ) (s₂:=univ) rfl (fun w _ => each w)
    rw [Finset.sum_add_distrib,Finset.sum_const,card_univ,cN] at total
    simp only [nsmul_eq_mul,Nat.mul_one] at total
    rw [←Finset.sum_coe_sort N (fun w => G.degree w)] at rem
    omega
  · intro S cl
    exact covers _ S cl (fun w hw => (Finset.mem_filter.mp hw).2)

end Ramsey39

namespace Ramsey39
open SimpleGraph Finset

/-- Relabel the five deleted neighbors by Fin 5, preserving both row counts. -/
theorem five_rows {V W : Type} [Fintype W] [DecidableEq W] [DecidableEq V]
    (G : SimpleGraph V) (five : Fintype.card W = 5) (A : W → Finset V)
    (rows : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6 ∧ Gᶜ.IsClique (A i))
    (total : (∑ i, (A i).card) = 24)
    (avoid : ∀ S : Finset V, Gᶜ.IsClique S →
      ((univ : Finset W).filter fun i => Disjoint (A i) S).card + S.card ≤ 7) :
    ∃ F : Fin 5 → Finset V,
      (∀ i, 4 ≤ (F i).card ∧ (F i).card ≤ 6 ∧ Gᶜ.IsClique (F i)) ∧
      (∑ i, (F i).card) = 24 ∧
      ∀ S : Finset V, Gᶜ.IsClique S →
        ((univ : Finset (Fin 5)).filter fun i => Disjoint (F i) S).card + S.card ≤ 7 := by
  classical
  let e := (Fintype.equivFinOfCardEq five).symm
  refine ⟨fun i => A (e i), fun i => rows (e i), (e.sum_comp (fun i => (A i).card)).trans total, ?_⟩
  intro S hs
  have cards : ((univ : Finset (Fin 5)).filter fun i => Disjoint (A (e i)) S).card =
      ((univ : Finset W).filter fun i => Disjoint (A i) S).card := by
    apply Finset.card_bij (fun i _ => e i)
    · simp
    · exact fun _ _ _ _ eq => e.injective eq
    · intro j hj
      exact ⟨e.symm j, by simpa using hj, e.apply_symm_apply j⟩
  rw [cards]
  exact avoid S hs
end Ramsey39

namespace GlueSeed
open Finset

/- Weighted independent six-sets rule out gluing five independent rows of
size 4–6 and total size 24 to any of the four listed Ramsey(3,7;21,51)
representatives. The labels use the House of Graphs graph6 ordering. -/
set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
theorem four_no_five (A : List Nat) (known : A ∈ [
    [0x380a8,0x140a8,0x3081,0x4480,0x4190,0x8c4,0x10a8,0x2a8,0x444,0x91,0x4,0x11,0x4,0x1,0x3,0x0,0x8,0x4,0x2,0x1,0x0],
    [0x380a8,0x100a8,0xb081,0x2480,0x4190,0x4c4,0x10a8,0x1a8,0x444,0x51,0x44,0x1,0x4,0x1,0x1,0x2,0x8,0x4,0x2,0x1,0x0],
    [0x380a8,0xc0a8,0x3081,0x2480,0x4190,0x10c4,0x10a8,0x4a8,0x444,0x111,0x44,0x11,0x4,0x1,0x1,0x0,0x8,0x4,0x2,0x1,0x0],
    [0x380a8,0x40a8,0x7081,0x4480,0x4190,0x8c4,0x10a8,0x2a8,0x444,0x11,0x84,0x1,0x4,0x5,0x1,0x4,0x8,0x4,0x2,0x1,0x0]]) :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ R K : Fin 5 → Nat, (∀ i, (R i,K i)∈enum A) →
      (∀ i, 4≤K i ∧ K i≤6) → (∑ i,K i)=24 →
      (∀ s, (s,6)∈enum A → ∀ i j, R i &&& s=0 → R j &&& s=0 → i=j) → False := by
  intro enum R K rows sizes sum pair
  let mem : List Nat → Nat → Nat → Bool := List.foldr
    (fun a next r k => if r%2=0 then next (r/2) k else
       decide (0<k) && (a &&& (r/2) == 0) && next (r/2) (k-1))
    (fun r k => r==0 && k==0)
  let missed (tests : List (Nat×Nat)) (r : Nat) :=
    tests.foldr (fun t acc => (if r &&& t.1 == 0 then t.2 else 0)+acc) 0
  have mem_ok {as : List Nat} {r k : Nat} (h : mem as r k=true) : (r,k)∈enum as := by
    induction as generalizing r k with
    | nil => simpa [mem,enum] using h
    | cons a as ih =>
      change (if r%2=0 then mem as (r/2) k else decide (0<k) && (a &&& (r/2) == 0) && mem as (r/2) (k-1))=true at h
      by_cases ev : r%2=0
      · rw [if_pos ev] at h
        exact List.mem_append_left _ (List.mem_map.mpr ⟨_,ih h,by congr 1; omega⟩)
      · simp only [if_neg ev,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨ih h.2,by simpa using h.1.2⟩,by congr 1 <;> omega⟩
  let valid (adj : List Nat) (tests : List (Nat×Nat)) (a b : Nat) :=
    tests.all (fun t => mem adj t.1 6) &&
      (enum adj).all (fun p => if 4≤p.2 ∧ p.2≤6 then decide (a ≤ missed tests p.1+b*p.2) else true)
  have cert : ∃ (tests : List (Nat×Nat)) (a b : Nat),
      valid A tests a b=true ∧ (tests.map Prod.snd).sum+b*24<5*a := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at known
    rcases known with rfl|rfl|rfl|rfl
    · refine ⟨[(0x104807,2),(0x105007,1),(0x10840b,1),(0x10300b,1),(0x8a00b,1),(0x10a00b,1),(0x85403,2),(0x8a803,1),(0x1002a5,1),(0x104825,1),(0x105085,1),(0x82a05,1),(0x83205,2),(0x1002a9,3),(0x83209,1),(0x844a1,1),(0x1044a1,2),(0x88a21,2),(0x108a21,1),(0x84c21,1),(0x88c21,1),(0x85481,1),(0x8aa01,1),(0x10aa01,1),(0x100156,1),(0x22846,1),(0x25106,2),(0x10015a,3),(0x2310a,1),(0x28852,1),(0x24512,1),(0x24c12,2),(0x28c12,1),(0x2a842,1),(0x25502,1),(0xaa802,1),(0x44834,2),(0x44194,1),(0x1002e4,1),(0x1003c4,1),(0x102344,1),(0x42a44,3),(0x45184,1),(0x105184,1),(0x65104,1),(0xe4804,1),(0x100f8,1),(0x18438,2),(0x101d8,1),(0x12348,1),(0x1a248,2),(0x11388,2),(0x11588,2),(0x31508,1),(0x33108,2),(0x9a208,1),(0xb1408,1),(0xb8408,1),(0x500f0,1),(0x108870,2),(0x444b0,2),(0x70150,2),(0x78050,1),(0x104590,1),(0x78410,1),(0x502e0,2),(0xd02a0,1),(0xd8220,1),(0x72140,1),(0x51380,1),(0xd1280,1),(0xe4c00,1),(0xf1400,1),(0xf8400,1),(0xf3000,2)],44,5,?_,by decide⟩
      dsimp +zetaDelta only
      decide +kernel
    · refine ⟨[(0x104807,1),(0x103007,2),(0x85007,1),(0x105007,1),(0x10840b,1),(0x85403,1),(0x8a803,1),(0x10a803,1),(0x1002a5,2),(0x1040a5,1),(0x84825,1),(0x83205,2),(0x108229,1),(0x88429,1),(0x108429,2),(0x101489,1),(0x8a209,2),(0x10a209,1),(0x844a1,1),(0x88a21,1),(0x88c21,1),(0x85481,2),(0x100156,2),(0x1805a,1),(0x1150a,1),(0x1310a,2),(0x14512,2),(0x18c12,1),(0x34812,1),(0x1a842,1),(0x15502,1),(0x33102,2),(0x9a802,1),(0x200f4,1),(0x20874,1),(0x24834,2),(0x1001d4,1),(0x20a64,1),(0x22344,1),(0x102344,1),(0x22a44,1),(0x21384,1),(0x25184,2),(0x23304,1),(0xa3204,1),(0x1001d8,1),(0x100598,1),(0x58418,2),(0x4a248,1),(0x10a248,1),(0x5a048,1),(0x41388,1),(0x101388,1),(0x51508,1),(0xd8408,1),(0x108870,2),(0x444b0,2),(0x70150,2),(0x58850,1),(0x104590,1),(0x74110,1),(0x602e0,2),(0x48a60,1),(0xe02a0,2),(0xda800,1),(0xf4800,1),(0xf3000,1),(0xf5000,1)],37,4,?_,by decide⟩
      dsimp +zetaDelta only
      decide +kernel
    · refine ⟨[(0x102807,1),(0x84807,1),(0x104807,2),(0x103007,1),(0x105007,1),(0x10140b,2),(0x10840b,2),(0x8a00b,1),(0x85403,2),(0x8a803,1),(0x1002a5,1),(0x101285,1),(0x82a05,1),(0x102a05,1),(0x83205,2),(0x1002a9,2),(0x88429,1),(0x101489,1),(0x83209,1),(0x8a209,1),(0x10a209,1),(0x844a1,1),(0x1044a1,1),(0x88a21,2),(0x108a21,1),(0x84c21,1),(0x104c21,1),(0x88c21,2),(0x85481,1),(0x10aa01,1),(0x100156,2),(0x43106,1),(0x10015a,1),(0x10214a,1),(0x4310a,2),(0x48852,2),(0x108852,1),(0x44512,1),(0x44c12,2),(0x48c12,1),(0x4a842,2),(0x45502,1),(0xca802,1),(0x240b4,1),(0x24834,2),(0x1001d4,1),(0x64814,1),(0x202e4,1),(0x1003c4,1),(0x22344,1),(0x22a44,2),(0x62844,1),(0x25184,3),(0x65104,1),(0xe4804,2),(0x18078,1),(0x18438,2),(0x1001d8,1),(0x58418,1),(0x1003c8,1),(0x52148,1),(0x1a248,3),(0x11388,1),(0x11588,2),(0x51508,1),(0xd8408,1),(0x28870,2),(0x108870,1),(0x144b0,2),(0x340b0,1),(0x301d0,1),(0x70150,2),(0x78050,1),(0x104590,1),(0x74110,1),(0x302e0,2),(0xb02a0,1),(0xb40a0,1),(0xb8220,1),(0xb1280,1),(0x33300,1),(0xd5400,1),(0xea800,1),(0xf3000,1),(0xf5000,2),(0xfa000,1)],47,5,?_,by decide⟩
      dsimp +zetaDelta only
      decide +kernel
    · refine ⟨[(0x103007,1),(0x10a00b,1),(0x85403,1),(0x8a803,1),(0x10a803,1),(0x1002a5,1),(0x1040a5,1),(0x84825,1),(0x83205,1),(0x108429,1),(0x101489,1),(0x8a209,1),(0x10a209,1),(0x88c21,1),(0x85481,1),(0x8aa01,1),(0x44816,1),(0x102146,1),(0x2310a,1),(0x24512,1),(0x104512,1),(0x28c12,1),(0x2a842,1),(0x63102,1),(0x44834,1),(0x1001d4,1),(0x42344,1),(0x42a44,1),(0x45184,2),(0x1001d8,1),(0x38418,1),(0x18268,1),(0x2a248,1),(0x11388,1),(0x11588,1),(0xb8408,1),(0x18870,1),(0x108870,1),(0x144b0,2),(0x70150,2),(0x502e0,1),(0xd02a0,1),(0xe3200,1),(0xf4800,1),(0xf5000,1)],20,2,?_,by decide⟩
      dsimp +zetaDelta only
      decide +kernel

  obtain ⟨tests,a,b,pass,heavy⟩ := cert
  simp only [valid,Bool.and_eq_true] at pass
  have pack (ts : List (Nat×Nat)) (good : ∀ t ∈ ts, (t.1,6)∈enum A) :
      (∑ i, missed ts (R i))≤(ts.map Prod.snd).sum := by
    induction ts with
    | nil => simp [missed]
    | cons t ts ih =>
      obtain ⟨s,w⟩ := t
      have tail := ih (fun t ht => good t (List.mem_cons_of_mem _ ht))
      have one : (∑ i : Fin 5, (if R i &&& s=0 then w else 0))≤w := by
        by_cases h : ∃ i, R i &&& s=0
        · obtain ⟨j,hj⟩ := h
          rw [Finset.sum_eq_single j]
          · simp [hj]
          · intro i _ ne
            have hi : R i &&& s≠0 := fun eq => ne (pair s (good (s,w) List.mem_cons_self) i j eq hj)
            simp [hi]
          · simp
        · push Not at h
          simp [h]
      simpa [missed,Finset.sum_add_distrib] using Nat.add_le_add one tail
  have lower (i : Fin 5) : a ≤ missed tests (R i)+b*(K i) := by
    have h := List.all_eq_true.mp pass.2 _ (rows i)
    simpa only [sizes i,and_self,if_true,decide_eq_true_eq] using h
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => lower i)
  rw [Finset.sum_add_distrib,← Finset.mul_sum,sum] at total
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at total
  have cap := pack tests (fun t ht => mem_ok (List.all_eq_true.mp pass.1 t ht))
  omega

end GlueSeed

namespace GlueSeed
open SimpleGraph Finset

theorem graph_rows {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) (nodup : vs.Nodup)
    (full : ∀ x : V, x∈vs) (A : Fin 5 → Finset V)
    (rows : ∀ i, 4≤(A i).card ∧ (A i).card≤6 ∧ Gᶜ.IsClique (A i : Set V))
    (total : (∑ i,(A i).card)=24)
    (obstruction : ∀ S : Finset V, Gᶜ.IsClique (S : Set V) →
      (univ.filter fun i => Disjoint (A i) S).card+S.card≤7) :
    let bits := fun bs : List Bool => bs.foldr (fun b k => 2*k+b.toNat) 0
    let enc := fun (ws : List V) => (ws.foldr (fun v (p : List V × List ℕ) =>
      (v::p.1, bits (p.1.map fun x => decide (G.Adj v x)) :: p.2)) ([],[])).2
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∃ R K : Fin 5 → Nat, (∀ i, (R i,K i)∈enum (enc vs)) ∧
      (∀ i, 4≤K i ∧ K i≤6) ∧ (∑ i,K i)=24 ∧
      (∀ s, (s,6)∈enum (enc vs) → ∀ i j, R i &&& s=0 → R j &&& s=0 → i=j) := by
  intro bits enc enum
  let mark (ws : List V) (S : Finset V) := bits (ws.map fun x => decide (x∈S))
  let ind0 (p : Nat × Nat) := (2*p.1,p.2)
  let ind1 (p : Nat × Nat) := (2*p.1+1,p.2+1)
  have enum_nil : enum [] = [(0,0)] := rfl
  have enum_cons (m : ℕ) (b : List ℕ) : enum (m::b) =
      (enum b).map ind0 ++ ((enum b).filter fun p=>m &&& p.1 == 0).map ind1 := rfl
  have enc_nil : enc [] = [] := rfl
  let foldPair (ws : List V) : List V × List ℕ :=
    ws.foldr (fun v (p : List V × List ℕ) =>
      (v::p.1,bits (p.1.map fun x => decide (G.Adj v x))::p.2)) ([],[])
  have prefix_eq (ws : List V) : (foldPair ws).1 = ws := by
    induction ws with
    | nil => rfl
    | cons x ws ih => exact congrArg (x :: ·) ih
  have enc_cons (a : V) (ws : List V) :
      enc (a::ws) = bits (ws.map fun x => decide (G.Adj a x)) :: enc ws := by
    change bits ((foldPair ws).1.map fun x => decide (G.Adj a x)) :: (foldPair ws).2 = _
    rw [prefix_eq]
  have bits_nil : bits [] = 0 := rfl
  have bits_cons (a : Bool) (l : List Bool) : bits (a::l) = 2*bits l+a.toNat := rfl
  have bit_form (b : Bool) (n : Nat) : Nat.bit b n = 2*n+b.toNat := by
    cases b <;> simp [Nat.bit, Nat.two_mul]
  have and_bit (a : Bool) (x : ℕ) (b : Bool) (y : ℕ) :
      Nat.bit a x &&& Nat.bit b y = Nat.bit (a && b) (x &&& y) := by
    apply Nat.eq_of_testBit_eq
    intro i
    cases i with
    | zero => cases a <;> cases b <;> simp [Nat.testBit_zero,bit_form]
    | succ i =>
      have half (c : Bool) (t : ℕ) : Nat.bit c t / 2 = t := by
        cases c <;> simp [bit_form]
        omega
      rw [Nat.testBit_and,Nat.testBit_succ,Nat.testBit_succ,Nat.testBit_succ,half,half,half,Nat.testBit_and]
  have and_mask (vs : List V) (f g : V → Bool) :
      bits (vs.map f) &&& bits (vs.map g) = 0 ↔ ∀ x∈vs, f x = true → g x = false := by
    induction vs with
    | nil => simp [bits_nil]
    | cons a l ih =>
      simp only [List.map_cons, bits_cons, ← bit_form, and_bit, List.forall_mem_cons]
      rw [bit_form]
      cases f a <;> cases g a <;> simp [ih]
  have mark_congr (vs : List V) (s t : Finset V)
      (h : ∀ x∈vs, x∈s ↔ x∈t) : mark vs s = mark vs t := by
    dsimp only [mark]
    congr 1
    exact List.map_congr_left (fun x hx => by simp only [h x hx])
  have sound (vs : List V) (hn : vs.Nodup) {p : Nat × Nat} (hp : p ∈ enum (enc vs)) :
      ∃ S : Finset V, S ⊆ vs.toFinset ∧ Gᶜ.IsClique (S : Set V) ∧ p = (mark vs S,S.card) := by
    induction vs generalizing p with
    | nil =>
      simp [enc_nil,enum_nil] at hp
      exact ⟨∅,by simp,by simp,by simp [hp,mark,bits_nil]⟩
    | cons a l ih =>
      have hn' := List.nodup_cons.mp hn
      simp only [enc_cons,enum_cons,List.mem_append,List.mem_map,List.mem_filter] at hp
      rcases hp with ⟨q,hq,rfl⟩ | ⟨q,⟨hq,hd⟩,rfl⟩
      · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
        have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
        exact ⟨S,by simpa using hS.trans (Finset.subset_insert a _),hI,by simp [ind0,mark,bits_cons,ha]⟩
      · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
        have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
        have hz := (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈S))).mp (beq_iff_eq.mp hd)
        have hi : Gᶜ.IsClique (insert a S : Finset V) := by
          rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem ha]
          refine ⟨hI,fun x hx => ⟨?_,?_⟩⟩
          · exact fun e => ha (e ▸ hx)
          · intro adj
            have := hz x (List.mem_toFinset.mp (hS hx)) (by simpa using adj)
            exact (of_decide_eq_false this) hx
        have hm := mark_congr l (insert a S) S (by intro x hx; simp [show x ≠ a from fun e => hn'.1 (e ▸ hx)])
        refine ⟨insert a S, by simpa using Finset.insert_subset_insert a hS, hi, ?_⟩
        simp [ind1,mark,bits_cons,Finset.card_insert_of_notMem ha] at hm ⊢
        omega
  have complete (vs : List V) (hn : vs.Nodup) (S : Finset V)
      (hS : S ⊆ vs.toFinset) (hI : Gᶜ.IsClique (S : Set V)) :
      (mark vs S,S.card) ∈ enum (enc vs) := by
    induction vs generalizing S with
    | nil =>
      have e : S=∅ := Finset.subset_empty.mp (by simpa using hS)
      simp [e,enc_nil,enum_nil,mark,bits_nil]
    | cons a l ih =>
      have hn' := List.nodup_cons.mp hn
      simp only [enc_cons,enum_cons,List.mem_append,List.mem_map,List.mem_filter]
      by_cases ha : a ∈ S
      · let T := S.erase a
        have hT : T ⊆ l.toFinset := by
          intro x hx
          have m := Finset.mem_erase.mp hx
          have h := List.mem_cons.mp (List.mem_toFinset.mp (hS m.2))
          exact List.mem_toFinset.mpr (h.resolve_left m.1)
        have hI' := hI.subset (show (T : Set V) ⊆ (S : Set V) from Finset.erase_subset ..)
        have hmark := mark_congr l S T (by intro x hx; simp [T,show x≠a from fun e => hn'.1 (e ▸ hx)])
        have hcard : T.card + 1 = S.card := Finset.card_erase_add_one ha
        right
        refine ⟨(mark l T,T.card),⟨ih hn'.2 T hT hI', ?_⟩,?_⟩
        · apply beq_iff_eq.mpr
          apply (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈T))).mpr
          intro x _ hx
          apply decide_eq_false
          intro hm
          have hmem := Finset.mem_erase.mp hm
          exact (hI ha hmem.2 hmem.1.symm).2 (of_decide_eq_true hx)
        · simp [ind1,mark,bits_cons,ha,hcard] at hmark ⊢
          omega
      · have hT : S ⊆ l.toFinset := by
          intro x hx
          have h := List.mem_cons.mp (List.mem_toFinset.mp (hS hx))
          exact List.mem_toFinset.mpr (h.resolve_left (fun e => ha (e ▸ hx)))
        exact Or.inl ⟨_,ih hn'.2 S hT hI,by simp [ind0,mark,bits_cons,ha]⟩
  have hPair : (∀ i,(mark vs (A i),(A i).card)∈enum (enc vs)) ∧
      (∀ mask, (mask,6)∈enum (enc vs) → ∀ i j : Fin 5,
        mark vs (A i) &&& mask=0 → mark vs (A j) &&& mask=0 → i=j) := by
    constructor
    · intro i
      exact complete vs nodup (A i) (fun x _ => List.mem_toFinset.mpr (full x)) (rows i).2.2
    · intro mask hm i j hi hj
      obtain ⟨S,_,cl,eq⟩ := sound vs nodup hm
      have value := congrArg Prod.fst eq
      have size := congrArg Prod.snd eq
      change mask=mark vs S at value
      change 6=S.card at size
      subst mask
      have dis (k : Fin 5) (none : mark vs (A k) &&& mark vs S=0) : Disjoint (A k) S := by
        apply Finset.disjoint_left.mpr
        intro x hx hy
        exact (of_decide_eq_false ((and_mask vs _ _).mp none x (full x) (by simpa using hx))) hy
      by_contra ne
      have many : 1 < (univ.filter fun k => Disjoint (A k) S).card :=
        Finset.one_lt_card.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,dis i hi⟩,
          j,mem_filter.mpr ⟨mem_univ _,dis j hj⟩,ne⟩
      have := obstruction S cl
      omega
  exact ⟨fun i => mark vs (A i), fun i => (A i).card, hPair.1,
    fun i => ⟨(rows i).1,(rows i).2.1⟩,total,hPair.2⟩

end GlueSeed

namespace GlueSeed
open SimpleGraph Finset

theorem graph_four_no_five {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) (nodup : vs.Nodup)
    (full : ∀ x : V, x∈vs) (A : Fin 5 → Finset V)
    (rows : ∀ i, 4≤(A i).card ∧ (A i).card≤6 ∧ Gᶜ.IsClique (A i : Set V))
    (total : (∑ i,(A i).card)=24)
    (obstruction : ∀ S : Finset V, Gᶜ.IsClique (S : Set V) →
      (univ.filter fun i => Disjoint (A i) S).card+S.card≤7) :
    let bits := fun bs : List Bool => bs.foldr (fun b k => 2*k+b.toNat) 0
    let enc := fun (ws : List V) => (ws.foldr (fun v (p : List V × List ℕ) =>
      (v::p.1, bits (p.1.map fun x => decide (G.Adj v x)) :: p.2)) ([],[])).2
    enc vs ∈ [
    [0x380a8,0x140a8,0x3081,0x4480,0x4190,0x8c4,0x10a8,0x2a8,0x444,0x91,0x4,0x11,0x4,0x1,0x3,0x0,0x8,0x4,0x2,0x1,0x0],
    [0x380a8,0x100a8,0xb081,0x2480,0x4190,0x4c4,0x10a8,0x1a8,0x444,0x51,0x44,0x1,0x4,0x1,0x1,0x2,0x8,0x4,0x2,0x1,0x0],
    [0x380a8,0xc0a8,0x3081,0x2480,0x4190,0x10c4,0x10a8,0x4a8,0x444,0x111,0x44,0x11,0x4,0x1,0x1,0x0,0x8,0x4,0x2,0x1,0x0],
    [0x380a8,0x40a8,0x7081,0x4480,0x4190,0x8c4,0x10a8,0x2a8,0x444,0x11,0x84,0x1,0x4,0x5,0x1,0x4,0x8,0x4,0x2,0x1,0x0]] → False := by
  intro bits enc known
  obtain ⟨R,K,r,sz,tot,p⟩ := graph_rows G vs nodup full A rows total obstruction
  exact four_no_five (enc vs) known R K r sz tot p

end GlueSeed


namespace OMA.R_RamseyNumbers_ramsey_number_three_nine_R2
open SimpleGraph RamseyNumbers Finset

/-- Lower edge bounds at orders 19, 20, 21 and 22 for triangle-free graphs with independence number at most six. -/
def H1 : Prop :=
  ∀ (n : ℕ), 19 ≤ n → n ≤ 22 → ∀ (D : SimpleGraph (Fin n)) [DecidableRel D.Adj],
    D.CliqueFree 3 → Dᶜ.CliqueFree 7 →
    (if n=22 then 59 else if n=21 then 51 else if n=20 then 44 else 37) ≤ D.edgeFinset.card

/-- Every triangle-free graph of order 21 and size 51 with independence number at most six
has an ordering with one of the four published forward adjacency codes. The lowest bit in a row
represents the next vertex in the ordering. The codes follow the House of Graphs catalogue. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (D : SimpleGraph V) [DecidableRel D.Adj],
    Fintype.card V = 21 → D.CliqueFree 3 → Dᶜ.CliqueFree 7 → D.edgeFinset.card = 51 →
    let bits := fun bs : List Bool => bs.foldr (fun b k => 2*k+b.toNat) 0
    let enc := fun vs : List V => (vs.foldr (fun v (p : List V × List ℕ) =>
      (v::p.1, bits (p.1.map fun x => decide (D.Adj v x)) :: p.2)) ([],[])).2
    ∃ vs : List V, vs.Nodup ∧ (∀ x, x ∈ vs) ∧ enc vs ∈
      [[0x380a8,0x140a8,0x3081,0x4480,0x4190,0x8c4,0x10a8,0x2a8,0x444,0x91,0x4,0x11,0x4,0x1,0x3,0x0,0x8,0x4,0x2,0x1,0x0],
       [0x380a8,0x100a8,0xb081,0x2480,0x4190,0x4c4,0x10a8,0x1a8,0x444,0x51,0x44,0x1,0x4,0x1,0x1,0x2,0x8,0x4,0x2,0x1,0x0],
       [0x380a8,0xc0a8,0x3081,0x2480,0x4190,0x10c4,0x10a8,0x4a8,0x444,0x111,0x44,0x11,0x4,0x1,0x1,0x0,0x8,0x4,0x2,0x1,0x0],
       [0x380a8,0x40a8,0x7081,0x4480,0x4190,0x8c4,0x10a8,0x2a8,0x444,0x11,0x84,0x1,0x4,0x5,0x1,0x4,0x8,0x4,0x2,0x1,0x0]]

/-- A 52-edge graph on 21 vertices with the same Ramsey restrictions has minimum degree four or greater. -/
def H3 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (D : SimpleGraph V) [DecidableRel D.Adj],
    Fintype.card V = 21 → D.CliqueFree 3 → Dᶜ.CliqueFree 7 →
    D.edgeFinset.card = 52 → ∀ w, 4 ≤ D.degree w

theorem main : H1 → H2 → H3 → type_of% @RamseyNumbers.ramsey_number_three_nine := by
  classical
  intro h1 h2 h3
  have upper : IsGraphRamsey 36 3 9 := by
    rintro G ⟨tr,ind⟩
    obtain ⟨K,dec,tk,ik,ed⟩ := RamseyDeficiency.sparse_anti G tr ind
    let := dec
    have mn := RamseyDeficiency.min_four_of_small K tk ik ed h1
    obtain ⟨v,hv⟩ := Ramsey39.focused21 K tk ik mn ed h1
    let N := K.neighborFinset v
    let B := Kᶜ.neighborFinset v
    let D := K.induce (B : Set (Fin 27))
    let A := fun i : N => (univ : Finset B).filter fun x => K.Adj i.val x.val
    obtain ⟨bc,nc,td,id,ec,rows,total,avoid⟩ := hv
    change D.edgeFinset.card + 5 + (∑ i, (A i).card) = 80 at total
    change ∀ S : Finset B, Dᶜ.IsClique S → ((univ : Finset N).filter fun i => Disjoint (A i) S).card + S.card ≤ 7 at avoid
    change D.edgeFinset.card = 51 ∨ (D.edgeFinset.card = 52 ∧ ∃ w, D.degree w ≤ 3) at ec
    rcases ec with e51 | ⟨e52,w,low⟩
    · rw [e51] at total
      have rowSum : (∑ i : N, (A i).card) = 24 := by omega
      obtain ⟨vs,unique,full,member⟩ := h2 B D bc td id e51
      obtain ⟨F,hF,weight,obstruction⟩ := Ramsey39.five_rows D nc A rows rowSum avoid
      exact GlueSeed.graph_four_no_five D vs unique full F hF weight obstruction member
    · have high := h3 B D bc td id e52 w
      omega
  rw [classicalRamsey_eq_sInf]
  apply IsLeast.csInf_eq
  refine ⟨upper, ?_⟩
  intro n hn
  by_contra! hlt
  have mono : Monotone (fun m => IsGraphRamsey m 3 9) :=
    monotone_nat_of_le_succ fun m => IsGraphRamsey.succ m 3 9
  obtain ⟨G, ht, hi⟩ := OMA.Ramsey35.lower_witness
  exact mono (show n ≤ 35 by omega) hn G ⟨ht, hi⟩

end OMA.R_RamseyNumbers_ramsey_number_three_nine_R2
