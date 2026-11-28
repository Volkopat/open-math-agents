import FormalConjectures.Wikipedia.RamseyNumbers
import Mathlib

/-! Angeltveit and McKay, R(5,5) ≤ 46, https://arxiv.org/html/2409.15709.
We verify the neighborhood restrictions, the general excess identity (1.2)
and the numerical and weighted counting inequalities in Sections 4 and 5.
The edge ceilings, structural selection of a rare pointed pair, and
exclusion of its gluing are recorded as distinct inputs.

The displayed definition of C3 in Section 4 says 21 vertices. Sections
3.3 and 3.4 and the excess formula specify 22 vertices with 113 edges.
This file uses the 22-vertex case. -/

namespace OMA.Ramsey55

open SimpleGraph RamseyNumbers

/-- A clique in a neighborhood extends to a larger clique by adjoining its root. -/
theorem neighbor_cliqueFree {V : Type*} [DecidableEq V] (G : SimpleGraph V) (v : V) {k : ℕ}
    (h : G.CliqueFree (k + 1)) : (G.induce (G.neighborSet v)).CliqueFree k := by
  intro s hs
  let f : G.induce (G.neighborSet v) ↪g G := SimpleGraph.Embedding.induce _
  let e := f.toEmbedding
  have hs' : G.IsNClique k (s.map e) := by
    refine ⟨?_, (Finset.card_map _).trans hs.card_eq⟩
    intro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hb
    exact f.map_adj_iff.mpr (hs.isClique hx hy fun he => hab (congrArg e he))
  apply h _ (hs'.insert (a := v) ?_)
  intro a ha
  obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp ha
  exact x.property

theorem neighbor_compl_cliqueFree {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (v : V) {t : ℕ} (h : Gᶜ.CliqueFree t) :
    (G.induce (G.neighborSet v))ᶜ.CliqueFree t :=
  h.comap (SimpleGraph.Embedding.complEquiv
    (SimpleGraph.Embedding.induce (G := G) (G.neighborSet v))).isContained

theorem neighbor_ramsey45 {V : Type*} [DecidableEq V] (G : SimpleGraph V) (v : V)
    (hK : G.CliqueFree 5) (hI : Gᶜ.CliqueFree 5) :
    (G.induce (G.neighborSet v)).CliqueFree 4 ∧
      (G.induce (G.neighborSet v))ᶜ.CliqueFree 5 :=
  ⟨neighbor_cliqueFree G v hK, neighbor_compl_cliqueFree G v hI⟩

/-- Restricting any sufficiently large finite graph to a labeled subset permits use of a
Ramsey statement formulated on `Fin n`. -/
theorem card_lt_of_ramsey {V : Type*} [Fintype V] [DecidableEq V]
    {n k l : ℕ} (hR : IsGraphRamsey n k l) (G : SimpleGraph V)
    (hK : G.CliqueFree k) (hI : Gᶜ.CliqueFree l) : Fintype.card V < n := by
  by_contra! hc
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin n) (β := V) (by simpa using hc)
  let H := G.comap e
  let f : H ↪g G := SimpleGraph.Embedding.comap e G
  exact hR H ⟨hK.comap f.isContained,
    hI.comap (SimpleGraph.Embedding.complEquiv f).isContained⟩

theorem degree_le_twentyFour {V : Type*} [Fintype V] [DecidableEq V]
    (hR : IsGraphRamsey 25 4 5) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hK : G.CliqueFree 5) (hI : Gᶜ.CliqueFree 5) (v : V) : G.degree v ≤ 24 := by
  obtain ⟨hA, hB⟩ := neighbor_ramsey45 G v hK hI
  have h := card_lt_of_ramsey hR _ hA hB
  rw [card_neighborSet_eq_degree] at h
  omega

theorem degree_range_of_card46 {V : Type*} [Fintype V] [DecidableEq V]
    (hR : IsGraphRamsey 25 4 5) (G : SimpleGraph V) [DecidableRel G.Adj]
    (h46 : Fintype.card V = 46) (hK : G.CliqueFree 5)
    (hI : Gᶜ.CliqueFree 5) (v : V) : 21 ≤ G.degree v ∧ G.degree v ≤ 24 := by
  have hUpper := degree_le_twentyFour hR G hK hI v
  have hDual := degree_le_twentyFour hR Gᶜ hI (by simpa using hK) v
  rw [G.degree_compl, h46] at hDual
  omega

theorem degree_compl_range_of_card46 {V : Type*} [Fintype V] [DecidableEq V]
    (hR : IsGraphRamsey 25 4 5) (G : SimpleGraph V) [DecidableRel G.Adj]
    (h46 : Fintype.card V = 46) (hK : G.CliqueFree 5)
    (hI : Gᶜ.CliqueFree 5) (v : V) : 21 ≤ Gᶜ.degree v ∧ Gᶜ.degree v ≤ 24 :=
  degree_range_of_card46 hR Gᶜ h46 hI (by simpa using hK) v

theorem edge_bound_from_fin {V : Type*} [Fintype V] [DecidableEq V]
    {n k l m : ℕ}
    (hBound : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      H.CliqueFree k → Hᶜ.CliqueFree l → H.edgeFinset.card ≤ m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Fintype.card V = n) (hK : G.CliqueFree k) (hI : Gᶜ.CliqueFree l) :
    G.edgeFinset.card ≤ m := by
  let e : Fin n ≃ V := Fintype.equivOfCardEq (by simpa using hn.symm)
  let H := G.comap e
  let f : H ≃g G := SimpleGraph.Iso.comap e G
  have hA : H.CliqueFree k := hK.comap f.toEmbedding.isContained
  have hB : Hᶜ.CliqueFree l :=
    hI.comap (SimpleGraph.Embedding.complEquiv f.toEmbedding).isContained
  exact f.card_edgeFinset_eq ▸ hBound H hA hB

/-- The four edge ceilings from Section 3, applied after labeling the neighborhood. -/
theorem neighbor_edge_bound_from_fin {V : Type*} [Fintype V] [DecidableEq V]
    (hR : IsGraphRamsey 25 4 5)
    (hBound : ∀ n, 21 ≤ n → n ≤ 24 → ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      H.CliqueFree 4 → Hᶜ.CliqueFree 5 →
      H.edgeFinset.card ≤ if n = 21 then 107 else if n = 22 then 114 else if n = 23 then 122 else 132)
    (G : SimpleGraph V) [DecidableRel G.Adj] (h46 : Fintype.card V = 46)
    (hK : G.CliqueFree 5) (hI : Gᶜ.CliqueFree 5) (v : V) :
    (G.induce (G.neighborSet v)).edgeFinset.card ≤
      if G.degree v = 21 then 107 else if G.degree v = 22 then 114
      else if G.degree v = 23 then 122 else 132 := by
  obtain ⟨hLo, hHi⟩ := degree_range_of_card46 hR G h46 hK hI v
  obtain ⟨hA, hB⟩ := neighbor_ramsey45 G v hK hI
  exact edge_bound_from_fin (hBound (G.degree v) hLo hHi) _
    (card_neighborSet_eq_degree G v) hA hB

/-- Complements partition the edges of the complete graph. -/
theorem edge_card_add_compl {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card + Gᶜ.edgeFinset.card = (Fintype.card V).choose 2 := by
  have hDisj : Disjoint G.edgeFinset Gᶜ.edgeFinset :=
    SimpleGraph.disjoint_edgeFinset.mpr disjoint_compl_right
  have hTop : (G ⊔ Gᶜ).edgeFinset = (⊤ : SimpleGraph V).edgeFinset :=
    SimpleGraph.edgeFinset_inj.mpr sup_compl_eq_top
  calc
    _ = (G.edgeFinset ∪ Gᶜ.edgeFinset).card := (Finset.card_union_of_disjoint hDisj).symm
    _ = (G ⊔ Gᶜ).edgeFinset.card := by rw [SimpleGraph.edgeFinset_sup]
    _ = _ := by rw [hTop, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]

/-- The edge counts of the dual neighborhood and the corresponding neighborhood in the
complement sum to the number of pairs of nonneighbors. -/
theorem dual_neighbor_edge_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (G.induce (Gᶜ.neighborSet v)).edgeFinset.card +
      (Gᶜ.induce (Gᶜ.neighborSet v)).edgeFinset.card = (Gᶜ.degree v).choose 2 := by
  let s := Gᶜ.neighborSet v
  let H := G.induce s
  let K := Gᶜ.induce s
  let e : K ≃g Hᶜ := {
    toEquiv := Equiv.refl _
    map_rel_iff' := fun {a b} =>
      show (a ≠ b ∧ ¬G.Adj a.val b.val) ↔ (a.val ≠ b.val ∧ ¬G.Adj a.val b.val) from
        and_congr
          ⟨fun h he => h (Subtype.ext he), fun h he => h (congrArg Subtype.val he)⟩ Iff.rfl }
  change H.edgeFinset.card + K.edgeFinset.card = (Gᶜ.degree v).choose 2
  rw [e.card_edgeFinset_eq, edge_card_add_compl, card_neighborSet_eq_degree]

end OMA.Ramsey55

open Finset SimpleGraph
open scoped BigOperators

namespace Ramsey55Excess

private theorem twice_induced_edges {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Set V) [DecidablePred (· ∈ S)] :
    2 * ((G.induce S).edgeFinset.card : ℤ) =
      ∑ a : V, ∑ b : V, if a ∈ S ∧ b ∈ S ∧ G.Adj a b then (1 : ℤ) else 0 := by
  let A := (Finset.univ : Finset (S × S)).filter (fun z => (G.induce S).Adj z.1 z.2)
  let B := (Finset.univ : Finset (V × V)).filter (fun z => z.1 ∈ S ∧ z.2 ∈ S ∧ G.Adj z.1 z.2)
  have hcard : A.card = B.card := by
    refine Finset.card_bij' (fun z _ => (z.1.val, z.2.val))
      (fun z hz => (⟨z.1, (mem_filter.mp hz).2.1⟩, ⟨z.2, (mem_filter.mp hz).2.2.1⟩)) ?_ ?_ ?_ ?_
    · intro z hz
      exact mem_filter.mpr ⟨mem_univ _, z.1.property, z.2.property, (mem_filter.mp hz).2⟩
    · intro z hz
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hz).2.2.2⟩
    · intro z hz
      rfl
    · intro z hz
      rfl
  calc
    _ = (A.card : ℤ) := by exact_mod_cast (G.induce S).two_mul_card_edgeFinset
    _ = (B.card : ℤ) := by rw [hcard]
    _ = ∑ z : V × V, if z.1 ∈ S ∧ z.2 ∈ S ∧ G.Adj z.1 z.2 then (1 : ℤ) else 0 := by
      simp [B, Finset.sum_boole]
    _ = _ := by rw [← Finset.univ_product_univ, Finset.sum_product]

private theorem sum_adj_indicator {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a : V) :
    (∑ b : V, if G.Adj a b then (1 : ℤ) else 0) = (G.degree a : ℤ) := by
  simp [Finset.sum_boole, ← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]

private theorem center_indicator {V : Type} (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj] (v a b : V) :
    (if Gᶜ.Adj v a ∧ Gᶜ.Adj v b ∧ G.Adj a b then (1 : ℤ) else 0) -
        (if G.Adj v a ∧ G.Adj v b ∧ G.Adj a b then (1 : ℤ) else 0) =
      if G.Adj a b then 1 - (if G.Adj v a then 1 else 0) - (if G.Adj v b then 1 else 0) else 0 := by
  by_cases hab : G.Adj a b
  · by_cases ha : G.Adj v a
    · by_cases hb : G.Adj v b <;> norm_num [hab, ha, hb, SimpleGraph.compl_adj]
    · by_cases hb : G.Adj v b
      · norm_num [hab, ha, hb, SimpleGraph.compl_adj]
      · have hva : v ≠ a := fun h => hb (h.symm ▸ hab)
        have hvb : v ≠ b := fun h => ha (h.symm ▸ hab.symm)
        norm_num [hab, ha, hb, hva, hvb, SimpleGraph.compl_adj]
  · simp [hab]

private theorem sum_cycle_three {V R : Type} [Fintype V] [AddCommMonoid R] (p : V → V → V → R) :
    (∑ v : V, ∑ a : V, ∑ b : V, p v a b) = ∑ a : V, ∑ b : V, ∑ v : V, p v a b := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

theorem excess_twice_zero {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    let n : ℤ := Fintype.card V
    let d (v : V) : ℤ := G.degree v
    (Finset.univ.sum (fun v : V => 2 * ((G.induce (Gᶜ.neighborSet v)).edgeFinset.card : ℤ) -
      2 * ((G.induce (G.neighborSet v)).edgeFinset.card : ℤ) - d v * (n - 2 * d v))) = 0 := by
  intro n d
  have hPair (a b : V) :
      (∑ v : V, if G.Adj a b then
        1 - (if G.Adj v a then (1 : ℤ) else 0) - (if G.Adj v b then (1 : ℤ) else 0) else 0) =
      if G.Adj a b then n - d a - d b else 0 := by
    by_cases hab : G.Adj a b
    · simp only [hab, if_true, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
      simp_rw [G.adj_comm _ a, G.adj_comm _ b, sum_adj_indicator]
      rfl
    · simp [hab]
  have hCycles :
      (∑ v : V, (2 * ((G.induce (Gᶜ.neighborSet v)).edgeFinset.card : ℤ) -
        2 * ((G.induce (G.neighborSet v)).edgeFinset.card : ℤ))) =
      ∑ a : V, ∑ b : V, if G.Adj a b then n - d a - d b else 0 := by
    simp_rw [twice_induced_edges, SimpleGraph.mem_neighborSet, ← sum_sub_distrib,
      center_indicator]
    rw [sum_cycle_three]
    simp_rw [hPair]
  have hSplit (a b : V) :
      (if G.Adj a b then n - d a - d b else 0) =
        (if G.Adj a b then n - d a else 0) - (if G.Adj a b then d b else 0) := by
    by_cases h : G.Adj a b <;> simp [h]
  have hWeight (a : V) (r : ℤ) :
      (∑ b : V, if G.Adj a b then r else 0) = d a * r := by
    dsimp only [d]
    rw [← sum_adj_indicator G a, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by by_cases h : G.Adj a b <;> simp [h]
  rw [sum_sub_distrib, hCycles]
  suffices h :
      (∑ a : V, ∑ b : V, if G.Adj a b then n - d a - d b else 0) =
        ∑ a : V, d a * (n - 2 * d a) by
    rw [h]
    exact sub_self _
  simp_rw [hSplit, sum_sub_distrib, hWeight]
  have hRight :
      (∑ a : V, ∑ b : V, if G.Adj a b then d b else 0) = ∑ b : V, d b * d b := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by simpa only [G.adj_comm _ b] using hWeight b (d b)
  rw [hRight, ← sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

end Ramsey55Excess

namespace Ramsey55Excess

private theorem local_weight_bound (d e : ℕ) (hlo : 21 ≤ d) (hhi : d ≤ 24)
    (hcap : e ≤ if d = 21 then 107 else if d = 22 then 114 else if d = 23 then 122 else 132) :
    let b (d : ℕ) : ℤ := if d = 21 then 106 else if d = 22 then 112 else if d = 23 then 118 else 127
    let k (d e : ℕ) : ℕ :=
      if (d = 24 ∧ 127 ≤ e) ∨ (d = 23 ∧ 121 ≤ e) then 1
      else if (d = 23 ∧ e = 120) ∨ (d = 22 ∧ e = 114) then 2
      else if (d = 23 ∧ e = 119) ∨ (d = 22 ∧ e = 113) ∨ (d = 21 ∧ e = 107) then 3
      else 0
    let w (i : ℕ) : ℤ := if i = 1 then 5 else if i = 2 then 2 else if i = 3 then 1 else 0
    (e : ℤ) + (if d = 24 ∧ k d e ≠ 1 then 1 else 0) ≤ b d + w (k d e) := by
  dsimp only
  interval_cases d <;> simp at hcap ⊢ <;> split_ifs <;> omega

private theorem baseline_sum (d d' : ℕ) (hlo : 21 ≤ d) (hhi : d ≤ 24) (h' : d' = 45 - d) :
    let b (d : ℕ) : ℤ := if d = 21 then 106 else if d = 22 then 112 else if d = 23 then 118 else 127
    2 * ((d'.choose 2 : ℕ) : ℤ) - (d : ℤ) * (46 - 2 * (d : ℤ)) = 2 * (1 + b d + b d') := by
  subst d'
  interval_cases d <;> decide

/-- Equations (1.2) and (4) imply the weighted exceptional count of §5.
The three classes have weights 5, 2 and 1, respectively. -/
theorem weights_total (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj]
    (hDegree : ∀ v, 21 ≤ G.degree v ∧ G.degree v ≤ 24)
    (hDegreeCompl : ∀ v, 21 ≤ Gᶜ.degree v ∧ Gᶜ.degree v ≤ 24)
    (hCap : ∀ v, (G.induce (G.neighborSet v)).edgeFinset.card ≤
      if G.degree v = 21 then 107 else if G.degree v = 22 then 114
      else if G.degree v = 23 then 122 else 132)
    (hCapCompl : ∀ v, (Gᶜ.induce (Gᶜ.neighborSet v)).edgeFinset.card ≤
      if Gᶜ.degree v = 21 then 107 else if Gᶜ.degree v = 22 then 114
      else if Gᶜ.degree v = 23 then 122 else 132) :
    let k (d e : ℕ) : ℕ :=
      if (d = 24 ∧ 127 ≤ e) ∨ (d = 23 ∧ 121 ≤ e) then 1
      else if (d = 23 ∧ e = 120) ∨ (d = 22 ∧ e = 114) then 2
      else if (d = 23 ∧ e = 119) ∨ (d = 22 ∧ e = 113) ∨ (d = 21 ∧ e = 107) then 3
      else 0
    let w (i : ℕ) : ℤ := if i = 1 then 5 else if i = 2 then 2 else if i = 3 then 1 else 0
    let W (H : SimpleGraph (Fin 46)) [DecidableRel H.Adj] (v : Fin 46) : ℤ :=
      w (k (H.degree v) (H.induce (H.neighborSet v)).edgeFinset.card)
    let X (H : SimpleGraph (Fin 46)) [DecidableRel H.Adj] (v : Fin 46) : ℤ :=
      if H.degree v = 24 ∧
        k (H.degree v) (H.induce (H.neighborSet v)).edgeFinset.card ≠ 1 then 1 else 0
    46 + (∑ v : Fin 46, X G v) + (∑ v : Fin 46, X Gᶜ v) ≤
      (∑ v : Fin 46, W G v) + (∑ v : Fin 46, W Gᶜ v) := by
  intro k w W X
  let b (d : ℕ) : ℤ := if d = 21 then 106 else if d = 22 then 112 else if d = 23 then 118 else 127
  let E (v : Fin 46) : ℕ := (G.induce (G.neighborSet v)).edgeFinset.card
  let EC (v : Fin 46) : ℕ := (Gᶜ.induce (Gᶜ.neighborSet v)).edgeFinset.card
  have hEq (v : Fin 46) : Gᶜ.degree v = 45 - G.degree v := by
    rw [G.degree_compl, Fintype.card_fin]
  have hZero :
      (∑ v : Fin 46, (2 * (1 + b (G.degree v) + b (Gᶜ.degree v) - (E v : ℤ) - (EC v : ℤ)))) = 0 := by
    calc
      _ = ∑ v : Fin 46, (2 * ((G.induce (Gᶜ.neighborSet v)).edgeFinset.card : ℤ) -
        2 * (E v : ℤ) - (G.degree v : ℤ) * (46 - 2 * (G.degree v : ℤ))) := by
        apply Finset.sum_congr rfl
        intro v _
        have hc : ((G.induce (Gᶜ.neighborSet v)).edgeFinset.card : ℤ) + (EC v : ℤ) =
            (((Gᶜ.degree v).choose 2 : ℕ) : ℤ) := by
          exact_mod_cast OMA.Ramsey55.dual_neighbor_edge_sum G v
        have hbase := baseline_sum _ _ (hDegree v).1 (hDegree v).2 (hEq v)
        change 2 * (((Gᶜ.degree v).choose 2 : ℕ) : ℤ) -
          (G.degree v : ℤ) * (46 - 2 * (G.degree v : ℤ)) =
            2 * (1 + b (G.degree v) + b (Gᶜ.degree v)) at hbase
        linarith only [hc, hbase]
      _ = _ := by simpa only [Fintype.card_fin, Nat.cast_ofNat, E] using excess_twice_zero G
  have hLocal (v : Fin 46) :
      (2 : ℤ) * (1 + X G v + X Gᶜ v - W G v - W Gᶜ v) ≤
        2 * (1 + b (G.degree v) + b (Gᶜ.degree v) - (E v : ℤ) - (EC v : ℤ)) := by
    have h1 : (E v : ℤ) + X G v ≤ b (G.degree v) + W G v :=
      local_weight_bound _ _ (hDegree v).1 (hDegree v).2 (hCap v)
    have h2 : (EC v : ℤ) + X Gᶜ v ≤ b (Gᶜ.degree v) + W Gᶜ v :=
      local_weight_bound _ _ (hDegreeCompl v).1 (hDegreeCompl v).2 (hCapCompl v)
    linarith only [h1, h2]
  have hTotal : (∑ v : Fin 46, (2 * (1 + X G v + X Gᶜ v - W G v - W Gᶜ v))) ≤ 0 :=
    (Finset.sum_le_sum fun v _ => hLocal v).trans_eq hZero
  rw [← Finset.mul_sum] at hTotal
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, mul_one] at hTotal
  linarith only [hTotal]

end Ramsey55Excess

namespace OMA.R_RamseyNumbers_ramsey_number_five_five_upper_bound_R1

open Finset SimpleGraph RamseyNumbers
open scoped BigOperators

/-- The off-diagonal upper bound determines the allowable degrees. -/
def H1 : Prop := IsGraphRamsey 25 4 5

/-- The four edge ceilings for Ramsey (4,5) graphs from Section 3. -/
def H2 : Prop :=
  ∀ n : ℕ, 21 ≤ n → n ≤ 24 → ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    H.CliqueFree 4 → Hᶜ.CliqueFree 5 →
    H.edgeFinset.card ≤ if n = 21 then 107 else if n = 22 then 114 else if n = 23 then 122 else 132

/-- Proposition 5.3 selects one of five pointed configurations after the
degree, edge-ceiling and weighted excess inputs have been verified. -/
def H3 : Prop :=
  let k (d e : ℕ) : ℕ :=
    if (d = 24 ∧ 127 ≤ e) ∨ (d = 23 ∧ 121 ≤ e) then 1
    else if (d = 23 ∧ e = 120) ∨ (d = 22 ∧ e = 114) then 2
    else if (d = 23 ∧ e = 119) ∨ (d = 22 ∧ e = 113) ∨ (d = 21 ∧ e = 107) then 3
    else 0
  let K (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj] (v : Fin 46) : ℕ :=
    k (G.degree v) (G.induce (G.neighborSet v)).edgeFinset.card
  let S (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj] : Prop :=
    ∃ v, (K G v = 1 ∧ ∃ u, G.Adj v u ∧ K G u ≠ 0) ∨
      (K G v = 2 ∧ ∃ u, G.Adj v u ∧ K G u = 2) ∨
      (K G v = 2 ∧ 5 ≤ (univ.filter fun u => G.Adj v u ∧ K G u ≠ 0).card) ∨
      (K G v = 3 ∧ G.degree v ≠ 21 ∧
        8 ≤ (univ.filter fun u => G.Adj v u ∧ K G u ≠ 0).card) ∨
      (K G v = 3 ∧ G.degree v = 21 ∧
        8 ≤ (univ.filter fun u => G.Adj v u ∧ K G u ≠ 0 ∧ G.degree u ≠ 21).card)
  let W (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj] (v : Fin 46) : ℤ :=
    if K G v = 1 then 5 else if K G v = 2 then 2 else if K G v = 3 then 1 else 0
  let X (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj] (v : Fin 46) : ℤ :=
    if G.degree v = 24 ∧ K G v ≠ 1 then 1 else 0
  let cap (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj] (v : Fin 46) : Prop :=
    (G.induce (G.neighborSet v)).edgeFinset.card ≤
      if G.degree v = 21 then 107 else if G.degree v = 22 then 114
      else if G.degree v = 23 then 122 else 132
  ∀ (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj], G.CliqueFree 5 → Gᶜ.CliqueFree 5 →
    (∀ v, 21 ≤ G.degree v ∧ G.degree v ≤ 24) →
    (∀ v, 21 ≤ Gᶜ.degree v ∧ Gᶜ.degree v ≤ 24) →
    (∀ v, cap G v) → (∀ v, cap Gᶜ v) →
    46 + (∑ v : Fin 46, X G v) + (∑ v : Fin 46, X Gᶜ v) ≤
      (∑ v : Fin 46, W G v) + (∑ v : Fin 46, W Gᶜ v) →
    S G ∨ S Gᶜ

/-- The five gluing computations of Theorem 5.4 and Sections 6–7 exclude
each selected local pattern from a 46-vertex Ramsey (5,5) graph. -/
def H4 : Prop :=
  let k (d e : ℕ) : ℕ :=
    if (d = 24 ∧ 127 ≤ e) ∨ (d = 23 ∧ 121 ≤ e) then 1
    else if (d = 23 ∧ e = 120) ∨ (d = 22 ∧ e = 114) then 2
    else if (d = 23 ∧ e = 119) ∨ (d = 22 ∧ e = 113) ∨ (d = 21 ∧ e = 107) then 3
    else 0
  let K (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj] (v : Fin 46) : ℕ :=
    k (G.degree v) (G.induce (G.neighborSet v)).edgeFinset.card
  let S (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj] : Prop :=
    ∃ v, (K G v = 1 ∧ ∃ u, G.Adj v u ∧ K G u ≠ 0) ∨
      (K G v = 2 ∧ ∃ u, G.Adj v u ∧ K G u = 2) ∨
      (K G v = 2 ∧ 5 ≤ (univ.filter fun u => G.Adj v u ∧ K G u ≠ 0).card) ∨
      (K G v = 3 ∧ G.degree v ≠ 21 ∧
        8 ≤ (univ.filter fun u => G.Adj v u ∧ K G u ≠ 0).card) ∨
      (K G v = 3 ∧ G.degree v = 21 ∧
        8 ≤ (univ.filter fun u => G.Adj v u ∧ K G u ≠ 0 ∧ G.degree u ≠ 21).card)
  ∀ (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj], G.CliqueFree 5 → Gᶜ.CliqueFree 5 →
    (∀ v, 21 ≤ G.degree v ∧ G.degree v ≤ 24) → S G → False

theorem main : H1 → H2 → H3 → H4 →
    type_of% @RamseyNumbers.ramsey_number_five_five_upper_bound := by
  classical
  intro hR hBound hSelect hGlue G hG
  obtain ⟨hK, hI⟩ := hG
  have hKC : Gᶜᶜ.CliqueFree 5 := by simpa using hK
  have h46 : Fintype.card (Fin 46) = 46 := Fintype.card_fin _
  have hd := OMA.Ramsey55.degree_range_of_card46 hR G h46 hK hI
  have hdc := OMA.Ramsey55.degree_range_of_card46 hR Gᶜ h46 hI hKC
  have he := OMA.Ramsey55.neighbor_edge_bound_from_fin hR hBound G h46 hK hI
  have hec := OMA.Ramsey55.neighbor_edge_bound_from_fin hR hBound Gᶜ h46 hI hKC
  have hn := Ramsey55Excess.weights_total G hd hdc he hec
  rcases hSelect G hK hI hd hdc he hec hn with hs | hs
  · exact hGlue G hK hI hd hs
  · exact hGlue Gᶜ hI hKC hdc hs

end OMA.R_RamseyNumbers_ramsey_number_five_five_upper_bound_R1
