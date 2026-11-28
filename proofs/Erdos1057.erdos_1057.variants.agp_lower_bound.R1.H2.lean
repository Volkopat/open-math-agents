import OMAReductions.R_Erdos1057_erdos_1057_variants_agp_lower_bound_R1

open Finset
/-!
# Counting bounded product-one subsets

Given a t-element subset A, take a product-one subset I of A with maximum
cardinality. Its complement has size at most n. Otherwise it contains a
nonempty product-one subset that could be added to I. Extend the complement
to an n-element subset D of A. The two sets recover A by union. This bounds
the number of t-subsets by the number of admissible I times the number of
n-subsets of the original reservoir. This is the counting bound of Alford,
Granville and Pomerance, Proposition 1.2. Credit: @ZedingZhang.
-/

namespace OMA.CarmichaelSubsets

open Finset
open scoped Classical

private lemma decompose {A P : Finset ℕ} {M n t : ℕ} (sub : A ⊆ P)
    (size : A.card = t) (hnt : n ≤ t)
    (extract : ∀ S ⊆ P, n < S.card → ∃ I ⊆ S, I.Nonempty ∧ (∏ p ∈ I, p) ≡ 1 [MOD M]) :
    ∃ I D : Finset ℕ, I ⊆ P ∧ t-n ≤ I.card ∧ I.card ≤ t ∧
      (∏ p ∈ I, p) ≡ 1 [MOD M] ∧ D ⊆ P ∧ D.card = n ∧ I ∪ D = A := by
  classical
  let F := A.powerset.filter (fun I => (∏ p ∈ I, p) ≡ 1 [MOD M])
  have empty : ∅ ∈ F := by
    refine mem_filter.mpr ⟨mem_powerset.mpr (empty_subset A), ?_⟩
    simpa only [prod_empty] using (show 1 ≡ 1 [MOD M] from rfl)
  obtain ⟨I, hi, hmax⟩ := exists_max_image F card ⟨∅,empty⟩
  obtain ⟨subA, one⟩ := mem_filter.mp hi
  have ia := mem_powerset.mp subA
  have small : (A \ I).card ≤ n := by
    by_contra! large
    obtain ⟨J,hj,hjpos,oneJ⟩ := extract (A \ I) (sdiff_subset.trans sub) large
    have dis : Disjoint I J := disjoint_left.mpr (fun x hx hxj =>
      (mem_sdiff.mp (hj hxj)).2 hx)
    have together : I ∪ J ∈ F := by
      refine mem_filter.mpr ⟨mem_powerset.mpr
        (union_subset ia (hj.trans sdiff_subset)), ?_⟩
      rw [prod_union dis]
      simpa only [one_mul] using one.mul oneJ
    have bigger := hmax (I ∪ J) together
    rw [card_union_of_disjoint dis] at bigger
    have nonzero := card_pos.mpr hjpos
    omega
  obtain ⟨D,rest,da,dsize⟩ := exists_subsuperset_card_eq
    (show A \ I ⊆ A from sdiff_subset) small (by omega)
  have ilo := card_sdiff_of_subset ia
  have ihi := card_le_card ia
  refine ⟨I,D,ia.trans sub,by omega,by omega,one,da.trans sub,dsize,?_⟩
  apply Subset.antisymm (union_subset ia da)
  intro a ha
  by_cases h : a ∈ I
  · exact mem_union.mpr (Or.inl h)
  · exact mem_union.mpr (Or.inr (rest (mem_sdiff.mpr ⟨ha,h⟩)))

theorem counted : OMA.R_Erdos1057_erdos_1057_variants_agp_lower_bound_R1.H2 := by
  classical
  intro P M n t hnt _ extract
  let G := P.powerset.filter (fun I => t-n ≤ I.card ∧ I.card ≤ t ∧
    (∏ p ∈ I, p) ≡ 1 [MOD M])
  let pairs := G ×ˢ P.powersetCard n
  let join (z : Finset ℕ × Finset ℕ) := z.1 ∪ z.2
  have cover : P.powersetCard t ⊆ pairs.image join := by
    intro A ha
    obtain ⟨sub, size⟩ := mem_powersetCard.mp ha
    obtain ⟨I,D,ip,lo,hi,one,dp,dsize,un⟩ := decompose sub size hnt extract
    refine mem_image.mpr ⟨(I,D), mem_product.mpr ⟨?_, ?_⟩, un⟩
    · exact mem_filter.mpr ⟨mem_powerset.mpr ip,lo,hi,one⟩
    · exact mem_powersetCard.mpr ⟨dp,dsize⟩
  have bound := (card_le_card cover).trans (card_image_le (s := pairs) (f := join))
  simpa only [pairs, card_product, card_powersetCard, G] using bound

end OMA.CarmichaelSubsets

theorem OMA.solution : OMA.R_Erdos1057_erdos_1057_variants_agp_lower_bound_R1.H2 :=
  OMA.CarmichaelSubsets.counted
