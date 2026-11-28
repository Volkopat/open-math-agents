import FormalConjectures.ErdosProblems.«669»

/-! Two-element subsets determine lines, and points on a parabola give distinct lines. -/

open Erdos669
open scoped EuclideanGeometry

theorem OMA.solution : type_of% @Erdos669.erdos_669.variants.k_two := by
  classical
  intro n
  let ps (U : Finset ℝ²) : AffineSubspace ℝ ℝ² := affineSpan ℝ (U : Set ℝ²)
  have hsub (S : Finset ℝ²) : linesWithAtLeastPointsFor 2 (S : Set ℝ²) ⊆
      ps '' (S.powersetCard 2 : Set (Finset ℝ²)) := by
    rintro _ ⟨⟨p, hp, q, hq, hpq, rfl⟩, _⟩
    refine ⟨{p, q}, Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair_eq_two_iff.mpr hpq⟩,
      by simp [ps]⟩
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hp, hq⟩
  have hup : maxLinesAtLeast 2 n ≤ n.choose 2 := by
    refine csSup_le' ?_
    rintro _ ⟨S, rfl, rfl⟩
    calc (linesWithAtLeastPointsFor 2 (S : Set ℝ²)).ncard
        ≤ (ps '' (S.powersetCard 2 : Set (Finset ℝ²))).ncard :=
          Set.ncard_le_ncard (hsub S) ((S.powersetCard 2).finite_toSet.image _)
      _ ≤ (S.powersetCard 2 : Set (Finset ℝ²)).ncard := Set.ncard_image_le (S.powersetCard 2).finite_toSet
      _ = S.card.choose 2 := by rw [Set.ncard_coe_finset, Finset.card_powersetCard]
  let pt (x : ℝ) : ℝ² := WithLp.toLp 2 ![x, x ^ 2]
  have hpt : Function.Injective pt := fun x y h => by simpa [pt] using congrArg (· 0) h
  let S : Finset ℝ² := (Finset.range n).map ⟨fun j : ℕ => pt j, fun _ _ h => by exact_mod_cast hpt h⟩
  have hSn : S.card = n := by simp [S]
  have hSr : (S : Set ℝ²) ⊆ Set.range pt := by
    intro p hp; obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hp; exact ⟨j, rfl⟩
  have hpi {U : Finset ℝ²} (hU : U ∈ S.powersetCard 2) : (ps U : Set ℝ²) ∩ S = U := by
    obtain ⟨hUS, hc⟩ := Finset.mem_powersetCard.mp hU
    obtain ⟨p, q, _, rfl⟩ := Finset.card_eq_two.mp hc
    have hp : p ∈ S := hUS (by simp); have hq : q ∈ S := hUS (by simp)
    obtain ⟨x, rfl⟩ := hSr hp; obtain ⟨y, rfl⟩ := hSr hq
    refine Set.Subset.antisymm ?_ fun _ hz => ⟨subset_affineSpan ℝ _ hz, hUS hz⟩
    rintro z ⟨hz, hzS⟩
    obtain ⟨w, rfl⟩ := hSr hzS
    have hz' : pt w ∈ line[ℝ, pt x, pt y] := by simpa [ps] using hz
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hz'
    have h0 := congrArg (· 0) ht
    have h1 := congrArg (· 1) ht
    simp [AffineMap.lineMap_apply_module, pt, PiLp.add_apply, PiLp.smul_apply] at h0 h1
    have h : (w - x) * (w - y) = 0 := by linear_combination (x + y) * h0 - h1
    rcases mul_eq_zero.mp h with hw | hw <;> simp [sub_eq_zero.mp hw]
  have hlo : n.choose 2 ≤ maxLinesExactly 2 n := by
    refine le_csSup (lineCountsExactly_bddAbove 2 n) ⟨S, hSn, ?_⟩
    have hinj : Set.InjOn ps (S.powersetCard 2 : Set (Finset ℝ²)) := fun U hU V hV h =>
      Finset.coe_injective (by rw [← hpi hU, ← hpi hV, h])
    have heq : EuclideanGeometry.linesWithPointsFor 2 (S : Set ℝ²) =
        ps '' (S.powersetCard 2 : Set (Finset ℝ²)) := Set.Subset.antisymm
      ((linesWithPointsFor_subset_linesWithAtLeastPointsFor 2 _).trans (hsub S))
      (by rintro _ ⟨U, hU, rfl⟩
          obtain ⟨hUS, hc⟩ := Finset.mem_powersetCard.mp hU
          refine ⟨?_, by rw [hpi hU, Set.ncard_coe_finset, hc]⟩
          obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hc
          exact ⟨p, hUS (by simp), q, hUS (by simp), hpq, by simp [ps]⟩)
    rw [heq, hinj.ncard_image, Set.ncard_coe_finset, Finset.card_powersetCard, hSn]
  have hmid := erdos_669.variants.exactly_le_atLeast 2 n
  omega

