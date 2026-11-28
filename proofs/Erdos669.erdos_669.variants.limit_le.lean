import FormalConjectures.ErdosProblems.«669»

/-! Each counted line contributes disjoint two-element subsets of the point set. -/

open Erdos669 Filter Topology
open scoped EuclideanGeometry

theorem OMA.solution : type_of% @Erdos669.erdos_669.variants.limit_le := by
  classical
  intro k hk L hL
  have c2 (m : ℕ) (hm : 1 ≤ m) : (m.choose 2 : ℝ) * 2 = (m : ℝ) * ((m : ℝ) - 1) := by
    have h : m.choose 2 * 2 = m * (m - 1) := by
      rw [Nat.choose_two_right, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self m)]
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hm, Nat.cast_one] using congrArg (fun x : ℕ => (x : ℝ)) h
  have hkposN : 0 < k.choose 2 := Nat.choose_pos hk
  have hkpos : (0 : ℝ) < k.choose 2 := by exact_mod_cast hkposN
  refine le_of_tendsto hL ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hbound : maxLinesAtLeast k n ≤ n.choose 2 / k.choose 2 := by
    refine csSup_le' ?_
    rintro _ ⟨S, rfl, rfl⟩
    refine (Nat.le_div_iff_mul_le hkposN).2 ?_
    let lines := linesWithAtLeastPointsFor k (S : Set ℝ²)
    have hfin : lines.Finite :=
      ((S.finite_toSet.prod S.finite_toSet).image fun pq : ℝ² × ℝ² => affineSpan ℝ {pq.1, pq.2}).subset
        fun _ ⟨⟨p, hp, q, hq, _, hL⟩, _⟩ => ⟨(p, q), Set.mk_mem_prod hp hq, hL⟩
    let Ls := hfin.toFinset
    let pts (L : AffineSubspace ℝ ℝ²) := S.filter (· ∈ L)
    let pairs (L : AffineSubspace ℝ ℝ²) := (pts L).powersetCard 2
    have hdisj : (Ls : Set (AffineSubspace ℝ ℝ²)).PairwiseDisjoint pairs := fun L hL M hM hne =>
      Finset.disjoint_left.2 fun U hUL hUM => by
        obtain ⟨hUL1, hc⟩ := Finset.mem_powersetCard.mp hUL
        obtain ⟨p, q, hp, hq, hpq⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < U.card)
        obtain ⟨_, _, _, _, _, ha⟩ := (hfin.mem_toFinset.mp hL).1
        obtain ⟨_, _, _, _, _, hc'⟩ := (hfin.mem_toFinset.mp hM).1
        have hl : affineSpan ℝ {p, q} = L := by
          rw [← ha]; exact affineSpan_pair_eq_of_mem_of_mem_of_ne
            (ha ▸ (Finset.mem_filter.mp (hUL1 hp)).2) (ha ▸ (Finset.mem_filter.mp (hUL1 hq)).2) hpq
        have hm : affineSpan ℝ {p, q} = M := by
          rw [← hc']; exact affineSpan_pair_eq_of_mem_of_mem_of_ne
            (hc' ▸ (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp hUM).1 hp)).2)
            (hc' ▸ (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp hUM).1 hq)).2) hpq
        exact hne (hl.symm.trans hm)
    have hsub : Ls.biUnion pairs ⊆ S.powersetCard 2 := fun U hU => by
      obtain ⟨L, _, hUL⟩ := Finset.mem_biUnion.mp hU
      obtain ⟨h1, h2⟩ := Finset.mem_powersetCard.mp hUL
      exact Finset.mem_powersetCard.2 ⟨h1.trans (Finset.filter_subset _ _), h2⟩
    change lines.ncard * k.choose 2 ≤ S.card.choose 2
    rw [Set.ncard_eq_toFinset_card lines hfin]
    calc Ls.card * k.choose 2 = ∑ _ ∈ Ls, k.choose 2 := by simp
      _ ≤ ∑ L ∈ Ls, (pairs L).card := Finset.sum_le_sum fun L hL => by
          rw [Finset.card_powersetCard]
          refine Nat.choose_le_choose 2 ?_
          have heq : ((pts L : Finset ℝ²) : Set ℝ²) = (L : Set ℝ²) ∩ S := by ext p; simp [pts, and_comm]
          rw [← Set.ncard_coe_finset, heq]; exact (hfin.mem_toFinset.mp hL).2
      _ = (Ls.biUnion pairs).card := (Finset.card_biUnion hdisj).symm
      _ ≤ S.card.choose 2 := (Finset.card_le_card hsub).trans_eq (Finset.card_powersetCard _ _)
  have hle : (maxLinesAtLeast k n : ℝ) * k.choose 2 ≤ n.choose 2 := by
    exact_mod_cast (Nat.le_div_iff_mul_le hkposN).1 hbound
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hchoose : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by nlinarith [c2 n hn]
  rw [← c2 k (by omega), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith
