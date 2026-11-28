import FormalConjectures.ErdosProblems.«876»

open Finset Erdos876 Filter

theorem OMA.solution : type_of% @Erdos876.erdos_876.variants.density_zero := by
  classical
  intro A ha hs
  simp only [Set.HasDensity, Set.partialDensity, Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat,
    Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / ε)
  obtain ⟨F, hF, hFc⟩ := ha.exists_subset_card_eq k
  let S := ∑ a ∈ F, a
  let L := S + 1
  refine ⟨S + k * L + 1, fun n hn => ?_⟩
  let U := (range n).filter (· ∈ A)
  let T := U \ range L
  let f (p : ℕ × ℕ) := (∑ a ∈ F.filter (· < p.1), a) + p.2
  have hcoll {i j x y : ℕ} (hi : i ∈ F) (hij : i < j) (hx : x ∈ A) (hy : y ∈ A)
      (hL : L ≤ y) (he : f (i, x) = f (j, y)) : False := by
    let D := F.filter (· < j) \ F.filter (· < i)
    have hsub : F.filter (· < i) ⊆ F.filter (· < j) := fun a ha =>
      mem_filter.mpr ⟨(mem_filter.mp ha).1, (mem_filter.mp ha).2.trans hij⟩
    have hsum : (∑ a ∈ D, a) + ∑ a ∈ F.filter (· < i), a = ∑ a ∈ F.filter (· < j), a :=
      sum_sdiff hsub
    have hle : i ≤ ∑ a ∈ D, a :=
      single_le_sum (f := id) (fun _ _ => Nat.zero_le _) (by simp [D, hi, hij])
    have hpos := (hs i (hF hi)).1
    have hD : ∀ a ∈ D, a ∈ F := fun a ha => (mem_filter.mp (mem_sdiff.mp ha).1).1
    have hlt : ∀ a ∈ F, a < y := fun a ha =>
      lt_of_le_of_lt (show a ≤ S from single_le_sum (f := id) (fun _ _ => Nat.zero_le _) ha) (by omega)
    have hny : y ∉ D := fun hm => lt_irrefl y (hlt y (hD y hm))
    have hyx : y < x := by dsimp [f] at he; omega
    refine (hs x hx).2 ⟨insert y D, fun a ha => ?_, by rw [sum_insert hny]; dsimp [f] at he; omega⟩
    rcases mem_insert.mp ha with rfl | ha
    · exact ⟨hy, hyx⟩
    · exact ⟨hF (hD a ha), (hlt a (hD a ha)).trans hyx⟩
  have hinj : Set.InjOn f ↑(F ×ˢ T) := by
    rintro ⟨i, x⟩ hix ⟨j, y⟩ hjy he
    obtain ⟨hi, hx⟩ := mem_product.mp hix
    obtain ⟨hj, hy⟩ := mem_product.mp hjy
    have hT : ∀ z ∈ T, z ∈ A ∧ L ≤ z := fun z hz =>
      ⟨(mem_filter.mp (mem_sdiff.mp hz).1).2, not_lt.mp (mem_range.not.mp (mem_sdiff.mp hz).2)⟩
    rcases lt_trichotomy i j with h | rfl | h
    · exact (hcoll hi h (hT x hx).1 (hT y hy).1 (hT y hy).2 he).elim
    · simp_all [f]
    · exact (hcoll hj h (hT y hy).1 (hT x hx).1 (hT x hx).2 he.symm).elim
  have hsub : (F ×ˢ T).image f ⊆ range (n + S) := by
    rintro _ hv
    obtain ⟨⟨i, y⟩, hp, rfl⟩ := mem_image.mp hv
    have hy : y < n := mem_range.mp (mem_filter.mp (mem_sdiff.mp (mem_product.mp hp).2).1).1
    have hsF : ∑ a ∈ F.filter (· < i), a ≤ S := sum_le_sum_of_subset (filter_subset _ _)
    exact mem_range.mpr (by dsimp [f]; omega)
  have hpack : k * T.card ≤ n + S := by
    simpa [hFc, card_image_of_injOn hinj] using card_le_card hsub
  have hcard : U.card ≤ T.card + L := by
    have := card_sdiff_add_card_inter U (range L)
    have := card_le_card (inter_subset_right (s₁ := U) (s₂ := range L))
    simp only [card_range] at this; dsimp [T]; omega
  have hU : (U : Set ℕ) = A ∩ Set.Iio n := by ext y; simp [U, and_comm]
  have hle : (k : ℝ) * (A ∩ Set.Iio n).ncard ≤ 2 * n := by
    rw [← hU, Set.ncard_coe_finset]
    exact_mod_cast (show k * U.card ≤ 2 * n by nlinarith)
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hk' : 2 < (k : ℝ) * ε := (div_lt_iff₀ hε).mp hk
  have hkp : (0 : ℝ) < k := by by_contra! h; nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hpos]
  apply lt_of_mul_lt_mul_left (a := (k : ℝ)) _ hkp.le
  nlinarith [mul_lt_mul_of_pos_right hk' hpos]
