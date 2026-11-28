import OMAReductions.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1
import Mathlib

-- Step Erdos103.erdos_103.variants.two_le.R1.H2.R1.H1: hypothesis H1 of reduction Erdos103.erdos_103.variants.two_le.R1.H2.R1
-- Credit: @chris01-dev

/-! Separated points on a circle about their centroid: a circle of radius r carries at most
12 r + 12 points with pairwise distances at least 1, and r is at most twice the diameter, so
such a set of n points has diameter at least (n - 12) / 24. Points of the integer grid give a
separated set of n points of diameter at most 2 sqrt n + 2, which is smaller for n >= 2500. -/

open EuclideanGeometry Filter Finset
open Erdos103
open scoped Classical ENNReal

namespace OMA.E103

/-- Squared distance in the plane in coordinates. -/
lemma dist_sq_coord (p q : ℝ²) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)),
    Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

/-- A coordinate difference is at most the distance. -/
lemma abs_coord_le (p q : ℝ²) (i : Fin 2) : |p i - q i| ≤ dist p q := by
  have h := dist_sq_coord p q
  have hd : (0 : ℝ) ≤ dist p q := dist_nonneg
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · exact abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (p 1 - q 1)]) hd
  · exact abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (p 0 - q 0)]) hd

/-- Separation as a real inequality. -/
lemma sep_dist {n : ℕ} {B : Finset ℝ²} (hB : B ∈ separatedSets n) {x y : ℝ²}
    (hx : x ∈ B) (hy : y ∈ B) (hxy : x ≠ y) : 1 ≤ dist x y := by
  have hh := hB.2 (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
  change (1 : ℝ≥0∞) ≤ edist x y at hh
  rwa [edist_dist, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff dist_nonneg] at hh

/-- Membership in `separatedSets` from real inequalities. -/
lemma mem_separatedSets_of {n : ℕ} {B : Finset ℝ²} (hc : B.card = n)
    (h : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → 1 ≤ dist x y) : B ∈ separatedSets n := by
  refine ⟨hc, ?_⟩
  intro x hx y hy hxy
  change (1 : ℝ≥0∞) ≤ edist x y
  rw [edist_dist, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff dist_nonneg]
  exact h x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hxy

/-- Deleting a point of a separated (n+1)-set gives a separated n-set. -/
lemma erase_mem {n : ℕ} {B : Finset ℝ²} (hB : B ∈ separatedSets (n + 1)) {p : ℝ²}
    (hp : p ∈ B) : B.erase p ∈ separatedSets n := by
  apply mem_separatedSets_of
  · rw [Finset.card_erase_of_mem hp, hB.1]
    simp
  · intro x hx y hy hxy
    exact sep_dist hB (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy) hxy

/-- Step 1: deletions are minimisers. -/
lemma erase_isMinimiser {n : ℕ} {B : Finset ℝ²} (hB : B ∈ separatedSets (n + 1))
    (hmin : ∀ C ∈ separatedSets n, Metric.diam (B : Set ℝ²) ≤ Metric.diam (C : Set ℝ²))
    {p : ℝ²} (hp : p ∈ B) : IsMinimiser n (B.erase p) := by
  refine ⟨erase_mem hB hp, ?_⟩
  rw [isMinOn_iff]
  intro C hC
  have h1 : Metric.diam ((B.erase p : Finset ℝ²) : Set ℝ²) ≤ Metric.diam (B : Set ℝ²) :=
    Metric.diam_mono (Finset.coe_subset.mpr (Finset.erase_subset p B))
      B.finite_toSet.isBounded
  exact h1.trans (hmin C hC)

/-- Congruent finite sets have the same sum of squared distances. -/
lemma sumsq_congr {X Y : Finset ℝ²} (h : Congruent X Y) :
    ∑ x ∈ X, ∑ y ∈ X, dist x y ^ 2 = ∑ x ∈ Y, ∑ y ∈ Y, dist x y ^ 2 := by
  obtain ⟨f, hf⟩ := h
  have hY : Y = X.image f := by
    apply Finset.coe_injective
    rw [Finset.coe_image]
    exact hf.symm
  rw [hY, Finset.sum_image f.injective.injOn]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_image f.injective.injOn]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [f.dist_eq]

/-- The sum of squared distances after deleting one point. -/
lemma sumsq_erase {B : Finset ℝ²} {p : ℝ²} (hp : p ∈ B) :
    ∑ x ∈ B.erase p, ∑ y ∈ B.erase p, dist x y ^ 2
      = ∑ x ∈ B, ∑ y ∈ B, dist x y ^ 2 - 2 * ∑ y ∈ B, dist p y ^ 2 := by
  have h1 : ∑ x ∈ B, ∑ y ∈ B, dist x y ^ 2
      = ∑ x ∈ B.erase p, ∑ y ∈ B, dist x y ^ 2 + ∑ y ∈ B, dist p y ^ 2 :=
    (Finset.sum_erase_add B (fun x => ∑ y ∈ B, dist x y ^ 2) hp).symm
  have h2 : ∀ x : ℝ², ∑ y ∈ B, dist x y ^ 2
      = ∑ y ∈ B.erase p, dist x y ^ 2 + dist x p ^ 2 :=
    fun x => (Finset.sum_erase_add B (fun y => dist x y ^ 2) hp).symm
  have h3 : ∑ x ∈ B.erase p, ∑ y ∈ B, dist x y ^ 2
      = ∑ x ∈ B.erase p, ∑ y ∈ B.erase p, dist x y ^ 2
        + ∑ x ∈ B.erase p, dist x p ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => h2 x)
  have h4 : ∑ y ∈ B, dist p y ^ 2 = ∑ x ∈ B.erase p, dist x p ^ 2 := by
    rw [h2 p, dist_self]
    have hc : ∀ x : ℝ², dist x p = dist p x := fun x => dist_comm x p
    simp [hc]
  linarith

/-- Expansion of the sum of squared distances from a point. -/
lemma g_expand (B : Finset ℝ²) (p : ℝ²) :
    ∑ y ∈ B, dist p y ^ 2 = (B.card : ℝ) * (p 0 ^ 2 + p 1 ^ 2)
      - 2 * (p 0 * (∑ y ∈ B, y 0) + p 1 * (∑ y ∈ B, y 1))
      + ((∑ y ∈ B, y 0 ^ 2) + (∑ y ∈ B, y 1 ^ 2)) := by
  have h : ∀ y ∈ B, dist p y ^ 2
      = (p 0 ^ 2 + p 1 ^ 2) - (2 * (p 0 * y 0) + 2 * (p 1 * y 1)) + (y 0 ^ 2 + y 1 ^ 2) := by
    intro y _
    rw [dist_sq_coord]
    ring
  rw [Finset.sum_congr rfl h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum]
  ring

/-- Algebra: equal values of the expansion give equal distances to the centroid. -/
lemma center_alg (N a b p0 p1 q0 q1 T : ℝ) (hN : 0 < N)
    (h : N * (p0 ^ 2 + p1 ^ 2) - 2 * (p0 * a + p1 * b) + T
      = N * (q0 ^ 2 + q1 ^ 2) - 2 * (q0 * a + q1 * b) + T) :
    (p0 - a / N) ^ 2 + (p1 - b / N) ^ 2 = (q0 - a / N) ^ 2 + (q1 - b / N) ^ 2 := by
  have hcx : N * (a / N) = a := by field_simp
  have hcy : N * (b / N) = b := by field_simp
  apply mul_left_cancel₀ hN.ne'
  linear_combination h - 2 * (p0 - q0) * hcx - 2 * (p1 - q1) * hcy

/-- A coordinate of a point of `B` is within the diameter of the centroid coordinate. -/
lemma centroid_coord (B : Finset ℝ²) (p : ℝ²) (hp : p ∈ B) (i : Fin 2) :
    |(B.card : ℝ) * p i - ∑ y ∈ B, y i| ≤ (B.card : ℝ) * Metric.diam (B : Set ℝ²) := by
  have h1 : (B.card : ℝ) * p i - ∑ y ∈ B, y i = ∑ y ∈ B, (p i - y i) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [h1]
  calc |∑ y ∈ B, (p i - y i)| ≤ ∑ y ∈ B, |p i - y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y ∈ B, Metric.diam (B : Set ℝ²) :=
        Finset.sum_le_sum (fun y hy => (abs_coord_le p y i).trans
          (Metric.dist_le_diam_of_mem B.finite_toSet.isBounded
            (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hy)))
    _ = (B.card : ℝ) * Metric.diam (B : Set ℝ²) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Dividing the centroid bound by the number of points. -/
lemma centroid_sq (N s x d : ℝ) (hN : 0 < N) (h : |N * x - s| ≤ N * d) :
    (x - s / N) ^ 2 ≤ d ^ 2 := by
  have hcx : N * (s / N) = s := by field_simp
  have h' : N * |x - s / N| ≤ N * d := by
    have e : N * x - s = N * (x - s / N) := by rw [mul_sub, hcx]
    rw [e, abs_mul, abs_of_pos hN] at h
    exact h
  have h2 : |x - s / N| ≤ d := le_of_mul_le_mul_left h' hN
  have h3 := abs_le.mp h2
  exact sq_le_sq' h3.1 h3.2

/-- Step 2: if all one-point deletions are congruent, the points lie on a circle whose
squared radius is at most twice the squared diameter. -/
lemma exists_center (B : Finset ℝ²) (hne : B.Nonempty)
    (hcong : ∀ p ∈ B, ∀ q ∈ B, Congruent (B.erase p) (B.erase q)) :
    ∃ cx cy ρ : ℝ, (∀ p ∈ B, (p 0 - cx) ^ 2 + (p 1 - cy) ^ 2 = ρ) ∧
      ρ ≤ 2 * Metric.diam (B : Set ℝ²) ^ 2 := by
  obtain ⟨p₀, hp₀⟩ := hne
  have hN : (0 : ℝ) < (B.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨p₀, hp₀⟩
  have hg : ∀ p ∈ B, ∀ q ∈ B, ∑ y ∈ B, dist p y ^ 2 = ∑ y ∈ B, dist q y ^ 2 := by
    intro p hp q hq
    have h1 := sumsq_congr (hcong p hp q hq)
    rw [sumsq_erase hp, sumsq_erase hq] at h1
    linarith
  have key : ∀ p ∈ B, ∀ q ∈ B,
      (p 0 - (∑ y ∈ B, y 0) / (B.card : ℝ)) ^ 2 + (p 1 - (∑ y ∈ B, y 1) / (B.card : ℝ)) ^ 2
        = (q 0 - (∑ y ∈ B, y 0) / (B.card : ℝ)) ^ 2
          + (q 1 - (∑ y ∈ B, y 1) / (B.card : ℝ)) ^ 2 := by
    intro p hp q hq
    have h := hg p hp q hq
    rw [g_expand, g_expand] at h
    exact center_alg _ _ _ _ _ _ _ _ hN h
  refine ⟨(∑ y ∈ B, y 0) / (B.card : ℝ), (∑ y ∈ B, y 1) / (B.card : ℝ),
    (p₀ 0 - (∑ y ∈ B, y 0) / (B.card : ℝ)) ^ 2
      + (p₀ 1 - (∑ y ∈ B, y 1) / (B.card : ℝ)) ^ 2, fun p hp => key p hp p₀ hp₀, ?_⟩
  have h0 := centroid_sq _ _ _ _ hN (centroid_coord B p₀ hp₀ 0)
  have h1 := centroid_sq _ _ _ _ hN (centroid_coord B p₀ hp₀ 1)
  linarith

/-- Step 3, one class: points on a circle with `|u| ≤ v`, pairwise at distance at least 1. -/
lemma class_card {ι : Type*} (F : Finset ι) (u v : ι → ℝ) (ρ : ℝ)
    (h1 : ∀ i ∈ F, |u i| ≤ v i) (h2 : ∀ i ∈ F, u i ^ 2 + v i ^ 2 = ρ)
    (h3 : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → 1 ≤ (u i - u j) ^ 2 + (v i - v j) ^ 2) :
    (F.card : ℝ) ≤ 3 * Real.sqrt ρ + 3 := by
  obtain ⟨M, hM⟩ : ∃ M : ℤ, M = ⌈(10 / 7 : ℝ) * Real.sqrt ρ⌉ := ⟨_, rfl⟩
  have hinj : Set.InjOn (fun i => ⌊(10 / 7 : ℝ) * u i⌋) (F : Set ι) := by
    intro i hi j hj hij
    by_contra hne
    have hi' := Finset.mem_coe.mp hi
    have hj' := Finset.mem_coe.mp hj
    have hij' : ⌊(10 / 7 : ℝ) * u i⌋ = ⌊(10 / 7 : ℝ) * u j⌋ := hij
    have hfl : |(10 / 7 : ℝ) * u i - (10 / 7 : ℝ) * u j| < 1 :=
      Int.abs_sub_lt_one_of_floor_eq_floor hij'
    have hsep := h3 i hi' j hj' hne
    have hi1 := abs_le.mp (h1 i hi')
    have hj1 := abs_le.mp (h1 j hj')
    have hi2 := h2 i hi'
    have hj2 := h2 j hj'
    have hfl' := abs_lt.mp hfl
    have hx : (u i - u j) ^ 2 < 49 / 100 := by nlinarith [hfl'.1, hfl'.2]
    have hs : 0 ≤ v i + v j := by linarith [hi1.1, hi1.2, hj1.1, hj1.2]
    rcases hs.eq_or_lt with hs0 | hspos
    · have hvi : v i = 0 := by linarith [hi1.1, hi1.2, hj1.1, hj1.2]
      have hvj : v j = 0 := by linarith [hi1.1, hi1.2, hj1.1, hj1.2]
      have hui : u i = 0 := by linarith [hi1.1, hi1.2]
      have huj : u j = 0 := by linarith [hj1.1, hj1.2]
      rw [hvi, hvj, hui, huj] at hsep
      norm_num at hsep
    · have h5 : -(v i + v j) ≤ u i + u j := by linarith [hi1.1, hj1.1]
      have h6 : u i + u j ≤ v i + v j := by linarith [hi1.2, hj1.2]
      have hsq : (u i + u j) ^ 2 ≤ (v i + v j) ^ 2 := sq_le_sq' h5 h6
      have e0 : (v i - v j) * (v i + v j) = -((u i - u j) * (u i + u j)) := by
        linear_combination hi2 - hj2
      have e : (v i - v j) ^ 2 * (v i + v j) ^ 2 = (u i - u j) ^ 2 * (u i + u j) ^ 2 := by
        calc (v i - v j) ^ 2 * (v i + v j) ^ 2 = ((v i - v j) * (v i + v j)) ^ 2 := by ring
          _ = (-((u i - u j) * (u i + u j))) ^ 2 := by rw [e0]
          _ = (u i - u j) ^ 2 * (u i + u j) ^ 2 := by ring
      have hmul : (v i - v j) ^ 2 * (v i + v j) ^ 2 ≤ (u i - u j) ^ 2 * (v i + v j) ^ 2 := by
        rw [e]
        exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      have hle : (v i - v j) ^ 2 ≤ (u i - u j) ^ 2 :=
        le_of_mul_le_mul_right hmul (pow_pos hspos 2)
      linarith
  have hmaps : ∀ i ∈ F, ⌊(10 / 7 : ℝ) * u i⌋ ∈ Finset.Icc (-M) M := by
    intro i hi
    have hi2 := h2 i hi
    have hu : |u i| ≤ Real.sqrt ρ := Real.abs_le_sqrt (by nlinarith [sq_nonneg (v i)])
    have hu' := abs_le.mp hu
    have hM1 : (10 / 7 : ℝ) * Real.sqrt ρ ≤ (M : ℝ) := by
      rw [hM]
      exact Int.le_ceil _
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.le_floor]
      push_cast
      linarith [hu'.1]
    · have hfl := Int.floor_le ((10 / 7 : ℝ) * u i)
      have h' : ((⌊(10 / 7 : ℝ) * u i⌋ : ℤ) : ℝ) ≤ (M : ℝ) := by linarith [hu'.2]
      exact_mod_cast h'
  have hcard : F.card ≤ (Finset.Icc (-M) M).card :=
    Finset.card_le_card_of_injOn _ (fun i hi => hmaps i hi) hinj
  rw [Int.card_Icc] at hcard
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact Int.ceil_nonneg (by positivity)
  have hM2 : (M : ℝ) < (10 / 7 : ℝ) * Real.sqrt ρ + 1 := by
    rw [hM]
    exact Int.ceil_lt_add_one _
  have hcZ : (F.card : ℤ) ≤ 2 * M + 1 := by omega
  have hcR : (F.card : ℝ) ≤ 2 * (M : ℝ) + 1 := by exact_mod_cast hcZ
  nlinarith [Real.sqrt_nonneg ρ]

/-- Step 3: few separated points on a circle. -/
lemma circle_card (B : Finset ℝ²) (cx cy ρ : ℝ)
    (hρ : ∀ p ∈ B, (p 0 - cx) ^ 2 + (p 1 - cy) ^ 2 = ρ)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p ≠ q → 1 ≤ dist p q) :
    (B.card : ℝ) ≤ 12 * Real.sqrt ρ + 12 := by
  have hsep' : ∀ p ∈ B, ∀ q ∈ B, p ≠ q → 1 ≤ (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
    intro p hp q hq hpq
    have h := hsep p hp q hq hpq
    rw [← dist_sq_coord]
    nlinarith
  have ha := class_card (B.filter (fun p : ℝ² => |p 0 - cx| ≤ p 1 - cy))
    (fun p => p 0 - cx) (fun p => p 1 - cy) ρ
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun p hp => hρ p (Finset.mem_filter.mp hp).1)
    (fun p hp q hq hpq => by
      have h := hsep' p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 hpq
      nlinarith [h])
  have hb := class_card (B.filter (fun p : ℝ² => |p 0 - cx| ≤ -(p 1 - cy)))
    (fun p => p 0 - cx) (fun p => -(p 1 - cy)) ρ
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun p hp => by
      have h := hρ p (Finset.mem_filter.mp hp).1
      nlinarith [h])
    (fun p hp q hq hpq => by
      have h := hsep' p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 hpq
      nlinarith [h])
  have hc := class_card (B.filter (fun p : ℝ² => |p 1 - cy| ≤ p 0 - cx))
    (fun p => p 1 - cy) (fun p => p 0 - cx) ρ
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun p hp => by
      have h := hρ p (Finset.mem_filter.mp hp).1
      nlinarith [h])
    (fun p hp q hq hpq => by
      have h := hsep' p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 hpq
      nlinarith [h])
  have hd := class_card (B.filter (fun p : ℝ² => |p 1 - cy| ≤ -(p 0 - cx)))
    (fun p => p 1 - cy) (fun p => -(p 0 - cx)) ρ
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun p hp => by
      have h := hρ p (Finset.mem_filter.mp hp).1
      nlinarith [h])
    (fun p hp q hq hpq => by
      have h := hsep' p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 hpq
      nlinarith [h])
  have hcov : B ⊆ (B.filter (fun p : ℝ² => |p 0 - cx| ≤ p 1 - cy)
        ∪ B.filter (fun p : ℝ² => |p 0 - cx| ≤ -(p 1 - cy)))
      ∪ (B.filter (fun p : ℝ² => |p 1 - cy| ≤ p 0 - cx)
        ∪ B.filter (fun p : ℝ² => |p 1 - cy| ≤ -(p 0 - cx))) := by
    intro p hp
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases le_total |p 0 - cx| |p 1 - cy| with h | h
    · rcases abs_choice (p 1 - cy) with h' | h'
      · rw [h'] at h
        exact Or.inl (Or.inl ⟨hp, h⟩)
      · rw [h'] at h
        exact Or.inl (Or.inr ⟨hp, h⟩)
    · rcases abs_choice (p 0 - cx) with h' | h'
      · rw [h'] at h
        exact Or.inr (Or.inl ⟨hp, h⟩)
      · rw [h'] at h
        exact Or.inr (Or.inr ⟨hp, h⟩)
  have hle := Finset.card_le_card hcov
  have hu1 := Finset.card_union_le
    (B.filter (fun p : ℝ² => |p 0 - cx| ≤ p 1 - cy)
        ∪ B.filter (fun p : ℝ² => |p 0 - cx| ≤ -(p 1 - cy)))
    (B.filter (fun p : ℝ² => |p 1 - cy| ≤ p 0 - cx)
        ∪ B.filter (fun p : ℝ² => |p 1 - cy| ≤ -(p 0 - cx)))
  have hu2 := Finset.card_union_le
    (B.filter (fun p : ℝ² => |p 0 - cx| ≤ p 1 - cy))
    (B.filter (fun p : ℝ² => |p 0 - cx| ≤ -(p 1 - cy)))
  have hu3 := Finset.card_union_le
    (B.filter (fun p : ℝ² => |p 1 - cy| ≤ p 0 - cx))
    (B.filter (fun p : ℝ² => |p 1 - cy| ≤ -(p 0 - cx)))
  have hnat : B.card ≤ (B.filter (fun p : ℝ² => |p 0 - cx| ≤ p 1 - cy)).card
      + (B.filter (fun p : ℝ² => |p 0 - cx| ≤ -(p 1 - cy))).card
      + ((B.filter (fun p : ℝ² => |p 1 - cy| ≤ p 0 - cx)).card
      + (B.filter (fun p : ℝ² => |p 1 - cy| ≤ -(p 0 - cx))).card) := by
    omega
  have hreal : (B.card : ℝ) ≤ ((B.filter (fun p : ℝ² => |p 0 - cx| ≤ p 1 - cy)).card : ℝ)
      + ((B.filter (fun p : ℝ² => |p 0 - cx| ≤ -(p 1 - cy))).card : ℝ)
      + (((B.filter (fun p : ℝ² => |p 1 - cy| ≤ p 0 - cx)).card : ℝ)
      + ((B.filter (fun p : ℝ² => |p 1 - cy| ≤ -(p 0 - cx))).card : ℝ)) := by
    exact_mod_cast hnat
  linarith

/-- Coordinates of a grid point. -/
lemma grid_coord (i j : ℕ) :
    (!₂[(i : ℝ), (j : ℝ)] : ℝ²) 0 = (i : ℝ) ∧ (!₂[(i : ℝ), (j : ℝ)] : ℝ²) 1 = (j : ℝ) := by
  constructor <;> simp

/-- Distinct naturals differ by at least one. -/
lemma nat_sq_sub (a b : ℕ) (h : a ≠ b) : (1 : ℝ) ≤ ((a : ℝ) - (b : ℝ)) ^ 2 := by
  rcases Nat.lt_or_gt_of_ne h with h' | h'
  · have h2 : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast h'
    nlinarith
  · have h2 : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast h'
    nlinarith

/-- Step 4: a separated n-set of small diameter (part of a square grid). -/
lemma exists_compact (n : ℕ) : ∃ C ∈ separatedSets n,
    Metric.diam (C : Set ℝ²) ≤ 2 * ((Nat.sqrt n : ℝ) + 1) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = Nat.sqrt n + 1 := ⟨_, rfl⟩
  have hmR : (m : ℝ) = (Nat.sqrt n : ℝ) + 1 := by
    rw [hm]
    push_cast
    ring
  have hinj : Function.Injective
      (fun ij : ℕ × ℕ => (!₂[(ij.1 : ℝ), (ij.2 : ℝ)] : ℝ²)) := by
    intro a b hab
    have h0 : (!₂[(a.1 : ℝ), (a.2 : ℝ)] : ℝ²) 0 = (!₂[(b.1 : ℝ), (b.2 : ℝ)] : ℝ²) 0 :=
      congrArg (fun v : ℝ² => v 0) hab
    have h1 : (!₂[(a.1 : ℝ), (a.2 : ℝ)] : ℝ²) 1 = (!₂[(b.1 : ℝ), (b.2 : ℝ)] : ℝ²) 1 :=
      congrArg (fun v : ℝ² => v 1) hab
    rw [(grid_coord _ _).1, (grid_coord _ _).1] at h0
    rw [(grid_coord _ _).2, (grid_coord _ _).2] at h1
    have h0' : (a.1 : ℝ) = (b.1 : ℝ) := h0
    have h1' : (a.2 : ℝ) = (b.2 : ℝ) := h1
    exact Prod.ext (Nat.cast_injective h0') (Nat.cast_injective h1')
  have hcard : n ≤ (((Finset.range m) ×ˢ (Finset.range m)).image
      (fun ij : ℕ × ℕ => (!₂[(ij.1 : ℝ), (ij.2 : ℝ)] : ℝ²))).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.card_range, hm]
    exact (Nat.lt_succ_sqrt n).le
  obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq hcard
  have hC : ∀ p ∈ C, ∃ i j : ℕ, i < m ∧ j < m ∧ p 0 = (i : ℝ) ∧ p 1 = (j : ℝ) := by
    intro p hp
    obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp (hCsub hp)
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hij
    exact ⟨ij.1, ij.2, hij.1, hij.2, (grid_coord _ _).1, (grid_coord _ _).2⟩
  refine ⟨C, mem_separatedSets_of hCcard ?_, ?_⟩
  · intro p hp q hq hpq
    obtain ⟨i, j, hi, hj, hp0, hp1⟩ := hC p hp
    obtain ⟨i', j', hi', hj', hq0, hq1⟩ := hC q hq
    have hd : 1 ≤ dist p q ^ 2 := by
      rw [dist_sq_coord, hp0, hp1, hq0, hq1]
      by_cases hii : i = i'
      · by_cases hjj : j = j'
        · exfalso
          apply hpq
          have hz : dist p q ^ 2 = 0 := by
            rw [dist_sq_coord, hp0, hp1, hq0, hq1, hii, hjj]
            ring
          exact dist_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hz)
        · nlinarith [nat_sq_sub j j' hjj, sq_nonneg ((i : ℝ) - (i' : ℝ))]
      · nlinarith [nat_sq_sub i i' hii, sq_nonneg ((j : ℝ) - (j' : ℝ))]
    nlinarith [dist_nonneg (x := p) (y := q)]
  · have hpos : (0 : ℝ) ≤ 2 * ((Nat.sqrt n : ℝ) + 1) := by positivity
    apply Metric.diam_le_of_forall_dist_le hpos
    intro p hp q hq
    obtain ⟨i, j, hi, hj, hp0, hp1⟩ := hC p (Finset.mem_coe.mp hp)
    obtain ⟨i', j', hi', hj', hq0, hq1⟩ := hC q (Finset.mem_coe.mp hq)
    have hiR : (i : ℝ) < (m : ℝ) := by exact_mod_cast hi
    have hjR : (j : ℝ) < (m : ℝ) := by exact_mod_cast hj
    have hiR' : (i' : ℝ) < (m : ℝ) := by exact_mod_cast hi'
    have hjR' : (j' : ℝ) < (m : ℝ) := by exact_mod_cast hj'
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hi0' : (0 : ℝ) ≤ (i' : ℝ) := Nat.cast_nonneg i'
    have hj0' : (0 : ℝ) ≤ (j' : ℝ) := Nat.cast_nonneg j'
    have h1 : ((i : ℝ) - (i' : ℝ)) ^ 2 ≤ (m : ℝ) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have h2 : ((j : ℝ) - (j' : ℝ)) ^ 2 ≤ (m : ℝ) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have hd : dist p q ^ 2 ≤ (2 * ((Nat.sqrt n : ℝ) + 1)) ^ 2 := by
      rw [dist_sq_coord, hp0, hp1, hq0, hq1, ← hmR]
      nlinarith [sq_nonneg (m : ℝ)]
    exact (abs_le_of_sq_le_sq' hd hpos).2

/-- Coordinates of the centroid condition. -/
lemma sum_coord (B : Finset ℝ²) (c : ℝ²) (hsum : ∑ x ∈ B, (x - c) = 0) (i : Fin 2) :
    ∑ y ∈ B, y i = (B.card : ℝ) * c i := by
  have h := congrArg (fun z : ℝ² => (EuclideanSpace.proj (𝕜 := ℝ) i) z) hsum
  simp only [map_sum, map_sub, map_zero] at h
  have h2 : ∑ y ∈ B, (y i - c i) = 0 := h
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h2
  linarith

/-- For large n the grid competitor beats every separated n-set lying on a circle about its
centroid. -/
theorem circle_beaten : ∀ᶠ n : ℕ in atTop, ∃ C ∈ separatedSets n, ∀ B ∈ separatedSets n,
    (∃ c : ℝ², ∃ R : ℝ, (∀ x ∈ B, dist x c = R) ∧ ∑ x ∈ B, (x - c) = 0) →
    Metric.diam (C : Set ℝ²) < Metric.diam (B : Set ℝ²) := by
  filter_upwards [eventually_ge_atTop 2500] with n hn
  obtain ⟨C, hC, hCd⟩ := exists_compact n
  refine ⟨C, hC, ?_⟩
  rintro B hB ⟨c, R, hR, hsum⟩
  by_contra hlt
  have hd : Metric.diam (B : Set ℝ²) ≤ 2 * ((Nat.sqrt n : ℝ) + 1) := (not_lt.mp hlt).trans hCd
  have hd0 : 0 ≤ Metric.diam (B : Set ℝ²) := Metric.diam_nonneg
  have hBc : (B.card : ℝ) = (n : ℝ) := by rw [hB.1]
  have hnR : (2500 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN : (0 : ℝ) < (B.card : ℝ) := by rw [hBc]; linarith
  have hcoord : ∀ p ∈ B, ∀ i : Fin 2,
      (p i - c i) ^ 2 ≤ Metric.diam (B : Set ℝ²) ^ 2 := by
    intro p hp i
    have h := centroid_coord B p hp i
    rw [sum_coord B c hsum i, ← mul_sub, abs_mul, abs_of_pos hN] at h
    have h2 : |p i - c i| ≤ Metric.diam (B : Set ℝ²) := le_of_mul_le_mul_left h hN
    have h3 := abs_le.mp h2
    exact sq_le_sq' h3.1 h3.2
  have hρ : ∀ p ∈ B, (p 0 - c 0) ^ 2 + (p 1 - c 1) ^ 2 = R ^ 2 := by
    intro p hp
    rw [← dist_sq_coord, hR p hp]
  have hcard := circle_card B (c 0) (c 1) (R ^ 2) hρ
    (fun p hp q hq hpq => sep_dist hB hp hq hpq)
  obtain ⟨p, hp⟩ : B.Nonempty := by
    rw [← Finset.card_pos, hB.1]
    omega
  have hsq : Real.sqrt (R ^ 2) ≤ 2 * Metric.diam (B : Set ℝ²) := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · have e := hρ p hp
      nlinarith [hcoord p hp 0, hcoord p hp 1, sq_nonneg (Metric.diam (B : Set ℝ²))]
  have hk : 50 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hk2 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have hkR : (50 : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast hk
  have hk2R : (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk2
  have hk3 : (50 : ℝ) * (Nat.sqrt n : ℝ) ≤ (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) := by
    nlinarith
  linarith

end OMA.E103

theorem OMA.solution : OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1.H1 :=
  OMA.E103.circle_beaten
