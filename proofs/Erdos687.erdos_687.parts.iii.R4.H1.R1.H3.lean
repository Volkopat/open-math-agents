import OMAReductions.R_Erdos687_erdos_687_parts_iii_R4_H1_R1
import Mathlib

-- Step Erdos687.erdos_687.parts.iii.R4.H1.R1.H3: hypothesis H3 of reduction Erdos687.erdos_687.parts.iii.R4.H1.R1
-- Credit: @sebastianbachmaier
-- H3 := ∀ᶠ n : ℕ in atTop,   ((fun n : ℕ => ⌊(n : ℝ) ^ (33/50 : ℝ)⌋₊ / 2) n : ℝ)^2/4 < (fun (f : ℕ → ℝ) (a h : ℕ) =>   f (a + 2*h) - 2 * f (a+h) + f a) (fun n : ℕ => ∑ k ∈ Finset.range n,   (ArithmeticFunction.vonMangoldt k : ℝ) * ((n : ℝ) - k)) (n+1) ((fun n : ℕ => ⌊(n : ℝ) ^ (33/50 : ℝ)⌋₊ / 2) n) →   ∃ p : ℕ, p.Prime ∧ n < p ∧ (p-n)^3 ≤ n^2

open Filter

namespace OMAH3aux

-- First differences of the weighted von Mangoldt sum lie between d * P a and d * P (a + d),
-- where P m is the plain von Mangoldt sum below m.
lemma diff_bounds (a d : ℕ) :
    (d : ℝ) * ∑ k ∈ Finset.range a, (ArithmeticFunction.vonMangoldt k : ℝ) ≤
      (∑ k ∈ Finset.range (a + d),
          (ArithmeticFunction.vonMangoldt k : ℝ) * (((a + d : ℕ) : ℝ) - k))
        - ∑ k ∈ Finset.range a, (ArithmeticFunction.vonMangoldt k : ℝ) * ((a : ℝ) - k) ∧
    (∑ k ∈ Finset.range (a + d),
          (ArithmeticFunction.vonMangoldt k : ℝ) * (((a + d : ℕ) : ℝ) - k))
        - ∑ k ∈ Finset.range a, (ArithmeticFunction.vonMangoldt k : ℝ) * ((a : ℝ) - k) ≤
      (d : ℝ) * ∑ k ∈ Finset.range (a + d), (ArithmeticFunction.vonMangoldt k : ℝ) := by
  have e1 := Finset.sum_range_add
    (fun k : ℕ => (ArithmeticFunction.vonMangoldt k : ℝ) * (((a + d : ℕ) : ℝ) - (k : ℝ))) a d
  have e3 := Finset.sum_range_add (fun k : ℕ => (ArithmeticFunction.vonMangoldt k : ℝ)) a d
  have e2 : ∑ k ∈ Finset.range a,
        (ArithmeticFunction.vonMangoldt k : ℝ) * (((a + d : ℕ) : ℝ) - (k : ℝ))
      = ∑ k ∈ Finset.range a, (ArithmeticFunction.vonMangoldt k : ℝ) * ((a : ℝ) - k)
        + (d : ℝ) * ∑ k ∈ Finset.range a, (ArithmeticFunction.vonMangoldt k : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    push_cast
    ring
  have e4 : 0 ≤ ∑ j ∈ Finset.range d,
      (ArithmeticFunction.vonMangoldt (a + j) : ℝ) * (((a + d : ℕ) : ℝ) - ((a + j : ℕ) : ℝ)) := by
    refine Finset.sum_nonneg (fun j hj => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ?_)
    have hjd : (j : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Finset.mem_range.mp hj).le
    push_cast
    linarith
  have e5 : ∑ j ∈ Finset.range d,
      (ArithmeticFunction.vonMangoldt (a + j) : ℝ) * (((a + d : ℕ) : ℝ) - ((a + j : ℕ) : ℝ))
      ≤ (d : ℝ) * ∑ j ∈ Finset.range d, (ArithmeticFunction.vonMangoldt (a + j) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have h0 : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt (a + j) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hm := mul_nonneg h0 hj0
    push_cast
    nlinarith [hm]
  have e6 : (d : ℝ) * ∑ k ∈ Finset.range (a + d), (ArithmeticFunction.vonMangoldt k : ℝ)
      = (d : ℝ) * (∑ k ∈ Finset.range a, (ArithmeticFunction.vonMangoldt k : ℝ)
        + ∑ j ∈ Finset.range d, (ArithmeticFunction.vonMangoldt (a + j) : ℝ)) := by
    rw [e3]
  constructor
  · linarith
  · linarith

-- If there is no prime in (n, n + 2h], the second difference is at most h times the
-- prime power mass below n + 2h.
lemma second_diff_le (n h : ℕ) (hn1 : 1 ≤ n)
    (hnp : ∀ p : ℕ, p.Prime → n < p → n + 2 * h < p) :
    (∑ k ∈ Finset.range (n + 1 + 2 * h),
        (ArithmeticFunction.vonMangoldt k : ℝ) * (((n + 1 + 2 * h : ℕ) : ℝ) - k))
      - 2 * (∑ k ∈ Finset.range (n + 1 + h),
        (ArithmeticFunction.vonMangoldt k : ℝ) * (((n + 1 + h : ℕ) : ℝ) - k))
      + (∑ k ∈ Finset.range (n + 1),
        (ArithmeticFunction.vonMangoldt k : ℝ) * (((n + 1 : ℕ) : ℝ) - k))
    ≤ (h : ℝ) * (2 * Real.sqrt ((n + 2 * h : ℕ) : ℝ) * Real.log ((n + 2 * h : ℕ) : ℝ)) := by
  have hA := (diff_bounds (n + 1 + h) h).2
  have hB := (diff_bounds (n + 1) h).1
  have e : n + 1 + 2 * h = n + 1 + h + h := by omega
  rw [e]
  have hS : ∑ k ∈ Finset.range (n + 1 + h + h), (ArithmeticFunction.vonMangoldt k : ℝ)
      - ∑ k ∈ Finset.range (n + 1), (ArithmeticFunction.vonMangoldt k : ℝ)
      ≤ 2 * Real.sqrt ((n + 2 * h : ℕ) : ℝ) * Real.log ((n + 2 * h : ℕ) : ℝ) := by
    have hI := Finset.sum_Ico_eq_sub (fun k : ℕ => (ArithmeticFunction.vonMangoldt k : ℝ))
      (by omega : n + 1 ≤ n + 1 + h + h)
    have key := Chebyshev.psi_sub_theta_eq_sum_not_prime ((n + 2 * h : ℕ) : ℝ)
    rw [Nat.floor_natCast] at key
    have h1N : (1 : ℝ) ≤ ((n + 2 * h : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ n + 2 * h)
    have hle := Chebyshev.psi_sub_theta_le (x := ((n + 2 * h : ℕ) : ℝ)) h1N
    rw [key] at hle
    have hsub : ∑ k ∈ Finset.Ico (n + 1) (n + 1 + h + h), (ArithmeticFunction.vonMangoldt k : ℝ)
        ≤ 2 * Real.sqrt ((n + 2 * h : ℕ) : ℝ) * Real.log ((n + 2 * h : ℕ) : ℝ) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hle
      · intro k hk
        rw [Finset.mem_Ico] at hk
        rw [Finset.mem_filter, Finset.mem_Ioc]
        refine ⟨⟨by omega, by omega⟩, fun hp => ?_⟩
        have hlt := hnp k hp (by omega)
        omega
      · intro _ _ _
        exact ArithmeticFunction.vonMangoldt_nonneg
    linarith
  have hH0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hm := mul_le_mul_of_nonneg_left hS hH0
  linarith

-- Size estimate: 2 * sqrt N * log N ≤ 40 * x ^ (3/5) when 1 ≤ N ≤ 2 x.
lemma analytic (x N : ℝ) (hN1 : 1 ≤ N) (hN2 : N ≤ 2 * x) :
    2 * Real.sqrt N * Real.log N ≤ 40 * x ^ (3/5 : ℝ) := by
  have hN0 : 0 < N := by linarith
  have hx0 : 0 ≤ x := by linarith
  have h1 : Real.sqrt N = N ^ (1/2 : ℝ) := Real.sqrt_eq_rpow N
  have h2 : Real.log N ≤ N ^ (1/10 : ℝ) / (1/10 : ℝ) :=
    Real.log_le_rpow_div hN0.le (by norm_num)
  have h3 : N ^ (1/2 : ℝ) * N ^ (1/10 : ℝ) = N ^ (3/5 : ℝ) := by
    rw [← Real.rpow_add hN0]
    norm_num
  have h4 : N ^ (3/5 : ℝ) ≤ (2 * x) ^ (3/5 : ℝ) :=
    Real.rpow_le_rpow hN0.le hN2 (by norm_num)
  have h5 : (2 * x) ^ (3/5 : ℝ) = (2 : ℝ) ^ (3/5 : ℝ) * x ^ (3/5 : ℝ) :=
    Real.mul_rpow (by norm_num) hx0
  have h6 : (2 : ℝ) ^ (3/5 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (3/5 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hu0 : 0 ≤ x ^ (3/5 : ℝ) := Real.rpow_nonneg hx0 _
  have hs0 : 0 ≤ N ^ (1/2 : ℝ) := Real.rpow_nonneg hN0.le _
  have h7 : (2 : ℝ) ^ (3/5 : ℝ) * x ^ (3/5 : ℝ) ≤ 2 * x ^ (3/5 : ℝ) :=
    mul_le_mul_of_nonneg_right h6 hu0
  have h8 : 2 * N ^ (1/2 : ℝ) * Real.log N
      ≤ 2 * N ^ (1/2 : ℝ) * (N ^ (1/10 : ℝ) / (1/10 : ℝ)) :=
    mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num) hs0)
  have h9 : 2 * N ^ (1/2 : ℝ) * (N ^ (1/10 : ℝ) / (1/10 : ℝ))
      = 20 * (N ^ (1/2 : ℝ) * N ^ (1/10 : ℝ)) := by ring
  rw [h1]
  rw [h3] at h9
  rw [h5] at h4
  linarith

-- The step with the floor generalised to F.
lemma core (n F h : ℕ) (hh : h = F / 2)
    (hF1 : (F : ℝ) ≤ (n : ℝ) ^ (33/50 : ℝ)) (hF2 : (n : ℝ) ^ (33/50 : ℝ) < (F : ℝ) + 1)
    (hg : 322 ≤ (n : ℝ) ^ (3/50 : ℝ)) :
    (h : ℝ)^2/4 <
      (∑ k ∈ Finset.range (n + 1 + 2 * h),
          (ArithmeticFunction.vonMangoldt k : ℝ) * (((n + 1 + 2 * h : ℕ) : ℝ) - k))
        - 2 * (∑ k ∈ Finset.range (n + 1 + h),
          (ArithmeticFunction.vonMangoldt k : ℝ) * (((n + 1 + h : ℕ) : ℝ) - k))
        + (∑ k ∈ Finset.range (n + 1),
          (ArithmeticFunction.vonMangoldt k : ℝ) * (((n + 1 : ℕ) : ℝ) - k)) →
    ∃ p : ℕ, p.Prime ∧ n < p ∧ (p - n)^3 ≤ n^2 := by
  intro hD
  have hn1 : 1 ≤ n := by
    by_contra hc
    have h0 : n = 0 := by omega
    rw [h0, Nat.cast_zero, Real.zero_rpow (by norm_num : (3/50 : ℝ) ≠ 0)] at hg
    norm_num at hg
  have hx1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hx0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h2a : 2 * h ≤ F := by omega
  have h2b : F ≤ 2 * h + 1 := by omega
  have h2aR : 2 * (h : ℝ) ≤ (F : ℝ) := by exact_mod_cast h2a
  have h2bR : (F : ℝ) ≤ 2 * (h : ℝ) + 1 := by exact_mod_cast h2b
  have hcube : F ^ 3 ≤ n ^ 2 := by
    have c1 : (F : ℝ) ^ 3 ≤ ((n : ℝ) ^ (33/50 : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg F) hF1 3
    have c2 : ((n : ℝ) ^ (33/50 : ℝ)) ^ 3 = (n : ℝ) ^ (99/50 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    have c3 : (n : ℝ) ^ (99/50 : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have c4 : (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ 2 := Real.rpow_two _
    have c5 : (F : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 :=
      calc (F : ℝ) ^ 3 ≤ ((n : ℝ) ^ (33/50 : ℝ)) ^ 3 := c1
        _ = (n : ℝ) ^ (99/50 : ℝ) := c2
        _ ≤ (n : ℝ) ^ (2 : ℝ) := c3
        _ = (n : ℝ) ^ 2 := c4
    exact_mod_cast c5
  by_cases hex : ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ n + 2 * h
  · obtain ⟨p, hp, hnp, hpl⟩ := hex
    refine ⟨p, hp, hnp, ?_⟩
    have hpn : p - n ≤ F := by omega
    exact le_trans (Nat.pow_le_pow_left hpn 3) hcube
  · exfalso
    have hnp : ∀ p : ℕ, p.Prime → n < p → n + 2 * h < p := by
      intro p hp hlt
      by_contra hc
      exact hex ⟨p, hp, hlt, by omega⟩
    have hS := second_diff_le n h hn1 hnp
    have hN1 : (1 : ℝ) ≤ ((n + 2 * h : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ n + 2 * h)
    have hrx : (n : ℝ) ^ (33/50 : ℝ) ≤ (n : ℝ) := by
      calc (n : ℝ) ^ (33/50 : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
        _ = (n : ℝ) := Real.rpow_one _
    have hN2 : ((n + 2 * h : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
      push_cast
      linarith
    have hA := analytic (n : ℝ) ((n + 2 * h : ℕ) : ℝ) hN1 hN2
    have hsplit : (n : ℝ) ^ (33/50 : ℝ) = (n : ℝ) ^ (3/5 : ℝ) * (n : ℝ) ^ (3/50 : ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
    have hu1 : 1 ≤ (n : ℝ) ^ (3/5 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
    have hu0 : 0 ≤ (n : ℝ) ^ (3/5 : ℝ) := by linarith
    have hH0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
    have hr : 322 * (n : ℝ) ^ (3/5 : ℝ) ≤ (n : ℝ) ^ (33/50 : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hg hu0
      rw [hsplit]
      linarith
    have hH : 160 * (n : ℝ) ^ (3/5 : ℝ) ≤ (h : ℝ) := by linarith
    have hlt := lt_of_lt_of_le hD hS
    have h7 := mul_le_mul_of_nonneg_left hA hH0
    have h8 := mul_le_mul_of_nonneg_left hH hH0
    nlinarith [hlt, h7, h8]

end OMAH3aux

theorem OMA.solution : OMA.R_Erdos687_erdos_687_parts_iii_R4_H1_R1.H3 := by
  unfold OMA.R_Erdos687_erdos_687_parts_iii_R4_H1_R1.H3
  have ht := ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3/50)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (322 : ℝ))
  filter_upwards [ht] with n hg
  change 322 ≤ (n : ℝ) ^ (3/50 : ℝ) at hg
  exact OMAH3aux.core n ⌊(n : ℝ) ^ (33/50 : ℝ)⌋₊ (⌊(n : ℝ) ^ (33/50 : ℝ)⌋₊ / 2) rfl
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (Nat.lt_floor_add_one _) hg
