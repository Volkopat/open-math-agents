import FormalConjectures.Wikipedia.PowerfulNumbersDensity

/-! # A variable cutoff for the powerful-number counting error

Separate cancellation of the Möbius function from the two estimates on opposite
sides of the divisor cutoff. Choosing the cutoff after the Mertens exponent is
given allows every exponent strictly below one. Explicitly, the saving is
(1-a)/(3(44-14a)). For example, a Mertens exponent of 3/5 gives a saving of
1/267 with the cutoff exponent 25/178.
-/

namespace OMA.R_PowerfulNumbersDensity_error_term_improvement_R1

open Finset Filter Asymptotics PowerfulNumbersDensity
open scoped ArithmeticFunction.Moebius

/-- Any fixed power saving in the summatory Möbius function suffices. -/
def H1 : Prop :=
  ∃ a C : ℝ, 0 ≤ a ∧ a < 1 ∧ 0 ≤ C ∧
  ∀ n : ℕ, |∑ k ∈ Ioc 0 n, (μ k : ℝ)| ≤ C * (n : ℝ) ^ a

/-- Bound the discarded divisors after truncating the Möbius convolution at x^t.
Interchange the divisor sum with the count of pairs and use cancellation on intervals. -/
def H2 : Prop :=
  let S (n : ℕ) := #{p ∈ Icc 1 n ×ˢ Icc 1 n | p.1 ^ 2 * p.2 ^ 3 ≤ n}
  let L (x t : ℝ) := ∑ d ∈ Icc 1 ⌊x ^ t⌋₊, (μ d : ℝ) * (S (⌊x⌋₊ / d ^ 6) : ℝ)
  ∀ a C t : ℝ, 0 ≤ a → a < 1 → 0 ≤ C → 0 < t → t < 1 / 6 →
    (∀ n : ℕ, |∑ k ∈ Ioc 0 n, (μ k : ℝ)| ≤ C * (n : ℝ) ^ a) →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x →
      |(Q x : ℝ) - L x t| ≤ K * x ^ (1 / 2 + (a - 3) * t)

/-- Expand the retained divisor sum. The lattice-point error gives the first power,
and the tails of the two Möbius Dirichlet sums give the other two. -/
def H3 : Prop :=
  let S (n : ℕ) := #{p ∈ Icc 1 n ×ˢ Icc 1 n | p.1 ^ 2 * p.2 ^ 3 ≤ n}
  let L (x t : ℝ) := ∑ d ∈ Icc 1 ⌊x ^ t⌋₊, (μ d : ℝ) * (S (⌊x⌋₊ / d ^ 6) : ℝ)
  ∀ a C t : ℝ, 0 ≤ a → a < 1 → 0 ≤ C → 0 < t → t < 1 / 6 →
    (∀ n : ℕ, |∑ k ∈ Ioc 0 n, (μ k : ℝ)| ≤ C * (n : ℝ) ^ a) →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x →
      |L x t - A * x ^ ((1 : ℝ) / 2) - B * x ^ ((1 : ℝ) / 3)| ≤
        K * (x ^ ((1 + t) / 7) + x ^ (1 / 2 + (a - 3) * t) + x ^ (1 / 3 + (a - 2) * t))

/-- Balance the small-divisor error and the large-divisor tail.
The third exponent differs from the second by t - 1/6. -/
theorem main : H1 → H2 → H3 → type_of% @PowerfulNumbersDensity.error_term_improvement := by
  rintro ⟨a, C, ha, ha1, hC, hM⟩ hLarge hSmall
  let t : ℝ := 5 / (44 - 14 * a)
  have hd : 0 < 44 - 14 * a := by linarith
  have ht : 0 < t := div_pos (by norm_num) hd
  have ht6 : t < 1 / 6 := by
    apply (div_lt_iff₀ hd).2
    linarith
  have hbalance : (1 : ℝ) / 2 + (a - 3) * t = (1 + t) / 7 := by
    have hprod : t * (44 - 14 * a) = 5 := div_mul_cancel₀ _ hd.ne'
    linarith only [hprod]
  let b := (1 + t) / 7
  have hthird : (1 : ℝ) / 3 + (a - 2) * t ≤ b := by
    dsimp [b]
    linarith only [hbalance, ht6]
  obtain ⟨K, hK, large⟩ := hLarge a C t ha ha1 hC ht ht6 hM
  obtain ⟨J, hJ, small⟩ := hSmall a C t ha ha1 hC ht ht6 hM
  refine ⟨1 / 6 - b, by dsimp [b]; linarith, ?_⟩
  refine IsBigO.of_bound (K + 3 * J) (eventually_atTop.2 ⟨1, fun x hx => ?_⟩)
  have hL := large x hx
  have hS := small x hx
  have hp := Real.rpow_le_rpow_of_exponent_le hx hthird
  rw [hbalance] at hL hS
  change |(Q x : ℝ) - _| ≤ K * x ^ b at hL
  have htail := mul_le_mul_of_nonneg_left hp hJ
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _),
    show (1 : ℝ) / 6 - (1 / 6 - b) = b by ring]
  obtain ⟨lower, upper⟩ := abs_le.mp hL
  obtain ⟨lower', upper'⟩ := abs_le.mp hS
  apply abs_le.mpr
  constructor <;> dsimp only [b] at * <;> linarith only [lower, upper, lower', upper', htail]

end OMA.R_PowerfulNumbersDensity_error_term_improvement_R1

