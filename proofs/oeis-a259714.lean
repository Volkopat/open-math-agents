import OMAStatements.S_oeis_a259714
import Mathlib

/-!
# A259714: Barker's recurrence and generating function

Since (k mod 5) is periodic with period 5, splitting the defining sum for a(n) into its first
five terms and the rest shows that the rest is exactly the defining sum for a(n−5):
a(n) = a(n−1) + 2a(n−2) + 3a(n−3) + 4a(n−4) + 0·a(n−5) + a(n−5) for n > 6. Multiplying the
series by (x+1)(x⁴+3x³+2x−1) = x⁵ + 4x⁴ + 3x³ + 2x² + x − 1, every coefficient from x⁷ on vanishes by
the recurrence, and the first seven are computed from a(1..6) = 1, 1, 3, 8, 21, 50, giving x⁶ − x.
-/

namespace A259714Proof
open OMA.S_oeis_a259714

theorem a_succ (m : ℕ) (hm : m ≠ 0) :
    a (m + 1) = ∑ j ∈ Finset.range m, ((j + 1) % 5) * a (m - j) := by
  rw [a, if_neg hm]

theorem rec (p : ℕ) (hp : 1 ≤ p) :
    a (p + 6) = a (p + 5) + 2 * a (p + 4) + 3 * a (p + 3) + 4 * a (p + 2) + a (p + 1) := by
  rw [a_succ (p + 5) (by omega), show p + 5 = 5 + p by ring, Finset.sum_range_add,
    a_succ p (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have h : ∀ i ∈ Finset.range p, (5 + i + 1) % 5 * a (5 + p - (5 + i)) = (i + 1) % 5 * a (p - i) := by
    intro i _
    rw [show 5 + p - (5 + i) = p - i by omega, show 5 + i + 1 = (i + 1) + 5 * 1 by ring,
      Nat.add_mul_mod_self_left]
  rw [Finset.sum_congr rfl h]
  simp only [show 5 + p - 0 = p + 5 by omega, show 5 + p - 1 = p + 4 by omega,
    show 5 + p - 2 = p + 3 by omega, show 5 + p - 3 = p + 2 by omega,
    show 5 + p - 4 = p + 1 by omega]
  norm_num
  ring_nf

end A259714Proof

open PowerSeries OMA.S_oeis_a259714 A259714Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a259714.main := by
  have hrec : ∀ n : ℕ, 6 < n → a n = a (n - 1) +
      2 * a (n - 2) + 3 * a (n - 3) +
      4 * a (n - 4) + a (n - 5) := by
    intro n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 6 := ⟨n - 6, by omega⟩
    rw [rec p (by omega)]
    simp only [show p + 6 - 1 = p + 5 by omega, show p + 6 - 2 = p + 4 by omega,
      show p + 6 - 3 = p + 3 by omega, show p + 6 - 4 = p + 2 by omega,
      show p + 6 - 5 = p + 1 by omega]
  refine ⟨hrec, ?_⟩
  have v1 : a 1 = 1 := by simp [a]
  have v2 : a 2 = 1 := by
    rw [a_succ 1 (by omega)]; simp [v1]
  have v3 : a 3 = 3 := by
    rw [a_succ 2 (by omega)]; simp [Finset.sum_range_succ, v1, v2]
  have v4 : a 4 = 8 := by
    rw [a_succ 3 (by omega)]; simp [Finset.sum_range_succ, v1, v2, v3]
  have v5 : a 5 = 21 := by
    rw [a_succ 4 (by omega)]; simp [Finset.sum_range_succ, v1, v2, v3, v4]
  have v6 : a 6 = 50 := by
    rw [a_succ 5 (by omega)]; simp [Finset.sum_range_succ, v1, v2, v3, v4, v5]
  have v0 : a 0 = 0 := by simp [a]
  have h4 : (C 4 : ℚ⟦X⟧) = 4 := map_ofNat C 4
  have h3 : (C 3 : ℚ⟦X⟧) = 3 := map_ofNat C 3
  have h2 : (C 2 : ℚ⟦X⟧) = 2 := map_ofNat C 2
  have hexp : PowerSeries.mk (fun n => (a n : ℚ)) *
      ((X + 1) * (X ^ 4 + 3 * X ^ 3 + 2 * X - 1)) =
      X ^ 5 * PowerSeries.mk (fun n => (a n : ℚ)) +
      C 4 * (X ^ 4 * PowerSeries.mk (fun n => (a n : ℚ))) +
      C 3 * (X ^ 3 * PowerSeries.mk (fun n => (a n : ℚ))) +
      C 2 * (X ^ 2 * PowerSeries.mk (fun n => (a n : ℚ))) +
      X ^ 1 * PowerSeries.mk (fun n => (a n : ℚ)) -
      PowerSeries.mk (fun n => (a n : ℚ)) := by
    rw [h4, h3, h2]; ring
  have hrhs : (X * (X - 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) : ℚ⟦X⟧) = X ^ 6 - X ^ 1 := by ring
  rw [hexp, hrhs]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6] <;> norm_num
  · have h := hrec n (by omega)
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_neg (by omega), if_neg (by omega), h]
    push_cast
    ring
