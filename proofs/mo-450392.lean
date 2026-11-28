import OMAStatements.S_mo_450392
import Mathlib

open Finset
-- Problem: mo-450392, the floor of sqrt(n^2) + sqrt(n^2+1) + ... + sqrt((n+1)^2) is the
-- hexagonal number H(n+1) = 2n^2 + 3n + 1.
-- Credit: @ivillar, original proof PR #13206.
-- Square-root comparisons shortened with Real.le_sqrt_of_sq_le and Real.sqrt_le_iff.
--
-- Lower bound: by concavity sqrt(n^2 + h) >= n + h / (2n + 1) for 0 <= h <= 2n + 1, and these
-- chords sum to exactly 2n^2 + 3n + 1. Upper bound: sqrt(n^2 + h) <= n + h / (2n) for
-- h <= 2n, the last term is n + 1, and the total is 2n^2 + 3n + 3/2 < 2n^2 + 3n + 2.

namespace MO450392

open OMA.S_mo_450392

lemma gauss (m : ℕ) : (∑ h ∈ range (m + 1), (h : ℝ)) = (m : ℝ) * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

lemma lower_term (x y : ℝ) (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy : y ≤ 2 * x + 1) :
    x + y / (2 * x + 1) ≤ Real.sqrt (x ^ 2 + y) := by
  have hd : (0 : ℝ) < 2 * x + 1 := by linarith
  have hz0 : 0 ≤ y / (2 * x + 1) := div_nonneg hy0 hd.le
  have hz1 : y / (2 * x + 1) ≤ 1 := (div_le_one hd).mpr hy
  have hyz : y = y / (2 * x + 1) * (2 * x + 1) := by field_simp
  apply Real.le_sqrt_of_sq_le
  nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz1), hyz]

lemma upper_term (x y : ℝ) (hx : 0 < x) (hy0 : 0 ≤ y) :
    Real.sqrt (x ^ 2 + y) ≤ x + y / (2 * x) := by
  have hyw : y = y / (2 * x) * (2 * x) := by field_simp
  apply Real.sqrt_le_iff.mpr
  exact ⟨by positivity, by nlinarith [sq_nonneg (y / (2 * x)), hyw]⟩

theorem main_proof : ∀ n : ℕ, 1 ≤ n →
    ⌊∑ h ∈ range (2 * n + 2), Real.sqrt ((n : ℝ) ^ 2 + (h : ℝ))⌋₊
      = hexagonal (n + 1) := by
  intro n hn
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hhex : hexagonal (n + 1) = 2 * n ^ 2 + 3 * n + 1 := by
    unfold hexagonal
    have h : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    rw [h]
    ring
  have hlow : 2 * (n : ℝ) ^ 2 + 3 * n + 1
      ≤ ∑ h ∈ range (2 * n + 2), Real.sqrt ((n : ℝ) ^ 2 + (h : ℝ)) := by
    have h1 : ∑ h ∈ range (2 * n + 2), ((n : ℝ) + (h : ℝ) / (2 * (n : ℝ) + 1))
        ≤ ∑ h ∈ range (2 * n + 2), Real.sqrt ((n : ℝ) ^ 2 + (h : ℝ)) := by
      apply sum_le_sum
      intro h hh
      rw [mem_range] at hh
      apply lower_term _ _ (by linarith) (Nat.cast_nonneg h)
      have h3 : (h : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : h ≤ 2 * n + 1)
      push_cast at h3
      linarith
    have hg : ∑ h ∈ range (2 * n + 2), (h : ℝ)
        = ((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) + 1) / 2 := gauss (2 * n + 1)
    have h2 : ∑ h ∈ range (2 * n + 2), ((n : ℝ) + (h : ℝ) / (2 * (n : ℝ) + 1))
        = 2 * (n : ℝ) ^ 2 + 3 * n + 1 := by
      rw [sum_add_distrib, ← sum_div, sum_const, card_range, hg,
        nsmul_eq_mul]
      have hd : (2 * (n : ℝ) + 1) ≠ 0 := by linarith
      push_cast
      field_simp
      ring
    linarith
  have hup : ∑ h ∈ range (2 * n + 2), Real.sqrt ((n : ℝ) ^ 2 + (h : ℝ))
      < 2 * (n : ℝ) ^ 2 + 3 * n + 1 + 1 := by
    rw [sum_range_succ]
    have hlast : Real.sqrt ((n : ℝ) ^ 2 + ((2 * n + 1 : ℕ) : ℝ)) = n + 1 := by
      have h : (n : ℝ) ^ 2 + ((2 * n + 1 : ℕ) : ℝ) = ((n : ℝ) + 1) ^ 2 := by
        push_cast
        ring
      rw [h, Real.sqrt_sq (by linarith)]
    have h1 : ∑ h ∈ range (2 * n + 1), Real.sqrt ((n : ℝ) ^ 2 + (h : ℝ))
        ≤ ∑ h ∈ range (2 * n + 1), ((n : ℝ) + (h : ℝ) / (2 * (n : ℝ))) := by
      apply sum_le_sum
      intro h _
      exact upper_term _ _ (by linarith) (Nat.cast_nonneg h)
    have h2 : ∑ h ∈ range (2 * n + 1), ((n : ℝ) + (h : ℝ) / (2 * (n : ℝ)))
        = 2 * (n : ℝ) ^ 2 + 2 * n + 1 / 2 := by
      rw [sum_add_distrib, ← sum_div, sum_const, card_range,
        gauss (2 * n), nsmul_eq_mul]
      have hd : (n : ℝ) ≠ 0 := by linarith
      push_cast
      field_simp
      ring
    rw [hlast]
    linarith
  have hnonneg : 0 ≤ ∑ h ∈ range (2 * n + 2), Real.sqrt ((n : ℝ) ^ 2 + (h : ℝ)) :=
    sum_nonneg fun h _ => Real.sqrt_nonneg _
  rw [hhex, Nat.floor_eq_iff hnonneg]
  push_cast
  exact ⟨hlow, hup⟩

end MO450392

theorem OMA.solution : type_of% @OMA.S_mo_450392.main := MO450392.main_proof
