import OMAStatements.S_oeis_a192759
import Mathlib

-- Original proof by @justusklocke-cloud.

namespace A192759
open Polynomial

/-- The constant added in step n of the recursion for p. -/
def cc (n : ℕ) : ℤ := ((((n + 1) + 5) / 5 : ℕ) : ℤ)

/-- The pair (constant coefficient, coefficient of X) of the reduction of p n. -/
def uv : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((uv n).2 + cc n, (uv n).1 + (uv n).2)

lemma cc_shift (n : ℕ) : cc (n + 5) = cc n + 1 := by
  unfold cc
  omega

lemma cc_succ (n : ℕ) : cc (n + 1) = cc n + (if (n + 2) % 5 = 0 then 1 else 0) := by
  unfold cc
  split_ifs <;> omega

lemma p_eq (n : ℕ) : ∃ q : ℤ[X], OMA.S_oeis_a192759.p n
    = (X ^ 2 - X - 1) * q + (C (uv n).1 + C (uv n).2 * X) := by
  induction n with
  | zero => exact ⟨0, by simp [OMA.S_oeis_a192759.p, uv]⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨X * q + C (uv n).2, ?_⟩
    rw [OMA.S_oeis_a192759.p, hq, uv, cc]
    simp only [map_add]
    ring

lemma monicQ : (X ^ 2 - X - 1 : ℤ[X]).Monic := by
  have h : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + C 1) := by simp only [map_one]; ring
  rw [h]
  apply monic_X_pow_sub
  rw [degree_X_add_C]
  decide

lemma mod_coeff (f q : ℤ[X]) (u v : ℤ) (h : f = (X ^ 2 - X - 1) * q + (C u + C v * X)) :
    (f %ₘ (X ^ 2 - X - 1)).coeff 1 = v := by
  have hdeg : (C u + C v * X : ℤ[X]).degree < (X ^ 2 - X - 1 : ℤ[X]).degree := by
    have h1 : (C u + C v * X : ℤ[X]).degree ≤ 1 := by compute_degree
    have h2 : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by compute_degree!
    rw [h2]
    exact lt_of_le_of_lt h1 (by decide)
  have := (div_modByMonic_unique (f := f) q (C u + C v * X) monicQ ⟨by rw [h]; ring, hdeg⟩).2
  rw [this, coeff_add, coeff_C_mul, coeff_X_one, coeff_C]
  simp

lemma a_eq (n : ℕ) : OMA.S_oeis_a192759.a n = (uv n).2 := by
  obtain ⟨q, hq⟩ := p_eq n
  exact mod_coeff _ q _ _ hq

lemma inv (n : ℕ) : (uv n).1 = OMA.S_oeis_a192759.A124502 (n + 1) ∧
    (uv n).2 = ∑ k ∈ Finset.Icc 1 n, OMA.S_oeis_a192759.A124502 k ∧
    OMA.S_oeis_a192759.A124502 (n + 2)
      = (∑ k ∈ Finset.Icc 1 n, OMA.S_oeis_a192759.A124502 k) + cc n := by
  induction n with
  | zero => simp [uv, OMA.S_oeis_a192759.A124502, cc]
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hs : ∑ k ∈ Finset.Icc 1 (n + 1), OMA.S_oeis_a192759.A124502 k
        = (∑ k ∈ Finset.Icc 1 n, OMA.S_oeis_a192759.A124502 k)
          + OMA.S_oeis_a192759.A124502 (n + 1) :=
      Finset.sum_Icc_succ_top (by omega) _
    have hA : OMA.S_oeis_a192759.A124502 (n + 3) = OMA.S_oeis_a192759.A124502 (n + 2)
        + OMA.S_oeis_a192759.A124502 (n + 1) + (if (n + 2) % 5 = 0 then 1 else 0) := by
      rw [OMA.S_oeis_a192759.A124502]
    refine ⟨?_, ?_, ?_⟩
    · rw [uv]; simp only; rw [h2, h3]
    · rw [uv]; simp only; rw [h1, h2, hs]; ring
    · rw [hA, hs, cc_succ, h3]; ring

end A192759

open PowerSeries A192759 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192759.main := by
  rw [show OMA.S_oeis_a192759.a = fun n => (uv n).2 from funext a_eq]
  refine ⟨?_, fun n => (A192759.inv n).2.1⟩
  have hD : (((X : PowerSeries ℤ) ^ 2 + X - 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (X - 1) ^ 2)
      = C (-1) * X ^ 0 + C 2 * X ^ 1 + C (-1) * X ^ 3 + C 1 * X ^ 5 + C (-2) * X ^ 6
        + C 1 * X ^ 8 := by
    simp only [map_neg, map_ofNat, map_one]; ring
  have hN : -(X : PowerSeries ℤ) = C (-1) * X ^ 1 := by simp
  rw [hD, hN]
  ext n
  simp only [mul_add, map_add, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C, coeff_mk, coeff_C]
  by_cases hn : n < 8
  · interval_cases n <;> norm_num [uv, cc]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    simp [uv]
    rw [cc_shift k, cc_shift (k + 1)]
    ring
