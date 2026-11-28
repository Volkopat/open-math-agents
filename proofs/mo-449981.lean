import OMAStatements.S_mo_449981
import Mathlib

-- Problem: mo-449981, the number of partitions of m^(n+1) - 1 into powers 1, m, ..., m^n is
-- given by the recursion R(0, q) = 1, R(n+1, q) = sum_{j < m (q+1)} R(n, j) at q = 0.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- More generally R(n, q) is the coefficient of x^((q+1) m^(n+1) - 1) in the generating
-- function. Multiplying a series A by 1 / (1 - x^K) turns the coefficient of x^N into the sum
-- of the coefficients of x^(N - t K), t <= N / K; for N = c K - 1 these are the coefficients
-- of x^((j+1) K - 1), j < c, and with K = m^(n+1), c = (q+1) m this is the recursion.

namespace MO449981

open OMA.S_mo_449981 PowerSeries

lemma geo_eq (K : ℕ) (hK : 0 < K) : geometric K = 1 + X ^ K * geometric K := by
  ext d
  rw [map_add, coeff_X_pow_mul', coeff_one]
  unfold geometric
  simp only [coeff_mk]
  by_cases hd0 : d = 0
  · subst hd0
    simp [Nat.not_le.mpr hK]
  · by_cases hdK : K ≤ d
    · rw [if_neg hd0, if_pos hdK, zero_add]
      have h : K ∣ d ↔ K ∣ d - K := by
        constructor
        · intro h
          exact Nat.dvd_sub h (dvd_refl K)
        · intro h
          have h2 := Nat.dvd_add h (dvd_refl K)
          rwa [Nat.sub_add_cancel hdK] at h2
      by_cases h1 : K ∣ d
      · rw [if_pos h1, if_pos (h.mp h1)]
      · rw [if_neg h1, if_neg (fun h2 => h1 (h.mpr h2))]
    · rw [if_neg hd0, if_neg hdK, add_zero]
      rw [if_neg]
      intro h
      exact hdK (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) h)

lemma coeff_mul_geo (A : PowerSeries ℕ) (K : ℕ) (hK : 0 < K) : ∀ N : ℕ,
    coeff N (A * geometric K) = ∑ t ∈ Finset.range (N / K + 1), coeff (N - t * K) A := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    have h1 : coeff N (A * geometric K)
        = coeff N A + (if K ≤ N then coeff (N - K) (A * geometric K) else 0) := by
      conv_lhs => rw [geo_eq K hK, mul_add, mul_one, mul_left_comm]
      rw [map_add, coeff_X_pow_mul']
    rw [h1]
    by_cases hKN : K ≤ N
    · rw [if_pos hKN, ih (N - K) (by omega)]
      have hdiv : N / K = (N - K) / K + 1 := Nat.div_eq_sub_div hK hKN
      rw [hdiv, Finset.sum_range_succ' _ ((N - K) / K + 1)]
      simp only [zero_mul, Nat.sub_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Nat.succ_mul, Nat.sub_add_eq, Nat.sub_right_comm]
    · rw [if_neg hKN, add_zero]
      have hdiv : N / K = 0 := Nat.div_eq_of_lt (by omega)
      rw [hdiv]
      simp

lemma R_eq (m : ℕ) (hm : 1 ≤ m) : ∀ n q : ℕ,
    R m n q = coeff ((q + 1) * m ^ (n + 1) - 1) (series m n) := by
  intro n
  induction n with
  | zero =>
    intro q
    simp [R, series, geometric]
  | succ n ih =>
    intro q
    have hK : 0 < m ^ (n + 1) := pow_pos (by omega) _
    obtain ⟨K, hKdef⟩ : ∃ K, K = m ^ (n + 1) := ⟨_, rfl⟩
    have hK' : 0 < K := hKdef ▸ hK
    have hc : 0 < (q + 1) * m := Nat.mul_pos (Nat.succ_pos q) hm
    obtain ⟨c, hcdef⟩ : ∃ c, c = (q + 1) * m := ⟨_, rfl⟩
    have hc' : 0 < c := hcdef ▸ hc
    have hN : (q + 1) * m ^ (n + 1 + 1) - 1 = c * K - 1 := by
      rw [hcdef, hKdef, pow_succ m (n + 1)]
      ring_nf
    have hdiv : (c * K - 1) / K = c - 1 := by
      apply Nat.div_eq_of_lt_le
      · have h1 : (c - 1) * K + K = c * K := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hc']
        omega
      · rw [Nat.sub_add_cancel hc']
        have h1 : 0 < c * K := Nat.mul_pos hc' hK'
        omega
    have hR : R m (n + 1) q = ∑ j ∈ Finset.range (m * (q + 1)), R m n j := rfl
    rw [hR, hN]
    show _ = coeff (c * K - 1) (series m n * geometric (m ^ (n + 1)))
    rw [← hKdef, coeff_mul_geo _ K hK', hdiv, Nat.sub_add_cancel hc']
    have hcm : m * (q + 1) = c := by rw [hcdef, Nat.mul_comm]
    rw [hcm, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    rw [ih (c - 1 - t), ← hKdef]
    congr 1
    have h1 : c - 1 - t + 1 = c - t := by omega
    rw [h1, Nat.sub_mul, Nat.sub_right_comm]

end MO449981

theorem OMA.solution : type_of% @OMA.S_mo_449981.main := by
  intro m n hm
  have h := MO449981.R_eq m hm n 0
  simpa using h
