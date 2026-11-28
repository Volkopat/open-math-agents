import OMAStatements.S_oeis_a106249
import Mathlib

-- Problem: oeis-a106249
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Proof sketch: J(2^k | 2k+1) = chi_8(2k+1)^k equals -1 when k = 1 mod 4 and 1 otherwise, so the
-- summand f is 4-periodic. With s the partial sums, mk s * (1 - X) = mk f and
-- mk f * (1 - X^4) = 1 - X + X^2 + X^3 by 4-periodicity. Since the denominator equals
-- (1 - X)(1 - X^4) and has an inverse, the generating function is mk s.

namespace OMA.Sol_a106249
open PowerSeries OMA.S_oeis_a106249

def f (k : ℕ) : ℤ := if k % 4 = 1 then -1 else 1
def s (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), f k

theorem jac (k : ℕ) : jacobiSym ((2 : ℤ) ^ k) (2 * k + 1) = f k := by
  rw [jacobiSym.pow_left, jacobiSym.at_two (by exact odd_two_mul_add_one k), ZMod.χ₈_nat_eq_if_mod_eight]
  have h2 : (2 * k + 1) % 2 = 1 := by omega
  rw [if_neg (by omega)]
  unfold f
  have : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ k = 4 * q + r := ⟨k / 4, k % 4, this, by omega⟩
  interval_cases r
  · rw [if_pos (by omega), if_neg (by omega)]; simp
  · rw [if_neg (by omega), if_pos (by omega)]
    exact Odd.neg_one_pow ⟨2 * q, by omega⟩
  · rw [if_neg (by omega), if_neg (by omega)]
    exact Even.neg_one_pow ⟨2 * q + 1, by omega⟩
  · rw [if_pos (by omega), if_neg (by omega)]; simp

theorem l1 : mk s * (1 - X) = mk f := by
  ext n
  rw [mul_sub, mul_one, map_sub]
  rcases n with _ | m
  · simp [s, coeff_zero_eq_constantCoeff]
  · rw [coeff_succ_mul_X, coeff_mk, coeff_mk, coeff_mk, s, s, Finset.sum_range_succ _ (m + 1)]
    ring

theorem l2 : mk f * (1 - X ^ 4) = num := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_mk, num]
  rcases n with _ | _ | _ | _ | m
  · simp [f]
  · simp [f, coeff_X, coeff_X_pow]
  · simp [f, coeff_X, coeff_X_pow]
  · simp [f, coeff_X, coeff_X_pow]
  · rw [if_pos (by omega), coeff_mk]
    have e : m + 1 + 1 + 1 + 1 - 4 = m := by omega
    rw [e]
    simp only [map_add, map_sub, coeff_one, coeff_X, coeff_X_pow]
    have : f (m + 1 + 1 + 1 + 1) = f m := by unfold f; congr 1; simp only [eq_iff_iff]; omega
    rw [this]
    simp

theorem main_proof : ∀ n : ℕ,
    a n = ∑ k ∈ Finset.range (n + 1), jacobiSym ((2 : ℤ) ^ k) (2 * k + 1) := by
  intro n
  have hden : den = (1 - X) * (1 - X ^ 4) := by unfold den; ring
  have hgf : gf = mk s := by
    have hu : den * invOfUnit den 1 = 1 := mul_invOfUnit den 1 (by simp [den])
    have hn : num = mk s * den := by rw [hden, ← mul_assoc, l1, l2]
    calc gf = mk s * (den * invOfUnit den 1) := by rw [gf, hn, mul_assoc]
      _ = mk s := by rw [hu, mul_one]
  rw [a, hgf, coeff_mk, s]
  exact Finset.sum_congr rfl (fun k _ => (jac k).symm)
end OMA.Sol_a106249

theorem OMA.solution : type_of% @OMA.S_oeis_a106249.main := OMA.Sol_a106249.main_proof
