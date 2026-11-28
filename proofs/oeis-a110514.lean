import OMAStatements.S_oeis_a110514
import Mathlib

-- The original proof is by @ivillar, PR #13428.
-- Idea: J(m) = Jacobi(2^m, 2m+1) = χ₈(2m+1)^m (second supplementary law) is 4-periodic:
-- 1, -1, 1, 1, ...; b(n) = Σ J(n-2k) satisfies b(n+2) = b(n) + J(n+2), hence
-- b(n) - b(n-2) - b(n-4) + b(n-6) = J(n) - J(n-4) = 0, which is the denominator of the g.f.

namespace OMAA110514Helpers

open PowerSeries OMA.S_oeis_a110514

def J (m : ℕ) : ℤ := jacobiSym ((2 : ℤ) ^ m) (2 * m + 1)

theorem Jval (m : ℕ) : J m = if m % 4 = 1 then -1 else 1 := by
  unfold J
  rw [jacobiSym.pow_left, jacobiSym.at_two (by exact ⟨m, by omega⟩), ZMod.χ₈_nat_eq_if_mod_eight]
  split_ifs <;> simp (disch := omega) [neg_one_pow_eq_ite, Nat.even_iff] <;> omega

theorem Jper (m : ℕ) : J (m + 4) = J m := by
  rw [Jval, Jval, show (m + 4) % 4 = m % 4 by omega]

def b (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n / 2 + 1), J (n - 2 * k)

theorem b_step (n : ℕ) : b (n + 2) = J (n + 2) + b n := by
  unfold b
  rw [show (n + 2) / 2 + 1 = n / 2 + 1 + 1 by omega, Finset.sum_range_succ']
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  omega

theorem b_rec (n : ℕ) : b (n + 6) - b (n + 4) - b (n + 2) + b n = 0 := by
  rw [show n + 6 = n + 4 + 2 from rfl, b_step (n + 4), b_step n,
    show J (n + 4 + 2) = J (n + 2) from Jper (n + 2)]
  ring

theorem key : mk (fun n => (b n : ℚ)) * (1 - X ^ 2 - X ^ 4 + X ^ 6) = 1 - X + X ^ 2 + X ^ 3 := by
  set A := mk (fun n => (b n : ℚ))
  have e1 : A * (1 - X ^ 2 - X ^ 4 + X ^ 6) = A - X ^ 2 * A - X ^ 4 * A + X ^ 6 * A := by ring
  have e2 : (1 - X + X ^ 2 + X ^ 3 : ℚ⟦X⟧) = X ^ 0 - X ^ 1 + X ^ 2 + X ^ 3 := by ring
  rw [e1, e2]
  ext n
  simp only [A, map_add, map_sub, coeff_mk, coeff_X_pow_mul', coeff_X_pow]
  by_cases hn : n ≤ 5
  · interval_cases n <;> norm_num [b, Jval, Finset.sum_range_succ]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    have h : (b (m + 6) : ℚ) - b (m + 4) - b (m + 2) + b m = 0 := by exact_mod_cast b_rec m
    simpa (disch := omega) [Nat.add_sub_assoc] using h

end OMAA110514Helpers

open PowerSeries OMA.S_oeis_a110514 OMAA110514Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a110514.main := by
  intro n
  have hG : G = mk (fun n => (b n : ℚ)) := by
    rw [G, eq_comm, PowerSeries.eq_mul_inv_iff_mul_eq (by simp), key]
  rw [a, hG, coeff_mk, b]
  push_cast
  rfl

