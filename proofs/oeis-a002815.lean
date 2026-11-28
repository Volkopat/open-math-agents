import OMAStatements.S_oeis_a002815
import Mathlib

-- Problem: A002815: a(n) = n + Sum_{k=1..n} pi(k), where pi() = A000720.
-- Upstream: formal-conjectures statements/oeis-a002815.lean:0 (declaration OMA.S_oeis_a002815.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Multiplying by (1 - x)^2 takes second differences. Since a(n+1) - a(n) = 1 + pi(n+1), the
second difference at n + 2 is pi(n+2) - pi(n+1), which is 1 when n + 2 is prime and 0 otherwise.
The coefficients of degree 0 and 1 are a(0) = 0 and a(1) - 2 a(0) = 1. -/

namespace A002815Aux

open PowerSeries OMA.S_oeis_a002815

theorem c_succ (f : ℤ⟦X⟧) (c : ℤ) (m : ℕ) :
    coeff (m + 1) (f * (1 - C c * X)) = coeff (m + 1) f - c * coeff m f := by
  rw [mul_sub, mul_one, map_sub, mul_comm (C c) X, ← mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_succ_mul_X]
  ring

theorem c_zero (f : ℤ⟦X⟧) (c : ℤ) : coeff 0 (f * (1 - C c * X)) = coeff 0 f := by
  rw [mul_sub, mul_one, map_sub, mul_comm (C c) X, ← mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_zero_mul_X]
  ring

theorem pi_succ (n : ℕ) :
    Nat.primeCounting (n + 1) = Nat.primeCounting n + if (n + 1).Prime then 1 else 0 := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_succ]

theorem a_succ (n : ℕ) : a (n + 1) = a n + 1 + Nat.primeCounting (n + 1) := by
  unfold a
  rw [Finset.sum_Icc_succ_top (by omega)]
  ring

theorem a_zero : a 0 = 0 := by
  simp [a]

theorem a_one : a 1 = 1 := by
  rw [a_succ 0, a_zero, pi_succ 0]
  simp [Nat.primeCounting_zero, Nat.not_prime_one]

theorem gf :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X) ^ 2 =
      PowerSeries.mk (fun n => if n = 1 ∨ n.Prime then (1 : ℤ) else 0) := by
  have h1 : (C 1 : ℤ⟦X⟧) = 1 := map_one C
  have hl : PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X) ^ 2 =
      PowerSeries.mk (fun n => (a n : ℤ)) * (1 - C 1 * X) * (1 - C 1 * X) := by
    rw [h1]
    ring
  rw [hl]
  ext m
  rcases m with _ | _ | m
  · simp only [c_zero, PowerSeries.coeff_mk, a_zero]
    simp [Nat.not_prime_zero]
  · simp only [c_succ, c_zero, PowerSeries.coeff_mk, a_zero]
    simp [a_one]
  · simp only [c_succ, PowerSeries.coeff_mk]
    have e1 := a_succ (m + 1)
    have e0 := a_succ m
    have ep := pi_succ (m + 1)
    rw [e1, ep, e0]
    by_cases hp : (m + 1 + 1).Prime
    · rw [if_pos hp, if_pos (Or.inr hp)]
      push_cast
      ring
    · rw [if_neg hp, if_neg (by
        intro h
        rcases h with h | h
        · omega
        · exact hp h)]
      push_cast
      ring

end A002815Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a002815.main :=
  A002815Aux.gf
