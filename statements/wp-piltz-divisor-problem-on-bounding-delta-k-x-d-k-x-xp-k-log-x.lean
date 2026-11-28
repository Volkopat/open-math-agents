import Mathlib

/-!
# Piltz divisor problem

Source: https://en.wikipedia.org/wiki/Divisor_summatory_function#Piltz_divisor_problem
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Problem: bound `Δ_k(x) = D_k(x) - x P_k(log x)`, where `D_k(x) = ∑_{n ≤ x} d_k(n)`, `d_k(n)`
is the number of ways to write `n` as an ordered product of `k` positive integers, and `P_k`
is a polynomial of degree `k - 1`. The source records the conjecture
`Δ_k(x) = O(x^{(k-1)/(2k) + ε})` for every `ε > 0`; that is the statement, for every `k ≥ 2`.

The main term `x P_k(log x)` is the residue of `ζ(s)^k x^s / s` at `s = 1`; it is the unique
term of this shape with error `o(x)`, so stating "some polynomial `P` of degree `k - 1`
works" is equivalent and avoids writing the residue. `O(·)` is as `x → ∞`.
-/

namespace OMA.S_wp_piltz_divisor_problem_on_bounding_delta_k_x_d_k_x_xp_k_log_x

open Filter Asymptotics

/-- `d_k(n)`: ordered factorisations of `n` into `k` positive factors. -/
noncomputable def dk (k n : ℕ) : ℕ :=
  Nat.card {f : Fin k → ℕ // (∀ i, 0 < f i) ∧ ∏ i, f i = n}

/-- `D_k(x) = ∑_{1 ≤ n ≤ x} d_k(n)`. -/
noncomputable def Dk (k : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (dk k n : ℝ)

/-- The Piltz divisor conjecture. -/
theorem main :
    ∀ k : ℕ, 2 ≤ k → ∃ P : Polynomial ℝ, P.natDegree = k - 1 ∧
      ∀ ε : ℝ, 0 < ε →
        (fun x : ℝ => Dk k x - x * P.eval (Real.log x)) =O[atTop]
          (fun x : ℝ => x ^ (((k : ℝ) - 1) / (2 * k) + ε)) := by
  sorry

end OMA.S_wp_piltz_divisor_problem_on_bounding_delta_k_x_d_k_x_xp_k_log_x
