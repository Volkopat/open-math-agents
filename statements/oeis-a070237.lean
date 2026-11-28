import Mathlib

/-!
# A070237: Asymptotic density 1/420 for sign(core(k) - phi(k)) != 2*mu(k)^2 - 1

Source: https://oeis.org/A070237
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A070237: Numbers k such that the sign of core(k)-phi(k) is not equal to 2*mu(k)^2-1,
where core(k) is the squarefree part of k.

Statement:
a(n) ~ C * n with C conjectured to be 420.

Conventions:
- `core k` is the squarefree part of `k`: the product of primes dividing `k` to an odd power.
- `Int.sign ((core k : ℤ) - (Nat.totient k : ℤ))` is compared with `2 * (ArithmeticFunction.moebius k) ^ 2 - 1`.
-/

namespace OMA.S_oeis_a070237

/-- The squarefree part (core) of `k`: product of primes dividing `k` to an odd power. -/
def core (k : ℕ) : ℕ :=
  ∏ p ∈ k.primeFactors.filter (fun p => Odd (padicValNat p k)), p

/-- Membership predicate for `A070237`. -/
def IsA070237 (k : ℕ) : Prop :=
  1 ≤ k ∧
  Int.sign ((core k : ℤ) - (Nat.totient k : ℤ)) ≠
    2 * (ArithmeticFunction.moebius k) ^ 2 - 1

/-- The `n`-th term of `A070237` (0-indexed). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth IsA070237 n

theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ)) Filter.atTop (nhds 420) := by
  sorry

end OMA.S_oeis_a070237
