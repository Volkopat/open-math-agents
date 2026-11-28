import Mathlib

/-!
# A002111: Glaisher's G numbers as unsigned numerators of B(2n+1, 1/3)

Source: https://oeis.org/A002111
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A002111: Glaisher's G numbers.

Statement:
From the OEIS entry: a(n) = (-1)^(n+1)*3^(2*n+1)*B(2*n+1,1/3), where B(n,x) denotes
the n-th Bernoulli polynomial. Conjecturally, a(n) = the unsigned numerator of B(2*n+1,1/3).

Conventions:
- `bernoulliPoly n x` is the `n`-th Bernoulli polynomial `∑ k ∈ range (n+1), C(n, k) * B_k * x^(n-k)`
  evaluated at `x : ℚ`.
- The conjecture is stated for `n >= 1` (since `B(1, 1/3) = -1/6` gives `a(0) = 1/2` whereas
  `a(1) = 1, a(2) = 5, a(3) = 49, ...`).
-/

namespace OMA.S_oeis_a002111

/-- The `n`-th Bernoulli polynomial evaluated at `x : ℚ`. -/
def bernoulliPoly (n : ℕ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℚ) * bernoulli k * x ^ (n - k)

/-- Glaisher's G number `a(n) = (-1)^(n+1) * 3^(2n+1) * B(2n+1, 1/3)`. -/
def glaisherG (n : ℕ) : ℚ :=
  (-1 : ℚ) ^ (n + 1) * (3 : ℚ) ^ (2 * n + 1) * bernoulliPoly (2 * n + 1) (1 / 3)

theorem main :
    ∀ n : ℕ, 1 ≤ n → glaisherG n = ((bernoulliPoly (2 * n + 1) (1 / 3)).num.natAbs : ℚ) := by
  sorry

end OMA.S_oeis_a002111
