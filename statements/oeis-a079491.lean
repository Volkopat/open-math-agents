import Mathlib

/-!
# A079491: Numerator of Sum_{k=0..n} binomial(n,k)/2^(k*(k-1)/2)

Source: https://oeis.org/A079491
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Numerator of Sum_{k=0..n} binomial(n,k)/2^(k*(k-1)/2).
Conjecture: a(n) = Sum_{k=0..n} binomial(n,k) 2^(k*(n-k) + binomial(k,2)).
-/

namespace OMA.S_oeis_a079491

def ratSum (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℚ) / (2 : ℚ) ^ (k * (k - 1) / 2)

theorem main :
    ∀ n : ℕ,
      (ratSum n).num =
        (∑ k ∈ Finset.range (n + 1),
          Nat.choose n k * 2 ^ (k * (n - k) + Nat.choose k 2) : ℕ) := by
  sorry

end OMA.S_oeis_a079491
