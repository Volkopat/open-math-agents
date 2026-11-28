import Mathlib

/-!
# OEIS A352305: 188 is the last even number that is a sum of two distinct primes in exactly 5 ways

Source: https://oeis.org/A352305 (EXAMPLE: "it is conjectured that 188 is the last term of
A080854"); A080854 lists the numbers that are the sum of two distinct primes in exactly five ways.
Credit: @LEGZM

188 = 7 + 181 = 31 + 157 = 37 + 151 = 61 + 127 = 79 + 109. The conjecture: 188 is the last term
of A080854, i.e. it has exactly five such representations and no larger number does.
-/

namespace OMA.S_oeis_a352305

/-- The number of ways to write n = p + q with primes p < q (unordered, distinct). -/
def numWays (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun p => p.Prime ∧ (n - p).Prime ∧ p < n - p)).card

theorem main : numWays 188 = 5 ∧ ∀ n : ℕ, 188 < n → numWays n ≠ 5 := by
  sorry

end OMA.S_oeis_a352305
