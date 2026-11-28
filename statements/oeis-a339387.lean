import Mathlib.Data.Nat.Squarefree

/-!
# Equality of two modular divisor sums forces squarefreeness

Source: https://oeis.org/A339387 and https://oeis.org/A339384
Credit: @anmolspace

Sebastian Karlsson compared two sums over the same quotients of the least
common multiple by the greatest common divisor. In A339387 the modulus is
the summation index. In A339384 it is the fixed sequence index.
-/

namespace OMA.S_oeis_a339387

/-- The common integer whose residues occur in both sequences. -/
def quotient (n k : ℕ) : ℕ := n.lcm k / n.gcd k

/-- A339387 uses the modulus k for the kth term. -/
def varying (n : ℕ) : ℕ := ∑ k ∈ Finset.Ico 1 (n + 1), quotient n k % k

/-- A339384 uses the fixed modulus n throughout. -/
def fixed (n : ℕ) : ℕ := ∑ k ∈ Finset.Ico 1 (n + 1), quotient n k % n

theorem main : ∀ n : ℕ, 0 < n → varying n = fixed n → Squarefree n := by
  sorry

end OMA.S_oeis_a339387
