import Mathlib

/-!
# The divisor-sum conjecture for OEIS A387724

Antti Karttunen asks whether 6 is the only nondeficient member and whether
every other member belongs to A337382. That sequence consists of the numbers
whose shifted divisor sum is strictly less than twice their divisor sum.
A003973 gives the shifted divisor sum as the Euler product used below.

Sources: https://oeis.org/A387724, https://oeis.org/A337382, https://oeis.org/A003973
OEIS text, CC BY-SA 4.0.
Credit: @pmaster, assisted by Codex.
-/

open Finset

namespace OMA.S_oeis_a387724

def nextP (p : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (p + 1))

/-- Euler's divisor-sum product with every prime replaced by its successor. -/
def shiftedSigma (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, ∑ i ∈ range (n.factorization p + 1), nextP p ^ i

abbrev sigma (n : ℕ) := ArithmeticFunction.sigma 1 n

def member (n : ℕ) : Prop := n * shiftedSigma n ≤ sigma n ^ 2

def conjecture : Prop :=
  member 6 ∧ (∀ n : ℕ, 0 < n → member n → (2 * n ≤ sigma n ↔ n = 6)) ∧
    ∀ n : ℕ, 0 < n → member n → n ≠ 6 → shiftedSigma n < 2 * sigma n

theorem main : conjecture := by
  sorry

end OMA.S_oeis_a387724
