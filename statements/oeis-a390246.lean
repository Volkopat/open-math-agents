import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fin.Basic

/-!
# Matching the integers up to n with distinct multiples

A390246 minimizes the width of an open interval starting at n.
A219787 minimizes the upper endpoint of a closed interval starting at n+1.
The value b(i) matches the positive integer i.val+1 with its multiple.
For positive n the interval bounds make all possible matches positive.

This is Bill McEachen's OEIS identity. Erdős and Pomerance also ask for
the asymptotic growth of the matching interval.
Sources: https://oeis.org/A390246 and https://oeis.org/A219787
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a390246

def widths (n : ℕ) : Set ℕ := {k | ∃ b : Fin n → ℕ, Function.Injective b ∧
  ∀ i, (i.val + 1) ∣ b i ∧ n < b i ∧ b i < n + k}

def endpoints (n : ℕ) : Set ℕ := {u | ∃ b : Fin n → ℕ, Function.Injective b ∧
  ∀ i, (i.val + 1) ∣ b i ∧ n + 1 ≤ b i ∧ b i ≤ u}

theorem main : ∀ n : ℕ, 1 ≤ n → sInf (widths n) = sInf (endpoints n) - (n - 1) := by
  sorry

end OMA.S_oeis_a390246
