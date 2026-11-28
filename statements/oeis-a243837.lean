import Mathlib

/-!
# OEIS A243837

Zhi-Wei Sun's conjecture concerns blocks of consecutive primes of every length.
The sequence entry lists the starting indices for blocks of length three.
Pan and Sun proved the general conjecture under the generalized Riemann hypothesis.

Source: https://oeis.org/A243837
Reference: https://arxiv.org/abs/1406.5951
Credit: @jacklarmer
-/

namespace OMA.S_oeis_a243837

/-- The prime with one-based index `k`, used only at positive indices. -/
noncomputable def primeAt (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

theorem main : ∀ m : ℕ, 0 < m →
    {n : ℕ | 0 < n ∧ ∀ i j : Fin (m + 1), i ≠ j →
      IsPrimitiveRoot (primeAt (n + i.val) : ZMod (primeAt (n + j.val)))
        (primeAt (n + j.val) - 1)}.Infinite := by
  sorry

end OMA.S_oeis_a243837
