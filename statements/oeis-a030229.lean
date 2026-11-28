import Mathlib

/-!
# A030229: inverse of the divisibility matrix at numbers with an even number of prime factors

Source: https://oeis.org/A030229 (comment in the OEIS entry)

A030229 lists the numbers that are the product of an even number of distinct primes
(1, 6, 10, 14, ...), i.e. the squarefree positive integers with an even number of
prime factors.

Conjecture: for the matrix `M(i, j) = 1` if `j` divides `i` and `0` otherwise
(rows and columns indexed by the positive integers), `Inverse(M)(a, 1) = -1` for every
`a` in the sequence.

`M` is lower unitriangular, so the entries of its inverse with indices `<= N` are the entries
of the inverse of the `N x N` truncation. We use the truncation to indices `1..N`
(stored as `Fin N`, so the index `i` stands for `i + 1`) for any `N >= a`, over the rationals.
-/

namespace OMA.S_oeis_a030229

/-- Squarefree positive integers with an even number of prime factors. -/
def A030229 : Set ℕ := {a | 0 < a ∧ Squarefree a ∧ Even a.primeFactors.card}

/-- The divisibility matrix truncated to indices `1..N`; entry `(i, j)` stands for `(i+1, j+1)`. -/
def M (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun i j => if ((j : ℕ) + 1) ∣ ((i : ℕ) + 1) then 1 else 0

theorem main : ∀ N a : ℕ, ∀ (ha : a ∈ A030229) (hN : a ≤ N),
    (M N)⁻¹ ⟨a - 1, by have := ha.1; omega⟩ ⟨0, by have := ha.1; omega⟩ = -1 := by
  sorry

end OMA.S_oeis_a030229
