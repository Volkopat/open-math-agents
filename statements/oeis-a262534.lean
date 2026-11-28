import Mathlib

/-!
# A262534: Numbers k such that phi(k-2) = phi(k-1) = (k-1) / 2

Source: https://oeis.org/A262534
Credit: @xor2k

Formalizes the OEIS A262534 conjecture: next term is 4294967297 (that is, after the terms
3, 5, 17, 257, 65537, the next term of the sequence is 4294967297).

Conventions: `phi` is `Nat.totient`. A term is an integer `k ≥ 3` (so that `k - 2` is a
positive integer, as in the Magma program, which starts at 3), and the condition
`phi(k-1) = (k-1)/2` is read as the exact equation `2 * phi(k-1) = k - 1`, as in the Magma
and PARI programs of the entry. The conjecture is stated as: the terms of the sequence that are
at most 4294967297 are exactly 3, 5, 17, 257, 65537 and 4294967297, so the sixth term is
4294967297.
-/

namespace OMA.S_oeis_a262534

/-- Membership in A262534: `k ≥ 3`, `phi(k-2) = phi(k-1)` and `2 * phi(k-1) = k - 1`. -/
def InA262534 (k : ℕ) : Prop :=
  3 ≤ k ∧ Nat.totient (k - 2) = Nat.totient (k - 1) ∧ 2 * Nat.totient (k - 1) = k - 1

/-- The terms of A262534 up to 4294967297 are exactly 3, 5, 17, 257, 65537, 4294967297. -/
theorem main :
    ∀ k : ℕ, (InA262534 k ∧ k ≤ 4294967297) ↔
      k ∈ ({3, 5, 17, 257, 65537, 4294967297} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a262534
