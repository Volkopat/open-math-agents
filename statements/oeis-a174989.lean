import Mathlib

/-!
# OEIS A174989: Partial sums of A003602.

Source: https://oeis.org/A174989
Credit: @unserus

OEIS: "I conjecture that infinitely many terms are prime."
A003602(n) = `k` where `n = (2k - 1) 2^m`, i.e. `(odd part of n + 1) / 2`, for `n ≥ 1`; the odd
part is `n / 2^(v_2(n))` (`v_2` = `Nat.factorization n 2`). A174989(n) = `∑_{i=1}^{n} A003602(i)`
(`1, 2, 4, 5, 8, ...`).
-/

namespace OMA.S_oeis_a174989

/-- A003602: `(n / 2^(v_2 n) + 1) / 2`. -/
def a003602 (n : ℕ) : ℕ := (n / 2 ^ (n.factorization 2) + 1) / 2

/-- A174989: the partial sums of A003602. -/
def a174989 (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 n, a003602 i

/-- Infinitely many terms of A174989 are prime. -/
theorem main : {n : ℕ | 1 ≤ n ∧ (a174989 n).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a174989
