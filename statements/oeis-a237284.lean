import Mathlib

/-!
# A237284: Number of ordered ways to write 2*n = p + q with p, q and A000720(p) all prime.

Source: https://oeis.org/A237284
Credit: @eltociear

`a(n)` (offset 1) counts the ordered ways to write `2n = p + q` with `p`, `q` and `π(p)` all prime
(A000720 is `π`). The entry conjectures (Zhi-Wei Sun):

  a(n) > 0 for all n > 2, and a(n) = 1 only for n = 3, 6, 13, 16, 19, 28, 34, 40, 61, 166, 278.

`main` is the conjunction of the two parts, with `a(n)` the number of primes `p < 2n` such that
`2n - p` and `π(p)` are prime (each such `p` gives exactly one ordered pair `(p, q)`). `π(x)` is `Nat.primeCounting x`.
-/

namespace OMA.S_oeis_a237284

/-- OEIS A237284: the number of ordered ways to write `2n = p + q` with `p`, `q`, `π(p)` prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * n)).filter
    (fun p => p.Prime ∧ (2 * n - p).Prime ∧ (Nat.primeCounting p).Prime)).card

/-- The conjecture in OEIS A237284. -/
theorem main : (∀ n : ℕ, 2 < n → 0 < a n) ∧
    (∀ n : ℕ, 2 < n → a n = 1 → n ∈ ({3, 6, 13, 16, 19, 28, 34, 40, 61, 166, 278} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a237284
