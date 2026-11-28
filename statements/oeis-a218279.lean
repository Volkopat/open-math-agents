import Mathlib

/-!
# A218279: Let (p(n), p(n)+2) be the n-th twin prime pair. a(n) is the smallest k, such that there is only one prime in the interval (k*p(n), k*(p(n)+2)), or a(n)=0, if there is no such k.

Source: https://oeis.org/A218279
Credit: @eltociear

For a twin prime pair `(p, p + 2)`, `a` is the least positive integer `k` such that the open
interval `(k p, k (p + 2))` contains exactly one prime, and `0` if there is no such `k`
(for `(3, 5)`: `k = 1` gives `(3, 5)` with no prime and `k = 2` gives `(6, 10)` with only `7`, so
`a(1) = 2`). The entry conjectures:

  a(n) > 0 for all n,

that is, for every twin prime pair `(p, p + 2)` some `k ≥ 1` works. `main` states this for every
prime `p` with `p + 2` prime, which ranges over exactly the twin prime pairs. The primes in the
open interval are counted with `Finset.Ioo`.
-/

namespace OMA.S_oeis_a218279

/-- The conjecture in OEIS A218279: for every twin prime pair `(p, p + 2)` there is `k ≥ 1` such
that the open interval `(k p, k (p + 2))` contains exactly one prime. -/
theorem main : ∀ p : ℕ, p.Prime → (p + 2).Prime →
    ∃ k : ℕ, 1 ≤ k ∧ ((Finset.Ioo (k * p) (k * (p + 2))).filter Nat.Prime).card = 1 := by
  sorry

end OMA.S_oeis_a218279
-- ci: re-run check-proof
