import Mathlib

/-!
# A240232: `prime(n) + a(n)` and `prime(n) + a(n) ^ 2` both prime

Source: https://oeis.org/A240232
Credit: @eltociear

For `n >= 1`, A240232 lists the smallest positive integer `a(n)` such that `prime(n) + a(n)` and
`prime(n) + a(n) ^ 2` are both prime numbers, where `prime(n)` is the `n`-th prime in increasing
order, so that `prime(1) = 2`, `prime(2) = 3`, and so on.

The entry records the conjecture that such an integer always exists:

*Conjecture: For each prime(n) there exists at least one positive integer a(n) such that
prime(n) + a(n) and prime(n) + (a(n))^2 are both primes.*

and gives next to it the equivalent reformulation: if one defines `a(n) = 0` for those `n` for
which no positive integer makes both `prime(n) + a(n)` and `prime(n) + a(n) ^ 2` prime, then the
conjecture is that `a(n) > 0` for all `n >= 1`.

`main` states the conjecture in the index-free form obtained by replacing the index `n` by the
prime itself. Since `prime` runs through the primes exactly once, in increasing order, the two
forms assert the same thing: every prime `p` admits a positive integer `a` such that `p + a` and
`p + a ^ 2` are both prime. Minimality of `a(n)` plays no role in the truth of the conjecture,
which asserts only that the set of such `a` is nonempty; the least element of that set is the
term `a(n)` of A240232.
-/

namespace OMA.S_oeis_a240232

theorem main : ∀ p : ℕ, Nat.Prime p → ∃ a : ℕ, 0 < a ∧ Nat.Prime (p + a) ∧ Nat.Prime (p + a ^ 2) := by
  sorry

end OMA.S_oeis_a240232
-- ci: re-run check-proof
