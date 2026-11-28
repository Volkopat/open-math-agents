import Mathlib

/-!
# A113598: least `n`-digit prime with at least `n` distinct prime digit-permutations.

Source: https://oeis.org/A113598
Credit: @cjchaffin

Conjecture (on the OEIS page): no term is zero, i.e. for every `n ≥ 1` such a prime exists.

Conventions: offset 1; a permutation of the decimal digits of `p` is interpreted by
`Nat.ofDigits 10` applied to a permutation of `Nat.digits 10 p`. As noted on the page,
leading zeros in a permutation do not contribute to the digit count of `p` itself, but
they are allowed in the permutations and yield the corresponding smaller numbers (e.g.
the permutations of `1009` include `9001`, `1009`, `0019 = 19` and `0109 = 109`). The
conjecture is formalized as existence, not the “least such prime” part of the name.
-/

namespace OMA.S_oeis_a113598

/-- The distinct primes obtained by permuting the decimal digits of `p`, including
those permutations that begin with zero. -/
def permPrimes (p : ℕ) : Set ℕ :=
  {m | m.Prime ∧ ∃ l : List ℕ, l.Perm (Nat.digits 10 p) ∧ m = Nat.ofDigits 10 l}

theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ p : ℕ, p.Prime ∧ (Nat.digits 10 p).length = n ∧ n ≤ Nat.card (permPrimes p) := by
  sorry

end OMA.S_oeis_a113598
