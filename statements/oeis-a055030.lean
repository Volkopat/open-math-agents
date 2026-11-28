import Mathlib

/-!
# A055030: (Sum(m^(p-1),m=1..p-1)+1)/p as p runs through the primes.

Source: https://oeis.org/A055030
Credit: @azmiozgen

Conjecture (from the entry; Giuga's conjecture, checked by Giuga up to 10^1000): the number
(Sum(m^(n-1),m=1..n-1)+1)/n is an integer iff n is 1 or a prime. (One direction is Fermat's
little theorem.)

Formalization notes:
* "Is an integer" is stated as divisibility in ℕ: n divides 1^(n-1) + ... + (n-1)^(n-1) + 1.
* The conjecture is stated for every n ≥ 1.
* Controls: for p = 2, 3, 5 the quotients are 1, 2, 71, the entry's first terms
  ((1 + 1)/2, (1 + 4 + 1)/3, (1 + 16 + 81 + 256 + 1)/5).
-/

namespace OMA.S_oeis_a055030

/-- Giuga's conjecture: `n ∣ ∑_{m=1}^{n-1} m^(n-1) + 1` iff `n` is `1` or a prime. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → (n ∣ ∑ m ∈ Finset.Icc 1 (n - 1), m ^ (n - 1) + 1 ↔ n = 1 ∨ n.Prime) := by
  sorry

end OMA.S_oeis_a055030
