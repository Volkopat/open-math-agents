import Mathlib

/-!
# A214449: Least m>0 such that n! <= m^m.

Source: https://oeis.org/A214449
Credit: @agchua

Comment of A214449 (the entry is by Clark Kimberling, Jul 18 2012), verbatim:
  Conjecture:  this sequence results from A118168 by deleting the first two 1s.
A214449 has offset 1; data 1, 2, 3, 3, 4, 5, 6, 6, 7, 8, 9, 10, 10, ...
A118168 (Olaf Voss, Apr 13 2006) has offset 0 and the name line
  a(n) = x for which abs(x^x-n!) is minimal.
Its data 1, 1, 1, 2, 3, 3, 4, 5, 6, 6, ... begin with a(0) = a(1) = a(2) = 1.

Formalisation. a n is the least m > 0 with n! <= m^m. b n is A118168(n): x runs over the
positive integers (x = 0 would tie with x = 1 at n = 2, since 0^0 = 1, against the listed
a(2) = 1), and if several x attained the minimum the least of them would be taken (no tie
occurs for n <= 400). Deleting the first two terms of A118168 leaves b 2, b 3, b 4, ..., so
the conjecture says a n = b (n + 1) for every n >= 1.
-/

namespace OMA.S_oeis_a214449

/-- A214449(n): the least m > 0 with n! <= m^m. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | 0 < m ∧ Nat.factorial n ≤ m ^ m}

/-- A118168(n): the positive integer x for which |x^x - n!| is minimal (the least such x). -/
noncomputable def b (n : ℕ) : ℕ :=
  sInf {x : ℕ | 0 < x ∧ ∀ y : ℕ, 0 < y →
    |(x : ℤ) ^ x - (Nat.factorial n : ℤ)| ≤ |(y : ℤ) ^ y - (Nat.factorial n : ℤ)|}

/-- The conjecture: A214449 is A118168 with its first two terms (two 1s) deleted, that is
A214449(n) = A118168(n + 1) for every n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = b (n + 1) := by
  sorry

end OMA.S_oeis_a214449
