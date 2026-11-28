import Mathlib

/-!
# A308644: Number of ways to write n as (3^a*5^b)^2 + c*(3c+1)/2 + d*(7d+1)/2, where a and b are nonnegative integers, and c and d are integers.

Source: https://oeis.org/A308644
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A308644 (Zhi-Wei Sun, Jun 13 2019), Conjecture 1, first
sentence: a(n) > 0 for all n > 0.

Conventions:
* The sequence has offset 1 (data 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, ...). `a n` is the number of
  quadruples (a, b, c, d) with a, b natural numbers and c, d integers such that n = (3^a*5^b)^2 +
  c*(3c+1)/2 + d*(7d+1)/2, exactly as in the OEIS name.
* c and d range over `ℤ` (the OEIS examples use negative values); the equation is stated in `ℤ`
  with the natural quantities cast, and the integer divisions by 2 are exact since c*(3c+1) and
  d*(7d+1) are always even.
* Only the first sentence of Conjecture 1 is formalized; its `Also` sentence and Conjecture 2 are
  different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a308644

/-- The condition in the name of A308644 on a tuple, for a given n. -/
def P (n : ℕ) (a b : ℕ) (c d : ℤ) : Prop :=
  ((3 ^ a * 5 ^ b : ℕ) : ℤ) ^ 2 + c * (3 * c + 1) / 2 + d * (7 * d + 1) / 2 = n

/-- A308644: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℤ × ℤ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A308644. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a308644
