import Mathlib

/-!
# A192056: a(n) = |{0<k<n/2: k^2+(n-k)^2-3(n-1 mod 2) is prime and JacobiSymbol[k,n+3(n-1 mod 2)]=1}|.

Source: https://oeis.org/A192056
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A192056 (Zhi-Wei Sun, Dec 30 2012): a(n)>0 for all n>2.

Conventions:
* The sequence has offset 1 (data 0, 0, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, ...). `a n` is the number of
  integers k with 0 < k < n/2 such that k^2 + (n-k)^2 - 3*((n-1) mod 2) is prime and the Jacobi
  symbol (k / (n + 3*((n-1) mod 2))) equals 1, exactly as in the OEIS name.
* The Jacobi symbol is the Mathlib function `jacobiSym` (integer numerator, natural denominator);
  the denominator n + 3*((n-1) mod 2) is always odd for n >= 1.
* 0 < k < n/2 is written 0 < k and 2 * k < n. The subtractions are exact for n >= 3 and 0 < k <
  n/2 (the expression k^2 + (n-k)^2 is then at least 5).
* Only the first sentence of the conjecture is formalized; the `Moreover` sentence is a different
  (stronger) statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a192056

/-- The condition in the name of A192056 on a tuple, for a given n. -/
def P (n : ℕ) (k : ℕ) : Prop :=
  0 < k ∧ 2 * k < n ∧ (k ^ 2 + (n - k) ^ 2 - 3 * ((n - 1) % 2)).Prime ∧
  jacobiSym (k : ℤ) (n + 3 * ((n - 1) % 2)) = 1

/-- A192056: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A192056. -/
theorem main : ∀ n : ℕ, 2 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a192056
