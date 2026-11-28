import Mathlib

/-!
# A242292: Least prime divisor of 2^n - n which does not divide any 2^k - k with 0 < k < n, or 1 if such a primitive prime divisor of 2^n - n does not exist.

Source: https://oeis.org/A242292
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A242292 (Zhi-Wei Sun, May 10 2014): a(n) = 1 only for n
= 1, 5, 16.

Conventions:
* The sequence has offset 1 (data 1, 2, 5, 3, 1, 29, 11, 31, 503, 13, 7, 1021, ...).
* `Prim n p` says that p is a primitive prime divisor of 2^n - n: p is prime, p divides 2^n - n,
  and p divides no 2^k - k with 0 < k < n. Since 2^n > n the natural-number subtractions are
  exact.
* By definition a(n) = 1 exactly when 2^n - n has no primitive prime divisor (otherwise a(n) is a
  prime, hence at least 2). So `a(n) = 1 only for n = 1, 5, 16` is stated as: for n > 0, if no
  primitive prime divisor exists then n is 1, 5 or 16. As usual the `only for` is an only-if.
-/

namespace OMA.S_oeis_a242292

/-- p is a primitive prime divisor of 2^n - n: a prime dividing 2^n - n and no 2^k - k with
0 < k < n. -/
def Prim (n p : ℕ) : Prop := p.Prime ∧ p ∣ 2 ^ n - n ∧ ∀ k : ℕ, 0 < k → k < n → ¬ p ∣ 2 ^ k - k

/-- The conjecture recorded in A242292. -/
theorem main : ∀ n : ℕ, 0 < n → (¬ ∃ p : ℕ, Prim n p) → n ∈ ({1, 5, 16} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a242292
