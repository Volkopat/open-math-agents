import Mathlib

/-!
# A210144: a(n) = least integer m>1 such that the product of the first k primes for k=1,...,n are pairwise distinct modulo m.

Source: https://oeis.org/A210144
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A210144 (Zhi-Wei Sun, Mar 17 2012): all the terms are
primes and a(n)<n^2 for all n > 1.

Conventions:
* The sequence has offset 1 (data 2, 3, 5, 11, 11, 23, 29, 37, 37, 41, 47, 47, ...).
* `a n` is the least integer m > 1 such that the products of the first k primes for k = 1, ..., n
  are pairwise distinct modulo m, as an infimum (`sInf`) over the natural numbers; the set is
  nonempty (any m larger than all these products works), so the infimum is the least element.
* The product of the first k primes is the helper `primorial k`, with `Nat.nth Nat.Prime`
  0-indexed (`Nat.nth Nat.Prime 0 = 2`).
* `all the terms are primes` is stated for every n >= 1 (the offset); `a(n) < n^2` for every n >
  1.
-/

namespace OMA.S_oeis_a210144

/-- The primorial p(k)# = product of the first k primes. -/
noncomputable def primorial (k : ℕ) : ℕ := ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- A210144: least m > 1 such that the primorials p(1)#, ..., p(n)# are pairwise distinct mod m. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 < m ∧ ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n → primorial i % m ≠ primorial j % m}

/-- The conjecture recorded in A210144. -/
theorem main : (∀ n : ℕ, 1 ≤ n → (a n).Prime) ∧ (∀ n : ℕ, 1 < n → a n < n ^ 2) := by
  sorry

end OMA.S_oeis_a210144
