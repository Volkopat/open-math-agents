import Mathlib

/-!
# A236358: a(n) = |{0 < k < n: m = phi(k)/2 + phi(n-k)/12 is an integer with 2*3^m + 1 prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A236358
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A236358 (Zhi-Wei Sun, Jan 23 2014), part (i): a(n) > 0
for all n > 26.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, ...). `a n` is the number of
  integers k with 0 < k < n such that m = phi(k)/2 + phi(n-k)/12 is an integer with 2*3^m + 1
  prime, exactly as in the OEIS name.
* phi is the Euler totient function `Nat.totient`.
* m = phi(k)/2 + phi(n-k)/12 = (6*phi(k) + phi(n-k))/12 as a rational number; it is an integer
  exactly when 12 divides 6*phi(k) + phi(n-k), which is a separate conjunct, and then the
  natural-number division is exact.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a236358

/-- The condition in the name of A236358 on a tuple, for a given n. -/
def P (n : ℕ) (k : ℕ) : Prop :=
  0 < k ∧ k < n ∧ 12 ∣ 6 * Nat.totient k + Nat.totient (n - k) ∧
  (2 * 3 ^ ((6 * Nat.totient k + Nat.totient (n - k)) / 12) + 1).Prime

/-- A236358: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A236358. -/
theorem main : ∀ n : ℕ, 26 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a236358
