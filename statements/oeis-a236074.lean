import Mathlib

/-!
# A236074: a(n) = |{0 < k < n: p = phi(k) + phi(n-k)/6 + 1, prime(2*p) - 2*prime(p) and prime(p) - 2*prime((p-1)/2) are all prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A236074
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A236074 (Zhi-Wei Sun, Jan 19 2014), part (i): a(n) > 0
for all n > 116.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...). `a n` is the number of
  integers k with 0 < k < n such that p = phi(k) + phi(n-k)/6 + 1, prime(2*p) - 2*prime(p) and
  prime(p) - 2*prime((p-1)/2) are all prime, exactly as in the OEIS name.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* phi is the Euler totient function `Nat.totient`.
* p is an integer, so phi(n-k)/6 has to be an integer: the divisibility 6 | phi(n-k) is a separate
  conjunct and the natural-number division is then exact. The helper `p n k` is p.
* For an odd prime p, (p-1)/2 is an exact division. For p = 2 the term prime((p-1)/2) is not
  defined, but p = 2 is already excluded by the second condition since prime(4) - 2*prime(2) = 1
  is not prime, so the value of the third conjunct at p = 2 is irrelevant.
* Natural-number subtraction is truncated: where the true value would be negative the truncated
  value is 0, and neither is prime, so the condition is unchanged.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a236074

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- p = phi(k) + phi(n-k)/6 + 1. -/
def p (n k : ℕ) : ℕ := Nat.totient k + Nat.totient (n - k) / 6 + 1

/-- The condition in the name of A236074 on a tuple, for a given n. -/
def P (n : ℕ) (k : ℕ) : Prop :=
  0 < k ∧ k < n ∧ 6 ∣ Nat.totient (n - k) ∧ (p n k).Prime ∧
  (pr (2 * p n k) - 2 * pr (p n k)).Prime ∧ (pr (p n k) - 2 * pr ((p n k - 1) / 2)).Prime

/-- A236074: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A236074. -/
theorem main : ∀ n : ℕ, 116 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a236074
