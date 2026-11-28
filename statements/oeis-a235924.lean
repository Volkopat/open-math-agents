import Mathlib

/-!
# A235924: a(n) = |{0 < k < n: p = phi(k) + phi(n-k)/3 + 1, q = prime(p) - p + 1 and r = prime(q) - q + 1 are all prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A235924
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A235924 (Zhi-Wei Sun, Jan 17 2014): a(n) > 0 for all n
> 37.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, ...). `a n` is the number of
  integers k with 0 < k < n such that p = phi(k) + phi(n-k)/3 + 1, q = prime(p) - p + 1 and r =
  prime(q) - q + 1 are all prime, exactly as in the OEIS name.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* phi is the Euler totient function `Nat.totient`.
* p is an integer, so phi(n-k)/3 has to be an integer: the divisibility 3 | phi(n-k) is a separate
  conjunct and the natural-number division is then exact. The helpers `p n k` and `q n k` are p
  and q.
* The subtractions are exact natural-number subtractions since prime(j) >= j for j >= 1 (and p, q
  >= 1).
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a235924

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- p = phi(k) + phi(n-k)/3 + 1. -/
def p (n k : ℕ) : ℕ := Nat.totient k + Nat.totient (n - k) / 3 + 1

/-- q = prime(p) - p + 1. -/
noncomputable def q (n k : ℕ) : ℕ := pr (p n k) - p n k + 1

/-- The condition in the name of A235924 on a tuple, for a given n. -/
def P (n : ℕ) (k : ℕ) : Prop :=
  0 < k ∧ k < n ∧ 3 ∣ Nat.totient (n - k) ∧ (p n k).Prime ∧ (q n k).Prime ∧
  (pr (q n k) - q n k + 1).Prime

/-- A235924: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A235924. -/
theorem main : ∀ n : ℕ, 37 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a235924
