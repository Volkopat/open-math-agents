import Mathlib

/-!
# A235061: Number of ways to write n = k*(k+1)/2 + m with k > 0 and m > 0 such that prime(k*(k+1)/2) + phi(m) is prime, where phi(.) is Euler's totient function.

Source: https://oeis.org/A235061
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A235061 (Zhi-Wei Sun, Jan 03 2014), part (i): a(n) > 0
for all n > 8.

Conventions:
* The sequence has offset 1 (data 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, ...). `a n` is the number of
  pairs (k, m) of natural numbers with n = k*(k+1)/2 + m, k > 0, m > 0 and prime(k*(k+1)/2) +
  phi(m) prime, exactly as in the OEIS name.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* phi is the Euler totient function `Nat.totient`.
* k*(k+1)/2 is the triangular number; the natural-number division by 2 is exact.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a235061

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The condition in the name of A235061 on a tuple, for a given n. -/
def P (n : ℕ) (k m : ℕ) : Prop :=
  0 < k ∧ 0 < m ∧ k * (k + 1) / 2 + m = n ∧ (pr (k * (k + 1) / 2) + Nat.totient m).Prime

/-- A235061: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A235061. -/
theorem main : ∀ n : ℕ, 8 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a235061
