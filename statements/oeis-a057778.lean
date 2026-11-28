import Mathlib

/-!
# A057778: a(n) is the least odd k such that k*2^n + 1 is prime.

Source: https://oeis.org/A057778
Credit: @gblacher2

The two conjectures of A057778, both by Thomas Ordowski:
1. (Apr 13 2019, comment) "for n > 0, a(n) = k < 2^n, so k*2^n + 1 is a Proth prime A080076",
   that is, for every `n ≥ 1` the least odd `k` with `k * 2^n + 1` prime satisfies `k < 2^n`;
2. (Oct 14 2014, formula section) "a(n) = O(n*log(n))", read as the usual Landau big-O as
   `n → ∞`.

Conventions:
* the offset of A057778 is 0, and the conjecture is stated for `n > 0` (for `n = 0` it fails,
  since `a 0 = 1` and `2^0 = 1`);
* for every `n` the set below is nonempty by Dirichlet's theorem on primes in arithmetic
  progressions (`k * 2^n + 1` with `k` odd runs over the progression `2^n + 1 (mod 2^(n+1))`),
  so its infimum is its least element and `a n < 2 ^ n` says exactly that some odd `k < 2^n`
  makes `k * 2^n + 1` prime.

With this definition `a 0 = 1`, `a 3 = 5` and `a 9 = 15`, as in the OEIS data
`1, 1, 1, 5, 1, 3, 3, 5, 1, 15, 13, 9, ...`.
-/

namespace OMA.S_oeis_a057778

/-- A057778: the least odd `k` such that `k * 2^n + 1` is prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | Odd k ∧ (k * 2 ^ n + 1).Prime}

/-- The two conjectures of A057778: for `n > 0`, `a n < 2 ^ n` (so `a n * 2 ^ n + 1` is a Proth
prime), and `a n = O(n log n)`. -/
theorem main :
    (∀ n : ℕ, 0 < n → a n < 2 ^ n) ∧
      (fun n : ℕ => (a n : ℝ)) =O[Filter.atTop] (fun n : ℕ => (n : ℝ) * Real.log n) := by
  sorry

end OMA.S_oeis_a057778
