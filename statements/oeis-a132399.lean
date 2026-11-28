import Mathlib

/-!
# A132399: Number of ordered ways of writing n = i + j, where i is 0 or a prime and j is a triangular number (A000217) >= 0.

Source: https://oeis.org/A132399
Credit: @gblacher2

Conjecture (Zhi-Wei Sun, Number Theory Mailing List, Mar 23 2008, quoted in A132399):
"a(n) > 0 except for n = 216." In Sun's paper "On sums of primes and triangular numbers"
(J. Combin. Number Theory 1 (2009) 65-76, arXiv:0803.3737) it reads: each natural number not
equal to 216 can be written in the form `p + T_x` with `x` an integer and `p` a prime or zero,
where `T_x = x(x+1)/2`.

Conventions:
* A triangular number (A000217) is `T k = k(k+1)/2` with `k ≥ 0` (0, 1, 3, 6, 10, …). For an
  integer `x`, `T_x = T_{-x-1}`, so integer and natural indices give the same triangular numbers.
* `a n` counts the ordered decompositions `n = i + j` with `i` zero or a prime and `j`
  triangular. Since `k ↦ T k` is injective, this is the number of pairs `(i, k)` with `i` zero or
  a prime and `i + T k = n`; both entries are at most `n` because `T k ≥ k`.

With these definitions `a(0), …, a(10)` are 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, as in the OEIS data
(for example `a(8) = 3` from `8 = 7 + 1 = 5 + 3 = 2 + 6`), `a(216) = 0`, and all terms of the
b-file (`n = 0..10000`) are reproduced.
-/

namespace OMA.S_oeis_a132399

/-- The `k`-th triangular number `T k = k (k + 1) / 2` (A000217). -/
def T (k : ℕ) : ℕ := k * (k + 1) / 2

/-- A132399: the number of ordered ways to write `n = i + j` with `i` zero or a prime and `j` a
triangular number, counted as the pairs `(i, k)` with `i + T k = n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun p : ℕ × ℕ => (p.1 = 0 ∨ p.1.Prime) ∧ p.1 + T p.2 = n)).card

/-- Sun's conjecture: `a(n) > 0` for every natural number `n ≠ 216`. -/
theorem main : ∀ n : ℕ, n ≠ 216 → 0 < a n := by
  sorry

end OMA.S_oeis_a132399
