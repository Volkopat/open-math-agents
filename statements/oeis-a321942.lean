import Mathlib

/-!
# A321942: A sequence related to the Euler-Gompertz constant.

Source: https://oeis.org/A321942 (OEIS Foundation, CC BY-SA 4.0)
Credit: @bmendonca3

[Lean proof of this statement](https://github.com/bmendonca3/open-math-agents/blob/367e55b097c28971ccb7b08a7a7d831742564854/proofs/oeis-a321942.lean)

Entry A321942 (Richard P. Brent, Dec 12 2018), offset 1, data 1, 2, 8, 44, 300, 2420, 22460, ...
Comment section: a(n) satisfies the recurrence a(n) = (2n-1)*a(n-1) - (n-1)*(n-2)*a(n-2) for
n > 2, with initial conditions a(1)=1, a(2)=2.

Formula section:
Conjecture: Integral_{x = 0..oo} (x/(1 + x))^n*exp(-x) dx = 1/(n-1)!*( a(n) - A000262(n)*G ),
where G = Integral_{x = 0..oo} exp(-x)/(1 + x) dx is the Euler-Gompertz constant A073003.
- Peter Bala, Mar 20 2022

## Reading of the statement

* `a` is A321942, defined by the recurrence and the initial conditions of the entry. The values
  are integers, so `a` takes values in `ℤ` and the subtraction in the recurrence is exact. The
  sequence has offset 1. The value `a 0 = 0` is a filler: `main` does not use it.
* `A000262 n` is OEIS A000262 (offset 0, data 1, 1, 3, 13, 73, 501, 4051, ...): the number of
  partitions of an `n`-set into any number of lists (ordered nonempty blocks). It is defined by
  the formula in the entry (Francesca Aicardi, Nov 03 2022): for n > 0,
  A000262(n) = Sum_{k=0..n-1} k!*C(n-1,k)*C(n,k), with A000262(0) = 1. The term for `k` is
  C(n-1,k) * n!/(n-k)!, the Lah number that counts the partitions of an `n`-set into `n-k`
  lists. The definition uses `n = m + 1`, so no subtraction of natural numbers occurs.
* `G` is the integral that the source gives for the Euler-Gompertz constant. Mathlib has no
  definition of this constant, so the integral itself is the definition.
* Integral_{x = 0..oo} is the Lebesgue integral over `Set.Ioi 0`, the usual Mathlib form of an
  integral from 0 to infinity. The single point 0 does not change the value. Both integrands are
  continuous and bounded by exp(-x) on this set, so both integrals converge.
* Range: the source gives no range. The reading is n >= 1: the sequence has offset 1 and the
  factor 1/(n-1)! needs n >= 1. With `1 ≤ n`, the subtraction `n - 1` in `ℕ` is exact.
* The two sides are compared in `ℝ`.
-/

namespace OMA.S_oeis_a321942

/-- OEIS A321942 (offset 1): `a(1) = 1`, `a(2) = 2` and
`a(n) = (2n-1)*a(n-1) - (n-1)*(n-2)*a(n-2)` for `n > 2`. The value at `0` is a filler. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | (n + 3) =>
    (2 * ((n : ℤ) + 3) - 1) * a (n + 2) - (((n : ℤ) + 3) - 1) * (((n : ℤ) + 3) - 2) * a (n + 1)

/-- OEIS A000262 (offset 0): the number of partitions of an `n`-set into lists.
`A000262(0) = 1` and `A000262(n) = ∑_{k=0}^{n-1} k! * C(n-1,k) * C(n,k)` for `n > 0`. -/
def A000262 : ℕ → ℕ
  | 0 => 1
  | (m + 1) => ∑ k ∈ Finset.range (m + 1), k.factorial * m.choose k * (m + 1).choose k

/-- The Euler-Gompertz constant, as the source defines it: `G = ∫_0^∞ exp(-x)/(1 + x) dx`. -/
noncomputable def G : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) / (1 + x)

/-- Bala's conjecture: for `n ≥ 1`,
`∫_0^∞ (x/(1 + x))^n * exp(-x) dx = 1/(n-1)! * (a(n) - A000262(n) * G)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∫ x in Set.Ioi (0 : ℝ), (x / (1 + x)) ^ n * Real.exp (-x) =
      1 / ((n - 1).factorial : ℝ) * ((a n : ℝ) - (A000262 n : ℝ) * G) := by
  sorry

end OMA.S_oeis_a321942
