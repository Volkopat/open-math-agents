import Mathlib

/-!
# A108954: the generating function of `pi(2n) - pi(n)`

Source: https://oeis.org/A108954

The sequence is `a(n) = pi(2n) - pi(n)` for `n ≥ 1` (offset 1), the number of primes `p` with
`n < p ≤ 2n`. The entry records the conjecture (Benedict W. J. Irwin, 2017)

  G.f.: `Sum_{i>0} Sum_{j>=i | i+j is prime} x^j`.

## Encoding

* `pi` is Mathlib's `Nat.primeCounting`, the number of primes `≤ n`.
* The generating function of `a` is the formal power series `Sum_{n≥1} a(n) x^n` over `ℕ`;
  its constant coefficient is `0` because the sequence starts at `n = 1`.
* In the double sum, the monomial `x^j` occurs once for every `i` with `1 ≤ i ≤ j` and `i + j`
  prime, and for no other `i`. Since only finitely many terms contribute to each power of `x`, the
  double sum is the formal power series whose coefficient of `x^j` is the number of `i` in
  `[1, j]` with `i + j` prime. The statement is the equality of these two power series.
-/

namespace OMA.S_oeis_a108954

/-- `a n = pi(2n) - pi(n)`, the number of primes in the interval `(n, 2n]` (A108954, offset 1). -/
def a (n : ℕ) : ℕ := Nat.primeCounting (2 * n) - Nat.primeCounting n

/-- **Irwin's conjecture for A108954**: the generating function `Sum_{n≥1} a(n) x^n` equals the
double sum `Sum_{i>0} Sum_{j>=i, i+j prime} x^j`, whose coefficient of `x^j` is the number of
`i` with `1 ≤ i ≤ j` and `i + j` prime. -/
theorem main :
    PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else a n) =
      PowerSeries.mk (fun j : ℕ => ((Finset.Icc 1 j).filter (fun i => Nat.Prime (i + j))).card) := by
  sorry

end OMA.S_oeis_a108954
