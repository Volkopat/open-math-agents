import Mathlib

/-!
# A028355: How the astronomical clock (Orloj) in Prague would strike 1,2,3,...

Source: https://oeis.org/A028355 (conjectures by Chai Wah Wu, Apr 18 2024)

The entry: how the astronomical clock in Prague would strike 1,2,3,...,24,25,.. (digits
follow 12343212343... (A028356), n-th group adds to n); offset 1, terms
1, 2, 3, 4, 32, 123, 43, 2123, 432, 1234, ...

Conjectures: a(n) = 1000001*a(n-15) - 1000000*a(n-30) for n > 30, and
G.f.: x*(100000*x^28 + ... + 2*x + 1)/(1000000*x^30 - 1000001*x^15 + 1).

Conventions. The digit stream is A028356 (offset 0), the periodic sequence
1, 2, 3, 4, 3, 2, 1, 2, ..., written `d i`. The stream is cut into consecutive groups,
the n-th group having digit sum n; so the first n groups use the first `P n` digits, where
`P n` is the least `m` such that the first `m` digits have sum at least `n(n+1)/2`
(for this stream the sum is then exactly `n(n+1)/2`). The term a(n) reads the digits of the
n-th group, i.e. digits `P (n-1)`, ..., `P n - 1` of the stream, as a decimal number.
For the generating function the series is `sum_{n >= 1} a(n) x^n` (offset 1), so its
constant coefficient is 0. The denominator has constant term 1, so the g.f. identity is
equivalent to the stated product identity of formal power series over `ℤ`. The statement
is the conjunction of the two conjectures.
-/

namespace OMA.S_oeis_a028355

open PowerSeries

/-- The digit stream A028356: 1, 2, 3, 4, 3, 2, repeated. -/
def d (i : ℕ) : ℕ := [1, 2, 3, 4, 3, 2].getD (i % 6) 0

/-- Sum of the first `m` digits of the stream. -/
def S (m : ℕ) : ℕ := ∑ i ∈ Finset.range m, d i

/-- Number of digits used by the first `n` groups. -/
noncomputable def P (n : ℕ) : ℕ := sInf {m : ℕ | n * (n + 1) / 2 ≤ S m}

/-- The n-th group read as a decimal number (for n >= 1). -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico (P (n - 1)) (P n), d i * 10 ^ (P n - 1 - i)

theorem main :
    (∀ n : ℕ, 30 < n → (a n : ℤ) = 1000001 * a (n - 15) - 1000000 * a (n - 30)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
        (1000000 * X ^ 30 - 1000001 * X ^ 15 + 1) =
      X * (100000*X^28 + 200000*X^27 + 300000*X^26 + 400000*X^25 + 320000*X^24 + 123000*X^23 + 430000*X^22 + 212300*X^21 + 432000*X^20 + 123400*X^19 + 321230*X^18 + 432120*X^17 + 343210*X^16 + 234320*X^15 + 123432*X^14 + 23432*X^13 + 34321*X^12 + 43212*X^11 + 32123*X^10 + 1234*X^9 + 432*X^8 + 2123*X^7 + 43*X^6 + 123*X^5 + 32*X^4 + 4*X^3 + 3*X^2 + 2*X + 1) := by
  sorry

end OMA.S_oeis_a028355
