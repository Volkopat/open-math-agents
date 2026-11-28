import Mathlib

/-!
# Is A276175 integer-only?

Source: https://mathoverflow.net/questions/248604
Credit: @Hyvok

Question (asked by uvdose on MathOverflow, 2016-08-30; previously asked on math.SE as
question 1905063, 2016-08-27). The terms of OEIS A276123, defined by `a_0 = a_1 = a_2 = 1` and
`a_n = (a_{n-1}+1)(a_{n-2}+1)/a_{n-3}`, are all integers. Is the same true for OEIS A276175,
defined by `a_0 = a_1 = a_2 = a_3 = 1` and
`a_n = (a_{n-1}+1)(a_{n-2}+1)(a_{n-3}+1)/a_{n-4}` ?

What the threads say. On math.SE, mercio (2016) answered yes, via the auxiliary sequence
`b_n b_{n+4} = b_{n+1} b_{n+2} b_{n+3} + 1` with `b_0, ..., b_3 = 1/2, 4, 1/2, 1/2` and
`a_n = b_n b_{n+1} b_{n+2}`: this shows that every `a_n` lies in `Z[1/2]`, and a 2-adic computer
calculation is claimed to exclude powers of 2 in the denominators. On MathOverflow, darij grinberg
noted that this 2-adic part relied on a computation nobody else had checked, and the OEIS entry
(as of Dec 2025) still lists integrality as a conjecture, checked by computer for `n <= 40`.
Martin Rubey commented that the analogous order-6 recurrence is not integral (its term 12 is not an
integer). In July 2026 the math.SE user Sil posted a complete Lean 4 + Mathlib formalization
(GitHub TheSil/mse_1905063, file Proof.lean, about 1.7k lines) proving that every term is an
integer. Its odd-prime part is a valuation induction. Its 2-adic part uses a 44-periodic
valuation pattern and a finite polynomial-jet checker that is closed by `native_decide`.
A MathOverflow comment by Sil points to it.

## Formalization notes

* `a : ℕ → ℚ` is A276175 computed in exact rational arithmetic, indexed from `0` as in OEIS
  (`a 4 = 8`, `a 5 = 36`, `a 6 = 666`, `a 7 = 222111`). Division in `ℚ` is total, but every
  `a n` is positive (each numerator factor is at least `2` and the divisor is an earlier
  positive term), so the junk value `x / 0 = 0` is never used.
* Integer-only is stated as: for every `n` there is an integer `k` with `a n = k`.
* Direction: TRUE. A Lean proof (using `native_decide`) exists, see above. Our scratch check
  with exact rational arithmetic confirms integrality for `n <= 19`.
-/

namespace OMA.S_mo_248604

/-- OEIS A276175: `a 0 = a 1 = a 2 = a 3 = 1` and
`a (n + 4) = (a (n + 3) + 1) * (a (n + 2) + 1) * (a (n + 1) + 1) / a n`, in `ℚ`. -/
def a : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | n + 4 => (a (n + 3) + 1) * (a (n + 2) + 1) * (a (n + 1) + 1) / a n

/-- Every term of A276175 is an integer. -/
theorem main : ∀ n : ℕ, ∃ k : ℤ, a n = k := by
  sorry

end OMA.S_mo_248604
