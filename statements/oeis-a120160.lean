import Mathlib

/-!
# A120160: a(n) = ceiling(Sum_{i=1..n-1} a(i)/4) for n >= 2 starting with a(1) = 1.

Source: https://oeis.org/A120160. Related: https://oeis.org/A024634 (n written in fractional base 5/4)
Credit: @Squee451

Data (offset 1): 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 5, 6, 8, 10, 12, 15, 19, 24, 30, 37, 47, 58, 73, 91, ...

The entry's comment (Petros Hadjicostas, 21 July 2020), Conjecture 2: a(n) equals 1/5 times the number
of nonnegative integers with the property that their 5/4-expansion has n digits (assuming that the
5/4-expansion of 0 has 1 digit). For example, a(7)*5 = 10 because the following 10 numbers have 5/4
expansions with n = 7 digits: 35 = 4321030, 36 = 4321031, ..., 44 = 4321424.

Conventions.
* The 5/4-expansion is the one of A024634: the last digit of `m` is `m mod 5` and the remaining
  digits are the expansion of `4 * floor(m / 5)`; numbers below 5 have one digit (so does 0, as the
  conjecture assumes). `digitLength` counts the digits accordingly.
* `aS n = (a(n), a(1) + ... + a(n))`, so that `a (n+2) = ceiling((a(1) + ... + a(n+1)) / 4)`, written
  `(s + 3) / 4` with floor division. The value at `n = 0` is a placeholder (offset 1).
* The count is `Set.ncard`; the statement `ncard = 5 * a n` with `a n ≥ 1` in particular says that
  the set of integers with exactly `n` digits is finite.
-/

namespace OMA.S_oeis_a120160

/-- `aS n = (a(n), a(1) + ... + a(n))` for A120160. -/
def aS : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | 1 => (1, 1)
  | n + 2 =>
    let s := (aS (n + 1)).2
    ((s + 3) / 4, s + (s + 3) / 4)

/-- A120160 (1-indexed). -/
def a (n : ℕ) : ℕ := (aS n).1

/-- Number of digits of `m` in fractional base 5/4 (A024634), with one digit for 0. -/
def digitLength (m : ℕ) : ℕ :=
  if m < 5 then 1 else 1 + digitLength (4 * (m / 5))
termination_by m
decreasing_by omega

/-- For every `n ≥ 1`, exactly `5 * a n` nonnegative integers have a 5/4-expansion with `n` digits. -/
theorem main : ∀ n : ℕ, 1 ≤ n → {m : ℕ | digitLength m = n}.ncard = 5 * a n := by
  sorry

end OMA.S_oeis_a120160
