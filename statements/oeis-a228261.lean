import Mathlib

/-!
# OEIS A228261: Barker's conjectures for the number of third differences of arrays of length 5 of numbers in 0..n

Source: https://oeis.org/A228261 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A228261 (R. H. Hardin, Aug 19 2013), offset 1: Number of third differences of arrays of
length 5 of numbers in 0..n.
Formula section:
Empirical: a(n) = 35*n^2 + n + 1 for n>1.
Conjectures from Colin Barker, Sep 10 2018: (Start)
G.f.: x*(31 + 50*x - 17*x^2 + 6*x^3) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>4.
(End)

Formalization notes:
* An array of length 5 of numbers in 0..n is a map x : Fin 5 -> Fin (n + 1). Its third
  differences form the array of the two integers x(i+3) - 3 x(i+2) + 3 x(i+1) - x(i), i = 0, 1
  (`thirdDiff`), and a(n) is the number of distinct such arrays, the size of the image of
  `thirdDiff`. The opposite sign convention for the differences negates every array and gives the
  same count.
* This reading reproduces every listed term of the table A228260 (third differences of arrays of
  length n + 3, of which the entry is row 2) with at most 200000 arrays to enumerate (lengths 4 to
  11), checked by direct enumeration.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^3 = x (31 + 50x - 17x^2 + 6x^3) in the formal power series ring over the
  rationals; and the recurrence, for every n > 4, as an identity of integers.
* The definition reproduces the entry's data (31, 143, 319, 565, 881, 1267, ... from n = 1,
  checked by direct enumeration for n <= 9 and against every listed term through the formula of
  the proof).
-/

namespace OMA.S_oeis_a228261

open PowerSeries Finset

/-- The third differences x(i+3) - 3 x(i+2) + 3 x(i+1) - x(i) of an array of length m + 3. -/
def thirdDiff {m N : ℕ} (x : Fin (m + 3) → Fin N) : Fin m → ℤ :=
  fun i => (x i.succ.succ.succ : ℤ) - 3 * (x i.succ.succ.castSucc : ℤ) +
    3 * (x i.succ.castSucc.castSucc : ℤ) - (x i.castSucc.castSucc.castSucc : ℤ)

/-- A228261: the number of third differences of arrays of length 5 of numbers in 0..n. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 5 → Fin (n + 1))).image thirdDiff).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 3 =
      X * (31 + 50 * X - 17 * X ^ 2 + 6 * X ^ 3) ∧
    ∀ n : ℕ, 4 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  sorry

end OMA.S_oeis_a228261
