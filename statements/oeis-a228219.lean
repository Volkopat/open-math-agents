import Mathlib

/-!
# OEIS A228219: Barker's conjectures for the number of second differences of arrays of length 4 of numbers in 0..n

Source: https://oeis.org/A228219 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A228219 (R. H. Hardin, Aug 16 2013), offset 1: Number of second differences of arrays of
length 4 of numbers in 0..n.
Formula section:
Empirical: a(n) = 10*n^2 + 4*n + 1 = A272039(n).
Conjectures from Colin Barker, Mar 16 2018: (Start)
G.f.: x*(15 + 4*x + x^2) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>3.
(End)

Formalization notes:
* An array of length 4 of numbers in 0..n is a map x : Fin 4 -> Fin (n + 1). Its second
  differences form the array of the two integers x(i) - 2 x(i+1) + x(i+2), i = 0, 1
  (`secondDiff`), and a(n) is the number of distinct such arrays, the size of the image of
  `secondDiff`.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^3 = x (15 + 4x + x^2) in the formal power series ring over the rationals;
  and the recurrence, for every n > 3, as an identity of integers.
* The definition reproduces the entry's data (15, 49, 103, 177, 271, 385, ... from n = 1, checked
  by direct enumeration for n <= 6 and against every listed term through the formula of the
  proof).
-/

namespace OMA.S_oeis_a228219

open PowerSeries Finset

/-- The second differences x(i) - 2 x(i+1) + x(i+2) of an array of length m + 2. -/
def secondDiff {m N : ℕ} (x : Fin (m + 2) → Fin N) : Fin m → ℤ :=
  fun i => (x i.castSucc.castSucc : ℤ) - 2 * (x i.succ.castSucc : ℤ) + (x i.succ.succ : ℤ)

/-- A228219: the number of second differences of arrays of length 4 of numbers in 0..n. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 4 → Fin (n + 1))).image secondDiff).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 3 =
      X * (15 + 4 * X + X ^ 2) ∧
    ∀ n : ℕ, 3 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  sorry

end OMA.S_oeis_a228219
