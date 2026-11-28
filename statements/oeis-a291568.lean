import Mathlib

/-!
# OEIS A291568: Wu's recurrence and generating function for uhat(n,5,5)

Source: https://oeis.org/A291568 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, Aug 26 2017), offset 1: The arithmetic function uhat(n,5,5). Data: 1, 1, 1, 1,
-3, 1, 1, 1, 1, -3, 1, 1, ... The formula section states: Conjectures from Chai Wah Wu, Jun 10 2025:
(Start) a(n) = a(n-5) for n > 5. G.f.: x*(3*x^4 - x^3 - x^2 - x - 1)/(x^5 - 1). (End)

The entry's Mathematica program, which this formalization follows: delta[r_, k_, d_] := If[r < k,
(k - r)*r - (d - 1), If[k < r && r < d, (d - r)*(r - k) - (d - 1), If[k == r && r == d, d - 1, 0]]];
uhat[n_, m_, h_] := (dx = Divisors[n]; dmin = n; For[i = 1, i <= Length[dx], i++, d = dx[[i]]; k =
m - d*Ceiling[m/d] + d; r = h - d*Ceiling[h/d] + d; If[h <= Min[k, d - 1], dmin = Min[dmin, n,
(h*Ceiling[m/d] - h + 1)*d, h*m - h*h + 1], dmin = Min[dmin, n, h*m - h*h + 1 - delta[r, k, d]]]];
dmin); Table[uhat[n, 5, 5], {n, 1, 70}].

Formalization notes:
* `delta` is the program's delta; `val n m h d` is the value the loop compares with dmin for the
  divisor d (including the program's n); Ceiling[x/d] is `Int.ceil` of the rational x/d.
* `uhat n m h` folds `min` over `Nat.divisors n` starting from n, which is the program's dmin after
  the loop (min is commutative and associative, so the order of the divisors does not matter);
  a(n) = uhat(n, 5, 5).
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) D(x) = N(x) in Z[[x]], which is equivalent because D has constant term 1 or -1.
* `main` is the conjunction of Wu's two conjectures.
* Controls proved in the proof file: a(1..70), all the entry's listed terms.
-/

namespace OMA.S_oeis_a291568

open PowerSeries

/-- The function delta[r, k, d] of the entry's program. -/
def delta (r k d : ℤ) : ℤ :=
  if r < k then (k - r) * r - (d - 1)
  else if k < r ∧ r < d then (d - r) * (r - k) - (d - 1)
  else if k = r ∧ r = d then d - 1 else 0

/-- The value that the program's loop compares with dmin for the divisor d of n. -/
noncomputable def val (n m h d : ℕ) : ℤ :=
  if (h : ℤ) ≤ min ((m : ℤ) - d * ⌈(m : ℚ) / d⌉ + d) ((d : ℤ) - 1) then
    min (n : ℤ) (min ((h * ⌈(m : ℚ) / d⌉ - h + 1) * d) (h * m - h * h + 1))
  else
    min (n : ℤ) (h * m - h * h + 1 -
      delta (h - d * ⌈(h : ℚ) / d⌉ + d) (m - d * ⌈(m : ℚ) / d⌉ + d) d)

/-- uhat(n, m, h): dmin starts at n and is lowered by the value of every divisor of n. -/
noncomputable def uhat (n m h : ℕ) : ℤ := (Nat.divisors n).fold min (n : ℤ) (fun d => val n m h d)

/-- A291568(n) = uhat(n, 5, 5). -/
noncomputable def a (n : ℕ) : ℤ := uhat n 5 5

/-- Wu's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 5 < n → a n = a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (X ^ 5 - 1) =
      X * (3 * X ^ 4 - X ^ 3 - X ^ 2 - X - 1) := by
  sorry

end OMA.S_oeis_a291568
