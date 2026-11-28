import Mathlib

/-!
# OEIS A291515: Wu's recurrence and generating function for uhat(n,3,6)

Source: https://oeis.org/A291515 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, Aug 25 2017), offset 1: The arithmetic function uhat(n,3,6). Data: -17, -17,
-19, -17, -17, -19, -17, -17, -19, -20, -22, -24, ... The formula section states: Conjectures from
Chai Wah Wu, Jun 10 2025: (Start) a(n) = 2*a(n-1) - a(n-2) for n > 11. G.f.: x*(-x^10 + x^9 -
2*x^8 - 2*x^7 + 4*x^6 - 2*x^5 - 2*x^4 + 4*x^3 - 2*x^2 + 17*x - 17)/(x - 1)^2. (End)

The entry's Mathematica program, which this formalization follows: delta[r_, k_, d_] := If[r < k,
(k - r)*r - (d - 1), If[k < r && r < d, (d - r)*(r - k) - (d - 1), If[k == r && r == d, d - 1, 0]]];
uhat[n_, m_, h_] := (dx = Divisors[n]; dmin = n; For[i = 1, i <= Length[dx], i++, d = dx[[i]]; k =
m - d*Ceiling[m/d] + d; r = h - d*Ceiling[h/d] + d; If[h <= Min[k, d - 1], dmin = Min[dmin, n,
(h*Ceiling[m/d] - h + 1)*d, h*m - h*h + 1], dmin = Min[dmin, n, h*m - h*h + 1 - delta[r, k, d]]]];
dmin); Table[uhat[n, 3, 6], {n, 1, 70}].

Formalization notes:
* `delta` is the program's delta; `val n m h d` is the value the loop compares with dmin for the
  divisor d (including the program's n); Ceiling[x/d] is `Int.ceil` of the rational x/d.
* `uhat n m h` folds `min` over `Nat.divisors n` starting from n, which is the program's dmin after
  the loop (min is commutative and associative, so the order of the divisors does not matter);
  a(n) = uhat(n, 3, 6).
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) D(x) = N(x) in Z[[x]], which is equivalent because D has constant term 1 or -1.
* `main` is the conjunction of Wu's two conjectures.
* Controls proved in the proof file: a(1..70), all the entry's listed terms.
-/

namespace OMA.S_oeis_a291515

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

/-- A291515(n) = uhat(n, 3, 6). -/
noncomputable def a (n : ℕ) : ℤ := uhat n 3 6

/-- Wu's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 11 < n → a n = 2 * a (n - 1) - a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((X - 1) ^ 2) =
      X * (-X ^ 10 + X ^ 9 - 2 * X ^ 8 - 2 * X ^ 7 + 4 * X ^ 6 - 2 * X ^ 5 - 2 * X ^ 4 + 4 * X ^ 3 -
        2 * X ^ 2 + 17 * X - 17) := by
  sorry

end OMA.S_oeis_a291515
