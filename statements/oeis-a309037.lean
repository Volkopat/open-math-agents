import Mathlib

/-!
# OEIS A309037: Barker's g.f., closed form and recurrence for the exponential Demlo numbers of 2

Source: https://oeis.org/A309037 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Eliora Ben-Gurion, Jul 08 2019), offset 1: Exponential Demlo sequence, like
12345...54321, but for powers of 2 instead. Data: 2, 242, 24842, 2496842, 249936842, ...
Formula: a(n) = 2^1*10^0 + 2^2*10^1 + ... + 2^(n-1)*10^(n-2) + 2^n*10^(n-1) + 2^(n-1)*10^n +
2^(n-2)*10^(n+1) + ... + 2^2*10^(2n-3) + 2^1*10^(2n-2). Conjectures from Colin Barker, Jul 16
2019: G.f.: 2*x*(1 - 10*x)*(1 + 10*x) / ((1 - x)*(1 - 20*x)*(1 - 100*x)).
a(n) = (-80 - 3*4^n*5^(1+n) + 19*100^n) / 760. a(n) = 121*a(n-1) - 2120*a(n-2) + 2000*a(n-3)
for n>3.

Formalization notes:
* The name is informal; the definition follows the entry's formula line (as does its worked
  example for n = 4): the terms 2^(k+1) 10^k for k = 0..n-1 and 2^(k+1) 10^(2n-2-k) for
  k = 0..n-2.
* The g.f. is Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x)*D(x) = N(x) in Q[[x]], which is
  equivalent to A = N/D because D has constant term 1.
* The closed form is stated in Q for every n >= 1 and the recurrence in Z for every n > 3.
* `main` is the conjunction of Barker's three conjectures.
* Controls proved in the proof file: a(1..10) = 2, 242, 24842, 2496842, 249936842, 24998736842,
  2499974736842, 249999494736842, 24999989894736842, 2499999797894736842, the entry's data.
-/

namespace OMA.S_oeis_a309037

open PowerSeries Finset

/-- A309037, offset 1, as in the entry's formula: the digits 2, 4, ..., 2^n, ..., 4, 2 placed
at the powers 10^0, ..., 10^(n-1), ..., 10^(2n-2). -/
def a (n : ℕ) : ℕ :=
  (∑ k ∈ range n, 2 ^ (k + 1) * 10 ^ k) + ∑ k ∈ range (n - 1), 2 ^ (k + 1) * 10 ^ (2 * n - 2 - k)

/-- Barker's conjectures: the g.f., the closed form and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 20 * X) * (1 - 100 * X)) = 2 * X * (1 - 10 * X) * (1 + 10 * X) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (-80 - 3 * 4 ^ n * 5 ^ (1 + n) + 19 * 100 ^ n) / 760) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 121 * a (n - 1) - 2120 * a (n - 2) + 2000 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a309037
