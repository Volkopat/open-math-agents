import Mathlib

/-!
# OEIS A294515: Lang's conjecture a(n) = A250550(n+1)/(n+1)

Source: https://oeis.org/A294515 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Wolfdieter Lang, Nov 02 2017), offset 0: Denominators of partial sums of the reciprocals of
the decagonal numbers. Comment: The positive decagonal numbers are A001107(k+1) = (k + 1)*(4*k + 1),
k >= 0. The formula section states: a(n) = denominator(V(4,1;n)) with V(4,1;n) = Sum_{k=0..n}
1/((k + 1)*(4*k + 1)), and: a(n) = A250550(n+1)/(n+1) [conjecture].
Entry A250550 (offset 1): Numerator of the harmonic mean of the first n 10-gonal numbers.

Formalization notes:
* a(n) is the denominator, in lowest terms, of V(4,1;n). The m-th 10-gonal number is m*(4*m - 3),
  and the harmonic mean of x_1, ..., x_m is m / (1/x_1 + ... + 1/x_m).
* The identity is stated in the rationals, so no integer division is involved.
* Controls (checked by kernel decide in a scratch file): the definitions give a(0..9) = 1, 10,
  270, 7020, 119340, 835380, 4176900, 242260200, 888287400, 32866633800 and A250550(1..5) = 1, 20,
  810, 28080, 596700, as in the entries.
-/

namespace OMA.S_oeis_a294515

/-- V(4,1;n) = Sum_{k=0..n} 1/((k+1)(4k+1)). -/
def V (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), (1 : ℚ) / ((k + 1) * (4 * k + 1))

/-- A294515(n), the denominator of V(4,1;n). -/
def a (n : ℕ) : ℕ := (V n).den

/-- A250550(m), the numerator of the harmonic mean of the first m decagonal numbers. -/
def b (m : ℕ) : ℤ :=
  ((m : ℚ) / ∑ k ∈ Finset.Icc 1 m, (1 : ℚ) / ((k : ℚ) * (4 * k - 3))).num

/-- Lang's conjecture: a(n) = A250550(n+1)/(n+1) for every n >= 0. -/
theorem main : ∀ n : ℕ, (a n : ℚ) = (b (n + 1) : ℚ) / ((n : ℚ) + 1) := by
  sorry

end OMA.S_oeis_a294515
