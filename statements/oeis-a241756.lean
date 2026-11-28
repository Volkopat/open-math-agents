import Mathlib

/-!
# A241756: denominators of Grosjean's sum
Source: https://oeis.org/A241756 (R. J. Mathar, Jun 30 2021, from sequencedb.net)

A241756(n) is the denominator of the rational number
  Sum_{m=0..n} binomial(-1/4, m)^2 * binomial(-1/4, n-m)^2   (offset 0),
where binomial(x, m) = x (x-1) ... (x-m+1) / m! is the generalized binomial coefficient.

Conjecture: a(n) = 8^A005187(n), where A005187 is defined by its title recursion
A005187(0) = 0 and A005187(n) = A005187(floor(n/2)) + n.
The denominator is that of the reduced fraction (Rat.den).
-/

namespace OMA.S_oeis_a241756

/-- Generalized binomial coefficient binomial(x, m) for rational x. -/
def gbinom (x : ℚ) (m : ℕ) : ℚ := (∏ i ∈ Finset.range m, (x - i)) / (m.factorial : ℚ)

/-- Grosjean's sum. -/
def grosjean (n : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (n + 1), gbinom (-1 / 4) m ^ 2 * gbinom (-1 / 4) (n - m) ^ 2

/-- A241756(n): the denominator of the sum. -/
def a (n : ℕ) : ℕ := (grosjean n).den

/-- A005187: a(0) = 0, a(n) = a(floor(n/2)) + n. -/
def A005187 : ℕ → ℕ
  | 0 => 0
  | n + 1 => A005187 ((n + 1) / 2) + (n + 1)

theorem main : ∀ n : ℕ, a n = 8 ^ A005187 n := by
  sorry

end OMA.S_oeis_a241756
