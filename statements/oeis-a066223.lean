import Mathlib

/-!
# A066223: Mathar's recurrence for the bisection of the involution numbers

Source: https://oeis.org/A066223
Credit: @ivillar

Status: known result (Emanuele Munarini, Aug 31 2017, cited below, remarks that the conjectured
recurrence is true).

A000085 (offset 0) counts the self-inverse permutations (involutions) of n letters:
1, 1, 2, 4, 10, 26, 76, ... A066223 (offset 0) is its bisection a(n) = A000085(2n):
1, 2, 10, 76, 764, 9496, ...
Conjecture (R. J. Mathar, Nov 24 2012): a(n) + 2*(-2*n+1)*a(n-1) + 2*(n-1)*(2*n-3)*a(n-2) = 0.
Emanuele Munarini (Aug 31 2017) remarks that the conjectured recurrence is true and can be
obtained from the e.g.f.

Formalization notes.
* A000085 is given by its classical recurrence t(0) = t(1) = 1, t(n) = t(n-1) + (n-1)*t(n-2)
  for n ≥ 2 (listed in A000085; it counts involutions by whether the last letter is fixed or
  paired with one of the other n-1 letters). The terms are computed in ℤ.
* The recurrence is stated for every n ≥ 2, i.e. wherever all three terms exist.
-/

namespace OMA.S_oeis_a066223

/-- A000085, the number of involutions of n letters: t(0) = t(1) = 1,
t(n) = t(n-1) + (n-1)*t(n-2). -/
def t : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => t (n + 1) + ((n : ℤ) + 1) * t n

/-- A066223: the bisection a(n) = A000085(2n). -/
def a (n : ℕ) : ℤ := t (2 * n)

/-- Mathar's recurrence, for every n ≥ 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    a n + 2 * (-2 * (n : ℤ) + 1) * a (n - 1) + 2 * ((n : ℤ) - 1) * (2 * (n : ℤ) - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a066223
