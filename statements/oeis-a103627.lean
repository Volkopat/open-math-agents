import Mathlib

/-!
# A103627: the trigonometric formula, the g.f. and the recurrence for the blocks (k, 1, k)

Source: https://oeis.org/A103627
Credit: @ivillar

Status: known result. Robert Israel (Jan 11 2018) notes that a(3k+1) = 1 and a(3k) = a(3k+2) = k,
and that the conjectures easily follow from that.

A103627 (offset 0): let S(k) = (k, 1, k); the sequence is the concatenation S(0), S(1), S(2), ...;
data 0, 1, 0, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 4, ...
Conjecture (Wesley Ivan Hurt, Sep 25 2017):
a(n) = (2*n+1 + (2*n-8)*cos((2*n+1)*Pi/3) + sqrt(3)*cos((8*n+1)*Pi/6)
  + sqrt(3)*sin((2*n+1)*Pi/3))/9.
Conjectures (Colin Barker, Sep 27 2017):
G.f.: x*(1 + x^2 - x^3 + x^4) / ((1 - x)^2*(1 + x + x^2)^2);
a(n) = 2*a(n-3) - a(n-6) for n > 5.

Formalization notes.
* Each block S(k) has length 3, so the term of index n of the concatenation is the entry of
  index (n mod 3) of the block S(floor(n/3)) = [floor(n/3), 1, floor(n/3)].
* The trigonometric formula is stated over ℝ. The g.f. identity is stated over ℤ⟦X⟧,
  cross-multiplied by the denominator (1-x)^2*(1+x+x^2)^2, whose constant coefficient is 1.
  The recurrence is stated in ℤ for n > 5.
-/

namespace OMA.S_oeis_a103627

open PowerSeries

/-- The block S(k) = (k, 1, k). -/
def S (k : ℕ) : List ℕ := [k, 1, k]

/-- A103627: the concatenation S(0), S(1), S(2), ... of the blocks of length 3. -/
def a (n : ℕ) : ℕ := (S (n / 3)).getD (n % 3) 0

/-- Hurt's trigonometric formula, and Barker's g.f. (cross-multiplied) and recurrence. -/
theorem main :
    (∀ n : ℕ, (a n : ℝ) = (2 * n + 1 + (2 * n - 8) * Real.cos ((2 * n + 1) * Real.pi / 3) +
        Real.sqrt 3 * Real.cos ((8 * n + 1) * Real.pi / 6) +
        Real.sqrt 3 * Real.sin ((2 * n + 1) * Real.pi / 3)) / 9) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X + X ^ 2) ^ 2 : PowerSeries ℤ) =
      X * (1 + X ^ 2 - X ^ 3 + X ^ 4) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 2 * a (n - 3) - a (n - 6)) := by
  sorry

end OMA.S_oeis_a103627
