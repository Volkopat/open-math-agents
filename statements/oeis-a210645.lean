import Mathlib

/-!
# A210645: Area A of the triangles such that A, the sides and one of the altitudes are four consecutive integers of an arithmetic progression d.

Source: https://oeis.org/A210645
Credit: @agchua

Colin Barker (Apr 19 2012), in the formula section of A210645:
  Conjecture: a(n) = 84*n^2. a(n) = 3*a(n-1)-3*a(n-2)+a(n-3). G.f.: 84*x*(1+x)/(1-x)^3.
This file states all three parts (offset 1): a(n) = 84 n^2 for n ≥ 1; the recurrence for n ≥ 4,
so that all indices are terms; and the g.f. as an identity of formal power series over ℚ,
(∑_{n ≥ 1} a(n) X^n) * (1 - X)^3 = 84 X (1 + X), the series having coefficient 0 at X^0.

Definition, from the entry's comment and Maple program (Michel Lagneau): the sides and one of
the altitudes are q+d, q, q-d and q-2d for integers d ≥ 1 and q > 2d (q > 2d is the program's
condition s > 0 for a proper triangle with a positive altitude q-2d); the area A is a natural
number with 16 A^2 = (x+y+z)(-x+y+z)(x-y+z)(x+y-z) for the sides x, y, z (Heron's formula; the
program requires the area to be an integer); and q-2d is the altitude to one of the sides,
2 A = (q-2d) * side. The sequence lists these areas in increasing order, so a(n) is the n-th
smallest of them, Nat.nth with index n - 1.
-/

namespace OMA.S_oeis_a210645

/-- Heron's expression (x+y+z)(-x+y+z)(x-y+z)(x+y-z), which is 16 * area^2 for sides x, y, z. -/
def heron (x y z : ℤ) : ℤ := (x + y + z) * (-x + y + z) * (x - y + z) * (x + y - z)

/-- A is the area of a triangle with sides q+d, q, q-d and an altitude q-2d (d ≥ 1, q > 2d). -/
def IsArea (A : ℕ) : Prop :=
  ∃ q d : ℤ, 0 < d ∧ 2 * d < q ∧ 16 * (A : ℤ) ^ 2 = heron (q + d) q (q - d) ∧
    (2 * (A : ℤ) = (q - 2 * d) * (q + d) ∨ 2 * (A : ℤ) = (q - 2 * d) * q ∨
      2 * (A : ℤ) = (q - 2 * d) * (q - d))

/-- A210645 (offset 1): a(n) is the n-th smallest such area. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsArea (n - 1)

/-- Barker's conjectures: a(n) = 84 n^2, a(n) = 3a(n-1) - 3a(n-2) + a(n-3), and the g.f.
84x(1+x)/(1-x)^3. -/
theorem main : (∀ n : ℕ, 1 ≤ n → a n = 84 * n ^ 2) ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - PowerSeries.X) ^ 3 =
      84 * PowerSeries.X * (1 + PowerSeries.X) := by
  sorry

end OMA.S_oeis_a210645
