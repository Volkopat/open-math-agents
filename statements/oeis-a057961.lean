import Mathlib

/-!
# A057961: lattice points in a quadrant of the growing disc (OEIS A057961)

Source: https://oeis.org/A057961 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @thomasfredrickson.

A057961(n) (offset 1: 1, 5, 9, 13, 21, ...) is the number of points of the
square lattice covered by a disc centered at (0,0) as its radius increases:
the n-th disc has squared radius the n-th sum of two squares 0, 1, 2, 4, 5, ...
(`radiusSq n`, `a n` below).

Formalized here is the conjecture of L. Edson Jeffery (Feb 10 2014) in the
comments: the number of lattice points in a quadrant of the n-th disc equals
A000592(n-1). The quadrant is the closed one (x >= 0 and y >= 0), which is the
reading that matches the data 1, 3, 4, 6, 8, ... of A000592. A000592 (offset 0)
is the number of nonnegative solutions of x^2 + y^2 = z in the first shells:
A000592(m) sums, over the first m + 1 sums of two squares z, the number of
pairs (x, y) of nonnegative integers with x^2 + y^2 = z. The entry reports the
conjecture as true (Flávio V. Fernandes, Jan 09 2026).
-/

namespace OMA.S_oeis_a057961

/-- z is a sum of two squares (A001481). -/
def IsSumTwoSq (z : ℕ) : Prop := ∃ x y : ℕ, x ^ 2 + y ^ 2 = z

/-- The squared radius of the n-th disc (n >= 1): the n-th sum of two squares,
0, 1, 2, 4, 5, 8, ... (`Nat.nth` counts from 0). -/
noncomputable def radiusSq (n : ℕ) : ℕ := Nat.nth IsSumTwoSq (n - 1)

/-- A057961(n): lattice points covered by the n-th disc. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 ≤ (radiusSq n : ℤ)}

/-- Lattice points of the n-th disc in the closed first quadrant. -/
noncomputable def quadrantCount (n : ℕ) : ℕ :=
  Nat.card {p : ℤ × ℤ // 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ (radiusSq n : ℤ)}

/-- A000592(m): nonnegative solutions of x^2 + y^2 = z in the first m + 1 shells
(offset 0: 1, 3, 4, 6, 8, ...). -/
noncomputable def A000592 (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (m + 1), Nat.card {p : ℕ × ℕ // p.1 ^ 2 + p.2 ^ 2 = Nat.nth IsSumTwoSq j}

theorem main : ∀ n : ℕ, 1 ≤ n → quadrantCount n = A000592 (n - 1) := by
  sorry

end OMA.S_oeis_a057961
