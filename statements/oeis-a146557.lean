/-
OEIS A146557, divisibility conjecture of Peter Bala (July 24, 2025).
Source: https://oeis.org/A146557
Credit: @Heart-galaxy
Text credit: OEIS Foundation, CC BY-SA 4.0.

The sequence starts at n = 1. We use unordered three-element sets, as in the
title's count of collinear triples and the listed value a(3) = 6. Reading the
matrix description as a count of ordered rows instead would give 36 at n = 3.
Collinearity here means vanishing determinant over `ZMod n`, as specified by
that description.
-/

import Mathlib

namespace OMA.S_oeis_a146557

abbrev Point (n : ℕ) := ZMod n × ZMod n

/-- Three points with distinct first and distinct second coordinates and zero
three-point determinant. -/
def valid {n : ℕ} (s : Finset (Point n)) : Prop :=
  s.card = 3 ∧
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → x.1 ≠ y.1 ∧ x.2 ≠ y.2) ∧
    (∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s,
      (y.1 - x.1) * (z.2 - x.2) = (z.1 - x.1) * (y.2 - x.2))

noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {s : Finset (Point n) // valid s}

theorem main : ∀ n : ℕ, 0 < n → ¬ 3 ∣ n → n ^ 2 ∣ a n := by
  sorry

end OMA.S_oeis_a146557
