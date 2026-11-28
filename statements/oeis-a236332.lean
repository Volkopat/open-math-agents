import Mathlib

/-!
# OEIS A236332

A236332: the number of orbits of 4-tuples of the dihedral group of order 2n acting on
{1, 2, ..., n}. Data: 1, 8, 14, 36, 63, 112, 172, 260, 365, ... (offset 1).

Colin Barker conjectured (Jan 22 2014) that a(n) = (9 + 7*(-1)^n + 2*n^3)/4
(equivalently, the g.f. -x*(4*x^4-12*x^3+8*x^2-5*x-1)/((x-1)^4*(x+1))).

Formalization: the points 1, ..., n are relabelled 0, ..., n-1 (`Fin n`), with the dihedral group
of order 2n acting as the symmetries of the regular n-gon, that is by the rotations x ↦ c + x and
the reflections x ↦ c - x (mod n), for c in `Fin n`. It acts on 4-tuples coordinatewise. `orbit n t`
is the orbit of the 4-tuple `t`, and `a n` is the number of distinct orbits. The right-hand side
is an exact integer division (the numerator is divisible by 4).
-/

namespace OMA.S_oeis_a236332

/-- The orbit of a 4-tuple `t` over `Fin n` under the dihedral group of order `2n`, acting
coordinatewise by the rotations `x ↦ c + x` and the reflections `x ↦ c - x` (mod `n`). -/
def orbit (n : ℕ) (t : Fin 4 → Fin n) : Finset (Fin 4 → Fin n) :=
  Finset.univ.image fun p : Bool × Fin n => fun i => if p.1 then p.2 - t i else p.2 + t i

/-- A236332(n): the number of orbits of 4-tuples under the dihedral group of order `2n`. -/
def a (n : ℕ) : ℕ := (Finset.univ.image (orbit n)).card

/-- Colin Barker's conjecture: for `n ≥ 1`, `a(n) = (9 + 7*(-1)^n + 2*n^3)/4`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n : ℤ) = (9 + 7 * (-1) ^ n + 2 * (n : ℤ) ^ 3) / 4 := by
  sorry

end OMA.S_oeis_a236332
