import Mathlib

/-!
# A236283: The number of orbits of triples of {1,2,...,n} under the action of the dihedral group of order 2n.

Source: https://oeis.org/A236283
Credit: @rtflynn

The conjectures listed in the entry (Colin Barker, Jan 2014), stated below as one conjunction:
* a(n) = (5 + 3*(-1)^n + 2*n^2)/4.
* a(n) = 2*a(n-1) - 2*a(n-3) + a(n-4).
* G.f.: -x*(2*x^3-3*x^2+2*x+1) / ((x-1)^3*(x+1)).
The recurrence involves a(n-4) and the offset is 1, so it is stated for n ≥ 5.

Conventions:
* The set {1, 2, ..., n} is the vertex set of the regular n-gon, labelled here by `ZMod n`
  (vertex j + 1 of the entry is `j : ZMod n`). The dihedral group of order 2n is Mathlib's
  `DihedralGroup n`, acting by its symmetries: the rotation `r i` sends x to x + i and the
  reflection `sr i` sends x to -i - x (these formulas respect the multiplication of
  `DihedralGroup n`, see `instance` below, and give all 2n symmetries of the n-gon).
* The group acts on 3-tuples (words of length 3) coordinatewise (Mathlib's `Pi.mulAction`), and
  a(n) is the number of orbits, `Nat.card` of the orbit quotient; offset 1, data
  1, 4, 5, 10, 13, 20, 25, 34, 41, 52, ...
* The g.f. of the entry is the series sum over n ≥ 1 of a(n) x^n, so its coefficient at x^0 is 0.
-/

namespace OMA.S_oeis_a236283

/-- The symmetries of the regular n-gon with vertices `ZMod n`: `r i` is the rotation x ↦ x + i,
`sr i` the reflection x ↦ -i - x. -/
def act (n : ℕ) : DihedralGroup n → ZMod n → ZMod n
  | .r i, x => x + i
  | .sr i, x => -i - x

instance (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  smul := act n
  one_smul x := show act n (DihedralGroup.r 0) x = x by simp [act]
  mul_smul g h x := show act n (g * h) x = act n g (act n h x) by
    cases g <;> cases h <;> simp only [act, DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr] <;> ring

/-- A236283(n): the number of orbits of 3-tuples of vertices of the n-gon under the dihedral group of order 2n. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card (MulAction.orbitRel.Quotient (DihedralGroup n) (Fin 3 → ZMod n))

open PowerSeries in
/-- Barker's conjectures for A236283. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (5 + 3 * (-1) ^ n + 2 * (n : ℚ) ^ 2) / 4) ∧
    (∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 3) + a (n - 4)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) * ((X - 1) ^ 3 * (X + 1) : ℚ⟦X⟧) =
      -X * (2 * X ^ 3 - 3 * X ^ 2 + 2 * X + 1) := by
  sorry

end OMA.S_oeis_a236283
