import Mathlib

/-!
# Polynomial point counts for Manin matrices

Source: Question 1 in [Alexander Chervov's MathOverflow post](https://mathoverflow.net/q/468145).
Credit: @wtho704

For a fixed block size, the proposed polynomial has rational coefficients and works over
all finite fields, including those of nonprime order.
-/

namespace OMA.S_mo_468145

universe u

/-- The Manin relations for the ordered blocks `a, b, c, d`. -/
def ManinRelations {n : ℕ} {K : Type u} [Field K]
    (M : Fin 4 → Matrix (Fin n) (Fin n) K) : Prop :=
  let a := M 0
  let b := M 1
  let c := M 2
  let d := M 3
  a * c = c * a ∧ b * d = d * b ∧ a * d - d * a = c * b - b * c

theorem main :
    ∀ n : ℕ, ∃ P : Polynomial ℚ, ∀ (K : Type u) [Field K] [Fintype K],
      (Nat.card {M : Fin 4 → Matrix (Fin n) (Fin n) K // ManinRelations M} : ℚ) =
        P.eval (Fintype.card K : ℚ) := by
  sorry

end OMA.S_mo_468145
