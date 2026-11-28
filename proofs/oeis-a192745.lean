import OMAStatements.S_oeis_a192745
import Mathlib

/-!
# The linear coefficient of the polynomial recurrence

Expand the three latest polynomials by the defining factorial recursion.
The proposed combination is a multiple of X² − X − 1 plus a constant,
since the two newest factorial contributions cancel. Its remainder
therefore has zero linear coefficient.
-/

namespace OMA.A192745

open Polynomial OMA.S_oeis_a192745

/-- The polynomial used for reduction. -/
private noncomputable def modulus : ℤ[X] := X ^ 2 - X - 1

/-- The divisor has degree two and leading coefficient one. -/
private lemma modulus_spec : modulus.Monic ∧ modulus.degree = 2 := by
  have h : (X + 1 : ℤ[X]).degree = 1 := by
    simpa using (degree_X_add_C (1 : ℤ))
  rw [modulus, sub_sub]
  constructor
  · apply monic_X_pow_sub
    rw [h]
    decide
  · calc
      _ = (X ^ 2 : ℤ[X]).degree := degree_sub_eq_left_of_degree_lt (by
        rw [h, degree_X_pow]
        decide)
      _ = 2 := degree_X_pow 2

/-- The coefficient of X in the remainder of this combination vanishes. -/
private lemma combination (k : ℕ) :
    ((p (k + 3) - ((k : ℤ) + 3) • p (k + 2) +
      ((k : ℤ) + 1) • p (k + 1) + ((k : ℤ) + 2) • p k) %ₘ modulus).coeff 1 = 0 := by
  let F : ℤ := (k + 1).factorial
  have step (j : ℕ) : p (j + 1) = X * p j + C ((j + 1).factorial : ℤ) := by
    simp only [p]
  have const_cast (z : ℤ) : C z = (z : ℤ[X]) := C_eq_intCast z
  have expand : p (k + 3) - ((k : ℤ) + 3) • p (k + 2) +
      ((k : ℤ) + 1) • p (k + 1) + ((k : ℤ) + 2) • p k =
    modulus * ((X - C ((k : ℤ) + 2)) * p k + C F) + C (((k : ℤ) + 2) * F) := by
    rw [step (k + 2), step (k + 1), step k]
    simp only [Nat.factorial_succ (n := k + 2), Nat.factorial_succ (n := k + 1),
      Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, smul_eq_C_mul, modulus, F, const_cast]
    push_cast
    ring
  rw [expand, add_modByMonic, self_mul_modByMonic modulus_spec.1, zero_add]
  rw [(modByMonic_eq_self_iff modulus_spec.1).mpr
    (lt_of_le_of_lt degree_C_le (by rw [modulus_spec.2]; decide))]
  simp

end OMA.A192745

open Polynomial OMA.S_oeis_a192745 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192745.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  have h := A192745.combination k
  simp only [add_modByMonic, sub_modByMonic, smul_modByMonic, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul] at h
  change a (k + 3) - _ * a (k + 2) + _ * a (k + 1) + _ * a k = 0 at h
  push_cast
  linear_combination h
