import Mathlib

/-!
# Vandermonde matrices twisted by roots of unity

Source: Anadim, https://mathoverflow.net/questions/66493 (CC BY-SA 3.0).
Credit: @connoranderson.

In the comments the author asks for a deterministic choice over a finite field
of unrestricted order for given exponents and roots of unity. For distinct
nonnegative exponents over any finite coefficient field F, a single element t
in a finite extension works simultaneously for every entrywise nonzero twist:
specialize x_j = t^(d_j). The same t works for every polynomial over F of
degree at most the sum of the squared exponents. With a repeated exponent the
all-ones twist is already singular for every choice of the x_j. The first
claim exhibits failure of the general determinant inequality in dimension two.
-/

namespace OMA.S_mo_66493

open Polynomial

def twisted {n : ℕ} {F K : Type} [Field F] [Field K] [Algebra F K]
    (d : Fin n → ℕ) (R : Matrix (Fin n) (Fin n) F) (x : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  fun i j => algebraMap F K (R i j) * (x j)^(d i)

theorem main :
    (∃ A B : Matrix (Fin 2) (Fin 2) ℝ, 0<A.det ∧ 0<B.det ∧ (A.hadamard B).det=0) ∧
    (∀ (F : Type) [Field F] [Fintype F] (n : ℕ) (d : Fin n → ℕ),
      (Function.Injective d →
        ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra F K) (t : K),
          (∀ p : F[X], p≠0 → p.natDegree ≤ ∑ i, (d i)^2 → aeval t p ≠ 0) ∧
          ∀ R : Matrix (Fin n) (Fin n) F, (∀ i j, R i j ≠ 0) →
            (twisted d R (fun j => t^(d j))).det ≠ 0) ∧
      (¬ Function.Injective d → ∀ (K : Type) [Field K] [Algebra F K] (x : Fin n → K),
        (twisted d (fun _ _ => (1:F)) x).det = 0)) := by
  sorry

end OMA.S_mo_66493
