import Mathlib

/-!
# An explicit inverse of the confluent Vandermonde system

Source: Hamed, https://mathoverflow.net/questions/342993 (CC BY-SA 4.0).
Credit: @connoranderson.

The columns are ordered by derivative order and node. Dividing the derivative
of a monomial by its factorial gives the binomial coefficient in each entry.
Distinct nodes are required for invertibility. The construction uses field
operations, polynomial powers and remainders by a monic polynomial.
-/
namespace OMA.S_mo_342993
open Polynomial Matrix
variable {K : Type*} [Field K] {k s : ℕ}

noncomputable def nodal (x : Fin k → K) (s : ℕ) : K[X] := ∏ i, (X-C (x i))^s

noncomputable def localFactor (x : Fin k → K) (s : ℕ) (i : Fin k) : K[X] :=
  let g := ∏ j ∈ Finset.univ.erase i, (X-C (x j))^s
  C ((g.eval (x i))⁻¹) * g

noncomputable def cardinalPoly (x : Fin k → K) (s : ℕ) (i : Fin k) (t : ℕ) : K[X] :=
  ((X-C (x i))^t * (1-(1-localFactor x s i)^s)) %ₘ nodal x s

def confluent (x : Fin k → K) (s : ℕ) : Matrix (Fin (k*s)) (Fin s × Fin k) K :=
  Matrix.of fun r p => (r.val.choose p.1.val : K) * (x p.2)^(r.val-p.1.val)

noncomputable def inverseFormula (x : Fin k → K) (s : ℕ) :
    Matrix (Fin s × Fin k) (Fin (k*s)) K :=
  Matrix.of fun p r => (cardinalPoly x s p.2 p.1.val).coeff r.val

theorem main : ∀ {K : Type} [Field K] (k s : ℕ), 0<k → 0<s →
    ∀ x : Fin k → K, Function.Injective x →
      inverseFormula x s * confluent x s = 1 ∧ confluent x s * inverseFormula x s = 1 ∧
      ∀ (b : Fin (k*s) → K) (v : Fin s × Fin k → K),
        (confluent x s) *ᵥ v = b ↔ v = (inverseFormula x s) *ᵥ b := by
  sorry
end OMA.S_mo_342993
