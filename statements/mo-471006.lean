import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Real.Basic

/-!
MathOverflow 471006, asked by Dawid Kielak on May 10, 2024.
Source: https://mathoverflow.net/questions/471006/are-there-only-finitely-many-totally-positive-algebraic-integers-of-bounded-heig
Source content license: CC BY-SA 4.0.

This formalizes the polynomial question in the body: monic integer polynomials
whose real roots, counted with multiplicity, lie strictly between zero and K,
and whose sum of roots divided by degree equals t. Positive degree makes this
mean defined. Splitting over the reals requires every root to be real.

The source body imposes no irreducibility or squarefree condition and explicitly
distinguishes this polynomial question from the algebraic-integer title.
The disproof allows repeated factors. It makes no claim about the different
problem restricted to irreducible minimal polynomials.
-/

open Polynomial

namespace OMA.S_mo_471006

def admissible (K t : ℝ) (p : ℤ[X]) : Prop :=
  p.Monic ∧
  0 < p.natDegree ∧
  (p.map (Int.castRingHom ℝ)).Splits ∧
  (∀ x ∈ (p.map (Int.castRingHom ℝ)).roots, 0 < x ∧ x < K) ∧
  (p.map (Int.castRingHom ℝ)).roots.sum / (p.natDegree : ℝ) = t

def P (K t : ℝ) : Set ℤ[X] := {p | admissible K t p}

theorem main : ∀ K t : ℝ, 0 < K → 0 < t → (P K t).Finite := by
  sorry

end OMA.S_mo_471006
