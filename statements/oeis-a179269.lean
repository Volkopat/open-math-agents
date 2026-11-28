import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Strictly increasing gaps in a partition

OEIS A179269, including the empty partition at index zero.
List the parts from smallest to largest. Starting at part zero and gap
zero, each new gap must strictly exceed the preceding gap. In particular,
the initial part is positive and the first actual gap exceeds that part.

The generating function conjectured by Ilya Gutkovskiy is stated
coefficientwise. For each length k the numerator is a monomial of degree
tetra k = k(k+1)(k+2)/6. A list of k nonnegative multiplicities chooses
one term from each geometric series 1/(1-x^T), for T running through
the triangular numbers from k(k+1)/2 down to 1. Only finitely many lists
can contribute to a fixed degree n since the degree bounds both length
and every multiplicity.

Source: https://oeis.org/A179269
-/

namespace OMA.S_oeis_a179269

def valid (previous gap : ℕ) : List ℕ → Prop
  | [] => True
  | p :: ps => previous + gap < p ∧ valid p (p - previous) ps

def triangular : ℕ → ℕ
  | 0 => 0
  | k + 1 => triangular k + (k + 1)

def tetra : ℕ → ℕ
  | 0 => 0
  | k + 1 => tetra k + triangular (k + 1)

def degree : List ℕ → ℕ
  | [] => 0
  | e :: es => triangular (es.length + 1) * e + degree es

theorem main : ∀ n : ℕ,
    {ps : List ℕ | valid 0 0 ps ∧ ps.sum = n}.ncard =
      {es : List ℕ | tetra es.length + degree es = n}.ncard := by
  sorry

end OMA.S_oeis_a179269
