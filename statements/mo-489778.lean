import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic

/-!
# Maximal Jordan blocks in split orthogonal groups

Source: https://mathoverflow.net/questions/489778
Credit: @etaubman

The source asks whether both O(p,p) and O(p,p+1) exclude a single maximal
Jordan block with diagonal entries 1. We state this joint universal assertion
for positive p. The signature matrix has p positive and q negative entries.
Membership in the orthogonal group means invertibility and preservation of
that form. Similarity to the single Jordan block is expressed by Q*S = S*J
with S invertible, which is equivalent to Q = S*J*S inverse.

The joint assertion is false in the odd dimensional case. The existing answers
of LSpice and Iosif Pinelis give the counterexample used in the accompanying
formal proof. This statement does not assert that the even dimensional case
is false.
-/

namespace OMA.S_mo_489778

def signature (p q : ℕ) : Matrix (Fin (p + q)) (Fin (p + q)) ℝ :=
  Matrix.diagonal (fun i => if i.val < p then 1 else -1)

def jordan (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then 1 else if i.val + 1 = j.val then 1 else 0

theorem main : ∀ p q : ℕ, 0 < p → (q = p ∨ q = p + 1) →
    ∀ Q : Matrix (Fin (p + q)) (Fin (p + q)) ℝ,
      IsUnit Q → Q.transpose * signature p q * Q = signature p q →
      ¬ ∃ S : Matrix (Fin (p + q)) (Fin (p + q)) ℝ,
        IsUnit S ∧ Q * S = S * jordan (p + q) := by
  sorry

end OMA.S_mo_489778
