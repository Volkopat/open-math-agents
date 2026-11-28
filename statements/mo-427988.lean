import Mathlib

/-!
# MathOverflow 427988

Source: https://mathoverflow.net/questions/427988
-/

namespace OMA.S_mo_427988

open Finset

def TripleSumset (A : Finset ℤ) : Finset ℤ :=
  (A.product (A.product A)).image (fun p => p.1+p.2.1+p.2.2)

theorem main : ∀ (b : ℤ), 1 ≤ b → ∀ A : Finset ℤ, A ⊆ Icc 0 b →
    Icc 0 b ∪ Icc (2*b) (3*b) ⊆ TripleSumset A → TripleSumset A = Icc 0 (3*b) := by
  sorry

end OMA.S_mo_427988
