import Mathlib

/-!
# Monomials in the algebraic normal form of majority

The squarefree monomial indexed by a set S has coefficient equal to the
sum in GF(2) of the truth-table entries at all subsets of S (Boolean
Möbius inversion). The threshold is the ceiling of n/2, including tied
votes when n is even. OEIS A397434 starts with n = 1.
-/
namespace OMA.S_oeis_a397434
open Finset

def coefficient {α : Type*} (t : ℕ) (s : Finset α) : ℕ :=
  (∑ u ∈ s.powerset, if t ≤ u.card then 1 else 0) % 2

def monomials (n : ℕ) : ℕ :=
  ∑ s ∈ (univ : Finset (Fin n)).powerset, coefficient ((n+1)/2) s

theorem main : ∀ n : ℕ, 1 ≤ n → (monomials n = monomials (n+1) ↔ n % 4 = 2) := by
  sorry

end OMA.S_oeis_a397434
