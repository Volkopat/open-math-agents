import FormalConjectures.Paper.LatinSquare
import Mathlib

/-!
Reduction LatinSquare.oddOrderLatinSquareTransversal.R1 (Ryser's conjecture for odd order).

Split by the algebraic structure of the square.

H1 is the classical group case: a Latin square of odd order that is isotopic to the Cayley table
of a group, `L i j = γ (α i * β j)` for bijections `α β : Fin n ≃ G` and `γ : G ≃ Fin n`, has a
transversal. In a group of odd order squaring is a bijection (`x = (x * x) ^ ((|G| + 1) / 2)`),
so the cells `(i, β⁻¹ (α i))` carry the distinct symbols `γ (α i * α i)`. This is the easy half of
the Hall-Paige theory (Euler for cyclic groups, Hall and Paige 1955 for odd order); it covers all
group-based squares of odd order, not progress on the conjecture.

H2 is the open remainder: Latin squares of odd order that are not isotopic to any group table.
-/

namespace OMA.R_LatinSquare_oddOrderLatinSquareTransversal_R1

open LatinSquare

/-- Group-based squares of odd order have a transversal. -/
def H1 : Prop :=
  ∀ (n : ℕ), Odd n → ∀ (L : LatinSquare n),
    (∃ (G : Type) (_ : Group G) (α β : Fin n ≃ G) (γ : G ≃ Fin n),
      ∀ i j, L.mat i j = γ (α i * β j)) →
    ∃ σ, IsTransversal L σ

/-- The open remainder: squares of odd order not isotopic to a group table. -/
def H2 : Prop :=
  ∀ (n : ℕ), Odd n → ∀ (L : LatinSquare n),
    (¬ ∃ (G : Type) (_ : Group G) (α β : Fin n ≃ G) (γ : G ≃ Fin n),
      ∀ i j, L.mat i j = γ (α i * β j)) →
    ∃ σ, IsTransversal L σ

theorem main : H1 → H2 → type_of% @LatinSquare.oddOrderLatinSquareTransversal := by
  intro h1 h2 n hn L
  by_cases h : ∃ (G : Type) (_ : Group G) (α β : Fin n ≃ G) (γ : G ≃ Fin n),
      ∀ i j, L.mat i j = γ (α i * β j)
  · exact h1 n hn L h
  · exact h2 n hn L h

end OMA.R_LatinSquare_oddOrderLatinSquareTransversal_R1
