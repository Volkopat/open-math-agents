import FormalConjectures.Paper.LatinSquare

-- Reduction LatinSquare.latinSquareNearTransversal.R1 of the Brualdi-Stein near-transversal conjecture
-- Credit: @marcusbuffett

/-!
# Near transversals: Cayley tables of odd-order groups, and the open rest

Brualdi's conjecture (Conjecture 5.1 of Wanless's survey): every Latin square has a near
transversal, `n - 1` cells in distinct rows and columns with distinct symbols.

* `H1` (classical, provable): Latin squares of odd order isotopic to the Cayley table of a group,
  `h (L i j) = f i * g j` for bijections `f g h : Fin n ≃ G`. Squaring is a bijection of a group
  of odd order, so the cells `(i, g⁻¹ (f i))` form a full transversal (Euler; the easy half of
  Hall-Paige), and any `n - 1` of them form a near transversal.
* `H2` (open): all other Latin squares, of even order or not isotopic to a group table.

This is the classical case of the conjecture, not progress on it.
-/

namespace OMA.R_LatinSquare_latinSquareNearTransversal_R1

/-- Classical: an odd-order Latin square isotopic to a group Cayley table has a near transversal. -/
def H1 : Prop :=
  ∀ (n : ℕ), Odd n → ∀ (L : LatinSquare n),
    (∃ (G : Type) (_ : Group G) (f g h : Fin n ≃ G), ∀ i j, h (L.mat i j) = f i * g j) →
      ∃ ρ σ, IsNearTransversal L ρ σ

/-- Open: every other Latin square has a near transversal. -/
def H2 : Prop :=
  ∀ (n : ℕ) (L : LatinSquare n),
    ¬ (Odd n ∧
      ∃ (G : Type) (_ : Group G) (f g h : Fin n ≃ G), ∀ i j, h (L.mat i j) = f i * g j) →
      ∃ ρ σ, IsNearTransversal L ρ σ

theorem main : H1 → H2 → type_of% @LatinSquare.latinSquareNearTransversal := by
  intro h1 h2 n L
  by_cases hG : Odd n ∧
      ∃ (G : Type) (_ : Group G) (f g h : Fin n ≃ G), ∀ i j, h (L.mat i j) = f i * g j
  · exact h1 n hG.1 L hG.2
  · exact h2 n L hG

end OMA.R_LatinSquare_latinSquareNearTransversal_R1
