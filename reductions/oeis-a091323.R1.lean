import OMAStatements.S_oeis_a091323
import Mathlib

/-! Ryser's conjecture: every Latin square of odd order has a transversal. The classical case
is that of squares isotopic to the Cayley table of a group (Euler for cyclic groups, and the
easy direction of the Hall-Paige theorem for all groups of odd order): if
L(i, j) = γ(α(i) β(j)) with bijections α, β, γ onto a group G of odd order 2n + 1, then
x = (x^2)^(n+1) in G, so squaring is injective and σ = β⁻¹ ∘ α gives the transversal
i -> γ(α(i)^2). H1 is this case. H2, the Latin squares of odd order that are not isotopic to
any group table (almost all of them, as the order grows), is the open part. -/

namespace OMA.R_oeis_a091323_R1

/-- A Latin square of odd order isotopic to the Cayley table of a group has a transversal. -/
def H1 : Prop :=
  ∀ (n : ℕ) (L : Fin (2 * n + 1) → Fin (2 * n + 1) → Fin (2 * n + 1)),
    OMA.S_oeis_a091323.IsLatin L →
    (∃ (G : Type) (_ : Group G) (α β : Fin (2 * n + 1) ≃ G) (γ : G ≃ Fin (2 * n + 1)),
      ∀ i j, L i j = γ (α i * β j)) →
    ∃ σ : Equiv.Perm (Fin (2 * n + 1)), Function.Injective fun i => L i (σ i)

/-- The open part: Latin squares of odd order not isotopic to a group table. -/
def H2 : Prop :=
  ∀ (n : ℕ) (L : Fin (2 * n + 1) → Fin (2 * n + 1) → Fin (2 * n + 1)),
    OMA.S_oeis_a091323.IsLatin L →
    (¬ ∃ (G : Type) (_ : Group G) (α β : Fin (2 * n + 1) ≃ G) (γ : G ≃ Fin (2 * n + 1)),
      ∀ i j, L i j = γ (α i * β j)) →
    ∃ σ : Equiv.Perm (Fin (2 * n + 1)), Function.Injective fun i => L i (σ i)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a091323.main := by
  intro h1 h2 n L hL
  by_cases h : ∃ (G : Type) (_ : Group G) (α β : Fin (2 * n + 1) ≃ G) (γ : G ≃ Fin (2 * n + 1)),
      ∀ i j, L i j = γ (α i * β j)
  · exact h1 n L hL h
  · exact h2 n L hL h

end OMA.R_oeis_a091323_R1
