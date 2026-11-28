import OMAReductions.R_LatinSquare_latinSquareNearTransversal_R1
import Mathlib

/-! Step LatinSquare.latinSquareNearTransversal.R1.H1. An odd-order Latin square isotopic to a
group table has a near-transversal. With `h (L i j) = f i * g j`, the cells `(i, g⁻¹ (f i))`
carry the symbols `h⁻¹ ((f i)²)`. These are distinct because squaring is injective in a group of
odd order (`x = (x²)^((|G|+1)/2)`). So this is even a full transversal, and its first `n - 1`
rows form a near-transversal. -/

namespace OMA.LatinNearH1

/-- In a finite group of odd order, squaring is injective. -/
lemma sq_injective {G : Type} [Group G] [Finite G] (hodd : Odd (Nat.card G)) {x y : G}
    (h : x * x = y * y) : x = y := by
  obtain ⟨k, hk⟩ := hodd
  have hx : x = (x * x) ^ (k + 1) := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = Nat.card G + 1 by omega, pow_succ,
      pow_card_eq_one', one_mul]
  have hy : y = (y * y) ^ (k + 1) := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = Nat.card G + 1 by omega, pow_succ,
      pow_card_eq_one', one_mul]
  rw [hx, hy, h]

theorem main (n : ℕ) (hn : Odd n) (L : LatinSquare n)
    (hL : ∃ (G : Type) (_ : Group G) (f g h : Fin n ≃ G), ∀ i j, h (L.mat i j) = f i * g j) :
    ∃ ρ σ, IsNearTransversal L ρ σ := by
  obtain ⟨G, _, f, g, h, hfg⟩ := hL
  have : Finite G := Finite.of_equiv _ f
  have hcard : Nat.card G = n := by rw [← Nat.card_congr f, Nat.card_eq_fintype_card, Fintype.card_fin]
  let τ : Fin n → Fin n := fun i => g.symm (f i)
  have hτ : Function.Injective τ := fun a b hab => f.injective (g.symm.injective hab)
  have hsym : Function.Injective (fun i => L.mat i (τ i)) := by
    intro a b hab
    have e := congrArg h hab
    simp only [hfg, τ, Equiv.apply_symm_apply] at e
    exact f.injective (sq_injective (hcard ▸ hn) e)
  let ρ : Fin (n - 1) → Fin n := Fin.castLE (Nat.sub_le n 1)
  have hρ : Function.Injective ρ := Fin.castLE_injective _
  exact ⟨ρ, τ ∘ ρ, hρ, hτ.comp hρ, hsym.comp hρ⟩

end OMA.LatinNearH1

theorem OMA.solution : OMA.R_LatinSquare_latinSquareNearTransversal_R1.H1 :=
  OMA.LatinNearH1.main
