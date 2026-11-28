import OMAReductions.R_LatinSquare_oddOrderLatinSquareTransversal_R1

/-! If L i j = γ (α i * β j) for a group G of odd order n = 2k + 1, take σ = β⁻¹ ∘ α. Then σ is
injective and L i (σ i) = γ (α i * α i). Squaring is injective in a group of order 2k + 1, since
x = x^(2k+2) = (x * x)^(k+1). -/

namespace OMA.LatinOdd

theorem sq_inj {G : Type} [Group G] (k : ℕ) (hc : Nat.card G = 2 * k + 1) {x y : G}
    (h : x * x = y * y) : x = y := by
  have hx : ∀ z : G, z = (z * z) ^ (k + 1) := by
    intro z
    rw [← sq, ← pow_mul, show 2 * (k + 1) = Nat.card G + 1 by omega, pow_succ,
      pow_card_eq_one', one_mul]
  rw [hx x, hx y, h]

end OMA.LatinOdd

theorem OMA.solution : OMA.R_LatinSquare_oddOrderLatinSquareTransversal_R1.H1 := by
  rintro n ⟨k, hk⟩ L ⟨G, inst, α, β, γ, hL⟩
  have hcard : Nat.card G = 2 * k + 1 := by
    rw [← hk, Nat.card_congr α.symm, Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun i => β.symm (α i), ?_, ?_⟩
  · intro i j hij
    exact α.injective (β.symm.injective hij)
  · intro i j hij
    simp only [hL, Equiv.apply_symm_apply] at hij
    exact α.injective (OMA.LatinOdd.sq_inj k hcard (γ.injective hij))
