import OMAReductions.R_erdos_634_R1_H4_R1_H3_R1

/-!
# Erdos 634, reduction R1.H4.R1.H3.R1.H1.R1

Splits the two independent Group 1 theorems bundled in R1.H4.R1.H3.R1.H1 (tile (α, β, 2α + β)
with 3α + 2β = π and α not a rational multiple of π):
* H1: rationality of the tile whenever T is not similar to it (Beeson-Rosu, theorem:rationaltile).
* H2: the j = 1 case of theorem:triquadratic (when T has angles (2α, β, α + β) and the tile has
  sides (m*k, k^2 - m^2, k^2) with 0 < m < k coprime, the number of tiles is not 2*k^2 - m^2).
-/

namespace OMA.R_erdos_634_R1_H4_R1_H3_R1_H1_R1

def H1 : Prop := ∀ (p : ℕ) (T M : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)), ∀ k, f ((Ts i).points k) = M.points (σ k)) → Pairwise (fun i j => Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle (M.points (k + 1)) (M.points k) (M.points (k + 2))) → (∀ k, L k = dist (M.points (k + 1)) (M.points (k + 2))) → ∀ α β γ a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → 3 * α + 2 * β = Real.pi → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, γ] ∧ L ∘ σ = ![a, b, c]) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∃ q : ℚ, a / c = q) ∧ (∃ q : ℚ, b / c = q) ∧ (∃ q : ℚ, a / b = q)

def H2 : Prop := ∀ (p : ℕ) (T M : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)), ∀ k, f ((Ts i).points k) = M.points (σ k)) → Pairwise (fun i j => Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle (M.points (k + 1)) (M.points k) (M.points (k + 2))) → (∀ k, L k = dist (M.points (k + 1)) (M.points (k + 2))) → ∀ α β γ a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → 3 * α + 2 * β = Real.pi → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, γ] ∧ L ∘ σ = ![a, b, c]) → ∀ m k : ℤ, 0 < m → m < k → IsCoprime m k → a = m * k → b = k ^ 2 - m ^ 2 → c = k ^ 2 → A = ![2 * α, β, α + β] → (p : ℝ) ≠ 2 * k ^ 2 - m ^ 2

theorem main : H1 → H2 → OMA.R_erdos_634_R1_H4_R1_H3_R1.H1 :=
  fun h1 h2 p T M Ts hc hd hu A B L hA hB hL α β γ a b c hα hrel hBL =>
    ⟨h1 p T M Ts hc hd hu A B L hA hB hL α β γ a b c hα hrel hBL,
     h2 p T M Ts hc hd hu A B L hA hB hL α β γ a b c hα hrel hBL⟩

end OMA.R_erdos_634_R1_H4_R1_H3_R1_H1_R1
