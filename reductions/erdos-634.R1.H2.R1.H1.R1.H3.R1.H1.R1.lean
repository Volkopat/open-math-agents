import OMAReductions.R_erdos_634_R1_H2_R1_H1_R1_H3_R1

/-!
# Erdos 634, reduction R1.H2.R1.H1.R1.H3.R1.H1.R1

Commensurability of the sides of the tile (α, π/3 - α, 2π/3) on an equilateral T from the theorem
of Beeson and Zhang (H1, Theorem 1.1: T not similar to the tile).

In H1 the tiling is given by cut data T, Ts and a model triangle M (each tile is the image of M under
an isometry of the plane, up to relabelling the vertices); A, B are the angle functions of T and M
and L k is the side of M opposite vertex k. In H2 T is the big triangle, Ts the tiles and t a tile; A, B are the angle functions of T
and of the tile t (A k is the angle at vertex k) and L k is the side of the tile t opposite vertex k.
-/

namespace OMA.R_erdos_634_R1_H2_R1_H1_R1_H3_R1_H1_R1

def H1 : Prop := ∀ (p : ℕ) (T M : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)), ∀ k, f ((Ts i).points k) = M.points (σ k)) → Pairwise (fun i j => Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle (M.points (k + 1)) (M.points k) (M.points (k + 2))) → (∀ k, L k = dist (M.points (k + 1)) (M.points (k + 2))) → ∀ α a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, Real.pi / 3 - α, 2 * Real.pi / 3] ∧ L ∘ σ = ![a, b, c]) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * b) ∧ (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * c)

def H2 : Prop := (∀ (p : ℕ) (T M : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)), ∀ k, f ((Ts i).points k) = M.points (σ k)) → Pairwise (fun i j => Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle (M.points (k + 1)) (M.points k) (M.points (k + 2))) → (∀ k, L k = dist (M.points (k + 1)) (M.points (k + 2))) → ∀ α a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, Real.pi / 3 - α, 2 * Real.pi / 3] ∧ L ∘ σ = ![a, b, c]) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * b) ∧ (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * c)) → ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → (∀ k, L k = dist ((Ts t).points (k + 1)) ((Ts t).points (k + 2))) → (∀ k, A k = Real.pi / 3) → (∀ α a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, Real.pi / 3 - α, 2 * Real.pi / 3] ∧ L ∘ σ = ![a, b, c]) → (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * c) ∧ (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * b = n * c))

theorem main : H1 → H2 → OMA.R_erdos_634_R1_H2_R1_H1_R1_H3_R1.H1 :=
  fun h1 h2 => h2 h1

end OMA.R_erdos_634_R1_H2_R1_H1_R1_H3_R1_H1_R1
