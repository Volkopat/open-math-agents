import OMAReductions.R_erdos_634_R1_H4_R1_H2_R1

/-!
# Erdos 634, reduction R1.H4.R1.H2.R1.H1.R1

The theorem of Beeson and Zhang (Comm a b and Comm a c for the tile (α, π/3 - α, 2π/3)) from its
key case (H1, Beeson-Zhang Theorem 3.7: if a, b are commensurable then so are a, c) and the rest of
the argument (H2: Lemmas 3.5, 3.6 give Comm a b).

In the hypotheses the tiling is given by cut data T, Ts and a model triangle M (each tile is the
image of M under an isometry of the plane, up to relabelling the vertices); A, B are the angle
functions of T and M (A k is the angle at vertex k) and L k is the side of M opposite vertex k.
-/

namespace OMA.R_erdos_634_R1_H4_R1_H2_R1_H1_R1

def H1 : Prop := ∀ (p : ℕ) (T M : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)), ∀ k, f ((Ts i).points k) = M.points (σ k)) → Pairwise (fun i j => Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle (M.points (k + 1)) (M.points k) (M.points (k + 2))) → (∀ k, L k = dist (M.points (k + 1)) (M.points (k + 2))) → ∀ α a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, Real.pi / 3 - α, 2 * Real.pi / 3] ∧ L ∘ σ = ![a, b, c]) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * b) → (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * c)

def H2 : Prop := (∀ (p : ℕ) (T M : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)), ∀ k, f ((Ts i).points k) = M.points (σ k)) → Pairwise (fun i j => Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle (M.points (k + 1)) (M.points k) (M.points (k + 2))) → (∀ k, L k = dist (M.points (k + 1)) (M.points (k + 2))) → ∀ α a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, Real.pi / 3 - α, 2 * Real.pi / 3] ∧ L ∘ σ = ![a, b, c]) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * b) → (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * c)) → ∀ (p : ℕ) (T M : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)), ∀ k, f ((Ts i).points k) = M.points (σ k)) → Pairwise (fun i j => Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle (M.points (k + 1)) (M.points k) (M.points (k + 2))) → (∀ k, L k = dist (M.points (k + 1)) (M.points (k + 2))) → ∀ α a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, Real.pi / 3 - α, 2 * Real.pi / 3] ∧ L ∘ σ = ![a, b, c]) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * b) ∧ (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * c)

theorem main : H1 → H2 → OMA.R_erdos_634_R1_H4_R1_H2_R1.H1 :=
  fun h1 h2 => h2 h1

end OMA.R_erdos_634_R1_H4_R1_H2_R1_H1_R1
