import OMAReductions.R_erdos_634_R1_H2_R1_H1_R1

/-!
# Erdos 634, reduction R1.H2.R1.H1.R1.H3.R1

The 2π/3 tile: the sides of the tile are commensurable (H1); the core of theorem:notprime120
(H2: with integer sides A, B, C without common factor, the number of tiles does not divide A);
given these, theorem:notprime120 (H3).

In each hypothesis T is the big triangle, Ts the tiles and t a tile; A, B are the angle functions of T
and of the tile t (A k is the angle at vertex k) and L k is the side of the tile t opposite vertex k.
-/

namespace OMA.R_erdos_634_R1_H2_R1_H1_R1_H3_R1

def H1 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → (∀ k, L k = dist ((Ts t).points (k + 1)) ((Ts t).points (k + 2))) → (∀ k, A k = Real.pi / 3) → (∀ α a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, Real.pi / 3 - α, 2 * Real.pi / 3] ∧ L ∘ σ = ![a, b, c]) → (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * c) ∧ (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * b = n * c))

def H2 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → (∀ k, L k = dist ((Ts t).points (k + 1)) ((Ts t).points (k + 2))) → (∀ k, A k = Real.pi / 3) → (∀ α β a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, 2 * Real.pi / 3] ∧ L ∘ σ = ![a, b, c]) → ∀ (A' B' C' : ℕ) (μ : ℝ), 0 < μ → a = μ * A' → b = μ * B' → c = μ * C' → Nat.gcd (Nat.gcd A' B') C' = 1 → p ∣ A' → False)

def H3 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → (∀ k, L k = dist ((Ts t).points (k + 1)) ((Ts t).points (k + 2))) → (∀ k, A k = Real.pi / 3) → (∀ α a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, Real.pi / 3 - α, 2 * Real.pi / 3] ∧ L ∘ σ = ![a, b, c]) → (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * c) ∧ (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * b = n * c)) → (∀ α β a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, 2 * Real.pi / 3] ∧ L ∘ σ = ![a, b, c]) → ∀ (A' B' C' : ℕ) (μ : ℝ), 0 < μ → a = μ * A' → b = μ * B' → c = μ * C' → Nat.gcd (Nat.gcd A' B') C' = 1 → p ∣ A' → False) → ∀ α : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, Real.pi / 3 - α, 2 * Real.pi / 3]) → False

theorem main : H1 → H2 → H3 → OMA.R_erdos_634_R1_H2_R1_H1_R1.H3 :=
  fun h1 h2 h3 p hp h3p T Ts hc hd hu t A B hA hB hEq α hα hBσ =>
    h3 p hp h3p T Ts hc hd hu t A B _ hA hB (fun _ => rfl) hEq
      (h1 p hp h3p T Ts hc hd hu t A B _ hA hB (fun _ => rfl) hEq)
      (h2 p hp h3p T Ts hc hd hu t A B _ hA hB (fun _ => rfl) hEq) α hα hBσ

end OMA.R_erdos_634_R1_H2_R1_H1_R1_H3_R1
