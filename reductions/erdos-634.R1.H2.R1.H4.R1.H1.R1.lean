import OMAReductions.R_erdos_634_R1_H2_R1_H4_R1

/-!
# Erdos 634, reduction R1.H2.R1.H4.R1.H1.R1

T equilateral, tiled by a prime number of congruent tiles with one of four exceptional shapes,
one hypothesis per shape:
* H1: (pi/6, pi/6, 2pi/3), from theorem:equilateral (the sides of T are u + q√3 times a tile side);
* H2: (pi/12, pi/3, 7pi/12), H3: (pi/30, pi/3, 19pi/30), H4: (7pi/30, pi/3, 13pi/30), which
  Laczkovich excludes by his graph argument.
A and B are the angle functions of T and of the tile t (A k is the angle at vertex k).
-/

namespace OMA.R_erdos_634_R1_H2_R1_H4_R1_H1_R1

def H1 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → (∀ k, A k = Real.pi / 3) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![Real.pi / 6, Real.pi / 6, 2 * Real.pi / 3]) → False

def H2 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → (∀ k, A k = Real.pi / 3) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![Real.pi / 12, Real.pi / 3, 7 * Real.pi / 12]) → False

def H3 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → (∀ k, A k = Real.pi / 3) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![Real.pi / 30, Real.pi / 3, 19 * Real.pi / 30]) → False

def H4 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → (∀ k, A k = Real.pi / 3) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![7 * Real.pi / 30, Real.pi / 3, 13 * Real.pi / 30]) → False

theorem main : H1 → H2 → H3 → H4 → OMA.R_erdos_634_R1_H2_R1_H4_R1.H1 := by
  intro g1 g2 g3 g4 p hp hp3 T Ts hc hd hu t A B hA hB _ heq hσ
  obtain ⟨σ, h | h | h | h⟩ := hσ
  · exact g1 p hp hp3 T Ts hc hd hu t A B hA hB heq ⟨σ, h⟩
  · exact g2 p hp hp3 T Ts hc hd hu t A B hA hB heq ⟨σ, h⟩
  · exact g3 p hp hp3 T Ts hc hd hu t A B hA hB heq ⟨σ, h⟩
  · exact g4 p hp hp3 T Ts hc hd hu t A B hA hB heq ⟨σ, h⟩

end OMA.R_erdos_634_R1_H2_R1_H4_R1_H1_R1
