import OMAReductions.R_erdos_634_R1_H2_R1_H2_R1

/-!
# Erdos 634, reduction R1.H2.R1.H2.R1.H4.R1

The exceptional denominators of Laczkovich's classification (Bonfioli, exc_dispatch_n), grouped so
that each step fits the size limit: H1 n = 3, 4, 18; H2 n = 6; H3 n = 10; H4 the rest.
A and B are the angle functions of T and of the tile t (A k is the angle at vertex k).
-/

namespace OMA.R_erdos_634_R1_H2_R1_H2_R1_H4_R1

def H1 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → ∀ (n : ℕ) (a : Fin 3 → ℕ), (∀ i, 0 < a i) → ∑ i, a i = n → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ k, B k = (a k : ℝ) * Real.pi / n) → (n = 3 ∨ n = 4 ∨ n = 18) → (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) ∨ (∃ k l : Fin 3, l ≠ k ∧ B k = Real.pi / 2 ∧ ∃ i j : Fin 3, i ≠ j ∧ A i = B l ∧ A j = B l) ∨ ((∀ k, A k = Real.pi / 3) ∧ ∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![Real.pi / 6, Real.pi / 6, 2 * Real.pi / 3] ∨ B ∘ σ = ![Real.pi / 12, Real.pi / 3, 7 * Real.pi / 12] ∨ B ∘ σ = ![Real.pi / 30, Real.pi / 3, 19 * Real.pi / 30] ∨ B ∘ σ = ![7 * Real.pi / 30, Real.pi / 3, 13 * Real.pi / 30])

def H2 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → ∀ (n : ℕ) (a : Fin 3 → ℕ), (∀ i, 0 < a i) → ∑ i, a i = n → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ k, B k = (a k : ℝ) * Real.pi / n) → n = 6 → (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) ∨ (∃ k l : Fin 3, l ≠ k ∧ B k = Real.pi / 2 ∧ ∃ i j : Fin 3, i ≠ j ∧ A i = B l ∧ A j = B l) ∨ ((∀ k, A k = Real.pi / 3) ∧ ∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![Real.pi / 6, Real.pi / 6, 2 * Real.pi / 3] ∨ B ∘ σ = ![Real.pi / 12, Real.pi / 3, 7 * Real.pi / 12] ∨ B ∘ σ = ![Real.pi / 30, Real.pi / 3, 19 * Real.pi / 30] ∨ B ∘ σ = ![7 * Real.pi / 30, Real.pi / 3, 13 * Real.pi / 30])

def H3 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → ∀ (n : ℕ) (a : Fin 3 → ℕ), (∀ i, 0 < a i) → ∑ i, a i = n → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ k, B k = (a k : ℝ) * Real.pi / n) → n = 10 → (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) ∨ (∃ k l : Fin 3, l ≠ k ∧ B k = Real.pi / 2 ∧ ∃ i j : Fin 3, i ≠ j ∧ A i = B l ∧ A j = B l) ∨ ((∀ k, A k = Real.pi / 3) ∧ ∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![Real.pi / 6, Real.pi / 6, 2 * Real.pi / 3] ∨ B ∘ σ = ![Real.pi / 12, Real.pi / 3, 7 * Real.pi / 12] ∨ B ∘ σ = ![Real.pi / 30, Real.pi / 3, 19 * Real.pi / 30] ∨ B ∘ σ = ![7 * Real.pi / 30, Real.pi / 3, 13 * Real.pi / 30])

def H4 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → ∀ (n : ℕ) (a : Fin 3 → ℕ), (∀ i, 0 < a i) → ∑ i, a i = n → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ k, B k = (a k : ℝ) * Real.pi / n) → (n = 8 ∨ n = 12 ∨ n = 24 ∨ n = 30 ∨ n = 60) → (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) ∨ (∃ k l : Fin 3, l ≠ k ∧ B k = Real.pi / 2 ∧ ∃ i j : Fin 3, i ≠ j ∧ A i = B l ∧ A j = B l) ∨ ((∀ k, A k = Real.pi / 3) ∧ ∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![Real.pi / 6, Real.pi / 6, 2 * Real.pi / 3] ∨ B ∘ σ = ![Real.pi / 12, Real.pi / 3, 7 * Real.pi / 12] ∨ B ∘ σ = ![Real.pi / 30, Real.pi / 3, 19 * Real.pi / 30] ∨ B ∘ σ = ![7 * Real.pi / 30, Real.pi / 3, 13 * Real.pi / 30])

theorem main : H1 → H2 → H3 → H4 → OMA.R_erdos_634_R1_H2_R1_H2_R1.H4 := by
  intro g1 g2 g3 g4 p hp hp3 T Ts hc hd hu t A B hA hB n a hpos hsum hg ha hexc
  rcases hexc with h | h | h | h | h | h | h | h | h | h
  · exact g1 p hp hp3 T Ts hc hd hu t A B hA hB n a hpos hsum hg ha (Or.inl h)
  · exact g1 p hp hp3 T Ts hc hd hu t A B hA hB n a hpos hsum hg ha (Or.inr (Or.inl h))
  · exact g2 p hp hp3 T Ts hc hd hu t A B hA hB n a hpos hsum hg ha (h)
  · exact g4 p hp hp3 T Ts hc hd hu t A B hA hB n a hpos hsum hg ha (Or.inl h)
  · exact g3 p hp hp3 T Ts hc hd hu t A B hA hB n a hpos hsum hg ha (h)
  · exact g4 p hp hp3 T Ts hc hd hu t A B hA hB n a hpos hsum hg ha (Or.inr (Or.inl h))
  · exact g1 p hp hp3 T Ts hc hd hu t A B hA hB n a hpos hsum hg ha (Or.inr (Or.inr h))
  · exact g4 p hp hp3 T Ts hc hd hu t A B hA hB n a hpos hsum hg ha (Or.inr (Or.inr (Or.inl h)))
  · exact g4 p hp hp3 T Ts hc hd hu t A B hA hB n a hpos hsum hg ha (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact g4 p hp hp3 T Ts hc hd hu t A B hA hB n a hpos hsum hg ha (Or.inr (Or.inr (Or.inr (Or.inr h))))

end OMA.R_erdos_634_R1_H2_R1_H2_R1_H4_R1
