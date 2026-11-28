import OMAReductions.R_erdos_634_R1_H2_R1_H1_R1_H2_R1

/-!
# Erdos 634, reduction R1.H2.R1.H1.R1.H2.R1.H1.R1

Commensurability of the sides a, b, c of the tile (α, 2π/3 - α, π/3) on an equilateral T
(Laczkovich 2012, Thm 2.1, Case IV, for a triangle): H1, a is a nonnegative rational combination of
b and c (Subcase IVa; applied to α and to 2π/3 - α it gives Subcase IVb, hence a, b commensurable);
H2, if a, b are commensurable then so are a, c (Subcase IVc).

In each hypothesis T is the big triangle, Ts the tiles and t a tile; A, B are the angle functions of T
and of the tile t (A k is the angle at vertex k) and L k is the side of the tile t opposite vertex k.
-/

namespace OMA.R_erdos_634_R1_H2_R1_H1_R1_H2_R1_H1_R1

def H1 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → (∀ k, L k = dist ((Ts t).points (k + 1)) ((Ts t).points (k + 2))) → (∀ k, A k = Real.pi / 3) → ∀ α a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, 2 * Real.pi / 3 - α, Real.pi / 3] ∧ L ∘ σ = ![a, b, c]) → (∀ r m n : ℕ, 0 < r → (r : ℝ) * a ≠ m * b + n * c) → False

def H2 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → (∀ k, L k = dist ((Ts t).points (k + 1)) ((Ts t).points (k + 2))) → (∀ k, A k = Real.pi / 3) → ∀ α a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, 2 * Real.pi / 3 - α, Real.pi / 3] ∧ L ∘ σ = ![a, b, c]) → (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * b) → ¬ (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * c) → False

theorem comb2 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) {r p q : ℕ} (hr : 0 < r)
    (e1 : (r : ℝ) * a = p * b + q * c) {r' p' q' : ℕ} (hr' : 0 < r')
    (e2 : (r' : ℝ) * b = p' * a + q' * c) : ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * b := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp
      have : (0 : ℝ) < r * a := mul_pos (by exact_mod_cast hr) ha
      have e0 : (r : ℝ) * a = 0 := by rw [e1]; simp
      linarith
    · exact ⟨r, p, hr, hp, by simpa using e1⟩
  rcases Nat.eq_zero_or_pos q' with hq' | hq'
  · subst hq'
    rcases Nat.eq_zero_or_pos p' with hp' | hp'
    · subst hp'
      have : (0 : ℝ) < r' * b := mul_pos (by exact_mod_cast hr') hb
      have e0 : (r' : ℝ) * b = 0 := by rw [e2]; simp
      linarith
    · exact ⟨p', r', hp', hr', by simpa using e2.symm⟩
  refine ⟨q * p' + q' * r, q * r' + q' * p, Nat.add_pos_right _ (Nat.mul_pos hq' hr),
    Nat.add_pos_left (Nat.mul_pos hq hr') _, ?_⟩
  push_cast
  linear_combination (q' : ℝ) * e1 - (q : ℝ) * e2

theorem ctrans {x y z : ℝ} (h1 : ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * x = n * y) (h2 : ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * y = n * z) : ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * x = n * z := by
  obtain ⟨p, q, hp, hq, e1⟩ := h1
  obtain ⟨p', q', hp', hq', e2⟩ := h2
  refine ⟨p * p', q * q', Nat.mul_pos hp hp', Nat.mul_pos hq hq', ?_⟩
  push_cast
  linear_combination (p' : ℝ) * e1 + (q : ℝ) * e2

theorem csymm {x y : ℝ} (h : ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * x = n * y) : ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * y = n * x := by
  obtain ⟨p, q, hp, hq, e⟩ := h
  exact ⟨q, p, hq, hp, e.symm⟩

theorem swapT {B L : Fin 3 → ℝ} {σ : Equiv.Perm (Fin 3)} {x y z a b c : ℝ} (h1 : B ∘ σ = ![x, y, z])
    (h2 : L ∘ σ = ![a, b, c]) :
    B ∘ (σ * Equiv.swap (0 : Fin 3) 1) = ![y, x, z] ∧ L ∘ (σ * Equiv.swap (0 : Fin 3) 1) = ![b, a, c] := by
  have a0 : B (σ 0) = x := by simpa using congrFun h1 0
  have a1 : B (σ 1) = y := by simpa using congrFun h1 1
  have a2 : B (σ 2) = z := by simpa using congrFun h1 2
  have b0 : L (σ 0) = a := by simpa using congrFun h2 0
  have b1 : L (σ 1) = b := by simpa using congrFun h2 1
  have b2 : L (σ 2) = c := by simpa using congrFun h2 2
  refine ⟨?_, ?_⟩ <;> funext k <;> fin_cases k <;> simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, a0, a1, a2, b0, b1, b2]

theorem main : H1 → H2 → OMA.R_erdos_634_R1_H2_R1_H1_R1_H2_R1.H1 :=
  by
  intro h1 h3 p hp h3p T Ts hc hd hu t A B L hA hB hL hEq α a b c hα hT ha hb
  obtain ⟨σ, hσ1, hσ2⟩ := hT
  have n1 : ¬ (∀ r m n : ℕ, 0 < r → (r : ℝ) * a ≠ m * b + n * c) := fun h => h1 p hp h3p T Ts hc hd hu t A B L hA hB hL hEq α a b c hα ⟨σ, hσ1, hσ2⟩ h
  have hα' : ¬ ∃ q : ℚ, 2 * Real.pi / 3 - α = q * Real.pi := fun ⟨q, hq⟩ =>
    hα ⟨2 / 3 - q, by push_cast; linarith⟩
  obtain ⟨s1, s2⟩ := swapT hσ1 hσ2
  have n2 : ¬ (∀ r m n : ℕ, 0 < r → (r : ℝ) * b ≠ m * a + n * c) := fun h => h1 p hp h3p T Ts hc hd hu t A B L hA hB hL hEq (2 * Real.pi / 3 - α) b a c hα'
    ⟨σ * Equiv.swap (0 : Fin 3) 1, by rw [s1, sub_sub_cancel], s2⟩ h
  simp only [not_forall, not_not, exists_prop] at n1 n2
  obtain ⟨r, m, n, hr, e1⟩ := n1
  obtain ⟨r', m', n', hr', e2⟩ := n2
  have hab := comb2 ha hb hr e1 hr' e2
  have hac : ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * c := by
    by_contra hac
    exact h3 p hp h3p T Ts hc hd hu t A B L hA hB hL hEq α a b c hα ⟨σ, hσ1, hσ2⟩ hab hac
  exact ⟨hac, ctrans (csymm hab) hac⟩

end OMA.R_erdos_634_R1_H2_R1_H1_R1_H2_R1_H1_R1
