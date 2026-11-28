import OMAReductions.R_Erdos651_erdos_651_R1_H1_R1_H1_R1

/-!
The geometric and finite ordering parts of Pohoata and Zakharov,
"Convex polytopes from fewer points", Section 3.
https://arxiv.org/html/2208.04878#S3
-/

open scoped Affine EuclideanGeometry

namespace OMA.R_Erdos651_erdos_651_R1_H1_R1_H1_R1_H2_R1

private theorem affine_coordinate_change (e : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3))
    (s t : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0) :
    ∃ f : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3), ∀ x i, f x i = s i * e x i + t i := by
  let c : (ℝ^3) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
    (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).toLinearEquiv
  let L : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
    { toFun := fun x i => s i * x i
      invFun := fun x i => (s i)⁻¹ * x i
      left_inv := by
        intro x
        ext i
        change (s i)⁻¹ * (s i * x i) = x i
        rw [← mul_assoc, inv_mul_cancel₀ (hs i), one_mul]
      right_inv := by
        intro x
        ext i
        change s i * ((s i)⁻¹ * x i) = x i
        rw [← mul_assoc, mul_inv_cancel₀ (hs i), one_mul]
      map_add' := by
        intro x y
        ext i
        exact mul_add (s i) (x i) (y i)
      map_smul' := by
        intro a x
        ext i
        change s i * (a * x i) = a * (s i * x i)
        ring }
  let shift : (Fin 3 → ℝ) ≃ᵃ[ℝ] (Fin 3 → ℝ) := AffineEquiv.constVAdd ℝ _ t
  let f := ((e.trans (c.trans L).toAffineEquiv).trans shift).trans c.symm.toAffineEquiv
  refine ⟨f, fun x i => ?_⟩
  change t i + s i * e x i = s i * e x i + t i
  exact add_comm _ _

private theorem affine_coordinate_signs (e : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3)) (ε : ℝ) :
    ∃ (U D : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3)),
      (∀ x, U x 0 = e x 0 ∧ U x 1 = -e x 1 + ε ∧ U x 2 = -e x 2 + ε) ∧
      (∀ x, D x 0 = e x 0 ∧ D x 1 = e x 1 + ε ∧ D x 2 = e x 2 + ε) := by
  let shift : Fin 3 → ℝ := fun i => if i = 0 then 0 else ε
  obtain ⟨U, hU⟩ := affine_coordinate_change e
    (fun i => if i = 0 then 1 else -1) shift (fun i => by split <;> norm_num)
  obtain ⟨D, hD⟩ := affine_coordinate_change e (fun _ => 1) shift (fun _ => one_ne_zero)
  refine ⟨U, D, fun x => ?_, fun x => ?_⟩
  · exact ⟨by simpa [shift] using hU x 0, by simpa [shift] using hU x 1,
      by simpa [shift] using hU x 2⟩
  · exact ⟨by simpa [shift] using hD x 0, by simpa [shift] using hD x 1,
      by simpa [shift] using hD x 2⟩

/-- The planar cap or cup and the cluster separation supply affine coordinates
with the three sign patterns. The two outer families can be separated with a
positive margin because only finitely many prescribed points must be retained. -/
def H1 : Prop :=
  ∀ k : ℕ, ∃ B : ℕ, ∀ X : Finset (ℝ^3), Erdos651.IsInGeneralPosition X → B ≤ X.card →
    ∃ C : Fin k → Finset (ℝ^3), (∀ i, C i ⊆ X) ∧ (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      (∀ i, X.card ≤ (C i).card ^ 2) ∧
      ∀ a b c, a < b → b < c → ∃ (e : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3)) (ε : ℝ), 0 < ε ∧
        (∀ x ∈ C b, 0 < e x 0 ∧ e x 1 < 0 ∧ 0 < e x 2) ∧
        (∀ i, i < a ∨ b < i ∧ i ≤ c → ∀ x ∈ C i,
          e x 0 < 0 ∧ ε < e x 1 ∧ ε < e x 2) ∧
        (∀ i, a ≤ i ∧ i < b ∨ c < i → ∀ x ∈ C i,
          e x 0 < 0 ∧ e x 1 < -ε ∧ e x 2 < -ε)

/-- In the middle sign region a large subset has all its joining lines avoid
one of the two closed outer regions. -/
def H2 : Prop :=
  ∀ (S : Finset (ℝ^3)) (f₀ f₁ f₂ : (ℝ^3) →ᵃ[ℝ] ℝ) (ε : ℝ), 0 < ε →
    (∀ x ∈ S, 0 < f₀ x ∧ f₁ x < 0 ∧ 0 < f₂ x) →
    ∃ Y ⊆ S, S.card ≤ Y.card ^ 2 ∧
      ((∀ x ∈ Y, ∀ y ∈ Y, x ≠ y →
          Disjoint (line[ℝ, x, y] : Set (ℝ^3))
            {z | f₀ z ≤ 0 ∧ ε ≤ f₁ z ∧ ε ≤ f₂ z}) ∨
        (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y →
          Disjoint (line[ℝ, x, y] : Set (ℝ^3))
            {z | f₀ z ≤ 0 ∧ f₁ z ≤ -ε ∧ f₂ z ≤ -ε}))

theorem main : H1 → H2 → OMA.R_Erdos651_erdos_651_R1_H1_R1_H1_R1.H2 := by
  classical
  intro hgeometry hselection k
  obtain ⟨B, hB⟩ := hgeometry k
  refine ⟨B, fun X hX hXB => ?_⟩
  obtain ⟨C, hsub, hdisj, hsize, htriple⟩ := hB X hX hXB
  have hchoice : ∀ a b c : Fin k, a < b → b < c → ∃ (color : Bool)
      (Y : Finset (ℝ^3)) (e : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3)),
      Y ⊆ C b ∧ X.card ≤ Y.card ^ 4 ∧
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y →
        Disjoint (line[ℝ, x, y] : Set (ℝ^3)) {z | ∀ s : Fin 3, e z s ≤ 0}) ∧
      ∀ i, (if color then i < a ∨ b < i ∧ i ≤ c else a ≤ i ∧ i < b ∨ c < i) →
        ∀ x ∈ C i, ∀ s : Fin 3, e x s < 0 := by
    intro a b c hab hbc
    obtain ⟨e, ε, hε, hmid, hupper, hlower⟩ := htriple a b c hab hbc
    let coord : (ℝ^3) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).toLinearEquiv
    let p (i : Fin 3) :=
      ((LinearMap.proj i).comp coord.toLinearMap).toAffineMap.comp e.toAffineMap
    have hp (i : Fin 3) (x : ℝ^3) : p i x = e x i := rfl
    obtain ⟨Y, hY, hYsize, hsep⟩ := hselection (C b) (p 0) (p 1) (p 2) ε hε
      (by simpa only [hp] using hmid)
    have hlarge : X.card ≤ Y.card ^ 4 := by
      calc
        X.card ≤ (C b).card ^ 2 := hsize b
        _ ≤ (Y.card ^ 2) ^ 2 := Nat.pow_le_pow_left hYsize 2
        _ = Y.card ^ 4 := by rw [← pow_mul]
    obtain ⟨U, D, hU, hD⟩ := affine_coordinate_signs e ε
    rcases hsep with hsep | hsep
    · refine ⟨true, Y, U, hY, hlarge, ?_, ?_⟩
      · intro x hx y hy hxy
        apply (hsep x hx y hy hxy).mono_right
        intro z hz
        obtain ⟨h₀, h₁, h₂⟩ := hU z
        have hz₀ := hz 0
        have hz₁ := hz 1
        have hz₂ := hz 2
        rw [h₀] at hz₀
        rw [h₁] at hz₁
        rw [h₂] at hz₂
        simp only [Set.mem_ofPred_eq, hp]
        exact ⟨hz₀, by linarith, by linarith⟩
      · intro i hi x hx s
        obtain ⟨h₀, h₁, h₂⟩ := hU x
        obtain ⟨hc₀, hc₁, hc₂⟩ := hupper i hi x hx
        fin_cases s
        · change U x 0 < 0
          rwa [h₀]
        · change U x 1 < 0
          rw [h₁]
          linarith
        · change U x 2 < 0
          rw [h₂]
          linarith
    · refine ⟨false, Y, D, hY, hlarge, ?_, ?_⟩
      · intro x hx y hy hxy
        apply (hsep x hx y hy hxy).mono_right
        intro z hz
        obtain ⟨h₀, h₁, h₂⟩ := hD z
        have hz₀ := hz 0
        have hz₁ := hz 1
        have hz₂ := hz 2
        rw [h₀] at hz₀
        rw [h₁] at hz₁
        rw [h₂] at hz₂
        simp only [Set.mem_ofPred_eq, hp]
        exact ⟨hz₀, by linarith, by linarith⟩
      · intro i hi x hx s
        obtain ⟨h₀, h₁, h₂⟩ := hD x
        obtain ⟨hc₀, hc₁, hc₂⟩ := hlower i hi x hx
        fin_cases s
        · change D x 0 < 0
          rwa [h₀]
        · change D x 1 < 0
          rw [h₁]
          linarith
        · change D x 2 < 0
          rw [h₂]
          linarith
  let color (a b c : Fin k) : Bool :=
    if h : a < b ∧ b < c then Classical.choose (hchoice a b c h.1 h.2) else false
  refine ⟨C, color, hsub, hdisj, ?_⟩
  intro a b c hab hbc
  simpa only [color, dif_pos (And.intro hab hbc)] using
    Classical.choose_spec (hchoice a b c hab hbc)

end OMA.R_Erdos651_erdos_651_R1_H1_R1_H1_R1_H2_R1
