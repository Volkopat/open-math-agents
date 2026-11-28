import OMAReductions.R_Fuglede_FugledeConjecture_variants_dim_1_R1

/-!
This reduction uses the rational spectrum argument of Dutkay and Lai,
Some reductions of the spectral set conjecture to integers, Theorem 1.3(ii).
-/

namespace OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1_H4_R1

/-- A finite family with a common real spectrum has a common spectrum modulo a
positive integer, with no collisions when reducing any of the sets. -/
def H1 : Prop :=
  ∀ (p : ℕ), 0 < p →
    ∀ (Γ : Finset ℝ) (𝒜 : Finset (Finset ℤ)),
      Γ.card = p →
      (∀ S ∈ 𝒜, S.card = p ∧
        ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ →
          ∑ k ∈ S, Complex.exp (2 * Real.pi * Complex.I * (γ₁ - γ₂) * (k : ℝ)) = 0) →
      ∃ (N : ℕ) (_ : NeZero N) (Λ : Finset (ZMod N)), Λ.card = p ∧
        ∀ S ∈ 𝒜, Set.InjOn (fun k : ℤ => (k : ZMod N)) (↑S : Set ℤ) ∧
          ∀ ξ₁ ∈ Λ, ∀ ξ₂ ∈ Λ, ξ₁ ≠ ξ₂ →
            ∑ k ∈ S, Complex.exp (2 * Real.pi * Complex.I *
              (((ξ₁.val : ℝ) - (ξ₂.val : ℝ)) * ((k : ZMod N).val : ℝ) / (N : ℝ))) = 0

/-- Universal tiling for finite cyclic groups. -/
def H2 : Prop :=
  ∀ (N : ℕ) (_ : NeZero N) (p : ℕ), 0 < p →
    ∀ (Λ : Finset (ZMod N)) (ℬ : Finset (Finset (ZMod N))),
      Λ.card = p →
      (∀ S ∈ ℬ, S.card = p ∧
        ∀ ξ₁ ∈ Λ, ∀ ξ₂ ∈ Λ, ξ₁ ≠ ξ₂ →
          ∑ k ∈ S, Complex.exp (2 * Real.pi * Complex.I *
            (((ξ₁.val : ℝ) - (ξ₂.val : ℝ)) * (k.val : ℝ) / (N : ℝ))) = 0) →
      ∃ B : Finset (ZMod N), ∀ S ∈ ℬ, ∀ m : ZMod N,
        ∃! q : {k // k ∈ S} × {b // b ∈ B}, q.1.1 + q.2.1 = m

theorem main : H1 → H2 → OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1.H4 := by
  classical
  intro hrational hcyclic p hp Γ 𝒜 hΓ h𝒜
  obtain ⟨N, hN, Λ, hΛ, hmod⟩ := hrational p hp Γ 𝒜 hΓ h𝒜
  let residue : ℤ → ZMod N := fun k => k
  let ℬ := 𝒜.image (fun S => S.image residue)
  have hℬ : ∀ U ∈ ℬ, U.card = p ∧
      ∀ ξ₁ ∈ Λ, ∀ ξ₂ ∈ Λ, ξ₁ ≠ ξ₂ →
        ∑ k ∈ U, Complex.exp (2 * Real.pi * Complex.I *
          (((ξ₁.val : ℝ) - (ξ₂.val : ℝ)) * (k.val : ℝ) / (N : ℝ))) = 0 := by
    intro U hU
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hU
    have hinj := (hmod S hS).1
    constructor
    · rw [Finset.card_image_of_injOn hinj]
      exact (h𝒜 S hS).1
    · intro ξ₁ hξ₁ ξ₂ hξ₂ hne
      rw [Finset.sum_image hinj]
      exact (hmod S hS).2 ξ₁ hξ₁ ξ₂ hξ₂ hne
  obtain ⟨B, hB⟩ := hcyclic N hN p hp Λ ℬ hΛ hℬ
  let T : Set ℤ := {t | residue t ∈ B}
  refine ⟨T, ?_⟩
  intro S hS m
  have hmem : S.image residue ∈ ℬ := Finset.mem_image_of_mem _ hS
  obtain ⟨w, hw, huniq⟩ := hB (S.image residue) hmem (residue m)
  change w.1.1 + w.2.1 = residue m at hw
  obtain ⟨a, ha, haw⟩ := Finset.mem_image.mp w.1.2
  have ht : m - a ∈ T := by
    change ((m - a : ℤ) : ZMod N) ∈ B
    rw [Int.cast_sub]
    change residue m - residue a ∈ B
    rw [haw, ← hw, add_sub_cancel_left]
    exact w.2.2
  refine ⟨(⟨a, ha⟩, ⟨m - a, ht⟩), by change a + (m - a) = m; omega, ?_⟩
  intro z hz
  change z.1.1 + z.2.1 = m at hz
  have hsum : residue z.1.1 + residue z.2.1 = residue m := by
    change (z.1.1 : ZMod N) + (z.2.1 : ZMod N) = (m : ZMod N)
    rw [← Int.cast_add, hz]
  have hzmod := huniq
    (⟨residue z.1.1, Finset.mem_image_of_mem _ z.1.2⟩, ⟨residue z.2.1, z.2.2⟩) hsum
  have haz : z.1.1 = a :=
    (hmod S hS).1 z.1.2 ha
      ((congrArg (fun q : {k // k ∈ S.image residue} × {b // b ∈ B} => q.1.1) hzmod).trans
        haw.symm)
  apply Prod.ext
  · exact Subtype.ext haz
  · apply Subtype.ext
    change z.2.1 = m - a
    omega

end OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1_H4_R1
