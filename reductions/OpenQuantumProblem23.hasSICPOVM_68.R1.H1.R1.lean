import OMAReductions.R_OpenQuantumProblem23_hasSICPOVM_68_R1
import Mathlib

-- Reduction OpenQuantumProblem23.hasSICPOVM_68.R1.H1.R1: the finite quantum dilogarithm step.
-- H1 is the input of Radchenko and Wheeler for d = 68: a finite quantum dilogarithm E on the
-- group G = ZMod 68 x ZMod 4420 (4420 = 68 * 65) for the Gaussian of their section 4.4 in Smith
-- coordinates, invariant under multiplication by the unit, with the origin value of their (37),
-- together with the common embedding of Stark reciprocity (Appleby, Flammia and Kopp) that puts
-- the restriction of E to the subgroup iota(ZMod 68 x ZMod 68) on the unit circle.
-- H2 is the finite harmonic analysis of Radchenko and Wheeler, (31) to (40): such an E restricts
-- to an array satisfying the reflection and twisted convolution identities of the parent step.
-- Formulation follows SICLean.L2b of Yaoling Yang, Hertaspace/sic-povm-lean at
-- e74571352233162adee70895903d82f8465fd054, Apache-2.0.
-- Parent reduction by @marcusbuffett, open-math-agents PR 3870.
-- Credit: @marcusbuffett

namespace OMA.R_OpenQuantumProblem23_hasSICPOVM_68_R1_H1_R1

-- A finite quantum dilogarithm on G whose restriction to iota(ZMod 68 x ZMod 68) is unimodular
-- after one common ring endomorphism of the complex numbers.
def H1 : Prop :=
  let ex := fun (N : ℕ) (n : ℤ) => Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (N : ℂ))
  let g := fun (x : ZMod 68 × ZMod 4420) =>
    ex 68 ((x.1.val : ℤ) ^ 2 + (x.1.val : ℤ) * (x.2.val : ℤ)) * ex 8840 (4486 * (x.2.val : ℤ) ^ 2)
  let ε := fun (x : ZMod 68 × ZMod 4420) =>
    ((((x.1.val : ℤ) + (x.2.val : ℤ) : ℤ) : ZMod 68),
      (((65 * (x.1.val : ℤ) + 66 * (x.2.val : ℤ)) : ℤ) : ZMod 4420))
  let ι := fun (i j : ZMod 68) =>
    ((((2 * (j.val : ℤ) - (i.val : ℤ)) : ℤ) : ZMod 68), (((65 * (j.val : ℤ)) : ℤ) : ZMod 4420))
  let u : ℝ := (67 + Real.sqrt 4485) / 2
  ∃ (E : ZMod 68 × ZMod 4420 → ℂ) (τ : ℂ →+* ℂ),
    (∃ C : ℂ, C ≠ 0 ∧ ∀ x y, g (x + y) / (g x * g y) * E x * E y =
      C + (∑ z, E (y - z) * E z * g z * E (x - z)) / (Real.sqrt 300560 : ℂ)) ∧
    (∀ x, E x = E (ε x)) ∧
    E 0 = (Real.sqrt u : ℂ) ^ 3 ∧
    (∀ i j, (i, j) ≠ (0, 0) → ‖τ (E (ι i j))‖ = 1)

-- Every such E restricts along iota to an array with the reflection and convolution identities.
def H2 : Prop :=
  let ex := fun (N : ℕ) (n : ℤ) => Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (N : ℂ))
  let g := fun (x : ZMod 68 × ZMod 4420) =>
    ex 68 ((x.1.val : ℤ) ^ 2 + (x.1.val : ℤ) * (x.2.val : ℤ)) * ex 8840 (4486 * (x.2.val : ℤ) ^ 2)
  let ε := fun (x : ZMod 68 × ZMod 4420) =>
    ((((x.1.val : ℤ) + (x.2.val : ℤ) : ℤ) : ZMod 68),
      (((65 * (x.1.val : ℤ) + 66 * (x.2.val : ℤ)) : ℤ) : ZMod 4420))
  let ι := fun (i j : ZMod 68) =>
    ((((2 * (j.val : ℤ) - (i.val : ℤ)) : ℤ) : ZMod 68), (((65 * (j.val : ℤ)) : ℤ) : ZMod 4420))
  let u : ℝ := (67 + Real.sqrt 4485) / 2
  let e := fun (t : ZMod 68) => ZMod.stdAddChar t
  let q := fun (i j : ZMod 68) => e (i^2 - i*j + j^2)
  ∀ E : ZMod 68 × ZMod 4420 → ℂ,
    (∃ C : ℂ, C ≠ 0 ∧ ∀ x y, g (x + y) / (g x * g y) * E x * E y =
      C + (∑ z, E (y - z) * E z * g z * E (x - z)) / (Real.sqrt 300560 : ℂ)) →
    (∀ x, E x = E (ε x)) →
    E 0 = (Real.sqrt u : ℂ) ^ 3 →
    (∀ i j, (i, j) ≠ (0, 0) → E (ι i j) * E (ι (-i) (-j)) = (q i j)⁻¹) ∧
    (∀ r s, (68 : ℂ)⁻¹ * ∑ i, ∑ j, E (ι i j) * E (ι (r-i) (s-j)) * q i j * e (-i*r+j*(r-s)) =
      (Real.sqrt 65 : ℂ) * E (ι r s) + if (r,s) = (0,0) then 68 else 0)

theorem main : H1 → H2 → OMA.R_OpenQuantumProblem23_hasSICPOVM_68_R1.H1 := by
  rintro ⟨E, τ, hpent, hinv, horigin, hcircle⟩ h2
  obtain ⟨hreflect, hconv⟩ := h2 E hpent hinv horigin
  refine ⟨fun i j => E ((((2 * (j.val : ℤ) - (i.val : ℤ)) : ℤ) : ZMod 68),
    (((65 * (j.val : ℤ)) : ℤ) : ZMod 4420)), τ, ?_, hreflect, hconv, hcircle⟩
  convert horigin using 2
  simp [Prod.mk_zero_zero]

end OMA.R_OpenQuantumProblem23_hasSICPOVM_68_R1_H1_R1
