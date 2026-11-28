import OMAReductions.R_ERH_extended_riemann_hypothesis_R2

/-
Copyright 2026 Anthropic, PBC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Reduction credit: @deepqntm.
Adapted from lsernau/grh-lean, grh-compact, commit 72fead102f663d5c7a407964a13dc0cf9d977207.
Based on Levent Alpöge's proof with Claude, shortened by Luke Sernau and colleagues.
This reduction expresses the prime error, quadratic twists and Landau criterion in the pinned
Mathlib vocabulary and proves the change of level and primitive reflection in this file.
-/

/-!
# Primitive strip zeros from a one-sided prime estimate and quadratic twists

At level `18480 * q`, choose a prime whose twists are zero-free through the height of the
putative zero. Apply Landau's criterion with the prime estimate, then use the Euler factors
for change of level and the primitive functional equation.
-/

namespace OMA.R_ERH_extended_riemann_hypothesis_R2_H2_R1

open ArithmeticFunction.vonMangoldt DirichletCharacter Filter
open scoped Classical

/-- One-sided estimate for the smoothed, centered von Mangoldt sum over the class 1 modulo M.
The Legendre symbol weights the non-split primes. The logarithmic derivatives fix the constant C. -/
def H1 : Prop :=
  ∀ (M d : ℕ) [NeZero M] [Fact d.Prime], 18480 ∣ M → d ≡ M / 2 - 1 [MOD M] →
    let κ : DirichletCharacter ℂ d := (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)
    let twist (ξ : DirichletCharacter ℂ M) :=
      ξ.changeLevel (dvd_mul_right M d) * κ.changeLevel (dvd_mul_left d M)
    let L₀ {N : ℕ} [NeZero N] (ξ : DirichletCharacter ℂ N) :=
      if ξ = 1 then LFunctionTrivChar₁ N else ξ.LFunction
    let diff (ξ : DirichletCharacter ℂ M) := logDeriv (L₀ (twist ξ)) 1 - logDeriv (L₀ ξ) 1
    let C := (((∑ ξ, diff ξ) - 1) / (M.totient : ℂ)).re
    let weight (n : ℕ) := residueClass (1 : ZMod M) n * (1 - (legendreSym d n : ℝ))
    ∀ β : ℝ, 1 / 2 < β → β < 1 → ∀ᶠ x : ℝ in atTop,
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, weight n * ((n : ℝ)⁻¹ - x⁻¹)) - Real.log x / M.totient - C ≤
        x ^ (β - 1)

/-- A prime in the prescribed progression makes every quadratic twist simultaneously zero-free
to the right of β, up to height T, including the boundary. -/
def H2 : Prop :=
  ∀ (M : ℕ) [NeZero M], 18480 ∣ M → ∀ β T : ℝ, 1 / 2 < β →
    ∃ (d : ℕ) (_ : Fact d.Prime), d ≡ M / 2 - 1 [MOD M] ∧
      let κ : DirichletCharacter ℂ d := (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)
      let twist (ξ : DirichletCharacter ℂ M) :=
        ξ.changeLevel (dvd_mul_right M d) * κ.changeLevel (dvd_mul_left d M)
      ∀ (ξ : DirichletCharacter ℂ M) (z : ℂ),
        β ≤ z.re → |z.im| ≤ T → (twist ξ).LFunction z ≠ 0

/-- Landau's criterion for one fixed prime d. The one-sided bound and the zero-free twists
through height |Im s| exclude an untwisted zero at s. -/
def H3 : Prop :=
  ∀ (M d : ℕ) [NeZero M] [Fact d.Prime], d % 8 = 7 → M.Coprime d →
    let κ : DirichletCharacter ℂ d := (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)
    let twist (ξ : DirichletCharacter ℂ M) :=
      ξ.changeLevel (dvd_mul_right M d) * κ.changeLevel (dvd_mul_left d M)
    let L₀ {N : ℕ} [NeZero N] (ξ : DirichletCharacter ℂ N) :=
      if ξ = 1 then LFunctionTrivChar₁ N else ξ.LFunction
    let diff (ξ : DirichletCharacter ℂ M) := logDeriv (L₀ (twist ξ)) 1 - logDeriv (L₀ ξ) 1
    let C := (((∑ ξ, diff ξ) - 1) / (M.totient : ℂ)).re
    let weight (n : ℕ) := residueClass (1 : ZMod M) n * (1 - (legendreSym d n : ℝ))
    ∀ (β : ℝ) (s : ℂ), 1 / 2 < β → β < s.re → s.re < 1 →
      (∀ᶠ x : ℝ in atTop,
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, weight n * ((n : ℝ)⁻¹ - x⁻¹)) - Real.log x / M.totient - C ≤
          x ^ (β - 1)) →
      (∀ (ξ : DirichletCharacter ℂ M) (z : ℂ),
        β ≤ z.re → |z.im| ≤ |s.im| → (twist ξ).LFunction z ≠ 0) →
      ∀ χ : DirichletCharacter ℂ M, χ.LFunction s ≠ 0

/-- The progression used in the prime estimate meets the arithmetic conditions of Landau's criterion. -/
theorem prime_class_conditions {M d : ℕ} [NeZero M] (hM : 18480 ∣ M)
    (hc : d ≡ M / 2 - 1 [MOD M]) : d % 8 = 7 ∧ M.Coprime d := by
  have hpos := NeZero.pos M
  obtain ⟨q, rfl⟩ := hM
  let a := 18480 * q / 2 - 1
  have h8 : 8 ∣ 18480 * q := (show 8 ∣ 18480 by decide).trans (dvd_mul_right _ _)
  have ha8 : a % 8 = 7 := by dsimp [a]; omega
  have hda : d % 8 = a % 8 := hc.of_dvd h8
  have ha : a.Coprime (18480 * q) := by
    have hfactor : 18480 * q = 2 * (a + 1) := by dsimp [a]; omega
    rw [hfactor, Nat.coprime_mul_iff_right, Nat.coprime_two_right, Nat.coprime_self_add_right]
    exact ⟨Nat.odd_iff.mpr (by omega), Nat.coprime_one_right _⟩
  have hcop : d.Coprime (18480 * q) := hc.gcd_eq.trans ha
  exact ⟨hda.trans ha8, hcop.symm⟩

theorem right_strip_nonzero (hbound : H1) (hprime : H2) (hlandau : H3)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hhalf : 1 / 2 < s.re) (hlt : s.re < 1) : χ.LFunction s ≠ 0 := by
  let M := 18480 * q
  have : NeZero M := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne q)⟩
  have hM : 18480 ∣ M := dvd_mul_right 18480 q
  have hq : q ∣ M := dvd_mul_left q 18480
  obtain ⟨β, hβ, hsβ⟩ := exists_between hhalf
  obtain ⟨d, hd, hclass, htwist⟩ := hprime M hM β |s.im| hβ
  obtain ⟨hd8, hcop⟩ := prime_class_conditions hM hclass
  have herror := hbound M d hM hclass β hβ (hsβ.trans hlt)
  have hnz := hlandau M d hd8 hcop β s hβ hsβ hlt herror htwist (χ.changeLevel hq)
  intro hz
  have hs : s ≠ 1 := fun e ↦ by simp [e] at hlt
  apply hnz
  rw [LFunction_changeLevel hq χ (.inr hs), hz, zero_mul]

theorem reflected_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {s : ℂ} (hpos : 0 < s.re) (hlt : s.re < 1)
    (hz : χ.LFunction s = 0) : (χ⁻¹).LFunction (1 - s) = 0 := by
  have hs : s ≠ 0 := fun e ↦ by simp [e] at hpos
  have ht : 1 - s ≠ 0 := sub_ne_zero.mpr (fun e ↦ by simp [← e] at hlt)
  have hgamma : χ.gammaFactor s ≠ 0 := by
    rcases χ.even_or_odd with he | ho
    · rw [he.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos hpos
    · rw [ho.gammaFactor_def]
      apply Complex.Gammaℝ_ne_zero_of_re_pos
      simp only [Complex.add_re, Complex.one_re]
      linarith
  rw [LFunction_eq_completed_div_gammaFactor χ s (.inl hs)] at hz
  have hcompleted := (div_eq_zero_iff.mp hz).resolve_right hgamma
  have hi : (χ⁻¹).IsPrimitive := χ.conductor_inv.trans hχ
  rw [LFunction_eq_completed_div_gammaFactor _ _ (.inl ht), hi.completedLFunction_one_sub,
    inv_inv, hcompleted, mul_zero, zero_div]

theorem main : H1 → H2 → H3 → OMA.R_ERH_extended_riemann_hypothesis_R2.H2 := by
  intro hbound hprime hlandau q _ χ hχ s hpos hlt hz
  rcases lt_trichotomy s.re (1 / 2) with hleft | heq | hright
  · have hhalf : 1 / 2 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
    have hlt' : (1 - s).re < 1 := by simp only [Complex.sub_re, Complex.one_re]; linarith
    exact (right_strip_nonzero hbound hprime hlandau χ⁻¹ hhalf hlt'
      (reflected_zero hχ hpos hlt hz)).elim
  · exact heq
  · exact (right_strip_nonzero hbound hprime hlandau χ hright hlt hz).elim

end OMA.R_ERH_extended_riemann_hypothesis_R2_H2_R1
