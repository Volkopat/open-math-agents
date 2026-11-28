import Mathlib

/-!
# Capacity region of the two-user Gaussian interference channel

Source: https://github.com/gokhanmergen/information-theory-problems/blob/main/problems/gaussian-interference-channel.md
Credit: @wispiANt

Adapted from the source's Lean module InfoTheory.Problems.GaussianInterferenceChannel
and its Core.Entropy definitions. This follows the source's 2026-11-27 correction.
-/

open scoped BigOperators Classical
open MeasureTheory

namespace OMA.S_itp_gaussian_interference_channel

noncomputable def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

noncomputable def gaussianPdf1D (v : ℝ) (x : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi * v)) * Real.exp (-(x ^ 2) / (2 * v))

/-- Gaussian Han–Kobayashi region **with a coded time-sharing variable `Q`** and power
    control (`ℛ_{HK-GS}`, Costa–Gohari–Nair–Ng 2023, Def. 2, for the two-sided channel).
    `Q` takes values in `Fin m` with `ℙ(Q = i) = w i`; in phase `i` user `j` sends
    `Xⱼ = Uⱼ + Vⱼ` with independent Gaussian common/private parts of powers `Pⱼc i`, `Pⱼp i`,
    subject to the *average* power constraints `∑ᵢ w i (Pⱼc i + Pⱼp i) ≤ Pⱼ`.  Each of the seven
    compact HK right-hand sides is averaged over `Q` **separately** (`E f = ∑ᵢ w i f i`); this is
    what distinguishes coded time-sharing from the convex hull of single-phase polytopes. -/
def InGaussianHKRegion (a b P₁ P₂ R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∃ (m : ℕ) (w P₁c P₁p P₂c P₂p : Fin m → ℝ),
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
    (∀ i, 0 ≤ P₁c i ∧ 0 ≤ P₁p i ∧ 0 ≤ P₂c i ∧ 0 ≤ P₂p i) ∧
    (∑ i, w i * (P₁c i + P₁p i) ≤ P₁) ∧ (∑ i, w i * (P₂c i + P₂p i) ≤ P₂) ∧
    let cap (s : ℝ) : ℝ := (1 / 2 : ℝ) * log2 (1 + s)
    let E (f : Fin m → ℝ) : ℝ := ∑ i, w i * f i
    let N₁ := fun i => 1 + a ^ 2 * P₂p i
    let N₂ := fun i => 1 + b ^ 2 * P₁p i
    R₁ ≤ E (fun i => cap ((P₁c i + P₁p i) / N₁ i)) ∧
    R₂ ≤ E (fun i => cap ((P₂c i + P₂p i) / N₂ i)) ∧
    R₁ + R₂ ≤ E (fun i => cap ((P₁c i + P₁p i + a ^ 2 * P₂c i) / N₁ i) +
                          cap (P₂p i / N₂ i)) ∧
    R₁ + R₂ ≤ E (fun i => cap (P₁p i / N₁ i) +
                          cap ((P₂c i + P₂p i + b ^ 2 * P₁c i) / N₂ i)) ∧
    R₁ + R₂ ≤ E (fun i => cap ((P₁p i + a ^ 2 * P₂c i) / N₁ i) +
                          cap ((P₂p i + b ^ 2 * P₁c i) / N₂ i)) ∧
    2 * R₁ + R₂ ≤ E (fun i => cap ((P₁c i + P₁p i + a ^ 2 * P₂c i) / N₁ i) +
                              cap (P₁p i / N₁ i) +
                              cap ((P₂p i + b ^ 2 * P₁c i) / N₂ i)) ∧
    R₁ + 2 * R₂ ≤ E (fun i => cap ((P₂c i + P₂p i + b ^ 2 * P₁c i) / N₂ i) +
                              cap (P₂p i / N₂ i) +
                              cap ((P₁p i + a ^ 2 * P₂c i) / N₁ i))

/-- Operational Gaussian IC achievability with measurable decoders, per-codeword power
    constraints `∑ᵢ xᵢ² ≤ n Pⱼ`, and average error over both messages evaluated via Lebesgue
    `lintegral` against the i.i.d. `N(0, 1)` noise densities (a value in `[0, 1]`, so `toReal`
    is not a junk value). -/
def InGaussianICAchievable (a b P₁ P₂ R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
    let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
    ∃ (enc₁ : Fin M₁ → Fin n → ℝ) (enc₂ : Fin M₂ → Fin n → ℝ)
      (dec₁ : (Fin n → ℝ) → Fin M₁) (dec₂ : (Fin n → ℝ) → Fin M₂),
      Measurable dec₁ ∧ Measurable dec₂ ∧
      (∀ m₁, (∑ i : Fin n, (enc₁ m₁ i) ^ 2) ≤ (n : ℝ) * P₁) ∧
      (∀ m₂, (∑ i : Fin n, (enc₂ m₂ i) ^ 2) ≤ (n : ℝ) * P₂) ∧
      let errProb (m₁ : Fin M₁) (m₂ : Fin M₂) : ℝ :=
        (∫⁻ z₁ : Fin n → ℝ, ∫⁻ z₂ : Fin n → ℝ,
          let g₁ := ∏ i : Fin n, gaussianPdf1D 1 (z₁ i)
          let g₂ := ∏ i : Fin n, gaussianPdf1D 1 (z₂ i)
          let y₁ := fun i => enc₁ m₁ i + a * enc₂ m₂ i + z₁ i
          let y₂ := fun i => b * enc₁ m₁ i + enc₂ m₂ i + z₂ i
          if dec₁ y₁ ≠ m₁ ∨ dec₂ y₂ ≠ m₂ then ENNReal.ofReal (g₁ * g₂) else 0).toReal
      ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, errProb m₁ m₂ ≤ ε

theorem main :
  ∀ (a b P₁ P₂ : ℝ), 0 ≤ a → 0 ≤ b → 0 < P₁ → 0 < P₂ →
    closure { p : ℝ × ℝ | InGaussianICAchievable a b P₁ P₂ p.1 p.2 } =
      closure { p : ℝ × ℝ | InGaussianHKRegion a b P₁ P₂ p.1 p.2 } := by
  sorry

end OMA.S_itp_gaussian_interference_channel
