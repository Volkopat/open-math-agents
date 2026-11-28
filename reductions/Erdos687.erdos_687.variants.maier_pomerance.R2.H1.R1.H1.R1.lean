import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1
import Mathlib

-- Reduction Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1.R1 of step Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1
-- Credit: @carterleffen

/-!
# Reference-tree margin and stopped-tree comparison for Jacobsthal survivors

Splits Theorem 1.2 of *A quadratic bound for Jacobsthal's function* (OpenAI Math Release preprint,
September 2026) at scale `L = log z`, `Y = floor(z^2 / L^2)`, `w = L / (log L)^2`,
`B = L / log w` into two independent hypotheses over the decreasing-prime admission tree `T`:

* `H1` (Reference-tree margin, Prop. 6.3): eventually `1 / (50 * B^2) <= R`, where
  `R = sum_{d in T} (-1)^|d| / prod_{p in d} p`.
* `H2` (Stopped-tree comparison, Secs. 7-11): eventually for every residue assignment `a`,
  `Y * V * (R - 1 / (100 * B^2)) <= |survivors in [1, Y] avoiding a p mod p for p <= z|`.

Combining `H1` and `H2` immediately yields the target survivor count with explicit constant
`c = 1/100`.
-/

namespace OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1
open Filter Finset
open scoped Classical
def H1 : Prop := ∀ᶠ z : ℝ in atTop,
  let L := Real.log z
  let Y := ⌊z ^ 2 / L ^ 2⌋₊
  let w := L / (Real.log L) ^ 2
  let B := L / Real.log w
  let P := (Finset.Icc (⌊w⌋₊ + 1) ⌊z⌋₊).filter Nat.Prime
  let e := fun p : ℕ => Real.log (p : ℝ) / Real.log w
  let T := P.powerset.filter fun d => ∀ p ∈ d,
    let A := d.filter fun q => p ≤ q
    Even A.card → max (2 * e p) (e p + 2) ≤
      Real.log ((Y : ℝ) / (∏ q ∈ A, (q : ℝ))) / Real.log w + 2 - 1/100
  let R := ∑ d ∈ T, (-1 : ℝ) ^ d.card / (∏ p ∈ d, (p : ℝ))
  1 / (50 * B ^ 2) ≤ R

def H2 : Prop := ∀ᶠ z : ℝ in atTop,
  let L := Real.log z
  let Y := ⌊z ^ 2 / L ^ 2⌋₊
  let w := L / (Real.log L) ^ 2
  let B := L / Real.log w
  let P := (Finset.Icc (⌊w⌋₊ + 1) ⌊z⌋₊).filter Nat.Prime
  let e := fun p : ℕ => Real.log (p : ℝ) / Real.log w
  let T := P.powerset.filter fun d => ∀ p ∈ d,
    let A := d.filter fun q => p ≤ q
    Even A.card → max (2 * e p) (e p + 2) ≤
      Real.log ((Y : ℝ) / (∏ q ∈ A, (q : ℝ))) / Real.log w + 2 - 1/100
  let R := ∑ d ∈ T, (-1 : ℝ) ^ d.card / (∏ p ∈ d, (p : ℝ))
  let V := ∏ p ∈ (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)
  ∀ a : ℕ → ℕ, (Y : ℝ) * V * (R - 1 / (100 * B ^ 2)) ≤
    (((Finset.Icc 1 Y).filter fun n => ∀ p ≤ ⌊z⌋₊, p.Prime →
       ¬ (n ≡ a p [MOD p])).card : ℝ)

theorem main : H1 → H2 → OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1.H1 := by
  intro h1 h2
  obtain ⟨z₀, h⟩ := Filter.eventually_atTop.1 (Filter.Eventually.and h1 h2)
  refine ⟨1/100, by norm_num, z₀, ?_⟩
  intro z hz a
  let L := Real.log z
  let Y := ⌊z ^ 2 / L ^ 2⌋₊
  let w := L / (Real.log L) ^ 2
  let B := L / Real.log w
  let P := (Finset.Icc (⌊w⌋₊ + 1) ⌊z⌋₊).filter Nat.Prime
  let e := fun p : ℕ => Real.log (p : ℝ) / Real.log w
  let T := P.powerset.filter fun d => ∀ p ∈ d,
    let A := d.filter fun q => p ≤ q
    Even A.card → max (2 * e p) (e p + 2) ≤
      Real.log ((Y : ℝ) / (∏ q ∈ A, (q : ℝ))) / Real.log w + 2 - 1/100
  let R := ∑ d ∈ T, (-1 : ℝ) ^ d.card / (∏ p ∈ d, (p : ℝ))
  let V := ∏ p ∈ (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)
  obtain ⟨ha,hb⟩ := h z hz
  have hR : 1 / (50 * B ^ 2) ≤ R := ha
  have hV : 0 ≤ V := by
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast ((Finset.mem_filter.mp hp).2).one_le
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp1)
  refine le_trans ?_ (hb a)
  change (1/100 : ℝ) * Y * V / B^2 ≤ (Y : ℝ)*V*(R-1/(100*B^2))
  have hRV := mul_le_mul_of_nonneg_left hR (mul_nonneg (Nat.cast_nonneg Y) hV)
  simp only [div_eq_mul_inv, mul_inv_rev] at hRV ⊢
  linear_combination hRV
end OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1
