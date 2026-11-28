import OMAReductions.R_Erdos52_erdos_52_R3
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Algebra.GCDMonoid.Finset

-- Reduction Erdos52.erdos_52.R3.H1.R1 of Erdos52.erdos_52.R3.H1
-- Credit: @sanchan
-- Losslessly normalizes finite positive integer sets to primitive positive natural sets
-- (preserving |A|, |A + A|, |A * A| with zero constant loss), narrows ε to (0, 1/2),
-- derives Cauchy-Schwarz additive and multiplicative energy lower bounds |A|^(5/2),
-- and splits the positive sum-product problem into the three classic 3/2-threshold regimes:
-- H1 (Few Products, Many Sums), H2 (Few Sums, Many Products), and H3 (Balanced Super-3/2 Core).

open Finset
open scoped Pointwise

namespace OMA.R_Erdos52_erdos_52_R3_H1_R1

/-- Few products, many sums (high multiplicative energy regime) for primitive positive
natural sets: when `|A * A| ≤ |A|^(3/2)` (hence `E_×(A, A) ≥ |A|^(5/2)`), the sumset
achieves `|A + A| ≥ C * |A|^(2 - ε)`. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℕ,
    (∀ a ∈ A, 0 < a) → A.gcd id = 1 →
    ((A * A).card : ℝ) ≤ (A.card : ℝ) ^ ((3 : ℝ) / 2) →
    (A.card : ℝ) ^ ((5 : ℝ) / 2) ≤ (mulEnergy A A : ℝ) →
    C * (A.card : ℝ) ^ (2 - ε) ≤ ((A + A).card : ℝ)

/-- Few sums, many products (high additive energy regime) for primitive positive
natural sets: when `|A + A| ≤ |A|^(3/2)` (hence `E_+(A, A) ≥ |A|^(5/2)`), the product set
achieves `|A * A| ≥ C * |A|^(2 - ε)`. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℕ,
    (∀ a ∈ A, 0 < a) → A.gcd id = 1 →
    ((A + A).card : ℝ) ≤ (A.card : ℝ) ^ ((3 : ℝ) / 2) →
    (A.card : ℝ) ^ ((5 : ℝ) / 2) ≤ (addEnergy A A : ℝ) →
    C * (A.card : ℝ) ^ (2 - ε) ≤ ((A * A).card : ℝ)

/-- Balanced super-`3/2` core regime for primitive positive natural sets: when both
`|A + A| > |A|^(3/2)` and `|A * A| > |A|^(3/2)`, their maximum achieves
`max |A + A| |A * A| ≥ C * |A|^(2 - ε)`. -/
def H3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℕ,
    (∀ a ∈ A, 0 < a) → A.gcd id = 1 →
    (A.card : ℝ) ^ ((3 : ℝ) / 2) < ((A + A).card : ℝ) →
    (A.card : ℝ) ^ ((3 : ℝ) / 2) < ((A * A).card : ℝ) →
    C * (A.card : ℝ) ^ (2 - ε) ≤ (max (A + A).card (A * A).card : ℝ)

/-- Exact primitive normalization: every nonempty finite set `A ⊆ ℤ_{>0}` can be lifted
to `ℕ` and divided by its greatest common divisor to obtain a primitive positive set
`B ⊆ ℕ_{>0}` (`B.gcd id = 1`) with identical `|B|`, `|B + B|`, and `|B * B|`. -/
theorem toNat_primitive_reduction (A : Finset ℤ) (hne : A.Nonempty) (hpos : ∀ a ∈ A, 0 < a) :
    ∃ B : Finset ℕ, (∀ b ∈ B, 0 < b) ∧ B.gcd id = 1 ∧
      B.card = A.card ∧ (B + B).card = (A + A).card ∧ (B * B).card = (A * A).card := by
  let B0 : Finset ℕ := A.image Int.toNat
  have hA_eq : A = B0.image (fun n : ℕ => (n : ℤ)) := by
    ext a
    simp only [B0, mem_image]
    constructor
    · intro ha
      exact ⟨a.toNat, ⟨a, ha, rfl⟩, Int.toNat_of_nonneg (le_of_lt (hpos a ha))⟩
    · rintro ⟨n, ⟨x, hx, rfl⟩, rfl⟩
      rwa [Int.toNat_of_nonneg (le_of_lt (hpos x hx))]
  have hB0_pos : ∀ b ∈ B0, 0 < b := by
    intro b hb
    rcases mem_image.mp hb with ⟨a, ha, rfl⟩
    have := hpos a ha
    omega
  have hA_card : B0.card = A.card := by
    rw [hA_eq, card_image_of_injective _ Nat.cast_injective]
  have hA_add : (B0 + B0).card = (A + A).card := by
    have hadd : A + A = (B0 + B0).image (fun n : ℕ => (n : ℤ)) := by
      ext z
      simp only [mem_add, mem_image, hA_eq]
      constructor
      · rintro ⟨x, ⟨n, hn, rfl⟩, y, ⟨m, hm, rfl⟩, rfl⟩
        exact ⟨n + m, ⟨n, hn, m, hm, rfl⟩, by push_cast; rfl⟩
      · rintro ⟨k, ⟨n, hn, m, hm, rfl⟩, rfl⟩
        exact ⟨(n : ℤ), ⟨n, hn, rfl⟩, (m : ℤ), ⟨m, hm, rfl⟩, by push_cast; rfl⟩
    rw [hadd, card_image_of_injective _ Nat.cast_injective]
  have hA_mul : (B0 * B0).card = (A * A).card := by
    have hmul : A * A = (B0 * B0).image (fun n : ℕ => (n : ℤ)) := by
      ext z
      simp only [mem_mul, mem_image, hA_eq]
      constructor
      · rintro ⟨x, ⟨n, hn, rfl⟩, y, ⟨m, hm, rfl⟩, rfl⟩
        exact ⟨n * m, ⟨n, hn, m, hm, rfl⟩, by push_cast; rfl⟩
      · rintro ⟨k, ⟨n, hn, m, hm, rfl⟩, rfl⟩
        exact ⟨(n : ℤ), ⟨n, hn, rfl⟩, (m : ℤ), ⟨m, hm, rfl⟩, by push_cast; rfl⟩
    rw [hmul, card_image_of_injective _ Nat.cast_injective]
  let g : ℕ := B0.gcd id
  have hg_pos : 0 < g := by
    obtain ⟨a, ha⟩ := hne
    have hb0 : a.toNat ∈ B0 := mem_image.mpr ⟨a, ha, rfl⟩
    have hdvd : g ∣ a.toNat := gcd_dvd hb0
    have hbp : 0 < a.toNat := hB0_pos a.toNat hb0
    exact Nat.pos_of_ne_zero fun hg0 => by
      rw [hg0, zero_dvd_iff] at hdvd
      omega
  let B : Finset ℕ := B0.image (fun b => b / g)
  have hB0_eq : B0 = B.image (fun x => g * x) := by
    ext b
    simp only [B, mem_image]
    constructor
    · intro hb
      exact ⟨b / g, ⟨b, hb, rfl⟩, Nat.mul_div_cancel' (gcd_dvd (f := id) hb)⟩
    · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      have hdiv : g * (y / g) = y := Nat.mul_div_cancel' (gcd_dvd (f := id) hy)
      rwa [hdiv]
  have hinj_g : Function.Injective (fun x : ℕ => g * x) := mul_right_injective₀ hg_pos.ne'
  have hinj_g2 : Function.Injective (fun x : ℕ => (g * g) * x) :=
    mul_right_injective₀ (Nat.mul_ne_zero hg_pos.ne' hg_pos.ne')
  have hB_pos : ∀ b ∈ B, 0 < b := by
    intro b hb
    have hgb : g * b ∈ B0 := by
      rw [hB0_eq]
      exact mem_image.mpr ⟨b, hb, rfl⟩
    exact Nat.pos_of_mul_pos_left (hB0_pos (g * b) hgb)
  have hB_gcd : B.gcd id = 1 := by
    let d : ℕ := B.gcd id
    have hgd_dvd : g * d ∣ g := by
      refine dvd_gcd fun b hb => ?_
      have hdiv : d ∣ b / g := gcd_dvd (f := id) (mem_image.mpr ⟨b, hb, rfl⟩)
      have hmuld : g * d ∣ g * (b / g) := mul_dvd_mul_left g hdiv
      have hbg : g * (b / g) = b := Nat.mul_div_cancel' (gcd_dvd (f := id) hb)
      simpa only [id, hbg] using hmuld
    have hgd_le : g * d ≤ g := Nat.le_of_dvd hg_pos hgd_dvd
    have hd_ne : d ≠ 0 := by
      intro hd0
      rw [hd0, mul_zero, zero_dvd_iff] at hgd_dvd
      omega
    have hd_le : d ≤ 1 := by nlinarith
    omega
  have hB_card : B.card = B0.card := by
    rw [hB0_eq, card_image_of_injective _ hinj_g]
  have hB_add : (B + B).card = (B0 + B0).card := by
    have hadd : B0 + B0 = (B + B).image (fun x => g * x) := by
      ext z
      simp only [mem_add, mem_image, hB0_eq]
      constructor
      · rintro ⟨x, ⟨n, hn, rfl⟩, y, ⟨m, hm, rfl⟩, rfl⟩
        exact ⟨n + m, ⟨n, hn, m, hm, rfl⟩, by ring⟩
      · rintro ⟨k, ⟨n, hn, m, hm, rfl⟩, rfl⟩
        exact ⟨g * n, ⟨n, hn, rfl⟩, g * m, ⟨m, hm, rfl⟩, by ring⟩
    rw [hadd, card_image_of_injective _ hinj_g]
  have hB_mul : (B * B).card = (B0 * B0).card := by
    have hmul : B0 * B0 = (B * B).image (fun x => (g * g) * x) := by
      ext z
      simp only [mem_mul, mem_image, hB0_eq]
      constructor
      · rintro ⟨x, ⟨n, hn, rfl⟩, y, ⟨m, hm, rfl⟩, rfl⟩
        exact ⟨n * m, ⟨n, hn, m, hm, rfl⟩, by ring⟩
      · rintro ⟨k, ⟨n, hn, m, hm, rfl⟩, rfl⟩
        exact ⟨g * n, ⟨n, hn, rfl⟩, g * m, ⟨m, hm, rfl⟩, by ring⟩
    rw [hmul, card_image_of_injective _ hinj_g2]
  exact ⟨B, hB_pos, hB_gcd, hB_card.trans hA_card, hB_add.trans hA_add, hB_mul.trans hA_mul⟩

/-- Cauchy-Schwarz multiplicative energy lower bound when `|B * B| ≤ |B|^(3/2)`. -/
theorem mulEnergy_ge_of_card_mul_le (B : Finset ℕ) (hB : B.Nonempty)
    (hprod : ((B * B).card : ℝ) ≤ (B.card : ℝ) ^ ((3 : ℝ) / 2)) :
    (B.card : ℝ) ^ ((5 : ℝ) / 2) ≤ (mulEnergy B B : ℝ) := by
  have hpos : (0 : ℝ) < (B.card : ℝ) := Nat.cast_pos.mpr (card_pos.mpr hB)
  have hcs : ((B.card : ℝ) ^ 2) * ((B.card : ℝ) ^ 2) ≤
      ((B * B).card : ℝ) * (mulEnergy B B : ℝ) := by
    exact_mod_cast Finset.le_card_mul_mul_mulEnergy B B
  have hpow4 : (B.card : ℝ) ^ ((3 : ℝ) / 2) * (B.card : ℝ) ^ ((5 : ℝ) / 2) =
      ((B.card : ℝ) ^ 2) * ((B.card : ℝ) ^ 2) := by
    rw [← Real.rpow_add hpos]
    norm_num
    ring
  have hle : (B.card : ℝ) ^ ((3 : ℝ) / 2) * (B.card : ℝ) ^ ((5 : ℝ) / 2) ≤
      (B.card : ℝ) ^ ((3 : ℝ) / 2) * (mulEnergy B B : ℝ) := by
    calc (B.card : ℝ) ^ ((3 : ℝ) / 2) * (B.card : ℝ) ^ ((5 : ℝ) / 2)
        = ((B.card : ℝ) ^ 2) * ((B.card : ℝ) ^ 2) := hpow4
      _ ≤ ((B * B).card : ℝ) * (mulEnergy B B : ℝ) := hcs
      _ ≤ (B.card : ℝ) ^ ((3 : ℝ) / 2) * (mulEnergy B B : ℝ) :=
          mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg _)
  exact le_of_mul_le_mul_left hle (Real.rpow_pos_of_pos hpos _)

/-- Cauchy-Schwarz additive energy lower bound when `|B + B| ≤ |B|^(3/2)`. -/
theorem addEnergy_ge_of_card_add_le (B : Finset ℕ) (hB : B.Nonempty)
    (hsum : ((B + B).card : ℝ) ≤ (B.card : ℝ) ^ ((3 : ℝ) / 2)) :
    (B.card : ℝ) ^ ((5 : ℝ) / 2) ≤ (addEnergy B B : ℝ) := by
  have hpos : (0 : ℝ) < (B.card : ℝ) := Nat.cast_pos.mpr (card_pos.mpr hB)
  have hcs : ((B.card : ℝ) ^ 2) * ((B.card : ℝ) ^ 2) ≤
      ((B + B).card : ℝ) * (addEnergy B B : ℝ) := by
    exact_mod_cast Finset.le_card_add_mul_addEnergy B B
  have hpow4 : (B.card : ℝ) ^ ((3 : ℝ) / 2) * (B.card : ℝ) ^ ((5 : ℝ) / 2) =
      ((B.card : ℝ) ^ 2) * ((B.card : ℝ) ^ 2) := by
    rw [← Real.rpow_add hpos]
    norm_num
    ring
  have hle : (B.card : ℝ) ^ ((3 : ℝ) / 2) * (B.card : ℝ) ^ ((5 : ℝ) / 2) ≤
      (B.card : ℝ) ^ ((3 : ℝ) / 2) * (addEnergy B B : ℝ) := by
    calc (B.card : ℝ) ^ ((3 : ℝ) / 2) * (B.card : ℝ) ^ ((5 : ℝ) / 2)
        = ((B.card : ℝ) ^ 2) * ((B.card : ℝ) ^ 2) := hpow4
      _ ≤ ((B + B).card : ℝ) * (addEnergy B B : ℝ) := hcs
      _ ≤ (B.card : ℝ) ^ ((3 : ℝ) / 2) * (addEnergy B B : ℝ) :=
          mul_le_mul_of_nonneg_right hsum (Nat.cast_nonneg _)
  exact le_of_mul_le_mul_left hle (Real.rpow_pos_of_pos hpos _)

theorem main : H1 → H2 → H3 → OMA.R_Erdos52_erdos_52_R3.H1 := by
  intro h1 h2 h3 ε hε0 hε1
  let ε' : ℝ := min ε (1 / 4)
  have hε'0 : 0 < ε' := lt_min hε0 (by norm_num)
  have hε'half : ε' < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hε'le : ε' ≤ ε := min_le_left _ _
  obtain ⟨C1, hC1, h1'⟩ := h1 ε' hε'0 hε'half
  obtain ⟨C2, hC2, h2'⟩ := h2 ε' hε'0 hε'half
  obtain ⟨C3, hC3, h3'⟩ := h3 ε' hε'0 hε'half
  let C : ℝ := min C1 (min C2 C3)
  have hC : 0 < C := lt_min hC1 (lt_min hC2 hC3)
  refine ⟨C, hC, fun A hApos => ?_⟩
  by_cases hAne : A.Nonempty
  · obtain ⟨B, hBpos, hBgcd, hBcard, hBadd, hBmul⟩ := toNat_primitive_reduction A hAne hApos
    have hBne : B.Nonempty := card_pos.mp (by rw [hBcard]; exact card_pos.mpr hAne)
    have hcard1 : (1 : ℝ) ≤ (B.card : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (card_pos.mpr hBne)
    have hexp : (B.card : ℝ) ^ (2 - ε) ≤ (B.card : ℝ) ^ (2 - ε') :=
      Real.rpow_le_rpow_of_exponent_le hcard1 (by linarith)
    have hpow_nonneg : (0 : ℝ) ≤ (B.card : ℝ) ^ (2 - ε') := by positivity
    have hBbound : C * (B.card : ℝ) ^ (2 - ε') ≤ (max (B + B).card (B * B).card : ℝ) := by
      by_cases hmul : ((B * B).card : ℝ) ≤ (B.card : ℝ) ^ ((3 : ℝ) / 2)
      · have hEm := mulEnergy_ge_of_card_mul_le B hBne hmul
        have hstep := h1' B hBpos hBgcd hmul hEm
        have hC1le : C ≤ C1 := min_le_left _ _
        have hmax : ((B + B).card : ℝ) ≤ (max (B + B).card (B * B).card : ℝ) := by
          exact_mod_cast le_max_left (B + B).card (B * B).card
        exact (mul_le_mul_of_nonneg_right hC1le hpow_nonneg).trans (hstep.trans hmax)
      · push Not at hmul
        by_cases hadd : ((B + B).card : ℝ) ≤ (B.card : ℝ) ^ ((3 : ℝ) / 2)
        · have hEa := addEnergy_ge_of_card_add_le B hBne hadd
          have hstep := h2' B hBpos hBgcd hadd hEa
          have hC2le : C ≤ C2 := le_trans (min_le_right _ _) (min_le_left _ _)
          have hmax : ((B * B).card : ℝ) ≤ (max (B + B).card (B * B).card : ℝ) := by
            exact_mod_cast le_max_right (B + B).card (B * B).card
          exact (mul_le_mul_of_nonneg_right hC2le hpow_nonneg).trans (hstep.trans hmax)
        · push Not at hadd
          have hstep := h3' B hBpos hBgcd hadd hmul
          have hC3le : C ≤ C3 := le_trans (min_le_right _ _) (min_le_right _ _)
          exact (mul_le_mul_of_nonneg_right hC3le hpow_nonneg).trans hstep
    have hle : C * (B.card : ℝ) ^ (2 - ε) ≤ (max (B + B).card (B * B).card : ℝ) :=
      (mul_le_mul_of_nonneg_left hexp hC.le).trans hBbound
    rw [hBcard, hBadd, hBmul] at hle
    exact hle
  · rw [Finset.not_nonempty_iff_eq_empty] at hAne
    subst hAne
    have h0 : (0 : ℝ) ^ (2 - ε) = 0 := Real.zero_rpow (by linarith)
    simp [h0]

end OMA.R_Erdos52_erdos_52_R3_H1_R1
