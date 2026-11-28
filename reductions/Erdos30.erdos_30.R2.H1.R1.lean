import OMAReductions.R_Erdos30_erdos_30_R2
import Mathlib

-- Reduction Erdos30.erdos_30.R2.H1.R1 of step Erdos30.erdos_30.R2.H1
-- Credit: @arindale

/-!
# Gluing rulers at comparable square lengths

`H1` of the parent reduction is the gluing direction: two optimal rulers at comparable square
lengths fit into a single ruler at the combined square length, up to `a^δ`.  We reduce it to the
two one-sided estimates at square lengths: the upper estimate `h(m^2) ≤ m + m^δ` and the lower
estimate `m ≤ h(m^2) + m^δ`, both eventually and for every `δ > 0`.  These are the two halves of
the Erdős–Turán asymptotic restricted to squares.

The main implication is arithmetic: with exponent `δ/2` the two estimates give
`h(a^2) + h(b^2) ≤ a + b + (1 + 2^(δ/2)) a^(δ/2)` and `h((a+b)^2) ≥ a + b - 3^(δ/2) a^(δ/2)`,
and `(1 + 2^(δ/2) + 3^(δ/2)) a^(δ/2) ≤ a^δ` for all large `a`.
-/

namespace OMA.R_Erdos30_erdos_30_R2_H1_R1

open Filter

/-- Upper half at square lengths: eventually `h(m^2) ≤ m + m^δ`. -/
def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ m : ℕ, K ≤ m →
    (Erdos30.h (m ^ 2) : ℝ) ≤ (m : ℝ) + (m : ℝ) ^ δ

/-- Lower half at square lengths: eventually `m ≤ h(m^2) + m^δ`. -/
def H2 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ m : ℕ, K ≤ m →
    (m : ℝ) ≤ (Erdos30.h (m ^ 2) : ℝ) + (m : ℝ) ^ δ

theorem main : H1 → H2 → OMA.R_Erdos30_erdos_30_R2.H1 := by
  intro ha hb δ hδ
  have hη : 0 < δ / 2 := by positivity
  obtain ⟨K1, hK1⟩ := ha (δ / 2) hη
  obtain ⟨K2, hK2⟩ := hb (δ / 2) hη
  have hlim : Tendsto (fun x : ℝ => x ^ (δ / 2)) atTop atTop := tendsto_rpow_atTop hη
  have hev : ∀ᶠ x in atTop,
      (1 + (2 : ℝ) ^ (δ / 2) + (3 : ℝ) ^ (δ / 2)) ≤ x ^ (δ / 2) :=
    hlim.eventually (eventually_ge_atTop _)
  rw [eventually_atTop] at hev
  obtain ⟨x0, hx0⟩ := hev
  obtain ⟨K3, hK3⟩ := exists_nat_ge x0
  refine ⟨max (max K1 K2) (max K3 1), ?_⟩
  intro a b haK hab hb2a
  have hX : max K1 K2 ≤ a := (le_max_left (max K1 K2) (max K3 1)).trans haK
  have hY : max K3 1 ≤ a := (le_max_right (max K1 K2) (max K3 1)).trans haK
  have hK1a : K1 ≤ a := (le_max_left K1 K2).trans hX
  have hK2a : K2 ≤ a := (le_max_right K1 K2).trans hX
  have hK3a : K3 ≤ a := (le_max_left K3 1).trans hY
  have hbK1 : K1 ≤ b := le_trans hK1a hab
  have hha : (Erdos30.h (a ^ 2) : ℝ) ≤ (a : ℝ) + (a : ℝ) ^ (δ / 2) := hK1 a hK1a
  have hhb : (Erdos30.h (b ^ 2) : ℝ) ≤ (b : ℝ) + (b : ℝ) ^ (δ / 2) := hK1 b hbK1
  have habK2 : K2 ≤ a + b := by omega
  have hH : ((a + b : ℕ) : ℝ) ≤
      (Erdos30.h ((a + b) ^ 2) : ℝ) + ((a + b : ℕ) : ℝ) ^ (δ / 2) := hK2 (a + b) habK2
  have hb2 : (b : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast hb2a
  have hab3 : ((a + b : ℕ) : ℝ) ≤ 3 * (a : ℝ) := by
    have h : a + b ≤ 3 * a := by omega
    exact_mod_cast h
  have hconst : 1 + (2 : ℝ) ^ (δ / 2) + (3 : ℝ) ^ (δ / 2) ≤ (a : ℝ) ^ (δ / 2) := by
    have hx0a : x0 ≤ (a : ℝ) := le_trans hK3 (by exact_mod_cast hK3a)
    exact hx0 (a : ℝ) hx0a
  have hbpow : (b : ℝ) ^ (δ / 2) ≤ (2 : ℝ) ^ (δ / 2) * (a : ℝ) ^ (δ / 2) := by
    calc (b : ℝ) ^ (δ / 2) ≤ (2 * (a : ℝ)) ^ (δ / 2) :=
          Real.rpow_le_rpow (Nat.cast_nonneg b) hb2 (le_of_lt hη)
      _ = (2 : ℝ) ^ (δ / 2) * (a : ℝ) ^ (δ / 2) :=
          Real.mul_rpow (by norm_num) (Nat.cast_nonneg a)
  have habpow : ((a + b : ℕ) : ℝ) ^ (δ / 2) ≤
      (3 : ℝ) ^ (δ / 2) * (a : ℝ) ^ (δ / 2) := by
    calc ((a + b : ℕ) : ℝ) ^ (δ / 2) ≤ (3 * (a : ℝ)) ^ (δ / 2) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hab3 (le_of_lt hη)
      _ = (3 : ℝ) ^ (δ / 2) * (a : ℝ) ^ (δ / 2) :=
          Real.mul_rpow (by norm_num) (Nat.cast_nonneg a)
  have hstep : (1 + (2 : ℝ) ^ (δ / 2) + (3 : ℝ) ^ (δ / 2)) * (a : ℝ) ^ (δ / 2)
      ≤ (a : ℝ) ^ δ := by
    have h2 : (a : ℝ) ^ (δ / 2) * (a : ℝ) ^ (δ / 2) = (a : ℝ) ^ δ := by
      have hd : δ / 2 + δ / 2 = δ := by ring
      rw [← Real.rpow_add' (Nat.cast_nonneg a) (by rw [hd]; exact ne_of_gt hδ), hd]
    calc (1 + (2 : ℝ) ^ (δ / 2) + (3 : ℝ) ^ (δ / 2)) * (a : ℝ) ^ (δ / 2)
        ≤ (a : ℝ) ^ (δ / 2) * (a : ℝ) ^ (δ / 2) :=
          mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (Nat.cast_nonneg a) _)
      _ = (a : ℝ) ^ δ := h2
  have hbnd : (a : ℝ) ^ (δ / 2) + (b : ℝ) ^ (δ / 2) + ((a + b : ℕ) : ℝ) ^ (δ / 2)
      ≤ (1 + (2 : ℝ) ^ (δ / 2) + (3 : ℝ) ^ (δ / 2)) * (a : ℝ) ^ (δ / 2) := by
    nlinarith [hbpow, habpow]
  have key : ((a : ℝ) + (a : ℝ) ^ (δ / 2)) + ((b : ℝ) + (b : ℝ) ^ (δ / 2))
      ≤ (Erdos30.h ((a + b) ^ 2) : ℝ) + (a : ℝ) ^ δ := by
    have hcast : ((a + b : ℕ) : ℝ) = (a : ℝ) + (b : ℝ) := by push_cast; ring
    calc ((a : ℝ) + (a : ℝ) ^ (δ / 2)) + ((b : ℝ) + (b : ℝ) ^ (δ / 2))
        = ((a + b : ℕ) : ℝ) + ((a : ℝ) ^ (δ / 2) + (b : ℝ) ^ (δ / 2)) := by
          rw [hcast]; ring
      _ ≤ (Erdos30.h ((a + b) ^ 2) : ℝ) + ((a + b : ℕ) : ℝ) ^ (δ / 2)
            + ((a : ℝ) ^ (δ / 2) + (b : ℝ) ^ (δ / 2)) := by linarith [hH]
      _ = (Erdos30.h ((a + b) ^ 2) : ℝ)
            + ((a : ℝ) ^ (δ / 2) + (b : ℝ) ^ (δ / 2) + ((a + b : ℕ) : ℝ) ^ (δ / 2)) := by
          ring
      _ ≤ (Erdos30.h ((a + b) ^ 2) : ℝ)
            + (1 + (2 : ℝ) ^ (δ / 2) + (3 : ℝ) ^ (δ / 2)) * (a : ℝ) ^ (δ / 2) := by
          linarith [hbnd]
      _ ≤ (Erdos30.h ((a + b) ^ 2) : ℝ) + (a : ℝ) ^ δ := by linarith [hstep]
  calc (Erdos30.h (a ^ 2) : ℝ) + (Erdos30.h (b ^ 2) : ℝ)
      ≤ ((a : ℝ) + (a : ℝ) ^ (δ / 2)) + ((b : ℝ) + (b : ℝ) ^ (δ / 2)) :=
        add_le_add hha hhb
    _ ≤ (Erdos30.h ((a + b) ^ 2) : ℝ) + (a : ℝ) ^ δ := key

end OMA.R_Erdos30_erdos_30_R2_H1_R1
