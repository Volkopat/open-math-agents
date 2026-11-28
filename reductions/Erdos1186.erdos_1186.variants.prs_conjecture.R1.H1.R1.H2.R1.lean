import OMAReductions.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1_H1_R1
import Mathlib.Tactic.Linarith

/-!
The first near-cut slab separates into a finite box inequality and a transfer
from the discrete signed cut to that box. Carlos Toledo gives the certificate
in https://carlostoledo.co/reports/delta3.html. The exact G24 grid and coefficient
data below are from Chandler Snively's formalization, release v1.0.0,
https://github.com/dreadpiratechan/erdos-1186, Copyright 2026 Chandler Snively,
Apache License 2.0. The three integers store the first halves of the endpoint,
linear, and quadratic tables, with fields of width 10, 9, and 9 respectively.
-/

open Finset
open scoped BigOperators

namespace OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1_H1_R1_H2_R1

/-- The exact mass and objective of the G24 grid, evaluated on a cell density. -/
theorem g24_model : ∃ model : ((ℕ → ℝ) → ℝ) × ((ℕ → ℝ) → ℝ), model =
    (let digit := fun (word width i : ℕ) => (word >>> (width * i)) &&& ((1 <<< width) - 1)
     let endpointWord := 0x8922087210821f87c1e0761c8701b06a198641805e16858150521445013c4e1344c12046108400f03a0d8340ce328c6308c02f8b82a0a024088210801f0781d0701805813048110400f0380d0300a01804000
     let alphaWord := 0x3090789c3642128f8373812140606616908361e0480c03000000606120a8d8362a088480a010080000008060c1c0f0d0240601800000303090280c0100000020000004081005070
     let betaWord := 0x120928890482412030600c30060c01812091202448090120904824120948090480c18060c01800c180c0600c061b600c0c03009048241209048c03036030180c03030180c1810060c0
     let endpoint := fun i =>
       if i ≤ 65 then digit endpointWord 10 i else 1096 - digit endpointWord 10 (130-i)
     let len := fun i => endpoint (i+1) - endpoint i
     let α := fun i => (digit alphaWord 9 (min i (129-i)) : ℝ) / 300304
     let β := fun i => (digit betaWord 9 (min i (129-i)) : ℝ) / 1801824
     let shade := fun i =>
       let b := endpoint i / 2
       b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
         (274 ≤ b && b < 390) || (449 ≤ b && b < 486) || (514 ≤ b && b < 520)
     let quarter := fun m : ℤ =>
       if 1 ≤ m ∧ m ≤ 1094 then (4 : ℕ)
       else if m = 0 ∨ m = 1095 then 3 else if m = -1 ∨ m = 1096 then 1 else 0
     let area := fun i j =>
       ((List.range' (endpoint i+1) (len i)).map fun x : ℕ =>
         ((List.range' (endpoint j+1) (len j)).map fun z : ℕ =>
           quarter (2 * (z : ℤ) - x - 1)).sum).sum
     let pair := fun i j (u v : ℝ) =>
       let whole := (len i : ℝ) * (len j : ℝ) / 1096^2
       let inside := (area i j : ℝ) / (4 * 1096^2)
       let selected := whole * (u*v)
       if shade i = shade j then max 0 (selected-(whole-inside))
       else max (-inside) (-selected)
     (fun y => ∑ i ∈ range 130, (len i : ℝ) / 1096 * y i,
      fun y => (∑ i ∈ range 130, (α i * y i + β i * (y i)^2)) +
        ∑ i ∈ range 130, ∑ j ∈ range 130, pair i j (y i) (y j))) :=
  ⟨_, rfl⟩

/-- The compact continuous box certificate on the middle slab. -/
def H1 : Prop :=
  let model := Classical.choose g24_model
  ∀ y : ℕ → ℝ, (∀ i < 130, 0 ≤ y i ∧ y i ≤ 1) →
    (1/5 : ℝ) ≤ model.1 y → model.1 y ≤ 3/10 → 0 ≤ model.2 y

/-- Transfer the cut to the G24 objective with exact mass and linear error. -/
def H2 : Prop :=
  let model := Classical.choose g24_model
  ∀ (w : ℕ), 1 ≤ w → ∀ d : ℕ → Bool,
    let n := 1096*w
    let ref := fun x : ℕ =>
      let b := (x - 1) / (2*w)
      b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
      (274 ≤ b && b < 390) || (449 ≤ b && b < 486) || (514 ≤ b && b < 520)
    let R := ((Icc 1 n ×ˢ Icc 1 n).filter fun p : ℕ × ℕ =>
      p.1 + 1 ≤ 2*p.2 ∧ 2*p.2 ≤ p.1 + n)
    let t := ((Icc 1 n).filter (fun x => d x = true)).card
    let gain : ℤ := ∑ p ∈ R, (if d p.1 = d p.2 then 0 else
      if ref p.1 = ref p.2 then 1 else -1 : ℤ)
    ∃ y : ℕ → ℝ, (∀ i < 130, 0 ≤ y i ∧ y i ≤ 1) ∧
      model.1 y = (t : ℝ) / n ∧ (gain : ℝ) + 2 * (n : ℝ)^2 * model.2 y ≤ 110680 * n

theorem main : H1 → H2 → OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1_H1_R1.H2 := by
  intro hCert hTransfer
  refine ⟨110680, by norm_num, ?_⟩
  intro w hw d
  dsimp only
  intro hlo hhi
  obtain ⟨y, hBox, hMass, hCut⟩ := hTransfer w hw d
  let n := 1096*w
  let t := ((Icc 1 n).filter (fun x => d x = true)).card
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.mul_pos (by decide : 0 < 1096) (Nat.zero_lt_of_lt hw)
  have hl : (n : ℝ) ≤ 5 * (t : ℝ) := by exact_mod_cast hlo
  have hu : 10 * (t : ℝ) ≤ 3 * (n : ℝ) := by exact_mod_cast hhi
  have hlMass : (1/5 : ℝ) ≤ (Classical.choose g24_model).1 y := by
    rw [hMass]
    apply (le_div_iff₀ hn).2
    linarith only [hl]
  have huMass : (Classical.choose g24_model).1 y ≤ (3/10 : ℝ) := by
    rw [hMass]
    apply (div_le_iff₀ hn).2
    linarith only [hu]
  have hObj := hCert y hBox hlMass huMass
  have hNonneg : 0 ≤ 2 * (n : ℝ)^2 * (Classical.choose g24_model).2 y :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hObj
  exact (le_add_of_nonneg_right hNonneg).trans hCut

end OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1_H1_R1_H2_R1
