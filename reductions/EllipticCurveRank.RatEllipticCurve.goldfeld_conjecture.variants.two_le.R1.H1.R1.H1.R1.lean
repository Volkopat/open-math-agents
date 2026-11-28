import OMAReductions.R_EllipticCurveRank_RatEllipticCurve_goldfeld_conjecture_variants_two_le_R1_H1_R1

/-! Positive squarefree twist parameters split according to their
fundamental-discriminant shape. Multiplication by four is a bijection
for the second class, including the change in the normalizing cutoff. -/

namespace OMA.R_EllipticCurveRank_RatEllipticCurve_goldfeld_conjecture_variants_two_le_R1_H1_R1_H1_R1

open EllipticCurveRank Finset Filter
open scoped Topology Classical

private theorem card_rescale (P : ℕ → Prop) (H : ℕ) :
    ((Icc 1 H).filter P).card =
      ((Icc 1 (4 * H)).filter (fun d : ℕ ↦ d % 4 = 0 ∧ P (d / 4))).card := by
  classical
  let F := (Icc 1 H).filter P
  let D := (Icc 1 (4 * H)).filter (fun d : ℕ ↦ d % 4 = 0 ∧ P (d / 4))
  have hImage : F.image (fun a ↦ 4 * a) = D := by
    ext d
    constructor
    · intro hd
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hd
      obtain ⟨haRange, haP⟩ := mem_filter.mp ha
      obtain ⟨ha0, haH⟩ := mem_Icc.mp haRange
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, by simpa using haP⟩
    · intro hd
      obtain ⟨hdRange, hd0, hdP⟩ := mem_filter.mp hd
      obtain ⟨hdPos, hdH⟩ := mem_Icc.mp hdRange
      exact mem_image.mpr ⟨d / 4, mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hdP⟩,
        by omega⟩
  calc
    F.card = (F.image (fun a ↦ 4 * a)).card :=
      (card_image_of_injective F (fun a b he ↦ by omega)).symm
    _ = D.card := by rw [hImage]

/-- Positive fundamental discriminants that are one modulo four. -/
def H1 : Prop :=
  ∀ E : RatEllipticCurve,
    Tendsto (fun H : ℕ ↦ (((Icc 1 H).filter (fun a : ℕ ↦
      Squarefree a ∧ a % 4 = 1 ∧ 2 ≤ E.twistRank (a : ℤ))).card : ℝ) / H) atTop (𝓝 0)

/-- Positive fundamental discriminants divisible by four, using the
squarefree parameter d/4 for the rank of the associated twist. -/
def H2 : Prop :=
  ∀ E : RatEllipticCurve,
    Tendsto (fun X : ℕ ↦ (((Icc 1 X).filter (fun d : ℕ ↦
      d % 4 = 0 ∧ Squarefree (d / 4) ∧ (d / 4) % 4 ≠ 1 ∧
        2 ≤ E.twistRank ((d / 4 : ℕ) : ℤ))).card : ℝ) / X) atTop (𝓝 0)

theorem main : H1 → H2 →
    OMA.R_EllipticCurveRank_RatEllipticCurve_goldfeld_conjecture_variants_two_le_R1_H1_R1.H1 := by
  intro hodd hfour E
  let high (a : ℕ) := Squarefree a ∧ 2 ≤ E.twistRank (a : ℤ)
  let other (a : ℕ) := Squarefree a ∧ a % 4 ≠ 1 ∧ 2 ≤ E.twistRank (a : ℤ)
  let A (H : ℕ) := (Icc 1 H).filter fun a : ℕ ↦
    Squarefree a ∧ a % 4 = 1 ∧ 2 ≤ E.twistRank (a : ℤ)
  let B (H : ℕ) := (Icc 1 H).filter other
  let D (X : ℕ) := (Icc 1 X).filter (fun d : ℕ ↦ d % 4 = 0 ∧ other (d / 4))
  have hAtTop : Tendsto (fun H : ℕ ↦ 4 * H) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with H hH
    omega
  have hd : Tendsto (fun X : ℕ ↦ ((D X).card : ℝ) / X) atTop (𝓝 0) := hfour E
  have hMul : Tendsto (fun H : ℕ ↦ (4 : ℝ) * (((D (4 * H)).card : ℝ) / ((4 * H : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    have h4 : Tendsto (fun _ : ℕ ↦ (4 : ℝ)) atTop (𝓝 4) := tendsto_const_nhds
    simpa [Function.comp_def] using h4.mul (hd.comp hAtTop)
  have hB : Tendsto (fun H : ℕ ↦ ((B H).card : ℝ) / H) atTop (𝓝 0) := by
    apply hMul.congr
    intro H
    have hc : (B H).card = (D (4 * H)).card := by
      convert card_rescale other H using 1 <;>
        apply congrArg Finset.card <;> ext d <;> simp only [B, D, mem_filter]
    rw [hc]
    by_cases hz : H = 0
    · simp [hz]
    · have hr : (H : ℝ) ≠ 0 := by exact_mod_cast hz
      push_cast
      field_simp
  have ha : Tendsto (fun H : ℕ ↦ ((A H).card : ℝ) / H) atTop (𝓝 0) := hodd E
  have hab := ha.add hB
  rw [zero_add] at hab
  apply hab.congr
  intro H
  have hsplit : (A H).card + (B H).card = ((Icc 1 H).filter high).card := by
    simpa [A, B, high, other, filter_filter, and_assoc, and_left_comm, and_comm] using
      (card_filter_add_card_filter_not (s := (Icc 1 H).filter high) (fun a ↦ a % 4 = 1))
  rw [← add_div, ← Nat.cast_add, hsplit]

end OMA.R_EllipticCurveRank_RatEllipticCurve_goldfeld_conjecture_variants_two_le_R1_H1_R1_H1_R1
