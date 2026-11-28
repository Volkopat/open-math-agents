import OMAReductions.R_Green14_W_3_16_R2_H2_R1
import Mathlib

/-! A central interval forces a last red position on one side of the reflection. -/

namespace OMA.R_Green14_W_3_16_R2_H2_R1_H2_R1

private def Admissible (c : Nat → Bool) : Prop :=
  (∀ x < 238, c (237-x) = c x) ∧
    ∀ (b : Bool) (a d : Nat), 0 < d →
      a + ((if b then 16 else 3)-1)*d < 238 →
      ∃ t < (if b then 16 else 3), c (a+t*d) = b

private def TailBlue (c : Nat → Bool) (r : Nat) : Prop :=
  ∀ j, r < j → j ≤ 118 → c j = false

private theorem nearest (c : Nat → Bool) (good : Admissible c) :
    ∃ r, 111 ≤ r ∧ r ≤ 118 ∧ c r = true ∧ TailBlue c r := by
  classical
  obtain ⟨t, ht, colored⟩ := good.2 true 111 1 (by decide) (by decide)
  change t < 16 at ht
  let y := 111+t
  have yLow : 111 ≤ y := by dsimp [y]; omega
  have yHigh : y ≤ 126 := by dsimp [y]; omega
  have yRed : c y = true := by simpa [y] using colored
  let r := min y (237-y)
  have bounds : 111 ≤ r ∧ r ≤ 118 := by
    constructor
    · exact le_min yLow (by omega)
    · by_cases side : y ≤ 118
      · exact (min_le_left y (237-y)).trans side
      · exact (min_le_right y (237-y)).trans (by omega)
  have rRed : c r = true := by
    dsimp only [r]
    by_cases side : y ≤ 237-y
    · simpa [min_eq_left side] using yRed
    · rw [min_eq_right (by omega), good.1 y (by omega)]
      exact yRed
  let reds := (Finset.Icc 111 118).filter (fun i => c i = true)
  have members : reds.Nonempty := ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr bounds, rRed⟩⟩
  let i := reds.max' members
  have chosen : i ∈ reds := Finset.max'_mem reds members
  have data := Finset.mem_filter.mp chosen
  have iBounds := Finset.mem_Icc.mp data.1
  refine ⟨i, iBounds.1, iBounds.2, data.2, ?_⟩
  intro j above cap
  cases value : c j
  · rfl
  · have jMem : j ∈ reds :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, cap⟩, value⟩
    have top : j ≤ i := Finset.le_max' reds j jMem
    omega

def H1 : Prop := ∀ (c : Nat → Bool) (r : Nat), 111 ≤ r → r ≤ 112 →
  c r = true → TailBlue c r → ¬ Admissible c

def H2 : Prop := ∀ c : Nat → Bool, c 113 = true → TailBlue c 113 → ¬ Admissible c

def H3 : Prop := ∀ (c : Nat → Bool) (r : Nat), 114 ≤ r → r ≤ 116 →
  c r = true → TailBlue c r → ¬ Admissible c

def H4 : Prop := ∀ (c : Nat → Bool) (r : Nat), 117 ≤ r → r ≤ 118 →
  c r = true → TailBlue c r → ¬ Admissible c

theorem main : H1 → H2 → H3 → H4 → OMA.R_Green14_W_3_16_R2_H2_R1.H2 := by
  intro low one middle high c good
  obtain ⟨r, rLow, rHigh, red, tail⟩ := nearest c good
  by_cases left : r ≤ 112
  · exact low c r rLow left red tail good
  · by_cases single : r = 113
    · subst r
      exact one c red tail good
    · by_cases mid : r ≤ 116
      · exact middle c r (by omega) mid red tail good
      · exact high c r (by omega) rHigh red tail good

end OMA.R_Green14_W_3_16_R2_H2_R1_H2_R1