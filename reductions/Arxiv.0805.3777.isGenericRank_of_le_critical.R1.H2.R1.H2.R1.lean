import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1

/-!
# A finite verified tangent instance inside the square-family problem

H1 isolates the format 7 × 8 × 8, where an explicit integral binary
tangent matrix has full row rank modulo 2. H2 is the original square-family
statement with only that case removed.

The reduction itself proves neither hypothesis. In particular, the remaining
unbounded family is still the open generic-rank conjecture.
-/

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H2_R1

/-- A bounded full tangent witness for the 7 × 8 × 8 format. -/
def H1 : Prop :=
  let r := 7*8*8 ⌈/⌉ (7+8+8-2)
  let D := 2*(7*8*8)+1
  ∃ x : Fin r → Fin 7 → Fin D,
  ∃ y z : Fin r → Fin 8 → Fin D,
    ∀ T : Fin 7 → Fin 8 → Fin 8 → ℂ,
      ∃ u : Fin r → Fin 7 → ℂ,
      ∃ v w : Fin r → Fin 8 → ℂ,
        ∀ i j k,
          T i j k = ∑ t, (u t i * (((y t j).val : ℂ) * ((z t k).val : ℂ)) +
            ((x t i).val : ℂ) * (v t j * ((z t k).val : ℂ)) +
            ((x t i).val : ℂ) * (((y t j).val : ℂ) * w t k))

/-- All other square formats, excluding the single verified finite case. -/
def H2 : Prop :=
  ∀ a m : ℕ, 3 ≤ a → a ≤ m → m < (a-1)*(m-1) →
    (∀ p : ℕ, (a,m,m) ≠ (3,2*p+1,2*p+1)) →
    a ≠ 5 → a ≠ 6 → (a,m) ≠ (7,8) →
    let r := a*m*m ⌈/⌉ (a+m+m-2)
    let D := 2*(a*m*m)+1
    ∃ x : Fin r → Fin a → Fin D,
    ∃ y : Fin r → Fin m → Fin D,
    ∃ z : Fin r → Fin m → Fin D,
      ∀ T : Fin a → Fin m → Fin m → ℂ,
        ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin m → ℂ,
        ∃ w : Fin r → Fin m → ℂ,
          ∀ i j k,
            T i j k = ∑ t, (u t i * (((y t j).val : ℂ) * ((z t k).val : ℂ)) +
              ((x t i).val : ℂ) * (v t j * ((z t k).val : ℂ)) +
              ((x t i).val : ℂ) * (((y t j).val : ℂ) * w t k))

theorem main : H1 → H2 →
    OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1.H2 := by
  intro h1 h2 a m ha ham hm hexc h5 h6
  by_cases h : a = 7 ∧ m = 8
  · obtain ⟨rfl,rfl⟩ := h
    exact h1
  · have hneq : (a,m) ≠ (7,8) := by
      intro he
      exact h ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
    exact h2 a m ha ham hm hexc h5 h6 hneq

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H2_R1
