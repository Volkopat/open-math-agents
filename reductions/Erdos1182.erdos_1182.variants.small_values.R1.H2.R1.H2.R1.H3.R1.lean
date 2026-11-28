import OMAReductions.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1

-- Credit: @Ehdunhackme
-- Split the three independent upper bounds by graph order. No bound is weakened.
-- This reduction is not itself a solved target.

namespace OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1_H3_R1

open SimpleGraph Finset

/-- The order-10 bound, with 19-vertex triangle-free obstruction hosts. -/
def H1 : Prop :=
  ∃ (r : ℕ) (masks : Fin r → ℕ),
    let C (a : Fin r) : SimpleGraph (Fin 19) :=
      { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*19+(max i j).val) = true
        symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
        loopless := ⟨by simp⟩ }
    (∀ a, (C a).CliqueFree 3) ∧
    ∀ f : Fin r → Fin 10 ↪ Fin 19,
      let D := ⨅ a, (C a)ᶜ.comap (f a)
      D.Connected → D.edgeSet.ncard ≤ 33

/-- The order-11 bound, with 21-vertex triangle-free obstruction hosts. -/
def H2 : Prop :=
  ∃ (r : ℕ) (masks : Fin r → ℕ),
    let C (a : Fin r) : SimpleGraph (Fin 21) :=
      { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*21+(max i j).val) = true
        symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
        loopless := ⟨by simp⟩ }
    (∀ a, (C a).CliqueFree 3) ∧
    ∀ f : Fin r → Fin 11 ↪ Fin 21,
      let D := ⨅ a, (C a)ᶜ.comap (f a)
      D.Connected → D.edgeSet.ncard ≤ 41

/-- The order-12 bound, with 23-vertex triangle-free obstruction hosts. -/
def H3 : Prop :=
  ∃ (r : ℕ) (masks : Fin r → ℕ),
    let C (a : Fin r) : SimpleGraph (Fin 23) :=
      { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*23+(max i j).val) = true
        symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
        loopless := ⟨by simp⟩ }
    (∀ a, (C a).CliqueFree 3) ∧
    ∀ f : Fin r → Fin 12 ↪ Fin 23,
      let D := ⨅ a, (C a)ᶜ.comap (f a)
      D.Connected → D.edgeSet.ncard ≤ 49

theorem main : H1 → H2 → H3 →
    OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1.H3 := by
  intro h10 h11 h12 t
  fin_cases t
  · exact h10
  · exact h11
  · exact h12

end OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1_H3_R1
