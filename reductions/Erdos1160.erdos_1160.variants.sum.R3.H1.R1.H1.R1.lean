import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1
import Mathlib.GroupTheory.Frattini
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
-- Formalization for @michelzerasafadaum-gif.

open Filter Erdos1160
namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H1_R1


/-- Count of groups within the central interval of generator ranks. -/
def H1 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let d := Nat.log 2 (frattini c.property.choose).index
                        1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d}
  C.ncard^27 ≤ 2^(2*m^3 + 216*(m+1)^2)

/-- Count of groups outside the central interval of generator ranks. -/
def H2 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let d := Nat.log 2 (frattini c.property.choose).index
                        1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d}
  (Cᶜ).ncard^27 ≤ 2^(2*m^3 + 216*(m+1)^2)

/-- The explicit class-two family gives a lower estimate at every order 2^m, m ≥ 3. -/
def H3 : Prop := ∀ m : ℕ, 3 ≤ m → 2^(2*m^3) ≤ g (2^m)^27 * 2^(12*m^2)

private theorem parts {X : Type*} (C : Set X) {E : ℕ}
    (hc : C.ncard^27 ≤ 2^E) (hx : Cᶜ.ncard^27 ≤ 2^E) : (Nat.card X)^27 ≤ 2^(E+27) := by
  classical
  have total : Nat.card X ≤ C.ncard + Cᶜ.ncard := by
    simpa only [Set.union_compl_self, Set.ncard_univ] using Set.ncard_union_le C Cᶜ
  let v := max C.ncard Cᶜ.ncard
  have hv : v^27 ≤ 2^E := by
    rcases le_total C.ncard Cᶜ.ncard with h|h
    · simpa only [v,max_eq_right h] using hx
    · simpa only [v,max_eq_left h] using hc
  have tot : Nat.card X ≤ 2*v := by
    have hl : C.ncard ≤ v := le_max_left _ _
    have hr : Cᶜ.ncard ≤ v := le_max_right _ _
    omega
  calc
    _ ≤ (2*v)^27 := Nat.pow_le_pow_left tot _
    _ = 2^27*v^27 := mul_pow ..
    _ ≤ 2^27*2^E := Nat.mul_le_mul_left _ hv
    _ = _ := by rw [← pow_add, Nat.add_comm]

theorem main : H1 → H2 → H3 → OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1.H1 := by
  classical
  intro center exterior lower
  have ev : ∀ᶠ m : ℕ in atTop, g (2^m)^27 ≤ 2^(2*m^3+243*(m+1)^2) := by
    filter_upwards [center,exterior] with m hc hx
    let A : Set (Quotient (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0})) :=
      Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
    let C : Set A := {c | let d := Nat.log 2 (frattini c.property.choose).index
                          1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d}
    have hsum : Nat.card A ^ 27 ≤ 2^((2*m^3 + 216*(m+1)^2)+27) := parts C hc hx
    change Nat.card A ^ 27 ≤ _
    exact hsum.trans (Nat.pow_le_pow_right (by decide) (by nlinarith [Nat.zero_le m]))
  obtain ⟨N,hN⟩ := eventually_atTop.mp ev
  let K := ∑ j ∈ Finset.range N, g (2^j)^27
  let B := 243 + K
  have upper (a : ℕ) : g (2^a)^27 ≤ 2^(2*a^3+B*(a+1)^2) := by
    by_cases ha : N ≤ a
    · exact (hN a ha).trans (Nat.pow_le_pow_right (by decide) (by dsimp [B]; nlinarith))
    · have hsmall : g (2^a)^27 ≤ K := Finset.single_le_sum (f:=fun j => g (2^j)^27)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
      have hpositive : 1 ≤ (a+1)^2 := Nat.succ_le_of_lt (by positivity)
      have cost : K ≤ B*(a+1)^2 := (by dsimp [B]; omega : K ≤ B).trans
        (by simpa using Nat.mul_le_mul_left B hpositive)
      have hg : g (2^a)^27 ≤ 2^(g (2^a)^27) := Nat.le_of_lt Nat.lt_two_pow_self
      exact hg.trans (Nat.pow_le_pow_right (by decide) (hsmall.trans (cost.trans (Nat.le_add_left ..))))
  exact ⟨B+12,OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1.dyadic_comparison g lower upper⟩

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H1_R1
