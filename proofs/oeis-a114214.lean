import OMAStatements.S_oeis_a114214
import Mathlib

namespace OMA.ShallowDiagonal114214

open OMA.S_oeis_a114214
open Finset

private theorem splitSum (g : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ range n, g i =
      (∑ j ∈ range ((n+1)/2), g (2*j)) + ∑ j ∈ range (n/2), g (2*j+1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih _ =>
    have h : (n+2+1)/2 = (n+1)/2+1 := by omega
    have h' : (n+2)/2 = n/2+1 := by omega
    rw [h,h',sum_range_succ, sum_range_succ, ih, sum_range_succ, sum_range_succ]
    rcases Nat.mod_two_eq_zero_or_one n with e|e
    · have u : 2*((n+1)/2) = n := by omega
      have v : 2*(n/2)+1 = n+1 := by omega
      rw [u,v]
      omega
    · have u : 2*((n+1)/2) = n+1 := by omega
      have v : 2*(n/2)+1 = n := by omega
      rw [u,v]
      omega

private theorem lucas (n k : ℕ) :
    n.choose k % 2 =
      ((n%2).choose (k%2) * (n/2).choose (k/2)) % 2 :=
  Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2)

private theorem evenChoose (n k : ℕ) :
    n.choose (2*k) ≡ (n/2).choose k [MOD 2] := by
  change _ % 2 = _
  rw [lucas]
  simp [Nat.mul_comm]

private theorem entry (a b : ℕ) :
    parityEntry a b = (a/2 + b/2).choose (b/2) % 2 := by
  unfold parityEntry
  rw [splitSum]
  simp only [Nat.mul_mod_right, ↓reduceIte]
  have z (k : ℕ) : (2*k+1)%2 ≠ 0 := by omega
  simp only [z, if_false, sum_const_zero, add_zero]
  have len : (b+1+1)/2 = b/2+1 := by omega
  rw [len, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Nat.ModEq.sum
  intro i hi
  have hi' : i ≤ b/2 := mem_range_succ_iff.mp hi
  rw [Nat.choose_symm hi']
  exact (evenChoose a i).mul (evenChoose b i)

/-- The sum of odd entries on a shallow diagonal of the ordinary Pascal triangle. -/
private def stern (m : ℕ) : ℕ :=
  ∑ j ∈ range m, (m-1-j).choose j % 2

private theorem stern_short (m : ℕ) :
    stern m = ∑ j ∈ range ((m+1)/2), (m-1-j).choose j % 2 := by
  unfold stern
  symm
  apply sum_subset (by apply range_mono; omega)
  intro k hk h
  simp only [mem_range, not_lt] at hk h
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  rfl

private theorem stern_even (m : ℕ) : stern (2*m) = stern m := by
  unfold stern
  rw [splitSum]
  have he : (2*m+1)/2 = m := by omega
  have ho : (2*m)/2 = m := by omega
  rw [he,ho]
  have oddZero : ∀ j ∈ range m, (2*m-1-(2*j+1)).choose (2*j+1) % 2 = 0 := by
    intro j hj
    have := mem_range.mp hj
    rw [lucas]
    have h : (2*m-1-(2*j+1))%2 = 0 := by omega
    have h' : (2*j+1)%2 = 1 := by omega
    simp [h,h']
  rw [sum_eq_zero oddZero,add_zero]
  apply sum_congr rfl
  intro j hj
  have := mem_range.mp hj
  have h : (2*m-1-2*j)/2 = m-1-j := by omega
  exact h ▸ evenChoose (2*m-1-2*j) j

private theorem stern_odd (m : ℕ) : stern (2*m+1) = stern m + stern (m+1) := by
  unfold stern
  rw [splitSum]
  have he : (2*m+1+1)/2 = m+1 := by omega
  have ho : (2*m+1)/2 = m := by omega
  rw [he,ho,add_comm]
  congr 1
  · apply sum_congr rfl
    intro j hj
    have := mem_range.mp hj
    have h : (2*m+1-1-(2*j+1))%2 = 1 := by omega
    have h' : (2*j+1)%2 = 1 := by omega
    have d : (2*m+1-1-(2*j+1))/2 = m-1-j := by omega
    have d' : (2*j+1)/2 = j := by omega
    rw [lucas,h,h',d,d']
    simp
  · apply sum_congr rfl
    intro j hj
    have := mem_range.mp hj
    have d : (2*m+1-1-2*j)/2 = m+1-1-j := by omega
    exact d ▸ evenChoose (2*m+1-1-2*j) j

private theorem edge_eq (m : ℕ) : edge m = (stern m, stern (m+1)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => decide +kernel
    | succ m =>
      let k := (m+1)/2
      have e := ih k (by dsimp [k]; omega)
      rw [edge,e]
      rcases Nat.mod_two_eq_zero_or_one (m+1) with h|h
      · simp only [h, ↓reduceIte]
        have hk : m+1 = 2*k := by dsimp [k]; omega
        change (stern k, stern k + stern (k+1)) = (stern (m+1), stern (m+1+1))
        rw [hk,stern_even,stern_odd]
      · simp only [h, Nat.reduceEqDiff, ↓reduceIte]
        have hk : m+1 = 2*k+1 := by dsimp [k]; omega
        have hk' : m+1+1 = 2*(k+1) := by omega
        change (stern k + stern (k+1), stern (k+1)) = (stern (m+1), stern (m+1+1))
        rw [hk',hk,stern_even,stern_odd]

private theorem diagonal_eq (n : ℕ) : diagonal n = stern (n/2+1) + stern (n/2) := by
  unfold diagonal
  rw [splitSum, stern_short (n/2+1), stern_short (n/2)]
  congr 1
  · apply sum_congr rfl
    intro j hj
    have := mem_range.mp hj
    have h : (2*j)/2+(n-2*(2*j))/2 = n/2+1-1-j := by omega
    rw [entry, ← Nat.choose_symm_add, h]
    congr 2
    omega
  · apply sum_congr rfl
    intro j hj
    have := mem_range.mp hj
    have h : (2*j+1)/2+(n-2*(2*j+1))/2 = n/2-1-j := by omega
    rw [entry, ← Nat.choose_symm_add, h]
    congr 2
    omega

theorem result (n : ℕ) : diagonal n = fareyDenominator (n/2) := by
  rw [diagonal_eq, fareyDenominator, edge_eq]
  exact add_comm _ _

end OMA.ShallowDiagonal114214

theorem OMA.solution : type_of% @OMA.S_oeis_a114214.main :=
  OMA.ShallowDiagonal114214.result
