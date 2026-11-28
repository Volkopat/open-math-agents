import OMAStatements.S_oeis_a159881
import Mathlib.Tactic

open OMA.S_oeis_a159881 Finset

namespace AbsoluteTriangle

private def magnitude (n k : ℕ) : ℕ :=
  ∑ t ∈ range (n+1), (n+1-t)*Nat.stirlingSecond t k

private lemma first (n : ℕ) : magnitude n 0=n+1 := by
  unfold magnitude
  rw [sum_range_succ']
  simp

private lemma shift (n k : ℕ) :
    magnitude (n+1) (k+1) = (k+1)*magnitude n (k+1)+magnitude n k := by
  unfold magnitude
  rw [sum_range_succ' _ (n+1)]
  simp only [Nat.stirlingSecond_zero_succ,mul_zero,add_zero]
  rw [mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [Nat.stirlingSecond_succ_succ,show n+1+1-(i+1)=n+1-i by omega]
  ring

private lemma signed (n k : ℕ) : triangle n k = (-1:ℤ)^k * (magnitude n k:ℤ) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [triangle,magnitude]
    | succ k => simp [triangle,magnitude]
  | succ n ih =>
    cases k with
    | zero => rw [first]; simp [triangle]; ring
    | succ k =>
      rw [triangle,ih (k+1),ih k,shift,pow_succ]
      push_cast
      ring

private lemma fullBell (n m : ℕ) (hm : m≤n) :
    ∑ k ∈ range (n+1), Nat.stirlingSecond m k = bellCount m := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [show m+r+1=m+1+r by omega,sum_range_add]
  have tail : ∑ k ∈ range r, Nat.stirlingSecond m (m+1+k) = 0 := by
    apply sum_eq_zero
    intro k _
    exact Nat.stirlingSecond_eq_zero_of_lt (by omega)
  rw [tail,add_zero]
  rfl

end AbsoluteTriangle

theorem OMA.solution : type_of% @OMA.S_oeis_a159881.main := by
  intro n
  have absolute (k : ℕ) : (triangle n k).natAbs = AbsoluteTriangle.magnitude n k := by
    rw [AbsoluteTriangle.signed]
    simp [Int.natAbs_mul,Int.natAbs_pow]
  simp_rw [absolute]
  unfold AbsoluteTriangle.magnitude
  rw [sum_comm]
  apply sum_congr rfl
  intro m hm
  rw [← mul_sum,AbsoluteTriangle.fullBell n m (by have := mem_range.mp hm; omega)]
