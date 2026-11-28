import OMAStatements.S_oeis_a363166
import Mathlib.Tactic

open OMA.S_oeis_a363166 Finset

namespace BoutonCount

private lemma middle_iff {y z : ℕ} (hy : y < z) :
    (0 < y ^^^ z ∧ y ^^^ z < y) ↔ 2^z.log2 ≤ y := by
  let b := 2^z.log2
  have bp : 0 < b := pow_pos (by decide) _
  have lo : b ≤ z := Nat.log2_self_le (by omega)
  have hi : z < 2*b := by simpa [b, pow_succ, Nat.mul_comm] using Nat.lt_log2_self (n := z)
  have zd : z / b = 1 := Nat.div_eq_of_lt_le (by simpa using lo) (by simpa using hi)
  have divXor : (y ^^^ z) / b = (y / b) ^^^ (z / b) := Nat.xor_div_two_pow
  have nonzero : y ^^^ z ≠ 0 := by
    intro h
    have e : (y ^^^ z) ^^^ z = y := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [h, Nat.zero_xor] at e
    omega
  change (0 < y ^^^ z ∧ y ^^^ z < y) ↔ b ≤ y
  by_cases below : y < b
  · have yd := Nat.div_eq_of_lt below
    rw [zd, yd] at divXor
    have xd : (y ^^^ z) / b = 1 := divXor
    have high : b ≤ y ^^^ z := by
      have hh := (Nat.le_div_iff_mul_le bp).1 (show 1 ≤ (y ^^^ z) / b by omega)
      simpa using hh
    omega
  · have yd : y / b = 1 :=
      Nat.div_eq_of_lt_le (by simpa using Nat.le_of_not_gt below) (by omega)
    rw [zd, yd, Nat.xor_self] at divXor
    have low := Nat.lt_of_div_eq_zero bp divXor
    omega

private lemma count (z : ℕ) : largestHeapCount z = z - 2^z.log2 := by
  have eqn : (range z).filter (fun y => 0 < y ^^^ z ∧ y ^^^ z < y) =
      Ico (2^z.log2) z := by
    ext y
    simp only [mem_filter, mem_range, mem_Ico]
    by_cases h : y < z
    · simp [h, middle_iff h]
    · simp [h]
  rw [largestHeapCount, eqn, Nat.card_Ico]

private lemma geometric (k : ℕ) : 1 + ∑ i ∈ range k, (2 : ℕ)^i = 2^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, pow_succ]; omega

private lemma difference (j : ℕ) (hj : 0 < j) : firstCumulative j = 2^j.log2 := by
  have eqn : (range j).filter (fun i => 2^(i+1) ≤ j) = range j.log2 := by
    ext i
    simp only [mem_filter, mem_range, ← Nat.le_log2 (Nat.ne_of_gt hj)]
    have := Nat.log2_le_self j
    omega
  rw [firstCumulative, eqn, geometric]

end BoutonCount

theorem OMA.solution : type_of% @OMA.S_oeis_a363166.main := by
  intro n hn
  have total : bouton n + a063915 (n-1) = ∑ i ∈ range n, (i+1) := by
    rw [bouton, a063915, show n-1+1 = n by omega, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [BoutonCount.count, BoutonCount.difference _ (by omega)]
    exact Nat.sub_add_cancel (Nat.log2_self_le (by omega))
  omega
