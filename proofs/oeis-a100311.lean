import OMAStatements.S_oeis_a100311

open OMA.S_oeis_a100311

namespace BinomialBits

private def encode (b : ℕ → ℕ) (m : ℕ) :=
  ∑ k ∈ Finset.range m, (b k % 2) * 8 ^ k

private theorem encode_succ (b : ℕ → ℕ) (m : ℕ) :
    encode b (m+1) = 8 * encode (fun k => b (k+1)) m + b 0 % 2 := by
  unfold encode
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_left_comm, mul_comm]

private theorem encode_bit (b : ℕ → ℕ) (m k r : ℕ) (hr : r < 3) :
    (encode b m).testBit (3*k+r) =
      if r = 0 ∧ k < m then decide (b k % 2 = 1) else false := by
  induction m generalizing b k with
  | zero => simp [encode]
  | succ m ih =>
    rw [encode_succ, show (8:ℕ) = 2^3 by decide,
      Nat.testBit_two_pow_mul_add _ (by omega : b 0 % 2 < 2^3)]
    cases k with
    | zero =>
      simp only [mul_zero, zero_add, hr, if_true, Nat.zero_lt_succ, and_true]
      have h : b 0 % 2 < 2 := Nat.mod_lt _ (by decide)
      interval_cases r
      · simp [Nat.testBit_eq_decide_div_mod_eq]
      · simp [Nat.testBit_eq_decide_div_mod_eq]
      · simp [Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt (by omega : b 0 % 2 < 4)]
    | succ k =>
      have h₁ : ¬ 3*(k+1)+r < 3 := by omega
      have h₂ : 3*(k+1)+r-3 = 3*k+r := by omega
      simp only [h₁, if_false, h₂]
      rw [ih _ _]
      simp

private theorem a_bit (n k r : ℕ) (hr : r < 3) :
    (a n).testBit (3*k+r) = if r = 0 then decide (n.choose k % 2 = 1) else false := by
  change (encode n.choose (n+1)).testBit _ = _
  rw [encode_bit _ _ _ _ hr]
  by_cases hk : k < n+1
  · simp [hk]
  · simp [hk, Nat.choose_eq_zero_of_lt (by omega : n < k)]

private theorem add_parity (u v : ℕ) :
    decide ((u+v)%2 = 1) = (decide (u%2=1) ^^ decide (v%2=1)) := by
  rw [Nat.add_mod u v 2]
  have hu : u%2 < 2 := Nat.mod_lt _ (by decide)
  have hv : v%2 < 2 := Nat.mod_lt _ (by decide)
  rcases (show u%2=0 ∨ u%2=1 by omega) with h₁ | h₁ <;>
    rcases (show v%2=0 ∨ v%2=1 by omega) with h₂ | h₂ <;> simp [h₁,h₂]

theorem result : type_of% @OMA.S_oeis_a100311.main := by
  refine ⟨by decide, fun n => ?_⟩
  apply Nat.eq_of_testBit_eq
  intro j
  obtain ⟨k,r,hr,rfl⟩ : ∃ k r, r < 3 ∧ j = 3*k+r := ⟨j/3,j%3,by omega,by omega⟩
  rw [Nat.testBit_xor, show (8:ℕ) = 2^3 by decide, Nat.testBit_mul_two_pow]
  cases k with
  | zero =>
    have hj : ¬ 3 ≤ 3*0+r := by omega
    rw [a_bit (n+1) 0 r hr, a_bit n 0 r hr]
    rw [show decide (3 ≤ 3*0+r) = false from decide_eq_false hj]
    simp
  | succ k =>
    have hj : 3 ≤ 3*(k+1)+r := by omega
    have hsub : 3*(k+1)+r-3 = 3*k+r := by omega
    simp only [hj, decide_true, Bool.true_and, hsub, a_bit _ _ _ hr]
    by_cases hh : r = 0
    · simp only [hh, if_true, Nat.choose_succ_succ']
      exact add_parity _ _
    · simp [hh]

end BinomialBits

theorem OMA.solution : type_of% @OMA.S_oeis_a100311.main := BinomialBits.result