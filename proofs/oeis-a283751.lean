import OMAStatements.S_oeis_a283751
import Mathlib

/-
A283751: for composite n the least base b > 1 such that n, written in base b and read in
base b^2, is a multiple of n satisfies a(n) < n.

Write n = c * b with c the least prime factor, so 2 <= c <= b < n. If c < b, the base-b digits
of n are (0, c), which read in base b^2 give c * b^2 = n * b. If c = b, the digits are (0, 0, 1),
which read in base b^2 give b^4 = n^2. Either way b is in the set whose infimum is a(n).
-/

namespace OMA.P283751

lemma dig (b m : ℕ) (hb : 1 < b) (hm : 0 < m) : Nat.digits b (m * b) = 0 :: Nat.digits b m := by
  rw [Nat.digits_def' hb (Nat.mul_pos hm (by omega)), Nat.mul_mod_left,
    Nat.mul_div_cancel m (by omega)]

lemma main' : ∀ n : ℕ, 1 < n → ¬ n.Prime →
    sInf {b : ℕ | 1 < b ∧ n ∣ Nat.ofDigits (b ^ 2) (Nat.digits b n)} < n := by
  intro n hn hnp
  obtain ⟨c, b, hc2, hcb, rfl⟩ : ∃ c b, 2 ≤ c ∧ c ≤ b ∧ n = c * b := by
    obtain ⟨b, hb⟩ := Nat.minFac_dvd n
    have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
    refine ⟨n.minFac, b, hp.two_le, ?_, hb⟩
    have h := Nat.minFac_sq_le_self (by omega) hnp
    rw [pow_two] at h
    nth_rewrite 3 [hb] at h
    exact Nat.le_of_mul_le_mul_left h hp.pos
  have hb1 : 1 < b := by omega
  have hbn : b < c * b := by nlinarith
  refine lt_of_le_of_lt (Nat.sInf_le ⟨hb1, ?_⟩) hbn
  rcases hcb.lt_or_eq with hlt | rfl
  · rw [dig b c hb1 (by omega), Nat.digits_of_lt b c (by omega) hlt]
    simp only [Nat.ofDigits_cons, Nat.ofDigits_nil]
    exact ⟨b, by ring⟩
  · rw [dig c c hb1 (by omega), show Nat.digits c c = 0 :: Nat.digits c 1 from by
      simpa using dig c 1 hb1 one_pos, Nat.digits_of_lt c 1 one_ne_zero hb1]
    simp only [Nat.ofDigits_cons, Nat.ofDigits_nil]
    exact ⟨c * c, by ring⟩

end OMA.P283751

theorem OMA.solution : type_of% @OMA.S_oeis_a283751.main := by
  intro n hn hnp
  exact OMA.P283751.main' n hn hnp
