import OMAStatements.S_oeis_a289682
import Mathlib

-- Problem: oeis-a289682
-- Credit: @rickmanelius (the owner of the agent is credited as the solver)
--
-- Approach. Write c(k) = catalan (2^k - 1) and P m = 1 * 3 * ... * (2m - 1).
-- From (n + 1) * centralBinom (n + 1) = 2 * (2n + 1) * centralBinom n we get
-- centralBinom m * m! = 2^m * P m and (2m)! = 2^m * m! * P m, hence
-- centralBinom (2m) * (P m)^2 = centralBinom m * P (2m).
-- Every block of 16 consecutive odd numbers multiplies to 1 mod 32, so P m = 1 mod 32 when 16 divides m,
-- and centralBinom (2^(k+1)) = centralBinom (2^k) mod 32 for k at least 4.
-- Also centralBinom (2^k) + 2 c(k) = 2^(k+2) c(k), which is 0 mod 32 for k at least 4.
-- So c(k+1) = c(k) mod 16 for k at least 4, and c(4) = catalan 15 = 9694845 = 13 mod 16; c(3) = 429.
-- Finally (2^k + 1) * catalan (2^k) = centralBinom (2^k) = -2 c(k) mod 32 gives
-- catalan (2^k) = -26 = 6 mod 16 for k at least 4, and catalan 8 = 1430 covers k = 3.

namespace OMA.P289682
open OMA.S_oeis_a289682

/-- The product of the first m odd numbers, 1 * 3 * ... * (2m - 1). -/
def P (m : ℕ) : ℕ := ∏ i ∈ Finset.range m, (2 * i + 1)

lemma P_succ (m : ℕ) : P (m + 1) = P m * (2 * m + 1) := by
  unfold P; rw [Finset.prod_range_succ]

lemma P_add (m n : ℕ) : P (m + n) = P m * ∏ i ∈ Finset.range n, (2 * (m + i) + 1) := by
  unfold P; rw [Finset.prod_range_add]

/-- centralBinom m * m! = 2^m * P m. -/
lemma cb_fact (m : ℕ) : Nat.centralBinom m * m.factorial = 2 ^ m * P m := by
  induction m with
  | zero => simp [P]
  | succ m ih =>
    have h := Nat.succ_mul_centralBinom_succ m
    rw [Nat.factorial_succ, P_succ, pow_succ]
    calc Nat.centralBinom (m + 1) * ((m + 1) * m.factorial)
        = ((m + 1) * Nat.centralBinom (m + 1)) * m.factorial := by ring
      _ = 2 * (2 * m + 1) * Nat.centralBinom m * m.factorial := by rw [h]
      _ = 2 * (2 * m + 1) * (Nat.centralBinom m * m.factorial) := by ring
      _ = 2 * (2 * m + 1) * (2 ^ m * P m) := by rw [ih]
      _ = 2 ^ m * 2 * (P m * (2 * m + 1)) := by ring

/-- (2m)! = 2^m * m! * P m. -/
lemma fact_two_mul (m : ℕ) : (2 * m).factorial = 2 ^ m * m.factorial * P m := by
  induction m with
  | zero => simp [P]
  | succ m ih =>
    have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [e, Nat.factorial_succ (2 * m + 1), Nat.factorial_succ (2 * m), ih, Nat.factorial_succ m,
      P_succ, pow_succ]
    ring

/-- centralBinom (2m) * (P m)^2 = centralBinom m * P (2m). -/
lemma cb_double (m : ℕ) : Nat.centralBinom (2 * m) * P m ^ 2 = Nat.centralBinom m * P (2 * m) := by
  have h1 := cb_fact (2 * m)
  have h2 := cb_fact m
  have h3 := fact_two_mul m
  rw [h3] at h1
  have hpos : 0 < 2 ^ m * m.factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc 2 ^ m * m.factorial * (Nat.centralBinom (2 * m) * P m ^ 2)
      = (Nat.centralBinom (2 * m) * (2 ^ m * m.factorial * P m)) * P m := by ring
    _ = 2 ^ (2 * m) * P (2 * m) * P m := by rw [h1]
    _ = 2 ^ m * (2 ^ m * P m) * P (2 * m) := by rw [two_mul, pow_add]; ring
    _ = 2 ^ m * (Nat.centralBinom m * m.factorial) * P (2 * m) := by rw [h2]
    _ = 2 ^ m * m.factorial * (Nat.centralBinom m * P (2 * m)) := by ring

/-- A block of 16 consecutive odd numbers multiplies to 1 mod 32. -/
lemma blk (q : ℕ) :
    (((∏ i ∈ Finset.range 16, (2 * (16 * q + i) + 1) : ℕ)) : ZMod 32) = 1 := by
  rw [Nat.cast_prod]
  have key : ∀ i ∈ Finset.range 16,
      (((2 * (16 * q + i) + 1 : ℕ)) : ZMod 32) = ((2 * i + 1 : ℕ) : ZMod 32) := by
    intro i _
    exact (ZMod.natCast_eq_natCast_iff' _ _ 32).mpr (by omega)
  rw [Finset.prod_congr rfl key]
  decide

lemma P_mul16 (q : ℕ) : ((P (16 * q) : ℕ) : ZMod 32) = 1 := by
  induction q with
  | zero => simp [P]
  | succ q ih =>
    rw [show 16 * (q + 1) = 16 * q + 16 by ring, P_add, Nat.cast_mul, ih, blk, one_mul]

lemma P_of_dvd (m : ℕ) (h : 16 ∣ m) : ((P m : ℕ) : ZMod 32) = 1 := by
  obtain ⟨q, rfl⟩ := h
  exact P_mul16 q

lemma cb_double_mod (m : ℕ) (h : 16 ∣ m) :
    Nat.centralBinom (2 * m) % 32 = Nat.centralBinom m % 32 := by
  have e := congrArg (fun x : ℕ => (x : ZMod 32)) (cb_double m)
  simp only [Nat.cast_mul, Nat.cast_pow] at e
  rw [P_of_dvd m h, P_of_dvd (2 * m) (Dvd.dvd.mul_left h 2)] at e
  simp only [one_pow, mul_one] at e
  exact (ZMod.natCast_eq_natCast_iff' _ _ 32).mp e

lemma cb_succ (n : ℕ) : Nat.centralBinom (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h1 := Nat.succ_mul_centralBinom_succ n
  have h2 := succ_mul_catalan_eq_centralBinom n
  apply Nat.eq_of_mul_eq_mul_left (show 0 < n + 1 by omega)
  rw [h1, ← h2]; ring

lemma dvd_mul_mod (d X c : ℕ) (h : d ∣ X) : (X * c) % d = 0 := by
  obtain ⟨t, rfl⟩ := h
  rw [show d * t * c = d * (t * c) by ring]
  exact Nat.mul_mod_right _ _

lemma cb_pow (k : ℕ) :
    Nat.centralBinom (2 ^ k) + 2 * catalan (2 ^ k - 1) = 2 * 2 ^ (k + 1) * catalan (2 ^ k - 1) := by
  obtain ⟨s, hs⟩ : ∃ s, 2 ^ k = s + 1 := ⟨2 ^ k - 1, by have := @Nat.one_le_two_pow k; omega⟩
  have h := cb_succ s
  rw [hs, pow_succ, hs, h, Nat.add_sub_cancel]
  ring

lemma c_step (k : ℕ) (hk : 4 ≤ k) :
    catalan (2 ^ (k + 1) - 1) % 16 = catalan (2 ^ k - 1) % 16 := by
  have h16 : 16 ∣ 2 ^ k := by
    have := pow_dvd_pow 2 hk
    simpa using this
  have h32 : 32 ∣ 2 ^ (k + 1) := by
    have := pow_dvd_pow 2 (show 5 ≤ k + 1 by omega)
    simpa using this
  have hA := cb_double_mod (2 ^ k) h16
  rw [show 2 * 2 ^ k = 2 ^ (k + 1) by rw [pow_succ]; ring] at hA
  have hB := cb_pow k
  have hC := cb_pow (k + 1)
  have hB' : (2 * 2 ^ (k + 1) * catalan (2 ^ k - 1)) % 32 = 0 :=
    dvd_mul_mod 32 _ _ (Dvd.dvd.mul_left h32 2)
  have hC' : (2 * 2 ^ (k + 1 + 1) * catalan (2 ^ (k + 1) - 1)) % 32 = 0 :=
    dvd_mul_mod 32 _ _ (Dvd.dvd.mul_left (dvd_trans h32 (pow_dvd_pow 2 (by omega))) 2)
  omega

lemma first_part (k : ℕ) (hk : 3 ≤ k) : catalan (2 ^ k - 1) % 16 = 13 := by
  rcases Nat.lt_or_ge k 4 with h | h
  · obtain rfl : k = 3 := by omega
    rw [show 2 ^ 3 - 1 = 7 by norm_num, catalan_eq_centralBinom_div]
    decide
  · induction k, h using Nat.le_induction with
    | base =>
      rw [show 2 ^ 4 - 1 = 15 by norm_num, catalan_eq_centralBinom_div, Nat.centralBinom,
        Nat.choose_eq_factorial_div_factorial (by norm_num)]
      decide
    | succ k hk4 ih =>
      rw [c_step k hk4]
      exact ih (by omega)

lemma second_part (k : ℕ) (hk : 3 ≤ k) : catalan (2 ^ k) % 16 = 6 := by
  rcases Nat.lt_or_ge k 4 with h | h
  · obtain rfl : k = 3 := by omega
    rw [show 2 ^ 3 = 8 by norm_num, catalan_eq_centralBinom_div]
    decide
  · have h16 : 16 ∣ 2 ^ k := by
      have := pow_dvd_pow 2 h
      simpa using this
    have h32 : 32 ∣ 2 ^ (k + 1) := by
      have := pow_dvd_pow 2 (show 5 ≤ k + 1 by omega)
      simpa using this
    have hc := first_part k hk
    have hB := cb_pow k
    have hB' : (2 * 2 ^ (k + 1) * catalan (2 ^ k - 1)) % 32 = 0 :=
      dvd_mul_mod 32 _ _ (Dvd.dvd.mul_left h32 2)
    have hD := succ_mul_catalan_eq_centralBinom (2 ^ k)
    have hW : (2 ^ k * catalan (2 ^ k)) % 16 = 0 := dvd_mul_mod 16 _ _ h16
    rw [add_mul, one_mul] at hD
    omega

theorem sol : type_of% @OMA.S_oeis_a289682.main := by
  intro n hn
  exact ⟨first_part n hn, second_part n hn⟩

end OMA.P289682

theorem OMA.solution : type_of% @OMA.S_oeis_a289682.main := OMA.P289682.sol

