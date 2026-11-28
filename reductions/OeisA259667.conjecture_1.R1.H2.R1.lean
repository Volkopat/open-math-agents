import OMAReductions.R_OeisA259667_conjecture_1_R1

-- Reduction OeisA259667.conjecture_1.R1.H2.R1 of step OeisA259667.conjecture_1.R1.H2
-- Credit: @rickmanelius

/-!
# Catalan numbers modulo 6 at `2 ^ k - 1`: ternary digits settle two thirds of the exponents

The step is the open direction of the conjecture: `C (2 ^ k - 1) ≡ 1 (mod 6)` only for
`k = 0, 1, 5`.

Proved below with no hypothesis:
* `centralBinom_mod_three` (Lucas's theorem, one base-3 digit at a time): `C(2 n, n) mod 3` is `0`
  if `n` has a digit `2` in base 3, and otherwise `1` or `2` according as `n` is even or odd.
* `odd_and_no_two`: since `2 ^ k * C (2 ^ k - 1) = C(2 ^ (k+1) - 2, 2 ^ k - 1)` and
  `2 ^ k ≡ (-1) ^ k (mod 3)`, residue `1` modulo `6` with `k > 0` forces `k` odd and no digit `2`
  in `2 ^ k - 1`.
* Write `k = 2 j + 1` and `j = 3 ^ v * w` with `3 ∤ w`. From `4 ^ (3 ^ v) = 1 + 3 ^ (v + 1) u`
  with `u ≡ 1 (mod 3)`, and `u ≡ 7 (mod 9)` once `v ≥ 1`, one gets
  `2 ^ k - 1 = 2 * 4 ^ j - 1 ≡ 1 + 3 ^ (v + 1) * 2 u w (mod 3 ^ (2 v + 2))`. So `2 ^ k - 1` has
  the digit `2` when `w ≡ 1 (mod 3)` (position `v + 1`, `odd_digit_one`), when `v ≥ 1` and
  `w ≡ 5 (mod 9)` (position `v + 2`, `odd_digit_two_b`), and when `v = 0` and `j ≡ 5 (mod 9)`
  (`2 * 4 ^ j - 1 ≡ 22 (mod 27)`, `odd_digit_two_a`).
These settle two thirds of the odd exponents in natural density. What is left:
* `H1`: `k ≡ 5` or `17 (mod 18)`, that is `j ≡ 2` or `8 (mod 9)` with `3 ∤ j`; this class
  contains the exception `k = 5` (`2 ^ 5 - 1 = 31` is `1011` in base 3);
* `H2`: `k ≡ 1 (mod 6)`, `k > 1`, and the `3`-free part of `j = k / 2` is `≡ 2` or
  `8 (mod 9)`; here no exception is expected.
A check of `2 * 4 ^ j - 1` for `j < 3000` found no failure of the three regimes and no survivor
without a digit `2` other than `j = 2`.
-/

namespace OMA.R_OeisA259667_conjecture_1_R1_H2_R1

/-- The exponents `k ≡ 5, 17 (mod 18)`: residue one only at `k = 5`. -/
def H1 : Prop :=
  ∀ k : ℕ, (k % 18 = 5 ∨ k % 18 = 17) → OeisA259667.a (2 ^ k - 1) = 1 → k = 5

/-- The exponents `k ≡ 1 (mod 6)`, `k > 1`, whose half `j = k / 2` has `3`-free part
`≡ 2, 8 (mod 9)`: residue one never occurs. -/
def H2 : Prop :=
  ∀ k : ℕ, k % 6 = 1 → 1 < k →
    (k / 2 / 3 ^ padicValNat 3 (k / 2) % 9 = 2 ∨ k / 2 / 3 ^ padicValNat 3 (k / 2) % 9 = 8) →
    OeisA259667.a (2 ^ k - 1) = 1 → False

/-- A base-3 digit `2` at position `m` puts `2` in the digit list. -/
lemma two_mem_digits : ∀ (m N : ℕ), N / 3 ^ m % 3 = 2 → 2 ∈ Nat.digits 3 N
  | 0, N, h => by
    have hN : 0 < N := by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp at h
      · exact hN
    rw [Nat.digits_def' (by norm_num) hN]
    simp only [pow_zero, Nat.div_one] at h
    exact List.mem_cons.mpr (Or.inl h.symm)
  | m + 1, N, h => by
    have hN : 0 < N := by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp at h
      · exact hN
    rw [Nat.digits_def' (by norm_num) hN]
    apply List.mem_cons_of_mem
    apply two_mem_digits m (N / 3)
    rw [Nat.div_div_eq_div_mul, ← pow_succ']
    exact h

/-- `(1 + a) ^ w = 1 + a w + a ^ 2 c` for some `c`. -/
lemma one_add_pow (a : ℕ) : ∀ w : ℕ, ∃ c, (1 + a) ^ w = 1 + a * w + a ^ 2 * c
  | 0 => ⟨0, by simp⟩
  | w + 1 => by
    obtain ⟨c, hc⟩ := one_add_pow a w
    exact ⟨w + c + a * c, by rw [pow_succ, hc]; ring⟩

/-- `4 ^ (3 ^ v) = 1 + 3 ^ (v + 1) u` with `u ≡ 1 (mod 3)`. -/
lemma four_pow_three_pow : ∀ v : ℕ, ∃ u, 4 ^ 3 ^ v = 1 + 3 ^ (v + 1) * u ∧ u % 3 = 1
  | 0 => ⟨1, by norm_num, by norm_num⟩
  | v + 1 => by
    obtain ⟨u, hu, hu3⟩ := four_pow_three_pow v
    refine ⟨u + 3 ^ (v + 1) * u ^ 2 + 3 ^ (2 * v + 1) * u ^ 3, ?_, ?_⟩
    · have e : 4 ^ 3 ^ (v + 1) = (4 ^ 3 ^ v) ^ 3 := by rw [← pow_mul, ← pow_succ]
      rw [e, hu]
      ring
    · have h1 : 3 ^ (v + 1) * u ^ 2 = 3 * (3 ^ v * u ^ 2) := by ring
      have h2 : 3 ^ (2 * v + 1) * u ^ 3 = 3 * (3 ^ (2 * v) * u ^ 3) := by ring
      rw [h1, h2]
      omega

/-- For `v = k + 1 ≥ 1`: `4 ^ (3 ^ v) = 1 + 3 ^ (v + 1) u` with `u ≡ 7 (mod 9)`. -/
lemma four_pow_three_pow_succ :
    ∀ k : ℕ, ∃ u, 4 ^ 3 ^ (k + 1) = 1 + 3 ^ (k + 2) * u ∧ u % 9 = 7
  | 0 => ⟨7, by norm_num, by norm_num⟩
  | k + 1 => by
    obtain ⟨u, hu, hu9⟩ := four_pow_three_pow_succ k
    refine ⟨u + 3 ^ (k + 2) * u ^ 2 + 3 ^ (2 * k + 3) * u ^ 3, ?_, ?_⟩
    · have e : 4 ^ 3 ^ (k + 1 + 1) = (4 ^ 3 ^ (k + 1)) ^ 3 := by rw [← pow_mul, ← pow_succ]
      rw [e, hu]
      ring
    · have h1 : 3 ^ (k + 2) * u ^ 2 = 9 * (3 ^ k * u ^ 2) := by ring
      have h2 : 3 ^ (2 * k + 3) * u ^ 3 = 9 * (3 ^ (2 * k + 1) * u ^ 3) := by ring
      rw [h1, h2]
      omega

/-- If `w ≡ 1 (mod 3)`, `2 * 4 ^ (3 ^ v * w) - 1` has the digit `2` at position `v + 1`. -/
lemma odd_digit_one (v w : ℕ) (hw : w % 3 = 1) :
    2 ∈ Nat.digits 3 (2 * 4 ^ (3 ^ v * w) - 1) := by
  obtain ⟨u, hu, hu3⟩ := four_pow_three_pow v
  obtain ⟨c, hc⟩ := one_add_pow (3 ^ (v + 1) * u) w
  have h4 : 4 ^ (3 ^ v * w) = 1 + 3 ^ (v + 1) * (u * w + 3 * (3 ^ v * (u ^ 2 * c))) := by
    rw [pow_mul, hu, hc]
    ring
  have hN : 2 * 4 ^ (3 ^ v * w) - 1 =
      1 + 3 ^ (v + 1) * (2 * (u * w) + 3 * (2 * (3 ^ v * (u ^ 2 * c)))) := by
    rw [h4]
    have e : 3 ^ (v + 1) * (2 * (u * w) + 3 * (2 * (3 ^ v * (u ^ 2 * c)))) =
        2 * (3 ^ (v + 1) * (u * w + 3 * (3 ^ v * (u ^ 2 * c)))) := by ring
    rw [e]
    omega
  have hlt : 1 < 3 ^ (v + 1) := Nat.one_lt_pow (Nat.succ_ne_zero v) (by norm_num)
  apply two_mem_digits (v + 1)
  rw [hN, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add,
    Nat.add_mul_mod_self_left, Nat.mul_mod, Nat.mul_mod u, hu3, hw]

/-- If `v ≥ 1` and `w ≡ 5 (mod 9)`, the digit at position `v + 2` is `2`. -/
lemma odd_digit_two_b (v w : ℕ) (hv : 1 ≤ v) (hw : w % 9 = 5) :
    2 ∈ Nat.digits 3 (2 * 4 ^ (3 ^ v * w) - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, v = k + 1 := ⟨v - 1, by omega⟩
  obtain ⟨u, hu, hu9⟩ := four_pow_three_pow_succ k
  obtain ⟨c, hc⟩ := one_add_pow (3 ^ (k + 2) * u) w
  have h4 : 4 ^ (3 ^ (k + 1) * w) =
      1 + 3 ^ (k + 2) * (u * w + 9 * (3 ^ k * (u ^ 2 * c))) := by
    rw [pow_mul, hu, hc]
    ring
  have hN : 2 * 4 ^ (3 ^ (k + 1) * w) - 1 =
      1 + 3 ^ (k + 2) * (2 * (u * w) + 9 * (2 * (3 ^ k * (u ^ 2 * c)))) := by
    rw [h4]
    have e : 3 ^ (k + 2) * (2 * (u * w) + 9 * (2 * (3 ^ k * (u ^ 2 * c)))) =
        2 * (3 ^ (k + 2) * (u * w + 9 * (3 ^ k * (u ^ 2 * c)))) := by ring
    rw [e]
    omega
  have hlt : 1 < 3 ^ (k + 2) := Nat.one_lt_pow (Nat.succ_ne_zero _) (by norm_num)
  apply two_mem_digits (k + 3)
  rw [hN, pow_succ 3 (k + 2), ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt hlt, zero_add, ← Nat.mod_mul_right_div_self, Nat.add_mul_mod_self_left,
    Nat.mul_mod, Nat.mul_mod u, hu9, hw]

/-- If `j ≡ 5 (mod 9)`, then `2 * 4 ^ j - 1 ≡ 22 (mod 27)`: digit `2` at position `2`. -/
lemma odd_digit_two_a (j : ℕ) (hj : j % 9 = 5) : 2 ∈ Nat.digits 3 (2 * 4 ^ j - 1) := by
  apply two_mem_digits 2
  have h27 : 4 ^ j % 27 = 25 := by
    rw [← Nat.div_add_mod j 9, hj, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hN : (2 * 4 ^ j - 1) % 27 = 22 := by omega
  rw [← Nat.mod_mul_right_div_self, show (3 : ℕ) ^ 2 * 3 = 27 by norm_num, hN]
  norm_num

/-- Lucas: `C(2 n, n) mod 3` from the base-3 digits of `n`. -/
lemma centralBinom_mod_three (n : ℕ) : n.centralBinom % 3 =
    if 2 ∈ Nat.digits 3 n then 0 else if n % 2 = 0 then 1 else 2 := by
  have hp : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · decide
    have hq := ih (n / 3) (Nat.div_lt_self hn (by norm_num))
    have hl : (2 * n).choose n % 3 =
        ((2 * n) % 3).choose (n % 3) * ((2 * n) / 3).choose (n / 3) % 3 :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    rw [Nat.centralBinom_eq_two_mul_choose, hl, Nat.digits_def' (by norm_num) hn]
    rw [Nat.centralBinom_eq_two_mul_choose] at hq
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hcases with h | h | h
    · rw [show (2 * n) % 3 = 0 by omega, show (2 * n) / 3 = 2 * (n / 3) by omega, h]
      simp only [Nat.choose_self, one_mul, List.mem_cons]
      rw [hq, show n % 2 = n / 3 % 2 by omega]
      simp
    · rw [show (2 * n) % 3 = 2 by omega, show (2 * n) / 3 = 2 * (n / 3) by omega, h]
      simp only [List.mem_cons, show (2 : ℕ) ≠ 1 by norm_num, false_or]
      rw [Nat.mul_mod, hq]
      have hpar : n % 2 = 0 ↔ n / 3 % 2 = 1 := by omega
      by_cases h2 : 2 ∈ Nat.digits 3 (n / 3)
      · simp [h2]
      · by_cases he : n / 3 % 2 = 0
        · have : ¬ n % 2 = 0 := by omega
          simp [h2, he, this]
        · have : n % 2 = 0 := by omega
          simp [h2, he, this]
    · rw [show (2 * n) % 3 = 1 by omega, h]
      simp

/-- `2 ^ k ≡ 1` or `2 (mod 3)` according to the parity of `k`. -/
lemma two_pow_mod_three (k : ℕ) : 2 ^ k % 3 = if k % 2 = 0 then 1 else 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs <;> omega

/-- `a (2 ^ k - 1) = 1` with `k > 0` forces `k` odd and no digit `2` in `2 ^ k - 1`. -/
lemma odd_and_no_two {k : ℕ} (hk : OeisA259667.a (2 ^ k - 1) = 1) (hkpos : 0 < k) :
    k % 2 = 1 ∧ 2 ∉ Nat.digits 3 (2 ^ k - 1) := by
  have hone : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hsucc : 2 ^ k - 1 + 1 = 2 ^ k := Nat.sub_add_cancel hone
  have hcb := succ_mul_catalan_eq_centralBinom (2 ^ k - 1)
  rw [hsucc] at hcb
  have h6 : catalan (2 ^ k - 1) % 6 = 1 := hk
  have h3 : catalan (2 ^ k - 1) % 3 = 1 := by omega
  have hodd : (2 ^ k - 1) % 2 = 1 := by
    have : 2 ^ k % 2 = 0 := by
      obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
      rw [pow_succ]
      simp
    omega
  have hmod : (2 ^ k - 1).centralBinom % 3 = 2 ^ k % 3 := by
    rw [← hcb, Nat.mul_mod, h3, mul_one, Nat.mod_mod]
  have hc3 := centralBinom_mod_three (2 ^ k - 1)
  rw [hmod, two_pow_mod_three] at hc3
  rw [if_neg (by omega : ¬ (2 ^ k - 1) % 2 = 0)] at hc3
  by_cases hk2 : k % 2 = 0
  · rw [if_pos hk2] at hc3
    split_ifs at hc3 <;> omega
  · rw [if_neg hk2] at hc3
    refine ⟨by omega, fun h2 => ?_⟩
    rw [if_pos h2] at hc3
    omega

theorem main : H1 → H2 → OMA.R_OeisA259667_conjecture_1_R1.H2 := by
  intro h1 h2 k hk
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Or.inl rfl
  obtain ⟨hodd, hno⟩ := odd_and_no_two hk hkpos
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · exact Or.inr (Or.inl rfl)
  have hpow : 2 ^ (2 * j + 1) - 1 = 2 * 4 ^ j - 1 := by
    rw [pow_succ, pow_mul]
    norm_num
    ring_nf
  rw [hpow] at hno
  have hj0 : j ≠ 0 := by omega
  have hhalf : (2 * j + 1) / 2 = j := by omega
  obtain ⟨v, hv⟩ : ∃ v, v = padicValNat 3 j := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : 3 ^ v ∣ j := hv ▸ pow_padicValNat_dvd
  have hw3 : ¬ 3 ∣ w := by
    rintro ⟨t, rfl⟩
    have hnd := pow_succ_padicValNat_not_dvd (p := 3) hj0
    rw [← hv] at hnd
    exact hnd ⟨t, by rw [hw, pow_succ]; ring⟩
  have hdiv : j / 3 ^ padicValNat 3 j = w := by
    rw [← hv, hw, Nat.mul_div_cancel_left _ (by positivity)]
  rcases (show w % 3 = 1 ∨ w % 3 = 2 by omega) with h1w | h2w
  · exact absurd (by rw [hw]; exact odd_digit_one v w h1w) hno
  · rcases Nat.eq_zero_or_pos v with hv0 | hvpos
    · have hjw : j = w := by rw [hw, hv0, pow_zero, one_mul]
      rcases (show w % 9 = 2 ∨ w % 9 = 5 ∨ w % 9 = 8 by omega) with h | h | h
      · exact Or.inr (Or.inr (h1 _ (Or.inl (by omega)) hk))
      · exact absurd (by rw [hjw]; exact odd_digit_two_a w h) hno
      · exact Or.inr (Or.inr (h1 _ (Or.inr (by omega)) hk))
    · have h3j : 3 ∣ j := by
        rw [hw]
        exact Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) w
      rcases (show w % 9 = 2 ∨ w % 9 = 5 ∨ w % 9 = 8 by omega) with h | h | h
      · exact (h2 _ (by omega) (by omega) (Or.inl (by rw [hhalf, hdiv]; exact h)) hk).elim
      · exact absurd (by rw [hw]; exact odd_digit_two_b v w hvpos h) hno
      · exact (h2 _ (by omega) (by omega) (Or.inr (by rw [hhalf, hdiv]; exact h)) hk).elim

end OMA.R_OeisA259667_conjecture_1_R1_H2_R1
