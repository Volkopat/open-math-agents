import OMAReductions.R_OeisA259667_conjecture_2_R1

-- Reduction OeisA259667.conjecture_2.R1.H2.R1 of step OeisA259667.conjecture_2.R1.H2
-- Credit: @rickmanelius

/-!
# Ternary digits of `4 ^ j`: the two digits above the 3-adic valuation of `j`

The step is the open tail of the Erdős ternary digit conjecture: `4 ^ j` has a digit `2` in
base 3 for every `j > 3 ^ 45`.

Write `j = 3 ^ v * w` with `3 ∤ w`. Since `4 = 1 + 3`, induction on `v` gives
`4 ^ (3 ^ v) = 1 + 3 ^ (v + 1) * u` with `u ≡ 1 (mod 3)`, and `u ≡ 7 (mod 9)` once `v ≥ 1`
(`four_pow_three_pow`, `four_pow_three_pow_succ`). Raising this to the power `w` and dropping the
terms divisible by `3 ^ (2 v + 2)` gives `4 ^ j ≡ 1 + 3 ^ (v + 1) * u * w (mod 3 ^ (2 v + 2))`.
So the base-3 digits of `4 ^ j` at the positions `1, …, v` vanish and the digit at position
`v + 1` is `w mod 3`.

Proved below with no hypothesis, for every exponent `j`:
* `w ≡ 2 (mod 3)`: the digit at position `v + 1` is `2` (`regime_one`);
* `v ≥ 1` and `w ≡ 1 (mod 9)`: the digits at positions `v + 1` and `v + 2` are those of
  `7 w ≡ 7 (mod 9)`, so the digit at position `v + 2` is `2` (`regime_two_b`);
* `v = 0` and `j ≡ 7 (mod 9)`: `4 ^ j ≡ 22 (mod 27)`, and `22` is `211` in base 3
  (`regime_two_a`).
These settle two thirds of all exponents in natural density. What is left of the tail is split by
whether `3` divides `j`:
* `H1`: `j ≡ 1` or `4 (mod 9)`;
* `H2`: `3 ∣ j` and the `3`-free part of `j` is `≡ 4` or `7 (mod 9)`.
Each further digit removes about a third of what is left, but no finite number of digits settles
the tail: for every `d`, the exponents `j ≡ 0` and `j ≡ 4 (mod 3 ^ d)` have their lowest `d + 1`
digits in `{0, 1}` (those of `1` and of `4 ^ 4 = 256`, which is `100111` in base 3).
-/

namespace OMA.R_OeisA259667_conjecture_2_R1_H2_R1

/-- The tail for the exponents prime to `3` that the first two digits leave open:
`j ≡ 1` or `4 (mod 9)`. -/
def H1 : Prop := ∀ j : ℕ, 3 ^ 45 < j → (j % 9 = 1 ∨ j % 9 = 4) → 2 ∈ Nat.digits 3 (4 ^ j)

/-- The tail for the exponents divisible by `3` that the two digits above the valuation leave
open: the `3`-free part of `j` is `≡ 4` or `7 (mod 9)`. -/
def H2 : Prop := ∀ j : ℕ, 3 ^ 45 < j → 3 ∣ j →
    (j / 3 ^ padicValNat 3 j % 9 = 4 ∨ j / 3 ^ padicValNat 3 j % 9 = 7) →
    2 ∈ Nat.digits 3 (4 ^ j)

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

/-- If `w ≡ 2 (mod 3)`, the digit of `4 ^ (3 ^ v * w)` at position `v + 1` is `2`. -/
lemma regime_one (v w : ℕ) (hw : w % 3 = 2) : 2 ∈ Nat.digits 3 (4 ^ (3 ^ v * w)) := by
  obtain ⟨u, hu, hu3⟩ := four_pow_three_pow v
  obtain ⟨c, hc⟩ := one_add_pow (3 ^ (v + 1) * u) w
  have hN : 4 ^ (3 ^ v * w) = 1 + 3 ^ (v + 1) * (u * w + 3 * (3 ^ v * (u ^ 2 * c))) := by
    rw [pow_mul, hu, hc]
    ring
  have hlt : 1 < 3 ^ (v + 1) := Nat.one_lt_pow (Nat.succ_ne_zero v) (by norm_num)
  apply two_mem_digits (v + 1)
  rw [hN, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add,
    Nat.add_mul_mod_self_left, Nat.mul_mod, hu3, hw]

/-- If `v ≥ 1` and `w ≡ 1 (mod 9)`, the digit of `4 ^ (3 ^ v * w)` at position `v + 2` is `2`. -/
lemma regime_two_b (v w : ℕ) (hv : 1 ≤ v) (hw : w % 9 = 1) :
    2 ∈ Nat.digits 3 (4 ^ (3 ^ v * w)) := by
  obtain ⟨k, rfl⟩ : ∃ k, v = k + 1 := ⟨v - 1, by omega⟩
  obtain ⟨u, hu, hu9⟩ := four_pow_three_pow_succ k
  obtain ⟨c, hc⟩ := one_add_pow (3 ^ (k + 2) * u) w
  have hN : 4 ^ (3 ^ (k + 1) * w) =
      1 + 3 ^ (k + 2) * (u * w + 9 * (3 ^ k * (u ^ 2 * c))) := by
    rw [pow_mul, hu, hc]
    ring
  have hlt : 1 < 3 ^ (k + 2) := Nat.one_lt_pow (Nat.succ_ne_zero _) (by norm_num)
  apply two_mem_digits (k + 3)
  rw [hN, pow_succ 3 (k + 2), ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt hlt, zero_add, ← Nat.mod_mul_right_div_self, Nat.add_mul_mod_self_left,
    Nat.mul_mod, hu9, hw]

/-- If `j ≡ 7 (mod 9)`, then `4 ^ j ≡ 22 (mod 27)` and its digit at position `2` is `2`. -/
lemma regime_two_a (j : ℕ) (hj : j % 9 = 7) : 2 ∈ Nat.digits 3 (4 ^ j) := by
  apply two_mem_digits 2
  have h27 : 4 ^ j % 27 = 22 := by
    rw [← Nat.div_add_mod j 9, hj, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [← Nat.mod_mul_right_div_self, show (3 : ℕ) ^ 2 * 3 = 27 by norm_num, h27]
  norm_num

theorem main : H1 → H2 → OMA.R_OeisA259667_conjecture_2_R1.H2 := by
  intro h1 h2 j hj
  have hj0 : j ≠ 0 := by omega
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
  · rcases Nat.eq_zero_or_pos v with hv0 | hvpos
    · have hjw : j = w := by rw [hw, hv0, pow_zero, one_mul]
      rcases (show w % 9 = 1 ∨ w % 9 = 4 ∨ w % 9 = 7 by omega) with h | h | h
      · exact h1 j hj (Or.inl (by rw [hjw]; exact h))
      · exact h1 j hj (Or.inr (by rw [hjw]; exact h))
      · rw [hjw]
        exact regime_two_a w h
    · have h3j : 3 ∣ j := by
        rw [hw]
        exact Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) w
      rcases (show w % 9 = 1 ∨ w % 9 = 4 ∨ w % 9 = 7 by omega) with h | h | h
      · rw [hw]
        exact regime_two_b v w hvpos h
      · exact h2 j hj h3j (Or.inl (by rw [hdiv]; exact h))
      · exact h2 j hj h3j (Or.inr (by rw [hdiv]; exact h))
  · rw [hw]
    exact regime_one v w h2w

end OMA.R_OeisA259667_conjecture_2_R1_H2_R1
