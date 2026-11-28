import OMAReductions.R_Arxiv_2107_12475_CollatzLike_R1

-- Reduction Arxiv.2107.12475.CollatzLike.R1.H2.R1 of step Arxiv.2107.12475.CollatzLike.R1.H2
-- Credit: @rickmanelius

/-!
# Powers of two in base three: the two deep classes modulo `162`

The step asks for a ternary digit `2` in `2 ^ n` for `n > 8` in the sixteen classes modulo `162`
left open by the five lowest digits. All of them are even; write `n = 2 j` and `j = 3 ^ v * w`
with `3 ∤ w`.

Since `4 = 1 + 3`, induction on `v` gives `4 ^ (3 ^ v) = 1 + 3 ^ (v + 1) * u` with
`u ≡ 1 (mod 3)`, and `u ≡ 7 (mod 9)` once `v ≥ 1`. Hence
`2 ^ n = 4 ^ j ≡ 1 + 3 ^ (v + 1) * u * w (mod 3 ^ (2 v + 2))`: the digits at the positions
`1, …, v` vanish, the digit at position `v + 1` is `w mod 3`, and for `v ≥ 1` the digits at
positions `v + 1, v + 2` are those of `7 w mod 9`. This holds for every `v`, so it reaches digits
that no fixed window of low digits sees.

In the classes `n ≡ 0` and `n ≡ 54 (mod 162)` one has `27 ∣ j`, so `v ≥ 3` and the five lowest
digits read `1, 0, 0, 0, *`: the window says nothing about `w` beyond `w mod 3`. Proved below
with no hypothesis: `2 ^ n` has a digit `2` there whenever `w ≡ 2 (mod 3)` (position `v + 1`) or
`w ≡ 1 (mod 9)` (position `v + 2`). This settles two thirds of the class `0` (where `v ≥ 4`)
and one third of the class `54` (where `v = 3` and `w ≡ 1 (mod 3)`).

What is left:
* `H1`: the fourteen classes in which `v ≤ 2`, where the two digits above the valuation lie
  inside the five-digit window and give nothing new;
* `H2`: the classes `0` and `54` with `w ≡ 4` or `7 (mod 9)`.
-/

namespace OMA.R_Arxiv_2107_12475_CollatzLike_R1_H2_R1

/-- The fourteen open classes modulo `162` in which `v_3 (n / 2) ≤ 2`. -/
def H1 : Prop :=
  ∀ n : ℕ, 8 < n →
    n % 162 ∈ ({2, 8, 20, 24, 26, 56, 62, 72, 74, 78, 80, 96, 126, 150} : Finset ℕ) →
    2 ∈ Nat.digits 3 (2 ^ n)

/-- The deep classes `n ≡ 0, 54 (mod 162)` whose `3`-free part of `n / 2` is `≡ 4, 7 (mod 9)`. -/
def H2 : Prop :=
  ∀ n : ℕ, 8 < n → (n % 162 = 0 ∨ n % 162 = 54) →
    (n / 2 / 3 ^ padicValNat 3 (n / 2) % 9 = 4 ∨ n / 2 / 3 ^ padicValNat 3 (n / 2) % 9 = 7) →
    2 ∈ Nat.digits 3 (2 ^ n)

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

theorem main : H1 → H2 → OMA.R_Arxiv_2107_12475_CollatzLike_R1.H2 := by
  intro h1 h2 n hn hmem
  by_cases hshallow :
      n % 162 ∈ ({2, 8, 20, 24, 26, 56, 62, 72, 74, 78, 80, 96, 126, 150} : Finset ℕ)
  · exact h1 n hn hshallow
  have hdeep : n % 162 = 0 ∨ n % 162 = 54 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem hshallow
    omega
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j := ⟨n / 2, by omega⟩
  have hhalf : 2 * j / 2 = j := by omega
  have h27 : 27 ∣ j := by omega
  have hj0 : j ≠ 0 := by omega
  have hpow : 2 ^ (2 * j) = 4 ^ j := by rw [pow_mul]; norm_num
  rw [hpow]
  obtain ⟨v, hv⟩ : ∃ v, v = padicValNat 3 j := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : 3 ^ v ∣ j := hv ▸ pow_padicValNat_dvd
  have hw3 : ¬ 3 ∣ w := by
    rintro ⟨t, rfl⟩
    have hnd := pow_succ_padicValNat_not_dvd (p := 3) hj0
    rw [← hv] at hnd
    exact hnd ⟨t, by rw [hw, pow_succ]; ring⟩
  have hdiv : j / 3 ^ padicValNat 3 j = w := by
    rw [← hv, hw, Nat.mul_div_cancel_left _ (by positivity)]
  have hvpos : 1 ≤ v := by
    rcases Nat.eq_zero_or_pos v with h0 | h0
    · exfalso
      apply hw3
      rw [hw, h0, pow_zero, one_mul] at h27
      exact dvd_trans (by norm_num) h27
    · exact h0
  rcases (show w % 3 = 2 ∨ w % 9 = 1 ∨ w % 9 = 4 ∨ w % 9 = 7 by omega) with h | h | h | h
  · rw [hw]
    exact regime_one v w h
  · rw [hw]
    exact regime_two_b v w hvpos h
  · have := h2 (2 * j) hn hdeep (Or.inl (by rw [hhalf, hdiv]; exact h))
    rwa [hpow] at this
  · have := h2 (2 * j) hn hdeep (Or.inr (by rw [hhalf, hdiv]; exact h))
    rwa [hpow] at this

end OMA.R_Arxiv_2107_12475_CollatzLike_R1_H2_R1
