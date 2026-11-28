import FormalConjectures.OEIS.«259667»

/-!
# A259667, residue one: reduction to a ternary digit problem for 2·4^m - 1

Lucas' theorem gives the central binomial coefficient modulo 3 from the ternary digits
of `n`: it is 0 if some digit is 2, and otherwise 1 or 2 according to the parity of `n`.
For `n = 2^k - 1` this gives the Catalan number modulo 3. Residue one modulo 6 forces
`k = 0`, or `k` odd with no ternary digit 2 in `2^k - 1`. So the conjecture follows once
`2·4^m - 1` has a ternary digit 2 for every `m ≥ 3`. This is the odd-exponent companion of
the Erdős ternary digit problem (erdosproblems.com/406), which concerns even exponents.
`H1` is a finite range and `H2` is the open tail. The digit of `n` at position `j` is
written `n / 3 ^ j % 3`.
-/

namespace OMA.R_OeisA259667_conjecture_1_R2

/-- A finite range of the digit statement. -/
def H1 : Prop := ∀ m : ℕ, 3 ≤ m → m ≤ 6561 → ∃ j : ℕ, (2 * 4 ^ m - 1) / 3 ^ j % 3 = 2

/-- The open tail: `2·4^m - 1` has a ternary digit 2. -/
def H2 : Prop := ∀ m : ℕ, 6561 < m → ∃ j : ℕ, (2 * 4 ^ m - 1) / 3 ^ j % 3 = 2

theorem lucas3 (n : ℕ) : n.centralBinom % 3 =
    ((2 * n) % 3).choose (n % 3) * (n / 3).centralBinom % 3 ∨
    (n % 3 = 2 ∧ n.centralBinom % 3 = 0) := by
  have _i : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : (2 * n).choose n % 3 = ((2 * n) % 3).choose (n % 3) * ((2 * n) / 3).choose (n / 3) % 3 :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with r | r | r
  · left
    rw [Nat.centralBinom, h, show 2 * n / 3 = 2 * (n / 3) by omega, Nat.centralBinom]
  · left
    rw [Nat.centralBinom, h, show 2 * n / 3 = 2 * (n / 3) by omega, Nat.centralBinom]
  · right
    refine ⟨r, ?_⟩
    rw [Nat.centralBinom, h, r, show 2 * n % 3 = 1 by omega]
    simp

theorem digit_shift (n j : ℕ) : n / 3 / 3 ^ j % 3 = n / 3 ^ (j + 1) % 3 := by
  rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]

theorem cb_zero : ∀ n : ℕ, (∃ j : ℕ, n / 3 ^ j % 3 = 2) → n.centralBinom % 3 = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rintro ⟨j, hj⟩
    rcases lucas3 n with h | ⟨-, h⟩
    · rcases j with _ | j
      · rw [pow_zero, Nat.div_one] at hj
        rw [h, hj, show 2 * n % 3 = 1 by omega]
        simp
      · have hn : 0 < n := by
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · simp at hj
          · exact hn
        have := ih (n / 3) (Nat.div_lt_self hn (by norm_num)) ⟨j, by rw [digit_shift]; exact hj⟩
        rw [h, Nat.mul_mod, this]
        simp
    · exact h

theorem cb_sign : ∀ n : ℕ, (∀ j : ℕ, n / 3 ^ j % 3 ≠ 2) →
    n.centralBinom % 3 = if n % 2 = 0 then 1 else 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hd
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · decide
    have h0 := hd 0
    rw [pow_zero, Nat.div_one] at h0
    have hq := ih (n / 3) (Nat.div_lt_self hn (by norm_num))
      (fun j => by rw [digit_shift]; exact hd (j + 1))
    rcases lucas3 n with h | ⟨h, -⟩
    · rcases (show n % 3 = 0 ∨ n % 3 = 1 by omega) with r | r
      · rw [h, r, show 2 * n % 3 = 0 by omega, Nat.choose_zero_right, one_mul, hq,
          show n % 2 = n / 3 % 2 by omega]
      · rw [h, r, show 2 * n % 3 = 2 by omega, Nat.mul_mod, hq]
        by_cases e : n / 3 % 2 = 0
        · rw [if_pos e, if_neg (by omega)]
          decide
        · rw [if_neg e, if_pos (by omega)]
          decide
    · exact absurd h h0

theorem catalan31 : _root_.catalan 31 % 6 = 1 := by
  rw [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose,
    Nat.choose_eq_factorial_div_factorial (by norm_num)]
  decide +kernel

theorem main : H1 → H2 → type_of% @OeisA259667.conjecture_1 := by
  intro h1 h2 k
  unfold OeisA259667.a
  constructor
  · intro ha
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact Or.inl rfl
    have hC3 : _root_.catalan (2 ^ k - 1) % 3 = 1 := by omega
    have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hmul : 2 ^ k * _root_.catalan (2 ^ k - 1) = (2 ^ k - 1).centralBinom := by
      have := Nat.mul_div_cancel' (Nat.succ_dvd_centralBinom (2 ^ k - 1))
      rwa [← catalan_eq_centralBinom_div, Nat.sub_add_cancel hpow] at this
    have hodd : (2 ^ k - 1) % 2 = 1 := by
      obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
      rw [pow_succ]
      omega
    have hnd : ∀ j : ℕ, (2 ^ k - 1) / 3 ^ j % 3 ≠ 2 := by
      intro j hj
      have hz := cb_zero _ ⟨j, hj⟩
      rw [← hmul, Nat.mul_mod, hC3] at hz
      have h2k : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
        have : ¬ 3 ∣ 2 ^ k := fun h => by
          have := Nat.prime_three.dvd_of_dvd_pow h
          omega
        omega
      rcases h2k with e | e <;> rw [e] at hz <;> omega
    have hs := cb_sign _ hnd
    rw [if_neg (by omega), ← hmul, Nat.mul_mod, hC3] at hs
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · exfalso
      have : 2 ^ (2 * m) % 3 = 1 := by
        rw [pow_mul, Nat.pow_mod]
        norm_num
      rw [this] at hs
      omega
    · have hform : 2 ^ (2 * m + 1) - 1 = 2 * 4 ^ m - 1 := by
        rw [pow_succ, pow_mul, mul_comm]
        norm_num
      rw [hform] at hnd
      rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ 3 ≤ m by omega) with rfl | rfl | rfl | h3
      · exact Or.inr (Or.inl rfl)
      · exact absurd (by norm_num) (hnd 1)
      · exact Or.inr (Or.inr rfl)
      · exfalso
        rcases Nat.lt_or_ge 6561 m with hm | hm
        · obtain ⟨j, hj⟩ := h2 m hm
          exact hnd j hj
        · obtain ⟨j, hj⟩ := h1 m h3 hm
          exact hnd j hj
  · rintro (rfl | rfl | rfl)
    · norm_num
    · norm_num
    · rw [show 2 ^ 5 - 1 = 31 by norm_num]
      exact catalan31

end OMA.R_OeisA259667_conjecture_1_R2
