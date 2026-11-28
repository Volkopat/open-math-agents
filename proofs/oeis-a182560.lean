import OMAStatements.S_oeis_a182560

open OMA.S_oeis_a182560

-- Each bit sees alternate blocks of zeros and ones of length L. During a
-- one block the output repeats 110 or 011, according to its incoming pair.
private def phaseBit (lengthMod phase offsetMod : ℕ) : Bool :=
  match phase with
  | 1 => decide (offsetMod ≠ 2)
  | 2 => decide (lengthMod = 2)
  | 3 => if lengthMod = 2 then decide (offsetMod ≠ 0) else decide (offsetMod ≠ 2)
  | _ => false

private def predicted (L n : ℕ) : Bool :=
  phaseBit (L % 3) (n / L % 4) (n % L % 3)

private theorem split_block {L q r : ℕ} (hL : 0 < L) (hr : r < L) :
    (r + L * q) / L = q ∧ (r + L * q) % L = r := by
  rw [Nat.add_mul_div_left r q hL, Nat.add_mul_mod_self_left, Nat.div_eq_of_lt hr,
    Nat.mod_eq_of_lt hr, zero_add]
  exact ⟨rfl, rfl⟩

private theorem predicted_step (L n : ℕ) (hL : 2 ≤ L) (hmod : L % 3 = 1 ∨ L % 3 = 2) :
    predicted L (n + 2) =
      ((predicted L (n + 1) && predicted L n) ^^ decide ((n + 2) / L % 2 = 1)) := by
  let q := n / L
  let r := n % L
  have hr : r < L := Nat.mod_lt _ (by omega)
  have hqr : r + L * q = n := Nat.mod_add_div n L
  have same (i : ℕ) (hi : r + i < L) :
      (n + i) / L = q ∧ (n + i) % L = r + i := by
    rw [show n + i = (r + i) + L * q by omega]
    exact split_block (by omega) hi
  have next (i j : ℕ) (he : r + i = L + j) (hj : j < L) :
      (n + i) / L = q + 1 ∧ (n + i) % L = j := by
    rw [show n + i = j + L * (q + 1) by rw [Nat.mul_succ]; omega]
    exact split_block (by omega) hj
  change phaseBit (L % 3) ((n + 2) / L % 4) ((n + 2) % L % 3) =
    ((phaseBit (L % 3) ((n + 1) / L % 4) ((n + 1) % L % 3) &&
      phaseBit (L % 3) (q % 4) (r % 3)) ^^ decide ((n + 2) / L % 2 = 1))
  by_cases h2 : r + 2 < L
  · obtain ⟨d₁, m₁⟩ := same 1 (by omega)
    obtain ⟨d₂, m₂⟩ := same 2 h2
    rw [d₁, d₂, m₁, m₂, show q % 2 = q % 4 % 2 by omega,
      show (r + 1) % 3 = (r % 3 + 1) % 3 by omega,
      show (r + 2) % 3 = (r % 3 + 2) % 3 by omega]
    set phase := q % 4
    set offset := r % 3
    have hp : phase < 4 := Nat.mod_lt _ (by decide)
    have ho : offset < 3 := Nat.mod_lt _ (by decide)
    rcases hmod with hm | hm <;> rw [hm] <;> interval_cases phase <;> interval_cases offset <;> decide
  · have phaseNext : (q + 1) % 4 = (q % 4 + 1) % 4 := by omega
    have bitNext : (q + 1) % 2 = ((q % 4 + 1) % 4) % 2 := by omega
    by_cases h1 : r + 1 < L
    · obtain ⟨d₁, m₁⟩ := same 1 h1
      obtain ⟨d₂, m₂⟩ := next 2 0 (by omega) (by omega)
      rw [d₁, d₂, m₁, m₂, phaseNext, bitNext,
        show r % 3 = (L % 3 + 1) % 3 by omega,
        show (r + 1) % 3 = (L % 3 + 2) % 3 by omega]
      set phase := q % 4
      have hp : phase < 4 := Nat.mod_lt _ (by decide)
      rcases hmod with hm | hm <;> rw [hm] <;> interval_cases phase <;> decide
    · obtain ⟨d₁, m₁⟩ := next 1 0 (by omega) (by omega)
      obtain ⟨d₂, m₂⟩ := next 2 1 (by omega) (by omega)
      rw [d₁, d₂, m₁, m₂, phaseNext, bitNext, show r % 3 = (L % 3 + 2) % 3 by omega]
      set phase := q % 4
      have hp : phase < 4 := Nat.mod_lt _ (by decide)
      rcases hmod with hm | hm <;> rw [hm] <;> interval_cases phase <;> decide

private theorem pow_two_mod_three (j : ℕ) :
    (2 : ℕ) ^ j % 3 = if j % 2 = 0 then 1 else 2 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    have hj : j % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases h : j % 2 <;>
      simp [h, show (j + 1) % 2 = (j % 2 + 1) % 2 by omega]

private theorem low_bit (n : ℕ) : (a n).testBit 0 = n.testBit 0 := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n h₀ h₁ =>
    rw [a, Nat.testBit_xor, Nat.testBit_and, h₀, h₁]
    have hz : ((n + 1).testBit 0 && n.testBit 0) = false := by
      simp only [Nat.testBit_zero]
      rw [show (n + 1) % 2 = (n % 2 + 1) % 2 by omega]
      have hn : n % 2 < 2 := Nat.mod_lt _ (by decide)
      interval_cases h : n % 2 <;> decide
    rw [hz]
    simp

private theorem high_bit (j n : ℕ) (hj : 0 < j) :
    (a n).testBit j = predicted (2 ^ j) n := by
  have hlen : 2 ≤ (2 : ℕ) ^ j := Nat.pow_le_pow_right Nat.zero_lt_two hj
  have hm : (2 : ℕ) ^ j % 3 = 1 ∨ (2 : ℕ) ^ j % 3 = 2 := by
    rw [pow_two_mod_three]
    split <;> decide
  induction n using Nat.twoStepInduction with
  | zero => simp [a, predicted, phaseBit]
  | one =>
    simp [a, Nat.testBit_eq_decide_div_mod_eq, predicted, phaseBit,
      Nat.div_eq_of_lt (show 1 < (2 : ℕ) ^ j by omega)]
  | more n h₀ h₁ =>
    simp only [a, Nat.testBit_xor, Nat.testBit_and, h₀, h₁]
    rw [Nat.testBit_eq_decide_div_mod_eq, predicted_step _ n hlen hm]

private def witness (k : ℕ) : ℕ := 3 * 2 ^ (2 * k + 1)

private theorem witness_bit (k j : ℕ) :
    predicted (2 ^ j) (witness k) = false := by
  have hpos : 0 < (2 : ℕ) ^ j := Nat.two_pow_pos _
  by_cases hle : j ≤ 2 * k + 1
  · let d := 2 * k + 1 - j
    have hexp : j + d = 2 * k + 1 := by dsimp [d]; omega
    have hfactor : witness k = 0 + 2 ^ j * (3 * 2 ^ d) := by
      rw [witness, ← hexp, pow_add]
      ring
    obtain ⟨hdiv, hrem⟩ := split_block (q := 3 * 2 ^ d) hpos hpos
    rw [← hfactor] at hdiv hrem
    unfold predicted
    rw [hdiv, hrem]
    by_cases hsmall : d < 2
    · interval_cases d
      · have hodd : j % 2 ≠ 0 := by omega
        norm_num [phaseBit, pow_two_mod_three, hodd]
      · have heven : j % 2 = 0 := by omega
        norm_num [phaseBit, pow_two_mod_three, heven]
    · have hd : 4 ∣ (2 : ℕ) ^ d := by
        have he : d = (d - 2) + 2 := by omega
        rw [he, pow_add]
        exact dvd_mul_left 4 _
      have hzero : (3 * 2 ^ d) % 4 = 0 :=
        Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hd 3)
      simp [hzero, phaseBit]
  · by_cases heq : j = 2 * k + 2
    · let t := (2 : ℕ) ^ (2 * k + 1)
      have ht : 0 < t := Nat.two_pow_pos _
      have hlen : (2 : ℕ) ^ j = 2 * t := by rw [heq, pow_succ]; exact Nat.mul_comm _ _
      have hfac : witness k = t + 2 ^ j * 1 := by rw [hlen, witness]; change 3 * t = _; omega
      obtain ⟨hdiv, hrem⟩ := split_block (q := 1) hpos (show t < 2 ^ j by omega)
      rw [← hfac] at hdiv hrem
      have htmod : t % 3 = 2 := by
        simp [t, pow_two_mod_three]
      simp [predicted, phaseBit, hdiv, hrem, htmod]
    · have hlt : witness k < (2 : ℕ) ^ (2 * k + 3) := by
        rw [witness, show 2 * k + 3 = (2 * k + 1) + 2 by omega, pow_add (2 : ℕ) (2 * k + 1) 2]
        have ht : 0 < (2 : ℕ) ^ (2 * k + 1) := Nat.two_pow_pos _
        norm_num
        omega
      have hbound := hlt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (show 2 * k + 3 ≤ j by omega))
      simp [predicted, phaseBit, Nat.div_eq_of_lt hbound]

private theorem witness_zero (k : ℕ) : a (witness k) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  cases j with
  | zero =>
    rw [low_bit, Nat.testBit_zero, Nat.testBit_zero]
    have h : witness k % 2 = 0 := by rw [witness, pow_succ]; omega
    simp [h]
  | succ j =>
    rw [high_bit _ _ (by omega), witness_bit _ _]
    simp

theorem OMA.solution : type_of% @OMA.S_oeis_a182560.main := by
  have hinj : Function.Injective witness := by
    apply StrictMono.injective
    intro a b hab
    unfold witness
    exact Nat.mul_lt_mul_of_pos_left
      (Nat.pow_lt_pow_right (by decide) (by omega)) (by decide)
  apply (Set.infinite_range_of_injective hinj).mono
  rintro n ⟨k, rfl⟩
  exact witness_zero k
