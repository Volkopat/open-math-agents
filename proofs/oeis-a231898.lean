import OMAStatements.S_oeis_a231898
import Mathlib

/-
Proof outline. Blocks: if `y < 2^k` and `x > 0` then the binary digits of `y + 2^k * x` are those of `y`, then
zeros up to `k` places, then those of `x`. Complement: `ones y + ones (2^a - 1 - y) = a` for `y < 2^a`, hence
`ones ((2^a - 1) * m) = a` for `1 ≤ m ≤ 2^a`. Family A: `(2^n - 1)^2` has `n` ones and `2n` digits. Family B:
`(M + 2^(2j+1))^2` has `1 + ones M + ones (M^2)` ones and `4j + 3` digits (an odd length) when `M < 2^j`. Every
`n ≥ 3` other than `4` is `1 + ones M + ones (M^2)` for some `M ≥ 1`. Multiplying `N` by `2^t` adds `2t` zeros, so the
two families give every large number of zeros of both parities.
-/

namespace OMA.A231898Proof

open OMA.S_oeis_a231898

theorem count01 : ∀ l : List ℕ, (∀ d ∈ l, d < 2) → l.count 1 + l.count 0 = l.length
  | [], _ => by simp
  | d :: l, h => by
    have hd : d < 2 := h d (by simp)
    have ih := count01 l (fun x hx => h x (by simp [hx]))
    rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl <;> simp <;> omega

theorem ones_add_zeros (x : ℕ) : ones x + zeros x = (Nat.digits 2 x).length :=
  count01 _ (fun _ hd => Nat.digits_lt_base (by norm_num) hd)

theorem ones_bit (r q : ℕ) (hr : r < 2) : ones (r + 2 * q) = r + ones q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · interval_cases r <;> simp [ones]
  · unfold ones
    rw [Nat.digits_add 2 (by norm_num) r q hr (Or.inr hq.ne')]
    interval_cases r <;> simp <;> omega

theorem ones_compl : ∀ a y : ℕ, y < 2 ^ a → ones y + ones (2 ^ a - 1 - y) = a
  | 0, y, h => by
    have hy : y = 0 := by rw [pow_zero] at h; omega
    subst hy
    simp [ones]
  | a + 1, y, h => by
    have hp : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
    have h2 : y / 2 < 2 ^ a := by omega
    have ih := ones_compl a (y / 2) h2
    have hy : ones y = y % 2 + ones (y / 2) := by
      have := ones_bit (y % 2) (y / 2) (Nat.mod_lt _ (by norm_num))
      rwa [Nat.mod_add_div] at this
    have e2 : 2 ^ (a + 1) - 1 - y = (1 - y % 2) + 2 * (2 ^ a - 1 - y / 2) := by omega
    rw [hy, e2, ones_bit (1 - y % 2) (2 ^ a - 1 - y / 2) (by omega)]
    omega

theorem blk2 {x y k : ℕ} (hx : 0 < x) (hy : y < 2 ^ k) :
    ones (y + 2 ^ k * x) = ones y + ones x ∧
      (Nat.digits 2 (y + 2 ^ k * x)).length = k + (Nat.digits 2 x).length := by
  have hl : (Nat.digits 2 y).length ≤ k :=
    (Nat.digits_length_le_iff (b := 2) (k := k) (by norm_num) y).2 hy
  have e : (Nat.digits 2 y).length + (k - (Nat.digits 2 y).length) = k := by omega
  have h := Nat.digits_append_zeroes_append_digits (b := 2) (k := k - (Nat.digits 2 y).length)
    (m := x) (n := y) (by norm_num) hx
  rw [e] at h
  unfold ones
  rw [← h]
  constructor
  · simp [List.count_append, List.count_replicate]
  · simp only [List.length_append, List.length_replicate]
    omega

theorem ones_mul (a m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ 2 ^ a) : ones ((2 ^ a - 1) * m) = a := by
  have h0 : ones 0 = 0 := by simp [ones]
  rcases Nat.eq_or_lt_of_le h1 with h | h
  · subst h
    have := ones_compl a 0 (by positivity)
    rw [h0, Nat.sub_zero, zero_add] at this
    rw [mul_one]
    exact this
  · have key : (2 ^ a - 1) * m = (2 ^ a - m) + 2 ^ a * (m - 1) := by
      generalize 2 ^ a = P at h2 ⊢
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j, P = j + k + 2 := ⟨P - k - 2, by omega⟩
      rw [show j + k + 2 - 1 = j + k + 1 by omega, show j + k + 2 - (k + 2) = j by omega,
        show k + 2 - 1 = k + 1 by omega]
      ring
    have hb := (blk2 (x := m - 1) (y := 2 ^ a - m) (k := a) (by omega) (by omega)).1
    rw [key, hb]
    have := ones_compl a (m - 1) (by omega)
    rw [show 2 ^ a - 1 - (m - 1) = 2 ^ a - m by omega] at this
    omega

theorem shift_sq {Z : ℕ} (hZ : 0 < Z) (t : ℕ) :
    ones ((2 ^ t * Z) ^ 2) = ones (Z ^ 2) ∧ zeros ((2 ^ t * Z) ^ 2) = 2 * t + zeros (Z ^ 2) := by
  have e : (2 ^ t * Z) ^ 2 = 2 ^ (2 * t) * Z ^ 2 := by ring
  have hZ2 : 0 < Z ^ 2 := by positivity
  rw [e]
  unfold ones zeros
  rw [Nat.digits_base_pow_mul (b := 2) (k := 2 * t) (by norm_num) hZ2]
  constructor
  · simp [List.count_append, List.count_replicate]
  · simp [List.count_append]

theorem len_eq {x j : ℕ} (h1 : 2 ^ j ≤ x) (h2 : x < 2 ^ (j + 1)) :
    (Nat.digits 2 x).length = j + 1 := by
  have a := (Nat.digits_length_le_iff (b := 2) (k := j + 1) (by norm_num) x).2 h2
  have b := (Nat.lt_digits_length_iff (b := 2) (k := j) (by norm_num) x).2 h1
  omega

theorem famA (n : ℕ) (hn : 2 ≤ n) : ones ((2 ^ n - 1) ^ 2) = n ∧ zeros ((2 ^ n - 1) ^ 2) = n := by
  have hpos : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have ho : ones ((2 ^ n - 1) ^ 2) = n := by
    rw [sq]
    exact ones_mul n (2 ^ n - 1) (by omega) (by omega)
  have hlen : (Nat.digits 2 ((2 ^ n - 1) ^ 2)).length = 2 * n := by
    obtain ⟨s, rfl⟩ : ∃ s, n = s + 2 := ⟨n - 2, by omega⟩
    have hs : 0 < 2 ^ s := by positivity
    obtain ⟨R, hR⟩ : ∃ R, 2 ^ s = R + 1 := ⟨2 ^ s - 1, by omega⟩
    have e1 : 2 ^ (s + 2) - 1 = 4 * R + 3 := by
      have : 2 ^ (s + 2) = 4 * 2 ^ s := by ring
      omega
    have e2 : 2 ^ (2 * s + 3) = 8 * (R + 1) ^ 2 := by rw [← hR]; ring
    have e3 : 2 ^ (2 * s + 3 + 1) = 16 * (R + 1) ^ 2 := by rw [← hR]; ring
    rw [e1, len_eq (x := (4 * R + 3) ^ 2) (j := 2 * s + 3) (by rw [e2]; nlinarith)
      (by rw [e3]; nlinarith)]
    omega
  refine ⟨ho, ?_⟩
  have := ones_add_zeros ((2 ^ n - 1) ^ 2)
  omega

theorem sqblock {A B c : ℕ} (hA : 0 < A) (h1 : B ^ 2 < 2 ^ (c + 2)) (h2 : A * B < 2 ^ c) :
    ones ((B + 2 ^ (c + 1) * A) ^ 2) = ones (B ^ 2) + ones (A * B) + ones (A ^ 2) ∧
      (Nat.digits 2 ((B + 2 ^ (c + 1) * A) ^ 2)).length =
        2 * c + 2 + (Nat.digits 2 (A ^ 2)).length := by
  have e : (B + 2 ^ (c + 1) * A) ^ 2 = B ^ 2 + 2 ^ (c + 2) * (A * B + 2 ^ c * A ^ 2) := by ring
  have hA2 : 0 < A ^ 2 := by positivity
  have hin : 0 < A * B + 2 ^ c * A ^ 2 := by positivity
  obtain ⟨o1, l1⟩ := blk2 hin h1
  obtain ⟨o2, l2⟩ := blk2 hA2 h2
  rw [e, o1, o2, l1, l2]
  exact ⟨by omega, by omega⟩

theorem famB {M j : ℕ} (_hM : 0 < M) (hj : M < 2 ^ j) :
    ones ((M + 2 ^ (2 * j + 1) * 1) ^ 2) = 1 + ones M + ones (M ^ 2) ∧
      (Nat.digits 2 ((M + 2 ^ (2 * j + 1) * 1) ^ 2)).length = 4 * j + 3 := by
  have hsq : M * M < 2 ^ j * 2 ^ j := Nat.mul_self_lt_mul_self hj
  have h1 : M ^ 2 < 2 ^ (2 * j + 2) := by
    have : 2 ^ (2 * j + 2) = 4 * (2 ^ j * 2 ^ j) := by ring
    rw [this, sq]
    omega
  have h2 : 1 * M < 2 ^ (2 * j) := by
    have : 2 ^ j ≤ 2 ^ (2 * j) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨o, l⟩ := sqblock (A := 1) (B := M) (c := 2 * j) (by norm_num) h1 h2
  have e1 : ones (1 * M) = ones M := by rw [one_mul]
  have e2 : ones (1 ^ 2) = 1 := by simp [ones]
  have e3 : (Nat.digits 2 (1 ^ 2)).length = 1 := by simp
  rw [o, l, e1, e2, e3]
  exact ⟨by omega, by omega⟩

theorem f_mersenne (a : ℕ) (ha : 1 ≤ a) : ones (2 ^ a - 1) = a ∧ ones ((2 ^ a - 1) ^ 2) = a := by
  have h2 : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  constructor
  · have := ones_mul a 1 le_rfl (by omega)
    rwa [mul_one] at this
  · rw [sq]
    exact ones_mul a (2 ^ a - 1) (by omega) (by omega)

theorem f_two_block (a b : ℕ) (hb : 1 ≤ b) (hba : b ≤ a) :
    0 < (2 ^ b - 1) + 2 ^ (2 * a + 1) * (2 ^ a - 1) ∧
      ones ((2 ^ b - 1) + 2 ^ (2 * a + 1) * (2 ^ a - 1)) +
        ones (((2 ^ b - 1) + 2 ^ (2 * a + 1) * (2 ^ a - 1)) ^ 2) = 3 * a + 2 * b := by
  have hb2 : 2 ≤ 2 ^ b := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hab : 2 ^ b ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hba
  have ha1 : 2 ^ a ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨oA, oA2⟩ := f_mersenne a (by omega)
  obtain ⟨oB, oB2⟩ := f_mersenne b hb
  have oAB : ones ((2 ^ a - 1) * (2 ^ b - 1)) = a := ones_mul a (2 ^ b - 1) (by omega) (by omega)
  have hM1 := (blk2 (x := 2 ^ a - 1) (y := 2 ^ b - 1) (k := 2 * a + 1) (by omega) (by omega)).1
  have hsq : (2 ^ a - 1) * (2 ^ b - 1) < 2 ^ a * 2 ^ a := by
    have u : 2 ^ a - 1 < 2 ^ a := by omega
    have v : 2 ^ b - 1 < 2 ^ a := by omega
    exact Nat.mul_lt_mul'' u v
  have hsq2 : (2 ^ b - 1) * (2 ^ b - 1) < 2 ^ a * 2 ^ a := by
    have v : 2 ^ b - 1 < 2 ^ a := by omega
    exact Nat.mul_lt_mul'' v v
  have h1 : (2 ^ b - 1) ^ 2 < 2 ^ (2 * a + 2) := by
    have : 2 ^ (2 * a + 2) = 4 * (2 ^ a * 2 ^ a) := by ring
    rw [this, sq]
    omega
  have h2 : (2 ^ a - 1) * (2 ^ b - 1) < 2 ^ (2 * a) := by
    have : 2 ^ (2 * a) = 2 ^ a * 2 ^ a := by ring
    rw [this]
    exact hsq
  have hM2 := (sqblock (A := 2 ^ a - 1) (B := 2 ^ b - 1) (c := 2 * a) (by omega) h1 h2).1
  refine ⟨by omega, ?_⟩
  omega

theorem exists_M (n : ℕ) (h3 : 3 ≤ n) (h4 : n ≠ 4) :
    ∃ M, 0 < M ∧ 1 + ones M + ones (M ^ 2) = n := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · by_cases h8 : n = 8
    · refine ⟨13, by norm_num, ?_⟩
      subst h8
      simp [ones]
    by_cases h10 : n = 10
    · refine ⟨21, by norm_num, ?_⟩
      subst h10
      simp [ones]
    obtain ⟨a, b, hb, hba, hv⟩ : ∃ a b, 1 ≤ b ∧ b ≤ a ∧ n = 1 + 3 * a + 2 * b := by
      rcases (by omega : (n - 1) % 6 = 5 ∨ (n - 1) % 6 = 1 ∨ (n - 1) % 6 = 3) with h' | h' | h'
      · exact ⟨(n - 3) / 3, 1, by omega, by omega, by omega⟩
      · exact ⟨(n - 5) / 3, 2, by omega, by omega, by omega⟩
      · exact ⟨(n - 7) / 3, 3, by omega, by omega, by omega⟩
    obtain ⟨hM, hf⟩ := f_two_block a b hb hba
    exact ⟨_, hM, by omega⟩
  · obtain ⟨o1, o2⟩ := f_mersenne (n / 2) (by omega)
    have : 2 ≤ 2 ^ (n / 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact ⟨2 ^ (n / 2) - 1, by omega, by omega⟩

theorem hasK_of {n X Y : ℕ} (hX : 0 < X) (hY : 0 < Y) (h1 : ones (X ^ 2) = n)
    (h2 : ones (Y ^ 2) = n) (hp : zeros (X ^ 2) % 2 ≠ zeros (Y ^ 2) % 2) : HasK n := by
  refine ⟨zeros (X ^ 2) + zeros (Y ^ 2), fun m hm => ?_⟩
  by_cases hm2 : m % 2 = zeros (X ^ 2) % 2
  · obtain ⟨h3, h4⟩ := shift_sq hX ((m - zeros (X ^ 2)) / 2)
    exact ⟨2 ^ ((m - zeros (X ^ 2)) / 2) * X, by rw [h3, h1], by rw [h4]; omega⟩
  · obtain ⟨h3, h4⟩ := shift_sq hY ((m - zeros (Y ^ 2)) / 2)
    exact ⟨2 ^ ((m - zeros (Y ^ 2)) / 2) * Y, by rw [h3, h2], by rw [h4]; omega⟩

theorem hasK_main (n : ℕ) (h1 : 1 ≤ n) (hn1 : n ≠ 1) (hn2 : n ≠ 2) (hn4 : n ≠ 4) : HasK n := by
  obtain ⟨M, hM, hf⟩ := exists_M n (by omega) hn4
  have hj : M < 2 ^ M := Nat.lt_two_pow_self
  obtain ⟨oB, lB⟩ := famB hM hj
  obtain ⟨oA, zA⟩ := famA n (by omega)
  have hzB := ones_add_zeros ((M + 2 ^ (2 * M + 1) * 1) ^ 2)
  have hpos : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact hasK_of (X := 2 ^ n - 1) (Y := M + 2 ^ (2 * M + 1) * 1) (by omega) (by positivity) oA
    (by omega) (by omega)

end OMA.A231898Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a231898.main := by
  intro n h1 hn1 hn2 hn4
  exact OMA.A231898Proof.hasK_main n h1 hn1 hn2 hn4
