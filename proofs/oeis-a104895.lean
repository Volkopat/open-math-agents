import OMAStatements.S_oeis_a104895

namespace P104895
open OMA.S_oeis_a104895

lemma xx (x y : ℕ) (i j : Bool) :
    (2 * x + i.toNat) ^^^ (2 * y + j.toNat) = 2 * (x ^^^ y) + (bne i j).toNat := by
  rw [← Nat.bit_val, ← Nat.bit_val, ← Nat.bit_val, Nat.xor_bit]

lemma x00 (x y : ℕ) : (2 * x) ^^^ (2 * y) = 2 * (x ^^^ y) := by
  simpa using xx x y false false
lemma x10 (x y : ℕ) : (2 * x + 1) ^^^ (2 * y) = 2 * (x ^^^ y) + 1 := by
  simpa using xx x y true false
lemma x01 (x y : ℕ) : (2 * x) ^^^ (2 * y + 1) = 2 * (x ^^^ y) + 1 := by
  simpa using xx x y false true
lemma x11 (x y : ℕ) : (2 * x + 1) ^^^ (2 * y + 1) = 2 * (x ^^^ y) := by
  simpa using xx x y true true

lemma a_succ (n : ℕ) (hn : n ≠ 0) : a n = if a (n - 2 ^ Nat.log 2 n) < 0 then
    a (n - 2 ^ Nat.log 2 n) + 2 ^ Nat.log 2 n else a (n - 2 ^ Nat.log 2 n) - 2 ^ Nat.log 2 n := by
  rw [a, dif_neg hn]

lemma a_zero : a 0 = 0 := by rw [a]; simp

lemma a_one : a 1 = -1 := by rw [a_succ 1 one_ne_zero]; simp [a_zero]

lemma a_rec (n : ℕ) : a (2 * n) = 2 * a n ∧ a (2 * n + 1) = -2 * a n - 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a_zero, a_one]
  have hpow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn.ne'
  have h1 : Nat.log 2 (2 * n) = Nat.log 2 n + 1 := by
    rw [Nat.log_of_one_lt_of_le (by norm_num) (by omega)]; congr 2; omega
  have h2 : Nat.log 2 (2 * n + 1) = Nat.log 2 n + 1 := by
    rw [Nat.log_of_one_lt_of_le (by norm_num) (by omega)]; congr 2; omega
  have hm : n - 2 ^ Nat.log 2 n < n := Nat.sub_lt hn (Nat.two_pow_pos _)
  obtain ⟨e1, e2⟩ := ih _ hm
  have k1 : 2 * n - 2 ^ (Nat.log 2 n + 1) = 2 * (n - 2 ^ Nat.log 2 n) := by rw [pow_succ]; omega
  have k2 : 2 * n + 1 - 2 ^ (Nat.log 2 n + 1) = 2 * (n - 2 ^ Nat.log 2 n) + 1 := by
    rw [pow_succ]; omega
  rw [a_succ n hn.ne', a_succ (2 * n) (by omega), a_succ (2 * n + 1) (by omega), h1, h2, k1, k2,
    e1, e2]
  generalize a (n - 2 ^ Nat.log 2 n) = A
  simp only [pow_succ]
  generalize (2 : ℤ) ^ Nat.log 2 n = P
  constructor <;> split_ifs <;> omega

lemma a_inj : ∀ s x y, x + y ≤ s → a x = a y → x = y := by
  intro s
  induction s with
  | zero => intro x y h _; omega
  | succ s ih =>
    intro x y hs hxy
    obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' x <;> obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' y
    · rw [(a_rec n).1, (a_rec m).1] at hxy
      have := ih n m (by omega) (by omega)
      omega
    · rw [(a_rec n).1, (a_rec m).2] at hxy; omega
    · rw [(a_rec n).2, (a_rec m).1] at hxy; omega
    · rw [(a_rec n).2, (a_rec m).2] at hxy
      have := ih n m (by omega) (by omega)
      omega

lemma b_even (k : ℕ) : b (2 * k) = 2 * b k := x00 k (2 * k)

lemma c_odd (k : ℕ) : c (2 * k + 1) = 2 * b k + 1 := by
  have hv : padicValNat 2 (2 * k + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  simp only [c, b, hv, pow_zero, Nat.add_sub_cancel]
  exact x10 k (2 * k)

lemma c_even (k : ℕ) (hk : 1 ≤ k) : c (2 * k) = 2 * c k := by
  have hv : padicValNat 2 (2 * k) = padicValNat 2 k + 1 := by
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]; ring
  have hle : 2 ^ padicValNat 2 k ≤ k := Nat.le_of_dvd hk pow_padicValNat_dvd
  simp only [c, hv]
  rw [show 2 * k - 2 ^ (padicValNat 2 k + 1) = 2 * (k - 2 ^ padicValNat 2 k) by
    rw [pow_succ]; omega]
  exact x00 k _

lemma f_eq (k : ℕ) : k ^^^ (2 * k + 1) = c (k + 1) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [x01, c_odd]; rfl
  · rw [x11, ih j (by omega), show 2 * j + 1 + 1 = 2 * (j + 1) by ring, c_even _ (by omega)]

lemma b_odd (k : ℕ) : b (2 * k + 1) = 2 * c (k + 1) + 1 := by
  simp only [b]
  rw [x10, f_eq]

lemma c_one : c 1 = 1 := by simp [c]

lemma ab (k : ℕ) : a (b k) = k ∧ (1 ≤ k → a (c k) = -k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [b, a_zero]
    obtain ⟨i1, i2⟩ := ih j (by omega)
    refine ⟨?_, fun _ => ?_⟩
    · rw [b_even, (a_rec _).1, i1]; push_cast; ring
    · rw [c_even _ hj, (a_rec _).1, i2 hj]; push_cast; ring
  · obtain ⟨i1, i2⟩ := ih j (by omega)
    refine ⟨?_, fun _ => ?_⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [b_odd, c_one, (a_rec _).2, a_one]; norm_num
      rw [b_odd, (a_rec _).2, ((ih (j + 1) (by omega)).2 (by omega))]; push_cast; ring
    · rw [c_odd, (a_rec _).2, i1]; push_cast; ring

end P104895

theorem OMA.solution : type_of% @OMA.S_oeis_a104895.main := by
  refine ⟨fun n k => ⟨fun h => P104895.a_inj _ n _ le_rfl (by rw [h, (P104895.ab k).1]),
    fun h => by rw [h, (P104895.ab k).1]⟩, fun n k hk => ⟨fun h => P104895.a_inj _ n _ le_rfl
    (by rw [h, (P104895.ab k).2 hk]), fun h => by rw [h, (P104895.ab k).2 hk]⟩⟩
