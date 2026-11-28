import FormalConjectures.Wikipedia.SmithNumber

open SmithNumber

abbrev S := digitSum 10

abbrev Q := primeFactorsDigitSum 10

alias R := Nat.pow_le_pow_right

alias W := Nat.pow_le_pow_left

alias V := Nat.perm_primeFactorsList_mul

lemma A (x : ℕ) : S x = S (x / 10) + x % 10 := by
  cases x <;> simp [digitSum, add_comm]

lemma C (d : ℕ) : ∀ n a c, a + c + 1 = 10 ^ n → S (10 ^ n * d + a) + S c = S d + 9 * n
  | 0, a, c, h => by simp_all [digitSum]
  | n + 1, a, c, h => by
    rw [pow_succ', mul_assoc, A (_ + a), A c, Nat.mul_add_div (by norm_num)] at *
    have := C d n (a / 10) (c / 10) (by omega)
    omega

lemma Z (x b : ℕ) : S (x * 10 ^ b) = S x := by
  induction b <;> simp_all [pow_succ, ← mul_assoc, A (_ * 10)]

lemma G (x : ℕ) (h : x.Prime ∨ 10 ≤ x) (hp : ∀ b, x + 1 ≠ 10 ^ b) :
    2 * 10 ^ S x ≤ x ^ 9 := by
  have t : 0 < 10 := by norm_num
  by_cases hx : x < 100
  · have := hp 2
    interval_cases x <;> norm_num [digitSum] at *
  rw [A x, pow_add]
  rcases em (∃ b, x / 10 + 1 = 10 ^ b) with ⟨b, hb⟩ | hq
  · have := pow_succ 10 b ▸ hp (b + 1)
    rw [show S (x / 10) = 9 * b by simpa [digitSum] using C 0 b 0 (x / 10) (by omega),
      pow_mul', ← hb]
    nlinarith [W (show 9 * (x / 10 + 1) ≤ x by omega) 9,
      R t (show x % 10 ≤ 8 by omega),
      (by positivity : 0 < (x / 10 + 1) ^ 9)]
  · linarith [Nat.mul_le_mul (G (x / 10) (.inr (by omega)) (not_exists.1 hq))
      (R t (show x % 10 ≤ 9 by omega)),
      W (show 10 * (x / 10) ≤ x by omega) 9]

lemma L : ∀ l : List ℕ, (∀ p ∈ l, p.Prime) →
    2 ^ l.length * 10 ^ (l.map S).sum ≤ l.prod ^ 9
  | [], _ => by simp
  | p :: l, h => by
    have hp := h p (.head _)
    have := Nat.mul_le_mul (G p (.inl hp) fun b e => by
      have : 10 ^ b % 9 = 1 := by simp [Nat.pow_mod]
      have := hp.eq_one_or_self_of_dvd 3 (by omega)
      omega) (L l fun q hq => h q (.tail _ hq))
    simp [pow_succ, pow_add]
    linarith

lemma O (j : ℕ) : j + 2 ≤ (10 ^ 2 ^ j - 1).primeFactorsList.length := by
  induction j with
  | zero => simp
  | succ j ih =>
    have := @Nat.one_lt_pow (2 ^ j) 10 (by positivity) (by norm_num)
    rw [pow_succ, pow_mul, sq, mul_self_tsub_one,
      (V (by omega) (by omega)).length_eq, List.length_append]
    have := List.length_pos_iff.2 ((Nat.primeFactorsList_ne_nil (10 ^ 2 ^ j + 1)).2 (by omega))
    omega

lemma M {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Q (a * b) = Q a + Q b := by
  simp [Q, primeFactorsDigitSum, ((V ha hb).map _).sum_eq]

lemma P {p x : ℕ} (hp : p.Prime) : Q (p ^ x) = x * S p := by
  simp [Q, primeFactorsDigitSum, hp.primeFactorsList_pow]

theorem OMA.solution : type_of% @SmithNumber.mcdaniel_infinitely_many_smith_numbers := by
  refine Set.infinite_of_forall_exists_gt fun k => ?_
  have hO := O (k + 65)
  have hk := @Nat.lt_two_pow_self (k + 65)
  generalize 2 ^ (k + 65) = n at hO hk
  have hn := @Nat.lt_pow_self n 10 (by norm_num)
  generalize hm : 10 ^ n - 1 = m at hO
  have hL := Nat.prod_primeFactorsList (show m ≠ 0 by omega) ▸
    L m.primeFactorsList fun p => Nat.prime_of_mem_primeFactorsList
  have h2 : m ^ 9 < 10 ^ (n * 9) := pow_mul 10 n 9 ▸ Nat.pow_lt_pow_left (by omega) (by norm_num)
  obtain ⟨D, hD⟩ := Nat.exists_eq_add_of_lt ((Nat.pow_lt_pow_iff_right (by norm_num)).1
    (((pow_add 10 20 (Q m)).trans_le ((Nat.mul_le_mul_right _
    ((show 10 ^ 20 ≤ 2 ^ 67 by norm_num).trans (R (by norm_num) (by omega)))).trans
    hL)).trans_lt h2))
  obtain ⟨i, b, hi, hib⟩ : ∃ i b, 2 ^ i ≤ 2 ^ 6 ∧ 2 * i + 7 * b = D + 21 :=
    ⟨D * 4 % 7, D / 7 + 3 - D % 7 % 2, R (by norm_num) (by omega), by omega⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_one.2 (Nat.two_pow_pos i)
  obtain ⟨a, rfl⟩ : ∃ a, m = a + c + 1 := ⟨m - c - 1, by omega⟩
  have := Nat.le_mul_of_pos_right (a + c + 1) (show 0 < 2 ^ i * (2 * 5) ^ b by positivity)
  refine ⟨(a + c + 1) * (2 ^ i * (2 * 5) ^ b), ⟨by norm_num, ⟨by omega,
    Nat.not_prime_mul (by omega) (by simp; omega)⟩, ?_⟩, by omega⟩
  have := (show 10 ^ n = a + c + 2 by omega) ▸ C c n (a + 1) c (by omega)
  show S _ = Q _
  rw [← mul_assoc, Z, M, M, P Nat.prime_two, mul_pow,
    M, P Nat.prime_two, P Nat.prime_five, hc] <;> try positivity
  ring_nf at *
  simp [digitSum] at *
  omega
