import OMAStatements.S_oeis_a064708

-- Reduction oeis-a064708.R1 of A064708: Initial term of run of (at least) n consecutive numbers with just 2 distinct prime factors.
-- Credit: @EmadY
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Idea. In a run of nine consecutive numbers with exactly two distinct prime factors, every multiple
-- of 6 is a 3-smooth number N = 2^a 3^b. Proved here:
-- * two multiples of 6 in the run (Catalan for powers of 2 and 3): the run starts below 49;
-- * N in the middle (window N-4..N+4): 5 divides one of N+4, N-2, N+2, N-4;
-- * N at offset 3 (window N-3..N+5), completely: for each class of (a mod 12, b mod 12) one of
--   5, 7, 13 divides a term whose cofactor must be a prime power, or two of them divide a term with
--   exactly two prime factors, or an algebraic factorization applies (N a square, a cube, or a
--   sixth power); the a = 1 family needs the prime 11 and b mod 60. Every resulting exponential
--   equation is solved by congruence certificates (lemmas cert_add and cert_eq, checked by decide),
--   and the finitely many small N are checked directly;
-- * N at offset 5 (window N-5..N+3), the same way, for every class except two.
-- Left open (the steps): the offset-5 window when a = b = 1 (mod 12) (H1) or a = b = 7 (mod 12)
-- (H2). These classes contain the virtual solution N = 6 (u = N/12 = 1/2, where every constrained
-- term is a unit or a power of 2 or 3), so no congruence covering can reach them.

namespace OMA.R_oeis_a064708_R1


/-- Open step: the offset-5 window with `a ≡ b ≡ 1 (mod 12)`. -/
def H1 : Prop := ∀ a b : ℕ, a % 12 = 1 → b % 12 = 1 →
  ¬ ∀ i < 9, (2 ^ a * 3 ^ b - 5 + i).primeFactors.card = 2

/-- Open step: the offset-5 window with `a ≡ b ≡ 7 (mod 12)`. -/
def H2 : Prop := ∀ a b : ℕ, a % 12 = 7 → b % 12 = 7 →
  ¬ ∀ i < 9, (2 ^ a * 3 ^ b - 5 + i).primeFactors.card = 2

lemma smooth_of_six_dvd {n : ℕ} (h6 : 6 ∣ n) (hc : n.primeFactors.card = 2) :
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ n = 2 ^ a * 3 ^ b := by
  have hn : n ≠ 0 := by rintro rfl; simp at hc
  have d2 : 2 ∣ n := dvd_trans (by norm_num) h6
  have d3 : 3 ∣ n := dvd_trans (by norm_num) h6
  have h2 : 2 ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨Nat.prime_two, d2, hn⟩
  have h3 : 3 ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨Nat.prime_three, d3, hn⟩
  have hpf : n.primeFactors = {2, 3} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · rw [hc]; rfl
  refine ⟨n.factorization 2, n.factorization 3,
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hn).1 d2,
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three hn).1 d3, ?_⟩
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization, hpf]
  simp

lemma three_pow_mod_eight (t : ℕ) : 3 ^ t % 8 = 1 ∨ 3 ^ t % 8 = 3 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

/-- `3^t + 1` is a power of two only for `t ≤ 1`. -/
lemma catalan_a {s t : ℕ} (h : 3 ^ t + 1 = 2 ^ s) : t ≤ 1 := by
  by_contra ht
  push Not at ht
  have h9 : 9 ≤ 3 ^ t := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) ht
  have hs : 3 ≤ s := by
    by_contra hs
    push Not at hs
    have : 2 ^ s ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h8 : 8 ∣ 2 ^ s := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
    exact ⟨2 ^ k, by rw [pow_add]; norm_num⟩
  have hm := three_pow_mod_eight t
  generalize 3 ^ t = x at *
  generalize 2 ^ s = y at *
  omega

lemma two_pow_mod_period (s M : ℕ) (hM : 2 ^ 18 % M = 1) : 2 ^ s % M = 2 ^ (s % 18) % M := by
  conv_lhs => rw [← Nat.div_add_mod s 18, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod (2 ^ 18), hM, one_pow]
  have hM2 : M ≠ 1 := by rintro rfl; norm_num at hM
  rw [Nat.one_mod_eq_one.mpr hM2, one_mul, Nat.mod_mod]

/-- `2^s + 1` is a power of three only for `t ≤ 2`. -/
lemma catalan_b {s t : ℕ} (h : 2 ^ s + 1 = 3 ^ t) : t ≤ 2 := by
  by_contra ht
  push Not at ht
  have h27 : 27 ∣ 2 ^ s + 1 := by
    rw [h]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    exact ⟨3 ^ k, by rw [pow_add]; norm_num⟩
  have p27 := two_pow_mod_period s 27 (by norm_num)
  have p19 := two_pow_mod_period s 19 (by norm_num)
  have hr : s % 18 < 18 := Nat.mod_lt _ (by norm_num)
  have h19 : 19 ∣ 2 ^ s + 1 := by
    generalize hr' : s % 18 = r at p27 p19 hr
    interval_cases r <;> norm_num at p27 p19 <;> omega
  rw [h] at h19
  have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 19) h19)
  norm_num at this

/-- Two `3`-smooth multiples of `6` that are `6` apart are small. -/
lemma small_of_two_mult {a b c d : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h : 2 ^ a * 3 ^ b + 6 = 2 ^ c * 3 ^ d) : 2 ^ a * 3 ^ b ≤ 48 := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' ha
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' hb
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hd
  have e : 2 ^ a * 3 ^ b + 1 = 2 ^ c * 3 ^ d := by
    have : 6 * (2 ^ a * 3 ^ b + 1) = 6 * (2 ^ c * 3 ^ d) := by
      rw [pow_succ, pow_succ, pow_succ, pow_succ] at h; linarith
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  rw [pow_succ, pow_succ]
  -- parity and divisibility by 3 force a = 0 or c = 0, and b = 0 or d = 0
  have hac : a = 0 ∨ c = 0 := by
    by_contra hh
    push Not at hh
    have h1 : 2 ∣ 2 ^ a * 3 ^ b := Dvd.dvd.mul_right (dvd_pow_self 2 hh.1) _
    have h2 : 2 ∣ 2 ^ c * 3 ^ d := Dvd.dvd.mul_right (dvd_pow_self 2 hh.2) _
    omega
  have hbd : b = 0 ∨ d = 0 := by
    by_contra hh
    push Not at hh
    have h1 : 3 ∣ 2 ^ a * 3 ^ b := Dvd.dvd.mul_left (dvd_pow_self 3 hh.1) _
    have h2 : 3 ∣ 2 ^ c * 3 ^ d := Dvd.dvd.mul_left (dvd_pow_self 3 hh.2) _
    omega
  rcases hac with rfl | rfl <;> rcases hbd with rfl | rfl
  · simp
  · simp at e
    have := catalan_a e
    interval_cases b <;> simp
  · simp at e
    have := catalan_b e
    have : 2 ^ a ≤ 8 := by
      have : 3 ^ d ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
      omega
    simp; omega
  · simp at e

lemma card_ne_two_of_prime {p : ℕ} (hp : p.Prime) : p.primeFactors.card ≠ 2 := by
  rw [hp.primeFactors]; simp

lemma not_prime_of_card_two {n : ℕ} (h : n.primeFactors.card = 2) : ¬ n.Prime :=
  fun hp => card_ne_two_of_prime hp h

/-- Every run of nine consecutive numbers starting at most at `48` contains `0`, `1` or a prime. -/
lemma small_window (m : ℕ) (hm : m ≤ 48) : ¬ ∀ i < 9, (m + i).primeFactors.card = 2 := by
  intro h
  interval_cases m <;>
  first
  | (have h0 := h 0 (by norm_num); simp at h0; done)
  | (have hp := not_prime_of_card_two (h 0 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (h 1 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (h 2 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (h 3 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (h 4 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (h 5 (by norm_num)); norm_num at hp; done)

lemma pow_mod_period (x P M n : ℕ) (h : x ^ P % M = 1) : x ^ n % M = x ^ (n % P) % M := by
  conv_lhs => rw [← Nat.div_add_mod n P, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod (x ^ P), h, one_pow]
  have hM : M ≠ 1 := by intro hM1; rw [hM1, Nat.mod_one] at h; exact zero_ne_one h
  rw [Nat.one_mod_eq_one.mpr hM, one_mul, Nat.mod_mod]

lemma not_dvd_23 {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) (h3 : q ≠ 3) (x y : ℕ) :
    ¬ q ∣ 2 ^ x * 3 ^ y := by
  intro h
  rcases (Nat.Prime.dvd_mul hq).1 h with h | h
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
  · exact h3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h))

lemma not_dvd_25 {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) (h5 : q ≠ 5) (x y : ℕ) :
    ¬ q ∣ 2 ^ x * 5 ^ y := by
  intro h
  rcases (Nat.Prime.dvd_mul hq).1 h with h | h
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
  · exact h5 ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 (hq.dvd_of_dvd_pow h))

lemma five_pow_mod_four (e : ℕ) : 5 ^ e % 4 = 1 := by
  rw [Nat.pow_mod]; norm_num

/-- `2^x 3^y + 1 = 5^e` forces `x ≤ 3` and `y ≤ 1`. -/
lemma eqA {x y e : ℕ} (h : 2 ^ x * 3 ^ y + 1 = 5 ^ e) : x ≤ 3 ∧ y ≤ 1 := by
  constructor
  · by_contra hx
    have h16 : 16 ∣ 2 ^ x * 3 ^ y := by
      have := pow_dvd_pow 2 (by omega : 4 ≤ x)
      exact Dvd.dvd.mul_right (by simpa using this) _
    have m16 : 5 ^ e % 16 = 1 := by omega
    rw [pow_mod_period 5 4 16 e (by norm_num)] at m16
    have he : e % 4 = 0 := by
      have : e % 4 < 4 := Nat.mod_lt _ (by norm_num)
      interval_cases (e % 4) <;> simp_all
    have m13 : 5 ^ e % 13 = 1 := by rw [pow_mod_period 5 4 13 e (by norm_num), he]; norm_num
    exact not_dvd_23 (q := 13) (by norm_num) (by norm_num) (by norm_num) x y (by omega)
  · by_contra hy
    have h9 : 9 ∣ 2 ^ x * 3 ^ y := by
      have := pow_dvd_pow 3 (by omega : 2 ≤ y)
      exact Dvd.dvd.mul_left (by simpa using this) _
    have m9 : 5 ^ e % 9 = 1 := by omega
    rw [pow_mod_period 5 6 9 e (by norm_num)] at m9
    have he : e % 6 = 0 := by
      have : e % 6 < 6 := Nat.mod_lt _ (by norm_num)
      interval_cases (e % 6) <;> simp_all
    have m7 : 5 ^ e % 7 = 1 := by rw [pow_mod_period 5 6 7 e (by norm_num), he]; norm_num
    exact not_dvd_23 (q := 7) (by norm_num) (by norm_num) (by norm_num) x y (by omega)

/-- `5^e + 1 = 2^x 3^y` forces `x ≤ 1` and `y ≤ 1`. -/
lemma eqB {x y e : ℕ} (h : 5 ^ e + 1 = 2 ^ x * 3 ^ y) : x ≤ 1 ∧ y ≤ 1 := by
  have m4 := five_pow_mod_four e
  constructor
  · by_contra hx
    have : 4 ∣ 2 ^ x * 3 ^ y := by
      have := pow_dvd_pow 2 (by omega : 2 ≤ x)
      exact Dvd.dvd.mul_right (by simpa using this) _
    omega
  · by_contra hy
    have h9 : 9 ∣ 2 ^ x * 3 ^ y := by
      have := pow_dvd_pow 3 (by omega : 2 ≤ y)
      exact Dvd.dvd.mul_left (by simpa using this) _
    have m9 : 5 ^ e % 9 = 8 := by omega
    rw [pow_mod_period 5 6 9 e (by norm_num)] at m9
    have he : e % 6 = 3 := by
      have : e % 6 < 6 := Nat.mod_lt _ (by norm_num)
      interval_cases (e % 6) <;> simp_all
    have m7 : 5 ^ e % 7 = 6 := by rw [pow_mod_period 5 6 7 e (by norm_num), he]; norm_num
    exact not_dvd_23 (q := 7) (by norm_num) (by norm_num) (by norm_num) x y (by omega)

/-- `3^b + 1 = 2^j 5^e` with `e ≥ 1` forces `b ≤ 2`. -/
lemma eqC {b j e : ℕ} (he : 1 ≤ e) (h : 3 ^ b + 1 = 2 ^ j * 5 ^ e) : b ≤ 2 := by
  rcases Nat.lt_or_ge e 2 with he2 | he2
  · obtain rfl : e = 1 := by omega
    rw [pow_one] at h
    have hj : j ≤ 2 := by
      by_contra hj
      have : 8 ∣ 2 ^ j := by
        have := pow_dvd_pow 2 (by omega : 3 ≤ j)
        simpa using this
      have := three_pow_mod_eight b
      omega
    have h4 : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hj
    by_contra hb
    have : 3 ^ 3 ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h4 this
    omega
  · have h25 : 25 ∣ 2 ^ j * 5 ^ e := by
      have := pow_dvd_pow 5 he2
      exact Dvd.dvd.mul_left (by simpa using this) _
    have m25 : 3 ^ b % 25 = 24 := by omega
    rw [pow_mod_period 3 20 25 b (by norm_num)] at m25
    have hb : b % 20 = 10 := by
      have : b % 20 < 20 := Nat.mod_lt _ (by norm_num)
      interval_cases (b % 20) <;> simp_all
    have m : 3 ^ b % 1181 = 1180 := by
      rw [pow_mod_period 3 20 1181 b (by norm_num), hb]; norm_num
    exact absurd (by omega : 1181 ∣ 2 ^ j * 5 ^ e)
      (not_dvd_25 (q := 1181) (by norm_num) (by norm_num) (by norm_num) j e)

/-- `3^b = 2^j 5^e + 1` with `e ≥ 1` forces `b ≤ 4`. -/
lemma eqD {b j e : ℕ} (he : 1 ≤ e) (h : 3 ^ b = 2 ^ j * 5 ^ e + 1) : b ≤ 4 := by
  rcases Nat.lt_or_ge e 2 with he2 | he2
  · obtain rfl : e = 1 := by omega
    rw [pow_one] at h
    have m5 : 3 ^ b % 5 = 1 := by omega
    rw [pow_mod_period 3 4 5 b (by norm_num)] at m5
    have hb4 : b % 4 = 0 := by
      have : b % 4 < 4 := Nat.mod_lt _ (by norm_num)
      interval_cases (b % 4) <;> simp_all
    rcases (show b % 8 = 0 ∨ b % 8 = 4 by omega) with hb8 | hb8
    · have m : 3 ^ b % 41 = 1 := by
        rw [pow_mod_period 3 8 41 b (by norm_num), hb8]; norm_num
      exact absurd (by rw [pow_one]; omega : 41 ∣ 2 ^ j * 5 ^ 1)
        (not_dvd_25 (q := 41) (by norm_num) (by norm_num) (by norm_num) j 1)
    · have m : 3 ^ b % 32 = 17 := by
        rw [pow_mod_period 3 8 32 b (by norm_num), hb8]; norm_num
      have hj : j = 4 := by
        rcases Nat.lt_or_ge j 5 with hj | hj
        · interval_cases j <;> omega
        · have : 32 ∣ 2 ^ j := by
            have := pow_dvd_pow 2 hj
            simpa using this
          omega
      subst hj
      have h81 : 3 ^ b = 3 ^ 4 := by omega
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h81).le
  · have h25 : 25 ∣ 2 ^ j * 5 ^ e := by
      have := pow_dvd_pow 5 he2
      exact Dvd.dvd.mul_left (by simpa using this) _
    have m25 : 3 ^ b % 25 = 1 := by omega
    rw [pow_mod_period 3 20 25 b (by norm_num)] at m25
    have hb : b % 20 = 0 := by
      have : b % 20 < 20 := Nat.mod_lt _ (by norm_num)
      interval_cases (b % 20) <;> simp_all
    have m : 3 ^ b % 11 = 1 := by
      rw [pow_mod_period 3 20 11 b (by norm_num), hb]; norm_num
    exact absurd (by omega : 11 ∣ 2 ^ j * 5 ^ e)
      (not_dvd_25 (q := 11) (by norm_num) (by norm_num) (by norm_num) j e)

/-- `3^b + 2 = 5^e` forces `b ≤ 1`. -/
lemma eqF {b e : ℕ} (h : 3 ^ b + 2 = 5 ^ e) : b ≤ 1 := by
  by_contra hb
  have h9 : 9 ∣ 3 ^ b := by
    have := pow_dvd_pow 3 (by omega : 2 ≤ b)
    simpa using this
  have m9 : 5 ^ e % 9 = 2 := by omega
  rw [pow_mod_period 5 6 9 e (by norm_num)] at m9
  have he : e % 6 = 5 := by
    have : e % 6 < 6 := Nat.mod_lt _ (by norm_num)
    interval_cases (e % 6) <;> simp_all
  have m7 : 5 ^ e % 7 = 3 := by rw [pow_mod_period 5 6 7 e (by norm_num), he]; norm_num
  have m4 := five_pow_mod_four e
  have a7 : 3 ^ b % 7 = 1 := by omega
  have a4 : 3 ^ b % 4 = 3 := by omega
  rw [pow_mod_period 3 6 7 b (by norm_num)] at a7
  rw [pow_mod_period 3 2 4 b (by norm_num)] at a4
  have h6 : b % 6 = 0 := by
    have : b % 6 < 6 := Nat.mod_lt _ (by norm_num)
    interval_cases (b % 6) <;> simp_all
  have h2 : b % 2 = 1 := by
    have : b % 2 < 2 := Nat.mod_lt _ (by norm_num)
    interval_cases (b % 2) <;> simp_all
  omega

/-- `3^b = 5^e + 2` forces `b ≤ 3`. -/
lemma eqG {b e : ℕ} (h : 3 ^ b = 5 ^ e + 2) : b ≤ 3 := by
  by_contra hb
  have h81 : 81 ∣ 3 ^ b := by
    have := pow_dvd_pow 3 (by omega : 4 ≤ b)
    simpa using this
  have m81 : 5 ^ e % 81 = 79 := by omega
  rw [pow_mod_period 5 54 81 e (by norm_num)] at m81
  have he : e % 54 = 20 := by
    have : e % 54 < 54 := Nat.mod_lt _ (by norm_num)
    interval_cases (e % 54) <;> simp_all
  have m109 : 5 ^ e % 109 = 35 := by
    rw [pow_mod_period 5 54 109 e (by norm_num), he]; norm_num
  have a109 : 3 ^ b % 109 = 37 := by omega
  rw [pow_mod_period 3 27 109 b (by norm_num)] at a109
  have : b % 27 < 27 := Nat.mod_lt _ (by norm_num)
  interval_cases (b % 27) <;> simp_all

lemma two_prime_form {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (dp : p ∣ n)
    (dq : q ∣ n) (hc : n.primeFactors.card = 2) :
    ∃ k e : ℕ, 1 ≤ k ∧ 1 ≤ e ∧ n = p ^ k * q ^ e := by
  have hn : n ≠ 0 := by rintro rfl; simp at hc
  have h2 : p ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hp, dp, hn⟩
  have h3 : q ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hq, dq, hn⟩
  have hpf : n.primeFactors = {p, q} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · rw [hc, Finset.card_pair hpq]
  refine ⟨n.factorization p, n.factorization q,
    (hp.dvd_iff_one_le_factorization hn).1 dp, (hq.dvd_iff_one_le_factorization hn).1 dq, ?_⟩
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization, hpf, Finset.prod_pair hpq]

-- 2-adic bookkeeping: Y is the odd part 5^e, X or T the cofactor of N.
lemma adic_p4_a3 {X Y k : ℕ} (hY : Y % 2 = 1) (h : 8 * X + 4 = 2 ^ k * Y) : 2 * X + 1 = Y := by
  rcases k with _ | _ | _ | k
  · simp at h; omega
  · simp at h; omega
  · simp at h; omega
  · have : 2 ^ (k + 1 + 1 + 1) * Y = 8 * (2 ^ k * Y) := by ring
    omega

lemma adic_m4_a3 {X Y k : ℕ} (hY : Y % 2 = 1) (h : 8 * X = 2 ^ k * Y + 4) : 2 * X = Y + 1 := by
  rcases k with _ | _ | _ | k
  · simp at h; omega
  · simp at h; omega
  · simp at h; omega
  · have : 2 ^ (k + 1 + 1 + 1) * Y = 8 * (2 ^ k * Y) := by ring
    omega

lemma adic_p2_a2 {X Y k : ℕ} (hY : Y % 2 = 1) (h : 4 * X + 2 = 2 ^ k * Y) : 2 * X + 1 = Y := by
  rcases k with _ | _ | k
  · simp at h; omega
  · simp at h; omega
  · have : 2 ^ (k + 1 + 1) * Y = 4 * (2 ^ k * Y) := by ring
    omega

lemma adic_m2_a2 {X Y k : ℕ} (hY : Y % 2 = 1) (h : 4 * X = 2 ^ k * Y + 2) : 2 * X = Y + 1 := by
  rcases k with _ | _ | k
  · simp at h; omega
  · simp at h; omega
  · have : 2 ^ (k + 1 + 1) * Y = 4 * (2 ^ k * Y) := by ring
    omega

lemma adic_p4_a2 {T Y k : ℕ} (hY : Y % 2 = 1) (h : 4 * T + 4 = 2 ^ k * Y) :
    ∃ j, T + 1 = 2 ^ j * Y := by
  rcases k with _ | _ | j
  · simp at h; omega
  · simp at h; omega
  · refine ⟨j, ?_⟩
    have : 2 ^ (j + 1 + 1) * Y = 4 * (2 ^ j * Y) := by ring
    omega

lemma adic_m4_a2 {T Y k : ℕ} (hY : Y % 2 = 1) (h : 4 * T = 2 ^ k * Y + 4) :
    ∃ j, T = 2 ^ j * Y + 1 := by
  rcases k with _ | _ | j
  · simp at h; omega
  · simp at h; omega
  · refine ⟨j, ?_⟩
    have : 2 ^ (j + 1 + 1) * Y = 4 * (2 ^ j * Y) := by ring
    omega

lemma adic_p4_a1 {T Y k : ℕ} (hT : T % 2 = 1) (hY : Y % 2 = 1) (h : 2 * T + 4 = 2 ^ k * Y) :
    T + 2 = Y := by
  rcases k with _ | _ | k
  · simp at h; omega
  · simp at h; omega
  · have : 2 ^ (k + 1 + 1) * Y = 4 * (2 ^ k * Y) := by ring
    omega

lemma adic_m4_a1 {T Y k : ℕ} (hT : T % 2 = 1) (hY : Y % 2 = 1) (h : 2 * T = 2 ^ k * Y + 4) :
    T = Y + 2 := by
  rcases k with _ | _ | k
  · simp at h; omega
  · simp at h; omega
  · have : 2 ^ (k + 1 + 1) * Y = 4 * (2 ^ k * Y) := by ring
    omega

lemma adic_p2_a1 {T Y k : ℕ} (hY : Y % 2 = 1) (h : 2 * T + 2 = 2 ^ k * Y) :
    ∃ j, T + 1 = 2 ^ j * Y := by
  rcases k with _ | j
  · simp at h; omega
  · refine ⟨j, ?_⟩
    have : 2 ^ (j + 1) * Y = 2 * (2 ^ j * Y) := by ring
    omega

lemma adic_m2_a1 {T Y k : ℕ} (hY : Y % 2 = 1) (h : 2 * T = 2 ^ k * Y + 2) :
    ∃ j, T = 2 ^ j * Y + 1 := by
  rcases k with _ | j
  · simp at h; omega
  · refine ⟨j, ?_⟩
    have : 2 ^ (j + 1) * Y = 2 * (2 ^ j * Y) := by ring
    omega

lemma card_322 : (322 : ℕ).primeFactors.card = 3 := by
  rw [show (322 : ℕ) = 2 * 7 * 23 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  decide

/-- The centered window: no run of nine has its multiple of 6 in the middle. -/
lemma centered : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    ¬ ∀ i < 9, (2 ^ a * 3 ^ b - 4 + i).primeFactors.card = 2 := by
  intro a b ha hb hw
  have h2a : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have h3b : 3 ≤ 3 ^ b := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hN6 : 6 ≤ 2 ^ a * 3 ^ b := by nlinarith
  have w0 := hw 0 (by norm_num)
  have w2 := hw 2 (by norm_num)
  have w6 := hw 6 (by norm_num)
  have w8 := hw 8 (by norm_num)
  rw [show 2 ^ a * 3 ^ b - 4 + 0 = 2 ^ a * 3 ^ b - 4 by omega] at w0
  rw [show 2 ^ a * 3 ^ b - 4 + 2 = 2 ^ a * 3 ^ b - 2 by omega] at w2
  rw [show 2 ^ a * 3 ^ b - 4 + 6 = 2 ^ a * 3 ^ b + 2 by omega] at w6
  rw [show 2 ^ a * 3 ^ b - 4 + 8 = 2 ^ a * 3 ^ b + 4 by omega] at w8
  have n5 : ¬ 5 ∣ 2 ^ a * 3 ^ b := not_dvd_23 (by norm_num) (by norm_num) (by norm_num) a b
  have d2 : 2 ∣ 2 ^ a * 3 ^ b := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  have hT : 3 ^ b % 2 = 1 := by rw [Nat.pow_mod]; norm_num
  have p5 : Nat.Prime 5 := by norm_num
  have hY : ∀ e : ℕ, 5 ^ e % 2 = 1 := fun e => by rw [Nat.pow_mod]; norm_num
  rcases (show 2 ^ a * 3 ^ b % 5 = 1 ∨ 2 ^ a * 3 ^ b % 5 = 2 ∨ 2 ^ a * 3 ^ b % 5 = 3 ∨
      2 ^ a * 3 ^ b % 5 = 4 by omega) with h5 | h5 | h5 | h5
  · -- 5 divides N + 4
    obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two p5 (by norm_num)
      (by omega : 2 ∣ 2 ^ a * 3 ^ b + 4) (by omega : 5 ∣ 2 ^ a * 3 ^ b + 4) w8
    rcases (show a = 1 ∨ a = 2 ∨ 3 ≤ a by omega) with rfl | rfl | ha3
    · have := eqF (adic_p4_a1 hT (hY e) (show 2 * 3 ^ b + 4 = 2 ^ k * 5 ^ e by omega))
      interval_cases b
      have hp := not_prime_of_card_two (hw 0 (by norm_num)); norm_num at hp
    · obtain ⟨j, hj⟩ := adic_p4_a2 (hY e) (show 4 * 3 ^ b + 4 = 2 ^ k * 5 ^ e by omega)
      have := eqC he hj
      interval_cases b
      · norm_num at h5
      · have hp := not_prime_of_card_two (hw 5 (by norm_num)); norm_num at hp
    · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 3 := ⟨a - 3, by omega⟩
      have h1 := adic_p4_a3 (hY e) (show 8 * (2 ^ a * 3 ^ b) + 4 = 2 ^ k * 5 ^ e by
        rw [← hke]; ring)
      obtain ⟨hx, hy⟩ := eqA (show 2 ^ (a + 1) * 3 ^ b + 1 = 5 ^ e by rw [← h1]; ring)
      have hx' : a ≤ 2 := by omega
      interval_cases b
      interval_cases a
      · norm_num at h5
      · norm_num at h5
      · have hp := not_prime_of_card_two (hw 5 (by norm_num)); norm_num at hp
  · -- 5 divides N - 2
    obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two p5 (by norm_num)
      (by omega : 2 ∣ 2 ^ a * 3 ^ b - 2) (by omega : 5 ∣ 2 ^ a * 3 ^ b - 2) w2
    rcases (show a = 1 ∨ 2 ≤ a by omega) with rfl | ha2
    · obtain ⟨j, hj⟩ := adic_m2_a1 (hY e) (show 2 * 3 ^ b = 2 ^ k * 5 ^ e + 2 by omega)
      have := eqD he hj
      interval_cases b
      · norm_num at h5
      · norm_num at h5
      · norm_num at h5
      · have hp := not_prime_of_card_two (hw 5 (by norm_num)); norm_num at hp
    · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
      have h1 := adic_m2_a2 (hY e) (show 4 * (2 ^ a * 3 ^ b) = 2 ^ k * 5 ^ e + 2 by
        rw [show 4 * (2 ^ a * 3 ^ b) = 2 ^ (a + 2) * 3 ^ b by ring]; omega)
      obtain ⟨hx, hy⟩ := eqB (show 5 ^ e + 1 = 2 ^ (a + 1) * 3 ^ b by rw [← h1]; ring)
      obtain rfl : a = 0 := by omega
      interval_cases b
      have hp := not_prime_of_card_two (hw 3 (by norm_num)); norm_num at hp
  · -- 5 divides N + 2
    obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two p5 (by norm_num)
      (by omega : 2 ∣ 2 ^ a * 3 ^ b + 2) (by omega : 5 ∣ 2 ^ a * 3 ^ b + 2) w6
    rcases (show a = 1 ∨ 2 ≤ a by omega) with rfl | ha2
    · obtain ⟨j, hj⟩ := adic_p2_a1 (hY e) (show 2 * 3 ^ b + 2 = 2 ^ k * 5 ^ e by omega)
      have := eqC he hj
      interval_cases b
      · norm_num at h5
      · have hp := not_prime_of_card_two (hw 3 (by norm_num)); norm_num at hp
    · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
      have h1 := adic_p2_a2 (hY e) (show 4 * (2 ^ a * 3 ^ b) + 2 = 2 ^ k * 5 ^ e by
        rw [← hke]; ring)
      obtain ⟨hx, hy⟩ := eqA (show 2 ^ (a + 1) * 3 ^ b + 1 = 5 ^ e by rw [← h1]; ring)
      have hx' : a ≤ 2 := by omega
      interval_cases b
      interval_cases a
      · norm_num at h5
      · norm_num at h5
      · have hp := not_prime_of_card_two (hw 3 (by norm_num)); norm_num at hp
  · -- 5 divides N - 4
    obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two p5 (by norm_num)
      (by omega : 2 ∣ 2 ^ a * 3 ^ b - 4) (by omega : 5 ∣ 2 ^ a * 3 ^ b - 4) w0
    rcases (show a = 1 ∨ a = 2 ∨ 3 ≤ a by omega) with rfl | rfl | ha3
    · have := eqG (adic_m4_a1 hT (hY e) (show 2 * 3 ^ b = 2 ^ k * 5 ^ e + 4 by omega))
      interval_cases b
      · norm_num at h5
      · norm_num at h5
      · have hp := not_prime_of_card_two (hw 3 (by norm_num)); norm_num at hp
    · obtain ⟨j, hj⟩ := adic_m4_a2 (hY e) (show 4 * 3 ^ b = 2 ^ k * 5 ^ e + 4 by omega)
      have := eqD he hj
      interval_cases b
      · norm_num at h5
      · norm_num at h5
      · norm_num at h5
      · have h' := hw 2 (by norm_num); norm_num [card_322] at h'
    · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 3 := ⟨a - 3, by omega⟩
      have h1 := adic_m4_a3 (hY e) (show 8 * (2 ^ a * 3 ^ b) = 2 ^ k * 5 ^ e + 4 by
        rw [show 8 * (2 ^ a * 3 ^ b) = 2 ^ (a + 3) * 3 ^ b by ring]; omega)
      obtain ⟨hx, hy⟩ := eqB (show 5 ^ e + 1 = 2 ^ (a + 1) * 3 ^ b by rw [← h1]; ring)
      obtain rfl : a = 0 := by omega
      interval_cases b
      have hp := not_prime_of_card_two (hw 3 (by norm_num)); norm_num at hp

/-! ## Certificate machinery -/

/-- Certificate lemma, form `g^n + t = Y`. -/
lemma cert_add {g t M P B : ℕ} (cert : ℕ → ℕ) {n Y : ℕ} (hP : 0 < P)
    (hper : g ^ P % M = 1) (hMY : M ∣ Y) (hYc : ∀ q, Nat.Coprime q B → Nat.Coprime q Y)
    (hc : ∀ r < P, (g ^ r + t) % M = 0 →
      1 < cert r ∧ Nat.Coprime (cert r) B ∧ g ^ P % cert r = 1 ∧ (g ^ r + t) % cert r = 0)
    (h : g ^ n + t = Y) : False := by
  have hr : n % P < P := Nat.mod_lt _ hP
  have h1 : (g ^ (n % P) + t) % M = 0 := by
    have : (g ^ n + t) % M = 0 := by rw [h]; exact Nat.mod_eq_zero_of_dvd hMY
    rwa [Nat.add_mod, pow_mod_period g P M n hper, ← Nat.add_mod] at this
  obtain ⟨hq1, hqB, hqper, hqr⟩ := hc _ hr h1
  have hq : cert (n % P) ∣ Y := by
    have : (g ^ n + t) % cert (n % P) = 0 := by
      rw [Nat.add_mod, pow_mod_period g P _ n hqper, ← Nat.add_mod]; exact hqr
    rw [h] at this; exact Nat.dvd_of_mod_eq_zero this
  have := Nat.Coprime.eq_one_of_dvd (hYc _ hqB) hq
  omega

/-- Certificate lemma, form `g^n = Y + t`. -/
lemma cert_eq {g t M P B : ℕ} (cert : ℕ → ℕ) {n Y : ℕ} (hP : 0 < P)
    (hper : g ^ P % M = 1) (hMY : M ∣ Y) (hYc : ∀ q, Nat.Coprime q B → Nat.Coprime q Y)
    (hc : ∀ r < P, g ^ r % M = t % M →
      1 < cert r ∧ Nat.Coprime (cert r) B ∧ g ^ P % cert r = 1 ∧ g ^ r % cert r = t % cert r)
    (h : g ^ n = Y + t) : False := by
  have hr : n % P < P := Nat.mod_lt _ hP
  have h1 : g ^ (n % P) % M = t % M := by
    rw [← pow_mod_period g P M n hper, h, Nat.add_mod, Nat.mod_eq_zero_of_dvd hMY, zero_add,
      Nat.mod_mod]
  obtain ⟨hq1, hqB, hqper, hqr⟩ := hc _ hr h1
  have hq : cert (n % P) ∣ Y := by
    have e1 : (Y + t) % cert (n % P) = t % cert (n % P) := by
      rw [← h, pow_mod_period g P _ n hqper]; exact hqr
    have : Y % cert (n % P) = 0 := by
      have := Nat.sub_mod_eq_zero_of_mod_eq e1
      simpa using this
    exact Nat.dvd_of_mod_eq_zero this
  have := Nat.Coprime.eq_one_of_dvd (hYc _ hqB) hq
  omega

lemma cop_mul_pow {q u v : ℕ} (i j : ℕ) (h : Nat.Coprime q (u * v)) :
    Nat.Coprime q (u ^ i * v ^ j) := by
  have hu : Nat.Coprime q u := Nat.Coprime.coprime_dvd_right (dvd_mul_right u v) h
  have hv : Nat.Coprime q v := Nat.Coprime.coprime_dvd_right (dvd_mul_left v u) h
  exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ hu) (Nat.Coprime.pow_right _ hv)

/-! ## Exponential equations against 3-smooth numbers and small primes -/

lemma SUp7 {x y e : ℕ} (h : 2 ^ x * 3 ^ y + 1 = 7 ^ e) : x ≤ 4 ∧ y ≤ 1 := by
  constructor
  · by_contra hx
    have hM : 2 ^ 5 ∣ 2 ^ x * 3 ^ y := Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
    exact cert_eq (B := 2 * 3) (t := 1) (P := 4) (fun _ => 5) (by norm_num) (by norm_num) hM
      (fun q hq => cop_mul_pow x y hq) (by decide) h.symm
  · by_contra hy
    have hM : 3 ^ 2 ∣ 2 ^ x * 3 ^ y := Dvd.dvd.mul_left (pow_dvd_pow 3 (by omega)) _
    exact cert_eq (B := 2 * 3) (t := 1) (P := 3) (fun _ => 19) (by norm_num) (by norm_num) hM
      (fun q hq => cop_mul_pow x y hq) (by decide) h.symm

lemma SUm7 {x y e : ℕ} (hy : 1 ≤ y) (h : 7 ^ e + 1 = 2 ^ x * 3 ^ y) : False := by
  have hM : 3 ^ 1 ∣ 2 ^ x * 3 ^ y := Dvd.dvd.mul_left (pow_dvd_pow 3 hy) _
  exact cert_add (B := 2 * 3) (P := 1) (fun _ => 5) (by norm_num) (by norm_num) hM
    (fun q hq => cop_mul_pow x y hq) (by decide) h

lemma SUp13 {x y e : ℕ} (h : 2 ^ x * 3 ^ y + 1 = 13 ^ e) : x ≤ 2 ∧ y ≤ 1 := by
  constructor
  · by_contra hx
    have hM : 2 ^ 3 ∣ 2 ^ x * 3 ^ y := Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
    exact cert_eq (B := 2 * 3) (t := 1) (P := 2) (fun _ => 7) (by norm_num) (by norm_num) hM
      (fun q hq => cop_mul_pow x y hq) (by decide) h.symm
  · by_contra hy
    have hM : 3 ^ 2 ∣ 2 ^ x * 3 ^ y := Dvd.dvd.mul_left (pow_dvd_pow 3 (by omega)) _
    exact cert_eq (B := 2 * 3) (t := 1) (P := 3) (fun _ => 61) (by norm_num) (by norm_num) hM
      (fun q hq => cop_mul_pow x y hq) (by decide) h.symm

lemma SUm13 {x y e : ℕ} (hy : 1 ≤ y) (h : 13 ^ e + 1 = 2 ^ x * 3 ^ y) : False := by
  have hM : 3 ^ 1 ∣ 2 ^ x * 3 ^ y := Dvd.dvd.mul_left (pow_dvd_pow 3 hy) _
  exact cert_add (B := 2 * 3) (P := 1) (fun _ => 5) (by norm_num) (by norm_num) hM
    (fun q hq => cop_mul_pow x y hq) (by decide) h

lemma SUp11 {x y e : ℕ} (hx : 1 ≤ x) (h : 2 ^ x * 3 ^ y + 1 = 11 ^ e) : False := by
  have hM : 2 ^ 1 ∣ 2 ^ x * 3 ^ y := Dvd.dvd.mul_right (pow_dvd_pow 2 hx) _
  exact cert_eq (B := 2 * 3) (t := 1) (P := 1) (fun _ => 5) (by norm_num) (by norm_num) hM
    (fun q hq => cop_mul_pow x y hq) (by decide) h.symm

lemma Tp7 {b j e : ℕ} (he : 1 ≤ e) (h : 3 ^ b + 1 = 2 ^ j * 7 ^ e) : b ≤ 3 := by
  obtain rfl : e = 1 := by
    by_contra he2
    have hM : 7 ^ 2 ∣ 2 ^ j * 7 ^ e := Dvd.dvd.mul_left (pow_dvd_pow 7 (by omega)) _
    exact cert_add (B := 2 * 7) (P := 42) (fun _ => 43) (by norm_num) (by norm_num) hM
      (fun q hq => cop_mul_pow j e hq) (by decide) h
  have hj : j ≤ 2 := by
    by_contra hj
    have hM : 2 ^ 3 ∣ 2 ^ j * 7 ^ 1 := Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
    exact cert_add (B := 2 * 7) (P := 2) (fun _ => 5) (by norm_num) (by norm_num) hM
      (fun q hq => cop_mul_pow j 1 hq) (by decide) h
  have h4 : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hj
  by_contra hb
  have : 3 ^ 4 ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at h4 this h
  omega

lemma Tm7 {b j e : ℕ} (he : 1 ≤ e) (h : 3 ^ b = 2 ^ j * 7 ^ e + 1) : False := by
  have hM : 7 ^ 1 ∣ 2 ^ j * 7 ^ e := Dvd.dvd.mul_left (pow_dvd_pow 7 he) _
  exact cert_eq (B := 2 * 7) (t := 1) (P := 6) (fun _ => 13) (by norm_num) (by norm_num) hM
    (fun q hq => cop_mul_pow j e hq) (by decide) h

lemma Tp13 {b j e : ℕ} (he : 1 ≤ e) (h : 3 ^ b + 1 = 2 ^ j * 13 ^ e) : False := by
  have hM : 13 ^ 1 ∣ 2 ^ j * 13 ^ e := Dvd.dvd.mul_left (pow_dvd_pow 13 he) _
  exact cert_add (B := 2 * 13) (P := 3) (fun _ => 5) (by norm_num) (by norm_num) hM
    (fun q hq => cop_mul_pow j e hq) (by decide) h

lemma Tm13 {b j e : ℕ} (he : 1 ≤ e) (h : 3 ^ b = 2 ^ j * 13 ^ e + 1) : b ≤ 4 := by
  obtain rfl : e = 1 := by
    by_contra he2
    have hM : 13 ^ 2 ∣ 2 ^ j * 13 ^ e := Dvd.dvd.mul_left (pow_dvd_pow 13 (by omega)) _
    exact cert_eq (B := 2 * 13) (t := 1) (P := 39) (fun _ => 313) (by norm_num) (by norm_num) hM
      (fun q hq => cop_mul_pow j e hq) (by decide) h
  have hj : j ≤ 3 := by
    by_contra hj
    have hM : 2 ^ 4 ∣ 2 ^ j * 13 ^ 1 := Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
    exact cert_eq (B := 2 * 13) (t := 1) (P := 4) (fun _ => 5) (by norm_num) (by norm_num) hM
      (fun q hq => cop_mul_pow j 1 hq) (by decide) h
  have h4 : 2 ^ j ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hj
  by_contra hb
  have : 3 ^ 5 ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at h4 this h
  omega

lemma Tm11 {b j e : ℕ} (he : 1 ≤ e) (h : 3 ^ b = 2 ^ j * 11 ^ e + 1) : b ≤ 6 := by
  have he2 : e ≤ 2 := by
    by_contra he2
    have hM : 11 ^ 3 ∣ 2 ^ j * 11 ^ e := Dvd.dvd.mul_left (pow_dvd_pow 11 (by omega)) _
    exact cert_eq (B := 2 * 11) (t := 1) (P := 55) (fun _ => 23) (by norm_num) (by norm_num) hM
      (fun q hq => cop_mul_pow j e hq) (by decide) h
  have hj : j ≤ 3 := by
    by_contra hj
    have hM : 2 ^ 4 ∣ 2 ^ j * 11 ^ e := Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
    exact cert_eq (B := 2 * 11) (t := 1) (P := 4) (fun _ => 5) (by norm_num) (by norm_num) hM
      (fun q hq => cop_mul_pow j e hq) (by decide) h
  have h4 : 2 ^ j * 11 ^ e ≤ 2 ^ 3 * 11 ^ 2 :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hj) (Nat.pow_le_pow_right (by norm_num) he2)
  by_contra hb
  have : 3 ^ 7 ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at h4 this
  omega

lemma Up7 {b e : ℕ} (hb : 1 ≤ b) (h : 3 ^ b + 2 = 7 ^ e) : False := by
  have hM : 3 ^ 1 ∣ 3 ^ b := pow_dvd_pow 3 hb
  exact cert_eq (B := 3) (t := 2) (P := 1) (fun _ => 5) (by norm_num) (by norm_num) hM
    (fun q hq => Nat.Coprime.pow_right _ hq) (by decide) h.symm

lemma Up13 {b e : ℕ} (hb : 1 ≤ b) (h : 3 ^ b + 2 = 13 ^ e) : False := by
  have hM : 3 ^ 1 ∣ 3 ^ b := pow_dvd_pow 3 hb
  exact cert_eq (B := 3) (t := 2) (P := 1) (fun _ => 5) (by norm_num) (by norm_num) hM
    (fun q hq => Nat.Coprime.pow_right _ hq) (by decide) h.symm

lemma Up11 {b e : ℕ} (h : 3 ^ b + 2 = 11 ^ e) : b ≤ 2 := by
  have he : e ≤ 1 := by
    by_contra he
    have hM : 11 ^ 2 ∣ 11 ^ e := pow_dvd_pow 11 (by omega)
    exact cert_add (B := 11) (P := 5) (fun _ => 5) (by norm_num) (by norm_num) hM
      (fun q hq => Nat.Coprime.pow_right _ hq) (by decide) h
  interval_cases e
  · simp at h
  · by_contra hb
    have : 3 ^ 3 ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h this
    omega

lemma Vp5 {a j e : ℕ} (he : 1 ≤ e) (h : 2 ^ a + 1 = 3 ^ j * 5 ^ e) : a ≤ 5 := by
  obtain rfl : e = 1 := by
    by_contra he2
    have hM : 5 ^ 2 ∣ 3 ^ j * 5 ^ e := Dvd.dvd.mul_left (pow_dvd_pow 5 (by omega)) _
    exact cert_add (B := 3 * 5) (P := 20) (fun _ => 41) (by norm_num) (by norm_num) hM
      (fun q hq => cop_mul_pow j e hq) (by decide) h
  have hj : j ≤ 2 := by
    by_contra hj
    have hM : 3 ^ 3 ∣ 3 ^ j * 5 ^ 1 := Dvd.dvd.mul_right (pow_dvd_pow 3 (by omega)) _
    exact cert_add (B := 3 * 5) (P := 18) (fun _ => 19) (by norm_num) (by norm_num) hM
      (fun q hq => cop_mul_pow j 1 hq) (by decide) h
  have h4 : 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hj
  by_contra ha
  have : 2 ^ 6 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at h4 this h
  omega

lemma Vm5 {a j e : ℕ} (he : 1 ≤ e) (h : 2 ^ a = 3 ^ j * 5 ^ e + 1) : a ≤ 4 := by
  obtain rfl : e = 1 := by
    by_contra he2
    have hM : 5 ^ 2 ∣ 3 ^ j * 5 ^ e := Dvd.dvd.mul_left (pow_dvd_pow 5 (by omega)) _
    exact cert_eq (B := 3 * 5) (t := 1) (P := 20) (fun _ => 11) (by norm_num) (by norm_num) hM
      (fun q hq => cop_mul_pow j e hq) (by decide) h
  have hj : j ≤ 1 := by
    by_contra hj
    have hM : 3 ^ 2 ∣ 3 ^ j * 5 ^ 1 := Dvd.dvd.mul_right (pow_dvd_pow 3 (by omega)) _
    exact cert_eq (B := 3 * 5) (t := 1) (P := 6) (fun _ => 7) (by norm_num) (by norm_num) hM
      (fun q hq => cop_mul_pow j 1 hq) (by decide) h
  have h4 : 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj
  by_contra ha
  have : 2 ^ 5 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at h4 this h
  omega

lemma Vp7 {a j e : ℕ} (he : 1 ≤ e) (h : 2 ^ a + 1 = 3 ^ j * 7 ^ e) : False := by
  have hM : 7 ^ 1 ∣ 3 ^ j * 7 ^ e := Dvd.dvd.mul_left (pow_dvd_pow 7 he) _
  exact cert_add (B := 3 * 7) (P := 3) (fun _ => 5) (by norm_num) (by norm_num) hM
    (fun q hq => cop_mul_pow j e hq) (by decide) h

lemma Vp13 {a j e : ℕ} (he : 1 ≤ e) (h : 2 ^ a + 1 = 3 ^ j * 13 ^ e) : False := by
  have hM : 13 ^ 1 ∣ 3 ^ j * 13 ^ e := Dvd.dvd.mul_left (pow_dvd_pow 13 he) _
  exact cert_add (B := 3 * 13) (P := 12) (fun _ => 5) (by norm_num) (by norm_num) hM
    (fun q hq => cop_mul_pow j e hq) (by decide) h

lemma Vm13 {a j e : ℕ} (he : 1 ≤ e) (h : 2 ^ a = 3 ^ j * 13 ^ e + 1) : False := by
  have hM : 13 ^ 1 ∣ 3 ^ j * 13 ^ e := Dvd.dvd.mul_left (pow_dvd_pow 13 he) _
  exact cert_eq (B := 3 * 13) (t := 1) (P := 12) (fun _ => 5) (by norm_num) (by norm_num) hM
    (fun q hq => cop_mul_pow j e hq) (by decide) h

/-! ## 3-adic bookkeeping -/

lemma adic3_p_b1 {T Y k : ℕ} (hY : Y % 3 ≠ 0) (h : 3 * T + 3 = 3 ^ k * Y) :
    ∃ j, T + 1 = 3 ^ j * Y := by
  rcases k with _ | j
  · simp at h; omega
  · refine ⟨j, ?_⟩
    have : 3 ^ (j + 1) * Y = 3 * (3 ^ j * Y) := by ring
    omega

lemma adic3_m_b1 {T Y k : ℕ} (hY : Y % 3 ≠ 0) (h : 3 * T = 3 ^ k * Y + 3) :
    ∃ j, T = 3 ^ j * Y + 1 := by
  rcases k with _ | j
  · simp at h; omega
  · refine ⟨j, ?_⟩
    have : 3 ^ (j + 1) * Y = 3 * (3 ^ j * Y) := by ring
    omega

lemma adic3_p {X Y k : ℕ} (hY : Y % 3 ≠ 0) (h : 9 * X + 3 = 3 ^ k * Y) : 3 * X + 1 = Y := by
  rcases k with _ | _ | k
  · simp at h; omega
  · simp at h; omega
  · have : 3 ^ (k + 1 + 1) * Y = 9 * (3 ^ k * Y) := by ring
    omega

lemma adic3_m {X Y k : ℕ} (hY : Y % 3 ≠ 0) (h : 9 * X = 3 ^ k * Y + 3) : 3 * X = Y + 1 := by
  rcases k with _ | _ | k
  · simp at h; omega
  · simp at h; omega
  · have : 3 ^ (k + 1 + 1) * Y = 9 * (3 ^ k * Y) := by ring
    omega

lemma smooth_le {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B) : 2 ^ a * 3 ^ b ≤ 2 ^ A * 3 ^ B :=
  Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) ha) (Nat.pow_le_pow_right (by norm_num) hb)

lemma odd_pow_two {p e : ℕ} (hp : p % 2 = 1) : p ^ e % 2 = 1 := by
  rw [Nat.pow_mod, hp]; simp

lemma not3_pow {p e : ℕ} (hp : p.Prime) (h3 : p ≠ 3) : p ^ e % 3 ≠ 0 := by
  intro h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
    (Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h))
  exact h3 this.symm

lemma two_dvd_N {a b : ℕ} (ha : 1 ≤ a) : 2 ∣ 2 ^ a * 3 ^ b :=
  Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _

lemma three_dvd_N {a b : ℕ} (hb : 1 ≤ b) : 3 ∣ 2 ^ a * 3 ^ b :=
  Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _

lemma N_ge {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 6 ≤ 2 ^ a * 3 ^ b := by
  have := smooth_le (A := a) (B := b) ha hb
  simpa using this

/-! ## Position lemmas: a small prime divides a constrained term of the window -/

lemma Lp4_5 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 5 ∣ 2 ^ a * 3 ^ b + 4)
    (hc : (2 ^ a * 3 ^ b + 4).primeFactors.card = 2) : 2 ^ a * 3 ^ b ≤ 1458 := by
  obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two (by norm_num : Nat.Prime 5)
    (by norm_num) (Dvd.dvd.add (two_dvd_N ha) (by norm_num)) hd hc
  have hY : 5 ^ e % 2 = 1 := odd_pow_two (by norm_num)
  have hT : 3 ^ b % 2 = 1 := odd_pow_two (by norm_num)
  rcases (show a = 1 ∨ a = 2 ∨ 3 ≤ a by omega) with rfl | rfl | ha3
  · have := eqF (adic_p4_a1 hT hY (show 2 * 3 ^ b + 4 = 2 ^ k * 5 ^ e by rw [← hke]; ring))
    calc 2 ^ 1 * 3 ^ b ≤ 2 ^ 1 * 3 ^ 1 := smooth_le le_rfl this
      _ ≤ 1458 := by norm_num
  · obtain ⟨j, hj⟩ := adic_p4_a2 hY (show 4 * 3 ^ b + 4 = 2 ^ k * 5 ^ e by rw [← hke]; ring)
    calc 2 ^ 2 * 3 ^ b ≤ 2 ^ 2 * 3 ^ 2 := smooth_le le_rfl (eqC he hj)
      _ ≤ 1458 := by norm_num
  · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 3 := ⟨a - 3, by omega⟩
    have h1 := adic_p4_a3 hY (show 8 * (2 ^ a * 3 ^ b) + 4 = 2 ^ k * 5 ^ e by rw [← hke]; ring)
    obtain ⟨hx, hy⟩ := eqA (show 2 ^ (a + 1) * 3 ^ b + 1 = 5 ^ e by rw [← h1]; ring)
    calc 2 ^ (a + 3) * 3 ^ b ≤ 2 ^ 5 * 3 ^ 1 := smooth_le (by omega) hy
      _ ≤ 1458 := by norm_num

lemma Lp4_7 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 7 ∣ 2 ^ a * 3 ^ b + 4)
    (hc : (2 ^ a * 3 ^ b + 4).primeFactors.card = 2) : 2 ^ a * 3 ^ b ≤ 1458 := by
  obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two (by norm_num : Nat.Prime 7)
    (by norm_num) (Dvd.dvd.add (two_dvd_N ha) (by norm_num)) hd hc
  have hY : 7 ^ e % 2 = 1 := odd_pow_two (by norm_num)
  have hT : 3 ^ b % 2 = 1 := odd_pow_two (by norm_num)
  rcases (show a = 1 ∨ a = 2 ∨ 3 ≤ a by omega) with rfl | rfl | ha3
  · exact (Up7 hb (adic_p4_a1 hT hY (show 2 * 3 ^ b + 4 = 2 ^ k * 7 ^ e by
      rw [← hke]; ring))).elim
  · obtain ⟨j, hj⟩ := adic_p4_a2 hY (show 4 * 3 ^ b + 4 = 2 ^ k * 7 ^ e by rw [← hke]; ring)
    calc 2 ^ 2 * 3 ^ b ≤ 2 ^ 2 * 3 ^ 3 := smooth_le le_rfl (Tp7 he hj)
      _ ≤ 1458 := by norm_num
  · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 3 := ⟨a - 3, by omega⟩
    have h1 := adic_p4_a3 hY (show 8 * (2 ^ a * 3 ^ b) + 4 = 2 ^ k * 7 ^ e by rw [← hke]; ring)
    obtain ⟨hx, hy⟩ := SUp7 (show 2 ^ (a + 1) * 3 ^ b + 1 = 7 ^ e by rw [← h1]; ring)
    calc 2 ^ (a + 3) * 3 ^ b ≤ 2 ^ 6 * 3 ^ 1 := smooth_le (by omega) hy
      _ ≤ 1458 := by norm_num

lemma Lp4_13 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 13 ∣ 2 ^ a * 3 ^ b + 4)
    (hc : (2 ^ a * 3 ^ b + 4).primeFactors.card = 2) : 2 ^ a * 3 ^ b ≤ 1458 := by
  obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two (by norm_num : Nat.Prime 13)
    (by norm_num) (Dvd.dvd.add (two_dvd_N ha) (by norm_num)) hd hc
  have hY : 13 ^ e % 2 = 1 := odd_pow_two (by norm_num)
  have hT : 3 ^ b % 2 = 1 := odd_pow_two (by norm_num)
  rcases (show a = 1 ∨ a = 2 ∨ 3 ≤ a by omega) with rfl | rfl | ha3
  · exact (Up13 hb (adic_p4_a1 hT hY (show 2 * 3 ^ b + 4 = 2 ^ k * 13 ^ e by
      rw [← hke]; ring))).elim
  · obtain ⟨j, hj⟩ := adic_p4_a2 hY (show 4 * 3 ^ b + 4 = 2 ^ k * 13 ^ e by rw [← hke]; ring)
    exact (Tp13 he hj).elim
  · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 3 := ⟨a - 3, by omega⟩
    have h1 := adic_p4_a3 hY (show 8 * (2 ^ a * 3 ^ b) + 4 = 2 ^ k * 13 ^ e by rw [← hke]; ring)
    obtain ⟨hx, hy⟩ := SUp13 (show 2 ^ (a + 1) * 3 ^ b + 1 = 13 ^ e by rw [← h1]; ring)
    calc 2 ^ (a + 3) * 3 ^ b ≤ 2 ^ 4 * 3 ^ 1 := smooth_le (by omega) hy
      _ ≤ 1458 := by norm_num

lemma Lp2_7 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 7 ∣ 2 ^ a * 3 ^ b + 2)
    (hc : (2 ^ a * 3 ^ b + 2).primeFactors.card = 2) : 2 ^ a * 3 ^ b ≤ 1458 := by
  obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two (by norm_num : Nat.Prime 7)
    (by norm_num) (Dvd.dvd.add (two_dvd_N ha) (by norm_num)) hd hc
  have hY : 7 ^ e % 2 = 1 := odd_pow_two (by norm_num)
  rcases (show a = 1 ∨ 2 ≤ a by omega) with rfl | ha2
  · obtain ⟨j, hj⟩ := adic_p2_a1 hY (show 2 * 3 ^ b + 2 = 2 ^ k * 7 ^ e by rw [← hke]; ring)
    calc 2 ^ 1 * 3 ^ b ≤ 2 ^ 1 * 3 ^ 3 := smooth_le le_rfl (Tp7 he hj)
      _ ≤ 1458 := by norm_num
  · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
    have h1 := adic_p2_a2 hY (show 4 * (2 ^ a * 3 ^ b) + 2 = 2 ^ k * 7 ^ e by rw [← hke]; ring)
    obtain ⟨hx, hy⟩ := SUp7 (show 2 ^ (a + 1) * 3 ^ b + 1 = 7 ^ e by rw [← h1]; ring)
    calc 2 ^ (a + 2) * 3 ^ b ≤ 2 ^ 5 * 3 ^ 1 := smooth_le (by omega) hy
      _ ≤ 1458 := by norm_num

lemma Lp2_13 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 13 ∣ 2 ^ a * 3 ^ b + 2)
    (hc : (2 ^ a * 3 ^ b + 2).primeFactors.card = 2) : 2 ^ a * 3 ^ b ≤ 1458 := by
  obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two (by norm_num : Nat.Prime 13)
    (by norm_num) (Dvd.dvd.add (two_dvd_N ha) (by norm_num)) hd hc
  have hY : 13 ^ e % 2 = 1 := odd_pow_two (by norm_num)
  rcases (show a = 1 ∨ 2 ≤ a by omega) with rfl | ha2
  · obtain ⟨j, hj⟩ := adic_p2_a1 hY (show 2 * 3 ^ b + 2 = 2 ^ k * 13 ^ e by rw [← hke]; ring)
    exact (Tp13 he hj).elim
  · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
    have h1 := adic_p2_a2 hY (show 4 * (2 ^ a * 3 ^ b) + 2 = 2 ^ k * 13 ^ e by rw [← hke]; ring)
    obtain ⟨hx, hy⟩ := SUp13 (show 2 ^ (a + 1) * 3 ^ b + 1 = 13 ^ e by rw [← h1]; ring)
    calc 2 ^ (a + 2) * 3 ^ b ≤ 2 ^ 3 * 3 ^ 1 := smooth_le (by omega) hy
      _ ≤ 1458 := by norm_num

lemma Lm2_7 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 7 ∣ 2 ^ a * 3 ^ b - 2)
    (hc : (2 ^ a * 3 ^ b - 2).primeFactors.card = 2) : 2 ^ a * 3 ^ b ≤ 1458 := by
  have h6 := N_ge ha hb
  obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two (by norm_num : Nat.Prime 7)
    (by norm_num) (Nat.dvd_sub (two_dvd_N ha) (dvd_refl 2)) hd hc
  have hY : 7 ^ e % 2 = 1 := odd_pow_two (by norm_num)
  rcases (show a = 1 ∨ 2 ≤ a by omega) with rfl | ha2
  · obtain ⟨j, hj⟩ := adic_m2_a1 hY (show 2 * 3 ^ b = 2 ^ k * 7 ^ e + 2 by omega)
    exact (Tm7 he hj).elim
  · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
    have h1 := adic_m2_a2 hY (show 4 * (2 ^ a * 3 ^ b) = 2 ^ k * 7 ^ e + 2 by
      rw [show 4 * (2 ^ a * 3 ^ b) = 2 ^ (a + 2) * 3 ^ b by ring]; omega)
    exact (SUm7 hb (show 7 ^ e + 1 = 2 ^ (a + 1) * 3 ^ b by rw [← h1]; ring)).elim

lemma Lm2_13 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 13 ∣ 2 ^ a * 3 ^ b - 2)
    (hc : (2 ^ a * 3 ^ b - 2).primeFactors.card = 2) : 2 ^ a * 3 ^ b ≤ 1458 := by
  have h6 := N_ge ha hb
  obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two (by norm_num : Nat.Prime 13)
    (by norm_num) (Nat.dvd_sub (two_dvd_N ha) (dvd_refl 2)) hd hc
  have hY : 13 ^ e % 2 = 1 := odd_pow_two (by norm_num)
  rcases (show a = 1 ∨ 2 ≤ a by omega) with rfl | ha2
  · obtain ⟨j, hj⟩ := adic_m2_a1 hY (show 2 * 3 ^ b = 2 ^ k * 13 ^ e + 2 by omega)
    calc 2 ^ 1 * 3 ^ b ≤ 2 ^ 1 * 3 ^ 4 := smooth_le le_rfl (Tm13 he hj)
      _ ≤ 1458 := by norm_num
  · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
    have h1 := adic_m2_a2 hY (show 4 * (2 ^ a * 3 ^ b) = 2 ^ k * 13 ^ e + 2 by
      rw [show 4 * (2 ^ a * 3 ^ b) = 2 ^ (a + 2) * 3 ^ b by ring]; omega)
    exact (SUm13 hb (show 13 ^ e + 1 = 2 ^ (a + 1) * 3 ^ b by rw [← h1]; ring)).elim

lemma Lp3_5 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 5 ∣ 2 ^ a * 3 ^ b + 3)
    (hc : (2 ^ a * 3 ^ b + 3).primeFactors.card = 2) : 2 ^ a * 3 ^ b ≤ 1458 := by
  obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_three (by norm_num : Nat.Prime 5)
    (by norm_num) (Dvd.dvd.add (three_dvd_N hb) (by norm_num)) hd hc
  have hY : 5 ^ e % 3 ≠ 0 := not3_pow (by norm_num) (by norm_num)
  rcases (show b = 1 ∨ 2 ≤ b by omega) with rfl | hb2
  · obtain ⟨j, hj⟩ := adic3_p_b1 hY (show 3 * 2 ^ a + 3 = 3 ^ k * 5 ^ e by rw [← hke]; ring)
    calc 2 ^ a * 3 ^ 1 ≤ 2 ^ 5 * 3 ^ 1 := smooth_le (Vp5 he hj) le_rfl
      _ ≤ 1458 := by norm_num
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
    have h1 := adic3_p hY (show 9 * (2 ^ a * 3 ^ b) + 3 = 3 ^ k * 5 ^ e by rw [← hke]; ring)
    obtain ⟨hx, hy⟩ := eqA (show 2 ^ a * 3 ^ (b + 1) + 1 = 5 ^ e by rw [← h1]; ring)
    calc 2 ^ a * 3 ^ (b + 2) ≤ 2 ^ 3 * 3 ^ 2 := smooth_le hx (by omega)
      _ ≤ 1458 := by norm_num

lemma Lp3_7 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 7 ∣ 2 ^ a * 3 ^ b + 3)
    (hc : (2 ^ a * 3 ^ b + 3).primeFactors.card = 2) : 2 ^ a * 3 ^ b ≤ 1458 := by
  obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_three (by norm_num : Nat.Prime 7)
    (by norm_num) (Dvd.dvd.add (three_dvd_N hb) (by norm_num)) hd hc
  have hY : 7 ^ e % 3 ≠ 0 := not3_pow (by norm_num) (by norm_num)
  rcases (show b = 1 ∨ 2 ≤ b by omega) with rfl | hb2
  · obtain ⟨j, hj⟩ := adic3_p_b1 hY (show 3 * 2 ^ a + 3 = 3 ^ k * 7 ^ e by rw [← hke]; ring)
    exact (Vp7 he hj).elim
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
    have h1 := adic3_p hY (show 9 * (2 ^ a * 3 ^ b) + 3 = 3 ^ k * 7 ^ e by rw [← hke]; ring)
    obtain ⟨hx, hy⟩ := SUp7 (show 2 ^ a * 3 ^ (b + 1) + 1 = 7 ^ e by rw [← h1]; ring)
    calc 2 ^ a * 3 ^ (b + 2) ≤ 2 ^ 4 * 3 ^ 2 := smooth_le hx (by omega)
      _ ≤ 1458 := by norm_num

lemma Lp3_13 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 13 ∣ 2 ^ a * 3 ^ b + 3)
    (hc : (2 ^ a * 3 ^ b + 3).primeFactors.card = 2) : 2 ^ a * 3 ^ b ≤ 1458 := by
  obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_three (by norm_num : Nat.Prime 13)
    (by norm_num) (Dvd.dvd.add (three_dvd_N hb) (by norm_num)) hd hc
  have hY : 13 ^ e % 3 ≠ 0 := not3_pow (by norm_num) (by norm_num)
  rcases (show b = 1 ∨ 2 ≤ b by omega) with rfl | hb2
  · obtain ⟨j, hj⟩ := adic3_p_b1 hY (show 3 * 2 ^ a + 3 = 3 ^ k * 13 ^ e by rw [← hke]; ring)
    exact (Vp13 he hj).elim
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
    have h1 := adic3_p hY (show 9 * (2 ^ a * 3 ^ b) + 3 = 3 ^ k * 13 ^ e by rw [← hke]; ring)
    obtain ⟨hx, hy⟩ := SUp13 (show 2 ^ a * 3 ^ (b + 1) + 1 = 13 ^ e by rw [← h1]; ring)
    calc 2 ^ a * 3 ^ (b + 2) ≤ 2 ^ 2 * 3 ^ 2 := smooth_le hx (by omega)
      _ ≤ 1458 := by norm_num

lemma Lm3_5 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 5 ∣ 2 ^ a * 3 ^ b - 3)
    (hc : (2 ^ a * 3 ^ b - 3).primeFactors.card = 2) : 2 ^ a * 3 ^ b ≤ 1458 := by
  have h6 := N_ge ha hb
  obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_three (by norm_num : Nat.Prime 5)
    (by norm_num) (Nat.dvd_sub (three_dvd_N hb) (dvd_refl 3)) hd hc
  have hY : 5 ^ e % 3 ≠ 0 := not3_pow (by norm_num) (by norm_num)
  rcases (show b = 1 ∨ 2 ≤ b by omega) with rfl | hb2
  · obtain ⟨j, hj⟩ := adic3_m_b1 hY (show 3 * 2 ^ a = 3 ^ k * 5 ^ e + 3 by omega)
    calc 2 ^ a * 3 ^ 1 ≤ 2 ^ 4 * 3 ^ 1 := smooth_le (Vm5 he hj) le_rfl
      _ ≤ 1458 := by norm_num
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
    have h1 := adic3_m hY (show 9 * (2 ^ a * 3 ^ b) = 3 ^ k * 5 ^ e + 3 by
      rw [show 9 * (2 ^ a * 3 ^ b) = 2 ^ a * 3 ^ (b + 2) by ring]; omega)
    obtain ⟨hx, hy⟩ := eqB (show 5 ^ e + 1 = 2 ^ a * 3 ^ (b + 1) by rw [← h1]; ring)
    calc 2 ^ a * 3 ^ (b + 2) ≤ 2 ^ 1 * 3 ^ 2 := smooth_le hx (by omega)
      _ ≤ 1458 := by norm_num

lemma Lm3_13 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 13 ∣ 2 ^ a * 3 ^ b - 3)
    (hc : (2 ^ a * 3 ^ b - 3).primeFactors.card = 2) : 2 ^ a * 3 ^ b ≤ 1458 := by
  have h6 := N_ge ha hb
  obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_three (by norm_num : Nat.Prime 13)
    (by norm_num) (Nat.dvd_sub (three_dvd_N hb) (dvd_refl 3)) hd hc
  have hY : 13 ^ e % 3 ≠ 0 := not3_pow (by norm_num) (by norm_num)
  rcases (show b = 1 ∨ 2 ≤ b by omega) with rfl | hb2
  · obtain ⟨j, hj⟩ := adic3_m_b1 hY (show 3 * 2 ^ a = 3 ^ k * 13 ^ e + 3 by omega)
    exact (Vm13 he hj).elim
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
    have h1 := adic3_m hY (show 9 * (2 ^ a * 3 ^ b) = 3 ^ k * 13 ^ e + 3 by
      rw [show 9 * (2 ^ a * 3 ^ b) = 2 ^ a * 3 ^ (b + 2) by ring]; omega)
    exact (SUm13 (by omega) (show 13 ^ e + 1 = 2 ^ a * 3 ^ (b + 1) by rw [← h1]; ring)).elim

/-! The family `a = 1`, `N = 2 * 3^b`, needs the prime 11 in three classes of `b mod 60`. -/

lemma L11p4 {b : ℕ} (hb : 1 ≤ b) (hd : 11 ∣ 2 ^ 1 * 3 ^ b + 4)
    (hc : (2 ^ 1 * 3 ^ b + 4).primeFactors.card = 2) : 2 ^ 1 * 3 ^ b ≤ 1458 := by
  obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two (by norm_num : Nat.Prime 11)
    (by norm_num) (Dvd.dvd.add (two_dvd_N le_rfl) (by norm_num)) hd hc
  have := Up11 (adic_p4_a1 (odd_pow_two (by norm_num)) (odd_pow_two (by norm_num))
    (show 2 * 3 ^ b + 4 = 2 ^ k * 11 ^ e by rw [← hke]; ring))
  calc 2 ^ 1 * 3 ^ b ≤ 2 ^ 1 * 3 ^ 2 := smooth_le le_rfl this
    _ ≤ 1458 := by norm_num

lemma L11p3 {b : ℕ} (hb : 1 ≤ b) (hd : 11 ∣ 2 ^ 1 * 3 ^ b + 3)
    (hc : (2 ^ 1 * 3 ^ b + 3).primeFactors.card = 2) : 2 ^ 1 * 3 ^ b ≤ 1458 := by
  rcases (show b = 1 ∨ 2 ≤ b by omega) with rfl | hb2
  · norm_num
  obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_three (by norm_num : Nat.Prime 11)
    (by norm_num) (Dvd.dvd.add (three_dvd_N hb) (by norm_num)) hd hc
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
  have h1 := adic3_p (not3_pow (by norm_num : Nat.Prime 11) (by norm_num))
    (show 9 * (2 ^ 1 * 3 ^ b) + 3 = 3 ^ k * 11 ^ e by rw [← hke]; ring)
  exact (SUp11 le_rfl (show 2 ^ 1 * 3 ^ (b + 1) + 1 = 11 ^ e by rw [← h1]; ring)).elim

lemma L11m2 {b : ℕ} (hb : 1 ≤ b) (hd : 11 ∣ 2 ^ 1 * 3 ^ b - 2)
    (hc : (2 ^ 1 * 3 ^ b - 2).primeFactors.card = 2) : 2 ^ 1 * 3 ^ b ≤ 1458 := by
  have h6 := N_ge le_rfl hb
  obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two (by norm_num : Nat.Prime 11)
    (by norm_num) (Nat.dvd_sub (two_dvd_N le_rfl) (dvd_refl 2)) hd hc
  obtain ⟨j, hj⟩ := adic_m2_a1 (odd_pow_two (by norm_num))
    (show 2 * 3 ^ b = 2 ^ k * 11 ^ e + 2 by omega)
  calc 2 ^ 1 * 3 ^ b ≤ 2 ^ 1 * 3 ^ 6 := smooth_le le_rfl (Tm11 he hj)
    _ ≤ 1458 := by norm_num

/-! ## Special cases: two small primes in a free term, and algebraic factorizations -/

lemma D713 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h7 : 7 ∣ 2 ^ a * 3 ^ b - 1)
    (h13 : 13 ∣ 2 ^ a * 3 ^ b - 1) (hc : (2 ^ a * 3 ^ b - 1).primeFactors.card = 2) : False := by
  obtain ⟨e, f, -, -, hef⟩ := two_prime_form (by norm_num : Nat.Prime 7)
    (by norm_num : Nat.Prime 13) (by norm_num) h7 h13 hc
  have h3 := three_dvd_N (a := a) hb
  have h6 := N_ge ha hb
  have hm : 7 ^ e * 13 ^ f % 3 = 1 := by
    rw [Nat.mul_mod, Nat.pow_mod, Nat.pow_mod 13]; norm_num
  omega

lemma smooth_dvd {d a b : ℕ} (h : d ∣ 2 ^ a * 3 ^ b) : ∃ i j : ℕ, d = 2 ^ i * 3 ^ j := by
  obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.mp h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hy
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hz
  exact ⟨i, j, rfl⟩

/-- Consecutive 3-smooth numbers are at most 8 and 9. -/
lemma consec {s t u v : ℕ} (h : 2 ^ s * 3 ^ t + 1 = 2 ^ u * 3 ^ v) : 2 ^ s * 3 ^ t ≤ 8 := by
  have hsu : s = 0 ∨ u = 0 := by
    by_contra hh
    push Not at hh
    have h1 : 2 ∣ 2 ^ s * 3 ^ t := Dvd.dvd.mul_right (dvd_pow_self 2 hh.1) _
    have h2 : 2 ∣ 2 ^ u * 3 ^ v := Dvd.dvd.mul_right (dvd_pow_self 2 hh.2) _
    omega
  have htv : t = 0 ∨ v = 0 := by
    by_contra hh
    push Not at hh
    have h1 : 3 ∣ 2 ^ s * 3 ^ t := Dvd.dvd.mul_left (dvd_pow_self 3 hh.1) _
    have h2 : 3 ∣ 2 ^ u * 3 ^ v := Dvd.dvd.mul_left (dvd_pow_self 3 hh.2) _
    omega
  rcases hsu with rfl | rfl <;> rcases htv with rfl | rfl
  · simp
  · simp at h
    have := catalan_a h
    interval_cases t <;> simp
  · simp at h
    have h9 : 3 ^ v ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (catalan_b h)
    simp
    omega
  · simp at h

/-- 3-smooth numbers two apart are small. -/
lemma two_apart {i j k l : ℕ} (h : 2 ^ i * 3 ^ j + 2 = 2 ^ k * 3 ^ l) : 2 ^ i * 3 ^ j ≤ 16 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have h3j : 3 ^ j % 2 = 1 := odd_pow_two (by norm_num)
    have h3l : 3 ^ l % 2 = 1 := odd_pow_two (by norm_num)
    have hk : k = 0 := by
      by_contra hk
      have : 2 ∣ 2 ^ k * 3 ^ l := Dvd.dvd.mul_right (dvd_pow_self 2 hk) _
      simp at h
      omega
    subst hk
    simp at h
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · exfalso
      have d1 : 3 ∣ 3 ^ j := dvd_pow_self 3 (by omega)
      rcases Nat.eq_zero_or_pos l with rfl | hl
      · simp at h
      · have d2 : 3 ∣ 3 ^ l := dvd_pow_self 3 (by omega)
        omega
  · have h3j : 3 ^ j % 2 = 1 := odd_pow_two (by norm_num)
    have h3l : 3 ^ l % 2 = 1 := odd_pow_two (by norm_num)
    have hk : 1 ≤ k := by
      by_contra hk
      push Not at hk
      interval_cases k
      have : 2 ∣ 2 ^ i * 3 ^ j := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
      simp at h
      omega
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h' : 2 ^ i * 3 ^ j + 1 = 2 ^ k * 3 ^ l := by
      have : 2 * (2 ^ i * 3 ^ j + 1) = 2 * (2 ^ k * 3 ^ l) := by
        rw [pow_succ, pow_succ] at h; linarith
      omega
    have := consec h'
    calc 2 ^ (i + 1) * 3 ^ j = 2 * (2 ^ i * 3 ^ j) := by ring
      _ ≤ 16 := by omega

/-- `N + 1 = 5^e 7^f` is impossible when `8 ∣ N`: both exponents are even, so `N = X^2 - 1`. -/
lemma D57 {a b : ℕ} (ha : 3 ≤ a) (h5 : 5 ∣ 2 ^ a * 3 ^ b + 1) (h7 : 7 ∣ 2 ^ a * 3 ^ b + 1)
    (hc : (2 ^ a * 3 ^ b + 1).primeFactors.card = 2) : False := by
  obtain ⟨e, f, he, hf, hef⟩ := two_prime_form (by norm_num : Nat.Prime 5)
    (by norm_num : Nat.Prime 7) (by norm_num) h5 h7 hc
  have h8 : 8 ∣ 2 ^ a * 3 ^ b := by
    have := pow_dvd_pow 2 ha
    exact Dvd.dvd.mul_right (by simpa using this) _
  have m8 : 5 ^ e * 7 ^ f % 8 = 1 := by omega
  rw [Nat.mul_mod, pow_mod_period 5 2 8 e (by norm_num), pow_mod_period 7 2 8 f (by norm_num)]
    at m8
  have he2 : e % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hf2 : f % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hev : e % 2 = 0 ∧ f % 2 = 0 := by
    interval_cases (e % 2) <;> interval_cases (f % 2) <;> simp_all
  obtain ⟨e, rfl⟩ : ∃ e', e = 2 * e' := ⟨e / 2, by omega⟩
  obtain ⟨f, rfl⟩ : ∃ f', f = 2 * f' := ⟨f / 2, by omega⟩
  have hX5 : 5 ≤ 5 ^ e := by
    calc 5 = 5 ^ 1 := by norm_num
      _ ≤ 5 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX7 : 7 ≤ 7 ^ f := by
    calc 7 = 7 ^ 1 := by norm_num
      _ ≤ 7 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX : 35 ≤ 5 ^ e * 7 ^ f := by nlinarith
  have hsq : 2 ^ a * 3 ^ b + 1 = (5 ^ e * 7 ^ f) * (5 ^ e * 7 ^ f) := by rw [hef]; ring
  obtain ⟨X, hXdef⟩ : ∃ X, X = 5 ^ e * 7 ^ f := ⟨_, rfl⟩
  rw [← hXdef] at hsq hX
  have hN : 2 ^ a * 3 ^ b = (X - 1) * (X + 1) := by
    have h1 : 1 ≤ X := by omega
    zify [h1] at hsq ⊢
    linear_combination hsq
  have hd1 : X - 1 ∣ 2 ^ a * 3 ^ b := hN ▸ dvd_mul_right _ _
  have hd2 : X + 1 ∣ 2 ^ a * 3 ^ b := hN ▸ dvd_mul_left _ _
  obtain ⟨i, j, hij⟩ := smooth_dvd hd1
  obtain ⟨k, l, hkl⟩ := smooth_dvd hd2
  have := two_apart (show 2 ^ i * 3 ^ j + 2 = 2 ^ k * 3 ^ l by omega)
  omega

/-- The family `a = 1`: `2 * 3^b + 1 = 5^e 7^f` in the two classes of `b mod 60` that remain. -/
lemma D57a1 {b : ℕ} (hb : b % 60 = 31 ∨ b % 60 = 43) (h5 : 5 ∣ 2 ^ 1 * 3 ^ b + 1)
    (h7 : 7 ∣ 2 ^ 1 * 3 ^ b + 1) (hc : (2 ^ 1 * 3 ^ b + 1).primeFactors.card = 2) : False := by
  obtain ⟨e, f, he, hf, hef⟩ := two_prime_form (by norm_num : Nat.Prime 5)
    (by norm_num : Nat.Prime 7) (by norm_num) h5 h7 hc
  clear hc h5 h7
  rcases hb with hb | hb
  · have A8 : 5 ^ e * 7 ^ f % 8 = 7 := by
      rw [← hef, Nat.add_mod, Nat.mul_mod, pow_mod_period 3 2 8 b (by norm_num),
        show b % 2 = 1 by omega]
      norm_num
    have A9 : 5 ^ e * 7 ^ f % 9 = 1 := by
      have h9 : 3 ^ 2 ∣ 3 ^ b := pow_dvd_pow 3 (show 2 ≤ b by omega)
      have m9 : 3 ^ b % 9 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using h9)
      rw [← hef, Nat.add_mod, Nat.mul_mod, m9]
      norm_num
    have A31 : 5 ^ e * 7 ^ f % 31 = 7 := by
      rw [← hef, Nat.add_mod, Nat.mul_mod, pow_mod_period 3 30 31 b (by norm_num),
        show b % 30 = 1 by omega]
      norm_num
    rw [Nat.mul_mod, pow_mod_period 5 6 8 e (by norm_num), pow_mod_period 7 30 8 f (by norm_num)]
      at A8
    rw [Nat.mul_mod, pow_mod_period 5 6 9 e (by norm_num), pow_mod_period 7 30 9 f (by norm_num)]
      at A9
    rw [Nat.mul_mod, pow_mod_period 5 6 31 e (by norm_num),
      pow_mod_period 7 30 31 f (by norm_num)] at A31
    have key : ∀ r < 6, ∀ s < 30, ¬ ((5 ^ r % 8) * (7 ^ s % 8) % 8 = 7 ∧
        (5 ^ r % 9) * (7 ^ s % 9) % 9 = 1 ∧ (5 ^ r % 31) * (7 ^ s % 31) % 31 = 7) := by
      decide
    exact key _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num)) ⟨A8, A9, A31⟩
  · have A11 : 5 ^ e * 7 ^ f % 11 = 0 := by
      rw [← hef, Nat.add_mod, Nat.mul_mod, pow_mod_period 3 5 11 b (by norm_num),
        show b % 5 = 3 by omega]
      norm_num
    have h11 : 11 ∣ 5 ^ e * 7 ^ f := Nat.dvd_of_mod_eq_zero A11
    rcases (Nat.Prime.dvd_mul (by norm_num)).1 h11 with h | h <;>
      have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 11) h <;> norm_num at this

/-- A product of two coprime factors with exactly two prime factors in total: each factor is
a prime power. -/
lemma pp_of_coprime_mul {x y n : ℕ} (hxy : x * y = n) (hcop : Nat.Coprime x y) (hx : 1 < x)
    (hy : 1 < y) (hn : n.primeFactors.card = 2) : x.primeFactors.card = 1 := by
  have hU : n.primeFactors = x.primeFactors ∪ y.primeFactors := by
    rw [← hxy, Nat.primeFactors_mul (by omega) (by omega)]
  have hD : Disjoint x.primeFactors y.primeFactors := Nat.Coprime.disjoint_primeFactors hcop
  have h1 := (Nat.nonempty_primeFactors.2 hx).card_pos
  have h2 := (Nat.nonempty_primeFactors.2 hy).card_pos
  have := Finset.card_union_of_disjoint hD
  rw [← hU, hn] at this
  omega

lemma pow_of_card_one {x p : ℕ} (hp : p.Prime) (hdvd : p ∣ x) (hx : x ≠ 0)
    (hc : x.primeFactors.card = 1) : x = p ^ x.factorization p := by
  have hmem : p ∈ x.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hdvd, hx⟩
  obtain ⟨q, hq⟩ := Finset.card_eq_one.1 hc
  have hpq : x.primeFactors = {p} := by
    rw [hq] at hmem ⊢; rw [Finset.mem_singleton.1 hmem]
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hx]
  rw [Finsupp.prod, Nat.support_factorization, hpq, Finset.prod_singleton]

/-- The class `a ≡ 10`, `b ≡ 4 (mod 12)`: `N = v^2`, so `N - 1 = (v - 1)(v + 1)` with
`v - 1` a prime power divisible by 7, while `3 ∣ v`. -/
lemma F104 {a b : ℕ} (ha : a % 12 = 10) (hb : b % 12 = 4)
    (hc : (2 ^ a * 3 ^ b - 1).primeFactors.card = 2) : False := by
  obtain ⟨v, hv⟩ : ∃ v, v = 2 ^ (a / 2) * 3 ^ (b / 2) := ⟨_, rfl⟩
  have hN : 2 ^ a * 3 ^ b = v * v := by
    have e1 : 2 ^ a = 2 ^ (a / 2) * 2 ^ (a / 2) := by rw [← pow_add]; congr 1; omega
    have e2 : 3 ^ b = 3 ^ (b / 2) * 3 ^ (b / 2) := by rw [← pow_add]; congr 1; omega
    rw [e1, e2, hv]; ring
  have hv3 : 3 ∣ v := hv ▸ Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
  have hv2 : 2 ∣ v := hv ▸ Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  have hv0 : v ≠ 0 := by rw [hv]; positivity
  have hv7 : v % 7 = 1 := by
    rw [hv, Nat.mul_mod, pow_mod_period 2 3 7 _ (by norm_num),
      pow_mod_period 3 6 7 _ (by norm_num), show a / 2 % 3 = 2 by omega,
      show b / 2 % 6 = 2 by omega]
    norm_num
  have hfac : (v - 1) * (v + 1) = 2 ^ a * 3 ^ b - 1 := by
    rw [hN]
    have h1 : 1 ≤ v := by omega
    have h2 : 1 ≤ v * v := by nlinarith
    zify [h1, h2]; ring
  have hcop : Nat.Coprime (v - 1) (v + 1) := by
    have hg1 := Nat.gcd_dvd_left (v - 1) (v + 1)
    have hg : Nat.gcd (v - 1) (v + 1) ∣ 2 := by
      have := Nat.dvd_sub (Nat.gcd_dvd_right (v - 1) (v + 1)) hg1
      rwa [show v + 1 - (v - 1) = 2 by omega] at this
    rcases (Nat.dvd_prime Nat.prime_two).1 hg with h | h
    · exact h
    · exfalso; rw [h] at hg1; omega
  have hpp := pp_of_coprime_mul hfac hcop (by omega) (by omega) hc
  have h7 : 7 ∣ v - 1 := by omega
  have hpow := pow_of_card_one (by norm_num : Nat.Prime 7) h7 (by omega) hpp
  have : (v - 1) % 3 = 1 := by rw [hpow, Nat.pow_mod]; norm_num
  omega

/-- The class `a ≡ 6`, `b ≡ 0 (mod 12)`: `N = w^3` with `w = z^2`, and
`N + 1 = (w + 1)(w^2 - w + 1)`; the factor `w + 1 = z^2 + 1` is a power of 5 or 13. -/
lemma D513 {a b : ℕ} (ha : a % 12 = 6) (hb : b % 12 = 0) (hb1 : 1 ≤ b)
    (h5 : 5 ∣ 2 ^ a * 3 ^ b + 1) (h13 : 13 ∣ 2 ^ a * 3 ^ b + 1)
    (hc : (2 ^ a * 3 ^ b + 1).primeFactors.card = 2) : False := by
  have hb12 : 12 ≤ b := by omega
  obtain ⟨w, hw⟩ : ∃ w, w = 2 ^ (a / 3) * 3 ^ (b / 3) := ⟨_, rfl⟩
  have hN : 2 ^ a * 3 ^ b = w ^ 3 := by
    have e1 : 2 ^ a = (2 ^ (a / 3)) ^ 3 := by rw [← pow_mul]; congr 1; omega
    have e2 : 3 ^ b = (3 ^ (b / 3)) ^ 3 := by rw [← pow_mul]; congr 1; omega
    rw [e1, e2, hw]; ring
  have hw3 : 3 ∣ w := hw ▸ Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
  have hw0 : w ≠ 0 := by rw [hw]; positivity
  have hw9 : 9 ≤ w := by
    have : 3 ^ 4 ≤ 3 ^ (b / 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 1 ≤ 2 ^ (a / 3) := Nat.one_le_two_pow
    rw [hw]; nlinarith
  have hle : w ≤ w ^ 2 + 1 := by nlinarith
  have hfac : (w + 1) * (w ^ 2 + 1 - w) = 2 ^ a * 3 ^ b + 1 := by
    rw [hN]; zify [hle]; ring
  have hcop : Nat.Coprime (w + 1) (w ^ 2 + 1 - w) := by
    have key : (w + 1) * (w + 1) = (w ^ 2 + 1 - w) + 3 * w := by zify [hle]; ring
    have hg1 := Nat.gcd_dvd_left (w + 1) (w ^ 2 + 1 - w)
    have hg2 := Nat.gcd_dvd_right (w + 1) (w ^ 2 + 1 - w)
    have h3w : Nat.gcd (w + 1) (w ^ 2 + 1 - w) ∣ 3 * w := by
      have := Nat.dvd_sub (Dvd.dvd.mul_right hg1 (w + 1)) hg2
      rwa [key, Nat.add_sub_cancel_left] at this
    have hcw : Nat.Coprime (Nat.gcd (w + 1) (w ^ 2 + 1 - w)) w :=
      Nat.Coprime.coprime_dvd_left hg1 (by simp)
    have h3 : Nat.gcd (w + 1) (w ^ 2 + 1 - w) ∣ 3 := hcw.dvd_of_dvd_mul_right h3w
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    · exact h
    · exfalso; rw [h] at hg1; omega
  have hC : 1 < w ^ 2 + 1 - w := by
    have : w + 1 < w ^ 2 + 1 := by nlinarith
    omega
  have hpp := pp_of_coprime_mul hfac hcop (by omega) hC hc
  obtain ⟨q, hq⟩ := Finset.card_eq_one.1 hpp
  have hqmem : q ∈ (w + 1).primeFactors := by rw [hq]; exact Finset.mem_singleton_self q
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqmem
  have hqd : q ∣ w + 1 := Nat.dvd_of_mem_primeFactors hqmem
  have hqN : q ∣ 2 ^ a * 3 ^ b + 1 := hfac ▸ Dvd.dvd.mul_right hqd _
  obtain ⟨k, e, -, -, hke⟩ := two_prime_form (by norm_num : Nat.Prime 5)
    (by norm_num : Nat.Prime 13) (by norm_num) h5 h13 hc
  have hq513 : q = 5 ∨ q = 13 := by
    rw [hke] at hqN
    rcases (Nat.Prime.dvd_mul hqp).1 hqN with h | h
    · left; exact (Nat.prime_dvd_prime_iff_eq hqp (by norm_num)).1 (hqp.dvd_of_dvd_pow h)
    · right; exact (Nat.prime_dvd_prime_iff_eq hqp (by norm_num)).1 (hqp.dvd_of_dvd_pow h)
  have hz : w = 2 ^ (a / 3) * 3 ^ (b / 3) := hw
  rcases hq513 with rfl | rfl
  · have hpow := pow_of_card_one (by norm_num : Nat.Prime 5) hqd (by omega) hpp
    have := (eqA (show 2 ^ (a / 3) * 3 ^ (b / 3) + 1 = 5 ^ (w + 1).factorization 5 by
      rw [← hz]; exact hpow)).2
    omega
  · have hpow := pow_of_card_one (by norm_num : Nat.Prime 13) hqd (by omega) hpp
    have := (SUp13 (show 2 ^ (a / 3) * 3 ^ (b / 3) + 1 = 13 ^ (w + 1).factorization 13 by
      rw [← hz]; exact hpow)).2
    omega

/-! ## The offset-3 window (H1) -/

lemma card_220 : (220 : ℕ).primeFactors.card = 3 := by
  rw [show (220 : ℕ) = 2 ^ 2 * 5 * 11 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_prime_pow (by norm_num)
    Nat.prime_two, Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  decide

/-- The offset-3 window for `N = 2^a 3^b ≤ 1458`: checked directly. -/
lemma small_H1 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hN : 2 ^ a * 3 ^ b ≤ 1458)
    (hw : ∀ i < 9, (2 ^ a * 3 ^ b - 3 + i).primeFactors.card = 2) : False := by
  have h3b : 3 ≤ 3 ^ b := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have h2a : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have ha8 : a ≤ 8 := by
    by_contra h
    have : 2 ^ 9 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ 9 * 3 ≤ 2 ^ a * 3 ^ b := Nat.mul_le_mul this h3b
    norm_num at this; omega
  have hb6 : b ≤ 6 := by
    by_contra h
    have : 3 ^ 7 ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 * 3 ^ 7 ≤ 2 ^ a * 3 ^ b := Nat.mul_le_mul h2a this
    norm_num at this; omega
  interval_cases a <;> interval_cases b <;>
  first
  | (norm_num at hN; done)
  | (have hp := not_prime_of_card_two (hw 0 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (hw 1 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (hw 2 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (hw 3 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (hw 4 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (hw 5 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (hw 6 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (hw 7 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (hw 8 (by norm_num)); norm_num at hp; done)
  | (have h' := hw 7 (by norm_num); norm_num [card_220] at h'; done)
  | (have h' := hw 1 (by norm_num); norm_num [card_322] at h'; done)

lemma Nmod {p a b ra rb : ℕ} (h2 : 2 ^ 12 % p = 1) (h3 : 3 ^ 12 % p = 1) (ha : a % 12 = ra)
    (hb : b % 12 = rb) : 2 ^ a * 3 ^ b % p = 2 ^ ra * 3 ^ rb % p := by
  rw [Nat.mul_mod, pow_mod_period 2 12 p a h2, pow_mod_period 3 12 p b h3, ha, hb, ← Nat.mul_mod]

/-- No run of nine has its multiple of 6 at offset 3. -/
theorem offset3 : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    ¬ ∀ i < 9, (2 ^ a * 3 ^ b - 3 + i).primeFactors.card = 2 := by
  intro a b ha hb hw
  have h6 := N_ge ha hb
  by_cases hsmall : 2 ^ a * 3 ^ b ≤ 1458
  · exact small_H1 ha hb hsmall hw
  push Not at hsmall
  have w0 : (2 ^ a * 3 ^ b - 3).primeFactors.card = 2 := by simpa using hw 0 (by norm_num)
  have w1 : (2 ^ a * 3 ^ b - 2).primeFactors.card = 2 := by
    have := hw 1 (by norm_num); rwa [show 2 ^ a * 3 ^ b - 3 + 1 = 2 ^ a * 3 ^ b - 2 by omega] at this
  have w2 : (2 ^ a * 3 ^ b - 1).primeFactors.card = 2 := by
    have := hw 2 (by norm_num); rwa [show 2 ^ a * 3 ^ b - 3 + 2 = 2 ^ a * 3 ^ b - 1 by omega] at this
  have w4 : (2 ^ a * 3 ^ b + 1).primeFactors.card = 2 := by
    have := hw 4 (by norm_num); rwa [show 2 ^ a * 3 ^ b - 3 + 4 = 2 ^ a * 3 ^ b + 1 by omega] at this
  have w5 : (2 ^ a * 3 ^ b + 2).primeFactors.card = 2 := by
    have := hw 5 (by norm_num); rwa [show 2 ^ a * 3 ^ b - 3 + 5 = 2 ^ a * 3 ^ b + 2 by omega] at this
  have w6 : (2 ^ a * 3 ^ b + 3).primeFactors.card = 2 := by
    have := hw 6 (by norm_num); rwa [show 2 ^ a * 3 ^ b - 3 + 6 = 2 ^ a * 3 ^ b + 3 by omega] at this
  have w7 : (2 ^ a * 3 ^ b + 4).primeFactors.card = 2 := by
    have := hw 7 (by norm_num); rwa [show 2 ^ a * 3 ^ b - 3 + 7 = 2 ^ a * 3 ^ b + 4 by omega] at this
  clear hw
  have hra : a % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hrb : b % 12 < 12 := Nat.mod_lt _ (by norm_num)
  interval_cases ha12 : a % 12 <;> interval_cases hb12 : b % 12
  · -- a % 12 = 0, b % 12 = 0
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 0, b % 12 = 1
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 0, b % 12 = 2
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_7 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 0, b % 12 = 3
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 0, b % 12 = 4
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 0, b % 12 = 5
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 0, b % 12 = 6
    have r7 := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    have r13 := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r7 r13
    exact D713 ha hb (by omega) (by omega) w2
  · -- a % 12 = 0, b % 12 = 7
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 0, b % 12 = 8
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 0, b % 12 = 9
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 0, b % 12 = 10
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_7 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 0, b % 12 = 11
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 1, b % 12 = 0
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 1, b % 12 = 1
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 1, b % 12 = 2
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 1, b % 12 = 3
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_7 ha hb (by omega) w5) (by omega)
  · -- a % 12 = 1, b % 12 = 4
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 1, b % 12 = 5
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 1, b % 12 = 6
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 1, b % 12 = 7
    have r5 := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    have r7 := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r5 r7
    have h5 : 5 ∣ 2 ^ a * 3 ^ b + 1 := by omega
    have h7 : 7 ∣ 2 ^ a * 3 ^ b + 1 := by omega
    rcases (show b % 60 = 7 ∨ b % 60 = 19 ∨ b % 60 = 31 ∨ b % 60 = 43 ∨ b % 60 = 55 by omega)
      with h60 | h60 | h60 | h60 | h60
    · have hb5 : b % 5 = 2 := by omega
      rcases (show a = 1 ∨ 3 ≤ a by omega) with rfl | ha3
      · have m11 : 3 ^ b % 11 = 9 := by
          rw [pow_mod_period 3 5 11 b (by norm_num), hb5]; norm_num
        have hd : 11 ∣ 2 ^ 1 * 3 ^ b + 4 :=
          Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, Nat.mul_mod, m11]; norm_num)
        exact absurd (L11p4 hb hd w7) (not_le.mpr hsmall)
      · exact D57 ha3 h5 h7 w4
    · have hb5 : b % 5 = 4 := by omega
      rcases (show a = 1 ∨ 3 ≤ a by omega) with rfl | ha3
      · have m11 : 3 ^ b % 11 = 4 := by
          rw [pow_mod_period 3 5 11 b (by norm_num), hb5]; norm_num
        have hd : 11 ∣ 2 ^ 1 * 3 ^ b + 3 :=
          Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, Nat.mul_mod, m11]; norm_num)
        exact absurd (L11p3 hb hd w6) (not_le.mpr hsmall)
      · exact D57 ha3 h5 h7 w4
    · rcases (show a = 1 ∨ 3 ≤ a by omega) with rfl | ha3
      · exact D57a1 (Or.inl h60) h5 h7 w4
      · exact D57 ha3 h5 h7 w4
    · rcases (show a = 1 ∨ 3 ≤ a by omega) with rfl | ha3
      · exact D57a1 (Or.inr h60) h5 h7 w4
      · exact D57 ha3 h5 h7 w4
    · have hb5 : b % 5 = 0 := by omega
      rcases (show a = 1 ∨ 3 ≤ a by omega) with rfl | ha3
      · have m11 : 3 ^ b % 11 = 1 := by
          rw [pow_mod_period 3 5 11 b (by norm_num), hb5]; norm_num
        have h1 : 1 ≤ 3 ^ b := Nat.one_le_pow _ _ (by norm_num)
        have hd : 11 ∣ 2 ^ 1 * 3 ^ b - 2 := by
          have h11 : 11 ∣ 3 ^ b - 1 := (Nat.modEq_iff_dvd' h1).1 (by unfold Nat.ModEq; rw [m11])
          have e : 2 ^ 1 * 3 ^ b - 2 = 2 * (3 ^ b - 1) := by rw [pow_one, Nat.mul_sub_one]
          rw [e]; exact Dvd.dvd.mul_left h11 2
        exact absurd (L11m2 hb hd w1) (not_le.mpr hsmall)
      · exact D57 ha3 h5 h7 w4
  · -- a % 12 = 1, b % 12 = 8
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 1, b % 12 = 9
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 1, b % 12 = 10
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 1, b % 12 = 11
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_7 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 2, b % 12 = 0
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_7 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 2, b % 12 = 1
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 2, b % 12 = 2
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 2, b % 12 = 3
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 2, b % 12 = 4
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_7 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 2, b % 12 = 5
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 2, b % 12 = 6
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 2, b % 12 = 7
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 2, b % 12 = 8
    have r := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_13 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 2, b % 12 = 9
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 2, b % 12 = 10
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 2, b % 12 = 11
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 3, b % 12 = 0
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 3, b % 12 = 1
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_7 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 3, b % 12 = 2
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 3, b % 12 = 3
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 3, b % 12 = 4
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 3, b % 12 = 5
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_7 ha hb (by omega) w5) (by omega)
  · -- a % 12 = 3, b % 12 = 6
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 3, b % 12 = 7
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 3, b % 12 = 8
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 3, b % 12 = 9
    have r5 := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    have r7 := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r5 r7
    exact D57 (by omega) (by omega) (by omega) w4
  · -- a % 12 = 3, b % 12 = 10
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 3, b % 12 = 11
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 4, b % 12 = 0
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 4, b % 12 = 1
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 4, b % 12 = 2
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_7 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 4, b % 12 = 3
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 4, b % 12 = 4
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 4, b % 12 = 5
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 4, b % 12 = 6
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_7 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 4, b % 12 = 7
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 4, b % 12 = 8
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 4, b % 12 = 9
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 4, b % 12 = 10
    have r := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_13 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 4, b % 12 = 11
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 5, b % 12 = 0
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 5, b % 12 = 1
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 5, b % 12 = 2
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 5, b % 12 = 3
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_7 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 5, b % 12 = 4
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 5, b % 12 = 5
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 5, b % 12 = 6
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 5, b % 12 = 7
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_7 ha hb (by omega) w5) (by omega)
  · -- a % 12 = 5, b % 12 = 8
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 5, b % 12 = 9
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 5, b % 12 = 10
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 5, b % 12 = 11
    have r := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_13 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 6, b % 12 = 0
    have r5 := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    have r13 := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r5 r13
    exact D513 ha12 hb12 hb (by omega) (by omega) w4
  · -- a % 12 = 6, b % 12 = 1
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 6, b % 12 = 2
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 6, b % 12 = 3
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 6, b % 12 = 4
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_7 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 6, b % 12 = 5
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 6, b % 12 = 6
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 6, b % 12 = 7
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 6, b % 12 = 8
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_7 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 6, b % 12 = 9
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 6, b % 12 = 10
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 6, b % 12 = 11
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 7, b % 12 = 0
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 7, b % 12 = 1
    have r5 := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    have r7 := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r5 r7
    exact D57 (by omega) (by omega) (by omega) w4
  · -- a % 12 = 7, b % 12 = 2
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 7, b % 12 = 3
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 7, b % 12 = 4
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 7, b % 12 = 5
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_7 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 7, b % 12 = 6
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 7, b % 12 = 7
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 7, b % 12 = 8
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 7, b % 12 = 9
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_7 ha hb (by omega) w5) (by omega)
  · -- a % 12 = 7, b % 12 = 10
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 7, b % 12 = 11
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 8, b % 12 = 0
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 8, b % 12 = 1
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 8, b % 12 = 2
    have r := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_13 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 8, b % 12 = 3
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 8, b % 12 = 4
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 8, b % 12 = 5
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 8, b % 12 = 6
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_7 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 8, b % 12 = 7
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 8, b % 12 = 8
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 8, b % 12 = 9
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 8, b % 12 = 10
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_7 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 8, b % 12 = 11
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 9, b % 12 = 0
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 9, b % 12 = 1
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 9, b % 12 = 2
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 9, b % 12 = 3
    have r5 := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    have r7 := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r5 r7
    exact D57 (by omega) (by omega) (by omega) w4
  · -- a % 12 = 9, b % 12 = 4
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 9, b % 12 = 5
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 9, b % 12 = 6
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 9, b % 12 = 7
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_7 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 9, b % 12 = 8
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 9, b % 12 = 9
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 9, b % 12 = 10
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 9, b % 12 = 11
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_7 ha hb (by omega) w5) (by omega)
  · -- a % 12 = 10, b % 12 = 0
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_7 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 10, b % 12 = 1
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 10, b % 12 = 2
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 10, b % 12 = 3
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 10, b % 12 = 4
    exact F104 ha12 hb12 w2
  · -- a % 12 = 10, b % 12 = 5
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 10, b % 12 = 6
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 10, b % 12 = 7
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 10, b % 12 = 8
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_7 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 10, b % 12 = 9
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 10, b % 12 = 10
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 10, b % 12 = 11
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 11, b % 12 = 0
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 11, b % 12 = 1
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_7 ha hb (by omega) w5) (by omega)
  · -- a % 12 = 11, b % 12 = 2
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 11, b % 12 = 3
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 11, b % 12 = 4
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 11, b % 12 = 5
    have r := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_13 ha hb (by omega) w5) (by omega)
  · -- a % 12 = 11, b % 12 = 6
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 11, b % 12 = 7
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 11, b % 12 = 8
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w0) (by omega)
  · -- a % 12 = 11, b % 12 = 9
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_7 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 11, b % 12 = 10
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w6) (by omega)
  · -- a % 12 = 11, b % 12 = 11
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp4_5 ha hb (by omega) w7) (by omega)

/-! ## The offset-5 window: extra lemmas -/

lemma Um13 {b e : ℕ} (he : 1 ≤ e) (h : 3 ^ b = 13 ^ e + 2) : False := by
  have hM : 13 ^ 1 ∣ 13 ^ e := pow_dvd_pow 13 he
  exact cert_eq (B := 13) (t := 2) (P := 3) (fun _ => 5) (by norm_num) (by norm_num) hM
    (fun q hq => Nat.Coprime.pow_right _ hq) (by decide) h

lemma Vm7 {a j e : ℕ} (he : 1 ≤ e) (h : 2 ^ a = 3 ^ j * 7 ^ e + 1) : a ≤ 6 := by
  obtain rfl : e = 1 := by
    by_contra he2
    have hM : 7 ^ 2 ∣ 3 ^ j * 7 ^ e := Dvd.dvd.mul_left (pow_dvd_pow 7 (by omega)) _
    exact cert_eq (B := 3 * 7) (t := 1) (P := 21) (fun _ => 127) (by norm_num) (by norm_num) hM
      (fun q hq => cop_mul_pow j e hq) (by decide) h
  have hj : j ≤ 2 := by
    by_contra hj
    have hM : 3 ^ 3 ∣ 3 ^ j * 7 ^ 1 := Dvd.dvd.mul_right (pow_dvd_pow 3 (by omega)) _
    exact cert_eq (B := 3 * 7) (t := 1) (P := 18) (fun _ => 19) (by norm_num) (by norm_num) hM
      (fun q hq => cop_mul_pow j 1 hq) (by decide) h
  have h4 : 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hj
  by_contra ha
  have : 2 ^ 7 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at h4 this h
  omega

lemma Lm4_5 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 5 ∣ 2 ^ a * 3 ^ b - 4)
    (hc : (2 ^ a * 3 ^ b - 4).primeFactors.card = 2) : 2 ^ a * 3 ^ b ≤ 1458 := by
  have h6 := N_ge ha hb
  obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two (by norm_num : Nat.Prime 5)
    (by norm_num) (Nat.dvd_sub (two_dvd_N ha) (by norm_num)) hd hc
  have hY : 5 ^ e % 2 = 1 := odd_pow_two (by norm_num)
  have hT : 3 ^ b % 2 = 1 := odd_pow_two (by norm_num)
  rcases (show a = 1 ∨ a = 2 ∨ 3 ≤ a by omega) with rfl | rfl | ha3
  · have := eqG (adic_m4_a1 hT hY (show 2 * 3 ^ b = 2 ^ k * 5 ^ e + 4 by omega))
    calc 2 ^ 1 * 3 ^ b ≤ 2 ^ 1 * 3 ^ 3 := smooth_le le_rfl this
      _ ≤ 1458 := by norm_num
  · obtain ⟨j, hj⟩ := adic_m4_a2 hY (show 4 * 3 ^ b = 2 ^ k * 5 ^ e + 4 by omega)
    calc 2 ^ 2 * 3 ^ b ≤ 2 ^ 2 * 3 ^ 4 := smooth_le le_rfl (eqD he hj)
      _ ≤ 1458 := by norm_num
  · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 3 := ⟨a - 3, by omega⟩
    have h1 := adic_m4_a3 hY (show 8 * (2 ^ a * 3 ^ b) = 2 ^ k * 5 ^ e + 4 by
      rw [show 8 * (2 ^ a * 3 ^ b) = 2 ^ (a + 3) * 3 ^ b by ring]; omega)
    obtain ⟨hx, hy⟩ := eqB (show 5 ^ e + 1 = 2 ^ (a + 1) * 3 ^ b by rw [← h1]; ring)
    calc 2 ^ (a + 3) * 3 ^ b ≤ 2 ^ 3 * 3 ^ 1 := smooth_le (by omega) hy
      _ ≤ 1458 := by norm_num

lemma Lm4_13 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 13 ∣ 2 ^ a * 3 ^ b - 4)
    (hc : (2 ^ a * 3 ^ b - 4).primeFactors.card = 2) : 2 ^ a * 3 ^ b ≤ 1458 := by
  have h6 := N_ge ha hb
  obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two (by norm_num : Nat.Prime 13)
    (by norm_num) (Nat.dvd_sub (two_dvd_N ha) (by norm_num)) hd hc
  have hY : 13 ^ e % 2 = 1 := odd_pow_two (by norm_num)
  have hT : 3 ^ b % 2 = 1 := odd_pow_two (by norm_num)
  rcases (show a = 1 ∨ a = 2 ∨ 3 ≤ a by omega) with rfl | rfl | ha3
  · exact (Um13 he (adic_m4_a1 hT hY (show 2 * 3 ^ b = 2 ^ k * 13 ^ e + 4 by omega))).elim
  · obtain ⟨j, hj⟩ := adic_m4_a2 hY (show 4 * 3 ^ b = 2 ^ k * 13 ^ e + 4 by omega)
    calc 2 ^ 2 * 3 ^ b ≤ 2 ^ 2 * 3 ^ 4 := smooth_le le_rfl (Tm13 he hj)
      _ ≤ 1458 := by norm_num
  · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 3 := ⟨a - 3, by omega⟩
    have h1 := adic_m4_a3 hY (show 8 * (2 ^ a * 3 ^ b) = 2 ^ k * 13 ^ e + 4 by
      rw [show 8 * (2 ^ a * 3 ^ b) = 2 ^ (a + 3) * 3 ^ b by ring]; omega)
    exact (SUm13 hb (show 13 ^ e + 1 = 2 ^ (a + 1) * 3 ^ b by rw [← h1]; ring)).elim

lemma Lm3_7 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 7 ∣ 2 ^ a * 3 ^ b - 3)
    (hc : (2 ^ a * 3 ^ b - 3).primeFactors.card = 2) : 2 ^ a * 3 ^ b ≤ 1458 := by
  have h6 := N_ge ha hb
  obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_three (by norm_num : Nat.Prime 7)
    (by norm_num) (Nat.dvd_sub (three_dvd_N hb) (dvd_refl 3)) hd hc
  have hY : 7 ^ e % 3 ≠ 0 := not3_pow (by norm_num) (by norm_num)
  rcases (show b = 1 ∨ 2 ≤ b by omega) with rfl | hb2
  · obtain ⟨j, hj⟩ := adic3_m_b1 hY (show 3 * 2 ^ a = 3 ^ k * 7 ^ e + 3 by omega)
    calc 2 ^ a * 3 ^ 1 ≤ 2 ^ 6 * 3 ^ 1 := smooth_le (Vm7 he hj) le_rfl
      _ ≤ 1458 := by norm_num
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
    have h1 := adic3_m hY (show 9 * (2 ^ a * 3 ^ b) = 3 ^ k * 7 ^ e + 3 by
      rw [show 9 * (2 ^ a * 3 ^ b) = 2 ^ a * 3 ^ (b + 2) by ring]; omega)
    exact (SUm7 (by omega) (show 7 ^ e + 1 = 2 ^ a * 3 ^ (b + 1) by rw [← h1]; ring)).elim

/-- `N - 1 = 5^e 7^f` is impossible when `8 ∣ N` and `3 ∣ N` (mod 8 forces `e` even, mod 3 forces
`e` odd). -/
lemma D57m {a b : ℕ} (ha : 3 ≤ a) (hb : 1 ≤ b) (h5 : 5 ∣ 2 ^ a * 3 ^ b - 1)
    (h7 : 7 ∣ 2 ^ a * 3 ^ b - 1) (hc : (2 ^ a * 3 ^ b - 1).primeFactors.card = 2) : False := by
  obtain ⟨e, f, -, -, hef⟩ := two_prime_form (by norm_num : Nat.Prime 5)
    (by norm_num : Nat.Prime 7) (by norm_num) h5 h7 hc
  have h8 : 8 ∣ 2 ^ a * 3 ^ b := by
    have := pow_dvd_pow 2 ha
    exact Dvd.dvd.mul_right (by simpa using this) _
  have h3 := three_dvd_N (a := a) hb
  have h6 := N_ge (by omega : 1 ≤ a) hb
  have m8 : 5 ^ e * 7 ^ f % 8 = 7 := by omega
  have m3 : 5 ^ e * 7 ^ f % 3 = 2 := by omega
  rw [Nat.mul_mod, pow_mod_period 5 2 8 e (by norm_num), pow_mod_period 7 2 8 f (by norm_num)]
    at m8
  have m7 : 7 ^ f % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  rw [Nat.mul_mod, pow_mod_period 5 2 3 e (by norm_num), m7] at m3
  have he2 : e % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hf2 : f % 2 < 2 := Nat.mod_lt _ (by norm_num)
  interval_cases (e % 2) <;> interval_cases (f % 2) <;> simp_all

/-- When `3 ∣ a` and `3 ∣ b`, `N = t^3` and `N - 1 = (t - 1)(t^2 + t + 1)`; if `5 ∣ t - 1` this
forces `t - 1` to be a power of 5. -/
lemma cube5 {a b : ℕ} (ha : a % 3 = 0) (hb : b % 3 = 0) (ha1 : 1 ≤ a) (hb1 : 1 ≤ b)
    (h5 : 2 ^ (a / 3) * 3 ^ (b / 3) % 5 = 1) (hc : (2 ^ a * 3 ^ b - 1).primeFactors.card = 2) :
    a ≤ 3 ∧ b ≤ 3 := by
  obtain ⟨t, ht⟩ : ∃ t, t = 2 ^ (a / 3) * 3 ^ (b / 3) := ⟨_, rfl⟩
  have hN : 2 ^ a * 3 ^ b = t ^ 3 := by
    have e1 : 2 ^ a = (2 ^ (a / 3)) ^ 3 := by rw [← pow_mul]; congr 1; omega
    have e2 : 3 ^ b = (3 ^ (b / 3)) ^ 3 := by rw [← pow_mul]; congr 1; omega
    rw [e1, e2, ht]; ring
  have ht3 : 3 ∣ t := ht ▸ Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
  have ht2 : 2 ∣ t := ht ▸ Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  have ht0 : t ≠ 0 := by rw [ht]; positivity
  have ht6 : 6 ≤ t := by omega
  have hfac : (t - 1) * (t ^ 2 + t + 1) = 2 ^ a * 3 ^ b - 1 := by
    rw [hN]
    have h1 : 1 ≤ t := by omega
    have h2 : 1 ≤ t ^ 3 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2]; ring
  have hcop : Nat.Coprime (t - 1) (t ^ 2 + t + 1) := by
    have key : t ^ 2 + t + 1 = (t - 1) * (t + 2) + 3 := by
      have h1 : 1 ≤ t := by omega
      zify [h1]; ring
    have hg1 := Nat.gcd_dvd_left (t - 1) (t ^ 2 + t + 1)
    have hg2 := Nat.gcd_dvd_right (t - 1) (t ^ 2 + t + 1)
    have h3 : Nat.gcd (t - 1) (t ^ 2 + t + 1) ∣ 3 := by
      have h' : Nat.gcd (t - 1) (t ^ 2 + t + 1) ∣ (t - 1) * (t + 2) + 3 - (t - 1) * (t + 2) := by
        rw [← key]; exact Nat.dvd_sub hg2 (Dvd.dvd.mul_right hg1 (t + 2))
      rwa [Nat.add_sub_cancel_left] at h'
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    · exact h
    · exfalso; rw [h] at hg1; omega
  have hpp := pp_of_coprime_mul hfac hcop (by omega) (by nlinarith) hc
  have ht5 : t % 5 = 1 := by rw [ht]; exact h5
  have h5' : 5 ∣ t - 1 := by omega
  have hpow := pow_of_card_one (by norm_num : Nat.Prime 5) h5' (by omega) hpp
  obtain ⟨hx, hy⟩ := eqB (show 5 ^ (t - 1).factorization 5 + 1 = 2 ^ (a / 3) * 3 ^ (b / 3) by
    rw [← hpow, ← ht]; omega)
  omega

/-- The offset-5 window for `N = 2^a 3^b ≤ 1458`: checked directly. -/
lemma small_H2 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hN : 2 ^ a * 3 ^ b ≤ 1458)
    (hw : ∀ i < 9, (2 ^ a * 3 ^ b - 5 + i).primeFactors.card = 2) : False := by
  have h3b : 3 ≤ 3 ^ b := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have h2a : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have ha8 : a ≤ 8 := by
    by_contra h
    have : 2 ^ 9 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ 9 * 3 ≤ 2 ^ a * 3 ^ b := Nat.mul_le_mul this h3b
    norm_num at this; omega
  have hb6 : b ≤ 6 := by
    by_contra h
    have : 3 ^ 7 ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 * 3 ^ 7 ≤ 2 ^ a * 3 ^ b := Nat.mul_le_mul h2a this
    norm_num at this; omega
  interval_cases a <;> interval_cases b <;>
  first
  | (norm_num at hN; done)
  | (have h0 := hw 0 (by norm_num); norm_num at h0; done)
  | (have hp := not_prime_of_card_two (hw 0 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (hw 1 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (hw 2 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (hw 3 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (hw 4 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (hw 5 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (hw 6 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (hw 7 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (hw 8 (by norm_num)); norm_num at hp; done)
  | (have h' := hw 3 (by norm_num); norm_num [card_322] at h'; done)

/-- The offset-5 window, outside the two classes `a ≡ b ≡ 1` and `a ≡ b ≡ 7 (mod 12)`. -/
theorem offset5 (hA : H1) (hB : H2) : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    ¬ ∀ i < 9, (2 ^ a * 3 ^ b - 5 + i).primeFactors.card = 2 := by
  intro a b ha hb hw
  have h6 := N_ge ha hb
  by_cases hsmall : 2 ^ a * 3 ^ b ≤ 1458
  · exact small_H2 ha hb hsmall hw
  push Not at hsmall
  have w1 : (2 ^ a * 3 ^ b - 4).primeFactors.card = 2 := by
    have := hw 1 (by norm_num); rwa [show 2 ^ a * 3 ^ b - 5 + 1 = 2 ^ a * 3 ^ b - 4 by omega] at this
  have w2 : (2 ^ a * 3 ^ b - 3).primeFactors.card = 2 := by
    have := hw 2 (by norm_num); rwa [show 2 ^ a * 3 ^ b - 5 + 2 = 2 ^ a * 3 ^ b - 3 by omega] at this
  have w3 : (2 ^ a * 3 ^ b - 2).primeFactors.card = 2 := by
    have := hw 3 (by norm_num); rwa [show 2 ^ a * 3 ^ b - 5 + 3 = 2 ^ a * 3 ^ b - 2 by omega] at this
  have w4 : (2 ^ a * 3 ^ b - 1).primeFactors.card = 2 := by
    have := hw 4 (by norm_num); rwa [show 2 ^ a * 3 ^ b - 5 + 4 = 2 ^ a * 3 ^ b - 1 by omega] at this
  have w7 : (2 ^ a * 3 ^ b + 2).primeFactors.card = 2 := by
    have := hw 7 (by norm_num); rwa [show 2 ^ a * 3 ^ b - 5 + 7 = 2 ^ a * 3 ^ b + 2 by omega] at this
  have w8 : (2 ^ a * 3 ^ b + 3).primeFactors.card = 2 := by
    have := hw 8 (by norm_num); rwa [show 2 ^ a * 3 ^ b - 5 + 8 = 2 ^ a * 3 ^ b + 3 by omega] at this
  have hra : a % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hrb : b % 12 < 12 := Nat.mod_lt _ (by norm_num)
  interval_cases ha12 : a % 12 <;> interval_cases hb12 : b % 12
  · -- a % 12 = 0, b % 12 = 0
    have r5 := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    have r7 := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r5 r7
    exact D57m (by omega) hb (by omega) (by omega) w4
  · -- a % 12 = 0, b % 12 = 1
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 0, b % 12 = 2
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_7 ha hb (by omega) w3) (by omega)
  · -- a % 12 = 0, b % 12 = 3
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 0, b % 12 = 4
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_7 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 0, b % 12 = 5
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 0, b % 12 = 6
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm4_5 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 0, b % 12 = 7
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 0, b % 12 = 8
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_7 ha hb (by omega) w3) (by omega)
  · -- a % 12 = 0, b % 12 = 9
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 0, b % 12 = 10
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_7 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 0, b % 12 = 11
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 1, b % 12 = 0
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 1, b % 12 = 1
    exact hA a b ha12 hb12 hw
  · -- a % 12 = 1, b % 12 = 2
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 1, b % 12 = 3
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_7 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 1, b % 12 = 4
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 1, b % 12 = 5
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_7 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 1, b % 12 = 6
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 1, b % 12 = 7
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm4_5 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 1, b % 12 = 8
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 1, b % 12 = 9
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_7 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 1, b % 12 = 10
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 1, b % 12 = 11
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm4_5 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 2, b % 12 = 0
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_7 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 2, b % 12 = 1
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 2, b % 12 = 2
    have r := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_13 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 2, b % 12 = 3
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 2, b % 12 = 4
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_7 ha hb (by omega) w3) (by omega)
  · -- a % 12 = 2, b % 12 = 5
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 2, b % 12 = 6
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_7 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 2, b % 12 = 7
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 2, b % 12 = 8
    have r := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_13 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 2, b % 12 = 9
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 2, b % 12 = 10
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_7 ha hb (by omega) w3) (by omega)
  · -- a % 12 = 2, b % 12 = 11
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 3, b % 12 = 0
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 3, b % 12 = 1
    have r := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_13 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 3, b % 12 = 2
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 3, b % 12 = 3
    have t5 : 2 ^ (a / 3) * 3 ^ (b / 3) % 5 = 1 := by
      rw [Nat.mul_mod, pow_mod_period 2 4 5 _ (by norm_num), pow_mod_period 3 4 5 _ (by norm_num),
        show a / 3 % 4 = 1 by omega, show b / 3 % 4 = 1 by omega]
      norm_num
    have := cube5 (by omega) (by omega) ha hb t5 w4
    have : 2 ^ a * 3 ^ b ≤ 2 ^ 3 * 3 ^ 3 := smooth_le this.1 this.2
    omega
  · -- a % 12 = 3, b % 12 = 4
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 3, b % 12 = 5
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_7 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 3, b % 12 = 6
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 3, b % 12 = 7
    have r := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_13 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 3, b % 12 = 8
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 3, b % 12 = 9
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm4_5 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 3, b % 12 = 10
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 3, b % 12 = 11
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_7 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 4, b % 12 = 0
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_7 ha hb (by omega) w3) (by omega)
  · -- a % 12 = 4, b % 12 = 1
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 4, b % 12 = 2
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_7 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 4, b % 12 = 3
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 4, b % 12 = 4
    have r5 := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    have r7 := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r5 r7
    exact D57m (by omega) hb (by omega) (by omega) w4
  · -- a % 12 = 4, b % 12 = 5
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 4, b % 12 = 6
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_7 ha hb (by omega) w3) (by omega)
  · -- a % 12 = 4, b % 12 = 7
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 4, b % 12 = 8
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_7 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 4, b % 12 = 9
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 4, b % 12 = 10
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm4_5 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 4, b % 12 = 11
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 5, b % 12 = 0
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 5, b % 12 = 1
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_7 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 5, b % 12 = 2
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 5, b % 12 = 3
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm4_5 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 5, b % 12 = 4
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 5, b % 12 = 5
    have r := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_13 ha hb (by omega) w3) (by omega)
  · -- a % 12 = 5, b % 12 = 6
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 5, b % 12 = 7
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_7 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 5, b % 12 = 8
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 5, b % 12 = 9
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_7 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 5, b % 12 = 10
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 5, b % 12 = 11
    have r := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_13 ha hb (by omega) w3) (by omega)
  · -- a % 12 = 6, b % 12 = 0
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm4_5 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 6, b % 12 = 1
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 6, b % 12 = 2
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_7 ha hb (by omega) w3) (by omega)
  · -- a % 12 = 6, b % 12 = 3
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 6, b % 12 = 4
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_7 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 6, b % 12 = 5
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 6, b % 12 = 6
    have r5 := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    have r7 := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r5 r7
    exact D57m (by omega) hb (by omega) (by omega) w4
  · -- a % 12 = 6, b % 12 = 7
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 6, b % 12 = 8
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_7 ha hb (by omega) w3) (by omega)
  · -- a % 12 = 6, b % 12 = 9
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 6, b % 12 = 10
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_7 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 6, b % 12 = 11
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 7, b % 12 = 0
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 7, b % 12 = 1
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm4_5 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 7, b % 12 = 2
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 7, b % 12 = 3
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_7 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 7, b % 12 = 4
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 7, b % 12 = 5
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm4_5 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 7, b % 12 = 6
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 7, b % 12 = 7
    exact hB a b ha12 hb12 hw
  · -- a % 12 = 7, b % 12 = 8
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 7, b % 12 = 9
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_7 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 7, b % 12 = 10
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 7, b % 12 = 11
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_7 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 8, b % 12 = 0
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_7 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 8, b % 12 = 1
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 8, b % 12 = 2
    have r := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_13 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 8, b % 12 = 3
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 8, b % 12 = 4
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_7 ha hb (by omega) w3) (by omega)
  · -- a % 12 = 8, b % 12 = 5
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 8, b % 12 = 6
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_7 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 8, b % 12 = 7
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 8, b % 12 = 8
    have r := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_13 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 8, b % 12 = 9
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 8, b % 12 = 10
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_7 ha hb (by omega) w3) (by omega)
  · -- a % 12 = 8, b % 12 = 11
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 9, b % 12 = 0
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 9, b % 12 = 1
    have r := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_13 ha hb (by omega) w3) (by omega)
  · -- a % 12 = 9, b % 12 = 2
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 9, b % 12 = 3
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm4_5 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 9, b % 12 = 4
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 9, b % 12 = 5
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_7 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 9, b % 12 = 6
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 9, b % 12 = 7
    have r := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_13 ha hb (by omega) w3) (by omega)
  · -- a % 12 = 9, b % 12 = 8
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 9, b % 12 = 9
    have t5 : 2 ^ (a / 3) * 3 ^ (b / 3) % 5 = 1 := by
      rw [Nat.mul_mod, pow_mod_period 2 4 5 _ (by norm_num), pow_mod_period 3 4 5 _ (by norm_num),
        show a / 3 % 4 = 3 by omega, show b / 3 % 4 = 3 by omega]
      norm_num
    have := cube5 (by omega) (by omega) ha hb t5 w4
    have : 2 ^ a * 3 ^ b ≤ 2 ^ 3 * 3 ^ 3 := smooth_le this.1 this.2
    omega
  · -- a % 12 = 9, b % 12 = 10
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 9, b % 12 = 11
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_7 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 10, b % 12 = 0
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_7 ha hb (by omega) w3) (by omega)
  · -- a % 12 = 10, b % 12 = 1
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 10, b % 12 = 2
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_7 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 10, b % 12 = 3
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 10, b % 12 = 4
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm4_5 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 10, b % 12 = 5
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 10, b % 12 = 6
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm2_7 ha hb (by omega) w3) (by omega)
  · -- a % 12 = 10, b % 12 = 7
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 10, b % 12 = 8
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_7 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 10, b % 12 = 9
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 10, b % 12 = 10
    have r := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm4_13 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 10, b % 12 = 11
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 11, b % 12 = 0
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 11, b % 12 = 1
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_7 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 11, b % 12 = 2
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 11, b % 12 = 3
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_7 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 11, b % 12 = 4
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 11, b % 12 = 5
    have r := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_13 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 11, b % 12 = 6
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 11, b % 12 = 7
    have r := (Nmod (p := 7) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_7 ha hb (by omega) w7) (by omega)
  · -- a % 12 = 11, b % 12 = 8
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm3_5 ha hb (by omega) w2) (by omega)
  · -- a % 12 = 11, b % 12 = 9
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lm4_5 ha hb (by omega) w1) (by omega)
  · -- a % 12 = 11, b % 12 = 10
    have r := (Nmod (p := 5) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp3_5 ha hb (by omega) w8) (by omega)
  · -- a % 12 = 11, b % 12 = 11
    have r := (Nmod (p := 13) (by norm_num) (by norm_num) ha12 hb12)
    norm_num at r
    exact absurd (Lp2_13 ha hb (by omega) w7) (by omega)

lemma two_mult_case (m r : ℕ) (hr : r ≤ 2) (h6 : 6 ∣ m + r)
    (hm : ∀ i < 9, (m + i).primeFactors.card = 2) : False := by
  obtain ⟨a, b, ha, hb, hab⟩ := smooth_of_six_dvd h6 (hm r (by omega))
  obtain ⟨c, d, hc, hd, hcd⟩ := smooth_of_six_dvd (by omega : 6 ∣ m + (r + 6)) (hm (r + 6) (by omega))
  have := small_of_two_mult ha hb hc hd (by rw [← hab, ← hcd]; ring)
  exact small_window m (by omega) hm

theorem reduce_core (h1 : H1) (h2 : H2) :
    ¬ ∃ m : ℕ, ∀ i < 9, (m + i).primeFactors.card = 2 := by
  rintro ⟨m, hm⟩
  have hmod : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have cen : ∀ (k : ℕ) (H : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      ¬ ∀ i < 9, (2 ^ a * 3 ^ b - k + i).primeFactors.card = 2), k < 9 → 6 ∣ m + k → False := by
    intro k H hk h6
    obtain ⟨a, b, ha, hb, hab⟩ := smooth_of_six_dvd h6 (hm k hk)
    apply H a b ha hb
    rw [← hab, Nat.add_sub_cancel]
    exact hm
  interval_cases hr : m % 6
  · exact two_mult_case m 0 (by norm_num) (by omega) hm
  · exact cen 5 (offset5 h1 h2) (by norm_num) (by omega)
  · exact cen 4 centered (by norm_num) (by omega)
  · exact cen 3 offset3 (by norm_num) (by omega)
  · exact two_mult_case m 2 (by norm_num) (by omega) hm
  · exact two_mult_case m 1 (by norm_num) (by omega) hm

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a064708.main :=
  fun h1 h2 => reduce_core h1 h2

end OMA.R_oeis_a064708_R1
