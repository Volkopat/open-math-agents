import OMAStatements.S_oeis_a079953

-- Problem: OEIS A079953, Mathar's conjecture A079953(n) = A039734(n) for n >= 2
-- Statement: statements/oeis-a079953.lean (declaration OMA.S_oeis_a079953.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Part 1 is a theorem on primes in short intervals: for every v >= 11 there is a prime q
-- with 3v/4 < q <= v (`exists_prime_interval`). It follows Chebyshev. With N = (30n)! n! and
-- D = (15n)! (10n)! (6n)!, the number N divides D lcm(1..30n), and D lcm(1..30n) divides
-- N lcm(1..5n), and N/D is between C^n / (C n^8) and C^n for C = 2^14 3^9 5^5. This gives a
-- lower and an upper bound for lcm(1..N). If (3v/4, v] has no prime, then lcm(1..v) divides
-- lcm(1..3v/4) times the product of the primes up to sqrt(v), which is at most 4^sqrt(v). The
-- bounds exclude this for v >= 16384, and a chain of 27 primes covers 11 <= v < 16384.
-- Part 2. Let p >= 17 be a prime and q0 the least prime above p/2. Part 1 with v = [2p/3]
-- gives a prime between p/2 and 2p/3, so q0 <= 2p/3 and p mod q0 = p - q0 >= p/3. A prime q
-- with p/2 < q < p and q != q0 has p mod q = p - q < p - q0. A prime q < p/2 has
-- p = q d + r with d >= 2 and r < q, so 3r < p. The primes p < 17 are checked one by one.

namespace OMA.PP

open Finset Nat Chebyshev

/-- The numerator of Chebyshev's quotient. -/
def Num (n : ℕ) : ℕ := (30 * n)! * n !

/-- The denominator of Chebyshev's quotient. -/
def Den (n : ℕ) : ℕ := (15 * n)! * (10 * n)! * (6 * n)!

lemma Num_pos (n : ℕ) : 0 < Num n := Nat.mul_pos (factorial_pos _) (factorial_pos _)

lemma Den_pos (n : ℕ) : 0 < Den n :=
  Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _)) (factorial_pos _)

lemma div_facts (n d : ℕ) :
    15 * n / d = (30 * n / d) / 2 ∧ 10 * n / d = (30 * n / d) / 3 ∧
      6 * n / d = (30 * n / d) / 5 ∧ n / d = (30 * n / d) / 30 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Nat.div_div_eq_div_mul, show 30 * n = 15 * n * 2 by ring,
      Nat.mul_div_mul_right _ _ (by norm_num)]
  · rw [Nat.div_div_eq_div_mul, show 30 * n = 10 * n * 3 by ring,
      Nat.mul_div_mul_right _ _ (by norm_num)]
  · rw [Nat.div_div_eq_div_mul, show 30 * n = 6 * n * 5 by ring,
      Nat.mul_div_mul_right _ _ (by norm_num)]
  · rw [Nat.div_div_eq_div_mul, show 30 * n = n * 30 by ring,
      Nat.mul_div_mul_right _ _ (by norm_num)]

lemma floorE_le (m : ℕ) : m + m / 30 ≤ m / 2 + m / 3 + m / 5 + 1 := by omega

lemma floorE_ge (m : ℕ) : m / 2 + m / 3 + m / 5 ≤ m + m / 30 := by omega

lemma floorE_small (m : ℕ) (h1 : 1 ≤ m) (h5 : m < 6) :
    m / 2 + m / 3 + m / 5 + 1 ≤ m + m / 30 := by omega

/-- The exponent of `p` in `lcm(1..N)` as a sum of indicators. -/
lemma log_eq_sum (p N b : ℕ) (hp : p.Prime) (hb : Nat.log p N < b) :
    Nat.log p N = ∑ i ∈ Ico 1 b, (if p ^ i ≤ N then 1 else 0) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
  by_cases hN : N = 0
  · subst hN
    have : (Ico 1 b).filter (fun i => p ^ i ≤ 0) = ∅ := by
      ext i
      simp only [mem_filter, mem_Ico, Nat.le_zero, Finset.notMem_empty, iff_false, not_and]
      intro _
      exact pow_ne_zero _ hp.ne_zero
    rw [this]
    simp
  · have : (Ico 1 b).filter (fun i => p ^ i ≤ N) = Ico 1 (Nat.log p N + 1) := by
      ext i
      simp only [mem_filter, mem_Ico]
      rw [← Nat.le_log_iff_pow_le hp.one_lt hN]
      omega
    rw [this]
    simp

lemma fact_num (p n : ℕ) (hp : p.Prime) :
    (Num n).factorization p
      = ∑ i ∈ Ico 1 (30 * n + 1), (30 * n / p ^ i + n / p ^ i) := by
  have h1 : Nat.log p (30 * n) < 30 * n + 1 := Nat.lt_succ_of_le (Nat.log_le_self _ _)
  have h2 : Nat.log p n < 30 * n + 1 :=
    Nat.lt_succ_of_le (le_trans (Nat.log_le_self _ _) (by omega))
  rw [Num, Nat.factorization_mul (factorial_ne_zero _) (factorial_ne_zero _), Finsupp.add_apply,
    factorization_factorial hp h1, factorization_factorial hp h2, ← Finset.sum_add_distrib]

lemma fact_den (p n : ℕ) (hp : p.Prime) :
    (Den n).factorization p
      = ∑ i ∈ Ico 1 (30 * n + 1), (15 * n / p ^ i + 10 * n / p ^ i + 6 * n / p ^ i) := by
  have h1 : Nat.log p (15 * n) < 30 * n + 1 :=
    Nat.lt_succ_of_le (le_trans (Nat.log_le_self _ _) (by omega))
  have h2 : Nat.log p (10 * n) < 30 * n + 1 :=
    Nat.lt_succ_of_le (le_trans (Nat.log_le_self _ _) (by omega))
  have h3 : Nat.log p (6 * n) < 30 * n + 1 :=
    Nat.lt_succ_of_le (le_trans (Nat.log_le_self _ _) (by omega))
  rw [Den, Nat.factorization_mul (Nat.mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _))
    (factorial_ne_zero _), Nat.factorization_mul (factorial_ne_zero _) (factorial_ne_zero _),
    Finsupp.add_apply, Finsupp.add_apply, factorization_factorial hp h1,
    factorization_factorial hp h2, factorization_factorial hp h3, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]

lemma fact_lcm (p N n : ℕ) (hp : p.Prime) (hN : N ≤ 30 * n) :
    (lcmUpto N).factorization p = ∑ i ∈ Ico 1 (30 * n + 1), (if p ^ i ≤ N then 1 else 0) := by
  rw [factorization_lcmUpto N hp]
  exact log_eq_sum p N _ hp (Nat.lt_succ_of_le (le_trans (Nat.log_le_self _ _) hN))

/-- Chebyshev's quotient divides `lcm(1..30n)`. -/
lemma num_dvd (n : ℕ) : Num n ∣ Den n * lcmUpto (30 * n) := by
  rw [← Nat.factorization_prime_le_iff_dvd (Num_pos n).ne'
    (Nat.mul_ne_zero (Den_pos n).ne' (lcmUpto_ne_zero _))]
  intro p hp
  rw [Nat.factorization_mul (Den_pos n).ne' (lcmUpto_ne_zero _), Finsupp.add_apply,
    fact_num p n hp, fact_den p n hp, fact_lcm p (30 * n) n hp le_rfl, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨e1, e2, e3, e4⟩ := div_facts n (p ^ i)
  rw [e1, e2, e3, e4]
  by_cases h : p ^ i ≤ 30 * n
  · rw [if_pos h]
    exact floorE_le _
  · rw [if_neg h, Nat.div_eq_of_lt (not_le.mp h)]

/-- The prime powers between `5n` and `30n` divide Chebyshev's quotient. -/
lemma den_dvd (n : ℕ) : Den n * lcmUpto (30 * n) ∣ Num n * lcmUpto (5 * n) := by
  rw [← Nat.factorization_prime_le_iff_dvd
    (Nat.mul_ne_zero (Den_pos n).ne' (lcmUpto_ne_zero _))
    (Nat.mul_ne_zero (Num_pos n).ne' (lcmUpto_ne_zero _))]
  intro p hp
  rw [Nat.factorization_mul (Den_pos n).ne' (lcmUpto_ne_zero _),
    Nat.factorization_mul (Num_pos n).ne' (lcmUpto_ne_zero _), Finsupp.add_apply,
    Finsupp.add_apply, fact_num p n hp, fact_den p n hp, fact_lcm p (30 * n) n hp le_rfl,
    fact_lcm p (5 * n) n hp (by omega), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨e1, e2, e3, e4⟩ := div_facts n (p ^ i)
  rw [e1, e2, e3, e4]
  have hpos : 0 < p ^ i := pow_pos hp.pos i
  by_cases h5 : p ^ i ≤ 5 * n
  · rw [if_pos h5, if_pos (by omega)]
    have := floorE_ge (30 * n / p ^ i)
    omega
  · rw [if_neg h5]
    by_cases h30 : p ^ i ≤ 30 * n
    · rw [if_pos h30]
      have h1 : 1 ≤ 30 * n / p ^ i := (Nat.one_le_div_iff hpos).mpr h30
      have h6 : 30 * n / p ^ i < 6 := by
        rw [Nat.div_lt_iff_lt_mul hpos]
        omega
      have := floorE_small _ h1 h6
      omega
    · rw [if_neg h30, Nat.div_eq_of_lt (not_le.mp h30)]

/-- Chebyshev's constant `2^14 * 3^9 * 5^5`. -/
def Cst : ℕ := 1007769600000

/-- The eight factors `30 n + a` with `a` coprime to 30. -/
def PA (n : ℕ) : ℕ :=
  (30 * n + 1) * (30 * n + 7) * (30 * n + 11) * (30 * n + 13) * (30 * n + 17) * (30 * n + 19)
    * (30 * n + 23) * (30 * n + 29)

/-- The eight factors `30 n + b` with `b` divisible by two or more of 2, 3, 5. -/
def PB (n : ℕ) : ℕ :=
  (30 * n + 6) * (30 * n + 10) * (30 * n + 12) * (30 * n + 15) * (30 * n + 18) * (30 * n + 20)
    * (30 * n + 24) * (30 * n + 30)

lemma PB_pos (n : ℕ) : 0 < PB n := by
  unfold PB
  positivity

lemma key_identity (n : ℕ) :
    (30 * n + 1).ascFactorial 30 * (n + 1) * PB n
      = Cst * ((15 * n + 1).ascFactorial 15 * (10 * n + 1).ascFactorial 10
          * (6 * n + 1).ascFactorial 6) * PA n := by
  simp only [Nat.ascFactorial_succ, Nat.ascFactorial_zero, PA, PB, Cst]
  ring

lemma PA_le_PB (n : ℕ) : PA n ≤ PB n := by
  unfold PA PB
  gcongr <;> omega

lemma PB_le_PA (n : ℕ) : PB n * n ^ 8 ≤ PA n * (n + 1) ^ 8 := by
  have h1 : n * (30 * n + 6) ≤ (n + 1) * (30 * n + 1) := by nlinarith
  have h2 : n * (30 * n + 10) ≤ (n + 1) * (30 * n + 7) := by nlinarith
  have h3 : n * (30 * n + 12) ≤ (n + 1) * (30 * n + 11) := by nlinarith
  have h4 : n * (30 * n + 15) ≤ (n + 1) * (30 * n + 13) := by nlinarith
  have h5 : n * (30 * n + 18) ≤ (n + 1) * (30 * n + 17) := by nlinarith
  have h6 : n * (30 * n + 20) ≤ (n + 1) * (30 * n + 19) := by nlinarith
  have h7 : n * (30 * n + 24) ≤ (n + 1) * (30 * n + 23) := by nlinarith
  have h8 : n * (30 * n + 30) ≤ (n + 1) * (30 * n + 29) := by nlinarith
  calc PB n * n ^ 8
      = (n * (30 * n + 6)) * (n * (30 * n + 10)) * (n * (30 * n + 12)) * (n * (30 * n + 15))
        * (n * (30 * n + 18)) * (n * (30 * n + 20)) * (n * (30 * n + 24))
        * (n * (30 * n + 30)) := by
        unfold PB
        ring
    _ ≤ ((n + 1) * (30 * n + 1)) * ((n + 1) * (30 * n + 7)) * ((n + 1) * (30 * n + 11))
        * ((n + 1) * (30 * n + 13)) * ((n + 1) * (30 * n + 17)) * ((n + 1) * (30 * n + 19))
        * ((n + 1) * (30 * n + 23)) * ((n + 1) * (30 * n + 29)) := by
        gcongr
    _ = PA n * (n + 1) ^ 8 := by
        unfold PA
        ring

lemma Num_succ (n : ℕ) : Num (n + 1) = Num n * ((30 * n + 1).ascFactorial 30 * (n + 1)) := by
  unfold Num
  rw [show 30 * (n + 1) = 30 * n + 30 by ring, ← Nat.factorial_mul_ascFactorial (30 * n) 30,
    Nat.factorial_succ]
  ring

lemma Den_succ (n : ℕ) :
    Den (n + 1) = Den n * ((15 * n + 1).ascFactorial 15 * (10 * n + 1).ascFactorial 10
      * (6 * n + 1).ascFactorial 6) := by
  unfold Den
  rw [show 15 * (n + 1) = 15 * n + 15 by ring, show 10 * (n + 1) = 10 * n + 10 by ring,
    show 6 * (n + 1) = 6 * n + 6 by ring, ← Nat.factorial_mul_ascFactorial (15 * n) 15,
    ← Nat.factorial_mul_ascFactorial (10 * n) 10, ← Nat.factorial_mul_ascFactorial (6 * n) 6]
  ring

/-- The upper bound for Chebyshev's quotient. -/
lemma num_le (n : ℕ) : Num n ≤ Cst ^ n * Den n := by
  induction n with
  | zero => simp [Num, Den]
  | succ n ih =>
    rw [Num_succ, Den_succ]
    set X := (30 * n + 1).ascFactorial 30 * (n + 1) with hX
    set Y := (15 * n + 1).ascFactorial 15 * (10 * n + 1).ascFactorial 10
      * (6 * n + 1).ascFactorial 6 with hY
    have hk : X * PB n = Cst * Y * PA n := key_identity n
    have hXY : X ≤ Cst * Y := by
      have : X * PB n ≤ Cst * Y * PB n := by
        rw [hk]
        exact Nat.mul_le_mul_left _ (PA_le_PB n)
      exact Nat.le_of_mul_le_mul_right this (PB_pos n)
    calc Num n * X ≤ (Cst ^ n * Den n) * (Cst * Y) := Nat.mul_le_mul ih hXY
      _ = Cst ^ (n + 1) * (Den n * Y) := by ring

/-- The lower bound for Chebyshev's quotient. -/
lemma num_ge (n : ℕ) (hn : 1 ≤ n) : Cst ^ n * Den n ≤ Num n * n ^ 8 * Cst := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h : Den 1 ≤ Num 1 := by
      unfold Den Num
      decide
    calc Cst ^ 1 * Den 1 = Den 1 * Cst := by ring
      _ ≤ Num 1 * Cst := Nat.mul_le_mul_right _ h
      _ = Num 1 * 1 ^ 8 * Cst := by ring
  | succ n hn ih =>
    rw [Num_succ, Den_succ]
    set X := (30 * n + 1).ascFactorial 30 * (n + 1) with hX
    set Y := (15 * n + 1).ascFactorial 15 * (10 * n + 1).ascFactorial 10
      * (6 * n + 1).ascFactorial 6 with hY
    have hk : X * PB n = Cst * Y * PA n := key_identity n
    -- `Cst * Y * n^8 ≤ X * (n+1)^8`
    have hYX : Cst * Y * n ^ 8 ≤ X * (n + 1) ^ 8 := by
      have : Cst * Y * n ^ 8 * PB n ≤ X * (n + 1) ^ 8 * PB n := by
        calc Cst * Y * n ^ 8 * PB n = Cst * Y * (PB n * n ^ 8) := by ring
          _ ≤ Cst * Y * (PA n * (n + 1) ^ 8) := Nat.mul_le_mul_left _ (PB_le_PA n)
          _ = Cst * Y * PA n * (n + 1) ^ 8 := by ring
          _ = X * PB n * (n + 1) ^ 8 := by rw [hk]
          _ = X * (n + 1) ^ 8 * PB n := by ring
      exact Nat.le_of_mul_le_mul_right this (PB_pos n)
    calc Cst ^ (n + 1) * (Den n * Y) = (Cst ^ n * Den n) * (Cst * Y) := by ring
      _ ≤ (Num n * n ^ 8 * Cst) * (Cst * Y) := Nat.mul_le_mul_right _ ih
      _ = Num n * Cst * (Cst * Y * n ^ 8) := by ring
      _ ≤ Num n * Cst * (X * (n + 1) ^ 8) := Nat.mul_le_mul_left _ hYX
      _ = Num n * X * (n + 1) ^ 8 * Cst := by ring

lemma lcm_mono {N M : ℕ} (h : N ≤ M) : lcmUpto N ≤ lcmUpto M := by
  apply Nat.le_of_dvd (lcmUpto_pos M)
  unfold lcmUpto
  exact Finset.lcm_mono (Finset.Icc_subset_Icc_right h)

/-- One step of the upper bound. -/
lemma lcm_step (n : ℕ) : lcmUpto (30 * n) ≤ Cst ^ n * lcmUpto (5 * n) := by
  have h1 : Den n * lcmUpto (30 * n) ≤ Num n * lcmUpto (5 * n) :=
    Nat.le_of_dvd (Nat.mul_pos (Num_pos n) (lcmUpto_pos _)) (den_dvd n)
  have h2 : Den n * lcmUpto (30 * n) ≤ Den n * (Cst ^ n * lcmUpto (5 * n)) := by
    calc Den n * lcmUpto (30 * n) ≤ Num n * lcmUpto (5 * n) := h1
      _ ≤ (Cst ^ n * Den n) * lcmUpto (5 * n) := Nat.mul_le_mul_right _ (num_le n)
      _ = Den n * (Cst ^ n * lcmUpto (5 * n)) := by ring
  exact Nat.le_of_mul_le_mul_left h2 (Den_pos n)

/-- The lower bound for `lcm(1..30n)`. -/
lemma lcm_lower (n : ℕ) (hn : 1 ≤ n) : Cst ^ n ≤ lcmUpto (30 * n) * n ^ 8 * Cst := by
  have h1 : Num n ≤ Den n * lcmUpto (30 * n) :=
    Nat.le_of_dvd (Nat.mul_pos (Den_pos n) (lcmUpto_pos _)) (num_dvd n)
  have h2 : Den n * Cst ^ n ≤ Den n * (lcmUpto (30 * n) * n ^ 8 * Cst) := by
    calc Den n * Cst ^ n = Cst ^ n * Den n := by ring
      _ ≤ Num n * n ^ 8 * Cst := num_ge n hn
      _ ≤ (Den n * lcmUpto (30 * n)) * n ^ 8 * Cst := by gcongr
      _ = Den n * (lcmUpto (30 * n) * n ^ 8 * Cst) := by ring
  exact Nat.le_of_mul_le_mul_left h2 (Den_pos n)

lemma Cst_pos : 0 < Cst := by decide

lemma one_lt_Cst : 1 < Cst := by decide

lemma lcm14 : lcmUpto 14 ≤ Cst := by
  unfold lcmUpto Cst
  decide

/-- The upper bound for `lcm(1..N)`. -/
lemma lcm_upper (N : ℕ) : lcmUpto N ^ 25 ≤ Cst ^ (N + 30 * Nat.log 2 N + 25) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases hN : N < 15
    · calc lcmUpto N ^ 25 ≤ lcmUpto 14 ^ 25 := Nat.pow_le_pow_left (lcm_mono (by omega)) 25
        _ ≤ Cst ^ 25 := Nat.pow_le_pow_left lcm14 25
        _ ≤ Cst ^ (N + 30 * Nat.log 2 N + 25) := Nat.pow_le_pow_right Cst_pos (by omega)
    · have hN15 : 15 ≤ N := by omega
      set n := N / 30 + 1 with hn
      have h1 : N ≤ 30 * n := by omega
      have h2 : 5 * n < N := by omega
      have h3 : 30 * n ≤ N + 30 := by omega
      have h4 : 5 * n ≤ N / 2 := by omega
      have hlog : Nat.log 2 (5 * n) + 1 ≤ Nat.log 2 N := by
        have h5 : Nat.log 2 (5 * n) ≤ Nat.log 2 (N / 2) := Nat.log_mono_right h4
        have h6 : Nat.log 2 (N / 2) = Nat.log 2 N - 1 := Nat.log_div_base 2 N
        have h7 : 1 ≤ Nat.log 2 N := Nat.log_pos (by norm_num) (by omega)
        omega
      have ih5 := ih (5 * n) h2
      calc lcmUpto N ^ 25 ≤ lcmUpto (30 * n) ^ 25 := Nat.pow_le_pow_left (lcm_mono h1) 25
        _ ≤ (Cst ^ n * lcmUpto (5 * n)) ^ 25 := Nat.pow_le_pow_left (lcm_step n) 25
        _ = Cst ^ (25 * n) * lcmUpto (5 * n) ^ 25 := by rw [mul_pow, ← pow_mul, mul_comm n 25]
        _ ≤ Cst ^ (25 * n) * Cst ^ (5 * n + 30 * Nat.log 2 (5 * n) + 25) :=
            Nat.mul_le_mul_left _ ih5
        _ = Cst ^ (25 * n + (5 * n + 30 * Nat.log 2 (5 * n) + 25)) := by rw [← pow_add]
        _ ≤ Cst ^ (N + 30 * Nat.log 2 N + 25) := Nat.pow_le_pow_right Cst_pos (by omega)

lemma pow_bound (L : ℕ) (hL : 13 ≤ L) : 432 * L + 962 < 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [pow_succ]
    omega

/-- For `v ≥ 8192` the least common multiple grows between `3v/4` and `v`. -/
lemma lcm_lt (v : ℕ) (hv : 8192 ≤ v) : lcmUpto (3 * v / 4) < lcmUpto v := by
  by_contra hcon
  rw [not_lt] at hcon
  set y := 3 * v / 4 with hy
  set n1 := v / 30 with hn1
  set L := Nat.log 2 v with hL
  have hv0 : v ≠ 0 := by omega
  have hL13 : 13 ≤ L := by
    rw [hL, Nat.le_log_iff_pow_le (by norm_num) hv0]
    norm_num
    exact hv
  have hvL : 2 ^ L ≤ v := Nat.pow_log_le_self 2 hv0
  have hvL1 : v < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) v
  have hn1pos : 1 ≤ n1 := by omega
  have h30 : 30 * n1 ≤ v := by omega
  -- the lower bound
  have hlow : Cst ^ n1 ≤ lcmUpto y * n1 ^ 8 * Cst := by
    calc Cst ^ n1 ≤ lcmUpto (30 * n1) * n1 ^ 8 * Cst := lcm_lower n1 hn1pos
      _ ≤ lcmUpto y * n1 ^ 8 * Cst := by
          have := le_trans (lcm_mono h30) hcon
          gcongr
  have hlow25 : Cst ^ (25 * n1) ≤ lcmUpto y ^ 25 * n1 ^ 200 * Cst ^ 25 := by
    calc Cst ^ (25 * n1) = (Cst ^ n1) ^ 25 := by rw [← pow_mul, mul_comm]
      _ ≤ (lcmUpto y * n1 ^ 8 * Cst) ^ 25 := Nat.pow_le_pow_left hlow 25
      _ = lcmUpto y ^ 25 * n1 ^ 200 * Cst ^ 25 := by
          rw [mul_pow, mul_pow, ← pow_mul]
  -- `n1 ^ 200 ≤ Cst ^ (6 * (L + 1))`
  have hn200 : n1 ^ 200 ≤ Cst ^ (6 * (L + 1)) := by
    have hn1v : n1 ≤ 2 ^ (L + 1) := by omega
    have h39 : 2 ^ 39 ≤ Cst := by decide
    calc n1 ^ 200 ≤ (2 ^ (L + 1)) ^ 200 := Nat.pow_le_pow_left hn1v 200
      _ = 2 ^ (200 * (L + 1)) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ (234 * (L + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = (2 ^ 39) ^ (6 * (L + 1)) := by rw [← pow_mul]; ring_nf
      _ ≤ Cst ^ (6 * (L + 1)) := Nat.pow_le_pow_left h39 _
  have hylog : Nat.log 2 y ≤ L := Nat.log_mono_right (by omega)
  have hup : lcmUpto y ^ 25 ≤ Cst ^ (y + 30 * L + 25) :=
    le_trans (lcm_upper y) (Nat.pow_le_pow_right Cst_pos (by omega))
  have hall : Cst ^ (25 * n1) ≤ Cst ^ (y + 30 * L + 25 + 6 * (L + 1) + 25) := by
    calc Cst ^ (25 * n1) ≤ lcmUpto y ^ 25 * n1 ^ 200 * Cst ^ 25 := hlow25
      _ ≤ Cst ^ (y + 30 * L + 25) * Cst ^ (6 * (L + 1)) * Cst ^ 25 := by gcongr
      _ = Cst ^ (y + 30 * L + 25 + 6 * (L + 1) + 25) := by rw [← pow_add, ← pow_add]
  have hexp : 25 * n1 ≤ y + 30 * L + 25 + 6 * (L + 1) + 25 :=
    (Nat.pow_le_pow_iff_right one_lt_Cst).mp hall
  have hpb := pow_bound L hL13
  omega

/-- A sub-interval with no prime power does not change the least common multiple. -/
lemma lcm_eq_of_no_primePow (a b : ℕ) (hab : a ≤ b)
    (h : ∀ q : ℕ, IsPrimePow q → a < q → ¬ q ≤ b) : lcmUpto b = lcmUpto a := by
  apply Nat.eq_of_factorization_eq (lcmUpto_ne_zero b) (lcmUpto_ne_zero a)
  intro p
  by_cases hp : p.Prime
  · rw [factorization_lcmUpto b hp, factorization_lcmUpto a hp]
    refine le_antisymm ?_ (Nat.log_mono_right hab)
    by_contra hlt
    rw [not_le] at hlt
    have hb0 : b ≠ 0 := by
      intro hb0
      subst hb0
      simp at hlt
    have hk : Nat.log p b ≠ 0 := by omega
    have h1 : p ^ Nat.log p b ≤ b := Nat.pow_log_le_self p hb0
    have h2 : a < p ^ Nat.log p b :=
      lt_of_lt_of_le (Nat.lt_pow_succ_log_self hp.one_lt a)
        (Nat.pow_le_pow_right hp.pos hlt)
    exact h _ ((Nat.prime_iff.mp hp).isPrimePow.pow hk) h2 h1
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]

/-- For `v ≥ 8192` there is a prime power `q` with `3v/4 < q ≤ v`. -/
lemma primePow_large (v : ℕ) (hv : 8192 ≤ v) : ∃ q : ℕ, IsPrimePow q ∧ 3 * v < 4 * q ∧ q ≤ v := by
  by_contra hcon
  have h : ∀ q : ℕ, IsPrimePow q → 3 * v / 4 < q → ¬ q ≤ v := by
    intro q hq h1 h2
    apply hcon
    refine ⟨q, hq, ?_, h2⟩
    omega
  have := lcm_eq_of_no_primePow (3 * v / 4) v (by omega) h
  have hlt := lcm_lt v hv
  omega

/-- With no prime in `(3v/4, v]`, the least common multiple grows at most by the primorial of
the square root. -/
lemma lcm_dvd_of_no_prime (v : ℕ) (hv : 2 ≤ v)
    (h : ∀ q : ℕ, q.Prime → 3 * v / 4 < q → ¬ q ≤ v) :
    lcmUpto v ∣ primorial (Nat.sqrt v) * lcmUpto (3 * v / 4) := by
  have hprim : primorial (Nat.sqrt v) ≠ 0 := (primorial_pos _).ne'
  rw [← Nat.factorization_prime_le_iff_dvd (lcmUpto_ne_zero v)
    (Nat.mul_ne_zero hprim (lcmUpto_ne_zero _))]
  intro p hp
  rw [Nat.factorization_mul hprim (lcmUpto_ne_zero _), Finsupp.add_apply,
    factorization_lcmUpto v hp, factorization_lcmUpto _ hp]
  set y := 3 * v / 4 with hy
  have hyv : y ≤ v := by omega
  by_cases hlog : Nat.log p v ≤ Nat.log p y
  · omega
  · rw [not_le] at hlog
    set k := Nat.log p v with hk
    have hv0 : v ≠ 0 := by omega
    have h1 : p ^ k ≤ v := Nat.pow_log_le_self p hv0
    have h2 : y < p ^ k :=
      lt_of_lt_of_le (Nat.lt_pow_succ_log_self hp.one_lt y) (Nat.pow_le_pow_right hp.pos hlog)
    -- `k ≥ 2`, since `p ^ k` is not a prime
    have hk2 : 2 ≤ k := by
      by_contra hk2
      have hk1 : k = 1 := by omega
      rw [hk1, pow_one] at h1 h2
      exact h p hp h2 h1
    obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h1' : p ^ (k' + 1) ≤ v := by
      rw [← hk']
      exact h1
    -- `p ^ k' ≤ y`
    have h3 : p ^ k' ≤ y := by
      have hp2 : 2 ≤ p := hp.two_le
      have : 2 * p ^ k' ≤ v := by
        calc 2 * p ^ k' ≤ p * p ^ k' := Nat.mul_le_mul_right _ hp2
          _ = p ^ (k' + 1) := by ring
          _ ≤ v := h1'
      omega
    have hy0 : y ≠ 0 := by omega
    have h4 : k' ≤ Nat.log p y := (Nat.le_log_iff_pow_le hp.one_lt hy0).mpr h3
    -- `p ≤ sqrt v`
    have h5 : p ≤ Nat.sqrt v := by
      rw [Nat.le_sqrt']
      calc p ^ 2 ≤ p ^ (k' + 1) := Nat.pow_le_pow_right hp.pos (by omega)
        _ ≤ v := h1'
    have h6 : p ∣ primorial (Nat.sqrt v) := by
      unfold primorial
      apply Finset.dvd_prod_of_mem
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp⟩
    have h7 : 0 < (primorial (Nat.sqrt v)).factorization p :=
      hp.factorization_pos_of_dvd hprim h6
    omega

lemma pow_bound2 (L : ℕ) (hL : 14 ≤ L) : 5 * (432 * L + 962) < 4 * 2 ^ L := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hL
  have e : (2 : ℕ) ^ (14 + m) = 16384 * 2 ^ m := by
    rw [pow_add]
    norm_num
  rw [e]
  have h2 : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  generalize 2 ^ m = X at h2 ⊢
  omega

/-- For `v ≥ 16384` there is a prime `q` with `3v/4 < q ≤ v`. -/
lemma prime_large (v : ℕ) (hv : 16384 ≤ v) : ∃ q : ℕ, q.Prime ∧ 3 * v < 4 * q ∧ q ≤ v := by
  by_contra hcon
  have hno : ∀ q : ℕ, q.Prime → 3 * v / 4 < q → ¬ q ≤ v := by
    intro q hq h1 h2
    apply hcon
    exact ⟨q, hq, by omega, h2⟩
  set y := 3 * v / 4 with hy
  set s := Nat.sqrt v with hs
  set n1 := v / 30 with hn1
  set L := Nat.log 2 v with hL
  have hv0 : v ≠ 0 := by omega
  have hdvd := lcm_dvd_of_no_prime v (by omega) hno
  have hle : lcmUpto v ≤ 4 ^ s * lcmUpto y := by
    calc lcmUpto v ≤ primorial s * lcmUpto y :=
          Nat.le_of_dvd (Nat.mul_pos (primorial_pos _) (lcmUpto_pos _)) hdvd
      _ ≤ 4 ^ s * lcmUpto y := Nat.mul_le_mul_right _ (primorial_le_four_pow s)
  have hL14 : 14 ≤ L := by
    rw [hL, Nat.le_log_iff_pow_le (by norm_num) hv0]
    norm_num
    exact hv
  have hvL : 2 ^ L ≤ v := Nat.pow_log_le_self 2 hv0
  have hvL1 : v < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) v
  have hn1pos : 1 ≤ n1 := by omega
  have h30 : 30 * n1 ≤ v := by omega
  have hlow : Cst ^ n1 ≤ 4 ^ s * lcmUpto y * n1 ^ 8 * Cst := by
    calc Cst ^ n1 ≤ lcmUpto (30 * n1) * n1 ^ 8 * Cst := lcm_lower n1 hn1pos
      _ ≤ (4 ^ s * lcmUpto y) * n1 ^ 8 * Cst := by
          have := le_trans (lcm_mono h30) hle
          gcongr
  have hlow25 : Cst ^ (25 * n1) ≤ 4 ^ (25 * s) * lcmUpto y ^ 25 * n1 ^ 200 * Cst ^ 25 := by
    calc Cst ^ (25 * n1) = (Cst ^ n1) ^ 25 := by rw [← pow_mul, mul_comm]
      _ ≤ (4 ^ s * lcmUpto y * n1 ^ 8 * Cst) ^ 25 := Nat.pow_le_pow_left hlow 25
      _ = 4 ^ (25 * s) * lcmUpto y ^ 25 * n1 ^ 200 * Cst ^ 25 := by
          rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm s 25]
  have h39 : 2 ^ 39 ≤ Cst := by decide
  have h4s : 4 ^ (25 * s) ≤ Cst ^ (2 * s) := by
    calc 4 ^ (25 * s) = 2 ^ (50 * s) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
          ring_nf
      _ ≤ 2 ^ (78 * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = (2 ^ 39) ^ (2 * s) := by rw [← pow_mul]; ring_nf
      _ ≤ Cst ^ (2 * s) := Nat.pow_le_pow_left h39 _
  have hn200 : n1 ^ 200 ≤ Cst ^ (6 * (L + 1)) := by
    have hn1v : n1 ≤ 2 ^ (L + 1) := by omega
    calc n1 ^ 200 ≤ (2 ^ (L + 1)) ^ 200 := Nat.pow_le_pow_left hn1v 200
      _ = 2 ^ (200 * (L + 1)) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ (234 * (L + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = (2 ^ 39) ^ (6 * (L + 1)) := by rw [← pow_mul]; ring_nf
      _ ≤ Cst ^ (6 * (L + 1)) := Nat.pow_le_pow_left h39 _
  have hylog : Nat.log 2 y ≤ L := Nat.log_mono_right (by omega)
  have hup : lcmUpto y ^ 25 ≤ Cst ^ (y + 30 * L + 25) :=
    le_trans (lcm_upper y) (Nat.pow_le_pow_right Cst_pos (by omega))
  have hall : Cst ^ (25 * n1) ≤ Cst ^ (2 * s + (y + 30 * L + 25) + 6 * (L + 1) + 25) := by
    calc Cst ^ (25 * n1) ≤ 4 ^ (25 * s) * lcmUpto y ^ 25 * n1 ^ 200 * Cst ^ 25 := hlow25
      _ ≤ Cst ^ (2 * s) * Cst ^ (y + 30 * L + 25) * Cst ^ (6 * (L + 1)) * Cst ^ 25 := by gcongr
      _ = Cst ^ (2 * s + (y + 30 * L + 25) + 6 * (L + 1) + 25) := by
          rw [← pow_add, ← pow_add, ← pow_add]
  have hexp : 25 * n1 ≤ 2 * s + (y + 30 * L + 25) + 6 * (L + 1) + 25 :=
    (Nat.pow_le_pow_iff_right one_lt_Cst).mp hall
  have hss : s * s ≤ v := Nat.sqrt_le v
  have hs128 : 128 ≤ s := by
    rw [hs, Nat.le_sqrt]
    omega
  have h120 : 120 * s ≤ v := by nlinarith
  have hpb := pow_bound2 L hL14
  omega

lemma chain_step_prime (q q' v : ℕ) (hq : q.Prime) (h : 3 * q' ≤ 4 * q + 2) (h1 : q ≤ v)
    (h2 : v < q') : ∃ r : ℕ, r.Prime ∧ 3 * v < 4 * r ∧ r ≤ v :=
  ⟨q, hq, by omega, h1⟩

/-- For `11 ≤ v < 16384` there is a prime `q` with `3v/4 < q ≤ v`. -/
lemma prime_small (v : ℕ) (hv11 : 11 ≤ v) (hv : v < 16384) :
    ∃ q : ℕ, q.Prime ∧ 3 * v < 4 * q ∧ q ≤ v := by
  by_cases h0 : v < 13
  · exact chain_step_prime 11 13 v (by norm_num) (by norm_num) (by omega) h0
  by_cases h1 : v < 17
  · exact chain_step_prime 13 17 v (by norm_num) (by norm_num) (by omega) h1
  by_cases h2 : v < 23
  · exact chain_step_prime 17 23 v (by norm_num) (by norm_num) (by omega) h2
  by_cases h3 : v < 31
  · exact chain_step_prime 23 31 v (by norm_num) (by norm_num) (by omega) h3
  by_cases h4 : v < 41
  · exact chain_step_prime 31 41 v (by norm_num) (by norm_num) (by omega) h4
  by_cases h5 : v < 53
  · exact chain_step_prime 41 53 v (by norm_num) (by norm_num) (by omega) h5
  by_cases h6 : v < 71
  · exact chain_step_prime 53 71 v (by norm_num) (by norm_num) (by omega) h6
  by_cases h7 : v < 89
  · exact chain_step_prime 71 89 v (by norm_num) (by norm_num) (by omega) h7
  by_cases h8 : v < 113
  · exact chain_step_prime 89 113 v (by norm_num) (by norm_num) (by omega) h8
  by_cases h9 : v < 151
  · exact chain_step_prime 113 151 v (by norm_num) (by norm_num) (by omega) h9
  by_cases h10 : v < 199
  · exact chain_step_prime 151 199 v (by norm_num) (by norm_num) (by omega) h10
  by_cases h11 : v < 263
  · exact chain_step_prime 199 263 v (by norm_num) (by norm_num) (by omega) h11
  by_cases h12 : v < 349
  · exact chain_step_prime 263 349 v (by norm_num) (by norm_num) (by omega) h12
  by_cases h13 : v < 463
  · exact chain_step_prime 349 463 v (by norm_num) (by norm_num) (by omega) h13
  by_cases h14 : v < 617
  · exact chain_step_prime 463 617 v (by norm_num) (by norm_num) (by omega) h14
  by_cases h15 : v < 823
  · exact chain_step_prime 617 823 v (by norm_num) (by norm_num) (by omega) h15
  by_cases h16 : v < 1097
  · exact chain_step_prime 823 1097 v (by norm_num) (by norm_num) (by omega) h16
  by_cases h17 : v < 1459
  · exact chain_step_prime 1097 1459 v (by norm_num) (by norm_num) (by omega) h17
  by_cases h18 : v < 1933
  · exact chain_step_prime 1459 1933 v (by norm_num) (by norm_num) (by omega) h18
  by_cases h19 : v < 2557
  · exact chain_step_prime 1933 2557 v (by norm_num) (by norm_num) (by omega) h19
  by_cases h20 : v < 3407
  · exact chain_step_prime 2557 3407 v (by norm_num) (by norm_num) (by omega) h20
  by_cases h21 : v < 4523
  · exact chain_step_prime 3407 4523 v (by norm_num) (by norm_num) (by omega) h21
  by_cases h22 : v < 6029
  · exact chain_step_prime 4523 6029 v (by norm_num) (by norm_num) (by omega) h22
  by_cases h23 : v < 8039
  · exact chain_step_prime 6029 8039 v (by norm_num) (by norm_num) (by omega) h23
  by_cases h24 : v < 10711
  · exact chain_step_prime 8039 10711 v (by norm_num) (by norm_num) (by omega) h24
  by_cases h25 : v < 14281
  · exact chain_step_prime 10711 14281 v (by norm_num) (by norm_num) (by omega) h25
  exact ⟨14281, by norm_num, by omega, by omega⟩

/-- For `v ≥ 11` there is a prime `q` with `3v/4 < q ≤ v`. -/
theorem exists_prime_interval (v : ℕ) (hv : 11 ≤ v) :
    ∃ q : ℕ, q.Prime ∧ 3 * v < 4 * q ∧ q ≤ v := by
  by_cases h : v < 16384
  · exact prime_small v hv h
  · exact prime_large v (by omega)

lemma small3 (q0 : ℕ) (hleast : IsLeast {q : ℕ | q.Prime ∧ 3 % (2 * q) = 3} q0) :
    q0.Prime ∧ q0 < 3 ∧ ∀ q : ℕ, q.Prime → q < 3 → q ≠ q0 → 3 % q < 3 % q0 := by
  have hc : (2 : ℕ) ∈ {q : ℕ | q.Prime ∧ 3 % (2 * q) = 3} := ⟨by norm_num, by norm_num⟩
  have hle : q0 ≤ 2 := hleast.2 hc
  obtain ⟨h1, h2⟩ := hleast.1
  have hq0c : q0 = 2 := by
    interval_cases q0 <;>
      first | rfl | (exfalso; revert h1; norm_num; done) | (exfalso; revert h2; norm_num; done)
  subst hq0c
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro q hq hqp hne
  interval_cases q <;>
    first | (exfalso; revert hq; norm_num; done) | (exfalso; exact hne rfl) | (norm_num; done)

lemma small5 (q0 : ℕ) (hleast : IsLeast {q : ℕ | q.Prime ∧ 5 % (2 * q) = 5} q0) :
    q0.Prime ∧ q0 < 5 ∧ ∀ q : ℕ, q.Prime → q < 5 → q ≠ q0 → 5 % q < 5 % q0 := by
  have hc : (3 : ℕ) ∈ {q : ℕ | q.Prime ∧ 5 % (2 * q) = 5} := ⟨by norm_num, by norm_num⟩
  have hle : q0 ≤ 3 := hleast.2 hc
  obtain ⟨h1, h2⟩ := hleast.1
  have hq0c : q0 = 3 := by
    interval_cases q0 <;>
      first | rfl | (exfalso; revert h1; norm_num; done) | (exfalso; revert h2; norm_num; done)
  subst hq0c
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro q hq hqp hne
  interval_cases q <;>
    first | (exfalso; revert hq; norm_num; done) | (exfalso; exact hne rfl) | (norm_num; done)

lemma small7 (q0 : ℕ) (hleast : IsLeast {q : ℕ | q.Prime ∧ 7 % (2 * q) = 7} q0) :
    q0.Prime ∧ q0 < 7 ∧ ∀ q : ℕ, q.Prime → q < 7 → q ≠ q0 → 7 % q < 7 % q0 := by
  have hc : (5 : ℕ) ∈ {q : ℕ | q.Prime ∧ 7 % (2 * q) = 7} := ⟨by norm_num, by norm_num⟩
  have hle : q0 ≤ 5 := hleast.2 hc
  obtain ⟨h1, h2⟩ := hleast.1
  have hq0c : q0 = 5 := by
    interval_cases q0 <;>
      first | rfl | (exfalso; revert h1; norm_num; done) | (exfalso; revert h2; norm_num; done)
  subst hq0c
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro q hq hqp hne
  interval_cases q <;>
    first | (exfalso; revert hq; norm_num; done) | (exfalso; exact hne rfl) | (norm_num; done)

lemma small11 (q0 : ℕ) (hleast : IsLeast {q : ℕ | q.Prime ∧ 11 % (2 * q) = 11} q0) :
    q0.Prime ∧ q0 < 11 ∧ ∀ q : ℕ, q.Prime → q < 11 → q ≠ q0 → 11 % q < 11 % q0 := by
  have hc : (7 : ℕ) ∈ {q : ℕ | q.Prime ∧ 11 % (2 * q) = 11} := ⟨by norm_num, by norm_num⟩
  have hle : q0 ≤ 7 := hleast.2 hc
  obtain ⟨h1, h2⟩ := hleast.1
  have hq0c : q0 = 7 := by
    interval_cases q0 <;>
      first | rfl | (exfalso; revert h1; norm_num; done) | (exfalso; revert h2; norm_num; done)
  subst hq0c
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro q hq hqp hne
  interval_cases q <;>
    first | (exfalso; revert hq; norm_num; done) | (exfalso; exact hne rfl) | (norm_num; done)

lemma small13 (q0 : ℕ) (hleast : IsLeast {q : ℕ | q.Prime ∧ 13 % (2 * q) = 13} q0) :
    q0.Prime ∧ q0 < 13 ∧ ∀ q : ℕ, q.Prime → q < 13 → q ≠ q0 → 13 % q < 13 % q0 := by
  have hc : (7 : ℕ) ∈ {q : ℕ | q.Prime ∧ 13 % (2 * q) = 13} := ⟨by norm_num, by norm_num⟩
  have hle : q0 ≤ 7 := hleast.2 hc
  obtain ⟨h1, h2⟩ := hleast.1
  have hq0c : q0 = 7 := by
    interval_cases q0 <;>
      first | rfl | (exfalso; revert h1; norm_num; done) | (exfalso; revert h2; norm_num; done)
  subst hq0c
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro q hq hqp hne
  interval_cases q <;>
    first | (exfalso; revert hq; norm_num; done) | (exfalso; exact hne rfl) | (norm_num; done)

lemma large (p q0 : ℕ) (hp : p.Prime) (hp17 : 17 ≤ p)
    (hleast : IsLeast {q : ℕ | q.Prime ∧ p % (2 * q) = p} q0) :
    q0.Prime ∧ q0 < p ∧ ∀ q : ℕ, q.Prime → q < p → q ≠ q0 → p % q < p % q0 := by
  have hmem : ∀ q : ℕ, q ∈ {q : ℕ | q.Prime ∧ p % (2 * q) = p} ↔ q.Prime ∧ p < 2 * q := by
    intro q
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have hpos : 0 < 2 * q := by have := h1.pos; omega
      have := Nat.mod_lt p hpos
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Nat.mod_eq_of_lt h2⟩
  -- a prime between `p / 2` and `2 p / 3`
  obtain ⟨q', hq', h3, h4⟩ := exists_prime_interval (2 * p / 3) (by omega)
  have hodd : ¬ 2 ∣ p := by
    intro h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
    omega
  have hq'1 : p < 2 * q' := by
    by_contra hcon
    have : p = 2 * q' := by omega
    exact hodd ⟨q', this⟩
  have hq'2 : 3 * q' ≤ 2 * p := by omega
  have hq0mem := (hmem q0).mp hleast.1
  obtain ⟨hq0, hq0p⟩ := hq0mem
  have hq0le : q0 ≤ q' := hleast.2 ((hmem q').mpr ⟨hq', hq'1⟩)
  have hq0lt : q0 < p := by omega
  have hmod0 : p % q0 = p - q0 := by
    rw [Nat.mod_eq_sub_mod hq0lt.le, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hq0, hq0lt, ?_⟩
  intro q hq hqp hne
  rw [hmod0]
  by_cases h2q : p < 2 * q
  · have hle : q0 ≤ q := hleast.2 ((hmem q).mpr ⟨hq, h2q⟩)
    have hmod : p % q = p - q := by
      rw [Nat.mod_eq_sub_mod hqp.le, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    omega
  · rw [not_lt] at h2q
    have hqpos : 0 < q := hq.pos
    have hd : 2 ≤ p / q := (Nat.le_div_iff_mul_le hqpos).mpr (by omega)
    have hdm := Nat.div_add_mod p q
    have hr : p % q < q := Nat.mod_lt p hqpos
    have h2 : q * 2 ≤ q * (p / q) := Nat.mul_le_mul_left q hd
    omega

theorem result (p q0 : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hleast : IsLeast {q : ℕ | q.Prime ∧ p % (2 * q) = p} q0) :
    q0.Prime ∧ q0 < p ∧ ∀ q : ℕ, q.Prime → q < p → q ≠ q0 → p % q < p % q0 := by
  by_cases h17 : 17 ≤ p
  · exact large p q0 hp h17 hleast
  · have hlt : p < 17 := by omega
    interval_cases p
    · exact small3 q0 hleast
    · exact absurd hp (by norm_num)
    · exact small5 q0 hleast
    · exact absurd hp (by norm_num)
    · exact small7 q0 hleast
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact small11 q0 hleast
    · exact absurd hp (by norm_num)
    · exact small13 q0 hleast
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)

end OMA.PP

theorem OMA.solution : type_of% @OMA.S_oeis_a079953.main :=
  fun p q0 hp hp3 hleast => OMA.PP.result p q0 hp hp3 hleast
