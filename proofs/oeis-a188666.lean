import OMAStatements.S_oeis_a188666

-- Problem: OEIS A188666, Fischer's conjecture a(n) = A000015(floor(n/2) + 1)
-- Statement: statements/oeis-a188666.lean (declaration OMA.S_oeis_a188666.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Part 1 is a theorem on short intervals: for every v >= 2 there is a prime power q with
-- 3v/4 < q <= v (`exists_primePow`). It follows Chebyshev. Let N = (30n)! n! and
-- D = (15n)! (10n)! (6n)!. For each prime power d the number
-- [30n/d] + [n/d] - [15n/d] - [10n/d] - [6n/d] is 0 or 1, and it is 1 when 5n < d <= 30n. So
-- N divides D lcm(1..30n), and D lcm(1..30n) divides N lcm(1..5n). With C = 2^14 3^9 5^5 the
-- quotient N/D is between C^n / (C n^8) and C^n. This gives lcm(1..N)^25 <= C^(N + 30 log2 N + 25)
-- and lcm(1..30n) >= C^n / (C n^8), so lcm(1..v) > lcm(1..3v/4) for v >= 8192. An interval with
-- no prime power does not change the least common multiple. For v < 8192 a chain of 31 prime
-- powers with ratio at most 4/3 is sufficient.
-- Part 2. Let q0 be the least prime power above n/2. A larger m loses the only multiple of q0
-- up to n. For m = q0 let r^k be the largest power of a prime r up to n and v = [n/r^k] r^k.
-- If [n/r^k] = 1, then v = r^k is a prime power above n/2, so v >= q0. If not, part 1 gives a
-- prime power q with 3v/4 < q <= v, and q > n/2 because n < 3v/2, so v >= q >= q0. Thus the
-- interval [q0, n] has a multiple of each r^k.

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

lemma primePow_of_prime (p : ℕ) (hp : p.Prime) : IsPrimePow p := (Nat.prime_iff.mp hp).isPrimePow

lemma primePow_four : IsPrimePow 4 := by
  have h : IsPrimePow (2 ^ 2) := (Nat.prime_iff.mp Nat.prime_two).isPrimePow.pow (by norm_num)
  simpa using h

lemma primePow_nine : IsPrimePow 9 := by
  have h : IsPrimePow (3 ^ 2) := (Nat.prime_iff.mp Nat.prime_three).isPrimePow.pow (by norm_num)
  simpa using h

lemma chain_step (q q' v : ℕ) (hq : IsPrimePow q) (h : 3 * q' ≤ 4 * q + 2) (h1 : q ≤ v)
    (h2 : v < q') : ∃ r : ℕ, IsPrimePow r ∧ 3 * v < 4 * r ∧ r ≤ v :=
  ⟨q, hq, by omega, h1⟩

/-- For `2 ≤ v < 8192` there is a prime power `q` with `3v/4 < q ≤ v`. -/
lemma primePow_small (v : ℕ) (hv2 : 2 ≤ v) (hv : v < 8192) :
    ∃ q : ℕ, IsPrimePow q ∧ 3 * v < 4 * q ∧ q ≤ v := by
  by_cases h0 : v < 3
  · exact chain_step 2 3 v (primePow_of_prime 2 (by norm_num)) (by norm_num) (by omega) h0
  by_cases h1 : v < 4
  · exact chain_step 3 4 v (primePow_of_prime 3 (by norm_num)) (by norm_num) (by omega) h1
  by_cases h2 : v < 5
  · exact chain_step 4 5 v primePow_four (by norm_num) (by omega) h2
  by_cases h3 : v < 7
  · exact chain_step 5 7 v (primePow_of_prime 5 (by norm_num)) (by norm_num) (by omega) h3
  by_cases h4 : v < 9
  · exact chain_step 7 9 v (primePow_of_prime 7 (by norm_num)) (by norm_num) (by omega) h4
  by_cases h5 : v < 11
  · exact chain_step 9 11 v primePow_nine (by norm_num) (by omega) h5
  by_cases h6 : v < 13
  · exact chain_step 11 13 v (primePow_of_prime 11 (by norm_num)) (by norm_num) (by omega) h6
  by_cases h7 : v < 17
  · exact chain_step 13 17 v (primePow_of_prime 13 (by norm_num)) (by norm_num) (by omega) h7
  by_cases h8 : v < 23
  · exact chain_step 17 23 v (primePow_of_prime 17 (by norm_num)) (by norm_num) (by omega) h8
  by_cases h9 : v < 31
  · exact chain_step 23 31 v (primePow_of_prime 23 (by norm_num)) (by norm_num) (by omega) h9
  by_cases h10 : v < 41
  · exact chain_step 31 41 v (primePow_of_prime 31 (by norm_num)) (by norm_num) (by omega) h10
  by_cases h11 : v < 53
  · exact chain_step 41 53 v (primePow_of_prime 41 (by norm_num)) (by norm_num) (by omega) h11
  by_cases h12 : v < 71
  · exact chain_step 53 71 v (primePow_of_prime 53 (by norm_num)) (by norm_num) (by omega) h12
  by_cases h13 : v < 89
  · exact chain_step 71 89 v (primePow_of_prime 71 (by norm_num)) (by norm_num) (by omega) h13
  by_cases h14 : v < 113
  · exact chain_step 89 113 v (primePow_of_prime 89 (by norm_num)) (by norm_num) (by omega) h14
  by_cases h15 : v < 151
  · exact chain_step 113 151 v (primePow_of_prime 113 (by norm_num)) (by norm_num) (by omega) h15
  by_cases h16 : v < 199
  · exact chain_step 151 199 v (primePow_of_prime 151 (by norm_num)) (by norm_num) (by omega) h16
  by_cases h17 : v < 263
  · exact chain_step 199 263 v (primePow_of_prime 199 (by norm_num)) (by norm_num) (by omega) h17
  by_cases h18 : v < 349
  · exact chain_step 263 349 v (primePow_of_prime 263 (by norm_num)) (by norm_num) (by omega) h18
  by_cases h19 : v < 463
  · exact chain_step 349 463 v (primePow_of_prime 349 (by norm_num)) (by norm_num) (by omega) h19
  by_cases h20 : v < 617
  · exact chain_step 463 617 v (primePow_of_prime 463 (by norm_num)) (by norm_num) (by omega) h20
  by_cases h21 : v < 823
  · exact chain_step 617 823 v (primePow_of_prime 617 (by norm_num)) (by norm_num) (by omega) h21
  by_cases h22 : v < 1097
  · exact chain_step 823 1097 v (primePow_of_prime 823 (by norm_num)) (by norm_num) (by omega) h22
  by_cases h23 : v < 1459
  · exact chain_step 1097 1459 v (primePow_of_prime 1097 (by norm_num)) (by norm_num) (by omega) h23
  by_cases h24 : v < 1933
  · exact chain_step 1459 1933 v (primePow_of_prime 1459 (by norm_num)) (by norm_num) (by omega) h24
  by_cases h25 : v < 2557
  · exact chain_step 1933 2557 v (primePow_of_prime 1933 (by norm_num)) (by norm_num) (by omega) h25
  by_cases h26 : v < 3407
  · exact chain_step 2557 3407 v (primePow_of_prime 2557 (by norm_num)) (by norm_num) (by omega) h26
  by_cases h27 : v < 4523
  · exact chain_step 3407 4523 v (primePow_of_prime 3407 (by norm_num)) (by norm_num) (by omega) h27
  by_cases h28 : v < 6029
  · exact chain_step 4523 6029 v (primePow_of_prime 4523 (by norm_num)) (by norm_num) (by omega) h28
  by_cases h29 : v < 8039
  · exact chain_step 6029 8039 v (primePow_of_prime 6029 (by norm_num)) (by norm_num) (by omega) h29
  exact ⟨8039, (primePow_of_prime 8039 (by norm_num)), by omega, by omega⟩

/-- For `v ≥ 2` there is a prime power `q` with `3v/4 < q ≤ v`. -/
theorem exists_primePow (v : ℕ) (hv : 2 ≤ v) : ∃ q : ℕ, IsPrimePow q ∧ 3 * v < 4 * q ∧ q ≤ v := by
  by_cases h : v < 8192
  · exact primePow_small v hv h
  · exact primePow_large v (by omega)

/-- A prime power that divides a least common multiple divides one of the numbers. -/
lemma primePow_dvd_lcm (p j : ℕ) (hp : p.Prime) (s : Finset ℕ) (hs : ∀ x ∈ s, x ≠ 0)
    (h : p ^ j ∣ s.lcm id) (hj : j ≠ 0) : ∃ x ∈ s, p ^ j ∣ x := by
  have hne : s.lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]
    simp only [id, not_exists, not_and]
    intro x hx h0
    exact hs x hx h0
  have h1 : j ≤ (s.lcm id).factorization p := (hp.pow_dvd_iff_le_factorization hne).mp h
  rw [Finset.factorization_lcm (f := id) (fun x hx => hs x hx) p] at h1
  have hpos : (⊥ : ℕ) < j := Nat.pos_of_ne_zero hj
  obtain ⟨x, hx, hjx⟩ := (Finset.le_sup_iff hpos).mp h1
  exact ⟨x, hx, (hp.pow_dvd_iff_le_factorization (hs x hx)).mpr hjx⟩

theorem result (n m : ℕ) (hn : 1 ≤ n)
    (hm : IsGreatest {k : ℕ | 1 ≤ k ∧ k ≤ n ∧ (Finset.Icc k n).lcm id = (Finset.Icc 1 n).lcm id} m) :
    IsLeast {q : ℕ | (q = 1 ∨ IsPrimePow q) ∧ n / 2 + 1 ≤ q} m := by
  classical
  -- the least prime power above `n / 2`
  have hex : ∃ q : ℕ, (q = 1 ∨ IsPrimePow q) ∧ n / 2 + 1 ≤ q ∧ q ≤ n := by
    by_cases h1 : n = 1
    · exact ⟨1, Or.inl rfl, by omega, by omega⟩
    · have hn0 : n ≠ 0 := by omega
      have hk : Nat.log 2 n ≠ 0 := by
        have := Nat.log_pos (b := 2) (by norm_num) (show 2 ≤ n by omega)
        omega
      refine ⟨2 ^ Nat.log 2 n, Or.inr ((Nat.prime_iff.mp Nat.prime_two).isPrimePow.pow hk), ?_,
        Nat.pow_log_le_self 2 hn0⟩
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
      rw [pow_succ] at this
      omega
  have hex' : ∃ q : ℕ, (q = 1 ∨ IsPrimePow q) ∧ n / 2 + 1 ≤ q := by
    obtain ⟨q, h1, h2, -⟩ := hex
    exact ⟨q, h1, h2⟩
  set q0 := Nat.find hex' with hq0
  have hq0spec : (q0 = 1 ∨ IsPrimePow q0) ∧ n / 2 + 1 ≤ q0 := Nat.find_spec hex'
  have hq0min : ∀ q : ℕ, (q = 1 ∨ IsPrimePow q) ∧ n / 2 + 1 ≤ q → q0 ≤ q := fun q hq =>
    Nat.find_min' hex' hq
  have hq0n : q0 ≤ n := by
    obtain ⟨q, h1, h2, h3⟩ := hex
    exact le_trans (hq0min q ⟨h1, h2⟩) h3
  have hq0pos : 1 ≤ q0 := by omega
  have hleast : IsLeast {q : ℕ | (q = 1 ∨ IsPrimePow q) ∧ n / 2 + 1 ≤ q} q0 :=
    ⟨hq0spec, fun q hq => hq0min q hq⟩
  -- `q0` is in the set
  have hmem : (Finset.Icc q0 n).lcm id = (Finset.Icc 1 n).lcm id := by
    apply Nat.dvd_antisymm
    · exact Finset.lcm_mono (Finset.Icc_subset_Icc_left hq0pos)
    · have hne1 : (Finset.Icc 1 n).lcm id ≠ 0 := lcmUpto_ne_zero n
      have hne2 : (Finset.Icc q0 n).lcm id ≠ 0 := by
        rw [Ne, Finset.lcm_eq_zero_iff]
        simp only [id, Finset.mem_Icc, not_exists, not_and]
        intro x hx h0
        omega
      rw [← Nat.factorization_prime_le_iff_dvd hne1 hne2]
      intro r hr
      have hlog : ((Finset.Icc 1 n).lcm id).factorization r = Nat.log r n :=
        factorization_lcmUpto n hr
      rw [hlog, ← hr.pow_dvd_iff_le_factorization hne2]
      set k := Nat.log r n with hk
      by_cases hk0 : k = 0
      · rw [hk0, pow_zero]
        exact one_dvd _
      · have hn0 : n ≠ 0 := by omega
        have hrk : r ^ k ≤ n := Nat.pow_log_le_self r hn0
        have hrk1 : n < r ^ (k + 1) := Nat.lt_pow_succ_log_self hr.one_lt n
        have hrkpos : 0 < r ^ k := pow_pos hr.pos k
        set j := n / r ^ k with hj
        have hj1 : 1 ≤ j := (Nat.one_le_div_iff hrkpos).mpr hrk
        have hv : j * r ^ k ≤ n := Nat.div_mul_le_self n (r ^ k)
        have hv2 : n < (j + 1) * r ^ k := by
          have := Nat.lt_mul_div_succ n hrkpos
          rw [mul_comm] at this
          exact this
        have hge : q0 ≤ j * r ^ k := by
          by_cases hj2 : j = 1
          · rw [hj2, one_mul]
            rw [hj2, show (1 + 1) * r ^ k = 2 * r ^ k by ring] at hv2
            exact hq0min _ ⟨Or.inr ((Nat.prime_iff.mp hr).isPrimePow.pow hk0), by omega⟩
          · have hj2' : 2 ≤ j := by omega
            have hvge : 2 ≤ j * r ^ k := by nlinarith
            obtain ⟨q', hq', h3, h4⟩ := exists_primePow (j * r ^ k) hvge
            have h5 : 2 * n < 3 * (j * r ^ k) := by nlinarith
            exact le_trans (hq0min q' ⟨Or.inr hq', by omega⟩) h4
        exact Dvd.dvd.trans (Dvd.intro_left j rfl)
          (Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hge, hv⟩))
  -- `q0` is an upper bound of the set
  have hub : ∀ k : ℕ, 1 ≤ k → k ≤ n → (Finset.Icc k n).lcm id = (Finset.Icc 1 n).lcm id →
      k ≤ q0 := by
    intro k hk1 hkn hk
    by_contra hlt
    rw [not_le] at hlt
    rcases hq0spec.1 with h1 | hpp
    · omega
    · obtain ⟨p, j, hp, hj, hpj⟩ := hpp
      have hpn : p.Prime := Nat.prime_iff.mpr hp
      have hdvd : p ^ j ∣ (Finset.Icc k n).lcm id := by
        rw [hk, hpj]
        exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hq0pos, hq0n⟩)
      obtain ⟨x, hx, hpx⟩ := primePow_dvd_lcm p j hpn (Finset.Icc k n)
        (fun x hx => by
          have := (Finset.mem_Icc.mp hx).1
          omega) hdvd (by omega)
      rw [hpj] at hpx
      obtain ⟨c, hc⟩ := hpx
      have hxk := Finset.mem_Icc.mp hx
      have hc2 : 2 ≤ c := by
        by_contra hc2
        have : c = 0 ∨ c = 1 := by omega
        rcases this with h0 | h1
        · rw [h0] at hc
          omega
        · rw [h1] at hc
          omega
      have : 2 * q0 ≤ x := by nlinarith
      omega
  have hgreat : IsGreatest {k : ℕ | 1 ≤ k ∧ k ≤ n ∧
      (Finset.Icc k n).lcm id = (Finset.Icc 1 n).lcm id} q0 :=
    ⟨⟨hq0pos, hq0n, hmem⟩, fun k hk => hub k hk.1 hk.2.1 hk.2.2⟩
  rw [hm.unique hgreat]
  exact hleast

end OMA.PP

theorem OMA.solution : type_of% @OMA.S_oeis_a188666.main :=
  fun n m hn hm => OMA.PP.result n m hn hm
