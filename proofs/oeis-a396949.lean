import OMAStatements.S_oeis_a396949

open Asymptotics Filter Finset

namespace OMA.A396949

/-
Use five fixed primes and one large prime p. Four independent exponents range from 1 to
p/4, the fifth balances their sum, and p has exponent one. For every such choice, the number
lies below p * 11^(p+21). This gives a quartic lower bound in log of the endpoint along primes.
-/

private abbrev Choices (p : ℕ) :=
  Fin (p / 4) × Fin (p / 4) × Fin (p / 4) × Fin (p / 4)

private def smallPrimes : Finset ℕ := {2, 3, 5, 7, 11}

private def stock (p : ℕ) : Finset ℕ := insert p smallPrimes

private def mass {p : ℕ} (t : Choices p) : ℕ :=
  (t.1 : ℕ) + (t.2.1 : ℕ) + (t.2.2.1 : ℕ) + (t.2.2.2 : ℕ) + 4

private theorem massLe {p : ℕ} (t : Choices p) : mass t ≤ p := by
  have h₁ := t.1.isLt
  have h₂ := t.2.1.isLt
  have h₃ := t.2.2.1.isLt
  have h₄ := t.2.2.2.isLt
  unfold mass
  omega

private def exponent (p : ℕ) (t : Choices p) (q : ℕ) : ℕ :=
  if q = 2 then (t.1 : ℕ) + 1 else
  if q = 3 then (t.2.1 : ℕ) + 1 else
  if q = 5 then (t.2.2.1 : ℕ) + 1 else
  if q = 7 then (t.2.2.2 : ℕ) + 1 else
  if q = 11 then p + 21 - mass t else 1

private theorem exponentPos {p : ℕ} (t : Choices p) (q : ℕ) : 0 < exponent p t q := by
  have h := massLe t
  unfold exponent
  split_ifs <;> omega

private theorem exponentAtPrime {p : ℕ} (hp : 11 < p) (t : Choices p) :
    exponent p t p = 1 := by
  unfold exponent
  split_ifs <;> omega

private theorem sumExp {p : ℕ} (t : Choices p) :
    ∑ q ∈ smallPrimes, exponent p t q = p + 21 := by
  have h := massLe t
  norm_num [smallPrimes, exponent, sum_insert, mass] at *
  omega

private noncomputable def exponents (p : ℕ) (t : Choices p) : ℕ →₀ ℕ :=
  Finsupp.onFinset (stock p) (fun q => if q ∈ stock p then exponent p t q else 0) (by aesop)

private theorem supportExponents (p : ℕ) (t : Choices p) :
    (exponents p t).support = stock p := by
  ext q
  by_cases h : q ∈ stock p
  · simp [exponents, h, (exponentPos t q).ne']
  · simp [exponents, h]

private theorem evalExponents {p : ℕ} (t : Choices p) {q : ℕ} (hq : q ∈ stock p) :
    exponents p t q = exponent p t q := by simp [exponents, hq]

private noncomputable def value (p : ℕ) (t : Choices p) : ℕ := (exponents p t).prod (· ^ ·)

private theorem stockPrime {p q : ℕ} (hp : p.Prime) (hq : q ∈ stock p) : q.Prime := by
  simp [stock, smallPrimes] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp
  all_goals norm_num

private theorem stockNotSmall {p : ℕ} (hp : 11 < p) : p ∉ smallPrimes := by
  simp [smallPrimes]
  omega

private theorem valueFactorization {p : ℕ} (hp : p.Prime) (t : Choices p) :
    (value p t).factorization = exponents p t := by
  apply Nat.prod_pow_factorization_eq_self
  rw [supportExponents]
  exact fun _ hq => stockPrime hp hq

private theorem valuePos {p : ℕ} (hp : p.Prime) (t : Choices p) : 0 < value p t := by
  unfold value Finsupp.prod
  rw [supportExponents]
  exact prod_pos fun q hq => pow_pos (stockPrime hp hq).pos _

private theorem memberValue {p : ℕ} (hp : p.Prime) (hp' : 11 < p) (t : Choices p) :
    OMA.S_oeis_a396949.member (value p t) := by
  unfold OMA.S_oeis_a396949.member
  rw [valueFactorization hp, supportExponents]
  have hsum : (∑ q ∈ stock p, exponents p t q) = ∑ q ∈ stock p, exponent p t q :=
    sum_congr rfl fun _ hq => evalExponents t hq
  rw [hsum]
  have hnot := stockNotSmall hp'
  simp only [stock, card_insert_of_notMem hnot, sum_insert hnot, exponentAtPrime hp', sumExp]
  norm_num [smallPrimes, sum_insert, card_insert_of_notMem]
  omega

private def bound (p : ℕ) : ℕ := p * 11 ^ (p + 21)

private theorem valueLe {p : ℕ} (hp : 11 < p) (t : Choices p) : value p t ≤ bound p := by
  unfold value Finsupp.prod bound
  rw [supportExponents]
  have hprod : (∏ q ∈ stock p, q ^ exponents p t q) =
      ∏ q ∈ stock p, q ^ exponent p t q :=
    prod_congr rfl fun q hq => congrArg (q ^ ·) (evalExponents t hq)
  rw [hprod]
  simp only [stock, prod_insert (stockNotSmall hp), exponentAtPrime hp, pow_one]
  apply Nat.mul_le_mul_left
  calc
    _ ≤ ∏ q ∈ smallPrimes, 11 ^ exponent p t q := by
      apply prod_le_prod'
      intro q hq
      apply Nat.pow_le_pow_left
      simp [smallPrimes] at hq
      omega
    _ = _ := by rw [prod_pow_eq_pow_sum, sumExp]

private theorem valueInjective {p : ℕ} (hp : p.Prime) : Function.Injective (value p) := by
  intro t u h
  have hfu := congrArg Nat.factorization h
  rw [valueFactorization hp, valueFactorization hp] at hfu
  have he (q : ℕ) (hq : q ∈ stock p) : exponent p t q = exponent p u q := by
    rw [← evalExponents t hq, ← evalExponents u hq, hfu]
  apply Prod.ext
  · apply Fin.ext
    simpa [exponent] using he 2 (by simp [stock, smallPrimes])
  · apply Prod.ext
    · apply Fin.ext
      simpa [exponent] using he 3 (by simp [stock, smallPrimes])
    · apply Prod.ext
      · apply Fin.ext
        simpa [exponent] using he 5 (by simp [stock, smallPrimes])
      · apply Fin.ext
        simpa [exponent] using he 7 (by simp [stock, smallPrimes])

private theorem countLower {p : ℕ} (hp : p.Prime) (hp' : 11 < p) :
    (p / 4) ^ 4 ≤ OMA.S_oeis_a396949.count (bound p) := by
  classical
  have hsub : univ.image (value p) ⊆
      (range (bound p + 1)).filter fun n => 0 < n ∧ OMA.S_oeis_a396949.member n := by
    intro n hn
    obtain ⟨t, _, rfl⟩ := mem_image.mp hn
    exact mem_filter.mpr ⟨mem_range.mpr (by have := valueLe hp' t; omega),
      valuePos hp t, memberValue hp hp' t⟩
  simpa [OMA.S_oeis_a396949.count, card_image_of_injective _ (valueInjective hp),
    Fintype.card_prod, pow_succ, mul_assoc] using card_le_card hsub

private theorem boundLeLog {p : ℕ} (hp : 11 < p) :
    Real.log (bound p : ℝ) ≤ 31 * (p : ℝ) := by
  have hp' : (11 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpp : (0 : ℝ) < p := by linarith
  have h11 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 11 by norm_num)
  have hpLog := Real.log_le_sub_one_of_pos hpp
  have hmul := mul_le_mul_of_nonneg_left h11 (show 0 ≤ (p : ℝ) + 21 by positivity)
  unfold bound
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul hpp.ne' (by positivity), Real.log_pow]
  push_cast
  norm_num at hmul
  linarith

set_option maxHeartbeats 600000 in
private theorem noCubicBound : ¬ OMA.S_oeis_a396949.conjecture := by
  intro h
  obtain ⟨C, hC⟩ := h.isBigO.bound
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hC
  let B := max C 1
  have hB : 0 ≤ B := le_trans (by norm_num) (le_max_right _ _)
  obtain ⟨m, hm⟩ := exists_nat_gt (B * 31 ^ 3 * 8 ^ 4)
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max N₀ (max 12 m))
  have hp₀ : N₀ ≤ p := (le_max_left _ _).trans hpN
  have hp' : 11 < p := by
    have h₁₂ : 12 ≤ p := (le_max_left _ _).trans ((le_max_right _ _).trans hpN)
    omega
  have hm' : m ≤ p := (le_max_right _ _).trans ((le_max_right _ _).trans hpN)
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hb : p ≤ bound p := by
    unfold bound
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hlog_nonneg : 0 ≤ Real.log (bound p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le.trans hb)
  have hcount : 0 ≤ (OMA.S_oeis_a396949.count (bound p) : ℝ) := Nat.cast_nonneg _
  have hup : (OMA.S_oeis_a396949.count (bound p) : ℝ) ≤ C * Real.log (bound p : ℝ) ^ 3 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hcount, abs_of_nonneg (pow_nonneg hlog_nonneg 3)]
      using hN₀ (bound p) (hp₀.trans hb)
  have hup' : (OMA.S_oeis_a396949.count (bound p) : ℝ) ≤ B * (31 * (p : ℝ)) ^ 3 :=
    hup.trans (mul_le_mul (le_max_left _ _)
      (pow_le_pow_left₀ hlog_nonneg (boundLeLog hp') 3) (by positivity) hB)
  have hdiv : (p : ℝ) / 8 ≤ ((p / 4 : ℕ) : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).2
    exact_mod_cast (show p ≤ (p / 4) * 8 by omega)
  have hlo : ((p : ℝ) / 8) ^ 4 ≤ (OMA.S_oeis_a396949.count (bound p) : ℝ) :=
    (pow_le_pow_left₀ (by positivity) hdiv 4).trans (by exact_mod_cast countLower hp hp')
  have hscaled := mul_le_mul_of_nonneg_left (hlo.trans hup') (show 0 ≤ (8 : ℝ) ^ 4 by positivity)
  have hpoly : (p : ℝ) * (p : ℝ) ^ 3 ≤ (B * 31 ^ 3 * 8 ^ 4) * (p : ℝ) ^ 3 := by
    calc
      _ = 8 ^ 4 * ((p : ℝ) / 8) ^ 4 := by ring
      _ ≤ 8 ^ 4 * (B * (31 * (p : ℝ)) ^ 3) := hscaled
      _ = _ := by ring
  have hcon := le_of_mul_le_mul_right hpoly (pow_pos hpp 3)
  exact (not_lt_of_ge hcon) (hm.trans_le (by exact_mod_cast hm'))

end OMA.A396949

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a396949.main) := OMA.A396949.noCubicBound
