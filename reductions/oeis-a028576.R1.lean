import OMAStatements.S_oeis_a028576

/-!
The Möbius sum reduces to differences of squared central binomial coefficients
at consecutive powers of each prime. H1 covers odd primes and H2 covers the
extra powers of two needed for division by 4n.

See Straub, Multivariate Apéry numbers and supercongruences of rational
functions, Lemma 5.1.
https://msp.org/ant/2014/8-8/ant-v8-n8-p07-s.pdf
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace OMA.R_oeis_a028576_R1

private theorem reindex_S (n : ℕ) : OMA.S_oeis_a028576.S n =
    ∑ d ∈ n.divisors, μ d * ((2 * (n / d)).choose (n / d) : ℤ) ^ 2 := by
  unfold OMA.S_oeis_a028576.S
  rw [← Nat.sum_divisorsAntidiagonal (fun d e => μ e * ((2 * d).choose d : ℤ) ^ 2),
    Nat.sum_divisorsAntidiagonal' (fun d e => μ e * ((2 * d).choose d : ℤ) ^ 2)]

theorem numerator_prime_power (f : ℕ → ℤ) {p m : ℕ}
    (hp : p.Prime) (hpm : p.Coprime m) (k : ℕ) :
    (∑ d ∈ (p ^ (k + 1) * m).divisors, μ d * f (p ^ (k + 1) * m / d)) =
      ∑ d ∈ m.divisors, μ d * (f (p ^ (k + 1) * (m / d)) - f (p ^ k * (m / d))) := by
  classical
  rw [(hpm.pow_left (k + 1)).divisors_mul, Finset.sum_map]
  change (∑ x ∈ ((p ^ (k + 1)).divisors ×ˢ m.divisors).attach,
    μ (x.val.1 * x.val.2) * f (p ^ (k + 1) * m / (x.val.1 * x.val.2))) = _
  rw [Finset.sum_attach (f := fun x : ℕ × ℕ =>
    μ (x.1 * x.2) * f (p ^ (k + 1) * m / (x.1 * x.2))), Finset.sum_product, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
  have hpd : p.Coprime d := hpm.coprime_dvd_right hdm
  change (∑ j ∈ (p ^ (k + 1)).divisors, μ (j * d) * f (p ^ (k + 1) * m / (j * d))) = _
  rw [Nat.sum_divisors_prime_pow hp]
  have hmu (j : ℕ) : μ (p ^ j * d) = μ (p ^ j) * μ d :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (hpd.pow_left j)
  simp_rw [hmu]
  rw [show k + 1 + 1 = k + 2 by rfl, Finset.sum_range_succ', Finset.sum_range_succ']
  have hzero : (∑ j ∈ range k, μ (p ^ (j + 1 + 1)) * μ d *
      f (p ^ (k + 1) * m / (p ^ (j + 1 + 1) * d))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp
  rw [hzero]
  simp only [zero_add, pow_zero, one_mul, pow_one, ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime hp, neg_one_mul]
  have hdiv : p ^ (k + 1) * m / (p * d) = p ^ k * (m / d) := by
    rw [pow_succ', mul_assoc, Nat.mul_div_mul_left _ _ hp.pos, Nat.mul_div_assoc _ hdm]
  rw [hdiv, Nat.mul_div_assoc _ hdm]
  ring

theorem exact_denominator {n s : ℤ} (hn : n ≠ 0)
    (h₂ : 4 * n ^ 2 ∣ s) (h₃ : 4 * n ^ 3 ∣ 3 * s) :
    n ∣ s / (4 * n) ∧ n ^ 2 ∣ 3 * (s / (4 * n)) := by
  have hbase : 4 * n ∣ s := by
    refine dvd_trans ⟨n, by ring⟩ h₂
  have hne : (4 : ℤ) * n ≠ 0 := mul_ne_zero (by decide) hn
  have hcancel : 4 * n * (s / (4 * n)) = s := Int.mul_ediv_cancel' hbase
  constructor
  · apply (mul_dvd_mul_iff_left hne).mp
    rw [hcancel, show 4 * n * n = 4 * n ^ 2 by ring]
    exact h₂
  · apply (mul_dvd_mul_iff_left hne).mp
    rw [show 4 * n * (3 * (s / (4 * n))) = 3 * (4 * n * (s / (4 * n))) by ring,
      hcancel, show 4 * n * n ^ 2 = 4 * n ^ 3 by ring]
    exact h₃

theorem scaled_of_prime_power_bounds {n : ℕ} (hn : n ≠ 0) (r : ℕ) {s : ℤ}
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ^ (r * n.factorization p + if p = 2 then 2 else 0) ∣ s) :
    4 * (n : ℤ) ^ r ∣ s := by
  by_cases hs : s = 0
  · simp [hs]
  have hnat : 4 * n ^ r ∣ s.natAbs := by
    apply (Nat.factorization_prime_le_iff_dvd (by positivity)
      (Int.natAbs_ne_zero.mpr hs)).mp
    intro p hp
    have hdiv : p ^ (r * n.factorization p + if p = 2 then 2 else 0) ∣ s.natAbs := by
      apply Int.natCast_dvd_natCast.mp
      simpa using Int.dvd_natAbs.mpr (h p hp)
    have h₄ : (4 : ℕ).factorization p = if p = 2 then 2 else 0 := by
      rw [show (4 : ℕ) = 2 ^ 2 by decide, Nat.prime_two.factorization_pow, Finsupp.single_apply]
      simp [eq_comm]
    rw [Nat.factorization_mul (by decide) (pow_ne_zero _ hn), Finsupp.add_apply,
      h₄, Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul, add_comm]
    exact (hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr hs)).mp hdiv
  simpa using Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hnat)

theorem four_dvd_S (n : ℕ) : (4 : ℤ) ∣ OMA.S_oeis_a028576.S n := by
  unfold OMA.S_oeis_a028576.S
  apply Finset.dvd_sum
  intro d hd
  have heven := Nat.two_dvd_centralBinom_of_one_le (Nat.pos_of_mem_divisors hd)
  rw [Nat.centralBinom_eq_two_mul_choose] at heven
  have heven' : (2 : ℤ) ∣ ((2 * d).choose d : ℤ) := by exact_mod_cast heven
  have hpow : (4 : ℤ) ∣ ((2 * d).choose d : ℤ) ^ 2 := by
    norm_num at *
    exact pow_dvd_pow_of_dvd heven' 2
  exact dvd_mul_of_dvd_right hpow _

/-- The two divisibility bounds for differences at odd primes. -/
def H1 : Prop := ∀ p k d : ℕ, p.Prime → p ≠ 2 →
  let x := p ^ (k + 1) * d
  let y := p ^ k * d
  let difference := ((2 * x).choose x : ℤ) ^ 2 - ((2 * y).choose y : ℤ) ^ 2
  (p : ℤ) ^ (2 * (k + 1)) ∣ difference ∧
  (p : ℤ) ^ (3 * (k + 1)) ∣ 3 * difference

/-- The strengthened bound for differences at the prime two. -/
def H2 : Prop := ∀ k d : ℕ,
  let x := 2 ^ (k + 1) * d
  let y := 2 ^ k * d
  (2 : ℤ) ^ (3 * (k + 1) + 2) ∣
    ((2 * x).choose x : ℤ) ^ 2 - ((2 * y).choose y : ℤ) ^ 2

theorem local_bounds (odd : H1) (two : H2)
    {n : ℕ} (hn : n ≠ 0) {p : ℕ} (hp : p.Prime) :
    (p : ℤ) ^ (2 * n.factorization p + if p = 2 then 2 else 0) ∣ OMA.S_oeis_a028576.S n ∧
    (p : ℤ) ^ (3 * n.factorization p + if p = 2 then 2 else 0) ∣ 3 * OMA.S_oeis_a028576.S n := by
  cases hk : n.factorization p with
  | zero =>
    by_cases h : p = 2
    · subst p
      norm_num
      exact ⟨four_dvd_S n, dvd_mul_of_dvd_right (four_dvd_S n) _⟩
    · simp [h]
  | succ k =>
    let m := n / p ^ n.factorization p
    have hpm : p.Coprime m := Nat.coprime_ordCompl hp hn
    have hnm : p ^ (k + 1) * m = n := by
      rw [← hk]
      exact Nat.ordProj_mul_ordCompl_eq_self n p
    let B (x : ℕ) : ℤ := ((2 * x).choose x : ℤ) ^ 2
    let difference (d : ℕ) := B (p ^ (k + 1) * d) - B (p ^ k * d)
    have hS : OMA.S_oeis_a028576.S n =
        ∑ d ∈ m.divisors, μ d * difference (m / d) := by
      calc
        OMA.S_oeis_a028576.S n = (∑ d ∈ n.divisors, μ d * B (n / d)) := reindex_S n
        _ = (∑ d ∈ (p ^ (k + 1) * m).divisors, μ d * B (p ^ (k + 1) * m / d)) :=
          congrArg (fun a : ℕ => ∑ d ∈ a.divisors, μ d * B (a / d)) hnm.symm
        _ = _ := numerator_prime_power B hp hpm k
    by_cases h : p = 2
    · subst p
      simp only [Nat.cast_ofNat, if_true]
      have hstrong : (2 : ℤ) ^ (3 * (k + 1) + 2) ∣ OMA.S_oeis_a028576.S n := by
        rw [hS]
        exact Finset.dvd_sum fun d _ => dvd_mul_of_dvd_right (two k (m / d)) _
      exact ⟨dvd_trans (pow_dvd_pow _ (by omega)) hstrong, dvd_mul_of_dvd_right hstrong _⟩
    · simp only [if_neg h, add_zero]
      constructor
      · rw [hS]
        exact Finset.dvd_sum fun d _ => dvd_mul_of_dvd_right (odd p k (m / d) hp h).1 _
      · rw [hS, Finset.mul_sum]
        apply Finset.dvd_sum
        intro d _
        rw [mul_left_comm]
        exact dvd_mul_of_dvd_right (odd p k (m / d) hp h).2 _

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a028576.main := by
  intro odd two n hn
  have hne : n ≠ 0 := by omega
  unfold OMA.S_oeis_a028576.a
  refine exact_denominator (by exact_mod_cast hne) ?_ ?_
  · exact scaled_of_prime_power_bounds hne 2 fun p hp => (local_bounds odd two hne hp).1
  · exact scaled_of_prime_power_bounds hne 3 fun p hp => (local_bounds odd two hne hp).2

end OMA.R_oeis_a028576_R1
