import OMAStatements.S_oeis_a304916

-- Credit: @kumagi
-- Uses note #106179

namespace OMA.R_oeis_a304916_R1

open OMA.S_oeis_a304916

private lemma factor_dvd_card {n : ℕ} (hn : n ≠ 0) (p : ℕ) :
    n.factorization p + 1 ∣ n.divisors.card := by
  rw [Nat.card_divisors hn]
  by_cases hp : p ∈ n.primeFactors
  · exact Finset.dvd_prod_of_mem _ hp
  · have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp
      (by rwa [Nat.support_factorization])
    simp [hz]

private lemma not_term_of_even_valuation {n p : ℕ}
    (he : Even (n.centralBinom.factorization p)) (hpos : 0 < n.centralBinom.factorization p) :
    ¬ IsTerm n := by
  obtain ⟨t, ht⟩ := he
  rintro ⟨j, hj⟩
  have hd := factor_dvd_card (Nat.centralBinom_ne_zero n) p
  rw [hj] at hd
  obtain ⟨u, _, hu⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  cases u with
  | zero => simp at hu; omega
  | succ u => rw [pow_succ] at hu; omega

private lemma valuation_two_of_granville_ramare {n p : ℕ}
    (hn : 2082 ≤ n) (hp : p.Prime) (hge : n ≤ 5 * p ^ 2)
    (hdvd : p ^ 2 ∣ n.centralBinom) : n.centralBinom.factorization p = 2 := by
  have hl := (hp.pow_dvd_iff_le_factorization (Nat.centralBinom_ne_zero n)).mp hdvd
  have h21 : 20 < p := by
    by_contra! hsmall
    have hh := Nat.pow_le_pow_left hsmall 2
    omega
  have hcubed : 2 * n < p ^ 3 := by
    calc
      2 * n ≤ 10 * p ^ 2 := by omega
      _ < p * p ^ 2 := Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos hp.pos 2)
      _ = p ^ 3 := by ring
  have hu := Nat.pow_factorization_choose_le (p := p) (k := n) (by omega : 0 < 2 * n)
  rw [← Nat.centralBinom_eq_two_mul_choose] at hu
  by_contra! hne
  have hbig := pow_le_pow_right₀ hp.one_lt.le (show 3 ≤ n.centralBinom.factorization p by omega)
  exact hcubed.not_ge (hbig.trans hu)

/-- The infinite range follows from Granville–Ramaré (1996), Theorem 1*. -/
theorem no_terms_from_granville_ramare
    (h : ∀ n : ℕ, 2082 ≤ n → ∃ p : ℕ, p.Prime ∧ n ≤ 5 * p ^ 2 ∧ p ^ 2 ∣ n.centralBinom) :
    ∀ n : ℕ, 2082 ≤ n → ¬ IsTerm n := by
  intro n hn
  obtain ⟨p, hp, hge, hdvd⟩ := h n hn
  have hv := valuation_two_of_granville_ramare hn hp hge hdvd
  exact not_term_of_even_valuation (p := p) (by rw [hv]; exact even_two)
    (by rw [hv]; decide)

private def smallPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

private lemma smallPrimes_prime (p : ℕ) (hp : p ∈ smallPrimes) : p.Prime := by
  simp [smallPrimes] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private def carryVal (n p : ℕ) : ℕ :=
  (List.range' 1 12).countP (fun i => decide (p ^ i ≤ n % p ^ i + n % p ^ i))

private lemma carryVal_correct {n p : ℕ} (hn : n < 2082) (hp : p.Prime) :
    carryVal n p = n.centralBinom.factorization p := by
  have hlog : Nat.log p (n + n) < 13 :=
    Nat.log_lt_of_lt_pow' (by decide) <|
      (show n + n < 2 ^ 13 by omega).trans_le (Nat.pow_le_pow_left hp.two_le 13)
  rw [Nat.centralBinom_eq_two_mul_choose, two_mul, Nat.factorization_choose' hp hlog]
  have hIco : Finset.Ico 1 13 = ⟨(List.range' 1 12 : Multiset ℕ), by decide⟩ := by
    ext i
    simp [List.mem_range'_1]
  rw [hIco, carryVal, List.countP_eq_length_filter]
  simp [Finset.card, Finset.filter_val, Multiset.filter_coe, Multiset.coe_card]

private def foundWitness (n : ℕ) : Bool :=
  smallPrimes.any fun p => let e := carryVal n p; (0 < e) && (e % 2 == 0)

set_option maxRecDepth 9000 in
set_option maxHeartbeats 0 in
private lemma foundBlock (i : ℕ) (hi : i ≤ 40) :
    (List.range' (785 + 32 * i) 32).all
      (fun n => if n < 2082 then foundWitness n else true) = true := by
  interval_cases i <;> decide +kernel

theorem no_terms_in_small_range (n : ℕ) (hlo : 784 < n) (hhi : n < 2082) : ¬ IsTerm n := by
  let j := (n - 785) / 32
  have hj : j ≤ 40 := by dsimp [j]; omega
  have hm : n ∈ List.range' (785 + 32 * j) 32 := by
    apply List.mem_range'_1.mpr
    dsimp [j]
    omega
  have hw := (List.all_eq_true.mp (foundBlock j hj)) n hm
  rw [if_pos hhi] at hw
  obtain ⟨p, hp, hv⟩ := List.any_eq_true.mp hw
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
  rw [carryVal_correct hhi (smallPrimes_prime p hp)] at hv
  exact not_term_of_even_valuation (Nat.even_iff.mpr hv.2) hv.1

/-- Granville–Ramaré (1996), p. 1. Their exponential-sum argument gives
a squared prime factor strictly greater than sqrt(n) in this range.
Source: https://dms.umontreal.ca/~andrew/PDF/ramare.pdf -/
def H1 : Prop := ∀ n : ℕ, 2 ^ 1617 ≤ n →
  ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ^ 2 ∣ n.centralBinom

/-- The bounded computation within Granville–Ramaré Theorem 1*, p. 2.
The larger range is covered separately by H1. -/
def H2 : Prop := ∀ n : ℕ, 2082 ≤ n → n < 2 ^ 1617 →
  ∃ p : ℕ, p.Prime ∧ n ≤ 5 * p ^ 2 ∧ p ^ 2 ∣ n.centralBinom

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a304916.main := by
  intro hlarge hmiddle n hn
  by_cases hsmall : n < 2082
  · exact no_terms_in_small_range n hn hsmall
  · apply no_terms_from_granville_ramare _ n (by omega)
    intro k hk
    by_cases h : 2 ^ 1617 ≤ k
    · obtain ⟨p, hp, hpk, hdvd⟩ := hlarge k h
      exact ⟨p, hp, by omega, hdvd⟩
    · exact hmiddle k hk (by omega)

end OMA.R_oeis_a304916_R1
