import OMAStatements.S_oeis_a345003

namespace OMA.S_oeis_a345003















/-! ### The radical and the two auxiliary quantities -/

lemma rad_dvd (n : ℕ) : rad n ∣ n := Nat.prod_primeFactors_dvd n

lemma rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

lemma dvd_rad {n p : ℕ} (hp : p ∈ n.primeFactors) : p ∣ rad n := Finset.dvd_prod_of_mem _ hp

lemma a003557_mul (n : ℕ) : a003557 n * rad n = n := Nat.div_mul_cancel (rad_dvd n)

lemma a003557_pos {n : ℕ} (hn : 0 < n) : 0 < a003557 n := by
  rcases Nat.eq_zero_or_pos (a003557 n) with h | h
  · have := a003557_mul n
    rw [h, zero_mul] at this
    omega
  · exact h

lemma div_prime_eq {n p : ℕ} (hp : p ∈ n.primeFactors) : n / p = a003557 n * (rad n / p) := by
  conv_lhs => rw [← a003557_mul n]
  exact Nat.mul_div_assoc _ (dvd_rad hp)

/-- D(n) = Sum_{p | n} v_p(n) * rad(n)/p. -/
def D (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, n.factorization p * (rad n / p)

/-- P(n) = Product_{p | n} (p + 1). -/
def P (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, (p + 1)

lemma deriv_eq (n : ℕ) : deriv n = a003557 n * D n := by
  unfold deriv D
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [div_prime_eq hp]
  ring

lemma psi_eq (n : ℕ) : psi n = (a003557 n : ℚ) * (P n : ℚ) := by
  unfold psi P
  have h1 : (n : ℚ) = (a003557 n : ℚ) * ∏ p ∈ n.primeFactors, (p : ℚ) := by
    have h := a003557_mul n
    unfold rad at h
    rw [← Nat.cast_prod, ← Nat.cast_mul, h]
  rw [h1, mul_assoc, ← Finset.prod_mul_distrib]
  push_cast
  congr 1
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  field_simp

lemma a048250_eq {n : ℕ} (hn : n ≠ 0) : a048250 n = P n := by
  unfold a048250 P
  rw [Nat.sum_divisors_filter_squarefree hn, Nat.factors_eq, Finset.prod_add_one]
  simp only [List.toFinset_coe, Nat.toFinset_factors]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id']

lemma a342001_eq {n : ℕ} (hn : 0 < n) : a342001 n = (D n : ℚ) := by
  unfold a342001
  rw [deriv_eq]
  have hm : (a003557 n : ℚ) ≠ 0 := by exact_mod_cast (a003557_pos hn).ne'
  push_cast
  field_simp

/-- The key identity: A344998(n) - A344999(n) = (D - P)(sigma - 2n). -/
lemma key {n : ℕ} (hn : 0 < n) :
    a344998 n - a344999 n = ((D n : ℚ) - P n) * ((sigma n : ℚ) - 2 * n) := by
  unfold a344998 a344999 a344753 a345001
  rw [a342001_eq hn, a048250_eq hn.ne', psi_eq, deriv_eq]
  push_cast
  ring

lemma mem_A345003_iff {n : ℕ} (hn : 0 < n) :
    a344998 n = a344999 n ↔ (D n = P n ∨ sigma n = 2 * n) := by
  rw [← sub_eq_zero, key hn, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · left
      exact_mod_cast h
    · right
      exact_mod_cast h
  · rintro (h | h)
    · left
      exact_mod_cast h
    · right
      exact_mod_cast h

lemma deriv_eq_psi_iff {n : ℕ} (hn : 0 < n) : (deriv n : ℚ) = psi n ↔ D n = P n := by
  rw [deriv_eq, psi_eq]
  have hm : (a003557 n : ℚ) ≠ 0 := by exact_mod_cast (a003557_pos hn).ne'
  push_cast
  constructor
  · intro h
    exact_mod_cast mul_left_cancel₀ hm h
  · intro h
    rw [h]

lemma perfect_iff {n : ℕ} (hn : 0 < n) : Nat.Perfect n ↔ sigma n = 2 * n :=
  Nat.perfect_iff_sum_divisors_eq_two_mul hn

/-! ### Even perfect numbers (Euclid-Euler, as in Mathlib's Archive) -/

lemma sigma_two_pow_eq_mersenne_succ (k : ℕ) :
    ArithmeticFunction.sigma 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [ArithmeticFunction.sigma_one_apply, mersenne, ← one_add_one_eq_two,
    ← geom_sum_mul_add 1 (k + 1)]
  norm_num

lemma eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  use multiplicity 2 n, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

/-- Euler: an even perfect number is 2^k (2^(k+1) - 1) with 2^(k+1) - 1 prime. -/
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n)
    (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
      (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self,
    ← succ_mersenne, add_mul, one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h_1 =>
    have j1 : j = 1 := Eq.trans hj.symm h_1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h_1
    simp [h_1, j1]
  | inr h_1 =>
    have jcon := Eq.trans hj.symm h_1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have jcon2 := mul_right_cancel₀ ?_ jcon
    · exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
    contrapose hm
    simp [hm]

/-- For an even perfect number, D(n) differs from P(n). -/
lemma even_case {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) : D n ≠ P n := by
  obtain ⟨k, hq, rfl⟩ := eq_two_pow_mul_prime_mersenne_of_even_perfect ev perf
  set q := mersenne (k + 1) with hqdef
  have hk : k ≠ 0 := by
    rintro rfl
    simp [hqdef, mersenne] at hq
    exact Nat.not_prime_one hq
  have hq3 : 3 ≤ q := by
    have h4 : 4 ≤ 2 ^ (k + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [hqdef, mersenne]
    omega
  have hq1 : q + 1 = 2 ^ (k + 1) := by
    simp only [hqdef, mersenne]
    have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    omega
  have h2q : (2 : ℕ) ≠ q := by
    intro h
    have : Even q := by rw [← h]; exact even_two
    have hodd : Odd q := by
      rw [Nat.odd_iff]
      have : q = 2 ^ (k + 1) - 1 := rfl
      rw [this]
      have h2 : 2 ^ (k + 1) % 2 = 0 := by
        rw [pow_succ]; simp
      have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      omega
    exact (Nat.not_even_iff_odd.mpr hodd) this
  have hpf : (2 ^ k * q).primeFactors = {2, q} := by
    rw [Nat.primeFactors_mul (by positivity) hq.ne_zero, Nat.primeFactors_prime_pow hk
      Nat.prime_two, Nat.Prime.primeFactors hq]
    rfl
  have hfac2 : (2 ^ k * q).factorization 2 = k := by
    rw [Nat.factorization_mul (by positivity) hq.ne_zero, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization hq]
    simp [Finsupp.single_apply, h2q]
  have hfacq : (2 ^ k * q).factorization q = 1 := by
    rw [Nat.factorization_mul (by positivity) hq.ne_zero, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization hq]
    simp [Finsupp.single_apply, h2q]
  have hrad : rad (2 ^ k * q) = 2 * q := by
    unfold rad
    rw [hpf, Finset.prod_pair h2q]
  have hD : D (2 ^ k * q) = k * q + 2 := by
    unfold D
    rw [hpf, Finset.sum_pair h2q, hfac2, hfacq, hrad]
    have hq0 : 0 < q := by omega
    rw [Nat.mul_div_cancel_left q (by norm_num : 0 < 2), Nat.mul_div_cancel _ hq0, one_mul]
  have hP : P (2 ^ k * q) = 3 * (q + 1) := by
    unfold P
    rw [hpf, Finset.prod_pair h2q]
  rw [hD, hP]
  intro h
  rcases Nat.lt_or_ge k 4 with hk4 | hk4
  · have : k * q ≤ 3 * q := Nat.mul_le_mul_right q (by omega)
    omega
  · have : 4 * q ≤ k * q := Nat.mul_le_mul_right q hk4
    omega

/-! ### Odd perfect numbers: a parity argument -/

lemma sigma_eq_prod {n : ℕ} (hn : n ≠ 0) :
    sigma n = ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i := by
  unfold sigma
  rw [← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hn,
    Nat.prod_factorization_eq_prod_primeFactors]
  refine Finset.prod_congr rfl fun p hp => ?_
  exact ArithmeticFunction.sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)

lemma geom_mod_two {p : ℕ} (hp : p % 2 = 1) (e : ℕ) :
    (∑ i ∈ Finset.range (e + 1), p ^ i) % 2 = (e + 1) % 2 := by
  rw [Finset.sum_nat_mod]
  have : ∀ i ∈ Finset.range (e + 1), p ^ i % 2 = 1 := by
    intro i _
    simp [Nat.pow_mod, hp]
  rw [Finset.sum_congr rfl this]
  simp

/-- For an odd perfect number, D(n) is odd and P(n) is even. -/
lemma odd_case {n : ℕ} (hodd : n % 2 = 1) (perf : Nat.Perfect n) : D n ≠ P n := by
  have hpos := perf.2
  have hn0 : n ≠ 0 := hpos.ne'
  have hσ : sigma n = 2 * n := (perfect_iff hpos).mp perf
  have hn1 : n ≠ 1 := by
    rintro rfl
    have : sigma 1 = 1 := by decide
    omega
  set S := n.primeFactors with hS
  have hSodd : ∀ p ∈ S, p % 2 = 1 := by
    intro p hp
    have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    rcases Nat.mod_two_eq_zero_or_one p with h | h
    · exfalso
      have : 2 ∣ n := (Nat.dvd_of_mod_eq_zero h).trans hpd
      omega
    · exact h
  set f : ℕ → ℕ := fun p => ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i with hf
  have hσprod : sigma n = ∏ p ∈ S, f p := sigma_eq_prod hn0
  have hfmod : ∀ p ∈ S, f p % 2 = (n.factorization p + 1) % 2 := fun p hp =>
    geom_mod_two (hSodd p hp) _
  set O := S.filter (fun p => n.factorization p % 2 = 1) with hO
  -- 2 ^ |O| divides sigma n = 2 n, so |O| <= 1.
  have hdvd : 2 ^ O.card ∣ 2 * n := by
    rw [← hσ, hσprod, ← Finset.prod_filter_mul_prod_filter_not S
      (fun p => n.factorization p % 2 = 1)]
    apply Dvd.dvd.mul_right
    rw [← Finset.prod_const]
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    rw [Finset.mem_filter] at hp
    have := hfmod p hp.1
    apply Nat.dvd_of_mod_eq_zero
    omega
  have hcard_le : O.card ≤ 1 := by
    by_contra h
    have h4 : 2 ^ 2 ∣ 2 * n := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    omega
  -- |O| = 0 would make sigma n odd.
  have hcard_pos : O.card ≠ 0 := by
    intro h0
    have hempty : ∀ p ∈ S, n.factorization p % 2 = 0 := by
      intro p hp
      by_contra hne
      have : p ∈ O := by
        rw [Finset.mem_filter]
        exact ⟨hp, by omega⟩
      rw [Finset.card_eq_zero] at h0
      rw [h0] at this
      simp at this
    have hprod : (∏ p ∈ S, f p) % 2 = 1 := by
      rw [Finset.prod_nat_mod]
      have : ∀ p ∈ S, f p % 2 = 1 := by
        intro p hp
        rw [hfmod p hp]
        have := hempty p hp
        omega
      rw [Finset.prod_congr rfl this]
      simp
    rw [← hσprod, hσ] at hprod
    omega
  have hcard : O.card = 1 := by omega
  -- The sum of the exponents is odd.
  have hsum : (∑ p ∈ S, n.factorization p) % 2 = 1 := by
    rw [Finset.sum_nat_mod]
    have : ∀ p ∈ S, n.factorization p % 2 =
        if n.factorization p % 2 = 1 then 1 else 0 := by
      intro p _
      split_ifs with h
      · exact h
      · omega
    rw [Finset.sum_congr rfl this, Finset.sum_boole]
    simp only [Nat.cast_id]
    rw [← hO, hcard]
  -- D n is odd.
  have hradodd : ∀ p ∈ S, (rad n / p) % 2 = 1 := by
    intro p hp
    have hd : rad n / p ∣ n := (Nat.div_dvd_of_dvd (dvd_rad hp)).trans (rad_dvd n)
    rcases Nat.mod_two_eq_zero_or_one (rad n / p) with h | h
    · exfalso
      have : 2 ∣ n := (Nat.dvd_of_mod_eq_zero h).trans hd
      omega
    · exact h
  have hD : D n % 2 = 1 := by
    unfold D
    rw [Finset.sum_nat_mod]
    have : ∀ p ∈ n.primeFactors, n.factorization p * (rad n / p) % 2 =
        n.factorization p % 2 := by
      intro p hp
      rw [Nat.mul_mod, hradodd p hp, mul_one, Nat.mod_mod]
    rw [Finset.sum_congr rfl this, ← Finset.sum_nat_mod]
    exact hsum
  -- P n is even.
  have hP : P n % 2 = 0 := by
    obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr (by omega : 1 < n)
    have hdv : p + 1 ∣ P n := Finset.dvd_prod_of_mem _ hp
    have h2 : 2 ∣ p + 1 := by
      have := hSodd p hp
      omega
    exact Nat.mod_eq_zero_of_dvd (h2.trans hdv)
  omega

lemma disjoint_main {n : ℕ} (perf : Nat.Perfect n) : D n ≠ P n := by
  rcases Nat.even_or_odd n with h | h
  · exact even_case h perf
  · exact odd_case (Nat.odd_iff.mp h) perf

/-! ### The conjecture -/

theorem conjecture : A345003 = A000396 ∪ A301939 ∧ Disjoint A000396 A301939 := by
  constructor
  · ext k
    simp only [A345003, A000396, A301939, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨hk, h⟩
      rcases (mem_A345003_iff hk).mp h with h1 | h1
      · right
        exact ⟨hk, (deriv_eq_psi_iff hk).mpr h1⟩
      · left
        exact (perfect_iff hk).mpr h1
    · rintro (h | ⟨hk, h⟩)
      · exact ⟨h.2, (mem_A345003_iff h.2).mpr (Or.inr ((perfect_iff h.2).mp h))⟩
      · exact ⟨hk, (mem_A345003_iff hk).mpr (Or.inl ((deriv_eq_psi_iff hk).mp h))⟩
  · rw [Set.disjoint_left]
    intro k hk hk'
    simp only [A000396, A301939, Set.mem_setOf_eq] at hk hk'
    exact disjoint_main hk ((deriv_eq_psi_iff hk'.1).mp hk'.2)

/-! ### Controls from the entries -/

lemma deriv_eight : deriv 8 = 12 := by
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
  unfold deriv
  rw [Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Finset.sum_singleton,
    Nat.Prime.factorization_pow Nat.prime_two]
  simp

lemma psi_eight : psi 8 = 12 := by
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
  unfold psi
  rw [Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Finset.prod_singleton]
  norm_num

/-- Controls: 6 (perfect) and 8 (8' = psi(8) = 12) are terms of A345003, as in its data;
1 is not, since A344998(1) = 0 and A344999(1) = -1. -/
lemma controls : 6 ∈ A345003 ∧ 8 ∈ A345003 ∧ 1 ∉ A345003 := by
  have hu := conjecture.1
  refine ⟨?_, ?_, ?_⟩
  · rw [hu]
    left
    show Nat.Perfect 6
    rw [Nat.perfect_iff_sum_divisors_eq_two_mul (by norm_num)]
    decide
  · rw [hu]
    right
    refine ⟨by norm_num, ?_⟩
    rw [deriv_eight, psi_eight]
    norm_num
  · rw [hu]
    rintro (h | ⟨-, h⟩)
    · exact absurd h (by
        rw [show (A000396 : Set ℕ) = {k | Nat.Perfect k} from rfl, Set.mem_setOf_eq,
          Nat.perfect_iff_sum_divisors_eq_two_mul (by norm_num)]
        decide)
    · have h0 : deriv 1 = 0 := by simp [deriv]
      have h1 : psi 1 = 1 := by simp [psi]
      rw [h0, h1] at h
      norm_num at h

end OMA.S_oeis_a345003

theorem OMA.solution : type_of% @OMA.S_oeis_a345003.main :=
  OMA.S_oeis_a345003.conjecture
