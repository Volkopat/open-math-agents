import OMAStatements.S_oeis_a064591

/-!
The weighted reciprocal condition proposed by Michel Lagneau in OEIS A064591.
Source: https://oeis.org/A064591
Credit: @anmolspace (reduction and Lean formalization). The upstream statement is by @divmxnd0x.
-/

namespace A064591Reciprocals

open Finset ArithmeticFunction OMA.S_oeis_a064591

private theorem even_double (m : ℕ) :
    ∑ d ∈ (2 * m).divisors.filter Even, (1 : ℚ) / d = (∑ d ∈ m.divisors, (1 : ℚ) / d) / 2 := by
  have hs : (2 * m).divisors.filter Even = m.divisors.image (2 * ·) := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, mem_image]
    constructor
    · rintro ⟨⟨hd, hn⟩, he⟩
      obtain ⟨t, rfl⟩ := even_iff_two_dvd.mp he
      exact ⟨t, ⟨(Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hd, by omega⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hm⟩, rfl⟩
      exact ⟨⟨Nat.mul_dvd_mul_left 2 ht, by omega⟩, even_iff_two_dvd.mpr ⟨t, rfl⟩⟩
  rw [hs, sum_image (by intro a _ b _ h; change 2 * a = 2 * b at h; omega), sum_div]
  apply sum_congr rfl
  intro d _
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

private theorem odd_double (m : ℕ) :
    ∑ d ∈ (2 * m).divisors.filter Odd, (1 : ℚ) / d = ∑ d ∈ m.divisors.filter Odd, (1 : ℚ) / d := by
  have hs : (2 * m).divisors.filter Odd = m.divisors.filter Odd := by
    ext d
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, hn⟩, ho⟩
      exact ⟨⟨ho.coprime_two_right.dvd_of_dvd_mul_left hd, by omega⟩, ho⟩
    · rintro ⟨⟨hd, hn⟩, ho⟩
      exact ⟨⟨dvd_mul_of_dvd_right hd 2, by omega⟩, ho⟩
  rw [hs]

private theorem separate (m : ℕ) :
    (∑ d ∈ m.divisors.filter Even, (1 : ℚ) / d) + (∑ d ∈ m.divisors.filter Odd, (1 : ℚ) / d) =
      ∑ d ∈ m.divisors, (1 : ℚ) / d := by
  simpa only [Nat.not_even_iff_odd] using
    sum_filter_add_sum_filter_not m.divisors Even (fun d => (1 : ℚ) / d)

private theorem weighted_double (m : ℕ) :
    2 * (∑ d ∈ (2 * m).divisors.filter Even, (1 : ℚ) / d) - (∑ d ∈ (2 * m).divisors.filter Odd, (1 : ℚ) / d) =
      ∑ d ∈ m.divisors.filter Even, (1 : ℚ) / d := by
  rw [even_double, odd_double]
  linarith [separate m]

private theorem even_of_odd {m : ℕ} (hm : Odd m) : (∑ d ∈ m.divisors.filter Even, (1 : ℚ) / d) = 0 := by
  apply sum_eq_zero
  intro d hd
  obtain ⟨hd, he⟩ := mem_filter.mp hd
  exact False.elim ((Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr
    (dvd_trans he.two_dvd (Nat.dvd_of_mem_divisors hd))))

private theorem reciprocal_perfect {m : ℕ} (hm : 0 < m) :
    (∑ d ∈ m.divisors, (1 : ℚ) / d) = 2 ↔ m.Perfect := by
  have hs : (m : ℚ) * (∑ d ∈ m.divisors, (1 : ℚ) / d) = (∑ d ∈ m.divisors, d : ℕ) := by
    rw [mul_sum, Nat.cast_sum, ← Nat.sum_div_divisors m (fun d => (d : ℚ))]
    apply sum_congr rfl
    intro d hd
    rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne')]
    ring
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hm]
  constructor
  · intro h
    rw [h] at hs
    exact_mod_cast (by linarith : (∑ d ∈ m.divisors, d : ℕ) = (2 : ℚ) * m)
  · intro h
    rw [h, Nat.cast_mul] at hs
    have hm' : (0 : ℚ) < m := by exact_mod_cast hm
    norm_num at hs ⊢
    nlinarith

/-- The weighted reciprocal criterion is exactly the condition that the input is four times
a perfect number. This classification is unconditional. -/
theorem weighted_iff (n : ℕ) (hn : 0 < n) :
    2 * (∑ d ∈ n.divisors.filter Even, (1 : ℚ) / d) -
      (∑ d ∈ n.divisors.filter Odd, (1 : ℚ) / d) = 1 ↔ ∃ m : ℕ, m.Perfect ∧ n = 4 * m := by
  constructor
  · intro h
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨m, rfl⟩ := even_iff_two_dvd.mp he
      rw [weighted_double] at h
      rcases Nat.even_or_odd m with hm | hm
      · obtain ⟨t, rfl⟩ := even_iff_two_dvd.mp hm
        rw [even_double] at h
        exact ⟨t, (reciprocal_perfect (by omega)).mp (by linarith), by omega⟩
      · rw [even_of_odd hm] at h
        norm_num at h
    · rw [even_of_odd ho] at h
      have hnonneg : 0 ≤ ∑ d ∈ n.divisors.filter Odd, (1 : ℚ) / d := sum_nonneg fun _ _ => by positivity
      linarith
  · rintro ⟨m, hm, rfl⟩
    rw [show 4 * m = 2 * (2 * m) by omega, weighted_double, even_double,
      (reciprocal_perfect hm.2).mpr hm]
    norm_num

/-- The odd part of an even perfect number is prime. The proof adapts Aaron Anderson's
Euclid–Euler theorem in `Archive.Wiedijk100Theorems.PerfectNumbers`. -/
private theorem even_perfect_odd_part {m : ℕ} (he : Even m) (hP : m.Perfect) :
    ∃ k p : ℕ, p.Prime ∧ m = 2^k * p := by
  obtain ⟨k, u, ho, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hP.2.ne'
  have hk : k ≠ 0 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr ho) (by simpa using he)
  have hm1 : 1 < mersenne (k + 1) := one_lt_mersenne.mpr (by omega)
  have hsig2 : sigma 1 (2^k) = mersenne (k + 1) := by
    simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
    norm_num
  have hEq : mersenne (k + 1) * sigma 1 u = (mersenne (k + 1) + 1) * u := by
    have h := (Nat.perfect_iff_sum_divisors_eq_two_mul hP.2).mp hP
    rw [← sigma_one_apply, isMultiplicative_sigma.map_mul_of_coprime (ho.coprime_two_left.pow_left _),
      hsig2, ← mul_assoc, ← pow_succ'] at h
    rwa [succ_mersenne]
  have hdiv : mersenne (k + 1) ∣ u :=
    (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)).dvd_of_dvd_mul_left ⟨_, hEq.symm⟩
  obtain ⟨j, rfl⟩ := hdiv
  have hsig : sigma 1 (mersenne (k + 1) * j) = (mersenne (k + 1) + 1) * j := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < mersenne (k + 1))
    rw [hEq]
    ring
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self] at hsig
  have hsum : ∑ d ∈ (mersenne (k + 1) * j).properDivisors, d = j := by nlinarith
  have hd : (∑ d ∈ (mersenne (k + 1) * j).properDivisors, d) ∣ mersenne (k + 1) * j := by
    rw [hsum]
    exact dvd_mul_left _ _
  rcases Nat.sum_properDivisors_dvd hd with ha | ha
  · have hj : j = 1 := hsum.symm.trans ha
    subst j
    simp only [mul_one] at ha ⊢
    exact ⟨k, mersenne (k + 1), Nat.sum_properDivisors_eq_one_iff_prime.mp ha, rfl⟩
  · have hj : j = mersenne (k + 1) * j := hsum.symm.trans ha
    have hjpos : 0 < j := by by_contra! h; interval_cases j; simp at ho
    nlinarith

private theorem doubles_subset {m : ℕ} (hm : 0 < m) :
    m.divisors.image (2 * ·) ⊆ (4 * m).divisors.filter (fun d => 1 < Nat.gcd d (4 * m / d)) := by
  intro x hx
  obtain ⟨d, hd, rfl⟩ := mem_image.mp hx
  have hdpos := Nat.pos_of_mem_divisors hd
  obtain ⟨t, ht⟩ := Nat.dvd_of_mem_divisors hd
  have hfac : 4 * m = (2 * d) * (2 * t) := by rw [ht]; ring
  apply mem_filter.mpr
  refine ⟨Nat.mem_divisors.mpr ⟨⟨2 * t, hfac⟩, by positivity⟩, ?_⟩
  rw [hfac, Nat.mul_div_cancel_left _ (by positivity : 0 < 2 * d), Nat.gcd_mul_left]
  have hg := Nat.gcd_pos_of_pos_left t hdpos
  omega

/-- The previously known direction of the nonunitary-perfect-number classification:
four times any even perfect number is nonunitary perfect. -/
theorem four_even_perfect {m : ℕ} (he : Even m) (hP : m.Perfect) : IsNonunitaryPerfect (4 * m) := by
  obtain ⟨k, p, hp, hm⟩ := even_perfect_odd_part he hP
  have hmpos := hP.2
  have hset : (4 * m).divisors.filter (fun d => 1 < Nat.gcd d (4 * m / d)) = m.divisors.image (2 * ·) := by
    apply Subset.antisymm _ (doubles_subset hmpos)
    intro d hd
    obtain ⟨hd, hg⟩ := mem_filter.mp hd
    have hdn := Nat.dvd_of_mem_divisors hd
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (by omega : Nat.gcd d (4 * m / d) ≠ 1)
    have hqd := dvd_trans hqdvd (Nat.gcd_dvd_left _ _)
    have hqc := dvd_trans hqdvd (Nat.gcd_dvd_right _ _)
    have h2 : q = 2 := by
      by_contra hne
      have hodd := hq.odd_of_ne_two hne
      have hqs : q^2 ∣ 4 * m := by
        simpa only [pow_two, Nat.div_mul_cancel hdn] using mul_dvd_mul hqc hqd
      rw [hm, show 4 * (2^k * p) = 2^(k + 2) * p by rw [pow_add]; ring] at hqs
      have hqp : q^2 ∣ p := ((hodd.coprime_two_right.pow_left 2).pow_right (k + 2)).dvd_of_dvd_mul_left hqs
      have hqp' : q ∣ p := dvd_trans (dvd_pow_self q (by decide : 2 ≠ 0)) hqp
      have hqeq : q = p := ((Nat.dvd_prime hp).mp hqp').resolve_left hq.ne_one
      have hle := Nat.le_of_dvd hp.pos hqp
      have hlt := hq.one_lt
      nlinarith
    subst q
    obtain ⟨t, rfl⟩ := hqd
    obtain ⟨v, hv⟩ := hqc
    have htot : 4 * m = (2 * v) * (2 * t) := by rw [← hv, Nat.div_mul_cancel hdn]
    exact mem_image.mpr ⟨t, Nat.mem_divisors.mpr ⟨⟨v, by nlinarith⟩, hmpos.ne'⟩, rfl⟩
  refine ⟨by positivity, ?_⟩
  rw [nonunitarySigma, hset, sum_image (by intro a _ b _ h; change 2 * a = 2 * b at h; omega),
    ← mul_sum, (Nat.perfect_iff_sum_divisors_eq_two_mul hmpos).mp hP]
  omega

private theorem prime_sigma {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  simp [sigma_one_apply, hp.divisors, hp.ne_one.symm, add_comm]

private theorem odd_divisor {a b : ℕ} (hb : Odd b) (h : a ∣ b) : Odd a := by
  apply Nat.not_even_iff_odd.mp
  intro ha
  exact (Nat.not_even_iff_odd.mpr hb) <| even_iff_two_dvd.mpr (dvd_trans ha.two_dvd h)

private theorem two_dvd_sigma {m : ℕ} (hm : Odd m) (hs : Squarefree m) (h1 : m ≠ 1) :
    2 ∣ sigma 1 m := by
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd h1
  have hodd := odd_divisor hm hd
  obtain ⟨t, rfl⟩ := hd
  rw [isMultiplicative_sigma.map_mul_of_coprime (Nat.coprime_of_squarefree_mul hs), prime_sigma hp]
  exact dvd_mul_of_dvd_left (by obtain ⟨j, hj⟩ := hodd; exact ⟨j + 1, by omega⟩) _

private theorem odd_perfect_not_squarefree {m : ℕ} (hm : Odd m) (hP : m.Perfect) : ¬ Squarefree m := by
  intro hs
  have h1 : m ≠ 1 := by rintro rfl; simp [Nat.Perfect] at hP
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd h1
  have hpo := odd_divisor hm hd
  obtain ⟨t, rfl⟩ := hd
  have ht1 : t ≠ 1 := by rintro rfl; exact hp.not_perfect (by simpa using hP)
  have ht := two_dvd_sigma (odd_divisor hm (dvd_mul_left t p)) hs.of_mul_right ht1
  have hp2 : 2 ∣ p + 1 := by obtain ⟨j,hj⟩ := hpo; exact ⟨j + 1, by omega⟩
  have h4 : 4 ∣ sigma 1 (p * t) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime (Nat.coprime_of_squarefree_mul hs), prime_sigma hp]
    exact Nat.mul_dvd_mul hp2 ht
  rw [sigma_one_apply, (Nat.perfect_iff_sum_divisors_eq_two_mul hP.2).mp hP] at h4
  obtain ⟨k, hk⟩ := hm
  omega

/-- A hypothetical odd perfect number produces a counterexample to Lagneau's conjecture. -/
theorem odd_perfect_counterexample {m : ℕ} (hm : Odd m) (hP : m.Perfect) :
    ¬ IsNonunitaryPerfect (4 * m) := by
  have hsq := odd_perfect_not_squarefree hm hP
  rw [Nat.squarefree_iff_prime_squarefree] at hsq
  push Not at hsq
  obtain ⟨p, hp, hpp⟩ := hsq
  have hpm : p ∣ m := dvd_trans (dvd_mul_right p p) hpp
  have hpo := odd_divisor hm hpm
  let A := m.divisors.image (2 * ·)
  let B := (4 * m).divisors.filter (fun d => 1 < Nat.gcd d (4 * m / d))
  have hmpos := hP.2
  have hab : A ⊆ B := doubles_subset hmpos
  have hpB : p ∈ B := by
    obtain ⟨t, ht⟩ := hpp
    have hfac : 4 * m = p * (p * (4 * t)) := by rw [ht]; ring
    apply mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨⟨p * (4 * t), hfac⟩, by positivity⟩, ?_⟩
    rw [hfac, Nat.mul_div_cancel_left _ hp.pos, Nat.gcd_eq_left (dvd_mul_right _ _)]
    exact hp.one_lt
  have hpA : p ∉ A := by
    intro h
    obtain ⟨d, _, hd⟩ := mem_image.mp h
    exact (Nat.not_even_iff_odd.mpr hpo) (even_iff_two_dvd.mpr ⟨d, hd.symm⟩)
  have hle : (∑ d ∈ insert p A, d) ≤ ∑ d ∈ B, d := by
    apply sum_le_sum_of_subset_of_nonneg (insert_subset hpB hab)
    intros
    omega
  rw [sum_insert hpA] at hle
  dsimp only [A] at hle
  rw [sum_image (by intro a _ b _ h; change 2 * a = 2 * b at h; omega),
    ← mul_sum, (Nat.perfect_iff_sum_divisors_eq_two_mul hmpos).mp hP] at hle
  rintro ⟨_, heq⟩
  change (∑ d ∈ B, d) = 4 * m at heq
  have hp0 := hp.pos
  omega

end A064591Reciprocals

namespace OMA.R_oeis_a064591_R1

open OMA.S_oeis_a064591 A064591Reciprocals

/-- There are no odd perfect numbers. -/
def H1 : Prop := ∀ m : ℕ, Odd m → ¬m.Perfect

/-- Every nonunitary perfect number is four times an even perfect number. -/
def H2 : Prop := ∀ n : ℕ, IsNonunitaryPerfect n → ∃ m : ℕ, Even m ∧ m.Perfect ∧ n = 4 * m

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a064591.main := by
  intro noOdd classified n hn
  rw [weighted_iff n hn]
  constructor
  · intro h
    obtain ⟨m, _, hP, rfl⟩ := classified n h
    exact ⟨m, hP, rfl⟩
  · rintro ⟨m, hP, rfl⟩
    rcases Nat.even_or_odd m with he | ho
    · exact four_even_perfect he hP
    · exact False.elim (noOdd m ho hP)

/-- Both open conditions in the reduction are also necessary. -/
theorem equivalent : (type_of% @OMA.S_oeis_a064591.main) ↔ H1 ∧ H2 := by
  constructor
  · intro h
    have noOdd : H1 := by
      intro m ho hP
      have hm := hP.2
      apply odd_perfect_counterexample ho hP
      exact (h (4 * m) (by omega)).mpr ((weighted_iff (4 * m) (by omega)).mpr ⟨m, hP, rfl⟩)
    refine ⟨noOdd, ?_⟩
    intro n hN
    obtain ⟨m, hP, rfl⟩ := (weighted_iff n hN.1).mp ((h n hN.1).mp hN)
    rcases Nat.even_or_odd m with he | ho
    · exact ⟨m, he, hP, rfl⟩
    · exact False.elim (noOdd m ho hP)
  · rintro ⟨noOdd, classified⟩
    exact main noOdd classified

end OMA.R_oeis_a064591_R1
