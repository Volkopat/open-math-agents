import OMAStatements.S_oeis_a078615

-- Reduction oeis-a078615.R1
-- Credit: @yuka30240
-- See Broughan, De Koninck, Katai and Luca, J. Integer Seq. 15 (2012), 12.7.5,
-- Lemma 1 for the exponent patterns and Theorem 2 for the small-support case.

namespace OMA.R_oeis_a078615_R1

open ArithmeticFunction OMA.S_oeis_a078615

/-- Test the odd square cofactor and a divisor of four times its squared radical. -/
def H1 : Prop :=
  ∀ s d : ℕ, Odd s → let u := s ^ 2
    2 ≤ u.primeFactors.card → d ∣ 4 * a u → d % 8 = 4 → (d - 1).Prime → ¬ (d - 1) ∣ u →
    let t := (4 * a u / d) * (d - 1) ^ 2
    sigma 1 u ∣ t → ∀ j : ℕ, t / sigma 1 u + 1 ≠ 2 ^ (j + 2)

/-- Exclude a second odd prime with odd exponent using the same finite divisor test. -/
def H2 : Prop :=
  ∀ q b s d : ℕ, q.Prime → q % 4 = 1 → Odd s → ¬ q ∣ s →
    let u := q ^ (4 * b + 1) * s ^ 2
    2 ≤ u.primeFactors.card → d ∣ 4 * a u → d % 4 = 2 → (d - 1).Prime → ¬ (d - 1) ∣ u →
    let t := (4 * a u / d) * (d - 1) ^ 2
    sigma 1 u ∣ t → ∀ j : ℕ, t / sigma 1 u + 1 ≠ 2 ^ (j + 2)

lemma rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos fun _ hp => Nat.pos_of_mem_primeFactors hp

lemma a_mul_of_coprime {m n : ℕ} (hc : m.Coprime n) :
    a (m * n) = a m * a n := by
  simp only [a, rad, ← Nat.radical_eq_prod_primeFactors,
    UniqueFactorizationMonoid.radical_mul (Nat.coprime_iff_isRelPrime.mp hc), mul_pow]

lemma a_prime_pow {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) : a (p ^ e) = p ^ 2 := by
  simp [a, rad, Nat.primeFactors_pow p he, hp.primeFactors]

lemma a_prime {p : ℕ} (hp : p.Prime) : a p = p ^ 2 := by
  simp [a, rad, hp.primeFactors]

lemma sigma_prime {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  simpa [geom_sum_two] using (sigma_one_apply_prime_pow (i := 1) hp)

lemma lt_sigma {n : ℕ} (hn : 1 < n) : n < sigma 1 n := by
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have := Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _)
    (Nat.one_mem_properDivisors_iff_one_lt.mpr hn)
  change 1 ≤ ∑ d ∈ n.properDivisors, d at this
  omega

lemma a_dvd_of_no_simple_prime {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p ∈ n.primeFactors, n.factorization p ≠ 1) : a n ∣ n := by
  have ht (p) (hp : p ∈ n.primeFactors) : 2 ≤ n.factorization p := by
    have hpos := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn
      (Nat.dvd_of_mem_primeFactors hp)
    have := h p hp
    omega
  unfold a rad
  rw [← Finset.prod_pow]
  have hprod : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n :=
    Nat.prod_factorization_pow_eq_self hn
  conv_rhs => rw [← hprod]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun p hp => pow_dvd_pow p (ht p hp)

lemma geom_parity {p : ℕ} (hp : Odd p) (e : ℕ) :
    (∑ i ∈ Finset.range (e + 1), p ^ i) ≡ e + 1 [MOD 2] := by
  have h : p ≡ 1 [MOD 2] := Nat.odd_iff.mp hp
  simpa using Nat.ModEq.sum (s := Finset.range (e + 1)) (g := fun _ => 1)
    (fun i _ => by simpa using h.pow i)

lemma sigma_square_odd {m : ℕ} (hm : Odd m) : Odd (sigma 1 (m ^ 2)) := by
  have hn : m ^ 2 ≠ 0 := pow_ne_zero _ hm.pos.ne'
  rw [Nat.odd_iff, sigma_one_apply, Nat.sum_divisors hn]
  apply Nat.ModEq.prod_one
  intro p hp
  have hop := Odd.of_dvd_nat (hm.pow (n := 2)) (Nat.dvd_of_mem_primeFactors hp)
  have he := geom_parity hop ((m ^ 2).factorization p)
  exact he.trans (by simp [Nat.ModEq, Nat.factorization_pow, Nat.add_mod])

lemma remove_simple_prime {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (he : n.factorization p = 1) :
    ∃ m : ℕ, n = p * m ∧ p.Coprime m := by
  refine ⟨ordCompl[p] n, ?_, Nat.coprime_ordCompl hp hn⟩
  simpa [he] using (Nat.ordProj_mul_ordCompl_eq_self n p).symm

lemma exists_odd_simple_prime {n : ℕ} (hn : 1 < n) (hsol : a n = sigma 1 n) :
    ∃ p ∈ n.primeFactors, Odd p ∧ n.factorization p = 1 := by
  have hn0 : n ≠ 0 := by omega
  have hlt : n < a n := hsol ▸ lt_sigma hn
  by_contra! hnone
  have htwo : n.factorization 2 = 1 := by
    by_contra h
    have hd := a_dvd_of_no_simple_prime hn0 (fun p hp => by
      rcases (Nat.prime_of_mem_primeFactors hp).eq_two_or_odd with rfl | hodd
      · exact h
      · exact hnone p hp (Nat.odd_iff.mpr hodd))
    exact (Nat.not_le_of_gt hlt) (Nat.le_of_dvd (by omega) hd)
  obtain ⟨m, rfl, hc⟩ := remove_simple_prime hn0 Nat.prime_two htwo
  have hm : Odd m := Nat.coprime_two_left.mp hc
  have hd : a m ∣ m := a_dvd_of_no_simple_prime hm.pos.ne' (by
    intro p hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have hop := hm.of_dvd_nat hdvd
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hmem := hp'.mem_primeFactors (hdvd.trans (dvd_mul_left m 2)) hn0
    have hne : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hop
    simpa [Nat.factorization_mul (by decide : 2 ≠ 0) hm.pos.ne',
      Nat.prime_two.factorization, Ne.symm hne] using hnone p hmem hop)
  rw [a_mul_of_coprime hc, a_prime Nat.prime_two] at hlt hsol
  have heq : m = a m := by
    obtain ⟨k, hk⟩ := hd
    have ha : 0 < a m := pow_pos (rad_pos _) _
    have hkpos : 0 < k := Nat.pos_of_mul_pos_left (hk ▸ hm.pos)
    have hklt : k < 2 := by
      by_contra! hge
      have := Nat.mul_le_mul_left (a m) hge
      omega
    have : k = 1 := by omega
    simpa [this] using hk
  have hodd : Odd (sigma 1 m) := by
    have hs : Odd (rad m) := hm.of_dvd_nat (Nat.prod_primeFactors_dvd m)
    rw [heq]
    exact sigma_square_odd hs
  rw [isMultiplicative_sigma.map_mul_of_coprime hc, sigma_prime Nat.prime_two] at hsol
  obtain ⟨b, hb⟩ := hodd
  omega

lemma square_of_even_exponents {u : ℕ} (hu : Odd u)
    (he : ∀ q ∈ u.primeFactors, u.factorization q % 2 = 0) :
    ∃ s : ℕ, Odd s ∧ u = s ^ 2 := by
  let s := ∏ q ∈ u.primeFactors, q ^ (u.factorization q / 2)
  have hs : u = s ^ 2 := by
    unfold s
    rw [← Finset.prod_pow]
    refine (Nat.prod_primeFactors_pow_factorization hu.pos.ne').trans ?_
    apply Finset.prod_congr rfl
    intro q hq
    rw [← pow_mul]
    have := he q hq
    congr 1
    omega
  exact ⟨s, hu.of_dvd_nat (hs ▸ dvd_pow_self s (by decide : 2 ≠ 0)), hs⟩

lemma square_of_sigma_odd {u : ℕ} (hu : Odd u) (hsig : Odd (sigma 1 u)) :
    ∃ s : ℕ, Odd s ∧ u = s ^ 2 := by
  apply square_of_even_exponents hu
  intro q hq
  have hdiv : (∑ i ∈ Finset.range (u.factorization q + 1), q ^ i) ∣ sigma 1 u := by
    rw [sigma_one_apply, Nat.sum_divisors hu.pos.ne']
    exact Finset.dvd_prod_of_mem _ hq
  have hval := Nat.odd_iff.mp (hsig.of_dvd_nat hdiv)
  have hpar := geom_parity (hu.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)) (u.factorization q)
  unfold Nat.ModEq at hpar
  omega

lemma succ_dvd_geom_pairs (q k : ℕ) : q + 1 ∣ ∑ i ∈ Finset.range (2 * k), q ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨z, hz⟩ := ih
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, hz, pow_succ]
    exact ⟨z + q ^ (2 * k), by ring⟩

lemma single_odd_exponent {u : ℕ} (hu : Odd u) (hsig : sigma 1 u % 4 = 2) :
    ∃ q b s : ℕ, q.Prime ∧ q % 4 = 1 ∧ Odd s ∧ ¬ q ∣ s ∧
      u = q ^ (4 * b + 1) * s ^ 2 := by
  have hex : ∃ q ∈ u.primeFactors, u.factorization q % 2 = 1 := by
    by_contra! h
    obtain ⟨s, hs, hu'⟩ := square_of_even_exponents hu (fun q hq => by
      have := h q hq
      omega)
    have hh := Nat.odd_iff.mp (sigma_square_odd hs)
    rw [hu'] at hsig
    omega
  obtain ⟨q, hq, he⟩ := hex
  let e := u.factorization q
  let v := ordCompl[q] u
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqo := hu.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
  have hvo : Odd v := hu.of_dvd_nat (Nat.ordCompl_dvd u q)
  have hc : q.Coprime v := Nat.coprime_ordCompl hqp hu.pos.ne'
  have huv : q ^ e * v = u := Nat.ordProj_mul_ordCompl_eq_self u q
  have hprod : sigma 1 (q ^ e) * sigma 1 v = sigma 1 u := by
    rw [← isMultiplicative_sigma.map_mul_of_coprime (hc.pow_left e), huv]
  have hpair : q + 1 ∣ sigma 1 (q ^ e) := by
    rw [sigma_one_apply_prime_pow hqp]
    have hx : e + 1 = 2 * ((e + 1) / 2) := by dsimp [e]; omega
    rw [hx]
    exact succ_dvd_geom_pairs _ _
  have h2 : 2 ∣ sigma 1 (q ^ e) := dvd_trans (by have := Nat.odd_iff.mp hqo; omega) hpair
  have h4 : ¬ 4 ∣ sigma 1 u := by omega
  have hq4 : q % 4 = 1 := by
    have hn : ¬ 4 ∣ q + 1 := fun h => h4 (h.trans (hpair.trans
      (hprod ▸ dvd_mul_right (sigma 1 (q ^ e)) (sigma 1 v))))
    have := Nat.odd_iff.mp hqo
    omega
  have hvso : Odd (sigma 1 v) := by
    rw [Nat.odd_iff]
    by_contra h
    have hv2 : 2 ∣ sigma 1 v := by omega
    have := mul_dvd_mul h2 hv2
    rw [hprod] at this
    exact h4 this
  have he4 : e % 4 = 1 := by
    have hmod : q ≡ 1 [MOD 4] := hq4
    have hsum : sigma 1 (q ^ e) ≡ e + 1 [MOD 4] := by
      rw [sigma_one_apply_prime_pow hqp]
      simpa using Nat.ModEq.sum (s := Finset.range (e + 1)) (g := fun _ => 1)
        (fun i _ => by simpa using hmod.pow i)
    have hnd : ¬ 4 ∣ sigma 1 (q ^ e) := fun h => h4 (h.trans
      (hprod ▸ dvd_mul_right (sigma 1 (q ^ e)) (sigma 1 v)))
    unfold Nat.ModEq at hsum
    omega
  obtain ⟨s, hs, hvs⟩ := square_of_sigma_odd hvo hvso
  refine ⟨q, e / 4, s, hqp, hq4, hs, ?_, ?_⟩
  · intro hqs
    apply hqp.coprime_iff_not_dvd.mp hc
    exact hvs ▸ hqs.trans (dvd_pow_self s (by decide : 2 ≠ 0))
  · have heq : 4 * (e / 4) + 1 = e := by omega
    rw [heq, ← hvs, huv]

lemma sigma_two_pow_add_one (e : ℕ) : sigma 1 (2 ^ e) + 1 = 2 ^ (e + 1) := by
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  simpa using geom_sum_mul_add (1 : ℕ) (e + 1)

lemma odd_a {u : ℕ} (hu : Odd u) : Odd (a u) :=
  (hu.of_dvd_nat (Nat.prod_primeFactors_dvd u)).pow

/-- Strip the odd prime of exponent one and the full power of two. -/
lemma solution_parameters {n : ℕ} (hn : 1 < n) (hsol : a n = sigma 1 n) :
    ∃ p e u : ℕ, p.Prime ∧ Odd p ∧ Odd u ∧ ¬ p ∣ u ∧ n = p * (2 ^ (e + 1) * u) ∧
      4 * (a u * p ^ 2) = (p + 1) * sigma 1 (2 ^ (e + 1)) * sigma 1 u := by
  obtain ⟨p, hmem, hop, he⟩ := exists_odd_simple_prime hn hsol
  have hp := Nat.prime_of_mem_primeFactors hmem
  obtain ⟨m, rfl, hc⟩ := remove_simple_prime (by omega) hp he
  rw [isMultiplicative_sigma.map_mul_of_coprime hc, sigma_prime hp] at hsol
  have hme : 2 ∣ m := by
    by_contra h
    have hm : Odd m := Nat.odd_iff.mpr (by omega)
    have hh := Nat.odd_iff.mp (odd_a (hop.mul hm))
    have hd : 2 ∣ p + 1 := by have := Nat.odd_iff.mp hop; omega
    have hdiv := hd.trans (dvd_mul_right (p + 1) (sigma 1 m))
    rw [← hsol] at hdiv
    omega
  obtain ⟨k, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := m) (by rintro rfl; simp at hn)
  cases k with
  | zero =>
    simp only [pow_zero, one_mul] at hme
    have := Nat.odd_iff.mp hu
    omega
  | succ e =>
    have hcu := (Nat.coprime_two_left.mpr hu).pow_left (e + 1)
    have hpu : ¬ p ∣ u := hp.coprime_iff_not_dvd.mp (hc.coprime_dvd_right (dvd_mul_left u _))
    refine ⟨p, e, u, hp, hop, hu, hpu, rfl, ?_⟩
    rw [a_mul_of_coprime hc, a_mul_of_coprime hcu, a_prime hp,
      a_prime_pow Nat.prime_two (Nat.succ_ne_zero _),
      isMultiplicative_sigma.map_mul_of_coprime hcu] at hsol
    calc
      4 * (a u * p ^ 2) = p ^ 2 * (2 ^ 2 * a u) := by ring
      _ = _ := hsol.trans (mul_assoc _ _ _).symm

lemma valuation_zero_of_odd {n : ℕ} (hn : Odd n) : n.factorization 2 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd (by have := Nat.odd_iff.mp hn; omega)

lemma split_two_valuation {r d t s : ℕ} (hr : Odd r) (ht : Odd t)
    (hd : 0 < d) (hs : 0 < s) (hde : 2 ∣ d) (h : 4 * r = d * t * s) :
    (d % 8 = 4 ∧ Odd s) ∨ (d % 4 = 2 ∧ s % 4 = 2) := by
  have hv := congrArg (fun n : ℕ => n.factorization 2) h
  have h4 : (4 : ℕ).factorization 2 = 2 := by
    change ((2 : ℕ) ^ 2).factorization 2 = 2
    rw [Nat.prime_two.factorization_pow, Finsupp.single_eq_same]
  simp only [Nat.factorization_mul (by decide : 4 ≠ 0) hr.pos.ne',
    Nat.factorization_mul (mul_ne_zero hd.ne' ht.pos.ne') hs.ne',
    Nat.factorization_mul hd.ne' ht.pos.ne', Finsupp.add_apply, valuation_zero_of_odd hr,
    valuation_zero_of_odd ht, h4, Nat.add_zero] at hv
  have hvd := (Nat.prime_two.dvd_iff_one_le_factorization hd.ne').mp hde
  have hd4 : 4 ∣ d ↔ 2 ≤ d.factorization 2 := Nat.prime_two.pow_dvd_iff_le_factorization (k := 2) hd.ne'
  have hd8 : 8 ∣ d ↔ 3 ≤ d.factorization 2 := Nat.prime_two.pow_dvd_iff_le_factorization (k := 3) hd.ne'
  have hs2 := Nat.prime_two.dvd_iff_one_le_factorization hs.ne'
  have hs4 : 4 ∣ s ↔ 2 ≤ s.factorization 2 := Nat.prime_two.pow_dvd_iff_le_factorization (k := 2) hs.ne'
  by_cases hdd : d.factorization 2 = 2
  · exact Or.inl ⟨by omega, Nat.odd_iff.mpr (by omega)⟩
  · exact Or.inr ⟨by omega, by omega⟩

/-- The divisor d determines the missing prime, and the quotient determines the power of two. -/
lemma divisor_test {p e u : ℕ} (hu : Odd u)
    (h : 4 * (a u * p ^ 2) = (p + 1) * sigma 1 (2 ^ (e + 1)) * sigma 1 u) :
    p + 1 ∣ 4 * a u ∧
    sigma 1 u ∣ (4 * a u / (p + 1)) * p ^ 2 ∧
    ((4 * a u / (p + 1)) * p ^ 2) / sigma 1 u + 1 = 2 ^ (e + 2) := by
  have heq : 4 * a u * p ^ 2 = (p + 1) * (sigma 1 (2 ^ (e + 1)) * sigma 1 u) := by
    simpa only [mul_assoc] using h
  have hc : (p + 1).Coprime p := by simp
  have hd := (hc.pow_right 2).dvd_of_dvd_mul_right (Dvd.intro _ heq.symm)
  have ht : (4 * a u / (p + 1)) * p ^ 2 = sigma 1 (2 ^ (e + 1)) * sigma 1 u := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos p)
    rwa [← mul_assoc, Nat.mul_div_cancel' hd]
  refine ⟨hd, ht ▸ dvd_mul_left _ _, ?_⟩
  rw [ht, Nat.mul_div_cancel _ (sigma_pos_iff.mpr hu.pos)]
  exact sigma_two_pow_add_one (e + 1)

/-- A passing divisor test reconstructs an actual solution. -/
lemma solution_of_divisor_test {p e u : ℕ} (hp : p.Prime) (hop : Odd p)
    (hu : Odd u) (hpu : ¬ p ∣ u) (hd : p + 1 ∣ 4 * a u)
    (hdiv : sigma 1 u ∣ (4 * a u / (p + 1)) * p ^ 2)
    (ht : ((4 * a u / (p + 1)) * p ^ 2) / sigma 1 u + 1 = 2 ^ (e + 2)) :
    a (p * (2 ^ (e + 1) * u)) = sigma 1 (p * (2 ^ (e + 1) * u)) := by
  have hquot : ((4 * a u / (p + 1)) * p ^ 2) / sigma 1 u = sigma 1 (2 ^ (e + 1)) :=
    Nat.add_right_cancel (ht.trans (sigma_two_pow_add_one (e + 1)).symm)
  have hprod : (4 * a u / (p + 1)) * p ^ 2 = sigma 1 (2 ^ (e + 1)) * sigma 1 u := by
    rw [← hquot, Nat.div_mul_cancel hdiv]
  have hc := ((Nat.coprime_two_right.mpr hop).pow_right (e + 1)).mul_right
    (hp.coprime_iff_not_dvd.mpr hpu)
  have hcu := (Nat.coprime_two_left.mpr hu).pow_left (e + 1)
  rw [a_mul_of_coprime hc, a_mul_of_coprime hcu, a_prime hp,
    a_prime_pow Nat.prime_two (Nat.succ_ne_zero _), isMultiplicative_sigma.map_mul_of_coprime hc,
    isMultiplicative_sigma.map_mul_of_coprime hcu, sigma_prime hp, ← hprod, ← mul_assoc (p + 1),
    Nat.mul_div_cancel' hd]
  ring

lemma known_odd_cofactor {p e u : ℕ} (hp : p + 1 = 12) (hu : u = 81)
    (ht : ((4 * a u / (p + 1)) * p ^ 2) / sigma 1 u + 1 = 2 ^ (e + 2)) :
    p * (2 ^ (e + 1) * u) = 1782 := by
  have hp' : p = 11 := by omega
  subst p
  subst u
  have h81 : a 81 = 9 := a_prime_pow (p := 3) (e := 4) (by decide) (by decide)
  have hs81 : sigma 1 81 = 121 := by
    change sigma 1 (3 ^ 4) = 121
    rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
    decide
  rw [h81, hs81] at ht
  norm_num at ht
  have hpow : 2 ^ (e + 1) * 2 = 4 := by simpa only [pow_succ (2 : ℕ) (e + 1)] using ht.symm
  omega

lemma divisors_prime_square {q x : ℕ} (hq : q.Prime) (hx : x ∣ q ^ 2) :
    x = 1 ∨ x = q ∨ x = q ^ 2 := by
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow hq).mp hx
  interval_cases k <;> simp

lemma prime_below_half_successor {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hm : (p + 1) % 4 = 2) (hd : p + 1 ∣ 4 * q ^ 2) : q < p := by
  let c := (p + 1) / 2
  have hc : 2 * c = p + 1 := by dsimp [c]; omega
  have hco : Odd c := Nat.odd_iff.mpr (by dsimp [c]; omega)
  have hdiv : c ∣ 2 * q ^ 2 := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) (by
    rw [hc, ← mul_assoc]
    exact hd)
  have hqdiv := (Nat.coprime_two_right.mpr hco).dvd_of_dvd_mul_left hdiv
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  rcases divisors_prime_square hq hqdiv with h | h | h
  · omega
  · omega
  · nlinarith

lemma sigma_mod_prime_square {q k : ℕ} (hq : q.Prime) (hk : 0 < k) :
    sigma 1 (q ^ k) ≡ q + 1 [MOD q ^ 2] := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  clear hk
  rw [sigma_one_apply_prime_pow hq]
  induction l with
  | zero =>
    change (∑ i ∈ Finset.range 2, q ^ i) ≡ q + 1 [MOD q ^ 2]
    rw [geom_sum_two]
  | succ l ih =>
    rw [Finset.sum_range_succ]
    have hzero := Nat.modEq_zero_iff_dvd.mpr
      (pow_dvd_pow q (by omega : 2 ≤ l.succ.succ))
    simpa using ih.add hzero

lemma sigma_coprime_prime {q k : ℕ} (hq : q.Prime) :
    (sigma 1 (q ^ k)).Coprime q := by
  apply Nat.Coprime.symm
  apply hq.coprime_iff_not_dvd.mpr
  rw [sigma_one_apply_prime_pow hq]
  intro h
  have hsum := geom_sum_mul_add (q - 1) (k + 1)
  rw [Nat.sub_add_cancel hq.one_le] at hsum
  have hmul := dvd_mul_of_dvd_left h (q - 1)
  have hpow := dvd_pow_self q (by omega : k + 1 ≠ 0)
  rw [← hsum] at hpow
  exact hq.not_dvd_one ((Nat.dvd_add_right hmul).mp hpow)

lemma prime_of_sigma_square {p q k : ℕ} (hq : q.Prime) (hk : 0 < k)
    (hlin : p + 1 = 4 * q) (hs : sigma 1 (q ^ k) = p ^ 2) : q = 3 := by
  have he := sigma_mod_prime_square hq hk
  rw [hs] at he
  have hpoly : p ^ 2 + 8 * q = 16 * q ^ 2 + 1 := by
    nlinarith [congrArg (fun n : ℕ => n ^ 2) hlin]
  have h9 : 9 * q + 1 ≡ 0 + 1 [MOD q ^ 2] := calc
    9 * q + 1 = q + 1 + 8 * q := by omega
    _ ≡ p ^ 2 + 8 * q [MOD q ^ 2] := he.symm.add_right _
    _ = 16 * q ^ 2 + 1 := hpoly
    _ ≡ 0 + 1 [MOD q ^ 2] := (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left _ _)).add_right 1
  have hq9 : q ∣ 9 := Nat.dvd_of_mul_dvd_mul_left hq.pos (by
    simpa only [pow_two, mul_comm 9 q] using
      Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_right_cancel' 1 h9))
  rcases hq.dvd_mul.mp (show q ∣ 3 * 3 from hq9) with h | h <;>
    exact (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 3)).mp h

/-- In the square case with one odd cofactor prime, congruence modulo its square
forces that prime to divide nine. -/
lemma classify_square_prime_power {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqo : Odd q) (hk : 2 ≤ k) (hm : (p + 1) % 8 = 4)
    (hd : p + 1 ∣ 4 * q ^ 2)
    (hs : sigma 1 (q ^ k) ∣ (4 * q ^ 2 / (p + 1)) * p ^ 2) :
    q ^ k = 81 ∧ p + 1 = 12 := by
  let c := (p + 1) / 4
  have hc : 4 * c = p + 1 := by dsimp [c]; omega
  have hcdiv : c ∣ q ^ 2 := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 4) (hc ▸ hd)
  have hq3 : 3 ≤ q := by have := hq.two_le; have := Nat.odd_iff.mp hqo; omega
  have hlow : 1 + q + q ^ 2 ≤ sigma 1 (q ^ k) := by
    rw [sigma_one_apply_prime_pow hq]
    have hh := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => q ^ i)
      (Finset.range_mono (by omega : 3 ≤ k + 1)) (fun _ _ _ => Nat.zero_le _)
    simpa [Finset.sum_range_succ] using hh
  have hcop := sigma_coprime_prime (k := k) hq
  rcases divisors_prime_square hq hcdiv with h1 | hq' | hsq
  · have hp3 : p = 3 := by omega
    subst p
    simp at hs
    have hd9 := (hcop.pow_right 2).dvd_of_dvd_mul_left hs
    have hh := Nat.le_of_dvd (by decide : 0 < 9) hd9
    nlinarith
  · have hlin : p + 1 = 4 * q := by omega
    have hquot : 4 * q ^ 2 / (p + 1) = q := by
      rw [hlin, Nat.mul_div_mul_left _ _ (by decide : 0 < 4), pow_two,
        Nat.mul_div_cancel _ hq.pos]
    rw [hquot] at hs
    have hd2 := hcop.dvd_of_dvd_mul_left hs
    rcases divisors_prime_square hp hd2 with h | h | h
    · omega
    · nlinarith [Nat.mul_le_mul_right q hq3]
    · obtain rfl := prime_of_sigma_square hq (by omega) hlin h
      have hp11 : p = 11 := by omega
      subst p
      have hsum := geom_sum_mul_add (2 : ℕ) (k + 1)
      change (∑ i ∈ Finset.range (k + 1), 3 ^ i) * 2 + 1 = 3 ^ (k + 1) at hsum
      rw [← sigma_one_apply_prime_pow (by decide : Nat.Prime 3), h] at hsum
      have hk5 : k + 1 = 5 := Nat.pow_right_injective (by decide : 2 ≤ 3) hsum.symm
      have hk4 : k = 4 := by omega
      simp [hk4]
  · have hpform : p + 1 = 4 * q ^ 2 := by omega
    have hz : 2 * q - 1 + 1 = 2 * q := by omega
    have hf : (2 * q - 1) * (2 * q + 1) = p := by
      nlinarith [congrArg (fun x : ℕ => x * (2 * q + 1)) hz]
    rcases hp.eq_one_or_self_of_dvd (2 * q - 1) ⟨_, hf.symm⟩ with h | h
    · omega
    · nlinarith

lemma parameter_parity {p e u : ℕ} (hop : Odd p) (hu : Odd u)
    (hbal : 4 * (a u * p ^ 2) = (p + 1) * sigma 1 (2 ^ (e + 1)) * sigma 1 u) :
    ((p + 1) % 8 = 4 ∧ Odd (sigma 1 u)) ∨ ((p + 1) % 4 = 2 ∧ sigma 1 u % 4 = 2) := by
  have hodd : Odd (sigma 1 (2 ^ (e + 1))) := by
    have hpow := sigma_two_pow_add_one (e + 1)
    rw [pow_succ (2 : ℕ) (e + 1)] at hpow
    exact Nat.odd_iff.mpr (by omega)
  have hd2 : 2 ∣ p + 1 := by have := Nat.odd_iff.mp hop; omega
  exact split_two_valuation ((odd_a hu).mul hop.pow) hodd (by omega)
    (sigma_pos_iff.mpr hu.pos) hd2 hbal

lemma classify_small_cofactor {p e u : ℕ} (hp : p.Prime) (hop : Odd p) (hu : Odd u)
    (hsmall : u.primeFactors.card ≤ 1)
    (hbal : 4 * (a u * p ^ 2) = (p + 1) * sigma 1 (2 ^ (e + 1)) * sigma 1 u) :
    p * (2 ^ (e + 1) * u) = 1782 := by
  obtain ⟨hd, hdiv, ht⟩ := divisor_test hu hbal
  by_cases hu1 : u = 1
  · subst u
    have hd4 : p + 1 ∣ 4 := by simpa [a, rad] using hd
    have := Nat.le_of_dvd (by decide : 0 < 4) hd4
    have hp3 : p = 3 := by have := hp.two_le; have := Nat.odd_iff.mp hop; omega
    subst p
    norm_num [a, rad] at ht
    have h4 : 4 ∣ 2 ^ (e + 2) := pow_dvd_pow 2 (by omega : 2 ≤ e + 2)
    omega
  have hnon := Nat.nonempty_primeFactors.mpr (show 1 < u by have := hu.pos; omega)
  have hcard : u.primeFactors.card = 1 := by have := Finset.card_pos.mpr hnon; omega
  obtain ⟨q, k, hq, hk, rfl⟩ :=
    (isPrimePow_nat_iff u).mp (isPrimePow_iff_card_primeFactors_eq_one.mpr hcard)
  have hqo := hu.of_dvd_nat (dvd_pow_self q hk.ne')
  have hpar := geom_parity hqo k
  rw [← sigma_one_apply_prime_pow hq] at hpar
  unfold Nat.ModEq at hpar
  rcases parameter_parity hop hu hbal with ⟨hd8, hsu⟩ | ⟨hd4, hsu⟩
  · have hk2 : 2 ≤ k := by have := Nat.odd_iff.mp hsu; omega
    rw [a_prime_pow hq hk.ne'] at hd hdiv
    obtain ⟨hu81, hd12⟩ := classify_square_prime_power hp hq hqo hk2 hd8 hd hdiv
    exact known_odd_cofactor hd12 hu81 ht
  · have hlen : k + 1 = 2 * ((k + 1) / 2) := by omega
    have hpair : q + 1 ∣ sigma 1 (q ^ k) := by
      rw [sigma_one_apply_prime_pow hq, hlen]
      exact succ_dvd_geom_pairs _ _
    have hq4 : (q + 1) % 4 = 2 := by
      have hh : ¬ 4 ∣ q + 1 := fun h => (show ¬ 4 ∣ sigma 1 (q ^ k) by omega) (h.trans hpair)
      have := Nat.odd_iff.mp hqo
      omega
    rw [a_prime_pow hq hk.ne'] at hd hbal
    have hcop : (q + 1).Coprime q := by simp
    have hrev : q + 1 ∣ 4 * p ^ 2 := (hcop.pow_right 2).dvd_of_dvd_mul_left (by
      rw [show q ^ 2 * (4 * p ^ 2) = 4 * (q ^ 2 * p ^ 2) by ring, hbal]
      exact hpair.trans (dvd_mul_left _ _))
    exact False.elim ((Nat.lt_asymm (prime_below_half_successor hp hq hd4 hd))
      (prime_below_half_successor hq hp hq4 hrev))

/-- Unconditionally classify solutions with at most three distinct prime factors. -/
lemma solutions_with_at_most_three_primes {n : ℕ} (hn : 1 < n) (hsmall : n.primeFactors.card ≤ 3)
    (hsol : a n = sigma 1 n) : n = 1782 := by
  obtain ⟨p, e, u, hp, hop, hu, hpu, rfl, hbal⟩ := solution_parameters hn hsol
  apply classify_small_cofactor hp hop hu _ hbal
  have h2 : 2 ∉ u.primeFactors := fun h =>
    (show ¬ 2 ∣ u by have := Nat.odd_iff.mp hu; omega) (Nat.dvd_of_mem_primeFactors h)
  have hpm : p ∉ u.primeFactors := fun h => hpu (Nat.dvd_of_mem_primeFactors h)
  have hne : p ≠ 2 := by have := Nat.odd_iff.mp hop; omega
  have hpos : 2 ^ (e + 1) * u ≠ 0 := mul_ne_zero (pow_ne_zero _ (by decide)) hu.pos.ne'
  rw [Nat.primeFactors_mul hp.ne_zero hpos,
    Nat.primeFactors_mul (pow_ne_zero _ (by decide)) hu.pos.ne',
    Nat.primeFactors_pow_succ, hp.primeFactors, Nat.prime_two.primeFactors] at hsmall
  have hpi : p ∉ insert 2 u.primeFactors := by simp [hne, hpm]
  simp only [Finset.singleton_union, Finset.card_insert_of_notMem hpi,
    Finset.card_insert_of_notMem h2] at hsmall
  omega

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a078615.main := by
  intro hsquare hsecond n hn
  constructor
  · intro hsol
    by_cases hn1 : n = 1
    · exact Or.inl hn1
    right
    obtain ⟨p, e, u, hp, hop, hu, hpu, rfl, hbal⟩ := solution_parameters (by omega) hsol
    obtain ⟨hd, hdiv, ht⟩ := divisor_test hu hbal
    by_cases hsmall : u.primeFactors.card ≤ 1
    · exact classify_small_cofactor hp hop hu hsmall hbal
    have hcard : 2 ≤ u.primeFactors.card := by omega
    rcases parameter_parity hop hu hbal with ⟨hd8, hsu⟩ | ⟨hd4, hsu⟩
    · obtain ⟨s, hs, rfl⟩ := square_of_sigma_odd hu hsu
      exact False.elim (hsquare s (p + 1) hs hcard hd hd8 (by simpa) (by simpa)
        (by simpa using hdiv) e (by simpa using ht))
    · obtain ⟨q, b, s, hq, hq4, hs, hqs, rfl⟩ := single_odd_exponent hu hsu
      exact False.elim (hsecond q b s (p + 1) hq hq4 hs hqs hcard hd hd4 (by simpa) (by simpa)
        (by simpa using hdiv) e (by simpa using ht))
  · rintro (rfl | rfl)
    · simp [a, rad]
    · change a (11 * (2 * 3 ^ 4)) = sigma 1 (11 * (2 * 3 ^ 4))
      have hc : Nat.Coprime 11 (2 * 3 ^ 4) := by decide
      have hc' : Nat.Coprime 2 (3 ^ 4) := by decide
      rw [a_mul_of_coprime hc, a_mul_of_coprime hc', a_prime (by decide : Nat.Prime 11),
        a_prime Nat.prime_two, a_prime_pow (by decide : Nat.Prime 3) (by decide : 4 ≠ 0),
        isMultiplicative_sigma.map_mul_of_coprime hc,
        isMultiplicative_sigma.map_mul_of_coprime hc', sigma_prime (by decide : Nat.Prime 11),
        sigma_prime Nat.prime_two, sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
      decide

end OMA.R_oeis_a078615_R1
