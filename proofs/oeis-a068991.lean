import OMAStatements.S_oeis_a068991

/-! Integrality gives a product divisibility condition. Its two-adic budget
excludes even a single predecessor divisible by eight, by descending through
the prime factors of the predecessors. Von Staudt–Clausen then applies. -/

namespace A068991Proof

open OMA.S_oeis_a068991 Nat Finset ArithmeticFunction

private theorem two_pow_mul_fact {n : ℕ} (hn : n ≠ 0) (k q : ℕ) :
    (2^k*n).factorization q = (if q = 2 then k else 0)+n.factorization q := by
  rw [Nat.factorization_mul (by positivity) hn, Nat.prime_two.factorization_pow,
    Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> simp_all

private theorem extend_small_factors (m : ℕ) (hm : m ≠ 0)
    (hsub : m.primeFactors ⊆ ({2,3,7}:Finset ℕ)) :
    m = 2^m.factorization 2 * 3^m.factorization 3 * 7^m.factorization 7 := by
  have h := Nat.prod_primeFactors_pow_factorization hm
  have he : (∏ q ∈ m.primeFactors, q^m.factorization q) =
      ∏ q ∈ ({2,3,7}:Finset ℕ), q^m.factorization q := by
    apply Finset.prod_subset hsub
    intro q hq hnot
    rw [show m.factorization q = 0 by
      simpa only [← Nat.support_factorization, Finsupp.notMem_support_iff] using hnot, pow_zero]
  rw [he] at h
  simpa [Finset.prod_insert, mul_assoc, mul_left_comm, mul_comm] using h

private theorem predecessors_dvd {n : ℕ} (hsq : Squarefree n)
    (hd : (∏ p ∈ n.primeFactors, (p-1)) ∣ 2^n.primeFactors.card * n) :
    ∀ q ∈ n.primeFactors, q-1 ∣ 2*n := by
  classical
  let S := n.primeFactors
  let U := S.erase 2
  let v := fun q : ℕ => (q-1).factorization 2
  let e := fun q : ℕ => v q - 1
  have hn := hsq.ne_zero
  have hP (q : ℕ) (hq : q ∈ S) : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hpred (q : ℕ) (hq : q ∈ S) : q-1 ≠ 0 := by have := (hP q hq).two_le; omega
  have hDne : (∏ q ∈ S, (q-1)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hpred
  have hW (p : ℕ) :
      (∑ q ∈ S, (q-1).factorization p) ≤ (if p=2 then S.card else 0) + n.factorization p := by
    have hh := (Nat.factorization_le_iff_dvd hDne (by positivity)).2 hd p
    rw [Nat.factorization_prod_apply hpred, two_pow_mul_fact hn] at hh
    exact hh
  have hSingle (q p : ℕ) (hq : q ∈ S) :
      (q-1).factorization p ≤ (if p=2 then S.card else 0) + n.factorization p :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hq).trans (hW p)
  have hOther (q p : ℕ) (hq : q ∈ S) (hp : p ≠ 2) :
      (q-1).factorization p ≤ n.factorization p := by simpa [hp] using hSingle q p hq
  have hv (q : ℕ) (hq : q ∈ U) : 1 ≤ v q := by
    obtain ⟨hq2,hqS⟩ := Finset.mem_erase.mp hq
    have hodd := ((hP q hqS).even_iff.not.mpr hq2)
    apply (Nat.prime_two.dvd_iff_one_le_factorization (hpred q hqS)).mp
    rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero] at hodd
    rw [Nat.dvd_iff_mod_eq_zero]
    have := (hP q hqS).two_le
    omega
  have hSumU : (∑ q ∈ U, v q) = ∑ q ∈ S, v q := by
    by_cases h2 : 2 ∈ S
    · have hh := Finset.sum_erase_add S v h2
      simpa [U,v] using hh
    · rw [show U = S from Finset.erase_eq_of_notMem h2]
  have hCard : S.card ≤ U.card + n.factorization 2 := by
    by_cases h2 : 2 ∈ S
    · have h2n : 1 ≤ n.factorization 2 := by
        apply Nat.pos_of_ne_zero
        change 2 ∈ n.factorization.support at h2
        exact Finsupp.mem_support_iff.mp h2
      have hs : U.card + 1 = S.card := by
        simpa [U] using Finset.card_erase_add_one h2
      omega
    · rw [show U = S from Finset.erase_eq_of_notMem h2]
      omega
  have hE : (∑ q ∈ U, e q) ≤ 2 * n.factorization 2 := by
    have he : (∑ q ∈ U, e q) + U.card = ∑ q ∈ U, v q := by
      have hu : (∑ q ∈ U, (1:ℕ)) = U.card := by simp
      rw [← hu, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      dsimp [e]
      exact Nat.sub_add_cancel (hv q hq)
    have hw := hW 2
    change (∑ q ∈ S, v q) ≤ S.card + n.factorization 2 at hw
    omega
  have hOddBound (p : ℕ) (hp : p ≠ 2) :
      (∑ q ∈ S, (q-1).factorization p) ≤ 1 := by
    have hw := hW p
    simp only [if_neg hp, zero_add] at hw
    exact hw.trans (hsq.natFactorization_le_one _)
  have hOddSupport (q p : ℕ) (hq : q ∈ S) (hp : p ≠ 2) (hpm : p ∈ (q-1).primeFactors) :
      p ∈ S := by
    change p ∈ (q-1).factorization.support at hpm
    change p ∈ n.factorization.support
    rw [Finsupp.mem_support_iff] at hpm ⊢
    have hh := hOther q p hq hp
    omega
  have hNoThree (q : ℕ) (hq : q ∈ U) : v q ≤ 2 := by
    by_contra! hq3
    have hqS := (Finset.mem_erase.mp hq).2
    have heq : e q ≤ ∑ p ∈ U, e p :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hq
    have hn2 := hsq.natFactorization_le_one 2
    have hqval : v q = 3 := by change v q - 1 ≤ _ at heq; omega
    have hrest (p : ℕ) (hp : p ∈ U) (hneq : p ≠ q) : v p = 1 := by
      have hsum := Finset.sum_erase_add U e hq
      have hl : e p ≤ ∑ a ∈ U.erase q, e a :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hneq,hp⟩)
      have hvp := hv p hp
      change v p - 1 ≤ _ at hl
      change (∑ a ∈ U.erase q, e a) + (v q - 1) = ∑ a ∈ U, e a at hsum
      omega
    have hsmall : ∀ p < q, p ∈ S → p = 2 ∨ p = 3 ∨ p = 7 := by
      intro p
      induction p using Nat.strong_induction_on with
      | h p ih =>
        intro hpq hpS
        by_cases hp2 : p = 2
        · exact Or.inl hp2
        have hpU : p ∈ U := Finset.mem_erase.mpr ⟨hp2,hpS⟩
        have hfac2 : (p-1).factorization 2 = 1 := hrest p hpU (by omega)
        have hsub : (p-1).primeFactors ⊆ ({2,3,7}:Finset ℕ) := by
          intro j hj
          by_cases hj2 : j = 2
          · simp [hj2]
          have hjp : j < p := by
            have := Nat.le_of_mem_primeFactors hj
            have := (hP p hpS).two_le
            omega
          have h := ih j hjp (by omega) (hOddSupport p j hpS hj2 hj)
          simpa using h
        have hex := extend_small_factors (p-1) (hpred p hpS) hsub
        have h3 := (hOther p 3 hpS (by decide)).trans (hsq.natFactorization_le_one 3)
        have h7 := (hOther p 7 hpS (by decide)).trans (hsq.natFactorization_le_one 7)
        rw [hfac2, pow_one] at hex
        have hposs : p=3 ∨ p=7 ∨ p=15 ∨ p=43 := by
          interval_cases h3v : (p-1).factorization 3 <;>
            interval_cases h7v : (p-1).factorization 7 <;>
            norm_num at hex <;> omega
        rcases hposs with rfl|rfl|rfl|rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
        · exact False.elim ((by decide : ¬Nat.Prime 15) (hP 15 hpS))
        · have h7m : 7 ∈ (43-1 : ℕ).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨by decide, by decide, by decide⟩
          have h7S : 7 ∈ S := hOddSupport 43 7 hpS (by decide) h7m
          have hh := hOddBound 3 (by decide)
          have hl : (7-1 : ℕ).factorization 3 ≤ ∑ u ∈ S.erase 43, (u-1).factorization 3 :=
            Finset.single_le_sum (fun u _ => Nat.zero_le ((u-1).factorization 3))
              (Finset.mem_erase.mpr ⟨(by decide : (7:ℕ) ≠ 43), h7S⟩)
          have he := Finset.sum_erase_add S (fun u : ℕ => (u-1).factorization 3) hpS
          have f7 : 1 ≤ (7-1 : ℕ).factorization 3 :=
            (Nat.prime_three.dvd_iff_one_le_factorization (by decide)).mp (by decide)
          have f43 : 1 ≤ (43-1 : ℕ).factorization 3 :=
            (Nat.prime_three.dvd_iff_one_le_factorization (by decide)).mp (by decide)
          omega
    have hqsub : (q-1).primeFactors ⊆ ({2,3,7}:Finset ℕ) := by
      intro j hj
      by_cases hj2 : j = 2
      · simp [hj2]
      have hjq : j < q := by
        have := Nat.le_of_mem_primeFactors hj
        have := (hP q hqS).two_le
        omega
      have h := hsmall j hjq (hOddSupport q j hqS hj2 hj)
      simpa using h
    have hres := extend_small_factors (q-1) (hpred q hqS) hqsub
    have h3 := (hOther q 3 hqS (by decide)).trans (hsq.natFactorization_le_one 3)
    have h7 := (hOther q 7 hqS (by decide)).trans (hsq.natFactorization_le_one 7)
    change (q-1).factorization 2 = 3 at hqval
    rw [hqval] at hres
    have hposs : q = 9 ∨ q = 25 ∨ q = 57 ∨ q = 169 := by
      interval_cases h3v : (q-1).factorization 3 <;>
        interval_cases h7v : (q-1).factorization 7 <;> norm_num at hres <;> omega
    rcases hposs with rfl|rfl|rfl|rfl
    · exact (by decide : ¬Nat.Prime 9) (hP 9 hqS)
    · exact (by decide : ¬Nat.Prime 25) (hP 25 hqS)
    · exact (by decide : ¬Nat.Prime 57) (hP 57 hqS)
    · exact Nat.not_prime_of_dvd_of_lt (by decide : 13 ∣ 169)
        (by decide) (by decide) (hP 169 hqS)
  intro q hq
  apply (Nat.factorization_le_iff_dvd (hpred q hq) (by positivity)).1
  intro p
  rw [show (2*n).factorization p = (if p=2 then 1 else 0)+n.factorization p by
    simpa using two_pow_mul_fact hn 1 p]
  by_cases hp : p=2
  · subst p
    change v q ≤ 1 + n.factorization 2
    by_cases hq2 : q=2
    · subst q
      simp [v]
    have hqU : q ∈ U := Finset.mem_erase.mpr ⟨hq2,hq⟩
    have hno := hNoThree q hqU
    have he : e q ≤ ∑ j ∈ U, e j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hqU
    change v q - 1 ≤ _ at he
    omega
  · simpa [hp] using hOther q p hq hp


open scoped ArithmeticFunction.zeta

private noncomputable def ratio : ArithmeticFunction ℚ :=
  ⟨fun n => (ArithmeticFunction.sigma 1 n : ℚ) / (n.totient : ℚ), by simp⟩

private theorem ratio_mult : ratio.IsMultiplicative := by
  refine ⟨by norm_num [ratio], ?_⟩
  intro m n hc
  change (ArithmeticFunction.sigma 1 (m*n) : ℚ) / ((m*n).totient : ℚ) =
    (ArithmeticFunction.sigma 1 m : ℚ) / (m.totient : ℚ) *
      ((ArithmeticFunction.sigma 1 n : ℚ) / (n.totient : ℚ))
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc, Nat.totient_mul hc]
  push_cast
  exact mul_div_mul_comm _ _ _ _

private noncomputable def ratioSum : ArithmeticFunction ℚ :=
  (ζ : ArithmeticFunction ℚ) * ratio

private theorem ratioSum_apply (n : ℕ) :
    ratioSum n = ∑ d ∈ n.divisors, (ArithmeticFunction.sigma 1 d : ℚ) / (d.totient : ℚ) := by
  rw [ratioSum, ArithmeticFunction.coe_zeta_mul_apply]
  rfl

private theorem ratioSum_prime {p : ℕ} (hp : p.Prime) :
    ratioSum p = (2*(p:ℚ)) / ((p-1 : ℕ):ℚ) := by
  have hsig : ArithmeticFunction.sigma 1 p = 1+p := by
    simp [ArithmeticFunction.sigma_apply, hp.divisors, Ne.symm hp.ne_one]
  rw [ratioSum_apply, hp.divisors, Finset.sum_insert (by simpa using Ne.symm hp.ne_one),
      Finset.sum_singleton, hsig, Nat.totient_prime hp]
  norm_num
  push_cast [Nat.cast_sub hp.one_le]
  have hpq : (1:ℚ) < (p:ℚ) := by exact_mod_cast hp.one_lt
  have hne : ((p:ℚ)-1) ≠ 0 := by linarith
  field_simp [hne]
  ring

private theorem product_divisibility {n : ℕ} (hsq : Squarefree n) (hi : IntegralDivisorRatio n) :
    (∏ p ∈ n.primeFactors, (p-1)) ∣ 2^n.primeFactors.card*n := by
  have hmult : ratioSum.IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.natCast.mul ratio_mult
  have hp (p : ℕ) (hp : p ∈ n.primeFactors) : p.Prime := Nat.prime_of_mem_primeFactors hp
  obtain ⟨z, hz⟩ := hi
  rw [← ratioSum_apply, ← hmult.prod_primeFactors hsq] at hz
  have ht : (∏ p ∈ n.primeFactors, ratioSum p) =
      (2^n.primeFactors.card * (n:ℚ)) / ((∏ p ∈ n.primeFactors, (p-1) : ℕ) : ℚ) := by
    calc
      _ = ∏ p ∈ n.primeFactors, (2*(p:ℚ)) / ((p-1:ℕ):ℚ) :=
        Finset.prod_congr rfl fun p h => ratioSum_prime (hp p h)
      _ = _ := by
        rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
          ← Nat.cast_prod, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  rw [ht] at hz
  let m := ∏ p ∈ n.primeFactors, (p-1)
  have hm : m ≠ 0 := Finset.prod_ne_zero_iff.mpr
    fun p h => by have := (hp p h).two_le; omega
  have he := (eq_div_iff (Nat.cast_ne_zero.mpr hm)).mp hz
  apply Int.natCast_dvd_natCast.mp
  refine ⟨z, ?_⟩
  have hs : ((2^n.primeFactors.card*n : ℕ):ℤ) = (m:ℤ)*z := by
    exact_mod_cast (by simpa [m,mul_comm] using he.symm :
      ((2^n.primeFactors.card*n : ℕ):ℚ) = (m:ℚ)*(z:ℚ))
  exact hs

private theorem prime_dvd_bernoulli_den {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hd : p-1 ∣ 2*n) : p ∣ (bernoulli (2*n)).den := by
  classical
  let S := (range (2*n+2)).filter (fun q : ℕ => q.Prime ∧ q-1 ∣ 2*n)
  have hpm : p ∈ S := by
    have hl := Nat.le_of_dvd (by omega : 0 < 2*n) hd
    have h2 := hp.two_le
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), hp, hd⟩
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen n
  change (z:ℚ) = bernoulli (2*n) + ∑ q ∈ S, (1:ℚ)/q at hz
  have hs := Finset.sum_erase_add S (fun q : ℕ => (1:ℚ)/q) hpm
  let rest := ∑ q ∈ S.erase p, (1:ℚ)/q
  have heq : (1:ℚ)/p = (z:ℚ) - (bernoulli (2*n) + rest) := by
    change rest + (1:ℚ)/p = _ at hs
    linarith
  by_contra hbad
  have hBC : (bernoulli (2*n)).den.Coprime p :=
    ((hp.coprime_iff_not_dvd).mpr hbad).symm
  have hprod : (∏ q ∈ S.erase p, ((1:ℚ)/q).den).Coprime p := by
    apply Nat.Coprime.prod_left
    intro q hq
    obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hq
    have hqP := (Finset.mem_filter.mp hm).2.1
    rw [show ((1:ℚ)/q).den = q by simp [hqP.ne_zero]]
    exact (Nat.coprime_primes hqP hp).mpr hne
  have hRest : rest.den.Coprime p :=
    Nat.Coprime.of_dvd_left (Rat.den_sum_dvd_prod_den _ _) hprod
  have hBRest : (bernoulli (2*n)+rest).den.Coprime p :=
    Nat.Coprime.of_dvd_left (Rat.add_den_dvd _ _) (hBC.mul_left hRest)
  have hDiff : ((z:ℚ) - (bernoulli (2*n)+rest)).den.Coprime p :=
    Nat.Coprime.of_dvd_left (Rat.sub_den_dvd _ _) (by simpa using hBRest)
  rw [← heq, show ((1:ℚ)/p).den = p by simp [hp.ne_zero]] at hDiff
  change Nat.gcd p p = 1 at hDiff
  rw [Nat.gcd_self] at hDiff
  exact hp.ne_one hDiff

end A068991Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a068991.main := by
  intro n hn hsq hh
  have hd := A068991Proof.product_divisibility hsq hh
  have he := A068991Proof.predecessors_dvd hsq hd
  apply (Nat.factorization_le_iff_dvd hsq.ne_zero (Rat.den_nz _)).mp
  intro p
  by_cases hp : p ∈ n.primeFactors
  · have hP := Nat.prime_of_mem_primeFactors hp
    have hdvd := A068991Proof.prime_dvd_bernoulli_den hn hP (he p hp)
    exact (hsq.natFactorization_le_one _).trans
      ((hP.dvd_iff_one_le_factorization (Rat.den_nz _)).mp hdvd)
  · change p ∉ n.factorization.support at hp
    rw [Finsupp.notMem_support_iff.mp hp]
    exact Nat.zero_le _
