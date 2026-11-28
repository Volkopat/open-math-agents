import OMAStatements.S_oeis_a095380

-- Problem: A095380: density of non-sigma numbers in [1, 2^n] tends to 1
-- Upstream: statements/oeis-a095380.lean (declaration OMA.S_oeis_a095380.main)
-- Credit: @cgaray

open Filter Topology
open scoped Classical

namespace OMA_oeis_a095380

private lemma card_filter_dvd_Icc (d X : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 X).filter (fun k => d ∣ k)).card = X / d := by
  have hbij : ((Finset.Icc 1 X).filter (fun k => d ∣ k)).card = (Finset.Icc 1 (X / d)).card := by
    symm
    refine Finset.card_bij (fun q _ => q * d) ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_Icc] at hq
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_left d q⟩
      calc q * d ≤ (X / d) * d := Nat.mul_le_mul_right d hq.2
        _ ≤ X := Nat.div_mul_le_self X d
    · intro q₁ _ q₂ _ h
      exact Nat.eq_of_mul_eq_mul_right hd h
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      rcases hk.2 with ⟨q, rfl⟩
      refine ⟨q, Finset.mem_Icc.mpr ⟨?_, ?_⟩, mul_comm q d⟩
      · by_contra hq0
        have : q = 0 := by omega
        subst this; simp at hk
      · exact (Nat.le_div_iff_mul_le hd).mpr (by linarith [hk.1.2, mul_comm q d])
  rw [hbij]
  simp [Nat.card_Icc]

private lemma nat_div_cast_le (X d : ℕ) : ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / (d : ℝ) := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd)
    rw [le_div_iff₀ hd_pos]
    exact_mod_cast Nat.div_mul_le_self X d

private lemma nat_div_cast_ge (X d : ℕ) (hd : 0 < d) :
    (X : ℝ) / (d : ℝ) - 1 ≤ ((X / d : ℕ) : ℝ) := by
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  rw [sub_le_iff_le_add, div_le_iff₀ hd_pos]
  have hlt : X < (X / d + 1) * d := by
    have := Nat.lt_div_mul_add (a := X) hd
    linarith
  have hle : (X : ℝ) ≤ ((X / d + 1) * d : ℕ) := by exact_mod_cast hlt.le
  push_cast at hle
  linarith

private lemma exists_finset_primes_gt_sum_ge (B : ℕ) (M : ℝ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ B < p) ∧ M ≤ ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
  by_contra h
  push_neg at h
  have hbound : ∀ s : Finset Nat.Primes,
      ∑ p ∈ s, (1 / ((p : ℕ) : ℝ)) ≤ (B + 1 : ℝ) + max M 0 := by
    intro s
    let s1 : Finset Nat.Primes := s.filter (fun p : Nat.Primes => p.1 ≤ B)
    let s2 : Finset Nat.Primes := s.filter (fun p : Nat.Primes => B < p.1)
    have hsplit : ∑ p ∈ s, (1 / ((p : ℕ) : ℝ)) =
        ∑ p ∈ s1, (1 / ((p : ℕ) : ℝ)) + ∑ p ∈ s2, (1 / ((p : ℕ) : ℝ)) := by
      have hdisj : Disjoint s1 s2 := by
        rw [Finset.disjoint_filter]
        intro p _ h1 h2; omega
      have hunion : s1 ∪ s2 = s := by
        ext p; simp only [s1, s2, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
        · intro hp; by_cases hle : p.1 ≤ B
          · exact Or.inl ⟨hp, hle⟩
          · exact Or.inr ⟨hp, by omega⟩
      rw [← hunion, Finset.sum_union hdisj]
    rw [hsplit]
    have h1 : ∑ p ∈ s1, (1 / ((p : ℕ) : ℝ)) ≤ (B + 1 : ℝ) := by
      have hle1 : ∑ p ∈ s1, (1 / ((p : ℕ) : ℝ)) ≤ ∑ _p ∈ s1, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        have hp1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.one_le
        exact div_le_one_of_le₀ hp1 (by positivity)
      have hcard : s1.card ≤ B + 1 := by
        have hinj : (s1.image (fun p : Nat.Primes => p.1)).card = s1.card :=
          Finset.card_image_of_injective s1 Subtype.val_injective
        have hsub : s1.image (fun p : Nat.Primes => p.1) ⊆ Finset.range (B + 1) := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
          rw [Finset.mem_filter] at hp
          exact Finset.mem_range.mpr (by omega)
        calc s1.card = (s1.image (fun p : Nat.Primes => p.1)).card := hinj.symm
          _ ≤ (Finset.range (B + 1)).card := Finset.card_le_card hsub
          _ = B + 1 := Finset.card_range _
      calc ∑ p ∈ s1, (1 / ((p : ℕ) : ℝ)) ≤ (s1.card : ℝ) := by simpa using hle1
        _ ≤ (B + 1 : ℝ) := by exact_mod_cast hcard
    have h2 : ∑ p ∈ s2, (1 / ((p : ℕ) : ℝ)) ≤ max M 0 := by
      let P : Finset ℕ := s2.image (fun p : Nat.Primes => p.1)
      have hP : ∀ p ∈ P, p.Prime ∧ B < p := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
        rw [Finset.mem_filter] at hp
        exact ⟨p.2, hp.2⟩
      have hsum : ∑ p ∈ s2, (1 / ((p : ℕ) : ℝ)) = ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
        symm
        exact Finset.sum_image (fun a _ b _ hab => Subtype.ext hab)
      rw [hsum]
      exact le_trans (h P hP).le (le_max_left M 0)
    linarith
  have hsumm : Summable (fun p : Nat.Primes => (1 / ((p : ℕ) : ℝ))) :=
    summable_of_sum_le (fun p => by positivity) hbound
  exact Nat.Primes.not_summable_one_div hsumm

private lemma sum_inv_sq_gt_le (P : Finset ℕ) (B : ℕ) (hB : 1 ≤ B) (hP : ∀ p ∈ P, B < p) :
    ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / (B : ℝ) := by
  let M := P.sup id
  have hsub : P ⊆ Finset.Icc (B + 1) (max (B + 1) M) := by
    intro p hp
    rw [Finset.mem_Icc]
    exact ⟨by have := hP p hp; omega, le_trans (Finset.le_sup (f := id) hp) (le_max_right _ _)⟩
  have h1 : ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 ≤
      ∑ m ∈ Finset.Icc (B + 1) (max (B + 1) M), (1 : ℝ) / (m : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have h2 : ∀ m ∈ Finset.Icc (B + 1) (max (B + 1) M),
      (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / ((m : ℝ) - 1) - 1 / (m : ℝ) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
    have hdiff : 1 / ((m : ℝ) - 1) - 1 / (m : ℝ) - 1 / (m : ℝ) ^ 2 =
        1 / ((m : ℝ) ^ 2 * ((m : ℝ) - 1)) := by
      have hm0 : (m : ℝ) ≠ 0 := by linarith
      have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hm0, hm1]
      ring
    have hnn : 0 ≤ 1 / ((m : ℝ) ^ 2 * ((m : ℝ) - 1)) := by
      have : (0 : ℝ) < (m : ℝ) - 1 := by linarith
      positivity
    linarith
  have htel : ∀ N : ℕ, B + 1 ≤ N →
      ∑ m ∈ Finset.Icc (B + 1) N, (1 / ((m : ℝ) - 1) - 1 / (m : ℝ)) =
      1 / (B : ℝ) - 1 / (N : ℝ) := by
    intro N hN
    induction N with
    | zero => omega
    | succ N ih =>
      rcases eq_or_lt_of_le hN with hEq | hLt
      · have hNB : N = B := by omega
        subst hNB
        simp [Nat.cast_add, Nat.cast_one]
      · rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]
        push_cast
        ring
  have hN : B + 1 ≤ max (B + 1) M := le_max_left _ _
  have h3 := Finset.sum_le_sum h2
  rw [htel _ hN] at h3
  have hpos : (0 : ℝ) ≤ 1 / ((max (B + 1) M : ℕ) : ℝ) := by positivity
  linarith

private lemma two_pow_dvd_sigma_of_primes {k : ℕ} (hk : 1 ≤ k) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) (hsq : ∀ p ∈ P, ¬ p ^ 2 ∣ k) :
    2 ^ (P.filter (fun p => p ∣ k)).card ∣ ∑ d ∈ k.divisors, d := by
  have hk0 : k ≠ 0 := by omega
  have hsig_eq : ∑ d ∈ k.divisors, d = ArithmeticFunction.sigma 1 k := by
    simp [ArithmeticFunction.sigma_apply]
  rw [hsig_eq, ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hk0]
  let Q := P.filter (fun p => p ∣ k)
  have hQ_sub : Q ⊆ k.primeFactors := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact Nat.mem_primeFactors.mpr ⟨(hP p hp.1).1, hp.2, hk0⟩
  have hdvd1 : ∏ p ∈ Q, ArithmeticFunction.sigma 1 (p ^ k.factorization p) ∣
      ∏ p ∈ k.primeFactors, ArithmeticFunction.sigma 1 (p ^ k.factorization p) :=
    Finset.prod_dvd_prod_of_subset Q k.primeFactors _ hQ_sub
  refine dvd_trans ?_ hdvd1
  have h2pow : 2 ^ Q.card = ∏ _p ∈ Q, 2 := by simp
  rw [h2pow]
  refine Finset.prod_dvd_prod_of_dvd _ _ (fun p hp => ?_)
  rw [Finset.mem_filter] at hp
  have hp_prime : p.Prime := (hP p hp.1).1
  have hp_gt2 : 2 < p := (hP p hp.1).2
  have hfac1 : k.factorization p = 1 := by
    have hge1 : 1 ≤ k.factorization p :=
      (hp_prime.dvd_iff_one_le_factorization hk0).mp hp.2
    have hlt2 : k.factorization p < 2 := by
      by_contra hge2
      push_neg at hge2
      have : p ^ 2 ∣ k := (hp_prime.pow_dvd_iff_le_factorization hk0).mpr hge2
      exact hsq p hp.1 this
    omega
  rw [hfac1, pow_one, ArithmeticFunction.sigma_apply, hp_prime.divisors,
    Finset.sum_pair hp_prime.ne_one.symm]
  simp only [pow_one]
  have hodd : Odd p := hp_prime.odd_of_ne_two (by omega)
  rcases hodd with ⟨t, rfl⟩
  exact ⟨t + 1, by ring⟩

private lemma turan_few_primes_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r X : ℕ)
    (hS : (2 : ℝ) * r ≤ ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) :
    (((Finset.Icc 1 X).filter (fun k => (P.filter (fun p => p ∣ k)).card < r)).card : ℝ) *
      ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) / 2) ^ 2 ≤
      (X : ℝ) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) +
        2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (P.card : ℝ) := by
  set S : ℝ := ∑ p ∈ P, (1 : ℝ) / (p : ℝ)
  let f : ℕ → ℝ := fun k => ((P.filter (fun p => p ∣ k)).card : ℝ)
  have hf_eq : ∀ k : ℕ, f k = ∑ p ∈ P, if p ∣ k then (1 : ℝ) else 0 := by
    intro k
    simp [f, Finset.sum_boole]
  have hsum1 : (X : ℝ) * S - (P.card : ℝ) ≤ ∑ k ∈ Finset.Icc 1 X, f k := by
    have hswap : ∑ k ∈ Finset.Icc 1 X, f k = ∑ p ∈ P, ((X / p : ℕ) : ℝ) := by
      simp_rw [hf_eq]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      rw [Finset.sum_boole, card_filter_dvd_Icc p X (hP p hp).pos]
    rw [hswap]
    have hterm : ∑ p ∈ P, ((X : ℝ) / (p : ℝ) - 1) ≤ ∑ p ∈ P, ((X / p : ℕ) : ℝ) :=
      Finset.sum_le_sum (fun p hp => nat_div_cast_ge X p (hP p hp).pos)
    have hlhs : ∑ p ∈ P, ((X : ℝ) / (p : ℝ) - 1) = (X : ℝ) * S - (P.card : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      simp only [S, Finset.mul_sum, mul_one_div]
    linarith
  have hsum2 : ∑ k ∈ Finset.Icc 1 X, (f k) ^ 2 ≤ (X : ℝ) * S + (X : ℝ) * S ^ 2 := by
    have hexp : ∑ k ∈ Finset.Icc 1 X, (f k) ^ 2 =
        ∑ p ∈ P, ∑ q ∈ P, (((Finset.Icc 1 X).filter (fun k => p ∣ k ∧ q ∣ k)).card : ℝ) := by
      have hsq : ∀ k : ℕ, (f k) ^ 2 =
          ∑ p ∈ P, ∑ q ∈ P, if p ∣ k ∧ q ∣ k then (1 : ℝ) else 0 := by
        intro k
        rw [hf_eq, sq, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        by_cases hp : p ∣ k <;> by_cases hq : q ∣ k <;> simp [hp, hq]
      simp_rw [hsq]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [Finset.sum_boole]
    rw [hexp]
    have hbound_pq : ∀ p ∈ P, ∀ q ∈ P,
        (((Finset.Icc 1 X).filter (fun k => p ∣ k ∧ q ∣ k)).card : ℝ) ≤
        (if p = q then (X : ℝ) / (p : ℝ) else 0) + (X : ℝ) / ((p : ℝ) * (q : ℝ)) := by
      intro p hp q hq
      rcases eq_or_ne p q with rfl | hpq
      · have hfilt : (Finset.Icc 1 X).filter (fun k => p ∣ k ∧ p ∣ k) =
            (Finset.Icc 1 X).filter (fun k => p ∣ k) := by
          ext k; simp
        rw [hfilt, card_filter_dvd_Icc p X (hP p hp).pos, if_pos rfl]
        have hnn : (0 : ℝ) ≤ (X : ℝ) / ((p : ℝ) * (p : ℝ)) := by positivity
        linarith [nat_div_cast_le X p]
      · have hcop : Nat.Coprime p q := (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq
        have hfilt : (Finset.Icc 1 X).filter (fun k => p ∣ k ∧ q ∣ k) =
            (Finset.Icc 1 X).filter (fun k => p * q ∣ k) := by
          ext k
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hk, hpk, hqk⟩; exact ⟨hk, hcop.mul_dvd_of_dvd_of_dvd hpk hqk⟩
          · rintro ⟨hk, hpqk⟩; exact ⟨hk, dvd_trans (dvd_mul_right p q) hpqk,
              dvd_trans (dvd_mul_left q p) hpqk⟩
        rw [hfilt, card_filter_dvd_Icc (p * q) X (Nat.mul_pos (hP p hp).pos (hP q hq).pos),
          if_neg hpq, zero_add]
        simpa [Nat.cast_mul] using nat_div_cast_le X (p * q)
    calc ∑ p ∈ P, ∑ q ∈ P, (((Finset.Icc 1 X).filter (fun k => p ∣ k ∧ q ∣ k)).card : ℝ)
        ≤ ∑ p ∈ P, ∑ q ∈ P, ((if p = q then (X : ℝ) / (p : ℝ) else 0) +
            (X : ℝ) / ((p : ℝ) * (q : ℝ))) :=
          Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun q hq => hbound_pq p hp q hq))
      _ = (X : ℝ) * S + (X : ℝ) * S ^ 2 := by
          simp_rw [Finset.sum_add_distrib]
          have hdiag : ∑ p ∈ P, ∑ q ∈ P, (if p = q then (X : ℝ) / (p : ℝ) else 0) = (X : ℝ) * S := by
            simp only [Finset.sum_ite_eq, S, Finset.mul_sum, mul_one_div]
            exact Finset.sum_congr rfl (fun p hp => by simp [hp])
          have hoff : ∑ p ∈ P, ∑ q ∈ P, (X : ℝ) / ((p : ℝ) * (q : ℝ)) = (X : ℝ) * S ^ 2 := by
            simp only [S, sq, Finset.sum_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
            ring
          rw [hdiag, hoff]
  have hvar : ∑ k ∈ Finset.Icc 1 X, (f k - S) ^ 2 ≤ (X : ℝ) * S + 2 * S * (P.card : ℝ) := by
    have hexp : ∑ k ∈ Finset.Icc 1 X, (f k - S) ^ 2 =
        ∑ k ∈ Finset.Icc 1 X, (f k) ^ 2 - 2 * S * (∑ k ∈ Finset.Icc 1 X, f k) + (X : ℝ) * S ^ 2 := by
      have hcard : ((Finset.Icc 1 X).card : ℝ) = (X : ℝ) := by simp [Nat.card_Icc]
      calc ∑ k ∈ Finset.Icc 1 X, (f k - S) ^ 2
          = ∑ k ∈ Finset.Icc 1 X, ((f k) ^ 2 - 2 * S * f k + S ^ 2) :=
            Finset.sum_congr rfl (fun k _ => by ring)
        _ = ∑ k ∈ Finset.Icc 1 X, (f k) ^ 2 - ∑ k ∈ Finset.Icc 1 X, 2 * S * f k +
            ∑ _k ∈ Finset.Icc 1 X, S ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = ∑ k ∈ Finset.Icc 1 X, (f k) ^ 2 - 2 * S * (∑ k ∈ Finset.Icc 1 X, f k) +
            (X : ℝ) * S ^ 2 := by
            rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcard]
    rw [hexp]
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun p _ => by positivity)
    nlinarith
  let A := (Finset.Icc 1 X).filter (fun k => (P.filter (fun p => p ∣ k)).card < r)
  have hmarkov : (A.card : ℝ) * (S / 2) ^ 2 ≤ ∑ k ∈ Finset.Icc 1 X, (f k - S) ^ 2 := by
    have hsub : A ⊆ Finset.Icc 1 X := Finset.filter_subset _ _
    calc (A.card : ℝ) * (S / 2) ^ 2
        = ∑ _k ∈ A, (S / 2) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ A, (f k - S) ^ 2 := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          rw [Finset.mem_filter] at hk
          have hfk : f k < (r : ℝ) := by dsimp only [f]; exact_mod_cast hk.2
          have hdiff : S / 2 ≤ S - f k := by linarith
          have hS0 : 0 ≤ S / 2 := by
            have : (0 : ℝ) ≤ S := Finset.sum_nonneg (fun p _ => by positivity)
            linarith
          nlinarith
      _ ≤ ∑ k ∈ Finset.Icc 1 X, (f k - S) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  exact le_trans hmarkov hvar

lemma sigma_count_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((Finset.Icc 1 X).filter (fun m => OMA.S_oeis_a095380.isSigmaValue m)).card : ℝ) <
        ε * (X : ℝ) := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (1 : ℝ) / (2 : ℝ) ^ r < ε / 3 := by
    have hlim : Tendsto (fun r : ℕ => (1 : ℝ) / (2 : ℝ) ^ r) atTop (𝓝 0) := by
      simpa [one_div, inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 : ℝ) / 2 < 1)
    rcases (Metric.tendsto_atTop.mp hlim (ε / 3) (by linarith)) with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    have := hr r le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
    exact this
  obtain ⟨B, hB2, hB⟩ : ∃ B : ℕ, 2 ≤ B ∧ (1 : ℝ) / (B : ℝ) < ε / 3 := by
    obtain ⟨B, hB⟩ := exists_nat_gt (3 / ε)
    refine ⟨max B 2, le_max_right _ _, ?_⟩
    have hB_pos : (0 : ℝ) < (max B 2 : ℕ) := Nat.cast_pos.mpr (by omega)
    have hB_gt : 3 / ε < (max B 2 : ℕ) := lt_of_lt_of_le hB (by exact_mod_cast le_max_left B 2)
    rw [div_lt_div_iff₀ hB_pos (by norm_num : (0 : ℝ) < 3)]
    have := (div_lt_iff₀ hε).mp hB_gt
    linarith
  obtain ⟨P, hP, hS⟩ := exists_finset_primes_gt_sum_ge B (max (2 * (r : ℝ)) (24 / ε))
  set S : ℝ := ∑ p ∈ P, (1 : ℝ) / (p : ℝ)
  have hS_pos : 0 < S := lt_of_lt_of_le (by positivity) (le_trans (le_max_right _ _) hS)
  have hS_r : (2 : ℝ) * r ≤ S := le_trans (le_max_left _ _) hS
  have hS_eps : 24 / ε ≤ S := le_trans (le_max_right _ _) hS
  obtain ⟨X₀, hX₀⟩ := exists_nat_gt (48 * (P.card : ℝ) / (ε * S))
  refine ⟨max X₀ 1, fun X hX => ?_⟩
  have hX_pos : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hX_gt : 48 * (P.card : ℝ) / (ε * S) < (X : ℝ) :=
    lt_of_lt_of_le hX₀ (by exact_mod_cast le_trans (le_max_left _ _) hX)
  let M := (Finset.Icc 1 X).filter (fun m => OMA.S_oeis_a095380.isSigmaValue m)
  let M1 := M.filter (fun m => 2 ^ r ∣ m)
  let M2 := M.filter (fun m => ¬ 2 ^ r ∣ m)
  have hM_split : M.card = M1.card + M2.card := by
    simpa [M1, M2] using (Finset.card_filter_add_card_filter_not (s := M) (p := fun m => 2 ^ r ∣ m)).symm
  have hM1 : (M1.card : ℝ) < (ε / 3) * (X : ℝ) := by
    have hsub : M1 ⊆ (Finset.Icc 1 X).filter (fun m => 2 ^ r ∣ m) := by
      intro m hm
      simp only [M1, M, Finset.mem_filter] at hm ⊢
      exact ⟨hm.1.1, hm.2⟩
    have hc : M1.card ≤ X / 2 ^ r := by
      rw [← card_filter_dvd_Icc (2 ^ r) X (by positivity)]
      exact Finset.card_le_card hsub
    calc (M1.card : ℝ) ≤ ((X / 2 ^ r : ℕ) : ℝ) := by exact_mod_cast hc
      _ ≤ (X : ℝ) / ((2 ^ r : ℕ) : ℝ) := nat_div_cast_le X (2 ^ r)
      _ = (1 / (2 : ℝ) ^ r) * (X : ℝ) := by push_cast; ring
      _ < (ε / 3) * (X : ℝ) := mul_lt_mul_of_pos_right hr hX_pos
  let Ksq := (Finset.Icc 1 X).filter (fun k => ∃ p ∈ P, p ^ 2 ∣ k)
  let Kfew := (Finset.Icc 1 X).filter (fun k => (P.filter (fun p => p ∣ k)).card < r)
  have hM2_le : M2.card ≤ Ksq.card + Kfew.card := by
    have hsub : M2 ⊆ (Ksq ∪ Kfew).image (fun k => ∑ d ∈ k.divisors, d) := by
      intro m hm
      simp only [M2, M, Finset.mem_filter] at hm
      rcases hm.1.2 with ⟨k, hk1, hsig⟩
      have hkX : k ≤ X := by
        have hk_le_sig : k ≤ ∑ d ∈ k.divisors, d :=
          Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self k (by omega))
        have hmX : m ≤ X := (Finset.mem_Icc.mp hm.1.1).2
        omega
      refine Finset.mem_image.mpr ⟨k, ?_, hsig⟩
      rw [Finset.mem_union]
      by_cases hsq : ∃ p ∈ P, p ^ 2 ∣ k
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk1, hkX⟩, hsq⟩)
      · right
        push_neg at hsq
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk1, hkX⟩, ?_⟩
        by_contra hge
        push_neg at hge
        have hdvd1 : 2 ^ r ∣ 2 ^ (P.filter (fun p => p ∣ k)).card := Nat.pow_dvd_pow 2 hge
        have hdvd2 : 2 ^ (P.filter (fun p => p ∣ k)).card ∣ m := by
          rw [← hsig]
          exact two_pow_dvd_sigma_of_primes hk1
            (fun p hp => ⟨(hP p hp).1, by have := (hP p hp).2; omega⟩) hsq
        exact hm.2 (dvd_trans hdvd1 hdvd2)
    calc M2.card ≤ ((Ksq ∪ Kfew).image (fun k => ∑ d ∈ k.divisors, d)).card := Finset.card_le_card hsub
      _ ≤ (Ksq ∪ Kfew).card := Finset.card_image_le
      _ ≤ Ksq.card + Kfew.card := Finset.card_union_le _ _
  have hKsq : (Ksq.card : ℝ) < (ε / 3) * (X : ℝ) := by
    have hsub : Ksq ⊆ P.biUnion (fun p => (Finset.Icc 1 X).filter (fun k => p ^ 2 ∣ k)) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      rcases hk.2 with ⟨p, hp, hpk⟩
      exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hk.1, hpk⟩⟩
    have hc : Ksq.card ≤ ∑ p ∈ P, X / p ^ 2 := by
      calc Ksq.card ≤ (P.biUnion (fun p => (Finset.Icc 1 X).filter (fun k => p ^ 2 ∣ k))).card :=
            Finset.card_le_card hsub
        _ ≤ ∑ p ∈ P, ((Finset.Icc 1 X).filter (fun k => p ^ 2 ∣ k)).card := Finset.card_biUnion_le
        _ = ∑ p ∈ P, X / p ^ 2 := Finset.sum_congr rfl (fun p hp =>
            card_filter_dvd_Icc (p ^ 2) X (sq_pos_of_pos (hP p hp).1.pos))
    calc (Ksq.card : ℝ) ≤ ∑ p ∈ P, ((X / p ^ 2 : ℕ) : ℝ) := by exact_mod_cast hc
      _ ≤ ∑ p ∈ P, (X : ℝ) / ((p ^ 2 : ℕ) : ℝ) := Finset.sum_le_sum (fun p _ => nat_div_cast_le X (p ^ 2))
      _ = (X : ℝ) * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun p _ => by push_cast; ring)
      _ ≤ (X : ℝ) * (1 / (B : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_inv_sq_gt_le P B (by omega) (fun p hp => (hP p hp).2)) hX_pos.le
      _ < (ε / 3) * (X : ℝ) := by
          rw [mul_comm (X : ℝ) _]
          exact mul_lt_mul_of_pos_right hB hX_pos
  have hKfew : (Kfew.card : ℝ) < (ε / 3) * (X : ℝ) := by
    have ht := turan_few_primes_bound P (fun p hp => (hP p hp).1) r X hS_r
    have hS2_pos : 0 < (S / 2) ^ 2 := by positivity
    have h1 : (Kfew.card : ℝ) ≤ 4 / S * (X : ℝ) + 8 * (P.card : ℝ) / S := by
      have hdiv := (le_div_iff₀ hS2_pos).mpr ht
      have heq : ((X : ℝ) * S + 2 * S * (P.card : ℝ)) / (S / 2) ^ 2 =
          4 / S * (X : ℝ) + 8 * (P.card : ℝ) / S := by
        field_simp [ne_of_gt hS_pos]; ring
      rwa [heq] at hdiv
    have hpart1 : 4 / S * (X : ℝ) ≤ (ε / 6) * (X : ℝ) := by
      have : 4 / S ≤ ε / 6 := by
        rw [div_le_div_iff₀ hS_pos (by norm_num : (0 : ℝ) < 6)]
        have := (div_le_iff₀ hε).mp hS_eps
        linarith
      exact mul_le_mul_of_nonneg_right this hX_pos.le
    have hpart2 : 8 * (P.card : ℝ) / S < (ε / 6) * (X : ℝ) := by
      have hmul := (div_lt_iff₀ (mul_pos hε hS_pos)).mp hX_gt
      rw [div_lt_iff₀ hS_pos]
      linarith
    linarith
  have hM2 : (M2.card : ℝ) < (2 * ε / 3) * (X : ℝ) := by
    have : (M2.card : ℝ) ≤ (Ksq.card : ℝ) + (Kfew.card : ℝ) := by exact_mod_cast hM2_le
    linarith
  have hM : (M.card : ℝ) = (M1.card : ℝ) + (M2.card : ℝ) := by exact_mod_cast hM_split
  linarith

end OMA_oeis_a095380

theorem OMA.solution : type_of% @OMA.S_oeis_a095380.main := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨X₀, hX₀⟩ := OMA_oeis_a095380.sigma_count_bound hε
  refine ⟨X₀, fun n hn => ?_⟩
  have h2n_ge : X₀ ≤ 2 ^ n := le_trans hn (Nat.lt_two_pow_self.le)
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hpart : OMA.S_oeis_a095380.a n +
      ((Finset.Icc 1 (2 ^ n)).filter (fun m => OMA.S_oeis_a095380.isSigmaValue m)).card = 2 ^ n := by
    classical
    unfold OMA.S_oeis_a095380.a
    have h := Finset.card_filter_add_card_filter_not
      (s := Finset.Icc 1 (2 ^ n)) (p := fun m => OMA.S_oeis_a095380.isSigmaValue m)
    simp only [Nat.card_Icc, add_tsub_cancel_right] at h
    omega
  have hpart_r : (OMA.S_oeis_a095380.a n : ℝ) +
      (((Finset.Icc 1 (2 ^ n)).filter (fun m => OMA.S_oeis_a095380.isSigmaValue m)).card : ℝ) =
      (2 : ℝ) ^ n := by
    exact_mod_cast hpart
  have hlt := hX₀ (2 ^ n) h2n_ge
  push_cast at hlt
  rw [Real.dist_eq]
  have hdiff : (OMA.S_oeis_a095380.a n : ℝ) / (2 : ℝ) ^ n - 1 =
      -((((Finset.Icc 1 (2 ^ n)).filter (fun m => OMA.S_oeis_a095380.isSigmaValue m)).card : ℝ) /
        (2 : ℝ) ^ n) := by
    field_simp [ne_of_gt h2n_pos]
    linarith
  rw [hdiff, abs_neg, abs_of_nonneg (by positivity), div_lt_iff₀ h2n_pos]
  exact hlt
