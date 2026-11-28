import OMAStatements.S_oeis_a370905

-- Credit: @oh-meh
open OMA.S_oeis_a370905 ArithmeticFunction Finset

private def squareIndicator : ArithmeticFunction ℤ :=
  ⟨fun n => if n ≠ 0 ∧ IsSquare n then 1 else 0, by simp⟩

private def phi : ArithmeticFunction ℤ := ⟨fun n => (n.totient : ℤ), by simp⟩

private theorem square_factor {a b : ℕ} (h : a.Coprime b) (hs : IsSquare (a*b)) :
    IsSquare a := by
  obtain ⟨c, hc⟩ := hs
  have hu : IsUnit (gcd a b) := by
    change IsUnit (Nat.gcd a b)
    rw [h.gcd_eq_one]
    exact isUnit_one
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hu (k := 2) (by simpa [pow_two] using hc)
  exact ⟨d, by simpa [pow_two] using hd⟩

private theorem square_mult : squareIndicator.IsMultiplicative := by
  apply IsMultiplicative.iff_ne_zero.mpr
  refine ⟨by simp [squareIndicator], ?_⟩
  intro a b ha hb hab
  have h : IsSquare (a*b) ↔ IsSquare a ∧ IsSquare b :=
    ⟨fun hs => ⟨square_factor hab hs, square_factor hab.symm (mul_comm a b ▸ hs)⟩,
      fun ⟨x,y⟩ => x.mul y⟩
  simp [squareIndicator, ha, hb, h]
  split_ifs <;> simp_all

private theorem primePowerSquare (p k : ℕ) (hp : p.Prime) :
    IsSquare (p^k) ↔ Even k := by
  refine ⟨?_, fun h => h.isSquare_pow p⟩
  rintro ⟨r, hr⟩
  have h := congrArg (fun a : ℕ => a.factorization p) (show p^k = r^2 by simpa [pow_two] using hr)
  rw [Nat.factorization_pow_self hp, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at h
  exact ⟨r.factorization p, by omega⟩

private theorem liouville_pow (p i : ℕ) (hp : p.Prime) : liouville (p^i) = (-1 : ℤ)^i := by
  rw [liouville_apply (pow_ne_zero i hp.ne_zero), cardFactors_apply_prime_pow hp]

private theorem alternating (k : ℕ) :
    (∑ i ∈ range (k+1), (-1 : ℤ)^i) = if Even k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    rcases Nat.even_or_odd k with he | ho
    · simp [he, Nat.even_add_one, pow_succ, he.neg_one_pow]
    · simp [Nat.not_even_iff_odd.mpr ho, Nat.even_add_one, pow_succ, ho.neg_one_pow]

private theorem liouville_zeta : liouville * (zeta : ArithmeticFunction ℤ) = squareIndicator := by
  apply (IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_liouville.mul isMultiplicative_zeta.natCast) _ square_mult).2
  intro p k hp
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  simp_rw [liouville_pow _ _ hp]
  rw [alternating]
  simp [squareIndicator, hp.ne_zero, primePowerSquare p k hp]

private theorem zeta_phi : (zeta : ArithmeticFunction ℤ) * phi = (ArithmeticFunction.id : ArithmeticFunction ℤ) := by
  ext n
  rw [coe_zeta_mul_apply]
  change (∑ d ∈ n.divisors, (d.totient : ℤ)) = (n : ℤ)
  exact_mod_cast Nat.sum_totient n

private theorem convolution (n : ℕ) (hn : n ≠ 0) :
    A206369 n = (squareIndicator * phi) n := by
  rw [← liouville_zeta, mul_assoc, zeta_phi]
  rw [IsMultiplicative.multiplicative_factorization _
    (isMultiplicative_liouville.mul isMultiplicative_id.natCast) hn]
  unfold A206369
  apply Finset.prod_congr rfl
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  dsimp only
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun i j => liouville i * (ArithmeticFunction.id : ArithmeticFunction ℤ) j),
    Nat.sum_divisors_prime_pow hp']
  apply Finset.sum_congr rfl
  intro i hi
  rw [liouville_pow _ _ hp']
  simp [Nat.pow_div (by simpa using hi : i ≤ n.factorization p) hp'.pos]

private theorem range_count (n : ℕ) (hn : 0 < n) :
    (squareIndicator * phi) n = ((range n).filter (fun k => IsSquare (n.gcd k))).card := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun i j => squareIndicator i * phi j)]
  calc
    _ = ∑ d ∈ n.divisors, (if IsSquare d then ((n / d).totient : ℤ) else 0) := by
      apply sum_congr rfl
      intro d hd
      have hd0 := (Nat.pos_of_mem_divisors hd).ne'
      by_cases hs : IsSquare d <;> simp [squareIndicator, phi, hd0, hs]
    _ = ∑ d ∈ n.divisors.filter IsSquare, ((n / d).totient : ℤ) := (sum_filter ..).symm
    _ = _ := by
      exact_mod_cast (show (∑ d ∈ n.divisors.filter IsSquare, (n / d).totient) =
        ((range n).filter (fun k => IsSquare (n.gcd k))).card from by
          calc
            _ = ∑ d ∈ n.divisors.filter IsSquare, ((range n).filter (fun k => n.gcd k = d)).card := by
              exact sum_congr rfl fun d hd => Nat.totient_div_of_dvd
                (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)
            _ = _ := by
              rw [sum_card_fiberwise_eq_card_filter]
              simp [Nat.mem_divisors, Nat.gcd_dvd_left, hn.ne'])

private theorem interval_count (n : ℕ) (hn : 0 < n) :
    ((range n).filter (fun k => IsSquare (n.gcd k))).card =
      ((Icc 1 n).filter (fun k => IsSquare (k.gcd n))).card := by
  apply card_bij (fun k _ => if k = 0 then n else k)
  · intro k hk
    simp only [mem_filter, mem_range] at hk
    by_cases h : k = 0
    · subst k
      simpa [show 1 ≤ n by omega] using hk.2
    · simpa [h, Nat.gcd_comm, Nat.one_le_iff_ne_zero, hk.1.le] using hk.2
  · intro i hi j hj h
    simp only [mem_filter, mem_range] at hi hj
    split_ifs at h <;> omega
  · intro j hj
    simp only [mem_filter, mem_Icc] at hj
    by_cases h : j = n
    · subst j
      refine ⟨0, ?_, by simp⟩
      simpa [hn] using hj.2
    · refine ⟨j, ?_, by simp [show j ≠ 0 by omega]⟩
      simp [show j < n by omega, Nat.gcd_comm n j, hj.2]

private theorem pairs (n : ℕ) :
    (((Icc 1 n ×ˢ Icc 1 n).filter (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ IsSquare (p.1.gcd p.2))).card) =
      ∑ y ∈ Icc 1 n, ((Icc 1 y).filter (fun x => IsSquare (x.gcd y))).card := by
  let S := (Icc 1 n ×ˢ Icc 1 n).filter (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ IsSquare (p.1.gcd p.2))
  change S.card = _
  rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := Icc 1 n)
    (fun p hp => (mem_product.mp (mem_filter.mp hp).1).2)]
  apply sum_congr rfl
  intro y hy
  have hy' := mem_Icc.mp hy
  apply card_bij (fun p _ => p.1)
  · rintro ⟨x,z⟩ h
    simp at h
    obtain ⟨h, rfl⟩ := h
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨h.1.1.1, h.2.1⟩, h.2.2⟩
  · rintro ⟨x,z⟩ hx ⟨x',z'⟩ hx' he
    simp at hx hx'
    simp_all
  · intro x hx
    refine ⟨(x,y), ?_, rfl⟩
    simp at hx
    simp [hx, hx.1.2.trans hy'.2, hy]

theorem OMA.solution : type_of% @OMA.S_oeis_a370905.main := by
  intro n hn
  rw [pairs]
  unfold a
  push_cast
  apply sum_congr rfl
  intro k hk
  have h := (mem_Icc.mp hk).1
  rw [convolution k (by omega), range_count k h, interval_count k h]
