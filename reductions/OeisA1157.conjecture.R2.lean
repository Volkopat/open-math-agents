import FormalConjectures.OEIS.«1157»

/-! Reduce collision testing to prime exponents. A composite exponent gives a prime-exponent collision with equal prime supports. The two
Euler products range over the union of the original prime supports. A missing prime has
shifted exponent one before scaling. -/

-- Reduction OeisA1157.conjecture.R2 of OeisA1157.conjecture
-- Credit: @Pockenauer-AI

namespace OMA.R_OeisA1157_conjecture_R2

open ArithmeticFunction Finset

-- Prime exponents with equal prime supports.
def H1 : Prop :=
  ∀ r : ℕ, r.Prime → ∀ n m : ℕ, 0 < n → 0 < m → n ≠ m →
    n.primeFactors = m.primeFactors →
    Int.fract ((sigma r n : ℚ) / (n : ℚ) ^ r) ≠
      Int.fract ((sigma r m : ℚ) / (m : ℚ) ^ r)

-- Prime exponents with different prime supports.
def H2 : Prop :=
  ∀ r : ℕ, r.Prime → ∀ n m : ℕ, 0 < n → 0 < m →
    n.primeFactors ≠ m.primeFactors →
    Int.fract ((sigma r n : ℚ) / (n : ℚ) ^ r) ≠
      Int.fract ((sigma r m : ℚ) / (m : ℚ) ^ r)

-- The bounds and on-support geometric identity are from the earlier reductions by JamesSlash.
theorem ratio_eq_sum (k n : ℕ) (hn : 0 < n) :
    (sigma k n : ℚ) / (n : ℚ) ^ k = ∑ d ∈ n.divisors, 1 / (d : ℚ) ^ k := by
  rw [sigma_eq_sum_div, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hpos : 0 < (d : ℚ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hnq : 0 < (n : ℚ) := by exact_mod_cast hn
  rw [Nat.cast_pow, Nat.cast_div (Nat.dvd_of_mem_divisors hd) hpos.ne', div_pow]
  field_simp

theorem telescope (N : ℕ) :
    (∑ i ∈ range N, (1 / ((i : ℚ) + 1) - 1 / ((i : ℚ) + 2))) =
      1 - 1 / ((N : ℚ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ, ih, Nat.cast_succ]
    rw [show (N : ℚ) + 1 + 1 = (N : ℚ) + 2 by ring]
    ring

theorem ratio_bounds (k n : ℕ) (hk : 2 ≤ k) (hn : 0 < n) :
    1 ≤ (sigma k n : ℚ) / (n : ℚ) ^ k ∧ (sigma k n : ℚ) / (n : ℚ) ^ k < 2 := by
  rw [ratio_eq_sum k n hn]
  have hsplit := Finset.sum_erase_add n.divisors (fun d ↦ (1 : ℚ) / (d : ℚ) ^ k)
    (Nat.one_mem_divisors.mpr hn.ne')
  simp only [Nat.cast_one, one_pow, div_one] at hsplit
  rw [← hsplit]
  have hnonneg : 0 ≤ ∑ d ∈ n.divisors.erase 1, (1 : ℚ) / (d : ℚ) ^ k := by
    exact Finset.sum_nonneg fun d _ ↦ by positivity
  refine ⟨by linarith, ?_⟩
  have hsubset : n.divisors.erase 1 ⊆ Ico 2 (n + 1) := by
    intro d hd
    have hm := mem_of_mem_erase hd
    have hpos := Nat.pos_of_mem_divisors hm
    have hle := Nat.divisor_le hm
    have hne := ne_of_mem_erase hd
    exact mem_Ico.mpr ⟨by omega, by omega⟩
  have hle : (∑ d ∈ n.divisors.erase 1, (1 : ℚ) / (d : ℚ) ^ k) ≤
      ∑ d ∈ Ico 2 (n + 1), (1 / ((d : ℚ) - 1) - 1 / (d : ℚ)) := by
    calc
      _ ≤ ∑ d ∈ Ico 2 (n + 1), (1 : ℚ) / (d : ℚ) ^ k :=
        sum_le_sum_of_subset_of_nonneg hsubset (fun d _ _ ↦ by positivity)
      _ ≤ _ := by
        apply sum_le_sum
        intro d hd
        have hd2 : (2 : ℚ) ≤ d := by exact_mod_cast (mem_Ico.mp hd).1
        have hdpos : 0 < (d : ℚ) := by linarith
        have hdsub : 0 < (d : ℚ) - 1 := by linarith
        rw [show 1 / ((d : ℚ) - 1) - 1 / (d : ℚ) =
          1 / ((d : ℚ) * ((d : ℚ) - 1)) by field_simp; ring]
        apply one_div_le_one_div_of_le (mul_pos hdpos hdsub)
        calc
          _ ≤ (d : ℚ) ^ 2 := by nlinarith
          _ ≤ _ := pow_le_pow_right₀ (by linarith) hk
  have htel : (∑ d ∈ Ico 2 (n + 1), (1 / ((d : ℚ) - 1) - 1 / (d : ℚ))) =
      1 - 1 / ((n - 1 : ℕ) + 1 : ℚ) := by
    rw [sum_Ico_eq_sum_range]
    rw [show n + 1 - 2 = n - 1 by omega, ← telescope (n - 1)]
    apply sum_congr rfl
    intro i _
    push_cast
    rw [show 2 + (i : ℚ) - 1 = (i : ℚ) + 1 by ring, add_comm (2 : ℚ)]
  rw [htel] at hle
  have hpos : (0 : ℚ) < 1 / ((n - 1 : ℕ) + 1 : ℚ) := by positivity
  linarith

theorem geom_ratio (z : ℚ) (hz : z ≠ 0) (a : ℕ) :
    ((∑ i ∈ range (a + 1), z ^ i) / z ^ a) * (1 - 1 / z) = 1 - 1 / z ^ (a + 1) := by
  calc
    _ = (∑ i ∈ range (a + 1), z ^ i) * (z - 1) / z ^ (a + 1) := by
      rw [pow_succ]
      field_simp
    _ = _ := by
      rw [geom_sum_mul]
      field_simp

theorem geometric_numerator (k n : ℕ) (hn : n ≠ 0) :
    (sigma k n : ℚ) / (n : ℚ) ^ k * (∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ) ^ k)) =
      ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ) ^ (k * (n.factorization p + 1))) := by
  have hpows : (n : ℚ) ^ k = ∏ p ∈ n.primeFactors, ((p : ℚ) ^ n.factorization p) ^ k := by
    rw [Finset.prod_pow]
    have hncast : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
      exact_mod_cast Nat.prod_primeFactors_pow_factorization hn
    exact congrArg (· ^ k) hncast
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn, Nat.cast_prod, hpows,
    ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hsym (i : ℕ) : (p : ℚ) ^ (i * k) = ((p : ℚ) ^ k) ^ i := by
    rw [Nat.mul_comm i k, pow_mul]
  rw [Nat.cast_sum, ← pow_mul, hsym, pow_mul]
  simp_rw [Nat.cast_pow, hsym]
  exact geom_ratio _ (pow_ne_zero _ hpq) _

theorem geometric_numerator_of_subset (k n : ℕ) (hn : n ≠ 0) (s : Finset ℕ)
    (hs : n.primeFactors ⊆ s) :
    (sigma k n : ℚ) / (n : ℚ) ^ k * (∏ p ∈ s, (1 - 1 / (p : ℚ) ^ k)) =
      ∏ p ∈ s, (1 - 1 / (p : ℚ) ^ (k * (n.factorization p + 1))) := by
  classical
  have hsplit : s \ n.primeFactors ∪ n.primeFactors = s := sdiff_union_of_subset hs
  have hdis : Disjoint (s \ n.primeFactors) n.primeFactors := sdiff_disjoint
  rw [← hsplit, prod_union hdis, prod_union hdis, ← mul_left_comm,
    geometric_numerator k n hn]
  congr 1
  apply prod_congr rfl
  intro p hp
  have hzero : n.factorization p = 0 := by
    rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
    exact (mem_sdiff.mp hp).2
  simp [hzero]

theorem product_collision_of_fractional_collision {k n m : ℕ} (hk : 2 ≤ k)
    (hn : 0 < n) (hm : 0 < m)
    (heq : Int.fract ((sigma k n : ℚ) / (n : ℚ) ^ k) =
      Int.fract ((sigma k m : ℚ) / (m : ℚ) ^ k)) :
    (∏ p ∈ n.primeFactors ∪ m.primeFactors,
      (1 - 1 / (p : ℚ) ^ (k * (n.factorization p + 1)))) =
    ∏ p ∈ n.primeFactors ∪ m.primeFactors,
      (1 - 1 / (p : ℚ) ^ (k * (m.factorization p + 1))) := by
  obtain ⟨hnlo, hnhi⟩ := ratio_bounds k n hk hn
  obtain ⟨hmlo, hmhi⟩ := ratio_bounds k m hk hm
  have hnf : ⌊(sigma k n : ℚ) / (n : ℚ) ^ k⌋ = 1 :=
    Int.floor_eq_iff.mpr (by norm_num; exact ⟨hnlo, hnhi⟩)
  have hmf : ⌊(sigma k m : ℚ) / (m : ℚ) ^ k⌋ = 1 :=
    Int.floor_eq_iff.mpr (by norm_num; exact ⟨hmlo, hmhi⟩)
  have hrat : (sigma k n : ℚ) / (n : ℚ) ^ k = (sigma k m : ℚ) / (m : ℚ) ^ k := by
    simpa [Int.fract, hnf, hmf] using heq
  rw [← geometric_numerator_of_subset k n hn.ne' _ subset_union_left,
    ← geometric_numerator_of_subset k m hm.ne' _ subset_union_right, hrat]

theorem factorization_of_prime_powers (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (a : ℕ → ℕ) (p : ℕ) :
    (∏ q ∈ s, q ^ a q).factorization p = if p ∈ s then a p else 0 := by
  rw [Nat.factorization_prod_apply (fun q hq ↦ pow_ne_zero _ (hs q hq).ne_zero)]
  calc
    _ = ∑ q ∈ s, if p = q then a q else 0 := by
      apply sum_congr rfl
      intro q hq
      rw [(hs q hq).factorization_pow]
      simp [Finsupp.single_apply, eq_comm]
    _ = _ := by simp

theorem realize_prime_exponents (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (u : ℕ → ℕ) (hu : ∀ p ∈ s, 2 ≤ u p) :
    ∃ n : ℕ, 0 < n ∧ n.primeFactors = s ∧ ∀ p ∈ s, n.factorization p + 1 = u p := by
  let n := ∏ p ∈ s, p ^ (u p - 1)
  have hn : 0 < n := prod_pos fun p hp ↦ pow_pos (hs p hp).pos _
  have hfac (p : ℕ) : n.factorization p = if p ∈ s then u p - 1 else 0 :=
    factorization_of_prime_powers s hs (fun p ↦ u p - 1) p
  refine ⟨n, hn, ?_, fun p hp ↦ ?_⟩
  · ext p
    rw [← Nat.support_factorization, Finsupp.mem_support_iff, hfac]
    by_cases hp : p ∈ s
    · have := hu p hp
      simp [hp, show u p - 1 ≠ 0 by omega]
    · simp [hp]
  · rw [hfac, if_pos hp]
    have := hu p hp
    omega

theorem collision_at_prime_divisor {r c n m : ℕ} (hr : r.Prime) (hc : 1 < c)
    (hn : 0 < n) (hm : 0 < m) (hne : n ≠ m)
    (heq : Int.fract ((sigma (r * c) n : ℚ) / (n : ℚ) ^ (r * c)) =
      Int.fract ((sigma (r * c) m : ℚ) / (m : ℚ) ^ (r * c))) :
    ∃ N M : ℕ, 0 < N ∧ 0 < M ∧ N ≠ M ∧
      N.primeFactors = n.primeFactors ∪ m.primeFactors ∧
      M.primeFactors = n.primeFactors ∪ m.primeFactors ∧
      Int.fract ((sigma r N : ℚ) / (N : ℚ) ^ r) =
      Int.fract ((sigma r M : ℚ) / (M : ℚ) ^ r) := by
  have hk : 2 ≤ r * c := by
    simpa using Nat.mul_le_mul hr.two_le (show 1 ≤ c by omega)
  have hprod := product_collision_of_fractional_collision hk hn hm heq
  let s := n.primeFactors ∪ m.primeFactors
  have hs : ∀ p ∈ s, p.Prime := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact Nat.prime_of_mem_primeFactors hp
    · exact Nat.prime_of_mem_primeFactors hp
  have he (a : ℕ) : 2 ≤ c * (a + 1) := by
    simpa using Nat.mul_le_mul (show 2 ≤ c by omega) (show 1 ≤ a + 1 by omega)
  obtain ⟨N, hN, hsN, hu⟩ := realize_prime_exponents s hs
    (fun p ↦ c * (n.factorization p + 1)) (fun p _ ↦ he (n.factorization p))
  obtain ⟨M, hM, hsM, hv⟩ := realize_prime_exponents s hs
    (fun p ↦ c * (m.factorization p + 1)) (fun p _ ↦ he (m.factorization p))
  have hprodN (x X : ℕ) (hX : X ≠ 0) (hx : X.primeFactors = s)
      (hfac : ∀ p ∈ s, X.factorization p + 1 = c * (x.factorization p + 1)) :
      (sigma r X : ℚ) / (X : ℚ) ^ r * (∏ p ∈ s, (1 - 1 / (p : ℚ) ^ r)) =
      ∏ p ∈ s, (1 - 1 / (p : ℚ) ^ ((r * c) * (x.factorization p + 1))) := by
    rw [geometric_numerator_of_subset r X hX s (hx.le)]
    apply prod_congr rfl
    intro p hp
    rw [hfac p hp, Nat.mul_assoc]
  rw [← hprodN n N hN.ne' hsN hu, ← hprodN m M hM.ne' hsM hv] at hprod
  have hfactor : (∏ p ∈ s, (1 - 1 / (p : ℚ) ^ r)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hpq : (1 : ℚ) < p := by exact_mod_cast (hs p hp).one_lt
    have hpow : (1 : ℚ) < (p : ℚ) ^ r := one_lt_pow₀ hpq hr.ne_zero
    have hrecip := one_div_lt_one_div_of_lt (by norm_num : (0 : ℚ) < 1) hpow
    exact ne_of_gt (sub_pos.mpr (by simpa using hrecip))
  refine ⟨N, M, hN, hM, ?_, hsN, hsM, congrArg Int.fract (mul_right_cancel₀ hfactor hprod)⟩
  intro hNM
  apply hne
  apply Nat.factorization_inj hn.ne' hm.ne'
  ext p
  by_cases hp : p ∈ s
  · have hequal : N.factorization p + 1 = M.factorization p + 1 := by rw [hNM]
    rw [hu p hp, hv p hp] at hequal
    have := Nat.mul_left_cancel (show 0 < c by omega) hequal
    omega
  · have hnot : p ∉ n.primeFactors ∧ p ∉ m.primeFactors := by
      simpa [s, mem_union] using hp
    have hzero (x p : ℕ) (hx : p ∉ x.primeFactors) : x.factorization p = 0 := by
      rwa [← Finsupp.notMem_support_iff, Nat.support_factorization]
    rw [hzero n p hnot.1, hzero m p hnot.2]

theorem main : H1 → H2 → type_of% @OeisA1157.conjecture := by
  intro sameSupport differentSupport k hk n m hn hm hne heq
  by_cases hprime : k.Prime
  · by_cases hs : n.primeFactors = m.primeFactors
    · exact sameSupport k hprime n m hn hm hne hs heq
    · exact differentSupport k hprime n m hn hm hs heq
  · obtain ⟨r, hr, c, hkc⟩ := Nat.exists_prime_and_dvd (show k ≠ 1 by omega)
    subst k
    have hc : 1 < c := by
      by_contra! h
      interval_cases c <;> simp_all
    obtain ⟨N, M, hN, hM, hNM, hNs, hMs, hcoll⟩ :=
      collision_at_prime_divisor hr hc hn hm hne heq
    exact sameSupport r hr N M hN hM hNM (hNs.trans hMs.symm) hcoll

end OMA.R_OeisA1157_conjecture_R2
