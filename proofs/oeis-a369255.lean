import OMAStatements.S_oeis_a369255

/-!
# A369255: the parity of A140773 as Dirichlet convolutions

Source: https://oeis.org/A369255
Credit: @wadimiusz
Statement formalization: @agchua.

All functions below are arithmetic functions over `ℤ`, and `*` is Dirichlet convolution.
Pairing each divisor `d` of `n` with `n / d` gives `2·A038548 = τ + [square]` and
`2·A007875 = U + [n = 1]`, where `U n` counts the unitary divisors of `n`.
Every other function is multiplicative and is fixed by its local factors at `p^k`:
`U = ζ * Q2`, `ζ = C2 * Q2`, `h = τ * S2` and `C2 = C4 * S2`, where `C2` and `C4` mark
squares and fourth powers, `Q2` has local factor `1 + x`, `S2` has local factor `1 + x²`,
and `h = A322327` has local factor `2k`. With `g = A219009 = C4 * μ` and
`W = A007875 * g` this gives `A140773 = W * h`. Because `h m` is even for `m > 1`,
`A140773 n ≡ W n (mod 2)`. Moreover `2 W = (C4 * Q2) + g`, where `C4 * Q2` takes values
`0, 1` and `g = ±(C4 * Q2)`, so `W n ∈ {0, 1}`. This is the first formula, and the second
follows from `A140773 * h⁻¹ = W`.
-/

namespace A369255

open Finset ArithmeticFunction OMA.S_oeis_a369255
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.sigma
open scoped Classical

/-! ### Pairing divisors `d ↔ n / d` -/

lemma pairing (n : ℕ) (hn : n ≠ 0) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ d ∈ n.divisors, P d → P (n / d)) :
    2 * #(n.divisors.filter fun d => d ≤ n / d ∧ P d) =
      #(n.divisors.filter P) + #(n.divisors.filter fun d => d = n / d ∧ P d) := by
  have hswap : #(n.divisors.filter fun d => d ≤ n / d ∧ P d) =
      #(n.divisors.filter fun d => n / d ≤ d ∧ P d) := by
    refine Finset.card_nbij' (fun d => n / d) (fun d => n / d) ?_ ?_ ?_ ?_
    · intro d hd
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hd ⊢
      have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd.1
      refine ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdn, hn⟩, ?_, hP d hd.1 hd.2.2⟩
      rw [Nat.div_div_self hdn hn]
      exact hd.2.1
    · intro d hd
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hd ⊢
      have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd.1
      refine ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdn, hn⟩, ?_, hP d hd.1 hd.2.2⟩
      rw [Nat.div_div_self hdn hn]
      exact hd.2.1
    · intro d hd
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hd
      exact Nat.div_div_self (Nat.dvd_of_mem_divisors hd.1) hn
    · intro d hd
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hd
      exact Nat.div_div_self (Nat.dvd_of_mem_divisors hd.1) hn
  have hunion := Finset.card_union_add_card_inter
    (n.divisors.filter fun d => d ≤ n / d ∧ P d) (n.divisors.filter fun d => n / d ≤ d ∧ P d)
  rw [← Finset.filter_or, ← Finset.filter_and] at hunion
  have h1 : (n.divisors.filter fun d => (d ≤ n / d ∧ P d) ∨ (n / d ≤ d ∧ P d)) =
      n.divisors.filter P := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h, (⟨_, hp⟩ | ⟨_, hp⟩)⟩ <;> exact ⟨h, hp⟩
    · rintro ⟨h, hp⟩
      rcases le_total d (n / d) with h' | h'
      · exact ⟨h, Or.inl ⟨h', hp⟩⟩
      · exact ⟨h, Or.inr ⟨h', hp⟩⟩
  have h2 : (n.divisors.filter fun d => (d ≤ n / d ∧ P d) ∧ (n / d ≤ d ∧ P d)) =
      n.divisors.filter fun d => d = n / d ∧ P d := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h, ⟨h', hp⟩, h'', _⟩
      exact ⟨h, le_antisymm h' h'', hp⟩
    · rintro ⟨h, h', hp⟩
      exact ⟨h, ⟨h'.le, hp⟩, h'.ge, hp⟩
  rw [h1, h2] at hunion
  omega

/-- The divisors `d` of `n` with `d = n / d` are the square roots of `n`. -/
lemma card_sqrt (n : ℕ) (hn : n ≠ 0) :
    #(n.divisors.filter fun d => d = n / d ∧ True) = if ∃ m : ℕ, m ^ 2 = n then 1 else 0 := by
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    have hm : m ≠ 0 := by rintro rfl; simp at hn
    rw [Finset.card_eq_one]
    refine ⟨m, ?_⟩
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton, and_true]
    constructor
    · rintro ⟨⟨hd, _⟩, he⟩
      have h1 : d * d = m * m := by
        have := Nat.div_mul_cancel hd
        rw [← he] at this
        rw [this, sq]
      exact Nat.mul_self_inj.mp h1
    · rintro rfl
      refine ⟨⟨Dvd.intro_left _ (sq d).symm, hn⟩, ?_⟩
      rw [sq, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm)]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro d hd ⟨he, _⟩
    apply h
    refine ⟨d, ?_⟩
    have := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
    rw [← he] at this
    rw [sq, this]

/-- The only `d` with `d = n / d` and `gcd(d, n / d) = 1` is `d = n = 1`. -/
lemma card_one (n : ℕ) (hn : n ≠ 0) :
    #(n.divisors.filter fun d => d = n / d ∧ Nat.Coprime d (n / d)) =
      if n = 1 then 1 else 0 := by
  split_ifs with h
  · subst h
    rw [Nat.divisors_one, Finset.filter_singleton,
      if_pos ⟨by norm_num, Nat.coprime_one_left _⟩, Finset.card_singleton]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro d hd ⟨he, hc⟩
    rw [← he, Nat.coprime_self] at hc
    subst hc
    apply h
    have := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
    rw [← he] at this
    omega

/-! ### Multiplicative functions given by their local factors -/

/-- The multiplicative function with value `c k` at `p ^ k` (`p` prime, `k ≥ 1`). -/
noncomputable def fp (c : ℕ → ℤ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else ∏ p ∈ n.primeFactors, c (n.factorization p), if_pos rfl⟩

lemma fp_apply (c : ℕ → ℤ) {n : ℕ} (hn : n ≠ 0) :
    fp c n = ∏ p ∈ n.primeFactors, c (n.factorization p) := by
  simp [fp, hn]

lemma fp_mult (c : ℕ → ℤ) : (fp c).IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.mpr ⟨by simp [fp], fun {m n} hm hn hmn => ?_⟩
  rw [fp_apply c (mul_ne_zero hm hn), fp_apply c hm, fp_apply c hn,
    Nat.Coprime.primeFactors_mul hmn, Finset.prod_union hmn.disjoint_primeFactors]
  congr 1
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hpn : ¬ p ∣ n := (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors hp)).mp
      (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) hmn)
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpn, add_zero]
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hpm : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors hp)).mp
      (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) hmn.symm)
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpm, zero_add]

lemma fp_pp (c : ℕ → ℤ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    fp c (p ^ k) = if k = 0 then 1 else c k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [fp]
  rw [fp_apply c (pow_ne_zero k hp.ne_zero), Nat.primeFactors_prime_pow hk hp,
    hp.factorization_pow, Finset.prod_singleton, Finsupp.single_eq_same, if_neg hk]

/-- `n` is a `k`-th power iff `k` divides every exponent of `n`. -/
lemma exists_pow_iff (k n : ℕ) (hn : n ≠ 0) :
    (∃ m : ℕ, m ^ k = n) ↔ ∀ p ∈ n.primeFactors, k ∣ n.factorization p := by
  constructor
  · rintro ⟨m, rfl⟩ p _
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right k _
  · intro h
    refine ⟨n.factorization.prod fun p e => p ^ (e / k), ?_⟩
    rw [Finsupp.prod, ← Finset.prod_pow]
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [Finsupp.prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [← pow_mul, Nat.div_mul_cancel (h p (by simpa using hp))]

lemma fp_ind_apply (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    fp (fun e => if k ∣ e then 1 else 0) n = if ∃ m : ℕ, m ^ k = n then 1 else 0 := by
  rw [fp_apply _ hn, Finset.prod_boole]
  exact if_congr (exists_pow_iff k n hn).symm rfl rfl

noncomputable def Q2 : ArithmeticFunction ℤ := fp fun k => if k ≤ 1 then 1 else 0
noncomputable def C2 : ArithmeticFunction ℤ := fp fun k => if 2 ∣ k then 1 else 0
noncomputable def C4 : ArithmeticFunction ℤ := fp fun k => if 4 ∣ k then 1 else 0
noncomputable def S2 : ArithmeticFunction ℤ := fp fun k => if k = 2 then 1 else 0
noncomputable def Hh : ArithmeticFunction ℤ := fp fun k => 2 * (k : ℤ)
noncomputable def T : ArithmeticFunction ℤ := ((σ 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)

/-- The number of unitary divisors. -/
noncomputable def U : ArithmeticFunction ℤ :=
  ⟨fun n => (#(n.divisors.filter fun d => Nat.Coprime d (n / d)) : ℤ), by simp⟩

lemma Q2_pp {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Q2 (p ^ k) = if k = 0 then 1 else if k ≤ 1 then 1 else 0 := fp_pp _ hp k
lemma C2_pp {p : ℕ} (hp : p.Prime) (k : ℕ) :
    C2 (p ^ k) = if k = 0 then 1 else if 2 ∣ k then 1 else 0 := fp_pp _ hp k
lemma C4_pp {p : ℕ} (hp : p.Prime) (k : ℕ) :
    C4 (p ^ k) = if k = 0 then 1 else if 4 ∣ k then 1 else 0 := fp_pp _ hp k
lemma S2_pp {p : ℕ} (hp : p.Prime) (k : ℕ) :
    S2 (p ^ k) = if k = 0 then 1 else if k = 2 then 1 else 0 := fp_pp _ hp k
lemma Hh_pp {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Hh (p ^ k) = if k = 0 then 1 else 2 * (k : ℤ) := fp_pp _ hp k
lemma Hh_one : Hh 1 = 1 := (fp_mult _).map_one
lemma C2_apply {n : ℕ} (hn : n ≠ 0) : C2 n = if ∃ m : ℕ, m ^ 2 = n then 1 else 0 := by
  convert fp_ind_apply 2 hn using 2
  rfl
lemma C4_apply {n : ℕ} (hn : n ≠ 0) : C4 n = if ∃ m : ℕ, m ^ 4 = n then 1 else 0 := by
  convert fp_ind_apply 4 hn using 2
  rfl
lemma Q2_m : Q2.IsMultiplicative := fp_mult _
lemma C2_m : C2.IsMultiplicative := fp_mult _
lemma C4_m : C4.IsMultiplicative := fp_mult _
lemma S2_m : S2.IsMultiplicative := fp_mult _
lemma Hh_m : Hh.IsMultiplicative := fp_mult _
lemma U_apply (n : ℕ) : U n = (#(n.divisors.filter fun d => Nat.Coprime d (n / d)) : ℤ) := rfl
lemma T_apply (n : ℕ) : T n = (#n.divisors : ℤ) := by
  simp [T, natCoe_apply, sigma_zero_apply]

lemma zeta_m : (ζ : ArithmeticFunction ℤ).IsMultiplicative := isMultiplicative_zeta.natCast

lemma T_m : T.IsMultiplicative := isMultiplicative_sigma.natCast

lemma U_mult : U.IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.mpr ⟨by
    rw [U_apply, Nat.divisors_one, Finset.filter_singleton, if_pos (Nat.coprime_one_left _),
      Finset.card_singleton, Nat.cast_one], fun {m n} hm hn hmn => ?_⟩
  simp only [U, coe_mk]
  rw [← Nat.cast_mul]
  congr 1
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.sum_mul_sum,
    Nat.divisors_mul, Finset.mul_def, Finset.sum_image hmn.mul_injOn_divisors,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  have ha' := Nat.dvd_of_mem_divisors ha
  have hb' := Nat.dvd_of_mem_divisors hb
  rw [ite_zero_mul_ite_zero, mul_one]
  refine if_congr ?_ rfl rfl
  have h1 : Nat.Coprime a (n / b) :=
    Nat.Coprime.coprime_dvd_left ha' (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hb') hmn)
  have h2 : Nat.Coprime b (m / a) :=
    Nat.Coprime.coprime_dvd_left hb'
      (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd ha') hmn.symm)
  rw [← Nat.div_mul_div_comm ha' hb']
  simp only [Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right]
  tauto

/-! ### Values at prime powers -/

lemma zeta_pp {p : ℕ} (hp : p.Prime) (k : ℕ) : (ζ : ArithmeticFunction ℤ) (p ^ k) = 1 := by
  simp [natCoe_apply, zeta_apply, hp.ne_zero]

lemma mu_pp {p : ℕ} (hp : p.Prime) (k : ℕ) :
    μ (p ^ k) = if k = 0 then 1 else if k = 1 then -1 else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  rw [moebius_apply_prime_pow hp hk, if_neg hk]

lemma T_pp {p : ℕ} (hp : p.Prime) (k : ℕ) : T (p ^ k) = (k : ℤ) + 1 := by
  simp [T, natCoe_apply, sigma_zero_apply_prime_pow hp]

lemma U_pp {p : ℕ} (hp : p.Prime) (k : ℕ) : U (p ^ k) = if k = 0 then 1 else 2 := by
  simp only [U, coe_mk]
  rw [Finset.card_filter, Nat.divisors_prime_pow hp, Finset.sum_map]
  have hc : ∀ i ∈ range (k + 1),
      Nat.Coprime (p ^ i) (p ^ k / p ^ i) ↔ (i = 0 ∨ i = k) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Nat.pow_div hik hp.pos]
    constructor
    · intro h
      by_contra hne
      rw [not_or] at hne
      exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt (dvd_pow_self p hne.1)
        (dvd_pow_self p (by omega)) h
    · rintro (rfl | rfl)
      · simp
      · simp
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.sum_congr rfl fun i hi => if_congr (hc i hi) rfl rfl]
  rcases k with _ | k
  · simp
  · rw [Finset.sum_range_succ, Finset.sum_range_succ']
    have hz : ∑ i ∈ range k, (if i + 1 = 0 ∨ i + 1 = k + 1 then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun i hi => if_neg (by have := Finset.mem_range.mp hi; omega)
    rw [hz]
    simp

/-- A Dirichlet convolution at a prime power, when the second factor vanishes at `p ^ j`, `j ≥ 3`. -/
lemma conv_pp (f g : ArithmeticFunction ℤ) {p : ℕ} (hp : p.Prime) (e : ℕ)
    (hg : ∀ j, 3 ≤ j → g (p ^ j) = 0) :
    (f * g) (p ^ e) = f (p ^ e) * g (p ^ 0) + (if 1 ≤ e then f (p ^ (e - 1)) * g (p ^ 1) else 0) +
      (if 2 ≤ e then f (p ^ (e - 2)) * g (p ^ 2) else 0) := by
  have key : (f * g) (p ^ e) = ∑ i ∈ range (e + 1), f (p ^ i) * g (p ^ (e - i)) := by
    rw [ArithmeticFunction.mul_apply]
    refine (Nat.sum_divisorsAntidiagonal (fun a b => f a * g b)).trans ?_
    rw [Nat.divisors_prime_pow hp, Finset.sum_map]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp only [Function.Embedding.coeFn_mk]
    rw [Nat.pow_div hi' hp.pos]
  rw [key]
  rcases e with _ | _ | e
  · simp
  · norm_num [Finset.sum_range_succ]
    ring
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have hz : ∑ i ∈ range e, f (p ^ i) * g (p ^ (e + 1 + 1 - i)) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [hg _ (by have := Finset.mem_range.mp hi; omega), mul_zero]
    have h1 : e + 1 + 1 - e = 2 := by omega
    have h2 : e + 1 + 1 - (e + 1) = 1 := by omega
    have h3 : e + 1 + 1 - (e + 1 + 1) = 0 := by omega
    have h4 : e + 1 + 1 - 1 = e + 1 := by omega
    have h5 : e + 1 + 1 - 2 = e := by omega
    rw [hz, h1, h2, h3, h4, h5, if_pos (by omega), if_pos (by omega)]
    ring

/-! ### The local identities -/

lemma U_eq : U = (ζ : ArithmeticFunction ℤ) * Q2 := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ U_mult _ (zeta_m.mul Q2_m)).mpr
    fun p e hp => ?_
  rw [conv_pp (ζ : ArithmeticFunction ℤ) Q2 hp e (fun j hj => by rw [Q2_pp hp]; split_ifs <;> omega)]
  simp only [U_pp hp, zeta_pp hp, Q2_pp hp]
  split_ifs <;> first | omega | simp_all

lemma zeta_eq : (ζ : ArithmeticFunction ℤ) = C2 * Q2 := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ zeta_m _
    (C2_m.mul Q2_m)).mpr fun p e hp => ?_
  rw [conv_pp C2 Q2 hp e (fun j hj => by rw [Q2_pp hp]; split_ifs <;> omega)]
  simp only [zeta_pp hp, C2_pp hp, Q2_pp hp]
  split_ifs <;> first | omega | simp_all

lemma Hh_eq : Hh = T * S2 := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ Hh_m _
    (T_m.mul S2_m)).mpr fun p e hp => ?_
  rw [conv_pp T S2 hp e (fun j hj => by rw [S2_pp hp]; split_ifs <;> omega)]
  simp only [T_pp hp, Hh_pp hp, S2_pp hp]
  split_ifs <;> first | omega | simp_all

lemma C2_eq : C2 = C4 * S2 := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ C2_m _
    (C4_m.mul S2_m)).mpr fun p e hp => ?_
  rw [conv_pp C4 S2 hp e (fun j hj => by rw [S2_pp hp]; split_ifs <;> omega)]
  simp only [C2_pp hp, C4_pp hp, S2_pp hp]
  split_ifs <;> first | omega | simp_all

lemma T_eq : T = (ζ : ArithmeticFunction ℤ) * ζ := by
  rw [T, ← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta, natCoe_mul]

/-! ### The algebra -/

noncomputable def G : ArithmeticFunction ℤ := C4 * μ

lemma GH : G * Hh = C2 * ζ := by
  calc G * Hh = (C4 * S2) * ((ζ : ArithmeticFunction ℤ) * μ) * ζ := by
        rw [G, Hh_eq, T_eq]; ring
    _ = C2 * ζ := by rw [← C2_eq, coe_zeta_mul_moebius, mul_one]

lemma UGH : U * G * Hh = T * ζ := by
  calc U * G * Hh = (C2 * Q2) * ζ * ζ := by rw [mul_assoc, GH, U_eq]; ring
    _ = T * ζ := by rw [← zeta_eq, T_eq]

lemma UG : U * G = C4 * Q2 := by
  calc U * G = C4 * Q2 * ((ζ : ArithmeticFunction ℤ) * μ) := by rw [U_eq, G]; ring
    _ = C4 * Q2 := by rw [coe_zeta_mul_moebius, mul_one]

noncomputable def A7 : ArithmeticFunction ℤ := ⟨fun n => (a007875 n : ℤ), by simp [a007875]⟩
noncomputable def A140 : ArithmeticFunction ℤ := ⟨fun n => (a140773 n : ℤ), by simp [a140773]⟩
noncomputable def W : ArithmeticFunction ℤ := A7 * G

lemma A7_apply (n : ℕ) : A7 n = (a007875 n : ℤ) := rfl
lemma A140_apply (n : ℕ) : A140 n = (a140773 n : ℤ) := rfl

lemma a007875_two (n : ℕ) (hn : n ≠ 0) :
    2 * a007875 n = #(n.divisors.filter fun d => Nat.Coprime d (n / d)) +
      (if n = 1 then 1 else 0) := by
  have h := pairing n hn (fun d => Nat.Coprime d (n / d)) (fun d hd hc => by
    rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hn]; exact hc.symm)
  have hA : #(n.divisors.filter fun d => d ≤ n / d ∧ Nat.Coprime d (n / d)) = a007875 n := rfl
  have hB : #(n.divisors.filter fun d => d = n / d ∧ Nat.Coprime d (n / d)) =
      if n = 1 then 1 else 0 := card_one n hn
  rw [hA, hB] at h
  exact h

lemma a038548_two (n : ℕ) (hn : n ≠ 0) :
    2 * a038548 n = #n.divisors + (if ∃ m : ℕ, m ^ 2 = n then 1 else 0) := by
  have h := pairing n hn (fun _ => True) (fun _ _ _ => trivial)
  have hA : #(n.divisors.filter fun e => e ≤ n / e ∧ True) = a038548 n := by
    rw [a038548]
    congr 1
    exact Finset.filter_congr fun e he => by
      rw [and_true, Nat.le_div_iff_mul_le (Nat.pos_of_mem_divisors he)]
  have hB : #(n.divisors.filter fun _ => True) = #n.divisors := by rw [Finset.filter_true]
  have hC := card_sqrt n hn
  rw [hA, hB, hC] at h
  exact h

lemma two_A7 : A7 + A7 = U + 1 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have h := a007875_two n hn
  rw [ArithmeticFunction.add_apply, ArithmeticFunction.add_apply, A7_apply, U_apply,
    ArithmeticFunction.one_apply]
  split_ifs at h ⊢ <;> omega

lemma two_A140 : A140 + A140 = T * ζ + C2 * ζ := by
  ext n
  rw [ArithmeticFunction.add_apply, ArithmeticFunction.add_apply, A140_apply,
    coe_mul_zeta_apply, coe_mul_zeta_apply, a140773, ← Finset.sum_add_distrib]
  push_cast
  rw [← two_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  have h := a038548_two d hd0
  rw [T_apply, C2_apply hd0]
  split_ifs at h ⊢ <;> omega

lemma A140_eq : A140 = W * Hh := by
  have h : A140 + A140 = W * Hh + W * Hh := by
    calc A140 + A140 = T * ζ + C2 * ζ := two_A140
      _ = U * G * Hh + G * Hh := by rw [UGH, GH]
      _ = (U + 1) * G * Hh := by ring
      _ = (A7 + A7) * G * Hh := by rw [two_A7]
      _ = W * Hh + W * Hh := by rw [W]; ring
  ext n
  have := congrArg (fun f : ArithmeticFunction ℤ => f n) h
  simp only [ArithmeticFunction.add_apply] at this
  omega

/-! ### `W` takes the values `0` and `1` -/

lemma signs (n : ℕ) :
    ((C4 * Q2) n = 0 ∧ G n = 0) ∨ ((C4 * Q2) n = 1 ∧ (G n = 1 ∨ G n = -1)) := by
  have hI : (C4 * Q2).IsMultiplicative := (fp_mult _).mul (fp_mult _)
  have hG : G.IsMultiplicative := (fp_mult _).mul isMultiplicative_moebius
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    have hI' := conv_pp C4 Q2 hp k (fun j hj => by rw [Q2, fp_pp _ hp]; split_ifs <;> omega)
    have hG' := conv_pp C4 μ hp k (fun j hj => by rw [mu_pp hp]; split_ifs <;> omega)
    rw [G, hG', hI']
    simp only [C4, Q2, fp_pp _ hp, mu_pp hp]
    split_ifs <;> first | omega | simp_all
  | zero => simp
  | one => simp [hI.map_one, hG.map_one]
  | coprime a b _ _ hab ha hb =>
    rw [hI.map_mul_of_coprime hab, hG.map_mul_of_coprime hab]
    rcases ha with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩ <;> rcases hb with ⟨h3, h4⟩ | ⟨h3, h4 | h4⟩ <;>
      simp only [h1, h2, h3, h4] <;> norm_num

lemma W01 (n : ℕ) : W n = 0 ∨ W n = 1 := by
  have h : W + W = C4 * Q2 + G := by
    calc W + W = (A7 + A7) * G := by rw [W]; ring
      _ = U * G + G := by rw [two_A7]; ring
      _ = C4 * Q2 + G := by rw [UG]
  have := congrArg (fun f : ArithmeticFunction ℤ => f n) h
  simp only [ArithmeticFunction.add_apply] at this
  rcases signs n with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩ <;> omega

/-! ### Parity -/

lemma Hh_even (m : ℕ) : 2 ∣ (Hh - 1) m := by
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply,
    ArithmeticFunction.one_apply]
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · simp
    · simp [Hh_one]
  · rw [if_neg (by omega), neg_zero, add_zero, show Hh m = _ from fp_apply _ (by omega)]
    obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hm
    exact (dvd_mul_right 2 _).trans (Finset.dvd_prod_of_mem _ hp)

lemma W_mod (n : ℕ) : (A140 n) % 2 = W n := by
  have e : W * Hh = W + W * (Hh - 1) := by ring
  have h1 : A140 n = W n + (W * (Hh - 1)) n := by
    rw [A140_eq, e, ArithmeticFunction.add_apply]
  have h2 : 2 ∣ (W * (Hh - 1)) n := by
    rw [ArithmeticFunction.mul_apply]
    exact Finset.dvd_sum fun x _ => (Hh_even x.2).mul_left _
  rcases W01 n with h | h <;> omega

/-! ### The inverse of `h` -/

noncomputable def Inv : ArithmeticFunction ℤ := ⟨a355837, by rw [a355837]; simp⟩

lemma Inv_apply (n : ℕ) : Inv n = a355837 n := rfl

lemma Hh_a (m : ℕ) : Hh m = (a322327 m : ℤ) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [Hh, a322327]
  rw [show Hh m = _ from fp_apply _ hm, a322327, if_neg hm]
  push_cast
  rfl

lemma Hh_Inv : Hh * Inv = 1 := by
  ext n
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp
    · rw [ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one, Finset.sum_singleton,
        ArithmeticFunction.one_apply, if_pos rfl, Hh_one, Inv_apply, a355837]
      simp
  · rw [ArithmeticFunction.one_apply_ne (by omega), ArithmeticFunction.mul_apply]
    refine (Nat.sum_divisorsAntidiagonal' (fun a b => Hh a * Inv b)).trans ?_
    rw [← Finset.add_sum_erase _ _ (Nat.mem_divisors_self n (by omega))]
    have hrec : Inv n = -∑ d ∈ n.divisors.erase n, (a322327 (n / d) : ℤ) * a355837 d := by
      rw [Inv_apply, a355837, dif_neg (by omega), if_neg (by omega)]
      congr 1
      exact Finset.sum_attach _ (fun d => (a322327 (n / d) : ℤ) * a355837 d)
    show Hh (n / n) * Inv n + ∑ x ∈ n.divisors.erase n, Hh (n / x) * Inv x = 0
    rw [Nat.div_self (by omega : 0 < n), Hh_one, one_mul, hrec]
    simp only [Hh_a, Inv_apply]
    ring

lemma G_apply (m : ℕ) : G m = a219009 m := by
  show (C4 * μ) m = _
  rw [ArithmeticFunction.mul_apply, a219009]
  refine (Nat.sum_divisorsAntidiagonal (fun a b => C4 a * μ b)).trans ?_
  refine Finset.sum_congr rfl fun e he => ?_
  have he0 : e ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors he)
  show C4 e * μ (m / e) = _
  rw [C4_apply he0]

lemma W_eq (n : ℕ) : W n = ∑ d ∈ n.divisors, (a007875 d : ℤ) * a219009 (n / d) := by
  show (A7 * G) n = _
  rw [ArithmeticFunction.mul_apply]
  refine (Nat.sum_divisorsAntidiagonal (fun a b => A7 a * G b)).trans ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  show A7 d * G (n / d) = _
  rw [G_apply, A7_apply]

lemma A140Inv (n : ℕ) :
    (A140 * Inv) n = ∑ d ∈ n.divisors, (a140773 d : ℤ) * a355837 (n / d) := by
  rw [ArithmeticFunction.mul_apply]
  exact Nat.sum_divisorsAntidiagonal (fun a b => A140 a * Inv b)

lemma a_eq (n : ℕ) : (a n : ℤ) = W n := by
  rw [← W_mod n, A140_apply, a]
  exact Int.natCast_mod _ _

end A369255

theorem OMA.solution : type_of% @OMA.S_oeis_a369255.main := by
  intro n _
  refine ⟨?_, ?_⟩
  · rw [A369255.a_eq, A369255.W_eq]
  · rw [A369255.a_eq, ← A369255.A140Inv, A369255.A140_eq, mul_assoc, A369255.Hh_Inv, mul_one]
