import FormalConjectures.OEIS.«217785»

-- Reduction OeisA217785.conjecture_1.R1 of OEIS A217785, conjecture 1
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Primes of the form `1 + 2s + ... + n s^(n-1)` from Bunyakovsky and irreducibility

For `n ≥ 2` the number `polyP n s = 1 + 2s + ... + n s^(n-1)` is the value at `s` of the integer
polynomial `s_(n-1)(x) = polyS (n - 1)`, where `s_n(x) = 1 + 2x + ... + (n + 1) x^n` is the
derivative of `1 + x + ... + x^(n+1)`.

Hypotheses:
* `H1` is the Bunyakovsky conjecture, word for word the catalogue row
  `Bunyakovsky.bunyakovsky_conjecture` (open, and stronger than the target: in this hypothesis
  the reduction is upward).
* `H2` (known, Borisov 1998): `s_n` is irreducible over the rationals when `n + 2` is squarefree.
  Source: A. Borisov, On some polynomials allegedly related to the abc conjecture, Acta Arith.
  84 (1998), 109-128, as quoted in the introduction of Borisov, Filaseta, Lam, Trifonov, Classes
  of polynomials having only one non-cyclotomic irreducible factor
  (people.math.sc.edu/filaseta/trifmaterial/papers/noncycl.pdf): for
  `f = 1 + x + ... + x^n`, the derivative is irreducible when `n + 1` is squarefree and at least
  `3`. The prime case is proved below, so `H2` asks only for composite `n + 2`.
* `H3` (open): `s_n` is irreducible when `n + 2` is not squarefree and `n + 1` is not a prime
  power. This is the part of the catalogue row `OeisA217785.conjecture_3` that is left; the first
  such `n` is `14`. It is a necessary condition for the target, since a reducible integer
  polynomial has only finitely many prime values.

Proved here (the two cases Filaseta noted in 1986, see the same introduction):
* `n + 2 = p` prime, by Eisenstein: the coefficient of `x^j` in `s_n(x + 1)` is
  `(j + 1) * C(p, j + 2)` (lemma `coeff_shift`), divisible by `p` for `j < n`, equal to `p - 1`
  for `j = n`, and equal to `C(p, 2)`, not divisible by `p^2`, for `j = 0`.
* `n + 1 = p^k` a prime power. By `(1 - z) s_n(z) = 1 + z + ... + z^n - (n + 1) z^(n+1)` every
  complex root of `s_n` has `|z| < 1` (lemma `norm_lt_one_of_root`, the Eneström-Kakeya bound).
  The constant coefficient of `s_n` is `1`, so a nonconstant integer factor has constant
  coefficient `±1` and hence leading coefficient of absolute value at least `2` (lemma
  `two_le_natAbs_leadingCoeff`). If `s_n = A * B` with both nonconstant, both leading
  coefficients divide `n + 1 = p^k` and are divisible by `p`, so `A * B` loses at least two
  degrees modulo `p`; but `s_n` loses only one, because its coefficient of `x^(n-1)` is `n`.

`main` then checks the two conditions of Bunyakovsky for `s_(n-1)`:
* degree `n - 1 ≥ 1` and leading coefficient `n > 0`;
* the constant coefficient is `1`, so the polynomial is primitive (irreducibility passes between
  the rationals and the integers by Gauss) and its value at `0` is `1`, so no prime divides all
  values.
It then moves the infinitely many prime values to positive `s`.
-/

namespace OMA.R_OeisA217785_conjecture_1_R1

open Polynomial

/-- The Bunyakovsky conjecture (the catalogue row `Bunyakovsky.bunyakovsky_conjecture`). -/
def H1 : Prop := ∀ f : ℤ[X], BunyakovskyCondition f ∧ SchinzelCondition {f} →
    Infinite {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime}

/-- Borisov (1998): `s_n(x)` is irreducible over the rationals when `n + 2` is squarefree (asked
here only for composite `n + 2`). -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n → Squarefree (n + 2) → ¬ (n + 2).Prime →
  Irreducible (Polynomial.map (Int.castRingHom ℚ) (OeisA217785.polyS n))

/-- The open part: `s_n(x)` is irreducible over the rationals when `n + 2` is not squarefree and
`n + 1` is not a prime power. -/
def H3 : Prop := ∀ n : ℕ, 1 ≤ n → ¬ Squarefree (n + 2) → ¬ IsPrimePow (n + 1) →
  Irreducible (Polynomial.map (Int.castRingHom ℚ) (OeisA217785.polyS n))

/-- The coefficients of `s_m`. -/
lemma coeff_polyS (m k : ℕ) :
    (OeisA217785.polyS m).coeff k = if k ≤ m then (k + 1 : ℤ) else 0 := by
  unfold OeisA217785.polyS
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-- `s_m` has degree `m`. -/
lemma natDegree_polyS (m : ℕ) : (OeisA217785.polyS m).natDegree = m := by
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_polyS, if_neg (by omega)]
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [coeff_polyS, if_pos le_rfl]
    positivity

/-- The value of `s_m` at a natural number. -/
lemma eval_polyS (m s : ℕ) :
    (OeisA217785.polyS m).eval (s : ℤ) = (OeisA217785.polyP (m + 1) s : ℤ) := by
  unfold OeisA217785.polyS OeisA217785.polyP
  rw [Polynomial.eval_finsetSum]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

/-- `s_m` is primitive, since its constant coefficient is `1`. -/
lemma isPrimitive_polyS (m : ℕ) : (OeisA217785.polyS m).IsPrimitive := by
  intro r hr
  have h := (Polynomial.C_dvd_iff_dvd_coeff r _).mp hr 0
  rw [coeff_polyS, if_pos (Nat.zero_le _)] at h
  simp only [Nat.cast_zero, zero_add] at h
  exact isUnit_of_dvd_one h

/-- The sum behind the shifted coefficients:
`∑_(k ≤ n) (k + 1) C(k, j) = (j + 1) C(n + 2, j + 2)`. -/
lemma sum_succ_mul_choose (n j : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (k + 1) * k.choose j = (j + 1) * (n + 2).choose (j + 2) := by
  induction n with
  | zero =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · simp [Nat.choose_eq_zero_of_lt hj, Nat.choose_eq_zero_of_lt (by omega : 2 < j + 2)]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : (n + 1 + 1) * (n + 1).choose j = (n + 2).choose (j + 1) * (j + 1) :=
      Nat.add_one_mul_choose_eq (n + 1) j
    have h2 : (n + 1 + 2).choose (j + 2) = (n + 2).choose (j + 1) + (n + 2).choose (j + 2) :=
      Nat.choose_succ_succ (n + 2) (j + 1)
    rw [h1, h2]
    ring

/-- The coefficients of `s_n(x + 1)`. -/
lemma coeff_shift (n j : ℕ) :
    (Polynomial.algEquivAevalXAddC (1 : ℤ) (OeisA217785.polyS n)).coeff j =
      (((j + 1) * (n + 2).choose (j + 2) : ℕ) : ℤ) := by
  rw [← sum_succ_mul_choose]
  unfold OeisA217785.polyS
  simp only [Polynomial.algEquivAevalXAddC_apply, map_sum, map_mul, Polynomial.aeval_C,
    map_pow, Polynomial.aeval_X, Polynomial.finsetSum_coeff]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  have : ((k : ℤ[X]) + 1) = Polynomial.C ((k : ℤ) + 1) := by simp
  rw [this, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  simp

/-- `s_n(x + 1)` is primitive. -/
lemma isPrimitive_shift (n : ℕ) :
    (Polynomial.algEquivAevalXAddC (1 : ℤ) (OeisA217785.polyS n)).IsPrimitive := by
  intro r hr
  obtain ⟨q, hq⟩ := hr
  apply isPrimitive_polyS n r
  refine ⟨(Polynomial.algEquivAevalXAddC (1 : ℤ)).symm q, ?_⟩
  have h := congrArg (Polynomial.algEquivAevalXAddC (1 : ℤ)).symm hq
  rw [AlgEquiv.symm_apply_apply, map_mul] at h
  rw [h, Polynomial.C_eq_algebraMap, AlgEquiv.commutes]

/-- For `p = n + 2` prime, `s_n(x + 1)` is irreducible over the integers (Eisenstein at `p`). -/
lemma irreducible_shift (n : ℕ) (hn : 1 ≤ n) (hp : (n + 2).Prime) :
    Irreducible (Polynomial.algEquivAevalXAddC (1 : ℤ) (OeisA217785.polyS n)) := by
  obtain ⟨g, hg⟩ : ∃ g, g = Polynomial.algEquivAevalXAddC (1 : ℤ) (OeisA217785.polyS n) :=
    ⟨_, rfl⟩
  rw [← hg]
  have hmem : ∀ a : ℕ, ((a : ℤ) ∈ Ideal.span {((n + 2 : ℕ) : ℤ)}) ↔ (n + 2) ∣ a := by
    intro a
    rw [Ideal.mem_span_singleton, Int.natCast_dvd_natCast]
  have hlead : g.coeff n = ((n + 1 : ℕ) : ℤ) := by
    rw [hg, coeff_shift]
    simp
  have hdeg : g.natDegree = n := by
    apply le_antisymm
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [hg, coeff_shift, Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [hlead]
      exact_mod_cast (by omega : n + 1 ≠ 0)
  have hg0 : g ≠ 0 := by
    intro h
    rw [h] at hlead
    simp at hlead
    omega
  have hprim : g.IsPrimitive := hg ▸ isPrimitive_shift n
  refine Polynomial.irreducible_of_eisenstein_criterion
    (P := Ideal.span {((n + 2 : ℕ) : ℤ)}) ?_ ?_ ?_ ?_ ?_ hprim
  · rw [Ideal.span_singleton_prime (by exact_mod_cast (by omega : n + 2 ≠ 0))]
    exact Nat.prime_iff_prime_int.mp hp
  · rw [Polynomial.leadingCoeff, hdeg, hlead, hmem]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  · intro k hk
    rw [Polynomial.degree_eq_natDegree hg0, hdeg] at hk
    have hk' : k < n := by exact_mod_cast hk
    rw [hg, coeff_shift, hmem]
    exact Dvd.dvd.mul_left (hp.dvd_choose_self (by omega) (by omega)) _
  · rw [Polynomial.degree_eq_natDegree hg0, hdeg]
    exact_mod_cast hn
  · rw [hg, coeff_shift, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro h
    have h' : (n + 2) ^ 2 ∣ (0 + 1) * (n + 2).choose (0 + 2) := by exact_mod_cast h
    rw [zero_add, one_mul, Nat.choose_two_right] at h'
    have h2 : (n + 2) ^ 2 ∣ (n + 2) * (n + 2 - 1) :=
      h'.trans (Nat.div_dvd_of_dvd (even_iff_two_dvd.mp (Nat.even_mul_pred_self (n + 2))))
    rw [pow_two] at h2
    have h3 : (n + 2) ∣ (n + 2 - 1) := Nat.dvd_of_mul_dvd_mul_left (by omega) h2
    have := Nat.le_of_dvd (by omega) h3
    omega

/-- For `n + 2` prime, `s_n` is irreducible over the rationals. -/
lemma irreducible_polyS_of_prime (n : ℕ) (hn : 1 ≤ n) (hp : (n + 2).Prime) :
    Irreducible (Polynomial.map (Int.castRingHom ℚ) (OeisA217785.polyS n)) := by
  have h := irreducible_shift n hn hp
  have h' : Irreducible (OeisA217785.polyS n) :=
    (MulEquiv.irreducible_iff (Polynomial.algEquivAevalXAddC (1 : ℤ)).toMulEquiv).mp h
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (isPrimitive_polyS n)).mp h'

/- The case `n + 1` a prime power. -/

/-- `(1 - z) (1 + 2 z + ... + (n + 1) z^n) = 1 + z + ... + z^n - (n + 1) z^(n + 1)`. -/
lemma one_sub_mul_sum (z : ℂ) (n : ℕ) :
    (1 - z) * ∑ k ∈ Finset.range (n + 1), ((k : ℂ) + 1) * z ^ k =
      ∑ k ∈ Finset.range (n + 1), z ^ k - ((n : ℂ) + 1) * z ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ (fun k => z ^ k) (n + 1)]
    push_cast
    ring

/-- A complex number with real part at least `1` and norm at most `1` is `1`. -/
lemma eq_one_of_re_ge_of_norm_le (w : ℂ) (hre : 1 ≤ w.re) (hn : ‖w‖ ≤ 1) : w = 1 := by
  have h1 : ‖w‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg w) hn
  rw [Complex.sq_norm, Complex.normSq_apply] at h1
  have him : w.im = 0 := by nlinarith [mul_self_nonneg w.im]
  have hre' : w.re = 1 := by nlinarith [mul_self_nonneg w.im]
  exact Complex.ext hre' him

/-- Eneström–Kakeya for `s_n`: every complex root of `1 + 2 z + ... + (n + 1) z^n` lies in the
open unit disc. -/
lemma norm_lt_one_of_root (n : ℕ) (z : ℂ)
    (hz : ∑ k ∈ Finset.range (n + 1), ((k : ℂ) + 1) * z ^ k = 0) : ‖z‖ < 1 := by
  by_contra hcon
  push Not at hcon
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hcon
    linarith
  have h1 := one_sub_mul_sum z n
  rw [hz, mul_zero] at h1
  have hw : ‖z⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hcon
  -- divide by `z^(n+1)`
  have h2 : ∑ k ∈ Finset.range (n + 1), z⁻¹ ^ (n + 1 - k) = (n : ℂ) + 1 := by
    have h3 : ∑ k ∈ Finset.range (n + 1), z⁻¹ ^ (n + 1 - k) =
        z⁻¹ ^ (n + 1) * ∑ k ∈ Finset.range (n + 1), z ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n + 1 := (Finset.mem_range.mp hk).le
      have : z⁻¹ ^ (n + 1) = z⁻¹ ^ (n + 1 - k) * z⁻¹ ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hk']
      rw [this, mul_assoc, ← mul_pow, inv_mul_cancel₀ hz0, one_pow, mul_one]
    have h4 : ∑ k ∈ Finset.range (n + 1), z ^ k = ((n : ℂ) + 1) * z ^ (n + 1) := by
      linear_combination -h1
    rw [h3, h4, mul_comm, mul_assoc, ← mul_pow, mul_inv_cancel₀ hz0, one_pow, mul_one]
  have h5 : ∑ k ∈ Finset.range (n + 1), (z⁻¹ ^ (n + 1 - k)).re = (n : ℝ) + 1 := by
    have := congrArg Complex.re h2
    rw [Complex.re_sum] at this
    simpa using this
  rw [Finset.sum_range_succ] at h5
  have h6 : ∑ k ∈ Finset.range n, (z⁻¹ ^ (n + 1 - k)).re ≤ (n : ℝ) := by
    have : ∑ k ∈ Finset.range n, (z⁻¹ ^ (n + 1 - k)).re ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) := by
      refine Finset.sum_le_sum fun k _ => ?_
      calc (z⁻¹ ^ (n + 1 - k)).re ≤ ‖z⁻¹ ^ (n + 1 - k)‖ := Complex.re_le_norm _
        _ = ‖z⁻¹‖ ^ (n + 1 - k) := norm_pow _ _
        _ ≤ 1 := pow_le_one₀ (norm_nonneg _) hw
    simpa using this
  have h7 : 1 ≤ (z⁻¹).re := by
    have : n + 1 - n = 1 := by omega
    rw [this, pow_one] at h5
    linarith
  have h8 : z⁻¹ = 1 := eq_one_of_re_ge_of_norm_le _ h7 hw
  have h9 : z = 1 := by
    have := congrArg (fun t => t⁻¹) h8
    simpa using this
  rw [h9] at hz
  have h10 : (∑ k ∈ Finset.range (n + 1), ((k : ℂ) + 1) * 1 ^ k).re =
      ∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  rw [hz, Complex.zero_re] at h10
  have h11 : (0 : ℝ) < ∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1) :=
    Finset.sum_pos (fun k _ => by positivity) ⟨0, Finset.mem_range.mpr (by omega)⟩
  linarith

/-- A nonempty multiset of complex numbers of norm less than `1` has product of norm less
than `1`. -/
lemma norm_prod_lt_one (s : Multiset ℂ) (hs : ∀ z ∈ s, ‖z‖ < 1) :
    ‖s.prod‖ ≤ 1 ∧ (s ≠ 0 → ‖s.prod‖ < 1) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : ‖a‖ < 1 := hs a (Multiset.mem_cons_self a s)
    have ih' := (ih fun z hz => hs z (Multiset.mem_cons_of_mem hz)).1
    have hlt : ‖(a ::ₘ s).prod‖ < 1 := by
      rw [Multiset.prod_cons, norm_mul]
      nlinarith [norm_nonneg a, norm_nonneg s.prod]
    exact ⟨hlt.le, fun _ => hlt⟩

/-- The value of `s_n` at a complex number. -/
lemma aeval_polyS (n : ℕ) (z : ℂ) :
    Polynomial.aeval z (OeisA217785.polyS n) =
      ∑ k ∈ Finset.range (n + 1), ((k : ℂ) + 1) * z ^ k := by
  unfold OeisA217785.polyS
  simp [map_sum]

/-- A nonconstant integer factor of `s_n` has leading coefficient of absolute value at least
`2`, because all its roots lie in the open unit disc and its constant coefficient is `±1`. -/
lemma two_le_natAbs_leadingCoeff (n : ℕ) (A B : ℤ[X]) (hAB : A * B = OeisA217785.polyS n)
    (hA : 1 ≤ A.natDegree) : 2 ≤ A.leadingCoeff.natAbs := by
  have hA0 : A ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hA
    omega
  have hc0 : A.coeff 0 * B.coeff 0 = 1 := by
    rw [← Polynomial.mul_coeff_zero, hAB, coeff_polyS, if_pos (Nat.zero_le _)]
    simp
  have hunit : A.coeff 0 = 1 ∨ A.coeff 0 = -1 := Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ hc0)
  have hinj : Function.Injective (algebraMap ℤ ℂ) := Int.cast_injective
  have hsplit : (A.map (algebraMap ℤ ℂ)).Splits := IsAlgClosed.splits _
  have hcoef := hsplit.coeff_zero_eq_leadingCoeff_mul_prod_roots
  rw [Polynomial.coeff_map, Polynomial.leadingCoeff_map_of_injective hinj] at hcoef
  have hroots : ∀ z ∈ (A.map (algebraMap ℤ ℂ)).roots, ‖z‖ < 1 := by
    intro z hz
    have hz1 : Polynomial.eval z (A.map (algebraMap ℤ ℂ)) = 0 := (Polynomial.mem_roots'.mp hz).2
    apply norm_lt_one_of_root n z
    rw [← aeval_polyS, ← hAB, ← Polynomial.eval_map_algebraMap, Polynomial.map_mul,
      Polynomial.eval_mul, hz1, zero_mul]
  have hcard : (A.map (algebraMap ℤ ℂ)).roots ≠ 0 := by
    intro h0
    have := hsplit.natDegree_eq_card_roots
    rw [h0, Multiset.card_zero, Polynomial.natDegree_map_eq_of_injective hinj] at this
    omega
  have hprod := (norm_prod_lt_one _ hroots).2 hcard
  have hnorm := congrArg norm hcoef
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at hnorm
  have hl1 : ‖(algebraMap ℤ ℂ) (A.coeff 0)‖ = 1 := by
    rcases hunit with h | h <;> rw [h] <;> simp
  rw [hl1] at hnorm
  have hlead : 1 < ‖(algebraMap ℤ ℂ) A.leadingCoeff‖ := by
    by_contra hle
    push Not at hle
    nlinarith [norm_nonneg ((A.map (algebraMap ℤ ℂ)).roots.prod),
      norm_nonneg ((algebraMap ℤ ℂ) A.leadingCoeff)]
  have hlead2 : (1 : ℝ) < |(A.leadingCoeff : ℝ)| := by
    have : ‖(algebraMap ℤ ℂ) A.leadingCoeff‖ = |(A.leadingCoeff : ℝ)| := by
      rw [eq_intCast, Complex.norm_intCast]
    rwa [this] at hlead
  have hlead3 : (1 : ℤ) < |A.leadingCoeff| := by exact_mod_cast hlead2
  rw [Int.abs_eq_natAbs] at hlead3
  omega

/-- A nonunit factor of `s_n` over the integers is nonconstant. -/
lemma one_le_natDegree_of_not_isUnit (n : ℕ) (A B : ℤ[X]) (hAB : A * B = OeisA217785.polyS n)
    (hA : ¬ IsUnit A) : 1 ≤ A.natDegree := by
  by_contra hcon
  have hd0 : A.natDegree = 0 := by omega
  apply hA
  rw [Polynomial.eq_C_of_natDegree_eq_zero hd0] at hAB ⊢
  exact Polynomial.isUnit_C.mpr (isPrimitive_polyS n _ ⟨B, hAB.symm⟩)

/-- For `n + 1` a prime power, `s_n` is irreducible over the rationals: of two nonconstant
integer factors, both leading coefficients would be divisible by `p` (previous lemma), but then
the product would lose two degrees modulo `p`, while `s_n` loses only one. -/
lemma irreducible_polyS_of_isPrimePow (n : ℕ) (hn : 1 ≤ n) (hpp : IsPrimePow (n + 1)) :
    Irreducible (Polynomial.map (Int.castRingHom ℚ) (OeisA217785.polyS n)) := by
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff _).mp hpp
  have := Fact.mk hp
  refine (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (isPrimitive_polyS n)).mp ⟨fun hu => ?_, fun A B hAB => ?_⟩
  · have := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [natDegree_polyS] at this
    omega
  · by_contra hcon
    push Not at hcon
    have hdA := one_le_natDegree_of_not_isUnit n A B hAB.symm hcon.1
    have hdB := one_le_natDegree_of_not_isUnit n B A (by rw [mul_comm, hAB]) hcon.2
    have hLA := two_le_natAbs_leadingCoeff n A B hAB.symm hdA
    have hLB := two_le_natAbs_leadingCoeff n B A (by rw [mul_comm, hAB]) hdB
    have hlead : A.leadingCoeff * B.leadingCoeff = ((n + 1 : ℕ) : ℤ) := by
      rw [← Polynomial.leadingCoeff_mul, ← hAB, Polynomial.leadingCoeff, natDegree_polyS,
        coeff_polyS, if_pos le_rfl]
      push_cast
      ring
    have hnat : A.leadingCoeff.natAbs * B.leadingCoeff.natAbs = p ^ k := by
      rw [← Int.natAbs_mul, hlead, Int.natAbs_natCast, hpk]
    have hdvd : ∀ L : ℤ, L.natAbs ∣ p ^ k → 2 ≤ L.natAbs →
        (Int.castRingHom (ZMod p)) L = 0 := by
      intro L hL h2
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp hL
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hm
        omega
      rw [eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd, hm]
      exact dvd_pow_self p hm0
    have hA0 := hdvd _ (Dvd.intro _ hnat) hLA
    have hB0 := hdvd _ (Dvd.intro_left _ hnat) hLB
    have h1 := Polynomial.natDegree_map_lt' hA0 (by omega)
    have h2 := Polynomial.natDegree_map_lt' hB0 (by omega)
    have hsum : n = A.natDegree + B.natDegree := by
      rw [← natDegree_polyS n, hAB, Polynomial.natDegree_mul]
      · intro h
        rw [h, Polynomial.natDegree_zero] at hdA
        omega
      · intro h
        rw [h, Polynomial.natDegree_zero] at hdB
        omega
    have h3 : n - 1 ≤ ((OeisA217785.polyS n).map (Int.castRingHom (ZMod p))).natDegree := by
      apply Polynomial.le_natDegree_of_ne_zero
      rw [Polynomial.coeff_map, coeff_polyS, if_pos (Nat.sub_le _ _)]
      have hc : (((n - 1 : ℕ) : ℤ) + 1) = ((n : ℕ) : ℤ) := by
        have : n - 1 + 1 = n := by omega
        exact_mod_cast this
      rw [hc, eq_intCast, Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
      intro hpn
      have hp1 : p ∣ n + 1 := by
        rw [← hpk]
        exact dvd_pow_self p (by omega)
      have : p ∣ 1 := (Nat.dvd_add_right hpn).mp hp1
      exact hp.one_lt.ne.symm (Nat.dvd_one.mp this)
    have h4 : ((OeisA217785.polyS n).map (Int.castRingHom (ZMod p))).natDegree ≤
        (A.map (Int.castRingHom (ZMod p))).natDegree +
          (B.map (Int.castRingHom (ZMod p))).natDegree := by
      rw [hAB, Polynomial.map_mul]
      exact Polynomial.natDegree_mul_le
    omega

/-- Irreducibility of every `s_n`, `n ≥ 1`, from `H2` and `H3`. -/
lemma irreducible_polyS (h2 : H2) (h3 : H3) (n : ℕ) (hn : 1 ≤ n) :
    Irreducible (Polynomial.map (Int.castRingHom ℚ) (OeisA217785.polyS n)) := by
  by_cases hp : (n + 2).Prime
  · exact irreducible_polyS_of_prime n hn hp
  by_cases hpp : IsPrimePow (n + 1)
  · exact irreducible_polyS_of_isPrimePow n hn hpp
  by_cases hsq : Squarefree (n + 2)
  · exact h2 n hn hsq hp
  · exact h3 n hn hsq hpp

/-- The Bunyakovsky condition for `s_m`, `m ≥ 1`, from `H2` and `H3`. -/
lemma bunyakovsky_polyS (h2 : H2) (h3 : H3) (m : ℕ) (hm : 1 ≤ m) :
    BunyakovskyCondition (OeisA217785.polyS m) := by
  have hne : OeisA217785.polyS m ≠ 0 := by
    intro h
    have := coeff_polyS m 0
    rw [h, if_pos (Nat.zero_le _)] at this
    simp at this
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.degree_eq_natDegree hne, natDegree_polyS]
    exact_mod_cast hm
  · exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      (isPrimitive_polyS m)).mpr (irreducible_polyS h2 h3 m hm)
  · rw [Polynomial.leadingCoeff, natDegree_polyS, coeff_polyS, if_pos le_rfl]
    positivity

/-- The Schinzel condition for `s_m`: the value at `0` is `1`. -/
lemma schinzel_polyS (m : ℕ) : SchinzelCondition {OeisA217785.polyS m} := by
  intro p hp
  refine ⟨0, fun f hf => ?_⟩
  rw [Finset.mem_singleton] at hf
  subst hf
  have h0 : (OeisA217785.polyS m).eval ((0 : ℕ) : ℤ) = 1 := by
    rw [eval_polyS]
    simp [OeisA217785.polyP, Finset.sum_range_succ']
  rw [h0]
  intro hdvd
  have := Int.natCast_dvd_natCast.mp (by simpa using hdvd : ((p : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ))
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem main : H1 → H2 → H3 → type_of% @OeisA217785.conjecture_1 := by
  intro h1 h2 h3 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hinf := h1 (OeisA217785.polyS m) ⟨bunyakovsky_polyS h2 h3 m (by omega), schinzel_polyS m⟩
  have hinf' : {s : ℕ | Nat.Prime (OeisA217785.polyP (m + 1) s)}.Infinite := by
    have := Set.infinite_coe_iff.mp hinf
    refine this.mono fun s hs => ?_
    simp only [Set.mem_ofPred_eq] at hs ⊢
    rw [eval_polyS] at hs
    simpa using hs
  refine (hinf'.sdiff (Set.finite_singleton 0)).mono fun s hs => ?_
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hs ⊢
  exact ⟨Nat.pos_of_ne_zero hs.2, hs.1⟩

end OMA.R_OeisA217785_conjecture_1_R1
