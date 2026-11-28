import OMAStatements.S_oeis_a320949
import Mathlib

namespace OMA.S_oeis_a320949

-- 1. Geometric / binomial HasSum: ∑_{n=0}^∞ C(n, j) / 2^(n+1) = 1
private lemma hasSum_half_pow : HasSum (fun n : ℕ => (1 : ℝ) / 2 ^ (n + 1)) 1 := by
  have hgeom : HasSum (fun n : ℕ => ((1 / 2 : ℝ)) ^ n) ((1 - 1 / 2 : ℝ)⁻¹) :=
    hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
  have hmul := hgeom.mul_left (1 / 2 : ℝ)
  have hval : (1 / 2 : ℝ) * (1 - 1 / 2 : ℝ)⁻¹ = 1 := by norm_num
  rw [hval] at hmul
  refine hmul.congr_fun fun n => ?_
  rw [pow_succ, one_div, one_div, inv_pow]
  ring

private lemma sum_range_choose (n j : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.choose k j = Nat.choose (n + 1) (j + 1) := by
  induction n with
  | zero => cases j <;> simp [Nat.choose_eq_zero_of_lt]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, add_comm, ← Nat.choose_succ_succ]

private lemma hasSum_choose_div_pow2 :
    ∀ j : ℕ, HasSum (fun n : ℕ => (Nat.choose n j : ℝ) / 2 ^ (n + 1)) 1 := by
  intro j
  induction j with
  | zero =>
    simpa only [Nat.choose_zero_right, Nat.cast_one] using hasSum_half_pow
  | succ j ih =>
    have hs1 : Summable (fun n : ℕ => ‖(Nat.choose n j : ℝ) / 2 ^ (n + 1)‖) := by
      refine Summable.congr ih.summable fun n => ?_
      rw [Real.norm_of_nonneg (by positivity)]
    have hs2 : Summable (fun n : ℕ => ‖(1 : ℝ) / 2 ^ (n + 1)‖) := by
      refine Summable.congr hasSum_half_pow.summable fun n => ?_
      rw [Real.norm_of_nonneg (by positivity)]
    have hprod := hasSum_sum_range_mul_of_summable_norm hs1 hs2
    rw [ih.tsum_eq, hasSum_half_pow.tsum_eq, mul_one] at hprod
    have hshift : HasSum (fun n : ℕ => (Nat.choose (n + 1) (j + 1) : ℝ) / 2 ^ (n + 2)) 1 := by
      refine hprod.congr_fun fun n => ?_
      have hterm : ∀ k ∈ Finset.range (n + 1),
          ((Nat.choose k j : ℝ) / 2 ^ (k + 1)) * ((1 : ℝ) / 2 ^ (n - k + 1)) =
          (Nat.choose k j : ℝ) / 2 ^ (n + 2) := by
        intro k hk
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [div_mul_div_comm, mul_one, ← pow_add, show k + 1 + (n - k + 1) = n + 2 by omega]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Nat.cast_sum, sum_range_choose]
    have h0 : (Nat.choose 0 (j + 1) : ℝ) / 2 ^ (0 + 1) = 0 := by simp
    have hfull := (hasSum_nat_add_iff' 1 (f := fun n : ℕ => (Nat.choose n (j + 1) : ℝ) / 2 ^ (n + 1))).mp
      (by simpa [h0] using hshift)
    simpa [h0] using hfull

-- 2. Finite difference operators on ℤ → ℤ
private def Δ (f : ℤ → ℤ) : ℤ → ℤ := fun n => f (n + 1) - f n
private def U (f : ℤ → ℤ) : ℤ → ℤ := fun n => f (n + 1) + f (n - 1) - 2 * f n

private def Δn : ℕ → (ℤ → ℤ) → (ℤ → ℤ)
  | 0, f => f
  | d + 1, f => Δ (Δn d f)

private def S (d : ℕ) (f : ℤ → ℤ) : ℤ :=
  ∑ j ∈ Finset.range (d + 1), Δn j f 0

private lemma Δn_add (d : ℕ) (f g : ℤ → ℤ) :
    Δn d (fun n => f n + g n) = fun n => Δn d f n + Δn d g n := by
  induction d with
  | zero => rfl
  | succ d ih =>
    funext n
    simp only [Δn, Δ, ih]; ring

private lemma Δn_sub (d : ℕ) (f g : ℤ → ℤ) :
    Δn d (fun n => f n - g n) = fun n => Δn d f n - Δn d g n := by
  induction d with
  | zero => rfl
  | succ d ih =>
    funext n
    simp only [Δn, Δ, ih]; ring

private lemma Δn_const_mul (d : ℕ) (c : ℤ) (f : ℤ → ℤ) :
    Δn d (fun n => c * f n) = fun n => c * Δn d f n := by
  induction d with
  | zero => rfl
  | succ d ih =>
    funext n
    simp only [Δn, Δ, ih]; ring

private lemma Δn_shift (d : ℕ) (c : ℤ) (f : ℤ → ℤ) :
    Δn d (fun n => f (n + c)) = fun n => Δn d f (n + c) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    funext n
    simp only [Δn, Δ, ih]
    rw [show n + 1 + c = n + c + 1 by omega]

private lemma Δn_zero_of_le (d e : ℕ) (hde : d ≤ e) (f : ℤ → ℤ) (hd : Δn d f = 0) :
    Δn e f = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hde
  clear hde
  induction k with
  | zero => simpa using hd
  | succ k ih =>
    rw [← add_assoc]
    funext n
    simp only [Δn, Δ, ih, Pi.zero_apply, sub_self]

private lemma newton_formula (n : ℕ) :
    ∀ f : ℤ → ℤ, f n = ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℤ) * Δn j f 0 := by
  induction n with
  | zero => intro f; simp [Δn]
  | succ n ih =>
    intro f
    have h1 : f (n + 1 : ℕ) = f n + Δ f n := by
      simp only [Δ, Nat.cast_add, Nat.cast_one]; ring
    rw [h1, ih f, ih (Δ f)]
    have hΔ : ∀ j, Δn j (Δ f) 0 = Δn (j + 1) f 0 := by
      intro j
      induction j with
      | zero => rfl
      | succ j ihj =>
        have : ∀ g : ℤ → ℤ, Δn (j + 1) (Δ g) = Δn (j + 2) g := by
          intro g
          clear ih ihj
          induction j generalizing g with
          | zero => rfl
          | succ m ihm =>
            simp only [Δn] at ihm ⊢
            rw [ihm]
        exact congr_fun (this f) 0
    simp_rw [hΔ]
    rw [Finset.sum_range_succ' (n := n + 1), Finset.sum_range_succ' (n := n)]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
    rw [show Δn 0 f 0 = f 0 from rfl]
    have h2 : (∑ k ∈ Finset.range (n + 1), (Nat.choose (n + 1) (k + 1) : ℤ) * Δn (k + 1) f 0) =
        (∑ k ∈ Finset.range (n + 1), (Nat.choose n (k + 1) : ℤ) * Δn (k + 1) f 0) +
        (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * Δn (k + 1) f 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hc : (Nat.choose (n + 1) (k + 1) : ℤ) = (Nat.choose n k : ℤ) + (Nat.choose n (k + 1) : ℤ) := by
        exact_mod_cast Nat.choose_succ_succ n k
      rw [hc]; ring
    rw [h2]
    have h3 : (∑ k ∈ Finset.range (n + 1), (Nat.choose n (k + 1) : ℤ) * Δn (k + 1) f 0) =
        ∑ k ∈ Finset.range n, (Nat.choose n (k + 1) : ℤ) * Δn (k + 1) f 0 := by
      rw [Finset.sum_range_succ]; simp
    rw [h3]; ring

private lemma newton_formula_trunc (d : ℕ) (f : ℤ → ℤ) (hd : Δn (d + 1) f = 0) (n : ℕ) :
    f n = ∑ j ∈ Finset.range (d + 1), (Nat.choose n j : ℤ) * Δn j f 0 := by
  rw [newton_formula n f]
  by_cases hnd : n ≤ d
  · refine Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj => ?_
    simp only [Finset.mem_range, not_lt] at hj
    simp [Nat.choose_eq_zero_of_lt (by omega : n < j)]
  · symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj => ?_
    simp only [Finset.mem_range, not_lt] at hj
    have hz : Δn j f = 0 := Δn_zero_of_le (d + 1) j (by omega) f hd
    simp [hz]

private lemma hasSum_poly_div_pow2 (d : ℕ) (f : ℤ → ℤ) (hd : Δn (d + 1) f = 0) :
    HasSum (fun n : ℕ => (f n : ℝ) / 2 ^ (n + 1)) (S d f : ℝ) := by
  have hsum : HasSum (fun n : ℕ =>
      ∑ j ∈ Finset.range (d + 1), (Δn j f 0 : ℝ) * ((Nat.choose n j : ℝ) / 2 ^ (n + 1)))
      (∑ j ∈ Finset.range (d + 1), (Δn j f 0 : ℝ) * 1) :=
    hasSum_sum fun j _ => (hasSum_choose_div_pow2 j).mul_left (Δn j f 0 : ℝ)
  simp only [mul_one, ← Int.cast_sum] at hsum
  refine hsum.congr_fun fun n => ?_
  rw [newton_formula_trunc d f hd n, Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Int.cast_mul, Int.cast_natCast]; ring

-- 3. Even-polynomial divisibility by 3 via U = E + E⁻¹ - 2
private lemma S_shift (d : ℕ) (f : ℤ → ℤ) (hd : Δn (d + 1) f = 0) :
    S d (fun n => f (n + 1)) = 2 * S d f - f 0 := by
  have hstep : ∀ j, Δn j (fun n => f (n + 1)) 0 = Δn j f 0 + Δn (j + 1) f 0 := by
    intro j
    rw [Δn_shift j 1 f]
    simp only [zero_add, Δn, Δ]; ring
  simp only [S, hstep, Finset.sum_add_distrib]
  have htail : ∑ j ∈ Finset.range (d + 1), Δn (j + 1) f 0 =
      (∑ j ∈ Finset.range (d + 1), Δn j f 0) - f 0 := by
    have h1 := Finset.sum_range_succ' (f := fun j => Δn j f 0) (d + 1)
    have h2 := Finset.sum_range_succ (f := fun j => Δn j f 0) (d + 1)
    have hz : Δn (d + 1) f 0 = 0 := congr_fun hd 0
    rw [show Δn 0 f 0 = f 0 from rfl] at h1
    linarith
  linarith

private lemma S_U_even (d : ℕ) (f : ℤ → ℤ) (hd : Δn (d + 1) f = 0)
    (heven : ∀ n : ℤ, f (-n) = f n) :
    2 * S d f = 2 * f 0 + 4 * S d (U f) - U f 0 := by
  have hE := S_shift d f hd
  have hd_m1 : Δn (d + 1) (fun n => f (n - 1)) = 0 := by
    have : (fun n : ℤ => f (n - 1)) = (fun n : ℤ => f (n + (-1))) := by funext n; ring_nf
    rw [this, Δn_shift, hd]; rfl
  have hEm1 := S_shift d (fun n => f (n - 1)) hd_m1
  simp only [show (fun n : ℤ => f (n + 1 - 1)) = f from by funext n; simp, zero_sub] at hEm1
  have hU_Δ : ∀ j, Δn j (U f) 0 =
      Δn j (fun n => f (n + 1)) 0 + Δn j (fun n => f (n - 1)) 0 - 2 * Δn j f 0 := by
    intro j
    change Δn j (fun n => (f (n + 1) + f (n - 1)) - 2 * f n) 0 = _
    rw [Δn_sub, Δn_add, Δn_const_mul]
  have hU_lin : S d (U f) = S d (fun n => f (n + 1)) + S d (fun n => f (n - 1)) - 2 * S d f := by
    simp only [S, hU_Δ, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hU0 : U f 0 = 2 * f (-1) - 2 * f 0 := by
    simp only [U, zero_add, zero_sub]
    have := heven 1
    linarith
  linarith

private lemma Δn_U (d : ℕ) (f : ℤ → ℤ) (hd : Δn (d + 2) f = 0) :
    Δn d (U f) = 0 := by
  have hU_eq : U f = fun n => Δn 2 f (n + (-1)) := by
    funext n
    simp only [U, Δn, Δ]
    rw [show n + (-1) + 1 = n by omega, show n + (-1) = n - 1 by omega]
    ring
  rw [hU_eq, Δn_shift]
  have hcomp : ∀ a b : ℕ, ∀ g : ℤ → ℤ, Δn a (Δn b g) = Δn (a + b) g := by
    intro a b g
    induction a with
    | zero => simp [Δn]
    | succ a iha =>
      simp only [Δn, iha]
      rw [show a + 1 + b = a + b + 1 by omega]
      rfl
  rw [hcomp d 2 f, hd]; rfl

private lemma three_dvd_S_even :
    ∀ m : ℕ, ∀ f : ℤ → ℤ, Δn (2 * m + 1) f = 0 → (∀ n : ℤ, f (-n) = f n) →
      (3 : ℤ) ∣ (2 * S (2 * m) f - 2 * f 0) := by
  intro m
  induction m with
  | zero =>
    intro f _ _
    simp [S, Δn]
  | succ m ih =>
    intro f hd heven
    have hU_even : ∀ n : ℤ, U f (-n) = U f n := by
      intro n
      simp only [U]
      have h1 := heven (n - 1)
      have h2 := heven (n + 1)
      have h3 := heven n
      rw [show -(n - 1) = -n + 1 by omega] at h1
      rw [show -(n + 1) = -n - 1 by omega] at h2
      linarith
    have hU_d : Δn (2 * m + 1) (U f) = 0 := Δn_U (2 * m + 1) f (by simpa [mul_add] using hd)
    have hS_trunc : S (2 * (m + 1)) (U f) = S (2 * m) (U f) := by
      simp only [S]
      have hz1 : Δn (2 * m + 1) (U f) 0 = 0 := congr_fun hU_d 0
      have hz2 : Δn (2 * m + 2) (U f) 0 = 0 :=
        congr_fun (Δn_zero_of_le (2 * m + 1) (2 * m + 2) (by omega) (U f) hU_d) 0
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, Finset.sum_range_succ,
        Finset.sum_range_succ, hz1, hz2, add_zero, add_zero]
    have hrec := S_U_even (2 * (m + 1)) f (by simpa [mul_add] using hd) heven
    rw [hS_trunc] at hrec
    have hih := ih (U f) hU_d hU_even
    have hrew : 2 * S (2 * (m + 1)) f - 2 * f 0 =
        2 * (2 * S (2 * m) (U f) - 2 * U f 0) + 3 * U f 0 := by linarith
    rw [hrew]
    exact dvd_add (dvd_mul_of_dvd_right hih 2) (dvd_mul_right 3 _)

-- 4. Polynomials over ℚ vanish under Δn (d + 1)
private def ΔQ (f : ℤ → ℚ) : ℤ → ℚ := fun n => f (n + 1) - f n

private def ΔQn : ℕ → (ℤ → ℚ) → (ℤ → ℚ)
  | 0, f => f
  | d + 1, f => ΔQ (ΔQn d f)

private lemma ΔQn_cast (d : ℕ) (f : ℤ → ℤ) (n : ℤ) :
    (Δn d f n : ℚ) = ΔQn d (fun k => (f k : ℚ)) n := by
  induction d generalizing n with
  | zero => rfl
  | succ d ih =>
    simp only [Δn, Δ, ΔQn, ΔQ, Int.cast_sub, ih]

private lemma ΔQn_zero (k : ℕ) : ΔQn k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext n
    simp [ΔQn, ΔQ, ih]

private lemma ΔQn_poly_zero :
    ∀ d : ℕ, ∀ P : Polynomial ℚ, P.natDegree < d →
      ΔQn d (fun n : ℤ => P.eval (n : ℚ)) = 0 := by
  intro d
  induction d with
  | zero => intro P hP; omega
  | succ d ih =>
    intro P hP
    by_cases hP0 : P = 0
    · subst hP0
      have : (fun n : ℤ => (0 : Polynomial ℚ).eval (n : ℚ)) = 0 := by funext n; simp
      rw [this]
      exact ΔQn_zero (d + 1)
    · have hQ : ∀ n : ℤ, ΔQ (fun k : ℤ => P.eval (k : ℚ)) n =
          (P.comp (Polynomial.X + 1) - P).eval (n : ℚ) := by
        intro n
        simp only [ΔQ, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_one, Int.cast_add, Int.cast_one]
      have hcomm : ∀ k : ℕ, ∀ g : ℤ → ℚ, ΔQn (k + 1) g = ΔQn k (ΔQ g) := by
        intro k g
        induction k generalizing g with
        | zero => rfl
        | succ m ihm =>
          simp only [ΔQn] at ihm ⊢
          rw [ihm]
      rw [hcomm d, funext hQ]
      by_cases hdeg0 : P.natDegree = 0
      · have hconst : P.comp (Polynomial.X + 1) - P = 0 := by
          rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0]
          simp
        rw [hconst]
        have : (fun n : ℤ => (0 : Polynomial ℚ).eval (n : ℚ)) = 0 := by funext n; simp
        rw [this]
        exact ΔQn_zero d
      · have hdeg_lt : (P.comp (Polynomial.X + 1) - P).natDegree < d := by
          have hX1 : (Polynomial.X + (1 : Polynomial ℚ)).natDegree = 1 := by
            rw [show (1 : Polynomial ℚ) = Polynomial.C 1 from rfl, Polynomial.natDegree_X_add_C]
          have hdeg_comp : (P.comp (Polynomial.X + 1)).natDegree = P.natDegree := by
            rw [Polynomial.natDegree_comp, hX1, mul_one]
          have hlc : (P.comp (Polynomial.X + 1)).leadingCoeff = P.leadingCoeff := by
            rw [Polynomial.leadingCoeff_comp (by omega)]
            have : (Polynomial.X + (1 : Polynomial ℚ)).leadingCoeff = 1 := by
              rw [show (1 : Polynomial ℚ) = Polynomial.C 1 from rfl, Polynomial.leadingCoeff_X_add_C]
            simp [this]
          have hle : (P.comp (Polynomial.X + 1) - P).natDegree ≤ P.natDegree := by
            refine (Polynomial.natDegree_sub_le _ _).trans ?_
            rw [hdeg_comp, max_self]
          by_cases hsub0 : P.comp (Polynomial.X + 1) - P = 0
          · rw [hsub0, Polynomial.natDegree_zero]; omega
          · have hne : (P.comp (Polynomial.X + 1) - P).natDegree ≠ P.natDegree := by
              intro heq
              have hc : (P.comp (Polynomial.X + 1) - P).coeff P.natDegree = 0 := by
                rw [Polynomial.coeff_sub, ← hdeg_comp, Polynomial.coeff_natDegree,
                  hdeg_comp, Polynomial.coeff_natDegree, hlc, sub_self]
              rw [← heq, Polynomial.coeff_natDegree] at hc
              exact Polynomial.leadingCoeff_ne_zero.mpr hsub0 hc
            omega
        exact ih _ hdeg_lt

private def chooseSq (k : ℕ) (n : ℤ) : ℤ := (Nat.choose (n.natAbs ^ 2) k : ℤ)

private lemma chooseSq_poly (k : ℕ) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ 2 * k ∧
      ∀ n : ℤ, (chooseSq k n : ℚ) = P.eval (n : ℚ) := by
  refine ⟨((Nat.factorial k : ℚ)⁻¹) • (∏ i ∈ Finset.range k, (Polynomial.X ^ 2 - Polynomial.C (i : ℚ))),
    ?_, ?_⟩
  · refine (Polynomial.natDegree_smul_le _ _).trans ?_
    refine (Polynomial.natDegree_prod_le (Finset.range k)
      (fun i => Polynomial.X ^ 2 - Polynomial.C (i : ℚ))).trans ?_
    have h1 : ∀ i ∈ Finset.range k,
        (Polynomial.X ^ 2 - Polynomial.C (i : ℚ)).natDegree ≤ 2 := by
      intro i _
      refine (Polynomial.natDegree_sub_le _ _).trans ?_
      simp
    have hsum : (∑ i ∈ Finset.range k, (Polynomial.X ^ 2 - Polynomial.C (i : ℚ)).natDegree) ≤
        ∑ _i ∈ Finset.range k, 2 := Finset.sum_le_sum h1
    simpa [mul_comm] using hsum
  · intro n
    simp only [chooseSq, Int.cast_natCast, Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    have hsq : ((n.natAbs ^ 2 : ℕ) : ℚ) = (n : ℚ) ^ 2 := by
      have h : ((n.natAbs : ℤ) ^ 2 : ℤ) = n ^ 2 := Int.natAbs_sq n
      have hq := congr_arg (Int.cast (R := ℚ)) h
      simp at hq ⊢
    have hdesc : (Nat.choose (n.natAbs ^ 2) k : ℚ) * (Nat.factorial k : ℚ) =
        ∏ i ∈ Finset.range k, (((n.natAbs ^ 2 : ℕ) : ℚ) - (i : ℚ)) := by
      have h1 : (Nat.descFactorial (n.natAbs ^ 2) k : ℚ) =
          (Nat.choose (n.natAbs ^ 2) k : ℚ) * (Nat.factorial k : ℚ) := by
        have := Nat.descFactorial_eq_factorial_mul_choose (n.natAbs ^ 2) k
        rw [mul_comm] at this
        exact_mod_cast this
      rw [← h1]
      clear hsq h1
      set m := n.natAbs ^ 2
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.prod_range_succ, ← ih, Nat.descFactorial_succ, Nat.cast_mul, mul_comm]
        by_cases hkm : k ≤ m
        · rw [Nat.cast_sub hkm]
        · have h0 : Nat.descFactorial m k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
          simp [h0]
    rw [← hsq, ← hdesc]
    have hfk : (Nat.factorial k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    field_simp [hfk]

private lemma chooseSq_Δn_zero (k : ℕ) : Δn (2 * k + 1) (chooseSq k) = 0 := by
  obtain ⟨P, hdeg, heval⟩ := chooseSq_poly k
  funext n
  have h0 : (Δn (2 * k + 1) (chooseSq k) n : ℚ) = 0 := by
    rw [ΔQn_cast]
    have hfun : (fun m : ℤ => (chooseSq k m : ℚ)) = (fun m : ℤ => P.eval (m : ℚ)) := funext heval
    rw [hfun, ΔQn_poly_zero (2 * k + 1) P (by omega)]
    rfl
  exact_mod_cast h0

private lemma three_dvd_S_chooseSq (k : ℕ) (hk : 0 < k) :
    (3 : ℤ) ∣ S (2 * k) (chooseSq k) := by
  have hev : ∀ n : ℤ, chooseSq k (-n) = chooseSq k n := by
    intro n; simp [chooseSq]
  have h0 : chooseSq k 0 = 0 := by
    simp only [chooseSq, Int.natAbs_zero, zero_pow (by omega : 2 ≠ 0)]
    rw [show k = (k - 1) + 1 by omega, Nat.choose_zero_succ]
    simp
  have hdvd := three_dvd_S_even k (chooseSq k) (chooseSq_Δn_zero k) hev
  rw [h0, mul_zero, sub_zero] at hdvd
  have hcop : IsCoprime (3 : ℤ) 2 := by decide
  exact hcop.dvd_of_dvd_mul_left hdvd

private lemma choose_add_one_poly (r : ℕ) :
    ∃ Q : Polynomial ℚ, Q.natDegree ≤ r ∧
      ∀ n : ℕ, (Nat.choose (n + 1) r : ℚ) = Q.eval (n : ℚ) := by
  refine ⟨((Nat.factorial r : ℚ)⁻¹) •
      (∏ i ∈ Finset.range r, (Polynomial.X + 1 - Polynomial.C (i : ℚ))), ?_, ?_⟩
  · refine (Polynomial.natDegree_smul_le _ _).trans ?_
    refine (Polynomial.natDegree_prod_le (Finset.range r)
      (fun i => Polynomial.X + 1 - Polynomial.C (i : ℚ))).trans ?_
    have h1 : ∀ i ∈ Finset.range r,
        (Polynomial.X + 1 - Polynomial.C (i : ℚ)).natDegree ≤ 1 := by
      intro i _
      refine (Polynomial.natDegree_sub_le _ _).trans ?_
      rw [show (1 : Polynomial ℚ) = Polynomial.C 1 from rfl, Polynomial.natDegree_X_add_C]
      simp
    have hsum : (∑ i ∈ Finset.range r, (Polynomial.X + 1 - Polynomial.C (i : ℚ)).natDegree) ≤
        ∑ _i ∈ Finset.range r, 1 := Finset.sum_le_sum h1
    simpa using hsum
  · intro n
    simp only [Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
      Polynomial.eval_C]
    have hdesc : (Nat.choose (n + 1) r : ℚ) * (Nat.factorial r : ℚ) =
        ∏ i ∈ Finset.range r, ((n : ℚ) + 1 - (i : ℚ)) := by
      have h1 : (Nat.descFactorial (n + 1) r : ℚ) =
          (Nat.choose (n + 1) r : ℚ) * (Nat.factorial r : ℚ) := by
        have := Nat.descFactorial_eq_factorial_mul_choose (n + 1) r
        rw [mul_comm] at this
        exact_mod_cast this
      rw [← h1]
      clear h1
      induction r with
      | zero => simp
      | succ r ih =>
        rw [Finset.prod_range_succ, ← ih, Nat.descFactorial_succ, Nat.cast_mul, mul_comm]
        by_cases hrn : r ≤ n + 1
        · rw [Nat.cast_sub hrn, Nat.cast_add, Nat.cast_one]
        · have h0 : Nat.descFactorial (n + 1) r = 0 :=
            Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
          simp [h0]
    rw [← hdesc]
    have hfr : (Nat.factorial r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
    field_simp [hfr]

private def ΔN : ℕ → (ℕ → ℤ) → (ℕ → ℤ)
  | 0, g => g
  | d + 1, g => fun n => ΔN d g (n + 1) - ΔN d g n

private lemma hasSum_chooseSq_mul_choose (j r : ℕ) :
    ∃ M : ℤ, HasSum (fun n : ℕ =>
      ((Nat.choose (n ^ 2) j : ℝ) * (Nat.choose (n + 1) r : ℝ)) / 2 ^ (n + 1)) (M : ℝ) := by
  obtain ⟨P, hPdeg, hPeval⟩ := chooseSq_poly j
  obtain ⟨Q, hQdeg, hQeval⟩ := choose_add_one_poly r
  let fN : ℕ → ℤ := fun n => (Nat.choose (n ^ 2) j : ℤ) * (Nat.choose (n + 1) r : ℤ)
  have hΔN_zero : ∀ d : ℕ, ∀ R : Polynomial ℚ, R.natDegree < d →
      ∀ g : ℕ → ℤ, (∀ n : ℕ, (g n : ℚ) = R.eval (n : ℚ)) → ∀ n : ℕ, ΔN d g n = 0 := by
    intro d R hR g hg n
    have hcast : ∀ k : ℕ, ∀ h : ℕ → ℤ, ∀ m : ℕ,
        (ΔN k h m : ℚ) = ΔQn k (fun x : ℤ => if 0 ≤ x then (h x.toNat : ℚ) else 0) (m : ℤ) := by
      intro k
      induction k with
      | zero => intro h m; simp [ΔN, ΔQn]
      | succ k ihk =>
        intro h m
        simp only [ΔN, Int.cast_sub, ihk h (m + 1), ihk h m, ΔQn, ΔQ, Nat.cast_add, Nat.cast_one]
    have hcast_eq : ∀ k : ℕ, ∀ h1 h2 : ℤ → ℚ, (∀ m : ℕ, h1 m = h2 m) →
        ∀ m : ℕ, ΔQn k h1 m = ΔQn k h2 m := by
      intro k
      induction k with
      | zero => intro h1 h2 heq m; exact heq m
      | succ k ihk =>
        intro h1 h2 heq m
        simp only [ΔQn, ΔQ]
        have h1' := ihk h1 h2 heq (m + 1)
        have h2' := ihk h1 h2 heq m
        simp only [Nat.cast_add, Nat.cast_one] at h1'
        rw [h1', h2']
    have hq : (ΔN d g n : ℚ) = 0 := by
      rw [hcast d g n, hcast_eq d _ (fun x : ℤ => R.eval (x : ℚ)) (fun m => by
        simp [hg m]) n, ΔQn_poly_zero d R hR]
      rfl
    exact_mod_cast hq
  have hnewtN : ∀ m : ℕ, ∀ g : ℕ → ℤ,
      g m = ∑ i ∈ Finset.range (m + 1), (Nat.choose m i : ℤ) * ΔN i g 0 := by
    intro m g
    have h := newton_formula m (fun x : ℤ => if 0 ≤ x then g x.toNat else 0)
    have hΔeq : ∀ i : ℕ, ∀ t : ℕ,
        Δn i (fun x : ℤ => if 0 ≤ x then g x.toNat else 0) t = ΔN i g t := by
      intro i
      induction i with
      | zero => intro t; simp [Δn, ΔN]
      | succ i ihi =>
        intro t
        simp only [Δn, Δ, ΔN]
        have h1 := ihi (t + 1)
        have h2 := ihi t
        simp only [Nat.cast_add, Nat.cast_one] at h1
        rw [h1, h2]
    have hΔeq0 : ∀ i : ℕ, Δn i (fun x : ℤ => if 0 ≤ x then g x.toNat else 0) 0 = ΔN i g 0 :=
      fun i => hΔeq i 0
    simpa [hΔeq0] using h
  set D := 2 * j + r
  have hPQ : ∀ n : ℕ, (fN n : ℚ) = (P * Q).eval (n : ℚ) := by
    intro n
    have hP := hPeval (n : ℤ)
    simp only [chooseSq, Int.natAbs_natCast, Int.cast_natCast] at hP
    simp only [fN, Int.cast_mul, Int.cast_natCast, Polynomial.eval_mul]
    rw [← hQeval n, ← hP]
  have hdegPQ : (P * Q).natDegree < D + 1 := by
    have := Polynomial.natDegree_mul_le (p := P) (q := Q)
    omega
  have hzero : ∀ i : ℕ, D + 1 ≤ i → ΔN i fN 0 = 0 := by
    intro i hi
    exact hΔN_zero i (P * Q) (by omega) fN hPQ 0
  refine ⟨∑ i ∈ Finset.range (D + 1), ΔN i fN 0, ?_⟩
  have hsum : HasSum (fun n : ℕ =>
      ∑ i ∈ Finset.range (D + 1), (ΔN i fN 0 : ℝ) * ((Nat.choose n i : ℝ) / 2 ^ (n + 1)))
      (∑ i ∈ Finset.range (D + 1), (ΔN i fN 0 : ℝ) * 1) :=
    hasSum_sum fun i _ => (hasSum_choose_div_pow2 i).mul_left (ΔN i fN 0 : ℝ)
  simp only [mul_one, ← Int.cast_sum] at hsum
  refine hsum.congr_fun fun n => ?_
  have hfN_eq : fN n = ∑ i ∈ Finset.range (D + 1), (Nat.choose n i : ℤ) * ΔN i fN 0 := by
    rw [hnewtN n fN]
    by_cases hnD : n ≤ D
    · refine Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hi => ?_
      simp only [Finset.mem_range, not_lt] at hi
      simp [Nat.choose_eq_zero_of_lt (by omega : n < i)]
    · symm
      refine Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hi => ?_
      simp only [Finset.mem_range, not_lt] at hi
      simp [hzero i (by omega)]
  have hcast_fN : (fN n : ℝ) = (Nat.choose (n ^ 2) j : ℝ) * (Nat.choose (n + 1) r : ℝ) := by
    simp [fN]
  rw [← hcast_fN, hfN_eq, Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_mul, Int.cast_natCast]; ring

-- 5. 3-divisibility over ℤ[1/2]
private def IsDiv3Half (q : ℚ) : Prop :=
  ∃ z : ℤ, ∃ e : ℕ, q = (3 * z : ℚ) / (2 ^ e : ℚ)

private def IsHalfInt (q : ℚ) : Prop :=
  ∃ z : ℤ, ∃ e : ℕ, q = (z : ℚ) / (2 ^ e : ℚ)

private lemma isDiv3Half_zero : IsDiv3Half 0 := ⟨0, 0, by simp⟩

private lemma isDiv3Half_add {x y : ℚ} (hx : IsDiv3Half x) (hy : IsDiv3Half y) :
    IsDiv3Half (x + y) := by
  obtain ⟨z1, e1, rfl⟩ := hx
  obtain ⟨z2, e2, rfl⟩ := hy
  refine ⟨z1 * 2 ^ e2 + z2 * 2 ^ e1, e1 + e2, ?_⟩
  push_cast
  have h1 : (2 : ℚ) ^ e1 ≠ 0 := by positivity
  have h2 : (2 : ℚ) ^ e2 ≠ 0 := by positivity
  rw [pow_add]
  field_simp [h1, h2]

private lemma isDiv3Half_neg {x : ℚ} (hx : IsDiv3Half x) : IsDiv3Half (-x) := by
  obtain ⟨z, e, rfl⟩ := hx
  refine ⟨-z, e, ?_⟩
  push_cast; ring

private lemma isDiv3Half_sub {x y : ℚ} (hx : IsDiv3Half x) (hy : IsDiv3Half y) :
    IsDiv3Half (x - y) := by
  rw [sub_eq_add_neg]; exact isDiv3Half_add hx (isDiv3Half_neg hy)

private lemma isDiv3Half_mul_halfInt {x y : ℚ} (hx : IsDiv3Half x) (hy : IsHalfInt y) :
    IsDiv3Half (x * y) := by
  obtain ⟨z1, e1, rfl⟩ := hx
  obtain ⟨z2, e2, rfl⟩ := hy
  refine ⟨z1 * z2, e1 + e2, ?_⟩
  push_cast; rw [pow_add]; ring

private lemma isDiv3Half_int_mul {m : ℤ} {x : ℚ} (hx : IsDiv3Half x) :
    IsDiv3Half ((m : ℚ) * x) := by
  rw [mul_comm]
  exact isDiv3Half_mul_halfInt hx ⟨m, 0, by simp⟩

private lemma isDiv3Half_of_int {m : ℤ} (hm : (3 : ℤ) ∣ m) : IsDiv3Half (m : ℚ) := by
  obtain ⟨z, rfl⟩ := hm
  exact ⟨z, 0, by push_cast; simp⟩

private lemma isDiv3Half_div2 {x : ℚ} (hx : IsDiv3Half x) : IsDiv3Half (x / 2) := by
  obtain ⟨z, e, rfl⟩ := hx
  refine ⟨z, e + 1, ?_⟩
  rw [div_div, pow_succ]

private lemma isDiv3Half_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, IsDiv3Half (f i)) : IsDiv3Half (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [isDiv3Half_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isDiv3Half_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma isHalfInt_add {x y : ℚ} (hx : IsHalfInt x) (hy : IsHalfInt y) :
    IsHalfInt (x + y) := by
  obtain ⟨z1, e1, rfl⟩ := hx
  obtain ⟨z2, e2, rfl⟩ := hy
  refine ⟨z1 * 2 ^ e2 + z2 * 2 ^ e1, e1 + e2, ?_⟩
  push_cast
  have h1 : (2 : ℚ) ^ e1 ≠ 0 := by positivity
  have h2 : (2 : ℚ) ^ e2 ≠ 0 := by positivity
  rw [pow_add]
  field_simp [h1, h2]

private lemma isHalfInt_neg {x : ℚ} (hx : IsHalfInt x) : IsHalfInt (-x) := by
  obtain ⟨z, e, rfl⟩ := hx
  exact ⟨-z, e, by push_cast; ring⟩

private lemma isHalfInt_mul {x y : ℚ} (hx : IsHalfInt x) (hy : IsHalfInt y) :
    IsHalfInt (x * y) := by
  obtain ⟨z1, e1, rfl⟩ := hx
  obtain ⟨z2, e2, rfl⟩ := hy
  exact ⟨z1 * z2, e1 + e2, by push_cast; rw [pow_add]; ring⟩

private lemma isHalfInt_div2 {x : ℚ} (hx : IsHalfInt x) : IsHalfInt (x / 2) := by
  obtain ⟨z, e, rfl⟩ := hx
  exact ⟨z, e + 1, by rw [div_div, pow_succ]⟩

private lemma isHalfInt_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, IsHalfInt (f i)) : IsHalfInt (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isHalfInt_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma isDiv3Half_to_int_dvd {m : ℤ} (h : IsDiv3Half (m : ℚ)) : (3 : ℤ) ∣ m := by
  obtain ⟨z, e, heq⟩ := h
  have h2ne : (2 : ℚ) ^ e ≠ 0 := by positivity
  have hmul : (m : ℚ) * (2 : ℚ) ^ e = (3 * z : ℚ) := (eq_div_iff h2ne).mp heq
  have hint : m * 2 ^ e = 3 * z := by exact_mod_cast hmul
  have hdvd : (3 : ℤ) ∣ m * 2 ^ e := ⟨z, hint⟩
  have hcop : IsCoprime (3 : ℤ) ((2 : ℤ) ^ e) := (by decide : IsCoprime (3 : ℤ) 2).pow_right
  exact hcop.dvd_of_dvd_mul_right hdvd

-- 6. Main theorem
private theorem main_proved :
    ∀ a : ℕ → ℤ,
      a 0 = 1 →
      ∀ B : PowerSeries ℚ,
        B * (1 + PowerSeries.mk (fun k => (a k : ℚ))) = 1 →
        (∀ k : ℕ,
          HasSum (fun n : ℕ =>
            ((PowerSeries.coeff k ((1 + PowerSeries.X) ^ (n ^ 2) * B ^ (n + 1)) : ℚ) : ℝ))
            (if k = 0 then 1 else 0)) →
        ∀ k : ℕ, 0 < k → (3 : ℤ) ∣ a k := by
  intro a ha0 B hBA hsum_eq
  set A : PowerSeries ℚ := PowerSeries.mk (fun k => (a k : ℚ))
  have hB0 : PowerSeries.coeff 0 B = 1 / 2 := by
    have h0 := congr_arg (PowerSeries.coeff 0) hBA
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => PowerSeries.coeff i B * PowerSeries.coeff j (1 + A))] at h0
    simp only [Finset.range_one, Finset.sum_singleton, Nat.sub_zero, map_add, PowerSeries.coeff_one,
      ↓reduceIte, A, PowerSeries.coeff_mk, ha0, Int.cast_one] at h0
    linarith
  have hB_rec : ∀ m : ℕ, 0 < m →
      2 * PowerSeries.coeff m B =
      -(∑ i ∈ Finset.Ico 1 (m + 1), (a i : ℚ) * PowerSeries.coeff (m - i) B) := by
    intro m hm
    have hm0 := congr_arg (PowerSeries.coeff m) hBA
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => PowerSeries.coeff i B * PowerSeries.coeff j (1 + A))] at hm0
    simp only [PowerSeries.coeff_one, show m ≠ 0 by omega, ↓reduceIte] at hm0
    rw [Finset.sum_range_succ] at hm0
    have hrew : ∑ x ∈ Finset.range m,
          PowerSeries.coeff x B * PowerSeries.coeff (m - x) (1 + A) =
        ∑ i ∈ Finset.Ico 1 (m + 1), (a i : ℚ) * PowerSeries.coeff (m - i) B := by
      refine Finset.sum_bij (fun x _ => m - x) ?_ ?_ ?_ ?_
      · intro x hx; simp only [Finset.mem_range] at hx; simp only [Finset.mem_Ico]; omega
      · intro x1 hx1 x2 hx2 h; simp only [Finset.mem_range] at hx1 hx2; omega
      · intro i hi; simp only [Finset.mem_Ico] at hi
        exact ⟨m - i, Finset.mem_range.mpr (by omega), by omega⟩
      · intro x hx
        simp only [Finset.mem_range] at hx
        have hmx : m - x ≠ 0 := by omega
        simp only [map_add, PowerSeries.coeff_one, hmx, ↓reduceIte, zero_add, A,
          PowerSeries.coeff_mk, show m - (m - x) = x by omega]
        ring
    rw [hrew] at hm0
    simp only [Nat.sub_self, map_add, PowerSeries.coeff_one, ↓reduceIte, A, PowerSeries.coeff_mk,
      ha0, Int.cast_one] at hm0
    linarith
  have hB_half : ∀ m : ℕ, IsHalfInt (PowerSeries.coeff m B) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      cases m with
      | zero => exact ⟨1, 1, by simp [hB0]⟩
      | succ m =>
        have hr := hB_rec (m + 1) (by omega)
        have hEq : PowerSeries.coeff (m + 1) B =
            (-(∑ i ∈ Finset.Ico 1 (m + 2), (a i : ℚ) * PowerSeries.coeff (m + 1 - i) B)) / 2 := by
          linarith
        rw [hEq]
        refine isHalfInt_div2 (isHalfInt_neg (isHalfInt_sum _ _ fun i hi => ?_))
        simp only [Finset.mem_Ico] at hi
        exact isHalfInt_mul ⟨a i, 0, by simp⟩ (ih (m + 1 - i) (by omega))
  -- Define C = 2 * B - 1 so B = (1/2) * (1 + C) and coeff 0 C = 0
  set C : PowerSeries ℚ := 2 * B - 1
  have hcoeff_2B : ∀ m : ℕ, PowerSeries.coeff m (2 * B) = 2 * PowerSeries.coeff m B := by
    intro m; rw [two_mul, map_add, two_mul]
  have hC0 : PowerSeries.coeff 0 C = 0 := by
    simp only [C, map_sub, hcoeff_2B, hB0, PowerSeries.coeff_one, ↓reduceIte]
    norm_num
  have hB_eq : B = (1 / 2 : ℚ) • (1 + C) := by
    ext m
    simp only [C, PowerSeries.coeff_smul, smul_eq_mul, map_add, map_sub, hcoeff_2B]
    ring
  have hC_half : ∀ m : ℕ, IsHalfInt (PowerSeries.coeff m C) := by
    intro m
    simp only [C, map_sub, hcoeff_2B, PowerSeries.coeff_one]
    have h1 : IsHalfInt (2 * PowerSeries.coeff m B) :=
      isHalfInt_mul ⟨2, 0, by simp⟩ (hB_half m)
    split_ifs
    · rw [sub_eq_add_neg]; exact isHalfInt_add h1 ⟨-1, 0, by simp⟩
    · simpa using h1
  -- Strong induction on k > 0
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hB_div3 : ∀ m : ℕ, 0 < m → m < k → IsDiv3Half (PowerSeries.coeff m B) := by
      intro m hm hmk
      induction m using Nat.strong_induction_on with
      | h m ihm =>
        have hr := hB_rec m hm
        have hEq : PowerSeries.coeff m B =
            (-(∑ i ∈ Finset.Ico 1 (m + 1), (a i : ℚ) * PowerSeries.coeff (m - i) B)) / 2 := by
          linarith
        rw [hEq]
        refine isDiv3Half_div2 (isDiv3Half_neg (isDiv3Half_sum _ _ fun i hi => ?_))
        simp only [Finset.mem_Ico] at hi
        exact isDiv3Half_mul_halfInt (isDiv3Half_of_int (ih i (by omega) (by omega))) (hB_half (m - i))
    have hC_div3 : ∀ m : ℕ, 0 < m → m < k → IsDiv3Half (PowerSeries.coeff m C) := by
      intro m hm hmk
      have hCm : PowerSeries.coeff m C = 2 * PowerSeries.coeff m B := by
        simp only [C, map_sub, hcoeff_2B, PowerSeries.coeff_one, show m ≠ 0 by omega, ↓reduceIte,
          sub_zero]
      rw [hCm, mul_comm]
      exact isDiv3Half_mul_halfInt (hB_div3 m hm hmk) ⟨2, 0, by simp⟩
    have hCk_div3 : IsDiv3Half (PowerSeries.coeff k C + (a k : ℚ) / 2) := by
      have hCk : PowerSeries.coeff k C = 2 * PowerSeries.coeff k B := by
        simp only [C, map_sub, hcoeff_2B, PowerSeries.coeff_one, show k ≠ 0 by omega, ↓reduceIte,
          sub_zero]
      rw [hCk, hB_rec k hk]
      have hsplit : ∑ i ∈ Finset.Ico 1 (k + 1), (a i : ℚ) * PowerSeries.coeff (k - i) B =
          (∑ i ∈ Finset.Ico 1 k, (a i : ℚ) * PowerSeries.coeff (k - i) B) +
          (a k : ℚ) * (1 / 2) := by
        rw [Finset.sum_Ico_succ_top (by omega), Nat.sub_self, hB0]
      rw [hsplit]
      have hrew : -((∑ i ∈ Finset.Ico 1 k, (a i : ℚ) * PowerSeries.coeff (k - i) B) +
            (a k : ℚ) * (1 / 2)) + (a k : ℚ) / 2 =
          -(∑ i ∈ Finset.Ico 1 k, (a i : ℚ) * PowerSeries.coeff (k - i) B) := by ring
      rw [hrew]
      refine isDiv3Half_neg (isDiv3Half_sum _ _ fun i hi => ?_)
      simp only [Finset.mem_Ico] at hi
      exact isDiv3Half_mul_halfInt (isDiv3Half_of_int (ih i (by omega) (by omega))) (hB_half (k - i))
    -- Powers of C: coeff m (C^r) = 0 for m < r, IsDiv3Half for 1 ≤ r and (m < k ∨ 2 ≤ r)
    have hCr_zero : ∀ r m : ℕ, m < r → PowerSeries.coeff m (C ^ r) = 0 := by
      intro r
      induction r with
      | zero => intro m hm; omega
      | succ r ihr =>
        intro m hm
        rw [pow_succ, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (f := fun i j => PowerSeries.coeff i (C ^ r) * PowerSeries.coeff j C)]
        refine Finset.sum_eq_zero fun x hx => ?_
        have hxm : x ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
        by_cases hxr : x < r
        · rw [ihr x hxr, zero_mul]
        · have : m - x = 0 := by omega
          rw [this, hC0, mul_zero]
    have hCr_div3 : ∀ r m : ℕ, 1 ≤ r → (m < k ∨ (m = k ∧ 2 ≤ r)) →
        IsDiv3Half (PowerSeries.coeff m (C ^ r)) := by
      intro r
      induction r with
      | zero => intro m hr; omega
      | succ r ihr =>
        intro m _ hm
        by_cases hr0 : r = 0
        · subst hr0
          simp only [Nat.zero_add, pow_one]
          by_cases hm0 : m = 0
          · subst hm0; rw [hC0]; exact isDiv3Half_zero
          · rcases hm with hlt | ⟨_, h2⟩
            · exact hC_div3 m (by omega) hlt
            · omega
        · rw [pow_succ, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (f := fun i j => PowerSeries.coeff i (C ^ r) * PowerSeries.coeff j C)]
          refine isDiv3Half_sum _ _ fun x hx => ?_
          have hxm : x ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
          by_cases hmx0 : m - x = 0
          · rw [hmx0, hC0, mul_zero]; exact isDiv3Half_zero
          · have hxl : x < k := by omega
            exact isDiv3Half_mul_halfInt (ihr x (by omega) (Or.inl hxl)) (hC_half (m - x))
    -- Expand coeff k ((1 + X)^(n^2) * B^(n+1)) as a finite sum over j, r!
    have hcoeff_expand : ∀ n : ℕ,
        PowerSeries.coeff k ((1 + PowerSeries.X) ^ (n ^ 2) * B ^ (n + 1)) =
        (∑ j ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (k - j + 1),
          PowerSeries.coeff (k - j) (C ^ r) *
            ((Nat.choose (n ^ 2) j : ℚ) * (Nat.choose (n + 1) r : ℚ))) / (2 ^ (n + 1) : ℚ) := by
      intro n
      rw [hB_eq, smul_pow, mul_smul_comm, PowerSeries.coeff_smul, smul_eq_mul, one_div, inv_pow,
        PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (f := fun i j => PowerSeries.coeff i ((1 + PowerSeries.X : PowerSeries ℚ) ^ (n ^ 2)) *
            PowerSeries.coeff j ((1 + C) ^ (n + 1))),
        div_eq_inv_mul]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hX : PowerSeries.coeff j ((1 + PowerSeries.X : PowerSeries ℚ) ^ (n ^ 2)) =
          (Nat.choose (n ^ 2) j : ℚ) := by
        have hpoly : ((1 + PowerSeries.X : PowerSeries ℚ) ^ (n ^ 2)) =
            (((1 + Polynomial.X : Polynomial ℚ) ^ (n ^ 2) : Polynomial ℚ) : PowerSeries ℚ) := by
          simp
        rw [hpoly, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
      have h1C : PowerSeries.coeff (k - j) ((1 + C) ^ (n + 1)) =
          ∑ r ∈ Finset.range (k - j + 1),
            (Nat.choose (n + 1) r : ℚ) * PowerSeries.coeff (k - j) (C ^ r) := by
        rw [add_comm 1 C, add_pow, map_sum]
        have hterm : ∀ r,
            PowerSeries.coeff (k - j) (C ^ r * 1 ^ (n + 1 - r) * ((Nat.choose (n + 1) r : ℕ) : PowerSeries ℚ)) =
            (Nat.choose (n + 1) r : ℚ) * PowerSeries.coeff (k - j) (C ^ r) := by
          intro r
          rw [one_pow, mul_one, mul_comm, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
        simp_rw [hterm]
        by_cases hle : n + 1 ≤ k - j
        · refine Finset.sum_subset (Finset.range_mono (by omega)) fun r _ hr => ?_
          simp only [Finset.mem_range, not_lt] at hr
          simp [Nat.choose_eq_zero_of_lt (by omega : n + 1 < r)]
        · symm
          refine Finset.sum_subset (Finset.range_mono (by omega)) fun r _ hr => ?_
          simp only [Finset.mem_range, not_lt] at hr
          rw [hCr_zero r (k - j) (by omega), mul_zero]
      rw [hX, h1C, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => by ring
    -- Build the HasSum of the right-hand side!
    choose M hM using hasSum_chooseSq_mul_choose
    have hHasSum_rhs : HasSum (fun n : ℕ =>
        ((PowerSeries.coeff k ((1 + PowerSeries.X) ^ (n ^ 2) * B ^ (n + 1)) : ℚ) : ℝ))
        ((∑ j ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (k - j + 1),
          PowerSeries.coeff (k - j) (C ^ r) * (M j r : ℚ) : ℚ) : ℝ) := by
      have h1 : HasSum (fun n : ℕ =>
          ∑ j ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (k - j + 1),
            ((PowerSeries.coeff (k - j) (C ^ r) : ℚ) : ℝ) *
              (((Nat.choose (n ^ 2) j : ℝ) * (Nat.choose (n + 1) r : ℝ)) / 2 ^ (n + 1)))
          (∑ j ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (k - j + 1),
            ((PowerSeries.coeff (k - j) (C ^ r) : ℚ) : ℝ) * (M j r : ℝ)) :=
        hasSum_sum fun j _ => hasSum_sum fun r _ => (hM j r).mul_left _
      have hcast_sum : (∑ j ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (k - j + 1),
            ((PowerSeries.coeff (k - j) (C ^ r) : ℚ) : ℝ) * (M j r : ℝ)) =
          ((∑ j ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (k - j + 1),
            PowerSeries.coeff (k - j) (C ^ r) * (M j r : ℚ) : ℚ) : ℝ) := by
        push_cast; rfl
      rw [hcast_sum] at h1
      refine h1.congr_fun fun n => ?_
      rw [hcoeff_expand n]
      push_cast
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun r _ => by ring
    have htotal0 : (∑ j ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (k - j + 1),
        PowerSeries.coeff (k - j) (C ^ r) * (M j r : ℚ)) = 0 := by
      have hu := hHasSum_rhs.unique (hsum_eq k)
      simp only [show k ≠ 0 by omega, ↓reduceIte] at hu
      exact_mod_cast hu
    -- Evaluate M k 0 = S (2*k) (chooseSq k) and M 0 1 = 2
    have hMk0 : M k 0 = S (2 * k) (chooseSq k) := by
      have h1 := hM k 0
      simp only [Nat.choose_zero_right, Nat.cast_one, mul_one] at h1
      have h2 := hasSum_poly_div_pow2 (2 * k) (chooseSq k) (chooseSq_Δn_zero k)
      have h2' : HasSum (fun n : ℕ => (Nat.choose (n ^ 2) k : ℝ) / 2 ^ (n + 1))
          (S (2 * k) (chooseSq k) : ℝ) :=
        h2.congr_fun fun n => by simp [chooseSq]
      exact_mod_cast h1.unique h2'
    have hM01 : M 0 1 = 2 := by
      have h1 := hM 0 1
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.choose_one_right] at h1
      have h2 : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / 2 ^ (n + 1)) (2 : ℝ) := by
        have ha := (hasSum_choose_div_pow2 1).add (hasSum_choose_div_pow2 0)
        rw [show (1 : ℝ) + 1 = 2 by norm_num] at ha
        refine ha.congr_fun fun n => ?_
        simp only [Nat.choose_one_right, Nat.choose_zero_right, Nat.cast_one, Nat.cast_add]
        ring
      exact_mod_cast h1.unique h2
    -- Every term in htotal0 EXCEPT (j = 0, r = 1) is IsDiv3Half!
    have hterm_div3 : ∀ j ∈ Finset.range (k + 1), ∀ r ∈ Finset.range (k - j + 1),
        ¬(j = 0 ∧ r = 1) → IsDiv3Half (PowerSeries.coeff (k - j) (C ^ r) * (M j r : ℚ)) := by
      intro j hj r hr hne
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      by_cases hr0 : r = 0
      · subst hr0
        simp only [pow_zero, PowerSeries.coeff_one]
        by_cases hkj : k - j = 0
        · have hjeq : j = k := by omega
          rw [hkj, hjeq]
          simp only [↓reduceIte, one_mul, hMk0]
          exact isDiv3Half_of_int (three_dvd_S_chooseSq k hk)
        · simp only [hkj, ↓reduceIte, zero_mul]
          exact isDiv3Half_zero
      · rw [mul_comm]
        refine isDiv3Half_int_mul (hCr_div3 r (k - j) (by omega) ?_)
        by_cases hj0 : j = 0
        · subst hj0
          have hr2 : 2 ≤ r := by omega
          exact Or.inr ⟨by omega, hr2⟩
        · exact Or.inl (by omega)
    -- Extract (j = 0, r = 1) from htotal0: it equals 2 * coeff k C
    have hCk2_div3 : IsDiv3Half (PowerSeries.coeff k C * 2) := by
      have hsplit : (∑ j ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (k - j + 1),
            PowerSeries.coeff (k - j) (C ^ r) * (M j r : ℚ)) =
          PowerSeries.coeff k C * 2 +
          (∑ j ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (k - j + 1),
            if j = 0 ∧ r = 1 then 0 else PowerSeries.coeff (k - j) (C ^ r) * (M j r : ℚ)) := by
        have h0_mem : 0 ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
        have h1_mem : 1 ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
        have hinner : ∀ j ∈ Finset.range (k + 1),
            (∑ r ∈ Finset.range (k - j + 1), PowerSeries.coeff (k - j) (C ^ r) * (M j r : ℚ)) =
            (if j = 0 then PowerSeries.coeff k C * 2 else 0) +
            ∑ r ∈ Finset.range (k - j + 1),
              if j = 0 ∧ r = 1 then 0 else PowerSeries.coeff (k - j) (C ^ r) * (M j r : ℚ) := by
          intro j _
          by_cases hj0 : j = 0
          · subst hj0
            simp only [↓reduceIte, Nat.sub_zero, true_and]
            rw [← Finset.add_sum_erase _ _ h1_mem, ← Finset.add_sum_erase _ _ h1_mem]
            simp only [↓reduceIte, zero_add, pow_one, hM01, Int.cast_ofNat]
            congr 1
            refine Finset.sum_congr rfl fun r hr => ?_
            have hr1 : r ≠ 1 := (Finset.mem_erase.mp hr).1
            simp [hr1]
          · simp [hj0]
        rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single 0]
        · simp
        · intro j _ hj0; simp [hj0]
        · intro h; exact absurd h0_mem h
      rw [hsplit] at htotal0
      have hrest_div3 : IsDiv3Half (∑ j ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (k - j + 1),
          if j = 0 ∧ r = 1 then 0 else PowerSeries.coeff (k - j) (C ^ r) * (M j r : ℚ)) := by
        refine isDiv3Half_sum _ _ fun j hj => isDiv3Half_sum _ _ fun r hr => ?_
        split_ifs with hcond
        · exact isDiv3Half_zero
        · exact hterm_div3 j hj r hr hcond
      have heq : PowerSeries.coeff k C * 2 =
          -(∑ j ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (k - j + 1),
            if j = 0 ∧ r = 1 then 0 else PowerSeries.coeff (k - j) (C ^ r) * (M j r : ℚ)) := by
        linarith
      rw [heq]
      exact isDiv3Half_neg hrest_div3
    -- Combine IsDiv3Half (coeff k C + a k / 2) and IsDiv3Half (coeff k C * 2) => IsDiv3Half (a k)
    have ha_div3 : IsDiv3Half (a k : ℚ) := by
      have h2 := isDiv3Half_mul_halfInt hCk_div3 (⟨2, 0, by simp⟩ : IsHalfInt (2 : ℚ))
      have hsub := isDiv3Half_sub h2 hCk2_div3
      simpa [show (PowerSeries.coeff k C + (a k : ℚ) / 2) * (2 : ℚ) - PowerSeries.coeff k C * 2 =
        (a k : ℚ) by ring] using hsub
    exact isDiv3Half_to_int_dvd ha_div3

end OMA.S_oeis_a320949

theorem OMA.solution : type_of% @OMA.S_oeis_a320949.main :=
  OMA.S_oeis_a320949.main_proved
