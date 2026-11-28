import OMAStatements.S_oeis_a356145
import Mathlib

namespace OMA.P_oeis_a356145

open OMA.S_oeis_a356145

section Proof

variable {K : Type} [CommRing K] [Algebra ℚ K]

private lemma invFac_mul_fac (n : ℕ) :
    (Nat.factorial n : K) * invFac n = 1 := by
  unfold invFac
  rw [← map_natCast (algebraMap ℚ K), ← map_mul]
  have hne : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [mul_inv_cancel₀ hne, map_one]

private lemma invFac_succ_mul (n : ℕ) :
    invFac (n + 1) * ((n : K) + 1) = invFac n := by
  unfold invFac
  have h1 : ((n : K) + 1) = algebraMap ℚ K ((n : ℚ) + 1) := by simp
  rw [h1, ← map_mul]
  congr 1
  rw [Nat.factorial_succ]
  have hfac : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp [hfac, hn1]

private lemma invFac_zero : invFac (K := K) 0 = 1 := by
  simp [invFac]

private lemma invFac_one : invFac (K := K) 1 = 1 := by
  simp [invFac]

private lemma choose_mul_invFac (n j : ℕ) (hj : j ≤ n) :
    (Nat.choose n j : K) * invFac n = invFac j * invFac (n - j) := by
  have hq : (Nat.choose n j : ℚ) * (Nat.factorial n : ℚ)⁻¹ =
      (Nat.factorial j : ℚ)⁻¹ * (Nat.factorial (n - j) : ℚ)⁻¹ := by
    have hch : (Nat.choose n j : ℚ) * (Nat.factorial j : ℚ) * (Nat.factorial (n - j) : ℚ) =
        (Nat.factorial n : ℚ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
    have hfn : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hfj : (Nat.factorial j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have hfnj : (Nat.factorial (n - j) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - j))
    field_simp [hfn, hfj, hfnj]
    linarith
  unfold invFac
  rw [← map_natCast (algebraMap ℚ K), ← map_mul, ← map_mul, hq]

private lemma A_eq_X_mul_U (a : ℕ → K) :
    A_series a = PowerSeries.X * U_series a := by
  apply PowerSeries.ext; intro n
  cases n with
  | zero => simp [A_series]
  | succ m => simp [A_series, U_series, PowerSeries.coeff_succ_X_mul]

private lemma U_mul_xDivA (a : ℕ → K) (ha : a 0 = 1) :
    U_series a * xDivA a ha = 1 :=
  ((PowerSeries.isUnit_iff_constantCoeff (φ := U_series a)).mpr (by
    unfold U_series
    rw [PowerSeries.constantCoeff_mk, invFac, Nat.factorial_one, Nat.cast_one, inv_one,
      map_one, one_mul, ha]
    exact isUnit_one)).mul_val_inv

private lemma derivative_A_series (a : ℕ → K) :
    PowerSeries.derivative K (A_series a) = PowerSeries.mk fun n => invFac n * a n := by
  apply PowerSeries.ext; intro n
  rw [PowerSeries.coeff_derivative, A_series, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  rw [mul_right_comm, invFac_succ_mul]

private lemma derivative_derivative_A_series (a : ℕ → K) :
    PowerSeries.derivative K (PowerSeries.derivative K (A_series a)) =
      PowerSeries.mk fun n => invFac n * a (n + 1) := by
  rw [derivative_A_series]
  apply PowerSeries.ext; intro n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  rw [mul_right_comm, invFac_succ_mul]

-- Part 1: F_k(y) = ∑_{j≥1} R(j, k) * y^j / j! satisfies F_k'(y) * (1 + F_1(y)) = a(k) + F_{k+1}(y)!

private noncomputable def F_series (a : ℕ → K) (k : ℕ) : PowerSeries K :=
  PowerSeries.mk fun n => if n = 0 then 0 else invFac n * kurkovR a n k

private lemma F_ode (a : ℕ → K) (k : ℕ) :
    PowerSeries.derivative K (F_series a k) * (1 + F_series a 1) =
      PowerSeries.C (a k) + F_series a (k + 1) := by
  apply PowerSeries.ext; intro n
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [map_add, PowerSeries.coeff_C, PowerSeries.coeff_one, F_series,
    PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
  cases n with
  | zero =>
    simp [kurkovR, invFac_one]
  | succ m =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add]
    -- Split the sum at j = m + 1 (where (m + 1) - j = 0 gives 1 + 0 = 1)
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, ↓reduceIte, add_zero, mul_one]
    rw [mul_right_comm (invFac (m + 2)), invFac_succ_mul (m + 1)]
    have hrest :
        ∑ j ∈ Finset.range (m + 1),
          invFac (j + 1) * kurkovR a (j + 1) k * ((j : K) + 1) *
            ((if m + 1 - j = 0 then 1 else 0) +
              if m + 1 - j = 0 then 0 else invFac (m + 1 - j) * kurkovR a (m + 1 - j) 1) =
        invFac (m + 1) *
          ∑ j ∈ Finset.range (m + 1),
            (Nat.choose (m + 1) j : K) * kurkovR a (j + 1) k * kurkovR a (m + 1 - j) 1 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjm : j < m + 1 := Finset.mem_range.mp hj
      have hne : m + 1 - j ≠ 0 := by omega
      simp only [hne, ↓reduceIte, zero_add]
      rw [mul_right_comm (invFac (j + 1)), invFac_succ_mul j]
      have hch := choose_mul_invFac (K := K) (m + 1) j (by omega)
      calc invFac j * kurkovR a (j + 1) k * (invFac (m + 1 - j) * kurkovR a (m + 1 - j) 1)
          = (invFac j * invFac (m + 1 - j)) * kurkovR a (j + 1) k * kurkovR a (m + 1 - j) 1 := by ring
        _ = ((Nat.choose (m + 1) j : K) * invFac (m + 1)) * kurkovR a (j + 1) k * kurkovR a (m + 1 - j) 1 := by
            rw [← hch]
        _ = invFac (m + 1) * ((Nat.choose (m + 1) j : K) * kurkovR a (j + 1) k * kurkovR a (m + 1 - j) 1) := by ring
    rw [hrest, kurkovR,
      Fin.sum_univ_eq_sum_range (fun j => (Nat.choose (m + 1) j : K) * kurkovR a (j + 1) k * kurkovR a (m + 1 - j) 1)]
    ring

-- Part 2: Composed series G_k(x) = ∑_{n≥1} (∑_{j=1}^n S(n, j) R(j, k)) x^n / n!
-- Notice [x^n] G_k(x) = ∑_{j=1}^n (invFac j * R(j, k)) * [x^n] A(x)^j!
-- So G_k'(x) = (∑_{j=1}^n (invFac (j-1) * R(j, k)) * A(x)^(j-1)) * A'(x)!

private lemma coeff_A_pow_eq_zero_of_lt (a : ℕ → K) (n k : ℕ) (h : n < k) :
    PowerSeries.coeff n ((A_series a) ^ k) = 0 := by
  rw [A_eq_X_mul_U, mul_pow, PowerSeries.coeff_X_pow_mul']
  simp [show ¬(k ≤ n) by omega]

private noncomputable def G_series (a : ℕ → K) (k : ℕ) : PowerSeries K :=
  PowerSeries.mk fun n =>
    ∑ j ∈ Finset.range n, invFac (j + 1) * kurkovR a (j + 1) k * PowerSeries.coeff n ((A_series a) ^ (j + 1))

private lemma G_series_coeff_eq (a : ℕ → K) (k n : ℕ) :
    PowerSeries.coeff n (G_series a k) =
      invFac n * ∑ j ∈ Finset.range n, bellS a n (j + 1) * kurkovR a (j + 1) k := by
  simp only [G_series, PowerSeries.coeff_mk, bellS, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  calc invFac (j + 1) * kurkovR a (j + 1) k * PowerSeries.coeff n (A_series a ^ (j + 1))
      = 1 * (invFac (j + 1) * kurkovR a (j + 1) k * PowerSeries.coeff n (A_series a ^ (j + 1))) := (one_mul _).symm
    _ = ((Nat.factorial n : K) * invFac n) *
          (invFac (j + 1) * kurkovR a (j + 1) k * PowerSeries.coeff n (A_series a ^ (j + 1))) := by
        rw [invFac_mul_fac]
    _ = invFac n * ((Nat.factorial n : K) * invFac (j + 1) *
          PowerSeries.coeff n (A_series a ^ (j + 1)) * kurkovR a (j + 1) k) := by ring

-- Finite-truncation composition: for any P, Q with P(0) = 0, up to degree N:
-- (∑_{j=0}^N c_j A^j) matches G_k up to degree N!
private noncomputable def truncComp (a : ℕ → K) (F : PowerSeries K) (N : ℕ) : PowerSeries K :=
  ∑ j ∈ Finset.range (N + 1), PowerSeries.C (PowerSeries.coeff j F) * (A_series a) ^ j

private lemma coeff_G_eq_truncComp (a : ℕ → K) (k N n : ℕ) (hn : n ≤ N) :
    PowerSeries.coeff n (G_series a k) = PowerSeries.coeff n (truncComp a (F_series a k) N) := by
  unfold truncComp
  rw [map_sum]
  simp only [PowerSeries.coeff_C_mul, F_series, PowerSeries.coeff_mk]
  rw [Finset.sum_range_succ']
  simp only [↓reduceIte, zero_mul, add_zero]
  rw [G_series, PowerSeries.coeff_mk]
  have hsplit : Finset.range N = Finset.range n ∪ Finset.Ico n N := by
    ext j; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hsplit, Finset.sum_union]
  · have hzero : ∑ j ∈ Finset.Ico n N,
        (if j + 1 = 0 then (0 : K) else invFac (j + 1) * kurkovR a (j + 1) k) *
          PowerSeries.coeff n (A_series a ^ (j + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjn : n ≤ j := (Finset.mem_Ico.mp hj).1
      rw [coeff_A_pow_eq_zero_of_lt a n (j + 1) (by omega), mul_zero]
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intro j _
    simp
  · rw [Finset.disjoint_left]; intro j h1 h2
    simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega

private lemma coeff_derivative_truncComp (a : ℕ → K) (F : PowerSeries K) (N n : ℕ) (hn : n < N) :
    PowerSeries.coeff n (PowerSeries.derivative K (truncComp a F N)) =
      PowerSeries.coeff n (truncComp a (PowerSeries.derivative K F) N * PowerSeries.derivative K (A_series a)) := by
  -- derivative (∑_{j=0}^N c_j A^j) = (∑_{j=0}^{N-1} (j+1) c_{j+1} A^j) * A'
  have hderiv : PowerSeries.derivative K (truncComp a F N) =
      (∑ j ∈ Finset.range N,
        PowerSeries.C (PowerSeries.coeff j (PowerSeries.derivative K F)) * (A_series a) ^ j) *
      PowerSeries.derivative K (A_series a) := by
    unfold truncComp
    rw [map_sum, Finset.sum_range_succ', pow_zero, mul_one, PowerSeries.derivative_C, add_zero,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Derivation.leibniz, PowerSeries.derivative_C, Derivation.leibniz_pow, PowerSeries.coeff_derivative]
    simp only [smul_eq_mul, mul_zero, add_zero, nsmul_eq_mul]
    have hC : PowerSeries.C (PowerSeries.coeff (j + 1) F * ((j : K) + 1)) =
        PowerSeries.C (PowerSeries.coeff (j + 1) F) * ((j : PowerSeries K) + 1) := by
      rw [map_mul, map_add, map_natCast, map_one]
    rw [hC]
    push_cast; ring
  rw [hderiv]
  -- Difference between range N and range (N+1) is the j = N term, which has A^N, so coeff n = 0 since n < N!
  have hdiff : truncComp a (PowerSeries.derivative K F) N =
      (∑ j ∈ Finset.range N,
        PowerSeries.C (PowerSeries.coeff j (PowerSeries.derivative K F)) * (A_series a) ^ j) +
      PowerSeries.C (PowerSeries.coeff N (PowerSeries.derivative K F)) * (A_series a) ^ N :=
    Finset.sum_range_succ _ N
  rw [hdiff, add_mul, map_add]
  have hzero : PowerSeries.coeff n
      (PowerSeries.C (PowerSeries.coeff N (PowerSeries.derivative K F)) * (A_series a) ^ N *
        PowerSeries.derivative K (A_series a)) = 0 := by
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [Finset.sum_eq_zero]
    · simp
    · intro j hj
      have hjn : j < n + 1 := Finset.mem_range.mp hj
      rw [coeff_A_pow_eq_zero_of_lt a j N (by omega), zero_mul]
  rw [hzero, add_zero]

private lemma coeff_truncComp_mul (a : ℕ → K) (F1 F2 : PowerSeries K) (N n : ℕ) (hn : n ≤ N) :
    PowerSeries.coeff n (truncComp a (F1 * F2) N) =
      PowerSeries.coeff n (truncComp a F1 N * truncComp a F2 N) := by
  unfold truncComp
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [map_sum, map_sum]
  simp_rw [map_sum]
  -- On RHS, coeff n (C c1 * A^i * (C c2 * A^j)) = c1 * c2 * coeff n (A^(i+j))!
  have hrhs : ∀ i j : ℕ,
      PowerSeries.coeff n (PowerSeries.C (PowerSeries.coeff i F1) * (A_series a) ^ i *
        (PowerSeries.C (PowerSeries.coeff j F2) * (A_series a) ^ j)) =
      PowerSeries.coeff i F1 * PowerSeries.coeff j F2 * PowerSeries.coeff n ((A_series a) ^ (i + j)) := by
    intro i j
    rw [show PowerSeries.C (PowerSeries.coeff i F1) * (A_series a) ^ i *
        (PowerSeries.C (PowerSeries.coeff j F2) * (A_series a) ^ j) =
        PowerSeries.C (PowerSeries.coeff i F1 * PowerSeries.coeff j F2) * (A_series a) ^ (i + j) by
      rw [map_mul, pow_add]; ring]
    rw [PowerSeries.coeff_C_mul]
  simp_rw [hrhs]
  -- On LHS, expand coeff k (F1 * F2) = ∑_{i+j=k} coeff i F1 * coeff j F2!
  simp_rw [PowerSeries.coeff_C_mul]
  simp only [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
  -- Restrict LHS to k ∈ range (n + 1) (since coeff n (A^k) = 0 for k > n)
  have hlhs_cut :
      ∑ k ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (k + 1),
        PowerSeries.coeff i F1 * PowerSeries.coeff (k - i) F2 * PowerSeries.coeff n (A_series a ^ k) =
      ∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (k + 1),
        PowerSeries.coeff i F1 * PowerSeries.coeff (k - i) F2 * PowerSeries.coeff n (A_series a ^ k) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k _ hkn
    have hgt : n < k := by simp only [Finset.mem_range] at hkn; omega
    apply Finset.sum_eq_zero
    intro i _
    rw [coeff_A_pow_eq_zero_of_lt a n k hgt, mul_zero]
  -- Restrict RHS to (i, j) with i + j ≤ n
  have hrhs_cut :
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        PowerSeries.coeff i F1 * PowerSeries.coeff j F2 * PowerSeries.coeff n (A_series a ^ (i + j)) =
      ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter (fun p => p.1 + p.2 ≤ n),
        PowerSeries.coeff p.1 F1 * PowerSeries.coeff p.2 F2 * PowerSeries.coeff n (A_series a ^ (p.1 + p.2)) := by
    rw [← Finset.sum_product']
    symm
    apply Finset.sum_subset
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
      exact ⟨by omega, by omega⟩
    · intro p _ hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      have hgt : n < p.1 + p.2 := by omega
      rw [coeff_A_pow_eq_zero_of_lt a n (p.1 + p.2) hgt, mul_zero]
  rw [hlhs_cut, hrhs_cut]
  trans (∑ q ∈ (Finset.range (n + 1)).sigma (fun k => Finset.range (k + 1)),
      PowerSeries.coeff q.2 F1 * PowerSeries.coeff (q.1 - q.2) F2 * PowerSeries.coeff n (A_series a ^ q.1))
  · rw [Finset.sum_sigma]
  symm
  apply Finset.sum_nbij'
    (fun p => (⟨p.1 + p.2, p.1⟩ : Σ _ : ℕ, ℕ))
    (fun q => (q.2, q.1 - q.2))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_sigma, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_range] at hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, by omega⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    ext <;> simp
  · intro q hq
    rcases q with ⟨k, i⟩
    simp only [Finset.mem_sigma, Finset.mem_range] at hq
    simp only [Sigma.mk.inj_iff, heq_eq_eq, and_true]
    omega
  · intro p _
    simp

private lemma G_ode (a : ℕ → K) (k : ℕ) :
    PowerSeries.derivative K (G_series a k) * (1 + G_series a 1) =
      (PowerSeries.C (a k) + G_series a (k + 1)) * PowerSeries.derivative K (A_series a) := by
  apply PowerSeries.ext; intro n
  let N := n + 1
  -- LHS coeff n:
  have hlhs_deriv : ∀ m ≤ n,
      PowerSeries.coeff m (PowerSeries.derivative K (G_series a k)) =
        PowerSeries.coeff m (truncComp a (PowerSeries.derivative K (F_series a k)) N *
          PowerSeries.derivative K (A_series a)) := by
    intro m hm
    rw [PowerSeries.coeff_derivative, coeff_G_eq_truncComp a k N (m + 1) (by omega),
      ← PowerSeries.coeff_derivative, coeff_derivative_truncComp a (F_series a k) N m (by omega)]
  have hlhs_1G : ∀ m ≤ n,
      PowerSeries.coeff m (1 + G_series a 1) =
        PowerSeries.coeff m (truncComp a (1 + F_series a 1) N) := by
    intro m hm
    rw [map_add, coeff_G_eq_truncComp a 1 N m (by omega)]
    unfold truncComp
    simp only [map_add, PowerSeries.coeff_C_mul, map_sum, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_range_succ']
    simp only [PowerSeries.coeff_one, ↓reduceIte, pow_zero, one_mul, Nat.succ_ne_zero, zero_mul,
      Finset.sum_const_zero, zero_add]
  have hlhs : PowerSeries.coeff n (PowerSeries.derivative K (G_series a k) * (1 + G_series a 1)) =
      PowerSeries.coeff n
        (truncComp a (PowerSeries.derivative K (F_series a k) * (1 + F_series a 1)) N *
          PowerSeries.derivative K (A_series a)) := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have h1 : ∑ j ∈ Finset.range (n + 1),
        PowerSeries.coeff j (PowerSeries.derivative K (G_series a k)) *
          PowerSeries.coeff (n - j) (1 + G_series a 1) =
        PowerSeries.coeff n
          ((truncComp a (PowerSeries.derivative K (F_series a k)) N * PowerSeries.derivative K (A_series a)) *
            truncComp a (1 + F_series a 1) N) := by
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [hlhs_deriv j hjn, hlhs_1G (n - j) (by omega)]
    rw [h1, mul_right_comm]
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [coeff_truncComp_mul a _ _ N j (by omega)]
  rw [hlhs, F_ode a k]
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  congr 1
  dsimp only
  rw [map_add, coeff_G_eq_truncComp a (k + 1) N j (by omega)]
  unfold truncComp
  simp only [map_add, PowerSeries.coeff_C_mul, map_sum, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_range_succ']
  simp only [PowerSeries.coeff_C, ↓reduceIte, pow_zero, PowerSeries.coeff_one, Nat.succ_ne_zero,
    zero_mul, Finset.sum_const_zero, zero_add]
  split_ifs <;> simp

-- Part 3: H_k(x) = ∑_{n≥1} a(n + k - 1) x^n / n! satisfies the SAME ODE ⇒ G_k = H_k!

private noncomputable def H_series (a : ℕ → K) (k : ℕ) : PowerSeries K :=
  PowerSeries.mk fun n => if n = 0 then 0 else invFac n * a (n + k - 1)

private lemma H_ode (a : ℕ → K) (ha : a 0 = 1) (k : ℕ) :
    PowerSeries.derivative K (H_series a k) * (1 + H_series a 1) =
      (PowerSeries.C (a k) + H_series a (k + 1)) * PowerSeries.derivative K (A_series a) := by
  have hH1 : 1 + H_series a 1 = PowerSeries.derivative K (A_series a) := by
    rw [derivative_A_series]
    apply PowerSeries.ext; intro n
    cases n with
    | zero => simp [H_series, invFac_zero, ha]
    | succ m => simp [H_series]
  have hHd : PowerSeries.derivative K (H_series a k) = PowerSeries.C (a k) + H_series a (k + 1) := by
    apply PowerSeries.ext; intro n
    rw [PowerSeries.coeff_derivative, H_series, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C]
    cases n with
    | zero =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.cast_zero, zero_add, mul_one, invFac_one,
        H_series, PowerSeries.coeff_mk, add_zero]
      rw [one_mul, Nat.add_sub_cancel_left]
    | succ m =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, H_series, PowerSeries.coeff_mk, zero_add]
      rw [mul_right_comm, invFac_succ_mul, show m + 1 + 1 + k - 1 = m + 1 + (k + 1) - 1 by omega]
  rw [hH1, hHd]

private lemma G_eq_H (a : ℕ → K) (ha : a 0 = 1) :
    ∀ n k : ℕ, PowerSeries.coeff n (G_series a k) = PowerSeries.coeff n (H_series a k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k
    cases n with
    | zero => simp [G_series, H_series]
    | succ m =>
      have hG := congr_arg (PowerSeries.coeff m) (G_ode a k)
      have hH := congr_arg (PowerSeries.coeff m) (H_ode a ha k)
      -- RHS of hG and hH agree because all coeffs of G_{k+1} and H_{k+1} up to m agree by IH!
      have hrhs : PowerSeries.coeff m ((PowerSeries.C (a k) + G_series a (k + 1)) * PowerSeries.derivative K (A_series a)) =
          PowerSeries.coeff m ((PowerSeries.C (a k) + H_series a (k + 1)) * PowerSeries.derivative K (A_series a)) := by
        rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        apply Finset.sum_congr rfl
        intro j hj
        have hjm : j < m + 1 := Finset.mem_range.mp hj
        simp only [map_add, ih j hjm (k + 1)]
      rw [hrhs, ← hH] at hG
      -- On LHS, split j = m (where coeff 0 (1 + G_1) = 1 = coeff 0 (1 + H_1)):
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, Finset.sum_range_succ] at hG
      have htail :
          ∑ j ∈ Finset.range m, PowerSeries.coeff j (PowerSeries.derivative K (G_series a k)) *
              PowerSeries.coeff (m - j) (1 + G_series a 1) =
          ∑ j ∈ Finset.range m, PowerSeries.coeff j (PowerSeries.derivative K (H_series a k)) *
              PowerSeries.coeff (m - j) (1 + H_series a 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjm : j < m := Finset.mem_range.mp hj
        simp only [PowerSeries.coeff_derivative, map_add, ih (j + 1) (by omega) k,
          ih (m - j) (by omega) 1]
      have h0G : PowerSeries.coeff (m - m) (1 + G_series a 1) = 1 := by
        simp [G_series]
      have h0H : PowerSeries.coeff (m - m) (1 + H_series a 1) = 1 := by
        simp [H_series]
      rw [htail, h0G, h0H, mul_one, mul_one] at hG
      have hd_eq : PowerSeries.coeff m (PowerSeries.derivative K (G_series a k)) =
          PowerSeries.coeff m (PowerSeries.derivative K (H_series a k)) := by
        linear_combination hG
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at hd_eq
      -- Cancel (m + 1) using invFac!
      have hcancel := congr_arg (· * (algebraMap ℚ K (((m : ℚ) + 1)⁻¹))) hd_eq
      have hm1 : ((m : K) + 1) * algebraMap ℚ K (((m : ℚ) + 1)⁻¹) = 1 := by
        have h1 : ((m : K) + 1) = algebraMap ℚ K ((m : ℚ) + 1) := by simp
        rw [h1, ← map_mul, mul_inv_cancel₀ (by positivity), map_one]
      rw [mul_assoc, mul_assoc, hm1, mul_one, mul_one] at hcancel
      exact hcancel

-- Part 4: Lagrange residue lemma ⇒ R(n, 1) = E_n^{(-1)}!

private lemma lagrange_residue (a : ℕ → K) (ha : a 0 = 1) (n k : ℕ) (hn : 1 ≤ n) :
    PowerSeries.coeff (n - 1) (PowerSeries.derivative K (A_series a) * (A_series a) ^ k * (xDivA a ha) ^ n) =
      if k = n - 1 then 1 else 0 := by
  by_cases hkn : k = n - 1
  · subst hkn
    simp only [↓reduceIte]
    rw [A_eq_X_mul_U]
    have hpow : (PowerSeries.X * U_series a) ^ (n - 1) * (xDivA a ha) ^ n =
        PowerSeries.X ^ (n - 1) * xDivA a ha := by
      have hn1 : n = (n - 1) + 1 := by omega
      conv_lhs => rw [hn1, pow_succ]
      calc (PowerSeries.X * U_series a) ^ (n - 1) * ((xDivA a ha) ^ (n - 1) * xDivA a ha)
          = PowerSeries.X ^ (n - 1) * ((U_series a * xDivA a ha) ^ (n - 1)) * xDivA a ha := by
            rw [mul_pow, mul_pow]; ring
        _ = PowerSeries.X ^ (n - 1) * xDivA a ha := by rw [U_mul_xDivA, one_pow, mul_one]
    rw [mul_assoc, hpow, mul_left_comm, PowerSeries.coeff_X_pow_mul', if_pos (le_refl _),
      Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff, map_mul, ← A_eq_X_mul_U,
      derivative_A_series, PowerSeries.constantCoeff_mk, invFac_zero, one_mul, ha, one_mul]
    have h1 := congr_arg PowerSeries.constantCoeff (U_mul_xDivA a ha)
    simp only [map_mul, map_one, U_series, PowerSeries.constantCoeff_mk, Nat.zero_add,
      invFac_one, ha, one_mul] at h1
    exact h1
  · simp only [hkn, ↓reduceIte]
    by_cases hgt : n - 1 < k
    · rw [A_eq_X_mul_U, mul_pow, mul_assoc, mul_left_comm, mul_assoc, PowerSeries.coeff_X_pow_mul']
      simp [show ¬(k ≤ n - 1) by omega]
    · -- k < n - 1! Let m = n - 1 - k ≥ 1.
      -- A' * A^k * U^(-n) = X^k * A' * U^(-(m+1))!
      -- And A' * U^(-(m+1)) = U^(-m) - (1/m) * X * (U^(-m))'!
      let m := n - 1 - k
      have hm1 : 1 ≤ m := by omega
      have hn_eq : n = k + m + 1 := by omega
      have hsimp : PowerSeries.derivative K (A_series a) * (A_series a) ^ k * (xDivA a ha) ^ n =
          PowerSeries.X ^ k * (PowerSeries.derivative K (A_series a) * (xDivA a ha) ^ (m + 1)) := by
        rw [A_eq_X_mul_U, mul_pow, hn_eq, pow_add, pow_add, pow_one]
        calc PowerSeries.derivative K (PowerSeries.X * U_series a) *
              (PowerSeries.X ^ k * U_series a ^ k) *
              (xDivA a ha ^ k * xDivA a ha ^ m * xDivA a ha)
            = PowerSeries.X ^ k *
                (PowerSeries.derivative K (PowerSeries.X * U_series a) *
                  ((U_series a * xDivA a ha) ^ k) * (xDivA a ha ^ (m + 1))) := by
              rw [mul_pow, pow_succ]; ring
          _ = PowerSeries.X ^ k *
                (PowerSeries.derivative K (PowerSeries.X * U_series a) * xDivA a ha ^ (m + 1)) := by
              rw [U_mul_xDivA, one_pow, mul_one]
      rw [hsimp, PowerSeries.coeff_X_pow_mul', if_pos (by omega)]
      have hsub : n - 1 - k = m := rfl
      rw [hsub]
      -- Now prove: coeff m (A' * (xDivA)^(m+1)) = 0!
      have hderiv_inv : U_series a * PowerSeries.derivative K (xDivA a ha) =
          -PowerSeries.derivative K (U_series a) * xDivA a ha := by
        have h1 := congr_arg (PowerSeries.derivative K) (U_mul_xDivA a ha)
        rw [Derivation.leibniz, Derivation.map_one_eq_zero] at h1
        simp only [smul_eq_mul] at h1
        linear_combination h1
      have hderiv_pow : PowerSeries.derivative K ((xDivA a ha) ^ m) =
          -((m : K) • (PowerSeries.derivative K (U_series a) * (xDivA a ha) ^ (m + 1))) := by
        rw [Derivation.leibniz_pow]
        have h1 : PowerSeries.derivative K (xDivA a ha) =
            -PowerSeries.derivative K (U_series a) * (xDivA a ha) ^ 2 := by
          calc PowerSeries.derivative K (xDivA a ha)
              = (xDivA a ha * U_series a) * PowerSeries.derivative K (xDivA a ha) := by
                rw [mul_comm (xDivA a ha), U_mul_xDivA, one_mul]
            _ = xDivA a ha * (U_series a * PowerSeries.derivative K (xDivA a ha)) := by ring
            _ = xDivA a ha * (-PowerSeries.derivative K (U_series a) * xDivA a ha) := by rw [hderiv_inv]
            _ = -PowerSeries.derivative K (U_series a) * (xDivA a ha) ^ 2 := by ring
        rw [h1]
        simp only [nsmul_eq_mul, smul_eq_mul]
        have : (xDivA a ha) ^ (m - 1) * (-PowerSeries.derivative K (U_series a) * (xDivA a ha) ^ 2) =
            -(PowerSeries.derivative K (U_series a) * (xDivA a ha) ^ (m + 1)) := by
          have : m - 1 + 2 = m + 1 := by omega
          rw [← this, pow_add]; ring
        rw [this]
        have hsmul : (m : K) • (PowerSeries.derivative K (U_series a) * xDivA a ha ^ (m + 1)) =
            (m : PowerSeries K) * (PowerSeries.derivative K (U_series a) * xDivA a ha ^ (m + 1)) := by
          rw [Algebra.smul_def]; rfl
        rw [hsmul]; ring
      have hA' : PowerSeries.derivative K (A_series a) * (xDivA a ha) ^ (m + 1) =
          (xDivA a ha) ^ m + PowerSeries.X * (PowerSeries.derivative K (U_series a) * (xDivA a ha) ^ (m + 1)) := by
        rw [A_eq_X_mul_U, Derivation.leibniz, PowerSeries.derivative_X]
        simp only [smul_eq_mul, mul_one, add_mul]
        rw [add_comm]
        congr 1
        · rw [pow_succ, ← mul_assoc, mul_comm (U_series a), mul_assoc, U_mul_xDivA, mul_one]
        · ring
      -- Multiply by m: m * A' * xDivA^(m+1) = m * V - X * V' where V = xDivA^m!
      have hmulm : (m : PowerSeries K) * (PowerSeries.derivative K (A_series a) * (xDivA a ha) ^ (m + 1)) =
          (m : PowerSeries K) * (xDivA a ha) ^ m -
            PowerSeries.X * PowerSeries.derivative K ((xDivA a ha) ^ m) := by
        rw [hA', hderiv_pow]
        have hsmul : (m : K) • (PowerSeries.derivative K (U_series a) * xDivA a ha ^ (m + 1)) =
            (m : PowerSeries K) * (PowerSeries.derivative K (U_series a) * xDivA a ha ^ (m + 1)) := by
          rw [Algebra.smul_def]; rfl
        rw [hsmul]
        ring
      have hcm := congr_arg (PowerSeries.coeff m) hmulm
      have hXderiv : PowerSeries.coeff m (PowerSeries.X * PowerSeries.derivative K ((xDivA a ha) ^ m)) =
          (m : K) * PowerSeries.coeff m ((xDivA a ha) ^ m) := by
        obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        conv_lhs => rw [hm']
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, ← hm']
        have : ((m' : K) + 1) = (m : K) := by rw [hm']; push_cast; ring
        rw [this, mul_comm]
      rw [show (m : PowerSeries K) = PowerSeries.C (m : K) by simp,
        PowerSeries.coeff_C_mul, map_sub, PowerSeries.coeff_C_mul, hXderiv, sub_self] at hcm
      have hinv := congr_arg (algebraMap ℚ K ((m : ℚ)⁻¹) * ·) hcm
      rw [mul_zero, ← mul_assoc] at hinv
      have h1 : algebraMap ℚ K ((m : ℚ)⁻¹) * (m : K) = 1 := by
        rw [← map_natCast (algebraMap ℚ K), ← map_mul,
          inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega)), map_one]
      rw [h1, one_mul] at hinv
      exact hinv

private theorem main_proved :
    ∀ (K : Type) [CommRing K] [Algebra ℚ K] (a : ℕ → K) (ha : a 0 = 1),
      (∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
        ∑ j ∈ Finset.range n, bellS a n (j + 1) * kurkovR a (j + 1) k = a (n + k - 1)) ∧
      (∀ n : ℕ, 1 ≤ n → kurkovR a n 1 = invEulerian a ha n) := by
  intro K _ _ a ha
  have hkania : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      ∑ j ∈ Finset.range n, bellS a n (j + 1) * kurkovR a (j + 1) k = a (n + k - 1) := by
    intro n k hn _
    have hEq := G_eq_H a ha n k
    rw [G_series_coeff_eq] at hEq
    simp only [H_series, PowerSeries.coeff_mk, show n ≠ 0 by omega, ↓reduceIte] at hEq
    have hmul := congr_arg ((Nat.factorial n : K) * ·) hEq
    rw [← mul_assoc, ← mul_assoc, invFac_mul_fac, one_mul, one_mul] at hmul
    exact hmul
  refine ⟨hkania, ?_⟩
  intro n hn
  -- From G_1 = H_1: derivative (G_1) = derivative (H_1) = A''(x)!
  have hG1' : PowerSeries.derivative K (G_series a 1) =
      PowerSeries.derivative K (PowerSeries.derivative K (A_series a)) := by
    apply PowerSeries.ext; intro m
    rw [PowerSeries.coeff_derivative, G_eq_H a ha (m + 1) 1, derivative_derivative_A_series,
      H_series, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [mul_right_comm, invFac_succ_mul]
  -- Also coeff m (G_1') = coeff m (truncComp (F_1') N * A') for m ≤ n - 1, where N = n!
  have htrunc : ∀ m ≤ n - 1,
      PowerSeries.coeff m (PowerSeries.derivative K (PowerSeries.derivative K (A_series a))) =
        PowerSeries.coeff m
          (truncComp a (PowerSeries.derivative K (F_series a 1)) n *
            PowerSeries.derivative K (A_series a)) := by
    intro m hm
    rw [← hG1', PowerSeries.coeff_derivative, coeff_G_eq_truncComp a 1 n (m + 1) (by omega),
      ← PowerSeries.coeff_derivative, coeff_derivative_truncComp a (F_series a 1) n m (by omega)]
  unfold invEulerian
  have hmul_eq :
      PowerSeries.coeff (n - 1)
        (PowerSeries.derivative K (PowerSeries.derivative K (A_series a)) * (xDivA a ha) ^ n) =
      PowerSeries.coeff (n - 1)
        (truncComp a (PowerSeries.derivative K (F_series a 1)) n *
          PowerSeries.derivative K (A_series a) * (xDivA a ha) ^ n) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n - 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [htrunc j hjn]
  rw [hmul_eq]
  unfold truncComp
  rw [Finset.sum_mul, Finset.sum_mul, map_sum]
  have hsum :
      ∑ j ∈ Finset.range (n + 1),
        PowerSeries.coeff (n - 1)
          (PowerSeries.C (PowerSeries.coeff j (PowerSeries.derivative K (F_series a 1))) *
            A_series a ^ j * PowerSeries.derivative K (A_series a) * xDivA a ha ^ n) =
      PowerSeries.coeff (n - 1) (PowerSeries.derivative K (F_series a 1)) := by
    have hterm : ∀ j ∈ Finset.range (n + 1),
        PowerSeries.coeff (n - 1)
          (PowerSeries.C (PowerSeries.coeff j (PowerSeries.derivative K (F_series a 1))) *
            A_series a ^ j * PowerSeries.derivative K (A_series a) * xDivA a ha ^ n) =
        if j = n - 1 then PowerSeries.coeff (n - 1) (PowerSeries.derivative K (F_series a 1)) else 0 := by
      intro j _
      rw [show PowerSeries.C (PowerSeries.coeff j (PowerSeries.derivative K (F_series a 1))) *
          A_series a ^ j * PowerSeries.derivative K (A_series a) * xDivA a ha ^ n =
          PowerSeries.C (PowerSeries.coeff j (PowerSeries.derivative K (F_series a 1))) *
            (PowerSeries.derivative K (A_series a) * A_series a ^ j * xDivA a ha ^ n) by ring]
      rw [PowerSeries.coeff_C_mul, lagrange_residue a ha n j hn]
      split_ifs with h
      · subst h; rw [mul_one]
      · rw [mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    simp [show n - 1 < n + 1 by omega]
  rw [hsum, PowerSeries.coeff_derivative, F_series, PowerSeries.coeff_mk]
  have hn1 : n - 1 + 1 = n := by omega
  rw [hn1, if_neg (by omega), mul_right_comm (invFac n),
    show ((n - 1 : ℕ) : K) + 1 = ((n - 1 : ℕ) : K) + 1 from rfl]
  have hinv_n : invFac (K := K) n * (((n - 1 : ℕ) : K) + 1) = invFac (n - 1) := by
    have := invFac_succ_mul (K := K) (n - 1)
    rwa [hn1] at this
  rw [hinv_n, ← mul_assoc, invFac_mul_fac, one_mul]

end Proof

end OMA.P_oeis_a356145

theorem OMA.solution : type_of% @OMA.S_oeis_a356145.main :=
  OMA.P_oeis_a356145.main_proved
