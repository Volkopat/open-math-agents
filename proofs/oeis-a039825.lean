import OMAStatements.S_oeis_a039825

/-!
The support of the Euler-tail series in OEIS A039825.

The finite Euler summation follows from inverse-factor telescoping. The finite
Gaussian binomial theorem gives the centered Gauss product, with the first
coefficients unchanged by further factors. The remaining arithmetic compares
consecutive triangular-number indicators and accounts for the initial cancellation.
-/

section A039825EulerSection

/- Finite Euler summation for the odd-index power series in OEIS A039825. -/

namespace OMA.A039825Euler

open Finset PowerSeries

private abbrev Series := ℚ⟦X⟧

private noncomputable def evenProduct (n : ℕ) : Series :=
  ∏ j ∈ range n, (1 - X ^ (2 * (j + 1)))

private noncomputable def oddProduct (n : ℕ) : Series :=
  ∏ j ∈ range n, (1 - X ^ (2 * j + 1))

private theorem const_one_factor {n : ℕ} (hn : 0 < n) :
    constantCoeff (1 - (X : Series) ^ n) = 1 := by
  rw [map_sub, map_one, map_pow, constantCoeff_X, zero_pow hn.ne']
  exact sub_zero _

private theorem const_evenProduct (n : ℕ) : constantCoeff (evenProduct n) = 1 := by
  rw [evenProduct, map_prod]
  apply Finset.prod_eq_one
  intro j _
  exact const_one_factor (by omega)

private theorem const_oddProduct (n : ℕ) : constantCoeff (oddProduct n) = 1 := by
  rw [oddProduct, map_prod]
  apply Finset.prod_eq_one
  intro j _
  exact const_one_factor (by omega)

private theorem inverse_step (n : ℕ) :
    (evenProduct n)⁻¹ = (1 - X ^ (2 * (n + 1))) * (evenProduct (n + 1))⁻¹ := by
  have hn : constantCoeff (evenProduct n) ≠ 0 := by rw [const_evenProduct]; norm_num
  have hn' : constantCoeff (evenProduct (n + 1)) ≠ 0 := by
    rw [const_evenProduct]
    norm_num
  have hne : evenProduct n ≠ 0 := fun h => hn (by rw [h, map_zero])
  apply mul_left_cancel₀ hne
  rw [PowerSeries.mul_inv_cancel _ hn, ← mul_assoc,
    show evenProduct n * (1 - X ^ (2 * (n + 1))) = evenProduct (n + 1) by
      rw [evenProduct, evenProduct, Finset.prod_range_succ],
    PowerSeries.mul_inv_cancel _ hn']

private noncomputable def finiteSum (a L : ℕ) : Series :=
  ∑ r ∈ range (L + 1), X ^ (a * r) * (evenProduct r)⁻¹

private theorem finiteSum_succ (a L : ℕ) :
    finiteSum a (L + 1) = finiteSum a L + X ^ (a * (L + 1)) * (evenProduct (L + 1))⁻¹ := by
  simp only [finiteSum, Finset.sum_range_succ]

/-- Euler's recurrence with the exact final term from the truncation. -/
private theorem finite_euler_step (a L : ℕ) :
    (1 - X ^ a) * finiteSum a L =
      finiteSum (a + 2) L - X ^ (a * (L + 1)) * (evenProduct L)⁻¹ := by
  induction L with
  | zero => simp [finiteSum, evenProduct]
  | succ L ih =>
    rw [finiteSum_succ a L, finiteSum_succ (a + 2) L, mul_add, ih, inverse_step L]
    rw [show (a + 2) * (L + 1) = a * (L + 1) + 2 * (L + 1) by ring,
      show a * (L + 1 + 1) = a * (L + 1) + a by ring, pow_add, pow_add]
    ring

private theorem power_dvd_term {d e : ℕ} (hle : d ≤ e) (f : Series) :
    (X : Series) ^ d ∣ X ^ e * f :=
  dvd_mul_of_dvd_left (pow_dvd_pow X hle) _

private theorem finite_euler_step_dvd {a L : ℕ} (ha : 0 < a) :
    (X : Series) ^ (L + 1) ∣ (1 - X ^ a) * finiteSum a L - finiteSum (a + 2) L := by
  rw [finite_euler_step, sub_right_comm, sub_self, zero_sub, dvd_neg]
  exact power_dvd_term (by simpa using Nat.mul_le_mul_right (L + 1) ha) _

private theorem oddProduct_times_finiteSum (k L : ℕ) :
    (X : Series) ^ (L + 1) ∣ oddProduct k * finiteSum 1 L - finiteSum (2 * k + 1) L := by
  induction k with
  | zero => simp [oddProduct]
  | succ k ih =>
    let a := 2 * k + 1
    have hsa : 2 * (k + 1) + 1 = a + 2 := by dsimp [a]; omega
    have hsucc : oddProduct (k + 1) = oddProduct k * (1 - X ^ a) := by
      simp only [oddProduct, Finset.prod_range_succ, a]
    rw [hsucc, hsa]
    have he : oddProduct k * (1 - X ^ a) * finiteSum 1 L - finiteSum (a + 2) L =
        (1 - X ^ a) * (oddProduct k * finiteSum 1 L - finiteSum a L) +
          ((1 - X ^ a) * finiteSum a L - finiteSum (a + 2) L) := by ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_right ih _) (finite_euler_step_dvd (by dsimp [a]; omega))

private theorem finiteSum_sub_one_dvd {a L : ℕ} (ha : L + 1 ≤ a) :
    (X : Series) ^ (L + 1) ∣ finiteSum a L - 1 := by
  rw [finiteSum, Finset.sum_range_succ']
  simp only [Nat.mul_zero, pow_zero, evenProduct, range_zero, prod_empty, inv_one,
    one_mul, add_sub_cancel_right]
  apply Finset.dvd_sum
  intro r _
  exact power_dvd_term (ha.trans (by
    simpa using Nat.mul_le_mul_left a (show 1 ≤ r + 1 by omega))) _

private theorem finiteSum_eq_inv_mod {k L : ℕ} (hk : L + 1 ≤ 2 * k + 1) :
    (X : Series) ^ (L + 1) ∣ finiteSum 1 L - (oddProduct k)⁻¹ := by
  have hprod := dvd_add (oddProduct_times_finiteSum k L) (finiteSum_sub_one_dvd hk)
  have hrew : (oddProduct k * finiteSum 1 L - finiteSum (2 * k + 1) L) +
      (finiteSum (2 * k + 1) L - 1) = oddProduct k * finiteSum 1 L - 1 := by ring
  rw [hrew] at hprod
  have hne : constantCoeff (oddProduct k) ≠ 0 := by rw [const_oddProduct]; norm_num
  have he : finiteSum 1 L - (oddProduct k)⁻¹ =
      (oddProduct k)⁻¹ * (oddProduct k * finiteSum 1 L - 1) := by
    rw [mul_sub, ← mul_assoc, PowerSeries.inv_mul_cancel _ hne, one_mul, mul_one]
  rw [he]
  exact dvd_mul_of_dvd_right hprod _

private theorem finiteSum_three_eq_product_mod {k L : ℕ} (hk : L + 1 ≤ 2*k + 1) :
    (X : Series) ^ (L + 1) ∣ (1 - X) * (oddProduct k)⁻¹ - finiteSum 3 L := by
  have hinv := finiteSum_eq_inv_mod hk
  have hstep := finite_euler_step_dvd (a := 1) (L := L) (by decide)
  simp only [pow_one] at hstep
  have hs : (1 - X) * (oddProduct k)⁻¹ - finiteSum 3 L =
      ((1 - X) * finiteSum 1 L - finiteSum 3 L) -
        (1 - X) * (finiteSum 1 L - (oddProduct k)⁻¹) := by ring
  rw [hs]
  exact dvd_sub hstep (dvd_mul_of_dvd_right hinv _)

private noncomputable def tailProduct (r N : ℕ) : Series :=
  ∏ k ∈ Icc (r + 1) N, (1 - X ^ k)

/-- Cancelling the common initial factors leaves the expanded tail product. -/
private theorem evenProduct_mul_inv {r N : ℕ} (h : r ≤ N) :
    evenProduct N * (evenProduct r)⁻¹ = expand 2 (by decide) (tailProduct r N) := by
  have hne : constantCoeff (evenProduct r) ≠ 0 := by rw [const_evenProduct]; norm_num
  have hprod : evenProduct N =
      evenProduct r * ∏ j ∈ Ico r N, (1 - (X : Series) ^ (2 * (j + 1))) := by
    simpa only [evenProduct] using
      (Finset.prod_range_mul_prod_Ico (fun j => 1 - (X : Series) ^ (2 * (j + 1))) h).symm
  rw [hprod, mul_right_comm, PowerSeries.mul_inv_cancel _ hne, one_mul]
  simp only [tailProduct, map_prod, map_sub, map_one, map_pow, expand_X, ← pow_mul]
  refine Finset.prod_bij (fun j _ => j + 1) ?_ ?_ ?_ ?_
  · intro j hj
    have hb := Finset.mem_Ico.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro j _ j' _ hjj'
    omega
  · intro k hk
    have hb := Finset.mem_Icc.mp hk
    exact ⟨k - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro j _
    rfl

private noncomputable def asSeries : Polynomial ℤ →ₐ[ℤ] Series :=
  Polynomial.coeToPowerSeries.algHom ℚ

private theorem asSeries_X : asSeries Polynomial.X = (X : Series) := by
  simp [asSeries, Polynomial.coeToPowerSeries.algHom_apply]

private theorem coeff_asSeries (f : Polynomial ℤ) (i : ℕ) :
    coeff i (asSeries f) = (f.coeff i : ℚ) := by
  simp [asSeries, Polynomial.coeToPowerSeries.algHom_apply, PowerSeries.coeff_map]

private noncomputable def originalTerm (m n : ℕ) : ℚ :=
  coeff (m + 2) (X ^ (3*n) * tailProduct (2*n - 1) (m + 2))

private noncomputable def eulerTerm (m r : ℕ) : ℚ :=
  coeff (2*m + 1) (evenProduct (m+2) * (X ^ (3*r) * (evenProduct r)⁻¹))

private theorem coeffAt_eq_sum (m : ℕ) :
    (OMA.S_oeis_a039825.coeffAt (m+2) : ℚ) = ∑ n ∈ Icc 1 (m+2), originalTerm m n := by
  unfold OMA.S_oeis_a039825.coeffAt
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos := (Finset.mem_Icc.mp hn).1
  rw [← coeff_asSeries]
  simp only [map_mul, map_pow, map_prod, map_sub, map_one, asSeries_X, originalTerm, tailProduct]
  rw [show 2 * n - 1 + 1 = 2 * n by omega]

private theorem eulerTerm_expand {m r : ℕ} (h : r ≤ m+2) :
    eulerTerm m r =
      coeff (2*m + 1) (X ^ (3*r) * expand 2 (by decide) (tailProduct r (m+2))) := by
  rw [eulerTerm, mul_left_comm, evenProduct_mul_inv h]

private theorem originalTerm_eq (m n : ℕ) (hn : 1 ≤ n) (hsmall : 3*n ≤ m+2) :
    originalTerm m n = eulerTerm m (2*n - 1) := by
  rw [eulerTerm_expand (by omega), coeff_X_pow_mul', if_pos (by omega),
    show 2*m+1-3*(2*n-1) = 2*(m+2-3*n) by omega, coeff_expand_mul,
    originalTerm, coeff_X_pow_mul', if_pos hsmall]

private theorem eulerTerm_eq_zero {m r : ℕ} (h : ¬ (r % 2 = 1 ∧ 3*r ≤ 2*m+1)) :
    eulerTerm m r = 0 := by
  by_cases hr : 3*r ≤ 2*m+1
  · have he : r % 2 = 0 := by omega
    rw [eulerTerm_expand (by omega), coeff_X_pow_mul', if_pos hr]
    exact coeff_expand_of_not_dvd 2 (by decide) _ (by omega)
  · rw [eulerTerm, mul_left_comm, coeff_X_pow_mul', if_neg hr]

private theorem euler_sum_eq_original (m : ℕ) :
    (∑ r ∈ range (2*m+2), eulerTerm m r) =
      ∑ n ∈ Icc 1 (m+2), originalTerm m n := by
  let R := (range (2*m+2)).filter (fun r => r % 2 = 1 ∧ 3*r ≤ 2*m+1)
  let N := (Icc 1 (m+2)).filter (fun n => 3*n ≤ m+2)
  have hR : (∑ r ∈ R, eulerTerm m r) = ∑ r ∈ range (2*m+2), eulerTerm m r := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro r hr hr'
    exact eulerTerm_eq_zero (fun h => hr' (Finset.mem_filter.mpr ⟨hr,h⟩))
  have hN : (∑ n ∈ N, originalTerm m n) = ∑ n ∈ Icc 1 (m+2), originalTerm m n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hn'
    have hbad : ¬ 3*n ≤ m+2 := fun h => hn' (Finset.mem_filter.mpr ⟨hn,h⟩)
    rw [originalTerm, coeff_X_pow_mul', if_neg hbad]
  rw [← hR, ← hN]
  symm
  refine Finset.sum_bij (fun n _ => 2*n - 1) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hb, hsmall⟩ := Finset.mem_filter.mp hn
    have hnPos := (Finset.mem_Icc.mp hb).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, by omega⟩
  · intro n hn n' hn' he
    have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have h2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn').1).1
    omega
  · intro r hr
    obtain ⟨_, hrOdd,hrSmall⟩ := Finset.mem_filter.mp hr
    exact ⟨(r+1)/2, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩,
      by omega⟩
  · intro n hn
    obtain ⟨hb, hsmall⟩ := Finset.mem_filter.mp hn
    exact originalTerm_eq m n (Finset.mem_Icc.mp hb).1 hsmall

/-- The finite coefficient equality between the original series and the Euler product. -/
theorem coeffAt_eq_euler_product (m : ℕ) :
    let P : Series := ∏ j ∈ range (m + 2), (1 - X ^ (2 * (j + 1)))
    let Q : Series := ∏ j ∈ range (m + 2), (1 - X ^ (2 * j + 1))
    (OMA.S_oeis_a039825.coeffAt (m+2) : ℚ) = coeff (2*m+1) ((1 - X) * (P * Q⁻¹)) := by
  change (OMA.S_oeis_a039825.coeffAt (m+2) : ℚ) =
    coeff (2*m+1) ((1 - X) * (evenProduct (m+2) * (oddProduct (m+2))⁻¹))
  have h := dvd_mul_of_dvd_right
    (finiteSum_three_eq_product_mod (k := m+2) (L := 2*m+1) (by omega))
    (evenProduct (m+2))
  rw [mul_sub, mul_left_comm] at h
  have hc := PowerSeries.X_pow_dvd_iff.mp h (2*m+1) (Nat.lt_succ_self _)
  rw [map_sub, sub_eq_zero] at hc
  rw [hc, coeffAt_eq_sum, ← euler_sum_eq_original]
  simp only [finiteSum, Finset.mul_sum, map_sum, eulerTerm, Nat.add_assoc]

end OMA.A039825Euler

end A039825EulerSection

section A039825GaussExponentSection

/- Centered exponents of the finite Gaussian product. -/

namespace OMA.A039825GaussExponent

/-- The triangular index attached to either side of the center. -/
def index (n k : ℕ) : ℕ := if k ≤ n then 2 * (n - k) else 2 * (k - n) - 1

def triangular (j : ℕ) : ℕ := j * (j + 1) / 2

theorem triangular_strictMono : StrictMono triangular := by
  apply strictMono_nat_of_lt_succ
  intro j
  unfold triangular
  have h : (j + 1) * (j + 1 + 1) = j * (j + 1) + 2 * (j + 1) := by ring
  rw [h]
  omega

theorem le_triangular (j : ℕ) : j ≤ triangular j := by
  cases j with
  | zero => simp [triangular]
  | succ j =>
    apply (Nat.le_div_iff_mul_le (show 0 < (2 : ℕ) by decide)).mpr
    exact Nat.mul_le_mul_left _ (by omega)

theorem index_injective (n : ℕ) : Function.Injective (index n) := by
  intro k l heq
  unfold index at heq
  split at heq <;> split at heq <;> omega

theorem index_surj_small {n j : ℕ} (hj : j ≤ n) : ∃ k ≤ 2 * n, index n k = j := by
  by_cases he : j % 2 = 0
  · refine ⟨n - j / 2, by omega, ?_⟩
    rw [index, if_pos (by omega)]
    omega
  · refine ⟨n + (j + 1) / 2, by omega, ?_⟩
    rw [index, if_neg (by omega)]
    omega

/-- Only central Gaussian coefficients can affect a given low degree. -/
theorem central_of_small {d n k : ℕ} (hn : 2 * d ≤ n)
    (hsmall : triangular (index n k) ≤ d) : d ≤ k ∧ d ≤ 2 * n - k := by
  have hIndex := (le_triangular (index n k)).trans hsmall
  unfold index at hIndex
  split at hIndex <;> omega

private theorem twice_triangle (j : ℕ) :
    2 * ((j * (j + 1) / 2 : ℕ) : ℤ) = (j : ℤ) * ((j : ℤ) + 1) := by
  have hEven := Nat.even_iff.mp (Nat.even_mul_succ_self j)
  exact_mod_cast (show 2 * (j * (j + 1) / 2) = j * (j + 1) by omega)

private theorem twice_staircase (j : ℕ) :
    2 * ((j * (j - 1) / 2 : ℕ) : ℤ) = (j : ℤ) * ((j : ℤ) - 1) := by
  cases j with
  | zero => norm_num
  | succ j =>
    rw [Nat.succ_sub_one, mul_comm (j + 1) j]
    push_cast
    rw [add_sub_cancel_right]
    simpa [mul_comm] using twice_triangle j

/-- The Gaussian exponent becomes triangular after removing the central monomial. -/
theorem centered_exponent (n k : ℕ) (hn : 0 < n) (hk : k ≤ 2 * n) :
    let l := if k ≤ n then 2 * (n - k) else 2 * (k - n) - 1
    (4 * n - 1) * (2 * n - k) + 4 * (k * (k - 1) / 2) =
      (4 * n - 1) * n + 4 * (n * (n - 1) / 2) + l * (l + 1) / 2 := by
  dsimp only
  have hn1 : 1 ≤ 4 * n := by omega
  apply (Nat.cast_injective (R := ℤ))
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hk, Nat.cast_sub hn1, Nat.cast_ofNat,
    Nat.cast_one]
  apply (mul_right_cancel₀ (show (2 : ℤ) ≠ 0 by decide))
  by_cases hkn : k ≤ n
  · simp only [if_pos hkn]
    have ht := twice_triangle (2 * (n - k))
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hkn] at ht
    linear_combination 4 * twice_staircase k - 4 * twice_staircase n - ht
  · simp only [if_neg hkn]
    have hnk : n ≤ k := by omega
    have hdiff : 1 ≤ 2 * (k - n) := by omega
    have ht := twice_triangle (2 * (k - n) - 1)
    simp only [Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.cast_sub hnk,
      Nat.cast_sub hdiff] at ht
    linear_combination 4 * twice_staircase k - 4 * twice_staircase n - ht

end OMA.A039825GaussExponent

end A039825GaussExponentSection

section OeisA039825GaussFiniteSection

/- Finite Gaussian binomial identities for the triangular-number product. -/

namespace OeisA039825GaussFinite

open Finset PowerSeries
open scoped BigOperators

def poch {R : Type*} [CommRing R] (q : R) (n : ℕ) : R :=
  ∏ i ∈ range n, (1 - q^(i+1))

theorem poch_succ {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    poch q (n+1) = poch q n * (1-q^(n+1)) := by
  exact prod_range_succ _ n

def gaussian {R : Type*} [CommSemiring R] (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, _+1 => 0
  | _+1, 0 => 1
  | n+1, k+1 => gaussian q n (k+1) + q^(n-k) * gaussian q n k

@[simp] theorem gaussian_zero_right {R : Type*} [CommSemiring R] (q : R) (n : ℕ) :
    gaussian q n 0 = 1 := by cases n <;> rfl

theorem gaussian_eq_zero {R : Type*} [CommSemiring R] (q : R) {n k : ℕ} (h : n < k) :
    gaussian q n k = 0 := by
  induction n generalizing k with
  | zero => cases k <;> simp_all [gaussian]
  | succ n ih =>
    obtain ⟨k,rfl⟩ : ∃ j, k = j+1 := ⟨k-1, by omega⟩
    rw [gaussian, ih (by omega : n < k+1), ih (by omega : n < k), mul_zero, add_zero]

@[simp] theorem gaussian_diag {R : Type*} [CommSemiring R] (q : R) (n : ℕ) :
    gaussian q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [gaussian, gaussian_eq_zero q (by omega : n < n+1), Nat.sub_self, pow_zero, ih]
    simp

/-- The polynomial Gaussian binomial agrees with its product formula after
multiplication by the denominator. -/
theorem gaussian_mul_poch {R : Type*} [CommRing R] (q : R) {n k : ℕ} (h : k ≤ n) :
    gaussian q n k * poch q k * poch q (n-k) = poch q n := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst k
    simp [poch]
  | succ n ih =>
    by_cases h₀ : k = 0
    · simp [h₀, poch]
    by_cases hdiag : k = n+1
    · simp [hdiag, poch]
    obtain ⟨j,rfl⟩ : ∃ j, k = j+1 := ⟨k-1, by omega⟩
    have hj : j+1 ≤ n := by omega
    have hj' : j ≤ n := by omega
    have hd : n-j = (n-(j+1))+1 := by omega
    have hh : n+1-(j+1) = n-j := by omega
    have hpow : n+1 = (n-j)+(j+1) := by omega
    rw [gaussian, hh, poch_succ q n, add_mul, add_mul]
    have h₁ : gaussian q n (j+1) * poch q (j+1) * poch q (n-j)
        = poch q n * (1-q^(n-j)) := by
      conv_lhs => rw [hd, poch_succ q (n-(j+1))]
      rw [← mul_assoc, ih hj, ← hd]
    have h₂ : q^(n-j) * gaussian q n j * poch q (j+1) * poch q (n-j)
        = q^(n-j) * poch q n * (1-q^(j+1)) := by
      rw [poch_succ q j]
      calc
        _ = q^(n-j) * (gaussian q n j * poch q j * poch q (n-j)) * (1-q^(j+1)) := by ring
        _ = _ := by rw [ih hj']
    rw [h₁,h₂]
    conv_rhs => rw [hpow, pow_add]
    ring

def staircase (k : ℕ) : ℕ := k*(k-1)/2

theorem staircase_succ (k : ℕ) : staircase (k+1) = staircase k + k := by
  have h : (k+1)*k = k*(k-1)+2*k := by
    cases k with
    | zero => simp
    | succ k => simp only [Nat.add_sub_cancel]; ring
  unfold staircase
  rw [show k+1-1 = k by omega, h]
  omega

/-- The homogeneous finite q-binomial theorem, with natural exponents on
both indeterminates. It specializes to the centered Jacobi product without
requiring Laurent series. -/
theorem finite_q_binomial {R : Type*} [CommSemiring R] (q a b : R) (n : ℕ) :
    ∏ i ∈ range n, (a+b*q^i) =
      ∑ k ∈ range (n+1), a^(n-k) * b^k * q^(staircase k) * gaussian q n k := by
  induction n with
  | zero => simp [staircase]
  | succ n ih =>
    rw [prod_range_succ, ih, mul_add, sum_mul, sum_mul]
    let A (k : ℕ) := a^((n+1)-k) * b^k * q^(staircase k) * gaussian q n k
    let B (k : ℕ) := a^((n+1)-(k+1)) * b^(k+1) * q^(staircase (k+1)) *
      (q^(n-k)*gaussian q n k)
    have hA :
        (∑ k ∈ range (n+1), (a^(n-k) * b^k * q^(staircase k) * gaussian q n k)*a)
          = ∑ k ∈ range (n+1), A k := by
      apply sum_congr rfl
      intro k hk
      have h := mem_range.mp hk
      dsimp only [A]
      rw [show n+1-k = (n-k)+1 by omega, pow_succ]
      ac_rfl
    have hB :
        (∑ k ∈ range (n+1), (a^(n-k) * b^k * q^(staircase k) * gaussian q n k)*(b*q^n))
          = ∑ k ∈ range (n+1), B k := by
      apply sum_congr rfl
      intro k hk
      have h := mem_range.mp hk
      dsimp only [B]
      rw [show n+1-(k+1) = n-k by omega, pow_succ b, staircase_succ, pow_add]
      have hq : q^n = q^k*q^(n-k) := by rw [← pow_add, show k+(n-k)=n by omega]
      rw [hq]
      ac_rfl
    rw [hA,hB]
    have hR (k : ℕ) :
        a^(n+1-(k+1))*b^(k+1)*q^staircase (k+1)*gaussian q (n+1) (k+1)
          = A (k+1)+B k := by
      dsimp only [A,B]
      rw [gaussian, mul_add]
    let F (k : ℕ) := a^(n+1-k)*b^k*q^staircase k*gaussian q (n+1) k
    change _ = ∑ k ∈ range ((n+1)+1), F k
    rw [sum_range_succ' F (n+1)]
    have hs : (∑ k ∈ range (n+1), F (k+1)) = ∑ k ∈ range (n+1), (A (k+1) + B k) :=
      sum_congr rfl (fun k _ => hR k)
    rw [hs, sum_add_distrib]
    have hA0 : A 0 = a^(n+1) := by simp [A, staircase]
    have hAz : A (n+1) = 0 := by simp [A, gaussian_eq_zero q (by omega : n < n+1)]
    have he : (∑ k ∈ range (n+1), A (k+1)) + A 0 = ∑ k ∈ range (n+1), A k := by
      rw [← sum_range_succ' A (n+1), sum_range_succ A (n+1), hAz, add_zero]
    simp only [F, Nat.sub_zero, pow_zero, mul_one, gaussian_zero_right, staircase,
      zero_mul, Nat.zero_div]
    rw [← hA0, ← he]
    ac_rfl

abbrev Series := ℚ⟦X⟧

/-- Agreement of two series in all coefficients through degree d. -/
def Agree (d : ℕ) (F G : Series) : Prop :=
  ∀ j ≤ d, coeff j F = coeff j G

theorem agree_refl (d : ℕ) (F : Series) : Agree d F F := fun _ _ => rfl

theorem Agree.symm {d : ℕ} {F G : Series} (h : Agree d F G) : Agree d G F :=
  fun j hj => (h j hj).symm

theorem Agree.trans {d : ℕ} {F G H : Series} (h : Agree d F G) (h' : Agree d G H) :
    Agree d F H := fun j hj => (h j hj).trans (h' j hj)

theorem Agree.mul {d : ℕ} {F G U V : Series} (h : Agree d F G) (h' : Agree d U V) :
    Agree d (F*U) (G*V) := by
  intro j hj
  rw [coeff_mul, coeff_mul]
  apply sum_congr rfl
  intro x hx
  have hx := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rw [h _ (by omega), h' _ (by omega)]

theorem Agree.inv {d : ℕ} {F G : Series} (h : Agree d F G)
    (hF : constantCoeff F ≠ 0) (hG : constantCoeff G ≠ 0) : Agree d F⁻¹ G⁻¹ := by
  have h' := h.symm.mul (agree_refl d (F⁻¹*G⁻¹))
  have hL : G*(F⁻¹*G⁻¹) = F⁻¹ := by
    rw [mul_comm F⁻¹ G⁻¹, ← mul_assoc, mul_comm G G⁻¹, PowerSeries.inv_mul_cancel G hG, one_mul]
  have hR : F*(F⁻¹*G⁻¹) = G⁻¹ := by
    rw [← mul_assoc, mul_comm F F⁻¹, PowerSeries.inv_mul_cancel F hF, one_mul]
  simpa only [hL,hR] using h'

noncomputable def factorProd (exponent : ℕ → ℕ) (n : ℕ) : Series :=
  ∏ i ∈ range n, (1-X^(exponent i))

theorem constantCoeff_factorProd (exponent : ℕ → ℕ) (n : ℕ)
    (h : ∀ i < n, 0 < exponent i) : constantCoeff (factorProd exponent n) = 1 := by
  rw [factorProd, map_prod]
  apply prod_eq_one
  intro i hi
  rw [map_sub, map_one, map_pow, constantCoeff_X,
    zero_pow (Nat.ne_of_gt (h i (mem_range.mp hi))), sub_zero]

theorem agree_factorProd {d m n : ℕ} (exponent : ℕ → ℕ) (hm : m ≤ n)
    (hd : ∀ i, m ≤ i → i < n → d < exponent i) :
    Agree d (factorProd exponent n) (factorProd exponent m) := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst m
    exact agree_refl _ _
  | succ n ih =>
    by_cases he : m = n+1
    · subst m
      exact agree_refl _ _
    have hmn : m ≤ n := by omega
    have hInd := ih hmn (fun i hi hi' => hd i hi (by omega))
    intro j hj
    unfold factorProd
    rw [prod_range_succ, coeff_mul_one_sub_of_lt_order j]
    · exact hInd j hj
    · rw [order_X_pow]
      exact_mod_cast (lt_of_le_of_lt hj (hd n hmn (by omega)))

theorem agree_factorProd_of_large {d m n : ℕ} (exponent : ℕ → ℕ)
    (hm : ∀ i, m ≤ i → d < exponent i) (hn : ∀ i, n ≤ i → d < exponent i) :
    Agree d (factorProd exponent m) (factorProd exponent n) := by
  rcases le_total m n with h | h
  · exact (agree_factorProd exponent h (fun i hi _ => hm i hi)).symm
  · exact agree_factorProd exponent h (fun i hi _ => hn i hi)

noncomputable def evenProd (m : ℕ) : Series := factorProd (fun j => 2*(j+1)) m
noncomputable def oddProd (m : ℕ) : Series := factorProd (fun j => 2*j+1) m
noncomputable def quarticProd (m : ℕ) : Series := factorProd (fun j => 4*(j+1)) m

/-- The ratio in the conjecture stabilizes in the stated degree range. -/
theorem agree_even_odd_ratio {d m n : ℕ} (hd : d ≤ 2*m) (hm : m ≤ n) :
    Agree d (evenProd n * (oddProd n)⁻¹) (evenProd m * (oddProd m)⁻¹) := by
  have he : Agree d (evenProd n) (evenProd m) :=
    agree_factorProd _ hm (fun _ hi _ => by omega)
  have ho : Agree d (oddProd n) (oddProd m) :=
    agree_factorProd _ hm (fun _ hi _ => by omega)
  have hc (j : ℕ) : constantCoeff (oddProd j) ≠ 0 := by
    rw [oddProd, constantCoeff_factorProd _ _ (fun _ _ => by omega)]
    exact one_ne_zero
  exact he.mul (ho.inv (hc n) (hc m))

theorem prod_range_alternating {R : Type*} [CommMonoid R] (f : ℕ → R) (n : ℕ) :
    ∏ i ∈ range (2*n), f i = (∏ i ∈ range n, f (2*i)) * ∏ i ∈ range n, f (2*i+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, prod_range_succ f, prod_range_succ f, ih,
      prod_range_succ (fun i => f (2*i)), prod_range_succ (fun i => f (2*i+1))]
    ac_rfl

noncomputable def plusProd (c n : ℕ) : Series :=
  ∏ i ∈ range n, (1 + X^(4*i+c))

noncomputable def centeredProduct (n : ℕ) : Series :=
  quarticProd n * plusProd 1 n * plusProd 3 n

/-- The natural shift is the sum of the smaller exponents in the original
homogeneous binomial product. -/
def centerShift (n : ℕ) : ℕ := (4*n-1)*n + 4*staircase n

private theorem center_product_shift {n : ℕ} (hn : 0 < n) :
    (∏ i ∈ range (2*n), ((X : Series)^(4*n-1)+(X^4)^i)) =
      X^(centerShift n) * (plusProd 1 n * plusProd 3 n) := by
  let f (i : ℕ) : Series := X^(4*n-1)+(X^4)^i
  change (∏ i ∈ range (2*n), f i) = _
  rw [two_mul, prod_range_add]
  have hs₀ :
      (∏ i ∈ range n, f i) =
        (∏ i ∈ range n, (X : Series)^(4*i)) * plusProd 3 n := by
    have hs :
        (∏ i ∈ range n, f i) =
          ∏ i ∈ range n, (X : Series)^(4*i) * (1+X^(4*(n-1-i)+3)) := by
      apply prod_congr rfl
      intro i hi
      have hi := mem_range.mp hi
      have he : 4*n-1 = 4*i+(4*(n-1-i)+3) := by omega
      dsimp only [f]
      rw [← pow_mul, he, pow_add, mul_add, mul_one]
      exact add_comm _ _
    rw [hs, prod_mul_distrib]
    exact congrArg (fun q : Series => (∏ i ∈ range n, (X:Series)^(4*i)) * q)
      (prod_range_reflect (fun i => 1+(X:Series)^(4*i+3)) n)
  have hs₁ :
      (∏ i ∈ range n, f (n+i)) =
        (∏ _i ∈ range n, (X : Series)^(4*n-1)) * plusProd 1 n := by
    unfold plusProd
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    have he : 4*(n+i) = (4*n-1)+(4*i+1) := by omega
    dsimp only [f]
    rw [← pow_mul, he, pow_add, mul_add, mul_one]
  rw [hs₀, hs₁, prod_pow_eq_pow_sum, ← Finset.mul_sum, Finset.sum_range_id, prod_const, card_range,
    ← pow_mul, centerShift, staircase, pow_add]
  ring

/-- The homogeneous finite q-binomial specializes to the centered product
with natural exponents after cancellation of the common power of X. -/
theorem centeredProduct_eq_sum {n : ℕ} (hn : 0 < n) (e : ℕ → ℕ)
    (hE : ∀ k ≤ 2*n, (4*n-1)*(2*n-k)+4*staircase k = centerShift n+e k) :
    centeredProduct n = ∑ k ∈ range (2*n+1),
      (X : Series)^(e k) * (gaussian (X^4) (2*n) k * quarticProd n) := by
  have hbin := finite_q_binomial ((X:Series)^4) ((X:Series)^(4*n-1)) 1 (2*n)
  simp only [one_mul, one_pow, mul_one, ← pow_mul] at hbin
  have hTerms :
      (∑ k ∈ range (2*n+1),
        (X : Series)^((4*n-1)*(2*n-k)) * X^(4*staircase k) * gaussian (X^4) (2*n) k)
        = ∑ k ∈ range (2*n+1), X^(centerShift n) * (X^(e k) * gaussian (X^4) (2*n) k) := by
    apply sum_congr rfl
    intro k hk
    rw [← pow_add, hE k (by have hi := mem_range.mp hk; omega), pow_add, mul_assoc]
  have hshift := center_product_shift hn
  simp only [← pow_mul] at hshift
  rw [hshift, hTerms, ← mul_sum] at hbin
  have he := mul_left_cancel₀ (pow_ne_zero (centerShift n) (X_ne_zero : (X : Series) ≠ 0)) hbin
  rw [centeredProduct, mul_assoc, he, mul_sum]
  apply sum_congr rfl
  intro k _
  ac_rfl

private theorem poch_pow_eq_quartic (n : ℕ) :
    poch ((X : Series)^4) n = quarticProd n := by
  simp only [poch, quarticProd, factorProd, ← pow_mul]

private theorem quartic_constant (n : ℕ) : constantCoeff (quarticProd n) = 1 :=
  constantCoeff_factorProd _ _ (fun _ _ => by omega)

/-- In any degree through all three growing cutoffs, the Gaussian factor
times its quartic product has the same coefficients as 1. -/
theorem agree_gaussian_mul_quartic {d n k : ℕ} (hk : k ≤ 2*n)
    (_hn : d ≤ n) (hk₁ : d ≤ k) (hk₂ : d ≤ 2*n-k) :
    Agree d (gaussian ((X:Series)^4) (2*n) k * quarticProd n) 1 := by
  let g := gaussian ((X:Series)^4) (2*n) k
  let D := quarticProd k * quarticProd (2*n-k)
  have hG := gaussian_mul_poch ((X:Series)^4) hk
  simp only [poch_pow_eq_quartic] at hG
  have hp : (g * quarticProd n) * D = quarticProd (2*n) * quarticProd n := by
    calc
      _ = (g*quarticProd k * quarticProd (2*n-k))*quarticProd n := by dsimp only [D]; ac_rfl
      _ = _ := by rw [show g*quarticProd k * quarticProd (2*n-k) = _ from hG]
  have hD : constantCoeff D ≠ 0 := by simp [D, quartic_constant]
  have hI : D*D⁻¹ = 1 := by rw [mul_comm D D⁻¹, PowerSeries.inv_mul_cancel D hD]
  have h₁ : Agree d (quarticProd (2*n)) (quarticProd k) :=
    agree_factorProd _ hk (fun i hi _ => by omega)
  have h₂ : Agree d (quarticProd n) (quarticProd (2*n-k)) :=
    agree_factorProd_of_large _ (fun i hi => by omega) (fun i hi => by omega)
  have h₀ : Agree d ((quarticProd (2*n) * quarticProd n)*D⁻¹) (D*D⁻¹) :=
    (h₁.mul h₂).mul (agree_refl d D⁻¹)
  rw [← hp, mul_assoc, hI, mul_one] at h₀
  exact h₀

end OeisA039825GaussFinite

end OeisA039825GaussFiniteSection

section A039825GaussRatioSection

/- Finite comparison of the Gauss product and the centered q-binomial product. -/

namespace OeisA039825GaussFinite

open Finset PowerSeries

/-- Doubling the odd exponents recovers all even exponents congruent to
two modulo four. Here the even product is taken through degree 8n. -/
theorem ratio_eq_extended_centeredProduct (n : ℕ) :
    evenProd (2*(2*n)) * (oddProd (2*n))⁻¹ = quarticProd (2*n) * plusProd 1 n * plusProd 3 n := by
  symm
  apply (eq_mul_inv_iff_mul_eq ?_).mpr
  · unfold evenProd oddProd factorProd
    rw [prod_range_alternating _ (2*n)]
    rw [prod_range_alternating (fun j => (1 - (X : Series)^(2*j+1))) n]
    rw [prod_range_alternating (fun j => (1 - (X : Series)^(2*(2*j+1)))) n]
    unfold plusProd quarticProd factorProd
    have h₁ : (∏ i ∈ range n, (1 + (X : Series)^(4*i+1))) *
        (∏ i ∈ range n, (1 - (X : Series)^(2*(2*i)+1))) =
        ∏ i ∈ range n, (1 - (X : Series)^(2*(2*(2*i)+1))) := by
      rw [← prod_mul_distrib]
      apply prod_congr rfl
      intro i _
      rw [show 2*(2*i)+1 = 4*i+1 by omega,
        show 2*(4*i+1) = (4*i+1)+(4*i+1) by omega, pow_add]
      ring
    have h₃ : (∏ i ∈ range n, (1 + (X : Series)^(4*i+3))) *
        (∏ i ∈ range n, (1 - (X : Series)^(2*(2*i+1)+1))) =
        ∏ i ∈ range n, (1 - (X : Series)^(2*(2*(2*i+1)+1))) := by
      rw [← prod_mul_distrib]
      apply prod_congr rfl
      intro i _
      rw [show 2*(2*i+1)+1 = 4*i+3 by omega,
        show 2*(4*i+3) = (4*i+3)+(4*i+3) by omega, pow_add]
      ring
    have he (i : ℕ) : 4*(i+1) = 2*(2*i+1+1) := by omega
    simp only [he]
    rw [← h₁, ← h₃]
    ring
  · rw [oddProd, constantCoeff_factorProd _ _ (fun _ _ => by omega)]
    exact one_ne_zero

/-- At degrees through 4n the finite Jacobi product agrees with the exact
even/odd ratio at index 2n. -/
theorem agree_ratio_centeredProduct {d n : ℕ} (hd : d ≤ 4*n) :
    Agree d (evenProd (2*n) * (oddProd (2*n))⁻¹) (centeredProduct n) := by
  have he : Agree d (evenProd (2*(2*n))) (evenProd (2*n)) :=
    agree_factorProd _ (by omega) (fun _ hi _ => by omega)
  have hq : Agree d (quarticProd (2*n)) (quarticProd n) :=
    agree_factorProd _ (by omega) (fun _ hi _ => by omega)
  have ha := he.mul (agree_refl d (oddProd (2*n))⁻¹)
  rw [ratio_eq_extended_centeredProduct] at ha
  exact ha.symm.trans ((hq.mul (agree_refl d (plusProd 1 n))).mul (agree_refl d (plusProd 3 n)))

end OeisA039825GaussFinite

end A039825GaussRatioSection

section A039825GaussConclusionSection

/- Coefficient extraction from the finite centered form of Gauss's identity. -/

namespace OMA.A039825GaussConclusion

open Finset PowerSeries Classical
open OeisA039825GaussFinite OMA.A039825GaussExponent

private theorem coeff_gaussian_term {i n k : ℕ} (hn : 2*i ≤ n) (hk : k ≤ 2*n) :
    coeff i ((X : Series) ^ triangular (index n k) *
      (gaussian (X^4) (2*n) k * quarticProd n)) =
      (if triangular (index n k) = i then (1 : ℚ) else 0) := by
  rw [coeff_X_pow_mul']
  by_cases hsmall : triangular (index n k) ≤ i
  · obtain ⟨hkL,hkR⟩ := central_of_small hn hsmall
    have hagree := agree_gaussian_mul_quartic hk (by omega : i ≤ n) hkL hkR
    rw [if_pos hsmall, hagree _ (Nat.sub_le _ _), coeff_one]
    by_cases he : triangular (index n k) = i
    · simp [he]
    · have hne : i - triangular (index n k) ≠ 0 := by omega
      simp [he,hne]
  · rw [if_neg hsmall, if_neg (fun h => hsmall h.le)]

private theorem sum_triangle_indicators {i n : ℕ} (hi : i ≤ n) :
    (∑ k ∈ range (2*n+1), if triangular (index n k) = i then (1 : ℚ) else 0) =
      (if ∃ j : ℕ, triangular j = i then (1 : ℚ) else 0) := by
  by_cases h : ∃ j : ℕ, triangular j = i
  · rw [if_pos h]
    obtain ⟨j,hj⟩ := h
    have hji : j ≤ i := hj ▸ le_triangular j
    obtain ⟨k,hk,hkj⟩ := index_surj_small (hji.trans hi)
    have hk' : triangular (index n k) = i := by rw [hkj,hj]
    have hmem : k ∈ range (2*n+1) := mem_range.mpr (by omega)
    calc
      _ = (if triangular (index n k) = i then (1 : ℚ) else 0) := by
        apply Finset.sum_eq_single k
        · intro l _ hl
          exact if_neg (fun hl' => hl ((triangular_strictMono.injective.comp
            (index_injective n)) (hl'.trans hk'.symm)))
        · exact fun hnot => (hnot hmem).elim
      _ = 1 := if_pos hk'
  · rw [if_neg h]
    exact Finset.sum_eq_zero (fun k _ => if_neg (fun hk => h ⟨index n k,hk⟩))

/-- Gauss's triangular-number generating function in the finite degree range. -/
theorem coeff_product_eq_triangle (m i : ℕ) (hi : i ≤ 2*m) :
    let P : Series := ∏ j ∈ range m, (1 - X ^ (2 * (j + 1)))
    let Q : Series := ∏ j ∈ range m, (1 - X ^ (2*j+1))
    coeff i (P*Q⁻¹) = (if ∃ j : ℕ, j*(j+1)/2 = i then (1 : ℚ) else 0) := by
  change coeff i (evenProd m * (oddProd m)⁻¹) =
    (if ∃ j : ℕ, triangular j = i then (1 : ℚ) else 0)
  let n := 4*m+1
  have hn : 0 < n := by dsimp [n]; omega
  have hnLarge : 2*i ≤ n := by dsimp [n]; omega
  have hagree := (agree_even_odd_ratio hi (show m ≤ 2*n by dsimp [n]; omega)).symm.trans
    (agree_ratio_centeredProduct (show i ≤ 4*n by omega))
  rw [hagree i le_rfl,
    centeredProduct_eq_sum hn (fun k => triangular (index n k))
      (fun k hk => centered_exponent n k hn hk),
    map_sum]
  calc
    _ = (∑ k ∈ range (2*n+1), if triangular (index n k) = i then (1 : ℚ) else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := mem_range.mp hk
      exact coeff_gaussian_term hnLarge (by omega)
    _ = _ := sum_triangle_indicators (by omega)

end OMA.A039825GaussConclusion

end A039825GaussConclusionSection

section oeis_a039825_R1Section

/- The Euler summation and Gauss product reduce the support question to triangular numbers. -/

namespace OMA.R_oeis_a039825_R1

open OMA.S_oeis_a039825
open PowerSeries Classical

private theorem triangle_succ (n : ℕ) :
    (n + 1) * (n + 1 + 1) / 2 = n * (n + 1) / 2 + n + 1 := by
  have h : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
  rw [h]
  omega

private theorem triangle_strictMono : StrictMono (fun n : ℕ => n * (n + 1) / 2) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [triangle_succ]
  omega

private theorem triangle_ge_three {n : ℕ} (hn : 2 ≤ n) : 3 ≤ n * (n + 1) / 2 :=
  triangle_strictMono.monotone hn

private theorem exponent_of_triangle (n : ℕ) : a n = (n * (n + 1) / 2 + 4) / 2 := by
  unfold a
  have hprod : n ^ 2 + n = n * (n + 1) := by ring
  have he := Nat.even_iff.mp (Nat.even_mul_succ_self n)
  rw [hprod]
  omega

private theorem neighboring_triangles (m : ℕ) (hm : 0 < m) :
    ¬ ((∃ n : ℕ, n * (n + 1) / 2 = 2 * m + 1) ∧
       (∃ n : ℕ, n * (n + 1) / 2 = 2 * m)) := by
  rintro ⟨⟨y, hy⟩, ⟨x, hx⟩⟩
  have hx1 : 1 ≤ x := by
    by_contra! h
    have hx0 : x = 0 := by omega
    subst x
    simp at hx
    omega
  have hxy : x < y := triangle_strictMono.lt_iff_lt.mp (by omega)
  have hh := triangle_strictMono.monotone (show x + 1 ≤ y by omega)
  change (x + 1) * (x + 1 + 1) / 2 ≤ y * (y + 1) / 2 at hh
  rw [triangle_succ, hx, hy] at hh
  omega

private theorem exponent_iff_adjacent (m : ℕ) (hm : 0 < m) :
    (∃ n : ℕ, 2 ≤ n ∧ a n = m + 2) ↔
      (∃ n : ℕ, n * (n + 1) / 2 = 2 * m + 1) ∨ (∃ n : ℕ, n * (n + 1) / 2 = 2 * m) := by
  constructor
  · rintro ⟨n, hn, he⟩
    rw [exponent_of_triangle] at he
    by_cases he' : n * (n + 1) / 2 = 2 * m + 1
    · exact Or.inl ⟨n, he'⟩
    · exact Or.inr ⟨n, by omega⟩
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    all_goals
      have hN : 2 ≤ n := by
        by_contra! h
        interval_cases n <;> norm_num at hn <;> omega
      exact ⟨n, hN, by rw [exponent_of_triangle, hn]; omega⟩

private theorem support_after_difference (m : ℕ) :
    (if ∃ n : ℕ, n * (n + 1) / 2 = 2 * m + 1 then (1 : ℚ) else 0) -
      (if ∃ n : ℕ, n * (n + 1) / 2 = 2 * m then 1 else 0) ≠ 0 ↔
      ∃ n : ℕ, 2 ≤ n ∧ a n = m + 2 := by
  by_cases hm : m = 0
  · subst m
    have h0 : ∃ n : ℕ, n * (n + 1) / 2 = 2 * 0 := ⟨0, by decide⟩
    have h1 : ∃ n : ℕ, n * (n + 1) / 2 = 2 * 0 + 1 := ⟨1, by decide⟩
    rw [if_pos h1, if_pos h0, sub_self]
    constructor
    · intro h
      exact (h rfl).elim
    · rintro ⟨n, hn, he⟩
      have ht := triangle_ge_three hn
      rw [exponent_of_triangle] at he
      omega
  · rw [exponent_iff_adjacent m (by omega)]
    have hd := neighboring_triangles m (by omega)
    by_cases h₁ : ∃ n : ℕ, n * (n + 1) / 2 = 2 * m + 1 <;>
      by_cases h₀ : ∃ n : ℕ, n * (n + 1) / 2 = 2 * m
    · exact (hd ⟨h₁, h₀⟩).elim
    · norm_num [h₁, h₀]
    · norm_num [h₁, h₀]
    · norm_num [h₁, h₀]

private theorem small_coeff (m : ℕ) (hm : m < 2) : coeffAt m = 0 := by
  unfold coeffAt
  apply Finset.sum_eq_zero
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  rw [Polynomial.coeff_X_pow_mul']
  simp [show ¬ 3 * n ≤ m by omega]

/-- The finite coefficient form of the odd-index Euler summation after `q = X²`. -/
def H1 : Prop :=
  ∀ m : ℕ,
    let P : ℚ⟦X⟧ := ∏ j ∈ Finset.range (m + 2), (1 - X ^ (2 * (j + 1)))
    let Q : ℚ⟦X⟧ := ∏ j ∈ Finset.range (m + 2), (1 - X ^ (2 * j + 1))
    (coeffAt (m + 2) : ℚ) = coeff (2 * m + 1) ((1 - X) * (P * Q⁻¹))

/-- Gauss's triangular-number identity in degrees unaffected by truncation. -/
def H2 : Prop :=
  ∀ m i : ℕ, i ≤ 2 * m →
    let P : ℚ⟦X⟧ := ∏ j ∈ Finset.range m, (1 - X ^ (2 * (j + 1)))
    let Q : ℚ⟦X⟧ := ∏ j ∈ Finset.range m, (1 - X ^ (2 * j + 1))
    coeff i (P * Q⁻¹) = (if ∃ n : ℕ, n * (n + 1) / 2 = i then (1 : ℚ) else 0)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a039825.main := by
  intro hEuler hGauss m
  by_cases hm : m < 2
  · rw [small_coeff m hm]
    constructor
    · simp
    · rintro ⟨n, hn, he⟩
      have hTri := triangle_ge_three hn
      rw [exponent_of_triangle] at he
      omega
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = j + 2 := ⟨m - 2, by omega⟩
    have hEq := hEuler j
    dsimp only at hEq
    rw [sub_mul, one_mul, map_sub, coeff_succ_X_mul,
      hGauss (j + 2) (2 * j + 1) (by omega), hGauss (j + 2) (2 * j) (by omega)] at hEq
    have hCast : ((coeffAt (j + 2) : ℚ) ≠ 0) ↔ ∃ n : ℕ, 2 ≤ n ∧ a n = j + 2 := by
      rw [hEq]
      exact support_after_difference j
    exact_mod_cast hCast

end OMA.R_oeis_a039825_R1

end oeis_a039825_R1Section

theorem OMA.solution : type_of% @OMA.S_oeis_a039825.main :=
  OMA.R_oeis_a039825_R1.main OMA.A039825Euler.coeffAt_eq_euler_product
    OMA.A039825GaussConclusion.coeff_product_eq_triangle
