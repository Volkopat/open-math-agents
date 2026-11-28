import OMAStatements.S_oeis_a300589
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

-- Credit: @HBreitkreutz
namespace OMA.A300589Proof

open PowerSeries

variable {R : Type*} [CommRing R]

/-- The Euler derivative multiplies the coefficient in degree n by n. -/
noncomputable def euler (f : PowerSeries R) : PowerSeries R :=
  X * derivative R f

lemma euler_coeff (f : PowerSeries R) (n : ℕ) :
    coeff n (euler f) = (n : R) * coeff n f := by
  cases n with
  | zero => simp [euler, coeff_zero_X_mul]
  | succ n =>
    rw [euler, coeff_succ_X_mul, coeff_derivative, Nat.cast_succ]
    ring

lemma euler_X : euler (X : PowerSeries R) = X := by simp [euler]

lemma euler_add (f g : PowerSeries R) : euler (f + g) = euler f + euler g := by
  simp [euler, mul_add]

lemma euler_sub (f g : PowerSeries R) : euler (f - g) = euler f - euler g := by
  simp [euler, mul_sub]

lemma euler_mul (f g : PowerSeries R) :
    euler (f * g) = euler f * g + f * euler g := by
  simp only [euler, Derivation.leibniz, smul_eq_mul]
  ring

/-- Clearing the factor of X permits the entire calculation in the power-series ring. -/
lemma normalization (g v a : PowerSeries R)
    (ha : X * a = X * (g * g + v + v) - v * v)
    (hx : (1 - euler g) * v = X) (hv : euler v = (1 - euler g) * g) :
    euler (euler a + a) = g + g := by
  have hprod : v * euler v = X * g := by rw [hv, ← hx]; ring
  have hsum : g * euler g + euler v = g := by rw [hv]; ring
  have hd := congrArg euler ha
  simp only [euler_mul, euler_X, euler_add, euler_sub] at hd
  have hcancel : X * (euler a + a) = X * (g * g + v + v) := by
    linear_combination hd + 2 * X * hsum - 2 * hprod
  have hinner : euler a + a = g * g + v + v := by
    ext n
    simpa only [coeff_succ_X_mul] using congrArg (coeff (n + 1)) hcancel
  rw [hinner, euler_add, euler_add, euler_mul]
  linear_combination 2 * hsum

noncomputable def exponential (g : PowerSeries ℚ) (n : ℕ) : PowerSeries ℚ :=
  subst (C (n : ℚ) * g) (PowerSeries.exp ℚ)

lemma exponential_zero (g : PowerSeries ℚ) (hg : constantCoeff g = 0) (n : ℕ) :
    coeff 0 (exponential g n) = 1 := by
  let t := C (n : ℚ) * g
  have ht : constantCoeff t = 0 := by simp [t, hg]
  have hs : HasSubst t := HasSubst.of_constantCoeff_zero ht
  have h1 : subst t (1 : PowerSeries ℚ) = 1 := by
    rw [← coe_substAlgHom hs, map_one]
  have he : constantCoeff (PowerSeries.exp ℚ - 1) = 0 := by simp [constantCoeff_exp]
  have h := constantCoeff_subst_eq_zero (a := t) ht _ he
  change constantCoeff (subst t (PowerSeries.exp ℚ - 1)) = 0 at h
  rw [subst_sub hs, h1, map_sub, map_one, sub_eq_zero] at h
  change coeff 0 (subst t (PowerSeries.exp ℚ)) = 1
  simpa only [coeff_zero_eq_constantCoeff] using h

lemma euler_exponential (g : PowerSeries ℚ) (hg : constantCoeff g = 0) (n : ℕ) :
    euler (exponential g n) = C (n : ℚ) * (euler g * exponential g n) := by
  have ht : constantCoeff (C (n : ℚ) * g) = 0 := by simp [hg]
  have hs : HasSubst (C (n : ℚ) * g) := HasSubst.of_constantCoeff_zero ht
  unfold euler exponential
  rw [derivative_subst hs, derivative_exp, Derivation.leibniz, derivative_C]
  simp only [smul_eq_mul, mul_zero, add_zero]
  ring

/-- Formal integration by parts at a fixed positive degree. -/
lemma coefficient_parts (f e q : PowerSeries ℚ) (n : ℕ)
    (he : euler e = C (n : ℚ) * (q * e)) :
    coeff n (euler f * e) = (n : ℚ) * coeff n (f * (1 - q) * e) := by
  have h := euler_coeff (f * e) n
  rw [euler_mul, map_add, he,
    show f * (C (n : ℚ) * (q * e)) = C (n : ℚ) * (f * q * e) by ring,
    coeff_C_mul] at h
  rw [show f * (1 - q) * e = f * e - f * q * e by ring, map_sub]
  linear_combination h

lemma first_product_coeff {n : ℕ} (f e : PowerSeries ℚ)
    (hf : ∀ i < n, coeff i f = 0) (he : coeff 0 e = 1) :
    coeff n (f * e) = coeff n f := by
  rw [coeff_mul, Finset.sum_eq_single (n, 0)]
  · simp [he]
  · rintro ⟨i, j⟩ hij hp
    have heq : i + j = n := by simpa using hij
    have hi : i < n := by
      by_contra! hh
      exact hp (Prod.ext (by dsimp; omega) (by dsimp; omega))
    simp [hf i hi]
  · simp

/-- A unit series in each degree gives a triangular test for a series to vanish. -/
lemma diagonal_vanish (f : PowerSeries ℚ) (e : ℕ → PowerSeries ℚ)
    (he : ∀ n, coeff 0 (e n) = 1) (hf : ∀ n, coeff n (f * e n) = 0) :
    f = 0 := by
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | h n ih => exact (first_product_coeff f (e n) ih (he n)).symm.trans (hf n)

/-- The defining exponential identities force the second differential equation,
given the first one. -/
lemma flow_of_coefficients (g v : PowerSeries ℚ) (hg : constantCoeff g = 0)
    (hx : (1 - euler g) * v = X)
    (hsource : ∀ n : ℕ, 0 < n → coeff n (exponential g n) =
      (n : ℚ) ^ 2 * coeff (n - 1) (exponential g n)) :
    euler v = (1 - euler g) * g := by
  apply sub_eq_zero.mp
  apply diagonal_vanish _ (exponential g) (exponential_zero g hg)
  intro n
  cases n with
  | zero => simp [euler, coeff_zero_eq_constantCoeff, hg]
  | succ k =>
    let e := exponential g (k + 1)
    let q := euler g
    have he : euler e = C ((k + 1 : ℕ) : ℚ) * (q * e) := euler_exponential g hg _
    have hg' := coefficient_parts g e q (k + 1) he
    have hv' := coefficient_parts v e q (k + 1) he
    have hdegree := euler_coeff e (k + 1)
    rw [he, coeff_C_mul] at hdegree
    have hn : ((k + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hco : coeff (k + 1) (q * e) = coeff (k + 1) e :=
      mul_left_cancel₀ hn hdegree
    have hx' : v * (1 - q) = X := (mul_comm _ _).trans hx
    rw [hx', coeff_succ_X_mul] at hv'
    have hdef : coeff (k + 1) e = ((k + 1 : ℕ) : ℚ) ^ 2 * coeff k e := by
      simpa only [Nat.add_sub_cancel] using hsource (k + 1) (Nat.succ_pos k)
    have rel : ((k + 1 : ℕ) : ℚ) * coeff (k + 1) (g * (1 - q) * e) =
        ((k + 1 : ℕ) : ℚ) * coeff (k + 1) (euler v * e) := by
      calc
        _ = coeff (k + 1) (q * e) := hg'.symm
        _ = coeff (k + 1) e := hco
        _ = _ := by rw [hdef, hv']; ring
    change coeff (k + 1) ((euler v - (1 - q) * g) * e) = 0
    rw [sub_mul, map_sub, sub_eq_zero, mul_comm (1 - q) g]
    exact (mul_left_cancel₀ hn rel).symm


abbrev integers : Subring ℚ := (Int.castRingHom ℚ).range

lemma integer_product (f h : PowerSeries ℚ)
    (hf : ∀ i, coeff i f ∈ integers) (hh : ∀ j, coeff j h ∈ integers) (n : ℕ) :
    coeff n (f * h) ∈ integers := by
  rw [coeff_mul]
  exact integers.sum_mem fun ⟨i, j⟩ _ => integers.mul_mem (hf i) (hh j)

lemma integer_product_lower (f h : PowerSeries ℚ) (n : ℕ)
    (f0 : coeff 0 f = 0) (h0 : coeff 0 h = 0)
    (hf : ∀ i < n, coeff i f ∈ integers) (hh : ∀ j < n, coeff j h ∈ integers) :
    coeff n (f * h) ∈ integers := by
  rw [coeff_mul]
  apply integers.sum_mem
  rintro ⟨i, j⟩ hij
  have hsum : i + j = n := by simpa using hij
  change coeff i f * coeff j h ∈ integers
  by_cases hi : i = 0
  · simp [hi, f0]
  by_cases hj : j = 0
  · simp [hj, h0]
  exact integers.mul_mem (hf _ (by omega)) (hh _ (by omega))

lemma integer_flow (g v : PowerSeries ℚ) (hg : constantCoeff g = 0)
    (hx : (1 - euler g) * v = X) (hv : euler v = (1 - euler g) * g) :
    ∀ n, coeff n v ∈ integers ∧ coeff n g ∈ integers := by
  have hg0 : coeff 0 g = 0 := by simpa only [coeff_zero_eq_constantCoeff] using hg
  have h0 := congrArg constantCoeff hx
  have hv0 : coeff 0 v = 0 := by simpa [euler, coeff_zero_eq_constantCoeff] using h0
  have hq0 : coeff 0 (euler g) = 0 := by simp [euler_coeff]
  have vr : v = X + euler g * v := by linear_combination hx
  have gr : g = euler v + euler g * g := by linear_combination -hv
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have dq : ∀ j < n, coeff j (euler g) ∈ integers := by
      intro j hj
      rw [euler_coeff]
      exact integers.mul_mem (natCast_mem integers j) (ih j hj).2
    have cx : coeff n (X : PowerSeries ℚ) ∈ integers := by
      by_cases hn : n = 1 <;> simp [coeff_X, hn]
    have vi : coeff n v ∈ integers := by
      rw [congrArg (coeff n) vr, map_add]
      exact integers.add_mem cx (integer_product_lower _ _ n hq0 hv0 dq fun j hj => (ih j hj).1)
    refine ⟨vi, ?_⟩
    rw [congrArg (coeff n) gr, map_add, euler_coeff]
    exact integers.add_mem (integers.mul_mem (natCast_mem integers n) vi)
      (integer_product_lower _ _ n hq0 hg0 dq fun j hj => (ih j hj).2)

/-- For every rational series satisfying the OEIS exponential identity,
each positive-degree coefficient is an integral multiple of its triangular number. -/
theorem source_integrality (g : PowerSeries ℚ) (hg : constantCoeff g = 0)
    (hs : ∀ n : ℕ, 0 < n → coeff n (exponential g n) =
      (n : ℚ) ^ 2 * coeff (n - 1) (exponential g n)) :
    ∀ n : ℕ, 0 < n → ∃ b : ℤ, coeff n g = (b : ℚ) ∧
      ((n * (n + 1) / 2 : ℕ) : ℤ) ∣ b := by
  let h := 1 - euler g
  let v : PowerSeries ℚ := X * h⁻¹
  have h0 : constantCoeff h = 1 := by simp [h, euler]
  have hx : (1 - euler g) * v = X := by
    change h * (X * h⁻¹) = X
    calc
      _ = X * (h * h⁻¹) := by ring
      _ = X := by rw [PowerSeries.mul_inv_cancel h (by rw [h0]; norm_num), mul_one]
  have hv := flow_of_coefficients g v hg hx hs
  have whole := integer_flow g v hg hx hv
  let c : PowerSeries ℚ := mk fun k => coeff (k + 1) v
  have hxc : X * c = v := by
    ext k
    cases k with
    | zero => simp [v, coeff_zero_X_mul]
    | succ k => simp only [coeff_succ_X_mul, c, coeff_mk]
  let a := g * g + v + v - v * c
  have ha : X * a = X * (g * g + v + v) - v * v := by
    dsimp [a]
    linear_combination -v * hxc
  have flow := normalization g v a ha hx hv
  intro n _
  have ca : coeff n a ∈ integers := by
    change coeff n (g * g + v + v - v * c) ∈ integers
    rw [map_sub, map_add, map_add]
    apply integers.sub_mem
    · exact integers.add_mem (integers.add_mem (integer_product g g
        (fun j => (whole j).2) (fun j => (whole j).2) n) (whole n).1) (whole n).1
    · apply integer_product v c (fun j => (whole j).1) _ n
      intro j
      simpa only [c, coeff_mk] using (whole (j + 1)).1
  obtain ⟨z, hz⟩ := ca
  change (z : ℚ) = coeff n a at hz
  have hcoef := congrArg (coeff n) flow
  simp only [euler_coeff, map_add] at hcoef
  have hq : (n : ℚ) * ((n : ℚ) + 1) * coeff n a = 2 * coeff n g := by
    linear_combination hcoef
  have ht : (2 : ℚ) * (↑(n * (n + 1) / 2) : ℚ) = (n : ℚ) * ((n : ℚ) + 1) := by
    exact_mod_cast Nat.mul_div_cancel' (n.two_dvd_mul_add_one)
  rw [← ht] at hq
  refine ⟨((n * (n + 1) / 2 : ℕ) : ℤ) * z, ?_, ⟨z, rfl⟩⟩
  rw [Int.cast_mul, Int.cast_natCast, hz]
  linear_combination -hq / 2

namespace Bridge

open PowerSeries OMA.S_oeis_a300589

noncomputable def series : PowerSeries ℚ :=
  mk fun k => (truncation k).coeff k

lemma unchanged (n j : ℕ) (hj : j ≠ n + 1) :
    (truncation (n + 1)).coeff j = (truncation n).coeff j := by
  simp [truncation, Polynomial.coeff_monomial, Ne.symm hj]

lemma above_degree (n j : ℕ) (hj : n < j) : (truncation n).coeff j = 0 := by
  induction n with
  | zero => simp [truncation]
  | succ n ih =>
    rw [unchanged _ _ (by omega)]
    exact ih (by omega)

lemma stable (k n : ℕ) (hk : k ≤ n) :
    (truncation n).coeff k = (truncation k).coeff k := by
  induction n with
  | zero =>
    have h : k = 0 := by omega
    subst k
    rfl
  | succ n ih =>
    by_cases h : k = n + 1
    · subst k
      rfl
    · rw [unchanged _ _ h]
      exact ih (by omega)

lemma series_zero : constantCoeff series = 0 := by
  rw [← coeff_zero_eq_constantCoeff]
  simp [series, truncation]

lemma agrees (n j : ℕ) (hj : j ≤ n) :
    coeff j series = coeff j (truncation n : PowerSeries ℚ) := by
  simpa [series] using (stable j n hj).symm

lemma trunc_zero (n : ℕ) : coeff 0 (truncation n : PowerSeries ℚ) = 0 := by
  rw [← agrees n 0 (Nat.zero_le _), coeff_zero_eq_constantCoeff, series_zero]

/-- Only the first k+1 coefficients can contribute to a product in degree k. -/
lemma product_congr {a b c d : PowerSeries ℚ} {k : ℕ}
    (h1 : ∀ j ≤ k, coeff j a = coeff j b)
    (h2 : ∀ j ≤ k, coeff j c = coeff j d) :
    coeff k (a * c) = coeff k (b * d) := by
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  have eq : i + j = k := by simpa using hij
  change coeff i a * coeff j c = coeff i b * coeff j d
  rw [h1 _ (by omega), h2 _ (by omega)]

lemma powers_congr {a b : PowerSeries ℚ} {k : ℕ}
    (h : ∀ j ≤ k, coeff j a = coeff j b) (i : ℕ) :
    ∀ j ≤ k, coeff j (a ^ i) = coeff j (b ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    intro j hj
    rw [pow_succ, pow_succ]
    exact product_congr (fun t ht => ih t (ht.trans hj)) (fun t ht => h t (ht.trans hj))

lemma nonlinear_congr {a b : PowerSeries ℚ} {k i : ℕ}
    (a0 : coeff 0 a = 0) (b0 : coeff 0 b = 0)
    (h : ∀ j < k, coeff j a = coeff j b) (hi : 2 ≤ i) :
    coeff k (a ^ i) = coeff k (b ^ i) := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
  rw [pow_succ a (m + 1), pow_succ b (m + 1), coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨u, w⟩ huw
  have hs : u + w = k := by simpa using huw
  change coeff u (a ^ (m + 1)) * coeff w a = coeff u (b ^ (m + 1)) * coeff w b
  by_cases hw : w = 0
  · simp [hw, a0, b0]
  by_cases hu : u = 0
  · have az : constantCoeff a = 0 := by simpa only [coeff_zero_eq_constantCoeff] using a0
    have bz : constantCoeff b = 0 := by simpa only [coeff_zero_eq_constantCoeff] using b0
    simp [hu, coeff_zero_eq_constantCoeff, az, bz]
  have lu : u < k := by omega
  have lw : w < k := by omega
  rw [powers_congr (fun j hj => h j (lt_of_le_of_lt hj lu)) (m + 1) u (le_refl u), h w lw]

/-- The formal exponential is a finite coefficient sum in each degree. -/
lemma exponential_coeff (a : PowerSeries ℚ) (ha : constantCoeff a = 0) (n k : ℕ) :
    coeff k (exponential a n) =
      ∑ i ∈ Finset.range (k + 1), (n : ℚ) ^ i / (i.factorial : ℚ) * coeff k (a ^ i) := by
  let t := C (n : ℚ) * a
  have ht : constantCoeff t = 0 := by simp [t, ha]
  have hs : HasSubst t := HasSubst.of_constantCoeff_zero ht
  change coeff k (subst t (PowerSeries.exp ℚ)) = _
  rw [coeff_subst' hs, finsum_eq_sum_of_support_subset _ (s := Finset.range (k + 1)) ?_]
  · apply Finset.sum_congr rfl
    intro i _
    dsimp only [t]
    rw [coeff_exp, mul_pow, ← map_pow, coeff_C_mul]
    simp only [Algebra.algebraMap_self_apply, smul_eq_mul]
    ring
  · intro i hi
    apply Finset.mem_range.mpr
    by_contra! h
    have lt : (k : ℕ∞) < (i : ℕ∞) := by exact_mod_cast (show k < i by omega)
    have hz : coeff k (t ^ i) = 0 :=
      coeff_of_lt_order k (lt.trans_le (le_order_pow_of_constantCoeff_eq_zero i ht))
    exact hi (by simp [hz])

lemma lower_exponential (n : ℕ) :
    coeff n (exponential series (n + 1)) = expCoeff (truncation n) (n + 1) n := by
  rw [exponential_coeff _ series_zero]
  unfold expCoeff
  apply Finset.sum_congr rfl
  intro i _
  have hp := powers_congr (agrees n) i n (le_refl n)
  rw [hp, ← Polynomial.coe_pow, Polynomial.coeff_coe]

/-- At degree k the only extra exponential term is k times the new coefficient. -/
lemma top_exponential (n : ℕ) :
    coeff (n + 1) (exponential series (n + 1)) =
      expCoeff (truncation n) (n + 1) (n + 1) +
      ((n + 1 : ℕ) : ℚ) * coeff (n + 1) series := by
  let k := n + 1
  let p := truncation n
  have az : coeff 0 series = 0 := by simpa only [coeff_zero_eq_constantCoeff] using series_zero
  have bz : coeff 0 (p : PowerSeries ℚ) = 0 := trunc_zero n
  have low : ∀ j < k, coeff j series = coeff j (p : PowerSeries ℚ) :=
    fun j hj => agrees n j (by dsimp [k] at hj; omega)
  have top : p.coeff k = 0 := above_degree n k (by simp [k])
  change coeff k (exponential series k) = expCoeff p k k + (k : ℚ) * coeff k series
  rw [exponential_coeff _ series_zero]
  unfold expCoeff
  have term : ∀ i ∈ Finset.range (k + 1),
      (k : ℚ) ^ i / (i.factorial : ℚ) * coeff k (series ^ i) =
      (k : ℚ) ^ i / (i.factorial : ℚ) * (p ^ i).coeff k +
        (if i = 1 then (k : ℚ) * coeff k series else 0) := by
    intro i _
    by_cases e0 : i = 0
    · subst i
      simp [k, PowerSeries.coeff_one, Polynomial.coeff_one]
    by_cases e1 : i = 1
    · subst i
      simp [top]
    have hp := nonlinear_congr az bz low (show 2 ≤ i by omega)
    rw [hp, ← Polynomial.coe_pow, Polynomial.coeff_coe]
    simp [e1]
  rw [Finset.sum_congr rfl term, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq', k]

lemma defining (n : ℕ) (hn : 0 < n) :
    coeff n (exponential series n) = (n : ℚ) ^ 2 * coeff (n - 1) (exponential series n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [Nat.succ_eq_add_one, Nat.add_sub_cancel, top_exponential, lower_exponential]
  have c : coeff (k + 1) series = (((k + 1 : ℕ) : ℚ) ^ 2 * expCoeff (truncation k) (k + 1) k -
      expCoeff (truncation k) (k + 1) (k + 1)) / ((k + 1 : ℕ) : ℚ) := by
    simp [series, truncation, above_degree k (k+1) (Nat.lt_succ_self k)]
  rw [c]
  field_simp
  ring

theorem quotient (n : ℕ) (hn : 0 < n) : ∃ z : ℤ,
    (truncation n).coeff n / ((n : ℚ) * ((n : ℚ) + 1) / 2) = (z : ℚ) := by
  obtain ⟨b, hcoef, z, hb⟩ := source_integrality series series_zero defining n hn
  have ht : (2 : ℚ) * (↑(n * (n + 1) / 2) : ℚ) = (n : ℚ) * ((n : ℚ) + 1) := by
    exact_mod_cast Nat.mul_div_cancel' (n.two_dvd_mul_add_one)
  refine ⟨z, ?_⟩
  have hd : 0 < (n : ℚ) * ((n : ℚ) + 1) / 2 := by positivity
  apply (div_eq_iff hd.ne').2
  rw [show (truncation n).coeff n = coeff n series by simp [series], hcoef, hb,
      Int.cast_mul, Int.cast_natCast, ← ht]
  ring

end Bridge

end OMA.A300589Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a300589.main := by
  exact OMA.A300589Proof.Bridge.quotient
