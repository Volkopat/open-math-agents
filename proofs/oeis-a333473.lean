import OMAStatements.S_oeis_a333473
import Mathlib

/-! A333473: coefficient formula via the Catalan route (LtsLagrange), then a p-adic layer comparison using Jacobsthal ratios (LtsJacobsthal). -/


/-! Building blocks toward Lagrange-type coefficient formulas (A333473 / A333472). -/

namespace LtsLagrange
open OMA.S_oeis_a333473

open PowerSeries

theorem coeff_sq (G : PowerSeries ℤ) (n : ℕ) :
    coeff n (G ^ 2) = ∑ i : Fin (n + 1), coeff i G * coeff (n - i) G := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Fin.sum_univ_eq_sum_range (fun i => coeff i G * coeff (n - i) G)]

/-- The quadratic `F = 1 + X + X * F^2`. -/
theorem F_quad : F = 1 + X + X * F ^ 2 := by
  ext n
  rcases n with _ | n
  · simp [F, fc]
  · rw [map_add, map_add, coeff_succ_X_mul, coeff_sq]
    simp only [F, coeff_mk, coeff_one, coeff_X]
    rw [fc]
    split_ifs <;> simp_all

/-- Uniqueness: any solution of the quadratic over a commutative ring is determined. -/
theorem quad_unique {R : Type*} [CommRing R] (G H : PowerSeries R)
    (hG : G = 1 + X + X * G ^ 2) (hH : H = 1 + X + X * H ^ 2) : G = H := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [hG, hH]; simp
    · rw [hG, hH]
      simp only [map_add, coeff_succ_X_mul]
      congr 1
      rw [pow_two, pow_two, coeff_mul, coeff_mul]
      refine Finset.sum_congr rfl fun ij hij => ?_
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      rw [ih ij.1 (by omega), ih ij.2 (by omega)]

theorem F_unit : IsUnit F := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp [F, fc]

theorem F_inv : F * Ring.inverse F = 1 := Ring.mul_inverse_cancel F F_unit

theorem X_ne : (X : PowerSeries ℤ) ≠ 0 := PowerSeries.X_ne_zero

theorem oneX_ne : (1 + X : PowerSeries ℤ) ≠ 0 := by
  intro h
  have := congrArg (constantCoeff) h
  simp at this

/-- Step-1 reduction: a family with G 0 = 1, G 1 = F and the three-term
recurrence X G(q+1) = G q - (1+X) G(q-1) is the family of integer powers of F. -/
theorem fam_eq (G : ℤ → PowerSeries ℤ) (h0 : G 0 = 1) (h1 : G 1 = F)
    (hr : ∀ q : ℤ, X * G (q + 1) = G q - (1 + X) * G (q - 1)) :
    ∀ q, G q = Fpow q := by
  set I := Ring.inverse F with hI
  have hFI : F * I = 1 := F_inv
  have pos : ∀ n : ℕ, G n = F ^ n ∧ G (n + 1) = F ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp [h0, h1]
    | succ n ih =>
      refine ⟨by exact_mod_cast ih.2, ?_⟩
      have h := hr ((n : ℤ) + 1)
      have e1 : ((n : ℤ) + 1 + 1) = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
      have e2 : ((n : ℤ) + 1 - 1) = (n : ℤ) := by ring
      rw [e1, e2, ih.1, ih.2] at h
      apply mul_left_cancel₀ X_ne
      rw [h]
      have q := F_quad
      calc F ^ (n + 1) - (1 + X) * F ^ n = F ^ n * (F - (1 + X)) := by ring
        _ = F ^ n * (X * F ^ 2) := by linear_combination F ^ n * q
        _ = X * F ^ (n + 1 + 1) := by ring
  have key : 1 = (1 + X) * I + X * F := by
    have q := F_quad
    calc (1 : PowerSeries ℤ) = F * I := hFI.symm
      _ = (1 + X + X * F ^ 2) * I := by rw [← q]
      _ = (1 + X) * I + X * F * (F * I) := by ring
      _ = (1 + X) * I + X * F := by rw [hFI]; ring
  have neg : ∀ n : ℕ, G (-(n : ℤ)) = I ^ n ∧ G (-((n : ℤ) + 1)) = I ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp [h0], ?_⟩
      have h := hr 0
      simp only [zero_add, zero_sub, h1, h0] at h
      apply mul_left_cancel₀ oneX_ne
      simp only [Nat.cast_zero, zero_add, pow_one]
      linear_combination h + key
    | succ n ih =>
      refine ⟨by push_cast; exact ih.2, ?_⟩
      have h := hr (-((n : ℤ) + 1))
      have e1 : -((n : ℤ) + 1) + 1 = -(n : ℤ) := by ring
      have e2 : -((n : ℤ) + 1) - 1 = -(((n + 1 : ℕ) : ℤ) + 1) := by push_cast; ring
      rw [e1, e2, ih.1, ih.2] at h
      apply mul_left_cancel₀ oneX_ne
      have k2 : I ^ (n + 1) = (1 + X) * I ^ (n + 2) + X * I ^ n := by
        calc I ^ (n + 1) = I ^ (n + 1) * 1 := by ring
          _ = I ^ (n + 1) * ((1 + X) * I + X * F) := by rw [← key]
          _ = (1 + X) * I ^ (n + 2) + X * I ^ n * (F * I) := by ring
          _ = (1 + X) * I ^ (n + 2) + X * I ^ n := by rw [hFI]; ring
      linear_combination h + k2
  intro q
  rcases q with n | n
  · simp only [Fpow, Int.ofNat_eq_natCast, Nat.cast_nonneg, if_true, Int.toNat_natCast]
    exact (pos n).1
  · have hq : Int.negSucc n = -((n : ℤ) + 1) := rfl
    rw [hq, (neg n).2]
    simp only [Fpow]
    rw [if_neg (by omega)]
    congr 1

end LtsLagrange

namespace LtsLagrange
open OMA.S_oeis_a333473

open PowerSeries

/-- generalized ballot numbers b(q,k) = C(2k+q-1,k) - C(2k+q-1,k-1). -/
def bb (q : ℤ) : ℕ → ℤ
  | 0 => 1
  | k + 1 => Ring.choose (2 * (k : ℤ) + q + 1) (k + 1) - Ring.choose (2 * (k : ℤ) + q + 1) k

theorem bb_rec (q : ℤ) (j : ℕ) : bb q (j + 1) - bb (q - 1) (j + 1) = bb (q + 1) j := by
  rcases j with _ | i
  · simp only [bb, Nat.cast_zero, mul_zero, zero_add, Ring.choose_one_right, Ring.choose_zero_right]
    ring
  · simp only [bb]
    have e1 : (2 * ((i + 1 : ℕ) : ℤ) + q + 1) = (2 * (i : ℤ) + q + 2) + 1 := by push_cast; ring
    have e2 : (2 * ((i + 1 : ℕ) : ℤ) + (q - 1) + 1) = (2 * (i : ℤ) + q + 2) := by push_cast; ring
    have e3 : (2 * (i : ℤ) + (q + 1) + 1) = (2 * (i : ℤ) + q + 2) := by ring
    rw [e1, e2, e3, Ring.choose_succ_succ, Ring.choose_succ_succ]
    ring

/-- the series (1+X)^r for integer r -/
def Hs (r : ℤ) : PowerSeries ℤ := mk fun j => Ring.choose r j

theorem Hs_succ (r : ℤ) : Hs (r + 1) = (1 + X) * Hs r := by
  ext j
  rcases j with _ | j
  · simp [Hs, Ring.choose_zero_right]
  · rw [add_mul, one_mul, map_add, coeff_succ_X_mul]
    simp only [Hs, coeff_mk, Ring.choose_succ_succ]
    ring

theorem Hs_nat (d : ℕ) : Hs d = (1 + X) ^ d := by
  induction d with
  | zero =>
    ext j
    simp only [Hs, coeff_mk, Nat.cast_zero, pow_zero, coeff_one]
    rw [show ((0 : ℤ)) = ((0 : ℕ) : ℤ) by rfl, Ring.choose_natCast]
    rcases j with _ | j <;> simp
  | succ d ih =>
    rw [Nat.cast_succ, Hs_succ, ih]; ring

def gq (q : ℤ) (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (m + 1), bb q k * Ring.choose (q + k) (m - k)

def G (q : ℤ) : PowerSeries ℤ := mk (gq q)

noncomputable def Sm (q : ℤ) (N : ℕ) : PowerSeries ℤ :=
  ∑ k ∈ Finset.range N, C (bb q k) * X ^ k * Hs (q + k)

theorem coeff_term (a : ℤ) (k m : ℕ) (r : ℤ) :
    coeff m (C a * X ^ k * Hs r) = if k ≤ m then a * Ring.choose r (m - k) else 0 := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs <;> simp [Hs]

theorem coeff_Sm (q : ℤ) (N m : ℕ) (h : m < N) : coeff m (Sm q N) = gq q m := by
  rw [Sm, map_sum, gq]
  simp only [coeff_term]
  symm
  apply Finset.sum_subset_zero_on_sdiff
  · intro k hk; simp only [Finset.mem_range] at *; omega
  · intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_range] at hk
    rw [if_neg (by omega)]
  · intro k hk
    simp only [Finset.mem_range] at hk
    rw [if_pos (by omega)]

theorem Sm_rec (q : ℤ) (N : ℕ) : Sm q (N + 1) - (1 + X) * Sm (q - 1) (N + 1) = X * Sm (q + 1) N := by
  have h1 : (1 + X) * Sm (q - 1) (N + 1) =
      ∑ k ∈ Finset.range (N + 1), C (bb (q - 1) k) * X ^ k * Hs (q + k) := by
    rw [Sm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : q + (k : ℤ) = (q - 1 + k) + 1 := by ring
    rw [this, Hs_succ]; ring
  rw [h1, Sm, ← Finset.sum_sub_distrib, Finset.sum_range_succ', Sm, Finset.mul_sum]
  rw [show bb q 0 = bb (q - 1) 0 from rfl, sub_self, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hb := bb_rec q j
  rw [← sub_mul, ← sub_mul, ← map_sub, hb]
  have : q + ((j + 1 : ℕ) : ℤ) = q + 1 + j := by push_cast; ring
  rw [this, pow_succ]; ring

theorem gq_zero (q : ℤ) : gq q 0 = 1 := by
  simp [gq, bb, Ring.choose_zero_right]

theorem G_rec (q : ℤ) : X * G (q + 1) = G q - (1 + X) * G (q - 1) := by
  ext m
  rcases m with _ | m
  · simp [G, gq_zero]
  · have h := congrArg (coeff (m + 1)) (Sm_rec q (m + 1))
    rw [coeff_succ_X_mul] at h ⊢
    rw [add_mul, one_mul, map_sub, map_add, coeff_succ_X_mul] at h ⊢
    rw [coeff_Sm _ _ _ (by omega), coeff_Sm _ _ _ (by omega), coeff_Sm _ _ _ (by omega),
      coeff_Sm _ _ _ (by omega)] at h
    simp only [G, coeff_mk]
    linarith

theorem bb_zero (k : ℕ) : bb 0 (k + 1) = 0 := by
  simp only [bb, add_zero]
  rw [show (2 * (k : ℤ) + 1) = ((2 * k + 1 : ℕ) : ℤ) by push_cast; ring,
    Ring.choose_natCast, Ring.choose_natCast, Nat.choose_symm_half]
  ring

theorem G_zero : G 0 = 1 := by
  ext m
  simp only [G, coeff_mk, gq, coeff_one]
  rw [Finset.sum_range_succ']
  simp only [bb_zero, zero_mul, Finset.sum_const_zero, zero_add]
  simp only [bb, one_mul, Nat.cast_zero, Nat.sub_zero, add_zero]
  rw [show ((0 : ℤ)) = ((0 : ℕ) : ℤ) by rfl, Ring.choose_natCast]
  rcases m with _ | m <;> simp

theorem bb_one (k : ℕ) : bb 1 k = catalan k := by
  rcases k with _ | k
  · simp [bb]
  · simp only [bb]
    rw [show (2 * (k : ℤ) + 1 + 1) = ((2 * k + 2 : ℕ) : ℤ) by push_cast; ring,
      Ring.choose_natCast, Ring.choose_natCast]
    have h1 := succ_mul_catalan_eq_centralBinom (k + 1)
    have h2 := Nat.choose_succ_right_eq (2 * k + 2) k
    rw [Nat.centralBinom, show 2 * (k + 1) = 2 * k + 2 by ring] at h1
    rw [show 2 * k + 2 - k = k + 2 by omega] at h2
    have h1' : ((k + 1 + 1 : ℕ) : ℤ) * catalan (k + 1) = ((2 * k + 2).choose (k + 1) : ℤ) := by
      exact_mod_cast h1
    have h2' : ((2 * k + 2).choose (k + 1) : ℤ) * (k + 1) = ((2 * k + 2).choose k : ℤ) * (k + 2) := by
      exact_mod_cast h2
    have hk : ((k : ℤ) + 2) ≠ 0 := by positivity
    apply mul_left_cancel₀ hk
    push_cast at h1'
    linear_combination h2' - h1'

/-- the Catalan series over ℤ -/
noncomputable def Cz : PowerSeries ℤ := PowerSeries.map (Nat.castRingHom ℤ) catalanSeries

theorem Cz_quad : Cz ^ 2 * X + 1 = Cz := by
  have := congrArg (PowerSeries.map (Nat.castRingHom ℤ)) catalanSeries_sq_mul_X_add_one
  simpa [Cz, map_add, map_mul, map_pow, map_X] using this

noncomputable def sig : PowerSeries ℤ := X * (1 + X)

theorem sig_hs : HasSubst sig := HasSubst.of_constantCoeff_zero' (by simp [sig])

noncomputable def Ct : PowerSeries ℤ := substAlgHom sig_hs Cz

theorem Ct_quad : Ct ^ 2 * sig + 1 = Ct := by
  have := congrArg (substAlgHom sig_hs) Cz_quad
  rw [map_add, map_mul, map_pow, map_one, substAlgHom_X] at this
  exact this

theorem coeff_Ct (m : ℕ) : coeff m Ct =
    ∑ d ∈ Finset.range (m + 1), (catalan d : ℤ) * coeff m (X ^ d * Hs d) := by
  rw [Ct, coe_substAlgHom, coeff_subst' sig_hs]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (m + 1))]
  · refine Finset.sum_congr rfl fun d _ => ?_
    simp [Cz, catalanSeries_coeff, sig, mul_pow, Hs_nat]
  · intro d hd
    simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hd ⊢
    by_contra hc
    apply hd
    rw [sig, mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]

noncomputable def Pc (N : ℕ) : PowerSeries ℤ :=
  ∑ d ∈ Finset.range N, C (catalan d : ℤ) * X ^ d * Hs d

theorem coeff_Ct_Pc (N j : ℕ) (h : j < N) : coeff j Ct = coeff j (Pc N) := by
  rw [coeff_Ct, Pc, map_sum]
  simp only [mul_assoc, coeff_C_mul]
  apply Finset.sum_subset_zero_on_sdiff
  · intro k hk; simp only [Finset.mem_range] at *; omega
  · intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_range] at hk
    rw [coeff_X_pow_mul', if_neg (by omega), mul_zero]
  · intro k _; rfl

theorem coeff_oneX (A : PowerSeries ℤ) (m : ℕ) :
    coeff (m + 1) ((1 + X) * A) = coeff (m + 1) A + coeff m A := by
  rw [add_mul, one_mul, map_add, coeff_succ_X_mul]

theorem oneX_Pc (N : ℕ) : (1 + X) * Pc N = Sm 1 N := by
  rw [Pc, Sm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [bb_one, add_comm (1 : ℤ), Hs_succ]; ring

theorem G_one_eq : G 1 = (1 + X) * Ct := by
  ext m
  have hS := coeff_Sm 1 (m + 1) m (by omega)
  rw [← oneX_Pc] at hS
  simp only [G, coeff_mk]
  rw [← hS]
  rcases m with _ | m
  · simp only [zero_add, add_mul, one_mul, map_add, coeff_zero_X_mul, add_zero]
    exact (coeff_Ct_Pc 1 0 (by omega)).symm
  · rw [coeff_oneX, coeff_oneX, coeff_Ct_Pc (m + 2) (m + 1) (by omega),
      coeff_Ct_Pc (m + 2) m (by omega)]

theorem G_one : G 1 = F := by
  apply quad_unique
  · rw [G_one_eq]
    have h := Ct_quad
    rw [sig] at h
    linear_combination (-(1 + X)) * h
  · exact F_quad

theorem coeff_Fpow (q : ℤ) (m : ℕ) : coeff m (Fpow q) = gq q m := by
  rw [← fam_eq G G_zero G_one G_rec q]
  simp [G]

end LtsLagrange

/-! Jacobsthal-Kazandzidis type congruence C(a p^r, b p^r) = C(a p^(r-1), b p^(r-1)) mod p^(3r), p >= 5. Base lemmas adapted from proofs/oeis-a375180.R1.H4.lean. -/

namespace LtsJacobsthal
open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- `D p e x` : the rational `x` lies in `p^e * ℤ_(p)`. -/
def D (p e : ℕ) (x : ℚ) : Prop :=
  ∃ a : ℤ, ∃ b : ℕ, ¬ p ∣ b ∧ x * (b : ℚ) = (p : ℚ) ^ e * (a : ℚ)

lemma D.zero (e : ℕ) : D p e 0 := ⟨0, 1, hp.out.not_dvd_one, by simp⟩

omit hp in
lemma D.neg {e : ℕ} {x : ℚ} (hx : D p e x) : D p e (-x) := by
  obtain ⟨a, b, hb, h⟩ := hx
  exact ⟨-a, b, hb, by push_cast; linear_combination -h⟩

lemma D.add {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p e y) : D p e (x + y) := by
  obtain ⟨a, b, hb, h⟩ := hx
  obtain ⟨a', b', hb', h'⟩ := hy
  refine ⟨a * b' + a' * b, b * b', ?_, ?_⟩
  · intro hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
    · exact hb h1
    · exact hb' h1
  · push_cast
    linear_combination (b' : ℚ) * h + (b : ℚ) * h'

lemma D.sub {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p e y) : D p e (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

lemma D.mul {e f : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p f y) : D p (e + f) (x * y) := by
  obtain ⟨a, b, hb, h⟩ := hx
  obtain ⟨a', b', hb', h'⟩ := hy
  refine ⟨a * a', b * b', ?_, ?_⟩
  · intro hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
    · exact hb h1
    · exact hb' h1
  · push_cast
    rw [pow_add]
    linear_combination (y * (b' : ℚ)) * h + ((p : ℚ) ^ e * (a : ℚ)) * h'

omit hp in
lemma D.le {e f : ℕ} {x : ℚ} (hx : D p e x) (hfe : f ≤ e) : D p f x := by
  obtain ⟨a, b, hb, h⟩ := hx
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hfe
  exact ⟨(p : ℤ) ^ c * a, b, hb, by push_cast; rw [h, pow_add]; ring⟩

lemma D.int (z : ℤ) : D p 0 (z : ℚ) := ⟨z, 1, hp.out.not_dvd_one, by simp⟩

lemma D.nat (n : ℕ) : D p 0 (n : ℚ) := ⟨(n : ℤ), 1, hp.out.not_dvd_one, by simp⟩

lemma D.one : D p 0 (1 : ℚ) := ⟨1, 1, hp.out.not_dvd_one, by simp⟩

lemma D.ppow (e : ℕ) : D p e ((p : ℚ) ^ e) := ⟨1, 1, hp.out.not_dvd_one, by simp⟩

lemma D.mul0 {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p 0 y) : D p e (x * y) :=
  (hx.mul hy).le (by omega)

lemma D.mul0' {e : ℕ} {x y : ℚ} (hy : D p 0 y) (hx : D p e x) : D p e (y * x) :=
  (hy.mul hx).le (by omega)

omit hp in
lemma D.inv {u : ℕ} (hu : ¬ p ∣ u) : D p 0 ((u : ℚ)⁻¹) := by
  have hu0 : (u : ℚ) ≠ 0 := by
    intro h
    apply hu
    have h0 : u = 0 := by exact_mod_cast h
    rw [h0]; exact dvd_zero p
  exact ⟨1, u, hu, by rw [inv_mul_cancel₀ hu0]; simp⟩

lemma D.sum {ι : Type*} {e : ℕ} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, D p e (f i)) :
    D p e (∑ i ∈ s, f i) :=
  Finset.sum_induction f (D p e) (fun _ _ ha hb => ha.add hb) (D.zero e) h

lemma D.prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, D p 0 (f i)) :
    D p 0 (∏ i ∈ s, f i) :=
  Finset.prod_induction f (D p 0) (fun _ _ ha hb => (ha.mul hb).le (by omega)) D.one h

lemma D.pow {e : ℕ} {x : ℚ} (hx : D p e x) (n : ℕ) : D p (e * n) (x ^ n) := by
  induction n with
  | zero => simpa using (D.one (p := p))
  | succ n ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul hx

lemma D.cancel {e c : ℕ} {x : ℚ} (h : D p (e + c) ((p : ℚ) ^ c * x)) : D p e x := by
  obtain ⟨a, b, hb, h⟩ := h
  refine ⟨a, b, hb, ?_⟩
  have hpc : ((p : ℚ) ^ c) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  apply mul_left_cancel₀ hpc
  rw [pow_add] at h
  linear_combination h

lemma D.ucancel {e u : ℕ} {x : ℚ} (hu : ¬ p ∣ u) (h : D p e ((u : ℚ) * x)) : D p e x := by
  obtain ⟨a, b, hb, h⟩ := h
  refine ⟨a, u * b, ?_, by push_cast; linear_combination h⟩
  intro hd
  rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
  · exact hu h1
  · exact hb h1

lemma D.dvd {e : ℕ} {z : ℤ} (h : D p e (z : ℚ)) : (p : ℤ) ^ e ∣ z := by
  obtain ⟨a, b, hb, h⟩ := h
  have h2 : z * (b : ℤ) = (p : ℤ) ^ e * a := by exact_mod_cast h
  have hc : IsCoprime ((p : ℤ) ^ e) (b : ℤ) := by
    have h3 : Nat.Coprime (p ^ e) b :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hb)
    have h4 := Nat.isCoprime_iff_coprime.mpr h3
    simpa using h4
  exact hc.dvd_of_dvd_mul_right ⟨a, h2⟩

/-! ### index sets -/

/-- the integers `0 < i < L` prime to `p` -/
def U (p L : ℕ) : Finset ℕ := (Finset.range L).filter (fun i => ¬ p ∣ i)

lemma mem_U {p L i : ℕ} : i ∈ U p L ↔ i < L ∧ ¬ p ∣ i := by
  simp [U]

omit hp in
lemma sum_U_blocks {q : ℕ} (hpq : p ∣ q) (f : ℕ → ℚ) (t : ℕ) :
    ∑ i ∈ U p (t * q), f i = ∑ h ∈ Finset.range t, ∑ u ∈ U p q, f (h * q + u) := by
  induction t with
  | zero => simp [U]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold U
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, add_one_mul,
      Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : p ∣ t * q + x ↔ p ∣ x := Nat.dvd_add_right (dvd_mul_of_dvd_right hpq t)
    simp only [h1]

lemma sum_range_mul_split {M : Type*} [AddCommMonoid M] (m n : ℕ) (hm : 0 < m)
    (f : ℕ → M) :
    ∑ k ∈ Finset.range (m * n), f k =
      ∑ k ∈ (Finset.range (m * n)).filter (fun k => ¬ m ∣ k), f k +
        ∑ c ∈ Finset.range n, f (m * c) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (m * n)) (fun k => m ∣ k), add_comm]
  congr 1
  have h1 : (Finset.range (m * n)).filter (fun k => m ∣ k) =
      (Finset.range n).image (fun c => m * c) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, c, rfl⟩
      exact ⟨c, lt_of_mul_lt_mul_left hk (Nat.zero_le m), rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by nlinarith, dvd_mul_right m c⟩
  rw [h1, Finset.sum_image]
  intro x _ y _ h
  exact Nat.eq_of_mul_eq_mul_left hm h

lemma prod_range_mul_split {M : Type*} [CommMonoid M] (m n : ℕ) (hm : 0 < m)
    (f : ℕ → M) :
    ∏ k ∈ Finset.range (m * n), f k =
      (∏ k ∈ (Finset.range (m * n)).filter (fun k => ¬ m ∣ k), f k) *
        ∏ c ∈ Finset.range n, f (m * c) := by
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.range (m * n)) (fun k => m ∣ k), mul_comm]
  congr 1
  have h1 : (Finset.range (m * n)).filter (fun k => m ∣ k) =
      (Finset.range n).image (fun c => m * c) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, c, rfl⟩
      exact ⟨c, lt_of_mul_lt_mul_left hk (Nat.zero_le m), rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by nlinarith, dvd_mul_right m c⟩
  rw [h1, Finset.prod_image]
  intro x _ y _ h
  exact Nat.eq_of_mul_eq_mul_left hm h

/-! ### binomials as products -/

/-- `Gp n m = ∏_{0 < i < m} (1 - n / i)` (the factor `i = 0` is `1`). -/
def Gp (n : ℚ) (m : ℕ) : ℚ := ∏ i ∈ Finset.range m, (1 - n / (i : ℚ))

omit hp in
lemma choose_mul_eq (n k : ℕ) :
    (n.choose (k + 1) : ℚ) * ((k : ℚ) + 1) = (n : ℚ) * (-1) ^ k * Gp n (k + 1) := by
  induction k with
  | zero => simp [Gp]
  | succ k ih =>
    have h1 : (n.choose (k + 1 + 1) : ℚ) * ((k : ℚ) + 1 + 1) =
        (n.choose (k + 1) : ℚ) * ((n : ℚ) - ((k : ℚ) + 1)) := by
      rcases le_or_gt (k + 1) n with h | h
      · have h2 := congrArg (Nat.cast (R := ℚ)) (Nat.choose_succ_right_eq n (k + 1))
        push_cast [Nat.cast_sub h] at h2
        linarith
      · rw [Nat.choose_eq_zero_of_lt (by omega : n < k + 1 + 1), Nat.choose_eq_zero_of_lt h]
        simp
    have hG : Gp n (k + 1 + 1) = Gp n (k + 1) * (1 - (n : ℚ) / ((k : ℚ) + 1)) := by
      unfold Gp
      rw [Finset.prod_range_succ]
      push_cast
      ring
    have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
    have h3 : (n : ℚ) * (-1) ^ (k + 1) * (Gp n (k + 1) * (1 - (n : ℚ) / ((k : ℚ) + 1))) =
        ((n : ℚ) * (-1) ^ k * Gp n (k + 1)) * (((n : ℚ) - ((k : ℚ) + 1)) / ((k : ℚ) + 1)) := by
      field_simp
      ring
    have h4 : ((n.choose (k + 1) : ℚ) * ((k : ℚ) + 1)) * (((n : ℚ) - ((k : ℚ) + 1)) / ((k : ℚ) + 1)) =
        (n.choose (k + 1) : ℚ) * ((n : ℚ) - ((k : ℚ) + 1)) := by
      field_simp
    push_cast
    rw [hG, h3, ← ih, h4, ← h1]

omit hp in
lemma choose_mul_eq' (n k : ℕ) (hk : 1 ≤ k) :
    (n.choose k : ℚ) * (k : ℚ) = -((n : ℚ) * (-1) ^ k * Gp n k) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := choose_mul_eq n k'
  push_cast
  rw [h, pow_succ]
  ring

/-- `R p x L = ∏_{0 < i < L, p ∤ i} (1 - x / i)` -/
def R (p : ℕ) (x : ℚ) (L : ℕ) : ℚ := ∏ i ∈ U p L, (1 - x / (i : ℚ))

omit hp in
lemma Gp_split (hp0 : 0 < p) (x : ℚ) (j : ℕ) :
    Gp x (p * j) = R p x (p * j) * Gp (x / p) j := by
  unfold Gp R U
  rw [prod_range_mul_split p j hp0]
  congr 1
  refine Finset.prod_congr rfl fun c _ => ?_
  push_cast
  rw [div_div]

lemma choose_ratio (hp2 : p ≠ 2) (n j : ℕ) :
    ((p * n).choose (p * j) : ℚ) = (n.choose j : ℚ) * R p ((p * n : ℕ) : ℚ) (p * j) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [R, U]
  have hp0 : 0 < p := hp.out.pos
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have h1 := choose_mul_eq' (p * n) (p * j) (by nlinarith)
  have h2 := choose_mul_eq' n j hj
  have h3 := Gp_split hp0 ((p * n : ℕ) : ℚ) j
  have h4 : ((p * n : ℕ) : ℚ) / (p : ℚ) = (n : ℚ) := by
    push_cast
    field_simp
  have h5 : (-1 : ℚ) ^ (p * j) = (-1) ^ j := by
    rw [pow_mul, hodd.neg_one_pow]
  rw [h3, h4, h5] at h1
  have hpj : ((p * j : ℕ) : ℚ) ≠ 0 := by
    have : 0 < p * j := Nat.mul_pos hp0 hj
    positivity
  have hj0 : (j : ℚ) ≠ 0 := by positivity
  have hpq : (p : ℚ) ≠ 0 := by positivity
  apply mul_right_cancel₀ hpj
  rw [h1]
  push_cast
  have h6 : (n : ℚ) * (-1) ^ j * Gp n j = -((n.choose j : ℚ) * (j : ℚ)) := by rw [h2]; ring
  linear_combination (-(p : ℚ) * R p ((p : ℚ) * (n : ℚ)) (p * j)) * h6

/-! ### expansions of `1/(u+a)^j` -/

lemma D.pow0 {x : ℚ} (hx : D p 0 x) (n : ℕ) : D p 0 (x ^ n) :=
  (hx.pow n).le (Nat.zero_le _)

lemma D.two : D p 0 (2 : ℚ) := by simpa using D.nat (p := p) 2

lemma D.three : D p 0 (3 : ℚ) := by simpa using D.nat (p := p) 3

lemma exp1_D {s : ℕ} {u v a : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (h : v = u + a)
    (hu : D p 0 u⁻¹) (hv : D p 0 v⁻¹) (ha : D p s a) :
    D p (4 * s) (v⁻¹ - (u⁻¹ - a * u⁻¹ ^ 2 + a ^ 2 * u⁻¹ ^ 3 - a ^ 3 * u⁻¹ ^ 4)) := by
  have h1 : v⁻¹ - (u⁻¹ - a * u⁻¹ ^ 2 + a ^ 2 * u⁻¹ ^ 3 - a ^ 3 * u⁻¹ ^ 4) =
      a ^ 4 * u⁻¹ ^ 4 * v⁻¹ := by
    subst h
    field_simp
    ring
  rw [h1]
  exact (((ha.pow 4).mul0 (hu.pow0 4)).mul0 hv).le (by omega)

lemma exp2_D {s : ℕ} {u v a : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (h : v = u + a)
    (hu : D p 0 u⁻¹) (hu' : D p 0 u) (hv : D p 0 v⁻¹) (ha : D p s a) :
    D p (2 * s) (v⁻¹ ^ 2 - (u⁻¹ ^ 2 - 2 * a * u⁻¹ ^ 3)) := by
  have h1 : v⁻¹ ^ 2 - (u⁻¹ ^ 2 - 2 * a * u⁻¹ ^ 3) =
      a ^ 2 * ((3 * u + 2 * a) * u⁻¹ ^ 3 * v⁻¹ ^ 2) := by
    subst h
    field_simp
    ring
  rw [h1]
  have ha0 : D p 0 a := ha.le (Nat.zero_le _)
  have h2 : D p 0 (3 * u + 2 * a) := (D.three.mul0 hu').add (D.two.mul0 ha0)
  exact ((ha.pow 2).mul0 ((h2.mul0 (hu.pow0 3)).mul0 (hv.pow0 2))).le (by omega)

lemma exp3_D {s : ℕ} {u v a : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (h : v = u + a)
    (hu : D p 0 u⁻¹) (hu' : D p 0 u) (hv : D p 0 v⁻¹) (ha : D p s a) :
    D p (2 * s) (v⁻¹ ^ 3 - (u⁻¹ ^ 3 - 3 * a * u⁻¹ ^ 4)) := by
  have h1 : v⁻¹ ^ 3 - (u⁻¹ ^ 3 - 3 * a * u⁻¹ ^ 4) =
      a ^ 2 * ((2 * (3 * u ^ 2) + 2 * (2 * (2 * (u * a))) + 3 * a ^ 2) * u⁻¹ ^ 4 * v⁻¹ ^ 3) := by
    subst h
    field_simp
    ring
  rw [h1]
  have ha0 : D p 0 a := ha.le (Nat.zero_le _)
  have h2 : D p 0 (2 * (3 * u ^ 2) + 2 * (2 * (2 * (u * a))) + 3 * a ^ 2) :=
    ((D.two.mul0 (D.three.mul0 (hu'.pow0 2))).add
      (D.two.mul0 (D.two.mul0 (D.two.mul0 (hu'.mul0 ha0))))).add (D.three.mul0 (ha0.pow0 2))
  exact ((ha.pow 2).mul0 ((h2.mul0 (hu.pow0 4)).mul0 (hv.pow0 3))).le (by omega)

/-! ### products -/

lemma prod_congr_D {ι : Type*} [DecidableEq ι] {e : ℕ} (s : Finset ι) (f g : ι → ℚ)
    (hf : ∀ i ∈ s, D p 0 (f i)) (hg : ∀ i ∈ s, D p 0 (g i)) (h : ∀ i ∈ s, D p e (f i - g i)) :
    D p e (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using D.zero (p := p) e
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        (f a - g a) * ∏ i ∈ s, f i + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by ring
    rw [h1]
    have hs : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    exact ((h a (Finset.mem_insert_self a s)).mul0 (D.prod s f fun i hi => hf i (hs i hi))).add
      ((hg a (Finset.mem_insert_self a s)).mul0'
        (ih (fun i hi => hf i (hs i hi)) (fun i hi => hg i (hs i hi)) (fun i hi => h i (hs i hi))))

lemma prod_expand2 {ι : Type*} [DecidableEq ι] (hp2 : ¬ p ∣ 2) (s : Finset ι)
    (a : ι → ℚ) (x : ℚ) (hx : D p 0 x) (ha : ∀ i ∈ s, D p 0 (a i)) :
    ∃ W : ℚ, D p 0 W ∧ ∏ i ∈ s, (1 - x * a i) =
      1 - x * (∑ i ∈ s, a i) + x ^ 2 * (((∑ i ∈ s, a i) ^ 2 - ∑ i ∈ s, a i ^ 2) / 2) +
        x ^ 3 * W := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, D.zero 0, by simp⟩
  | insert b s hb ih =>
    obtain ⟨W, hW, hprod⟩ := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    have hab := ha b (Finset.mem_insert_self b s)
    have hS1 : D p 0 (∑ i ∈ s, a i) :=
      D.sum s a fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hS2 : D p 0 (∑ i ∈ s, a i ^ 2) :=
      D.sum s _ fun i hi => (ha i (Finset.mem_insert_of_mem hi)).pow0 2
    have h2 : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2
    have hE : D p 0 (((∑ i ∈ s, a i) ^ 2 - ∑ i ∈ s, a i ^ 2) / 2) := by
      rw [div_eq_mul_inv]
      exact ((hS1.pow0 2).sub hS2).mul0 h2
    refine ⟨W - a b * (((∑ i ∈ s, a i) ^ 2 - ∑ i ∈ s, a i ^ 2) / 2) - x * a b * W, ?_, ?_⟩
    · exact (hW.sub (hab.mul0 hE)).sub ((hx.mul0 hab).mul0 hW)
    · rw [Finset.prod_insert hb, Finset.sum_insert hb, Finset.sum_insert hb, hprod]
      ring

/-! ### symmetries of `U p q` -/

omit hp in
lemma sum_U_reflect {q : ℕ} (hpq : p ∣ q) (f : ℕ → ℚ) :
    ∑ u ∈ U p q, f u = ∑ u ∈ U p q, f (q - u) := by
  symm
  have hmem : ∀ u ∈ U p q, q - u ∈ U p q := by
    intro u hu
    obtain ⟨hlt, hnd⟩ := mem_U.mp hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact hnd (dvd_zero p)
    refine mem_U.mpr ⟨by omega, ?_⟩
    intro hd
    have h1 : q - u + u = q := Nat.sub_add_cancel (le_of_lt hlt)
    have h2 : p ∣ q - u + u := by rw [h1]; exact hpq
    exact hnd ((Nat.dvd_add_right hd).mp h2)
  have hinv : ∀ u ∈ U p q, q - (q - u) = u := by
    intro u hu
    obtain ⟨hlt, _⟩ := mem_U.mp hu
    omega
  exact Finset.sum_nbij' (fun u => q - u) (fun u => q - u) hmem hmem hinv hinv
    (fun u _ => rfl)

omit hp in
lemma sum_U_double {q : ℕ} (hp' : p.Prime) (hp2 : ¬ p ∣ 2) (hpq : p ∣ q)
    (hq : Nat.Coprime q 2) (f : ℕ → ℚ) :
    ∑ u ∈ U p q, f (2 * u % q) = ∑ u ∈ U p q, f u := by
  have hinj : Set.InjOn (fun u => 2 * u % q) (U p q : Set ℕ) := by
    intro u hu v hv h
    have hu' := mem_U.mp (Finset.mem_coe.mp hu)
    have hv' := mem_U.mp (Finset.mem_coe.mp hv)
    have h1 : 2 * u ≡ 2 * v [MOD q] := h
    have h2 : u ≡ v [MOD q] := Nat.ModEq.cancel_left_of_coprime hq h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 hu'.1 hv'.1
  have himg : (U p q).image (fun u => 2 * u % q) = U p q := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      have hu' := mem_U.mp hu
      have hq0 : 0 < q := by omega
      refine mem_U.mpr ⟨Nat.mod_lt _ hq0, ?_⟩
      intro hd
      have h3 : p ∣ 2 * u := (Nat.dvd_mod_iff hpq).mp hd
      rcases (Nat.Prime.dvd_mul hp').mp h3 with h4 | h4
      · exact hp2 h4
      · exact hu'.2 h4
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ u ∈ U p q, f (2 * u % q)
      = ∑ w ∈ (U p q).image (fun u => 2 * u % q), f w := by
        rw [Finset.sum_image hinj]
    _ = ∑ u ∈ U p q, f u := by rw [himg]

lemma D_inv_pow_congr {s x y : ℕ} (hx : ¬ p ∣ x) (hy : ¬ p ∣ y)
    (h : D p s ((x : ℚ) - (y : ℚ))) (j : ℕ) :
    D p s (((x : ℚ)⁻¹) ^ j - ((y : ℚ)⁻¹) ^ j) := by
  have hx0 : (x : ℚ) ≠ 0 := by
    intro h0
    apply hx
    have h1 : x = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  have hy0 : (y : ℚ) ≠ 0 := by
    intro h0
    apply hy
    have h1 : y = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  have hxx : (x : ℚ) * (x : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hx0
  have hyy : (y : ℚ) * (y : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hy0
  have h1 : D p s ((x : ℚ)⁻¹ - (y : ℚ)⁻¹) := by
    have h2 : (x : ℚ)⁻¹ - (y : ℚ)⁻¹ = -(((x : ℚ) - (y : ℚ)) * ((x : ℚ)⁻¹ * (y : ℚ)⁻¹)) := by
      linear_combination (y : ℚ)⁻¹ * hxx - (x : ℚ)⁻¹ * hyy
    rw [h2]
    exact (h.mul0 (((D.inv hx).mul (D.inv hy)).le (by omega))).neg
  induction j with
  | zero => simpa using D.zero (p := p) s
  | succ j ih =>
    have h3 : ((x : ℚ)⁻¹) ^ (j + 1) - ((y : ℚ)⁻¹) ^ (j + 1) =
        (x : ℚ)⁻¹ * (((x : ℚ)⁻¹) ^ j - ((y : ℚ)⁻¹) ^ j) +
          ((x : ℚ)⁻¹ - (y : ℚ)⁻¹) * ((y : ℚ)⁻¹) ^ j := by ring
    rw [h3]
    exact ((D.inv hx).mul0' ih).add (h1.mul0 ((D.inv hy).pow0 j))

/-! ### power sums over the units below `p^s` -/

/-- `sg p q j = ∑_{0<u<q, p ∤ u} u^(-j)` -/
def sg (p q j : ℕ) : ℚ := ∑ u ∈ U p q, ((u : ℚ)⁻¹) ^ j

lemma sg_scale (hp2 : ¬ p ∣ 2) {s : ℕ} (hs : 1 ≤ s) (j : ℕ) :
    D p s (((2 : ℚ) ^ j - 1) * sg p (p ^ s) j) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hq2 : Nat.Coprime (p ^ s) 2 :=
    Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hp2)
  have h1 : sg p (p ^ s) j = ∑ u ∈ U p (p ^ s), (((2 * u % p ^ s : ℕ) : ℚ)⁻¹) ^ j := by
    unfold sg
    exact (sum_U_double hp.out hp2 hpq hq2 (fun w => ((w : ℚ)⁻¹) ^ j)).symm
  have h2 : D p s (∑ u ∈ U p (p ^ s),
      ((((2 * u % p ^ s : ℕ) : ℚ)⁻¹) ^ j - (((2 * u : ℕ) : ℚ)⁻¹) ^ j)) := by
    apply D.sum
    intro u hu
    have hu' := mem_U.mp hu
    have h2u : ¬ p ∣ 2 * u := by
      intro hd
      rcases (Nat.Prime.dvd_mul hp.out).mp hd with h4 | h4
      · exact hp2 h4
      · exact hu'.2 h4
    have hmod : ¬ p ∣ 2 * u % p ^ s := fun hd => h2u ((Nat.dvd_mod_iff hpq).mp hd)
    apply D_inv_pow_congr hmod h2u
    have h5 : ((2 * u % p ^ s : ℕ) : ℚ) - ((2 * u : ℕ) : ℚ) =
        -((p : ℚ) ^ s * ((2 * u / p ^ s : ℕ) : ℚ)) := by
      have h6 := Nat.div_add_mod (2 * u) (p ^ s)
      have h7 : ((p ^ s * (2 * u / p ^ s) + 2 * u % p ^ s : ℕ) : ℚ) = ((2 * u : ℕ) : ℚ) := by
        rw [h6]
      push_cast at h7 ⊢
      linarith
    rw [h5]
    exact ((D.ppow s).mul0 (D.nat _)).neg
  rw [Finset.sum_sub_distrib, ← h1] at h2
  have h3 : ∑ u ∈ U p (p ^ s), (((2 * u : ℕ) : ℚ)⁻¹) ^ j = ((2 : ℚ)⁻¹) ^ j * sg p (p ^ s) j := by
    unfold sg
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    push_cast
    rw [mul_inv, mul_pow]
  rw [h3] at h2
  have h4 : ((2 : ℚ) ^ j - 1) * sg p (p ^ s) j =
      (2 : ℚ) ^ j * (sg p (p ^ s) j - ((2 : ℚ)⁻¹) ^ j * sg p (p ^ s) j) := by
    have h5 : (2 : ℚ) ^ j * ((2 : ℚ)⁻¹) ^ j = 1 := by
      rw [← mul_pow]; norm_num
    linear_combination (sg p (p ^ s) j) * h5
  rw [h4]
  exact (D.two.pow0 j).mul0' h2

/-- generic shifted sums: `v = u + a` with `a ∈ p^s ℤ_(p)` -/
lemma shift_sums {s : ℕ} (a : ℚ) (ha : D p s a) (v : ℕ → ℚ)
    (hv : ∀ u ∈ U p (p ^ s), v u = (u : ℚ) + a ∧ v u ≠ 0 ∧ D p 0 (v u)⁻¹) :
    D p (4 * s) (∑ u ∈ U p (p ^ s), (v u)⁻¹ -
      (sg p (p ^ s) 1 - a * sg p (p ^ s) 2 + a ^ 2 * sg p (p ^ s) 3 - a ^ 3 * sg p (p ^ s) 4)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 2 -
      (sg p (p ^ s) 2 - 2 * a * sg p (p ^ s) 3)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 3 -
      (sg p (p ^ s) 3 - 3 * a * sg p (p ^ s) 4)) := by
  have hu : ∀ u ∈ U p (p ^ s), (u : ℚ) ≠ 0 ∧ D p 0 ((u : ℚ)⁻¹) := by
    intro u hu
    obtain ⟨_, hnd⟩ := mem_U.mp hu
    refine ⟨?_, D.inv hnd⟩
    intro h0
    apply hnd
    have h1 : u = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ∑ u ∈ U p (p ^ s), (v u)⁻¹ -
        (sg p (p ^ s) 1 - a * sg p (p ^ s) 2 + a ^ 2 * sg p (p ^ s) 3 - a ^ 3 * sg p (p ^ s) 4) =
        ∑ u ∈ U p (p ^ s), ((v u)⁻¹ - ((u : ℚ)⁻¹ - a * (u : ℚ)⁻¹ ^ 2 + a ^ 2 * (u : ℚ)⁻¹ ^ 3 -
          a ^ 3 * (u : ℚ)⁻¹ ^ 4)) := by
      simp only [sg, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, pow_one]
    rw [h1]
    apply D.sum
    intro u hmem
    obtain ⟨h2, h3, h4⟩ := hv u hmem
    exact exp1_D (hu u hmem).1 h3 h2 (hu u hmem).2 h4 ha
  · have h1 : ∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 2 - (sg p (p ^ s) 2 - 2 * a * sg p (p ^ s) 3) =
        ∑ u ∈ U p (p ^ s), ((v u)⁻¹ ^ 2 - ((u : ℚ)⁻¹ ^ 2 - 2 * a * (u : ℚ)⁻¹ ^ 3)) := by
      simp only [sg, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [h1]
    apply D.sum
    intro u hmem
    obtain ⟨h2, h3, h4⟩ := hv u hmem
    exact exp2_D (hu u hmem).1 h3 h2 (hu u hmem).2 (D.nat u) h4 ha
  · have h1 : ∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 3 - (sg p (p ^ s) 3 - 3 * a * sg p (p ^ s) 4) =
        ∑ u ∈ U p (p ^ s), ((v u)⁻¹ ^ 3 - ((u : ℚ)⁻¹ ^ 3 - 3 * a * (u : ℚ)⁻¹ ^ 4)) := by
      simp only [sg, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [h1]
    apply D.sum
    intro u hmem
    obtain ⟨h2, h3, h4⟩ := hv u hmem
    exact exp3_D (hu u hmem).1 h3 h2 (hu u hmem).2 (D.nat u) h4 ha
/-! ### derived power sum facts -/

omit hp in
lemma D.congr {e : ℕ} {x y : ℚ} (h : D p e x) (hxy : x = y) : D p e y := hxy ▸ h

lemma sg_D0 (q j : ℕ) : D p 0 (sg p q j) :=
  D.sum _ _ fun _ hu => (D.inv (mem_U.mp hu).2).pow0 j

/-- `Eps p ε`: `ε = 0` and `p ∤ 15`, or `ε = 1` and `p = 5`. -/
def Eps (p ε : ℕ) : Prop := (ε = 0 ∧ ¬ p ∣ 15) ∨ (ε = 1 ∧ p = 5)

omit hp in
lemma Eps.le_one {ε : ℕ} (h : Eps p ε) : ε ≤ 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

lemma sg2 (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) : D p s (sg p (p ^ s) 2) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hp3 : ¬ p ∣ 3 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h := sg_scale hp2 hs 2
  exact D.ucancel hp3 (h.congr (by push_cast; ring))

lemma sg4 (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) :
    D p s ((p : ℚ) ^ ε * sg p (p ^ s) 4) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hp3 : ¬ p ∣ 3 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h := sg_scale hp2 hs 4
  rcases hε with ⟨rfl, h15⟩ | ⟨rfl, h55⟩
  · have h6 : D p s (sg p (p ^ s) 4) := D.ucancel h15 (h.congr (by push_cast; ring))
    exact h6.congr (by ring)
  · have h6 : D p s (((3 : ℕ) : ℚ) * ((p : ℚ) ^ 1 * sg p (p ^ s) 4)) := by
      refine h.congr ?_
      rw [h55]
      push_cast
      ring
    exact D.ucancel hp3 h6

lemma refl_sums {s : ℕ} (hs : 1 ≤ s) :
    D p (4 * s) (2 * sg p (p ^ s) 1 + (p : ℚ) ^ s * sg p (p ^ s) 2 +
      ((p : ℚ) ^ s) ^ 2 * sg p (p ^ s) 3 + ((p : ℚ) ^ s) ^ 3 * sg p (p ^ s) 4) ∧
    D p (2 * s) (2 * sg p (p ^ s) 3 + 3 * (p : ℚ) ^ s * sg p (p ^ s) 4) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hv : ∀ u ∈ U p (p ^ s), (-(((p ^ s - u : ℕ) : ℚ))) = (u : ℚ) + (-(p : ℚ) ^ s) ∧
      (-(((p ^ s - u : ℕ) : ℚ))) ≠ 0 ∧ D p 0 (-(((p ^ s - u : ℕ) : ℚ)))⁻¹ := by
    intro u hu
    obtain ⟨hlt, hnd⟩ := mem_U.mp hu
    have hw : ¬ p ∣ p ^ s - u := by
      intro hd
      have h1 : p ^ s - u + u = p ^ s := Nat.sub_add_cancel (le_of_lt hlt)
      have h2 : p ∣ p ^ s - u + u := by rw [h1]; exact hpq
      exact hnd ((Nat.dvd_add_right hd).mp h2)
    have hw0 : ((p ^ s - u : ℕ) : ℚ) ≠ 0 := by
      have h1 : p ^ s - u ≠ 0 := by omega
      exact_mod_cast h1
    refine ⟨?_, neg_ne_zero.mpr hw0, ?_⟩
    · rw [Nat.cast_sub (le_of_lt hlt)]
      push_cast
      ring
    · rw [inv_neg]
      exact (D.inv hw).neg
  obtain ⟨h1, _, h3⟩ :=
    shift_sums (-(p : ℚ) ^ s) (D.ppow s).neg (fun u => -(((p ^ s - u : ℕ) : ℚ))) hv
  have hr1 : ∑ u ∈ U p (p ^ s), (-(((p ^ s - u : ℕ) : ℚ)))⁻¹ = -sg p (p ^ s) 1 := by
    have h := sum_U_reflect hpq (fun w => (w : ℚ)⁻¹ ^ 1)
    simp only [sg]
    rw [h, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [inv_neg, pow_one]
  have hr3 : ∑ u ∈ U p (p ^ s), (-(((p ^ s - u : ℕ) : ℚ)))⁻¹ ^ 3 = -sg p (p ^ s) 3 := by
    have h := sum_U_reflect hpq (fun w => (w : ℚ)⁻¹ ^ 3)
    simp only [sg]
    rw [h, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [inv_neg]
    ring
  rw [hr1] at h1
  rw [hr3] at h3
  exact ⟨h1.neg.congr (by ring), h3.neg.congr (by ring)⟩

lemma sg3 (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) :
    D p s (sg p (p ^ s) 3) ∧ D p (2 * s) ((p : ℚ) ^ ε * sg p (p ^ s) 3) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨_, h3⟩ := refl_sums (p := p) hs
  have h4 := sg4 h5 hε hs
  have hσ4 : D p 0 (sg p (p ^ s) 4) := sg_D0 _ _
  constructor
  · have h6 : D p s (((2 : ℕ) : ℚ) * sg p (p ^ s) 3) := by
      have h7 := (h3.le (by omega : s ≤ 2 * s)).sub (D.three.mul0' ((D.ppow s).mul0 hσ4))
      exact h7.congr (by push_cast; ring)
    exact D.ucancel hp2 h6
  · have h6 : D p (2 * s) (((2 : ℕ) : ℚ) * ((p : ℚ) ^ ε * sg p (p ^ s) 3)) := by
      have h7 := (((D.ppow (p := p) ε).le (Nat.zero_le _)).mul0' h3).sub
        (D.three.mul0' (((D.ppow s).mul h4).le (by omega : 2 * s ≤ s + s)))
      exact h7.congr (by push_cast; ring)
    exact D.ucancel hp2 h6

lemma sg1 (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) :
    D p (4 * s) ((p : ℚ) ^ ε * (2 * sg p (p ^ s) 1 + (p : ℚ) ^ s * sg p (p ^ s) 2)) := by
  obtain ⟨h1, _⟩ := refl_sums (p := p) hs
  obtain ⟨_, h3⟩ := sg3 h5 hε hs
  have h4 := sg4 h5 hε hs
  have h7 := ((((D.ppow (p := p) ε).le (Nat.zero_le _)).mul0' h1).sub
    ((((D.ppow s).pow 2).mul h3).le (by omega : 4 * s ≤ s * 2 + 2 * s))).sub
    ((((D.ppow s).pow 3).mul h4).le (by omega : 4 * s ≤ s * 3 + s))
  exact h7.congr (by ring)

lemma trans_sums {s : ℕ} (hs : 1 ≤ s) (h : ℕ) :
    D p (4 * s) (∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ -
      (sg p (p ^ s) 1 - ((h : ℚ) * (p : ℚ) ^ s) * sg p (p ^ s) 2 +
        ((h : ℚ) * (p : ℚ) ^ s) ^ 2 * sg p (p ^ s) 3 -
        ((h : ℚ) * (p : ℚ) ^ s) ^ 3 * sg p (p ^ s) 4)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 2 -
      (sg p (p ^ s) 2 - 2 * ((h : ℚ) * (p : ℚ) ^ s) * sg p (p ^ s) 3)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 3 -
      (sg p (p ^ s) 3 - 3 * ((h : ℚ) * (p : ℚ) ^ s) * sg p (p ^ s) 4)) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  apply shift_sums ((h : ℚ) * (p : ℚ) ^ s) ((D.nat h).mul0' (D.ppow s))
    (fun u => ((h * p ^ s + u : ℕ) : ℚ))
  intro u hu
  obtain ⟨hlt, hnd⟩ := mem_U.mp hu
  have hw : ¬ p ∣ h * p ^ s + u :=
    fun hd => hnd ((Nat.dvd_add_right (dvd_mul_of_dvd_right hpq h)).mp hd)
  refine ⟨by push_cast; ring, ?_, D.inv hw⟩
  intro h0
  have h1 : h * p ^ s + u = 0 := by exact_mod_cast h0
  apply hw
  rw [h1]
  exact dvd_zero p

/-- `h_1(t q) = -(q t^2 / 2) H_2(q)` to precision `4s - ε` -/
lemma hs1_blocks (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) :
    D p (4 * s) ((p : ℚ) ^ ε *
      (2 * sg p (t * p ^ s) 1 + (p : ℚ) ^ s * (t : ℚ) ^ 2 * sg p (p ^ s) 2)) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have h1 := sg1 h5 hε hs
  obtain ⟨_, h3⟩ := sg3 h5 hε hs
  have h4 := sg4 h5 hε hs
  have hb : sg p (t * p ^ s) 1 =
      ∑ h ∈ Finset.range t, ∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ := by
    unfold sg
    rw [sum_U_blocks hpq]
    simp only [pow_one]
  rw [hb]
  clear hb
  induction t with
  | zero => exact (D.zero _).congr (by simp)
  | succ t ih =>
    obtain ⟨hT, _, _⟩ := trans_sums (p := p) hs t
    have hpe : D p 0 ((p : ℚ) ^ ε) := (D.ppow ε).le (Nat.zero_le _)
    have htq : D p s ((t : ℚ) * (p : ℚ) ^ s) := (D.nat t).mul0' (D.ppow s)
    have h7 := ih.add ((((D.two.mul0' (hpe.mul0' hT)).add h1).add
      (D.two.mul0' (((htq.pow 2).mul h3).le (by omega : 4 * s ≤ s * 2 + 2 * s)))).sub
      (D.two.mul0' (((htq.pow 3).mul h4).le (by omega : 4 * s ≤ s * 3 + s))))
    refine h7.congr ?_
    rw [Finset.sum_range_succ]
    push_cast
    ring

/-- `h_2(t q) = t H_2(q)` to precision `2s` -/
lemma hs2_blocks (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) :
    D p (2 * s) (sg p (t * p ^ s) 2 - (t : ℚ) * sg p (p ^ s) 2) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hε : Eps p (if p = 5 then 1 else 0) := by
    by_cases h : p = 5
    · right; simp [h]
    · left
      refine ⟨by simp [h], ?_⟩
      intro hd
      have h15 : (15 : ℕ) = 3 * 5 := by norm_num
      rw [h15] at hd
      rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
      · have := Nat.le_of_dvd (by norm_num) h1; omega
      · have := Nat.le_of_dvd (by norm_num) h1; omega
  obtain ⟨h3, _⟩ := sg3 h5 hε hs
  have hb : sg p (t * p ^ s) 2 =
      ∑ h ∈ Finset.range t, ∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 2 := by
    unfold sg
    rw [sum_U_blocks hpq]
  rw [hb]
  clear hb
  induction t with
  | zero => exact (D.zero _).congr (by simp)
  | succ t ih =>
    obtain ⟨_, hT, _⟩ := trans_sums (p := p) hs t
    have h7 := ih.add (hT.sub (D.two.mul0' (((D.nat t).mul0' ((D.ppow s).mul h3)).le
      (by omega : 2 * s ≤ s + s))))
    refine h7.congr ?_
    rw [Finset.sum_range_succ]
    push_cast
    ring

/-! ### the non-unit part: auxiliary sums -/

lemma exists_eps (h5 : 5 ≤ p) : ∃ ε, Eps p ε := by
  by_cases h : p = 5
  · exact ⟨1, Or.inr ⟨rfl, h⟩⟩
  · refine ⟨0, Or.inl ⟨rfl, ?_⟩⟩
    intro hd
    have h15 : (15 : ℕ) = 3 * 5 := by norm_num
    rw [h15] at hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
    · have := Nat.le_of_dvd (by norm_num) h1
      omega
    · have := Nat.le_of_dvd (by norm_num) h1
      omega

lemma sg1' (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) : D p (2 * s) (sg p (p ^ s) 1) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨ε, hε⟩ := exists_eps (p := p) h5
  have hε1 := hε.le_one
  have h1 := sg1 h5 hε hs
  have h2 : D p (4 * s - ε) (2 * sg p (p ^ s) 1 + (p : ℚ) ^ s * sg p (p ^ s) 2) := by
    apply D.cancel (c := ε)
    rw [show 4 * s - ε + ε = 4 * s by omega]
    exact h1
  have h6 : D p (2 * s) (((2 : ℕ) : ℚ) * sg p (p ^ s) 1) := by
    have h7 := (h2.le (by omega : 2 * s ≤ 4 * s - ε)).sub
      (((D.ppow s).mul (sg2 h5 hs)).le (by omega : 2 * s ≤ s + s))
    exact h7.congr (by push_cast; ring)
  exact D.ucancel hp2 h6
/-! ### Wolstenholme type sums below `t p^s` -/

lemma S1_D (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) : D p (2 * s) (sg p (t * p ^ s) 1) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨ε, hε⟩ := exists_eps (p := p) h5
  have hε1 := hε.le_one
  have h1 := hs1_blocks h5 hε hs t
  have h2 : D p (4 * s - ε)
      (2 * sg p (t * p ^ s) 1 + (p : ℚ) ^ s * (t : ℚ) ^ 2 * sg p (p ^ s) 2) := by
    apply D.cancel (c := ε)
    rw [show 4 * s - ε + ε = 4 * s by omega]
    exact h1
  have h6 : D p (2 * s) (((2 : ℕ) : ℚ) * sg p (t * p ^ s) 1) := by
    have h7 := (h2.le (by omega : 2 * s ≤ 4 * s - ε)).sub
      ((((D.ppow s).mul0 ((D.nat t).pow0 2)).mul (sg2 h5 hs)).le (by omega : 2 * s ≤ s + s))
    exact h7.congr (by push_cast; ring)
  exact D.ucancel hp2 h6

lemma S2_D (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) : D p s (sg p (t * p ^ s) 2) := by
  have h := (hs2_blocks h5 hs t).le (by omega : s ≤ 2 * s)
  exact (h.add ((D.nat t).mul0' (sg2 h5 hs))).congr (by ring)

/-- `∏_{0<i<t p^s, p ∤ i} (1 - A p^s / i) ≡ 1 mod p^(3s)` -/
lemma R_D (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (A t : ℕ) :
    D p (3 * s) (R p ((A : ℚ) * (p : ℚ) ^ s) (t * p ^ s) - 1) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨W, hW, hprod⟩ := prod_expand2 hp2 (U p (t * p ^ s)) (fun i => (A : ℚ) * ((i : ℚ)⁻¹))
    ((p : ℚ) ^ s) ((D.ppow s).le (Nat.zero_le _))
    (fun i hi => (D.nat A).mul0 (D.inv (mem_U.mp hi).2))
  have hR : R p ((A : ℚ) * (p : ℚ) ^ s) (t * p ^ s) =
      ∏ i ∈ U p (t * p ^ s), (1 - (p : ℚ) ^ s * ((A : ℚ) * ((i : ℚ)⁻¹))) := by
    unfold R
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [div_eq_mul_inv]; ring
  have h1 : ∑ i ∈ U p (t * p ^ s), (A : ℚ) * ((i : ℚ)⁻¹) = (A : ℚ) * sg p (t * p ^ s) 1 := by
    unfold sg; rw [Finset.mul_sum]; simp only [pow_one]
  have h2 : ∑ i ∈ U p (t * p ^ s), ((A : ℚ) * ((i : ℚ)⁻¹)) ^ 2 =
      (A : ℚ) ^ 2 * sg p (t * p ^ s) 2 := by
    unfold sg; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hR, hprod, h1, h2]
  have hS1 := S1_D h5 hs t
  have hS2 := S2_D h5 hs t
  have hi2 : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2
  have e1 : D p (3 * s) ((p : ℚ) ^ s * ((A : ℚ) * sg p (t * p ^ s) 1)) :=
    ((D.ppow s).mul ((D.nat A).mul0' hS1)).le (by omega)
  have e2 : D p (3 * s) (((p : ℚ) ^ s) ^ 2 *
      (((A : ℚ) * sg p (t * p ^ s) 1) ^ 2 - (A : ℚ) ^ 2 * sg p (t * p ^ s) 2)) := by
    have hin : D p s (((A : ℚ) * sg p (t * p ^ s) 1) ^ 2 - (A : ℚ) ^ 2 * sg p (t * p ^ s) 2) :=
      ((((D.nat A).mul0' hS1).pow 2).le (by omega)).sub (((D.nat A).pow0 2).mul0' hS2)
    exact (((D.ppow s).pow 2).mul hin).le (by omega)
  have e3 : D p (3 * s) (((p : ℚ) ^ s) ^ 3 * W) :=
    (((D.ppow s).pow 3).mul0 hW).le (by omega)
  exact ((e1.neg.add (e2.mul0 hi2)).add e3).congr (by ring)


/-! ### additions for A333473: integer units, integer tops -/

lemma D.zinv {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) : D p 0 ((u : ℚ)⁻¹) := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg u
  · subst hm
    have h : ¬ p ∣ m := fun h => hu (Int.natCast_dvd_natCast.mpr h)
    simpa using D.inv (p := p) h
  · subst hm
    have h : ¬ p ∣ m := fun h => hu ((Int.dvd_neg).mpr (Int.natCast_dvd_natCast.mpr h))
    have := (D.inv (p := p) h).neg
    push_cast
    rw [inv_neg]
    exact this

lemma D.zcancel {e : ℕ} {u : ℤ} {x : ℚ} (hu : ¬ (p : ℤ) ∣ u) (h : D p e ((u : ℚ) * x)) :
    D p e x := by
  have hu0 : (u : ℚ) ≠ 0 := by
    intro h0
    apply hu
    have : u = 0 := by exact_mod_cast h0
    rw [this]; exact dvd_zero _
  exact (h.mul0 (D.zinv hu)).congr (by field_simp)

/-- `R_D` with an integer `A`. -/
lemma R_Dz (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (A : ℤ) (t : ℕ) :
    D p (3 * s) (R p ((A : ℚ) * (p : ℚ) ^ s) (t * p ^ s) - 1) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨W, hW, hprod⟩ := prod_expand2 hp2 (U p (t * p ^ s)) (fun i => (A : ℚ) * ((i : ℚ)⁻¹))
    ((p : ℚ) ^ s) ((D.ppow s).le (Nat.zero_le _))
    (fun i hi => (D.int A).mul0 (D.inv (mem_U.mp hi).2))
  have hR : R p ((A : ℚ) * (p : ℚ) ^ s) (t * p ^ s) =
      ∏ i ∈ U p (t * p ^ s), (1 - (p : ℚ) ^ s * ((A : ℚ) * ((i : ℚ)⁻¹))) := by
    unfold R
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [div_eq_mul_inv]; ring
  have h1 : ∑ i ∈ U p (t * p ^ s), (A : ℚ) * ((i : ℚ)⁻¹) = (A : ℚ) * sg p (t * p ^ s) 1 := by
    unfold sg; rw [Finset.mul_sum]; simp only [pow_one]
  have h2 : ∑ i ∈ U p (t * p ^ s), ((A : ℚ) * ((i : ℚ)⁻¹)) ^ 2 =
      (A : ℚ) ^ 2 * sg p (t * p ^ s) 2 := by
    unfold sg; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hR, hprod, h1, h2]
  have hS1 := S1_D h5 hs t
  have hS2 := S2_D h5 hs t
  have hi2 : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2
  have e1 : D p (3 * s) ((p : ℚ) ^ s * ((A : ℚ) * sg p (t * p ^ s) 1)) :=
    ((D.ppow s).mul ((D.int A).mul0' hS1)).le (by omega)
  have e2 : D p (3 * s) (((p : ℚ) ^ s) ^ 2 *
      (((A : ℚ) * sg p (t * p ^ s) 1) ^ 2 - (A : ℚ) ^ 2 * sg p (t * p ^ s) 2)) := by
    have hin : D p s (((A : ℚ) * sg p (t * p ^ s) 1) ^ 2 - (A : ℚ) ^ 2 * sg p (t * p ^ s) 2) :=
      ((((D.int A).mul0' hS1).pow 2).le (by omega)).sub (((D.int A).pow0 2).mul0' hS2)
    exact (((D.ppow s).pow 2).mul hin).le (by omega)
  have e3 : D p (3 * s) (((p : ℚ) ^ s) ^ 3 * W) :=
    (((D.ppow s).pow 3).mul0 hW).le (by omega)
  exact ((e1.neg.add (e2.mul0 hi2)).add e3).congr (by ring)

lemma choose_step (x : ℤ) (k : ℕ) :
    Ring.choose x (k + 1) * ((k : ℤ) + 1) = Ring.choose x k * (x - k) := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose x (k + 1)
  have h0 := Ring.descPochhammer_eq_factorial_smul_choose x k
  rw [descPochhammer_succ_right, Polynomial.smeval_mul, h0] at h1
  simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast, pow_one,
    pow_zero, nsmul_eq_mul, Nat.factorial_succ, mul_one] at h1
  push_cast at h1
  have hf : ((k.factorial : ℕ) : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  apply mul_left_cancel₀ hf
  linear_combination -h1

lemma choose_mul_eqz (x : ℤ) (k : ℕ) :
    ((Ring.choose x (k + 1) : ℤ) : ℚ) * ((k : ℚ) + 1) = (x : ℚ) * (-1) ^ k * Gp x (k + 1) := by
  induction k with
  | zero => simp [Gp, Ring.choose_one_right]
  | succ k ih =>
    have h1 : ((Ring.choose x (k + 1 + 1) : ℤ) : ℚ) * ((k : ℚ) + 1 + 1) =
        ((Ring.choose x (k + 1) : ℤ) : ℚ) * ((x : ℚ) - ((k : ℚ) + 1)) := by
      have := congrArg (Int.cast : ℤ → ℚ) (choose_step x (k + 1))
      push_cast at this
      linear_combination this
    have hG : Gp x (k + 1 + 1) = Gp x (k + 1) * (1 - (x : ℚ) / ((k : ℚ) + 1)) := by
      unfold Gp
      rw [Finset.prod_range_succ]
      push_cast
      ring
    have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
    have h3 : (x : ℚ) * (-1) ^ (k + 1) * (Gp x (k + 1) * (1 - (x : ℚ) / ((k : ℚ) + 1))) =
        ((x : ℚ) * (-1) ^ k * Gp x (k + 1)) * (((x : ℚ) - ((k : ℚ) + 1)) / ((k : ℚ) + 1)) := by
      field_simp
      ring
    have h4 : (((Ring.choose x (k + 1) : ℤ) : ℚ) * ((k : ℚ) + 1)) *
        (((x : ℚ) - ((k : ℚ) + 1)) / ((k : ℚ) + 1)) =
        ((Ring.choose x (k + 1) : ℤ) : ℚ) * ((x : ℚ) - ((k : ℚ) + 1)) := by
      field_simp
    push_cast
    rw [hG, h3, ← ih, h4, ← h1]

lemma choose_mul_eqz' (x : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    ((Ring.choose x k : ℤ) : ℚ) * (k : ℚ) = -((x : ℚ) * (-1) ^ k * Gp x k) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := choose_mul_eqz x k'
  push_cast
  rw [h, pow_succ]
  ring

lemma choose_ratio_int (hp2 : p ≠ 2) (x : ℤ) (j : ℕ) :
    ((Ring.choose ((p : ℤ) * x) (p * j) : ℤ) : ℚ) =
      ((Ring.choose x j : ℤ) : ℚ) * R p ((p : ℚ) * (x : ℚ)) (p * j) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [R, U, Ring.choose_zero_right]
  have hp0 : 0 < p := hp.out.pos
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have h1 := choose_mul_eqz' ((p : ℤ) * x) (p * j) (by nlinarith)
  have h2 := choose_mul_eqz' x j hj
  have h3 := Gp_split hp0 ((p : ℚ) * (x : ℚ)) j
  have h4 : (p : ℚ) * (x : ℚ) / (p : ℚ) = (x : ℚ) := by
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
    field_simp
  have h5 : (-1 : ℚ) ^ (p * j) = (-1) ^ j := by
    rw [pow_mul, hodd.neg_one_pow]
  have hc : (((p : ℤ) * x : ℤ) : ℚ) = (p : ℚ) * (x : ℚ) := by push_cast; ring
  rw [hc, h3, h4, h5] at h1
  have hpj : ((p * j : ℕ) : ℚ) ≠ 0 := by
    have : 0 < p * j := Nat.mul_pos hp0 hj
    positivity
  apply mul_right_cancel₀ hpj
  rw [h1, Nat.cast_mul]
  have h6 : (x : ℚ) * (-1) ^ j * Gp x j = -(((Ring.choose x j : ℤ) : ℚ) * (j : ℚ)) := by rw [h2]; ring
  linear_combination (-(p : ℚ) * R p ((p : ℚ) * (x : ℚ)) (p * j)) * h6

lemma choose_neg_one (k : ℕ) : Ring.choose (-1 : ℤ) k = (-1) ^ k := by
  induction k with
  | zero => simp [Ring.choose_zero_right]
  | succ k ih =>
    have h := choose_step (-1) k
    rw [ih] at h
    have hk : ((k : ℤ) + 1) ≠ 0 := by positivity
    apply mul_right_cancel₀ hk
    rw [h, pow_succ]; ring

end LtsJacobsthal

namespace A333473P
open Finset LtsJacobsthal LtsLagrange

lemma bb_negtwo (k : ℕ) : bb (-(2 * ((k : ℤ) + 1))) (k + 1) = -2 * (-1) ^ k := by
  simp only [bb]
  rw [show 2 * (k : ℤ) + -(2 * ((k : ℤ) + 1)) + 1 = -1 by ring, choose_neg_one, choose_neg_one]
  ring

lemma bbM (Q : ℤ) (j : ℕ) : bb Q j * (Q + 2 * j) = Q * Ring.choose (Q + 2 * j) j := by
  rcases j with _ | k
  · simp [bb, Ring.choose_zero_right]
  · simp only [bb]
    have hs := choose_step (2 * (k : ℤ) + Q + 1) k
    have hp := Ring.choose_succ_succ (2 * (k : ℤ) + Q + 1) k
    rw [show Q + 2 * ((k + 1 : ℕ) : ℤ) = 2 * (k : ℤ) + Q + 1 + 1 by push_cast; ring, hp]
    apply mul_left_cancel₀ (show ((k : ℤ) + 1) ≠ 0 by positivity)
    push_cast at hs ⊢
    linear_combination (2 * ((k : ℤ) + 1)) * hs

lemma Tid (Q : ℤ) (N j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) :
    bb Q j * Ring.choose (Q + j) (N - j) * (Q + 2 * j) * j =
      Q * N * (((N - 1).choose (j - 1) : ℤ) * Ring.choose (Q + 2 * j) N) := by
  have h1 := bbM Q j
  have h2 := Ring.choose_smul_choose (Q + 2 * (j : ℤ)) hjN
  rw [nsmul_eq_mul, show Q + 2 * (j : ℤ) - j = Q + j by ring] at h2
  have h4 : ((N.choose j : ℕ) : ℤ) * j = N * ((N - 1).choose (j - 1) : ℤ) := by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have := Nat.add_one_mul_choose_eq n i
    simp only [Nat.add_sub_cancel]
    exact_mod_cast this.symm
  linear_combination (Ring.choose (Q + j) (N - j) * j) * h1 - (Q * j) * h2 +
    (Q * Ring.choose (Q + 2 * j) N) * h4

variable {p : ℕ} [hp : Fact p.Prime]

lemma not_dvd_add (h5 : 5 ≤ p) {a : ℤ} {u : ℕ} (ha : (p : ℤ) ∣ a) (hu : ¬ p ∣ u) :
    ¬ (p : ℤ) ∣ a + 2 * u := by
  intro h
  have h2 : (p : ℤ) ∣ ((2 * u : ℕ) : ℤ) := by
    have := (dvd_add_right ha).mp h
    push_cast; exact this
  rw [Int.natCast_dvd_natCast] at h2
  rcases (Nat.Prime.dvd_mul hp.out).mp h2 with h | h
  · have := Nat.le_of_dvd (by norm_num) h; omega
  · exact hu h

lemma lay (Q : ℤ) (N j g j1 N1 : ℕ) (Q1 : ℤ) (c1 c2 : ℕ) (hg : 1 ≤ g) (hN : N = g * N1)
    (hQ : Q = g * Q1) (hj : j = g * j1) (hj1 : ¬ p ∣ j1) (hM : ¬ (p : ℤ) ∣ Q1 + 2 * j1)
    (hjN : j ≤ N) (hQ1 : D p c1 (Q1 : ℚ)) (hN1 : D p c2 (N1 : ℚ)) :
    D p (c1 + c2) ((bb Q j * Ring.choose (Q + j) (N - j) : ℤ) : ℚ) := by
  have hj10 : 1 ≤ j1 := by
    rcases Nat.eq_zero_or_pos j1 with h | h
    · exact absurd (h ▸ dvd_zero p) hj1
    · exact h
  have hj0 : 1 ≤ j := by rw [hj]; exact Nat.mul_pos hg hj10
  have h := Tid Q N j hj0 hjN
  set X := bb Q j * Ring.choose (Q + j) (N - j) with hX
  set Y := (((N - 1).choose (j - 1) : ℕ) : ℤ) * Ring.choose (Q + 2 * j) N with hY
  clear_value X Y
  subst hN hQ hj
  have hq : (X : ℚ) * ((g : ℚ) * Q1 + 2 * ((g : ℚ) * j1)) * ((g : ℚ) * j1) =
      (g : ℚ) * Q1 * ((g : ℚ) * N1) * (Y : ℚ) := by
    have := congrArg (Int.cast : ℤ → ℚ) h
    push_cast at this
    linear_combination this
  have hg0 : (g : ℚ) ≠ 0 := by
    have : (1 : ℚ) ≤ g := by exact_mod_cast hg
    linarith
  have key : (((Q1 + 2 * j1 : ℤ)) : ℚ) * ((j1 : ℚ) * X) = (Q1 : ℚ) * N1 * Y := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hg0)
    push_cast
    linear_combination hq
  have hR : D p (c1 + c2) ((((Q1 + 2 * j1 : ℤ)) : ℚ) * ((j1 : ℚ) * X)) := by
    rw [key]; exact (hQ1.mul hN1).mul0 (D.int Y)
  exact D.ucancel hj1 (D.zcancel hM hR)

lemma bb_ratio (hp2 : p ≠ 2) (Q0 : ℤ) (J : ℕ) :
    ((bb ((p : ℤ) * Q0) (p * J) : ℤ) : ℚ) =
      ((bb Q0 J : ℤ) : ℚ) * R p ((p : ℚ) * ((Q0 + 2 * J : ℤ) : ℚ)) (p * J) := by
  have hp0 : 0 < p := hp.out.pos
  by_cases hM : Q0 + 2 * J = 0
  · rw [hM]
    have hR1 : ∀ L, R p ((p : ℚ) * ((0 : ℤ) : ℚ)) L = 1 := by
      intro L; simp [R]
    rw [hR1, mul_one]
    rcases J with _ | k
    · simp [bb]
    · have hQ0 : Q0 = -(2 * ((k : ℤ) + 1)) := by push_cast at hM; linarith
      obtain ⟨m, hm⟩ : ∃ m, p * (k + 1) = m + 1 := ⟨p * (k + 1) - 1, by
        have : 1 ≤ p * (k + 1) := Nat.mul_pos hp0 (Nat.succ_pos k)
        omega⟩
      have hQ : (p : ℤ) * Q0 = -(2 * ((m : ℤ) + 1)) := by
        rw [hQ0]
        have : ((p * (k + 1) : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) := by rw [hm]
        push_cast at this
        linear_combination (-2) * this
      rw [hm, hQ, bb_negtwo, hQ0, bb_negtwo]
      have hodd : Odd p := hp.out.odd_of_ne_two hp2
      have e : ((-1 : ℤ)) ^ (m + 1) = (-1) ^ (k + 1) := by
        rw [← hm, pow_mul, hodd.neg_one_pow]
      have e2 : ((-1 : ℤ)) ^ m = (-1) ^ k := by
        rw [pow_succ, pow_succ] at e
        linarith
      rw [e2]
  · have h1 := bbM ((p : ℤ) * Q0) (p * J)
    have h0 := bbM Q0 J
    have hr := choose_ratio_int hp2 (Q0 + 2 * J) J
    have e1 : (p : ℤ) * Q0 + 2 * ((p * J : ℕ) : ℤ) = (p : ℤ) * (Q0 + 2 * J) := by push_cast; ring
    rw [e1] at h1
    have h1q := congrArg (Int.cast : ℤ → ℚ) h1
    have h0q := congrArg (Int.cast : ℤ → ℚ) h0
    simp only [Int.cast_mul, Int.cast_natCast] at h1q h0q
    rw [hr] at h1q
    have hMq : ((Q0 + 2 * J : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hM
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
    apply mul_right_cancel₀ (mul_ne_zero hpq hMq)
    linear_combination h1q - ((p : ℚ) * R p ((p : ℚ) * ((Q0 + 2 * J : ℤ) : ℚ)) (p * J)) * h0q

lemma T_ratio (hp2 : p ≠ 2) (Q0 : ℤ) (N0 J : ℕ) (hJ : J ≤ N0) :
    ((bb ((p : ℤ) * Q0) (p * J) * Ring.choose ((p : ℤ) * Q0 + ((p * J : ℕ) : ℤ)) (p * N0 - p * J)
      : ℤ) : ℚ) =
      ((bb Q0 J * Ring.choose (Q0 + J) (N0 - J) : ℤ) : ℚ) *
        R p ((p : ℚ) * ((Q0 + 2 * J : ℤ) : ℚ)) (p * J) *
        R p ((p : ℚ) * ((Q0 + J : ℤ) : ℚ)) (p * (N0 - J)) := by
  obtain ⟨d, rfl⟩ : ∃ d, N0 = J + d := ⟨N0 - J, by omega⟩
  have e1 : p * (J + d) - p * J = p * d := by rw [mul_add, Nat.add_sub_cancel_left]
  have e2 : (p : ℤ) * Q0 + ((p * J : ℕ) : ℤ) = (p : ℤ) * (Q0 + J) := by push_cast; ring
  have e3 : J + d - J = d := by omega
  rw [e1, e2, e3, Int.cast_mul, Int.cast_mul, bb_ratio hp2, choose_ratio_int hp2]
  ring

lemma sum_split (f : ℕ → ℤ) (N0 : ℕ) (hp0 : 0 < p) :
    ∑ j ∈ range (p * N0 + 1), f j =
      ∑ j ∈ (range (p * N0 + 1)).filter (fun j => ¬ p ∣ j), f j +
        ∑ J ∈ range (N0 + 1), f (p * J) := by
  rw [← Finset.sum_filter_add_sum_filter_not (range (p * N0 + 1)) (fun j => p ∣ j), add_comm]
  congr 1
  symm
  apply Finset.sum_nbij (fun J => p * J)
  · intro J hJ
    simp only [mem_filter, mem_range] at hJ ⊢
    refine ⟨?_, dvd_mul_right p J⟩
    nlinarith
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hp0 h
  · intro j hj
    simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hj
    obtain ⟨hj1, J, rfl⟩ := hj
    refine ⟨J, ?_, rfl⟩
    simp only [coe_range, Set.mem_Iio]
    by_contra hc
    have : p * (N0 + 1) ≤ p * J := Nat.mul_le_mul_left p (by omega)
    nlinarith
  · intro J _; rfl

lemma combine {c0 ca e : ℕ} {T0 Ra Rb : ℚ} (h : e ≤ c0 + ca) (hT : D p c0 T0)
    (ha : D p ca (Ra - 1)) (hb : D p ca (Rb - 1)) : D p e (T0 * Ra * Rb - T0) := by
  have hb0 : D p 0 Rb := ((hb.le (Nat.zero_le _)).add D.one).congr (by ring)
  exact ((hT.mul ((ha.mul0 hb0).add hb)).le h).congr (by ring)

lemma pair_term (h5 : 5 ≤ p) (E R : ℕ) (S : ℤ) (J : ℕ) (hJ : J ≤ R * p ^ E) :
    D p (2 * (E + 1))
      (((bb ((p : ℤ) * (S * (p : ℤ) ^ E)) (p * J) *
        Ring.choose ((p : ℤ) * (S * (p : ℤ) ^ E) + ((p * J : ℕ) : ℤ)) (p * (R * p ^ E) - p * J)
          : ℤ) : ℚ) -
        ((bb (S * (p : ℤ) ^ E) J * Ring.choose (S * (p : ℤ) ^ E + J) (R * p ^ E - J) : ℤ) : ℚ)) := by
  have hp2 : p ≠ 2 := by omega
  have hp0 : 0 < p := hp.out.pos
  rw [T_ratio hp2 _ _ _ hJ]
  by_cases hdiv : p ^ E ∣ J
  · obtain ⟨t, rfl⟩ := hdiv
    have htR : t ≤ R := by
      have : p ^ E * t ≤ p ^ E * R := by rw [mul_comm (p ^ E) R]; exact hJ
      exact Nat.le_of_mul_le_mul_left this (pow_pos hp0 E)
    apply combine (c0 := 0) (ca := 3 * (E + 1)) (by omega) (D.int _)
    · have h := R_Dz h5 (s := E + 1) (by omega) (S + 2 * t) t
      have ex1 : (p : ℚ) * ((S * (p : ℤ) ^ E + 2 * ((p ^ E * t : ℕ) : ℤ) : ℤ) : ℚ) =
          ((S + 2 * t : ℤ) : ℚ) * (p : ℚ) ^ (E + 1) := by push_cast; ring
      have ex2 : p * (p ^ E * t) = t * p ^ (E + 1) := by ring
      rw [ex1, ex2]; exact h
    · have h := R_Dz h5 (s := E + 1) (by omega) (S + t) (R - t)
      have ex1 : (p : ℚ) * ((S * (p : ℤ) ^ E + ((p ^ E * t : ℕ) : ℤ) : ℤ) : ℚ) =
          ((S + t : ℤ) : ℚ) * (p : ℚ) ^ (E + 1) := by push_cast; ring
      have ex2 : p * (R * p ^ E - p ^ E * t) = (R - t) * p ^ (E + 1) := by
        rw [mul_comm (p ^ E) t, ← Nat.sub_mul]; ring
      rw [ex1, ex2]; exact h
  · have hJ0 : J ≠ 0 := by
      intro h0; apply hdiv; rw [h0]; exact dvd_zero _
    obtain ⟨β, u, hu, hJu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hJ0 p (by omega)
    have hβ : β < E := by
      by_contra hc
      apply hdiv
      rw [hJu]
      exact Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) u
    obtain ⟨c, hc⟩ : ∃ c, E = β + c + 1 := ⟨E - β - 1, by omega⟩
    subst hc
    have hT0 : D p ((c + 1) + (c + 1))
        ((bb (S * (p : ℤ) ^ (β + c + 1)) J *
          Ring.choose (S * (p : ℤ) ^ (β + c + 1) + J) (R * p ^ (β + c + 1) - J) : ℤ) : ℚ) := by
      refine lay _ _ _ (p ^ β) u (R * p ^ (c + 1)) (S * (p : ℤ) ^ (c + 1)) (c + 1) (c + 1)
        (Nat.one_le_pow _ _ hp0) (by ring) (by push_cast; ring) hJu hu ?_ hJ ?_ ?_
      · exact not_dvd_add h5 (Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _) hu
      · exact ((D.int S).mul0' (D.ppow (p := p) (c + 1))).congr (by push_cast; ring)
      · exact ((D.nat R).mul0' (D.ppow (p := p) (c + 1))).congr (by push_cast; ring)
    apply combine (c0 := (c + 1) + (c + 1)) (ca := 3 * (β + 1)) (by omega) hT0
    · have h := R_Dz h5 (s := β + 1) (by omega) (S * (p : ℤ) ^ (c + 1) + 2 * u) u
      have ex1 : (p : ℚ) * ((S * (p : ℤ) ^ (β + c + 1) + 2 * (J : ℤ) : ℤ) : ℚ) =
          ((S * (p : ℤ) ^ (c + 1) + 2 * u : ℤ) : ℚ) * (p : ℚ) ^ (β + 1) := by
        rw [hJu]; push_cast; ring
      have ex2 : p * J = u * p ^ (β + 1) := by rw [hJu]; ring
      rw [ex1, ex2]; exact h
    · have h := R_Dz h5 (s := β + 1) (by omega) (S * (p : ℤ) ^ (c + 1) + u) (R * p ^ (c + 1) - u)
      have ex1 : (p : ℚ) * ((S * (p : ℤ) ^ (β + c + 1) + (J : ℤ) : ℤ) : ℚ) =
          ((S * (p : ℤ) ^ (c + 1) + u : ℤ) : ℚ) * (p : ℚ) ^ (β + 1) := by
        rw [hJu]; push_cast; ring
      have ex2 : p * (R * p ^ (β + c + 1) - J) = (R * p ^ (c + 1) - u) * p ^ (β + 1) := by
        rw [hJu, Nat.sub_mul, Nat.mul_sub]
        congr 1 <;> ring
      rw [ex1, ex2]; exact h

lemma core (h5 : 5 ≤ p) (E R : ℕ) (S : ℤ) :
    (p : ℤ) ^ (2 * (E + 1)) ∣
      gq ((p : ℤ) * (S * (p : ℤ) ^ E)) (p * (R * p ^ E)) - gq (S * (p : ℤ) ^ E) (R * p ^ E) := by
  have hp0 : 0 < p := hp.out.pos
  unfold gq
  rw [sum_split _ (R * p ^ E) hp0]
  apply D.dvd
  have hU : D p (2 * (E + 1)) (∑ j ∈ (range (p * (R * p ^ E) + 1)).filter (fun j => ¬ p ∣ j),
      ((bb ((p : ℤ) * (S * (p : ℤ) ^ E)) j *
        Ring.choose ((p : ℤ) * (S * (p : ℤ) ^ E) + j) (p * (R * p ^ E) - j) : ℤ) : ℚ)) := by
    apply D.sum
    intro j hj
    simp only [mem_filter, mem_range] at hj
    refine (lay _ _ _ 1 j (p * (R * p ^ E)) ((p : ℤ) * (S * (p : ℤ) ^ E)) (E + 1) (E + 1)
      le_rfl (by ring) (by push_cast; ring) (by ring) hj.2
      (not_dvd_add h5 (dvd_mul_right _ _) hj.2) (by omega) ?_ ?_).le (by omega)
    · exact ((D.int S).mul0' (D.ppow (p := p) (E + 1))).congr (by push_cast; ring)
    · exact ((D.nat R).mul0' (D.ppow (p := p) (E + 1))).congr (by push_cast; ring)
  have hP : D p (2 * (E + 1)) (∑ J ∈ range (R * p ^ E + 1),
      ((((bb ((p : ℤ) * (S * (p : ℤ) ^ E)) (p * J) *
        Ring.choose ((p : ℤ) * (S * (p : ℤ) ^ E) + ((p * J : ℕ) : ℤ)) (p * (R * p ^ E) - p * J)
          : ℤ) : ℚ) -
        ((bb (S * (p : ℤ) ^ E) J * Ring.choose (S * (p : ℤ) ^ E + J) (R * p ^ E - J) : ℤ) : ℚ)))) := by
    apply D.sum
    intro J hJ
    simp only [mem_range] at hJ
    exact pair_term h5 E R S J (by omega)
  refine (hU.add hP).congr ?_
  rw [Finset.sum_sub_distrib]
  push_cast
  ring

end A333473P


namespace A333473Final
open OMA.S_oeis_a333473

theorem final :
    (∀ p n k : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < k →
      ((p : ℤ) ^ (2 * k)) ∣ (a (n * p ^ k) - a (n * p ^ (k - 1)))) ∧
    (∀ (r : ℕ) (s : ℤ) (p n k : ℕ), 0 < r → p.Prime → 5 ≤ p → 0 < n → 0 < k →
      ((p : ℤ) ^ (2 * k)) ∣ (ars r s (n * p ^ k) - ars r s (n * p ^ (k - 1)))) := by
  have hars : ∀ (r : ℕ) (s : ℤ) (p n k : ℕ), 0 < r → p.Prime → 5 ≤ p → 0 < n → 0 < k →
      ((p : ℤ) ^ (2 * k)) ∣ (ars r s (n * p ^ k) - ars r s (n * p ^ (k - 1))) := by
    intro r s p n k hr hp h5 hn hk
    haveI := Fact.mk hp
    obtain ⟨E, rfl⟩ : ∃ E, k = E + 1 := ⟨k - 1, by omega⟩
    simp only [ars, LtsLagrange.coeff_Fpow, Nat.add_sub_cancel]
    have e1 : r * (n * p ^ (E + 1)) = p * (r * n * p ^ E) := by ring
    have e2 : s * ((n * p ^ (E + 1) : ℕ) : ℤ) = (p : ℤ) * (s * n * (p : ℤ) ^ E) := by
      push_cast; ring
    have e3 : r * (n * p ^ E) = r * n * p ^ E := by ring
    have e4 : s * ((n * p ^ E : ℕ) : ℤ) = s * n * (p : ℤ) ^ E := by push_cast; ring
    rw [e1, e2, e3, e4]
    exact A333473P.core h5 E (r * n) (s * n)
  refine ⟨?_, hars⟩
  intro p n k hp h5 hn hk
  have ha : ∀ m, a m = ars 1 1 m := by intro m; simp [a, ars, Fpow]
  rw [ha, ha]
  exact hars 1 1 p n k one_pos hp h5 hn hk

end A333473Final

theorem OMA.solution : type_of% @OMA.S_oeis_a333473.main := A333473Final.final
