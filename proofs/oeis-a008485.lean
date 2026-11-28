import OMAStatements.S_oeis_a008485
import Mathlib

/-!
# Proof of OEIS A008485, supercongruence a(p) == p + 1 (mod p^2), p >= 3 (Peter Bala, Apr 18 2023)

The statement defines `a(n) = [x^n] ((Product_{k=1..n} (1 - x^k))^(-1))^n` in `Q[[x]]` and asks for an
integer `m` with `a(p) - (p + 1) = p^2 * m`.

The proof works with the integer series: `aZ(n) = [x^n] Product_{k=1..n} (1/(1 - x^k))^n` in `Z[[x]]`,
where `1/(1 - x^k)` is `PowerSeries.invOfUnit (1 - x^k) 1`. Steps 1 to 5 prove `p^2 | aZ(p) - (p + 1)`;
step 6 is the bridge `a(n) = aZ(n)`.

Work in `(ZMod (p^2))[[x]]`. Call `F` *good for* `c` if `F` agrees in degrees `<= p` with
`1 + c x^p + p Q` for some `Q` with `Q(0) = 0` and `[x^p] Q = 0`.

1. Good series multiply: good for `c1` times good for `c2` is good for `c1 + c2`
   (`x^p x^p` and `x^p Q` vanish in degrees `<= p`, and `p * p = 0`).
2. `(1 + t)^p = 1 + t^p + p S(t)`, `S(t) = sum_{j=1..p-1} (C(p,j)/p) t^j`.
3. `(1 - x)^p` is good for `-1` (`p` odd), `(1 - x^p)^p` is good for `-p`, and `(1 - x^k)^p` is good
   for `0` when `2 <= k <= p - 1` (`k` does not divide `p`). So `P = prod_{k=1..p} (1 - x^k)^p` is good
   for `-(1 + p)`.
4. If `F` is good for `c` and `F G = 1` then `[x^p] G = -c`: with `G' = 1 - c x^p - p Q` the product
   `F G'` agrees with `1` in degrees `<= p`, so `[x^p] G = [x^p] (G (F G')) = [x^p] G' = -c`.
5. In `Z[[x]]`, `P` times `prod_{k=1..p} (1/(1 - x^k))^p` is `1`; map this to `ZMod (p^2)`.
6. Bridge. Let `A = prod_{k=1..n} (1 - x^k)` in `Q[[x]]` and let `G` be the integer series
   `prod_{k=1..n} (1/(1 - x^k))^n`. The identity of step 5 maps to `A^n * map G = 1` in `Q[[x]]`.
   Since `A(0) = 1` is not zero, `A⁻¹ * A = 1`, hence `(A⁻¹)^n = (A⁻¹)^n * (A^n * map G) = map G`.
   Taking the coefficient of `x^n` gives `a(n) = aZ(n)` as rational numbers.
-/

namespace A008485Proof

/-- Equality of coefficients in degrees `<= p` is compatible with products. -/
private lemma coeff_mul_congr {R : Type*} [CommRing R] {p : ℕ} {A B C D : PowerSeries R}
    (hAB : ∀ d ≤ p, PowerSeries.coeff d A = PowerSeries.coeff d B)
    (hCD : ∀ d ≤ p, PowerSeries.coeff d C = PowerSeries.coeff d D) :
    ∀ d ≤ p, PowerSeries.coeff d (A * C) = PowerSeries.coeff d (B * D) := by
  intro d hd
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [hAB x.1 (by omega), hCD x.2 (by omega)]

private lemma coeff_X_pow_mul_low {R : Type*} [CommRing R] {p d : ℕ} (hd : d ≤ p)
    (Q : PowerSeries R) (hQ0 : PowerSeries.constantCoeff Q = 0) :
    PowerSeries.coeff d (PowerSeries.X ^ p * Q) = 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · have h0 : d - p = 0 := by omega
    rw [h0, PowerSeries.coeff_zero_eq_constantCoeff_apply, hQ0]
  · rfl

private lemma coeff_X_pow_sq_low {R : Type*} [CommRing R] {p d : ℕ} (hp : 0 < p) (hd : d ≤ p) :
    PowerSeries.coeff d ((PowerSeries.X : PowerSeries R) ^ p * PowerSeries.X ^ p) = 0 := by
  rw [← pow_add, PowerSeries.coeff_X_pow, if_neg (by omega)]

/-- `Good π p F c`: in degrees `<= p`, `F` agrees with `1 + c x^p + π Q`, where `Q(0) = 0` and
`[x^p] Q = 0`. -/
private def Good {R : Type*} [CommRing R] (π : R) (p : ℕ) (F : PowerSeries R) (c : R) : Prop :=
  ∃ Q : PowerSeries R,
    PowerSeries.constantCoeff Q = 0 ∧
    PowerSeries.coeff p Q = 0 ∧
    ∀ d ≤ p, PowerSeries.coeff d F =
      PowerSeries.coeff d (1 + PowerSeries.C c * PowerSeries.X ^ p + PowerSeries.C π * Q)

private lemma Good.mul {R : Type*} [CommRing R] {π : R} {p : ℕ} (hπ : π * π = 0) (hp : 0 < p)
    {F G : PowerSeries R} {c1 c2 : R} (hF : Good π p F c1) (hG : Good π p G c2) :
    Good π p (F * G) (c1 + c2) := by
  obtain ⟨Q1, hQ10, hQ1p, hFeq⟩ := hF
  obtain ⟨Q2, hQ20, hQ2p, hGeq⟩ := hG
  refine ⟨Q1 + Q2, by simp [hQ10, hQ20], by simp [hQ1p, hQ2p], fun d hd => ?_⟩
  rw [coeff_mul_congr hFeq hGeq d hd]
  have hexp : (1 + PowerSeries.C c1 * PowerSeries.X ^ p + PowerSeries.C π * Q1) *
      (1 + PowerSeries.C c2 * PowerSeries.X ^ p + PowerSeries.C π * Q2) =
      (1 + PowerSeries.C (c1 + c2) * PowerSeries.X ^ p + PowerSeries.C π * (Q1 + Q2)) +
      PowerSeries.C (c1 * c2) * (PowerSeries.X ^ p * PowerSeries.X ^ p) +
      (PowerSeries.C (c1 * π) * (PowerSeries.X ^ p * Q2) +
        PowerSeries.C (c2 * π) * (PowerSeries.X ^ p * Q1)) +
      PowerSeries.C (π * π) * (Q1 * Q2) := by
    simp only [map_mul, map_add]; ring
  rw [hexp, hπ, map_zero, zero_mul, add_zero]
  simp only [map_add, PowerSeries.coeff_C_mul, coeff_X_pow_sq_low hp hd,
    coeff_X_pow_mul_low hd Q2 hQ20, coeff_X_pow_mul_low hd Q1 hQ10]
  ring

private lemma Good.prod_zero {R : Type*} [CommRing R] {π : R} {p : ℕ} (hπ : π * π = 0) (hp : 0 < p)
    {ι : Type*} (s : Finset ι) (f : ι → PowerSeries R) (hf : ∀ i ∈ s, Good π p (f i) 0) :
    Good π p (∏ i ∈ s, f i) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp, fun _ _ => by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h := (hf a (Finset.mem_insert_self a s)).mul hπ hp
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rwa [add_zero] at h

/-- If `F` is good for `c` and `F * G = 1`, then `[x^p] G = -c`. -/
private lemma Good.coeff_inv {R : Type*} [CommRing R] {π : R} {p : ℕ} (hπ : π * π = 0) (hp : 0 < p)
    {F G : PowerSeries R} {c : R} (hF : Good π p F c) (hFG : F * G = 1) :
    PowerSeries.coeff p G = -c := by
  obtain ⟨Q, hQ0, hQp, hFeq⟩ := hF
  have h1 : ∀ d ≤ p, PowerSeries.coeff d
      (F * (1 + PowerSeries.C (-c) * PowerSeries.X ^ p + PowerSeries.C π * (-Q))) =
      PowerSeries.coeff d (1 : PowerSeries R) := by
    intro d hd
    rw [coeff_mul_congr hFeq (fun _ _ => rfl) d hd]
    have hexp : (1 + PowerSeries.C c * PowerSeries.X ^ p + PowerSeries.C π * Q) *
        (1 + PowerSeries.C (-c) * PowerSeries.X ^ p + PowerSeries.C π * (-Q)) =
        1 - PowerSeries.C (c * c) * (PowerSeries.X ^ p * PowerSeries.X ^ p) -
          PowerSeries.C (c * π + c * π) * (PowerSeries.X ^ p * Q) -
          PowerSeries.C (π * π) * (Q * Q) := by
      simp only [map_mul, map_add, map_neg]; ring
    rw [hexp, hπ, map_zero, zero_mul, sub_zero]
    simp only [map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_sq_low hp hd,
      coeff_X_pow_mul_low hd Q hQ0, mul_zero, sub_zero]
  have h2 := coeff_mul_congr (A := G) (B := G) (fun _ _ => rfl) (fun d hd => (h1 d hd).symm) p le_rfl
  rw [mul_one, ← mul_assoc, mul_comm G F, hFG, one_mul] at h2
  rw [h2, map_add, map_add, PowerSeries.coeff_one, if_neg hp.ne', PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow, if_pos rfl, PowerSeries.coeff_C_mul, map_neg, hQp]
  ring

/-- `S p t = sum_{j=1..p-1} (C(p,j)/p) t^j`, so that `(1 + t)^p = 1 + t^p + p * S p t` for prime `p`. -/
private noncomputable def S {R : Type*} [CommRing R] (p : ℕ) (t : PowerSeries R) : PowerSeries R :=
  ∑ j ∈ Finset.range (p - 1), PowerSeries.C (((p.choose (j + 1) / p : ℕ) : R)) * t ^ (j + 1)

private lemma one_add_pow_prime {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime) (t : PowerSeries R) :
    (1 + t) ^ p = 1 + t ^ p + PowerSeries.C ((p : ℕ) : R) * S p t := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have key : ∀ m ∈ Finset.range q,
      t ^ (m + 1) * 1 ^ (q + 1 - (m + 1)) * (((q + 1).choose (m + 1) : ℕ) : PowerSeries R) =
        PowerSeries.C ((q + 1 : ℕ) : R) *
          (PowerSeries.C ((((q + 1).choose (m + 1) / (q + 1) : ℕ)) : R) * t ^ (m + 1)) := by
    intro m hm
    have hm' := Finset.mem_range.mp hm
    obtain ⟨e, he⟩ : (q + 1) ∣ (q + 1).choose (m + 1) := hp.dvd_choose_self (by omega) (by omega)
    have hc : (((q + 1) * e : ℕ) : PowerSeries R) =
        PowerSeries.C ((q + 1 : ℕ) : R) * PowerSeries.C ((e : ℕ) : R) := by
      rw [← map_mul, ← Nat.cast_mul, map_natCast]
    rw [he, Nat.mul_div_cancel_left e hp.pos, one_pow, mul_one, hc]
    ring
  rw [add_comm 1 t, add_pow, Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_congr rfl key]
  unfold S
  rw [Nat.add_sub_cancel, Finset.mul_sum]
  simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one]
  ring

private lemma coeff_S_eq_zero {R : Type*} [CommRing R] (p k d : ℕ) (u : R)
    (h : ∀ j ∈ Finset.range (p - 1), d ≠ k * (j + 1)) :
    PowerSeries.coeff d (S p (PowerSeries.C u * PowerSeries.X ^ k)) = 0 := by
  unfold S
  rw [map_sum]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [mul_pow, ← map_pow, ← pow_mul, ← mul_assoc, ← map_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow, if_neg (h j hj), mul_zero]

/-- `(1 - x)^p` is good for `-1` when `p` is an odd prime. -/
private lemma good_first {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    Good ((p : ℕ) : R) p ((1 + PowerSeries.C (-1 : R) * PowerSeries.X ^ 1) ^ p) (-1) := by
  refine ⟨S p (PowerSeries.C (-1 : R) * PowerSeries.X ^ 1), ?_, ?_, fun d _ => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact coeff_S_eq_zero p 1 0 (-1) fun j _ => by omega
  · refine coeff_S_eq_zero p 1 p (-1) fun j hj => ?_
    have := Finset.mem_range.mp hj
    omega
  · rw [one_add_pow_prime hp, mul_pow, ← map_pow, hodd.neg_one_pow, ← pow_mul, one_mul]

/-- `(1 - x^k)^p` is good for `0` when `2 <= k < p`. -/
private lemma good_middle {R : Type*} [CommRing R] {p k : ℕ} (hp : p.Prime) (hk2 : 2 ≤ k)
    (hkp : k < p) :
    Good ((p : ℕ) : R) p ((1 + PowerSeries.C (-1 : R) * PowerSeries.X ^ k) ^ p) 0 := by
  refine ⟨S p (PowerSeries.C (-1 : R) * PowerSeries.X ^ k), ?_, ?_, fun d hd => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact coeff_S_eq_zero p k 0 (-1) fun j _ => (Nat.mul_pos (by omega) (Nat.succ_pos j)).ne
  · refine coeff_S_eq_zero p k p (-1) fun j _ heq => ?_
    rcases (Nat.dvd_prime hp).mp ⟨j + 1, heq⟩ with h | h <;> omega
  · have hne : d ≠ k * p := by
      have h1 : 2 * p ≤ k * p := Nat.mul_le_mul_right p hk2
      have h2 := hp.pos
      omega
    rw [one_add_pow_prime hp, mul_pow, ← map_pow, ← pow_mul, map_zero, zero_mul, add_zero]
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg hne, mul_zero,
      add_zero]

/-- In degrees `<= p`, `(1 + u x^p)^n` agrees with `1 + n u x^p`. -/
private lemma coeff_one_add_X_pow_pow {R : Type*} [CommRing R] {p : ℕ} (hp : 0 < p) (u : R) (n : ℕ) :
    ∀ d ≤ p, PowerSeries.coeff d ((1 + PowerSeries.C u * PowerSeries.X ^ p) ^ n) =
      PowerSeries.coeff d (1 + PowerSeries.C (((n : ℕ) : R) * u) * PowerSeries.X ^ p) := by
  induction n with
  | zero => intro d _; simp
  | succ n ih =>
    intro d hd
    rw [pow_succ, coeff_mul_congr ih (fun _ _ => rfl) d hd]
    have hexp : (1 + PowerSeries.C (((n : ℕ) : R) * u) * PowerSeries.X ^ p) *
        (1 + PowerSeries.C u * PowerSeries.X ^ p) =
        1 + PowerSeries.C (((n + 1 : ℕ) : R) * u) * PowerSeries.X ^ p +
          PowerSeries.C (((n : ℕ) : R) * u * u) * (PowerSeries.X ^ p * PowerSeries.X ^ p) := by
      simp only [map_mul, map_add, Nat.cast_add, Nat.cast_one, map_one]; ring
    rw [hexp, map_add, PowerSeries.coeff_C_mul, coeff_X_pow_sq_low hp hd, mul_zero, add_zero]

/-- `(1 - x^p)^p` is good for `-p`. -/
private lemma good_last {R : Type*} [CommRing R] {p : ℕ} (hp : 0 < p) :
    Good ((p : ℕ) : R) p ((1 + PowerSeries.C (-1 : R) * PowerSeries.X ^ p) ^ p) (-((p : ℕ) : R)) := by
  refine ⟨0, by simp, by simp, fun d hd => ?_⟩
  rw [coeff_one_add_X_pow_pow hp (-1) p d hd, mul_zero, add_zero, mul_neg, mul_one]

/-- `prod_{k=1..p} (1 - x^k)^p` is good for `-(1 + p)` when `p >= 3` is prime and `p * p = 0`. -/
private lemma good_prod {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hπ : ((p : ℕ) : R) * ((p : ℕ) : R) = 0) :
    Good ((p : ℕ) : R) p
      (∏ k ∈ Finset.Icc 1 p, (1 + PowerSeries.C (-1 : R) * PowerSeries.X ^ k) ^ p)
      (-1 + (-((p : ℕ) : R) + 0)) := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hset : Finset.Icc 1 p = insert 1 (insert p (Finset.Icc 2 (p - 1))) := by
    ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have h1 : (1 : ℕ) ∉ insert p (Finset.Icc 2 (p - 1)) := by
    simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have h2 : p ∉ Finset.Icc 2 (p - 1) := by
    simp only [Finset.mem_Icc]; omega
  rw [hset, Finset.prod_insert h1, Finset.prod_insert h2]
  refine (good_first hp hodd).mul hπ hp.pos ((good_last hp.pos).mul hπ hp.pos ?_)
  refine Good.prod_zero hπ hp.pos _ _ fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  exact good_middle hp hk.1 (by omega)

/-- The coefficient of `x^p` in an inverse of `prod_{k=1..p} (1 - x^k)^p` over `ZMod (p^2)`. -/
private lemma coeff_inv_prod {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (G : PowerSeries (ZMod (p ^ 2)))
    (hG : (∏ k ∈ Finset.Icc 1 p, (1 - PowerSeries.X ^ k : PowerSeries (ZMod (p ^ 2))) ^ p) * G = 1) :
    PowerSeries.coeff p G = 1 + ((p : ℕ) : ZMod (p ^ 2)) := by
  have hπ : ((p : ℕ) : ZMod (p ^ 2)) * ((p : ℕ) : ZMod (p ^ 2)) = 0 := by
    rw [← Nat.cast_mul, ← pow_two]; exact ZMod.natCast_self (p ^ 2)
  have hP : (∏ k ∈ Finset.Icc 1 p, (1 - PowerSeries.X ^ k : PowerSeries (ZMod (p ^ 2))) ^ p) =
      ∏ k ∈ Finset.Icc 1 p,
        (1 + PowerSeries.C (-1 : ZMod (p ^ 2)) * PowerSeries.X ^ k) ^ p := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_neg, map_one, neg_one_mul, ← sub_eq_add_neg]
  rw [hP] at hG
  rw [(good_prod hp hp3 hπ).coeff_inv hπ hp.pos hG]
  ring

/-- The integer version of the sequence: `aZ n = [x^n] prod_{k=1..n} (1/(1 - x^k))^n` in `Z[[x]]`,
with `1/(1 - x^k)` the inverse `invOfUnit (1 - x^k) 1`. -/
private noncomputable def aZ (n : ℕ) : ℤ :=
  PowerSeries.coeff n
    (∏ k ∈ Finset.Icc 1 n, (PowerSeries.invOfUnit (1 - PowerSeries.X ^ k : PowerSeries ℤ) 1) ^ n)

/-- In `Z[[x]]`, `prod_{k=1..n} (1 - x^k)^n` times the series that defines `aZ n` is `1`. -/
private lemma prod_mul_inv_int (n : ℕ) :
    (∏ k ∈ Finset.Icc 1 n, (1 - PowerSeries.X ^ k : PowerSeries ℤ) ^ n) *
      (∏ k ∈ Finset.Icc 1 n,
        (PowerSeries.invOfUnit (1 - PowerSeries.X ^ k : PowerSeries ℤ) 1) ^ n) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  have hc : PowerSeries.constantCoeff (1 - PowerSeries.X ^ k : PowerSeries ℤ) = ((1 : ℤˣ) : ℤ) := by
    simp [show k ≠ 0 by omega]
  rw [← mul_pow, PowerSeries.mul_invOfUnit _ _ hc, one_pow]

/-- The supercongruence for the integer version: `p^2` divides `aZ p - (p + 1)`. -/
private theorem key (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    ((p : ℤ) ^ 2) ∣ (aZ p - ((p : ℤ) + 1)) := by
  unfold aZ
  generalize hGZ : (∏ k ∈ Finset.Icc 1 p,
      (PowerSeries.invOfUnit (1 - PowerSeries.X ^ k : PowerSeries ℤ) 1) ^ p) = GZ
  have hZ : (∏ k ∈ Finset.Icc 1 p, (1 - PowerSeries.X ^ k : PowerSeries ℤ) ^ p) * GZ = 1 := by
    rw [← hGZ]
    exact prod_mul_inv_int p
  have hR : (∏ k ∈ Finset.Icc 1 p, (1 - PowerSeries.X ^ k : PowerSeries (ZMod (p ^ 2))) ^ p) *
      PowerSeries.map (Int.castRingHom (ZMod (p ^ 2))) GZ = 1 := by
    have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod (p ^ 2)))) hZ
    rw [map_mul, map_one, map_prod] at h
    refine Eq.trans ?_ h
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_pow, map_sub, map_one, map_pow, PowerSeries.map_X]
  have hcoeff := coeff_inv_prod hp hp3 _ hR
  rw [PowerSeries.coeff_map, eq_intCast] at hcoeff
  rw [show ((p : ℤ) ^ 2) = ((p ^ 2 : ℕ) : ℤ) from (Nat.cast_pow p 2).symm,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [hcoeff]
  ring

/-- Over a field: if `A(0)` is not zero and `A^n * B = 1`, then `(A⁻¹)^n = B`. -/
private lemma inv_pow_eq_of_pow_mul_eq_one {K : Type*} [Field K] {A B : PowerSeries K} {n : ℕ}
    (hA : PowerSeries.constantCoeff A ≠ 0) (h : A ^ n * B = 1) : A⁻¹ ^ n = B := by
  have hinv : A⁻¹ * A = 1 := PowerSeries.inv_mul_cancel A hA
  calc A⁻¹ ^ n = A⁻¹ ^ n * (A ^ n * B) := by rw [h, mul_one]
    _ = B := by rw [← mul_assoc, ← mul_pow, hinv, one_pow, one_mul]

/-- The constant coefficient of `prod_{k=1..n} (1 - x^k)` over `Q` is not zero. -/
private lemma constantCoeff_prod_ne_zero (n : ℕ) :
    PowerSeries.constantCoeff
      (∏ k ∈ Finset.Icc 1 n, (1 - PowerSeries.X ^ k : PowerSeries ℚ)) ≠ 0 := by
  rw [map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  have hc : PowerSeries.constantCoeff (1 - PowerSeries.X ^ k : PowerSeries ℚ) = 1 := by
    simp [show k ≠ 0 by omega]
  rw [hc]
  exact one_ne_zero

/-- The integer identity `prod (1 - x^k)^n * G = 1`, mapped to `Q[[x]]`. -/
private lemma pow_prod_mul_map_eq_one (n : ℕ) (G : PowerSeries ℤ)
    (hG : (∏ k ∈ Finset.Icc 1 n, (1 - PowerSeries.X ^ k : PowerSeries ℤ) ^ n) * G = 1) :
    (∏ k ∈ Finset.Icc 1 n, (1 - PowerSeries.X ^ k : PowerSeries ℚ)) ^ n *
      PowerSeries.map (Int.castRingHom ℚ) G = 1 := by
  have hmap : PowerSeries.map (Int.castRingHom ℚ)
      (∏ k ∈ Finset.Icc 1 n, (1 - PowerSeries.X ^ k : PowerSeries ℤ) ^ n) =
      (∏ k ∈ Finset.Icc 1 n, (1 - PowerSeries.X ^ k : PowerSeries ℚ)) ^ n := by
    rw [map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_pow, map_sub, map_one, map_pow, PowerSeries.map_X]
  rw [← hmap, ← map_mul, hG, map_one]

/-- Bridge: the rational series of the statement is the image of the integer series of `aZ`. -/
private lemma bridge (n : ℕ) :
    ((∏ k ∈ Finset.Icc 1 n, (1 - PowerSeries.X ^ k : PowerSeries ℚ))⁻¹) ^ n =
      PowerSeries.map (Int.castRingHom ℚ) (∏ k ∈ Finset.Icc 1 n,
        (PowerSeries.invOfUnit (1 - PowerSeries.X ^ k : PowerSeries ℤ) 1) ^ n) :=
  inv_pow_eq_of_pow_mul_eq_one (constantCoeff_prod_ne_zero n)
    (pow_prod_mul_map_eq_one n _ (prod_mul_inv_int n))

/-- The sequence of the statement is the integer sequence `aZ`, seen in `Q`. -/
private lemma a_eq (n : ℕ) : OMA.S_oeis_a008485.a n = ((aZ n : ℤ) : ℚ) := by
  unfold OMA.S_oeis_a008485.a aZ
  rw [bridge, PowerSeries.coeff_map, eq_intCast]

end A008485Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a008485.main := by
  intro p hp hp3
  obtain ⟨c, hc⟩ := A008485Proof.key p hp hp3
  refine ⟨c, ?_⟩
  rw [A008485Proof.a_eq]
  exact_mod_cast hc
