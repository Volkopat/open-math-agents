import OMAStatements.S_oeis_a278405
import Mathlib

-- Gaussian coefficient lemmas from @TaifengYi, OEIS A179524 conjecture 4.
namespace SunQ

open Finset Polynomial

noncomputable def gb (Q : ℂ) : ℕ → ℕ → ℂ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => gb Q n (k + 1) + Q ^ (n - k) * gb Q n k

@[simp] theorem gb_zero (Q : ℂ) (n : ℕ) : gb Q n 0 = 1 := by cases n <;> rfl

theorem gb_zero_of_lt (Q : ℂ) {n k : ℕ} (h : n < k) : gb Q n k = 0 := by
  induction n generalizing k with
  | zero => cases k <;> simp_all [gb]
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k => simp [gb, ih (show n < k+1 by omega), ih (show n < k by omega)]

@[simp] theorem gb_self (Q : ℂ) (n : ℕ) : gb Q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [gb, gb_zero_of_lt Q (Nat.lt_succ_self n), ih]

noncomputable def fac (Q : ℂ) (k : ℕ) : ℂ := ∏ i ∈ range k, (1-Q^(i+1))

@[simp] theorem fac_zero (Q : ℂ) : fac Q 0 = 1 := by simp [fac]
theorem fac_succ (Q : ℂ) (k : ℕ) : fac Q (k+1) = fac Q k * (1-Q^(k+1)) := by
  simp [fac, prod_range_succ]

theorem gb_mul_fac (Q : ℂ) {n k : ℕ} (hk : k ≤ n) :
    gb Q n k * fac Q k * fac Q (n-k) = fac Q n := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      by_cases h : k = n
      · subst k; simp
      have h₀ : k ≤ n := by omega
      have h₁ : k+1 ≤ n := by omega
      have hF : fac Q (n-k) = fac Q (n-(k+1)) * (1-Q^(n-k)) := by
        have e : n-k = n-(k+1)+1 := by omega
        rw [e, fac_succ]
      have he : n-k + (k+1) = n+1 := by omega
      simp only [Nat.succ_sub_succ_eq_sub, gb, add_mul]
      calc
        _ = (gb Q n (k+1) * fac Q (k+1) * fac Q (n-(k+1))) * (1-Q^(n-k)) +
            Q^(n-k) * (gb Q n k * fac Q k * fac Q (n-k)) * (1-Q^(k+1)) := by
              nth_rw 1 [hF]
              nth_rw 2 [fac_succ Q k]
              ring
        _ = _ := by rw [ih h₁, ih h₀, fac_succ, ← he, pow_add]; ring

theorem gb_one (n k : ℕ) : gb 1 n k = (n.choose k : ℂ) := by
  induction n generalizing k with
  | zero => cases k <;> simp [gb]
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => simp [gb, Nat.choose_succ_succ, ih, add_comm]

theorem gaussianProduct_coeff (Q : ℂ) (n k : ℕ) :
    (∏ i ∈ range n, (1 + C (Q^i) * X : ℂ[X])).coeff k = Q^(k.choose 2) * gb Q n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [gb, coeff_one]
  | succ n ih =>
    rw [prod_range_succ, mul_add, mul_one, ← mul_assoc, coeff_add]
    cases k with
    | zero => rw [coeff_mul_X_zero, ih]; simp
    | succ k =>
      rw [coeff_mul_X, coeff_mul_C, ih, ih, Nat.choose_succ_succ, Nat.choose_one_right, gb]
      by_cases hk : k ≤ n
      · have hpow : Q^n = Q^k * Q^(n-k) := by rw [← pow_add, Nat.add_sub_of_le hk]
        rw [pow_add, hpow]
        ring
      · have h₁ : n < k := by omega
        rw [gb_zero_of_lt Q h₁, gb_zero_of_lt Q (show n < k+1 by omega)]
        ring

theorem fac_ne_zero {Q : ℂ} {n d : ℕ} (hQ : IsPrimitiveRoot Q d) (hn : n < d) :
    fac Q n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply sub_ne_zero.mpr
  exact (hQ.pow_ne_one_of_pos_of_lt (Nat.succ_ne_zero i)
    (lt_of_le_of_lt (Finset.mem_range.mp hi) hn)).symm
end SunQ

section

open Polynomial Finset
namespace OMA.Sun

noncomputable def gaussianProduct (q : ℂ) (n : ℕ) : ℂ[X] :=
  ∏ i ∈ range n, (1 + C (q ^ i) * X)

noncomputable def gaussian (q : ℂ) (n k : ℕ) : ℂ :=
  (gaussianProduct q n).coeff k / q ^ (k.choose 2)

theorem gaussian_period {d : ℕ} (hd : Odd d) {q : ℂ} (hq : IsPrimitiveRoot q d) :
    gaussianProduct q d = 1 + X ^ d := by
  have dh : 0 < d := by obtain ⟨t, rfl⟩ := hd; omega
  have hroot : IsPrimitiveRoot (C q : ℂ[X]) d := hq.map_of_injective C_injective
  have H := X_pow_sub_C_eq_prod hroot dh (hd.neg_pow (X : ℂ[X]))
  have H1 := congrArg (Polynomial.eval (1 : ℂ[X])) H
  simpa [gaussianProduct, eval_prod, ← map_pow] using H1.symm

theorem gaussian_blocks {d : ℕ} (hd : Odd d) {q : ℂ} (hq : IsPrimitiveRoot q d)
    (a b : ℕ) :
    gaussianProduct q (a*d+b) = (1+X^d)^a * gaussianProduct q b := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Nat.add_assoc, ih]
    have h : gaussianProduct q (d+b) = gaussianProduct q d * gaussianProduct q b := by
      simp only [gaussianProduct, prod_range_add, pow_add, hq.pow_eq_one, one_mul]
    rw [h, gaussian_period hd hq, pow_succ, mul_assoc]

theorem gaussianProduct_degree (q : ℂ) (n : ℕ) : (gaussianProduct q n).natDegree ≤ n := by
  unfold gaussianProduct
  refine (natDegree_prod_le _ _).trans ?_
  calc
    _ ≤ ∑ i ∈ range n, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      apply natDegree_add_le_of_degree_le (by simp)
      exact (natDegree_mul_le ..).trans (by simp)
    _ = _ := by simp

private theorem block_coeff {d b : ℕ} (hb : b < d) {q : ℂ} (a c e : ℕ) (he : e < d) :
    (((1+X^d)^a * gaussianProduct q b).coeff (c*d+e)) =
      (a.choose c : ℂ) * (gaussianProduct q b).coeff e := by
  induction a generalizing c with
  | zero =>
    cases c with
    | zero => simp
    | succ c =>
      rw [pow_zero, one_mul, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
      apply coeff_eq_zero_of_natDegree_lt
      have := gaussianProduct_degree q b
      rw [Nat.succ_mul]
      omega
  | succ a ih =>
    rw [pow_succ', add_mul, one_mul, add_mul, mul_assoc, coeff_add]
    cases c with
    | zero =>
      simpa [coeff_X_pow_mul', he.not_ge] using ih 0
    | succ c =>
      have hi : (c+1)*d+e=(c*d+e)+d := by ring
      rw [ih, hi, coeff_X_pow_mul, ih, Nat.choose_succ_succ, Nat.cast_add]
      ring

private theorem phase_period {d : ℕ} (hd : Odd d) {q : ℂ} (hq : IsPrimitiveRoot q d)
    (a e : ℕ) : q ^ ((a*d+e).choose 2) = q ^ (e.choose 2) := by
  have step (b : ℕ) : q ^ ((d+b).choose 2) = q ^ (b.choose 2) := by
    induction b with
    | zero =>
      simp only [Nat.add_zero, Nat.choose_eq_zero_of_lt (by decide : 0 < 2), pow_zero]
      obtain ⟨t, ht⟩ := hd
      have h : d.choose 2 = d*t := by
        rw [Nat.choose_two_right, ht]
        simp only [Nat.add_sub_cancel]; rw [show (2*t+1)*(2*t) = ((2*t+1)*t)*2 by ring, Nat.mul_div_cancel _ (by decide : 0 < 2)]
      rw [h, pow_mul, hq.pow_eq_one, one_pow]
    | succ b ih =>
      rw [← Nat.add_assoc, Nat.choose_succ_succ (d+b) 1, Nat.choose_succ_succ b 1,
        Nat.choose_one_right, Nat.choose_one_right, pow_add, pow_add, ih, pow_add, hq.pow_eq_one, one_mul]
  induction a generalizing e with
  | zero => simp
  | succ a ih => rw [Nat.succ_mul, Nat.add_assoc, ih, step]

theorem gaussian_lucas {d : ℕ} (hd : Odd d) {q : ℂ} (hq : IsPrimitiveRoot q d)
    (a b c e : ℕ) (hb : b < d) (he : e < d) :
    gaussian q (a*d+b) (c*d+e) = (a.choose c : ℂ) * gaussian q b e := by
  simp only [gaussian, gaussian_blocks hd hq, block_coeff hb _ _ _ he, phase_period hd hq]
  ring

end OMA.Sun

end

section

/- The q-Lucas factorization for the recursive Gaussian coefficients. -/

namespace SunQ

theorem gb_eq_gaussian {Q : ℂ} (hQ : Q ≠ 0) (n k : ℕ) :
    gb Q n k = OMA.Sun.gaussian Q n k := by
  unfold OMA.Sun.gaussian OMA.Sun.gaussianProduct
  rw [gaussianProduct_coeff, eq_div_iff (pow_ne_zero _ hQ), mul_comm]

theorem gb_lucas {d : ℕ} (hd : Odd d) {Q : ℂ} (hQ : IsPrimitiveRoot Q d)
    (a b c e : ℕ) (hb : b < d) (he : e < d) :
    gb Q (a*d+b) (c*d+e) = (a.choose c : ℂ) * gb Q b e := by
  have h : Q ≠ 0 := hQ.ne_zero (by omega)
  simpa only [gb_eq_gaussian h] using OMA.Sun.gaussian_lucas hd hQ a b c e hb he

end SunQ

end

namespace SunWZ
open SunQ Finset

noncomputable def phase (q : ℂ) (k : ℕ) := (-1 : ℂ)^k / q^(k.choose 2)
noncomputable def R (q : ℂ) (n k : ℕ) :=
  phase q k * (1 + q^k) / (1-q^k)^2 *
    (fac q (n+k) * fac q (n-k)) / (fac q n)^2
noncomputable def U (q : ℂ) (n k : ℕ) :=
  phase q k * q^(n+1) / (1-q^(n+1))^3 *
    (fac q (n+k) * fac q (n+1-k)) / (fac q n)^2
noncomputable def V (q : ℂ) (k : ℕ) :=
  phase q k * (1+3*q^k+q^(2*k)) * gb q (2*k) k / ((1+q^k)*(1-q^k)^2)

theorem phase_succ {q : ℂ} (_hq : q ≠ 0) (k : ℕ) :
    phase q (k+1) = - phase q k / q^k := by
  simp [phase, Nat.choose_succ_succ, Nat.choose_one_right, pow_add, pow_succ, div_eq_mul_inv]
  ring

theorem no_neg {d : ℕ} {q : ℂ} (hd : Odd d) (h : IsPrimitiveRoot q d) (k : ℕ) :
    1+q^k ≠ 0 := by
  intro hzero
  have e : q^k = -1 := by linear_combination hzero
  have E := congrArg (fun w : ℂ => w^d) e
  change (q^k)^d = (-1:ℂ)^d at E
  rw [← pow_mul, Nat.mul_comm k d, pow_mul, h.pow_eq_one, one_pow, hd.neg_one_pow] at E
  norm_num at E

theorem cert (a b : ℂ) (ha : 1-a ≠ 0) (hb : b ≠ 0) (_hp : 1+b ≠ 0) (hm : 1-b ≠ 0) :
    (1+b)/(1-b)^2 * (1-a*b)*(1-a/b)/(1-a)^2 - (1+b)/(1-b)^2 =
    - (a/b)/(1-a)^3 * (1-a*b) - a/(1-a)^3 * (1-a/b) := by
  field_simp
  ring

theorem wz {d : ℕ} {q : ℂ} (hd : Odd d) (h : IsPrimitiveRoot q d)
    {n k : ℕ} (hn : n+1<d) (hk : 0<k) (hkn : k≤n) :
    R q (n+1) k - R q n k = U q n (k+1) - U q n k := by
  have q0 := h.ne_zero (by omega)
  have b0 := pow_ne_zero k q0
  have ha := sub_ne_zero.mpr (h.pow_ne_one_of_pos_of_lt (by omega : n+1 ≠ 0) hn).symm
  have hm := sub_ne_zero.mpr (h.pow_ne_one_of_pos_of_lt (by omega : k ≠ 0) (by omega : k<d)).symm
  have hc := cert (q^(n+1)) (q^k) ha b0 (no_neg hd h k) hm
  have H : q^(n+1-k) = q^(n+1)/q^k := by
    rw [eq_div_iff b0, ←pow_add]; congr 1; omega
  have E : fac q (n+1-k) = fac q (n-k)*(1-q^(n+1)/q^k) := by
    rw [←H, show n+1-k = n-k+1 by omega, fac_succ]
  have B : fac q (n+k+1) = fac q (n+k)*(1-q^(n+1)*q^k) := by
    rw [fac_succ, ←pow_add, show n+k+1=n+1+k by omega]
  unfold R U
  rw [show n+1+k=n+k+1 by omega, show n+(k+1)=n+k+1 by omega,
    B, E, show n+1-(k+1)=n-k by omega, fac_succ q n, phase_succ q0]
  convert congrArg (fun x : ℂ => phase q k * (fac q (n+k) * fac q (n-k)) / (fac q n)^2 * x) hc using 1 <;>
    simp only [div_eq_mul_inv, mul_inv_rev, mul_pow] <;> ring


theorem boundary_left {d : ℕ} {q : ℂ} (h : IsPrimitiveRoot q d) {n : ℕ}
    (hn : n+1<d) : U q n 1 = - q^(n+1)/(1-q^(n+1))^2 := by
  have hf := fac_ne_zero h (show n<d by omega)
  have ha := sub_ne_zero.mpr (h.pow_ne_one_of_pos_of_lt (by omega : n+1≠0) hn).symm
  simp only [U, phase, pow_one, Nat.choose_eq_zero_of_lt (by decide : 1<2), pow_zero, div_one,
    Nat.add_sub_cancel, fac_succ q n]
  field_simp

theorem boundary_diag {d : ℕ} {q : ℂ} (hd : Odd d) (h : IsPrimitiveRoot q d) {n : ℕ}
    (hn : n+1<d) : R q (n+1) (n+1) + U q n (n+1) = V q (n+1) := by
  let m := n+1
  have hm : m<d := hn
  have hfm := fac_ne_zero h hm
  have hfn := fac_ne_zero h (show n<d by omega)
  have hq := sub_ne_zero.mpr (h.pow_ne_one_of_pos_of_lt (by dsimp [m]; omega : m≠0) hm).symm
  have hp := no_neg hd h m
  have G : fac q (2*m) = gb q (2*m) m * (fac q m)^2 := by
    have H := gb_mul_fac q (show m≤2*m by omega)
    rw [show 2*m-m=m by omega] at H
    linear_combination -H
  have Hm : fac q m = fac q n * (1-q^m) := fac_succ q n
  have H2 : fac q (2*m) = fac q (n+m) * (1-q^m)*(1+q^m) := by
    rw [show 2*m=n+m+1 by dsimp [m]; omega, fac_succ, show n+m+1=m+m by dsimp [m]; omega, pow_add]
    ring
  have HG : fac q (n+m) * (1+q^m) = gb q (2*m) m * (fac q n)^2 * (1-q^m) := by
    apply mul_right_cancel₀ hq
    rw [Hm, H2] at G
    linear_combination G
  change R q m m + U q n m = V q m
  simp only [R,U,V, show n+1=m by rfl, Nat.sub_self, fac_zero, mul_one,
    show m+m=2*m by omega, G, show q^(2*m)=q^m*q^m by rw [two_mul, pow_add]]
  rw [(eq_div_iff hp).mpr HG]
  field_simp [hfm,hfn,hq,hp] <;> ring


theorem identity {d : ℕ} {q : ℂ} (hd : Odd d) (h : IsPrimitiveRoot q d)
    (n : ℕ) (hn : n<d) :
    ∑ i ∈ range n, V q (i+1) =
    ∑ i ∈ range n, R q n (i+1) - ∑ i ∈ range n, q^(i+1)/(1-q^(i+1))^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (by omega)
    have H : (∑ i ∈ range n, R q (n+1) (i+1)) - (∑ i ∈ range n, R q n (i+1)) =
        U q n (n+1) - U q n 1 := by
      rw [← sum_sub_distrib]
      calc
        _ = ∑ i ∈ range n, (U q n (i+1+1) - U q n (i+1)) := by
          apply sum_congr rfl; intro i hi
          exact wz hd h hn (by omega) (mem_range.mp hi)
        _ = _ := sum_range_sub (fun i => U q n (i+1)) n
    rw [sum_range_succ, sum_range_succ, sum_range_succ]
    rw [boundary_left h hn] at H
    linear_combination ih' - H - boundary_diag hd h hn

theorem R_vanish {d : ℕ} {q : ℂ} (h : IsPrimitiveRoot q d) (hd : 0<d) {k : ℕ}
    (hk : 0<k) : R q (d-1) k = 0 := by
  have HF : fac q (d-1+k) = 0 := by
    apply Finset.prod_eq_zero (mem_range.mpr (show d-1<d-1+k by omega))
    simp [show d-1+1=d by omega, h.pow_eq_one]
  simp [R, HF]

theorem full_sum {d : ℕ} {q : ℂ} (hd : Odd d) (h : IsPrimitiveRoot q d) :
    ∑ i ∈ range (d-1), V q (i+1) = -∑ i ∈ range (d-1), q^(i+1)/(1-q^(i+1))^2 := by
  have hd0 : 0<d := by obtain ⟨a,ha⟩ := hd; omega
  rw [identity hd h _ (by omega)]
  simp [R_vanish h hd0 (Nat.succ_pos _)]


theorem sum_nontrivial {d : ℕ} (hd : 0<d) {q w : ℂ} (h : IsPrimitiveRoot q d)
    (hw : IsPrimitiveRoot w d) (f : ℂ → ℂ) :
    ∑ i ∈ range (d-1), f (q^(i+1)) = ∑ i ∈ range (d-1), f (w^(i+1)) := by
  have : NeZero d := ⟨hd.ne'⟩
  have aux (z : ℂ) (hz : IsPrimitiveRoot z d) :
      (range d).image (fun i => z^i) = Polynomial.nthRootsFinset d (1:ℂ) := by
    ext x
    rw [mem_image, Polynomial.mem_nthRootsFinset hd]
    constructor
    · rintro ⟨i,_,rfl⟩
      rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]
    · intro hx
      obtain ⟨i,hi,H⟩ := hz.eq_pow_of_pow_eq_one hx
      exact ⟨i,mem_range.mpr hi,H⟩
  have S (z : ℂ) (hz : IsPrimitiveRoot z d) :
      ∑ i ∈ range d, f (z^i) = ∑ x ∈ Polynomial.nthRootsFinset d (1:ℂ), f x := by
    rw [← aux z hz, sum_image]
    exact fun i hi j hj e => hz.pow_inj (mem_range.mp hi) (mem_range.mp hj) e
  have H := (S q h).trans (S w hw).symm
  nth_rw 1 2 [show d=d-1+1 by omega] at H
  simpa only [sum_range_succ', pow_zero, add_left_inj] using H

theorem V_high {d k : ℕ} {q : ℂ} (hd : Odd d) (h : IsPrimitiveRoot q d)
    (hk : k<d) (hh : d≤2*k) : V q k = 0 := by
  have e := gb_lucas hd h 1 (2*k-d) 0 k (by omega) hk
  simp only [one_mul, zero_mul, zero_add, Nat.choose_zero_right, Nat.cast_one, one_mul,
    Nat.add_sub_of_le hh, gb_zero_of_lt q (show 2*k-d < k by omega)] at e
  simp [V,e]

theorem half_sum {d : ℕ} {q : ℂ} (hd : Odd d) (h : IsPrimitiveRoot q d) :
    ∑ i ∈ range ((d-1)/2), V q (i+1) = -∑ i ∈ range (d-1), q^(i+1)/(1-q^(i+1))^2 := by
  rw [← full_sum hd h]
  apply sum_subset (range_mono (by omega))
  intro i hi hn
  simp only [mem_range] at hi hn
  apply V_high hd h <;> omega

theorem half_sum_invariant {d : ℕ} {q w : ℂ} (hd : Odd d) (h : IsPrimitiveRoot q d)
    (hw : IsPrimitiveRoot w d) :
    ∑ i ∈ range ((d-1)/2), V q (i+1) = ∑ i ∈ range ((d-1)/2), V w (i+1) := by
  rw [half_sum hd h,half_sum hd hw]
  congr 1
  exact sum_nontrivial (by obtain ⟨a,ha⟩ := hd; omega) h hw (fun x => x/(1-x)^2)

end SunWZ

namespace SunCubic
open Polynomial Finset SunQ
section
variable {R : Type*} [CommRing R]
noncomputable def G (Q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => G Q n (k + 1) + Q ^ (n - k) * G Q n k

@[simp] theorem G_zero (Q : R) (n : ℕ) : G Q n 0 = 1 := by cases n <;> rfl

theorem G_zero_of_lt (Q : R) {n k : ℕ} (h : n < k) : G Q n k = 0 := by
  induction n generalizing k with
  | zero => cases k <;> simp_all [G]
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k => simp [G, ih (show n < k+1 by omega), ih (show n < k by omega)]

@[simp] theorem G_self (Q : R) (n : ℕ) : G Q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [G, G_zero_of_lt Q (Nat.lt_succ_self n), ih]

noncomputable def qfac (Q : R) (k : ℕ) : R := ∏ i ∈ range k, (1-Q^(i+1))

@[simp] theorem qfac_zero (Q : R) : qfac Q 0 = 1 := by simp [qfac]
theorem qfac_succ (Q : R) (k : ℕ) : qfac Q (k+1) = qfac Q k * (1-Q^(k+1)) := by
  simp [qfac, prod_range_succ]

theorem G_mul_qfac (Q : R) {n k : ℕ} (hk : k ≤ n) :
    G Q n k * qfac Q k * qfac Q (n-k) = qfac Q n := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      by_cases h : k = n
      · subst k; simp
      have h₀ : k ≤ n := by omega
      have h₁ : k+1 ≤ n := by omega
      have hF : qfac Q (n-k) = qfac Q (n-(k+1)) * (1-Q^(n-k)) := by
        have e : n-k = n-(k+1)+1 := by omega
        rw [e, qfac_succ]
      have he : n-k + (k+1) = n+1 := by omega
      simp only [Nat.succ_sub_succ_eq_sub, G, add_mul]
      calc
        _ = (G Q n (k+1) * qfac Q (k+1) * qfac Q (n-(k+1))) * (1-Q^(n-k)) +
            Q^(n-k) * (G Q n k * qfac Q k * qfac Q (n-k)) * (1-Q^(k+1)) := by
              nth_rw 1 [hF]
              nth_rw 2 [qfac_succ Q k]
              ring
        _ = _ := by rw [ih h₁, ih h₀, qfac_succ, ← he, pow_add]; ring


end

theorem G_eval {R : Type*} [CommRing R] (q : R) (n k : ℕ) :
    (G (X : R[X]) n k).eval q = G q n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [G]
  | succ n ih => cases k <;> simp [G, ih]

theorem G_complex (q : ℂ) (n k : ℕ) : G q n k = gb q n k := by
  induction n generalizing k with
  | zero => cases k <;> rfl
  | succ n ih => cases k <;> simp [G,gb,ih]

theorem qfacX_ne (n : ℕ) : qfac (X : ℂ[X]) n ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro i _
  apply sub_ne_zero.mpr
  intro h
  have hh := congrArg (Polynomial.eval (0:ℂ)) h
  simpa using hh

theorem contiguous {n k : ℕ} (hk : k≤n) :
    G (X : ℂ[X]) (n+1) (k+1) * (1-X^(k+1)) = G X n k * (1-X^(n+1)) := by
  apply mul_right_cancel₀ (mul_ne_zero (qfacX_ne k) (qfacX_ne (n-k)))
  have h := G_mul_qfac (X:ℂ[X]) (Nat.succ_le_succ hk)
  rw [Nat.succ_sub_succ_eq_sub, qfac_succ X k, qfac_succ X n] at h
  rw [← G_mul_qfac X hk] at h
  linear_combination h

noncomputable def δ (a : ℂ[X]) := X * derivative a

theorem delta_mul (a b : ℂ[X]) : δ (a*b) = δ a * b + a * δ b := by
  simp [δ,derivative_mul]; ring

theorem delta_add (a b : ℂ[X]) : δ (a+b) = δ a + δ b := by simp [δ,mul_add]

theorem delta_sub (a b : ℂ[X]) : δ (a-b) = δ a - δ b := by simp [δ,mul_sub]

theorem delta_Xpow (k : ℕ) : δ (X^k) = C (k:ℂ)*X^k := by
  cases k with
  | zero => simp [δ]
  | succ k => rw [δ, derivative_X_pow_succ, pow_succ, Nat.cast_succ, map_add, map_one]; ring

theorem delta_contiguous {n k : ℕ} (hk : k≤n) {z : ℂ} (hN : z^(n+1)=1)
    (hkz : 1-z^(k+1)≠0) :
    (δ (G X (n+1) (k+1))).eval z = - (n+1 : ℕ) * gb z n k / (1-z^(k+1)) := by
  have H := congrArg (Polynomial.eval z) (contiguous hk)
  simp only [eval_mul, eval_sub, eval_one, eval_pow, eval_X, hN, sub_self, mul_zero] at H
  have H0 := (mul_eq_zero.mp H).resolve_right hkz
  have H' := congrArg (fun f => (δ f).eval z) (contiguous hk)
  have hδ : δ 1 = 0 := by simp [δ]
  simp only [delta_mul, delta_sub, delta_Xpow, hδ, zero_sub, eval_add,
    eval_mul, eval_neg, eval_C, eval_pow, eval_X, eval_sub, eval_one, H0, hN, sub_self,
    zero_mul, add_zero, mul_zero, zero_add, mul_one, G_eval, G_complex] at H'
  rw [eq_div_iff hkz]
  push_cast at *
  linear_combination H'

end SunCubic

namespace SunCubic
open Finset SunQ Polynomial

theorem fac_reflect {q : ℂ} {d : ℕ} (h : IsPrimitiveRoot q d) {j : ℕ} (hj : j<d) :
    fac q (d-1) * q^(j.choose 2 + j) = fac q (d-1-j) * (-1)^j * fac q j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have H := ih (by omega)
    have e : q^(d-1-j)*q^(j+1)=1 := by rw [←pow_add, show d-1-j+(j+1)=d by omega, h.pow_eq_one]
    have t : 1-q^(j+1) = -((1-q^(d-1-j))*q^(j+1)) := by linear_combination -e
    have E : fac q (d-1-j) = fac q (d-1-(j+1)) * (1-q^(d-1-j)) := by
      conv_lhs => rw [show d-1-j = d-1-(j+1)+1 by omega, fac_succ]
      rw [show d-1-(j+1)+1=d-1-j by omega]
    rw [Nat.choose_succ_succ, Nat.choose_one_right,
      show j+j.choose 2+(j+1)=(j.choose 2+j)+(j+1) by omega, pow_add _ (j.choose 2+j), ←mul_assoc,
      H, E, fac_succ q j, pow_succ (-1:ℂ), t]
    ring

theorem reflect_last {q : ℂ} {d j : ℕ} (h : IsPrimitiveRoot q d) (hj : j<d) :
    gb q (d-1) j = (-1)^j / q^(j.choose 2+j) := by
  have H := fac_reflect h hj
  rw [←gb_mul_fac q (show j≤d-1 by omega)] at H
  apply (eq_div_iff (pow_ne_zero _ (h.ne_zero (by omega)))).mpr
  apply mul_right_cancel₀ (mul_ne_zero (fac_ne_zero h hj) (fac_ne_zero h (by omega : d-1-j<d)))
  linear_combination H

theorem central_step {d s : ℕ} {q : ℂ} (h : IsPrimitiveRoot q d) (hs : 0<s)
    (h2 : 2*s<d) : gb q (2*s-1) s = gb q (2*s) s / (1+q^s) := by
  have hf := fac_ne_zero h (show s<d by omega)
  have hg := fac_ne_zero h (show s-1<d by omega)
  have ha := sub_ne_zero.mpr (h.pow_ne_one_of_pos_of_lt hs.ne' (by omega : s<d)).symm
  have hp : 1+q^s≠0 := by
    intro e
    have h2' := h.pow_ne_one_of_pos_of_lt (by omega : 2*s≠0) h2
    apply h2'
    rw [two_mul,pow_add, show q^s=-1 by linear_combination e]
    norm_num
  have F : fac q s = fac q (s-1)*(1-q^s) := by
    nth_rw 1 [show s=s-1+1 by omega]
    rw [fac_succ, show s-1+1=s by omega]
  have E : fac q (2*s) = fac q (2*s-1)*(1-q^s)*(1+q^s) := by
    conv_lhs => rw [show 2*s=(2*s-1)+1 by omega, fac_succ]
    rw [show 2*s-1+1=2*s by omega, two_mul, pow_add]; ring
  have H := gb_mul_fac q (show s≤2*s by omega)
  rw [E, ←gb_mul_fac q (show s≤2*s-1 by omega), show 2*s-s=s by omega,
    show 2*s-1-s=s-1 by omega] at H
  apply (eq_div_iff hp).mpr
  apply mul_right_cancel₀ (mul_ne_zero hf hf)
  simp only [F] at H ⊢
  linear_combination -H

end SunCubic

namespace SunCubic
open SunQ Polynomial Finset

theorem bin_chain {d n i j : ℕ} {q : ℂ} (h : IsPrimitiveRoot q d) (hn : n<d)
    (hij : i+j≤n) :
    gb q n i * gb q (n-i) j = gb q n (i+j) * gb q (i+j) j := by
  have quot (a b : ℕ) (hb : b≤a) (ha : a<d) :
      gb q a b = fac q a / (fac q b * fac q (a-b)) := by
    apply (eq_div_iff (mul_ne_zero (fac_ne_zero h (by omega)) (fac_ne_zero h (by omega)))).mpr
    rw [←mul_assoc,gb_mul_fac q hb]
  rw [quot n i (by omega) hn, quot (n-i) j (by omega) (by omega), quot n (i+j) hij hn,
    quot (i+j) j (by omega) (by omega), show i+j-j=i by omega, Nat.sub_sub]
  field_simp [fac_ne_zero h (show n-i<d by omega),fac_ne_zero h (show i+j<d by omega)]

theorem twice_tri (k : ℕ) : 2*k.choose 2 + k = k*k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.choose_succ_succ k 1,Nat.choose_one_right]; nlinarith

theorem reflect_central {q : ℂ} {d s : ℕ} (h : IsPrimitiveRoot q d) (hs : 0<s)
    (h2 : 2*s<d) :
    gb q (d-s) s = (-1)^s / q^(s*s+s.choose 2) * gb q (2*s) s / (1+q^s) := by
  have H := bin_chain (q:=q) (n:=d-1) (i:=s-1) (j:=s) h (by omega) (by omega)
  rw [show d-1-(s-1)=d-s by omega, show s-1+s=2*s-1 by omega,
    reflect_last h (show s-1<d by omega), reflect_last h (show 2*s-1<d by omega)] at H
  have hA : 2*(2*s-1).choose 2 + (2*s-1) = (2*s-1)*(2*s-1) := twice_tri _
  have hB := twice_tri (s-1)
  have hC := twice_tri s
  have hD : s-1+1=s := by omega
  have hE : 2*s-1+1=2*s := by omega
  have expo : (2*s-1).choose 2 + (2*s-1) =
      ((s-1).choose 2 + (s-1)) + (s*s+s.choose 2) := by
    nlinarith [congrArg (fun n : ℕ => n*n) hD, congrArg (fun n : ℕ => n*n) hE]
  rw [show (-1:ℂ)^(2*s-1) = (-1)^(s-1)*(-1)^s by rw [←pow_add]; congr 1; omega,
    expo, pow_add, central_step h hs h2] at H
  have nz := h.ne_zero (by omega)
  have hp : 1+q^s ≠ 0 := by
    intro e
    apply h.pow_ne_one_of_pos_of_lt (by omega : 2*s≠0) h2
    rw [two_mul,pow_add, show q^s=-1 by linear_combination e]; norm_num
  field_simp [nz,hp] at H ⊢
  rw [pow_add _ ((s-1).choose 2 + (s-1)),pow_add _ ((s-1).choose 2)] at H
  exact mul_left_cancel₀ (mul_ne_zero (pow_ne_zero ((s-1).choose 2) nz) (pow_ne_zero (s-1) nz))
    (by linear_combination H)

end SunCubic

namespace SunCubic
open SunQ Polynomial Finset

noncomputable def weight {R : Type*} [CommRing R] (x : R) (c k : ℕ) :=
  x^((c*k-1)*(c*k)+k*k) * (1+3*x^k+(x^k)^2) * (∑ i ∈ range c,(x^k)^i)^2
noncomputable def term {R : Type*} [CommRing R] (x : R) (c N k : ℕ) :=
  (weight x c k * G x (N-k) k) * G x N (c*k)^2

theorem pow_block {d : ℕ} {q : ℂ} (h : IsPrimitiveRoot q d) (a b : ℕ) :
    q^(a*d+b)=q^b := by rw [pow_add, mul_comm a, pow_mul, h.pow_eq_one, one_pow, one_mul]

theorem G_block_zero {d : ℕ} {q : ℂ} (hd : Odd d) (h : IsPrimitiveRoot q d)
    (L a b : ℕ) (hb : 0<b) (hbd : b<d) : (G (X:ℂ[X]) (L*d) (a*d+b)).eval q = 0 := by
  rw [G_eval,G_complex]
  simpa [gb_zero_of_lt q hb] using gb_lucas hd h L 0 a b (by omega) hbd

theorem G_block_deriv {d : ℕ} {q : ℂ} (hd : Odd d) (h : IsPrimitiveRoot q d)
    {L a b : ℕ} (ha : a<L) (hb : 0<b) (hbd : b<d) :
    (δ (G X (L*d) (a*d+b))).eval q =
    - (L*d : ℕ) * ((L-1).choose a : ℂ) * ((-1)^(b-1) / q^((b-1).choose 2+(b-1))) / (1-q^b) := by
  have E : L*d = (L-1)*d+(d-1)+1 := by
    rw [Nat.add_assoc,show d-1+1=d by omega, ←Nat.succ_mul, show (L-1).succ=L by omega]
  have F : a*d+b=a*d+(b-1)+1 := by omega
  have ha' : a*d+(b-1) ≤ (L-1)*d+(d-1) := by gcongr <;> omega
  have r := delta_contiguous (n:=(L-1)*d+(d-1)) (k:=a*d+(b-1)) ha' (z:=q)
  rw [← E, ← F, pow_block h a b] at r
  have H := r (by rw [mul_comm, pow_mul,h.pow_eq_one,one_pow])
    (sub_ne_zero.mpr (h.pow_ne_one_of_pos_of_lt hb.ne' hbd).symm)
  rw [gb_lucas hd h _ _ _ _ (by omega) (by omega),reflect_last h (by omega : b-1<d)] at H
  linear_combination H

theorem term_eval_zero {d : ℕ} {q : ℂ} (hd : Odd d) (h : IsPrimitiveRoot q d)
    {L k c a b : ℕ} (he : c*k=a*d+b) (hb : 0<b) (hbd : b<d) :
    (term (X:ℂ[X]) c (L*d) k).eval q=0 ∧ (δ (term X c (L*d) k)).eval q=0 ∧
    (δ (δ (term X c (L*d) k))).eval q =
      2*(weight (X:ℂ[X]) c k).eval q * gb q (L*d-k) k * ((δ (G X (L*d) (c*k))).eval q)^2 := by
  have H : (G (X:ℂ[X]) (L*d) (c*k)).eval q=0 := he ▸ G_block_zero hd h L a b hb hbd
  simp only [term, sq, delta_mul, delta_add, eval_add, eval_mul, H, mul_zero, zero_mul, add_zero,
    zero_add,G_eval,G_complex, true_and]
  ring

theorem eval_weight (q : ℂ) (c k : ℕ) : (weight (X:ℂ[X]) c k).eval q = weight q c k := by
  simp [weight, eval_finsetSum]

theorem weight_block {d : ℕ} {q : ℂ} (h : IsPrimitiveRoot q d) (c u s : ℕ)
    (hs : 0<c*s) : weight q c (u*d+s)=weight q c s := by
  have ec : c*(u*d+s)=c*u*d+c*s := by ring
  have ef : c*(u*d+s)-1=c*u*d+(c*s-1) := by omega
  have e1 : q^((c*(u*d+s)-1)*(c*(u*d+s))) = q^((c*s-1)*(c*s)) := by
    rw [pow_mul,ef,pow_block h, ←pow_mul, Nat.mul_comm, pow_mul,ec,pow_block h,←pow_mul,Nat.mul_comm]
  have e2 : q^((u*d+s)*(u*d+s))=q^(s*s) := by
    rw [pow_mul,pow_block h,←pow_mul, Nat.mul_comm s, pow_mul,pow_block h, pow_mul]
  simp only [weight, pow_block h u s]
  rw [pow_add _ ((c*(u*d+s)-1)*(c*(u*d+s))),pow_add _ ((c*s-1)*(c*s)),e1,e2]

end SunCubic

namespace SunCubic
open Finset Polynomial SunQ SunWZ

theorem phase_square (q : ℂ) {a : ℕ} (h : 0<a) :
    ((-1 : ℂ)^(a-1) / q^((a-1).choose 2 + (a-1)))^2 =
      1/q^((a-1)*a) := by
  have e := twice_tri (a-1)
  have h' : a-1+1=a := by omega
  have he : ((a-1).choose 2+(a-1))*2=(a-1)*a := by nlinarith [congrArg ((a-1)*·) h']
  rw [div_pow, ←pow_mul q, he, ←pow_mul, Nat.mul_comm (a-1) 2, pow_mul]
  norm_num

theorem normalized {d c s : ℕ} {q : ℂ} (hd : Odd d) (h : IsPrimitiveRoot q d)
    (hs : 0<s) (h2 : 2*s<d) (ha : 0<c*s) (had : c*s<d) :
    weight q c s * gb q (d-s) s *
      (((-1)^(c*s-1) / q^((c*s-1).choose 2+(c*s-1))) / (1-q^(c*s)))^2 = V q s := by
  have nz := h.ne_zero (by omega)
  have hs0 := sub_ne_zero.mpr (h.pow_ne_one_of_pos_of_lt hs.ne' (by omega : s<d)).symm
  have ha0 := sub_ne_zero.mpr (h.pow_ne_one_of_pos_of_lt ha.ne' had).symm
  have H : (∑ i ∈ range c, (q^s)^i) = (1-q^(c*s))/(1-q^s) := by
    rw [eq_div_iff hs0,geom_sum_mul_neg,←pow_mul,Nat.mul_comm]
  rw [weight,div_pow,phase_square q ha, H,reflect_central h hs h2,V,phase,
    pow_add _ ((c*s-1)*(c*s)),pow_add _ (s*s),show 2*s=s*2 by omega, pow_mul q s 2]
  field_simp [nz,ha0,hs0,no_neg hd h s] <;> ring

theorem tail_digits {L d u s : ℕ} (hu : u<L) (hs : s≤d) :
    L*d-(u*d+s) = (L-u-1)*d + (d-s) := by
  have e : L=(L-u-1)+1+u := by omega
  conv_lhs => lhs; rw [e, Nat.add_mul,Nat.add_mul,one_mul]
  omega

noncomputable def coeff (c L d u : ℕ) : ℂ :=
  2 * ((L*d:ℕ):ℂ)^2 * ((L-1).choose (c*u) : ℂ)^2 * ((L-u-1).choose u : ℂ)

theorem low {c L d u s : ℕ} {q : ℂ} (hd : Odd d) (h : IsPrimitiveRoot q d)
    (hu : u<L) (hc : c*u<L) (hs : 0<s) (h2 : 2*s<d) (ha : 0<c*s) (had : c*s<d) :
    (δ (δ (term X c (L*d) (u*d+s)))).eval q = coeff c L d u * V q s := by
  have e : c*(u*d+s)=c*u*d+c*s := by ring
  have H := (term_eval_zero hd h (L:=L) e ha had).2.2
  rw [eval_weight, weight_block h c u s ha, e,G_block_deriv hd h hc ha had,
    tail_digits hu (by omega : s≤d),gb_lucas hd h _ _ _ _ (by omega) (by omega)] at H
  rw [H,coeff,← normalized hd h hs h2 ha had]
  ring

end SunCubic

namespace SunCubic
open Finset Polynomial SunQ SunWZ

theorem residue_digits {c d u s : ℕ} (hc : c=1 ∨ c=2) (hd : Odd d) (hs : 0<s) (hsd : s<d) :
    ∃ a b, 0<b ∧ b<d ∧ c*(u*d+s)=a*d+b := by
  rcases hc with rfl|rfl
  · exact ⟨u,s,hs,hsd,by ring⟩
  · by_cases hl : 2*s<d
    · exact ⟨2*u,2*s,by omega,hl,by ring⟩
    · obtain ⟨v,hv⟩ := hd
      refine ⟨2*u+1,2*s-d,by omega,by omega,?_⟩
      rw [Nat.add_mul, one_mul]
      have e : d+(2*s-d)=2*s := by omega
      rw [Nat.add_assoc,e]; ring

theorem residue {c L d u s : ℕ} {q : ℂ} (hc : c=1 ∨ c=2) (hd : Odd d)
    (h : IsPrimitiveRoot q d) (hu : u<L) (hs : 0<s) (hsd : s<d) :
    (term (X:ℂ[X]) c (L*d) (u*d+s)).eval q=0 ∧
    (δ (term X c (L*d) (u*d+s))).eval q=0 ∧
    (δ (δ (term X c (L*d) (u*d+s)))).eval q = coeff c L d u * V q s := by
  obtain ⟨a,b,hb,hbd,he⟩ := residue_digits (u:=u) hc hd hs hsd
  obtain ⟨h0,h1,h2⟩ := term_eval_zero (L:=L) hd h he hb hbd
  refine ⟨h0,h1,?_⟩
  by_cases hh : 2*s<d
  · have ha : 0<c*s := by rcases hc with rfl|rfl <;> omega
    have had : c*s<d := by rcases hc with rfl|rfl <;> omega
    by_cases hcu : c*u<L
    · exact low hd h hu hcu hs hh ha had
    · have H : L*d<c*(u*d+s) := by
        have E : L*d ≤ (c*u)*d := Nat.mul_le_mul_right d (by omega)
        rw [Nat.mul_add,←Nat.mul_assoc]; omega
      rw [show term (X:ℂ[X]) c (L*d) (u*d+s)=0 by simp [term,G_zero_of_lt X H]]
      simp [δ,coeff,Nat.choose_eq_zero_of_lt (by omega : L-1<c*u)]
  · have Hg : gb q (L*d-(u*d+s)) (u*d+s)=0 := by
      rw [tail_digits hu hsd.le,gb_lucas hd h _ _ _ _ (by omega) hsd]
      have H : d-s<s := by obtain ⟨v,hv⟩ := hd; omega
      rw [gb_zero_of_lt q H,mul_zero]
    rw [h2,Hg, V_high hd h hsd (by omega)]
    ring

noncomputable def block (c L d u : ℕ) : ℂ[X] :=
  ∑ i ∈ range (d-1), term X c (L*d) (u*d+(i+1))

theorem delta_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) :
    δ (∑ i ∈ s,f i)=∑ i ∈ s,δ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [δ]
  | insert a s ha ih => simp [ha,delta_add,ih]

theorem block_values {c L d u : ℕ} {q : ℂ} (hc : c=1 ∨ c=2) (hd : Odd d)
    (h : IsPrimitiveRoot q d) (hu : u<L) :
    (block c L d u).eval q=0 ∧ (δ (block c L d u)).eval q=0 ∧
    (δ (δ (block c L d u))).eval q = coeff c L d u * ∑ i ∈ range (d-1), V q (i+1) := by
  have H (i : ℕ) (hi : i∈range (d-1)) :=
    residue hc hd h hu (Nat.succ_pos i) (by have := mem_range.mp hi; omega : i+1<d)
  simp only [block,delta_sum,eval_finsetSum,mul_sum]
  exact ⟨sum_eq_zero (fun i hi => (H i hi).1),sum_eq_zero (fun i hi => (H i hi).2.1),
    sum_congr rfl (fun i hi => (H i hi).2.2)⟩

end SunCubic

namespace SunCubic
open Finset Polynomial SunQ SunWZ

def Same (z w : ℂ) (f : ℂ[X]) : Prop :=
  f.eval z=f.eval w ∧ (δ f).eval z=(δ f).eval w ∧ (δ (δ f)).eval z=(δ (δ f)).eval w

theorem same_const (z w a : ℂ) : Same z w (C a) := by simp [Same,δ]
theorem same_Xpow {z w : ℂ} {k : ℕ} (h : z^k=w^k) : Same z w (X^k) := by
  simp only [Same,delta_Xpow,delta_mul,show δ (C (k:ℂ))=0 by simp [δ], zero_mul,zero_add,
    eval_mul,eval_C,eval_pow,eval_X,h,true_and]
theorem Same.add {z w : ℂ} {f g : ℂ[X]} (h : Same z w f) (j : Same z w g) :
    Same z w (f+g) := by simp only [Same, delta_add,eval_add,h.1,h.2.1,h.2.2,j.1,j.2.1,j.2.2,true_and]
theorem Same.mul {z w : ℂ} {f g : ℂ[X]} (h : Same z w f) (j : Same z w g) :
    Same z w (f*g) := by
  simp only [Same, delta_mul,delta_add,eval_add,eval_mul,h.1,h.2.1,h.2.2,j.1,j.2.1,j.2.2,true_and]
theorem Same.pow {z w : ℂ} {f : ℂ[X]} (h : Same z w f) (i : ℕ) : Same z w (f^i) := by
  induction i with
  | zero => simpa using same_const z w 1
  | succ i ih => rw [pow_succ]; exact ih.mul h
theorem same_sum {ι : Type*} {z w : ℂ} (s : Finset ι) (f : ι → ℂ[X])
    (H : ∀ i ∈ s, Same z w (f i)) : Same z w (∑ i ∈ s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using same_const z w 0
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact (H i (mem_insert_self ..)).add (ih (fun a h => H a (mem_insert_of_mem h)))

noncomputable def log1 (z : ℂ) (f : ℂ[X]) := (δ f).eval z / f.eval z
noncomputable def log2 (z : ℂ) (f : ℂ[X]) := (δ (δ f)).eval z / f.eval z - (log1 z f)^2

theorem log1_mul {z : ℂ} {f g : ℂ[X]} (hf : f.eval z ≠ 0) (hg : g.eval z ≠ 0) :
    log1 z (f*g) = log1 z f + log1 z g := by
  simp only [log1,delta_mul,eval_add,eval_mul]
  field_simp
theorem log2_mul {z : ℂ} {f g : ℂ[X]} (hf : f.eval z ≠ 0) (hg : g.eval z ≠ 0) :
    log2 z (f*g) = log2 z f + log2 z g := by
  simp only [log2,log1_mul hf hg,delta_mul,delta_add,eval_add,eval_mul,log1]
  field_simp
  ring

noncomputable def row (d a : ℕ) : ℂ[X] := ∏ i ∈ range (d-1), (1-X^(a*d+(i+1)))
noncomputable def geomP (d a : ℕ) : ℂ[X] := ∑ i ∈ range a, (X^d)^i

theorem same_geom {d : ℕ} {z w : ℂ} (h : z^d=w^d) (a : ℕ) : Same z w (geomP d a) :=
  same_sum _ _ (fun i _ => (same_Xpow h).pow i)
theorem geom_val {d : ℕ} {z : ℂ} (h : z^d=1) (a : ℕ) : (geomP d a).eval z=a := by
  simp [geomP,eval_finsetSum,h]
theorem row_factor {d : ℕ} (hd : 0<d) (a : ℕ) :
    qfac (X:ℂ[X]) ((a+1)*d) = qfac X (a*d) * row d a * (1-X^d) * geomP d (a+1) := by
  have e : (a+1)*d = a*d+(d-1)+1 := by rw [Nat.succ_mul]; omega
  rw [e,qfac_succ,qfac, prod_range_add]
  change (_ * ∏ i ∈ range (d-1), (1-X^(a*d+i+1):ℂ[X])) * (1-X^(a*d+(d-1)+1)) = _
  simp only [Nat.add_assoc,show d-1+1=d by omega]
  rw [←Nat.succ_mul, mul_comm a.succ d, pow_mul,←geom_sum_mul_neg]
  unfold row geomP qfac
  ring

theorem G_step {d A B : ℕ} (hd : 0<d) (hab : B≤A) :
    G (X:ℂ[X]) ((A+1)*d) ((B+1)*d) * row d B * geomP d (B+1) =
    G X (A*d) (B*d) * row d A * geomP d (A+1) := by
  have h1 := G_mul_qfac (X:ℂ[X]) (Nat.mul_le_mul_right d (Nat.succ_le_succ hab))
  have h0 := G_mul_qfac (X:ℂ[X]) (Nat.mul_le_mul_right d hab)
  rw [row_factor hd A,row_factor hd B, ←Nat.sub_mul, Nat.succ_sub_succ_eq_sub] at h1
  rw [← Nat.sub_mul] at h0
  rw [←h0] at h1
  have hn : (1-X^d:ℂ[X])≠0 := by
    intro hh
    have H := congrArg (Polynomial.eval (0:ℂ)) hh
    simp [zero_pow hd.ne'] at H
  apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (qfacX_ne (B*d)) (qfacX_ne ((A-B)*d))) hn)
  linear_combination h1

noncomputable def ff (x : ℂ) := x/(1-x)^2
noncomputable def ee (x : ℂ) := x/(1-x)

theorem log_factor {z : ℂ} (n : ℕ) (hn : 1-z^n≠0) :
    log1 z (1-X^n) = -(n:ℂ)*ee (z^n) ∧ log2 z (1-X^n) = -(n:ℂ)^2*ff (z^n) := by
  have H0 : δ 1=0 := by simp [δ]
  have H1 : δ (C (n:ℂ))=0 := by simp [δ]
  have H2 : δ (0:ℂ[X])=0 := by simp [δ]
  simp only [log1,log2,delta_sub,delta_Xpow,delta_mul,H0,H1,H2,zero_mul,zero_add,
    eval_sub,eval_zero,eval_one,eval_mul,eval_C,eval_pow,eval_X,ee,ff]
  constructor <;> field_simp <;> ring

theorem nz_factor {d : ℕ} {z : ℂ} (h : IsPrimitiveRoot z d) (a : ℕ)
    (i : ℕ) (hi : i∈range (d-1)) : (1-X^(a*d+(i+1)):ℂ[X]).eval z ≠ 0 := by
  simp only [eval_sub,eval_one,eval_pow,eval_X,pow_block h]
  exact sub_ne_zero.mpr (h.pow_ne_one_of_pos_of_lt (by omega : i+1≠0) (by have :=mem_range.mp hi; omega)).symm

theorem nz_row {d : ℕ} {z : ℂ} (h : IsPrimitiveRoot z d) (a : ℕ) :
    (row d a).eval z≠0 := by
  rw [row,eval_prod]
  exact prod_ne_zero_iff.mpr (nz_factor h a)

theorem log_prod {z : ℂ} {ι : Type*} (s : Finset ι) (f : ι → ℂ[X])
    (h : ∀ i ∈ s,(f i).eval z ≠ 0) (L : ℂ → ℂ[X] → ℂ) (hl : L z 1=0)
    (hm : ∀ {a b : ℂ[X]}, a.eval z ≠ 0 → b.eval z ≠ 0 → L z (a*b)=L z a+L z b) :
    L z (∏ i ∈ s, f i) = ∑ i ∈ s,L z (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hl
  | insert i s hi ih =>
    have h' := fun j (hj : j∈s) => h j (mem_insert_of_mem hj)
    rw [prod_insert hi, sum_insert hi, hm (h i (mem_insert_self ..)) (by rw [eval_prod]; exact prod_ne_zero_iff.mpr h'), ih h']

theorem log_row {d : ℕ} {z : ℂ} (h : IsPrimitiveRoot z d) (a : ℕ) :
    log1 z (row d a) = ∑ i ∈ range (d-1), -((a*d+(i+1):ℕ):ℂ)*ee (z^(i+1)) ∧
    log2 z (row d a) = ∑ i ∈ range (d-1), -((a*d+(i+1):ℕ):ℂ)^2*ff (z^(i+1)) := by
  constructor
  · rw [row,log_prod _ _ (nz_factor h a) log1 (by simp [log1,δ]) (fun h1 h2 => log1_mul h1 h2)]
    apply sum_congr rfl; intro i hi
    rw [(log_factor _ (by simpa using nz_factor h a i hi)).1, pow_block h]
  · rw [row,log_prod _ _ (nz_factor h a) log2 (by simp [log1,log2,δ]) (fun h1 h2 => log2_mul h1 h2)]
    apply sum_congr rfl; intro i hi
    rw [(log_factor _ (by simpa using nz_factor h a i hi)).2,pow_block h]

end SunCubic

namespace SunCubic
open Finset Polynomial SunQ SunWZ

theorem weighted {d : ℕ} {z : ℂ} (hd : 0<d) (h : IsPrimitiveRoot z d) :
    2*(∑ i ∈ range (d-1), ((i+1:ℕ):ℂ)*ff (z^(i+1))) =
      (d:ℂ)*(∑ i ∈ range (d-1), ff (z^(i+1))) := by
  have H := sum_range_reflect (fun i => ((i+1:ℕ):ℂ)*ff (z^(i+1))) (d-1)
  have E (i : ℕ) (hi : i∈range (d-1)) : ff (z^(d-1-1-i+1)) = ff (z^(i+1)) := by
    have hi' := mem_range.mp hi
    have K : z^(d-1-1-i+1)= (z^(i+1))⁻¹ := by
      rw [←one_div, eq_div_iff (pow_ne_zero _ (h.ne_zero hd.ne'))]
      rw [←pow_add,show d-1-1-i+1+(i+1)=d by omega,h.pow_eq_one]
    rw [K,ff,ff]
    have nz := pow_ne_zero (i+1) (h.ne_zero hd.ne')
    have h1 := sub_ne_zero.mpr (h.pow_ne_one_of_pos_of_lt (by omega : i+1≠0) (by omega : i+1<d)).symm
    have h2 : 1-(z^(i+1))⁻¹≠0 := by
      intro hh; apply h1
      have := sub_eq_zero.mp hh
      have hh' := congrArg (· * z^(i+1)) this
      simpa [nz,sub_eq_zero] using hh'.symm
    generalize hx : z^(i+1)=x at *
    rw [show 1-x⁻¹ = -(1-x)/x by field_simp; ring]
    field_simp
  have T : (d:ℂ)*(∑ i ∈ range (d-1), ff (z^(i+1))) -
      (∑ i ∈ range (d-1), ((i+1:ℕ):ℂ)*ff (z^(i+1))) =
      ∑ i ∈ range (d-1), ((d-1-1-i+1:ℕ):ℂ)*ff (z^(d-1-1-i+1)) := by
    rw [mul_sum, ←sum_sub_distrib]
    apply sum_congr rfl; intro i hi
    rw [E i hi, ←sub_mul]
    congr 1
    have : d-1-1-i+1+(i+1)=d := by have := mem_range.mp hi; omega
    exact sub_eq_of_eq_add (by exact_mod_cast this.symm)
  linear_combination -T - H

theorem log_row_diff {d : ℕ} {z w : ℂ} (hd : 0<d) (h : IsPrimitiveRoot z d) (hw : IsPrimitiveRoot w d)
    (a b : ℕ) :
    log1 z (row d a) - log1 z (row d b) = log1 w (row d a) - log1 w (row d b) ∧
    log2 z (row d a) - log2 z (row d b) = log2 w (row d a) - log2 w (row d b) := by
  have L (q : ℂ) (hq : IsPrimitiveRoot q d) :
      log1 q (row d a) - log1 q (row d b) = (((b:ℂ)-a)*d) * ∑ i ∈ range (d-1), ee (q^(i+1)) := by
    rw [(log_row hq a).1,(log_row hq b).1,←sum_sub_distrib,mul_sum]
    apply sum_congr rfl; intro i hi; push_cast; ring
  have K (q : ℂ) (hq : IsPrimitiveRoot q d) :
      log2 q (row d a) - log2 q (row d b) =
      (((b:ℂ)*d)^2-(a*d)^2+((b:ℂ)-a)*d^2) * ∑ i ∈ range (d-1), ff (q^(i+1)) := by
    have k' : log2 q (row d a) - log2 q (row d b) =
        (((b:ℂ)*d)^2-((a:ℂ)*d)^2)* (∑ i ∈ range (d-1),ff (q^(i+1))) +
        (((b:ℂ)-a)*d)* (2*∑ i ∈ range (d-1), ((i+1:ℕ):ℂ)*ff (q^(i+1))) := by
      rw [(log_row hq a).2,(log_row hq b).2,←sum_sub_distrib,mul_sum,mul_sum,mul_sum,←sum_add_distrib]
      apply sum_congr rfl; intro i hi; push_cast; ring
    rw [k',weighted hd hq]
    push_cast; ring
  exact ⟨by rw [L z h,L w hw,sum_nontrivial hd h hw ee],
    by rw [K z h,K w hw,sum_nontrivial hd h hw ff]⟩

end SunCubic

namespace SunCubic
open Finset Polynomial SunQ SunWZ

theorem G_multiple_val {d : ℕ} {z : ℂ} (hd : Odd d) (h : IsPrimitiveRoot z d) (a b : ℕ) :
    (G (X:ℂ[X]) (a*d) (b*d)).eval z = a.choose b := by
  rw [G_eval,G_complex]
  simpa using gb_lucas hd h a 0 b 0 (by obtain ⟨v,hv⟩:=hd; omega) (by obtain ⟨v,hv⟩:=hd; omega)

theorem log_step {d A B : ℕ} {z : ℂ} (hd : Odd d) (hz : IsPrimitiveRoot z d) (hba : B≤A)
    (L : ℂ → ℂ[X] → ℂ)
    (hm : ∀ {f g : ℂ[X]}, f.eval z ≠ 0 → g.eval z ≠ 0 → L z (f*g)=L z f+L z g) :
    L z (G X ((A+1)*d) ((B+1)*d)) =
    L z (G X (A*d) (B*d)) + (L z (row d A)-L z (row d B)) +
      (L z (geomP d (A+1))-L z (geomP d (B+1))) := by
  have hd0 : 0<d := by obtain ⟨v,hv⟩:=hd; omega
  have nzG (a b : ℕ) (hh : b≤a) : (G (X:ℂ[X]) (a*d) (b*d)).eval z≠0 := by
    rw [G_multiple_val hd hz]; exact_mod_cast (Nat.choose_pos hh).ne'
  have nzg (a : ℕ) : (geomP d (a+1)).eval z ≠ 0 := by
    rw [geom_val hz.pow_eq_one]; exact_mod_cast Nat.succ_ne_zero a
  have H := congrArg (L z) (G_step (d:=d) hd0 hba)
  rw [hm (by rw [eval_mul]; exact mul_ne_zero (nzG _ _ (Nat.succ_le_succ hba)) (nz_row hz B)) (nzg B),
    hm (nzG _ _ (Nat.succ_le_succ hba)) (nz_row hz B),
    hm (by rw [eval_mul]; exact mul_ne_zero (nzG _ _ hba) (nz_row hz A)) (nzg A),
    hm (nzG _ _ hba) (nz_row hz A)] at H
  linear_combination H

theorem Same.logs {z w : ℂ} {f : ℂ[X]} (h : Same z w f) :
    log1 z f=log1 w f ∧ log2 z f=log2 w f := by simp [log1,log2,h.1,h.2.1,h.2.2]
theorem same_of_logs {z w : ℂ} {f : ℂ[X]} (hv : f.eval z=f.eval w) (hn : f.eval w≠0)
    (h1 : log1 z f=log1 w f) (h2 : log2 z f=log2 w f) : Same z w f := by
  rw [log2,log2,h1,sub_left_inj] at h2
  simp only [log1,hv,div_left_inj' hn] at h1
  simp only [hv,div_left_inj' hn] at h2
  exact ⟨hv,h1,h2⟩

theorem G_multiple_same {d : ℕ} {z w : ℂ} (hd : Odd d) (h : IsPrimitiveRoot z d)
    (hw : IsPrimitiveRoot w d) (a b : ℕ) : Same z w (G X (a*d) (b*d)) := by
  by_cases hab : b≤a
  · induction b generalizing a with
    | zero => simpa using same_const z w 1
    | succ b ih =>
      obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show a≠0 by omega)
      have H := ih a (by omega)
      have hd0 : 0<d := by obtain ⟨v,hv⟩:=hd; omega
      have RR := log_row_diff hd0 h hw a b
      have gg (k : ℕ) := (same_geom (h.pow_eq_one.trans hw.pow_eq_one.symm) k).logs
      apply same_of_logs
      · rw [G_multiple_val hd h,G_multiple_val hd hw]
      · rw [G_multiple_val hd hw]; exact_mod_cast (Nat.choose_pos hab).ne'
      · rw [log_step hd h (by omega : b≤a) log1 (fun h1 h2 => log1_mul h1 h2),
          log_step hd hw (by omega : b≤a) log1 (fun h1 h2 => log1_mul h1 h2),
          H.logs.1,RR.1,(gg _).1,(gg _).1]
      · rw [log_step hd h (by omega : b≤a) log2 (fun h1 h2 => log2_mul h1 h2),
          log_step hd hw (by omega : b≤a) log2 (fun h1 h2 => log2_mul h1 h2),
          H.logs.2,RR.2,(gg _).2,(gg _).2]
  · have hd0 : 0<d := by obtain ⟨v,hv⟩:=hd; omega
    rw [G_zero_of_lt X (Nat.mul_lt_mul_of_pos_right (by omega : a<b) hd0)]
    simpa using same_const z w 0

theorem pow_mult {z : ℂ} {d : ℕ} (h : z^d=1) (u : ℕ) : z^(u*d)=1 := by
  rw [Nat.mul_comm, pow_mul,h,one_pow]

theorem weight_same {d : ℕ} {z w : ℂ} (h : z^d=1) (hw : w^d=1) (c u : ℕ) :
    Same z w (weight X c (u*d)) := by
  have HH (j : ℕ) := same_Xpow ((pow_mult h j).trans (pow_mult hw j).symm)
  have H := HH u
  unfold weight
  have e : (c*(u*d)-1)*(c*(u*d))+(u*d)*(u*d) = ((c*(u*d)-1)*(c*u)+u*(u*d))*d := by ring
  rw [e]
  exact ((HH _).mul (((by simpa using same_const z w 1 : Same z w 1).add
    ((by simpa [Same,δ] : Same z w 3).mul H)).add (H.pow 2))).mul
    ((same_sum _ _ (fun i _ => H.pow i)).pow 2)

theorem mult_term_same {d : ℕ} {z w : ℂ} (hd : Odd d) (h : IsPrimitiveRoot z d)
    (hw : IsPrimitiveRoot w d) (L c u : ℕ) : Same z w (term X c (L*d) (u*d)) := by
  unfold term
  rw [←Nat.sub_mul,←Nat.mul_assoc]
  exact ((weight_same h.pow_eq_one hw.pow_eq_one c u).mul (G_multiple_same hd h hw _ _)).mul
    ((G_multiple_same hd h hw _ _).pow 2)

end SunCubic

namespace SunCubic
open Finset Polynomial SunQ SunWZ

def seq (c N : ℕ) : ℕ :=
  ∑ k ∈ range N, N.choose (c*k)^2 * (N-k).choose k

noncomputable def P {R : Type*} [CommRing R] (x : R) (c N : ℕ) :=
  ∑ k ∈ range N, term x c N k

theorem G_hom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : R) (n k : ℕ) :
    f (G x n k) = G (f x) n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [G]
  | succ n ih => cases k <;> simp [G,ih]
theorem P_hom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : R) (c N : ℕ) :
    f (P x c N)=P (f x) c N := by
  simp [P,term,weight,G_hom,map_ofNat]

theorem P_map (c N : ℕ) :
    (P (X:ℤ[X]) c N).map (Int.castRingHom ℂ) = P (X:ℂ[X]) c N := by
  simpa using P_hom (Polynomial.mapRingHom (Int.castRingHom ℂ)) X c N

theorem sum_blocks {M : Type*} [AddCommMonoid M] (m d : ℕ) (f : ℕ → M) :
    ∑ i ∈ range (m*d), f i = ∑ a ∈ range m, ∑ b ∈ range d, f (a*d+b) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul,sum_range_add,ih,sum_range_succ]

theorem P_blocks (c L d : ℕ) (hd : 0<d) :
    P X c (L*d) = ∑ u ∈ range L, (block c L d u + term X c (L*d) (u*d)) := by
  rw [P,sum_blocks]
  apply sum_congr rfl
  intro u hu
  nth_rw 1 [show d=d-1+1 by omega]
  rw [sum_range_succ']
  simp [block]

theorem val_multiple {d : ℕ} {z : ℂ} (hd : Odd d) (h : IsPrimitiveRoot z d) (L c u : ℕ) :
    (term (X:ℂ[X]) c (L*d) (u*d)).eval z = 5*(c:ℂ)^2*((L.choose (c*u)^2*(L-u).choose u:ℕ):ℂ) := by
  have e : (c*(u*d)-1)*(c*(u*d))+(u*d)*(u*d) = ((c*(u*d)-1)*(c*u)+u*(u*d))*d := by ring
  simp only [term,eval_mul,eval_pow,eval_weight,←Nat.sub_mul,show c*(u*d)=c*u*d by ring,G_multiple_val hd h]
  simp only [weight,e,pow_mult h.pow_eq_one,one_pow,sum_const,card_range,nsmul_one]
  push_cast; ring

theorem P_root {d : ℕ} {z : ℂ} (hc : c=1 ∨ c=2) (hd : Odd d) (h : IsPrimitiveRoot z d) (L : ℕ) :
    (P (X:ℂ[X]) c (L*d)).eval z = 5*(c:ℂ)^2*(seq c L : ℂ) := by
  have hd0 : 0<d := by obtain ⟨v,hv⟩:=hd; omega
  rw [P_blocks c L d hd0,eval_finsetSum,seq,Nat.cast_sum,mul_sum]
  apply sum_congr rfl; intro u hu
  rw [eval_add,(block_values hc hd h (mem_range.mp hu)).1,zero_add,val_multiple hd h]
theorem P_same {d : ℕ} {z w : ℂ} (hc : c=1 ∨ c=2) (hd : Odd d) (h : IsPrimitiveRoot z d)
    (hw : IsPrimitiveRoot w d) (L : ℕ) : Same z w (P X c (L*d)) := by
  have hd0 : 0<d := by obtain ⟨v,hv⟩:=hd; omega
  rw [P_blocks c L d hd0]
  apply same_sum; intro u hu
  apply Same.add _ (mult_term_same hd h hw L c u)
  obtain ⟨h0,h1,h2⟩ := block_values hc hd h (mem_range.mp hu)
  obtain ⟨g0,g1,g2⟩ := block_values hc hd hw (mem_range.mp hu)
  exact ⟨h0.trans g0.symm,h1.trans g1.symm,by
    rw [h2,g2,full_sum hd h,full_sum hd hw,sum_nontrivial hd0 h hw (fun x => x/(1-x)^2)]⟩

theorem P_at_one (hc : c=1 ∨ c=2) (N : ℕ) :
    (P (X:ℤ[X]) c N).eval 1=5*(c:ℤ)^2*(seq c N:ℤ) := by
  have HP := P_root (z:=(1:ℂ)) hc (by decide : Odd 1) IsPrimitiveRoot.one N
  rw [Nat.mul_one,←P_map] at HP
  apply (Int.cast_injective (α:=ℂ))
  push_cast
  convert HP using 1
  simpa using (Polynomial.eval₂_at_apply (Int.castRingHom ℂ) (P (X:ℤ[X]) c N) (1:ℤ)).symm

end SunCubic

namespace SunCubic
open Finset Polynomial SunQ SunWZ

noncomputable def twist {R : Type*} [CommRing R] (f : R[X]) (k : ℕ) := f.comp (X^k)
theorem twist_val (f : ℂ[X]) (k : ℕ) (z : ℂ) : (twist f k).eval z = f.eval (z^k) := by simp [twist,eval_comp]
theorem delta_twist (f : ℂ[X]) (k : ℕ) : δ (twist f k) = C (k:ℂ) * twist (δ f) k := by
  unfold twist
  change X * derivative (f.comp (X^k)) = _
  rw [derivative_comp,←mul_assoc,←δ,delta_Xpow,δ,mul_comp,X_comp]; ring
theorem delta_scale (a : ℂ) (f : ℂ[X]) : δ (C a * f) = C a * δ f := by simp [δ]; ring
theorem delta2_twist (f : ℂ[X]) (k : ℕ) : δ (δ (twist f k)) = C (k:ℂ)^2 * twist (δ (δ f)) k := by
  rw [delta_twist,delta_scale,delta_twist]; ring

noncomputable def combo {R : Type*} [CommRing R] (f : R[X]) :=
  C 8*f - C 6*twist f 2 + twist f 4
noncomputable def diff {R : Type*} [CommRing R] (c m p r : ℕ) :=
  P (X:R[X]) c (m*p^(r+1)) - twist (P X c (m*p^r)) p

theorem combo_zero {z : ℂ} {f : ℂ[X]} (h0 : f.eval z=0) (h2 : Same z (z^2) f)
    (h4 : Same z (z^4) f) :
    (combo f).eval z=0 ∧ (δ (combo f)).eval z=0 ∧ (δ (δ (combo f))).eval z=0 := by
  simp only [combo,delta_sub,delta_add,delta_scale,delta2_twist,delta_twist,
    eval_mul,eval_C,eval_sub,eval_add,eval_pow,twist_val,←h2.1,←h4.1,←h2.2.1,←h4.2.1,
    ←h2.2.2,←h4.2.2,h0]
  push_cast
  exact ⟨by ring,by ring,by ring⟩

noncomputable def J {R : Type*} [CommRing R] (t : ℕ) : R[X] := ∑ i ∈ range t, X^i

theorem cube_dvd {t : ℕ} (ht : 0<t) (f : ℂ[X]) (h : ∀ z : ℂ, z^t=1 → z≠1 →
    f.eval z=0 ∧ (δ f).eval z=0 ∧ (δ (δ f)).eval z=0) : J t ^ 3 ∣ f := by
  classical
  by_cases hf : f=0
  · simp [hf]
  have H : J t * (X-1 : ℂ[X])=X^t-1 := geom_sum_mul _ _
  have hm : (J t:ℂ[X]).Monic := monic_geom_sum_X ht.ne'
  have hs : (J t:ℂ[X]).Separable := by
    apply (separable_X_pow_sub_C (1:ℂ) (by exact_mod_cast ht.ne') one_ne_zero).of_dvd
    exact ⟨X-1,by simpa using H.symm⟩
  apply (IsAlgClosed.splits _).dvd_of_roots_le_roots (pow_ne_zero _ hm.ne_zero)
  rw [Multiset.le_iff_count,roots_pow]
  intro z
  by_cases hz : z ∈ (J t:ℂ[X]).roots
  · rw [Multiset.count_nsmul,Multiset.count_eq_one_of_mem (nodup_roots hs) hz,mul_one,count_roots]
    have hv := (mem_roots hm.ne_zero).mp hz
    change (J t:ℂ[X]).eval z=0 at hv
    have hzt : z^t=1 := by
      have E := congrArg (Polynomial.eval z) H
      simpa [hv,sub_eq_zero] using E.symm
    have hz0 : z≠0 := by rintro rfl; simp [zero_pow ht.ne'] at hzt
    have hz1 : z≠1 := by rintro rfl; simpa [J,eval_finsetSum,ht.ne'] using hv
    obtain ⟨hf0,hf1,hf2⟩ := h z hzt hz1
    have hh1 : f.derivative.eval z=0 := by simpa [δ,hz0] using hf1
    have hh2 : f.derivative.derivative.eval z=0 := by simpa [δ,derivative_mul,hh1,hz0] using hf2
    exact lt_rootMultiplicity_of_isRoot_iterate_derivative (n:=2) hf (by
      intro m hm
      interval_cases m
      · exact hf0
      · exact hh1
      · exact hh2)
  · simp [Multiset.count_nsmul,Multiset.count_eq_zero.mpr hz]

end SunCubic

namespace SunCubic
open Finset Polynomial SunWZ

theorem same_sub {z w : ℂ} {f g : ℂ[X]} (h : Same z w f) (hg : Same z w g) :
    Same z w (f-g) := by simp only [Same,delta_sub,eval_sub,h.1,h.2.1,h.2.2,hg.1,hg.2.1,hg.2.2,true_and]
theorem same_twist {z w : ℂ} {f : ℂ[X]} {p : ℕ} (h : Same (z^p) (w^p) f) :
    Same z w (twist f p) := by simp only [Same,delta_twist,delta_scale,eval_mul,eval_C,twist_val,
      h.1,h.2.1,h.2.2,true_and]

theorem combo_prime {c m p r : ℕ} (hc : c=1 ∨ c=2) (hp : p.Prime) (hp5 : 5<p) :
    (J (p^(r+1)):ℂ[X])^3 ∣ combo (diff c m p r) := by
  apply cube_dvd (pow_pos hp.pos _)
  intro z hz hz1
  have h := IsPrimitiveRoot.orderOf z
  have hdiv := (h.pow_eq_one_iff_dvd _).mp hz
  obtain ⟨j,hj,ej⟩ := (Nat.dvd_prime_pow hp).mp hdiv
  cases j with
  | zero =>
    rw [ej,pow_zero] at h
    exact (hz1 (by simpa using h.pow_eq_one)).elim
  | succ j =>
    rw [ej] at h
    let L := m*p^(r-j)
    have e : m*p^r=L*p^j := by
      dsimp [L]; rw [mul_assoc,←pow_add,Nat.sub_add_cancel (by omega)]
    have e' : m*p^(r+1)=L*p^(j+1) := by
      rw [pow_succ,pow_succ,←mul_assoc,←mul_assoc,e]
    have hd : Odd (p^(j+1)) := (hp.odd_of_ne_two (by omega)).pow
    have hd' : Odd (p^j) := (hp.odd_of_ne_two (by omega)).pow
    have hpwr {x : ℂ} (hx : IsPrimitiveRoot x (p^(j+1))) : IsPrimitiveRoot (x^p) (p^j) := by
      have H := hx.pow_of_dvd hp.ne_zero (show p ∣ p^(j+1) by rw [pow_succ]; exact dvd_mul_left ..)
      rwa [pow_succ,Nat.mul_div_cancel _ hp.pos] at H
    have S {w : ℂ} (hw : IsPrimitiveRoot w (p^(j+1))) : Same z w (diff c m p r) := by
      rw [diff,e,e']
      exact same_sub (P_same hc hd h hw L) (same_twist (P_same hc hd' (hpwr h) (hpwr hw) L))
    apply combo_zero
    · rw [diff,e,e',eval_sub,twist_val,P_root hc hd h,P_root hc hd' (hpwr h),sub_self]
    · exact S (h.pow_of_coprime _ hd.coprime_two_left)
    · exact S (h.pow_of_coprime _ (hd.coprime_two_left.pow_left 2))

theorem diff_map (c m p r : ℕ) : (diff (R:=ℤ) c m p r).map (Int.castRingHom ℂ) = diff c m p r := by
  simp only [diff,twist,Polynomial.map_sub,Polynomial.map_comp,P_map,Polynomial.map_pow,Polynomial.map_X]
theorem combo_map (f : ℤ[X]) : (combo f).map (Int.castRingHom ℂ) = combo (f.map (Int.castRingHom ℂ)) := by
  simp only [combo,twist,Polynomial.map_add,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_comp,
    Polynomial.map_pow,Polynomial.map_X, show (Int.castRingHom ℂ) (8:ℤ)=(8:ℂ) by norm_num,
    show (Int.castRingHom ℂ) (6:ℤ)=(6:ℂ) by norm_num]

theorem integer_cube {c m p r : ℕ} (hc : c=1 ∨ c=2) (hp : p.Prime) (hp5 : 5<p) :
    (J (p^(r+1)):ℤ[X])^3 ∣ combo (diff c m p r) := by
  have hm : (J (p^(r+1)):ℤ[X]).Monic := monic_geom_sum_X (pow_ne_zero _ hp.ne_zero)
  apply (Polynomial.map_dvd_map (Int.castRingHom ℂ) Int.cast_injective (hm.pow 3)).mp
  have hmap (t : ℕ) : (J t : ℤ[X]).map (Int.castRingHom ℂ)=J t := by simp [J,Polynomial.map_sum]
  rw [Polynomial.map_pow,hmap,combo_map,diff_map]
  exact combo_prime hc hp hp5

theorem scaled_dvd {c m p r : ℕ} (hc : c=1 ∨ c=2) (hp : p.Prime) (hp5 : 5<p) :
    ((p:ℤ)^(r+1))^3 ∣ 15*(c:ℤ)^2*((seq c (m*p^(r+1)):ℤ)-seq c (m*p^r)) := by
  obtain ⟨g,hg⟩ := integer_cube (m:=m) (r:=r) hc hp hp5
  refine ⟨g.eval 1,?_⟩
  have E := congrArg (Polynomial.eval (1:ℤ)) hg
  simp only [combo,diff,twist,eval_add,eval_sub,eval_mul,eval_C,eval_comp,eval_X,eval_pow,
    one_pow,P_at_one hc,J,eval_finsetSum,sum_const,card_range,nsmul_one,Nat.cast_pow] at E
  linear_combination E

end SunCubic

namespace SunCubic
open Finset

theorem cubic_dvd {c m p r : ℕ} (hc : c=1 ∨ c=2) (hp : p.Prime) (hp5 : 5<p) :
    ((p:ℤ)^(r+1))^3 ∣ (seq c (m*p^(r+1)):ℤ)-seq c (m*p^r) := by
  have h15 : p.Coprime 15 := by
    rw [show 15=3*5 by decide,Nat.coprime_mul_iff_right]
    exact ⟨hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) (by omega)),
      hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hp5)⟩
  have h2 : p.Coprime c := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (by rcases hc with rfl|rfl <;> decide) (by rcases hc with rfl|rfl <;> omega))
  have H : IsCoprime (p:ℤ) (15*(c:ℤ)^2) := by
    exact_mod_cast (h15.mul_right (h2.pow_right 2)).isCoprime
  have H' : IsCoprime (((p:ℤ)^(r+1))^3) (15*(c:ℤ)^2) := H.pow_left.pow_left
  exact H'.dvd_of_dvd_mul_left (scaled_dvd hc hp hp5)

theorem denominator {c p n : ℕ} (hc : c=1 ∨ c=2) (hp : p.Prime) (hp5 : 5<p) (hn : 0<n) :
    ¬p ∣ (((seq c (p*n):ℚ)-seq c n)/((p:ℚ)*n)^3).den := by
  obtain ⟨r,m,hm,he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.ne_one
  have N : n=m*p^r := he.trans (mul_comm ..)
  have pN : p*n=m*p^(r+1) := by rw [N,pow_succ]; ring
  obtain ⟨k,hk⟩ := cubic_dvd (m:=m) (r:=r) hc hp hp5
  rw [←pN,←N] at hk
  have Q : (seq c (p*n):ℚ)-seq c n=((p:ℚ)^(r+1))^3*k := by exact_mod_cast hk
  have hx : m≠0 := by intro e; simp [e] at N; omega
  have hp0 : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  have hm0 : (m:ℚ)≠0 := by exact_mod_cast hx
  have H : ((seq c (p*n):ℚ)-seq c n)/((p:ℚ)*n)^3 = Rat.divInt k ((m:ℤ)^3) := by
    rw [Q,N,Rat.divInt_eq_div]
    push_cast
    field_simp
    ring
  rw [H]
  intro h
  have D := Rat.den_dvd k ((m:ℤ)^3)
  have dvd : p ∣ m^3 := by
    exact_mod_cast (dvd_trans (show (p:ℤ) ∣ (↑(Rat.divInt k ((m:ℤ)^3)).den:ℤ) by exact_mod_cast h) D)
  exact hm (hp.dvd_of_dvd_pow dvd)

end SunCubic

theorem OMA.solution : type_of% @OMA.S_oeis_a278405.main := by
  intro p n hp hp5 hn
  have H (j : ℕ) (hj : 0<j) : OMA.S_oeis_a278405.a j = SunCubic.seq 2 j := by
    simp [OMA.S_oeis_a278405.a,SunCubic.seq,Finset.sum_range_succ,
      Nat.choose_eq_zero_of_lt (show j<2*j by omega)]
  rw [H _ (Nat.mul_pos hp.pos hn),H _ hn]
  exact SunCubic.denominator (Or.inr rfl) hp hp5 hn
