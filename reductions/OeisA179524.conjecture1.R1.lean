import FormalConjectures.OEIS.«179524»
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# A reduction of the principal split-prime congruence for A179524

The two finite Clausen squares differ by a first-order shift of the
hypergeometric parameters. Their Wronskian gives a differential equation over
the field modulo p for the correction. The remaining inputs are the ordinary
binomial evaluation and the point evaluation of this correction.

The binomial collapse and the shifted symmetric square are adapted from
@MrSeizy's merged A179524 conjecture 3 proof, which credits the factorial
cancellation method of @rleshner.
-/

namespace OMA
open Finset Nat

private lemma convolution (m k N : ℕ) :
    ∑ i ∈ range (N + 1), (i + m).choose m * (N - i + k).choose k =
      (N + m + k + 1).choose (m + k + 1) := by
  induction k generalizing N with
  | zero => simpa using Nat.sum_range_add_choose N m
  | succ k ih =>
    induction N with
    | zero => simp [Nat.add_assoc]
    | succ N jh =>
      rw [sum_range_succ]
      have eq (i : ℕ) (hi : i ∈ range (N + 1)) :
          (N + 1 - i + (k + 1)).choose (k + 1) =
            (N - i + (k + 1)).choose (k + 1) + (N + 1 - i + k).choose k := by
        rw [show N + 1 - i + (k + 1) = (N + 1 - i + k) + 1 by omega,
          Nat.choose_succ_succ', add_comm]
        congr 2
        simp only [mem_range] at hi
        omega
      rw [sum_congr rfl (show ∀ i ∈ range (N + 1),
          (i + m).choose m * (N + 1 - i + (k + 1)).choose (k + 1) =
           (i + m).choose m * (N - i + (k + 1)).choose (k + 1) +
           (i + m).choose m * (N + 1 - i + k).choose k from fun i hi => by rw [eq i hi, mul_add])]
      simp only [Nat.sub_self, Nat.zero_add, Nat.choose_self, mul_one]
      rw [sum_add_distrib, jh, add_assoc]
      have hh := ih (N + 1)
      rw [sum_range_succ] at hh
      simp only [Nat.sub_self, Nat.zero_add, Nat.choose_self, mul_one] at hh
      -- The final index in the second convolution contributes its own boundary term.
      rw [hh]
      rw [show N + 1 + m + (k + 1) + 1 = (N + m + (k + 1) + 1) + 1 by omega,
        show m + (k + 1) + 1 = (m + k + 1) + 1 by omega, Nat.choose_succ_succ', add_comm]
      congr 1 <;> congr 1 <;> omega


private lemma choose_mul_factorial_prod {R : Type*} [CommRing R] {n m : ℕ} (hm : m ≤ n) :
    (m.factorial : R) * (n.choose m : R) = ∏ i ∈ range m, ((n : R) - (i : R)) := by
  rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range,
    Nat.cast_prod]
  exact prod_congr rfl fun i hi => Nat.cast_sub (by have := mem_range.mp hi; omega)

private lemma choose_reflect (p m n : ℕ) (hp : p.Prime) (hm : m < p)
    (hn : n ∈ Ico m p) (he : Even m) :
    (n.choose m : ZMod p) = ((p + m - 1 - n).choose m : ZMod p) := by
  have hn' := mem_Ico.mp hn
  have hunit : IsUnit (m.factorial : ZMod p) := by
    have h := ZMod.coe_mul_inv_eq_one m.factorial (hp.coprime_factorial_of_lt hm).symm
    exact ⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, rfl⟩
  apply hunit.mul_left_cancel
  rw [choose_mul_factorial_prod hn'.1, choose_mul_factorial_prod (by omega)]
  rw [← prod_range_reflect (fun i => ((n : ZMod p) - (i : ZMod p))) m]
  have hsign : (∏ i ∈ range m, -((n : ZMod p) - (↑(m - 1 - i) : ZMod p))) =
      ∏ i ∈ range m, ((n : ZMod p) - (↑(m - 1 - i) : ZMod p)) := by
    rw [prod_neg, card_range, he.neg_one_pow, one_mul]
  rw [← hsign]
  apply prod_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  push_cast [show i ≤ m - 1 by omega, show 1 ≤ m by omega,
    show n ≤ p + m - 1 by omega, show 1 ≤ p + m by omega]
  rw [ZMod.natCast_self]
  ring

/-- Reflect the index over the interval on which both binomials are supported.
The difference between the square sum and the reflected convolution is half
the sum of squared differences. -/
private lemma choose_square_sum (p m : ℕ) (hp : p.Prime) (hp2 : 2 < p) (hm : m < p)
    (he : Even m) :
    (∑ n ∈ range p, (n.choose m : ZMod (p ^ 2)) ^ 2) = ((p + m).choose (2 * m + 1) : ℕ) := by
  let R := ZMod (p ^ 2)
  let b (n : ℕ) : R := n.choose m
  let r (n : ℕ) := p + m - 1 - n
  have hr : ∀ n ∈ Ico m p, r n ∈ Ico m p := by
    intro n hn
    simp only [mem_Ico, r] at *
    omega
  have hr2 : ∀ n ∈ Ico m p, r (r n) = n := by
    intro n hn
    simp only [mem_Ico, r] at *
    omega
  have hsq (n : ℕ) (hn : n ∈ Ico m p) : (b n - b (r n)) ^ 2 = 0 := by
    have h := choose_reflect p m n hp hm hn he
    have hdvd : (p : ℤ) ∣ (n.choose m : ℤ) - ((r n).choose m : ℤ) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      exact sub_eq_zero.mpr h
    obtain ⟨d, hd⟩ := hdvd
    have hx : (b n - b (r n)) = (p : R) * (d : R) := by
      dsimp [R, b]
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using
        congrArg (fun x : ℤ => (x : ZMod (p ^ 2))) hd
    rw [hx, mul_pow]
    rw [← Nat.cast_pow, ZMod.natCast_self, zero_mul]
  have hsum : (∑ n ∈ Ico m p, b (r n) ^ 2) = ∑ n ∈ Ico m p, b n ^ 2 :=
    sum_nbij' r r hr hr hr2 hr2 (fun _ _ => rfl)
  have hb : (∑ n ∈ range p, b n ^ 2) = ∑ n ∈ Ico m p, b n ^ 2 := by
    symm
    apply sum_subset
    · intro n hn
      exact mem_range.mpr (mem_Ico.mp hn).2
    · intro n hn hnm
      have h : n < m := by simpa [mem_Ico, mem_range.mp hn] using hnm
      simp [b, Nat.choose_eq_zero_of_lt h]
  have hc : (∑ n ∈ Ico m p, b n * b (r n)) = ((p + m).choose (2 * m + 1) : R) := by
    rw [sum_Ico_eq_sum_range]
    have hlen : p - m = (p - m - 1) + 1 := by omega
    rw [hlen]
    have eq (i : ℕ) (hi : i ∈ range (p - m - 1 + 1)) : r (m + i) = (p - m - 1) - i + m := by
      simp only [r, mem_range] at *
      omega
    rw [sum_congr rfl (fun i hi => show b (m+i) * b (r (m+i)) =
      ((m+i).choose m * (p-m-1-i+m).choose m : ℕ) by simp [R, b, eq i hi]), ← Nat.cast_sum]
    rw [show (∑ x ∈ range (p - m - 1 + 1), (m + x).choose m *
          (p - m - 1 - x + m).choose m) =
          ((p - m - 1) + m + m + 1).choose (m + m + 1) from by
      simpa only [add_comm m] using convolution m m (p - m - 1)]
    congr 2 <;> omega
  change (∑ n ∈ range p, b n ^ 2) = _
  rw [hb, ← hc]
  have ht := sum_congr rfl hsq
  simp only [sum_const_zero] at ht
  have exp (n : ℕ) : (b n - b (r n)) ^ 2 = b n ^ 2 + b (r n) ^ 2 - 2 * (b n * b (r n)) := by ring
  simp_rw [exp, sum_sub_distrib, sum_add_distrib, ← mul_sum, hsum, ← two_mul] at ht
  have hc2 : (2 : ℕ).Coprime (p ^ 2) := (Nat.coprime_of_lt_prime (by decide) hp2 hp).symm.pow_right 2
  have hu2 : IsUnit (2 : R) := by
    obtain h := ZMod.coe_mul_inv_eq_one 2 hc2
    exact ⟨⟨2, _, h, by rw [mul_comm]; exact h⟩, rfl⟩
  apply hu2.mul_left_cancel
  exact sub_eq_zero.mp ht

private lemma collapse (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    (∑ n ∈ range p, (OeisA179524.a n : ZMod (p ^ 2))) =
      ∑ k ∈ range ((p - 1) / 2 + 1), (-4 : ZMod (p ^ 2)) ^ k *
        ((2 * k).choose k : ZMod (p ^ 2)) ^ 2 * ((p + 2 * k).choose (4 * k + 1) : ℕ) := by
  let R := ZMod (p ^ 2)
  let h := (p - 1) / 2 + 1
  have ha (n : ℕ) (hn : n < p) :
      (OeisA179524.a n : R) =
        ∑ k ∈ range h, (-4 : R) ^ k * ((2 * k).choose k : R) ^ 2 * (n.choose (2 * k) : R) ^ 2 := by
    dsimp [R]
    simp only [OeisA179524.a, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_ofNat, Int.cast_natCast]
    have he (k : ℕ) :
        (-4 : R) ^ k * (n.choose k : R) ^ 2 * ((n - k).choose k : R) ^ 2 =
          (-4 : R) ^ k * ((2 * k).choose k : R) ^ 2 * (n.choose (2 * k) : R) ^ 2 := by
      have hx := Nat.choose_mul (n := n) (k := 2 * k) (s := k) (by omega)
      rw [show 2 * k - k = k by omega] at hx
      dsimp [R]
      have hx' := congrArg (fun x : ℕ => (x : ZMod (p ^ 2))) hx
      simp only [Nat.cast_mul] at hx'
      linear_combination ((-4 : R) ^ k * ((n.choose (2 * k) : R) * ((2 * k).choose k : R) +
        (n.choose k : R) * ((n-k).choose k : R))) * (-hx')
    simp_rw [he]
    rcases le_total (n + 1) h with hh | hh
    · apply sum_subset (range_mono hh)
      intro k hk hk'
      have hnk : n < 2 * k := by simp only [mem_range, not_lt] at hk'; omega
      simp [Nat.choose_eq_zero_of_lt hnk]
    · symm
      apply sum_subset (range_mono hh)
      intro k hk hk'
      have hnk : n < 2 * k := by dsimp [h] at hk'; simp only [mem_range, not_lt] at hk'; omega
      simp [Nat.choose_eq_zero_of_lt hnk]
  rw [sum_congr rfl (fun n hn => ha n (mem_range.mp hn)), sum_comm]
  apply sum_congr rfl
  intro k hk
  change k ∈ range h at hk
  rw [← mul_sum, choose_square_sum p (2 * k) hp hp2 (by
    dsimp [h] at hk; simp only [mem_range] at hk; omega) ⟨k, by omega⟩]
  congr 3
  omega

end OMA

namespace OMA
open Nat Finset

private abbrev R2 (p : ℕ) := ZMod (p^2)

private def red (p : ℕ) : R2 p →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by decide)) _

private lemma p_sq_zero (p : ℕ) : (p : R2 p) ^ 2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

private lemma unit_red {p : ℕ} (hp : p.Prime) {x : R2 p} (hx : red p x ≠ 0) : IsUnit x := by
  letI : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide)]
  intro hd
  apply hx
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [map_natCast, ZMod.natCast_eq_zero_iff]
  exact hd

private lemma red_kern {p : ℕ} (hp : p.Prime) {x : R2 p} (hx : red p x = 0) :
    ∃ d : R2 p, x = (p : R2 p) * d := by
  letI : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, map_natCast, ZMod.natCast_eq_zero_iff] at hx
  obtain ⟨d, hd⟩ := hx
  refine ⟨d, ?_⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x, hd, Nat.cast_mul]

private lemma unit_small {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n) (hnp : n < p) :
    IsUnit (n : R2 p) := by
  apply unit_red hp
  rw [map_natCast]
  intro hz
  exact Nat.not_dvd_of_pos_of_lt hn hnp ((ZMod.natCast_eq_zero_iff n p).mp hz)

private def half (p : ℕ) : R2 p := (2 : R2 p)⁻¹
private def pa (p : ℕ) : R2 p := (1-2*(p : R2 p)) * half p ^ 2
private def pb (p : ℕ) : R2 p := (3-2*(p : R2 p)) * half p ^ 2
private def pc (p : ℕ) : R2 p := 1-(p : R2 p) * half p

private lemma two_half {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) : 2 * half p = 1 :=
  ZMod.mul_inv_of_unit _ (unit_small hp (by decide : 0 < 2) hp2)

private lemma param_sums {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p = 2*h+1) :
    pa p + pb p = 2 * pc p - 1 ∧ 2 * (-(h : R2 p)) = 2 * pc p - 1 := by
  have hi := two_half hp hp2
  have hP : (p : R2 p) = 2 * (h : R2 p) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      congrArg (fun n : ℕ => (n : R2 p)) hh
  constructor
  · unfold pa pb pc
    linear_combination ((1 - (p : R2 p)) * (2 * half p + 1) + (p : R2 p)) * hi
  · unfold pc
    linear_combination (p : R2 p) * hi + hP

private lemma choose_move (u w : ℕ) :
    (u+w+2).choose (u+2) * ((u+1)*(u+2)*(u+w+4)*(u+w+3)) =
      (u+w+4).choose u * ((w+4)*(w+3)*(w+2)*(w+1)) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show u+2 ≤ u+w+2 by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show u ≤ u+w+4 by omega)
  rw [show u+w+2-(u+2)=w by omega, Nat.factorial_succ, Nat.factorial_succ u] at h1
  rw [show u+w+4-u=w+4 by omega, Nat.factorial_succ (w+3), Nat.factorial_succ (w+2),
    Nat.factorial_succ (w+1), Nat.factorial_succ w,
    Nat.factorial_succ (u+w+3), Nat.factorial_succ (u+w+2), ← h1] at h2
  have he : (u+w+2).choose (u+2) * ((u+1)*(u+2)*(u+w+4)*(u+w+3)) *
      (u.factorial*w.factorial) =
      (u+w+4).choose u * ((w+4)*(w+3)*(w+2)*(w+1)) * (u.factorial*w.factorial) := by
    push_cast at h2
    convert h2.symm using 1 <;> ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) he

private def weight (p h j : ℕ) : R2 p :=
  (-4)^(h-j) * ((2*(h-j)).choose (h-j) : ℕ)^2 * ((p+2*(h-j)).choose (2*j) : ℕ) * (-16)^j

/-- The reversed summand, multiplied by $(-16)^j$, satisfies the recurrence
at the polynomial argument $X(1-X)$. The cancellation uses
$(p-v)^2 = -v(2p-v)$ in the ring modulo $p^2$. -/
private lemma weight_recurrence {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p = 2*h+1)
    (j : ℕ) (hj : j < h) :
    ((j : R2 p)+1)*((j : R2 p)+pc p)*((j : R2 p)+2*pc p-1)*weight p h (j+1) =
      4*((j : R2 p)+pa p)*((j : R2 p)+pb p)*((j : R2 p)-(h : R2 p))*weight p h j := by
  let J : R2 p := j
  let P : R2 p := p
  let v : R2 p := 2*J+1
  let w : R2 p := v+1
  let A : R2 p := (2*(h-j-1)).choose (h-j-1)
  let B : R2 p := (2*(h-j)).choose (h-j)
  let D : R2 p := (p+2*(h-j-1)).choose (2*(j+1))
  let E : R2 p := (p+2*(h-j)).choose (2*j)
  have hP : P = 2*(h : R2 p)+1 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      congrArg (fun n : ℕ => (n : R2 p)) hh
  have hC : 4*(P-w)*A = (P-v)*B := by
    have he := Nat.succ_mul_centralBinom_succ (h-j-1)
    rw [show h-j-1+1 = h-j by omega] at he
    have he' := congrArg (fun n : ℕ => (n : R2 p)) he
    simp only [Nat.centralBinom, Nat.cast_mul, Nat.cast_add, Nat.cast_sub (by omega : j ≤ h),
      Nat.cast_sub (by omega : 1 ≤ h-j), Nat.cast_one, Nat.cast_ofNat] at he'
    change ((h : R2 p) - J) * B = 2 * (2*((h : R2 p)-J-1)+1)*A at he'
    dsimp [w, v]
    linear_combination -2*he' + ((4*A)-B) * hP
  let z := p+2*(h-j)-2*j-4
  have hD : D * (v*w*(2*P-v)*(2*P-w)) =
      E * ((2*P-4*J-1)*(2*P-4*J-3)*4*(P-v)*(P-w)) := by
    have he := choose_move (2*j) z
    have hz : 2*j+z+2 = p+2*(h-j-1) := by dsimp [z]; omega
    have hz' : 2*j+z+4 = p+2*(h-j) := by dsimp [z]; omega
    have hz'' : 2*j+z+3 = p+2*(h-j)-1 := by dsimp [z]; omega
    rw [hz, hz', hz''] at he
    have he' := congrArg (fun n : ℕ => (n : R2 p)) he
    have hzcast : (z : R2 p) = P+2*((h : R2 p)-J)-2*J-4 := by
      dsimp [z, P, J]
      push_cast [show 2*j ≤ p+2*(h-j) by omega, show 4 ≤ p+2*(h-j)-2*j by omega,
        show j ≤ h by omega]
      ring
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      show 2*j+2=2*(j+1) by omega, Nat.cast_sub (by omega : 1 ≤ p+2*(h-j)),
      Nat.cast_sub (by omega : j ≤ h), hzcast] at he'
    change D*( (2*J+1)*(2*(J+1))*(P+2*((h : R2 p)-J))*(P+2*((h : R2 p)-J)-1)) =
      E*((P+2*((h : R2 p)-J)-2*J-4+4)*(P+2*((h : R2 p)-J)-2*J-4+3)*
        (P+2*((h : R2 p)-J)-2*J-4+2)*(P+2*((h : R2 p)-J)-2*J-4+1)) at he'
    dsimp [w, v]
    have hr (X : R2 p) : 2*((h : R2 p)-X) = P-1-2*X := by linear_combination -hP
    rw [hr J] at he'
    linear_combination he'
  have hhj : h-j = h-j-1+1 := by omega
  let L : R2 p := (-4)^(h-j-1) * (-16)^j
  have hW1 : weight p h (j+1) = -16*L*A^2*D := by
    unfold weight
    simp only [show h-(j+1)=h-j-1 by omega, pow_succ (-16 : R2 p) j]
    dsimp [L, A, D]
    ring
  have hW0 : weight p h j = -4*L*B^2*E := by
    change (-4 : R2 p)^(h-j)*B^2*E*(-16)^j = _
    rw [show (-4 : R2 p)^(h-j) = (-4)^(h-j-1)*(-4) by rw [← pow_succ, ← hhj]]
    dsimp [L]
    ring
  letI : Fact p.Prime := ⟨hp⟩
  have hv : IsUnit v := by
    dsimp [v, J]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      unit_small hp (by omega : 0 < 2*j+1) (by omega : 2*j+1 < p)
  have hredP : red p P = 0 := (map_natCast (red p) p).trans (ZMod.natCast_self p)
  have hu : IsUnit (2*P-v) := by
    apply unit_red hp
    rw [map_sub, map_mul, hredP, mul_zero, zero_sub, neg_ne_zero]
    exact (hv.map (red p)).ne_zero
  have hw : IsUnit (P-w) := by
    apply unit_red hp
    have hww : IsUnit w := by
      dsimp [w,v,J]
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
        unit_small hp (by omega : 0 < 2*j+1+1) (by omega : 2*j+1+1 < p)
    rw [map_sub, hredP, zero_sub, neg_ne_zero]
    exact (hww.map (red p)).ne_zero
  have hpv : (P-v)^2 = -(v*(2*P-v)) := by
    have hz : P^2 = 0 := p_sq_zero p
    linear_combination hz
  have hrec : (P-w)*w*(2*P-w)*weight p h (j+1) =
      (v-P)*(2*P-4*J-1)*(2*P-4*J-3)*weight p h j := by
    rw [hW1, hW0]
    apply (hv.mul hu).mul_left_cancel
    apply hw.mul_left_cancel
    have hC2 : (4*(P-w)*A)^2 = ((P-v)*B)^2 := congrArg (fun x : R2 p => x^2) hC
    linear_combination (-16*L*A^2*(P-w)^2)*hD -
      (4*L*E*(2*P-4*J-1)*(2*P-4*J-3)*(P-v)*(P-w)) * (hC2+B^2*hpv)
  have hi := two_half hp hp2
  have k1 : 2*(J+1)=w := by dsimp [w,v]; ring
  have k2 : 2*(J+pc p)=w-P := by
    unfold pc
    linear_combination k1 - P*hi
  have k3 : 2*(J+2*pc p-1)=w-2*P := by
    unfold pc
    linear_combination k1 - 2*P*hi
  have k4 : 4*(J+pa p)=4*J+1-2*P := by
    unfold pa
    linear_combination (1-2*P)*(2*half p+1)*hi
  have k5 : 4*(J+pb p)=4*J+3-2*P := by
    unfold pb
    linear_combination (3-2*P)*(2*half p+1)*hi
  have k6 : 2*(J-(h : R2 p))=v-P := by
    dsimp [v]
    linear_combination hP
  apply ((unit_small hp (by decide : 0 < 2) hp2).pow 3).mul_left_cancel
  calc
    _ = (2*(J+1))*(2*(J+pc p))*(2*(J+2*pc p-1))*weight p h (j+1) := by ring
    _ = (4*(J+pa p))*(4*(J+pb p))*(2*(J-(h : R2 p)))*weight p h j := by
      rw [k1,k2,k3,k4,k5,k6]
      linear_combination hrec
    _ = _ := by ring

end OMA

namespace OMA
open Polynomial Finset

section Operators
variable {R : Type*} [CommRing R]

private noncomputable def theta (P : R[X]) : R[X] := X * derivative P
private noncomputable def step (a : R) (P : R[X]) : R[X] := theta P + C a * P
private noncomputable def delta : R[X] := X * (1 - X)
private noncomputable def ell : R[X] := 1 - 2 * X

private lemma theta_coeff (P : R[X]) (n : ℕ) :
    (theta P).coeff n = (n : R) * P.coeff n := by
  cases n with
  | zero => simp [theta]
  | succ n => rw [theta, coeff_X_mul, coeff_derivative, mul_comm, Nat.cast_add, Nat.cast_one]

private lemma step_coeff (a : R) (P : R[X]) (n : ℕ) :
    (step a P).coeff n = ((n : R) + a) * P.coeff n := by
  rw [step, coeff_add, theta_coeff, coeff_C_mul, add_mul]

private noncomputable def odeT (a b c : R) (T : R[X]) : R[X] :=
  theta (step (c - 1) T) - X * step a (step b T)

private noncomputable def odeY (a b c d : R) (Y : R[X]) : R[X] :=
  theta (step (c - 1) (step (2*c - 2) Y)) - C 4 * X * step a (step b (step d Y))

private noncomputable def odeS (q c : R) (S : R[X]) : R[X] :=
  (1-X)^2 * theta (step (-1) (step (-2) S)) +
    C (3*c) * (1-X) * ell * theta (step (-1) S) +
    (C (2*c^2-c) * ell^2 + C (-2*c-4*q) * delta) * theta S +
    C ((2-4*c)*q) * X * ell * S

private lemma odeT_deriv (a b c : R) (hab : a+b = 2*c-1) (T : R[X]) :
    odeT a b c T = X * (delta * derivative (derivative T) +
      C c * ell * derivative T - C (a*b) * T) := by
  simp [odeT, step, theta, delta, ell, derivative_add, derivative_mul,
    derivative_C, derivative_X, map_sub, map_add, map_one, map_ofNat, C_eq_natCast]
  have h := congrArg (C : R → R[X]) hab
  simp [map_add, map_sub, map_mul, map_ofNat] at h
  linear_combination -(X^2 * derivative T) * h

private lemma odeS_deriv (q c : R) (S : R[X]) :
    odeS q c S = X * (delta^2 * derivative (derivative (derivative S)) +
      C (3*c) * delta * ell * derivative (derivative S) +
      (C (2*c^2-c) * ell^2 + C (-2*c-4*q) * delta) * derivative S +
      C ((2-4*c)*q) * ell * S) := by
  simp [odeS, step, theta, delta, ell, derivative_add, derivative_mul,
    derivative_C, derivative_X, map_sub, map_add, map_one, map_neg, map_pow, map_ofNat, C_eq_natCast]
  ring

private lemma odeS_square (a b c : R) (hab : a+b = 2*c-1) (T : R[X]) :
    odeS (a*b) c (T^2) = 2*(1-X)*T*theta (odeT a b c T) +
      (6*(1-X)*theta T + 2*C (2*c-1)*ell*T - 2*(1-X)*T) * odeT a b c T := by
  rw [odeS_deriv, odeT_deriv a b c hab]
  simp only [pow_two T]
  simp [theta, delta, ell, derivative_add, derivative_sub, derivative_mul,
    derivative_C, derivative_X, map_sub, map_add, map_one, map_neg,
    map_pow, map_ofNat, C_eq_natCast]
  ring

private lemma odeY_deriv (a b c d : R) (hab : a+b = 2*c-1) (hd : 2*d = 2*c-1) (Y : R[X]) :
    odeY a b c d Y = X * (
      X^2*(1-4*X)*derivative (derivative (derivative Y)) +
      (C (3*c)*X*(1-4*X)-6*X^2)*derivative (derivative Y) +
      (C (2*c^2-c)*(1-4*X)-C (8*c+4*a*b)*X)*derivative Y +
      C ((2-4*c)*(a*b))*Y) := by
  simp [odeY, step, theta, derivative_add, derivative_mul,
    derivative_C, derivative_X, map_sub, map_add, map_one, map_neg, map_pow,
    map_ofNat, C_eq_natCast]
  have h1 := congrArg (C : R → R[X]) hab
  have h2 := congrArg (C : R → R[X]) hd
  simp [map_add, map_sub, map_one, map_mul, map_ofNat, C_eq_natCast] at h1 h2
  linear_combination
    (-4*X^3*derivative (derivative Y) - 4*C d*X^2*derivative Y - 4*X^2*derivative Y) * h1 +
    (-2*X^3*derivative (derivative Y) - 4*C c*X^2*derivative Y -
      2*C a*C b*X*Y) * h2

private lemma odeS_comp (a b c d : R) (hab : a+b = 2*c-1) (hd : 2*d = 2*c-1) (Y : R[X]) :
    (1-X)*odeS (a*b) c (Y.comp delta) = ell * (odeY a b c d Y).comp delta := by
  rw [odeS_deriv, odeY_deriv a b c d hab hd]
  simp [delta, ell, derivative_comp, derivative_mul, derivative_sub, derivative_add,
    derivative_X, derivative_one, derivative_C, mul_comp, add_comp, sub_comp, pow_comp,
    C_comp, X_comp, one_comp, map_ofNat]
  ring

private lemma coeff_mul_initial (P Q : R[X]) (n : ℕ) (hq : ∀ j < n, Q.coeff j = 0) :
    (P*Q).coeff n = P.coeff 0 * Q.coeff n := by
  rw [coeff_mul, sum_eq_single (0,n)]
  · rintro ⟨i,j⟩ hij hne
    simp only [HasAntidiagonal.mem_antidiagonal] at hij
    rw [hq j (by
      by_contra! hn
      exact hne (Prod.ext (by omega) (by omega))), mul_zero]
  · simp

private lemma odeS_initial (q c : R) (P : R[X]) (n : ℕ)
    (hp : ∀ j < n, P.coeff j = 0) :
    ((1-X)*odeS q c P).coeff n =
      ((n : R) * ((n : R)+c-1) * ((n : R)+2*c-2)) * P.coeff n := by
  have hz (k : ℕ) (hk : k ≤ n) (P0 : R[X])
      (hP0 : ∀ j < k, P0.coeff j = 0) :
      (odeS q c P0).coeff k =
        ((k : R) * ((k : R)+c-1) * ((k : R)+2*c-2)) * P0.coeff k := by
    have hs : ∀ a b (j : ℕ), j < k → (theta (step a (step b P0))).coeff j = 0 := by
      intro a b j hj
      simp [theta_coeff, step_coeff, hP0 j hj]
    have hs' : ∀ a (j : ℕ), j < k → (theta (step a P0)).coeff j = 0 := by
      intro a j hj
      simp [theta_coeff, step_coeff, hP0 j hj]
    have ht : ∀ j < k, (theta P0).coeff j = 0 := by
      intro j hj
      simp [theta_coeff, hP0 j hj]
    simp only [odeS, coeff_add]
    rw [coeff_mul_initial _ _ _ (hs _ _), coeff_mul_initial _ _ _ (hs' _),
      coeff_mul_initial _ _ _ ht, coeff_mul_initial _ _ _ hP0]
    simp [delta, ell, coeff_zero_eq_eval_zero, theta_coeff, step_coeff]
    ring
  rw [coeff_mul_initial _ _ _ (fun j hj => by
    rw [hz j (by omega) P (fun i hi => hp i (by omega)), hp j hj, mul_zero]), hz n le_rfl P hp]
  simp [coeff_zero_eq_eval_zero]

private lemma odeS_C_mul (q c k : R) (P : R[X]) :
    odeS q c (C k * P) = C k * odeS q c P := by
  simp [odeS, theta, step, derivative_mul, derivative_C]
  ring

private lemma odeS_sub (q c : R) (P Q : R[X]) :
    odeS q c (P-Q) = odeS q c P - odeS q c Q := by
  simp [odeS, theta, step, derivative_sub]
  ring

private lemma theta_dvd (P : R[X]) {p : ℕ} (hp : X^p ∣ P) : X^p ∣ theta P := by
  rw [X_pow_dvd_iff] at hp ⊢
  intro n hn
  rw [theta_coeff, hp n hn, mul_zero]

/-- The symmetric square and the quadratic substitution satisfy the same
coefficient recursion through degree $p-1$. This proves the finite form
of Clausen's square identity used here. -/
private lemma clausal_square (a b c d k : R) (hab : a+b = 2*c-1) (hd : 2*d = 2*c-1)
    (p : ℕ) (T Y : R[X]) (h0 : (Y.comp delta).coeff 0 = k * (T^2).coeff 0)
    (hu : ∀ n : ℕ, 0 < n → n < p → IsUnit (((n : R) * ((n : R)+c-1) * ((n : R)+2*c-2))))
    (ht : X^p ∣ odeT a b c T) (hy : odeY a b c d Y = 0)
    (htdeg : (T^2).natDegree < p) (hydeg : (Y.comp delta).natDegree < p) :
    Y.comp delta = C k * T^2 := by
  have hs : X^p ∣ (1-X)*odeS (a*b) c (T^2) := by
    rw [odeS_square a b c hab]
    exact dvd_mul_of_dvd_right (dvd_add
      (dvd_mul_of_dvd_right (theta_dvd _ ht) _)
      (dvd_mul_of_dvd_right ht _)) _
  have hy' : (1-X)*odeS (a*b) c (Y.comp delta) = 0 := by
    rw [odeS_comp a b c d hab hd, hy, zero_comp, mul_zero]
  let P := Y.comp delta - C k * T^2
  have hz : X^p ∣ (1-X)*odeS (a*b) c P := by
    change X^p ∣ (1-X)*odeS (a*b) c (Y.comp delta - C k * T^2)
    rw [odeS_sub, mul_sub, hy', zero_sub, odeS_C_mul,
      show (1-X)* (C k * odeS (a*b) c (T^2)) = C k * ((1-X)*odeS (a*b) c (T^2)) by ring]
    exact dvd_neg.mpr (dvd_mul_of_dvd_right hs _)
  rw [X_pow_dvd_iff] at hz
  have hall (n : ℕ) : P.coeff n = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < p
      · by_cases hn0 : n = 0
        · subst n
          simpa [P, coeff_sub, coeff_C_mul, h0]
        · have h := hz n hn
          rw [odeS_initial _ _ _ _ ih] at h
          exact (hu n (by omega) hn).mul_left_cancel (by simpa using h)
      · simp [P, coeff_sub, coeff_C_mul, coeff_eq_zero_of_natDegree_lt (show (Y.comp delta).natDegree < n by omega),
          coeff_eq_zero_of_natDegree_lt (show (T^2).natDegree < n by omega)]
  exact sub_eq_zero.mp (Polynomial.ext fun n => by simpa [P] using hall n)

private noncomputable def polyOf (N : ℕ) (f : ℕ → R) : R[X] :=
  ∑ i ∈ range N, monomial i (f i)

private lemma polyOf_coeff (N : ℕ) (f : ℕ → R) (n : ℕ) :
    (polyOf N f).coeff n = if n < N then f n else 0 := by
  rw [polyOf, finsetSum_coeff]
  by_cases h : n < N
  · rw [if_pos h, sum_eq_single n, coeff_monomial_same]
    · intro b hb hbn
      simp [coeff_monomial, hbn, Ne.symm hbn]
    · simp [h]
  · rw [if_neg h]
    apply sum_eq_zero
    intro i hi
    have hni : i ≠ n := by have := mem_range.mp hi; omega
    simp [coeff_monomial, hni, Ne.symm hni]

private lemma polyOf_odeT (a b c : R) (p : ℕ) (f : ℕ → R)
    (hf : ∀ n, n+1 < p →
      ((n : R)+1)*((n : R)+c)*f (n+1) = ((n : R)+a)*((n : R)+b)*f n) :
    X^p ∣ odeT a b c (polyOf p f) := by
  rw [X_pow_dvd_iff]
  intro n hn
  rw [odeT, coeff_sub, theta_coeff]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_X_mul, step_coeff, step_coeff, step_coeff, polyOf_coeff, polyOf_coeff,
      if_pos hn, if_pos (by omega : n < p), Nat.cast_add, Nat.cast_one]
    rw [show (n : R) + 1 + (c-1) = (n : R)+c by ring]
    linear_combination hf n hn

private lemma polyOf_odeY (a b c d : R) (h : ℕ) (f : ℕ → R) (hd : d = -(h : R))
    (hf : ∀ n < h, ((n : R)+1)*((n : R)+c)*((n : R)+2*c-1)*f (n+1) =
      4*((n : R)+a)*((n : R)+b)*((n : R)+d)*f n) :
    odeY a b c d (polyOf (h+1) f) = 0 := by
  ext n
  rw [odeY, coeff_sub, theta_coeff, coeff_zero, mul_assoc, coeff_C_mul]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_X_mul, step_coeff, step_coeff, step_coeff, step_coeff, step_coeff,
      polyOf_coeff, polyOf_coeff, Nat.cast_add, Nat.cast_one]
    rcases lt_trichotomy n h with hn | rfl | hn
    · rw [if_pos (by omega : n+1 < h+1), if_pos (by omega : n < h+1)]
      linear_combination hf n hn
    · simp [hd]
    · rw [if_neg (by omega : ¬ n+1 < h+1), if_neg (by omega : ¬ n < h+1)]
      ring

end Operators
end OMA

namespace OMA
open Polynomial Finset

private abbrev Quadr (R : Type*) [CommRing R] := QuadraticAlgebra R (5 : R) 0

private def quadMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    Quadr R →+* Quadr S where
  toFun x := ⟨f x.re, f x.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by ext <;> simp
  map_mul' x y := by
    rcases x with ⟨a,b⟩
    rcases y with ⟨c,d⟩
    simp [QuadraticAlgebra.mk_mul_mk, map_ofNat]

private lemma quad_omega_sq (R : Type*) [CommRing R] : (QuadraticAlgebra.omega : Quadr R)^2 = 5 := by
  rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  simp [map_ofNat]

private def tCoef (p n : ℕ) : R2 p :=
  ((∏ j ∈ range n, ((j : R2 p) + pa p)) *
    (∏ j ∈ range n, ((j : R2 p) + pb p))) *
    ∏ j ∈ range n, (((j : R2 p)+1)*((j : R2 p)+pc p))⁻¹

private lemma pc_red (p : ℕ) : red p (pc p) = 1 := by
  simp [pc, map_sub, map_mul, map_natCast]

private lemma t_recurrence {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : n+1 < p) :
    ((n : R2 p)+1)*((n : R2 p)+pc p)*tCoef p (n+1) =
      ((n : R2 p)+pa p)*((n : R2 p)+pb p)*tCoef p n := by
  have h : IsUnit (((n : R2 p)+1)*((n : R2 p)+pc p)) := by
    apply unit_red hp
    rw [map_mul, map_add, map_add, map_natCast, map_one, pc_red]
    have h' : (n : ZMod p)+1 ≠ 0 := by
      rw [← Nat.cast_one, ← Nat.cast_add]
      exact fun hz => Nat.not_dvd_of_pos_of_lt (by omega) hn ((ZMod.natCast_eq_zero_iff _ _).mp hz)
    letI : Fact p.Prime := ⟨hp⟩
    exact mul_ne_zero h' h'
  simp only [tCoef, prod_range_succ]
  rw [show ((n : R2 p)+1)*((n : R2 p)+pc p) *
      (((∏ j ∈ range n, ((j : R2 p) + pa p)) * ((n : R2 p) + pa p)) *
        ((∏ j ∈ range n, ((j : R2 p) + pb p)) * ((n : R2 p) + pb p)) *
        ((∏ j ∈ range n, (((j : R2 p)+1)*((j : R2 p)+pc p))⁻¹) *
          ((((n : R2 p)+1)*((n : R2 p)+pc p)))⁻¹)) =
        ((((n : R2 p)+1)*((n : R2 p)+pc p)) *
          ((((n : R2 p)+1)*((n : R2 p)+pc p)))⁻¹) *
        (((n : R2 p)+pa p)*((n : R2 p)+pb p) *
          (((∏ j ∈ range n, ((j : R2 p) + pa p)) * (∏ j ∈ range n, ((j : R2 p) + pb p))) *
            (∏ j ∈ range n, (((j : R2 p)+1)*((j : R2 p)+pc p))⁻¹))) by ring,
      ZMod.mul_inv_of_unit _ h, one_mul]

private lemma recover_term {p : ℕ} (hp : p.Prime) (a : R2 p) (n : ℕ)
    (hn : (-(red p a)).val < n) :
    ∃ d : R2 p, (∏ j ∈ range n, ((j : R2 p) + a)) = (p : R2 p)*d := by
  apply red_kern hp
  rw [map_prod]
  apply Finset.prod_eq_zero (mem_range.mpr hn)
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [map_add, map_natCast, ZMod.natCast_zmod_val, neg_add_cancel]

/-- The two root offsets sum to $p-1$. A product of coefficients in
total degree at least $p$ therefore contains two factors of $p$. -/
private lemma high_t_mul {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p=2*h+1)
    (i j : ℕ) (hij : p ≤ i+j) : tCoef p i * tCoef p j = 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let a := (-(red p (pa p))).val
  let b := (-(red p (pb p))).val
  have ha : a < p := ZMod.val_lt _
  have hb : b < p := ZMod.val_lt _
  have hs : (a : ZMod p) + (b : ZMod p) = -1 := by
    rw [show (a : ZMod p) = -(red p (pa p)) from ZMod.natCast_zmod_val _,
      show (b : ZMod p) = -(red p (pb p)) from ZMod.natCast_zmod_val _,
      ← neg_add, ← map_add, (param_sums hp hp2 hh).1]
    simp [pc_red, map_ofNat] <;> ring
  have hs' : a+b=p-1 := by
    have hcast : ((a+b+1 : ℕ) : ZMod p) = 0 := by push_cast; rw [hs, neg_add_cancel]
    obtain ⟨r, hr⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hcast
    have hbound : p*r < p*2 := by omega
    have hr2 : r < 2 := Nat.lt_of_mul_lt_mul_left hbound
    interval_cases r <;> omega
  have bothA (hi : a < i) (hj : a < j) : tCoef p i * tCoef p j = 0 := by
    obtain ⟨x, hx⟩ := recover_term hp (pa p) i hi
    obtain ⟨y, hy⟩ := recover_term hp (pa p) j hj
    simp only [tCoef, hx, hy] 
    linear_combination
      (x*y * (∏ k ∈ range i, ((k : R2 p)+pb p)) * (∏ k ∈ range j, ((k : R2 p)+pb p)) *
        (∏ k ∈ range i, (((k : R2 p)+1)*((k : R2 p)+pc p))⁻¹) *
        (∏ k ∈ range j, (((k : R2 p)+1)*((k : R2 p)+pc p))⁻¹)) * p_sq_zero p
  have bothB (hi : b < i) (hj : b < j) : tCoef p i * tCoef p j = 0 := by
    obtain ⟨x, hx⟩ := recover_term hp (pb p) i hi
    obtain ⟨y, hy⟩ := recover_term hp (pb p) j hj
    simp only [tCoef, hx, hy]
    linear_combination
      (x*y * (∏ k ∈ range i, ((k : R2 p)+pa p)) * (∏ k ∈ range j, ((k : R2 p)+pa p)) *
        (∏ k ∈ range i, (((k : R2 p)+1)*((k : R2 p)+pc p))⁻¹) *
        (∏ k ∈ range j, (((k : R2 p)+1)*((k : R2 p)+pc p))⁻¹)) * p_sq_zero p
  have single (n : ℕ) (ha : a < n) (hb : b < n) : tCoef p n = 0 := by
    obtain ⟨x, hx⟩ := recover_term hp (pa p) n ha
    obtain ⟨y, hy⟩ := recover_term hp (pb p) n hb
    rw [tCoef, hx, hy, show (p : R2 p)*x*((p : R2 p)*y)=(p : R2 p)^2*(x*y) by ring,
      p_sq_zero, zero_mul, zero_mul]
  by_cases hai : a < i <;> by_cases haj : a < j <;> by_cases hbi : b < i <;> by_cases hbj : b < j <;>
    first | exact bothA hai haj | exact bothB hbi hbj | rw [single i hai hbi, zero_mul] |
      rw [single j haj hbj, mul_zero] | omega


private lemma polyOf_eval₂ {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : S) (n : ℕ) (c : ℕ → R) :
    (polyOf n c).eval₂ f x = ∑ j ∈ range n, f (c j) * x^j := by
  simp [polyOf, eval₂_finsetSum, eval₂_monomial]

private lemma t_square_degree {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p=2*h+1) :
    ((polyOf p (tCoef p))^2).natDegree < p := by
  apply lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.mpr _) (show p-1 < p by omega)
  intro n hn
  rw [pow_two (polyOf p (tCoef p)), coeff_mul]
  apply sum_eq_zero
  rintro ⟨i,j⟩ hij
  simp only [HasAntidiagonal.mem_antidiagonal] at hij
  simp only [polyOf_coeff]
  by_cases hi : i < p <;> by_cases hj : j < p <;>
    simp [hi, hj, high_t_mul hp hp2 hh i j (by omega)]

private lemma total_eq_eval {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p=2*h+1) :
    let f := algebraMap (R2 p) (Quadr (R2 p))
    let u := (2 - QuadraticAlgebra.omega)*(f (half p))^2
    f (∑ n ∈ range p, (OeisA179524.a n : R2 p)) =
      ((polyOf (h+1) (weight p h)).comp delta).eval₂ f u := by
  dsimp only
  let f := algebraMap (R2 p) (Quadr (R2 p))
  let i := f (half p)
  let s : Quadr (R2 p) := QuadraticAlgebra.omega
  let u := (2-s)*i^2
  let y := delta.eval₂ f u
  change f _ = _
  have h2 : (2 : Quadr (R2 p))*i = 1 := by
    simpa only [i, map_mul, map_ofNat, map_one] using congrArg f (two_half hp hp2)
  have hs : s^2 = 5 := quad_omega_sq _
  have h4 : (4 : Quadr (R2 p))*i^2=1 := by linear_combination (2*i+1)*h2
  have h16 : (16 : Quadr (R2 p))*i^4=1 := by linear_combination (4*i^2+1)*h4
  have hy : (-16 : Quadr (R2 p))*y = 1 := by
    have hy' : y = u*(1-u) := by simp [y, delta]
    rw [hy']
    dsimp [u]
    linear_combination hs + (s^2 - 4*s + 4)*h16 - 4*(2-s)*h4
  rw [collapse p hp hp2, show (p-1)/2=h by omega, map_sum, eval₂_comp]
  change _ = (polyOf (h+1) (weight p h)).eval₂ f y
  rw [polyOf_eval₂, ← sum_range_reflect]
  apply sum_congr rfl
  intro j hj
  have hjh : j ≤ h := by have := mem_range.mp hj; omega
  rw [show h+1-1-j=h-j by omega,
    ← Nat.choose_symm (show 4*(h-j)+1 ≤ p+2*(h-j) by omega),
    show p+2*(h-j)-(4*(h-j)+1)=2*j by omega]
  simp only [weight, map_mul, map_pow, map_natCast, map_neg, map_ofNat]
  rw [mul_assoc _ ((-16 : Quadr (R2 p))^j) (y^j), ← mul_pow, hy, one_pow, mul_one]

private lemma polynomial_square {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p = 2*h+1) :
    (polyOf (h+1) (weight p h)).comp delta = C (weight p h 0)*(polyOf p (tCoef p))^2 := by
  have hs := param_sums hp hp2 hh
  apply clausal_square (pa p) (pb p) (pc p) (-(h : R2 p)) _ hs.1 hs.2 p
  · have hd0 : (delta : (R2 p)[X]).eval 0 = 0 := by simp [delta]
    rw [coeff_zero_eq_eval_zero, eval_comp, hd0, ← coeff_zero_eq_eval_zero, polyOf_coeff, if_pos (by omega)]
    have H : ((polyOf p (tCoef p)).coeff 0) = 1 := by
      rw [polyOf_coeff, if_pos (by omega)]
      simp [tCoef]
    simp only [pow_two (polyOf p (tCoef p)), mul_coeff_zero, H, mul_one]
  · intro n hn hnp
    apply unit_red hp
    rw [map_mul, map_mul, map_sub, map_sub, map_add, map_add, map_mul, map_natCast, pc_red,
      map_one, map_ofNat, mul_one, add_sub_cancel_right, add_sub_cancel_right]
    have h0 : (n : ZMod p) ≠ 0 :=
      fun hz => Nat.not_dvd_of_pos_of_lt hn hnp ((ZMod.natCast_eq_zero_iff n p).mp hz)
    letI : Fact p.Prime := ⟨hp⟩
    exact mul_ne_zero (mul_ne_zero h0 h0) h0
  · exact polyOf_odeT _ _ _ _ _ (t_recurrence hp)
  · apply polyOf_odeY _ _ _ _ _ _ rfl
    intro j hj
    simpa only [sub_eq_add_neg] using weight_recurrence hp hp2 hh j hj
  · exact t_square_degree hp hp2 hh
  · have hy : (polyOf (h+1) (weight p h)).natDegree ≤ h :=
      natDegree_le_iff_coeff_eq_zero.mpr (fun n hn => by rw [polyOf_coeff, if_neg (by omega)])
    have hd : (delta : (R2 p)[X]).natDegree ≤ 2 := by
      have h' : (1-X : (R2 p)[X]).natDegree ≤ 1 :=
        (natDegree_sub_le (p := (1 : (R2 p)[X])) (q := X)).trans (max_le (by simp) natDegree_X_le)
      exact natDegree_mul_le.trans (Nat.add_le_add natDegree_X_le h')
    exact natDegree_comp_le.trans_lt ((Nat.mul_le_mul hy hd).trans_lt (by omega))

end OMA


namespace OMA
open Polynomial Finset

private def a0 (p : ℕ) : R2 p := (half p)^2
private def b0 (p : ℕ) : R2 p := 3*(half p)^2

private def fCoef (p n : ℕ) : R2 p :=
  ((∏ j ∈ range n, ((j : R2 p) + a0 p)) *
    (∏ j ∈ range n, ((j : R2 p) + b0 p))) *
    ∏ j ∈ range n, ((((j : R2 p)+1)^2))⁻¹

private noncomputable def F (p : ℕ) : (R2 p)[X] := polyOf p (fCoef p)
private noncomputable def T (p : ℕ) : (R2 p)[X] := polyOf p (tCoef p)

private lemma shift_params {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    pa p = a0 p - (p : R2 p)*half p ∧ pb p = b0 p - (p : R2 p)*half p ∧
      a0 p + b0 p = 1 ∧ pa p * pb p = a0 p * b0 p - (p : R2 p)*half p := by
  have hi := two_half hp hp2
  have hA : pa p = a0 p - (p : R2 p)*half p := by
    unfold pa a0
    linear_combination -(p : R2 p)*half p*hi
  have hB : pb p = b0 p - (p : R2 p)*half p := by
    unfold pb b0
    linear_combination -(p : R2 p)*half p*hi
  have hAB : a0 p + b0 p = 1 := by
    unfold a0 b0
    linear_combination (2*half p+1)*hi
  refine ⟨hA, hB, hAB, ?_⟩
  rw [hA, hB]
  linear_combination -(p : R2 p)*half p*hAB + (half p)^2*p_sq_zero p

private lemma f_recurrence {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : n+1 < p) :
    ((n : R2 p)+1)^2*fCoef p (n+1) = ((n : R2 p)+a0 p)*((n : R2 p)+b0 p)*fCoef p n := by
  have h : IsUnit (((n : R2 p)+1)^2) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    exact (unit_small hp (by omega : 0 < n+1) hn).pow 2
  simp only [fCoef, prod_range_succ]
  calc
    _ = (((n : R2 p)+1)^2 * (((n : R2 p)+1)^2)⁻¹) *
        ((((n : R2 p)+a0 p)*((n : R2 p)+b0 p)) *
          ((∏ j ∈ range n, ((j : R2 p)+a0 p)) *
            (∏ j ∈ range n, ((j : R2 p)+b0 p)) *
            (∏ j ∈ range n, ((((j : R2 p)+1)^2))⁻¹))) := by ring
    _ = _ := by rw [ZMod.mul_inv_of_unit _ h, one_mul]

private lemma root_red {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) {n : ℕ} (hn : n < p) :
    red p (fCoef p n) = red p (tCoef p n) := by
  obtain ⟨ha, hb, _, _⟩ := shift_params hp hp2
  have ha' : red p (pa p) = red p (a0 p) := by simp [ha]
  have hb' : red p (pb p) = red p (b0 p) := by simp [hb]
  induction n with
  | zero => simp [fCoef, tCoef]
  | succ n ih =>
    have hF := congrArg (red p) (f_recurrence hp n hn)
    have hT := congrArg (red p) (t_recurrence hp n hn)
    simp only [map_mul, map_pow, map_add, map_natCast, map_one, pc_red, ha', hb'] at hF hT
    rw [ih (by omega)] at hF
    rw [← pow_two, ← hF] at hT
    have h : IsUnit (((n : ZMod p)+1)^2) := by
      rw [← Nat.cast_one, ← Nat.cast_add]
      simpa only [map_natCast] using ((unit_small hp (by omega : 0 < n+1) hn).map (red p)).pow 2
    exact (h.mul_left_cancel hT).symm

private lemma root_factors {p m : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hm : p=4*m+1) :
    (-(red p (a0 p))).val = m ∧ (-(red p (b0 p))).val = 3*m ∧
    (-(red p (pa p))).val = m ∧ (-(red p (pb p))).val = 3*m := by
  obtain ⟨ha, hb, _, _⟩ := shift_params hp hp2
  have ha' : red p (pa p) = red p (a0 p) := by simp [ha]
  have hb' : red p (pb p) = red p (b0 p) := by simp [hb]
  let i := red p (half p)
  have hi : 2*i = 1 := by
    simpa only [i, map_mul, map_ofNat, map_one] using congrArg (red p) (two_half hp hp2)
  have hm' : 4*(m : ZMod p)+1 = 0 := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, ZMod.natCast_self] using
      congrArg (fun n : ℕ => (n : ZMod p)) hm.symm
  have ha0 : -(red p (a0 p)) = (m : ZMod p) := by
    simp only [a0, map_pow]
    change -i^2 = _
    linear_combination -i^2*hm' + (m : ZMod p)*(2*i+1)*hi
  have hb0 : -(red p (b0 p)) = ((3*m : ℕ) : ZMod p) := by
    simp only [b0, a0, map_mul, map_ofNat, map_pow, Nat.cast_mul, Nat.cast_ofNat] at ha0 ⊢
    change -(3*i^2) = 3*(m : ZMod p)
    linear_combination 3*ha0
  simp only [ha', hb', ha0, hb0, ZMod.val_natCast_of_lt (by omega : m < p),
    ZMod.val_natCast_of_lt (by omega : 3*m < p), and_self]

private lemma root_cutoff {p m n : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hm : p=4*m+1)
    (hn : 3*m < n) : fCoef p n = 0 ∧ tCoef p n = 0 := by
  obtain ⟨hA, hB, hC, hD⟩ := root_factors hp hp2 hm
  obtain ⟨a, ha⟩ := recover_term hp (a0 p) n (by rw [hA]; omega)
  obtain ⟨b, hb⟩ := recover_term hp (b0 p) n (by rwa [hB])
  obtain ⟨c, hc⟩ := recover_term hp (pa p) n (by rw [hC]; omega)
  obtain ⟨d, hd⟩ := recover_term hp (pb p) n (by rwa [hD])
  constructor
  · simp only [fCoef, ha, hb]
    linear_combination (a*b * (∏ j ∈ range n, ((((j : R2 p)+1)^2))⁻¹)) * p_sq_zero p
  · simp only [tCoef, hc, hd]
    linear_combination (c*d * (∏ j ∈ range n, (((j : R2 p)+1)*((j : R2 p)+pc p))⁻¹)) * p_sq_zero p

private lemma odeT_of_cutoff {R : Type*} [CommRing R] (a b c : R) (p : ℕ) (f : ℕ → R)
    (hp : 0 < p) (hcut : f (p-1) = 0)
    (hf : ∀ n, n+1 < p →
      ((n : R)+1)*((n : R)+c)*f (n+1) = ((n : R)+a)*((n : R)+b)*f n) :
    odeT a b c (polyOf p f) = 0 := by
  ext n
  by_cases hn : n < p
  · rw [coeff_zero]
    exact (X_pow_dvd_iff.mp (polyOf_odeT a b c p f hf)) n hn
  · cases n with
    | zero => omega
    | succ n =>
      simp only [odeT, coeff_sub, coeff_zero, theta_coeff, coeff_X_mul, step_coeff,
        polyOf_coeff, if_neg hn, mul_zero, zero_sub]
      by_cases hn' : n < p
      · rw [if_pos hn', show n = p-1 by omega, hcut, mul_zero, mul_zero, neg_zero]
      · rw [if_neg hn', mul_zero, mul_zero, neg_zero]

private lemma root_ode {p m : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hm : p=4*m+1) :
    odeT (a0 p) (b0 p) 1 (F p) = 0 ∧ odeT (pa p) (pb p) (pc p) (T p) = 0 := by
  have hcut := root_cutoff hp hp2 hm (by omega : 3*m < p-1)
  constructor
  · apply odeT_of_cutoff _ _ _ _ _ hp.pos hcut.1
    intro n hn
    simpa only [pow_two] using f_recurrence hp n hn
  · exact odeT_of_cutoff _ _ _ _ _ hp.pos hcut.2 (t_recurrence hp)

private lemma red_poly_eq {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    (F p).map (red p) = (T p).map (red p) := by
  ext n
  simp only [coeff_map, F, T, polyOf_coeff]
  by_cases hn : n < p
  · simpa only [if_pos hn] using root_red hp hp2 hn
  · simp [hn]

private def divP (p : ℕ) (x : R2 p) : ℕ := x.val / p

private lemma mul_divP {p : ℕ} (hp : p.Prime) {x : R2 p} (hx : red p x = 0) :
    (p : R2 p) * (divP p x : R2 p) = x := by
  letI : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h : p ∣ x.val := by
    rw [← ZMod.natCast_zmod_val x, map_natCast, ZMod.natCast_eq_zero_iff] at hx
    exact hx
  rw [divP, ← Nat.cast_mul, Nat.mul_div_cancel_left' h, ZMod.natCast_zmod_val]

private lemma red_of_p_mul_zero {p : ℕ} (hp : p.Prime) {x : R2 p}
    (hx : (p : R2 p) * x = 0) : red p x = 0 := by
  letI : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have H := congrArg ZMod.val hx
  rw [← ZMod.natCast_zmod_val x, ← Nat.cast_mul, ZMod.val_natCast, ZMod.val_zero] at H
  have hMul : (p*x.val) % (p^2) = p*(x.val%p) := by
    simpa only [pow_two] using Nat.mul_mod_mul_left p x.val p
  rw [hMul] at H
  have hmod : x.val % p = 0 := by
    rcases Nat.mul_eq_zero.mp H with h | h
    · exact (hp.ne_zero h).elim
    · exact h
  rw [← ZMod.natCast_zmod_val x, map_natCast, ZMod.natCast_eq_zero_iff]
  exact Nat.dvd_of_mod_eq_zero hmod

private noncomputable def liftCorrection (p : ℕ) : (R2 p)[X] :=
  polyOf p (fun n => (divP p ((T p-F p).coeff n) : R2 p))

private noncomputable def P (p : ℕ) : (ZMod p)[X] := (F p).map (red p)
private noncomputable def Q (p : ℕ) : (ZMod p)[X] := (liftCorrection p).map (red p)

private lemma correction_lift {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    C (p : R2 p) * liftCorrection p = T p - F p := by
  have H := red_poly_eq hp hp2
  ext n
  rw [coeff_C_mul, liftCorrection, polyOf_coeff]
  by_cases hn : n < p
  · rw [if_pos hn]
    apply mul_divP hp
    rw [coeff_sub, map_sub, sub_eq_zero]
    simpa only [coeff_map] using (congrArg (fun z : (ZMod p)[X] => z.coeff n) H).symm
  · simp only [hn, if_false, mul_zero, coeff_sub, T, F, polyOf_coeff, sub_self]

private lemma P_degree {p m : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hm : p=4*m+1) :
    (P p).natDegree ≤ m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [P, coeff_map, F, polyOf_coeff]
  by_cases hn' : n < p
  · rw [if_pos hn', fCoef, (recover_term hp (a0 p) n (by rwa [(root_factors hp hp2 hm).1])).choose_spec]
    simp
  · simp only [if_neg hn', map_zero]

private lemma Q_degree {p m : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hm : p=4*m+1) :
    (Q p).natDegree ≤ 3*m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have H := root_cutoff hp hp2 hm hn
  simp [Q, liftCorrection, polyOf_coeff, divP, T, F, H.1, H.2]

private lemma correction_zero {p : ℕ} (hp : p.Prime) : (Q p).coeff 0 = 0 := by
  simp [Q, liftCorrection, polyOf_coeff, divP, T, F, tCoef, fCoef, hp.pos]

private def scale (p : ℕ) : R2 p := weight p ((p-1)/2) 0
private def scale_correction (p : ℕ) : ℕ := divP p (scale p-1)

private lemma scale_red {p m : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hm : p=4*m+1) :
    red p (scale p) = 1 := by
  let h := (p-1)/2
  have hh : p=2*h+1 := by dsimp [h]; omega
  have he : Even h := ⟨m, by dsimp [h]; omega⟩
  have choose_one := choose_reflect p h (p-1) hp (by omega)
    (mem_Ico.mpr ⟨by omega, by omega⟩) he
  rw [show p+h-1-(p-1)=h by omega, Nat.choose_self, Nat.cast_one] at choose_one
  have h4 : (-4 : ZMod p)^h = 1 := by
    rw [show (-4 : ZMod p) = (-1)*2^2 by ring, mul_pow, he.neg_one_pow, one_mul, ← pow_mul,
      show 2*h=p-1 by omega]
    letI : Fact p.Prime := ⟨hp⟩
    apply ZMod.pow_card_sub_one_eq_one
    exact fun hz => Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hp2
      ((ZMod.natCast_eq_zero_iff 2 p).mp hz)
  change red p (weight p h 0) = 1
  simp only [weight, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one,
    map_mul, map_pow, map_neg, map_ofNat, map_natCast, show 2*h=p-1 by omega,
    choose_one, h4, one_pow, mul_one, mul_zero]

private lemma P_endpoints {p m : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hm : p=4*m+1) :
    (P p).eval 0 = 1 ∧ ((P p).eval 1)^2 = 1 := by
  have h0 : (F p).coeff 0 = 1 := by simp [F, polyOf_coeff, fCoef, hp.pos]
  have hP0 : (P p).eval 0 = 1 := by simp [← coeff_zero_eq_eval_zero, P, h0]
  refine ⟨hP0, ?_⟩
  let h := (p-1)/2
  have hh : p=2*h+1 := by dsimp [h]; omega
  have H := polynomial_square hp hp2 hh
  have h01 : (delta : (R2 p)[X]).eval 0 = 0 := by simp [delta]
  have h11 : (delta : (R2 p)[X]).eval 1 = 0 := by simp [delta]
  have h01' := congrArg (fun z : (R2 p)[X] => z.eval 0) H
  have h11' := congrArg (fun z : (R2 p)[X] => z.eval 1) H
  simp only [eval_comp, h01, h11, eval_mul, eval_C, eval_pow] at h01' h11'
  have h := congrArg (red p) (h01'.symm.trans h11')
  have hmap (z : R2 p) : red p ((T p).eval z) = (P p).eval (red p z) := by
    rw [P, red_poly_eq hp hp2, eval_map, eval₂_at_apply]
  change red p (scale p * ((T p).eval 0)^2) =
    red p (scale p * ((T p).eval 1)^2) at h
  simp only [map_mul, map_pow, scale_red hp hp2 hm, one_mul] at h
  rw [hmap, hmap, map_zero, map_one, hP0, one_pow] at h
  exact h.symm

private lemma coefficient_derivative_reduction {p : ℕ} (hp : p.Prime) {D : (R2 p)[X]}
    (hh : C (p : R2 p) * derivative D = 0) :
    derivative (D.map (red p)) = 0 := by
  rw [derivative_map]
  ext n
  rw [coeff_map, coeff_zero]
  apply red_of_p_mul_zero hp
  simpa only [coeff_C_mul, coeff_zero] using congrArg (fun z : (R2 p)[X] => z.coeff n) hh

private lemma correction_deriv {p m : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hm : p=4*m+1) :
    derivative (4*delta*((P p)*(derivative (Q p))-(Q p)*(derivative (P p))) -
      ell*(P p)^2) = 0 := by
  let U := F p
  let V := T p
  let L := liftCorrection p
  let Cₚ : (R2 p)[X] := C (p : R2 p)
  have hh : p=2*((p-1)/2)+1 := by omega
  obtain ⟨_, _, hab, hab'⟩ := shift_params hp hp2
  obtain ⟨hU, hV⟩ := root_ode hp hp2 hm
  have hd (W : (R2 p)[X]) (h : X*W=0) : W = 0 := by
    ext n
    simpa only [coeff_X_mul, coeff_zero] using congrArg (fun z : (R2 p)[X] => z.coeff (n+1)) h
  have hE1 : delta*derivative (derivative U) + ell*derivative U - C (a0 p*b0 p)*U = 0 := by
    rw [odeT_deriv _ _ _ (by rw [hab]; ring)] at hU
    simpa only [map_one, one_mul] using hd _ hU
  have hE2 : delta*derivative (derivative V) + ell*derivative V - C (a0 p*b0 p)*V =
      C ((p : R2 p)*half p)*(ell*derivative V - V) := by
    rw [odeT_deriv _ _ _ (param_sums hp hp2 hh).1] at hV
    have H := hd _ hV
    simp only [pc, hab', map_sub, map_one] at H
    linear_combination H
  have hg : derivative (delta : (R2 p)[X]) = ell := by
    simp [delta, ell, derivative_mul]; ring
  have he : derivative (ell : (R2 p)[X]) = -2 := by
    simp [ell, derivative_mul]
  have hW : derivative (delta*(U*derivative V-V*derivative U)) =
      C ((p : R2 p)*half p)*U*(ell*derivative V - V) := by
    simp only [derivative_mul, derivative_sub, hg]
    linear_combination U*hE2 - V*hE1
  have hL : Cₚ*L = V-U := correction_lift hp hp2
  have hL' : Cₚ*derivative L = derivative V-derivative U := by
    simpa [derivative_mul, derivative_sub, Cₚ] using congrArg derivative hL
  have hSq : Cₚ*Cₚ = 0 := by
    dsimp only [Cₚ]
    rw [← map_mul, ← pow_two, p_sq_zero, map_zero]
  have H0 : Cₚ*(V-U) = 0 := by rw [← hL, ← mul_assoc, hSq, zero_mul]
  have H1 : Cₚ*(derivative V-derivative U) = 0 := by rw [← hL', ← mul_assoc, hSq, zero_mul]
  have hW' : Cₚ*(4*delta*(U*derivative L-L*derivative U)) =
      4*(delta*(U*derivative V-V*derivative U)) := by
    linear_combination 4*delta*U*hL' - 4*delta*derivative U*hL
  have h4 : 4*C ((p : R2 p)*half p) = 2*Cₚ := by
    have h := congrArg (C : R2 p →+* (R2 p)[X]) (two_half hp hp2)
    simp only [map_mul, map_ofNat, map_one] at h
    simp only [Cₚ, map_mul]
    linear_combination 2*Cₚ*h
  let D := 4*delta*(U*derivative L-L*derivative U) - ell*U^2
  have hHD : Cₚ*derivative D = 0 := by
    have hE : derivative (ell*U^2) = 2*U*(ell*derivative U-U) := by
      rw [derivative_mul, he, pow_two U, derivative_mul]
      ring
    calc
      _ = derivative (Cₚ*D) := by simp only [Cₚ, derivative_mul, derivative_C, zero_mul, zero_add]
      _ = derivative (4*(delta*(U*derivative V-V*derivative U))-Cₚ*(ell*U^2)) := by
        congr 1
        dsimp only [D]
        rw [mul_sub, hW']
      _ = 4*(C ((p : R2 p)*half p)*U*(ell*derivative V-V)) -
          Cₚ*(2*U*(ell*derivative U-U)) := by
        rw [derivative_sub, derivative_mul (f := (4 : (R2 p)[X])),
          derivative_mul (f := Cₚ), hW, hE]
        simp only [Cₚ, derivative_C, derivative_ofNat, zero_mul, zero_add]
      _ = 0 := by
        linear_combination U*(ell*derivative V-V)*h4 + 2*U*ell*H1 - 2*U*H0
  have H := coefficient_derivative_reduction hp hHD
  convert H using 2
  simp [D, P, Q, U, L, ell, delta, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow,
    ← derivative_map]

private lemma derivative_kernel {p : ℕ} (hp : p.Prime) {D : (ZMod p)[X]}
    (hD : D.natDegree ≤ p) (hder : derivative D = 0) :
    D = C (D.coeff 0) + C (D.coeff p)*X^p := by
  letI : Fact p.Prime := ⟨hp⟩
  ext n
  rw [coeff_add, coeff_C, coeff_C_mul, coeff_X_pow]
  rcases lt_trichotomy n p with hn | rfl | hn
  · by_cases hn0 : n=0
    · subst n
      simp [show 0 ≠ p by omega]
    · simp only [if_neg hn0, if_neg hn.ne, mul_zero, add_zero]
      have H := congrArg (fun z : (ZMod p)[X] => z.coeff (n-1)) hder
      have hs : n-1+1 = n := by omega
      have hc : ((n-1 : ℕ) : ZMod p)+1 = (n : ZMod p) := by
        simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun k : ℕ => (k : ZMod p)) hs
      rw [coeff_derivative, hc, hs, coeff_zero] at H
      refine (mul_eq_zero.mp H).resolve_right ?_
      exact fun hz => Nat.not_dvd_of_pos_of_lt (by omega) hn
        ((ZMod.natCast_eq_zero_iff n p).mp hz)
  · simp [hp.ne_zero]
  · rw [coeff_eq_zero_of_natDegree_lt (hD.trans_lt hn), if_neg (by omega : n ≠ 0),
      if_neg hn.ne', mul_zero, add_zero]

/-- The normalized Wronskian determines the first-order shift correction.
Its derivative vanishes after reduction, leaving only degrees zero and p. -/
private lemma correction_wronskian {p m : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hm : p=4*m+1) :
    4*delta*(P p * derivative (Q p)-Q p * derivative (P p)) =
      ell*(P p)^2 - 1 + 2*X^p := by
  let D := 4*delta*(P p * derivative (Q p)-Q p * derivative (P p)) - ell*(P p)^2
  have hP := P_degree hp hp2 hm
  have hQ := Q_degree hp hp2 hm
  have hPD := (natDegree_derivative_le (P p)).trans (Nat.sub_le_sub_right hP 1)
  have hQD := (natDegree_derivative_le (Q p)).trans (Nat.sub_le_sub_right hQ 1)
  have hδ : (delta : (ZMod p)[X]).natDegree ≤ 2 := by
    apply natDegree_mul_le.trans
    have h := natDegree_sub_le (p := (1 : (ZMod p)[X])) (q := X)
    have h' : (1-X : (ZMod p)[X]).natDegree ≤ 1 :=
      h.trans (max_le (by simp) natDegree_X_le)
    exact Nat.add_le_add natDegree_X_le h'
  have hℓ : (ell : (ZMod p)[X]).natDegree ≤ 1 := by
    unfold ell
    refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    refine le_trans natDegree_mul_le ?_
    simpa using (natDegree_X_le (R := ZMod p))
  have h4 : (4 : (ZMod p)[X]).natDegree = 0 := by simp
  have hM := (natDegree_mul_le (p := P p) (q := derivative (Q p))).trans (Nat.add_le_add hP hQD)
  have hN := (natDegree_mul_le (p := Q p) (q := derivative (P p))).trans (Nat.add_le_add hQ hPD)
  have hD : D.natDegree ≤ p := by
    unfold D
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine le_trans natDegree_mul_le ?_
      have h4δ := (natDegree_mul_le (p := (4 : (ZMod p)[X])) (q := delta)).trans
        (Nat.add_le_add h4.le hδ)
      have hSub := (natDegree_sub_le (p := P p * derivative (Q p)) (q := Q p * derivative (P p)))
      have hSub' := hSub.trans (max_le (hM.trans (show m+(3*m-1) ≤ p-2 by omega))
        (hN.trans (show 3*m+(m-1) ≤ p-2 by omega)))
      omega
    · refine le_trans natDegree_mul_le ?_
      have hP2 := (natDegree_pow_le (p := P p) (n := 2)).trans (Nat.mul_le_mul_left 2 hP)
      omega
  have h := derivative_kernel hp hD (correction_deriv hp hp2 hm)
  obtain ⟨h0, h1⟩ := P_endpoints hp hp2 hm
  have d0L : D.eval 0 = -1 := by
    dsimp only [D]
    simp only [eval_sub, eval_mul, eval_pow, h0]
    simp [delta, ell]
  have d1L : D.eval 1 = 1 := by
    dsimp only [D]
    simp only [eval_sub, eval_mul, eval_pow, h1]
    simp [delta, ell]
    ring
  have d0 : D.coeff 0 = -1 := by rwa [coeff_zero_eq_eval_zero]
  have d1 := congrArg (fun z : (ZMod p)[X] => z.eval 1) h
  simp only [d1L, eval_add, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one, d0] at d1
  have dp : D.coeff p = 2 := by linear_combination -d1
  rw [d0, dp] at h
  dsimp only [D] at h
  simp only [map_neg, map_one, map_ofNat] at h
  linear_combination h

private def point {R : Type*} [CommRing R] (i : R) : Quadr R :=
  (2 - QuadraticAlgebra.omega) * (algebraMap R (Quadr R) i)^2

private lemma map_point {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (i : R) :
    quadMap f (point i) = point (f i) := by
  simp only [point, map_mul, map_sub, map_pow, map_ofNat]
  congr 2
  · ext <;> simp [quadMap, QuadraticAlgebra.omega]
  · ext <;> simp [quadMap]

private lemma map_point_eval {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (Y : R[X]) (i : R) :
    quadMap f (Y.eval₂ (algebraMap R (Quadr R)) (point i)) =
      (Y.map f).eval₂ (algebraMap S (Quadr S)) (point (f i)) := by
  rw [hom_eval₂, map_point, eval₂_map]
  congr 1
  ext z <;> simp [quadMap]


private def bCoef (p n : ℕ) : R2 p :=
  ((4*n).factorial : R2 p) * (((n.factorial : R2 p)^4)⁻¹) * (half p)^(6*n)

private lemma factorial_unit {p n : ℕ} (hp : p.Prime) (hn : n < p) :
    IsUnit (n.factorial : R2 p) := by
  rw [ZMod.isUnit_iff_coprime]
  exact (hp.coprime_factorial_of_lt hn).symm.pow_right 2

private lemma b_clear {p n : ℕ} (hp : p.Prime) (hn : n < p) :
    (n.factorial : R2 p)^4*bCoef p n = ((4*n).factorial : R2 p)*(half p)^(6*n) := by
  unfold bCoef
  have h := ZMod.mul_inv_of_unit _ ((factorial_unit hp hn).pow 4)
  linear_combination (((4*n).factorial : R2 p)*(half p)^(6*n))*h

private lemma b_cutoff {p n : ℕ} (hp : p.Prime) (hn : 2*p ≤ 4*n) :
    bCoef p n = 0 := by
  have h : p^2 ∣ (2*p).factorial := by
    have hp' : p ∣ (2*p-1).factorial := Nat.dvd_factorial hp.pos (by omega)
    have H := Nat.mul_dvd_mul (show p ∣ 2*p by exact dvd_mul_left _ _) hp'
    have hFac : (2*p).factorial = (2*p)*(2*p-1).factorial := by
      have hpos := hp.pos
      simpa only [show 2*p-1+1=2*p by omega] using Nat.factorial_succ (2*p-1)
    simpa only [pow_two, hFac] using H
  have hd := h.trans (Nat.factorial_dvd_factorial hn)
  simp [bCoef, (ZMod.natCast_eq_zero_iff _ _).mpr hd]

private lemma b_recurrence {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (n : ℕ) (hn : n+1 < p) :
    ((n : R2 p)+1)^3 * bCoef p (n+1) =
      4*((n : R2 p)+a0 p)*((n : R2 p)+b0 p)*((n : R2 p)+half p)*bCoef p n := by
  let N : R2 p := n
  let i := half p
  have hi : 2*i = 1 := two_half hp hp2
  have hi' : 4*i^2 = 1 := by linear_combination (2*i+1)*hi
  have hA : (4*N+1)*i^2 = N+a0 p := by
    change (4*N+1)*i^2 = N+i^2
    linear_combination N*hi'
  have hB : (4*N+3)*i^2 = N+b0 p := by
    change (4*N+3)*i^2 = N+3*i^2
    linear_combination N*hi'
  have hC : (4*N+2)*i^2 = N+i := by linear_combination N*hi' + i*hi
  have hProd : ((4*N+4)*(4*N+3)*(4*N+2)*(4*N+1))*i^6 =
      4*(N+a0 p)*(N+b0 p)*(N+i)*(N+1) := by
    calc
      _ = 4*((4*N+1)*i^2)*((4*N+3)*i^2)*((4*N+2)*i^2)*(N+1) := by ring
      _ = _ := by rw [hA,hB,hC]
  have h0 := b_clear hp (n := n) (by omega)
  have h1 := b_clear hp hn
  rw [Nat.factorial_succ n, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    show 4*(n+1)=4*n+3+1 by omega, Nat.factorial_succ (4*n+3),
    Nat.factorial_succ (4*n+2), Nat.factorial_succ (4*n+1), Nat.factorial_succ (4*n),
    show 6*(n+1)=6*n+6 by omega, pow_add] at h1
  push_cast at h1
  have H1 : (((N+1)*(n.factorial : R2 p))^4)*bCoef p (n+1) =
      ((4*N+4)*((4*N+3)*((4*N+2)*((4*N+1)*((4*n).factorial : R2 p))))) *
        (i^(6*n)*i^6) := by
    convert h1 using 1 <;> dsimp only [N, i] <;> ring
  have hu : IsUnit (N+1) := by
    simpa only [N, Nat.cast_add, Nat.cast_one] using unit_small hp (by omega : 0<n+1) hn
  apply ((factorial_unit hp (n := n) (by omega : n < p)).pow 4).mul_left_cancel
  apply hu.mul_left_cancel
  change (N+1)*((n.factorial : R2 p)^4*((N+1)^3*bCoef p (n+1))) =
    (N+1)*((n.factorial : R2 p)^4*(4*(N+a0 p)*(N+b0 p)*(N+i)*bCoef p n))
  linear_combination H1 +
    ((4*n).factorial : R2 p)*i^(6*n)*hProd -
    4*(N+a0 p)*(N+b0 p)*(N+i)*(N+1)*h0

private lemma f_coef_red_zero {p m n : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hm : p=4*m+1)
    (hn : m < n) : red p (fCoef p n) = 0 := by
  rw [fCoef, (recover_term hp (a0 p) n
    (by rwa [(root_factors hp hp2 hm).1])).choose_spec]
  simp

private lemma f_square_degree {p m : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hm : p=4*m+1) :
    ((F p)^2).natDegree < p := by
  apply lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.mpr _) (show p-1 < p by omega)
  intro n hn
  rw [pow_two (F p), coeff_mul]
  apply sum_eq_zero
  rintro ⟨i,j⟩ hij
  simp only [HasAntidiagonal.mem_antidiagonal] at hij
  change (polyOf p (fCoef p)).coeff i * (polyOf p (fCoef p)).coeff j = 0
  rw [polyOf_coeff, polyOf_coeff]
  by_cases hi : i < p
  · by_cases hj : j < p
    · rw [if_pos hi, if_pos hj]
      by_cases hi' : m < i
      · by_cases hj' : m < j
        · obtain ⟨r, hr⟩ := red_kern hp (f_coef_red_zero hp hp2 hm hi')
          obtain ⟨s, hs⟩ := red_kern hp (f_coef_red_zero hp hp2 hm hj')
          rw [hr, hs]
          linear_combination r*s*p_sq_zero p
        · rw [(root_cutoff hp hp2 hm (by omega : 3*m < i)).1, zero_mul]
      · rw [(root_cutoff hp hp2 hm (by omega : 3*m < j)).1, mul_zero]
    · rw [if_neg hj, mul_zero]
  · rw [if_neg hi, zero_mul]

private lemma ordinary_square {p m : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hm : p=4*m+1) :
    (polyOf p (bCoef p)).comp delta = (F p)^2 := by
  have hab := (shift_params hp hp2).2.2.1
  have hab' : a0 p+b0 p=2*1-1 := by rw [hab]; ring
  have hd : 2*half p=2*1-1 := by rw [two_half hp hp2]; ring
  suffices H : (polyOf p (bCoef p)).comp delta = C 1*(F p)^2 by simpa using H
  apply clausal_square (a0 p) (b0 p) 1 (half p) 1 hab' hd p
  · have hd0 : (delta : (R2 p)[X]).eval 0 = 0 := by simp [delta]
    rw [coeff_zero_eq_eval_zero, eval_comp, hd0, ← coeff_zero_eq_eval_zero, polyOf_coeff,
      if_pos hp.pos]
    have hf : (F p).coeff 0 = 1 := by simp [F, polyOf_coeff, fCoef, hp.pos]
    simp [bCoef, pow_two (F p), mul_coeff_zero, hf]
  · intro n hn hnp
    have H := (unit_small hp hn hnp).pow 3
    simpa only [mul_one, add_sub_cancel_right, pow_succ, pow_zero, one_mul] using H
  · rw [(root_ode hp hp2 hm).1]
    exact dvd_zero _
  · ext n
    rw [odeY, coeff_sub, theta_coeff, coeff_zero, mul_assoc, coeff_C_mul]
    cases n with
    | zero => simp
    | succ n =>
      rw [coeff_X_mul, step_coeff, step_coeff, step_coeff, step_coeff, step_coeff,
        polyOf_coeff, polyOf_coeff, Nat.cast_add, Nat.cast_one]
      by_cases hn : n+1 < p
      · rw [if_pos hn, if_pos (by omega : n < p)]
        have H := b_recurrence hp hp2 n hn
        linear_combination H
      · rw [if_neg hn]
        by_cases hnp : n < p
        · rw [if_pos hnp, b_cutoff hp (by omega : 2*p ≤ 4*n)]
          ring
        · rw [if_neg hnp]
          ring
  · exact f_square_degree hp hp2 hm
  · have hB : (polyOf p (bCoef p)).natDegree ≤ (p-1)/2 := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      rw [polyOf_coeff]
      by_cases hnp : n < p
      · rw [if_pos hnp, b_cutoff hp (by omega : 2*p ≤ 4*n)]
      · rw [if_neg hnp]
    have hδ : (delta : (R2 p)[X]).natDegree ≤ 2 := by
      have h' : (1-X : (R2 p)[X]).natDegree ≤ 1 :=
        (natDegree_sub_le (p := (1 : (R2 p)[X])) (q := X)).trans (max_le (by simp) natDegree_X_le)
      exact natDegree_mul_le.trans (Nat.add_le_add natDegree_X_le h')
    exact natDegree_comp_le.trans_lt ((Nat.mul_le_mul hB hδ).trans_lt (by omega))

private def factorial_sum (p : ℕ) : R2 p :=
  ∑ j ∈ range p, ((4*j).factorial : R2 p)*(((j.factorial : R2 p)^4)⁻¹)*(-(half p)^10)^j

private lemma ordinary_at_point {p m : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hm : p=4*m+1) :
    let f := algebraMap (R2 p) (Quadr (R2 p))
    ((F p).eval₂ f (point (half p)))^2 = f (factorial_sum p) := by
  dsimp only
  let f := algebraMap (R2 p) (Quadr (R2 p))
  let i := f (half p)
  let s : Quadr (R2 p) := QuadraticAlgebra.omega
  let u := point (half p)
  change ((F p).eval₂ f u)^2 = f (factorial_sum p)
  have h2 : (2 : Quadr (R2 p))*i = 1 := by
    simpa only [i, map_mul, map_ofNat, map_one] using congrArg f (two_half hp hp2)
  have hs : s^2 = 5 := quad_omega_sq _
  have h4 : (4 : Quadr (R2 p))*i^2 = 1 := by linear_combination (2*i+1)*h2
  have hu : delta.eval₂ f u = -i^4 := by
    have H : delta.eval₂ f u = u*(1-u) := by simp [delta]
    rw [H]
    change (2-s)*i^2*(1-(2-s)*i^2) = -i^4
    linear_combination (2-s)*i^2*(-h4) - i^4*hs
  rw [← eval₂_pow, ← ordinary_square hp hp2 hm, eval₂_comp, polyOf_eval₂, factorial_sum, map_sum]
  apply sum_congr rfl
  intro j hj
  rw [hu]
  simp only [bCoef, map_mul, map_pow, map_neg]
  change f ((4*j).factorial : R2 p) * f (((j.factorial : R2 p)^4)⁻¹) * i^(6*j)*(-i^4)^j =
    f ((4*j).factorial : R2 p) * f (((j.factorial : R2 p)^4)⁻¹) * (-i^10)^j
  rw [pow_mul i 6 j, mul_assoc _ ((i^6)^j), ← mul_pow]
  rw [show i^6*(-i^4) = -i^10 by ring]

private lemma quad_annihilated {p : ℕ} (hp : p.Prime) {z : Quadr (R2 p)}
    (hz : quadMap (red p) z = 0) : (p : Quadr (R2 p))*z = 0 := by
  obtain ⟨r, hr⟩ := red_kern hp (show red p z.re = 0 from congrArg QuadraticAlgebra.re hz)
  obtain ⟨i, hi⟩ := red_kern hp (show red p z.im = 0 from congrArg QuadraticAlgebra.im hz)
  have he : z = (p : Quadr (R2 p))*⟨r,i⟩ := by
    ext
    · simpa [QuadraticAlgebra.re_mul] using hr
    · simpa [QuadraticAlgebra.im_mul] using hi
  rw [he, ← mul_assoc, ← pow_two]
  have H : (p : Quadr (R2 p))^2 = 0 := by
    simpa only [map_pow, map_natCast, map_zero] using
      congrArg (algebraMap (R2 p) (Quadr (R2 p))) (p_sq_zero p)
  rw [H, zero_mul]

private lemma shift_at_point {p m : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hm : p=4*m+1)
    (hv : 2*(Q p).eval₂ (algebraMap (ZMod p) (Quadr (ZMod p))) (point (red p (half p))) +
      (scale_correction p : Quadr (ZMod p)) *
        (P p).eval₂ (algebraMap (ZMod p) (Quadr (ZMod p))) (point (red p (half p))) = 0) :
    let f := algebraMap (R2 p) (Quadr (R2 p))
    f (scale p) * ((T p).eval₂ f (point (half p)))^2 =
      ((F p).eval₂ f (point (half p)))^2 := by
  dsimp only
  let f := algebraMap (R2 p) (Quadr (R2 p))
  let ev := eval₂RingHom f (point (half p))
  let c : Quadr (R2 p) := p
  have hc : c^2 = 0 := by
    simpa only [c, f, map_pow, map_natCast, map_zero] using congrArg f (p_sq_zero p)
  have hL : c * ev (liftCorrection p) = ev (T p) - ev (F p) := by
    simpa only [ev, map_mul, map_sub, coe_eval₂RingHom, eval₂_C, f, c, map_natCast]
      using congrArg ev (correction_lift hp hp2)
  have hScale : f (scale p) = 1+c*(scale_correction p : Quadr (R2 p)) := by
    have h := mul_divP hp (x := scale p-1) (by simp [map_sub, scale_red hp hp2 hm])
    have H := congrArg f h
    change f ((p : R2 p)*(scale_correction p : R2 p)) = f (scale p-1) at H
    simp only [map_mul, map_natCast, map_sub, map_one] at H
    dsimp only [c]
    linear_combination -H
  have hq : c*(2*ev (liftCorrection p)+(scale_correction p : Quadr (R2 p))*ev (F p)) = 0 :=
    quad_annihilated hp (by
      simp only [map_add, map_mul, map_ofNat, map_natCast, ev, coe_eval₂RingHom, f,
        map_point_eval]
      exact hv)
  change f (scale p)*(ev (T p))^2 = (ev (F p))^2
  have ht : ev (T p) = ev (F p)+c*ev (liftCorrection p) := by linear_combination -hL
  rw [hScale, ht]
  linear_combination
    ev (F p)*hq +
    ((ev (liftCorrection p))^2 + 2*(scale_correction p : Quadr (R2 p))*
      ev (F p)*ev (liftCorrection p) + c*(scale_correction p : Quadr (R2 p))*
        (ev (liftCorrection p))^2)*hc

end OMA

namespace OMA.R_OeisA179524_conjecture1_R1
open Finset Polynomial

/-- The ordinary binomial evaluation at −1/1024, in factorial form.
This is the m = 5 case of Sun and Ye's supercongruence. -/
def H1 : Prop :=
  ∀ (p : ℕ), p.Prime → (p % 20 = 1 ∨ p % 20 = 9) →
    ∀ (x y : ℤ), (p : ℤ) = x^2 + 5*y^2 →
    factorial_sum p = ((4*x^2 - 2*(p : ℤ) : ℤ) : R2 p)

/-- The normalized finite-field Wronskian solution has the prescribed value
at the discriminant −20 point. -/
def H2 : Prop :=
  ∀ (p : ℕ), p.Prime → (p % 20 = 1 ∨ p % 20 = 9) →
    ∀ D : (ZMod p)[X], D.natDegree < p → D.coeff 0 = 0 →
      4*delta*(P p * derivative D-D * derivative (P p)) =
        ell*(P p)^2 - 1 + 2*X^p →
      let f := algebraMap (ZMod p) (Quadr (ZMod p))
      let u := point (red p (half p))
      2*D.eval₂ f u+(scale_correction p : Quadr (ZMod p))*(P p).eval₂ f u = 0

theorem main : H1 → H2 → type_of% @OeisA179524.conjecture1 := by
  intro h1 h2 p hp hmod x y hs
  have hm : p % 20 = 1 ∨ p % 20 = 9 := by
    rcases hmod with h | h <;> unfold Int.ModEq at h <;> omega
  have hp2 : 2 < p := by have := hp.two_le; omega
  let m := (p-1)/4
  have hm' : p = 4*m+1 := by dsimp [m]; omega
  let h := (p-1)/2
  have hh : p = 2*h+1 := by dsimp [h]; omega
  have hc := h2 p hp hm (Q p) ((Q_degree hp hp2 hm').trans_lt (by omega))
    (correction_zero hp) (correction_wronskian hp hp2 hm')
  have H := total_eq_eval hp hp2 hh
  dsimp only at H
  rw [polynomial_square hp hp2 hh, eval₂_mul, eval₂_C, eval₂_pow] at H
  change (algebraMap (R2 p) (Quadr (R2 p))) (∑ n ∈ range p, (OeisA179524.a n : R2 p)) =
    (algebraMap (R2 p) (Quadr (R2 p))) (scale p) *
      ((T p).eval₂ _ (point (half p)))^2 at H
  rw [shift_at_point hp hp2 hm' hc, ordinary_at_point hp hp2 hm', h1 p hp hm x y hs] at H
  have Hz := QuadraticAlgebra.algebraMap_injective H
  have Hz' : ((∑ n ∈ range p, OeisA179524.a n : ℤ) : R2 p) =
      ((4*x^2 - 2*(p : ℤ) : ℤ) : R2 p) := by
    simpa only [Int.cast_sum] using Hz
  simpa only [Nat.cast_pow] using (ZMod.intCast_eq_intCast_iff _ _ _).mp Hz'

end OMA.R_OeisA179524_conjecture1_R1
