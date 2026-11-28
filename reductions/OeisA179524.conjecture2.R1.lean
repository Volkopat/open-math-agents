import FormalConjectures.OEIS.«179524»
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.FieldTheory.Finite.Basic

/-!
The binomial collapse, reversed recurrence and quadratic-algebra setup
are adapted from the merged A179524 conjecture 3 proof by @MrSeizy.
Its factorial argument credits @rleshner's A357513 supercongruence proof.

Write F for the multinomial series, S for its truncation at p, and T for
the same truncation with the rising factorials shifted by p. The affine
shift shows that grouping F into blocks of length p gives
F(X) = S(X) F(X^p) + (T(X)-S(X)) X^p F'(X^p) modulo p², using
the congruence of multinomial coefficients at indices n and pn.
Beukers's formal Frobenius congruence then gives
X^sigma = X^p T(X)/S(X), by cancelling F'(X^p), whose constant is 24.
Maier's two degree-five maps (arXiv:math/0611041, Table 6) commute with
the same substitution q ↦ q^p. Clearing the resulting first-order
identities at the cusp and inverting the first branch Jacobian
gives the common-lift input H1. H2 is the m = 5 evaluation in
Sun and Ye, arXiv:2408.09776v4, Theorem 1.11, reduced modulo p².

At r = -5 ± sqrt(5) both branches have value -1/1024. The factor
r² + 10r + 20 occurs simply in their cleared difference. This forces
the common lift to stay on one of these two roots and proves the
required shifted congruence. Morley's congruence supplies the sign.
-/

namespace OMA.R_OeisA179524_conjecture2_R1
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

private def rising (p : ℕ) (v : R2 p) (j : ℕ) : R2 p :=
  ∏ i ∈ range j, ((i : R2 p) + 1 + v)

private def coef (p : ℕ) (v : R2 p) (j : ℕ) : R2 p :=
  rising p (4*v) (4*j) * (rising p v j)⁻¹ ^ 4

private lemma prod_unit {R : Type*} [CommMonoid R] {s : Finset ℕ} {f : ℕ → R}
    (hu : ∀ i ∈ s, IsUnit (f i)) : IsUnit (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi]
    exact (hu i (mem_insert_self _ _)).mul (ih fun j hj => hu j (mem_insert_of_mem hj))

private lemma rising_unit {p j : ℕ} (hp : p.Prime) (hj : j < p)
    {v : R2 p} (hv : red p v = 0) : IsUnit (rising p v j) := by
  unfold rising
  apply prod_unit
  intro i hi
  apply unit_red hp
  rw [map_add, hv, add_zero, map_add, map_natCast, map_one, ← Nat.cast_succ]
  exact fun hz => Nat.not_dvd_of_pos_of_lt (Nat.succ_pos _) (by
    have := mem_range.mp hi
    omega) ((ZMod.natCast_eq_zero_iff _ _).mp hz)

private lemma rising_succ (p : ℕ) (v : R2 p) (j : ℕ) :
    rising p v (j+1) = rising p v j * ((j : R2 p)+1+v) := by
  simp [rising, prod_range_succ]

private lemma coef_recurrence {p j : ℕ} (hp : p.Prime) (hj : j+1 < p)
    {v : R2 p} (hv : red p v = 0) :
    ((j : R2 p)+1+v)^4 * coef p v (j+1) =
      ((4*(j : R2 p)+1+4*v)*(4*(j : R2 p)+2+4*v)*
        (4*(j : R2 p)+3+4*v)*(4*(j : R2 p)+4+4*v)) * coef p v j := by
  have hu := (rising_unit hp (by omega : j < p) hv).pow 4
  have mul_cancel (n : ℕ) (hn : n < p) :
      rising p v n ^ 4 * coef p v n = rising p (4*v) (4*n) := by
    unfold coef
    rw [mul_left_comm, ← mul_pow, ZMod.mul_inv_of_unit _ (rising_unit hp hn hv),
      one_pow, mul_one]
  apply hu.mul_left_cancel
  have ha := mul_cancel (j+1) hj
  have hb := mul_cancel j (by omega)
  rw [rising_succ p v j, mul_pow, show 4*(j+1)=4*j+1+1+1+1 by omega,
    rising_succ, rising_succ, rising_succ, rising_succ] at ha
  push_cast at ha
  linear_combination ha - ((4*(j : R2 p)+1+4*v)*(4*(j : R2 p)+2+4*v)*
    (4*(j : R2 p)+3+4*v)*(4*(j : R2 p)+4+4*v)) * hb

private lemma reversed_weight {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p = 2*h+1)
    (j : ℕ) (hj : j ≤ h) :
    weight p h j = weight p h 0 * coef p (-(p : R2 p)*half p) j * (half p ^ 6)^j := by
  let v : R2 p := -(p : R2 p)*half p
  have hv : red p v = 0 := by simp [v, ZMod.natCast_self]
  induction j with
  | zero => simp [coef, rising]
  | succ j ih =>
    have hj' : j < h := by omega
    specialize ih (by omega)
    have h2 := two_half hp hp2
    have hP : (p : R2 p) = 2*(h : R2 p)+1 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
        congrArg (fun n : ℕ => (n : R2 p)) hh
    have hp0 := p_sq_zero p
    have hs := coef_recurrence hp (by omega : j+1 < p) hv
    let x : R2 p := (j : R2 p)+1+v
    have hx : IsUnit x := by
      apply unit_red hp
      rw [show x = (j : R2 p)+1+v by rfl, map_add, hv, add_zero, map_add, map_natCast,
        map_one, ← Nat.cast_succ]
      intro hz
      exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos j) (by omega)
        ((ZMod.natCast_eq_zero_iff _ _).mp hz)
    let L : R2 p := ((j : R2 p)+1)*((j : R2 p)+pc p)*((j : R2 p)+2*pc p-1)
    let K : R2 p := 4*((j : R2 p)+pa p)*((j : R2 p)+pb p)*((j : R2 p)-(h : R2 p))
    have hL : L = x^3 := by
      have aux : ((j : R2 p)+1)*((j : R2 p)+2*pc p-1) = x^2 := by
        unfold pc x v
        linear_combination -(half p)^2 * hp0
      calc
        L = (((j : R2 p)+1)*((j : R2 p)+2*pc p-1)) * x := by
          dsimp [L, pc, x, v]
          ring
        _ = x^3 := by rw [aux]; ring
    have hr := weight_recurrence hp hp2 hh j hj'
    change L * _ = K * _ at hr
    change weight p h j = _ * coef p v j * _ at ih
    rw [ih, hL] at hr
    have h1 : 4*((j : R2 p)+pa p) = 4*(j : R2 p)+1+4*v := by
      unfold pa v
      linear_combination ((1-2*(p : R2 p))*(2*half p+1)+2*(p : R2 p))*h2
    have h3 : 4*((j : R2 p)+pb p) = 4*(j : R2 p)+3+4*v := by
      unfold pb v
      linear_combination ((3-2*(p : R2 p))*(2*half p+1)+2*(p : R2 p))*h2
    have h4 : 4*((j : R2 p)-(h : R2 p)) = 4*(j : R2 p)+2+4*v := by
      unfold v
      linear_combination 2*hP + 2*(p : R2 p)*h2
    have hk : (4*(j : R2 p)+1+4*v)*(4*(j : R2 p)+2+4*v)*
        (4*(j : R2 p)+3+4*v)*(4*(j : R2 p)+4+4*v) = x*(64*K) := by
      rw [← h1, ← h3, ← h4]
      unfold K x
      ring
    change x^4 * _ = _ at hs
    rw [hk, show x^4=x*x^3 by ring, mul_assoc, mul_assoc] at hs
    have hrec := hx.mul_left_cancel hs
    have h64 : (64 : R2 p)*half p^6 = 1 := by
      linear_combination ((2*half p)^5+(2*half p)^4+(2*half p)^3+
        (2*half p)^2+2*half p+1)*h2
    change weight p h (j+1) = _ * coef p v (j+1) * _
    apply (hx.pow 3).mul_left_cancel
    rw [pow_succ _ j]
    linear_combination hr -
      (weight p h 0*(half p^6)^j*half p^6)*hrec -
      (weight p h 0*(half p^6)^j*K*coef p v j)*h64

private lemma coef_vanish {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p = 2*h+1)
    {j : ℕ} (hj : h < j) :
    coef p (-(p : R2 p)*half p) j = 0 := by
  have ha : ((2*p-1 : ℕ) : R2 p)+1+4*(-(p : R2 p)*half p) = 0 := by
    have h2 := two_half hp hp2
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2*p)]
    linear_combination -2*(p : R2 p)*h2
  have hz : rising p (4*(-(p : R2 p)*half p)) (4*j) = 0 :=
    prod_eq_zero (mem_range.mpr (by omega : 2*p-1 < 4*j)) ha
  rw [coef, hz, zero_mul]

private def t0 (p : ℕ) : R2 p := -(half p)^10

private lemma collapse_shifted {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p = 2*h+1) :
    (∑ n ∈ range p, (OeisA179524.a n : R2 p)) =
      weight p h 0 * ∑ j ∈ range p, coef p (-(p : R2 p)*half p) j * t0 p ^ j := by
  let z : R2 p := -half p ^ 4
  have h16 : (-16 : R2 p)*z = 1 := by
    have h2 := two_half hp hp2
    unfold z
    linear_combination (((2*half p)^3+(2*half p)^2+2*half p+1))*h2
  have hz : half p ^ 6 * z = t0 p := by simp [z, t0]; ring
  rw [collapse p hp hp2, show (p-1)/2=h by omega, ← sum_range_reflect, mul_sum]
  calc
    _ = ∑ j ∈ range (h+1), weight p h 0 *
          (coef p (-(p : R2 p)*half p) j * t0 p^j) := by
      apply sum_congr rfl
      intro j hj
      have hjh : j ≤ h := by have := mem_range.mp hj; omega
      have hw := reversed_weight hp hp2 hh j hjh
      rw [show h+1-1-j=h-j by omega,
        ← Nat.choose_symm (show 4*(h-j)+1 ≤ p+2*(h-j) by omega),
        show p+2*(h-j)-(4*(h-j)+1)=2*j by omega]
      calc
        _ = weight p h j * z^j := by
          unfold weight
          rw [mul_assoc _ ((-16 : R2 p)^j), ← mul_pow, h16, one_pow, mul_one]
        _ = _ := by rw [hw, mul_assoc _ _ (z^j), ← mul_pow, hz]; ring
    _ = _ := by
      apply sum_subset (range_mono (by omega))
      intro j hj hj'
      rw [coef_vanish hp hp2 hh (by simp only [mem_range, not_lt] at hj'; omega),
        zero_mul, mul_zero]

private lemma prod_affine {R : Type*} [CommRing R] (s : Finset ℕ) (a b : ℕ → R) :
    ∃ c : R, ∀ v : R, v^2 = 0 →
      (∏ i ∈ s, (a i + v*b i)) = (∏ i ∈ s, a i) + v*c := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨a i*c+b i*(∏ j ∈ s, a j), ?_⟩
    intro v hv
    rw [prod_insert hi, prod_insert hi, hc v hv]
    linear_combination b i*c*hv

private lemma coef_affine {p j : ℕ} (hp : p.Prime) (hj : j < p) :
    ∃ c : R2 p, ∀ (v : R2 p), red p v = 0 → coef p v j = coef p 0 j + v*c := by
  obtain ⟨a, ha⟩ := prod_affine (range (4*j)) (fun i => (i : R2 p)+1) (fun _ => 4)
  obtain ⟨b, hb⟩ := prod_affine (range j) (fun i => (i : R2 p)+1) (fun _ => 1)
  let d : R2 p := rising p 0 j
  let e : R2 p := d⁻¹
  have he : d*e = 1 := ZMod.mul_inv_of_unit _ (rising_unit hp hj (map_zero _))
  refine ⟨a*e^4 - 4*rising p 0 (4*j)*e^5*b, ?_⟩
  intro v hv
  have hv2 : v^2 = 0 := by
    obtain ⟨c, rfl⟩ := red_kern hp hv
    rw [mul_pow, p_sq_zero, zero_mul]
  have hA : rising p (4*v) (4*j) = rising p 0 (4*j)+v*a := by
    simp only [rising, add_zero]
    rw [← ha v hv2]
    congr 1
    funext i
    ring
  have hB : rising p v j = d+v*b := by
    simpa [d, rising] using hb v hv2
  have hI : (rising p v j)⁻¹ = e - e^2*b*v := by
    apply (rising_unit hp hj hv).mul_left_cancel
    rw [ZMod.mul_inv_of_unit _ (rising_unit hp hj hv), hB]
    linear_combination (b*e*v-1)*he + b^2*e^2*hv2
  have hpower : (e - e^2*b*v)^4 = e^4-4*e^5*b*v := by
    linear_combination (6*e^6*b^2-4*e^7*b^3*v+e^8*b^4*v^2)*hv2
  rw [show coef p v j = rising p (4*v) (4*j) * (rising p v j)⁻¹ ^ 4 by rfl,
    hA, hI, hpower, show coef p 0 j = rising p 0 (4*j) * e^4 by simp [coef, e, d]]
  linear_combination -4*a*e^5*b*hv2

private lemma coef_interpolate {p j : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hj : j < p) :
    2 * coef p (-(p : R2 p)*half p) j = 3*coef p 0 j - coef p (p : R2 p) j := by
  obtain ⟨c, hc⟩ := coef_affine hp hj
  rw [hc (-(p : R2 p)*half p) (by simp), hc (p : R2 p) (by simp)]
  linear_combination -(p : R2 p)*c*two_half hp hp2

private lemma rising_zero (p j : ℕ) : rising p 0 j = (j.factorial : R2 p) := by
  induction j with
  | zero => simp [rising]
  | succ j ih => rw [rising_succ, ih, Nat.factorial_succ]; push_cast; ring

private lemma coef_zero_eq {p j : ℕ} (hp : p.Prime) (hj : j < p) :
    coef p 0 j = (((2*j).choose j)^2 * (4*j).choose (2*j) : ℕ) := by
  have h := (rising_unit hp hj (v := 0) (map_zero _)).pow 4
  rw [rising_zero] at h
  apply h.mul_left_cancel
  rw [show coef p 0 j = ((4*j).factorial : R2 p) * (j.factorial : R2 p)⁻¹ ^ 4 by
    simp [coef, rising_zero]]
  have hu := ZMod.mul_inv_of_unit _ (rising_unit hp hj (v := 0) (map_zero _))
  rw [rising_zero] at hu
  rw [mul_left_comm, ← mul_pow, hu, one_pow, mul_one]
  have h1 := Nat.choose_mul_factorial_mul_factorial (n := 2*j) (k := j) (by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (n := 4*j) (k := 2*j) (by omega)
  rw [show 2*j-j=j by omega] at h1
  rw [show 4*j-2*j=2*j by omega] at h2
  push_cast
  have h1' := congrArg (fun n : ℕ => (n : R2 p)) h1
  have h2' := congrArg (fun n : ℕ => (n : R2 p)) h2
  push_cast at h1' h2'
  linear_combination -h2' - ((4*j).choose (2*j) : R2 p) *
    ((2*j).choose j * (j.factorial : R2 p)^2 + ((2*j).factorial : R2 p))*h1'

private lemma sum_range_pairs {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    (∑ k ∈ range (2*n), f k) = ∑ j ∈ range n, (f (2*j)+f (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ac_rfl

private lemma even_binom_sum {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p = 2*h+1) :
    (2 : R2 p)^(p-1) = ∑ j ∈ range (h+1), (p.choose (2*j) : R2 p) := by
  have hS : ∑ k ∈ range (p+1), (p.choose k : R2 p) = (2 : R2 p)^p := by
    simpa only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n : R2 p)) (Nat.sum_range_choose p)
  rw [show p+1=2*(h+1) by omega, sum_range_pairs, sum_add_distrib] at hS
  have href : (∑ j ∈ range (h+1), (p.choose (2*j+1) : R2 p)) =
      ∑ j ∈ range (h+1), (p.choose (2*j) : R2 p) := by
    rw [← sum_range_reflect (fun j => (p.choose (2*j) : R2 p))]
    apply sum_congr rfl
    intro j hj
    change (p.choose (2*j+1) : R2 p) = (p.choose (2*(h+1-1-j)) : R2 p)
    have hj' := mem_range.mp hj
    rw [← Nat.choose_symm (by omega : 2*j+1 ≤ p), show p-(2*j+1)=2*(h+1-1-j) by omega]
  have hpow : (2 : R2 p)^p = 2*2^(p-1) := by
    calc
      _ = (2 : R2 p)^(p-1+1) := congrArg (fun n : ℕ => (2 : R2 p)^n) (by omega)
      _ = _ := _root_.pow_succ' _ _
  rw [href, ← two_mul, hpow] at hS
  exact (unit_small hp (by decide : 0 < 2) hp2).mul_left_cancel hS.symm

private lemma choose_sign_red {p j : ℕ} (hp : p.Prime) (hj : j < p) :
    ((p-1).choose j : ZMod p) = (-1 : ZMod p)^j := by
  have h : IsUnit (j.factorial : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (hp.coprime_factorial_of_lt hj).symm
  apply h.mul_left_cancel
  rw [choose_mul_factorial_prod (by omega), Nat.cast_sub (by omega : 1 ≤ p), ZMod.natCast_self, zero_sub]
  have he : ∀ i : ℕ, (-1 : ZMod p) - (i : ZMod p) = (-1 : ZMod p)*((i : ZMod p)+1) := by
    intro i
    ring
  simp only [Nat.cast_one, he]
  rw [prod_mul_distrib, prod_const, card_range]
  have hprod : ∏ i ∈ range j, ((i : ZMod p)+1) = (j.factorial : ZMod p) := by
    clear h he hj hp
    induction j with
    | zero => simp
    | succ j ih =>
      rw [prod_range_succ, ih, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, mul_comm]
  rw [hprod, mul_comm]

private lemma prod_linear {R : Type*} [CommRing R] (s : Finset ℕ) (v : R)
    (hv : v^2 = 0) (f : ℕ → R) :
    ∏ i ∈ s, (1+v*f i) = 1+v*(∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi, ih]
    linear_combination f i * (∑ j ∈ s, f j) * hv

private lemma morley_data {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p = 2*h+1) :
    ∃ q : R2 p, q^2 = 0 ∧ (2 : R2 p)^(p-1) = 1+q ∧
      ((p-1).choose h : R2 p) = (-1)^h * ((2 : R2 p)^(p-1))^2 := by
  let P : R2 p := p
  let H : R2 p := ∑ j ∈ range h, ((j : R2 p)+1)⁻¹
  let q : R2 p := -P * half p * H
  have hP : P^2 = 0 := p_sq_zero p
  have hq : q^2 = 0 := by dsimp [q]; rw [mul_pow, mul_pow, neg_pow, hP]; simp
  have h1 (j : ℕ) (hj : j < h) :
      (p.choose (2*(j+1)) : R2 p) = -P * half p * ((j : R2 p)+1)⁻¹ := by
    have H0 := Nat.add_one_mul_choose_eq (p-1) (2*j+1)
    rw [show p-1+1=p by omega, show 2*j+1+1=2*(j+1) by omega] at H0
    have H0' := congrArg (fun n : ℕ => (n : R2 p)) H0
    push_cast at H0'
    have H1 : red p (((p-1).choose (2*j+1) : R2 p) + 1) = 0 := by
      rw [map_add, map_natCast, map_one, choose_sign_red hp (by omega),
        Odd.neg_one_pow (show Odd (2*j+1) from ⟨j, by omega⟩), neg_add_cancel]
    obtain ⟨c, hc⟩ := red_kern hp H1
    have H2 : P * ((p-1).choose (2*j+1) : R2 p) = -P := by
      linear_combination P*hc+c*hP
    have hu : IsUnit ((j : R2 p)+1) := by
      rw [← Nat.cast_succ]
      exact unit_small hp (by omega) (by omega)
    have hi := ZMod.mul_inv_of_unit _ hu
    have htwo := two_half hp hp2
    apply ((unit_small hp (show 0 < 2 by decide) hp2).mul hu).mul_left_cancel
    change 2*((j : R2 p)+1)*(p.choose (2*(j+1)) : R2 p) = _
    linear_combination -H0' + H2 + P*((j : R2 p)+1)⁻¹*((j : R2 p)+1)*htwo + P*hi
  have hb : (2 : R2 p)^(p-1) = 1+q := by
    rw [even_binom_sum hp hp2 hh, sum_range_succ', Nat.mul_zero, choose_zero_right,
      Nat.cast_one, add_comm]
    congr 1
    change (∑ j ∈ range h, (p.choose (2*(j+1)) : R2 p)) =
      -P*half p*(∑ j ∈ range h, ((j : R2 p)+1)⁻¹)
    rw [mul_sum]
    exact sum_congr rfl fun j hj => h1 j (mem_range.mp hj)
  refine ⟨q, hq, hb, ?_⟩
  have hchoose : ((p-1).choose h : R2 p) =
      (-1)^h * ∏ i ∈ range h, (1-P*((i : R2 p)+1)⁻¹) := by
    have hu : IsUnit (h.factorial : R2 p) := by
      rw [← rising_zero]
      exact rising_unit hp (by omega) (map_zero _)
    apply hu.mul_left_cancel
    rw [choose_mul_factorial_prod (by omega)]
    have hrange : (∏ i ∈ range h, ((i : R2 p)+1)) = (h.factorial : R2 p) := by
      rw [← rising_zero p h]
      simp [rising]
    have hsign : (-1 : R2 p)^h = ∏ i ∈ range h, (-1 : R2 p) := by
      rw [prod_const, card_range]
    rw [← hrange, hsign]
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    apply prod_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    have hU : IsUnit ((i : R2 p)+1) := by
      rw [← Nat.cast_succ]
      exact unit_small hp (by omega) (by omega)
    have hInv := ZMod.mul_inv_of_unit _ hU
    push_cast [show 1 ≤ p by omega]
    linear_combination -P*hInv
  rw [hchoose, hb]
  congr 1
  simp_rw [sub_eq_add_neg, ← neg_mul]
  rw [prod_linear _ (-P) (by rw [neg_sq]; exact hP)]
  change 1 + -P*H = (1+q)^2
  have htwo := two_half hp hp2
  unfold q at hq ⊢
  linear_combination P*H*htwo - hq


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

private lemma quad_kernel {p : ℕ} (hp : p.Prime) (x : Quadr (R2 p))
    (hx : quadMap (red p) x = 0) : ∃ y : Quadr (R2 p), x = (p : Quadr (R2 p))*y := by
  have hr : red p x.re = 0 := congrArg QuadraticAlgebra.re hx
  have hi : red p x.im = 0 := congrArg QuadraticAlgebra.im hx
  obtain ⟨r, hr⟩ := red_kern hp hr
  obtain ⟨i, hi⟩ := red_kern hp hi
  refine ⟨⟨r,i⟩, ?_⟩
  ext
  · simpa [QuadraticAlgebra.re_mul] using hr
  · simpa [QuadraticAlgebra.im_mul] using hi

private def period (p : ℕ) (v : R2 p) {R : Type*} [CommRing R] [Algebra (R2 p) R] (z : R) : R :=
  ∑ j ∈ range p, algebraMap (R2 p) R (coef p v j) * z^j

private def sourceV {R : Type*} [CommRing R] (first : Bool) (r : R) : R × R :=
  if first then (r*(r+4)^5, r+5) else (r^5*(r+4), (r+5)^5)

private def branch {R : Type*} [CommRing R] (first : Bool) (r : R) : R × R :=
  let (n,d) := sourceV first r
  (n*d, (n+64*d)^2)

private def jacFirst {R : Type*} [CommRing R] (r : R) : R :=
  let (n,d) := sourceV true r
  (5*(r+4)^4*(r^2+6*r+4))*(n+64*d)*(64*d-n)

/-- The common Frobenius lift on the ordinary part of the degree-five
correspondence, with the first branch used as a local parameter. -/
def H1 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 < p →
    ∀ (R : Type) [CommRing R] [Algebra (R2 p) R] (r a b : R),
      IsUnit (jacFirst r) →
      IsUnit (branch true r).2 → IsUnit (branch false r).2 →
      (branch true r).1 = a*(branch true r).2 →
      (branch false r).1 = b*(branch false r).2 →
      IsUnit (period p 0 a) → IsUnit (period p 0 b) →
      ∃ e : R, let r' := r^p + (p : R)*e
        (branch true r').1 * period p 0 a =
          (branch true r').2 * a^p * period p (p : R2 p) a ∧
        (branch false r').1 * period p 0 b =
          (branch false r').2 * b^p * period p (p : R2 p) b

/-- Sun and Ye's evaluation at the point of discriminant minus twenty. -/
def H2 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 < p → (p % 20 = 3 ∨ p % 20 = 7) →
    ∀ x y : ℤ, 2*(p : ℤ) = x^2+5*y^2 →
      (∑ j ∈ range p,
        ((((2*j).choose j)^2 * (4*j).choose (2*j) : ℕ) : R2 p)*t0 p^j) =
        (2*(p : ℤ)-2*x^2 : ℤ)

section

private lemma scalar_unit {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) :
    IsUnit (2 : R2 p) ∧ IsUnit (5 : R2 p) :=
  ⟨unit_small hp (n := 2) (by decide) (by omega), unit_small hp (n := 5) (by decide) hp5⟩

private lemma root_data {R : Type*} [CommRing R] {s i : R} (hs : s^2 = 5)
    (hi : 2*i = 1) (h2 : IsUnit (2 : R)) (h5 : IsUnit (5 : R)) :
    let r := -5+s
    let z := -i^10
    IsUnit r ∧ IsUnit (r+4) ∧ IsUnit (r+5) ∧
    IsUnit (jacFirst r) ∧ IsUnit (branch true r).2 ∧ IsUnit (branch false r).2 ∧
    (branch true r).1 = z*(branch true r).2 ∧
    (branch false r).1 = z*(branch false r).2 ∧
    IsUnit (4096*(sourceV true r).2*(sourceV false r).2 -
      (sourceV true r).1*(sourceV false r).1) := by
  let r : R := -5+s
  let v : R := -576+256*s
  let z : R := -i^10
  have hq : (r+4)*(r+5) = -r := by
    dsimp [r]
    linear_combination hs
  have hA : r*(r+4)^5 = v*(r+5) := by
    dsimp [r, v]
    linear_combination (s^4-10*s^3+40*s^2-110*s-1)*hs
  have hB : r^5*(r+4) = v*(r+5)^5 := by
    dsimp [r, v]
    linear_combination (-255*s^4+550*s^3-1000*s^2+1250*s-625)*hs
  have hu1 : IsUnit r := by
    have hh : r*(-5-s) = (2 : R)^2*5 := by
      dsimp [r]
      linear_combination -hs
    exact isUnit_of_mul_isUnit_left (hh ▸ (h2.pow 2).mul h5)
  have hu2 : IsUnit (r+4) := by
    have hh : (r+4)*(-1-s) = -(2 : R)^2 := by
      dsimp [r]
      linear_combination -hs
    exact isUnit_of_mul_isUnit_left (hh ▸ (h2.pow 2).neg)
  have hu3 : IsUnit (r+5) := by
    have hh : (r+5)^2 = 5 := by
      dsimp [r]
      linear_combination hs
    have H : IsUnit ((r+5)^2) := by rw [hh]; exact h5
    rw [pow_two] at H
    exact isUnit_of_mul_isUnit_left H
  have hplus : IsUnit (v+64) := by
    have hz : (s-2)*(-s-2) = -1 := by linear_combination -hs
    have he : v+64 = (2 : R)^8*(s-2) := by dsimp [v]; ring
    rw [he]
    exact (h2.pow 8).mul (isUnit_of_mul_isUnit_left (hz ▸ isUnit_one.neg))
  have hminus : IsUnit (64-v) := by
    have hz : (5-2*s)*(5+2*s) = 5 := by linear_combination -4*hs
    have he : 64-v = (2 : R)^7*(5-2*s) := by dsimp [v]; ring
    rw [he]
    exact (h2.pow 7).mul (isUnit_of_mul_isUnit_left (hz ▸ h5))
  have hv : v = z*(v+64)^2 := by
    have hs' : (v+64)^2 = -1024*v := by
      dsimp [v]
      linear_combination 65536*hs
    have hi' : (2 : R)^10*i^10 = 1 := by rw [← mul_pow, hi, one_pow]
    rw [hs']
    dsimp [z]
    linear_combination -v*hi'
  have hC : r^2+6*r+4 = -4*(r+4) := by
    dsimp [r]
    linear_combination hs
  have ej : jacFirst r = (-((2:R)^2*5))*(r+4)^5*((v+64)*(r+5))*((64-v)*(r+5)) := by
    simp only [jacFirst, sourceV, if_true, hA, hC]
    ring
  have ea : branch true r = (v*(r+5)^2, ((v+64)*(r+5))^2) := by
    simp only [branch, sourceV, if_true, hA, Prod.mk.injEq]
    constructor <;> ring
  have eb : branch false r = (v*((r+5)^5)^2, ((v+64)*(r+5)^5)^2) := by
    simp only [branch, sourceV, Bool.false_eq_true, if_false, hB, Prod.mk.injEq]
    constructor <;> ring
  have en : 4096*(sourceV true r).2*(sourceV false r).2 -
      (sourceV true r).1*(sourceV false r).1 =
      (64-v)*(64+v)*(r+5)*(r+5)^5 := by
    simp only [sourceV, if_true, Bool.false_eq_true, if_false, hA, hB]
    ring
  change IsUnit r ∧ IsUnit (r+4) ∧ IsUnit (r+5) ∧
    IsUnit (jacFirst r) ∧ IsUnit (branch true r).2 ∧ IsUnit (branch false r).2 ∧
    (branch true r).1 = z*(branch true r).2 ∧ (branch false r).1 = z*(branch false r).2 ∧ _
  refine ⟨hu1, hu2, hu3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ej]
    exact ((((h2.pow 2).mul h5).neg.mul (hu2.pow 5)).mul (hplus.mul hu3)).mul (hminus.mul hu3)
  · rw [ea]
    exact (hplus.mul hu3).pow 2
  · rw [eb]
    exact (hplus.mul (hu3.pow 5)).pow 2
  · rw [ea]
    linear_combination (r+5)^2*hv
  · rw [eb]
    linear_combination ((r+5)^5)^2*hv
  · rw [en, add_comm (64 : R) v]
    exact ((hminus.mul hplus).mul hu3).mul (hu3.pow 5)

private lemma branch_diagonal {R : Type*} [CommRing R] (r : R) :
    (branch true r).1*(branch false r).2 - (branch false r).1*(branch true r).2 =
    (r^2+10*r+20) * (r*(r+4)*(r+5)*((r+4)*(r+5)-r)*(((r+4)*(r+5))^2+r^2) *
      (4096*(sourceV true r).2*(sourceV false r).2 -
        (sourceV true r).1*(sourceV false r).1)) := by
  simp only [branch, sourceV, if_true, Bool.false_eq_true, if_false]
  ring

private lemma unit_near {R : Type*} [CommRing R] {v e : R} (hv : IsUnit v) (he : e^2 = 0) :
    IsUnit (v+e) := by
  obtain ⟨u, rfl⟩ := hv
  have hi : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := Units.mul_inv _
  let a := ((u⁻¹ : Rˣ) : R)
  have h : ((u : R)+e)*(a-a^2*e)=1 := by
    change (u : R)*a = 1 at hi
    linear_combination (1-a*e)*hi-a^2*he
  exact IsUnit.of_mul_eq_one _ h

private lemma poly_unit_near {R : Type*} [CommRing R] (f : Polynomial R) {r e : R}
    (he : e^2=0) (hu : IsUnit (f.eval r)) : IsUnit (f.eval (r+e)) := by
  rw [Polynomial.eval_add_of_sq_eq_zero _ _ _ he]
  exact unit_near hu (by rw [mul_pow, he, mul_zero])

open Polynomial

private lemma same_branch_simple_root {R : Type*} [CommRing R] {s i e : R}
    (hs : s^2=5) (hi : 2*i=1) (h2 : IsUnit (2:R)) (h5 : IsUnit (5:R)) (he : e^2=0)
    (hdiag : (branch true (-5+s+e)).1*(branch false (-5+s+e)).2 =
      (branch false (-5+s+e)).1*(branch true (-5+s+e)).2) :
    e = 0 := by
  obtain ⟨hu1, hu2, hu3, _, _, _, _, _, hlast⟩ := root_data hs hi h2 h5
  let r := -5+s
  let f : R[X] :=
    X*(X+4)*(X+5)*((X+4)*(X+5)-X)*(((X+4)*(X+5))^2+X^2) *
      (4096*(sourceV true X).2*(sourceV false X).2 -
        (sourceV true X).1*(sourceV false X).1)
  have hprod (x : R) : f.eval x =
      x*(x+4)*(x+5)*((x+4)*(x+5)-x)*(((x+4)*(x+5))^2+x^2) *
      (4096*(sourceV true x).2*(sourceV false x).2 -
        (sourceV true x).1*(sourceV false x).1) := by
    simp [f, sourceV]
  have hq : (r+4)*(r+5) = -r := by
    dsimp [r]
    linear_combination hs
  have hfr : IsUnit (f.eval r) := by
    rw [hprod, hq, show -r-r = -(2*r) by ring, show (-r)^2+r^2=2*r^2 by ring]
    exact (((((hu1.mul hu2).mul hu3).mul (h2.mul hu1).neg).mul
      (h2.mul (hu1.pow 2))).mul hlast)
  have hu := poly_unit_near f he hfr
  have hz := branch_diagonal (r+e)
  rw [← hprod, sub_eq_zero.mpr hdiag] at hz
  have hroot : (r+e)^2+10*(r+e)+20 = 0 := hu.mul_right_cancel (by rw [zero_mul]; exact hz.symm)
  have hsunit : IsUnit s := by
    exact isUnit_of_mul_isUnit_left (by rw [← pow_two, hs]; exact h5)
  apply (h2.mul hsunit).mul_left_cancel
  rw [mul_zero]
  dsimp [r] at hroot
  linear_combination hroot - he - hs

private lemma frob_near_root {p h : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hh : p = 2*h+1) :
    ∃ s e : Quadr (R2 p), s^2=5 ∧
      (-5 + QuadraticAlgebra.omega : Quadr (R2 p))^p = -5+s+(p : Quadr (R2 p))*e := by
  letI : Fact p.Prime := ⟨hp⟩
  let K := Quadr (ZMod p)
  letI : CharP K p := charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective p
  let f := algebraMap (ZMod p) K
  let q := quadMap (red p)
  let u : K := QuadraticAlgebra.omega
  let d : ZMod p := 5^h
  have h5u : IsUnit (5 : ZMod p) := by
    simpa only [map_ofNat] using (scalar_unit hp hp5).2.map (red p)
  have hpow : (5 : ZMod p)^(p-1) = 1 := ZMod.pow_card_sub_one_eq_one h5u.ne_zero
  have hd : d^2 = 1 := by
    dsimp [d]
    rw [← pow_mul, show h*2=p-1 by omega, hpow]
  have hu : u^p = f d*u := by
    calc
      _ = u^(2*h+1) := congrArg (fun n : ℕ => u^n) hh
      _ = (u^2)^h*u := by rw [pow_succ, ← pow_mul]
      _ = _ := by
        rw [quad_omega_sq]
        simp only [d, map_pow, map_ofNat]
  have hneg : (-5 : K)^p = -5 := by
    have ht := congrArg f (ZMod.pow_card (-5 : ZMod p))
    simpa only [map_pow, map_neg, map_ofNat, f] using ht
  have hmap : q (QuadraticAlgebra.omega : Quadr (R2 p)) = u := by
    ext <;> simp [q, quadMap, u, QuadraticAlgebra.omega]
  have hex (s : Quadr (R2 p)) (hs : s^2=5) (hm : f d*u = q s) :
      ∃ s e : Quadr (R2 p), s^2=5 ∧
        (-5 + QuadraticAlgebra.omega : Quadr (R2 p))^p = -5+s+(p : Quadr (R2 p))*e := by
    have hz : q (((-5+QuadraticAlgebra.omega : Quadr (R2 p))^p)-(-5+s)) = 0 := by
      simp only [map_sub, map_pow, map_add, map_neg, map_ofNat, hmap]
      rw [add_pow_char _ _ p, hneg, hu, hm, sub_self]
    obtain ⟨e, he⟩ := quad_kernel hp _ hz
    exact ⟨s, e, hs, by linear_combination he⟩
  rcases sq_eq_one_iff.mp hd with hd' | hd'
  · apply hex QuadraticAlgebra.omega (quad_omega_sq _)
    simp [hd', hmap]
  · apply hex (-QuadraticAlgebra.omega) (by rw [neg_sq, quad_omega_sq])
    simp [hd', hmap, neg_one_mul]

private lemma block_specialization (hcompat : H1) {p h : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hh : p = 2*h+1) (hsum : IsUnit (period p 0 (t0 p))) :
    (t0 p)^p * period p (p : R2 p) (t0 p) = (t0 p)*period p 0 (t0 p) := by
  let R := Quadr (R2 p)
  let f := algebraMap (R2 p) R
  let i := f (half p)
  let z := f (t0 p)
  let r : R := -5+QuadraticAlgebra.omega
  have htwo : (2 : R)*i = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using congrArg f (two_half hp (by omega))
  have hi : -i^10 = z := by simp [z, i, t0]
  have hp0 : (p : R)^2=0 := by
    simpa only [map_pow, map_zero, map_natCast] using congrArg f (p_sq_zero p)
  have h2 : IsUnit (2 : R) := by
    simpa only [map_ofNat] using (scalar_unit hp hp5).1.map f
  have h5 : IsUnit (5 : R) := by
    simpa only [map_ofNat] using (scalar_unit hp hp5).2.map f
  have hmap (v : R2 p) : f (period p v (t0 p)) = period p v z := by
    simp [period, z, f]
  have hs : IsUnit (period p 0 z) := by rw [← hmap]; exact hsum.map f
  obtain ⟨_, _, _, hj, hD, hE, hA, hB, _⟩ :=
    root_data (quad_omega_sq (R2 p)) htwo h2 h5
  rw [hi] at hA hB
  obtain ⟨e, he⟩ := hcompat p hp hp5 R r z z hj hD hE hA hB hs hs
  let w := r^p+(p : R)*e
  change (branch true w).1*period p 0 z = (branch true w).2*z^p*period p (p : R2 p) z ∧
      (branch false w).1*period p 0 z = (branch false w).2*z^p*period p (p : R2 p) z at he
  have hd : (branch true w).1*(branch false w).2 =
      (branch false w).1*(branch true w).2 := by
    apply hs.mul_right_cancel
    linear_combination (branch false w).2*he.1-(branch true w).2*he.2
  obtain ⟨s, d, hs5, hrd⟩ := frob_near_root hp hp5 hh
  change r^p = -5+s+(p : R)*d at hrd
  have hw : w = -5+s+(p : R)*(d+e) := by
    dsimp [w]
    linear_combination hrd
  have hnil : ((p : R)*(d+e))^2=0 := by rw [mul_pow, hp0, zero_mul]
  rw [hw] at hd
  have hz0 := same_branch_simple_root hs5 htwo h2 h5 hnil hd
  rw [hz0, add_zero] at hw
  obtain ⟨_, _, _, _, hu, _, haf, _, _⟩ := root_data hs5 htwo h2 h5
  rw [hi] at haf
  have hf := he.1
  rw [hw, haf] at hf
  have hfin : z^p * period p (p : R2 p) z = z * period p 0 z := by
    apply hu.mul_left_cancel
    linear_combination -hf
  apply QuadraticAlgebra.algebraMap_injective (a := (5 : R2 p)) (b := 0)
  simpa only [map_mul, map_pow, ← hmap, z] using hfin

private lemma nilpotent_pow {R : Type*} [CommRing R] {q : R} (hq : q^2=0) (n : ℕ) :
    (1+q)^n = 1+(n : R)*q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ]
    linear_combination (n : R)*hq

private lemma t0_normalizes {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hodd : Odd p) :
    IsUnit (t0 p) ∧ (t0 p)^(p-1)*((2 : R2 p)^(p-1))^10 = 1 := by
  have hi := two_half hp hp2
  have hu : IsUnit (half p) := IsUnit.of_mul_eq_one_right _ hi
  refine ⟨(hu.pow 10).neg, ?_⟩
  have ht : t0 p*(2 : R2 p)^10 = -1 := by
    rw [t0, neg_mul, ← mul_pow, mul_comm (half p) 2, hi, one_pow]
  rw [← pow_mul, Nat.mul_comm (p-1) 10, pow_mul, ← mul_pow, ht]
  obtain ⟨h, hh⟩ := hodd
  have he : Even (p-1) := ⟨h, by omega⟩
  exact he.neg_one_pow

private lemma strip_normalization {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (hh : p = 2*h+1) (ho : Odd h)
    (hf : (t0 p)^p * period p (p : R2 p) (t0 p) = (t0 p)*period p 0 (t0 p)) :
    (∑ n ∈ range p, (OeisA179524.a n : R2 p)) = -period p 0 (t0 p) := by
  let z := t0 p
  let b : R2 p := 2^(p-1)
  let S := period p 0 z
  let T := period p (p : R2 p) z
  have hop : Odd p := ⟨h, hh⟩
  obtain ⟨hu, hnorm⟩ := t0_normalizes hp hp2 hop
  change z^(p-1)*b^10=1 at hnorm
  change z^p*T=z*S at hf
  have hf' : z^(p-1)*T = S := by
    apply hu.mul_left_cancel
    have hzp : z^p = z*z^(p-1) := by
      calc
        _ = z^(p-1+1) := congrArg (fun n : ℕ => z^n) (by omega)
        _ = _ := _root_.pow_succ' _ _
    rw [hzp] at hf
    linear_combination hf
  have hT : T = b^10*S := by
    linear_combination b^10*hf' - T*hnorm
  obtain ⟨q, hq, hb, hm⟩ := morley_data hp hp2 hh
  change b=1+q at hb
  have hW : weight p h 0 = -b^5 := by
    have ha : (-4 : R2 p)^h = -b := by
      calc
        _ = (-1 : R2 p)^h * (4 : R2 p)^h := by rw [← mul_pow]; ring
        _ = -b := by
          rw [ho.neg_one_pow, neg_one_mul]
          unfold b
          rw [show (4 : R2 p)=(2 : R2 p)^2 by ring, ← pow_mul, show 2*h=p-1 by omega]
    unfold weight
    rw [Nat.sub_zero, show 2*h=p-1 by omega, Nat.mul_zero, choose_zero_right, Nat.cast_one,
      pow_zero, ha, hm]
    have hsq : ((-1 : R2 p)^h)^2 = 1 := by rw [ho.neg_one_pow]; ring
    change -b * ((-1 : R2 p)^h * b^2)^2 * 1 * 1 = -b^5
    rw [mul_pow, hsq]
    ring
  have hl : 2*(∑ j ∈ range p, coef p (-(p : R2 p)*half p) j * z^j) = 3*S-T := by
    unfold S T period
    simp only [Algebra.algebraMap_self, RingHom.id_apply, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j hj
    linear_combination z^j*coef_interpolate hp hp2 (mem_range.mp hj)
  have hQ : b^5*(3-b^10) = 2 := by
    rw [hb, nilpotent_pow hq 5, nilpotent_pow hq 10]
    push_cast
    linear_combination -50*hq
  rw [collapse_shifted hp hp2 hh, hW]
  change -b^5*(∑ j ∈ range p, coef p (-(p : R2 p)*half p) j * z^j) = -S
  apply (unit_small hp (by decide : 0 < 2) hp2).mul_left_cancel
  linear_combination -b^5*(hl-hT) - S*hQ

private lemma period_value (heval : H2) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hm : p % 20 = 3 ∨ p % 20 = 7) {x y : ℤ} (hxy : 2*(p : ℤ)=x^2+5*y^2) :
    period p 0 (t0 p) = ((2*(p : ℤ)-2*x^2 : ℤ) : R2 p) := by
  unfold period
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [← heval p hp hp5 hm x y hxy]
  exact sum_congr rfl fun j hj => congrArg (fun c : R2 p => c*t0 p^j)
    (coef_zero_eq hp (mem_range.mp hj))

private lemma period_value_unit {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hm : p % 20 = 3 ∨ p % 20 = 7) {x y : ℤ} (hxy : 2*(p : ℤ)=x^2+5*y^2) :
    IsUnit ((2*(p : ℤ)-2*x^2 : ℤ) : R2 p) := by
  have habs : |x| < (p : ℤ) := by
    apply abs_lt.mpr
    constructor
    · by_contra! h
      have h0 : 0 ≤ (-x-(p : ℤ))*(-x+(p : ℤ)) := mul_nonneg (by omega) (by omega)
      nlinarith [sq_nonneg y]
    · by_contra! h
      have h0 : 0 ≤ (x-(p : ℤ))*(x+(p : ℤ)) := mul_nonneg (by omega) (by omega)
      nlinarith [sq_nonneg y]
  have hx : (x : ZMod p) ≠ 0 := by
    intro h
    have hx0 := Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h) habs
    rw [hx0, zero_pow (by decide : 2 ≠ 0), zero_add] at hxy
    omega
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : IsUnit (2 : ZMod p) := by
    simpa only [map_ofNat] using (scalar_unit hp hp5).1.map (red p)
  apply unit_red hp
  push_cast
  simp only [map_sub, map_mul, map_pow, map_natCast, map_intCast, map_ofNat, ZMod.natCast_self,
    mul_zero, zero_sub, neg_ne_zero]
  exact mul_ne_zero h2.ne_zero (pow_ne_zero _ hx)

private lemma case_three (x y : ℤ) (hxy : 2 * (3 : ℤ) = x^2+5*y^2) :
    ∑ n ∈ range 3, OeisA179524.a n ≡ 2*x^2-2*(3 : ℤ) [ZMOD (3 : ℤ)^2] := by
  have hxs : |x| < 3 := by
    apply abs_lt.mpr
    constructor
    · by_contra! h
      have h0 : 0 ≤ (-x-3)*(-x+3) := mul_nonneg (by omega) (by omega)
      nlinarith [sq_nonneg y]
    · by_contra! h
      have h0 : 0 ≤ (x-3)*(x+3) := mul_nonneg (by omega) (by omega)
      nlinarith [sq_nonneg y]
  have hys : |y| < 2 := by
    apply abs_lt.mpr
    constructor
    · by_contra! h
      have h0 : 0 ≤ (-y-2)*(-y+2) := mul_nonneg (by omega) (by omega)
      nlinarith [sq_nonneg x]
    · by_contra! h
      have h0 : 0 ≤ (y-2)*(y+2) := mul_nonneg (by omega) (by omega)
      nlinarith [sq_nonneg x]
  have hx : x^2 = 1 := by
    rw [abs_lt] at hxs hys
    obtain ⟨hxl,hxu⟩ := hxs
    obtain ⟨hyl,hyu⟩ := hys
    interval_cases x <;> interval_cases y <;> norm_num at hxy
    all_goals norm_num
  rw [hx]
  norm_num [sum_range_succ, OeisA179524.a_0, OeisA179524.a_1, OeisA179524.a_2, Int.ModEq]

theorem main : H1 → H2 → type_of% @OeisA179524.conjecture2 := by
  intro hcompat heval p hp hmod x y hxy
  have hm : p % 20 = 3 ∨ p % 20 = 7 := by
    rcases hmod with ha | ha <;> unfold Int.ModEq at ha <;> omega
  by_cases hp3 : p = 3
  · subst p
    exact case_three x y hxy
  have hp5 : 5 < p := by omega
  let h := (p-1)/2
  have hh : p = 2*h+1 := by dsimp [h]; omega
  have ho : Odd h := by
    use h/2
    dsimp [h]
    omega
  have hperiod := period_value heval hp hp5 hm hxy
  have hu : IsUnit (period p 0 (t0 p)) := by
    rw [hperiod]
    exact period_value_unit hp hp5 hm hxy
  have hf := block_specialization hcompat hp hp5 hh hu
  have H := strip_normalization hp (by omega) hh ho hf
  rw [hperiod, ← Int.cast_neg] at H
  have Hz : ((∑ n ∈ range p, OeisA179524.a n : ℤ) : R2 p) =
      ((2*x^2-2*(p : ℤ) : ℤ) : R2 p) := by
    rw [Int.cast_sum, H]
    congr 1
    ring
  simpa only [Nat.cast_pow] using (ZMod.intCast_eq_intCast_iff _ _ _).mp Hz

end

end OMA.R_OeisA179524_conjecture2_R1
