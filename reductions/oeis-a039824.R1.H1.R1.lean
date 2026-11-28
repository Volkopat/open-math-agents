import OMAReductions.R_oeis_a039824_R1
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Strict monotonicity near both ends of Stephan's polynomial

The weighted derivative of the product bounds adjacent coefficients near degree zero.
After removing the factor 1+X from the reverse product, a second weighted derivative
compares coefficients at distance two. Restoring 1+X gives consecutive strict
inequalities beyond the first reversed coefficient.

Source: https://oeis.org/A039824
Credit: @HBreitkreutz
-/

namespace OMA.R_oeis_a039824_R1_H1_R1

open Polynomial Finset OMA.S_oeis_a039824
open OMA.R_oeis_a039824_R1

lemma coeff_le_mul_right {p q : ℕ[X]} (h : ∀ k, p.coeff k ≤ q.coeff k)
    (r : ℕ[X]) (k : ℕ) : (p*r).coeff k ≤ (q*r).coeff k := by
  rw [coeff_mul, coeff_mul]
  exact sum_le_sum (fun a _ => Nat.mul_le_mul_right _ (h a.1))

lemma weighted_derivative_coeff (p : ℕ[X]) (k : ℕ) :
    ((1+X)*derivative p).coeff k = (k+1)*p.coeff (k+1) + k*p.coeff k := by
  rw [add_mul, one_mul, coeff_add, coeff_derivative]
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_X_mul, coeff_derivative]
    change p.coeff (k+1+1)*(k+1+1) + p.coeff (k+1)*(k+1) =
      (k+1+1)*p.coeff (k+1+1) + (k+1)*p.coeff (k+1)
    ac_rfl

lemma factor_derivative_bound (p : ℕ[X]) (h : p.coeff 0 ≤ p.coeff 1) (k : ℕ) :
    p.coeff k ≤ ((1+X)*derivative p).coeff k := by
  rw [weighted_derivative_coeff]
  cases k with
  | zero => simpa using h
  | succ k =>
    have hm := Nat.mul_le_mul_right (p.coeff (k+1)) (show 1 ≤ k+1 by omega)
    simpa only [one_mul] using hm.trans (Nat.le_add_left _ _)

lemma differentiated_product (n k : ℕ) :
    (C n * P n).coeff k ≤ ((1+X)*derivative (P n)).coeff k := by
  let f (i : ℕ) : ℕ[X] := 1 + ∑ j ∈ range i, X^(2*j+1)
  have spec (i : ℕ) : f i = 1 + ∑ j ∈ range i, X^(2*j+1) := rfl
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    have e : (f (n+1)).coeff 0 ≤ (f (n+1)).coeff 1 := by simp [factor_coeff spec]
    have h₁ := coeff_le_mul_right ih (f (n+1)) k
    have h₂ := coeff_le_mul_right (factor_derivative_bound _ e) (P n) k
    rw [product_step spec, derivative_mul]
    have lhs : C (n+1 : ℕ)*(P n*f (n+1)) = (C n*P n)*f (n+1) + f (n+1)*P n := by
      rw [show C (n+1 : ℕ) = C n + 1 by simp]
      ring
    have rhs : (1+X)*(derivative (P n)*f (n+1)+P n*derivative (f (n+1))) =
        ((1+X)*derivative (P n))*f (n+1) + ((1+X)*derivative (f (n+1)))*P n := by ring
    rw [lhs, rhs, coeff_add, coeff_add]
    exact Nat.add_le_add h₁ h₂

theorem front_inequality (n k : ℕ) :
    n*(P n).coeff k ≤ (k+1)*(P n).coeff (k+1) + k*(P n).coeff k := by
  simpa only [coeff_C_mul, weighted_derivative_coeff] using differentiated_product n k

lemma strict_from_weight {n k a b : ℕ} (w : n*a ≤ (k+1)*b+k*a) (ha : 0 < a)
    (hk : 2*k+1 < n) : a < b := by
  by_contra! h
  have hm := Nat.mul_le_mul_left (k+1) h
  have hl := Nat.mul_lt_mul_of_pos_right hk ha
  nlinarith

lemma early (n k : ℕ) (h : 2*k+1 < n) :
    0 < (P n).coeff k ∧ (P n).coeff k < (P n).coeff (k+1) := by
  induction k with
  | zero =>
    have pos : 0 < (P n).coeff 0 := by
      rw [product_zero (factor := fun i => 1 + ∑ j ∈ range i, X^(2*j+1)) (fun _ => rfl)]
      decide
    exact ⟨pos, strict_from_weight (front_inequality n 0) pos h⟩
  | succ k ih =>
    have prev := ih (by omega)
    have pos := prev.1.trans prev.2
    exact ⟨pos, strict_from_weight (front_inequality n (k+1)) pos h⟩

theorem front_increasing (n a b : ℕ) (hab : a < b) (hb : 2*b ≤ n) :
    (P n).coeff a < (P n).coeff b := by
  induction b with
  | zero => omega
  | succ b ih =>
    have t := (early n b (by omega)).2
    by_cases e : a = b
    · simpa [e] using t
    · exact (ih (by omega) (by omega)).trans t


lemma euler_coeff (p : ℕ[X]) (k : ℕ) : (X * derivative p).coeff k = k * p.coeff k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_X_mul, coeff_derivative]
    change p.coeff (k+1)*(k+1) = (k+1)*p.coeff (k+1)
    exact Nat.mul_comm _ _

lemma stride_weight (p : ℕ[X]) (k : ℕ) :
    ((1+X^2)*(X*derivative p)).coeff (k+2) = (k+2)*p.coeff (k+2) + k*p.coeff k := by
  rw [add_mul, one_mul, coeff_add, coeff_X_pow_mul, euler_coeff, euler_coeff]

lemma stride_factor (p : ℕ[X]) (h0 : p.coeff 0 = 1) (h1 : p.coeff 1 = 0)
    (h2 : p.coeff 2 = 1) (k : ℕ) :
    (C 2*(X^2*p)).coeff k ≤ ((1+X^2)*(X*derivative p)).coeff k := by
  rw [coeff_C_mul]
  obtain _ | _ | d := k
  · simp
  · simp [coeff_X_pow_mul']
  · rw [coeff_X_pow_mul, stride_weight]
    obtain _ | _ | u := d
    · simp [h0, h2]
    · simp [h1]
    · have h := Nat.mul_le_mul_right (p.coeff (u+2)) (show 2 ≤ u+2 by omega)
      exact h.trans (Nat.le_add_left _ _)

section ReversedFactors

variable {f : ℕ → ℕ[X]} (spec : ∀ i, f i = 1 + ∑ j ∈ range i, (X : ℕ[X])^(2*j+1))
variable {t : ℕ → ℕ[X]} (t0 : t 0 = 1) (ts : ∀ n, t (n+1) = t n * (f (n+2)).reverse)
include spec

lemma reverse_small_factor (i : ℕ) (hi : 2 ≤ i) :
    (f i).reverse.coeff 0 = 1 ∧ (f i).reverse.coeff 1 = 0 ∧ (f i).reverse.coeff 2 = 1 := by
  have low (k : ℕ) (hk : k ≤ 2) : (f i).reverse.coeff k = if k%2 = 0 then 1 else 0 := by
    rw [coeff_reverse, (factor_data spec i).2, revAt_le (by omega), factor_coeff spec]
    split_ifs <;> omega
  exact ⟨by simpa using low 0 (by decide), by simpa using low 1 (by decide),
    by simpa using low 2 (by decide)⟩

include ts in
lemma reversed_bound (n k : ℕ) : (C (2*n)*(X^2*t n)).coeff k ≤
    ((1+X^2)*(X*derivative (t n))).coeff k := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    let q := (f (n+2)).reverse
    obtain ⟨h0,h1,h2⟩ := reverse_small_factor spec (n+2) (by omega)
    have ha := coeff_le_mul_right ih q k
    have hb := coeff_le_mul_right (stride_factor q h0 h1 h2) (t n) k
    rw [ts, derivative_mul]
    have lhs : C (2*(n+1))*(X^2*(t n*q)) =
        (C (2*n)*(X^2*t n))*q + (C 2*(X^2*q))*t n := by
      rw [show C (2*(n+1) : ℕ) = C (2*n)+C 2 by rw [Nat.mul_succ, map_add]]
      ring
    have rhs : (1+X^2)*(X*(derivative (t n)*q + t n*derivative q)) =
        ((1+X^2)*(X*derivative (t n)))*q + ((1+X^2)*(X*derivative q))*t n := by ring
    rw [lhs, rhs, coeff_add, coeff_add]
    exact Nat.add_le_add ha hb

include t0 ts in
lemma reverse_split (n : ℕ) : (P (n+1)).reverse = (1+X)*t n := by
  induction n with
  | zero =>
    rw [t0, mul_one, product_step spec, show P 0 = 1 by simp [P], one_mul]
    have f1 : f 1 = 1+X := by simp [spec]
    ext k
    rw [coeff_reverse, (factor_data spec 1).2, f1]
    by_cases hk : k ≤ 1
    · rw [revAt_le (by omega)]
      rcases (show k = 0 ∨ k = 1 by omega) with h | h <;> subst k <;>
        norm_num [coeff_add, coeff_X, coeff_one]
    · rw [revAt_eq_self_of_lt (by omega)]
  | succ n ih =>
    rw [reverse_product spec, ih, ts]
    ring

include t0 ts in
lemma tail_bases (n : ℕ) (hn : 1 ≤ n) :
    (t n).coeff 0 = 1 ∧ (t n).coeff 1 = 0 ∧ (t n).coeff 3 = 1 := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := reverse_low spec (n+1) (by omega)
  rw [reverse_split spec t0 ts] at h0 h1 h2 h3
  simp only [add_mul, one_mul, coeff_add, coeff_X_mul, coeff_X_mul_zero, add_zero] at h0 h1 h2 h3
  omega

include t0 ts in
lemma stride_increasing (n d : ℕ) (hd : d+1 < n) : (t n).coeff d < (t n).coeff (d+2) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    obtain ⟨h0,h1,h3⟩ := tail_bases spec t0 ts n (by omega)
    by_cases one : d=1
    · subst d; simp [h1,h3]
    have pos : 0 < (t n).coeff d := by
      by_cases zero : d=0
      · simp [zero,h0]
      · have lt := ih (d-2) (by omega) (by omega)
        rw [show d-2+2=d by omega] at lt
        omega
    have w := reversed_bound spec ts n (d+2)
    rw [coeff_C_mul, coeff_X_pow_mul, stride_weight] at w
    by_contra! bad
    have ha := Nat.mul_le_mul_left (d+2) bad
    have hb := Nat.mul_lt_mul_of_pos_right (show 2*d+2 < 2*n by omega) pos
    nlinarith

include t0 ts in
lemma reverse_next (n d : ℕ) (hd : d+1 < n) :
    (P (n+1)).reverse.coeff (d+1) < (P (n+1)).reverse.coeff (d+2) := by
  rw [reverse_split spec t0 ts, add_mul, one_mul, coeff_add, coeff_add, coeff_X_mul, coeff_X_mul]
  have h := stride_increasing spec t0 ts n d hd
  omega

end ReversedFactors

theorem back_increasing (N a b : ℕ) (ha : 1 ≤ a) (hab : a < b) (hb : b < N) :
    (P N).reverse.coeff a < (P N).reverse.coeff b := by
  let f (i : ℕ) : ℕ[X] := 1 + ∑ j ∈ range i, X^(2*j+1)
  let t : ℕ → ℕ[X] := Nat.rec 1 (fun n prior => prior*(f (n+2)).reverse)
  have spec (i : ℕ) : f i = 1 + ∑ j ∈ range i, X^(2*j+1) := rfl
  have t0 : t 0 = 1 := rfl
  have ts (j : ℕ) : t (j+1) = t j * (f (j+2)).reverse := rfl
  obtain _ | n := N
  · omega
  induction b with
  | zero => omega
  | succ b ih =>
    have hn : b-1+1 < n := by omega
    have q := reverse_next spec t0 ts n (b-1) hn
    rw [show b-1+1 = b by omega, show b-1+2 = b+1 by omega] at q
    by_cases e : a=b
    · simpa [e] using q
    · exact (ih (by omega) (by omega)).trans q


/-- Remaining comparisons on the rising side, after removing its initial strictly increasing range. -/
def H1 : Prop :=
  ∀ n m i j : ℕ, 6 < n → m ≤ n^2-5 →
    (∀ k : ℕ, k ≤ n^2-5 → (P n).coeff k ≤ (P n).coeff m) →
    i < j → j ≤ m → n < 2*j → (P n).coeff i ≠ (P n).coeff j

/-- Remaining comparisons on the falling side, after removing its final strictly decreasing range. -/
def H2 : Prop :=
  ∀ n m i j : ℕ, 6 < n → m ≤ n^2-5 →
    (∀ k : ℕ, k ≤ n^2-5 → (P n).coeff k ≤ (P n).coeff m) →
    m ≤ i → i < j → j ≤ n^2-5 → n ≤ n^2-i → (P n).coeff i ≠ (P n).coeff j

lemma reverse_offset (n i : ℕ) (hi : i ≤ n^2) :
    (P n).reverse.coeff (n^2-i) = (P n).coeff i := by
  have deg := (product_data (factor := fun v => 1 + ∑ j ∈ range v, (X : ℕ[X])^(2*j+1))
    (fun _ => rfl) n).2
  rw [coeff_reverse, deg, revAt_le (by omega), Nat.sub_sub_self hi]

theorem main : H1 → H2 → OMA.R_oeis_a039824_R1.H1 := by
  intro hleft hright n m hn hm peak
  have big : 49 ≤ n^2 := by nlinarith
  have left {i j : ℕ} (hij : i < j) (hj : j ≤ m) : (P n).coeff i ≠ (P n).coeff j := by
    by_cases edge : 2*j ≤ n
    · exact (front_increasing n i j hij edge).ne
    · exact hleft n m i j hn hm peak hij hj (by omega)
  have right {i j : ℕ} (hi : m ≤ i) (hij : i < j) (hj : j ≤ n^2-5) :
      (P n).coeff i ≠ (P n).coeff j := by
    by_cases edge : n^2-i < n
    · have e := back_increasing n (n^2-j) (n^2-i) (by omega) (by omega) edge
      rw [reverse_offset n j (by omega), reverse_offset n i (by omega)] at e
      exact e.ne'
    · exact hright n m i j hn hm peak hi hij hj (by omega)
  constructor
  · intro i hi j hj eq
    rcases lt_trichotomy i j with h | h | h
    · exact False.elim (left h hj.2 eq)
    · exact h
    · exact False.elim (left h hi.2 eq.symm)
  · intro i hi j hj eq
    rcases lt_trichotomy i j with h | h | h
    · exact False.elim (right hi.1 h hj.2 eq)
    · exact h
    · exact False.elim (right hj.1 h hi.2 eq.symm)

end OMA.R_oeis_a039824_R1_H1_R1
