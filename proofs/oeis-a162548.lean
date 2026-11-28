import OMAStatements.S_oeis_a162548
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The six-lag Chebyshev–Schröder recurrence, OEIS A162548

Source: https://oeis.org/A162548. Paul Barry gives the transform and its
generating function. R. J. Mathar proposed the recurrence in 2012 and Fung
Lam recorded verification in 2014. Credit: @jiyongparkphysics

The Narayana numerator is a coefficient of ((1+X)(1+2X))^m. A polynomial
derivative certifies its divisibility by m, justifying the natural-number
quotient. A second derivative identity yields the small Schröder recurrence.
The last step applies the resulting linear functional to a polynomial identity
for the Chebyshev transform, proving the requested recurrence from the sum.
-/
namespace OMA.S_oeis_a162548
open Finset Polynomial

private theorem linear_coeff (a : ℤ) (m i : ℕ) :
    ((1 + C a * X : ℤ[X])^m).coeff i = (m.choose i : ℤ)*a^i := by
  induction m generalizing i with
  | zero => cases i <;> simp [coeff_one]
  | succ m ih =>
    rw [pow_succ,mul_add,mul_one,← mul_assoc,coeff_add]
    cases i with
    | zero => rw [coeff_mul_X_zero,add_zero,ih]; simp
    | succ i =>
      rw [coeff_mul_X,coeff_mul_C,ih,ih,Nat.choose_succ_succ,Nat.cast_add,pow_succ]
      ring

private noncomputable def G : ℤ[X] := (1+X)*(1+2*X)
private def numerator (m : ℕ) := ∑ k ∈ Icc 1 m, m.choose k * m.choose (k-1) * 2^(k-1)

private theorem numerator_coeff (t : ℕ) :
    (numerator (t+1) : ℤ) = (G^(t+1)).coeff t := by
  have hi : Icc 1 (t+1) = Ico 1 (t+2) := by ext i; simp; omega
  have hg : G = (1+C (2:ℤ)*X)*(1+C (1:ℤ)*X) := by simp [G,mul_comm]
  rw [numerator,hi,sum_Ico_eq_sum_range,hg,mul_pow,coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  push_cast
  try simp only [show t+2-1=t+1 by omega]
  apply sum_congr rfl
  intro i hi
  have leq : i ≤ t := by simpa using hi
  simp only [linear_coeff,one_pow,mul_one]
  rw [show t-i=(t+1)-(i+1) by omega,Nat.choose_symm (by omega : i+1 ≤ t+1)]
  simp [add_comm 1 i]
  ring

private theorem coeff_euler (P : ℤ[X]) (i : ℕ) :
    (X*P.derivative).coeff i = (i:ℤ)*P.coeff i := by
  cases i with
  | zero => simp
  | succ i => rw [coeff_X_mul,coeff_derivative]; push_cast; ring

private theorem int_dvd_coeff (P : ℤ[X]) (t : ℕ) :
    (↑(t+1) : ℤ) ∣ (P^(t+1)).coeff t := by
  refine ⟨(P^t*(P-X*P.derivative)).coeff t, ?_⟩
  have h := coeff_euler (P^(t+1)) t
  rw [derivative_pow_succ] at h
  have hp : X * (C ((t:ℤ)+1)*P^t*P.derivative) = C ((t:ℤ)+1) * (P^t*(X*P.derivative)) := by ring
  rw [hp,coeff_C_mul] at h
  rw [mul_sub,coeff_sub,←pow_succ]
  push_cast
  linear_combination h

theorem narayana_coeff (m : ℕ) (hm : 1 ≤ m) :
    (s m : ℤ)*m = (((1+X)*(1+2*X) : ℤ[X])^m).coeff (m-1) := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hx := numerator_coeff t
  have hi := int_dvd_coeff G t
  rw [←hx] at hi
  have hd : t+1 ∣ numerator (t+1) := by exact_mod_cast hi
  have e : s (t+1)*(t+1) = numerator (t+1) := by
    change (if t+1=0 then 1 else numerator (t+1)/(t+1))*(t+1) = _
    simp [Nat.div_mul_cancel hd]
  change (s (t+1) : ℤ)*((t+1:ℕ):ℤ) = (G^(t+1)).coeff t
  rw [←hx,← Nat.cast_mul,e]

end OMA.S_oeis_a162548

namespace SchroderCoefficient

open Polynomial

noncomputable def G : ℤ[X] := (1+X)*(1+2*X)

private noncomputable def cert (m : ℕ) : ℤ[X] :=
  -C ((m:ℤ)+3) - 3*X + 2*C ((m:ℤ)+1)*X^2

/-- A coefficient of an Euler derivative of degree d, minus d times that coefficient, vanishes. -/
private lemma vanish (f : ℤ[X]) (d : ℕ) :
    (X*f.derivative - C (d:ℤ)*f).coeff d = 0 := by
  cases d with
  | zero => simp
  | succ d =>
    rw [coeff_sub,coeff_X_mul,coeff_derivative,coeff_C_mul]
    push_cast
    ring

private lemma cert_identity (m : ℕ) :
    C (((m:ℤ)+3)*(m+1)) * G^(m+2) -
    C ((6*(m:ℤ)+9)*(m+2)) * G^(m+1)*X +
    C (((m:ℤ)+1)*(m+2))*G^m*X^2 =
    X*(G^(m+1)*cert m).derivative - C ((m:ℤ)+1)*(G^(m+1)*cert m) := by
  rw [derivative_mul, derivative_pow_succ]
  simp only [cert, G, derivative_sub, derivative_neg, derivative_mul,
    derivative_X, derivative_one, derivative_ofNat, derivative_pow,
    map_mul, map_add, map_ofNat, map_one, map_natCast]
  rw [pow_succ _ (m+1), pow_succ _ m]
  push_cast
  simp only [derivative_natCast]
  ring

/-- The consecutive coefficient recurrence for the little Schröder numbers. -/
theorem recurrence (s : ℕ → ℤ)
    (h : ∀ k : ℕ, ((k:ℤ)+1)*s (k+1) = (G^(k+1)).coeff k) (m : ℕ) :
    ((m:ℤ)+3)*s (m+2) - (6*(m:ℤ)+9)*s (m+1) + m*s m = 0 := by
  cases m with
  | zero =>
    have h0 := h 0
    have h1 := h 1
    have square : G^2 = 1 + C (6:ℤ)*X^1 + C (13:ℤ)*X^2 +
        C (12:ℤ)*X^3+C (4:ℤ)*X^4 := by norm_num [G]; ring
    rw [show 1+1=2 by decide, square] at h1
    norm_num [G,coeff_add,coeff_X,coeff_one,coeff_C_mul_X_pow,coeff_mul_X] at h0 h1 ⊢
    omega
  | succ k =>
    let m := k+1
    have hh := vanish (G^(m+1)*cert m) (m+1)
    rw [Nat.cast_add,Nat.cast_one,← cert_identity] at hh
    change (_ : ℤ[X]).coeff (k+2) = 0 at hh
    simp only [coeff_add,coeff_sub,coeff_mul_X,coeff_mul_X_pow,coeff_C_mul] at hh
    rw [← h (k+2), ← h (k+1), ← h k] at hh
    dsimp [m] at hh
    push_cast at hh ⊢
    have pos : (0:ℤ) < ((k:ℤ)+2)*((k:ℤ)+3) := by positivity
    apply (mul_eq_zero.mp (show (((k:ℤ)+2)*((k:ℤ)+3)) * _ = 0 by
      linear_combination hh)).resolve_left (ne_of_gt pos)

end SchroderCoefficient

namespace OMA.Cheb162548

open Polynomial Finset

noncomputable def term (n k : ℕ) : ℤ[X] :=
  C (((-1 : ℤ)^k) * ((n-k).choose k : ℤ)) * X^(n-2*k)

noncomputable def p (n : ℕ) : ℤ[X] := ∑ k ∈ range (n+1), term n k

private lemma beyond (n k : ℕ) (h : n < 2*k) : term n k = 0 := by
  have h' : n-k < k := by omega
  simp [term, Nat.choose_eq_zero_of_lt h']

private lemma pascal (n k : ℕ) :
    term (n+2) (k+1) = X * term (n+1) (k+1) - term n k := by
  by_cases h : 2*k ≤ n
  · rw [term, term, term]
    rw [show n+2-(k+1) = (n-k)+1 by omega, Nat.choose_succ_succ,
      show n+1-(k+1) = n-k by omega, show n+2-2*(k+1) = n-2*k by omega]
    by_cases h' : 2*k < n
    · have hx : (X:ℤ[X]) ^ (n-2*k) = X * X^(n+1-2*(k+1)) := by
        rw [← pow_succ']; congr 1; omega
      rw [hx]
      simp only [Nat.cast_add, map_mul, map_add, pow_succ, map_pow, map_neg, map_one]
      ring
    · have hz : (n-k).choose (k+1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp only [hz, Nat.cast_zero, add_zero, mul_zero, map_zero, zero_mul,
        zero_sub, pow_succ, map_mul, map_neg, map_one]
      ring
  · rw [beyond _ _ (by omega), beyond _ _ (by omega), beyond _ _ (by omega)]
    ring

lemma p_step (n : ℕ) : p (n+2) = X*p (n+1) - p n := by
  have hpad (i : ℕ) : ∑ k ∈ range (i+2), term i k = p i := by
    rw [sum_range_succ, beyond _ _ (by omega), add_zero, p]
  rw [← hpad n, ← hpad (n+1), p, sum_range_succ' (f:=term (n+2)),
    sum_range_succ' (f:=term (n+1))]
  simp_rw [pascal]
  rw [sum_sub_distrib, ← mul_sum]
  have h0 (i : ℕ) : term i 0 = X^i := by simp [term]
  rw [h0,h0,pow_succ' (n:=n+1)]
  ring

private noncomputable def op (f : ℤ[X]) : ℤ[X] :=
  (X^3-6*X^2+X)*f.derivative + (3*X^2-9*X)*f

private noncomputable def cert (m : ℕ) : ℤ[X] :=
  ((m:ℤ[X])+7)*p (m+6)+3*(-2*(m:ℤ[X])-11)*p (m+5)+(4*(m:ℤ[X])+19)*p (m+4)
  +12*(-(m:ℤ[X])-4)*p (m+3)+(4*(m:ℤ[X])+13)*p (m+2)
  +3*(-2*(m:ℤ[X])-5)*p (m+1)+((m:ℤ[X])+1)*p m - op (p (m+4)) + op (p (m+2))

private lemma cert_zero (m : ℕ) : cert m = 0 := by
  induction m using Nat.twoStepInduction with
  | zero =>
    norm_num [cert, p, term, op, sum_range_succ, Nat.choose, derivative_add, derivative_mul]
    ring
  | one =>
    norm_num [cert, p, term, op, sum_range_succ, Nat.choose, derivative_add, derivative_mul]
    ring
  | more m h0 h1 =>
    have relation : cert (m+2) = X*cert (m+1) - cert m := by
      simp only [cert, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Nat.add_assoc, Nat.reduceAdd]
      simp only [show p (m+8) = X*p (m+7)-p (m+6) from p_step (m+6),
        show p (m+7) = X*p (m+6)-p (m+5) from p_step (m+5),
        show p (m+6) = X*p (m+5)-p (m+4) from p_step (m+4),
        show p (m+5) = X*p (m+4)-p (m+3) from p_step (m+3),
        show p (m+4) = X*p (m+3)-p (m+2) from p_step (m+2),
        show p (m+3) = X*p (m+2)-p (m+1) from p_step (m+1),
        p_step m, op, derivative_sub, derivative_mul, derivative_X]
      ring
    simp [relation,h0,h1]

noncomputable def moment (s : ℕ → ℤ) : ℤ[X] →ₗ[ℤ] ℤ :=
  Polynomial.lsum fun j => s j • LinearMap.id

private lemma monom (s : ℕ → ℤ) (j : ℕ) (r : ℤ) :
    moment s (C r*X^j) = r*s j := by
  rw [C_mul_X_pow_eq_monomial]
  simp [moment, lsum_apply, sum_monomial_index, mul_comm]

def transform (s : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ range (n/2+1), (-1:ℤ)^k * ((n-k).choose k : ℤ) * s (n-2*k)

private lemma as_moment (s : ℕ → ℤ) (n : ℕ) : transform s n = moment s (p n) := by
  rw [p,map_sum,transform]
  rw [← sum_subset (s₁ := range (n/2+1)) (s₂ := range (n+1)) (by
    apply range_mono; omega)]
  · apply sum_congr rfl
    intro k _
    exact (monom s _ _).symm
  · intro k _ hk
    simp only [mem_range,not_lt] at hk
    rw [beyond _ _ (by omega), map_zero]

private lemma annihilate (s : ℕ → ℤ) (hs : ∀ k : ℕ,
    ((k:ℤ)+3)*s (k+2) - (6*(k:ℤ)+9)*s (k+1) + (k:ℤ)*s k = 0) (f : ℤ[X]) :
    moment s (op f) = 0 := by
  induction f using Polynomial.induction_on' with
  | add u v hu hv =>
    have h : op (u+v) = op u + op v := by simp only [op,derivative_add]; ring
    rw [h,map_add,hu,hv,add_zero]
  | monomial k r =>
    rw [← C_mul_X_pow_eq_monomial]
    have hd : X*derivative (C r*X^k) = C (r*(k:ℤ))*X^k := by
      cases k with
      | zero => simp
      | succ k =>
        rw [derivative_C_mul_X_pow, Nat.succ_sub_one, pow_succ]
        ring
    have he : op (C r*X^k) =
        C (r*((k:ℤ)+3))*X^(k+2) - C (r*(6*(k:ℤ)+9))*X^(k+1) + C (r*(k:ℤ))*X^k := by
      unfold op
      rw [show X^3-6*X^2+(X:ℤ[X]) = (X^2-6*X+1)*X by ring, mul_assoc, hd]
      simp only [map_mul, map_add, map_ofNat, pow_succ]
      ring
    rw [he,map_add,map_sub,monom,monom,monom]
    linear_combination r * hs k

theorem chebRecurrence (s : ℕ → ℤ) (hs : ∀ k : ℕ,
    ((k:ℤ)+3)*s (k+2) - (6*(k:ℤ)+9)*s (k+1) + (k:ℤ)*s k = 0) :
    ∀ n : ℕ, 6 ≤ n →
    ((n:ℤ)+1)*transform s n + 3*(-2*(n:ℤ)+1)*transform s (n-1)
    +(4*(n:ℤ)-5)*transform s (n-2)+12*(-(n:ℤ)+2)*transform s (n-3)
    +(4*(n:ℤ)-11)*transform s (n-4)+3*(-2*(n:ℤ)+7)*transform s (n-5)
    +((n:ℤ)-5)*transform s (n-6) = 0 := by
  intro n hn
  obtain ⟨m,rfl⟩ : ∃ m, n = m+6 := ⟨n-6,by omega⟩
  have h : ((m:ℤ)+7) • p (m+6)+(3*(-2*(m:ℤ)-11)) • p (m+5)+
      (4*(m:ℤ)+19) • p (m+4)+(12*(-(m:ℤ)-4)) • p (m+3)+
      (4*(m:ℤ)+13) • p (m+2)+(3*(-2*(m:ℤ)-5)) • p (m+1)+
      ((m:ℤ)+1) • p m - op (p (m+4)) + op (p (m+2)) = 0 := by
    simpa only [smul_eq_C_mul,map_add,map_mul,map_sub,map_neg,map_natCast,map_ofNat,map_one,cert]
      using cert_zero m
  have h' := congrArg (fun u => moment s u) h
  simp only [map_add,map_sub,map_smul,map_zero,annihilate s hs,smul_eq_mul,sub_zero,add_zero] at h'
  simp only [as_moment, Nat.cast_add, Nat.cast_ofNat]
  simp only [show m+6-1=m+5 by omega, show m+6-2=m+4 by omega, show m+6-3=m+3 by omega,
    show m+6-4=m+2 by omega, show m+6-5=m+1 by omega, show m+6-6=m by omega]
  linear_combination h'

end OMA.Cheb162548

open OMA.S_oeis_a162548 in
theorem OMA.solution : type_of% @OMA.S_oeis_a162548.main := by
  let v (m : ℕ) : ℤ := s m
  have coeffs (k : ℕ) :
      ((k:ℤ)+1)*v (k+1) = (SchroderCoefficient.G^(k+1)).coeff k := by
    calc
      _ = (s (k+1) : ℤ)*((k+1 : ℕ):ℤ) := by dsimp [v]; ring
      _ = _ := by simpa [SchroderCoefficient.G] using narayana_coeff (k+1) (by omega)
  exact OMA.Cheb162548.chebRecurrence v (SchroderCoefficient.recurrence v coeffs)
