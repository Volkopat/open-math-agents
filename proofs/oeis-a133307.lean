import OMAStatements.S_oeis_a133307
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
The Narayana sum is seven times a coefficient of a power of
1+13X+42X². Two Euler derivative identities express the neighboring
coefficients and give a recurrence for the central ones. Eliminating
those central coefficients gives the desired recurrence.
-/

namespace OMA.S_oeis_a133307

open Finset Polynomial

private abbrev R := ℚ[X]

private noncomputable def P : R := 1+13*Polynomial.X+42*Polynomial.X^2

private noncomputable def J (u : ℚ) : R := Polynomial.C u*Polynomial.X+1

private theorem j_coeff (u : ℚ) (n k : ℕ) :
    (J u^n).coeff k=u^k*(n.choose k : ℚ) := by
  induction n generalizing k with
  | zero => cases k <;> simp [Polynomial.coeff_one]
  | succ n ih =>
    rw [pow_succ' (J u),show J u*J u^n = Polynomial.C u*Polynomial.X*J u^n+J u^n by
      nth_rw 1 [J]
      rw [add_mul,one_mul],coeff_add,mul_assoc,coeff_C_mul]
    cases k with
    | zero => simp [coeff_X_mul_zero,ih]
    | succ k =>
      rw [coeff_X_mul,ih,ih,Nat.choose_succ_succ,pow_succ]
      push_cast
      ring

private theorem a_coeff (n : ℕ) (hn : 1≤n) :
    (n:ℚ)*a n=7*(P^n).coeff (n-1) := by
  have hp : P=J 6*J 7 := by
    unfold P J
    simp only [map_ofNat]
    ring
  rw [a,if_neg (by omega),show (n:ℚ) *
    ((∑ i ∈ range n, (n.choose i:ℚ)*(n.choose (i+1):ℚ)*6^i*7^(n-i))/(n:ℚ)) =
      ∑ i ∈ range n, (n.choose i:ℚ)*(n.choose (i+1):ℚ)*6^i*7^(n-i) by
        have hn' : (n:ℚ)≠0 := by exact_mod_cast (show n≠0 by omega)
        field_simp, hp,mul_pow,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (J 6^n).coeff i*(J 7^n).coeff j),
    show (n-1).succ=n by omega,mul_sum]
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  have hb : n-1-i≤n := by omega
  simp only [j_coeff]
  rw [←Nat.choose_symm hb,show n-(n-1-i)=i+1 by omega,
    show n-i=(n-1-i)+1 by omega,pow_succ (7:ℚ)]
  ring

private noncomputable def b (n : ℕ) : ℚ := (P^n).coeff n

private theorem euler_zero (f : R) (k : ℕ) :
    (Polynomial.X*derivative f-Polynomial.C (k:ℚ)*f).coeff k=0 := by
  cases k with
  | zero => simp [coeff_X_mul_zero]
  | succ k =>
    rw [coeff_sub,coeff_X_mul,coeff_derivative,coeff_C_mul]
    push_cast
    ring

private theorem central_rec (m : ℕ) :
    ((m:ℚ)+2)*b (m+2)=13*(2*(m:ℚ)+3)*b (m+1)-((m:ℚ)+1)*b m := by
  let H : R := 42*Polynomial.X^2-1
  let g := H*P^(m+1)
  have h :
      Polynomial.X*derivative g-Polynomial.C ((m:ℚ)+2)*g =
        Polynomial.C ((m:ℚ)+2)*P^(m+2) -
          Polynomial.C (13*(2*(m:ℚ)+3))*(Polynomial.X*P^(m+1)) +
          Polynomial.C ((m:ℚ)+1)*(Polynomial.X^2*P^m) := by
    unfold g
    rw [derivative_mul,derivative_pow_succ,pow_add P m 2,pow_add P m 1]
    simp only [P,H,derivative_mul,derivative_pow,derivative_one,derivative_ofNat,
      derivative_X,map_add,map_mul,map_sub,map_one,map_ofNat,Nat.cast_ofNat]
    ring
  have h0 := euler_zero g (m+2)
  rw [show ((m+2:ℕ):ℚ)=(m:ℚ)+2 by push_cast; rfl,h] at h0
  simp only [coeff_add,coeff_sub,coeff_C_mul,coeff_X_mul,coeff_X_pow_mul,b] at h0
  unfold b
  linear_combination h0

private theorem neighbor_coeff (m : ℕ) :
    (P^(m+1)).coeff (m+2)=42*(P^(m+1)).coeff m := by
  have h := euler_zero (P^(m+2)) (m+2)
  have he :
      Polynomial.X*derivative (P^(m+2))-Polynomial.C ((m+2:ℕ):ℚ)*P^(m+2) =
        Polynomial.C ((m+2:ℕ):ℚ)*
          (Polynomial.C 42*(Polynomial.X^2*P^(m+1))-P^(m+1)) := by
    rw [show m+2=(m+1)+1 by omega,derivative_pow_succ,pow_succ P (m+1)]
    simp only [P,derivative_mul,derivative_pow,derivative_one,derivative_ofNat,map_add,
      map_sub,map_mul,map_ofNat,map_one,map_natCast,derivative_X,Nat.cast_one,Nat.cast_add]
    ring
  rw [he,coeff_C_mul,coeff_sub,coeff_C_mul,coeff_X_pow_mul] at h
  have hh : ((m+2:ℕ):ℚ)≠0 := by positivity
  have hz := (mul_eq_zero.mp h).resolve_left hh
  linear_combination -hz

private theorem related (m : ℕ) :
    b (m+2)-13*b (m+1)=12*((m:ℚ)+1)*a (m+1) := by
  have h := a_coeff (m+1) (by omega)
  rw [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at h
  have he : b (m+2) = (P^(m+1)).coeff (m+2) +
      13*(P^(m+1)).coeff (m+1)+42*(P^(m+1)).coeff m := by
    unfold b
    rw [show P^(m+2)=P*P^(m+1) by rw [pow_succ'],show P*P^(m+1)=
      P^(m+1)+Polynomial.C 13*(Polynomial.X*P^(m+1))+
        Polynomial.C 42*(Polynomial.X^2*P^(m+1)) by unfold P; simp only [map_ofNat]; ring]
    simp only [coeff_add,coeff_C_mul,coeff_X_mul,coeff_X_pow_mul]
  rw [neighbor_coeff] at he
  unfold b at *
  linear_combination he - 12*h

private theorem recur (m : ℕ) :
    ((m:ℚ)+4)*a (m+3) + 13*(-2*(m:ℚ)-5)*a (m+2) + ((m:ℚ)+1)*a (m+1)=0 := by
  have hr0 := central_rec (m+1)
  have hr1 := central_rec (m+2)
  have hs0 := related m
  have hs1 := related (m+1)
  have hs2 := related (m+2)
  have hn : 12*((m:ℚ)+2)*((m:ℚ)+3) ≠ 0 := by positivity
  simp only [Nat.add_assoc,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at *
  apply mul_left_cancel₀ hn
  linear_combination ((m:ℚ)+2)*hr1-13*((m:ℚ)+3)*hr0 -
    ((m:ℚ)+2)*((m:ℚ)+4)*hs2+13*(2*(m:ℚ)+5)*((m:ℚ)+3)*hs1 -
    ((m:ℚ)+2)*((m:ℚ)+3)*hs0

end OMA.S_oeis_a133307

open OMA.S_oeis_a133307 in
theorem OMA.solution : type_of% @OMA.S_oeis_a133307.main := by
  intro n hn
  by_cases h : n=2
  · subst n
    decide +kernel
  · let m := n-3
    have hm : n=m+3 := by omega
    rw [hm,show m+3-1=m+2 by omega,show m+3-2=m+1 by omega,Nat.cast_add,Nat.cast_ofNat]
    linear_combination recur m
