import OMAStatements.S_mo_335694
import Mathlib

/-! The final two derivative orders force an affine first-order relation. Its
highest coefficient, first for f and then for its difference from a shifted
power, gives the classification. -/
open Polynomial
namespace PolynomialRemainders
variable {K : Type*} [Field K] [CharZero K]
noncomputable section

def op (a b z : K) (f : K[X]) : K[X] :=
  C b * ((X - C a) * derivative f) - C z * f

lemma top_coeff (a b z : K) (f : K[X]) :
    (op a b z f).coeff f.natDegree = (b * (f.natDegree:K) - z) * f.leadingCoeff := by
  have h : (X * derivative f).coeff f.natDegree = f.leadingCoeff * (f.natDegree:K) := by
    generalize hn : f.natDegree = n
    cases n with
    | zero => simp
    | succ n => rw [coeff_X_mul,coeff_derivative,← hn,coeff_natDegree]; simp [hn]
  have hd : (derivative f).coeff f.natDegree = 0 := by
    rw [coeff_derivative,coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _),zero_mul]
  simp only [op,sub_mul,coeff_sub,coeff_C_mul,h,hd,coeff_natDegree]
  ring

lemma high_root {a b z : K} {f : K[X]} {m : ℕ} (hm : 0 < m) (hf : m ≤ f.natDegree)
    (hr : (op a b z f).natDegree < m) : b*(f.natDegree:K) = z := by
  have h := coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hr hf)
  rw [top_coeff] at h
  apply sub_eq_zero.mp
  exact (mul_eq_zero.mp h).resolve_right (leadingCoeff_ne_zero.mpr (by
    intro he; simp [he] at hf; omega))

lemma power_op (a b c : K) (d : ℕ) :
    op a b (b*d) (C c * (X-C a)^d) = 0 := by
  cases d with
  | zero => simp [op]
  | succ d =>
    rw [op,derivative_mul,derivative_C,zero_mul,zero_add,derivative_pow_succ]
    simp only [derivative_C,
      derivative_sub,derivative_X,sub_zero,mul_one,Nat.cast_succ,map_mul,pow_succ]
    ring

lemma monomial_shape {a b z : K} {f : K[X]} {m : ℕ}
    (hm : 0 < m) (hd : m ≤ f.natDegree) (hb : b≠0) (hr : (op a b z f).natDegree < m) :
    ∃ (c:K) (r:K[X]), c≠0 ∧ r.natDegree < m ∧ f = C c * (X-C a)^f.natDegree+r := by
  have fn : f ≠ 0 := by intro h; simp [h] at hd; omega
  have hz := high_root hm hd hr
  subst z
  let g := C f.leadingCoeff * (X-C a)^f.natDegree
  let r := f-g
  have lc := leadingCoeff_ne_zero.mpr fn
  have dg : g.natDegree = f.natDegree := by simp [g, natDegree_C_mul lc, natDegree_pow]
  have cg : g.leadingCoeff = f.leadingCoeff := by simp [g,leadingCoeff_mul,leadingCoeff_pow]
  have dr : r.natDegree < f.natDegree := by
    have bound : r.natDegree ≤ f.natDegree := (natDegree_sub_le _ _).trans (by simp [dg])
    apply lt_of_le_of_ne bound
    intro eqd
    have rz : r ≠ 0 := by intro h; simp [h] at eqd; omega
    apply (leadingCoeff_ne_zero.mpr rz)
    rw [← coeff_natDegree,eqd]
    change (f-g).coeff f.natDegree = 0
    rw [coeff_sub,coeff_natDegree,← dg,coeff_natDegree,cg,sub_self]
  have oper : op a b (b*f.natDegree) r = op a b (b*f.natDegree) f := by
    have zero := power_op a b f.leadingCoeff f.natDegree
    change op a b (b*f.natDegree) g = 0 at zero
    calc
      _ = op a b (b*f.natDegree) f - op a b (b*f.natDegree) g := by
        simp only [r,op,map_sub]; ring
      _ = _ := by rw [zero,sub_zero]
  refine ⟨_,r,lc,?_,by simp [r,g]⟩
  by_contra! bad
  have same := high_root hm bad (oper ▸ hr)
  have hn : (r.natDegree:K) = (f.natDegree:K) := mul_left_cancel₀ hb same
  exact dr.ne (by exact_mod_cast hn)

end
end PolynomialRemainders

open Polynomial
namespace PolynomialRemainders
variable {K : Type*} [Field K] [CharZero K]
noncomputable section

lemma iter_degree (g : K[X]) (k : ℕ) : (derivative^[k] g).natDegree = g.natDegree-k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply',natDegree_derivative,ih]; omega

lemma quotient_degree {D f P R : K[X]} {m : ℕ} (fn : f ≠ 0) (fd : m ≤ f.natDegree)
    (dd : m ≤ D.natDegree) (eqn : D = P*f+R) (hr : R.natDegree < m) :
    D.natDegree = P.natDegree + f.natDegree := by
  have pn : P ≠ 0 := by
    intro h
    simp [h] at eqn
    rw [eqn] at dd
    omega
  rw [eqn,natDegree_add_eq_left_of_natDegree_lt, natDegree_mul pn fn]
  rw [natDegree_mul pn fn]; omega

lemma extract {f Q : K[X]} {m : ℕ} (hm : 0 < m) (fd : m ≤ f.natDegree)
    (hq : 0 < Q.natDegree) (hyp : ∀ k : ℕ, 1 ≤ k → k ≤ Q.natDegree →
      ∃ P R : K[X], (derivative^[k]) (Q*f) = P*f+R ∧ R.natDegree < m) :
    ∃ a b z : K, b ≠ 0 ∧ (C b * ((X-C a) * derivative f) - C z * f).natDegree < m := by
  have fn : f ≠ 0 := by intro h; simp [h] at fd; omega
  have qn : Q ≠ 0 := by intro h; simp [h] at hq
  obtain ⟨s,hs⟩ : ∃ s, Q.natDegree = s+1 := ⟨Q.natDegree-1,by omega⟩
  have ds (t : ℕ) : (derivative^[t] (Q*f)).natDegree = s+1+f.natDegree-t := by
    rw [iter_degree,natDegree_mul qn fn,hs]
  obtain ⟨P,R,e,r⟩ : ∃ P R : K[X], (derivative^[s]) (Q*f) = P*f+R ∧ R.natDegree < m := by
    by_cases sz : s=0
    · subst s; exact ⟨Q,0,by simp,by simpa using hm⟩
    · exact hyp s (by omega) (by omega)
  obtain ⟨P',R',e',r'⟩ := hyp (s+1) (by omega) hs.ge
  have dP := quotient_degree fn fd (D:=derivative^[s] (Q*f)) (by rw [ds]; omega) e r
  have dP' := quotient_degree fn fd (D:=derivative^[s+1] (Q*f)) (by rw [ds]; omega) e' r'
  rw [ds] at dP dP'
  have pd : P.natDegree = 1 := by omega
  have pd' : P'.natDegree = 0 := by omega
  obtain ⟨b,v,pform⟩ := exists_eq_X_add_C_of_natDegree_le_one pd.le
  have hn : b ≠ 0 := by intro h; simp [pform,h] at pd
  let a := -v/b
  have bv : C b * C a = -(C v : K[X]) := by
    rw [← map_mul,← map_neg]
    congr 1
    dsimp [a]; field_simp
  have pf : P = C b * (X - C a) := by rw [mul_sub,bv,sub_neg_eq_add,pform]
  have dp : derivative P = C b := by simp [pform,derivative_mul]
  have E := congrArg (fun p : K[X] => derivative p) e
  change derivative (derivative^[s] (Q*f)) = derivative (P*f+R) at E
  rw [Function.iterate_succ_apply'] at e'
  rw [e',map_add,derivative_mul,dp,pf,
    eq_C_of_natDegree_eq_zero pd'] at E
  refine ⟨a,b,P'.coeff 0 - b,hn,?_⟩
  have iden : C b * ((X-C a) * derivative f) - C (P'.coeff 0-b)*f = R'-derivative R := by
    rw [map_sub]; linear_combination -E
  rw [iden]
  apply lt_of_le_of_lt (natDegree_sub_le _ _)
  exact max_lt r' ((natDegree_derivative_le _).trans_lt (by omega))

end
end PolynomialRemainders

open Polynomial
namespace PolynomialRemainders
variable {K : Type*} [Field K] [CharZero K]
noncomputable section

lemma converse {f r : K[X]} {m : ℕ} (a c : K) (d : ℕ) (hm : 2 ≤ m)
    (hr : r.natDegree < m) (hf : f = C c * (X-C a)^d + r) :
    ∃ Q : K[X], 0 < Q.natDegree ∧ ∀ k : ℕ, 1 ≤ k → k ≤ Q.natDegree →
      ∃ P R : K[X], (derivative^[k]) (Q*f) = P*f+R ∧ R.natDegree < m := by
  refine ⟨X-C a,by simp,?_⟩
  intro k hk hQ
  rw [natDegree_X_sub_C] at hQ
  obtain rfl : k = 1 := by omega
  refine ⟨1+C (d:K),op a 1 d r,?_,?_⟩
  · have h := power_op a (1:K) c d
    simp only [op,one_mul,map_one] at h
    rw [Function.iterate_one,derivative_mul,derivative_sub,derivative_X,derivative_C,sub_zero,one_mul,hf]
    simp only [map_add,op,map_one,one_mul]
    linear_combination h
  · simp only [op,map_one,one_mul]
    apply lt_of_le_of_lt (natDegree_sub_le _ _)
    apply max_lt _ ((natDegree_C_mul_le _ _).trans_lt hr)
    apply lt_of_le_of_lt natDegree_mul_le
    rw [natDegree_X_sub_C,natDegree_derivative]
    omega

lemma result (f : K[X]) (m : ℕ) (hm : 2 ≤ m) (hd : 2*m ≤ f.natDegree) :
    ((∃ Q : K[X], 0 < Q.natDegree ∧ ∀ k : ℕ, 1 ≤ k → k ≤ Q.natDegree →
      ∃ P R : K[X], (derivative^[k]) (Q*f) = P*f+R ∧ R.natDegree < m) ↔
    ∃ (a c : K) (r : K[X]), c ≠ 0 ∧ r.natDegree < m ∧
      f = C c * (X-C a)^f.natDegree + r) := by
  constructor
  · rintro ⟨Q,hq,h⟩
    obtain ⟨a,b,z,hb,hr⟩ := extract (by omega) (by omega) hq h
    exact ⟨a,monomial_shape (a:=a) (b:=b) (z:=z) (f:=f) (by omega) (by omega) hb hr⟩
  · rintro ⟨a,c,r,_,hr,hf⟩
    exact converse a c _ hm hr hf

end
end PolynomialRemainders

open Polynomial
namespace PolynomialRemainders
variable {K : Type*} [Field K] [CharZero K]
noncomputable section

/-- If only the first B derivatives are tested, every polynomial works with Q=f^B. -/
lemma fixed_orders (f : K[X]) (B k : ℕ) (hk : k ≤ B) :
    f ∣ derivative^[k] (f^B * f) := by
  rw [← pow_succ]
  apply dvd_trans _ (pow_sub_dvd_iterate_derivative_pow f (B+1) k)
  simpa using pow_dvd_pow f (show 1 ≤ B+1-k by omega)

/-- For quadratic g, Q=g^t has degree 2t and the first t derivatives are exact multiples
of f=g^u. This gives examples for the half-degree relaxation. -/
lemma half_orders (g : K[X]) (u t k : ℕ) (dg : g.natDegree = 2)
    (hk : 2*k ≤ (g^t).natDegree) :
    g^u ∣ derivative^[k] (g^t * g^u) := by
  rw [natDegree_pow,dg] at hk
  rw [← pow_add]
  exact (pow_dvd_pow g (show u ≤ t+u-k by omega)).trans
    (pow_sub_dvd_iterate_derivative_pow g (t+u) k)

/-- The quartic (X²−1)² cannot equal a translated fourth power plus a polynomial
of degree below two. -/
lemma quartic_example : ¬ ∃ (a c : ℚ) (r : ℚ[X]), r.natDegree < 2 ∧
    (X^2-1 : ℚ[X])^2 = C c*(X-C a)^4 + r := by
  rintro ⟨a,c,r,hr,h⟩
  have left : (X^2-1 : ℚ[X])^2 = X^4 - C 2*X^2 + 1 := by simp only [map_ofNat]; ring
  have right : C c*(X-C a)^4 =
      C c*X^4 + C (-4*c*a)*X^3 + C (6*c*a^2)*X^2 + C (-4*c*a^3)*X + C (c*a^4) := by
    simp only [map_neg,map_mul,map_pow,map_ofNat]
    ring
  rw [left,right] at h
  have H (i : ℕ) (hi : 2 ≤ i) := congrArg (fun p : ℚ[X] => p.coeff i) h
  have h₄ := H 4 (by decide)
  have h₃ := H 3 (by decide)
  have h₂ := H 2 (by decide)
  simp (disch := omega) only [coeff_sub,coeff_add,coeff_C_mul,coeff_X_pow,coeff_one,coeff_C,
    coeff_X,coeff_eq_zero_of_natDegree_lt (show r.natDegree < 4 by omega),
    coeff_eq_zero_of_natDegree_lt (show r.natDegree < 3 by omega), coeff_eq_zero_of_natDegree_lt hr] at h₄ h₃ h₂
  norm_num at h₄ h₃ h₂
  subst c
  have : a = 0 := h₃.resolve_left (by norm_num)
  subst a
  norm_num at h₂

end
end PolynomialRemainders

theorem OMA.solution : type_of% @OMA.S_mo_335694.main := @PolynomialRemainders.result
