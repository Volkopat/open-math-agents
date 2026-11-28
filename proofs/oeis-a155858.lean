import OMAStatements.S_oeis_a155858
import Mathlib
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

/-!
# A factorial-binomial recurrence

This proves R. J. Mathar's 2015 recurrence for Paul Barry's OEIS A155858
(https://oeis.org/A155858). Reindex n=j+2k. The contribution for fixed j
has ordinary series j! X^j/(1-X^2)^(2j+1). The proof verifies the resulting
series composition and a first-order differential equation, using only finite
truncations in each coefficient. Coefficient extraction gives both a
sixth-order recurrence and the conjectured seventh-order recurrence.

The sixth-order recurrence also appears as executable data in loader3229's
LODA program for A155858. A second derivation proves a pointwise identity of
the padded binomial summands directly from Pascal's rule.
-/

namespace Fact155
open Finset PowerSeries

/-- The even geometric series has constant term one and inverts `1-X^2`. -/
theorem even_geometric_inverse :
    expand 2 (by decide) (mk 1 : PowerSeries ℚ) * (1-X^2) = 1 := by
  simpa using congrArg (expand 2 (by decide) : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ)
    (mk_one_mul_one_sub_eq_one (S := ℚ))

theorem coeff_even_inv_pow (h : PowerSeries ℚ) (hh : h*(1-X^2)=1) (e s : ℕ) :
    coeff s (h^(e+1)) = if 2 ∣ s then ((e+s/2).choose (s/2) : ℚ) else 0 := by
  have H : h = expand 2 (by decide) (mk 1 : PowerSeries ℚ) :=
    left_inv_eq_right_inv hh ((mul_comm _ _).trans even_geometric_inverse)
  rw [H, ← map_pow, mk_one_pow_eq_mk_choose_add, coeff_expand]
  simp only [coeff_mk, Nat.choose_symm_add (a:=e)]

theorem coeff_fact_term (h : PowerSeries ℚ) (hh : h*(1-X^2)=1) (j n : ℕ) :
    coeff n (C (j.factorial : ℚ)*X^j*h^(2*j+1)) =
    if j ≤ n ∧ 2 ∣ n-j then (j.factorial : ℚ)*((2*j+(n-j)/2).choose ((n-j)/2) : ℚ) else 0 := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_even_inv_pow h hh]
  split_ifs <;> simp_all

theorem coeff_fact_trunc (h : PowerSeries ℚ) (hh : h*(1-X^2)=1) (N n : ℕ) (hn : n ≤ N) :
    coeff n (∑ j ∈ range (N+1), C (j.factorial : ℚ)*X^j*h^(2*j+1)) =
      ∑ k ∈ range (n/2+1), ((2*n-3*k).choose k : ℚ) * ((n-2*k).factorial : ℚ) := by
  rw [map_sum]
  simp_rw [coeff_fact_term h hh]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun k _ => n-2*k)
  · intro k hk
    simp only [mem_range] at hk
    simp only [mem_filter,mem_range]
    refine ⟨by omega,by omega,⟨k,by omega⟩⟩
  · intro k hk l hl he
    simp only [mem_range] at hk hl
    omega
  · intro j hj
    simp only [mem_filter,mem_range] at hj
    obtain ⟨u,hu⟩ := hj.2.2
    exact ⟨u,by simp only [mem_range]; omega,by omega⟩
  · intro k hk
    simp only [mem_range] at hk
    have he : (n - (n-2*k))/2 = k := by omega
    rw [he, show 2*(n-2*k)+k = 2*n-3*k by omega, mul_comm]

theorem native_trunc (h : PowerSeries ℚ) (hh : h*(1-X^2)=1) (N n : ℕ) (hn : n ≤ N) :
    coeff n (∑ j ∈ range (N+1), C (j.factorial : ℚ)*X^j*h^(2*j+1)) =
      (OMA.S_oeis_a155858.a n : ℚ) := by
  rw [coeff_fact_trunc h hh N n hn]
  simp [OMA.S_oeis_a155858.a]

end Fact155

namespace Fact155
open Finset PowerSeries

private theorem coeff_subst_trunc (f h : PowerSeries ℚ) (N n : ℕ) (hn : n ≤ N) :
    coeff n (subst (X*h^2) f) =
      coeff n (∑ j ∈ range (N+1), C (coeff j f) * (X*h^2)^j) := by
  have hb : HasSubst (X*h^2) := HasSubst.of_constantCoeff_zero (by
    change PowerSeries.constantCoeff (X*h^2) = 0
    simp)
  rw [coeff_subst' hb, map_sum]
  simp_rw [coeff_C_mul]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  change coeff j f * coeff n ((X*h^2)^j) ≠ 0 at hj
  change j ∈ range (N+1)
  rw [mem_range]
  by_contra! hnj
  rw [mul_pow, coeff_X_pow_mul', if_neg (by omega), mul_zero] at hj
  exact hj rfl

/-- The ordinary generating series for A155858 is `h * F(X*h^2)`,
where `h=(1-X^2)⁻¹` and `F` has coefficients `j!`. -/
theorem factorial_generating_series (h : PowerSeries ℚ) (hh : h*(1-X^2)=1) :
    mk (fun n => (OMA.S_oeis_a155858.a n : ℚ)) =
      h * subst (X*h^2) (mk (fun j => (j.factorial : ℚ))) := by
  symm
  let F : PowerSeries ℚ := mk (fun j => (j.factorial : ℚ))
  ext n
  rw [coeff_mk, ← native_trunc h hh n n le_rfl]
  change coeff n (h * subst (X*h^2) F) = _
  have he : (∑ j ∈ range (n+1), C (j.factorial : ℚ)*X^j*h^(2*j+1)) =
      h * ∑ j ∈ range (n+1), C (coeff j F) * (X*h^2)^j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [F, coeff_mk, pow_succ, mul_pow, ← pow_mul]
    ring
  rw [he, coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [coeff_subst_trunc F h n ij.2 (by have := (mem_antidiagonal.mp hij); omega)]

end Fact155

namespace Fact155
open PowerSeries Finset

noncomputable def den : ℚ⟦X⟧ := 1-X^2
noncomputable def factor : ℚ⟦X⟧ := 1+3*X^2
noncomputable def geom : ℚ⟦X⟧ := den⁻¹
noncomputable def arg : ℚ⟦X⟧ := X*geom^2
noncomputable def row (j : ℕ) : ℚ⟦X⟧ := C (j.factorial:ℚ)*X^j*geom^(2*j+1)
noncomputable def op (f : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  (-X^2*den)*derivative ℚ f + (2*X^3+(den^2-X)*factor)*f

theorem geom_den : geom*den=1 := PowerSeries.inv_mul_cancel _ (by simp [den])

theorem den_arg : den^2*arg=X := by
  calc
    _ = X*(geom*den)^2 := by unfold arg; ring
    _ = _ := by rw [geom_den]; ring

theorem dgeom : derivative ℚ geom=2*X*geom^2 := by
  unfold geom
  rw [derivative_inv']
  change -(den⁻¹)^2 * derivative ℚ (1-X^2) = _
  rw [map_sub,derivative_one,derivative_pow,derivative_X]
  norm_num
  ring

theorem darg : derivative ℚ arg = factor*geom^3 := by
  unfold arg
  rw [Derivation.leibniz,derivative_pow,derivative_X,dgeom]
  simp only [smul_eq_mul]
  norm_num
  have h : geom*(1-X^2)=1 := geom_den
  unfold factor
  linear_combination -(geom^2)*h

theorem arg_differential : X^2*den*derivative ℚ arg = factor*den^2*arg^2 := by
  rw [darg]
  calc
    _ = factor*X^2*geom^2*(geom*den) := by ring
    _ = factor*(den^2*arg)*arg := by rw [geom_den,den_arg]; unfold arg; ring
    _ = _ := by ring

theorem row_zero : row 0 = geom := by simp [row]

theorem row_succ (j : ℕ) : row (j+1) = C ((j:ℚ)+1)*arg*row j := by
  simp only [row,arg,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,map_mul]
  rw [show 2*(j+1)+1=(2*j+1)+2 by omega,pow_add geom (2*j+1) 2,pow_succ X j]
  ring

theorem op_factor (c : ℚ) (f : ℚ⟦X⟧) :
    op (C c*arg*f) = C c*(arg*op f - X^2*den*derivative ℚ arg*f) := by
  unfold op
  simp only [Derivation.leibniz,derivative_C,smul_eq_mul]
  ring

theorem row_telescopes (j : ℕ) : op (row j) = factor*den^2*(row j-row (j+1)) := by
  induction j with
  | zero =>
    rw [row_succ,row_zero]
    simp only [Nat.cast_zero,zero_add,map_one,one_mul]
    unfold op
    rw [dgeom]
    calc
      _ = -2*X^3*geom*(geom*den)+2*X^3*geom+factor*den^2*geom-factor*X*geom := by ring
      _ = factor*den^2*geom - factor*(den^2*arg)*geom := by rw [geom_den,den_arg]; ring
      _ = _ := by ring
  | succ j ih =>
    calc
      op (row (j+1)) = C ((j:ℚ)+1)*(arg*op (row j)-X^2*den*derivative ℚ arg*row j) := by rw [row_succ,op_factor]
      _ = C ((j:ℚ)+1)*(arg*(factor*den^2*(row j-C ((j:ℚ)+1)*arg*row j))-factor*den^2*arg^2*row j) := by
        rw [ih,row_succ j,arg_differential]
      _ = factor*den^2*(row (j+1)-row (j+1+1)) := by
        rw [row_succ (j+1),row_succ j]
        simp only [Nat.cast_add,Nat.cast_one,map_add,map_one]
        ring

theorem finite_telescopes (N : ℕ) : op (∑ j ∈ range N, row j) = den*factor - factor*den^2*row N := by
  induction N with
  | zero =>
    simp only [range_zero,sum_empty,row_zero,op,map_zero,mul_zero,add_zero]
    calc
      (0 : ℚ⟦X⟧) = den*factor-den*factor*(geom*den) := by rw [geom_den]; ring
      _ = _ := by ring
  | succ N ih =>
    rw [sum_range_succ]
    have add (f g : ℚ⟦X⟧) : op (f+g)=op f + op g := by unfold op; rw [map_add]; ring
    rw [add,ih,row_telescopes]
    ring

end Fact155

namespace Fact155
open PowerSeries Finset

noncomputable def series : ℚ⟦X⟧ := mk (fun n => (OMA.S_oeis_a155858.a n : ℚ))

theorem coeff_multiple_agree (u f g : ℚ⟦X⟧) (n : ℕ)
    (h : ∀ j ≤ n, coeff j f = coeff j g) : coeff n (u*f) = coeff n (u*g) := by
  rw [coeff_mul,coeff_mul]
  apply sum_congr rfl
  intro j hj
  have hj' := Finset.HasAntidiagonal.mem_antidiagonal.mp hj
  rw [h j.2 (by omega)]

/-- The nth coefficient uses only rows up to n+1 even after differentiation.
The explicit boundary row in the finite telescoping identity has no coefficient there. -/
theorem series_equation : op series = den*factor := by
  ext n
  let N := n+1
  let f := ∑ j ∈ range (N+1), row j
  have upto (k : ℕ) (hk : k ≤ n+1) : coeff k series = coeff k f := by
    rw [series,coeff_mk]
    exact (native_trunc geom geom_den N k hk).symm
  have deriv (k : ℕ) (hk : k ≤ n) : coeff k (derivative ℚ series) = coeff k (derivative ℚ f) := by
    rw [coeff_derivative,coeff_derivative,upto (k+1) (by omega)]
  have same : coeff n (op series) = coeff n (op f) := by
    unfold op
    simp only [map_add]
    rw [coeff_multiple_agree _ _ _ n deriv,coeff_multiple_agree _ series f n (fun j hj => upto j (by omega))]
  have tail : coeff n (factor*den^2*row (N+1))=0 := by
    rw [show factor*den^2*row (N+1) = (factor*den^2*C ((N+1).factorial:ℚ)*geom^(2*(N+1)+1))*X^(N+1) by
      unfold row; ring,coeff_mul_X_pow',if_neg (by dsimp [N]; omega)]
  rw [same]
  change coeff n (op (∑ j ∈ range (N+1), row j)) = _
  rw [finite_telescopes,map_sub,tail,sub_zero]

end Fact155

namespace Fact155
open PowerSeries

/-- Multiply the differential equation by 1 + X before taking its nth
coefficient, so that the shifts agree with the proposed seven-step recurrence. -/
theorem recurrence_of_ode {R : Type*} [CommRing R] (A : PowerSeries R)
    (ode : (-X^2*(1-X^2))*derivative R A +
      (2*X^3+((1-X^2)^2-X)*(1+3*X^2))*A = (1-X^2)*(1+3*X^2))
    (n : ℕ) (hn : 7 ≤ n) :
    coeff n A - ((n : R)-1)*coeff (n-1) A - ((n : R)-2)*coeff (n-2) A +
      ((n : R)-3)*coeff (n-3) A + ((n : R)-10)*coeff (n-4) A -
      5*coeff (n-5) A + 3*coeff (n-6) A + 3*coeff (n-7) A = 0 := by
  let D := derivative R A
  have expanded : A - X^2*D - X^3*D + X^4*D + X^5*D -
      C (6:R)*(X^4*A) - C (5:R)*(X^5*A) + C (3:R)*(X^6*A) + C (3:R)*(X^7*A) =
      1+X + C (2:R)*X^2 + C (2:R)*X^3 - C (3:R)*X^4 - C (3:R)*X^5 := by
    simp only [map_ofNat,D]
    linear_combination (1+X) * ode
  have heq := congrArg (PowerSeries.coeff n) expanded
  simp (disch := omega) only [map_add,map_sub,coeff_C_mul,coeff_X_pow_mul',if_pos,if_neg,
    D, coeff_derivative, coeff_one, coeff_X, coeff_X_pow, Nat.cast_sub,
    Nat.cast_ofNat, mul_zero, add_zero, sub_zero] at heq
  rw [show n-2+1=n-1 by omega, show n-3+1=n-2 by omega,
    show n-4+1=n-3 by omega, show n-5+1=n-4 by omega] at heq
  linear_combination heq

end Fact155

namespace Fact155
open PowerSeries

/-- The unmultiplied differential equation yields the order-six recurrence
implemented independently in loader3229's LODA program for A155858. -/
theorem six_of_ode {R : Type*} [CommRing R] (A : PowerSeries R)
    (ode : (-X^2*(1-X^2))*derivative R A +
      (2*X^3+((1-X^2)^2-X)*(1+3*X^2))*A = (1-X^2)*(1+3*X^2))
    (n : ℕ) (hn : 6 ≤ n) :
    coeff n A - (n:R)*coeff (n-1) A + coeff (n-2) A +
      ((n:R)-4)*coeff (n-3) A - 5*coeff (n-4) A + 3*coeff (n-6) A = 0 := by
  let D := derivative R A
  have expanded : A - X^2*D + X^4*D - X^1*A + X^2*A - X^3*A -
      C (5:R)*(X^4*A) + C (3:R)*(X^6*A) =
      1 + C (2:R)*X^2 - C (3:R)*X^4 := by
    simp only [map_ofNat,D]
    linear_combination ode
  have heq := congrArg (PowerSeries.coeff n) expanded
  simp (disch := omega) only [map_add,map_sub,coeff_C_mul,coeff_X_pow_mul',if_pos,if_neg,
    D, coeff_derivative, coeff_one, coeff_X_pow, Nat.cast_sub, Nat.cast_ofNat,
    mul_zero, add_zero, sub_zero] at heq
  rw [show n-2+1=n-1 by omega, show n-4+1=n-3 by omega] at heq
  linear_combination heq

end Fact155

namespace Fact155

/-- Zero-padded binomial row of the reciprocal power `(1-X)^(-a-1)`. -/
def pascalKernel (a : ℕ) : ℤ → ℤ
  | Int.ofNat k => ((a+k).choose k : ℤ)
  | Int.negSucc _ => 0

theorem pascal_back (a : ℕ) (k : ℤ) :
    pascalKernel (a+1) k - pascalKernel (a+1) (k-1) = pascalKernel a k := by
  cases k with
  | negSucc k => rfl
  | ofNat k =>
    cases k with
    | zero => rw [show Int.ofNat 0 - 1 = Int.negSucc 0 by decide]; simp [pascalKernel]
    | succ k =>
      rw [show Int.ofNat (k+1) - 1 = Int.ofNat k by change ((k+1 : ℕ):ℤ)-1 = (k:ℤ); omega]
      change (((a+1+(k+1)).choose (k+1) : ℕ) : ℤ) - ((a+1+k).choose k : ℕ) = ((a+(k+1)).choose (k+1) : ℕ)
      rw [show a+1+(k+1) = (a+1+k)+1 by omega, Nat.choose_succ_succ, Nat.cast_add,
        show a+(k+1) = a+1+k by omega]
      ring

theorem pascal_moment (a : ℕ) (k : ℤ) :
    k * pascalKernel a k = (a+k)*pascalKernel a (k-1) := by
  cases k with
  | negSucc k => change _ * 0 = _ * 0; simp
  | ofNat k =>
    cases k with
    | zero => rw [show Int.ofNat 0 - 1 = Int.negSucc 0 by decide]; simp [pascalKernel]
    | succ k =>
      rw [show Int.ofNat (k+1) - 1 = Int.ofNat k by change ((k+1 : ℕ):ℤ)-1 = (k:ℤ); omega]
      change ((k+1 : ℕ) : ℤ)*((a+(k+1)).choose (k+1) : ℕ) =
        ((a:ℤ)+(k+1 : ℕ))*((a+k).choose k : ℕ)
      exact_mod_cast (show (k+1)*(a+(k+1)).choose (k+1) = (a+(k+1))*(a+k).choose k by
        simpa only [Nat.add_assoc, Nat.mul_comm] using (Nat.add_one_mul_choose_eq (a+k) k).symm)

theorem pascal_second (a : ℕ) (k : ℤ) :
    pascalKernel (a+2) k - 2*pascalKernel (a+2) (k-1) + pascalKernel (a+2) (k-2) =
    pascalKernel a k := by
  have h1 := pascal_back (a+1) k
  have h2 := pascal_back (a+1) (k-1)
  have h3 := pascal_back a k
  rw [show k-1-1 = k-2 by ring] at h2
  linarith

/-- Pointwise cancellation for the sixth-order recurrence, after extracting the
common factorial. Here the factorial index in its even shifts is `b+1`. -/
theorem pascal_local (b : ℕ) (k : ℤ) :
    (b+1 : ℤ)*(pascalKernel (2*b+2) k + pascalKernel (2*b+2) (k-1)
      -5*pascalKernel (2*b+2) (k-2) +3*pascalKernel (2*b+2) (k-3)) =
    (b+1+2*k)*pascalKernel (2*b) k - (b+1+2*k-4)*pascalKernel (2*b) (k-1) := by
  have h0 := pascal_second (2*b) k
  have h1 := pascal_second (2*b) (k-1)
  rw [show k-1-1 = k-2 by ring, show k-1-2 = k-3 by ring] at h1
  have hb := pascal_moment (2*b) k
  push_cast at hb
  calc
    _ = (b+1 : ℤ)*(pascalKernel (2*b) k + 3*pascalKernel (2*b) (k-1)) := by
      congr 1
      linarith
    _ = _ := by linear_combination -2 * hb

end Fact155

namespace Fact155

/-- The factorial index and binomial summation index, both padded by zero. -/
def factorialBlock : ℤ → ℤ → ℤ
  | Int.ofNat j, k => (j.factorial : ℤ) * pascalKernel (2*j) k
  | Int.negSucc _, _ => 0

def diagonalTerm (v k : ℤ) := factorialBlock (v-2*k) k

theorem kernel_zero_row (k : ℤ) (hk : 0 ≤ k) : pascalKernel 0 k = 1 := by
  cases k with
  | ofNat k => simp [pascalKernel]
  | negSucc k => omega

theorem factorial_local (j k : ℤ) (hn : 6 ≤ j+2*k) :
    factorialBlock j k + factorialBlock j (k-1) - 5*factorialBlock j (k-2) + 3*factorialBlock j (k-3) =
    (j+2*k)*factorialBlock (j-1) k - (j+2*k-4)*factorialBlock (j-1) (k-1) := by
  cases j with
  | negSucc j => change 0+0-5*0+3*0 = _*0-_*0; ring
  | ofNat j =>
    cases j with
    | zero =>
      rw [show Int.ofNat 0 - 1 = Int.negSucc 0 by decide]
      change 6 ≤ 0+2*k at hn
      have hk : 3 ≤ k := by omega
      simp only [factorialBlock, Nat.factorial_zero, Nat.cast_one, one_mul,
        kernel_zero_row k (by omega),kernel_zero_row (k-1) (by omega),
        kernel_zero_row (k-2) (by omega),kernel_zero_row (k-3) (by omega),mul_zero]
      norm_num
    | succ b =>
      rw [show Int.ofNat (b+1)-1 = Int.ofNat b by change ((b+1 : ℕ):ℤ)-1 = (b:ℤ); omega]
      simp only [factorialBlock, Nat.mul_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Int.ofNat_eq_natCast]
      linear_combination (b.factorial : ℤ) * pascal_local b k

theorem diagonal_local (v k : ℤ) (hv : 6 ≤ v) :
    diagonalTerm v k - v*diagonalTerm (v-1) k + diagonalTerm (v-2) (k-1) +
    (v-4)*diagonalTerm (v-3) (k-1) - 5*diagonalTerm (v-4) (k-2) +
    3*diagonalTerm (v-6) (k-3) = 0 := by
  have h := factorial_local (v-2*k) k (by omega)
  unfold diagonalTerm
  rw [show v-2-2*(k-1) = v-2*k by ring, show v-4-2*(k-2) = v-2*k by ring,
    show v-6-2*(k-3) = v-2*k by ring, show v-1-2*k=v-2*k-1 by ring,
    show v-3-2*(k-1)=v-2*k-1 by ring]
  linear_combination h

theorem diagonal_low (v k : ℤ) (hk : k < 0) : diagonalTerm v k = 0 := by
  unfold diagonalTerm
  cases v-2*k with
  | negSucc j => rfl
  | ofNat j => cases k with
    | ofNat z => change (z:ℤ) < 0 at hk; omega
    | negSucc z => simp [factorialBlock,pascalKernel]

theorem diagonal_high (v k : ℕ) (hk : v < 2*k) : diagonalTerm v k = 0 := by
  unfold diagonalTerm
  obtain ⟨j,hj⟩ : ∃ j, (v:ℤ)-2*k = Int.negSucc j := by
    cases h : (v:ℤ)-2*k with
    | negSucc j => exact ⟨j,rfl⟩
    | ofNat j => change (v:ℤ)-2*k=(j:ℤ) at h; omega
  rw [hj]
  rfl

theorem diagonal_in_range (v k : ℕ) (hk : 2*k ≤ v) :
    diagonalTerm v k = ((2*v-3*k).choose k : ℤ) * ((v-2*k).factorial : ℤ) := by
  unfold diagonalTerm
  rw [show (v:ℤ)-2*k = Int.ofNat (v-2*k) by change _ = ((v-2*k : ℕ):ℤ); omega]
  change ((v-2*k).factorial : ℤ) * ((2*(v-2*k)+k).choose k : ℤ) = _
  rw [show 2*(v-2*k)+k = 2*v-3*k by omega, mul_comm]

theorem sum_diagonal (v M s : ℕ) (hh : v/2+s ≤ M) :
    (∑ k ∈ Finset.range (M+1), diagonalTerm v ((k:ℤ)-s)) = OMA.S_oeis_a155858.a v := by
  rw [show M+1 = s+(M+1-s) by omega, Finset.sum_range_add]
  have hz : (∑ k ∈ Finset.range s, diagonalTerm v ((k:ℤ)-s)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact diagonal_low _ _ (by have := Finset.mem_range.mp hk; omega)
  simp only [hz, zero_add, Nat.cast_add, add_sub_cancel_left]
  unfold OMA.S_oeis_a155858.a
  calc
    _ = ∑ k ∈ Finset.range (v/2+1), diagonalTerm v k := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k _ hk
      exact diagonal_high _ _ (by have := Finset.mem_range.not.mp hk; omega)
    _ = _ := Finset.sum_congr rfl (fun k hk => diagonal_in_range _ _ (by have := Finset.mem_range.mp hk; omega))

end Fact155

namespace Fact155
open OMA.S_oeis_a155858

/-- Pascal cancellation gives a sixth-order homogeneous recurrence. -/
theorem six (v : ℕ) (hv : 6 ≤ v) :
    a v - (v:ℤ)*a (v-1) + a (v-2) + ((v:ℤ)-4)*a (v-3) -5*a (v-4)+3*a (v-6) = 0 := by
  have h := Finset.sum_eq_zero (s:=Finset.range (v+1))
    (fun (k : ℕ) _ => diagonal_local (v:ℤ) (k:ℤ) (by exact_mod_cast hv))
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at h
  have h0 := sum_diagonal v v 0 (by omega)
  have h1 := sum_diagonal (v-1) v 0 (by omega)
  simp only [Nat.cast_zero,sub_zero] at h0 h1
  have h2 := sum_diagonal (v-2) v 1 (by omega)
  have h3 := sum_diagonal (v-3) v 1 (by omega)
  have h4 := sum_diagonal (v-4) v 2 (by omega)
  have h6 := sum_diagonal (v-6) v 3 (by omega)
  norm_num only [Nat.cast_one, Nat.cast_ofNat] at h2 h3 h4 h6
  rw [show (v:ℤ)-1 = ((v-1:ℕ):ℤ) by omega, show (v:ℤ)-2 = ((v-2:ℕ):ℤ) by omega,
    show (v:ℤ)-3 = ((v-3:ℕ):ℤ) by omega, show (v:ℤ)-4 = ((v-4:ℕ):ℤ) by omega,
    show (v:ℤ)-6 = ((v-6:ℕ):ℤ) by omega,
    h0,h1,h2,h3,h4,h6] at h
  simpa only [Nat.cast_sub (by omega : 4≤v), Nat.cast_ofNat] using h

theorem seven (v : ℕ) (hv : 7 ≤ v) :
    a v - ((v:ℤ)-1)*a (v-1) - ((v:ℤ)-2)*a (v-2) + ((v:ℤ)-3)*a (v-3) +
    ((v:ℤ)-10)*a (v-4)-5*a (v-5)+3*a (v-6)+3*a (v-7)=0 := by
  have lo := six (v-1) (by omega)
  simp only [Nat.sub_sub, Nat.cast_sub (by omega : 1≤v), Nat.cast_one] at lo
  linear_combination six v (by omega) + lo

end Fact155

open Fact155 PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a155858.main := by
  intro n hn
  have h := Fact155.recurrence_of_ode Fact155.series Fact155.series_equation n hn
  simp only [Fact155.series,coeff_mk] at h
  exact_mod_cast h
