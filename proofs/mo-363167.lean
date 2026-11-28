import OMAStatements.S_mo_363167
import Mathlib

namespace OMA.S_mo_363167

open Matrix Polynomial
open scoped BigOperators MatrixOrder

private theorem expand_supported {A : Finset ℕ} {p : ℝ[X]} (hp : supported A p) :
    p = ∑ i ∈ A, monomial i (p.coeff i) := by
  calc
    p = ∑ i ∈ p.support, monomial i (p.coeff i) := (sum_monomial_eq p).symm
    _ = _ := Finset.sum_subset hp fun i _ hi => by
      rw [notMem_support_iff.mp hi, monomial_zero_right]

private noncomputable def rowPoly {A : Finset ℕ} {ι : Type*} (V : Matrix ι A ℝ) (r : ι) : ℝ[X] :=
  ∑ i : A, monomial i.val (V r i)

private theorem row_supported {A : Finset ℕ} {ι : Type*} (V : Matrix ι A ℝ) (r : ι) :
    supported A (rowPoly V r) := by
  intro k hk
  by_contra h
  have hzero : (rowPoly V r).coeff k = 0 := by
    rw [rowPoly, finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro i _
    have hne : i.val ≠ k := fun he => h (he ▸ i.property)
    rw [coeff_monomial, if_neg hne]
  exact (mem_support_iff.mp hk) hzero

private noncomputable def gramPoly {A : Finset ℕ} (Q : Matrix A A ℝ) : ℝ[X] :=
  ∑ i : A, ∑ j : A, monomial (i.val + j.val) (Q i j)

private theorem gram_coeff {A : Finset ℕ} (Q : Matrix A A ℝ) (k : ℕ) :
    (gramPoly Q).coeff k =
      ∑ i : A, ∑ j : A, if i.val + j.val = k then Q i j else 0 := by
  simp only [gramPoly, finsetSum_coeff, coeff_monomial]

private theorem gram_squares {A : Finset ℕ} {ι : Type*} [Fintype ι] (V : Matrix ι A ℝ) :
    gramPoly (Vᴴ * V) = ∑ r : ι, (rowPoly V r)^2 := by
  classical
  let g (i j : A) (r : ι) := monomial (i.val + j.val) (V r i * V r j)
  calc
    _ = ∑ i : A, ∑ j : A, ∑ r : ι, g i j r := by
      simp only [gramPoly, Matrix.mul_apply, conjTranspose_apply, star_trivial,
        g, map_sum]
    _ = ∑ i : A, ∑ r : ι, ∑ j : A, g i j r := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ r : ι, ∑ i : A, ∑ j : A, g i j r := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [rowPoly, pow_two, Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial, g]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [add_comm j.val i.val, mul_comm (V r j) (V r i)]

/-- A sum of squares gives a Gram matrix, and a positive semidefinite matrix factors into rows. -/
private theorem gram_iff (A : Finset ℕ) (f : ℝ[X]) :
    ordinarySOS A f ↔
      ∃ Q : Matrix A A ℝ, Q.PosSemidef ∧
        ∀ k, f.coeff k = ∑ i : A, ∑ j : A, if i.val + j.val = k then Q i j else 0 := by
  classical
  constructor
  · rintro ⟨m, p, hp, hf⟩
    let V : Matrix (Fin m) A ℝ := .of fun r i => (p r).coeff i.val
    have hr (r : Fin m) : rowPoly V r = p r := by
      rw [expand_supported (hp r)]
      unfold rowPoly
      exact Finset.sum_coe_sort A (fun i => monomial i ((p r).coeff i))
    refine ⟨Vᴴ * V, posSemidef_conjTranspose_mul_self V, fun k => ?_⟩
    rw [← gram_coeff, gram_squares, hf]
    simp only [hr]
  · rintro ⟨Q, hQ, hcoeff⟩
    have hf : f = gramPoly Q := by
      ext k
      rw [gram_coeff, hcoeff]
    obtain ⟨V, hV⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hQ.nonneg
    have heq : Q = Vᴴ * V := by simpa only [star_eq_conjTranspose] using hV
    let e := (Fintype.equivFin A).symm
    refine ⟨Fintype.card A, fun i => rowPoly V (e i), fun i => row_supported V _, ?_⟩
    rw [hf, heq, gram_squares]
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm

private theorem example_supported : supported (sumSupport exponents) examplePoly := by
  have hset : sumSupport exponents = Finset.range 9 := by decide
  rw [hset]
  intro k hk
  have hdeg : examplePoly.natDegree ≤ 8 := by
    have h1 : ((X : ℝ[X])^2 - 1).natDegree ≤ 2 := by compute_degree
    have h4 : ((X : ℝ[X])^2 - 4).natDegree ≤ 2 := by compute_degree
    have hm := natDegree_mul_le (p := (X : ℝ[X])^2 - 1) (q := X^2 - 4)
    have hp := natDegree_pow_le (p := ((X : ℝ[X])^2 - 1) * (X^2 - 4)) (n := 2)
    unfold examplePoly
    omega
  exact Finset.mem_range.mpr ((le_natDegree_of_mem_supp k hk).trans hdeg |>.trans_lt (by decide))

private theorem sparse_eval (q : ℝ[X]) (hq : supported exponents q) (x : ℝ) :
    q.eval x = q.coeff 0 + q.coeff 1 * x + q.coeff 3 * x^3 + q.coeff 4 * x^4 := by
  conv_lhs => rw [expand_supported hq]
  norm_num [exponents, eval_finsetSum, eval_monomial]; ring

/-- Values at the four roots determine all coefficients on this support. -/
private theorem sparse_four_roots (q : ℝ[X]) (hq : supported exponents q)
    (h1 : q.eval 1 = 0) (h2 : q.eval 2 = 0)
    (hn1 : q.eval (-1) = 0) (hn2 : q.eval (-2) = 0) : q = 0 := by
  rw [sparse_eval q hq] at h1 h2 hn1 hn2
  norm_num at h1 h2 hn1 hn2
  have h0 : q.coeff 0 = 0 := by linarith
  have h1' : q.coeff 1 = 0 := by linarith
  have h3 : q.coeff 3 = 0 := by linarith
  have h4 : q.coeff 4 = 0 := by linarith
  rw [expand_supported hq]
  norm_num [exponents, h0, h1', h3, h4]

private theorem no_weighted : ¬ weightedSOS exponents examplePoly := by
  rintro ⟨m, p, g, h, hsum⟩
  have hver (x : ℝ) (hx : examplePoly.eval x = 0) (i : Fin m) :
      (g i * p i).eval x = 0 := by
    have hone : (g i).eval x * ((p i).eval x)^2 ≤
        ∑ j : Fin m, (g j).eval x * ((p j).eval x)^2 := by
      exact Finset.single_le_sum (fun j _ =>
        mul_nonneg ((h j).2.2 x) (sq_nonneg ((p j).eval x))) (Finset.mem_univ i)
    have hzero : (∑ j : Fin m, (g j).eval x * ((p j).eval x)^2) = 0 := by
      rw [hsum, eval_finsetSum] at hx
      simpa only [eval_mul, eval_pow] using hx
    rw [hzero] at hone
    have heq := le_antisymm hone (mul_nonneg ((h i).2.2 x) (sq_nonneg ((p i).eval x)))
    rw [eval_mul]
    rcases mul_eq_zero.mp heq with hg | hp
    · rw [hg, zero_mul]
    · rw [eq_zero_of_pow_eq_zero hp, mul_zero]
  have hp (i : Fin m) : g i * p i = 0 := by
    apply sparse_four_roots _ (h i).2.1
    all_goals
      apply hver
      norm_num [examplePoly, eval_mul, eval_sub, eval_pow]
  have hz : examplePoly = 0 := by
    rw [hsum]
    apply Finset.sum_eq_zero
    intro i _
    rw [pow_two, ← mul_assoc, hp i, zero_mul]
  have hh := congrArg (Polynomial.eval (0 : ℝ)) hz
  norm_num [examplePoly, eval_mul, eval_sub, eval_pow] at hh

end OMA.S_mo_363167

open OMA.S_mo_363167 in
theorem OMA.solution : type_of% @OMA.S_mo_363167.main := by
  refine ⟨gram_iff, by decide, example_supported, ?_, no_weighted⟩
  intro x
  simp only [examplePoly, Polynomial.eval_pow]
  exact sq_nonneg _