import OMAStatements.S_oeis_a004737

/-!
# Jeffery's Gram matrix at the midpoint Chebyshev nodes

Midpoint averaging kills every nonconstant cosine mode of frequency less than
twice the number of nodes. The Chebyshev recurrence gives the resulting mean
of each second-kind polynomial. A product identity then reduces the two
column indices together, leaving one contribution for each matching parity.
-/

namespace Jeffery4737
open Finset Real

/-- Each nonconstant cosine frequency below 2q averages to zero on the q midpoints. -/
theorem midpoint_cos_sum (q m : ℕ) (hq : 1 ≤ q) (hm : 0 < m) (hmq : m < 2*q) :
    (∑ r : Fin q, Real.cos ((m:ℝ) * ((2*(r.val:ℝ)+1)*Real.pi/(2*(q:ℝ))))) = 0 := by
  let h := (m:ℝ)*π/(2*(q:ℝ))
  have hq' : 0 < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hh : 0 < h := by dsimp [h]; positivity
  have hhp : h < π := by
    apply (div_lt_iff₀ (by positivity : 0 < 2*(q:ℝ))).mpr
    have hm' : (m:ℝ) < 2*(q:ℝ) := by exact_mod_cast hmq
    linarith [mul_lt_mul_of_pos_right hm' Real.pi_pos]
  have hsin := Real.sin_pos_of_pos_of_lt_pi hh hhp
  let f := fun i : ℕ => Real.sin (2 * (i:ℝ) * h)
  have adj (i : ℕ) : (2 * Real.sin h) * Real.cos ((m:ℝ)*((2*(i:ℝ)+1)*π/(2*(q:ℝ)))) =
      f (i+1) - f i := by
    dsimp [f]
    rw [Real.sin_sub_sin]
    push_cast
    have mid : (2*((i:ℝ)+1)*h+2*i*h)/2 = (m:ℝ)*((2*i+1)*π/(2*q)) := by
      dsimp [h]
      ring
    rw [mid, show (2*((i:ℝ)+1)*h-2*i*h)/2 = h by ring]
  have htop : f q = 0 := by
    dsimp [f,h]
    rw [show 2*(q:ℝ)*((m:ℝ)*π/(2*q)) = m*π by field_simp]
    exact Real.sin_nat_mul_pi m
  have hval : (2 * Real.sin h) *
      (∑ i ∈ range q, Real.cos ((m:ℝ)*((2*(i:ℝ)+1)*π/(2*(q:ℝ))))) = 0 := by
    simp only [Finset.mul_sum, adj]
    rw [Finset.sum_range_sub f q, htop]
    simp [f]
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => Real.cos ((m:ℝ)*((2*(r:ℝ)+1)*π/(2*(q:ℝ))))) q]
  exact (mul_eq_zero.mp hval).resolve_left (by positivity)

end Jeffery4737

/-! Midpoint sums for Chebyshev polynomials of the second kind. -/

namespace A4737
open OMA.S_oeis_a004737 Polynomial Polynomial.Chebyshev

theorem U_sum (cosine : ∀ q m : ℕ, 1 ≤ q → 0 < m → m < 2*q →
    ∑ r : Fin q, Real.cos ((m:ℝ)*((2*(r.val:ℝ)+1)*Real.pi/(2*(q:ℝ)))) = 0)
    (q m : ℕ) (hq : 0 < q) (hm : m < 2*q) :
    ∑ r : Fin q, (U ℝ (m:ℤ)).eval (x q r) = if Even m then (q:ℝ) else 0 := by
  have tsum (k : ℕ) (hpos : 0 < k) (hlt : k < 2*q) :
      ∑ r : Fin q, (T ℝ (k:ℤ)).eval (x q r) = 0 := by
    simpa only [x,T_real_cos,Int.cast_natCast] using cosine q k hq hpos hlt
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases m with _|m
    · simp
    rcases m with _|k
    · have h := tsum 1 (by decide) hm
      have hx : ∑ r : Fin q, x q r = 0 := by simpa using h
      change (∑ r : Fin q, (U ℝ 1).eval (x q r)) = if Even (1:ℕ) then (q:ℝ) else 0
      simp [← Finset.mul_sum,hx]
    · have h := tsum (k+2) (by omega) hm
      have ihk := ih k (by omega) (by omega)
      change ∑ r : Fin q, (U ℝ ((k:ℤ)+2)).eval (x q r) = _
      simp_rw [U_eq_two_mul_T_add_U,eval_add,eval_mul,eval_ofNat]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      change 2*(∑ r : Fin q, (T ℝ ((k+2:ℕ):ℤ)).eval (x q r)) + _ = _
      rw [h, ihk]
      have he : Even (k+1+1) ↔ Even k := by simp only [Nat.even_iff]; omega
      simp [he]

end A4737

namespace Cheb4737
open Polynomial Polynomial.Chebyshev

/-- The second-kind Chebyshev recurrence lets one shift a unit of degree
between the two factors in their product difference. -/
theorem u_product (R : Type*) [CommRing R] (i j : ℕ) :
    U R ((i : ℤ)+1) * U R ((j : ℤ)+1) =
      U R i * U R j + U R ((i : ℤ)+j+2) := by
  induction i generalizing j with
  | zero =>
    simp only [Nat.cast_zero, zero_add, U_one, U_zero, one_mul]
    rw [U_add_two]
    ring
  | succ i ih =>
    have h := ih (j+1)
    simp only [Nat.cast_succ] at h ⊢
    rw [show (j : ℤ)+1+1 = j+2 by ring, U_add_two] at h
    rw [show (i : ℤ)+1+1 = i+2 by ring, U_add_two,
      show (i : ℤ)+1+j+2 = i+(j+1)+2 by ring]
    linear_combination h

theorem u_eval_product (i j : ℕ) (x : ℝ) :
    (U ℝ (↑(i+1 : ℕ))).eval x * (U ℝ (↑(j+1 : ℕ))).eval x =
      (U ℝ i).eval x * (U ℝ j).eval x + (U ℝ (↑(i+j+2 : ℕ))).eval x := by
  simpa using congrArg (fun P : ℝ[X] => eval x P) (u_product ℝ i j)

end Cheb4737

namespace Jeffery4737
open Finset

/-- The product identity strips one degree from each column. All degrees seen
in the process are below twice the number of nodes. -/
theorem gram_from_means {q : ℕ} (u : ℕ → Fin q → ℝ)
    (hzero : ∀ r, u 0 r = 1)
    (hmean : ∀ m : ℕ, m < 2*q → ∑ r : Fin q, u m r = if Even m then (q:ℝ) else 0)
    (hprod : ∀ i j r, u (i+1) r*u (j+1) r = u i r*u j r+u (i+j+2) r)
    (i j : ℕ) (hi : i < q) (hj : j < q) :
    (∑ r : Fin q, u i r * u j r) =
      if Even (i+j) then (q:ℝ)*((min i j+1 : ℕ):ℝ) else 0 := by
  induction i generalizing j with
  | zero => simpa [hzero] using hmean j (by omega)
  | succ i ih =>
    cases j with
    | zero => simpa [hzero] using hmean (i+1) (by omega)
    | succ j =>
      simp_rw [hprod]
      rw [sum_add_distrib, ih j (by omega) (by omega), hmean _ (by omega)]
      have hpar : Even (i+j+2) ↔ Even (i+j) := by simp only [Nat.even_iff]; omega
      have hpar' : Even (i+1+(j+1)) ↔ Even (i+j) := by
        rw [show i+1+(j+1)=i+j+2 by omega, hpar]
      by_cases h : Even (i+j)
      · simp only [if_pos h, if_pos (hpar.mpr h), if_pos (hpar'.mpr h), Nat.succ_min_succ, Nat.cast_succ]
        ring
      · rw [if_neg h, if_neg (fun he => h (hpar.mp he)), if_neg (fun he => h (hpar'.mp he)), zero_add]

end Jeffery4737

open OMA.S_oeis_a004737 Polynomial.Chebyshev

theorem OMA.solution : type_of% @OMA.S_oeis_a004737.main := by
  intro q hq i j
  let u (k : ℕ) (r : Fin q) := (U ℝ (k:ℤ)).eval (x q r)
  have mean := A4737.U_sum Jeffery4737.midpoint_cos_sum q
  have hg := Jeffery4737.gram_from_means u (fun r => by simp [u])
    (fun m hm => mean m hq hm)
    (fun k l r => Cheb4737.u_eval_product k l (x q r)) i.val j.val i.isLt j.isLt
  change (q : ℝ)⁻¹ * (∑ r : Fin q, u i.val r * u j.val r) = _
  rw [hg]
  have hp : (q:ℝ) ≠ 0 := by exact_mod_cast (show q≠0 by omega)
  split <;> simp [hp]
