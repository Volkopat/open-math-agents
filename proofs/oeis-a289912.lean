import OMAStatements.S_oeis_a289912
import Mathlib

open PowerSeries OMA.S_oeis_a289912

private noncomputable def r : ℝ := Real.sqrt 2

private noncomputable def deltaSeries : ℚ⟦X⟧ := denominator r * (1+X)

private noncomputable def poly : ℚ⟦X⟧ := deltaSeries * (1-X^2)

private theorem root_bounds : (7/5 : ℝ) < r ∧ r < (71/50 : ℝ) := by
  unfold r
  constructor
  · exact (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  · exact (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)

private theorem weight_inc (n : ℕ) : 1 ≤ weight r (n+1)-weight r n ∧ weight r (n+1)-weight r n ≤ 2 := by
  let x : ℝ := ((n : ℝ)+1)*r
  have h : 1 ≤ r ∧ r ≤ 2 := by have := root_bounds; constructor <;> linarith
  have h₁ : round (x+1) ≤ round (x+r) := by
    rw [round_eq, round_eq]
    apply Int.floor_mono
    linarith [h.1]
  have h₂ : round (x+r) ≤ round (x+2) := by
    rw [round_eq, round_eq]
    apply Int.floor_mono
    linarith [h.2]
  rw [round_add_one] at h₁
  rw [round_add_ofNat] at h₂
  have hq₁ : (round x : ℚ) + 1 ≤ (round (x+r) : ℚ) := by exact_mod_cast h₁
  have hq₂ : (round (x+r) : ℚ) ≤ (round x : ℚ) + 2 := by exact_mod_cast h₂
  have e : (((n+1 : ℕ) : ℝ)+1)*r = x+r := by push_cast; unfold x; ring
  unfold weight
  rw [e]
  change 1 ≤ (round (x+r) : ℚ) - round x ∧ (round (x+r) : ℚ)-round x ≤ 2
  constructor <;> linarith

private theorem w0 : weight r 0 = 1 := by
  unfold weight
  have h : round r = 1 := by
    apply round_eq_iff.mpr
    have e := root_bounds
    constructor <;> norm_num <;> linarith
  simpa using congrArg (fun z : ℤ => (z : ℚ)) h

private theorem wi : weight r 1 = 3 ∧ weight r 2 = 4 ∧ weight r 3 = 6 ∧ weight r 4 = 7 := by
  have h : ∀ (n m : ℕ), ((n=1 ∧ m=3) ∨ (n=2 ∧ m=4) ∨ (n=3 ∧ m=6) ∨ (n=4 ∧ m=7)) →
      round (((n:ℝ)+1)*r) = (m:ℤ) := by
    intro n m e
    apply round_eq_iff.mpr
    have h := root_bounds
    rcases e with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      constructor <;> norm_num <;> linarith
  unfold weight
  exact ⟨by exact_mod_cast h 1 3 (by decide), by exact_mod_cast h 2 4 (by decide),
    by exact_mod_cast h 3 6 (by decide), by exact_mod_cast h 4 7 (by decide)⟩

private theorem delta_step (n : ℕ) :
    coeff (n+1) deltaSeries = (-1 : ℚ)^(n+1)*(weight r (n+1)-weight r n) := by
  simp [deltaSeries, denominator, mul_add, coeff_succ_mul_X, pow_succ]
  ring

private theorem delta_zero : coeff 0 deltaSeries = 1 := by simp [deltaSeries,denominator,mul_add,w0]

private theorem poly_step (n : ℕ) :
    coeff (n+3) poly = (-1 : ℚ)^(n+3)*
      ((weight r (n+3)-weight r (n+2))-(weight r (n+1)-weight r n)) := by
  unfold poly
  rw [mul_sub,mul_one,map_sub,coeff_mul_X_pow',if_pos (by omega),show n+3-2=n+1 by omega,
    show n+3=(n+2)+1 by omega,delta_step (n+2),delta_step n]
  simp only [pow_add]
  ring

private theorem poly_tail (n : ℕ) : coeff (n+3) poly ≤ 1 := by
  have h1 := weight_inc (n+2)
  have h2 := weight_inc n
  rw [poly_step]
  apply (le_abs_self _).trans
  rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,abs_le]
  constructor <;> linarith

private theorem poly_head :
    coeff 0 poly = 1 ∧ coeff 1 poly = -2 ∧ coeff 2 poly = 0 ∧
      coeff 3 poly = 0 ∧ coeff 4 poly = 0 := by
  obtain ⟨h1,h2,h3,h4⟩ := wi
  have h3' := poly_step 0
  have h4' := poly_step 1
  norm_num [h1,h2,h3,h4,w0] at h3' h4'
  simp only [poly,mul_sub,mul_one,map_sub,coeff_mul_X_pow']
  norm_num [delta_zero,delta_step,h1,h2,w0,poly_step,h3,h4]

private noncomputable def pulse : ℚ⟦X⟧ := 1+X^1-X^2-X^3

private theorem product_eq : (denominator r)⁻¹ * poly = pulse := by
  have h0 : constantCoeff (denominator r) = 1 := by simp [denominator,w0]
  unfold poly deltaSeries pulse
  rw [← mul_assoc, ← mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [h0]; norm_num)]
  ring

private theorem convolution (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), a r i * coeff (n-i) poly) = coeff n pulse := by
  rw [← product_eq, coeff_mul]
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => a r i * coeff j poly) n).symm

private theorem small_values (n : ℕ) (hn : n < 5) :
    a r n = ([1,3,5,9,18] : List ℚ)[n]?.getD 0 := by
  obtain ⟨p0,p1,p2,p3,p4⟩ := poly_head
  have c0 : a r 0 = 1 := by
    have e := convolution 0
    norm_num [pulse,p0,Finset.sum_range_succ,map_add,map_sub,coeff_one,coeff_X,coeff_X_pow] at e
    exact e
  have c1 : a r 1 = 3 := by
    have e := convolution 1
    norm_num [pulse,p0,p1,c0,Finset.sum_range_succ,map_add,map_sub,coeff_one,coeff_X,coeff_X_pow] at e
    linarith
  have c2 : a r 2 = 5 := by
    have e := convolution 2
    norm_num [pulse,p0,p1,p2,c0,c1,Finset.sum_range_succ,map_add,map_sub,coeff_one,coeff_X,coeff_X_pow] at e
    linarith
  have c3 : a r 3 = 9 := by
    have e := convolution 3
    norm_num [pulse,p0,p1,p2,p3,c0,c1,c2,Finset.sum_range_succ,map_add,map_sub,coeff_one,coeff_X,coeff_X_pow] at e
    linarith
  have c4 : a r 4 = 18 := by
    have e := convolution 4
    norm_num [pulse,p0,p1,p2,p3,p4,c0,c1,c2,c3,Finset.sum_range_succ,map_add,map_sub,coeff_one,coeff_X,coeff_X_pow] at e
    linarith
  interval_cases n <;> norm_num [c0,c1,c2,c3,c4]

private noncomputable def partialSum (n : ℕ) : ℚ := ∑ i ∈ Finset.range (n+1), a r i

private theorem tail_recurrence (n : ℕ) (hn : 5 ≤ n) :
    a r n - 2*a r (n-1) + (∑ i ∈ Finset.range (n-4), a r i * coeff (n-i) poly) = 0 := by
  have e := convolution n
  have hz : coeff n pulse = 0 := by
    simp [pulse,map_add,map_sub,coeff_one,coeff_X,coeff_X_pow,show n≠0 by omega,show n≠1 by omega,
      show n≠2 by omega,show n≠3 by omega]
  rw [hz, show n+1=(n-4)+5 by omega,Finset.sum_range_add] at e
  obtain ⟨p0,p1,p2,p3,p4⟩ := poly_head
  have er : (∑ i ∈ Finset.range 5, a r ((n-4)+i)*coeff (n-((n-4)+i)) poly) =
      a r n-2*a r (n-1) := by
    simp [Finset.sum_range_succ,show n-4+4=n by omega,show n-4+3=n-1 by omega,
      show n-(n-4)=4 by omega,show n-(n-4+1)=3 by omega,show n-(n-4+2)=2 by omega,
      show n-(n-1)=1 by omega,p0,p1,p2,p3,p4]
    ring
  rw [er] at e
  linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a289912.main := by
  change StrictMono (a r)
  have grow (n : ℕ) : 0 < a r n ∧ (0<n → 5*a r (n-1) ≤ 3*a r n) ∧ 2*partialSum n ≤ 5*a r n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases h : n < 5
      · interval_cases n <;> norm_num [partialSum,Finset.sum_range_succ,small_values]
      · have hprev := ih (n-1) (by omega)
        have hp := hprev.1
        have h1 := hprev.2.1 (by omega)
        have h2 := (ih (n-2) (by omega)).2.1 (by omega)
        have h3 := (ih (n-3) (by omega)).2.1 (by omega)
        have h4 := (ih (n-4) (by omega)).2.1 (by omega)
        rw [show n-1-1=n-2 by omega] at h1
        rw [show n-2-1=n-3 by omega] at h2
        rw [show n-3-1=n-4 by omega] at h3
        rw [show n-4-1=n-5 by omega] at h4
        have hsmall := (ih (n-5) (by omega)).2.2
        have hsum : (∑ i ∈ Finset.range (n-4), a r i * coeff (n-i) poly) ≤ partialSum (n-5) := by
          unfold partialSum
          rw [show n-5+1=n-4 by omega]
          apply Finset.sum_le_sum
          intro i hi
          have hil := Finset.mem_range.mp hi
          have ht := poly_tail (n-i-3)
          rw [show n-i-3+3=n-i by omega] at ht
          simpa only [mul_one] using mul_le_mul_of_nonneg_left ht (ih i (by omega)).1.le
        have he := tail_recurrence n (by omega)
        have hratio : 5*a r (n-1) ≤ 3*a r n := by
          linarith
        have hprefix : partialSum n = partialSum (n-1) + a r n := by
          unfold partialSum
          rw [show n-1+1=n by omega,Finset.sum_range_succ]
        exact ⟨by linarith, fun _ => hratio, by rw [hprefix]; linarith [hprev.2.2]⟩
  apply strictMono_nat_of_lt_succ
  intro n
  have hp := (grow n).1
  have hn := (grow (n+1)).2.1 (by omega)
  rw [Nat.add_sub_cancel] at hn
  linarith