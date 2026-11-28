import OMAStatements.S_oeis_a072523

namespace OMA.S_oeis_a072523
open Filter Topology Real Finset
open scoped goldenRatio

private noncomputable def r : ℝ := -ψ

private lemma rp : 0<r := neg_pos.mpr goldenConj_neg
private lemma r₁ : r<1 := by dsimp [r]; linarith [neg_one_lt_goldenConj]
private lemma r_inv : r=φ⁻¹ := inv_goldenRatio.symm

private lemma gap_ratio (l : ℕ) :
    Tendsto (fun n : ℕ => ((n+l).fib:ℝ)/n.fib) atTop (𝓝 (φ^l)) := by
  induction l with
  | zero =>
    apply Tendsto.congr' (f₁:=fun _ : ℕ => (1:ℝ))
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have h : n.fib≠0 := (Nat.fib_pos.mpr hn).ne'
      simp [h]
    · simp
  | succ l ih =>
    have h := (tendsto_add_atTop_iff_nat l).mpr tendsto_fib_succ_div_fib_atTop
    rw [pow_succ]
    apply (ih.mul h).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hpos : ((n+l).fib:ℝ) ≠ 0 := by exact_mod_cast (Nat.fib_pos.mpr (by omega : 0<n+l)).ne'
    change ((n+l).fib:ℝ)/n.fib * (((n+l+1).fib:ℝ)/(n+l).fib) = _
    field_simp
    rw [Nat.add_assoc]

private lemma lucas_trace (k : ℕ) : ∃ z : ℤ, φ^(k+1)+ψ^(k+1)=(z:ℝ) := by
  refine ⟨((k+1).fib:ℤ)+2*k.fib,?_⟩
  rw [← goldenRatio_mul_fib_succ_add_fib,← goldenConj_mul_fib_succ_add_fib]
  push_cast
  linear_combination ((k+1).fib:ℝ)*goldenRatio_add_goldenConj

private noncomputable def limitTerm (k : ℕ) : ℝ :=
  (r^(k+1)+ψ^(k+1))/2-(r*ψ)^(k+1)

private lemma fractional (k : ℕ) :
    0 < Int.fract (φ^(k+1)) ∧ Int.fract (φ^(k+1))/φ^(k+1) = limitTerm k := by
  obtain ⟨z,hz⟩ := lucas_trace k
  have hpos := pow_pos rp (k+1)
  have hlt := pow_lt_one₀ rp.le r₁ (by omega : k+1≠0)
  have hinv : (φ^(k+1))⁻¹=r^(k+1) := by rw [r_inv,inv_pow]
  have hp : ψ = -r := by simp [r]
  rw [div_eq_mul_inv,hinv]
  rcases Nat.even_or_odd (k+1) with he|ho
  · have heq : ψ^(k+1)=r^(k+1) := by rw [hp,he.neg_pow]
    have hh : Int.fract (φ^(k+1)) = 1-r^(k+1) := by
      apply Int.fract_eq_iff.mpr
      refine ⟨by linarith,by linarith,z-1,?_⟩
      rw [heq] at hz
      push_cast; linarith
    rw [hh]
    refine ⟨by linarith,?_⟩
    unfold limitTerm
    rw [mul_pow,heq]; ring
  · have heq : ψ^(k+1)= -r^(k+1) := by rw [hp,ho.neg_pow]
    have hh : Int.fract (φ^(k+1)) = r^(k+1) := by
      refine Int.fract_eq_iff.mpr ⟨hpos.le,hlt,z,?_⟩
      rw [heq] at hz
      linarith
    rw [hh]
    refine ⟨hpos,?_⟩
    unfold limitTerm
    rw [mul_pow,heq]; ring

private noncomputable def term (n k : ℕ) : ℝ := (remainder n k:ℝ)/n.fib

private lemma term_limit (k : ℕ) :
    Tendsto (fun n => term n k) atTop (𝓝 (limitTerm k)) := by
  apply (tendsto_add_atTop_iff_nat (k+1)).mp
  have h := gap_ratio (k+1)
  have hne : φ^(k+1) ≠ (⌊φ^(k+1)⌋:ℤ) := by
    intro h
    have hz : Int.fract (φ^(k+1))=0 := by unfold Int.fract; rw [← h]; ring
    exact (fractional k).1.ne' hz
  have hf := (continuousAt_fract hne).tendsto.comp h
  rw [← (fractional k).2]
  apply (hf.div h (pow_ne_zero _ goldenRatio_ne_zero)).congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hp : (n.fib:ℝ) ≠0 := by exact_mod_cast (Nat.fib_pos.mpr (by omega : 0<n)).ne'
  simp only [Pi.div_apply,Function.comp_apply,term,remainder,Nat.add_sub_cancel,if_pos hn,Int.fract_div_natCast_eq_div_natCast_mod]
  field_simp

private lemma fib_bounds (m : ℕ) :
    ((m+1).fib:ℝ) ≤ φ^(m+1) ∧ φ^(m+1) ≤ φ^2*((m+1).fib:ℝ) := by
  induction m using Nat.twoStepInduction with
  | zero => simp only [zero_add,Nat.fib_one,Nat.cast_one,pow_one,mul_one,goldenRatio_sq]; constructor <;> linarith [one_lt_goldenRatio]
  | one => norm_num [goldenRatio_sq]; linarith [goldenRatio_pos]
  | more m h0 h1 =>
    have hpow := goldenRatio_pow_sub_goldenRatio_pow (m+1)
    rw [show m+2+1=(m+1)+2 by omega,Nat.fib_add_two,Nat.cast_add]
    constructor <;> nlinarith only [h0.1,h0.2,h1.1,h1.2,hpow]

private lemma term_bound (n k : ℕ) : ‖term n k‖ ≤ φ^2 * r^(k+1) := by
  by_cases h : 3 ≤ n-(k+1)
  · let m := n-(k+1)
    have he : n=m+(k+1) := by dsimp [m]; omega
    have hm : 0 < m := by dsimp [m]; omega
    have hm' := fib_bounds (m-1)
    rw [Nat.sub_add_cancel hm] at hm'
    have hn' := fib_bounds (n-1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hn'
    have hmf : 0 < m.fib := Nat.fib_pos.mpr hm
    have hp : (0:ℝ)<n.fib := by exact_mod_cast (Nat.fib_pos.mpr (by omega : 0<n))
    have hle : ((remainder n k):ℝ) ≤ m.fib := by
      exact_mod_cast (show remainder n k < m.fib by simpa [remainder,h,m] using Nat.mod_lt n.fib hmf).le
    rw [Real.norm_eq_abs,abs_of_nonneg (by unfold term; positivity),term,div_le_iff₀ hp,r_inv,inv_pow]
    apply hle.trans
    apply hm'.1.trans
    have hmul := hn'.2
    rw [he,pow_add] at hmul
    have hpow : 0 < φ^(k+1) := pow_pos goldenRatio_pos _
    calc
      φ^m ≤ φ^2 * (n.fib:ℝ) / φ^(k+1) := (le_div_iff₀ hpow).mpr (by simpa only [← he] using hmul)
      _ = _ := by ring
  · have hh : 0 ≤ φ^2*r^(k+1) := mul_nonneg (sq_nonneg _) (pow_nonneg rp.le _)
    simpa only [term,remainder,if_neg h,Nat.cast_zero,zero_div,norm_zero] using hh

private lemma sum_identity (n : ℕ) : ∑' k, term n k = (a n:ℝ)/n.fib := by
  rw [tsum_eq_sum (s:=range n)]
  · simp [a,term,Nat.cast_sum,sum_div]
  · intro k hk
    simp only [mem_range,not_lt] at hk
    simp [term,remainder,show n-(k+1)=0 by omega]

private theorem sum_limitTerms : (∑' k, limitTerm k) = 2/Real.sqrt 5 := by
  have geo (x : ℝ) (hx : |x|<1) : HasSum (fun k : ℕ => x^(k+1)) (x/(1-x)) := by
    simpa [pow_succ,div_eq_mul_inv,mul_comm] using (hasSum_geometric_of_abs_lt_one hx).mul_right x
  have hr : |r|<1 := by simpa only [abs_of_pos rp] using r₁
  have hψ : |ψ|<1 := by rw [abs_of_neg goldenConj_neg]; exact r₁
  have hprod : |r*ψ|<1 := by
    rw [abs_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hr.le (abs_nonneg _) hψ
  have h : HasSum limitTerm ((r/(1-r)+ψ/(1-ψ))/2-(r*ψ)/(1-r*ψ)) := by
    unfold limitTerm
    simpa only [div_eq_mul_inv,one_mul] using
      (((geo r hr).add (geo ψ hψ)).mul_right (1/2:ℝ)).sub (geo (r*ψ) hprod)
  rw [h.tsum_eq]
  have calc_value (x : ℝ) (hx : 0 < x) (hx' : x < 1) (ht : x^2+x=1) :
      (x/(1-x)+(-x)/(1-(-x)))/2-(x*(-x))/(1-x*(-x)) = 2/(1+2*x) := by
    have h1 : 1-x ≠ 0 := by linarith
    have h2 : 1- -x ≠ 0 := by linarith
    have h3 : 1-x* -x ≠ 0 := by nlinarith [sq_nonneg x]
    have h4 : 1+2*x ≠ 0 := by linarith
    field_simp [h1,h2,h3,h4,show (1+x^2) ≠ 0 by positivity,show (1+x) ≠ 0 by positivity]
    linear_combination 4*(x^2+x+1)*ht
  have hs : Real.sqrt 5=1+2*r := by dsimp [r]; linarith [goldenRatio_sub_goldenConj,goldenRatio_add_goldenConj]
  have ht : r^2+r=1 := by dsimp [r]; nlinarith [goldenConj_sq]
  have he : ψ= -r := by simp [r]
  rw [hs,he]
  exact calc_value r rp r₁ ht

private theorem normalized : Tendsto (fun n : ℕ => (a n:ℝ)/n.fib) atTop (𝓝 (2/Real.sqrt 5)) := by
  have hbound : Summable (fun k : ℕ => φ^2*r^(k+1)) := by
    have hh : |r| < 1 := by simpa only [abs_of_pos rp] using r₁
    have h₁ : Summable (fun k : ℕ => r^k) := summable_geometric_of_abs_lt_one hh
    have h₂ : Summable (fun k : ℕ => r^k*r) := h₁.mul_right r
    have h₃ : Summable (fun k : ℕ => φ^2*(r^k*r)) := h₂.mul_left (φ^2)
    exact h₃.congr (fun k => by rw [pow_succ r k])
  have h := tendsto_tsum_of_dominated_convergence hbound term_limit (Eventually.of_forall term_bound)
  simpa only [sum_identity,sum_limitTerms] using h

end OMA.S_oeis_a072523

open Filter Topology OMA.S_oeis_a072523 in
theorem OMA.solution : type_of% @OMA.S_oeis_a072523.main := by
  have hc : (2:ℝ)/Real.sqrt 5≠0 := by positivity
  constructor
  · simpa only [inv_div] using normalized.inv₀ hc
  · have hg := (tendsto_add_atTop_iff_nat 1).mpr normalized
    apply (tendsto_add_atTop_iff_nat 1).mp
    have hh := (hg.div normalized hc).mul tendsto_fib_succ_div_fib_atTop
    rw [div_self hc,one_mul] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hx : (n.fib:ℝ) ≠ 0 := by exact_mod_cast (Nat.fib_pos.mpr hn).ne'
    have hy : ((n+1).fib:ℝ) ≠ 0 := by exact_mod_cast (Nat.fib_pos.mpr (by omega : 0<n+1)).ne'
    simp only [Nat.add_sub_cancel,Pi.div_apply]
    field_simp
