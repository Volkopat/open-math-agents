import OMAStatements.S_oeis_a398920
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.BigOperators

namespace OMA.S_oeis_a398920

open Finset Filter Asymptotics

lemma sum_successors (q : ℕ) :
    (∑ m ∈ range q, ((m:ℝ)+1)) = (q:ℝ)*(q+1)/2 := by
  induction q with
  | zero => simp
  | succ q ih => rw [sum_range_succ,ih]; push_cast; ring

lemma triangle_estimate (N i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    0 ≤ (N:ℝ)^2 / (2*i*j) - triangle N i j ∧
    (N:ℝ)^2 / (2*i*j) - triangle N i j ≤ (N:ℝ)/i + (N:ℝ)/j := by
  let q := N/i
  let r := N%i
  let f := fun u : ℕ => (N-i*(u+1))/j
  have hi' : (0:ℝ) < i := by exact_mod_cast hi
  have hj' : (0:ℝ) < j := by exact_mod_cast hj
  have hr : (r:ℝ) ≤ i := by exact_mod_cast (Nat.mod_lt N hi).le
  have he : (r:ℝ) + i*q = N := by exact_mod_cast Nat.mod_add_div N i
  have point (u : ℕ) (hu : u ∈ range q) :
      (f u:ℝ)*j ≤ (N:ℝ)-i*((u:ℝ)+1) ∧
      (N:ℝ)-i*((u:ℝ)+1) ≤ ((f u:ℝ)+1)*j := by
    have hu' : u+1 ≤ N/i := mem_range.mp hu
    have hu'' : i*(u+1) ≤ N := by
      simpa [mul_comm] using (Nat.le_div_iff_mul_le hi).mp hu'
    have h1 := Nat.div_mul_le_self (N-i*(u+1)) j
    have h2 := Nat.lt_mul_div_succ (N-i*(u+1)) hj
    have h1' : (f u:ℝ)*j ≤ ((N-i*(u+1):ℕ):ℝ) := by exact_mod_cast h1
    have h2' : ((N-i*(u+1):ℕ):ℝ) ≤ ((f u:ℝ)+1)*j := by
      exact_mod_cast (show N-i*(u+1) ≤ (f u+1)*j by simpa [f,mul_comm] using h2.le)
    rw [Nat.cast_sub hu''] at h1' h2'
    push_cast at h1' h2'
    exact ⟨h1',h2'⟩
  have h1 := sum_le_sum (fun u hu => (point u hu).1)
  have h2 := sum_le_sum (fun u hu => (point u hu).2)
  have hW : (∑ u ∈ range q, (f u:ℝ)) = triangle N i j := by simp [triangle,q,f]
  have hS : (∑ u ∈ range q, ((N:ℝ)-i*((u:ℝ)+1))) =
      q*N - i*((q:ℝ)*(q+1)/2) := by
    rw [sum_sub_distrib, ← mul_sum, sum_successors]
    simp
  rw [← sum_mul, hW, hS] at h1
  rw [hS, ← sum_mul, sum_add_distrib, hW] at h2
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at h2
  have hr0 : (0:ℝ) ≤ r := by positivity
  have hq0 : (0:ℝ) ≤ q := by positivity
  have harea : (N:ℝ)^2 - 2*i*((q:ℝ)*N-i*(q*(q+1)/2)) = r^2 + i*(i*q) := by
    rw [← he]; ring
  have harea1 : (0:ℝ) ≤ r^2 + i*(i*q) := by positivity
  have harea2 : (r:ℝ)^2 + i*(i*q) ≤ i*N := by
    rw [← he]
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr)]
  have hqi : (i:ℝ)*q ≤ N := by linarith
  constructor
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ (by positivity)).2
    linarith only [harea,harea1,mul_le_mul_of_nonneg_left h1 hi'.le]
  · apply (sub_le_iff_le_add).2
    apply (div_le_iff₀ (by positivity)).2
    rw [show ((N:ℝ)/i + (N:ℝ)/j + triangle N i j)*(2*i*j) =
        2*N*j + 2*N*i + 2*i*((triangle N i j:ℝ)*j) by field_simp]
    linarith only [harea,harea2,mul_le_mul_of_nonneg_left h2 hi'.le,
      mul_le_mul_of_nonneg_right hqi hj'.le, mul_nonneg (by positivity : (0:ℝ) ≤ N) hi'.le]

noncomputable section

def weight (i : ℕ) : ℝ := ((i:ℝ)+1)⁻¹

def H (N : ℕ) : ℝ := ∑ i ∈ range N, weight i

def pairSum (N : ℕ) (f : ℕ → ℕ → ℝ) : ℝ :=
  ∑ j ∈ range N, ∑ i ∈ range j, f i j

lemma weight_bounds (i : ℕ) : 0 ≤ weight i ∧ weight i ≤ 1 := by
  unfold weight
  exact ⟨by positivity, inv_le_one_of_one_le₀ (by linarith only [(Nat.cast_nonneg i : (0:ℝ) ≤ i)])⟩

lemma harmonic_bounds (N : ℕ) (hN : 1 ≤ N) : Real.log N ≤ H N ∧ H N ≤ 1 + Real.log N := by
  have he : H N = (harmonic N:ℝ) := by simp [H,weight,harmonic]
  rw [he]
  exact ⟨by simpa using log_le_harmonic_floor (N:ℝ) (by positivity), harmonic_le_one_add_log N⟩

lemma pair_mono (N : ℕ) {f g : ℕ → ℕ → ℝ} (h : ∀ i j, f i j ≤ g i j) :
    pairSum N f ≤ pairSum N g := by
  exact sum_le_sum fun _ _ => sum_le_sum fun _ _ => h _ _

lemma pair_const_mul (N : ℕ) (c : ℝ) (f : ℕ → ℕ → ℝ) :
    pairSum N (fun i j => c * f i j) = c * pairSum N f := by
  simp only [pairSum, mul_sum]

lemma pair_sub (N : ℕ) (f g : ℕ → ℕ → ℝ) :
    pairSum N (fun i j => f i j-g i j) = pairSum N f-pairSum N g := by
  simp only [pairSum,sum_sub_distrib]

lemma square_identity (N : ℕ) :
    2*pairSum N (fun i j => weight i * weight j) + (∑ i ∈ range N, (weight i)^2) = (H N)^2 := by
  induction N with
  | zero => simp [pairSum,H]
  | succ N ih =>
    unfold pairSum H at *
    rw [sum_range_succ, sum_range_succ (f := fun i => (weight i)^2),
      sum_range_succ (f := weight), ← sum_mul]
    nlinarith only [ih]

lemma square_error (N : ℕ) :
    0 ≤ (H N)^2 - 2*pairSum N (fun i j => weight i * weight j) ∧
    (H N)^2 - 2*pairSum N (fun i j => weight i * weight j) ≤ H N := by
  rw [show (H N)^2 - 2*pairSum N (fun i j => weight i * weight j)
      = ∑ i ∈ range N, (weight i)^2 by linarith only [square_identity N]]
  exact ⟨sum_nonneg fun i _ => sq_nonneg _, sum_le_sum fun i _ => by
    have hh := weight_bounds i
    nlinarith [mul_nonneg hh.1 (sub_nonneg.mpr hh.2)]⟩

lemma sum_weights (N : ℕ) : pairSum N (fun i j => weight i + weight j) ≤ 2*N*H N := by
  unfold pairSum
  calc
    _ ≤ ∑ j ∈ range N, ∑ i ∈ range N, (weight i+weight j) := by
      apply sum_le_sum
      intro j hj
      exact sum_le_sum_of_subset_of_nonneg (range_mono (mem_range.mp hj).le)
        (fun i _ _ => add_nonneg (weight_bounds i).1 (weight_bounds j).1)
    _ = _ := by
      simp [sum_add_distrib, H, ← mul_sum]
      ring

lemma total_area_error (N : ℕ) :
    let area : ℝ := (N:ℝ)^2/2 * pairSum N (fun i j => weight i * weight j)
    0 ≤ area - (count N : ℝ) ∧ area - (count N : ℝ) ≤ 2*(N:ℝ)^2*H N := by
  dsimp only
  let f := fun i j : ℕ => (N:ℝ)^2/2*(weight i*weight j)
  let g := fun i j : ℕ => (triangle N (i+1) (j+1) : ℝ)
  have hp (i j : ℕ) : 0 ≤ f i j - g i j ∧ f i j - g i j ≤ (N:ℝ)*(weight i+weight j) := by
    have hh := triangle_estimate N (i+1) (j+1) (by omega) (by omega)
    simp only [Nat.cast_add_one] at hh
    simpa only [f,g,weight,div_eq_mul_inv,mul_inv_rev,mul_add,mul_assoc,mul_left_comm,mul_comm] using hh
  have hf : pairSum N f = (N:ℝ)^2/2 * pairSum N (fun i j => weight i * weight j) :=
    pair_const_mul .. 
  have hg : pairSum N g = (count N : ℝ) := by simp [pairSum,g,count]
  rw [← hf, ← hg, ← pair_sub]
  constructor
  · exact sum_nonneg fun j _ => sum_nonneg fun i _ => (hp i j).1
  · calc
      _ ≤ pairSum N (fun i j => (N:ℝ)*(weight i+weight j)) := pair_mono N fun i j => (hp i j).2
      _ = (N:ℝ)*pairSum N (fun i j => weight i+weight j) := pair_const_mul .. 
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (sum_weights N) (by positivity : (0:ℝ) ≤ N)
        linarith only [hh]

theorem solution :
    (fun N : ℕ => (count N : ℝ) - (N:ℝ)^2 * (Real.log N)^2 / 4)
      =O[atTop] (fun N : ℕ => (N:ℝ)^2 * Real.log N) := by
  apply Asymptotics.IsBigO.of_bound 6
  have hl := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hl,eventually_ge_atTop 1] with N hL hN
  change 1 ≤ Real.log N at hL
  have hh := harmonic_bounds N hN
  have hS := square_error N
  have hA := total_area_error N
  dsimp only at hA
  have hH : 0 ≤ H N := by linarith
  have hdiff : 0 ≤ (H N)^2-(Real.log N)^2 ∧ (H N)^2-(Real.log N)^2 ≤ 2*H N := by
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hh.1) (by linarith : 0 ≤ H N+Real.log N)]
    · nlinarith [mul_nonneg (by linarith : 0 ≤ 1-(H N-Real.log N)) (by linarith : 0 ≤ H N+Real.log N)]
  change ‖(count N:ℝ) - (N:ℝ)^2 * (Real.log N)^2 / 4‖ ≤ 6 * ‖(N:ℝ)^2 * Real.log N‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg (N:ℝ)) (show 0 ≤ Real.log N by linarith))]
  apply abs_le.mpr
  have hn2 : 0 ≤ (N:ℝ)^2 := sq_nonneg _
  have U := mul_le_mul_of_nonneg_left hS.2 hn2
  have V := mul_nonneg hn2 hS.1
  have W := mul_le_mul_of_nonneg_left hdiff.2 hn2
  have Z := mul_nonneg hn2 hdiff.1
  have T := mul_le_mul_of_nonneg_left (by linarith : H N ≤ 2*Real.log N) hn2
  constructor <;> linarith only [U,V,W,Z,T,hA.1,hA.2]

end

/-- The four original positive variables in the Diophantine inequality. -/
structure Quadruple (N : ℕ) where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  ha : 0<a
  hb : 0<b
  hc : 0<c
  hd : 0<d
  bound : a*b + b*c + c*d ≤ N

lemma quad_ext_val {N : ℕ} {x y : Quadruple N} (ha : x.a=y.a) (hb : x.b=y.b)
    (hc : x.c=y.c) (hd : x.d=y.d) : x=y := by
  cases x
  cases y
  congr

abbrev Indices (N : ℕ) :=
  (j : Fin N) × (i : Fin j.val) × (u : Fin (N/(i.val+1))) ×
    Fin ((N-(i.val+1)*(u.val+1))/(j.val+1))

def indicesToQuad {N : ℕ} : Indices N → Quadruple N
  | ⟨j,i,u,v⟩ => by
    have hu := (Nat.le_div_iff_mul_le (Nat.succ_pos i.val)).mp u.isLt
    have hv := (Nat.le_div_iff_mul_le (Nat.succ_pos j.val)).mp v.isLt
    change (u.val+1)*(i.val+1) ≤ N at hu
    change (v.val+1)*(j.val+1) ≤ N-(i.val+1)*(u.val+1) at hv
    have hi := i.isLt
    refine ⟨u.val+1,i.val+1,v.val+1,j.val-i.val,by omega,by omega,by omega,by omega,?_⟩
    have hb : i.val+1+(j.val-i.val)=j.val+1 := by omega
    calc
      _ = (i.val+1)*(u.val+1)+(v.val+1)*(i.val+1+(j.val-i.val)) := by ring
      _ ≤ N := by rw [hb];rw [mul_comm] at hu; omega

def quadToIndices {N : ℕ} (x : Quadruple N) : Indices N := by
  obtain ⟨a,b,c,d,ha,hb,hc,hd,h⟩ := x
  have H : b*a+c*(b+d)≤N := by nlinarith only [h]
  have h1 : b+d≤c*(b+d) := Nat.le_mul_of_pos_left _ hc
  have h2 : b*a≤N := by omega
  have jpos : 0<b+d := by omega
  let j : Fin N := ⟨b+d-1,by omega⟩
  let i : Fin j.val := ⟨b-1,by dsimp [j];omega⟩
  have hi : i.val+1=b := by dsimp [i];omega
  have hj : j.val+1=b+d := by dsimp [j];omega
  let u : Fin (N/(i.val+1)) := ⟨a-1,by
    rw [hi]
    have h' := (Nat.le_div_iff_mul_le hb).mpr (by simpa [mul_comm] using h2 : a*b≤N)
    omega⟩
  have hu : u.val+1=a := by dsimp [u];omega
  refine ⟨j,i,u,⟨c-1,?_⟩⟩
  rw [hu,hi,hj]
  have h' : c ≤ (N-b*a)/(b+d) :=
    (Nat.le_div_iff_mul_le jpos).mpr (by omega)
  omega

lemma index_ext_val {N : ℕ} {x y : Indices N} (hj : x.1.val=y.1.val)
    (hi : x.2.1.val=y.2.1.val) (hu : x.2.2.1.val=y.2.2.1.val)
    (hv : x.2.2.2.val=y.2.2.2.val) : x=y := by
  obtain ⟨j,i,u,v⟩ := x
  obtain ⟨k,l,w,z⟩ := y
  have he : j=k := Fin.ext hj
  subst k
  have he : i=l := Fin.ext hi
  subst l
  have he : u=w := Fin.ext hu
  subst w
  have he : v=z := Fin.ext hv
  subst z
  rfl

def quadEquiv (N : ℕ) : Indices N ≃ Quadruple N where
  toFun := indicesToQuad
  invFun := quadToIndices
  left_inv := by
    rintro ⟨⟨j,hj⟩,⟨i,hi⟩,⟨u,hu⟩,⟨v,hv⟩⟩
    change i<j at hi
    apply index_ext_val <;> (dsimp [indicesToQuad,quadToIndices] <;> omega)
  right_inv := by
    rintro ⟨a,b,c,d,ha,hb,hc,hd,hh⟩
    apply quad_ext_val <;> (dsimp [indicesToQuad,quadToIndices] <;> omega)

theorem count_original_quadruples (N : ℕ) : Nat.card (Quadruple N) = count N := by
  rw [← Nat.card_congr (quadEquiv N),Nat.card_eq_fintype_card]
  unfold count triangle Indices
  simp only [Fintype.card_sigma,Fintype.card_fin]
  rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ i ∈ range j, ∑ u ∈ range (N/(i+1)), (N-(i+1)*(u+1))/(j+1))]
  apply sum_congr rfl
  intro j _
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ u ∈ range (N/(i+1)), (N-(i+1)*(u+1))/(j.val+1))]
  apply sum_congr rfl
  intro i _
  exact Fin.sum_univ_eq_sum_range (fun u => (N-(i.val+1)*(u+1))/(j.val+1)) _

theorem original_quadruples_asymptotic :
    (fun N : ℕ => (Nat.card (Quadruple N) : ℝ) - (N:ℝ)^2 * (Real.log N)^2 / 4)
      =O[atTop] (fun N : ℕ => (N:ℝ)^2 * Real.log N) := by
  simpa only [count_original_quadruples] using solution

end OMA.S_oeis_a398920

theorem OMA.solution : type_of% @OMA.S_oeis_a398920.main :=
  OMA.S_oeis_a398920.solution
