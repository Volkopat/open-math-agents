import FormalConjectures.ErdosProblems.«1132»
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Lagrange

section
-- Sol's definitions, and their agreement with the upstream ones
noncomputable def Erdos1132Proof.lagrangeBasisL (n : ℕ) (x : ℕ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  (Lagrange.basis (Finset.range n) x k).eval t

noncomputable def Erdos1132Proof.lebesgueFunctionL (n : ℕ) (x : ℕ → ℝ) (t : ℝ) : ℝ :=
  Finset.sum (Finset.range n) fun k => |Erdos1132Proof.lagrangeBasisL n x k t|

theorem Erdos1132Proof.lebesgueFunction_eq :
    Erdos1132.lebesgueFunction = Erdos1132Proof.lebesgueFunctionL := by
  funext n x t
  unfold Erdos1132.lebesgueFunction Erdos1132Proof.lebesgueFunctionL
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold Erdos1132.lagrangeBasis Erdos1132Proof.lagrangeBasisL
  simp only [Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rw [div_eq_mul_inv, mul_comm]
end

section
-- InterpTools
open Finset Filter Polynomial
open scoped BigOperators

namespace Erdos1132Proof

noncomputable def W (x : ℕ → ℝ) (s : Finset ℕ) (t : ℝ) := ∏ k ∈ s, |t - x k|
noncomputable def D (x : ℕ → ℝ) (n k : ℕ) := W x ((range n).erase k) (x k)

theorem W_nonneg (x : ℕ → ℝ) (s : Finset ℕ) (t : ℝ) : 0 ≤ W x s t :=
  prod_nonneg fun _ _ => abs_nonneg _

theorem W_pos {x : ℕ → ℝ} {s : Finset ℕ} {t : ℝ} (h : ∀ k ∈ s, t ≠ x k) :
    0 < W x s t := prod_pos fun k hk => abs_pos.mpr (sub_ne_zero.mpr (h k hk))

theorem D_pos {x : ℕ → ℝ} (hx : Function.Injective x) (n k : ℕ) : 0 < D x n k :=
  W_pos fun _ hi => fun h => (mem_erase.mp hi).1 (hx h).symm

theorem W_succ (x : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    W x (range (n + 1)) t = W x (range n) t * |t - x n| := by
  simp [W, prod_range_succ]

theorem D_split (x : ℕ → ℝ) {p n k : ℕ} (hk : k < p) (hp : p ≤ n) :
    D x n k = D x p k * W x (Ico p n) (x k) := by
  have h : (range n).erase k = (range p).erase k ∪ Ico p n := by
    ext i
    simp only [mem_erase, mem_range, mem_union, mem_Ico]
    omega
  unfold D W
  rw [h, prod_union]
  exact disjoint_left.mpr (by simp only [mem_erase, mem_range, mem_Ico]; omega)

theorem abs_basis_eq (x : ℕ → ℝ) (n k : ℕ) (t : ℝ) :
    |Erdos1132Proof.lagrangeBasisL n x k t| = W x ((range n).erase k) t / D x n k := by
  simp only [Erdos1132Proof.lagrangeBasisL, Lagrange.basis, eval_prod, Lagrange.basisDivisor,
    eval_mul, eval_C, eval_sub, eval_X, prod_mul_distrib, abs_mul, abs_inv, abs_prod,
    W, D, prod_inv_distrib, div_eq_mul_inv]
  exact mul_comm ..

theorem abs_basis_mul (x : ℕ → ℝ) (hx : Function.Injective x) {n k : ℕ}
    (hk : k < n) (t : ℝ) :
    |Erdos1132Proof.lagrangeBasisL n x k t| * (|t - x k| * D x n k) = W x (range n) t := by
  rw [abs_basis_eq]
  simp only [W]
  rw [← mul_prod_erase _ _ (mem_range.mpr hk)]
  field_simp [(D_pos hx n k).ne']

theorem continuous_W (x : ℕ → ℝ) (s : Finset ℕ) : Continuous (W x s) := by
  unfold W
  fun_prop

theorem continuous_L (x : ℕ → ℝ) (n : ℕ) :
    Continuous (Erdos1132Proof.lebesgueFunctionL n x) := by
  unfold Erdos1132Proof.lebesgueFunctionL Erdos1132Proof.lagrangeBasisL
  exact continuous_finsetSum _ fun k _ => (Polynomial.continuous _).abs

theorem eval_le_L (x : ℕ → ℝ) (hx : Function.Injective x) {n : ℕ}
    (P : ℝ[X]) (hP : P.degree < n) (t B : ℝ)
    (hB : ∀ k < n, |P.eval (x k)| ≤ B) :
    |P.eval t| ≤ B * Erdos1132Proof.lebesgueFunctionL n x t := by
  have he := Lagrange.eq_interpolate (s := range n) hx.injOn (f := P) (by simpa using hP)
  have h := congrArg (eval t) he
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C] at h
  calc
    _ = |∑ k ∈ range n, P.eval (x k) * Erdos1132Proof.lagrangeBasisL n x k t| := congrArg abs h
    _ ≤ ∑ k ∈ range n, |P.eval (x k) * Erdos1132Proof.lagrangeBasisL n x k t| := Finset.abs_sum_le_sum_abs ..
    _ ≤ _ := by
      rw [Erdos1132Proof.lebesgueFunctionL, mul_sum]
      exact sum_le_sum fun k hk => by rw [abs_mul]; gcongr; exact hB k (mem_range.mp hk)

noncomputable def angleMap (a : ℝ) : ℝ := Real.cos (Real.pi * a)

theorem angleMap_mem (a : ℝ) : angleMap a ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem angleMap_strictAnti : StrictAntiOn angleMap (Set.Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  apply Real.strictAntiOn_cos
  · exact ⟨mul_nonneg Real.pi_pos.le ha.1, mul_le_of_le_one_right Real.pi_pos.le ha.2⟩
  · exact ⟨mul_nonneg Real.pi_pos.le hb.1, mul_le_of_le_one_right Real.pi_pos.le hb.2⟩
  · exact mul_lt_mul_of_pos_left hab Real.pi_pos

theorem angleMap_interior {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    angleMap a ∈ Set.Ioo (-1 : ℝ) 1 := by
  constructor
  · simpa [angleMap] using angleMap_strictAnti (Set.Ioo_subset_Icc_self ha)
      (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) ha.2
  · simpa [angleMap] using angleMap_strictAnti (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
      (Set.Ioo_subset_Icc_self ha) ha.1

theorem angle_exists {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ a ∈ Set.Icc (0 : ℝ) 1, angleMap a = x := by
  refine ⟨Real.arccos x / Real.pi, ⟨by positivity [Real.arccos_nonneg x], ?_⟩, ?_⟩
  · exact (div_le_iff₀ Real.pi_pos).2 (by simpa using Real.arccos_le_pi x)
  · simpa [angleMap, mul_div_cancel₀ _ Real.pi_ne_zero] using Real.cos_arccos hx.1 hx.2

theorem angleMap_deriv (a : ℝ) : HasDerivAt angleMap (- (Real.pi * Real.sin (Real.pi * a))) a := by
  have h := (Real.hasDerivAt_cos (Real.pi * a)).comp a ((hasDerivAt_id a).const_mul Real.pi)
  change HasDerivAt (fun w => Real.cos (Real.pi * w)) _ a
  rw [mul_comm Real.pi (Real.sin (Real.pi*a))]
  simpa [Function.comp_def] using h

theorem angleMap_slope {a b l u : ℝ} (hab : a < b)
    (h : ∀ z ∈ Set.Ioo a b, l ≤ Real.pi * Real.sin (Real.pi * z) ∧
                             Real.pi * Real.sin (Real.pi * z) ≤ u) :
    l * (b - a) ≤ angleMap a - angleMap b ∧ angleMap a - angleMap b ≤ u * (b - a) := by
  obtain ⟨c, hc, he⟩ := exists_deriv_eq_slope angleMap hab
    (by unfold angleMap; fun_prop) (fun z _ => (angleMap_deriv z).differentiableAt.differentiableWithinAt)
  rw [(angleMap_deriv c).deriv] at he
  have h₁ := (eq_div_iff (sub_ne_zero.mpr hab.ne')).mp he
  constructor
  · linarith [mul_le_mul_of_nonneg_right (h c hc).1 (sub_nonneg.mpr hab.le)]
  · linarith [mul_le_mul_of_nonneg_right (h c hc).2 (sub_nonneg.mpr hab.le)]

theorem abs_sub_le_two {a b : ℝ} (ha : a ∈ Set.Icc (-1 : ℝ) 1)
    (hb : b ∈ Set.Icc (-1 : ℝ) 1) : |a-b| ≤ 2 := abs_le.mpr ⟨by linarith [ha.1,hb.2], by linarith [ha.2,hb.1]⟩

noncomputable def peak (a : ℝ) : ℝ[X] := 1 - C (1 / 4) * (X - C a)^2

theorem degree_peak (a : ℝ) : (peak a).natDegree ≤ 2 := by
  unfold peak
  refine (natDegree_sub_le _ _).trans ?_
  simp only [natDegree_one, zero_le, sup_of_le_right]
  refine natDegree_mul_le.trans ?_
  simp [natDegree_pow]

theorem eval_peak (a t : ℝ) : (peak a).eval t = 1 - (t-a)^2/4 := by
  simp [peak]; ring

theorem peak_exp {a t : ℝ} (ha : a ∈ Set.Icc (-1 : ℝ) 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (m : ℕ) :
    |((peak a)^m).eval t| ≤ Real.exp (- ((m : ℝ) * (t-a)^2/4)) := by
  rw [eval_pow, eval_peak]
  have hab := abs_sub_le_two ht ha
  have hsq : (t-a)^2 ≤ 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (t-a)]
  have hq : 0 ≤ 1 - (t-a)^2/4 := by linarith
  rw [abs_of_nonneg (pow_nonneg hq _), show Real.exp (-( (m : ℝ)*(t-a)^2/4)) =
      (Real.exp (-(t-a)^2/4))^m by rw [← Real.exp_nat_mul]; congr 1; ring]
  apply pow_le_pow_left₀ hq
  linarith [Real.add_one_le_exp (-(t-a)^2/4)]
end Erdos1132Proof
end

section
-- InterpGrid
open Finset Filter Polynomial MeasureTheory
open scoped BigOperators Topology ENNReal

namespace Erdos1132Proof

theorem angleMap_lower {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) : 2 * (a-b)^2 ≤ |angleMap a - angleMap b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm, ← neg_sub, neg_sq]
    exact this hb ha (by linarith)
  have hs₁ : b-a ≤ Real.sin (Real.pi * (b-a)/2) := by
    have h := Real.mul_le_sin (x := Real.pi * (b-a)/2) (by positivity [sub_nonneg.mpr hab])
      (by nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left (show b-a ≤ 1 by linarith [ha.1,hb.2]) Real.pi_pos.le])
    convert h using 1
    field_simp [Real.pi_ne_zero]
  have hs₂ : b-a ≤ Real.sin (Real.pi * (b+a)/2) := by
    by_cases h : b+a ≤ 1
    · have H := Real.mul_le_sin (x := Real.pi * (b+a)/2) (by positivity [ha.1, hb.1])
        (by linarith [mul_le_mul_of_nonneg_left h Real.pi_pos.le])
      rw [show 2 / Real.pi * (Real.pi * (b + a) / 2) = b+a by field_simp] at H
      linarith [ha.1]
    · have H := Real.mul_le_sin (x := Real.pi * (2-(b+a))/2)
        (by positivity [show 0 ≤ 2-(b+a) by linarith [ha.2, hb.2]])
        (by nlinarith [mul_le_mul_of_nonneg_left (show 2-(b+a) ≤ 1 by linarith) Real.pi_pos.le])
      rw [show 2 / Real.pi * (Real.pi * (2 - (b + a)) / 2) = 2-(b+a) by field_simp,
        show Real.pi * (2-(b+a))/2 = Real.pi - Real.pi * (b+a)/2 by ring,
        Real.sin_pi_sub] at H
      linarith [hb.2]
  have hcos : angleMap a - angleMap b =
      2 * Real.sin (Real.pi * (b+a)/2) * Real.sin (Real.pi * (b-a)/2) := by
    unfold angleMap
    rw [Real.cos_sub_cos]
    rw [show (Real.pi*a + Real.pi*b)/2 = Real.pi*(b+a)/2 by ring,
        show (Real.pi*a - Real.pi*b)/2 = -(Real.pi*(b-a)/2) by ring, Real.sin_neg]
    ring
  rw [abs_of_nonneg (sub_nonneg.mpr (angleMap_strictAnti.antitoneOn ha hb hab)), hcos]
  rw [show 2*(a-b)^2=(2*(b-a))*(b-a) by ring]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hs₂ (by norm_num)) hs₁
    (sub_nonneg.mpr hab) (mul_nonneg (by norm_num) ((sub_nonneg.mpr hab).trans hs₂))

noncomputable def mesh (n : ℕ) : ℝ := (n : ℝ) ^ (-(1/8 : ℝ))

theorem mesh_pos {n : ℕ} (hn : 0 < n) : 0 < mesh n := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem mesh_anti {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) : mesh b ≤ mesh a :=
  Real.rpow_le_rpow_of_nonpos (by exact_mod_cast ha) (by exact_mod_cast hab) (by norm_num)

theorem eventually_peak_small {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^4 * Real.exp (-(c*n) * (mesh n)^4) < 1 := by
  have H : Tendsto (fun v : ℝ => v ^ (8 : ℝ) * Real.exp (-(c*v))) atTop (𝓝 0) := by
    simpa only [neg_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 8 c hc
  have H' := H.comp ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).comp
    tendsto_natCast_atTop_atTop)
  filter_upwards [H'.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)), eventually_ge_atTop 1]
    with n hn h₁
  have hp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  change ((n : ℝ) ^ (1/2 : ℝ)) ^ (8 : ℝ) * Real.exp (-(c * (n:ℝ) ^ (1/2 : ℝ))) < 1 at hn
  rw [← Real.rpow_mul hp.le, show (1/2:ℝ)*8 = (4:ℕ) by norm_num, Real.rpow_natCast] at hn
  have he : - (c * n) * mesh n ^ 4 = -(c*(n:ℝ) ^ (1/2 : ℝ)) := by
    unfold mesh
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le, show -(1/8:ℝ) * (4:ℕ) = -(1/2:ℝ) by norm_num]
    rw [neg_mul, mul_assoc]
    congr 1
    nth_rw 1 [← Real.rpow_one (n:ℝ)]
    rw [← Real.rpow_add hp]
    norm_num
  rwa [he]

theorem eventually_mesh_cover {x θ : ℕ → ℝ} (hx : Function.Injective x)
    (hθ : ∀ k, θ k ∈ Set.Icc (0 : ℝ) 1) (hmap : ∀ k, angleMap (θ k) = x k)
    {E : Set ℝ} (hE : E ⊆ Set.Icc 0 1)
    (hL : ∀ᶠ n : ℕ in atTop, ∀ a ∈ E,
      Erdos1132Proof.lebesgueFunctionL n x (angleMap a) ≤ Real.log n) :
    ∀ᶠ n : ℕ in atTop, ∀ a ∈ E, ∃ k < n, |θ k-a| < mesh n := by
  filter_upwards [hL, eventually_peak_small (by norm_num : (0:ℝ)<1/8), eventually_ge_atTop 8]
    with n hLn hsmall hn a ha
  by_contra! h
  let m := n/4
  have hdeg : ((peak (angleMap a))^m).degree < (n : WithBot ℕ) := by
    by_cases hz : (peak (angleMap a))^m = 0
    · simp [hz]
    apply (natDegree_lt_iff_degree_lt hz).mp
    rw [natDegree_pow]
    have := Nat.mul_le_mul_left m (degree_peak (angleMap a))
    dsimp [m] at *; omega
  have hm : (n:ℝ)/8 ≤ (m:ℝ) := (div_le_iff₀ (by norm_num)).mpr (by
    exact_mod_cast (show n ≤ m*8 by dsimp [m]; omega))
  have hh : ∀ k < n, |((peak (angleMap a))^m).eval (x k)| ≤
      Real.exp (-((1/8 : ℝ)*n)*(mesh n)^4) := by
    intro k hk
    rw [← hmap k]
    apply (peak_exp (angleMap_mem a) (angleMap_mem (θ k)) m).trans
    apply Real.exp_le_exp.mpr
    have H := angleMap_lower (hθ k) (hE ha)
    have hs : 2 * (mesh n)^2 ≤ |angleMap (θ k)-angleMap a| := by
      rw [← sq_abs] at H
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mesh_pos (by omega)).le (h k hk) 2)
        (by norm_num)).trans H
    have hs' : 4 * mesh n ^ 4 ≤ (angleMap (θ k)-angleMap a)^2 := by
      calc _ = (2 * (mesh n)^2)^2 := by ring
           _ ≤ _ := by rw [← sq_abs (angleMap (θ k)-angleMap a)]; exact pow_le_pow_left₀ (by positivity) hs 2
    have hs'' := mul_le_mul hm hs' (by positivity) (Nat.cast_nonneg m)
    linarith
  have hp := eval_le_L x hx _ hdeg (angleMap a) _ hh
  rw [eval_pow, eval_peak, sub_self, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero, one_pow,
    abs_one] at hp
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog := Real.log_le_self (Nat.cast_nonneg n)
  have he : (n:ℝ) ≤ (n:ℝ)^4 := by nlinarith [pow_le_pow_right₀ hnR (show 1 ≤ 4 by decide)]
  have := mul_le_mul_of_nonneg_left ((hLn a ha).trans (hlog.trans he))
    (Real.exp_pos (-((1/8 : ℝ)*n)*(mesh n)^4)).le
  rw [mul_comm] at hsmall
  linarith

noncomputable def grid (m j : ℕ) (u : ℝ) : ℝ :=
  ((j : ℝ) + if Even j then u else 1-u) / m

theorem grid_in_cell {m j : ℕ} (hj : j < m) {u : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    grid m j u ∈ Set.Ioo ((j:ℝ)/m) ((j+1:ℝ)/m) := by
  have hm : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold grid
  split <;> constructor <;> gcongr <;> linarith [hu.1,hu.2]

theorem grid_mem {m j : ℕ} (hj : j < m) {u : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    grid m j u ∈ Set.Ioo (0:ℝ) 1 := by
  obtain ⟨h₁,h₂⟩ := grid_in_cell hj hu
  have hm : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  exact ⟨(by positivity : 0 ≤ (j:ℝ)/m).trans_lt h₁, h₂.trans_le <|
    (div_le_one hm).2 (by exact_mod_cast (show j+1 ≤ m by omega))⟩

theorem grid_inj {m : ℕ} {u : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    Set.InjOn (fun j => angleMap (grid m j u)) (range m : Set ℕ) := by
  intro i hi j hj h
  simp only [coe_range, Set.mem_Iio] at hi hj
  have eq := angleMap_strictAnti.injOn (Set.Ioo_subset_Icc_self (grid_mem hi hu))
    (Set.Ioo_subset_Icc_self (grid_mem hj hu)) h
  have hh : ∀ a b : ℕ, a < m → b < m → a < b → grid m a u < grid m b u := by
    intro a b ha hb hab
    exact (grid_in_cell ha hu).2.trans <| (div_le_div_of_nonneg_right
      (by exact_mod_cast (Nat.succ_le_of_lt hab)) (Nat.cast_nonneg m)).trans_lt (grid_in_cell hb hu).1
  exact le_antisymm (le_of_not_gt (fun H => (hh j i hj hi H).ne eq.symm))
    (le_of_not_gt (fun H => (hh i j hi hj H).ne eq))

open Polynomial.Chebyshev in
theorem grid_eval {m j : ℕ} (hj : j < m) (u : ℝ) :
    (T ℝ (m:ℤ)).eval (angleMap (grid m j u)) = Real.cos (Real.pi * u) := by
  have hm : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [angleMap, T_real_cos, Int.cast_natCast, grid,
    show (m:ℝ) * (Real.pi * (((j:ℝ) + if Even j then u else 1-u) / m)) =
      (j:ℝ)*Real.pi + Real.pi * (if Even j then u else 1-u) by field_simp]
  split_ifs with he
  · obtain ⟨d, hd⟩ := he
    rw [hd, Nat.cast_add, show ((d:ℝ)+d)*Real.pi + Real.pi*u = Real.pi*u + (d:ℝ)*(2*Real.pi) by ring]
    exact Real.cos_add_nat_mul_two_pi _ _
  · have ho : Odd j := Nat.not_even_iff_odd.mp he
    obtain ⟨d, hd⟩ := ho
    rw [hd, Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_one,
      show (2*(d:ℝ)+1)*Real.pi + Real.pi*(1-u) = -(Real.pi*u) + ((d+1:ℕ):ℝ)*(2*Real.pi) by push_cast; ring,
      Real.cos_add_nat_mul_two_pi, Real.cos_neg]

open Polynomial.Chebyshev in
theorem grid_poly {m : ℕ} (hmp : 0 < m) {u : ℝ} (hmu : u ∈ Set.Ioo (0:ℝ) 1) :
    T ℝ (m:ℤ) - C (Real.cos (Real.pi*u)) =
      C ((2:ℝ)^(m-1)) * ∏ i ∈ range m, (X - C (angleMap (grid m i u))) := by
  let y := fun j => angleMap (grid m j u)
  let P := T ℝ (m:ℤ) - C (Real.cos (Real.pi*u))
  let Q : ℝ[X] := ∏ i ∈ range m, (X - C (y i))
  change P = C ((2:ℝ)^(m-1)) * Q
  have hT : (T ℝ (m:ℤ)).natDegree = m := by simp [natDegree_T]
  have hT' : (T ℝ (m:ℤ)).degree = (m : WithBot ℕ) := by simp [degree_T]
  have hPm : P.natDegree = m := by
    exact (natDegree_sub_eq_left_of_natDegree_lt (by simpa [hT] using hmp)).trans hT
  have hPnz : P ≠ 0 := by intro e; simp [e] at hPm; omega
  have hlead : P.leadingCoeff = (2:ℝ)^(m-1) := by
    rw [show P.leadingCoeff = (T ℝ (m:ℤ)).leadingCoeff by
      unfold P; apply leadingCoeff_sub_of_degree_lt
      rw [hT']; exact lt_of_le_of_lt degree_C_le (by exact_mod_cast hmp)]
    simp [leadingCoeff_T]
  have hQ : Q.Monic := monic_prod_X_sub_C y _
  have hQm : Q.natDegree = m := by simp [Q]
  apply eq_of_degree_sub_lt_of_eval_index_eq (range m) (grid_inj hmu)
  · have hC : (C ((2:ℝ)^(m-1)) * Q).natDegree = m := by rw [natDegree_C_mul (by positivity),hQm]
    have hcl : (C ((2:ℝ)^(m-1)) * Q).leadingCoeff = (2:ℝ)^(m-1) := by
      simp [leadingCoeff_mul, hQ.leadingCoeff]
    have hPdeg : P.degree = (m : WithBot ℕ) := by rw [degree_eq_natDegree hPnz, hPm]
    rw [card_range, ← hPdeg]
    apply degree_sub_lt_left _ hPnz (hlead.trans hcl.symm)
    rw [hPdeg, degree_eq_natDegree (mul_ne_zero (by simp) hQ.ne_zero), hC]
  · intro i hi
    change P.eval (y i) = _
    unfold P
    rw [eval_sub, eval_C, show (T ℝ (m:ℤ)).eval (y i) = _ from grid_eval (mem_range.mp hi) u,
      sub_self, eval_mul, eval_C]
    change 0 = _ * Q.eval (y i)
    suffices Q.eval (y i) = 0 by simp [this]
    simp only [Q, eval_prod, eval_sub, eval_X, eval_C]
    exact prod_eq_zero hi (sub_self _)

open Polynomial.Chebyshev in
theorem grid_denoms {m : ℕ} {u : ℝ} (hu : u ∈ Set.Icc (1/4 : ℝ) (3/4)) :
    ∀ j < m, (m:ℝ)/2^(m:ℕ) ≤ D (fun j => angleMap (grid m j u)) m j := by
  intro j hj
  let y := fun j => angleMap (grid m j u)
  let P := T ℝ (m:ℤ) - C (Real.cos (Real.pi*u))
  have hmu : u ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hmp : 0 < m := by omega
  have hprod : P = C ((2:ℝ)^(m-1)) * ∏ i ∈ range m, (X - C (y i)) := grid_poly hmp hmu
  have hd₁ : |P.derivative.eval (y j)| = 2^(m-1) * D y m j := by
    rw [hprod, ← mul_prod_erase _ _ (mem_range.mpr hj), ← mul_assoc, derivative_mul,
      eval_add, eval_mul, derivative_mul]
    simp only [derivative_C, zero_mul, mul_zero, derivative_sub, derivative_X, sub_zero, zero_add,
      mul_one, eval_mul, eval_C, eval_sub, eval_X, sub_self, add_zero, abs_mul, abs_of_nonneg
        (show 0 ≤ (2:ℝ)^(m-1) by positivity), D, W, eval_prod, abs_prod]
  have hd₂ : (m:ℝ)/2 ≤ |P.derivative.eval (y j)| := by
    let z := Real.pi * grid m j u
    have hz : 0 < z ∧ z < Real.pi := by
      obtain ⟨h₁,h₂⟩ := grid_mem hj hmu
      exact ⟨mul_pos Real.pi_pos h₁, by nlinarith [mul_lt_mul_of_pos_left h₂ Real.pi_pos]⟩
    have H : (fun t : ℝ => (T ℝ (m:ℤ)).eval (Real.cos t)) = fun t => Real.cos ((m:ℝ)*t) := by
      ext t; simp [T_real_cos]
    have h := ((T ℝ (m:ℤ)).hasDerivAt (Real.cos z)).comp z (Real.hasDerivAt_cos z)
    change HasDerivAt (fun t => (T ℝ (m:ℤ)).eval (Real.cos t)) _ z at h
    rw [H] at h
    have h' := (Real.hasDerivAt_cos ((m:ℝ)*z)).comp z ((hasDerivAt_id z).const_mul (m:ℝ))
    have h'' := h.unique (by simpa [Function.comp_def] using h')
    have hc : Real.cos ((m:ℝ)*z) = Real.cos (Real.pi*u) := by
      rw [← Int.cast_natCast (R := ℝ) m, ← T_real_cos]
      exact grid_eval hj u
    have hs : (1/2:ℝ) ≤ |Real.sin ((m:ℝ)*z)| := by
      have hcu : |Real.cos (Real.pi*u)| ≤ Real.sqrt 2 / 2 := by
        apply abs_le.mpr
        constructor
        · have hh := Real.strictAntiOn_cos.antitoneOn
            (show Real.pi*u ∈ Set.Icc 0 Real.pi from ⟨by positivity [hmu.1],by nlinarith [Real.pi_pos,hmu.2]⟩)
            (show 3*Real.pi/4 ∈ Set.Icc 0 Real.pi from ⟨by positivity, by linarith [Real.pi_pos]⟩)
            (by nlinarith [mul_le_mul_of_nonneg_left hu.2 Real.pi_pos.le])
          rw [show 3*Real.pi/4 = Real.pi - Real.pi/4 by ring, Real.cos_pi_sub, Real.cos_pi_div_four] at hh
          linarith
        · have hh := Real.strictAntiOn_cos.antitoneOn
            (show Real.pi/4 ∈ Set.Icc 0 Real.pi from ⟨by positivity, by linarith [Real.pi_pos]⟩)
            (show Real.pi*u ∈ Set.Icc 0 Real.pi from ⟨by positivity [hmu.1],by nlinarith [Real.pi_pos,hmu.2]⟩)
            (by nlinarith [mul_le_mul_of_nonneg_left hu.1 Real.pi_pos.le])
          rwa [Real.cos_pi_div_four] at hh
      have hcs := pow_le_pow_left₀ (abs_nonneg _) hcu 2
      rw [sq_abs, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at hcs
      have Hs := Real.sin_sq_add_cos_sq ((m:ℝ)*z)
      rw [hc] at Hs
      nlinarith [sq_abs (Real.sin ((m:ℝ)*z)),abs_nonneg (Real.sin ((m:ℝ)*z))]
    have hh := congrArg abs h''
    simp only [abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) m)] at hh
    have hg : |(T ℝ (m:ℤ)).derivative.eval (Real.cos z)| * |Real.sin z| ≤
        |(T ℝ (m:ℤ)).derivative.eval (Real.cos z)| :=
      mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
    simp only [P, y, derivative_sub, derivative_C, sub_zero]
    change (m:ℝ)/2 ≤ |(T ℝ (m:ℤ)).derivative.eval (Real.cos z)|
    nlinarith [mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg m)]
  rw [hd₁] at hd₂
  rw [div_le_iff₀ (by positivity)]
  have hm : 2^m = (2:ℝ)^(m-1) * 2 := by
    conv_lhs => rw [show m = m-1+1 by omega, pow_succ]
  change (m:ℝ) ≤ D y m j * 2^m
  rw [hm]
  linarith only [hd₂]

open Polynomial.Chebyshev in
theorem grid_basis_bdd {m : ℕ} {u : ℝ} (hu : u ∈ Set.Icc (1/4 : ℝ) (3/4))
    {j : ℕ} (hj : j < m) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |Erdos1132Proof.lagrangeBasisL m (fun j => angleMap (grid m j u)) j t| ≤ 2*m := by
  let y := fun j => angleMap (grid m j u)
  let P := T ℝ (m:ℤ) - C (Real.cos (Real.pi*u))
  have hm : 0 < m := by omega
  have hmu : u ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have he : |P.eval t| = 2^(m-1) * W y (range m) t := by
    unfold P
    rw [grid_poly hm hmu, eval_mul, eval_C, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2:ℝ)^(m-1))]
    simp [y, W, eval_prod, abs_prod]
  have hder : ∀ z ∈ Set.Icc (-1:ℝ) 1, |P.derivative.eval z| ≤ (m:ℝ)^2 := by
    intro z hz
    simpa [P, derivative_T_eval_one] using abs_iterate_derivative_T_real_le (m:ℤ) 1 (abs_le.mpr hz)
  have hPv : P.eval (y j) = 0 := by simp [P, y, grid_eval hj]
  have hLip : |P.eval t| ≤ (m:ℝ)^2 * |t-y j| := by
    have hyy : y j ∈ Set.Icc (-1:ℝ) 1 := angleMap_mem _
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun z => P.eval z)
      (s := Set.Icc (-1:ℝ) 1)
      (fun z _ => (P.hasDerivAt z).differentiableAt)
      (fun z hz => by
        rw [(P.hasDerivAt z).deriv, Real.norm_eq_abs]
        exact hder z hz)
      (convex_Icc _ _) hyy ht
    simpa [Real.norm_eq_abs, hPv] using hh
  by_cases hty : t = y j
  · subst t
    rw [Erdos1132Proof.lagrangeBasisL, Lagrange.eval_basis_self (grid_inj hmu) (mem_range.mpr hj), abs_one]
    exact_mod_cast (show 1 ≤ 2*m by omega)
  · have hh : W y (range m) t = |t-y j| * W y ((range m).erase j) t := by
      unfold W; exact (mul_prod_erase _ _ (mem_range.mpr hj)).symm
    rw [he, hh] at hLip
    have hh₁ : 2^(m-1) * W y ((range m).erase j) t ≤ (m:ℝ)^2 := by
      apply le_of_mul_le_mul_right _ (abs_pos.mpr (sub_ne_zero.mpr hty))
      linarith only [hLip]
    change |Erdos1132Proof.lagrangeBasisL m y j t| ≤ _
    rw [abs_basis_eq, div_le_iff₀ ((div_pos (by exact_mod_cast hm) (by positivity)).trans_le
      (grid_denoms hu j hj))]
    have hh₂ := grid_denoms hu j hj
    have h2 := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^m)).mp hh₂
    have H : (2:ℝ)^m = 2^(m-1)*2 := by conv_lhs => rw [show m=m-1+1 by omega, pow_succ]
    rw [H] at h2
    change W y ((range m).erase j) t ≤ 2 * (m:ℝ) * D y m j
    apply le_of_mul_le_mul_left _ (show 0 < (2:ℝ)^(m-1) by positivity)
    nlinarith only [hh₁, mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg m)]

end Erdos1132Proof
end

section
-- InterpBlocks
open Finset Filter Polynomial
open scoped BigOperators Topology Matrix

namespace Erdos1132Proof

theorem prod_le_mean_pow {ι : Type*} [Fintype ι] {A : ℝ} (_hA : 0 ≤ A)
    (hι : 0 < Fintype.card ι) (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i)
    (hs : ∑ i, z i ≤ Fintype.card ι * A) : ∏ i, z i ≤ A ^ Fintype.card ι := by
  let n := Fintype.card ι
  have hn : 0 < (n:ℝ) := by exact_mod_cast hι
  have H := Real.geom_mean_le_arith_mean_weighted (univ : Finset ι) (fun _ => (n:ℝ)⁻¹) z
    (fun _ _ => inv_nonneg.mpr hn.le) (by simp [n, show (Fintype.card ι : ℝ) ≠ 0 from hn.ne'])
    (fun i _ => hz i)
  rw [Real.finsetProd_rpow _ _ (fun i _ => hz i), ← mul_sum] at H
  have H' : (∏ i, z i) ^ (n:ℝ)⁻¹ ≤ A := H.trans <| by
    rw [← div_eq_inv_mul, div_le_iff₀ hn, mul_comm]
    exact hs
  have HH := pow_le_pow_left₀ (Real.rpow_nonneg (prod_nonneg fun i _ => hz i) _) H' n
  rw [← Real.rpow_natCast, ← Real.rpow_mul (prod_nonneg fun i _ => hz i), inv_mul_cancel₀ hn.ne',
    Real.rpow_one] at HH
  exact HH

theorem det_sq_le {m : ℕ} (hm : 0 < m) (B : Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ i j, |B i j| ≤ 1) : B.det^2 ≤ (m:ℝ)^m := by
  let A := Bᴴ * B
  have hA : A.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self B
  have ht : A.trace ≤ (m:ℝ)*m := by
    unfold A Matrix.trace Matrix.diag
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
    calc
      _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, (1:ℝ) := by
        apply sum_le_sum; intro i _
        apply sum_le_sum; intro j _
        have hh := pow_le_pow_left₀ (abs_nonneg _) (hB j i) 2
        rwa [sq_abs, one_pow, sq] at hh
      _ = _ := by simp
  rw [hA.isHermitian.trace_eq_sum_eigenvalues] at ht
  have hp := prod_le_mean_pow (Nat.cast_nonneg m) (by simpa using hm)
    hA.isHermitian.eigenvalues hA.eigenvalues_nonneg (by simpa using ht)
  have he : A.det = ∏ i, hA.isHermitian.eigenvalues i := by
    simpa using hA.isHermitian.det_eq_prod_eigenvalues
  rw [← he] at hp
  simpa [A, Matrix.det_mul, Matrix.det_conjTranspose, sq] using hp

theorem angle_sep_le (a b : ℝ) : |angleMap a-angleMap b| ≤ Real.pi*|a-b| := by
  unfold angleMap
  exact (Real.abs_cos_sub_cos_le _ _).trans_eq (by rw [← mul_sub, abs_mul, abs_of_pos Real.pi_pos])

theorem prod_D_succ (x : ℕ → ℝ) (m : ℕ) :
    ∏ k ∈ range (m+1), D x (m+1) k = (∏ k ∈ range m, D x m k) * W x (range m) (x m)^2 := by
  rw [prod_range_succ]
  have he : ∀ k ∈ range m, D x (m+1) k = D x m k * |x k - x m| := by
    intro k hk
    rw [D_split x (mem_range.mp hk) (Nat.le_succ _)]
    simp [W, Nat.Ico_succ_singleton]
  rw [prod_congr rfl he, prod_mul_distrib]
  rw [show (∏ k ∈ range m, |x k - x m|) = W x (range m) (x m) by simp [W, abs_sub_comm]]
  rw [show D x (m+1) m = W x (range m) (x m) by
    simp [D, range_add_one]]
  ring

theorem vandermonde_sq (x : ℕ → ℝ) (m : ℕ) :
    (Matrix.vandermonde (fun i : Fin m => x i)).det ^ 2 = ∏ k ∈ range m, D x m k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_D_succ, ← ih]
    simp only [Matrix.det_vandermonde, Fin.prod_univ_castSucc (n := m)]
    have he : ∀ i : Fin m,
        (∏ j ∈ Ioi i.castSucc, (x ↑j - x ↑i.castSucc)) =
          (∏ j ∈ Ioi i, (x ↑j - x ↑i)) * (x m - x i) := by
      intro i
      have hI : Ioi i.castSucc = insert (Fin.last m) ((Ioi i).map Fin.castSuccEmb) := by
        ext j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simp only [mem_Ioi, mem_insert, true_or]
          exact iff_true_intro (show i.val < m from i.isLt)
        · simp only [mem_Ioi, mem_insert, Finset.mem_map]
          constructor
          · intro h; exact Or.inr ⟨j, h, rfl⟩
          · rintro (h|⟨a, ha, he⟩)
            · have he := congrArg Fin.val h; simp at he; omega
            · exact (Fin.castSuccEmb.injective he : a = j) ▸ ha
      rw [hI, prod_insert (by simp), prod_map]
      simp [mul_comm]
    simp_rw [he, prod_mul_distrib]
    have hv : (∏ j ∈ Ioi (Fin.last m), (x ↑j - x ↑(Fin.last m))) = 1 := by
      rw [show Ioi (Fin.last m) = ∅ by
        ext j; simp only [mem_Ioi, notMem_empty, iff_false]; exact show ¬m < j.val by omega, prod_empty]
    rw [hv, mul_one, mul_pow]
    congr 1
    rw [← sq_abs, abs_prod, Fin.prod_univ_eq_prod_range (fun i => |x m - x i|)]
    rfl

/-- The Vandermonde estimate controls the product of all the Newton denominators. -/
theorem prod_D_upper {x : ℕ → ℝ} (hbox : ∀ k, x k ∈ Set.Icc (-1:ℝ) 1)
    {m : ℕ} (hm : 0 < m) :
    ∏ k ∈ range m, D x m k ≤ (m:ℝ)^m / 2^(m*(m-1)-(m-1)*2) := by
  classical
  let P := fun i : Fin m => Polynomial.Chebyshev.T ℝ (i.val:ℤ)
  let B : Matrix (Fin m) (Fin m) ℝ := Matrix.of (fun i j => (P j).eval (x i))
  have hB : ∀ i j, |B i j| ≤ 1 := by
    intro i j
    obtain ⟨a, ha, hax⟩ := angle_exists (hbox i)
    change |(P j).eval (x i)| ≤ 1
    rw [← hax, angleMap]
    exact (by simp [P, Polynomial.Chebyshev.T_real_cos, Real.abs_cos_le_one])
  have hd := det_sq_le hm B hB
  have hdeg : ∀ i : Fin m, (P i).natDegree = i := by intro i; simp [P, Polynomial.Chebyshev.natDegree_T]
  have hM : (Matrix.of (fun (i j : Fin m) => (P j).coeff i)).det =
      ∏ j : Fin m, (P j).leadingCoeff := by
    rw [Matrix.det_of_isUpperTriangular]
    · exact prod_congr rfl (fun j _ => by simp [Matrix.of_apply, leadingCoeff, hdeg])
    · intro i j hij
      apply coeff_eq_zero_of_natDegree_lt
      simpa [hdeg] using hij
  have hdet : B.det = (Matrix.vandermonde (fun i : Fin m => x i)).det *
      ∏ j : Fin m, (P j).leadingCoeff := by
    unfold B
    rw [Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials _ _
      (fun i => (hdeg i).le), Matrix.det_mul, hM]
  have hcoeff : (∏ j : Fin m, (P j).leadingCoeff)^2 = (2:ℝ)^(m*(m-1)-(m-1)*2) := by
    simp only [P, Polynomial.Chebyshev.leadingCoeff_T, Int.natAbs_natCast]
    rw [Fin.prod_univ_eq_prod_range (fun j => (2:ℝ)^(j-1)), Finset.prod_pow_eq_pow_sum, ← pow_mul]
    congr 1
    have hs : ∀ m : ℕ, (∑ j ∈ range m, (j-1))*2 = m*(m-1)-(m-1)*2 := by
      intro m
      cases m with
      | zero => simp
      | succ v =>
        rw [sum_range_succ']
        simp only [Nat.add_one_sub_one, Nat.zero_sub, add_zero, sum_range_id_mul_two]
        rcases v with _ | v
        · simp
        · simp only [Nat.succ_sub_one]
          have H : (v+1+1)*(v+1) = (v+1)*v + (v+1)*2 := by ring
          change (v+1)*v = (v+1+1)*(v+1) - (v+1)*2
          omega
    exact hs m
  rw [hdet, mul_pow, vandermonde_sq, hcoeff] at hd
  exact (le_div_iff₀ (by positivity)).2 hd

end Erdos1132Proof
end

section
-- InterpMeasure
open Finset Filter MeasureTheory
open scoped BigOperators Topology ENNReal

namespace Erdos1132Proof

noncomputable def dyad (k : ℕ) : ℝ := (1/2:ℝ)^k

theorem dyad_pos (k : ℕ) : 0 < dyad k := by unfold dyad; positivity

theorem dyad_tendsto : Tendsto dyad atTop (𝓝 (0:ℝ)) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem affine_volume (E : Set ℝ) (b a : ℝ) (ha : a ≠ 0) :
    volume ((fun u : ℝ => b + a*u) ⁻¹' E) = ENNReal.ofReal |a⁻¹| * volume E := by
  have he : (fun u : ℝ => b + a*u) ⁻¹' E =
      (a * ·) ⁻¹' ((· + b) ⁻¹' E) := by ext; simp [add_comm]
  rw [he, Real.volume_preimage_mul_left ha, measure_preimage_add_right]

theorem grid_volume {m : ℕ} (hm : 0 < m) (j : ℕ) (E : Set ℝ) :
    volume (grid m j ⁻¹' E) = (m : ℝ≥0∞) * volume E := by
  have hmp : (0:ℝ) < m := by exact_mod_cast hm
  unfold grid
  by_cases hj : Even j
  · simp only [if_pos hj]
    rw [show (fun u : ℝ => ((j:ℝ)+u)/m) = (fun u => (j:ℝ)/m + (m:ℝ)⁻¹*u) by ext; ring,
      affine_volume E _ _ (inv_ne_zero hmp.ne'), inv_inv, abs_of_pos hmp]
    simp
  · simp only [if_neg hj]
    rw [show (fun u : ℝ => ((j:ℝ)+(1-u))/m) = (fun u => ((j:ℝ)+1)/m + (-(m:ℝ)⁻¹)*u) by ext; ring,
      affine_volume E _ _ (neg_ne_zero.mpr (inv_ne_zero hmp.ne')), inv_neg, inv_inv, abs_neg, abs_of_pos hmp]
    simp

theorem grid_cont (m j : ℕ) : Continuous (grid m j) := by
  unfold grid
  split <;> fun_prop


open Classical in
/-- At some level of the Chebyshev polynomial, almost all of its level nodes
belong to a set of almost full angular measure. -/
theorem grid_hits {E : Set ℝ} (hE : MeasurableSet E) {ε : ℝ} (hε : 0 < ε)
    (hvol : volume ((Set.Icc (0:ℝ) 1) \ E) < ENNReal.ofReal ε) {m : ℕ} (hm : 0 < m) :
    ∃ u ∈ Set.Icc (1/4 : ℝ) (3/4),
      (1-2*ε) * m ≤ (((range m).filter (fun j => grid m j u ∈ E)).card : ℝ) := by
  classical
  let U := Set.Icc (1/4:ℝ) (3/4)
  let I := fun j : ℕ => Set.Ioo ((j:ℝ)/m) (((j:ℝ)+1)/m)
  let V := fun j => grid m j ⁻¹' (((Set.Icc (0:ℝ) 1) \ E) ∩ I j)
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hV : ∀ j, MeasurableSet (V j) := fun j =>
    ((measurableSet_Icc.diff hE).inter measurableSet_Ioo).preimage (grid_cont m j).measurable
  have hI : (range m : Set ℕ).PairwiseDisjoint I := by
    intro i hi j hj hij
    wlog hh : i < j generalizing i j
    · exact (this hj hi hij.symm (by omega)).symm
    have h : ((i:ℝ)+1)/m ≤ (j:ℝ)/m := div_le_div_of_nonneg_right
      (by exact_mod_cast (show i+1 ≤ j by omega)) hmR.le
    exact Set.disjoint_left.mpr fun a ha hb => (not_lt_of_ge h) (hb.1.trans ha.2)
  have hsumV : (∑ j ∈ range m, volume (V j)) < (m : ℝ≥0∞) * ENNReal.ofReal ε := by
    simp_rw [V, grid_volume hm]
    rw [← mul_sum, ← measure_biUnion_finset (fun i hi j hj h => (hI hi hj h).mono
      Set.inter_subset_right Set.inter_subset_right) (fun j _ => (measurableSet_Icc.diff hE).inter measurableSet_Ioo)]
    rw [mul_comm (m:ℝ≥0∞), mul_comm (m:ℝ≥0∞)]
    refine ENNReal.mul_lt_mul_left (a := (m:ℝ≥0∞)) (by simp [hm.ne']) (by simp) (lt_of_le_of_lt (measure_mono ?_) hvol)
    intro a ha; obtain ⟨j, hj, h⟩ := Set.mem_iUnion₂.mp ha; exact h.1
  by_contra! h
  have hs : ∀ u : ℝ, U.indicator (fun _ => ENNReal.ofReal (2*ε*m)) u ≤
      ∑ j ∈ range m, (V j).indicator (fun _ => (1 : ℝ≥0∞)) u := by
    intro u
    by_cases hu : u ∈ U
    · rw [Set.indicator_of_mem hu]
      have hu' : u ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
      have he : (∑ j ∈ range m, (V j).indicator (fun _ => (1:ℝ≥0∞)) u) =
          (((range m).filter fun j => grid m j u ∉ E).card : ℝ≥0∞) := by
        simp only [Set.indicator_apply, sum_boole]
        apply congrArg (fun s : Finset ℕ => (s.card : ℝ≥0∞))
        ext j
        simp only [mem_filter, mem_range]
        exact and_congr_right fun hj => ⟨fun h => h.1.2, fun h =>
          ⟨⟨Set.Ioo_subset_Icc_self (grid_mem hj hu'), h⟩, grid_in_cell hj hu'⟩⟩
      rw [he, ← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff (by positivity)]
      have he' := card_filter_add_card_filter_not (s := range m) (fun j => grid m j u ∈ E)
      rw [card_range] at he'
      have hh := h u hu
      have heR : (((range m).filter fun j => grid m j u ∈ E).card : ℝ) +
        (((range m).filter fun j => grid m j u ∉ E).card : ℝ) = (m:ℝ) := by exact_mod_cast he'
      linarith [hh, heR]
    · rw [Set.indicator_of_notMem hu]; positivity
  have hi := lintegral_mono (μ := (volume : Measure ℝ)) hs
  rw [lintegral_indicator_const measurableSet_Icc, lintegral_finsetSum _
    (fun j _ => measurable_const.indicator (hV j))] at hi
  simp_rw [lintegral_indicator_const (hV _), one_mul] at hi
  have he : ENNReal.ofReal (2*ε*m) * volume U = (m : ℝ≥0∞)*ENNReal.ofReal ε := by
    rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul hmR.le]
    congr 1; ring
  exact (not_lt_of_ge (he ▸ hi)) hsumV

/-- Large compact sets on which the assumed pointwise bounds are uniform. -/
theorem large_E (x : ℕ → ℝ) (h : ∀ a ∈ Set.Ioo (0 : ℝ) 1,
    ∀ᶠ n : ℕ in atTop, Erdos1132Proof.lebesgueFunctionL n x (angleMap a) ≤ Real.log n)
    {ε : ℝ} (hε : 0 < ε) : ∃ E : Set ℝ, IsCompact E ∧ E ⊆ Set.Ioo (0:ℝ) 1 ∧
      volume ((Set.Icc (0:ℝ) 1) \ E) < ENNReal.ofReal ε ∧
      ∀ᶠ n : ℕ in atTop, ∀ a ∈ E, Erdos1132Proof.lebesgueFunctionL n x (angleMap a) ≤ Real.log n := by
  let δ := fun N : ℕ => ((N:ℝ)+2)⁻¹
  let B := fun N => Set.Icc (δ N) (1-δ N) ∩
    ⋂ (n : ℕ) (_ : N ≤ n), {a | Erdos1132Proof.lebesgueFunctionL n x (angleMap a) ≤ Real.log n}
  have hδ (N : ℕ) : 0 < δ N := by dsimp [δ]; positivity
  have hsub (N : ℕ) : B N ⊆ Set.Ioo (0:ℝ) 1 := fun a ha =>
    ⟨(hδ N).trans_le ha.1.1, ha.1.2.trans_lt (by linarith [hδ N])⟩
  have hcl (N : ℕ) : IsClosed (B N) := isClosed_Icc.inter <| isClosed_iInter fun n =>
    isClosed_iInter fun _ => isClosed_le ((continuous_L x n).comp (by unfold angleMap; fun_prop)) continuous_const
  have hmono : Monotone B := by
    intro i j hij a ha
    have hle : δ j ≤ δ i := inv_anti₀ (by positivity) (by gcongr)
    exact ⟨⟨hle.trans ha.1.1, ha.1.2.trans (by linarith)⟩,
      Set.mem_iInter.mpr fun n => Set.mem_iInter.mpr fun hn =>
        Set.mem_iInter.mp (Set.mem_iInter.mp ha.2 n) (hij.trans hn)⟩
  have hU : (⋃ N, B N) = Set.Ioo (0:ℝ) 1 := by
    refine Set.Subset.antisymm (Set.iUnion_subset hsub) ?_
    intro a ha
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h a ha)
    have hδ0 : Tendsto δ atTop (𝓝 (0:ℝ)) :=
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).inv_tendsto_atTop
    obtain ⟨j, hj, hja, hjb⟩ := ((eventually_ge_atTop N).and
      ((hδ0.eventually (gt_mem_nhds ha.1)).and (hδ0.eventually (gt_mem_nhds (sub_pos.mpr ha.2))))).exists
    exact Set.mem_iUnion.mpr ⟨j, ⟨⟨hja.le, by linarith⟩, Set.mem_iInter.mpr fun n =>
      Set.mem_iInter.mpr fun hn => hN n (hj.trans hn)⟩⟩
  have ht := tendsto_measure_iUnion_atTop (μ := (volume : Measure ℝ)) hmono
  rw [hU, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one] at ht
  have htR := (ENNReal.tendsto_toReal (by simp : (1:ℝ≥0∞) ≠ ⊤)).comp ht
  obtain ⟨N, hN⟩ := (htR.eventually (lt_mem_nhds (show 1-ε < (1:ℝ≥0∞).toReal by simp; linarith))).exists
  have hNJ : B N ⊆ (Set.Icc (0:ℝ) 1) := (hsub N).trans Set.Ioo_subset_Icc_self
  refine ⟨B N, isCompact_Icc.of_isClosed_subset (hcl N) hNJ, hsub N, ?_, ?_⟩
  · have hfin : volume (Set.Icc (0:ℝ) 1) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hv : volume ((Set.Icc (0:ℝ) 1) \ B N) ≠ ⊤ := ne_top_of_le_ne_top hfin
        (measure_mono Set.sdiff_subset)
    rw [← ENNReal.toReal_lt_toReal hv ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε.le]
    change volume.real ((Set.Icc (0:ℝ) 1) \ B N) < ε
    rw [measureReal_sdiff hNJ (hcl N).measurableSet hfin, Real.volume_real_Icc_of_le (by norm_num)]
    change 1-ε < volume.real (B N) at hN
    linarith
  · exact eventually_atTop.mpr ⟨N, fun n hn a ha => Set.mem_iInter.mp (Set.mem_iInter.mp ha.2 n) hn⟩

theorem density_centres {E : Set ℝ} (hE : MeasurableSet E) (hi : E ⊆ Set.Ioo (0:ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) (hvol : volume ((Set.Icc (0:ℝ) 1) \ E) < ENNReal.ofReal ε) :
    ∃ F : Set ℝ, MeasurableSet F ∧ F ⊆ E ∧ volume ((Set.Icc (0:ℝ) 1) \ F) < ENNReal.ofReal ε ∧
      ∃ K : ℕ, ∀ a ∈ F, ∀ k ≥ K,
        volume.real (Metric.closedBall a (dyad k) \ E) ≤ dyad k / 1000 := by
  let f := fun K => E ∩ ⋂ (k : ℕ) (_ : K ≤ k),
    {a | volume.real (Metric.closedBall a (dyad k) \ E) ≤ dyad k / 1000}
  have hmeas : ∀ K, MeasurableSet (f K) := by
    intro K
    refine hE.inter (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => ?_)
    have h : MeasurableSet {ab : ℝ × ℝ | dist ab.2 ab.1 ≤ dyad k ∧ ab.2 ∉ E} := by
      exact (isClosed_le (by fun_prop : Continuous (fun ab : ℝ × ℝ => dist ab.2 ab.1)) continuous_const).measurableSet.inter
        (hE.compl.preimage measurable_snd)
    exact measurableSet_le (measurable_measure_prodMk_left (ν := (volume : Measure ℝ)) h).ennreal_toReal measurable_const
  have hfsub : ∀ K, f K ⊆ E := fun _ => Set.inter_subset_left
  have hmono : Monotone f := by
    intro i j hij a ha
    exact ⟨ha.1, Set.mem_iInter.mpr fun k => Set.mem_iInter.mpr fun hk =>
      Set.mem_iInter.mp (Set.mem_iInter.mp ha.2 k) (hij.trans hk)⟩
  have hae : ∀ᵐ a ∂(volume : Measure ℝ).restrict E, a ∈ ⋃ K, f K := by
    filter_upwards [ae_restrict_mem hE,
      IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div (volume : Measure ℝ) E 0] with a ha ht
    have hg := ht (fun _ : ℕ => a) dyad
      (tendsto_nhdsWithin_iff.mpr ⟨dyad_tendsto, Eventually.of_forall fun k => dyad_pos k⟩)
       (Eventually.of_forall fun k => by simp)
    have hgR := (ENNReal.tendsto_toReal (by simp : (1:ℝ≥0∞) ≠ ⊤)).comp hg
    obtain ⟨K,hK⟩ := eventually_atTop.mp (hgR.eventually (lt_mem_nhds
      (by norm_num : (1 - 1/2000:ℝ) < (1:ℝ≥0∞).toReal)))
    refine Set.mem_iUnion.mpr ⟨K,ha,Set.mem_iInter.mpr fun k => Set.mem_iInter.mpr fun hk => ?_⟩
    let B := Metric.closedBall a (dyad k)
    have hB : volume.real B = 2 * dyad k := by
      unfold B
      rw [Real.closedBall_eq_Icc, Real.volume_real_Icc_of_le (by linarith [dyad_pos k])]
      ring
    have hfin : volume B ≠ ⊤ := by unfold B; rw [Real.closedBall_eq_Icc,Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hq := hK k hk
    change 1-1/2000 < (volume (E ∩ B) / volume B).toReal at hq
    rw [ENNReal.toReal_div] at hq
    change 1-1/2000 < volume.real (E ∩ B) / volume.real B at hq
    rw [hB] at hq
    change volume.real (B \ E) ≤ _
    rw [show B \ E = B \ (E ∩ B) by ext z; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto,
      measureReal_sdiff Set.inter_subset_right (hE.inter measurableSet_closedBall) hfin, hB]
    linarith [(lt_div_iff₀ (show 0 < 2*dyad k by positivity [dyad_pos k])).mp hq]
  have heq : volume (⋃ K, f K) = volume E := by
    apply measure_congr
    filter_upwards [(ae_restrict_iff' hE).mp hae] with a ha
    apply propext
    exact ⟨fun h => Set.iUnion_subset hfsub h, ha⟩
  have ht := tendsto_measure_iUnion_atTop (μ := (volume : Measure ℝ)) hmono
  rw [heq] at ht
  have hJfin : volume (Set.Icc (0:ℝ) 1) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hEfin : volume E ≠ ⊤ := ne_top_of_le_ne_top hJfin (measure_mono (hi.trans Set.Ioo_subset_Icc_self))
  have hR := (ENNReal.tendsto_toReal hEfin).comp ht
  have hpre : 1-ε < volume.real E := by
    have hfin := ne_top_of_le_ne_top hJfin (measure_mono (Set.sdiff_subset : (Set.Icc (0:ℝ) 1) \ E ⊆ (Set.Icc (0:ℝ) 1)))
    have H : volume.real ((Set.Icc (0:ℝ) 1) \ E) < ε := by
      simpa only [measureReal_def, ENNReal.toReal_ofReal hε.le] using
        (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).2 hvol
    rw [measureReal_sdiff (hi.trans Set.Ioo_subset_Icc_self) hE hJfin,
      Real.volume_real_Icc_of_le (by norm_num)] at H
    linarith
  obtain ⟨K,hK⟩ := (hR.eventually (lt_mem_nhds hpre)).exists
  refine ⟨f K, hmeas K, hfsub K, ?_, K, fun a ha k hk => Set.mem_iInter.mp (Set.mem_iInter.mp ha.2 k) hk⟩
  have hfin := ne_top_of_le_ne_top hJfin (measure_mono (Set.sdiff_subset : (Set.Icc (0:ℝ) 1) \ f K ⊆ (Set.Icc (0:ℝ) 1)))
  rw [← ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε.le]
  change volume.real ((Set.Icc (0:ℝ) 1) \ f K) < ε
  rw [measureReal_sdiff ((hfsub K).trans (hi.trans Set.Ioo_subset_Icc_self)) (hmeas K) hJfin,
    Real.volume_real_Icc_of_le (by norm_num)]
  change 1-ε < volume.real (f K) at hK
  linarith

end Erdos1132Proof
end

section
-- InterpGrowth
open Finset Filter Polynomial MeasureTheory
open scoped BigOperators Topology ENNReal

namespace Erdos1132Proof

theorem degree_lt_of_nat_lt {P : ℝ[X]} {n : ℕ} (h : P.natDegree < n) : P.degree < n := by
  by_cases hp : P = 0
  · simp [hp]
  · exact (natDegree_lt_iff_degree_lt hp).mp h

noncomputable def Wpoly (x : ℕ → ℝ) (s : Finset ℕ) : ℝ[X] := ∏ i ∈ s, (X - C (x i))

theorem Wpoly_abs (x : ℕ → ℝ) (s : Finset ℕ) (t : ℝ) : |(Wpoly x s).eval t| = W x s t := by
  simp [Wpoly, W, eval_prod, abs_prod]

open Classical in
/-- Localized Chebyshev interpolation tests force almost all of the prefix to
lie close to the chosen large set. -/
theorem count_near {x θ : ℕ → ℝ} (hx : Function.Injective x)
    (hθ : ∀ k, θ k ∈ Set.Icc (0:ℝ) 1) (hmap : ∀ k, angleMap (θ k) = x k)
    {E F : Set ℝ} (hE : E ⊆ Set.Icc 0 1) (hF : F ⊆ E) (hFm : MeasurableSet F)
    {B : ℕ} (hB : 8 ≤ B) (hvol : volume (Set.Icc (0:ℝ) 1 \ F) < ENNReal.ofReal (1/(B:ℝ)))
    (hL : ∀ᶠ n : ℕ in atTop, ∀ a ∈ E,
      Erdos1132Proof.lebesgueFunctionL n x (angleMap a) ≤ Real.log n) :
    ∀ᶠ n : ℕ in atTop,
      (1-4/(B:ℝ))*n ≤ (((range n).filter fun i => ∃ a ∈ F, |θ i-a| < mesh n).card : ℝ) := by
  classical
  have hBR : (8:ℝ) ≤ B := by exact_mod_cast hB
  have hBp : 0 < (B:ℝ) := by linarith
  filter_upwards [hL, eventually_ge_atTop (2*B), eventually_peak_small (c := 1/(2*(B:ℝ))) (by positivity)]
    with n hLn hn hsmall
  let d := n/B
  let m := n-2*d
  have hd_le : (d:ℝ) ≤ (n:ℝ)/B := by
    rw [le_div_iff₀ hBp]
    exact_mod_cast Nat.div_mul_le_self n B
  have hd_ge : (n:ℝ)/(2*B) ≤ d := by
    have he := Nat.mod_add_div n B
    have hf := Nat.mod_lt n (show 0 < B by omega)
    change n % B + B*d = n at he
    have h₁ : (n:ℝ) < (d:ℝ)*B+B := by
      exact_mod_cast (show n < d*B+B by rw [mul_comm d B]; omega)
    have h₂ : 2*(B:ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have h2d : 2*d < n := by
    have h := (le_div_iff₀ hBp).mp hd_le
    have h' := mul_le_mul_of_nonneg_left hBR (Nat.cast_nonneg d)
    exact_mod_cast (show (2:ℝ)*d < n by linarith)
  have hm : 0 < m := by dsimp [m]; omega
  have hmle : m ≤ n := Nat.sub_le n _
  have hmd : m + 2*d = n := Nat.sub_add_cancel h2d.le
  obtain ⟨u,hu,hits⟩ := grid_hits hFm (by positivity : 0 < 1/(B:ℝ)) hvol hm
  let a := fun j => grid m j u
  let y := fun j => angleMap (a j)
  let s := (range m).filter (fun j => a j ∈ F)
  let g := (range n).filter (fun i => ∃ a ∈ F, |θ i-a| < mesh n)
  have hcount : (1-4/(B:ℝ))*n ≤ (s.card:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hd_le (show (0:ℝ) ≤ 2 by norm_num)
    have h' := mul_le_mul_of_nonneg_left (show (m:ℝ) ≤ n by exact_mod_cast hmle)
      (show (0:ℝ) ≤ 2/(B:ℝ) by positivity)
    have hh : (m:ℝ)+2*d = n := by exact_mod_cast hmd
    change (1-2*(1/(B:ℝ)))*m ≤ (s.card:ℝ) at hits
    nlinarith only [h,h',hh,hits,show 2*(1/(B:ℝ))*(m:ℝ)=2/(B:ℝ)*(m:ℝ) by ring,
      show 2*((n:ℝ)/B)+2/(B:ℝ)*n = (4/(B:ℝ))*n by ring]
  refine hcount.trans ?_
  by_contra! hcard
  have hcard' : g.card < s.card := by exact_mod_cast hcard
  have hU : u ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  let Q := fun j : s => Lagrange.basis (range m) y j * peak (y j)^d
  let T : (s → ℝ) →ₗ[ℝ] ℝ[X] :=
    { toFun := fun f => ∑ j : s, f j • Q j
      map_add' := by intro f g; simp [add_smul, sum_add_distrib]
      map_smul' := by intro c f; simp [smul_sum, mul_smul] }
  let R : (s → ℝ) →ₗ[ℝ] (g → ℝ) :=
    { toFun := fun f i => (T f).eval (x i)
      map_add' := by intro f g; ext i; simp
      map_smul' := by intro c f; ext i; simp [eval_smul] }
  have hR : ¬Function.Injective R := by
    intro h
    have hr := LinearMap.finrank_le_finrank_of_injective h
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hr
    exact (not_le_of_gt hcard') hr
  obtain ⟨f₁,f₂,he,hh⟩ := Function.not_injective_iff.mp hR
  let f := f₁-f₂
  have hf : f ≠ 0 := sub_ne_zero.mpr hh
  have hfR : R f = 0 := by simp [f, he]
  have hnns : Nonempty s := Finset.nonempty_coe_sort.mpr (card_pos.mp (by omega))
  obtain ⟨j,_,hj⟩ := exists_max_image (univ : Finset s) (fun i => |f i|) univ_nonempty
  have hfj : 0 < |f j| := by
    by_contra! H
    apply hf; ext i
    exact abs_eq_zero.mp (le_antisymm ((hj i (mem_univ i)).trans H) (abs_nonneg _))
  have hdegQ : ∀ j : s, (Q j).natDegree ≤ m-1+2*d := by
    intro j
    have hjr : (j:ℕ) ∈ range m := (mem_filter.mp j.prop).1
    apply (natDegree_mul_le (p := Lagrange.basis (range m) y j) (q := peak (y j)^d)).trans
    rw [Lagrange.natDegree_basis (grid_inj hU) hjr, card_range, natDegree_pow]
    exact Nat.add_le_add_left (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left d (degree_peak (y j))) _
  have hdeg : (T f).degree < n := by
    apply degree_lt_of_nat_lt
    change (∑ j : s, f j • Q j).natDegree < n
    have h := natDegree_sum_le (univ : Finset s) (fun j => f j • Q j)
    refine h.trans_lt ?_
    apply lt_of_le_of_lt (Finset.sup_le_iff.mpr fun j _ => ?_) (show m-1+2*d < n by omega)
    exact (natDegree_smul_le _ _).trans (hdegQ j)
  have hcheck : ∀ i : s, (T f).eval (y i) = f i := by
    intro i
    change (∑ j : s, f j • Q j).eval (y i) = f i
    simp only [eval_finsetSum, eval_smul, smul_eq_mul]
    calc
      _ = f i * (Q i).eval (y i) := by
        apply sum_eq_single i
        · intro l _ hli
          change f l * (Lagrange.basis (range m) y l * peak (y l)^d).eval (y i) = 0
          rw [eval_mul, Lagrange.eval_basis_of_ne (fun h => hli (Subtype.ext h)) (mem_filter.mp i.prop).1]
          ring
        · simp
      _ = _ := by
        change f i * (Lagrange.basis (range m) y i * peak (y i)^d).eval (y i) = _
        rw [eval_mul, Lagrange.eval_basis_self (show Set.InjOn y (range m : Set ℕ) from grid_inj hU)
          (mem_filter.mp i.prop).1]
        simp [peak]
  let b : ℝ := Real.exp (-(1/(2*(B:ℝ))*n) * mesh n ^ 4)
  have hP : ∀ i < n, |(T f).eval (x i)| ≤ 2*(n:ℝ)^2 * |f j| * b := by
    intro i hi
    by_cases hgi : i ∈ g
    · have hh := congrFun hfR ⟨i,hgi⟩
      change (T f).eval (x i) = 0 at hh
      simp only [hh, abs_zero]; positivity [Real.exp_pos (-(1/(2*(B:ℝ))*n) * mesh n ^ 4)]
    have hi' : ∀ v ∈ F, mesh n ≤ |θ i-v| := by
      simpa only [g, mem_filter, mem_range, hi, true_and, not_exists, not_and, not_lt] using hgi
    have hbox : x i ∈ Set.Icc (-1:ℝ) 1 := hmap i ▸ angleMap_mem (θ i)
    have hv (l : s) : |((peak (y l))^d).eval (x i)| ≤ b := by
      apply (peak_exp (angleMap_mem _) hbox d).trans
      apply Real.exp_le_exp.mpr
      have hlF := (mem_filter.mp l.prop).2
      have H := angleMap_lower (hθ i) (hE (hF hlF))
      rw [hmap i] at H
      have H' : 2 * (mesh n)^2 ≤ |x i-y l| := by
        rw [← sq_abs] at H
        exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mesh_pos (by omega)).le (hi' _ hlF) 2)
          (by norm_num)).trans H
      have H'' : 4 * (mesh n)^4 ≤ (x i-y l)^2 := by
        calc _ = (2*(mesh n)^2)^2 := by ring
             _ ≤ _ := by rw [← sq_abs (x i-y l)]; exact pow_le_pow_left₀ (by positivity) H' 2
      change -(↑d * (x i-y l)^2/4) ≤ -(1/(2*(B:ℝ))*n) * mesh n ^ 4
      have Hm := mul_le_mul hd_ge H'' (by positivity) (Nat.cast_nonneg d)
      linarith only [Hm, show (n:ℝ)/(2*(B:ℝ)) * (4*mesh n^4) =
        4*(1/(2*(B:ℝ))*n)*mesh n^4 by ring]
    change |(∑ l : s, f l • Q l).eval (x i)| ≤ _
    simp only [eval_finsetSum, eval_smul, smul_eq_mul]
    refine (Finset.abs_sum_le_sum_abs ..).trans ?_
    calc
      _ ≤ ∑ _l : s, (|f j| * (2*(m:ℝ)) * b) := by
        apply sum_le_sum
        intro l _
        change |f l * (Lagrange.basis (range m) y l * peak (y l)^d).eval (x i)| ≤ _
        simp only [eval_mul, abs_mul]
        rw [← mul_assoc]
        exact mul_le_mul (mul_le_mul (hj l (mem_univ _))
          (grid_basis_bdd hu (mem_range.mp (mem_filter.mp l.prop).1) hbox)
          (abs_nonneg _) (abs_nonneg _)) (hv l) (abs_nonneg _) (by positivity)
      _ ≤ _ := by
        simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
        have hs : (s.card:ℝ) ≤ n := by exact_mod_cast (card_filter_le _ _).trans (card_range m ▸ hmle)
        calc (s.card:ℝ) * (|f j| * (2*(m:ℝ)) * b) ≤ (n:ℝ) * (|f j| * (2*(n:ℝ)) * b) := by
               gcongr
             _ = _ := by ring
  have h := eval_le_L x hx _ hdeg (y j) _ hP
  rw [hcheck j] at h
  have hLg := hLn _ (hF (mem_filter.mp j.prop).2)
  have hh₁ : Erdos1132Proof.lebesgueFunctionL n x (y j) ≤ (n:ℝ) := hLg.trans (Real.log_le_self (Nat.cast_nonneg n))
  have hh₂ : (2:ℝ)*(n:ℝ)^2 * (n:ℝ) ≤ (n:ℝ)^4 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    nlinarith [mul_le_mul_of_nonneg_left this (show 0 ≤ (n:ℝ)^3 by positivity)]
  have hp : (n:ℝ)^4 * b < 1 := hsmall
  have hn' : |f j| ≤ |f j| * ((n:ℝ)^4 * b) := by
    refine h.trans ((mul_le_mul_of_nonneg_left hh₁ (by positivity)).trans ?_)
    calc _ = |f j| * ((2*(n:ℝ)^2*n)*b) := by ring
         _ ≤ _ := by gcongr
  exact (not_le_of_gt (mul_lt_of_lt_one_right hfj hp)) hn'

/-- A lower bound on the norm of a monic nodal polynomial restricted to a
set of almost full angular measure. -/
theorem large_norm {x : ℕ → ℝ} {E : Set ℝ} (hE : MeasurableSet E)
    {B : ℕ} (hB : 8 ≤ B) (hvol : volume (Set.Icc (0:ℝ) 1 \ E) < ENNReal.ofReal (1/(B:ℝ)))
    {M : ℕ → ℝ} (hM : ∀ n a, a ∈ E → W x (range n) (angleMap a) ≤ M n) :
    ∀ᶠ n : ℕ in atTop, -(1+10/(B:ℝ)) * n * Real.log 2 ≤ Real.log (M n) := by
  classical
  have hBR : (8:ℝ) ≤ B := by exact_mod_cast hB
  have hBp : 0 < (B:ℝ) := by linarith
  filter_upwards [eventually_ge_atTop (2*B)] with n hn
  let d := (n+1)/B
  let m := n+1+4*d
  have hm : 0 < m := by dsimp [m]; omega
  have hmd : (m:ℝ) = (n:ℝ)+1+4*d := by dsimp [m]; push_cast; ring
  have hd : (d:ℝ)*(B:ℝ) ≤ (n:ℝ)+1 := by exact_mod_cast Nat.div_mul_le_self (n+1) B
  have hd' : (n:ℝ)+1 < (d:ℝ)*B+B := by
    have he := Nat.mod_add_div (n+1) B
    have hf := Nat.mod_lt (n+1) (show 0 < B by omega)
    change (n+1)%B + B*d = n+1 at he
    exact_mod_cast (show n+1 < d*B+B by rw [mul_comm d B]; omega)
  have hd₁ : (2:ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by dsimp [d]; exact Nat.le_div_iff_mul_le (by omega) |>.2 (by omega))
  have hreg : 2*(B:ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨u,hu,hh⟩ := grid_hits hE (by positivity : 0 < 1/(B:ℝ)) hvol hm
  have hbig : (n:ℝ)+1 ≤ (1-2*(1/(B:ℝ)))*m := by
    apply le_of_mul_le_mul_right _ hBp
    rw [hmd]
    field_simp [hBp.ne']
    nlinarith only [hd', hBR, mul_nonneg (show 0 ≤ (B:ℝ)-4 by linarith) (sub_nonneg.mpr hd₁)]
  let y := fun j => angleMap (grid m j u)
  obtain ⟨s,hs,hsc⟩ := exists_subset_card_eq (n := n+1) (by exact_mod_cast hbig.trans hh)
  have hsr : s ⊆ range m := hs.trans (filter_subset _ _)
  have hu' : u ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  let P := Wpoly x (range n)
  have hnP : P.natDegree = n := by simp [P,Wpoly]
  have hMon : P.Monic := monic_prod_X_sub_C x _
  have hInj : Set.InjOn y (s : Set ℕ) := (grid_inj hu').mono (coe_subset.mpr hsr)
  have hInt := Lagrange.eq_interpolate hInj (f := P) (by
    rw [degree_eq_natDegree hMon.ne_zero, hnP, hsc]; exact_mod_cast Nat.lt_succ_self n)
  have hcoeff := congrArg (fun Q : ℝ[X] => Q.coeff n) hInt
  have hc : ∀ j ∈ s, |(Lagrange.basis s y j).coeff n| ≤ 2^(m+(m-(n+1)))/(m:ℝ) := by
    intro j hj
    have hjr := hsr hj
    have hs' : s.erase j ⊆ (range m).erase j := erase_subset_erase _ hsr
    let V := (range m).erase j \ s.erase j
    have hV : V.card = m-(n+1) := by
      have h := card_sdiff_add_card_eq_card hs'
      change V.card + (s.erase j).card = ((range m).erase j).card at h
      rw [card_erase_of_mem hjr, card_erase_of_mem hj, card_range,hsc] at h
      omega
    have hD : D y m j ≤ W y (s.erase j) (y j) * (2:ℝ)^(m-(n+1)) := by
      unfold D W
      rw [← prod_sdiff hs', mul_comm]
      gcongr
      rw [← hV, ← prod_const]
      exact prod_le_prod (fun _ _ => abs_nonneg _) fun i hi => abs_sub_le_two (angleMap_mem _) (angleMap_mem _)
    have hden := grid_denoms hu j (mem_range.mp hjr)
    have hmR : (0:ℝ) < m := by exact_mod_cast hm
    have hp : 0 < W y (s.erase j) (y j) := by
      have hx := (div_pos hmR (by positivity)).trans_le (hden.trans hD)
      by_contra! hn
      linarith [mul_nonpos_of_nonpos_of_nonneg hn (show 0 ≤ (2:ℝ)^(m-(n+1)) by positivity)]
    have hdeg : (Lagrange.basis s y j).natDegree = n := by rw [Lagrange.natDegree_basis hInj hj,hsc]; simp
    rw [show (Lagrange.basis s y j).coeff n = (Lagrange.basis s y j).leadingCoeff by rw [leadingCoeff,hdeg],
      Lagrange.leadingCoeff_basis hInj hj, abs_inv, abs_prod]
    change (W y (s.erase j) (y j))⁻¹ ≤ _
    rw [le_div_iff₀ hmR, inv_mul_eq_div, div_le_iff₀ hp, pow_add]
    have h := (div_le_iff₀ (show 0 < (2:ℝ)^m by positivity)).mp (hden.trans hD)
    nlinarith only [h]
  have hlim : 1 ≤ M n * (2:ℝ)^(m+(m-(n+1))) := by
    have hEval : ∀ j ∈ s, |P.eval (y j)| ≤ M n := by
      intro j hj
      change |(Wpoly x (range n)).eval (y j)| ≤ _
      rw [Wpoly_abs]
      exact hM n _ (mem_filter.mp (hs hj)).2
    have hpM : 0 ≤ M n := by
      obtain ⟨j,hj⟩ := card_pos.mp (show 0 < s.card by omega)
      exact (abs_nonneg _).trans (hEval j hj)
    have hh : (1:ℝ) = ∑ j ∈ s, P.eval (y j) * (Lagrange.basis s y j).coeff n := by
      have hP1 : P.coeff n = 1 := by rw [← hnP]; exact hMon.leadingCoeff
      simpa only [hP1, Lagrange.interpolate_apply, finsetSum_coeff, coeff_C_mul] using hcoeff
    calc
      1 = |∑ j ∈ s, P.eval (y j) * (Lagrange.basis s y j).coeff n| := by rw [← hh,abs_one]
      _ ≤ ∑ j ∈ s, |P.eval (y j) * (Lagrange.basis s y j).coeff n| := Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ _j ∈ s, M n * (2:ℝ)^(m+(m-(n+1)))/(m:ℝ) := by
        apply sum_le_sum; intro j hj; rw [abs_mul, mul_div_assoc]
        exact mul_le_mul (hEval j hj) (hc j hj) (abs_nonneg _) hpM
      _ ≤ _ := by
        rw [sum_const, nsmul_eq_mul, hsc]
        have h := (show n+1 ≤ m by dsimp [m]; omega)
        rw [← mul_div_assoc, div_le_iff₀ (show (0:ℝ) < m by exact_mod_cast hm)]
        have hh := mul_le_mul_of_nonneg_right (show ((n+1:ℕ):ℝ) ≤ m by exact_mod_cast h)
          (show 0 ≤ M n * (2:ℝ)^(m+(m-(n+1))) by positivity)
        linarith only [hh]
  have hMpos : 0 < M n := by
    by_contra! hh; linarith [mul_nonpos_of_nonpos_of_nonneg hh (show 0 ≤ (2:ℝ)^(m+(m-(n+1))) by positivity)]
  have hh₀ := Real.log_le_log (by norm_num : (0:ℝ)<1) hlim
  rw [Real.log_one, Real.log_mul hMpos.ne' (by positivity), Real.log_pow] at hh₀
  have he : ((m+(m-(n+1)):ℕ):ℝ) ≤ (1+10/(B:ℝ))*n := by
    have heq : m+(m-(n+1)) = n+1+8*d := by dsimp [m]; omega
    rw [heq]; push_cast
    apply le_of_mul_le_mul_right _ hBp
    field_simp [hBp.ne']
    nlinarith
  linarith [mul_le_mul_of_nonneg_right he (Real.log_nonneg (by norm_num : (1:ℝ)≤2))]

end Erdos1132Proof
end

section
-- InterpGaps
open Finset Filter MeasureTheory
open scoped BigOperators Topology ENNReal

namespace Erdos1132Proof

theorem W_erase {x : ℕ → ℝ} {s : Finset ℕ} {i : ℕ} (hi : i ∈ s) (t : ℝ) :
    W x s t = |t-x i| * W x (s.erase i) t := (mul_prod_erase _ _ hi).symm

theorem W_between {x : ℕ → ℝ} {s : Finset ℕ} {a b t : ℝ}
    (ht₁ : a < t) (ht₂ : t < b) (hs : ∀ k ∈ s, x k ≤ a ∨ b ≤ x k) :
    min (W x s a) (W x s b) ≤ W x s t := by
  let v : ℝ := (t-a)/(b-a)
  have hv : 0 ≤ v := div_nonneg (by linarith) (by linarith)
  have hv' : 0 ≤ 1-v := by dsimp [v]; rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have ht : t = (1-v)*a+v*b := by dsimp [v]; field_simp [show b-a ≠ 0 by linarith]; ring
  have hA : ∀ k ∈ s, |a - x k| ^ (1-v) * |b - x k| ^ v ≤ |t-x k| := by
    intro k hk
    have hh := Real.geom_mean_le_arith_mean2_weighted hv' hv (abs_nonneg (a-x k))
      (abs_nonneg (b-x k)) (show 1-v+v=1 by ring)
    apply hh.trans_eq
    rcases hs k hk with h|h
    · rw [abs_of_nonneg (by linarith : 0 ≤ a-x k), abs_of_nonneg (by linarith : 0 ≤ b-x k),
        abs_of_nonneg (by linarith : 0 ≤ t-x k), ht]; ring
    · rw [abs_of_nonpos (by linarith : a-x k ≤ 0), abs_of_nonpos (by linarith : b-x k ≤ 0),
        abs_of_nonpos (by linarith : t-x k ≤ 0), ht]; ring
  have hp := prod_le_prod (s := s) (fun k _ => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
    (Real.rpow_nonneg (abs_nonneg _) _)) hA
  rw [prod_mul_distrib, Real.finsetProd_rpow _ _ (fun _ _ => abs_nonneg _),
    Real.finsetProd_rpow _ _ (fun _ _ => abs_nonneg _)] at hp
  change W x s a ^ (1-v) * W x s b ^ v ≤ W x s t at hp
  have hm : 0 ≤ min (W x s a) (W x s b) := le_min (W_nonneg ..) (W_nonneg ..)
  refine le_trans ?_ hp
  calc
    _ = (min (W x s a) (W x s b)) ^ (1-v) * (min (W x s a) (W x s b)) ^ v := by
      by_cases h : min (W x s a) (W x s b) = 0
      · have h₁ : 0 < v := div_pos (by linarith) (by linarith)
        simp [h, Real.zero_rpow h₁.ne']
      · rw [← Real.rpow_add (lt_of_le_of_ne hm (Ne.symm h)), show 1-v+v=1 by ring, Real.rpow_one]
    _ ≤ _ := mul_le_mul (Real.rpow_le_rpow hm (min_le_left ..) hv') (Real.rpow_le_rpow hm (min_le_right ..) hv)
      (Real.rpow_nonneg hm _) (Real.rpow_nonneg (W_nonneg ..) _)

theorem reciprocal_gap {x : ℕ → ℝ} (hx : Function.Injective x) {p i j : ℕ}
    (hi : i < p) (hj : j < p) (hij : x j < x i)
    (hgap : ∀ k < p, ¬ (x j < x k ∧ x k < x i))
    {t M : ℝ} (hM : 0 < M) (ht : W x (range p) t ≤ M)
    (hl : (x i-x j)/16 ≤ t-x j) (hr : (x i-x j)/16 ≤ x i-t) :
    (x i-x j)/(256*M) ≤ (D x p i)⁻¹ + (D x p j)⁻¹ := by
  let s := ((range p).erase i).erase j
  have hij' : i ≠ j := fun e => (ne_of_gt hij) (congrArg x e)
  have hs : ∀ k ∈ s, x k ≤ x j ∨ x i ≤ x k := by
    intro k hk
    have hh := hgap k (mem_range.mp (mem_erase.mp (mem_erase.mp hk).2).2)
    by_cases h : x j < x k
    · exact Or.inr (le_of_not_gt fun he => hh ⟨h,he⟩)
    · exact Or.inl (le_of_not_gt h)
  have htj : x j < t := by linarith
  have hti : t < x i := by linarith
  have hI : W x (range p) t = (x i-t) * ((t-x j)*W x s t) := by
    rw [W_erase (mem_range.mpr hi), W_erase (mem_erase.mpr ⟨hij'.symm,mem_range.mpr hj⟩),
      abs_of_neg (by linarith : t-x i<0), abs_of_pos (by linarith : 0<t-x j)]
    ring
  have hd₁ : D x p i = (x i-x j)*W x s (x i) := by
    rw [D, W_erase (mem_erase.mpr ⟨hij'.symm,mem_range.mpr hj⟩), abs_of_pos (sub_pos.mpr hij)]
  have hd₂ : D x p j = (x i-x j)*W x s (x j) := by
    rw [D, W_erase (mem_erase.mpr ⟨hij',mem_range.mpr hi⟩), abs_sub_comm, abs_of_pos (sub_pos.mpr hij), erase_right_comm]
  have hab : 0 < x i-x j := sub_pos.mpr hij
  have H : (x i-x j) * min (D x p i) (D x p j) ≤ 256 * M := by
    have h := W_between htj hti hs
    have h' := mul_le_mul hr hl (by positivity) (by linarith : 0 ≤ x i-t)
    have h'' := mul_le_mul h' h (le_min (W_nonneg ..) (W_nonneg ..)) (by positivity [sub_pos.mpr hti,sub_pos.mpr htj])
    rw [hI] at ht
    rw [hd₁,hd₂, ← mul_min_of_nonneg _ _ hab.le]
    rw [min_comm (W x s (x i))]
    linarith only [ht,h'']
  have hinv (c : ℝ) (hc : 0 < c) (h : (x i-x j)*c ≤ 256*M) :
      (x i-x j)/(256*M) ≤ c⁻¹ := by
    rw [← one_div, le_div_iff₀ hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    simpa using h
  rcases le_total (D x p i) (D x p j) with h|h
  · rw [min_eq_left h] at H
    linarith [hinv _ (D_pos hx p i) H, inv_nonneg.mpr (D_pos hx p j).le]
  · rw [min_eq_right h] at H
    linarith [hinv _ (D_pos hx p j) H, inv_nonneg.mpr (D_pos hx p i).le]

theorem band_sine {a r : ℝ}
    (hsmall : 8*Real.pi*r ≤ Real.sin (Real.pi*a)) :
    ∀ z, |z-a| ≤ 4*r → (Real.pi*Real.sin (Real.pi*a))/2 ≤ Real.pi*Real.sin (Real.pi*z) ∧
      Real.pi*Real.sin (Real.pi*z) ≤ 2*(Real.pi*Real.sin (Real.pi*a)) := by
  intro z hz
  have hh := Real.abs_sin_sub_sin_le (Real.pi*z) (Real.pi*a)
  rw [← mul_sub,abs_mul,abs_of_pos Real.pi_pos] at hh
  have H := abs_le.mp (hh.trans (mul_le_mul_of_nonneg_left hz Real.pi_pos.le))
  have hr : 0 ≤ r := by linarith only [abs_nonneg (z-a), hz]
  have h₁ : Real.sin (Real.pi*a)/2 ≤ Real.sin (Real.pi*z) := by linarith
  have h₂ : Real.sin (Real.pi*z) ≤ 2*Real.sin (Real.pi*a) := by
    linarith only [H.2, hsmall, mul_nonneg Real.pi_pos.le hr]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left h₁ Real.pi_pos.le, mul_le_mul_of_nonneg_left h₂ Real.pi_pos.le]

open Classical in
theorem band_mass {x θ : ℕ → ℝ} (hx : Function.Injective x)
    (hθ : ∀ k, θ k ∈ Set.Icc (0:ℝ) 1) (hmap : ∀ k, angleMap (θ k) = x k)
    {E : Set ℝ} {p : ℕ} {M : ℝ} (hM : 0 < M)
    (hMp : ∀ a ∈ E, W x (range p) (angleMap a) ≤ M)
    {q : ℝ} (hq : 0 < q) (hcover : ∀ a ∈ E, ∃ i < p, |θ i-a| < q)
    {y r L : ℝ} (hr : 0 < r) (hq' : q ≤ r/100) (hLp : 0 < L)
    (hslope : ∀ a b : ℝ, y ≤ a → a < b → b ≤ y+r →
      L*(b-a) ≤ angleMap a-angleMap b ∧ angleMap a-angleMap b ≤ 4*L*(b-a))
    (hm : volume.real (Set.Icc (y+r/2) (y+r) \ E) ≤ r/100) :
    1/(32768*M) ≤ ∑ i ∈ (range p).filter (fun i => θ i ∈ Set.Ioo (y+r/2) (y+r)),
      1 / (|angleMap y - x i| * D x p i) := by
  classical
  let s := (range p).filter (fun i => θ i ∈ Set.Ioo (y+r/2) (y+r))
  have hs (i : ℕ) (hi : i ∈ s) : i < p ∧ θ i ∈ Set.Ioo (y+r/2) (y+r) := by
    simpa [s] using hi
  let A := Set.Icc (y+r/2) (y+r)
  have hfin : volume (A \ E) ≠ ⊤ := ne_top_of_le_ne_top (by unfold A; rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    (measure_mono Set.sdiff_subset)
  have hmeet (a b : ℝ) (ha : y+r/2 ≤ a) (hb : b ≤ y+r) (hab : r/100 < b-a) :
      ∃ z ∈ E, a < z ∧ z < b := by
    by_contra! hh
    have he : Set.Ioo a b ⊆ A \ E := by
      intro t ht
      exact ⟨⟨ha.trans ht.1.le, ht.2.le.trans hb⟩, fun h => (not_lt_of_ge (hh t h ht.1)) ht.2⟩
    have h := (measureReal_mono he hfin).trans hm
    rw [Real.volume_real_Ioo_of_le (by linarith)] at h
    linarith
  obtain ⟨v,hv,hv₁,hv₂⟩ := hmeet (y+11*r/20) (y+3*r/5) (by linarith) (by linarith) (by linarith)
  obtain ⟨w,hw,hw₁,hw₂⟩ := hmeet (y+9*r/10) (y+19*r/20) (by linarith) (by linarith) (by linarith)
  obtain ⟨i,hi,hi'⟩ := hcover v hv
  obtain ⟨j,hj,hj'⟩ := hcover w hw
  have hvi := abs_lt.mp hi'
  have hwj := abs_lt.mp hj'
  have his : i ∈ s := mem_filter.mpr ⟨mem_range.mpr hi, by constructor <;> linarith⟩
  have hjs : j ∈ s := mem_filter.mpr ⟨mem_range.mpr hj, by constructor <;> linarith⟩
  have hspan : r/4 ≤ θ j - θ i := by linarith
  have hθinj : Function.Injective θ := fun a b he => hx (by rw [← hmap a, ← hmap b, he])
  let V := s.image θ
  have hVcard : V.card = s.card := card_image_of_injective _ hθinj
  have hV₂ : 2 ≤ V.card := by
    apply (show (2:ℕ) = ({θ i, θ j}:Finset ℝ).card by rw [card_pair]; intro h; linarith [hspan]).trans_le
    apply card_le_card
    intro k hk
    simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl|rfl
    · exact mem_image_of_mem _ his
    · exact mem_image_of_mem _ hjs
  let d := V.card - 1
  have hd : V.card = d+1 := by dsimp [d]; omega
  let z := V.orderEmbOfFin hd
  have hzM (l : Fin (d+1)) : z l ∈ V := V.orderEmbOfFin_mem hd l
  choose f hf hfz using (fun l : Fin (d+1) => mem_image.mp (hzM l))
  have hfi : Function.Injective f := by
    intro a b hab
    apply z.injective
    rw [← hfz a, ← hfz b, hab]
  have hfs : ∀ l, θ (f l) ∈ Set.Ioo (y+r/2) (y+r) := fun l => (hs _ (hf l)).2
  have hzS (l : Fin (d+1)) : z l ∈ Set.Ioo (y+r/2) (y+r) := hfz l ▸ hfs l
  have hz_span : r/4 ≤ z (Fin.last d) - z 0 := by
    have aa : θ i ∈ V := mem_image_of_mem _ his
    have bb : θ j ∈ V := mem_image_of_mem _ hjs
    obtain ⟨a,ha⟩ := (show Set.range z = (V : Set ℝ) from V.range_orderEmbOfFin hd).superset aa
    obtain ⟨b,hb⟩ := (show Set.range z = (V : Set ℝ) from V.range_orderEmbOfFin hd).superset bb
    rw [← ha, ← hb] at hspan
    linarith [z.monotone (Fin.zero_le a), z.monotone (Fin.le_last b)]
  let l := fun k : Fin d => z k.castSucc
  let u := fun k : Fin d => z k.succ
  have hlt (k : Fin d) : l k < u k := z.strictMono Fin.castSucc_lt_succ
  let mid := fun k => Set.Ioo (l k+(u k-l k)/4) (u k-(u k-l k)/4)
  let bad := (univ : Finset (Fin d)).filter (fun k => Disjoint (mid k) E)
  let good := (univ : Finset (Fin d)).filter (fun k => ¬ Disjoint (mid k) E)
  have hbad : ∑ k ∈ bad, (u k-l k)/2 ≤ r/100 := by
    have hdj : (bad : Set (Fin d)).PairwiseDisjoint mid := by
      intro a ha b hb hab
      wlog hab' : a < b generalizing a b
      · exact (this hb ha hab.symm (lt_of_le_of_ne (le_of_not_gt hab') hab.symm)).symm
      have hle : u a ≤ l b := z.monotone (by change a.val+1 ≤ b.val; exact Nat.succ_le_of_lt hab')
      exact Set.disjoint_left.mpr fun t ht ht' => by linarith [ht.2, ht'.1, hlt a,hlt b]
    have hsub : ∀ k ∈ bad, mid k ⊆ A \ E := by
      intro k hk t ht
      have hh := Set.disjoint_left.mp ((mem_filter.mp hk).2) ht
      exact ⟨⟨by linarith [(hzS k.castSucc).1,ht.1,hlt k],by linarith [(hzS k.succ).2,ht.2,hlt k]⟩,hh⟩
    have hmeasure : (∑ k ∈ bad, volume.real (mid k)) ≤ r / 100 := by
      rw [← measureReal_biUnion_finset hdj (fun _ _ => measurableSet_Ioo) (fun _ _ => by
        rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)]
      exact (measureReal_mono (Set.iUnion₂_subset hsub) hfin).trans hm
    refine le_trans (le_of_eq ?_) hmeasure
    apply sum_congr rfl
    intro k hk
    unfold mid
    rw [Real.volume_real_Ioo_of_le (by linarith [hlt k])]; ring
  have htotal : ∑ k : Fin d, (u k - l k) = z (Fin.last d) - z 0 := by
    rw [sum_sub_distrib]
    have h₁ := Fin.sum_univ_succ z
    have h₂ := Fin.sum_univ_castSucc z
    dsimp only [u,l]
    linarith
  have hg_length : r/5 ≤ ∑ k ∈ good, (u k-l k) := by
    have h := sum_filter_add_sum_filter_not (univ : Finset (Fin d)) (fun k => Disjoint (mid k) E) (fun k => u k-l k)
    change ∑ k ∈ bad, (u k-l k) + ∑ k ∈ good, (u k-l k) = _ at h
    rw [← sum_div] at hbad
    linarith
  have hD (k : Fin d) (hk : k ∈ good) : L*(u k-l k)/(256*M) ≤
      (D x p (f k.castSucc))⁻¹ + (D x p (f k.succ))⁻¹ := by
    have hnde := (mem_filter.mp hk).2
    obtain ⟨a,ha,haE⟩ := Set.not_disjoint_iff.mp hnde
    have hlr : l k < a ∧ a < u k := ⟨by linarith [ha.1,hlt k],by linarith [ha.2,hlt k]⟩
    have hlo : y ≤ l k := by linarith [(hzS k.castSucc).1]
    have hup : u k ≤ y+r := (hzS k.succ).2.le
    have hsl := hslope _ _ hlo (hlt k) hup
    have hgap' : ∀ b < p, ¬ (x (f k.succ) < x b ∧ x b < x (f k.castSucc)) := by
      intro b hb hb'
      have bx : θ b < u k ∧ l k < θ b := by
        have h₁ : u k ∈ Set.Icc (0:ℝ) 1 := by change z k.succ ∈ _; rw [← hfz k.succ]; exact hθ _
        have h₂ : l k ∈ Set.Icc (0:ℝ) 1 := by change z k.castSucc ∈ _; rw [← hfz k.castSucc]; exact hθ _
        rw [← hmap (f k.succ), ← hmap b, ← hmap (f k.castSucc), hfz k.succ,hfz k.castSucc] at hb'
        exact ⟨(angleMap_strictAnti.lt_iff_gt h₁ (hθ b)).mp hb'.1,
          (angleMap_strictAnti.lt_iff_gt (hθ b) h₂).mp hb'.2⟩
      have hbS : b ∈ s := mem_filter.mpr ⟨mem_range.mpr hb, ⟨(hzS k.castSucc).1.trans bx.2, bx.1.trans (hzS k.succ).2⟩⟩
      have hV : θ b ∈ V := mem_image_of_mem _ hbS
      obtain ⟨c,hc⟩ := (show Set.range z = (V : Set ℝ) from V.range_orderEmbOfFin hd).superset hV
      rw [← hc] at bx
      have h₁ := z.strictMono.lt_iff_lt.mp bx.1
      have h₂ := z.strictMono.lt_iff_lt.mp bx.2
      exact (Nat.not_lt_of_ge (Nat.succ_le_of_lt h₂)) h₁
    have h₁ := hslope _ _ hlo hlr.1 (hlr.2.le.trans hup)
    have h₂ := hslope _ _ (hlo.trans hlr.1.le) hlr.2 hup
    have ht₁ : (angleMap (l k)-angleMap (u k))/16 ≤ angleMap a-angleMap (u k) := by
      nlinarith [mul_le_mul_of_nonneg_left (show (u k-l k)/4 ≤ u k-a by linarith [ha.2]) hLp.le]
    have ht₂ : (angleMap (l k)-angleMap (u k))/16 ≤ angleMap (l k)-angleMap a := by
      nlinarith [mul_le_mul_of_nonneg_left (show (u k-l k)/4 ≤ a-l k by linarith [ha.1]) hLp.le]
    have hle := reciprocal_gap hx (hs _ (hf k.castSucc)).1 (hs _ (hf k.succ)).1
      (by rw [← hmap,← hmap,hfz,hfz]; linarith [mul_pos hLp (sub_pos.mpr (hlt k))]) hgap'
      hM (hMp a haE) (by simpa only [← hmap,hfz] using ht₁) (by simpa only [← hmap,hfz] using ht₂)
    apply le_trans _ hle
    gcongr
    simpa only [← hmap,hfz] using hsl.1
  have hsD : L*(r/5)/(256*M) ≤ 2 * ∑ i ∈ s, (D x p i)⁻¹ := by
    have H := sum_le_sum hD
    rw [sum_add_distrib, ← sum_div, ← mul_sum] at H
    have h₁ : ∑ k ∈ good, (D x p (f k.castSucc))⁻¹ ≤ ∑ i ∈ s, (D x p i)⁻¹ := by
      rw [← sum_image (f := fun i => (D x p i)⁻¹) (g := fun k : Fin d => f k.castSucc)
        (fun a _ b _ h => Fin.castSucc_injective _ (hfi h))]
      refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => (inv_pos.mpr (D_pos hx _ _)).le)
      exact image_subset_iff.mpr fun a _ => hf _
    have h₂ : ∑ k ∈ good, (D x p (f k.succ))⁻¹ ≤ ∑ i ∈ s, (D x p i)⁻¹ := by
      rw [← sum_image (f := fun i => (D x p i)⁻¹) (g := fun k : Fin d => f k.succ)
        (fun a _ b _ h => Fin.succ_injective _ (hfi h))]
      refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => (inv_pos.mpr (D_pos hx _ _)).le)
      exact image_subset_iff.mpr fun a _ => hf _
    have h₃ : L*(r/5)/(256*M) ≤ L*(∑ k ∈ good, (u k-l k))/(256*M) := by gcongr
    linarith only [H,h₁,h₂,h₃]
  have hsX : (∑ i ∈ s, (D x p i)⁻¹) / (4*L*r) ≤ ∑ i ∈ s, 1/(|angleMap y-x i| * D x p i) := by
    rw [sum_div]
    apply sum_le_sum
    intro i hi
    have hh := hslope y (θ i) le_rfl (by linarith [(hs i hi).2.1]) (hs i hi).2.2.le
    have hh' : 0 < angleMap y-x i := by
      rw [← hmap i]; exact (mul_pos hLp (by linarith [(hs i hi).2.1])).trans_le hh.1
    have hb : |angleMap y-x i| ≤ 4*L*r := by
      rw [abs_of_pos hh', ← hmap i]
      exact hh.2.trans (by gcongr; linarith [(hs i hi).2.2])
    rw [inv_eq_one_div, div_div, mul_comm (D x p i)]
    exact one_div_le_one_div_of_le (by positivity [hh', D_pos hx p i]) (mul_le_mul_of_nonneg_right hb (D_pos hx p i).le)
  have hfinal : 1/(32768*M) ≤ (∑ i ∈ s, (D x p i)⁻¹) / (4*L*r) := by
    rw [le_div_iff₀ (by positivity)]
    calc _ ≤ L*(r/5)/(256*M)/2 := by
            rw [div_div]; field_simp; nlinarith only [mul_pos hLp hr]
         _ ≤ _ := by linarith
  exact hfinal.trans hsX

end Erdos1132Proof
end

section
-- InterpFinal
open Finset Filter MeasureTheory
open scoped BigOperators Topology ENNReal

namespace Erdos1132Proof

theorem log_prod_D {x : ℕ → ℝ} (hx : Function.Injective x)
    (hbox : ∀ i, x i ∈ Set.Icc (-1:ℝ) 1) {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ range n, Real.log (D x n i) ≤ (n:ℝ) * Real.log n -
      ((n*(n-1)-(n-1)*2:ℕ):ℝ)*Real.log 2 := by
  rw [← Real.log_prod (fun i _ => (D_pos hx n i).ne')]
  have h := Real.log_le_log (prod_pos (fun i _ => D_pos hx n i)) (prod_D_upper hbox hn)
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h
  exact h

theorem newton_log_sum {x : ℕ → ℝ} (hx : Function.Injective x) (n : ℕ) :
    2 * (∑ i ∈ range n, Real.log (W x (range i) (x i))) =
      ∑ i ∈ range n, Real.log (D x n i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, sum_range_succ]
    have HD : ∀ i ∈ range n, Real.log (D x (n+1) i) =
        Real.log (D x n i) + Real.log |x i-x n| := by
      intro i hi
      rw [D_split x (mem_range.mp hi) (Nat.le_succ n)]
      simp only [W, Nat.Ico_succ_singleton, prod_singleton]
      exact Real.log_mul (D_pos hx n i).ne' (abs_pos.mpr (sub_ne_zero.mpr (hx.ne (Nat.ne_of_lt (mem_range.mp hi))))).ne'
    rw [sum_congr rfl HD, sum_add_distrib]
    rw [show D x (n+1) n = W x (range n) (x n) by simp [D, range_add_one]]
    have he : ∑ i ∈ range n, Real.log |x i-x n| = Real.log (W x (range n) (x n)) := by
      unfold W
      rw [Real.log_prod (fun i hi => (abs_pos.mpr (sub_ne_zero.mpr
        (hx.ne (Nat.ne_of_lt (mem_range.mp hi)).symm))).ne')]
      exact sum_congr rfl (fun _ _ => congrArg Real.log (abs_sub_comm ..))
    rw [he]
    ring

theorem mesh_small_dyad (K : ℕ) : ∀ᶠ n : ℕ in atTop, ∀ k < Nat.log 2 n / 16,
    mesh n ≤ dyad (k+K) / 100 := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/16)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (100 / dyad K), eventually_ge_atTop 1]
    with n hn hn₁ k hk
  have hp : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnk : (2:ℝ)^(16*k) ≤ n := by
    exact_mod_cast (le_trans (pow_le_pow_right₀ (by decide : (1:ℕ)≤2) (show 16*k ≤ Nat.log 2 n by omega))
      (Nat.pow_log_le_self 2 (by omega : n ≠ 0)))
  have hkbound : (2:ℝ)^k ≤ (n:ℝ)^(1/16:ℝ) := by
    have hf := Real.rpow_le_rpow (by positivity : 0 ≤ (2:ℝ)^(16*k)) hnk (by norm_num : (0:ℝ) ≤ 1/16)
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2), Nat.cast_mul,
      Nat.cast_ofNat, show (16:ℝ)*(k:ℝ)*(1/16:ℝ)=k by ring, Real.rpow_natCast] at hf
    exact hf
  change 100 / dyad K ≤ (n:ℝ)^(1/16:ℝ) at hn
  have hm : 100 * (2:ℝ)^k ≤ dyad K * ((n:ℝ)^(1/16:ℝ) * (n:ℝ)^(1/16:ℝ)) := by
    have hx := (div_le_iff₀ (dyad_pos K)).mp hn
    have hy := mul_le_mul hx hkbound (by positivity) (by positivity [dyad_pos K])
    linarith only [hy]
  rw [← Real.rpow_add hp, show (1/16:ℝ)+1/16=1/8 by norm_num] at hm
  rw [mesh, Real.rpow_neg hp.le, show dyad (k+K) = dyad K * ((2:ℝ)^k)⁻¹ by
    unfold dyad; rw [pow_add, ← inv_pow]; ring]
  rw [le_div_iff₀ (by norm_num : (0:ℝ)<100), inv_mul_eq_div, div_le_iff₀ (by positivity),
    ← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith only [hm]

theorem log_logNat_le :
    ∀ᶠ p : ℕ in atTop, Real.log p / 32 ≤ ((Nat.log 2 p / 16 : ℕ):ℝ) := by
  have hl := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hl.eventually_ge_atTop 64, eventually_ge_atTop 1] with p hp hp₁
  have hpR : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hg := Real.log_le_log hpR (show (p:ℝ) ≤ (2:ℝ)^(Nat.log 2 p+1) by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : (1:ℕ) < 2) p).le)
  rw [Real.log_pow, Nat.cast_add, Nat.cast_one] at hg
  have hr : (Nat.log 2 p : ℝ) ≤ 16 * (Nat.log 2 p / 16 : ℕ) + 15 := by
    exact_mod_cast (show Nat.log 2 p ≤ 16*(Nat.log 2 p/16)+15 by omega)
  have hd := mul_le_mul_of_nonneg_right hr (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  have hl₂ : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have ht := mul_le_mul_of_nonneg_left hl₂ (show 0 ≤ (16:ℝ)*((Nat.log 2 p/16:ℕ):ℝ)+16 by positivity)
  change 64 ≤ Real.log p at hp
  nlinarith only [hg,hd,ht,hp]

theorem maxW {x : ℕ → ℝ} {E : Set ℝ} (hE : IsCompact E) (hvol : 0 < volume E)
    (hsub : E ⊆ Set.Icc (0:ℝ) 1) :
    ∃ M : ℕ → ℝ, (∀ n, 0 < M n) ∧
      ∀ n, (∃ a ∈ E, W x (range n) (angleMap a) = M n) ∧
        ∀ a ∈ E, W x (range n) (angleMap a) ≤ M n := by
  classical
  have hne : E.Nonempty := by by_contra! h; simp [h] at hvol
  have hc : Continuous angleMap := by unfold angleMap; fun_prop
  have H (n : ℕ) := hE.exists_isMaxOn hne ((continuous_W x (range n)).comp hc).continuousOn
  choose z hz hmax using H
  refine ⟨fun n => W x (range n) (angleMap (z n)), ?_, fun n => ⟨⟨z n,hz n,rfl⟩, fun a ha => hmax n ha⟩⟩
  intro n
  by_contra! h
  have hn : E ⊆ ⋃ i ∈ range n, {θ | θ ∈ Set.Icc (0:ℝ) 1 ∧ angleMap θ = x i} := by
    intro a ha
    by_contra he
    have hw := W_pos (s := range n) (x := x) (t := angleMap a) (fun i hi h =>
      he (Set.mem_iUnion₂.mpr ⟨i,hi,hsub ha,h⟩))
    exact (not_lt_of_ge ((hmax n ha).trans h)) hw
  have hzero : volume (⋃ i ∈ range n, {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ angleMap θ = x i}) = 0 := by
    apply (measure_biUnion_null_iff (range n).finite_toSet.countable).2
    intro i hi
    by_cases h : ∃ t ∈ Set.Icc (0:ℝ) 1, angleMap t = x i
    · obtain ⟨t,ht,he⟩ := h
      refine le_antisymm ((measure_mono (show {θ | θ ∈ Set.Icc (0:ℝ) 1 ∧ angleMap θ = x i} ⊆ {t} from ?_)).trans (by simp)) (by positivity)
      intro z hz
      exact angleMap_strictAnti.injOn hz.1 ht (hz.2.trans he.symm)
    · rw [show {θ | θ ∈ Set.Icc (0:ℝ) 1 ∧ angleMap θ = x i} = ∅ by
        ext z; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]; exact fun hz => h ⟨z,hz⟩]
      simp
  exact hvol.ne' (le_antisymm ((measure_mono hn).trans hzero.le) (by positivity))

theorem sum_shells {x θ : ℕ → ℝ} (hx : Function.Injective x)
    (hθ : ∀ i, θ i ∈ Set.Icc (0:ℝ) 1) (hmap : ∀ i, angleMap (θ i) = x i)
    {E F : Set ℝ}
    {K₀ : ℕ} (hden : ∀ a ∈ F, ∀ k ≥ K₀,
      volume.real (Metric.closedBall a (dyad k) \ E) ≤ dyad k / 1000)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hR : ∀ a ∈ F, R₀ ≤ Real.sin (Real.pi*a))
    (K : ℕ) (hK₀ : K₀+2 ≤ K) (hK : 8*Real.pi*dyad K ≤ R₀)
    {p : ℕ} (hp : 0 < p) {M : ℝ} (hM : 0 < M)
    (hMp : ∀ a ∈ E, W x (range p) (angleMap a) ≤ M)
    (hc : ∀ a ∈ E, ∃ i < p, |θ i-a| < mesh p)
    (hmesh : ∀ k < Nat.log 2 p/16, mesh p ≤ dyad (k+K)/100)
    {y a : ℝ} (ha : a ∈ F) (hya : |y-a| < mesh p) :
    ((Nat.log 2 p/16 : ℕ):ℝ)/(32768*M) ≤
      ∑ i ∈ (range p).filter (fun i => y < θ i ∧ θ i < y+dyad K),
        1/(|angleMap y-x i| * D x p i) := by
  classical
  let N := Nat.log 2 p/16
  let r := fun k => dyad (k+K)
  let S := fun k => (range p).filter (fun i => θ i ∈ Set.Ioo (y+r k/2) (y+r k))
  have hS : (range N : Set ℕ).PairwiseDisjoint S := by
    intro i hi j hj hij
    wlog h : i < j generalizing i j
    · exact (this hj hi hij.symm (by omega)).symm
    have hh : r j ≤ r i/2 := by
      unfold r dyad
      rw [← show (1/2:ℝ)^(i+K+1) = (1/2:ℝ)^(i+K)/2 by rw [pow_succ]; ring]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact disjoint_left.mpr fun k hk hk' => by
      linarith [(mem_filter.mp hk).2.1, (mem_filter.mp hk').2.2]
  have hsum : ∀ k ∈ range N, 1/(32768*M) ≤
      ∑ i ∈ S k, 1/(|angleMap y-x i| * D x p i) := by
    intro k hk
    have hq := hmesh k (mem_range.mp hk)
    have hdist := (abs_lt.mp hya)
    have hrp : 0 < r k := dyad_pos _
    have hrK : r k ≤ dyad K := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hsmall : 8 * Real.pi * r k ≤ Real.sin (Real.pi*a) := by
      nlinarith only [hK, hR a ha, mul_le_mul_of_nonneg_left hrK (show 0 ≤ 8*Real.pi by positivity)]
    have hsin : 0 < Real.sin (Real.pi*a) := hR₀.trans_le (hR a ha)
    let L := (Real.pi * Real.sin (Real.pi*a))/2
    have hLp : 0 < L := by dsimp [L]; positivity
    apply band_mass hx hθ hmap hM hMp (mesh_pos hp) hc hrp hq hLp
    · intro b c hb hbc hc'
      apply angleMap_slope hbc
      intro z hz
      have hzz : |z-a| ≤ 4*r k := abs_le.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩
      have hh := band_sine hsmall z hzz
      exact ⟨hh.1, by dsimp [L]; linarith [hh.2]⟩
    · have he : dyad (k+K-2) = 4*r k := by
        dsimp only [r, dyad]
        conv_rhs => rw [show k+K = (k+K-2)+2 by omega, pow_add]
        ring
      have hball : Metric.closedBall a (dyad (k+K-2)) = Set.Icc (a-4*r k) (a+4*r k) := by
        rw [he, Real.closedBall_eq_Icc]
      have hsub : Set.Icc (y+r k/2) (y+r k) \ E ⊆ Metric.closedBall a (dyad (k+K-2)) \ E := by
        intro b hb
        rw [hball]
        exact ⟨⟨by linarith [hb.1.1], by linarith [hb.1.2]⟩, hb.2⟩
      have hf : volume (Metric.closedBall a (dyad (k+K-2)) \ E) ≠ ⊤ :=
        ne_top_of_le_ne_top (by rw [hball, Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (measure_mono Set.sdiff_subset)
      have ht := (measureReal_mono hsub hf).trans (hden a ha _ (by omega))
      rw [he] at ht
      linarith
  calc
    _ = ∑ _k ∈ range N, 1/(32768*M) := by simp [N, sum_const, div_eq_mul_inv]
    _ ≤ _ := sum_le_sum hsum
    _ = ∑ i ∈ (range N).biUnion S, 1/(|angleMap y-x i| * D x p i) := (sum_biUnion hS).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun a ha =>
      let ⟨k,hk,ha⟩ := mem_biUnion.mp ha
      let ⟨h₁,h₂⟩ := mem_filter.mp ha
      mem_filter.mpr ⟨h₁,by
        have h := dyad_pos (k+K)
        have hg : dyad (k+K) ≤ dyad K := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        change θ a ∈ Set.Ioo (y+r k/2) (y+r k) at h₂
        change 0 < r k at h
        change r k ≤ dyad K at hg
        exact ⟨by linarith [h₂.1], h₂.2.trans_le (by linarith)⟩⟩)
      (fun i hi _ => div_nonneg zero_le_one (mul_nonneg (abs_nonneg _) (D_pos hx p i).le))

open Classical in
/-- A logarithmic amount of reciprocal-denominator weight in a small
one-sided neighbourhood of a recent node. -/
theorem local_mass {x θ : ℕ → ℝ} (hx : Function.Injective x)
    (hθ : ∀ i, θ i ∈ Set.Icc (0:ℝ) 1) (hmap : ∀ i, angleMap (θ i) = x i)
    {E F : Set ℝ} (hE : IsCompact E) (hEi : E ⊆ Set.Ioo (0:ℝ) 1) (hEn : E.Nonempty) (hF : F ⊆ E)
    {K₀ : ℕ} (hden : ∀ a ∈ F, ∀ k ≥ K₀,
      volume.real (Metric.closedBall a (dyad k) \ E) ≤ dyad k / 1000)
    {M : ℕ → ℝ} (hM : ∀ p, 0 < M p)
    (hMp : ∀ p a, a ∈ E → W x (range p) (angleMap a) ≤ M p)
    (hc : ∀ᶠ p : ℕ in atTop, ∀ a ∈ E, ∃ i < p, |θ i-a| < mesh p)
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ p : ℕ in atTop, (∃ a ∈ F, |θ p-a| < mesh p) →
      Real.log p / (1048576*M p) ≤
        ∑ i ∈ (range p).filter (fun i => θ p < θ i ∧ θ i < θ p+R),
          1/(|x p-x i| * D x p i) := by
  obtain ⟨a,ha,hm⟩ := hE.exists_isMinOn hEn (f := fun t => Real.sin (Real.pi*t)) (by fun_prop)
  have hsin : 0 < Real.sin (Real.pi*a) := Real.sin_pos_of_pos_of_lt_pi
    (mul_pos Real.pi_pos (hEi ha).1) (by nlinarith [mul_lt_mul_of_pos_left (hEi ha).2 Real.pi_pos])
  have h₁ := (dyad_tendsto.const_mul (8*Real.pi)).eventually
    (gt_mem_nhds (show (8*Real.pi)*0 < Real.sin (Real.pi*a) by simpa using hsin))
  obtain ⟨K,hK,hKR,hK₀⟩ := (h₁.and ((dyad_tendsto.eventually (gt_mem_nhds hR)).and
    (eventually_ge_atTop (K₀+2)))).exists
  filter_upwards [hc, mesh_small_dyad K, log_logNat_le, eventually_ge_atTop 1]
    with p hpC hpM hpL hp₁ h
  obtain ⟨b,hb,hnear⟩ := h
  have hs := sum_shells hx hθ hmap hden hsin
    (fun b hb => hm (hF hb)) K hK₀ hK.le (by omega) (hM p) (hMp p) hpC hpM hb hnear
  rw [hmap p] at hs
  apply le_trans _ (hs.trans (sum_le_sum_of_subset_of_nonneg ?_ (fun i hi _ => by positivity [D_pos hx p i])))
  · have h := div_le_div_of_nonneg_right hpL (show 0 ≤ 32768*M p by positivity [hM p])
    convert h using 1; ring
  · intro i hi
    obtain ⟨hin,hi₁,hi₂⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hin, hi₁,hi₂.trans_le (by linarith)⟩

/-- Record times remain after excluding the ends of short blocks containing
an exceptional node. -/
theorem record_times (A : ℕ → ℝ) (bad : ℕ → Prop) [DecidablePred bad] {s B : ℕ} (hs : 0 < s)
    (hB : 100*s*s ≤ B)
    (hstep : ∀ n, A (n+1) ≤ A n + 3)
    (hgrow : ∀ᶠ n : ℕ in atTop, (n:ℝ)/(2*s) ≤ A n)
    (hbad : ∀ᶠ n : ℕ in atTop, (((range n).filter bad).card:ℝ) ≤ 4/(B:ℝ)*n) :
    ∃ᶠ n : ℕ in atTop, (∀ p ≤ n, A p ≤ A n) ∧ ∀ p ∈ Ico (n-s) n, ¬bad p := by
  classical
  by_contra h
  obtain ⟨T,hT⟩ := eventually_atTop.mp (not_frequently.mp h)
  let exc := fun j => j+1 < T ∨ ∃ p ∈ Ico (j+1-s) (j+1), bad p
  let b := fun j => if exc j then (3:ℝ) else 0
  have hrec (j : ℕ) (h : ¬exc j) : ∃ p ≤ j, A (j+1) ≤ A p := by
    by_contra! he
    apply hT (j+1) (le_of_not_gt (fun h₁ => h (Or.inl h₁)))
    refine ⟨?_, fun p hp hb => h (Or.inr ⟨p,hp,hb⟩)⟩
    intro p hp
    rcases Nat.eq_or_lt_of_le hp with h|hp
    · rw [h]
    · exact (he p (by omega)).le
  have hb₀ (i : ℕ) : 0 ≤ b i := by unfold b; split <;> norm_num
  have H : ∀ n, ∀ p ≤ n, A p ≤ A 0 + ∑ j ∈ range n, b j := by
    intro n
    induction n with
    | zero => intro p hp; simp [Nat.eq_zero_of_le_zero hp]
    | succ n ih =>
      intro p hp
      rw [sum_range_succ, ← add_assoc]
      rcases Nat.eq_or_lt_of_le hp with rfl|hh
      · by_cases he : exc n
        · rw [show b n = 3 from if_pos he]
          exact (hstep n).trans (add_le_add_left (ih _ le_rfl) _)
        · obtain ⟨q,hq,hle⟩ := hrec n he
          exact hle.trans ((ih _ hq).trans (le_add_of_nonneg_right (hb₀ _)))
      · exact (ih p (Nat.le_of_lt_succ hh)).trans (le_add_of_nonneg_right (hb₀ _))
  have Hc (n : ℕ) : ((range n).filter exc).card ≤ T + s * ((range n).filter bad).card := by
    let U := ((range n).filter bad).biUnion (fun p => Ico p (p+s))
    have hsu : ((range n).filter exc) ⊆ range T ∪ U := by
      intro j hj
      obtain ⟨hjn,hj⟩ := mem_filter.mp hj
      have hj' := mem_range.mp hjn
      rcases hj with hh|⟨p,hp,hbp⟩
      · exact mem_union_left _ (mem_range.mpr (by omega))
      · have hp' := mem_Ico.mp hp
        exact mem_union_right _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem_range.mpr (by omega),hbp⟩,
          mem_Ico.mpr ⟨by omega,by omega⟩⟩)
    have ht : #U ≤ s * #((range n).filter bad) := by
      refine card_biUnion_le.trans_eq ?_
      simp [Nat.card_Ico, mul_comm]
    exact (card_le_card hsu).trans ((card_union_le _ _).trans (by simpa using Nat.add_le_add_left ht T))
  have hf : ∀ n, A n ≤ A 0 + 3*(T+s*(((range n).filter bad).card:ℝ)) := by
    intro n
    have := H n n le_rfl
    have hr : (∑ j ∈ range n, b j) = (3:ℝ)*(((range n).filter exc).card:ℝ) := by
      unfold b
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    rw [hr] at this
    have hn : (((range n).filter exc).card:ℝ) ≤ T+s*(((range n).filter bad).card:ℝ) := by exact_mod_cast Hc n
    linarith only [this, hn]
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  have hBR : (100:ℝ)*(s:ℝ)*(s:ℝ) ≤ B := by exact_mod_cast hB
  have hBp : (0:ℝ) < B := lt_of_lt_of_le (by positivity) hBR
  have hcoef : 12*(s:ℝ)/(B:ℝ) ≤ 1/(4*(s:ℝ)) := by
    rw [div_le_div_iff₀ hBp (by positivity)]
    nlinarith only [hBR, sq_nonneg (s:ℝ)]
  obtain ⟨n,hn₁,hn₂,hn₃⟩ := (hgrow.and (hbad.and
    (tendsto_natCast_atTop_atTop.eventually_gt_atTop (4*(s:ℝ)*(A 0+3*T))))).exists
  have hnn := hf n
  have hun := mul_le_mul_of_nonneg_left hn₂ (show 0 ≤ (3:ℝ)*s by positivity)
  have huu := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (α := ℝ) n)
  have ht' : A 0+3*T < (n:ℝ)/(4*s) := (lt_div_iff₀ (by positivity)).2 (by linarith only [hn₃])
  linarith only [hn₁,hnn,hun,huu,ht',show 3*(s:ℝ)*(4/(B:ℝ)*n)=12*s/B*n by ring,
    show (n:ℝ)/(2*s)=2*(n/(4*s)) by ring, show 1/(4*(s:ℝ))*n=n/(4*s) by ring]

end Erdos1132Proof
end

section
-- InterpBlockSum
open Finset Filter
open scoped BigOperators

namespace Erdos1132Proof

noncomputable def newton (x : ℕ → ℝ) (j : ℕ) : ℝ := ∏ i ∈ range j, (2 * |x j - x i|)

theorem newton_eq (x : ℕ → ℝ) (j : ℕ) : newton x j = (2:ℝ)^j * W x (range j) (x j) := by
  simp [newton, W, prod_mul_distrib]

theorem newton_pos {x : ℕ → ℝ} (hx : Function.Injective x) (j : ℕ) : 0 < newton x j := by
  rw [newton_eq]
  exact mul_pos (by positivity) (W_pos fun i hi he => (Nat.ne_of_lt (mem_range.mp hi)) (hx he).symm)

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]

theorem log_newton_bound {x : ℕ → ℝ} (hx : Function.Injective x)
    (hbox : ∀ i, x i ∈ Set.Icc (-1:ℝ) 1) {s : ℕ} (hs : 2 ≤ s) :
    2 * (∑ i ∈ range s, Real.log (newton x i)) ≤ (s:ℝ) * (Real.log s + 2*Real.log 2) := by
  have hC (i : ℕ) : Real.log (newton x i) = i * Real.log 2 + Real.log (W x (range i) (x i)) := by
    rw [newton_eq, Real.log_mul (by positivity) (W_pos (fun k hk he =>
      (Nat.ne_of_lt (mem_range.mp hk)) (hx he).symm)).ne', Real.log_pow]
  simp_rw [hC]
  rw [sum_add_distrib, mul_add, newton_log_sum hx, ← sum_mul]
  have hI : (∑ i ∈ range s, (i:ℝ)) * 2 = (s:ℝ)*((s:ℝ)-1) := by
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_sub (show 1 ≤ s by omega), Nat.cast_one] using
        congrArg (fun m : ℕ => (m:ℝ)) (sum_range_id_mul_two s)
  have hD := log_prod_D hx hbox (show 0 < s by omega)
  have hsub : (s-1)*2 ≤ s*(s-1) := by simpa [Nat.mul_comm] using Nat.mul_le_mul_right (s-1) hs
  push_cast [Nat.cast_sub hsub, Nat.cast_sub (by omega : 1 ≤ s)] at hD
  have hb : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linear_combination hD + Real.log 2 * hI + 2 * hb

/-- In a long block, the reciprocals of the normalized Newton products have
large total mass, regardless of the order of the nodes. -/
theorem newton_inv_sum {x : ℕ → ℝ} (hx : Function.Injective x)
    (hbox : ∀ i, x i ∈ Set.Icc (-1:ℝ) 1) {s : ℕ} (hs : 2 ≤ s)
    {k : ℝ} (hk : 0 < k) (hbig : 4*k^2 < (s:ℝ)) :
    k < ∑ i ∈ range s, (newton x i)⁻¹ := by
  by_contra! hsum
  have hsR : 0 < (s:ℝ) := by exact_mod_cast (show 0 < s by omega)
  let a : ℝ := (s:ℝ)/k
  have ha : 0 < a := div_pos hsR hk
  have hsum₁ : (s:ℝ) * Real.log a - (∑ i ∈ range s, Real.log (newton x i)) ≤
      a * (∑ i ∈ range s, (newton x i)⁻¹) - s := by
    have h : ∑ i ∈ range s, (Real.log a - Real.log (newton x i)) ≤
        ∑ i ∈ range s, (a * (newton x i)⁻¹ - 1) := by
      apply sum_le_sum
      intro i _
      have hpos := newton_pos hx i
      have hi := Real.log_le_sub_one_of_pos (div_pos ha hpos)
      rwa [Real.log_div ha.ne' hpos.ne', div_eq_mul_inv] at hi
    simpa only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one, ← mul_sum] using h
  have hsum₂ := mul_le_mul_of_nonneg_left hsum ha.le
  have heq : a*k = s := div_mul_cancel₀ (s:ℝ) hk.ne'
  have hupper := log_newton_bound hx hbox hs
  have hh : 4*(s:ℝ) < a^2 := by
    dsimp [a]
    rw [div_pow, lt_div_iff₀ (by positivity)]
    linear_combination (s:ℝ) * hbig
  have hlog := Real.log_lt_log (by positivity : 0 < 4*(s:ℝ)) hh
  rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hsR.ne',
    show (4:ℝ) = (2:ℝ)^2 by norm_num, Real.log_pow, Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hl := mul_lt_mul_of_pos_left hlog hsR
  linarith only [hsum₁, hsum₂, heq, hupper, hl]

/-- Reverse the first `n` indices, leaving the rest fixed. -/
def revIndex (n i : ℕ) : ℕ := if i < n then n-1-i else i

theorem revIndex_of_lt {n i : ℕ} (hi : i < n) : revIndex n i = n-1-i := if_pos hi

theorem revIndex_involutive (n : ℕ) : Function.Involutive (revIndex n) := by
  intro i
  by_cases h : i < n
  · rw [revIndex_of_lt h, revIndex_of_lt (show n-1-i < n by omega)]
    omega
  · simp [revIndex, h]

noncomputable def laterProduct (x : ℕ → ℝ) (n p : ℕ) : ℝ :=
  ∏ q ∈ Ico (p+1) n, (2 * |x p - x q|)

theorem rev_newton (x : ℕ → ℝ) {n j : ℕ} (hj : j < n) :
    newton (x ∘ revIndex n) j = laterProduct x n (revIndex n j) := by
  unfold newton laterProduct
  refine prod_bij (fun i _ => revIndex n i) ?_ ?_ ?_ ?_
  · intro i hi
    have hi' := mem_range.mp hi
    rw [revIndex_of_lt (hi'.trans hj), revIndex_of_lt hj, mem_Ico]
    omega
  · exact fun _ _ _ _ h => (revIndex_involutive n).injective h
  · intro q hq
    rw [mem_Ico, revIndex_of_lt hj] at hq
    refine ⟨revIndex n q, mem_range.mpr ?_, revIndex_involutive n q⟩
    rw [revIndex_of_lt hq.2]
    omega
  · intros; rfl

theorem later_inv_sum {x : ℕ → ℝ} (hx : Function.Injective x)
    (hbox : ∀ i, x i ∈ Set.Icc (-1:ℝ) 1) {s n : ℕ} (hs : 2 ≤ s) (hsn : s ≤ n)
    {k : ℝ} (hk : 0 < k) (hbig : 4*k^2 < (s:ℝ)) :
    k < ∑ p ∈ Ico (n-s) n, (laterProduct x n p)⁻¹ := by
  have h := newton_inv_sum (hx.comp (revIndex_involutive n).injective)
    (fun i => hbox (revIndex n i)) hs hk hbig
  refine h.trans_le (le_of_eq ?_)
  refine sum_bij (fun i _ => revIndex n i) ?_ ?_ ?_ ?_
  · intro i hi
    have hi' := mem_range.mp hi
    rw [revIndex_of_lt (hi'.trans_le hsn), mem_Ico]
    omega
  · exact fun _ _ _ _ h => (revIndex_involutive n).injective h
  · intro p hp
    rw [mem_Ico] at hp
    refine ⟨revIndex n p, mem_range.mpr ?_, revIndex_involutive n p⟩
    rw [revIndex_of_lt hp.2]
    omega
  · intro i hi
    rw [rev_newton x ((mem_range.mp hi).trans_le hsn)]

theorem record_bound {M : ℕ → ℝ} (hM : ∀ n, 0 < M n) {s n p : ℕ}
    (hs : 0 < s) (hp : p ∈ Ico (n-s) n)
    (hrec : Real.log (M p) + p * Real.log 2 + (p:ℝ)/s ≤
      Real.log (M n) + n * Real.log 2 + (n:ℝ)/s) :
    M p ≤ 4 * (2:ℝ)^(n-p) * M n := by
  have hp' := mem_Ico.mp hp
  have hnps : ((n-p:ℕ):ℝ) ≤ s := by exact_mod_cast (show n-p ≤ s by omega)
  have hsR : 0 < (s:ℝ) := by exact_mod_cast hs
  have h' : ((n-p:ℕ):ℝ)/s ≤ 1 := (div_le_one hsR).2 hnps
  rw [Nat.cast_sub hp'.2.le] at h'
  have hf : Real.log (M p) ≤ Real.log (((2:ℝ)^(n-p))*M n) + 1 := by
    rw [Real.log_mul (by positivity) (hM n).ne', Real.log_pow, Nat.cast_sub hp'.2.le]
    linarith only [hrec, h', show ((n:ℝ)-p)/s = (n:ℝ)/s-p/s by ring]
  have hg := Real.exp_le_exp.mpr hf
  rw [Real.exp_log (hM p), Real.exp_add, Real.exp_log (by positivity [hM n])] at hg
  calc
    M p ≤ (2:ℝ)^(n-p)*M n * Real.exp 1 := hg
    _ ≤ (2:ℝ)^(n-p)*M n * 4 := mul_le_mul_of_nonneg_left
      (Real.exp_one_lt_three.le.trans (by norm_num)) (by positivity [hM n])
    _ = 4 * (2:ℝ)^(n-p)*M n := by ring

end Erdos1132Proof
end

section
-- InterpTransfer
open Finset Filter
open scoped BigOperators

namespace Erdos1132Proof

/-- A uniform bound on how much a product of bounded nonnegative factors can
increase if each factor increases by at most `d`. -/
theorem prod_near_le {α : Type*} (J : Finset α) {v w : α → ℝ} {d : ℝ} (hd : 0 ≤ d)
    (hv : ∀ j ∈ J, 0 ≤ v j ∧ v j ≤ 4) (hw : ∀ j ∈ J, 0 ≤ w j ∧ w j ≤ 4)
    (hvw : ∀ j ∈ J, v j ≤ w j+d) :
    ∏ j ∈ J, v j ≤ (∏ j ∈ J, w j) + d*(J.card:ℝ)*4^J.card := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | insert j J hj ih =>
    have hv' := hv j (mem_insert_self j J)
    have hw' := hw j (mem_insert_self j J)
    have h' := hvw j (mem_insert_self j J)
    let P := ∏ i ∈ J, w i
    let e : ℝ := d*(J.card:ℝ)*4^J.card
    have hP : 0 ≤ P := prod_nonneg (fun i hi => (hw i (mem_insert_of_mem hi)).1)
    have hP' : P ≤ (4:ℝ)^J.card := by
      simpa [P] using prod_le_prod (s := J) (fun i hi => (hw i (mem_insert_of_mem hi)).1)
        (fun i hi => (hw i (mem_insert_of_mem hi)).2)
    have he : 0 ≤ e := by dsimp [e]; positivity
    have hi := ih (fun i hi => hv i (mem_insert_of_mem hi))
      (fun i hi => hw i (mem_insert_of_mem hi)) (fun i hi => hvw i (mem_insert_of_mem hi))
    rw [prod_insert hj, prod_insert hj, card_insert_of_notMem hj]
    calc
      _ ≤ v j * (P+e) := mul_le_mul_of_nonneg_left hi hv'.1
      _ = v j * P + v j * e := mul_add ..
      _ ≤ (w j+d)*P + 4*e := add_le_add (mul_le_mul_of_nonneg_right h' hP)
        (mul_le_mul_of_nonneg_right hv'.2 he)
      _ ≤ _ := by
        have h₁ := mul_le_mul_of_nonneg_left hP' hd
        have h₂ : 0 ≤ d*(4:ℝ)^J.card := by positivity
        rw [Nat.cast_succ, pow_succ]
        dsimp only [e]
        nlinarith only [h₁,h₂]


noncomputable def blockRadius (s : ℕ) : ℝ := ((1/67108864:ℝ)) / (8*((s:ℝ)+1)*4^s)

theorem blockRadius_pos (s : ℕ) : 0 < blockRadius s := by unfold blockRadius; positivity

theorem blockRadius_small (s : ℕ) :
    2 * blockRadius s * s * (4:ℝ)^s ≤ ((1/67108864:ℝ)) ∧ 4 * blockRadius s * (4:ℝ)^s < ((1/67108864:ℝ)) := by
  have h : blockRadius s * (4:ℝ)^s * (8*((s:ℝ)+1)) = ((1/67108864:ℝ)) := by
    unfold blockRadius
    have hs : (s:ℝ)+1 ≠ 0 := by positivity
    have hp : (4:ℝ)^s ≠ 0 := by positivity
    field_simp [hs, hp]
  have h₀ := mul_pos (blockRadius_pos s) (show (0:ℝ) < (4:ℝ)^s by positivity)
  have h₁ := mul_nonneg h₀.le (Nat.cast_nonneg (α := ℝ) s)
  constructor <;> nlinarith only [h,h₀,h₁]

theorem laterProduct_nonneg (x : ℕ → ℝ) (n p : ℕ) : 0 ≤ laterProduct x n p :=
  prod_nonneg (fun _ _ => by positivity)

theorem later_product_near {x : ℕ → ℝ} (hbox : ∀ j, x j ∈ Set.Icc (-1:ℝ) 1)
    {s n p i : ℕ} (hp : p ∈ Ico (n-s) n) (hi : |x i - x p| ≤ blockRadius s) :
    ∏ q ∈ Ico (p+1) n, (2*|x i-x q|) ≤ laterProduct x n p + ((1/67108864:ℝ)) := by
  have hp' := mem_Ico.mp hp
  let J := Ico (p+1) n
  have hJ : J.card ≤ s := by dsimp [J]; rw [Nat.card_Ico]; omega
  have hg (a q : ℕ) : 0 ≤ 2*|x a - x q| ∧ 2*|x a - x q| ≤ 4 :=
    ⟨by positivity, by linarith [abs_sub_le_two (hbox a) (hbox q)]⟩
  have H := prod_near_le J (v := fun q => 2*|x i-x q|) (w := fun q => 2*|x p-x q|)
    (d := 2*blockRadius s) (by positivity [blockRadius_pos s])
    (fun q _ => hg i q) (fun q _ => hg p q)
    (fun q _ => by linarith only [hi, abs_sub_le (x i) (x p) (x q)])
  apply H.trans
  change laterProduct x n p + 2 * blockRadius s * (J.card:ℝ) * (4:ℝ)^J.card ≤ _
  refine add_le_add_right (le_trans ?_ (blockRadius_small s).1) _
  have hJR : (J.card:ℝ) ≤ s := by exact_mod_cast hJ
  have hr := (blockRadius_pos s).le
  exact mul_le_mul (mul_le_mul_of_nonneg_left hJR (by positivity))
    (pow_le_pow_right₀ (by norm_num) hJ) (by positivity) (by positivity)

theorem expanded_denom {x : ℕ → ℝ} (hx : Function.Injective x)
    (hbox : ∀ j, x j ∈ Set.Icc (-1:ℝ) 1) {s n p i : ℕ} (hp : p ∈ Ico (n-s) n)
    (hip : i < p) (hi : |x i-x p| ≤ blockRadius s) {z : ℝ} (hz : z ∈ Set.Icc (-1:ℝ) 1) :
    (|z-x i| * D x n i) * (2:ℝ)^(n-p) ≤
      4 * (laterProduct x n p + ((1/67108864:ℝ))) * (|x p-x i| * D x p i) := by
  have hp' := mem_Ico.mp hp
  have hco : Ico p n = insert p (Ico (p+1) n) := by
    ext q
    simp only [mem_Ico, mem_insert]
    omega
  have hd := D_split x hip hp'.2.le
  rw [hco, W, prod_insert (by simp)] at hd
  change D x n i = D x p i * (|x i-x p| * W x (Ico (p+1) n) (x i)) at hd
  have H : ∏ q ∈ Ico (p+1) n, (2*|x i-x q|) =
      (2:ℝ)^(n-(p+1)) * W x (Ico (p+1) n) (x i) := by
    simp [W, prod_mul_distrib, Nat.card_Ico]
  have hn : n-p = n-(p+1)+1 := by omega
  calc
    _ = (2*|z-x i|) * (|x p-x i| * D x p i) * (∏ q ∈ Ico (p+1) n, (2 * |x i-x q|)) := by
      rw [hd, H, hn, pow_succ, abs_sub_comm (x p) (x i)]
      ring
    _ ≤ 4 * (|x p-x i| * D x p i) * (laterProduct x n p + ((1/67108864:ℝ))) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_right ?_ (by positivity [D_pos hx p i]))
        (later_product_near hbox hp hi) (prod_nonneg fun _ _ => by positivity) (by positivity [D_pos hx p i])
      linarith [abs_sub_le_two hz (hbox i)]
    _ = _ := by ring

/-- At a product-norm record, the small-scale contributions of the recent
nodes transfer to one and the same Lebesgue function. The norm bound first
forces these neighbourhoods to be disjoint; then the reverse Newton sum
forces their aggregate contribution to be too large. -/
theorem block_contradiction {x : ℕ → ℝ} (hx : Function.Injective x)
    (hbox : ∀ i, x i ∈ Set.Icc (-1:ℝ) 1) {s n : ℕ} (hs : 2 ≤ s) (hsn : s ≤ n)
    (hbig : 4*(67108864:ℝ)^2 < (s:ℝ)) {M : ℕ → ℝ} (hM : ∀ p, 0 < M p)
    {z : ℝ} (hz : z ∈ Set.Icc (-1:ℝ) 1) (hzW : W x (range n) z = M n)
    (hL : Erdos1132Proof.lebesgueFunctionL n x z ≤ Real.log n)
    (hrec : ∀ p ∈ Ico (n-s) n, M p ≤ 4*(2:ℝ)^(n-p)*M n)
    (hlog : ∀ p ∈ Ico (n-s) n, Real.log n/2 ≤ Real.log p)
    {S : ℕ → Finset ℕ} (hS : ∀ p ∈ Ico (n-s) n, ∀ i ∈ S p,
      i < p ∧ |x i-x p| ≤ blockRadius s)
    (hmass : ∀ p ∈ Ico (n-s) n, Real.log p/(1048576*M p) ≤
      ∑ i ∈ S p, 1/(|x p-x i| * D x p i)) : False := by
  classical
  let J := Ico (n-s) n
  let b := fun i => |Erdos1132Proof.lagrangeBasisL n x i z|
  let A := fun p => ∑ i ∈ S p, b i
  let U := laterProduct x n
  have hLn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hSsub (p : ℕ) (hp : p ∈ J) : S p ⊆ range n := fun i hi =>
    mem_range.mpr ((hS p hp i hi).1.trans (mem_Ico.mp hp).2)
  have hA (p : ℕ) (hp : p ∈ J) : A p ≤ Real.log n :=
    (sum_le_sum_of_subset_of_nonneg (hSsub p hp) (fun _ _ _ => abs_nonneg _)).trans hL
  have hm (p : ℕ) (hp : p ∈ J) : 2*((1/67108864:ℝ))*Real.log n ≤ (U p+((1/67108864:ℝ)))*A p := by
    have hpt (i : ℕ) (hi : i ∈ S p) :
        M p * (1/(|x p-x i| * D x p i)) ≤ 16*(U p+((1/67108864:ℝ)))*b i := by
      have ⟨hip,hi'⟩ := hS p hp i hi
      have hb : b i * (|z-x i| * D x n i) = M n :=
        (abs_basis_mul x hx (hip.trans (mem_Ico.mp hp).2) z).trans hzW
      have hv : 0 < |x p-x i| * D x p i := mul_pos
        (abs_pos.mpr (sub_ne_zero.mpr (hx.ne (Nat.ne_of_lt hip).symm))) (D_pos hx p i)
      rw [mul_one_div, div_le_iff₀ hv]
      calc
        M p ≤ 4 * (2:ℝ)^(n-p) * M n := hrec p hp
        _ = (4*b i) * ((|z-x i| * D x n i) * (2:ℝ)^(n-p)) := by rw [← hb]; ring
        _ ≤ (4*b i) * (4*(U p+((1/67108864:ℝ))) * (|x p-x i| * D x p i)) :=
          mul_le_mul_of_nonneg_left (expanded_denom hx hbox hp hip hi' hz) (by dsimp [b]; positivity)
        _ = _ := by ring
    have ht := mul_le_mul_of_nonneg_left (hmass p hp) (hM p).le
    rw [mul_sum, show M p * (Real.log p/(1048576*M p)) = Real.log p/1048576 by
      field_simp [(hM p).ne']] at ht
    have hh := ht.trans (sum_le_sum hpt)
    rw [← mul_sum] at hh
    change Real.log p/1048576 ≤ 16*(U p+((1/67108864:ℝ)))*A p at hh
    linarith only [hh, hlog p hp]
  have hU (p : ℕ) (hp : p ∈ J) : ((1/67108864:ℝ)) ≤ U p := by
    have ht := (hm p hp).trans (mul_le_mul_of_nonneg_left (hA p hp)
      (add_nonneg (laterProduct_nonneg x n p) (by positivity)))
    have hh := le_of_mul_le_mul_right ht hLn
    linarith only [hh]
  have hdisj : (J : Set ℕ).PairwiseDisjoint S := by
    intro p hp q hq hpq
    wlog hpq' : p < q generalizing p q
    · exact (this hq hp hpq.symm (by omega)).symm
    apply disjoint_left.mpr
    intro i hi hi'
    have hpn := mem_Ico.mp hp
    have hqn := mem_Ico.mp hq
    have hclose : |x p-x q| ≤ 2*blockRadius s := by
      linarith only [abs_sub_le (x p) (x i) (x q), abs_sub_comm (x p) (x i),
        (hS p hp i hi).2, (hS q hq i hi').2]
    let I := Ico (p+1) n
    have hqI : q ∈ I := mem_Ico.mpr ⟨by omega, hqn.2⟩
    have hIc : I.card ≤ s := by dsimp [I]; rw [Nat.card_Ico]; omega
    have hprod : ∏ j ∈ I.erase q, (2*|x p-x j|) ≤ (4:ℝ)^s := by
      calc
        _ ≤ ∏ _j ∈ I.erase q, (4:ℝ) := prod_le_prod (fun _ _ => by positivity)
          (fun j _ => by linarith [abs_sub_le_two (hbox p) (hbox j)])
        _ = (4:ℝ)^(I.erase q).card := prod_const _
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) (card_erase_le.trans hIc)
    have hab : U p ≤ 4*blockRadius s*(4:ℝ)^s := by
      change (∏ j ∈ I, (2*|x p-x j|)) ≤ _
      rw [← mul_prod_erase _ _ hqI]
      exact mul_le_mul (by linarith only [hclose]) hprod
        (prod_nonneg fun _ _ => by positivity) (by positivity [blockRadius_pos s])
    exact (not_lt_of_ge (hU p hp)) (hab.trans_lt (blockRadius_small s).2)
  have hinv (p : ℕ) (hp : p ∈ J) : ((1/67108864:ℝ))*Real.log n * (U p)⁻¹ ≤ A p := by
    rw [← div_eq_mul_inv, div_le_iff₀ (lt_of_lt_of_le (by positivity) (hU p hp))]
    have H := (hm p hp).trans (mul_le_mul_of_nonneg_right (show U p+((1/67108864:ℝ)) ≤ 2*U p by
      linarith only [hU p hp]) (sum_nonneg fun _ _ => abs_nonneg _))
    change 2*((1/67108864:ℝ))*Real.log n ≤ 2*U p*A p at H
    linarith only [H]
  have hsum : ∑ p ∈ J, (U p)⁻¹ ≤ 67108864 := by
    apply le_of_mul_le_mul_left _ (show 0 < ((1/67108864:ℝ))*Real.log n by positivity)
    rw [mul_sum]
    calc
      _ ≤ ∑ p ∈ J, A p := sum_le_sum hinv
      _ = ∑ i ∈ J.biUnion S, b i := (sum_biUnion hdisj).symm
      _ ≤ Erdos1132Proof.lebesgueFunctionL n x z := sum_le_sum_of_subset_of_nonneg
        (fun i hi => let ⟨p,hp,hi⟩ := mem_biUnion.mp hi; hSsub p hp hi) (fun _ _ _ => abs_nonneg _)
      _ ≤ _ := by linarith only [hL]
  exact (not_lt_of_ge hsum) (later_inv_sum hx hbox hs hsn (by norm_num) hbig)

end Erdos1132Proof
end

section
-- InterpConclusion
open Finset Filter MeasureTheory
open scoped BigOperators Topology ENNReal

namespace Erdos1132Proof

theorem norm_record_growth {M : ℕ → ℝ} {s B : ℕ} (hs : 0 < s) (hB : 20*s ≤ B)
    (h : ∀ᶠ n : ℕ in atTop, -(1+10/(B:ℝ))*n*Real.log 2 ≤ Real.log (M n)) :
    ∀ᶠ n : ℕ in atTop, (n:ℝ)/(2*s) ≤ Real.log (M n) + n*Real.log 2 + (n:ℝ)/s := by
  have hsR : 0 < (s:ℝ) := by exact_mod_cast hs
  have hBR : 20*(s:ℝ) ≤ B := by exact_mod_cast hB
  have hBp : 0 < (B:ℝ) := (mul_pos (by norm_num) hsR).trans_le hBR
  have hc : 10/(B:ℝ) * Real.log 2 ≤ 1/(2*(s:ℝ)) := calc
    _ ≤ 10/(B:ℝ) * 1 := mul_le_mul_of_nonneg_left log_two_le_one (by positivity)
    _ = 10/(B:ℝ) := mul_one _
    _ ≤ _ := by rw [div_le_div_iff₀ hBp (by positivity)]; linarith only [hBR]
  filter_upwards [h] with n hn
  have he := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (α := ℝ) n)
  calc
    _ = (n:ℝ)/s - (1/(2*(s:ℝ)))*n := by ring
    _ ≤ (n:ℝ)/s - (10/(B:ℝ)*Real.log 2)*n := sub_le_sub_left he _
    _ ≤ _ := by linarith only [hn]

theorem norm_record_step {x : ℕ → ℝ} (hbox : ∀ i, x i ∈ Set.Icc (-1:ℝ) 1)
    {E : Set ℝ} {M : ℕ → ℝ} (hM : ∀ n, 0 < M n)
    (hMe : ∀ n, (∃ a ∈ E, W x (range n) (angleMap a) = M n) ∧
        ∀ a ∈ E, W x (range n) (angleMap a) ≤ M n) {s : ℕ} (hs : 0 < s) (n : ℕ) :
    Real.log (M (n+1)) + (↑(n+1):ℝ)*Real.log 2 + (↑(n+1):ℝ)/s ≤
      (Real.log (M n) + n*Real.log 2 + (n:ℝ)/s) + 3 := by
  obtain ⟨a,ha,he⟩ := (hMe (n+1)).1
  have hle : M (n+1) ≤ 2*M n := by
    rw [← he, W_succ, mul_comm (2:ℝ)]
    exact mul_le_mul ((hMe n).2 a ha) (abs_sub_le_two (angleMap_mem a) (hbox n))
      (abs_nonneg _) (hM n).le
  have hl := Real.log_le_log (hM (n+1)) hle
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (hM n).ne'] at hl
  have hinv : (1:ℝ)/(s:ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hs)).2
    (by exact_mod_cast (show 1 ≤ s by omega))
  push_cast
  linarith only [hl, log_two_le_one, hinv, show ((n:ℝ)+1)/s = (n:ℝ)/s+1/s by ring]

open Classical in
theorem bad_count {θ : ℕ → ℝ} {F : Set ℝ} {B : ℕ}
    (h : ∀ᶠ n : ℕ in atTop,
      (1-4/(B:ℝ))*n ≤ (((range n).filter fun i => ∃ a ∈ F, |θ i-a| < mesh n).card : ℝ)) :
    ∀ᶠ n : ℕ in atTop, (((range n).filter (fun i =>
      0 < i ∧ ¬ ∃ a ∈ F, |θ i-a| < mesh i)).card : ℝ) ≤ 4/(B:ℝ)*n := by
  classical
  filter_upwards [h] with n hn
  let good := fun i => ∃ a ∈ F, |θ i-a| < mesh n
  let bad := fun i => 0 < i ∧ ¬ ∃ a ∈ F, |θ i-a| < mesh i
  have hsub : (range n).filter bad ⊆ (range n).filter (fun i => ¬ good i) := by
    intro i hi
    obtain ⟨hin,hip,hib⟩ := mem_filter.mp hi
    refine mem_filter.mpr ⟨hin, ?_⟩
    rintro ⟨a,ha,hd⟩
    exact hib ⟨a,ha,hd.trans_le (mesh_anti hip (mem_range.mp hin).le)⟩
  have hs : (((range n).filter bad).card:ℝ) ≤ (((range n).filter (fun i => ¬ good i)).card:ℝ) := by
    exact_mod_cast card_le_card hsub
  have he := card_filter_add_card_filter_not (s := range n) good
  rw [card_range] at he
  have heR : (((range n).filter good).card:ℝ) + (((range n).filter (fun i => ¬ good i)).card:ℝ) = n := by
    exact_mod_cast he
  change (1-4/(B:ℝ))*n ≤ (((range n).filter good).card : ℝ) at hn
  change (((range n).filter bad).card : ℝ) ≤ _
  linarith only [hn,hs,heR]

theorem past_half_log {s n p : ℕ} (hn : 2*s+4 ≤ n) (hp : p ∈ Ico (n-s) n) :
    Real.log n/2 ≤ Real.log p := by
  have hh := mem_Ico.mp hp
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast (show 2 ≤ p by omega)
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnp : (n:ℝ) ≤ 2*(p:ℝ) := by exact_mod_cast (show n ≤ 2*p by omega)
  have hlog := Real.log_le_log hnR (show (n:ℝ) ≤ (p:ℝ)^2 by
    nlinarith only [hnp, mul_nonneg (sub_nonneg.mpr hpR) (Nat.cast_nonneg (α := ℝ) p)])
  rw [Real.log_pow, Nat.cast_ofNat] at hlog
  linarith only [hlog]

/-- A logarithmic bound cannot hold eventually at every interior point for
the successive prefixes of one sequence of distinct nodes. -/
private theorem not_eventually_log_aux {x : ℕ → ℝ} (hx : Function.Injective x)
    (hbox : ∀ i, x i ∈ Set.Icc (-1:ℝ) 1)
    {s B : ℕ} (hs : 2 ≤ s) (hbig : 4*(67108864:ℝ)^2 < (s:ℝ))
    (hB : 8 ≤ B) (hB' : 20*s ≤ B) (hBrec : 100*s*s ≤ B)
    (h : ∀ a ∈ Set.Ioo (0:ℝ) 1,
      ∀ᶠ n : ℕ in atTop, Erdos1132Proof.lebesgueFunctionL n x (angleMap a) ≤ Real.log n) : False := by
  classical
  choose θ hθ hmap using fun i => angle_exists (hbox i)
  have hsp : 0 < s := by omega
  have hBR : (8:ℝ) ≤ B := by exact_mod_cast hB
  have hBp : 0 < (B:ℝ) := by linarith
  have hε : 0 < 1/(B:ℝ) := by positivity
  obtain ⟨E,hE,hEi,hvol,hL⟩ := large_E x h hε
  have hEJ := hEi.trans Set.Ioo_subset_Icc_self
  have hEm := hE.isClosed.measurableSet
  have hEn : 0 < volume E := by
    by_contra! he
    have hzero : volume E = 0 := le_antisymm he zero_le
    have H := measure_union_le (μ := volume) (Set.Icc (0:ℝ) 1 \ E) E
    rw [Set.sdiff_union_of_subset hEJ, hzero, add_zero, Real.volume_Icc, sub_zero, ENNReal.ofReal_one] at H
    have hsmall : ENNReal.ofReal (1/(B:ℝ)) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal ((div_le_one hBp).2 (by linarith))
    exact (not_lt_of_ge H) (hvol.trans_le hsmall)
  obtain ⟨F,hFm,hFE,hFvol,K₀,hden⟩ := density_centres hEm hEi hε hvol
  obtain ⟨M,hM,hMe⟩ := maxW (x := x) hE hEn hEJ
  have hMp : ∀ n a, a ∈ E → W x (range n) (angleMap a) ≤ M n := fun n => (hMe n).2
  have hEn' : E.Nonempty := by
    obtain ⟨a,ha,_⟩ := (hMe 0).1
    exact ⟨a,ha⟩
  let A := fun n : ℕ => Real.log (M n) + n*Real.log 2 + (n:ℝ)/s
  let bad := fun p => 0 < p ∧ ¬ ∃ a ∈ F, |θ p-a| < mesh p
  have hstep : ∀ n, A (n+1) ≤ A n+3 := norm_record_step hbox hM hMe hsp
  have hnorm := large_norm (x := x) (E := E) (M := M) (B := B) hEm hB hvol hMp
  have hgrow : ∀ᶠ n : ℕ in atTop, (n:ℝ)/(2*s) ≤ A n := norm_record_growth hsp hB' hnorm
  have hnear := count_near (x := x) (θ := θ) (E := E) (F := F) (B := B) hx hθ hmap hEJ hFE hFm hB hFvol hL
  have hbad : ∀ᶠ n : ℕ in atTop, (((range n).filter bad).card:ℝ) ≤ 4/(B:ℝ)*n := bad_count hnear
  have hrecord := record_times A bad hsp hBrec hstep hgrow hbad
  let R := blockRadius s / Real.pi
  have hR : 0 < R := div_pos (blockRadius_pos s) Real.pi_pos
  obtain ⟨N,hN⟩ := eventually_atTop.mp (local_mass hx hθ hmap hE hEi hEn' hFE hden hM hMp
    (eventually_mesh_cover hx hθ hmap hEJ hL) hR)
  obtain ⟨n,⟨hnRec,hnGood⟩,hnL,hnLarge⟩ :=
    (hrecord.and_eventually (hL.and (eventually_ge_atTop (N+3*s+4)))).exists
  obtain ⟨a,ha,haW⟩ := (hMe n).1
  let S := fun p => (range p).filter (fun i => θ p < θ i ∧ θ i < θ p+R)
  refine block_contradiction hx hbox hs (by omega) hbig hM (angleMap_mem a) haW (hnL a ha)
    (fun p hp => record_bound hM hsp hp (hnRec p (mem_Ico.mp hp).2.le))
    (fun p hp => past_half_log (s := s) (n := n) (by omega) hp) (S := S) ?_ ?_
  · intro p hp i hi
    obtain ⟨hi,hi₁,hi₂⟩ := mem_filter.mp hi
    refine ⟨mem_range.mp hi, ?_⟩
    have hθd : |θ i-θ p| ≤ R := abs_le.mpr ⟨by linarith, by linarith⟩
    have hd := angle_sep_le (θ i) (θ p)
    rw [hmap i, hmap p] at hd
    exact hd.trans ((mul_le_mul_of_nonneg_left hθd Real.pi_pos.le).trans_eq
      (by dsimp [R]; rw [mul_comm, div_mul_cancel₀ _ Real.pi_ne_zero]))
  · intro p hp
    have hp' := mem_Ico.mp hp
    apply hN p (by omega)
    by_contra hb
    exact hnGood p hp ⟨by omega,hb⟩

theorem not_eventually_log {x : ℕ → ℝ} (hx : Function.Injective x)
    (hbox : ∀ i, x i ∈ Set.Icc (-1:ℝ) 1)
    (h : ∀ a ∈ Set.Ioo (0:ℝ) 1,
      ∀ᶠ n : ℕ in atTop, Erdos1132Proof.lebesgueFunctionL n x (angleMap a) ≤ Real.log n) : False := by
  let s : ℕ := 2^56
  let B : ℕ := 100*s*s
  exact not_eventually_log_aux hx hbox (s := s) (B := B)
    (by norm_num [s]) (by norm_num [s]) (by norm_num [B,s]) (by norm_num [B,s]) le_rfl h

end Erdos1132Proof
end

section
-- Main
open Filter

theorem OMA.solution : type_of% @Erdos1132.erdos_1132.parts.i := by
  rw [Erdos1132Proof.lebesgueFunction_eq]
  intro x hbox hx
  have he : ∃ a ∈ Set.Ioo (0:ℝ) 1, ∃ᶠ n : ℕ in atTop,
      Real.log n < Erdos1132Proof.lebesgueFunctionL n x (Erdos1132Proof.angleMap a) := by
    by_contra h
    apply Erdos1132Proof.not_eventually_log hx hbox
    intro a ha
    exact (not_frequently.mp (fun hf => h ⟨a,ha,hf⟩)).mono (fun _ hn => le_of_not_gt hn)
  obtain ⟨a,ha,h⟩ := he
  refine ⟨Erdos1132Proof.angleMap a, Erdos1132Proof.angleMap_interior ha, 0, ?_⟩
  refine (h.and_eventually (eventually_ge_atTop 1)).mono fun n ⟨hn,hn₁⟩ => ?_
  have hπ : 2 / Real.pi ≤ 1 := (div_le_one Real.pi_pos).2 (by linarith [Real.one_le_pi_div_two])
  have hn₀ : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn₁)
  rw [sub_zero]
  exact (mul_le_of_le_one_left hn₀ hπ).trans_lt hn
end
