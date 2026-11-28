import OMAReductions.R_Arxiv_2501_03234_conjecture_4_4_R1
import Mathlib.Tactic

/-!
Independent proof of the analytic step of the theta-sum growth reduction.
No external proof code or certificate data is ported. This proves the exact
step only; the uniform arithmetic overshoot hypothesis remains open.

Context: Berndt, Bhat, Meyer, Xie, Zaharescu, An Arithmetic Sum Associated
with the Classical Theta Function, Results in Mathematics81:25(2026),
DOI10.1007/s00025-025-02584-2 (refereed); Alessandro Lageler, Continued
fractions and Hardy sums, DOI10.1007/s12188-024-00283-3 (refereed).
Related site context: @sebastianbachmaier PR#6138 (ECF recurrence);
@LordMike PR#12031 (the separate finite/large split for conjecture4.3).
All new arguments and Lean code are independently authored in this workspace.
-/

namespace ThetaLongHaul

def ecfPrefix : ℕ → ℕ → ℕ → ℤ
  | 0, _, _ => 0
  | t+1, a, b => if a=0 then 0 else
      1-if b%(2*a)<a then ecfPrefix t (b%(2*a)) a
        else -ecfPrefix t (2*a-b%(2*a)) a

def depthPrefixSum (t p : ℕ) : ℤ :=
  ∑ a ∈ (Finset.Ico 1 p).filter Even, ecfPrefix t a p

namespace RealECF
noncomputable section

def residue (x : ℝ) : ℝ := x⁻¹-2*(⌊x⁻¹/2⌋₊ : ℕ)

def realPrefix : ℕ → ℝ → ℝ
  | 0, _ => 0
  | t+1, x => if x=0 then 0 else
      if residue x<1 then 1-realPrefix t (residue x)
      else 1+realPrefix t (2-residue x)
end
end RealECF
end ThetaLongHaul

namespace ThetaLongHaul.RealECF
noncomputable section
open MeasureTheory
lemma residue_measurable : Measurable residue := by
  unfold residue
  fun_prop

lemma prefix_measurable (t : ℕ) : Measurable (realPrefix t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    change Measurable (fun x : ℝ => if x = 0 then 0 else
      if residue x < 1 then 1-realPrefix t (residue x) else 1+realPrefix t (2-residue x))
    apply Measurable.ite (measurableSet_singleton (0 : ℝ))
    · exact measurable_const
    · apply Measurable.ite (measurableSet_lt residue_measurable measurable_const)
      · exact measurable_const.sub (ih.comp residue_measurable)
      · exact measurable_const.add (ih.comp (measurable_const.sub residue_measurable))

lemma prefix_abs_le (t : ℕ) (x : ℝ) : |realPrefix t x| ≤ (t : ℝ) := by
  induction t generalizing x with
  | zero => simp [realPrefix]
  | succ t ih =>
    by_cases hx : x = 0
    · simp only [realPrefix, if_pos hx, abs_zero, Nat.cast_add, Nat.cast_one]
      positivity
    by_cases hr : residue x < 1
    · have hi := abs_le.mp (ih (residue x))
      simp only [realPrefix, if_neg hx, if_pos hr]
      rw [abs_le]
      push_cast
      constructor <;> linarith
    · have hi := abs_le.mp (ih (2-residue x))
      simp only [realPrefix, if_neg hx, if_neg hr]
      rw [abs_le]
      push_cast
      constructor <;> linarith

lemma prefix_intervalIntegrable (t : ℕ) (a b : ℝ) :
    IntervalIntegrable (realPrefix t) volume a b := by
  have hc : IntervalIntegrable (fun _ : ℝ => (t : ℝ)) volume a b := intervalIntegrable_const
  apply hc.mono_fun' (prefix_measurable t).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using prefix_abs_le t x)

lemma residue_plus (q : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    residue ((2*((q : ℝ)+1)+y)⁻¹) = y := by
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hf : ⌊(2*((q : ℝ)+1)+y)/2⌋₊ = q+1 := by
    apply (Nat.floor_eq_iff (by linarith [hy.1])).mpr
    constructor <;> push_cast <;> linarith [hy.1,hy.2]
  unfold residue
  rw [inv_inv, hf]
  push_cast
  ring

lemma residue_minus (q : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    residue ((2*((q : ℝ)+1)-y)⁻¹) = 2-y := by
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hf : ⌊(2*((q : ℝ)+1)-y)/2⌋₊ = q := by
    apply (Nat.floor_eq_iff (by linarith [hy.2])).mpr
    constructor <;> push_cast <;> linarith [hy.1,hy.2]
  unfold residue
  rw [inv_inv, hf]
  ring

lemma prefix_plus (t q : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    realPrefix (t+1) ((2*((q : ℝ)+1)+y)⁻¹) = 1-realPrefix t y := by
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hn : (2*((q : ℝ)+1)+y)⁻¹ ≠ 0 := inv_ne_zero (by linarith [hy.1])
  rw [realPrefix, if_neg hn, residue_plus q y hy, if_pos hy.2]

lemma prefix_minus (t q : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    realPrefix (t+1) ((2*((q : ℝ)+1)-y)⁻¹) = 1+realPrefix t y := by
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hn : (2*((q : ℝ)+1)-y)⁻¹ ≠ 0 := inv_ne_zero (by linarith [hy.2])
  rw [realPrefix, if_neg hn, residue_minus q y hy, if_neg (by linarith [hy.2] : ¬2-y<1),
    show 2-(2-y)=y by ring]

lemma residue_nat_ratio (a b : ℕ) (ha : 0 < a) :
    residue ((a : ℝ)/b) = ((b%(2*a) : ℕ) : ℝ)/a := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hf : ⌊((a : ℝ)/b)⁻¹/2⌋₊ = b/(2*a) := by
    rw [inv_div, div_div]
    have he : (a : ℝ)*2 = ((2*a : ℕ) : ℝ) := by push_cast; ring
    rw [he, Nat.floor_div_eq_div]
  have he := Nat.mod_add_div b (2*a)
  have heR : ((b%(2*a) : ℕ) : ℝ) + 2*(a : ℝ)*((b/(2*a) : ℕ) : ℝ) = b := by
    exact_mod_cast he
  unfold residue
  rw [hf, inv_div]
  field_simp [ne_of_gt haR]
  nlinarith

theorem prefix_nat_ratio (t a b : ℕ) (hb : 0 < b) :
    realPrefix t ((a : ℝ)/b) = ((ThetaLongHaul.ecfPrefix t a b : ℤ) : ℝ) := by
  induction t generalizing a b with
  | zero => simp [realPrefix, ThetaLongHaul.ecfPrefix]
  | succ t ih =>
    by_cases ha0 : a = 0
    · subst a
      simp [realPrefix, ThetaLongHaul.ecfPrefix]
    have ha : 0 < a := by omega
    have haR : 0 < (a : ℝ) := by exact_mod_cast ha
    have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
    have hx : (a : ℝ)/b ≠ 0 := ne_of_gt (div_pos haR hbR)
    have hres := residue_nat_ratio a b ha
    have hr : b%(2*a) < 2*a := Nat.mod_lt _ (by omega)
    by_cases hs : b%(2*a) < a
    · have hsR : ((b%(2*a) : ℕ) : ℝ)/a < 1 := (div_lt_one haR).mpr (by exact_mod_cast hs)
      rw [realPrefix, if_neg hx, hres, if_pos hsR, ih _ _ ha,
        ThetaLongHaul.ecfPrefix, if_neg ha0, if_pos hs]
      push_cast
      rfl
    · have hsR : ¬((b%(2*a) : ℕ) : ℝ)/a < 1 := by
        rw [div_lt_one haR]
        exact_mod_cast hs
      have he : 2-((b%(2*a) : ℕ) : ℝ)/a = ((2*a-b%(2*a) : ℕ) : ℝ)/a := by
        rw [Nat.cast_sub hr.le]
        push_cast
        field_simp [ne_of_gt haR]
        <;> ring
      rw [realPrefix, if_neg hx, hres, if_neg hsR, he, ih _ _ ha,
        ThetaLongHaul.ecfPrefix, if_neg ha0, if_neg hs]
      push_cast
      ring

end
end ThetaLongHaul.RealECF


/-! Independently authored fixed-depth continuity, derived in GRID_LIMIT_SKETCH.md.
No external proof or unrefereed theorem is used. -/
namespace ThetaLongHaul.RealECF
noncomputable section
open Filter MeasureTheory Topology

lemma natFloor_continuousAt_irrational {x : ℝ} (hx : Irrational x) :
    ContinuousAt (fun y : ℝ => (⌊y⌋₊ : ℝ)) x := by
  by_cases hz : ⌊x⌋₊=0
  · have hl : x<1 := Nat.floor_eq_zero.mp hz
    apply (continuousAt_const (y := (0 : ℝ))).congr
    filter_upwards [gt_mem_nhds hl] with y hy
    simp only [Nat.floor_eq_zero.mpr hy,Nat.cast_zero]
  · have hf := Nat.floor_eq_iff' hz |>.mp (rfl : ⌊x⌋₊=⌊x⌋₊)
    have hlow : (⌊x⌋₊ : ℝ)<x := lt_of_le_of_ne hf.1 (Ne.symm (hx.ne_nat _))
    apply continuousAt_const.congr
    filter_upwards [Ioo_mem_nhds hlow hf.2] with y hy
    rw [(Nat.floor_eq_iff' hz).mpr ⟨hy.1.le,hy.2⟩]

lemma residue_irrational {x : ℝ} (hx : Irrational x) : Irrational (residue x) := by
  simpa only [residue,Nat.cast_mul,Nat.cast_ofNat] using
    hx.inv.sub_natCast (2*⌊x⁻¹/2⌋₊)

lemma residue_continuousAt_irrational {x : ℝ} (hx : Irrational x) :
    ContinuousAt residue x := by
  have hi : ContinuousAt (fun y : ℝ => y⁻¹) x := continuousAt_inv₀ hx.ne_zero
  have hq : Irrational (x⁻¹/2) := hx.inv.div_natCast (by decide : (2 : ℕ) ≠ 0)
  have hf := (natFloor_continuousAt_irrational hq).comp (f := fun y : ℝ => y⁻¹/2) (hi.div_const 2)
  exact hi.sub (continuousAt_const.mul hf)

lemma prefix_continuousAt_irrational (t : ℕ) {x : ℝ} (hx : Irrational x) :
    ContinuousAt (realPrefix t) x := by
  induction t generalizing x with
  | zero => exact continuousAt_const
  | succ t ih =>
    have hr := residue_continuousAt_irrational hx
    have hri := residue_irrational hx
    have hne : ∀ᶠ y in 𝓝 x, y≠0 := eventually_ne_nhds hx.ne_zero
    by_cases hlt : residue x<1
    · have hc := (continuousAt_const (y := (1 : ℝ))).sub ((ih hri).comp (f := residue) hr)
      apply hc.congr
      filter_upwards [hne,hr.eventually (gt_mem_nhds hlt)] with y hy hres
      simp only [realPrefix,if_neg hy,if_pos hres]
      rfl
    · have hgt : 1<residue x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hri.ne_one)
      have hc := (continuousAt_const (y := (1 : ℝ))).add ((ih (hri.natCast_sub 2)).comp (f := fun y : ℝ => 2-residue y)
        ((continuousAt_const (y := (2 : ℝ))).sub hr))
      apply hc.congr
      filter_upwards [hne,hr.eventually (lt_mem_nhds hgt)] with y hy hres
      simp only [realPrefix,if_neg hy,if_neg (not_lt_of_ge hres.le)]
      rfl


lemma irrational_ae (μ : Measure ℝ) [NullSingletonClass μ] : ∀ᵐ x ∂μ, Irrational x := by
  exact (Set.countable_range (fun q : ℚ => (q : ℝ))).ae_notMem μ

lemma prefix_continuous_ae (t : ℕ) (μ : Measure ℝ) [NullSingletonClass μ] :
    ∀ᵐ x ∂μ, ContinuousAt (realPrefix t) x :=
  (irrational_ae μ).mono fun _ hx => prefix_continuousAt_irrational t hx

def evenGrid (n : ℕ) (x : ℝ) : ℝ := 2*(⌊(x/2)*(n : ℝ)⌋₊ : ℝ)/(n : ℝ)

lemma evenGrid_measurable (n : ℕ) : Measurable (evenGrid n) := by
  unfold evenGrid
  fun_prop

lemma evenGrid_tendsto {x : ℝ} (hx : 0≤x) :
    Tendsto (fun n => evenGrid n x) atTop (𝓝 x) := by
  have ha : 0≤x/2 := by positivity
  have hf := (tendsto_nat_floor_mul_div_atTop (a := x/2) ha).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  convert hf.const_mul 2 using 1
  · funext n
    dsimp [evenGrid]
    ring
  · ring

/-- Fixed fuel only. No effective cutoff, growing-fuel error, or signed-tail
control is asserted by this dominated-convergence theorem. -/
lemma integral_prefix_grid_tendsto (t : ℕ) :
    Tendsto (fun n => ∫ x in (0 : ℝ)..1, realPrefix t (evenGrid n x))
      atTop (𝓝 (∫ x in (0 : ℝ)..1, realPrefix t x)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (t : ℝ))
  · exact Filter.Eventually.of_forall (fun n =>
      ((prefix_measurable t).comp (evenGrid_measurable n)).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun n => Filter.Eventually.of_forall (fun x hx => by
      rw [Real.norm_eq_abs]
      exact prefix_abs_le t (evenGrid n x)))
  · exact intervalIntegrable_const
  · filter_upwards [irrational_ae volume] with x hx hxin
    simp only [Set.uIoc_of_le (by norm_num : (0 : ℝ)≤1)] at hxin
    exact (prefix_continuousAt_irrational t hx).tendsto.comp (evenGrid_tendsto hxin.1.le)


open Finset

def evenCell (n j : ℕ) : ℝ := 2*(j : ℝ)/(n : ℝ)

lemma grid_prefix_intervalIntegrable (t n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => realPrefix t (evenGrid n x)) volume a b := by
  have hc : IntervalIntegrable (fun _ : ℝ => (t : ℝ)) volume a b := intervalIntegrable_const
  apply hc.mono_fun' ((prefix_measurable t).comp (evenGrid_measurable n)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs,Function.comp_apply] using! prefix_abs_le t (evenGrid n x))

lemma evenGrid_cell {n j : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Set.Ioo (evenCell n j) (evenCell n (j+1))) :
    evenGrid n x=evenCell n j := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlo : 2*(j : ℝ) < x*n := (div_lt_iff₀ hnR).mp hx.1
  have hhi : x*n < 2*((j : ℝ)+1) := by
    have h := (lt_div_iff₀ hnR).mp hx.2
    simpa only [Nat.cast_add,Nat.cast_one] using h
  have hxpos : 0 ≤ x := by
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hf : ⌊(x/2)*(n : ℝ)⌋₊=j := by
    apply (Nat.floor_eq_iff (by positivity)).mpr
    constructor <;> nlinarith
  dsimp [evenGrid,evenCell]
  rw [hf]

lemma grid_cell_integral (t n j : ℕ) (hn : 0 < n) :
    (∫ x in evenCell n j..evenCell n (j+1), realPrefix t (evenGrid n x)) =
      (2/(n : ℝ))*realPrefix t (evenCell n j) := by
  have hle : evenCell n j ≤ evenCell n (j+1) := by
    dsimp [evenCell]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    push_cast
    linarith
  calc
    _ = ∫ _ in evenCell n j..evenCell n (j+1), realPrefix t (evenCell n j) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hle
      intro x hx
      dsimp only
      rw [evenGrid_cell hn hx]
    _ = _ := by
      simp only [intervalIntegral.integral_const,smul_eq_mul,evenCell,Nat.cast_add,Nat.cast_one]
      ring

lemma grid_integral_initial (t n m : ℕ) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..evenCell n m, realPrefix t (evenGrid n x)) =
      (2/(n : ℝ))*∑ j ∈ range m, realPrefix t (evenCell n j) := by
  induction m with
  | zero => simp [evenCell]
  | succ m ih =>
    have ha := intervalIntegral.integral_add_adjacent_intervals
      (grid_prefix_intervalIntegrable t n 0 (evenCell n m))
      (grid_prefix_intervalIntegrable t n (evenCell n m) (evenCell n (m+1)))
    rw [←ha,ih,grid_cell_integral t n m hn,sum_range_succ,mul_add]

lemma evenGrid_last_cell {m : ℕ} {x : ℝ}
    (hx : x ∈ Set.Ioo (evenCell (2*m+1) m) 1) :
    evenGrid (2*m+1) x=evenCell (2*m+1) m := by
  have hnR : 0 < ((2*m+1 : ℕ) : ℝ) := by positivity
  have hlo : 2*(m : ℝ) < x*(2*m+1 : ℕ) := (div_lt_iff₀ hnR).mp hx.1
  have hhi : x*(2*m+1 : ℕ) < 2*(m : ℝ)+1 := by
    have h := mul_lt_mul_of_pos_right hx.2 hnR
    push_cast at h
    simpa using h
  have hxpos : 0 ≤ x := by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hf : ⌊(x/2)*((2*m+1 : ℕ) : ℝ)⌋₊=m := by
    apply (Nat.floor_eq_iff (by positivity)).mpr
    constructor <;> nlinarith
  dsimp [evenGrid,evenCell]
  rw [hf]

lemma grid_integral_odd (t m : ℕ) :
    (∫ x in (0 : ℝ)..1, realPrefix t (evenGrid (2*m+1) x)) =
      (2/((2*m+1 : ℕ) : ℝ))*∑ j ∈ range m, realPrefix t (evenCell (2*m+1) j) +
      (1/((2*m+1 : ℕ) : ℝ))*realPrefix t (evenCell (2*m+1) m) := by
  have hle : evenCell (2*m+1) m ≤ 1 := by
    dsimp [evenCell]
    apply (div_le_iff₀ (by positivity : 0 < ((2*m+1 : ℕ) : ℝ))).mpr
    push_cast
    linarith
  have hr : (∫ x in evenCell (2*m+1) m..1, realPrefix t (evenGrid (2*m+1) x)) =
      (1/((2*m+1 : ℕ) : ℝ))*realPrefix t (evenCell (2*m+1) m) := by
    calc
      _ = ∫ _ in evenCell (2*m+1) m..1, realPrefix t (evenCell (2*m+1) m) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hle
        intro x hx
        dsimp only
        rw [evenGrid_last_cell hx]
      _ = _ := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul,evenCell]
        have hn : ((2*m+1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
        push_cast
        ring
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (grid_prefix_intervalIntegrable t (2*m+1) 0 (evenCell (2*m+1) m))
    (grid_prefix_intervalIntegrable t (2*m+1) (evenCell (2*m+1) m) 1)
  rw [←ha,grid_integral_initial t (2*m+1) m (by omega),hr]


lemma sum_even_Ico_reindex (m : ℕ) (f : ℕ → ℝ) (hf : f 0=0) :
    (∑ a ∈ (Ico 1 (2*m+1)).filter Even, f a)=∑ j ∈ range (m+1), f (2*j) := by
  rw [sum_range_eq_add_Ico (fun j => f (2*j)) (by omega : 0 < m+1)]
  simp only [Nat.mul_zero,hf,zero_add]
  apply sum_bij (fun a _ => a/2)
  · intro a ha
    have ham := mem_Ico.mp (mem_filter.mp ha).1
    have hae := Nat.even_iff.mp (mem_filter.mp ha).2
    exact mem_Ico.mpr ⟨by omega,by omega⟩
  · intro a ha b hb hab
    have hae := Nat.even_iff.mp (mem_filter.mp ha).2
    have hbe := Nat.even_iff.mp (mem_filter.mp hb).2
    omega
  · intro j hj
    have hjm := mem_Ico.mp hj
    refine ⟨2*j,mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,
      Nat.even_iff.mpr (by omega)⟩,by omega⟩
  · intro a ha
    have hae := Nat.even_iff.mp (mem_filter.mp ha).2
    congr 1
    omega

lemma grid_prefix_sum (t m : ℕ) :
    (∑ j ∈ range (m+1), realPrefix t (evenCell (2*m+1) j))=
      (depthPrefixSum t (2*m+1) : ℝ) := by
  have hzero : ((ecfPrefix t 0 (2*m+1) : ℤ) : ℝ)=0 := by
    cases t <;> simp [ThetaLongHaul.ecfPrefix]
  unfold depthPrefixSum
  rw [Int.cast_sum,sum_even_Ico_reindex m _ hzero]
  apply sum_congr rfl
  intro j hj
  have h := prefix_nat_ratio t (2*j) (2*m+1) (by omega)
  convert h using 1
  dsimp [evenCell]
  push_cast
  ring

/-- Exact endpoint correction for odd denominators; no primality needed. -/
lemma grid_integral_eq_discrete (t m : ℕ) :
    (∫ x in (0 : ℝ)..1, realPrefix t (evenGrid (2*m+1) x)) =
      (2/((2*m+1 : ℕ) : ℝ))*(depthPrefixSum t (2*m+1) : ℝ)-
      (1/((2*m+1 : ℕ) : ℝ))*realPrefix t (evenCell (2*m+1) m) := by
  have hg := grid_integral_odd t m
  have hs := grid_prefix_sum t m
  rw [sum_range_succ] at hs
  rw [hg]
  rw [←hs]
  ring

lemma prefix_zero_real (t : ℕ) : realPrefix t 0=0 := by
  cases t <;> simp [realPrefix]

lemma grid_discrete_error_bound (t m : ℕ) :
    |(depthPrefixSum t (2*m+1) : ℝ)/((2*m+1 : ℕ) : ℝ)-
      (1/2)*(∫ x in (0 : ℝ)..1, realPrefix t (evenGrid (2*m+1) x))| ≤
      (t : ℝ)/(2*((2*m+1 : ℕ) : ℝ)) := by
  rw [grid_integral_eq_discrete]
  have hn : 0 < ((2*m+1 : ℕ) : ℝ) := by positivity
  have he : (depthPrefixSum t (2*m+1) : ℝ)/((2*m+1 : ℕ) : ℝ)-
      (1/2)*((2/((2*m+1 : ℕ) : ℝ))*(depthPrefixSum t (2*m+1) : ℝ)-
      (1/((2*m+1 : ℕ) : ℝ))*realPrefix t (evenCell (2*m+1) m)) =
      realPrefix t (evenCell (2*m+1) m)/(2*((2*m+1 : ℕ) : ℝ)) := by ring
  rw [he,abs_div,abs_of_pos (by positivity : (0 : ℝ) < 2*((2*m+1 : ℕ) : ℝ))]
  exact div_le_div_of_nonneg_right (prefix_abs_le t _) (by positivity)


/-- A genuine fixed-depth discrete mean limit, for all odd denominators. No
uniformity in fuel or bound on the final signed tail is claimed. -/
theorem depthPrefixSum_normalized_tendsto (t : ℕ) :
    Tendsto (fun m : ℕ => (depthPrefixSum t (2*m+1) : ℝ)/((2*m+1 : ℕ) : ℝ))
      atTop (𝓝 ((1/2)*(∫ x in (0 : ℝ)..1, realPrefix t x))) := by
  have hodds : Tendsto (fun m : ℕ => 2*m+1) atTop atTop :=
    tendsto_atTop_mono (fun m => by change m ≤ 2*m+1; omega) tendsto_id
  have hreal : Tendsto (fun m : ℕ => 2*((2*m+1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hodds).const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hzero : Tendsto (fun m : ℕ => (t : ℝ)/(2*((2*m+1 : ℕ) : ℝ)))
      atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds.div_atTop hreal
  have hdiff0 := squeeze_zero (fun m => abs_nonneg _) (grid_discrete_error_bound t) hzero
  have hdiff : Tendsto (fun m : ℕ =>
      (depthPrefixSum t (2*m+1) : ℝ)/((2*m+1 : ℕ) : ℝ)-
      (1/2)*(∫ x in (0 : ℝ)..1, realPrefix t (evenGrid (2*m+1) x)))
      atTop (𝓝 (0 : ℝ)) := (tendsto_zero_iff_abs_tendsto_zero _).mpr hdiff0
  have hmain := ((integral_prefix_grid_tendsto t).comp hodds).const_mul (1/2 : ℝ)
  have hfin := hdiff.add hmain
  simpa only [Function.comp_apply,sub_add_cancel,zero_add] using hfin

end
end ThetaLongHaul.RealECF


namespace ThetaLongHaul.RealECF
lemma realPrefix_eq_explicit_rec (t : ℕ) (x : ℝ) : realPrefix t x =
    (Nat.rec (fun _ : ℝ => (0 : ℝ)) (fun _ f x =>
      let r := x⁻¹-2*(⌊x⁻¹/2⌋₊ : ℕ)
      if x=0 then 0 else if r<1 then 1-f r else 1+f (2-r)) t x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih => simp only [realPrefix,residue,ih]
lemma ecfPrefix_eq_explicit_rec (t a b : ℕ) : ecfPrefix t a b =
    (Nat.rec (fun _ _ : ℕ => (0 : ℤ)) (fun _ f a b =>
      if a=0 then 0 else 1-if b%(2*a)<a then f (b%(2*a)) a else -f (2*a-b%(2*a)) a) t a b) := by
  induction t generalizing a b with
  | zero => rfl
  | succ t ih => simp only [ecfPrefix,ih]
end ThetaLongHaul.RealECF

theorem OMA.solution : OMA.R_Arxiv_2501_03234_conjecture_4_4_R1.H2 := by
  dsimp only [OMA.R_Arxiv_2501_03234_conjecture_4_4_R1.H2]
  intro t
  simpa only [ThetaLongHaul.depthPrefixSum,ThetaLongHaul.RealECF.realPrefix_eq_explicit_rec,
    ThetaLongHaul.RealECF.ecfPrefix_eq_explicit_rec] using
    ThetaLongHaul.RealECF.depthPrefixSum_normalized_tendsto t
