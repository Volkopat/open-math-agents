import OMAStatements.S_mo_130917
import Mathlib

-- Retains @Genbox’s real-power estimate from PR #27229.
-- The endpoint absolute-value bound follows @etaubman’s earlier companion (#21152).

open Set

private noncomputable def nearbyConstant (q : ℝ) : ℝ :=
  q*((1/2:ℝ)^(q-1)+(3/2:ℝ)^(q-1))

private theorem nearby_nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ nearbyConstant q := by
  unfold nearbyConstant
  positivity

private theorem nearby_power {q t : ℝ} (hq : 0 < q) (ht : |t| ≤ 1/2) :
    |(t+1)^q-1| ≤ nearbyConstant q*|t| := by
  have hpos (u : ℝ) (hu : u ∈ Icc (1/2:ℝ) (3/2)) : 0 < u := by
    linarith [hu.1]
  have hd (u : ℝ) (hu : u ∈ Icc (1/2:ℝ) (3/2)) :
      HasDerivAt (fun x : ℝ => x^q) (q*u^(q-1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl (hpos u hu).ne')
  have hbound (u : ℝ) (hu : u ∈ Icc (1/2:ℝ) (3/2)) :
      ‖deriv (fun x : ℝ => x^q) u‖ ≤ nearbyConstant q := by
    rw [(hd u hu).deriv,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hq.le (Real.rpow_nonneg (hpos u hu).le _))]
    unfold nearbyConstant
    apply mul_le_mul_of_nonneg_left _ hq.le
    by_cases he : 0 ≤ q-1
    · have hle := Real.rpow_le_rpow (hpos u hu).le hu.2 he
      have hp : 0 ≤ (1/2:ℝ)^(q-1) := by positivity
      linarith
    · have hle := Real.rpow_le_rpow_of_nonpos (z:=q-1) (by norm_num : 0 < (1/2:ℝ)) hu.1 (by linarith)
      have hp : 0 ≤ (3/2:ℝ)^(q-1) := by positivity
      linarith
  have h1 : (1:ℝ) ∈ Icc (1/2:ℝ) (3/2) := by norm_num
  have hu : t+1 ∈ Icc (1/2:ℝ) (3/2) := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp ht
    exact ⟨by linarith,by linarith⟩
  have hm := (convex_Icc (1/2:ℝ) (3/2)).norm_image_sub_le_of_norm_deriv_le
    (fun u hu => (hd u hu).differentiableAt) hbound h1 hu
  simpa [Real.norm_eq_abs,Real.one_rpow] using hm

private noncomputable def scale (p : ℝ) : ℝ :=
  p*(nearbyConstant (p-1)+3^(p-1)+2)

private noncomputable def slopeTerm (p t : ℝ) : ℝ :=
  p*(|t+1|^(p-2)*(t+1))-p

private theorem scale_nonneg {p : ℝ} (hp : 1 < p) : 0 ≤ scale p := by
  unfold scale
  have h := nearby_nonneg (q:=p-1) (by linarith)
  have hp0 : 0 ≤ p := by linarith
  positivity

private theorem slope_bound {p : ℝ} (hp : 1 < p) (t : ℝ) :
    |slopeTerm p t| ≤ scale p*(|t|+|t|^(p-1)) := by
  have hp0 : 0 < p := by linarith
  have hq : 0 < p-1 := by linarith
  have hK := nearby_nonneg hq.le
  have h3 : 0 ≤ (3:ℝ)^(p-1) := by positivity
  have hT : 0 ≤ |t|^(p-1) := by positivity
  by_cases ht : |t| ≤ 1/2
  · have hz : 0 < t+1 := by linarith [(abs_le.mp ht).1]
    have he : |t+1|^(p-2)*(t+1) = (t+1)^(p-1) := by
      rw [abs_of_pos hz,← Real.rpow_add_one hz.ne']
      congr 1
      ring
    have hb := nearby_power hq ht
    unfold slopeTerm scale
    rw [he,← mul_sub_one,abs_mul,abs_of_pos hp0,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hp0.le
    calc
      _ ≤ nearbyConstant (p-1)*|t| := hb
      _ ≤ (nearbyConstant (p-1)+3^(p-1)+2)*(|t|+|t|^(p-1)) := by
        apply mul_le_mul <;> linarith [abs_nonneg t]
  · have hz : |t+1| ≤ 3*|t| := by
      calc
        |t+1| ≤ |t|+|(1:ℝ)| := abs_add_le _ _
        _ ≤ 3*|t| := by norm_num; linarith
    have hpow : |t+1|^(p-1) ≤ (3:ℝ)^(p-1)*|t|^(p-1) := by
      rw [← Real.mul_rpow (by norm_num) (abs_nonneg t)]
      exact Real.rpow_le_rpow (abs_nonneg _) hz hq.le
    have habs : abs (|t+1|^(p-2)*(t+1)) = |t+1|^(p-1) := by
      rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
        ← Real.rpow_add_one' (y:=p-2) (abs_nonneg _) (by linarith)]
      congr 1
      ring
    have hrough : |slopeTerm p t| ≤ p*(|t+1|^(p-1)+1) := by
      unfold slopeTerm
      calc
        _ ≤ |p*(|t+1|^(p-2)*(t+1))| + |p| := by
          simpa using abs_sub_le (p*(|t+1|^(p-2)*(t+1))) 0 p
        _ = _ := by rw [abs_mul,abs_of_pos hp0,habs]; ring
    refine hrough.trans ?_
    unfold scale
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hp0.le
    have hX : 0 ≤ |t| := abs_nonneg _
    nlinarith only [hpow,lt_of_not_ge ht,mul_nonneg hK hX,mul_nonneg hK hT,
      mul_nonneg h3 hX,hT]

theorem OMA.solution : type_of% @OMA.S_mo_130917.main := by
  intro p hp
  refine ⟨scale p, ?_⟩
  intro x y
  let F : ℝ → ℝ := fun t => |t+1|^p-p*t
  let C : ℝ := scale p*(|x|+|y|+|x|^(p-1)+|y|^(p-1))
  have hF (t : ℝ) : HasDerivAt F (slopeTerm p t) t := by
    have h := ((hasDerivAt_abs_rpow (t+1) hp).comp t ((hasDerivAt_id t).add_const 1)).sub
      ((hasDerivAt_id t).const_mul p)
    simpa [F,slopeTerm,mul_assoc,Function.comp_def,Pi.sub_def] using h
  have hf (t : ℝ) (ht : t ∈ uIcc y x) : ‖deriv F t‖ ≤ C := by
    rw [(hF t).deriv,Real.norm_eq_abs]
    refine (slope_bound hp t).trans ?_
    have htmax : |t| ≤ max |x| |y| := by
      rcases Set.mem_uIcc.mp ht with h | h
      · simpa [max_comm] using abs_le_max_abs_abs h.1 h.2
      · exact abs_le_max_abs_abs h.1 h.2
    have hpow := Real.rpow_le_rpow (abs_nonneg t) htmax (by linarith : 0 ≤ p-1)
    apply mul_le_mul_of_nonneg_left _ (scale_nonneg hp)
    rcases le_total |x| |y| with hxy | hyx
    · rw [max_eq_right hxy] at htmax hpow
      linarith [abs_nonneg x, Real.rpow_nonneg (abs_nonneg x) (p-1)]
    · rw [max_eq_left hyx] at htmax hpow
      linarith [abs_nonneg y, Real.rpow_nonneg (abs_nonneg y) (p-1)]

  have h := (convex_Icc (min y x) (max y x)).norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (hF t).differentiableAt) hf (left_mem_uIcc : y ∈ uIcc y x) (right_mem_uIcc : x ∈ uIcc y x)
  have he : F x-F y = (|x+1|^p-|y+1|^p)-p*(x-y) := by dsimp [F]; ring
  simpa [C,Real.norm_eq_abs,he] using h