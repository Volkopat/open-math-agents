import OMAStatements.S_mo_104197
import Mathlib

open OMA.S_mo_104197

private theorem powerTangent {x y α : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hα : 0 ≤ α) :
    x^(1+α) + (1+α)*x^α*(y-x) ≤ y^(1+α) := by
  have hd : -1 ≤ (y-x)/x := (le_div_iff₀ hx).2 (by linarith)
  have hp : 1 ≤ 1+α := by linarith
  have hb := one_add_mul_self_le_rpow_one_add hd hp
  rw [show 1+(y-x)/x = y/x by field_simp [hx.ne'] <;> ring, Real.div_rpow hy hx.le] at hb
  have hs := (le_div_iff₀ (Real.rpow_pos_of_pos hx (1+α))).1 hb
  calc
    _ = (1+(1+α)*((y-x)/x))*x^(1+α) := by
      rw [Real.rpow_one_add' hx.le (by positivity : 1+α ≠ 0)]
      field_simp [hx.ne'] <;> ring
    _ ≤ _ := hs

private theorem powerDifference {y α : ℝ} (hy : 1 ≤ y) (hα : 0 ≤ α) :
    y^α - 1 ≤ 2*α*Real.sqrt y*y^α := by
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hlog : Real.log y ≤ 2*Real.sqrt y := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hy0)
    rw [Real.log_sqrt hy0.le] at h
    linarith
  let t := Real.log y * α
  have ht : (1-t)*Real.exp t ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-t)) (Real.exp_pos t).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
    simpa only [sub_eq_add_neg, add_comm (1 : ℝ)] using h
  rw [Real.rpow_def_of_pos hy0]
  calc
    Real.exp t - 1 ≤ t*Real.exp t := by nlinarith only [ht]
    _ ≤ 2*α*Real.sqrt y*Real.exp t := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      have h := mul_le_mul_of_nonneg_right hlog hα
      dsimp [t]
      nlinarith only [h]

private theorem ratioBound {α a b δ : ℝ}
    (hα : 0 < α) (hα₁ : α ≤ 1/4) (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ) :
    ((1+a)^(1+α)+(1+b)^(1+α)) /
      ((1+δ^2+2*δ+a)^(1+α)+(1+δ^2-2*δ+b)^(1+α)) ≤ 1+16*α^2 := by
  let x := 1+a
  let y := 1+b
  let s := 1+α
  let N := x^s+y^s
  let D := (x+δ^2+2*δ)^s+(y+δ^2-2*δ)^s
  have hx : 0 < x := by dsimp [x]; linarith
  have hy : 0 < y := by dsimp [y]; linarith
  have hf : 0 < x+δ^2+2*δ := by positivity
  have hg : 0 < y+δ^2-2*δ := by dsimp [y]; nlinarith [sq_nonneg (δ-1)]
  have hD : 0 < D := by
    exact add_pos (Real.rpow_pos_of_pos hf _) (Real.rpow_pos_of_pos hg _)
  have hxA : 1 ≤ x^α := Real.one_le_rpow (by dsimp [x]; linarith) hα.le
  have hyA : 0 ≤ y^α := Real.rpow_nonneg hy.le _
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hs2 : s ≤ 2 := by dsimp [s]; linarith
  have hsq : α^2 ≤ 1/16 := by nlinarith [mul_nonneg hα.le (sub_nonneg.2 hα₁)]
  have htang : N+s*x^α*(δ^2+2*δ)+s*y^α*(δ^2-2*δ) ≤ D := by
    have h₁ := powerTangent hx hf.le hα.le
    have h₂ := powerTangent hy hg.le hα.le
    dsimp only [N, D, s]
    nlinarith only [h₁,h₂]
  have hdiff : y^α-x^α ≤ 2*α*Real.sqrt y*y^α := by
    have h := powerDifference (by dsimp [y]; linarith : 1 ≤ y) hα.le
    linarith
  have hdiff' := mul_le_mul_of_nonneg_left hdiff (show 0 ≤ 2*s*δ by positivity)
  have hxterm : 0 ≤ s*x^α*δ^2 := by positivity
  have hlinear : N+s*y^α*(δ^2-4*α*Real.sqrt y*δ) ≤ D := by
    nlinarith only [htang, hdiff', hxterm]
  have hcomplete := mul_nonneg (mul_nonneg hs hyA) (sq_nonneg (δ-2*α*Real.sqrt y))
  have hdifference : s*y^α*(δ-2*α*Real.sqrt y)^2 =
      s*y^α*(δ^2-4*α*Real.sqrt y*δ)+4*s*α^2*y^α*y := by
    calc
      _ = s*y^α*(δ^2-4*α*Real.sqrt y*δ)+4*s*α^2*y^α*(Real.sqrt y)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hy.le]
  rw [hdifference] at hcomplete
  have hp : y^s = y*y^α := Real.rpow_one_add' hy.le (by dsimp [s]; positivity)
  have hNy : y^α*y ≤ N := by
    rw [mul_comm, ← hp]
    have hnonneg : 0 ≤ x^s := Real.rpow_nonneg hx.le _
    dsimp only [N]
    linarith
  have hprod : 4*s*α^2*y^α*y ≤ 8*α^2*N := by
    calc
      _ = s*(4*α^2*(y^α*y)) := by ring
      _ ≤ 2*(4*α^2*(y^α*y)) := mul_le_mul_of_nonneg_right hs2 (by positivity)
      _ = (8*α^2)*(y^α*y) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hNy (by positivity)
  have hlower : (1-8*α^2)*N ≤ D := by nlinarith only [hlinear,hcomplete,hprod]
  have hpos : 0 < 1-8*α^2 := by linarith
  have hratio : N/D ≤ 1/(1-8*α^2) :=
    (div_le_div_iff₀ hD hpos).2 (by simpa [mul_comm] using hlower)
  have hlast : 1/(1-8*α^2) ≤ 1+16*α^2 := by
    apply (div_le_iff₀ hpos).2
    nlinarith only [mul_nonneg (show 0 ≤ 8*α^2 by positivity)
      (show 0 ≤ 1-16*α^2 by linarith)]
  rw [show 1+δ^2+2*δ+a = x+δ^2+2*δ by dsimp [x]; ring,
    show 1+δ^2-2*δ+b = y+δ^2-2*δ by dsimp [y]; ring]
  exact hratio.trans hlast

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_104197.main) := by
  rintro ⟨M, ε, hM, hε, h⟩
  let α := min (ε/2) (min (1/8) (M/32))
  have hα : 0 < α := by dsimp [α]; positivity
  have hαε : α < ε := (min_le_left _ _).trans_lt (by linarith)
  have hα₁ : α ≤ 1/4 := (min_le_right _ _).trans ((min_le_left _ _).trans (by norm_num))
  have hαM : α ≤ M/32 := (min_le_right _ _).trans (min_le_right _ _)
  have upper : QiuRatioSup α ≤ 1+16*α^2 := by
    unfold QiuRatioSup
    apply csSup_le
    · exact ⟨_, 1, 1, 1/2, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩
    · rintro _ ⟨a, b, δ, ha, hb, hδ, _, rfl⟩
      exact ratioBound hα hα₁ ha hb hδ
  have lower := h α hα hαε
  have strict : 16*α^2 < M*α := by
    have e := mul_lt_mul_of_pos_right (show 16*α < M by linarith) hα
    nlinarith only [e]
  linarith