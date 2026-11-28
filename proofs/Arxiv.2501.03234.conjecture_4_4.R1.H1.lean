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

namespace ThetaLongHaul.TransferCone
noncomputable section

def Cone (w : ℝ → ℝ) : Prop :=
  (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ w x) ∧ MonotoneOn w (Set.Icc 0 1)

lemma Cone.const {c : ℝ} (hc : 0 ≤ c) : Cone (fun _ => c) := by
  exact ⟨fun _ _ => hc, fun _ _ _ _ _ => le_rfl⟩

lemma Cone.id : Cone (fun x : ℝ => x) :=
  ⟨fun _ hx => hx.1, fun _ _ _ _ hxy => hxy⟩

lemma Cone.add {f g : ℝ → ℝ} (hf : Cone f) (hg : Cone g) : Cone (fun x => f x + g x) := by
  exact ⟨fun x hx => add_nonneg (hf.1 x hx) (hg.1 x hx),
    fun _ hx _ hy hxy => add_le_add (hf.2 hx hy hxy) (hg.2 hx hy hxy)⟩

lemma Cone.mul {f g : ℝ → ℝ} (hf : Cone f) (hg : Cone g) : Cone (fun x => f x * g x) := by
  refine ⟨fun x hx => mul_nonneg (hf.1 x hx) (hg.1 x hx), ?_⟩
  intro x hx y hy hxy
  exact mul_le_mul (hf.2 hx hy hxy) (hg.2 hx hy hxy) (hg.1 x hx) (hf.1 y hy)

lemma Cone.scale {f : ℝ → ℝ} (hf : Cone f) {c : ℝ} (hc : 0 ≤ c) :
    Cone (fun x => c * f x) := (Cone.const hc).mul hf

lemma Cone.pow {f : ℝ → ℝ} (hf : Cone f) (n : ℕ) : Cone (fun x => (f x) ^ n) := by
  refine ⟨fun x hx => pow_nonneg (hf.1 x hx) n, ?_⟩
  intro x hx y hy hxy
  exact pow_le_pow_left₀ (hf.1 x hx) (hf.2 hx hy hxy) n

lemma unit_sq_le {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : x ^ 2 ≤ 1 := by
  nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]

def gap (α x : ℝ) : ℝ := (α - x ^ 2)⁻¹

lemma gap_cone {α : ℝ} (ha : 1 < α) : Cone (gap α) := by
  have hpos (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 < α - x ^ 2 := by
    have h := unit_sq_le hx
    linarith
  refine ⟨fun x hx => inv_nonneg.mpr (hpos x hx).le, ?_⟩
  intro x hx y hy hxy
  unfold gap
  apply (inv_le_inv₀ (hpos x hx) (hpos y hy)).mpr
  have hs : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx.1 hxy 2
  linarith

def branch (c : ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  w ((c - x)⁻¹) * ((c - x)⁻¹) ^ 2 - w ((c + x)⁻¹) * ((c + x)⁻¹) ^ 2

lemma reciprocal_branch_mem {c x : ℝ} (hc : 2 ≤ c) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (c - x)⁻¹ ∈ Set.Icc (0 : ℝ) 1 ∧ (c + x)⁻¹ ∈ Set.Icc (0 : ℝ) 1 := by
  have hm : 0 < c - x := by linarith [hx.2]
  have hp : 0 < c + x := by linarith [hx.1]
  constructor
  · exact ⟨inv_nonneg.mpr hm.le, (inv_le_one₀ hm).mpr (by linarith [hx.2])⟩
  · exact ⟨inv_nonneg.mpr hp.le, (inv_le_one₀ hp).mpr (by linarith [hx.1])⟩

/-- A signed branch pair preserves nonnegative increasing functions. -/
lemma branch_cone {c : ℝ} (hc : 2 ≤ c) {w : ℝ → ℝ} (hw : Cone w) : Cone (branch c w) := by
  have hf := hw.mul (Cone.id.pow 2)
  refine ⟨?_, ?_⟩
  · intro x hx
    have hd := reciprocal_branch_mem hc hx
    have horder : (c + x)⁻¹ ≤ (c - x)⁻¹ := by
      apply (inv_le_inv₀ (by linarith [hx.1]) (by linarith [hx.2])).mpr
      linarith [hx.1]
    exact sub_nonneg.mpr (hf.2 hd.2 hd.1 horder)
  · intro x hx y hy hxy
    have hdx := reciprocal_branch_mem hc hx
    have hdy := reciprocal_branch_mem hc hy
    have hm : (c - x)⁻¹ ≤ (c - y)⁻¹ := by
      apply (inv_le_inv₀ (by linarith [hx.2]) (by linarith [hy.2])).mpr
      linarith
    have hp : (c + y)⁻¹ ≤ (c + x)⁻¹ := by
      apply (inv_le_inv₀ (by linarith [hy.1]) (by linarith [hx.1])).mpr
      linarith
    have h1 := hf.2 hdx.1 hdy.1 hm
    have h2 := hf.2 hdy.2 hdx.2 hp
    change w ((c-x)⁻¹)*((c-x)⁻¹)^2 - w ((c+x)⁻¹)*((c+x)⁻¹)^2 ≤
      w ((c-y)⁻¹)*((c-y)⁻¹)^2 - w ((c+y)⁻¹)*((c+y)⁻¹)^2
    change w ((c-x)⁻¹)*((c-x)⁻¹)^2 ≤ w ((c-y)⁻¹)*((c-y)⁻¹)^2 at h1
    change w ((c+y)⁻¹)*((c+y)⁻¹)^2 ≤ w ((c+x)⁻¹)*((c+x)⁻¹)^2 at h2
    linarith

def transfer (w : ℝ → ℝ) : ℝ → ℝ := fun x => branch 2 w x + branch 4 w x

lemma transfer_cone {w : ℝ → ℝ} (hw : Cone w) : Cone (transfer w) :=
  (branch_cone (by norm_num : (2 : ℝ) ≤ 2) hw).add
    (branch_cone (by norm_num : (2 : ℝ) ≤ 4) hw)

lemma transfer_sub (f g : ℝ → ℝ) :
    transfer (fun x => f x - g x) = fun x => transfer f x - transfer g x := by
  funext x
  unfold transfer branch
  ring

def residualD (y : ℝ) : ℝ :=
  (11 / 600) * y +
  y ^ 3 * ((1 / 16) * gap 16 y + (gap 16 y) ^ 2) +
  3 * (y ^ 3 * ((7 / 144) * gap 16 y + ((7 / 9) * gap 9 y) * gap 16 y)) +
  (3 / 50) * (y ^ 3 * gap 25 y) +
  (y ^ 3 * (1 + (1 / 4) * y ^ 2)) * (gap 4 y) ^ 2

lemma residualD_cone : Cone residualD := by
  have h4 := gap_cone (by norm_num : (1 : ℝ) < 4)
  have h9 := gap_cone (by norm_num : (1 : ℝ) < 9)
  have h16 := gap_cone (by norm_num : (1 : ℝ) < 16)
  have h25 := gap_cone (by norm_num : (1 : ℝ) < 25)
  have h3 := Cone.id.pow 3
  have hA := Cone.id.scale (by norm_num : (0 : ℝ) ≤ 11 / 600)
  have hB := h3.mul ((h16.scale (by norm_num : (0 : ℝ) ≤ 1 / 16)).add (h16.pow 2))
  have hC := (h3.mul ((h16.scale (by norm_num : (0 : ℝ) ≤ 7 / 144)).add
    ((h9.scale (by norm_num : (0 : ℝ) ≤ 7 / 9)).mul h16))).scale (by norm_num : (0 : ℝ) ≤ 3)
  have hD := (h3.mul h25).scale (by norm_num : (0 : ℝ) ≤ 3 / 50)
  have hE := (h3.mul ((Cone.const (by norm_num : (0 : ℝ) ≤ 1)).add
    ((Cone.id.pow 2).scale (by norm_num : (0 : ℝ) ≤ 1 / 4)))).mul (h4.pow 2)
  exact (((hA.add hB).add hC).add hD).add hE

def residualR (h y : ℝ) : ℝ :=
  ((2 * h ^ 2) * (y * (27 - h ^ 2 + y ^ 2))) *
    gap ((3 - h) ^ 2) y * gap ((3 + h) ^ 2) y * gap 9 y +
  (25 - (5 - h) ^ 2) * (y * gap ((5 - h) ^ 2) y * gap 25 y)

lemma residualR_cone {h : ℝ} (hh : h ∈ Set.Icc (0 : ℝ) 1) : Cone (residualR h) := by
  have ha := gap_cone (show (1 : ℝ) < (3 - h) ^ 2 by nlinarith [hh.1, hh.2])
  have hb := gap_cone (show (1 : ℝ) < (3 + h) ^ 2 by nlinarith [hh.1, hh.2])
  have hc := gap_cone (show (1 : ℝ) < (5 - h) ^ 2 by nlinarith [hh.1, hh.2])
  have h9 := gap_cone (by norm_num : (1 : ℝ) < 9)
  have h25 := gap_cone (by norm_num : (1 : ℝ) < 25)
  have hs := unit_sq_le hh
  have hp : Cone (fun y : ℝ => 27 - h ^ 2 + y ^ 2) :=
    (Cone.const (by linarith : 0 ≤ 27 - h ^ 2)).add (Cone.id.pow 2)
  have hfirst := (((((Cone.id.mul hp).scale (by positivity : 0 ≤ 2 * h ^ 2)).mul ha).mul hb).mul h9)
  have hsecond := ((Cone.id.mul hc).mul h25).scale
    (show 0 ≤ 25 - (5 - h) ^ 2 by nlinarith [hh.1, hh.2])
  exact hfirst.add hsecond


lemma Cone.congr_on {f g : ℝ → ℝ} (hf : Cone f)
    (he : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = g x) : Cone g := by
  constructor
  · intro x hx
    rw [← he x hx]
    exact hf.1 x hx
  · intro x hx y hy hxy
    rw [← he x hx, ← he y hy]
    exact hf.2 hx hy hxy

def kernelK (c y : ℝ) : ℝ := y * gap (c ^ 2) y

def W (z y : ℝ) : ℝ := z ^ 2 * y / (1 - z ^ 2 * y ^ 2)

lemma kernelK_diff (c d y : ℝ) (hc : c ^ 2 - y ^ 2 ≠ 0) (hd : d ^ 2 - y ^ 2 ≠ 0) :
    kernelK c y - kernelK d y = (d ^ 2 - c ^ 2) * (y * gap (c ^ 2) y * gap (d ^ 2) y) := by
  unfold kernelK gap
  field_simp
  <;> ring

lemma kernelK_symmetric (c h y : ℝ) (ha : (c - h) ^ 2 - y ^ 2 ≠ 0)
    (hb : (c + h) ^ 2 - y ^ 2 ≠ 0) (hc : c ^ 2 - y ^ 2 ≠ 0) :
    kernelK (c - h) y + kernelK (c + h) y - 2 * kernelK c y =
      ((2 * h ^ 2) * (y * (3 * c ^ 2 - h ^ 2 + y ^ 2))) *
        gap ((c - h) ^ 2) y * gap ((c + h) ^ 2) y * gap (c ^ 2) y := by
  unfold kernelK gap
  field_simp
  <;> ring

lemma residualR_identity (h y : ℝ) (hh : h ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    kernelK (3 - h) y + kernelK (3 + h) y - 2 * kernelK 3 y +
      (kernelK (5 - h) y - kernelK 5 y) = residualR h y := by
  have hs := unit_sq_le hy
  have ha : (3 - h) ^ 2 - y ^ 2 ≠ 0 := by nlinarith [hh.1, hh.2]
  have hb : (3 + h) ^ 2 - y ^ 2 ≠ 0 := by nlinarith [hh.1, hh.2]
  have hc : (3 : ℝ) ^ 2 - y ^ 2 ≠ 0 := by nlinarith
  have hd : (5 - h) ^ 2 - y ^ 2 ≠ 0 := by nlinarith [hh.1, hh.2]
  have he : (5 : ℝ) ^ 2 - y ^ 2 ≠ 0 := by nlinarith
  rw [kernelK_symmetric 3 h y ha hb hc, kernelK_diff (5-h) 5 y hd he]
  norm_num only [show (3 : ℝ) ^ 2 = 9 by norm_num, show (5 : ℝ) ^ 2 = 25 by norm_num]
  unfold residualR
  ring

lemma transfer_one (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    transfer (fun _ => 1) y = 8 * y * (gap 4 y) ^ 2 + 16 * y * (gap 16 y) ^ 2 := by
  have hs := unit_sq_le hy
  have hm2 : (2 : ℝ) - y ≠ 0 := by linarith [hy.2]
  have hp2 : (2 : ℝ) + y ≠ 0 := by linarith [hy.1]
  have hm4 : (4 : ℝ) - y ≠ 0 := by linarith [hy.2]
  have hp4 : (4 : ℝ) + y ≠ 0 := by linarith [hy.1]
  have h4 : (4 : ℝ) - y ^ 2 ≠ 0 := by linarith
  have h16 : (16 : ℝ) - y ^ 2 ≠ 0 := by linarith
  unfold transfer branch gap
  field_simp
  <;> ring

lemma residualD_identity (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (8 * y * (gap 4 y) ^ 2 + 16 * y * (gap 16 y) ^ 2) -
      (3 / 2) * (2 * kernelK 2 y + 2 * kernelK 4 y - 2 * kernelK 3 y - kernelK 5 y) =
      residualD y := by
  have hs := unit_sq_le hy
  have h4 : (4 : ℝ) - y ^ 2 ≠ 0 := by linarith
  have h9 : (9 : ℝ) - y ^ 2 ≠ 0 := by linarith
  have h16 : (16 : ℝ) - y ^ 2 ≠ 0 := by linarith
  have h25 : (25 : ℝ) - y ^ 2 ≠ 0 := by linarith
  unfold residualD kernelK gap
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num, show (3 : ℝ) ^ 2 = 9 by norm_num,
    show (4 : ℝ) ^ 2 = 16 by norm_num, show (5 : ℝ) ^ 2 = 25 by norm_num]
  field_simp
  <;> ring

lemma branch_W (c z y : ℝ) (hc : 2 ≤ c) (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    branch c (W z) y = kernelK (c - z) y + kernelK (c + z) y - 2 * kernelK c y := by
  have hs := unit_sq_le hy
  have hz2 : z ^ 2 < 1 := by nlinarith [hz.1, hz.2]
  have hm : 0 < c - y := by linarith [hy.2]
  have hp : 0 < c + y := by linarith [hy.1]
  have hcm : 1 < c - z := by linarith [hz.2]
  have hcp : 1 < c + z := by linarith [hz.1]
  have hkm : 0 < (c - z) ^ 2 - y ^ 2 := by nlinarith
  have hkp : 0 < (c + z) ^ 2 - y ^ 2 := by nlinarith
  have hkc : 0 < c ^ 2 - y ^ 2 := by nlinarith
  have hrec := reciprocal_branch_mem hc hy
  have hwm : 0 < 1 - z ^ 2 * ((c-y)⁻¹) ^ 2 := by
    have hi := unit_sq_le hrec.1
    have hmul := mul_le_mul_of_nonneg_left hi (sq_nonneg z)
    nlinarith
  have hwp : 0 < 1 - z ^ 2 * ((c+y)⁻¹) ^ 2 := by
    have hi := unit_sq_le hrec.2
    have hmul := mul_le_mul_of_nonneg_left hi (sq_nonneg z)
    nlinarith
  have hm1 : 1 ≤ c - y := by linarith [hy.2]
  have hp1 : 1 ≤ c + y := by linarith [hy.1]
  have hpm : (c-y) ^ 2 - z ^ 2 ≠ 0 := by nlinarith [sq_nonneg (c-y-1)]
  have hpp : (c+y) ^ 2 - z ^ 2 ≠ 0 := by nlinarith [sq_nonneg (c+y-1)]
  ring_nf at hpm hpp
  have hnm : 0 < -z ^ 2 - c*y*2 + c ^ 2 + y ^ 2 := by nlinarith [sq_nonneg (c-y-1)]
  have hnp : 0 < -z ^ 2 + c*y*2 + c ^ 2 + y ^ 2 := by nlinarith [sq_nonneg (c+y-1)]
  unfold branch W kernelK gap
  field_simp [ne_of_gt hm, ne_of_gt hp, ne_of_gt hkm, ne_of_gt hkp, ne_of_gt hkc,
    ne_of_gt hwm, ne_of_gt hwp, hpm, hpp, ne_of_gt hnm, ne_of_gt hnp]
  all_goals ring_nf
  all_goals field_simp [ne_of_gt hnm, ne_of_gt hnp]
  all_goals ring

lemma W_next (z y : ℝ) (hz : z ∈ Set.Ico (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    W ((2 - z)⁻¹) y = kernelK (2 - z) y := by
  have hs := unit_sq_le hy
  have hp : 1 < 2 - z := by linarith [hz.2]
  have hne : 2 - z ≠ 0 := by linarith
  have hgap : (2-z) ^ 2 - y ^ 2 ≠ 0 := by nlinarith
  unfold W kernelK gap
  field_simp
  <;> ring

/-- The explicit3/2 rational subsolution has a positive increasing residual. -/
theorem transfer_subsolution_cone (z : ℝ) (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    Cone (fun y => transfer (fun _ => 1) y + (3/2) * transfer (W z) y -
      (3/2) * W ((2-z)⁻¹) y) := by
  have hh : 1 - z ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hz.2], by linarith [hz.1]⟩
  apply (residualD_cone.add ((residualR_cone hh).scale (by norm_num : (0 : ℝ) ≤ 3/2))).congr_on
  intro y hy
  have hb2 := branch_W 2 z y (by norm_num) hz hy
  have hb4 := branch_W 4 z y (by norm_num) hz hy
  have hw := W_next z y hz hy
  have hD := residualD_identity y hy
  have hR := residualR_identity (1-z) y hh hy
  rw [show 3 - (1-z) = 2+z by ring, show 3 + (1-z) = 4-z by ring,
    show 5 - (1-z) = 4+z by ring] at hR
  change residualD y + (3/2)*residualR (1-z) y = _
  rw [transfer_one y hy, transfer, hb2, hb4, hw]
  linarith


def approx : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun x => transfer (fun _ => 1) x + transfer (approx t) x

def criticalPoint (t : ℕ) : ℝ := (t : ℝ) / ((t : ℝ) + 1)

lemma criticalPoint_mem (t : ℕ) : criticalPoint t ∈ Set.Ico (0 : ℝ) 1 := by
  have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg t
  unfold criticalPoint
  exact ⟨div_nonneg ht (by positivity), (div_lt_one (by positivity)).mpr (by linarith)⟩

lemma criticalPoint_next (t : ℕ) : (2 - criticalPoint t)⁻¹ = criticalPoint (t + 1) := by
  have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg t
  have h1 : (t : ℝ) + 1 ≠ 0 := by linarith
  have he : 2 - (t : ℝ) / ((t : ℝ) + 1) = ((t : ℝ) + 2) / ((t : ℝ) + 1) := by
    field_simp [h1]
    <;> ring
  unfold criticalPoint
  rw [he, inv_div]
  push_cast
  rw [show (t : ℝ) + 1 + 1 = (t : ℝ) + 2 by ring]

lemma transfer_scale (c : ℝ) (f : ℝ → ℝ) :
    transfer (fun x => c * f x) = fun x => c * transfer f x := by
  funext x
  unfold transfer branch
  ring

/-- Finite two-branch iterates dominate an explicit rational function in the
positive increasing cone. No infinite series or prime-grid estimate is assumed. -/
theorem approx_lower_cone (t : ℕ) :
    Cone (fun y => approx t y - (3/2) * W (criticalPoint t) y) := by
  induction t with
  | zero =>
    simpa [approx, criticalPoint, W] using (Cone.const (by norm_num : (0 : ℝ) ≤ 0))
  | succ t ih =>
    have hT := transfer_cone ih
    have hR := transfer_subsolution_cone (criticalPoint t) (criticalPoint_mem t)
    apply (hR.add hT).congr_on
    intro x hx
    change (transfer (fun _ => 1) x + (3/2)*transfer (W (criticalPoint t)) x -
      (3/2)*W ((2-criticalPoint t)⁻¹) x) +
      transfer (fun y => approx t y - (3/2)*W (criticalPoint t) y) x =
      transfer (fun _ => 1) x + transfer (approx t) x - (3/2)*W (criticalPoint (t+1)) x
    rw [transfer_sub, transfer_scale, criticalPoint_next]
    ring

theorem approx_lower (t : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (3/2)*W (criticalPoint t) x ≤ approx t x := by
  have h := (approx_lower_cone t).1 x hx
  linarith


open MeasureTheory
local instance : NormedAlgebra ℝ ℝ := NormedAlgebra.id ℝ
local instance : NormedSpace ℝ ℝ := NormedAlgebra.toNormedSpace ℝ

lemma W_den_pos (z x : ℝ) (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 < 1 - z ^ 2 * x ^ 2 := by
  have hz2 : z ^ 2 < 1 := by nlinarith [hz.1, hz.2]
  have hs := unit_sq_le hx
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg z)
  nlinarith

lemma W_cone (z : ℝ) (hz : z ∈ Set.Ico (0 : ℝ) 1) : Cone (W z) := by
  have hi : Cone (fun x : ℝ => (1-z^2*x^2)⁻¹) := by
    constructor
    · intro x hx
      exact inv_nonneg.mpr (W_den_pos z x hz hx).le
    · intro x hx y hy hxy
      apply (inv_le_inv₀ (W_den_pos z x hz hx) (W_den_pos z y hz hy)).mpr
      have hs : x^2 ≤ y^2 := pow_le_pow_left₀ hx.1 hxy 2
      nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg z)]
  apply ((Cone.id.mul hi).scale (sq_nonneg z)).congr_on
  intro x hx
  unfold W
  ring

lemma approx_cone (t : ℕ) : Cone (approx t) := by
  induction t with
  | zero => simpa only [approx] using (Cone.const (le_refl (0 : ℝ)))
  | succ t ih => exact (transfer_cone (Cone.const (by norm_num : (0 : ℝ) ≤ 1))).add (transfer_cone ih)

lemma Cone.intervalIntegrable {w : ℝ → ℝ} (hw : Cone w) : IntervalIntegrable w volume 0 1 := by
  have hm : MonotoneOn w (Set.uIcc (0 : ℝ) 1) := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hw.2
  exact hm.intervalIntegrable

def logPrimitive (z x : ℝ) : ℝ := -(1/2)*Real.log (1-z^2*x^2)

lemma hasDerivAt_logPrimitive (z x : ℝ) (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt (logPrimitive z) (W z x) x := by
  have hi : HasDerivAt (fun y : ℝ => 1-z^2*y^2) (-2*z^2*x) x := by
    convert! (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_pow 2 x).const_mul (z^2)) using 1 <;> ring
  have hl := (hi.log (ne_of_gt (W_den_pos z x hz hx))).const_mul (-(1/2) : ℝ)
  convert! hl using 1 <;> first | rfl | (unfold W; ring)

lemma integral_W (z : ℝ) (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..1, W z x) = -(1/2)*Real.log (1-z^2) := by
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (logPrimitive z) (W z x) x := by
    intro x hx
    apply hasDerivAt_logPrimitive z x hz
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (W_cone z hz).intervalIntegrable
  simpa [logPrimitive] using h

/-- A logarithmic integral lower bound for the finite TWO-BRANCH transfer
iterates. The full real ECF recurrence and the prime grid remain to be bridged. -/
theorem integral_approx_lower (t : ℕ) :
    -(3/4)*Real.log (1-(criticalPoint t)^2) ≤ ∫ x in (0 : ℝ)..1, approx t x := by
  have hw := ((W_cone (criticalPoint t) (criticalPoint_mem t)).scale
    (by norm_num : (0 : ℝ) ≤ 3/2)).intervalIntegrable
  have ha := (approx_cone t).intervalIntegrable
  have hm := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hw ha
    (fun x hx => approx_lower t x hx)
  rw [intervalIntegral.integral_const_mul, integral_W (criticalPoint t) (criticalPoint_mem t)] at hm
  linarith

end
end ThetaLongHaul.TransferCone
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


end
end ThetaLongHaul.RealECF

namespace ThetaLongHaul.TransferCone
noncomputable section
open Finset MeasureTheory

def transferFrom (d : ℕ) (w : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑' q : ℕ, branch (2*((q+d+1 : ℕ) : ℝ)) w y

lemma indexed_branch_cone (d q : ℕ) {w : ℝ → ℝ} (hw : Cone w) :
    Cone (branch (2*((q+d+1 : ℕ) : ℝ)) w) := by
  have h : (1 : ℝ) ≤ ((q+d+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ q+d+1 by omega)
  exact branch_cone (by linarith) hw

lemma indexed_branch_bound (d q : ℕ) {w : ℝ → ℝ} (hw : Cone w)
    (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    branch (2*((q+d+1 : ℕ) : ℝ)) w y ≤ w 1 * (((q+1 : ℕ) : ℝ)⁻¹)^2 := by
  let c : ℝ := 2*((q+d+1 : ℕ) : ℝ)
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hc : 2 ≤ c := by dsimp [c]; push_cast; linarith
  have hdom := reciprocal_branch_mem hc hy
  have hw1 : 0 ≤ w 1 := hw.1 1 (by norm_num)
  have htop : w ((c-y)⁻¹) ≤ w 1 := hw.2 hdom.1 (by norm_num) hdom.1.2
  have hbase : 0 < ((q+1 : ℕ) : ℝ) := by positivity
  have hcy : 0 < c-y := by linarith [hy.2]
  have horder : ((q+1 : ℕ) : ℝ) ≤ c-y := by dsimp [c]; push_cast; linarith [hy.2]
  have hinv : (c-y)⁻¹ ≤ ((q+1 : ℕ) : ℝ)⁻¹ := (inv_le_inv₀ hcy hbase).mpr horder
  have hsq : ((c-y)⁻¹)^2 ≤ (((q+1 : ℕ) : ℝ)⁻¹)^2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hcy.le) hinv 2
  have hmul := mul_le_mul htop hsq (sq_nonneg ((c-y)⁻¹)) hw1
  have hplus : 0 ≤ w ((c+y)⁻¹)*((c+y)⁻¹)^2 := mul_nonneg (hw.1 _ hdom.2) (sq_nonneg _)
  exact (sub_le_self _ hplus).trans hmul

lemma reciprocalSquare_summable : Summable (fun q : ℕ => (((q+1 : ℕ) : ℝ)⁻¹)^2) := by
  have h0 : Summable (fun q : ℕ => ((q : ℝ)^2)⁻¹) := Real.summable_nat_pow_inv.mpr (by decide)
  have h1 := (summable_nat_add_iff 1).mpr h0
  simpa only [inv_pow] using h1


end
end ThetaLongHaul.TransferCone


/-! Independently authored branch integration lemmas; REAL_ECF_SKETCH.md contains
our derivation before Lean. ECF context: Lageler2024,
DOI10.1007/s12188-024-00283-3 (refereed); no external proof code.
The full real-prefix adjoint and prime-grid/tail bounds remain open. -/
namespace ThetaLongHaul.RealECF
noncomputable section
open MeasureTheory
open ThetaLongHaul.TransferCone
local instance : NormedAlgebra ℝ ℝ := NormedAlgebra.id ℝ
local instance : NormedSpace ℝ ℝ := NormedAlgebra.toNormedSpace ℝ

lemma weighted_integrable {w : ℝ → ℝ} (hw : IntervalIntegrable w volume 0 1)
    (hp : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ w x) (t : ℕ) :
    IntervalIntegrable (fun x => w x*realPrefix t x) volume 0 1 := by
  have hm : AEStronglyMeasurable (fun x => w x*realPrefix t x)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    hw.def'.aestronglyMeasurable.mul (prefix_measurable t).aestronglyMeasurable
  apply (hw.const_mul (t : ℝ)).mono_fun' hm
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact ⟨hx.1.le,hx.2⟩
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp x hx')]
  exact (mul_le_mul_of_nonneg_left (prefix_abs_le t x) (hp x hx')).trans_eq (mul_comm _ _)

lemma cone_weighted_integrable {w : ℝ → ℝ} (hw : Cone w) (t : ℕ) :
    IntervalIntegrable (fun x => w x*realPrefix t x) volume 0 1 :=
  weighted_integrable hw.intervalIntegrable hw.1 t

def minusWeight (c : ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ := w ((c-x)⁻¹)*((c-x)⁻¹)^2

def plusWeight (c : ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ := w ((c+x)⁻¹)*((c+x)⁻¹)^2

lemma minusWeight_cone {c : ℝ} (hc : 2 ≤ c) {w : ℝ → ℝ} (hw : Cone w) :
    Cone (minusWeight c w) := by
  have hf := hw.mul (Cone.id.pow 2)
  constructor
  · intro x hx
    have hd := (reciprocal_branch_mem hc hx).1
    exact hf.1 _ hd
  · intro x hx y hy hxy
    have hdx := (reciprocal_branch_mem hc hx).1
    have hdy := (reciprocal_branch_mem hc hy).1
    have hi : (c-x)⁻¹ ≤ (c-y)⁻¹ := by
      apply (inv_le_inv₀ (by linarith [hx.2]) (by linarith [hy.2])).mpr
      linarith
    exact hf.2 hdx hdy hi

lemma plusWeight_properties {c : ℝ} (hc : 2 ≤ c) {w : ℝ → ℝ} (hw : Cone w) :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ plusWeight c w x) ∧
      AntitoneOn (plusWeight c w) (Set.Icc 0 1) := by
  have hf := hw.mul (Cone.id.pow 2)
  constructor
  · intro x hx
    have hd := (reciprocal_branch_mem hc hx).2
    exact hf.1 _ hd
  · intro x hx y hy hxy
    have hdx := (reciprocal_branch_mem hc hx).2
    have hdy := (reciprocal_branch_mem hc hy).2
    have hi : (c+y)⁻¹ ≤ (c+x)⁻¹ := by
      apply (inv_le_inv₀ (by linarith [hy.1]) (by linarith [hx.1])).mpr
      linarith
    exact hf.2 hdy hdx hi

lemma plusWeight_integrable {c : ℝ} (hc : 2 ≤ c) {w : ℝ → ℝ} (hw : Cone w) :
    IntervalIntegrable (plusWeight c w) volume 0 1 := by
  have hm : AntitoneOn (plusWeight c w) (Set.uIcc (0 : ℝ) 1) := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using (plusWeight_properties hc hw).2
  exact hm.intervalIntegrable

lemma inv_minus_deriv {c x : ℝ} (hc : 2 ≤ c) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun y : ℝ => (c-y)⁻¹) (((c-x)⁻¹)^2) x := by
  have h := ((hasDerivAt_const x c).sub (hasDerivAt_id x)).inv (show c-x ≠ 0 by linarith [hx.2])
  simpa only [zero_sub,neg_neg,one_div,inv_pow] using! h

lemma inv_plus_deriv {c x : ℝ} (hc : 2 ≤ c) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun y : ℝ => (c+y)⁻¹) (-((c+x)⁻¹)^2) x := by
  have h := ((hasDerivAt_const x c).add (hasDerivAt_id x)).inv (show c+x ≠ 0 by linarith [hx.1])
  simpa only [zero_add,neg_div,one_div,inv_pow] using! h

lemma inv_minus_cont {c : ℝ} (hc : 2 ≤ c) :
    ContinuousOn (fun y : ℝ => (c-y)⁻¹) (Set.uIcc 0 1) := by
  apply (continuous_const.sub continuous_id).continuousOn.inv₀
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  change c-x ≠ 0
  linarith [hx.2]

lemma inv_plus_cont {c : ℝ} (hc : 2 ≤ c) :
    ContinuousOn (fun y : ℝ => (c+y)⁻¹) (Set.uIcc 0 1) := by
  apply (continuous_const.add continuous_id).continuousOn.inv₀
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  change c+x ≠ 0
  linarith [hx.1]

lemma integral_inv_minus {c : ℝ} (hc : 2 ≤ c) (g : ℝ → ℝ) :
    (∫ y in (0 : ℝ)..1, g ((c-y)⁻¹)*((c-y)⁻¹)^2) = ∫ x in c⁻¹..(c-1)⁻¹, g x := by
  have hd : ∀ x ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivAt (fun y : ℝ => (c-y)⁻¹) (((c-x)⁻¹)^2) x := by
    intro x hx
    simp only [min_eq_left zero_le_one,max_eq_right zero_le_one] at hx
    exact inv_minus_deriv hc ⟨hx.1.le,hx.2.le⟩
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (g := g) (inv_minus_cont hc) hd
    (fun x hx => sq_nonneg _)
  simpa only [Function.comp_def,sub_zero] using h

lemma integral_inv_plus {c : ℝ} (hc : 2 ≤ c) (g : ℝ → ℝ) :
    (∫ y in (0 : ℝ)..1, g ((c+y)⁻¹)*((c+y)⁻¹)^2) = ∫ x in (c+1)⁻¹..c⁻¹, g x := by
  have hd : ∀ x ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivAt (fun y : ℝ => (c+y)⁻¹) (-((c+x)⁻¹)^2) x := by
    intro x hx
    simp only [min_eq_left zero_le_one,max_eq_right zero_le_one] at hx
    exact inv_plus_deriv hc ⟨hx.1.le,hx.2.le⟩
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos (g := g) (inv_plus_cont hc) hd
    (fun x hx => neg_nonpos.mpr (sq_nonneg _))
  have h' : -(∫ y in (0 : ℝ)..1, g ((c+y)⁻¹)*((c+y)⁻¹)^2) =
      ∫ x in c⁻¹..(c+1)⁻¹, g x := by
    simpa only [Function.comp_def,add_zero,mul_neg,intervalIntegral.integral_neg] using h
  have hs : (∫ x in c⁻¹..(c+1)⁻¹, g x) = -(∫ x in (c+1)⁻¹..c⁻¹, g x) := by
    rw [intervalIntegral.integral_symm]
  exact neg_injective (h'.trans hs)


lemma integrable_between {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable f volume a b := by
  apply hf.mono_set
  intro x hx
  change min a b ≤ x ∧ x ≤ max a b at hx
  change min (0 : ℝ) 1 ≤ x ∧ x ≤ max (0 : ℝ) 1
  constructor
  · rw [min_eq_left zero_le_one]
    exact (le_min ha.1 hb.1).trans hx.1
  · rw [max_eq_right zero_le_one]
    exact hx.2.trans (max_le ha.2 hb.2)

/-- Exact recurrence on one reciprocal cell. No equidistribution estimate is
used; endpoints have Lebesgue measure zero. -/
theorem cell_integral (q t : ℕ) {w : ℝ → ℝ} (hw : Cone w) :
    (∫ x in (2*((q : ℝ)+1)+1)⁻¹..(2*((q : ℝ)+1)-1)⁻¹, w x*realPrefix (t+1) x) =
      (∫ x in (2*((q : ℝ)+1)+1)⁻¹..(2*((q : ℝ)+1)-1)⁻¹, w x) +
      ∫ y in (0 : ℝ)..1, branch (2*((q : ℝ)+1)) w y*realPrefix t y := by
  let c : ℝ := 2*((q : ℝ)+1)
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hc : 2 ≤ c := by dsimp [c]; linarith
  have hwM := (minusWeight_cone hc hw).intervalIntegrable
  have hwP := plusWeight_integrable hc hw
  have heM := weighted_integrable hwM (minusWeight_cone hc hw).1 t
  have heP := weighted_integrable hwP (plusWeight_properties hc hw).1 t
  have hmid : c⁻¹ ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [sub_zero] using (reciprocal_branch_mem hc (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)).1
  have hlo : (c+1)⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
    (reciprocal_branch_mem hc (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)).2
  have hhi : (c-1)⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
    (reciprocal_branch_mem hc (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)).1
  have hEW := cone_weighted_integrable hw (t+1)
  have heAdd := intervalIntegral.integral_add_adjacent_intervals
    (integrable_between hEW hlo hmid) (integrable_between hEW hmid hhi)
  have hwAdd := intervalIntegral.integral_add_adjacent_intervals
    (integrable_between hw.intervalIntegrable hlo hmid) (integrable_between hw.intervalIntegrable hmid hhi)
  have hEM : (∫ x in c⁻¹..(c-1)⁻¹, w x*realPrefix (t+1) x) =
      (∫ y in (0 : ℝ)..1, minusWeight c w y) +
        ∫ y in (0 : ℝ)..1, minusWeight c w y*realPrefix t y := by
    calc
      _ = ∫ y in (0 : ℝ)..1, (w ((c-y)⁻¹)*realPrefix (t+1) ((c-y)⁻¹))*((c-y)⁻¹)^2 :=
        (integral_inv_minus hc _).symm
      _ = ∫ y in (0 : ℝ)..1, (minusWeight c w y+minusWeight c w y*realPrefix t y) := by
        apply intervalIntegral.integral_congr_uIoo
        intro y hy
        rw [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
        have h := prefix_minus t q y hy
        change realPrefix (t+1) ((c-y)⁻¹) = 1+realPrefix t y at h
        dsimp only
        rw [h]
        unfold minusWeight
        ring
      _ = _ := intervalIntegral.integral_add hwM heM
  have hEP : (∫ x in (c+1)⁻¹..c⁻¹, w x*realPrefix (t+1) x) =
      (∫ y in (0 : ℝ)..1, plusWeight c w y) -
        ∫ y in (0 : ℝ)..1, plusWeight c w y*realPrefix t y := by
    calc
      _ = ∫ y in (0 : ℝ)..1, (w ((c+y)⁻¹)*realPrefix (t+1) ((c+y)⁻¹))*((c+y)⁻¹)^2 :=
        (integral_inv_plus hc _).symm
      _ = ∫ y in (0 : ℝ)..1, (plusWeight c w y-plusWeight c w y*realPrefix t y) := by
        apply intervalIntegral.integral_congr_uIoo
        intro y hy
        rw [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
        have h := prefix_plus t q y hy
        change realPrefix (t+1) ((c+y)⁻¹) = 1-realPrefix t y at h
        dsimp only
        rw [h]
        unfold plusWeight
        ring
      _ = _ := intervalIntegral.integral_sub hwP heP
  have hWM : (∫ x in c⁻¹..(c-1)⁻¹, w x) = ∫ y in (0 : ℝ)..1, minusWeight c w y :=
    (integral_inv_minus hc w).symm
  have hWP : (∫ x in (c+1)⁻¹..c⁻¹, w x) = ∫ y in (0 : ℝ)..1, plusWeight c w y :=
    (integral_inv_plus hc w).symm
  have hB : (∫ y in (0 : ℝ)..1, branch c w y*realPrefix t y) =
      (∫ y in (0 : ℝ)..1, minusWeight c w y*realPrefix t y) -
        ∫ y in (0 : ℝ)..1, plusWeight c w y*realPrefix t y := by
    calc
      _ = ∫ y in (0 : ℝ)..1, (minusWeight c w y*realPrefix t y-plusWeight c w y*realPrefix t y) := by
        congr 1
        funext y
        unfold branch minusWeight plusWeight
        ring
      _ = _ := intervalIntegral.integral_sub heM heP
  change (∫ x in (c+1)⁻¹..(c-1)⁻¹, w x*realPrefix (t+1) x) =
    (∫ x in (c+1)⁻¹..(c-1)⁻¹, w x) + ∫ y in (0 : ℝ)..1, branch c w y*realPrefix t y
  linarith


open Filter Topology Finset

def endpoint (N : ℕ) : ℝ := (2*(N : ℝ)+1)⁻¹

def branchIntegral (w : ℝ → ℝ) (t q : ℕ) : ℝ :=
  ∫ y in (0 : ℝ)..1, branch (2*((q : ℝ)+1)) w y*realPrefix t y

lemma endpoint_mem (N : ℕ) : endpoint N ∈ Set.Icc (0 : ℝ) 1 := by
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  unfold endpoint
  exact ⟨inv_nonneg.mpr (by linarith), (inv_le_one₀ (by linarith)).mpr (by linarith)⟩

lemma endpoint_plus (N : ℕ) : (2*((N : ℝ)+1)+1)⁻¹ = endpoint (N+1) := by
  unfold endpoint
  push_cast
  congr 1 <;> ring

lemma endpoint_minus (N : ℕ) : (2*((N : ℝ)+1)-1)⁻¹ = endpoint N := by
  unfold endpoint
  congr 1 <;> ring

/-- Finite exact telescoping identity, before taking the endpoint limit. -/
theorem finite_telescope (N t : ℕ) {w : ℝ → ℝ} (hw : Cone w) :
    (∫ x in endpoint N..1, w x*realPrefix (t+1) x) =
      (∫ x in endpoint N..1, w x) + ∑ q ∈ range N, branchIntegral w t q := by
  induction N with
  | zero => simp [endpoint]
  | succ N ih =>
    have hcell := cell_integral N t hw
    rw [endpoint_plus,endpoint_minus] at hcell
    change (∫ x in endpoint (N+1)..endpoint N, w x*realPrefix (t+1) x) =
      (∫ x in endpoint (N+1)..endpoint N, w x) + branchIntegral w t N at hcell
    have he := cone_weighted_integrable hw (t+1)
    have hEadd := intervalIntegral.integral_add_adjacent_intervals
      (integrable_between he (endpoint_mem (N+1)) (endpoint_mem N))
      (integrable_between he (endpoint_mem N) (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1))
    have hWadd := intervalIntegral.integral_add_adjacent_intervals
      (integrable_between hw.intervalIntegrable (endpoint_mem (N+1)) (endpoint_mem N))
      (integrable_between hw.intervalIntegrable (endpoint_mem N) (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1))
    rw [← hEadd,← hWadd,hcell,ih,sum_range_succ]
    ring

lemma endpoint_tendsto_zero : Tendsto endpoint atTop (𝓝 (0 : ℝ)) := by
  apply squeeze_zero (fun N => (endpoint_mem N).1)
    (fun N => show endpoint N ≤ 1/((N : ℝ)+1) from ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  unfold endpoint
  rw [one_div]
  apply (inv_le_inv₀ (by linarith) (by linarith)).mpr
  linarith

lemma omitted_integral_bound {f : ℝ → ℝ} {B : ℝ}
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f x‖ ≤ B) (N : ℕ) :
    ‖∫ x in (0 : ℝ)..endpoint N, f x‖ ≤ B*endpoint N := by
  have he := endpoint_mem N
  have hb : ∀ x ∈ Set.uIoc (0 : ℝ) (endpoint N), ‖f x‖ ≤ B := by
    intro x hx
    rw [Set.uIoc_of_le he.1] at hx
    exact hf x ⟨hx.1.le,hx.2.trans he.2⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa only [sub_zero,abs_of_nonneg he.1] using h

lemma omitted_integral_tendsto {f : ℝ → ℝ} {B : ℝ}
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f x‖ ≤ B) :
    Tendsto (fun N => ∫ x in (0 : ℝ)..endpoint N, f x) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun N => omitted_integral_bound hf N)
  simpa only [mul_zero] using (tendsto_const_nhds (x := B)).mul endpoint_tendsto_zero

lemma integral_endpoint_tendsto {f : ℝ → ℝ} {B : ℝ}
    (hi : IntervalIntegrable f volume 0 1)
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f x‖ ≤ B) :
    Tendsto (fun N => ∫ x in endpoint N..1, f x) atTop (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  have he (N : ℕ) : (∫ x in endpoint N..1, f x) =
      (∫ x in (0 : ℝ)..1, f x) - ∫ x in (0 : ℝ)..endpoint N, f x := by
    have h := intervalIntegral.integral_add_adjacent_intervals
      (integrable_between hi (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1) (endpoint_mem N))
      (integrable_between hi (endpoint_mem N) (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1))
    linarith
  simp_rw [he]
  simpa only [sub_zero] using tendsto_const_nhds.sub (omitted_integral_tendsto hf)

lemma weighted_prefix_bound {w : ℝ → ℝ} (hw : Cone w) (t : ℕ)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖w x*realPrefix t x‖ ≤ (t : ℝ)*w 1 := by
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hw.1 x hx)]
  have ht := hw.2 hx (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1) hx.2
  have h := mul_le_mul ht (prefix_abs_le t x) (abs_nonneg _) (hw.1 1 (by norm_num))
  simpa only [mul_comm] using h


lemma branchIntegral_bound {w : ℝ → ℝ} (hw : Cone w) (t q : ℕ) :
    ‖branchIntegral w t q‖ ≤ ((t : ℝ)*w 1)*(((q+1 : ℕ) : ℝ)⁻¹)^2 := by
  have hc : Cone (branch (2*((q : ℝ)+1)) w) := by
    simpa only [Nat.add_zero,Nat.cast_add,Nat.cast_one] using indexed_branch_cone 0 q hw
  have hb : ∀ y ∈ Set.uIoc (0 : ℝ) 1,
      ‖branch (2*((q : ℝ)+1)) w y*realPrefix t y‖ ≤ ((t : ℝ)*w 1)*(((q+1 : ℕ) : ℝ)⁻¹)^2 := by
    intro y hy
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
    have hy' : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le,hy.2⟩
    have htop : branch (2*((q : ℝ)+1)) w y ≤ w 1*(((q+1 : ℕ) : ℝ)⁻¹)^2 := by
      simpa only [Nat.add_zero,Nat.cast_add,Nat.cast_one] using indexed_branch_bound 0 q hw y hy'
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hc.1 y hy')]
    have hB : 0 ≤ w 1*(((q+1 : ℕ) : ℝ)⁻¹)^2 :=
      mul_nonneg (hw.1 1 (by norm_num)) (sq_nonneg _)
    have hm := mul_le_mul htop (prefix_abs_le t y) (abs_nonneg _) hB
    calc
      _ ≤ (w 1*(((q+1 : ℕ) : ℝ)⁻¹)^2)*(t : ℝ) := hm
      _ = _ := by ring
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa only [branchIntegral,sub_zero,abs_one,mul_one] using h

lemma branchIntegral_summable {w : ℝ → ℝ} (hw : Cone w) (t : ℕ) :
    Summable (branchIntegral w t) := by
  have hn : Summable (fun q : ℕ => ‖branchIntegral w t q‖) :=
    Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => branchIntegral_bound hw t q)
      (reciprocalSquare_summable.mul_left ((t : ℝ)*w 1))
  exact hn.of_norm

/-- Exact full-branch scalar recurrence, obtained without exchanging a full
operator and an integral. -/
theorem weighted_series_identity (t : ℕ) {w : ℝ → ℝ} (hw : Cone w) :
    (∫ x in (0 : ℝ)..1, w x*realPrefix (t+1) x) =
      (∫ x in (0 : ℝ)..1, w x) + ∑' q : ℕ, branchIntegral w t q := by
  have hbW : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖w x‖ ≤ w 1 := by
    intro x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (hw.1 x hx)]
    exact hw.2 hx (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1) hx.2
  have hL := integral_endpoint_tendsto (cone_weighted_integrable hw (t+1)) (weighted_prefix_bound hw (t+1))
  have hW := integral_endpoint_tendsto hw.intervalIntegrable hbW
  have hS := (branchIntegral_summable hw t).hasSum.tendsto_sum_nat
  have hR := hW.add hS
  have hR' : Tendsto (fun N => ∫ x in endpoint N..1, w x*realPrefix (t+1) x)
      atTop (𝓝 ((∫ x in (0 : ℝ)..1, w x) + ∑' q : ℕ, branchIntegral w t q)) := by
    have he : (fun N => ∫ x in endpoint N..1, w x*realPrefix (t+1) x) =
        (fun N => (∫ x in endpoint N..1, w x) + ∑ q ∈ range N, branchIntegral w t q) := by
      funext N
      exact finite_telescope N t hw
    rw [he]
    exact hR
  exact tendsto_nhds_unique hL hR'

/-- Every positive increasing weight has a nonnegative actual real ECF mean. -/
theorem weighted_prefix_nonneg (t : ℕ) {w : ℝ → ℝ} (hw : Cone w) :
    0 ≤ ∫ x in (0 : ℝ)..1, w x*realPrefix t x := by
  induction t generalizing w with
  | zero => simp [realPrefix]
  | succ t ih =>
    rw [weighted_series_identity t hw]
    apply add_nonneg (intervalIntegral.integral_nonneg (by norm_num) hw.1)
    apply tsum_nonneg
    intro q
    apply ih
    simpa only [Nat.add_zero,Nat.cast_add,Nat.cast_one] using indexed_branch_cone 0 q hw


theorem two_branch_mean_step (t : ℕ) {w : ℝ → ℝ} (hw : Cone w) :
    (∫ x in (0 : ℝ)..1, w x) + (∫ x in (0 : ℝ)..1, transfer w x*realPrefix t x) ≤
      ∫ x in (0 : ℝ)..1, w x*realPrefix (t+1) x := by
  have hs := Summable.sum_add_tsum_nat_add 2 (branchIntegral_summable hw t)
  have hfin : (∑ q ∈ range 2, branchIntegral w t q) = branchIntegral w t 0+branchIntegral w t 1 := by
    simp [sum_range_succ]
  rw [hfin] at hs
  have htail : 0 ≤ ∑' q : ℕ, branchIntegral w t (q+2) := by
    apply tsum_nonneg
    intro q
    apply weighted_prefix_nonneg t
    simpa only [Nat.add_zero,Nat.cast_add,Nat.cast_one] using indexed_branch_cone 0 (q+2) hw
  have h0 := cone_weighted_integrable (branch_cone (by norm_num : (2 : ℝ) ≤ 2) hw) t
  have h1 := cone_weighted_integrable (branch_cone (by norm_num : (2 : ℝ) ≤ 4) hw) t
  have hL : (∫ x in (0 : ℝ)..1, transfer w x*realPrefix t x) =
      (∫ x in (0 : ℝ)..1, branch 2 w x*realPrefix t x) +
        ∫ x in (0 : ℝ)..1, branch 4 w x*realPrefix t x := by
    simpa only [transfer,add_mul] using intervalIntegral.integral_add h0 h1
  have hLI : (∫ x in (0 : ℝ)..1, transfer w x*realPrefix t x) =
      branchIntegral w t 0+branchIntegral w t 1 := by
    convert hL using 1 <;> norm_num [branchIntegral]
  have he := weighted_series_identity t hw
  linarith

lemma transfer_add_linear (f g : ℝ → ℝ) :
    transfer (fun x => f x+g x) = fun x => transfer f x+transfer g x := by
  funext x
  unfold transfer branch
  ring

def totalAdjoint : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, _ => fun _ => 0
  | t+1, w => fun x => w x+totalAdjoint t (transfer w) x

lemma totalAdjoint_cone (t : ℕ) {w : ℝ → ℝ} (hw : Cone w) : Cone (totalAdjoint t w) := by
  induction t generalizing w with
  | zero => simpa only [totalAdjoint] using (Cone.const (le_refl (0 : ℝ)))
  | succ t ih => exact hw.add (ih (transfer_cone hw))

lemma totalAdjoint_commute (t : ℕ) (w : ℝ → ℝ) :
    totalAdjoint t (transfer w) = transfer (totalAdjoint t w) := by
  induction t generalizing w with
  | zero =>
    funext x
    simp only [totalAdjoint,transfer,branch]
    ring
  | succ t ih =>
    funext x
    change transfer w x+totalAdjoint t (transfer (transfer w)) x =
      transfer (fun y => w y+totalAdjoint t (transfer w) y) x
    rw [ih (transfer w),transfer_add_linear]

lemma totalAdjoint_one (t : ℕ) :
    totalAdjoint (t+1) (fun _ => 1) = fun x => 1+approx t x := by
  induction t with
  | zero => funext x; simp [totalAdjoint,approx]
  | succ t ih =>
    funext x
    change 1+totalAdjoint (t+1) (transfer (fun _ => 1)) x = 1+approx (t+1) x
    rw [totalAdjoint_commute (t+1) (fun _ => 1),ih,transfer_add_linear]
    simp only [approx] <;> ring

theorem weighted_totalAdjoint_lower (t : ℕ) {w : ℝ → ℝ} (hw : Cone w) :
    (∫ x in (0 : ℝ)..1, totalAdjoint t w x) ≤ ∫ x in (0 : ℝ)..1, w x*realPrefix t x := by
  induction t generalizing w with
  | zero => simp [totalAdjoint,realPrefix]
  | succ t ih =>
    have hs := two_branch_mean_step t hw
    have hi := ih (transfer_cone hw)
    have he : (∫ x in (0 : ℝ)..1, totalAdjoint (t+1) w x) =
        (∫ x in (0 : ℝ)..1, w x) + ∫ x in (0 : ℝ)..1, totalAdjoint t (transfer w) x := by
      change (∫ x in (0 : ℝ)..1, w x+totalAdjoint t (transfer w) x) = _
      exact intervalIntegral.integral_add hw.intervalIntegrable
        (totalAdjoint_cone t (transfer_cone hw)).intervalIntegrable
    rw [he]
    linarith

/-- Actual real ECF prefix means grow at least logarithmically. This is NOT a
fixed-prime-grid or signed-tail estimate, so it does not settle the theta root. -/
theorem real_prefix_integral_lower (t : ℕ) :
    1-(3/4)*Real.log (1-(criticalPoint t)^2) ≤ ∫ x in (0 : ℝ)..1, realPrefix (t+1) x := by
  have h := weighted_totalAdjoint_lower (t+1) (Cone.const (by norm_num : (0 : ℝ) ≤ 1))
  rw [totalAdjoint_one] at h
  rw [intervalIntegral.integral_add intervalIntegrable_const (approx_cone t).intervalIntegrable] at h
  simp only [intervalIntegral.integral_const,sub_zero,one_smul,one_mul] at h
  have hl := integral_approx_lower t
  linarith

end
end ThetaLongHaul.RealECF


/-! Independently authored consequence of the checked logarithmic mean theorem.
See EVENTUAL_GROWTH_REDUCTION_SKETCH.md. No prime-grid/tail estimate is assumed. -/
namespace ThetaLongHaul.RealECF
noncomputable section
open Filter Topology MeasureTheory ThetaLongHaul.TransferCone

lemma criticalPoint_tendsto_one : Tendsto criticalPoint atTop (𝓝 (1 : ℝ)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    tendsto_one_div_add_atTop_nhds_zero_nat
  convert h using 1
  · funext t
    dsimp [criticalPoint]
    have hn : (t : ℝ)+1 ≠ 0 := by positivity
    field_simp
    ring
  · norm_num

lemma prefix_integral_unbounded (B : ℝ) : ∃ t : ℕ,
    B < ∫ x in (0 : ℝ)..1, realPrefix t x := by
  have hdpos : ∀ t : ℕ, 0 < 1-(criticalPoint t)^2 := by
    intro t
    simpa using W_den_pos (criticalPoint t) 1 (criticalPoint_mem t)
      (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
  have hd : Tendsto (fun t => 1-(criticalPoint t)^2) atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub (criticalPoint_tendsto_one.pow 2) using 1
    norm_num
  have hd' : Tendsto (fun t => 1-(criticalPoint t)^2) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_inf.mpr
    exact ⟨hd,tendsto_principal.mpr (Filter.Eventually.of_forall hdpos)⟩
  have hl := Real.tendsto_log_nhdsGT_zero.comp hd'
  have hs := hl.const_mul_atBot_of_neg (by norm_num : (-3/4 : ℝ) < 0)
  rcases (hs.eventually_gt_atTop B).exists with ⟨t,ht⟩
  refine ⟨t+1,?_⟩
  have hb := real_prefix_integral_lower t
  change B < (-3/4)*Real.log (1-(criticalPoint t)^2) at ht
  linarith

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
end ThetaLongHaul.RealECF

theorem OMA.solution : OMA.R_Arxiv_2501_03234_conjecture_4_4_R1.H1 := by
  unfold OMA.R_Arxiv_2501_03234_conjecture_4_4_R1.H1
  simpa only [ThetaLongHaul.RealECF.realPrefix_eq_explicit_rec] using
    ThetaLongHaul.RealECF.prefix_integral_unbounded
