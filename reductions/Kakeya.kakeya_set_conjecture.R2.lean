import FormalConjectures.Wikipedia.Kakeya
import Mathlib

open MeasureTheory AffineMap Metric
open scoped ENNReal

namespace OMA.R_Kakeya_kakeya_set_conjecture_R2

def H1 : Prop := ∀ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))),
    dimH {x : EuclideanSpace ℝ (Fin (n + 1)) | WithLp.toLp 2 (fun i : Fin n => x i.castSucc) ∈ K}
      ≤ dimH K + 1

def H2 : Prop := ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), Kakeya.IsKakeya S → (n : ℝ≥0∞) ≤ dimH S

lemma norm_drop_le {n : ℕ} (w : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖(WithLp.toLp 2 (fun i : Fin n => w i.castSucc) : EuclideanSpace ℝ (Fin n))‖ ≤ ‖w‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_castSucc]
  exact le_add_of_nonneg_right (by positivity)

lemma exists_unit_dir {n : ℕ} (hn : 0 < n) (u : EuclideanSpace ℝ (Fin n)) :
    ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 ∧ u = ‖u‖ • v := by
  by_cases hu : u = 0
  · refine ⟨EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ), by simp, ?_⟩
    simp [hu]
  · have hpos : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    refine ⟨‖u‖⁻¹ • u, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos]
    · rw [smul_smul, mul_inv_cancel₀ hpos, one_smul]

lemma isKakeya_cylinder {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : Kakeya.IsKakeya K) :
    Kakeya.IsKakeya
      {x : EuclideanSpace ℝ (Fin (n + 1)) | WithLp.toLp 2 (fun i : Fin n => x i.castSucc) ∈ K} := by
  intro w hw
  obtain ⟨v, hv, huv⟩ := exists_unit_dir hn
    (WithLp.toLp 2 (fun i : Fin n => w i.castSucc) : EuclideanSpace ℝ (Fin n))
  have hle : ‖(WithLp.toLp 2 (fun i : Fin n => w i.castSucc) : EuclideanSpace ℝ (Fin n))‖ ≤ 1 :=
    hw ▸ norm_drop_le w
  obtain ⟨a, ha⟩ := hK v hv
  refine ⟨WithLp.toLp 2 (Fin.snoc (fun i : Fin n => a i) (0 : ℝ)), ?_⟩
  rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
  have key : (WithLp.toLp 2 (fun i : Fin n =>
      (lineMap (WithLp.toLp 2 (Fin.snoc (fun i : Fin n => a i) (0 : ℝ)) :
          EuclideanSpace ℝ (Fin (n + 1)))
        (WithLp.toLp 2 (Fin.snoc (fun i : Fin n => a i) (0 : ℝ)) + w) t) i.castSucc) :
        EuclideanSpace ℝ (Fin n))
      = lineMap a (a + v)
          (t * ‖(WithLp.toLp 2 (fun i : Fin n => w i.castSucc) : EuclideanSpace ℝ (Fin n))‖) := by
    have h2 : ∀ i : Fin n, w i.castSucc =
        ‖(WithLp.toLp 2 (fun i : Fin n => w i.castSucc) : EuclideanSpace ℝ (Fin n))‖ * v i := by
      intro i
      have := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i) huv
      simpa using this
    ext i
    simp only [lineMap_apply, vadd_eq_add, vsub_eq_sub, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, Fin.snoc_castSucc, add_sub_cancel_left]
    rw [h2 i]
    ring
  show (WithLp.toLp 2 (fun i : Fin n => _) : EuclideanSpace ℝ (Fin n)) ∈ K
  rw [key]
  exact ha ⟨_, ⟨mul_nonneg ht0 (norm_nonneg _), mul_le_one₀ ht1 (norm_nonneg _) hle⟩, rfl⟩

lemma lift_kakeya (h1 : H1) {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : Kakeya.IsKakeya K) (j : ℕ) :
    ∃ S : Set (EuclideanSpace ℝ (Fin (n + j))), Kakeya.IsKakeya S ∧ dimH S ≤ dimH K + j := by
  induction j with
  | zero => exact ⟨K, hK, by simp⟩
  | succ j ih =>
    obtain ⟨S, hS, hd⟩ := ih
    refine ⟨{x : EuclideanSpace ℝ (Fin (n + j + 1)) |
      WithLp.toLp 2 (fun i : Fin (n + j) => x i.castSucc) ∈ S},
      isKakeya_cylinder (Nat.add_pos_left hn j) hS, ?_⟩
    calc dimH {x : EuclideanSpace ℝ (Fin (n + j + 1)) |
          WithLp.toLp 2 (fun i : Fin (n + j) => x i.castSucc) ∈ S}
        ≤ dimH S + 1 := h1 (n + j) S
      _ ≤ dimH K + j + 1 := by gcongr
      _ = dimH K + (j + 1 : ℕ) := by push_cast; rw [add_assoc]

theorem main : H1 → H2 → type_of% @Kakeya.kakeya_set_conjecture := by
  intro h1 h2 n hn S hS
  apply le_antisymm
  · simpa [Real.dimH_univ_eq_finrank] using dimH_mono (Set.subset_univ S)
  · obtain ⟨m, hnm, hm⟩ := h2 n
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnm
    obtain ⟨T, hT, hd⟩ := lift_kakeya h1 hn hS j
    have h := (hm T hT).trans hd
    rw [Nat.cast_add] at h
    exact (ENNReal.add_le_add_iff_right (ENNReal.natCast_ne_top j)).mp h

end OMA.R_Kakeya_kakeya_set_conjecture_R2
