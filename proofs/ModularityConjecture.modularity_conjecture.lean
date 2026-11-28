import FormalConjectures.Wikipedia.ModularityConjecture
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-! Shorter disproof of `ModularityConjecture.modularity_conjecture` as formalised. -/

open Complex CongruenceSubgroup UpperHalfPlane Function
open scoped MatrixGroups ModularForm

theorem OMA.disproof : ¬ (type_of% @ModularityConjecture.modularity_conjecture) := by
  intro h
  let E : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩
  have : E.IsElliptic := ⟨isUnit_iff_ne_zero.mpr (by
    simp [E, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈])⟩
  obtain ⟨N, f, hf, -⟩ := h E
  refine zero_ne_one (Eq.trans ?_ hf.1)
  symm; unfold ModularityConjecture.modularFormAn
  rcases Nat.lt_or_ge (N : ℕ) 2 with hlt | hge
  · obtain rfl : N = 1 := PNat.eq (show (N : ℕ) = 1 by have := N.pos; omega)
    have hG : (Gamma0 1 : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
      have : Gamma0 1 = ⊤ := by ext; simp [Gamma0_mem, Subsingleton.elim (_ : ZMod 1) 0]
      simp [this, MonoidHom.range_eq_map]
    let g : ModularForm 𝒮ℒ 2 := (ModularFormClass.modularForm f).copy (f : ℍ → ℂ) rfl hG.symm
    have hg : (f : ℍ → ℂ) = 0 := funext fun τ =>
      congrFun (congrArg DFunLike.coe (rank_zero_iff_forall_zero.mp
        ModularForm.levelOne_weight_two_rank_zero g)) τ
    rw [hg, qExpansion_zero]; simp
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
    have h1 : (1 : ℝ) ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
    have hNmem : ((N : ℕ) : ℝ) ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
      rw [strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples_iff.mpr ⟨(N : ℕ), by simp⟩
    have : Fact (IsCusp OnePoint.infty (Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :=
      ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
    let c : ℕ → ℂ := fun n => if (N : ℕ) ∣ n then (qExpansion (1 : ℝ) f).coeff (n / N) else 0
    have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam ((N : ℕ) : ℝ) τ ^ m) (f τ) :=
      fun τ => ((mul_right_injective₀ N.pos.ne').hasSum_iff fun n hn => by
        simp [c, show ¬ (N : ℕ) ∣ n from fun ⟨k, hk⟩ => hn ⟨k, hk.symm⟩]).mp <| by
        convert ModularForm.hasSum_qExpansion f one_pos h1 τ using 1
        funext m
        have hq : Periodic.qParam (1 : ℝ) τ = Periodic.qParam ((N : ℕ) : ℝ) τ ^ (N : ℕ) := by
          simp only [Periodic.qParam]; rw [← Complex.exp_nat_mul]; congr 1
          have : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast N.pos.ne'
          push_cast; field_simp
        simp only [comp_apply, c, dvd_mul_right, if_true, Nat.mul_div_cancel_left m N.pos,
          smul_eq_mul, pow_mul, ← hq]
    rw [← qExpansion_coeff_unique f hNpos
      (ModularFormClass.analyticAt_cuspFunction_zero f hNpos hNmem) hsum 1]
    simp [c, show ¬ (N : ℕ) ∣ 1 from fun hd => by have := Nat.le_of_dvd one_pos hd; omega]
