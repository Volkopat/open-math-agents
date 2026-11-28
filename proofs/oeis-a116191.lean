import OMAStatements.S_oeis_a116191
import Mathlib

namespace OMA.Helpers

open IntermediateField Cardinal

theorem trdeg_le_of_alg (S : Set ℂ) (t : Set (adjoin ℚ S))
    (h : ∀ x : adjoin ℚ S, (x : ℂ) ∈ S → IsAlgebraic (Algebra.adjoin ℚ t) x) :
    Algebra.trdeg ℚ (adjoin ℚ S) ≤ #t := by
  have hmem : ∀ x : adjoin ℚ S, x ∈ adjoin ℚ (Subtype.val ⁻¹' S : Set (adjoin ℚ S)) := by
    intro x
    apply (mem_lift (E := adjoin ℚ (Subtype.val ⁻¹' S : Set (adjoin ℚ S))) x).mp
    rw [lift_adjoin, Set.image_preimage_eq_of_subset]
    · exact x.2
    · intro y hy; exact ⟨⟨y, subset_adjoin ℚ S hy⟩, rfl⟩
  have h1 : Algebra.IsAlgebraic (adjoin ℚ (Subtype.val ⁻¹' S : Set (adjoin ℚ S))) (adjoin ℚ S) :=
    ⟨fun y => isAlgebraic_algebraMap
      (⟨y, hmem y⟩ : adjoin ℚ (Subtype.val ⁻¹' S : Set (adjoin ℚ S)))⟩
  rw [isAlgebraic_adjoin_iff_top] at h1
  have h2 : Algebra.IsAlgebraic (Algebra.adjoin ℚ t) (adjoin ℚ S) :=
    ⟨fun x => IsAlgebraic.adjoin_of_forall_isAlgebraic (fun y hy => h y hy.1) (h1.isAlgebraic x)⟩
  exact Algebra.IsAlgebraic.trdeg_le_cardinalMk ℚ t

theorem alg_of_alg {S : Set ℂ} {t : Set (adjoin ℚ S)} (x : adjoin ℚ S)
    (hx : IsAlgebraic ℚ (x : ℂ)) : IsAlgebraic (Algebra.adjoin ℚ t) x := by
  have : IsAlgebraic ℚ x := (isAlgebraic_algHom_iff (adjoin ℚ S).val Subtype.val_injective).mp hx
  exact this.extendScalars (algebraMap ℚ _).injective

theorem alg_of_mem {S : Set ℂ} {t : Set (adjoin ℚ S)} (x : adjoin ℚ S)
    (hx : x ∈ Algebra.adjoin ℚ t) : IsAlgebraic (Algebra.adjoin ℚ t) x :=
  isAlgebraic_algebraMap (⟨x, hx⟩ : Algebra.adjoin ℚ t)

theorem alg_mul {S : Set ℂ} {t : Set (adjoin ℚ S)} (x y z : adjoin ℚ S)
    (h : (x : ℂ) = y * z) (hy : IsAlgebraic (Algebra.adjoin ℚ t) y)
    (hz : IsAlgebraic (Algebra.adjoin ℚ t) z) : IsAlgebraic (Algebra.adjoin ℚ t) x := by
  have : x = y * z := Subtype.ext h
  rw [this]; exact hy.mul hz

theorem I_alg : IsAlgebraic ℚ Complex.I :=
  (IsIntegral.of_pow (n := 2) two_pos (by rw [Complex.I_sq]; exact isIntegral_one.neg)).isAlgebraic

theorem rat_alg (q : ℚ) : IsAlgebraic ℚ (q : ℂ) := by
  simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) q

end OMA.Helpers

open OMA.Helpers IntermediateField Cardinal Complex in
theorem OMA.solution : type_of% @OMA.S_oeis_a116191.main := by
  intro hS
  set L := Complex.log I with hLdef
  have hL : L = Real.pi / 2 * I := log_I
  have hexpL : exp L = I := exp_log I_ne_zero
  have hu : I ^ I = exp (L * I) := cpow_def_of_ne_zero I_ne_zero I
  have hw : I ^ (I ^ I) = exp (L * I ^ I) := cpow_def_of_ne_zero I_ne_zero _
  set r : ℝ := Real.exp (-(Real.pi / 2)) with hr
  have hur : I ^ I = (r : ℂ) := by
    rw [hu, hL, hr, ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  -- Step 1: r is irrational
  have hirr : ∀ q : ℚ, r ≠ (q : ℝ) := by
    intro q hq
    have hli : LinearIndependent ℚ ![L, L * I] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Rat.smul_def,
        hL] at hg
      have hre := congrArg Complex.re hg
      have him := congrArg Complex.im hg
      simp at hre him
      intro i; fin_cases i <;> simp [hre, him]
    have h2 := hS 2 ![L, L * I] hli
    set S := Set.range ![L, L * I] ∪ Set.range (exp ∘ ![L, L * I]) with hSdef
    have hLm : L ∈ adjoin ℚ S := subset_adjoin ℚ S (Or.inl ⟨0, rfl⟩)
    have hIm : I ∈ adjoin ℚ S := subset_adjoin ℚ S (Or.inr ⟨0, by simp [hexpL]⟩)
    have hle : Algebra.trdeg ℚ (adjoin ℚ S) ≤ #({⟨L, hLm⟩} : Set (adjoin ℚ S)) := by
      apply trdeg_le_of_alg
      intro x hx
      rcases hx with ⟨i, hi⟩ | ⟨i, hi⟩ <;> fin_cases i <;> simp at hi
      · exact alg_of_mem x (Algebra.subset_adjoin (Subtype.ext hi.symm))
      · exact alg_mul x ⟨L, hLm⟩ ⟨I, hIm⟩ hi.symm
          (alg_of_mem _ (Algebra.subset_adjoin rfl)) (alg_of_alg _ I_alg)
      · exact alg_of_alg x (by rw [← hi, hexpL]; exact I_alg)
      · exact alg_of_alg x (by rw [← hi, ← hu, hur, hq]; push_cast; exact rat_alg q)
    rw [mk_singleton] at hle
    have := h2.trans hle
    norm_cast at this
  -- Step 2
  refine fun hwalg => ?_
  have hli : LinearIndependent ℚ ![L, L * I, L * I ^ I] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, Rat.smul_def, hL, hur] at hg
    have hre := congrArg Complex.re hg
    have him := congrArg Complex.im hg
    simp at hre him
    have h3 : (g 0 : ℝ) + g 2 * r = 0 := by
      have h4 : (Real.pi / 2) * ((g 0 : ℝ) + g 2 * r) = 0 := by rw [← him]; ring
      rcases mul_eq_zero.mp h4 with h | h
      · exact absurd h (by positivity)
      · exact h
    have hg2 : g 2 = 0 := by
      by_contra hne
      apply hirr (-(g 0) / g 2)
      have hne' : (g 2 : ℝ) ≠ 0 := by exact_mod_cast hne
      push_cast
      field_simp
      linarith
    have hg0 : g 0 = 0 := by
      rw [hg2] at h3
      simp at h3
      exact h3
    intro i; fin_cases i <;> simp [hre, hg0, hg2]
  have h3 := hS 3 ![L, L * I, L * I ^ I] hli
  set S := Set.range ![L, L * I, L * I ^ I] ∪ Set.range (exp ∘ ![L, L * I, L * I ^ I]) with hSdef
  have hLm : L ∈ adjoin ℚ S := subset_adjoin ℚ S (Or.inl ⟨0, rfl⟩)
  have hIm : I ∈ adjoin ℚ S := subset_adjoin ℚ S (Or.inr ⟨0, by simp [hexpL]⟩)
  have hum : I ^ I ∈ adjoin ℚ S := subset_adjoin ℚ S (Or.inr ⟨1, by simp [hu]⟩)
  have hle : Algebra.trdeg ℚ (adjoin ℚ S) ≤
      #({⟨L, hLm⟩, ⟨I ^ I, hum⟩} : Set (adjoin ℚ S)) := by
    apply trdeg_le_of_alg
    intro x hx
    rcases hx with ⟨i, hi⟩ | ⟨i, hi⟩ <;> fin_cases i <;> simp at hi
    · exact alg_of_mem x (Algebra.subset_adjoin (Or.inl (Subtype.ext hi.symm)))
    · exact alg_mul x ⟨L, hLm⟩ ⟨I, hIm⟩ hi.symm
        (alg_of_mem _ (Algebra.subset_adjoin (Or.inl rfl))) (alg_of_alg _ I_alg)
    · exact alg_mul x ⟨L, hLm⟩ ⟨I ^ I, hum⟩ hi.symm
        (alg_of_mem _ (Algebra.subset_adjoin (Or.inl rfl)))
        (alg_of_mem _ (Algebra.subset_adjoin (Or.inr rfl)))
    · exact alg_of_alg x (by rw [← hi, hexpL]; exact I_alg)
    · exact alg_of_mem x (Algebra.subset_adjoin
        (Or.inr (Subtype.ext (show (x : ℂ) = I ^ I by rw [← hi, hu]))))
    · exact alg_of_alg x (by rw [← hi, ← hw]; exact hwalg)
  have hc : #({⟨L, hLm⟩, ⟨I ^ I, hum⟩} : Set (adjoin ℚ S)) ≤ 2 :=
    mk_insert_le.trans (by rw [mk_singleton, one_add_one_eq_two])
  have := (h3.trans hle).trans hc
  norm_cast at this
