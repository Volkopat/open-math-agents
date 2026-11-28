import OMAReductions.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_real_orderedField_R1
import Mathlib

-- Step H4 of TarskiExponentialFunctionProblem.isDecidable_completeTheory_real_orderedField.R1.
-- Credit: @LordMike

open FirstOrder FirstOrder.Language Polynomial Filter Topology

/-- A monic polynomial of odd degree over the reals has a root (intermediate value theorem). -/
lemma oma_odd_root (P : ℝ[X]) (hm : P.Monic) (ho : Odd P.natDegree) :
    ∃ x : ℝ, P.eval x = 0 := by
  have hdeg : 0 < P.degree := by
    rw [← natDegree_pos_iff_degree_pos]
    exact ho.pos
  have hlc : P.leadingCoeff = 1 := hm
  have hup : Tendsto (fun x => P.eval x) atTop atTop :=
    tendsto_atTop_of_leadingCoeff_nonneg P hdeg (by rw [hlc]; norm_num)
  have hQdeg : 0 < (P.comp (-X)).degree := by
    rw [← natDegree_pos_iff_degree_pos, natDegree_comp, natDegree_neg, natDegree_X, mul_one]
    exact ho.pos
  have hQlc : (P.comp (-X)).leadingCoeff ≤ 0 := by
    rw [comp_neg_X_leadingCoeff_eq, hlc, ho.neg_one_pow]
    norm_num
  have hdown : Tendsto (fun x => (P.comp (-X)).eval x) atTop atBot :=
    tendsto_atBot_of_leadingCoeff_nonpos _ hQdeg hQlc
  obtain ⟨b, hb⟩ := (hup.eventually_gt_atTop 0).exists
  obtain ⟨c, hc⟩ := (hdown.eventually_lt_atBot 0).exists
  have hc' : P.eval (-c) < 0 := by
    simpa [eval_comp] using hc
  have h0 : (0 : ℝ) ∈ Set.Icc (P.eval (-c)) (P.eval b) := ⟨hc'.le, hb.le⟩
  obtain ⟨x, hx⟩ := intermediate_value_univ (-c) b P.continuous h0
  exact ⟨x, hx⟩

/-- Horner evaluation of the monic polynomial attached to a list of coefficients. -/
lemma oma_horner_monic (l : List ℝ) :
    (l.foldr (fun c t => C c + X * t) (1 : ℝ[X])).Monic ∧
      (l.foldr (fun c t => C c + X * t) (1 : ℝ[X])).natDegree = l.length := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.foldr_cons, List.length_cons]
    have hXP : (X * l.foldr (fun c t => C c + X * t) (1 : ℝ[X])).Monic :=
      monic_X.mul ih.1
    have hne : l.foldr (fun c t => C c + X * t) (1 : ℝ[X]) ≠ 0 := ih.1.ne_zero
    have hXPdeg : (X * l.foldr (fun c t => C c + X * t) (1 : ℝ[X])).natDegree = l.length + 1 := by
      rw [natDegree_X_mul hne, ih.2]
    have hlt : (C c).degree < (X * l.foldr (fun c t => C c + X * t) (1 : ℝ[X])).degree := by
      refine lt_of_le_of_lt degree_C_le ?_
      rw [degree_eq_natDegree hXP.ne_zero, hXPdeg]
      exact_mod_cast Nat.succ_pos _
    refine ⟨hXP.add_of_right hlt, ?_⟩
    rw [natDegree_add_eq_right_of_degree_lt hlt, hXPdeg]

lemma oma_horner_eval (l : List ℝ) (x : ℝ) :
    (l.foldr (fun c t => C c + X * t) (1 : ℝ[X])).eval x = l.foldr (fun c t => c + x * t) 1 := by
  induction l with
  | nil => simp
  | cons c l ih => simp [List.foldr_cons, ih]

lemma oma_realize_horner (m : ℕ) (v : Empty ⊕ Fin (m + 1) → ℝ) (l : List (Fin m)) :
    (l.foldr (fun (i : Fin m) (t : Language.ring.Term (Empty ⊕ Fin (m + 1))) => (Term.var (Sum.inr i.castSucc) : Language.ring.Term (Empty ⊕ Fin (m + 1))) +
      Term.var (Sum.inr (Fin.last m)) * t) 1).realize v =
      l.foldr (fun (i : Fin m) (t : ℝ) => v (Sum.inr i.castSucc) + v (Sum.inr (Fin.last m)) * t) 1 := by
  induction l with
  | nil => simp [FirstOrder.Ring.realize_one]
  | cons i l ih => simp [List.foldr_cons, FirstOrder.Ring.realize_add, FirstOrder.Ring.realize_mul, ih]

lemma oma_horner_root (k : ℕ) (a : Fin (2 * k + 1) → ℝ) :
    ∃ x : ℝ, (List.finRange (2 * k + 1)).foldr (fun i t => a i + x * t) 1 = 0 := by
  obtain ⟨hmon, hdeg⟩ := oma_horner_monic ((List.finRange (2 * k + 1)).map a)
  have hlen : ((List.finRange (2 * k + 1)).map a).length = 2 * k + 1 := by simp
  obtain ⟨x, hx⟩ := oma_odd_root _ hmon (by rw [hdeg, hlen]; exact odd_two_mul_add_one k)
  refine ⟨x, ?_⟩
  have h2 := oma_horner_eval ((List.finRange (2 * k + 1)).map a) x
  rw [hx, List.foldr_map] at h2
  exact h2.symm

theorem OMA.solution : OMA.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_real_orderedField_R1.H4 := by
  dsimp only [OMA.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_real_orderedField_R1.H4]
  rw [Theory.model_iff]
  have hO : (Language.ring.sum Language.order).OrderedStructure ℝ :=
    ⟨fun x => relMap_leSymb (L := Language.order) x⟩
  rintro φ (((hF | hL) | hC) | ⟨k, rfl⟩)
  · have : (ℝ : Type) ⊨ (LHom.sumInl : Language.ring →ᴸ Language.ring.sum Language.order).onTheory Theory.field :=
      (LHom.onTheory_model _ _).2 inferInstance
    exact Theory.realize_sentence_of_mem _ hF
  · have : (ℝ : Type) ⊨ (Language.ring.sum Language.order).linearOrderTheory := inferInstance
    exact Theory.realize_sentence_of_mem _ hL
  · rcases hC with rfl | rfl | rfl
    · simp [Sentence.Realize, Formula.Realize, LHom.realize_onTerm, FirstOrder.Ring.realize_add,
        FirstOrder.Ring.realize_mul, FirstOrder.Ring.realize_zero, FirstOrder.Ring.realize_one]
    · simp [Sentence.Realize, Formula.Realize, LHom.realize_onTerm, FirstOrder.Ring.realize_add,
        FirstOrder.Ring.realize_mul, FirstOrder.Ring.realize_zero, FirstOrder.Ring.realize_one]
      intro a b ha hb
      exact mul_nonneg ha hb
    · simp [Sentence.Realize, Formula.Realize, LHom.realize_onTerm, FirstOrder.Ring.realize_add,
        FirstOrder.Ring.realize_mul, FirstOrder.Ring.realize_zero, FirstOrder.Ring.realize_one]
      intro a ha
      exact ⟨√a, Real.mul_self_sqrt ha⟩
  · dsimp only [Sentence.Realize]
    rw [BoundedFormula.realize_alls]
    intro xs
    rw [BoundedFormula.realize_ex]
    obtain ⟨x, hx⟩ := oma_horner_root k xs
    refine ⟨x, ?_⟩
    simpa [BoundedFormula.realize_bdEqual, LHom.realize_onTerm, oma_realize_horner,
      FirstOrder.Ring.realize_zero, Fin.snoc_castSucc, Fin.snoc_last] using hx
