import OMAStatements.S_oeis_a227433

-- Problem: A227433, the number of non-commuting pairs of 2x2 matrices over F_p is p^3 (p^3-1)(p^2-1).
-- The centralizer of a scalar matrix is everything (p^4 elements); the centralizer of a non-scalar A is
-- {l I + m A} (solving AB = BA entrywise), and (l, m) -> l I + m A is injective, so it has p^2 elements.
-- There are p scalar matrices, so the commuting pairs number p * p^4 + (p^4 - p) p^2, and the rest of the
-- p^8 pairs number p^3 (p^3 - 1)(p^2 - 1).

namespace OMA.A227433

variable {K : Type} [Field K]

def IsScal (A : Matrix (Fin 2) (Fin 2) K) : Prop := A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 0 0 = A 1 1

lemma scal_eq (A : Matrix (Fin 2) (Fin 2) K) (h : IsScal A) : A = A 0 0 • (1 : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨h1, h2, h3⟩ := h
  ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]

lemma comm_entries {A B : Matrix (Fin 2) (Fin 2) K} (h : A * B = B * A) :
    A 0 1 * B 1 0 = B 0 1 * A 1 0 ∧
    A 0 0 * B 0 1 + A 0 1 * B 1 1 = B 0 0 * A 0 1 + B 0 1 * A 1 1 ∧
    A 1 0 * B 0 0 + A 1 1 * B 1 0 = B 1 0 * A 0 0 + B 1 1 * A 1 0 := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  refine ⟨by linear_combination h00, by linear_combination h01, by linear_combination h10⟩

lemma centralizer_surj (A B : Matrix (Fin 2) (Fin 2) K) (hA : ¬ IsScal A) (h : A * B = B * A) :
    ∃ l m : K, l • (1 : Matrix (Fin 2) (Fin 2) K) + m • A = B := by
  obtain ⟨e1, e2, e3⟩ := comm_entries h
  by_cases hb : A 0 1 = 0
  · by_cases hc : A 1 0 = 0
    · have had : A 0 0 - A 1 1 ≠ 0 := fun h' => hA ⟨hb, hc, by linear_combination h'⟩
      refine ⟨B 0 0 - (B 1 1 - B 0 0) / (A 1 1 - A 0 0) * A 0 0, (B 1 1 - B 0 0) / (A 1 1 - A 0 0), ?_⟩
      have had' : A 1 1 - A 0 0 ≠ 0 := fun h' => had (by linear_combination -h')
      have hf : B 0 1 = 0 := by
        rw [hb] at e2; have : B 0 1 * (A 0 0 - A 1 1) = 0 := by linear_combination e2
        exact (mul_eq_zero.mp this).resolve_right had
      have hg : B 1 0 = 0 := by
        rw [hc] at e3; have : B 1 0 * (A 1 1 - A 0 0) = 0 := by linear_combination e3
        exact (mul_eq_zero.mp this).resolve_right had'
      ext i j; fin_cases i <;> fin_cases j <;> simp [hb, hc, hf, hg] <;> field_simp
      all_goals first | ring1 | linear_combination e1 | linear_combination -e1 | linear_combination e2 | linear_combination -e2 | linear_combination e3 | linear_combination -e3 | linear_combination e1 - e2 | linear_combination e2 - e1 | linear_combination e1 + e2 | linear_combination -e1 - e2 | linear_combination e1 - e3 | linear_combination e3 - e1
    · refine ⟨B 0 0 - B 1 0 / A 1 0 * A 0 0, B 1 0 / A 1 0, ?_⟩
      have hf : B 0 1 = 0 := by
        rw [hb] at e1; have : B 0 1 * A 1 0 = 0 := by linear_combination -e1
        exact (mul_eq_zero.mp this).resolve_right hc
      ext i j; fin_cases i <;> fin_cases j <;> simp [hb, hf] <;> field_simp
      all_goals first | ring1 | linear_combination e1 | linear_combination -e1 | linear_combination e2 | linear_combination -e2 | linear_combination e3 | linear_combination -e3 | linear_combination e1 - e2 | linear_combination e2 - e1 | linear_combination e1 + e2 | linear_combination -e1 - e2 | linear_combination e1 - e3 | linear_combination e3 - e1
  · refine ⟨B 0 0 - B 0 1 / A 0 1 * A 0 0, B 0 1 / A 0 1, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp
    all_goals first | ring1 | linear_combination e1 | linear_combination -e1 | linear_combination e2 | linear_combination -e2 | linear_combination e3 | linear_combination -e3 | linear_combination e1 - e2 | linear_combination e2 - e1 | linear_combination e1 + e2 | linear_combination -e1 - e2 | linear_combination e1 - e3 | linear_combination e3 - e1

lemma centralizer_inj (A : Matrix (Fin 2) (Fin 2) K) (hA : ¬ IsScal A) (l m l' m' : K)
    (h : l • (1 : Matrix (Fin 2) (Fin 2) K) + m • A = l' • 1 + m' • A) : l = l' ∧ m = m' := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
    mul_zero, mul_one, zero_add] at h00 h01 h10 h11
  by_cases hm : m = m'
  · subst hm; exact ⟨by linear_combination h00, rfl⟩
  · exfalso; apply hA
    have hmm : m - m' ≠ 0 := sub_ne_zero.mpr hm
    refine ⟨?_, ?_, ?_⟩
    · have : (m - m') * A 0 1 = 0 := by linear_combination h01
      exact (mul_eq_zero.mp this).resolve_left hmm
    · have : (m - m') * A 1 0 = 0 := by linear_combination h10
      exact (mul_eq_zero.mp this).resolve_left hmm
    · have : (m - m') * (A 0 0 - A 1 1) = 0 := by linear_combination h00 - h11
      have := (mul_eq_zero.mp this).resolve_left hmm
      linear_combination this

instance (A : Matrix (Fin 2) (Fin 2) K) [DecidableEq K] : Decidable (IsScal A) := by
  unfold IsScal; infer_instance

variable [Fintype K] [DecidableEq K]

lemma card_mat : Fintype.card (Matrix (Fin 2) (Fin 2) K) = Fintype.card K ^ 4 := by
  have : Fintype.card (Fin 2 → Fin 2 → K) = Fintype.card K ^ 4 := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]; ring
  convert this

lemma card_centralizer (A : Matrix (Fin 2) (Fin 2) K) :
    (Finset.univ.filter (fun B : Matrix (Fin 2) (Fin 2) K => A * B = B * A)).card
      = if IsScal A then Fintype.card K ^ 4 else Fintype.card K ^ 2 := by
  split_ifs with hA
  · rw [Finset.filter_true_of_mem, Finset.card_univ, card_mat]
    intro B _
    rw [scal_eq A hA, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  · rw [← Fintype.card_subtype, sq, ← Fintype.card_prod K K]
    symm
    refine Fintype.card_congr (Equiv.ofBijective
      (fun lm : K × K => ⟨lm.1 • (1 : Matrix (Fin 2) (Fin 2) K) + lm.2 • A,
        (((Commute.one_left A).smul_left lm.1).add_left ((Commute.refl A).smul_left lm.2)).symm.eq⟩)
      ⟨fun lm lm' h => ?_, fun B => ?_⟩)
    · have h' := congrArg Subtype.val h
      obtain ⟨h1, h2⟩ := centralizer_inj A hA _ _ _ _ h'
      exact Prod.ext h1 h2
    · obtain ⟨l, m, hlm⟩ := centralizer_surj A B.1 hA B.2
      exact ⟨(l, m), Subtype.ext hlm⟩

lemma card_scal : (Finset.univ.filter (fun A : Matrix (Fin 2) (Fin 2) K => IsScal A)).card
    = Fintype.card K := by
  have : Finset.univ.filter (fun A : Matrix (Fin 2) (Fin 2) K => IsScal A)
      = Finset.univ.image (fun a : K => a • (1 : Matrix (Fin 2) (Fin 2) K)) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h; exact ⟨A 0 0, (scal_eq A h).symm⟩
    · rintro ⟨a, rfl⟩; refine ⟨?_, ?_, ?_⟩ <;> simp
  rw [this, Finset.card_image_of_injective, Finset.card_univ]
  intro a b h
  have := congrFun (congrFun h 0) 0
  simpa using this

end OMA.A227433

theorem OMA.solution : type_of% @OMA.S_oeis_a227433.main := by
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  set Mat := Matrix (Fin 2) (Fin 2) (ZMod p)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Mat × Mat)))
    (fun P : Mat × Mat => P.1 * P.2 = P.2 * P.1)
  rw [Finset.card_univ, Fintype.card_prod, OMA.A227433.card_mat, ZMod.card] at htot
  have hC : (Finset.univ.filter (fun P : Mat × Mat => P.1 * P.2 = P.2 * P.1)).card
      = p * p ^ 4 + (p ^ 4 - p) * p ^ 2 := by
    rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
    rw [Finset.sum_congr rfl (fun A _ =>
      (Finset.card_filter (fun B : Mat => A * B = B * A) _).symm.trans (OMA.A227433.card_centralizer A))]
    simp only [ZMod.card]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
      OMA.A227433.card_scal, ZMod.card]
    have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Mat))
      (fun A : Mat => OMA.A227433.IsScal A)
    rw [Finset.card_univ, OMA.A227433.card_mat, ZMod.card, OMA.A227433.card_scal, ZMod.card] at hsplit
    have : (Finset.univ.filter (fun A : Mat => ¬ OMA.A227433.IsScal A)).card = p ^ 4 - p := by omega
    rw [this]
  have hp1 : 1 ≤ p := hp.one_lt.le
  have h4 : p ≤ p ^ 4 := Nat.le_self_pow (by norm_num) p
  have h3 : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ hp1
  have h2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp1
  have key : p ^ 3 * (p ^ 3 - 1) * (p ^ 2 - 1) + (p * p ^ 4 + (p ^ 4 - p) * p ^ 2) = p ^ 4 * p ^ 4 := by
    zify [h4, h3, h2]; ring
  rw [hC] at htot
  show (Finset.univ.filter (fun P : Mat × Mat => ¬ (P.1 * P.2 = P.2 * P.1))).card = _
  omega
