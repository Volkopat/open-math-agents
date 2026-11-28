import OMAStatements.S_mo_301954

-- Retains @Genbox's lexicographic-leading-index proof from PR #27797.
-- Uses the ordered additive structure on lexicographic finite function spaces.

open OMA.S_mo_301954

private def bump {n : ℕ} (i : Fin n) : Fin n → ℕ := fun j => if j = i then 1 else 0

private theorem bump_injective (n : ℕ) : Function.Injective (bump (n := n)) := by
  intro i j h
  by_contra hn
  have hh := congrFun h i
  simp [bump, hn] at hh

private theorem unique_largest {n m k : ℕ} (row : Fin (k+1) ↪ Fin n)
    (col : Fin (k+1) ↪ MultiIndex n (m+1)) :
    ∃ i₀ j₀, ∀ i j,
      raiseIndex (col j) (row i) = raiseIndex (col j₀) (row i₀) → i = i₀ ∧ j = j₀ := by
  obtain ⟨i₀, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => toLex (bump (row i))) Finset.univ_nonempty
  obtain ⟨j₀, _, hj⟩ := Finset.exists_max_image Finset.univ
    (fun j => toLex (col j).val) Finset.univ_nonempty
  refine ⟨i₀, j₀, fun i j he => ?_⟩
  have h₁ := hi i (Finset.mem_univ i)
  have h₂ := hj j (Finset.mem_univ j)
  have hadd : (col j).val + bump (row i) = (col j₀).val + bump (row i₀) :=
    congrArg Subtype.val he
  rcases lt_or_eq_of_le h₁ with hl | he₁
  · have hl' := add_lt_add_of_le_of_lt h₂ hl
    exact (ne_of_lt hl' (congrArg toLex hadd)).elim
  · have hh := congrArg ofLex he₁
    change bump (row i) = bump (row i₀) at hh
    have hi' := row.injective (bump_injective n hh)
    subst i
    exact ⟨rfl, col.injective (Subtype.ext (add_right_cancel hadd))⟩

private def evaluated {n m k : ℕ} (row : Fin k ↪ Fin n)
    (col : Fin k ↪ MultiIndex n (m+1)) (c : MultiIndex n (m+2) → ℤ) :
    Matrix (Fin k) (Fin k) ℤ :=
  fun i j => (((col j).val (row i) + 1 : ℕ) : ℤ) * c (raiseIndex (col j) (row i))

private theorem exists_nonzero_det {n m : ℕ} (k : ℕ) :
    ∀ (row : Fin k ↪ Fin n) (col : Fin k ↪ MultiIndex n (m+1)),
      ∃ c, (evaluated row col c).det ≠ 0 := by
  classical
  induction k with
  | zero =>
    intro row col
    exact ⟨0, by simp [Matrix.det_fin_zero]⟩
  | succ k ih =>
    intro row col
    obtain ⟨i₀,j₀,huniq⟩ := unique_largest row col
    let row' : Fin k ↪ Fin n := ⟨row ∘ i₀.succAbove, row.injective.comp i₀.succAbove_right_injective⟩
    let col' : Fin k ↪ MultiIndex n (m+1) :=
      ⟨col ∘ j₀.succAbove, col.injective.comp j₀.succAbove_right_injective⟩
    obtain ⟨c,hchild⟩ := ih row' col'
    let μ := raiseIndex (col j₀) (row i₀)
    let c' := Function.update c μ (c μ + 1)
    let A := evaluated row col c
    let B := evaluated row col c'
    have hkeep (i j : Fin (k+1)) (h : i ≠ i₀ ∨ j ≠ j₀) : B i j = A i j := by
      have hne : raiseIndex (col j) (row i) ≠ μ := fun he => by
        obtain ⟨hi,hj⟩ := huniq i j he
        exact h.elim (fun hn => hn hi) (fun hn => hn hj)
      change _ * c' _ = _ * c _
      simp only [c', Function.update_of_ne hne]
    have hsub (j : Fin (k+1)) :
        B.submatrix i₀.succAbove j.succAbove = A.submatrix i₀.succAbove j.succAbove := by
      ext i l
      exact hkeep _ _ (Or.inl (Fin.succAbove_ne _ _))
    have hentry : B i₀ j₀ - A i₀ j₀ = (((col j₀).val (row i₀) + 1 : ℕ) : ℤ) := by
      change _ * c' μ - _ * c μ = _
      simp only [c', Function.update_self]
      ring
    have hdiff : B.det - A.det =
        (-1 : ℤ) ^ (i₀.val + j₀.val) *
          (((col j₀).val (row i₀) + 1 : ℕ) : ℤ) * (evaluated row' col' c).det := by
      rw [Matrix.det_succ_row B i₀, Matrix.det_succ_row A i₀, ← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single j₀]
      · rw [hsub]
        change _ * B i₀ j₀ * (evaluated row' col' c).det -
          _ * A i₀ j₀ * (evaluated row' col' c).det = _
        rw [← hentry]
        ring
      · intro j _ hj
        rw [hsub, hkeep _ _ (Or.inr hj), sub_self]
      · simp
    by_cases hz : A.det = 0
    · refine ⟨c', ?_⟩
      change B.det ≠ 0
      rw [hz, sub_zero] at hdiff
      rw [hdiff]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)) hchild
    · exact ⟨c,hz⟩

theorem OMA.solution : type_of% @OMA.S_mo_301954.main := by
  intro m n _ col
  obtain ⟨c,hc⟩ := exists_nonzero_det n (Function.Embedding.refl (Fin n)) col
  have he : MvPolynomial.eval c (minor col).det ≠ 0 := by
    rw [RingHom.map_det]
    convert hc using 2
    ext i j
    simp [minor, evaluated]
  exact ⟨fun h => he (by rw [h, map_zero]), c, he⟩