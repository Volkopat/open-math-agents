import OMAStatements.S_mo_393176

open MvPolynomial

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_393176.main) := by
  intro h
  have hhom : (∑ i : Fin 5, (X i : MvPolynomial (Fin 5) ℂ) ^ 2).IsHomogeneous 2 := by
    apply IsHomogeneous.sum
    intro i _
    exact (isHomogeneous_X ℂ i).pow 2
  obtain ⟨a, ha⟩ := h 5 2 (by norm_num) (by norm_num) _ hhom
  have hc : OMA.S_mo_393176.count 5 2 = 2 := by decide
  -- the linear map collecting all the linear forms
  let L : (Fin 5 → ℂ) →ₗ[ℂ] (Fin (OMA.S_mo_393176.count 5 2) × Fin 2 → ℂ) :=
    { toFun := fun v tj => ∑ i, a tj.1 tj.2 i * v i
      map_add' := by
        intro v w
        funext tj
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        funext tj
        simp [Finset.mul_sum, mul_left_comm] }
  have hdim : Module.finrank ℂ (Fin (OMA.S_mo_393176.count 5 2) × Fin 2 → ℂ)
      < Module.finrank ℂ (Fin 5 → ℂ) := by
    simp [hc]
  have hninj : ¬ Function.Injective L := by
    intro hi
    have := LinearMap.finrank_le_finrank_of_injective hi
    omega
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff] at hninj
  push Not at hninj
  obtain ⟨v, hLv, hv0⟩ := hninj
  rw [LinearMap.mem_ker] at hLv
  have hLv' : ∀ t j, ∑ i, a t j i * v i = 0 := fun t j => congrFun hLv (t, j)
  have hev : ∀ w : Fin 5 → ℂ, ∑ i, w i ^ 2 = ∑ t, ∏ j, ∑ i, a t j i * w i := by
    intro w
    have := congrArg (MvPolynomial.eval w) ha
    simpa [OMA.S_mo_393176.linear] using this
  have key : ∀ w : Fin 5 → ℂ, ∑ i, (v i + w i) ^ 2 = ∑ i, w i ^ 2 := by
    intro w
    rw [hev w, hev (fun i => v i + w i)]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.prod_congr rfl
    intro j _
    simp only [mul_add, Finset.sum_add_distrib, hLv' t j, zero_add]
  have h0 : ∑ i, v i ^ 2 = 0 := by
    have := key 0
    simpa using this
  apply hv0
  funext k
  have hk := key (Pi.single k 1)
  have e1 : ∑ i, (v i + (Pi.single k (1 : ℂ) : Fin 5 → ℂ) i) ^ 2
      = ∑ i, v i ^ 2 + 2 * v k + 1 := by
    simp only [Fin.sum_univ_five]
    fin_cases k <;> simp [Pi.single_apply] <;> ring
  have e2 : ∑ i, ((Pi.single k (1 : ℂ) : Fin 5 → ℂ) i) ^ 2 = 1 := by
    simp only [Fin.sum_univ_five]
    fin_cases k <;> simp [Pi.single_apply]
  rw [e1, e2, h0] at hk
  have : 2 * v k = 0 := by linear_combination hk
  simpa using this
