import FormalConjectures.Wikipedia.RamanujanTau

-- Only the factor indexed by one contributes to the product's linear coefficient.
open PowerSeries PowerSeries.WithPiTopology

lemma OMA.linear_coeff_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℤ)
    (hf : ∀ i, constantCoeff (f i) = 1) :
    coeff 1 (∏ i ∈ s, f i) = ∑ i ∈ s, coeff 1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeff_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, coeff_mul, Finset.Nat.antidiagonal_succ]
    simp [coeff_zero_eq_constantCoeff_apply, hf, ih, add_comm]

theorem OMA.solution : type_of% @RamanujanTau.τ_two := by
  have factor (n : ℕ+) : coeff 1 ((1 - X ^ (n : ℕ)) ^ 24 : PowerSeries ℤ) =
      if n = 1 then -24 else 0 := by
    have h := OMA.linear_coeff_prod (Finset.range 24) (fun _ => (1 - X ^ (n : ℕ) : PowerSeries ℤ))
      (fun _ => by simp [n.ne_zero])
    by_cases hn : n = 1
    · subst n
      simpa [coeff_one, nsmul_eq_mul] using h
    · have hn' : 1 ≠ (n : ℕ) := fun e => hn (PNat.coe_eq_one_iff.mp e.symm)
      simpa [hn, hn', coeff_one, coeff_X_pow, nsmul_eq_mul] using h
  obtain ⟨s, hs⟩ := by
    simpa using ((continuous_coeff ℤ 1).tendsto _).comp RamanujanTau.multipliable.hasProd
  unfold RamanujanTau.τ RamanujanTau.Δ
  rw [show (2 : ℕ) = 1 + 1 from rfl, coeff_succ_X_mul, ← hs (insert 1 s) (Finset.subset_insert _ _)]
  rw [OMA.linear_coeff_prod _ _ (fun n => by simp [n.ne_zero])]
  simp [factor]
