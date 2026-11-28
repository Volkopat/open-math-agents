import OMAStatements.S_mo_155384
namespace OMA.S_mo_155384
open Equiv Matrix

private lemma entry {k : ℕ} (z : Fin k → ℂ) (hz : Function.Injective z) (hu : ∀ i, ‖z i‖=1)
    (N : ℕ) (i j : Fin k) : gram z N i j = if i=j then (N:ℂ) else quotient z N i j := by
  have hzi : z i ≠ 0 := by intro h;simpa [h] using hu i
  have hs : gram z N i j = ∑ a ∈ Finset.range N, (z j / z i)^a := by
    rw [← Fin.sum_univ_eq_sum_range (fun a : ℕ => (z j / z i)^a)]
    rw [gram, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro a _
    change star ((z i)^a.val) * (z j)^a.val = _
    rw [star_pow, div_pow, div_eq_mul_inv, ← inv_pow, Complex.star_def, ← Complex.inv_eq_conj (hu i)]
    ring
  rw [hs]
  by_cases he : i=j
  · subst j;simp [hzi]
  · simpa [he,quotient] using geom_sum_eq (show z j / z i ≠ 1 by
      intro hc;exact he (hz ((div_eq_one_iff_eq hzi).mp hc)).symm) N

private lemma expansion {k : ℕ} (z : Fin k → ℂ) (hz : Function.Injective z) (hu : ∀ i, ‖z i‖=1)
    (N : ℕ) : (gram z N).det =
      ∑ σ : Perm (Fin k), Perm.sign σ •
        ((N:ℂ)^σ.supportᶜ.card * ∏ i ∈ σ.support, quotient z N (σ i) i) := by
  classical
  rw [Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  rw [← Finset.prod_mul_prod_compl σ.supportᶜ (fun i => gram z N (σ i) i), compl_compl]
  congr 1
  · rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro i hi
    have hfix : σ i=i := by simpa using hi
    simp [entry z hz hu, hfix]
  · apply Finset.prod_congr rfl
    intro i hi
    simp [entry z hz hu,Perm.mem_support.mp hi]

private lemma polynomial_classes {k : ℕ} (z : Fin k → ℂ) (hz : Function.Injective z)
    (hu : ∀ i, ‖z i‖=1) (L : ℕ) (hL : ∀ i, z i ^ L=1) (r : ℕ) :
    ∃ P : Polynomial ℂ, P.Monic ∧ P.natDegree=k ∧
      ∀ m : ℕ, (gram z (m*L+r)).det = P.eval ((m*L+r : ℕ) : ℂ) := by
  classical
  let A : Matrix (Fin k) (Fin k) ℂ := fun i j => if i=j then 0 else quotient z r i j
  refine ⟨(-A).charpoly, Matrix.charpoly_monic _, by simp, ?_⟩
  intro m
  rw [Matrix.eval_charpoly,sub_neg_eq_add]
  congr 1
  ext i j
  rw [entry z hz hu]
  change _ = Matrix.diagonal (fun _ => ((m*L+r : ℕ) : ℂ)) i j +
    (if i=j then 0 else quotient z r i j)
  by_cases hij : i=j
  · subst j;simp
  · have hpow : (z j/z i)^(m*L+r) = (z j/z i)^r := by
      simp [pow_add,mul_comm m L,pow_mul,div_pow,hL]
    simp [hij,quotient,hpow]

end OMA.S_mo_155384

theorem OMA.solution : type_of% @OMA.S_mo_155384.main := by
  intro k z hz hu
  exact ⟨OMA.S_mo_155384.expansion z hz hu,
    fun L _ hL r _ => OMA.S_mo_155384.polynomial_classes z hz hu L hL r⟩
