import OMAStatements.S_mo_336709

namespace OMA.S_mo_336709
open Matrix Finset Unitary
private lemma pow_entry {n : ℕ} (A : Mat n) (U : unitary (Mat n)) (a : Fin n → ℝ)
    (h : specData A U a) (k : ℕ) (i j : Fin n) :
    (A^k) i j = ∑ p, (a p:ℂ)^k*(U:Mat n) i p*star ((U:Mat n) j p) := by
  let F := conjStarAlgAut ℂ _ U
  change A=F (diagonal fun p => (a p:ℂ)) at h
  rw [h,←map_pow,Matrix.diagonal_pow]
  change ((U:Mat n)*diagonal (fun p => (a p:ℂ)^k)*(U:Mat n)ᴴ) i j=_
  rw [Matrix.mul_apply]
  simp only [mul_diagonal,conjTranspose_apply]
  exact sum_congr rfl fun p _ => by ring
lemma expand_term {n : ℕ} (A B : Mat n) (U V : unitary (Mat n))
    (a b : Fin n → ℝ) (hA : specData A U a) (hB : specData B V b) (k : ℕ) :
    term A B k = ∑ p,∑ q, (((a p*b q:ℝ):ℂ)^k) • coeff U V p q := by
  ext i j
  simp only [term,hadamard_apply,pow_entry A U a hA,pow_entry B V b hB,
    Finset.sum_mul,Finset.mul_sum,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    coeff,vec,star_mul',Complex.ofReal_mul,mul_pow]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  ring
end OMA.S_mo_336709

namespace OMA.S_mo_336709
open Matrix Finset
lemma hasSum_closed {n : ℕ} (A B : Mat n) (U V : unitary (Mat n))
    (a b : Fin n → ℝ) (hA : specData A U a) (hB : specData B V b) (h : activeBound U V a b) :
    HasSum (term A B) (closedForm U V a b) := by
  classical
  have one (p q : Fin n) : HasSum (fun k : ℕ => (((a p*b q:ℝ):ℂ)^k) • coeff U V p q)
      ((1-(a p*b q:ℝ):ℂ)⁻¹ • coeff U V p q) := by
    by_cases hv : ∃ i,vec U V p q i≠0
    · have hn : ‖((a p*b q:ℝ):ℂ)‖<1 := by simpa using h p q hv
      exact (hasSum_geometric_of_norm_lt_one hn).smul_const _
    · push Not at hv
      have hz : coeff U V p q=0 := by ext i j; simp [coeff,hv]
      simp [hz]
  simp_rw [funext (expand_term A B U V a b hA hB)]
  exact hasSum_sum fun p _ => hasSum_sum fun q _ => one p q
end OMA.S_mo_336709

namespace OMA.S_mo_336709
open Matrix Filter Finset
open scoped Topology

lemma active_of_tendsto {n : ℕ} (A B : Mat n) (U V : unitary (Mat n)) (a b : Fin n → ℝ)
    (hA : specData A U a) (hB : specData B V b) (ht : Tendsto (term A B) atTop (𝓝 0)) :
    activeBound U V a b := by
  intro p q ha
  obtain ⟨i,hi⟩ := ha
  by_contra! hbad
  let f (k : ℕ) (p q : Fin n) := ((a p*b q)^2)^k * Complex.normSq (vec U V p q i)
  have he (k : ℕ) : (term A B (2*k) i i).re = ∑ p,∑ q,f k p q := by
    rw [expand_term A B U V a b hA hB]
    simp only [Matrix.sum_apply, Matrix.smul_apply,Complex.re_sum,smul_eq_mul,coeff]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    have hz (z : ℂ) : z * star z = (Complex.normSq z : ℂ) := Complex.mul_conj z
    rw [← Complex.ofReal_pow,hz]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,f,pow_mul]
  have hn (k p q) : 0≤f k p q := mul_nonneg (pow_nonneg (sq_nonneg _) _) (Complex.normSq_nonneg _)
  have hb (k) : Complex.normSq (vec U V p q i) ≤ (term A B (2*k) i i).re := by
    rw [he]
    have hsq : 1≤(a p*b q)^2 := by nlinarith [sq_abs (a p*b q),mul_nonneg (sub_nonneg.mpr hbad) (add_nonneg (abs_nonneg (a p*b q)) zero_le_one)]
    have hle : Complex.normSq (vec U V p q i)≤f k p q :=
      le_mul_of_one_le_left (Complex.normSq_nonneg _) (one_le_pow₀ hsq)
    exact hle.trans ((Finset.single_le_sum (s:=univ) (fun r _ => hn k p r) (mem_univ q)).trans
      (Finset.single_le_sum (s:=univ) (fun s _ => Finset.sum_nonneg (fun r _ => hn k s r)) (mem_univ p)))
  have htime : Tendsto (fun k : ℕ => 2*k) atTop atTop :=
    tendsto_atTop_mono (fun k => show k ≤ 2*k by omega) tendsto_id
  have hcont : Continuous (fun M : Mat n => (M i i).re) := by fun_prop
  have hlim : Tendsto (fun k => (term A B (2*k) i i).re) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (hcont.continuousAt (x:=(0:Mat n))).tendsto.comp (ht.comp htime)
  exact (Complex.normSq_pos.mpr hi).not_ge (le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hb)

end OMA.S_mo_336709

namespace OMA.S_mo_336709
open Matrix Filter Finset
open scoped Topology

private lemma hermitian_square {n : ℕ} (M : Mat n) (hm : M.IsHermitian) (i : Fin n) :
    (M*M) i i = ((∑ j,‖M i j‖^2 : ℝ):ℂ) := by
  rw [Matrix.mul_apply,Complex.ofReal_sum]
  apply sum_congr rfl
  intro j _
  rw [←hm.apply j i]
  rw [Complex.ofReal_pow]
  exact Complex.mul_conj' _

lemma inverse_even {n : ℕ} (A B : Mat n) (ha : A.IsHermitian) (hu : IsUnit A)
    (he : A⁻¹=Bᵀ) (t : ℕ) (i : Fin n) : 1 ≤ ((term A B (2*t)) i i).re := by
  let C := A^t
  let D := (A⁻¹)^t
  have hC : C.IsHermitian := ha.pow t
  have hD : D.IsHermitian := ha.inv.pow t
  have hu' := A.isUnit_iff_isUnit_det.mp hu
  have hcomm : Commute A A⁻¹ := by
    show A*A⁻¹=A⁻¹*A
    rw [mul_nonsing_inv _ hu',nonsing_inv_mul _ hu']
  have heq : C*D=1 := by
    rw [show C*D=A^t*(A⁻¹)^t from rfl,←hcomm.mul_pow,mul_nonsing_inv _ hu',one_pow]
  have hsum : (∑ j,C i j*D j i)=1 := by simp only [←Matrix.mul_apply,heq,Matrix.one_apply_eq]
  have ht : 1 ≤ ∑ j,‖C i j‖*‖D i j‖ := by
    have h := norm_sum_le (s:=univ) (f:=fun j => C i j*D j i)
    rw [hsum,norm_one] at h
    convert h using 1
    apply sum_congr rfl
    intro j _
    rw [norm_mul,←hD.apply j i,norm_star]
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun j => ‖C i j‖) (fun j => ‖D i j‖)
  have h1 : 1 ≤ (∑ j,‖C i j‖^2)*(∑ j,‖D i j‖^2) := by nlinarith only [hcs,ht,sq_nonneg ((∑ j,‖C i j‖*‖D i j‖)-1)]
  have hb : B^(2*t)=(D*D)ᵀ := by
    rw [show D*D=(A⁻¹)^(2*t) by rw [two_mul,pow_add],he,←Matrix.transpose_pow,Matrix.transpose_transpose]
  simpa only [term,Matrix.hadamard_apply,hb,Matrix.transpose_apply,
    show A^(2*t)=C*C by rw [two_mul,pow_add],hermitian_square C hC,hermitian_square D hD,
    ←Complex.ofReal_mul,Complex.ofReal_re] using h1

lemma inverse_diverges {n : ℕ} (hn : 0 < n) (A B : Mat n) (ha : A.IsHermitian)
    (hu : IsUnit A) (he : A⁻¹=Bᵀ) : ¬ Tendsto (term A B) atTop (𝓝 0) := by
  intro h
  let i : Fin n := ⟨0,hn⟩
  have heval : Continuous (fun M : Mat n => (M i i).re) := by fun_prop
  have hsub : Tendsto (fun t : ℕ => 2*t) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b,fun t ht => by omega⟩)
  have hlim : Tendsto (fun t : ℕ => ((term A B (2*t)) i i).re) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (heval.continuousAt.tendsto.comp (h.comp hsub))
  have hh := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Filter.Eventually.of_forall (fun t => inverse_even A B ha hu he t i))
  norm_num at hh
end OMA.S_mo_336709

open OMA.S_mo_336709
theorem OMA.solution : type_of% @OMA.S_mo_336709.main := by
  refine ⟨fun _ _ h => ⟨h.eigenvectorUnitary,h.eigenvalues,h.spectral_theorem⟩,?_,
    fun _ hn A B hA _ hu he => inverse_diverges hn A B hA hu he⟩
  intro n A B U V a b hA hB
  have hn := active_of_tendsto A B U V a b hA hB
  have hs := hasSum_closed A B U V a b hA hB
  exact ⟨expand_term A B U V a b hA hB,⟨hn,fun h => (hs h).summable.tendsto_atTop_zero⟩,
    ⟨fun h => hn h.tendsto_atTop_zero,fun h => (hs h).summable⟩,hs⟩
