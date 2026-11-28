import OMAStatements.S_mo_363983

namespace OMA.S_mo_363983
open Matrix Finset
open scoped MatrixOrder Matrix.Norms.L2Operator
private noncomputable def low {n : ℕ} (M : Mat n) := sInf (spectrum ℝ M)
private noncomputable def high {n : ℕ} (M : Mat n) := sSup (spectrum ℝ M)
private lemma shifted_nonneg {n : ℕ} (A : Mat n) (ha : A.IsHermitian) (t : ℝ)
    (hb : ∀ z ∈ spectrum ℝ A, t ≤ z) : (A-t • (1:Mat n)).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply (StarOrderedRing.nonneg_iff_spectrum_nonneg (R:=ℝ) _ (ha.sub (Matrix.isHermitian_one.smul (IsSelfAdjoint.all t)))).mpr
  intro z hz
  have he : z+t ∈ spectrum ℝ A := by
    rw [spectrum.mem_iff,Algebra.algebraMap_eq_smul_one,add_smul]
    rwa [spectrum.mem_iff,Algebra.algebraMap_eq_smul_one,sub_sub_eq_add_sub] at hz
  linarith [hb _ he]

private lemma spectral_vec {n : ℕ} {A : Mat n} {z : ℝ} (hz : z∈spectrum ℝ A) :
    ∃ v : (Fin n → ℝ), v≠0 ∧ A *ᵥ v=z • v := by
  rw [←Matrix.spectrum_toLin'] at hz
  obtain ⟨v,hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz).exists_hasEigenvector
  exact ⟨v,hv.2,Module.End.mem_eigenspace_iff.mp hv.1⟩

private lemma spectral_of_vec {n : ℕ} (A : Mat n) (v : (Fin n → ℝ)) (hv : v≠0) (z : ℝ) (hz : A*ᵥv=z•v) :
    z∈spectrum ℝ A := by
  rw [←Matrix.spectrum_toLin',←Module.End.hasEigenvalue_iff_mem_spectrum]
  exact Module.End.hasEigenvalue_of_hasEigenvector (show Module.End.HasEigenvector A.toLin' z v from
    ⟨Module.End.mem_eigenspace_iff.mpr hz,hv⟩)



private lemma extreme_bounds {n : ℕ} [Nonempty (Fin n)] (M : Mat n) (hm : M.IsHermitian) :
    IsLeast (spectrum ℝ M) (low M) ∧ IsGreatest (spectrum ℝ M) (high M) := by
  let s := univ.image hm.eigenvalues
  have he : (s : Set ℝ)=spectrum ℝ M := by simp [s,hm.spectrum_real_eq_range_eigenvalues]
  have hne : s.Nonempty := univ_nonempty.image _
  have hl : IsLeast (spectrum ℝ M) (s.min' hne) := he ▸ Finset.isLeast_min' s hne
  have hu : IsGreatest (spectrum ℝ M) (s.max' hne) := he ▸ Finset.isGreatest_max' s hne
  simpa only [low,high,hl.csInf_eq,hu.csSup_eq] using And.intro hl hu

private lemma floor_psd {n : ℕ} [Nonempty (Fin n)] {M : Mat n} (hm : M.IsHermitian) :
    (M - low M • (1:Mat n)).PosSemidef :=
  shifted_nonneg M hm _ (extreme_bounds M hm).1.2

private lemma ceil_psd {n : ℕ} [Nonempty (Fin n)] {M : Mat n} (hm : M.IsHermitian) :
    (high M • (1:Mat n) - M).PosSemidef := by
  have h : ∀ z ∈ spectrum ℝ (-M), -high M ≤ z := by
    intro z hz
    obtain ⟨v,hv,he⟩ := spectral_vec hz
    rw [neg_mulVec] at he
    have he' : M*ᵥv=(-z) • v := by rw [neg_smul,←he,neg_neg]
    linarith [(extreme_bounds M hm).2.2 (spectral_of_vec _ _ hv _ he')]
  simpa only [neg_smul,sub_neg_eq_add,sub_eq_add_neg,neg_neg,add_comm] using shifted_nonneg (-M) hm.neg _ h

private lemma lower_of_psd {n : ℕ} [Nonempty (Fin n)] {M : Mat n} (hm : M.IsHermitian)
    {t : ℝ} (h : (M-t • (1:Mat n)).PosSemidef) : t ≤ low M := by
  obtain ⟨v,hv,ev⟩ := spectral_vec (extreme_bounds M hm).1.1
  have hh := h.dotProduct_mulVec_nonneg v
  have hn : 0 < v ⬝ᵥ v := by simpa using (Matrix.PosDef.one (n:=Fin n) (R:=ℝ)).dotProduct_mulVec_pos hv
  simp only [star_trivial,sub_mulVec,ev,smul_mulVec,one_mulVec,dotProduct_sub,dotProduct_smul,smul_eq_mul] at hh
  exact (mul_le_mul_iff_of_pos_right hn).mp (sub_nonneg.mp hh)

end OMA.S_mo_363983

namespace OMA.S_mo_363983
private def spaced {n : ℕ} (ε : ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ i j, i ≤ j → ((j.val-i.val : ℕ) : ℝ)*ε ≤ x j - x i

private lemma separate_iff {n : ℕ} (ε : ℝ) (hε : 0 ≤ ε) (x : Fin (n+1) → ℝ) :
    spaced ε x ↔ separated ε x := by
  constructor
  · intro hx i j hij
    have hd : (1:ℝ) ≤ ((j.val-i.val : ℕ):ℝ) := by exact_mod_cast (by omega : 1 ≤ j.val-i.val)
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right hd hε).trans (hx i j hij.le)
  · intro hx i j
    induction j using Fin.induction with
    | zero =>
      intro hi
      have he : i=0 := le_antisymm hi (Fin.zero_le i)
      simp [he]
    | succ j ih =>
      intro hij
      rcases eq_or_lt_of_le hij with e | h
      · simp [e]
      · have hle : i ≤ j.castSucc := by
          change i.val ≤ j.val
          change i.val < j.val+1 at h
          omega
        have hp := ih hle
        have hs := hx j.castSucc j.succ Fin.castSucc_lt_succ
        have he : j.succ.val-i.val = (j.castSucc.val-i.val)+1 := by
          change i.val ≤ j.val at hle
          change j.val+1-i.val=j.val-i.val+1
          omega
        rw [he,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
        linarith
end OMA.S_mo_363983

namespace OMA.S_mo_363983
open Matrix Finset
private lemma sum_into {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ)
    (e : ι → κ) (F : κ → ℝ) (hi : Set.InjOn e s) (ht : ∀ i ∈ s, e i ∈ t)
    (hp : ∀ j ∈ t, 0 ≤ F j) : ∑ i ∈ s, F (e i) ≤ ∑ j ∈ t, F j := by
  rw [← Finset.sum_image hi]
  exact Finset.sum_le_sum_of_subset_of_nonneg (by intro j hj; obtain ⟨i,hi,rfl⟩ := mem_image.mp hj; exact ht i hi) (fun j hj _ => hp j hj)

private lemma row_upper {n : ℕ} (g : ℝ → ℝ) (ε : ℝ) (x : Fin n → ℝ)
    (hg : ∀ t ≥ 0, 0 ≤ g t) (hm : AntitoneOn g (Set.Ici 0)) (hε : 0 < ε)
    (hx : spaced ε x) (i : Fin n) :
    ∑ j, gram g x i j ≤ 2 * ∑ k ∈ range n, g ((k:ℝ)*ε) := by
  classical
  let F := fun k : ℕ => g ((k:ℝ)*ε)
  have hF (k : ℕ) : 0 ≤ F k := hg _ (by positivity)
  let L := univ.filter (fun j : Fin n => j ≤ i)
  let R := univ.filter (fun j : Fin n => ¬ j ≤ i)
  have left : ∑ j ∈ L, gram g x i j ≤ ∑ k ∈ range n, F k := by
    refine (sum_le_sum (g := fun j : Fin n => F (i.val-j.val)) ?_).trans ?_
    · intro j hj
      have hji : j ≤ i := (mem_filter.mp hj).2
      exact hm (by positivity : 0 ≤ ((i.val-j.val:ℕ):ℝ)*ε) (show |x i-x j| ∈ Set.Ici 0 from abs_nonneg (x i-x j))
        ((hx j i hji).trans (le_abs_self _))
    · apply sum_into L (range n) (fun j => i.val-j.val) F
      · intro j hj k hk h
        have hj' := (mem_filter.mp hj).2
        have hk' := (mem_filter.mp hk).2
        apply Fin.ext
        change j.val ≤ i.val at hj'
        change k.val ≤ i.val at hk'
        dsimp at h
        omega
      · intro j hj
        exact mem_range.mpr (lt_of_le_of_lt (Nat.sub_le _ _) i.isLt)
      · exact fun k _ => hF k
  have right : ∑ j ∈ R, gram g x i j ≤ ∑ k ∈ range n, F k := by
    refine (sum_le_sum (g := fun j : Fin n => F (j.val-i.val)) ?_).trans ?_
    · intro j hj
      have hij : i ≤ j := le_of_lt (lt_of_not_ge (mem_filter.mp hj).2)
      apply hm (by positivity : 0 ≤ ((j.val-i.val:ℕ):ℝ)*ε) (show |x i-x j| ∈ Set.Ici 0 from abs_nonneg (x i-x j))
      exact (hx i j hij).trans (by rw [abs_sub_comm]; exact le_abs_self _)
    · apply sum_into R (range n) (fun j => j.val-i.val) F
      · intro j hj k hk h
        have hj' := (mem_filter.mp hj).2
        have hk' := (mem_filter.mp hk).2
        apply Fin.ext
        change ¬ j.val ≤ i.val at hj'
        change ¬ k.val ≤ i.val at hk'
        dsimp at h
        omega
      · intro j hj
        exact mem_range.mpr (lt_of_le_of_lt (Nat.sub_le _ _) j.isLt)
      · exact fun k _ => hF k
  have hadd := sum_filter_add_sum_filter_not (s:=univ) (fun j : Fin n => j ≤ i) (fun j => gram g x i j)
  change ∑ j ∈ L, gram g x i j + ∑ j ∈ R, gram g x i j = _ at hadd
  change _ ≤ 2 * ∑ k ∈ range n, F k
  linarith

private lemma grid_separated {n : ℕ} (ε : ℝ) : spaced ε (fun i : Fin n => (i.val:ℝ)*ε) := by
  intro i j hij
  rw [Nat.cast_sub hij]
  ring_nf
  rfl

private lemma grid_lower {n : ℕ} (N : ℕ) (hn : 2*N<n) (g : ℝ → ℝ) (ε : ℝ)
    (hg : ∀ t ≥ 0, 0 ≤ g t) (hε : 0 < ε) (i : Fin n) :
    ∑ k ∈ range (N+1), g ((k:ℝ)*ε) ≤
      ∑ j, gram g (fun j : Fin n => (j.val:ℝ)*ε) i j := by
  classical
  let e (k : Fin (N+1)) : Fin n :=
    if hi : i.val ≤ N then ⟨i.val+k.val,by omega⟩ else ⟨i.val-k.val,by omega⟩
  have he : Function.Injective e := by
    intro j k h
    have hh := congrArg Fin.val h
    apply Fin.ext
    by_cases hi : i.val ≤ N <;> simp [e,hi] at hh <;> omega
  let F := fun j : Fin n => gram g (fun j : Fin n => (j.val:ℝ)*ε) i j
  have hF (k : Fin (N+1)) : F (e k) = g ((k.val:ℝ)*ε) := by
    change g |(i.val:ℝ)*ε-((e k).val:ℝ)*ε| = _
    by_cases h : i.val ≤ N
    · simp only [e,dif_pos h,Nat.cast_add]
      rw [show (i.val:ℝ)*ε - ((i.val:ℝ)+k.val)*ε = -((k.val:ℝ)*ε) by ring,
        abs_neg,abs_of_nonneg (by positivity)]
    · have hk : k.val ≤ i.val := by omega
      simp only [e,dif_neg h,Nat.cast_sub hk]
      rw [show (i.val:ℝ)*ε - ((i.val:ℝ)-k.val)*ε = (k.val:ℝ)*ε by ring,
        abs_of_nonneg (by positivity)]
  rw [← Fin.sum_univ_eq_sum_range]
  simpa only [hF] using sum_into univ univ e F he.injOn (by simp) (fun j _ => hg _ (abs_nonneg _))
end OMA.S_mo_363983

namespace OMA.S_mo_363983
open Matrix Finset

private lemma ridge_herm {n : ℕ} (g : ℝ → ℝ) (hp : positiveKernel g) (α : ℝ) (x : Fin n → ℝ) :
    (ridge g α x).IsHermitian := (hp n x).1.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all α))

private lemma ridge_floor {n : ℕ} [Nonempty (Fin n)] (g : ℝ → ℝ) (hp : positiveKernel g)
    (α : ℝ) (x : Fin n → ℝ) : α ≤ low (ridge g α x) ∧ low (ridge g α x) ≤ α+g 0 := by
  have hh := ridge_herm g hp α x
  constructor
  · apply lower_of_psd hh
    simpa only [ridge,add_sub_cancel_right] using hp n x
  · have hd := (floor_psd hh).diag_nonneg (i:=Classical.arbitrary (Fin n))
    simpa [ridge,gram,sub_nonneg,add_comm] using hd

private lemma ridge_rows {n : ℕ} (g : ℝ → ℝ) (α : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    ∑ j, ridge g α x i j = α + ∑ j, gram g x i j := by
  simp [ridge,Finset.sum_add_distrib,Matrix.one_apply,add_comm]

private lemma ridge_max_upper {n : ℕ} [Nonempty (Fin n)] (g : ℝ → ℝ) (hp : positiveKernel g)
    (hg : ∀ t ≥ 0, 0 ≤ g t) (α : ℝ) (hα : 0 ≤ α) (x : Fin n → ℝ) (C : ℝ)
    (hx : ∀ i, (∑ j, gram g x i j) ≤ C) : high (ridge g α x) ≤ α+C := by
  let A := ridge g α x
  have hv := (extreme_bounds A (ridge_herm g hp α x)).2.1
  rw [←Matrix.spectrum_toLin',←Module.End.hasEigenvalue_iff_mem_spectrum] at hv
  obtain ⟨i,hi⟩ := eigenvalue_mem_ball hv
  rw [Metric.mem_closedBall,Real.dist_eq] at hi
  have hnil (j : Fin n) : 0 ≤ A i j := by
    dsimp [A,ridge,gram,Matrix.of]
    exact add_nonneg (hg _ (abs_nonneg _)) (mul_nonneg hα (by simp [Matrix.one_apply]; split <;> norm_num))
  simp_rw [Real.norm_eq_abs,abs_of_nonneg (hnil _)] at hi
  have hsum := sum_erase_add univ (A i) (mem_univ i)
  have htotal : ∑ j, A i j ≤ α+C := (ridge_rows g α x i).trans_le (by linarith [hx i])
  change high A ≤ α+C
  linarith [le_abs_self (high A-A i i)]

private lemma ridge_max_lower {n : ℕ} [Nonempty (Fin n)] (g : ℝ → ℝ) (hp : positiveKernel g)
    (α : ℝ) (x : Fin n → ℝ) (C : ℝ) (hx : ∀ i, C ≤ ∑ j, gram g x i j) :
    α+C ≤ high (ridge g α x) := by
  let A := ridge g α x
  have hh := (ceil_psd (ridge_herm g hp α x)).dotProduct_mulVec_nonneg (fun _ => (1:ℝ))
  have hh' : 0 ≤ ∑ i : Fin n, (high A - ∑ j : Fin n, A i j) := by
    change 0 ≤ (star (fun _ : Fin n => (1:ℝ))) ⬝ᵥ ((high A • 1 - A) *ᵥ (fun _ => 1)) at hh
    rw [sub_mulVec,smul_mulVec,one_mulVec] at hh
    simpa only [star_trivial,dotProduct,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,mul_one,one_mul,mulVec] using hh
  have hsum := sum_le_sum (s:=univ) (f:=fun _ : Fin n => α+C)
    (g:=fun i => ∑ j, A i j) (fun i _ => (add_le_add_right (hx i) α).trans_eq (by rw [ridge_rows]))
  rw [sum_sub_distrib] at hh'
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hh' hsum
  have hn : 0 < (n:ℝ) := by exact_mod_cast (Fin.pos_iff_nonempty.mpr inferInstance : 0<n)
  exact (mul_le_mul_iff_right₀ hn).mp (by linarith)

private lemma constant_pos : positiveKernel (fun _ => 1) := by
  intro n x
  convert Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin n => (1:ℝ)) using 1
  ext i j
  simp [gram,Matrix.vecMulVec]
end OMA.S_mo_363983

namespace OMA.S_mo_363983
open Matrix Finset
private lemma constant_exact (n : ℕ) (x : Fin (n+2) → ℝ) (α : ℝ) (hα : 0<α) :
    condition (ridge (fun _ => 1) α x) = (α+(n+2))/α := by
  let A := ridge (fun _ => 1) α x
  have hrows (i : Fin (n+2)) : ∑ j, gram (fun _ => 1) x i j = (n:ℝ)+2 := by simp [gram]
  have hu : high A = α+(n+2) := le_antisymm
    (ridge_max_upper _ constant_pos (by simp) α hα.le x _ (fun i => (hrows i).le))
    (ridge_max_lower _ constant_pos α x _ (fun i => (hrows i).ge))
  let v : Fin (n+2) → ℝ := Pi.single 0 1 - Pi.single 1 1
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp [v] at h0
  have hA : A *ᵥ v = α • v := by
    change (gram (fun _ => 1) x + α • 1) *ᵥ v = _
    rw [add_mulVec,smul_mulVec,one_mulVec,add_eq_right]
    ext i
    simp [v,mulVec_sub,gram]
  have hl : low A = α := le_antisymm
    ((extreme_bounds A (ridge_herm _ constant_pos α x)).1.2 (spectral_of_vec A v hv α hA))
    (ridge_floor _ constant_pos α x).1
  change high A/low A=_
  rw [hu,hl]
end OMA.S_mo_363983

namespace OMA.S_mo_363983
open Matrix Finset
private lemma iff_sum (g : ℝ → ℝ) (α ε : ℝ) (hp : positiveKernel g) (hg : ∀ t ≥ 0, 0 ≤ g t)
    (hm : AntitoneOn g (Set.Ici 0)) (hα : 0 < α) (hε : 0 < ε) :
    boundedCondition g α ε ↔ Summable (fun j : ℕ => g ((j:ℝ)*ε)) := by
  constructor
  · rintro ⟨K,hK⟩
    let C := max K 0
    have hC : 0 ≤ C := le_max_right _ _
    apply summable_of_sum_range_le (c:=C*(α+g 0)) (fun j => hg _ (by positivity))
    intro N
    let x := fun j : Fin (2*N+1) => (j.val:ℝ)*ε
    have hl := ridge_floor g hp α x
    have hx := hK (2*N) x ((separate_iff ε hε.le x).mp (grid_separated ε))
    change high (ridge g α x) / low (ridge g α x) ≤ K at hx
    have hb := (div_le_iff₀ (hα.trans_le hl.1)).mp (hx.trans (le_max_left K 0))
    have hL := ridge_max_lower g hp α x _ (grid_lower N (by omega) g ε hg hε)
    have hs : ∑ k ∈ range N, g ((k:ℝ)*ε) ≤ ∑ k ∈ range (N+1), g ((k:ℝ)*ε) := by
      rw [sum_range_succ]; exact le_add_of_nonneg_right (hg _ (by positivity))
    exact hs.trans ((by linarith : (∑ k ∈ range (N+1), g ((k:ℝ)*ε)) ≤ C*low (ridge g α x)).trans
      (mul_le_mul_of_nonneg_left hl.2 hC))
  · intro hs
    let S := ∑' j : ℕ, g ((j:ℝ)*ε)
    have hS : 0 ≤ S := tsum_nonneg (fun j => hg _ (by positivity))
    refine ⟨(α+2*S)/α,?_⟩
    intro n x hx
    have hl := ridge_floor g hp α x
    have hu := ridge_max_upper g hp hg α hα.le x (2*S) (fun i =>
      (row_upper g ε x hg hm hε ((separate_iff ε hε.le x).mpr hx) i).trans (by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact hs.sum_le_tsum _ (fun j _ => hg _ (by positivity))))
    apply (div_le_iff₀ (hα.trans_le hl.1)).mpr
    calc
      high (ridge g α x) ≤ α+2*S := hu
      _ = ((α+2*S)/α)*α := (div_mul_cancel₀ _ hα.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hl.1 (by positivity)

private lemma grid_unbounded (α ε : ℝ) (hα : 0 < α) (_hε : 0 < ε) (K : ℝ) :
    ∃ n : ℕ, K < condition (ridge (fun _ => 1) α (fun i : Fin (n+2) => (i.val:ℝ)*ε)) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (K*α)
  refine ⟨n,?_⟩
  rw [constant_exact n _ α hα]
  exact (lt_div_iff₀ hα).mpr (by linarith)

lemma solve :
    (positiveKernel (fun _ => 1) ∧
      (∀ (n : ℕ) (x : Fin (n+2) → ℝ) (α : ℝ), 0 < α →
        condition (ridge (fun _ => 1) α x) = (α+(n+2))/α) ∧
      ∀ α ε : ℝ, 0 < α → 0 < ε → ∀ K : ℝ,
      ∃ n : ℕ, K < condition (ridge (fun _ => 1) α (fun i : Fin (n+2) => (i.val:ℝ)*ε))) ∧
    ∀ (g : ℝ → ℝ) (α ε : ℝ), positiveKernel g → (∀ t ≥ 0, 0 ≤ g t) →
      AntitoneOn g (Set.Ici 0) → 0 < α → 0 < ε →
      (boundedCondition g α ε ↔ Summable (fun j : ℕ => g ((j:ℝ)*ε))) :=
  ⟨⟨constant_pos,constant_exact,grid_unbounded⟩,iff_sum⟩
end OMA.S_mo_363983

open OMA.S_mo_363983 in
theorem OMA.solution : type_of% @OMA.S_mo_363983.main := solve
