import OMAStatements.S_mo_420936

namespace OMA.S_mo_420936

lemma diag_sv {d : ℕ} (a : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a)
    (i : Fin d) : (Matrix.diagonal a).toEuclideanLin.singularValues i.val = a i := by
  classical
  let T := (Matrix.diagonal a).toEuclideanLin
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  let q := fun j : Fin d => a j ^ 2
  have hq : Antitone q := fun j k hjk => pow_le_pow_left₀ (ha k) (hmono hjk) 2
  have hT : T.adjoint ∘ₗ T = (Matrix.diagonal q).toEuclideanLin := by
    dsimp only [T]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change (Matrix.toLpLin 2 2 _ ∘ₗ Matrix.toLpLin 2 2 _) = Matrix.toLpLin 2 2 _
    rw [← Matrix.toLpLin_mul_same]
    congr 1
    simp [q, Matrix.diagonal_mul_diagonal, sq]
  have hroots : (T.adjoint ∘ₗ T).charpoly.roots = Finset.univ.val.map q := by
    rw [hT, Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.charpoly_toLin,
      Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by simp [Finset.prod_ne_zero_iff,
        Polynomial.X_sub_C_ne_zero])]
    simp
  have hev : T.isSymmetric_adjoint_comp_self.eigenvalues hn = q := by
    rw [← List.ofFn_inj, ← T.isSymmetric_adjoint_comp_self.sort_roots_charpoly_eq_eigenvalues hn,
      hroots, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hq.sortedGE_ofFn
  change T.singularValues i.val = a i
  rw [T.singularValues_fin hn, hev]
  exact Real.sqrt_sq (ha i)

end OMA.S_mo_420936

namespace OMA.S_mo_420936

private lemma single_lower {a b p q : ℝ} (hb : 0≤b) (hab : b≤a) (hp : 0<p) (hq : 0<q) :
    ((a*b)^p)^(1+q/(2*p)) ≤ (a*b)^p*a^q := by
  have ha := hb.trans hab
  have hab0 := mul_nonneg ha hb
  have he : p*(1+q/(2*p))=p+q/2 := by field_simp
  have hhalf : (a*b)^(q/2) ≤ a^q := by
    calc
      _ ≤ (a*a)^(q/2) := Real.rpow_le_rpow hab0 (mul_le_mul_of_nonneg_left hab ha) (by positivity)
      _ = a^q := by
        rw [← sq,← Real.rpow_natCast,← Real.rpow_mul ha]
        congr 1
        push_cast
        ring
  rw [← Real.rpow_mul hab0,he,Real.rpow_add_of_nonneg hab0 hp.le (by positivity)]
  exact mul_le_mul_of_nonneg_left hhalf (Real.rpow_nonneg hab0 _)

private lemma lower (d m : ℕ) (p q : ℝ) (hp : 0<p) (hq : 0<q) (A : Fin (m+2) → Mat (d+2)) :
    ((m:ℝ)+2)*(t2 A p / ((m:ℝ)+2))^(1+q/(2*p)) ≤ mixed A p q := by
  let N : ℝ := (m:ℝ)+2
  have hN : 0<N := by dsimp [N]; positivity
  let a (i : Fin (m+2)) := pair (A i) p
  have ha (i : Fin (m+2)) : 0 ≤ a i := Real.rpow_nonneg
    (mul_nonneg ((A i).toEuclideanLin.singularValues_nonneg _) ((A i).toEuclideanLin.singularValues_nonneg _)) _
  have hw : ∑ _ : Fin (m+2), N⁻¹ = 1 := by simp [N,show (m:ℝ)+2 ≠ 0 by positivity]
  have hJ := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ (fun _ => N⁻¹) a
    (fun i _ => inv_nonneg.mpr hN.le) hw (fun i _ => ha i) (p := 1+q/(2*p)) (by have := div_nonneg hq.le (by positivity : 0≤2*p); linarith)
  simp only [← Finset.mul_sum] at hJ
  have h2 : ∑ i, (a i)^(1+q/(2*p)) ≤ mixed A p q := by
    apply Finset.sum_le_sum
    intro i _
    exact single_lower ((A i).toEuclideanLin.singularValues_nonneg 1)
      ((A i).toEuclideanLin.singularValues_antitone (by decide : 0≤1)) hp hq
  change N*((∑ i, a i)/N)^(1+q/(2*p)) ≤ _
  apply le_trans _ h2
  rw [div_eq_inv_mul]
  calc
    _ ≤ N*(N⁻¹*∑ i, (a i)^(1+q/(2*p))) := mul_le_mul_of_nonneg_left hJ hN.le
    _ = _ := by rw [← mul_assoc,mul_inv_cancel₀ hN.ne',one_mul]

end OMA.S_mo_420936

namespace OMA.S_mo_420936

private lemma sv_one (d : ℕ) : sv (1:Mat (d+2)) 0 = 1 ∧ sv (1:Mat (d+2)) 1 = 1 := by
  have h (i : Fin (d+2)) := diag_sv (fun _ : Fin (d+2) => (1:ℝ)) (fun _ => zero_le_one) antitone_const i
  exact ⟨by simpa [sv] using h 0,by simpa [sv] using h 1⟩

private lemma sharp (d m : ℕ) (p q : ℝ) :
    let A : Fin (m+2) → Mat (d+2) := fun _ => 1
    ((m:ℝ)+2)*(t2 A p / ((m:ℝ)+2))^(1+q/(2*p)) = mixed A p q := by
  dsimp only
  simp [t2,pair,mixed,(sv_one d).1,(sv_one d).2,show (m:ℝ)+2 ≠ 0 by positivity]

private lemma counter (d m : ℕ) (p q : ℝ) (hp : 0<p) (hq : 0<q) (c : ℝ) (hc : 0<c) :
    ∃ A : Fin (m+2) → Mat (d+2),
      (∀ i, IsUnit (A i) ∧ ∃ a : Fin (d+2) → ℝ, (∀ j, 0<a j) ∧ A i=Matrix.diagonal a) ∧
      mixed A p q < c*t2 A p*t1 A q := by
  let M : ℝ := max 1 (((m:ℝ)+2)/c) + 1
  have h1 : 1 ≤ M := by dsimp [M]; linarith [le_max_left 1 (((m:ℝ)+2)/c)]
  have hM : 0<M := zero_lt_one.trans_le h1
  have hbig : (m:ℝ)+2 < c*M := by
    have h : ((m:ℝ)+2)/c < M := by dsimp [M]; linarith [le_max_right 1 (((m:ℝ)+2)/c)]
    simpa [mul_comm] using (div_lt_iff₀ hc).mp h
  let u : ℝ := M^(1/q)
  let v : ℝ := M^(-(1/p) - 1/q)
  have hu : 1 ≤ u := Real.one_le_rpow h1 (by positivity)
  have hv : v ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by have := one_div_pos.mpr hp; have := one_div_pos.mpr hq; linarith)
  have hvp : 0<v := Real.rpow_pos_of_pos hM _
  have hprod : (u*v)^p = M⁻¹ := by
    dsimp [u,v]
    rw [← Real.rpow_add hM,← Real.rpow_mul hM.le]
    rw [show (1/q+(-(1/p)-1/q))*p = -1 by field_simp; ring,Real.rpow_neg_one]
  have hup : u^q=M := by dsimp [u]; rw [← Real.rpow_mul hM.le,one_div_mul_cancel hq.ne',Real.rpow_one]
  let a (j : Fin (d+2)) : ℝ := if j=0 then u else v
  have hap (j : Fin (d+2)) : 0<a j := by dsimp [a]; split <;> first | exact hvp | exact zero_lt_one.trans_le hu
  have ham : Antitone a := by
    intro i j hij
    by_cases hi : i=0
    · subst i; by_cases hj : j=0 <;> simp [a,hj,hv.trans hu]
    · have hj : j≠0 := fun h => hi (Fin.le_zero_iff.mp (h ▸ hij))
      simp [a,hi,hj]
  let D : Mat (d+2) := Matrix.diagonal a
  have hd0 : sv D 0=u := by simpa [sv,D,a] using diag_sv a (fun j => (hap j).le) ham 0
  have hd1 : sv D 1=v := by simpa [sv,D,a] using diag_sv a (fun j => (hap j).le) ham 1
  let A : Fin (m+2) → Mat (d+2) := Fin.cases D (fun _ => 1)
  refine ⟨A,?_,?_⟩
  · intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · refine ⟨(Matrix.isUnit_iff_isUnit_det D).mpr ?_,a,hap,rfl⟩
      change IsUnit (Matrix.diagonal a).det
      rw [Matrix.det_diagonal]
      exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun j _ => (hap j).ne'))
    · exact ⟨isUnit_one,fun _ => 1,fun _ => zero_lt_one,by simp [A]⟩
  · have hs : t1 A q = M+((m:ℝ)+1) := by
      simp only [t1,Fin.sum_univ_succ,A,Fin.cases_zero,Fin.cases_succ]
      simp [hd0,hup,(sv_one d).1]; ring
    have ht : t2 A p = M⁻¹+((m:ℝ)+1) := by
      simp only [t2,Fin.sum_univ_succ,A,Fin.cases_zero,Fin.cases_succ]
      simp [pair,hd0,hd1,hprod,(sv_one d).1,(sv_one d).2]; ring
    have hb : mixed A p q = (m:ℝ)+2 := by
      simp only [mixed,Fin.sum_univ_succ,A,Fin.cases_zero,Fin.cases_succ]
      simp [pair,hd0,hd1,hprod,hup,hM.ne',(sv_one d).1,(sv_one d).2]; ring
    rw [hs,ht,hb]
    apply hbig.trans_le
    calc
      c*M = (c*1)*M := by ring
      _ ≤ (c*(M⁻¹+((m:ℝ)+1)))*(M+((m:ℝ)+1)) := by
        gcongr <;> first | positivity | linarith [inv_pos.mpr hM,Nat.cast_nonneg (α:=ℝ) m]

end OMA.S_mo_420936

open OMA.S_mo_420936

theorem OMA.solution : type_of% @OMA.S_mo_420936.main := by
  intro d m p q hp hq
  exact ⟨fun A _ => lower d m p q hp hq A,sharp d m p q,counter d m p q hp hq⟩
