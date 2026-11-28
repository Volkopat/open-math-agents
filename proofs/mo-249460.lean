import OMAStatements.S_mo_249460

namespace OMA.S_mo_249460
open Matrix Finset

private lemma horizontal_psd {n m : ℕ} (Q : Form n m) (hf : feasible Q) :
    Q.G.PosSemidef := by
  have hrv (l : ℕ) : rv (0 : ZV l) = 0 := by ext i; simp [rv]
  have hi (z : ZV n) : 0 ≤ bil Q.G z z := by
    by_cases hz : z=0
    · simp [hz,bil,hrv]
    · have h := hf z 0 ⟨none,none,by simp⟩ (Or.inl hz)
      simpa [val,bil,hrv] using (zero_le_one.trans h)
  have hq (q : Fin n → ℚ) : 0 ≤ (fun i => (q i : ℝ)) ⬝ᵥ (Q.G *ᵥ fun i => (q i : ℝ)) := by
    obtain ⟨s,hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
    choose z hz using hs
    let y : RV n := fun i => (q i:ℝ)
    have hx : rv z = (s.val:ℝ) • y := by
      funext i
      have h : (z i : ℚ) = (s.val:ℚ)*q i := by simpa [zsmul_eq_mul] using hz i
      change (z i:ℝ) = (s.val:ℝ)*(q i:ℝ)
      exact_mod_cast h
    have h := hi z
    rw [bil,hx,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul,smul_eq_mul,← mul_assoc] at h
    have hs0 : (s.val:ℝ)≠0 := by exact_mod_cast nonZeroDivisors.ne_zero s.property
    exact nonneg_of_mul_nonneg_right h (mul_self_pos.mpr hs0)
  have hreal (x : RV n) : 0 ≤ x ⬝ᵥ (Q.G *ᵥ x) := by
    have hden : DenseRange (fun q : Fin n → ℚ => fun i => (q i : ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    apply hden.induction_on (p:=fun x => 0 ≤ x ⬝ᵥ (Q.G *ᵥ x)) x _ hq
    apply isClosed_le continuous_const
    unfold dotProduct Matrix.mulVec
    fun_prop
  exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg Q.symG (fun x => by simpa using hreal x)

lemma positive_of_det {n m : ℕ} (Q : Form n m) (hf : feasible Q) (hd : 0<Q.G.det) :
    Q.G.PosDef :=
  (horizontal_psd Q hf).posDef_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd.ne'))
end OMA.S_mo_249460

namespace OMA.S_mo_249460
open Matrix Finset Set

private lemma db_cast_mul {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (v : ZV n) :
    rv (B *ᵥ v) = (B.map (Int.castRingHom ℝ)) *ᵥ rv v := by
  ext i
  simp [rv,mulVec,dotProduct]

private lemma db_repr {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (G : Mat n) (hb : ∀ j,normal G (fun i => B i j))
    (x : ZV n) : ∃ y : ZV n, (∃ u : ZV n, x-y=B*ᵥu) ∧
      ∀ z, |2*bil G y z| ≤ 3*(n:ℝ)*bil G z z := by
  let A := B.map (Int.castRingHom ℝ)
  have hA : IsUnit A.det := by
    change IsUnit (((Int.castRingHom ℝ).mapMatrix B).det)
    rw [← RingHom.map_det,isUnit_iff_ne_zero]
    change (B.det : ℝ) ≠ 0
    exact_mod_cast hB
  let v := A⁻¹ *ᵥ rv x
  let u : ZV n := fun i => ⌊v i⌋
  let t : RV n := fun i => Int.fract (v i)
  let y := x-B*ᵥu
  have ht (i : Fin n) : t i ∈ Set.Ico (0:ℝ) 1 := ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  have hf : t = v-rv u := rfl
  have hy : rv y = A *ᵥ t := by
    rw [hf,mulVec_sub,show A *ᵥ v = rv x by
      simp [v,mulVec_mulVec,A.mul_nonsing_inv hA],←db_cast_mul]
    ext i
    simp [y,rv]
  refine ⟨y,⟨u,by simp [y]⟩,fun z => ?_⟩
  have heq : 2*bil G y z=∑ j,t j*(2*bil G (fun i => B i j) z) := by
    rw [bil,hy]
    have H : A*ᵥt=∑ j,t j • rv (fun i => B i j) := by
      ext i
      simp [A,rv,mulVec,dotProduct,Finset.sum_apply,mul_comm]
    rw [H,sum_dotProduct,Finset.mul_sum]
    apply sum_congr rfl
    intro j _
    rw [smul_dotProduct,smul_eq_mul,bil]
    ring
  rw [heq]
  calc
    _ ≤ ∑ j, |t j * (2*bil G (fun i => B i j) z)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n,3*bil G z z := by
      apply sum_le_sum
      intro j _
      rw [abs_mul,abs_of_nonneg (ht j).1]
      exact (mul_le_of_le_one_left (abs_nonneg _) (ht j).2.le).trans (hb j z)
    _ = _ := by simp; ring

private lemma db_residue_inj {n : ℕ} (G : Mat n) (hG : G.PosDef) (x y : ZV n)
    (hx : ∀ z, |2*bil G x z| ≤ 3*(n:ℝ)*bil G z z)
    (hy : ∀ z, |2*bil G y z| ≤ 3*(n:ℝ)*bil G z z)
    (he : ∀ i, (x i : ZMod (6*n+1)) = (y i : ZMod (6*n+1))) : x=y := by
  let q := 6*n+1
  have divis (i : Fin n) : (q:ℤ) ∣ y i-x i := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (he i)
  choose w hw using divis
  by_cases hw0 : w=0
  · ext i
    have h := hw i
    rw [hw0] at h
    simpa [sub_eq_zero,eq_comm] using h
  have hwr : rv w ≠ 0 := by
    intro h
    apply hw0
    ext i
    have hi := congrFun h i
    change (w i:ℝ) = 0 at hi
    change w i=0
    exact_mod_cast hi
  have hpos : 0 < bil G w w := by simpa [bil] using hG.dotProduct_mulVec_pos hwr
  have hd : rv y-rv x = (q:ℝ) • rv w := by
    ext i
    change (y i : ℝ) - (x i : ℝ) = (q:ℝ)*(w i:ℝ)
    exact_mod_cast hw i
  have H : bil G y w-bil G x w=(q:ℝ)*bil G w w := by
    simp only [bil,←sub_dotProduct,hd,smul_dotProduct,smul_eq_mul]
  have hx' := (abs_le.mp (hx w)).1
  have hy' := (abs_le.mp (hy w)).2
  dsimp [q] at H
  push_cast at H
  nlinarith [Nat.cast_nonneg (α:=ℝ) n, mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) hpos.le]

lemma det_normal_bound {n : ℕ} (G : Mat n) (h : G.PosDef)
    (B : Matrix (Fin n) (Fin n) ℤ) (hb : ∀ j,normal G (fun i => B i j)) :
    B.det.natAbs ≤ (6*n+1)^n := by
  classical
  by_cases hB : B.det=0
  · simp [hB]
  let f := B.toLin'
  let L := LinearMap.range f
  have hf : Function.Injective f := B.mulVec_injective_of_det_ne_zero hB
  let e := LinearEquiv.ofInjective f hf
  have hcard : B.det.natAbs = Nat.card (ZV n ⧸ L) := by
    rw [←LinearMap.det_toLin']
    exact L.natAbs_det_equiv e
  have reps (c : ZV n ⧸ L) : ∃ y : ZV n, L.mkQ y = c ∧
      ∀ z, |2*bil G y z| ≤ 3*(n:ℝ)*bil G z z := by
    obtain ⟨x,rfl⟩ := L.mkQ_surjective c
    obtain ⟨y,⟨u,hu⟩,hy⟩ := db_repr B hB G hb x
    refine ⟨y,?_,hy⟩
    symm
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (Submodule.Quotient.mk_eq_zero L).mpr
    exact ⟨u,hu.symm⟩
  choose repr hclass hbound using reps
  let F (c : ZV n ⧸ L) (i : Fin n) : ZMod (6*n+1) := (repr c i:ℤ)
  have hinj : Function.Injective F := by
    intro c d hcd
    have hr := db_residue_inj G h (repr c) (repr d) (hbound c) (hbound d) (congrFun hcd)
    rw [←hclass c,hr,hclass d]
  rw [hcard]
  simpa [Nat.card_pi,Nat.card_zmod] using Nat.card_le_card_of_injective F hinj

end OMA.S_mo_249460

namespace OMA.S_mo_249460
open Matrix Finset

private def rmat {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℤ) : Matrix (Fin n) (Fin m) ℝ :=
  fun i j => U i j
private lemma s_rv_add {n : ℕ} (x z : ZV n) : rv (x+z)=rv x+rv z := by ext i; simp [rv]
private lemma s_rv_neg {n : ℕ} (x : ZV n) : rv (-x) = -rv x := by ext i; simp [rv]
private lemma s_rv_sub {n : ℕ} (x z : ZV n) : rv (x-z)=rv x-rv z := by ext i; simp [rv]
private lemma s_rv_zero (n : ℕ) : rv (0 : ZV n) = 0 := by ext i; simp [rv]
private lemma s_rv_mul {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℤ) (y : ZV m) :
    rv (U *ᵥ y)=rmat U *ᵥ rv y := by ext i; simp [rv,rmat,Matrix.mulVec,dotProduct]
private lemma s_rt_neg {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℤ) : rmat (-U)= -rmat U := by
  ext i j
  simp [rmat]

private def shear {n m : ℕ} (Q : Form n m) (C : Matrix (Fin n) (Fin m) ℝ) : Form n m where
  G := Q.G
  B := Q.G*C+Q.B
  D := Q.D+Cᵀ*Q.G*C+Cᵀ*Q.B+Q.Bᵀ*C
  symG := Q.symG
  symD := by
    change (Q.D+Cᵀ*Q.G*C+Cᵀ*Q.B+Q.Bᵀ*C)ᵀ=_
    have hg : Q.Gᵀ=Q.G := Q.symG
    have hd : Q.Dᵀ=Q.D := Q.symD
    simp only [transpose_add,transpose_mul,transpose_transpose,hg,hd,Matrix.mul_assoc]
    abel

private lemma shear_cancel {n m : ℕ} (Q : Form n m) (C : Matrix (Fin n) (Fin m) ℝ) :
    shear (shear Q C) (-C)=Q := by
  cases Q with
  | mk G B D hG hD =>
    simp only [shear,Form.mk.injEq,true_and]
    constructor
    · simp
    · have hg : Gᵀ=G := hG
      simp only [transpose_neg,Matrix.neg_mul,Matrix.mul_neg,neg_neg,transpose_add,transpose_mul,hg,
        Matrix.mul_add,Matrix.add_mul,Matrix.mul_assoc]
      abel

private lemma s_trans_dot {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (x : RV m) (y : RV n) :
    x ⬝ᵥ (Cᵀ *ᵥ y) = (C *ᵥ x) ⬝ᵥ y := by rw [dotProduct_mulVec,vecMul_transpose]
private lemma s_sym_dot {n : ℕ} (G : Mat n) (h : G.IsHermitian) (x y : RV n) :
    x ⬝ᵥ (G *ᵥ y) = y ⬝ᵥ (G *ᵥ x) := by
  have he : Gᵀ=G := h
  simpa only [he] using dotProduct_transpose_mulVec G x y

private lemma val_shear {n m : ℕ} (Q : Form n m) (U : Matrix (Fin n) (Fin m) ℤ) (x : ZV n) (y : ZV m) :
    val (shear Q (rmat U)) x y = val Q (x+U*ᵥy) y := by
  simp only [val,bil,shear,s_rv_add,s_rv_mul,add_mulVec,mulVec_add,← mulVec_mulVec,
    dotProduct_add,add_dotProduct,s_trans_dot]
  rw [s_sym_dot Q.G Q.symG ((rmat U)*ᵥrv y) (rv x)]
  rw [dotProduct_comm (Q.B *ᵥ rv y) (rmat U *ᵥ rv y)]
  ring

private lemma shear_feasible {n m : ℕ} (Q : Form n m) (U : Matrix (Fin n) (Fin m) ℤ)
    (hf : feasible Q) : feasible (shear Q (rmat U)) := by
  intro x y hy hxy
  rw [val_shear]
  apply hf _ _ hy
  by_cases hz : y=0
  · subst y
    simpa using hxy
  · exact Or.inr hz

private lemma shear_perfect {n m : ℕ} (Q : Form n m) (U : Matrix (Fin n) (Fin m) ℤ)
    (hp : perfect Q) : perfect (shear Q (rmat U)) := by
  intro T hT
  have h : shear T (rmat (-U))=Q := by
    apply hp
    intro x y hy hxy
    rw [val_shear]
    apply hT _ _ hy
    rw [val_shear,neg_mulVec,neg_add_cancel_right]
    exact hxy
  have he := congrArg (fun R => shear R (rmat U)) h
  rw [s_rt_neg] at he
  simpa only [show shear (shear T (-rmat U)) (rmat U)=T by simpa using shear_cancel T (-rmat U)] using he
private lemma quad_coercive {n : ℕ} [Nonempty (Fin n)] (G : Mat n) (hg : G.PosDef) :
    ∃ c : ℝ, 0<c ∧ ∀ x : RV n,c*‖x‖^2 ≤ x ⬝ᵥ (G *ᵥ x) := by
  let q (x : RV n) := x ⬝ᵥ (G *ᵥ x)
  have hcont : Continuous q := by
    unfold q Matrix.mulVec dotProduct
    fun_prop
  obtain ⟨u,hu,hm⟩ := (isCompact_sphere (0:RV n) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
  have hun : ‖u‖=1 := by simpa using hu
  have hc : 0<q u := by simpa [q] using hg.dotProduct_mulVec_pos (show u≠0 by intro h; simp [h] at hun)
  refine ⟨q u,hc,fun x => ?_⟩
  by_cases hx : x=0
  · simp [hx]
  have hp := norm_pos_iff.mpr hx
  let v := ‖x‖⁻¹ • x
  have hv : v∈Metric.sphere (0:RV n) 1 := by simp [v,norm_smul,hp.ne']
  have hh := isMinOn_iff.mp hm v hv
  have hback : x=‖x‖ • v := by simp [v,smul_smul,hp.ne']
  have he : x ⬝ᵥ (G *ᵥ x)=‖x‖^2 * q v := by
    conv_lhs => rw [hback]
    simp [q,mulVec_smul,smul_dotProduct,dotProduct_smul,sq,mul_assoc]
  rw [he,mul_comm]
  exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)

private lemma layer_min {n m : ℕ} (Q : Form n m) (hg : Q.G.PosDef) (y : ZV m) :
    ∃ b : ZV n,∀ x : ZV n,val Q b y ≤ val Q x y := by
  classical
  cases n with
  | zero =>
    exact ⟨0, fun x => by rw [Subsingleton.elim x 0]⟩
  | succ n =>
    obtain ⟨c,hc,hco⟩ := quad_coercive Q.G hg
    let w := Q.B *ᵥ rv y
    let M := ∑ i, |w i|
    have hM : 0≤M := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have cross (x : RV (n+1)) : |x ⬝ᵥ w| ≤ ‖x‖*M := by
      change |∑ i, x i*w i| ≤ _
      calc
        _ ≤ ∑ i, |x i*w i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, ‖x‖*|w i| := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (norm_le_pi_norm x i) (abs_nonneg _)
        _ = _ := (Finset.mul_sum ..).symm
    have bounded (x : ZV (n+1)) (hx : val Q x y ≤ val Q 0 y) : ‖rv x‖ ≤ 2*M/c := by
      have hle : c*‖rv x‖^2 ≤ 2*‖rv x‖*M := by
        simp only [val,bil,s_rv_zero,zero_dotProduct,mul_zero,add_zero,zero_add] at hx
        have h := (abs_le.mp (cross (rv x))).1
        change -(‖rv x‖*M) ≤ rv x ⬝ᵥ (Q.B *ᵥ rv y) at h
        linarith [hco (rv x)]
      rw [le_div_iff₀ hc]
      rcases (norm_nonneg (rv x)).eq_or_lt with h|h
      · rw [← h,zero_mul]; positivity
      · apply le_of_mul_le_mul_right _ h
        nlinarith only [hle]
    obtain ⟨N,hN⟩ := exists_nat_gt (2*M/c)
    let box := Finset.Icc (fun _ : Fin (n+1) => -(N:ℤ)) (fun _ => (N:ℤ))
    have hzero : (0:ZV (n+1))∈box := by
      apply Finset.mem_Icc.mpr
      constructor <;> intro i <;> simp
    obtain ⟨a,_,ha⟩ := box.exists_min_image (fun x => val Q x y) ⟨0,hzero⟩
    refine ⟨a,fun x => ?_⟩
    by_cases hx : val Q x y ≤ val Q 0 y
    · apply ha
      have hxn := (bounded x hx).trans hN.le
      have bnd (i : Fin (n+1)) : |(x i:ℝ)| ≤ (N:ℝ) := (norm_le_pi_norm (rv x) i).trans hxn
      apply Finset.mem_Icc.mpr
      exact ⟨fun i => by exact_mod_cast (abs_le.mp (bnd i)).1,fun i => by exact_mod_cast (abs_le.mp (bnd i)).2⟩
    · exact (ha 0 hzero).trans (le_of_not_ge hx)
private def s_cross {n m : ℕ} (Q : Form n m) (z : ZV n) (y : ZV m) : ℝ :=
  rv z ⬝ᵥ (Q.B *ᵥ rv y)

private lemma line_plus {n m : ℕ} (Q : Form n m) (x z : ZV n) (y : ZV m) :
    val Q (x+z) y = val Q x y+2*bil Q.G x z+2*s_cross Q z y+bil Q.G z z := by
  simp only [val,bil,s_cross,s_rv_add,mulVec_add,add_dotProduct,dotProduct_add]
  rw [s_sym_dot Q.G Q.symG (rv z) (rv x)]
  ring

private lemma line_neg {n m : ℕ} (Q : Form n m) (x z : ZV n) (y : ZV m) :
    val Q (x+ -z) y=val Q x y-2*bil Q.G x z-2*s_cross Q z y+bil Q.G z z := by
  rw [line_plus]
  simp [bil,s_cross,s_rv_neg,mulVec_neg,neg_dotProduct,dotProduct_neg]
  ring

private lemma contact_bound {n m : ℕ} (Q : Form n m) (hg : Q.G.PosDef) (hf : feasible Q)
    (hmin : ∀ (j : Fin m) (x : ZV n),val Q 0 (site (some j)) ≤ val Q x (site (some j))) :
    ∀ x y,allowed y → val Q x y=1 → normal Q.G x := by
  have gnon (z : ZV n) : 0≤bil Q.G z z := by
    simpa only [bil,star_trivial] using hg.posSemidef.dotProduct_mulVec_nonneg (rv z)
  have zsite (z : ZV n) (i : Option (Fin m)) : |2*s_cross Q z (site i)| ≤ bil Q.G z z := by
    cases i with
    | none => simpa [site,s_cross,s_rv_zero] using gnon z
    | some j =>
      have ha := hmin j (0+z)
      have hb := hmin j (0+ -z)
      rw [line_plus] at ha
      rw [line_neg] at hb
      have h0 : bil Q.G 0 z=0 := by simp [bil,s_rv_zero]
      rw [h0] at ha hb
      exact abs_le.mpr ⟨by linarith,by linarith⟩
  have zcross (z : ZV n) (y : ZV m) (hy : allowed y) : |2*s_cross Q z y| ≤ 2*bil Q.G z z := by
    obtain ⟨i,j,rfl⟩ := hy
    have he : 2*s_cross Q z (site i-site j)=2*s_cross Q z (site i)-2*s_cross Q z (site j) := by
      simp [s_cross,s_rv_sub,mulVec_sub,dotProduct_sub,mul_sub]
    rw [he]
    exact (abs_sub ..).trans (by linarith [zsite z i,zsite z j])
  have zallow : allowed (0 : ZV m) := ⟨none,none,by simp⟩
  have vnon (w : ZV n) (y : ZV m) (hy : allowed y) : 0≤val Q w y := by
    by_cases hn : w≠0 ∨ y≠0
    · exact zero_le_one.trans (hf _ _ hy hn)
    · push Not at hn
      simp [hn.1,hn.2,val,bil,s_rv_zero]
  intro x y hy hval z
  by_cases hz : z=0
  · simp [hz,bil,s_rv_zero]
  by_cases hzero : y=0
  · subst y
    have ha := vnon (x+z) 0 hy
    have hb := vnon (x+ -z) 0 hy
    rw [line_plus,hval] at ha
    rw [line_neg,hval] at hb
    have h0 : s_cross Q z 0=0 := by simp [s_cross,s_rv_zero]
    rw [h0] at ha hb
    have h1 : 1≤bil Q.G z z := by simpa [val,bil,s_rv_zero] using hf z 0 zallow (Or.inl hz)
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · have ha := hf (x+z) y hy (Or.inr hzero)
    have hb := hf (x+ -z) y hy (Or.inr hzero)
    rw [line_plus,hval] at ha
    rw [line_neg,hval] at hb
    obtain ⟨hl,hu⟩ := abs_le.mp (zcross z y hy)
    exact abs_le.mpr ⟨by linarith,by linarith⟩

private lemma normalize {n m : ℕ} (Q : Form n m) (hg : Q.G.PosDef) (hf : feasible Q)
    (hp : perfect Q) : ∃ R : Form n m,R.G=Q.G ∧ perfect R ∧
      ∀ x y,allowed y → val R x y=1 → normal R.G x := by
  choose b hmin using fun j : Fin m => layer_min Q hg (site (some j))
  let U : Matrix (Fin n) (Fin m) ℤ := fun i j => b j i
  have hu (j : Fin m) : U *ᵥ site (some j)=b j := Matrix.mulVec_single_one U j
  refine ⟨shear Q (rmat U),rfl,shear_perfect Q U hp,?_⟩
  apply contact_bound (shear Q (rmat U)) hg (shear_feasible Q U hf)
  intro j x
  rw [val_shear,val_shear,hu,zero_add]
  exact hmin j _
end OMA.S_mo_249460

namespace OMA.S_mo_249460
open Matrix Finset Set Submodule Module
private def contacts {n m : ℕ} (Q : Form n m) : Set (RV n) :=
  {u | ∃ (x : ZV n) (y : ZV m), allowed y ∧ val Q x y=1 ∧ rv x=u}

private lemma contacts_span {n m : ℕ} (Q : Form n m) (hQ : perfect Q) :
    span ℝ (contacts Q)=⊤ := by
  classical
  by_contra hn
  obtain ⟨f,hf,hker⟩ := (span ℝ (contacts Q)).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hn)
  let z : RV n := fun i => f (Pi.single i 1)
  have hrepr (u : RV n) : f u = z ⬝ᵥ u := by
    have h : u=∑ i,u i • (Pi.single i (1:ℝ) : RV n) := by
      ext j
      simp [Pi.single_apply]
    calc
      f u = f (∑ i,u i • (Pi.single i (1:ℝ) : RV n)) := congrArg f h
      _ = z ⬝ᵥ u := by simp [z,dotProduct,mul_comm]
  let Z : Mat n := vecMulVec z z
  have hZ : Z.IsHermitian := by ext i j; simp [Z,vecMulVec,mul_comm]
  let R : Form n m := {Q with G:=Q.G+Z, symG:=Q.symG.add hZ}
  have hR : R=Q := by
    apply hQ
    intro x y hy hv
    have hxc : rv x∈contacts Q := ⟨x,y,hy,hv,rfl⟩
    have hx : f (rv x)=0 := hker (subset_span hxc)
    rw [hrepr] at hx
    have hz : Z*ᵥrv x=0 := by change vecMulVec z z *ᵥ rv x=0; rw [vecMulVec_mulVec,hx]; simp
    simpa [R,val,bil,add_mulVec,hz] using hv
  have he (i : Fin n) : z i=0 := by
    have h := congrArg (fun M : Form n m => M.G i i) hR
    change Q.G i i+z i*z i=Q.G i i at h
    nlinarith
  exact hf (by ext x; simp [hrepr,dotProduct,he])

private lemma contact_basis {n m : ℕ} (Q : Form n m) (hQ : perfect Q) :
    ∃ B : Matrix (Fin n) (Fin n) ℤ, B.det≠0 ∧
      ∀ j, ∃ y, allowed y ∧ val Q (fun i => B i j) y=1 := by
  classical
  obtain ⟨T,hT,hspan,hind⟩ := exists_linearIndependent ℝ (contacts Q)
  have htop : span ℝ T=⊤ := hspan.trans (contacts_span Q hQ)
  let b : Basis T ℝ (RV n) := Basis.mk hind (by simpa using htop.ge)
  have : Finite T := Module.Finite.finite_basis b
  let _ := Fintype.ofFinite T
  have hcard : Fintype.card T=n := by simpa using (Module.finrank_eq_card_basis b).symm
  let e := (Fintype.equivFinOfCardEq hcard).symm
  choose X Y hY hval hX using fun i : Fin n => hT (e i).property
  let B : Matrix (Fin n) (Fin n) ℤ := fun i j => X j i
  have hind' : LinearIndependent ℝ (fun i => rv (X i)) := by
    simp_rw [hX]
    exact hind.comp e e.injective
  have hU : IsUnit (B.map (Int.castRingHom ℝ)) := Matrix.linearIndependent_cols_iff_isUnit.mp hind'
  have hdet := ((Matrix.isUnit_iff_isUnit_det _).mp hU).ne_zero
  refine ⟨B,?_,fun j => ⟨Y j,hY j,hval j⟩⟩
  intro h
  exact hdet (((Int.castRingHom ℝ).map_det B).symm.trans (by simp [h]))
end OMA.S_mo_249460

namespace OMA.S_mo_249460
open Matrix Finset Set
private abbrev IMat (n : ℕ) := Matrix (Fin n) (Fin n) ℤ
private def realMat {n : ℕ} (B : IMat n) : Mat n := B.map (Int.castRingHom ℝ)
private lemma real_det {n : ℕ} (B : IMat n) : (realMat B).det=(B.det:ℝ) :=
  ((Int.castRingHom ℝ).map_det B).symm

private lemma inverse_coordinate {n : ℕ} (B : IMat n) (h : B.det≠0) (x : ZV n) (i : Fin n) :
    ((realMat B)⁻¹ *ᵥ rv x) i = ((B.updateCol i x).det:ℝ)/(B.det:ℝ) := by
  have hD : (B.det:ℝ) ≠ 0 := by exact_mod_cast h
  have hU : IsUnit (realMat B).det := isUnit_iff_ne_zero.mpr ((real_det B).trans_ne hD)
  have hh : realMat B*ᵥrv (B.cramer x)=(B.det:ℝ) • rv x := by
    ext j
    have hc := (Int.castRingHom ℝ).map_mulVec B (B.cramer x) j
    rw [Matrix.mulVec_cramer] at hc
    calc
      _ = (↑((B.det • x) j) : ℝ) := hc.symm
      _ = _ := by simp [rv]
  have hx := congrArg (fun u : RV n => (realMat B)⁻¹ *ᵥ u) hh
  change (realMat B)⁻¹ *ᵥ (realMat B*ᵥrv (B.cramer x)) = (realMat B)⁻¹ *ᵥ ((B.det:ℝ) • rv x) at hx
  rw [mulVec_mulVec,Matrix.nonsing_inv_mul _ hU,one_mulVec,Matrix.mulVec_smul] at hx
  apply (eq_div_iff hD).2
  have hi := congrFun hx i
  simpa [rv,Matrix.cramer_apply,mul_comm] using hi.symm
end OMA.S_mo_249460

namespace OMA.S_mo_249460
open Matrix Finset Set
private def valueR {n m : ℕ} (Q : Form n m) (u : RV n) (y : ZV m) : ℝ :=
  u ⬝ᵥ (Q.G *ᵥ u) + 2*(u ⬝ᵥ (Q.B *ᵥ rv y)) + bil Q.D y y

private def pull {n m : ℕ} (L : Mat n) (Q : Form n m) : Form n m where
  G := Lᴴ*Q.G*L
  B := Lᴴ*Q.B
  D := Q.D
  symG := by
    change (Lᴴ*Q.G*L)ᴴ=_
    simp only [conjTranspose_mul,conjTranspose_conjTranspose,Q.symG.eq,Matrix.mul_assoc]
  symD := Q.symD

private lemma pull_value {n m : ℕ} (L : Mat n) (Q : Form n m) (u : RV n) (y : ZV m) :
    valueR (pull L Q) u y = valueR Q (L*ᵥu) y := by
  have move (z : RV n) : u ⬝ᵥ (Lᴴ *ᵥ z) = (L*ᵥu) ⬝ᵥ z := by
    change u ⬝ᵥ (Lᵀ*ᵥz)=_
    rw [dotProduct_mulVec,vecMul_transpose]
  simp only [valueR,pull,← mulVec_mulVec,move]

private lemma form_ext {n m : ℕ} {Q R : Form n m} (hG : Q.G=R.G) (hB : Q.B=R.B)
    (hD : Q.D=R.D) : Q=R := by cases Q; cases R; congr
private lemma pull_comp {n m : ℕ} (L N : Mat n) (Q : Form n m) :
    pull N (pull L Q)=pull (L*N) Q := by
  apply form_ext <;> simp [pull,Matrix.mul_assoc]
private lemma pull_one {n m : ℕ} (Q : Form n m) : pull 1 Q=Q := by
  apply form_ext <;> simp [pull]

private def small (c : ℕ) : Set ℤ := {z | z.natAbs≤c}
private def scalars (c : ℕ) : Set ℝ := Set.image2 (fun u v : ℤ => (u:ℝ)/(v:ℝ)) (small c) (small c)
private def grid (n m c : ℕ) : Set (RV n × ZV m) :=
  (Set.univ.pi fun _ : Fin n => scalars c) ×ˢ {y | allowed y}
private lemma finite_grid (n m c : ℕ) : (grid n m c).Finite := by
  have hs : (small c).Finite := (Set.finite_Icc (-(c:ℤ)) c).subset (by intro z hz; change z.natAbs≤c at hz; constructor <;> omega)
  have hsc := hs.image2 (fun u v : ℤ => (u:ℝ)/(v:ℝ)) hs
  have ha : ({y | allowed y} : Set (ZV m)).Finite := by
    apply (Set.finite_range (fun t : Option (Fin m) × Option (Fin m) => site t.1-site t.2)).subset
    rintro y ⟨i,j,h⟩
    exact ⟨(i,j),h.symm⟩
  exact (Set.Finite.pi (fun _ => hsc)).prod ha

private def determined {n m : ℕ} (s : Set (RV n × ZV m)) : Set (Form n m) :=
  {Q | ∀ R : Form n m, (∀ p∈s, valueR Q p.1 p.2=1 → valueR R p.1 p.2=1) → R=Q}
private lemma finite_determined {n m : ℕ} {s : Set (RV n × ZV m)} (hs : s.Finite) :
    (determined s).Finite := by
  let F := fun Q : Form n m => s ∩ {p | valueR Q p.1 p.2=1}
  apply Set.Finite.of_injOn (f:=F) (t:=𝒫 s) (fun _ _ => Set.inter_subset_left) _ hs.powerset
  intro Q hQ R hR he
  apply hR
  intro p hp hv
  have hh : p∈F R := ⟨hp,hv⟩
  exact (show p∈F Q from he ▸ hh).2
end OMA.S_mo_249460

namespace OMA.S_mo_249460
open Matrix Finset Set
private lemma determinant_finite (n m : ℕ) :
    {t : ℝ | ∃ Q : Form n m, feasible Q ∧ perfect Q ∧ Q.G.det=t}.Finite := by
  classical
  let c := (6*n+1)^n
  let s := grid n m c
  let forms := determined s
  have hforms : forms.Finite := finite_determined (finite_grid n m c)
  have hsmall : (small c).Finite :=
    (Set.finite_Icc (-(c:ℤ)) c).subset (by intro z hz; change z.natAbs≤c at hz; constructor <;> omega)
  let F := fun (R : Form n m) (d : ℤ) => R.G.det/(d:ℝ)^2
  apply ((hforms.image2 F hsmall).insert 0).subset
  rintro t ⟨Q,hf,hp,rfl⟩
  by_cases hz : Q.G.det=0
  · exact Or.inl hz
  right
  have hg := positive_of_det Q hf (lt_of_le_of_ne (horizontal_psd Q hf).det_nonneg (Ne.symm hz))
  obtain ⟨R,hG,hR,hn⟩ := normalize Q hg hf hp
  obtain ⟨B,hB,hcol⟩ := contact_basis R hR
  have hgR : R.G.PosDef := hG ▸ hg
  have hcols (j : Fin n) : normal R.G (fun i => B i j) := by
    obtain ⟨y,hy,he⟩ := hcol j
    exact hn _ _ hy he
  have hsmallB : B.det∈small c := det_normal_bound _ hgR B hcols
  let L := realMat B
  have hunit : IsUnit L.det := isUnit_iff_ne_zero.mpr (by
    change (realMat B).det≠0
    rw [real_det]
    exact_mod_cast hB)
  have hgrid (x : ZV n) (y : ZV m) (hy : allowed y) (he : val R x y=1) :
      (L⁻¹*ᵥrv x,y)∈s := by
    refine ⟨fun i _ => ?_,hy⟩
    have hu : ∀ j, normal R.G (fun k => (B.updateCol i x) k j) := by
      intro j
      by_cases h : j=i
      · subst j
        simpa only [Matrix.updateCol_self] using hn x y hy he
      · simpa only [Matrix.updateCol_ne h] using hcols j
    have hnum := det_normal_bound _ hgR (B.updateCol i x) hu
    exact ⟨_,hnum,_,hsmallB,(inverse_coordinate B hB x i).symm⟩
  refine ⟨pull L R,?_,B.det,hsmallB,?_⟩
  · intro T hT
    have ht : pull L⁻¹ T=R := by
      apply hR
      intro x y hy he
      change valueR (pull L⁻¹ T) (rv x) y=1
      rw [pull_value]
      apply hT (L⁻¹*ᵥrv x,y) (hgrid x y hy he)
      change valueR (pull L R) (L⁻¹*ᵥrv x) y=1
      rwa [pull_value,mulVec_mulVec,Matrix.mul_nonsing_inv L hunit,one_mulVec]
    calc
      T = pull L (pull L⁻¹ T) := by rw [pull_comp,Matrix.nonsing_inv_mul L hunit,pull_one]
      _ = pull L R := congrArg (pull L) ht
  · change (Lᴴ*R.G*L).det/(B.det:ℝ)^2=Q.G.det
    rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_conjTranspose,hG]
    change L.det*Q.G.det*L.det/(B.det:ℝ)^2=Q.G.det
    rw [show L.det=(B.det:ℝ) from real_det B]
    field_simp [show (B.det:ℝ)≠0 by exact_mod_cast hB]

private lemma determinant_bound (n m : ℕ) : ∃ C : ℝ, ∀ Q : Form n m,
    feasible Q → perfect Q → Q.G.det≤C := by
  obtain ⟨C,hC⟩ := (determinant_finite n m).bddAbove
  exact ⟨C,fun Q hf hp => hC ⟨Q,hf,hp,rfl⟩⟩
end OMA.S_mo_249460

open OMA.S_mo_249460
theorem OMA.solution : type_of% @OMA.S_mo_249460.main :=
  ⟨determinant_finite,determinant_bound⟩
