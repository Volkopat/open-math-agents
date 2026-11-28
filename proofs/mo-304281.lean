import OMAStatements.S_mo_304281
namespace OMA.S_mo_304281
open Finset Module Polynomial

private lemma finite_tests {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : Module.End ℂ V) (D : V →ₗ[ℂ] W) (v : V)
    (hf : ∀ j < finrank ℂ V, D ((T^j) v)=0) (k : ℕ) : D ((T^k) v)=0 := by
  classical
  by_cases hv : finrank ℂ V=0
  · have := Module.finrank_zero_iff.mp hv
    simp [Subsingleton.elim v 0]
  let P := (X^k : ℂ[X]) %ₘ T.charpoly
  have hc : T.charpoly ≠ 1 := fun he => hv (by
    rw [← T.charpoly_natDegree,he,natDegree_one])
  have hdeg : P.natDegree < finrank ℂ V := by
    rw [← T.charpoly_natDegree]
    exact natDegree_modByMonic_lt _ T.charpoly_monic hc
  have he : aeval T P = T^k := by
    have h := congrArg (aeval T) (modByMonic_add_div (X^k) T.charpoly)
    simpa [P,T.aeval_self_charpoly] using h
  rw [← he,aeval_def,eval₂_eq_sum_range' _ hdeg,LinearMap.sum_apply,map_sum]
  apply sum_eq_zero
  intro j hj
  simp [Algebra.algebraMap_eq_smul_one,hf j (mem_range.mp hj)]

private def invisible {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup W] [Module ℂ W] (T : Module.End ℂ V) (D : V →ₗ[ℂ] W) : Submodule ℂ V :=
  ⨅ k : ℕ, LinearMap.ker (D.comp (T^k))

private lemma invisible_iff {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup W] [Module ℂ W] (T : Module.End ℂ V) (D : V →ₗ[ℂ] W) (v : V) :
    v ∈ invisible T D ↔ ∀ k : ℕ, D ((T^k) v)=0 := by
  simp only [invisible,Submodule.mem_iInf,LinearMap.mem_ker,LinearMap.comp_apply]

private lemma stable_iff_tests {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (T : Module.End ℂ V) (D : V →ₗ[ℂ] W) (hrow : ∀ x, ‖T x‖^2+‖D x‖^2=‖x‖^2) :
    (∀ z : ℂ, T.HasEigenvalue z → ‖z‖ < 1) ↔
    ∀ x : V, (∀ j < finrank ℂ V, D ((T^j) x)=0) → x=0 := by
  constructor
  · intro hs x hx
    let S := invisible T D
    have hxS : x ∈ S := (invisible_iff T D x).2 (finite_tests T D x hx)
    by_contra hn
    have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr (fun hb => by
      change x ∈ S at hxS
      rw [hb,Submodule.mem_bot] at hxS
      exact hn hxS)
    have hinv (v : V) (hv : v ∈ S) : T v ∈ S := by
      apply (invisible_iff T D _).2
      intro k
      have hk := (invisible_iff T D v).1 hv (k+1)
      simpa [pow_succ,Module.End.mul_apply] using hk
    let U : Module.End ℂ S := T.restrict hinv
    obtain ⟨z,hz⟩ := U.exists_eigenvalue
    obtain ⟨v,hv⟩ := hz.exists_hasEigenvector
    have he : T v = z • (v:V) := congrArg Subtype.val hv.apply_eq_smul
    have hv0 : (v:V) ≠ 0 := fun heq => hv.2 (Subtype.ext heq)
    have heig : T.HasEigenvalue z := Module.End.hasEigenvalue_of_hasEigenvector (show T.HasEigenvector z (v:V) from
      ⟨Module.End.mem_eigenspace_iff.mpr he,hv0⟩)
    have hz1 := hs z heig
    have hDv := (invisible_iff T D (v:V)).1 v.2 0
    have hq := hrow (v:V)
    simp only [pow_zero,Module.End.one_apply] at hDv
    rw [he,norm_smul,hDv,norm_zero,zero_pow (by decide),add_zero,mul_pow] at hq
    have hpos := sq_pos_of_pos (norm_pos_iff.mpr hv0)
    have hh : ‖z‖^2 < 1 := by nlinarith [norm_nonneg z]
    nlinarith [mul_pos (sub_pos.mpr hh) hpos]
  · intro ht z hz
    obtain ⟨x,hx⟩ := hz.exists_hasEigenvector
    have he := hx.apply_eq_smul
    have hn : x ≠ 0 := hx.2
    have hq := hrow x
    rw [he,norm_smul,mul_pow] at hq
    have hp := sq_pos_of_pos (norm_pos_iff.mpr hn)
    by_contra! hge
    have hh : 1 ≤ ‖z‖^2 := by nlinarith
    have hd : D x=0 := norm_eq_zero.mp (by nlinarith [mul_nonneg (sub_nonneg.mpr hh) hp.le, norm_nonneg (D x)])
    apply hn (ht x ?_)
    intro k hk
    clear hk
    have hpow : (T^k) x=z^k • x := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ',Module.End.mul_apply,ih,map_smul,he,smul_smul,pow_succ]
    simp [hpow,hd]

open Matrix
open scoped Matrix ComplexConjugate InnerProductSpace
private abbrev E (n : ℕ) := EuclideanSpace ℂ (Fin n)
private abbrev liftM {ι κ : Type} (A : Matrix ι κ ℝ) := A.map Complex.ofReal

private lemma lift_adjoint {ι κ : Type} (A : Matrix ι κ ℝ) : (liftM A)ᴴ=liftM Aᵀ := by
  ext i j
  simp [liftM,Matrix.conjTranspose_apply]
private lemma lift_mul {ι κ ν : Type} [Fintype κ] (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) :
    liftM (A*B) = liftM A * liftM B := by
  ext i j
  simp [liftM,Matrix.mul_apply,Complex.ofReal_sum]
private lemma lift_pow {n : ℕ} (A : Sq n) (t : ℕ) : liftM (A^t)=(liftM A)^t := by
  induction t with
  | zero => simp [liftM,Matrix.map_one]
  | succ t h => rw [pow_succ,lift_mul,h,pow_succ]

private lemma eucl_mul {n m k : ℕ} (A : Matrix (Fin n) (Fin m) ℂ)
    (B : Matrix (Fin m) (Fin k) ℂ) (v : E k) :
    (A*B).toEuclideanLin v = A.toEuclideanLin (B.toEuclideanLin v) := by
  simp [Matrix.toEuclideanLin,Matrix.toLpLin_apply,Matrix.mulVec_mulVec]
private lemma eucl_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : ℕ) :
    (A^t).toEuclideanLin = (A.toEuclideanLin : Module.End ℂ (E n))^t := by
  induction t with
  | zero =>
    ext v i
    simp
  | succ t h =>
    ext v i
    rw [pow_succ,eucl_mul,h,pow_succ,Module.End.mul_apply]
private lemma eucl_char {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A.toEuclideanLin.charpoly=A.charpoly := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,Matrix.charpoly_toLin]

private lemma row_norm {n k : ℕ} (A : Sq n) (B : Matrix (Fin n) (Fin k) ℝ)
    (hr : A*Aᵀ+B*Bᵀ=1) (x : E n) :
    ‖(liftM Aᵀ).toEuclideanLin x‖^2+‖(liftM Bᵀ).toEuclideanLin x‖^2=‖x‖^2 := by
  have hr' : liftM A*liftM Aᵀ + liftM B*liftM Bᵀ = 1 := by
    rw [← lift_mul,← lift_mul]
    have h := congrArg (fun M : Sq n => liftM M) hr
    simpa [liftM,Matrix.map_add,Matrix.map_one] using h
  have hv : (liftM A).toEuclideanLin ((liftM Aᵀ).toEuclideanLin x) +
      (liftM B).toEuclideanLin ((liftM Bᵀ).toEuclideanLin x) = x := by
    rw [← eucl_mul,← eucl_mul]
    change ((liftM A*liftM Aᵀ).toEuclideanLin + (liftM B*liftM Bᵀ).toEuclideanLin) x=x
    rw [← map_add,hr']
    simp
  have hi := congrArg (fun y : E n => inner ℂ x y) hv
  rw [inner_add_right,← LinearMap.adjoint_inner_left (liftM A).toEuclideanLin,
    ← LinearMap.adjoint_inner_left (liftM B).toEuclideanLin,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint (liftM A),
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint (liftM B),lift_adjoint,lift_adjoint] at hi
  have he := congrArg (RCLike.re : ℂ → ℝ) hi
  simpa only [map_add,inner_self_eq_norm_sq] using he

private lemma re_mulvec {ι κ : Type} [Fintype κ] (M : Matrix ι κ ℝ) (x : κ → ℂ) (i : ι) :
    ((liftM M *ᵥ x) i).re = (M *ᵥ (fun j => (x j).re)) i := by
  simp [Matrix.mulVec,dotProduct,liftM,Complex.re_sum,Complex.mul_re]
private lemma im_mulvec {ι κ : Type} [Fintype κ] (M : Matrix ι κ ℝ) (x : κ → ℂ) (i : ι) :
    ((liftM M *ᵥ x) i).im = (M *ᵥ (fun j => (x j).im)) i := by
  simp [Matrix.mulVec,dotProduct,liftM,Complex.im_sum,Complex.mul_im]
private lemma null_lift {ι κ : Type} [Fintype κ] (M : Matrix ι κ ℝ) :
    (∀ x : κ → ℂ, liftM M *ᵥ x=0 → x=0) ↔ (∀ x : κ → ℝ, M *ᵥ x=0 → x=0) := by
  constructor
  · intro h x hx
    have hv : liftM M *ᵥ (fun i => (x i:ℂ))=0 := by
      funext i
      apply Complex.ext
      · simpa [re_mulvec] using congrFun hx i
      · simp [Matrix.mulVec,dotProduct]
    have hz := h _ hv
    funext i
    exact congrArg Complex.re (congrFun hz i)
  · intro h x hx
    have hr : M *ᵥ (fun j => (x j).re)=0 := funext fun i => by
      rw [← re_mulvec,hx];rfl
    have hi : M *ᵥ (fun j => (x j).im)=0 := funext fun i => by
      rw [← im_mulvec,hx];rfl
    funext i
    exact Complex.ext (congrFun (h _ hr) i) (congrFun (h _ hi) i)

private lemma rank_iff_null {ι : Type} [Fintype ι] {n : ℕ} (M : Matrix ι (Fin n) ℝ) :
    M.rank=n ↔ ∀ x : Fin n → ℝ, M *ᵥ x=0 → x=0 := by
  let f := M.mulVecLin
  have h := f.finrank_range_add_finrank_ker
  have ht : finrank ℝ (Fin n → ℝ)=n := by simp
  rw [ht] at h
  change finrank ℝ (LinearMap.range f)=n ↔ _
  rw [show finrank ℝ (LinearMap.range f)=n ↔ finrank ℝ (LinearMap.ker f)=0 by omega,
    Submodule.finrank_eq_zero]
  exact ⟨fun he x hx => by
    have hm : x ∈ LinearMap.ker f := hx
    rwa [he,Submodule.mem_bot] at hm,fun h => LinearMap.ker_eq_bot'.mpr h⟩

private lemma tests_iff_null {n k : ℕ} (A : Sq n) (B : Matrix (Fin n) (Fin k) ℝ) :
    (∀ x : E n, (∀ j < finrank ℂ (E n),
      (liftM Bᵀ).toEuclideanLin ((((liftM Aᵀ).toEuclideanLin : Module.End ℂ (E n))^j) x)=0) → x=0) ↔
    ∀ x : Fin n → ℂ, liftM (tests A B) *ᵥ x=0 → x=0 := by
  have hf : finrank ℂ (E n)=n := by simp [E]
  let T : Module.End ℂ (E n) := (liftM Aᵀ).toEuclideanLin
  let D := (liftM Bᵀ).toEuclideanLin
  have hentry (x : E n) (t : Fin n) (i : Fin k) :
      (D ((T^t.val) x)) i = (liftM (tests A B) *ᵥ WithLp.ofLp x) (t,i) := by
    dsimp only [D,T]
    rw [← eucl_pow,← eucl_mul,← lift_pow,← lift_mul]
    rfl
  have hz (x : E n) : (∀ j < finrank ℂ (E n), D ((T^j) x)=0) ↔
      liftM (tests A B) *ᵥ WithLp.ofLp x=0 := by
    rw [hf]
    constructor
    · intro hh
      funext ti
      rcases ti with ⟨t,i⟩
      rw [← hentry,hh _ t.isLt]
      rfl
    · intro hh j hj
      ext i
      exact (hentry x ⟨j,hj⟩ i).trans (congrFun hh _)
  constructor
  · intro h x hx
    have hy := h (WithLp.toLp 2 x) ((hz _).2 hx)
    exact congrArg WithLp.ofLp hy
  · intro h x hx
    have hy := h (WithLp.ofLp x) ((hz _).1 hx)
    exact congrArg (WithLp.toLp 2) hy

private lemma solve (n k : ℕ) (A : Sq n) (B : Matrix (Fin n) (Fin k) ℝ)
    (hr : A*Aᵀ+B*Bᵀ=1) :
    (∀ z : ℂ, (A.map Complex.ofReal).charpoly.IsRoot z → ‖z‖ ≤ 1) ∧
    (stable A ↔ (tests A B).rank=n) := by
  let T : Module.End ℂ (E n) := (liftM Aᵀ).toEuclideanLin
  let D := (liftM Bᵀ).toEuclideanLin
  have hi (z : ℂ) : T.HasEigenvalue z ↔ (A.map Complex.ofReal).charpoly.IsRoot z := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
    change (liftM Aᵀ).toEuclideanLin.charpoly.IsRoot z ↔ _
    rw [eucl_char,show liftM Aᵀ=(liftM A)ᵀ from rfl,Matrix.charpoly_transpose]
  constructor
  · intro z h
    obtain ⟨x,hx⟩ := ((hi z).2 h).exists_hasEigenvector
    have hnorm : ‖T x‖^2+‖D x‖^2=‖x‖^2 := row_norm A B hr x
    rw [hx.apply_eq_smul,norm_smul,mul_pow] at hnorm
    have hp := sq_pos_of_pos (norm_pos_iff.mpr hx.2)
    by_contra! hgt
    have hh : 1 < ‖z‖^2 := by nlinarith
    nlinarith [mul_pos (sub_pos.mpr hh) hp,sq_nonneg ‖D x‖]
  · unfold stable
    simp_rw [← hi]
    exact (stable_iff_tests T D (row_norm A B hr)).trans
      ((tests_iff_null A B).trans ((null_lift _).trans (rank_iff_null _).symm))
end OMA.S_mo_304281
theorem OMA.solution : type_of% @OMA.S_mo_304281.main := OMA.S_mo_304281.solve
