import OMAReductions.R_Arxiv_0805_3777_cprank_le_of_square_slices_R1

/-! # Diagonal terms and projective corank in a complex square pencil

A pencil whose matrices have corank at most h at every projective point
can be made regular with simple spectrum using h pure corrections.
Each parameter of the generic corrected determinant occurs at most
linearly. Rank completion at each scalar rules out a repeated root, and
specialization preserves the degree and separability. If a contraction
already has rank at most floor(n/2), split it off directly. These two
cases give the required bound for every square pencil.

The original proof of this step is credited to ivillar. This proof
reuses the spectral decomposition from the registered parent reduction.
-/

namespace MaxCube.ParentPencil

open Matrix Polynomial

noncomputable abbrev penPoly {n : Type*} [Fintype n] [DecidableEq n] (U V : Matrix n n ℂ) : ℂ[X] :=
  ((X : ℂ[X]) • U.map C + V.map C).det

abbrev Good {n : Type*} [Fintype n] [DecidableEq n] (U V : Matrix n n ℂ) : Prop :=
  U.det ≠ 0 ∧ (penPoly U V).Separable

end MaxCube.ParentPencil

namespace MaxCube.Multiaffine

/-- Each perturbation variable occurs at most linearly. A square divisor can
therefore contain none of those variables. -/
theorem constant_of_square_dvd {σ R : Type*} [CommSemiring R] [NoZeroDivisors R]
    (F G : MvPolynomial σ R) (hF : F≠0) (multi : ∀ i : σ, F.degreeOf i≤1)
    (divides : G*G ∣ F) : G=MvPolynomial.C (G.coeff 0) := by
  classical
  obtain ⟨H,eq⟩ := divides
  have nzG : G≠0 := by rintro rfl; simp [eq] at hF
  have nzH : H≠0 := by rintro rfl; simp [eq] at hF
  have zero (i : σ) : G.degreeOf i=0 := by
    have h := multi i
    rw [eq,MvPolynomial.degreeOf_mul_eq (mul_ne_zero nzG nzG) nzH,
      MvPolynomial.degreeOf_mul_eq nzG nzG] at h
    omega
  apply MvPolynomial.vars_eq_empty_iff_eq_C.mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  exact fun i hin => (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hin) (zero i)

/-- A common square divisor of the coefficients is the only obstruction to
squarefreeness of a multiaffine polynomial over a domain. -/
theorem squarefree_of_scalar_squares {σ R : Type*} [CommSemiring R] [NoZeroDivisors R]
    (F : MvPolynomial σ R) (hF : F≠0) (multi : ∀ i : σ, F.degreeOf i≤1)
    (scalars : ∀ p : R, (∀ d : σ →₀ ℕ, p^2 ∣ F.coeff d) → IsUnit p) : Squarefree F := by
  classical
  intro G div
  have constant := constant_of_square_dvd F G hF multi div
  obtain ⟨H,eq⟩ := div
  let p := G.coeff 0
  have product : F=MvPolynomial.C (p^2)*H := by
    change F=MvPolynomial.C ((G.coeff 0)^2)*H
    calc
      F=G*G*H := eq
      _=(MvPolynomial.C (G.coeff 0)*MvPolynomial.C (G.coeff 0))*H :=
        congrArg (fun t => t*t*H) constant
      _=_ := by rw [map_pow,pow_two]
  have coefficients (d : σ →₀ ℕ) : p^2 ∣ F.coeff d :=
    ⟨H.coeff d,by rw [product,MvPolynomial.coeff_C_mul]⟩
  rw [constant]
  exact (scalars p coefficients).map MvPolynomial.C

/-- Over an algebraically closed field, test the coefficients for a squared
linear factor at each scalar point of the pencil. -/
theorem squarefree_of_coefficients {σ K : Type*} [Field K] [IsAlgClosed K]
    (F : MvPolynomial σ (Polynomial K)) (hF : F≠0) (multi : ∀ i : σ, F.degreeOf i≤1)
    (roots : ∀ a : K, ∃ d : σ →₀ ℕ, ¬(Polynomial.X-Polynomial.C a)^2 ∣ F.coeff d) :
    Squarefree F := by
  apply squarefree_of_scalar_squares F hF multi
  intro p all
  by_contra not_unit
  have degree : p.degree ≠ 0 := fun h => not_unit (Polynomial.isUnit_iff_degree_eq_zero.mpr h)
  obtain ⟨a,ha⟩ := IsAlgClosed.exists_root p degree
  obtain ⟨d,ndvd⟩ := roots a
  exact ndvd ((pow_dvd_pow_of_dvd (Polynomial.dvd_iff_isRoot.mpr ha) 2).trans (all d))

/-- A nonvanishing cofactor supplies a coefficient test even at the origin,
where the universal update contributes a single factor X. -/
theorem not_sq_dvd_X_mul {K : Type*} [Field K] (a : K) (p : Polynomial K) (hp : p.eval a≠0) :
    ¬(Polynomial.X-Polynomial.C a)^2 ∣ Polynomial.X*p := by
  rintro ⟨q,hq⟩
  by_cases zero : a=0
  · subst a
    simp only [Polynomial.C_0,sub_zero,pow_two,mul_assoc] at hq
    have h := mul_left_cancel₀ (Polynomial.X_ne_zero (R:=K)) hq
    apply hp
    rw [h,Polynomial.eval_mul,Polynomial.eval_X,zero_mul]
  · have he := congrArg (Polynomial.eval a) hq
    simp [zero,hp] at he

theorem squarefree_of_X_cofactors {σ K : Type*} [Field K] [IsAlgClosed K]
    (F : MvPolynomial σ (Polynomial K)) (multi : ∀ i : σ, F.degreeOf i≤1)
    (cofactor : ∀ a : K, ∃ (d : σ →₀ ℕ) (p : Polynomial K),
      F.coeff d=Polynomial.X*p ∧ p.eval a≠0) : Squarefree F := by
  have roots (a : K) : ∃ d : σ →₀ ℕ, ¬(Polynomial.X-Polynomial.C a)^2 ∣ F.coeff d := by
    obtain ⟨d,p,coeff,nonzero⟩ := cofactor a
    exact ⟨d,coeff ▸ not_sq_dvd_X_mul a p nonzero⟩
  apply squarefree_of_coefficients F _ multi roots
  rintro rfl
  obtain ⟨d,ndvd⟩ := roots 0
  exact ndvd (by simp)

end MaxCube.Multiaffine

namespace MaxCube.SquarefreeSpecialize

/-- Localization preserves radical elements, since it commutes with the radical of a principal ideal. -/
private lemma radical_localization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] {f : R} (hf : IsRadical f) : IsRadical (algebraMap R S f) := by
  let J : Ideal R := Ideal.span {f}
  have hJ : J.IsRadical := isRadical_iff_span_singleton.mp hf
  have hmap : J.map (algebraMap R S) = Ideal.span {algebraMap R S f} := by
    rw [show J=Ideal.span {f} from rfl,Ideal.map_span,Set.image_singleton]
  apply isRadical_iff_span_singleton.mpr
  rw [← hmap]
  apply Ideal.radical_eq_iff.mp
  rw [← IsLocalization.map_radical M S,hJ.radical]

/-- Parameter-only factors become units in the coefficient fraction field. -/
private lemma fraction_separable {σ : Type*} (G : Polynomial (MvPolynomial σ ℂ)) (hs : Squarefree G) :
    (G.map (algebraMap (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ)))).Separable := by
  classical
  let R := MvPolynomial σ ℂ
  let K := FractionRing R
  let A := Polynomial R
  let S := Polynomial K
  let _ : Algebra A S := Polynomial.algebra R K
  let L := (nonZeroDivisors R).map (Polynomial.C : R →+* A)
  let _ : IsLocalization L S := Polynomial.isLocalization (nonZeroDivisors R) K
  let φ := algebraMap R K
  have inj : Function.Injective φ := IsFractionRing.injective R K
  have hn : G.map φ ≠ 0 := by
    intro hz
    exact hs.ne_zero ((Polynomial.map_injective φ inj) (hz.trans (Polynomial.map_zero φ).symm))
  have hr : IsRadical (algebraMap A S G) := radical_localization L hs.isRadical
  exact PerfectField.separable_iff_squarefree.mpr (hr.squarefree hn)

private lemma eval_resultant {R S : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [CommRing S] [IsDomain S] [CharZero S] (G : Polynomial R) (φ : R →+* S)
    (hd : (G.map φ).natDegree=G.natDegree) :
    φ (G.resultant G.derivative) = (G.map φ).resultant (G.map φ).derivative := by
  have hder : (G.map φ).derivative.natDegree = G.derivative.natDegree := by simp only [Polynomial.natDegree_derivative,hd]
  change φ (G.resultant G.derivative G.natDegree G.derivative.natDegree) =
    (G.map φ).resultant (G.map φ).derivative (G.map φ).natDegree (G.map φ).derivative.natDegree
  rw [hd,hder,Polynomial.derivative_map,Polynomial.resultant_map_map]

/-- A squarefree univariate polynomial in algebraically independent parameters over the complex
numbers admits a complex specialization preserving degree and separability. -/
lemma specialize {σ : Type*} (G : Polynomial (MvPolynomial σ ℂ)) (hs : Squarefree G) :
    ∃ v : σ → ℂ, (G.map (MvPolynomial.eval v)).natDegree=G.natDegree ∧
      (G.map (MvPolynomial.eval v)).Separable := by
  classical
  let R := MvPolynomial σ ℂ
  let K := FractionRing R
  let φ := algebraMap R K
  have inj : Function.Injective φ := IsFractionRing.injective R K
  have hr : G.resultant G.derivative ≠ 0 := by
    intro hz
    have hd := Polynomial.natDegree_map_eq_of_injective (p:=G) inj
    have h := eval_resultant G φ hd
    rw [hz,map_zero] at h
    exact Polynomial.resultant_ne_zero _ _ (fraction_separable G hs) h.symm
  have hp : G.leadingCoeff * G.resultant G.derivative ≠ 0 := mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hs.ne_zero) hr
  obtain ⟨v,hv⟩ : ∃ v : σ → ℂ, MvPolynomial.eval v (G.leadingCoeff*G.resultant G.derivative) ≠ 0 := by
    by_contra! H
    apply hp
    apply MvPolynomial.funext
    intro v
    simpa only [map_zero] using H v
  rw [map_mul] at hv
  have hl := (mul_ne_zero_iff.mp hv).1
  have hd := Polynomial.natDegree_map_of_leadingCoeff_ne_zero (MvPolynomial.eval v) hl
  refine ⟨v,hd,?_⟩
  change IsCoprime (G.map (MvPolynomial.eval v)) (G.map (MvPolynomial.eval v)).derivative
  by_contra hbad
  have hn : G.map (MvPolynomial.eval v) ≠ 0 := by
    intro hz
    have hm := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (MvPolynomial.eval v) hl
    rw [hz,Polynomial.leadingCoeff_zero] at hm
    exact hl hm.symm
  have hb := Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hn,hbad⟩
  exact (mul_ne_zero_iff.mp hv).2 ((eval_resultant G (MvPolynomial.eval v) hd).trans hb)

end MaxCube.SquarefreeSpecialize

namespace MaxCube.SquarefreeSpecialize

/-- A globally squarefree polynomial in the perturbations and the pencil variable has
an evaluation of the perturbations that preserves its degree in the pencil variable
and has no repeated roots. -/
lemma of_mv {σ : Type*} (F : MvPolynomial σ (Polynomial ℂ)) (hF : Squarefree F) {n : ℕ}
    (hn : (MvPolynomial.eval₂Hom (Polynomial.mapRingHom (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ))
      (fun i : σ => Polynomial.C (MvPolynomial.X i : MvPolynomial σ ℂ)) F).natDegree=n) :
    ∃ v : σ → ℂ, (MvPolynomial.eval (fun i => Polynomial.C (v i)) F).natDegree=n ∧
      (MvPolynomial.eval (fun i => Polynomial.C (v i)) F).Separable := by
  classical
  let R := MvPolynomial σ ℂ
  let β : MvPolynomial σ (Polynomial ℂ) →+* Polynomial R :=
    MvPolynomial.eval₂Hom (Polynomial.mapRingHom (MvPolynomial.C : ℂ →+* R))
      (fun i => Polynomial.C (MvPolynomial.X i : R))
  let ψ : Polynomial R →+* MvPolynomial σ (Polynomial ℂ) :=
    Polynomial.eval₂RingHom (MvPolynomial.map (Polynomial.C : ℂ →+* Polynomial ℂ)) (MvPolynomial.C Polynomial.X)
  have leftC : ψ.comp (Polynomial.mapRingHom (MvPolynomial.C : ℂ →+* R)) = MvPolynomial.C := by
    apply Polynomial.ringHom_ext
    · intro z; simp [ψ]; exact MvPolynomial.map_C _ _
    · simp [ψ]
  have left : ψ.comp β=RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simpa only [RingHom.comp_apply,β,MvPolynomial.eval₂Hom_C,RingHom.id_apply] using DFunLike.congr_fun leftC z
    · intro i; simp [β,ψ]; exact MvPolynomial.map_X _ _
  have rightC : β.comp (MvPolynomial.map (Polynomial.C : ℂ →+* Polynomial ℂ)) = Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro z; simp [β]
    · intro i; simp [β]
  have right : β.comp ψ=RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro z
      simpa [ψ] using DFunLike.congr_fun rightC z
    · simp [β,ψ]
  have hs : Squarefree (β F) := by
    intro h hh
    have hi : ψ (β F)=F := DFunLike.congr_fun left F
    have hd : ψ h * ψ h ∣ F := by simpa only [map_mul,hi] using! map_dvd ψ hh
    have hu := (hF (ψ h) hd).map β
    exact (show β (ψ h)=h from DFunLike.congr_fun right h) ▸ hu
  obtain ⟨v,hd,hsep⟩ := specialize (β F) hs
  have base : (MvPolynomial.eval v).comp (MvPolynomial.C : ℂ →+* R) = RingHom.id ℂ := by ext z; simp
  have comm : (Polynomial.mapRingHom (MvPolynomial.eval v)).comp β = MvPolynomial.eval (fun i => Polynomial.C (v i)) := by
    apply MvPolynomial.ringHom_ext
    · intro z; simp [β,base]
    · intro i; simp [β]
  have he : (β F).map (MvPolynomial.eval v) = MvPolynomial.eval (fun i => Polynomial.C (v i)) F :=
    DFunLike.congr_fun comm F
  exact ⟨v,he ▸ hd.trans hn,he ▸ hsep⟩

end MaxCube.SquarefreeSpecialize

namespace MaxCube.EvenRepair

open Polynomial

/-- A multiaffine family of scalar polynomials is squarefree when its
parameters can remove every prescribed scalar root. -/
lemma squarefree_of_regular_fibres {σ : Type*}
    (F : MvPolynomial σ (Polynomial ℂ)) (multi : ∀ i, F.degreeOf i ≤ 1)
    (regular : ∀ t : ℂ, ∃ s : σ → ℂ, (MvPolynomial.eval (fun i => C (s i)) F).eval t ≠ 0) :
    Squarefree F := by
  classical
  have hn : F ≠ 0 := by
    rintro rfl
    obtain ⟨s,h⟩ := regular 0
    simp at h
  apply Multiaffine.squarefree_of_coefficients F hn multi
  intro t
  by_contra! all
  obtain ⟨s,nz⟩ := regular t
  have divides : (X-C t)^2 ∣ MvPolynomial.eval (fun i => C (s i)) F := by
    rw [MvPolynomial.eval_eq]
    exact Finset.dvd_sum (fun m _ => dvd_mul_of_dvd_left (all m) _)
  obtain ⟨p,eq⟩ := divides
  apply nz
  rw [eq]
  simp

/-- Determinants of the affine pencil specialize to the ordinary scalar
determinant, including for an empty matrix. -/
lemma eval_det_pencil {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    (((X : ℂ[X]) • A.map C - B.map C).det).eval t = (t • A - B).det := by
  change evalRingHom t _ = _
  rw [RingHom.map_det,RingHom.mapMatrix_apply]
  congr 1
  ext i j
  change (X * C (A i j) - C (B i j)).eval t = t * A i j - B i j
  simp only [eval_sub,eval_mul,eval_X,eval_C]

end MaxCube.EvenRepair

namespace MaxCube.DetUpdate

/-- The rank-one determinant identity, without any invertibility hypothesis.
After replacing row r by v, adding multiples of v to the other rows preserves
the determinant. Multilinearity in row r then gives its cofactor contribution. -/
theorem det_add_outer {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (u v : n → R) :
    (A + Matrix.vecMulVec u v).det = A.det + ∑ i,∑ j, u i*v j*A.adjugate j i := by
  classical
  let mat (s : Finset n) : Matrix n n R := fun i j => if i∈s then A i j+u i*v j else A i j
  have empty : mat ∅=A := by ext i j; simp [mat]
  have insertRow (s : Finset n) (i : n) (hi : i∉s) :
      mat (insert i s) = (mat s).updateRow i (mat s i + u i • v) := by
    ext j k
    by_cases hj : j=i
    · subst j
      rw [Matrix.updateRow_self]
      simp [mat,hi]
    · rw [Matrix.updateRow_ne hj]
      simp [mat,hj]
  have clear (r : n) (s : Finset n) (hr : r∉s) :
      ((mat s).updateRow r v).det = (A.updateRow r v).det := by
    induction s using Finset.induction_on with
    | empty => rw [empty]
    | @insert i s hi ih =>
      have hir : i≠r := by intro e; exact hr (e ▸ Finset.mem_insert_self _ _)
      have hrs : r∉s := fun h => hr (Finset.mem_insert_of_mem h)
      let M := (mat s).updateRow r v
      have swap : (mat (insert i s)).updateRow r v = M.updateRow i (M i+u i • M r) := by
        rw [insertRow s i hi]
        ext j k
        by_cases hj : j=i
        · subst j
          simp [M,hir]
        · by_cases h' : j=r
          · subst j
            simp [M,Ne.symm hir]
          · simp [M,hj,h']
      rw [swap,Matrix.det_updateRow_add_smul_self M hir,ih hrs]
  have cofactor (i : n) : (A.updateRow i v).det = ∑ j,v j*A.adjugate j i := by
    rw [Matrix.det_eq_sum_mul_adjugate_row (A.updateRow i v) i]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.updateRow_self,Matrix.adjugate_apply,Matrix.adjugate_apply]
    congr 2
    ext k l
    by_cases hk : k=i <;> simp [hk]
  have expansion (s : Finset n) : (mat s).det = A.det+∑ i∈s,∑ j,u i*v j*A.adjugate j i := by
    induction s using Finset.induction_on with
    | empty => simp [empty]
    | @insert i s hi ih =>
      rw [insertRow s i hi,Matrix.det_updateRow_add,Matrix.updateRow_eq_self,Matrix.det_updateRow_smul,
        clear i s hi,cofactor,ih,Finset.sum_insert hi,Finset.mul_sum]
      simp only [mul_assoc]
      abel
  have all : mat Finset.univ=A+Matrix.vecMulVec u v := by ext i j; simp [mat,Matrix.vecMulVec_apply]
  rw [← all]
  exact expansion Finset.univ

end MaxCube.DetUpdate

namespace MaxCube.MultiCorrection

abbrev Slot (n : ℕ) := Fin 2 ⊕ (Fin n ⊕ Fin n)
abbrev Param (n h : ℕ) := Fin h × Slot n

/-- Each direction has independent slope and constant parameters and two independent vectors. -/
def pack {n h : ℕ} {S : Type*} (a b : Fin h → S) (u v : Fin h → Fin n → S) : Param n h → S
  | (l,.inl j) => if j=0 then a l else b l
  | (l,.inr (.inl i)) => u l i
  | (l,.inr (.inr i)) => v l i

lemma pack_components {n h : ℕ} {S : Type*} (s : Param n h → S) :
    pack (fun l => s (l,.inl 0)) (fun l => s (l,.inl 1))
      (fun l i => s (l,.inr (.inl i))) (fun l i => s (l,.inr (.inr i))) = s := by
  funext p
  rcases p with ⟨l,j|i|i⟩
  · fin_cases j <;> rfl
  · rfl
  · rfl

def headMatrix {n : ℕ} {J S : Type*} [Fintype J] [CommRing S]
    (A : Matrix (Fin n) (Fin n) S) (s : J × Slot n → S) :=
  A + ∑ l, s (l,.inl 0) • Matrix.vecMulVec (fun i => s (l,.inr (.inl i))) (fun j => s (l,.inr (.inr j)))

def tailMatrix {n : ℕ} {J S : Type*} [Fintype J] [CommRing S]
    (B : Matrix (Fin n) (Fin n) S) (s : J × Slot n → S) :=
  B - ∑ l, s (l,.inl 1) • Matrix.vecMulVec (fun i => s (l,.inr (.inl i))) (fun j => s (l,.inr (.inr j)))

lemma head_pack {n h : ℕ} {S : Type*} [CommRing S] (A : Matrix (Fin n) (Fin n) S)
    (a b : Fin h → S) (u v : Fin h → Fin n → S) :
    headMatrix A (pack a b u v) = A + ∑ l, a l • Matrix.vecMulVec (u l) (v l) := rfl

lemma tail_pack {n h : ℕ} {S : Type*} [CommRing S] (B : Matrix (Fin n) (Fin n) S)
    (a b : Fin h → S) (u v : Fin h → Fin n → S) :
    tailMatrix B (pack a b u v) = B - ∑ l, b l • Matrix.vecMulVec (u l) (v l) := rfl

private def family {n : ℕ} {J S : Type*} [Fintype J] [CommRing S] (t : S)
    (A B : Matrix (Fin n) (Fin n) S) (s : J × Slot n → S) : Matrix (Fin n) (Fin n) S := fun i j =>
  t*A i j - B i j + ∑ l, (t*s (l,.inl 0)+s (l,.inl 1))*s (l,.inr (.inl i))*s (l,.inr (.inr j))

/-- The universal corrected determinant of `tA-B+Σ(taᵢ+bᵢ)uᵢvᵢᵀ`. -/
noncomputable def F {n : ℕ} (h : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) : MvPolynomial (Param n h) (Polynomial ℂ) :=
  let ι := (MvPolynomial.C : Polynomial ℂ →+* MvPolynomial (Param n h) (Polynomial ℂ)).comp Polynomial.C
  (family (MvPolynomial.C Polynomial.X) (A.map ι) (B.map ι) (MvPolynomial.X : Param n h → _)).det

private lemma family_image {n h : ℕ} {S : Type*} [CommRing S] (φ : ℂ →+* S)
    (A B : Matrix (Fin n) (Fin n) ℂ) (s : Param n h → S)
    (ψ : MvPolynomial (Param n h) (Polynomial ℂ) →+* Polynomial S)
    (hc : ∀ c : Polynomial ℂ, ψ (MvPolynomial.C c)=c.map φ)
    (hx : ∀ i : Param n h, ψ (MvPolynomial.X i)=Polynomial.C (s i)) :
    ψ (F h A B) = ((Polynomial.X : Polynomial S) • (headMatrix (A.map φ) s).map Polynomial.C -
      (tailMatrix (B.map φ) s).map Polynomial.C).det := by
  classical
  rw [F,RingHom.map_det,RingHom.mapMatrix_apply]
  congr 1
  apply Matrix.ext
  intro i j
  simp only [family,headMatrix,tailMatrix,Matrix.sub_apply,Matrix.smul_apply,Matrix.map_apply,Matrix.add_apply,
    Matrix.sum_apply,Matrix.vecMulVec_apply,smul_eq_mul,RingHom.comp_apply,map_sub,map_sum,map_add,map_mul,hc,hx,
    Polynomial.map_X,Polynomial.map_C,add_mul,Finset.sum_add_distrib,Finset.mul_sum,mul_add,mul_assoc]
  ring

lemma specialize_F {n : ℕ} (h : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) (s : Param n h → ℂ) :
    MvPolynomial.eval (fun i => Polynomial.C (s i)) (F h A B) =
      ((Polynomial.X : Polynomial ℂ) • (headMatrix A s).map Polynomial.C -
        (tailMatrix B s).map Polynomial.C).det := by
  simpa using family_image (RingHom.id ℂ) A B s (MvPolynomial.eval fun i => Polynomial.C (s i))
    (fun c => by simp) (fun i => MvPolynomial.eval_X i)

/-- Evaluation at both a scalar point and a choice of correction factors gives the ordinary matrix determinant. -/
lemma specialize_at {n : ℕ} (h : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) (s : Param n h → ℂ) (t : ℂ) :
    Polynomial.eval t (MvPolynomial.eval (fun i => Polynomial.C (s i)) (F h A B)) =
      (t • headMatrix A s - tailMatrix B s).det := by
  rw [specialize_F]
  change (Polynomial.evalRingHom t) ((Polynomial.X : Polynomial ℂ) • (headMatrix A s).map Polynomial.C -
    (tailMatrix B s).map Polynomial.C).det = _
  rw [RingHom.map_det,RingHom.mapMatrix_apply]
  congr 1
  ext i j
  simp [Matrix.map_apply]
  exact mul_comm _ _

/-- Complete coefficient rings can also be substituted for the correction parameters. -/
private lemma swapped {n h : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    let R := MvPolynomial (Param n h) ℂ
    let φ : ℂ →+* R := MvPolynomial.C
    let β : MvPolynomial (Param n h) (Polynomial ℂ) →+* Polynomial R :=
      MvPolynomial.eval₂Hom (Polynomial.mapRingHom φ) (fun i => Polynomial.C (MvPolynomial.X i : R))
    let H := headMatrix (A.map φ) (MvPolynomial.X : Param n h → R)
    let T := tailMatrix (B.map φ) (MvPolynomial.X : Param n h → R)
    β (F h A B) = ((Polynomial.X : Polynomial R) • H.map Polynomial.C + (-T).map Polynomial.C).det := by
  intro R φ β H T
  have h := family_image φ A B (MvPolynomial.X : Param n h → R) β
    (fun c => MvPolynomial.eval₂Hom_C _ _ c) (fun i => MvPolynomial.eval₂Hom_X' _ _ i)
  rw [h]
  congr 1
  apply Matrix.ext
  intro i j
  simp [H,T,sub_eq_add_neg]

lemma swapped_degree_le {n : ℕ} (h : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    (MvPolynomial.eval₂Hom (Polynomial.mapRingHom (MvPolynomial.C : ℂ →+* MvPolynomial (Param n h) ℂ))
      (fun i : Param n h => Polynomial.C (MvPolynomial.X i : MvPolynomial (Param n h) ℂ)) (F h A B)).natDegree ≤ n := by
  rw [swapped A B]
  apply (Polynomial.natDegree_det_X_add_C_le _ _).trans
  simp

lemma swapped_degree {n : ℕ} (h : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) (s : Param n h → ℂ)
    (hs : (headMatrix A s).det ≠ 0) :
    (MvPolynomial.eval₂Hom (Polynomial.mapRingHom (MvPolynomial.C : ℂ →+* MvPolynomial (Param n h) ℂ))
      (fun i : Param n h => Polynomial.C (MvPolynomial.X i : MvPolynomial (Param n h) ℂ)) (F h A B)).natDegree=n := by
  classical
  let R := MvPolynomial (Param n h) ℂ
  let φ : ℂ →+* R := MvPolynomial.C
  let H := headMatrix (A.map φ) (MvPolynomial.X : Param n h → R)
  let T := tailMatrix (B.map φ) (MvPolynomial.X : Param n h → R)
  have hH : H.map (MvPolynomial.eval s) = headMatrix A s := by
    ext i j
    simp [H,φ,headMatrix,Matrix.map_apply,Matrix.sum_apply,Matrix.vecMulVec_apply]
    exact MvPolynomial.eval_C _
  have hn : H.det≠0 := by
    intro hz
    apply hs
    have hm : MvPolynomial.eval s H.det = (H.map (MvPolynomial.eval s)).det := (MvPolynomial.eval s).map_det H
    simpa only [hz,map_zero,hH] using hm.symm
  apply le_antisymm (swapped_degree_le h A B)
  rw [swapped A B]
  apply Polynomial.le_natDegree_of_ne_zero
  have hc : ((Polynomial.X : Polynomial R) • H.map Polynomial.C + (-T).map Polynomial.C).det.coeff n = H.det := by
    simpa only [Fintype.card_fin] using Polynomial.coeff_det_X_add_C_card H (-T)
  exact hc.trans_ne hn

end MaxCube.MultiCorrection

namespace MaxCube.MultiCorrection

private lemma correction_degree {n h : ℕ} (k : Fin h) (q : Slot n) (a : Fin 2) (i j : Fin n) :
    let z := MvPolynomial.X (R:=Polynomial ℂ) (σ:=Param n h)
    (z (k,.inl a)*z (k,.inr (.inl i))*z (k,.inr (.inr j))).degreeOf (k,q) ≤ 1 := by
  intro z
  apply (MvPolynomial.degreeOf_mul_le _ _ _).trans
  apply (Nat.add_le_add_right (MvPolynomial.degreeOf_mul_le _ _ _) _).trans
  rcases q with u|u|u <;> simp [z,MvPolynomial.degreeOf_X] <;> split <;> decide

private lemma rank_one_degree {σ S R : Type*} [CommRing S] [CommRing R] {n : ℕ} (q : σ)
    (ι : S →+* MvPolynomial σ R) (absent : ∀ f : S, (ι f).degreeOf q=0)
    (M : Matrix (Fin n) (Fin n) S) (U V : Fin n → MvPolynomial σ R)
    (small : ∀ i j, (U i*V j).degreeOf q ≤ 1) :
    ((M.map ι + Matrix.vecMulVec U V).det).degreeOf q ≤ 1 := by
  have det_degree : (M.map ι).det.degreeOf q=0 := by
    have hm : ι M.det=(M.map ι).det := ι.map_det M
    rw [←hm]
    exact absent _
  have adj_degree (i j : Fin n) : ((M.map ι).adjugate j i).degreeOf q=0 := by
    have mapped : M.adjugate.map ι = (M.map ι).adjugate := ι.map_adjugate M
    have entry : ι (M.adjugate j i) = (M.map ι).adjugate j i := congrFun (congrFun mapped j) i
    rw [←entry]
    exact absent _
  rw [MaxCube.DetUpdate.det_add_outer]
  apply (MvPolynomial.degreeOf_add_le _ _ _).trans
  apply max_le (det_degree.le.trans (by decide : 0≤1))
  apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro i _
  apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro j _
  have deg := MvPolynomial.degreeOf_mul_le q (U i*V j) ((M.map ι).adjugate j i)
  rw [adj_degree,add_zero] at deg
  exact deg.trans (small i j)

/-- Each parameter enters exactly one direction block. Removing that block leaves a matrix
independent of the parameter, and its correction is one outer product with multiaffine entries. -/
lemma degreeOf_le_one {n : ℕ} (h : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) (q : Param n h) :
    (F h A B).degreeOf q ≤ 1 := by
  classical
  rcases q with ⟨k,w⟩
  let E := Finset.univ.erase k
  let P := MvPolynomial (Param n h) (Polynomial ℂ)
  let S := MvPolynomial (E × Slot n) (Polynomial ℂ)
  let inc (v : E × Slot n) : Param n h := (v.1.val,v.2)
  let ι : S →+* P := (MvPolynomial.rename inc).toRingHom
  have absent (f : S) : (ι f).degreeOf (k,w)=0 := by
    by_contra hq
    have hmem := MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr hq
    obtain ⟨j,_,hj⟩ := MvPolynomial.mem_vars_rename inc f hmem
    exact (Finset.mem_erase.mp j.1.property).1 (congrArg Prod.fst hj)
  let c : ℂ →+* P := (MvPolynomial.C : Polynomial ℂ →+* P).comp Polynomial.C
  let d : ℂ →+* S := (MvPolynomial.C : Polynomial ℂ →+* S).comp Polynomial.C
  let T : P := MvPolynomial.C Polynomial.X
  let z : Param n h → P := MvPolynomial.X
  let M := family (MvPolynomial.C Polynomial.X) (A.map d) (B.map d) (MvPolynomial.X : E × Slot n → S)
  let term (i j : Fin n) (l : Fin h) := (T*z (l,.inl 0)+z (l,.inl 1))*z (l,.inr (.inl i))*z (l,.inr (.inr j))
  let base (i j : Fin n) := T*c (A i j)-c (B i j)
  have evalM (i j : Fin n) : ι (M i j)=base i j+∑ l ∈ E, term i j l := by
    calc
      _ = base i j + ∑ l : E, term i j l.val := by
        have hc (p : Polynomial ℂ) : ι (MvPolynomial.C p)=MvPolynomial.C p := MvPolynomial.rename_C _ p
        have hx (l : E) (t : Slot n) : ι (MvPolynomial.X (l,t))=MvPolynomial.X (l.val,t) :=
          MvPolynomial.rename_X inc (l,t)
        simp only [M,family,base,term,z,T,c,d,RingHom.comp_apply,Matrix.map_apply,map_add,map_sub,map_sum,map_mul,hc,hx]
      _ = _ := congrArg (fun U : P => base i j+U) (Finset.sum_attach E (term i j))
  let U (i : Fin n) := (T*z (k,.inl 0)+z (k,.inl 1))*z (k,.inr (.inl i))
  let V (j : Fin n) := z (k,.inr (.inr j))
  have split : F h A B = (M.map ι + Matrix.vecMulVec U V).det := by
    change (family T (A.map c) (B.map c) z).det = (M.map ι + Matrix.vecMulVec U V).det
    apply congrArg Matrix.det
    apply Matrix.ext
    intro i j
    change base i j + ∑ l, term i j l = ι (M i j) + U i*V j
    rw [evalM,add_assoc,← Finset.sum_erase_add Finset.univ (term i j) (Finset.mem_univ k)]
  rw [split]
  apply rank_one_degree (k,w) ι absent M U V
  intro i j
  have expand : U i*V j = T*(z (k,.inl 0)*z (k,.inr (.inl i))*z (k,.inr (.inr j))) +
      z (k,.inl 1)*z (k,.inr (.inl i))*z (k,.inr (.inr j)) := by dsimp only [U,V]; ring
  rw [expand]
  apply (MvPolynomial.degreeOf_add_le _ _ _).trans
  apply max_le _ (correction_degree k w 1 i j)
  exact (MvPolynomial.degreeOf_C_mul_le _ (k,w) Polynomial.X).trans (correction_degree k w 0 i j)

end MaxCube.MultiCorrection

namespace MaxCube.ScalarRepair

private lemma det_of_full {K : Type*} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (full : n≤M.rank) : M.det ≠ 0 := by
  have ons : Function.Surjective M.mulVecLin := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    change M.rank=Module.finrank K (Fin n → K)
    rw [Module.finrank_pi,Fintype.card_fin]
    exact le_antisymm (by simpa only [Fintype.card_fin] using M.rank_le_card_width) full
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det M).mp
    (Matrix.mulVec_surjective_iff_isUnit.mp ons))

/-- In a rank-deficient matrix one unit-entry update strictly enlarges
the column space. The coordinate is chosen outside the old column space,
and its column index meets a nonzero vector in the old kernel. -/
theorem raise_entry {K : Type*} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (small : M.rank<n) :
    ∃ i j : Fin n, M.rank < (M+Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1)).rank := by
  classical
  let old := LinearMap.range M.mulVecLin
  have proper : old≠⊤ := by
    intro top
    have hd : M.rank=n := calc
      M.rank = Module.finrank K old := rfl
      _ = n := by rw [top,finrank_top,Module.finrank_pi,Fintype.card_fin]
    omega
  obtain ⟨i,missing⟩ : ∃ i : Fin n, Pi.single i (1:K) ∉ old := by
    by_contra! all
    apply proper
    have incl : Submodule.span K (Set.range (Pi.basisFun K (Fin n))) ≤ old := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change (Pi.basisFun K (Fin n)) i ∈ old
      rw [Pi.basisFun_apply]
      exact all i
    rw [Module.Basis.span_eq] at incl
    exact top_unique incl
  obtain ⟨x,hx,nonzero⟩ : ∃ x : Fin n → K, M.mulVecLin x=0 ∧ x≠0 := by
    by_contra! none
    have inject : Function.Injective M.mulVecLin := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr none)
    exact proper (LinearMap.range_eq_top.mpr
      ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp inject))
  obtain ⟨j,hj⟩ : ∃ j, x j≠0 := by by_contra! all; exact nonzero (funext all)
  let e : Fin n → K := Pi.single i 1
  let N := M+Matrix.vecMulVec e (Pi.single j 1)
  let W := LinearMap.range N.mulVecLin
  have action (z : Fin n → K) : N.mulVec z=M.mulVec z+z j • e := by
    change (M+Matrix.vecMulVec e (Pi.single j 1)).mulVec z = _
    rw [Matrix.add_mulVec,Matrix.vecMulVec_mulVec,single_one_dotProduct]
    congr 1
    funext k
    exact mul_comm _ _
  have inserted : e ∈ W := by
    have scaled : x j • e ∈ W := by
      refine ⟨x,?_⟩
      change N.mulVec x = _
      rw [action,show M.mulVec x=0 from hx,zero_add]
    simpa only [←mul_smul,inv_mul_cancel₀ hj,one_smul] using W.smul_mem (x j)⁻¹ scaled
  have include_old : old≤W := by
    rintro _ ⟨z,rfl⟩
    have val : N.mulVec z ∈ W := ⟨z,rfl⟩
    have h := W.sub_mem val (W.smul_mem (z j) inserted)
    rwa [action,add_sub_cancel_right] at h
  have strict : old<W := lt_of_le_of_ne include_old (fun same => missing (same ▸ inserted))
  exact ⟨i,j,Submodule.finrank_lt_finrank_of_lt strict⟩

/-- A number of outer products at least the corank repairs a square
matrix over any field. A full-rank intermediate matrix uses zero padding. -/
theorem repair {K : Type*} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (h : ℕ) (capacity : n≤M.rank+h) :
    ∃ u v : Fin h → Fin n → K, (M+∑ i,Matrix.vecMulVec (u i) (v i)).det≠0 := by
  classical
  induction h generalizing M with
  | zero =>
    exact ⟨0,0,by simpa using det_of_full M (by omega)⟩
  | succ h ih =>
    by_cases full : n≤M.rank
    · exact ⟨0,0,by simpa using det_of_full M full⟩
    obtain ⟨i,j,better⟩ := raise_entry M (by omega)
    let a : Fin n → K := Pi.single i 1
    let b : Fin n → K := Pi.single j 1
    let N := M+Matrix.vecMulVec a b
    have next : n≤N.rank+h := by change n≤(M+Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1)).rank+h; omega
    obtain ⟨u,v,regular⟩ := ih N next
    refine ⟨Fin.cons a u,Fin.cons b v,?_⟩
    rw [Fin.sum_univ_succ]
    simpa only [Fin.cons_zero,Fin.cons_succ,←add_assoc] using regular

end MaxCube.ScalarRepair

namespace MaxCube.EvenRepair

open Polynomial MultiCorrection

/-- When every projective member of a square matrix pencil has nullity at
most h, h shared rank-one corrections give a regular simple-spectrum pencil. -/
theorem pencil {n h : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hinfty : n ≤ A.rank + h) (finite : ∀ t : ℂ, n ≤ (t • A - B).rank + h) :
    ∃ a b : Fin h → ℂ, ∃ u v : Fin h → Fin n → ℂ,
      let A' := A + ∑ i, a i • Matrix.vecMulVec (u i) (v i)
      let B' := B - ∑ i, b i • Matrix.vecMulVec (u i) (v i)
      let P := ((X : ℂ[X]) • A'.map C - B'.map C).det
      P.natDegree = n ∧ P.Separable := by
  classical
  have regular (t : ℂ) : ∃ s : Param n h → ℂ,
      (MvPolynomial.eval (fun i => C (s i)) (F h A B)).eval t ≠ 0 := by
    obtain ⟨u,v,fix⟩ := ScalarRepair.repair (t • A - B) h (finite t)
    refine ⟨pack (fun _ => 0) (fun _ => 1) u v,?_⟩
    rw [specialize_F,eval_det_pencil,head_pack,tail_pack]
    simp only [zero_smul,one_smul,Finset.sum_const_zero,add_zero]
    have eq : t • A - (B - ∑ i, Matrix.vecMulVec (u i) (v i)) =
        (t • A - B) + ∑ i, Matrix.vecMulVec (u i) (v i) := by abel
    rwa [eq]
  have square := squarefree_of_regular_fibres (F h A B) (degreeOf_le_one h A B) regular
  obtain ⟨u₀,v₀,atInfinity⟩ := ScalarRepair.repair A h hinfty
  let w := pack (fun _ => 1) (fun _ => 0) u₀ v₀
  have hw : (headMatrix A w).det ≠ 0 := by
    change (headMatrix A (pack (fun _ => 1) (fun _ => 0) u₀ v₀)).det ≠ 0
    rw [head_pack]
    simpa only [one_smul] using atInfinity
  obtain ⟨s,hs,hsep⟩ := SquarefreeSpecialize.of_mv (F h A B) square (swapped_degree h A B w hw)
  let a (k : Fin h) := s (k,.inl 0)
  let b (k : Fin h) := s (k,.inl 1)
  let u (k : Fin h) (i : Fin n) := s (k,.inr (.inl i))
  let v (k : Fin h) (j : Fin n) := s (k,.inr (.inr j))
  have eta : pack a b u v = s := pack_components s
  have identity := specialize_F h A B (pack a b u v)
  rw [head_pack,tail_pack,eta] at identity
  exact ⟨a,b,u,v,identity ▸ hs,identity ▸ hsep⟩

end MaxCube.EvenRepair

namespace MaxCube

/-- A bounded-rank matrix is a sum of that many outer products, including zero padding. -/
private lemma low_rank_coordinates {b c r : ℕ} (M : Matrix (Fin b) (Fin c) ℂ) (hr : M.rank ≤ r) :
    ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ, ∀ i j, M i j = ∑ t,y t i*z t j := by
  classical
  let V := LinearMap.range M.mulVecLin
  let basis : Module.Basis (Fin M.rank) ℂ V := Module.finBasis ℂ V
  let column (j : Fin c) : V := ⟨M.col j,Pi.single j 1,Matrix.mulVec_single_one M j⟩
  let u (t : Fin M.rank) (i : Fin b) := ((basis t : V) : Fin b → ℂ) i
  let v (t : Fin M.rank) (j : Fin c) := basis.repr (column j) t
  have hm (i : Fin b) (j : Fin c) : M i j=∑ t,u t i*v t j := by
    have hh := congrArg (fun w : V => (w : Fin b → ℂ) i) (basis.sum_repr (column j))
    change ((∑ t,basis.repr (column j) t • basis t : V) : Fin b → ℂ) i=M i j at hh
    simpa only [u,v,Submodule.coe_sum,Submodule.coe_smul_of_tower,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using hh.symm
  let e : Fin M.rank ⊕ Fin (r-M.rank) ≃ Fin r := Fintype.equivOfCardEq (by simp; omega)
  refine ⟨fun t => (e.symm t).elim u 0,fun t => (e.symm t).elim v 0,?_⟩
  intro i j
  let w (t : Fin M.rank ⊕ Fin (r-M.rank)) := (t.elim u 0) i*(t.elim v 0) j
  change M i j=∑ t : Fin r,w (e.symm t)
  rw [e.symm.sum_comp,Fintype.sum_sum_type]
  simpa [w] using hm i j


end MaxCube

namespace MaxCube.EvenSpectral

open Matrix Polynomial

/-- The top coefficient of a degree-`n` separable pencil gives a regular leading
slice. Negating the second slice matches the `MaxCube.ParentPencil.Good` convention. -/
theorem good_of_separable {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (degree : ((X : ℂ[X]) • A.map C - B.map C).det.natDegree = n)
    (separable : ((X : ℂ[X]) • A.map C - B.map C).det.Separable) :
    MaxCube.ParentPencil.Good A (-B) := by
  have neg_map : (-B).map (C : ℂ →+* ℂ[X]) = -(B.map C) := by ext i j; simp
  have coeff : ((X : ℂ[X]) • A.map C - B.map C).det.coeff n = A.det := by
    rw [sub_eq_add_neg, ← neg_map]
    simpa only [Fintype.card_fin] using coeff_det_X_add_C_card A (-B)
  refine ⟨?_,?_⟩
  · have nonzero := leadingCoeff_ne_zero.mpr separable.ne_zero
    rwa [← coeff_natDegree, degree, coeff] at nonzero
  · simpa only [MaxCube.ParentPencil.penPoly, neg_map, sub_eq_add_neg] using separable

private lemma factors_mul {n : ℕ} (x y : Fin n → Fin n → ℂ) :
    (Matrix.of fun i j => x j i) * (Matrix.of fun i j => y i j) =
      ∑ t, vecMulVec (x t) (y t) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]

private lemma factors_diagonal {n : ℕ} (x y : Fin n → Fin n → ℂ) (μ : Fin n → ℂ) :
    (Matrix.of fun i j => x j i) * diagonal μ * (Matrix.of fun i j => y i j) =
      ∑ t, μ t • vecMulVec (x t) (y t) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.sum_apply]
  simp only [Matrix.mul_diagonal, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Both slices use the same `n` pure matrices. Their left factors form the
columns of an invertible matrix and their right factors form the rows of one. -/
theorem common_factors {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (degree : ((X : ℂ[X]) • A.map C - B.map C).det.natDegree = n)
    (separable : ((X : ℂ[X]) • A.map C - B.map C).det.Separable) :
    ∃ x y : Fin n → Fin n → ℂ, ∃ μ : Fin n → ℂ,
      IsUnit (Matrix.of fun i j => x j i) ∧ IsUnit (Matrix.of fun i j => y i j) ∧
      A = ∑ t, vecMulVec (x t) (y t) ∧ B = ∑ t, μ t • vecMulVec (x t) (y t) := by
  have good := good_of_separable A B degree separable
  obtain ⟨x,y,c,ha,hb⟩ := OMA.R_Arxiv_0805_3777_cprank_le_of_square_slices_R1.nice_of_good A (-B) good
  have units : ((Matrix.of fun i j => x j i) * (Matrix.of fun i j => y i j)).det ≠ 0 := by
    rw [factors_mul, ← ha]
    exact good.1
  rw [Matrix.det_mul] at units
  obtain ⟨left,right⟩ := mul_ne_zero_iff.mp units
  refine ⟨x,y,fun t => -c t,(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr left),
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr right),ha,?_⟩
  simpa only [neg_neg, ← Finset.sum_neg_distrib, neg_smul] using congrArg Neg.neg hb

end MaxCube.EvenSpectral

namespace MaxCube.PencilCover

open Matrix

/-- Two matrices are diagonal in the same two bases after subtracting h
terms with shared left and right vectors and separate scalar weights. -/
def DiagonalPlus {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (h : ℕ) : Prop :=
  ∃ (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ)
    (u v : Fin h → Fin n → ℂ) (α β : Fin h → ℂ),
    IsUnit P ∧ IsUnit Q ∧
    A = P * diagonal a * Q + ∑ i, α i • vecMulVec (u i) (v i) ∧
    B = P * diagonal b * Q + ∑ i, β i • vecMulVec (u i) (v i)

private theorem diagonal_form {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ∃ P Q : Matrix (Fin n) (Fin n) ℂ, ∃ d : Fin n → ℂ,
      IsUnit P ∧ IsUnit Q ∧ M = P * diagonal d * Q := by
  obtain ⟨L,K,d,eq⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  have unit (S : List (Matrix.TransvectionStruct (Fin n) ℂ)) :
      IsUnit (S.map Matrix.TransvectionStruct.toMatrix).prod := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.TransvectionStruct.det_toMatrix_prod]
    exact isUnit_one
  exact ⟨_,_,d,unit L,unit K,eq⟩

private theorem rank_terms {n h : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hr : M.rank ≤ h) :
    ∃ u v : Fin h → Fin n → ℂ, M = ∑ i, vecMulVec (u i) (v i) := by
  obtain ⟨u,v,eq⟩ := MaxCube.low_rank_coordinates M hr
  refine ⟨u,v,?_⟩
  ext i j
  rw [Matrix.sum_apply]
  exact eq i j

theorem low_first {n h : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hr : A.rank ≤ h) :
    DiagonalPlus A B h := by
  obtain ⟨P,Q,d,hP,hQ,di⟩ := diagonal_form B
  obtain ⟨u,v,eq⟩ := rank_terms A hr
  refine ⟨P,Q,0,d,u,v,fun _ => 1,fun _ => 0,hP,hQ,?_,?_⟩
  · simpa using eq
  · simpa using di

theorem low_finite {n h : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (t : ℂ) (hr : (t • A - B).rank ≤ h) : DiagonalPlus A B h := by
  obtain ⟨P,Q,d,hP,hQ,di⟩ := diagonal_form A
  obtain ⟨u,v,eq⟩ := rank_terms (t • A - B) hr
  refine ⟨P,Q,d,t • d,u,v,fun _ => 0,fun _ => -1,hP,hQ,?_,?_⟩
  · simpa using di
  · rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul, ← di]
    simp only [neg_one_smul, Finset.sum_neg_distrib, ← eq]
    abel

/-- The span of n matched outer products is the common diagonal space. -/
theorem diagonal_of_factors {n : ℕ} (x y : Fin n → Fin n → ℂ) (d : Fin n → ℂ) :
    (Matrix.of fun i j => x j i) * diagonal d * (Matrix.of fun i j => y i j) =
      ∑ j, d j • vecMulVec (x j) (y j) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro l _
  rw [Matrix.mul_diagonal, Matrix.smul_apply]
  change x l i * d l * y l j = d l * (x l i * y l j)
  ring

end MaxCube.PencilCover

namespace MaxCube.PencilCover

open Matrix Polynomial

/-- Bounds on corank at finite points and infinity suffice to put the
whole pencil in common diagonal form up to h pure corrections. -/
theorem of_projective_corank {n h : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hinf : n ≤ A.rank + h) (hfin : ∀ t : ℂ, n ≤ (t • A-B).rank + h) :
    DiagonalPlus A B h := by
  classical
  obtain ⟨a,b,u,v,degree,sep⟩ := EvenRepair.pencil A B hinf hfin
  let U := A + ∑ i, a i • vecMulVec (u i) (v i)
  let V := B - ∑ i, b i • vecMulVec (u i) (v i)
  obtain ⟨x,y,μ,px,qy,hU,hV⟩ := EvenSpectral.common_factors U V degree sep
  refine ⟨Matrix.of (fun i j => x j i),Matrix.of (fun i j => y i j),1,μ,u,v,-a,b,px,qy,?_,?_⟩
  · rw [diagonal_of_factors]
    simp only [Pi.one_apply, one_smul, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, ← hU]
    change A = (A + _) + -_
    abel
  · rw [diagonal_of_factors, ← hV]
    change B = (B - _) + _
    abel

/-- Uniformly over all square complex pencils, at most floor(n/2)
additional pure terms suffice after a common diagonal change of bases. -/
theorem half {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : DiagonalPlus A B (n/2) := by
  by_cases low : A.rank ≤ n/2
  · exact low_first A B low
  by_cases finiteLow : ∃ t : ℂ, (t • A-B).rank ≤ n/2
  · obtain ⟨t,ht⟩ := finiteLow
    exact low_finite A B t ht
  · apply of_projective_corank A B (by omega)
    intro t
    have h : ¬ (t • A-B).rank ≤ n/2 := fun ht => finiteLow ⟨t,ht⟩
    omega

end MaxCube.PencilCover

theorem OMA.solution : OMA.R_Arxiv_0805_3777_cprank_le_of_square_slices_R1.H2 := by
  intro n A B _
  exact MaxCube.PencilCover.half A B
