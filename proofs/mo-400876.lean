import OMAStatements.S_mo_400876

/-!
Complete proof by @connoranderson, linked by statement PR #23905 and desk DONE #109681.
Pinned source: https://github.com/connoranderson/open-math-agents/blob/1b6dcc1e1e3720f53d76946852ebef8ca1c413dc/proofs/mo-400876.lean
The mathematical source is unchanged; this port adds attribution and current-checker validation.
Joseph Van Name previously factored the uniform matrix and proved an interior-density result:
https://mathoverflow.net/a/396795 and https://mathoverflow.net/a/398124.
Port and validation: @rodolfoquint.
-/

namespace OMA.S_mo_400876

open Finset Matrix

private noncomputable def meanVec {n : ℕ} (x : Fin (n+2) → ℝ) := (∑ i, x i)/(n+2:ℝ)

private noncomputable def expand (n : ℕ) : (Fin (n+1) → ℝ) →ₗ[ℝ] (Fin (n+2) → ℝ) where
  toFun v := Fin.cons (v 0+∑ j : Fin n,v j.succ)
    (Fin.cons (-v 0+∑ j : Fin n,v j.succ) (fun j => -2*v j.succ))
  map_add' u v := by
    ext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i <;> simp [sum_add_distrib] <;> ring
  map_smul' c v := by
    ext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i <;>
      simp [Finset.mul_sum,mul_add]; ring

private noncomputable def extract (n : ℕ) : (Fin (n+2) → ℝ) →ₗ[ℝ] (Fin (n+1) → ℝ) where
  toFun x := Fin.cons ((x 0-x (Fin.succ 0))/2) (fun j => (meanVec x-x j.succ.succ)/2)
  map_add' u v := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [meanVec,sum_add_distrib] <;> ring
  map_smul' c v := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [meanVec,← Finset.mul_sum] <;> ring

private lemma expand_mean (n : ℕ) (v : Fin (n+1) → ℝ) : meanVec (expand n v)=0 := by
  apply div_eq_zero_iff.mpr (Or.inl ?_)
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp [expand,← Finset.mul_sum]
  ring

private lemma extract_expand (n : ℕ) (v : Fin (n+1) → ℝ) : extract n (expand n v)=v := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [extract,expand]
  · simp only [extract,LinearMap.coe_mk,AddHom.coe_mk,Fin.cons_succ,expand_mean]
    simp [expand]

private lemma expand_extract (n : ℕ) (x : Fin (n+2) → ℝ) :
    expand n (extract n x) = fun i => x i-meanVec x := by
  have hsum : (∑ j : Fin n, (meanVec x - x j.succ.succ)/2) =
    (n*meanVec x-(∑ j : Fin n, x j.succ.succ))/2 := by
    rw [← Finset.sum_div,sum_sub_distrib]; simp
  have hmean : (n+2:ℝ)*meanVec x = x 0+x (Fin.succ 0)+∑ j : Fin n,x j.succ.succ := by
    unfold meanVec
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    field_simp
    ring
  ext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i <;>
    simp only [expand,extract,LinearMap.coe_mk,AddHom.coe_mk,Fin.cons_zero,Fin.cons_succ,hsum] <;> linarith

private lemma extract_const (n : ℕ) (c : ℝ) : extract n (fun _ => c) = 0 := by
  have hm : meanVec (n := n) (fun _ => c) = c := by
    simp [meanVec]
    field_simp
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [extract,hm]

private noncomputable def S (n : ℕ) := LinearMap.toMatrix' (expand n)
private noncomputable def R (n : ℕ) := LinearMap.toMatrix' (extract n)

private lemma uniform_vec (n : ℕ) (x : Fin (n+2) → ℝ) :
    uniform (n+2) *ᵥ x = fun _ => meanVec x := by
  ext i
  simp [mulVec,dotProduct,uniform,meanVec,Finset.sum_mul,div_eq_mul_inv,mul_comm]

private lemma RS (n : ℕ) : R n * S n = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  simp only [R,S,← Matrix.mulVec_mulVec,LinearMap.toMatrix'_mulVec,one_mulVec,extract_expand]

private lemma SR (n : ℕ) : S n * R n = 1-uniform (n+2) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  simp only [R,S,← Matrix.mulVec_mulVec,LinearMap.toMatrix'_mulVec,sub_mulVec,one_mulVec,
    expand_extract,uniform_vec]
  rfl

private lemma US (n : ℕ) : uniform (n+2) * S n = 0 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  simp only [S,← Matrix.mulVec_mulVec,LinearMap.toMatrix'_mulVec,uniform_vec,expand_mean,zero_mulVec]
  rfl

private lemma RU (n : ℕ) : R n * uniform (n+2) = 0 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  simp only [R,← Matrix.mulVec_mulVec,LinearMap.toMatrix'_mulVec,uniform_vec,extract_const,zero_mulVec]

end OMA.S_mo_400876
namespace OMA.S_mo_400876

open Matrix Finset

def Margins {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i, ∑ j, A i j=1) ∧ ∀ j, ∑ i, A i j=1

noncomputable def toBlock (n : ℕ) : Matrix (Fin (n+2)) (Fin (n+2)) ℝ →ₗ[ℝ]
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ where
  toFun A := R n * A * S n
  map_add' A B := by simp [Matrix.mul_add,Matrix.add_mul]
  map_smul' c A := by simp [Matrix.mul_smul,Matrix.smul_mul]

noncomputable def fromBlock (n : ℕ) (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Matrix (Fin (n+2)) (Fin (n+2)) ℝ := uniform (n+2) + S n * X * R n

lemma continuous_fromBlock (n : ℕ) : Continuous (fromBlock n) := by unfold fromBlock; fun_prop

private lemma margins_iff (n : ℕ) (A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) :
    Margins A ↔ A*uniform (n+2)=uniform (n+2) ∧ uniform (n+2)*A=uniform (n+2) := by
  let k : ℝ := ((n+2:ℕ):ℝ)⁻¹
  have hk : k≠0 := by dsimp [k]; positivity
  have hr (i j : Fin (n+2)) : (A*uniform (n+2)) i j = (∑ l,A i l)*k := by simp [k,uniform,mul_apply,sum_mul]
  have hc (i j : Fin (n+2)) : (uniform (n+2)*A) i j = k*(∑ l,A l j) := by simp [k,uniform,mul_apply,mul_sum]
  constructor
  · rintro ⟨h₁,h₂⟩
    constructor
    · ext i j; rw [hr,h₁,one_mul]; rfl
    · ext i j; rw [hc,h₂,mul_one]; rfl
  · rintro ⟨h₁,h₂⟩
    constructor
    · intro i
      apply mul_right_cancel₀ hk
      exact (hr i 0).symm.trans ((congrFun₂ h₁ i 0).trans (one_mul k).symm)
    · intro j
      apply mul_left_cancel₀ hk
      exact (hc 0 j).symm.trans ((congrFun₂ h₂ 0 j).trans (mul_one k).symm)

private lemma UU (n : ℕ) : uniform (n+2)*uniform (n+2)=uniform (n+2) := by
  apply ((margins_iff n _).mp ?_).1
  constructor <;> intro i <;> simp [uniform,show (n:ℝ)+2 ≠ 0 by positivity]

lemma fromBlock_margins (n : ℕ) (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : Margins (fromBlock n X) := by
  apply (margins_iff n _).mpr
  constructor
  · simp [fromBlock,Matrix.add_mul,Matrix.mul_assoc,UU,RU]
  · simp [fromBlock,Matrix.mul_add,← Matrix.mul_assoc,UU,US]

lemma toBlock_one (n : ℕ) : toBlock n 1 = 1 := by simp [toBlock,RS]
lemma toBlock_uniform (n : ℕ) : toBlock n (uniform (n+2)) = 0 := by simp [toBlock,RU]
lemma fromBlock_zero (n : ℕ) : fromBlock n 0 = uniform (n+2) := by simp [fromBlock]

lemma toBlock_fromBlock (n : ℕ) (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    toBlock n (fromBlock n X)=X := by
  change R n*(uniform (n+2)+S n*X*R n)*S n=X
  calc
    _ = R n*uniform (n+2)*S n + (R n*S n)*X*(R n*S n) := by
      rw [Matrix.mul_add,Matrix.add_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by simp [RU,RS]

lemma fromBlock_toBlock {n : ℕ} (A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (h : Margins A) :
    fromBlock n (toBlock n A)=A := by
  obtain ⟨h₁,h₂⟩ := (margins_iff n A).mp h
  change uniform (n+2)+S n*(R n*A*S n)*R n=A
  calc
    _ = uniform (n+2)+(S n*R n)*A*(S n*R n) := by simp only [Matrix.mul_assoc]
    _ = _ := by simp [SR,Matrix.sub_mul,Matrix.mul_sub,h₁,h₂,UU]

lemma toBlock_mul {n : ℕ} (A B : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (h : Margins A) :
    toBlock n (A*B)=toBlock n A * toBlock n B := by
  have h₁ := ((margins_iff n A).mp h).1
  symm
  change (R n*A*S n)*(R n*B*S n)=R n*(A*B)*S n
  calc
    _ = R n*(A*(S n*R n))*B*S n := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [SR,Matrix.mul_sub,Matrix.mul_sub]; simp [h₁,RU,Matrix.mul_assoc]

end OMA.S_mo_400876
namespace OMA.S_mo_400876

open Matrix Finset

lemma toBlock_swap (n : ℕ) :
    toBlock n ((Equiv.swap (0 : Fin (n+2)) 1).permMatrix ℝ) =
      Matrix.diagonal (fun i : Fin (n+1) => if i=0 then -1 else 1) := by
  let d (i : Fin (n+1)) : ℝ := if i=0 then -1 else 1
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  change (R n*(Equiv.swap (0 : Fin (n+2)) 1).permMatrix ℝ * S n) *ᵥ v=diagonal d *ᵥ v
  simp only [R,S,← Matrix.mulVec_mulVec,LinearMap.toMatrix'_mulVec,Matrix.permMatrix_mulVec]
  rw [← extract_expand n (diagonal d *ᵥ v)]
  congr 1
  let t := ∑ j : Fin n,v j.succ
  change (Matrix.vecCons (v 0+t) (Matrix.vecCons (-v 0+t) (fun j => -2*v j.succ))) ∘
    Equiv.swap 0 1 = _
  rw [Matrix.cons_cons_comp_swap_zero_one]
  ext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i <;>
    simp [expand,Matrix.mulVec_diagonal,d,t]

end OMA.S_mo_400876

namespace OMA.S_mo_400876
open Matrix Finset
noncomputable section

def SmallFactor {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∃ N : Matrix (Fin n) (Fin n) ℝ, N*N=0 ∧ (∀ i j, |N i j| ≤ 1) ∧ M=1+N) ∨
  (∃ i j : Fin n, M=(Equiv.swap i j).permMatrix ℝ) ∨
  (∃ (i : Fin n) (t : ℝ), |t|≤1 ∧ M=Matrix.diagonal (fun j => if j=i then t else 1))

end
end OMA.S_mo_400876

namespace OMA.S_mo_400876
open Matrix Finset
noncomputable section

private def colSp {n : ℕ} (u : Fin n → ℝ) (p : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun x y => if y=p then u x else 0

private def rowSp {n : ℕ} (p : Fin n) (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun x y => if x=p then u y else 0

private lemma colSp_mul {n} (u : Fin n → ℝ) (p : Fin n) (A : Matrix (Fin n) (Fin n) ℝ) (x y) :
    (colSp u p * A) x y = u x*A p y := by simp [Matrix.mul_apply,colSp,ite_mul]

private lemma mul_rowSp {n} (A : Matrix (Fin n) (Fin n) ℝ) (p : Fin n) (v : Fin n → ℝ) (x y) :
    (A * rowSp p v) x y = A x p*v y := by simp [Matrix.mul_apply,rowSp,mul_ite]

private lemma small_col {n} (u : Fin n → ℝ) (p : Fin n) (hp : u p=0) (hu : ∀ x, |u x|≤1) :
    SmallFactor (1+colSp u p) := by
  refine Or.inl ⟨_,?_,?_,rfl⟩
  · ext x y
    simp [colSp_mul,colSp,hp]
  · intro x y
    by_cases hy : y=p <;> simp [colSp,hy,hu]

private lemma small_row {n} (p : Fin n) (v : Fin n → ℝ) (hp : v p=0) (hv : ∀ x, |v x|≤1) :
    SmallFactor (1+rowSp p v) := by
  refine Or.inl ⟨_,?_,?_,rfl⟩
  · ext x y
    simp [mul_rowSp,rowSp,hp]
  · intro x y
    by_cases hx : x=p <;> simp [rowSp,hx,hv]

private lemma schur_factor {n} (B C : Matrix (Fin n) (Fin n) ℝ) (p : Fin n)
    (u v : Fin n → ℝ) (hup : u p=0) (hvp : v p=0)
    (hu : ∀ x, x≠p → u x*B p p=B x p) (hv : ∀ y, y≠p → B p p*v y=B p y)
    (hc : ∀ x y, C x y=if x=p ∨ y=p then (1 : Matrix (Fin n) (Fin n) ℝ) x y
                          else B x y-u x*B p y) :
    (1+colSp u p) * (Matrix.diagonal (fun j => if j=p then B p p else 1)*C) *
      (1+rowSp p v) = B := by
  ext x y
  rw [mul_add,Matrix.mul_one]
  simp only [Matrix.add_apply,mul_rowSp,add_mul,Matrix.one_mul,colSp_mul,Matrix.diagonal_mul,
    hc, Matrix.one_apply]
  by_cases hx : x=p <;> by_cases hy : y=p
  · subst x;subst y;simp [hup,hvp]
  · subst x;simp [hy,hup,hv y hy,Ne.symm hy]
  · subst y;simp [hx,hvp,hu x hx]
  · simp [hx,hy,Ne.symm hy]
    linear_combination u x * (hv y hy)

private lemma bounded_eliminate_on {n : ℕ} (S : Finset (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) (hδ : 0≤δ) (hl : δ * 2^S.card ≤ 1)
    (hin : ∀ x ∈ S, ∀ y ∈ S, |A x y|≤δ)
    (hout : ∀ x y, x∉S ∨ y∉S → A x y=(1 : Matrix (Fin n) (Fin n) ℝ) x y) :
    ∃ L : List (Matrix (Fin n) (Fin n) ℝ), L.length ≤ 4*S.card ∧
      (∀ M ∈ L, SmallFactor M) ∧ L.prod=A := by
  classical
  induction S using Finset.strongInductionOn generalizing A δ with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl|hne
    · have ha : A=1 := Matrix.ext fun x y => hout _ _ (Or.inl (by simp))
      exact ⟨[], by simp, by simp, by simp [ha]⟩
    obtain ⟨⟨p,q⟩,hpq,hm⟩ := (S ×ˢ S).exists_max_image (fun z => |A z.1 z.2|) (hne.product hne)
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
    let σ := Equiv.swap p q
    let B : Matrix (Fin n) (Fin n) ℝ := fun x y => A x (σ y)
    have hswap : ∀ y, σ y ∈ S ↔ y ∈ S := by
      intro y
      by_cases hy : y=p
      · subst y;simp [σ,hp,hq]
      by_cases hy' : y=q
      · subst y;simp [σ,hp,hq]
      simp [σ,Equiv.swap_apply_of_ne_of_ne hy hy']
    have houtB (x y) (hxy : x ∉ S ∨ y ∉ S) : B x y=(1 : Matrix (Fin n) (Fin n) ℝ) x y := by
      change A x (σ y)=_
      rw [hout _ _ (hxy.imp_right (fun h hs => h ((hswap _).mp hs)))]
      by_cases hy : y∈S
      · have hx := hxy.resolve_right (not_not.mpr hy)
        have h₁ : x≠σ y := fun e => hx (e ▸ (hswap _).mpr hy)
        have h₂ : x≠y := fun e => hx (e ▸ hy)
        simp [h₁,h₂]
      · have h₁ : y≠p := fun e => hy (e ▸ hp)
        have h₂ : y≠q := fun e => hy (e ▸ hq)
        have hyfix : σ y=y := Equiv.swap_apply_of_ne_of_ne h₁ h₂
        exact congrArg (fun z => (1 : Matrix (Fin n) (Fin n) ℝ) x z) hyfix
    have hinB (x) (hx : x∈S) (y) (hy : y∈S) : |B x y|≤δ := hin _ hx _ ((hswap _).mpr hy)
    have hmax (x) (hx : x∈S) (y) (hy : y∈S) : |B x y|≤|B p p| := by
      simpa only [B,σ,Equiv.swap_apply_left] using hm (x,σ y) (Finset.mem_product.mpr ⟨hx,(hswap _).mpr hy⟩)
    have hcol (x) (hx : x≠p) : |B x p|≤|B p p| := by
      by_cases hxS : x∈S
      · exact hmax _ hxS _ hp
      · simp [houtB _ _ (Or.inl hxS),hx]
    have hrow (y) (hy : y≠p) : |B p y|≤|B p p| := by
      by_cases hyS : y∈S
      · exact hmax _ hp _ hyS
      · simp [houtB _ _ (Or.inr hyS),Ne.symm hy]
    let u (x : Fin n) := if x=p then 0 else B x p/B p p
    let v (y : Fin n) := if y=p then 0 else B p y/B p p
    have divBound (z : ℝ) (h : |z| ≤ |B p p|) : |z/B p p| ≤ 1 := by
      by_cases hb : B p p=0
      · simp [hb]
      · rw [abs_div];exact (div_le_one (abs_pos.mpr hb)).mpr h
    have hcancel (z : ℝ) (h : |z| ≤ |B p p|) : z/B p p*B p p=z := by
      by_cases hb : B p p=0
      · have hz : z=0 := abs_nonpos_iff.mp (by simpa [hb] using h)
        simp [hz]
      · exact div_mul_cancel₀ z hb
    have hu (x) : |u x|≤1 := by
      by_cases hx : x=p
      · simp [u,hx]
      · simpa only [u,if_neg hx] using divBound _ (hcol _ hx)
    have hv (y) : |v y|≤1 := by
      by_cases hy : y=p
      · simp [v,hy]
      · simpa only [v,if_neg hy] using divBound _ (hrow _ hy)
    let C : Matrix (Fin n) (Fin n) ℝ := fun x y =>
      if x=p ∨ y=p then (1 : Matrix (Fin n) (Fin n) ℝ) x y else B x y-u x*B p y
    have hCout (x y) (hxy : x ∉ S.erase p ∨ y ∉ S.erase p) :
        C x y=(1 : Matrix (Fin n) (Fin n) ℝ) x y := by
      by_cases he : x=p ∨ y=p
      · simp [C,he]
      · obtain ⟨hx,hy⟩ := not_or.mp he
        have hxy : x∉S ∨ y∉S := hxy.imp (fun h hs => h (Finset.mem_erase.mpr ⟨hx,hs⟩))
          (fun h hs => h (Finset.mem_erase.mpr ⟨hy,hs⟩))
        rw [show C x y=B x y-u x*B p y from if_neg he,houtB _ _ hxy]
        rcases hxy with hxS|hyS
        · simp [u,houtB _ _ (Or.inl hxS),Matrix.one_apply,hx]
        · simp [houtB _ _ (Or.inr hyS),Ne.symm hy]
    have hCin (x) (hx : x ∈ S.erase p) (y) (hy : y ∈ S.erase p) : |C x y|≤δ*2 := by
      obtain ⟨hx,hxS⟩ := Finset.mem_erase.mp hx
      obtain ⟨hy,hyS⟩ := Finset.mem_erase.mp hy
      change |(if _ then _ else _)|≤_
      rw [if_neg (not_or.mpr ⟨hx,hy⟩)]
      calc _ ≤ |B x y| + |u x*B p y| := abs_sub _ _
           _ ≤ δ + 1*δ := add_le_add (hinB _ hxS _ hyS)
             (by rw [abs_mul];exact mul_le_mul (hu _) (hinB _ hp _ hyS) (abs_nonneg _) zero_le_one)
           _ = _ := by ring
    have hcard : (S.erase p).card+1=S.card := Finset.card_erase_add_one hp
    have hrec : (δ*2)*2^(S.erase p).card ≤ 1 := by
      rw [← hcard,pow_succ] at hl
      linarith
    obtain ⟨L,hL,good,prodL⟩ := ih (S.erase p) (Finset.erase_ssubset hp) C (δ*2)
      (by positivity) hrec hCin hCout
    let D := Matrix.diagonal (fun j => if j=p then B p p else 1)
    let P := σ.permMatrix ℝ
    have hD : SmallFactor D := by
      refine Or.inr (Or.inr ⟨p,_,(hinB _ hp _ hp).trans ?_,rfl⟩)
      calc δ = δ*1 := by ring
           _ ≤ δ*2^S.card := mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num)) hδ
           _ ≤ 1 := hl
    have hP : SmallFactor P := Or.inr (Or.inl ⟨p,q,rfl⟩)
    have hback : B * P=A := by
      change B * σ.toPEquiv.toMatrix=A
      rw [PEquiv.mul_toMatrix_toPEquiv]
      ext x y
      change A x (σ (σ.symm y)) = A x y
      rw [σ.apply_symm_apply]
    have he := schur_factor B C p u v (by simp [u]) (by simp [v])
      (fun x hx => by simpa [u,hx] using hcancel _ (hcol _ hx))
      (fun y hy => by simpa [v,hy,mul_comm] using hcancel _ (hrow _ hy)) (fun _ _ => rfl)
    refine ⟨(1+colSp u p)::D::(L++[1+rowSp p v,P]),?_,?_,?_⟩
    · simp only [List.length_cons,List.length_append,List.length_nil]; omega
    · intro M hM
      simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hM
      rcases hM with rfl|rfl|h|rfl|rfl
      · exact small_col _ _ (by simp [u]) hu
      · exact hD
      · exact good _ h
      · exact small_row _ _ (by simp [v]) hv
      · exact hP
    · simp only [List.prod_cons,List.prod_append,List.prod_nil,Matrix.mul_one,prodL]
      simpa only [Matrix.mul_assoc,D] using (congrArg (fun X => X*P) he).trans hback

lemma bounded_elimination (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ i j, |A i j| ≤ (2^n : ℝ)⁻¹) :
    ∃ L : List (Matrix (Fin n) (Fin n) ℝ), L.length ≤ 4*n ∧
      (∀ M ∈ L, SmallFactor M) ∧ L.prod=A := by
  simpa using bounded_eliminate_on Finset.univ A ((2^n : ℝ)⁻¹) (by positivity)
    (by simp) (by simpa using h) (by simp)

end
end OMA.S_mo_400876

namespace OMA.S_mo_400876
open Matrix
open scoped Matrix.Norms.Elementwise

private lemma nil_power {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) (hN : N*N=0) (s : ℝ) (k : ℕ) :
    (1+s • N)^k = 1+((k:ℝ)*s) • N := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ,ih,add_mul,mul_add,one_mul,mul_one,smul_mul_smul_comm,hN,smul_zero,
      add_zero,add_assoc,←add_smul,Nat.cast_succ]


private lemma scaled_nilpotents {n : ℕ} (S : Submonoid (Matrix (Fin n) (Fin n) ℝ))
    {c : ℝ} (hc : 0<c) (h : c • (1 : Matrix (Fin n) (Fin n) ℝ) ∈ interior (S : Set _)) :
    ∃ g : ℝ, 0<g ∧ ∀ N : Matrix (Fin n) (Fin n) ℝ, N*N=0 →
      (∀ i j, |N i j|≤1) → g • (1+N) ∈ S := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h)
  obtain ⟨k,hk⟩ := exists_nat_gt (c/ε)
  have hk0 : 0 < (k:ℝ) := lt_trans (div_pos hc hε) hk
  refine ⟨c^k,pow_pos hc k,?_⟩
  intro N hN hbound
  have hnorm : ‖N‖ ≤ 1 := (Matrix.norm_le_iff zero_le_one).mpr (by simpa [Real.norm_eq_abs] using hbound)
  have hstep : c • (1 + (k:ℝ)⁻¹ • N) ∈ S := by
    apply hball
    rw [Metric.mem_ball,dist_eq_norm,smul_add,add_sub_cancel_left,norm_smul,norm_smul,
      Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hc,abs_of_pos (inv_pos.mpr hk0)]
    calc c * ((k:ℝ)⁻¹ * ‖N‖) ≤ c * ((k:ℝ)⁻¹ * 1) := by gcongr
         _ < ε := by rw [mul_one,←div_eq_mul_inv,div_lt_iff₀ hk0]; linarith [(div_lt_iff₀ hε).mp hk]
  have hp := S.pow_mem hstep k
  rw [smul_pow,nil_power N hN, mul_inv_cancel₀ hk0.ne', one_smul] at hp
  exact hp

private lemma scale_mul {n : ℕ} {S : Submonoid (Matrix (Fin n) (Fin n) ℝ)} {g : ℝ} {k l : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : (g^k) • A ∈ S) (hB : (g^l) • B ∈ S) :
    (g^(k+l)) • (A*B) ∈ S := by
  simpa only [pow_add,smul_mul_smul_comm] using S.mul_mem hA hB

private lemma scale_pad {n : ℕ} {S : Submonoid (Matrix (Fin n) (Fin n) ℝ)} {g : ℝ}
    (hI : g • (1 : Matrix (Fin n) (Fin n) ℝ) ∈ S) {k m : ℕ} (hkm : k ≤ m)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : (g^k) • A ∈ S) : (g^m) • A ∈ S := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hkm
  have hl := S.pow_mem hI l
  rw [smul_pow,one_pow] at hl
  simpa using scale_mul hA hl

private def axis {n : ℕ} (i : Fin n) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun j => if j=i then t else 1)

private def turn {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  (Equiv.swap i j).permMatrix ℝ * axis i (-1)

private lemma turn_eq {n : ℕ} {i j : Fin n} (h : i≠j) :
    turn i j = transvection i j 1 * transvection j i (-1) * transvection i j 1 := by
  ext a b
  rw [turn,axis,mul_diagonal]
  by_cases ha : a=i <;> by_cases ha' : a=j <;> by_cases hb : b=i <;> by_cases hb' : b=j <;>
    simp_all [PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,Equiv.swap_apply_def,
      Matrix.transvection,Matrix.add_mul,Matrix.mul_add,Matrix.one_apply,Matrix.single_apply] <;> grind

end OMA.S_mo_400876

namespace OMA.S_mo_400876
open Matrix
open scoped Matrix.Norms.Elementwise

private lemma turn_axis {n : ℕ} {i j : Fin n} (h : i≠j) (t : ℝ) :
    turn i j * axis i t * turn j i = axis j t := by
  ext a b
  simp only [turn,axis,←Matrix.mul_assoc,mul_diagonal,Equiv.Perm.permMatrix,
    PEquiv.mul_toMatrix_toPEquiv,submatrix_apply,id_eq,Equiv.symm_swap,PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply,Option.mem_def,Option.some.injEq,diagonal_apply,Equiv.swap_apply_def]
  grind

private lemma turn_flip {n : ℕ} (i j : Fin n) :
    turn i j * axis i (-1) = (Equiv.swap i j).permMatrix ℝ := by
  ext a b
  simp only [turn,axis,mul_diagonal]
  split <;> ring

lemma small_factor_scale {n : ℕ} (i₀ : Fin n) (S : Submonoid (Matrix (Fin n) (Fin n) ℝ))
    (haxis : ∀ t : ℝ, |t|≤1 → axis i₀ t ∈ S)
    {c : ℝ} (hc : 0<c) (h : c • (1 : Matrix (Fin n) (Fin n) ℝ) ∈ interior (S : Set _)) :
    ∃ v : ℝ, 0<v ∧ v • (1 : Matrix (Fin n) (Fin n) ℝ) ∈ S ∧
      ∀ M : Matrix (Fin n) (Fin n) ℝ, SmallFactor M → v • M ∈ S := by
  obtain ⟨g,hg,hN⟩ := scaled_nilpotents S hc h
  have hI : g • (1 : Matrix (Fin n) (Fin n) ℝ) ∈ S := by simpa using hN 0 (by simp) (by simp)
  have ht (i j : Fin n) (hij : i≠j) (t : ℝ) (ht : |t|≤1) :
      (g^1) • transvection i j t ∈ S := by
    simp only [pow_one]
    apply hN
    · simp [hij.symm]
    · intro a b
      simp only [Matrix.single_apply]
      split <;> simp [ht]
  have hturn (i j : Fin n) (hij : i≠j) : (g^3) • turn i j ∈ S := by
    rw [turn_eq hij]
    exact scale_mul (scale_mul (ht i j hij 1 (by norm_num)) (ht j i hij.symm (-1) (by norm_num))) (ht i j hij 1 (by norm_num))
  have hd (i : Fin n) (t : ℝ) (ht : |t|≤1) : (g^6) • axis i t ∈ S := by
    have h0 : (g^0) • axis i₀ t ∈ S := by simpa using haxis t ht
    by_cases hh : i₀=i
    · subst i
      exact scale_pad hI (by decide : 0 ≤ 6) h0
    · rw [←turn_axis hh]
      exact scale_mul (scale_mul (hturn _ _ hh) h0) (hturn _ _ (Ne.symm hh))
  have hs (i j : Fin n) : (g^9) • (Equiv.swap i j).permMatrix ℝ ∈ S := by
    by_cases hh : i=j
    · subst j
      simpa [smul_pow] using S.pow_mem hI 9
    · rw [←turn_flip]
      exact scale_mul (hturn i j hh) (hd i (-1) (by norm_num))
  refine ⟨g^9,pow_pos hg _,?_,?_⟩
  · simpa only [smul_pow,one_pow] using S.pow_mem hI 9
  · intro M hM
    rcases hM with ⟨N,hn,hb,rfl⟩ | ⟨i,j,rfl⟩ | ⟨i,t,ht,rfl⟩
    · exact scale_pad hI (by decide : 1 ≤ 9) (by simpa using hN N hn hb)
    · exact hs i j
    · exact scale_pad hI (by decide : 6 ≤ 9) (hd i t ht)

end OMA.S_mo_400876

namespace OMA.S_mo_400876
open Matrix
open scoped Matrix.Norms.Elementwise

lemma zero_interior_of_scalar {n : ℕ} (i₀ : Fin n) (S : Submonoid (Matrix (Fin n) (Fin n) ℝ))
    (haxis : ∀ t : ℝ, |t|≤1 → Matrix.diagonal (fun j => if j=i₀ then t else 1) ∈ S)
    {c : ℝ} (hc : 0<c) (h : c • (1 : Matrix (Fin n) (Fin n) ℝ) ∈ interior (S : Set _)) :
    (0 : Matrix (Fin n) (Fin n) ℝ) ∈ interior (S : Set _) := by
  obtain ⟨v,hv,hI,hM⟩ := small_factor_scale i₀ S haxis hc h
  have hp (L : List (Matrix (Fin n) (Fin n) ℝ)) (hL : ∀ M ∈ L, SmallFactor M) :
      (v^L.length) • L.prod ∈ S := by
    induction L with
    | nil => simp
    | cons M L ih =>
      have hh : (v^1) • M ∈ S := by simpa using hM M (hL _ (by simp))
      simpa [Nat.add_comm] using scale_mul hh (ih (fun X hX => hL X (List.mem_cons_of_mem M hX)))
  let d := v^(4*n)
  have hd : 0<d := pow_pos hv _
  apply mem_interior_iff_mem_nhds.mpr
  apply Metric.mem_nhds_iff.mpr
  refine ⟨d*(2^n : ℝ)⁻¹,mul_pos hd (by positivity),?_⟩
  intro A hA
  have hnorm : ‖A‖ < d*(2^n : ℝ)⁻¹ := by simpa [Metric.mem_ball] using hA
  have hB : ‖d⁻¹ • A‖ ≤ (2^n : ℝ)⁻¹ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd),←div_eq_inv_mul,div_le_iff₀ hd]
    linarith
  obtain ⟨L,hLen,hFactors,hProd⟩ := bounded_elimination n (d⁻¹ • A)
    (by simpa [Real.norm_eq_abs] using (Matrix.norm_le_iff (by positivity)).mp hB)
  have hm := scale_pad hI hLen (hp L hFactors)
  change d • L.prod ∈ S at hm
  change A ∈ S
  simpa only [hProd,smul_smul,mul_inv_cancel₀ hd.ne',one_smul] using hm
end OMA.S_mo_400876

namespace OMA.S_mo_400876
open Finset Filter Topology
noncomputable section
private lemma small_smul_dir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hU : U ∈ 𝓝 0) (v : E) : ∃ δ : ℝ, 0<δ ∧ δ • v ∈ U := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hU
  have hv : 0<‖v‖+1 := by positivity
  refine ⟨ε/(‖v‖+1),by positivity,hball ?_⟩
  rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hε hv)]
  calc _ < (ε/(‖v‖+1))*(‖v‖+1) := mul_lt_mul_of_pos_left (by linarith) (div_pos hε hv)
       _ = ε := div_mul_cancel₀ _ (ne_of_gt hv)

lemma convex_directions {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ι → E) (e : E) (U : Set E) (hU : U ∈ 𝓝 0)
    (h : ∀ x ∈ U, ∃ w : ι → ℝ, (∀ i, 0≤w i) ∧ (∑ i, w i)=1 ∧ (∑ i, w i • P i)=x) :
    Function.Surjective (fun w : ι → ℝ => ∑ i, w i • (P i-e)) ∧
      ∃ w : ι → ℝ, (∀ i, 0<w i) ∧ (∑ i, w i • (P i-e)) = -e := by
  classical
  have shift (w : ι → ℝ) : (∑ i, w i • (P i-e)) = (∑ i, w i • P i)-(∑ i, w i) • e := by
    simp only [smul_sub,Finset.sum_sub_distrib,Finset.sum_smul]
  constructor
  · intro x
    obtain ⟨δ,hδ,hu⟩ := small_smul_dir U hU x
    obtain ⟨v,_,hv,hvP⟩ := h _ hu
    obtain ⟨w,_,hw,hwP⟩ := h 0 (mem_of_mem_nhds hU)
    refine ⟨fun i => δ⁻¹*(v i-w i),?_⟩
    simp only [mul_smul,← Finset.smul_sum,sub_smul,Finset.sum_sub_distrib]
    rw [shift,shift,hv,hw,hvP,hwP,one_smul,zero_sub,sub_neg_eq_add,sub_add_cancel]
    exact inv_smul_smul₀ (ne_of_gt hδ) x
  · obtain ⟨δ,hδ,hu⟩ := small_smul_dir U hU (-(∑ i, P i))
    obtain ⟨v,hv,hvsum,hvP⟩ := h _ hu
    let c := 1+δ*(Fintype.card ι:ℝ)
    have hc : 0<c := by dsimp [c]; positivity
    let w (i : ι) := c⁻¹*(v i+δ)
    have hw (i) : 0<w i := mul_pos (inv_pos.mpr hc) (add_pos_of_nonneg_of_pos (hv i) hδ)
    have hws : (∑ i,w i)=1 := by
      simp only [w,← Finset.mul_sum,Finset.sum_add_distrib,hvsum,Finset.sum_const,
        Finset.card_univ,nsmul_eq_mul]
      rw [mul_comm (Fintype.card ι:ℝ)]
      exact inv_mul_cancel₀ (ne_of_gt hc)
    refine ⟨w,hw,?_⟩
    rw [shift,hws,one_smul]
    simp only [w,mul_smul,← Finset.smul_sum,add_smul,Finset.sum_add_distrib,hvP,smul_neg]
    simp
end
end OMA.S_mo_400876

namespace OMA.S_mo_400876

open Filter Set
open scoped Topology

/-- Along a direction pointing strictly inside every parameter constraint, the target ray
enters the interior of the image of an invertible differentiable chart. -/
lemma ray_interior_image {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [Finite ι]
    (f : E → F) (e : E ≃L[ℝ] F) (hf : HasStrictFDerivAt f (e : E →L[ℝ] F) 0)
    (v : F) (L : ι → E →L[ℝ] ℝ) (hv : ∀ i, 0 < L i (e.symm v)) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, f 0 + t • v ∈ interior (f '' {x : E | ∀ i, L i x ∈ Ioo 0 1}) := by
  classical
  let U := {x : E | ∀ i, L i x ∈ Ioo 0 1}
  have hU : IsOpen U := by
    change IsOpen {x : E | ∀ i, L i x ∈ Ioo 0 1}
    rw [show {x : E | ∀ i, L i x ∈ Ioo 0 1} = ⋂ i, (L i) ⁻¹' Ioo 0 1 by ext; simp]
    exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (L i).continuous
  let p := hf.toOpenPartialHomeomorph f
  let g := hf.localInverse f e 0
  let line := fun t : ℝ => f 0 + t • v
  have hline : HasDerivAt line v 0 := by
    simpa only [line,one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add (f 0)
  have hline0 : line 0=f 0 := by simp [line]
  have hginv : HasFDerivAt g (e.symm : F →L[ℝ] E) (line 0) := hline0 ▸ hf.to_localInverse.hasFDerivAt
  have hgle : HasDerivAt (fun t => g (line t)) (e.symm v) 0 := hginv.comp_hasDerivAt 0 hline
  have hgi : ∀ i, ∀ᶠ t in 𝓝[>] (0:ℝ), L i (g (line t)) ∈ Ioo 0 1 := by
    intro i
    let q := fun t => L i (g (line t))
    have hq : HasDerivAt q (L i (e.symm v)) 0 := (L i).hasFDerivAt.comp_hasDerivAt 0 hgle
    have hq0 : q 0=0 := by simp [q,hline0,g]
    have ht := hq.tendsto_slope_zero_right (Ioi_mem_nhds (hv i))
    have hu : ∀ᶠ t in 𝓝[>] (0:ℝ), q t<1 := (hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (Iio_mem_nhds (by simp [hq0]))
    filter_upwards [ht,hu,self_mem_nhdsWithin] with t ht hu ht0
    have H : 0 < t⁻¹*q t := by simpa [hq0] using ht
    exact ⟨(mul_pos_iff_of_pos_left (inv_pos.mpr ht0)).mp H,hu⟩
  have htarget : ∀ᶠ t in 𝓝[>] (0:ℝ), line t ∈ p.target := by
    apply (hline.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually
    exact p.open_target.mem_nhds (hline0 ▸ hf.image_mem_toOpenPartialHomeomorph_target)
  filter_upwards [eventually_all.mpr hgi,htarget] with t ht htx
  apply mem_interior_iff_mem_nhds.mpr
  have hgU : g (line t) ∈ U := ht
  have hsource : g (line t) ∈ p.source := p.map_target htx
  have heq : p (g (line t)) = line t := p.right_inv htx
  change p '' U ∈ 𝓝 (line t)
  rw [← heq]
  exact p.image_mem_nhds hsource (hU.mem_nhds hgU)

end OMA.S_mo_400876

namespace OMA.S_mo_400876

open Filter Set
open scoped Topology

/-- An ordered product of perturbations of the identity has first derivative equal to the
sum of the perturbations, also for a noncommutative normed algebra. -/
private lemma word_deriv {A E ι : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (D : ι → A) (L : ι → E →L[ℝ] ℝ) (s : List ι) :
    HasStrictFDerivAt (fun x : E => (s.map (fun i => 1 + L i x • D i)).prod)
      (s.map (fun i => (L i).smulRight (D i))).sum 0 := by
  induction s with
  | nil => simpa using hasStrictFDerivAt_const (1:A) (0:E) (𝕜 := ℝ)
  | cons i s ih =>
    have h : HasStrictFDerivAt (fun x => 1+L i x • D i) ((L i).smulRight (D i)) (0:E) :=
      ((L i).hasStrictFDerivAt.smul_const (D i)).const_add (1:A)
    simpa [add_comm,Pi.mul_def] using h.mul' ih

/-- A product set containing all words in segments from the identity contains an open
neighborhood at small positive points of every ray with strictly positive coefficients,
provided the segment directions linearly generate the whole algebra. -/
lemma product_ray_interior {A ι : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] [Fintype ι] (D : ι → A) (w : ι → ℝ) (hw : ∀ i, 0<w i)
    (R : A →L[ℝ] (ι → ℝ)) (hR : ∀ x : A, ∑ i, R x i • D i = x)
    (Y : Set A) (hY : ∀ u : ι → ℝ, (∀ i, u i ∈ Ioo 0 1) →
      ((Finset.univ : Finset ι).toList.map (fun i => 1+u i • D i)).prod ∈ Y) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (1:A) + t • (∑ i, w i • D i) ∈ interior Y := by
  classical
  let W := ∑ i, w i • D i
  let L (i : ι) : (A×ℝ) →L[ℝ] ℝ :=
    ((ContinuousLinearMap.proj i).comp (R.comp (ContinuousLinearMap.fst ℝ A ℝ))) +
      w i • ContinuousLinearMap.snd ℝ A ℝ
  let s := (Finset.univ : Finset ι).toList
  let word (p : A×ℝ) := (s.map (fun i => 1+L i p • D i)).prod
  let F (p : A×ℝ) := (word p - p.2 • W,p.2)
  have hword := word_deriv D L s
  have hd := (hword.sub ((ContinuousLinearMap.snd ℝ A ℝ).hasStrictFDerivAt.smul_const W)).prodMk
    (ContinuousLinearMap.snd ℝ A ℝ).hasStrictFDerivAt
  have hF : HasStrictFDerivAt F ((ContinuousLinearEquiv.refl ℝ (A×ℝ) : (A×ℝ) ≃L[ℝ] (A×ℝ)) : (A×ℝ) →L[ℝ] (A×ℝ)) 0 := by
    have hmap : (((s.map fun i => (L i).smulRight (D i)).sum - (ContinuousLinearMap.snd ℝ A ℝ).smulRight W).prod
        (ContinuousLinearMap.snd ℝ A ℝ)) = (ContinuousLinearEquiv.refl ℝ (A×ℝ) : (A×ℝ) →L[ℝ] (A×ℝ)) := by
      apply ContinuousLinearMap.ext
      rintro ⟨x,t⟩
      apply Prod.ext
      · have hsc (i : ι) : (w i * t) • D i = t • (w i • D i) := by rw [mul_comm,mul_smul]
        simp [s,sum_apply,L,W,add_smul,Finset.sum_add_distrib,hR,hsc,← Finset.smul_sum]
      · rfl
    rw [← hmap]
    exact hd
  have hL (i : ι) : 0 < L i ((ContinuousLinearEquiv.refl ℝ (A×ℝ)).symm (0,1)) := by simpa [L] using hw i
  have hc := ray_interior_image F (ContinuousLinearEquiv.refl ℝ (A×ℝ)) hF (0,1) L hL
  have hF0 : F 0 = (1,0) := by simp [F,word]
  filter_upwards [hc] with t ht
  have ht' : (1,t) ∈ interior (F '' {x | ∀ i, L i x ∈ Ioo 0 1}) := by simpa [hF0] using ht
  let g (x : A) := (x-t • W,t)
  have hg : Continuous g := by fun_prop
  have hx : g ((1:A)+t • W)=(1,t) := by simp [g]
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hg.continuousAt.preimage_mem_nhds (hx ▸ mem_interior_iff_mem_nhds.mp ht'))
  rintro x ⟨p,hp,he⟩
  have hpt : p.2=t := congrArg Prod.snd he
  have hxword : word p=x := by
    have he' : word p - p.2 • W = x-t • W := congrArg Prod.fst he
    rw [hpt] at he'; exact sub_left_inj.mp he'
  exact hxword ▸ hY (fun i => L i p) hp

end OMA.S_mo_400876

namespace OMA.S_mo_400876
open Filter Set
open scoped Topology

lemma product_ray_of_surjective {A ι : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [FiniteDimensional ℝ A] [CompleteSpace A] [Fintype ι]
    (D : ι → A) (w : ι → ℝ) (hw : ∀ i, 0<w i)
    (hsurj : Function.Surjective (fun u : ι → ℝ => ∑ i, u i • D i))
    (Y : Set A) (hY : ∀ u : ι → ℝ, (∀ i, u i ∈ Ioo 0 1) →
      ((Finset.univ : Finset ι).toList.map (fun i => 1+u i • D i)).prod ∈ Y) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (1:A) + t • (∑ i, w i • D i) ∈ interior Y := by
  classical
  let T : (ι → ℝ) →L[ℝ] A := ∑ i, (ContinuousLinearMap.proj i).smulRight (D i)
  have hT (u : ι→ℝ) : T u = ∑ i, u i • D i := by simp [T,sum_apply]
  have honto : Function.Surjective T := by
    intro x
    obtain ⟨u,hu⟩ := hsurj x
    exact ⟨u,(hT u).trans hu⟩
  obtain ⟨R,hR⟩ := T.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr honto)
  apply product_ray_interior D w hw R _ Y hY
  intro x
  rw [← hT]
  exact congrArg (fun g : A →L[ℝ] A => g x) hR

end OMA.S_mo_400876

namespace OMA.S_mo_400876
open Matrix Filter Topology
noncomputable section
lemma block_convex (n : ℕ) : ∃ U ∈ 𝓝 (0 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ),
    ∀ x ∈ U, ∃ w : Equiv.Perm (Fin (n+2)) → ℝ, (∀ i, 0≤w i) ∧ (∑ i,w i)=1 ∧
      (∑ i,w i • toBlock n (i.permMatrix ℝ))=x := by
  classical
  let U : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ) := {x | ∀ i j, 0 < fromBlock n x i j}
  have hU : U ∈ 𝓝 0 := by
    change ∀ᶠ x in 𝓝 0, ∀ i j, 0 < fromBlock n x i j
    simp only [Filter.eventually_all]
    intro i j
    have hc : Continuous (fun x => fromBlock n x i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp (continuous_fromBlock n))
    apply hc.continuousAt.eventually_const_lt
    change 0 < fromBlock n 0 i j
    rw [fromBlock_zero]
    change 0 < ((n+2:ℕ):ℝ)⁻¹
    positivity
  refine ⟨U,hU,?_⟩
  intro x hx
  have hx' : fromBlock n x ∈ doublyStochastic ℝ (Fin (n+2)) :=
    mem_doublyStochastic_iff_sum.mpr ⟨fun i j => (hx i j).le, fromBlock_margins n x⟩
  obtain ⟨w,hw,hs,he⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hx'
  exact ⟨w,hw,hs,by simpa only [map_sum,map_smul,toBlock_fromBlock] using congrArg (toBlock n) he⟩
end
end OMA.S_mo_400876

namespace OMA.S_mo_400876
open Matrix Finset

private lemma products_stochastic (n : ℕ) : products n ≤ doublyStochastic ℝ (Fin n) := by
  apply Submonoid.closure_le.mpr
  rintro _ ⟨p,q,t,ht,rfl⟩
  exact convex_doublyStochastic permMatrix_mem_doublyStochastic permMatrix_mem_doublyStochastic
    (sub_nonneg.mpr ht.2) ht.1 (by ring)

private def blockProducts (n : ℕ) : Submonoid (Matrix (Fin (n+1)) (Fin (n+1)) ℝ) where
  carrier := toBlock n '' (products (n+2) : Set _)
  one_mem' := ⟨1,(products _).one_mem,toBlock_one n⟩
  mul_mem' := by
    rintro _ _ ⟨A,hA,rfl⟩ ⟨B,hB,rfl⟩
    refine ⟨A*B,(products _).mul_mem hA hB,toBlock_mul A B ?_⟩
    exact (mem_doublyStochastic_iff_sum.mp (products_stochastic _ hA)).2

private lemma block_line (n : ℕ) (p : Equiv.Perm (Fin (n+2))) (s : ℝ) (hs : s ∈ Set.Icc 0 1) :
    1+s • (toBlock n (p.permMatrix ℝ)-1) ∈ blockProducts n := by
  refine ⟨(1-s) • (1 : Matrix (Fin (n+2)) (Fin (n+2)) ℝ)+s • p.permMatrix ℝ,?_,?_⟩
  · apply Submonoid.subset_closure
    exact ⟨1,p,s,hs,by simp⟩
  · rw [map_add,map_smul,map_smul,toBlock_one]
    simp only [smul_sub,sub_smul,one_smul]
    abel

private lemma block_axis (n : ℕ) (t : ℝ) (ht : |t|≤1) :
    Matrix.diagonal (fun j : Fin (n+1) => if j=0 then t else 1) ∈ blockProducts n := by
  let s := (1-t)/2
  have hs : s ∈ Set.Icc 0 1 := by
    obtain ⟨lo,hi⟩ := abs_le.mp ht
    constructor <;> dsimp [s] <;> linarith
  have h := block_line n (Equiv.swap 0 1) s hs
  rw [toBlock_swap] at h
  convert h using 1
  ext i j
  simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.sub_apply,Matrix.one_apply,
    Matrix.diagonal_apply,smul_eq_mul]
  dsimp [s]
  grind

end OMA.S_mo_400876

namespace OMA.S_mo_400876
open Matrix Filter Set
open scoped Topology Matrix.Norms.Operator

private lemma block_interior (n : ℕ) :
    (0 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) ∈ interior (blockProducts n : Set _) := by
  classical
  let P (p : Equiv.Perm (Fin (n+2))) := toBlock n (p.permMatrix ℝ)
  obtain ⟨U,hU,h⟩ := block_convex n
  obtain ⟨hs,⟨w,hw,hdir⟩⟩ := convex_directions P 1 U hU h
  have ray := product_ray_of_surjective (fun p => P p - 1) w hw hs (blockProducts n : Set _) (by
    intro u hu
    apply (blockProducts n).list_prod_mem
    intro A hA
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hA
    exact block_line n p _ ⟨(hu p).1.le,(hu p).2.le⟩)
  rw [hdir] at ray
  have hs1 : ∀ᶠ t : ℝ in 𝓝[>] 0, t<1 := nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  obtain ⟨t,ht,hit⟩ := (hs1.and ray).exists
  apply zero_interior_of_scalar (0 : Fin (n+1)) (blockProducts n) (block_axis n) (sub_pos.mpr ht)
  rw [sub_smul,one_smul,sub_eq_add_neg]
  rw [smul_neg] at hit
  convert! hit using 1

private lemma near_uniform (n : ℕ) : ∃ U : Set (Matrix (Fin (n+2)) (Fin (n+2)) ℝ),
    IsOpen U ∧ uniform (n+2) ∈ U ∧ ∀ A ∈ U, A ∈ doublyStochastic ℝ (Fin (n+2)) → A ∈ products (n+2) := by
  let V : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ) := interior (blockProducts n : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ))
  have hcont : Continuous (toBlock n) := (toBlock n).continuous_of_finiteDimensional
  refine ⟨(toBlock n) ⁻¹' V, isOpen_interior.preimage hcont,?_,?_⟩
  · change toBlock n (uniform (n+2)) ∈ V
    rw [toBlock_uniform]
    exact block_interior n
  · intro A hA hds
    change toBlock n A ∈ interior (blockProducts n : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) at hA
    have hm : toBlock n A ∈ blockProducts n := interior_subset hA
    obtain ⟨B,hB,hEq⟩ := hm
    have hBds := products_stochastic _ hB
    have eq := congrArg (fromBlock n) hEq
    rw [fromBlock_toBlock B (mem_doublyStochastic_iff_sum.mp hBds).2,
      fromBlock_toBlock A (mem_doublyStochastic_iff_sum.mp hds).2] at eq
    exact eq ▸ hB

end OMA.S_mo_400876

open OMA.S_mo_400876

theorem OMA.solution : type_of% @OMA.S_mo_400876.main := by
  intro n hn
  match n with
  | 0 => omega
  | 1 =>
    refine ⟨Set.univ,isOpen_univ,Set.mem_univ _,?_⟩
    intro A _ hA
    have h : A=1 := by
      ext i j
      fin_cases i
      fin_cases j
      simpa using sum_row_of_mem_doublyStochastic hA 0
    exact h ▸ (products 1).one_mem
  | n+2 => exact near_uniform n
