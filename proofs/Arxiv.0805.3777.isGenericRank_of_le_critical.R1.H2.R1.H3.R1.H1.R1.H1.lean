import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H1_R1

/-! Consecutive long dimensions in complex tensor spaces.

Finite tangent configurations and simultaneous width-two growth give the exact
generic ranks for three and five slices. Four slices use the middle-axis
construction in the parent reduction. Combining the spanning configurations
yields a dense-open upper bound in every first dimension, together with the
dimension-count lower bound. -/

namespace CriticalTensor

def Spans (a b c r : ℕ) : Prop :=
  ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
    ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
      ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))

/-- A diagonal block with a regular coordinate part of length h and a base of length d. -/
def Border (a d h base extra : ℕ) : Prop :=
  ∃ X : Fin extra → Fin a → ℂ, ∃ Y Z : Fin extra → (Fin h ⊕ Fin d) → ℂ,
  ∃ x : Fin base → Fin a → ℂ, ∃ y z : Fin base → Fin d → ℂ,
    ∀ T : Fin a → (Fin h ⊕ Fin d) → (Fin h ⊕ Fin d) → ℂ,
    ∃ U : Fin extra → Fin a → ℂ, ∃ V W : Fin extra → (Fin h ⊕ Fin d) → ℂ,
    ∃ v w : Fin base → Fin h → ℂ, ∀ i j k, (j.isLeft=true ∨ k.isLeft=true) →
      T i j k =
        (∑ t, (U t i*(Y t j*Z t k) + X t i*(V t j*Z t k) + X t i*(Y t j*W t k))) +
        ∑ t, (x t i*(j.elim (v t) (fun _ => 0) * k.elim (fun _ => 0) (z t)) +
          x t i*(j.elim (fun _ => 0) (y t) * k.elim (w t) (fun _ => 0)))

/-- Two independent regular groups interact through one partial variation
of each point in the opposite group. -/
def Cross (a h extra : ℕ) : Prop :=
  ∃ x₁ x₂ : Fin extra → Fin a → ℂ, ∃ y z : Fin extra → Fin h → ℂ,
    ∀ T : Fin a → Fin h → Fin h → ℂ, ∃ v w : Fin extra → Fin h → ℂ, ∀ i j k,
      T i j k = ∑ t, (x₂ t i*(v t j*z t k) + x₁ t i*(y t j*w t k))

end CriticalTensor

namespace CriticalTensor

/-- A tangent witness on the two width-h borders of a rectangular d-by-e base. -/
def RectBorder (a d e h base extra : ℕ) : Prop :=
  ∃ X : Fin extra → Fin a → ℂ,
    ∃ Y : Fin extra → (Fin h ⊕ Fin d) → ℂ, ∃ Z : Fin extra → (Fin h ⊕ Fin e) → ℂ,
    ∃ x : Fin base → Fin a → ℂ, ∃ y : Fin base → Fin d → ℂ, ∃ z : Fin base → Fin e → ℂ,
    ∀ T : Fin a → (Fin h ⊕ Fin d) → (Fin h ⊕ Fin e) → ℂ,
    ∃ U : Fin extra → Fin a → ℂ, ∃ V : Fin extra → (Fin h ⊕ Fin d) → ℂ,
    ∃ W : Fin extra → (Fin h ⊕ Fin e) → ℂ, ∃ v w : Fin base → Fin h → ℂ,
      ∀ i j k, (j.isLeft=true ∨ k.isLeft=true) →
        T i j k =
          (∑ t, (U t i*(Y t j*Z t k) + X t i*(V t j*Z t k) + X t i*(Y t j*W t k))) +
          ∑ t, (x t i*(j.elim (v t) (fun _ => 0) * k.elim (fun _ => 0) (z t)) +
            x t i*(j.elim (fun _ => 0) (y t) * k.elim (w t) (fun _ => 0)))

end CriticalTensor

namespace CriticalTensor.RectGrowth

open MvPolynomial

/-- A single surjective specialization gives a polynomial whose nonvanishing
guarantees surjectivity. Its determinant uses a fixed right inverse at that point. -/
lemma surjectivity_polynomial {I J V : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (M : Matrix I J (MvPolynomial V ℂ)) (x₀ : V → ℂ)
    (h₀ : Function.Surjective (M.map (eval x₀)).mulVec) :
    ∃ Q : MvPolynomial V ℂ, Q ≠ 0 ∧ ∀ x : V → ℂ,
      eval x Q ≠ 0 → Function.Surjective (M.map (eval x)).mulVec := by
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h₀
  let D := M * B.map (C : ℂ →+* MvPolynomial V ℂ)
  have specialize (x : V → ℂ) : eval x D.det = (M.map (eval x) * B).det := by
    have hconst : (B.map (C : ℂ →+* MvPolynomial V ℂ)).map (eval x) = B := by
      ext i j
      simp [Matrix.map_apply]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, show D = _ from rfl, Matrix.map_mul, hconst]
  have hvalue : eval x₀ D.det = 1 := by rw [specialize, hB, Matrix.det_one]
  refine ⟨D.det, ?_, ?_⟩
  · intro he
    rw [he, map_zero] at hvalue
    exact zero_ne_one hvalue
  · intro x hx
    rw [specialize] at hx
    have hprod : Function.Surjective (M.map (eval x) * B).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hx))
    intro y
    obtain ⟨z, hz⟩ := hprod y
    refine ⟨B.mulVec z, ?_⟩
    rw [Matrix.mulVec_mulVec]
    exact hz

lemma avoid_two {V : Type} {P Q : MvPolynomial V ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ x : V → ℂ, eval x P ≠ 0 ∧ eval x Q ≠ 0 := by
  by_contra! h
  apply (mul_ne_zero hP hQ)
  apply MvPolynomial.funext
  intro x
  rw [map_mul, map_zero]
  by_cases hx : eval x P = 0
  · exact mul_eq_zero.mpr (Or.inl hx)
  · exact mul_eq_zero.mpr (Or.inr (h x hx))

/-- Separate specializations can verify blocks depending on the same parameters:
the product of their certificate polynomials is nonzero over the complex numbers. -/
lemma simultaneous_surjectivity {K V : Type} [Fintype K] {I J : K → Type}
    [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)] [∀ k, Fintype (J k)]
    (M : ∀ k, Matrix (I k) (J k) (MvPolynomial V ℂ))
    (h : ∀ k, ∃ x : V → ℂ, Function.Surjective ((M k).map (eval x)).mulVec)
    (P : MvPolynomial V ℂ) (hP : P ≠ 0) :
    ∃ x : V → ℂ, eval x P ≠ 0 ∧ ∀ k, Function.Surjective ((M k).map (eval x)).mulVec := by
  classical
  choose z hz using h
  choose Q hQ hgood using fun k => surjectivity_polynomial (M k) (z k) (hz k)
  have hprod : (∏ k, Q k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hQ k
  obtain ⟨x, hx, hrest⟩ := avoid_two hP hprod
  have hvals : (∏ k, eval x (Q k)) ≠ 0 := by simpa only [map_prod] using hrest
  exact ⟨x, hx, fun k => hgood k x (Finset.prod_ne_zero_iff.mp hvals k (Finset.mem_univ k))⟩

/-- A priority for each sector is enough. Distinct sectors at the same priority
are disjoint on their diagonal rows and columns. -/
lemma graded_surjective {R C S : Type} [Fintype R] [Fintype C] [Fintype S] [DecidableEq S]
    (f : R → S) (g : C → S) (priority : S → Fin 3) (A : Matrix R C ℂ)
    (zero_above : ∀ i j, f i ≠ g j → priority (f i) ≤ priority (g j) → A i j=0)
    (local_maps : ∀ s : S, Function.Surjective
      (A.submatrix (fun i : {i // f i=s} => i.val) (fun j : {j // g j=s} => j.val)).mulVec) :
    Function.Surjective A.mulVec := by
  classical
  have hpre (j : R) : ∃ v : {k // g k=f j} → ℂ, ∀ i : {i // f i=f j},
      (∑ k, A i.val k.val * v k) = if i.val=j then 1 else 0 := by
    obtain ⟨v,hv⟩ := local_maps (f j) fun i => if i.val=j then 1 else 0
    exact ⟨v,fun i => congrFun hv i⟩
  choose v hv using hpre
  let B : Matrix C R ℂ := fun k j => if h : g k=f j then v j ⟨k,h⟩ else 0
  let L := A*B
  have entries (i j : R) : L i j = ∑ k : {k // g k=f j}, A i k.val*v j k := by
    change (∑ k : C, A i k*(if h : g k=f j then v j ⟨k,h⟩ else 0)) = _
    let F (k : C) := A i k * (if h : g k=f j then v j ⟨k,h⟩ else 0)
    have e := (Equiv.sumCompl (fun k : C => g k=f j)).sum_comp F
    rw [Fintype.sum_sum_type] at e
    have hp (q : {k // g k=f j}) : g q.val=f j := q.property
    have hn (q : {k // g k≠f j}) : g q.val≠f j := q.property
    simpa [F,hp,hn] using e.symm
  have off (i j : R) (h : f i ≠ f j) (hle : priority (f i) ≤ priority (f j)) : L i j=0 := by
    rw [entries]
    apply Finset.sum_eq_zero
    intro k _
    rw [zero_above i k.val (by simpa only [k.property] using h)
      (by simpa only [k.property] using hle),zero_mul]
  have triangular : L.BlockTriangular (fun i => OrderDual.toDual (priority (f i))) := by
    intro i j h
    change priority (f i) < priority (f j) at h
    exact off i j (fun he => (ne_of_lt h) (congrArg priority he)) (le_of_lt h)
  have diag (s : (Fin 3)ᵒᵈ) : L.toSquareBlock (fun i => OrderDual.toDual (priority (f i))) s = 1 := by
    ext i j
    obtain ⟨i,hi⟩ := i
    obtain ⟨j,hj⟩ := j
    have hlev : priority (f i)=priority (f j) := hi.trans hj.symm
    change L i j = _
    by_cases hij : f i=f j
    · rw [entries,hv j ⟨i,hij⟩,Matrix.one_apply]
      simp only [Subtype.mk.injEq]
    · rw [off i j hij (le_of_eq hlev),Matrix.one_apply]
      simp [show i ≠ j from fun h => hij (congrArg f h)]
  have detL : L.det=1 := by rw [triangular.det_fintype]; simp [diag]
  have hL : Function.Surjective L.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (by rw [detL]; exact isUnit_one))
  intro y
  obtain ⟨z,hz⟩ := hL y
  refine ⟨B.mulVec z,?_⟩
  rw [Matrix.mulVec_mulVec]
  exact hz

/-- Transfer the row equations of a finite template to a global sector. Every
row needed by the sector has a local representative. Coincident selected
columns can be combined by summing their coefficients. -/
lemma cover_matrix {R C I J : Type} [Fintype C] [DecidableEq C] [Fintype J]
    (A : Matrix R C ℂ) (L : Matrix I J ℂ) (rmap : I → R) (cmap : J → C)
    (hR : Function.Surjective rmap) (hM : ∀ i j, A (rmap i) (cmap j)=L i j)
    (hs : Function.Surjective L.mulVec) : Function.Surjective A.mulVec := by
  classical
  let E : Matrix C J ℂ := fun k j => if k=cmap j then 1 else 0
  have hcols (i j) : (A*E) (rmap i) j=L i j := by
    rw [Matrix.mul_apply]
    simpa [E,mul_ite,Finset.sum_ite_eq'] using hM i j
  intro y
  obtain ⟨z,hz⟩ := hs (fun i => y (rmap i))
  refine ⟨E.mulVec z,?_⟩
  rw [Matrix.mulVec_mulVec]
  funext r
  obtain ⟨i,rfl⟩ := hR r
  change (∑ j, (A*E) (rmap i) j*z j) = _
  simpa only [hcols,Matrix.mulVec,dotProduct] using congrFun hz i

end CriticalTensor.RectGrowth

namespace CriticalTensor.RectGrowth

open MvPolynomial

structure Dimensions where
  a : ℕ
  d : ℕ
  e : ℕ
  h : ℕ
  base : ℕ
  extra : ℕ

variable (p : Dimensions)

abbrev Pt (G : Type) := Fin p.base ⊕ (G × Fin p.extra)
abbrev Axis (n : ℕ) (G : Type) := Fin n ⊕ (G × Fin p.h)
abbrev LocalAxis (n : ℕ) := Fin p.h ⊕ Fin n
abbrev Dir (I J : Type) := Fin p.a ⊕ (I ⊕ J)
abbrev V (G : Type) := (Fin p.base × Dir p (Fin p.d) (Fin p.e)) ⊕ (G × Fin p.extra × Dir p (LocalAxis p p.d) (LocalAxis p p.e))
abbrev RR (G : Type) := Fin p.a × Axis p p.d G × Axis p p.e G
abbrev CC (G : Type) := Pt p G × Dir p (Axis p p.d G) (Axis p p.e G)
abbrev Pair (G : Type) := {z : G × G // z.1 ≠ z.2}
abbrev Sector (G : Type) := Unit ⊕ (G ⊕ Pair G)
abbrev Arm := (Fin p.h × Fin p.e) ⊕ ((Fin p.d × Fin p.h) ⊕ (Fin p.h × Fin p.h))

def arms : Arm p → LocalAxis p p.d × LocalAxis p p.e
  | .inl (j,k) => (.inl j,.inr k)
  | .inr (.inl (j,k)) => (.inr j,.inl k)
  | .inr (.inr (j,k)) => (.inl j,.inl k)

def loc {G : Type} {n : ℕ} (g : G) : LocalAxis p n → Axis p n G
  | .inl u => .inr (g,u)
  | .inr j => .inl j

def Row {G : Type} : Sector G → Type
  | .inl _ => Fin p.a × Fin p.d × Fin p.e
  | .inr (.inl _) => Fin p.a × Arm p
  | .inr (.inr _) => Fin p.a × Fin p.h × Fin p.h

def Col {G : Type} : Sector G → Type
  | .inl _ => Fin p.base × Dir p (Fin p.d) (Fin p.e)
  | .inr (.inl _) => (Fin p.extra × Dir p (LocalAxis p p.d) (LocalAxis p p.e)) ⊕ (Fin p.base × (Fin p.h ⊕ Fin p.h))
  | .inr (.inr _) => Fin p.extra × (Fin p.h ⊕ Fin p.h)

instance {G : Type} (s : Sector G) : Fintype (Row p s) := by rcases s with u|g|z <;> dsimp [Row] <;> infer_instance
instance {G : Type} (s : Sector G) : DecidableEq (Row p s) := by rcases s with u|g|z <;> dsimp [Row] <;> infer_instance
instance {G : Type} (s : Sector G) : Fintype (Col p s) := by rcases s with u|g|z <;> dsimp [Col] <;> infer_instance
instance {G : Type} (s : Sector G) : DecidableEq (Col p s) := by rcases s with u|g|z <;> dsimp [Col] <;> infer_instance

def row {G : Type} : (s : Sector G) → Row p s → RR p G
  | .inl _,(i,j,k) => (i,.inl j,.inl k)
  | .inr (.inl g),(i,z) => (i,loc p g (arms p z).1,loc p g (arms p z).2)
  | .inr (.inr q),(i,j,k) => (i,.inr (q.val.1,j),.inr (q.val.2,k))

def col {G : Type} : (s : Sector G) → Col p s → CC p G
  | .inl _,(t,h) => (.inl t,h.map id (Sum.map Sum.inl Sum.inl))
  | .inr (.inl g),.inl (t,h) => (.inr (g,t),h.map id (Sum.map (loc p g) (loc p g)))
  | .inr (.inl g),.inr (t,.inl h) => (.inl t,.inr (.inl (.inr (g,h))))
  | .inr (.inl g),.inr (t,.inr h) => (.inl t,.inr (.inr (.inr (g,h))))
  | .inr (.inr q),(t,.inl h) => (.inr (q.val.2,t),.inr (.inl (.inr (q.val.1,h))))
  | .inr (.inr q),(t,.inr h) => (.inr (q.val.1,t),.inr (.inr (.inr (q.val.2,h))))

def lev {G : Type} : Sector G → Fin 3
  | .inl _ => 2
  | .inr (.inl _) => 1
  | .inr (.inr _) => 0

section
variable {G K : Type} [DecidableEq G] [CommSemiring K]

def A (x : V p G → K) : Pt p G → Fin p.a → K
  | .inl t,i => x (.inl (t,.inl i))
  | .inr (g,t),i => x (.inr (g,t,.inl i))

def tail {n : ℕ} (b : Fin p.base → Fin n → K) (B : G → Fin p.extra → LocalAxis p n → K) : Pt p G → Axis p n G → K
  | .inl t,.inl j => b t j
  | .inl _,.inr _ => 0
  | .inr (g,t),.inl j => B g t (.inr j)
  | .inr (g,t),.inr (h,i) => if h=g then B g t (.inl i) else 0

def B (x : V p G → K) := tail p (n:=p.d) (fun t j => x (.inl (t,.inr (.inl j)))) (fun g t j => x (.inr (g,t,.inr (.inl j))))
def Cc (x : V p G → K) := tail p (n:=p.e) (fun t k => x (.inl (t,.inr (.inr k)))) (fun g t k => x (.inr (g,t,.inr (.inr k))))

def tangent (x : V p G → K) (r : RR p G) : CC p G → K
  | (t,.inl h) => if h=r.1 then B p x t r.2.1 * Cc p x t r.2.2 else 0
  | (t,.inr (.inl h)) => if h=r.2.1 then A p x t r.1 * Cc p x t r.2.2 else 0
  | (t,.inr (.inr h)) => if h=r.2.2 then A p x t r.1 * B p x t r.2.1 else 0

def full (x : V p G → K) : Matrix (Σ s : Sector G, Row p s) (Σ s : Sector G, Col p s) K :=
  fun r c => tangent p x (row p r.1 r.2) (col p c.1 c.2)

def block (x : V p G → K) (s : Sector G) : Matrix (Row p s) (Col p s) K :=
  fun r c => tangent p x (row p s r) (col p s c)

lemma tail_loc {n : ℕ} (b : Fin p.base → Fin n → K) (H : G → Fin p.extra → LocalAxis p n → K)
    (g : G) (t : Fin p.extra) (j : LocalAxis p n) : tail p b H (.inr (g,t)) (loc p g j) = H g t j := by
  cases j <;> simp [tail,loc]

omit [DecidableEq G] in
lemma loc_eq {n : ℕ} (g : G) (j k : LocalAxis p n) : loc p g j=loc p g k ↔ j=k := by cases j <;> cases k <;> simp [loc]

private lemma tail_map {L : Type} [CommSemiring L] {n : ℕ} (φ : K →+* L) (b : Fin p.base → Fin n → K)
    (H : G → Fin p.extra → LocalAxis p n → K) (t : Pt p G) (j : Axis p n G) :
    φ (tail p b H t j) = tail p (fun t j => φ (b t j)) (fun g t j => φ (H g t j)) t j := by
  rcases t with t|⟨g,t⟩ <;> rcases j with j|⟨h,j⟩ <;> simp only [tail,map_zero]
  by_cases he : h=g <;> simp [he]

lemma block_eval (x : V p G → ℂ) (s : Sector G) :
    (block p (MvPolynomial.X : V p G → MvPolynomial (V p G) ℂ) s).map (eval x) = block p x s := by
  ext r j
  change eval x (tangent p MvPolynomial.X (row p s r) (col p s j)) = tangent p x (row p s r) (col p s j)
  generalize hc : col p s j = z
  rcases z with ⟨t,h|h|h⟩ <;> rcases t with t|⟨g,t⟩ <;>
    simp only [tangent,A,B,Cc,apply_ite,tail_map,map_mul,map_zero,eval_X]
  all_goals split <;> simp_all

end

lemma row_surj {G : Type} [DecidableEq G] : Function.Surjective (fun z : Σ s : Sector G, Row p s => row p z.1 z.2) := by
  rintro ⟨i,j|⟨g,j⟩,k|⟨l,k⟩⟩
  · exact ⟨⟨.inl (),i,j,k⟩,rfl⟩
  · exact ⟨⟨.inr (.inl l),i,.inr (.inl (j,k))⟩,rfl⟩
  · exact ⟨⟨.inr (.inl g),i,.inl (j,k)⟩,rfl⟩
  · by_cases h : g=l
    · subst l
      exact ⟨⟨.inr (.inl g),i,.inr (.inr (j,k))⟩,rfl⟩
    · exact ⟨⟨.inr (.inr ⟨(g,l),h⟩),i,j,k⟩,rfl⟩

end CriticalTensor.RectGrowth

namespace CriticalTensor.RectGrowth

variable (p : Dimensions) {G : Type} [DecidableEq G]

def param (a : Fin p.base → Fin p.a → ℂ) (b : Fin p.base → Fin p.d → ℂ) (c : Fin p.base → Fin p.e → ℂ)
    (A : G → Fin p.extra → Fin p.a → ℂ) (B : G → Fin p.extra → LocalAxis p p.d → ℂ)
    (C : G → Fin p.extra → LocalAxis p p.e → ℂ) : V p G → ℂ
  | .inl (t,.inl i) => a t i
  | .inl (t,.inr (.inl j)) => b t j
  | .inl (t,.inr (.inr k)) => c t k
  | .inr (g,t,.inl i) => A g t i
  | .inr (g,t,.inr (.inl j)) => B g t j
  | .inr (g,t,.inr (.inr k)) => C g t k

lemma base_rank (hb : Spans p.a p.d p.e p.base) :
    ∃ x : V p G → ℂ, Function.Surjective (block p x (.inl ())).mulVec := by
  classical
  obtain ⟨a,b,c,hb⟩ := hb
  let x : V p G → ℂ := param p a b c 0 0 0
  refine ⟨x,?_⟩
  intro y
  obtain ⟨u,v,w,hu⟩ := hb fun i j k => y (i,j,k)
  let z : Fin p.base × Dir p (Fin p.d) (Fin p.e) → ℂ := fun (t,h) => h.elim (u t) (Sum.elim (v t) (w t))
  refine ⟨z,?_⟩
  funext r
  obtain ⟨i,j,k⟩ := r
  change (∑ s : Fin p.base × Dir p (Fin p.d) (Fin p.e), tangent p x (i,.inl j,.inl k) (col p (.inl ()) s) * z s) = y (i,j,k)
  rw [hu,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp [tangent,col,x,param,A,B,Cc,tail,z,ite_mul,Finset.sum_ite_eq']
  ring

def target (y : Fin p.a × Arm p → ℂ) (i : Fin p.a) : LocalAxis p p.d → LocalAxis p p.e → ℂ
  | .inl j,.inl k => y (i,.inr (.inr (j,k)))
  | .inl j,.inr k => y (i,.inl (j,k))
  | .inr j,.inl k => y (i,.inr (.inl (j,k)))
  | .inr _,.inr _ => 0

lemma target_arms (y : Fin p.a × Arm p → ℂ) (i : Fin p.a) (r : Arm p) :
    target p y i (arms p r).1 (arms p r).2=y (i,r) := by
  rcases r with ⟨j,k⟩|⟨j,k⟩|⟨j,k⟩ <;> rfl

lemma arms_hit (r : Arm p) : (arms p r).1.isLeft=true ∨ (arms p r).2.isLeft=true := by
  rcases r with ⟨j,k⟩|⟨j,k⟩|⟨j,k⟩ <;> simp [arms]

lemma border_rank (g : G) (hr : RectBorder p.a p.d p.e p.h p.base p.extra) :
    ∃ x : V p G → ℂ, Function.Surjective (block p x (.inr (.inl g))).mulVec := by
  classical
  obtain ⟨aa,bb,cc,a,b,c,hr⟩ := hr
  let x : V p G → ℂ := param p a b c (fun _ => aa) (fun _ => bb) (fun _ => cc)
  refine ⟨x,?_⟩
  intro y
  obtain ⟨u,v,w,vb,wb,hu⟩ := hr (target p y)
  let z : (Fin p.extra × Dir p (LocalAxis p p.d) (LocalAxis p p.e)) ⊕ (Fin p.base × (Fin p.h ⊕ Fin p.h)) → ℂ
    | .inl (t,h) => h.elim (u t) (Sum.elim (v t) (w t))
    | .inr (t,h) => h.elim (vb t) (wb t)
  refine ⟨z,?_⟩
  funext r
  obtain ⟨i,r⟩ := r
  change (∑ s : (Fin p.extra × Dir p (LocalAxis p p.d) (LocalAxis p p.e)) ⊕ (Fin p.base × (Fin p.h ⊕ Fin p.h)),
    tangent p x (i,loc p g (arms p r).1,loc p g (arms p r).2) (col p (.inr (.inl g)) s) * z s) = y (i,r)
  rw [← target_arms p y i r,hu i _ _ (arms_hit p r),Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_prod_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    simp [tangent,col,x,param,A,B,Cc,z,tail_loc,loc_eq,ite_mul,Finset.sum_ite_eq']
    ring
  · apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type]
    rcases r with ⟨j,k⟩|⟨j,k⟩|⟨j,k⟩ <;>
      simp [tangent,col,x,param,A,B,Cc,tail,z,arms,loc,ite_mul,Finset.sum_ite_eq'] <;> ring

lemma cross_rank (q : Pair G) (hc : Cross p.a p.h p.extra) :
    ∃ x : V p G → ℂ, Function.Surjective (block p x (.inr (.inr q))).mulVec := by
  classical
  obtain ⟨x₁,x₂,b,c,hc⟩ := hc
  let x : V p G → ℂ := param p 0 0 0 (fun g => if g=q.val.1 then x₁ else x₂)
    (fun _ t => Sum.elim (b t) 0) (fun _ t => Sum.elim (c t) 0)
  refine ⟨x,?_⟩
  intro y
  obtain ⟨v,w,hw⟩ := hc fun i j k => y (i,j,k)
  let z : Fin p.extra × (Fin p.h ⊕ Fin p.h) → ℂ := fun (t,h) => h.elim (v t) (w t)
  refine ⟨z,?_⟩
  funext r
  obtain ⟨i,j,k⟩ := r
  change (∑ s : Fin p.extra × (Fin p.h ⊕ Fin p.h),
    tangent p x (i,.inr (q.val.1,j),.inr (q.val.2,k)) (col p (.inr (.inr q)) s)*z s)=y (i,j,k)
  rw [hw,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type]
  simp [tangent,col,x,param,A,B,Cc,tail,z,ite_mul,Finset.sum_ite_eq',q.property.symm]
  ring

end CriticalTensor.RectGrowth

namespace CriticalTensor.RectGrowth

variable (p : Dimensions) {G : Type} [DecidableEq G] (x : V p G → ℂ)

private lemma arm_base (g : G) (r : Row p (.inr (.inl g))) (z : Col p (G:=G) (.inl ())) :
    tangent p x (row p (.inr (.inl g)) r) (col p (.inl ()) z)=0 := by
  rcases r with ⟨i,⟨j,k⟩|⟨j,k⟩|⟨j,k⟩⟩ <;> rcases z with ⟨t,h|h|h⟩ <;>
    simp [row,col,tangent,arms,loc,B,Cc,tail]

private lemma arm_other (g h : G) (gh : g ≠ h) (r : Row p (.inr (.inl g))) (z : Col p (.inr (.inl h))) :
    tangent p x (row p (.inr (.inl g)) r) (col p (.inr (.inl h)) z)=0 := by
  rcases r with ⟨i,⟨j,k⟩|⟨j,k⟩|⟨j,k⟩⟩ <;> rcases z with ⟨t,u|(u|u)|(u|u)⟩|⟨t,u|u⟩ <;>
    simp [row,col,tangent,arms,loc,B,Cc,tail,gh,gh.symm]

private lemma pair_base (q : Pair G) (r : Row p (.inr (.inr q))) (z : Col p (G:=G) (.inl ())) :
    tangent p x (row p (.inr (.inr q)) r) (col p (.inl ()) z)=0 := by
  rcases r with ⟨i,j,k⟩
  rcases z with ⟨t,h|h|h⟩ <;> simp [row,col,tangent,B,Cc,tail]

private lemma pair_arm (q : Pair G) (h : G) (r : Row p (.inr (.inr q))) (z : Col p (.inr (.inl h))) :
    tangent p x (row p (.inr (.inr q)) r) (col p (.inr (.inl h)) z)=0 := by
  rcases q with ⟨⟨g,l⟩,hg⟩
  change g≠l at hg
  rcases r with ⟨i,j,k⟩
  rcases z with ⟨t,u|(u|u)|(u|u)⟩|⟨t,u|u⟩ <;>
    by_cases he : g=h <;> by_cases hf : l=h <;>
    simp_all [row,col,tangent,loc,B,Cc,tail]
  all_goals grind

private lemma pair_other (q q' : Pair G) (hpq : q≠q') (r : Row p (.inr (.inr q))) (z : Col p (.inr (.inr q'))) :
    tangent p x (row p (.inr (.inr q)) r) (col p (.inr (.inr q')) z)=0 := by
  rcases q with ⟨⟨a,b⟩,hab⟩
  rcases q' with ⟨⟨c,d⟩,hcd⟩
  have h : a=c → b≠d := by rintro rfl rfl; exact (hpq rfl).elim
  rcases r with ⟨i,j,k⟩
  rcases z with ⟨t,v|v⟩ <;> by_cases hac : a=c <;> by_cases hbd : b=d <;>
    simp_all [row,col,tangent,B,Cc,tail,eq_comm]

lemma off (s t : Sector G) (h : s≠t) (hl : lev s≤lev t) (r : Row p s) (z : Col p t) :
    tangent p x (row p s r) (col p t z)=0 := by
  rcases s with ⟨⟩|g|q <;> rcases t with ⟨⟩|h'|q'
  · exact (h rfl).elim
  · exact (by decide : ¬((2:Fin 3)≤1)) hl |>.elim
  · exact (by decide : ¬((2:Fin 3)≤0)) hl |>.elim
  · exact arm_base p x g r z
  · exact arm_other p x g h' (fun e => h (e ▸ rfl)) r z
  · exact (by decide : ¬((1:Fin 3)≤0)) hl |>.elim
  · exact pair_base p x q r z
  · exact pair_arm p x q h' r z
  · exact pair_other p x q q' (fun e => h (e ▸ rfl)) r z

end CriticalTensor.RectGrowth

namespace CriticalTensor.RectGrowth

open MvPolynomial

variable (p : Dimensions) {G : Type} [Fintype G] [DecidableEq G]

def actual (x : V p G → ℂ) : Matrix (RR p G) (CC p G) ℂ := tangent p x

lemma common (hb : Spans p.a p.d p.e p.base) (hr : RectBorder p.a p.d p.e p.h p.base p.extra)
    (hc : Cross p.a p.h p.extra) : ∃ x : V p G → ℂ, Function.Surjective (actual p x).mulVec := by
  classical
  have each (s : Sector G) : ∃ x : V p G → ℂ, Function.Surjective (block p x s).mulVec := by
    rcases s with ⟨⟩|g|q
    · exact base_rank p hb
    · exact border_rank p g hr
    · exact cross_rank p q hc
  let M (s : Sector G) := block p (MvPolynomial.X : V p G → MvPolynomial (V p G) ℂ) s
  have openSet (s : Sector G) : ∃ x : V p G → ℂ, Function.Surjective ((M s).map (eval x)).mulVec := by
    obtain ⟨x,h⟩ := each s
    exact ⟨x,by simpa only [M,block_eval] using h⟩
  obtain ⟨x,_,hx⟩ := simultaneous_surjectivity M openSet 1 one_ne_zero
  have hs (s : Sector G) : Function.Surjective (block p x s).mulVec := by simpa only [M,block_eval] using hx s
  have hfull : Function.Surjective (full p x).mulVec := by
    apply graded_surjective (fun r => r.1) (fun j => j.1) lev (full p x)
    · rintro ⟨s,i⟩ ⟨t,j⟩ h ht
      exact off p x s t h ht i j
    · intro s
      apply cover_matrix _ (block p x s) (fun i => ⟨⟨s,i⟩,rfl⟩) (fun j => ⟨⟨s,j⟩,rfl⟩)
      · rintro ⟨⟨t,i⟩,ht⟩
        change t=s at ht
        subst t
        exact ⟨i,rfl⟩
      · intro i j; rfl
      · exact hs s
  exact ⟨x,cover_matrix (actual p x) (full p x) (fun r => row p r.1 r.2) (fun j => col p j.1 j.2)
    (row_surj p) (fun _ _ => rfl) hfull⟩

lemma action (x : V p G → ℂ) (z : CC p G → ℂ) (i : Fin p.a) (j : Axis p p.d G) (k : Axis p p.e G) :
    (actual p x).mulVec z (i,j,k) = ∑ t : Pt p G,
      (z (t,.inl i)*(B p x t j*Cc p x t k) + A p x t i*(z (t,.inr (.inl j))*Cc p x t k) +
      A p x t i*(B p x t j*z (t,.inr (.inr k)))) := by
  classical
  change (∑ w : CC p G, tangent p x (i,j,k) w*z w)=_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp [tangent,ite_mul,Finset.sum_ite_eq']
  ring

end CriticalTensor.RectGrowth

namespace CriticalTensor

open RectGrowth

/-- A base block, its border with one regular block, and an ordered pair of regular
blocks suffice to extend both axes by the same number of regular blocks. -/
lemma grow_rect (a d e h base extra t : ℕ) (hb : Spans a d e base)
    (hr : RectBorder a d e h base extra) (hc : Cross a h extra) :
    Spans a (d+h*t) (e+h*t) (base+extra*t) := by
  classical
  let p : Dimensions := ⟨a,d,e,h,base,extra⟩
  let G := Fin t
  let left : Fin (d+h*t) ≃ Axis p p.d G := Fintype.equivOfCardEq (by simp [G,p,Axis,Nat.mul_comm])
  let right : Fin (e+h*t) ≃ Axis p p.e G := Fintype.equivOfCardEq (by simp [G,p,Axis,Nat.mul_comm])
  let f : Fin (base+extra*t) ≃ Pt p G := Fintype.equivOfCardEq (by simp [G,p,Pt,Nat.mul_comm])
  obtain ⟨x,hx⟩ := common p (G:=G) hb hr hc
  refine ⟨fun t i => A p x (f t) i,fun t j => B p x (f t) (left j),fun t k => Cc p x (f t) (right k),?_⟩
  intro T
  obtain ⟨z,hz⟩ := hx fun r => T r.1 (left.symm r.2.1) (right.symm r.2.2)
  refine ⟨fun t i => z (f t,.inl i),fun t j => z (f t,.inr (.inl (left j))),
    fun t k => z (f t,.inr (.inr (right k))),?_⟩
  intro i j k
  have hw := (congrFun hz (i,left j,right k)).symm
  simp only [Equiv.symm_apply_apply] at hw
  rw [action] at hw
  exact hw.trans (f.sum_comp (fun t => z (t,Sum.inl i)*(B p x t (left j)*Cc p x t (right k)) +
    A p x t i*(z (t,Sum.inr (Sum.inl (left j)))*Cc p x t (right k)) +
    A p x t i*(B p x t (left j)*z (t,Sum.inr (Sum.inr (right k)))))).symm

end CriticalTensor

namespace CriticalTensor

/-- Independent crossed blocks on complementary first-axis subspaces may be combined. -/
lemma cross_add {a b h n m : ℕ} (hl : Cross a h n) (hr : Cross b h m) : Cross (a+b) h (n+m) := by
  classical
  obtain ⟨xl,ul,yl,zl,hl⟩ := hl
  obtain ⟨xr,ur,yr,zr,hr⟩ := hr
  let e : Fin a ⊕ Fin b ≃ Fin (a+b) := finSumFinEquiv
  let p : Fin n ⊕ Fin m ≃ Fin (n+m) := finSumFinEquiv
  let first (f : Fin n → Fin a → ℂ) (g : Fin m → Fin b → ℂ) (t : Fin (n+m)) (i : Fin (a+b)) : ℂ :=
    (p.symm t).elim (fun s => (e.symm i).elim (f s) 0) (fun s => (e.symm i).elim 0 (g s))
  let second (f : Fin n → Fin h → ℂ) (g : Fin m → Fin h → ℂ) (t : Fin (n+m)) := (p.symm t).elim f g
  refine ⟨first xl xr,first ul ur,second yl yr,second zl zr,?_⟩
  intro T
  obtain ⟨v₁,w₁,h₁⟩ := hl (fun i => T (e (.inl i)))
  obtain ⟨v₂,w₂,h₂⟩ := hr (fun i => T (e (.inr i)))
  refine ⟨second v₁ v₂,second w₁ w₂,?_⟩
  intro i j k
  obtain ⟨s,rfl⟩ := e.surjective i
  let term (t : Fin (n+m)) := first ul ur t (e s)*(second v₁ v₂ t j*second zl zr t k) +
    first xl xr t (e s)*(second yl yr t j*second w₁ w₂ t k)
  change T (e s) j k = ∑ t,term t
  rw [← p.sum_comp term,Fintype.sum_sum_type]
  cases s with
  | inl i => simpa [term,first,second] using h₁ i j k
  | inr i => simpa [term,first,second] using h₂ i j k

private lemma cross_small_two : Cross 2 2 2 := by
  let q (t j : Fin 2) : ℂ := if t=j then 1 else 0
  refine ⟨fun _ i => if i=0 then 1 else 0,fun _ i => if i=1 then 1 else 0,q,q,?_⟩
  intro T
  refine ⟨fun t j => T 1 j t,fun t k => T 0 t k,?_⟩
  intro i j k
  fin_cases i <;> simp [q,ite_mul,mul_ite,Finset.sum_ite_eq']

/-- The two crossed groups on three first coordinates give a unimodular twelve-by-twelve matrix. -/
private lemma cross_small_three : Cross 3 2 3 := by
  let x₁ : Fin 3 → Fin 3 → ℂ := ![![1,0,0],![0,1,0],![0,0,1]]
  let x₂ : Fin 3 → Fin 3 → ℂ := ![![1,0,1],![0,1,1],![1,1,1]]
  let b : Fin 3 → Fin 2 → ℂ := ![![1,0],![0,1],![1,1]]
  refine ⟨x₁,x₂,b,b,?_⟩
  intro T
  let v : Fin 3 → Fin 2 → ℂ := ![
    ![T 0 1 0 - T 1 0 0 + T 2 0 0 - T 2 1 0, T 0 1 0 - T 0 1 1],
    ![-T 1 0 0 + T 1 0 1, -T 0 1 1 + T 1 0 1 - T 2 0 1 + T 2 1 1],
    ![T 1 0 0, T 0 1 1]]
  let w : Fin 3 → Fin 2 → ℂ := ![
    ![T 0 0 0 - T 0 1 0 - T 2 0 0 + T 2 1 0, T 0 0 1 - T 1 0 0],
    ![-T 0 1 1 + T 1 1 0, -T 1 0 1 + T 1 1 1 + T 2 0 1 - T 2 1 1],
    ![-T 0 1 0 + T 2 1 0, -T 1 0 1 + T 2 0 1]]
  refine ⟨v,w,?_⟩
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [Fin.sum_univ_three,Matrix.cons_val_two,x₁,x₂,b,v,w] <;> ring_nf <;> rfl

/-- At width two, two groups with one point per first coordinate span all crossed rows. -/
lemma cross_width_two (a : ℕ) (ha : 2 ≤ a) : Cross a 2 a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases h₂ : a=2
    · simpa [h₂] using cross_small_two
    by_cases h₃ : a=3
    · simpa [h₃] using cross_small_three
    have hsmall : Cross (a-2) 2 (a-2) := ih (a-2) (by omega) (by omega)
    simpa only [show a-2+2=a by omega] using cross_add hsmall cross_small_two

end CriticalTensor

namespace CriticalTensor.ConsecutiveBorder.Binary

def intBit (b : Bool) : ℤ := if b then 1 else 0
def fieldBit (b : Bool) : ZMod 2 := if b then 1 else 0

lemma cast_intBit (b : Bool) : ((intBit b : ℤ) : ZMod 2) = fieldBit b := by cases b <;> rfl

lemma fieldBit_xor (a b : Bool) : fieldBit (a ^^ b) = fieldBit a + fieldBit b := by
  cases a <;> cases b <;> decide

/-- XOR of the columns whose index occurs in the mask. -/
def xorColumns (cols : ℕ → ℕ) (mask : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => xorColumns cols mask m ^^^ (if mask.testBit m then cols m else 0)

lemma xorColumns_entry (cols : ℕ → ℕ) (mask row m : ℕ) :
    fieldBit ((xorColumns cols mask m).testBit row) =
      ∑ j ∈ Finset.range m, fieldBit ((cols j).testBit row) * fieldBit (mask.testBit j) := by
  induction m with
  | zero => simp [xorColumns, fieldBit]
  | succ m ih =>
    rw [xorColumns, Nat.testBit_xor, fieldBit_xor, ih, Finset.sum_range_succ]
    cases mask.testBit m <;> simp [fieldBit]

lemma complex_surjectivity {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℤ) (B : Matrix κ ι ℤ)
    (hab : A.map (Int.castRingHom (ZMod 2)) * B.map (Int.castRingHom (ZMod 2)) = 1) :
    Function.Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  let C := A * B
  have h2 : ((C.det : ℤ) : ZMod 2) = 1 := by
    change (Int.castRingHom (ZMod 2)) C.det = 1
    rw [RingHom.map_det, RingHom.mapMatrix_apply, show C = A * B from rfl, Matrix.map_mul, hab,
      Matrix.det_one]
  have hne : C.det ≠ 0 := by
    intro he
    rw [he, Int.cast_zero] at h2
    exact zero_ne_one h2
  have hu : IsUnit (C.map (Int.castRingHom ℂ)).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    change (C.det : ℂ) ≠ 0
    exact_mod_cast hne
  have hsurj : Function.Surjective (C.map (Int.castRingHom ℂ)).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  refine ⟨(B.map (Int.castRingHom ℂ)).mulVec x, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul]
  exact hx

lemma surjective_of_certificate {d m : ℕ} (A : Matrix (Fin d) (Fin m) ℤ) (cols masks : ℕ → ℕ)
    (hcols : ∀ i j, A i j = intBit ((cols j.val).testBit i.val))
    (hcheck : ∀ i : Fin d, xorColumns cols (masks i.val) m = 2 ^ i.val) :
    Function.Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  let B : Matrix (Fin m) (Fin d) ℤ := fun j i => intBit ((masks i.val).testBit j.val)
  apply complex_surjectivity A B
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  calc
    _ = ∑ k : Fin m, fieldBit ((cols k.val).testBit i.val) * fieldBit ((masks j.val).testBit k.val) := by
      apply Finset.sum_congr rfl
      intro k _
      change ((A i k : ℤ) : ZMod 2) * ((intBit ((masks j.val).testBit k.val) : ℤ) : ZMod 2) = _
      rw [hcols, cast_intBit, cast_intBit]
    _ = ∑ k ∈ Finset.range m, fieldBit ((cols k).testBit i.val) * fieldBit ((masks j.val).testBit k) := by
      exact Fin.sum_univ_eq_sum_range (fun k => fieldBit ((cols k).testBit i.val) *
        fieldBit ((masks j.val).testBit k)) m
    _ = fieldBit ((xorColumns cols (masks j.val) m).testBit i.val) := (xorColumns_entry _ _ _ _).symm
    _ = _ := by
      rw [hcheck j, Nat.testBit_two_pow]
      by_cases h : i = j
      · subst j; simp [fieldBit]
      · have hji : j.val ≠ i.val := fun hv => h (Fin.ext hv.symm)
        simp [h, hji, fieldBit]

end CriticalTensor.ConsecutiveBorder.Binary



namespace CriticalTensor.RectFiveBase

open CriticalTensor.ConsecutiveBorder.Binary

private lemma lift_surj {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] (A : Matrix I K ℤ)
    (h : Function.Surjective (A.map (Int.castRingHom (ZMod 2))).mulVec) :
    Function.Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  obtain ⟨b,hb⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h
  let B : Matrix K I ℤ := fun j i => (b j i).val
  have he : B.map (Int.castRingHom (ZMod 2)) = b := by
    ext i j
    change (((b i j).val : ℤ) : ZMod 2) = b i j
    simp
  apply complex_surjectivity A B
  rwa [he]

def fit (w i : ℕ) : Bool := w.testBit i && (w >>> (i+1) == 0)

private lemma off_bit {w i j : ℕ} (h : fit w i = true) (hj : i<j) : w.testBit j = false := by
  have he := congrArg (fun z : ℕ => z.testBit (j-(i+1))) (beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2)
  simp only [Nat.testBit_shiftRight,Nat.zero_testBit] at he
  rwa [show i+1+(j-(i+1))=j by omega] at he

/-- Decode consecutive 16-bit blocks. Zero and one- or two-bit blocks
are represented by flags and positions. Other blocks store all sixteen bits. -/
def unpack16 : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, v =>
    if v=0 then 0
    else if v%2=0 then (unpack16 n (v >>> 1)) <<< 16
    else if v%4=1 then (1 <<< ((v >>> 2)%16)) ||| ((unpack16 n (v >>> 6)) <<< 16)
    else if v%8=3 then (1 <<< ((v >>> 3)%16)) ||| (1 <<< ((v >>> 7)%16)) |||
      ((unpack16 n (v >>> 11)) <<< 16)
    else ((v >>> 3)%65536) ||| ((unpack16 n (v >>> 19)) <<< 16)

def window (f : ℕ → Bool) (start : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => window f start n && f (start+n)

def Before (f : ℕ → Bool) (b : ℕ) := ∀ i < b, f i = true

lemma before_zero (f : ℕ → Bool) : Before f 0 := fun _ h => by omega

lemma extend {f : ℕ → Bool} {b n : ℕ} (earlier : Before f b) (h : window f b n = true) :
    Before f (b+n) := by
  induction n with
  | zero => simpa using earlier
  | succ n ih =>
    obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp h
    intro i hi
    by_cases h' : i < b+n
    · exact ih h₁ i h'
    · have he : i=b+n := by omega
      exact he ▸ h₂

structure RowWindow (f : ℕ → Bool) (n : ℕ) : Type where
  verified : Before f n

def start (f : ℕ → Bool) : RowWindow f 0 := ⟨before_zero f⟩

def nextWindow {f : ℕ → Bool} {b : ℕ} (prev : RowWindow f b) (n : ℕ)
    (h : window f b n = true) : RowWindow f (b+n) := ⟨extend prev.verified h⟩

end CriticalTensor.RectFiveBase

namespace CriticalTensor.RectFiveBase

open CriticalTensor.ConsecutiveBorder.Binary

private abbrev R (d e a : ℕ) := Fin d × Fin e × Fin a
private abbrev C (d e a n : ℕ) := (Fin n × Fin d) ⊕ ((Fin n × Fin e) ⊕ (Fin n × Fin a))

def rowOrder (d e a : ℕ) : R d e a ≃ Fin (d*(e*a)) :=
  ((Equiv.refl (Fin d)).prodCongr finProdFinEquiv).trans finProdFinEquiv

private def coordinate (data : Array ℕ) (t axis i : ℕ) := (data[t*3+axis]?.getD 0).testBit i

private def matrix {d e a n : ℕ} (data : Array ℕ) : Matrix (R d e a) (C d e a n) ℤ
  | (i,j,k),.inl (t,h) => if h=i then intBit (coordinate data t.val 1 j.val)*intBit (coordinate data t.val 2 k.val) else 0
  | (i,j,k),.inr (.inl (t,h)) => if h=j then intBit (coordinate data t.val 0 i.val)*intBit (coordinate data t.val 2 k.val) else 0
  | (i,j,k),.inr (.inr (t,h)) => if h=k then intBit (coordinate data t.val 0 i.val)*intBit (coordinate data t.val 1 j.val) else 0

private def index {d e a n : ℕ} : C d e a n → ℕ
  | .inl (t,h) => t.val*d+h.val
  | .inr (.inl (t,h)) => n*d+t.val*e+h.val
  | .inr (.inr (t,h)) => n*(d+e)+t.val*a+h.val

private lemma spans_of_rank {d e a n : ℕ} (data : Array ℕ)
    (h : Function.Surjective ((matrix (d:=d) (e:=e) (a:=a) (n:=n) data).map (Int.castRingHom ℂ)).mulVec) :
    CriticalTensor.Spans a d e n := by
  let x (t : Fin n) (i : Fin a) : ℂ := (intBit (coordinate data t.val 2 i.val) : ℤ)
  let y (t : Fin n) (j : Fin d) : ℂ := (intBit (coordinate data t.val 0 j.val) : ℤ)
  let z (t : Fin n) (k : Fin e) : ℂ := (intBit (coordinate data t.val 1 k.val) : ℤ)
  refine ⟨x,y,z,?_⟩
  intro T
  obtain ⟨v,hv⟩ := h (fun r => T r.2.2 r.1 r.2.1)
  refine ⟨fun t i => v (.inr (.inr (t,i))),fun t j => v (.inl (t,j)),fun t k => v (.inr (.inl (t,k))),?_⟩
  intro i j k
  refine (congrFun hv (j,k,i)).symm.trans ?_
  change (∑ p : C d e a n, ((matrix data (j,k,i) p : ℤ) : ℂ)*v p) = _
  simp [matrix,x,y,z,Fintype.sum_sum_type,Fintype.sum_prod_type,apply_ite,ite_mul,
    Finset.sum_ite_eq']
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  ring

private def addTerm (x y : Bool) (b z : ℕ) := if x && y then b ^^^ z else z

private lemma bit_addTerm (x y : Bool) (b z j : ℕ) :
    fieldBit ((addTerm x y b z).testBit j) = ((intBit x * intBit y : ℤ) : ZMod 2)*
      fieldBit (b.testBit j) + fieldBit (z.testBit j) := by
  cases x <;> cases y <;> simp [addTerm,intBit,Nat.testBit_xor,fieldBit_xor]

private def sweep (f : ℕ → ℕ → ℕ) (z : ℕ) : ℕ → ℕ
  | 0 => z
  | t+1 => f t (sweep f z t)

private def family (n : ℕ) (x y : ℕ → Bool) (b : ℕ → ℕ) (z : ℕ) :=
  sweep (fun t => addTerm (x t) (y t) (b t)) z n

private lemma bit_family (n : ℕ) (x y : ℕ → Bool) (b : ℕ → ℕ) (z j : ℕ) :
    fieldBit ((family n x y b z).testBit j) =
      (∑ t : Fin n, ((intBit (x t.val)*intBit (y t.val) : ℤ) : ZMod 2)*fieldBit ((b t.val).testBit j)) +
        fieldBit (z.testBit j) := by
  induction n with
  | zero => simp [family,sweep]
  | succ n ih =>
    change fieldBit ((addTerm (x n) (y n) (b n) (family n x y b z)).testBit j)=_
    rw [bit_addTerm,ih,Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    abel

/-- Multiply one geometric row by all proposed triangular columns in parallel. -/
def rowProduct (d e a n : ℕ) (data : Array ℕ) (b : ℕ → ℕ) (i j k : ℕ) :=
  let u := family n (fun t => coordinate data t 1 j) (fun t => coordinate data t 2 k) (fun t => b (t*d+i)) 0
  let v := family n (fun t => coordinate data t 0 i) (fun t => coordinate data t 2 k) (fun t => b (n*d+t*e+j)) u
  family n (fun t => coordinate data t 0 i) (fun t => coordinate data t 1 j) (fun t => b (n*(d+e)+t*a+k)) v

private lemma row_product_entry {d e a : ℕ} (n : ℕ) (data : Array ℕ) (b : ℕ → ℕ)
    (i : Fin d) (j : Fin e) (k : Fin a) (h : ℕ) :
    fieldBit ((rowProduct d e a n data b i.val j.val k.val).testBit h) =
      ∑ t : C d e a n, ((matrix data (i,j,k) t : ℤ) : ZMod 2)*fieldBit ((b (index t)).testBit h) := by
  unfold rowProduct
  rw [bit_family,bit_family,bit_family]
  have hz : fieldBit ((0 : ℕ).testBit h) = 0 := by simp [fieldBit]
  rw [hz,add_zero]
  simp [Fintype.sum_sum_type,Fintype.sum_prod_type,matrix,index,apply_ite,ite_mul]
  abel

lemma checked {d e a n : ℕ} (data : Array ℕ) (b : ℕ → ℕ)
    (h : ∀ q : Fin (d*(e*a)), let p := (rowOrder d e a).symm q
      fit (rowProduct d e a n data b p.1.val p.2.1.val p.2.2.val) q.val = true) :
    CriticalTensor.Spans a d e n := by
  let E := rowOrder d e a
  let M : Matrix (Fin (d*(e*a))) (C d e a n) ℤ := fun q t => matrix data (E.symm q) t
  let N := M.map (Int.castRingHom (ZMod 2))
  let B : Matrix (C d e a n) (Fin (d*(e*a))) (ZMod 2) := fun t q => fieldBit ((b (index t)).testBit q.val)
  let L := N*B
  let row (i : Fin (d*(e*a))) := rowProduct d e a n data b (E.symm i).1.val (E.symm i).2.1.val (E.symm i).2.2.val
  have read (i j : Fin (d*(e*a))) : L i j = fieldBit ((row i).testBit j.val) :=
    (row_product_entry n data b (E.symm i).1 (E.symm i).2.1 (E.symm i).2.2 j.val).symm
  have ht : L.IsLowerTriangular := by
    intro i j hij
    change i.val < j.val at hij
    have hb : (row i).testBit j.val=false := off_bit (h i) hij
    rw [read,hb]
    rfl
  have hd : L.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular L ht]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have hb : (row i).testBit i.val=true := (Bool.and_eq_true_iff.mp (h i)).1
    rw [read,hb]
    exact one_ne_zero
  have hl : Function.Surjective L.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  have hn : Function.Surjective N.mulVec := by
    intro y
    obtain ⟨z,hz⟩ := hl y
    exact ⟨B.mulVec z,(Matrix.mulVec_mulVec _ _ _).trans hz⟩
  have hs := lift_surj M hn
  apply spans_of_rank data
  intro y
  obtain ⟨z,hz⟩ := hs (y ∘ E.symm)
  refine ⟨z,?_⟩
  funext i
  have h' := congrFun hz (E i)
  change (∑ t, ((M (E i) t : ℤ) : ℂ)*z t) = y (E.symm (E i)) at h'
  change (∑ t, ((matrix data i t : ℤ) : ℂ)*z t)=y i
  simpa only [M,Equiv.symm_apply_apply] using h'

end CriticalTensor.RectFiveBase

namespace CriticalTensor.RectFiveBase.Five

private def factors : Array ℕ := #[0x1, 0x1, 0x1, 0x2, 0x2, 0x2, 0x4, 0x4, 0x4, 0x8, 0x8, 0x8, 0x10, 0x10, 0x10, 0x19, 0x20, 0xf, 0x15, 0x1f, 0x19, 0xe, 0x26, 0x13, 0x11, 0x35, 0x1b, 0x1a, 0x21, 0x1d, 0x5, 0x29, 0x1]
private def unpack := unpack16 10

private def t0 : Array ℕ := #[
  0x603208220c128536880003000000026000001,
  unpack 0x4360fdb01c45ff5f2,
  0,
  unpack 0x7b831073f9ca60,
  (0x28c27 <<< 120),
  unpack 0x4c3f7d59be8c01e07,
  unpack 0xa0997f86aab08c,
  unpack 0x261a930,
  (0x2b <<< 96),
  (0xca3 <<< 126),
  unpack 0xc20cf63,
  unpack 0x29a4,
  0,
  (0x5 <<< 102),
  (0x1 <<< 132),
  unpack 0x128d31780f512]

private def t1 : Array ℕ := #[
  unpack 0x8,
  unpack 0x1082ff30,
  0,
  (0x601 <<< 138),
  unpack 0x210604a3842,
  unpack 0xc8,
  unpack 0x10bd5a20,
  unpack 0x480,
  0,
  unpack 0x125070251d8eada6,
  unpack 0x86c1fb601a038,
  (0x6000062007044a05 <<< 86),
  unpack 0xd0620c380,
  0,
  0,
  0]

private def t2 : Array ℕ := #[
  unpack 0x2618d37d0,
  unpack 0xf40,
  unpack 0x100,
  unpack 0x10a00a3825,
  unpack 0x7a1584,
  unpack 0x87c1a0997f960,
  unpack 0xf068221c0,
  (0x25 <<< 131),
  (0x5 <<< 146),
  unpack 0xa8,
  unpack 0x420a0,
  (0x7 <<< 110),
  unpack 0x84d500,
  unpack 0x109cc35604839b8eadb6,
  0,
  (0x30000211028275 <<< 95)]

private def t3 : Array ℕ := #[
  unpack 0x3cf20,
  (0x1 <<< 122),
  unpack 0x62c0493b83f56680e00e,
  (0x15 <<< 45),
  (0x80c400e08d41b <<< 85),
  unpack 0x85800e380,
  (0x3005 <<< 135),
  0,
  unpack 0x340065c01d07,
  unpack 0x249fc1a09d7820afecc5d3,
  0xa03258880413283609800200000000e008000,
  unpack 0x52634002f800b0e,
  0,
  unpack 0x3d5802f8dab7a,
  0,
  unpack 0xf5730c94]

private def t4 : Array ℕ := #[
  (0x9 <<< 46),
  (0x3 <<< 51),
  unpack 0xaad817c41c038,
  unpack 0x86c0c078440f4132fe6dc8,
  unpack 0x7a68d0,
  unpack 0x7a6a10,
  unpack 0x2618d3750,
  unpack 0x6920,
  unpack 0x986ec01478760,
  unpack 0x3cea0,
  unpack 0x1e4c0,
  (0x283 <<< 103),
  0,
  unpack 0x280,
  unpack 0x21385d980,
  (0x1 <<< 124)]

private def t5 : Array ℕ := #[
  (0x15 <<< 129),
  (0x1 <<< 134),
  (0x301 <<< 139),
  0,
  (0x1 <<< 149),
  unpack 0x79ec60,
  unpack 0x681d,
  unpack 0x10839,
  unpack 0x130c69a0,
  unpack 0x80,
  0,
  unpack 0x86c10881e8275fdf07e8,
  unpack 0x10dbd8028e6fa30,
  (0x3 <<< 147),
  0,
  unpack 0x4370a00a383a]

private def t6 : Array ℕ := #[
  unpack 0x86ce80,
  unpack 0x1082e368,
  unpack 0x1c112ff2d50,
  0,
  unpack 0x28,
  (0xd <<< 50),
  unpack 0x10dc03fb61710,
  unpack 0x109ab280,
  unpack 0x987e8df4621,
  unpack 0x42640947075b,
  unpack 0x4c31a6e3a8,
  unpack 0x21384102a,
  0,
  0,
  unpack 0x7a62c0,
  (0x1 <<< 127)]

private def t7 : Array ℕ := #[
  unpack 0xf4,
  unpack 0x88,
  unpack 0x10d83680,
  (0x1800282801c112836810019 <<< 60),
  unpack 0x14ffd6001970,
  (0x4a4800504ea082a01 <<< 70),
  (0x3000505003822506d11 <<< 75),
  unpack 0x253ff5fab000be0,
  0,
  0,
  unpack 0x2b20f9ec78ea045,
  unpack 0x10995c120fd8f1d45085c9,
  0xc02210aa0801ad0029000a000000028002008,
  unpack 0x64c0c878550fc112fef83f45011d1,
  unpack 0xe08c7f96aab06c,
  0]

private def t8 : Array ℕ := #[
  unpack 0x18b2954,
  unpack 0x3162b6cc,
  unpack 0xe08c7f96aaa2301c,
  0,
  unpack 0x841c112f0205dd0,
  0,
  unpack 0x10fb0051cc5fcb0,
  (0x402000504ea082a1 <<< 74),
  (0x30180001c41 <<< 105),
  unpack 0x986a40,
  unpack 0x986b40,
  unpack 0x130df8c0,
  (0x5 <<< 109),
  (0x1 <<< 140),
  (0x1 <<< 141),
  (0x1 <<< 142)]

private def t9 : Array ℕ := #[
  (0x1 <<< 143),
  unpack 0x200,
  (0xb <<< 145),
  unpack 0x22507086a,
  (0x1 <<< 148),
  unpack 0x130b838028e28262,
  (0x5 <<< 117),
  (0xc0114d <<< 125),
  (0x1 <<< 136),
  (0x1 <<< 99),
  unpack 0x43730deac0,
  (0xc01 <<< 137),
  0,
  unpack 0x1efab9860,
  unpack 0x3d148,
  unpack 0x7a15b4]

private def t10 : Array ℕ := #[
  unpack 0xc4,
  (0xc9 <<< 130),
  0,
  unpack 0x26832,
  unpack 0x130c6835,
  unpack 0x986840,
  unpack 0x43700fed85c6a58,
  unpack 0x10bd5800e0,
  unpack 0x4,
  unpack 0x1514,
  unpack 0x420b8dab24,
  0,
  unpack 0x108c7502,
  unpack 0x130c340a,
  unpack 0x10dc28028e62c10,
  unpack 0x10dc234dc751a]

private def tables := #[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10]
private def multiplier (j : ℕ) := ((tables[j/16]?.getD #[])[j%16]?).getD 0

private def checkAt (i : ℕ) : Bool :=
  let p := (rowOrder 5 6 5).symm (Fin.ofNat 150 i)
  fit (rowProduct 5 6 5 11 factors multiplier p.1.val p.2.1.val p.2.2.val) i

private def w8 : RowWindow checkAt 8 := nextWindow (start checkAt) 8 (by decide +kernel)
private def w16 : RowWindow checkAt 16 := nextWindow w8 8 (by decide +kernel)
private def w24 : RowWindow checkAt 24 := nextWindow w16 8 (by decide +kernel)
private def w32 : RowWindow checkAt 32 := nextWindow w24 8 (by decide +kernel)
private def w40 : RowWindow checkAt 40 := nextWindow w32 8 (by decide +kernel)
private def w48 : RowWindow checkAt 48 := nextWindow w40 8 (by decide +kernel)
private def w56 : RowWindow checkAt 56 := nextWindow w48 8 (by decide +kernel)
private def w64 : RowWindow checkAt 64 := nextWindow w56 8 (by decide +kernel)
private def w72 : RowWindow checkAt 72 := nextWindow w64 8 (by decide +kernel)
private def w80 : RowWindow checkAt 80 := nextWindow w72 8 (by decide +kernel)
private def w88 : RowWindow checkAt 88 := nextWindow w80 8 (by decide +kernel)
private def w96 : RowWindow checkAt 96 := nextWindow w88 8 (by decide +kernel)
private def w104 : RowWindow checkAt 104 := nextWindow w96 8 (by decide +kernel)
private def w112 : RowWindow checkAt 112 := nextWindow w104 8 (by decide +kernel)
private def w120 : RowWindow checkAt 120 := nextWindow w112 8 (by decide +kernel)
private def w128 : RowWindow checkAt 128 := nextWindow w120 8 (by decide +kernel)
private def w136 : RowWindow checkAt 136 := nextWindow w128 8 (by decide +kernel)
private def w144 : RowWindow checkAt 144 := nextWindow w136 8 (by decide +kernel)
private def w150 : RowWindow checkAt 150 := nextWindow w144 6 (by decide +kernel)

theorem spans : CriticalTensor.Spans 5 5 6 11 := by
  apply checked factors multiplier
  intro i
  have h := w150.verified i.val i.isLt
  have he : Fin.ofNat 150 i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simpa only [checkAt,he] using h

end CriticalTensor.RectFiveBase.Five

namespace CriticalTensor.RectFiveBase

theorem base_five : CriticalTensor.Spans 5 5 6 11 := Five.spans

end CriticalTensor.RectFiveBase

namespace CriticalTensor.RectFiveBase.Six

private def factors : Array ℕ := #[0x1, 0x1, 0x1, 0x2, 0x2, 0x2, 0x4, 0x4, 0x4, 0x8, 0x8, 0x8, 0x10, 0x10, 0x10, 0x20, 0x20, 0xd, 0x1b, 0x40, 0x11, 0x7, 0x4b, 0xa, 0x22, 0x17, 0x9, 0x36, 0x5b, 0x1e, 0x3e, 0x2a, 0xf, 0x37, 0x6c, 0x14, 0x2e, 0x1e, 0x14, 0x3f, 0x5f, 0x11]
private def unpack := unpack16 14

private def t0 : Array ℕ := #[
  unpack 0x4190307da7a842170340e883aee83,
  unpack 0x1e004faece00382903fad79d82e6c,
  unpack 0x38183ed3cb60250e74a103d330,
  unpack 0x20e0113ebb19206c401c0,
  unpack 0x322fe300,
  (0x1c0c0491d <<< 175),
  unpack 0x1a84217647a8ddd6728e90a07,
  unpack 0x1c04bc101c0e2dbe8dd6651b2394,
  unpack 0x3eb5d84217647a8dd7630,
  unpack 0x1f44301d0903f40,
  unpack 0x3e9d42600,
  unpack 0x1f7d5800,
  unpack 0x3fcf5dc6640763,
  unpack 0x14060f4ea1a05f4,
  0,
  unpack 0x65d580]

private def t1 : Array ℕ := #[
  (0x36020240038c021 <<< 152),
  (0x80027 <<< 187),
  unpack 0x9668eaeeb394726,
  unpack 0x4010fa761301c480bdcbf46d6728fd58,
  unpack 0x1f5aec210bb23d46d860,
  unpack 0x3ea19660231f6d80,
  unpack 0x3eb5df200,
  (0x17031 <<< 193),
  unpack 0x18050ed4cea2942,
  unpack 0xc8675168,
  unpack 0x1035c31a40f29cdf20,
  (0x21 <<< 129),
  (0x2e0152000015 <<< 164),
  unpack 0x5d000,
  0x18000000,
  unpack 0x1dac4301c0207b18]

private def t2 : Array ℕ := #[
  unpack 0x7d3a081fa0,
  unpack 0x140c1f69c3b19300,
  unpack 0x1f403c1c00,
  0,
  unpack 0x178197ed3a404a1d0824,
  unpack 0x5c065fb4f6980943a128b0,
  unpack 0x1492408e5081f25ca440,
  unpack 0x41c002f6d35bb00,
  0,
  0,
  unpack 0x1480d3d30ba80a1fd1abace51c5b0807,
  unpack 0x8043e9c863581d2043d00875759ca30,
  unpack 0xa4049e985de468abb6f90,
  unpack 0x1110a0487a40,
  unpack 0x58074f4dc31210e00,
  0]

private def t3 : Array ℕ := #[
  unpack 0x350a02eca20775,
  (0x40184101 <<< 178),
  unpack 0x1dd660,
  unpack 0x48087d3b5ac903e40,
  unpack 0x6a1085fd00,
  0,
  unpack 0x509b21e280a1c0179,
  unpack 0x1c024f4e5bc7900,
  unpack 0xb4009d6ce54050e5a0,
  unpack 0xe030f4e2679d80,
  (0x9015 <<< 194),
  (0x601 <<< 197),
  (0x1 <<< 168),
  unpack 0x76b6c301918,
  0,
  unpack 0x108d00]

private def t4 : Array ℕ := #[
  (0x5 <<< 166),
  (0x1 <<< 191),
  unpack 0x28193d43d714050e00a,
  unpack 0x4ec3d878f2128,
  unpack 0x13b0f61e3c8db960,
  (0x103 <<< 126),
  unpack 0x12064f50f5dea00,
  0,
  unpack 0xe0027871c50143802f3b,
  unpack 0x41b0127a863201f1e42458,
  unpack 0x43bd714250e340,
  unpack 0x836020f4e267021380,
  unpack 0x7c9c2c9a00,
  0,
  (0x18045 <<< 192),
  (0x1c0029 <<< 189)]

private def t5 : Array ℕ := #[
  (0x6c048001 <<< 179),
  unpack 0x107000bda8d40,
  0,
  0,
  0,
  unpack 0x168183ed3b4610bcb3440e91107,
  unpack 0x5e065f4e322d9440eed3,
  unpack 0x10640c1f69edb1240f2cc037d,
  unpack 0x832035fb4d22da8c52746,
  unpack 0x3e86403a00e,
  unpack 0xc002f6db1a40f68544f2,
  unpack 0x10025e0b36cc2143feb328501cc8c,
  0,
  unpack 0x106c041c1c7164d0e4,
  unpack 0xb012fa48503db30850ffac4401638,
  unpack 0x41b01070719e4b646108]

private def t6 : Array ℕ := #[
  unpack 0x76b6c3009a8,
  unpack 0x2804be9b663081ed1ea2130,
  unpack 0x5f574e33c96c8cb610,
  unpack 0xf002776d9e4b9667759feb0,
  unpack 0x41e0227746403809439a0a04e0,
  unpack 0x3002776d9e4b949760,
  unpack 0xf002774a503e4b946e20,
  unpack 0x1f40001dc0,
  unpack 0x83e040fadb3c972cd0cc0,
  unpack 0x12021f4ef59160015fd8c0,
  unpack 0x24043e9dec30a40e02a1f4580,
  unpack 0x9010fa760a40ec8f5980,
  0,
  unpack 0x24043e9d829038028f00,
  unpack 0x90307da709500,
  unpack 0x6a1085e900]

private def t7 : Array ℕ := #[
  unpack 0xac08bf50200,
  unpack 0x158117eacaa00,
  unpack 0x2022f0c607da600,
  unpack 0x41f022fd759fa00,
  0,
  unpack 0xfa9400,
  unpack 0x3cae9e400,
  unpack 0xc4e85800,
  (0xd818205 <<< 182),
  (0x260411 <<< 188),
  (0xc0197 <<< 190),
  (0x4c01 <<< 195),
  (0x1 <<< 203),
  0,
  unpack 0x20fc192047c6792d9196d274,
  unpack 0x38097904470940f92c09239037759da25]

private def t8 : Array ℕ := #[
  (0x70129b <<< 185),
  unpack 0xe025e4111ca503e4b94541a,
  unpack 0x703072088faced9b3abbb4d48,
  unpack 0x486a,
  (0xd018090007 <<< 170),
  unpack 0xe4c88487d865754090e64,
  unpack 0x722900e1185d1a010eeac0,
  unpack 0x41b0107a72dbaca2076d,
  unpack 0xe570f167d5759ca02,
  unpack 0x1580d3d370dc8d102a,
  unpack 0x438ec052,
  0,
  unpack 0x313259b6610a1ff5bbaf3b0,
  (0x3606005d <<< 180),
  unpack 0x15810793889207647a6dd01d4,
  unpack 0x3002776d9e4b94201538]

private def t9 : Array ℕ := #[
  unpack 0xac083c9c6792d919d29d8,
  unpack 0x3e8007f98,
  unpack 0x2804be9b663401ed00,
  unpack 0xb6788f500,
  unpack 0x36198dc002f6a0,
  (0x1 <<< 171),
  unpack 0x43b33e80,
  0,
  0,
  0,
  unpack 0x107eadc6100,
  unpack 0x20fd6a348180,
  unpack 0x41b0107a7132680,
  (0x1 <<< 209),
  (0x3801 <<< 196),
  unpack 0x3ea1d8040]

private def t10 : Array ℕ := #[
  (0xf <<< 206),
  unpack 0xe02a7328b0207e776854,
  (0x1c05001 <<< 184),
  0,
  unpack 0x1c054faeb8f2300,
  unpack 0x30043c308032,
  unpack 0x9d87b0f1e46062,
  unpack 0x200c3d432900e0250e840,
  unpack 0x836030f4e5bc619f3bb40,
  unpack 0xfa36c33d7376cfd0,
  0,
  unpack 0x481c3ed3d7647d0c8,
  0,
  unpack 0x140c1f69c2646010,
  unpack 0x20e8143eb680d0,
  unpack 0x83f264811ce103ca02a1cb690]

private def t11 : Array ℕ := #[
  unpack 0x2c041c8223db3c960491c81bbaced0,
  (0x32003 <<< 172),
  unpack 0x1c040e0911ca103e4b9662a0,
  unpack 0x703af2088ecdb31dda60,
  unpack 0xa060fb4e132240,
  0,
  0,
  unpack 0x16cf1190a07f4ca148732e90817,
  unpack 0x1fe61140f88f51f3bb42a2f13,
  unpack 0xa1038c2972110f4021ddd502439941b,
  unpack 0x723940e890887e77687562f23,
  unpack 0x2c0c9c17538c207b6604b1c8017ba4028f84,
  0,
  unpack 0xed61939b2840fe81297a4,
  unpack 0x41a9305d4e4281ed984287fd6eea8b23b4,
  unpack 0xd4c6c81b9b2840fec8bc4]

private def t12 : Array ℕ := #[
  unpack 0x45e2d11f5b5935d2041e0,
  unpack 0x106c041e9c7164d0a0,
  0,
  unpack 0x106c041e9c44903b23d362048e0,
  unpack 0x41b01071288e7201c04a1c0a10e0,
  unpack 0xc0f5deb69b080,
  unpack 0x876837280,
  unpack 0x90307da64301c00b1f100380,
  0,
  unpack 0x87647400380,
  (0x41 <<< 160),
  unpack 0x160193d21285c00,
  unpack 0x100a1c0289c00,
  (0x500c80800129 <<< 163),
  0,
  (0x9 <<< 200)]

private def t13 : Array ℕ := #[
  (0x1 <<< 201),
  (0x3 <<< 202),
  0,
  (0x1 <<< 204),
  unpack 0x148017b2dda10a1d0950,
  unpack 0x72b7167d5759ca7a,
  unpack 0x40307da796d28d0804,
  unpack 0xe5689207647fadd5814,
  0,
  unpack 0x45edb63481e500,
  0,
  unpack 0x59000,
  unpack 0x350842ec8f51bbace50,
  (0x1 <<< 208),
  unpack 0x106c0c3e9dee31a40e8eae808,
  (0x401 <<< 176)]

private def t14 : Array ℕ := #[
  (0xf <<< 205),
  0,
  0,
  unpack 0x90307da6cb200,
  unpack 0x1a84503ca00,
  0,
  unpack 0x6a1140eca3a80,
  unpack 0x3c081f5d400,
  unpack 0x1f4321e8,
  unpack 0xfa7400,
  (0x3 <<< 207),
  0,
  0,
  (0x481809 <<< 186),
  unpack 0x18ec03a,
  unpack 0x28183ed31900]

private def t15 : Array ℕ := #[
  (0x21 <<< 151),
  0,
  (0x7008841 <<< 183),
  unpack 0x16e200,
  0,
  unpack 0xdb63085d91ea3740,
  0,
  unpack 0x168197ed35a00,
  unpack 0x106c041e9cb78b2880,
  0,
  (0x1b01002001c000d01 <<< 145),
  0]

private def tables := #[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15]
private def multiplier (j : ℕ) := ((tables[j/16]?.getD #[])[j%16]?).getD 0

private def checkAt (i : ℕ) : Bool :=
  let p := (rowOrder 6 7 5).symm (Fin.ofNat 210 i)
  fit (rowProduct 6 7 5 14 factors multiplier p.1.val p.2.1.val p.2.2.val) i

private def w8 : RowWindow checkAt 8 := nextWindow (start checkAt) 8 (by decide +kernel)
private def w16 : RowWindow checkAt 16 := nextWindow w8 8 (by decide +kernel)
private def w24 : RowWindow checkAt 24 := nextWindow w16 8 (by decide +kernel)
private def w32 : RowWindow checkAt 32 := nextWindow w24 8 (by decide +kernel)
private def w40 : RowWindow checkAt 40 := nextWindow w32 8 (by decide +kernel)
private def w48 : RowWindow checkAt 48 := nextWindow w40 8 (by decide +kernel)
private def w56 : RowWindow checkAt 56 := nextWindow w48 8 (by decide +kernel)
private def w64 : RowWindow checkAt 64 := nextWindow w56 8 (by decide +kernel)
private def w72 : RowWindow checkAt 72 := nextWindow w64 8 (by decide +kernel)
private def w80 : RowWindow checkAt 80 := nextWindow w72 8 (by decide +kernel)
private def w88 : RowWindow checkAt 88 := nextWindow w80 8 (by decide +kernel)
private def w96 : RowWindow checkAt 96 := nextWindow w88 8 (by decide +kernel)
private def w104 : RowWindow checkAt 104 := nextWindow w96 8 (by decide +kernel)
private def w112 : RowWindow checkAt 112 := nextWindow w104 8 (by decide +kernel)
private def w120 : RowWindow checkAt 120 := nextWindow w112 8 (by decide +kernel)
private def w128 : RowWindow checkAt 128 := nextWindow w120 8 (by decide +kernel)
private def w136 : RowWindow checkAt 136 := nextWindow w128 8 (by decide +kernel)
private def w144 : RowWindow checkAt 144 := nextWindow w136 8 (by decide +kernel)
private def w152 : RowWindow checkAt 152 := nextWindow w144 8 (by decide +kernel)
private def w160 : RowWindow checkAt 160 := nextWindow w152 8 (by decide +kernel)
private def w168 : RowWindow checkAt 168 := nextWindow w160 8 (by decide +kernel)
private def w176 : RowWindow checkAt 176 := nextWindow w168 8 (by decide +kernel)
private def w184 : RowWindow checkAt 184 := nextWindow w176 8 (by decide +kernel)
private def w192 : RowWindow checkAt 192 := nextWindow w184 8 (by decide +kernel)
private def w200 : RowWindow checkAt 200 := nextWindow w192 8 (by decide +kernel)
private def w208 : RowWindow checkAt 208 := nextWindow w200 8 (by decide +kernel)
private def w210 : RowWindow checkAt 210 := nextWindow w208 2 (by decide +kernel)

theorem spans : CriticalTensor.Spans 5 6 7 14 := by
  apply checked factors multiplier
  intro i
  have h := w210.verified i.val i.isLt
  have he : Fin.ofNat 210 i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simpa only [checkAt,he] using h

end CriticalTensor.RectFiveBase.Six

namespace CriticalTensor.RectFiveBase

theorem base_six : CriticalTensor.Spans 5 6 7 14 := Six.spans

end CriticalTensor.RectFiveBase

namespace CriticalTensor.RectFiveBase.Eight

private def factors : Array ℕ := #[0x1, 0x1, 0x1, 0x2, 0x2, 0x2, 0x4, 0x4, 0x4, 0x8, 0x8, 0x8, 0x10, 0x10, 0x10, 0x20, 0x20, 0xb, 0x40, 0x40, 0x13, 0x80, 0x80, 0x9, 0x5b, 0x100, 0x5, 0x2a, 0x148, 0x1f, 0x46, 0x186, 0x3, 0x88, 0x55, 0xc, 0x35, 0x17d, 0x1e, 0xf4, 0x1e0, 0x11, 0x5a, 0x194, 0xf, 0xba, 0x112, 0x12, 0xeb, 0x49, 0x15, 0x63, 0x17a, 0xe]
private def unpack := unpack16 23

private def t0 : Array ℕ := #[
  unpack 0x3a301c3fc4c1483841874044e848061c000fa62c1,
  unpack 0xeba4cc3516c88817390169fac,
  unpack 0x44850f80004c00e0,
  unpack 0xd0f82d0813830870a3ae48a724b6add00,
  unpack 0xc8c850f920671c2863b28455d1800,
  unpack 0xe8ca207f22031c28eb8440bc2003dc000,
  (0x240c50d000018a00808080f <<< 270),
  (0x238e8408b <<< 315),
  0xa00b40,
  unpack 0x6466187e49cc30a30e8089c62038a3400cb9a39f7e5812238,
  unpack 0xc703a10271310e1071c9110af0fa0e01c041f2001bc0,
  unpack 0x1d3042e1300e0425f898085717df3629a07500,
  unpack 0x19194a1f9272ac28ebf13b5fce902387003800,
  unpack 0x227187c0c31c28ebf130a0b01c000,
  (0x50280140001600023010b <<< 276),
  (0x81c61210f <<< 321)]

private def t1 : Array ℕ := #[
  unpack 0x1d18440f0a8c70828e010af0a917158b018b8007,
  unpack 0x3a30881e1518f6b22015ca962e36d8b04aa58,
  0,
  unpack 0x128609ec0438414764060bb90b8f4bb3600,
  unpack 0x1d99c817e260e61d518042bc2a41000,
  unpack 0xc8ca007f22c01e56260195e1d4000,
  unpack 0x7461103c2a31edba60000,
  (0x1a0418a07 <<< 327),
  unpack 0xeee3014000c26,
  unpack 0xeee30140073e8,
  unpack 0xd0e1183f90510e1061d89e1b84881b8c0,
  0,
  unpack 0xc9c4179260641e4d8042b8a8d9000,
  unpack 0x7661305c0a41e559390e0d8000,
  unpack 0x3b30982e0530e20c0000,
  (0x6818a19 <<< 333)]

private def t2 : Array ℕ := #[
  unpack 0xecf5df20631c2843930c33f6900a1a42,
  unpack 0xc8ca007f22a31d54044e3095c030ba8daa335889550,
  unpack 0x3438c00f0b9470838ece200480,
  unpack 0x322185f91018e1075f998065700c2e8408e2e1b7a00,
  unpack 0x1910c2e1328e1465f9984057734011f1000,
  (0x401821000009800115202200e501 <<< 249),
  (0x20087010810500009 <<< 294),
  (0x20719 <<< 339),
  unpack 0x191180e8409d0d81187627080888052,
  unpack 0x39c2fc890c70230ec4e10111001a070,
  unpack 0xe846179262c31c08e3b390c010d80,
  unpack 0x7678cf91310e0461d89c1b14088007c00,
  unpack 0x6301e50418ea8440bc276b000,
  0,
  (0x200e109080040203 <<< 298),
  (0x2018d <<< 341)]

private def t3 : Array ℕ := #[
  unpack 0xc764809870a28e140002fa,
  unpack 0x3a5305f89830870a30ec4f058062540070,
  unpack 0x6871801e1728e1071d9c4004c0380,
  unpack 0xecc830bc931620e62d8984c5715e801971009e8441c00,
  unpack 0x44840f922c31d5260dc2001ce000,
  unpack 0x89001f9440639a1107fe8000,
  0,
  (0x9 <<< 346),
  unpack 0xecca30bca2661c28a3800064,
  unpack 0x1d7490130f72d9c870a52d03060,
  unpack 0x88841f4204e2621c20e3922215e1f41c03803a80,
  unpack 0x1a1c030fc934360461d898a862e29801c00,
  unpack 0x3230941f281847436c4c4423c20780e000,
  (0xd03941020003080018004411b <<< 260),
  (0x800102019b <<< 305),
  0]

private def t4 : Array ℕ := #[
  unpack 0xd0e0183fa5838473133108f0a9582a0a4,
  unpack 0x7467287fa5811c7179998847840c21d8da5401a0e0,
  unpack 0x88841f4204e2621c20e3922215e1f41c0380036700,
  unpack 0x113080e4cc30818fc94057730421d51983f400,
  unpack 0x748303f22051c006bb20215cd000e000,
  (0x4000612002091c0504200017 <<< 265),
  (0x140050500001f <<< 310),
  (0x15 <<< 355),
  unpack 0x880a1f029c7b568362a000,
  unpack 0x6871801e1728e1071d9c5098000,
  unpack 0x3438c00f0b9470838ece200d40,
  unpack 0x7467005e4983147516c4edda137a0065c4027800,
  unpack 0x323305f90638eab144aa9b000,
  0,
  (0x1200306800022300435 <<< 287),
  (0x8040001 <<< 331)]

private def t5 : Array ℕ := #[
  unpack 0x3b328c2f2899870a28e0000eaed,
  unpack 0x7666281c2c51cd38b179986020c29d8,
  0,
  unpack 0x1d9dbb9408e3a9b2605bd0a3100,
  unpack 0x3438c00f9262c01e55b2ec0bfe74b25800,
  unpack 0x44e207c931438f26d8980c17817d2c000,
  unpack 0x7466207c91620eae20000,
  (0x1a03002041 <<< 323),
  unpack 0x1dd764809870a28e00002141f5,
  (0x803 <<< 348),
  unpack 0x850813cab0006a0,
  (0x20084021805 <<< 317),
  unpack 0x19184a0f940c83c9b270dc21d9800,
  unpack 0x1a1ce507ca0641e4d922015e144000,
  unpack 0xe8c6107aa1a9b0242e0000,
  (0x40210041 <<< 328)]

private def t6 : Array ℕ := #[
  (0x18001 <<< 343),
  unpack 0xc88e07e962261ed1b20000,
  0,
  unpack 0xc9c41f92788518762706c50e400,
  unpack 0x1919841f9444e3850c76262015e10a800,
  unpack 0x44e307f13a561071d0edf8c000,
  unpack 0x6761ca0a71c20e3ca0000,
  (0x14063 <<< 342),
  unpack 0x3a6281fa5e5300006a,
  (0x843420005 <<< 312),
  unpack 0xecdc4c001d180,
  unpack 0xc8ce703840c3cab260d8a08025c00,
  unpack 0xecc4607c931110e1431d916139000,
  unpack 0xe8ce1fe695ca48885f0000,
  (0xc010c00004113803 <<< 296),
  0]

private def t7 : Array ℕ := #[
  unpack 0x6465203d0813898470218e3d000756,
  unpack 0x6873901e8409c4463adc5e80148,
  unpack 0x6460207d8d9b6270c3ed2000,
  unpack 0x112942fc4c44e384187b270ee05f34b19400,
  unpack 0x191348e4ddb3140be800,
  (0x40c20c0810440020c0010045 <<< 262),
  0,
  (0x40620001 <<< 326),
  unpack 0x775d920261c28a3800025,
  unpack 0x3a30981e0429c1863840d724622b8befaa8f104a0,
  unpack 0xd0e3285d89ac4c0623c3fce9621e6c0,
  unpack 0x1d1801e8421c08a3cab2605bd0a0200,
  unpack 0xe8c450b810a70718eab36ee16a000,
  unpack 0x647b6c0853898c7358980c17817d4c000,
  unpack 0xc9420fe2708d5c760000,
  0]

private def t8 : Array ℕ := #[
  unpack 0x647a2f90628e8b13c870951800316,
  (0x140c709081044600049 <<< 286),
  unpack 0x323385c91120f26c2c22a0720,
  unpack 0x3032410a381197e2706c502a00,
  unpack 0x112941f24d0dda36262015ca8e800,
  unpack 0x3300f898a9470232fccc060bc32071c000,
  (0x5031c24204111800124003 <<< 272),
  (0xa061840409 <<< 319),
  0,
  (0x903143400006180230004401 <<< 264),
  unpack 0x1d99ca170b9470838ece200240,
  (0x1 <<< 334),
  unpack 0xd0e6007e498b98753649a16800,
  unpack 0x1a1c030fc930038f72c0215df0c000,
  unpack 0x7667285c2e71c2863aa0000,
  (0x1 <<< 358)]

private def t9 : Array ℕ := #[
  0,
  unpack 0x64210ba10271520e0451c0001d584d07,
  unpack 0x3105fa583907436010af0fb48b8ac58026007,
  unpack 0xecca60b80ce3840970805739580017d,
  unpack 0x6871841e4838c70a18e3d0001070e,
  unpack 0x46d00002e00e,
  unpack 0x7667085d08138b047023ae100ae72b0001fe6,
  unpack 0x226107e498a1c70830e3d00000d1c,
  unpack 0x1d994617e9790d458022bb94620ec6d1ada6e950c,
  unpack 0x6461083f89c326c9100af0802d083e4,
  0,
  unpack 0x112901f2881c7b46480700e4a100dc41f22e18,
  unpack 0x7466287f95461421d9010ae294d88481c6d303a8,
  unpack 0x1a2f89831c70a3ae484c573e980197c65c261529930,
  unpack 0xc8421792792c008053b0,
  unpack 0x88ce0f9553506e059510903996f69b10]

private def t10 : Array ℕ := #[
  unpack 0x6873003e8409f219ace432618b8dcb2441f2001ae0,
  unpack 0xecca70385ca3851976260311dfce618a6f332400aff20340e0,
  unpack 0xc603ca0641e4d85845407000e0,
  unpack 0x3390e14ac6d042c0,
  unpack 0x6465003f91600f72d899ed4b6368640,
  unpack 0x1a1ce507f4b0630e1471d898805711541b6c0,
  unpack 0x64a10bc93c960004180,
  unpack 0xcec3941823841472605c27a0a80,
  unpack 0xeee3009870818ec4f11eac2e980,
  unpack 0x3a31103fc4f218114761b87da87ee369e80,
  unpack 0xd0e7283fa5cc30228ec370fb50fdc6d32300,
  unpack 0x3a329c7fd2c54c3cab260d8a056900,
  unpack 0x3a3b768409c1843841470313d00,
  unpack 0x32310c1e8609e9423a9b65cdc3cd2c7a5a200,
  unpack 0x1a1c4407e4b1600e1035c1315e05a00c3801971009fcca00,
  unpack 0xc8c4313a10270610f6807200]

private def t11 : Array ℕ := #[
  unpack 0x6464205d0813838c7b468a08031c00,
  unpack 0x851f922641c28839306c508400,
  unpack 0x3230043f2809470830ec4c54315dac00,
  unpack 0x220287c0e51c006bac5b98600ea8cc9800,
  unpack 0x110103e4889079364880578552b0800,
  unpack 0x192902e481147936b45fe7b4da800,
  unpack 0x34390c1fe2794ed1b20215e109000,
  unpack 0x3a33143fcaa30a10ecc1b45545d000,
  0,
  unpack 0x3438881f0a0879561108e0a000,
  unpack 0x1d198a1fe55185087660da2ab2000,
  unpack 0x46c1922811c2823b131615a000,
  unpack 0x1918420f269b47c98c070112fc0c000,
  unpack 0xcc172410a385187244623c32009c000,
  (0x9 <<< 230),
  unpack 0x1982e4821470a30ec4c032bc3d6c000]

private def t12 : Array ℕ := #[
  unpack 0x3105e50228e1431d0ec818000,
  unpack 0x3a2281fa58a987b56c407838000,
  (0x4808218102019c001c000000c51 <<< 253),
  (0x6608001010a028c00010463 <<< 258),
  unpack 0x184072404c3dcb32b0000,
  (0x2406505081000a028e001007 <<< 266),
  (0xa0420680002a4000500481 <<< 271),
  unpack 0x888c1fe715dcbc360000,
  (0xd0088100041028081019 <<< 280),
  (0x4818a1a000001004197 <<< 285),
  (0x100e30808005020007 <<< 290),
  (0xf <<< 295),
  (0xc0184242041301 <<< 304),
  (0x300c0010010109 <<< 306),
  (0x3184840829 <<< 311),
  (0x240611d0003 <<< 318)]

private def t13 : Array ℕ := #[
  (0x9008804209 <<< 320),
  (0x10a0203 <<< 325),
  (0x24023003 <<< 330),
  (0x1205381 <<< 335),
  (0x9019f <<< 340),
  (0x201f <<< 345),
  0,
  (0x3 <<< 357),
  unpack 0x1918081f090c7b46c4c402b950001f4,
  unpack 0x29b000043b,
  unpack 0xecce40bf130730e86c0215e1522e2b1600,
  unpack 0x44e607c931138e1431d89e432aa8c001a,
  unpack 0x744503f4b1530f66d8b200010c0e,
  unpack 0x3b31842f24c50238518762708088805a,
  unpack 0x3438041f970dca36155505a0000fc,
  unpack 0x3a32083f24c4c638510700857261800eac]

private def t14 : Array ℕ := #[
  0,
  (0x2031028000221 <<< 307),
  unpack 0x32e260871c28239302de85000,
  (0xc021800204001 <<< 308),
  unpack 0xe8c400fca2441c08cbf22215d09951aa3000,
  unpack 0xa50b922a61c2063b22391e1d8000,
  unpack 0x1d98c2174204e2811c28c3b1384040210,
  unpack 0x7462087d0813aa0435f89c1b0114e0038ea8c2d350,
  unpack 0x191982e54686c9010ae4a000,
  unpack 0xe98a07e9792c2863f133160229d0841d51e22a420,
  unpack 0x190942fce2b0005a0,
  unpack 0x1d01c1f24c1ca3850c70805787d0700e00057defa0,
  unpack 0x1d9e5be41423850c708417879a452c5a9b00,
  unpack 0x1d18041f4204e2e21c20c3b13c370910369988,
  unpack 0x7478f2a9ac4c0623c3fce96205050,
  unpack 0x1d3001fc8a1c79564c200250]

private def t15 : Array ℕ := #[
  unpack 0x191948079260261c2863b13c860196f69bd0,
  unpack 0xe80c1fe444438418764420bb9986c45361a0,
  0,
  unpack 0xc8c661fc34801c03956500,
  unpack 0x190843e0638e68042bbd0a3900,
  0,
  (0xc039431 <<< 332),
  unpack 0xc8423f4304f6c51ed5b2e6dfccc7a5ea00,
  unpack 0xd0e2207e49899070a20e4c1b14088029c00,
  unpack 0x746438fe61d80870a22ec8cc573d5801971009fcec00,
  unpack 0x840ff131038e1461c9118ae2f350cc400,
  unpack 0x34390e170b0c7021ae110af0fb28a2800,
  unpack 0xc94a17e71580000,
  (0x2018602002099001 <<< 297),
  (0x80218042000028083 <<< 292),
  unpack 0x1d01c0e8409c5c438418762786e122000]

private def t16 : Array ℕ := #[
  unpack 0xd0e2207f91708ea8c9c870fb48050d0,
  (0x40e305001 <<< 322),
  unpack 0xc94817240c43dcb4201680,
  unpack 0xd0e7203d08138a147340215c986000,
  unpack 0x3a32083f24c54e38418727187da41500,
  unpack 0x3230841fc4e193616115000,
  unpack 0x1d98c00f9262c21d4db2ec0bfe74b10f40,
  unpack 0x1d18821fe404a3841c7670d8a3f9800,
  unpack 0x1938c2fd2c4463ca498b1154152c0,
  unpack 0x74a207f38aed39b726205e40,
  0,
  unpack 0x11b07c4c48c3d9b40b84542e580,
  unpack 0x1d984417e40463811472451530c0500,
  unpack 0x1a1ca20b81c83cab25d179311900,
  unpack 0x7185d0813881c7b46c8a00008,
  (0x8011 <<< 293)]

private def t17 : Array ℕ := #[
  unpack 0x7771f34ac08a3da0000,
  unpack 0x3362e5a96a6c9c8688000,
  unpack 0x1d19821f926a8c28c38422711c0eefb4b10280,
  unpack 0x3b3740641d16402000,
  unpack 0xeee3009870818ec4c402ba2436000,
  unpack 0x34388a1f241031ec9e438530cb400,
  unpack 0x34388a1f24184380157b26847efa000,
  unpack 0x44040f922241e4d9386e100028,
  (0x501081401 <<< 324),
  unpack 0x1d0982f2828c7322311c500168,
  unpack 0x1860708907936010ae2a35460010,
  unpack 0x7664381d0843cc30a3ae8089c4623c3ec204761b6200,
  unpack 0x3a6003f91438f2ac984040290,
  unpack 0x1d98c21f4204f09a4e229b5461880,
  unpack 0x3983fd2c4423aa32446238a840220,
  unpack 0x1d1101e8831070832fc4ed0000]

private def t18 : Array ℕ := #[
  unpack 0x113980fc8282ba0227c3708000,
  (0x120110084080c20105 <<< 291),
  unpack 0x88ce0fe96a6c20c3800039,
  0,
  unpack 0xc8cc60bcb0acd62c8000,
  (0x5029 <<< 344),
  unpack 0x321205c90130e1031d898885784882d024,
  unpack 0x6461083c953668042b930c0074,
  unpack 0xa1fe615810576750000,
  (0x398340041 <<< 316),
  unpack 0x64c303f131320f2800021,
  unpack 0x68700c3f24d10f4000,
  unpack 0x192041fca9b4589e4384a8c0002,
  unpack 0x1d3040e48b987b49c870a900a1a3a,
  unpack 0x1a1c060f922431c08c3b1384044400,
  unpack 0xe8c01f9262a31ecd8c58a82d014]

private def t19 : Array ℕ := #[
  unpack 0xc9c617945043841c7008577b30c0044,
  (0x2800a1800201980401 <<< 289),
  0,
  unpack 0x3439c20f255000005,
  unpack 0x3438c80f9262c41c28aba02271102f09518001f442abe93,
  unpack 0x1d19041f9262621c28a3850001d5e9b,
  unpack 0x7461103f91608e1435f98362a300062d1,
  unpack 0x1a1c2707c9394d6270c20700e2e20837be812138,
  0,
  unpack 0x3a1185d0813888c795898085787d945c6d02488,
  unpack 0x74230ba10271118e0451c9100aef42e2022a8,
  unpack 0x227187d50c206b923101cf400cbe2094c8,
  unpack 0x14817028c7436c4f21bd9862e800758b106440,
  unpack 0xecce10bc931510e0461d89808578548b8ac5b9540,
  0,
  unpack 0x110043e8409e9b964e4387da40740]

private def t20 : Array ℕ := #[
  unpack 0x113881fc8a1870228ec4f2187f30840,
  unpack 0x7467207c2641c082bb130980f02de8c00cb8804f3200,
  unpack 0xd0e4381e51320e1475c9188ae79b0032e2013e59ba00,
  unpack 0xe8c600b890270520e0475c9b770a00c3801971009fcc200,
  0,
  unpack 0x192003f24f21840d72462039e801971009fcd200,
  unpack 0x74230ba10271118f28d8988657766a61000,
  unpack 0x644603c930438e0071d908c0ee2f9d65000,
  unpack 0x1d1140fd2c54c38418764430380e0729000,
  unpack 0x1c765d9c3b2d000,
  0,
  unpack 0x6465003c2261ed1920303f698000,
  unpack 0x64210bc93c9636d8000,
  (0x901801400415380228004411881 <<< 252),
  0,
  (0x40e205000050c008a00110422d <<< 254)]

private def t21 : Array ℕ := #[
  (0xc029c2400412011 <<< 300),
  unpack 0xc8cc170104fd40000,
  (0x200220808001881 <<< 302),
  unpack 0x64c203a1f40000,
  0,
  (0x341 <<< 350),
  (0x21 <<< 351),
  (0xd1 <<< 352),
  (0x1 <<< 353),
  (0x5 <<< 354),
  unpack 0x321205f89831470238e48845787f9a110763694db69ba0,
  unpack 0x64a40bf130038e1415c91108f0a9582a094,
  0,
  unpack 0x8503f4b1238e1415c91108f0a9582a0b4,
  unpack 0x1911c2f24f11841976266211e1f69582a0c4,
  unpack 0x720a51c088bb1322e46a8c1b4c0]

private def t22 : Array ℕ := #[
  unpack 0x3b0efa59a0075f9c1682c688481c00,
  unpack 0x74c503f4b1138e8b22215d12a354601c8,
  unpack 0x1d984617e962811d05f1331708c5460390,
  0,
  unpack 0x646703844e38518764422b8bccc3620015f00,
  unpack 0x3439060f2551da30844787f9d2c4537c80,
  unpack 0x1d0982fc4e8d851c7430a56368120,
  unpack 0x1d0982fc4e8d851c76710000,
  unpack 0xc8cc60ff4b1530f2ac983628000,
  unpack 0x325087f9041c7670d8a12da00,
  unpack 0x44470f928a9b088178161ca100,
  (0x300611 <<< 338),
  0,
  unpack 0x1918c60792794c03956d00,
  (0x201cc1 <<< 337),
  (0x1 <<< 349)]

private def t23 : Array ℕ := #[
  0,
  unpack 0x325085e49e4b000062,
  (0x5038c1 <<< 336),
  unpack 0x3a0283e595686d89e200e80,
  unpack 0x1a1c6503ca2a11ed5920000,
  unpack 0x1d19041f4204e2241d16262205e13d000,
  unpack 0x112103fc4c4cc3dcb4200c80,
  (0x1 <<< 359),
  (0xe309081040a02880010046000003 <<< 238),
  unpack 0x338ec0471d4d930bf9d22e329200,
  unpack 0xc9421792792d4d818800,
  0,
  unpack 0x191180e8409e15ca4e3b0000,
  (0x1 <<< 356),
  unpack 0x34398217245ce384197e4d15e6c6800,
  unpack 0xe8c030ff4ba5524d0000]

private def t24 : Array ℕ := #[
  unpack 0x3a300c3fd2e934934310110,
  0,
  unpack 0x1d990607e262221c28eb8440bc2af2000,
  (0xa01 <<< 347),
  unpack 0x3b33141f24e61c9b2154000,
  unpack 0xd0e7001c050000,
  0,
  (0x8140001 <<< 329),
  (0x200421010209 <<< 313),
  (0x120110084080c201 <<< 299),
  0,
  (0x140630008105 <<< 314)]

private def tables := #[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24]
private def multiplier (j : ℕ) := ((tables[j/16]?.getD #[])[j%16]?).getD 0

private def checkAt (i : ℕ) : Bool :=
  let p := (rowOrder 8 9 5).symm (Fin.ofNat 360 i)
  fit (rowProduct 8 9 5 18 factors multiplier p.1.val p.2.1.val p.2.2.val) i

private def w8 : RowWindow checkAt 8 := nextWindow (start checkAt) 8 (by decide +kernel)
private def w16 : RowWindow checkAt 16 := nextWindow w8 8 (by decide +kernel)
private def w24 : RowWindow checkAt 24 := nextWindow w16 8 (by decide +kernel)
private def w32 : RowWindow checkAt 32 := nextWindow w24 8 (by decide +kernel)
private def w40 : RowWindow checkAt 40 := nextWindow w32 8 (by decide +kernel)
private def w48 : RowWindow checkAt 48 := nextWindow w40 8 (by decide +kernel)
private def w56 : RowWindow checkAt 56 := nextWindow w48 8 (by decide +kernel)
private def w64 : RowWindow checkAt 64 := nextWindow w56 8 (by decide +kernel)
private def w72 : RowWindow checkAt 72 := nextWindow w64 8 (by decide +kernel)
private def w80 : RowWindow checkAt 80 := nextWindow w72 8 (by decide +kernel)
private def w88 : RowWindow checkAt 88 := nextWindow w80 8 (by decide +kernel)
private def w96 : RowWindow checkAt 96 := nextWindow w88 8 (by decide +kernel)
private def w104 : RowWindow checkAt 104 := nextWindow w96 8 (by decide +kernel)
private def w112 : RowWindow checkAt 112 := nextWindow w104 8 (by decide +kernel)
private def w120 : RowWindow checkAt 120 := nextWindow w112 8 (by decide +kernel)
private def w128 : RowWindow checkAt 128 := nextWindow w120 8 (by decide +kernel)
private def w136 : RowWindow checkAt 136 := nextWindow w128 8 (by decide +kernel)
private def w144 : RowWindow checkAt 144 := nextWindow w136 8 (by decide +kernel)
private def w152 : RowWindow checkAt 152 := nextWindow w144 8 (by decide +kernel)
private def w160 : RowWindow checkAt 160 := nextWindow w152 8 (by decide +kernel)
private def w168 : RowWindow checkAt 168 := nextWindow w160 8 (by decide +kernel)
private def w176 : RowWindow checkAt 176 := nextWindow w168 8 (by decide +kernel)
private def w184 : RowWindow checkAt 184 := nextWindow w176 8 (by decide +kernel)
private def w192 : RowWindow checkAt 192 := nextWindow w184 8 (by decide +kernel)
private def w200 : RowWindow checkAt 200 := nextWindow w192 8 (by decide +kernel)
private def w208 : RowWindow checkAt 208 := nextWindow w200 8 (by decide +kernel)
private def w216 : RowWindow checkAt 216 := nextWindow w208 8 (by decide +kernel)
private def w224 : RowWindow checkAt 224 := nextWindow w216 8 (by decide +kernel)
private def w232 : RowWindow checkAt 232 := nextWindow w224 8 (by decide +kernel)
private def w240 : RowWindow checkAt 240 := nextWindow w232 8 (by decide +kernel)
private def w248 : RowWindow checkAt 248 := nextWindow w240 8 (by decide +kernel)
private def w256 : RowWindow checkAt 256 := nextWindow w248 8 (by decide +kernel)
private def w264 : RowWindow checkAt 264 := nextWindow w256 8 (by decide +kernel)
private def w272 : RowWindow checkAt 272 := nextWindow w264 8 (by decide +kernel)
private def w280 : RowWindow checkAt 280 := nextWindow w272 8 (by decide +kernel)
private def w288 : RowWindow checkAt 288 := nextWindow w280 8 (by decide +kernel)
private def w296 : RowWindow checkAt 296 := nextWindow w288 8 (by decide +kernel)
private def w304 : RowWindow checkAt 304 := nextWindow w296 8 (by decide +kernel)
private def w312 : RowWindow checkAt 312 := nextWindow w304 8 (by decide +kernel)
private def w320 : RowWindow checkAt 320 := nextWindow w312 8 (by decide +kernel)
private def w328 : RowWindow checkAt 328 := nextWindow w320 8 (by decide +kernel)
private def w336 : RowWindow checkAt 336 := nextWindow w328 8 (by decide +kernel)
private def w344 : RowWindow checkAt 344 := nextWindow w336 8 (by decide +kernel)
private def w352 : RowWindow checkAt 352 := nextWindow w344 8 (by decide +kernel)
private def w360 : RowWindow checkAt 360 := nextWindow w352 8 (by decide +kernel)

theorem spans : CriticalTensor.Spans 5 8 9 18 := by
  apply checked factors multiplier
  intro i
  have h := w360.verified i.val i.isLt
  have he : Fin.ofNat 360 i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simpa only [checkAt,he] using h

end CriticalTensor.RectFiveBase.Eight

namespace CriticalTensor.RectFiveBase

theorem base_eight : CriticalTensor.Spans 5 8 9 18 := Eight.spans

end CriticalTensor.RectFiveBase



namespace CriticalTensor.ConsecutiveBorder

abbrev Side (d : ℕ) := Fin 2 ⊕ Fin d
abbrev Rows (a d e : ℕ) := (Fin 2 × Side e × Fin a) ⊕ (Fin d × Fin 2 × Fin a)
abbrev Cols (a d e r : ℕ) := (Fin a × (Side d ⊕ (Side e ⊕ Fin a))) ⊕ (Fin r × (Fin 2 ⊕ Fin 2))

def coords {a d e : ℕ} : Rows a d e → Side d × Side e × Fin a
  | .inl (j,k,i) => (.inl j,k,i)
  | .inr (j,k,i) => (.inr j,.inl k,i)

def matrix {a d e r : ℕ} {K : Type} [CommSemiring K]
    (X : Fin a → Fin a → K) (Y : Fin a → Side d → K) (Z : Fin a → Side e → K)
    (x : Fin r → Fin a → K) (y : Fin r → Fin d → K) (z : Fin r → Fin e → K) :
    Matrix (Rows a d e) (Cols a d e r) K := fun row col =>
  let (j,k,i) := coords row
  match col with
  | .inl (t,.inl h) => if h=j then X t i * Z t k else 0
  | .inl (t,.inr (.inl h)) => if h=k then X t i * Y t j else 0
  | .inl (t,.inr (.inr h)) => if h=i then Y t j * Z t k else 0
  | .inr (t,.inl h) => if Sum.inl h=j then x t i * k.elim (fun _ => 0) (z t) else 0
  | .inr (t,.inr h) => if Sum.inl h=k then x t i * j.elim (fun _ => 0) (y t) else 0

lemma cast_matrix {a d e r : ℕ} (X : Fin a → Fin a → ℤ) (Y : Fin a → Side d → ℤ)
    (Z : Fin a → Side e → ℤ) (x : Fin r → Fin a → ℤ) (y : Fin r → Fin d → ℤ) (z : Fin r → Fin e → ℤ) :
    (matrix X Y Z x y z).map (Int.castRingHom ℂ) = matrix (fun t i => (X t i : ℂ)) (fun t j => (Y t j : ℂ))
      (fun t k => (Z t k : ℂ)) (fun t i => (x t i : ℂ)) (fun t j => (y t j : ℂ)) (fun t k => (z t k : ℂ)) := by
  have ec (P : Prop) [Decidable P] (v : ℤ) (w : ℂ) (hv : (v : ℂ)=w) :
      ((if P then v else 0 : ℤ) : ℂ) = (if P then w else 0) := by by_cases hp : P <;> simp [hp,hv]
  ext row col
  change ((matrix X Y Z x y z row col : ℤ) : ℂ) = _
  rcases row with ⟨j,k|k,i⟩|⟨j,k,i⟩ <;> rcases col with ⟨t,v|v|v⟩|⟨t,v|v⟩ <;>
    simp only [matrix,coords,Sum.elim_inl,Sum.elim_inr]
  all_goals apply ec
  all_goals simp

lemma from_rank {a d e r : ℕ} (X : Fin a → Fin a → ℤ) (Y : Fin a → Side d → ℤ)
    (Z : Fin a → Side e → ℤ) (x : Fin r → Fin a → ℤ) (y : Fin r → Fin d → ℤ) (z : Fin r → Fin e → ℤ)
    (hs : Function.Surjective ((matrix X Y Z x y z).map (Int.castRingHom ℂ)).mulVec) : RectBorder a d e 2 r a := by
  classical
  rw [cast_matrix] at hs
  refine ⟨fun t i => X t i,fun t j => Y t j,fun t k => Z t k,fun t i => x t i,fun t j => y t j,fun t k => z t k,?_⟩
  intro T
  obtain ⟨v,hv⟩ := hs fun row => T (coords row).2.2 (coords row).1 (coords row).2.1
  refine ⟨fun t i => v (.inl (t,.inr (.inr i))),fun t j => v (.inl (t,.inl j)),
    fun t k => v (.inl (t,.inr (.inl k))),fun t h => v (.inr (t,.inl h)),fun t h => v (.inr (t,.inr h)),?_⟩
  intro i j k hij
  obtain ⟨u,hu⟩ : ∃ u : Rows a d e,coords u=(j,k,i) := by
    rcases j with j|j
    · exact ⟨.inl (j,k,i),rfl⟩
    · rcases k with k|k
      · exact ⟨.inr (j,k,i),rfl⟩
      · simp at hij
  have hh := (congrFun hv u).symm
  simp only [hu] at hh
  rw [hh]
  change (∑ q : Cols a d e r, matrix (fun t i => (X t i : ℂ)) (fun t j => (Y t j : ℂ))
    (fun t k => (Z t k : ℂ)) (fun t i => (x t i : ℂ)) (fun t j => (y t j : ℂ)) (fun t k => (z t k : ℂ))
    u q*v q) = _
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_prod_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    rcases j with j|j <;> rcases k with k|k <;>
      simp [matrix,hu,ite_mul,Fintype.sum_sum_type,Finset.sum_ite_eq'] <;> ring
  · apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type]
    rcases j with j|j <;> rcases k with k|k <;> simp [matrix,hu,ite_mul,Finset.sum_ite_eq'] <;> ring

def prodFin {I J : Type} {n k : ℕ} (ei : I ≃ Fin n) (ej : J ≃ Fin k) : I × J ≃ Fin (n*k) :=
  (ei.prodCongr ej).trans finProdFinEquiv

def sumFin {I J : Type} {n k : ℕ} (ei : I ≃ Fin n) (ej : J ≃ Fin k) : I ⊕ J ≃ Fin (n+k) :=
  (Equiv.sumCongr ei ej).trans finSumFinEquiv

def rows (a d e : ℕ) : Rows a d e ≃ Fin (2*((2+e)*a)+d*(2*a)) :=
  sumFin (prodFin (Equiv.refl _) (prodFin finSumFinEquiv (Equiv.refl _))) (prodFin (Equiv.refl _) finProdFinEquiv)

def cols (a d e r : ℕ) : Cols a d e r ≃ Fin (a*((2+d)+((2+e)+a))+r*(2+2)) :=
  sumFin (prodFin (Equiv.refl _) (sumFin finSumFinEquiv (sumFin finSumFinEquiv (Equiv.refl _))))
    (prodFin (Equiv.refl _) finSumFinEquiv)

def flags {n m : ℕ} (a : Array ℕ) (t : Fin n) (u : Fin m) : ℤ := Binary.intBit ((a[t.val]?.getD 0).testBit u.val)

end CriticalTensor.ConsecutiveBorder

namespace CriticalTensor.ConsecutiveBorder

open Binary

lemma rank_of_binary {I J : Type} [Fintype J] [DecidableEq J] {n k : ℕ} (M : Matrix I J ℤ)
    (er : I ≃ Fin n) (ec : J ≃ Fin k) (cols masks : ℕ → ℕ)
    (he : ∀ (i : Fin n) (j : Fin k), M (er.symm i) (ec.symm j) = intBit ((cols j.val).testBit i.val))
    (hc : ∀ i : Fin n, xorColumns cols (masks i.val) k=2^i.val) :
    Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  let N := M.submatrix er.symm ec.symm
  have hs := surjective_of_certificate N cols masks he hc
  have hm : M.map (Int.castRingHom ℂ) = (N.map (Int.castRingHom ℂ)).submatrix er ec := by
    ext i j
    simp [N,Matrix.submatrix,Matrix.map_apply]
  rw [hm]
  intro T
  obtain ⟨v,hv⟩ := hs (T ∘ er.symm)
  refine ⟨v ∘ ec,?_⟩
  rw [Matrix.submatrix_mulVec_equiv]
  have hec : (v ∘ ec) ∘ ec.symm=v := by ext; simp
  rw [hec,hv]
  ext
  simp

def window (f : ℕ → Bool) (start : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => window f start n && f (start+n)

def Before (f : ℕ → Bool) (b : ℕ) := ∀ i < b, f i = true

lemma before_zero (f : ℕ → Bool) : Before f 0 := fun _ h => by omega

lemma extend {f : ℕ → Bool} {b n : ℕ} (earlier : Before f b) (h : window f b n = true) :
    Before f (b+n) := by
  induction n with
  | zero => simpa using earlier
  | succ n ih =>
    obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp h
    intro i hi
    by_cases h' : i < b+n
    · exact ih h₁ i h'
    · have he : i=b+n := by omega
      exact he ▸ h₂

structure RowWindow (f : ℕ → Bool) (n : ℕ) : Type where
  verified : Before f n

def start (f : ℕ → Bool) : RowWindow f 0 := ⟨before_zero f⟩

def nextWindow {f : ℕ → Bool} {b : ℕ} (prev : RowWindow f b) (n : ℕ)
    (h : window f b n = true) : RowWindow f (b+n) := ⟨extend prev.verified h⟩

def directCheck {I J : Type} {n k : ℕ} [NeZero n] (M : Matrix I J ℤ) (er : I ≃ Fin n)
    (ec : J ≃ Fin k) (a b : ℕ → ℕ) (i : ℕ) : Bool :=
  (List.finRange k).all (fun j => M (er.symm (Fin.ofNat n i)) (ec.symm j) == intBit ((a j.val).testBit i)) &&
    (xorColumns a (b i) k == 2^i)

lemma checked {I J : Type} [Fintype J] [DecidableEq J] {n k : ℕ} [NeZero n]
    (M : Matrix I J ℤ) (er : I ≃ Fin n) (ec : J ≃ Fin k) (a b : ℕ → ℕ)
    (h : Before (directCheck M er ec a b) n) : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  apply rank_of_binary M er ec a b
  · intro i j
    have hv := (Bool.and_eq_true_iff.mp (h i.val i.isLt)).1
    have hj := List.all_eq_true.mp hv j (List.mem_finRange _)
    have he : Fin.ofNat n i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    simpa only [beq_iff_eq,he] using hj
  · intro i
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp (h i.val i.isLt)).2

end CriticalTensor.ConsecutiveBorder


namespace CriticalTensor.ConsecutiveBorder

/-- Each stored word contains eight fixed-width natural numbers. -/
def packedEntry (t : Array ℕ) (width i : ℕ) : ℕ := (t[i/8]?.getD 0 >>> (width*(i%8))) % 2^width

end CriticalTensor.ConsecutiveBorder

namespace CriticalTensor.ConsecutiveBorder
namespace Five

open Binary

def X (t : Fin 5) (i : Fin 5) : ℤ := flags #[
  0x1,0x2,0x4,0x8,0x10] t i
def Y (t : Fin 5) (i : Side 5) : ℤ := flags #[
  0x51,0x63,0x47,0x71,0x16] t (finSumFinEquiv i)
def Z (t : Fin 5) (i : Side 6) : ℤ := flags #[
  0x67,0x79,0x17,0x2e,0x21] t (finSumFinEquiv i)
def x (t : Fin 11) (i : Fin 5) : ℤ := flags #[
  0x7,0x18,0x19,0x1d,0x2,0x14,0x17,0x11,0x4,0x1b,0x1e] t i
def y (t : Fin 11) (i : Fin 5) : ℤ := flags #[
  0x15,0x19,0x1d,0xe,0x2,0xf,0x18,0xa,0xa,0x18,0xc] t i
def z (t : Fin 11) (i : Fin 6) : ℤ := flags #[
  0x2b,0x17,0x12,0x1d,0x23,0x3,0x3a,0x24,0x37,0x6,0x34] t i

def M := matrix X Y Z x y z

private def a0 : Array ℕ := #[0x42000421, 0x420004210000000000, 0x2100000000000000000000, 0x840000000000000000000000, 0x210000000000000000000000000, 0x84000000000000000000000000000, 0x21000000000000000000000000000000, 0x1000010000000000000000000000001]
private def a1 : Array ℕ := #[0x20000200000000000000000000000020, 0x400, 0x8000, 0x100000, 0x2000000, 0x40000000, 0x800000000, 0x21000210000000000000000042000421]
private def a2 : Array ℕ := #[0x42000420000000000000000084000842, 0x84000840000000000000000108001084, 0x108001080000000000000000210002108, 0x210002100000000000000000420004210, 0x84210002, 0x842100020000000000, 0x200000000000000000000, 0x80000000000000000000000]
private def a3 : Array ℕ := #[0x20000000000000000000000000, 0x8000000000000000000000000000, 0x2000000000000000000000000000000, 0x2008000000000000000020000000002, 0x40100000000000000000400000000040, 0x8000000000800, 0x100000000010000, 0x2000000000200000]
private def a4 : Array ℕ := #[0x40000000004000000, 0x800000000080000000, 0x10000000001000000000, 0x1004000000000421080010042108001, 0x2008000000000842100020084210002, 0x4010000000001084200040108420004, 0x8020000000002108400080210840008, 0x10040000000004210800100421080010]
private def a5 : Array ℕ := #[0x401084, 0x4010840000000000, 0x8400000000000000000000, 0x2100000000000000000000000, 0x840000000000000000000000000, 0x210000000000000000000000000000, 0x84000000000000000000000000000000, 0x4000000000400000000040000000004]
private def a6 : Array ℕ := #[0x80000000008000000000800000000080, 0x10000000001000, 0x200000000020000, 0x4000000000400000, 0x80000000008000000, 0x1000000000100000000, 0x20000000002000000000, 0x21000000002100001004210000100421]
private def a7 : Array ℕ := #[0x42000000004200002008420000200842, 0x84000000008400004010840000401084, 0x108000000010800008021080000802108, 0x210000000021000010042100001004210, 0x10042100, 0x100421000000000000, 0x10000000000000000000000, 0x4000000000000000000000000]
private def a8 : Array ℕ := #[0x1000000000000000000000000000, 0x400000000000000000000000000000, 0x100000000000000000000000000000000, 0x8020080000000000000000000000008, 0x100401000000000000000000000000100, 0x2000, 0x40000, 0x800000]
private def a9 : Array ℕ := #[0x10000000, 0x200000000, 0x4000000000, 0x20080200000000000000000002008420, 0x40100400000000000000000004010840, 0x80200800000000000000000008021080, 0x100401000000000000000000010042100, 0x200802000000000000000000020084200]
private def a10 : Array ℕ := #[0x20000010, 0x200000100000000000, 0x1000000000000000000000, 0x400000000000000000000000, 0x100000000000000000000000000, 0x40000000000000000000000000000, 0x10000000000000000000000000000000, 0x100001000000000100000000000]
private def a11 : Array ℕ := #[0x2000020000000002000000000000, 0x40000000000000, 0x800000000000000, 0x10000000000000000, 0x200000000000000000, 0x4000000000000000000, 0x80000000000000000000, 0x10000100020000010000000000]
private def a12 : Array ℕ := #[0x20000200040000020000000000, 0x40000400080000040000000000, 0x80000800100000080000000000, 0x100001000200000100000000000, 0x380e039c00, 0x380e039c000000000000, 0x7000070000700000000000000000000, 0xe0000e0000e000000000000000000000]
private def a13 : Array ℕ := #[0x6018c6000, 0x6018c60000000000000, 0x18060000001800000000000000000000, 0x300c00000030000000000000000000000, 0x6400c8000, 0x6400c80000000000000, 0x19064190001900000000000000000000, 0x320c83200032000000000000000000000]
private def a14 : Array ℕ := #[0x77bd07400, 0x77bd074000000000000, 0x741d0740000000000000000000000, 0xe83a0e800000000000000000000000, 0x1000010800, 0x10000108000000000000, 0x80000000000000000000000, 0x1000000000000000000000000]
private def a15 : Array ℕ := #[0xa5000, 0xa50000000000000, 0x50140501400000000000000000000, 0xa0280a028000000000000000000000, 0xbdee0b8000, 0xbdee0b80000000000000, 0x1705c000000000000000000000000000, 0x2e0b80000000000000000000000000000]
private def a16 : Array ℕ := #[0x8801100000, 0x88011000000000000000, 0x44000440000000000000000000000, 0x880008800000000000000000000000, 0x2100421000, 0x21004210000000000000, 0x10000100000000000000000000000, 0x200002000000000000000000000000]
private def a17 : Array ℕ := #[0x1bd8000, 0x1bd80000000000000, 0x1b06c000000000000000000000000000, 0x360d80000000000000000000000000000, 0xf781e00000, 0xf781e000000000000000, 0x781e0000000000000000000000000, 0xf03c00000000000000000000000000]
private def aBlocks : Array (Array ℕ) := #[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17]
private def a (i : ℕ) := ((aBlocks[i/8]?.getD #[])[i%8]?.getD 0)
private def b0 : Array ℕ := #[0x48400888400060000280377f20034000e4, 0x100010001100000000000051010f425600, 0x5150171045500d9c2eed18062000064e0af1, 0x4c40c4000000000c02431037272003040000, 0x30001000d8102e00806000000080000, 0x48400888400060000280377f2003400134, 0x915dc910190127fa86e548372ba10c415399, 0x1950951001120bbc04a60827f720000a1dd1]
private def b1 : Array ℕ := #[0x170000000000000000, 0xc0c0009000b9482e648003c0000080028, 0x200, 0x1011011011012c630620000000810f505fd1, 0x1010027e3003718005180000a09d1, 0x200000000000000000, 0x1002c6302e00000008000000000, 0x400]
private def b2 : Array ℕ := #[0x815cc81008d00b9990c549372e20bc135a1c, 0x201010021e3003718065180000a09d1, 0x400000000000000000, 0x30001002a6302e00006008000000000, 0x800, 0x805ccb1019d00d9990a549312e20bc1341cd, 0x48008201454221c32a7c082187a0064e1ef1, 0x800000000000000000]
private def b3 : Array ℕ := #[0x10002c63024000000080000017d1, 0x1000, 0x1000100010000000000000510000025600, 0x5910931045520da02eeb18218720064e0af1, 0x771000000000000000, 0x30001000d8002e00806000000080000, 0x13d1, 0x1000300110106000060000600010f501bd1]
private def b4 : Array ℕ := #[0x1110111100102c6304971000518000021400, 0x2000000000000000000, 0x30011002a6300a000060080000017d1, 0x4000, 0x914dc91019d127fa96e549372ea1b34305cd, 0x5900911045520ba02eeb1827d620064c0af1, 0x4000000000000000000, 0x1000010002c6302400000008000005fd1]
private def b5 : Array ℕ := #[0x84bb30889400d7502e488451fac8b7800e4, 0x1000100011000000000000510101425600, 0x5950971045500d9c2eeb18318720064e0af1, 0x4042040323344f7902336c5080e563085fd1, 0x9400000000000000000000, 0x4841f7004530c50900ab181327a1eb3c59d3, 0xd1110110dd01279284af18003081194553a5, 0x1150151001120bbc04a008119400000a1dd1]
private def b6 : Array ℕ := #[0x4f09b40bd970c21800b7c4939f492e704f72, 0xc0c0000000114000000003c0000000028, 0x43097408dc74cf090239ec2238892e784d35, 0x1011011011012c630620000000812f505fd1, 0x1010027e3003718025180000a09d1, 0xc00c00006042e6402b91000604000000000, 0x20000000000000000000000, 0x3330001000d7502e008f200848e380447]
private def b7 : Array ℕ := #[0x815cc81008d00b9990c549372e20fc135a1c, 0x201010021e3003718025180000a09d1, 0x4f0bb408f844a36d027688f458cc4e7c10a3, 0x40000000000000000000000, 0x30330001004077500767cf400844e3c1f96, 0x805ccb1019d00d9990a549312e203c1341cd, 0x48008201454221c32a7c082240a0064e1ef1, 0x4f0bb408f840a36d0080fcf458cc4e7810a3]
private def b8 : Array ℕ := #[0x80000000000000000000000, 0x400b7708cd408d0900af9872388c8e7c00e4, 0x1000100010000000000000510100025600, 0x5910931045520da02eeb18318720064e0af1, 0xc02c00327304f1100787c67a7c5600c5fd1, 0x9600000000000000000000, 0x43084708dd448a7c00d9e4063808c04014e4, 0x100030011010600006000060000c1601bd1]
private def b9 : Array ℕ := #[0x1110111100102c6304971020518000021400, 0xc00c00004000064004f6400604000040000, 0x200000000000000000000000, 0x301300010044f7500767cf400844e3c1f96, 0x914dc91019d127fa96e549372ea5b34305cd, 0x5900911045520ba02eeb1867d620064c0af1, 0x730a7708ed40e16a06ef9891ff09004c4f72, 0x400000000000000000000000]
private def b10 : Array ℕ := #[0x40084408cc40007c0a4f9000380000441744, 0x400000, 0x48008000444000200a4b1000600006441720, 0xc00c0000400006400060000600000000000, 0x400000000000000000000, 0x40084408cc40007c0a4f9000380000441740, 0x804ccb0019c00d9980a548317f20034017cd, 0x48008000444000200a4b1000640006441720]
private def b11 : Array ℕ := #[0x4000000000000000, 0x404c0800cc000008024c10377b200304005c, 0x400000000002808000000000000001720, 0x800000, 0x48408000444000200a4b1037272006441720, 0xc000ccc000000024f9000380000040064, 0x800000000000000000000, 0x400000000002808000000000000001728]
private def b12 : Array ℕ := #[0x800000000000000000000000000000, 0x48408000444000200a4b10372f2006441720, 0x8000000000000000, 0xc030011000df980a008060000000017f9, 0x848800888400000080480371f2005401744, 0x1000000, 0x484084004440001c0a4b1000600006441720, 0x404004000000000c024d1037472003040000]
private def b13 : Array ℕ := #[0x1000000000000000000000, 0x848800888400000080480371f2005401754, 0x404cc800c4c00068024a51374f20ba040068, 0x484084004440001c0a4b1000700006441720, 0x10000000000000000, 0x40400400cc00001c024c1037472003040074, 0x8000000000000001720, 0x2000000]
private def b14 : Array ℕ := #[0x48008000444000200a4b1037272006441720, 0x24d1000000000040000, 0x2000000000000000000000, 0x8000000000000001700, 0x804ccb0019c00d9980a549317f20b90017cd, 0x48008000444000200a4b1037072006441720, 0x20000000000000000, 0x30011000dd180a008060000000017d1]
private def b15 : Array ℕ := #[0x800c0000000006008060000600006001720, 0x4000000, 0x40000000444000200a4d1037472006441720, 0xc00c00000000000024b1000600000040000, 0x4000000000000000000000, 0x800c0000000006008060000600006001760, 0xc0000300ddc00df182ef19066400bc0417f1, 0x40000000444000200a4d1037072006441720]
private def b16 : Array ℕ := #[0x40000000000000000, 0x404c0b00d5000dd982ea58317b200304178d]
private def bBlocks : Array (Array ℕ) := #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16]
private def b (i : ℕ) := ((bBlocks[i/8]?.getD #[])[i%8]?.getD 0)
private def test := directCheck M (rows 5 5 6) (cols 5 5 6 11) a b
private def w3 : RowWindow test 3 := nextWindow (start test) 3 (by decide +kernel)
private def w6 : RowWindow test 6 := nextWindow w3 3 (by decide +kernel)
private def w9 : RowWindow test 9 := nextWindow w6 3 (by decide +kernel)
private def w12 : RowWindow test 12 := nextWindow w9 3 (by decide +kernel)
private def w15 : RowWindow test 15 := nextWindow w12 3 (by decide +kernel)
private def w18 : RowWindow test 18 := nextWindow w15 3 (by decide +kernel)
private def w21 : RowWindow test 21 := nextWindow w18 3 (by decide +kernel)
private def w24 : RowWindow test 24 := nextWindow w21 3 (by decide +kernel)
private def w27 : RowWindow test 27 := nextWindow w24 3 (by decide +kernel)
private def w30 : RowWindow test 30 := nextWindow w27 3 (by decide +kernel)
private def w33 : RowWindow test 33 := nextWindow w30 3 (by decide +kernel)
private def w36 : RowWindow test 36 := nextWindow w33 3 (by decide +kernel)
private def w39 : RowWindow test 39 := nextWindow w36 3 (by decide +kernel)
private def w42 : RowWindow test 42 := nextWindow w39 3 (by decide +kernel)
private def w45 : RowWindow test 45 := nextWindow w42 3 (by decide +kernel)
private def w48 : RowWindow test 48 := nextWindow w45 3 (by decide +kernel)
private def w51 : RowWindow test 51 := nextWindow w48 3 (by decide +kernel)
private def w54 : RowWindow test 54 := nextWindow w51 3 (by decide +kernel)
private def w57 : RowWindow test 57 := nextWindow w54 3 (by decide +kernel)
private def w60 : RowWindow test 60 := nextWindow w57 3 (by decide +kernel)
private def w63 : RowWindow test 63 := nextWindow w60 3 (by decide +kernel)
private def w66 : RowWindow test 66 := nextWindow w63 3 (by decide +kernel)
private def w69 : RowWindow test 69 := nextWindow w66 3 (by decide +kernel)
private def w72 : RowWindow test 72 := nextWindow w69 3 (by decide +kernel)
private def w75 : RowWindow test 75 := nextWindow w72 3 (by decide +kernel)
private def w78 : RowWindow test 78 := nextWindow w75 3 (by decide +kernel)
private def w81 : RowWindow test 81 := nextWindow w78 3 (by decide +kernel)
private def w84 : RowWindow test 84 := nextWindow w81 3 (by decide +kernel)
private def w87 : RowWindow test 87 := nextWindow w84 3 (by decide +kernel)
private def w90 : RowWindow test 90 := nextWindow w87 3 (by decide +kernel)
private def w93 : RowWindow test 93 := nextWindow w90 3 (by decide +kernel)
private def w96 : RowWindow test 96 := nextWindow w93 3 (by decide +kernel)
private def w99 : RowWindow test 99 := nextWindow w96 3 (by decide +kernel)
private def w102 : RowWindow test 102 := nextWindow w99 3 (by decide +kernel)
private def w105 : RowWindow test 105 := nextWindow w102 3 (by decide +kernel)
private def w108 : RowWindow test 108 := nextWindow w105 3 (by decide +kernel)
private def w111 : RowWindow test 111 := nextWindow w108 3 (by decide +kernel)
private def w114 : RowWindow test 114 := nextWindow w111 3 (by decide +kernel)
private def w117 : RowWindow test 117 := nextWindow w114 3 (by decide +kernel)
private def w120 : RowWindow test 120 := nextWindow w117 3 (by decide +kernel)
private def w123 : RowWindow test 123 := nextWindow w120 3 (by decide +kernel)
private def w126 : RowWindow test 126 := nextWindow w123 3 (by decide +kernel)
private def w129 : RowWindow test 129 := nextWindow w126 3 (by decide +kernel)
private def w130 : RowWindow test 130 := nextWindow w129 1 (by decide +kernel)
lemma spans : RectBorder 5 5 6 2 11 5 := from_rank X Y Z x y z (checked M (rows 5 5 6) (cols 5 5 6 11) a b w130.verified)
end Five
lemma border_five : RectBorder 5 5 6 2 11 5 := Five.spans
end CriticalTensor.ConsecutiveBorder

namespace CriticalTensor.ConsecutiveBorder
namespace Eight

open Binary

def X (t : Fin 5) (i : Fin 5) : ℤ := flags #[
  0x1,0x2,0x4,0x8,0x10] t i
def Y (t : Fin 5) (i : Side 8) : ℤ := flags #[
  0x1de,0x3cb,0x1bd,0x163,0x33d] t (finSumFinEquiv i)
def Z (t : Fin 5) (i : Side 9) : ℤ := flags #[
  0x26,0x3f9,0x3b3,0x386,0x155] t (finSumFinEquiv i)
def x (t : Fin 18) (i : Fin 5) : ℤ := flags #[
  0x13,0x1a,0x19,0x16,0x1a,0x1c,0xb,0x12,0xb,0x9,0x19,0x6,0x17,0x16,0x1f,0x3,0x13,0x15] t i
def y (t : Fin 18) (i : Fin 8) : ℤ := flags #[
  0x11,0x94,0xeb,0xab,0x3c,0x8b,0x3d,0x4d,0x9d,0xe1,0xcd,0xb3,0x44,0xbc,0x21,0xc,0xfd,0x82] t i
def z (t : Fin 18) (i : Fin 9) : ℤ := flags #[
  0x19f,0x76,0x132,0x101,0xdc,0x2f,0x5a,0x169,0x4c,0x25,0x67,0xe1,0x1c9,0xbf,0xd1,0x79,0xc0,0x42] t i

def M := matrix X Y Z x y z

private def a0 : Array ℕ := #[0x2000420, 0x100021000000000000000, 0x80000000000000000000000000000, 0x20000000000000000000000000000000, 0x8000000000000000000000000000000000, 0x2000000000000000000000000000000000000, 0x800000000000000000000000000000000000000, 0x200000000000000000000000000000000000000000]
private def a1 : Array ℕ := #[0x80000000000000000000000000000000000000000000, 0x20000000000000000000000000000000000000000000000, 0x4010040000401004000000000000080000000000000, 0x80200800008020080000000000001000000000000000, 0x20000000000000000, 0x400000000000000000, 0x8000000000000000000, 0x100000000000000000000]
private def a2 : Array ℕ := #[0x2000000000000000000000, 0x40000000000000000000000, 0x800000000000000000000000, 0x10000000000000000000000000, 0x200000000000000000000000000, 0x80200800008020080000000100021000000000000000, 0x100401000010040100000000200042000000000000000, 0x200802000020080200000000400084000000000000000]
private def a3 : Array ℕ := #[0x401004000040100400000000800108000000000000000, 0x802008000080200800000001000210000000000000000, 0x421084210002, 0x21084210800100000000000000, 0x8000000000000000000000000000, 0x2000000000000000000000000000000, 0x800000000000000000000000000000000, 0x200000000000000000000000000000000000]
private def a4 : Array ℕ := #[0x80000000000000000000000000000000000000, 0x20000000000000000000000000000000000000000, 0x8000000000000000000000000000000000000000000, 0x2000000000000000000000000000000000000000000000, 0x2008020080000002000000000000000100000000000002, 0x40100401000000040000000000000002000000000000040, 0x40000000000000800, 0x800000000000010000]
private def a5 : Array ℕ := #[0x10000000000000200000, 0x200000000000004000000, 0x4000000000000080000000, 0x80000000000001000000000, 0x1000000000000020000000000, 0x20000000000000400000000000, 0x400000000000008000000000000, 0x1004010040000001000010842108400080210842108001]
private def a6 : Array ℕ := #[0x2008020080000002000021084210800100421084210002, 0x4010040100000004000042108421000200842108420004, 0x8020080200000008000084210842000401084210840008, 0x10040100400000010000108421084000802108421080010, 0x842008400084, 0x42100420004200000000000000, 0x210000000000000000000000000000, 0x84000000000000000000000000000000]
private def a7 : Array ℕ := #[0x21000000000000000000000000000000000, 0x8400000000000000000000000000000000000, 0x2100000000000000000000000000000000000000, 0x840000000000000000000000000000000000000000, 0x210000000000000000000000000000000000000000000, 0x84000000000000000000000000000000000000000000000, 0x10040000401004010000000000000000000000000004, 0x200800008020080200000000000000000000000000080]
private def a8 : Array ℕ := #[0x1000, 0x20000, 0x400000, 0x8000000, 0x100000000, 0x2000000000, 0x40000000000, 0x800000000000]
private def a9 : Array ℕ := #[0x10000000000000, 0x84210002108421084000000000000000210802100021, 0x108420004210842108000000000000000421004200042, 0x210840008421084210000000000000000842008400084, 0x421080010842108420000000000000001084010800108, 0x842100021084210840000000000000002108021000210, 0x1084000002100, 0x84200000108000000000000000]
private def a10 : Array ℕ := #[0x400000000000000000000000000000, 0x100000000000000000000000000000000, 0x40000000000000000000000000000000000, 0x10000000000000000000000000000000000000, 0x4000000000000000000000000000000000000000, 0x1000000000000000000000000000000000000000000, 0x400000000000000000000000000000000000000000000, 0x100000000000000000000000000000000000000000000000]
private def a11 : Array ℕ := #[0x20000200800000000000000000000400000000000008, 0x400004010000000000000000000008000000000000100, 0x100000000000002000, 0x2000000000000040000, 0x40000000000000800000, 0x800000000000010000000, 0x10000000000000200000000, 0x200000000000004000000000]
private def a12 : Array ℕ := #[0x4000000000000080000000000, 0x80000000000001000000000000, 0x1000000000000020000000000000, 0x80000802000000000010840000021000210800000420, 0x100001004000000000021080000042000421000000840, 0x200002008000000000042100000084000842000001080, 0x400004010000000000084200000108001084000002100, 0x800008020000000000108400000210002108000004200]
private def a13 : Array ℕ := #[0x100401004010, 0x8020080200800000000000000, 0x40000000000000000000000000000, 0x10000000000000000000000000000000, 0x4000000000000000000000000000000000, 0x1000000000000000000000000000000000000, 0x400000000000000000000000000000000000000, 0x100000000000000000000000000000000000000000]
private def a14 : Array ℕ := #[0x40000000000000000000000000000000000000000000, 0x10000000000000000000000000000000000000000000000, 0x10040000001004010040000000000000000000000000010, 0x200800000020080200800000000000000000000000000200, 0x4000, 0x80000, 0x1000000, 0x20000000]
private def a15 : Array ℕ := #[0x400000000, 0x8000000000, 0x100000000000, 0x2000000000000, 0x40000000000000, 0x1004000000100401004000000000000000010040100401, 0x2008000000200802008000000000000000020080200802, 0x4010000000401004010000000000000000040100401004]
private def a16 : Array ℕ := #[0x8020000000802008020000000000000000080200802008, 0x10040000001004010040000000000000000100401004010, 0x4e6004e739cc00, 0x273002739ce60000000000000000, 0x4c000000004c000000000000000000000000000, 0x9800000000980000000000000000000000000000, 0x1ad681ad0000, 0xd6b40d6800000000000000000]
private def a17 : Array ℕ := #[0x1a000000680006800000000000000000000000000000000, 0x34000000d0000d0000000000000000000000000000000000, 0x6400ce400c8000, 0x3200672006400000000000000000, 0x19064190001900019064000000000000000000000000000, 0x320c83200032000320c80000000000000000000000000000, 0x58000000005800, 0x2c000000002c0000000000000000]
private def a18 : Array ℕ := #[0x16000160001600016058000000000000000000000000000, 0x2c0002c0002c0002c0b00000000000000000000000000000, 0x35a06b5a00000, 0x1ad035ad0000000000000000000, 0x1a0681a06800000000000000000000000000000000, 0x340d0340d0000000000000000000000000000000000, 0xe039ce7000, 0x701ce7380000000000000000]
private def a19 : Array ℕ := #[0x1c000000001c0001c070000000000000000000000000000, 0x380000000038000380e00000000000000000000000000000, 0xb02d6058000, 0x5816b02c00000000000000000, 0xb02c0b02c0002c000000000000000000000000000, 0x1605816058000580000000000000000000000000000, 0x48129024004800, 0x2409481200240000000000000000]
private def a20 : Array ℕ := #[0x48000001204800048000000000000000000000000000, 0x900000024090000900000000000000000000000000000, 0xb0016b00000, 0x5800b58000000000000000000, 0xb0000002c0b02c0002c000000000000000000000000000, 0x160000005816058000580000000000000000000000000000, 0x4800902400, 0x240048120000000000000000]
private def a21 : Array ℕ := #[0x9024090000000000024000000000000000000000000000, 0x120481200000000000480000000000000000000000000000, 0x19c8019ce400, 0xce400ce720000000000000000, 0x19064000001906400064000000000000000000000000000, 0x320c800000320c8000c80000000000000000000000000000, 0xc63000001800, 0x631800000c0000000000000000]
private def a22 : Array ℕ := #[0x6000060180000006018000000000000000000000000000, 0xc0000c030000000c0300000000000000000000000000000, 0x5ef7002e005c00, 0x2f7b8017002e0000000000000000, 0x5c000000005c00000000000000000000000000000000, 0xb800000000b8000000000000000000000000000000000, 0x2c0b5ad6b5800, 0x1605ad6b5ac0000000000000000]
private def a23 : Array ℕ := #[0x16000160581605800000000000000000000000000000000, 0x2c0002c0b02c0b0000000000000000000000000000000000, 0x3ff07c0007c00, 0x1ff83e0003e0000000000000000, 0x1f000000000007c000000000000000000000000000, 0x3e00000000000f80000000000000000000000000000, 0x318c6000c00, 0x18c6300060000000000000000]
private def a24 : Array ℕ := #[0x300c00000000000000000000000000000000, 0x6018000000000000000000000000000000000, 0x2730000000000, 0x139800000000000000000000000, 0x1304c1304c1304c0004c000000000000000000000000000, 0x260982609826098000980000000000000000000000000000, 0x1500000a8000, 0xa800005400000000000000000]
private def a25 : Array ℕ := #[0x15000000000000015000000000000000000000000000000, 0x2a00000000000002a0000000000000000000000000000000]
private def aBlocks : Array (Array ℕ) := #[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25]
private def a (i : ℕ) := ((aBlocks[i/8]?.getD #[])[i%8]?.getD 0)
private def b0 : Array ℕ := #[0x6b374659c13071244208ec80982dc657be5900f2bd54f1a2d, 0x55000401d05c0050142bc01c018358c066dbd4968404081400, 0x37806465921e271274a08c3001a599a52ec2d48aa8454f1c7a, 0x27b30031c4477751200b7e4c08cd43f72e2f449c2fd5443d30, 0x73c00000000000000000000000000, 0x11c00001dc1c00101020001c08b358c00000049bc400055cbc, 0x15c7430596384730702a0ec019838ee44129048f379801067f, 0x37806465921e271274a08c3001a599a52e19148aa8454f1c7a]
private def b1 : Array ℕ := #[0x55800401505400505469f721005977c066dbd49e48f5087400, 0x20000300022000220000080010004200002cc007f41c0000ac, 0x510000011010001010217721087f58c0420004800400016563, 0x40000004400004004048f00000262f40420000000cf5000000, 0x10000000000000000, 0x15444441c80800105508e01c009518d3460004858e010c4c63, 0x100000000000000000000000000000, 0x444004480844004048c00008580000410000058cf40f78bd]
private def b2 : Array ℕ := #[0x55444001d4584050106ab01c09a577810200049688f5060cbd, 0x20000000000000000, 0x40c44040185c40400163e73d007e40130fdbd01bc6f5066863, 0x200000000000000000000000000000, 0x844004880444004048c00009a400004100000d4cf40f18bd, 0x40804004404004404000d73d00262f4110dbd01e40010709de, 0x40000000000000000, 0x55c400415c180410502ac721082758c07200049bc400070cbd]
private def b3 : Array ℕ := #[0x400000000000000000000000000000, 0x40c00000cc0c00000001773d00cc00004200001bc0000439de, 0x4044044444044400444270000800000178dbd0000cf40e18bd, 0x80000000000000000, 0x40c44040985c00400161173d00ea401320dbd01bc6f5043863, 0x800000000000000000000000000000, 0xc00000cc0000000000000001a400000000000d4000010000, 0x4080000440400440404b273d00262f414300001e4cf50709de]
private def b4 : Array ℕ := #[0x100000000000000000, 0x40444000981404004168600001a46f522c00001306f4060863, 0x1000000000000000000000000000000, 0x51844005581444105069b721014f58c00300048d48f40c2dde, 0x55444041d41840101029672109a577800edbd4968401060cbd, 0x200000000000000000, 0x40804400141004000522273d082640133400001e4a010910de, 0x2000000000000000000000000000000]
private def b5 : Array ℕ := #[0x40444004480844004049b73d08580000030000058cf40f78bd, 0x15004405905c04505468c01c01a577807700049688f5081400, 0x400000000000000000, 0xc44044585c40400161b73d007e40134ddbd01bc6f5066863, 0x1573d00000000000000000000000000, 0x51000001dc1000101021772101db58c0420004930400097400, 0x440400044440400409573d08262f403600000000010e18bd, 0x6cdbd0000000000000]
private def b6 : Array ℕ := #[0x804404d41044000522873d08946f535900001e4a000b40de, 0x8000000000000000000000000000000, 0x55840045981844505462f01c00b358c15c00049bc8f40b4400, 0x40000004400004404058e00000262f41430000000cf5000000, 0x1000000000000000000, 0x44844404d05c04040179073d01fc6f5309dbd008c6f40061bd, 0x10000000000000000000000000000000, 0x3024773046a04670050635abd0130a1224118801303e4045d3f]
private def b7 : Array ℕ := #[0x55000401d05c0050142bc01c018358c066dbd4969b24081400, 0x24e9044ce828ac0c08434dcd953692453a93924541c34511f0, 0x3134737412e5c27500448aaa10859ce7014c350058e340f79e1, 0x44434448a220080c680afe049510d78539f4d855521b4e6b1a, 0x9dc, 0x15c44005b4184410502197210983c5c441000488e2f4010717, 0x178144a5921e071054208ec021a531a57b5e148d7ca94f1eda, 0x55800401505400505469f721005b2fc066dbd49e48f5087400]
private def b8 : Array ℕ := #[0x4484004884e4674c8442f9679c1801015c2ac85e79681e1197, 0x1000, 0x40000004400004004048f00000262f40420000004cf5000000, 0xce26a92004068e8e0cc30a760ca484a43823aa40fe1dd07a2d, 0x15444441c80800105508e01c009118d3460004858e010c4c63, 0xc00c00013cb012e58c0000008151f2c000000, 0x2000, 0x55444001d4584050106ab01c09a577810200049608f5060cbd]
private def b9 : Array ℕ := #[0x132d2d21fef20edef0ab03519cff0be05ed776dde4f2855537, 0x40c44040185c40400163e73d007640130fdbd01bc6f5066863, 0x1d830405b2fc08507c20eaec91538f4424f4d48849375a76c4, 0x4000, 0x40804004404004404000d73d00262f4110dbd01f40010709de, 0x136961e97a368a1e7ce3c35194930be019d776c8372a8a0d8a, 0x55c400415c180410502ac721083758c07200049bc400070cbd, 0xc43040462e0084c6000893b9418d78424f4d858d21b5f22c4]
private def b10 : Array ℕ := #[0x19de, 0x4044044444044400444270000800000178dbd0020cf40e18bd, 0xee2788e00406af8c2c430a2a2ca42ca46de2aa472b7150788d, 0x40c44040985c00400161173d00ca401320dbd01bc6f5043863, 0x5107440d36f84c5c3069fdd19c938f4427f4d4c1c5c3510e79, 0x10000, 0x4080000440400440404b273d00262f414300001a4cf50709de, 0x248e69846eec29ce848b8d91bd5a27453735d050985bca48d9]
private def b11 : Array ℕ := #[0x40444000981404004168600001e46f522c00001306f4060863, 0x4000000cc0000c00000074f601fe58c0420008089f2c042000, 0x20000, 0x55444041d41840101029672109a577800edbd49e8401060cbd, 0x3942694972fc29de54ab8d8db49327450735d4c3c377cf1dba, 0x40804400141004000522273d08a640133400001e4a010910de, 0x59c0404d10dc0c5c1428301c04b500011d0004d58400141dde, 0x40000]
private def b12 : Array ℕ := #[0x15004405905c04505468c01c01a577807700048688f5081400, 0x86ae69644cce06ce4481f9bd0c7484a52523a245adc5ce6a2d, 0xc44044585c40400161b73d017e40134ddbd01bc6f5066863, 0x800404000c00040c80a100001d800015f00001000001569de, 0x80000, 0x440400044440400409573d08262f403600001f9f2d0e18bd, 0x71caa9cd3a34a19e1ce97e46b443274417ee0cc14f83d10dba, 0x804404d41044000522873d091237935900001e4a000b40de]
private def b13 : Array ℕ := #[0x1544004594d84450986b8721085b58c11e00048917d81f6563, 0x100000, 0x40000004400004404058e00000262f41430000400cf5000000, 0xcee1ed202222ce0ee08b0086955a0be15cd77a5ebfde800054, 0x44844404d05c04040179073d05fc6f5309dbd008c6f40061bd, 0xc7440026244c402c58093b98d0d78465f4d84b1eef507a79, 0x325f43760ea0b40002443d68d00958d873aec1499a7a14b44d1, 0x10000000]
private def b14 : Array ℕ := #[0x37a34465901e261074208c6c01a52ca57bf4948aa9354f1dee, 0x3134773057a04771040635a51014ff9e24118841307f404593f, 0x400000000000000000000000000, 0x4, 0x15834445b23c073074208ec001a53ca57bde148aa3854f1cb6, 0x37a34465901e261074208c6c01a52ca57bf4d48aa9354f1dee, 0x100000000000000000000, 0x35834445901c0730542b177d01a59c857bde148aa3854f1d86]
private def b15 : Array ℕ := #[0x30003001101020123000010c007ff0c00011040000800002a0, 0x20000000, 0x235834765b01e051274ab177d01a538852e9a548aa8b54f1d26, 0x1001000002a0007f58c0000004000a80000000, 0x800000000000000000000000000, 0x8, 0x32020002320200b9b111000872000060007feac0002a8, 0x235834765b01e051274ab177d01a538852e9ad48aa8b54f1d26]
private def b16 : Array ℕ := #[0x200000000000000000000, 0x20000320022000220000000010008f00002cc007f41c000398, 0x31447004480464027068c2a00130a8024111001306b4045ac3, 0x40000000, 0x10100000001000080005c00000000554000000a40000000, 0x17c40470ca1b431104484f3c00ea69673ad3d099a5314b46b9, 0x1000000000000000000000000000, 0x10]
private def b17 : Array ℕ := #[0x200032000202320200b9b1100002720000600000180000018, 0x10100000001000080005c00000000554100000a40000000, 0x400000000000000000000, 0x22030320220003222000005c00002f00002900000a4000016c, 0x30447004480464027068c2a00130a802411100130674045ac3, 0x80000000, 0x20220030020002202000b99bd00001420002ec0000b300000c8, 0x444004581454014068c2a001300002410000130c74045863]
private def b18 : Array ℕ := #[0x2000000000000000000000000000, 0x20, 0x32000202320200b9b1100002720000600000180000028, 0x20220030020002202000b99bd00001420002cc0000b300000c8, 0x800000000000000000000, 0x32020000322200002ac00002f000006000001800002a8, 0x325f43760ea0b40003443d6c900958d873aec1499a6b14b44d1, 0x100000000]
private def b19 : Array ℕ := #[0x20220020020002302000b9b1100001420002ec0000ab00000c8, 0x3134773147a14771050635921014ff9e241188413053404593f, 0x4000000000000000000000000000, 0x40, 0x15834465b21c2410542b15d111a51b857bf4d48d56194f1c9e, 0x20220020020002302000b9b1100001420002ac0000ab00000c8, 0x1000000000000000000000, 0x35834465903c241054208c6c11a5bba57bf4d48d56194f1dea]
private def b20 : Array ℕ := #[0x3124773057a14671050635ae5014ff9e241188413063404593f, 0x200000000, 0x17804465921e061054208e9c01a531a57bd3d48aa2f54f1eda, 0x304c73760e81b70001443d44d009590873acb5499afb14b47e5, 0x8000000000000000000000000000, 0x80, 0x200002000002320200b9b1110001a20002ac007f59c0000ec, 0x17804465921e061054208e9c01a531a57bdbd48aa2f54f1eda]
private def b21 : Array ℕ := #[0x2000000000000000000000, 0x2030020202003202000005c100086000005c007fe5c00026c, 0x11444004480444005068c3b0013000024100001302f4045863, 0x400000000, 0x20012100000021022080005c0000a800555100000a400002a0, 0x27f70460c81b731034484f6c00ea74673af49099a8a14b458d, 0x10000000000000000000000000000, 0x100]
private def b22 : Array ℕ := #[0x15804445901c0410542b172111a577857bdbd48d5dd94f1dde, 0x20012100000021022080005c0000a800554100000a400002a0, 0x4000000000000000000000, 0x15834445b23c041074208c6c11a5d7a57bf4d48d56194f1f1a, 0x31203330132102310100b9ae5007ff9e0001884000ac000015c, 0x800000000, 0x17804465921e061054a08e9c01a531a52e93d48aa2f54f1eda, 0x304837764b00f3400542b144d01a590857bcb548aa9454f1f86]
private def b23 : Array ℕ := #[0x20000000000000000000000000000, 0x200, 0x200002020202320200b9b111000ba20002ac007f59c00026c, 0x17804465921e061054a08e9c01a531a52eb3d48aa2f54f1eda, 0x8000000000000000000000, 0x203002020200320200b99e1100086200005c007fe5c00026c]
private def bBlocks : Array (Array ℕ) := #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23]
private def b (i : ℕ) := ((bBlocks[i/8]?.getD #[])[i%8]?.getD 0)
private def test := directCheck M (rows 5 8 9) (cols 5 8 9 18) a b
private def w3 : RowWindow test 3 := nextWindow (start test) 3 (by decide +kernel)
private def w6 : RowWindow test 6 := nextWindow w3 3 (by decide +kernel)
private def w9 : RowWindow test 9 := nextWindow w6 3 (by decide +kernel)
private def w12 : RowWindow test 12 := nextWindow w9 3 (by decide +kernel)
private def w15 : RowWindow test 15 := nextWindow w12 3 (by decide +kernel)
private def w18 : RowWindow test 18 := nextWindow w15 3 (by decide +kernel)
private def w21 : RowWindow test 21 := nextWindow w18 3 (by decide +kernel)
private def w24 : RowWindow test 24 := nextWindow w21 3 (by decide +kernel)
private def w27 : RowWindow test 27 := nextWindow w24 3 (by decide +kernel)
private def w30 : RowWindow test 30 := nextWindow w27 3 (by decide +kernel)
private def w33 : RowWindow test 33 := nextWindow w30 3 (by decide +kernel)
private def w36 : RowWindow test 36 := nextWindow w33 3 (by decide +kernel)
private def w39 : RowWindow test 39 := nextWindow w36 3 (by decide +kernel)
private def w42 : RowWindow test 42 := nextWindow w39 3 (by decide +kernel)
private def w45 : RowWindow test 45 := nextWindow w42 3 (by decide +kernel)
private def w48 : RowWindow test 48 := nextWindow w45 3 (by decide +kernel)
private def w51 : RowWindow test 51 := nextWindow w48 3 (by decide +kernel)
private def w54 : RowWindow test 54 := nextWindow w51 3 (by decide +kernel)
private def w57 : RowWindow test 57 := nextWindow w54 3 (by decide +kernel)
private def w60 : RowWindow test 60 := nextWindow w57 3 (by decide +kernel)
private def w63 : RowWindow test 63 := nextWindow w60 3 (by decide +kernel)
private def w66 : RowWindow test 66 := nextWindow w63 3 (by decide +kernel)
private def w69 : RowWindow test 69 := nextWindow w66 3 (by decide +kernel)
private def w72 : RowWindow test 72 := nextWindow w69 3 (by decide +kernel)
private def w75 : RowWindow test 75 := nextWindow w72 3 (by decide +kernel)
private def w78 : RowWindow test 78 := nextWindow w75 3 (by decide +kernel)
private def w81 : RowWindow test 81 := nextWindow w78 3 (by decide +kernel)
private def w84 : RowWindow test 84 := nextWindow w81 3 (by decide +kernel)
private def w87 : RowWindow test 87 := nextWindow w84 3 (by decide +kernel)
private def w90 : RowWindow test 90 := nextWindow w87 3 (by decide +kernel)
private def w93 : RowWindow test 93 := nextWindow w90 3 (by decide +kernel)
private def w96 : RowWindow test 96 := nextWindow w93 3 (by decide +kernel)
private def w99 : RowWindow test 99 := nextWindow w96 3 (by decide +kernel)
private def w102 : RowWindow test 102 := nextWindow w99 3 (by decide +kernel)
private def w105 : RowWindow test 105 := nextWindow w102 3 (by decide +kernel)
private def w108 : RowWindow test 108 := nextWindow w105 3 (by decide +kernel)
private def w111 : RowWindow test 111 := nextWindow w108 3 (by decide +kernel)
private def w114 : RowWindow test 114 := nextWindow w111 3 (by decide +kernel)
private def w117 : RowWindow test 117 := nextWindow w114 3 (by decide +kernel)
private def w120 : RowWindow test 120 := nextWindow w117 3 (by decide +kernel)
private def w123 : RowWindow test 123 := nextWindow w120 3 (by decide +kernel)
private def w126 : RowWindow test 126 := nextWindow w123 3 (by decide +kernel)
private def w129 : RowWindow test 129 := nextWindow w126 3 (by decide +kernel)
private def w132 : RowWindow test 132 := nextWindow w129 3 (by decide +kernel)
private def w135 : RowWindow test 135 := nextWindow w132 3 (by decide +kernel)
private def w138 : RowWindow test 138 := nextWindow w135 3 (by decide +kernel)
private def w141 : RowWindow test 141 := nextWindow w138 3 (by decide +kernel)
private def w144 : RowWindow test 144 := nextWindow w141 3 (by decide +kernel)
private def w147 : RowWindow test 147 := nextWindow w144 3 (by decide +kernel)
private def w150 : RowWindow test 150 := nextWindow w147 3 (by decide +kernel)
private def w153 : RowWindow test 153 := nextWindow w150 3 (by decide +kernel)
private def w156 : RowWindow test 156 := nextWindow w153 3 (by decide +kernel)
private def w159 : RowWindow test 159 := nextWindow w156 3 (by decide +kernel)
private def w162 : RowWindow test 162 := nextWindow w159 3 (by decide +kernel)
private def w165 : RowWindow test 165 := nextWindow w162 3 (by decide +kernel)
private def w168 : RowWindow test 168 := nextWindow w165 3 (by decide +kernel)
private def w171 : RowWindow test 171 := nextWindow w168 3 (by decide +kernel)
private def w174 : RowWindow test 174 := nextWindow w171 3 (by decide +kernel)
private def w177 : RowWindow test 177 := nextWindow w174 3 (by decide +kernel)
private def w180 : RowWindow test 180 := nextWindow w177 3 (by decide +kernel)
private def w183 : RowWindow test 183 := nextWindow w180 3 (by decide +kernel)
private def w186 : RowWindow test 186 := nextWindow w183 3 (by decide +kernel)
private def w189 : RowWindow test 189 := nextWindow w186 3 (by decide +kernel)
private def w190 : RowWindow test 190 := nextWindow w189 1 (by decide +kernel)
lemma spans : RectBorder 5 8 9 2 18 5 := from_rank X Y Z x y z (checked M (rows 5 8 9) (cols 5 8 9 18) a b w190.verified)
end Eight
lemma border_eight : RectBorder 5 8 9 2 18 5 := Eight.spans
end CriticalTensor.ConsecutiveBorder

namespace CriticalTensor.ConsecutiveBase

private def three34Points : Array ℕ := #[
  0x1, 0x1, 0x1, 0x2, 0x2, 0x2, 0x4, 0x4, 0x4,
  0x6, 0x8, 0x5, 0x5, 0x1, 0x7]

private def three34Multiplier : Array ℕ := #[
  0x5, 0x5000, 0x5000000, 0x30, 0x10000, 0x10000000,
  0x100, 0x100000, 0x100000000, 0x800, 0xa00000, 0x200000000,
  0x4, 0x4004000, 0x0, 0x0, 0x28, 0xc0,
  0xe00, 0x4006000, 0x0, 0x80000, 0x400400000, 0x0,
  0x20000000, 0x0, 0x800000000, 0x4000000, 0x8000000, 0x40000,
  0x0, 0x0, 0x20, 0x80, 0x400, 0x0,
  0x2000006, 0x0, 0x8008000, 0x0, 0x8020000, 0x40000000,
  0x80000000, 0x0, 0x800000, 0x400000000, 0x0, 0x0,
  0x2000000, 0x0]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4500000 in
theorem three34 : CriticalTensor.Spans 3 3 4 5 := by
  apply CriticalTensor.RectFiveBase.checked three34Points (fun j => three34Multiplier[j]?.getD 0)
  decide +kernel

end CriticalTensor.ConsecutiveBase

namespace CriticalTensor.ConsecutiveBase

private def three45Points : Array ℕ := #[
  0x1, 0x1, 0x1, 0x2, 0x2, 0x2, 0x4, 0x4, 0x4,
  0x8, 0x8, 0x3, 0x3, 0x10, 0x5, 0xc, 0x1f, 0x6]

private def three45Multiplier : Array ℕ := #[
  0x4020001, 0x4028000, 0x240000000, 0xc00e00000000000, 0x90, 0x0,
  0x4800400000000, 0xc06000000000000, 0x200100, 0x4800000, 0x0, 0xc20000000000000,
  0x400, 0x1000000, 0x8000000000, 0xc80000000000000, 0x4000, 0x20000000,
  0x40000000000, 0x800000000000000, 0x80, 0x4000000, 0xc00800000000000, 0x0,
  0x0, 0xa8, 0x200040, 0xe00, 0x28005000, 0x4010000,
  0x4080000, 0x4400000, 0x6000000, 0x10000000, 0xc00000100000000, 0xc04800800000000,
  0x10804000000000, 0xc00020000000000, 0xc00100000000000, 0xc00c00000000000, 0x1000000000000, 0x8000000000000,
  0x0, 0xa00000000000000, 0x4020000, 0xa0, 0x200000, 0x800,
  0x0, 0x800080000000, 0x4000000000000, 0xc10000000000000, 0x810000000000, 0x880000000000,
  0x0, 0x82, 0x4020084, 0x40000, 0x0, 0x4100000,
  0x1000000000, 0xc10802000000000, 0x0, 0xcc0000000000000, 0x0, 0x100000000000000,
  0x28000000, 0x2000, 0x0, 0x200000000, 0xc00000000000000, 0x0]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4500000 in
theorem three45 : CriticalTensor.Spans 3 4 5 6 := by
  apply CriticalTensor.RectFiveBase.checked three45Points (fun j => three45Multiplier[j]?.getD 0)
  decide +kernel

end CriticalTensor.ConsecutiveBase

namespace CriticalTensor.ConsecutiveBorder
namespace Case33

def X (t : Fin 3) (i : Fin 3) : ℤ := flags #[1,2,4] t i
def Y (t : Fin 3) (i : Side 3) : ℤ := flags #[11,2,9] t (finSumFinEquiv i)
def Z (t : Fin 3) (i : Side 4) : ℤ := flags #[46,25,19] t (finSumFinEquiv i)
def x (t : Fin 5) (i : Fin 3) : ℤ := flags #[6,5,6,7,5] t i
def y (t : Fin 5) (i : Fin 3) : ℤ := flags #[6,3,5,2,7] t i
def z (t : Fin 5) (i : Fin 4) : ℤ := flags #[12,3,8,11,15] t i

private def M := matrix X Y Z x y z

private def columns := packedEntry #[
    0x40001000200000200008001000001000048000000000000008000000000000008000000000000008248000000000000008248,
    0x2402000000000000002402020020920824800400412410490008008248209200000200008000000001000040000000008000200,
    0x2000000000000010000000000000080000000000000400000000000002000002000000000000002000000000000002000000000,
    0x24000000000000024000000000000004024000000000000004024000004804000000000090080000000001201000000000400000000,
    0x9000000040240000000020000000000000100000000000000800000000000004000800000000020004000000000124000000000000,
    0xb40000000000000000b40c30000000000006180000000000000036000000000000000036000024000000100900480000002012,
    0x38fc0000000000000038fc0c00c00000000006006000000000000030000000000000000030000028a00000000000145000000000,
    0xa28a0000000000514500000000000002db4000000000000002db400380000000000001c0000000000] 54
private def preimages := packedEntry #[
    0x10050005c940000888080026002e280084016001800422cad041811611d3022300600180072a0021003000600100333151a4448472e50210df90040019,
    0x22200000180072c0000006900000000010101a40000000488c046906001cb00000040000000000c8c140011251cb0223026009800b88000000800000000,
    0x230110040086000000000001000000223006001800608000c8442148a180000000000020000040000de900000290000010000000000004004000000000,
    0x1220000488c046906003cb00230110a40086000000000004000000223026009800f88008005c290020000000000000800000088808002600262,
    0x120001001c006001c00000000000400021011001c004001c00200000040000000000000010000000222000001800000008080000488000,
    0x8008400600180042202100180060018000000000000002200210010006001000000000000800021021001000400108000400600180072220300180060014,
    0x800800000000004220220000000001800000000000000420020001000000100000000000100003003000100000010] 62
private def test := directCheck M (rows 3 3 4) (cols 3 3 4 5) columns preimages

private def w5 : RowWindow test 5 := nextWindow (start test) 5 (by decide +kernel)
private def w10 : RowWindow test 10 := nextWindow w5 5 (by decide +kernel)
private def w15 : RowWindow test 15 := nextWindow w10 5 (by decide +kernel)
private def w20 : RowWindow test 20 := nextWindow w15 5 (by decide +kernel)
private def w25 : RowWindow test 25 := nextWindow w20 5 (by decide +kernel)
private def w30 : RowWindow test 30 := nextWindow w25 5 (by decide +kernel)
private def w35 : RowWindow test 35 := nextWindow w30 5 (by decide +kernel)
private def w40 : RowWindow test 40 := nextWindow w35 5 (by decide +kernel)
private def w45 : RowWindow test 45 := nextWindow w40 5 (by decide +kernel)
private def w50 : RowWindow test 50 := nextWindow w45 5 (by decide +kernel)
private def w54 : RowWindow test 54 := nextWindow w50 4 (by decide +kernel)

lemma spans : RectBorder 3 3 4 2 5 3 :=
  from_rank X Y Z x y z (checked M (rows 3 3 4) (cols 3 3 4 5) columns preimages w54.verified)

end Case33

lemma border_3_3 : RectBorder 3 3 4 2 5 3 := Case33.spans

end CriticalTensor.ConsecutiveBorder

namespace CriticalTensor.ConsecutiveBorder
namespace Case34

def X (t : Fin 3) (i : Fin 3) : ℤ := flags #[1,2,4] t i
def Y (t : Fin 3) (i : Side 4) : ℤ := flags #[63,13,30] t (finSumFinEquiv i)
def Z (t : Fin 3) (i : Side 5) : ℤ := flags #[49,14,95] t (finSumFinEquiv i)
def x (t : Fin 6) (i : Fin 3) : ℤ := flags #[5,5,7,6,7,6] t i
def y (t : Fin 6) (i : Fin 4) : ℤ := flags #[3,14,15,7,5,12] t i
def z (t : Fin 6) (i : Fin 5) : ℤ := flags #[19,9,23,28,10,27] t i

private def M := matrix X Y Z x y z

private def columns := packedEntry #[
    0x208208000040000201041040000200001040000000000000000040000000000000000040000000000000000040000000000000000048008000000000000000009001,
    0x104104120020900102082082400412002041041048008240040000008000040000000000040000200000000000200001000000000001000008000000000008000040,
    0x410000000000400002080000000002400000000000000000400000000000000000400000000000000000400000000000000000002480000000000000000000490,
    0x820000000024800010400000000490000208000000009200000000000080000000000000000400000000000000002000000000000000010000000000000000080,
    0x20820000100000000104100000800000900000000000000000900000000000000000900000000000000000900000000000000000824920000000000000000104924,
    0x24924824920000000492490492400000009249209248000000000020000000000000000100000000000000000800000000000000004000000000000000020000000,
    0xa28a00000000000005145000000000000000000140a00000000000000000028140000a28000000000000005140000000000000000a05a00000000000000000140b40,
    0x30c30000000000000186180000000000000000db00000000000000000001b6000e38e380000000000071c71c0000000000000000e3fe000000000000000001c7fc0,
    0xc30000000000000006180000000000000000000d86c000000000000000001b0d800380380000000000001c01c00000000000000001c7000000000000000000038e00] 66
private def preimages := packedEntry #[
    0x10000001900b221bfb114819e9080040c6d18a1800c0000000000008c000091801c0c6db12c800c10100704d3848d130c40040400000040003099919324de39b504e0,
    0x19009228bfb11484e18090000c619c2c80000000000000040000008091010c6188a1800080803301bf802c967f0000000000018d00008880a22dde2038019e1000330dde188d167f,
    0x8000005c001c0000609303048f84d1c40099919324de39b5049c90800308bf98a1930000000000001000000091801208bf912c930010000304de188d1300000000000008000000,
    0xf3f333402c15ff47008880a22dde2038039e0000000100000000001333330cde198d07001900b221bfb114809e0080000080001c0000e0c0004cf20c7040001188180c61b1208080,
    0x91801208bf912c83000000000800000000006073034f4d84d3c40019009228bfb114809e000000040000000000c0e0004bf20c7240008091010c6188a18400000000020000000000,
    0x8000440034003000340000000000000400008008c40034000c0034800044003000300034c4444400300030001c00000000000000000400000007de00000000a0b3030f6188a18400,
    0x40c404001c001c00300000000000000000108000400038003000380000000000000800008008c80038000c003880004000300030003884404000300030002c000000000000000008,
    0x88808c000c0038000c808004002c002c000c80c404002c002c0030000000000000000020008004000c001c000c000000000000100000088884000c0034000c008004001c001c000c,
    0x808004000c002c000c000000000000200000] 72
private def test := directCheck M (rows 3 4 5) (cols 3 4 5 6) columns preimages

private def w5 : RowWindow test 5 := nextWindow (start test) 5 (by decide +kernel)
private def w10 : RowWindow test 10 := nextWindow w5 5 (by decide +kernel)
private def w15 : RowWindow test 15 := nextWindow w10 5 (by decide +kernel)
private def w20 : RowWindow test 20 := nextWindow w15 5 (by decide +kernel)
private def w25 : RowWindow test 25 := nextWindow w20 5 (by decide +kernel)
private def w30 : RowWindow test 30 := nextWindow w25 5 (by decide +kernel)
private def w35 : RowWindow test 35 := nextWindow w30 5 (by decide +kernel)
private def w40 : RowWindow test 40 := nextWindow w35 5 (by decide +kernel)
private def w45 : RowWindow test 45 := nextWindow w40 5 (by decide +kernel)
private def w50 : RowWindow test 50 := nextWindow w45 5 (by decide +kernel)
private def w55 : RowWindow test 55 := nextWindow w50 5 (by decide +kernel)
private def w60 : RowWindow test 60 := nextWindow w55 5 (by decide +kernel)
private def w65 : RowWindow test 65 := nextWindow w60 5 (by decide +kernel)
private def w66 : RowWindow test 66 := nextWindow w65 1 (by decide +kernel)

lemma spans : RectBorder 3 4 5 2 6 3 :=
  from_rank X Y Z x y z (checked M (rows 3 4 5) (cols 3 4 5 6) columns preimages w66.verified)

end Case34

lemma border_3_4 : RectBorder 3 4 5 2 6 3 := Case34.spans

end CriticalTensor.ConsecutiveBorder

namespace CriticalTensor.ConsecutiveThree

/-- Cancellation of the common last dimension leaves the ceiling of 3b/2. -/
theorem rank_formula (b : ℕ) :
    3*b*(b+1) ⌈/⌉ (3+b+(b+1)-2) = (3*b+1)/2 := by
  have hd : 3+b+(b+1)-2 = (b+1)*2 := by omega
  have hc : 3*b*(b+1) ⌈/⌉ ((b+1)*2) = 3*b ⌈/⌉ 2 := by
    apply eq_of_forall_ge_iff
    intro u
    rw [ceilDiv_le_iff_le_mul (by positivity : 0<(b+1)*2),
      ceilDiv_le_iff_le_mul (by decide : 0<2),
      show 3*b*(b+1) = (b+1)*(3*b) by ring, Nat.mul_assoc (b+1) 2 u]
    exact ⟨fun h => Nat.le_of_mul_le_mul_left h (Nat.succ_pos b), Nat.mul_le_mul_left _⟩
  rw [hd,hc,Nat.ceilDiv_eq_add_pred_div]
  omega

/-- Both parity classes are obtained by simultaneous width-two rectangular growth. -/
theorem all (b : ℕ) (hb : 3≤b) :
    Spans 3 b (b+1) (3*b*(b+1) ⌈/⌉ (3+b+(b+1)-2)) := by
  rw [rank_formula]
  by_cases he : b%2=0
  · obtain ⟨t,rfl⟩ : ∃ t, b=4+2*t := ⟨(b-4)/2,by omega⟩
    rw [show (3*(4+2*t)+1)/2 = 6+3*t by omega, show 4+2*t+1 = 5+2*t by omega]
    exact grow_rect 3 4 5 2 6 3 t ConsecutiveBase.three45 ConsecutiveBorder.border_3_4
      (cross_width_two 3 (by decide))
  · obtain ⟨t,rfl⟩ : ∃ t, b=3+2*t := ⟨(b-3)/2,by omega⟩
    rw [show (3*(3+2*t)+1)/2 = 5+3*t by omega, show 3+2*t+1 = 4+2*t by omega]
    exact grow_rect 3 3 4 2 5 3 t ConsecutiveBase.three34 ConsecutiveBorder.border_3_3
      (cross_width_two 3 (by decide))

end CriticalTensor.ConsecutiveThree

namespace CriticalTensor.RectFive

private lemma target_between {n d q : ℕ} (hd : 0 < d) (lo : d*q < n) (hi : n ≤ d*(q+1)) :
    n ⌈/⌉ d = q+1 := by
  apply le_antisymm ((ceilDiv_le_iff_le_mul hd).mpr hi)
  by_contra! h
  exact (not_le_of_gt lo) ((ceilDiv_le_iff_le_mul hd).mp (show n ⌈/⌉ d ≤ q by omega))

/-- The two infinite progressions and the exceptional square side six. -/
lemma spans_of_templates
    (b₅ : Spans 5 5 6 11) (b₆ : Spans 5 6 7 14) (b₈ : Spans 5 8 9 18)
    (r₅ : RectBorder 5 5 6 2 11 5) (r₈ : RectBorder 5 8 9 2 18 5)
    (growth : ∀ a d e h base extra t : ℕ, Spans a d e base → RectBorder a d e h base extra →
      Cross a h extra → Spans a (d+h*t) (e+h*t) (base+extra*t))
    (cross : Cross 5 2 5) (m : ℕ) (hm : 5 ≤ m) :
    Spans 5 m (m+1) (5*m*(m+1) ⌈/⌉ (5+m+(m+1)-2)) := by
  by_cases six : m=6
  · subst m
    exact b₆
  · by_cases even : m%2=0
    · obtain ⟨t,rfl⟩ : ∃ t, m=8+2*t := ⟨(m-8)/2,by omega⟩
      have side : 8+2*t+1=9+2*t := by omega
      rw [side]
      have den : 5+(8+2*t)+(9+2*t)-2=20+4*t := by omega
      rw [den]
      have num : 5*(8+2*t)*(9+2*t) ⌈/⌉ (20+4*t) = 18+5*t := by
        have h := target_between (n:=5*(8+2*t)*(9+2*t)) (d:=20+4*t) (q:=17+5*t)
          (by omega) (by nlinarith) (by nlinarith)
        omega
      rw [num]
      exact growth 5 8 9 2 18 5 t b₈ r₈ cross
    · obtain ⟨t,rfl⟩ : ∃ t, m=5+2*t := ⟨(m-5)/2,by omega⟩
      have side : 5+2*t+1=6+2*t := by omega
      rw [side]
      have den : 5+(5+2*t)+(6+2*t)-2=14+4*t := by omega
      rw [den]
      have num : 5*(5+2*t)*(6+2*t) ⌈/⌉ (14+4*t) = 11+5*t := by
        have h := target_between (n:=5*(5+2*t)*(6+2*t)) (d:=14+4*t) (q:=10+5*t)
          (by omega) (by nlinarith) (by nlinarith)
        omega
      rw [num]
      exact growth 5 5 6 2 11 5 t b₅ r₅ cross

end CriticalTensor.RectFive

namespace CriticalTensor.RectFive

theorem five_gap_one (m : ℕ) (hm : 5 ≤ m) :
    Spans 5 m (m+1) (5*m*(m+1) ⌈/⌉ (5+m+(m+1)-2)) :=
  spans_of_templates RectFiveBase.base_five RectFiveBase.base_six RectFiveBase.base_eight
    ConsecutiveBorder.border_five ConsecutiveBorder.border_eight grow_rect (cross_width_two 5 (by decide)) m hm

end CriticalTensor.RectFive

namespace CriticalTensor.Consecutive35

/-- Both remaining small first dimensions admit a spanning unrestricted tangent. -/
theorem witnesses (a b : ℕ) (ha : a=3 ∨ a=5) (hb : a≤b) :
    Spans a b (b+1) (a*b*(b+1) ⌈/⌉ (a+b+(b+1)-2)) := by
  rcases ha with rfl | rfl
  · exact ConsecutiveThree.all b hb
  · exact RectFive.five_gap_one b hb

end CriticalTensor.Consecutive35

namespace CriticalTensor.Consecutive35

open Arxiv.«0805.3777» in
theorem generic_rank (a b : ℕ) (ha : a=3 ∨ a=5) (hb : a≤b) :
    IsGenericRank [a,b,b+1] (a*b*(b+1) ⌈/⌉ (a+b+(b+1)-2)) := by
  apply OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1.generic_of_bounded a b (b+1)
    (by omega) hb (by omega)
  exact CriticalReduction.bounded_of_witness (witnesses a b ha hb)

open Arxiv.«0805.3777» in
theorem generic_rank_three (b : ℕ) (hb : 3≤b) :
    IsGenericRank [3,b,b+1] (3*b*(b+1) ⌈/⌉ (3+b+(b+1)-2)) :=
  generic_rank 3 b (Or.inl rfl) hb

open Arxiv.«0805.3777» in
theorem generic_rank_five (b : ℕ) (hb : 5≤b) :
    IsGenericRank [5,b,b+1] (5*b*(b+1) ⌈/⌉ (5+b+(b+1)-2)) :=
  generic_rank 5 b (Or.inr rfl) hb

end CriticalTensor.Consecutive35

namespace CriticalTensor.ConsecutivePublic

open Arxiv.«0805.3777»

/-- The three- and five-slice witnesses give an unconditional configuration. -/
theorem consecutive_block_witness (a b : ℕ) (ha : 3≤a) (hb : a≤b) :
    Spans a b (b+1) (a*b ⌈/⌉ 2 - 3*((a-3)/5)/2) :=
  uniform_block_bound ConsecutiveThree.all RectFive.five_gap_one a b ha hb

/-- On a dense open set the actual complex CP rank lies between the
dimension-count ceiling and the repeated five-slice construction. -/
theorem consecutive_rank_interval (a b : ℕ) (ha : 3≤a) (hb : a≤b) :
    let r := a*b*(b+1) ⌈/⌉ (a+b+(b+1)-2)
    let u := a*b ⌈/⌉ 2 - 3*((a-3)/5)/2
    ∃ U : Set (Holor ℂ [a,b,b+1]), IsOpen U ∧ Dense U ∧
      ∀ T ∈ U, r ≤ T.cprank ∧ T.cprank ≤ u := by
  classical
  intro r u
  let D := a+b+(b+1)-2
  have dpos : 0<D := by dsimp only [D]; omega
  have numpos : 0<a*b*(b+1) := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have rpos : 0<r := by
    by_contra! hz
    have he : a*b*(b+1)≤D*0 := (ceilDiv_le_iff_le_mul dpos).mp hz
    omega
  have budget : D*(r-1)<a*b*(b+1) := by
    by_contra! he
    have hh : r≤r-1 := (ceilDiv_le_iff_le_mul dpos).mpr he
    omega
  obtain ⟨U,hu,hd,hit⟩ := CriticalReduction.upper_of_witness (consecutive_block_witness a b ha hb)
  let Z := closure {T : Holor ℂ [a,b,b+1] | T.cprank ≤ r-1}
  have hz : Dense Zᶜ := interior_eq_empty_iff_dense_compl.mp (CriticalReduction.lower_of_count a b (b+1) (r-1) budget)
  refine ⟨U ∩ Zᶜ,hu.inter isClosed_closure.isOpen_compl,hd.inter_of_isOpen_left hz hu,?_⟩
  intro T ht
  have lo : ¬T.cprank≤r-1 := fun he => ht.2 (subset_closure he)
  exact ⟨by omega,hit T ht.1⟩

end CriticalTensor.ConsecutivePublic

namespace CriticalTensor.ConsecutivePublic

/-- The dimension-count ceiling for four slices and consecutive long sides. -/
lemma four_rank_formula (b : ℕ) : 4*b*(b+1) ⌈/⌉ (4+b+(b+1)-2) = b*2 := by
  have hd : 4+b+(b+1)-2=2*b+3 := by omega
  rw [hd]
  have hp : 0<2*b+3 := by omega
  apply le_antisymm
  · apply (ceilDiv_le_iff_le_mul hp).mpr
    nlinarith
  · by_contra! hh
    have hle := (ceilDiv_le_iff_le_mul hp).mp (show 4*b*(b+1) ⌈/⌉ (2*b+3) ≤ 4*b*(b+1) ⌈/⌉ (2*b+3) from le_rfl)
    have hplus : (4*b*(b+1) ⌈/⌉ (2*b+3))+1 ≤ b*2 := by omega
    have hm := Nat.mul_le_mul_left (2*b+3) hplus
    nlinarith

end CriticalTensor.ConsecutivePublic

namespace CriticalTensor.ConsecutiveGeneric

open Arxiv.«0805.3777» Set
open scoped Topology

/-- A spanning tangent at the dimension-count rank gives equality on a dense open set. -/
lemma generic_rank_of_tangent (a b c : ℕ) (ha : 3≤a) (hab : a≤b) (hbc : b≤c)
    (span : Spans a b c (a*b*c ⌈/⌉ (a+b+c-2))) :
    IsGenericRank [a,b,c] (a*b*c ⌈/⌉ (a+b+c-2)) := by
  classical
  let d := a+b+c-2
  let r := a*b*c ⌈/⌉ d
  have hd : 0<d := by dsimp only [d]; omega
  have habc : 0<a*b*c := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hrpos : 0<r := by
    by_contra! hz
    have he : a*b*c≤d*0 := (ceilDiv_le_iff_le_mul hd).mp hz
    rw [Nat.mul_zero] at he
    omega
  have hcost : d*(r-1)<a*b*c := by
    by_contra! he
    have hsmall : r≤r-1 := (ceilDiv_le_iff_le_mul hd).mpr he
    omega
  obtain ⟨U,hu,hU,hi⟩ := @CriticalReduction.upper_of_witness a b c r span
  let D := closure {T : Holor ℂ [a,b,c] | T.cprank≤r-1}
  have lower : Dense Dᶜ := interior_eq_empty_iff_dense_compl.mp
    (CriticalReduction.lower_of_count a b c (r-1) hcost)
  refine ⟨U ∩ Dᶜ,hu.inter isClosed_closure.isOpen_compl,hU.inter_of_isOpen_left lower hu,?_⟩
  intro T hT
  have hup := hi T hT.1
  have hlo : ¬ T.cprank≤r-1 := fun he => hT.2 (subset_closure he)
  change T.cprank=r
  omega

/-- For every b at least three, the complex generic rank of format
3 by b by b+1 is the ceiling of three halves of b. -/
theorem generic_rank_three_consecutive (b : ℕ) (hb : 3≤b) :
    IsGenericRank [3,b,b+1] (3*b ⌈/⌉ 2) := by
  have h := generic_rank_of_tangent 3 b (b+1) (by decide) hb (Nat.le_succ b)
    (ConsecutiveThree.all b hb)
  have rank : 3*b*(b+1) ⌈/⌉ (3+b+(b+1)-2) = 3*b ⌈/⌉ 2 := by
    rw [ConsecutiveThree.rank_formula,Nat.ceilDiv_eq_add_pred_div]
    omega
  rwa [rank] at h

/-- For every b at least four, the complex generic rank of format
4 by b by b+1 is twice b. -/
theorem generic_rank_four_consecutive (b : ℕ) (hb : 4≤b) :
    IsGenericRank [4,b,b+1] (2*b) := by
  have h := generic_rank_of_tangent 4 b (b+1) (by decide) hb (Nat.le_succ b)
    (ConsecutivePublic.four_consecutive b)
  simpa only [ConsecutivePublic.four_rank_formula, Nat.mul_comm b 2] using h

end CriticalTensor.ConsecutiveGeneric

theorem OMA.solution : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H1_R1.H1 := by
  intro a b ha hab _
  exact CriticalTensor.Consecutive35.witnesses a b ha hab
