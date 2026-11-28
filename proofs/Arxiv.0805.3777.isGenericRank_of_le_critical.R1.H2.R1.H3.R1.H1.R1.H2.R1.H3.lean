import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H1_R1_H2_R1

/-! Uniform propagation by two coordinates on each long axis for six slices. -/

namespace CriticalTensor

def Spans (a b c r : ℕ) : Prop :=
  ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
    ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
      ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))

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

namespace CriticalTensor.SixConsecutiveBorder

/-- The two-face condition with the factors fixed and the two base axes allowed to differ. -/
def Holds {D E N : Type} [Fintype N] (X : Fin 6 → Fin 6 → ℂ)
    (Y : Fin 6 → (Fin 2 ⊕ D) → ℂ) (Z : Fin 6 → (Fin 2 ⊕ E) → ℂ)
    (x : N → Fin 6 → ℂ) (y : N → D → ℂ) (z : N → E → ℂ) : Prop :=
  ∀ T : Fin 6 → (Fin 2 ⊕ D) → (Fin 2 ⊕ E) → ℂ,
    ∃ U : Fin 6 → Fin 6 → ℂ, ∃ V : Fin 6 → (Fin 2 ⊕ D) → ℂ, ∃ W : Fin 6 → (Fin 2 ⊕ E) → ℂ,
    ∃ v w : N → Fin 2 → ℂ, ∀ i j k, (j.isLeft=true ∨ k.isLeft=true) →
      T i j k = (∑ t, (U t i*(Y t j*Z t k)+X t i*(V t j*Z t k)+X t i*(Y t j*W t k))) +
        ∑ t, (x t i*(j.elim (v t) (fun _ => 0)*k.elim (fun _ => 0) (z t)) +
          x t i*(j.elim (fun _ => 0) (y t)*k.elim (w t) (fun _ => 0)))

def Witness (D E N : Type) [Fintype N] : Prop :=
  ∃ X : Fin 6 → Fin 6 → ℂ, ∃ Y : Fin 6 → (Fin 2 ⊕ D) → ℂ, ∃ Z : Fin 6 → (Fin 2 ⊕ E) → ℂ,
    ∃ x : N → Fin 6 → ℂ, ∃ y : N → D → ℂ, ∃ z : N → E → ℂ, Holds X Y Z x y z

/-- On each new interior coordinate the remaining rows form one 6-by-2 rectangle. -/
def Wing (O : Fin 6 → Fin 2 → ℂ) (X : Fin 6 → Fin 6 → ℂ) (pair : Fin 3 → Fin 6 → ℂ) : Prop :=
  ∀ T : Fin 6 → Fin 2 → ℂ, ∃ p : Fin 6 → ℂ, ∃ v : Fin 3 → Fin 2 → ℂ, ∀ i j,
    T i j = (∑ t, X t i*(p t*O t j)) + ∑ t, pair t i*v t j

private def join {D L : Type} (old : Fin 2 ⊕ D → ℂ) (new : L → ℂ) : Fin 2 ⊕ (D ⊕ L) → ℂ :=
  Sum.elim (fun j => old (.inl j)) (Sum.elim (fun j => old (.inr j)) new)

private def embed {D L : Type} : Fin 2 ⊕ D → Fin 2 ⊕ (D ⊕ L) := Sum.map id Sum.inl

/-- Add one copy of a pair of narrow faces for each new coordinate; padding labels carry zero factors. -/
lemma extend {D E N : Type} [Fintype N] (X : Fin 6 → Fin 6 → ℂ)
    (Y : Fin 6 → (Fin 2 ⊕ D) → ℂ) (Z : Fin 6 → (Fin 2 ⊕ E) → ℂ)
    (x : N → Fin 6 → ℂ) (y : N → D → ℂ) (z : N → E → ℂ) (base : Holds X Y Z x y z)
    (pair : Fin 3 → Fin 6 → ℂ) (left : Wing (fun t j => Z t (.inl j)) X pair)
    (right : Wing (fun t j => Y t (.inl j)) X pair) (L Q : Type) [Fintype L] [DecidableEq L] [Fintype Q] :
    Witness (D ⊕ L) (E ⊕ L) (N ⊕ ((L × Fin 3) ⊕ Q)) := by
  classical
  let unit (p l : L) : ℂ := if p=l then 1 else 0
  refine ⟨X,fun t => join (Y t) 0,fun t => join (Z t) 0,
    Sum.elim x (Sum.elim (fun p => pair p.2) 0),
    Sum.elim (fun t => Sum.elim (y t) 0) (Sum.elim (fun p => Sum.elim 0 (unit p.1)) 0),
    Sum.elim (fun t => Sum.elim (z t) 0) (Sum.elim (fun p => Sum.elim 0 (unit p.1)) 0),?_⟩
  intro T
  obtain ⟨U,V,W,v,w,core⟩ := base fun i j k => T i (embed j) (embed k)
  choose p vL hl using fun l : L => left (fun i k => T i (.inr (.inr l)) (.inl k))
  choose q vR hr using fun l : L => right (fun i j => T i (.inl j) (.inr (.inr l)))
  refine ⟨U,fun t => join (V t) (fun l => p l t),fun t => join (W t) (fun l => q l t),
    Sum.elim v (Sum.elim (fun g => vR g.1 g.2) 0), Sum.elim w (Sum.elim (fun g => vL g.1 g.2) 0),?_⟩
  rintro i (j|j|l) (k|k|g) he
  · simpa [join,embed,Fintype.sum_sum_type] using core i (.inl j) (.inl k) (Or.inl rfl)
  · simpa [join,embed,Fintype.sum_sum_type] using core i (.inl j) (.inr k) (Or.inl rfl)
  · simpa [join,unit,Fintype.sum_sum_type,Fintype.sum_prod_type,ite_mul,mul_ite,Finset.sum_ite_irrel,
      mul_comm,mul_left_comm,mul_assoc] using hr g i j
  · simpa [join,embed,Fintype.sum_sum_type] using core i (.inr j) (.inl k) (Or.inr rfl)
  · simp at he
  · simp at he
  · simpa [join,unit,Fintype.sum_sum_type,Fintype.sum_prod_type,ite_mul,mul_ite,Finset.sum_ite_irrel,
      mul_comm,mul_left_comm,mul_assoc] using hl l i k
  · simp at he
  · simp at he

lemma to_rect {D E N : Type} [Fintype N] {d e r : ℕ} (ed : Fin d ≃ D) (ee : Fin e ≃ E)
    (en : Fin r ≃ N) (hs : Witness D E N) : RectBorder 6 d e 2 r 6 := by
  classical
  obtain ⟨X,Y,Z,x,y,z,hs⟩ := hs
  let jd := Equiv.sumCongr (Equiv.refl (Fin 2)) ed
  let ke := Equiv.sumCongr (Equiv.refl (Fin 2)) ee
  refine ⟨X,fun t j => Y t (jd j),fun t k => Z t (ke k),fun t => x (en t),fun t j => y (en t) (ed j),
    fun t k => z (en t) (ee k),?_⟩
  intro T
  obtain ⟨U,V,W,v,w,hu⟩ := hs (fun i j k => T i (jd.symm j) (ke.symm k))
  refine ⟨U,fun t j => V t (jd j),fun t k => W t (ke k),fun t => v (en t),fun t => w (en t),?_⟩
  intro i j k he
  have edge : (jd j).isLeft=true ∨ (ke k).isLeft=true := by cases j <;> cases k <;> exact he
  have h := hu i (jd j) (ke k) edge
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply] at h
  rw [h]
  congr 1
  let term (t : N) := x t i*((jd j).elim (v t) (fun _ => 0)*(ke k).elim (fun _ => 0) (z t)) +
    x t i*((jd j).elim (fun _ => 0) (y t)*(ke k).elim (w t) (fun _ => 0))
  change (∑ t, term t) = _
  rw [← en.sum_comp term]
  apply Finset.sum_congr rfl
  intro t _
  cases j <;> cases k <;> rfl

end CriticalTensor.SixConsecutiveBorder

namespace CriticalTensor.SixConsecutiveBorder

open CriticalTensor.ConsecutiveBorder

lemma holds_of_rank {d e r : ℕ} (X : Fin 6 → Fin 6 → ℤ) (Y : Fin 6 → Side d → ℤ)
    (Z : Fin 6 → Side e → ℤ) (x : Fin r → Fin 6 → ℤ) (y : Fin r → Fin d → ℤ) (z : Fin r → Fin e → ℤ)
    (hs : Function.Surjective ((matrix X Y Z x y z).map (Int.castRingHom ℂ)).mulVec) :
    Holds (fun t i => (X t i : ℂ)) (fun t j => (Y t j : ℂ)) (fun t k => (Z t k : ℂ))
      (fun t i => (x t i : ℂ)) (fun t j => (y t j : ℂ)) (fun t k => (z t k : ℂ)) := by
  classical
  rw [cast_matrix] at hs
  intro T
  obtain ⟨v,hv⟩ := hs fun row => T (coords row).2.2 (coords row).1 (coords row).2.1
  refine ⟨fun t i => v (.inl (t,.inr (.inr i))),fun t j => v (.inl (t,.inl j)),
    fun t k => v (.inl (t,.inr (.inl k))),fun t h => v (.inr (t,.inl h)),fun t h => v (.inr (t,.inr h)),?_⟩
  intro i j k hij
  obtain ⟨u,hu⟩ : ∃ u : Rows 6 d e,coords u=(j,k,i) := by
    rcases j with j|j
    · exact ⟨.inl (j,k,i),rfl⟩
    · rcases k with k|k
      · exact ⟨.inr (j,k,i),rfl⟩
      · simp at hij
  have hh := (congrFun hv u).symm
  simp only [hu] at hh
  rw [hh]
  change (∑ q : Cols 6 d e r, matrix (fun t i => (X t i : ℂ)) (fun t j => (Y t j : ℂ))
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

end CriticalTensor.SixConsecutiveBorder

namespace CriticalTensor.SixConsecutiveBorder

open CriticalTensor.ConsecutiveBorder

def wingMatrix (O : Fin 6 → Fin 2 → ℤ) (X : Fin 6 → Fin 6 → ℤ) (pair : Fin 3 → Fin 6 → ℤ) :
    Matrix (Fin 6 × Fin 2) ((Fin 6) ⊕ (Fin 3 × Fin 2)) ℤ
  | (i,j),.inl t => X t i * O t j
  | (i,j),.inr (t,k) => if k=j then pair t i else 0

private lemma wing_of_rank (O : Fin 6 → Fin 2 → ℤ) (X : Fin 6 → Fin 6 → ℤ) (pair : Fin 3 → Fin 6 → ℤ)
    (hs : Function.Surjective ((wingMatrix O X pair).map (Int.castRingHom ℂ)).mulVec) :
    Wing (fun t j => (O t j : ℂ)) (fun t i => (X t i : ℂ)) (fun t i => (pair t i : ℂ)) := by
  intro T
  obtain ⟨p,hp⟩ := hs fun ij => T ij.1 ij.2
  refine ⟨fun t => p (.inl t),fun t j => p (.inr (t,j)),?_⟩
  intro i j
  refine (congrFun hp (i,j)).symm.trans ?_
  change (∑ c : Fin 6 ⊕ (Fin 3 × Fin 2), ((wingMatrix O X pair (i,j) c : ℤ):ℂ)*p c) = _
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro l _
    simp only [wingMatrix,Int.cast_mul]
    ring
  · apply Finset.sum_congr rfl
    intro l _
    simp [wingMatrix,apply_ite,ite_mul,Finset.sum_ite_eq']

end CriticalTensor.SixConsecutiveBorder

namespace CriticalTensor.SixConsecutiveBorder

open CriticalTensor.ConsecutiveBorder

def seedX (s : Fin 6) (i : Fin 6) : ℤ := flags #[1,2,4,8,16,32] s i
def seedY (s : Fin 6) (i : Side 2) : ℤ := flags #[2,7,15,13,5,14] s (finSumFinEquiv i)
def seedZ (s : Fin 6) (i : Side 3) : ℤ := flags #[31,1,18,23,14,5] s (finSumFinEquiv i)
def seedx (s : Fin 2) (i : Fin 6) : ℤ := flags #[59,14] s i
def seedy (s : Fin 2) (i : Fin 2) : ℤ := flags #[2,1] s i
def seedz (s : Fin 2) (i : Fin 3) : ℤ := flags #[5,4] s i
def pair (s : Fin 3) (i : Fin 6) : ℤ := flags #[3,12,48] s i

private def M := matrix seedX seedY seedZ seedx seedy seedz
private def coreColumns := packedEntry #[
    0x1000000000000000000000040000000000000000000001000000000000000000000040000000041000000000000000000000041000000000000000000000041041040000000000000000000001041041,
    0x2000000820820800000000000000410410400000000000000208208200000000000000104104100000000000000082082080000000000000041041040000000000000040000000000000,
    0x80000002000000000000002000000080000000000000080000002000000080000002000000080000002000000080000002002000000000000000000000002000000000000000000000000000080000000,
    0x100004000000000000000000000004000100000020000000800000020000010000000400000010000008000000200000008000004000000100000004000002000000080000002000001000000040000001,
    0x40040040001001000040000000100000004000000000000004000000100000000000000100000004000100100000004000000100004004000000100000004100000000000000000000000100000000000000000,
    0x208000000000000000000000200208200000000000000000000008008208800800800020020000800400400400010010000400200200200008008000200100100100004004000100080080080002002000080,
    0x82082000000002002082041041000000001001041000000000000008000000000000000000000200000000000000000000008000200200000000000000200008008000000000000008208000000000000000000,
    0x400000000000000000000000400000000000000000000000010410000000000000000000000000410400820820000000020020820410410000000010010410208208000000008008208104104000000004004104,
    0x100000000000104100000080000000000082080000040000000000041040000000000000010000000000000000000000400000000000000000000010000000400000000000000400000010000000000000010,
    0x20020000000800000000020000000000000000000000020000000000000000000000000800800000000000000000000000020020000800000000000820800000400000000000410400000200000000000208200,
    0x8008000200200000000004004000100100000000002002000080080000000001001000040040000000000000800000000000000000000020000000000000000000000800000000000800800000020000000000,
    0x38000000000000000000000000000e000000ec000000000000000000003b000000000000000000000000ec0ec000000000000000000000003b03b000020020000800800000000010010000400400000000,
    0x38000000000000000000000e000000000000000] 84
private def corePreimages := packedEntry #[
    0x802800500025994040102100000100020000000800100009b0000300000000000080000000c928f156a41b440bc8f624b20020000000027900000000000404000c0010fa02280f10c00000000000000000000002000010104117841d000001040040,
    0x20000000000000400000c0010fa03680f10c0000080000000000000009c000010004117845d0080010400c2050a6258e116ac2008348135c000000024000000000000000002000000003990000000000040000040000fa00040f10400,
    0x9081b5d2216e86000118137c00000006500000000000000000000000000400000000000000000000001000037c000080000000000002000400019e100000000000004000000000000d0000320000000000080000000000000040000000000000000,
    0x4000000000000000000000000001005082258e116a82008348135c000000100000000000000000000000000003e80000000000040000040000fa00000f104000000001000000000003c41000000000200000000001000015,
    0x3000000000010102f0200000040000040000fa00b40f1040000080010002000400014210000000000000000000000000200000380000000000000000000000000010000000010000000000000400007c000020000000400000c0000fa031c0f10c00,
    0x3c0000000000000000000c828f141201b440bd8f624b20000004000053900020000000400000c0010fa02680f10c0000080000000000000001c000000000000000000000000004000021a000200040000000000000000013a000080010002000,
    0x1000000000001c410000000000000000000000000f200001e0002000400000010000c828f152a01b4c0bc8f604b200000000000010000000040000000000001000017c000080000000000002000400009e1000000000000000000000000080,
    0x2000400005b900000000000004000000100001344000000000000000000000000008000010104117841d0000000400500002000000000000000000000000000012000000010002000300000000003e802f0200000040000040000fa00bc0f10400,
    0xc024a05c30044400025000200000000040000000000000000020004000059900000000000000000000000000100000000802000400005990040000000010104117841d0000000400540000080000000000000000000c928f157a41b440bc8f624b2,
    0x4000240000010004117841d00000004000800001000000000000000000000000001784000000000000000000004000074000000000000000000000000000404000000000000000000000000010000010004117841d000000040000,
    0xc001005c10040400025000200000000080000000000000000000004000070000000000000000000000000000200000000] 98
private def coreTest := directCheck M (rows 6 2 3) (cols 6 2 3 2) coreColumns corePreimages
private def coreW4 : RowWindow coreTest 4 := nextWindow (start coreTest) 4 (by decide +kernel)
private def coreW8 : RowWindow coreTest 8 := nextWindow coreW4 4 (by decide +kernel)
private def coreW12 : RowWindow coreTest 12 := nextWindow coreW8 4 (by decide +kernel)
private def coreW16 : RowWindow coreTest 16 := nextWindow coreW12 4 (by decide +kernel)
private def coreW20 : RowWindow coreTest 20 := nextWindow coreW16 4 (by decide +kernel)
private def coreW24 : RowWindow coreTest 24 := nextWindow coreW20 4 (by decide +kernel)
private def coreW28 : RowWindow coreTest 28 := nextWindow coreW24 4 (by decide +kernel)
private def coreW32 : RowWindow coreTest 32 := nextWindow coreW28 4 (by decide +kernel)
private def coreW36 : RowWindow coreTest 36 := nextWindow coreW32 4 (by decide +kernel)
private def coreW40 : RowWindow coreTest 40 := nextWindow coreW36 4 (by decide +kernel)
private def coreW44 : RowWindow coreTest 44 := nextWindow coreW40 4 (by decide +kernel)
private def coreW48 : RowWindow coreTest 48 := nextWindow coreW44 4 (by decide +kernel)
private def coreW52 : RowWindow coreTest 52 := nextWindow coreW48 4 (by decide +kernel)
private def coreW56 : RowWindow coreTest 56 := nextWindow coreW52 4 (by decide +kernel)
private def coreW60 : RowWindow coreTest 60 := nextWindow coreW56 4 (by decide +kernel)
private def coreW64 : RowWindow coreTest 64 := nextWindow coreW60 4 (by decide +kernel)
private def coreW68 : RowWindow coreTest 68 := nextWindow coreW64 4 (by decide +kernel)
private def coreW72 : RowWindow coreTest 72 := nextWindow coreW68 4 (by decide +kernel)
private def coreW76 : RowWindow coreTest 76 := nextWindow coreW72 4 (by decide +kernel)
private def coreW80 : RowWindow coreTest 80 := nextWindow coreW76 4 (by decide +kernel)
private def coreW84 : RowWindow coreTest 84 := nextWindow coreW80 4 (by decide +kernel)

lemma seed : Holds (fun t i => (seedX t i : ℂ)) (fun t j => (seedY t j : ℂ)) (fun t k => (seedZ t k : ℂ))
    (fun t i => (seedx t i : ℂ)) (fun t j => (seedy t j : ℂ)) (fun t k => (seedz t k : ℂ)) :=
  holds_of_rank seedX seedY seedZ seedx seedy seedz (checked M (rows 6 2 3) (cols 6 2 3 2) coreColumns corePreimages coreW84.verified)

private def leftM := wingMatrix (fun t j => seedZ t (.inl j)) seedX pair
private def leftColumns := packedEntry #[
    0xa0054002000c0020004003,
    0xa005000a0050] 12
private def leftPreimages := packedEntry #[
    0x20420c00430c0c3002043042,
    0x810020010420] 12
private def leftTest := directCheck leftM (finProdFinEquiv) (sumFin (Equiv.refl (Fin 6)) finProdFinEquiv) leftColumns leftPreimages
private def leftW4 : RowWindow leftTest 4 := nextWindow (start leftTest) 4 (by decide +kernel)
private def leftW8 : RowWindow leftTest 8 := nextWindow leftW4 4 (by decide +kernel)
private def leftW12 : RowWindow leftTest 12 := nextWindow leftW8 4 (by decide +kernel)

lemma left_wing : Wing (fun t j => (seedZ t (.inl j) : ℂ)) (fun t i => (seedX t i : ℂ)) (fun t i => (pair t i : ℂ)) :=
  wing_of_rank (fun t j => seedZ t (.inl j)) seedX pair (checked leftM (finProdFinEquiv) (sumFin (Equiv.refl (Fin 6)) finProdFinEquiv) leftColumns leftPreimages leftW12.verified)

private def rightM := wingMatrix (fun t j => seedY t (.inl j)) seedX pair
private def rightColumns := packedEntry #[
    0xa00580010004003000c002,
    0xa005000a0050] 12
private def rightPreimages := packedEntry #[
    0x30c00810c1080810830010c3,
    0x20410820010] 12
private def rightTest := directCheck rightM (finProdFinEquiv) (sumFin (Equiv.refl (Fin 6)) finProdFinEquiv) rightColumns rightPreimages
private def rightW4 : RowWindow rightTest 4 := nextWindow (start rightTest) 4 (by decide +kernel)
private def rightW8 : RowWindow rightTest 8 := nextWindow rightW4 4 (by decide +kernel)
private def rightW12 : RowWindow rightTest 12 := nextWindow rightW8 4 (by decide +kernel)

lemma right_wing : Wing (fun t j => (seedY t (.inl j) : ℂ)) (fun t i => (seedX t i : ℂ)) (fun t i => (pair t i : ℂ)) :=
  wing_of_rank (fun t j => seedY t (.inl j)) seedX pair (checked rightM (finProdFinEquiv) (sumFin (Equiv.refl (Fin 6)) finProdFinEquiv) rightColumns rightPreimages rightW12.verified)

end CriticalTensor.SixConsecutiveBorder

namespace CriticalTensor.SixConsecutiveBorder

open CriticalTensor.ConsecutiveBorder

/-- Starting with the 2-by-3 base, each additional interior coordinate on both axes
requires three more old points. Further zero old summands may be adjoined. -/
lemma borders (k padding : ℕ) : RectBorder 6 (2+k) (3+k) 2 (2+(k*3+padding)) 6 := by
  let w := extend (fun t i => (seedX t i : ℂ)) (fun t j => (seedY t j : ℂ)) (fun t j => (seedZ t j : ℂ))
    (fun t i => (seedx t i : ℂ)) (fun t j => (seedy t j : ℂ)) (fun t j => (seedz t j : ℂ)) seed
    (fun t i => (pair t i : ℂ)) left_wing right_wing (Fin k) (Fin padding)
  exact to_rect finSumFinEquiv.symm finSumFinEquiv.symm
    (sumFin (Equiv.refl (Fin 2)) (sumFin finProdFinEquiv (Equiv.refl (Fin padding)))).symm w

end CriticalTensor.SixConsecutiveBorder

namespace CriticalTensor.SixConsecutive

/-- The two-column border admits every old point count at least 3m−4. -/
theorem uniform_border (m r : ℕ) (hm : 6 ≤ m) (hr : 3 * m - 4 ≤ r) :
    RectBorder 6 m (m + 1) 2 r 6 := by
  let k := m - 2
  let padding := r - (3 * m - 4)
  have left : 2 + k = m := by dsimp only [k]; omega
  have right : 3 + k = m + 1 := by omega
  have points : 2 + (k * 3 + padding) = r := by dsimp only [k,padding]; omega
  simpa only [left,right,points] using SixConsecutiveBorder.borders k padding

/-- Any spanning six-slice configuration above the border threshold extends
by two coordinates on each long axis at the cost of six new points. -/
theorem width_two (m r : ℕ) (hm : 6 ≤ m) (hr : 3 * m - 4 ≤ r)
    (span : Spans 6 m (m + 1) r) : Spans 6 (m + 2) (m + 3) (r + 6) := by
  simpa only [Nat.mul_one,Nat.add_assoc] using
    grow_rect 6 m (m + 1) 2 r 6 1 span (uniform_border m r hm hr) (cross_width_two 6 (by decide))

end CriticalTensor.SixConsecutive

theorem OMA.solution :
    OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H1_R1_H2_R1.H3 :=
  CriticalTensor.SixConsecutive.width_two
