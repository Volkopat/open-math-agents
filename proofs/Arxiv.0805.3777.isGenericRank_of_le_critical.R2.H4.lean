import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R2

/-! Width-two growth for rectangular tensors with a spanning base and border. -/

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

theorem OMA.solution : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R2.H4 := by
  intro a d e base t ha hb hr
  exact CriticalTensor.grow_rect a d e 2 base a t hb hr (CriticalTensor.cross_width_two a (by omega))
