import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1

/-! Generic rank for six-slice complex tensors with equal last dimensions.

The construction starts at square sizes 6, 7, 10 and 11. Growing both
long axes by two uses six additional simple tensors. A 72-row border and
two 12-row extensions supply a common border construction for all four
bases. The cross has one column for every one of its 24 coordinates.
The verified dimension count identifies the expected generic rank.

For the general critical-format conjecture see Friedland,
https://arxiv.org/abs/0805.3777.
-/

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

namespace CriticalTensor.Growth

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

end CriticalTensor.Growth

namespace CriticalTensor.Growth

open MvPolynomial

structure Dimensions where
  a : ℕ
  d : ℕ
  h : ℕ
  base : ℕ
  extra : ℕ

variable (p : Dimensions)

abbrev Pt (G : Type) := Fin p.base ⊕ (G × Fin p.extra)
abbrev Axis (G : Type) := Fin p.d ⊕ (G × Fin p.h)
abbrev LocalAxis := Fin p.h ⊕ Fin p.d
abbrev Dir (I : Type) := Fin p.a ⊕ (I ⊕ I)
abbrev V (G : Type) := (Fin p.base × Dir p (Fin p.d)) ⊕ (G × Fin p.extra × Dir p (LocalAxis p))
abbrev RR (G : Type) := Fin p.a × Axis p G × Axis p G
abbrev CC (G : Type) := Pt p G × Dir p (Axis p G)
abbrev Pair (G : Type) := {z : G × G // z.1 ≠ z.2}
abbrev Sector (G : Type) := Unit ⊕ (G ⊕ Pair G)
abbrev Arm := (Fin p.h × Fin p.d) ⊕ ((Fin p.d × Fin p.h) ⊕ (Fin p.h × Fin p.h))

def arms : Arm p → LocalAxis p × LocalAxis p
  | .inl (j,k) => (.inl j,.inr k)
  | .inr (.inl (j,k)) => (.inr j,.inl k)
  | .inr (.inr (j,k)) => (.inl j,.inl k)

def loc {G : Type} (g : G) : LocalAxis p → Axis p G
  | .inl u => .inr (g,u)
  | .inr j => .inl j

def Row {G : Type} : Sector G → Type
  | .inl _ => Fin p.a × Fin p.d × Fin p.d
  | .inr (.inl _) => Fin p.a × Arm p
  | .inr (.inr _) => Fin p.a × Fin p.h × Fin p.h

def Col {G : Type} : Sector G → Type
  | .inl _ => Fin p.base × Dir p (Fin p.d)
  | .inr (.inl _) => (Fin p.extra × Dir p (LocalAxis p)) ⊕ (Fin p.base × (Fin p.h ⊕ Fin p.h))
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

def tail (b : Fin p.base → Fin p.d → K) (B : G → Fin p.extra → LocalAxis p → K) : Pt p G → Axis p G → K
  | .inl t,.inl j => b t j
  | .inl _,.inr _ => 0
  | .inr (g,t),.inl j => B g t (.inr j)
  | .inr (g,t),.inr (h,i) => if h=g then B g t (.inl i) else 0

def B (x : V p G → K) := tail p (fun t j => x (.inl (t,.inr (.inl j)))) (fun g t j => x (.inr (g,t,.inr (.inl j))))
def Cc (x : V p G → K) := tail p (fun t k => x (.inl (t,.inr (.inr k)))) (fun g t k => x (.inr (g,t,.inr (.inr k))))

def tangent (x : V p G → K) (r : RR p G) : CC p G → K
  | (t,.inl h) => if h=r.1 then B p x t r.2.1 * Cc p x t r.2.2 else 0
  | (t,.inr (.inl h)) => if h=r.2.1 then A p x t r.1 * Cc p x t r.2.2 else 0
  | (t,.inr (.inr h)) => if h=r.2.2 then A p x t r.1 * B p x t r.2.1 else 0

def full (x : V p G → K) : Matrix (Σ s : Sector G, Row p s) (Σ s : Sector G, Col p s) K :=
  fun r c => tangent p x (row p r.1 r.2) (col p c.1 c.2)

def block (x : V p G → K) (s : Sector G) : Matrix (Row p s) (Col p s) K :=
  fun r c => tangent p x (row p s r) (col p s c)

lemma tail_loc (b : Fin p.base → Fin p.d → K) (H : G → Fin p.extra → LocalAxis p → K)
    (g : G) (t : Fin p.extra) (j : LocalAxis p) : tail p b H (.inr (g,t)) (loc p g j) = H g t j := by
  cases j <;> simp [tail,loc]

omit [DecidableEq G] in
lemma loc_eq (g : G) (j k : LocalAxis p) : loc p g j=loc p g k ↔ j=k := by cases j <;> cases k <;> simp [loc]

private lemma tail_map {L : Type} [CommSemiring L] (φ : K →+* L) (b : Fin p.base → Fin p.d → K)
    (H : G → Fin p.extra → LocalAxis p → K) (t : Pt p G) (j : Axis p G) :
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

end CriticalTensor.Growth

namespace CriticalTensor.Growth

variable (p : Dimensions) {G : Type} [DecidableEq G]

def param (a : Fin p.base → Fin p.a → ℂ) (b c : Fin p.base → Fin p.d → ℂ)
    (A : G → Fin p.extra → Fin p.a → ℂ) (B C : G → Fin p.extra → LocalAxis p → ℂ) : V p G → ℂ
  | .inl (t,.inl i) => a t i
  | .inl (t,.inr (.inl j)) => b t j
  | .inl (t,.inr (.inr k)) => c t k
  | .inr (g,t,.inl i) => A g t i
  | .inr (g,t,.inr (.inl j)) => B g t j
  | .inr (g,t,.inr (.inr k)) => C g t k

lemma base_rank (hb : Spans p.a p.d p.d p.base) :
    ∃ x : V p G → ℂ, Function.Surjective (block p x (.inl ())).mulVec := by
  classical
  obtain ⟨a,b,c,hb⟩ := hb
  let x : V p G → ℂ := param p a b c 0 0 0
  refine ⟨x,?_⟩
  intro y
  obtain ⟨u,v,w,hu⟩ := hb fun i j k => y (i,j,k)
  let z : Fin p.base × Dir p (Fin p.d) → ℂ := fun (t,h) => h.elim (u t) (Sum.elim (v t) (w t))
  refine ⟨z,?_⟩
  funext r
  obtain ⟨i,j,k⟩ := r
  change (∑ s : Fin p.base × Dir p (Fin p.d), tangent p x (i,.inl j,.inl k) (col p (.inl ()) s) * z s) = y (i,j,k)
  rw [hu,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp [tangent,col,x,param,A,B,Cc,tail,z,ite_mul,Finset.sum_ite_eq']
  ring

def target (y : Fin p.a × Arm p → ℂ) (i : Fin p.a) : LocalAxis p → LocalAxis p → ℂ
  | .inl j,.inl k => y (i,.inr (.inr (j,k)))
  | .inl j,.inr k => y (i,.inl (j,k))
  | .inr j,.inl k => y (i,.inr (.inl (j,k)))
  | .inr _,.inr _ => 0

lemma target_arms (y : Fin p.a × Arm p → ℂ) (i : Fin p.a) (r : Arm p) :
    target p y i (arms p r).1 (arms p r).2=y (i,r) := by
  rcases r with ⟨j,k⟩|⟨j,k⟩|⟨j,k⟩ <;> rfl

lemma arms_hit (r : Arm p) : (arms p r).1.isLeft=true ∨ (arms p r).2.isLeft=true := by
  rcases r with ⟨j,k⟩|⟨j,k⟩|⟨j,k⟩ <;> simp [arms]

lemma border_rank (g : G) (hr : Border p.a p.d p.h p.base p.extra) :
    ∃ x : V p G → ℂ, Function.Surjective (block p x (.inr (.inl g))).mulVec := by
  classical
  obtain ⟨aa,bb,cc,a,b,c,hr⟩ := hr
  let x : V p G → ℂ := param p a b c (fun _ => aa) (fun _ => bb) (fun _ => cc)
  refine ⟨x,?_⟩
  intro y
  obtain ⟨u,v,w,vb,wb,hu⟩ := hr (target p y)
  let z : (Fin p.extra × Dir p (LocalAxis p)) ⊕ (Fin p.base × (Fin p.h ⊕ Fin p.h)) → ℂ
    | .inl (t,h) => h.elim (u t) (Sum.elim (v t) (w t))
    | .inr (t,h) => h.elim (vb t) (wb t)
  refine ⟨z,?_⟩
  funext r
  obtain ⟨i,r⟩ := r
  change (∑ s : (Fin p.extra × Dir p (LocalAxis p)) ⊕ (Fin p.base × (Fin p.h ⊕ Fin p.h)),
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

end CriticalTensor.Growth

namespace CriticalTensor.Growth

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

end CriticalTensor.Growth

namespace CriticalTensor.Growth

open MvPolynomial

variable (p : Dimensions) {G : Type} [Fintype G] [DecidableEq G]

def actual (x : V p G → ℂ) : Matrix (RR p G) (CC p G) ℂ := tangent p x

lemma common (hb : Spans p.a p.d p.d p.base) (hr : Border p.a p.d p.h p.base p.extra)
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

lemma action (x : V p G → ℂ) (z : CC p G → ℂ) (i : Fin p.a) (j k : Axis p G) :
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

end CriticalTensor.Growth

namespace CriticalTensor

open Growth

/-- A base block, its border with one regular block, and an ordered pair of regular
blocks suffice for an arbitrary finite number of regular blocks along the two equal axes. -/
lemma grow (a d h base extra t : ℕ) (hb : Spans a d d base)
    (hr : Border a d h base extra) (hc : Cross a h extra) :
    Spans a (d+h*t) (d+h*t) (base+extra*t) := by
  classical
  let p : Dimensions := ⟨a,d,h,base,extra⟩
  let G := Fin t
  let e : Fin (d+h*t) ≃ Axis p G := Fintype.equivOfCardEq (by simp [G,p,Axis,Nat.mul_comm])
  let f : Fin (base+extra*t) ≃ Pt p G := Fintype.equivOfCardEq (by simp [G,p,Pt,Nat.mul_comm])
  obtain ⟨x,hx⟩ := common p (G:=G) hb hr hc
  refine ⟨fun t i => A p x (f t) i,fun t j => B p x (f t) (e j),fun t k => Cc p x (f t) (e k),?_⟩
  intro T
  obtain ⟨z,hz⟩ := hx fun r => T r.1 (e.symm r.2.1) (e.symm r.2.2)
  refine ⟨fun t i => z (f t,.inl i),fun t j => z (f t,.inr (.inl (e j))),
    fun t k => z (f t,.inr (.inr (e k))),?_⟩
  intro i j k
  have hw := (congrFun hz (i,e j,e k)).symm
  simp only [Equiv.symm_apply_apply] at hw
  rw [action] at hw
  exact hw.trans (f.sum_comp (fun t => z (t,Sum.inl i)*(B p x t (e j)*Cc p x t (e k)) +
    A p x t i*(z (t,Sum.inr (Sum.inl (e j)))*Cc p x t (e k)) +
    A p x t i*(B p x t (e j)*z (t,Sum.inr (Sum.inr (e k)))))).symm

end CriticalTensor

namespace CriticalTensor.SixBase

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

abbrev Slot (G : Type) (s : ℕ) := G × G × Fin s
abbrev Parameters (G W : Type) (s d : ℕ) := Slot G s × (Fin d ⊕ (Fin d ⊕ W))
abbrev Columns (G W : Type) (s d : ℕ) :=
  (G × Fin s × Fin d) ⊕ ((G × Fin s × Fin d) ⊕ (Fin s × W))

variable {s d : ℕ}

def LocalSpan {G W : Type} [Fintype G] (a b : Slot G s → Fin d → ℂ)
    (c : Slot G s → W → ℂ) (g h : G) : Prop :=
  ∀ T : Fin d → Fin d → W → ℂ,
    ∃ u v : G → Fin s → Fin d → ℂ, ∃ w : Fin s → W → ℂ, ∀ i j k,
      T i j k =
        (∑ l, ∑ t, u l t i * (b (l,h,t) j * c (l,h,t) k)) +
        (∑ l, ∑ t, a (g,l,t) i * (v l t j * c (g,l,t) k)) +
        ∑ t, a (g,h,t) i * (b (g,h,t) j * w t k)

def pad {G : Type} [DecidableEq G] (g : G) (v : Fin d → ℂ) (i : G × Fin d) : ℂ :=
  if g = i.1 then v i.2 else 0

lemma assemble {G W : Type} [Fintype G] [DecidableEq G] (a b : Slot G s → Fin d → ℂ)
    (c : Slot G s → W → ℂ) (H : ∀ g h, LocalSpan a b c g h)
    (T : (G × Fin d) → (G × Fin d) → W → ℂ) :
    ∃ u v : Slot G s → (G × Fin d) → ℂ, ∃ w : Slot G s → W → ℂ, ∀ i j k,
      T i j k = ∑ z, (u z i * (pad z.2.1 (b z) j * c z k) +
        pad z.1 (a z) i * (v z j * c z k) +
        pad z.1 (a z) i * (pad z.2.1 (b z) j * w z k)) := by
  classical
  choose U V Z h using fun g h => H g h (fun i j k => T (g,i) (h,j) k)
  refine ⟨fun z i => U i.1 z.2.1 z.1 z.2.2 i.2,
    fun z j => V z.1 j.1 z.2.1 z.2.2 j.2, fun z => Z z.1 z.2.1 z.2.2, ?_⟩
  rintro ⟨g,i⟩ ⟨f,j⟩ k
  rw [h g f i j k]
  simp only [Finset.sum_add_distrib]
  congr 1
  · congr 1
    · simp [Fintype.sum_prod_type, pad, ite_mul, mul_ite, Finset.sum_ite_irrel]
    · simp [Fintype.sum_prod_type, pad, ite_mul, Finset.sum_ite_irrel]
  · simp [Fintype.sum_prod_type, pad, ite_mul, mul_ite, Finset.sum_ite_irrel]

def aval {G W : Type} (x : Parameters G W s d → ℂ) (z : Slot G s) (i : Fin d) := x (z, Sum.inl i)
def bval {G W : Type} (x : Parameters G W s d → ℂ) (z : Slot G s) (j : Fin d) := x (z, Sum.inr (Sum.inl j))
def cval {G W : Type} (x : Parameters G W s d → ℂ) (z : Slot G s) (k : W) := x (z, Sum.inr (Sum.inr k))

noncomputable def polynomialMatrix {G W : Type} [DecidableEq W] (g h : G) :
    Matrix (Fin d × Fin d × W) (Columns G W s d) (MvPolynomial (Parameters G W s d) ℂ)
  | (i,j,k), Sum.inl (l,t,q) =>
      if q = i then X ((l,h,t), Sum.inr (Sum.inl j)) * X ((l,h,t), Sum.inr (Sum.inr k)) else 0
  | (i,j,k), Sum.inr (Sum.inl (l,t,q)) =>
      if q = j then X ((g,l,t), Sum.inl i) * X ((g,l,t), Sum.inr (Sum.inr k)) else 0
  | (i,j,k), Sum.inr (Sum.inr (t,q)) =>
      if q = k then X ((g,h,t), Sum.inl i) * X ((g,h,t), Sum.inr (Sum.inl j)) else 0

lemma polynomial_action {G W : Type} [Fintype G] [Fintype W] [DecidableEq W]
    (g h : G) (x : Parameters G W s d → ℂ) (y : Columns G W s d → ℂ) (i j : Fin d) (k : W) :
    ((polynomialMatrix (s:=s) (d:=d) g h).map (eval x)).mulVec y (i,j,k) =
      (∑ l, ∑ t, y (Sum.inl (l,t,i)) * (bval x (l,h,t) j * cval x (l,h,t) k)) +
      (∑ l, ∑ t, aval x (g,l,t) i * (y (Sum.inr (Sum.inl (l,t,j))) * cval x (g,l,t) k)) +
      ∑ t, aval x (g,h,t) i * (bval x (g,h,t) j * y (Sum.inr (Sum.inr (t,k)))) := by
  classical
  change (∑ z : Columns G W s d, eval x (polynomialMatrix g h (i,j,k) z) * y z) = _
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, polynomialMatrix, aval, bval, cval,
    apply_ite, Finset.sum_ite_eq', mul_assoc, mul_comm, add_assoc]

lemma local_iff_surjective {G W : Type} [Fintype G] [Fintype W] [DecidableEq W]
    (g h : G) (x : Parameters G W s d → ℂ) :
    LocalSpan (aval x) (bval x) (cval x) g h ↔
      Function.Surjective ((polynomialMatrix (s:=s) (d:=d) g h).map (eval x)).mulVec := by
  constructor
  · intro H T
    obtain ⟨u,v,w,hT⟩ := H fun i j k => T (i,j,k)
    let y : Columns G W s d → ℂ := Sum.elim (fun z => u z.1 z.2.1 z.2.2)
      (Sum.elim (fun z => v z.1 z.2.1 z.2.2) (fun z => w z.1 z.2))
    refine ⟨y, ?_⟩
    funext z
    obtain ⟨i,j,k⟩ := z
    rw [polynomial_action]
    exact (hT i j k).symm
  · intro H T
    obtain ⟨y,hy⟩ := H fun z => T z.1 z.2.1 z.2.2
    refine ⟨fun l t i => y (Sum.inl (l,t,i)), fun l t j => y (Sum.inr (Sum.inl (l,t,j))),
      fun t k => y (Sum.inr (Sum.inr (t,k))), ?_⟩
    intro i j k
    exact (congrFun hy (i,j,k)).symm.trans (polynomial_action g h x y i j k)

lemma simultaneous_local {G W : Type} [Fintype G] [Fintype W] [DecidableEq W]
    (H : ∀ g h : G, ∃ x : Parameters G W s d → ℂ, LocalSpan (aval x) (bval x) (cval x) g h) :
    ∃ x : Parameters G W s d → ℂ, ∀ g h : G, LocalSpan (aval x) (bval x) (cval x) g h := by
  classical
  have h (p : G × G) : ∃ x : Parameters G W s d → ℂ,
      Function.Surjective ((polynomialMatrix p.1 p.2).map (eval x)).mulVec := by
    obtain ⟨x,hx⟩ := H p.1 p.2
    exact ⟨x, (local_iff_surjective _ _ _).mp hx⟩
  obtain ⟨x, _, hx⟩ := simultaneous_surjectivity (fun p : G × G => polynomialMatrix p.1 p.2)
    h 1 one_ne_zero
  exact ⟨x, fun g h => (local_iff_surjective g h x).mpr (hx (g,h))⟩

def relabel {G H : Type} (e f : G ≃ H) (z : Slot G s) : Slot H s := (e z.1, f z.2.1, z.2.2)

lemma relabel_local {G H W : Type} [Fintype G] [Fintype H] (e f : G ≃ H)
    (a b : Slot H s → Fin d → ℂ) (c : Slot H s → W → ℂ) (g h : G)
    (hs : LocalSpan a b c (e g) (f h)) :
    LocalSpan (fun z => a (relabel e f z)) (fun z => b (relabel e f z))
      (fun z => c (relabel e f z)) g h := by
  intro T
  obtain ⟨u,v,w,hT⟩ := hs T
  refine ⟨fun l => u (e l), fun l => v (f l), w, ?_⟩
  intro i j k
  rw [hT i j k]
  dsimp only [relabel]
  congr 1
  congr 1
  · exact (e.sum_comp (fun l => ∑ t, u l t i * (b (l,f h,t) j * c (l,f h,t) k))).symm
  · exact (f.sum_comp (fun l => ∑ t, a (e g,l,t) i * (v l t j * c (e g,l,t) k))).symm

set_option maxHeartbeats 800000 in
/-- One local witness works in every cell after relabeling the two group indices.
Their determinant conditions then hold at a single shared choice of the factors. -/
lemma spans_of_cell {g d s a : ℕ} [NeZero g]
    (x₀ : Parameters (Fin g) (Fin a) s d → ℂ)
    (h₀ : LocalSpan (aval x₀) (bval x₀) (cval x₀) 0 0) :
    CriticalTensor.Spans a (g*d) (g*d) (g*(g*s)) := by
  classical
  let G := Fin g
  let W := Fin a
  have hw (i j : G) : ∃ x : Parameters G W s d → ℂ,
      LocalSpan (aval x) (bval x) (cval x) i j := by
    let e := Equiv.swap i 0
    let f := Equiv.swap j 0
    have ho : LocalSpan (aval x₀) (bval x₀) (cval x₀) (e i) (f j) := by simpa [e,f] using h₀
    exact ⟨fun z => x₀ (relabel e f z.1,z.2), relabel_local e f (aval x₀) (bval x₀) (cval x₀) i j ho⟩
  obtain ⟨x,h⟩ := simultaneous_local hw
  let A := fun z : Slot G s => pad z.1 (aval x z)
  let B := fun z : Slot G s => pad z.2.1 (bval x z)
  let C := cval x
  let e : (G × Fin d) ≃ Fin (g*d) := finProdFinEquiv
  let er : Slot G s ≃ Fin (g*(g*s)) := ((Equiv.refl G).prodCongr finProdFinEquiv).trans finProdFinEquiv
  refine ⟨fun t => C (er.symm t),fun t j => A (er.symm t) (e.symm j),
    fun t k => B (er.symm t) (e.symm k),?_⟩
  intro T
  obtain ⟨u,v,w,hw⟩ := assemble (aval x) (bval x) (cval x) h (fun j k i => T i (e j) (e k))
  refine ⟨fun t => w (er.symm t),fun t j => u (er.symm t) (e.symm j),
    fun t k => v (er.symm t) (e.symm k),?_⟩
  intro i j k
  have hv := hw (e.symm j) (e.symm k) i
  simp only [Equiv.apply_symm_apply] at hv
  rw [hv, ← er.sum_comp]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Equiv.symm_apply_apply,A,B,C]
  ring

end CriticalTensor.SixBase

namespace CriticalTensor.SixBase.Binary

def intBit (b : Bool) : ℤ := if b then 1 else 0
def fieldBit (b : Bool) : ZMod 2 := if b then 1 else 0

lemma cast_intBit (b : Bool) : ((intBit b : ℤ) : ZMod 2) = fieldBit b := by cases b <;> rfl

lemma fieldBit_xor (a b : Bool) : fieldBit (a ^^ b) = fieldBit a + fieldBit b := by
  cases a <;> cases b <;> decide

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

end CriticalTensor.SixBase.Binary

namespace CriticalTensor.SixBase

open MvPolynomial Binary

def prodFin {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (f : B ≃ Fin b) : A × B ≃ Fin (a*b) :=
  (e.prodCongr f).trans finProdFinEquiv

def sumFin {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (f : B ≃ Fin b) : A ⊕ B ≃ Fin (a+b) :=
  (Equiv.sumCongr e f).trans finSumFinEquiv

def rowOrder (d a : ℕ) : Fin d × Fin d × Fin a ≃ Fin (d*(d*a)) :=
  prodFin (Equiv.refl _) finProdFinEquiv

def colOrder (g s d a : ℕ) :
    Columns (Fin g) (Fin a) s d ≃ Fin (g*(s*d)+(g*(s*d)+s*a)) :=
  sumFin (prodFin (Equiv.refl _) finProdFinEquiv)
    (sumFin (prodFin (Equiv.refl _) finProdFinEquiv) finProdFinEquiv)

def factorBit {g s d a : ℕ} (masks : Array ℕ) (p : Parameters (Fin g) (Fin a) s d) : ℤ :=
  let z := p.1
  let idx := ((z.1.val*g+z.2.1.val)*s+z.2.2.val)*3
  match p.2 with
  | .inl i => intBit ((masks[idx]?.getD 0).testBit i.val)
  | .inr (.inl j) => intBit ((masks[idx+1]?.getD 0).testBit j.val)
  | .inr (.inr k) => intBit ((masks[idx+2]?.getD 0).testBit k.val)

def integerMatrix {g s d a : ℕ} [NeZero g] (masks : Array ℕ) :
    Matrix (Fin d × Fin d × Fin a) (Columns (Fin g) (Fin a) s d) ℤ
  | (i,j,k), .inl (l,t,q) =>
    if q=i then factorBit (g:=g) (s:=s) (d:=d) (a:=a) masks ((l,0,t), Sum.inr (.inl j)) *
      factorBit (g:=g) (s:=s) (d:=d) (a:=a) masks ((l,0,t), Sum.inr (.inr k)) else 0
  | (i,j,k), .inr (.inl (l,t,q)) =>
    if q=j then factorBit (g:=g) (s:=s) (d:=d) (a:=a) masks ((0,l,t), .inl i) *
      factorBit (g:=g) (s:=s) (d:=d) (a:=a) masks ((0,l,t), Sum.inr (.inr k)) else 0
  | (i,j,k), .inr (.inr (t,q)) =>
    if q=k then factorBit (g:=g) (s:=s) (d:=d) (a:=a) masks ((0,0,t), .inl i) * factorBit (g:=g) (s:=s) (d:=d) (a:=a) masks ((0,0,t), .inr (.inl j)) else 0

lemma evaluate_integer {g s d a : ℕ} [NeZero g] (masks : Array ℕ) :
    (integerMatrix (g:=g) (s:=s) (d:=d) (a:=a) masks).map (Int.castRingHom ℂ) =
      (polynomialMatrix (W:=Fin a) (s:=s) (d:=d) (0:Fin g) 0).map
        (eval (fun p => (factorBit masks p : ℂ))) := by
  ext ⟨i,j,k⟩ z
  rcases z with ⟨l,t,h⟩|⟨l,t,h⟩|⟨t,h⟩ <;>
    simp [Matrix.map_apply,integerMatrix,polynomialMatrix,apply_ite] <;> split <;> simp_all

end CriticalTensor.SixBase

namespace CriticalTensor.SixBase

open Binary

private def addMultiple (v : ℤ) (w z : ℕ) : ℕ := if v%2=0 then z else w ^^^ z

private lemma eval_addMultiple (v : ℤ) (w z j : ℕ) :
    fieldBit ((addMultiple v w z).testBit j) =
      (v : ZMod 2)*fieldBit (w.testBit j) + fieldBit (z.testBit j) := by
  have h : v%2=0 ∨ v%2=1 := by omega
  rw [← ZMod.intCast_mod v 2]
  rcases h with h|h <;> simp [addMultiple,h,Nat.testBit_xor,fieldBit_xor]

private def foldWord : (n : ℕ) → (Fin n → ℕ → ℕ) → ℕ → ℕ
  | 0, _, v => v
  | n+1, f, v => f (Fin.last n) (foldWord n (fun i => f i.castSucc) v)

private lemma eval_fold (j : ℕ) {n : ℕ} (f : Fin n → ℕ → ℕ) (v : ℕ) (g : Fin n → ZMod 2)
    (hf : ∀ i z, fieldBit ((f i z).testBit j) = g i + fieldBit (z.testBit j)) :
    fieldBit ((foldWord n f v).testBit j) = (∑ i,g i) + fieldBit (v.testBit j) := by
  induction n with
  | zero => simp [foldWord]
  | succ n ih =>
    rw [foldWord,hf,ih (fun i => f i.castSucc) (fun i => g i.castSucc)
      (fun i => hf i.castSucc),Fin.sum_univ_castSucc]
    abel

section RowProduct
variable {g s d a : ℕ} [NeZero g]
private abbrev Key (g s d a : ℕ) := Columns (Fin g) (Fin a) s d

/-- Only three column families can contribute to one row. The multiplier carries
all output columns simultaneously in the bits of one natural number. -/
def rowProduct (data : Array ℕ) (b : Key g s d a → ℕ) (r : Fin d × Fin d × Fin a) : ℕ :=
  let op := fun c acc => addMultiple (integerMatrix data r c) (b c) acc
  let v := foldWord g (fun l z => foldWord s (fun t => op (.inl (l,t,r.1))) z) 0
  let w := foldWord g (fun l z => foldWord s (fun t => op (.inr (.inl (l,t,r.2.1)))) z) v
  foldWord s (fun t => op (.inr (.inr (t,r.2.2)))) w

private lemma eval_product (data : Array ℕ) (b : Key g s d a → ℕ) (r : Fin d × Fin d × Fin a) (j : ℕ) :
    fieldBit ((rowProduct data b r).testBit j) =
      ∑ k, ((integerMatrix data r k : ℤ) : ZMod 2) * fieldBit ((b k).testBit j) := by
  obtain ⟨u,v,w⟩ := r
  let f : Key g s d a → ZMod 2 := fun k => ((integerMatrix data (u,v,w) k : ℤ) : ZMod 2)*fieldBit ((b k).testBit j)
  let op := fun (k : Key g s d a) (z : ℕ) => addMultiple (integerMatrix data (u,v,w) k) (b k) z
  have step (k : Key g s d a) (z : ℕ) : fieldBit ((op k z).testBit j) = f k + fieldBit (z.testBit j) := eval_addMultiple _ _ _ _
  have twice (c : Fin g → Fin s → Key g s d a) (z : ℕ) :
      fieldBit ((foldWord g (fun l y => foldWord s (fun t => op (c l t)) y) z).testBit j) =
        (∑ l, ∑ t, f (c l t)) + fieldBit (z.testBit j) := by
    apply eval_fold
    intro l y
    exact eval_fold j _ y _ (fun t => step _)
  change fieldBit ((foldWord s (fun t => op (.inr (.inr (t,w))))
    (foldWord g (fun l z => foldWord s (fun t => op (.inr (.inl (l,t,v)))) z)
      (foldWord g (fun l z => foldWord s (fun t => op (.inl (l,t,u))) z) 0))).testBit j) = ∑ k, f k
  rw [eval_fold (g:=fun t => f (.inr (.inr (t,w)))) (hf:=fun t => step _)]
  rw [twice (fun l t => .inr (.inl (l,t,v))), twice (fun l t => .inl (l,t,u))]
  have right :
      (∑ k, f k) = (∑ l,∑ t, f (.inl (l,t,u))) +
        ((∑ l,∑ t, f (.inr (.inl (l,t,v)))) + ∑ t,f (.inr (.inr (t,w)))) := by
    simp [f,Fintype.sum_sum_type,Fintype.sum_prod_type,integerMatrix,apply_ite,ite_mul]
  rw [right]
  simp only [Nat.zero_testBit,fieldBit,Bool.false_eq_true,if_false,add_zero]
  abel

end RowProduct

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

lemma from_rows {g s d a : ℕ} [NeZero g] (data : Array ℕ) (b : Columns (Fin g) (Fin a) s d → ℕ)
    (h : ∀ i : Fin (d*(d*a)), fit (rowProduct data b ((rowOrder d a).symm i)) i.val = true) :
    CriticalTensor.Spans a (g*d) (g*d) (g*(g*s)) := by
  let e := rowOrder d a
  let K := Columns (Fin g) (Fin a) s d
  let M : Matrix (Fin (d*(d*a))) K ℤ := fun i j => integerMatrix data (e.symm i) j
  let N := M.map (Int.castRingHom (ZMod 2))
  let T : Matrix K (Fin (d*(d*a))) (ZMod 2) := fun j i => fieldBit ((b j).testBit i.val)
  let L := N*T
  have hL (i j : Fin (d*(d*a))) : L i j = fieldBit ((rowProduct data b (e.symm i)).testBit j.val) :=
    (eval_product data b (e.symm i) j.val).symm
  have ht : L.IsLowerTriangular := by
    intro i j hij
    change i.val < j.val at hij
    have bit : (rowProduct data b (e.symm i)).testBit j.val = false := off_bit (h i) hij
    rw [hL,bit]
    rfl
  have hd : L.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular L ht]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    rw [hL]
    have bit : (rowProduct data b (e.symm i)).testBit i.val = true := (Bool.and_eq_true_iff.mp (h i)).1
    rw [bit]
    exact one_ne_zero
  have hsurj : Function.Surjective L.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  have hn : Function.Surjective N.mulVec := by
    intro y
    obtain ⟨z,hz⟩ := hsurj y
    exact ⟨T.mulVec z,(Matrix.mulVec_mulVec _ _ _).trans hz⟩
  have hs := lift_surj M hn
  apply spans_of_cell (fun p => (factorBit data p : ℂ))
  apply (local_iff_surjective _ _ _).mpr
  rw [← evaluate_integer]
  intro y
  obtain ⟨z,hz⟩ := hs (y ∘ e.symm)
  refine ⟨z,?_⟩
  funext i
  have h' := congrFun hz (e i)
  change (∑ k, ((M (e i) k : ℤ) : ℂ)*z k) = y (e.symm (e i)) at h'
  change (∑ k, ((integerMatrix data i k : ℤ) : ℂ)*z k)=y i
  simpa only [M,Equiv.symm_apply_apply] using h'

end CriticalTensor.SixBase

namespace CriticalTensor.SixBase

open Binary

/-- Natural-index folds keep numeric execution independent of the finite index casts. -/
private def sweep (f : ℕ → ℕ → ℕ) (z : ℕ) : ℕ → ℕ
  | 0 => z
  | t+1 => f t (sweep f z t)

private lemma fold_index (f : ℕ → ℕ → ℕ) (z n : ℕ) :
    foldWord n (fun t => f t.val) z = sweep f z n := by
  induction n with
  | zero => rfl
  | succ n h => exact congrArg (f n) h

private def productBit (data : Array ℕ) (t u i v j : ℕ) : Bool :=
  (data[t+u]?.getD 0).testBit i && (data[t+v]?.getD 0).testBit j

private def addBit (h : Bool) (w z : ℕ) := if h then w ^^^ z else z

private lemma add_bits (a b : Bool) (w z : ℕ) :
    addMultiple (intBit a * intBit b) w z = addBit (a && b) w z := by
  cases a <;> cases b <;> simp [intBit,addMultiple,addBit]

def fastProduct (g s d a : ℕ) (data : Array ℕ) (b : ℕ → ℕ) (i j k : ℕ) : ℕ :=
  let u := sweep (fun l z => sweep (fun t =>
    addBit (productBit data ((l*g*s+t)*3) 1 j 2 k) (b ((l*s+t)*d+i))) z s) 0 g
  let v := sweep (fun l z => sweep (fun t =>
    addBit (productBit data ((l*s+t)*3) 0 i 2 k) (b (g*(s*d)+(l*s+t)*d+j))) z s) u g
  sweep (fun t => addBit (productBit data (t*3) 0 i 1 j) (b (g*(s*d)+(g*(s*d)+t*a+k)))) v s

private lemma col1 {g s d a : ℕ} (l : Fin g) (t : Fin s) (h : Fin d) :
    (colOrder g s d a (.inl (l,t,h))).val = (l.val*s+t.val)*d+h.val := by
  change h.val + d*t.val + s*d*l.val = _
  ring

private lemma col2 {g s d a : ℕ} (l : Fin g) (t : Fin s) (h : Fin d) :
    (colOrder g s d a (.inr (.inl (l,t,h)))).val = g*(s*d)+(l.val*s+t.val)*d+h.val := by
  change g*(s*d)+(h.val+d*t.val+s*d*l.val) = _
  ring

private lemma col3 {g s d a : ℕ} (t : Fin s) (h : Fin a) :
    (colOrder g s d a (.inr (.inr (t,h)))).val = g*(s*d)+(g*(s*d)+t.val*a+h.val) := by
  change g*(s*d)+(g*(s*d)+(h.val+a*t.val)) = _
  ring

lemma fast_correct {g s d a : ℕ} [NeZero g] (data : Array ℕ) (b : ℕ → ℕ)
    (i j : Fin d) (k : Fin a) :
    rowProduct data (fun c => b (colOrder g s d a c).val) (i,j,k) = fastProduct g s d a data b i.val j.val k.val := by
  have h₁ (l : Fin g) (t : Fin s) (z : ℕ) :
      addMultiple (integerMatrix (g:=g) data (i,j,k) (.inl (l,t,i))) (b (colOrder g s d a (.inl (l,t,i))).val) z =
        addBit (productBit data ((l.val*g*s+t.val)*3) 1 j.val 2 k.val) (b ((l.val*s+t.val)*d+i.val)) z := by
    rw [col1]
    simp [integerMatrix,factorBit,productBit,add_bits]
  have h₂ (l : Fin g) (t : Fin s) (z : ℕ) :
      addMultiple (integerMatrix (g:=g) data (i,j,k) (.inr (.inl (l,t,j)))) (b (colOrder g s d a (.inr (.inl (l,t,j)))).val) z =
        addBit (productBit data ((l.val*s+t.val)*3) 0 i.val 2 k.val) (b (g*(s*d)+(l.val*s+t.val)*d+j.val)) z := by
    rw [col2]
    simp [integerMatrix,factorBit,productBit,add_bits]
  have h₃ (t : Fin s) (z : ℕ) :
      addMultiple (integerMatrix (g:=g) data (i,j,k) (.inr (.inr (t,k)))) (b (colOrder g s d a (.inr (.inr (t,k)))).val) z =
        addBit (productBit data (t.val*3) 0 i.val 1 j.val) (b (g*(s*d)+(g*(s*d)+t.val*a+k.val))) z := by
    rw [col3]
    simp [integerMatrix,factorBit,productBit,add_bits]
  unfold rowProduct fastProduct
  have op₁ (l : Fin g) (t : Fin s) : addMultiple (integerMatrix (g:=g) data (i,j,k) (.inl (l,t,i))) (b (colOrder g s d a (.inl (l,t,i))).val) =
      addBit (productBit data ((l.val*g*s+t.val)*3) 1 j.val 2 k.val) (b ((l.val*s+t.val)*d+i.val)) := funext (h₁ l t)
  have op₂ (l : Fin g) (t : Fin s) : addMultiple (integerMatrix (g:=g) data (i,j,k) (.inr (.inl (l,t,j)))) (b (colOrder g s d a (.inr (.inl (l,t,j)))).val) =
      addBit (productBit data ((l.val*s+t.val)*3) 0 i.val 2 k.val) (b (g*(s*d)+(l.val*s+t.val)*d+j.val)) := funext (h₂ l t)
  have op₃ (t : Fin s) : addMultiple (integerMatrix (g:=g) data (i,j,k) (.inr (.inr (t,k)))) (b (colOrder g s d a (.inr (.inr (t,k)))).val) =
      addBit (productBit data (t.val*3) 0 i.val 1 j.val) (b (g*(s*d)+(g*(s*d)+t.val*a+k.val))) := funext (h₃ t)
  simp only [op₁,op₂,op₃,← fold_index]

lemma from_bits {g s d a : ℕ} [NeZero g] (data : Array ℕ) (b : ℕ → ℕ)
    (h : ∀ i : Fin (d*(d*a)), let p := (rowOrder d a).symm i
      fit (fastProduct g s d a data b p.1.val p.2.1.val p.2.2.val) i.val = true) :
    CriticalTensor.Spans a (g*d) (g*d) (g*(g*s)) := by
  apply from_rows data (fun c => b (colOrder g s d a c).val)
  intro i
  have he := fast_correct (g:=g) (s:=s) (a:=a) data b ((rowOrder d a).symm i).1 ((rowOrder d a).symm i).2.1 ((rowOrder d a).symm i).2.2
  exact (congrArg (fun w => fit w i.val) he).trans (h i)

end CriticalTensor.SixBase

namespace CriticalTensor.SixBase

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

end CriticalTensor.SixBase

namespace CriticalTensor.SixBase.Six

private def factors : Array ℕ := #[0x1, 0x1, 0x1, 0x2, 0x2, 0x2, 0x4, 0x4, 0x4, 0x8, 0x8, 0x8, 0x10, 0x10, 0x10, 0x20, 0x20, 0x20, 0x38, 0x15, 0x35, 0x2f, 0x39, 0x3d, 0x3c, 0x3, 0x2c, 0x5, 0x2b, 0x31, 0x33, 0x17, 0x1a, 0x3a, 0x33, 0x7, 0x15, 0x1f, 0x1, 0x1d, 0xe, 0x17]
private def unpack := unpack16 14

private def t0 : Array ℕ := #[
  unpack 0x52c477a02c7c0403e1019cc00b84221c1,
  unpack 0x28403b04073404031f08c,
  (0xe4ca7403009c0963004011140002480031 <<< 72),
  (0x35c17481809480000a5011141 <<< 108),
  0,
  (0x445361b <<< 180),
  unpack 0x528876002fe9500a6ebb,
  unpack 0x10a11ddf77f6c098381287195801c7b4,
  unpack 0x14b11d8203ad2937d0,
  unpack 0x1540febeda94c1c096380,
  (0xe9248104011007 <<< 151),
  (0x1e124b <<< 187),
  unpack 0x40847d5cdfdb014a79,
  unpack 0x4211f9d9a04420538,
  unpack 0x2a25c820b9bf6dad2bb660,
  unpack 0x1fac6da9481cd00380]

private def t1 : Array ℕ := #[
  unpack 0x407c0fcdf200,
  (0x2045 <<< 194),
  unpack 0x3e9904177a0ada2aa,
  unpack 0x3200f6082e02e58,
  unpack 0x38223b001737d29fd60,
  0,
  unpack 0x21227b8b5400,
  (0x33 <<< 201),
  unpack 0x2678db4185fadc6,
  unpack 0x508076080e68010,
  unpack 0x8419fced680861c0,
  unpack 0x3402fb8b37ed8580700,
  (0xd09200839 <<< 172),
  (0x1 <<< 208),
  unpack 0x18311dc5bd065634,
  unpack 0x10c8fd429d9d0]

private def t2 : Array ℕ := #[
  unpack 0xa400fc2cdf4b40,
  unpack 0x19447ea6bd00,
  (0x1c922801 <<< 179),
  (0x1 <<< 215),
  unpack 0x10603f2e6fed80a52,
  unpack 0x150fb5bbe832a8,
  unpack 0x2a1b8b37ed94ac0,
  0,
  unpack 0x3842382b9600,
  (0x39 <<< 202),
  unpack 0x89e0fbbf4022,
  unpack 0x228103cd02d94,
  unpack 0xca03d0207c0447f4a40,
  0,
  (0xc01 <<< 196),
  0]

private def t3 : Array ℕ := #[
  unpack 0x72c87e77e6fd0542a1,
  unpack 0xf37a800c20f2cc,
  unpack 0x3a4476040feec53c2ed0,
  unpack 0x1044bf338088eb5c580,
  unpack 0xc217f59fbb2204e00,
  0,
  0,
  unpack 0x4211f9d9a05330c,
  unpack 0xcb11f9d9a29400ce0,
  unpack 0x4480e3100,
  (0x7248a0008005141 <<< 149),
  (0x248241 <<< 184),
  0,
  unpack 0x4599ee2de82cd8,
  unpack 0xa77cecd14f20,
  (0x6a49 <<< 193)]

private def t4 : Array ℕ := #[
  unpack 0x2925deea00,
  (0x3 <<< 204),
  0,
  (0x1 <<< 142),
  (0x201 <<< 97),
  0,
  unpack 0x79b2802e00,
  (0x10c5005 <<< 181),
  unpack 0x12ccf75007381a070108f910d40e2500e,
  unpack 0xd19afcc00e70015478,
  (0x2402d000b02000d <<< 150),
  unpack 0x1d7438a40f77edf2300,
  0,
  (0x357 <<< 198),
  (0x5 <<< 205),
  unpack 0x79bd406420c38]

private def t5 : Array ℕ := #[
  unpack 0x14201c0b360,
  unpack 0x1a6f52d00,
  unpack 0x667bd0b00e00,
  (0x81117 <<< 188),
  0,
  unpack 0x614aee803e0053dac888a70421e9009f909403d33,
  unpack 0x1812b9a41fc096e3681d2843e430423e04a03f1,
  unpack 0x16925d020bc04e700847d3003b230d40e2554e,
  0,
  unpack 0x299995881f2,
  unpack 0x304076002eebadca32bb56eac,
  0,
  unpack 0x304076002ee6c000e1c00eb8,
  unpack 0x333d8203fa54026038,
  unpack 0xc101d800bbaeb728caf80038,
  unpack 0x8423f3b3adca001c70]

private def t6 : Array ℕ := #[
  unpack 0x4221c5f77e892077168045faddd30,
  unpack 0x3a3e7dfb62481dc5f0b480be0,
  0,
  unpack 0xc911f9d9a29fc60,
  unpack 0xd3be80859c0,
  (0x3 <<< 104),
  unpack 0x14111f81b9b8208f6b8bf40,
  unpack 0xb13f5dbdb5d580,
  unpack 0x194078ae6e4db6d80,
  unpack 0x18021f41fbbf4500,
  unpack 0xc04fb001ff3726dd00,
  unpack 0xcb31c13500,
  unpack 0x1aefb5f9b0230e00,
  unpack 0x8019e4105dcdd200,
  unpack 0x20647ea20c00,
  (0x10465000a03 <<< 166)]

private def t7 : Array ℕ := #[
  0,
  unpack 0xe6f89800,
  (0x508821 <<< 185),
  (0x10a21 <<< 191),
  (0x201 <<< 197),
  (0x1 <<< 203),
  (0x1 <<< 209),
  0,
  unpack 0x3506fe8bf77e8d00700,
  unpack 0x2d02bf6b8088ecb6c80,
  unpack 0x308ae0107decb880,
  unpack 0x113f54400,
  0,
  unpack 0x224874081e2a00700,
  0,
  0]

private def t8 : Array ℕ := #[
  (0x30801 <<< 189),
  0,
  unpack 0x508076080e68050,
  unpack 0x30267ea14ec0,
  unpack 0x3581e8181cd148a0,
  (0x2424081 <<< 182),
  unpack 0xb592e1a80,
  (0x1 <<< 95),
  unpack 0x4508fc2cdf4340,
  unpack 0x32c47e7668940,
  unpack 0x38063e83717694acc9ee30,
  unpack 0x310438041f800ae0542a9,
  unpack 0x6088fc0c022bfdb014a06,
  unpack 0x19047883f17e83232,
  unpack 0x8233dc1f8bb406a,
  unpack 0x8211f9dfbbf4a7665624]

private def t9 : Array ℕ := #[
  unpack 0xf5020bba00214774,
  (0x1 <<< 207),
  (0x14322c10401 <<< 167),
  (0x1 <<< 200),
  unpack 0xa108e2b9b00be8,
  unpack 0xa76540fa,
  unpack 0x70ccf6080f0111fde43348,
  unpack 0x21067b04075a1481d9180,
  unpack 0x14211d8203b9bf4110,
  unpack 0x10123f9df9b03308,
  unpack 0xc091fafbbf790c2fb18,
  unpack 0xfe7cefcdb953b2130,
  (0xa599400180160223 <<< 144),
  (0x18328d002025a0d012940005000092011 <<< 78),
  (0x40d3540000949 <<< 156),
  (0x3c20d020c007a2d012840440000013 <<< 90)]

private def t10 : Array ℕ := #[
  unpack 0x1083803dc2d0380847c0,
  unpack 0xa107f9de00a70ecc0,
  unpack 0xe090eefbb14da0,
  unpack 0xa589fcc044702a14,
  0,
  (0x4822c1 <<< 183),
  unpack 0x38423f3b5a00,
  unpack 0x2108fcec29d804,
  0,
  unpack 0x663f3eeed554daa2e10a3bb26c5,
  unpack 0x524cfd76b4a6d5161691c13,
  unpack 0x18133d820bba04214776d181847,
  unpack 0x1a6f9d9a15080ce6085c10a3bb48d1,
  unpack 0x10833d820bba2959933022e169184907,
  unpack 0xb183fcee0073da9481d918ca210fa4,
  0]

private def t11 : Array ℕ := #[
  unpack 0x38047ebb5a9481d918cd23c4,
  unpack 0x6501faba006147d4,
  unpack 0x128476002e6fa0c821c7e4,
  unpack 0x2408faedcdfa0cdabf4,
  (0x4c27403c09e1b404a1011000420081 <<< 84),
  unpack 0x333d82039a294820e0,
  0,
  unpack 0x4ac5f6002e6fad69e760,
  unpack 0x1c123d82039a154900e0,
  unpack 0x2544bb8b7ad695ca0,
  unpack 0xd3638a4178084ec97c80,
  unpack 0xc519fafb6dbe80,
  unpack 0x8488e0a1b58300,
  0,
  unpack 0xe000e8103d10c02700,
  unpack 0xa511fa0d161b00]

private def t12 : Array ℕ := #[
  (0x90491400c1 <<< 168),
  unpack 0x8423f3b9400,
  unpack 0x10233dda400,
  (0x6114c0051 <<< 171),
  0,
  (0x108420409 <<< 173),
  (0x1 <<< 210),
  (0x1 <<< 211),
  (0x1 <<< 212),
  (0x1 <<< 213),
  (0x1 <<< 214),
  0,
  (0x35321d <<< 186),
  unpack 0x2807d8203b9bfb76ae5d40,
  unpack 0x18a31d800fbb6f3300,
  unpack 0x7f3d7d8208e00]

private def t13 : Array ℕ := #[
  unpack 0x14a21c020fbdb96080,
  unpack 0x2418e4107decae80,
  (0x3c06c8204005 <<< 162),
  unpack 0x69500,
  (0x1124003 <<< 175),
  (0xca224006001 <<< 163),
  unpack 0x28043e830190,
  unpack 0x2118e0800,
  unpack 0x126573483f0129ed64445380,
  unpack 0x4121dd8088f6aaa17d6e50,
  unpack 0x6410eec0447b44903b8be40,
  0,
  unpack 0x1c011c0b750,
  0,
  (0x2210003 <<< 174),
  unpack 0x4211f9d9a542a1a]

private def t14 : Array ℕ := #[
  unpack 0x70c8fe76efa00,
  unpack 0x5280f160223fa0a857cb,
  0,
  unpack 0x6188ec005de8016d,
  unpack 0x2526bf3b8014e04435038,
  unpack 0x52c474082ee8150,
  (0x19021 <<< 190),
  unpack 0x42847e5df4168,
  0,
  unpack 0x6400fcbbe8323a,
  unpack 0xd19afcc00e7023c8,
  unpack 0x708477a4820f280,
  0,
  (0x52cc2041 <<< 177),
  (0x4191 <<< 192),
  (0x1c21 <<< 195)]

private def t15 : Array ℕ := #[
  0,
  unpack 0x1cb11cb550a2fd4a,
  (0xcb <<< 199),
  unpack 0x38263bb0111c0fb6b7d,
  (0x20cca0418041 <<< 161),
  unpack 0x720476001ee2fd064716,
  unpack 0x7192ee2cdfb69421f2180,
  unpack 0x10647eab5502fa975,
  0,
  unpack 0x14a03c58088fe83d5a,
  0,
  (0x3 <<< 206)]

private def tables := #[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15]
private def multiplier (j : ℕ) : ℕ :=
  ((tables[j/16]?.getD #[])[j%16]?).getD 0

private def checkAt (i : ℕ) : Bool :=
  let p := (rowOrder 6 6).symm (Fin.ofNat 216 i)
  fit (fastProduct 1 14 6 6 factors multiplier p.1.val p.2.1.val p.2.2.val) i

private def r8 : RowWindow checkAt 8 := nextWindow (start checkAt) 8 (by decide +kernel)
private def r16 : RowWindow checkAt 16 := nextWindow r8 8 (by decide +kernel)
private def r24 : RowWindow checkAt 24 := nextWindow r16 8 (by decide +kernel)
private def r32 : RowWindow checkAt 32 := nextWindow r24 8 (by decide +kernel)
private def r40 : RowWindow checkAt 40 := nextWindow r32 8 (by decide +kernel)
private def r48 : RowWindow checkAt 48 := nextWindow r40 8 (by decide +kernel)
private def r56 : RowWindow checkAt 56 := nextWindow r48 8 (by decide +kernel)
private def r64 : RowWindow checkAt 64 := nextWindow r56 8 (by decide +kernel)
private def r72 : RowWindow checkAt 72 := nextWindow r64 8 (by decide +kernel)
private def r80 : RowWindow checkAt 80 := nextWindow r72 8 (by decide +kernel)
private def r88 : RowWindow checkAt 88 := nextWindow r80 8 (by decide +kernel)
private def r96 : RowWindow checkAt 96 := nextWindow r88 8 (by decide +kernel)
private def r104 : RowWindow checkAt 104 := nextWindow r96 8 (by decide +kernel)
private def r112 : RowWindow checkAt 112 := nextWindow r104 8 (by decide +kernel)
private def r120 : RowWindow checkAt 120 := nextWindow r112 8 (by decide +kernel)
private def r128 : RowWindow checkAt 128 := nextWindow r120 8 (by decide +kernel)
private def r136 : RowWindow checkAt 136 := nextWindow r128 8 (by decide +kernel)
private def r144 : RowWindow checkAt 144 := nextWindow r136 8 (by decide +kernel)
private def r152 : RowWindow checkAt 152 := nextWindow r144 8 (by decide +kernel)
private def r160 : RowWindow checkAt 160 := nextWindow r152 8 (by decide +kernel)
private def r168 : RowWindow checkAt 168 := nextWindow r160 8 (by decide +kernel)
private def r176 : RowWindow checkAt 176 := nextWindow r168 8 (by decide +kernel)
private def r184 : RowWindow checkAt 184 := nextWindow r176 8 (by decide +kernel)
private def r192 : RowWindow checkAt 192 := nextWindow r184 8 (by decide +kernel)
private def r200 : RowWindow checkAt 200 := nextWindow r192 8 (by decide +kernel)
private def r208 : RowWindow checkAt 208 := nextWindow r200 8 (by decide +kernel)
private def r216 : RowWindow checkAt 216 := nextWindow r208 8 (by decide +kernel)

theorem spans : CriticalTensor.Spans 6 6 6 14 := by
  apply from_bits (g:=1) (s:=14) (d:=6) (a:=6) factors multiplier
  intro i
  have ok := r216.verified i.val i.isLt
  have hi : Fin.ofNat 216 i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simpa only [checkAt,hi] using ok

end CriticalTensor.SixBase.Six

namespace CriticalTensor.SixBase

theorem base_six : CriticalTensor.Spans 6 6 6 14 := Six.spans

end CriticalTensor.SixBase

namespace CriticalTensor.SixBase.Seven

private def factors : Array ℕ := #[0x1, 0x1, 0x1, 0x2, 0x2, 0x2, 0x4, 0x4, 0x4, 0x8, 0x8, 0x8, 0x10, 0x10, 0x10, 0x20, 0x20, 0x20, 0x40, 0x40, 0x13, 0x29, 0x77, 0x7, 0x6c, 0x15, 0xc, 0x40, 0x65, 0x1a, 0x1, 0x18, 0x34, 0x17, 0x28, 0xe, 0x47, 0x62, 0x1d, 0x33, 0x29, 0x3d, 0x25, 0x23, 0x26, 0x37, 0x55, 0x24, 0x15, 0xc, 0x38]
private def unpack := unpack16 19

private def t0 : Array ℕ := #[
  unpack 0x325bb3a967001fdf9660c8907f630e54f0099c880fed5b2281,
  unpack 0x28207311e0017f667462619a4,
  unpack 0x5200e94d043e8017f6618cf14410e0,
  unpack 0xbb10a9ff980,
  unpack 0x12ef5983407b47ecfd998b8400,
  unpack 0x32607d672ea3d844e000,
  (0x40001811b <<< 252),
  unpack 0x1607d6752d19c02f0efc1970cfe412a9ed3b,
  0,
  unpack 0x1dd674ec5043c60078180fe0cbb03f3ee2fb60,
  unpack 0x18300b0700,
  unpack 0x12c0eecdd460070005ff400,
  unpack 0x19803eb3a96f96000,
  (0xec0041d <<< 259),
  unpack 0x1ccdd98f003e80079572413c8867a4407b71d4975eec800fff3,
  unpack 0xec01c3400fe80034038]

private def t1 : Array ℕ := #[
  0,
  unpack 0x39d674ec101baa036ef100,
  unpack 0x21207766edd3d002e04c1e4303800,
  unpack 0xa501dd9ba302fc000,
  (0x108009 <<< 266),
  unpack 0x10c0eecd68ff9c15079209fb2ed020d49850a20e,
  unpack 0x5280faeea5dbe2e0b03983d9600803fe8,
  unpack 0x2102fd77288a871c00e0701c0aa791207b7e98a1c01c0,
  unpack 0x40bf5dcbb1940e0dd3600,
  (0x3360102003401800680040501 <<< 189),
  (0x8a40800c0073 <<< 231),
  (0x3 <<< 273),
  unpack 0x1607d76ea374fe5fa76dc750049740427dc6,
  unpack 0x1cef59d3bca7e802590,
  unpack 0x292077674ecf0438e2076280e679f44180,
  (0x3 <<< 154)]

private def t2 : Array ℕ := #[
  0,
  unpack 0x1b4dd9d4be4000,
  (0x25 <<< 280),
  unpack 0x3600facc6021ff9c0607440247f34e1b0003f550111c,
  unpack 0x4a0381a03edbf170501c0067ecb03750,
  unpack 0xeebba963021e010bf0207f4680f9a71d80,
  (0x1 <<< 161),
  (0xa10041000c00700100051 <<< 203),
  0,
  (0x1 <<< 287),
  unpack 0x5040eecdd3400f8005f01039cdbd94680541c,
  unpack 0x33407d772eba001f998020f90,
  unpack 0x9103a5debfcf999d32180,
  (0x15 <<< 162),
  unpack 0x4981cda7fcf1000,
  unpack 0x12ccc8000]

private def t3 : Array ℕ := #[
  0,
  unpack 0x73bd772e53b17eccc8c00,
  (0x5 <<< 279),
  unpack 0x9903bb37464e9880,
  unpack 0xed01c75b017cb00,
  unpack 0x19903ebb75c8c5800,
  0,
  (0x40c020d <<< 260),
  unpack 0x9207d67496007cc40fc401cd5a0a4cb7d,
  unpack 0x14b03bb35b9801f88038053b8c,
  unpack 0x2481f59d36e6307e200e6ad3d8760,
  unpack 0x19a03bb384a043ce08764c6d2203c1a6f00,
  unpack 0xc981dd9ca2821e7103f1207317b6c00,
  0,
  0,
  unpack 0x1b607d672ef69a8017f660074]

private def t4 : Array ℕ := #[
  unpack 0x1d8039b8c000,
  unpack 0x14a03bb39769e0bf667400,
  unpack 0x74900,
  unpack 0x143039af0b18bd400,
  unpack 0x39d6728000,
  0,
  unpack 0x325eb30680e5021e300bf1407341b776e3b6c85884a743b2480e,
  unpack 0xe901cdc6004a830,
  unpack 0x2640eece9d8e0879c00ec501cd67adfa280,
  (0x109 <<< 152),
  unpack 0xa401f5dd4bc71981907000,
  (0x64002080028021 <<< 232),
  (0x41 <<< 275),
  unpack 0x2480facc1a038c087e51811dd1f63a70d8954eca,
  unpack 0x9a03bb30680e88b2c604fd960107c8,
  unpack 0x2440e97748c410bcb1803c8823f3f4d6ec0]

private def t5 : Array ℕ := #[
  (0x41 <<< 157),
  0,
  unpack 0xa401dd9cb4ac000,
  (0x14b3 <<< 274),
  0,
  unpack 0x1260776672c8020e10,
  unpack 0x8181f5d9d8c0720,
  unpack 0x52c0eecc00a100,
  (0x29 <<< 174),
  unpack 0xc901f59ba5900e000,
  0,
  unpack 0xa101ce92087ec7f2cc191487ec74e1b0003fb5614,
  unpack 0xc96a767001c000,
  unpack 0x3a407d674ece043b0bf4e8c80,
  unpack 0xba00,
  unpack 0x3b1ebba76d8a000]

private def t6 : Array ℕ := #[
  0,
  0,
  unpack 0x19803bb30680ec40afeccd0051e04e229,
  unpack 0x33407d7728a0875c02e0681cc19700705368,
  unpack 0xe801f5d834074a057f666b237a7a0,
  (0x20d <<< 134),
  unpack 0x6b3a7794d70038c1800,
  0,
  (0x1001 <<< 269),
  unpack 0xa766021d4103b040718302178a1d8a,
  unpack 0x3a0077674ee3002dd4,
  unpack 0x966a964821d010bf04073a6e34a0,
  unpack 0xc9fc85a4700,
  unpack 0xec81f59d4b3400f8cc3000,
  (0x7640208005 <<< 248),
  0]

private def t7 : Array ℕ := #[
  unpack 0x13207034071810fa085e0c83c84475a0a4ceda,
  unpack 0x1d2f59d3bca7e802a58,
  unpack 0x2576752c6043862179660071c0323f5b30ba40,
  unpack 0x177900,
  unpack 0x13407d672ed39042e0641ff1800,
  (0x1a00901 <<< 226),
  (0x2001 <<< 268),
  0,
  unpack 0x6400faee5ca6a005fd0068741887c5d4c19,
  unpack 0x6d01f59cbb3400e2fa88068f438872591931,
  unpack 0xda7ace91c10ef960033c8867a0607a44033b2000fed5e2292,
  unpack 0x9903bb394d003f0bf401a3d98b10e6ea25942,
  unpack 0x2680faeea5da316599832241fcc3887348809ed5e22f2,
  unpack 0x7440eecdd6239b4188794320161c,
  unpack 0x9203eb3a9788c0681c1981c14dd3b4,
  unpack 0x9903bb30680e8c42f0781c12e00e0a6c58]

private def t8 : Array ℕ := #[
  unpack 0x31debba976ae017f9600e8,
  unpack 0x7400eecc3021d700bfbe0c8867f2020fb58,
  unpack 0x5280eece5d8e007dc02ff2c029b0,
  unpack 0x34c0eecddc468085fe1f832e19fc854b0,
  unpack 0x6d01f59cbb1410ea085f82038020fd0,
  unpack 0x3600faeea19a0078c72fecc86f9dfdb3040e03c0e0,
  unpack 0x12cd2ef29e0bf401a1dee2b000e0,
  unpack 0x3a5eb3986302de314bf0d0790a1e4591f9dc6007dc74009c0,
  unpack 0x5045faee51d40f9881c0d83c85cf2208fceed1042fb0c0,
  unpack 0xec01f59c25821e30c3b2637ceed3002ffcc0,
  unpack 0x3440e0680f74c5e280f0013c8b07f3f4d5180,
  unpack 0x12cd2ef29e0bf40b00380,
  unpack 0x28407d670ecb043ce187640093f9dc1a5700,
  unpack 0x3a207766eb10143b00,
  unpack 0x18ed50ca05bce087640093d2203f000700,
  0]

private def t9 : Array ℕ := #[
  unpack 0xa101f59c3b2c10f3861d931b4a00e00,
  unpack 0xe881dd9bac47a00,
  unpack 0x1d103bb37588eac00,
  unpack 0xd803a51c10ea081d9317b8c00,
  unpack 0x7480ea7794ff18c9800,
  unpack 0x40c0e180874042fc701e61800,
  (0x10a0082000800d041410b8203 <<< 190),
  unpack 0x6d81dd983407ca7881987000,
  unpack 0x6480faee51410fe2e9000,
  unpack 0x197660d01f19001e000,
  (0xcd0040800b00402189 <<< 215),
  unpack 0x9769774ea000,
  (0x6c0001800600601 <<< 227),
  unpack 0x1302f3a2c01c000,
  (0x490040800301 <<< 239),
  unpack 0x162fd66a8000]

private def t10 : Array ℕ := #[
  unpack 0xe881d68000,
  (0x10400060d <<< 253),
  (0x300025 <<< 258),
  (0x608039 <<< 264),
  (0x14b01 <<< 270),
  (0x261 <<< 276),
  0,
  0,
  unpack 0xe75db5327068944fe80,
  0,
  unpack 0x39d76d4c9c1a900,
  unpack 0x7640eecdd620044f10c0e00,
  unpack 0x1cebb6a64e0d9b4dd40,
  unpack 0xe200,
  unpack 0x646f43494,
  unpack 0xa481ced2a8b4f40]

private def t11 : Array ℕ := #[
  unpack 0x10b03ebb75880ed60,
  unpack 0x2481f59d242c000,
  (0x81482000a0065 <<< 230),
  unpack 0x292073b4aa000,
  unpack 0x10b03ebb75886f3f4d9580,
  unpack 0x10b03ebb7588e9680,
  (0x200c804081 <<< 255),
  (0x160007 <<< 261),
  (0x822201d <<< 265),
  (0x19 <<< 271),
  (0x137 <<< 277),
  (0x201 <<< 283),
  0,
  unpack 0x3aecea5ea2085f8a03c004f2250f8eee9b1b4096f0c20e8182e286107,
  unpack 0xe881dd9bac40409c4543,
  unpack 0x1d9bb3a97688217e3c0e0551cc1dbe842c4093a1b06]

private def t12 : Array ℕ := #[
  unpack 0xb03bb3a699c42ec741c42a7914cf5080f1801cdd4818c597408172c00e,
  0,
  unpack 0x40c0e772df0b94c19148fec74e1b1396c0107c,
  unpack 0x3297794f05fa0089ef65193c40781c,
  unpack 0x18ef5dae9e6207e200e0148,
  unpack 0x3a40753bca7f8c6800,
  unpack 0x9303a9b73003f1007000,
  unpack 0x4817a92810ffce58809fb2c00,
  unpack 0x4303eb374b003a6007e200e0150,
  (0xec0a01800d000821800501811 <<< 187),
  unpack 0x5280e9766801fb1f33000,
  unpack 0x1d003eb30680f6b2000,
  unpack 0x39d66e8000,
  (0x1d <<< 282),
  unpack 0x52c0e63c2d4800,
  unpack 0x3a00729f401d0]

private def t13 : Array ℕ := #[
  unpack 0x4aecd88aa4601060,
  unpack 0x4b37672ee9c79000,
  unpack 0x1d203a5a4000,
  unpack 0x6640faedd72000,
  unpack 0xd803ebb7769fa000,
  unpack 0x1da038328800,
  unpack 0xd803ebb775003930,
  0,
  (0x1 <<< 281),
  unpack 0x5200e1c0078808f30e002797647e776e2f560,
  unpack 0x5200facc9808e000,
  unpack 0x7640eecdb8f05b2a800,
  unpack 0x10a03bb3a761821f05fbeacd7ab40,
  unpack 0x6c81f5dca7801f700bfcb1aefdbc76d920,
  unpack 0x3aece5d8e007d80aff0c1923f9a70d80,
  unpack 0x1d003bb37515040ec101ce9280]

private def t14 : Array ℕ := #[
  unpack 0xd103ebb94d043ae00763c0f0013cb8038290,
  unpack 0x7480facccc00e000,
  0,
  unpack 0x1b22fd772ef71f8b60c0fe8c04a8b0,
  unpack 0x1b407d674ef5002510,
  unpack 0x8bdd9ca7021f700bf0a07f4774c00,
  unpack 0x1d003eb3a77a800a0,
  unpack 0x4d81dd9d22821f16419420,
  unpack 0x9607d774e53d000e000,
  unpack 0x33607d774ecd003b0b564803800,
  0,
  unpack 0x9303a9da6c8d5a00,
  unpack 0x19203eb3a9788c000,
  unpack 0x194bbca782fd000,
  0,
  unpack 0xecf59d23801d410bca60c8a43bb0289ff1a0093ab4bbed0b]

private def t15 : Array ℕ := #[
  unpack 0x39debb7515040e383b62513fb341b5274fb6c4127,
  unpack 0xda7acea59c0071042f29832290eb001e91048e0107f64e97176c1047,
  unpack 0x26c0faee9d9e007678203fa0183f9ddb8a00abd2c100e286187,
  0,
  unpack 0x190041c208,
  0,
  unpack 0x4d01dd983407445986097007010750ec98,
  unpack 0x7600ea7794ff1b268041c268,
  unpack 0x1cef59d3bca7eb200003fc8688,
  unpack 0xec81dd9cb48f400b81a073065c01c0da6d58,
  unpack 0x4303ebb769fe644122083c0,
  unpack 0x1d003bb397298be80147bb1801f1140,
  0,
  unpack 0x14ec858e1078160f2161d8df26170811c0,
  unpack 0x1db0381a03960070c42ec541e4863b3d6fd61748c0,
  unpack 0x10c0faee9d9c0075c40fc541e4863bb6eed1042f4ac0]

private def t16 : Array ℕ := #[
  unpack 0x7640eecdd6239b1041e00,
  unpack 0x7640eecdd6238330c2e00,
  unpack 0x1d117eb3946503e23833944e00,
  0,
  (0x1091 <<< 148),
  (0x849 <<< 149),
  unpack 0x8607d76ed3fcc1000,
  unpack 0x6c81f59ca3801e700bc1017000,
  (0x80082001a00f0424000019 <<< 194),
  unpack 0x66c0ea967821f4003b1b000,
  0,
  0,
  unpack 0x33407d6608000,
  unpack 0xe67aec0a0b8000,
  unpack 0x1481781a138000,
  unpack 0x14a039cd8000]

private def t17 : Array ℕ := #[
  (0x34c02040069 <<< 244),
  0,
  (0x1 <<< 288),
  (0x9 <<< 289),
  (0x1 <<< 290),
  (0x3 <<< 291),
  0,
  (0x1 <<< 293),
  unpack 0x9103bb33ad84188700,
  unpack 0x3b4071d6c3400,
  unpack 0xcd01f59ba5800e000,
  (0xc88041 <<< 263),
  unpack 0x2960776600400,
  (0x1 <<< 143),
  unpack 0x9607d66d4c9d31c40,
  unpack 0xe75db532736efdb00]

private def t18 : Array ℕ := #[
  unpack 0xc981d0860878c30e000,
  0,
  (0x14b0003 <<< 262),
  unpack 0x191f9ddba80,
  (0x8d007 <<< 267),
  (0x10240000d1 <<< 256),
  (0x1008241 <<< 254),
  (0x81 <<< 285),
  (0x1 <<< 292),
  unpack 0x12e8b0000,
  0,
  unpack 0x18cf59cbbca7c2fd0068f767ee1bb4954936,
  unpack 0x766ece5d9a0075002fe80347b3f6cdd4e4c2a90e,
  0,
  unpack 0x52c0facc1a03edb616c101fd0b485e0b40827766,
  0]

private def t19 : Array ℕ := #[
  unpack 0x6d01dd9d25021d9f691ba313188,
  unpack 0x9917bb3a767021e7103cb0811c0367f200,
  0,
  unpack 0x690bd4ec7003f8b8280e0033f6582d0,
  unpack 0x2481dd9d36e0217669180955c4c,
  (0x2405 <<< 272),
  0,
  unpack 0x1b607d664799fbb000,
  (0x1 <<< 286),
  0,
  unpack 0x1d2f59d3bca7e802710,
  unpack 0x975dbb8801a0,
  unpack 0x3b3766ea28085fd99d18980,
  unpack 0x66c0eecea5dacfcb3064581c00,
  unpack 0x73ace9d856080fe800,
  (0x9b <<< 278)]

private def t20 : Array ℕ := #[
  unpack 0x4a03ebba696400e4,
  unpack 0x7337672ecb0038ac101fd00f4,
  unpack 0x134071d8d93a62ea60,
  unpack 0x10a03aa59410bfc3f065c21f90c567a,
  0,
  unpack 0x4881dd9ba0d0025,
  (0x5 <<< 284),
  unpack 0x10903ebb969c17eccd646f4342d,
  unpack 0x73bd76eed3f400c8,
  unpack 0x8181f5dcbb8e400bf6b000,
  unpack 0x3480faeddd4000,
  0,
  (0x1d80003001 <<< 250),
  0,
  unpack 0x8607d76eb92209640,
  unpack 0x14a0381a03e5b5c00ff2d500d9ea40eb5]

private def t21 : Array ℕ := #[
  unpack 0x4303bb36a35042f0ae4227916474880f1801f1d4975eea,
  unpack 0x19a03ebb5a36160681e5d800,
  unpack 0xc67aee52410f8cf8203aa6bd085e284,
  0]

private def tables := #[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21]
private def multiplier (j : ℕ) : ℕ :=
  ((tables[j/16]?.getD #[])[j%16]?).getD 0

private def checkAt (i : ℕ) : Bool :=
  let p := (rowOrder 7 6).symm (Fin.ofNat 294 i)
  fit (fastProduct 1 17 7 6 factors multiplier p.1.val p.2.1.val p.2.2.val) i

private def r8 : RowWindow checkAt 8 := nextWindow (start checkAt) 8 (by decide +kernel)
private def r16 : RowWindow checkAt 16 := nextWindow r8 8 (by decide +kernel)
private def r24 : RowWindow checkAt 24 := nextWindow r16 8 (by decide +kernel)
private def r32 : RowWindow checkAt 32 := nextWindow r24 8 (by decide +kernel)
private def r40 : RowWindow checkAt 40 := nextWindow r32 8 (by decide +kernel)
private def r48 : RowWindow checkAt 48 := nextWindow r40 8 (by decide +kernel)
private def r56 : RowWindow checkAt 56 := nextWindow r48 8 (by decide +kernel)
private def r64 : RowWindow checkAt 64 := nextWindow r56 8 (by decide +kernel)
private def r72 : RowWindow checkAt 72 := nextWindow r64 8 (by decide +kernel)
private def r80 : RowWindow checkAt 80 := nextWindow r72 8 (by decide +kernel)
private def r88 : RowWindow checkAt 88 := nextWindow r80 8 (by decide +kernel)
private def r96 : RowWindow checkAt 96 := nextWindow r88 8 (by decide +kernel)
private def r104 : RowWindow checkAt 104 := nextWindow r96 8 (by decide +kernel)
private def r112 : RowWindow checkAt 112 := nextWindow r104 8 (by decide +kernel)
private def r120 : RowWindow checkAt 120 := nextWindow r112 8 (by decide +kernel)
private def r128 : RowWindow checkAt 128 := nextWindow r120 8 (by decide +kernel)
private def r136 : RowWindow checkAt 136 := nextWindow r128 8 (by decide +kernel)
private def r144 : RowWindow checkAt 144 := nextWindow r136 8 (by decide +kernel)
private def r152 : RowWindow checkAt 152 := nextWindow r144 8 (by decide +kernel)
private def r160 : RowWindow checkAt 160 := nextWindow r152 8 (by decide +kernel)
private def r168 : RowWindow checkAt 168 := nextWindow r160 8 (by decide +kernel)
private def r176 : RowWindow checkAt 176 := nextWindow r168 8 (by decide +kernel)
private def r184 : RowWindow checkAt 184 := nextWindow r176 8 (by decide +kernel)
private def r192 : RowWindow checkAt 192 := nextWindow r184 8 (by decide +kernel)
private def r200 : RowWindow checkAt 200 := nextWindow r192 8 (by decide +kernel)
private def r208 : RowWindow checkAt 208 := nextWindow r200 8 (by decide +kernel)
private def r216 : RowWindow checkAt 216 := nextWindow r208 8 (by decide +kernel)
private def r224 : RowWindow checkAt 224 := nextWindow r216 8 (by decide +kernel)
private def r232 : RowWindow checkAt 232 := nextWindow r224 8 (by decide +kernel)
private def r240 : RowWindow checkAt 240 := nextWindow r232 8 (by decide +kernel)
private def r248 : RowWindow checkAt 248 := nextWindow r240 8 (by decide +kernel)
private def r256 : RowWindow checkAt 256 := nextWindow r248 8 (by decide +kernel)
private def r264 : RowWindow checkAt 264 := nextWindow r256 8 (by decide +kernel)
private def r272 : RowWindow checkAt 272 := nextWindow r264 8 (by decide +kernel)
private def r280 : RowWindow checkAt 280 := nextWindow r272 8 (by decide +kernel)
private def r288 : RowWindow checkAt 288 := nextWindow r280 8 (by decide +kernel)
private def r294 : RowWindow checkAt 294 := nextWindow r288 6 (by decide +kernel)

theorem spans : CriticalTensor.Spans 6 7 7 17 := by
  apply from_bits (g:=1) (s:=17) (d:=7) (a:=6) factors multiplier
  intro i
  have ok := r294.verified i.val i.isLt
  have hi : Fin.ofNat 294 i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simpa only [checkAt,hi] using ok

end CriticalTensor.SixBase.Seven

namespace CriticalTensor.SixBase

theorem base_seven : CriticalTensor.Spans 6 7 7 17 := Seven.spans

end CriticalTensor.SixBase

namespace CriticalTensor.SixBase.Ten

private def factors : Array ℕ := #[0x3, 0x3, 0x20, 0x2, 0x3, 0x37, 0x1, 0x1, 0x34, 0x1, 0x3, 0xe, 0x1, 0x3, 0x5, 0x2, 0x1, 0x15, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x2, 0x2, 0x28, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x3, 0x2, 0x27, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x3, 0x2, 0x11, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]
private def unpack := unpack16 2

private def t0 : Array ℕ := #[
  0x20000,
  0,
  0x11f010,
  0x100000,
  0x11f600,
  0x200000,
  0x11f400,
  0x400000,
  0x930d40,
  0x1c0000,
  0x2f020,
  0x800000,
  0xa000,
  0x480000,
  0xf004,
  0x820800]

private def t1 : Array ℕ := #[
  0x8002,
  0x117480,
  0x14011,
  0x924900,
  0x10b000,
  0x8000,
  0x10c000,
  0x8008,
  0x110000,
  0]

private def tables := #[t0, t1]
private def multiplier (j : ℕ) : ℕ :=
  ((tables[j/16]?.getD #[])[j%16]?).getD 0

private def checkAt (i : ℕ) : Bool :=
  let p := (rowOrder 2 6).symm (Fin.ofNat 24 i)
  fit (fastProduct 5 1 2 6 factors multiplier p.1.val p.2.1.val p.2.2.val) i

private def r8 : RowWindow checkAt 8 := nextWindow (start checkAt) 8 (by decide +kernel)
private def r16 : RowWindow checkAt 16 := nextWindow r8 8 (by decide +kernel)
private def r24 : RowWindow checkAt 24 := nextWindow r16 8 (by decide +kernel)

theorem spans : CriticalTensor.Spans 6 10 10 25 := by
  apply from_bits (g:=5) (s:=1) (d:=2) (a:=6) factors multiplier
  intro i
  have ok := r24.verified i.val i.isLt
  have hi : Fin.ofNat 24 i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simpa only [checkAt,hi] using ok

end CriticalTensor.SixBase.Ten

namespace CriticalTensor.SixBase

theorem base_ten : CriticalTensor.Spans 6 10 10 25 := Ten.spans

end CriticalTensor.SixBase

namespace CriticalTensor.SixBase.Eleven

private def factors : Array ℕ := #[0x1, 0x1, 0x1, 0x2, 0x2, 0x2, 0x4, 0x4, 0x4, 0x8, 0x8, 0x8, 0x10, 0x10, 0x10, 0x20, 0x20, 0x20, 0x40, 0x40, 0x13, 0x80, 0x80, 0x31, 0x100, 0x100, 0x1a, 0x200, 0x200, 0x26, 0x400, 0x400, 0x22, 0x49b, 0x64a, 0x28, 0x1a, 0x4a6, 0x1b, 0x576, 0x414, 0x3b, 0x62b, 0x97, 0x23, 0x67a, 0x50c, 0x17, 0x1ae, 0x313, 0x34, 0x5b2, 0xce, 0x7, 0x1fe, 0x441, 0x33, 0x721, 0xd5, 0x3d, 0x71f, 0x7ae, 0x31, 0x370, 0x15, 0x9, 0x35, 0x393, 0x37, 0x5e6, 0x643, 0x2f, 0x758, 0x3d4, 0x6, 0x1ab, 0x245, 0x15, 0x51e, 0x7e8, 0x36, 0x1a8, 0x247, 0xa]
private def unpack := unpack16 46

private def t0 : Array ℕ := #[
  unpack 0x8c87ce05bca807703c108ec4c561c1fd4a411c0343c20852f8a01c620381943b0b2754008371da5a15f2c080fc400f,
  unpack 0x2a3f1016fc800770064f1e31d9628405ed28807507b0c6041e6198407018470000526a07a70,
  unpack 0x412970074f1221d001b802374605ec4c54c40e2305f6da8037ba4241c1107d0c03a06074a00103edc0c8700,
  unpack 0x51a471030fba21f8da934119e2d0075186fb0d401dd9c820e3c42fd2de10381c57e201c6c011782a07000,
  unpack 0x8605e7001fe18007740c7e8019f1156803a8c17e8663c7e0b09270071ffb6b501c0891c441382d0bf96e868070000,
  unpack 0x1ca83c509be40870042fc104e63383c6fcb862b80787e824e7160e01d6303805139822f0038e49a00700000,
  unpack 0x645de7065c6403a00574026e0a3bf198ab481d0f0bc26304e01e3c24838b043f2f491f71f8007000000,
  (0x3911cb11350400020031a2070411000016003060d84000002c9280144a0800c1d <<< 462),
  (0x15500044400400c4004c205004400004840d04708c1090d <<< 528),
  (0x3856810db74010018009d2844411080d <<< 594),
  (0xa60b3034001057d <<< 660),
  unpack 0x402bf3424fb221d0033b39c33f09828c81e871bf5b3125700d1ed001db8f2c03b82075430008001285407,
  unpack 0xc30fe50ede7003993260873b13106ac81dca07da3307e01c1d20938f28be40076a80e0659ea889c917aee1de03050031f81e2c4345f4b0,
  unpack 0x10405c015bac88714008fc300fc4195491bf433b3707c249c41e1f0403b46070188f2500e4a2c3e0c1035f6ed00,
  unpack 0x120ef1064f3801cc9a041fc314e495903f1c27b861205ecf092716687942303809578ab1ff06a011e4db8b760027953781f6b000,
  unpack 0x435ae18c9f444380077757d0c0b0a1ba48070966f0070f9201c0807fd7ac0e0508ea809c9458762013fd0000]

private def t1 : Array ℕ := #[
  unpack 0x1884798317dc00e800dd0097878af6260aa2071247fb6c069dc0383e002700787cb00e9501c060bcd58baa3001ae00000,
  unpack 0x10eb7ce1cbc60870003f8705e2089c11240e440bda0038c323abd241c2983e30038510790c8e000000,
  unpack 0x38c13a930007700a1f8e33d910794d8192719c0307b5d370260e0000000,
  (0x140b438c50800800800c59410208800042000c10298200d <<< 535),
  (0x40ab0e134208000520206404c0220b <<< 601),
  (0x14e0440a48a019 <<< 667),
  unpack 0x41fb0bd900fc2d0193c38c71044e20d4903d880f6100ee243e01a1f80938a08fa38073280e0000014079,
  unpack 0x332e72c24f8201c90086f0e11f1051103b021f4900e8003e0183e84138e2cf878072ac0e0308e00054513b00be0,
  unpack 0x3182b861375510e801dc018fa6047c665c00f2507c5389e01a3e158a2c3e10071a40ea860006e4bac44e00,
  unpack 0x2243e388df3003b95a3887641cb6e28bf6d94d0f80387c920ec1750dd980473e931c5d9be4551746000,
  unpack 0x1882bce153e4887e26818fd0477b130a2079145fd0de299c01c7b41070c18fc400ea101c0493c441392eee981c071240e0000,
  unpack 0x644ae6825d104392014bc08639220c3103e0a1f4900e73c7e0163c80938c18bf5b32c0e0109e6089cd1500e00000,
  unpack 0x5025f2c62fb221c5e56103bd89883e40907f6b002770091f4041c5943d38039d36fa400e000000,
  unpack 0x1c205c1093e800715c1c8315103f043fd56287c00c7d0d377000e0000000,
  (0x19178700b14000001000d38704000000d6801c3043547 <<< 542),
  (0xc2123452150040080004c518b315 <<< 608)]

private def t2 : Array ℕ := #[
  (0x19c00c05875b <<< 674),
  unpack 0xe6678c1e540398b00a7e0c3bd898abc81cc417f6b002370031ed001c5101c000000756,
  unpack 0xe618e184ded1f132068a3bf1106ac01cc513a480720447407c009c3981c000009760,
  unpack 0xc835c419be6087e16008fe2853882271068c81c8d1ff5b71617040000190e00e00,
  unpack 0x2851784197c800e48013f860de48bd6d0d1782487c0387f1308587e86032af3b580eb6000,
  unpack 0x214fe4849c74039a80c5f2417920a3207d1c2fd6ce211c00c7f00270e6076283625b61fd60000,
  unpack 0x8458e1025e4043f1b4042f1e23f198b8b943feb6830ee0063da013b6dd3881d17b21177a00000,
  unpack 0xfd63089e744398b4021f0023c9046803a0a1785a019df6c6881c909dc000000,
  (0x4abc10e19220801800069c1000080002a4812782c2000001868c0063d07 <<< 483),
  (0x1849839600020040043a18e882200018220310014d <<< 549),
  (0x18aa010288020001000c7003227 <<< 615),
  (0x128e000307 <<< 681),
  unpack 0x40ce2849d544393caf1c17e20e40f418bda003a87038078f8124e30a3f1801d0b03aa18004000dc6,
  unpack 0x1151b9a087b47c6f81c38e7c660ad207b041e9201d0211c01c3940270a597ba6e001d06c002061611fe60,
  unpack 0x1ca25d89c6087240307a70af1044e2a62076005fd6c6599c0383b4927026878d00ee581c0613c0002007c00,
  unpack 0x4de10e1f0043f1340a7e1629f10f0073105ec201ce707d98024e1023f30e5981557800464c000]

private def t3 : Array ℕ := #[
  unpack 0x10c17cc15be4807e3681c3f2c47994f4c1fec35040f4070832cfe18071a00e0055ee081fdc50a038b28c0000,
  unpack 0x30c70434e2821c85a0237cd1cf88b94fc613ec35043700f1f0249c29c1d0c03906070328fed7ecc00000,
  unpack 0x38c6bb10039a81c3d30139d6ec007c2c285e8849271671fcf00eb201c000000,
  unpack 0x685ca113ea8073268187e246381b67e489f6d80b2ba39801c0000000,
  (0x65531c30090040064064c009104400035040c3833 <<< 556),
  (0x3845cc15964400031018e3865 <<< 622),
  (0x87431437 <<< 688),
  unpack 0x18073901b7d500e42d030387807c6620ed9a80270000000034,
  unpack 0x3045796287e8662c0313938cc10a40ec501f94823767d0000048540,
  unpack 0x805ae5025f604398b4007e0611f11061c81cc2038208dd9000007400,
  unpack 0x12972842f9021c940c5f983bd9045903f8a0fd4808fc0343a0827303f96e81d53802bf2c000,
  unpack 0x2942f940374d10e8015c0313f13c660852076280fca411bb3e800b40000,
  0,
  unpack 0xab7c910bc2807150297d936441a90078184e6082767c98f4000000,
  (0x71079e20428020050052260488000000a5000922b000000008828069 <<< 497),
  (0x44b0188c0200000000c79030208000048480c19 <<< 563)]

private def t4 : Array ℕ := #[
  (0x6300880a2c0800040012e69 <<< 629),
  (0x1448069 <<< 695),
  unpack 0x1005f416b221cd0063e9419c91062881ecf03b0807410370070f04d8ad1c039940700000006c1c,
  unpack 0x710df1834ff6d002ba0307cc11ec81903f8e3f2900e3107e0b09070420f4600fb2d06c00001e81c0,
  unpack 0x5200f2074eb021c85802378d01e2089d74f0503948077105700a1ec241c4145e61b800700005201c00,
  unpack 0x518573822e0a21c85b13c411f88a1881c8917f2b181eef0827126978600ea501c60c018801c000,
  unpack 0x2a670016f1a01cc5a01374809f88831a00f8385fa1bca1fbb32904e1852e4280e0690d316e001c0000,
  unpack 0xe70fe308dd5003a00574027f0231c411383d2ccf13f43580277079001c3103e18038c407028c73124ffcc00000,
  0,
  unpack 0x4310e3069d64038a814fc3817b1354be204f70d6317c037380000000,
  (0xa34a3c160d00400800c48515100400024200409 <<< 564),
  (0x10d10109830400008018421 <<< 630),
  (0x870239 <<< 696),
  unpack 0x10a6f5824eb801f89ba1a09f1146103b8a1fb5e68dc0343ea38a2fcf4b4a00000e4,
  unpack 0x10d67ba3a7cc10fc2dc1c384724b001c0e13f5b61c770051f0241c7827c34039960702a07ca61d180a201f8c0,
  unpack 0x710eb869f60039bcc680f2451c00f460fe110e7f656c201c58c1ed4ac0e986a901c3a3014410be400]

private def t5 : Array ℕ := #[
  unpack 0x947fbc037c400e800ddc58408f1044e20fa5a1027b4001bdde120e30c1e0e01ce103811579a0270e8c05418000,
  unpack 0xc319ed065d7443f0b05087c662dcb8380fb6c869dd95908270a31fca00f6817484e030d380000,
  unpack 0x394439e087f468015d0307e20c71044e2d4ba281fb0d459fdd9b48070c0878b00eb001c0899dc0c3800000,
  unpack 0x318472072ff6cd0007e8431c4113883a96c703fa1a4d078018f847805c36038000000,
  0,
  (0x1171a1c910010028030300644010000971025 <<< 570),
  (0x664f60460110400840c3d <<< 636),
  0,
  unpack 0x1146b9c0178500e001dd0093a3827319e063fdb6620ce01c1c1880f9601dc103aa1800400000cb8,
  unpack 0x421be08cdc54038a80c7e0c17b13171d287f69cc0b8028fa800e0070ff2f6daa18004a0038380,
  unpack 0xc68dc60c3c23e26008bd1c47924c40f4003da003b040780687e820e0482e9e01cc10381c07805a00a83800,
  unpack 0x340e60edd704393c2c1c1388227055803c9e1f6100ee106e8a4927005978b00ec81c03800416038000,
  unpack 0x835c0193fa3326e4c0c43e332c0075306f09c51fbaba924e3c01feb40075033004e0a80380000,
  unpack 0x31aff2436fa801d003b8023f8309e1074d8c174900ec185e0143f20938e34fc18077240e030df6800000,
  unpack 0x10e39c401bc8887400ee2c48276460c3e5201ca083d5b41063ff58000000,
  unpack 0x230cf2446e9a01c96270c19f09883ba60189c40c9fe80000000]

private def t6 : Array ℕ := #[
  (0x7452066c51040084024060910440002505 <<< 580),
  (0x240d284690100000407 <<< 644),
  (0x109 <<< 711),
  unpack 0x12abf0830f9821d002ba011f4900f8cc5b96e18bda40390f17a370db8f2c03b82075430008001436038,
  unpack 0x605e2849e340390b00e1f30c9106ac81c8b03a48073962f507684107fc37280e0608f04c306188da60700380,
  unpack 0x38cf2432f1801d001ba003f0d19e2d2075307e9201de583d51c2b0e21fc800facd46c003ed800,
  unpack 0x38d07edb1810fc4d0087c606f2451e00fa205f91865f00e0e9049c48e1ee1912070180f826183020fb58000,
  unpack 0x4602e186de60439009fe604fc2668a3feb65084ec0ca49387383e400758c0e0310e4809c107e80000,
  unpack 0xc250e20edf9179de30876262ac207b243f084703ba3e000e38b1fc91607030f7000000,
  unpack 0x2115fe29021cd40a1f0c09d89829c01f02138a619c0343c08271a5470000000,
  (0x31878a116c0820032003e102802000018800512324000000507 <<< 517),
  (0x188b008283020001880c81c22208000060f <<< 583),
  0,
  (0x9 <<< 716),
  unpack 0x32ae70066f68f89ab0e39f198831840fc307fa1b402fb8352600f1e1e01dea0381077ec300b038044a885817b58,
  unpack 0x4154e68a1ff99934081f1a29d964ba080e4061f0051e9249c39e3e1803ecb0180f00c834a8d00]

private def t7 : Array ℕ := #[
  unpack 0x21de30e9d7043a003700e1e9c3bc20c4903f040fb4240bd5e560873f50da00381c23806428b000,
  unpack 0x2884398197cc10e2a061f8410ec4c41e5312c4e5201ce381c0247a08270a387b86d081c0e03c0004c70000,
  unpack 0x2115393ba21cc9a001f4301f8a9e040e48c3700d1ec041c2165e1403b9607000efd860170700000,
  unpack 0x138ef3c54f3821c014ff1057e20e4bf1c7e6141f607d249c3083f3c039960702c07000000,
  unpack 0x18683ed1e5b4006e81cdd3823e132d207e007fd0c060dc0307d49271d0070000000,
  unpack 0x5303744244398b40a3f8e11c2ab0071105e6db00000000,
  (0x320d04290c8020070021830000020000d <<< 589),
  (0xc28068a922000013 <<< 655),
  0,
  (0x25f0832cd5060000080031d00040003 <<< 592),
  unpack 0x728573402ec8f458022fc009ec9190391c176800e6242e0000004a0,
  unpack 0x4206f3420f3a21cd00e0f8023c90569039163fd8612c2e0800003374f500,
  unpack 0x18827c108bc4a876006e0145e2827815840ea38bd2403a0e278078fd418e1fa180cabc00e16000,
  unpack 0x5207f3466f2a81d801b8053783784c1a97e40bcd142ef4004c3800ae0000,
  unpack 0x60a373012e8a01c003b80627c901ec4c41f63d004f6b05aa3e000e1c40f480c9bd908b800000,
  unpack 0x388438c087d510e6a050fcf1ce150903d980f4900e7080e242c267656000000]

private def t8 : Array ℕ := #[
  (0x14c90380132a0c0188087142a208800042881e40812000001e1000003006087 <<< 471),
  (0x42ca11854000031029f1c34001000090100840106081 <<< 538),
  (0x46041865b820801480409e3226887 <<< 603),
  0,
  unpack 0x8505e200dd7043f28181e1c53e20862075004e01000000029,
  unpack 0x310bf0434f68d001ba05278014f88b2a1037d4e890a401d48c8503800000,
  unpack 0x6107f1814eb801c9e769a21f198abc81f460fea4184ec80000000,
  unpack 0x102b7ca0db8e087340307c18a70a3c01f471ff2d081ee8f0403981fcb5280e0344e4281c02be8c000,
  0,
  unpack 0xc006e588de44039281c7e0477e22aa207d244ed201d6319c01c7e49070870fa960581c043bf19f83e4600000,
  unpack 0x112473020f8221f89807070718e272075302e608276490c409c000000,
  unpack 0x200639c3a78d10e64f9cc10ec8a8481d0907f6b0882f00d1fb2c0000000,
  (0xc04184c8020001001c81c28208000022c81038e11 <<< 551),
  (0x850510065c10400040c0871104401 <<< 604),
  (0x8202003 <<< 692),
  (0x20c50c1db3001001901111410001000011101 <<< 574)]

private def t9 : Array ℕ := #[
  unpack 0x502270c10e3201c003ba04274218e48a3c81ec00bf43294770091fd209c59c1c3403894074a00001a0,
  unpack 0x71a173076e2821d003ba01370311f84c5eb7020bed4024f00b0ea4c60c5e6195207543000359fc600,
  unpack 0x30d47862074110e0025f8c09c411391803d8a374900e214dea0e10009fce00ed101c0603f498054d40c0e000,
  unpack 0x700d73c00fa801d001bb2833e13151903f9c2f856707d96024e0cc0f1a01d89038257172ca0000,
  unpack 0x20c67921979910fc4c008fa48af023081c4307f434144700e0fa8908bd4b2a00e0414e6a49c1e9600000,
  unpack 0xe349ecac62c5c10df84c15640fc487ee1a8037807078120e3833f1201d0b33da000000,
  (0x18a242049a200800480498e1a208800002881678c12000000621a006240685 <<< 475),
  (0xe44c08509800000600e78c0800000003444021c568421 <<< 540),
  (0x508106180a8820062003a58e11a1 <<< 609),
  (0x875d24321959 <<< 672),
  unpack 0x1c538c1979c10fc2d0297a004fc6620f99a8c3f4900e92cae01e3e1580000002d,
  unpack 0x1c48bec5c6007250107820af02bc81e081f9480741a1f606a833cbf53ec6840000d5d0,
  unpack 0x1054f9c2a7d510e62d0303a304f62608f20770c2f70d441dc0187b492700517986e001c00063efcb00,
  unpack 0x15139a1170910e2a93c115ec4c418e0071206e7062700000000,
  unpack 0x700071026f490b4027fc0d898a3c01d840bdc340e677079049c00a5e2403cb349b1290417350000,
  unpack 0xe11ae586df2990b073073e331725b180fe46013dd1e49271c21f8a00ea401c061bdd507801c70651e00000]

private def t10 : Array ℕ := #[
  unpack 0x420df0052e2821f94064e1e19c9106a481d8d1bf6b4843f00d1ed049c3067f3c0385647d66000000,
  unpack 0x14299c219bfa2a033f0114f84d8cf841bf5b4925f308274108e0000000,
  (0x430208500100000e40a58709100400011040730329c5 <<< 544),
  (0x823a18cd3a20801c00cd8822000041 <<< 599),
  (0x29d54218204015 <<< 666),
  (0x18238082d9a208008814a9432000800043 <<< 587),
  unpack 0xc487c409b840c7006178414f8883c4c41bec321c0700000000,
  unpack 0x395739e2971110fc6c018bc48876260a40f8789e12180704000019a6600,
  unpack 0xc117e4025d7063f2014bc3807e130729f9837e860389ecae841382147c18073880e0355e001560063ba000,
  unpack 0x875fe4089f04639937579c0bc9169a1c1f0a8827807878262091fd6d090380567d20b680000,
  unpack 0x20650e9f24639a804bf1473e13147903e9a3fe86b180ea0fd18a0d815400e00000,
  unpack 0x28477961a79908e62c019be282fc2620d110389407e5ebd040c000000,
  unpack 0x4301e18edf7043a00370025f28f198790388a2fb86f080e0fa3e000e0000000,
  unpack 0x8656fa2e91a007740c1f1a23f107130c3f6cc00000000,
  (0xe34c0462c418400a4066c404135 <<< 612),
  0]

private def t11 : Array ℕ := #[
  unpack 0x400372420e8a01c003ba043fcf1df84ca881d0703dc321c1f506c201c3101f2c03b82075430008003d961,
  (0x661624664100000e0066071410000002144072064c5501 <<< 536),
  unpack 0x625ae2865c2443a00574047e0e23f1165d183e48abe11284ea8fb5841a70077280e8400196c00,
  unpack 0x18c27902a71c10e8019f81c00af2455a40ea70bd1157c3448fc0287d49270601f2d2074b3000000,
  unpack 0x4320f3042eaa21f858061fc210e482a481e8313ec340c47407f0c0823e3c038d6070124f3404e0b20380000,
  unpack 0x4c3dc014be2887326e868af241a67c589d3157c32517dd1c49070e207e96b081c0ab9c5103f9b0644e00000,
  unpack 0x1803fce15b8a88734038be00efc450c40f2287e13006f747c009c59e7f1803bd327fc6000000,
  (0x30841a08628820050071a68008000001ad207121322a808068c780006451 <<< 481),
  0,
  (0x116c31993001001800050006d <<< 618),
  (0x1 <<< 713),
  (0xc2070c541 <<< 684),
  0,
  unpack 0x2022f0c42fd8c940e3f803bd898b2b80176800eb300ef40000334fd300,
  unpack 0x20972436f2a21d003b806170b0ce2089c54240e028ff50805f00e1e4249c2103d3403b5607338800000,
  unpack 0x400be2825fd400ae8109f2047b1325207c102fca4e278068f8262091fd6d490380147d248b00000]

private def t12 : Array ℕ := #[
  unpack 0x20d7394307c910e68022f4a1cf84c41f4b1180fd0da78bc03c7a08270c38f2140701aef6405ea8c00000,
  unpack 0x32470436f8201c003b806270109f88835600f6001d8403ac403abe4c01127b010e000000,
  unpack 0x6006f44f00438a00cfd2053e13106a081e801bb400759807614b7e660000000,
  (0x10c60200370000030008f3c440110000c69028119955c21 <<< 534),
  (0xe40520109900400000c28410834031 <<< 600),
  (0x200304425d401 <<< 668),
  unpack 0x18a8bcb19be4887400ae80cfe042788227106a401d8407f6b00237546d001c5101c000000a94,
  unpack 0x2096b861275800e62c5cd18f8829401c4903a48075064700a1f9041c4903ed5280e3060000ba662d90,
  unpack 0x18d338e3179110fc6d0117a30871044e20d7803e9407e42799dd9b080706097c700ed181d50c000d3040f1801fd00,
  unpack 0x4348e2829d6443f1b4044f1639f1054903e862f6800ec202ec8ea0138134fa70076240e0055fa4c0046a9000,
  unpack 0xa701f84e70038a800de1c0388227152803e0c276800e63cae01c1d498c0c7f43c760519e4a01c974580000,
  unpack 0x94b94087a4500a3e8233f1146903b0c3fb50301ddc024e1830f50d8103901b20276200000,
  unpack 0x21fe2845f10438a018bc3417851c40fa287d8403a4d0fa832920eb471a01cd1042e000000,
  unpack 0x50be3045c1443928149f2873b13733d184f70ce083d91f5087e960000000,
  (0x70850a2b060000060061e20600000001ab2069803403049 <<< 533),
  (0x40151c504810400640e385012052605 <<< 596)]

private def t13 : Array ℕ := #[
  (0xe00630560d5041 <<< 664),
  unpack 0x1956f9a2b74410e62c011be38276260a700712c6fb0ce415c0147c2b063170000000,
  unpack 0x128271c62eaa01c004dd1837e13157003e02176100e1007e0163da0938b1c3a48074280e98600006a0,
  unpack 0xa1bc00cbc28019d0187a5027c441ae207d186fd6cc607c1c824e2c63e9601ca903aa18001b6fa00,
  unpack 0x18527941374110e801dd038fe306f1044e20c4903994376100ed2c1ec8da083843cbc18073880e0454fa4c02bead000,
  unpack 0x1c41fcd00bea007000eee0f2c73b13107d6e0b1bedb098576600938d2c7fcb10c0e944ba80000,
  unpack 0x15678c0279100e801dc008fc108fc260d4bd1c0e1824f0061f5249c01e3c2c039460701a476021f0051c00000,
  unpack 0x10c2b921b71900e801dd0383e102fc660af207d207fd0c8119d41a41071a007f5ca93fa000000,
  unpack 0x28c6f98237d510e42d028ffcbc45654013ea22c0e0143e029bc20000000,
  (0x1960a0d114010030009200344110000c69010819365 <<< 546),
  (0x51821e034080200100302082c2021 <<< 605),
  0,
  (0x381247 <<< 698),
  (0xce8e10652000000c0001120020880006348181 <<< 567),
  (0x1829218088820001 <<< 659),
  unpack 0x84c5013e8087e50317e10af1044e0a50074245fc8461780687c104e607f2dd03aa70057cdf2000]

private def t14 : Array ℕ := #[
  unpack 0x6556e78a1fd2168181c3853b13145803c84270000940000,
  unpack 0x500671846ee16818de0453851a40ec10ff6da8f178078f4104e1871e4280e035dec80bc00c7f200000,
  unpack 0x200be5021e7443f200c9f3c67800253079080e000000,
  (0x39d5c615130400011020820240000000d4101040d840000005 <<< 522),
  (0xc51c28440800400e4024841d104000034e0012426d1 <<< 548),
  (0x8ca858451a20001c81cb8413 <<< 623),
  0,
  unpack 0x1c82dc40cbe288732680cfc1c6388227106a481ec407b08077121f00d0fc049c5047d1c039940700000017d,
  unpack 0xc20dc1143d26b130700f88b8cd8a0fedb29a7f00f0e8249c3925f2403a92074030000345f2b0,
  unpack 0xa214e684dd44439934005f9001f19979039022f848015c02c7848270220fc800ec181c0e01c0016ce3003cbb00,
  unpack 0x4ab5cd093c2087e5020be3847643801e8713f4309c4f74708f00bfdb1280e0255e00171b626000,
  unpack 0x89f2830eb801cc5a03278805f2609c038be2808bf56042f646c009c7101d2c039c4070380f5500e49b2c80e6db0000,
  unpack 0x28f2442e1221c014dc3437c9a0700e3e8481d490ff6b308270784938d00798b0381943a88078028e2023f500000,
  (0x62268c9aa20800801c19229060001c48881a40282000001e28c01601200000030e20c0061d90083 <<< 399),
  unpack 0x46b863a720077072453b20aa007e3c1f70d6719c01c3c1d97420ae0000000,
  (0x68670848820801c804d9a01260001c21401660c8aae025 <<< 531)]

private def t15 : Array ℕ := #[
  0,
  (0x46b6084098a005 <<< 663),
  unpack 0x410e72c72f9821c85b0bc908f883d2d8f13b4007318176565249c4145f9e969400001eca,
  (0x31138811a5041000103 <<< 646),
  unpack 0x14e23cd10e2a04178e1de48a8c81c8c0fb40077823f00f0f8201c0163fe98000000,
  unpack 0x4c3b5794cc5a03174308e150903f940fd86b0c5e0163d0413b1da68070a40e0515e00f4000,
  unpack 0xe209e1885d4043a003700c2f123bc41138396f4903b080741c2700d0e5009c4841e2c03b520700a4f3404e2e980000,
  unpack 0xa65fe2061f740398b0043f1221d89871039100f840519c01c3b40271e0974f00ea101c0aa3d4417801c70640e00000,
  unpack 0x10e31d85c6807e16804fe81e22a62070385fab420b8068f8924e38b2e9c01ccb23ea000000,
  unpack 0x3ad73874f8a21d003bb930f01e4829481fcd13c2438fee0d2083f20000000,
  (0x108be50811a208000010e0622008800008081838ac2001 <<< 539),
  (0x50a79a02600020000030e68e1 <<< 621),
  (0x1 <<< 717),
  (0x2803051d3 <<< 686),
  unpack 0xc44de388dc7543f1b6068239c0ac007e246fdad8011c0307fa1cd0f9c01c8a0380c278000293160,
  unpack 0x8643e00ede35439a00c9d3c33b13047003d08274900ed008ea8e108597986e001c0006338c00e00]

private def t16 : Array ℕ := #[
  unpack 0xe71de6069ff1a00776578a09f1106c89617e50791c01c7941071659ffa67181c04abc00234000,
  unpack 0x414ee6065f91f2a4f3037e331061c81f0d17ead381e0063e8083ad9a5807640e33c9403800000,
  unpack 0x1c4b5c10cb84a07e368087d0837850e40e818bda003b0423806870920e0013f1a01d890381907a2207f400000,
  unpack 0xc2abc11dbaa287000efcee1817b13172df1a07d4c483c0287f09071041fba7c6c000000,
  (0x1021076c54000040062061c100000031040a14168000000930c00e0a33 <<< 484),
  (0x42a0801924a800010030268680220000832058c08401 <<< 545),
  (0x675000300510000440c1830427 <<< 616),
  0,
  unpack 0x30971804f6f28109c20279cd083785e68dc0343ea38a2fcf4b4a0000035,
  unpack 0x11d7f802b74500e001dc009be38e724ac01cce179480761c1f00d1f04c58a3d1c03950c0000b000e0,
  unpack 0x638073430f3a21f85f33ce0ce1076ce480fb480710a070061fc201ce8ee5f200006903ea00,
  0,
  unpack 0xa115e4885d2043f28047d3467b22a900793c7f690327b24249c0165f0403e3301acfa414b223a1c071220e0000,
  unpack 0x638af3452fb021c57168a01d898bcc800f6100e1280e80c049387087c3b8c02a3cd593983e7600000,
  unpack 0x62ae76461821cc9b830908ec821481e8113f5b102670071f04c51e3d34039c547a200e000000,
  unpack 0x6454fac2807e37c0ea19220d7803d0c3fdb633c8e01e1e225bfa0000000]

private def t17 : Array ℕ := #[
  (0xc6a670c91a20800480490a30208800049400a380d823 <<< 543),
  (0xcc1a20e5aa208014800a840140b <<< 611),
  (0x400094300eb <<< 677),
  unpack 0x1080dcc0dbf63400ee0a3867c260a320790c4f090c178070feb61ce1e00000002,
  unpack 0x190638c197ba66a032f880de2089c50e00e2281f61b4c038078f8124e2053e9401fa5a90000524015d10,
  unpack 0x722370866e3221d003ba0717c405ec4c15600f6183d8403b8a078058fa804e0443f0601dc003800066e9fc300,
  unpack 0x310f73070f1801c014bc0827b20f5b71c6fd6dc597c0387f131a487eb76cc0431f900154d5c3000,
  unpack 0x487c504bc48074006e804bc3857b13056803d162fed6f3c0ea8e8013995fcb4a40e0549eaa01c06447290000,
  unpack 0x2219e68e9c4443928183f3c77922a22071385fd0de381c03c7eab0c10f4700f8ec04a3f21c00c727100000,
  unpack 0xe257e180dd4043a00574061f1433c4113ba9d86072900e0388eeac84838a307e500722c0fb8f9000000,
  unpack 0x2003e100de2443f2a0c20178571607eb640caea851a74101e0000000,
  (0x19d68e14830000010038c1c304100000178000205a30c241 <<< 530),
  (0x19808910164400038000524608159 <<< 606),
  (0x281406150610001 <<< 662),
  (0x8d28f0ca7401 <<< 670),
  (0x18c78f09900400038000d1c744010000c2101481d <<< 558)]

private def t18 : Array ℕ := #[
  unpack 0x1b0c9053c40872168181c1417b2c97810fcf5e800006400,
  unpack 0x29d7b9c037dd00e4a073f8804f84c41db35207fc8000084000,
  unpack 0x3107f0036f3a21c003b804374701e48831c40fa10bf901000840000,
  unpack 0x30c1b923b7fc62a071f4a15e1716087ed001da28bc0343a08270c38f29407012af6405e0063c00000,
  unpack 0x310bf0434f68d001ba05278014f88b2a1037d4e8902441c000000,
  unpack 0x10289c51dbe8887316800bd0073e2ca70505c028501c0000000,
  (0x38560519b60410031020308704000000050020a0c1 <<< 554),
  (0x51aa9231448000040012e68cc1 <<< 617),
  (0x1cc805 <<< 699),
  unpack 0xa102e18c5f3043a007700e6e0433d89939038823f6800e900be2451c3c1c039940700000054b,
  unpack 0x7c33856e2a01d001ba0437ca08e2089c55a00ec48bee1bc52b80587ed63cd0e9a01c4a03818238000293790,
  unpack 0x600972474f2801cd4064ffcf1072d98a0fdb6110cecaff9861cbc18071a40ea860006e3ecab00,
  (0xc40b24668500000e40a5411c004400000640104408c5081 <<< 532),
  unpack 0x3900782197d800fca0417c614e0f007e0c6fca842f803876800e0471ff2f6d80863b80070d0c80e6cb0000,
  unpack 0x215de78a1c5443a006700c1f9211f11061c01f5980e2fb47838bc0387a01271a01f4e00fdac0493fb5fa2023ed00000,
  unpack 0x963079c00e28050fc318f84c15e40e0605e159c07766c249c68a1ee1a1207606000000]

private def t19 : Array ℕ := #[
  unpack 0xa37ca0d3e480735c9e004f2e9b0a1701c5f68ecb07b032924e8611fd0000000,
  0,
  (0x10008d00840410019029c2c54c10083 <<< 598),
  (0x21ae800b2e0801 <<< 665),
  0,
  unpack 0x9157941b7e87c2d0313c48cfc2620d4803b121feb6f2cfe0063ff58118bf4b1280e840018da07b286207,
  unpack 0x255e60e9fd2022fc804f88396e8e1fb080749e1700b1f1241c0987f08038880a27540000041fe3,
  unpack 0xa043e082de6443a005740e0e080bd91068881f8e039ebd0000000005ce,
  unpack 0x9163861b7cc00fcf31e09f1982b881d0d13f2b184ec0c20938234fa1807b96a460289d50020c6d03d2700e,
  unpack 0x3080f9a3a7f86801dd0397c106f6410a40e2403cf41f4000000103fe6,
  unpack 0x2052e0849f934001fe00afc265840e440ff61bc233b35201c79e7e2803b4607220289d500000a8c,
  unpack 0xe87ce11b8e00731681cbecd882270a2077206e9201c2415d01b40271e1979867001c0e21c4513aa005104e3680b801c,
  unpack 0x38967860b7c900e800dd038f8104f62620c7803a160feb6b2c7e00e1ff58b0c3f431280e98600c86368000578,
  unpack 0x2228f2860f4a00674083e9231d9107d8cc713dc32924f57a4038b187ff3c96937880c432007c6d01415038,
  unpack 0x412ef2816fa801f94082f0013c9250076384fab0e038018f4920e0083f29060702aef004844a885807b18,
  unpack 0xc309e70cdea1a006700e7f0409f19858039180f4900e524ee0123e8013830c7e500797604000174f4da06470]

private def t20 : Array ℕ := #[
  0,
  unpack 0x32adf1430eb221f89bb34611f8cc5c66408bf979e7f56d18287e96d001c0633c850392ed0ef1001f8fd0,
  unpack 0xc718e18c1d6043f1340a6f0613d8994903c94076100e4380e00062032e88560,
  unpack 0x8493ca1cb8a807400cec2e2063e131468039841f4900e638ce00e1d8013820cfe500738c0e0501e0006852170b800e0,
  unpack 0x10473922b75800e42c0217e402fc4418d2079080fa9d1214803a9190a070876018d8140,
  unpack 0x6a5cd053d234006e814fc0867922e53e2c1fc8842fb248718ba78073ac0e0350f4831018d8740,
  unpack 0x211ee086de54039aeaf3407e131069881f9d46589dc1ff30411f4700e7501c0491cd503843bc414418b8068e03fac0,
  unpack 0x8629c6153e5b400ce8189c2c63e13153903c18376800e828fe01e1f2413872c785807ed60059f480b6600e03b1b003a380,
  unpack 0x10609cc083ca807150183c58afc26ea7c385fa198f1fb248e10bf43b960709f8800e229003b1b0780380,
  unpack 0x448fcd013ac88725018fc18c7083cb7c483fad9c617805876020e1070e1c01dea038145792a0708762429b003471be80,
  unpack 0x8dfa561a01f89a0227cd10e0658303f08c703aa32804e2453f50c6103a900037540a0700,
  unpack 0x3091b8a0375d00fca020fc004ec4c1b96270bfb5b0d3fb21049c58a7fadb02074c30003ede800700,
  0,
  unpack 0x1009fcc143e2001dd028bc30ef1044e2db381c1f0b0c03bd00000cc200,
  unpack 0x6102e7865d300380077e678a3bf10794300fd6ca015d41d0927160874e00e3401d52c0020685017fe600,
  unpack 0x210e72c24f2a01c85a06074f0df88b2a102f3d07d00000c8c00]

private def t21 : Array ℕ := #[
  unpack 0x308478e0374500e8019d010fc68a7c441d331187fd6ce38dc0247d00270810f8600eb181d50c000da400,
  unpack 0x801fe50edf119031be00efc262ad2079345fd6d4287d91d41270239f086074b8800a20c1800,
  unpack 0x317e38c5f40438a000ff2c538822714390399c07d86826ecf898c1cbc70073a80e806001b6600d03800,
  unpack 0xa65fe30e5d5003993e679411d9151103b862f844189c1e124e1452ffcda103a9c40623f1800,
  unpack 0x2100f2012e9821d002b8011fc011f888364810f9650ddd9909271e197f4a20380927ec300b03824000e7000,
  unpack 0x20d7b960b7a46001dc001f870e764b801c091bdc3490570031e1249c6087ee5ad4075135545e015e58987007000,
  unpack 0x231fe78edd1443a00774041e8a09f1051903a942fe867246ecada48383307e5807dc6021de48c5fc1a804735d1a5420fd000,
  unpack 0x8d378e3271500fc80517cf10f88835640e6489da4038418030fa824e2852f8801dc303881b802f1d2808f8301c72300e0e000,
  0,
  unpack 0x30833983274410e4a05370f00f8cc55400f2603fa1986138058fc804e10774dc003aa580282fafa048015c000,
  unpack 0x6117e188df1443a003700e1e0e39f11063481e4203ea74485200ea464281c21d874000,
  unpack 0x2111e50cdfd1a007740a1e141bc91069401d820bc2e042e01e1d80938e2cbf4b5240e0658eaa8bc175f40abc001c000,
  unpack 0x384178a387d910e42d020b86827c66a972403f500a4f7664209c78a7d2403e20505e6281c1758180e050d8000,
  unpack 0xe61ee5869f11f20145f3457e331699a0e076900e91c9eeafc98b0438680758c0e060df482ebe928000,
  unpack 0x3850f82237c810e00c7e8229f1145103a9427e5411bd95b482702797f96e80133b2a0f05d7d03e8000,
  unpack 0x2328f2034e3821f89a033f021dec83d8e810bedb684377471049c4907f3803f6b0120f0544e4bb43b3ab0000]

private def t22 : Array ℕ := #[
  unpack 0xca8bcb04be533585c18a7c414240e868fda40388e3f8050fe100e3880e9601ce10381943b3ee3c96057310000,
  unpack 0x130af2006e3a01d001ba021f471106ac01c0b03b40073944f74a4138c34bc48076840e0411e8881c94820bcc3f260000,
  unpack 0x62a0f0442e2a01c540e2fc81881d4c03edb18247657d209c5985c3c038520700aef7b8f0b240ae9860000,
  unpack 0x18aa7cf19bc408735010b858ef6441ab2077180fd0d4413c03c7c131048feb68481c02b3e905b661f20000,
  0,
  unpack 0x2006f1846f0a01c85b2067841872071202fa9d1214803a9190a070a40000,
  unpack 0x1202f670443f0b4086e080bc4113bb199037b86434de0183ea403821cfc70076a80e926e801c34320780000,
  unpack 0xe61ae68e1d2443928085e3c379220d4803f1e2f2900e4087e0143d00938124be7807ed6326c381c975980000,
  unpack 0x3182390337ca6800dc021fa7847c261640f8483f921e6700c1e4249c1983ee5f6b0006f3404e0b880000,
  unpack 0x803b8a0a70d00e6a0437020dec4c2881e0a07a480738b5079049c40e3f1c03986072135404e19300000,
  unpack 0x8456e5865c6043a00674025f1e13f1053103998372083b8038f4900e04c3e9401c4a0380d3790a072100000,
  unpack 0x18179a3a7d500e800dd008bc58072441f4bf307e9201da31bc0187da04d2e9601dc30381d478820ff562cabfd00000,
  unpack 0x2984f843378910e8015d0293a68e7c662e5373c0e5201c6581d41fdb1651f0d00f6ec0683d458f801cf4660e00000,
  unpack 0xa014e1845c44438007740c4e022bf0986803b123f08e3f8248b18be70073200e0705e8883fd5da00000,
  unpack 0x4150e1881d50038a80c9fad841e2e307f92881747800387103d3881d17b21171400000,
  unpack 0x410af4168a01c900e2e0c09f19883a96e2ca403a4c23baba904e3c31e9601d430380953b280f7400000]

private def t23 : Array ℕ := #[
  unpack 0xc293c914b8a887150187a606fc454600e2209fb5acc13b2bf462836d400000,
  unpack 0x116794117c4540e5e1239f107a9e1a27b86c86e8c0493958700e3481d00d0123800000,
  unpack 0x408271c60fa821c57269c01c20d1903d101fb5a689c00c7b40071221fca00ed001c0c21d9803800000,
  unpack 0x48b5ca083c2087400eec018f88a3c01fc30fdac285e01a3e048382047e60075200e0504fe800000,
  unpack 0x24fe408de5043a00374083e822bc411382a801dc01ff43592170070f5049c7007fe98c20701907000000,
  unpack 0x112670c26f3021d003b8012fc518ecba9d0e270091f80707b5618f2f9601ca203ad000000,
  unpack 0x120a70852eb021d003b8021f0919e106b481f8d13ec351a17547c049c2127e5cb62087f5000000,
  unpack 0x2a070c54fa821f8d8052f4a04f8cdd8f8017b08077047f547c001c7141f1c03a544720d4e000000,
  unpack 0xc652e5021f7003f1b00c5e023bc1c00f850bda0038420b8060ff43003e24038464f3900e000000,
  unpack 0x3884b983b74900e6f034a05f8cdcd0c0fb86f080ef2616107f2000000,
  unpack 0x1915b8e2a78910e8019d0213903c260f4b1007fdac6385c0287b48070841f4a00e25a1c000000,
  unpack 0x4504e20add300380387c7847c6608f2079080fa9d7930f801c000000,
  unpack 0x2095b942875510e800dd001fe08a76411840ee0d84039062f825241c68e7d24438000000,
  unpack 0x51a9f1076ff4c858032fcb19e106a881dca07f5b3063f0031f0209c3885e0f038000000,
  unpack 0x1022bc71cbe8087e1600cde04478418d207b0c3e41e477471201c58a5f40038000000,
  unpack 0x600ee42f9400aeec5047c662ae0074240ed001c429bdd9dab180270000000]

private def t24 : Array ℕ := #[
  unpack 0x520af1864f9821c96261603c28f2071140fb6ca585dd9d4827148070000000,
  unpack 0x475ae3021ff998b00a5f1819f1155103f8a178522c0347d41274204e0000000,
  (0x44013810c000000640a44e10100400030c00710508000000a48c00b04ba2415 <<< 468),
  (0x28134908044410039031118504010000c61024c18800000021d100140224b3 <<< 474),
  unpack 0x1ca13c41c3e208735018bc00c71044e2ad20751c1f70d4e01d850fc0000000,
  (0x134b14070000018038724304000000179024414a400000240140247ad <<< 486),
  (0x841c3062180040040023041c000000020e40d1c401000000050500d0b <<< 492),
  (0x842268e59020801c8008920a008800061c012008c2000000458e00d <<< 499),
  0,
  unpack 0x22d73844f2821c85a043f4a04e4834f1c0fdb695cbfc80000000,
  unpack 0x8642e6825ee99001fa708f0a1c01f0e17948074b28700000000,
  0,
  (0x538512106a8820060070028a880200012d202143b0820499 <<< 529),
  (0x322c1c1b668000072001a300880200002e00494190e287 <<< 537),
  (0x7329080a608020072033a086880200002500506110e25 <<< 541),
  (0xc08c78481820801880c884222080000420804682c03 <<< 547)]

private def t25 : Array ℕ := #[
  unpack 0x2150ec8ea1f1b7060629f19ad3044edc01c00000000,
  unpack 0xcc1fcc19be28072168814ec8b4903f400000000,
  (0x2288163a2e8800002030e504800200018820709 <<< 565),
  (0x429028852020001c00c51810200000069880b <<< 571),
  0,
  (0xe34b08308d00400c002449190004000307 <<< 584),
  (0x42ba188d982080100083961220800003 <<< 591),
  (0x1c4ac4000ba208014000a163a2eacc03 <<< 595),
  (0x1010c21900440003000960404c010d <<< 602),
  (0x1c48448498a00801481ca1a286e15 <<< 607),
  (0x2090e106208200220112306093 <<< 613),
  (0x82946824b000000080481c335 <<< 619),
  (0x530e9811468800072072e109 <<< 625),
  (0xca9470e180208004000901 <<< 631),
  (0x110382104e8800050023d <<< 637),
  (0x1001c6820aa208018017 <<< 643)]

private def t26 : Array ℕ := #[
  0,
  (0x4718182014104005 <<< 656),
  (0x6284820902880b9 <<< 661),
  (0xca9818603821 <<< 671),
  (0x202b10100cb1 <<< 673),
  (0x8e8400a50b <<< 679),
  (0x520212197 <<< 685),
  (0x830685 <<< 691),
  (0x41ae99 <<< 697),
  (0x18225 <<< 703),
  (0x427 <<< 709),
  (0x1f <<< 715),
  (0x1 <<< 725),
  (0x31 <<< 714),
  0,
  unpack 0x630b71036f8021c50046e1609c0ad00701c0fd6c6281c1547941f90000000a]

private def t27 : Array ℕ := #[
  unpack 0x2082b9c387fe662d89828c70bd8cc013dc37840707d000000843a,
  unpack 0x2886f982a7eb642d0317f4bc441a2207a0c0ec201d8093c0287e01070439ff872ed0800185805a,
  unpack 0x210e72c24f2a01c85a06074f00f8cc41db35004e01000000014,
  unpack 0x14eb9ca043a6007400ce0f9b0835400f208dfada001bb2b8804e3c03e0e01cca0380000074,
  unpack 0x30913803874810e8019d019fc58c7649801c4b17a48073125f74a48381207e200730c0e867cec0015010d4,
  unpack 0xc4b7c710bca0072481e382f249084fd6d80c16124e0032f0816075200109860000e38,
  unpack 0x31c4f821b74410e42c009fe48c7c6620d2103a92376900e20cce0183ca4938c0c7c2807e760709f04c30601c4320070128,
  unpack 0x108873006f68d003bbb34d10f84c5c6401ba480761e470071faad4efd6080e0114fb0c02c0e0001e8,
  (0x1185480002441001002193430011 <<< 610),
  unpack 0x3993b861275100e68021f8011e142903f9637b5e717d54024e28c0e9e01d4103814679aa070d746828018fc0f1000,
  unpack 0x308670442fb021d001b8030fc409e2089c0145f70d2609c0343a48270c197f50b038086790a070000a40,
  unpack 0x508e2829e20438a00cdfcdb22f4bb187ed201ce001c0000008460,
  unpack 0xe359e20a9d74439a81c9f0433922aa00723c5fcb4f2babd241c1863e3003f6b0300f00030b0da60,
  unpack 0x710273004f8221f89a07278204f88835400f8703c4104ec0c90a401d48c8503800293060c0,
  unpack 0x21c17e8b8110e64d81e602fc2608b207a245fa90a03b038024e0c50f52c0601e0000940,
  unpack 0x320bf3040ea221f89b834b19ec4c418c2077184f6bc53ba83a124e0492f8c01ee580d43b0e0700062c083f40]

private def t28 : Array ℕ := #[
  unpack 0x532af0472fe8c94003e0e13f198aa481c051fda510be01e3e118407cc00e3501c0c03c003689860031380,
  unpack 0xc019c304bec887e2600c5ed185964207f2304be0d48270038f8600e3581c0e11e09860c0388ea60a40380,
  unpack 0x421de78a9d34038a20e1453922ae207e246fd6cc583c03c3edb045074300eb181c021bd900b0380340bc80,
  (0x1004c501b34010001001f040000000001 <<< 590),
  unpack 0x3886b963a75400fc6c018fa684fc661c40f6085d8403a0407ab9009c1045e0c03a54074a0006800,
  0,
  (0x41433032cc10000200668700100000020e00c107690000007 <<< 524),
  (0x18020411 <<< 690),
  unpack 0x405fe6829f24038a8089e1c33e22a62071104fab0613b200000a4c00,
  unpack 0x8708e6045c7403f1b00a4f8033f098a2481cc31bf43608070091f8249c7803fad8000000,
  unpack 0x2501f62d2043f130086f9229f1983903b043fe44601c0307c41071660feb6b481d50c000a8280,
  unpack 0x3081f1042e3a01f94042f1603f110794d8b17b08074107700e1f8049c3081fd60c0e0700e0012800,
  unpack 0x8411ec82887e16800bd1863e3305310381617ed6e28deecec9b1de58076ac0e0608e0001a80,
  unpack 0x630cf1034f2021c9e779033d8986103f1a27db64186e8f4308497fb6e101d00c0320d000,
  unpack 0x10639c1093ec80721601cdf3833e13053803e1827e8653c5e01a1f24138f00fdd3d4000000,
  0]

private def t29 : Array ℕ := #[
  unpack 0xe019e7829fa199340a5e1e09c91078b0e372c0338078fe800e2041fc8000000,
  unpack 0xa746e58cdd3003f28187d1437e220ed9d0a0f000000001a,
  unpack 0x338471032fa021d001b807270315e0699f983f6800e30ceeaa012765b0000000,
  unpack 0x660fe6069c7043f28181f1c53e20862075004e0100000007a,
  unpack 0x440fe6805e240390b7169e03f0982a881e821fb0807494570031ffac6185f900000084,
  unpack 0x10813863075800e4a0727ce00e4883e97a089d840384d0380387a004e2ce1fc990074c3c40220900b4,
  unpack 0x148a1c11c3e8007400aea4f1807b2ba6a701da0038063fb364c6085f1c039500703807000b2001518,
  unpack 0x3043b942b79900e42d0287e08efc260a2207e3c7fb6ca21bc03c3a08271449f8d00eb581c0611f101886400e00b08,
  unpack 0x39d4f8c237d110e8015d0287e080f1044ea96428bf521c070031f9241c0107e520c0e055de009089510b00,
  unpack 0x31a9f0834e3021cc5a053f0c0cf84c41f338181e68a5f00b1f70c3043d3c03b04070304f000000,
  unpack 0x85f3426e3221d0033a03170e1ce045803d1e2fed61047e01c1cc693a00e0419ea801c35d1a0000,
  unpack 0x2a7f0c62f090b756860bd898ac8843fe5a51fdd9b0807160070000000,
  0,
  unpack 0x14621c205bd433160087d0047e130c207e046fa9cf1bb23d44141f18038000000,
  unpack 0x10873961279500e42d0303a786fc4595081bea744800005400,
  (0x19d3091027440003 <<< 658)]

private def t30 : Array ℕ := #[
  unpack 0x4204e78add704398b2480f6262862070305ec201d0585c01c7edb04617f86f001c0c81f9d800000,
  unpack 0x7385f3052eaa01f898051f4b18e496803a0e27ed68184e0123d04838b3cbe50077280e8400210e80,
  unpack 0x4fe7045d4403a00675069231c41138834240fc583ed70c770051e9209c11c1cb181c0e03c00391680,
  unpack 0x400571442f0a21d002b80637c210f84d2cdc20bec340c4700b0faac2163e568c0ea960011000,
  (0x112e8c01460000012010808c002200002e206043b22a808060e30050b48000001438428019 <<< 425),
  unpack 0x460fe60c1f1043a00374083f1021f0982ac81ec01f82aaf858e13831049c7103ee980e23c9403928b0f830416b900,
  (0xa0481830d910000200c58f091 <<< 620),
  unpack 0x29577883271910e62c9cb04ec4c41a8207a240ed001d6601c1f400001ae88660,
  unpack 0x9c07e38801c003ba934e0de48392d4c1fb62af874f038030fe904e3480e9201d2203a61897601034290b87a0,
  unpack 0x4504e20add300380387c782fc594e0a0b800000000,
  (0x30850e11010400031000d34644000000821 <<< 582),
  unpack 0xd0638e9c244392a709832ccca07c2e6601a3e04938024fa4807d76a96a901c3a301443d01e40,
  unpack 0x51a971462e9a01cd40e7f0421d898abc81e8c13862af87c71faaa890cffa6101d00c003680190e1d180,
  unpack 0x2800b8e0b7fe7cf330910f88a9481ec313822af84831f807876804e1041e9601da803a10008620071880,
  unpack 0x1855f941975800e64c41878c76441caa303e128c670051fb6c59a5d2c03a840704bb000073c10300,
  unpack 0x10817942974d00fc6f85e602f32df9e27b5c785d51a49073ab0000000]

private def t31 : Array ℕ := #[
  unpack 0xc11de78a1e30039201c7f91851c00f4785f6d8012bb23a020e38f0e1c01d2b0381c478a027052082f0fa0000,
  unpack 0x4705e00cde10439020be1007c260f3a307fa18c927ab4201c6987d3003ad60701847000000,
  (0x448b19930010011010c107 <<< 626),
  (0x841 <<< 708),
  (0x1c89658600000801481 <<< 647),
  unpack 0x28b70414f9221d003b938639f1983cc16174900e638aeecf618f283c68075280e0309e0000840,
  unpack 0x8c6f92097d410e64d0107e388f1044e5840f6485f6188a2f805870920e3c53f1c01dc303aa5e200288000,
  unpack 0x325fb569201c50045f0a09c4113ad980a3fb8600cfee120e28c1f8401de1038100b66211800,
  unpack 0xc40be5045ee9f201cde3c47e13252074046f084d3bbb36900e3880ff6d090381407e200388000,
  unpack 0xa41ae20e5d3043f134026f8021d9106cf8e07d866080e0183d208383387e78077240e0654e009060ca8900,
  (0x808c0493 <<< 682),
  unpack 0x32272c16ea021c003ba00378b19e2089c1c7411fdad348e01e3ca0938934fe40075ac0e84000dc400,
  unpack 0xc41de3889f2003928047d1833841ad20780c6f08821783c001c0000000,
  (0xc60a1416cd1040004060cf11000000024e403 <<< 572),
  unpack 0x618072864e2821d00338043fc319ec8a3881dc403ea900aecc49070a20ffb6ea9000000,
  unpack 0x1389f1462e8821d001ba022f0f1cec8831c40fa50dc3d00000a8340]

private def t32 : Array ℕ := #[
  0,
  unpack 0x3855b8e027d800e8019d028fa10af034812176800e50caeeb604e0e9201cc103a94480e1d180000,
  unpack 0x2009f2006fb201d002b8073fcb14e48a3c01e041fb400759847707caddc7807db6806016cc4a30c80,
  unpack 0x2201f1842fd4cc9a041fcf05e2089c3401e4013f6b08e3f00b0f8201c1143c3803b820703847c400711c800,
  unpack 0x9c3b8e2979d00e8015c019ba008f0835040fa403ca403b851bbabe004e14c2e9201dca03a99ec300b03824183000,
  unpack 0x1c087c401bec8872168083c3453e33051103b8e07d86e2600e1e80138210be7007e50cd8083800000,
  unpack 0x21063883b79100fc4dc9a404f2441a920731c3fdac6291d95f130030f0700e6501c000000,
  (0x27 <<< 712),
  unpack 0x460dcb0dbc6887400ce8189f3c37882270b2079181f70de101de800000420,
  unpack 0x823bc501b8e087e50097e30a762620f29d103f4900ef105e00e3c24938b0cbe3007dc684000c2c00,
  (0x844d0c32441001800032050010000081 <<< 586),
  unpack 0x190038c087dc00fca0227020cf8cc1881e800fc25343ee80000000,
  unpack 0x19378e3974900e0064f9409c41138b52ec41f96289dc1811c7f100398607433e76000a8080,
  unpack 0x821be6069c5443f130063e021bd898b96ec50fdad308e0161d2493862cbe50077280e8400261800,
  unpack 0xc44ee2829e5043a00770066e1a29c9106ac81e4717b480710437507f6cc8fe5b90070384f82618300e219003800,
  unpack 0x6641e5849fd19280c7d0c23e220f91082e5201d871dd94820e2c00feb0407008a7d860160700000]

private def t33 : Array ℕ := #[
  unpack 0x6f9e1075400e64d020be58a71044ec74817b40073041700c1fcac1083f0803b8407420000b40,
  (0x1093d30db54410001028e3840411000012101c3 <<< 566),
  unpack 0x5fec0e5f2998be160c33c9151103b983fe4c007dd1c49070841f0000000,
  unpack 0x9561db848874006e0187e3017b22a700700c4e01000000032,
  unpack 0xe54ae38a1f440390093c002f1044e0ad007c182fdaca50dd41d0927583cc00eecc0e01c0020006a,
  unpack 0x20463b6397a4642d030387807c6620ed9a80270000000024,
  (0x438f12022c80200520128208882200012b2000039 <<< 557),
  0,
  unpack 0x13a0f4426fb021d003b90863b13057903a0e0f2900e914ae0063f5101178b00e6481c0e01c002000a8,
  unpack 0x3813fac007e485a0637040de2089c41a70072242fd0d830bc0147b0027045078c00e8581d50c00200168,
  unpack 0x146bfd3103fa3317caf3c738a801dc707f6b00237546d001c5101c000000830,
  (0x728c1a0a28082007004022004182007 <<< 597),
  unpack 0x20a471c44e3201f89a062f8810ec838f141784e003d5f408a7ea199407010c76040e2e9cc3f790000,
  unpack 0x10c99c6113a280734038bc30ef9300e01c5fa9d863fe5c407c0147e09271a1178300e1581c0a0be99922c820bfcb0290e0000,
  unpack 0x10abbce00b8a80721681cbe1467b220fb19880f6900e8280eafa3141b12db2d20000,
  unpack 0xcabfce153e434006e0185d2467c980700e0ea881e060bdc36145f00f1f5001c6865e28039500751b0405ea4c00000]

private def t34 : Array ℕ := #[
  unpack 0x8439cb093ca8072168181d3c37e22ca840df53a24290075232140e12cc0000,
  unpack 0x19077962a7c468015d0097c18ef6262dd39341e9201d8211d01c23c22f0e01f50082f5500e010570c80fdac0000,
  unpack 0x18601c9013868873168089d0c538519227b867000e01c3ff98e04fa68075a40e0515e4281c916a80000,
  unpack 0x82adce08b82887326800fd3053e3306e58880feb63340ec8d04838030ff5b3a80e0105e6009c16a180000,
  unpack 0x308af0830f68a8085f0827b220c69039923f6900e828be0161fa01389007fd332c0e030deaa01c307c80000,
  unpack 0x461de5805f29a00674023f9c03d910752fc21fb40075161f00e0ed241c09e5e3403956070300fa660168700000,
  unpack 0x1891f9a237f47c2c10c11e2089c11840e448df61b4a0780707fb61403ff0dca038000d400,
  unpack 0xc64ce2089c544398b00e1e8613d898834a00e678fe108e4f56d58e10fc60077660700e0010000,
  (0x8c0880895400003900921 <<< 634),
  (0x862248e13 <<< 683),
  0,
  (0x190781158304100000001 <<< 638),
  unpack 0x840de3009d2443f135079029f0988397cd0b94807190670070e4049c5047d1c0399407000000a64,
  unpack 0xcc1dc504ba20872502138782fc441872073347f70c471dc0147f01071a70fe4c803a61e201104800,
  unpack 0x35be6889c5043f1b00a1f082bc9106b401c43179480770c3f0071e9201c6185ee9ad2074a00c8000,
  unpack 0x46b1c8153b8da0307ca1cec8831e00ea301f6d9853380707c020e1870e8c01da203a8de2003886400e02e98]

private def t35 : Array ℕ := #[
  unpack 0x6383fa7e98a8143d00278822716e98841785279bdc1d0827147970d00eb481d0cf6180581c12001c8,
  unpack 0x2ad72030f8cf85a011f0b09f887803b980f6800e91cee0063c2493b50000000,
  (0x412f9e1b4c2000032021c40288220000222060e2208000003040007 <<< 501),
  (0xc31334140d00000040038e1000400001060063 <<< 568),
  (0x61e20c92a00001c00c39 <<< 635),
  (0x39d <<< 710),
  (0x200b28109d1040000064cf19 <<< 624),
  (0x29850515865 <<< 678),
  unpack 0x802b842971910e4a042f4a09f88831600e820bf91041700d1ed009c0145e61b80070000c5800,
  unpack 0x10a03c409384887400ae00c5f3847b13630703c4109ea0fa4038120ba78073040e0701e0168000,
  unpack 0x8211c1053cea07400ee800bf2c07b13106b001d8903f6b6144767f98628bf5bd66a36001a800,
  unpack 0x814f9c0b71050fc4f94a14f8cc54840f258fda4038480ba20938a383858076ac0ea060190000,
  unpack 0x4614e60e9e2443f0b707822bf11074cfcd07dc33080f76d1a317c200f8ec029bfb5800000,
  unpack 0x28d3b982278c10e7578a13c5c40f470ffa184c27bb3b2624c2fe984070128f4404e1ae8d3cdb9000,
  unpack 0x4081f2474faa21c90023f8801d91076d92270ce3380707e2610d1f72de10380137a80271c5d9be40000,
  unpack 0x8446e18e5e3443a00674067f1831f098b8cf821bc23180ea86283625b61cb60000]

private def t36 : Array ℕ := #[
  unpack 0xe34ae288df74038007700e5f9621d89883e674685ca40384233abd241c18a1ff9950070280fd2601504000,
  (0x5 <<< 230),
  unpack 0x1ce2bc9103ca007e2600c3c0817e13156903884372c6378030fa104e0831f6bc6070028f7000e01f8c000,
  unpack 0xe3fc408be534006e0147d346788227155803e0e074900ea382e0922c23e1a40e807a4c00400d38000,
  unpack 0x6150e82f2192008fc3433924600f4083da403b433bbbc85303d3aed52c00308000,
  unpack 0x14cbdc60db8e007400eee4d1407e1372c603f6da060380787a020ec160e01d610381c67a80270050000,
  unpack 0x8154e7805d244398b4047e062bf1079e082fb0ce401d01e49070e19f0d00e7481c00b9c03230000,
  (0x10a0808e12200001c00060e30000000023080a10ad0000001851 <<< 515),
  (0x30938309b14410019 <<< 654),
  unpack 0x4e1bc205bce007316e8586f1044ee78903a480741867507fcc0000000,
  unpack 0x3140f983170d00e001dc018786807c41481e4607dc37840707d0000008422,
  unpack 0x8e31c308bca087e2601c3e2c33922ae207b382f0943238058f6020e20d0e1a01f99a900081858052,
  unpack 0x1000000004,
  0,
  unpack 0x212470856e2a21cd40a3f9e21f198b8cf4817f5b38427547d049c50c1fe9816074b35080e01104aa021f8c,
  unpack 0x420fe7005e1443f2810df30239220e5981427e86e148e00a3da0038a3c3868075880ea96001644c30048]

private def t37 : Array ℕ := #[
  unpack 0x5001f3422e9021d002bf3122bf198bccd4d0ba480718e5f547b6c6887f0c03b50074031104e18300000,
  unpack 0xccb3ed5e6007e2680cff043381ec6db65043eecfa493813cbc68073ac0e0054e0090000,
  (0x7091c004d00400240c5061 <<< 628),
  unpack 0x1ce87c500bac007400eee2e2043e20832075207fd6ca093c01c3d41071e48f858803808479280725161f060000,
  (0x8e86000c802007 <<< 657),
  unpack 0x31c07981275410fc6c018fc182fc414640ea181c02000006ba00,
  unpack 0x4326f0846f1821d001ba071f4b10e1063801cc00ff6b68300e0f8009c69a3e3003a52074225d801b72c00,
  (0x220c82102c880004203 <<< 645),
  0,
  unpack 0x38970c52eb201f89f0b8109e2089c54c00e470bf6198c2fba34900e1ce1f9e01f2da55480e1d184400077f400,
  unpack 0x5386f2c60fa821c56060e01c90799f3a9433ba032024e2023f1a01d4a03a81805a25d800,
  unpack 0x1957f982a75410e6a0727c905ec4c5b66620fee188033b3c249c18a3c3403ac2071a001e800,
  unpack 0x6150e200dd70039a00c3c1073b220f25f060fb4e50dd5a104e6738039c4070384712ec3215000,
  unpack 0x8173903975910e001dc029fa58a71044e20d1903a882760c5f68f0a2fb3c86103d432880e0750eea83c03d53b000,
  unpack 0x21173820378510e8015c010fc086f028c81f4a1784e2fb46e491d41b09071a21f4300ed581c0e81cc18bf835008e00000,
  unpack 0x1468bf69c6807340217c702f62620c4903f1c2769c5f68c0f1f80787c904e0452f8c01ed022ef7005e38bb368301c0aa4048e000]

private def t38 : Array ℕ := #[
  unpack 0x1c62bc518be2680617c610ec4c50e00f8283e16180707d00ed600000,
  unpack 0x19c178e3175510e8015d0313a408f6260ab207c001fa90c2fad58424be08071ac0e0304e25d820027fa000,
  unpack 0x3883f9e2078500e8015c0293a604fc414a00e248bfb58441780687c100e607f2d4a0380d1390a0708762b00c1c000,
  unpack 0x38d5f822b78900fc6d039fe504fc260d4b53c4e838bed1d985757a49395f52a038d7541e00b001c000,
  unpack 0x235be7849ee990b4066e101bf198a8881d0117dae206e0063da0838320fe78076ac0e08a27087604005b8000,
  unpack 0x72077db79221cc9805270910e48a9c01dcc0f948071960700b1fa4c20c1d3803dcb0204fa4006e98000,
  unpack 0x111439e0974900e64d0383a6087641c70d0ba0e2fb47a00dd9e920e34c1fd0ca30380d23b2a0f01c8000,
  unpack 0x4406e78ade1043a005740e7f1e01f09b1a3c6f094923aa32820e14f2ff4d6a038187792a0725da1d9d0000,
  0,
  unpack 0x1091386337cb6800dd49878876451a00ee407da403acc2ba83f47183f3403a94070001a8054b287017,
  unpack 0x538371026e2221c018fd1c63b21640fe681f57142f00f1ec009c69c5f0c03b82075336020e0020d40280c13,
  unpack 0x63097d669a01d00338060f450ce48835e00f0209e16820f5071049c69c5e3803f2866c041c000002c3047,
  unpack 0x6541e4849d7003f1b40e4e9611d915110389a07b5e68fdd1c2b0a10fa96e081c0e81d808380083516854a0c23,
  unpack 0x424ce3809f4443928043e003788227142903a9e276900ef280ecaf84938d30fdcb5040e0740ec041c0041a8b42a504907,
  unpack 0x12571434039242d3863e13156903e1637ed66247e0063e1120974e00ec401c0611d5013829041787d050031f81e2c4524015e10,
  0]

private def t39 : Array ℕ := #[
  unpack 0xa71ee6009d3403f0b4067e141bc4113829881f61da83c8e01c3d518187c900e6081c0a03f89862f45c3e6c105ab72a2662e90,
  unpack 0x2414e10e5e1403f134027f0e19f1982b881c0703f43498575064241c5101d3003ac00741bca61ae8d050031f81e268245f5b0,
  unpack 0x18e35d05a28073834f05e2089cbc01dc607dc368a17656d209c0063c3403a500701887e4020063f03c596dc912710,
  unpack 0x31c17920274c00e42d010ba180f6455a00ec4ed1006f767c4c7187f3003bb30204f000832db9524415f50,
  unpack 0x720372042eaa21f89a02170818f8829481d89ec34966f348270611730607038070006331041e00,
  unpack 0x1738c107d000e2a0607470df8cc15240e4501f56900f406c009c70a7e61a840704bb000d007b042e00,
  0,
  unpack 0x5328f0c64fb021c951744f1046803cb0b4a3baa38260032f30dea03a50003711c08e00,
  unpack 0x10a9f2024e2a01f85ab1603f0982b881c4113a480720e0f00a1f64c1967d1403b96070184f0005b31850e00,
  unpack 0x8348e7049ff9a00674044f9421f09b25d8407b40385d81e4027061074b00ee001c0000c2079020e00,
  unpack 0x3184b8a0b7478db2b4d08ecb2dc042f6900e3187e00a3d049386247a600752c0e0441f880091e86000,
  unpack 0x650ae1841d1e26814fc3033e3307207d2c6fb6c2305c0287c01270c687ce00e3401c0e8bf29bb5cb6c396c1560463ca000,
  unpack 0x3957790297b462f130e04ec4c55600e4783fa19860b8050ff5618d0f9c01d090380877e24b6c396c1560463d2000,
  0,
  unpack 0x2351e28e5d600398b0026e9c01c41138b4cc070ba480710c6700b0fdad68e13800ea06001423ec6000,
  unpack 0x70ad70872f1801f94026e1433c9069f385f6a013ba83e104e0c31f8601dd40300560423ea000]

private def t40 : Array ℕ := #[
  unpack 0x43a972c20e3801d001ba0227c91ce1558039060f6900e91cfea0ca49386207f53ec60415fc0d4985280afe0c0000,
  unpack 0x120af1c72f08c003b8023f8910ec4c5a97668bf57087f7679001c6041fa1b0607008af3404e18b7368305c0000,
  unpack 0x18d2beab9510fc2d89860476415240f2607f6da8607aa3e804e2853f1c01ce203809339a02700a0bea8709c0000,
  unpack 0xcc09c319bc0887150213a084f1044e2a5007b146e9201d869bc03c7a08270878f4600e5101c0c1bd4417a93010572c02f0411c0000,
  0,
  unpack 0x256e58e5ed19d9c580725d4fcc1ff4361e27707d209c59e1c34039c00704bbd772ac0000,
  unpack 0xc306f84d6043a00775b88a2c81c8517b080769e6f7661049c1121ea58920702a875505ff0c00000,
  unpack 0x20ee10c1f21928083c2047e33107d8dc41bb0807586475479241c11a3fe981607018675505ff2c00000,
  unpack 0x19947962171110e6a0137cd10ec8b2d001feb6d1c5e01a3fa1861c794a0380957b202fa400000,
  unpack 0x12871416e3801d0033a053f0218ec82a801e4c0fdc330c6f00e1e1049c2141fe9cb302a4fc67f6c00000,
  unpack 0x14aafcf053c8087007378a10e1063801f450b9480749b4069249c21c3ea589607018afc67f8c00000,
  0,
  unpack 0x18037cd10b8a807326c4f1013b13106a801dc61fb0807402270061fb0c5923c30478000000,
  unpack 0x3057f9a197d110e48021f4114ec4d72c0613a480718e274078249c39c7d044b8000000,
  unpack 0x63a373842f9021c85b834409f84c10640f8687fa1a09a35041c3905c0c138000000,
  unpack 0x28c638a1a71d00fc2d008fe708f1044e4e00e468bf5710570091f5009c3045d30238000000]

private def t41 : Array ℕ := #[
  0,
  unpack 0x96fe8b4510e64d0383c284fc43081fce13edb2822f5071041c08e7f24838000000,
  unpack 0xe712e18e1ea1f130025f983bd907a5e1017e866746f080000000,
  unpack 0x438ef3036f9201d002bf2bc81cec8352c0607da704cf280000000,
  (0x1003c008954000030008f18044010000c3000ce01240000034d281 <<< 506),
  unpack 0x4a17cf0d3d43e26804fe1c33e3305710380e07e86930af680000000,
  unpack 0x14601ce083ec807000ee014dd1c63b2a5011bc20444f880000000,
  unpack 0x1846f821b7ba60061f9023c20ea5906276800eb547fa80000000,
  (0xa54b10165c10000600a0c604004000015a01 <<< 576),
  (0x60ac9c00440820052001228a00220000af29 <<< 577),
  (0x884cf18874010028009234700110000d411 <<< 578),
  (0x108b668c93a00800c0149021220000002803 <<< 579),
  0,
  (0x71801c00648800010003448288020000281 <<< 581),
  (0xa54b3076cc00400e41 <<< 648),
  (0x12c9a032a08000021 <<< 649)]

private def t42 : Array ℕ := #[
  (0x118104158340100101 <<< 650),
  (0x1869438e9a20000089 <<< 651),
  (0x41062c50540040081 <<< 652),
  (0x2099623040820073 <<< 653),
  (0x1 <<< 720),
  (0x11 <<< 721),
  (0x1 <<< 722),
  (0x1 <<< 723),
  (0x1 <<< 724),
  0,
  (0x651408321910000400c5 <<< 640),
  (0x605824304500400400660f14100400011040a141 <<< 560),
  (0x3 <<< 718),
  (0x4c36500c2a804018814f9e2a2008000630012100c0000000008c0060d000000051 <<< 455),
  (0x1068a15904400000030c1044000000012800031 <<< 562),
  (0x730e161360283 <<< 669)]

private def t43 : Array ℕ := #[
  unpack 0x202a71c64f8821f89b21c33c91063881e0a1bea741240000000,
  unpack 0x1cab1c90dbfbc4d001b86827c26a96800df97af4290075232140e10ec0000,
  unpack 0x3092f982a7c410e28021f0218e2089c418d2079283fdace8900000a8240,
  0,
  unpack 0x2003b8c297c5001ba061f8b15ec821481f85f6b7bb7930000008920,
  (0x72a9 <<< 705),
  (0x2844c31 <<< 694),
  unpack 0x4306e68cdd74438001fa20c70a3c01fc61bedb2885f7069009c20e3e2803a840704bb00000,
  (0x41590c005110400600c34805100400005440b10129000000034b <<< 512),
  unpack 0x1cc19c2183ac887216010fe1847b131719f8827eb62146e880000000,
  unpack 0x2244e2881d644390b40a7f121bc41138aa801c4603da93600e3e15811cbc700702c0e0309e0000440,
  0,
  unpack 0x2bc105baa0874006ee4d3837b220d6803f1437b86b141e8849273a30f00eb481c000000,
  (0x18438d0c130400019031 <<< 642),
  (0x51a08664d <<< 680),
  (0x1021a584c3a008010818f <<< 639)]

private def t44 : Array ℕ := #[
  (0x1 <<< 707),
  0,
  (0x64573c260d18000640454418000400034200c3072800000033 <<< 520),
  unpack 0x13a872472e6a00570007e0429d932a10dfb5bddbc985840e0558f4800000,
  (0x84166040901 <<< 675),
  unpack 0x8501f96e919a80c5e1453882271419038122feb6520cead931a2070000000,
  (0x432d0a21220420032050c40e00220000a3 <<< 585),
  (0x1225003a6a0820012003 <<< 641),
  unpack 0x2600e2825f7403f1b40e2e062bd91699a0e376100e2142e0dab0c30fc500fb6c000000,
  (0x1800a6860a0208000010a8e2000880002b4816204d <<< 555),
  (0x2895 <<< 706),
  unpack 0x11537aa3201d001b8043f8608f8cc15200ec185d840388c0fb03e904e1840feb060703807000000,
  (0xa04d1c548910400c408041 <<< 632),
  0,
  (0x8ab22025280080100089983 <<< 627),
  unpack 0x728cf0442f1801cd40a1f8023c916e5b1e0fed6f760f930b081c0ab1e90620000]

private def t45 : Array ℕ := #[
  0,
  (0xc71d <<< 704),
  (0xc4aa18c43a200008000d8e3200800000bc01 <<< 575),
  (0x108e0009408820022073c58a88220000222061 <<< 569),
  0,
  unpack 0x28947822279800e8019dd5840c7c48481ec007b080768c7700b1f8241c6185fa18000000,
  (0x1 <<< 719),
  (0x23e688d <<< 687),
  unpack 0x391639e0275d00e64f98f05e4b99382fd0da085d51b402700517986e001c000000,
  unpack 0x4f943870d00e62d038ba286fc662a420762c2f6a432fa03c924e24e1fe8000000,
  unpack 0x6165861d2043f0b4043e1421f10d0078105ed201d600dc01c7dc30618fca00ed181c880a275400000,
  (0x130f9201060020062062a48888020001af003081240000001 <<< 525),
  (0x2182c160d10000040630101000400025a00a04109 <<< 552),
  0,
  (0xc78708834410011001e383401 <<< 614),
  (0x430d0c744110400240640309104000025440104060000000018f00c061 <<< 488)]

private def t46 : Array ℕ := #[
  unpack 0x2657ea8a5d1400ee004bd1467e3354b4205e7af40000000,
  (0xa45e1856d11 <<< 676),
  unpack 0x22a2f0c54eb001d001ba2053b22d20080000000,
  (0x62840409 <<< 689),
  (0x5088b61 <<< 693),
  (0x1806d <<< 702),
  unpack 0x309f0476e2a21cc5805374919e482b481f400ba480731e3700f0f4041d6f431a40e0648e4a01c3161115fe5ba0000,
  unpack 0x4204f1c56eaa01f89802374504ec8834600e068df619473f8060f6104e1050f8e01d490381077920270d00000,
  unpack 0x2712e1845e91a005700c1f982bc41138831840e2501ed582770061fd249c4881d0c0394607020a7c494302380000,
  0,
  unpack 0x500d70444f0821f8da040fea6c883cb66409e108c4f6478249c3121e1c66306e081fdc7900000,
  unpack 0x2895f880a79500e8019f90e14ec8abc01c011fec34841f4068249d94f1803b86071a2500000,
  unpack 0x2719f84d10438a8083c2423b220fb1e921f84258fc03c7a48270e3978600e7101d4800418da00,
  unpack 0x402fc70cbd2801dd030bc7047c665c40e8281c1240e00c3d20838000000f4,
  (0x302a0c2a06882003005042808002000185001 <<< 573),
  (0xc0a438cc0820801c80850218008000041081c200d0000001420a00a25 <<< 491)]

private def t47 : Array ℕ := #[
  0,
  (0x60841802448020022013600880220000830000a3a480000049650078009 <<< 485),
  unpack 0x455fe28c087216814ff18778165800b948077020700000000,
  (0x81 <<< 700),
  0,
  unpack 0xf061841c2443a00570085f800bf09a59c9a2f4900ef1c5e0183f20038628bc1807e4000000,
  unpack 0x52a8f1834e1a01cc9a071f8e15e2089dd4f8807a480769857348276230000000,
  (0x3299832060000060061018288000001 <<< 593),
  unpack 0x1c201c308be4887e2600cbd08739208d2075247ed201c4503c0307f48071649fe863501c0229c002e4000,
  unpack 0x104bbc40d3ec087e268049e2827921c40fe40ffa1a45b2c249c30a1f3003bc60701887000000,
  0,
  unpack 0xa749e6085fe9f2808fc1453e2b672587fadbc82bba36800e2070f0a01ca8038818175f40000,
  unpack 0x712772024e8f0b7578a21f116e5d823784a609d5241c1823f1403ebb032a7000000,
  (0x21500d09050410038031014540100000d6002c20c20000003 <<< 526),
  0,
  unpack 0x2156b981a7fc6800dd019b903c26ec7e00dda0039862f8068fc924e3002e0e01dc203a5000000]

private def t48 : Array ℕ := #[
  unpack 0x420df1474f9221f940c5e8631f1047003e802728c1bba34904e141c03b84074a0000050,
  unpack 0x20d379e3a744900c2f1623d9179a244fdac6205dc1f09076e30000000,
  (0x23a702214c8020060063878c08200000ae0001a09480000069 <<< 521),
  (0x5620149500400600064719004000001 <<< 588),
  (0x43a81 <<< 701),
  unpack 0x4023cb11bf2801dd0117a78e764418e207d286e000000c6c00,
  (0x31a89e2a608020072072e1 <<< 633),
  unpack 0x33a9f0c02f68d001bbab0505ecb25e043f3d00000000,
  0,
  unpack 0x28d539a1b71900e801dc038fc080f641ec7c207f528e1700000000,
  unpack 0x801b881b7fb664d028bf9b0834840fe58fda40388b07b34209c50a1f3403a440701887ec600682000,
  unpack 0x2503e3061d700398b4064f8213d9072072301fd6d0195c0147a0907181074500eb181c0a03cd517800000,
  unpack 0x5100f2436f88c8083d3033e33057803e1207b86b142e01a1f24838418f868076a80e0608e4800000,
  0,
  unpack 0x2912b92287fb7c80317c71cf84c3081d8713edb2827f448093a9de18075080e0645fc800000,
  unpack 0x301178a107c8662c0393c50cf023c81fc31fb48070183f7665249c3985f3c03a84070200a8000]

private def tables := #[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48]
private def multiplier (j : ℕ) : ℕ :=
  ((tables[j/16]?.getD #[])[j%16]?).getD 0

private def checkAt (i : ℕ) : Bool :=
  let p := (rowOrder 11 6).symm (Fin.ofNat 726 i)
  fit (fastProduct 1 28 11 6 factors multiplier p.1.val p.2.1.val p.2.2.val) i

private def r8 : RowWindow checkAt 8 := nextWindow (start checkAt) 8 (by decide +kernel)
private def r16 : RowWindow checkAt 16 := nextWindow r8 8 (by decide +kernel)
private def r24 : RowWindow checkAt 24 := nextWindow r16 8 (by decide +kernel)
private def r32 : RowWindow checkAt 32 := nextWindow r24 8 (by decide +kernel)
private def r40 : RowWindow checkAt 40 := nextWindow r32 8 (by decide +kernel)
private def r48 : RowWindow checkAt 48 := nextWindow r40 8 (by decide +kernel)
private def r56 : RowWindow checkAt 56 := nextWindow r48 8 (by decide +kernel)
private def r64 : RowWindow checkAt 64 := nextWindow r56 8 (by decide +kernel)
private def r72 : RowWindow checkAt 72 := nextWindow r64 8 (by decide +kernel)
private def r80 : RowWindow checkAt 80 := nextWindow r72 8 (by decide +kernel)
private def r88 : RowWindow checkAt 88 := nextWindow r80 8 (by decide +kernel)
private def r96 : RowWindow checkAt 96 := nextWindow r88 8 (by decide +kernel)
private def r104 : RowWindow checkAt 104 := nextWindow r96 8 (by decide +kernel)
private def r112 : RowWindow checkAt 112 := nextWindow r104 8 (by decide +kernel)
private def r120 : RowWindow checkAt 120 := nextWindow r112 8 (by decide +kernel)
private def r128 : RowWindow checkAt 128 := nextWindow r120 8 (by decide +kernel)
private def r136 : RowWindow checkAt 136 := nextWindow r128 8 (by decide +kernel)
private def r144 : RowWindow checkAt 144 := nextWindow r136 8 (by decide +kernel)
private def r152 : RowWindow checkAt 152 := nextWindow r144 8 (by decide +kernel)
private def r160 : RowWindow checkAt 160 := nextWindow r152 8 (by decide +kernel)
private def r168 : RowWindow checkAt 168 := nextWindow r160 8 (by decide +kernel)
private def r176 : RowWindow checkAt 176 := nextWindow r168 8 (by decide +kernel)
private def r184 : RowWindow checkAt 184 := nextWindow r176 8 (by decide +kernel)
private def r192 : RowWindow checkAt 192 := nextWindow r184 8 (by decide +kernel)
private def r200 : RowWindow checkAt 200 := nextWindow r192 8 (by decide +kernel)
private def r208 : RowWindow checkAt 208 := nextWindow r200 8 (by decide +kernel)
private def r216 : RowWindow checkAt 216 := nextWindow r208 8 (by decide +kernel)
private def r224 : RowWindow checkAt 224 := nextWindow r216 8 (by decide +kernel)
private def r232 : RowWindow checkAt 232 := nextWindow r224 8 (by decide +kernel)
private def r240 : RowWindow checkAt 240 := nextWindow r232 8 (by decide +kernel)
private def r248 : RowWindow checkAt 248 := nextWindow r240 8 (by decide +kernel)
private def r256 : RowWindow checkAt 256 := nextWindow r248 8 (by decide +kernel)
private def r264 : RowWindow checkAt 264 := nextWindow r256 8 (by decide +kernel)
private def r272 : RowWindow checkAt 272 := nextWindow r264 8 (by decide +kernel)
private def r280 : RowWindow checkAt 280 := nextWindow r272 8 (by decide +kernel)
private def r288 : RowWindow checkAt 288 := nextWindow r280 8 (by decide +kernel)
private def r296 : RowWindow checkAt 296 := nextWindow r288 8 (by decide +kernel)
private def r304 : RowWindow checkAt 304 := nextWindow r296 8 (by decide +kernel)
private def r312 : RowWindow checkAt 312 := nextWindow r304 8 (by decide +kernel)
private def r320 : RowWindow checkAt 320 := nextWindow r312 8 (by decide +kernel)
private def r328 : RowWindow checkAt 328 := nextWindow r320 8 (by decide +kernel)
private def r336 : RowWindow checkAt 336 := nextWindow r328 8 (by decide +kernel)
private def r344 : RowWindow checkAt 344 := nextWindow r336 8 (by decide +kernel)
private def r352 : RowWindow checkAt 352 := nextWindow r344 8 (by decide +kernel)
private def r360 : RowWindow checkAt 360 := nextWindow r352 8 (by decide +kernel)
private def r368 : RowWindow checkAt 368 := nextWindow r360 8 (by decide +kernel)
private def r376 : RowWindow checkAt 376 := nextWindow r368 8 (by decide +kernel)
private def r384 : RowWindow checkAt 384 := nextWindow r376 8 (by decide +kernel)
private def r392 : RowWindow checkAt 392 := nextWindow r384 8 (by decide +kernel)
private def r400 : RowWindow checkAt 400 := nextWindow r392 8 (by decide +kernel)
private def r408 : RowWindow checkAt 408 := nextWindow r400 8 (by decide +kernel)
private def r416 : RowWindow checkAt 416 := nextWindow r408 8 (by decide +kernel)
private def r424 : RowWindow checkAt 424 := nextWindow r416 8 (by decide +kernel)
private def r432 : RowWindow checkAt 432 := nextWindow r424 8 (by decide +kernel)
private def r440 : RowWindow checkAt 440 := nextWindow r432 8 (by decide +kernel)
private def r448 : RowWindow checkAt 448 := nextWindow r440 8 (by decide +kernel)
private def r456 : RowWindow checkAt 456 := nextWindow r448 8 (by decide +kernel)
private def r464 : RowWindow checkAt 464 := nextWindow r456 8 (by decide +kernel)
private def r472 : RowWindow checkAt 472 := nextWindow r464 8 (by decide +kernel)
private def r480 : RowWindow checkAt 480 := nextWindow r472 8 (by decide +kernel)
private def r488 : RowWindow checkAt 488 := nextWindow r480 8 (by decide +kernel)
private def r496 : RowWindow checkAt 496 := nextWindow r488 8 (by decide +kernel)
private def r504 : RowWindow checkAt 504 := nextWindow r496 8 (by decide +kernel)
private def r512 : RowWindow checkAt 512 := nextWindow r504 8 (by decide +kernel)
private def r520 : RowWindow checkAt 520 := nextWindow r512 8 (by decide +kernel)
private def r528 : RowWindow checkAt 528 := nextWindow r520 8 (by decide +kernel)
private def r536 : RowWindow checkAt 536 := nextWindow r528 8 (by decide +kernel)
private def r544 : RowWindow checkAt 544 := nextWindow r536 8 (by decide +kernel)
private def r552 : RowWindow checkAt 552 := nextWindow r544 8 (by decide +kernel)
private def r560 : RowWindow checkAt 560 := nextWindow r552 8 (by decide +kernel)
private def r568 : RowWindow checkAt 568 := nextWindow r560 8 (by decide +kernel)
private def r576 : RowWindow checkAt 576 := nextWindow r568 8 (by decide +kernel)
private def r584 : RowWindow checkAt 584 := nextWindow r576 8 (by decide +kernel)
private def r592 : RowWindow checkAt 592 := nextWindow r584 8 (by decide +kernel)
private def r600 : RowWindow checkAt 600 := nextWindow r592 8 (by decide +kernel)
private def r608 : RowWindow checkAt 608 := nextWindow r600 8 (by decide +kernel)
private def r616 : RowWindow checkAt 616 := nextWindow r608 8 (by decide +kernel)
private def r624 : RowWindow checkAt 624 := nextWindow r616 8 (by decide +kernel)
private def r632 : RowWindow checkAt 632 := nextWindow r624 8 (by decide +kernel)
private def r640 : RowWindow checkAt 640 := nextWindow r632 8 (by decide +kernel)
private def r648 : RowWindow checkAt 648 := nextWindow r640 8 (by decide +kernel)
private def r656 : RowWindow checkAt 656 := nextWindow r648 8 (by decide +kernel)
private def r664 : RowWindow checkAt 664 := nextWindow r656 8 (by decide +kernel)
private def r672 : RowWindow checkAt 672 := nextWindow r664 8 (by decide +kernel)
private def r680 : RowWindow checkAt 680 := nextWindow r672 8 (by decide +kernel)
private def r688 : RowWindow checkAt 688 := nextWindow r680 8 (by decide +kernel)
private def r696 : RowWindow checkAt 696 := nextWindow r688 8 (by decide +kernel)
private def r704 : RowWindow checkAt 704 := nextWindow r696 8 (by decide +kernel)
private def r712 : RowWindow checkAt 712 := nextWindow r704 8 (by decide +kernel)
private def r720 : RowWindow checkAt 720 := nextWindow r712 8 (by decide +kernel)
private def r726 : RowWindow checkAt 726 := nextWindow r720 6 (by decide +kernel)

theorem spans : CriticalTensor.Spans 6 11 11 28 := by
  apply from_bits (g:=1) (s:=28) (d:=11) (a:=6) factors multiplier
  intro i
  have ok := r726.verified i.val i.isLt
  have hi : Fin.ofNat 726 i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simpa only [checkAt,hi] using ok

end CriticalTensor.SixBase.Eleven

namespace CriticalTensor.SixBase

theorem base_eleven : CriticalTensor.Spans 6 11 11 28 := Eleven.spans

end CriticalTensor.SixBase

namespace CriticalTensor.SixBorder

def outsideOnly {D : Type} (f : Fin 2 → ℂ) : Fin 2 ⊕ D → ℂ := Sum.elim f (fun _ => 0)
def insideOnly {D : Type} (f : D → ℂ) : Fin 2 ⊕ D → ℂ := Sum.elim (fun _ => 0) f
def edge {D : Type} : (Fin 2 ⊕ D) → (Fin 2 ⊕ D) → Prop
  | Sum.inr _, Sum.inr _ => False
  | _, _ => True

def Holds {D W X N Q : Type} [Fintype X] [Fintype N] [Fintype Q]
    (a b : X → (Fin 2 ⊕ D) → ℂ) (c : X → W → ℂ)
    (ai bi : N → D → ℂ) (ci : N → W → ℂ)
    (aq bq : Q → (Fin 2 ⊕ D) → ℂ) : Prop :=
  ∀ T : (Fin 2 ⊕ D) → (Fin 2 ⊕ D) → W → ℂ,
    ∃ u v : X → (Fin 2 ⊕ D) → ℂ, ∃ w : X → W → ℂ,
      ∃ ui vi : N → Fin 2 → ℂ, ∃ wq : Q → W → ℂ, ∀ i j k, edge i j →
        T i j k =
          (∑ t, (u t i * (b t j * c t k) + a t i * (v t j * c t k) + a t i * (b t j * w t k))) +
          (∑ t, (outsideOnly (ui t) i * (insideOnly (bi t) j * ci t k) +
            insideOnly (ai t) i * (outsideOnly (vi t) j * ci t k))) +
          ∑ t, aq t i * (bq t j * wq t k)

/-- The exterior part of one group of slices. The points in X have three
free factors. Points in N lie in the inner block, and those in Q contribute
only their third-factor variations to this pencil. -/
def PencilFor (D W X N Q : Type) [Fintype X] [Fintype N] [Fintype Q] : Prop :=
  ∃ a b : X → (Fin 2 ⊕ D) → ℂ, ∃ c : X → W → ℂ,
    ∃ ai bi : N → D → ℂ, ∃ ci : N → W → ℂ,
    ∃ aq bq : Q → (Fin 2 ⊕ D) → ℂ, Holds a b c ai bi ci aq bq

end CriticalTensor.SixBorder

namespace CriticalTensor.SixBorder

lemma pencil_transport {D W X N Q E Y S R : Type} [Fintype X] [Fintype N] [Fintype Q]
    [Fintype Y] [Fintype S] [Fintype R] (ed : E ≃ D) (ex : Y ≃ X) (en : S ≃ N) (eq : R ≃ Q)
    (h : PencilFor D W X N Q) : PencilFor E W Y S R := by
  obtain ⟨a,b,c,ai,bi,ci,aq,bq,hs⟩ := h
  let ez := Equiv.sumCongr (Equiv.refl (Fin 2)) ed
  have ho (f : Fin 2 → ℂ) (i : Fin 2 ⊕ E) : outsideOnly f (ez i) = outsideOnly f i := by
    cases i <;> rfl
  have hi (f : D → ℂ) (i : Fin 2 ⊕ E) :
      insideOnly f (ez i) = insideOnly (fun s => f (ed s)) i := by cases i <;> rfl
  refine ⟨fun y i => a (ex y) (ez i),fun y i => b (ex y) (ez i),fun y => c (ex y),
    fun z i => ai (en z) (ed i),fun z i => bi (en z) (ed i),fun z => ci (en z),
    fun z i => aq (eq z) (ez i),fun z i => bq (eq z) (ez i),?_⟩
  intro T
  obtain ⟨u,v,w,ui,vi,wq,hT⟩ := hs fun i j k => T (ez.symm i) (ez.symm j) k
  refine ⟨fun t i => u (ex t) (ez i),fun t j => v (ex t) (ez j),fun t => w (ex t),
    fun t => ui (en t),fun t => vi (en t),fun t => wq (eq t),?_⟩
  intro i j k he
  have hh : edge (ez i) (ez j) := by cases i <;> cases j <;> exact he
  have hT := hT (ez i) (ez j) k hh
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hT
  rw [hT]
  congr 1
  · congr 1
    · exact (ex.sum_comp (fun z => u z (ez i) * (b z (ez j) * c z k) +
        a z (ez i) * (v z (ez j) * c z k) + a z (ez i) * (b z (ez j) * w z k))).symm
    · have hsum := en.sum_comp (fun z => outsideOnly (ui z) (ez i) * (insideOnly (bi z) (ez j) * ci z k) +
        insideOnly (ai z) (ez i) * (outsideOnly (vi z) (ez j) * ci z k))
      simpa only [ho,hi] using hsum.symm
  · exact (eq.sum_comp (fun z => aq z (ez i) * (bq z (ez j) * wq z k))).symm

end CriticalTensor.SixBorder

namespace CriticalTensor.SixBorder.Pencils

abbrev Coord (D : Type) := Fin 2 ⊕ D
abbrev Rows (D W : Type) := {z : Coord D × Coord D × W // edge z.1 z.2.1}
abbrev Cols (D W X N Q : Type) :=
  (X × (Coord D ⊕ (Coord D ⊕ W))) ⊕ ((N × (Fin 2 ⊕ Fin 2)) ⊕ (Q × W))

def matrix {D W X N Q K : Type} [CommRing K] [DecidableEq D] [DecidableEq W]
    (a b : X → Coord D → K) (c : X → W → K)
    (ai bi : N → D → K) (ci : N → W → K) (aq bq : Q → Coord D → K) :
    Matrix (Rows D W) (Cols D W X N Q) K
  | ⟨(i,j,k),_⟩, Sum.inl (t,Sum.inl h) => if h=i then b t j * c t k else 0
  | ⟨(i,j,k),_⟩, Sum.inl (t,Sum.inr (Sum.inl h)) => if h=j then a t i * c t k else 0
  | ⟨(i,j,k),_⟩, Sum.inl (t,Sum.inr (Sum.inr h)) => if h=k then a t i * b t j else 0
  | ⟨(i,j,k),_⟩, Sum.inr (Sum.inl (t,Sum.inl h)) =>
      if Sum.inl h=i then j.elim (fun _ => 0) (bi t) * ci t k else 0
  | ⟨(i,j,k),_⟩, Sum.inr (Sum.inl (t,Sum.inr h)) =>
      if Sum.inl h=j then i.elim (fun _ => 0) (ai t) * ci t k else 0
  | ⟨(i,j,k),_⟩, Sum.inr (Sum.inr (t,h)) => if h=k then aq t i * bq t j else 0

lemma action {D W X N Q : Type} [Fintype W] [Fintype D] [Fintype X] [Fintype N] [Fintype Q] [DecidableEq D] [DecidableEq W]
    (a b : X → Coord D → ℂ) (c : X → W → ℂ) (ai bi : N → D → ℂ) (ci : N → W → ℂ)
    (aq bq : Q → Coord D → ℂ) (y : Cols D W X N Q → ℂ) (i j : Coord D) (k : W) (e : edge i j) :
    (matrix a b c ai bi ci aq bq).mulVec y ⟨(i,j,k),e⟩ =
      (∑ t, (y (Sum.inl (t,Sum.inl i)) * (b t j * c t k) +
        a t i * (y (Sum.inl (t,Sum.inr (Sum.inl j))) * c t k) +
        a t i * (b t j * y (Sum.inl (t,Sum.inr (Sum.inr k)))))) +
      (∑ t, (outsideOnly (fun h => y (Sum.inr (Sum.inl (t,Sum.inl h)))) i * (insideOnly (bi t) j * ci t k) +
        insideOnly (ai t) i * (outsideOnly (fun h => y (Sum.inr (Sum.inl (t,Sum.inr h)))) j * ci t k))) +
      ∑ t, aq t i * (bq t j * y (Sum.inr (Sum.inr (t,k)))) := by
  change (∑ z : Cols D W X N Q, matrix a b c ai bi ci aq bq ⟨(i,j,k),e⟩ z * y z) = _
  cases i <;> cases j <;>
    simp [Fintype.sum_sum_type, Fintype.sum_prod_type, matrix, outsideOnly, insideOnly, ite_mul,
      Finset.sum_ite_eq', Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm, add_assoc]

lemma holds_iff {D W X N Q : Type} [Fintype W] [Fintype D] [Fintype X] [Fintype N] [Fintype Q] [DecidableEq D] [DecidableEq W]
    (a b : X → Coord D → ℂ) (c : X → W → ℂ) (ai bi : N → D → ℂ) (ci : N → W → ℂ)
    (aq bq : Q → Coord D → ℂ) :
    Holds a b c ai bi ci aq bq ↔ Function.Surjective (matrix a b c ai bi ci aq bq).mulVec := by
  classical
  constructor
  · intro hh T
    let lift (i j : Coord D) (k : W) := if e : edge i j then T ⟨(i,j,k),e⟩ else 0
    obtain ⟨u,v,w,ui,vi,wq,hT⟩ := hh lift
    let y : Cols D W X N Q → ℂ := Sum.elim (fun z => z.2.elim (u z.1) (Sum.elim (v z.1) (w z.1)))
      (Sum.elim (fun z => z.2.elim (ui z.1) (vi z.1)) (fun z => wq z.1 z.2))
    refine ⟨y, ?_⟩
    funext z
    obtain ⟨⟨i,j,k⟩,e⟩ := z
    exact ((action a b c ai bi ci aq bq y i j k e).trans (hT i j k e).symm).trans (dif_pos e)
  · intro hh T
    obtain ⟨y,hy⟩ := hh fun z => T z.1.1 z.1.2.1 z.1.2.2
    refine ⟨fun t i => y (Sum.inl (t,Sum.inl i)),fun t j => y (Sum.inl (t,Sum.inr (Sum.inl j))),
      fun t k => y (Sum.inl (t,Sum.inr (Sum.inr k))),fun t i => y (Sum.inr (Sum.inl (t,Sum.inl i))),
      fun t j => y (Sum.inr (Sum.inl (t,Sum.inr j))),fun t k => y (Sum.inr (Sum.inr (t,k))),?_⟩
    intro i j k e
    exact (congrFun hy ⟨(i,j,k),e⟩).symm.trans (action a b c ai bi ci aq bq y i j k e)

end CriticalTensor.SixBorder.Pencils


namespace CriticalTensor.SixBorder.Tiles

/-- The exterior parts of the active points are prescribed so that the same
points can serve an arbitrarily large number of independent interior rows. -/
def Anchored {D Wh X N Q : Type} [Fintype X] [Fintype N] [Fintype Q]
    (A B : X → Fin 2 → ℂ) (C : X → Wh → ℂ) : Prop :=
  ∃ ax bx : X → D → ℂ, ∃ ai bi : N → D → ℂ, ∃ ci : N → Wh → ℂ,
    ∃ aq bq : Q → (Fin 2 ⊕ D) → ℂ,
      Holds (fun t => Sum.elim (A t) (ax t)) (fun t => Sum.elim (B t) (bx t)) C ai bi ci aq bq

def Limb {D Wh X N V : Type} [Fintype X] [Fintype N] [Fintype V] (O : X → Fin 2 → ℂ)
    (C : X → Wh → ℂ) (a : N → D → ℂ) (ci : N → Wh → ℂ) (b : V → D → ℂ) (f : V → Fin 2 → ℂ) : Prop :=
  ∀ T : D → Fin 2 → Wh → ℂ, ∃ u₀ : X → D → ℂ, ∃ u : N → Fin 2 → ℂ, ∃ v : V → Wh → ℂ,
    ∀ i j k, T i j k =
      (∑ t, u₀ t i * (O t j * C t k)) + (∑ t, a t i * (u t j * ci t k)) +
      ∑ t, b t i * (f t j * v t k)

def Paired {D Wh X N V : Type} [Fintype X] [Fintype N] [Fintype V] (A B : X → Fin 2 → ℂ)
    (C : X → Wh → ℂ) : Prop :=
  ∃ ai bi : N → D → ℂ, ∃ ci : N → Wh → ℂ, ∃ aq bq : V → D → ℂ, ∃ f g : V → Fin 2 → ℂ,
    Limb B C ai ci aq f ∧ Limb A C bi ci bq g

lemma to_pencil {D Wh X N Q : Type} [Fintype X] [Fintype N] [Fintype Q]
    {A B : X → Fin 2 → ℂ} {C : X → Wh → ℂ} (h : Anchored (D:=D) (N:=N) (Q:=Q) A B C) :
    PencilFor D Wh X N Q := by
  obtain ⟨ax,bx,ai,bi,ci,aq,bq,hs⟩ := h
  exact ⟨_,_,C,ai,bi,ci,aq,bq,hs⟩

lemma repeat_limb {D Wh X N V : Type} [Fintype X] [Fintype N] [Fintype V]
    {O : X → Fin 2 → ℂ} {C : X → Wh → ℂ} {a : N → D → ℂ} {ci : N → Wh → ℂ}
    {b : V → D → ℂ} {f : V → Fin 2 → ℂ} (L : Type) [Fintype L] [DecidableEq L] (h : Limb O C a ci b f) :
    Limb O C (fun (z : L×N) (i : L×D) => if z.1=i.1 then a z.2 i.2 else 0) (fun z => ci z.2)
      (fun (z : L×V) (i : L×D) => if z.1=i.1 then b z.2 i.2 else 0) (fun z => f z.2) := by
  classical
  intro T
  choose u₀ u v hv using fun l : L => h fun i j k => T (l,i) j k
  refine ⟨fun t i => u₀ i.1 t i.2,fun t => u t.1 t.2,fun t => v t.1 t.2,?_⟩
  rintro ⟨l,i⟩ j k
  simpa [Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel] using hv l i j k

lemma repeat_paired {D Wh X N V : Type} [Fintype X] [Fintype N] [Fintype V]
    {A B : X → Fin 2 → ℂ} {C : X → Wh → ℂ} (L : Type) [Fintype L] [DecidableEq L]
    (h : Paired (D:=D) (N:=N) (V:=V) A B C) : Paired (D:=L×D) (N:=L×N) (V:=L×V) A B C := by
  obtain ⟨ai,bi,ci,aq,bq,f,g,ha,hb⟩ := h
  exact ⟨_,_,_,_,_,_,_,repeat_limb L ha,repeat_limb L hb⟩

lemma append {D E Wh X N Q M V : Type} [Fintype X] [Fintype N] [Fintype Q] [Fintype M] [Fintype V]
    {A B : X → Fin 2 → ℂ} {C : X → Wh → ℂ}
    (base : Anchored (D:=D) (N:=N) (Q:=Q) A B C) (arms : Paired (D:=E) (N:=M) (V:=V) A B C) :
    Anchored (D:=D⊕E) (N:=N⊕M) (Q:=Q⊕(V⊕V)) A B C := by
  obtain ⟨ax,bx,ai,bi,ci,aq,bq,hs⟩ := base
  obtain ⟨al,bl,cl,rl,sl,f,g,hl,hr⟩ := arms
  let lower (z : Fin 2 ⊕ D) : Fin 2 ⊕ (D⊕E) := z.elim Sum.inl (fun i => Sum.inr (Sum.inl i))
  let extend (t : (Fin 2⊕D) → ℂ) : Fin 2 ⊕ (D⊕E) → ℂ :=
    Sum.elim (fun j => t (Sum.inl j)) (Sum.elim (fun j => t (Sum.inr j)) (fun _ => 0))
  let eg (v : E → ℂ) : Fin 2 ⊕ (D⊕E) → ℂ := insideOnly (Sum.elim (fun _ => 0) v)
  refine ⟨fun t => Sum.elim (ax t) (fun _ => 0),fun t => Sum.elim (bx t) (fun _ => 0),
    Sum.elim (fun t => Sum.elim (ai t) (fun _ => 0)) (fun t => Sum.elim (fun _ => 0) (al t)),
    Sum.elim (fun t => Sum.elim (bi t) (fun _ => 0)) (fun t => Sum.elim (fun _ => 0) (bl t)),Sum.elim ci cl,
    Sum.elim (fun t => extend (aq t)) (Sum.elim (fun t => eg (rl t)) (fun t => outsideOnly (g t))),
    Sum.elim (fun t => extend (bq t)) (Sum.elim (fun t => outsideOnly (f t)) (fun t => eg (sl t))),?_⟩
  intro T
  obtain ⟨u,v,w,ui,vi,wq,hb⟩ := hs fun i j k => T (lower i) (lower j) k
  obtain ⟨y,l,t,hy⟩ := hl fun i j k => T (Sum.inr (Sum.inr i)) (Sum.inl j) k
  obtain ⟨z,r,s,hz⟩ := hr fun j i k => T (Sum.inl i) (Sum.inr (Sum.inr j)) k
  let join (v : (Fin 2⊕D) → ℂ) (r : E → ℂ) : Fin 2 ⊕ (D⊕E) → ℂ :=
    Sum.elim (fun i => v (Sum.inl i)) (Sum.elim (fun i => v (Sum.inr i)) r)
  refine ⟨fun t => join (u t) (y t),fun t => join (v t) (z t),w,Sum.elim ui r,Sum.elim vi l,
    Sum.elim wq (Sum.elim t s),?_⟩
  rintro (i|i) (j|j) k he
  · simpa [lower,extend,eg,join,insideOnly,outsideOnly,Fintype.sum_sum_type] using (hb (Sum.inl i) (Sum.inl j) k (by trivial))
  · cases j with
    | inl j => simpa [lower,extend,eg,join,insideOnly,outsideOnly,Fintype.sum_sum_type] using (hb (Sum.inl i) (Sum.inr j) k (by trivial))
    | inr j => simpa [extend,eg,join,insideOnly,outsideOnly,Fintype.sum_sum_type,mul_comm,mul_assoc,mul_left_comm] using hz j i k
  · cases i with
    | inl i => simpa [lower,extend,eg,join,insideOnly,outsideOnly,Fintype.sum_sum_type] using (hb (Sum.inr i) (Sum.inl j) k (by trivial))
    | inr i => simpa [extend,eg,join,insideOnly,outsideOnly,Fintype.sum_sum_type] using hy i j k
  · exact False.elim he

end CriticalTensor.SixBorder.Tiles


namespace CriticalTensor.SixBorder.Binary

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

end CriticalTensor.SixBorder.Binary

namespace CriticalTensor.SixBorder.Cells

def prodFin {A B : Type} {a b : ℕ} (ea : A ≃ Fin a) (eb : B ≃ Fin b) : A×B ≃ Fin (a*b) :=
  (ea.prodCongr eb).trans finProdFinEquiv
def sumFin {A B : Type} {a b : ℕ} (ea : A ≃ Fin a) (eb : B ≃ Fin b) : A⊕B ≃ Fin (a+b) :=
  (Equiv.sumCongr ea eb).trans finSumFinEquiv

/-- Row order is the two outer rows followed by the two outer columns in
each interior row. The third index varies fastest. -/
def rowEquiv (d w : ℕ) : Pencils.Rows (Fin d) (Fin w) ≃ Fin (2*((2+d)*w)+d*(2*w)) :=
  let e : Pencils.Rows (Fin d) (Fin w) ≃ (Fin 2 × Pencils.Coord (Fin d) × Fin w) ⊕ (Fin d × Fin 2 × Fin w) :=
    { toFun := fun z => match z with
        | ⟨(Sum.inl i,j,k),_⟩ => Sum.inl (i,j,k)
        | ⟨(Sum.inr i,Sum.inl j,k),_⟩ => Sum.inr (i,j,k)
        | ⟨(Sum.inr _,Sum.inr _,_),h⟩ => False.elim h
      invFun := Sum.elim (fun z => ⟨(Sum.inl z.1,z.2.1,z.2.2),by cases z.2.1 <;> trivial⟩)
        (fun z => ⟨(Sum.inr z.1,Sum.inl z.2.1,z.2.2),by trivial⟩)
      left_inv := by rintro ⟨⟨i,j,k⟩,h⟩; cases i <;> cases j <;> first | rfl | exact False.elim h
      right_inv := by rintro (⟨i,j,k⟩|⟨i,j,k⟩) <;> rfl }
  e.trans (sumFin (prodFin (Equiv.refl _) (prodFin finSumFinEquiv (Equiv.refl _)))
    (prodFin (Equiv.refl _) (prodFin (Equiv.refl _) (Equiv.refl _))))

def colEquiv (d w x n q : ℕ) : Pencils.Cols (Fin d) (Fin w) (Fin x) (Fin n) (Fin q) ≃
    Fin (x*((2+d)+((2+d)+w))+(n*(2+2)+q*w)) :=
  sumFin (prodFin (Equiv.refl _) (sumFin finSumFinEquiv (sumFin finSumFinEquiv (Equiv.refl _))))
    (sumFin (prodFin (Equiv.refl _) finSumFinEquiv) (prodFin (Equiv.refl _) (Equiv.refl _)))

end CriticalTensor.SixBorder.Cells


namespace CriticalTensor.SixBorder.Cells

open CriticalTensor.SixBorder.Pencils CriticalTensor.SixBorder.Tiles

def mask {s d : ℕ} (data : Array ℕ) (t : Fin s) (k : Fin d) : ℤ :=
  Binary.intBit ((data[t.val]?.getD 0).testBit k.val)

def outA {x : ℕ} : Fin x → Fin 2 → ℤ := mask #[2, 1, 2, 3, 3, 2]
def outB {x : ℕ} : Fin x → Fin 2 → ℤ := mask #[3, 1, 1, 2, 3, 1]
def basisC {x w : ℕ} (t : Fin x) (k : Fin w) : ℤ := if t.val=k.val then 1 else 0

def Room (d w x n q : ℕ) : Prop :=
  Anchored (D:=Fin d) (N:=Fin n) (Q:=Fin q) (fun (t : Fin x) i => (outA t i : ℂ))
    (fun t j => (outB t j : ℂ)) (fun t (k : Fin w) => (basisC t k : ℂ))

def Wing (d w x n v : ℕ) : Prop :=
  Paired (D:=Fin d) (N:=Fin n) (V:=Fin v) (fun (t : Fin x) i => (outA t i : ℂ))
    (fun t j => (outB t j : ℂ)) (fun t (k : Fin w) => (basisC t k : ℂ))

lemma pencil_cast {D Wh X N Q : Type} [DecidableEq D] [DecidableEq Wh]
    (a b : X → Coord D → ℤ) (c : X → Wh → ℤ) (ai bi : N → D → ℤ) (ci : N → Wh → ℤ)
    (aq bq : Q → Coord D → ℤ) :
    (Pencils.matrix a b c ai bi ci aq bq).map (Int.castRingHom ℂ) =
      Pencils.matrix (fun t i => (a t i : ℂ)) (fun t i => (b t i : ℂ)) (fun t i => (c t i : ℂ))
        (fun t i => (ai t i : ℂ)) (fun t i => (bi t i : ℂ)) (fun t i => (ci t i : ℂ))
        (fun t i => (aq t i : ℂ)) (fun t i => (bq t i : ℂ)) := by
  ext ⟨⟨i,j,h⟩,hz⟩ z
  rcases z with ⟨t,e|e|e⟩ | ⟨t,e|e⟩ | ⟨t,e⟩ <;> cases i <;> cases j <;>
    simp only [Pencils.matrix, Matrix.map_apply, Sum.elim_inl,Sum.elim_inr] <;> split <;> simp

lemma certified_room {d w x n q : ℕ} (ax bx : Fin x → Fin d → ℤ)
    (ai bi : Fin n → Fin d → ℤ) (ci : Fin n → Fin w → ℤ) (aq bq : Fin q → Coord (Fin d) → ℤ)
    (h : Function.Surjective ((Pencils.matrix (fun t => Sum.elim (outA t) (ax t))
      (fun t => Sum.elim (outB t) (bx t)) basisC ai bi ci aq bq).map (Int.castRingHom ℂ)).mulVec) :
    Room d w x n q := by
  classical
  refine ⟨fun t i => ax t i,fun t i => bx t i,fun t i => ai t i,fun t i => bi t i,
    fun t k => ci t k,fun t i => aq t i,fun t i => bq t i,?_⟩
  apply (holds_iff _ _ _ _ _ _ _ _).mpr
  rw [pencil_cast] at h
  have he (a : Fin 2 → ℤ) (b : Fin d → ℤ) :
      (fun i => ((Sum.elim a b i : ℤ) : ℂ)) = Sum.elim (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) := by
    funext i
    cases i <;> rfl
  have hOut (op : Fin x → Fin 2 → ℤ) (ip : Fin x → Fin d → ℤ) :
      (fun t i => ((Sum.elim (op t) (ip t) i : ℤ) : ℂ)) =
        (fun t => Sum.elim (fun i => (op t i : ℂ)) (fun i => (ip t i : ℂ))) := by
    funext t
    exact he (op t) (ip t)
  rw [hOut outA ax,hOut outB bx] at h
  exact h

abbrev ArmCols (D Wh X N V : Type) := (X × D) ⊕ ((N × Fin 2) ⊕ (V × Wh))
def armMatrix {D Wh X N V : Type} [DecidableEq D] [DecidableEq Wh] (O : X → Fin 2 → ℤ) (C : X → Wh → ℤ)
    (a : N → D → ℤ) (ci : N → Wh → ℤ) (b : V → D → ℤ) (f : V → Fin 2 → ℤ) :
    Matrix (D × Fin 2 × Wh) (ArmCols D Wh X N V) ℤ
  | (i,j,k),Sum.inl (t,h) => if h=i then O t j*C t k else 0
  | (i,j,k),Sum.inr (Sum.inl (t,h)) => if h=j then a t i*ci t k else 0
  | (i,j,k),Sum.inr (Sum.inr (t,h)) => if h=k then b t i*f t j else 0

lemma certified_limb {D Wh X N V : Type} [Fintype D] [Fintype Wh] [Fintype X] [Fintype N] [Fintype V]
    [DecidableEq D] [DecidableEq Wh] (O : X → Fin 2 → ℤ) (C : X → Wh → ℤ)
    (a : N → D → ℤ) (ci : N → Wh → ℤ) (b : V → D → ℤ) (f : V → Fin 2 → ℤ)
    (h : Function.Surjective ((armMatrix O C a ci b f).map (Int.castRingHom ℂ)).mulVec) :
    Limb (fun t i => (O t i : ℂ)) (fun t k => (C t k : ℂ)) (fun t i => (a t i : ℂ))
      (fun t k => (ci t k : ℂ)) (fun t i => (b t i : ℂ)) (fun t j => (f t j : ℂ)) := by
  intro T
  obtain ⟨y,hy⟩ := h fun z => T z.1 z.2.1 z.2.2
  refine ⟨fun t i => y (Sum.inl (t,i)),fun t j => y (Sum.inr (Sum.inl (t,j))),
    fun t k => y (Sum.inr (Sum.inr (t,k))),?_⟩
  intro i j k
  refine (congrFun hy (i,j,k)).symm.trans ?_
  change (∑ z : ArmCols D Wh X N V, ((armMatrix O C a ci b f (i,j,k) z : ℤ) : ℂ) * y z) = _
  simp [Fintype.sum_sum_type,Fintype.sum_prod_type,armMatrix,apply_ite,Finset.sum_ite_eq',
    mul_comm,mul_assoc,add_assoc]

def armRows (d w : ℕ) : Fin d × Fin 2 × Fin w ≃ Fin (d*(2*w)) :=
  prodFin (Equiv.refl _) (prodFin (Equiv.refl _) (Equiv.refl _))
def armCols (d w x n v : ℕ) : ArmCols (Fin d) (Fin w) (Fin x) (Fin n) (Fin v) ≃ Fin (x*d+(n*2+v*w)) :=
  sumFin (prodFin (Equiv.refl _) (Equiv.refl _)) (sumFin (prodFin (Equiv.refl _) (Equiv.refl _))
    (prodFin (Equiv.refl _) (Equiv.refl _)))

end CriticalTensor.SixBorder.Cells


namespace CriticalTensor.SixBorder.Cells

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

end CriticalTensor.SixBorder.Cells

namespace CriticalTensor.SixBorder.Cells

open Pencils Tiles Binary

def y : Fin 6 → Fin 2 → ℤ := mask #[1, 1, 0, 2, 1, 3]
def z : Fin 6 → Fin 2 → ℤ := mask #[1, 1, 3, 3, 0, 0]
def byCoord : Fin 1 → Fin 2 → ℤ := mask #[1]
def bzCoord : Fin 1 → Fin 2 → ℤ := mask #[3]
def axCoord : Fin 1 → Fin 6 → ℤ := mask #[0x3f]

/-- The initial room has two inner coordinates and one incoming point. -/
def M : Matrix (Rows (Fin 2) (Fin 6)) (Cols (Fin 2) (Fin 6) (Fin 6) (Fin 1) (Fin 0)) ℤ :=
  Pencils.matrix (fun t => Sum.elim (outA t) (y t)) (fun t => Sum.elim (outB t) (z t)) basisC
    byCoord bzCoord axCoord 0 0

def roomCols (j : ℕ) : ℕ := (#[0x1041, 0x1041000000, 0x41000000000000, 0x41000000000000000, 0x1000001000000, 0x40000040000000, 0x1000000000, 0x40000000000, 0x41001041000000, 0x82002082000000, 0x104004104000000, 0x208008208000000, 0x410010410000000, 0x820020820000000, 0x2002, 0x2002000000, 0x2000000000000, 0x2000000000000000, 0x2000000000002, 0x80000000000080, 0x2000, 0x80000, 0x1000000001001, 0x2000000002002, 0x4000000004004, 0x8000000008008, 0x10000000010010, 0x20000000020020, 0x104004, 0x104004000000, 0x4000000000000, 0x4000000000000000, 0x4000000, 0x100000000, 0x4000000000, 0x100000000000, 0x41001000000, 0x82002000000, 0x104004000000, 0x208008000000, 0x410010000000, 0x820020000000, 0x208200, 0x208200000000, 0x200000000000000, 0x200000000000000000, 0x8000000008000008, 0x200000000200000200, 0x8000008000, 0x200000200000, 0x40000041040041040, 0x80000082080082080, 0x100000104100104100, 0x200000208200208200, 0x400000410400410400, 0x800000820800820800, 0x410, 0x410000000, 0x410000000000000, 0x410000000000000000, 0x10000010000010, 0x400000400000400, 0x10000010000, 0x400000400000, 0x41000041000041, 0x82000082000082, 0x104000104000104, 0x208000208000208, 0x410000410000410, 0x820000820000820, 0x20, 0x20000000, 0x20000000000000, 0x20000000000000000, 0x20020000020000000, 0x800800000800000000, 0x20000000000, 0x800000000000, 0x1001000001000000, 0x2002000002000000, 0x4004000004000000, 0x8008000008000000, 0x10010000010000000, 0x20020000020000000, 0xfff000, 0xfff000000000, 0x3f000000000000, 0xfc0000000000000][j]?.getD 0)
def roomInv (i : ℕ) : ℕ := (#[0x10000001000400097, 0x50000, 0xd0d9ea92851707166afe8f, 0x1188002000800, 0x42010046015890460118a6, 0x400000000000000000, 0x10004000a7, 0x80020000000000068200, 0xd0d9ee92851703166afa8f, 0x200080000588000000000, 0x42010047015890460118a6, 0x10600000000000002000, 0x10000000000000031, 0x54000, 0xd0d9ea92851707576afe8f, 0x200000000400002000000, 0x4600000000001000, 0x1400000000008000000, 0x400100040000004000ba, 0x200000, 0x51000000, 0x800001c8002000000, 0xd000010004000000, 0xc298a204814a870a0fae04, 0x10000000b6, 0x80000000000000030000, 0x100000000, 0x200080000f00000000000, 0x5600000004001000, 0x800000000000000000, 0x1000000082, 0x800200000000000f0000, 0x200000000, 0x200080000f88000000000, 0x5400000004001000, 0xc2908204014887020fae04, 0x36, 0x80000000000000038000, 0x400000000, 0x200000001400002000000, 0x600000000001000, 0x10000000000000000000, 0x80, 0x2000008000, 0x520000000, 0x80001b08002000000, 0x5000010004000000, 0x10800000020000000000, 0x10000000a6, 0x10000, 0x40000000, 0x200000001588002000800, 0x42010000015890420108a6, 0x1000000000000000000, 0x10000000a2, 0x800200000000000e8200, 0x740000400, 0x100000000000, 0x42010004015890420108a6, 0xc2810204014887020f8e04, 0x40000000000000000010, 0x20000, 0x80000000, 0x200080001a88002000800, 0x420100db415890420108a6, 0x2000000000000000000, 0x40000000000000000018, 0x800000080020002fc200, 0x40010000730000400, 0x200000000000, 0x420100d3415890420108a6, 0x19800000000000002000][i]?.getD 0)

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
lemma room_rank : Function.Surjective ((M).map (Int.castRingHom ℂ)).mulVec := by
  apply rank_of_binary (M) (rowEquiv 2 6) (colEquiv 2 6 6 1 0) roomCols roomInv
  · decide +kernel
  · decide +kernel

lemma initial : Room 2 6 6 1 0 := certified_room y z byCoord bzCoord axCoord 0 0 room_rank

def ones : Fin 3 → Fin 1 → ℤ := fun _ _ => 1
def pairs : Fin 3 → Fin 6 → ℤ := mask #[3,12,48]

def leftM : Matrix (Fin 1 × Fin 2 × Fin 6) (ArmCols (Fin 1) (Fin 6) (Fin 6) (Fin 3) (Fin 0)) ℤ :=
  armMatrix outB basisC ones pairs 0 0

def leftCols (j : ℕ) : ℕ := (#[0x41, 2, 4, 0x200, 0x410, 0x20, 3, 0xc0, 0xc, 0x300, 0x30, 0xc00][j]?.getD 0)
def leftInv (i : ℕ) : ℕ := (#[0x42, 2, 4, 0x104, 0x420, 0x20, 0x43, 0xc3, 0x208, 8, 0x430, 0xc30][i]?.getD 0)

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
lemma left_rank : Function.Surjective ((leftM).map (Int.castRingHom ℂ)).mulVec := by
  apply rank_of_binary (leftM) (armRows 1 6) (armCols 1 6 6 3 0) leftCols leftInv
  · decide +kernel
  · decide +kernel

def rightM : Matrix (Fin 1 × Fin 2 × Fin 6) (ArmCols (Fin 1) (Fin 6) (Fin 6) (Fin 3) (Fin 0)) ℤ :=
  armMatrix outA basisC ones pairs 0 0

def rightCols (j : ℕ) : ℕ := (#[0x40, 2, 0x100, 0x208, 0x410, 0x800, 3, 0xc0, 0xc, 0x300, 0x30, 0xc00][j]?.getD 0)
def rightInv (i : ℕ) : ℕ := (#[0x42, 2, 0x30c, 0x20c, 0x830, 0xc30, 1, 0x81, 4, 0x204, 0x820, 0x20][i]?.getD 0)

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
lemma right_rank : Function.Surjective ((rightM).map (Int.castRingHom ℂ)).mulVec := by
  apply rank_of_binary (rightM) (armRows 1 6) (armCols 1 6 6 3 0) rightCols rightInv
  · decide +kernel
  · decide +kernel

lemma wing : Wing 1 6 6 3 0 :=
  ⟨_,_,_,_,_,_,_,certified_limb outB basisC ones pairs 0 0 left_rank,
    certified_limb outA basisC ones pairs 0 0 right_rank⟩

end CriticalTensor.SixBorder.Cells

namespace CriticalTensor.SixBorder

open Cells Tiles

/-- Each additional base coordinate uses three incoming points and preserves
all six anchored regular factors from the initial two-coordinate case. -/
private lemma extend (r : ℕ) : PencilFor (Fin (2+r)) (Fin 6) (Fin 6) (Fin (1+r*3)) (Fin 0) := by
  have raw := to_pencil (append initial (repeat_paired (Fin r) wing))
  refine pencil_transport ?_ (Equiv.refl _) ?_ ?_ raw <;> apply Fintype.equivOfCardEq
  all_goals simp [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]

private lemma pad_inner {D W X N Z Q : Type} [Fintype X] [Fintype N] [Fintype Z] [Fintype Q]
    (h : PencilFor D W X N Q) : PencilFor D W X (N⊕Z) Q := by
  obtain ⟨a,b,c,ai,bi,ci,aq,bq,hh⟩ := h
  refine ⟨a,b,c,Sum.elim ai 0,Sum.elim bi 0,Sum.elim ci 0,aq,bq,?_⟩
  intro T
  obtain ⟨u,v,w,ui,vi,wq,hs⟩ := hh T
  refine ⟨u,v,w,Sum.elim ui 0,Sum.elim vi 0,wq,?_⟩
  intro i j k he
  cases i <;> cases j <;> simpa [outsideOnly,insideOnly,Fintype.sum_sum_type] using hs _ _ k he

private lemma to_border {d n : ℕ} (h : PencilFor (Fin d) (Fin 6) (Fin 6) (Fin n) (Fin 0)) :
    CriticalTensor.Border 6 d 2 n 6 := by
  obtain ⟨a,b,c,ai,bi,ci,aq,bq,hh⟩ := h
  refine ⟨c,a,b,ci,ai,bi,?_⟩
  intro T
  obtain ⟨u,v,w,ui,vi,wq,hs⟩ := hh fun j k i => T i j k
  refine ⟨w,u,v,ui,vi,?_⟩
  intro i j k hleft
  have he : edge j k := by cases j <;> cases k <;> simp_all [edge]
  simpa [outsideOnly,insideOnly,mul_comm,mul_left_comm,mul_assoc,add_comm,add_left_comm,add_assoc] using hs j k i he


private lemma extend_one (r : ℕ) : Border 6 (2+r) 2 (1+r*3+1) 6 := by
  apply to_border
  have h := pad_inner (Z:=Fin 1) (extend r)
  refine pencil_transport (Equiv.refl _) (Equiv.refl _) ?_ (Equiv.refl _) h
  apply Fintype.equivOfCardEq
  simp

lemma border_six : Border 6 6 2 14 6 := extend_one 4
lemma border_seven : Border 6 7 2 17 6 := extend_one 5
lemma border_ten : Border 6 10 2 25 6 := to_border (extend 8)
lemma border_eleven : Border 6 11 2 28 6 := to_border (extend 9)

/-- The 24 cross columns are the coordinate vectors of the six-by-two-by-two block. -/
lemma cross_six : Cross 6 2 6 := by
  classical
  let e : Fin 3 × Fin 2 ≃ Fin 6 := finProdFinEquiv
  let f : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv
  let low (t : Fin 6) := f (.inl (e.symm t).1)
  let high (t : Fin 6) := f (.inr (e.symm t).1)
  let bit (t : Fin 6) := (e.symm t).2
  let x₁ (t : Fin 6) (i : Fin 6) : ℂ := if low t=i then 1 else 0
  let x₂ (t : Fin 6) (i : Fin 6) : ℂ := if high t=i then 1 else 0
  let b (t : Fin 6) (j : Fin 2) : ℂ := if bit t=j then 1 else 0
  refine ⟨x₁,x₂,b,b,?_⟩
  intro T
  let v (t : Fin 6) (j : Fin 2) := T (high t) j (bit t)
  let w (t : Fin 6) (k : Fin 2) := T (low t) (bit t) k
  refine ⟨v,w,?_⟩
  intro i j k
  obtain ⟨s,rfl⟩ := f.surjective i
  let term (t : Fin 6) := x₂ t (f s)*(v t j*b t k) + x₁ t (f s)*(b t j*w t k)
  change T (f s) j k = ∑ t,term t
  rw [← e.sum_comp term,Fintype.sum_prod_type]
  cases s <;> simp [term,x₁,x₂,b,v,w,low,high,bit,mul_ite,ite_mul,Finset.sum_ite_eq']

end CriticalTensor.SixBorder

namespace CriticalTensor

private lemma six_ceiling {n d q : ℕ} (hd : 0 < d) (lo : d*q < n) (hi : n ≤ d*(q+1)) :
    n ⌈/⌉ d = q+1 := by
  apply le_antisymm ((ceilDiv_le_iff_le_mul hd).mpr hi)
  by_contra! h
  exact (not_le_of_gt lo) ((ceilDiv_le_iff_le_mul hd).mp (show n ⌈/⌉ d ≤ q by omega))

/-- Four finite templates suffice for the predicted six-slice rank at every square size. -/
lemma six_square_of_templates
    (b₆ : Spans 6 6 6 14) (b₇ : Spans 6 7 7 17)
    (b₁₀ : Spans 6 10 10 25) (b₁₁ : Spans 6 11 11 28)
    (r₆ : Border 6 6 2 14 6) (r₇ : Border 6 7 2 17 6)
    (r₁₀ : Border 6 10 2 25 6) (r₁₁ : Border 6 11 2 28 6)
    (cross : Cross 6 2 6) (m : ℕ) (hm : 6 ≤ m) :
    Spans 6 m m (6*m*m ⌈/⌉ (6+m+m-2)) := by
  by_cases small : m < 10
  · interval_cases m
    · exact b₆
    · exact b₇
    · exact grow 6 6 2 14 6 1 b₆ r₆ cross
    · exact grow 6 7 2 17 6 1 b₇ r₇ cross
  · by_cases even : m%2=0
    · obtain ⟨t,rfl⟩ : ∃ t, m=10+2*t := ⟨(m-10)/2,by omega⟩
      have den : 6+(10+2*t)+(10+2*t)-2=24+4*t := by omega
      rw [den]
      have num : 6*(10+2*t)*(10+2*t) ⌈/⌉ (24+4*t) = 25+6*t := by
        have h := six_ceiling (n:=6*(10+2*t)*(10+2*t)) (d:=24+4*t) (q:=24+6*t)
          (by omega) (by nlinarith) (by nlinarith)
        omega
      rw [num]
      exact grow 6 10 2 25 6 t b₁₀ r₁₀ cross
    · obtain ⟨t,rfl⟩ : ∃ t, m=11+2*t := ⟨(m-11)/2,by omega⟩
      have den : 6+(11+2*t)+(11+2*t)-2=26+4*t := by omega
      rw [den]
      have num : 6*(11+2*t)*(11+2*t) ⌈/⌉ (26+4*t) = 28+6*t := by
        have h := six_ceiling (n:=6*(11+2*t)*(11+2*t)) (d:=26+4*t) (q:=27+6*t)
          (by omega) (by nlinarith) (by nlinarith)
        omega
      rw [num]
      exact grow 6 11 2 28 6 t b₁₁ r₁₁ cross

end CriticalTensor

namespace CriticalTensor

/-- The tangent configuration at the dimension-count ceiling for all six-slice squares. -/
theorem six_square (m : ℕ) (hm : 6 ≤ m) : Spans 6 m m (6*m*m ⌈/⌉ (6+m+m-2)) :=
  six_square_of_templates SixBase.base_six SixBase.base_seven SixBase.base_ten SixBase.base_eleven
    SixBorder.border_six SixBorder.border_seven SixBorder.border_ten SixBorder.border_eleven
    SixBorder.cross_six m hm

end CriticalTensor

theorem OMA.solution : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1.H1 := by
  intro m hm
  exact CriticalReduction.bounded_of_witness (CriticalTensor.six_square m hm)
