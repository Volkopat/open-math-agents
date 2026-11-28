import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1
import Mathlib

/-! # Comparing reduced forms and ordered three-square representations

Fix a primitive pure integral quaternion of norm s. For a reduced form
(a,b,c), an odd-norm left divisor of b+v supplies an integral conjugate of
v. Signs are reduced by quaternion units, with one optional quarter turn
to record the image as a nonnegative ordered triple. If two images coincide,
a short quaternion commuting with v is scalar. Its norm and the primitive
divisors recover a and b; the discriminant then recovers c.

The quaternion splitting and prime divisor lemmas and the Legendre
three-square theorem are adapted from earlier proofs credited below.
-/

/-! The quaternion model, eigenline count, and eight representatives per line are adapted from @ysanatomic (Yordan), merged Tunnell even-twist proof 3112a07, via @marcusbuffett in the merged Erdős 338 squares proof. We apply them to conjugation of trace-zero quaternions to count primitive ternary representations. -/

section

/- Integral quaternion norm shells, rotations, and the weight on a coordinate. -/

namespace TunnellQuaternion

open Finset Quaternion


abbrev QInt := Quaternion ℤ

lemma normSq_mk (a b c d : ℤ) : Quaternion.normSq (⟨a,b,c,d⟩:QInt) = a^2+b^2+c^2+d^2 := Quaternion.normSq_def' _

lemma neg_mk (a b c d : ℤ) : -(⟨a,b,c,d⟩:QInt) = ⟨-a,-b,-c,-d⟩ := rfl

abbrev coordsEquiv := Quaternion.equivProd ℤ

noncomputable def quatShell (N : ℕ) : Finset QInt :=
  let I := Icc (-(N:ℤ)) (N:ℤ)
  ((I ×ˢ (I ×ˢ (I ×ˢ I))).map coordsEquiv.symm.toEmbedding).filter (fun q => Quaternion.normSq q=N)

@[simp] lemma mem_quatShell {q : QInt} {N : ℕ} : q ∈ quatShell N ↔ Quaternion.normSq q=N := by
  simp only [quatShell,mem_filter,mem_map_equiv]
  refine ⟨And.right,fun hn => ⟨?_,hn⟩⟩
  rw [Quaternion.normSq_def'] at hn
  obtain ⟨a,b,c,d⟩ := q
  change a^2+b^2+c^2+d^2 = (N:ℤ) at hn
  simp only [mem_product,mem_Icc]
  change (- (N:ℤ) ≤ a ∧ a ≤ N) ∧ (- (N:ℤ) ≤ b ∧ b ≤ N) ∧
    (- (N:ℤ) ≤ c ∧ c ≤ N) ∧ - (N:ℤ) ≤ d ∧ d ≤ N
  have hb (x : ℤ) (h : x^2 ≤ N) : -(N:ℤ) ≤ x ∧ x ≤ N := by
    constructor <;> by_contra! he
    · have := mul_nonneg_of_nonpos_of_nonpos (by omega : x ≤ 0) (by omega : x+1 ≤ 0)
      nlinarith
    · have := mul_nonneg (by omega : 0 ≤ x) (by omega : 0 ≤ x-1)
      nlinarith
  exact ⟨hb _ (by nlinarith [sq_nonneg b,sq_nonneg c,sq_nonneg d]),
    hb _ (by nlinarith [sq_nonneg a,sq_nonneg c,sq_nonneg d]),
    hb _ (by nlinarith [sq_nonneg a,sq_nonneg b,sq_nonneg d]),
    hb _ (by nlinarith [sq_nonneg a,sq_nonneg b,sq_nonneg c])⟩

end TunnellQuaternion

end

section

/- Explicit splitting of the Hamilton quaternion algebra at odd primes. -/

namespace TunnellQuaternion

open Matrix Quaternion

variable {K : Type*} [Field K]

def matrixOf (a b : K) (x : Quaternion K) : Matrix (Fin 2) (Fin 2) K :=
  !![x.re + a*x.imJ + b*x.imK, x.imI+b*x.imJ-a*x.imK;
     -x.imI+b*x.imJ-a*x.imK, x.re-a*x.imJ-b*x.imK]

def splitHom (a b : K) (hab : a^2+b^2 = -1) : Quaternion K →+* Matrix (Fin 2) (Fin 2) K where
  toFun := matrixOf a b
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp [matrixOf]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp [matrixOf]
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> simp [matrixOf] <;> ring
  map_mul' x y := by
    have hb : b^2= -1-a^2 := by linear_combination hab
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixOf,Matrix.mul_apply,Fin.sum_univ_two] <;> ring_nf <;> rw [hb] <;> ring

lemma split_det (a b : K) (hab : a^2+b^2 = -1) (x : Quaternion K) :
    (splitHom a b hab x).det = normSq x := by
  change (matrixOf a b x).det = _
  simp [Matrix.det_fin_two,matrixOf,normSq_def']
  linear_combination -(x.imJ^2+x.imK^2)*hab

lemma split_trace (a b : K) (hab : a^2+b^2 = -1) (x : Quaternion K) :
    (splitHom a b hab x).trace = 2*x.re := by
  change (matrixOf a b x).trace = _
  simp [Matrix.trace_fin_two,matrixOf]
  ring

lemma split_star (a b : K) (hab : a^2+b^2 = -1) (x : Quaternion K) :
    splitHom a b hab (star x) = (splitHom a b hab x).adjugate := by
  change matrixOf a b (star x) = (matrixOf a b x).adjugate
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixOf] <;> ring

def quaternionOf (a b : K) (m : Matrix (Fin 2) (Fin 2) K) : Quaternion K :=
  ⟨(m 0 0+m 1 1)/2,(m 0 1-m 1 0)/2,
    -(a*(m 0 0-m 1 1) + b*(m 0 1+m 1 0))/2,
    -(b*(m 0 0-m 1 1) - a*(m 0 1+m 1 0))/2⟩

lemma split_iso (a b : K) (hab : a^2+b^2 = -1) (htwo : (2:K) ≠ 0) :
    Function.Bijective (splitHom a b hab) := by
  have hb : b^2 = -1-a^2 := by linear_combination hab
  have left : Function.LeftInverse (quaternionOf a b) (splitHom a b hab) := by
    intro x
    change quaternionOf a b (matrixOf a b x) = x
    ext <;> dsimp [matrixOf,quaternionOf] <;> field_simp <;> ring_nf <;> rw [hb] <;> ring
  have right : Function.RightInverse (quaternionOf a b) (splitHom a b hab) := by
    intro M
    change matrixOf a b (quaternionOf a b M) = M
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp [matrixOf,quaternionOf] <;> field_simp <;> ring_nf <;> rw [hb] <;> ring
  exact ⟨left.injective,right.surjective⟩

lemma exists_splitting (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∃ a b : ZMod p, a^2+b^2 = -1 ∧ (2:ZMod p) ≠ 0 := by
  obtain ⟨a,b,ha,hb,h⟩ := Nat.sq_add_sq_zmodEq p (-1)
  refine ⟨a,b,?_,?_⟩
  · exact_mod_cast ((ZMod.intCast_eq_intCast_iff _ _ _).mpr h)
  · intro he
    have hh := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using he)
    have := (Nat.dvd_prime Nat.prime_two).mp hh
    have := (Fact.out : p.Prime).ne_one
    tauto

end TunnellQuaternion

end

section

/- Projective lines and rank-one quaternion reductions modulo an odd prime. -/

namespace TunnellQuaternion

open Matrix

variable {K : Type*} [Field K]
abbrev M2 (K : Type*) := Matrix (Fin 2) (Fin 2) K
abbrev V2 (K : Type*) := Fin 2 → K

def inLine (l : Option K) (M : M2 K) : Prop :=
  match l with
  | none => ∀ j, M 0 j = 0
  | some r => ∀ j, M 1 j = r*M 0 j

def direction (l : Option K) : V2 K := match l with
  | none => ![0,1]
  | some r => ![1,r]

def rowOf (l : Option K) (M : M2 K) : V2 K := match l with
  | none => M 1
  | some _ => M 0

lemma line_factored {l : Option K} {M : M2 K} (h : inLine l M) :
    vecMulVec (direction l) (rowOf l M) = M := by
  ext i j
  cases l <;> fin_cases i <;> fin_cases j <;> simp_all [inLine,rowOf,direction,vecMulVec]

lemma line_mul {l : Option K} {M : M2 K} (h : inLine l M) (B : M2 K) :
    inLine l (M*B) := by
  cases l with
  | none => change ∀ j, M 0 j = 0 at h; intro j; simp [Matrix.mul_apply,h]
  | some r =>
    intro j
    change ∀ j, M 1 j=r*M 0 j at h
    simp [Matrix.mul_apply,h,mul_assoc,mul_add]

lemma line_smul {l : Option K} {M : M2 K} (h : inLine l M) (t : K) :
    inLine l (t • M) := by
  cases l with
  | none => change ∀ j, M 0 j = 0 at h; intro j; simp [h]
  | some r => intro j; change ∀ j, M 1 j = r*M 0 j at h; simp [h,mul_left_comm]

lemma det_line {l : Option K} {M : M2 K} (h : inLine l M) : M.det=0 := by
  cases l <;> simp_all [inLine, Matrix.det_fin_two] <;> ring

lemma line_unique (M : M2 K) (h : M≠0) (hd : M.det=0) : ∃! l, inLine l M := by
  by_cases h0 : ∀ j, M 0 j=0
  · refine ⟨none,h0,?_⟩
    rintro (_|r) he
    · rfl
    · change ∀ j, M 1 j=r*M 0 j at he; exfalso; apply h; ext i j; fin_cases i <;> simp [h0,he]
  · obtain ⟨j,hj⟩ := not_forall.mp h0
    refine ⟨some (M 1 j/M 0 j),?_,?_⟩
    · intro k
      rw [div_mul_eq_mul_div,eq_div_iff hj]
      rw [Matrix.det_fin_two] at hd
      fin_cases j <;> fin_cases k
      · rfl
      · change M 1 1 * M 0 0 = M 1 0 * M 0 1; linear_combination hd
      · change M 1 0 * M 0 1 = M 1 1 * M 0 0; linear_combination -hd
      · rfl
    · rintro (_|r) he
      · exact False.elim (hj (he j))
      · congr 1
        exact (eq_div_iff hj).mpr (he j).symm

lemma adj_mul_zero_iff {l : Option K} {A : M2 K} (hA : A≠0)
    (hdl : inLine l A) (B : M2 K) : A.adjugate * B = 0 ↔ inLine l B := by
  by_cases hr : rowOf l A = 0
  · have := line_factored hdl
    rw [hr, Matrix.vecMulVec_zero] at this
    exact False.elim (hA this.symm)
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hr
  rw [Matrix.adjugate_fin_two]
  cases l with
  | none =>
    change ∀ j, A 0 j=0 at hdl
    change A 1 i ≠ 0 at hi
    constructor
    · intro h j
      have h₀ := congrArg (fun M:M2 K => M 0 j) h
      have h₁ := congrArg (fun M:M2 K => M 1 j) h
      simp [Matrix.mul_apply,Fin.sum_univ_two,hdl] at h₀ h₁
      fin_cases i <;> grind
    · intro h; change ∀ j, B 0 j=0 at h; ext i j; fin_cases i <;> simp [Matrix.mul_apply,Fin.sum_univ_two,hdl,h]
  | some r =>
    change ∀ j, A 1 j=r*A 0 j at hdl
    change A 0 i ≠ 0 at hi
    constructor
    · intro h j
      have h₀ := congrArg (fun M:M2 K => M 0 j) h
      have h₁ := congrArg (fun M:M2 K => M 1 j) h
      simp [Matrix.mul_apply,Fin.sum_univ_two,hdl] at h₀ h₁
      fin_cases i
      · apply mul_left_cancel₀ hi
        change A 0 0 * B 1 j = A 0 0 * (r*B 0 j)
        linear_combination h₁
      · apply mul_left_cancel₀ hi
        change A 0 1 * B 1 j = A 0 1 * (r*B 0 j)
        linear_combination -h₀
    · intro h; change ∀ j, B 1 j=r*B 0 j at h
      ext i j; fin_cases i <;> simp [Matrix.mul_apply,Fin.sum_univ_two,hdl,h] <;> ring

lemma reversed_product_zero {A B : M2 K} (ha : A.det=0) (hb : B.det=0)
    (hab : A*B≠0) (htr : (A*B).trace=0) : B*A=0 := by
  obtain ⟨l,hl,_⟩ := line_unique A (by rintro rfl; simp at hab) ha
  obtain ⟨m,hm,_⟩ := line_unique B (by rintro rfl; simp at hab) hb
  rw [←line_factored hl,←line_factored hm] at hab htr ⊢
  let u := direction l
  let v := rowOf l A
  let x := direction m
  let y := rowOf m B
  have mul (a b c d : V2 K) : vecMulVec a b * vecMulVec c d = (b ⬝ᵥ c) • vecMulVec a d := by
    rw [Matrix.vecMulVec_mul_vecMulVec]
    ext i j
    simp [mul_left_comm]
  rw [mul] at hab htr ⊢
  have hd : (v ⬝ᵥ x) ≠ 0 := by intro h; exact hab (by rw [show rowOf l A ⬝ᵥ direction m = 0 from h,zero_smul])
  rw [Matrix.trace_smul,Matrix.trace_vecMulVec] at htr
  have e := (mul_eq_zero.mp htr).resolve_left hd
  rw [dotProduct_comm, e,zero_smul]

end TunnellQuaternion

end

section

/- Descent of integral Hamilton quaternions inside specified right ideals modulo an odd prime. -/

namespace TunnellQuaternion

open Quaternion


def redFun (p : ℕ) (q : Quaternion ℤ) : Quaternion (ZMod p) := ⟨q.re,q.imI,q.imJ,q.imK⟩

def red (p : ℕ) : Quaternion ℤ →+* Quaternion (ZMod p) where
  toFun := redFun p
  map_add' x y := by apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_add,Quaternion.imI_add,Quaternion.imJ_add,Quaternion.imK_add] <;> simp [redFun]
  map_mul' x y := by
    apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul] <;> simp [redFun]
  map_zero' := by ext <;> simp [redFun]
  map_one' := by ext <;> simp [redFun]

lemma red_apply (p : ℕ) (x : Quaternion ℤ) : red p x = redFun p x := rfl

lemma red_star (p : ℕ) (x : Quaternion ℤ) : red p (star x) = star (red p x) := by
  change redFun p (star x) = star (redFun p x)
  apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_star,Quaternion.imI_star,Quaternion.imJ_star,Quaternion.imK_star] <;> simp [redFun]

lemma red_norm (p : ℕ) (x : Quaternion ℤ) : ((normSq x:ℤ) : ZMod p) = normSq (red p x) := by
  rw [normSq_def',normSq_def']
  simp [red_apply,redFun]

lemma red_smul (p : ℕ) (t : ℤ) (x : Quaternion ℤ) :
    red p (t • x) = (t:ZMod p) • red p x := by
  change redFun p (t • x) = (t:ZMod p) • redFun p x
  apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_smul,Quaternion.imI_smul,Quaternion.imJ_smul,Quaternion.imK_smul] <;> simp [redFun,smul_eq_mul]

lemma norm_smul (t : ℤ) (x : Quaternion ℤ) : normSq (t • x) = t^2*normSq x := by
  rw [← coe_mul_eq_smul, map_mul, normSq_coe]

lemma div_iff (m : ℕ) (q : Quaternion ℤ) : red m q = 0 ↔ ∃ v : Quaternion ℤ, q = (m:ℤ) • v := by
  constructor
  · intro h
    have hd (a : ℤ) (ha : (a:ZMod m)=0) : a=(m:ℤ)*(a/m) :=
      (Int.mul_ediv_cancel' (ZMod.intCast_zmod_eq_zero_iff_dvd a m |>.mp ha)).symm
    refine ⟨⟨q.re/m,q.imI/m,q.imJ/m,q.imK/m⟩,?_⟩
    cases q with | mk a b c d =>
      exact QuaternionAlgebra.ext (hd a (congrArg (fun q : Quaternion (ZMod m) => q.re) h)) (hd b (congrArg (fun q : Quaternion (ZMod m) => q.imI) h))
        (hd c (congrArg (fun q : Quaternion (ZMod m) => q.imJ) h)) (hd d (congrArg (fun q : Quaternion (ZMod m) => q.imK) h))
  · rintro ⟨v,rfl⟩
    rw [red_smul]; simp

def lift (m : ℕ) (x : Quaternion (ZMod m)) : Quaternion ℤ :=
  ⟨x.re.valMinAbs,x.imI.valMinAbs,x.imJ.valMinAbs,x.imK.valMinAbs⟩

@[simp] lemma red_lift (m : ℕ) (x : Quaternion (ZMod m)) : red m (lift m x)=x := by
  change redFun m (lift m x)=x
  apply QuaternionAlgebra.ext <;> dsimp only [redFun,lift] <;> simp

lemma norm_lift_lt {m : ℕ} [NeZero m] (hm : Odd m) (x : Quaternion (ZMod m)) :
    normSq (lift m x) < (m:ℤ)^2 := by
  have hn : 0<(m:ℤ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
  have h (a : ZMod m) : 4*a.valMinAbs^2 < (m:ℤ)^2 := by
    obtain ⟨hl,hu⟩ := a.valMinAbs_mem_Ioc
    have hm' := hm
    rcases hm' with ⟨k,hk⟩
    have hu2 : a.valMinAbs*2 < (m:ℤ) := by omega
    nlinarith [mul_pos (sub_pos.mpr hu2) (by linarith [hl] : 0<(m:ℤ)+a.valMinAbs*2)]
  rw [normSq_def']
  dsimp only [lift]
  linarith [h x.re,h x.imI,h x.imJ,h x.imK]

lemma even_descent (x : Quaternion ℤ) (h : Even (normSq x)) :
    ∃ r : Quaternion ℤ, normSq r=2 ∧ red 2 (x*r)=0 := by
  let i : Quaternion ℤ := ⟨1,1,0,0⟩
  let j : Quaternion ℤ := ⟨1,0,1,0⟩
  let k : Quaternion ℤ := ⟨1,0,0,1⟩
  have ee : normSq (red 2 x)=0 := by rw [←red_norm]; exact h.intCast_zmod_two
  letI : DecidableEq (Quaternion (ZMod 2)) := (Quaternion.equivProd _).decidableEq
  have claim : ∀ w : Quaternion (ZMod 2), normSq w=0 →
      w*red 2 i=0 ∨ w*red 2 j=0 ∨ w*red 2 k=0 := by
    intro ⟨a,b,c,d⟩
    revert a b c d
    decide
  rcases claim _ ee with h|h|h
  · exact ⟨i,by decide, by simpa using h⟩
  · exact ⟨j,by decide, by simpa using h⟩
  · exact ⟨k,by decide, by simpa using h⟩

theorem find_generator {p : ℕ} (hp : p.Prime) (ho : p ≠ 2) (S : Set (Quaternion (ZMod p)))
    (hS : ∀ a ∈ S, ∀ b, a*b ∈ S)
    (hSc : ∀ (r : ZMod p) a, a ∈ S → r • a ∈ S)
    (hzero : ∀ a ∈ S, normSq a=0) (hne : ∃ a ∈ S, a≠0) :
    ∃ q : Quaternion ℤ, normSq q = p ∧ red p q ∈ S := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hodd := hp.odd_of_ne_two ho
  have initial : ∃ m : ℕ, 0 < m ∧ m < p ∧ ∃ x : Quaternion ℤ, normSq x = (m:ℤ)*p ∧ red p x ∈ S := by
    obtain ⟨a,ha,ha0⟩ := hne
    let x := lift p a
    have hr : red p x = a := red_lift p a
    have hd : (p:ℤ) ∣ normSq x := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      (by rw [red_norm,hr,hzero _ ha])
    obtain ⟨v,hv⟩ := hd
    have hx : 0 < normSq x := (normSq_nonneg (a:=x)).lt_of_ne' (normSq_ne_zero.mpr
      (fun he => ha0 (by rw [←hr,he,map_zero])))
    have hpos : 0 < v := pos_of_mul_pos_right (hv ▸ hx) (by positivity : (0:ℤ) ≤ p)
    have hlt := norm_lift_lt hodd a
    change normSq x < (p:ℤ)^2 at hlt
    refine ⟨v.toNat,by omega,?_,x,?_,hr ▸ ha⟩
    · rw [hv,sq] at hlt
      have := lt_of_mul_lt_mul_left hlt (by positivity : (0:ℤ) ≤ p)
      omega
    · rw [Int.toNat_of_nonneg hpos.le,hv,mul_comm]
  obtain ⟨m,⟨hm0,hmp,x,hx,hxs⟩,minimal⟩ := Nat.findX initial
  by_cases hm1 : m=1
  · subst m; exact ⟨x,by simpa using hx,hxs⟩
  have hm : 1 < m := by omega
  have hp0 : (0:ℤ) < p := by exact_mod_cast hp.pos
  have hm0' : (0:ℤ) < m := by exact_mod_cast hm0
  have preserve {d : ℕ} (hd : 0 < d) (hdp : d < p) {r y : Quaternion ℤ}
      (hy : x*r = (d:ℤ) • y) : red p y ∈ S := by
    have hd0 : (d:ZMod p)≠0 := fun hh =>
      have hh' := (ZMod.natCast_eq_zero_iff _ _).mp hh
      (Nat.not_dvd_of_pos_of_lt hd hdp) hh'
    have hs := hS _ hxs (red p r)
    rw [←map_mul,hy,red_smul] at hs
    have := hSc ((d:ZMod p)⁻¹) _ hs
    simpa [smul_smul,hd0] using this
  exfalso
  by_cases he : Even m
  · obtain ⟨u,hu⟩ := he
    have hx2 : Even (normSq x) := by rw [hx]; exact (by exact_mod_cast (show Even m from ⟨u,hu⟩) : Even (m:ℤ)).mul_right _
    obtain ⟨r,hr,hr0⟩ := even_descent x hx2
    obtain ⟨y,hy⟩ := (div_iff 2 _).mp hr0
    have hnorm := congrArg normSq hy
    rw [map_mul,hx,hr,norm_smul] at hnorm
    have hu' : (m:ℤ)=u+u := by exact_mod_cast hu
    refine minimal u (by omega) ⟨by omega,by omega,y,?_,preserve (d:=2) (by decide) (by omega) hy⟩
    norm_num at hnorm
    nlinarith [congrArg (fun k:ℤ => k*p) hu']
  · have hmOdd := Nat.not_even_iff_odd.mp he
    letI : NeZero m := ⟨hm0.ne'⟩
    let r := lift m (red m x)
    have hr : red m r = red m x := red_lift m _
    have hm_norm : ((normSq x:ℤ):ZMod m)=0 := by simp [hx]
    have hd : (m:ℤ) ∣ normSq r := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by
      rw [red_norm,hr,←red_norm]; exact hm_norm)
    obtain ⟨u,hu⟩ := hd
    have hr0 : r≠0 := by
      intro hz
      have hz' : red m x=0 := by rw [←hr,hz,map_zero]
      obtain ⟨w,hw⟩ := (div_iff m x).mp hz'
      rw [hw,norm_smul] at hx
      have hdiv : (m:ℤ) ∣ p := ⟨normSq w,by
        apply mul_left_cancel₀ hm0'.ne' (b := (p:ℤ))
        nlinarith [hx]⟩
      have hdvd : m ∣ p := by exact_mod_cast hdiv
      rcases (Nat.dvd_prime hp).mp hdvd with ee|ee <;> omega
    have hupos : 0 < u := pos_of_mul_pos_right (hu ▸ (normSq_nonneg (a:=r)).lt_of_ne' (normSq_ne_zero.mpr hr0)) hm0'.le
    have hless := norm_lift_lt hmOdd (red m x)
    change normSq r < (m:ℤ)^2 at hless
    rw [hu,sq] at hless
    have huLt := lt_of_mul_lt_mul_left hless hm0'.le
    have hz : red m (x*star r)=0 := by
      rw [map_mul,red_star,hr,self_mul_star,←red_norm,hm_norm,coe_zero]
    obtain ⟨y,hy⟩ := (div_iff m _).mp hz
    have hnorm := congrArg normSq hy
    rw [map_mul,normSq_star,norm_smul,hx,hu] at hnorm
    refine minimal u.toNat (by omega) ⟨by omega,by omega,y,?_,preserve hm0 hmp hy⟩
    rw [Int.toNat_of_nonneg hupos.le]
    apply mul_left_cancel₀ (pow_ne_zero 2 hm0'.ne') (b := normSq y)
    linear_combination -hnorm


end TunnellQuaternion

end

section

namespace TunnellEigenlines

open Matrix

abbrev Mat (p : ℕ) := Matrix (Fin 2) (Fin 2) (ZMod p)

def vec {p : ℕ} : Option (ZMod p) → Fin 2 → ZMod p
  | none => ![0, 1]
  | some r => ![1, r]

def invariant {p : ℕ} (W : Mat p) : Option (ZMod p) → Prop
  | none => W 0 1 = 0
  | some r => W 1 0 + W 1 1 * r = r * (W 0 0 + W 0 1 * r)

instance {p : ℕ} [NeZero p] (W : Mat p) (l : Option (ZMod p)) : Decidable (invariant W l) := by
  cases l <;> unfold invariant <;> infer_instance

theorem invariant_iff {p : ℕ} (W : Mat p) (l : Option (ZMod p)) : invariant W l ↔
    ∃ k : ZMod p, W.mulVec (vec l) = k • vec l := by
  cases l with
  | none =>
    constructor
    · intro h
      refine ⟨W 1 1, ?_⟩
      ext i
      fin_cases i <;> simp_all [vec, invariant, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]
    · rintro ⟨k, h⟩
      simpa [vec, invariant, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail] using congrFun h 0
  | some r =>
    constructor
    · intro h
      refine ⟨W 0 0 + W 0 1 * r, ?_⟩
      ext i
      fin_cases i <;> simp_all [vec, invariant, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, mul_comm]
    · rintro ⟨k, h⟩
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [vec, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail] at h0 h1
      rw [← h0] at h1
      simpa [invariant, mul_comm] using h1

theorem card_invariant {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (W : Mat p)
    (ht : W.trace = 0) :
    ((Finset.univ.filter (invariant W)).card : ℤ) =
      if W = 0 then (p : ℤ) + 1 else 1 + quadraticChar (ZMod p) (-W.det) := by
  classical
  have hc : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp
  have h2 : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)
  by_cases hW : W = 0
  · subst W
    have hall : (Finset.univ.filter (invariant (0 : Mat p))) = Finset.univ := by
      ext l
      cases l <;> simp [invariant]
    simp [hall, ZMod.card]
  rw [if_neg hW]
  have hd : W 1 1 = -W 0 0 := by
    rw [Matrix.trace_fin_two] at ht
    linear_combination ht
  have hdet : -W.det = (W 0 0)^2 + W 0 1 * W 1 0 := by
    rw [Matrix.det_fin_two, hd]
    ring
  by_cases hb : W 0 1 = 0
  · rw [hdet, hb, zero_mul, add_zero]
    by_cases ha : W 0 0 = 0
    · have hc' : W 1 0 ≠ 0 := by
        intro h
        apply hW
        ext i j
        fin_cases i <;> fin_cases j <;> simp_all
      have heq : Finset.univ.filter (invariant W) = {none} := by
        ext l
        cases l <;> simp [invariant, hb, hd, ha, hc']
      simp [heq, ha]
    · have hden := mul_ne_zero h2 ha
      set r : ZMod p := W 1 0 / (2 * W 0 0) with hr
      have hi (s : ZMod p) : invariant W (some s) ↔ s = r := by
        change W 1 0 + W 1 1*s = s*(W 0 0 + W 0 1*s) ↔ _
        rw [hd, hb, zero_mul, add_zero, hr, eq_div_iff hden]
        constructor <;> intro h <;> linear_combination -h
      have heq : Finset.univ.filter (invariant W) = {none, some r} := by
        ext l
        cases l with
        | none => simp [invariant,hb]
        | some s => simpa using hi s
      simp [heq, quadraticChar_sq_one' ha]
  · have hi (r : ZMod p) : invariant W (some r) ↔ (W 0 1*r+W 0 0)^2 = -W.det := by
      change W 1 0 + W 1 1*r = r*(W 0 0 + W 0 1*r) ↔ _
      rw [hd,hdet]
      constructor
      · intro h
        linear_combination -W 0 1*h
      · intro h
        have e : W 0 1*(W 1 0 + -W 0 0*r-r*(W 0 0 + W 0 1*r))=0 := by
          linear_combination -h
        exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hb)
    have hcard : (Finset.univ.filter (invariant W)).card =
        {x : ZMod p | x^2 = -W.det}.toFinset.card := by
      apply Finset.card_nbij' (fun l => W 0 1*l.getD 0 + W 0 0)
        (fun s => some ((s-W 0 0)/W 0 1))
      · intro l hl
        cases l with
        | none => simp [invariant,hb] at hl
        | some r => simpa using (hi r).mp (Finset.mem_filter.mp hl).2
      · intro s hs
        have hs' : s^2 = -W.det := by simpa using hs
        apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hi _).mpr ?_⟩
        have h : W 0 1*((s-W 0 0)/W 0 1)+W 0 0=s := by field_simp; ring
        rw [h, hs']
      · intro l hl
        cases l with
        | none => simp [invariant,hb] at hl
        | some r => simp [hb]
      · intro s _
        change W 0 1*((s-W 0 0)/W 0 1)+W 0 0=s
        field_simp
        ring
    rw [hcard, quadraticChar_card_sqrts hc, add_comm]

end TunnellEigenlines

end

section

/- Norm-prime right divisors parameterized by the projective line at an odd prime. -/

namespace TunnellQuaternion

open Matrix Quaternion

variable {p : ℕ} [Fact p.Prime]

structure Model (p : ℕ) where
  f : Quaternion (ZMod p) ≃+* M2 (ZMod p)
  det (x) : (f x).det=normSq x
  trace (x) : (f x).trace=2*x.re
  bar (x) : f (star x) = (f x).adjugate
  smul (t : ZMod p) (x) : f (t • x)=t • f x

noncomputable def localModel (hp : p≠2) : Model p := Classical.choice <| by
  classical
  obtain ⟨a,b,hab,h2⟩ := exists_splitting p hp
  refine ⟨?_⟩
  exact ⟨RingEquiv.ofBijective (splitHom a b hab) (split_iso a b hab h2),split_det a b hab,
    split_trace a b hab,split_star a b hab,fun t x => by
      change matrixOf a b (t • x) = t • matrixOf a b x
      ext i j; fin_cases i <;> fin_cases j <;> simp [matrixOf] <;> ring⟩

variable (M : Model p)

def residue : Quaternion ℤ →+* M2 (ZMod p) := M.f.toRingHom.comp (red p)

lemma residue_zero (x : Quaternion ℤ) : residue M x = 0 ↔ red p x = 0 :=
  M.f.map_eq_zero_iff

lemma residue_star (x : Quaternion ℤ) : residue M (star x) = (residue M x).adjugate := by
  change M.f (red p (star x)) = _
  rw [red_star,M.bar]
  rfl

lemma residue_det (x : Quaternion ℤ) : (residue M x).det = (normSq x : ℤ) :=
  (M.det _).trans (red_norm p x).symm

lemma norm_prime_nonzero {x : Quaternion ℤ} (hx : normSq x = p) : residue M x ≠ 0 := by
  intro h
  obtain ⟨v,hv⟩ := (div_iff p x).mp ((residue_zero M x).mp h)
  have pp := Fact.out (p:=p.Prime)
  have hh := congrArg normSq hv
  rw [hx,norm_smul,pow_two,mul_assoc] at hh
  have eq := mul_left_cancel₀ (by exact_mod_cast pp.ne_zero : (p:ℤ)≠0)
    (show (p:ℤ)*1=p*((p:ℤ)*normSq v) by simpa using hh)
  have hd : (p:ℤ) ∣ 1 := ⟨_,eq⟩
  have hdn : p ∣ 1 := by exact_mod_cast hd
  exact pp.not_dvd_one hdn

lemma exists_at_line (hp : p≠2) (l : Option (ZMod p)) :
    ∃ x : Quaternion ℤ, normSq x = p ∧ inLine l (residue M x) := by
  let S := {a : Quaternion (ZMod p) | inLine l (M.f a)}
  apply find_generator Fact.out hp S
  · intro a ha b; change inLine l (M.f (a*b)); rw [map_mul]; exact line_mul ha _
  · intro r a ha; change inLine l (M.f (r • a)); rw [M.smul]; exact line_smul ha _
  · intro a ha; rw [←M.det]; exact det_line ha
  · let B : M2 (ZMod p) := vecMulVec (direction l) ![1,0]
    refine ⟨M.f.symm B,?_,?_⟩
    · change inLine l (M.f (M.f.symm B))
      rw [M.f.apply_symm_apply]
      cases l <;> intro j <;> fin_cases j <;> simp [B,vecMulVec,direction]
    · intro h
      have := congrArg M.f h
      rw [M.f.apply_symm_apply,map_zero] at this
      cases l with
      | none => simpa [B,vecMulVec,direction] using congrArg (fun m:M2 (ZMod p) => m 1 0) this
      | some r => simpa [B,vecMulVec,direction] using congrArg (fun m:M2 (ZMod p) => m 0 0) this

lemma scalar_cancel (d : ℤ) (hd : d≠0) {x y : Quaternion ℤ} (h : d • x = d • y) : x=y := by
  apply QuaternionAlgebra.ext
  all_goals
    first
    | exact mul_left_cancel₀ hd (congrArg (fun x:Quaternion ℤ => x.re) h)
    | exact mul_left_cancel₀ hd (congrArg (fun x:Quaternion ℤ => x.imI) h)
    | exact mul_left_cancel₀ hd (congrArg (fun x:Quaternion ℤ => x.imJ) h)
    | exact mul_left_cancel₀ hd (congrArg (fun x:Quaternion ℤ => x.imK) h)

lemma divide_left {q w : Quaternion ℤ} (hq : normSq q=p) {l : Option (ZMod p)}
    (hl : inLine l (residue M q)) (hw : inLine l (residue M w)) :
    ∃ x, w=q*x := by
  have hz := (adj_mul_zero_iff (norm_prime_nonzero M hq) hl (residue M w)).mpr hw
  rw [←residue_star,←map_mul,residue_zero] at hz
  obtain ⟨x,hx⟩ := (div_iff p _).mp hz
  refine ⟨x,?_⟩
  apply scalar_cancel (p:ℤ) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have he := congrArg (q*·) hx
  simpa only [←mul_assoc,self_mul_star,hq,coe_mul_eq_smul,Algebra.mul_smul_comm] using he


end TunnellQuaternion
end

namespace Grimm338
open Quaternion Finset TunnellQuaternion
abbrev Q := Quaternion ℤ

lemma odd_divisor (n : ℕ) (hn : 0<n) (ho : n%2=1) (w : Q) (hd : (n:ℤ) ∣ normSq w) :
    ∃ q d : Q, normSq q=n ∧ w=q*d := by
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases one : n=1
    · subst n; exact ⟨1,w,by simp,by simp⟩
    let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime one
    obtain ⟨m,hm⟩ := Nat.minFac_dvd n
    change n=p*m at hm
    have op : p≠2 := by rintro eq; rw [hm,eq] at ho; omega
    have mp : 0 < m := by
      by_contra! h
      have ez : m=0 := by omega
      rw [ez,mul_zero] at hm
      omega
    have lt : m < n := hm ▸ (by have h := hp.two_le; nlinarith [Nat.mul_le_mul_right m h])
    have om : m%2=1 := by
      by_contra h
      obtain ⟨u,e⟩ : 2 ∣ m := by omega
      rw [hm,e,show p*(2*u)=2*(p*u) by ring] at ho
      omega
    let : Fact p.Prime := ⟨hp⟩
    let M := localModel op
    have dp : (p:ℤ) ∣ normSq w := dvd_trans (by exact_mod_cast (show p ∣ n from ⟨m,hm⟩)) hd
    have det0 : (residue M w).det=0 := (residue_det M w).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr dp)
    have line : ∃ l, inLine l (residue M w) := by
      by_cases hz : residue M w=0
      · exact ⟨none,by rw [hz]; intro j; rfl⟩
      · exact (line_unique _ hz det0).exists
    obtain ⟨l,hl⟩ := line
    obtain ⟨u,hu,ul⟩ := exists_at_line M op l
    obtain ⟨v,ev⟩ := divide_left M hu ul hl
    have dm : (m:ℤ) ∣ normSq v := by
      obtain ⟨k,hk⟩ := hd
      rw [ev,map_mul,hu,hm,Nat.cast_mul,mul_assoc] at hk
      exact ⟨k,mul_left_cancel₀ (by exact_mod_cast hp.ne_zero : (p:ℤ)≠0) hk⟩
    obtain ⟨q,d,hq,eq⟩ := ih m lt mp om v dm
    exact ⟨u*q,d,by rw [map_mul,hu,hq,hm,Nat.cast_mul],by rw [ev,eq,mul_assoc]⟩

def primitive (v : Q) : Prop := ∃ i j k : ℤ, i*v.imI+j*v.imJ+k*v.imK=1

lemma prim_of_sqfree {a b c s : ℕ} (hs : Squarefree s) (h : a^2+b^2+c^2=s) :
    primitive ⟨0,a,b,c⟩ := by
  let d := (a.gcd b).gcd c
  have da : d ∣ a := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have db : d ∣ b := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have dc : d ∣ c := Nat.gcd_dvd_right _ _
  have dd : d=1 := Nat.isUnit_iff.mp (hs d (by
    obtain ⟨x,hx⟩ := da; obtain ⟨y,hy⟩ := db; obtain ⟨z,hz⟩ := dc
    exact ⟨x^2+y^2+z^2,by rw [←h,hx,hy,hz]; ring⟩))
  have e := Nat.gcd_eq_gcd_ab (a.gcd b) c
  change (d:ℤ)=_ at e
  rw [dd,Nat.cast_one,Nat.gcd_eq_gcd_ab a b] at e
  refine ⟨a.gcdA b * (a.gcd b).gcdA c,a.gcdB b * (a.gcd b).gcdA c,(a.gcd b).gcdB c,?_⟩
  dsimp
  linear_combination -e

lemma short_central {v w : Q} (pv : primitive v) (v0 : v.re=0) (comm : w*v=v*w)
    (lt : normSq w < normSq v) : w=(w.re:Q) := by
  obtain ⟨i,j,k,bez⟩ := pv
  let t := i*w.imI+j*w.imJ+k*w.imK
  have ex := congrArg QuaternionAlgebra.imI comm
  have ey := congrArg QuaternionAlgebra.imJ comm
  have ez := congrArg QuaternionAlgebra.imK comm
  simp only [Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul,v0,mul_zero,zero_mul] at ex ey ez
  have ix : w.imJ*v.imK=w.imK*v.imJ := by linarith only [ex]
  have iy : w.imK*v.imI=w.imI*v.imK := by linarith only [ey]
  have iz : w.imI*v.imJ=w.imJ*v.imI := by linarith only [ez]
  have px : w.imI=t*v.imI := by dsimp [t]; linear_combination -w.imI*bez+j*iz-k*iy
  have py : w.imJ=t*v.imJ := by dsimp [t]; linear_combination -w.imJ*bez+k*ix-i*iz
  have pz : w.imK=t*v.imK := by dsimp [t]; linear_combination -w.imK*bez+i*iy-j*ix
  have ht : t=0 := by
    by_contra nz
    have one : 1 ≤ t^2 := by have : 0<t^2 := sq_pos_of_ne_zero nz; omega
    rw [Quaternion.normSq_def' w,Quaternion.normSq_def' v,v0,px,py,pz] at lt
    have hh := mul_le_mul_of_nonneg_right one (show 0 ≤ v.imI^2+v.imJ^2+v.imK^2 by positivity)
    nlinarith only [lt,hh,sq_nonneg w.re]
  rw [ht,zero_mul] at px py pz
  apply Quaternion.ext <;> simp [px,py,pz]

/-- If q divides b+v on the left, its four coordinates are relatively prime. -/
lemma prim_div {v q d r : Q} {b n k : ℤ} (pv : primitive v) (hd : (b:Q)+v=q*d)
    (he : k • q=n • r) : n ∣ k := by
  have eq := congrArg (fun x : Q => x*d) he
  change (k • q)*d=(n • r)*d at eq
  rw [smul_mul_assoc,smul_mul_assoc,←hd] at eq
  obtain ⟨i,j,l,h⟩ := pv
  let z := r*d
  have e1 := congrArg QuaternionAlgebra.imI eq
  have e2 := congrArg QuaternionAlgebra.imJ eq
  have e3 := congrArg QuaternionAlgebra.imK eq
  change k*(0+v.imI)=n*z.imI at e1
  change k*(0+v.imJ)=n*z.imJ at e2
  change k*(0+v.imK)=n*z.imK at e3
  refine ⟨i*z.imI+j*z.imJ+l*z.imK,?_⟩
  linear_combination -k*h+i*e1+j*e2+l*e3

end Grimm338

namespace TernaryOrientation
open Quaternion
abbrev Q := Quaternion ℤ
def mkQ (r x y z : ℤ) : Q := ⟨r,x,y,z⟩
lemma mkQ_mul (a b c d A B C D : ℤ) :
    mkQ a b c d * mkQ A B C D =
    mkQ (a*A-b*B-c*C-d*D) (a*B+b*A+c*D-d*C)
        (a*C-b*D+c*A+d*B) (a*D+b*C-c*B+d*A) :=
  Quaternion.ext _ _ (Quaternion.re_mul _ _) (Quaternion.imI_mul _ _)
    (Quaternion.imJ_mul _ _) (Quaternion.imK_mul _ _)
lemma norm_mkQ (r x y z : ℤ) : normSq (mkQ r x y z)=r^2+x^2+y^2+z^2 :=
  Quaternion.normSq_def' _
def oriented (d : ℕ×ℕ×ℕ) (side : Bool) : Q :=
  if side then mkQ 0 d.2.1 (-(d.1:ℤ)) d.2.2 else mkQ 0 d.1 d.2.1 d.2.2

lemma representative (v : Q) (hz : v.re=0) :
    ∃ (d : ℕ×ℕ×ℕ) (side : Bool) (u : Q), normSq u=1 ∧ v*u=u*oriented d side ∧
      ((d.1^2+d.2.1^2+d.2.2^2:ℕ):ℤ)=normSq v := by
  obtain ⟨r,x,y,z⟩ := v; change r=0 at hz; subst r
  change ∃ d side u, normSq u=1 ∧ mkQ 0 x y z*u=u*oriented d side ∧ _=normSq (mkQ 0 x y z)
  have stage : ∃ (u : Q) (x' y' z' : ℤ), normSq u=1 ∧ 0≤x' ∧ 0≤z' ∧
      mkQ 0 x y z*u=u*mkQ 0 x' y' z' ∧ x'^2+y'^2+z'^2=x^2+y^2+z^2 := by
    by_cases hx : 0≤x <;> by_cases hz : 0≤z
    · exact ⟨1,x,y,z,by simp,hx,hz,by simp,rfl⟩
    · refine ⟨mkQ 0 1 0 0,x,-y,-z,by decide,hx,by omega,?_,by ring⟩
      rw [mkQ_mul,mkQ_mul]; congr 1 <;> ring
    · refine ⟨mkQ 0 0 0 1,-x,-y,z,by decide,by omega,hz,?_,by ring⟩
      rw [mkQ_mul,mkQ_mul]; congr 1 <;> ring
    · refine ⟨mkQ 0 0 1 0,-x,y,-z,by decide,by omega,by omega,?_,by ring⟩
      rw [mkQ_mul,mkQ_mul]; congr 1 <;> ring
  obtain ⟨u,X,Y,Z,hu,hX,hZ,e,f⟩ := stage
  by_cases hY : 0≤Y
  · refine ⟨(X.toNat,Y.toNat,Z.toNat),false,u,hu,?_,?_⟩
    · simpa [oriented,Int.toNat_of_nonneg,hX,hY,hZ] using e
    · push_cast
      rw [norm_mkQ]; simpa [hX,hY,hZ] using f
  · have hn : 0 ≤ -Y := by omega
    refine ⟨((-Y).toNat,X.toNat,Z.toNat),true,u,hu,?_,?_⟩
    · simpa [oriented,Int.toNat_of_nonneg,hX,hn,hZ,max_eq_left hn] using e
    · push_cast
      rw [norm_mkQ]
      simp [hX,max_eq_left hn,hZ]
      linarith only [f]

lemma turn (d : ℕ×ℕ×ℕ) (a b : Bool) : ∃ h : Q, (normSq h=1 ∨ normSq h=2) ∧
    oriented d a*h=h*oriented d b := by
  cases a <;> cases b
  · exact ⟨1,Or.inl (by simp),by simp⟩
  · refine ⟨mkQ 1 0 0 1,Or.inr (by decide),?_⟩
    simp only [oriented, Bool.false_eq_true, if_false, if_true, mkQ_mul]; congr 1 <;> ring
  · refine ⟨mkQ 1 0 0 (-1),Or.inr (by decide),?_⟩
    simp only [oriented, Bool.false_eq_true, if_false, if_true, mkQ_mul]; congr 1 <;> ring
  · exact ⟨1,Or.inl (by simp),by simp⟩

end TernaryOrientation

namespace Grimm338
open Quaternion Finset TunnellQuaternion TernaryOrientation
abbrev Triple := ℕ×ℕ×ℕ

def form (s : ℕ) (f : Triple) : Prop :=
  0 < f.1 ∧ f.2.1 ≤ f.1 ∧ f.1 ≤ f.2.2 ∧ 4*f.1*f.2.2=s+f.2.1^2

lemma form_est {s : ℕ} {f : Triple} (hs : s%8=3) (hf : form s f) :
    f.1%2=1 ∧ 0 < f.2.1 ∧ 3*f.1^2 ≤ s := by
  obtain ⟨ap,ba,ac,eq⟩ := hf
  have tab : ∀ a b c : Fin 8, (4*a.val*c.val)%8=(3+b.val^2)%8 →
      a.val%2=1 ∧ b.val%2=1 := by decide
  have congr8 : (4*(f.1%8)*(f.2.2%8))%8=(3+(f.2.1%8)^2)%8 := by
    have a := Nat.mod_modEq f.1 8
    have b := Nat.mod_modEq f.2.1 8
    have c := Nat.mod_modEq f.2.2 8
    calc
      _ = (4*f.1*f.2.2)%8 := ((Nat.ModEq.refl 4).mul a).mul c
      _ = (s+f.2.1^2)%8 := by rw [eq]
      _ = _ := (show s ≡ 3 [MOD 8] from hs).add (b.pow 2).symm
  obtain ⟨a,b⟩ := tab ⟨_,Nat.mod_lt _ (by decide)⟩ ⟨_,Nat.mod_lt _ (by decide)⟩ ⟨_,Nat.mod_lt _ (by decide)⟩ congr8
  dsimp only at a b
  exact ⟨by omega,by omega,by nlinarith only [eq,Nat.pow_le_pow_left ba 2,Nat.mul_le_mul_left f.1 ac]⟩

structure Witness (v : Grimm338.Q) (f t : Triple) where
  q : Grimm338.Q
  d : Grimm338.Q
  side : Bool
  norm : normSq q=f.1
  divides : (Quaternion.coe (f.2.1:ℤ) : Grimm338.Q)+v=q*d
  intertwine : v*q=q*oriented t side

lemma make_witness {s : ℕ} {v : Grimm338.Q} (v0 : v.re=0) (vn : normSq v=s)
    (hs : s%8=3) (f : Triple) (hf : form s f) :
    ∃ t : Triple, t.1^2+t.2.1^2+t.2.2^2=s ∧ Nonempty (Witness v f t) := by
  obtain ⟨odd,_,_⟩ := form_est hs hf
  let b : ℤ := f.2.1
  let w := (Quaternion.coe b : Grimm338.Q)+v
  have ww : normSq w=b^2+s := by
    simp [w,normSq_def',v0] at vn ⊢
    linarith only [vn]
  have eq : (4:ℤ)*f.1*f.2.2=(s:ℤ)+b^2 := by dsimp only [b]; exact_mod_cast hf.2.2.2
  obtain ⟨q,d,hq,hd⟩ := odd_divisor f.1 hf.1 odd w ⟨4*f.2.2,by rw [ww]; linarith only [eq]⟩
  let y := d*q-(Quaternion.coe b : Grimm338.Q)
  have it : v*q=q*y := by
    have e : v=q*d-(Quaternion.coe b : Grimm338.Q) := by change (Quaternion.coe b : Grimm338.Q)+v=q*d at hd; rw [←hd]; abel
    dsimp only [y]
    rw [e,sub_mul,mul_sub,mul_assoc,coe_mul_eq_smul,mul_coe_eq_smul]
  have y0 : y.re=0 := by
    have e := congrArg QuaternionAlgebra.re hd
    change b+v.re=(q*d).re at e
    change (d*q).re-b=0
    rw [Quaternion.re_mul] at e ⊢
    rw [v0] at e
    linarith only [e]
  have yn : normSq y=s := by
    have e := congrArg normSq it
    simp only [map_mul,hq,vn] at e
    have ap : (0:ℤ) < f.1 := by exact_mod_cast hf.1
    rw [mul_comm (s:ℤ)] at e
    exact (mul_left_cancel₀ ap.ne' e).symm
  obtain ⟨t,side,u,un,ue,te⟩ := representative y y0
  have prod : u*star u=1 := by rw [self_mul_star,un]; rfl
  refine ⟨t,by exact_mod_cast te.trans yn,⟨⟨q*u,star u*d,side,by simp [hq,un],?_,?_⟩⟩⟩
  · change w=_
    rw [hd,mul_assoc,←mul_assoc u,prod,one_mul]
  · rw [←mul_assoc,it,mul_assoc,ue,mul_assoc]

lemma equal_shift {v q d d' : Grimm338.Q} {a b c : ℤ} (pv : primitive v)
    (h : normSq q=a) (hb : (Quaternion.coe b : Grimm338.Q)+v=q*d) (hc : (Quaternion.coe c : Grimm338.Q)+v=q*d') : a ∣ b-c := by
  have diff : (Quaternion.coe (b-c) : Grimm338.Q)=q*(d-d') := by rw [mul_sub,←hb,←hc,Quaternion.coe_sub]; abel
  have e := congrArg (fun w : Grimm338.Q => star q*w) diff
  change star q * (Quaternion.coe (b-c) : Grimm338.Q)=star q*(q*(d-d')) at e
  rw [mul_coe_eq_smul,←mul_assoc,star_mul_self,h,coe_mul_eq_smul] at e
  have e' := congrArg star e
  simp only [Quaternion.star_smul,star_star] at e'
  exact prim_div pv hb e'

lemma witness_inj {s : ℕ} {v : Grimm338.Q} {f g t : Triple}
    (sf : s%8=3) (pv : primitive v) (v0 : v.re=0) (vn : normSq v=s)
    (ff : form s f) (gf : form s g) (F : Witness v f t) (G : Witness v g t) : f=g := by
  obtain ⟨od,bp,fb⟩ := form_est sf ff
  obtain ⟨od',bp',gb⟩ := form_est sf gf
  have apos := ff.1
  have gpos := gf.1
  obtain ⟨h,nh,turn⟩ := TernaryOrientation.turn t F.side G.side
  let Y := oriented t G.side
  have y0 : Y.re=0 := by dsimp only [Y,oriented]; split <;> rfl
  have gs := congrArg star G.intertwine
  change star (v*G.q)=star (G.q*Y) at gs
  rw [star_mul,star_mul,Quaternion.star_eq_neg.mpr v0,Quaternion.star_eq_neg.mpr y0,mul_neg,neg_mul,neg_inj] at gs
  let w := F.q*h*star G.q
  have comm : w*v=v*w := by
    calc w*v = F.q*(h*(star G.q*v)) := by simp [w,mul_assoc]
         _ = F.q*(h*(Y*star G.q)) := by rw [gs]
         _ = (F.q*(oriented t F.side*h))*star G.q := by rw [←mul_assoc h,←turn]; simp [mul_assoc]
         _ = v*w := by simp only [w,←mul_assoc,F.intertwine]
  have wn : normSq w=(f.1:ℤ)*normSq h*g.1 := by simp [w,F.norm,G.norm]
  have bound : 2*f.1*g.1 < s := by
    have sqp : 0 < (f.1:ℤ)^2 := by positivity
    zify at fb gb ⊢
    nlinarith only [fb,gb,sq_nonneg ((f.1:ℤ)-(g.1:ℤ)),sqp]
  have lt : normSq w < normSq v := by
    rw [vn,wn]
    have bb : (2:ℤ)*f.1*g.1 < s := by exact_mod_cast bound
    rcases nh with e|e <;> rw [e] <;> nlinarith [mul_nonneg (Int.natCast_nonneg f.1) (Int.natCast_nonneg g.1)]
  let r := w.re
  have wr : w=(Quaternion.coe r : Grimm338.Q) := short_central pv v0 comm lt
  have rn : r^2=(f.1:ℤ)*normSq h*g.1 := by rw [←wn,wr,normSq_coe]
  have one : normSq h=1 := by
    rcases nh with z|z
    · exact z
    · rw [z] at rn
      have E : ((r%4)^2)%4=2 := by
        have modpow : ((r%4)^2)%4=r^2%4 := (Int.mod_modEq r 4).pow 2
        rw [modpow, rn]
        have fodd : (f.1:ℤ)%2=1 := by exact_mod_cast od
        have godd : (g.1:ℤ)%2=1 := by exact_mod_cast od'
        obtain ⟨i,ei⟩ : ∃ i:ℤ,(f.1:ℤ)=2*i+1 := ⟨f.1/2,by omega⟩
        obtain ⟨j,ej⟩ : ∃ j:ℤ,(g.1:ℤ)=2*j+1 := ⟨g.1/2,by omega⟩
        rw [ei,ej,show (2*i+1)*2*(2*j+1)=4*(2*i*j+i+j)+2 by ring]
        omega
      have hh := Int.emod_nonneg r (by decide : (4:ℤ)≠0)
      have hh' := Int.emod_lt_of_pos r (by decide : (0:ℤ) < 4)
      interval_cases r%4 <;> norm_num at E
  have rel : r • G.q=(g.1:ℤ) • (F.q*h) := by
    rw [←coe_mul_eq_smul,←wr]
    change (F.q*h*star G.q)*G.q=_
    rw [mul_assoc,star_mul_self,G.norm,mul_coe_eq_smul]
  have divg := prim_div pv G.divides rel
  have rel2 : r • F.q=(f.1:ℤ) • (G.q*star h) := by
    have bar := congrArg star wr
    change star ((F.q*h)*star G.q)=star (Quaternion.coe r : Grimm338.Q) at bar
    simp only [star_mul,star_star,Quaternion.star_coe] at bar
    rw [←coe_mul_eq_smul,←bar]
    simp only [mul_assoc,star_mul_self,F.norm,mul_coe_eq_smul,Algebra.mul_smul_comm]
  have divf := prim_div pv F.divides rel2
  rw [one,mul_one] at rn
  have rn' : r.natAbs^2=f.1*g.1 := by
    zify; rw [sq_abs]; exact rn
  have rp : 0 < r.natAbs := by
    by_contra! hz
    have e : r.natAbs=0 := by omega
    simp [e,apos.ne',gpos.ne'] at rn'
  have d1 : f.1 ∣ r.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr divf
  have d2 : g.1 ∣ r.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr divg
  have p1 := Nat.le_of_dvd rp d1
  have p2 := Nat.le_of_dvd rp d2
  have ee : r.natAbs=f.1 ∧ r.natAbs=g.1 := by
    constructor
    · by_contra ne
      have l := (Nat.mul_le_mul_left f.1 p2).trans_lt (Nat.mul_lt_mul_of_pos_right (show f.1 < r.natAbs by omega) rp)
      nlinarith only [rn',l]
    · by_contra ne
      have l := (Nat.mul_le_mul_right g.1 p1).trans_lt (Nat.mul_lt_mul_of_pos_left (show g.1 < r.natAbs by omega) rp)
      nlinarith only [rn',l]
  have ag : f.1=g.1 := ee.1.symm.trans ee.2
  have sign : r=(g.1:ℤ) ∨ r= -(g.1:ℤ) := Int.natAbs_eq_natAbs_iff.mp (by simpa using ee.2)
  have left : ∃ d', (Quaternion.coe (g.2.1:ℤ) : Grimm338.Q)+v=F.q*d' := by
    have ng : (g.1:ℤ) ≠ 0 := by exact_mod_cast gpos.ne'
    rcases sign with e|e
    · rw [e] at rel
      have u := scalar_cancel (g.1:ℤ) ng rel
      exact ⟨h*G.d,by rw [G.divides,u,mul_assoc]⟩
    · rw [e,neg_smul,←smul_neg] at rel
      have u := scalar_cancel (g.1:ℤ) ng rel
      exact ⟨-(h*G.d),by rw [G.divides,←neg_neg G.q,u,neg_mul,mul_neg,mul_assoc]⟩
  obtain ⟨d',hd'⟩ := left
  have dv := equal_shift pv F.norm F.divides hd'
  have b1 := ff.2.1
  have b2 := gf.2.1
  have b : f.2.1=g.2.1 := by
    obtain ⟨k,hk⟩ := dv
    have abs1 : |(f.2.1:ℤ)-g.2.1| < (f.1:ℤ) := by rw [abs_lt]; omega
    rw [hk,abs_mul,abs_of_nonneg (Int.natCast_nonneg _)] at abs1
    have hk0 : k=0 := by
      by_contra hn
      have h1 : 1 ≤ |k| := by have := abs_pos.mpr hn; omega
      nlinarith only [abs1,mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg f.1)]
    simp [hk0] at hk
    omega
  have e1 := ff.2.2.2
  have e2 := gf.2.2.2
  rw [←ag,←b] at e2
  exact Prod.ext ag (Prod.ext b (Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 4*f.1) (e1.trans e2.symm)))

end Grimm338

/-! The following three-square proof in namespace Nat is adapted from ATLAS,
MathlibExt/NumberTheory/QuadraticForms/LegendreThreeSquare.lean, commit
dcb77c85757e945810657e5dce688ae82ff8eb25. The module header was removed
and conditional rewrite lemmas were updated for this Mathlib version.

Source: https://github.com/Deicyde/atlas-lean/blob/dcb77c85757e945810657e5dce688ae82ff8eb25/MathlibExt/NumberTheory/QuadraticForms/LegendreThreeSquare.lean
Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
The upstream license is reproduced at the end of this file.
-/

namespace Nat

/-- Divisibility step of Ankeny's proof: a small nonzero lattice value divisible
by both `m` and `k` (which are coprime since `m ∣ k + 1`) and below `2 * m * k`
must equal `m * k`. -/
private theorem ankeny_lattice_value_eq {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hmk : m ∣ k + 1) {b : ℤ} (hb : (k : ℤ) ∣ b ^ 2 + (m : ℤ))
    {R X T : ℤ} (hne : ¬ (R = 0 ∧ X = 0 ∧ T = 0))
    (hRX : (m : ℤ) ∣ R - X) (hXT : (k : ℤ) ∣ X - b * T)
    (hlt : (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 < 2 * (m : ℤ) * (k : ℤ)) :
    (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 = (m : ℤ) * (k : ℤ) := by
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hVnn : (0 : ℤ) ≤ (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 := by
    positivity
  have hVne : (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 ≠ 0 := by
    intro hV0
    have e1 : (0 : ℤ) ≤ (k : ℤ) * R ^ 2 := by positivity
    have e2 : (0 : ℤ) ≤ X ^ 2 := by positivity
    have e3 : (0 : ℤ) ≤ (m : ℤ) * T ^ 2 := by positivity
    have g1 : (k : ℤ) * R ^ 2 = 0 := le_antisymm (by linarith) e1
    have g2 : X ^ 2 = 0 := le_antisymm (by linarith) e2
    have g3 : (m : ℤ) * T ^ 2 = 0 := le_antisymm (by linarith) e3
    obtain ⟨hR, hX, hT⟩ : (k : ℤ) * R ^ 2 = 0 ∧ X ^ 2 = 0 ∧ (m : ℤ) * T ^ 2 = 0 :=
      ⟨g1, g2, g3⟩
    have hR0 : R = 0 := by
      by_contra hR
      have hpos2 : (0 : ℤ) < (k : ℤ) * R ^ 2 :=
        mul_pos hkZ (sq_pos_of_ne_zero hR)
      linarith
    have hX0 : X = 0 := by
      by_contra hX
      have hpos : (0 : ℤ) < X ^ 2 := sq_pos_of_ne_zero hX
      linarith
    have hT0 : T = 0 := by
      by_contra hT
      have hpos2 : (0 : ℤ) < (m : ℤ) * T ^ 2 :=
        mul_pos hmZ (sq_pos_of_ne_zero hT)
      linarith
    exact hne ⟨hR0, hX0, hT0⟩
  have hVpos : (0 : ℤ) < (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 :=
    lt_of_le_of_ne hVnn (Ne.symm hVne)
  -- `k` divides the value, via `X ≡ b * T`.
  have hX : b * T ≡ X [ZMOD (k : ℤ)] := Int.modEq_iff_dvd.mpr hXT
  have hkV : (k : ℤ) ∣ (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 := by
    have e1 : (b * T) ^ 2 ≡ X ^ 2 [ZMOD (k : ℤ)] := hX.pow 2
    have e2 : (b * T) ^ 2 + (m : ℤ) * T ^ 2 ≡ X ^ 2 + (m : ℤ) * T ^ 2
        [ZMOD (k : ℤ)] := e1.add_right _
    have hrr : (b * T) ^ 2 + (m : ℤ) * T ^ 2 = (b ^ 2 + (m : ℤ)) * T ^ 2 := by
      ring
    rw [hrr] at e2
    have hzero : (b ^ 2 + (m : ℤ)) * T ^ 2 ≡ 0 [ZMOD (k : ℤ)] :=
      Int.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hb _)
    have hfin : X ^ 2 + (m : ℤ) * T ^ 2 ≡ 0 [ZMOD (k : ℤ)] := e2.symm.trans hzero
    have hdvd : (k : ℤ) ∣ X ^ 2 + (m : ℤ) * T ^ 2 := by
      have h := hfin.dvd
      rwa [zero_sub, dvd_neg] at h
    have h1 : (k : ℤ) ∣ (k : ℤ) * R ^ 2 := dvd_mul_right _ _
    have h := h1.add hdvd
    rwa [← add_assoc] at h
  -- `m` divides the value, via `R ≡ X` and `k + 1 ≡ 0`.
  have hR : X ≡ R [ZMOD (m : ℤ)] := Int.modEq_iff_dvd.mpr hRX
  have hmV : (m : ℤ) ∣ (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 := by
    have e1 : (k : ℤ) * X ^ 2 ≡ (k : ℤ) * R ^ 2 [ZMOD (m : ℤ)] :=
      (Int.ModEq.refl _).mul (hR.pow 2)
    have hmid : (k : ℤ) * X ^ 2 + X ^ 2 ≡ (k : ℤ) * R ^ 2 + X ^ 2
        [ZMOD (m : ℤ)] := e1.add (Int.ModEq.refl _)
    have hring : (k : ℤ) * X ^ 2 + X ^ 2 = ((k : ℤ) + 1) * X ^ 2 := by ring
    rw [hring] at hmid
    have hkm : ((k : ℤ) + 1) * X ^ 2 ≡ 0 [ZMOD (m : ℤ)] := by
      have hcast : (m : ℤ) ∣ ((k : ℤ) + 1) := by exact_mod_cast hmk
      exact Int.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hcast _)
    have hfin : (k : ℤ) * R ^ 2 + X ^ 2 ≡ 0 [ZMOD (m : ℤ)] :=
      hmid.symm.trans hkm
    have hdvd : (m : ℤ) ∣ (k : ℤ) * R ^ 2 + X ^ 2 := by
      have h := hfin.dvd
      rwa [zero_sub, dvd_neg] at h
    have h2 : (m : ℤ) ∣ (m : ℤ) * T ^ 2 := dvd_mul_right _ _
    exact hdvd.add h2
  -- `(m : ℤ)` and `(k : ℤ)` are coprime since `m ∣ k + 1`, so their product
  -- divides the value.
  have hiso : IsCoprime (m : ℤ) (k : ℤ) := by
    obtain ⟨t, ht⟩ := hmk
    refine ⟨(t : ℤ), -1, ?_⟩
    have h2 : ((k + 1 : ℕ) : ℤ) = ((m * t : ℕ) : ℤ) := by exact_mod_cast ht
    push_cast at h2
    linear_combination -h2
  have hmkV : (m : ℤ) * (k : ℤ)
      ∣ (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 := hiso.mul_dvd hmV hkV
  have hmkZ : (0 : ℤ) < (m : ℤ) * (k : ℤ) := mul_pos hmZ hkZ
  obtain ⟨j, hj⟩ := hmkV
  have hjpos : 0 < j := by
    by_contra h
    push Not at h
    have hle : (m : ℤ) * (k : ℤ) * j ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hmkZ) h
    linarith
  have hjlt : j < 2 := by
    by_contra h
    push Not at h
    have hle : 2 * ((m : ℤ) * (k : ℤ)) ≤ (m : ℤ) * (k : ℤ) * j := by
      calc 2 * ((m : ℤ) * (k : ℤ)) = ((m : ℤ) * (k : ℤ)) * 2 := by ring
        _ ≤ ((m : ℤ) * (k : ℤ)) * j :=
          mul_le_mul_of_nonneg_left h (le_of_lt hmkZ)
    linarith
  have hj1 : j = 1 := by omega
  rw [hj1, mul_one] at hj
  exact hj

/-- Valuation step: if `-d` is not a square in `ZMod p`, then every value of
`X ^ 2 + d * T ^ 2` has even `p`-adic valuation. -/
private theorem even_padicValInt_sq_add_mul_sq_of_not_isSquare {p : ℕ} [Fact p.Prime]
    {d : ℤ} (hd : ¬ IsSquare (-(d : ZMod p))) (X T : ℤ) :
    Even (padicValInt p (X ^ 2 + d * T ^ 2)) := by
  have hp2 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpZ : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have key : ∀ N : ℕ, ∀ X T : ℤ, X.natAbs + T.natAbs = N →
      Even (padicValInt p (X ^ 2 + d * T ^ 2)) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro X T hNT
      by_cases h0 : X ^ 2 + d * T ^ 2 = 0
      · rw [h0, padicValInt.zero]
        exact ⟨0, rfl⟩
      by_cases hdvd : (p : ℤ) ∣ X ^ 2 + d * T ^ 2
      · have hT : (p : ℤ) ∣ T := by
          by_contra hT
          have hTz : (T : ZMod p) ≠ 0 := fun hz =>
            hT ((ZMod.intCast_zmod_eq_zero_iff_dvd T p).mp hz)
          have hcast : (X : ZMod p) ^ 2 + (d : ZMod p) * (T : ZMod p) ^ 2 = 0 := by
            have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
            push_cast at h
            exact h
          set x : ZMod p := (X : ZMod p) with hx
          set t : ZMod p := (T : ZMod p) with ht
          set δ : ZMod p := (d : ZMod p) with hδ
          have hx2 : x ^ 2 = -(δ * t ^ 2) := by linear_combination hcast
          have e2 : (t⁻¹) ^ 2 * t ^ 2 = 1 := by
            rw [← mul_pow, inv_mul_cancel₀ hTz, one_pow]
          have e3 : -(δ * t ^ 2) * (t⁻¹) ^ 2 = -δ := by
            have e4 : -(δ * t ^ 2) * (t⁻¹) ^ 2 = -δ * ((t⁻¹) ^ 2 * t ^ 2) := by
              ring
            rw [e4, e2, mul_one]
          have hsq : -(δ) = (x * t⁻¹) * (x * t⁻¹) := by
            have e : (x * t⁻¹) * (x * t⁻¹) = x ^ 2 * (t⁻¹) ^ 2 := by ring
            rw [e, hx2, e3]
          exact hd ⟨x * t⁻¹, hsq⟩
        have hT2 : (p : ℤ) ∣ d * T ^ 2 :=
          dvd_mul_of_dvd_right (dvd_pow hT two_ne_zero) _
        have hX2 : (p : ℤ) ∣ X ^ 2 := (dvd_add_left hT2).mp hdvd
        have hX : (p : ℤ) ∣ X := hpZ.dvd_of_dvd_pow hX2
        obtain ⟨X', hX'⟩ := hX
        obtain ⟨T', hT'⟩ := hT
        have hfactor : X ^ 2 + d * T ^ 2
            = (p : ℤ) ^ 2 * (X' ^ 2 + d * T' ^ 2) := by
          rw [hX', hT']
          ring
        have hSne : X' ^ 2 + d * T' ^ 2 ≠ 0 := by
          intro hcon
          apply h0
          rw [hfactor, hcon, mul_zero]
        have hpp : padicValInt p ((p : ℤ) ^ 2) = 2 := by
          have h1 : (p : ℤ) ^ 2 = (p : ℤ) * (p : ℤ) := by ring
          have hp0 : (p : ℤ) ≠ 0 := by
            have := hp2
            omega
          rw [h1, padicValInt.mul hp0 hp0, padicValInt.self hp2]
        have hval : padicValInt p (X ^ 2 + d * T ^ 2)
            = 2 + padicValInt p (X' ^ 2 + d * T' ^ 2) := by
          rw [hfactor, padicValInt.mul (by positivity) hSne, hpp]
        have eX : X.natAbs = p * X'.natAbs := by
          rw [hX', Int.natAbs_mul, Int.natAbs_natCast]
        have eT : T.natAbs = p * T'.natAbs := by
          rw [hT', Int.natAbs_mul, Int.natAbs_natCast]
        have hXle : X'.natAbs ≤ X.natAbs := by
          rw [eX]
          exact le_mul_of_one_le_left (Nat.zero_le _) hp2.le
        have hTle : T'.natAbs ≤ T.natAbs := by
          rw [eT]
          exact le_mul_of_one_le_left (Nat.zero_le _) hp2.le
        have hne00 : X ≠ 0 ∨ T ≠ 0 := by
          by_contra hcon
          push Not at hcon
          apply h0
          rw [hcon.1, hcon.2]
          simp
        have hltN : X'.natAbs + T'.natAbs < N := by
          have hXlt : X ≠ 0 → X'.natAbs < X.natAbs := by
            intro hneX
            have hneX' : X' ≠ 0 := by
              intro hcon
              apply hneX
              rw [hX', hcon, mul_zero]
            rw [eX]
            have hpos : 0 < X'.natAbs := Int.natAbs_pos.mpr hneX'
            calc X'.natAbs = 1 * X'.natAbs := (one_mul _).symm
              _ < p * X'.natAbs := by
                rw [one_mul]
                exact lt_mul_of_one_lt_left hpos hp2
          have hTlt : T ≠ 0 → T'.natAbs < T.natAbs := by
            intro hneT
            have hneT' : T' ≠ 0 := by
              intro hcon
              apply hneT
              rw [hT', hcon, mul_zero]
            rw [eT]
            have hpos : 0 < T'.natAbs := Int.natAbs_pos.mpr hneT'
            calc T'.natAbs = 1 * T'.natAbs := (one_mul _).symm
              _ < p * T'.natAbs := by
                rw [one_mul]
                exact lt_mul_of_one_lt_left hpos hp2
          rcases hne00 with hneX | hneT
          · have := hXlt hneX
            omega
          · have := hTlt hneT
            omega
        have ihE := ih _ hltN X' T' rfl
        rw [hval]
        obtain ⟨r, hr⟩ := ihE
        exact ⟨r + 1, by omega⟩
      · rw [padicValInt.eq_zero_of_not_dvd hdvd]
        exact ⟨0, rfl⟩
  exact key _ X T rfl

/-- Two-square step: from `m = R ^ 2 + N` and `k * N = X ^ 2 + m * T ^ 2`,
with `m` squarefree and no prime factor of `k` congruent to `3 mod 4`,
conclude `N` is a sum of two natural squares. -/
private theorem ankeny_exists_two_sq_of_rep {m k : ℕ} (hm : Squarefree m)
    (hk : 0 < k) (hmk : m ∣ k + 1)
    (hk4 : ∀ p : ℕ, p.Prime → p ∣ k → p % 4 ≠ 3)
    {R X T : ℤ} {N : ℕ} (hRm : (m : ℤ) = R ^ 2 + (N : ℤ))
    (hrep : (k : ℤ) * (N : ℤ) = X ^ 2 + (m : ℤ) * T ^ 2) :
    ∃ a c : ℕ, N = a ^ 2 + c ^ 2 := by
  by_cases hN0 : N = 0
  · subst hN0
    exact ⟨0, 0, by simp⟩
  rw [Nat.eq_sq_add_sq_iff]
  intro q hq hq4
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqdvdN : q ∣ N := Nat.dvd_of_mem_primeFactors hq
  have : Fact q.Prime := ⟨hqprime⟩
  have hpZq : _root_.Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hqprime
  have hqN : (q : ℤ) ∣ (N : ℤ) := by exact_mod_cast hqdvdN
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hqprime.ne_zero
  by_cases hqm : (q : ℤ) ∣ (m : ℤ)
  · -- Case `q ∣ m`: derive a contradiction from `-1` being a square mod `q`.
    have hqmN : q ∣ m := Int.natCast_dvd_natCast.mp hqm
    have hqk1 : q ∣ k + 1 := dvd_trans hqmN hmk
    rcases hqmN with ⟨m₁, hm₁⟩
    have hqm1 : ¬ q ∣ m₁ := by
      intro hd
      obtain ⟨t, ht⟩ := hd
      have hqq : q * q ∣ m := ⟨t, by rw [hm₁, ht]; ring⟩
      exact (Nat.squarefree_iff_prime_squarefree.mp hm) q hqprime hqq
    have hR2 : (q : ℤ) ∣ R ^ 2 := by
      have e : R ^ 2 = (m : ℤ) - (N : ℤ) := by omega
      rw [e]
      obtain ⟨a, ha⟩ := hqm
      obtain ⟨b, hb⟩ := hqN
      exact ⟨a - b, by linear_combination ha - hb⟩
    have hR : (q : ℤ) ∣ R := hpZq.dvd_of_dvd_pow hR2
    have hX2 : (q : ℤ) ∣ X ^ 2 := by
      have e : X ^ 2 = (k : ℤ) * (N : ℤ) - (m : ℤ) * T ^ 2 := by omega
      rw [e]
      obtain ⟨a, ha⟩ := dvd_mul_of_dvd_right hqN ((k : ℤ))
      obtain ⟨b, hb⟩ := dvd_mul_of_dvd_right hqm (T ^ 2)
      exact ⟨a - b, by linear_combination ha - hb⟩
    have hX : (q : ℤ) ∣ X := hpZq.dvd_of_dvd_pow hX2
    obtain ⟨R₁, hR₁⟩ := hR
    obtain ⟨X₁, hX₁⟩ := hX
    obtain ⟨N₁, hN₁⟩ := hqdvdN
    have hdiv : (k : ℤ) * (N₁ : ℤ) = (q : ℤ) * X₁ ^ 2 + (m₁ : ℤ) * T ^ 2 := by
      have h := hrep
      rw [hN₁, hm₁, hX₁] at h
      push_cast at h
      have h2 : ((k : ℤ) * (N₁ : ℤ)) * (q : ℤ)
          = ((q : ℤ) * X₁ ^ 2 + (m₁ : ℤ) * T ^ 2) * (q : ℤ) := by
        linear_combination h
      exact mul_right_cancel₀ hq0 h2
    have hNm : (N₁ : ℤ) = (m₁ : ℤ) - (q : ℤ) * R₁ ^ 2 := by
      have h := hRm
      rw [hN₁, hm₁, hR₁] at h
      push_cast at h
      have hcan : ((m₁ : ℤ) - (N₁ : ℤ)) * (q : ℤ)
          = ((q : ℤ) * R₁ ^ 2) * (q : ℤ) := by
        linear_combination h
      have hcan2 := mul_right_cancel₀ hq0 hcan
      omega
    have hdivZ : (k : ZMod q) * ((N₁ : ℕ) : ZMod q)
        = ((m₁ : ℕ) : ZMod q) * (T : ZMod q) ^ 2 := by
      have h := congrArg (fun z : ℤ => (z : ZMod q)) hdiv
      simpa using h
    have hNmZ : ((N₁ : ℕ) : ZMod q) = ((m₁ : ℕ) : ZMod q) := by
      have h := congrArg (fun z : ℤ => (z : ZMod q)) hNm
      simpa using h
    rw [hNmZ] at hdivZ
    have hm1z : ((m₁ : ℕ) : ZMod q) ≠ 0 := by
      intro hz
      apply hqm1
      have hz' : ((((m₁ : ℕ)) : ℤ) : ZMod q) = 0 := by exact_mod_cast hz
      have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hz'
      exact Int.natCast_dvd_natCast.mp hdvd
    have hkT : (k : ZMod q) = (T : ZMod q) ^ 2 := by
      have h := hdivZ
      rw [mul_comm ((m₁ : ℕ) : ZMod q) _] at h
      exact mul_right_cancel₀ hm1z h
    have hk1 : ((k : ℕ) : ZMod q) = -1 := by
      have hdvd : (q : ℤ) ∣ ((k : ℕ) : ℤ) + 1 := by exact_mod_cast hqk1
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hdvd
      have hz2 : ((k : ℕ) : ZMod q) + 1 = 0 := by
        simpa using hz
      linear_combination hz2
    have hsqN : IsSquare (-1 : ZMod q) := ⟨(T : ZMod q), by rw [← hk1, hkT, pow_two]⟩
    exact absurd hq4 (ZMod.exists_sq_eq_neg_one_iff.mp hsqN)
  · -- Case `¬ q ∣ m`: the valuation of `N` is even.
    have hqmB : ¬ q ∣ m := fun hd => hqm (by exact_mod_cast hd)
    have hqk : ¬ q ∣ k := fun hd => (hk4 q hqprime hd) hq4
    have hNq : ((N : ℕ) : ZMod q) = 0 := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hqN
      exact_mod_cast h
    have hRmZ : ((m : ℕ) : ZMod q) = (R : ZMod q) ^ 2 + ((N : ℕ) : ZMod q) := by
      have h := congrArg (fun z : ℤ => (z : ZMod q)) hRm
      simpa using h
    have hnsqB : ¬ IsSquare (-((((m : ℕ)) : ℤ) : ZMod q)) := by
      intro hs
      have hRz : (R : ZMod q) ≠ 0 := by
        intro hz
        apply hqmB
        have h : ((m : ℕ) : ZMod q) = 0 := by
          rw [hRmZ, hz, hNq]
          simp
        have h' : ((((m : ℕ)) : ℤ) : ZMod q) = 0 := by exact_mod_cast h
        have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'
        exact Int.natCast_dvd_natCast.mp hdvd
      obtain ⟨s, hs⟩ := hs
      have hRmz : (R : ZMod q) ^ 2 = ((((m : ℕ)) : ℤ) : ZMod q) := by
        have h := hRmZ
        rw [hNq, add_zero] at h
        exact_mod_cast h.symm
      have hsq1 : (-1 : ZMod q)
          = (s * (R : ZMod q)⁻¹) * (s * (R : ZMod q)⁻¹) := by
        have eR : (R : ZMod q) * (R : ZMod q)⁻¹ = 1 := mul_inv_cancel₀ hRz
        have e : (s * (R : ZMod q)⁻¹) * (s * (R : ZMod q)⁻¹)
            = (s * s) * ((R : ZMod q)⁻¹ * (R : ZMod q)⁻¹) := by ring
        have e3 : ((R : ZMod q)⁻¹ * (R : ZMod q)⁻¹) * (R : ZMod q) ^ 2 = 1 := by
          have e4 : ((R : ZMod q)⁻¹ * (R : ZMod q)⁻¹) * (R : ZMod q) ^ 2
              = ((R : ZMod q) * (R : ZMod q)⁻¹) ^ 2 := by ring
          rw [e4, eR, one_pow]
        have e6 : -((R : ZMod q) ^ 2) * ((R : ZMod q)⁻¹ * (R : ZMod q)⁻¹)
            = -1 := by
          have e7 : -((R : ZMod q) ^ 2) * ((R : ZMod q)⁻¹ * (R : ZMod q)⁻¹)
              = -(((R : ZMod q)⁻¹ * (R : ZMod q)⁻¹) * (R : ZMod q) ^ 2) := by
            ring
          rw [e7, e3]
        rw [e, ← hs, ← hRmz]
        exact e6.symm
      exact (ZMod.exists_sq_eq_neg_one_iff.mp ⟨_, hsq1⟩) hq4
    have hmul : padicValInt q ((k : ℤ) * (N : ℤ))
        = padicValNat q k + padicValNat q N := by
      have hk0 : (k : ℤ) ≠ 0 := by
        have := hk
        omega
      have hN0' : (N : ℤ) ≠ 0 := by
        have := hN0
        omega
      rw [padicValInt.mul hk0 hN0', padicValInt.of_nat, padicValInt.of_nat]
    have heven := even_padicValInt_sq_add_mul_sq_of_not_isSquare (p := q) hnsqB X T
    rw [← hrep, hmul, padicValNat.eq_zero_of_not_dvd hqk, zero_add] at heven
    exact heven

/-- Jacobi step, case `m ≡ 1 (mod 4)`: `-m` is a nonzero square in `ZMod q`. -/
private theorem isSquare_neg_of_one_mod_four_case {q m : ℕ} [Fact q.Prime]
    (hq : q % 4 = 1) (hm : m % 4 = 1) (hdvd : m ∣ q + 1) :
    IsSquare (-((m : ℕ) : ZMod q)) ∧ (-((m : ℕ) : ZMod q)) ≠ 0 := by
  have hqprime : q.Prime := Fact.out
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
  have h2q := hqprime.two_le
  -- `q` does not divide `m`.
  have hqm0 : ((m : ℕ) : ZMod q) ≠ 0 := by
    intro hz
    have hdvdZ : (q : ℤ) ∣ ((m : ℕ) : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast hz)
    have hdvdN : q ∣ m := Int.natCast_dvd_natCast.mp hdvdZ
    obtain ⟨s, hs⟩ := hdvd
    rcases hdvdN with ⟨t, ht⟩
    have hqq1 : q ∣ q + 1 := ⟨t * s, by rw [hs, ht]; ring⟩
    have hqq1Z : (q : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast hqq1
    have hq1Z : (q : ℤ) ∣ 1 := by
      obtain ⟨a, ha⟩ := hqq1Z
      exact ⟨a - 1, by linear_combination ha⟩
    have hq1 : q ∣ 1 := Int.natCast_dvd_natCast.mp hq1Z
    have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hq1
    omega
  -- `q ≡ -1 (mod m)` as integers.
  have hmod : (q : ℤ) % ((m : ℕ) : ℤ) = (-1 : ℤ) % ((m : ℕ) : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have hcast : ((m : ℕ) : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast hdvd
    have h0 : ((q : ℤ) + 1) % ((m : ℕ) : ℤ) = 0 := Int.emod_eq_zero_of_dvd hcast
    have heq : (q : ℤ) - (-1) = (q : ℤ) + 1 := by ring
    rw [heq]
    exact h0
  have hchiq : ZMod.χ₄ (↑q : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four hq
  have hchim : ZMod.χ₄ (↑m : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four hm
  have hleg : legendreSym q (-((m : ℕ) : ℤ)) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.neg _ hqodd, hchiq, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four hm hqodd,
      jacobiSym.mod_left' hmod, jacobiSym.at_neg_one hmodd, hchim]
  have hne' : (Int.cast (-((m : ℕ) : ℤ)) : ZMod q) ≠ 0 := by
    intro h
    apply hqm0
    have h3 := h
    simp only [Int.cast_neg, Int.cast_natCast, neg_eq_zero] at h3
    exact h3
  have hsq : IsSquare (-((m : ℕ) : ZMod q)) := by
    have h := (legendreSym.eq_one_iff q hne').mp hleg
    simpa using h
  exact ⟨hsq, by simpa using hqm0⟩

/-- Jacobi step, case `m ≡ 3 (mod 8)`: `-m` is a nonzero square in `ZMod q`. -/
private theorem isSquare_neg_of_three_mod_eight_case {q m : ℕ} [Fact q.Prime]
    (hq : q % 4 = 1) (hm : m % 8 = 3) (hdvd : m ∣ 2 * q + 1) :
    IsSquare (-((m : ℕ) : ZMod q)) ∧ (-((m : ℕ) : ZMod q)) ≠ 0 := by
  have hqprime : q.Prime := Fact.out
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
  have h2q := hqprime.two_le
  -- `q` does not divide `m`.
  have hqm0 : ((m : ℕ) : ZMod q) ≠ 0 := by
    intro hz
    have hdvdZ : (q : ℤ) ∣ ((m : ℕ) : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast hz)
    have hdvdN : q ∣ m := Int.natCast_dvd_natCast.mp hdvdZ
    obtain ⟨s, hs⟩ := hdvd
    rcases hdvdN with ⟨t, ht⟩
    have hqq1 : q ∣ 2 * q + 1 := ⟨t * s, by rw [hs, ht]; ring⟩
    have hqq1Z : (q : ℤ) ∣ 2 * (q : ℤ) + 1 := by exact_mod_cast hqq1
    have hq1Z : (q : ℤ) ∣ 1 := by
      obtain ⟨a, ha⟩ := hqq1Z
      exact ⟨a - 2, by linear_combination ha⟩
    have hq1 : q ∣ 1 := Int.natCast_dvd_natCast.mp hq1Z
    have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hq1
    omega
  -- `-2 * q ≡ 1 (mod m)` as integers.
  have hmod2 : (-2 * (q : ℤ)) % ((m : ℕ) : ℤ) = (1 : ℤ) % ((m : ℕ) : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have hdvd2 : ((m : ℕ) : ℤ) ∣ (-2 * (q : ℤ)) - 1 := by
      have hcast : ((m : ℕ) : ℤ) ∣ 2 * (q : ℤ) + 1 := by exact_mod_cast hdvd
      obtain ⟨a, ha⟩ := hcast
      exact ⟨-a, by linear_combination -ha⟩
    exact Int.emod_eq_zero_of_dvd hdvd2
  have hchiq : ZMod.χ₄ (↑q : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four hq
  have hchi8 : ZMod.χ₈' (↑m : ZMod 8) = 1 := by
    rw [ZMod.χ₈'_nat_eq_if_mod_eight, if_neg (by omega : ¬ m % 2 = 0),
      if_pos (Or.inr hm)]
  have hJq : jacobiSym ((q : ℤ)) m = 1 := by
    have h2q1 : jacobiSym (-2 * (q : ℤ)) m = 1 := by
      rw [jacobiSym.mod_left' hmod2, jacobiSym.one_left]
    have hsplit := jacobiSym.mul_left (-2 : ℤ) ((q : ℤ)) m
    have hneg2 : jacobiSym (-2 : ℤ) m = 1 := by
      rw [jacobiSym.at_neg_two hmodd]
      exact hchi8
    rw [hsplit, hneg2, one_mul] at h2q1
    exact h2q1
  have hleg : legendreSym q (-((m : ℕ) : ℤ)) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.neg _ hqodd, hchiq, one_mul,
      (jacobiSym.quadratic_reciprocity_one_mod_four hq hmodd).symm, hJq]
  have hne' : (Int.cast (-((m : ℕ) : ℤ)) : ZMod q) ≠ 0 := by
    intro h
    apply hqm0
    have h3 := h
    simp only [Int.cast_neg, Int.cast_natCast, neg_eq_zero] at h3
    exact h3
  have hsq : IsSquare (-((m : ℕ) : ZMod q)) := by
    have h := (legendreSym.eq_one_iff q hne').mp hleg
    simpa using h
  exact ⟨hsq, by simpa using hqm0⟩

/-- Jacobi step, case `m ≡ 2 (mod 4)`: then `q ≡ 1 (mod 4)` and `-m` is a
nonzero square in `ZMod q`. Here `m = 2 * m'` with `m'` odd. -/
private theorem isSquare_neg_of_two_mod_four_case {q m : ℕ} [Fact q.Prime]
    (hm : m % 4 = 2) (hdvd : m ∣ q + 1) (hq8 : q % 8 = (m - 1) % 8) :
    q % 4 = 1 ∧ IsSquare (-((m : ℕ) : ZMod q))
      ∧ (-((m : ℕ) : ZMod q)) ≠ 0 := by
  have hqprime : q.Prime := Fact.out
  have hq4 : q % 4 = 1 := by omega
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hmeven : Even m := Nat.even_iff.mpr (by omega)
  obtain ⟨m', hm'⟩ := hmeven
  have hm2 : m = 2 * m' := by omega
  have hm'odd : Odd m' := by
    rw [Nat.odd_iff]
    omega
  have h2q := hqprime.two_le
  -- `q` does not divide `m`.
  have hqm0 : ((m : ℕ) : ZMod q) ≠ 0 := by
    intro hz
    have hdvdZ : (q : ℤ) ∣ ((m : ℕ) : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast hz)
    have hdvdN : q ∣ m := Int.natCast_dvd_natCast.mp hdvdZ
    obtain ⟨s, hs⟩ := hdvd
    rcases hdvdN with ⟨t, ht⟩
    have hqq1 : q ∣ q + 1 := ⟨t * s, by rw [hs, ht]; ring⟩
    have hqq1Z : (q : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast hqq1
    have hq1Z : (q : ℤ) ∣ 1 := by
      obtain ⟨a, ha⟩ := hqq1Z
      exact ⟨a - 1, by linear_combination ha⟩
    have hq1 : q ∣ 1 := Int.natCast_dvd_natCast.mp hq1Z
    have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hq1
    omega
  have hmZ : ((m : ℕ) : ℤ) = 2 * ((m' : ℕ) : ℤ) := by exact_mod_cast hm2
  -- `q ≡ -1 (mod m')` as integers.
  have hmod' : (q : ℤ) % ((m' : ℕ) : ℤ) = (-1 : ℤ) % ((m' : ℕ) : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have hdvd' : m' ∣ q + 1 :=
      dvd_trans ⟨2, by rw [hm2]; ring⟩ hdvd
    have hcast : ((m' : ℕ) : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast hdvd'
    have h0 : ((q : ℤ) + 1) % ((m' : ℕ) : ℤ) = 0 := Int.emod_eq_zero_of_dvd hcast
    have heq : (q : ℤ) - (-1) = (q : ℤ) + 1 := by ring
    rw [heq]
    exact h0
  have e1 : (-((m : ℕ) : ℤ)) = -(2 * ((m' : ℕ) : ℤ)) := by rw [hmZ]
  have hchiq : ZMod.χ₄ (↑q : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four hq4
  have hleg : legendreSym q (-((m : ℕ) : ℤ)) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym, e1, jacobiSym.neg _ hqodd,
      jacobiSym.mul_left, jacobiSym.at_two hqodd,
      (jacobiSym.quadratic_reciprocity_one_mod_four hq4 hm'odd).symm,
      jacobiSym.mod_left' hmod', jacobiSym.at_neg_one hm'odd]
    have h2 : m' % 2 = 1 := Nat.odd_iff.mp hm'odd
    have hm'4 : m' % 4 = 1 ∨ m' % 4 = 3 := by omega
    rcases hm'4 with h1 | h3
    · have e41 : ZMod.χ₄ (↑q : ZMod 4) = 1 := hchiq
      have e81 : ZMod.χ₈ (↑q : ZMod 8) = 1 := by
        have hq81 : q % 8 = 1 := by omega
        rw [ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega : ¬ q % 2 = 0),
          if_pos (by omega : q % 8 = 1 ∨ q % 8 = 7)]
      have e4m : ZMod.χ₄ (↑m' : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four h1
      rw [e41, e81, e4m]
      norm_num
    · have e41 : ZMod.χ₄ (↑q : ZMod 4) = 1 := hchiq
      have e85 : ZMod.χ₈ (↑q : ZMod 8) = -1 := by
        have hq85 : q % 8 = 5 := by omega
        rw [ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega : ¬ q % 2 = 0),
          if_neg (by omega : ¬ (q % 8 = 1 ∨ q % 8 = 7))]
      have e4m : ZMod.χ₄ (↑m' : ZMod 4) = -1 := by
        rw [ZMod.χ₄_nat_eq_if_mod_four, if_neg (by omega : ¬ m' % 2 = 0),
          if_neg (by omega : ¬ m' % 4 = 1)]
      rw [e41, e85, e4m]
      norm_num
  have hne' : (Int.cast (-((m : ℕ) : ℤ)) : ZMod q) ≠ 0 := by
    intro h
    apply hqm0
    have h3 := h
    simp only [Int.cast_neg, Int.cast_natCast, neg_eq_zero] at h3
    exact h3
  have hsq : IsSquare (-((m : ℕ) : ZMod q)) := by
    have h := (legendreSym.eq_one_iff q hne').mp hleg
    simpa using h
  exact ⟨hq4, hsq, by simpa using hqm0⟩

/-- An odd `a` coprime to `n` is coprime to `4 * n`. -/
private theorem ankeny_coprime_aux {a n : ℕ} (hodd : Odd a)
    (hcop : Nat.Coprime a n) : Nat.Coprime a (4 * n) := by
  have h2 : Nat.Coprime a 2 := by
    obtain ⟨t, ht⟩ := hodd
    have hbez : IsCoprime (((a : ℕ)) : ℤ) (((2 : ℕ)) : ℤ) := by
      refine ⟨1, -(t : ℤ), ?_⟩
      have htZ : ((a : ℕ) : ℤ) = 2 * (t : ℤ) + 1 := by exact_mod_cast ht
      omega
    have h := Int.isCoprime_iff_nat_coprime.mp hbez
    simpa using h
  have h4 : Nat.Coprime a 4 := by
    have h := Nat.coprime_mul_iff_right.mpr ⟨h2, h2⟩
    rwa [show (2 : ℕ) * 2 = 4 from rfl] at h
  exact Nat.coprime_mul_iff_right.mpr ⟨h4, hcop⟩

/-- Dirichlet helper: a residue `a` coprime to `4 * m` yields a prime
`q ≡ a (mod 4 * m)` exceeding `4 * m`. -/
private theorem ankeny_dirichlet_prime {m a : ℕ} (hm : 0 < m)
    (hcop : Nat.Coprime a (4 * m)) :
    ∃ q : ℕ, q.Prime ∧ (4 * m) < q ∧ q % (4 * m) = a % (4 * m) := by
  have hne : NeZero (4 * m) := ⟨by omega⟩
  have hunit : IsUnit ((a : ℕ) : ZMod (4 * m)) :=
    (ZMod.isUnit_iff_coprime a (4 * m)).mpr hcop
  obtain ⟨q, hqgt, hqprime, hqeq⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 4 * m) hunit (4 * m)
  exact ⟨q, hqprime, hqgt,
    (ZMod.natCast_eq_natCast_iff' q a (4 * m)).mp hqeq⟩

/-- From `-m` a square mod `q`, get an integer root `b₀` with `q ∣ b₀ ^ 2 + m`. -/
private theorem ankeny_sq_root_mod {q m : ℕ} [NeZero q]
    (hsq : IsSquare (-((m : ℕ) : ZMod q))) :
    ∃ b₀ : ℤ, (q : ℤ) ∣ b₀ ^ 2 + (m : ℤ) := by
  obtain ⟨s, hs⟩ := hsq
  refine ⟨((s.val : ℕ) : ℤ), ?_⟩
  have hsq0 : (((s.val : ℕ)) : ZMod q) = s := ZMod.natCast_zmod_val s
  have hcast : (s ^ 2 + ((m : ℕ) : ZMod q)) = 0 := by
    rw [pow_two, ← hs, neg_add_cancel]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_add, Int.cast_pow, Int.cast_natCast, hsq0]
  exact hcast

/-- The sum-of-squares ball in `Fin 3 → ℝ`: volume, convexity, symmetry,
openness. It is the preimage of the Euclidean ball under `WithLp.toLp`. -/
private theorem volume_setOf_sum_sq_lt_fin_three {r : ℝ} (hr : 0 < r) :
    MeasureTheory.volume {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2}
        = ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)
    ∧ Convex ℝ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2}
    ∧ (∀ x ∈ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2},
      -x ∈ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2})
    ∧ IsOpen {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2} := by
  have hmem : ∀ x : Fin 3 → ℝ,
      (∑ i, (x i) ^ 2 < r ^ 2)
        ↔ WithLp.toLp 2 x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r := by
    intro x
    rw [Metric.mem_ball, _root_.dist_zero_right, EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three]
    rw [Real.sqrt_lt' hr]
  have hset : {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2}
      = WithLp.toLp 2 ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r := by
    ext x
    simp only [Set.mem_preimage]
    exact hmem x
  have hvol : MeasureTheory.volume {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2}
      = ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
    rw [hset, (PiLp.volume_preserving_toLp (ι := Fin 3)).measure_preimage
      measurableSet_ball.nullMeasurableSet]
    exact EuclideanSpace.volume_ball_fin_three _ _
  have hconv : Convex ℝ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2} := by
    rw [hset]
    exact Convex.linear_preimage (convex_ball _ _)
      (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap
  have hsymm : ∀ x ∈ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2},
      -x ∈ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2} := by
    intro x hx
    change ∑ i, ((-x) i) ^ 2 < r ^ 2
    simp only [Pi.neg_apply, neg_sq]
    exact hx
  have hopen : IsOpen {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2} := by
    rw [hset]
    exact Continuous.isOpen_preimage (PiLp.continuous_toLp 2 _) _ Metric.isOpen_ball
  exact ⟨hvol, hconv, hsymm, hopen⟩

/-- Minkowski for an ellipsoid in `ℝ³`: a real `3 × 3` matrix with nonzero
determinant sends some nonzero integer vector into the ball of radius `r`,
provided `8 * |det M| < (π * 4 / 3) * r ^ 3`. -/
private theorem exists_int_ne_zero_sum_sq_mulVec_lt
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hdet : M.det ≠ 0)
    (r : ℝ) (hr : 0 < r)
    (hvol : 8 * |M.det| < (Real.pi * 4 / 3) * r ^ 3) :
    ∃ u : Fin 3 → ℤ, u ≠ 0 ∧
      ∑ i, ((M.mulVec (fun i => ((u i : ℤ) : ℝ))) i) ^ 2 < r ^ 2 := by
  obtain ⟨hBvol, hBconv, hBsymm, -⟩ := volume_setOf_sum_sq_lt_fin_three hr
  set f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := Matrix.toLin' M with hf
  set S : Set (Fin 3 → ℝ) := f ⁻¹' {x | ∑ i, (x i) ^ 2 < r ^ 2} with hS
  have hSconv : Convex ℝ S := hBconv.linear_preimage f
  have hSsymm : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    have hx' : f x ∈ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2} := hx
    have hneg : f (-x) ∈ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2} := by
      rw [map_neg]
      exact hBsymm _ hx'
    exact hneg
  have hdetf : LinearMap.det f ≠ 0 := by
    rw [hf, LinearMap.det_toLin']
    exact hdet
  have hSvol : MeasureTheory.volume S = ENNReal.ofReal (|M.det|⁻¹) *
      (ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)) := by
    rw [hS,
      MeasureTheory.Measure.addHaar_preimage_linearMap MeasureTheory.volume hdetf,
      hBvol]
    congr 1
    rw [hf, LinearMap.det_toLin', abs_inv]
  have hFvol : MeasureTheory.volume
      (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, Real.volume_pi_Ico]
    simp
  have hfin : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by simp
  have hDpos : 0 < |M.det| := abs_pos.mpr hdet
  have hlat : MeasureTheory.volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))) *
      2 ^ Module.finrank ℝ (Fin 3 → ℝ) < MeasureTheory.volume S := by
    rw [hFvol, hfin, one_mul]
    have h2 : (2 : ENNReal) ^ 3 = ENNReal.ofReal 8 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num,
        ENNReal.ofReal_pow (show (0 : ℝ) ≤ 2 by norm_num), ENNReal.ofReal_ofNat]
    rw [h2, hSvol, ← ENNReal.ofReal_pow hr.le,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ r ^ 3),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ |M.det|⁻¹),
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have hmul := mul_lt_mul_of_pos_right hvol (inv_pos.mpr hDpos)
    have hinv : (8 : ℝ) = 8 * |M.det| * |M.det|⁻¹ := by field_simp
    rw [hinv]
    linear_combination hmul
  have : Countable
      ↥((Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))).toAddSubgroup) :=
    inferInstanceAs
      (Countable ↥(Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))))
  obtain ⟨x, hx0, hxS⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin 3)) MeasureTheory.volume)
      hSsymm hSconv hlat
  have hymem : (↑x : Fin 3 → ℝ) ∈
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3))) :=
    x.2
  rw [Module.Basis.mem_span_iff_repr_mem] at hymem
  choose u hu using hymem
  have hAlg : ∀ n : ℤ, (algebraMap ℤ ℝ) n = (((n : ℤ)) : ℝ) := fun n => by simp
  have hu' : ∀ i, (((u i : ℤ)) : ℝ) = (↑x : Fin 3 → ℝ) i := by
    intro i
    have h1 := hu i
    rw [Pi.basisFun_repr, hAlg] at h1
    exact h1
  refine ⟨u, ?_, ?_⟩
  · intro hu0
    apply hx0
    have hy0 : (↑x : Fin 3 → ℝ) = 0 := by
      funext i
      have h1 : u i = 0 := by simp [hu0]
      simp only [← hu' i, h1, Int.cast_zero, Pi.zero_apply]
    exact Subtype.ext (by simpa using hy0)
  · have hM : M.mulVec (fun i => ((u i : ℤ) : ℝ)) = f (↑x : Fin 3 → ℝ) := by
      rw [hf, Matrix.toLin'_apply]
      congr 1
      funext i
      exact hu' i
    rw [hM]
    simpa [hS] using hxS

/-- Small lattice point step of Ankeny's proof: for `m > 0`, `k > 0` and `b : ℤ`
there are integers `R, X, T`, not all zero, with `m ∣ R - X`, `k ∣ X - b * T`
and `k * R ^ 2 + X ^ 2 + m * T ^ 2 < 2 * m * k`. -/
private theorem ankeny_exists_small_lattice_point {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (b : ℤ) :
    ∃ R X T : ℤ, ¬ (R = 0 ∧ X = 0 ∧ T = 0) ∧ (m : ℤ) ∣ R - X ∧ (k : ℤ) ∣ X - b * T ∧
      (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 < 2 * (m : ℤ) * (k : ℤ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set M : Matrix (Fin 3) (Fin 3) ℝ :=
    !![Real.sqrt (k : ℝ) * (m : ℝ), Real.sqrt (k : ℝ) * (k : ℝ),
        Real.sqrt (k : ℝ) * ((b : ℤ) : ℝ);
       0, (k : ℝ), ((b : ℤ) : ℝ);
       0, 0, Real.sqrt (m : ℝ)] with hM
  set r : ℝ := Real.sqrt (2 * (m : ℝ) * (k : ℝ)) with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def]
    exact Real.sqrt_pos.mpr (by positivity)
  have hdetM : M.det
      = Real.sqrt (k : ℝ) * (m : ℝ) * ((k : ℝ) * Real.sqrt (m : ℝ)) := by
    rw [Matrix.det_fin_three, hM]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hsk : (0 : ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkR
  have hsm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hdetpos : 0 < M.det := by
    rw [hdetM]
    positivity
  have hdet : M.det ≠ 0 := ne_of_gt hdetpos
  have hsq : Real.sqrt (k : ℝ) * Real.sqrt (m : ℝ)
      = Real.sqrt ((m : ℝ) * (k : ℝ)) := by
    rw [mul_comm ((m : ℝ)) ((k : ℝ))]
    exact (Real.sqrt_mul hkR.le _).symm
  have hsq2 : Real.sqrt (2 * (m : ℝ) * (k : ℝ))
      = Real.sqrt 2 * Real.sqrt ((m : ℝ) * (k : ℝ)) := by
    rw [show 2 * (m : ℝ) * (k : ℝ) = 2 * ((m : ℝ) * (k : ℝ)) by ring,
      Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num)]
  have ht1 : (1 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num)]
    norm_num
  have h8 : (8 : ℝ) < Real.pi * 4 / 3 * 2 * Real.sqrt 2 := by
    have hpi := Real.pi_gt_three
    have h3 : (3 : ℝ) < Real.pi * Real.sqrt 2 := by
      nlinarith [hpi, ht1, Real.pi_pos,
        Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
    linarith
  have hr2 : r ^ 2 = 2 * (m : ℝ) * (k : ℝ) := by
    rw [hr_def]
    exact Real.sq_sqrt (by positivity)
  have hvol : 8 * |M.det| < (Real.pi * 4 / 3) * r ^ 3 := by
    have e1 : |M.det|
        = (m : ℝ) * (k : ℝ) * Real.sqrt ((m : ℝ) * (k : ℝ)) := by
      have e1' : Real.sqrt (k : ℝ) * (m : ℝ) * ((k : ℝ) * Real.sqrt (m : ℝ))
          = (m : ℝ) * (k : ℝ) * (Real.sqrt (k : ℝ) * Real.sqrt (m : ℝ)) := by ring
      rw [abs_of_pos hdetpos, hdetM, e1', hsq]
    have e2 : r ^ 3
        = 2 * ((m : ℝ) * (k : ℝ))
          * (Real.sqrt 2 * Real.sqrt ((m : ℝ) * (k : ℝ))) := by
      have er3 : r ^ 3 = r ^ 2 * r := by ring
      rw [er3, hr2, hr_def, hsq2]
      ring
    have hP : (0 : ℝ) < (m : ℝ) * (k : ℝ) * Real.sqrt ((m : ℝ) * (k : ℝ)) := by
      positivity
    have hmain := mul_lt_mul_of_pos_left h8 hP
    rw [e1, e2]
    linear_combination hmain
  obtain ⟨u, hu0, hult⟩ := exists_int_ne_zero_sum_sq_mulVec_lt M hdet r hr_pos hvol
  set T : ℤ := u 2 with hT
  set X : ℤ := (k : ℤ) * u 1 + b * u 2 with hX
  set R : ℤ := (m : ℤ) * u 0 + X with hR
  have e0 : (M.mulVec (fun i => ((u i : ℤ) : ℝ))) 0
      = Real.sqrt (k : ℝ) * ((R : ℤ) : ℝ) := by
    rw [hR, hX]
    push_cast
    rw [hM]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, Matrix.cons_val]
    ring
  have e1 : (M.mulVec (fun i => ((u i : ℤ) : ℝ))) 1 = ((X : ℤ) : ℝ) := by
    rw [hX]
    push_cast
    rw [hM]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, Matrix.cons_val]
    ring
  have e2 : (M.mulVec (fun i => ((u i : ℤ) : ℝ))) 2
      = Real.sqrt (m : ℝ) * ((T : ℤ) : ℝ) := by
    rw [hT, hM]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hksq : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hkR.le
  have hmsq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hmR.le
  rw [Fin.sum_univ_three, e0, e1, e2, mul_pow, mul_pow, hksq, hmsq, hr2] at hult
  have hint : (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2
      < 2 * (m : ℤ) * (k : ℤ) := by
    exact_mod_cast hult
  have hdivR : (m : ℤ) ∣ R - X := ⟨u 0, by rw [hR]; ring⟩
  have hdivX : (k : ℤ) ∣ X - b * T := ⟨u 1, by rw [hX, hT]; ring⟩
  have hne : ¬ (R = 0 ∧ X = 0 ∧ T = 0) := by
    rintro ⟨hR0, hX0, hT0⟩
    apply hu0
    have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    have hu2 : u 2 = 0 := by
      rw [hT] at hT0
      exact hT0
    have hu1 : u 1 = 0 := by
      have hX' : (k : ℤ) * u 1 + b * u 2 = 0 := by
        rw [← hX]
        exact hX0
      rw [hu2, mul_zero, add_zero] at hX'
      exact eq_zero_of_ne_zero_of_mul_left_eq_zero hk0 hX'
    have hu0' : u 0 = 0 := by
      have hR' : (m : ℤ) * u 0 + X = 0 := by
        rw [← hR]
        exact hR0
      rw [hX0, add_zero] at hR'
      exact eq_zero_of_ne_zero_of_mul_left_eq_zero hm0 hR'
    funext i
    fin_cases i
    · simpa using hu0'
    · simpa using hu1
    · simpa using hu2
  exact ⟨R, X, T, hne, hdivR, hdivX, hint⟩

/-- Three-square assembly: from the auxiliary modulus (`m ∣ k + 1`,
`k ∣ b ^ 2 + m`, no prime factor of `k` is `3 mod 4`), the small lattice value
`m * k` yields `m` as a sum of three natural squares. -/
private theorem ankeny_exists_three_sq_of_aux {m k : ℕ} (hm : Squarefree m)
    (hk : 0 < k) (hmk : m ∣ k + 1) {b : ℤ} (hb : (k : ℤ) ∣ b ^ 2 + (m : ℤ))
    (hk4 : ∀ p : ℕ, p.Prime → p ∣ k → p % 4 ≠ 3) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = m := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  obtain ⟨R, X, T, hne, hRX, hXT, hlt⟩ :=
    ankeny_exists_small_lattice_point hmpos hk b
  have hval := ankeny_lattice_value_eq hmpos hk hmk hb hne hRX hXT hlt
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hmpos
  have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hRle : R ^ 2 ≤ (m : ℤ) := by
    have h1 : (k : ℤ) * R ^ 2 ≤ (k : ℤ) * (m : ℤ) := by
      have hnn : (0 : ℤ) ≤ X ^ 2 + (m : ℤ) * T ^ 2 := by positivity
      linarith
    exact le_of_mul_le_mul_left h1 hkZ
  have hsq : ((((R.natAbs ^ 2 : ℕ))) : ℤ) = R ^ 2 := by
    exact_mod_cast Int.natAbs_sq R
  have hRnat : R.natAbs ^ 2 ≤ m := by
    have h2 : (((R.natAbs ^ 2 : ℕ)) : ℤ) ≤ ((m : ℕ) : ℤ) := by
      rw [hsq]
      exact hRle
    exact_mod_cast h2
  set N : ℕ := m - R.natAbs ^ 2 with hN
  have hNadd : R.natAbs ^ 2 + N = m := Nat.add_sub_cancel' hRnat
  have hRm : (m : ℤ) = R ^ 2 + (N : ℤ) := by
    have h2 : (N : ℤ) = (m : ℤ) - R ^ 2 := by
      rw [hN, Nat.cast_sub hRnat, hsq]
    linarith
  have hrep : (k : ℤ) * (N : ℤ) = X ^ 2 + (m : ℤ) * T ^ 2 := by
    linear_combination -hval - (k : ℤ) * hRm
  obtain ⟨a, c, hac⟩ := ankeny_exists_two_sq_of_rep hm hk hmk hk4 hRm hrep
  exact ⟨R.natAbs, a, c, by omega⟩

/-- Auxiliary modulus (Dirichlet plus reciprocity): for `m` with
`m % 8 ∈ {1, 2, 3, 5, 6}` there are `k > 0` and `b` with `m ∣ k + 1`,
`k ∣ b ^ 2 + m`, and no prime factor of `k` is `3 mod 4`. -/
private theorem ankeny_exists_aux_modulus {m : ℕ} (hm : 0 < m)
    (hmod : m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 6) :
    ∃ k : ℕ, 0 < k ∧ ∃ b : ℤ, m ∣ k + 1 ∧ (k : ℤ) ∣ b ^ 2 + (m : ℤ)
      ∧ ∀ p : ℕ, p.Prime → p ∣ k → p % 4 ≠ 3 := by
  have hcase : m % 4 = 1 ∨ m % 4 = 2 ∨ m % 8 = 3 := by omega
  rcases hcase with h4 | h4 | h8
  · -- Case `m % 4 = 1`: `a = 2 * m - 1`, `k = q`.
    have hm1 : 1 ≤ m := by omega
    have hodd : Odd (2 * m - 1) := Nat.odd_iff.mpr (by omega)
    have hcopm : Nat.Coprime (2 * m - 1) m := by
      have haZ : (((2 * m - 1 : ℕ)) : ℤ) = 2 * (m : ℤ) - 1 := by omega
      have hbez : IsCoprime (((2 * m - 1 : ℕ)) : ℤ) (((m : ℕ)) : ℤ) := ⟨-1, 2, by omega⟩
      have h := Int.isCoprime_iff_nat_coprime.mp hbez
      simpa using h
    have hcop := ankeny_coprime_aux hodd hcopm
    obtain ⟨q, hqprime, hqgt, hqm_eq⟩ := ankeny_dirichlet_prime hm hcop
    have ha4 : (2 * m - 1) % 4 = 1 := by omega
    have ha_lt : 2 * m - 1 < 4 * m := by omega
    rw [Nat.mod_eq_of_lt ha_lt] at hqm_eq
    have hq4 : q % 4 = 1 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      have hq : q = (2 * m - 1) + 4 * (m * (q / (4 * m))) := by
        linear_combination -hdiv
      rw [hq, Nat.add_mul_mod_self_left, ha4]
    have hdivm : m ∣ q + 1 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      refine ⟨4 * (q / (4 * m)) + 2, ?_⟩
      calc q + 1 = (4 * m * (q / (4 * m)) + (2 * m - 1)) + 1 := by omega
        _ = 4 * m * (q / (4 * m)) + 2 * m := by
          rw [add_assoc, Nat.sub_add_cancel (by omega : 1 ≤ 2 * m)]
        _ = m * (4 * (q / (4 * m)) + 2) := by ring
    have : Fact q.Prime := ⟨hqprime⟩
    have : NeZero q := ⟨hqprime.ne_zero⟩
    obtain ⟨hsq, hne⟩ := isSquare_neg_of_one_mod_four_case hq4 h4 hdivm
    obtain ⟨b₀, hb0⟩ := ankeny_sq_root_mod hsq
    refine ⟨q, hqprime.pos, b₀, hdivm, hb0, ?_⟩
    intro p hpprime hpk
    have h2 := hpprime.two_le
    rcases (Nat.dvd_prime hqprime).mp hpk with h | h
    · omega
    · rw [h]
      omega
  · -- Case `m % 4 = 2`: `a = m - 1`, `k = q`.
    have hm2 : 2 ≤ m := by omega
    have hodd : Odd (m - 1) := Nat.odd_iff.mpr (by omega)
    have hcopm : Nat.Coprime (m - 1) m := by
      have haZ : (((m - 1 : ℕ)) : ℤ) = (m : ℤ) - 1 := by omega
      have hbez : IsCoprime (((m - 1 : ℕ)) : ℤ) (((m : ℕ)) : ℤ) := ⟨-1, 1, by omega⟩
      have h := Int.isCoprime_iff_nat_coprime.mp hbez
      simpa using h
    have hcop := ankeny_coprime_aux hodd hcopm
    obtain ⟨q, hqprime, hqgt, hqm_eq⟩ := ankeny_dirichlet_prime hm hcop
    have ha4 : (m - 1) % 4 = 1 := by omega
    have ha_lt : m - 1 < 4 * m := by omega
    rw [Nat.mod_eq_of_lt ha_lt] at hqm_eq
    have hq4 : q % 4 = 1 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      have hq : q = (m - 1) + 4 * (m * (q / (4 * m))) := by
        linear_combination -hdiv
      rw [hq, Nat.add_mul_mod_self_left, ha4]
    have hdivm : m ∣ q + 1 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      refine ⟨4 * (q / (4 * m)) + 1, ?_⟩
      calc q + 1 = (4 * m * (q / (4 * m)) + (m - 1)) + 1 := by omega
        _ = 4 * m * (q / (4 * m)) + m := by
          rw [add_assoc, Nat.sub_add_cancel (by omega : 1 ≤ m)]
        _ = m * (4 * (q / (4 * m)) + 1) := by ring
    have hq8 : q % 8 = (m - 1) % 8 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      have e8 : 8 * ((m / 2) * (q / (4 * m))) = 4 * (m * (q / (4 * m))) := by
        have hm2eq : m = 2 * (m / 2) := by omega
        calc 8 * ((m / 2) * (q / (4 * m)))
            = 4 * ((2 * (m / 2)) * (q / (4 * m))) := by ring
          _ = 4 * (m * (q / (4 * m))) := by rw [← hm2eq]
      have hq : q = (m - 1) + 8 * ((m / 2) * (q / (4 * m))) := by
        linear_combination -hdiv - e8
      rw [hq, Nat.add_mul_mod_self_left]
    have : Fact q.Prime := ⟨hqprime⟩
    have : NeZero q := ⟨hqprime.ne_zero⟩
    obtain ⟨hq4', hsq, hne⟩ := isSquare_neg_of_two_mod_four_case h4 hdivm hq8
    obtain ⟨b₀, hb0⟩ := ankeny_sq_root_mod hsq
    refine ⟨q, hqprime.pos, b₀, hdivm, hb0, ?_⟩
    intro p hpprime hpk
    have h2 := hpprime.two_le
    rcases (Nat.dvd_prime hqprime).mp hpk with h | h
    · omega
    · rw [h]
      omega
  · -- Case `m % 8 = 3`: `a = (m - 1) / 2`, `k = 2 * q`.
    have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
    have hodd : Odd ((m - 1) / 2) := Nat.odd_iff.mpr (by omega)
    have hcopm : Nat.Coprime ((m - 1) / 2) m := by
      have haZ : 2 * ((((m - 1) / 2 : ℕ)) : ℤ) = (m : ℤ) - 1 := by omega
      have hbez : IsCoprime ((((m - 1) / 2 : ℕ)) : ℤ) (((m : ℕ)) : ℤ) := ⟨-2, 1, by omega⟩
      have h := Int.isCoprime_iff_nat_coprime.mp hbez
      simpa only [Int.natAbs_natCast] using h
    have hcop := ankeny_coprime_aux hodd hcopm
    obtain ⟨q, hqprime, hqgt, hqm_eq⟩ := ankeny_dirichlet_prime hm hcop
    have ha4 : ((m - 1) / 2) % 4 = 1 := by omega
    have ha_lt : (m - 1) / 2 < 4 * m := by omega
    rw [Nat.mod_eq_of_lt ha_lt] at hqm_eq
    have hq4 : q % 4 = 1 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      have hq : q = ((m - 1) / 2) + 4 * (m * (q / (4 * m))) := by
        linear_combination -hdiv
      rw [hq, Nat.add_mul_mod_self_left, ha4]
    have hdivm : m ∣ 2 * q + 1 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      have e : 2 * ((m - 1) / 2) + 1 = m := by omega
      refine ⟨8 * (q / (4 * m)) + 1, ?_⟩
      calc 2 * q + 1 = 2 * (4 * m * (q / (4 * m)) + (m - 1) / 2) + 1 := by
            omega
        _ = 8 * m * (q / (4 * m)) + (2 * ((m - 1) / 2) + 1) := by ring
        _ = 8 * m * (q / (4 * m)) + m := by rw [e]
        _ = m * (8 * (q / (4 * m)) + 1) := by ring
    have : Fact q.Prime := ⟨hqprime⟩
    have : NeZero q := ⟨hqprime.ne_zero⟩
    obtain ⟨hsq, hne⟩ := isSquare_neg_of_three_mod_eight_case hq4 h8 hdivm
    obtain ⟨b₀, hb0⟩ := ankeny_sq_root_mod hsq
    have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
    obtain ⟨tq, htq⟩ := hqodd
    have hqoddZ : Odd (((q : ℕ)) : ℤ) := ⟨(tq : ℤ), by exact_mod_cast htq⟩
    obtain ⟨tm, htm⟩ := hmodd
    have hmoddZ : Odd (((m : ℕ)) : ℤ) := ⟨(tm : ℤ), by exact_mod_cast htm⟩
    have hqpos : 0 < q := hqprime.pos
    have hcop2q : IsCoprime (((2 : ℕ)) : ℤ) (((q : ℕ)) : ℤ) := ⟨-tq, 1, by omega⟩
    have hdivs : ∀ p : ℕ, p.Prime → p ∣ 2 * q → p % 4 ≠ 3 := by
      intro p hpprime hpk
      have h2 := hpprime.two_le
      rcases (Nat.Prime.dvd_mul hpprime).mp hpk with h | h
      · rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2'
        · omega
        · rw [h2']
          decide
      · rcases (Nat.dvd_prime hqprime).mp h with h1 | h2'
        · omega
        · rw [h2']
          omega
    by_cases hbodd : Odd b₀
    · have h2dvd : (2 : ℤ) ∣ b₀ ^ 2 + (m : ℤ) := by
        have hsq_odd : Odd (b₀ ^ 2) := by
          rw [pow_two]
          exact hbodd.mul hbodd
        have heven2 : Even (b₀ ^ 2 + (m : ℤ)) := hsq_odd.add_odd hmoddZ
        obtain ⟨r, hr⟩ := heven2
        exact ⟨r, by omega⟩
      have h2q : (((2 * q : ℕ)) : ℤ) ∣ b₀ ^ 2 + (m : ℤ) := by
        have h := hcop2q.mul_dvd h2dvd hb0
        have e : (((2 * q : ℕ)) : ℤ) = ((2 : ℕ) : ℤ) * (((q : ℕ)) : ℤ) := by simp
        rw [e]
        exact h
      exact ⟨2 * q, mul_pos (by norm_num) hqprime.pos, b₀, hdivm, h2q, hdivs⟩
    · have heven : Even b₀ := Int.not_odd_iff_even.mp hbodd
      have hbodd' : Odd (b₀ + ((q : ℕ) : ℤ)) := heven.add_odd hqoddZ
      have hqb : (q : ℤ) ∣ (b₀ + ((q : ℕ) : ℤ)) ^ 2 + (m : ℤ) := by
        have e : (b₀ + ((q : ℕ) : ℤ)) ^ 2 + (m : ℤ)
            = (b₀ ^ 2 + (m : ℤ)) + (q : ℤ) * (2 * b₀ + (q : ℤ)) := by ring
        rw [e]
        exact dvd_add hb0 (dvd_mul_right _ _)
      have h2dvd : (2 : ℤ) ∣ (b₀ + ((q : ℕ) : ℤ)) ^ 2 + (m : ℤ) := by
        have hsq_odd : Odd ((b₀ + ((q : ℕ) : ℤ)) ^ 2) := by
          rw [pow_two]
          exact hbodd'.mul hbodd'
        have heven2 : Even ((b₀ + ((q : ℕ) : ℤ)) ^ 2 + (m : ℤ)) :=
          hsq_odd.add_odd hmoddZ
        obtain ⟨r, hr⟩ := heven2
        exact ⟨r, by omega⟩
      have h2q : (((2 * q : ℕ)) : ℤ) ∣ (b₀ + ((q : ℕ) : ℤ)) ^ 2 + (m : ℤ) := by
        have h := hcop2q.mul_dvd h2dvd hqb
        have e : (((2 * q : ℕ)) : ℤ) = ((2 : ℕ) : ℤ) * (((q : ℕ)) : ℤ) := by simp
        rw [e]
        exact h
      exact ⟨2 * q, mul_pos (by norm_num) hqprime.pos, b₀ + ((q : ℕ) : ℤ), hdivm, h2q, hdivs⟩

/-- Squarefree case: every squarefree `m` with `m % 8 ≠ 7` is a sum of three
natural squares. -/
private theorem exists_three_sq_of_squarefree_of_mod_eight_ne_seven {m : ℕ}
    (hm : Squarefree m) (h7 : m % 8 ≠ 7) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = m := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  have h4 : ¬ 4 ∣ m := by
    intro hdvd
    have h22 : 2 * 2 ∣ m := by
      have h44 : (4 : ℕ) = 2 * 2 := rfl
      rwa [h44] at hdvd
    exact (Nat.squarefree_iff_prime_squarefree.mp hm) 2 Nat.prime_two h22
  have hmod : m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 6 := by
    have h8 : m % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have h0 : m % 8 ≠ 0 := by
      intro h0
      apply h4
      have hdvd8 : 8 ∣ m := Nat.dvd_of_mod_eq_zero h0
      omega
    have h44 : m % 8 ≠ 4 := by
      intro h44
      apply h4
      have hdiv := Nat.div_add_mod m 8
      omega
    omega
  obtain ⟨k, hk, b, hmk, hb, hk4⟩ := ankeny_exists_aux_modulus hmpos hmod
  exact ankeny_exists_three_sq_of_aux hm hk hmk hb hk4

/-- An odd natural is `1`, `3`, `5`, or `7` mod `8`. -/
private theorem odd_mod_eight {c : ℕ} (h : Odd c) :
    c % 8 = 1 ∨ c % 8 = 3 ∨ c % 8 = 5 ∨ c % 8 = 7 := by
  obtain ⟨t, ht⟩ := h
  omega

/-- Legendre's three-square theorem: a natural number `n` is a sum of three
    squares provided it is not of the form `4 ^ a * (8 * b + 7)`.
    Source: Soufiane Mezroui, Abdelmalek Azizi, and M'hammed Ziane,
    "On a Conjecture of Farhi", Journal of Integer Sequences 17 (2014),
    source TeX lines 122-127,
    https://cs.uwaterloo.ca/journals/JIS/VOL17/Mezroui/soufiane4.tex
    (full source SHA-256
    `e3121b115a35156b3aae46f175bfb165ab45588165b59569ce5d9061c52c104f`,
    normalized theorem-span SHA-256
    `fd5d4315a995eda1995848786e22b3563ea1dd2080f3a1598e907d36082a6180`).

    Proves `Wanted` entry `exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven`. -/
theorem exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven
    (n : Nat)
    (h : ¬ ∃ a b : Nat, n = 4 ^ a * (8 * b + 7)) :
    ∃ x y z : Nat, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, 0, 0, by simp⟩
  obtain ⟨e, n', hn4, hn_eq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 4 (by norm_num)
  have hn'pos : 0 < n' := Nat.pos_of_ne_zero fun h0 => hn.ne' (by rw [hn_eq, h0, mul_zero])
  obtain ⟨m, c, hmpos, hc, hcm, hmsq⟩ := Nat.sq_mul_squarefree_of_pos hn'pos
  have hcodd : Odd c := by
    by_contra hcon
    rw [Nat.not_odd_iff_even] at hcon
    obtain ⟨t, ht⟩ := hcon
    apply hn4
    have h4c : 4 ∣ c ^ 2 := ⟨t * t, by rw [ht]; ring⟩
    have hc2n : c ^ 2 ∣ n' := ⟨m, hcm.symm⟩
    exact dvd_trans h4c hc2n
  have hc2 : c ^ 2 % 8 = 1 := by
    have hodd8 := odd_mod_eight hcodd
    rw [Nat.pow_mod]
    rcases hodd8 with h | h | h | h <;> rw [h]
  have hnm : n' % 8 = m % 8 := by
    have e : (c ^ 2 * m) % 8 = m % 8 := by
      rw [Nat.mul_mod, hc2, Nat.one_mul]
      omega
    rwa [hcm] at e
  have hm7 : m % 8 ≠ 7 := by
    intro hm7
    apply h
    have hnm7 : n' % 8 = 7 := hnm.trans hm7
    have hn'' : n' = 8 * (n' / 8) + 7 := by omega
    refine ⟨e, n' / 8, ?_⟩
    rw [hn_eq, ← hn'']
  obtain ⟨x, y, z, hxyz⟩ :=
    exists_three_sq_of_squarefree_of_mod_eight_ne_seven hmsq hm7
  have h4e : (4 : ℕ) ^ e = (2 ^ e) ^ 2 := by
    have g1 : (4 : ℕ) ^ e = 2 ^ (2 * e) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    have g2 : (2 ^ e) ^ 2 = 2 ^ (e * 2) := by
      rw [← pow_mul]
    rw [g1, g2, mul_comm e 2]
  have hfin : (2 ^ e * c * x) ^ 2 + (2 ^ e * c * y) ^ 2 + (2 ^ e * c * z) ^ 2
      = 4 ^ e * n' := by
    rw [← hcm, ← hxyz, h4e]
    ring
  refine ⟨2 ^ e * c * x, 2 ^ e * c * y, 2 ^ e * c * z, ?_⟩
  rw [hn_eq]
  exact hfin

end Nat

/-
Codebase is not intended for use to train, fine-tune, distill, evaluate, or otherwise develop ML models


                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

namespace Bridge
open Finset Quaternion Grimm338

theorem result : OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1.H2 := by
  classical
  intro s sp sf sm
  have rep := Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven s (by
    rintro ⟨n,b,rfl⟩
    cases n with
    | zero => simp at sm
    | succ n =>
      rw [pow_succ, show 4^n*4*(8*b+7)=4*(4^n*(8*b+7)) by ring] at sm
      omega)
  obtain ⟨a,b,c,r⟩ := rep
  let v := TernaryOrientation.mkQ 0 a b c
  have v0 : v.re=0 := rfl
  have vn : normSq v=s := by
    rw [TernaryOrientation.norm_mkQ]
    norm_num
    exact_mod_cast r
  have prim : primitive v := prim_of_sqfree sf r
  let U := (range (s+1)) ×ˢ ((range (s+1)) ×ˢ (range (s+1)))
  let F := U.filter (fun f => 0 < f.1 ∧ f.2.1 ≤ f.1 ∧ f.1 ≤ f.2.2 ∧ 4*f.1*f.2.2=s+f.2.1^2)
  let S := U.filter (fun u => u.1^2+u.2.1^2+u.2.2^2=s)
  change F.card ≤ S.card
  have image (f) (hf : f∈F) : ∃ t ∈ S, Nonempty (Witness v f t) := by
    obtain ⟨t,ht,w⟩ := make_witness v0 vn sm f (mem_filter.mp hf).2
    refine ⟨t,mem_filter.mpr ⟨?_,ht⟩,w⟩
    simp only [U,mem_product,mem_range]
    have h (u v w : ℕ) (e : u^2+v^2+w^2=s) : u<s+1 := by
      have hu := Nat.le_self_pow (by decide : 2≠0) u
      omega
    exact ⟨h _ _ _ ht,h _ t.1 t.2.2 (by linarith only [ht]),h _ t.1 t.2.1 (by linarith only [ht])⟩
  choose j hj using fun (x : F) => image x.1 x.2
  let g : F → S := fun x => ⟨j x,(hj x).1⟩
  have inj : Function.Injective g := by
    intro x y h
    have e : j x=j y := congrArg Subtype.val h
    obtain ⟨wx⟩ := (hj x).2
    obtain ⟨wy⟩ := (hj y).2
    rw [←e] at wy
    exact Subtype.ext (witness_inj sm prim v0 vn (mem_filter.mp x.2).2 (mem_filter.mp y.2).2 wx wy)
  simpa using Fintype.card_le_of_injective g inj

end Bridge

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1.H2 := Bridge.result
