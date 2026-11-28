import FormalConjectures.ErdosProblems.«338»

/-! The quaternion shell formula is taken from Yordan’s checked Tunnell even-twist proof (3112a07). The binary shell formula follows TheWaler’s checked Gauss circle floor formula. The divisor bound follows zarnab’s checked Erdős 821 divisor estimate (323fe03). -/
section

/- Integral quaternion norm shells, rotations, and the weight on a coordinate. -/

namespace TunnellQuaternion

open Finset Quaternion


abbrev QInt := Quaternion ℤ

lemma normSq_mk (a b c d : ℤ) : Quaternion.normSq (⟨a,b,c,d⟩:QInt) = a^2+b^2+c^2+d^2 := Quaternion.normSq_def' _

abbrev coordsEquiv := Quaternion.equivProd ℤ

def quatShell (N : ℕ) : Finset QInt :=
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

def invariant {p : ℕ} (W : Mat p) : Option (ZMod p) → Prop
  | none => W 0 1 = 0
  | some r => W 1 0 + W 1 1 * r = r * (W 0 0 + W 0 1 * r)

instance {p : ℕ} [NeZero p] (W : Mat p) (l : Option (ZMod p)) : Decidable (invariant W l) := by
  cases l <;> unfold invariant <;> infer_instance

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

lemma same_line_iff {q w : Quaternion ℤ} (hq : normSq q=p) (hw : normSq w=p)
    {l : Option (ZMod p)} (hl : inLine l (residue M q)) :
    inLine l (residue M w) ↔ ∃ u : Quaternion ℤ, normSq u=1 ∧ w=q*u := by
  constructor
  · intro hh
    obtain ⟨u,hu⟩ := divide_left M hq hl hh
    have h := hw
    rw [hu,map_mul,hq] at h
    refine ⟨u,?_,hu⟩
    apply mul_left_cancel₀ (by exact_mod_cast (Fact.out:p.Prime).ne_zero : (p:ℤ)≠0)
    simpa using h
  · rintro ⟨u,_,rfl⟩; rw [map_mul]; exact line_mul hl _

end TunnellQuaternion

end

section

/- Eight integral quaternions represent each projective line at an odd prime. -/

namespace TunnellQuaternion

open Finset Quaternion

variable {p : ℕ} [Fact p.Prime] (M : Model p)

lemma unique_class {q : QInt} (hq : normSq q=p) : ∃! l, inLine l (residue M q) := by
  apply line_unique _ (norm_prime_nonzero M hq)
  rw [residue_det,hq]
  simp

noncomputable def classOf (q : QInt) : Option (ZMod p) :=
  if h : normSq q = p then (unique_class M h).exists.choose else none

lemma class_eq_iff {q : QInt} (hq : normSq q=p) (l : Option (ZMod p)) :
    classOf M q=l ↔ inLine l (residue M q) := by
  rw [classOf,dif_pos hq]
  have h := (unique_class M hq).exists.choose_spec
  constructor
  · rintro rfl
    exact h
  · exact fun h' => (unique_class M hq).unique h h'

lemma quatShell_one_card : (quatShell 1).card = 8 := by decide

lemma fiber_class_card (hp : p≠2) (l : Option (ZMod p)) :
    ((quatShell p).filter (fun q => classOf M q = l)).card = 8 := by
  classical
  obtain ⟨q,hq,hl⟩ := exists_at_line M hp l
  rw [←quatShell_one_card]
  symm
  apply card_nbij (fun u => q*u)
  · intro u hu
    have hu' := mem_quatShell.mp hu
    have hqu : normSq (q*u)=p := by rw [map_mul,hq,hu']; simp
    refine mem_filter.mpr ⟨mem_quatShell.mpr hqu,(class_eq_iff M hqu l).mpr ?_⟩
    rw [map_mul]
    exact line_mul hl _
  · intro u hu v hv h
    apply scalar_cancel (p:ℤ) (by exact_mod_cast (Fact.out:p.Prime).ne_zero)
    have he := congrArg (star q * ·) h
    simpa only [←mul_assoc,star_mul_self,hq,coe_mul_eq_smul] using he
  · intro w hw
    obtain ⟨hn,he⟩ := mem_filter.mp hw
    have hn' := mem_quatShell.mp hn
    obtain ⟨u,hu,hw⟩ := (same_line_iff M hq hn' hl).mp ((class_eq_iff M hn' l).mp he)
    exact ⟨u,mem_quatShell.mpr hu,hw.symm⟩

lemma card_class_mem (hp : p≠2) (L : Finset (Option (ZMod p))) :
    ((quatShell p).filter (fun q => classOf M q ∈ L)).card = 8*L.card := by
  classical
  have h := Finset.sum_fiberwise_eq_sum_filter (quatShell p) L (classOf M) (fun _ => (1:ℕ))
  simp only [sum_const,nsmul_eq_mul,mul_one] at h
  simpa [fiber_class_card M hp,mul_comm] using h.symm

end TunnellQuaternion

end

section

/- The odd-prime recurrence for the number of representations by four squares. -/

namespace TunnellQuaternion

open Finset Quaternion
open scoped Classical

noncomputable section

lemma quat_left_cancel {q u v : QInt} (hq : normSq q≠0) (h : q*u=q*v) : u=v := by
  apply scalar_cancel (normSq q) hq
  have he := congrArg (star q * ·) h
  simpa only [←mul_assoc, star_mul_self,coe_mul_eq_smul] using he

lemma count_left_factors {α : Type*} [DecidableEq α] (D : Finset α) (q : α→QInt) {d : ℕ}
    (hd : d≠0) (hq : ∀ a ∈ D, normSq (q a)=d) (n : ℕ) :
    D.card*(quatShell n).card = ∑ w ∈ quatShell (d*n),
      (D.filter (fun a => ∃ u : QInt, w=q a*u)).card := by
  classical
  let S := D ×ˢ quatShell n
  let f (a : α × QInt) := q a.1 * a.2
  have h : (S:Set _).MapsTo f (quatShell (d*n)) := by
    rintro ⟨a,u⟩ h
    obtain ⟨ha,hu⟩ := mem_product.mp h
    exact mem_quatShell.mpr (by simp [f,hq a ha,mem_quatShell.mp hu])
  rw [←card_product,card_eq_sum_card_fiberwise h]
  apply sum_congr rfl
  intro w hw
  apply card_nbij Prod.fst
  · rintro ⟨a,u⟩ h
    obtain ⟨hu,hf⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨(mem_product.mp hu).1,u,hf.symm⟩
  · rintro ⟨a,u⟩ hu ⟨b,v⟩ hv he
    change a=b at he
    subst b
    obtain ⟨hau,hw'⟩ := mem_filter.mp hu
    have ha := (mem_product.mp hau).1
    exact Prod.ext rfl (quat_left_cancel (by rw [hq a ha]; exact_mod_cast hd) (hw'.trans (mem_filter.mp hv).2.symm))
  · intro a ha
    obtain ⟨ha',u,rfl⟩ := mem_filter.mp ha
    have hw' := mem_quatShell.mp hw
    rw [map_mul,hq a ha',Nat.cast_mul] at hw'
    have hu := mul_left_cancel₀ (by exact_mod_cast hd : (d:ℤ)≠0) hw'
    exact ⟨(a,u),mem_filter.mpr ⟨mem_product.mpr ⟨ha',mem_quatShell.mpr hu⟩,rfl⟩,rfl⟩

lemma quatShell_prime_card {p : ℕ} [Fact p.Prime] (hp : p≠2) : (quatShell p).card=8*(p+1) := by
  simpa using card_class_mem (localModel hp) hp univ

lemma odd_factors_card {p : ℕ} [Fact p.Prime] (hp : p≠2) (n : ℕ) (w : QInt)
    (hw : w∈quatShell (p*n)) :
    ((quatShell p).filter (fun q => ∃ u : QInt, w=q*u)).card =
      if red p w=0 then 8*(p+1) else 8 := by
  classical
  let M := localModel hp
  have hdet : (residue M w).det=0 := by
    rw [residue_det,mem_quatShell.mp hw]
    simp
  split_ifs with h
  · have hw0 := (residue_zero M w).mpr h
    have hall : ∀ q ∈ quatShell p, ∃ u : QInt, w=q*u := by
      intro q hq
      have hqn := mem_quatShell.mp hq
      apply divide_left M hqn ((class_eq_iff M hqn _).mp rfl)
      rw [hw0]
      cases classOf M q <;> simp [inLine]
    simpa [filter_eq_self.mpr hall] using quatShell_prime_card hp
  · obtain ⟨l,hl,hu⟩ := line_unique _ (fun he => h ((residue_zero M w).mp he)) hdet
    rw [←fiber_class_card M hp l]
    congr 1
    apply filter_congr
    intro q hq
    have hqn := mem_quatShell.mp hq
    constructor
    · rintro ⟨u,rfl⟩
      apply hu
      rw [map_mul]
      exact line_mul ((class_eq_iff M hqn _).mp rfl) _
    · intro hq'
      exact divide_left M hqn ((class_eq_iff M hqn l).mp hq') hl

lemma imprimitive_quat_card {p : ℕ} (hp : p≠0) (n : ℕ) :
    ((quatShell (p*n)).filter (fun w => red p w=0)).card =
      if p∣n then (quatShell (n/p)).card else 0 := by
  classical
  split_ifs with h
  · symm
    apply card_nbij (fun u => (p:ℤ) • u)
    · intro u hu
      apply mem_filter.mpr ⟨mem_quatShell.mpr ?_,by rw [red_smul]; simp⟩
      rw [norm_smul,mem_quatShell.mp hu,pow_two,mul_assoc,←Nat.cast_mul, Nat.mul_div_cancel' h]
      simp
    · intro u _ v _ huv
      exact scalar_cancel p (by exact_mod_cast hp) huv
    · intro w hw
      obtain ⟨hn,hred⟩ := mem_filter.mp hw
      obtain ⟨u,rfl⟩ := (div_iff p w).mp hred
      refine ⟨u, mem_quatShell.mpr ?_,rfl⟩
      have hh := mem_quatShell.mp hn
      rw [norm_smul,Nat.cast_mul,←Nat.mul_div_cancel' h] at hh
      simp only [Nat.cast_mul] at hh
      apply mul_left_cancel₀ (pow_ne_zero 2 (by exact_mod_cast hp : (p:ℤ)≠0))
      simpa [pow_two,mul_assoc] using hh
  · apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hn,hred⟩ := mem_filter.mp hw
    obtain ⟨u,rfl⟩ := (div_iff p w).mp hred
    have hh := mem_quatShell.mp hn
    rw [norm_smul,pow_two,mul_assoc,Nat.cast_mul] at hh
    have e := mul_left_cancel₀ (by exact_mod_cast hp : (p:ℤ)≠0) hh
    exact h (by exact_mod_cast (show (p:ℤ)∣(n:ℤ) from ⟨_, e.symm⟩))

theorem quatShell_odd_recurrence {p : ℕ} [Fact p.Prime] (hp : p≠2) (n : ℕ) :
    (p+1)*(quatShell n).card = (quatShell (p*n)).card +
      (if p∣n then p*(quatShell (n/p)).card else 0) := by
  classical
  have h := count_left_factors (quatShell p) id (Fact.out:p.Prime).ne_zero (fun q hq => mem_quatShell.mp hq) n
  change _ = ∑ w ∈ quatShell (p*n), ((quatShell p).filter (fun q => ∃ u : QInt, w=q*u)).card at h
  rw [sum_congr rfl (odd_factors_card hp n),quatShell_prime_card hp] at h
  have split (w : QInt) : (if red p w=0 then 8*(p+1) else 8) = 8 + (if red p w=0 then 8*p else 0) := by
    split_ifs <;> omega
  simp_rw [split] at h
  rw [sum_add_distrib,←sum_filter,sum_const,sum_const,imprimitive_quat_card (Fact.out:p.Prime).ne_zero] at h
  simp only [nsmul_eq_mul] at h
  split_ifs at h ⊢ <;> nlinarith

end
end TunnellQuaternion

end

section

/- The dyadic recurrence for four squares, by counting the three norm-two left factors. -/

namespace TunnellQuaternion

open Finset Quaternion

def dyadic (i : Fin 3) : QInt := ![⟨1,1,0,0⟩,⟨1,0,1,0⟩,⟨1,0,0,1⟩] i

lemma norm_dyadic (i : Fin 3) : normSq (dyadic i)=2 := by fin_cases i <;> decide

lemma dyadic_dvd_iff (i : Fin 3) (w : QInt) :
    (∃ u : QInt, w=dyadic i*u) ↔ red 2 (star (dyadic i)*w)=0 := by
  rw [div_iff]
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨u,by rw [←mul_assoc,star_mul_self,norm_dyadic,coe_mul_eq_smul]; rfl⟩
  · rintro ⟨u,hu⟩
    refine ⟨u,scalar_cancel 2 (by decide) ?_⟩
    have hh := congrArg (dyadic i * ·) hu
    simpa only [←mul_assoc,self_mul_star,norm_dyadic,coe_mul_eq_smul,Algebra.mul_smul_comm, Nat.cast_ofNat] using hh

def reduceFour (w : Quaternion (ZMod 4)) : Quaternion (ZMod 2) :=
  let f := ZMod.castHom (by decide : 2∣4) (ZMod 2)
  ⟨f w.re,f w.imI,f w.imJ,f w.imK⟩

lemma reduceFour_red (w : QInt) : reduceFour (red 4 w)=red 2 w := by
  change reduceFour (redFun 4 w)=redFun 2 w
  apply QuaternionAlgebra.ext <;> simp [reduceFour,redFun]

instance finiteQuatDecEq {n : ℕ} : DecidableEq (Quaternion (ZMod n)) :=
  (Quaternion.equivProd _).decidableEq

def dyadicCount (w : Quaternion (ZMod 4)) : ℕ :=
  (univ.filter (fun i : Fin 3 => red 2 (star (dyadic i))*reduceFour w=0)).card

lemma dyadic_table (w : Quaternion (ZMod 4)) :
    (normSq w=0 → dyadicCount w=3) ∧ (normSq w=2 → dyadicCount w=1) := by
  obtain ⟨a,b,c,d⟩ := w
  revert a b c d
  decide

open scoped Classical in
theorem quatShell_two_recurrence (n : ℕ) :
    (quatShell (2*n)).card = if Even n then (quatShell n).card else 3*(quatShell n).card := by
  classical
  have h := count_left_factors (univ : Finset (Fin 3)) dyadic (d:=2) (by decide)
    (fun i _ => norm_dyadic i) n
  simp only [card_univ,Fintype.card_fin] at h
  have hf (w : QInt) (hw : w∈quatShell (2*n)) :
      (univ.filter (fun i : Fin 3 => ∃ u : QInt, w=dyadic i*u)).card = if Even n then 3 else 1 := by
    have hq := dyadic_table (red 4 w)
    rw [←red_norm,mem_quatShell.mp hw] at hq
    have heq : (univ.filter (fun i : Fin 3 => ∃ u : QInt, w=dyadic i*u)).card = dyadicCount (red 4 w) := by
      unfold dyadicCount
      congr 1
      apply filter_congr
      intro i _
      rw [dyadic_dvd_iff,map_mul,reduceFour_red]
    rw [heq]
    split_ifs with he
    · apply hq.1
      rcases he with ⟨t,ht⟩
      rw [ht]
      push_cast
      have hz : (4:ZMod 4)=0 := by decide
      linear_combination (t:ZMod 4)*hz
    · apply hq.2
      obtain ⟨t,ht⟩ := Nat.not_even_iff_odd.mp he
      rw [ht]
      push_cast
      have hz : (4:ZMod 4)=0 := by decide
      linear_combination (t:ZMod 4)*hz
  rw [sum_congr rfl hf,sum_const] at h
  split_ifs at h ⊢ <;> simp_all <;> omega

end TunnellQuaternion

end

section

/- Jacobi's four-square theorem, obtained from the quaternion counts at every prime. -/

namespace TunnellQuaternion

open Finset Quaternion
open scoped Pointwise

def divisorWeight (d : ℕ) : ℕ := if 4∣d then 0 else d

def fourDivSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors, divisorWeight d

lemma divisorWeight_mul {a b : ℕ} (h : a.Coprime b) :
    divisorWeight (a*b) = divisorWeight a*divisorWeight b := by
  have hodd : ¬(2∣a ∧ 2∣b) := by
    rintro ⟨ha,hb⟩
    have hc := Nat.dvd_gcd ha hb
    rw [h.gcd_eq_one] at hc
    omega
  have hd : 4∣a*b ↔ 4∣a ∨ 4∣b := by
    simp only [Nat.dvd_iff_mod_eq_zero] at hodd ⊢
    rw [Nat.mul_mod]
    have ha := Nat.mod_lt a (by decide : 0<4)
    have hb := Nat.mod_lt b (by decide : 0<4)
    interval_cases ha' : a%4 <;> interval_cases hb' : b%4 <;> omega
  unfold divisorWeight
  simp only [hd]
  split_ifs <;> simp_all

lemma fourDivSum_mul {a b : ℕ} (h : a.Coprime b) :
    fourDivSum (a*b) = fourDivSum a * fourDivSum b := by
  unfold fourDivSum
  rw [Nat.divisors_mul,Finset.mul_def,Finset.sum_image h.mul_injOn_divisors]
  calc
    _ = ∑ v ∈ a.divisors ×ˢ b.divisors, divisorWeight v.1 * divisorWeight v.2 := by
      apply sum_congr rfl
      intro v hv
      obtain ⟨hm,hn⟩ := mem_product.mp hv
      exact divisorWeight_mul ((h.coprime_dvd_left (Nat.mem_divisors.mp hm).1).coprime_dvd_right (Nat.mem_divisors.mp hn).1)
    _ = _ := by rw [sum_product]; simp only [←mul_sum,←sum_mul]

lemma oddDivSum_pow {p : ℕ} (h : p.Prime) (hp : p≠2) (r : ℕ) :
    fourDivSum (p^r) = ∑ i ∈ range (r+1), p^i := by
  rw [fourDivSum,Nat.sum_divisors_prime_pow h]
  apply sum_congr rfl
  intro i _
  apply if_neg
  intro hd
  have he := dvd_trans (by decide : 2∣4) hd
  exact (Nat.not_even_iff_odd.mpr ((h.odd_of_ne_two hp).pow (n:=i))) (even_iff_two_dvd.mpr he)

lemma evenDivSum_pow {r : ℕ} (hr : 0<r) : fourDivSum (2^r)=3 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  rw [fourDivSum,Nat.sum_divisors_prime_pow Nat.prime_two]
  clear hr
  induction r with
  | zero => decide
  | succ r ih =>
    rw [sum_range_succ,ih]
    have hd : 4∣2^(r+2) := by rw [pow_add]; exact dvd_mul_left _ _
    simp [divisorWeight,hd]

lemma quatShell_odd_pow_mul {p : ℕ} (h : p.Prime) (hp : p≠2) (m : ℕ) (hm : ¬p∣m) (r : ℕ) :
    (quatShell (p^r*m)).card = (∑ i ∈ range (r+1),p^i) * (quatShell m).card := by
  let : Fact p.Prime := ⟨h⟩
  induction r using Nat.twoStepInduction with
  | zero => simp
  | one =>
    have hh := quatShell_odd_recurrence hp m
    simpa [sum_range_succ,hm,Nat.add_comm] using hh.symm
  | more r hr hr' =>
    have hd : p∣p^(r+1)*m := by rw [pow_succ]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    have hdiv : p^(r+1)*m/p=p^r*m := by
      rw [pow_succ',mul_assoc,Nat.mul_div_cancel_left _ h.pos]
    have hh := quatShell_odd_recurrence hp (p^(r+1)*m)
    rw [if_pos hd,hdiv,hr,hr'] at hh
    have he : p*(p^(r+1)*m)=p^(r+2)*m := by rw [pow_succ' p (r+1),mul_assoc]
    rw [he] at hh
    simp only [sum_range_succ, pow_succ] at hh ⊢
    nlinarith

lemma quatShell_two_pow_mul (m : ℕ) (hm : ¬2∣m) {r : ℕ} (hr : 0<r) :
    (quatShell (2^r*m)).card = 3*(quatShell m).card := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  clear hr
  induction r with
  | zero => simpa [even_iff_two_dvd,hm] using quatShell_two_recurrence m
  | succ r ih =>
    have he : Even (2^(r+1)*m) := even_two.pow_of_ne_zero (by omega) |>.mul_right _
    rw [pow_succ' 2 (r+1),mul_assoc,quatShell_two_recurrence,if_pos he,ih]

theorem quatShell_card_divisors {n : ℕ} (hn : n≠0) :
    (quatShell n).card = 8 * ∑ d ∈ n.divisors with ¬4∣d, d := by
  suffices h : ∀ m : ℕ, m≠0 → (quatShell m).card = 8*fourDivSum m by
    rw [h n hn,fourDivSum,sum_filter]
    simp [divisorWeight]
  apply Nat.recOnPrimePow
  · simp
  · intro _
    simpa [fourDivSum,divisorWeight] using quatShell_one_card
  · intro m p r h hm hr ih hne
    have hm0 : m≠0 := by rintro rfl; simp at hm
    rw [fourDivSum_mul ((h.coprime_iff_not_dvd.mpr hm).pow_left r)]
    by_cases hp : p=2
    · subst p
      rw [quatShell_two_pow_mul m hm hr,evenDivSum_pow hr,ih hm0]
      ring
    · rw [quatShell_odd_pow_mul h hp m hm r,oddDivSum_pow h hp r,ih hm0]
      ring

end TunnellQuaternion

end
namespace GaussCircleFloorProof

open scoped EuclideanGeometry

/- ### Character modulo 4 and divisor sum -/

private def chi4 (d : ℕ) : ℤ :=
  if d % 4 = 1 then 1 else if d % 4 = 3 then -1 else 0

private lemma chi4_one : chi4 1 = 1 := by decide

private lemma chi4_mul (a b : ℕ) : chi4 (a * b) = chi4 a * chi4 b := by
  have ha := Nat.mod_lt a (by omega : 0 < 4)
  have hb := Nat.mod_lt b (by omega : 0 < 4)
  unfold chi4
  rw [Nat.mul_mod]
  interval_cases (a % 4) <;> interval_cases (b % 4) <;> decide

private lemma chi4_pow (p k : ℕ) : chi4 (p ^ k) = (chi4 p) ^ k := by
  induction k with
  | zero => simp [chi4_one]
  | succ k ih => rw [pow_succ, chi4_mul, ih, pow_succ]

private def divSumChi4 (n : ℕ) : ℤ := ∑ d ∈ n.divisors, chi4 d

private lemma divSumChi4_one : divSumChi4 1 = 1 := by
  simp [divSumChi4, chi4_one]

private lemma divSumChi4_mul {m n : ℕ} (hmn : Nat.Coprime m n) :
    divSumChi4 (m * n) = divSumChi4 m * divSumChi4 n := by
  simp only [divSumChi4]
  rw [hmn.divisors_mul, Finset.sum_map]
  change ∑ p ∈ (m.divisors ×ˢ n.divisors).attach, chi4 (p.1.1 * p.1.2) = _
  rw [Finset.sum_attach (s := m.divisors ×ˢ n.divisors) (f := fun p => chi4 (p.1 * p.2)),
    Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact chi4_mul a b

private lemma divSumChi4_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    divSumChi4 (p ^ k) = ∑ j ∈ Finset.range (k + 1), (chi4 p) ^ j := by
  rw [divSumChi4, Nat.divisors_prime_pow hp, Finset.sum_map]
  refine Finset.sum_congr rfl fun j _ => ?_
  simpa using chi4_pow p j

/- ### Gaussian integers: units, first-quadrant canonical form, norm -/

def giNorm (z : GaussianInt) : ℕ := z.norm.natAbs

lemma giNorm_eq (z : GaussianInt) :
    giNorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  simpa [giNorm, sq] using GaussianInt.natAbs_norm_eq z

private lemma giNorm_mul (z w : GaussianInt) : giNorm (z * w) = giNorm z * giNorm w := by
  simp [giNorm, Zsqrtd.norm_mul, Int.natAbs_mul]

private lemma giNorm_pow (z : GaussianInt) (k : ℕ) : giNorm (z ^ k) = (giNorm z) ^ k := by
  induction k with
  | zero => simp [giNorm]
  | succ k ih => rw [pow_succ, giNorm_mul, ih, pow_succ]

private lemma giNorm_star (z : GaussianInt) : giNorm (star z) = giNorm z := by
  simp [giNorm, Zsqrtd.norm_conj]

private lemma giNorm_natCast (n : ℕ) : giNorm (n : GaussianInt) = n ^ 2 := by
  simp [giNorm, Zsqrtd.norm_natCast, Int.natAbs_mul, sq]

private lemma giNorm_eq_one_iff (z : GaussianInt) : giNorm z = 1 ↔ IsUnit z :=
  Zsqrtd.norm_eq_one_iff

private lemma giNorm_eq_zero_iff (z : GaussianInt) : giNorm z = 0 ↔ z = 0 := by
  simp only [giNorm, Int.natAbs_eq_zero]
  exact Zsqrtd.norm_eq_zero_iff (d := -1) (by norm_num) z

private lemma giNorm_eq_of_associated {z w : GaussianInt} (h : Associated z w) :
    giNorm z = giNorm w := by
  rcases h with ⟨u, rfl⟩
  rw [giNorm_mul, (giNorm_eq_one_iff (u : GaussianInt)).mpr u.isUnit, mul_one]

private lemma giNorm_dvd_of_dvd {z w : GaussianInt} (h : z ∣ w) : giNorm z ∣ giNorm w := by
  rcases h with ⟨c, rfl⟩
  rw [giNorm_mul]
  exact dvd_mul_right _ _

private lemma gi_mul_star (z : GaussianInt) : z * star z = (giNorm z : GaussianInt) := by
  have h1 : (z.norm : GaussianInt) = z * star z := Zsqrtd.norm_eq_mul_conj z
  have h2 : (giNorm z : GaussianInt) = (z.norm : GaussianInt) := by
    simp [giNorm]
  exact h1.symm.trans h2.symm

private def giI : GaussianInt := ⟨0, 1⟩

private def giUnits : Finset GaussianInt := {1, -1, giI, -giI}

private lemma giUnits_card : giUnits.card = 4 := by decide

private lemma mem_giUnits_iff (u : GaussianInt) : u ∈ giUnits ↔ IsUnit u := by
  constructor
  · intro hu
    rw [← giNorm_eq_one_iff]
    simp only [giUnits, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> decide
  · intro hu
    have hnorm : u.re.natAbs ^ 2 + u.im.natAbs ^ 2 = 1 := by
      rw [← giNorm_eq, (giNorm_eq_one_iff u).mpr hu]
    have ha : u.re.natAbs ≤ 1 := by nlinarith
    have hb : u.im.natAbs ≤ 1 := by nlinarith
    have hcases : (u.re = 1 ∧ u.im = 0) ∨ (u.re = -1 ∧ u.im = 0) ∨
        (u.re = 0 ∧ u.im = 1) ∨ (u.re = 0 ∧ u.im = -1) := by
      interval_cases ha' : u.re.natAbs <;> interval_cases hb' : u.im.natAbs <;>
        omega
    simp only [giUnits, Finset.mem_insert, Finset.mem_singleton]
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; ext <;> simp [h1, h2]
    · right; left; ext <;> simp [h1, h2]
    · right; right; left; ext <;> simp [giI, h1, h2]
    · right; right; right; ext <;> simp [giI, h1, h2]

private def InQ1 (z : GaussianInt) : Prop := 0 < z.re ∧ 0 ≤ z.im

private instance : DecidablePred InQ1 := fun z => inferInstanceAs (Decidable (0 < z.re ∧ 0 ≤ z.im))

private def canon (z : GaussianInt) : GaussianInt :=
  if 0 < z.re ∧ 0 ≤ z.im then z
  else if z.re ≤ 0 ∧ 0 < z.im then -giI * z
  else if z.re < 0 ∧ z.im ≤ 0 then -z
  else giI * z

private lemma canon_associated (z : GaussianInt) : Associated z (canon z) := by
  have h2 : IsUnit (-1 : GaussianInt) := (mem_giUnits_iff (-1)).mp (by decide)
  have h3 : IsUnit giI := (mem_giUnits_iff giI).mp (by decide)
  have h4 : IsUnit (-giI) := (mem_giUnits_iff (-giI)).mp (by decide)
  unfold canon
  split_ifs
  · exact Associated.refl z
  · rcases h4 with ⟨u, hu⟩
    exact ⟨u, by rw [hu, mul_comm]⟩
  · rcases h2 with ⟨u, hu⟩
    exact ⟨u, by rw [hu]; ring⟩
  · rcases h3 with ⟨u, hu⟩
    exact ⟨u, by rw [hu, mul_comm]⟩

private lemma canon_inQ1 {z : GaussianInt} (hz : z ≠ 0) : InQ1 (canon z) := by
  have hne : z.re ≠ 0 ∨ z.im ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (by ext <;> simp [h.1, h.2])
  unfold canon InQ1
  split_ifs with h1 h2 h3
  · exact h1
  · constructor <;> simp [giI] <;> omega
  · constructor <;> simp <;> omega
  · constructor <;> simp [giI] <;> omega

private lemma eq_of_associated_inQ1 {z w : GaussianInt}
    (hz : InQ1 z) (hw : InQ1 w) (h : Associated z w) : z = w := by
  rcases h with ⟨u, hu⟩
  have hmem : (u : GaussianInt) ∈ giUnits := (mem_giUnits_iff u).mpr u.isUnit
  simp only [giUnits, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1 | h1 | h1
  · rw [h1, mul_one] at hu; exact hu
  · rw [h1] at hu
    have hre : w.re = -z.re := by rw [← hu]; simp
    have : 0 < z.re := hz.1
    have : 0 < w.re := hw.1
    omega
  · rw [h1] at hu
    have hre : w.re = -z.im := by rw [← hu]; simp [giI]
    have : 0 ≤ z.im := hz.2
    have : 0 < w.re := hw.1
    omega
  · rw [h1] at hu
    have him : w.im = -z.re := by rw [← hu]; simp [giI]
    have : 0 < z.re := hz.1
    have : 0 ≤ w.im := hw.2
    omega

private lemma canon_eq_iff_associated {z w : GaussianInt} (hz : z ≠ 0) (hw : w ≠ 0) :
    canon z = canon w ↔ Associated z w := by
  constructor
  · intro h
    exact (canon_associated z).trans (h ▸ (canon_associated w).symm)
  · intro h
    have hass : Associated (canon z) (canon w) :=
      (canon_associated z).symm.trans (h.trans (canon_associated w))
    exact eq_of_associated_inQ1 (canon_inQ1 hz) (canon_inQ1 hw) hass

private lemma canon_eq_self {z : GaussianInt} (hz : InQ1 z) : canon z = z := by
  have hz0 : z ≠ 0 := by
    intro h0; subst h0; exact lt_irrefl 0 hz.1
  exact eq_of_associated_inQ1 (canon_inQ1 hz0) hz (canon_associated z).symm

private lemma giNorm_canon (z : GaussianInt) : giNorm (canon z) = giNorm z :=
  giNorm_eq_of_associated (canon_associated z).symm

/- ### Finite sets of Gaussian integers of norm `n` -/

def giOfNorm (n : ℕ) : Finset GaussianInt :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).image fun p => (⟨p.1, p.2⟩ : GaussianInt)).filter
    fun z => giNorm z = n

lemma mem_giOfNorm_iff {n : ℕ} {z : GaussianInt} :
    z ∈ giOfNorm n ↔ giNorm z = n := by
  simp only [giOfNorm, Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro hn
    refine ⟨⟨(z.re, z.im), ⟨?_, ?_⟩, by ext <;> rfl⟩, hn⟩
    · have hle : z.re.natAbs ≤ n := by
        have hsq : z.re.natAbs ≤ z.re.natAbs ^ 2 := Nat.le_self_pow (by norm_num) _
        have := giNorm_eq z
        omega
      omega
    · have hle : z.im.natAbs ≤ n := by
        have hsq : z.im.natAbs ≤ z.im.natAbs ^ 2 := Nat.le_self_pow (by norm_num) _
        have := giNorm_eq z
        omega
      omega

private def Q1Set (n : ℕ) : Finset GaussianInt :=
  (giOfNorm n).filter InQ1

private lemma mem_Q1Set_iff {n : ℕ} {z : GaussianInt} :
    z ∈ Q1Set n ↔ giNorm z = n ∧ InQ1 z := by
  simp [Q1Set, mem_giOfNorm_iff]

private lemma card_giOfNorm_eq_four_mul {n : ℕ} (hn : 1 ≤ n) :
    (giOfNorm n).card = 4 * (Q1Set n).card := by
  have hbij : (giUnits ×ˢ Q1Set n).card = (giOfNorm n).card := by
    refine Finset.card_bij (fun p _ => p.1 * p.2) ?_ ?_ ?_
    · intro p hp
      rcases Finset.mem_product.mp hp with ⟨hu, hw⟩
      rw [mem_giOfNorm_iff, giNorm_mul]
      rw [(giNorm_eq_one_iff p.1).mpr ((mem_giUnits_iff p.1).mp hu), one_mul]
      exact (mem_Q1Set_iff.mp hw).1
    · intro p₁ hp₁ p₂ hp₂ heq
      rcases Finset.mem_product.mp hp₁ with ⟨hu₁, hw₁⟩
      rcases Finset.mem_product.mp hp₂ with ⟨hu₂, hw₂⟩
      rcases (mem_giUnits_iff p₁.1).mp hu₁ with ⟨u₁, hu₁'⟩
      rcases (mem_giUnits_iff p₂.1).mp hu₂ with ⟨u₂, hu₂'⟩
      have hass : Associated p₁.2 p₂.2 := by
        refine ⟨u₁ * u₂⁻¹, ?_⟩
        calc
          p₁.2 * ((u₁ * u₂⁻¹ : GaussianIntˣ) : GaussianInt)
            = (p₁.1 * p₁.2) * (u₂⁻¹ : GaussianIntˣ) := by
                rw [← hu₁', Units.val_mul]; ring
          _ = (p₂.1 * p₂.2) * (u₂⁻¹ : GaussianIntˣ) := by rw [heq]
          _ = p₂.2 * ((u₂ : GaussianInt) * (u₂⁻¹ : GaussianIntˣ)) := by
                rw [← hu₂']; ring
          _ = p₂.2 := by simp
      have hw_eq : p₁.2 = p₂.2 :=
        eq_of_associated_inQ1 (mem_Q1Set_iff.mp hw₁).2 (mem_Q1Set_iff.mp hw₂).2 hass
      have hw_ne : p₁.2 ≠ 0 := by
        intro h0
        have := (mem_Q1Set_iff.mp hw₁).1
        rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at this
        omega
      rw [hw_eq] at heq
      have hu_eq : p₁.1 = p₂.1 := mul_right_cancel₀ (hw_eq ▸ hw_ne) heq
      exact Prod.ext hu_eq hw_eq
    · intro z hz
      have hzn : giNorm z = n := mem_giOfNorm_iff.mp hz
      have hz0 : z ≠ 0 := by
        intro h0; rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hzn; omega
      rcases (canon_associated z).symm with ⟨u, hu⟩
      refine ⟨((u : GaussianInt), canon z), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact (mem_giUnits_iff u).mpr u.isUnit
      · exact mem_Q1Set_iff.mpr ⟨by rw [giNorm_canon, hzn], canon_inQ1 hz0⟩
      · simpa [mul_comm] using hu
  rw [← hbij, Finset.card_product, giUnits_card]

/- ### Multiplicativity of `(Q1Set n).card` -/

private lemma isCoprime_natCast {m n : ℕ} (hmn : Nat.Coprime m n) :
    IsCoprime (m : GaussianInt) (n : GaussianInt) := by
  have hbez := Nat.gcd_eq_gcd_ab m n
  rw [hmn.gcd_eq_one] at hbez
  refine ⟨(Nat.gcdA m n : GaussianInt), (Nat.gcdB m n : GaussianInt), ?_⟩
  have hcast : ((1 : ℤ) : GaussianInt) =
      ((m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n : ℤ) := by
    exact_mod_cast hbez
  push_cast at hcast
  linear_combination -hcast

private lemma isCoprime_of_dvd {a b c d : GaussianInt}
    (h : IsCoprime a b) (hc : c ∣ a) (hd : d ∣ b) : IsCoprime c d := by
  rcases h with ⟨x, y, hxy⟩
  rcases hc with ⟨u, rfl⟩
  rcases hd with ⟨v, rfl⟩
  exact ⟨x * u, y * v, by linear_combination hxy⟩

private lemma isCoprime_of_coprime_giNorm {a b : GaussianInt}
    (h : Nat.Coprime (giNorm a) (giNorm b)) : IsCoprime a b := by
  have hmn : IsCoprime (giNorm a : GaussianInt) (giNorm b : GaussianInt) := isCoprime_natCast h
  have ha : a ∣ (giNorm a : GaussianInt) := ⟨star a, (gi_mul_star a).symm⟩
  have hb : b ∣ (giNorm b : GaussianInt) := ⟨star b, (gi_mul_star b).symm⟩
  exact isCoprime_of_dvd hmn ha hb

private lemma card_Q1Set_mul {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : Nat.Coprime m n) :
    (Q1Set (m * n)).card = (Q1Set m).card * (Q1Set n).card := by
  rw [← Finset.card_product]
  symm
  refine Finset.card_bij (fun p _ => canon (p.1 * p.2)) ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨hu, hv⟩
    have hum := (mem_Q1Set_iff.mp hu).1
    have hvn := (mem_Q1Set_iff.mp hv).1
    have huv0 : p.1 * p.2 ≠ 0 := by
      intro h0
      have := giNorm_mul p.1 p.2
      rw [h0, (giNorm_eq_zero_iff 0).mpr rfl, hum, hvn] at this
      nlinarith
    exact mem_Q1Set_iff.mpr ⟨by rw [giNorm_canon, giNorm_mul, hum, hvn], canon_inQ1 huv0⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    rcases Finset.mem_product.mp hp₁ with ⟨hu₁, hv₁⟩
    rcases Finset.mem_product.mp hp₂ with ⟨hu₂, hv₂⟩
    have hum₁ := (mem_Q1Set_iff.mp hu₁).1
    have hvn₁ := (mem_Q1Set_iff.mp hv₁).1
    have hum₂ := (mem_Q1Set_iff.mp hu₂).1
    have hvn₂ := (mem_Q1Set_iff.mp hv₂).1
    have hne₁ : p₁.1 * p₁.2 ≠ 0 := by
      intro h0
      have := giNorm_mul p₁.1 p₁.2
      rw [h0, (giNorm_eq_zero_iff 0).mpr rfl, hum₁, hvn₁] at this
      nlinarith
    have hne₂ : p₂.1 * p₂.2 ≠ 0 := by
      intro h0
      have := giNorm_mul p₂.1 p₂.2
      rw [h0, (giNorm_eq_zero_iff 0).mpr rfl, hum₂, hvn₂] at this
      nlinarith
    have hass : Associated (p₁.1 * p₁.2) (p₂.1 * p₂.2) :=
      (canon_eq_iff_associated hne₁ hne₂).mp heq
    have hdvd1 : p₁.1 ∣ p₂.1 * p₂.2 := (dvd_mul_right p₁.1 p₁.2).trans hass.dvd
    have hdvd2 : p₂.1 ∣ p₁.1 * p₁.2 := (dvd_mul_right p₂.1 p₂.2).trans hass.symm.dvd
    have hcop12 : IsCoprime p₁.1 p₂.2 := isCoprime_of_coprime_giNorm (by rwa [hum₁, hvn₂])
    have hcop21 : IsCoprime p₂.1 p₁.2 := isCoprime_of_coprime_giNorm (by rwa [hum₂, hvn₁])
    have hu_ass : Associated p₁.1 p₂.1 :=
      associated_of_dvd_dvd (hcop12.dvd_of_dvd_mul_right hdvd1) (hcop21.dvd_of_dvd_mul_right hdvd2)
    have hu_eq : p₁.1 = p₂.1 :=
      eq_of_associated_inQ1 (mem_Q1Set_iff.mp hu₁).2 (mem_Q1Set_iff.mp hu₂).2 hu_ass
    have hv_dvd1 : p₁.2 ∣ p₂.2 := by
      have h1 : p₁.2 ∣ p₂.1 * p₂.2 := (dvd_mul_left p₁.2 p₁.1).trans hass.dvd
      exact hcop21.symm.dvd_of_dvd_mul_left h1
    have hv_dvd2 : p₂.2 ∣ p₁.2 := by
      have h2 : p₂.2 ∣ p₁.1 * p₁.2 := (dvd_mul_left p₂.2 p₂.1).trans hass.symm.dvd
      exact hcop12.symm.dvd_of_dvd_mul_left h2
    have hv_eq : p₁.2 = p₂.2 :=
      eq_of_associated_inQ1 (mem_Q1Set_iff.mp hv₁).2 (mem_Q1Set_iff.mp hv₂).2
        (associated_of_dvd_dvd hv_dvd1 hv_dvd2)
    exact Prod.ext hu_eq hv_eq
  · intro w hw
    have hwn := (mem_Q1Set_iff.mp hw).1
    have hwq := (mem_Q1Set_iff.mp hw).2
    have hw0 : w ≠ 0 := by
      intro h0; rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hwn; nlinarith
    have hw_dvd_mn : w ∣ (m : GaussianInt) * (n : GaussianInt) := by
      refine ⟨star w, ?_⟩
      rw [gi_mul_star, hwn, Nat.cast_mul]
    let g₁ : GaussianInt := EuclideanDomain.gcd w (m : GaussianInt)
    let g₂ : GaussianInt := EuclideanDomain.gcd w (n : GaussianInt)
    have hg1_w : g₁ ∣ w := EuclideanDomain.gcd_dvd_left w (m : GaussianInt)
    have hg1_m : g₁ ∣ (m : GaussianInt) := EuclideanDomain.gcd_dvd_right w (m : GaussianInt)
    have hg2_w : g₂ ∣ w := EuclideanDomain.gcd_dvd_left w (n : GaussianInt)
    have hg2_n : g₂ ∣ (n : GaussianInt) := EuclideanDomain.gcd_dvd_right w (n : GaussianInt)
    have hcop_g : IsCoprime g₁ g₂ :=
      isCoprime_of_dvd (isCoprime_natCast hmn) hg1_m hg2_n
    have hg12_dvd_w : g₁ * g₂ ∣ w := hcop_g.mul_dvd hg1_w hg2_w
    have hw_dvd_g12 : w ∣ g₁ * g₂ := by
      have h1 := EuclideanDomain.gcd_eq_gcd_ab w (m : GaussianInt)
      have h2 := EuclideanDomain.gcd_eq_gcd_ab w (n : GaussianInt)
      have hexp : g₁ * g₂ =
          w * (w * EuclideanDomain.gcdA w m * EuclideanDomain.gcdA w n +
               (m : GaussianInt) * EuclideanDomain.gcdB w m * EuclideanDomain.gcdA w n +
               (n : GaussianInt) * EuclideanDomain.gcdB w n * EuclideanDomain.gcdA w m) +
          ((m : GaussianInt) * (n : GaussianInt)) *
            (EuclideanDomain.gcdB w m * EuclideanDomain.gcdB w n) := by
        change EuclideanDomain.gcd w m * EuclideanDomain.gcd w n = _
        rw [h1, h2]
        ring
      rw [hexp]
      exact dvd_add (dvd_mul_right w _) (dvd_mul_of_dvd_left hw_dvd_mn _)
    have hass_w : Associated (g₁ * g₂) w := associated_of_dvd_dvd hg12_dvd_w hw_dvd_g12
    have hprod_norm : giNorm g₁ * giNorm g₂ = m * n := by
      rw [← giNorm_mul, giNorm_eq_of_associated hass_w, hwn]
    have hg1_dvd_m2 : giNorm g₁ ∣ m ^ 2 := by
      simpa [giNorm_natCast] using giNorm_dvd_of_dvd hg1_m
    have hg2_dvd_n2 : giNorm g₂ ∣ n ^ 2 := by
      simpa [giNorm_natCast] using giNorm_dvd_of_dvd hg2_n
    have hcop_g1_n : Nat.Coprime (giNorm g₁) n :=
      ((hmn.pow_left 2).coprime_dvd_left hg1_dvd_m2)
    have hcop_g2_m : Nat.Coprime (giNorm g₂) m :=
      ((hmn.symm.pow_left 2).coprime_dvd_left hg2_dvd_n2)
    have hg1_eq : giNorm g₁ = m := by
      have hd1 : giNorm g₁ ∣ m := hcop_g1_n.dvd_of_dvd_mul_right ⟨giNorm g₂, hprod_norm.symm⟩
      have hd2 : m ∣ giNorm g₁ := hcop_g2_m.symm.dvd_of_dvd_mul_right ⟨n, by linarith⟩
      exact Nat.dvd_antisymm hd1 hd2
    have hg2_eq : giNorm g₂ = n := by
      rw [hg1_eq] at hprod_norm
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) hprod_norm
    have hg1_ne : g₁ ≠ 0 := by
      intro h0; rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hg1_eq; omega
    have hg2_ne : g₂ ≠ 0 := by
      intro h0; rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hg2_eq; omega
    refine ⟨(canon g₁, canon g₂), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact mem_Q1Set_iff.mpr ⟨by rw [giNorm_canon, hg1_eq], canon_inQ1 hg1_ne⟩
    · exact mem_Q1Set_iff.mpr ⟨by rw [giNorm_canon, hg2_eq], canon_inQ1 hg2_ne⟩
    · have hc_ass : Associated (canon g₁ * canon g₂) w :=
        ((canon_associated g₁).symm.mul_mul (canon_associated g₂).symm).trans hass_w
      have hc_ne : canon g₁ * canon g₂ ≠ 0 := by
        intro h0
        have := giNorm_eq_of_associated hc_ass
        rw [h0, (giNorm_eq_zero_iff 0).mpr rfl, hwn] at this
        nlinarith
      rw [← canon_eq_self hwq]
      exact (canon_eq_iff_associated hc_ne hw0).mpr hc_ass

/- ### Prime power cases for `(Q1Set (p ^ k)).card` -/

private lemma gi_prime_of_norm_prime {π : GaussianInt} {p : ℕ} (hp : p.Prime)
    (hπ : giNorm π = p) : Prime π := by
  have hπ0 : π ≠ 0 := by
    intro h0; rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hπ; exact hp.ne_zero hπ.symm
  have hnu : ¬ IsUnit π := by
    rw [← giNorm_eq_one_iff, hπ]; exact hp.ne_one
  refine ⟨hπ0, hnu, fun x y hxy => ?_⟩
  by_cases hx : π ∣ x
  · exact Or.inl hx
  · right
    let g := EuclideanDomain.gcd π x
    have hgπ : g ∣ π := EuclideanDomain.gcd_dvd_left π x
    have hgx : g ∣ x := EuclideanDomain.gcd_dvd_right π x
    have hgdvd : giNorm g ∣ p := by rw [← hπ]; exact giNorm_dvd_of_dvd hgπ
    rcases hp.eq_one_or_self_of_dvd _ hgdvd with hg1 | hgp
    · rcases (giNorm_eq_one_iff g).mp hg1 with ⟨u, hu⟩
      have hab := EuclideanDomain.gcd_eq_gcd_ab π x
      change g = π * EuclideanDomain.gcdA π x + x * EuclideanDomain.gcdB π x at hab
      have hy : y = π * (EuclideanDomain.gcdA π x * (u⁻¹ : GaussianIntˣ) * y) +
          (x * y) * (EuclideanDomain.gcdB π x * (u⁻¹ : GaussianIntˣ)) := by
        have h1 : (1 : GaussianInt) =
            π * (EuclideanDomain.gcdA π x * (u⁻¹ : GaussianIntˣ)) +
            x * (EuclideanDomain.gcdB π x * (u⁻¹ : GaussianIntˣ)) := by
          calc
            (1 : GaussianInt) = (u : GaussianInt) * (u⁻¹ : GaussianIntˣ) := by simp
            _ = g * (u⁻¹ : GaussianIntˣ) := by rw [hu]
            _ = (π * EuclideanDomain.gcdA π x + x * EuclideanDomain.gcdB π x) *
                  (u⁻¹ : GaussianIntˣ) := by rw [hab]
            _ = _ := by ring
        calc
          y = 1 * y := (one_mul y).symm
          _ = (π * (EuclideanDomain.gcdA π x * (u⁻¹ : GaussianIntˣ)) +
                x * (EuclideanDomain.gcdB π x * (u⁻¹ : GaussianIntˣ))) * y := by rw [← h1]
          _ = _ := by ring
      rw [hy]
      exact dvd_add (dvd_mul_right π _) (dvd_mul_of_dvd_left hxy _)
    · exfalso
      rcases hgπ with ⟨c, hc⟩
      have hc1 : giNorm c = 1 := by
        have hmul := giNorm_mul g c
        rw [← hc, hπ, hgp] at hmul
        exact Nat.eq_of_mul_eq_mul_left hp.pos (by linarith)
      rcases (giNorm_eq_one_iff c).mp hc1 with ⟨u, hu⟩
      have hπg : π ∣ g := ⟨(u⁻¹ : GaussianIntˣ), by rw [hc, ← hu]; simp⟩
      exact hx (hπg.trans hgx)

private lemma card_Q1Set_two_pow (k : ℕ) : (Q1Set (2 ^ k)).card = 1 := by
  let π : GaussianInt := ⟨1, 1⟩
  have hπ_norm : giNorm π = 2 := by decide
  have hall : ∀ m : ℕ, ∀ z : GaussianInt, giNorm z = 2 ^ m → Associated z (π ^ m) := by
    intro m
    induction m with
    | zero =>
      intro z hz
      rw [pow_zero, giNorm_eq_one_iff] at hz
      rcases hz with ⟨u, hu⟩
      exact ⟨u⁻¹, by rw [pow_zero, ← hu]; simp⟩
    | succ m ih =>
      intro z hz
      have h2dvd : 2 ∣ z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
        rw [← giNorm_eq, hz, pow_succ]
        exact dvd_mul_left 2 _
      have hpar : (z.re + z.im) % 2 = 0 ∧ (z.im - z.re) % 2 = 0 := by
        have h2int : (2 : ℤ) ∣ z.re ^ 2 + z.im ^ 2 := by
          have : (z.re.natAbs ^ 2 + z.im.natAbs ^ 2 : ℤ) = z.re ^ 2 + z.im ^ 2 := by
            simp
          rw [← this]
          exact_mod_cast h2dvd
        have hsq_mod : ∀ a : ℤ, a ^ 2 % 2 = a % 2 := by
          intro a
          rcases Int.emod_two_eq_zero_or_one a with h0 | h1
          · rw [sq, Int.mul_emod, h0]; norm_num
          · rw [sq, Int.mul_emod, h1]; norm_num
        have h1 : (z.re ^ 2 + z.im ^ 2) % 2 = 0 := Int.emod_eq_zero_of_dvd h2int
        rw [Int.add_emod, hsq_mod, hsq_mod] at h1
        omega
      let w : GaussianInt := ⟨(z.re + z.im) / 2, (z.im - z.re) / 2⟩
      have hzw : z = π * w := by
        ext <;> simp [π, w] <;> omega
      have hwn : giNorm w = 2 ^ m := by
        have hmul := giNorm_mul π w
        rw [← hzw, hz, hπ_norm, pow_succ] at hmul
        omega
      have hass := ih w hwn
      rw [hzw, pow_succ']
      exact (Associated.refl π).mul_mul hass
  have hπk0 : π ^ k ≠ 0 := by
    intro h0
    have := giNorm_pow π k
    rw [h0, (giNorm_eq_zero_iff 0).mpr rfl, hπ_norm] at this
    exact (pow_ne_zero k (by norm_num : (2 : ℕ) ≠ 0)) this.symm
  have hset : Q1Set (2 ^ k) = {canon (π ^ k)} := by
    ext z
    simp only [mem_Q1Set_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨hzn, hzq⟩
      have hass : Associated z (canon (π ^ k)) :=
        (hall k z hzn).trans (canon_associated (π ^ k))
      exact eq_of_associated_inQ1 hzq (canon_inQ1 hπk0) hass
    · rintro rfl
      exact ⟨by rw [giNorm_canon, giNorm_pow, hπ_norm], canon_inQ1 hπk0⟩
  rw [hset, Finset.card_singleton]

private lemma card_Q1Set_mod4_three {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) (k : ℕ) :
    ((Q1Set (p ^ k)).card : ℤ) = if Even k then 1 else 0 := by
  have hdvd_both : ∀ z : GaussianInt, p ∣ giNorm z → (p : GaussianInt) ∣ z := by
    intro z hz
    have hmod : ((z.re : ZMod p) ^ 2 + (z.im : ZMod p) ^ 2) = 0 := by
      have h2 : (p : ℤ) ∣ z.re ^ 2 + z.im ^ 2 := by
        have : (z.re.natAbs ^ 2 + z.im.natAbs ^ 2 : ℤ) = z.re ^ 2 + z.im ^ 2 := by
          simp
        rw [← this]
        rw [giNorm_eq] at hz
        exact_mod_cast hz
      rcases h2 with ⟨c, hc⟩
      have hcast : (((z.re ^ 2 + z.im ^ 2 : ℤ) : ZMod p)) = ((p : ℤ) * c : ℤ) := by
        rw [hc]
      push_cast at hcast
      simpa using hcast
    have : Fact p.Prime := ⟨hp⟩
    have hre0 : (z.re : ZMod p) = 0 := by
      by_contra hne
      have hsq : IsSquare (-1 : ZMod p) := by
        refine ⟨(z.im : ZMod p) * (z.re : ZMod p)⁻¹, ?_⟩
        have h1 : (z.im : ZMod p) ^ 2 = -(z.re : ZMod p) ^ 2 := eq_neg_of_add_eq_zero_right hmod
        calc
          (-1 : ZMod p) = -((z.re : ZMod p) ^ 2 * ((z.re : ZMod p)⁻¹) ^ 2) := by
            rw [← mul_pow, mul_inv_cancel₀ hne, one_pow]
          _ = (-(z.re : ZMod p) ^ 2) * ((z.re : ZMod p)⁻¹) ^ 2 := by ring
          _ = (z.im : ZMod p) ^ 2 * ((z.re : ZMod p)⁻¹) ^ 2 := by rw [← h1]
          _ = ((z.im : ZMod p) * (z.re : ZMod p)⁻¹) * ((z.im : ZMod p) * (z.re : ZMod p)⁻¹) := by
            ring
      have hne3 : p % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.mp hsq
      exact hne3 hp3
    have him0 : (z.im : ZMod p) = 0 := by
      rw [hre0, zero_pow (by norm_num), zero_add] at hmod
      exact eq_zero_of_pow_eq_zero hmod
    have hdre : (p : ℤ) ∣ z.re := (ZMod.intCast_zmod_eq_zero_iff_dvd z.re p).mp hre0
    have hdim : (p : ℤ) ∣ z.im := (ZMod.intCast_zmod_eq_zero_iff_dvd z.im p).mp him0
    rcases hdre with ⟨a, ha⟩
    rcases hdim with ⟨b, hb⟩
    refine ⟨⟨a, b⟩, ?_⟩
    ext <;> simp [ha, hb]
  have hstep : ∀ m : ℕ, (Q1Set (p ^ (m + 2))).card = (Q1Set (p ^ m)).card := by
    intro m
    symm
    refine Finset.card_bij (fun w _ => (p : GaussianInt) * w) ?_ ?_ ?_
    · intro w hw
      rcases mem_Q1Set_iff.mp hw with ⟨hwn, hre, him⟩
      refine mem_Q1Set_iff.mpr ⟨?_, ?_, ?_⟩
      · rw [giNorm_mul, giNorm_natCast, hwn]; ring
      · simp
        have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp.pos
        nlinarith
      · simp
        have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp.pos
        nlinarith
    · intro w₁ _ w₂ _ heq
      have hp0 : (p : GaussianInt) ≠ 0 := by exact_mod_cast hp.ne_zero
      exact mul_left_cancel₀ hp0 heq
    · intro z hz
      rcases mem_Q1Set_iff.mp hz with ⟨hzn, hre, him⟩
      have hpdvd : p ∣ giNorm z := by
        rw [hzn, pow_add]; exact dvd_mul_of_dvd_right (dvd_pow_self p (by norm_num)) _
      rcases hdvd_both z hpdvd with ⟨w, hw⟩
      refine ⟨w, mem_Q1Set_iff.mpr ⟨?_, ?_, ?_⟩, hw.symm⟩
      · have hmul := giNorm_mul (p : GaussianInt) w
        rw [← hw, hzn, giNorm_natCast, pow_add] at hmul
        have hp2_pos : 0 < p ^ 2 := pow_pos hp.pos 2
        exact Nat.eq_of_mul_eq_mul_left hp2_pos (by linarith)
      · have hre' : z.re = (p : ℤ) * w.re := by rw [hw]; simp
        have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp.pos
        nlinarith
      · have him' : z.im = (p : ℤ) * w.im := by rw [hw]; simp
        have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp.pos
        nlinarith
  have hbase0 : (Q1Set 1).card = 1 := by
    have hset : Q1Set 1 = {1} := by
      ext z
      simp only [mem_Q1Set_iff, Finset.mem_singleton]
      constructor
      · rintro ⟨hz1, hzq⟩
        have hass : Associated z 1 := by
          rcases (giNorm_eq_one_iff z).mp hz1 with ⟨u, hu⟩
          exact ⟨u⁻¹, by rw [← hu]; simp⟩
        exact eq_of_associated_inQ1 hzq ⟨by decide, by decide⟩ hass
      · rintro rfl
        exact ⟨by decide, ⟨by decide, by decide⟩⟩
    rw [hset, Finset.card_singleton]
  have hbase1 : (Q1Set p).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro z hz
    have hzn : giNorm z = p := (mem_Q1Set_iff.mp hz).1
    rcases hdvd_both z (by rw [hzn]) with ⟨w, hw⟩
    have hmul := giNorm_mul (p : GaussianInt) w
    rw [← hw, hzn, giNorm_natCast] at hmul
    have hp2 : p ^ 2 ≤ p := by
      have hw1 : 1 ≤ giNorm w := by
        by_contra h0
        have hw0 : giNorm w = 0 := by omega
        rw [hw0, mul_zero] at hmul
        exact hp.ne_zero hmul
      nlinarith [hp.two_le]
    nlinarith [hp.two_le]
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [hbase0]
    | 1 => simp [hbase1]
    | m + 2 =>
      rw [hstep m, ih m (by omega)]
      have hev : Even (m + 2) ↔ Even m := by
        constructor
        · rintro ⟨r, hr⟩; exact ⟨r - 1, by omega⟩
        · rintro ⟨r, hr⟩; exact ⟨r + 1, by omega⟩
      simp [hev]

private lemma card_Q1Set_mod4_one {p : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) (k : ℕ) :
    (Q1Set (p ^ k)).card = k + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rcases Nat.Prime.sq_add_sq (p := p) (by omega : p % 4 ≠ 3) with ⟨a, b, hab⟩
  let π : GaussianInt := ⟨(a : ℤ), (b : ℤ)⟩
  let π' : GaussianInt := star π
  have hπ_norm : giNorm π = p := by
    simp only [giNorm_eq, π, Int.natAbs_natCast]
    exact hab
  have hπ'_norm : giNorm π' = p := by rw [giNorm_star, hπ_norm]
  have hπ_prime : Prime π := gi_prime_of_norm_prime hp hπ_norm
  have hπ'_prime : Prime π' := gi_prime_of_norm_prime hp hπ'_norm
  have hmul_p : π * π' = (p : GaussianInt) := by
    simpa [π', hπ_norm] using gi_mul_star π
  have hnot_ass : ¬ Associated π π' := by
    intro hass
    have ha_ne0 : a ≠ 0 := by
      intro h0; subst h0
      have hb2 : b ^ 2 = p := by simpa using hab
      have hb_pos : 0 < b := by nlinarith [hp.two_le]
      rcases (by omega : b = 1 ∨ 2 ≤ b) with rfl | hb2'
      · nlinarith [hp.two_le]
      · have hdvd : b ∣ p := ⟨b, by linarith⟩
        rcases hp.eq_one_or_self_of_dvd b hdvd with h1 | hbp
        · omega
        · nlinarith
    have hb_ne0 : b ≠ 0 := by
      intro h0; subst h0
      have ha2 : a ^ 2 = p := by simpa using hab
      have ha_pos : 0 < a := by nlinarith [hp.two_le]
      rcases (by omega : a = 1 ∨ 2 ≤ a) with rfl | ha2'
      · nlinarith [hp.two_le]
      · have hdvd : a ∣ p := ⟨a, by linarith⟩
        rcases hp.eq_one_or_self_of_dvd a hdvd with h1 | hap
        · omega
        · nlinarith
    have hab_ne : a ≠ b := by
      intro heq; subst heq
      have h2 : 2 ∣ p := ⟨a ^ 2, by linarith⟩
      rcases hp.eq_one_or_self_of_dvd 2 h2 with h1 | h2p
      · omega
      · omega
    rcases hass with ⟨u, hu⟩
    have hmem := (mem_giUnits_iff u).mpr u.isUnit
    simp only [giUnits, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1 | h1 | h1
    · rw [h1, mul_one] at hu
      have := congr_arg Zsqrtd.im hu
      simp [π, π'] at this; omega
    · rw [h1] at hu
      have := congr_arg Zsqrtd.re hu
      simp [π, π'] at this; omega
    · rw [h1] at hu
      have := congr_arg Zsqrtd.re hu
      simp [π, π', giI] at this; omega
    · rw [h1] at hu
      have := congr_arg Zsqrtd.re hu
      simp [π, π', giI] at this; omega
  have hall : ∀ m : ℕ, ∀ z : GaussianInt, giNorm z = p ^ m →
      ∃ j ≤ m, Associated z (π ^ j * π' ^ (m - j)) := by
    intro m
    induction m with
    | zero =>
      intro z hz
      rw [pow_zero, giNorm_eq_one_iff] at hz
      rcases hz with ⟨u, hu⟩
      exact ⟨0, le_refl 0, ⟨u⁻¹, by simp [← hu]⟩⟩
    | succ m ih =>
      intro z hz
      have hprod : z * star z = (p ^ (m + 1) : GaussianInt) := by
        simpa [hz] using gi_mul_star z
      have hπ_dvd_prod : π ∣ z * star z := by
        refine ⟨π' * (p : GaussianInt) ^ m, ?_⟩
        calc
          z * star z = (p : GaussianInt) * (p : GaussianInt) ^ m := by
            rw [hprod, pow_succ']
          _ = (π * π') * (p : GaussianInt) ^ m := by rw [hmul_p]
          _ = π * (π' * (p : GaussianInt) ^ m) := by ring
      rcases hπ_prime.dvd_or_dvd hπ_dvd_prod with hπz | hπsz
      · rcases hπz with ⟨w, hw⟩
        have hwn : giNorm w = p ^ m := by
          have hmul := giNorm_mul π w
          rw [← hw, hz, hπ_norm, pow_succ'] at hmul
          exact Nat.eq_of_mul_eq_mul_left hp.pos hmul.symm
        rcases ih w hwn with ⟨j, hjm, hass⟩
        refine ⟨j + 1, by omega, ?_⟩
        have hsub : m + 1 - (j + 1) = m - j := by omega
        rw [hsub, hw, pow_succ', mul_assoc]
        exact (Associated.refl π).mul_mul hass
      · rcases hπsz with ⟨w, hw⟩
        have hπ'z : z = π' * star w := by
          have := congr_arg star hw
          simpa [π', star_mul, mul_comm] using this
        have hwn : giNorm (star w) = p ^ m := by
          have hmul := giNorm_mul π' (star w)
          rw [← hπ'z, hz, hπ'_norm, pow_succ'] at hmul
          exact Nat.eq_of_mul_eq_mul_left hp.pos hmul.symm
        rcases ih (star w) hwn with ⟨j, hjm, hass⟩
        refine ⟨j, by omega, ?_⟩
        have hsub : m + 1 - j = (m - j) + 1 := by omega
        rw [hsub, hπ'z, pow_succ', mul_left_comm]
        exact (Associated.refl π').mul_mul hass
  rw [← Finset.card_range (k + 1)]
  symm
  refine Finset.card_bij (fun j _ => canon (π ^ j * π' ^ (k - j))) ?_ ?_ ?_
  · intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hnorm : giNorm (π ^ j * π' ^ (k - j)) = p ^ k := by
      rw [giNorm_mul, giNorm_pow, giNorm_pow, hπ_norm, hπ'_norm, ← pow_add,
        Nat.add_sub_of_le hjk]
    have hne : π ^ j * π' ^ (k - j) ≠ 0 := by
      intro h0
      rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hnorm
      exact pow_ne_zero k hp.ne_zero hnorm.symm
    exact mem_Q1Set_iff.mpr ⟨by rw [giNorm_canon, hnorm], canon_inQ1 hne⟩
  · intro j₁ hj₁ j₂ hj₂ heq
    have hjk₁ : j₁ ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₁)
    have hjk₂ : j₂ ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₂)
    have hne₁ : π ^ j₁ * π' ^ (k - j₁) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hπ_prime.ne_zero) (pow_ne_zero _ hπ'_prime.ne_zero)
    have hne₂ : π ^ j₂ * π' ^ (k - j₂) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hπ_prime.ne_zero) (pow_ne_zero _ hπ'_prime.ne_zero)
    have hass := (canon_eq_iff_associated hne₁ hne₂).mp heq
    by_contra hne
    have hcontra : ∀ a b : ℕ, a < b → b ≤ k →
        Associated (π ^ a * π' ^ (k - a)) (π ^ b * π' ^ (k - b)) → False := by
      intro a b hab hbk hba
      have hba_dvd : π ^ b * π' ^ (k - b) ∣ π ^ a * π' ^ (k - a) := hba.symm.dvd
      have hre1 : π ^ b * π' ^ (k - b) = (π ^ a * π' ^ (k - b)) * π ^ (b - a) := by
        rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le (le_of_lt hab)]
      have hre2 : π ^ a * π' ^ (k - a) = (π ^ a * π' ^ (k - b)) * π' ^ (b - a) := by
        rw [mul_assoc, ← pow_add, show (k - b) + (b - a) = k - a by omega]
      rw [hre1, hre2] at hba_dvd
      have hc0 : π ^ a * π' ^ (k - b) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hπ_prime.ne_zero) (pow_ne_zero _ hπ'_prime.ne_zero)
      have hpow_dvd : π ^ (b - a) ∣ π' ^ (b - a) := (mul_dvd_mul_iff_left hc0).mp hba_dvd
      have hπ_dvd_pow : π ∣ π' ^ (b - a) :=
        (dvd_pow_self π (by omega : b - a ≠ 0)).trans hpow_dvd
      have hπ_dvd_π' : π ∣ π' := hπ_prime.dvd_of_dvd_pow hπ_dvd_pow
      rcases hπ_dvd_π' with ⟨c, hc⟩
      have hc1 : giNorm c = 1 := by
        have hmul := giNorm_mul π c
        rw [← hc, hπ'_norm, hπ_norm] at hmul
        exact Nat.eq_of_mul_eq_mul_left hp.pos (by linarith)
      rcases (giNorm_eq_one_iff c).mp hc1 with ⟨u, hu⟩
      exact hnot_ass ⟨u, by rw [hu, ← hc]⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hcontra j₁ j₂ hlt hjk₂ hass
    · exact hcontra j₂ j₁ hgt hjk₁ hass.symm
  · intro z hz
    rcases mem_Q1Set_iff.mp hz with ⟨hzn, hzq⟩
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hzn
      exact pow_ne_zero k hp.ne_zero hzn.symm
    rcases hall k z hzn with ⟨j, hjk, hass⟩
    refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
    have hne : π ^ j * π' ^ (k - j) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hπ_prime.ne_zero) (pow_ne_zero _ hπ'_prime.ne_zero)
    rw [← canon_eq_self hzq]
    exact (canon_eq_iff_associated hne hz0).mpr hass.symm

private lemma card_Q1Set_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ((Q1Set (p ^ k)).card : ℤ) = divSumChi4 (p ^ k) := by
  rw [divSumChi4_prime_pow hp k]
  by_cases hp2 : p = 2
  · subst hp2
    rw [card_Q1Set_two_pow k]
    have hchi2 : chi4 2 = 0 := by decide
    simp only [hchi2]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj; simp [zero_pow hj]
    · intro h0; exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h0
  · have hodd : p % 2 = 1 := by
      have hndvd : ¬ (2 ∣ p) := fun h => hp2 ((hp.eq_one_or_self_of_dvd 2 h).resolve_left (by decide)).symm
      omega
    have hmod4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hmod4 with hp1 | hp3
    · rw [card_Q1Set_mod4_one hp hp1 k]
      have hchi : chi4 p = 1 := by simp [chi4, hp1]
      simp [hchi]
    · rw [card_Q1Set_mod4_three hp hp3 k]
      have hchi : chi4 p = -1 := by simp [chi4, hp3]
      simp only [hchi]
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ← ih]
        by_cases hev : Even k
        · have hodd' : ¬ Even (k + 1) := by
            rcases hev with ⟨r, hr⟩; rintro ⟨s, hs⟩; omega
          have hpow : (-1 : ℤ) ^ (k + 1) = -1 := by
            rcases hev with ⟨r, hr⟩
            rw [hr, ← two_mul, pow_succ, pow_mul]; norm_num
          simp [hev, hodd', hpow]
        · have hev' : Even (k + 1) := by
            have : k % 2 = 1 := by
              by_contra h
              exact hev ⟨k / 2, by omega⟩
            exact ⟨k / 2 + 1, by omega⟩
          have hpow : (-1 : ℤ) ^ (k + 1) = 1 := by
            rcases hev' with ⟨r, hr⟩
            rw [hr, ← two_mul, pow_mul]; norm_num
          simp [hev, hev', hpow]

private lemma card_Q1Set_eq_divSumChi4 {n : ℕ} (hn : 1 ≤ n) :
    ((Q1Set n).card : ℤ) = divSumChi4 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn1 : n = 1
    · subst hn1
      rw [divSumChi4_one]
      have hset : Q1Set 1 = {1} := by
        ext z
        simp only [mem_Q1Set_iff, Finset.mem_singleton]
        constructor
        · rintro ⟨hz1, hzq⟩
          rcases (giNorm_eq_one_iff z).mp hz1 with ⟨u, hu⟩
          exact eq_of_associated_inQ1 hzq ⟨by decide, by decide⟩ ⟨u⁻¹, by rw [← hu]; simp⟩
        · rintro rfl
          exact ⟨by decide, ⟨by decide, by decide⟩⟩
      simp [hset]
    · let p := n.minFac
      have hp : p.Prime := Nat.minFac_prime hn1
      have hpn : p ∣ n := Nat.minFac_dvd n
      let a := p ^ n.factorization p
      let b := n / a
      have hadvd : a ∣ n := Nat.ordProj_dvd n p
      have hmul : a * b = n := Nat.mul_div_cancel' hadvd
      have hcop : Nat.Coprime a b := (Nat.coprime_ordCompl hp (by omega : n ≠ 0)).pow_left _
      have ha_ge : 1 ≤ a := pow_pos hp.pos _
      have hb_ge : 1 ≤ b := Nat.pos_of_ne_zero fun hb0 => by
        rw [hb0, mul_zero] at hmul; omega
      have ha_gt1 : 1 < a := by
        have hfac : 1 ≤ n.factorization p := by
          have hne : n.factorization p ≠ 0 :=
            (hp.dvd_iff_one_le_factorization (by omega : n ≠ 0)).mp hpn |> Nat.pos_iff_ne_zero.mp
          omega
        exact one_lt_pow₀ hp.one_lt (by omega)
      have hb_lt : b < n := by nlinarith
      rw [← hmul, card_Q1Set_mul ha_ge hb_ge hcop, Nat.cast_mul, divSumChi4_mul hcop,
        card_Q1Set_prime_pow hp (n.factorization p), ih b hb_lt hb_ge]

private lemma card_giOfNorm_eq {n : ℕ} (hn : 1 ≤ n) :
    ((giOfNorm n).card : ℤ) = 4 * divSumChi4 n := by
  rw [card_giOfNorm_eq_four_mul hn, Nat.cast_mul, Nat.cast_ofNat, card_Q1Set_eq_divSumChi4 hn]

theorem shell_upper {m : ℕ} (hm : 0 < m) : (giOfNorm m).card ≤ 4 * m.divisors.card := by
  have h := card_giOfNorm_eq hm
  have hsum : divSumChi4 m ≤ (m.divisors.card : ℤ) := by
    calc
      _ ≤ ∑ d ∈ m.divisors, (1 : ℤ) :=
        Finset.sum_le_sum (fun d _ => by unfold chi4; split_ifs <;> decide)
      _ = _ := by simp
  omega

end GaussCircleFloorProof
open Finset Filter
namespace DivisorCap

private lemma local_bound (p e : ℕ) (hp : 2 ≤ p) :
    (e + 1)^14 ≤ (if p < 2^14 then 14^14 else 1) * p^e := by
  split_ifs with hsmall
  · have hquot : e + 1 ≤ 14 * (e / 14 + 1) := by omega
    have hle : e + 1 ≤ 14 * 2^(e/14) :=
      hquot.trans (Nat.mul_le_mul_left 14 (e/14).lt_two_pow_self)
    calc
      (e + 1)^14 ≤ (14 * 2^(e/14))^14 := Nat.pow_le_pow_left hle 14
      _ = 14^14 * 2^(e/14*14) := by rw [mul_pow, ← pow_mul]
      _ ≤ 14^14 * p^e := Nat.mul_le_mul_left _ <|
        (Nat.pow_le_pow_right (by decide) (Nat.div_mul_le_self e 14)).trans
          (Nat.pow_le_pow_left hp e)
  · rw [one_mul]
    calc
      (e + 1)^14 ≤ (2^e)^14 := Nat.pow_le_pow_left e.lt_two_pow_self 14
      _ = (2^14)^e := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ p^e := Nat.pow_le_pow_left (by omega) e

private lemma divisor_power_le (n : ℕ) (hn : 0 < n) :
    n.divisors.card^14 ≤ (14^14)^(2^14) * n := by
  have hsmall : (n.primeFactors.filter (fun p => p < 2^14)).card ≤ 2^14 := by
    calc
      _ ≤ (Finset.range (2^14)).card := Finset.card_le_card (fun _ hp =>
        Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = _ := Finset.card_range _
  have hcoef : (∏ p ∈ n.primeFactors, (if p < 2^14 then (14:ℕ)^14 else 1))
      ≤ (14^14)^(2^14) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
    exact pow_le_pow_right₀ (by norm_num) hsmall
  calc
    n.divisors.card^14 = ∏ p ∈ n.primeFactors, (n.factorization p + 1)^14 := by
      rw [Nat.card_divisors hn.ne', Finset.prod_pow]
    _ ≤ ∏ p ∈ n.primeFactors, (if p < 2^14 then 14^14 else 1) * p^(n.factorization p) :=
      Finset.prod_le_prod' (fun p hp => local_bound p _ (Nat.prime_of_mem_primeFactors hp).two_le)
    _ = (∏ p ∈ n.primeFactors, (if p < 2^14 then 14^14 else 1)) * n := by
      rw [Finset.prod_mul_distrib, ← Nat.prod_primeFactors_pow_factorization hn.ne']
    _ ≤ (14^14)^(2^14) * n := Nat.mul_le_mul_right n hcoef

lemma divisor_cap : ∀ᶠ t : ℕ in atTop, ∀ n ∈ Finset.Icc 1 (t^6), n.divisors.card ≤ t.sqrt := by
  filter_upwards [eventually_ge_atTop ((14^14 : ℕ)^(2^14))] with t ht
  intro n hn
  obtain ⟨hn0, hnt⟩ := Finset.mem_Icc.mp hn
  apply Nat.le_sqrt'.mpr
  apply (Nat.pow_le_pow_iff_left (by decide : 7 ≠ 0)).mp
  calc
    (n.divisors.card^2)^7 = n.divisors.card^14 := by rw [← pow_mul]
    _ ≤ (14^14)^(2^14) * n := divisor_power_le n hn0
    _ ≤ t * t^6 := Nat.mul_le_mul ht hnt
    _ = t^7 := by ring

end DivisorCap

namespace Pall
open Finset Filter TunnellQuaternion

abbrev Vec (m : ℕ) := Fin 4 → Fin (m+1)
def reps (m : ℕ) : Finset (Vec m) :=
  univ.filter fun v => ∑ i, (v i : ℕ)^2 = m

lemma many (m : ℕ) (hm : Odd m) : m ≤ 2*(reps m).card := by
  classical
  have mp : 0 < m := by obtain ⟨i,hi⟩ := hm; omega
  have nd : ¬4 ∣ m := by obtain ⟨i,hi⟩ := hm; omega
  have mem : m ∈ m.divisors.filter (fun d => ¬4 ∣ d) := by simp [nd,mp.ne']
  have lb := single_le_sum (fun x (_ : x ∈ m.divisors.filter (fun d => ¬4 ∣ d)) => Nat.zero_le x) mem
  have cnt := quatShell_card_divisors mp.ne'
  let signed (v : Vec m) (s : Fin 4 → Bool) (i : Fin 4) : ℤ :=
    if s i then -(v i : ℤ) else (v i : ℤ)
  let build (p : Vec m × (Fin 4 → Bool)) : QInt :=
    ⟨signed p.1 p.2 0, signed p.1 p.2 1, signed p.1 p.2 2, signed p.1 p.2 3⟩
  have sub : quatShell m ⊆ (((reps m) ×ˢ (univ : Finset (Fin 4 → Bool))).image build) := by
    rintro ⟨a,b,c,d⟩ h
    have hh := mem_quatShell.mp h
    rw [normSq_mk] at hh
    let F : Fin 4 → ℤ := ![a,b,c,d]
    have sumAbs : ∑ i, (F i).natAbs^2 = m := by
      apply Int.ofNat_inj.mp
      simpa [F, Fin.sum_univ_four, Int.natCast_natAbs, sq_abs, add_assoc] using hh
    have bound (i : Fin 4) : (F i).natAbs < m+1 := by
      have hle := single_le_sum (s := (univ : Finset (Fin 4)))
        (fun j _ => Nat.zero_le ((F j).natAbs^2)) (mem_univ i)
      rw [sumAbs] at hle
      nlinarith
    let v : Vec m := fun i => ⟨_,bound i⟩
    let s : Fin 4 → Bool := fun i => decide (F i < 0)
    have back (i : Fin 4) : signed v s i = F i := by
      by_cases hi : F i < 0
      · simp [signed,v,s,hi,Int.natCast_natAbs,abs_of_neg hi]
      · simp [signed,v,s,hi,Int.natCast_natAbs,abs_of_nonneg (le_of_not_gt hi)]
    refine mem_image.mpr ⟨(v,s), mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,sumAbs⟩, mem_univ _⟩, ?_⟩
    change QuaternionAlgebra.mk _ _ _ _ = _
    rw [back,back,back,back]
    rfl
  have ub := (card_le_card sub).trans card_image_le
  simp only [card_product,card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at ub
  omega
end Pall

namespace Pall
open Filter Finset GaussCircleFloorProof

private lemma perm_pair : ∀ i j : Fin 4, i ≠ j →
    ∃ e : Equiv.Perm (Fin 4), e 0 = i ∧ e 1 = j := by decide

private def fiber (m : ℕ) (p : Equiv.Perm (Fin 4) × ℕ) : Finset (Vec m) :=
  (reps m).filter fun v => (v (p.1 0) : ℕ) = p.2 ∧ (v (p.1 1) : ℕ) = p.2

private lemma fiber_eqn {m : ℕ} {e : Equiv.Perm (Fin 4)} {a : ℕ}
    {v : Vec m} (hv : v ∈ fiber m (e,a)) :
    2*a^2 + (v (e 2) : ℕ)^2 + (v (e 3) : ℕ)^2 = m := by
  obtain ⟨hh,h0,h1⟩ := mem_filter.mp hv
  have h := (Equiv.sum_comp e (fun i => (v i : ℕ)^2)).trans (mem_filter.mp hh).2
  simp only [Fin.sum_univ_four] at h
  change (v (e 0) : ℕ) = a at h0
  change (v (e 1) : ℕ) = a at h1
  rw [h0,h1] at h
  omega

private lemma fiber_card {m : ℕ} (hm : Odd m) (t : ℕ)
    (cap : ∀ n ∈ Icc 1 m, n.divisors.card ≤ t)
    (e : Equiv.Perm (Fin 4)) (a : ℕ) : (fiber m (e,a)).card ≤ 4*t := by
  classical
  by_cases empty : fiber m (e,a) = ∅
  · simp [empty]
  obtain ⟨v,hv⟩ := nonempty_iff_ne_empty.mpr empty
  have sum := fiber_eqn hv
  have hpos : 0 < m-2*a^2 := by obtain ⟨b,hb⟩ := hm; omega
  let z (w : Vec m) : GaussianInt := ⟨(w (e 2) : ℕ),(w (e 3) : ℕ)⟩
  have bound : (fiber m (e,a)).card ≤ (giOfNorm (m-2*a^2)).card := by
    apply card_le_card_of_injOn z
    · intro w hw
      apply mem_giOfNorm_iff.mpr
      have eqn := fiber_eqn hw
      simp [giNorm_eq,z]
      omega
    · intro v hv w hw he
      have h2 := congrArg Zsqrtd.re he
      have h3 := congrArg Zsqrtd.im he
      change ((v (e 2) : ℕ) : ℤ) = ((w (e 2) : ℕ) : ℤ) at h2
      change ((v (e 3) : ℕ) : ℤ) = ((w (e 3) : ℕ) : ℤ) at h3
      obtain ⟨_,v0,v1⟩ := mem_filter.mp hv
      obtain ⟨_,w0,w1⟩ := mem_filter.mp hw
      funext i
      obtain ⟨j,rfl⟩ := e.surjective i
      fin_cases j
      · exact Fin.ext (v0.trans w0.symm)
      · exact Fin.ext (v1.trans w1.symm)
      · exact Fin.ext (by exact_mod_cast h2)
      · exact Fin.ext (by exact_mod_cast h3)
  exact bound.trans ((shell_upper hpos).trans (Nat.mul_le_mul_left 4 <|
    cap _ (mem_Icc.mpr ⟨hpos,Nat.sub_le _ _⟩)))

lemma few : ∀ᶠ m : ℕ in atTop, Odd m →
    2*((reps m).filter fun v => ¬ Function.Injective v).card < m := by
  classical
  obtain ⟨B,hB⟩ := eventually_atTop.mp DivisorCap.divisor_cap
  filter_upwards [eventually_ge_atTop ((B+401^2)^2)] with m hm
  intro odd
  let t := m.sqrt
  have big : B+401^2 ≤ t := Nat.le_sqrt.mpr (by simpa [pow_two] using hm)
  have t2 : 2 ≤ t := by omega
  have tsq : t^2 ≤ m := by simpa [t,pow_two] using Nat.sqrt_le m
  have m6 : m ≤ t^6 := by
    have h := Nat.lt_succ_sqrt m
    change m < (t+1)*(t+1) at h
    have inc : t+1 ≤ t*t := by nlinarith [Nat.mul_le_mul_left t t2]
    calc m ≤ (t*t)*(t*t) := h.le.trans (Nat.mul_le_mul inc inc)
         _ = t^4 := by ring
         _ ≤ t^6 := Nat.pow_le_pow_right (by omega) (by decide)
  let I := (univ : Finset (Equiv.Perm (Fin 4))) ×ˢ range (t+1)
  have cover : ((reps m).filter fun v => ¬ Function.Injective v) ⊆ I.biUnion (fiber m) := by
    intro v hv
    obtain ⟨hh,bad⟩ := mem_filter.mp hv
    simp only [Function.Injective,not_forall,exists_prop] at bad
    obtain ⟨i,j,eq,ne⟩ := bad
    obtain ⟨e,h0,h1⟩ := perm_pair i j ne
    have hl := single_le_sum (fun l (_ : l ∈ (univ : Finset (Fin 4))) => Nat.zero_le ((v l : ℕ)^2)) (mem_univ i)
    rw [(mem_filter.mp hh).2] at hl
    have ht : (v i : ℕ) ≤ t := Nat.le_sqrt.mpr (by simpa [pow_two] using hl)
    refine mem_biUnion.mpr ⟨(e,(v i : ℕ)),mem_product.mpr ⟨mem_univ _,mem_range.mpr (by omega)⟩,?_⟩
    exact mem_filter.mpr ⟨hh,by simp [h0,h1,eq]⟩
  have fc (p : Equiv.Perm (Fin 4) × ℕ) (_ : p ∈ I) : (fiber m p).card ≤ 4*t.sqrt :=
    fiber_card odd _ (fun n hn => hB t (by omega) n (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,(mem_Icc.mp hn).2.trans m6⟩)) p.1 p.2
  have upper := (card_le_card cover).trans (card_biUnion_le_card_mul I (fiber m) _ fc)
  have ic : I.card = 24*(t+1) := by simp [I,Fintype.card_perm, Nat.factorial]
  rw [ic] at upper
  have sq : 401 ≤ t.sqrt := Nat.le_sqrt.mpr (by omega)
  have y := (Nat.mul_le_mul_right t.sqrt sq).trans (Nat.sqrt_le t)
  have grow := Nat.mul_le_mul_left t y
  have loose : t.sqrt ≤ t := Nat.sqrt_le_self _
  nlinarith only [upper,grow,tsq,y,loose,big,Nat.mul_le_mul_left t (show 400 ≤ t by omega)]
end Pall

-- Reduction Erdos338.erdos_338.variants.squares.R1 of Erdős Problem 338 — squares
-- Credit: @luciusacarr
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The squares: order `4`, restricted order `5`

* `H1` is the classical part: the squares are a basis of order exactly `4` (Lagrange's
  four-square theorem, and `8k + 7` is never a sum of at most three squares).
* `H2` is Pall's theorem: every sufficiently large integer is a sum of at most `5` distinct
  squares.  This is the hard part.
* `H3` is the matching lower bound: infinitely many integers (for instance `2 * 4 ^ k`) are not
  sums of at most `4` distinct squares.
-/

namespace OMA.R_Erdos338_erdos_338_variants_squares_R1

open Erdos338

/-- The squares form a basis of order exactly `4`. -/
def H1 : Prop :=
  basisOrder (Set.range fun k : ℕ ↦ k ^ 2) = 4

/-- Pall: every sufficiently large integer is a sum of at most `5` distinct squares. -/
def H2 : Prop :=
  HasRestrictedOrder (Set.range fun k : ℕ ↦ k ^ 2) 5

/-- Not every sufficiently large integer is a sum of at most `4` distinct squares. -/
def H3 : Prop :=
  ¬ HasRestrictedOrder (Set.range fun k : ℕ ↦ k ^ 2) 4

lemma hasRestrictedOrder_mono {A : Set ℕ} {t t' : ℕ} (h : HasRestrictedOrder A t)
    (htt : t ≤ t') : HasRestrictedOrder A t' := by
  unfold HasRestrictedOrder at *
  filter_upwards [h] with m ⟨S, hS, hc, hs⟩
  exact ⟨S, hS, hc.trans htt, hs⟩

theorem main : H1 → H2 → H3 → type_of% @Erdos338.erdos_338.variants.squares := by
  intro h1 h2 h3
  refine ⟨h1, ?_⟩
  unfold restrictedOrder
  apply le_antisymm
  · exact iInf₂_le 5 h2
  · refine le_iInf₂ fun t ht => ?_
    by_contra hlt
    have ht4 : t ≤ 4 := by
      have : (t : ℕ∞) < 5 := lt_of_not_ge hlt
      exact_mod_cast Order.le_of_lt_succ (by exact_mod_cast this)
    exact h3 (hasRestrictedOrder_mono ht ht4)

end OMA.R_Erdos338_erdos_338_variants_squares_R1

/-! For an odd integer, Jacobi’s four-square formula gives at least eight times
the integer in signed ordered representations. Taking absolute values loses a
factor of at most sixteen. Repeated coordinates contribute only a ternary
quadratic form. The reduction separates those two counts and proves the passage
from large odd integers to all large integers by adjoining one larger square. -/

namespace OMA.R_Erdos338_erdos_338_variants_squares_R1_H2_R1

open Filter Finset

def H1 : Prop := ∀ᶠ m : ℕ in atTop, Odd m → m ≤ 2 * ((univ : Finset (Fin 4 → Fin (m+1))).filter fun v => ∑ i, ((v i : ℕ)^2) = m).card

def H2 : Prop := ∀ᶠ m : ℕ in atTop, Odd m →
  2 * (((univ : Finset (Fin 4 → Fin (m+1))).filter fun v => ∑ i, ((v i : ℕ)^2) = m).filter fun v => ¬ Function.Injective v).card < m

private lemma separate (T : ℕ) : ∀ᶠ n : ℕ in atTop, ∃ k m : ℕ,
    T ≤ m ∧ Odd m ∧ n = k^2+m ∧ m < k^2 := by
  filter_upwards [eventually_ge_atTop ((8*(T+100))^2)] with n hn
  let t := n.sqrt/8
  have hq : 8*(T+100) ≤ n.sqrt := Nat.le_sqrt.mpr (by simpa [pow_two] using hn)
  have ht : T+100 ≤ t := by dsimp [t]; omega
  have h1 : 8*t ≤ n.sqrt := by dsimp [t]; omega
  have h2 : n.sqrt+1 ≤ 8*t+8 := by dsimp [t]; omega
  have lo := (Nat.mul_le_mul h1 h1).trans (Nat.sqrt_le n)
  have hi := (Nat.lt_succ_sqrt n).trans_le (Nat.mul_le_mul h2 h2)
  let k := 6*t + (n+1)%2
  have k1 : 6*t ≤ k := by dsimp [k]; omega
  have k2 : k ≤ 6*t+1 := by dsimp [k]; omega
  have hsq : 20*t ≤ t*t := by nlinarith only [Nat.mul_le_mul_right t (show 20 ≤ t by omega)]
  have hk : k^2 + T ≤ n := by nlinarith only [lo, Nat.mul_le_mul k2 k2, hsq, ht]
  have hg : n < 2*k^2 := by nlinarith only [hi, Nat.mul_le_mul k1 k1, hsq, ht]
  refine ⟨k,n-k^2,by omega,?_,by omega,by omega⟩
  rw [Nat.odd_iff]
  have hmod : k^2 % 2 = (n+1)%2 := by
    have hp : k % 2 = (n+1)%2 := by dsimp [k]; omega
    calc k^2 % 2 = (k % 2)^2 % 2 := Nat.pow_mod _ _ _
         _ = (n+1)%2 := by
           rw [hp]
           have cases : (n+1)%2 = 0 ∨ (n+1)%2 = 1 := by omega
           rcases cases with e | e <;> rw [e] <;> decide
  omega

theorem main : H1 → H2 → OMA.R_Erdos338_erdos_338_variants_squares_R1.H2 := by
  classical
  intro h1 h2
  obtain ⟨T,hT⟩ := eventually_atTop.mp (h1.and h2)
  filter_upwards [separate T] with n ⟨k,m,hm,ho,hn,hl⟩
  obtain ⟨hA,hB⟩ := hT m hm
  have ha := hA ho
  have hb := hB ho
  let reps := ((univ : Finset (Fin 4 → Fin (m+1))).filter fun v => ∑ i, ((v i : ℕ)^2) = m)
  change m ≤ 2 * reps.card at ha
  change 2 * (reps.filter fun v => ¬ Function.Injective v).card < m at hb
  have ex : ∃ v ∈ reps, Function.Injective v := by
    by_contra! h
    have he : (reps.filter fun v => ¬ Function.Injective v) = reps :=
      filter_eq_self.mpr h
    rw [he] at hb
    omega
  obtain ⟨v,hv,hinj⟩ := ex
  have hsum := (mem_filter.mp hv).2
  let f (i : Fin 4) : ℕ := (v i : ℕ)^2
  have fi : Function.Injective f := by
    intro i j h
    apply hinj
    apply Fin.ext
    dsimp [f] at h
    nlinarith only [h]
  let S := univ.image f
  have hs : ∑ x ∈ S, x = m := by
    rw [show S = univ.image f from rfl, sum_image fi.injOn]
    exact hsum
  have hk : k^2 ∉ S := by
    intro hk
    have := single_le_sum (fun x (_ : x ∈ S) => Nat.zero_le x) hk
    omega
  refine ⟨insert (k^2) S, ?_, ?_, ?_⟩
  · intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact ⟨k,rfl⟩
    · obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      exact ⟨v i,rfl⟩
  · rw [card_insert_of_notMem hk]
    simp [S, card_image_of_injective _ fi]
  · rw [sum_insert hk,hs,hn]
end OMA.R_Erdos338_erdos_338_variants_squares_R1_H2_R1

open Erdos338

private lemma fourEnough : HasOrder (Set.range fun n : ℕ => n ^ 2) 4 := by
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨a,b,c,d,h⟩ := Nat.sum_four_squares n
  refine ⟨{a^2,b^2,c^2,d^2}, ?_, by simp, ?_⟩
  · intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨a,rfl⟩
    · exact ⟨b,rfl⟩
    · exact ⟨c,rfl⟩
    · exact ⟨d,rfl⟩
  · simpa [add_assoc] using h

private lemma orderLower (t : ℕ) (ht : HasOrder (Set.range fun n : ℕ => n^2) t) : 4 ≤ t := by
  by_contra! small
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 ht
  obtain ⟨s,hs,hc,hv⟩ := hN (8*N+7) (by omega)
  let u := s + Multiset.replicate (3-s.card) 0
  have uc : u.card = 3 := by simp [u]; omega
  have uv : u.sum = 8*N+7 := by simp [u,hv]
  have us : ∀ x ∈ u, x ∈ Set.range fun n : ℕ => n^2 := by
    intro x hx
    rcases Multiset.mem_add.1 hx with hx | hx
    · exact hs x hx
    · have hx0 := Multiset.eq_of_mem_replicate hx
      exact ⟨0,by simp [hx0]⟩
  obtain ⟨x,y,z,hu⟩ := Multiset.card_eq_three.1 uc
  rw [hu] at uv us
  obtain ⟨a,rfl⟩ := us x (by simp)
  obtain ⟨b,rfl⟩ := us y (by simp)
  obtain ⟨c,rfl⟩ := us z (by simp)
  have h := congrArg (fun n : ℕ => (n : ZMod 8)) uv
  push_cast at h
  have bad : ∀ a b c : ZMod 8, a^2 + (b^2 + c^2) ≠ 7 := by decide
  have z8 : (8 : ZMod 8) = 0 := by decide
  exact bad a b c (by simpa [z8, add_assoc] using h)

private theorem solved1 : OMA.R_Erdos338_erdos_338_variants_squares_R1.H1 := by
  unfold OMA.R_Erdos338_erdos_338_variants_squares_R1.H1 basisOrder
  apply le_antisymm (iInf₂_le 4 fourEnough)
  refine le_iInf₂ fun t ht => ?_
  exact_mod_cast orderLower t ht

/-! # `2 * 4 ^ k` is not a sum of at most four distinct squares

A sum of at most four squares that is divisible by `8` has all its terms divisible by `4`,
so a representation of `2 * 4 ^ (k + 1)` by distinct squares descends to one of `2 * 4 ^ k`.
The descent ends at `2`, which is not a sum of distinct squares.
-/

namespace OMA338

open Finset

lemma sq_mod_eight (a : ℕ) : a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
  have h : a ^ 2 % 8 = (a % 8) ^ 2 % 8 := Nat.pow_mod a 2 8
  have h8 : a % 8 < 8 := Nat.mod_lt _ (by norm_num)
  rw [h]
  interval_cases (a % 8) <;> simp

/-- If at most four squares sum to a multiple of `8`, each of them is a multiple of `4`. -/
lemma four_dvd_of_sum (S : Finset ℕ) (hsq : ∀ x ∈ S, ∃ a : ℕ, a ^ 2 = x) (hcard : S.card ≤ 4)
    (hsum : (∑ x ∈ S, x) % 8 = 0) : ∀ x ∈ S, 4 ∣ x := by
  have hmod : ∀ x ∈ S, x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 4 := by
    intro x hx
    obtain ⟨a, rfl⟩ := hsq x hx
    exact sq_mod_eight a
  have hrew : ∑ x ∈ S, x % 8 =
      (S.filter (fun x => x % 8 = 1)).card + 4 * (S.filter (fun x => x % 8 = 4)).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rcases hmod x hx with h | h | h <;> simp [h]
  have hle : (S.filter (fun x => x % 8 = 1)).card + (S.filter (fun x => x % 8 = 4)).card
      ≤ S.card := by
    rw [← Finset.card_union_of_disjoint]
    · exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
        (Finset.filter_subset _ _))
    · rw [Finset.disjoint_filter]
      intro x _ h1 h4
      omega
  have hsum' : (∑ x ∈ S, x % 8) % 8 = 0 := by
    rw [← Finset.sum_nat_mod]
    exact hsum
  have hO : (S.filter (fun x => x % 8 = 1)).card = 0 := by
    rw [hrew] at hsum'
    omega
  intro x hx
  have hx1 : x % 8 ≠ 1 := by
    intro h1
    have hmem : x ∈ S.filter (fun x => x % 8 = 1) := Finset.mem_filter.2 ⟨hx, h1⟩
    rw [Finset.card_eq_zero] at hO
    rw [hO] at hmem
    exact absurd hmem (Finset.notMem_empty x)
  rcases hmod x hx with h | h | h
  · omega
  · exact absurd h hx1
  · omega

lemma key (k : ℕ) : ∀ S : Finset ℕ, (∀ x ∈ S, ∃ a : ℕ, a ^ 2 = x) → S.card ≤ 4 →
    ∑ x ∈ S, x = 2 * 4 ^ k → False := by
  induction k with
  | zero =>
    intro S hsq _ hsum
    have hsub : S ⊆ ({0, 1} : Finset ℕ) := by
      intro x hx
      have hle : x ≤ ∑ y ∈ S, y := Finset.single_le_sum (f := fun y => y) (fun _ _ => Nat.zero_le _) hx
      obtain ⟨a, rfl⟩ := hsq x hx
      have ha : a ≤ 1 := by
        by_contra hlt
        have h2 : 2 ≤ a := by omega
        have : 4 ≤ a ^ 2 := by nlinarith
        omega
      interval_cases a <;> simp
    have := Finset.sum_le_sum_of_subset (f := fun y : ℕ => y) hsub
    simp at this
    omega
  | succ k ih =>
    intro S hsq hcard hsum
    have h8 : (∑ x ∈ S, x) % 8 = 0 := by
      rw [hsum, pow_succ]
      omega
    have h4 := four_dvd_of_sum S hsq hcard h8
    apply ih (S.image (fun x => x / 4))
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨a, rfl⟩ := hsq x hx
      have h2 : 2 ∣ a := by
        have : 2 ∣ a ^ 2 := Dvd.dvd.trans (by norm_num) (h4 _ hx)
        exact Nat.prime_two.dvd_of_dvd_pow this
      obtain ⟨b, rfl⟩ := h2
      refine ⟨b, ?_⟩
      have : (2 * b) ^ 2 = 4 * b ^ 2 := by ring
      rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
    · exact Finset.card_image_le.trans hcard
    · rw [Finset.sum_image]
      · have hmul : 4 * ∑ x ∈ S, x / 4 = ∑ x ∈ S, x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          exact Nat.mul_div_cancel' (h4 x hx)
        rw [hsum, pow_succ] at hmul
        omega
      · intro x hx y hy hxy
        have hx4 := h4 x hx
        have hy4 := h4 y hy
        simp only at hxy
        omega

end OMA338

private theorem solved3 : OMA.R_Erdos338_erdos_338_variants_squares_R1.H3 := by
  intro h
  unfold Erdos338.HasRestrictedOrder at h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  have hbig : N ≤ 2 * 4 ^ N := by
    have : N < 4 ^ N := Nat.lt_pow_self (by norm_num)
    omega
  obtain ⟨S, hS, hcard, hsum⟩ := hN (2 * 4 ^ N) hbig
  refine OMA338.key N S ?_ hcard hsum
  intro x hx
  obtain ⟨a, ha⟩ := hS x hx
  exact ⟨a, ha⟩

theorem OMA.solution : type_of% @Erdos338.erdos_338.variants.squares :=
  OMA.R_Erdos338_erdos_338_variants_squares_R1.main solved1
    (OMA.R_Erdos338_erdos_338_variants_squares_R1_H2_R1.main (Filter.Eventually.of_forall Pall.many) Pall.few) solved3
