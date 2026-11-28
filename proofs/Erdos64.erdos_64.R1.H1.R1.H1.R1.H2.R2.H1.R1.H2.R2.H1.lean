import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R2
import Mathlib

/-!
# Short dyadic theta in a finite odd metabelian marking

A cyclic abelianization has an ordinary lattice patch or one of four exceptional
markings. Integer tables certify three paths of length 8 or 16. The ordinary
patch projects to the abelianization. For repeated offsets, progressions,
three-step markings and cubic differences, orbit-chart coordinates realize the
paths on the marked group itself.

Halldon supplied the equal-arm descent (note 48826). This proof uses JamesSlash's
matching reduction, the seven-face determinant and Hermite coordinate work,
the ordinary cyclic atlas, and the repeated-offset, progression, three-step
and order-three certificates of the #64 team. Codex, gpt-6.2-astra, ultra.
-/

namespace OddCyclicCertificate

/- Number the two endpoints first, then the interiors of the three routes. -/
namespace AtlasIndices
abbrev shores8 : Fin 23 → Bool := ![false,false,true,false,true,false,true,false,true,true,false,true,false,true,false,true,true,false,true,false,true,false,true]
abbrev route8 (c : Fin 3) (i : ℕ) : Fin 23 := Fin.ofNat 23 (if i=0 then 0 else if i=8 then 1 else 2+c.val*7+(i-1))
abbrev shores16 : Fin 47 → Bool := ![false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]
abbrev shores16Indexed (i : Fin 47) : Bool := #[false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true][i.val]!
abbrev route16 (c : Fin 3) (i : ℕ) : Fin 47 := Fin.ofNat 47 (if i=0 then 0 else if i=16 then 1 else 2+c.val*15+(i-1))
end AtlasIndices

namespace MetabelianRegular
def rightMatching {Q : Type*} [Group Q] (a b : Q) : SimpleGraph (Bool × Q) :=
  SimpleGraph.fromRel fun u v =>
    u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=u.2*a ∨ v.2=u.2*b)
theorem rightMatching_adj {Q : Type*} [Group Q] (a b x y : Q) :
    (rightMatching a b).Adj (false,x) (true,y) ↔ y=x ∨ y=x*a ∨ y=x*b := by
  simp [rightMatching,SimpleGraph.fromRel_adj]
end MetabelianRegular
namespace EqualArms
structure Theta {V : Type*} (B : SimpleGraph V) (d : ℕ) where
  src : V
  dst : V
  endpoints : src≠dst
  arm : Fin 3 → ℕ → V
  head : ∀ c,arm c 0=src
  last : ∀ c,arm c d=dst
  step : ∀ c i,i<d → B.Adj (arm c i) (arm c (i+1))
  avoid : ∀ c i,0 < i → i<d → arm c i≠src ∧ arm c i≠dst
  distinct : ∀ c e i j,0 < i → i<d → 0 < j → j<d → arm c i=arm e j → c=e ∧ i=j

end EqualArms

/- Model the displacement of a marked generator in its orbit ring. -/
namespace MetabelianModule
open Polynomial
open scoped Polynomial
variable {D : Type*} [AddCommGroup D]
noncomputable section

def ideal (A : Module.End ℤ D) (u : D) : Ideal ℤ[X] where
  carrier := {p | (aeval A p) u = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; change (aeval A (a+b)) u=0; simp only [map_add,LinearMap.add_apply,show (aeval A a) u = 0 from ha,show (aeval A b) u = 0 from hb,add_zero]
  smul_mem' p q h := by
    change (aeval A (p*q)) u=0
    rw [map_mul, Module.End.mul_apply, show (aeval A q) u=0 from h, map_zero]

abbrev Orbit (A : Module.End ℤ D) (u : D) := ℤ[X] ⧸ ideal A u
def x (A : Module.End ℤ D) (u : D) : Orbit A u := Ideal.Quotient.mk _ X

def evalPoly (A : Module.End ℤ D) (u : D) : ℤ[X] →+ D where
  toFun p := aeval A p u
  map_zero' := by simp
  map_add' p q := by simp

def evaluate (A : Module.End ℤ D) (u : D) : Orbit A u →+ D :=
  QuotientAddGroup.lift (ideal A u).toAddSubgroup (evalPoly A u) (fun _ h => h)

@[simp] lemma evaluate_mk (A : Module.End ℤ D) (u : D) (p : ℤ[X]) :
    evaluate A u (Ideal.Quotient.mk _ p) = aeval A p u := rfl

@[simp] lemma evaluate_one (A : Module.End ℤ D) (u : D) : evaluate A u 1=u := by
  simpa only [map_one,Module.End.one_apply] using (evaluate_mk A u 1)

lemma evaluate_injective (A : Module.End ℤ D) (u : D) : Function.Injective (evaluate A u) := by
  apply (injective_iff_map_eq_zero _).2
  intro z
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
  exact fun h => Ideal.Quotient.eq_zero_iff_mem.mpr h

lemma evaluate_mul_x (A : Module.End ℤ D) (u : D) (z : Orbit A u) :
    evaluate A u (x A u * z) = A (evaluate A u z) := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
  change evaluate A u (Ideal.Quotient.mk _ X * Ideal.Quotient.mk _ p) = _
  rw [← map_mul,evaluate_mk,map_mul,aeval_X,Module.End.mul_apply,evaluate_mk]

lemma evaluate_pow (A : Module.End ℤ D) (u : D) (n : ℕ) :
    evaluate A u (x A u ^ n)=(A^n) u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',evaluate_mul_x,ih,pow_succ',Module.End.mul_apply]

lemma orbit_nontrivial (A : Module.End ℤ D) {u : D} (hu : u≠0) : Nontrivial (Orbit A u) :=
  ⟨⟨1,0,fun h => hu (by simpa using congrArg (evaluate A u) h)⟩⟩

lemma orbit_finite (A : Module.End ℤ D) (u : D) [Finite D] : Finite (Orbit A u) :=
  Finite.of_injective _ (evaluate_injective A u)

lemma unit_of_zero_kernel {R : Type*} [CommRing R] [Finite R] (a : R)
    (h : ∀ y : R, a*y=0 → y=0) : IsUnit a := by
  have hi : Function.Injective (a*·) := by
    intro b c e
    change a*b=a*c at e
    exact sub_eq_zero.mp (h _ (by rw [mul_sub,e,sub_self]))
  obtain ⟨b,hb⟩ := (Finite.surjective_of_injective hi) 1
  exact isUnit_of_dvd_one ⟨b,hb.symm⟩

lemma orbit_unit_sub_one [Finite D] (A : Module.End ℤ D) (u : D)
    (fix : ∀ z, A z = z → z=0) : IsUnit (x A u-1) := by
  let _ := orbit_finite A u
  apply unit_of_zero_kernel
  intro z h
  apply evaluate_injective A u
  rw [map_zero]
  apply fix
  rw [sub_mul,one_mul,sub_eq_zero] at h
  simpa only [evaluate_mul_x] using congrArg (evaluate A u) h

lemma orbit_unit_two [Finite D] (A : Module.End ℤ D) (u : D)
    (odd : Odd (Nat.card D)) : IsUnit (2 : Orbit A u) := by
  let _ := orbit_finite A u
  apply unit_of_zero_kernel
  intro z h
  have hc : Nat.Coprime 2 (Nat.card D) := Nat.coprime_two_left.mpr odd
  apply evaluate_injective A u
  apply (hc.symm.nsmul_right_bijective (G := D)).injective
  change 2 • evaluate A u z = (2 : ℕ) • evaluate A u 0
  rw [map_zero, nsmul_zero]
  simpa only [two_mul,map_add,map_zero,two_nsmul] using congrArg (evaluate A u) h

end
end MetabelianModule

namespace MetabelianModule
variable {R V : Type*} [CommRing R]

structure Chart (B : SimpleGraph V) (m jump : ℕ) (x : R) where
  loc : Bool → ℕ → R → V
  sep : ∀ s t h k y z, h < m → k < m → loc s h y = loc t k z → s = t ∧ h = k ∧ y = z
  forward : ∀ h k y z,
    ((k%m = h%m ∧ z = y) ∨ (k%m = (h+1)%m ∧ z = y) ∨ (k%m = (h+jump)%m ∧ z = y+x^h)) →
    B.Adj (loc false h y) (loc true k z)

def evalVec (x : R) : {n : ℕ} → (Fin n → ℤ) → R
  | 0,_ => 0
  | n+1,c => (c 0 : R) + x * @evalVec x n (fun j => c j.succ)

lemma evalVec_sub (x : R) {n} (a b : Fin n → ℤ) :
    evalVec x (fun j => a j-b j) = evalVec x a - evalVec x b := by
  induction n with
  | zero => simp [evalVec]
  | succ n ih =>
    simp only [evalVec,Int.cast_sub]
    rw [ih (fun j => a j.succ) (fun j => b j.succ)]
    ring

lemma evalVec_add_mod (x : R) {q : ℕ} (hq : (q : R) = 0) {n : ℕ}
    (a b c : Fin n → ℤ) (h : ∀ i, (a i-b i-c i) % (q:ℤ) = 0) :
    evalVec x a = evalVec x b + evalVec x c := by
  have cast (i : Fin n) : (a i : R) = (b i : R) + (c i : R) := by
    obtain ⟨t,ht⟩ := Int.dvd_of_emod_eq_zero (h i)
    have e := congrArg (fun z : ℤ => (z : R)) ht
    push_cast at e
    rw [hq,zero_mul] at e
    linear_combination e
  clear h
  induction n with
  | zero => simp [evalVec]
  | succ n ih =>
    simp only [evalVec]
    rw [cast 0,ih (fun j => a j.succ) (fun j => b j.succ) (fun j => c j.succ)
      (fun i => cast i.succ)]
    ring

@[simp] lemma evalVec_zero (x : R) (n : ℕ) : evalVec x (fun _ : Fin n => (0:ℤ)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [evalVec,ih]

structure Table (N d H K : ℕ) where
  side : Fin N → Bool
  ht : Fin N → Fin H
  lamp : Fin N → Fin K → ℤ
  route : Fin 3 → ℕ → Fin N
  src : Fin N
  dst : Fin N

def Layer (period a b : ℕ) : Prop := a % period = b % period

instance (period a b : ℕ) : Decidable (Layer period a b) :=
  inferInstanceAs (Decidable (a%period = b%period))

def Forward {N d H K : ℕ} (P : Table N d H K) (period jump q : ℕ)
    (gap : Fin H → Fin K → ℤ) (a b : Fin N) : Prop :=
  P.side a = false ∧ P.side b = true ∧
  ((Layer period (P.ht b).val (P.ht a).val ∧ P.lamp b = P.lamp a) ∨
   (Layer period (P.ht b).val ((P.ht a).val+1) ∧ P.lamp b = P.lamp a) ∨
   (Layer period (P.ht b).val ((P.ht a).val+jump) ∧
    ∀ j, (P.lamp b j-P.lamp a j-gap (P.ht a) j) % (q:ℤ) = 0))

instance {N d H K : ℕ} (P : Table N d H K) (period jump q : ℕ)
    (gap : Fin H → Fin K → ℤ) (a b : Fin N) : Decidable (Forward P period jump q gap a b) := by
  unfold Forward; infer_instance

def Delta {K} (a b c : Fin K → ℤ) := (fun j => a j - b j) = c
instance {K} (a b c : Fin K → ℤ) : Decidable (Delta a b c) :=
  inferInstanceAs (Decidable ((fun j => a j-b j) = c))

structure Valid {N d H K L : ℕ} (P : Table N d H K) (period jump q : ℕ)
    (gap : Fin H → Fin K → ℤ) (obs : Fin L → Fin K → ℤ) : Prop where
  ends : P.src ≠ P.dst
  head : ∀ c,P.route c 0 = P.src
  last : ∀ c,P.route c d = P.dst
  interior : ∀ c (i : Fin d),0 < i.val → P.route c i.val ≠ P.src ∧ P.route c i.val ≠ P.dst
  unique : ∀ c e (i j : Fin d),0 < i.val → 0 < j.val → P.route c i.val = P.route e j.val → c = e ∧ i = j
  walk : ∀ c (i : Fin d),let a:=P.route c i.val; let b:=P.route c (i.val+1);
                          Forward P period jump q gap a b ∨ Forward P period jump q gap b a
  distinguish : ∀ i j,i ≠ j → P.side i = P.side j → P.ht i = P.ht j →
                ∃ l, Delta (P.lamp i) (P.lamp j) (obs l) ∨ Delta (P.lamp j) (P.lamp i) (obs l)

theorem tableTheta {B : SimpleGraph V} {m jump : ℕ} {x : R} (C : Chart B m jump x)
    {N d H K L period q : ℕ} (P : Table N d H K)
    (gap : Fin H → Fin K → ℤ) (obs : Fin L → Fin K → ℤ)
    (t : Valid P period jump q gap obs) (hH : H ≤ m) (hp : period = 0 ∨ period = m)
    (hq : (q:R) = 0) (hg : ∀ j,evalVec x (gap j) = x^j.val)
    (ho : ∀ j,evalVec x (obs j) ≠ 0) : Nonempty (EqualArms.Theta B d) := by
  let loc (i : Fin N) := C.loc (P.side i) (P.ht i).val (evalVec x (P.lamp i))
  have inj : Function.Injective loc := by
    intro i j h
    obtain ⟨s,k,l⟩ := C.sep _ _ _ _ _ _ (lt_of_lt_of_le (P.ht i).isLt hH)
      (lt_of_lt_of_le (P.ht j).isLt hH) h
    by_contra ne
    obtain ⟨v,alt⟩ := t.distinguish i j ne s (Fin.ext k)
    rcases alt with a|a
    · exact ho v (by rw [←a,evalVec_sub,l,sub_self])
    · exact ho v (by rw [←a,evalVec_sub,l,sub_self])
  have layer {a b : ℕ} (h : Layer period a b) : a%m = b%m := by
    rcases hp with rfl|rfl
    · change a%0 = b%0 at h
      simpa only [Nat.mod_zero] using congrArg (·%m) h
    · exact h
  have edge (i j : Fin N) (f : Forward P period jump q gap i j) : B.Adj (loc i) (loc j) := by
    obtain ⟨s,w,h⟩ := f
    dsimp only [loc]; rw [s,w]; apply C.forward
    rcases h with ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩
    · exact Or.inl ⟨layer a,congrArg (evalVec x) b⟩
    · exact Or.inr (Or.inl ⟨layer a,congrArg (evalVec x) b⟩)
    · exact Or.inr (Or.inr ⟨layer a, (evalVec_add_mod x hq _ _ _ b).trans (by rw [hg])⟩)
  refine ⟨⟨loc P.src,loc P.dst,fun h => t.ends (inj h),fun c i => loc (P.route c i),
    fun c => congrArg loc (t.head c), fun c => congrArg loc (t.last c),?_,?_,?_⟩⟩
  · intro c i hi
    rcases t.walk c ⟨i,hi⟩ with f|f
    · exact edge _ _ f
    · exact (edge _ _ f).symm
  · intro c i lo hi
    obtain ⟨a,b⟩ := t.interior c ⟨i,hi⟩ lo
    exact ⟨fun h => a (inj h),fun h => b (inj h)⟩
  · intro c e i j lo hi low high h
    obtain ⟨a,b⟩ := t.unique c e ⟨i,hi⟩ ⟨j,high⟩ lo low (inj h)
    exact ⟨a,congrArg Fin.val b⟩

end MetabelianModule

/- Cubic transverse difference. The finite routes use three rows of the chart. -/
namespace MetabelianOrderThree.rowA
open MetabelianModule

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def table : Table 47 16 15 15 where
  side := AtlasIndices.shores16Indexed
  ht i := ⟨#[0,5,0,10,10,5,5,0,1,11,11,6,6,1,1,0,5,5,5,6,1,1,11,11,6,6,5,5,0,0,10,10,1,11,11,10,10,5,6,1,1,0,0,10,11,6,6][i.val]!, by decide +revert⟩
  lamp i j := ((#[#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,-1,0,0,0,-1,-1,0,0,0,-1,-1,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0],#[0,0,0,0,0,-1,0,0,0,0,-1,0,0,0,0],#[0,0,0,0,0,-1,0,0,0,0,-1,0,0,0,0],#[-1,0,0,0,0,-1,0,0,0,0,-1,0,0,0,0],#[-1,0,0,0,0,-1,0,0,0,0,-1,0,0,0,0],#[-1,0,0,0,0,-1,0,0,0,0,-1,-1,0,0,0],#[-1,0,0,0,0,-1,0,0,0,0,-1,-1,0,0,0],#[-1,0,0,0,0,-1,-1,0,0,0,-1,-1,0,0,0],#[-1,0,0,0,0,-1,-1,0,0,0,-1,-1,0,0,0],#[-1,-1,0,0,0,-1,-1,0,0,0,-1,-1,0,0,0],#[-1,-1,0,0,0,-1,-1,0,0,0,-1,-1,0,0,0],#[-1,-1,0,0,0,-1,-1,0,0,0,-1,-1,0,0,0],#[0,-1,0,0,0,-1,-1,0,0,0,-1,-1,0,0,0],#[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0],#[1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0],#[1,-1,0,0,0,0,0,0,0,0,0,-1,0,0,0],#[1,-1,0,0,0,0,0,0,0,0,0,-1,0,0,0],#[1,-1,0,0,0,0,-1,0,0,0,0,-1,0,0,0],#[1,-1,0,0,0,0,-1,0,0,0,0,-1,0,0,0],#[1,-1,0,0,0,0,-1,0,0,0,0,-1,0,0,0],#[1,-1,0,0,0,0,-1,0,0,0,0,-1,0,0,0],#[0,-1,0,0,0,0,-1,0,0,0,0,-1,0,0,0],#[0,-1,0,0,0,0,-1,0,0,0,0,-1,0,0,0],#[0,-1,0,0,0,0,-1,0,0,0,-1,-1,0,0,0],#[0,-1,0,0,0,0,-1,0,0,0,-1,-1,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0],#[0,0,0,0,0,-1,0,0,0,0,0,-1,0,0,0],#[0,0,0,0,0,-1,0,0,0,0,0,-1,0,0,0],#[0,-1,0,0,0,-1,0,0,0,0,0,-1,0,0,0],#[0,-1,0,0,0,-1,0,0,0,0,0,-1,0,0,0],#[0,-1,0,0,0,-1,0,0,0,0,0,-1,0,0,0],#[0,-1,0,0,0,-1,0,0,0,0,0,-1,0,0,0],#[0,-1,0,0,0,-1,0,0,0,0,-1,-1,0,0,0],#[0,-1,0,0,0,-1,0,0,0,0,-1,-1,0,0,0],#[0,-1,0,0,0,-1,-1,0,0,0,-1,-1,0,0,0],#[0,-1,0,0,0,-1,-1,0,0,0,-1,-1,0,0,0]] : Array (Array ℤ))[i.val]!)[j.val]!
  route c t := if t=0 then 0 else if h : t<16 then ⟨2+c.val*15+(t-1),by have := c.isLt; omega⟩ else 1
  src := 0
  dst := 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def obs (i : Fin 16) (j : Fin 15) : ℤ := ((#[#[0,0,0,0,0,0,0,0,0,0,1,-1,0,0,0],#[0,0,0,0,0,1,-1,0,0,0,0,0,0,0,0],#[0,1,0,0,0,0,1,0,0,0,0,1,0,0,0],#[0,1,0,0,0,0,1,0,0,0,1,0,0,0,0],#[0,1,0,0,0,1,0,0,0,0,0,1,0,0,0],#[0,1,0,0,0,1,0,0,0,0,1,0,0,0,0],#[1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0],#[1,-1,0,0,0,0,0,0,0,0,1,-1,0,0,0],#[1,-1,0,0,0,1,-1,0,0,0,0,0,0,0,0],#[1,-1,0,0,0,1,-1,0,0,0,1,-1,0,0,0],#[1,0,0,0,0,0,1,0,0,0,1,0,0,0,0],#[1,0,0,0,0,1,0,0,0,0,0,1,0,0,0],#[1,0,0,0,0,1,0,0,0,0,1,0,0,0,0],#[1,1,0,0,0,1,1,0,0,0,1,1,0,0,0],#[2,-1,0,0,0,1,0,0,0,0,1,0,0,0,0],#[2,0,0,0,0,1,1,0,0,0,1,1,0,0,0]] : Array (Array ℤ))[i.val]!)[j.val]!
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def gap (i j : Fin 15) : ℤ := if i=j then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem valid : Valid table 15 5 0 gap obs := by
  constructor <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem width : ∀ i,(table.ht i).val%5 < 3 := by decide +kernel
end MetabelianOrderThree.rowA

namespace MetabelianModule
variable {R : Type*} [CommRing R] {x : R} {m : ℕ}

lemma unit_period (odd : Odd m) (period : x^m=1) : IsUnit x :=
  (isUnit_pow_iff (by obtain ⟨k,h⟩ := odd; omega : m ≠ 0)).mp (period ▸ isUnit_one)

lemma unit_sum_pow (odd : Odd m) (period : x^m=1) (two : IsUnit (2:R)) (n : ℕ) :
    IsUnit (1+x^n) := by
  have hd := Odd.add_dvd_pow_add_pow (1:R) (x^n) odd
  have p : (x^n)^m=1 := by rw [←pow_mul,Nat.mul_comm,pow_mul,period,one_pow]
  rw [one_pow,p,one_add_one_eq_two] at hd
  exact isUnit_of_dvd_unit hd two

lemma unit_cyclo12 (odd : Odd m) (period : x^m=1) (two : IsUnit (2:R)) :
    IsUnit (1-x^2+x^4) := by
  apply isUnit_of_dvd_unit _ (unit_sum_pow odd period two 6)
  exact ⟨1+x^2,by ring⟩

lemma unit_diff2 (odd : Odd m) (period : x^m=1) (two : IsUnit (2:R)) (reg : IsUnit (x-1)) :
    IsUnit (1-x^2) := by
  convert reg.neg.mul (unit_sum_pow odd period two 1) using 1; ring

lemma unit_diff4 (odd : Odd m) (period : x^m=1) (two : IsUnit (2:R)) (reg : IsUnit (x-1)) :
    IsUnit (1-x^4) := by
  convert (unit_diff2 odd period two reg).mul (unit_sum_pow odd period two 2) using 1; ring

end MetabelianModule

namespace MetabelianOrderThree
open MetabelianModule EqualArms
variable {R V : Type*} [CommRing R]

def dot {n : ℕ} (w : Fin n → R) (c : Fin n → ℤ) : R :=
  ∑ i, (c i : R) * w i

lemma dot_sub {n : ℕ} (w : Fin n → R) (a b : Fin n → ℤ) :
    dot w (fun i => a i-b i) = dot w a-dot w b := by
  simp only [dot,Int.cast_sub,sub_mul,Finset.sum_sub_distrib]

lemma dot_map {S : Type*} [CommRing S] {n : ℕ} (f : R →+* S)
    (w : Fin n → R) (c : Fin n → ℤ) : f (dot w c) = dot (fun j => f (w j)) c := by
  simp [dot]

def jump (d : ℕ) (rev : Bool) := if rev then 2*d else d

def band (rev : Bool) (j : ℕ) := if rev then (3-j)%3 else j

def place (d : ℕ) (rev : Bool) (v : Fin 15) := v.val%5 + band rev (v.val/5)*d

private theorem lane_lt (v : Fin 15) : v.val/5 < 3 := by omega

private theorem band_lt (rev : Bool) (j : ℕ) (hj : j<3) : band rev j < 3 := by
  cases rev <;> simp [band,hj]
  omega

private theorem band_inj (rev : Bool) {i j : ℕ} (hi : i<3) (hj : j<3)
    (eq : band rev i=band rev j) : i=j := by
  cases rev <;> simp [band] at eq <;> omega

private theorem place_lt {d : ℕ} (rev : Bool) {v : Fin 15} (lo : v.val%5<d) :
    place d rev v < 3*d := by
  have t := band_lt rev _ (lane_lt v)
  unfold place
  have := Nat.mul_le_mul_right d (show band rev (v.val/5) ≤ 2 by omega)
  omega

private theorem place_inj {d : ℕ} (rev : Bool) {i j : Fin 15}
    (hi : i.val%5<d) (hj : j.val%5<d) (eq : place d rev i=place d rev j) : i=j := by
  have pos : 0<d := by omega
  unfold place at eq
  have a := congrArg (· % d) eq
  have b := congrArg (· / d) eq
  simp only [Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] at a
  simp only [Nat.add_mul_div_right _ _ pos,Nat.div_eq_of_lt hi,Nat.div_eq_of_lt hj,zero_add] at b
  have := band_inj rev (lane_lt i) (lane_lt j) b
  exact Fin.ext (by omega)

private theorem across_place {d : ℕ} (rev : Bool) (i k : Fin 15)
    (step : Layer 15 k.val (i.val+5)) :
    place d rev k % (3*d) = (place d rev i + jump d rev) % (3*d) := by
  have eql : k.val=(i.val+5)%15 := by simpa only [Layer,Nat.mod_eq_of_lt k.isLt] using step
  have a : k.val%5=i.val%5 := by omega
  have b : k.val/5=(i.val/5+1)%3 := by omega
  simp only [place,a,b]
  generalize i.val%5=h
  have lt:=lane_lt i
  generalize i.val/5=j at *
  interval_cases j <;> cases rev <;> simp [band,jump] <;>
    first | (congr 1; omega) | rw [show h+2*d+d=h+3*d by omega,Nat.add_mod_right]
          | rw [show h+d+2*d=h+3*d by omega,Nat.add_mod_right]
          | rw [show h+2*d+2*d=(h+d)+3*d by omega,Nat.add_mod_right]

lemma pow_place {d : ℕ} {x : R} (rev : Bool) (period : x^(3*d)=1) (v : Fin 15) :
    x^(place d rev v) = x^(v.val%5) * (x^(jump d rev))^(v.val/5) := by
  unfold place
  rw [pow_add]
  congr 1
  have lt := lane_lt v
  generalize v.val/5=j at *
  interval_cases j <;> cases rev <;> simp [band,jump,← pow_mul] <;>
    first | (congr 1; omega) | rw [show 2*d*2=3*d+d by omega,pow_add,period,one_mul]

def weights (x u : R) (v : Fin 15) := x^(v.val%5)*u^(v.val/5)

def basis (i j : Fin 15) : ℤ := if i = j then 1 else 0

theorem dot_basis (x u : R) (v : Fin 15) : dot (weights x u) (basis v)=weights x u v := by
  classical
  simp [dot,basis,Finset.sum_ite_eq]

theorem project_fixed {S : Type*} [CommRing S] (f : R →+* S) (x u : R) (fu : f u=1)
    (c : Fin 15 → ℤ) (nonzero : dot (weights (f x) 1) c≠0) : dot (weights x u) c≠0 := by
  intro eq
  apply nonzero
  change dot (fun i : Fin 15 => (f x)^(i.val%5)*(1:S)^(i.val/5)) c = 0
  simpa only [dot_map,weights,map_mul,map_pow,fu,map_zero] using congrArg f eq

theorem bandTheta {B : SimpleGraph V} {d : ℕ} {x : R} (rev : Bool)
    (C : Chart B (3*d) (jump d rev) x) {N n K L : ℕ}
    (P : Table N n 15 K) (gap : Fin 15 → Fin K → ℤ) (obs : Fin L → Fin K → ℤ)
    (cert : Valid P 15 5 0 gap obs) (w : Fin K → R)
    (lo : ∀ i,(P.ht i).val%5 < d) (buffer : ∀ i,(P.ht i).val%5 < 4)
    (hg : ∀ v, dot w (gap v)=x^(place d rev v))
    (ho : ∀ i,dot w (obs i)≠0) : Nonempty (Theta B n) := by
  let loc (i : Fin N) := C.loc (P.side i) (place d rev (P.ht i)) (dot w (P.lamp i))
  have inj : Function.Injective loc := by
    intro i j eq
    obtain ⟨s,k,l⟩ := C.sep _ _ _ _ _ _ (place_lt rev (lo i)) (place_lt rev (lo j)) eq
    by_contra ne
    obtain ⟨z,h|h⟩ := cert.distinguish _ _ ne s (place_inj rev (lo i) (lo j) k)
    · exact ho z (by rw [← h,dot_sub,l,sub_self])
    · exact ho z (by rw [← h,dot_sub,l,sub_self])
  have edge (i j : Fin N) (h : Forward P 15 5 0 gap i j) : B.Adj (loc i) (loc j) := by
    obtain ⟨s,t,h⟩ := h
    dsimp only [loc]; rw [s,t]; apply C.forward
    rcases h with ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩
    · have he : P.ht j=P.ht i := Fin.ext (by simpa only [Layer,Nat.mod_eq_of_lt (P.ht j).isLt,Nat.mod_eq_of_lt (P.ht i).isLt] using a)
      exact .inl ⟨by rw [he],congrArg (dot w) b⟩
    · have hbuf := buffer i
      have hval : (P.ht j).val=(P.ht i).val+1 := by
        simp only [Layer,Nat.mod_eq_of_lt (P.ht j).isLt] at a
        omega
      have hstep : place d rev (P.ht j)=place d rev (P.ht i)+1 := by
        simp only [place,hval]
        rw [show ((P.ht i).val+1)/5=(P.ht i).val/5 by omega,
          show ((P.ht i).val+1)%5=(P.ht i).val%5+1 by omega]
        omega
      exact .inr (.inl ⟨congrArg (·%(3*d)) hstep,congrArg (dot w) b⟩)
    · refine .inr (.inr ⟨across_place rev _ _ a,?_⟩)
      have same : (fun z => P.lamp j z-P.lamp i z)=gap (P.ht i) := by
        funext z
        have e := b z
        change (_ : ℤ) % 0 = 0 at e
        rw [Int.emod_zero] at e
        omega
      rw [←hg,←same,dot_sub]; abel
  refine ⟨⟨loc P.src,loc P.dst,fun h => cert.ends (inj h),fun c i => loc (P.route c i),
    fun c => congrArg loc (cert.head c),fun c => congrArg loc (cert.last c),?_,?_,?_⟩⟩
  · intro c i hi
    rcases cert.walk c ⟨i,hi⟩ with h|h
    · exact edge _ _ h
    · exact (edge _ _ h).symm
  · intro c i hi li
    have h:=cert.interior c ⟨i,li⟩ hi
    exact ⟨fun e => h.1 (inj e),fun e => h.2 (inj e)⟩
  · intro c e i j hi li hj lj h
    obtain ⟨a,b⟩:=cert.unique c e ⟨i,li⟩ ⟨j,lj⟩ hi hj (inj h)
    exact ⟨a,congrArg Fin.val b⟩

end MetabelianOrderThree

namespace MetabelianOrderThree.rowA
variable {R : Type*} [CommRing R]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
def vals (x u : R) (i : Fin 16) : R := (#[-u^2*x + u^2,-u*x + u,u^2*x + u*x + x,u^2 + u*x + x,u^2*x + u + x,u^2 + u + x,1 - x,-u^2*x + u^2 - x + 1,-u*x + u - x + 1,-u^2*x + u^2 - u*x + u - x + 1,u^2 + u*x + 1,u^2*x + u + 1,u^2 + u + 1,u^2*x + u^2 + u*x + u + x + 1,u^2 + u - x + 2,u^2*x + u^2 + u*x + u + 2] : Array R)[i.val]?.getD 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem eval_obs (x u : R) (i : Fin 16) : dot (weights x u) (obs i)=vals x u i := by
  fin_cases i
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(x^0*u^0)+(((0:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((0:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((1:ℤ):R)*(x^0*u^2)+(((-1:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = -u^2*x + u^2
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(x^0*u^0)+(((0:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((1:ℤ):R)*(x^0*u^1)+(((-1:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((0:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = -u*x + u
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(x^0*u^0)+(((1:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((0:ℤ):R)*(x^0*u^1)+(((1:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((0:ℤ):R)*(x^0*u^2)+(((1:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = u^2*x + u*x + x
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(x^0*u^0)+(((1:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((0:ℤ):R)*(x^0*u^1)+(((1:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((1:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = u^2 + u*x + x
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(x^0*u^0)+(((1:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((1:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((0:ℤ):R)*(x^0*u^2)+(((1:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = u^2*x + u + x
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(x^0*u^0)+(((1:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((1:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((1:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = u^2 + u + x
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(x^0*u^0)+(((-1:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((0:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((0:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = 1 - x
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(x^0*u^0)+(((-1:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((0:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((1:ℤ):R)*(x^0*u^2)+(((-1:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = -u^2*x + u^2 - x + 1
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(x^0*u^0)+(((-1:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((1:ℤ):R)*(x^0*u^1)+(((-1:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((0:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = -u*x + u - x + 1
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(x^0*u^0)+(((-1:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((1:ℤ):R)*(x^0*u^1)+(((-1:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((1:ℤ):R)*(x^0*u^2)+(((-1:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = -u^2*x + u^2 - u*x + u - x + 1
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(x^0*u^0)+(((0:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((0:ℤ):R)*(x^0*u^1)+(((1:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((1:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = u^2 + u*x + 1
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(x^0*u^0)+(((0:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((1:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((0:ℤ):R)*(x^0*u^2)+(((1:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = u^2*x + u + 1
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(x^0*u^0)+(((0:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((1:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((1:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = u^2 + u + 1
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(x^0*u^0)+(((1:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((1:ℤ):R)*(x^0*u^1)+(((1:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((1:ℤ):R)*(x^0*u^2)+(((1:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = u^2*x + u^2 + u*x + u + x + 1
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((2:ℤ):R)*(x^0*u^0)+(((-1:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((1:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((1:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = u^2 + u - x + 2
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((2:ℤ):R)*(x^0*u^0)+(((0:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((1:ℤ):R)*(x^0*u^1)+(((1:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((1:ℤ):R)*(x^0*u^2)+(((1:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = u^2*x + u^2 + u*x + u + 2
    push_cast
    ring
end MetabelianOrderThree.rowA

namespace MetabelianOrderThree.rowA
open MetabelianModule
variable {R : Type*} [CommRing R] [Nontrivial R]
omit [Nontrivial R] in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
private theorem unit_eq {a b : R} (h : IsUnit a) (eq : a=b) : IsUnit b := eq ▸ h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem fixed (x : R) (ux : IsUnit x) (reg : IsUnit (x-1)) (plus : IsUnit (x+1)) (two : IsUnit (2:R))
    (h3 : (3:R)≠0) (h2 : x+2≠0) (h1 : 2*x+1≠0) (h4 : 4-x≠0) (i : Fin 16) :
    dot (weights x 1) (obs i)≠0 := by
  rw [eval_obs]
  fin_cases i
  · change (-(1:R)^2*x + (1:R)^2) ≠ 0
    intro h
    have ok : IsUnit (1 - x : R) := unit_eq ((reg).mul (isUnit_one.neg)) (by ring)
    apply (one_ne_zero (α := R))
    apply ok.mul_right_inj.mp
    linear_combination h
  · change (-(1:R)*x + (1:R)) ≠ 0
    intro h
    have ok : IsUnit (1 - x : R) := unit_eq ((reg).mul (isUnit_one.neg)) (by ring)
    apply (one_ne_zero (α := R))
    apply ok.mul_right_inj.mp
    linear_combination h
  · change ((1:R)^2*x + (1:R)*x + x) ≠ 0
    intro h
    have ok : IsUnit (x : R) := unit_eq (ux) (by ring)
    apply h3
    apply ok.mul_right_inj.mp
    linear_combination h
  · change ((1:R)^2 + (1:R)*x + x) ≠ 0
    intro h
    have ok : IsUnit (1 : R) := unit_eq (isUnit_one) (by ring)
    apply h1
    apply ok.mul_right_inj.mp
    linear_combination h
  · change ((1:R)^2*x + (1:R) + x) ≠ 0
    intro h
    have ok : IsUnit (1 : R) := unit_eq (isUnit_one) (by ring)
    apply h1
    apply ok.mul_right_inj.mp
    linear_combination h
  · change ((1:R)^2 + (1:R) + x) ≠ 0
    intro h
    have ok : IsUnit (1 : R) := unit_eq (isUnit_one) (by ring)
    apply h2
    apply ok.mul_right_inj.mp
    linear_combination h
  · change (1 - x) ≠ 0
    intro h
    have ok : IsUnit (1 - x : R) := unit_eq ((reg).mul (isUnit_one.neg)) (by ring)
    apply (one_ne_zero (α := R))
    apply ok.mul_right_inj.mp
    linear_combination h
  · change (-(1:R)^2*x + (1:R)^2 - x + 1) ≠ 0
    intro h
    have ok : IsUnit (2 - 2*x : R) := unit_eq (((reg).mul (two)).mul (isUnit_one.neg)) (by ring)
    apply (one_ne_zero (α := R))
    apply ok.mul_right_inj.mp
    linear_combination h
  · change (-(1:R)*x + (1:R) - x + 1) ≠ 0
    intro h
    have ok : IsUnit (2 - 2*x : R) := unit_eq (((reg).mul (two)).mul (isUnit_one.neg)) (by ring)
    apply (one_ne_zero (α := R))
    apply ok.mul_right_inj.mp
    linear_combination h
  · change (-(1:R)^2*x + (1:R)^2 - (1:R)*x + (1:R) - x + 1) ≠ 0
    intro h
    have ok : IsUnit (1 - x : R) := unit_eq ((reg).mul (isUnit_one.neg)) (by ring)
    apply h3
    apply ok.mul_right_inj.mp
    linear_combination h
  · change ((1:R)^2 + (1:R)*x + 1) ≠ 0
    intro h
    have ok : IsUnit (1 : R) := unit_eq (isUnit_one) (by ring)
    apply h2
    apply ok.mul_right_inj.mp
    linear_combination h
  · change ((1:R)^2*x + (1:R) + 1) ≠ 0
    intro h
    have ok : IsUnit (1 : R) := unit_eq (isUnit_one) (by ring)
    apply h2
    apply ok.mul_right_inj.mp
    linear_combination h
  · change ((1:R)^2 + (1:R) + 1) ≠ 0
    intro h
    have ok : IsUnit (1 : R) := unit_eq (isUnit_one) (by ring)
    apply h3
    apply ok.mul_right_inj.mp
    linear_combination h
  · change ((1:R)^2*x + (1:R)^2 + (1:R)*x + (1:R) + x + 1) ≠ 0
    intro h
    have ok : IsUnit (x + 1 : R) := unit_eq (plus) (by ring)
    apply h3
    apply ok.mul_right_inj.mp
    linear_combination h
  · change ((1:R)^2 + (1:R) - x + 2) ≠ 0
    intro h
    have ok : IsUnit (1 : R) := unit_eq (isUnit_one) (by ring)
    apply h4
    apply ok.mul_right_inj.mp
    linear_combination h
  · change ((1:R)^2*x + (1:R)^2 + (1:R)*x + (1:R) + 2) ≠ 0
    intro h
    have ok : IsUnit (2 : R) := unit_eq (two) (by ring)
    apply h2
    apply ok.mul_right_inj.mp
    linear_combination h
end MetabelianOrderThree.rowA

namespace MetabelianOrderThree.rowB
open MetabelianModule

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def table : Table 47 16 15 15 where
  side := AtlasIndices.shores16Indexed
  ht i := ⟨#[1,1,1,11,12,12,2,2,7,6,6,5,10,10,0,0,1,6,5,10,10,0,0,1,11,12,12,2,2,7,6,6,2,2,7,6,6,5,10,10,0,0,1,11,12,12,2][i.val]!, by decide +revert⟩
  lamp i j := ((#[#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,1,0,0,1,0,0,0,0,1,-1,1,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0],#[0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0],#[0,0,1,0,0,0,0,0,0,0,0,-1,1,0,0],#[0,0,1,0,0,0,0,0,0,0,0,-1,1,0,0],#[0,0,1,0,0,0,0,0,0,0,0,-1,1,0,0],#[0,0,1,0,0,0,0,0,0,0,0,-1,1,0,0],#[0,0,1,0,0,1,0,0,0,0,0,-1,1,0,0],#[0,0,1,0,0,1,0,0,0,0,0,-1,1,0,0],#[0,0,1,0,0,1,0,0,0,0,1,-1,1,0,0],#[0,0,1,0,0,1,0,0,0,0,1,-1,1,0,0],#[0,0,1,0,0,1,0,0,0,0,1,-1,1,0,0],#[0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,1,0,0,0,1,0,0,0,0,0,0,0,0,0],#[0,1,0,0,0,1,0,0,0,0,0,0,0,0,0],#[0,1,0,0,0,1,0,0,0,0,1,0,0,0,0],#[0,1,0,0,0,1,0,0,0,0,1,0,0,0,0],#[0,1,0,0,0,1,0,0,0,0,1,0,0,0,0],#[0,1,0,0,0,1,0,0,0,0,1,-1,0,0,0],#[0,1,0,0,0,1,0,0,0,0,1,-1,0,0,0],#[0,1,0,0,0,1,0,0,0,0,1,-1,0,0,0],#[0,1,0,0,0,1,0,0,0,0,1,-1,1,0,0],#[0,1,0,0,0,1,0,0,0,0,1,-1,1,0,0],#[0,1,1,0,0,1,0,0,0,0,1,-1,1,0,0],#[0,1,1,0,0,1,0,0,0,0,1,-1,1,0,0],#[0,1,1,0,0,1,0,0,0,0,1,-1,1,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,1,0,0,1,0,0,0,0,0,0,0,0,0],#[0,0,1,0,0,1,0,0,0,0,0,0,0,0,0],#[0,0,1,0,0,1,0,0,0,0,1,0,0,0,0],#[0,0,1,0,0,1,0,0,0,0,1,0,0,0,0],#[0,0,1,0,0,1,0,0,0,0,1,0,0,0,0],#[0,0,1,0,0,1,0,0,0,0,1,-1,0,0,0],#[0,0,1,0,0,1,0,0,0,0,1,-1,0,0,0],#[0,0,1,0,0,1,0,0,0,0,1,-1,0,0,0],#[0,0,1,0,0,1,0,0,0,0,1,-1,1,0,0]] : Array (Array ℤ))[i.val]!)[j.val]!
  route c t := if t=0 then 0 else if h : t<16 then ⟨2+c.val*15+(t-1),by have := c.isLt; omega⟩ else 1
  src := 0
  dst := 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def obs (i : Fin 7) (j : Fin 15) : ℤ := ((#[#[0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0],#[0,0,1,0,0,1,0,0,0,0,1,-1,1,0,0],#[0,0,1,0,0,1,0,0,0,0,1,0,0,0,0],#[0,1,-1,0,0,0,0,0,0,0,0,0,0,0,0],#[0,1,-1,0,0,0,0,0,0,0,0,1,-1,0,0],#[0,1,0,0,0,1,0,0,0,0,1,-1,1,0,0],#[0,1,0,0,0,1,0,0,0,0,1,0,0,0,0]] : Array (Array ℤ))[i.val]!)[j.val]!
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def gap (i j : Fin 15) : ℤ := if i=j then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem valid : Valid table 15 5 0 gap obs := by
  constructor <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem width : ∀ i,(table.ht i).val%5 < 3 := by decide +kernel
end MetabelianOrderThree.rowB

namespace MetabelianOrderThree.rowB
variable {R : Type*} [CommRing R]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
def vals (x u : R) (i : Fin 7) : R := (#[-u^2*x^2 + u^2*x,u^2*x^2 - u^2*x + u^2 + u + x^2,u^2 + u + x^2,-x^2 + x,-u^2*x^2 + u^2*x - x^2 + x,u^2*x^2 - u^2*x + u^2 + u + x,u^2 + u + x] : Array R)[i.val]?.getD 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem eval_obs (x u : R) (i : Fin 7) : dot (weights x u) (obs i)=vals x u i := by
  fin_cases i
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(x^0*u^0)+(((0:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((0:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((0:ℤ):R)*(x^0*u^2)+(((1:ℤ):R)*(x^1*u^2)+(((-1:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = -u^2*x^2 + u^2*x
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(x^0*u^0)+(((0:ℤ):R)*(x^1*u^0)+(((1:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((1:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((1:ℤ):R)*(x^0*u^2)+(((-1:ℤ):R)*(x^1*u^2)+(((1:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = u^2*x^2 - u^2*x + u^2 + u + x^2
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(x^0*u^0)+(((0:ℤ):R)*(x^1*u^0)+(((1:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((1:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((1:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = u^2 + u + x^2
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(x^0*u^0)+(((1:ℤ):R)*(x^1*u^0)+(((-1:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((0:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((0:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = -x^2 + x
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(x^0*u^0)+(((1:ℤ):R)*(x^1*u^0)+(((-1:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((0:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((0:ℤ):R)*(x^0*u^2)+(((1:ℤ):R)*(x^1*u^2)+(((-1:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = -u^2*x^2 + u^2*x - x^2 + x
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(x^0*u^0)+(((1:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((1:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((1:ℤ):R)*(x^0*u^2)+(((-1:ℤ):R)*(x^1*u^2)+(((1:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = u^2*x^2 - u^2*x + u^2 + u + x
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(x^0*u^0)+(((1:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((1:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((1:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = u^2 + u + x
    push_cast
    ring
end MetabelianOrderThree.rowB

namespace MetabelianOrderThree.rowB
open MetabelianModule
variable {R : Type*} [CommRing R] [Nontrivial R]
omit [Nontrivial R] in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
private theorem unit_eq {a b : R} (h : IsUnit a) (eq : a=b) : IsUnit b := eq ▸ h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem charThree (x : R) (ux : IsUnit x) (reg : IsUnit (x-1)) (plus : IsUnit (x+1)) (two : IsUnit (2:R)) (three : (3:R)=0) (i : Fin 7) :
    dot (weights x 1) (obs i)≠0 := by
  rw [eval_obs]
  fin_cases i
  · change (-(1:R)^2*x^2 + (1:R)^2*x) ≠ 0
    intro h
    have ok : IsUnit (-x^2 + x : R) := unit_eq (((ux).mul (reg)).mul (isUnit_one.neg)) (by ring)
    apply ok.ne_zero
    linear_combination h+(0)*three
  · change ((1:R)^2*x^2 - (1:R)^2*x + (1:R)^2 + (1:R) + x^2) ≠ 0
    intro h
    have ok : IsUnit (-x^2 + 2*x - 1 : R) := unit_eq (((reg).mul (reg)).mul (isUnit_one.neg)) (by ring)
    apply ok.ne_zero
    linear_combination h+(-x^2 + x - 1)*three
  · change ((1:R)^2 + (1:R) + x^2) ≠ 0
    intro h
    have ok : IsUnit (x^2 - 1 : R) := unit_eq ((reg).mul (plus)) (by ring)
    apply ok.ne_zero
    linear_combination h+(-1)*three
  · change (-x^2 + x) ≠ 0
    intro h
    have ok : IsUnit (-x^2 + x : R) := unit_eq (((ux).mul (reg)).mul (isUnit_one.neg)) (by ring)
    apply ok.ne_zero
    linear_combination h+(0)*three
  · change (-(1:R)^2*x^2 + (1:R)^2*x - x^2 + x) ≠ 0
    intro h
    have ok : IsUnit (-2*x^2 + 2*x : R) := unit_eq ((((ux).mul (reg)).mul (two)).mul (isUnit_one.neg)) (by ring)
    apply ok.ne_zero
    linear_combination h+(0)*three
  · change ((1:R)^2*x^2 - (1:R)^2*x + (1:R)^2 + (1:R) + x) ≠ 0
    intro h
    have ok : IsUnit (x^2 - 1 : R) := unit_eq ((reg).mul (plus)) (by ring)
    apply ok.ne_zero
    linear_combination h+(-1)*three
  · change ((1:R)^2 + (1:R) + x) ≠ 0
    intro h
    have ok : IsUnit (x - 1 : R) := unit_eq (reg) (by ring)
    apply ok.ne_zero
    linear_combination h+(-1)*three
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem minusHalf (x : R) (two : IsUnit (2:R)) (three : IsUnit (3:R)) (eqn : 2*x + 1=0) (i : Fin 7) :
    dot (weights x 1) (obs i)≠0 := by
  rw [eval_obs]
  fin_cases i
  · change (-(1:R)^2*x^2 + (1:R)^2*x) ≠ 0
    intro h
    have ok : IsUnit (3:R) := unit_eq (three) (by ring)
    apply ok.ne_zero
    linear_combination (-4) * h + (3 - 2*x) * eqn
  · change ((1:R)^2*x^2 - (1:R)^2*x + (1:R)^2 + (1:R) + x^2) ≠ 0
    intro h
    have ok : IsUnit (12:R) := unit_eq (((two).mul (two)).mul (three)) (by ring)
    apply ok.ne_zero
    linear_combination (4) * h + (4 - 4*x) * eqn
  · change ((1:R)^2 + (1:R) + x^2) ≠ 0
    intro h
    have ok : IsUnit (9:R) := unit_eq ((three).mul (three)) (by ring)
    apply ok.ne_zero
    linear_combination (4) * h + (1 - 2*x) * eqn
  · change (-x^2 + x) ≠ 0
    intro h
    have ok : IsUnit (3:R) := unit_eq (three) (by ring)
    apply ok.ne_zero
    linear_combination (-4) * h + (3 - 2*x) * eqn
  · change (-(1:R)^2*x^2 + (1:R)^2*x - x^2 + x) ≠ 0
    intro h
    have ok : IsUnit (6:R) := unit_eq ((two).mul (three)) (by ring)
    apply ok.ne_zero
    linear_combination (-4) * h + (6 - 4*x) * eqn
  · change ((1:R)^2*x^2 - (1:R)^2*x + (1:R)^2 + (1:R) + x) ≠ 0
    intro h
    have ok : IsUnit (9:R) := unit_eq ((three).mul (three)) (by ring)
    apply ok.ne_zero
    linear_combination (4) * h + (1 - 2*x) * eqn
  · change ((1:R)^2 + (1:R) + x) ≠ 0
    intro h
    have ok : IsUnit (3:R) := unit_eq (three) (by ring)
    apply ok.ne_zero
    linear_combination (2) * h + (-1) * eqn
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem atFour (x : R) (two : IsUnit (2:R)) (three : IsUnit (3:R)) (five : IsUnit (5:R)) (eqn : 4 - x=0) (i : Fin 7) :
    dot (weights x 1) (obs i)≠0 := by
  rw [eval_obs]
  fin_cases i
  · change (-(1:R)^2*x^2 + (1:R)^2*x) ≠ 0
    intro h
    have ok : IsUnit (12:R) := unit_eq (((two).mul (two)).mul (three)) (by ring)
    apply ok.ne_zero
    linear_combination (-1) * h + (x + 3) * eqn
  · change ((1:R)^2*x^2 - (1:R)^2*x + (1:R)^2 + (1:R) + x^2) ≠ 0
    intro h
    have ok : IsUnit (30:R) := unit_eq (((two).mul (three)).mul (five)) (by ring)
    apply ok.ne_zero
    linear_combination (1) * h + (2*x + 7) * eqn
  · change ((1:R)^2 + (1:R) + x^2) ≠ 0
    intro h
    have ok : IsUnit (18:R) := unit_eq (((two).mul (three)).mul (three)) (by ring)
    apply ok.ne_zero
    linear_combination (1) * h + (x + 4) * eqn
  · change (-x^2 + x) ≠ 0
    intro h
    have ok : IsUnit (12:R) := unit_eq (((two).mul (two)).mul (three)) (by ring)
    apply ok.ne_zero
    linear_combination (-1) * h + (x + 3) * eqn
  · change (-(1:R)^2*x^2 + (1:R)^2*x - x^2 + x) ≠ 0
    intro h
    have ok : IsUnit (24:R) := unit_eq ((((two).mul (two)).mul (two)).mul (three)) (by ring)
    apply ok.ne_zero
    linear_combination (-1) * h + (2*x + 6) * eqn
  · change ((1:R)^2*x^2 - (1:R)^2*x + (1:R)^2 + (1:R) + x) ≠ 0
    intro h
    have ok : IsUnit (18:R) := unit_eq (((two).mul (three)).mul (three)) (by ring)
    apply ok.ne_zero
    linear_combination (1) * h + (x + 4) * eqn
  · change ((1:R)^2 + (1:R) + x) ≠ 0
    intro h
    have ok : IsUnit (6:R) := unit_eq ((two).mul (three)) (by ring)
    apply ok.ne_zero
    linear_combination (1) * h + (1) * eqn
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem cubic (x u : R) (rel : u^2+u+1=0)
    (ux : IsUnit x) (uu : IsUnit u) (reg : IsUnit (x-1)) (plus : IsUnit (x+1))
    (up : IsUnit (u+1)) (vplus : IsUnit (1+u^2*x)) (other : 1-u*x≠0)
    (i : Fin 7) : dot (weights x u) (obs i)≠0 := by
  rw [eval_obs]
  fin_cases i
  · change (-u^2*x^2 + u^2*x) ≠ 0
    intro h
    apply (one_ne_zero (α := R))
    apply ((ux.mul up).mul reg).mul_right_inj.mp
    linear_combination (1)*h+(x^2 - x)*rel
  · change (u^2*x^2 - u^2*x + u^2 + u + x^2) ≠ 0
    intro h
    apply other
    apply reg.mul_right_inj.mp
    linear_combination (1)*h+(-x^2 + x - 1)*rel
  · change (u^2 + u + x^2) ≠ 0
    intro h
    apply (one_ne_zero (α := R))
    apply (reg.mul plus).mul_right_inj.mp
    linear_combination (1)*h+(-1)*rel
  · change (-x^2 + x) ≠ 0
    intro h
    apply (one_ne_zero (α := R))
    apply (ux.mul reg).mul_right_inj.mp
    linear_combination (-1)*h+(0)*rel
  · change (-u^2*x^2 + u^2*x - x^2 + x) ≠ 0
    intro h
    apply (one_ne_zero (α := R))
    apply ((uu.mul ux).mul reg).mul_right_inj.mp
    linear_combination (1)*h+(x^2 - x)*rel
  · change (u^2*x^2 - u^2*x + u^2 + u + x) ≠ 0
    intro h
    apply (one_ne_zero (α := R))
    apply (reg.mul vplus).mul_right_inj.mp
    linear_combination (1)*h+(-1)*rel
  · change (u^2 + u + x) ≠ 0
    intro h
    apply (one_ne_zero (α := R))
    apply reg.mul_right_inj.mp
    linear_combination (1)*h+(-1)*rel
end MetabelianOrderThree.rowB

namespace MetabelianOrderThree.rowC
open MetabelianModule

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def table : Table 47 16 15 15 where
  side := AtlasIndices.shores16Indexed
  ht i := ⟨#[0,0,0,10,11,11,12,12,2,2,7,7,12,11,11,10,0,5,5,6,6,7,7,12,12,2,2,7,6,6,5,5,1,1,6,6,7,7,12,12,2,2,7,6,6,1,1][i.val]!, by decide +revert⟩
  lamp i j := ((#[#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,1,0,0,0,0,1,0,0,0,0,1,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,-1,0,1,0,0],#[0,0,0,0,0,0,0,0,0,0,-1,0,1,0,0],#[0,0,1,0,0,0,0,0,0,0,-1,0,1,0,0],#[0,0,1,0,0,0,0,0,0,0,-1,0,1,0,0],#[0,0,1,0,0,0,0,1,0,0,-1,0,1,0,0],#[0,0,1,0,0,0,0,1,0,0,-1,0,1,0,0],#[0,0,1,0,0,0,0,1,0,0,-1,0,1,0,0],#[0,0,1,0,0,0,0,1,0,0,-1,0,1,0,0],#[0,0,1,0,0,0,0,1,0,0,0,0,1,0,0],#[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[1,0,0,0,0,0,0,1,0,0,0,0,0,0,0],#[1,0,0,0,0,0,0,1,0,0,0,0,0,0,0],#[1,0,0,0,0,0,0,1,0,0,0,0,1,0,0],#[1,0,0,0,0,0,0,1,0,0,0,0,1,0,0],#[1,0,1,0,0,0,0,1,0,0,0,0,1,0,0],#[1,0,1,0,0,0,0,1,0,0,0,0,1,0,0],#[1,0,1,0,0,0,0,1,0,0,0,0,1,0,0],#[1,0,1,0,0,0,0,1,0,0,0,0,1,0,0],#[1,0,1,0,0,0,0,1,0,0,0,0,1,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,1,0,0,0,0,0,1,0,0,0,0,0,0,0],#[0,1,0,0,0,0,0,1,0,0,0,0,0,0,0],#[0,1,0,0,0,0,0,1,0,0,0,0,1,0,0],#[0,1,0,0,0,0,0,1,0,0,0,0,1,0,0],#[0,1,1,0,0,0,0,1,0,0,0,0,1,0,0],#[0,1,1,0,0,0,0,1,0,0,0,0,1,0,0],#[0,1,1,0,0,0,0,1,0,0,0,0,1,0,0],#[0,0,1,0,0,0,0,1,0,0,0,0,1,0,0],#[0,0,1,0,0,0,0,1,0,0,0,0,1,0,0]] : Array (Array ℤ))[i.val]!)[j.val]!
  route c t := if t=0 then 0 else if h : t<16 then ⟨2+c.val*15+(t-1),by have := c.isLt; omega⟩ else 1
  src := 0
  dst := 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def obs (i : Fin 8) (j : Fin 15) : ℤ := ((#[#[0,0,1,0,0,0,0,1,0,0,0,0,1,0,0],#[0,1,-1,0,0,0,0,0,0,0,1,0,-1,0,0],#[0,1,0,0,0,0,0,1,0,0,1,0,0,0,0],#[1,-1,-1,0,0,0,0,-1,0,0,0,0,-1,0,0],#[1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0],#[1,-1,1,0,0,0,0,1,0,0,0,0,1,0,0],#[1,0,-1,0,0,0,0,0,0,0,1,0,-1,0,0],#[1,0,0,0,0,0,0,1,0,0,1,0,0,0,0]] : Array (Array ℤ))[i.val]!)[j.val]!
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def gap (i j : Fin 15) : ℤ := if i=j then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem valid : Valid table 15 5 0 gap obs := by
  constructor <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem width : ∀ i,(table.ht i).val%5 < 3 := by decide +kernel
end MetabelianOrderThree.rowC

namespace MetabelianOrderThree.rowC
variable {R : Type*} [CommRing R]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
def vals (x u : R) (i : Fin 8) : R := (#[u^2*x^2 + u*x^2 + x^2,-u^2*x^2 + u^2 - x^2 + x,u^2 + u*x^2 + x,-u^2*x^2 - u*x^2 - x^2 - x + 1,1 - x,u^2*x^2 + u*x^2 + x^2 - x + 1,-u^2*x^2 + u^2 - x^2 + 1,u^2 + u*x^2 + 1] : Array R)[i.val]?.getD 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem eval_obs (x u : R) (i : Fin 8) : dot (weights x u) (obs i)=vals x u i := by
  fin_cases i
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(x^0*u^0)+(((0:ℤ):R)*(x^1*u^0)+(((1:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((0:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((1:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((0:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((1:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = u^2*x^2 + u*x^2 + x^2
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(x^0*u^0)+(((1:ℤ):R)*(x^1*u^0)+(((-1:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((0:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((1:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((-1:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = -u^2*x^2 + u^2 - x^2 + x
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(x^0*u^0)+(((1:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((0:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((1:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((1:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = u^2 + u*x^2 + x
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(x^0*u^0)+(((-1:ℤ):R)*(x^1*u^0)+(((-1:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((0:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((-1:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((0:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((-1:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = -u^2*x^2 - u*x^2 - x^2 - x + 1
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(x^0*u^0)+(((-1:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((0:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((0:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = 1 - x
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(x^0*u^0)+(((-1:ℤ):R)*(x^1*u^0)+(((1:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((0:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((1:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((0:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((1:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = u^2*x^2 + u*x^2 + x^2 - x + 1
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(x^0*u^0)+(((0:ℤ):R)*(x^1*u^0)+(((-1:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((0:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((0:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((1:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((-1:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = -u^2*x^2 + u^2 - x^2 + 1
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(x^0*u^0)+(((0:ℤ):R)*(x^1*u^0)+(((0:ℤ):R)*(x^2*u^0)+(((0:ℤ):R)*(x^3*u^0)+(((0:ℤ):R)*(x^4*u^0)+(((0:ℤ):R)*(x^0*u^1)+(((0:ℤ):R)*(x^1*u^1)+(((1:ℤ):R)*(x^2*u^1)+(((0:ℤ):R)*(x^3*u^1)+(((0:ℤ):R)*(x^4*u^1)+(((1:ℤ):R)*(x^0*u^2)+(((0:ℤ):R)*(x^1*u^2)+(((0:ℤ):R)*(x^2*u^2)+(((0:ℤ):R)*(x^3*u^2)+(((0:ℤ):R)*(x^4*u^2)+0))))))))))))))) = u^2 + u*x^2 + 1
    push_cast
    ring
end MetabelianOrderThree.rowC

namespace MetabelianOrderThree.rowC
open MetabelianModule
variable {R : Type*} [CommRing R] [Nontrivial R]
omit [Nontrivial R] in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
private theorem unit_eq {a b : R} (h : IsUnit a) (eq : a=b) : IsUnit b := eq ▸ h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem atMinusTwo (x : R) (two : IsUnit (2:R)) (three : IsUnit (3:R)) (five : IsUnit (5:R)) (eqn : x + 2=0) (i : Fin 8) :
    dot (weights x 1) (obs i)≠0 := by
  rw [eval_obs]
  fin_cases i
  · change ((1:R)^2*x^2 + (1:R)*x^2 + x^2) ≠ 0
    intro h
    have ok : IsUnit (12:R) := unit_eq (((two).mul (two)).mul (three)) (by ring)
    apply ok.ne_zero
    linear_combination (1) * h + (6 - 3*x) * eqn
  · change (-(1:R)^2*x^2 + (1:R)^2 - x^2 + x) ≠ 0
    intro h
    have ok : IsUnit (9:R) := unit_eq ((three).mul (three)) (by ring)
    apply ok.ne_zero
    linear_combination (-1) * h + (5 - 2*x) * eqn
  · change ((1:R)^2 + (1:R)*x^2 + x) ≠ 0
    intro h
    have ok : IsUnit (3:R) := unit_eq (three) (by ring)
    apply ok.ne_zero
    linear_combination (1) * h + (1 - x) * eqn
  · change (-(1:R)^2*x^2 - (1:R)*x^2 - x^2 - x + 1) ≠ 0
    intro h
    have ok : IsUnit (9:R) := unit_eq ((three).mul (three)) (by ring)
    apply ok.ne_zero
    linear_combination (-1) * h + (5 - 3*x) * eqn
  · change (1 - x) ≠ 0
    intro h
    have ok : IsUnit (3:R) := unit_eq (three) (by ring)
    apply ok.ne_zero
    linear_combination (1) * h + (1) * eqn
  · change ((1:R)^2*x^2 + (1:R)*x^2 + x^2 - x + 1) ≠ 0
    intro h
    have ok : IsUnit (15:R) := unit_eq ((three).mul (five)) (by ring)
    apply ok.ne_zero
    linear_combination (1) * h + (7 - 3*x) * eqn
  · change (-(1:R)^2*x^2 + (1:R)^2 - x^2 + 1) ≠ 0
    intro h
    have ok : IsUnit (6:R) := unit_eq ((two).mul (three)) (by ring)
    apply ok.ne_zero
    linear_combination (-1) * h + (4 - 2*x) * eqn
  · change ((1:R)^2 + (1:R)*x^2 + 1) ≠ 0
    intro h
    have ok : IsUnit (6:R) := unit_eq ((two).mul (three)) (by ring)
    apply ok.ne_zero
    linear_combination (1) * h + (2 - x) * eqn
end MetabelianOrderThree.rowC

namespace MetabelianOrderThree.rowD
open MetabelianModule

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def table : Table 47 16 15 2 where
  side := AtlasIndices.shores16Indexed
  ht i := ⟨#[2,0,2,12,12,7,8,8,13,12,2,1,1,11,11,10,0,7,6,6,5,5,0,1,11,11,10,10,5,6,1,1,3,3,8,8,13,12,12,7,7,2,2,1,6,5,5][i.val]!, by decide +revert⟩
  lamp i j := ((#[#[0,0],#[0,0],#[0,0],#[-1,0],#[-1,0],#[-1,-1],#[-1,-1],#[-1,-1],#[-2,-2],#[-2,-2],#[-1,-2],#[-1,-2],#[-1,-2],#[0,-1],#[0,-1],#[0,-1],#[0,0],#[-1,-1],#[-1,-1],#[-1,-1],#[-1,-1],#[-1,-1],#[-2,-1],#[-2,-1],#[-1,0],#[-1,0],#[-1,0],#[-1,0],#[0,1],#[0,1],#[0,0],#[0,0],#[0,0],#[0,0],#[1,0],#[1,0],#[0,-1],#[0,-1],#[0,-1],#[0,-2],#[0,-2],#[1,-1],#[1,-1],#[1,-1],#[1,0],#[1,0],#[1,0]] : Array (Array ℤ))[i.val]!)[j.val]!
  route c t := if t=0 then 0 else if h : t<16 then ⟨2+c.val*15+(t-1),by have := c.isLt; omega⟩ else 1
  src := 0
  dst := 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def obs (i : Fin 3) (j : Fin 2) : ℤ := ((#[#[1,-1],#[1,2],#[2,1]] : Array (Array ℤ))[i.val]!)[j.val]!
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def gap (i : Fin 15) (j : Fin 2) : ℤ := ((#[#[1,0],#[0,1],#[-1,-1],#[1,0],#[0,1],#[-1,-1],#[1,0],#[0,1],#[-1,-1],#[1,0],#[0,1],#[-1,-1],#[1,0],#[0,1],#[-1,-1]] : Array (Array ℤ))[i.val]!)[j.val]!

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem valid : Valid table 15 5 0 gap obs := by
  constructor <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem width : ∀ i,(table.ht i).val%5 < 4 := by decide +kernel
end MetabelianOrderThree.rowD

namespace MetabelianOrderThree.rowD
variable {R : Type*} [CommRing R]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
def ew (x : R) : Fin 2 → R := ![1,x]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
def vals (x : R) (i : Fin 3) : R := (#[1 - x,2*x + 1,x + 2] : Array R)[i.val]?.getD 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem eval_obs (x : R) (i : Fin 3) : dot (ew x) (obs i)=vals x i := by
  fin_cases i
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(1:R)+(((-1:ℤ):R)*x+0)) = 1 - x
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(1:R)+(((2:ℤ):R)*x+0)) = 2*x + 1
    push_cast
    ring
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((2:ℤ):R)*(1:R)+(((1:ℤ):R)*x+0)) = x + 2
    push_cast
    ring
end MetabelianOrderThree.rowD

namespace MetabelianOrderThree.rowD
open MetabelianModule
variable {R : Type*} [CommRing R]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem cubic (x : R) (cycl : x^2+x+1=0) (three : (3:R)≠0) (i : Fin 3) :
    dot (ew x) (obs i)≠0 := by
  rw [eval_obs]
  fin_cases i
  · change (1 - x) ≠ 0
    intro h
    apply three
    linear_combination (x + 2)*h+(1)*cycl
  · change (2*x + 1) ≠ 0
    intro h
    apply three
    linear_combination (-2*x - 1)*h+(4)*cycl
  · change (x + 2) ≠ 0
    intro h
    apply three
    linear_combination (1 - x)*h+(1)*cycl
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem gap_value (x : R) (cycl : x^2+x+1=0) (v : Fin 15) :
    dot (ew x) (gap v) = x^(v.val%5)*(x^2)^(v.val/5) := by
  fin_cases v
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(1:R)+(((0:ℤ):R)*x+0)) = x^0*(x^2)^0
    push_cast
    linear_combination (0)*cycl
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(1:R)+(((1:ℤ):R)*x+0)) = x^1*(x^2)^0
    push_cast
    linear_combination (0)*cycl
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((-1:ℤ):R)*(1:R)+(((-1:ℤ):R)*x+0)) = x^2*(x^2)^0
    push_cast
    linear_combination (-1)*cycl
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(1:R)+(((0:ℤ):R)*x+0)) = x^3*(x^2)^0
    push_cast
    linear_combination (1 - x)*cycl
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(1:R)+(((1:ℤ):R)*x+0)) = x^4*(x^2)^0
    push_cast
    linear_combination (-x^2 + x)*cycl
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((-1:ℤ):R)*(1:R)+(((-1:ℤ):R)*x+0)) = x^0*(x^2)^1
    push_cast
    linear_combination (-1)*cycl
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(1:R)+(((0:ℤ):R)*x+0)) = x^1*(x^2)^1
    push_cast
    linear_combination (1 - x)*cycl
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(1:R)+(((1:ℤ):R)*x+0)) = x^2*(x^2)^1
    push_cast
    linear_combination (-x^2 + x)*cycl
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((-1:ℤ):R)*(1:R)+(((-1:ℤ):R)*x+0)) = x^3*(x^2)^1
    push_cast
    linear_combination (-x^3 + x^2 - 1)*cycl
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(1:R)+(((0:ℤ):R)*x+0)) = x^4*(x^2)^1
    push_cast
    linear_combination (-x^4 + x^3 - x + 1)*cycl
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(1:R)+(((1:ℤ):R)*x+0)) = x^0*(x^2)^2
    push_cast
    linear_combination (-x^2 + x)*cycl
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((-1:ℤ):R)*(1:R)+(((-1:ℤ):R)*x+0)) = x^1*(x^2)^2
    push_cast
    linear_combination (-x^3 + x^2 - 1)*cycl
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((1:ℤ):R)*(1:R)+(((0:ℤ):R)*x+0)) = x^2*(x^2)^2
    push_cast
    linear_combination (-x^4 + x^3 - x + 1)*cycl
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((0:ℤ):R)*(1:R)+(((1:ℤ):R)*x+0)) = x^3*(x^2)^2
    push_cast
    linear_combination (-x^5 + x^4 - x^2 + x)*cycl
  · simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (((-1:ℤ):R)*(1:R)+(((-1:ℤ):R)*x+0)) = x^4*(x^2)^2
    push_cast
    linear_combination (-x^6 + x^5 - x^3 + x^2 - 1)*cycl
end MetabelianOrderThree.rowD

/- Arithmetic progression. Check the wide routes and the exceptional short periods. -/
namespace MetabelianProgression.wideA
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 47 16 7 7 where
  side := AtlasIndices.shores16
  ht := ![3,3,3,2,2,1,1,0,2,2,3,3,5,4,6,5,5,4,4,6,5,5,4,4,2,2,1,1,0,2,2,4,5,4,6,5,5,3,3,2,2,1,1,0,2,2,3]
  lamp := ![![0,0,0,0,0,0,0],![1,0,0,0,1,0,0],![0,0,0,0,0,0,0],![0,0,0,0,0,0,0],![0,0,0,0,0,0,0],![0,0,0,0,0,0,0],![0,0,0,0,0,0,0],![0,0,0,0,0,0,0],![1,0,0,0,0,0,0],![1,0,0,0,0,0,0],![1,0,0,0,0,0,0],![1,0,0,0,0,0,0],![1,0,0,1,0,0,0],![1,0,0,1,0,0,0],![1,0,0,1,1,0,0],![1,0,0,1,1,0,0],![1,0,0,1,1,0,0],![0,0,0,0,0,0,0],![0,0,0,0,0,0,0],![0,0,0,0,1,0,0],![0,0,0,0,1,0,0],![0,0,0,0,1,0,0],![0,0,0,0,1,0,0],![0,0,0,0,1,0,0],![0,0,-1,0,1,0,0],![0,0,-1,0,1,0,0],![0,0,-1,0,1,0,0],![0,0,-1,0,1,0,0],![0,0,-1,0,1,0,0],![1,0,-1,0,1,0,0],![1,0,-1,0,1,0,0],![1,0,0,0,1,0,0],![0,0,0,1,0,0,0],![0,0,0,1,0,0,0],![0,0,0,1,1,0,0],![0,0,0,1,1,0,0],![0,0,0,1,1,0,0],![0,0,0,0,1,0,0],![0,0,0,0,1,0,0],![0,0,0,0,1,0,0],![0,0,0,0,1,0,0],![0,0,0,0,1,0,0],![0,0,0,0,1,0,0],![0,0,0,0,1,0,0],![1,0,0,0,1,0,0],![1,0,0,0,1,0,0],![1,0,0,0,1,0,0]]
  route := AtlasIndices.route16
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 7 → Fin 7 → ℤ := ![![1,0,0,0,0,0,0],![0,1,0,0,0,0,0],![0,0,1,0,0,0,0],![0,0,0,1,0,0,0],![0,0,0,0,1,0,0],![0,0,0,0,0,1,0],![0,0,0,0,0,0,1]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obstacles : Fin 14 → Fin 7 → ℤ := ![![0,0,0,0,1,0,0],![0,0,0,1,-1,0,0],![0,0,0,1,0,0,0],![0,0,1,0,-1,0,0],![0,0,1,0,0,0,0],![1,0,-1,0,0,0,0],![1,0,-1,0,1,0,0],![1,0,0,0,-1,0,0],![1,0,0,0,0,0,0],![1,0,0,0,1,0,0],![1,0,0,1,-1,0,0],![1,0,0,1,0,0,0],![1,0,1,0,-1,0,0],![1,0,1,0,0,0,0]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem checked : Valid tbl 0 2 0 gaps obstacles := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] [Nontrivial R] {x : R}

omit [Nontrivial R] in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval  : ∀ j,evalVec x (gaps j)=x^j.val := by
  intro j
  fin_cases j
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=x^0
    push_cast; ring
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=x^1
    push_cast; ring
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=x^2
    push_cast; ring
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=x^3
    push_cast; ring
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=x^4
    push_cast; ring
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=x^5
    push_cast; ring
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R))))))))=x^6
    push_cast; ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem obstacles_ne (m : ℕ) (odd : Odd m) (period : x^m=1) (two : IsUnit (2:R)) (reg : IsUnit (x-1)) (no1 : -x^4+x^2+1≠0) (no2 : -x^4+x^3+1≠0) : ∀ i,evalVec x (obstacles i)≠0 := by
  have ux := unit_period odd period
  have un (k : ℕ) := unit_sum_pow odd period two k
  intro i h
  fin_cases i
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (1:R)≠0 := by
      convert (isUnit_one (M := R)).ne_zero using 1
    apply n
    apply (ux.pow 4).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (-x+1:R)≠0 := by
      convert reg.neg.ne_zero using 1; ring
    apply n
    apply (ux.pow 3).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (1:R)≠0 := by
      convert (isUnit_one (M := R)).ne_zero using 1
    apply n
    apply (ux.pow 3).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (-x^2+1:R)≠0 := by
      convert (unit_diff2 odd period two reg).ne_zero using 1; ring
    apply n
    apply (ux.pow 2).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (1:R)≠0 := by
      convert (isUnit_one (M := R)).ne_zero using 1
    apply n
    apply (ux.pow 2).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (-x^2+1:R)≠0 := by
      convert (unit_diff2 odd period two reg).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (x^4-x^2+1:R)≠0 := by
      convert (unit_cyclo12 odd period two).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (-x^4+1:R)≠0 := by
      convert (unit_diff4 odd period two reg).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (1:R)≠0 := by
      convert (isUnit_one (M := R)).ne_zero using 1
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (x^4+1:R)≠0 := by
      convert (un 4).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (-x^4+x^3+1:R)≠0 := no2
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (x^3+1:R)≠0 := by
      convert (un 3).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (-x^4+x^2+1:R)≠0 := no1
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (x^2+1:R)≠0 := by
      convert (un 2).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h

end MetabelianProgression.wideA

namespace MetabelianProgression.wideB
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 47 16 7 7 where
  side := AtlasIndices.shores16
  ht := ![2,2,2,1,1,0,2,2,4,3,5,4,6,5,5,3,4,3,1,1,0,2,1,3,3,5,4,6,5,5,3,3,4,3,5,4,6,5,5,3,4,2,2,1,1,0,2]
  lamp := ![![0,0,0,0,0,0,0],![1,0,0,0,1,0,0],![0,0,0,0,0,0,0],![0,0,0,0,0,0,0],![0,0,0,0,0,0,0],![0,0,0,0,0,0,0],![1,0,0,0,0,0,0],![1,0,0,0,0,0,0],![1,0,1,0,0,0,0],![1,0,1,0,0,0,0],![1,0,1,1,0,0,0],![1,0,1,1,0,0,0],![1,0,1,1,1,0,0],![1,0,1,1,1,0,0],![1,0,1,1,1,0,0],![1,0,1,0,1,0,0],![1,0,1,0,1,0,0],![0,0,0,0,0,0,0],![0,-1,0,0,0,0,0],![0,-1,0,0,0,0,0],![0,-1,0,0,0,0,0],![1,-1,0,0,0,0,0],![1,-1,0,0,0,0,0],![1,0,0,0,0,0,0],![1,0,0,0,0,0,0],![1,0,0,1,0,0,0],![1,0,0,1,0,0,0],![1,0,0,1,1,0,0],![1,0,0,1,1,0,0],![1,0,0,1,1,0,0],![1,0,0,0,1,0,0],![1,0,0,0,1,0,0],![0,0,1,0,0,0,0],![0,0,1,0,0,0,0],![0,0,1,1,0,0,0],![0,0,1,1,0,0,0],![0,0,1,1,1,0,0],![0,0,1,1,1,0,0],![0,0,1,1,1,0,0],![0,0,1,0,1,0,0],![0,0,1,0,1,0,0],![0,0,0,0,1,0,0],![0,0,0,0,1,0,0],![0,0,0,0,1,0,0],![0,0,0,0,1,0,0],![0,0,0,0,1,0,0],![1,0,0,0,1,0,0]]
  route := AtlasIndices.route16
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 7 → Fin 7 → ℤ := ![![1,0,0,0,0,0,0],![0,1,0,0,0,0,0],![0,0,1,0,0,0,0],![0,0,0,1,0,0,0],![0,0,0,0,1,0,0],![0,0,0,0,0,1,0],![0,0,0,0,0,0,1]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obstacles : Fin 14 → Fin 7 → ℤ := ![![0,0,0,0,1,0,0],![0,0,1,0,-1,0,0],![0,0,1,0,0,0,0],![0,0,1,0,1,0,0],![0,1,0,0,0,0,0],![0,1,0,0,1,0,0],![1,-1,0,0,-1,0,0],![1,-1,0,0,0,0,0],![1,0,-1,0,-1,0,0],![1,0,-1,0,0,0,0],![1,0,-1,0,1,0,0],![1,0,0,0,-1,0,0],![1,0,0,0,0,0,0],![1,0,0,0,1,0,0]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem checked : Valid tbl 0 2 0 gaps obstacles := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] [Nontrivial R] {x : R}

omit [Nontrivial R] in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval  : ∀ j,evalVec x (gaps j)=x^j.val := by
  intro j
  fin_cases j
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=x^0
    push_cast; ring
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=x^1
    push_cast; ring
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=x^2
    push_cast; ring
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=x^3
    push_cast; ring
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=x^4
    push_cast; ring
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=x^5
    push_cast; ring
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R))))))))=x^6
    push_cast; ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem obstacles_ne (m : ℕ) (odd : Odd m) (period : x^m=1) (two : IsUnit (2:R)) (reg : IsUnit (x-1)) (no1 : -x^4-x+1≠0) (no2 : -x^4-x^2+1≠0) : ∀ i,evalVec x (obstacles i)≠0 := by
  have ux := unit_period odd period
  have un (k : ℕ) := unit_sum_pow odd period two k
  intro i h
  fin_cases i
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (1:R)≠0 := by
      convert (isUnit_one (M := R)).ne_zero using 1
    apply n
    apply (ux.pow 4).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (-x^2+1:R)≠0 := by
      convert (unit_diff2 odd period two reg).ne_zero using 1; ring
    apply n
    apply (ux.pow 2).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (1:R)≠0 := by
      convert (isUnit_one (M := R)).ne_zero using 1
    apply n
    apply (ux.pow 2).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (x^2+1:R)≠0 := by
      convert (un 2).ne_zero using 1; ring
    apply n
    apply (ux.pow 2).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (1:R)≠0 := by
      convert (isUnit_one (M := R)).ne_zero using 1
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (x^3+1:R)≠0 := by
      convert (un 3).ne_zero using 1; ring
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (-x^4-x+1:R)≠0 := no1
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (-x+1:R)≠0 := by
      convert reg.neg.ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (-x^4-x^2+1:R)≠0 := no2
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (-x^2+1:R)≠0 := by
      convert (unit_diff2 odd period two reg).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (x^4-x^2+1:R)≠0 := by
      convert (unit_cyclo12 odd period two).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (-x^4+1:R)≠0 := by
      convert (unit_diff4 odd period two reg).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (1:R)≠0 := by
      convert (isUnit_one (M := R)).ne_zero using 1
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))))))=0 at h
    push_cast at h
    have n : (x^4+1:R)≠0 := by
      convert (un 4).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h

end MetabelianProgression.wideB

namespace MetabelianProgression.three
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 47 16 3 2 where
  side := AtlasIndices.shores16
  ht := ![0,2,0,2,1,0,2,2,0,1,1,2,0,0,2,1,0,1,1,0,0,2,1,1,2,0,1,1,0,0,1,2,2,1,0,0,2,2,1,0,0,2,1,0,2,1,1]
  lamp := ![![0,0],![2,0],![0,0],![0,0],![-1,-1],![-1,-1],![0,-1],![0,-1],![0,-1],![0,-2],![0,-2],![1,-1],![1,-1],![1,-1],![2,-1],![2,-1],![2,0],![0,0],![0,0],![0,1],![0,1],![1,1],![1,1],![1,1],![2,2],![2,2],![2,1],![2,1],![2,1],![2,1],![2,0],![2,0],![1,0],![1,0],![1,1],![1,1],![2,1],![2,1],![1,0],![1,0],![1,0],![1,0],![0,-1],![0,-1],![1,-1],![1,-1],![1,-1]]
  route := AtlasIndices.route16
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 3 → Fin 2 → ℤ := ![![1,0],![0,1],![-1,-1]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obstacles : Fin 14 → Fin 2 → ℤ := ![![0,1],![0,2],![1,-2],![1,-1],![1,0],![1,1],![1,2],![1,3],![2,-1],![2,0],![2,1],![2,2],![2,3],![3,2]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem checked : Valid tbl 3 2 0 gaps obstacles := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] [Nontrivial R] {x : R}

omit [Nontrivial R] in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (cyclo : x^2+x+1=0) : ∀ j,evalVec x (gaps j)=x^j.val := by
  intro j
  fin_cases j
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))=x^0
    push_cast; ring
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))=x^1
    push_cast; ring
  · change (((-1:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R)))=x^2
    push_cast; linear_combination -cyclo

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem obstacles_ne (cyclo : x^2+x+1=0) (two : IsUnit (2:R)) (reg : IsUnit (x-1)) (no7 : ¬ ((7:R)=0 ∧ (x=2 ∨ x=4))) : ∀ i,evalVec x (obstacles i)≠0 := by
  intro i h
  fin_cases i
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (-x-1) * h + (1) * cyclo
  · change (((0:ℤ):R)+x*(((2:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply two.ne_zero
    linear_combination (-x-1) * h + (2) * cyclo
  · change (((1:ℤ):R)+x*(((-2:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply no7
    refine ⟨?_,Or.inr ?_⟩
    · linear_combination (2*x+3) * h + (4) * cyclo
    · linear_combination (-x-2) * h + (-2) * cyclo
  · change (((1:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply reg.ne_zero
    linear_combination (-1) * h + (0) * cyclo
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1) * h + (0) * cyclo
  · change (((1:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (-x) * h + (1) * cyclo
  · change (((1:ℤ):R)+x*(((2:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply reg.ne_zero
    linear_combination (x+1) * h + (-2) * cyclo
  · change (((1:ℤ):R)+x*(((3:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply no7
    refine ⟨?_,Or.inl ?_⟩
    · linear_combination (-3*x-2) * h + (9) * cyclo
    · linear_combination (x+1) * h + (-3) * cyclo
  · change (((2:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply no7
    refine ⟨?_,Or.inl ?_⟩
    · linear_combination (x+3) * h + (1) * cyclo
    · linear_combination (-1) * h + (0) * cyclo
  · change (((2:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply two.ne_zero
    linear_combination (1) * h + (0) * cyclo
  · change (((2:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply reg.ne_zero
    linear_combination (x) * h + (-1) * cyclo
  · change (((2:ℤ):R)+x*(((2:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply two.ne_zero
    linear_combination (-x) * h + (2) * cyclo
  · change (((2:ℤ):R)+x*(((3:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply no7
    refine ⟨?_,Or.inr ?_⟩
    · linear_combination (-3*x-1) * h + (9) * cyclo
    · linear_combination (2*x+1) * h + (-6) * cyclo
  · change (((3:ℤ):R)+x*(((2:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply no7
    refine ⟨?_,Or.inl ?_⟩
    · linear_combination (-2*x+1) * h + (4) * cyclo
    · linear_combination (x) * h + (-2) * cyclo

end MetabelianProgression.three

namespace MetabelianProgression.five
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 47 16 5 4 where
  side := AtlasIndices.shores16
  ht := ![0,1,0,4,4,3,0,0,1,1,3,2,4,4,0,0,2,1,1,3,3,4,4,0,0,2,2,4,3,0,0,1,2,1,1,4,4,2,2,0,1,1,3,2,4,3,3]
  lamp := ![![0,0,0,0],![1,1,1,1],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,1],![0,0,0,1],![0,0,0,1],![0,0,0,1],![0,1,0,1],![0,1,0,1],![0,1,1,1],![0,1,1,1],![0,1,1,1],![0,1,1,1],![1,1,1,1],![0,0,0,0],![0,0,0,0],![0,1,0,0],![0,1,0,0],![0,1,0,0],![0,1,0,0],![0,1,0,0],![0,1,0,0],![1,1,0,0],![1,1,0,0],![1,1,1,0],![1,1,1,0],![1,1,1,1],![1,1,1,1],![1,1,1,1],![1,0,0,0],![1,0,0,0],![1,0,0,0],![2,1,1,1],![2,1,1,1],![2,1,0,1],![2,1,0,1],![1,1,0,1],![1,1,0,1],![1,1,0,1],![1,2,0,1],![1,2,0,1],![1,2,1,1],![1,2,1,1],![1,2,1,1]]
  route := AtlasIndices.route16
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 5 → Fin 4 → ℤ := ![![1,0,0,0],![0,1,0,0],![0,0,1,0],![0,0,0,1],![-1,-1,-1,-1]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obstacles : Fin 23 → Fin 4 → ℤ := ![![0,0,0,1],![0,0,1,0],![0,0,1,1],![0,1,0,-1],![0,1,0,0],![0,1,0,1],![0,1,1,0],![0,1,1,1],![1,-1,0,0],![1,0,-1,0],![1,0,0,-1],![1,0,0,0],![1,0,0,1],![1,0,1,0],![1,0,1,1],![1,1,0,0],![1,1,0,1],![1,1,1,0],![1,1,1,1],![1,2,1,1],![2,0,0,0],![2,0,1,1],![2,1,1,1]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem checked : Valid tbl 5 2 0 gaps obstacles := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] [Nontrivial R] {x : R}

omit [Nontrivial R] in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (cyclo : x^4+x^3+x^2+x+1=0) : ∀ j,evalVec x (gaps j)=x^j.val := by
  intro j
  fin_cases j
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=x^0
    push_cast; ring
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=x^1
    push_cast; ring
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=x^2
    push_cast; ring
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))))=x^3
    push_cast; ring
  · change (((-1:ℤ):R)+x*(((-1:ℤ):R)+x*(((-1:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R)))))=x^4
    push_cast; linear_combination -cyclo

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem obstacles_ne (cyclo : x^4+x^3+x^2+x+1=0) (two : IsUnit (2:R)) (reg : IsUnit (x-1)) : ∀ i,evalVec x (obstacles i)≠0 := by
  intro i h
  fin_cases i
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (x^2) * h + (-x+1) * cyclo
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (x^3) * h + (-x+1) * cyclo
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (x^3+x^2+1) * h + (-x^2-x+1) * cyclo
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply reg.ne_zero
    linear_combination (x^2+1) * h + (x-1) * cyclo
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (-x^3-x^2-x-1) * h + (1) * cyclo
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (-x-1) * h + (1) * cyclo
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (-x^2-1) * h + (1) * cyclo
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (-x^3-x-1) * h + (x^2+1) * cyclo
  · change (((1:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply reg.ne_zero
    linear_combination (-1) * h + (0) * cyclo
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply reg.ne_zero
    linear_combination (x^3+x) * h + (x-1) * cyclo
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply reg.ne_zero
    linear_combination (-x^3-1) * h + (-x^2+x) * cyclo
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1) * h + (0) * cyclo
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (x^2+x+1) * h + (-x) * cyclo
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (-x^2-x) * h + (1) * cyclo
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (x^3+x^2) * h + (-x^2-x+1) * cyclo
  · change (((1:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (-x^3-x) * h + (1) * cyclo
  · change (((1:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (-x^3-x^2-x) * h + (x^2+1) * cyclo
  · change (((1:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (x^3+1) * h + (-x) * cyclo
  · change (((1:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (-x) * h + (1) * cyclo
  · change (((1:ℤ):R)+x*(((2:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply reg.ne_zero
    linear_combination (x^3+x+1) * h + (-x^2-2) * cyclo
  · change (((2:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply two.ne_zero
    linear_combination (1) * h + (0) * cyclo
  · change (((2:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (-x^3-x^2+1) * h + (x^2+x-1) * cyclo
  · change (((2:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    apply reg.ne_zero
    linear_combination (x) * h + (-1) * cyclo

end MetabelianProgression.five

namespace MetabelianProgression.sevenT2
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 3 1 where
  side := AtlasIndices.shores8
  ht := ![0,1,0,1,2,2,1,0,2,1,1,2,0,0,2,1,2,2,0,1,2,0,0]
  lamp := ![![0],![3],![0],![5],![5],![5],![2],![2],![3],![0],![0],![0],![6],![6],![6],![3],![1],![1],![1],![6],![6],![5],![5]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 3 → Fin 1 → ℤ := ![![1],![2],![4]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obstacles : Fin 6 → Fin 1 → ℤ := ![![1],![2],![3],![4],![5],![6]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem checked : Valid tbl 3 2 7 gaps obstacles := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] [Nontrivial R] {x : R}

omit [Nontrivial R] in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=2) (seven : (7:R)=0) : ∀ j,evalVec x (gaps j)=x^j.val := by
  intro j
  fin_cases j
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R) * seven
  · change (((2:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R) * seven
  · change (((4:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (0:R) * seven

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem obstacles_ne (_hx : x=2) (seven : (7:R)=0) : ∀ i,evalVec x (obstacles i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h + (0:R)*seven
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h + (-1:R)*seven
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h + (-2:R)*seven
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (2:R)*h + (-1:R)*seven
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (3:R)*h + (-2:R)*seven
  · change (((6:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h + (-5:R)*seven

end MetabelianProgression.sevenT2

namespace MetabelianProgression.sevenT4
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 3 1 where
  side := AtlasIndices.shores8
  ht := ![0,1,0,1,1,0,0,2,1,1,1,2,2,1,0,0,2,2,0,1,1,0,2]
  lamp := ![![0],![5],![0],![3],![3],![3],![3],![3],![5],![0],![0],![0],![0],![2],![2],![2],![1],![1],![1],![4],![4],![4],![5]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 3 → Fin 1 → ℤ := ![![1],![4],![2]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obstacles : Fin 5 → Fin 1 → ℤ := ![![1],![2],![3],![4],![5]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem checked : Valid tbl 3 2 7 gaps obstacles := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] [Nontrivial R] {x : R}

omit [Nontrivial R] in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=4) (seven : (7:R)=0) : ∀ j,evalVec x (gaps j)=x^j.val := by
  intro j
  fin_cases j
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R) * seven
  · change (((4:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R) * seven
  · change (((2:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (-2:R) * seven

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem obstacles_ne (_hx : x=4) (seven : (7:R)=0) : ∀ i,evalVec x (obstacles i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h + (0:R)*seven
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h + (-1:R)*seven
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h + (-2:R)*seven
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (2:R)*h + (-1:R)*seven
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (3:R)*h + (-2:R)*seven

end MetabelianProgression.sevenT4

namespace MetabelianProgression
open MetabelianModule EqualArms MetabelianRegular
variable {R V : Type*} [CommRing R] [Nontrivial R] {x : R} {B : SimpleGraph V}

theorem large {m : ℕ} (C : Chart B m 2 x) (hm : 7 ≤ m) (odd : Odd m)
    (period : x^m=1) (two : IsUnit (2:R)) (reg : IsUnit (x-1)) : Nonempty (Theta B 16) := by
  by_cases a : -x^4+x^2+1 ≠ 0 ∧ -x^4+x^3+1 ≠ 0
  · exact tableTheta C wideA.tbl wideA.gaps wideA.obstacles wideA.checked hm (Or.inl rfl)
      (by simp) wideA.gaps_eval (wideA.obstacles_ne m odd period two reg a.1 a.2)
  have ux := unit_period odd period
  have u1 : IsUnit (1+x) := by simpa only [pow_one] using unit_sum_pow odd period two 1
  have u2 := unit_sum_pow odd period two 2
  push Not at a
  have b1 : -x^4-x+1 ≠ 0 := by
    intro h
    by_cases h₁ : -x^4+x^2+1 = 0
    · apply (ux.mul u1).ne_zero
      linear_combination h₁-h
    · apply (ux.mul u2).ne_zero
      linear_combination a h₁-h
  have b2 : -x^4-x^2+1 ≠ 0 := by
    intro h
    by_cases h₁ : -x^4+x^2+1 = 0
    · apply (two.mul (ux.pow 2)).ne_zero
      linear_combination h₁-h
    · apply ((ux.pow 2).mul u1).ne_zero
      linear_combination a h₁-h
  exact tableTheta C wideB.tbl wideB.gaps wideB.obstacles wideB.checked hm (Or.inl rfl)
    (by simp) wideB.gaps_eval (wideB.obstacles_ne m odd period two reg b1 b2)

theorem indexFive (C : Chart B 5 2 x) (period : x^5=1)
    (two : IsUnit (2:R)) (reg : IsUnit (x-1)) : Nonempty (Theta B 16) := by
  have cyc : x^4+x^3+x^2+x+1=0 := reg.mul_right_eq_zero.mp (by linear_combination period)
  exact tableTheta C five.tbl five.gaps five.obstacles five.checked le_rfl (Or.inr rfl)
    (by simp) (five.gaps_eval cyc) (five.obstacles_ne cyc two reg)

theorem indexThree (C : Chart B 3 2 x) (period : x^3=1)
    (two : IsUnit (2:R)) (reg : IsUnit (x-1)) :
    Nonempty (Theta B 16) ∨ Nonempty (Theta B 8) := by
  by_cases small : (7:R)=0 ∧ (x=2 ∨ x=4)
  · right
    obtain ⟨seven,h|h⟩ := small
    · exact tableTheta C sevenT2.tbl sevenT2.gaps sevenT2.obstacles sevenT2.checked le_rfl
        (Or.inr rfl) (by simpa using seven) (sevenT2.gaps_eval h seven) (sevenT2.obstacles_ne h seven)
    · exact tableTheta C sevenT4.tbl sevenT4.gaps sevenT4.obstacles sevenT4.checked le_rfl
        (Or.inr rfl) (by simpa using seven) (sevenT4.gaps_eval h seven) (sevenT4.obstacles_ne h seven)
  · left
    have cyc : x^2+x+1=0 := reg.mul_right_eq_zero.mp (by linear_combination period)
    exact tableTheta C three.tbl three.gaps three.obstacles three.checked le_rfl (Or.inr rfl)
      (by simp) (three.gaps_eval cyc) (three.obstacles_ne cyc two reg small)

theorem chart {m : ℕ} (C : Chart B m 2 x) (hm : 3 ≤ m) (odd : Odd m)
    (period : x^m=1) (two : IsUnit (2:R)) (reg : IsUnit (x-1)) :
    Nonempty (Theta B 16) ∨ Nonempty (Theta B 8) := by
  have cases : m=3 ∨ m=5 ∨ 7 ≤ m := by obtain ⟨e,h⟩ := odd; omega
  rcases cases with rfl|rfl|h
  · exact indexThree C period two reg
  · exact Or.inl (indexFive C period two reg)
  · exact Or.inl (large C h odd period two reg)

end MetabelianProgression

namespace MetabelianOrderThree
open EqualArms MetabelianModule
variable {R V : Type*} [CommRing R] [Nontrivial R] {B : SimpleGraph V}

private theorem one_fixed {m : ℕ} (x : R) (om : Odd m) (period : x^m=1)
    (reg : IsUnit (x-1)) (two : IsUnit (2:R)) :
    (∀ i,dot (weights x 1) (rowA.obs i)≠0) ∨
    (∀ i,dot (weights x 1) (rowB.obs i)≠0) ∨
    (∀ i,dot (weights x 1) (rowC.obs i)≠0) := by
  have ux := unit_period om period
  have plus : IsUnit (x+1) := by simpa [add_comm] using unit_sum_pow om period two 1
  by_cases h3 : (3:R)=0
  · exact .inr (.inl (rowB.charThree x ux reg plus two h3))
  by_cases hm : x+2=0
  · have three : IsUnit (3:R) := by convert reg.neg using 1; linear_combination hm
    have five : IsUnit (5:R) := by
      convert unit_sum_pow om period two 2 using 1
      linear_combination (2-x)*hm
    exact .inr (.inr (rowC.atMinusTwo x two three five hm))
  by_cases hh : 2*x+1=0
  · have three : IsUnit (3:R) := by convert (two.mul reg).neg using 1; linear_combination hh
    exact .inr (.inl (rowB.minusHalf x two three hh))
  by_cases four : 4-x=0
  · have three : IsUnit (3:R) := by convert reg using 1; linear_combination four
    have five : IsUnit (5:R) := by convert plus using 1; linear_combination four
    exact .inr (.inl (rowB.atFour x two three five four))
  exact .inl (rowA.fixed x ux reg plus two h3 hm hh four)

theorem large {d : ℕ} {x : R} (rev : Bool) (C : Chart B (3*d) (jump d rev) x)
    (hd : 3≤d) (om : Odd (3*d)) (period : x^(3*d)=1)
    (reg : IsUnit (x-1)) (two : IsUnit (2:R)) : Nonempty (Theta B 16) := by
  let r := jump d rev
  let u := x^r
  have uc : u^3=1 := by
    change (x^(jump d rev))^3=1
    cases rev
    · change (x^d)^3=1
      rwa [←pow_mul,Nat.mul_comm]
    · change (x^(2*d))^3=1
      rw [←pow_mul,show 2*d*3=(3*d)*2 by omega,pow_mul,period,one_pow]
  have runFree {L : ℕ} (P : Table 47 16 15 15) (ob : Fin L → Fin 15 → ℤ)
      (cert : Valid P 15 5 0 basis ob) (width : ∀ i,(P.ht i).val%5<3)
      (sep : ∀ i,dot (weights x u) (ob i)≠0) : Nonempty (Theta B 16) := by
    apply bandTheta rev C P basis ob cert (weights x u)
      (fun i => lt_of_lt_of_le (width i) hd) (fun i => lt_trans (width i) (by decide : 3<4)) _ sep
    intro i
    exact (dot_basis x u i).trans (pow_place rev period i).symm
  by_cases norm : u^2+u+1=0
  · have ux := unit_period om period
    have plus : IsUnit (x+1) := by simpa [add_comm] using unit_sum_pow om period two 1
    by_cases other : 1-u*x≠0
    · have up : IsUnit (u+1) := by simpa [u,add_comm] using unit_sum_pow om period two r
      have vplus : IsUnit (1+u^2*x) := by
        simpa only [u,←pow_mul,←pow_succ] using unit_sum_pow om period two (r*2+1)
      exact runFree rowB.table rowB.obs rowB.valid rowB.width
        (rowB.cubic x u norm ux (ux.pow r) reg plus up vplus other)
    have prod : u*x=1 := by by_contra h; apply other; intro eq; apply h; linear_combination -eq
    have xc : x^3=1 := by
      calc x^3 = u^3*x^3 := by rw [uc,one_mul]
           _ = (u*x)^3 := by ring
           _ = 1 := by rw [prod,one_pow]
    have us : u=x^2 := by
      calc u = u*x^3 := by rw [xc,mul_one]
           _ = (u*x)*x^2 := by ring
           _ = x^2 := by rw [prod,one_mul]
    have phi : x^2+x+1=0 := reg.mul_right_eq_zero.mp (by linear_combination xc)
    have three : (3:R)≠0 := by
      intro zero
      apply (reg.pow 2).ne_zero
      linear_combination phi-x*zero
    have large : 4≤d := by
      by_contra! small
      have eq : d=3 := by omega
      have u1 : u=1 := by
        dsimp [u,r,jump]
        cases rev <;> simp [eq,show x^6=1 by rw [show (6:ℕ)=3*2 by decide,pow_mul,xc,one_pow],xc]
      apply reg.ne_zero
      rw [u1,one_mul] at prod
      rw [prod,sub_self]
    apply bandTheta rev C rowD.table rowD.gap rowD.obs rowD.valid (rowD.ew x)
      (fun i => lt_of_lt_of_le (rowD.width i) large) rowD.width _ (rowD.cubic x phi three)
    intro i
    rw [pow_place rev period]
    change _ = x^(i.val%5)*u^(i.val/5)
    rw [us]
    exact rowD.gap_value x phi i
  · let I : Ideal R := Ideal.span {u-1}
    have proper : I≠⊤ := by
      intro top
      have unit := Ideal.span_singleton_eq_top.mp top
      apply norm
      apply unit.mul_right_eq_zero.mp
      linear_combination uc
    let S := R ⧸ I
    let _ : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr proper
    let f := Ideal.Quotient.mk I
    have fu : f u=1 := by
      apply sub_eq_zero.mp
      rw [←map_one f,←map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have fp : (f x)^(3*d)=1 := by rw [←map_pow,period,map_one]
    have fr : IsUnit (f x-1) := by simpa only [map_sub,map_one] using reg.map f
    have ft : IsUnit (2:S) := by simpa only [map_ofNat] using two.map f
    rcases one_fixed (f x) om fp fr ft with ha|hb|hc
    · exact runFree rowA.table rowA.obs rowA.valid rowA.width (fun i => project_fixed f x u fu _ (ha i))
    · exact runFree rowB.table rowB.obs rowB.valid rowB.width (fun i => project_fixed f x u fu _ (hb i))
    · exact runFree rowC.table rowC.obs rowC.valid rowC.width (fun i => project_fixed f x u fu _ (hc i))

theorem chart {d : ℕ} {x : R} (rev : Bool) (C : Chart B (3*d) (jump d rev) x)
    (different : jump d rev ≠ 1) (om : Odd (3*d)) (period : x^(3*d)=1)
    (reg : IsUnit (x-1)) (two : IsUnit (2:R)) :
    Nonempty (Theta B 16) ∨ Nonempty (Theta B 8) := by
  by_cases h : 3≤d
  · exact .inl (large rev C h om period reg two)
  obtain ⟨k,hk⟩ := om
  have e : d=1 := by omega
  subst d
  cases rev
  · exact False.elim (different rfl)
  · exact MetabelianProgression.indexThree C period two reg

end MetabelianOrderThree

namespace OddDyadicSize
open EqualArms MetabelianRegular
universe u v
def Short {M : Type u} [Group M] (s t : M) : Prop :=
  ∃ (Q : Type v) (_ : Group Q) (_ : Nontrivial Q) (π : M →* Q),
    Function.Surjective π ∧ ∃ j : ℕ, 1≤j ∧ j≤4 ∧
      Nonempty (Theta (rightMatching (π s) (π t)) (2^j))

def CyclicShort : Prop :=
  ∀ (M : Type u) [Group M] [Finite M], Odd (Nat.card M) → IsMulCommutative (commutator M) →
    IsCyclic (Abelianization M) → ∀ s t : M, Subgroup.closure ({s,t} : Set M)=⊤ →
      s≠1 → t≠1 → s≠t → ¬Commute s t → Short.{u,v} s t

end OddDyadicSize

namespace SmallHNF
abbrev Point := ℤ × ℤ

def eval {Q : Type*} [AddCommGroup Q] (a b : Q) (p : Point) : Q := p.1 • a+p.2 • b
def project (A B C : ℕ) (v : Point) : Point :=
  ((v.1-(B:ℤ)*(v.2/(C:ℤ)))%(A:ℤ),v.2%(C:ℤ))
def coord {Q : Type*} [AddCommGroup Q] (a b : Q) {A C : ℕ} (p : Fin A × Fin C) : Q :=
  p.1.val • a+p.2.val • b

structure Frame {Q : Type*} [AddCommGroup Q] (a b : Q) (A B C : ℕ) : Prop where
  width : 0<A
  shear : B<A
  height : 0<C
  area : A*C=Nat.card Q
  horizontal : (A:ℤ) • a=0
  diagonal : (B:ℤ) • a+(C:ℤ) • b=0
  bijective : Function.Bijective (coord a b : Fin A × Fin C → Q)

theorem project_eval {Q : Type*} [AddCommGroup Q] (a b : Q) {A B C : ℕ}
    (hA : (A:ℤ) • a=0) (hC : (B:ℤ) • a+(C:ℤ) • b=0) (p : Point) :
    eval a b (project A B C p)=eval a b p := by
  let x := p.1-(B:ℤ)*(p.2/(C:ℤ))
  have horizontal : (x%(A:ℤ)) • a=x • a := by
    have h := congrArg (fun k : ℤ => k • a) (Int.emod_add_ediv_mul x (A:ℤ))
    simpa only [add_zsmul,mul_zsmul,hA,zsmul_zero,add_zero] using h
  have vertical := congrArg (fun k : ℤ => k • b) (Int.emod_add_ediv_mul p.2 (C:ℤ))
  change (p.2%(C:ℤ)+p.2/(C:ℤ)*(C:ℤ)) • b=p.2 • b at vertical
  have relation : (C:ℤ) • b= -((B:ℤ) • a) := by
    linear_combination (norm := abel) hC
  rw [add_zsmul,mul_zsmul,relation,zsmul_neg] at vertical
  change (x%(A:ℤ)) • a + (p.2%(C:ℤ)) • b=p.1 • a+p.2 • b
  rw [horizontal]
  dsimp [x]
  rw [sub_zsmul,mul_comm (B:ℤ),mul_zsmul]
  linear_combination (norm := abel) vertical

theorem project_finite {A B C : ℕ} (hA : 0<A) (hC : 0<C) (p : Point) :
    ∃ v : Fin A × Fin C, project A B C p=((v.1.val:ℤ),(v.2.val:ℤ)) := by
  let z:=project A B C p
  have ap : (0:ℤ)<A := by exact_mod_cast hA
  have cp : (0:ℤ)<C := by exact_mod_cast hC
  have x0 : 0≤z.1 := Int.emod_nonneg _ ap.ne'
  have y0 : 0≤z.2 := Int.emod_nonneg _ cp.ne'
  have x1 : z.1<(A:ℤ) := Int.emod_lt_of_pos _ ap
  have y1 : z.2<(C:ℤ) := Int.emod_lt_of_pos _ cp
  refine ⟨(⟨z.1.toNat,by omega⟩,⟨z.2.toNat,by omega⟩),?_⟩
  change z=(↑z.1.toNat,↑z.2.toNat)
  exact Prod.ext (Int.toNat_of_nonneg x0).symm (Int.toNat_of_nonneg y0).symm

theorem eval_eq_iff {Q : Type*} [AddCommGroup Q] {a b : Q} {A B C : ℕ}
    (F : Frame a b A B C) (p r : Point) :
    eval a b p=eval a b r ↔ project A B C p=project A B C r := by
  have pe := project_eval a b F.horizontal F.diagonal p
  have re := project_eval a b F.horizontal F.diagonal r
  obtain ⟨v,hv⟩ := project_finite (B:=B) F.width F.height p
  obtain ⟨w,hw⟩ := project_finite (B:=B) F.width F.height r
  rw [hv] at pe
  rw [hw] at re
  constructor
  · intro equal
    have same : (coord a b v) = (coord a b w) := by simpa [coord,eval] using pe.trans (equal.trans re.symm)
    rw [hv,hw,F.bijective.1 same]
  · intro equal
    rw [←project_eval a b F.horizontal F.diagonal p,←project_eval a b F.horizontal F.diagonal r,equal]

theorem exists_frame {Q : Type*} [AddCommGroup Q] [Finite Q] (a b : Q)
    (gen : AddSubgroup.closure ({a,b} : Set Q)=⊤) : ∃ A B C,Frame a b A B C := by
  classical
  let H := AddSubgroup.zmultiples a
  let q := QuotientAddGroup.mk' H
  let A := addOrderOf a
  let C := addOrderOf (q b)
  have ap : 0<A := addOrderOf_pos a
  have cp : 0<C := addOrderOf_pos (q b)
  have aq : q a=0 := (QuotientAddGroup.eq_zero_iff a).mpr (AddSubgroup.mem_zmultiples a)
  have cardH : Nat.card H=A := Nat.card_zmultiples a
  have top : AddSubgroup.zmultiples (q b)=⊤ := by
    apply top_unique
    intro y _
    obtain ⟨g,rfl⟩ := QuotientAddGroup.mk'_surjective H y
    obtain ⟨i,j,rep⟩ := AddSubgroup.mem_closure_pair.mp (gen ▸ AddSubgroup.mem_top g)
    change i • a+j • b=g at rep
    rw [←rep,map_add,map_zsmul,map_zsmul,aq,zsmul_zero,zero_add]
    exact ⟨j,rfl⟩
  have cardQ : C=Nat.card (Q ⧸ H) := addOrderOf_eq_card_of_zmultiples_eq_top top
  have area : A*C=Nat.card Q := by
    rw [←cardH,cardQ,←H.index_eq_card,H.card_mul_index]
  have cat : q (-(C • b))=0 := by simp [C]
  have member : -(C • b) ∈ H := (QuotientAddGroup.eq_zero_iff _).mp cat
  obtain ⟨j,hj⟩ := member
  change j • a= -(C • b) at hj
  let B := (j%(A:ℤ)).toNat
  have aj : (0:ℤ)<A := by exact_mod_cast ap
  have rem0 := Int.emod_nonneg j aj.ne'
  have rem1 := Int.emod_lt_of_pos j aj
  have bj : (B:ℤ)=j%(A:ℤ) := Int.toNat_of_nonneg rem0
  have ba : B<A := by dsimp [B];omega
  have horizontal : (A:ℤ) • a=0 := by simp [A]
  have diag : (B:ℤ) • a+(C:ℤ) • b=0 := by
    rw [bj,mod_addOrderOf_zsmul,hj]
    simp
  refine ⟨A,B,C,ap,ba,cp,area,horizontal,diag,?_,?_⟩
  · rintro ⟨x,y⟩ ⟨u,v⟩ equal
    change x.val • a+y.val • b=u.val • a+v.val • b at equal
    have pr := congrArg q equal
    simp only [map_add,map_nsmul,aq,nsmul_zero,zero_add] at pr
    obtain rfl : y=v := Fin.ext (nsmul_injOn_Iio_addOrderOf y.isLt v.isLt pr)
    have h := add_right_cancel equal
    exact Prod.ext (Fin.ext (nsmul_injOn_Iio_addOrderOf x.isLt u.isLt h)) rfl
  · intro g
    obtain ⟨i,j,rep⟩ := AddSubgroup.mem_closure_pair.mp (gen ▸ AddSubgroup.mem_top g)
    obtain ⟨v,hv⟩ := project_finite (B:=B) ap cp (i,j)
    have reduced := project_eval a b horizontal diag (i,j)
    rw [hv] at reduced
    exact ⟨v,(by simpa [coord,eval] using reduced.trans rep)⟩

end SmallHNF

/- Two independent lattice collisions bound the size of the quotient. -/
namespace SevenFaceLattice

abbrev Plane := Fin 2 → ℤ
abbrev Point := ℤ × ℤ
def vec (w : Point) : Plane := ![w.1,w.2]
def det (w z : Point) : ℤ := w.1*z.2-z.1*w.2

theorem card_dvd_det {Q : Type*} [AddCommGroup Q] (f : Plane →+ Q) (surj : Function.Surjective f)
    (w z : Point) (hw : f (vec w)=0) (hz : f (vec z)=0) :
    Nat.card Q ∣ (det w z).natAbs := by
  classical
  by_cases zero : det w z=0
  · simp [zero]
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![w.1,z.1;w.2,z.2]
  have d : M.det=det w z := Matrix.det_fin_two _
  let T := M.mulVecLin
  have inj : Function.Injective T := M.mulVec_injective_of_det_ne_zero (d ▸ zero)
  let E := LinearEquiv.ofInjective T inj
  have quotient := Submodule.natAbs_det_equiv T.range E
  change (LinearMap.det T).natAbs = T.range.toAddSubgroup.index at quotient
  have detT : LinearMap.det T=M.det := by
    rw [← LinearMap.det_toMatrix']
    change (LinearMap.toMatrix' (Matrix.toLin' M)).det = M.det
    simp
  have contained : T.range.toAddSubgroup ≤ f.ker := by
    rintro _ ⟨v,rfl⟩
    have cols : T v=v 0 • vec w+v 1 • vec z := by
      funext i
      fin_cases i <;> simp [T,M,vec,Matrix.mulVec,Fin.sum_univ_two,mul_comm,dotProduct]
    change f (T v)=0
    rw [cols,map_add,map_zsmul,map_zsmul,hw,hz]
    simp
  have ker : f.ker.index=Nat.card Q := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_congr (((AddEquiv.addSubgroupCongr (AddMonoidHom.range_eq_top.mpr surj)).trans
      AddSubgroup.topEquiv).toEquiv)
  rw [← ker,← d,← detT,quotient]
  exact AddSubgroup.index_dvd_of_le contained

def directions {Q : Type*} [AddCommGroup Q] (a b : Q) : Fin 6 → Q × Q :=
  ![(a,b),(b,a),(-a,b-a),(b-a,-a),(-b,a-b),(a-b,-b)]

def mark {Q : Type*} [AddCommGroup Q] (a b : Q) : Plane →+ Q where
  toFun p := p 0 • a + p 1 • b
  map_zero' := by simp
  map_add' p q := by simp [add_zsmul]; abel

end SevenFaceLattice

/- Check the integer honeycomb atlas, then project it through the marked quotient. -/
namespace OrdinaryCyclicTheta
open EqualArms MetabelianRegular SmallHNF
abbrev V2 := ℤ × ℤ
abbrev Site := Bool × V2

def canon (p : V2) : V2 := if p.1<0 ∨ (p.1=0 ∧ p.2<0) then -p else p

structure Patch where
  len : ℕ
  point : Fin 3 → Fin (len+1) → Site
  equal : List V2
  distinct : List V2

def edge (p q : Site) : Prop := p.1=false ∧ q.1=true ∧
  (q.2=p.2 ∨ q.2=p.2+(1,0) ∨ q.2=p.2+(0,1))
instance (p q : Site) : Decidable (edge p q) := by unfold edge; infer_instance

def Shape (P : Patch) : Prop :=
  (P.len=8 ∨ P.len=16) ∧
  (∀ c, P.point c 0=P.point 0 0 ∧ (P.point c (Fin.last P.len)).1=(P.point 0 (Fin.last P.len)).1 ∧
    canon ((P.point c (Fin.last P.len)).2-(P.point 0 (Fin.last P.len)).2) ∈ P.equal) ∧
  (∀ c (i : Fin P.len),edge (P.point c i.castSucc) (P.point c i.succ) ∨
    edge (P.point c i.succ) (P.point c i.castSucc)) ∧
  (∀ c e i j,(c=e ∧ i=j) ∨ (i=0 ∧ j=0) ∨ (i=Fin.last P.len ∧ j=Fin.last P.len) ∨
    (P.point c i).1≠(P.point e j).1 ∨
    canon ((P.point c i).2-(P.point e j).2) ∈ P.distinct)
instance (P : Patch) : Decidable (Shape P) := by unfold Shape; infer_instance

variable {Q : Type*} [AddCommGroup Q]

def marking (a b : Q) : V2 →+ Q where
  toFun := eval a b
  map_zero' := by simp [eval]
  map_add' p q := by simp [eval,add_zsmul]; abel

def Valid (f : V2 →+ Q) (P : Patch) : Prop :=
  (∀ w∈P.equal,f w=0) ∧ ∀ w∈P.distinct,f w≠0

def Short (s t : Multiplicative Q) : Prop :=
  Nonempty (Theta (rightMatching s t) 8) ∨ Nonempty (Theta (rightMatching s t) 16)

theorem canon_zero (f : V2 →+ Q) (p : V2) : f (canon p)=0 ↔ f p=0 := by
  unfold canon
  split <;> simp

private def project (a b : Q) (p : Site) : Bool × Multiplicative Q :=
  (p.1,Multiplicative.ofAdd (marking a b p.2))

private theorem forward_adj (a b : Q) {p q : Site} (h : edge p q) :
    (rightMatching (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)).Adj
      (project a b p) (project a b q) := by
  rcases p with ⟨s,p⟩
  rcases q with ⟨t,q⟩
  obtain ⟨rfl,rfl,h⟩ := h
  apply (rightMatching_adj _ _ _ _).2
  rcases h with rfl|rfl|rfl
  · exact Or.inl rfl
  · right; left
    change marking a b (p+(1,0))=marking a b p + a
    simp [map_add,marking,eval]
  · right; right
    change marking a b (p+(0,1))=marking a b p + b
    simp [map_add,marking,eval]

theorem of_patch (a b : Q) (P : Patch) (shape : Shape P) (good : Valid (marking a b) P) :
    Short (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) := by
  obtain ⟨length,ends,edges,apart⟩ := shape
  have pos : 0<P.len := by rcases length with h|h <;> omega
  let idx (i : ℕ) : Fin (P.len+1) := ⟨min i P.len,by omega⟩
  let v (c : Fin 3) (i : Fin (P.len+1)) := project a b (P.point c i)
  have separate (c e : Fin 3) (i j : Fin (P.len+1)) (eq : v c i=v e j) :
      (c=e ∧ i=j) ∨ (i=0 ∧ j=0) ∨ (i=Fin.last P.len ∧ j=Fin.last P.len) := by
    rcases apart c e i j with h|h|h|diff|key
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
    · exact (diff (congrArg (fun z : Bool × Multiplicative Q => z.1) eq)).elim
    · apply False.elim
      apply good.2 _ key
      apply (canon_zero ..).mpr
      rw [map_sub,sub_eq_zero]
      exact congrArg (fun p : Bool × Multiplicative Q => p.2.toAdd) eq
  have htheta : Nonempty (Theta (rightMatching (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)) P.len) := by
    refine ⟨⟨v 0 0,v 0 (Fin.last P.len),?_,fun c i => v c (idx i),?_,?_,?_,?_,?_⟩⟩
    · intro eq
      have := separate 0 0 0 (Fin.last P.len) eq
      simp only [true_and,Fin.ext_iff,Fin.val_zero,Fin.val_last] at this
      omega
    · intro c
      change project a b (P.point c (idx 0))=_
      rw [show idx 0=0 by apply Fin.ext; simp [idx],(ends c).1]
    · intro c
      rw [show idx P.len=Fin.last P.len by apply Fin.ext; simp [idx]]
      apply Prod.ext
      · exact (ends c).2.1
      · apply congrArg Multiplicative.ofAdd
        have z := (canon_zero ..).mp (good.1 _ (ends c).2.2)
        rw [map_sub] at z
        exact sub_eq_zero.mp z
    · intro c i hi
      let k : Fin P.len := ⟨i,hi⟩
      rw [show idx i=k.castSucc by apply Fin.ext; exact Nat.min_eq_left hi.le,
          show idx (i+1)=k.succ by apply Fin.ext; exact Nat.min_eq_left hi]
      rcases edges c k with f|r
      · exact forward_adj a b f
      · exact (forward_adj a b r).symm
    · intro c i hi hd
      constructor <;> intro eq
      · have h := separate c 0 (idx i) 0 eq
        simp only [Fin.ext_iff,Fin.val_zero,Fin.val_last,idx,Nat.min_eq_left hd.le] at h
        omega
      · have h := separate c 0 (idx i) (Fin.last P.len) eq
        simp only [Fin.ext_iff,Fin.val_zero,Fin.val_last,idx,Nat.min_eq_left hd.le] at h
        omega
    · intro c e i j hi hd hj he eq
      have h := separate c e (idx i) (idx j) eq
      rcases h with ⟨rfl,ij⟩|⟨ij,_⟩|⟨ij,_⟩
      · exact ⟨rfl,by simpa [idx,hd.le,he.le] using congrArg Fin.val ij⟩
      all_goals have h':=congrArg Fin.val ij; simp [idx,hd.le] at h'; omega
  rcases length with h|h
  · exact Or.inl (h ▸ htheta)
  · exact Or.inr (h ▸ htheta)

end OrdinaryCyclicTheta

namespace OrdinaryCyclicTheta
def keys : List V2 := [(0,1),(0,3),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-3),(2,-1),(2,1),(3,-3),(3,-2),(3,-1),(3,0)]
def p0 : Patch := ⟨16,
  ![![(false,(0,0)),(true,(0,0)),(false,(-1,0)),(true,(-1,1)),(false,(-2,1)),(true,(-2,1)),(false,(-2,0)),(true,(-1,0)),(false,(-1,-1)),(true,(0,-1)),(false,(0,-1)),(true,(1,-1)),(false,(1,-2)),(true,(1,-2)),(false,(0,-2)),(true,(0,-2)),(false,(-1,-2))],![(false,(0,0)),(true,(1,0)),(false,(1,0)),(true,(2,0)),(false,(2,-1)),(true,(2,-1)),(false,(2,-2)),(true,(2,-2)),(false,(2,-3)),(true,(2,-3)),(false,(1,-3)),(true,(1,-3)),(false,(0,-3)),(true,(0,-3)),(false,(-1,-3)),(true,(-1,-2)),(false,(-1,-2))],![(false,(0,0)),(true,(0,1)),(false,(0,1)),(true,(0,2)),(false,(-1,2)),(true,(-1,2)),(false,(-2,2)),(true,(-2,2)),(false,(-3,2)),(true,(-3,2)),(false,(-3,1)),(true,(-3,1)),(false,(-3,0)),(true,(-2,0)),(false,(-2,-1)),(true,(-1,-1)),(false,(-1,-2))]],
  [(0,0)],
  [(0,1),(0,2),(0,3),(0,4),(0,5),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1)]⟩
def p1 : Patch := ⟨16,
  ![![(false,(0,0)),(true,(0,0)),(false,(0,-1)),(true,(1,-1)),(false,(1,-2)),(true,(1,-2)),(false,(0,-2)),(true,(0,-1)),(false,(-1,-1)),(true,(-1,0)),(false,(-1,0)),(true,(-1,1)),(false,(-2,1)),(true,(-2,1)),(false,(-2,0)),(true,(-2,0)),(false,(-2,-1))],![(false,(0,0)),(true,(0,1)),(false,(0,1)),(true,(0,2)),(false,(-1,2)),(true,(-1,2)),(false,(-2,2)),(true,(-2,2)),(false,(-3,2)),(true,(-3,2)),(false,(-3,1)),(true,(-3,1)),(false,(-3,0)),(true,(-3,0)),(false,(-3,-1)),(true,(-2,-1)),(false,(-2,-1))],![(false,(0,0)),(true,(1,0)),(false,(1,0)),(true,(2,0)),(false,(2,-1)),(true,(2,-1)),(false,(2,-2)),(true,(2,-2)),(false,(2,-3)),(true,(2,-3)),(false,(1,-3)),(true,(1,-3)),(false,(0,-3)),(true,(0,-2)),(false,(-1,-2)),(true,(-1,-1)),(false,(-2,-1))]],
  [(0,0)],
  [(0,1),(0,2),(0,3),(0,4),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0)]⟩
def p2 : Patch := ⟨16,
  ![![(false,(0,0)),(true,(1,0)),(false,(1,0)),(true,(1,1)),(false,(1,1)),(true,(2,1)),(false,(2,0)),(true,(2,0)),(false,(2,-1)),(true,(2,-1)),(false,(1,-1)),(true,(1,-1)),(false,(1,-2)),(true,(2,-2)),(false,(2,-2)),(true,(3,-2)),(false,(3,-2))],![(false,(0,0)),(true,(0,0)),(false,(-1,0)),(true,(-1,0)),(false,(-1,-1)),(true,(0,-1)),(false,(0,-2)),(true,(1,-2)),(false,(1,-3)),(true,(2,-3)),(false,(2,-3)),(true,(3,-3)),(false,(3,-3)),(true,(4,-3)),(false,(4,-3)),(true,(4,-2)),(false,(3,-2))],![(false,(0,0)),(true,(0,1)),(false,(-1,1)),(true,(-1,2)),(false,(-1,2)),(true,(0,2)),(false,(0,2)),(true,(1,2)),(false,(1,2)),(true,(2,2)),(false,(2,1)),(true,(3,1)),(false,(3,0)),(true,(3,0)),(false,(3,-1)),(true,(3,-1)),(false,(3,-2))]],
  [(0,0)],
  [(0,1),(0,2),(0,3),(0,4),(0,5),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(5,-5),(5,-4),(5,-3),(5,-2)]⟩
def p3 : Patch := ⟨16,
  ![![(false,(0,0)),(true,(1,0)),(false,(1,-1)),(true,(1,-1)),(false,(1,-2)),(true,(2,-2)),(false,(2,-2)),(true,(2,-1)),(false,(2,-1)),(true,(2,0)),(false,(1,0)),(true,(1,1)),(false,(1,1)),(true,(2,1)),(false,(2,0)),(true,(3,0)),(false,(3,-1))],![(false,(0,0)),(true,(0,1)),(false,(-1,1)),(true,(-1,2)),(false,(-1,2)),(true,(0,2)),(false,(0,2)),(true,(1,2)),(false,(1,2)),(true,(2,2)),(false,(2,1)),(true,(3,1)),(false,(3,0)),(true,(4,0)),(false,(4,-1)),(true,(4,-1)),(false,(3,-1))],![(false,(0,0)),(true,(0,0)),(false,(-1,0)),(true,(-1,0)),(false,(-1,-1)),(true,(0,-1)),(false,(0,-2)),(true,(1,-2)),(false,(1,-3)),(true,(2,-3)),(false,(2,-3)),(true,(3,-3)),(false,(3,-3)),(true,(3,-2)),(false,(3,-2)),(true,(3,-1)),(false,(3,-1))]],
  [(0,0)],
  [(0,1),(0,2),(0,3),(0,4),(0,5),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(5,-3),(5,-2),(5,-1),(5,0)]⟩
def p4 : Patch := ⟨16,
  ![![(false,(0,0)),(true,(0,1)),(false,(0,1)),(true,(1,1)),(false,(1,1)),(true,(1,2)),(false,(0,2)),(true,(0,2)),(false,(-1,2)),(true,(-1,2)),(false,(-1,1)),(true,(-1,1)),(false,(-2,1)),(true,(-2,2)),(false,(-2,2)),(true,(-2,3)),(false,(-2,3))],![(false,(0,0)),(true,(0,0)),(false,(0,-1)),(true,(0,-1)),(false,(-1,-1)),(true,(-1,0)),(false,(-2,0)),(true,(-2,1)),(false,(-3,1)),(true,(-3,2)),(false,(-3,2)),(true,(-3,3)),(false,(-3,3)),(true,(-3,4)),(false,(-3,4)),(true,(-2,4)),(false,(-2,3))],![(false,(0,0)),(true,(1,0)),(false,(1,-1)),(true,(2,-1)),(false,(2,-1)),(true,(2,0)),(false,(2,0)),(true,(2,1)),(false,(2,1)),(true,(2,2)),(false,(1,2)),(true,(1,3)),(false,(0,3)),(true,(0,3)),(false,(-1,3)),(true,(-1,3)),(false,(-2,3))]],
  [(0,0)],
  [(0,1),(0,2),(0,3),(0,4),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(5,-5),(5,-4),(5,-3),(5,-2),(5,-1),(5,0)]⟩
def p5 : Patch := ⟨16,
  ![![(false,(0,0)),(true,(0,1)),(false,(-1,1)),(true,(-1,1)),(false,(-2,1)),(true,(-2,2)),(false,(-2,2)),(true,(-1,2)),(false,(-1,2)),(true,(0,2)),(false,(0,1)),(true,(1,1)),(false,(1,1)),(true,(1,2)),(false,(0,2)),(true,(0,3)),(false,(-1,3))],![(false,(0,0)),(true,(1,0)),(false,(1,-1)),(true,(2,-1)),(false,(2,-1)),(true,(2,0)),(false,(2,0)),(true,(2,1)),(false,(2,1)),(true,(2,2)),(false,(1,2)),(true,(1,3)),(false,(0,3)),(true,(0,4)),(false,(-1,4)),(true,(-1,4)),(false,(-1,3))],![(false,(0,0)),(true,(0,0)),(false,(0,-1)),(true,(0,-1)),(false,(-1,-1)),(true,(-1,0)),(false,(-2,0)),(true,(-2,1)),(false,(-3,1)),(true,(-3,2)),(false,(-3,2)),(true,(-3,3)),(false,(-3,3)),(true,(-2,3)),(false,(-2,3)),(true,(-1,3)),(false,(-1,3))]],
  [(0,0)],
  [(0,1),(0,2),(0,3),(0,4),(0,5),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(5,-4),(5,-3),(5,-2),(5,-1),(5,0)]⟩
def p6 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(0,0)),(false,(-1,0)),(true,(-1,1)),(false,(-2,1)),(true,(-2,1)),(false,(-2,0)),(true,(-2,0)),(false,(-2,-1))],![(false,(0,0)),(true,(1,0)),(false,(1,-1)),(true,(1,-1)),(false,(0,-1)),(true,(0,-1)),(false,(-1,-1)),(true,(-1,-1)),(false,(-2,-1))],![(false,(0,0)),(true,(0,1)),(false,(-1,1)),(true,(-1,2)),(false,(-2,2)),(true,(-2,2)),(false,(-3,2)),(true,(-3,3)),(false,(-3,3))]],
  [(0,0),(1,-4)],
  [(0,1),(0,2),(0,3),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(4,-4),(4,-3)]⟩
def p7 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(0,0)),(false,(0,-1)),(true,(1,-1)),(false,(1,-2)),(true,(1,-2)),(false,(0,-2)),(true,(0,-2)),(false,(-1,-2))],![(false,(0,0)),(true,(0,1)),(false,(-1,1)),(true,(-1,1)),(false,(-1,0)),(true,(-1,0)),(false,(-1,-1)),(true,(-1,-1)),(false,(-1,-2))],![(false,(0,0)),(true,(1,0)),(false,(1,-1)),(true,(2,-1)),(false,(2,-2)),(true,(2,-2)),(false,(2,-3)),(true,(3,-3)),(false,(3,-3))]],
  [(0,0),(4,-1)],
  [(0,1),(0,2),(0,3),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(4,-4),(4,-3),(4,-2)]⟩
def p8 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(1,0)),(false,(1,0)),(true,(1,1)),(false,(1,1)),(true,(2,1)),(false,(2,0)),(true,(3,0)),(false,(3,-1))],![(false,(0,0)),(true,(0,0)),(false,(0,-1)),(true,(1,-1)),(false,(1,-1)),(true,(2,-1)),(false,(2,-1)),(true,(3,-1)),(false,(3,-1))],![(false,(0,0)),(true,(0,1)),(false,(0,1)),(true,(0,2)),(false,(0,2)),(true,(1,2)),(false,(1,2)),(true,(1,3)),(false,(0,3))]],
  [(0,0),(3,-4)],
  [(0,1),(0,2),(0,3),(0,4),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-3),(3,-2),(3,-1),(3,0)]⟩
def p9 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(1,0)),(false,(1,-1)),(true,(1,-1)),(false,(1,-2)),(true,(2,-2)),(false,(2,-2)),(true,(3,-2)),(false,(3,-2))],![(false,(0,0)),(true,(0,1)),(false,(0,1)),(true,(1,1)),(false,(1,0)),(true,(2,0)),(false,(2,-1)),(true,(3,-1)),(false,(3,-2))],![(false,(0,0)),(true,(0,0)),(false,(0,-1)),(true,(0,-1)),(false,(0,-2)),(true,(1,-2)),(false,(1,-3)),(true,(1,-3)),(false,(0,-3))]],
  [(0,0),(3,1)],
  [(0,1),(0,2),(0,3),(0,4),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(3,-3),(3,-2),(3,-1),(3,0)]⟩
def p10 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(0,1)),(false,(0,1)),(true,(1,1)),(false,(1,1)),(true,(1,2)),(false,(0,2)),(true,(0,3)),(false,(-1,3))],![(false,(0,0)),(true,(0,0)),(false,(-1,0)),(true,(-1,1)),(false,(-1,1)),(true,(-1,2)),(false,(-1,2)),(true,(-1,3)),(false,(-1,3))],![(false,(0,0)),(true,(1,0)),(false,(1,0)),(true,(2,0)),(false,(2,0)),(true,(2,1)),(false,(2,1)),(true,(3,1)),(false,(3,0))]],
  [(0,0),(4,-3)],
  [(0,1),(0,2),(0,3),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(4,-2),(4,-1),(4,0)]⟩
def p11 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(0,1)),(false,(-1,1)),(true,(-1,1)),(false,(-2,1)),(true,(-2,2)),(false,(-2,2)),(true,(-2,3)),(false,(-2,3))],![(false,(0,0)),(true,(1,0)),(false,(1,0)),(true,(1,1)),(false,(0,1)),(true,(0,2)),(false,(-1,2)),(true,(-1,3)),(false,(-2,3))],![(false,(0,0)),(true,(0,0)),(false,(-1,0)),(true,(-1,0)),(false,(-2,0)),(true,(-2,1)),(false,(-3,1)),(true,(-3,1)),(false,(-3,0))]],
  [(0,0),(1,3)],
  [(0,1),(0,2),(0,3),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(4,-1),(4,0)]⟩
def p12 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(0,0)),(false,(-1,0)),(true,(-1,1)),(false,(-2,1)),(true,(-2,1)),(false,(-2,0)),(true,(-1,0)),(false,(-1,-1))],![(false,(0,0)),(true,(1,0)),(false,(1,-1)),(true,(1,-1)),(false,(1,-2)),(true,(1,-2)),(false,(0,-2)),(true,(0,-1)),(false,(-1,-1))],![(false,(0,0)),(true,(0,1)),(false,(-1,1)),(true,(-1,2)),(false,(-2,2)),(true,(-2,3)),(false,(-3,3)),(true,(-3,4)),(false,(-3,4))]],
  [(0,0),(2,-5)],
  [(0,1),(0,2),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(4,-6),(4,-5),(4,-4)]⟩
def p13 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(0,0)),(false,(0,-1)),(true,(1,-1)),(false,(1,-2)),(true,(1,-2)),(false,(0,-2)),(true,(0,-1)),(false,(-1,-1))],![(false,(0,0)),(true,(0,1)),(false,(-1,1)),(true,(-1,1)),(false,(-2,1)),(true,(-2,1)),(false,(-2,0)),(true,(-1,0)),(false,(-1,-1))],![(false,(0,0)),(true,(1,0)),(false,(1,-1)),(true,(2,-1)),(false,(2,-2)),(true,(3,-2)),(false,(3,-3)),(true,(4,-3)),(false,(4,-3))]],
  [(0,0),(5,-2)],
  [(0,1),(0,2),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(2,-3),(2,-2),(2,-1),(2,0),(3,-3),(3,-2),(3,-1),(4,-4),(4,-3),(4,-2),(4,-1),(5,-4),(5,-3),(6,-4),(6,-3)]⟩
def p14 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(1,0)),(false,(1,0)),(true,(1,1)),(false,(1,1)),(true,(2,1)),(false,(2,0)),(true,(2,0)),(false,(2,-1))],![(false,(0,0)),(true,(0,0)),(false,(0,-1)),(true,(1,-1)),(false,(1,-2)),(true,(2,-2)),(false,(2,-2)),(true,(2,-1)),(false,(2,-1))],![(false,(0,0)),(true,(0,1)),(false,(0,1)),(true,(0,2)),(false,(0,2)),(true,(0,3)),(false,(0,3)),(true,(0,4)),(false,(-1,4))]],
  [(0,0),(3,-5)],
  [(0,1),(0,2),(0,3),(0,4),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-6),(3,-4)]⟩
def p15 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(1,0)),(false,(1,-1)),(true,(1,-1)),(false,(1,-2)),(true,(2,-2)),(false,(2,-2)),(true,(2,-1)),(false,(2,-1))],![(false,(0,0)),(true,(0,1)),(false,(0,1)),(true,(1,1)),(false,(1,1)),(true,(2,1)),(false,(2,0)),(true,(2,0)),(false,(2,-1))],![(false,(0,0)),(true,(0,0)),(false,(0,-1)),(true,(0,-1)),(false,(0,-2)),(true,(0,-2)),(false,(0,-3)),(true,(0,-3)),(false,(-1,-3))]],
  [(0,0),(3,2)],
  [(0,1),(0,2),(0,3),(0,4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)]⟩
def p16 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(0,1)),(false,(0,1)),(true,(1,1)),(false,(1,1)),(true,(1,2)),(false,(0,2)),(true,(0,2)),(false,(-1,2))],![(false,(0,0)),(true,(0,0)),(false,(-1,0)),(true,(-1,1)),(false,(-2,1)),(true,(-2,2)),(false,(-2,2)),(true,(-1,2)),(false,(-1,2))],![(false,(0,0)),(true,(1,0)),(false,(1,0)),(true,(2,0)),(false,(2,0)),(true,(3,0)),(false,(3,0)),(true,(4,0)),(false,(4,-1))]],
  [(0,0),(5,-3)],
  [(0,1),(0,2),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-2),(2,-1),(2,0),(2,1),(3,-2),(3,-1),(3,0),(4,-3),(4,-2),(4,-1),(4,0),(5,-2),(5,-1),(6,-3),(6,-2)]⟩
def p17 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(0,1)),(false,(-1,1)),(true,(-1,1)),(false,(-2,1)),(true,(-2,2)),(false,(-2,2)),(true,(-1,2)),(false,(-1,2))],![(false,(0,0)),(true,(1,0)),(false,(1,0)),(true,(1,1)),(false,(1,1)),(true,(1,2)),(false,(0,2)),(true,(0,2)),(false,(-1,2))],![(false,(0,0)),(true,(0,0)),(false,(-1,0)),(true,(-1,0)),(false,(-2,0)),(true,(-2,0)),(false,(-3,0)),(true,(-3,0)),(false,(-3,-1))]],
  [(0,0),(2,3)],
  [(0,1),(0,2),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)]⟩
def p18 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(0,0)),(false,(-1,0)),(true,(-1,0)),(false,(-2,0)),(true,(-2,0)),(false,(-3,0)),(true,(-3,1)),(false,(-3,1))],![(false,(0,0)),(true,(1,0)),(false,(1,0)),(true,(2,0)),(false,(2,0)),(true,(3,0)),(false,(3,0)),(true,(4,0)),(false,(4,-1))],![(false,(0,0)),(true,(0,1)),(false,(-1,1)),(true,(-1,2)),(false,(-2,2)),(true,(-2,2)),(false,(-2,1)),(true,(-2,1)),(false,(-3,1))]],
  [(0,0),(7,-2)],
  [(0,1),(0,2),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-2),(2,-1),(2,0),(2,1),(3,-2),(3,-1),(3,0),(4,-2),(4,-1),(4,0),(5,-2),(5,-1),(5,0),(6,-3),(6,-2),(6,-1),(6,0),(7,-1)]⟩
def p19 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(0,0)),(false,(0,-1)),(true,(0,-1)),(false,(0,-2)),(true,(0,-2)),(false,(0,-3)),(true,(1,-3)),(false,(1,-3))],![(false,(0,0)),(true,(0,1)),(false,(0,1)),(true,(0,2)),(false,(0,2)),(true,(0,3)),(false,(0,3)),(true,(0,4)),(false,(-1,4))],![(false,(0,0)),(true,(1,0)),(false,(1,-1)),(true,(2,-1)),(false,(2,-2)),(true,(2,-2)),(false,(1,-2)),(true,(1,-2)),(false,(1,-3))]],
  [(0,0),(2,-7)],
  [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,-7),(1,-6),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-6),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-6)]⟩
def p20 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(1,0)),(false,(1,0)),(true,(2,0)),(false,(2,0)),(true,(3,0)),(false,(3,0)),(true,(3,1)),(false,(2,1))],![(false,(0,0)),(true,(0,0)),(false,(-1,0)),(true,(-1,0)),(false,(-2,0)),(true,(-2,0)),(false,(-3,0)),(true,(-3,0)),(false,(-3,-1))],![(false,(0,0)),(true,(0,1)),(false,(0,1)),(true,(0,2)),(false,(0,2)),(true,(1,2)),(false,(1,1)),(true,(2,1)),(false,(2,1))]],
  [(0,0),(5,2)],
  [(0,1),(0,2),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-2),(2,-1),(2,0),(2,1),(2,2),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0),(5,1),(6,0),(6,1)]⟩
def p21 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(1,0)),(false,(1,-1)),(true,(2,-1)),(false,(2,-2)),(true,(3,-2)),(false,(3,-3)),(true,(3,-3)),(false,(2,-3))],![(false,(0,0)),(true,(0,1)),(false,(-1,1)),(true,(-1,2)),(false,(-2,2)),(true,(-2,3)),(false,(-3,3)),(true,(-3,4)),(false,(-3,4))],![(false,(0,0)),(true,(0,0)),(false,(0,-1)),(true,(0,-1)),(false,(0,-2)),(true,(1,-2)),(false,(1,-2)),(true,(2,-2)),(false,(2,-3))]],
  [(0,0),(5,-7)],
  [(0,1),(0,2),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(3,-6),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(4,-6),(4,-5),(4,-4),(5,-6),(5,-5),(6,-7),(6,-6)]⟩
def p22 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(0,1)),(false,(0,1)),(true,(0,2)),(false,(0,2)),(true,(0,3)),(false,(0,3)),(true,(1,3)),(false,(1,2))],![(false,(0,0)),(true,(0,0)),(false,(0,-1)),(true,(0,-1)),(false,(0,-2)),(true,(0,-2)),(false,(0,-3)),(true,(0,-3)),(false,(-1,-3))],![(false,(0,0)),(true,(1,0)),(false,(1,0)),(true,(2,0)),(false,(2,0)),(true,(2,1)),(false,(1,1)),(true,(1,2)),(false,(1,2))]],
  [(0,0),(2,5)],
  [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)]⟩
def p23 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(0,1)),(false,(-1,1)),(true,(-1,2)),(false,(-2,2)),(true,(-2,3)),(false,(-3,3)),(true,(-3,3)),(false,(-3,2))],![(false,(0,0)),(true,(1,0)),(false,(1,-1)),(true,(2,-1)),(false,(2,-2)),(true,(3,-2)),(false,(3,-3)),(true,(4,-3)),(false,(4,-3))],![(false,(0,0)),(true,(0,0)),(false,(-1,0)),(true,(-1,0)),(false,(-2,0)),(true,(-2,1)),(false,(-2,1)),(true,(-2,2)),(false,(-3,2))]],
  [(0,0),(7,-5)],
  [(0,1),(0,2),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(2,-3),(2,-2),(2,-1),(2,0),(3,-3),(3,-2),(3,-1),(4,-4),(4,-3),(4,-2),(5,-5),(5,-4),(5,-3),(6,-6),(6,-5),(6,-4),(6,-3),(7,-6)]⟩
def p24 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(0,0)),(false,(-1,0)),(true,(-1,0)),(false,(-2,0)),(true,(-2,0)),(false,(-3,0)),(true,(-3,1)),(false,(-3,1))],![(false,(0,0)),(true,(1,0)),(false,(1,0)),(true,(2,0)),(false,(2,-1)),(true,(2,-1)),(false,(2,-2)),(true,(2,-2)),(false,(2,-3))],![(false,(0,0)),(true,(0,1)),(false,(-1,1)),(true,(-1,2)),(false,(-2,2)),(true,(-2,2)),(false,(-2,1)),(true,(-2,1)),(false,(-3,1))]],
  [(0,0),(5,-4)],
  [(0,1),(0,2),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(4,-5),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(5,-3),(5,-2),(5,-1)]⟩
def p25 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(0,0)),(false,(0,-1)),(true,(0,-1)),(false,(0,-2)),(true,(0,-2)),(false,(0,-3)),(true,(1,-3)),(false,(1,-3))],![(false,(0,0)),(true,(0,1)),(false,(0,1)),(true,(0,2)),(false,(-1,2)),(true,(-1,2)),(false,(-2,2)),(true,(-2,2)),(false,(-3,2))],![(false,(0,0)),(true,(1,0)),(false,(1,-1)),(true,(2,-1)),(false,(2,-2)),(true,(2,-2)),(false,(1,-2)),(true,(1,-2)),(false,(1,-3))]],
  [(0,0),(4,-5)],
  [(0,1),(0,2),(0,3),(0,4),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(4,-4),(4,-3),(5,-4)]⟩
def p26 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(1,0)),(false,(1,0)),(true,(2,0)),(false,(2,0)),(true,(3,0)),(false,(3,0)),(true,(3,1)),(false,(2,1))],![(false,(0,0)),(true,(0,0)),(false,(-1,0)),(true,(-1,0)),(false,(-1,-1)),(true,(0,-1)),(false,(0,-2)),(true,(1,-2)),(false,(1,-3))],![(false,(0,0)),(true,(0,1)),(false,(0,1)),(true,(0,2)),(false,(0,2)),(true,(1,2)),(false,(1,1)),(true,(2,1)),(false,(2,1))]],
  [(0,0),(1,4)],
  [(0,1),(0,2),(0,3),(0,4),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(4,0),(4,1)]⟩
def p27 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(1,0)),(false,(1,-1)),(true,(2,-1)),(false,(2,-2)),(true,(3,-2)),(false,(3,-3)),(true,(3,-3)),(false,(2,-3))],![(false,(0,0)),(true,(0,1)),(false,(-1,1)),(true,(-1,2)),(false,(-1,2)),(true,(0,2)),(false,(0,2)),(true,(1,2)),(false,(1,2))],![(false,(0,0)),(true,(0,0)),(false,(0,-1)),(true,(0,-1)),(false,(0,-2)),(true,(1,-2)),(false,(1,-2)),(true,(2,-2)),(false,(2,-3))]],
  [(0,0),(1,-5)],
  [(0,1),(0,2),(0,3),(0,4),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-5),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-5),(3,-4),(3,-3),(3,-2),(3,-1),(4,-5),(4,-4)]⟩
def p28 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(0,1)),(false,(0,1)),(true,(0,2)),(false,(0,2)),(true,(0,3)),(false,(0,3)),(true,(1,3)),(false,(1,2))],![(false,(0,0)),(true,(0,0)),(false,(0,-1)),(true,(0,-1)),(false,(-1,-1)),(true,(-1,0)),(false,(-2,0)),(true,(-2,1)),(false,(-3,1))],![(false,(0,0)),(true,(1,0)),(false,(1,0)),(true,(2,0)),(false,(2,0)),(true,(2,1)),(false,(1,1)),(true,(1,2)),(false,(1,2))]],
  [(0,0),(4,1)],
  [(0,1),(0,2),(0,3),(0,4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(4,-1),(4,0),(5,-1)]⟩
def p29 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(0,1)),(false,(-1,1)),(true,(-1,2)),(false,(-2,2)),(true,(-2,3)),(false,(-3,3)),(true,(-3,3)),(false,(-3,2))],![(false,(0,0)),(true,(1,0)),(false,(1,-1)),(true,(2,-1)),(false,(2,-1)),(true,(2,0)),(false,(2,0)),(true,(2,1)),(false,(2,1))],![(false,(0,0)),(true,(0,0)),(false,(-1,0)),(true,(-1,0)),(false,(-2,0)),(true,(-2,1)),(false,(-2,1)),(true,(-2,2)),(false,(-3,2))]],
  [(0,0),(5,-1)],
  [(0,1),(0,2),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(5,-4),(5,-3),(5,-2)]⟩
def p30 : Patch := ⟨8,
  ![![(false,(0,0)),(true,(0,0)),(false,(-1,0)),(true,(-1,0)),(false,(-2,0)),(true,(-2,0)),(false,(-2,-1)),(true,(-2,-1)),(false,(-3,-1))],![(false,(0,0)),(true,(1,0)),(false,(1,0)),(true,(1,1)),(false,(1,1)),(true,(2,1)),(false,(2,0)),(true,(2,0)),(false,(2,-1))],![(false,(0,0)),(true,(0,1)),(false,(-1,1)),(true,(-1,2)),(false,(-2,2)),(true,(-2,3)),(false,(-3,3)),(true,(-3,4)),(false,(-3,4))]],
  [(0,0),(0,5),(5,0)],
  [(0,1),(0,2),(0,3),(0,4),(1,-5),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1),(4,2),(5,-4),(5,-3),(5,1)]⟩
def atlas : Fin 31 → Patch := ![p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30]
end OrdinaryCyclicTheta

namespace OrdinaryCyclicTheta
open SmallHNF
inductive Choice where
  | bad (i : Fin 15)
  | use (i : Fin 31)
  deriving Inhabited
def smallPlan (A B C : ℕ) : Choice :=
  match A,C with
  | 1,1 => ([.bad 0] : List Choice)[B]!
  | 1,3 => ([.bad 1] : List Choice)[B]!
  | 1,5 => ([.bad 5] : List Choice)[B]!
  | 1,7 => ([.bad 5] : List Choice)[B]!
  | 1,9 => ([.bad 5] : List Choice)[B]!
  | 1,11 => ([.bad 5] : List Choice)[B]!
  | 1,13 => ([.bad 5] : List Choice)[B]!
  | 1,15 => ([.bad 5] : List Choice)[B]!
  | 1,17 => ([.bad 5] : List Choice)[B]!
  | 1,19 => ([.bad 5] : List Choice)[B]!
  | 1,21 => ([.bad 5] : List Choice)[B]!
  | 1,23 => ([.bad 5] : List Choice)[B]!
  | 1,25 => ([.bad 5] : List Choice)[B]!
  | 3,1 => ([.bad 0,.bad 1,.bad 1] : List Choice)[B]!
  | 3,3 => ([.bad 1,.bad 8,.bad 2] : List Choice)[B]!
  | 3,5 => ([.bad 14,.bad 14,.bad 14] : List Choice)[B]!
  | 3,7 => ([.bad 14,.bad 14,.bad 14] : List Choice)[B]!
  | 5,1 => ([.bad 0,.bad 6,.bad 3,.bad 2,.bad 4] : List Choice)[B]!
  | 5,3 => ([.bad 1,.use 10,.bad 11,.bad 8,.bad 2] : List Choice)[B]!
  | 5,5 => ([.use 30,.use 25,.use 14,.use 12,.use 27] : List Choice)[B]!
  | 7,1 => ([.bad 0,.bad 6,.bad 2,.bad 3,.bad 7,.bad 9,.bad 4] : List Choice)[B]!
  | 7,3 => ([.bad 1,.use 11,.use 16,.use 10,.bad 11,.bad 8,.bad 2] : List Choice)[B]!
  | 9,1 => ([.bad 0,.bad 6,.bad 10,.bad 1,.bad 3,.bad 7,.bad 1,.bad 9,.bad 4] : List Choice)[B]!
  | 11,1 => ([.bad 0,.bad 6,.bad 10,.bad 8,.bad 12,.bad 3,.bad 7,.bad 2,.bad 13,.bad 9,.bad 4] : List Choice)[B]!
  | 13,1 => ([.bad 0,.bad 6,.bad 10,.use 18,.bad 2,.bad 12,.bad 3,.bad 7,.bad 8,.use 19,.bad 13,.bad 9,.bad 4] : List Choice)[B]!
  | 15,1 => ([.bad 0,.bad 6,.bad 10,.use 8,.bad 11,.bad 1,.bad 12,.bad 3,.bad 7,.bad 11,.bad 1,.use 6,.bad 13,.bad 9,.bad 4] : List Choice)[B]!
  | 17,1 => ([.bad 0,.bad 6,.bad 10,.use 9,.use 6,.bad 8,.use 11,.bad 12,.bad 3,.bad 7,.use 10,.bad 2,.use 8,.use 7,.bad 13,.bad 9,.bad 4] : List Choice)[B]!
  | 19,1 => ([.bad 0,.bad 6,.bad 10,.use 9,.use 8,.use 10,.bad 2,.use 13,.bad 12,.bad 3,.bad 7,.use 12,.bad 8,.use 11,.use 6,.use 7,.bad 13,.bad 9,.bad 4] : List Choice)[B]!
  | 21,1 => ([.bad 0,.bad 6,.bad 10,.use 9,.use 24,.use 6,.bad 11,.bad 1,.use 12,.bad 12,.bad 3,.bad 7,.use 14,.bad 11,.bad 1,.use 8,.use 25,.use 7,.bad 13,.bad 9,.bad 4] : List Choice)[B]!
  | 23,1 => ([.bad 0,.bad 6,.bad 10,.use 9,.use 14,.use 8,.use 16,.bad 8,.use 11,.use 13,.bad 12,.bad 3,.bad 7,.use 15,.use 10,.bad 2,.use 17,.use 6,.use 12,.use 7,.bad 13,.bad 9,.bad 4] : List Choice)[B]!
  | 25,1 => ([.bad 0,.bad 6,.bad 10,.use 9,.use 28,.use 24,.use 6,.use 10,.bad 2,.use 17,.use 13,.bad 12,.bad 3,.bad 7,.use 15,.use 16,.bad 8,.use 11,.use 8,.use 26,.use 29,.use 7,.bad 13,.bad 9,.bad 4] : List Choice)[B]!
  | _,_ => .bad 0

def covers (A B C : ℕ) (ch : Choice) : Prop :=
  match ch with
  | .bad i => SmallHNF.project A B C keys[i.val]! = (0,0)
  | .use i =>
    (∀ z ∈ (atlas i).equal, SmallHNF.project A B C z=(0,0)) ∧
    (∀ z ∈ (atlas i).distinct, SmallHNF.project A B C z≠(0,0))
instance (A B C : ℕ) (ch : Choice) : Decidable (covers A B C ch) := by
  cases ch <;> unfold covers <;> infer_instance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem small_table : ∀ a b c : Fin 26, a.val%2=1 → c.val%2=1 → b.val<a.val →
    a.val*c.val≤25 → covers a.val b.val c.val (smallPlan a.val b.val c.val) := by
  intro a
  fin_cases a <;> decide +kernel
end OrdinaryCyclicTheta

namespace OrdinaryCyclicTheta
open SevenFaceLattice (det)
def alternate (w : V2) : Fin 31 :=
  match w with
  | (0,5) => 1
  | (1,-5) => 4
  | (1,-4) => 6
  | (1,3) => 11
  | (1,4) => 1
  | (2,-5) => 12
  | (2,3) => 17
  | (3,-5) => 14
  | (3,-4) => 8
  | (3,1) => 9
  | (3,2) => 15
  | (4,-5) => 5
  | (4,-3) => 10
  | (4,-1) => 7
  | (5,-5) => 3
  | (5,-4) => 3
  | (5,-3) => 16
  | (5,-2) => 13
  | (5,-1) => 2
  | _ => 0
def multipleCoeff (w z : V2) : ℤ := if w.1=0 then z.2/w.2 else z.1/w.1
def immediate (w : V2) : Prop :=
  w∈keys ∨ (∃ z∈keys, w=(2:ℤ) • z ∨ w=(4:ℤ) • z)
instance (w : V2) : Decidable (immediate w) := by unfold immediate; infer_instance
def escapes (w z : V2) : Prop :=
  z∈keys ∨ (w-z)∈keys ∨ (det w z ≠ 0 ∧ (det w z).natAbs≤25)
instance (w z : V2) : Decidable (escapes w z) := by unfold escapes; infer_instance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem wide_table : ∀ w∈p0.distinct, immediate w ∨
    ((∀ z∈(atlas (alternate w)).equal,z=multipleCoeff w z • w) ∧
      ∀ z∈(atlas (alternate w)).distinct,escapes w z) := by decide +kernel
end OrdinaryCyclicTheta

namespace OrdinaryCyclicTheta
open SmallHNF
variable {Q : Type*} [AddCommGroup Q] [Finite Q]

def Clean (a b : Q) : Prop := ∀ w∈keys, marking a b w≠0

omit [Finite Q] in
private theorem double_ne (odd : Odd (Nat.card Q)) {q : Q} (nz : q≠0) : (2:ℤ) • q ≠ 0 := by
  intro h
  have dv : addOrderOf q ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by simpa only [two_zsmul,two_nsmul] using h)
  have od := odd.of_dvd_nat (addOrderOf_dvd_natCard q)
  have small := Nat.le_of_dvd (by decide : 0<2) dv
  have one : addOrderOf q=1 := by obtain ⟨k,hk⟩:=od; omega
  exact nz (AddMonoid.addOrderOf_eq_one_iff.mp one)

omit [Finite Q] in
private theorem chosen_large (a b : Q) (odd : Odd (Nat.card Q)) (clean : Clean a b)
    (gen : AddSubgroup.closure ({a,b} : Set Q)=⊤) (large : 25<Nat.card Q) :
    ∃ i, Valid (marking a b) (atlas i) := by
  let f:=marking a b
  by_cases ok : ∀ z∈p0.distinct, f z≠0
  · refine ⟨0,?_,ok⟩
    intro z hz
    have : z=(0,0) := by simpa [atlas,p0] using hz
    rw [this]; exact map_zero _
  push Not at ok
  obtain ⟨w,hw,zero⟩:=ok
  rcases wide_table w hw with immediate|⟨ends,away⟩
  · rcases immediate with bad|⟨z,hz,twice|four⟩
    · exact (clean _ bad zero).elim
    · rw [twice,map_zsmul] at zero
      exact (double_ne odd (clean _ hz) zero).elim
    · rw [four,show (4:ℤ)=2*2 by decide,mul_zsmul,map_zsmul,map_zsmul] at zero
      exact (double_ne odd (double_ne odd (clean _ hz)) zero).elim
  refine ⟨alternate w,?_,?_⟩
  · intro z hz
    rw [ends z hz,map_zsmul,zero,zsmul_zero]
  · intro z hz collide
    rcases away z hz with bad|bad|⟨nz,small⟩
    · exact clean _ bad collide
    · apply clean _ bad
      rw [map_sub,zero,collide,sub_zero]
    have surj : Function.Surjective (SevenFaceLattice.mark a b) := by
      intro g
      obtain ⟨i,j,h⟩ := AddSubgroup.mem_closure_pair.mp (gen ▸ AddSubgroup.mem_top g)
      exact ⟨![i,j],h⟩
    have dv := SevenFaceLattice.card_dvd_det (SevenFaceLattice.mark a b) surj w z zero collide
    exact (not_lt_of_ge ((Nat.le_of_dvd (Int.natAbs_pos.mpr nz) dv).trans small)) large

private theorem chosen_small (a b : Q) (odd : Odd (Nat.card Q)) (clean : Clean a b)
    (gen : AddSubgroup.closure ({a,b} : Set Q)=⊤) (size : Nat.card Q≤25) :
    ∃ i, Valid (marking a b) (atlas i) := by
  obtain ⟨A,B,C,F⟩:=exists_frame a b gen
  have area:=F.area
  have ap:=F.width
  have cp:=F.height
  have ba:=F.shear
  have al : A≤25 := (Nat.le_mul_of_pos_right A cp).trans (area ▸ size)
  have cl : C≤25 := (Nat.le_mul_of_pos_left C ap).trans (area ▸ size)
  have ao : Odd A := odd.of_dvd_nat (area ▸ dvd_mul_right A C)
  have co : Odd C := odd.of_dvd_nat (area ▸ dvd_mul_left C A)
  have card := small_table (⟨A,by omega⟩ : Fin 26) (⟨B,by omega⟩ : Fin 26) (⟨C,by omega⟩ : Fin 26)
    (Nat.odd_iff.mp ao) (Nat.odd_iff.mp co) ba (area ▸ size)
  have zero (z : V2) : marking a b z=0 ↔ SmallHNF.project A B C z=(0,0) := by
    rw [show (0:Q)=eval a b (0,0) by simp [eval]]
    change eval a b z=eval a b (0,0) ↔ _
    simpa [SmallHNF.project] using eval_eq_iff F z (0,0)
  cases h : smallPlan A B C with
  | bad i =>
    change covers A B C (smallPlan A B C) at card
    rw [h] at card
    have hi : i.val<keys.length := i.isLt
    exact (clean _ (by simpa only [getElem!_pos keys i.val hi] using List.getElem_mem hi)
      ((zero _).mpr card)).elim
  | use i =>
    change covers A B C (smallPlan A B C) at card
    rw [h] at card
    exact ⟨i,fun z hz => (zero z).mpr (card.1 z hz),fun z hz eq => card.2 z hz ((zero z).mp eq)⟩

theorem select_patch (a b : Q) (odd : Odd (Nat.card Q)) (clean : Clean a b)
    (gen : AddSubgroup.closure ({a,b} : Set Q)=⊤) : ∃ i, Valid (marking a b) (atlas i) := by
  by_cases small : Nat.card Q≤25
  · exact chosen_small a b odd clean gen small
  · exact chosen_large a b odd clean gen (by omega)

end OrdinaryCyclicTheta

namespace OrdinaryCyclicTheta
open SevenFaceLattice (directions)
open SmallHNF

def basis (k : Fin 6) : V2 × V2 := directions (1,0) (0,1) k

private theorem key_cases : ∀ w∈keys, w=(1,0) ∨ w=(0,1) ∨ w=(1,-1) ∨
    ∃ k : Fin 6, let u:=(basis k).1; let v:=(basis k).2
      w=canon ((2:ℤ) • u-v) ∨ w=canon ((3:ℤ) • u-v) ∨ w=canon ((3:ℤ) • u) := by
  decide +kernel

def ExceptionalA {Q : Type*} [AddCommGroup Q] (a b : Q) : Prop :=
  ∃ k : Fin 6, let u:=(directions a b k).1; let v:=(directions a b k).2
    (2:ℤ) • u=v ∨ (3:ℤ) • u=v ∨ addOrderOf u=3

theorem clean_of_ordinary {Q : Type*} [AddCommGroup Q] (a b : Q)
    (a0 : a≠0) (b0 : b≠0) (ab : a≠b) (ordinary : ¬ExceptionalA a b) : Clean a b := by
  let f:=marking a b
  have basis_map (k : Fin 6) :
      (f (basis k).1,f (basis k).2)=directions a b k := by
    fin_cases k <;> simp [f,basis,directions,marking,eval] <;> abel
  have nz (k : Fin 6) : (directions a b k).1≠0 := by
    fin_cases k <;> simp [directions, a0, b0, sub_eq_zero, ab, ab.symm]
  intro w hw zero
  rcases key_cases w hw with rfl|rfl|rfl|⟨k,h|h|h⟩
  · exact a0 (by simpa [marking,eval] using zero)
  · exact b0 (by simpa [marking,eval] using zero)
  · exact ab (sub_eq_zero.mp (by simpa [marking,eval,sub_eq_add_neg] using zero))
  all_goals
    have z := (canon_zero f _).mp (h ▸ zero)
    have bu := congrArg Prod.fst (basis_map k)
    have bv := congrArg Prod.snd (basis_map k)
    change f (basis k).1=(directions a b k).1 at bu
    change f (basis k).2=(directions a b k).2 at bv
    apply ordinary
    refine ⟨k,?_⟩
  · rw [map_sub,map_zsmul,bu,bv,sub_eq_zero] at z
    exact .inl z
  · rw [map_sub,map_zsmul,bu,bv,sub_eq_zero] at z
    exact .inr (.inl z)
  · rw [map_zsmul,bu] at z
    apply Or.inr ∘ Or.inr
    apply addOrderOf_eq_prime ?_ (nz k)
    simpa only [ofNat_zsmul] using z

def reorder {H : Type*} [Group H] (a b : H) : Fin 6 → H × H :=
  ![(a,b),(b,a),(a⁻¹,b/a),(b/a,a⁻¹),(b⁻¹,a/b),(a/b,b⁻¹)]

theorem reorder_generates {H : Type*} [Group H] (a b : H)
    (gen : Subgroup.closure ({a,b} : Set H)=⊤) (k : Fin 6) :
    Subgroup.closure ({(reorder a b k).1,(reorder a b k).2} : Set H)=⊤ := by
  let K:=Subgroup.closure ({(reorder a b k).1,(reorder a b k).2} : Set H)
  have hx : (reorder a b k).1 ∈ K := Subgroup.subset_closure (by simp)
  have hy : (reorder a b k).2 ∈ K := Subgroup.subset_closure (by simp)
  have recover (x y : H) (invx : x⁻¹∈K) (diff : y/x∈K) : x∈K ∧ y∈K := by
    have h : x∈K := by simpa only [inv_inv] using K.inv_mem invx
    exact ⟨h,by simpa only [div_mul_cancel] using K.mul_mem diff h⟩
  change K=⊤
  apply top_unique
  rw [←gen,Subgroup.closure_le]
  have both : a∈K ∧ b∈K := by
    fin_cases k
    · exact ⟨hx,hy⟩
    · exact ⟨hy,hx⟩
    · exact recover a b hx hy
    · exact recover a b hy hx
    · exact (recover b a hx hy).symm
    · exact (recover b a hy hx).symm
  simpa only [Set.insert_subset_iff,Set.singleton_subset_iff,SetLike.mem_coe] using both

theorem generator_of_reordered_power {H : Type*} [Group H] (a b : H)
    (gen : Subgroup.closure ({a,b} : Set H)=⊤) (k : Fin 6) {n : ℕ}
    (power : (reorder a b k).1^n=(reorder a b k).2) :
    Subgroup.zpowers (reorder a b k).1=⊤ := by
  apply top_unique
  rw [←reorder_generates a b gen k,Subgroup.closure_le]
  simp only [Set.insert_subset_iff,Set.singleton_subset_iff,SetLike.mem_coe]
  exact ⟨Subgroup.mem_zpowers _,power ▸ (Subgroup.zpowers _).pow_mem (Subgroup.mem_zpowers _) n⟩

def Exceptional {H : Type*} [Group H] (a b : H) : Prop :=
  ∃ k : Fin 6, let u:=(reorder a b k).1; let v:=(reorder a b k).2
    u^2=v ∨ u^3=v ∨ orderOf u=3

theorem exceptional_of_add {H : Type*} [CommGroup H] {a b : H}
    (h : ExceptionalA (Additive.ofMul a) (Additive.ofMul b)) : Exceptional a b := by
  obtain ⟨k,h⟩:=h
  refine ⟨k,?_⟩
  let u:=(directions (Additive.ofMul a) (Additive.ofMul b) k).1
  let v:=(directions (Additive.ofMul a) (Additive.ofMul b) k).2
  have pu : u.toMul=(reorder a b k).1 := by fin_cases k <;> rfl
  have pv : v.toMul=(reorder a b k).2 := by fin_cases k <;> rfl
  change (reorder a b k).1^2=(reorder a b k).2 ∨ (reorder a b k).1^3=(reorder a b k).2 ∨ _
  rw [←pu,←pv]
  change (2:ℤ) • u=v ∨ (3:ℤ) • u=v ∨ addOrderOf u=3 at h
  rcases h with h|h|h
  · left
    have hz:=congrArg Additive.toMul h
    change u.toMul^(2:ℤ)=v.toMul at hz
    simpa using hz
  · right; left
    have hz:=congrArg Additive.toMul h
    change u.toMul^(3:ℤ)=v.toMul at hz
    simpa using hz
  · exact .inr (.inr h)

end OrdinaryCyclicTheta

namespace MatchingRelabel
open MetabelianRegular OrdinaryCyclicTheta
variable {G H : Type*} [Group G] [Group H]

def Mark (a b z : G) : Prop := z=1 ∨ z=a ∨ z=b

def Remark (a b c d r : G) : Prop := ∀ z, Mark c d z ↔ Mark a b (z*r)

def translate (r : G) : (Bool × G) ≃ (Bool × G) where
  toFun v := (v.1, if v.1 then v.2*r else v.2)
  invFun v := (v.1, if v.1 then v.2*r⁻¹ else v.2)
  left_inv := by rintro ⟨s,x⟩; cases s <;> simp
  right_inv := by rintro ⟨s,x⟩; cases s <;> simp

private lemma adj_mark (a b x y : G) :
    (rightMatching a b).Adj (false,x) (true,y) ↔ Mark a b (x⁻¹*y) := by
  rw [rightMatching_adj]
  simp [Mark, inv_mul_eq_iff_eq_mul]

def iso {a b c d r : G} (h : Remark a b c d r) : rightMatching c d ≃g rightMatching a b := by
  have front (x y : G) : (rightMatching a b).Adj (false,x) (true,y*r) ↔
      (rightMatching c d).Adj (false,x) (true,y) := by
    rw [adj_mark,adj_mark,← mul_assoc]
    exact (h _).symm
  refine ⟨translate r,?_⟩
  rintro ⟨s,x⟩ ⟨t,y⟩
  cases s <;> cases t
  · simp [translate,rightMatching,SimpleGraph.fromRel_adj]
  · exact front x y
  · exact ⟨fun e => ((front y x).mp e.symm).symm, fun e => ((front y x).mpr e.symm).symm⟩
  · simp [translate,rightMatching,SimpleGraph.fromRel_adj]

def mapTheta {U W : Type*} {A : SimpleGraph U} {B : SimpleGraph W} (e : A ≃g B)
    {n : ℕ} (T : EqualArms.Theta A n) : EqualArms.Theta B n where
  src := e T.src
  dst := e T.dst
  endpoints := e.injective.ne T.endpoints
  arm c i := e (T.arm c i)
  head c := congrArg e (T.head c)
  last c := congrArg e (T.last c)
  step c i hi := e.map_rel_iff.mpr (T.step c i hi)
  avoid c i lo hi := ⟨e.injective.ne (T.avoid c i lo hi).1, e.injective.ne (T.avoid c i lo hi).2⟩
  distinct c d i j lo hi low high eq := T.distinct c d i j lo hi low high (e.injective eq)

lemma changeTheta {a b c d r : G} (h : Remark a b c d r) {n : ℕ}
    (T : Nonempty (EqualArms.Theta (rightMatching c d) n)) :
    Nonempty (EqualArms.Theta (rightMatching a b) n) := T.map (mapTheta (iso h))

def origin (a b : G) : Fin 6 → G := ![1,1,a,a,b,b]

theorem reorder_remark (a b : G) (k : Fin 6) :
    Remark a b (reorder a b k).1 (reorder a b k).2 (origin a b k) := by
  fin_cases k <;> intro z <;> simp [Mark, reorder, origin, div_eq_mul_inv, ← eq_mul_inv_iff_mul_eq] <;> tauto

theorem reorderTheta (a b : G) (k : Fin 6) {n : ℕ}
    (T : Nonempty (EqualArms.Theta (rightMatching (reorder a b k).1 (reorder a b k).2) n)) :
    Nonempty (EqualArms.Theta (rightMatching a b) n) := changeTheta (reorder_remark a b k) T

end MatchingRelabel

namespace OrdinaryCyclicTheta
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem geometry (i : Fin 31) : Shape (atlas i) := by
  fin_cases i <;> decide +kernel
end OrdinaryCyclicTheta

namespace OrdinaryCyclicTheta
open EqualArms MetabelianRegular
universe u v

theorem marked {H : Type u} [CommGroup H] [Finite H] (a b : H) (odd : Odd (Nat.card H))
    (gen : Subgroup.closure ({a,b} : Set H)=⊤) (a1 : a≠1) (b1 : b≠1) (ab : a≠b) :
    Exceptional a b ∨ Nonempty (Theta (rightMatching a b) 8) ∨ Nonempty (Theta (rightMatching a b) 16) := by
  by_cases exc : Exceptional a b
  · exact .inl exc
  right
  let x:=Additive.ofMul a
  let y:=Additive.ofMul b
  have agen : AddSubgroup.closure ({x,y} : Set (Additive H))=⊤ := by
    apply top_unique
    intro z _
    obtain ⟨i,j,rep⟩ := Subgroup.mem_closure_pair.mp (gen ▸ Subgroup.mem_top z.toMul)
    exact AddSubgroup.mem_closure_pair.mpr ⟨i,j,congrArg Additive.ofMul rep⟩
  have clean := clean_of_ordinary x y a1 b1 ab (fun h => exc (exceptional_of_add h))
  obtain ⟨i,valid⟩:=select_patch x y odd clean agen
  exact of_patch x y _ (geometry i) valid

theorem ordinary_theta {H : Type u} [CommGroup H] [Finite H] (a b : H) (odd : Odd (Nat.card H))
    (gen : Subgroup.closure ({a,b} : Set H)=⊤) (a1 : a≠1) (b1 : b≠1) (ab : a≠b)
    (ordinary : ¬Exceptional a b) :
    Nonempty (Theta (rightMatching a b) 8) ∨ Nonempty (Theta (rightMatching a b) 16) :=
  (marked a b odd gen a1 b1 ab).resolve_left ordinary

theorem map_reorder {M H : Type*} [Group M] [Group H] (f : M →* H) (a b : M) (k : Fin 6) :
    (f (reorder a b k).1,f (reorder a b k).2)=reorder (f a) (f b) k := by
  fin_cases k <;> simp [reorder]

end OrdinaryCyclicTheta

namespace OddCyclicShort
open EqualArms MetabelianRegular OddDyadicSize OrdinaryCyclicTheta
universe u v

def EightOrSixteen {V : Type*} (B : SimpleGraph V) : Prop :=
  Nonempty (Theta B 8) ∨ Nonempty (Theta B 16)

theorem quotient_short {G H : Type} [Group G] [Group H] [Nontrivial H]
    (q : G →* H) (onto : Function.Surjective q) (a b : G)
    (arms : EightOrSixteen (rightMatching (q a) (q b))) : OddDyadicSize.Short.{0,0} a b := by
  refine ⟨H,inferInstance,inferInstance,q,onto,?_⟩
  rcases arms with h|h
  · exact ⟨3,by decide,by decide,h⟩
  · exact ⟨4,by decide,by decide,h⟩

theorem ordinary_short {M : Type} [Group M] [Finite M] (odd : Odd (Nat.card M))
    (a b : M) (gen : Subgroup.closure ({a,b} : Set M)=⊤)
    (a1 : Abelianization.of a≠1) (b1 : Abelianization.of b≠1)
    (ab : Abelianization.of a≠Abelianization.of b)
    (ordinary : ¬Exceptional (Abelianization.of a) (Abelianization.of b)) :
    OddDyadicSize.Short.{0,0} a b := by
  let q : M →* Abelianization M := Abelianization.of
  have sur : Function.Surjective q := QuotientGroup.mk'_surjective _
  let _ : Nontrivial (Abelianization M) := ⟨⟨q a,1,a1⟩⟩
  have qgen : Subgroup.closure ({q a,q b} : Set (Abelianization M))=⊤ := by
    rw [← Set.image_pair,← MonoidHom.map_closure,gen,← MonoidHom.range_eq_map]
    exact q.range_eq_top_of_surjective sur
  exact quotient_short q sur a b (ordinary_theta (q a) (q b)
    (odd.of_dvd_nat (commutator M).card_quotient_dvd_card) qgen a1 b1 ab ordinary)

theorem reorder_arms {M : Type*} [Group M] (a b : M) (k : Fin 6)
    (arms : EightOrSixteen (rightMatching (reorder a b k).1 (reorder a b k).2)) :
    EightOrSixteen (rightMatching a b) :=
  arms.imp (MatchingRelabel.reorderTheta a b k) (MatchingRelabel.reorderTheta a b k)

end OddCyclicShort

namespace OddCyclicShort
open Subgroup
variable {H : Type*} [CommGroup H] [Finite H]

theorem third_offsets {g x : H} (gen : zpowers g=⊤) (ord : orderOf x=3) :
    let d := orderOf g / 3
    orderOf g=3*d ∧ (x=g^d ∨ x=g^(2*d)) := by
  classical
  have mem : x∈zpowers g := gen ▸ mem_top _
  have dvd : 3 ∣ orderOf g := ord ▸ orderOf_dvd_of_mem_zpowers mem
  obtain ⟨d,hd⟩ := dvd
  simp only [hd,Nat.mul_div_cancel_left _ (by decide : 0<3),true_and]
  obtain ⟨n,hn,pow⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp mem)
  have small := Finset.mem_range.mp hn
  have xp : x^3=1 := ord ▸ pow_orderOf_eq_one x
  have dn : orderOf g ∣ n*3 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_mul,pow,xp])
  obtain ⟨k,hk⟩ := dn
  have klt : k<3 := by
    by_contra! big
    have := Nat.mul_le_mul_left (orderOf g) big
    omega
  have nn : n≠0 := by
    rintro rfl
    simp only [pow_zero] at pow
    simp [←pow] at ord
  have cases : k=1 ∨ k=2 := by
    by_cases z : k=0
    · simp [z] at hk
      omega
    · omega
  rcases cases with rfl|rfl
  · exact .inl (by rw [←pow]; congr 1; omega)
  · exact .inr (by rw [←pow]; congr 1; omega)

private theorem third_or_inverse [IsCyclic H] {x z : H}
    (hx : orderOf x=3) (hz : orderOf z=3) : x=z ∨ x=z⁻¹ := by
  obtain ⟨g,gen⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic H)
  obtain ⟨hm,xx⟩ := third_offsets gen hx
  obtain ⟨_,zz⟩ := third_offsets gen hz
  let d:=orderOf g/3
  have inv : g^(2*d)=(g^d)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [←pow_add,show 2*d+d=orderOf g by dsimp [d]; omega,pow_orderOf_eq_one]
  change x=g^d ∨ x=g^(2*d) at xx
  change z=g^d ∨ z=g^(2*d) at zz
  rw [inv] at xx zz
  rcases xx with rfl|rfl <;> rcases zz with rfl|rfl <;> simp

theorem third_generator [IsCyclic H] (x y : H) (gen : closure ({x,y} : Set H)=⊤)
    (hx : orderOf x=3) : zpowers y=⊤ ∨ zpowers (y/x)=⊤ := by
  have close {K : Subgroup H} (mx : x∈K) (my : y∈K) : K=⊤ := by
    apply top_unique
    rw [←gen,closure_le]
    simpa only [Set.insert_subset_iff,Set.singleton_subset_iff,SetLike.mem_coe] using And.intro mx my
  by_cases dvd : 3∣orderOf y
  · left
    let z:= y^(orderOf y / 3)
    have mz : z∈zpowers y := (zpowers y).pow_mem (mem_zpowers y) _
    have hz : orderOf z=3 := orderOf_pow_orderOf_div (orderOf_pos y).ne' dvd
    apply close _ (mem_zpowers y)
    rcases third_or_inverse hx hz with h|h
    · exact h ▸ mz
    · exact h ▸ (zpowers y).inv_mem mz
  · right
    let K:=zpowers (y/x)
    have hm : y/x∈K := mem_zpowers _
    have hy3 : y^3∈K := by
      have xp : x^3=1 := hx ▸ pow_orderOf_eq_one x
      simpa only [div_pow,xp,div_one] using K.pow_mem hm 3
    obtain ⟨n,hn⟩ := exists_pow_eq_self_of_coprime (x:=y)
      ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr dvd)
    have hy : y∈K := hn ▸ K.pow_mem hy3 n
    exact close (by simpa using K.div_mem hy hm) hy

end OddCyclicShort

/- Repeated offsets. Separate the generic rows and the exceptional scalar actions. -/
namespace NecklaceTheta.three
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 47 16 3 2 where
  side := AtlasIndices.shores16
  ht := ![0,2,0,0,1,1,1,0,0,2,2,2,0,0,0,2,2,0,0,1,1,1,0,0,2,2,2,0,0,0,2,2,1,1,2,2,2,1,1,1,2,2,2,1,1,0,0]
  lamp := ![![0,0],![0,1],![0,0],![-1,0],![-1,0],![-1,0],![-1,1],![-1,1],![-1,1],![-1,1],![-2,0],![-2,0],![-2,0],![-2,0],![-1,0],![-1,0],![-1,0],![1,0],![1,0],![1,0],![1,0],![1,1],![1,1],![1,1],![1,1],![1,1],![2,2],![2,2],![1,2],![1,2],![1,2],![0,1],![0,0],![0,-1],![0,-1],![0,-1],![-1,-2],![-1,-2],![-1,-1],![-1,-1],![-1,-1],![0,0],![0,0],![0,0],![0,1],![0,1],![0,1]]
  route := AtlasIndices.route16
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 3 → Fin 2 → ℤ := ![![1,0],![0,1],![-1,-1]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 17 → Fin 2 → ℤ := ![![0,1],![0,2],![1,-2],![1,-1],![1,0],![1,1],![1,2],![1,3],![2,-1],![2,0],![2,1],![2,2],![2,3],![3,0],![3,1],![3,2],![4,2]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 3 0 0 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] [Nontrivial R] {x : R}

omit [Nontrivial R] in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (cyclo : x^2+x+1=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))=x^0
    push_cast; ring
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))=x^1
    push_cast; ring
  · change (((-1:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R)))=x^2
    push_cast; linear_combination -cyclo

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (cyclo : x^2+x+1=0) (two : IsUnit (2:R)) (reg : IsUnit (x-1))
    (no7 : ¬ ((7:R)=0 ∧ (x=2 ∨ x=4))) : ∀ i,evalVec x (obs i)≠0 := by
  have three : IsUnit (3:R) := isUnit_of_dvd_unit (show (3:R)∣(x-1)^2 from
    ⟨-x,by linear_combination cyclo⟩) (reg.pow 2)
  intro i h
  fin_cases i
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply one_ne_zero (α := R)
    linear_combination (-x-1) * h + (1) * cyclo
  · change (((0:ℤ):R)+x*(((2:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply two.ne_zero
    linear_combination (-x-1) * h + (2) * cyclo
  · change (((1:ℤ):R)+x*(((-2:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply no7
    refine ⟨?_,Or.inr ?_⟩
    · linear_combination (2*x+3) * h + (4) * cyclo
    · linear_combination (-x-2) * h + (-2) * cyclo
  · change (((1:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply three.ne_zero
    linear_combination (x+2) * h + (1) * cyclo
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply one_ne_zero (α := R)
    linear_combination (1) * h + (0) * cyclo
  · change (((1:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply one_ne_zero (α := R)
    linear_combination (-x) * h + (1) * cyclo
  · change (((1:ℤ):R)+x*(((2:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply three.ne_zero
    linear_combination (-2*x-1) * h + (4) * cyclo
  · change (((1:ℤ):R)+x*(((3:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply no7
    refine ⟨?_,Or.inl ?_⟩
    · linear_combination (-3*x-2) * h + (9) * cyclo
    · linear_combination (x+1) * h + (-3) * cyclo
  · change (((2:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply no7
    refine ⟨?_,Or.inl ?_⟩
    · linear_combination (x+3) * h + (1) * cyclo
    · linear_combination (-1) * h + (0) * cyclo
  · change (((2:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply two.ne_zero
    linear_combination (1) * h + (0) * cyclo
  · change (((2:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply three.ne_zero
    linear_combination (-x+1) * h + (1) * cyclo
  · change (((2:ℤ):R)+x*(((2:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply two.ne_zero
    linear_combination (-x) * h + (2) * cyclo
  · change (((2:ℤ):R)+x*(((3:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply no7
    refine ⟨?_,Or.inr ?_⟩
    · linear_combination (-3*x-1) * h + (9) * cyclo
    · linear_combination (2*x+1) * h + (-6) * cyclo
  · change (((3:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply three.ne_zero
    linear_combination (1) * h + (0) * cyclo
  · change (((3:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply no7
    refine ⟨?_,Or.inr ?_⟩
    · linear_combination (-x+2) * h + (1) * cyclo
    · linear_combination (x-1) * h + (-1) * cyclo
  · change (((3:ℤ):R)+x*(((2:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply no7
    refine ⟨?_,Or.inl ?_⟩
    · linear_combination (-2*x+1) * h + (4) * cyclo
    · linear_combination (x) * h + (-2) * cyclo
  · change (((4:ℤ):R)+x*(((2:ℤ):R)+x*(0:R)))=0 at h
    push_cast at h
    apply (by convert ((two.pow 2).mul three).ne_zero using 1; norm_num : (12:R)≠0)
    linear_combination (-2*x+2) * h + (4) * cyclo

end NecklaceTheta.three

namespace NecklaceTheta.two
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 3 1 where
  side := AtlasIndices.shores8
  ht := ![0,0,0,0,0,2,2,2,0,0,2,2,1,1,1,1,1,1,1,1,1,0,0]
  lamp := ![![0],![3],![0],![6],![6],![6],![3],![3],![3],![1],![1],![5],![5],![5],![3],![3],![0],![0],![2],![2],![4],![4],![4]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 3 → Fin 1 → ℤ := ![![1],![2],![4]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 6 → Fin 1 → ℤ := ![![1],![2],![3],![4],![5],![6]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 3 0 7 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] [Nontrivial R] {x : R}

omit [Nontrivial R] in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=2) (seven : (7:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*seven
  · change (((2:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*seven
  · change (((4:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (0:R)*seven

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (seven : (7:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*seven
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h+(-1:R)*seven
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h+(-2:R)*seven
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (2:R)*h+(-1:R)*seven
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (3:R)*h+(-2:R)*seven
  · change (((6:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-5:R)*seven

end NecklaceTheta.two

namespace NecklaceTheta.four
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 3 1 where
  side := AtlasIndices.shores8
  ht := ![0,0,0,0,0,0,0,0,0,0,2,2,2,2,1,1,1,1,2,2,2,2,0]
  lamp := ![![0],![3],![0],![6],![6],![5],![5],![4],![4],![1],![1],![1],![6],![6],![6],![3],![0],![0],![0],![5],![5],![3],![3]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 3 → Fin 1 → ℤ := ![![1],![4],![2]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 6 → Fin 1 → ℤ := ![![1],![2],![3],![4],![5],![6]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 3 0 7 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] [Nontrivial R] {x : R}

omit [Nontrivial R] in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=4) (seven : (7:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*seven
  · change (((4:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*seven
  · change (((2:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (-2:R)*seven

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (seven : (7:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*seven
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h+(-1:R)*seven
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h+(-2:R)*seven
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (2:R)*h+(-1:R)*seven
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (3:R)*h+(-2:R)*seven
  · change (((6:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-5:R)*seven

end NecklaceTheta.four

namespace NecklaceTheta
open MetabelianModule EqualArms MetabelianRegular

theorem chart_three {R V : Type*} [CommRing R] [Nontrivial R] {x : R} {B : SimpleGraph V}
    (C : Chart B 3 0 x) (period : x^3=1) (twoUnit : IsUnit (2:R)) (reg : IsUnit (x-1)) :
    Nonempty (Theta B 8) ∨ Nonempty (Theta B 16) := by
  have cyclo : x^2+x+1=0 := reg.mul_right_eq_zero.mp (by linear_combination period)
  by_cases h : (7:R)=0 ∧ (x=2 ∨ x=4)
  · obtain ⟨seven,hx|hx⟩ := h
    · exact .inl (tableTheta C two.tbl two.gaps two.obs two.table_ok (by decide) (.inr rfl)
        (by simpa only [Nat.cast_ofNat] using seven) (two.gaps_eval hx seven) (two.separated seven))
    · exact .inl (tableTheta C four.tbl four.gaps four.obs four.table_ok (by decide) (.inr rfl)
        (by simpa only [Nat.cast_ofNat] using seven) (four.gaps_eval hx seven) (four.separated seven))
  · exact .inr (tableTheta C three.tbl three.gaps three.obs three.table_ok (by decide) (.inr rfl)
      (by simp) (three.gaps_eval cyclo) (three.separated cyclo twoUnit reg h))

end NecklaceTheta

namespace NecklaceTheta
variable {R : Type*} [CommRing R]

def badA (x : R) : Fin 6 → R := ![-2*x+1,-x^2-x+1,x^2-x+1,-x^2+x+1,x^2+x+1,2*x+1]

def badB (x : R) : Fin 17 → R := ![-x^2-2*x+2,x^2-2*x+2,-x+2,-x^2-x+2,x^2-x+2,-x^2+2,x^2+2,x+2,-x^2+x+2,x^2+x+2,-x^2+2*x+2,x^2+2*x+2,3,-x^2+3,x^2+3,-x^2+4,x^2+4]

end NecklaceTheta

namespace NecklaceTheta.wideA
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 47 16 4 4 where
  side := AtlasIndices.shores16
  ht := ![2,2,2,1,1,0,0,0,1,1,1,0,0,0,1,1,2,2,1,1,1,2,2,3,3,3,2,2,2,3,3,3,3,3,3,2,2,2,3,3,3,2,2,1,1,1,2]
  lamp := ![![0,0,0,0],![0,-1,-1,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![-1,0,0,0],![-1,0,0,0],![-1,-1,0,0],![-1,-1,0,0],![-1,-1,0,0],![0,-1,0,0],![0,-1,0,0],![0,-1,0,0],![0,-1,0,0],![0,-1,0,0],![0,0,1,0],![0,0,1,0],![0,0,1,0],![0,-1,1,0],![0,-1,1,0],![0,-1,0,0],![0,-1,0,0],![0,-1,0,0],![0,-1,0,1],![0,-1,0,1],![0,-1,0,1],![0,-1,-1,1],![0,-1,-1,1],![0,-1,-1,0],![0,-1,-1,0],![0,0,0,0],![0,0,0,0],![0,0,0,1],![0,0,0,1],![0,0,0,1],![0,0,-1,1],![0,0,-1,1],![0,0,-1,0],![0,0,-1,0],![0,0,-1,0],![0,0,-1,0],![0,0,-1,0],![0,0,-1,0],![0,-1,-1,0],![0,-1,-1,0]]
  route := AtlasIndices.route16
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 4 → Fin 4 → ℤ := ![![1,0,0,0],![0,1,0,0],![0,0,1,0],![0,0,0,1]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 23 → Fin 4 → ℤ := ![![0,0,0,1],![0,0,1,-1],![0,0,1,0],![0,0,1,1],![0,0,2,0],![0,1,-2,0],![0,1,-1,-1],![0,1,-1,0],![0,1,-1,1],![0,1,0,-1],![0,1,0,0],![0,1,0,1],![0,1,1,-1],![0,1,1,0],![0,1,1,1],![0,1,2,0],![1,-1,0,0],![1,0,-1,0],![1,0,0,0],![1,0,1,0],![1,1,-1,0],![1,1,0,0],![1,1,1,0]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 0 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval  : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=x^0
    push_cast; ring
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=x^1
    push_cast; ring
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=x^2
    push_cast; ring
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))))=x^3
    push_cast; ring

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated {m : ℕ} (odd : Odd m) (period : x^m=1) (two : IsUnit (2:R))
    (reg : IsUnit (x-1)) (good : ∀ i,badA x i≠0) : ∀ i,evalVec x (obs i)≠0 := by
  have ux := unit_period odd period
  have un (k : ℕ) := unit_sum_pow odd period two k
  intro i h
  fin_cases i
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (1:R)≠0 := by
      convert ((isUnit_one (M:=R)) : IsUnit _).ne_zero using 1
    apply n
    apply (ux.pow 3).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (-x+1:R)≠0 := by
      convert (reg.neg : IsUnit _).ne_zero using 1; ring
    apply n
    apply (ux.pow 2).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (1:R)≠0 := by
      convert ((isUnit_one (M:=R)) : IsUnit _).ne_zero using 1
    apply n
    apply (ux.pow 2).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (x+1:R)≠0 := by
      convert (un 1 : IsUnit _).ne_zero using 1; ring
    apply n
    apply (ux.pow 2).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((2:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (2:R)≠0 := by
      convert (two : IsUnit _).ne_zero using 1
    apply n
    apply (ux.pow 2).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((-2:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (-2*x+1:R)≠0 := good 0
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((-1:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (-x^2-x+1:R)≠0 := good 1
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (-x+1:R)≠0 := by
      convert (reg.neg : IsUnit _).ne_zero using 1; ring
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((-1:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (x^2-x+1:R)≠0 := good 2
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (-x^2+1:R)≠0 := by
      convert (unit_diff2 odd period two reg : IsUnit _).ne_zero using 1; ring
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (1:R)≠0 := by
      convert ((isUnit_one (M:=R)) : IsUnit _).ne_zero using 1
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (x^2+1:R)≠0 := by
      convert (un 2 : IsUnit _).ne_zero using 1; ring
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (-x^2+x+1:R)≠0 := good 3
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (x+1:R)≠0 := by
      convert (un 1 : IsUnit _).ne_zero using 1; ring
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (x^2+x+1:R)≠0 := good 4
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((2:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (2*x+1:R)≠0 := good 5
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (-x+1:R)≠0 := by
      convert (reg.neg : IsUnit _).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (-x^2+1:R)≠0 := by
      convert (unit_diff2 odd period two reg : IsUnit _).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (1:R)≠0 := by
      convert ((isUnit_one (M:=R)) : IsUnit _).ne_zero using 1
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (x^2+1:R)≠0 := by
      convert (un 2 : IsUnit _).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((1:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (-x^2+x+1:R)≠0 := good 3
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (x+1:R)≠0 := by
      convert (un 1 : IsUnit _).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R)))))=0 at h
    push_cast at h
    have n : (x^2+x+1:R)≠0 := good 4
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) (odd : Odd m) (period : x^m=1)
    (two : IsUnit (2:R)) (reg : IsUnit (x-1)) (good : ∀ i,badA x i≠0)
    {V : Type*} {B : SimpleGraph V} (C : Chart B m 0 x) : Nonempty (EqualArms.Theta B 16) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl) (by simp) gaps_eval
    (separated odd period two reg good)

end NecklaceTheta.wideA

namespace NecklaceTheta.wideB
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 47 16 3 3 where
  side := AtlasIndices.shores16
  ht := ![0,0,0,0,0,0,1,1,2,2,2,1,1,0,0,0,0,0,0,0,0,1,1,2,2,2,1,1,0,0,0,0,1,1,1,1,1,1,2,2,2,1,1,1,1,1,1]
  lamp := ![![0,0,0],![0,0,1],![0,0,0],![-1,0,0],![-1,0,0],![-2,0,0],![-2,0,0],![-2,0,0],![-2,0,0],![-2,0,0],![-2,0,1],![-2,0,1],![-2,0,1],![-2,0,1],![-1,0,1],![-1,0,1],![0,0,1],![1,0,0],![1,0,0],![2,0,0],![2,0,0],![2,0,0],![2,0,0],![2,0,0],![2,0,0],![2,0,1],![2,0,1],![2,0,1],![2,0,1],![2,0,1],![1,0,1],![1,0,1],![0,0,0],![0,0,0],![0,1,0],![0,1,0],![0,2,0],![0,2,0],![0,2,0],![0,2,0],![0,2,1],![0,2,1],![0,2,1],![0,1,1],![0,1,1],![0,0,1],![0,0,1]]
  route := AtlasIndices.route16
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 3 → Fin 3 → ℤ := ![![1,0,0],![0,1,0],![0,0,1]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 31 → Fin 3 → ℤ := ![![0,0,1],![0,1,-1],![0,1,0],![0,1,1],![0,2,-1],![0,2,0],![0,2,1],![1,0,-1],![1,0,0],![1,0,1],![2,-2,-1],![2,-2,0],![2,-2,1],![2,-1,-1],![2,-1,0],![2,-1,1],![2,0,-1],![2,0,0],![2,0,1],![2,1,-1],![2,1,0],![2,1,1],![2,2,-1],![2,2,0],![2,2,1],![3,0,-1],![3,0,0],![3,0,1],![4,0,-1],![4,0,0],![4,0,1]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 0 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval  : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))=x^0
    push_cast; ring
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))=x^1
    push_cast; ring
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R))))=x^2
    push_cast; ring

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated {m : ℕ} (odd : Odd m) (period : x^m=1) (two : IsUnit (2:R))
    (reg : IsUnit (x-1)) (good : ∀ i,badB x i≠0) : ∀ i,evalVec x (obs i)≠0 := by
  have ux := unit_period odd period
  have un (k : ℕ) := unit_sum_pow odd period two k
  intro i h
  fin_cases i
  · change (((0:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (1:R)≠0 := by
      convert ((isUnit_one (M:=R)) : IsUnit _).ne_zero using 1
    apply n
    apply (ux.pow 2).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (-x+1:R)≠0 := by
      convert (reg.neg : IsUnit _).ne_zero using 1; ring
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (1:R)≠0 := by
      convert ((isUnit_one (M:=R)) : IsUnit _).ne_zero using 1
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (x+1:R)≠0 := by
      convert (un 1 : IsUnit _).ne_zero using 1; ring
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((2:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (-x+2:R)≠0 := good 2
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((2:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (2:R)≠0 := by
      convert (two : IsUnit _).ne_zero using 1
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((0:ℤ):R)+x*(((2:ℤ):R)+x*(((1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (x+2:R)≠0 := good 7
    apply n
    apply (ux.pow 1).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (-x^2+1:R)≠0 := by
      convert (unit_diff2 odd period two reg : IsUnit _).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (1:R)≠0 := by
      convert ((isUnit_one (M:=R)) : IsUnit _).ne_zero using 1
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((1:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (x^2+1:R)≠0 := by
      convert (un 2 : IsUnit _).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((2:ℤ):R)+x*(((-2:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (-x^2-2*x+2:R)≠0 := good 0
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((2:ℤ):R)+x*(((-2:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (-2*x+2:R)≠0 := by
      convert (two.mul reg.neg : IsUnit _).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((2:ℤ):R)+x*(((-2:ℤ):R)+x*(((1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (x^2-2*x+2:R)≠0 := good 1
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((2:ℤ):R)+x*(((-1:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (-x^2-x+2:R)≠0 := good 3
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((2:ℤ):R)+x*(((-1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (-x+2:R)≠0 := good 2
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((2:ℤ):R)+x*(((-1:ℤ):R)+x*(((1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (x^2-x+2:R)≠0 := good 4
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((2:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (-x^2+2:R)≠0 := good 5
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((2:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (2:R)≠0 := by
      convert (two : IsUnit _).ne_zero using 1
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((2:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (x^2+2:R)≠0 := good 6
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((2:ℤ):R)+x*(((1:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (-x^2+x+2:R)≠0 := good 8
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((2:ℤ):R)+x*(((1:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (x+2:R)≠0 := good 7
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((2:ℤ):R)+x*(((1:ℤ):R)+x*(((1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (x^2+x+2:R)≠0 := good 9
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((2:ℤ):R)+x*(((2:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (-x^2+2*x+2:R)≠0 := good 10
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((2:ℤ):R)+x*(((2:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (2*x+2:R)≠0 := by
      convert (two.mul (un 1) : IsUnit _).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((2:ℤ):R)+x*(((2:ℤ):R)+x*(((1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (x^2+2*x+2:R)≠0 := good 11
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((3:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (-x^2+3:R)≠0 := good 13
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((3:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (3:R)≠0 := good 12
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((3:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (x^2+3:R)≠0 := good 14
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((4:ℤ):R)+x*(((0:ℤ):R)+x*(((-1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (-x^2+4:R)≠0 := good 15
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((4:ℤ):R)+x*(((0:ℤ):R)+x*(((0:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (4:R)≠0 := by
      convert (two.pow 2 : IsUnit _).ne_zero using 1; ring
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h
  · change (((4:ℤ):R)+x*(((0:ℤ):R)+x*(((1:ℤ):R)+x*(0:R))))=0 at h
    push_cast at h
    have n : (x^2+4:R)≠0 := good 16
    apply n
    apply (ux.pow 0).mul_right_eq_zero.mp
    linear_combination h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) (odd : Odd m) (period : x^m=1)
    (two : IsUnit (2:R)) (reg : IsUnit (x-1)) (good : ∀ i,badB x i≠0)
    {V : Type*} {B : SimpleGraph V} (C : Chart B m 0 x) : Nonempty (EqualArms.Theta B 16) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl) (by simp) gaps_eval
    (separated odd period two reg good)

end NecklaceTheta.wideB

namespace NecklaceTheta.case7_2
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 4 1 where
  side := AtlasIndices.shores8
  ht := ![1,1,1,1,1,0,0,0,1,1,0,0,0,1,1,1,2,2,3,3,3,2,2]
  lamp := ![![0],![6],![0],![5],![5],![5],![6],![6],![6],![2],![2],![3],![3],![3],![1],![1],![0],![0],![0],![6],![6],![6],![6]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 4 → Fin 1 → ℤ := ![![1],![2],![4],![1]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 6 → Fin 1 → ℤ := ![![1],![2],![3],![4],![5],![6]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 7 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=2) (char : (7:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((4:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((1:ℤ):R)+x*(0:R))=x^3
    rw [hx]
    push_cast; linear_combination (-1:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (7:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h+(-1:R)*char
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h+(-2:R)*char
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (2:R)*h+(-1:R)*char
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (3:R)*h+(-2:R)*char
  · change (((6:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-5:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (7:R)=0) (hx : x=2) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case7_2

namespace NecklaceTheta.case7_4
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 4 1 where
  side := AtlasIndices.shores8
  ht := ![2,1,2,1,1,0,0,0,1,2,1,1,0,0,0,1,3,3,3,2,2,2,2]
  lamp := ![![0],![6],![0],![0],![0],![0],![0],![6],![6],![2],![2],![2],![2],![3],![3],![3],![0],![0],![1],![1],![1],![6],![6]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 4 → Fin 1 → ℤ := ![![1],![4],![2],![1]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 6 → Fin 1 → ℤ := ![![1],![2],![3],![4],![5],![6]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 7 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=4) (char : (7:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((4:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (-2:R)*char
  · change (((1:ℤ):R)+x*(0:R))=x^3
    rw [hx]
    push_cast; linear_combination (-9:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (7:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h+(-1:R)*char
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h+(-2:R)*char
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (2:R)*h+(-1:R)*char
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (3:R)*h+(-2:R)*char
  · change (((6:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-5:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (7:R)=0) (hx : x=4) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case7_4

namespace NecklaceTheta.case11_3
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 2 1 where
  side := AtlasIndices.shores8
  ht := ![0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,0,0]
  lamp := ![![0],![7],![0],![10],![10],![9],![9],![8],![8],![1],![1],![1],![1],![4],![4],![7],![0],![0],![3],![3],![6],![6],![7]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 2 → Fin 1 → ℤ := ![![1],![3]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 10 → Fin 1 → ℤ := ![![1],![2],![3],![4],![5],![6],![7],![8],![9],![10]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 11 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=3) (char : (11:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((3:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (11:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-1:R)*char
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h+(-1:R)*char
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (3:R)*h+(-1:R)*char
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (9:R)*h+(-4:R)*char
  · change (((6:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (2:R)*h+(-1:R)*char
  · change (((7:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (8:R)*h+(-5:R)*char
  · change (((8:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (7:R)*h+(-5:R)*char
  · change (((9:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h+(-4:R)*char
  · change (((10:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (10:R)*h+(-9:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (11:R)=0) (hx : x=3) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case11_3

namespace NecklaceTheta.case11_4
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 3 1 where
  side := AtlasIndices.shores8
  ht := ![1,1,1,1,2,2,2,2,2,1,0,0,0,0,0,1,2,2,2,2,2,1,1]
  lamp := ![![0],![6],![0],![7],![7],![7],![1],![1],![6],![4],![4],![5],![5],![6],![6],![6],![0],![0],![5],![5],![10],![10],![10]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 3 → Fin 1 → ℤ := ![![1],![4],![5]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 9 → Fin 1 → ℤ := ![![1],![2],![3],![4],![5],![6],![7],![9],![10]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 11 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=4) (char : (11:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((4:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((5:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (-1:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (11:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-1:R)*char
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h+(-1:R)*char
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (3:R)*h+(-1:R)*char
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (9:R)*h+(-4:R)*char
  · change (((6:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (2:R)*h+(-1:R)*char
  · change (((7:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (8:R)*h+(-5:R)*char
  · change (((9:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h+(-4:R)*char
  · change (((10:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (10:R)*h+(-9:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (11:R)=0) (hx : x=4) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case11_4

namespace NecklaceTheta.case11_5
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 2 1 where
  side := AtlasIndices.shores8
  ht := ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,0,0,0,0]
  lamp := ![![0],![7],![0],![10],![10],![9],![9],![8],![8],![1],![1],![2],![2],![2],![2],![7],![0],![0],![5],![5],![6],![6],![7]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 2 → Fin 1 → ℤ := ![![1],![5]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 10 → Fin 1 → ℤ := ![![1],![2],![3],![4],![5],![6],![7],![8],![9],![10]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 11 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=5) (char : (11:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((5:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (11:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-1:R)*char
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h+(-1:R)*char
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (3:R)*h+(-1:R)*char
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (9:R)*h+(-4:R)*char
  · change (((6:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (2:R)*h+(-1:R)*char
  · change (((7:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (8:R)*h+(-5:R)*char
  · change (((8:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (7:R)*h+(-5:R)*char
  · change (((9:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h+(-4:R)*char
  · change (((10:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (10:R)*h+(-9:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (11:R)=0) (hx : x=5) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case11_5

namespace NecklaceTheta.case11_9
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 4 1 where
  side := AtlasIndices.shores8
  ht := ![1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,1,2,2,3,3,3,2,2]
  lamp := ![![0],![8],![0],![2],![2],![4],![4],![6],![6],![9],![9],![7],![7],![8],![8],![8],![0],![0],![0],![8],![8],![8],![8]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 4 → Fin 1 → ℤ := ![![1],![9],![4],![3]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 9 → Fin 1 → ℤ := ![![1],![2],![3],![4],![5],![6],![7],![8],![9]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 11 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=9) (char : (11:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((9:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((4:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (-7:R)*char
  · change (((3:ℤ):R)+x*(0:R))=x^3
    rw [hx]
    push_cast; linear_combination (-66:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (11:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-1:R)*char
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h+(-1:R)*char
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (3:R)*h+(-1:R)*char
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (9:R)*h+(-4:R)*char
  · change (((6:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (2:R)*h+(-1:R)*char
  · change (((7:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (8:R)*h+(-5:R)*char
  · change (((8:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (7:R)*h+(-5:R)*char
  · change (((9:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h+(-4:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (11:R)=0) (hx : x=9) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case11_9

namespace NecklaceTheta.case13_3
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 3 1 where
  side := AtlasIndices.shores8
  ht := ![1,1,1,1,1,1,1,1,1,1,0,0,0,0,0,1,2,2,2,2,2,2,2]
  lamp := ![![0],![1],![0],![10],![10],![7],![7],![4],![4],![3],![3],![3],![2],![2],![1],![1],![0],![0],![9],![9],![5],![5],![1]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 3 → Fin 1 → ℤ := ![![1],![3],![9]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 10 → Fin 1 → ℤ := ![![1],![2],![3],![4],![5],![6],![7],![8],![9],![10]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 13 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=3) (char : (13:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((3:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((9:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (0:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (13:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (7:R)*h+(-1:R)*char
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (9:R)*h+(-2:R)*char
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (10:R)*h+(-3:R)*char
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (8:R)*h+(-3:R)*char
  · change (((6:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (11:R)*h+(-5:R)*char
  · change (((7:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (2:R)*h+(-1:R)*char
  · change (((8:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h+(-3:R)*char
  · change (((9:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (3:R)*h+(-2:R)*char
  · change (((10:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h+(-3:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (13:R)=0) (hx : x=3) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case13_3

namespace NecklaceTheta.case13_9
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 2 1 where
  side := AtlasIndices.shores8
  ht := ![0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,0,0]
  lamp := ![![0],![9],![0],![12],![12],![11],![11],![10],![10],![1],![1],![1],![5],![5],![9],![9],![0],![4],![4],![8],![8],![8],![9]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 2 → Fin 1 → ℤ := ![![1],![9]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 11 → Fin 1 → ℤ := ![![1],![2],![3],![4],![5],![7],![8],![9],![10],![11],![12]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 13 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=9) (char : (13:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((9:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (13:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (7:R)*h+(-1:R)*char
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (9:R)*h+(-2:R)*char
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (10:R)*h+(-3:R)*char
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (8:R)*h+(-3:R)*char
  · change (((7:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (2:R)*h+(-1:R)*char
  · change (((8:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h+(-3:R)*char
  · change (((9:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (3:R)*h+(-2:R)*char
  · change (((10:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h+(-3:R)*char
  · change (((11:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-5:R)*char
  · change (((12:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (12:R)*h+(-11:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (13:R)=0) (hx : x=9) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case13_9

namespace NecklaceTheta.case19_4
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 3 1 where
  side := AtlasIndices.shores8
  ht := ![1,0,1,1,1,1,1,0,0,1,1,1,0,0,0,0,2,2,2,2,2,1,1]
  lamp := ![![0],![10],![0],![15],![15],![11],![11],![11],![11],![4],![4],![8],![8],![9],![9],![10],![0],![3],![3],![6],![6],![6],![10]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 3 → Fin 1 → ℤ := ![![1],![4],![16]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 12 → Fin 1 → ℤ := ![![1],![2],![3],![4],![5],![6],![7],![8],![9],![10],![11],![15]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 19 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=4) (char : (19:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((4:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((16:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (0:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (19:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (10:R)*h+(-1:R)*char
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (13:R)*h+(-2:R)*char
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h+(-1:R)*char
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h+(-1:R)*char
  · change (((6:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (16:R)*h+(-5:R)*char
  · change (((7:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (11:R)*h+(-4:R)*char
  · change (((8:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (12:R)*h+(-5:R)*char
  · change (((9:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (17:R)*h+(-8:R)*char
  · change (((10:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (2:R)*h+(-1:R)*char
  · change (((11:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (7:R)*h+(-4:R)*char
  · change (((15:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (14:R)*h+(-11:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (19:R)=0) (hx : x=4) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case19_4

namespace NecklaceTheta.case19_5
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 3 1 where
  side := AtlasIndices.shores8
  ht := ![0,1,0,0,0,0,0,0,1,0,0,1,1,1,1,1,1,1,1,1,2,2,2]
  lamp := ![![0],![11],![0],![18],![18],![17],![17],![16],![16],![1],![1],![1],![1],![6],![6],![11],![0],![0],![5],![5],![5],![5],![11]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 3 → Fin 1 → ℤ := ![![1],![5],![6]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 11 → Fin 1 → ℤ := ![![1],![2],![4],![5],![6],![10],![11],![15],![16],![17],![18]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 19 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=5) (char : (19:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((5:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((6:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (-1:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (19:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (10:R)*h+(-1:R)*char
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h+(-1:R)*char
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h+(-1:R)*char
  · change (((6:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (16:R)*h+(-5:R)*char
  · change (((10:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (2:R)*h+(-1:R)*char
  · change (((11:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (7:R)*h+(-4:R)*char
  · change (((15:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (14:R)*h+(-11:R)*char
  · change (((16:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-5:R)*char
  · change (((17:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (9:R)*h+(-8:R)*char
  · change (((18:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (18:R)*h+(-17:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (19:R)=0) (hx : x=5) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case19_5

namespace NecklaceTheta.case19_6
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 2 1 where
  side := AtlasIndices.shores8
  ht := ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,0,0,0,0]
  lamp := ![![0],![15],![0],![18],![18],![17],![17],![16],![16],![1],![1],![2],![2],![2],![15],![15],![0],![13],![13],![13],![14],![14],![15]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 2 → Fin 1 → ℤ := ![![1],![6]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 13 → Fin 1 → ℤ := ![![1],![2],![3],![4],![5],![11],![12],![13],![14],![15],![16],![17],![18]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 19 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=6) (char : (19:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((6:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (19:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (10:R)*h+(-1:R)*char
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (13:R)*h+(-2:R)*char
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h+(-1:R)*char
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h+(-1:R)*char
  · change (((11:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (7:R)*h+(-4:R)*char
  · change (((12:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (8:R)*h+(-5:R)*char
  · change (((13:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (3:R)*h+(-2:R)*char
  · change (((14:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (15:R)*h+(-11:R)*char
  · change (((15:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (14:R)*h+(-11:R)*char
  · change (((16:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-5:R)*char
  · change (((17:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (9:R)*h+(-8:R)*char
  · change (((18:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (18:R)*h+(-17:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (19:R)=0) (hx : x=6) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case19_6

namespace NecklaceTheta.case19_7
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 2 1 where
  side := AtlasIndices.shores8
  ht := ![0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,0,0]
  lamp := ![![0],![15],![0],![18],![18],![17],![17],![16],![16],![1],![1],![1],![1],![8],![8],![15],![0],![0],![7],![7],![14],![14],![15]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 2 → Fin 1 → ℤ := ![![1],![7]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 13 → Fin 1 → ℤ := ![![1],![2],![3],![4],![6],![7],![8],![13],![14],![15],![16],![17],![18]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 19 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=7) (char : (19:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((7:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (19:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (10:R)*h+(-1:R)*char
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (13:R)*h+(-2:R)*char
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h+(-1:R)*char
  · change (((6:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (16:R)*h+(-5:R)*char
  · change (((7:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (11:R)*h+(-4:R)*char
  · change (((8:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (12:R)*h+(-5:R)*char
  · change (((13:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (3:R)*h+(-2:R)*char
  · change (((14:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (15:R)*h+(-11:R)*char
  · change (((15:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (14:R)*h+(-11:R)*char
  · change (((16:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-5:R)*char
  · change (((17:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (9:R)*h+(-8:R)*char
  · change (((18:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (18:R)*h+(-17:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (19:R)=0) (hx : x=7) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case19_7

namespace NecklaceTheta.case19_9
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 4 1 where
  side := AtlasIndices.shores8
  ht := ![1,1,1,0,0,0,0,0,1,1,0,0,0,0,0,1,2,2,3,3,3,2,2]
  lamp := ![![0],![2],![0],![0],![1],![1],![2],![2],![2],![9],![9],![10],![10],![11],![11],![11],![0],![14],![14],![14],![2],![2],![2]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 4 → Fin 1 → ℤ := ![![1],![9],![5],![7]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 8 → Fin 1 → ℤ := ![![1],![2],![7],![8],![9],![10],![11],![12]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 19 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=9) (char : (19:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((9:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((5:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (-4:R)*char
  · change (((7:ℤ):R)+x*(0:R))=x^3
    rw [hx]
    push_cast; linear_combination (-38:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (19:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (10:R)*h+(-1:R)*char
  · change (((7:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (11:R)*h+(-4:R)*char
  · change (((8:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (12:R)*h+(-5:R)*char
  · change (((9:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (17:R)*h+(-8:R)*char
  · change (((10:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (2:R)*h+(-1:R)*char
  · change (((11:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (7:R)*h+(-4:R)*char
  · change (((12:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (8:R)*h+(-5:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (19:R)=0) (hx : x=9) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case19_9

namespace NecklaceTheta.case19_11
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 4 1 where
  side := AtlasIndices.shores8
  ht := ![1,1,1,1,1,1,1,1,1,1,0,0,0,0,0,1,2,2,3,3,3,2,2]
  lamp := ![![0],![13],![0],![8],![8],![16],![16],![5],![5],![11],![11],![12],![12],![13],![13],![13],![0],![12],![12],![12],![13],![13],![13]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 4 → Fin 1 → ℤ := ![![1],![11],![7],![1]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 9 → Fin 1 → ℤ := ![![1],![2],![3],![5],![6],![8],![11],![13],![16]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 19 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=11) (char : (19:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((11:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((7:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (-6:R)*char
  · change (((1:ℤ):R)+x*(0:R))=x^3
    rw [hx]
    push_cast; linear_combination (-70:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (19:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (10:R)*h+(-1:R)*char
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (13:R)*h+(-2:R)*char
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h+(-1:R)*char
  · change (((6:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (16:R)*h+(-5:R)*char
  · change (((8:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (12:R)*h+(-5:R)*char
  · change (((11:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (7:R)*h+(-4:R)*char
  · change (((13:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (3:R)*h+(-2:R)*char
  · change (((16:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-5:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (19:R)=0) (hx : x=11) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case19_11

namespace NecklaceTheta.case19_16
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 4 1 where
  side := AtlasIndices.shores8
  ht := ![1,2,1,1,1,1,1,1,2,1,0,0,0,1,1,2,2,2,2,2,3,3,3]
  lamp := ![![0],![9],![0],![3],![3],![6],![6],![9],![9],![16],![16],![16],![15],![15],![18],![18],![0],![10],![10],![1],![1],![9],![9]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 4 → Fin 1 → ℤ := ![![1],![16],![9],![11]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 11 → Fin 1 → ℤ := ![![1],![3],![6],![8],![9],![10],![12],![13],![15],![16],![18]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 19 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=16) (char : (19:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((16:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((9:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (-13:R)*char
  · change (((11:ℤ):R)+x*(0:R))=x^3
    rw [hx]
    push_cast; linear_combination (-215:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (19:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (13:R)*h+(-2:R)*char
  · change (((6:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (16:R)*h+(-5:R)*char
  · change (((8:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (12:R)*h+(-5:R)*char
  · change (((9:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (17:R)*h+(-8:R)*char
  · change (((10:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (2:R)*h+(-1:R)*char
  · change (((12:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (8:R)*h+(-5:R)*char
  · change (((13:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (3:R)*h+(-2:R)*char
  · change (((15:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (14:R)*h+(-11:R)*char
  · change (((16:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-5:R)*char
  · change (((18:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (18:R)*h+(-17:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (19:R)=0) (hx : x=16) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case19_16

namespace NecklaceTheta.case19_17
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 4 1 where
  side := AtlasIndices.shores8
  ht := ![1,2,1,0,0,0,1,1,2,1,0,0,0,1,1,2,2,2,3,3,3,3,3]
  lamp := ![![0],![18],![0],![0],![1],![1],![1],![3],![3],![17],![17],![17],![16],![16],![18],![18],![0],![15],![15],![15],![7],![7],![18]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 4 → Fin 1 → ℤ := ![![1],![17],![4],![11]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 8 → Fin 1 → ℤ := ![![1],![3],![8],![11],![15],![16],![17],![18]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 19 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=17) (char : (19:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((17:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((4:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (-15:R)*char
  · change (((11:ℤ):R)+x*(0:R))=x^3
    rw [hx]
    push_cast; linear_combination (-258:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (19:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (13:R)*h+(-2:R)*char
  · change (((8:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (12:R)*h+(-5:R)*char
  · change (((11:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (7:R)*h+(-4:R)*char
  · change (((15:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (14:R)*h+(-11:R)*char
  · change (((16:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-5:R)*char
  · change (((17:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (9:R)*h+(-8:R)*char
  · change (((18:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (18:R)*h+(-17:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (19:R)=0) (hx : x=17) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case19_17

namespace NecklaceTheta.case29_7
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 3 1 where
  side := AtlasIndices.shores8
  ht := ![1,1,1,0,0,0,0,0,1,1,0,0,0,0,0,1,2,2,2,2,2,2,2]
  lamp := ![![0],![27],![0],![0],![0],![28],![28],![27],![27],![7],![7],![7],![6],![6],![5],![5],![0],![9],![9],![18],![18],![27],![27]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 3 → Fin 1 → ℤ := ![![1],![7],![20]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 13 → Fin 1 → ℤ := ![![1],![2],![5],![6],![7],![9],![18],![20],![21],![22],![23],![27],![28]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 29 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=7) (char : (29:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((7:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((20:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (-1:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (29:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (15:R)*h+(-1:R)*char
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-1:R)*char
  · change (((6:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h+(-1:R)*char
  · change (((7:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (25:R)*h+(-6:R)*char
  · change (((9:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (13:R)*h+(-4:R)*char
  · change (((18:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (21:R)*h+(-13:R)*char
  · change (((20:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (16:R)*h+(-11:R)*char
  · change (((21:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (18:R)*h+(-13:R)*char
  · change (((22:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h+(-3:R)*char
  · change (((23:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (24:R)*h+(-19:R)*char
  · change (((27:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (14:R)*h+(-13:R)*char
  · change (((28:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (28:R)*h+(-27:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (29:R)=0) (hx : x=7) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case29_7

namespace NecklaceTheta.case29_16
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 4 1 where
  side := AtlasIndices.shores8
  ht := ![1,2,1,1,1,1,1,1,2,1,0,0,0,1,1,2,2,2,3,3,3,3,3]
  lamp := ![![0],![15],![0],![13],![13],![26],![26],![10],![10],![16],![16],![16],![15],![15],![15],![15],![0],![0],![0],![22],![22],![15],![15]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 4 → Fin 1 → ℤ := ![![1],![16],![24],![7]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 12 → Fin 1 → ℤ := ![![1],![2],![3],![5],![7],![10],![11],![13],![15],![16],![22],![26]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 29 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=16) (char : (29:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((16:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((24:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (-8:R)*char
  · change (((7:ℤ):R)+x*(0:R))=x^3
    rw [hx]
    push_cast; linear_combination (-141:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (29:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (15:R)*h+(-1:R)*char
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (10:R)*h+(-1:R)*char
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-1:R)*char
  · change (((7:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (25:R)*h+(-6:R)*char
  · change (((10:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (3:R)*h+(-1:R)*char
  · change (((11:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (8:R)*h+(-3:R)*char
  · change (((13:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (9:R)*h+(-4:R)*char
  · change (((15:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (2:R)*h+(-1:R)*char
  · change (((16:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (20:R)*h+(-11:R)*char
  · change (((22:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h+(-3:R)*char
  · change (((26:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (19:R)*h+(-17:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (29:R)=0) (hx : x=16) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case29_16

namespace NecklaceTheta.case29_20
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 4 1 where
  side := AtlasIndices.shores8
  ht := ![1,2,1,1,1,1,1,1,2,1,0,0,0,1,1,2,2,2,2,2,3,3,3]
  lamp := ![![0],![27],![0],![9],![9],![18],![18],![27],![27],![20],![20],![21],![21],![21],![21],![21],![0],![0],![23],![23],![23],![27],![27]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 4 → Fin 1 → ℤ := ![![1],![20],![23],![25]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 13 → Fin 1 → ℤ := ![![1],![2],![3],![4],![6],![9],![11],![12],![18],![20],![21],![23],![27]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 29 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=20) (char : (29:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((20:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((23:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (-13:R)*char
  · change (((25:ℤ):R)+x*(0:R))=x^3
    rw [hx]
    push_cast; linear_combination (-275:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (29:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (15:R)*h+(-1:R)*char
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (10:R)*h+(-1:R)*char
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (22:R)*h+(-3:R)*char
  · change (((6:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h+(-1:R)*char
  · change (((9:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (13:R)*h+(-4:R)*char
  · change (((11:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (8:R)*h+(-3:R)*char
  · change (((12:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (17:R)*h+(-7:R)*char
  · change (((18:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (21:R)*h+(-13:R)*char
  · change (((20:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (16:R)*h+(-11:R)*char
  · change (((21:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (18:R)*h+(-13:R)*char
  · change (((23:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (24:R)*h+(-19:R)*char
  · change (((27:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (14:R)*h+(-13:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (29:R)=0) (hx : x=20) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case29_20

namespace NecklaceTheta.case29_23
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 2 1 where
  side := AtlasIndices.shores8
  ht := ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,0,0,0,0]
  lamp := ![![0],![25],![0],![28],![28],![27],![27],![26],![26],![1],![1],![2],![2],![2],![2],![25],![0],![0],![23],![23],![24],![24],![25]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 2 → Fin 1 → ℤ := ![![1],![23]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 13 → Fin 1 → ℤ := ![![1],![2],![3],![4],![5],![21],![22],![23],![24],![25],![26],![27],![28]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 29 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=23) (char : (29:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((23:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (29:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((2:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (15:R)*h+(-1:R)*char
  · change (((3:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (10:R)*h+(-1:R)*char
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (22:R)*h+(-3:R)*char
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-1:R)*char
  · change (((21:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (18:R)*h+(-13:R)*char
  · change (((22:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (4:R)*h+(-3:R)*char
  · change (((23:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (24:R)*h+(-19:R)*char
  · change (((24:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (23:R)*h+(-19:R)*char
  · change (((25:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (7:R)*h+(-6:R)*char
  · change (((26:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (19:R)*h+(-17:R)*char
  · change (((27:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (14:R)*h+(-13:R)*char
  · change (((28:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (28:R)*h+(-27:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (29:R)=0) (hx : x=23) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case29_23

namespace NecklaceTheta.case29_24
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 4 1 where
  side := AtlasIndices.shores8
  ht := ![1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,1,2,2,3,3,3,2,2]
  lamp := ![![0],![20],![0],![5],![5],![10],![10],![15],![15],![24],![24],![19],![19],![20],![20],![20],![0],![0],![0],![0],![20],![20],![20]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 4 → Fin 1 → ℤ := ![![1],![24],![25],![20]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 10 → Fin 1 → ℤ := ![![1],![4],![5],![9],![10],![14],![15],![19],![20],![24]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 29 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=24) (char : (29:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((24:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((25:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (-19:R)*char
  · change (((20:ℤ):R)+x*(0:R))=x^3
    rw [hx]
    push_cast; linear_combination (-476:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (29:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (22:R)*h+(-3:R)*char
  · change (((5:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (6:R)*h+(-1:R)*char
  · change (((9:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (13:R)*h+(-4:R)*char
  · change (((10:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (3:R)*h+(-1:R)*char
  · change (((14:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (27:R)*h+(-13:R)*char
  · change (((15:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (2:R)*h+(-1:R)*char
  · change (((19:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (26:R)*h+(-17:R)*char
  · change (((20:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (16:R)*h+(-11:R)*char
  · change (((24:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (23:R)*h+(-19:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (29:R)=0) (hx : x=24) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case29_24

namespace NecklaceTheta.case29_25
open MetabelianModule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def tbl : Table 23 8 4 1 where
  side := AtlasIndices.shores8
  ht := ![1,2,1,1,1,1,1,1,2,1,0,0,0,1,1,2,2,2,3,3,3,3,3]
  lamp := ![![0],![12],![0],![4],![4],![8],![8],![12],![12],![25],![25],![25],![24],![24],![28],![28],![0],![0],![0],![6],![6],![12],![12]]
  route := AtlasIndices.route8
  src := 0
  dst := 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def gaps : Fin 4 → Fin 1 → ℤ := ![![1],![25],![16],![23]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
def obs : Fin 12 → Fin 1 → ℤ := ![![1],![4],![6],![8],![12],![16],![17],![20],![21],![24],![25],![28]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem table_ok : Valid tbl 0 0 29 gaps obs := by
  constructor <;> decide +kernel

variable {R : Type*} [CommRing R] {x : R}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem gaps_eval (hx : x=25) (char : (29:R)=0) : ∀ i,evalVec x (gaps i)=x^i.val := by
  intro i
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=x^0
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((25:ℤ):R)+x*(0:R))=x^1
    rw [hx]
    push_cast; linear_combination (0:R)*char
  · change (((16:ℤ):R)+x*(0:R))=x^2
    rw [hx]
    push_cast; linear_combination (-21:R)*char
  · change (((23:ℤ):R)+x*(0:R))=x^3
    rw [hx]
    push_cast; linear_combination (-538:R)*char

variable [Nontrivial R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem separated (char : (29:R)=0) : ∀ i,evalVec x (obs i)≠0 := by
  intro i h
  fin_cases i
  · change (((1:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (1:R)*h+(0:R)*char
  · change (((4:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (22:R)*h+(-3:R)*char
  · change (((6:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (5:R)*h+(-1:R)*char
  · change (((8:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (11:R)*h+(-3:R)*char
  · change (((12:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (17:R)*h+(-7:R)*char
  · change (((16:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (20:R)*h+(-11:R)*char
  · change (((17:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (12:R)*h+(-7:R)*char
  · change (((20:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (16:R)*h+(-11:R)*char
  · change (((21:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (18:R)*h+(-13:R)*char
  · change (((24:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (23:R)*h+(-19:R)*char
  · change (((25:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (7:R)*h+(-6:R)*char
  · change (((28:ℤ):R)+x*(0:R))=0 at h
    push_cast at h
    apply (one_ne_zero (α := R))
    linear_combination (28:R)*h+(-27:R)*char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem theta {m : ℕ} (hm : 5 ≤ m) {V : Type*} {B : SimpleGraph V}
    (C : Chart B m 0 x) (char : (29:R)=0) (hx : x=25) : Nonempty (EqualArms.Theta B 8) :=
  tableTheta C tbl gaps obs table_ok (by omega) (.inl rfl)
    (by simpa only [Nat.cast_ofNat] using char) (gaps_eval hx char) (separated char)

end NecklaceTheta.case29_25

namespace NecklaceTheta
open MetabelianModule

set_option maxHeartbeats 1000000 in
theorem ringrow0 {R : Type*} [CommRing R] [Nontrivial R] {x : R} {m : ℕ}
    (odd : Odd m) (period : x^m=1) (two : IsUnit (2:R)) (_reg : IsUnit (x-1))
    (hf : badA x 0=0) (j : Fin 17) (hg : badB x j=0) :
    ((7:R)=0 ∧ x=2) ∨ ((7:R)=0 ∧ x=4) ∨ ((11:R)=0 ∧ x=3) ∨ ((11:R)=0 ∧ x=4) ∨ ((11:R)=0 ∧ x=5) ∨ ((11:R)=0 ∧ x=9) ∨ ((13:R)=0 ∧ x=3) ∨ ((13:R)=0 ∧ x=9) ∨ ((19:R)=0 ∧ x=4) ∨ ((19:R)=0 ∧ x=5) ∨ ((19:R)=0 ∧ x=6) ∨ ((19:R)=0 ∧ x=7) ∨ ((19:R)=0 ∧ x=9) ∨ ((19:R)=0 ∧ x=11) ∨ ((19:R)=0 ∧ x=16) ∨ ((19:R)=0 ∧ x=17) ∨ ((29:R)=0 ∧ x=7) ∨ ((29:R)=0 ∧ x=16) ∨ ((29:R)=0 ∧ x=20) ∨ ((29:R)=0 ∧ x=23) ∨ ((29:R)=0 ∧ x=24) ∨ ((29:R)=0 ∧ x=25) := by
  have ux := unit_period odd period
  have un (k : ℕ) := unit_sum_pow odd period two k
  change -2*x+1=0 at hf
  fin_cases j
  · change (-x^2-2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^1)) := (un 1)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x-3)*hf + (2)*hg
  · change (x^2-2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^2)) := (un 2)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-1)*hf + (1)*hg
  · change (-x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^1)) := (un 1)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-1)*hf + (1)*hg
  · change (-x^2-x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^2)) := (un 2)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x-1)*hf + (1)*hg
  · change (x^2-x+2:R)=0 at hg
    right; left; constructor
    · linear_combination (2*x-1)*hf + (4)*hg
    · apply sub_eq_zero.mp
      linear_combination (-x)*hf + (-2)*hg
  · change (-x^2+2:R)=0 at hg
    right; left; constructor
    · linear_combination (-2*x-1)*hf + (4)*hg
    · apply sub_eq_zero.mp
      linear_combination (x)*hf + (-2)*hg
  · change (x^2+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^1)*(1+x^1)) := ((un 1)).mul (un 1)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-1)*hf + (1)*hg
  · change (x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have u2 : IsUnit (2:R) := by convert (two.pow 1) using 1; norm_num
    have unit : IsUnit ((1+x^2)*(2:R)) := ((un 2)).mul u2
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x)*hf + (1)*hg
  · change (-x^2+x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^1)*(1+x^1)) := ((un 1)).mul (un 1)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x-1)*hf + (1)*hg
  · change (x^2+x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have u2 : IsUnit (8:R) := by convert (two.pow 3) using 1; norm_num
    have unit : IsUnit ((1+x^5)*(8:R)) := ((un 5)).mul u2
    apply unit.mul_right_eq_zero.mp
    linear_combination (-4*x^4-2*x^3-x^2+x+2)*hf + (3)*hg
  · change (-x^2+2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have u2 : IsUnit (8:R) := by convert (two.pow 3) using 1; norm_num
    have unit : IsUnit ((1+x^5)*(8:R)) := ((un 5)).mul u2
    apply unit.mul_right_eq_zero.mp
    linear_combination (-4*x^4-2*x^3-x^2-2*x+2)*hf + (3)*hg
  · change (x^2+2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have u2 : IsUnit (16:R) := by convert (two.pow 4) using 1; norm_num
    have unit : IsUnit ((1+x^6)*(16:R)) := ((un 6)).mul u2
    apply unit.mul_right_eq_zero.mp
    linear_combination (-8*x^5-4*x^4-2*x^3-x^2+2*x+6)*hf + (5)*hg
  · change (3:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have u2 : IsUnit (2:R) := by convert (two.pow 1) using 1; norm_num
    have unit : IsUnit ((1+x^1)*(2:R)) := ((un 1)).mul u2
    apply unit.mul_right_eq_zero.mp
    linear_combination (-1)*hf + (1)*hg
  · change (-x^2+3:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have u2 : IsUnit (8:R) := by convert (two.pow 3) using 1; norm_num
    have unit : IsUnit ((1+x^5)*(8:R)) := ((un 5)).mul u2
    apply unit.mul_right_eq_zero.mp
    linear_combination (-4*x^4-2*x^3-x^2-2*x-1)*hf + (3)*hg
  · change (x^2+3:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have u2 : IsUnit (16:R) := by convert (two.pow 4) using 1; norm_num
    have unit : IsUnit ((1+x^6)*(16:R)) := ((un 6)).mul u2
    apply unit.mul_right_eq_zero.mp
    linear_combination (-8*x^5-4*x^4-2*x^3-x^2+2*x+1)*hf + (5)*hg
  · change (-x^2+4:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have u2 : IsUnit (2:R) := by convert (two.pow 1) using 1; norm_num
    have unit : IsUnit ((1+x^2)*(1+x^1)*(2:R)) := (((un 2)).mul (un 1)).mul u2
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x^2-2*x-2)*hf + (1)*hg
  · change (x^2+4:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have u2 : IsUnit (4:R) := by convert (two.pow 2) using 1; norm_num
    have unit : IsUnit ((1+x^4)*(4:R)) := ((un 4)).mul u2
    apply unit.mul_right_eq_zero.mp
    linear_combination (-2*x^3-x^2)*hf + (1)*hg

end NecklaceTheta

namespace NecklaceTheta
open MetabelianModule

set_option maxHeartbeats 1000000 in
theorem ringrow1 {R : Type*} [CommRing R] [Nontrivial R] {x : R} {m : ℕ}
    (odd : Odd m) (period : x^m=1) (two : IsUnit (2:R)) (_reg : IsUnit (x-1))
    (hf : badA x 1=0) (j : Fin 17) (hg : badB x j=0) :
    ((7:R)=0 ∧ x=2) ∨ ((7:R)=0 ∧ x=4) ∨ ((11:R)=0 ∧ x=3) ∨ ((11:R)=0 ∧ x=4) ∨ ((11:R)=0 ∧ x=5) ∨ ((11:R)=0 ∧ x=9) ∨ ((13:R)=0 ∧ x=3) ∨ ((13:R)=0 ∧ x=9) ∨ ((19:R)=0 ∧ x=4) ∨ ((19:R)=0 ∧ x=5) ∨ ((19:R)=0 ∧ x=6) ∨ ((19:R)=0 ∧ x=7) ∨ ((19:R)=0 ∧ x=9) ∨ ((19:R)=0 ∧ x=11) ∨ ((19:R)=0 ∧ x=16) ∨ ((19:R)=0 ∧ x=17) ∨ ((29:R)=0 ∧ x=7) ∨ ((29:R)=0 ∧ x=16) ∨ ((29:R)=0 ∧ x=20) ∨ ((29:R)=0 ∧ x=23) ∨ ((29:R)=0 ∧ x=24) ∨ ((29:R)=0 ∧ x=25) := by
  have ux := unit_period odd period
  have un (k : ℕ) := unit_sum_pow odd period two k
  change -x^2-x+1=0 at hf
  fin_cases j
  · change (-x^2-2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    linear_combination (-x-3)*hf + (x+2)*hg
  · change (x^2-2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^4)) := (un 4)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x^2+x-1)*hf + (1)*hg
  · change (-x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^2)) := (un 2)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-1)*hf + (1)*hg
  · change (-x^2-x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    linear_combination (-1)*hf + (1)*hg
  · change (x^2-x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^5)) := (un 5)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x^3+x^2-x+1)*hf + (x)*hg
  · change (-x^2+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    linear_combination (-x+1)*hf + (x)*hg
  · change (x^2+2:R)=0 at hg
    right; right; left; constructor
    · linear_combination (x+3)*hf + (x+4)*hg
    · apply sub_eq_zero.mp
      linear_combination (-1)*hf + (-1)*hg
  · change (x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    linear_combination (-1)*hf + (-x+1)*hg
  · change (-x^2+x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^2)) := (un 2)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x+1)*hf + (x)*hg
  · change (x^2+x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^4)) := (un 4)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x^2-1)*hf + (-x+1)*hg
  · change (-x^2+2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^5)) := (un 5)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x^3+x^2-x-1)*hf + (-x+1)*hg
  · change (x^2+2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^2)) := (un 2)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x-1)*hf + (-x+1)*hg
  · change (3:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^4)) := (un 4)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x^2+x-2)*hf + (-x+1)*hg
  · change (-x^2+3:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    linear_combination (x-2)*hf + (-x+1)*hg
  · change (x^2+3:R)=0 at hg
    right; right; right; right; right; right; right; right; left; constructor
    · linear_combination (x+4)*hf + (x+5)*hg
    · apply sub_eq_zero.mp
      linear_combination (-1)*hf + (-1)*hg
  · change (-x^2+4:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^2)) := (un 2)
    apply unit.mul_right_eq_zero.mp
    linear_combination (x-3)*hf + (-x+1)*hg
  · change (x^2+4:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^7)) := (un 7)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x^5+x^4-2*x^3+3*x^2-3*x+5)*hf + (2*x-1)*hg

end NecklaceTheta

namespace NecklaceTheta
open MetabelianModule

set_option maxHeartbeats 1000000 in
theorem ringrow2 {R : Type*} [CommRing R] [Nontrivial R] {x : R} {m : ℕ}
    (odd : Odd m) (period : x^m=1) (two : IsUnit (2:R)) (_reg : IsUnit (x-1))
    (hf : badA x 2=0) (j : Fin 17) (hg : badB x j=0) :
    ((7:R)=0 ∧ x=2) ∨ ((7:R)=0 ∧ x=4) ∨ ((11:R)=0 ∧ x=3) ∨ ((11:R)=0 ∧ x=4) ∨ ((11:R)=0 ∧ x=5) ∨ ((11:R)=0 ∧ x=9) ∨ ((13:R)=0 ∧ x=3) ∨ ((13:R)=0 ∧ x=9) ∨ ((19:R)=0 ∧ x=4) ∨ ((19:R)=0 ∧ x=5) ∨ ((19:R)=0 ∧ x=6) ∨ ((19:R)=0 ∧ x=7) ∨ ((19:R)=0 ∧ x=9) ∨ ((19:R)=0 ∧ x=11) ∨ ((19:R)=0 ∧ x=16) ∨ ((19:R)=0 ∧ x=17) ∨ ((29:R)=0 ∧ x=7) ∨ ((29:R)=0 ∧ x=16) ∨ ((29:R)=0 ∧ x=20) ∨ ((29:R)=0 ∧ x=23) ∨ ((29:R)=0 ∧ x=24) ∨ ((29:R)=0 ∧ x=25) := by
  have ux := unit_period odd period
  have un (k : ℕ) := unit_sum_pow odd period two k
  change x^2-x+1=0 at hf
  fin_cases j
  · change (-x^2-2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^1)*(1+x^1)) := ((un 1)).mul (un 1)
    apply unit.mul_right_eq_zero.mp
    linear_combination (x+3)*hf + (x-1)*hg
  · change (x^2-2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    linear_combination (-x+1)*hf + (x)*hg
  · change (-x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^1)) := (un 1)
    apply unit.mul_right_eq_zero.mp
    linear_combination (1)*hf + (x)*hg
  · change (-x^2-x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^3)) := (un 3)
    apply unit.mul_right_eq_zero.mp
    linear_combination (x+1)*hf + (0)*hg
  · change (x^2-x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    linear_combination (-1)*hf + (1)*hg
  · change (-x^2+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^3)) := (un 3)
    apply unit.mul_right_eq_zero.mp
    linear_combination (x+1)*hf + (0)*hg
  · change (x^2+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^1)) := (un 1)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-1)*hf + (1)*hg
  · change (x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^3)) := (un 3)
    apply unit.mul_right_eq_zero.mp
    linear_combination (x+1)*hf + (0)*hg
  · change (-x^2+x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^1)*(1+x^1)) := ((un 1)).mul (un 1)
    apply unit.mul_right_eq_zero.mp
    linear_combination (x+1)*hf + (x)*hg
  · change (x^2+x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^3)) := (un 3)
    apply unit.mul_right_eq_zero.mp
    linear_combination (x+1)*hf + (0)*hg
  · change (-x^2+2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^3)) := (un 3)
    apply unit.mul_right_eq_zero.mp
    linear_combination (x+1)*hf + (0)*hg
  · change (x^2+2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^3)) := (un 3)
    apply unit.mul_right_eq_zero.mp
    linear_combination (x+1)*hf + (0)*hg
  · change (3:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^1)*(1+x^1)) := ((un 1)).mul (un 1)
    apply unit.mul_right_eq_zero.mp
    linear_combination (1)*hf + (x)*hg
  · change (-x^2+3:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^3)) := (un 3)
    apply unit.mul_right_eq_zero.mp
    linear_combination (x+1)*hf + (0)*hg
  · change (x^2+3:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^3)) := (un 3)
    apply unit.mul_right_eq_zero.mp
    linear_combination (x+1)*hf + (0)*hg
  · change (-x^2+4:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^3)) := (un 3)
    apply unit.mul_right_eq_zero.mp
    linear_combination (x+1)*hf + (0)*hg
  · change (x^2+4:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^3)) := (un 3)
    apply unit.mul_right_eq_zero.mp
    linear_combination (x+1)*hf + (0)*hg

end NecklaceTheta

namespace NecklaceTheta
open MetabelianModule

set_option maxHeartbeats 1000000 in
theorem ringrow3 {R : Type*} [CommRing R] [Nontrivial R] {x : R} {m : ℕ}
    (odd : Odd m) (period : x^m=1) (two : IsUnit (2:R)) (_reg : IsUnit (x-1))
    (hf : badA x 3=0) (j : Fin 17) (hg : badB x j=0) :
    ((7:R)=0 ∧ x=2) ∨ ((7:R)=0 ∧ x=4) ∨ ((11:R)=0 ∧ x=3) ∨ ((11:R)=0 ∧ x=4) ∨ ((11:R)=0 ∧ x=5) ∨ ((11:R)=0 ∧ x=9) ∨ ((13:R)=0 ∧ x=3) ∨ ((13:R)=0 ∧ x=9) ∨ ((19:R)=0 ∧ x=4) ∨ ((19:R)=0 ∧ x=5) ∨ ((19:R)=0 ∧ x=6) ∨ ((19:R)=0 ∧ x=7) ∨ ((19:R)=0 ∧ x=9) ∨ ((19:R)=0 ∧ x=11) ∨ ((19:R)=0 ∧ x=16) ∨ ((19:R)=0 ∧ x=17) ∨ ((29:R)=0 ∧ x=7) ∨ ((29:R)=0 ∧ x=16) ∨ ((29:R)=0 ∧ x=20) ∨ ((29:R)=0 ∧ x=23) ∨ ((29:R)=0 ∧ x=24) ∨ ((29:R)=0 ∧ x=25) := by
  have ux := unit_period odd period
  have un (k : ℕ) := unit_sum_pow odd period two k
  change -x^2+x+1=0 at hf
  fin_cases j
  · change (-x^2-2*x+2:R)=0 at hg
    right; right; right; left; constructor
    · linear_combination (3*x+7)*hf + (-3*x+2)*hg
    · apply sub_eq_zero.mp
      linear_combination (-x-2)*hf + (x-1)*hg
  · change (x^2-2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^2)) := (un 2)
    apply unit.mul_right_eq_zero.mp
    linear_combination (x-1)*hf + (x+1)*hg
  · change (-x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    linear_combination (-1)*hf + (x+1)*hg
  · change (-x^2-x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^2)) := (un 2)
    apply unit.mul_right_eq_zero.mp
    linear_combination (x+1)*hf + (-x)*hg
  · change (x^2-x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^4)) := (un 4)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x^2-1)*hf + (x+1)*hg
  · change (-x^2+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    linear_combination (x+1)*hf + (-x)*hg
  · change (x^2+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^5)) := (un 5)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x^3-x^2-x-1)*hf + (x+1)*hg
  · change (x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^2)) := (un 2)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-1)*hf + (1)*hg
  · change (-x^2+x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    linear_combination (-1)*hf + (1)*hg
  · change (x^2+x+2:R)=0 at hg
    right; right; right; left; constructor
    · linear_combination (-2*x+1)*hf + (-2*x+5)*hg
    · apply sub_eq_zero.mp
      linear_combination (x)*hf + (x-2)*hg
  · change (-x^2+2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    linear_combination (x-3)*hf + (-x+2)*hg
  · change (x^2+2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^4)) := (un 4)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x^2-x-1)*hf + (1)*hg
  · change (3:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^4)) := (un 4)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x^2-x-2)*hf + (x+1)*hg
  · change (-x^2+3:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    linear_combination (-x-2)*hf + (x+1)*hg
  · change (x^2+3:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^9)) := (un 9)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x^7-x^6-2*x^5-3*x^4-5*x^3-8*x^2-7*x-11)*hf + (6*x+4)*hg
  · change (-x^2+4:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^2)) := (un 2)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x-3)*hf + (x+1)*hg
  · change (x^2+4:R)=0 at hg
    right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; constructor
    · linear_combination (-x+5)*hf + (-x+6)*hg
    · apply sub_eq_zero.mp
      linear_combination (x-4)*hf + (x-5)*hg

end NecklaceTheta

namespace NecklaceTheta
open MetabelianModule

set_option maxHeartbeats 1000000 in
theorem ringrow4 {R : Type*} [CommRing R] [Nontrivial R] {x : R} {m : ℕ}
    (odd : Odd m) (period : x^m=1) (two : IsUnit (2:R)) (reg : IsUnit (x-1))
    (hf : badA x 4=0) (j : Fin 17) (hg : badB x j=0) :
    ((7:R)=0 ∧ x=2) ∨ ((7:R)=0 ∧ x=4) ∨ ((11:R)=0 ∧ x=3) ∨ ((11:R)=0 ∧ x=4) ∨ ((11:R)=0 ∧ x=5) ∨ ((11:R)=0 ∧ x=9) ∨ ((13:R)=0 ∧ x=3) ∨ ((13:R)=0 ∧ x=9) ∨ ((19:R)=0 ∧ x=4) ∨ ((19:R)=0 ∧ x=5) ∨ ((19:R)=0 ∧ x=6) ∨ ((19:R)=0 ∧ x=7) ∨ ((19:R)=0 ∧ x=9) ∨ ((19:R)=0 ∧ x=11) ∨ ((19:R)=0 ∧ x=16) ∨ ((19:R)=0 ∧ x=17) ∨ ((29:R)=0 ∧ x=7) ∨ ((29:R)=0 ∧ x=16) ∨ ((29:R)=0 ∧ x=20) ∨ ((29:R)=0 ∧ x=23) ∨ ((29:R)=0 ∧ x=24) ∨ ((29:R)=0 ∧ x=25) := by
  have ux := unit_period odd period
  have un (k : ℕ) := unit_sum_pow odd period two k
  change x^2+x+1=0 at hf
  fin_cases j
  · change (-x^2-2*x+2:R)=0 at hg
    right; right; right; right; right; right; left; constructor
    · linear_combination (x+5)*hf + (x+4)*hg
    · apply sub_eq_zero.mp
      linear_combination (-1)*hf + (-1)*hg
  · change (x^2-2*x+2:R)=0 at hg
    right; right; right; right; right; right; right; left; constructor
    · linear_combination (-3*x+5)*hf + (3*x+4)*hg
    · apply sub_eq_zero.mp
      linear_combination (2*x-3)*hf + (-2*x-3)*hg
  · change (-x+2:R)=0 at hg
    left; constructor
    · linear_combination (1)*hf + (x+3)*hg
    · apply sub_eq_zero.mp
      linear_combination (0)*hf + (-1)*hg
  · change (-x^2-x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((x-1)*(x-1)) := ((reg)).mul (reg)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x+1)*hf + (-x)*hg
  · change (x^2-x+2:R)=0 at hg
    right; left; constructor
    · linear_combination (-2*x+1)*hf + (2*x+3)*hg
    · apply sub_eq_zero.mp
      linear_combination (x)*hf + (-x-2)*hg
  · change (-x^2+2:R)=0 at hg
    right; left; constructor
    · linear_combination (-x+3)*hf + (-x+2)*hg
    · apply sub_eq_zero.mp
      linear_combination (x-2)*hf + (x-1)*hg
  · change (x^2+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((x-1)) := (reg)
    apply unit.mul_right_eq_zero.mp
    linear_combination (1)*hf + (-1)*hg
  · change (x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((x-1)) := (reg)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-1)*hf + (x)*hg
  · change (-x^2+x+2:R)=0 at hg
    left; constructor
    · linear_combination (-2*x+5)*hf + (-2*x+1)*hg
    · apply sub_eq_zero.mp
      linear_combination (x-2)*hf + (x)*hg
  · change (x^2+x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    linear_combination (-1)*hf + (1)*hg
  · change (-x^2+2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((x-1)*(x-1)) := ((reg)).mul (reg)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x+3)*hf + (-x-1)*hg
  · change (x^2+2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    linear_combination (x+1)*hf + (-x)*hg
  · change (3:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((x-1)*(x-1)) := ((reg)).mul (reg)
    apply unit.mul_right_eq_zero.mp
    linear_combination (1)*hf + (-x)*hg
  · change (-x^2+3:R)=0 at hg
    right; right; right; right; right; right; right; left; constructor
    · linear_combination (-x+4)*hf + (-x+3)*hg
    · apply sub_eq_zero.mp
      linear_combination (x-3)*hf + (x-2)*hg
  · change (x^2+3:R)=0 at hg
    left; constructor
    · linear_combination (-x-2)*hf + (x+3)*hg
    · apply sub_eq_zero.mp
      linear_combination (1)*hf + (-1)*hg
  · change (-x^2+4:R)=0 at hg
    left; constructor
    · have unit : IsUnit ((x-1)) := (reg)
      apply unit.mul_right_eq_zero.mp
      linear_combination (2*x-3)*hf + (2*x-1)*hg
    · apply sub_eq_zero.mp
      have unit : IsUnit ((x-1)) := (reg)
      apply unit.mul_right_eq_zero.mp
      linear_combination (-x+2)*hf + (-x)*hg
  · change (x^2+4:R)=0 at hg
    right; right; right; right; right; right; left; constructor
    · linear_combination (-x-3)*hf + (x+4)*hg
    · apply sub_eq_zero.mp
      linear_combination (1)*hf + (-1)*hg

end NecklaceTheta

namespace NecklaceTheta
open MetabelianModule

set_option maxHeartbeats 1000000 in
theorem ringrow5 {R : Type*} [CommRing R] [Nontrivial R] {x : R} {m : ℕ}
    (odd : Odd m) (period : x^m=1) (two : IsUnit (2:R)) (reg : IsUnit (x-1))
    (hf : badA x 5=0) (j : Fin 17) (hg : badB x j=0) :
    ((7:R)=0 ∧ x=2) ∨ ((7:R)=0 ∧ x=4) ∨ ((11:R)=0 ∧ x=3) ∨ ((11:R)=0 ∧ x=4) ∨ ((11:R)=0 ∧ x=5) ∨ ((11:R)=0 ∧ x=9) ∨ ((13:R)=0 ∧ x=3) ∨ ((13:R)=0 ∧ x=9) ∨ ((19:R)=0 ∧ x=4) ∨ ((19:R)=0 ∧ x=5) ∨ ((19:R)=0 ∧ x=6) ∨ ((19:R)=0 ∧ x=7) ∨ ((19:R)=0 ∧ x=9) ∨ ((19:R)=0 ∧ x=11) ∨ ((19:R)=0 ∧ x=16) ∨ ((19:R)=0 ∧ x=17) ∨ ((29:R)=0 ∧ x=7) ∨ ((29:R)=0 ∧ x=16) ∨ ((29:R)=0 ∧ x=20) ∨ ((29:R)=0 ∧ x=23) ∨ ((29:R)=0 ∧ x=24) ∨ ((29:R)=0 ∧ x=25) := by
  have ux := unit_period odd period
  have un (k : ℕ) := unit_sum_pow odd period two k
  change 2*x+1=0 at hf
  fin_cases j
  · change (-x^2-2*x+2:R)=0 at hg
    right; right; right; right; left; constructor
    · linear_combination (2*x+3)*hf + (4)*hg
    · apply sub_eq_zero.mp
      linear_combination (-x-1)*hf + (-2)*hg
  · change (x^2-2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have u2 : IsUnit (16:R) := by convert (two.pow 4) using 1; norm_num
    have unit : IsUnit ((1+x^6)*(16:R)) := ((un 6)).mul u2
    apply unit.mul_right_eq_zero.mp
    linear_combination (8*x^5-4*x^4+2*x^3-x^2-2*x+6)*hf + (5)*hg
  · change (-x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have u2 : IsUnit (2:R) := by convert (two.pow 1) using 1; norm_num
    have unit : IsUnit ((1+x^2)*(2:R)) := ((un 2)).mul u2
    apply unit.mul_right_eq_zero.mp
    linear_combination (x)*hf + (1)*hg
  · change (-x^2-x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((x-1)*(x-1)) := ((reg)).mul (reg)
    apply unit.mul_right_eq_zero.mp
    linear_combination (x-1)*hf + (1)*hg
  · change (x^2-x+2:R)=0 at hg
    right; right; right; right; left; constructor
    · linear_combination (-2*x+3)*hf + (4)*hg
    · apply sub_eq_zero.mp
      linear_combination (x-1)*hf + (-2)*hg
  · change (-x^2+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have u2 : IsUnit (2:R) := by convert (two.pow 1) using 1; norm_num
    have unit : IsUnit ((1+x^3)*(2:R)) := ((un 3)).mul u2
    apply unit.mul_right_eq_zero.mp
    linear_combination (x^2)*hf + (1)*hg
  · change (x^2+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((x-1)*(x-1)) := ((reg)).mul (reg)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-1)*hf + (1)*hg
  · change (x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((x-1)) := (reg)
    apply unit.mul_right_eq_zero.mp
    linear_combination (1)*hf + (-1)*hg
  · change (-x^2+x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^2)) := (un 2)
    apply unit.mul_right_eq_zero.mp
    linear_combination (x-1)*hf + (1)*hg
  · change (x^2+x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have u2 : IsUnit (2:R) := by convert (two.pow 1) using 1; norm_num
    have unit : IsUnit ((1+x^3)*(2:R)) := ((un 3)).mul u2
    apply unit.mul_right_eq_zero.mp
    linear_combination (x^2-x)*hf + (1)*hg
  · change (-x^2+2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((x-1)) := (reg)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-x+3)*hf + (-2)*hg
  · change (x^2+2*x+2:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have unit : IsUnit ((1+x^2)) := (un 2)
    apply unit.mul_right_eq_zero.mp
    linear_combination (-1)*hf + (1)*hg
  · change (3:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have u2 : IsUnit (2:R) := by convert (two.pow 1) using 1; norm_num
    have unit : IsUnit ((x-1)*(2:R)) := ((reg)).mul u2
    apply unit.mul_right_eq_zero.mp
    linear_combination (1)*hf + (-1)*hg
  · change (-x^2+3:R)=0 at hg
    right; right; right; right; left; constructor
    · linear_combination (2*x-1)*hf + (4)*hg
    · apply sub_eq_zero.mp
      linear_combination (-x+1)*hf + (-2)*hg
  · change (x^2+3:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have u2 : IsUnit (16:R) := by convert (two.pow 4) using 1; norm_num
    have unit : IsUnit ((1+x^6)*(16:R)) := ((un 6)).mul u2
    apply unit.mul_right_eq_zero.mp
    linear_combination (8*x^5-4*x^4+2*x^3-x^2-2*x+1)*hf + (5)*hg
  · change (-x^2+4:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have u2 : IsUnit (2:R) := by convert (two.pow 1) using 1; norm_num
    have unit : IsUnit ((1+x^2)*(x-1)*(2:R)) := (((un 2)).mul (reg)).mul u2
    apply unit.mul_right_eq_zero.mp
    linear_combination (x^2-2*x+2)*hf + (-1)*hg
  · change (x^2+4:R)=0 at hg
    exfalso
    apply (one_ne_zero (α := R))
    have u2 : IsUnit (4:R) := by convert (two.pow 2) using 1; norm_num
    have unit : IsUnit ((1+x^4)*(4:R)) := ((un 4)).mul u2
    apply unit.mul_right_eq_zero.mp
    linear_combination (2*x^3-x^2)*hf + (1)*hg

end NecklaceTheta

namespace NecklaceTheta
open EqualArms MetabelianModule MetabelianRegular

variable {R V : Type*} [CommRing R] [Nontrivial R] {x : R} {m : ℕ} {B : SimpleGraph V}

theorem chart_wide (C : Chart B m 0 x) (hm : 5 ≤ m) (odd : Odd m) (period : x^m=1)
    (two : IsUnit (2:R)) (reg : IsUnit (x-1)) :
    Nonempty (Theta B 8) ∨ Nonempty (Theta B 16) := by
  classical
  by_cases goodA : ∀ i,badA x i≠0
  · exact .inr (wideA.theta hm odd period two reg goodA C)
  by_cases goodB : ∀ i,badB x i≠0
  · exact .inr (wideB.theta hm odd period two reg goodB C)
  push Not at goodA goodB
  obtain ⟨i,hf⟩ := goodA
  obtain ⟨j,hg⟩ := goodB
  have residual : ((7:R)=0 ∧ x=2) ∨ ((7:R)=0 ∧ x=4) ∨ ((11:R)=0 ∧ x=3) ∨ ((11:R)=0 ∧ x=4) ∨ ((11:R)=0 ∧ x=5) ∨ ((11:R)=0 ∧ x=9) ∨ ((13:R)=0 ∧ x=3) ∨ ((13:R)=0 ∧ x=9) ∨ ((19:R)=0 ∧ x=4) ∨ ((19:R)=0 ∧ x=5) ∨ ((19:R)=0 ∧ x=6) ∨ ((19:R)=0 ∧ x=7) ∨ ((19:R)=0 ∧ x=9) ∨ ((19:R)=0 ∧ x=11) ∨ ((19:R)=0 ∧ x=16) ∨ ((19:R)=0 ∧ x=17) ∨ ((29:R)=0 ∧ x=7) ∨ ((29:R)=0 ∧ x=16) ∨ ((29:R)=0 ∧ x=20) ∨ ((29:R)=0 ∧ x=23) ∨ ((29:R)=0 ∧ x=24) ∨ ((29:R)=0 ∧ x=25) := by
    fin_cases i <;> first
      | exact ringrow0 odd period two reg hf j hg
      | exact ringrow1 odd period two reg hf j hg
      | exact ringrow2 odd period two reg hf j hg
      | exact ringrow3 odd period two reg hf j hg
      | exact ringrow4 odd period two reg hf j hg
      | exact ringrow5 odd period two reg hf j hg
  rcases residual with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact .inl (case7_2.theta hm C h.1 h.2)
  · exact .inl (case7_4.theta hm C h.1 h.2)
  · exact .inl (case11_3.theta hm C h.1 h.2)
  · exact .inl (case11_4.theta hm C h.1 h.2)
  · exact .inl (case11_5.theta hm C h.1 h.2)
  · exact .inl (case11_9.theta hm C h.1 h.2)
  · exact .inl (case13_3.theta hm C h.1 h.2)
  · exact .inl (case13_9.theta hm C h.1 h.2)
  · exact .inl (case19_4.theta hm C h.1 h.2)
  · exact .inl (case19_5.theta hm C h.1 h.2)
  · exact .inl (case19_6.theta hm C h.1 h.2)
  · exact .inl (case19_7.theta hm C h.1 h.2)
  · exact .inl (case19_9.theta hm C h.1 h.2)
  · exact .inl (case19_11.theta hm C h.1 h.2)
  · exact .inl (case19_16.theta hm C h.1 h.2)
  · exact .inl (case19_17.theta hm C h.1 h.2)
  · exact .inl (case29_7.theta hm C h.1 h.2)
  · exact .inl (case29_16.theta hm C h.1 h.2)
  · exact .inl (case29_20.theta hm C h.1 h.2)
  · exact .inl (case29_23.theta hm C h.1 h.2)
  · exact .inl (case29_24.theta hm C h.1 h.2)
  · exact .inl (case29_25.theta hm C h.1 h.2)

theorem all_charts (C : Chart B m 0 x) (hm : 3 ≤ m) (odd : Odd m) (period : x^m=1)
    (two : IsUnit (2:R)) (reg : IsUnit (x-1)) :
    Nonempty (Theta B 8) ∨ Nonempty (Theta B 16) := by
  by_cases eq : m=3
  · subst m
    exact chart_three C period two reg
  · apply chart_wide C _ odd period two reg
    obtain ⟨k,h⟩ := odd
    omega

end NecklaceTheta

/- Recover the chart from the commutator subgroup of the original group. -/
namespace MetabelianModule
open scoped IsMulCommutative
open Subgroup
variable {G : Type*} [Group G]

lemma pair_commutative {a b : G} (gen : closure ({a,b} : Set G)=⊤) (h : Commute a b) :
    IsMulCommutative G := by
  have hc : IsMulCommutative (closure ({a,b} : Set G)) := by
    apply isMulCommutative_closure
    intro x hx y hy
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> first | rfl | exact h.eq | exact h.symm.eq
  rw [gen] at hc
  let _ := hc
  exact ⟨⟨fun x y => congrArg Subtype.val (mul_comm' (⟨x,trivial⟩ : (⊤ : Subgroup G)) ⟨y,trivial⟩)⟩⟩

lemma pair_map_top {a b : G} (gen : closure ({a,b} : Set G)=⊤) {Q : Type*} [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) : closure ({f a,f b} : Set Q)=⊤ := by
  have h := congrArg (Subgroup.map f) gen
  simpa only [MonoidHom.map_closure, Set.image_insert_eq,Set.image_singleton,
    Subgroup.map_top_of_surjective f hf] using h

noncomputable section
variable [IsMulCommutative (commutator G)]

abbrev conjD (a : G) : MulAut (commutator G) := MulAut.conjNormal a
def diffD (a : G) : commutator G →* commutator G :=
  (conjD a).toMonoidHom / MonoidHom.id _

@[simp] lemma diffD_apply (a : G) (d : commutator G) : diffD a d=conjD a d / d := rfl

lemma conjugation_fixed [Finite G] (a b : G) (j : ℕ)
    (gen : closure ({a,b} : Set G)=⊤) (u : commutator G) (bu : b=u.val*a^j) :
    ∀ z : commutator G,conjD a z=z → z=1 := by
  let H : Subgroup G := ((commutator G).subtype.comp (diffD a)).range
  have aH : a ∈ normalizer (H : Set G) := by
    apply mem_normalizer_fintype
    rintro g ⟨w,rfl⟩
    refine ⟨conjD a w,?_⟩
    change ((conjD a (conjD a w) / conjD a w : commutator G) : G) =
      a * ((diffD a w : commutator G) : G) * a⁻¹
    rw [← MulAut.conjNormal_apply]
    exact congrArg Subtype.val (map_div (conjD a) (conjD a w) w).symm
  have uH : u.val ∈ normalizer (H : Set G) := by
    apply mem_normalizer_fintype
    rintro g ⟨w,rfl⟩
    refine ⟨w,?_⟩
    exact congrArg Subtype.val (show diffD a w = u * diffD a w * u⁻¹ by rw [mul_comm u]; group)
  have hn : H.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←gen,Subgroup.closure_le]
    intro z hz
    rcases (Set.mem_insert_iff.mp hz) with rfl|hz
    · exact aH
    · obtain rfl := Set.mem_singleton_iff.mp hz
      rw [bu]
      exact mul_mem uH (pow_mem aH j)
  let _ := hn
  let f := QuotientGroup.mk' H
  have e : Commute (f a) (f u.val) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [←map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨u,by simp [commutatorElement_def,diffD_apply,div_eq_mul_inv,conjD]⟩
  have comm : IsMulCommutative (G ⧸ H) := by
    apply pair_commutative (pair_map_top gen f (QuotientGroup.mk'_surjective H))
    rw [bu,map_mul,map_pow]
    exact e.mul_right (Commute.self_pow _ _)
  have dh : commutator G ≤ H := Subgroup.Normal.quotient_commutative_iff_commutator_le.mp comm
  have surj : Function.Surjective (diffD a) := by
    intro z
    obtain ⟨y,eq⟩ := dh z.property
    exact ⟨y,Subtype.ext eq⟩
  have inj := Finite.injective_iff_surjective.mpr surj
  intro z hz
  apply inj
  simp [hz]

omit [IsMulCommutative (commutator G)] in
lemma in_derived {x : G} (h : Abelianization.of x=1) : x ∈ commutator G := by
  rw [←Abelianization.ker_of]; exact h

omit [IsMulCommutative (commutator G)] in
lemma projected_one (z : commutator G) : Abelianization.of z.val=1 := by
  exact (QuotientGroup.eq_one_iff _).mpr z.property

def displacement (a b : G) (j : ℕ) (h : Abelianization.of b=(Abelianization.of a)^j) :
    commutator G := ⟨b*(a^j)⁻¹,in_derived (by simp [h])⟩

omit [IsMulCommutative (commutator G)] in
lemma displacement_mul (a b : G) (j : ℕ) (h : Abelianization.of b=(Abelianization.of a)^j) :
    b=(displacement a b j h).val*a^j := by simp [displacement]

omit [IsMulCommutative (commutator G)] in
lemma marked_order (a : G) (fix : ∀ z : commutator G,conjD a z=z → z=1) :
    orderOf a=orderOf (Abelianization.of a) := by
  let m := orderOf (Abelianization.of a)
  have hm : a^m ∈ commutator G := in_derived (by rw [map_pow]; exact pow_orderOf_eq_one _)
  let z : commutator G := ⟨a^m,hm⟩
  have ez : conjD a z=z := by
    apply Subtype.ext
    change a*a^m*a⁻¹=a^m
    rw [(Commute.self_pow a m).eq]; group
  exact Nat.dvd_antisymm (orderOf_dvd_iff_pow_eq_one.mpr (congrArg Subtype.val (fix z ez)))
    (orderOf_map_dvd _ _)

end
end MetabelianModule

namespace MetabelianModule
open scoped IsMulCommutative
open MetabelianRegular
universe u v
noncomputable section

structure Normalized {V : Type v} (B : SimpleGraph V) (m jump : ℕ) where
  R : Type
  [ring : CommRing R]
  [nontrivial : Nontrivial R]
  x : R
  chart : Chart B m jump x
  period : x^m=1
  reg : IsUnit (x-1)
  two : IsUnit (2:R)
  odd : Odd m
  lower : 3 ≤ m

instance {V : Type v} {B : SimpleGraph V} {m j : ℕ} (N : Normalized B m j) : CommRing N.R := N.ring
instance {V : Type v} {B : SimpleGraph V} {m j : ℕ} (N : Normalized B m j) : Nontrivial N.R := N.nontrivial
variable {G : Type u} [Group G] [IsMulCommutative (commutator G)]

abbrev Der (G : Type*) [Group G] := Additive (commutator G)

def derivedOp (a : G) : Module.End ℤ (Der G) :=
  (conjD a).toAdditive.toAddMonoidHom.toIntLinearMap

lemma derivedOp_pow (a : G) (h : ℕ) (z : Der G) :
    (((derivedOp a)^h) z).toMul.val = a^h * z.toMul.val * (a^h)⁻¹ := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [pow_succ',Module.End.mul_apply]
    change a * ((((derivedOp a)^h) z).toMul : G) * a⁻¹ = _
    rw [ih,pow_succ',mul_inv_rev]; group

def markedLoc (a : G) (u : Der G) (s : Bool) (h : ℕ) (z : Orbit (derivedOp a) u) : Bool × G :=
  (s,(evaluate _ u z).toMul.val*a^h)

def markedChart (a b : G) (j : ℕ) (u : Der G) (bu : b=u.toMul.val*a^j)
    (ord : orderOf a=orderOf (Abelianization.of a)) :
    Chart (rightMatching a b) (orderOf (Abelianization.of a)) j (x (derivedOp a) u) where
  loc := markedLoc a u
  sep s t h k y z hh hk e := by
    have g := congrArg Prod.snd e
    change (evaluate _ u y).toMul.val * a^h = (evaluate _ u z).toMul.val * a^k at g
    have eq := congrArg Abelianization.of g
    simp only [map_mul,map_pow,projected_one,one_mul] at eq
    have he : h=k := by
      simpa only [Nat.mod_eq_of_lt hh,Nat.mod_eq_of_lt hk] using pow_inj_mod.mp eq
    refine ⟨congrArg Prod.fst e,he,?_⟩
    subst k
    apply evaluate_injective _ _
    exact (Subtype.ext (mul_right_cancel g) : (evaluate _ u y).toMul=(evaluate _ u z).toMul)
  forward h k y z hyp := by
    apply (rightMatching_adj _ _ _ _).mpr
    have poweq {i n : ℕ} (e : i % orderOf (Abelianization.of a)=n % orderOf (Abelianization.of a)) :
        a^i=a^n := pow_inj_mod.mpr (ord.symm ▸ e)
    rcases hyp with ⟨e,rfl⟩|⟨e,rfl⟩|⟨e,rfl⟩
    · exact Or.inl (congrArg (fun w => (evaluate _ u z).toMul.val*w) (poweq e))
    · apply Or.inr; apply Or.inl
      rw [poweq e,pow_succ,mul_assoc]
    · apply Or.inr; apply Or.inr
      change (evaluate _ u (y+x (derivedOp a) u^h)).toMul.val * a^k =
        ((evaluate _ u y).toMul.val*a^h)*b
      rw [map_add,evaluate_pow]
      change ((evaluate _ u y).toMul.val * (((derivedOp a)^h) u).toMul.val) * a^k = _
      rw [derivedOp_pow,poweq e,pow_add,bu]; group

def normalForm [Finite G] (a b : G) (jump : ℕ)
    (gen : Subgroup.closure ({a,b} : Set G)=⊤) (nonab : ¬ IsMulCommutative G)
    (oddG : Odd (Nat.card G)) (offset : Abelianization.of b=(Abelianization.of a)^jump) :
    Normalized (rightMatching a b) (orderOf (Abelianization.of a)) jump := by
  let w := displacement a b jump offset
  let u : Der G := Additive.ofMul w
  let A := derivedOp a
  let m := orderOf (Abelianization.of a)
  have bu : b=w.val*a^jump := displacement_mul a b jump offset
  have fix := conjugation_fixed a b jump gen w bu
  have ord := marked_order a fix
  have ac : ¬ Commute a b := fun c => nonab (pair_commutative gen c)
  have un : u ≠ 0 := by
    intro h; apply ac
    have e : w=1 := congrArg Additive.toMul h
    rw [bu,e,Subgroup.coe_one,one_mul]
    exact Commute.self_pow _ _
  have fixed : ∀ z : Der G,A z=z → z=0 := fun z h => congrArg Additive.ofMul (fix z.toMul h)
  let _ := orbit_nontrivial A un
  have period : x A u ^ m=1 := by
    apply evaluate_injective A u
    rw [evaluate_pow,evaluate_one]
    apply (show Function.Injective (fun z : Der G => z.toMul.val) from fun _ _ e => Subtype.ext e)
    change (((derivedOp a)^m) u).toMul.val=u.toMul.val
    rw [derivedOp_pow,show a^m=1 by change a ^ orderOf (Abelianization.of a) = 1; rw [←ord,pow_orderOf_eq_one]]
    simp
  have om : Odd m := Odd.of_dvd_nat oddG (by change orderOf (Abelianization.of a) ∣ _; rw [←ord]; exact orderOf_dvd_natCard a)
  have hm : 3 ≤ m := by
    have ne : m ≠ 1 := by
      intro e
      apply ac
      have h : a=1 := orderOf_eq_one_iff.mp (ord.trans e)
      rw [h]
      exact Commute.one_left _
    obtain ⟨k,h⟩:=om; omega
  have od : Odd (Nat.card (Der G)) := Odd.of_dvd_nat oddG (Subgroup.card_subgroup_dvd_card _)
  exact ⟨Orbit A u,x A u,markedChart a b jump u bu ord,period,orbit_unit_sub_one A u fixed,
     orbit_unit_two A u od,om,hm⟩

theorem normalize [Finite G] (a b : G) (jump : ℕ)
    (gen : Subgroup.closure ({a,b} : Set G)=⊤) (nonab : ¬ IsMulCommutative G)
    (oddG : Odd (Nat.card G)) (offset : Abelianization.of b=(Abelianization.of a)^jump) :
    Nonempty (Normalized (rightMatching a b) (orderOf (Abelianization.of a)) jump) :=
  ⟨normalForm a b jump gen nonab oddG offset⟩

end
end MetabelianModule

namespace NecklaceTheta
open MetabelianModule EqualArms MetabelianRegular

theorem marked {G : Type*} [Group G] [Finite G] [IsMulCommutative (commutator G)]
    (a b : G) (gen : Subgroup.closure ({a,b} : Set G)=⊤) (nonab : ¬ IsMulCommutative G)
    (odd : Odd (Nat.card G)) (offset : Abelianization.of b=1) :
    Nonempty (Theta (rightMatching a b) 8) ∨ Nonempty (Theta (rightMatching a b) 16) := by
  obtain ⟨N⟩ := MetabelianModule.normalize a b 0 gen nonab odd (by simpa using offset)
  exact all_charts N.chart N.lower N.odd N.period N.two N.reg

end NecklaceTheta

namespace MetabelianProgression
open MetabelianModule EqualArms MetabelianRegular
variable {G : Type*} [Group G] [Finite G] [IsMulCommutative (commutator G)]

theorem intrinsic (a b : G) (gen : Subgroup.closure ({a,b} : Set G)=⊤)
    (nonab : ¬ IsMulCommutative G) (oddG : Odd (Nat.card G))
    (offset : Abelianization.of b=(Abelianization.of a)^2) :
    Nonempty (Theta (rightMatching a b) 16) ∨ Nonempty (Theta (rightMatching a b) 8) := by
  obtain ⟨n⟩ := normalize a b 2 gen nonab oddG offset
  exact chart n.chart n.lower n.odd n.period n.two n.reg

end MetabelianProgression

/- Three-step marking. Certify the five routes and their polynomial obstructions. -/
namespace SemanticThreeStep.rowA
open MetabelianModule

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
def table : Table 47 16 9 9 where
  side := AtlasIndices.shores16Indexed
  ht i := ⟨#[4,1,4,1,1,0,3,3,4,4,5,5,6,3,3,0,1,5,2,3,3,4,1,2,2,5,5,6,3,3,2,2,7,7,8,5,6,3,4,4,5,5,8,7,7,4,4][i.val]!, by decide +revert⟩
  lamp i j := ((#[#[0,0,0,0,0,0,0,0,0],#[0,-1,0,-1,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0],#[0,-1,0,0,0,0,0,0,0],#[0,-1,0,0,0,0,0,0,0],#[0,-1,0,0,0,0,0,0,0],#[1,-1,0,0,0,0,0,0,0],#[1,-1,0,0,0,0,0,0,0],#[1,-1,0,0,0,0,0,0,0],#[1,-1,0,0,0,0,0,0,0],#[1,-1,0,0,0,0,0,0,0],#[1,-1,0,0,0,0,0,0,0],#[1,-1,0,0,0,0,0,0,0],#[1,-1,0,-1,0,0,0,0,0],#[1,-1,0,-1,0,0,0,0,0],#[0,-1,0,-1,0,0,0,0,0],#[0,-1,0,-1,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0],#[0,0,-1,0,0,0,0,0,0],#[0,0,-1,0,0,0,0,0,0],#[0,0,-1,0,0,0,0,0,0],#[0,0,-1,0,0,0,0,0,0],#[0,-1,-1,0,0,0,0,0,0],#[0,-1,-1,0,0,0,0,0,0],#[0,-1,-1,0,0,0,0,0,0],#[0,-1,0,0,0,0,0,0,0],#[0,-1,0,0,0,0,0,0,0],#[0,-1,0,0,0,0,0,0,0],#[0,-1,0,-1,0,0,0,0,0],#[0,-1,0,-1,0,0,0,0,0],#[0,-1,0,-1,0,0,0,0,0],#[0,-1,0,-1,0,0,0,0,0],#[0,0,0,0,1,0,0,0,0],#[0,0,0,0,1,0,0,0,0],#[0,0,0,0,1,0,0,0,0],#[0,0,0,0,1,-1,0,0,0],#[0,0,0,0,1,-1,0,0,0],#[0,0,0,-1,1,-1,0,0,0],#[0,0,0,-1,1,-1,0,0,0],#[0,0,0,-1,1,-1,0,0,0],#[0,0,0,-1,1,-1,0,0,0],#[0,0,0,-1,1,-1,0,0,0],#[0,0,0,-1,1,0,0,0,0],#[0,0,0,-1,1,0,0,0,0],#[0,0,0,-1,1,0,0,0,0],#[0,0,0,-1,0,0,0,0,0],#[0,0,0,-1,0,0,0,0,0]] : Array (Array ℤ))[i.val]!)[j.val]!
  route c t := if t = 0 then 0 else if ht : t < 16 then ⟨2+c.val*15+(t-1),by have := c.isLt; omega⟩ else 1
  src := 0
  dst := 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
def obs (i : Fin 18) (j : Fin 9) : ℤ := ((#[#[0,0,0,0,1,-1,0,0,0],#[0,0,0,1,-1,1,0,0,0],#[0,0,0,1,0,0,0,0,0],#[0,0,1,-1,0,0,0,0,0],#[0,0,1,-1,1,-1,0,0,0],#[0,0,1,0,0,0,0,0,0],#[0,1,-1,1,0,0,0,0,0],#[0,1,0,-1,1,-1,0,0,0],#[0,1,0,0,0,0,0,0,0],#[0,1,0,0,1,-1,0,0,0],#[1,-1,0,0,-1,1,0,0,0],#[1,-1,0,0,0,0,0,0,0],#[1,-1,0,1,-1,1,0,0,0],#[1,-1,0,1,0,0,0,0,0],#[1,-1,1,-1,0,0,0,0,0],#[1,-1,1,0,0,0,0,0,0],#[1,0,0,0,0,0,0,0,0],#[1,0,0,1,0,0,0,0,0]] : Array (Array ℤ))[i.val]!)[j.val]!
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
def gap (i : Fin 9) (j : Fin 9) : ℤ := ((#[#[1,0,0,0,0,0,0,0,0],#[0,1,0,0,0,0,0,0,0],#[0,0,1,0,0,0,0,0,0],#[0,0,0,1,0,0,0,0,0],#[0,0,0,0,1,0,0,0,0],#[0,0,0,0,0,1,0,0,0],#[0,0,0,0,0,0,1,0,0],#[0,0,0,0,0,0,0,1,0],#[0,0,0,0,0,0,0,0,1]] : Array (Array ℤ))[i.val]!)[j.val]!

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem valid : Valid table 0 3 0 gap obs := by
  constructor <;> decide +kernel
end SemanticThreeStep.rowA

namespace SemanticThreeStep
variable {R : Type*} [CommRing R]

def guardPoly (x : R) := (x + 1)^1 * (x - 1)^2 * (x)^4 * (x^2 - x + 1)^1 * (x^2 + 1)^1 * (x^4 - x^3 + x^2 - x + 1)^1

theorem guardUnit (x : R) {m : ℕ} (hm : Odd m) (hx : x^m=1)
    (us : IsUnit (x-1)) (two : IsUnit (2:R)) : IsUnit (guardPoly x) := by
  have ux := MetabelianModule.unit_period hm hx
  have plus (j : ℕ) : IsUnit (x^j+1) := by
    simpa only [add_comm] using MetabelianModule.unit_sum_pow hm hx two j
  have u1 : IsUnit (x+1) := by simpa using plus 1
  have u2 := plus 2
  have u3 : IsUnit (x^2-x+1) := isUnit_of_dvd_unit ⟨x+1, by ring⟩ (plus 3)
  have u5 : IsUnit (x^4-x^3+x^2-x+1) := isUnit_of_dvd_unit ⟨x+1, by ring⟩ (plus 5)
  exact ((((((u1.pow 1).mul (us.pow 2)).mul (ux.pow 4)).mul (u3.pow 1)).mul (u2.pow 1)).mul (u5.pow 1))

def prodA (x : R) := x^15 - 2*x^14 + 2*x^13 + x^12 - 7*x^11 + 9*x^10 - 5*x^9 - 5*x^8 + 11*x^7 - 9*x^6 + 5*x^4 - 5*x^3 + x^2 + x - 1
def prodB (x : R) := x^11 - 2*x^9 + 2*x^8 - 2*x^7 - 4*x^6 + 4*x^5 - 3*x^4 - x^3 + 3*x^2 - 2*x + 1
def prodC (x : R) := x^10 - x^9 - x^8 + 3*x^7 - 3*x^6 + 2*x^5 + x^4 - 3*x^3 + 3*x^2 - 2*x + 1

theorem oneRow [Nontrivial R] (x : R) : prodA x ≠ 0 ∨ prodB x ≠ 0 ∨ prodC x ≠ 0 := by
  by_contra! h
  obtain ⟨a,b,c⟩ := h
  unfold prodA at a
  unfold prodB at b
  unfold prodC at c
  apply one_ne_zero (α := R)
  linear_combination (5568*x^10 + 696*x^9 - 16762*x^8 + 6322*x^7 + 5626*x^6 - 22562*x^5 + 14790*x^4 + 7482*x^3 - 13340*x^2 + 4640*x - 1798) * a + (-5568*x^14 + 10440*x^13 - 4118*x^12 - 14790*x^11 + 38570*x^10 - 24895*x^9 - 16164*x^8 + 36822*x^7 - 18817*x^6 - 7438*x^5 + 27343*x^4 - 7662*x^3 - 21899*x^2 + 21198*x - 3583) * b + (-5149*x^10 + 285*x^9 + 14896*x^8 - 10697*x^7 + 361*x^6 + 27626*x^5 - 25137*x^4 - 2109*x^3 + 16796*x^2 - 18354*x + 1786) * c

def phi5 (x : R) := x^4 + x^3 + x^2 + x + 1
theorem phi5_zero (x : R) (h : x^5=1) (us : IsUnit (x-1)) : phi5 x=0 := by
  apply us.mul_right_inj.mp
  unfold phi5
  linear_combination h

theorem unit5 (x : R) (h : phi5 x=0) (us : IsUnit (x-1)) : IsUnit (5:R) := by
  apply isUnit_of_dvd_unit (y := (x-1)^4) _ (us.pow _)
  refine ⟨-x^3 + x^2 - x, ?_⟩
  unfold phi5 at h
  linear_combination h
def phi7 (x : R) := x^6 + x^5 + x^4 + x^3 + x^2 + x + 1
theorem phi7_zero (x : R) (h : x^7=1) (us : IsUnit (x-1)) : phi7 x=0 := by
  apply us.mul_right_inj.mp
  unfold phi7
  linear_combination h

theorem unit7 (x : R) (h : phi7 x=0) (us : IsUnit (x-1)) : IsUnit (7:R) := by
  apply isUnit_of_dvd_unit (y := (x-1)^6) _ (us.pow _)
  refine ⟨-x^5 + 2*x^4 - 3*x^3 + 2*x^2 - x, ?_⟩
  unfold phi7 at h
  linear_combination h
end SemanticThreeStep

namespace SemanticThreeStep.rowA
open MetabelianModule
variable {R : Type*} [CommRing R]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem gap_ok (x : R)  (j : Fin 9) : evalVec x (gap j)=x^j.val := by
  fin_cases j
  · change (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^0
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^1
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^2
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^3
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^4
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^5
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^6
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^7
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0))))))))) = x^8
    push_cast; ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem obs_ok (x : R) (hu : IsUnit (guardPoly x)) (hp : prodA x≠0) (j : Fin 18) : evalVec x (obs j)≠0 := by
  intro hj
  apply hp
  apply hu.mul_right_inj.mp
  unfold guardPoly prodA
  fin_cases j
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (-x^25 + 4*x^24 - 9*x^23 + 12*x^22 - 5*x^21 - 16*x^20 + 45*x^19 - 62*x^18 + 48*x^17 + x^16 - 62*x^15 + 101*x^14 - 92*x^13 + 39*x^12 + 28*x^11 - 72*x^10 + 73*x^9 - 40*x^8 - x^7 + 25*x^6 - 26*x^5 + 13*x^4 - x^3 - 4*x^2 + 3*x - 1) * hj
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^25 - 4*x^24 + 8*x^23 - 9*x^22 + 20*x^20 - 41*x^19 + 46*x^18 - 23*x^17 - 22*x^16 + 64*x^15 - 77*x^14 + 52*x^13 - 2*x^12 - 43*x^11 + 59*x^10 - 43*x^9 + 11*x^8 + 15*x^7 - 22*x^6 + 14*x^5 - 3*x^4 - 3*x^3 + 3*x^2 - x) * hj
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^27 - 5*x^26 + 13*x^25 - 21*x^24 + 17*x^23 + 11*x^22 - 61*x^21 + 107*x^20 - 110*x^19 + 47*x^18 + 63*x^17 - 163*x^16 + 193*x^15 - 131*x^14 + 11*x^13 + 100*x^12 - 145*x^11 + 113*x^10 - 39*x^9 - 26*x^8 + 51*x^7 - 39*x^6 + 14*x^5 + 3*x^4 - 7*x^3 + 4*x^2 - x) * hj
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (-x^27 + 4*x^26 - 9*x^25 + 12*x^24 - 5*x^23 - 16*x^22 + 45*x^21 - 62*x^20 + 48*x^19 + x^18 - 62*x^17 + 101*x^16 - 92*x^15 + 39*x^14 + 28*x^13 - 72*x^12 + 73*x^11 - 40*x^10 - x^9 + 25*x^8 - 26*x^7 + 13*x^6 - x^5 - 4*x^4 + 3*x^3 - x^2) * hj
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (-x^25 + 4*x^24 - 8*x^23 + 8*x^22 + 3*x^21 - 24*x^20 + 42*x^19 - 38*x^18 + 6*x^17 + 39*x^16 - 68*x^15 + 62*x^14 - 24*x^13 - 23*x^12 + 52*x^11 - 49*x^10 + 21*x^9 + 9*x^8 - 22*x^7 + 16*x^6 - 4*x^5 - 3*x^4 + 3*x^3 - x^2) * hj
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^28 - 5*x^27 + 13*x^26 - 21*x^25 + 17*x^24 + 11*x^23 - 61*x^22 + 107*x^21 - 110*x^20 + 47*x^19 + 63*x^18 - 163*x^17 + 193*x^16 - 131*x^15 + 11*x^14 + 100*x^13 - 145*x^12 + 113*x^11 - 39*x^10 - 26*x^9 + 51*x^8 - 39*x^7 + 14*x^6 + 3*x^5 - 7*x^4 + 4*x^3 - x^2) * hj
  · change (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^27 - 4*x^26 + 8*x^25 - 9*x^24 + 20*x^22 - 41*x^21 + 46*x^20 - 23*x^19 - 22*x^18 + 64*x^17 - 77*x^16 + 52*x^15 - 2*x^14 - 43*x^13 + 59*x^12 - 43*x^11 + 11*x^10 + 15*x^9 - 22*x^8 + 14*x^7 - 3*x^6 - 3*x^5 + 3*x^4 - x^3) * hj
  · change (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (-x^25 + 4*x^24 - 8*x^23 + 9*x^22 - x^21 - 17*x^20 + 37*x^19 - 44*x^18 + 28*x^17 + 8*x^16 - 46*x^15 + 65*x^14 - 54*x^13 + 20*x^12 + 17*x^11 - 38*x^10 + 36*x^9 - 19*x^8 + x^7 + 8*x^6 - 8*x^5 + 4*x^4 - x^3) * hj
  · change (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^29 - 5*x^28 + 13*x^27 - 21*x^26 + 17*x^25 + 11*x^24 - 61*x^23 + 107*x^22 - 110*x^21 + 47*x^20 + 63*x^19 - 163*x^18 + 193*x^17 - 131*x^16 + 11*x^15 + 100*x^14 - 145*x^13 + 113*x^12 - 39*x^11 - 26*x^10 + 51*x^9 - 39*x^8 + 14*x^7 + 3*x^6 - 7*x^5 + 4*x^4 - x^3) * hj
  · change (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (-x^25 + 4*x^24 - 9*x^23 + 12*x^22 - 6*x^21 - 13*x^20 + 39*x^19 - 56*x^18 + 48*x^17 - 12*x^16 - 36*x^15 + 71*x^14 - 74*x^13 + 45*x^12 - 2*x^11 - 31*x^10 + 40*x^9 - 28*x^8 + 9*x^7 + 4*x^6 - 7*x^5 + 4*x^4 - x^3) * hj
  · change (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^25 - 4*x^24 + 9*x^23 - 12*x^22 + 6*x^21 + 12*x^20 - 36*x^19 + 50*x^18 - 42*x^17 + 11*x^16 + 26*x^15 - 51*x^14 + 50*x^13 - 28*x^12 - 2*x^11 + 21*x^10 - 23*x^9 + 12*x^8 - x^7 - 4*x^6 + 3*x^5 - x^4) * hj
  · change (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (-x^29 + 4*x^28 - 9*x^27 + 12*x^26 - 5*x^25 - 16*x^24 + 45*x^23 - 62*x^22 + 48*x^21 + x^20 - 62*x^19 + 101*x^18 - 92*x^17 + 39*x^16 + 28*x^15 - 72*x^14 + 73*x^13 - 40*x^12 - x^11 + 25*x^10 - 26*x^9 + 13*x^8 - x^7 - 4*x^6 + 3*x^5 - x^4) * hj
  · change (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^25 - 4*x^24 + 8*x^23 - 9*x^22 + x^21 + 16*x^20 - 34*x^19 + 40*x^18 - 26*x^17 - 4*x^16 + 35*x^15 - 50*x^14 + 42*x^13 - 17*x^12 - 9*x^11 + 23*x^10 - 21*x^9 + 10*x^8 - 4*x^6 + 3*x^5 - x^4) * hj
  · change (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^27 - 5*x^26 + 14*x^25 - 27*x^24 + 36*x^23 - 30*x^22 + 2*x^21 + 41*x^20 - 78*x^19 + 86*x^18 - 56*x^17 + x^16 + 51*x^15 - 74*x^14 + 61*x^13 - 25*x^12 - 10*x^11 + 27*x^10 - 24*x^9 + 11*x^8 - 4*x^6 + 3*x^5 - x^4) * hj
  · change (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (-x^27 + 4*x^26 - 8*x^25 + 8*x^24 + 3*x^23 - 24*x^22 + 42*x^21 - 38*x^20 + 6*x^19 + 39*x^18 - 68*x^17 + 62*x^16 - 24*x^15 - 23*x^14 + 52*x^13 - 49*x^12 + 21*x^11 + 9*x^10 - 22*x^9 + 16*x^8 - 4*x^7 - 3*x^6 + 3*x^5 - x^4) * hj
  · change (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^28 - 4*x^27 + 8*x^26 - 9*x^25 + 20*x^23 - 41*x^22 + 46*x^21 - 23*x^20 - 22*x^19 + 64*x^18 - 77*x^17 + 52*x^16 - 2*x^15 - 43*x^14 + 59*x^13 - 43*x^12 + 11*x^11 + 15*x^10 - 22*x^9 + 14*x^8 - 3*x^7 - 3*x^6 + 3*x^5 - x^4) * hj
  · change (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^30 - 5*x^29 + 13*x^28 - 21*x^27 + 17*x^26 + 11*x^25 - 61*x^24 + 107*x^23 - 110*x^22 + 47*x^21 + 63*x^20 - 163*x^19 + 193*x^18 - 131*x^17 + 11*x^16 + 100*x^15 - 145*x^14 + 113*x^13 - 39*x^12 - 26*x^11 + 51*x^10 - 39*x^9 + 14*x^8 + 3*x^7 - 7*x^6 + 4*x^5 - x^4) * hj
  · change (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^27 - 5*x^26 + 13*x^25 - 22*x^24 + 22*x^23 - 2*x^22 - 39*x^21 + 85*x^20 - 108*x^19 + 86*x^18 - 22*x^17 - 55*x^16 + 107*x^15 - 109*x^14 + 66*x^13 - 7*x^12 - 36*x^11 + 47*x^10 - 32*x^9 + 10*x^8 + 4*x^7 - 7*x^6 + 4*x^5 - x^4) * hj
end SemanticThreeStep.rowA

namespace SemanticThreeStep.rowB
open MetabelianModule

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
def table : Table 47 16 9 9 where
  side := AtlasIndices.shores16Indexed
  ht i := ⟨#[4,3,4,3,6,5,5,2,3,0,1,1,4,4,7,6,6,5,2,3,0,1,1,4,4,7,6,6,5,5,4,4,7,6,6,3,3,0,1,1,4,3,6,5,5,2,3][i.val]!, by decide +revert⟩
  lamp i j := ((#[#[0,0,0,0,0,0,0,0,0],#[-1,1,-1,0,1,0,0,0,0],#[0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0],#[0,0,0,1,0,0,0,0,0],#[0,0,0,1,0,0,0,0,0],#[0,0,0,1,0,0,0,0,0],#[0,0,-1,1,0,0,0,0,0],#[0,0,-1,1,0,0,0,0,0],#[-1,0,-1,1,0,0,0,0,0],#[-1,0,-1,1,0,0,0,0,0],#[-1,0,-1,1,0,0,0,0,0],#[-1,1,-1,1,0,0,0,0,0],#[-1,1,-1,1,0,0,0,0,0],#[-1,1,-1,1,1,0,0,0,0],#[-1,1,-1,1,1,0,0,0,0],#[-1,1,-1,1,1,0,0,0,0],#[0,0,0,0,0,0,0,0,0],#[0,0,-1,0,0,0,0,0,0],#[0,0,-1,0,0,0,0,0,0],#[-1,0,-1,0,0,0,0,0,0],#[-1,0,-1,0,0,0,0,0,0],#[-1,0,-1,0,0,0,0,0,0],#[-1,1,-1,0,0,0,0,0,0],#[-1,1,-1,0,0,0,0,0,0],#[-1,1,-1,0,1,0,0,0,0],#[-1,1,-1,0,1,0,0,0,0],#[-1,1,-1,0,1,0,0,0,0],#[-1,1,-1,0,1,0,0,0,0],#[-1,1,-1,0,1,0,0,0,0],#[-1,1,-1,0,1,0,0,0,0],#[-1,1,-1,0,1,0,0,0,0],#[0,0,0,0,1,0,0,0,0],#[0,0,0,0,1,0,0,0,0],#[0,0,0,0,1,0,0,0,0],#[0,0,0,-1,1,0,0,0,0],#[0,0,0,-1,1,0,0,0,0],#[-1,0,0,-1,1,0,0,0,0],#[-1,0,0,-1,1,0,0,0,0],#[-1,0,0,-1,1,0,0,0,0],#[-1,1,0,-1,1,0,0,0,0],#[-1,1,0,-1,1,0,0,0,0],#[-1,1,0,0,1,0,0,0,0],#[-1,1,0,0,1,0,0,0,0],#[-1,1,0,0,1,0,0,0,0],#[-1,1,-1,0,1,0,0,0,0],#[-1,1,-1,0,1,0,0,0,0]] : Array (Array ℤ))[i.val]!)[j.val]!
  route c t := if t = 0 then 0 else if ht : t < 16 then ⟨2+c.val*15+(t-1),by have := c.isLt; omega⟩ else 1
  src := 0
  dst := 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
def obs (i : Fin 14) (j : Fin 9) : ℤ := ((#[#[0,0,0,0,1,0,0,0,0],#[0,0,0,1,-1,0,0,0,0],#[0,0,0,1,0,0,0,0,0],#[0,0,1,-2,1,0,0,0,0],#[0,0,1,-1,0,0,0,0,0],#[0,0,1,-1,1,0,0,0,0],#[0,0,1,0,0,0,0,0,0],#[1,-1,0,0,-1,0,0,0,0],#[1,-1,0,0,0,0,0,0,0],#[1,-1,0,1,-1,0,0,0,0],#[1,-1,1,-1,0,0,0,0,0],#[1,-1,1,0,-1,0,0,0,0],#[1,-1,1,0,0,0,0,0,0],#[1,-1,1,1,-1,0,0,0,0]] : Array (Array ℤ))[i.val]!)[j.val]!
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
def gap (i : Fin 9) (j : Fin 9) : ℤ := ((#[#[1,0,0,0,0,0,0,0,0],#[0,1,0,0,0,0,0,0,0],#[0,0,1,0,0,0,0,0,0],#[0,0,0,1,0,0,0,0,0],#[0,0,0,0,1,0,0,0,0],#[0,0,0,0,0,1,0,0,0],#[0,0,0,0,0,0,1,0,0],#[0,0,0,0,0,0,0,1,0],#[0,0,0,0,0,0,0,0,1]] : Array (Array ℤ))[i.val]!)[j.val]!

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem valid : Valid table 0 3 0 gap obs := by
  constructor <;> decide +kernel
end SemanticThreeStep.rowB

namespace SemanticThreeStep.rowB
open MetabelianModule
variable {R : Type*} [CommRing R]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem gap_ok (x : R)  (j : Fin 9) : evalVec x (gap j)=x^j.val := by
  fin_cases j
  · change (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^0
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^1
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^2
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^3
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^4
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^5
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^6
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^7
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0))))))))) = x^8
    push_cast; ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem obs_ok (x : R) (hu : IsUnit (guardPoly x)) (hp : prodB x≠0) (j : Fin 14) : evalVec x (obs j)≠0 := by
  intro hj
  apply hp
  apply hu.mul_right_inj.mp
  unfold guardPoly prodB
  fin_cases j
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^22 - 3*x^21 + 3*x^20 + 2*x^19 - 13*x^18 + 22*x^17 - 18*x^16 - 4*x^15 + 36*x^14 - 58*x^13 + 53*x^12 - 18*x^11 - 30*x^10 + 66*x^9 - 71*x^8 + 46*x^7 - 8*x^6 - 22*x^5 + 32*x^4 - 26*x^3 + 14*x^2 - 5*x + 1) * hj
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (-x^22 + 2*x^21 - x^20 - 3*x^19 + 10*x^18 - 12*x^17 + 6*x^16 + 10*x^15 - 26*x^14 + 32*x^13 - 21*x^12 - 3*x^11 + 27*x^10 - 39*x^9 + 32*x^8 - 14*x^7 - 6*x^6 + 16*x^5 - 16*x^4 + 10*x^3 - 4*x^2 + x) * hj
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^23 - 3*x^22 + 3*x^21 + 2*x^20 - 13*x^19 + 22*x^18 - 18*x^17 - 4*x^16 + 36*x^15 - 58*x^14 + 53*x^13 - 18*x^12 - 30*x^11 + 66*x^10 - 71*x^9 + 46*x^8 - 8*x^7 - 22*x^6 + 32*x^5 - 26*x^4 + 14*x^3 - 5*x^2 + x) * hj
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-2 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^22 - x^21 + 3*x^19 - 7*x^18 + 5*x^17 - x^16 - 11*x^15 + 15*x^14 - 17*x^13 + 4*x^12 + 7*x^11 - 20*x^10 + 19*x^9 - 13*x^8 + x^7 + 7*x^6 - 9*x^5 + 7*x^4 - 3*x^3 + x^2) * hj
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (-x^23 + 2*x^22 - x^21 - 3*x^20 + 10*x^19 - 12*x^18 + 6*x^17 + 10*x^16 - 26*x^15 + 32*x^14 - 21*x^13 - 3*x^12 + 27*x^11 - 39*x^10 + 32*x^9 - 14*x^8 - 6*x^7 + 16*x^6 - 16*x^5 + 10*x^4 - 4*x^3 + x^2) * hj
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^22 - 2*x^21 + 4*x^19 - 9*x^18 + 9*x^17 - 13*x^15 + 23*x^14 - 22*x^13 + 8*x^12 + 12*x^11 - 26*x^10 + 28*x^9 - 17*x^8 + x^7 + 10*x^6 - 13*x^5 + 9*x^4 - 4*x^3 + x^2) * hj
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^24 - 3*x^23 + 3*x^22 + 2*x^21 - 13*x^20 + 22*x^19 - 18*x^18 - 4*x^17 + 36*x^16 - 58*x^15 + 53*x^14 - 18*x^13 - 30*x^12 + 66*x^11 - 71*x^10 + 46*x^9 - 8*x^8 - 22*x^7 + 32*x^6 - 26*x^5 + 14*x^4 - 5*x^3 + x^2) * hj
  · change (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (-x^22 + 3*x^21 - 3*x^20 - x^19 + 9*x^18 - 16*x^17 + 16*x^16 - 6*x^15 - 11*x^14 + 26*x^13 - 31*x^12 + 23*x^11 - 7*x^10 - 9*x^9 + 17*x^8 - 16*x^7 + 10*x^6 - 4*x^5 + x^4) * hj
  · change (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (-x^25 + 2*x^24 - x^23 - 3*x^22 + 10*x^21 - 12*x^20 + 6*x^19 + 10*x^18 - 26*x^17 + 32*x^16 - 21*x^15 - 3*x^14 + 27*x^13 - 39*x^12 + 32*x^11 - 14*x^10 - 6*x^9 + 16*x^8 - 16*x^7 + 10*x^6 - 4*x^5 + x^4) * hj
  · change (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (-x^22 + 2*x^21 - x^20 - 2*x^19 + 8*x^18 - 11*x^17 + 8*x^16 + 2*x^15 - 15*x^14 + 24*x^13 - 23*x^12 + 12*x^11 + 3*x^10 - 16*x^9 + 20*x^8 - 17*x^7 + 10*x^6 - 4*x^5 + x^4) * hj
  · change (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (-x^23 + 2*x^22 - 5*x^20 + 10*x^19 - 7*x^18 - 4*x^17 + 17*x^16 - 22*x^15 + 15*x^14 + x^13 - 18*x^12 + 26*x^11 - 21*x^10 + 6*x^9 + 7*x^8 - 12*x^7 + 9*x^6 - 4*x^5 + x^4) * hj
  · change (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (-x^22 + 3*x^21 - 4*x^20 + 2*x^19 + 5*x^18 - 13*x^17 + 17*x^16 - 12*x^15 - x^14 + 16*x^13 - 25*x^12 + 23*x^11 - 12*x^10 - 2*x^9 + 11*x^8 - 13*x^7 + 9*x^6 - 4*x^5 + x^4) * hj
  · change (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^24 - 2*x^23 + 4*x^21 - 9*x^20 + 9*x^19 - 13*x^17 + 23*x^16 - 22*x^15 + 8*x^14 + 12*x^13 - 26*x^12 + 28*x^11 - 17*x^10 + x^9 + 10*x^8 - 13*x^7 + 9*x^6 - 4*x^5 + x^4) * hj
  · change (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (-x^22 + 2*x^21 - 2*x^20 - x^19 + 7*x^18 - 12*x^17 + 12*x^16 - 4*x^15 - 9*x^14 + 21*x^13 - 25*x^12 + 19*x^11 - 6*x^10 - 7*x^9 + 14*x^8 - 14*x^7 + 9*x^6 - 4*x^5 + x^4) * hj
end SemanticThreeStep.rowB

namespace SemanticThreeStep.rowC
open MetabelianModule

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
def table : Table 47 16 9 9 where
  side := AtlasIndices.shores16Indexed
  ht i := ⟨#[4,4,4,3,6,6,7,7,8,5,5,2,3,0,1,1,4,5,2,3,0,1,1,4,3,6,6,7,7,8,5,5,7,7,8,5,5,2,3,0,1,1,4,3,6,6,7][i.val]!, by decide +revert⟩
  lamp i j := ((#[#[0,0,0,0,0,0,0,0,0],#[-1,1,-1,1,0,-1,0,0,0],#[0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0],#[0,0,0,1,0,0,0,0,0],#[0,0,0,1,0,0,0,0,0],#[0,0,0,1,0,0,0,0,0],#[0,0,0,1,0,0,0,0,0],#[0,0,0,1,0,0,0,0,0],#[0,0,0,1,0,-1,0,0,0],#[0,0,0,1,0,-1,0,0,0],#[0,0,-1,1,0,-1,0,0,0],#[0,0,-1,1,0,-1,0,0,0],#[-1,0,-1,1,0,-1,0,0,0],#[-1,0,-1,1,0,-1,0,0,0],#[-1,0,-1,1,0,-1,0,0,0],#[-1,1,-1,1,0,-1,0,0,0],#[0,0,0,0,0,0,0,0,0],#[0,0,-1,0,0,0,0,0,0],#[0,0,-1,0,0,0,0,0,0],#[-1,0,-1,0,0,0,0,0,0],#[-1,0,-1,0,0,0,0,0,0],#[-1,0,-1,0,0,0,0,0,0],#[-1,1,-1,0,0,0,0,0,0],#[-1,1,-1,0,0,0,0,0,0],#[-1,1,-1,1,0,0,0,0,0],#[-1,1,-1,1,0,0,0,0,0],#[-1,1,-1,1,0,0,0,0,0],#[-1,1,-1,1,0,0,0,0,0],#[-1,1,-1,1,0,0,0,0,0],#[-1,1,-1,1,0,-1,0,0,0],#[-1,1,-1,1,0,-1,0,0,0],#[0,0,0,0,1,0,0,0,0],#[0,0,0,0,1,0,0,0,0],#[0,0,0,0,1,0,0,0,0],#[0,0,0,0,1,-1,0,0,0],#[0,0,0,0,1,-1,0,0,0],#[0,0,-1,0,1,-1,0,0,0],#[0,0,-1,0,1,-1,0,0,0],#[-1,0,-1,0,1,-1,0,0,0],#[-1,0,-1,0,1,-1,0,0,0],#[-1,0,-1,0,1,-1,0,0,0],#[-1,1,-1,0,1,-1,0,0,0],#[-1,1,-1,0,1,-1,0,0,0],#[-1,1,-1,1,1,-1,0,0,0],#[-1,1,-1,1,1,-1,0,0,0],#[-1,1,-1,1,1,-1,0,0,0]] : Array (Array ℤ))[i.val]!)[j.val]!
  route c t := if t = 0 then 0 else if ht : t < 16 then ⟨2+c.val*15+(t-1),by have := c.isLt; omega⟩ else 1
  src := 0
  dst := 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
def obs (i : Fin 7) (j : Fin 9) : ℤ := ((#[#[0,0,0,0,1,-1,0,0,0],#[0,0,0,1,-1,0,0,0,0],#[0,0,0,1,0,-1,0,0,0],#[1,-1,1,-1,0,1,0,0,0],#[1,-1,1,-1,1,0,0,0,0],#[1,-1,1,0,-1,1,0,0,0],#[1,-1,1,0,0,0,0,0,0]] : Array (Array ℤ))[i.val]!)[j.val]!
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
def gap (i : Fin 9) (j : Fin 9) : ℤ := ((#[#[1,0,0,0,0,0,0,0,0],#[0,1,0,0,0,0,0,0,0],#[0,0,1,0,0,0,0,0,0],#[0,0,0,1,0,0,0,0,0],#[0,0,0,0,1,0,0,0,0],#[0,0,0,0,0,1,0,0,0],#[0,0,0,0,0,0,1,0,0],#[0,0,0,0,0,0,0,1,0],#[0,0,0,0,0,0,0,0,1]] : Array (Array ℤ))[i.val]!)[j.val]!

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem valid : Valid table 0 3 0 gap obs := by
  constructor <;> decide +kernel
end SemanticThreeStep.rowC

namespace SemanticThreeStep.rowC
open MetabelianModule
variable {R : Type*} [CommRing R]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem gap_ok (x : R)  (j : Fin 9) : evalVec x (gap j)=x^j.val := by
  fin_cases j
  · change (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^0
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^1
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^2
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^3
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^4
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^5
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^6
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = x^7
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0))))))))) = x^8
    push_cast; ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem obs_ok (x : R) (hu : IsUnit (guardPoly x)) (hp : prodC x≠0) (j : Fin 7) : evalVec x (obs j)≠0 := by
  intro hj
  apply hp
  apply hu.mul_right_inj.mp
  unfold guardPoly prodC
  fin_cases j
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (-x^20 + 3*x^19 - 4*x^18 + x^17 + 7*x^16 - 18*x^15 + 25*x^14 - 21*x^13 + 4*x^12 + 20*x^11 - 40*x^10 + 46*x^9 - 35*x^8 + 13*x^7 + 9*x^6 - 22*x^5 + 24*x^4 - 18*x^3 + 10*x^2 - 4*x + 1) * hj
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (-x^21 + 3*x^20 - 4*x^19 + x^18 + 7*x^17 - 18*x^16 + 25*x^15 - 21*x^14 + 4*x^13 + 20*x^12 - 40*x^11 + 46*x^10 - 35*x^9 + 13*x^8 + 9*x^7 - 22*x^6 + 24*x^5 - 18*x^4 + 10*x^3 - 4*x^2 + x) * hj
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (-x^20 + 4*x^19 - 8*x^18 + 9*x^17 - 2*x^16 - 16*x^15 + 41*x^14 - 62*x^13 + 66*x^12 - 46*x^11 + 6*x^10 + 40*x^9 - 75*x^8 + 88*x^7 - 79*x^6 + 57*x^5 - 33*x^4 + 15*x^3 - 5*x^2 + x) * hj
  · change (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^20 - 4*x^19 + 8*x^18 - 10*x^17 + 7*x^16 + 2*x^15 - 14*x^14 + 23*x^13 - 24*x^12 + 16*x^11 - 3*x^10 - 9*x^9 + 15*x^8 - 14*x^7 + 9*x^6 - 4*x^5 + x^4) * hj
  · change (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^21 - 3*x^20 + 3*x^19 + 2*x^18 - 11*x^17 + 18*x^16 - 15*x^15 + 19*x^13 - 30*x^12 + 26*x^11 - 11*x^10 - 5*x^9 + 14*x^8 - 14*x^7 + 9*x^6 - 4*x^5 + x^4) * hj
  · change (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^20 - 3*x^19 + 4*x^18 - 2*x^17 - 4*x^16 + 13*x^15 - 21*x^14 + 23*x^13 - 17*x^12 + 5*x^11 + 8*x^10 - 17*x^9 + 19*x^8 - 15*x^7 + 9*x^6 - 4*x^5 + x^4) * hj
  · change (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0))))))))) = 0 at hj
    push_cast at hj
    linear_combination (x^23 - 3*x^22 + 3*x^21 + x^20 - 8*x^19 + 16*x^18 - 19*x^17 + 11*x^16 + 5*x^15 - 22*x^14 + 33*x^13 - 31*x^12 + 17*x^11 - 13*x^9 + 18*x^8 - 15*x^7 + 9*x^6 - 4*x^5 + x^4) * hj
end SemanticThreeStep.rowC

namespace SemanticThreeStep.row5
open MetabelianModule

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
def table : Table 47 16 5 4 where
  side := AtlasIndices.shores16Indexed
  ht i := ⟨#[0,0,0,4,4,1,1,3,4,4,0,0,1,1,4,4,0,1,1,2,2,0,0,1,3,4,4,0,2,2,1,1,3,2,2,1,1,3,4,4,0,0,1,1,2,2,3][i.val]!, by decide +revert⟩
  lamp i j := ((#[#[0,0,0,0],#[0,0,0,-1],#[0,0,0,0],#[0,0,0,0],#[0,0,0,0],#[0,-1,0,0],#[0,-1,0,0],#[0,-1,0,-1],#[0,-1,0,-1],#[0,-1,0,-1],#[0,-1,0,-1],#[0,-1,0,-1],#[0,-1,0,-1],#[0,-1,0,-1],#[0,0,0,-1],#[0,0,0,-1],#[0,0,0,-1],#[0,0,0,0],#[0,0,0,0],#[0,0,0,0],#[0,0,0,0],#[0,0,1,0],#[0,0,1,0],#[0,0,1,0],#[0,0,1,-1],#[0,0,1,-1],#[0,0,1,-1],#[0,0,1,-1],#[0,0,0,-1],#[0,0,0,-1],#[0,0,0,-1],#[0,0,0,-1],#[1,0,0,0],#[1,0,0,0],#[1,0,0,0],#[1,0,0,0],#[1,0,0,0],#[1,0,0,-1],#[1,0,0,-1],#[1,0,0,-1],#[1,0,0,-1],#[1,0,0,-1],#[1,0,0,-1],#[1,0,0,-1],#[1,0,0,-1],#[1,0,0,-1],#[1,0,0,-1]] : Array (Array ℤ))[i.val]!)[j.val]!
  route c t := if t = 0 then 0 else if ht : t < 16 then ⟨2+c.val*15+(t-1),by have := c.isLt; omega⟩ else 1
  src := 0
  dst := 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
def obs (i : Fin 17) (j : Fin 4) : ℤ := ((#[#[0,0,0,1],#[0,0,1,-1],#[0,0,1,0],#[0,0,1,1],#[0,1,0,-1],#[0,1,0,0],#[0,1,0,1],#[0,1,1,0],#[0,1,1,1],#[1,0,-1,-1],#[1,0,-1,0],#[1,0,0,-1],#[1,0,0,0],#[1,0,0,1],#[1,1,0,-1],#[1,1,0,0],#[1,1,0,1]] : Array (Array ℤ))[i.val]!)[j.val]!
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
def gap (i : Fin 5) (j : Fin 4) : ℤ := ((#[#[1,0,0,0],#[0,1,0,0],#[0,0,1,0],#[0,0,0,1],#[-1,-1,-1,-1]] : Array (Array ℤ))[i.val]!)[j.val]!

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem valid : Valid table 5 3 0 gap obs := by
  constructor <;> decide +kernel
end SemanticThreeStep.row5

namespace SemanticThreeStep.row5
open MetabelianModule
variable {R : Type*} [CommRing R]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem gap_ok (x : R) (hp : phi5 x=0) (j : Fin 5) : evalVec x (gap j)=x^j.val := by
  unfold phi5 at hp
  fin_cases j
  · change (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))) = x^0
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))) = x^1
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))) = x^2
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))) = x^3
    push_cast; ring
  · change (((-1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * 0)))) = x^4
    linear_combination (-1) * hp

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem obs_ok (x : R) (hphi : phi5 x=0) (hn : (5:R)≠0) (j : Fin 17) : evalVec x (obs j)≠0 := by
  intro hj
  apply hn
  unfold phi5 at hphi
  fin_cases j
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))) = 0 at hj
    push_cast at hj
    linear_combination (5*x^2) * hj + (5 - 5*x) * hphi
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * 0)))) = 0 at hj
    push_cast at hj
    linear_combination (x^3 - 3*x^2 - 2*x - 1) * hj + (x^2 - 5*x + 5) * hphi
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))) = 0 at hj
    push_cast at hj
    linear_combination (5*x^3) * hj + (5 - 5*x) * hphi
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))) = 0 at hj
    push_cast at hj
    linear_combination (5*x^3 + 5*x^2 + 5) * hj + (-5*x^2 - 5*x + 5) * hphi
  · change (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * 0)))) = 0 at hj
    push_cast at hj
    linear_combination (-2*x^3 - 4*x^2 - x - 3) * hj + (-2*x^2 - 2*x + 5) * hphi
  · change (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))) = 0 at hj
    push_cast at hj
    linear_combination (-5*x^3 - 5*x^2 - 5*x - 5) * hj + (5) * hphi
  · change (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))) = 0 at hj
    push_cast at hj
    linear_combination (-5*x - 5) * hj + (5) * hphi
  · change (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))) = 0 at hj
    push_cast at hj
    linear_combination (-5*x^2 - 5) * hj + (5) * hphi
  · change (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))) = 0 at hj
    push_cast at hj
    linear_combination (-5*x^3 - 5*x - 5) * hj + (5*x^2 + 5) * hphi
  · change (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * 0)))) = 0 at hj
    push_cast at hj
    linear_combination (5*x^3 + 5*x^2 + 10) * hj + (5*x^2 + 5*x - 5) * hphi
  · change (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))) = 0 at hj
    push_cast at hj
    linear_combination (-2*x^3 + x^2 - x + 2) * hj + (3 - 2*x) * hphi
  · change (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * 0)))) = 0 at hj
    push_cast at hj
    linear_combination (2*x^3 - x^2 + x + 3) * hj + (2*x^2 - 3*x + 2) * hphi
  · change (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))) = 0 at hj
    push_cast at hj
    linear_combination (5) * hj + (0) * hphi
  · change (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))) = 0 at hj
    push_cast at hj
    linear_combination (5*x^2 + 5*x + 5) * hj + (-5*x) * hphi
  · change (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * 0)))) = 0 at hj
    push_cast at hj
    linear_combination (5*x^3 - 5*x^2 + 5*x) * hj + (5*x^2 - 10*x + 5) * hphi
  · change (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))) = 0 at hj
    push_cast at hj
    linear_combination (-5*x^3 - 5*x) * hj + (5) * hphi
  · change (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))) = 0 at hj
    push_cast at hj
    linear_combination (-5*x^3 - 5*x^2 - 5*x) * hj + (5*x^2 + 5) * hphi
end SemanticThreeStep.row5

namespace SemanticThreeStep.row7
open MetabelianModule

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
def table : Table 47 16 7 6 where
  side := AtlasIndices.shores16Indexed
  ht i := ⟨#[0,4,0,6,2,2,5,4,0,0,1,5,5,2,2,6,0,1,1,2,2,3,3,6,6,0,0,1,5,6,3,4,3,3,6,5,5,4,0,6,2,1,4,3,3,2,5][i.val]!, by decide +revert⟩
  lamp i j := ((#[#[0,0,0,0,0,0],#[0,0,0,0,0,-1],#[0,0,0,0,0,0],#[0,0,0,0,0,0],#[-1,-1,-1,-1,-1,-1],#[-1,-1,-1,-1,-1,-1],#[-1,-1,0,-1,-1,-1],#[-1,-1,0,-1,-1,-1],#[-1,-1,0,-1,0,-1],#[-1,-1,0,-1,0,-1],#[-1,-1,0,-1,0,-1],#[-1,-1,0,-1,0,-2],#[-1,-1,0,-1,0,-2],#[-1,-1,-1,-1,0,-2],#[-1,-1,-1,-1,0,-2],#[0,0,0,0,1,-1],#[0,0,0,0,1,-1],#[0,0,0,0,0,0],#[0,0,0,0,0,0],#[0,0,0,0,0,0],#[0,0,0,0,0,0],#[0,0,0,0,0,0],#[0,0,0,0,0,0],#[0,0,0,1,0,0],#[0,0,0,1,0,0],#[0,0,0,1,0,0],#[0,0,0,1,0,0],#[0,0,0,1,0,0],#[0,0,0,1,0,-1],#[0,0,0,1,0,-1],#[0,0,0,0,0,-1],#[0,0,0,0,0,-1],#[1,0,0,0,0,0],#[1,0,0,0,0,0],#[1,0,0,1,0,0],#[1,0,0,1,0,0],#[1,0,0,1,0,0],#[1,0,0,1,0,0],#[1,0,0,1,1,0],#[1,0,0,1,1,0],#[0,-1,-1,0,0,-1],#[0,-1,-1,0,0,-1],#[0,0,-1,0,0,-1],#[0,0,-1,0,0,-1],#[0,0,-1,0,0,-1],#[0,0,-1,0,0,-1],#[0,0,0,0,0,-1]] : Array (Array ℤ))[i.val]!)[j.val]!
  route c t := if t = 0 then 0 else if ht : t < 16 then ⟨2+c.val*15+(t-1),by have := c.isLt; omega⟩ else 1
  src := 0
  dst := 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
def obs (i : Fin 20) (j : Fin 6) : ℤ := ((#[#[0,0,0,0,0,1],#[0,0,0,0,1,-1],#[0,0,0,1,-1,1],#[0,0,0,1,0,0],#[0,0,1,0,0,0],#[0,0,1,0,0,1],#[0,1,1,0,0,1],#[1,0,0,0,0,0],#[1,0,0,0,0,1],#[1,0,0,0,1,0],#[1,0,0,1,0,1],#[1,0,0,1,1,0],#[1,0,1,0,0,1],#[1,1,0,1,0,1],#[1,1,0,1,1,0],#[1,1,0,2,0,1],#[1,1,1,1,0,2],#[1,1,1,1,1,1],#[2,1,0,2,0,2],#[2,1,0,2,1,1]] : Array (Array ℤ))[i.val]!)[j.val]!
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
def gap (i : Fin 7) (j : Fin 6) : ℤ := ((#[#[1,0,0,0,0,0],#[0,1,0,0,0,0],#[0,0,1,0,0,0],#[0,0,0,1,0,0],#[0,0,0,0,1,0],#[0,0,0,0,0,1],#[-1,-1,-1,-1,-1,-1]] : Array (Array ℤ))[i.val]!)[j.val]!

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem valid : Valid table 7 3 0 gap obs := by
  constructor <;> decide +kernel
end SemanticThreeStep.row7

namespace SemanticThreeStep.row7
open MetabelianModule
variable {R : Type*} [CommRing R]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem gap_ok (x : R) (hp : phi7 x=0) (j : Fin 7) : evalVec x (gap j)=x^j.val := by
  unfold phi7 at hp
  fin_cases j
  · change (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))))) = x^0
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))))) = x^1
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))))) = x^2
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))))) = x^3
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))))) = x^4
    push_cast; ring
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))))) = x^5
    push_cast; ring
  · change (((-1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * 0)))))) = x^6
    linear_combination (-1) * hp

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem obs_ok (x : R) (hphi : phi7 x=0) (hn : (56:R)≠0) (j : Fin 20) : evalVec x (obs j)≠0 := by
  intro hj
  apply hn
  unfold phi7 at hphi
  fin_cases j
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (56*x^2) * hj + (56 - 56*x) * hphi
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (8*x^5 + 16*x^4 + 24*x^3 - 24*x^2 - 16*x - 8) * hj + (8*x^4 - 56*x + 56) * hphi
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((-1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (56*x^5 + 112*x^4 + 112*x^3 + 112*x^2 + 56*x) * hj + (-56*x^4 - 56*x + 56) * hphi
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (56*x^4) * hj + (56 - 56*x) * hphi
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (56*x^5) * hj + (56 - 56*x) * hphi
  · change (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (56*x^5 + 56*x^4 + 56*x^3 + 56*x^2) * hj + (-56*x^4 - 56*x + 56) * hphi
  · change (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (-56*x^3 - 56*x) * hj + (56*x^2 - 56*x + 56) * hphi
  · change (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (56) * hj + (0) * hphi
  · change (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (-56*x^5 - 56*x^4 - 56*x) * hj + (56*x^4 - 56*x^2 + 56) * hphi
  · change (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (56*x^3 + 56*x^2 + 56*x + 56) * hj + (-56*x) * hphi
  · change (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (56*x^4 + 56*x^3 + 56*x^2 + 56*x + 56) * hj + (-56*x^3 - 56*x) * hphi
  · change (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (56*x^5 + 56*x^4 + 56*x^3 + 56*x^2 + 56) * hj + (-56*x^3 - 56*x^2) * hphi
  · change (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (-56*x^4 - 56*x^3) * hj + (56*x^3 - 56*x + 56) * hphi
  · change (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (-56*x^5 - 56*x^4 - 56*x^3 - 56*x^2 - 56*x) * hj + (56*x^4 + 56*x^2 + 56) * hphi
  · change (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (-56*x^5 - 56*x^3 - 56*x^2 - 56*x - 56) * hj + (56*x^3 + 112) * hphi
  · change (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((2 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (28*x^4 - 28*x^2 - 28*x) * hj + (-28*x^3 + 28*x^2 - 28*x + 56) * hphi
  · change (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((2 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (-56*x^4 - 112*x^3 - 112*x^2 - 112*x - 56) * hj + (112*x^3 + 112*x^2 + 56*x + 112) * hphi
  · change (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (-56*x) * hj + (56) * hphi
  · change (((2 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((2 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((2 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (-40*x^5 - 24*x^4 - 8*x^3 + 8*x^2 + 24*x + 40) * hj + (80*x^4 - 32*x^3 + 48*x^2 - 64*x - 24) * hphi
  · change (((2 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((0 : ℤ) : R) + x * (((2 : ℤ) : R) + x * (((1 : ℤ) : R) + x * (((1 : ℤ) : R) + x * 0)))))) = 0 at hj
    push_cast at hj
    linear_combination (24*x^5 + 48*x^4 + 16*x^3 - 16*x^2 - 48*x - 24) * hj + (-24*x^4 - 48*x^3 - 40*x^2 + 16*x + 104) * hphi
end SemanticThreeStep.row7

namespace SemanticThreeStep
open MetabelianModule MetabelianRegular

theorem chartTheta {R V : Type*} [CommRing R] [Nontrivial R] {B : SimpleGraph V}
    {m : ℕ} {x : R} (C : Chart B m 3 x) (hm : 5 ≤ m) (odd : Odd m)
    (period : x^m = 1) (reg : IsUnit (x-1)) (two : IsUnit (2:R)) :
    Nonempty (EqualArms.Theta B 16) := by
  by_cases five : m=5
  · subst m
    have phi := phi5_zero x period reg
    exact tableTheta C row5.table row5.gap row5.obs row5.valid le_rfl (Or.inr rfl)
      (by simp) (row5.gap_ok x phi) (row5.obs_ok x phi (unit5 x phi reg).ne_zero)
  by_cases seven : m=7
  · subst m
    have phi := phi7_zero x period reg
    have num : IsUnit (56:R) := by
      convert (unit7 x phi reg).mul (two.pow 3) using 1; norm_num
    exact tableTheta C row7.table row7.gap row7.obs row7.valid le_rfl (Or.inr rfl)
      (by simp) (row7.gap_ok x phi) (row7.obs_ok x phi num.ne_zero)
  have large : 9 ≤ m := by obtain ⟨k,hk⟩ := odd; omega
  have hu := guardUnit x odd period reg two
  rcases oneRow x with a|b|c
  · exact tableTheta C rowA.table rowA.gap rowA.obs rowA.valid large (Or.inl rfl)
      (by simp) (rowA.gap_ok x) (rowA.obs_ok x hu a)
  · exact tableTheta C rowB.table rowB.gap rowB.obs rowB.valid large (Or.inl rfl)
      (by simp) (rowB.gap_ok x) (rowB.obs_ok x hu b)
  · exact tableTheta C rowC.table rowC.gap rowC.obs rowC.valid large (Or.inl rfl)
      (by simp) (rowC.gap_ok x) (rowC.obs_ok x hu c)

end SemanticThreeStep

/- Reorder the three original shifts and apply the appropriate chart theorem. -/
namespace OddCyclicShort
open EqualArms MetabelianRegular MetabelianModule OrdinaryCyclicTheta
universe u

def ThirdCharts : Prop :=
  ∀ {R : Type} [CommRing R] [Nontrivial R] {V : Type u} {B : SimpleGraph V}
    {d : ℕ} {x : R} (rev : Bool), Chart B (3*d) (MetabelianOrderThree.jump d rev) x →
    5≤d → Odd d → x^(3*d)=1 → IsUnit (x-1) → IsUnit (2:R) → EightOrSixteen B

variable {M : Type u} [Group M] [Finite M] [IsMulCommutative (commutator M)]

private theorem repeated (a b : M) (gen : Subgroup.closure ({a,b} : Set M)=⊤)
    (nonab : ¬IsMulCommutative M) (odd : Odd (Nat.card M))
    (off : Abelianization.of b=1) : EightOrSixteen (rightMatching a b) :=
  NecklaceTheta.marked a b gen nonab odd off

private theorem progression (a b : M) (gen : Subgroup.closure ({a,b} : Set M)=⊤)
    (nonab : ¬IsMulCommutative M) (odd : Odd (Nat.card M))
    (off : Abelianization.of b=(Abelianization.of a)^2) : EightOrSixteen (rightMatching a b) :=
  (MetabelianProgression.intrinsic a b gen nonab odd off).symm

theorem three_step (a b : M) (gen : Subgroup.closure ({a,b} : Set M)=⊤)
    (nonab : ¬IsMulCommutative M) (odd : Odd (Nat.card M))
    (off : Abelianization.of b=(Abelianization.of a)^3) : EightOrSixteen (rightMatching a b) := by
  obtain ⟨N⟩:=normalize a b 3 gen nonab odd off
  by_cases large : 5≤orderOf (Abelianization.of a)
  · exact .inr (SemanticThreeStep.chartTheta N.chart large N.odd N.period N.reg N.two)
  · have lower:=N.lower
    obtain ⟨k,hk⟩:=N.odd
    have eq : orderOf (Abelianization.of a)=3 := by omega
    exact repeated a b gen nonab odd (off.trans (eq ▸ pow_orderOf_eq_one _))

theorem coincidence (a b : M) (gen : Subgroup.closure ({a,b} : Set M)=⊤)
    (nonab : ¬IsMulCommutative M) (odd : Odd (Nat.card M))
    (same : Abelianization.of a=1 ∨ Abelianization.of b=1 ∨
      Abelianization.of a=Abelianization.of b) : EightOrSixteen (rightMatching a b) := by
  rcases same with h|h|h
  · apply reorder_arms a b 1
    exact repeated _ _ (reorder_generates a b gen 1) nonab odd h
  · exact repeated a b gen nonab odd h
  · apply reorder_arms a b 2
    apply repeated _ _ (reorder_generates a b gen 2) nonab odd
    change Abelianization.of (b/a)=1
    simp [h]

private theorem third_chart (charts : ThirdCharts.{u}) (a b : M)
    (gen : Subgroup.closure ({a,b} : Set M)=⊤) (nonab : ¬IsMulCommutative M)
    (odd : Odd (Nat.card M)) (generator : Subgroup.zpowers (Abelianization.of a)=⊤)
    (ord : orderOf (Abelianization.of b)=3) : EightOrSixteen (rightMatching a b) := by
  let g:=Abelianization.of a
  let d:=orderOf g/3
  obtain ⟨period,offset⟩:=third_offsets generator ord
  change orderOf g=3*d at period
  change Abelianization.of b=g^d ∨ Abelianization.of b=g^(2*d) at offset
  have choose : ∃ rev : Bool, Abelianization.of b=g^(MetabelianOrderThree.jump d rev) := by
    rcases offset with h|h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  obtain ⟨rev,shift⟩:=choose
  obtain ⟨N⟩:=normalize a b _ gen nonab odd shift
  have lower : 3≤orderOf g := N.lower
  have oddm : Odd (3*d) := period ▸ N.odd
  have oddd : Odd d := oddm.of_dvd_nat (dvd_mul_left _ _)
  by_cases large : 5≤d
  · apply charts rev (period ▸ N.chart) large oddd (period ▸ N.period) N.reg N.two
  obtain ⟨k,hk⟩:=oddd
  have sm : d=1 ∨ d=3 := by omega
  rcases sm with h|h <;> cases rev
  · apply coincidence a b gen nonab odd
    exact .inr (.inr (by simpa [MetabelianOrderThree.jump,h,g] using shift.symm))
  · exact progression a b gen nonab odd (by simpa [MetabelianOrderThree.jump,h,g] using shift)
  · exact three_step a b gen nonab odd (by simpa [MetabelianOrderThree.jump,h,g] using shift)
  · have off : Abelianization.of b=g^6 := by simpa [MetabelianOrderThree.jump,h] using shift
    have nine : g^9=1 := by rw [show 9=orderOf g by omega,pow_orderOf_eq_one]
    have eighteen : g^(6*3)=1 := by rw [show 6*3=9*2 by decide,pow_mul,nine,one_pow]
    apply reorder_arms a b 5
    apply three_step _ _ (reorder_generates a b gen 5) nonab odd
    change Abelianization.of b⁻¹=(Abelianization.of (a/b))^3
    rw [map_inv,map_div,off,div_pow,←pow_mul,eighteen,div_one]
    change (g^6)⁻¹=g^3
    apply inv_eq_iff_mul_eq_one.mpr
    rw [←pow_add]
    exact nine

theorem order_three (charts : ThirdCharts.{u}) [IsCyclic (Abelianization M)] (a b : M)
    (gen : Subgroup.closure ({a,b} : Set M)=⊤) (nonab : ¬IsMulCommutative M)
    (odd : Odd (Nat.card M)) (ord : orderOf (Abelianization.of a)=3) :
    EightOrSixteen (rightMatching a b) := by
  have qgen := pair_map_top gen (Abelianization.of : M →* Abelianization M)
    (QuotientGroup.mk'_surjective _)
  rcases third_generator _ _ qgen ord with direct|translated
  · apply reorder_arms a b 1
    exact third_chart charts _ _ (reorder_generates a b gen 1) nonab odd direct ord
  · apply reorder_arms a b 3
    apply third_chart charts _ _ (reorder_generates a b gen 3) nonab odd
    · change Subgroup.zpowers (Abelianization.of (b/a))=⊤
      rwa [map_div]
    · change orderOf (Abelianization.of a⁻¹)=3
      rwa [map_inv,orderOf_inv]

end OddCyclicShort

namespace OddCyclicShort
open EqualArms MetabelianRegular OddDyadicSize OrdinaryCyclicTheta
universe u

theorem cyclicShort_of_thirdCharts (charts : ThirdCharts.{0}) : CyclicShort.{0,0} := by
  intro M _ _ odd met cyclic a b gen a1 _ _ noncomm
  have nonab : ¬IsMulCommutative M := fun h => noncomm (h.is_comm.comm _ _)
  let _ : Nontrivial M := ⟨⟨a,1,a1⟩⟩
  let q : M →* Abelianization M := Abelianization.of
  have finish (h : EightOrSixteen (rightMatching a b)) : OddDyadicSize.Short.{0,0} a b :=
    quotient_short (MonoidHom.id M) Function.surjective_id a b h
  by_cases same : q a=1 ∨ q b=1 ∨ q a=q b
  · exact finish (coincidence a b gen nonab odd same)
  push Not at same
  by_cases exc : Exceptional (q a) (q b)
  · obtain ⟨k,hk⟩:=exc
    apply finish
    apply reorder_arms a b k
    let s:=(reorder a b k).1
    let t:=(reorder a b k).2
    have stgen : Subgroup.closure ({s,t} : Set M)=⊤ := reorder_generates a b gen k
    have pair:=map_reorder q a b k
    change (reorder (q a) (q b) k).1^2=(reorder (q a) (q b) k).2 ∨
      (reorder (q a) (q b) k).1^3=(reorder (q a) (q b) k).2 ∨
      orderOf (reorder (q a) (q b) k).1=3 at hk
    rw [←pair] at hk
    change (q s)^2=q t ∨ (q s)^3=q t ∨ orderOf (q s)=3 at hk
    rcases hk with ap|cube|three
    · exact (MetabelianProgression.intrinsic s t stgen nonab odd ap.symm).symm
    · exact three_step s t stgen nonab odd cube.symm
    · exact order_three charts s t stgen nonab odd three
  · exact ordinary_short odd a b gen same.1 same.2.1 same.2.2 exc

end OddCyclicShort

namespace MetabelianOrderThree
open OddCyclicShort MetabelianModule MetabelianRegular OrdinaryCyclicTheta EqualArms
universe u

theorem thirdCharts : ThirdCharts.{u} := by
  intro R _ _ V B d x rev C wide odd period reg two
  exact .inr (large rev C (by omega) (Odd.mul (by decide : Odd 3) odd) period reg two)

end MetabelianOrderThree

namespace OddCyclicShort
open OddDyadicSize
universe u

theorem thirdCharts : ThirdCharts.{u} := MetabelianOrderThree.thirdCharts

theorem cyclicShort : OddDyadicSize.CyclicShort.{0,0} :=
  cyclicShort_of_thirdCharts thirdCharts

end OddCyclicShort

end OddCyclicCertificate

theorem OMA.solution : OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R2.H1 := by
  intro M _ _ odd met cyc a b gen nc
  have a1 : a≠1 := by rintro rfl; exact nc (Commute.one_left _)
  have b1 : b≠1 := by rintro rfl; exact nc (Commute.one_right _)
  have ab : a≠b := by rintro rfl; exact nc (Commute.refl _)
  obtain ⟨Q,_,_,π,onto,j,lo,hi,⟨T⟩⟩ :=
    OddCyclicCertificate.OddCyclicShort.cyclicShort M odd met cyc a b gen a1 b1 ab nc
  exact ⟨Q,inferInstance,inferInstance,π,onto,j,lo,hi,T.src,T.dst,T.arm,T.endpoints,
    T.head,T.last,T.step,T.avoid,T.distinct⟩
