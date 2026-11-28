import OMAStatements.S_mo_478169
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Tactic.NoncommRing

/-!
# Addition for maps preserving multiplication and successor

Credit: @xlh1551. Source: Friedrich Wehrung, "Is addition definable from
multiplication and successor?", Corollary 3.6, Lemma 6.2 and Theorem 8.3.
https://arxiv.org/abs/2405.08364 and https://mathoverflow.net/questions/478169

The two remaining statements concern two explicit pairs of elements in the
free integer algebra on two generators. Both pairs contain the same commutator.
The shift in the third pair in Theorem 8.3 is supplied by substitution.
-/

namespace OMA.R_mo_478169_R1

section RingIdentities
variable {R S : Type} [Ring R] [Ring S]

private theorem left_comm_formula (x y z : R) (h : x*z*y = x*y*z) :
    (1+x*z)*(1+y*z) = 1+(1+x*y)*(z*z)+(x+y-z)*z := by
  calc
    _ = 1+x*z+y*z+(x*z*y)*z := by noncomm_ring
    _ = _ := by rw [h]; noncomm_ring

private theorem annihilate_of_shift {a z : S} (h : a*z=0) (hs : a*(1+z)=0) : a=0 := by
  simpa [mul_add,h] using hs

private theorem weak_comm_zero (f : R → S)
    (mul : ∀ u v, f (u*v) = f u * f v) (succ : ∀ u, f (1+u) = 1+f u)
    (x y : R) (h : x*y*x = x*x*y) :
    (f x + f y - f (x+y))*f (x+y) = 0 := by
  let z := x+y
  have hc : x*z*y=x*y*z := by
    dsimp [z]; simp only [mul_add,add_mul]; rw [h]
  have hp := left_comm_formula x y z hc
  have hz : x+y-z = 0 := sub_self _
  rw [hz,zero_mul,add_zero] at hp
  have mapped := congrArg f hp
  simp only [mul,succ] at mapped
  have comm := congrArg f hc
  simp only [mul] at comm
  have reflected := left_comm_formula (f x) (f y) (f z) comm
  rw [mapped] at reflected
  exact (add_eq_left.mp reflected.symm)

/-- Wehrung, Lemma 6.2, under the weaker relation x*y*x = x*x*y. -/
theorem add_of_weak_commutation (f : R → S)
    (mul : ∀ u v, f (u*v) = f u * f v) (succ : ∀ u, f (1+u) = 1+f u)
    (x y : R) (h : x*y*x = x*x*y) : f (x+y) = f x + f y := by
  apply Eq.symm
  apply sub_eq_zero.mp
  apply annihilate_of_shift (weak_comm_zero f mul succ x y h)
  have hs : x*(1+y)*x = x*x*(1+y) := by simp only [mul_add, add_mul, mul_one]; rw [h]
  have shifted := weak_comm_zero f mul succ x (1+y) hs
  rw [show x+(1+y) = 1+(x+y) by abel, succ, succ] at shifted
  convert shifted using 1; noncomm_ring

theorem add_of_commute (f : R → S)
    (mul : ∀ u v, f (u*v) = f u * f v) (succ : ∀ u, f (1+u) = 1+f u)
    (x y : R) (h : Commute x y) : f (x+y) = f x + f y := by
  apply add_of_weak_commutation f mul succ
  rw [mul_assoc, ← h.eq, ← mul_assoc]

end RingIdentities

private theorem commutator_formula {S : Type} [Ring S] (a b s : S) :
    (1+s*a)*(1+b*s)+(a*s-s*a) = 1+s*(1+a*b)*s+(a+b-s)*s := by noncomm_ring

private theorem commutator_zero {R S : Type} [Ring R] [Ring S] (f : R → S)
    (mul : ∀ u v, f (u*v) = f u * f v) (succ : ∀ u, f (1+u) = 1+f u)
    (x y : R)
    (h1 : f ((x*y-y*x)+(x+y)*x) = f (x*y-y*x) + f ((x+y)*x))
    (h2 : f ((x*y-y*x)+(1+(x+y)*x)*(1+y*(x+y))) =
      f (x*y-y*x) + f ((1+(x+y)*x)*(1+y*(x+y)))) :
    (f x + f y - f (x+y))*f (x+y) = 0 := by
  let z := x+y
  change f ((x*y-y*x)+z*x) = f (x*y-y*x) + f (z*x) at h1
  rw [show x*y-y*x+z*x = x*z by dsimp [z]; noncomm_ring,mul,mul] at h1
  have fc : f (x*y-y*x) = f x*f z - f z*f x := by
    exact eq_sub_of_add_eq h1.symm
  change f ((x*y-y*x)+(1+z*x)*(1+y*z)) = f (x*y-y*x) + f ((1+z*x)*(1+y*z)) at h2
  rw [show (x*y-y*x)+(1+z*x)*(1+y*z) = 1+z*(1+x*y)*z by dsimp [z]; noncomm_ring] at h2
  simp only [mul,succ,fc] at h2
  have eq := commutator_formula (f x) (f y) (f z)
  rw [add_comm ((1 + f z * f x) * (1 + f y * f z)), ← h2] at eq
  exact add_eq_left.mp eq.symm

/-- Add the generator commutator to (X+Y)X in the two-generator free ring. -/
def H1 : Prop :=
  ∀ (S : Type) [Ring S] (f : FreeAlgebra ℤ Bool → S),
    (∀ u v, f (u*v) = f u * f v) → (∀ u, f (1+u) = 1+f u) →
    let x := FreeAlgebra.ι ℤ false
    let y := FreeAlgebra.ι ℤ true
    let c := x*y-y*x
    let q := (x+y)*x
    f (c+q) = f c + f q

/-- Add the same commutator to the product in Wehrung's Notation 8.2. -/
def H2 : Prop :=
  ∀ (S : Type) [Ring S] (f : FreeAlgebra ℤ Bool → S),
    (∀ u v, f (u*v) = f u * f v) → (∀ u, f (1+u) = 1+f u) →
    let x := FreeAlgebra.ι ℤ false
    let y := FreeAlgebra.ι ℤ true
    let z := x+y
    let c := x*y-y*x
    let p := (1+z*x)*(1+y*z)
    f (c+p) = f c + f p

theorem main : H1 → H2 → type_of% @OMA.S_mo_478169.main := by
  intro h1 h2 R S _ _ f mul succ
  have kill (x y : R) : (f x + f y - f (x+y))*f (x+y) = 0 := by
    let e := FreeAlgebra.lift ℤ (fun b : Bool => if b then y else x)
    let g := fun v => f (e v)
    have gm u v : g (u*v) = g u * g v := by simp [g,map_mul,mul]
    have gs u : g (1+u) = 1+g u := by simp [g,map_add,map_one,succ]
    apply commutator_zero f mul succ x y
    · simpa [g,e,FreeAlgebra.lift_ι_apply] using h1 S g gm gs
    · simpa [g,e,FreeAlgebra.lift_ι_apply] using h2 S g gm gs
  intro x y
  apply Eq.symm
  apply sub_eq_zero.mp
  apply annihilate_of_shift (kill x y)
  have shifted := kill x (1+y)
  rw [show x+(1+y) = 1+(x+y) by abel, succ, succ] at shifted
  convert shifted using 1; noncomm_ring

end OMA.R_mo_478169_R1
