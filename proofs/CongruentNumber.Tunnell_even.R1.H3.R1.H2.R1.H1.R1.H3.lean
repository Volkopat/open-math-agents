import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1
import Mathlib

/-! The exact winding values at twists 2 and 34 and a positive class of norm 34. -/
namespace SignedSquareCalibration
open Finset Polynomial
open scoped Classical
noncomputable section

def iunit : GaussianInt := ⟨0,1⟩
def rot (k : ℤ) : GaussianInt :=
  if k%4=0 then 1 else if k%4=1 then iunit else if k%4=2 then -1 else -iunit
def folded := Nat.rec (motive:=fun _ => ℤ → ℕ → GaussianInt) (fun _ _ => 1)
  (fun _ f a n => let r := a.bmod n
                  rot (a.bdiv n)*(if r=0 then 1 else if 2*r= -(n:ℤ) then 1-iunit else
                    1-f (if 0≤r then -(n:ℤ) else (n:ℤ)) (2*r.natAbs)))
def symbol (a : ℤ) (d : ℕ) := folded d a d
def weight (n m : ℕ) : ℤ := if Odd m then jacobiSym n m else 0
def winding (n : ℕ) (hn : 0<n) : ℤ :=
  haveI : NeZero (4*n) := ⟨by omega⟩
  ∑ j : ZMod (4*n),weight n j.val*(symbol j.val n).re
def chordPoly (d j : ℕ) : ℤ[X] := (X^(16*d-j)-X^j)*X^(4*d)
def rootPoly (d : ℕ) : ℤ[X] := chordPoly d (2*d)*∏ j ∈ range (4*d-1),chordPoly d (j+1)
def chiPoly (d : ℕ) (hd : 0<d) : ℤ[X] :=
  haveI : NeZero (4*(2*d)) := ⟨by omega⟩
  ∑ j : ZMod (4*(2*d)),C (weight (2*d) j.val)*X^(2*j.val)
def epsilon (d : ℕ) (hd : 0<d) : ℤ :=
  if (chiPoly d hd-rootPoly d) %ₘ cyclotomic (16*d) ℤ=0 then 1 else -1

private def smallChar (n j : ℕ) : ℤ :=
  if j%2=0 then 0 else
  (if j%8=1 ∨ j%8=7 then 1 else -1) *
  (if n=2 then 1 else if j%17=0 then 0 else
    if j%17∈([1,2,4,8,9,13,15,16] : List ℕ) then 1 else -1)

private lemma tab_two (j : Fin 8) : weight 2 j.val = smallChar 2 j.val := by
  fin_cases j <;> norm_num [weight,Nat.odd_iff,smallChar,List.mem_cons]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private lemma tab_thirtyfour (j : Fin 136) : weight 34 j.val = smallChar 34 j.val := by
  fin_cases j <;> norm_num [weight,Nat.odd_iff,smallChar,List.mem_cons]

lemma winding_two : winding 2 (by decide) = 4 := by
  change (∑ j : Fin 8, weight 2 j.val*(symbol (j.val:ℤ) 2).re) = _
  simp_rw [tab_two]
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
lemma winding_thirtyfour : winding 34 (by decide) = 0 := by
  change (∑ j : Fin 136, weight 34 j.val*(symbol (j.val:ℤ) 34).re) = _
  simp_rw [tab_thirtyfour]
  decide


private lemma chi : chiPoly 1 (by decide)= X^2-X^6-X^10+X^14 := by
  change (∑ i : Fin 8, C (weight 2 i.val)*X^(2*i.val))=_
  rw [Fin.sum_univ_eight]
  norm_num [weight,Nat.odd_iff]
  ring

lemma epsilon_one : epsilon 1 (by decide)=1 := by
  rw [epsilon,if_pos]
  rw [modByMonic_eq_zero_iff_dvd (cyclotomic.monic _ _),chi]
  have h : cyclotomic 16 ℤ = X^8+1 := by
    simpa [sum_range_succ,add_comm] using cyclotomic_prime_pow_eq_geom_sum (R:=ℤ) (n:=3) Nat.prime_two
  change cyclotomic 16 ℤ ∣ _
  rw [h]
  refine ⟨(1)*X^2 + (-1)*X^6 + (-2)*X^10 + (2)*X^14 + (2)*X^18 + (-2)*X^22 + (-1)*X^24 + (-2)*X^26 + (2)*X^30 + (1)*X^32 + (3)*X^34 + (2)*X^36 + (-1)*X^38 + (-1)*X^40 + (-3)*X^42 + (-2)*X^44 + (-1)*X^46 + (-1)*X^48 + (1)*X^50 + (2)*X^52 + (1)*X^54 + (1)*X^56 + (-1)*X^64,?_⟩
  norm_num [rootPoly,chordPoly,prod_range_succ]
  ring



def classes (d : ℕ) : Finset (ℤ×ℤ×ℤ) :=
  let b := Icc (-((2*d:ℕ):ℤ)-1) (((2*d:ℕ):ℤ)+1)
  let s := (b ×ˢ (b ×ˢ b)).filter (fun v => v.1^2+v.2.1^2+v.2.2^2=((2*d:ℕ):ℤ))
  s.filter (fun v => Odd v.1 ∧ Odd v.2.1 ∧ Even v.2.2 ∧ 0<v.1 ∧ 0<v.2.1)

lemma member (d : ℕ) (x y z : ℤ) (hs : x^2+y^2+z^2=((2*d:ℕ):ℤ))
    (hx : Odd x) (hy : Odd y) (hz : Even z) (hp : 0<x) (hq : 0<y)
    (hx' : x∈Icc (-((2*d:ℕ):ℤ)-1) (((2*d:ℕ):ℤ)+1))
    (hy' : y∈Icc (-((2*d:ℕ):ℤ)-1) (((2*d:ℕ):ℤ)+1))
    (hz' : z∈Icc (-((2*d:ℕ):ℤ)-1) (((2*d:ℕ):ℤ)+1)) : 0<(classes d).card := by
  apply Finset.card_pos.mpr
  refine ⟨(x,y,z),?_⟩
  unfold classes
  simp only [mem_filter,mem_product]
  exact ⟨⟨⟨hx',hy',hz'⟩,hs⟩,hx,hy,hz,hp,hq⟩

end
end SignedSquareCalibration
open SignedSquareCalibration

theorem OMA.solution : OMA.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1.H3 := by
  change ∀ k : ℕ, (hk:k%4=1) → (k=1 → epsilon k (by omega)*winding (2*k) (by omega)=4) ∧
    (k=17 → epsilon k (by omega)*winding (2*k) (by omega)=0 ∧ 0<(classes k).card)
  intro k hk
  constructor
  · rintro rfl
    rw [epsilon_one,winding_two,one_mul]
  rintro rfl
  refine ⟨by rw [winding_thirtyfour,mul_zero],?_⟩
  exact member 17 3 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Finset.mem_Icc.mpr (by decide)) (Finset.mem_Icc.mpr (by decide)) (Finset.mem_Icc.mpr (by decide))
