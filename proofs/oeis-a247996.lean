import OMAStatements.S_oeis_a247996
import Mathlib
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

/-!
# Six entries with no equal sums of disjoint triples

We prove the two parity polynomials and the generating function conjectured
by Colin Barker for R. H. Hardin's OEIS sequence A247996.
Inclusion-exclusion uses the ten unoriented complementary triple pairs.
There are 19 classes of their subcollections under coordinate relabeling,
including the empty subcollection. The finite certificate supplies a path
of adjacent transpositions from each subcollection to a representative.
The representative counts use only free coordinates, balanced sums, and an
integral midpoint. Summing these counts gives the parity formulas and
multiplication by the generating-function denominator gives the numerator.

Source: https://oeis.org/A247996
Formal problem statement: @VashaTS, LeftToSolve PR #28528.
Earlier hyperplane analysis: @fluxxnexus, LeftToSolve desk note #166305.
-/


namespace A247996Base
open Finset PowerSeries

def equalCount (k n : ℕ) : ℕ :=
  (univ.filter fun t : (Fin k → Fin (n+1)) × (Fin k → Fin (n+1)) =>
    ∑ i, (t.1 i).val = ∑ i, (t.2 i).val).card

def midCount (n : ℕ) : ℕ :=
  (univ.filter fun x : Fin 3 → Fin (n+1) => 2*(x 0).val = (x 1).val+(x 2).val).card

end A247996Base

namespace A247996Base
open Finset PowerSeries

private noncomputable def box (n : ℕ) : PowerSeries ℚ :=
  ∑ i : Fin (n+1), X^i.val

private theorem row (k n : ℕ) (g : Fin (n+1) → ℕ) :
    (∑ i : Fin (n+1), (X:PowerSeries ℚ)^(g i))^k =
      ∑ v : Fin k → Fin (n+1), X^(∑ i,g (v i)) := by
  rw [sum_pow']
  simp only [Fintype.piFinset_univ,prod_pow_eq_pow_sum]

theorem equalCount_coeff (k n : ℕ) :
    (equalCount k n:ℚ)=coeff (k*n) ((box n)^(2*k)) := by
  classical
  have forward := row k n (fun i => i.val)
  have backward := row k n (fun i => i.rev.val)
  have hr : (∑ i : Fin (n+1), (X:PowerSeries ℚ)^i.rev.val) = box n :=
    Equiv.sum_comp (Fin.revPerm) (fun i => (X:PowerSeries ℚ)^i.val)
  rw [hr] at backward
  change (box n)^k = _ at forward
  rw [two_mul,pow_add,congrArg₂ (· * ·) forward backward]
  simp only [sum_mul,mul_sum,←pow_add,map_sum,coeff_X_pow]
  unfold equalCount
  rw [card_filter,show (univ : Finset ((Fin k → Fin (n+1)) × (Fin k → Fin (n+1)))) =
    univ ×ˢ univ from rfl, sum_product]
  push_cast
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  have htotal : (∑ i, (u i).rev.val)+(∑ i,(u i).val)=k*n := by
    rw [←sum_add_distrib]
    simp only [Fin.rev_add_cast,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    rfl
  have heq : ((∑ i,(u i).val)=(∑ i,(v i).val)) ↔ k*n=(∑ i,(v i).val)+(∑ i,(u i).rev.val) := by omega
  simp only [heq]

private theorem box_fraction (n d : ℕ) :
    box n ^(d+1) = ((1-X^(n+1))^(d+1) : PowerSeries ℚ)*
      (PowerSeries.mk fun j => ((d+j).choose d:ℚ)) := by
  have geom : box n * (1-X) = (1-X^(n+1) : PowerSeries ℚ) := by
    unfold box
    rw [Fin.sum_univ_eq_sum_range (fun i => (X:PowerSeries ℚ)^i) (n+1)]
    exact geom_sum_mul_neg X (n+1)
  rw [←geom,mul_pow,mul_assoc,mul_comm ((1-X)^(d+1)),mk_add_choose_mul_one_sub_pow_eq_one,mul_one]

theorem equal1 (n : ℕ) : (equalCount 1 n:ℚ) = ((n:ℚ)+1) := by
  rw [equalCount_coeff, show 2*1=1+1 by rfl, box_fraction]
  let F : PowerSeries ℚ := mk fun j => ((1+j).choose 1:ℚ)
  change coeff (1*n) (((1-X^(n+1))^(1+1))*F) = _
  have expand : ((1-X^(n+1))^(1+1))*F = F - (((2 : ℚ)) • (F*X^(1*(n+1)))) + (((1 : ℚ)) • (F*X^(2*(n+1)))) := by
    simp only [Algebra.smul_def, map_ofNat, map_one]
    simp only [Nat.mul_comm _ (n+1), pow_mul]
    ring
  rw [expand]
  simp only [map_sub,map_add,map_smul,smul_eq_mul,coeff_mul_X_pow',F,coeff_mk]
  have choose (m : ℕ) : ((1+m).choose 1:ℚ) = ((m:ℚ)+1)/1 := by
    simp [add_comm]
  by_cases hn : 2≤n
  · have h1 : 1*(n+1) > 1*n := by omega
    have h2 : 2*(n+1) > 1*n := by omega
    simp only [if_neg (Nat.not_le.mpr h1),if_neg (Nat.not_le.mpr h2),choose]
    push_cast
    ring
  · have h : n≤1 := by omega
    interval_cases n <;> norm_num [Nat.choose]

theorem equal2 (n : ℕ) : (equalCount 2 n:ℚ) = (2*((n:ℚ)+1)^3+((n:ℚ)+1))/3 := by
  rw [equalCount_coeff, show 2*2=3+1 by rfl, box_fraction]
  let F : PowerSeries ℚ := mk fun j => ((3+j).choose 3:ℚ)
  change coeff (2*n) (((1-X^(n+1))^(3+1))*F) = _
  have expand : ((1-X^(n+1))^(3+1))*F = F - (((4 : ℚ)) • (F*X^(1*(n+1)))) + (((6 : ℚ)) • (F*X^(2*(n+1)))) - (((4 : ℚ)) • (F*X^(3*(n+1)))) + (((1 : ℚ)) • (F*X^(4*(n+1)))) := by
    simp only [Algebra.smul_def, map_ofNat, map_one]
    simp only [Nat.mul_comm _ (n+1), pow_mul]
    ring
  rw [expand]
  simp only [map_sub,map_add,map_smul,smul_eq_mul,coeff_mul_X_pow',F,coeff_mk]
  have choose (m : ℕ) : ((3+m).choose 3:ℚ) = ((m:ℚ)+1)*((m:ℚ)+2)*((m:ℚ)+3)/6 := by
    have h := Nat.ascFactorial_eq_factorial_mul_choose m 3
    norm_num [Nat.ascFactorial,Nat.factorial] at h
    rw [Nat.add_comm 3 m]
    have hq := congrArg ((↑) : ℕ → ℚ) h
    push_cast at hq
    linarith only [hq]
  by_cases hn : 2≤n
  · have h1 : 1*(n+1) ≤ 2*n := by omega
    have h2 : 2*(n+1) > 2*n := by omega
    have h3 : 3*(n+1) > 2*n := by omega
    have h4 : 4*(n+1) > 2*n := by omega
    simp only [if_pos h1,if_neg (Nat.not_le.mpr h2),if_neg (Nat.not_le.mpr h3),if_neg (Nat.not_le.mpr h4),choose]
    rw [Nat.cast_sub h1]
    push_cast
    ring
  · have h : n≤1 := by omega
    interval_cases n <;> norm_num [Nat.choose]

theorem equal3 (n : ℕ) : (equalCount 3 n:ℚ) = (11*((n:ℚ)+1)^5+5*((n:ℚ)+1)^3+4*((n:ℚ)+1))/20 := by
  rw [equalCount_coeff, show 2*3=5+1 by rfl, box_fraction]
  let F : PowerSeries ℚ := mk fun j => ((5+j).choose 5:ℚ)
  change coeff (3*n) (((1-X^(n+1))^(5+1))*F) = _
  have expand : ((1-X^(n+1))^(5+1))*F = F - (((6 : ℚ)) • (F*X^(1*(n+1)))) + (((15 : ℚ)) • (F*X^(2*(n+1)))) - (((20 : ℚ)) • (F*X^(3*(n+1)))) + (((15 : ℚ)) • (F*X^(4*(n+1)))) - (((6 : ℚ)) • (F*X^(5*(n+1)))) + (((1 : ℚ)) • (F*X^(6*(n+1)))) := by
    simp only [Algebra.smul_def, map_ofNat, map_one]
    simp only [Nat.mul_comm _ (n+1), pow_mul]
    ring
  rw [expand]
  simp only [map_sub,map_add,map_smul,smul_eq_mul,coeff_mul_X_pow',F,coeff_mk]
  have choose (m : ℕ) : ((5+m).choose 5:ℚ) = ((m:ℚ)+1)*((m:ℚ)+2)*((m:ℚ)+3)*((m:ℚ)+4)*((m:ℚ)+5)/120 := by
    have h := Nat.ascFactorial_eq_factorial_mul_choose m 5
    norm_num [Nat.ascFactorial,Nat.factorial] at h
    rw [Nat.add_comm 5 m]
    have hq := congrArg ((↑) : ℕ → ℚ) h
    push_cast at hq
    linarith only [hq]
  by_cases hn : 2≤n
  · have h1 : 1*(n+1) ≤ 3*n := by omega
    have h2 : 2*(n+1) ≤ 3*n := by omega
    have h3 : 3*(n+1) > 3*n := by omega
    have h4 : 4*(n+1) > 3*n := by omega
    have h5 : 5*(n+1) > 3*n := by omega
    have h6 : 6*(n+1) > 3*n := by omega
    simp only [if_pos h1,if_pos h2,if_neg (Nat.not_le.mpr h3),if_neg (Nat.not_le.mpr h4),if_neg (Nat.not_le.mpr h5),if_neg (Nat.not_le.mpr h6),choose]
    rw [Nat.cast_sub h1]
    rw [Nat.cast_sub h2]
    push_cast
    ring
  · have h : n≤1 := by omega
    interval_cases n <;> norm_num [Nat.choose]

end A247996Base

namespace A247996Base
open Finset

private abbrev Mid (n : ℕ) := {x : Fin 3 → Fin (n+1) // 2*(x 0).val = (x 1).val+(x 2).val}
private abbrev Pairs (n : ℕ) := {u : Fin (n+1) × Fin (n+1) // u.1.val%2=u.2.val%2}

private def midPair (n : ℕ) : Mid n ≃ Pairs n where
  toFun x := ⟨(x.1 1,x.1 2), by dsimp only; have h:=x.2; omega⟩
  invFun u := ⟨![⟨(u.1.1.val+u.1.2.val)/2,by have := u.1.1.isLt; have := u.1.2.isLt; omega⟩,
    u.1.1,u.1.2],by dsimp; have h:=u.2; omega⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    fin_cases i <;> apply Fin.ext <;> simp
    have h := x.2
    omega
  right_inv u := by apply Subtype.ext; rfl

private def parityPair (n : ℕ) : Pairs n ≃
    (Fin (n/2+1) × Fin (n/2+1)) ⊕ (Fin ((n+1)/2) × Fin ((n+1)/2)) where
  toFun u := if h : u.1.1.val%2=0 then
    .inl (⟨u.1.1/2,by have := u.1.1.isLt; omega⟩,⟨u.1.2/2,by have := u.1.2.isLt; omega⟩)
    else .inr (⟨u.1.1/2,by have := u.1.1.isLt; omega⟩,
      ⟨u.1.2/2,by have := u.1.2.isLt; have := u.2; omega⟩)
  invFun
    | .inl (b,c) => ⟨(⟨2*b.val,by have:=b.isLt; omega⟩,⟨2*c.val,by have:=c.isLt; omega⟩),by dsimp;omega⟩
    | .inr (b,c) => ⟨(⟨2*b.val+1,by have:=b.isLt; omega⟩,⟨2*c.val+1,by have:=c.isLt; omega⟩),by dsimp;omega⟩
  left_inv u := by
    obtain ⟨⟨b,c⟩,h⟩ := u
    dsimp at h ⊢
    split_ifs with hb <;> apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
  right_inv u := by
    rcases u with ⟨b,c⟩|⟨b,c⟩ <;> simp
    constructor <;> apply Fin.ext <;> dsimp <;> omega

theorem midpoint_nat (n : ℕ) : midCount n = (n/2+1)^2 + ((n+1)/2)^2 := by
  classical
  rw [midCount,←Fintype.card_subtype]
  change Fintype.card (Mid n) = _
  rw [Fintype.card_congr ((midPair n).trans (parityPair n))]
  simp [pow_two]

theorem midpoint (n : ℕ) : (midCount n:ℚ)=(((n:ℚ)+1)^2 + if n%2=0 then 1 else 0)/2 := by
  rw [midpoint_nat]
  push_cast
  have h : n%2=0 ∨ n%2=1 := by omega
  rcases h with h|h
  · have h1 : 2*(n/2)=n := by omega
    have h2 : (n+1)/2=n/2 := by omega
    have hq := congrArg ((↑):ℕ→ℚ) h1
    push_cast at hq
    rw [h2,if_pos h,←hq]
    ring
  · have h1 : 2*(n/2)+1=n := by omega
    have h2 : (n+1)/2=n/2+1 := by omega
    have hq := congrArg ((↑):ℕ→ℚ) h1
    push_cast at hq
    rw [h2,if_neg (by omega),←hq]
    push_cast
    ring

end A247996Base

/-! Orient complementary triples by placing position zero on the chosen side.
Inclusion-exclusion then involves ten hyperplanes. -/

namespace A247996IE
open Finset OMA.S_oeis_a247996

/-- The ten triples containing zero, ordered by their remaining two positions. -/
def triple : Fin 10 → Finset (Fin 6) :=
  ![{0,1,2},{0,1,3},{0,1,4},{0,1,5},{0,2,3},{0,2,4},{0,2,5},{0,3,4},{0,3,5},{0,4,5}]

theorem triple_card : ∀ i, (triple i).card = 3 := by decide +kernel

theorem triple_or_complement : ∀ t : Finset (Fin 6), t.card = 3 →
    ∃ i : Fin 10, t = triple i ∨ t = (triple i)ᶜ := by decide +kernel

/-- Equality between the chosen triple sum and the complementary sum. -/
def bad (n : ℕ) (i : Fin 10) (x : Fin 6 → Fin (n+1)) : Prop :=
  (∑ j ∈ triple i, (x j).val) = ∑ j ∈ (triple i)ᶜ, (x j).val

instance (n : ℕ) (i : Fin 10) (x : Fin 6 → Fin (n+1)) : Decidable (bad n i x) := by
  unfold bad
  infer_instance

theorem noEqual_iff (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    NoEqualTriples n x ↔ ∀ i, ¬ bad n i x := by
  constructor
  · intro h i
    exact h (triple i) (triple_card i)
  · intro h t ht
    obtain ⟨i, hi | hi⟩ := triple_or_complement t ht
    · subst t
      exact h i
    · subst t
      simpa only [compl_compl] using Ne.symm (h i)

/-- The intersection size for a prescribed set of equalities. -/
def interCount (n : ℕ) (T : Finset (Fin 10)) : ℕ :=
  (univ.filter (fun x : Fin 6 → Fin (n+1) => ∀ i ∈ T, bad n i x)).card

private theorem inf_mem {α ι : Type*} [Fintype α] [DecidableEq α]
    (T : Finset ι) (S : ι → Finset α) (x : α) :
    x ∈ T.inf S ↔ ∀ i ∈ T, x ∈ S i := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih => simp [ih]

/-- Signed inclusion-exclusion over the ten distinct complementary partitions. -/
theorem a_eq_sum (n : ℕ) : (a n : ℤ) =
    ∑ T ∈ (univ : Finset (Fin 10)).powerset, (-1:ℤ)^T.card * (interCount n T:ℤ) := by
  classical
  let S (i : Fin 10) := univ.filter (bad n i)
  have L : (univ : Finset (Fin 10)).inf (fun i => (S i)ᶜ) =
      univ.filter (NoEqualTriples n) := by
    ext x
    simp [inf_mem,S,noEqual_iff]
  have R (T : Finset (Fin 10)) : (T.inf S).card = interCount n T := by
    unfold interCount
    congr 1
    ext x
    simp [inf_mem,S]
  have h := inclusion_exclusion_card_inf_compl (univ : Finset (Fin 10)) S
  rw [L] at h
  simpa only [a,R] using h

theorem a_eq_sum_rat (n : ℕ) : (a n : ℚ) =
    ∑ T ∈ (univ : Finset (Fin 10)).powerset, (-1:ℚ)^T.card * (interCount n T:ℚ) := by
  exact_mod_cast a_eq_sum n

/-- Signed coefficients of the oriented equality. -/
def coeff (i : Fin 10) (j : Fin 6) : ℤ := if j ∈ triple i then 1 else -1

theorem bad_iff (n : ℕ) (i : Fin 10) (x : Fin 6 → Fin (n+1)) :
    bad n i x ↔ ∑ j : Fin 6, coeff i j * ((x j).val:ℤ) = 0 := by
  classical
  have hin : ∑ j ∈ triple i, coeff i j * ((x j).val:ℤ) =
      ∑ j ∈ triple i, ((x j).val:ℤ) :=
    sum_congr rfl fun j hj => by simp [coeff,hj]
  have hout : ∑ j ∈ (triple i)ᶜ, coeff i j * ((x j).val:ℤ) =
      -(∑ j ∈ (triple i)ᶜ, ((x j).val:ℤ)) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun j hj => by simp [coeff,mem_compl.mp hj]
  rw [← sum_add_sum_compl (triple i),hin,hout,←sub_eq_add_neg,sub_eq_zero]
  unfold bad
  norm_cast

/-- An ordinary ten-bit mask for a subset of the ten equalities. -/
def mask (m : Fin 1024) : Finset (Fin 10) := univ.filter (fun i => m.val.testBit i.val)

theorem mask_bijective : Function.Bijective mask := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,by simp⟩
  intro a b hab
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k<10
  · have h : (⟨k,hk⟩ : Fin 10) ∈ mask a ↔ ⟨k,hk⟩ ∈ mask b := by rw [hab]
    simpa [mask] using h
  · have h : 2^10 ≤ (2:ℕ)^k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (a.isLt.trans_le h),Nat.testBit_eq_false_of_lt (b.isLt.trans_le h)]

theorem a_eq_mask_sum (n : ℕ) : (a n : ℤ) =
    ∑ m : Fin 1024, (-1:ℤ)^(mask m).card * (interCount n (mask m):ℤ) := by
  classical
  let f (T : Finset (Fin 10)) := (-1:ℤ)^T.card * (interCount n T:ℤ)
  calc
    (a n:ℤ) = ∑ T, f T := by simpa [f] using a_eq_sum n
    _ = _ := ((Equiv.ofBijective mask mask_bijective).sum_comp f).symm

end A247996IE

/-! Counting normal forms for intersections of the ten complementary-triple equalities. -/

namespace A247996Normal
open Finset A247996Base

/-- Bijections restricted to the satisfying assignments preserve the filtered count. -/
theorem card_transport {X Y : Type*} [Fintype X] [Fintype Y] (P : X → Prop) (Q : Y → Prop)
    [DecidablePred P] [DecidablePred Q] (F : X → Y) (G : Y → X)
    (toQ : ∀ x, P x → Q (F x)) (toP : ∀ y, Q y → P (G y))
    (left : ∀ x, P x → G (F x)=x) (right : ∀ y, Q y → F (G y)=y) :
    (univ.filter P).card = (univ.filter Q).card := by
  let e : {x // P x} ≃ {y // Q y} := {
    toFun := fun x => ⟨F x, toQ x x.property⟩
    invFun := fun y => ⟨G y, toP y y.property⟩
    left_inv := fun x => Subtype.ext (left x x.property)
    right_inv := fun y => Subtype.ext (right y y.property) }
  simpa [Fintype.card_subtype] using Fintype.card_congr e

/-- Free coordinates times one equality between two independent sums. -/
theorem card_eq (n k z : ℕ) :
    (univ.filter (fun y : (Fin z → Fin (n+1)) ×
        ((Fin k → Fin (n+1)) × (Fin k → Fin (n+1))) =>
      ∑ i, (y.2.1 i).val = ∑ i, (y.2.2 i).val)).card =
      (n+1)^z * equalCount k n := by
  classical
  let Q (t : (Fin k → Fin (n+1)) × (Fin k → Fin (n+1))) :=
    (∑ i, (t.1 i).val) = ∑ i, (t.2 i).val
  change (univ.filter (fun y : (Fin z → Fin (n+1)) × _ => Q y.2)).card = _
  rw [← univ_product_univ,filter_product_right Q,card_product,card_univ,Fintype.card_fun]
  simp only [Fintype.card_fin,equalCount,Q]

/-- All the coordinates are free. -/
theorem card_free (n z : ℕ) :
    (univ.filter (fun _ : Fin z → Fin (n+1) => True)).card = (n+1)^z := by simp

/-- One coordinate is the midpoint of the other two. -/
theorem card_mid (n : ℕ) :
    (univ.filter (fun x : Fin 3 → Fin (n+1) =>
        2*(x 0).val=(x 1).val+(x 2).val)).card = midCount n := rfl

end A247996Normal

namespace A247996Orbit

/-- Action of the identity and the five adjacent coordinate transpositions
on complementary triple partitions, in increasing lexicographic order. -/
def move (g : Fin 6) (i : Fin 10) : Fin 10 :=
  ![![0,1,2,3,4,5,6,7,8,9], ![0,1,2,3,9,8,7,6,5,4],
    ![0,4,5,6,1,2,3,7,8,9], ![1,0,2,3,4,7,8,5,6,9],
    ![0,2,1,3,5,4,6,7,9,8], ![0,1,3,2,4,6,5,8,7,9]] g i

end A247996Orbit

namespace A247996Orbit

open Finset A247996IE

/-- The identity and the five adjacent transpositions of the six coordinates. -/
def adjacent (g : Fin 6) : Equiv.Perm (Fin 6) :=
  if g=0 then Equiv.refl _ else Equiv.swap ⟨g.val-1,by omega⟩ g

theorem adjacent_inv : ∀ (g i : Fin 6), adjacent g (adjacent g i) = i := by decide +kernel

theorem move_inv : ∀ (g : Fin 6) (i : Fin 10), move g (move g i) = i := by decide +kernel

private theorem sends_pair : ∀ (g : Fin 6) (i : Fin 10),
    ((triple i).map (adjacent g).toEmbedding = triple (move g i) ∧
      ((triple i)ᶜ).map (adjacent g).toEmbedding = (triple (move g i))ᶜ) ∨
    ((triple i).map (adjacent g).toEmbedding = (triple (move g i))ᶜ ∧
      ((triple i)ᶜ).map (adjacent g).toEmbedding = triple (move g i)) := by
  decide +kernel

theorem bad_adjacent (n : ℕ) (g : Fin 6) (i : Fin 10) (x : Fin 6 → Fin (n+1)) :
    bad n i (x ∘ adjacent g) ↔ bad n (move g i) x := by
  unfold bad
  simp only [Function.comp_apply]
  let f := fun j : Fin 6 => (x j).val
  change (∑ j ∈ triple i, f ((adjacent g).toEmbedding j)) =
      (∑ j ∈ (triple i)ᶜ, f ((adjacent g).toEmbedding j)) ↔
    (∑ j ∈ triple (move g i), f j) = (∑ j ∈ (triple (move g i))ᶜ, f j)
  rw [← sum_map (triple i) (adjacent g).toEmbedding f,
    ← sum_map ((triple i)ᶜ) (adjacent g).toEmbedding f]
  rcases sends_pair g i with h | h
  · rw [h.1,h.2]
  · rw [h.1,h.2,eq_comm]

/-- Relabeling the coordinates preserves every intersection cardinality. -/
theorem inter_count_image (n : ℕ) (g : Fin 6) (T : Finset (Fin 10)) :
    interCount n (T.image (move g)) = interCount n T := by
  let good (U : Finset (Fin 10)) (x : Fin 6 → Fin (n+1)) := ∀ i ∈ U, bad n i x
  let e : {x // good (T.image (move g)) x} ≃ {x // good T x} := {
    toFun := fun x => ⟨x.val ∘ adjacent g, fun i hi =>
      (bad_adjacent n g i x.val).mpr (x.property _ (mem_image_of_mem _ hi))⟩
    invFun := fun x => ⟨x.val ∘ adjacent g, fun i hi => by
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
      exact (bad_adjacent n g (move g j) x.val).mpr (by
        rw [move_inv]
        exact x.property _ hj)⟩
    left_inv := fun x => Subtype.ext (funext (fun j => congrArg x.val (adjacent_inv g j)))
    right_inv := fun x => Subtype.ext (funext (fun j => congrArg x.val (adjacent_inv g j))) }
  simpa [interCount,good,Fintype.card_subtype] using Fintype.card_congr e

theorem interCount_swap (n : ℕ) (g : Fin 6) (m m' : Fin 1024)
    (h : ∀ i : Fin 10, i ∈ mask m ↔ move g i ∈ mask m') :
    interCount n (mask m) = interCount n (mask m') := by
  have he : (mask m).image (move g) = mask m' := by
    ext j
    constructor
    · intro hj
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hj
      exact (h k).mp hk
    · intro hj
      refine mem_image.mpr ⟨move g j,(h _).mpr ?_,move_inv g j⟩
      simpa only [move_inv] using hj
  rw [← he]
  exact (inter_count_image n g (mask m)).symm

end A247996Orbit

namespace A247996Orbit

/-- Minimal bit-mask representative of each of the 19 coordinate orbits. -/
def rep (i : Fin 19) : Fin 1024 := ![0,1,3,7,15,21,23,31,54,55,59,63,126,127,207,223,255,511,1023] i

/-- Size of each orbit of complementary-triple hyperplane subcollections. -/
def pop (i : Fin 19) : ℕ := ![1,10,45,60,15,60,180,90,15,90,72,180,15,60,15,60,45,10,1] i

/-- For a mask, the certificate records its adjacent-swap parent, orbit label,
swap index, and distance to the representative. Each field is checked below. -/
private def packed : Array ℕ := #[
  67269988766594604376215747180978644087939048278782042681734017984909830805942966518842942326668564287997490173107402302006438919052996208709984764679973186917034624114022581729335613192637060762042368,
  105841532996065199785230362268668642923540468403161892223865395365902047977823355859279391065890661786893538099085728410548806409449946303474430623470542385888020439293970639621799636413168724956580880,
  2105580489869102206384308455944564222903041817635238637617278813210804744131591804247436522277856333083661854152510088341439217495827287947286150071005564654333316573706513324217002183182984649711853600,
  125572436926155188781376967142744740148923824986528959547156726968763594360566937142519098643177339184012538277349245548753536011304076210862868663571203891757533082677542839953029855589237240929853520,
  1741989937366668836071990235512027114651741435408931373144520213988637800191864545557689136773014236350146616802534321885036368485660183578550154091587911346096678300602999179770437752170403255510632480,
  5399709800126418949852038579676314298693509945978429132983527759133201840850789907468171256636009066492558926317987401869682515600335831609680589226331494405512823303279217991307322275772971557755390084,
  145610735930943991278081720771850441041271827971409915213890531886640450477028414165155917009311615758131216700130389053950305628540440329866989295867671693609245742206109809947454444077069172468325664,
  155476927720087278720948005993096041623733521972347656072717850427594288013768121417469406531919798288324203299031550038240707611804910340519092630980622674401107380608442446488355170405187676982056076,
  3197243626465927835540361335533109044711982210071843294173698823876750303571712904253532912716816765782659634369080294196615871504236214723751925614556096542740546055753291640104240170942167211252930048,
  1781760698017835570613749193521471775546717051930050240642695880398898628541085799352523094363735292388697801372368597903396486726286308346137105384724652178275630191043406286420627920104236577576329744,
  4129689330646539224021895665890993347835897640443095073185878389696801927758911582323747644157024410377674930666616728507782988208420840697591853705783170520989796642560502391893664693228173078620210336,
  2155215798477057627425221587484025449677972519970210654726323589242040503088046902202670783812086845384117913308541012304901353086698706192609825808074206321544312665492795080246772736666583574617140816,
  1761725253598584079247210925058532132013426993517160741010400683049314676483611841989298736073966885879019623445639604753558459925750757704133802225264331650942585276992450430942013001060277783957858944,
  1791625163133891710608810913342298789060376247348991090229655740182130254345464329815334538852078262352054597843770780448452847901853265512885281333509168576288248855375935529386507609705350140862803600,
  3247775864985745294230838995488982965626490117713390932348438969873177457738282115638277339574886112248094939264518786314847247933212552780104672283682130475511603200201546482247126086919166809521013152,
  167436500647583195872214519966315159799467555218891924396566030828772591313829923358192951278758367800102009614699194982919764543561983459069867806803158147922023816520698568891729055225804823194006224,
  3045499810070424877321708420727755895187913867215741729825446468594044105020709473736630049542717203646006611156132048654226149684809511529899994459237312342909070653332741904921076350232246889803524112,
  3055218762046947778647740995059713139961941994266833489242390498798175339322087009012921387077757051180220371264756686239989241526697636868430810028393203442091851938000430644119051673850327711487899200,
  4330171413330260521986152142730953506505921539947148410394185252231801350397097449345218059151780487112526205331484082405275546669893080518405003642582476696504952783485140937091373073379673402900036752,
  3065383525298160904572936000111988911852864217002719626059108961238104435524565838980696868291190108713283993306138082530344590762091310145512364747253604116534704225578988095487445769598466712956242320,
  3966581984560063408339300826098759879012482503674821190718301927105270496977323507862354825332001261987385529990788249458493411313052540324161112517478025199307001370190599805040384779664662001563102976,
  3065981194891785422298640830944801379010481747000972989009731769787491456640687571978308609828227566067912662113408267662048519004730653199976289733301801233960151189746557824561269483536452300183393924,
  8159181525619525337274785687467278101810972621961865507487348994274595651792390602908390134923453637866624719407352919481839485221179289409269531221291722032461191863794733007385281272125269584332277968,
  1985380700031859086461799994937319236365546649908468655994214266285337888655488340130557060156669369046678119508318508405480498954744062196084119521836380188629174060170858615288051120834298780821826188,
  4150619793031530964459290995106346978523240470329944608740780730845037253840921997582784512685271829433218283493386666663278978396535973290344023826566588172529169646245147196149260634747173905268962352,
  7069572399473237672585625178121489277967945627190839368005698808975760414392202651531574360832420411731326575728994843138266501683025896321438726987065562867983374090448454632955320444750407610384658192,
  4160785171766722938468379571386056517429887845787038561429478109099096293139137414970553985470714878075607086257717707160001625025317340530366461158197857894491842788660365915656251250872971390798864136,
  3260335083758676126761147613931073773935809260021741757713518252295989239689972101731135974755947871047054379078197067650187310627189483106592521175862474765733293027142350020950450371336799190946354608,
  4161382651274859088885866502386098419954786018489205187856803780276170175170221369655850336926845482825237264956385850082216343257271593589227580510887612585359763990023899245556057149537256110895480944,
  2896745568925836674984820777978515053814047921250280648653728780972124844063862958838251393315291769948142712379591252387470223471232343114177070867302724993056771488732333689280031022475409611532473712,
  3080781817542457264558352726789865748590249188270416506560193202532358913887700717373867543077846669347730507053751425658172897354255113329208734964300303236588634802462986960873543246543604546789788912,
  181787056503028768106977648513868284286130490140560281198196372965318188388327398661034304116698769473918411223064174366725175259924459806459042085735894773724140542695693148985456022373080479572777456]

private def datum (m : Fin 1024) : ℕ :=
  ((packed[m.val/32]?.getD 0) >>> (21*(m.val%32))) % (2^21)

def parent (m : Fin 1024) : Fin 1024 := Fin.ofNat 1024 (datum m)

def tag (m : Fin 1024) : Fin 19 := Fin.ofNat 19 (datum m / 1024)

def gen (m : Fin 1024) : Fin 6 := Fin.ofNat 6 (datum m / (1024*19))

def depth (m : Fin 1024) : ℕ := datum m / (1024*19*6)

end A247996Orbit

/-! Check all rows of the finite permutation-orbit certificate and descend to the representatives. -/

namespace A247996Orbit
open Finset A247996IE

private def rowOK (m : Fin 1024) : Prop :=
    (∀ i : Fin 10, m.val.testBit i.val = (parent m).val.testBit (move (gen m) i).val) ∧
    tag (parent m) = tag m ∧ (m = rep (tag m) ∨ depth (parent m) < depth m)

private instance rowDecision (m : Fin 1024) : Decidable (rowOK m) := by
  unfold rowOK
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem row_grid : ∀ a b : Fin 32, rowOK (finProdFinEquiv (a,b)) := by
  decide +kernel

private theorem table_rows (m : Fin 1024) : rowOK m := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (finProdFinEquiv (m:=32) (n:=32)).surjective m
  exact row_grid a b

private theorem member_swap (m : Fin 1024) (i : Fin 10) :
    i ∈ mask m ↔ move (gen m) i ∈ mask (parent m) := by
  simp only [mask, mem_filter, mem_univ, true_and]
  rw [(table_rows m).1 i]

private theorem card_swap (m : Fin 1024) : (mask m).card = (mask (parent m)).card := by
  apply card_bij' (fun i _ => move (gen m) i) (fun i _ => move (gen m) i)
  · intro i hi
    exact (member_swap m i).mp hi
  · intro i hi
    apply (member_swap m _).mpr
    rwa [move_inv]
  · intro i _
    exact move_inv _ _
  · intro i _
    exact move_inv _ _

/-- Each mask has the signed intersection count of its recorded orbit representative. -/
theorem signed_orbit (n : ℕ) (m : Fin 1024) :
    (-1:ℤ)^(mask m).card * (interCount n (mask m):ℤ) =
      (-1:ℤ)^(mask (rep (tag m))).card * (interCount n (mask (rep (tag m))):ℤ) := by
  let val (m : Fin 1024) := (-1:ℤ)^(mask m).card * (interCount n (mask m):ℤ)
  have step (m : Fin 1024) : val m = val (parent m) :=
    congrArg₂ (· * ·) (congrArg (fun k : ℕ => (-1:ℤ)^k) (card_swap m))
      (congrArg (Nat.cast : ℕ → ℤ) (interCount_swap n (gen m) m (parent m) (member_swap m)))
  have descend (d : ℕ) : ∀ x : Fin 1024, depth x = d → val x = val (rep (tag x)) := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro x hx
      obtain ⟨_,ht,he | hl⟩ := table_rows x
      · exact congrArg val he
      · exact (step x).trans ((ih (depth (parent x)) (hl.trans_eq hx) (parent x) rfl).trans
          (congrArg (fun k => val (rep k)) ht))
  exact descend (depth m) m rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
/-- Population of each of the nineteen tags in the permutation-orbit table. -/
theorem population : ∀ i : Fin 19, (univ.filter fun m : Fin 1024 => tag m = i).card = pop i := by
  decide +kernel

end A247996Orbit

namespace A247996Classes
open Finset A247996IE A247996Normal A247996Base

private theorem row0 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    bad n 0 x ↔ (x 0).val + (x 1).val + (x 2).val = (x 3).val + (x 4).val + (x 5).val := by
  have h : triple 0 = {0,1,2} := by decide
  have hc : (triple 0)ᶜ = {3,4,5} := by decide
  rw [bad, hc, h]
  simp (disch := decide) only [sum_insert, sum_singleton]
  omega

private theorem row1 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    bad n 1 x ↔ (x 0).val + (x 1).val + (x 3).val = (x 2).val + (x 4).val + (x 5).val := by
  have h : triple 1 = {0,1,3} := by decide
  have hc : (triple 1)ᶜ = {2,4,5} := by decide
  rw [bad, hc, h]
  simp (disch := decide) only [sum_insert, sum_singleton]
  omega

private theorem row2 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    bad n 2 x ↔ (x 0).val + (x 1).val + (x 4).val = (x 2).val + (x 3).val + (x 5).val := by
  have h : triple 2 = {0,1,4} := by decide
  have hc : (triple 2)ᶜ = {2,3,5} := by decide
  rw [bad, hc, h]
  simp (disch := decide) only [sum_insert, sum_singleton]
  omega

private theorem row3 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    bad n 3 x ↔ (x 0).val + (x 1).val + (x 5).val = (x 2).val + (x 3).val + (x 4).val := by
  have h : triple 3 = {0,1,5} := by decide
  have hc : (triple 3)ᶜ = {2,3,4} := by decide
  rw [bad, hc, h]
  simp (disch := decide) only [sum_insert, sum_singleton]
  omega

private theorem row4 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    bad n 4 x ↔ (x 0).val + (x 2).val + (x 3).val = (x 1).val + (x 4).val + (x 5).val := by
  have h : triple 4 = {0,2,3} := by decide
  have hc : (triple 4)ᶜ = {1,4,5} := by decide
  rw [bad, hc, h]
  simp (disch := decide) only [sum_insert, sum_singleton]
  omega

private theorem row5 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    bad n 5 x ↔ (x 0).val + (x 2).val + (x 4).val = (x 1).val + (x 3).val + (x 5).val := by
  have h : triple 5 = {0,2,4} := by decide
  have hc : (triple 5)ᶜ = {1,3,5} := by decide
  rw [bad, hc, h]
  simp (disch := decide) only [sum_insert, sum_singleton]
  omega

private theorem row6 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    bad n 6 x ↔ (x 0).val + (x 2).val + (x 5).val = (x 1).val + (x 3).val + (x 4).val := by
  have h : triple 6 = {0,2,5} := by decide
  have hc : (triple 6)ᶜ = {1,3,4} := by decide
  rw [bad, hc, h]
  simp (disch := decide) only [sum_insert, sum_singleton]
  omega

private theorem row7 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    bad n 7 x ↔ (x 0).val + (x 3).val + (x 4).val = (x 1).val + (x 2).val + (x 5).val := by
  have h : triple 7 = {0,3,4} := by decide
  have hc : (triple 7)ᶜ = {1,2,5} := by decide
  rw [bad, hc, h]
  simp (disch := decide) only [sum_insert, sum_singleton]
  omega

private theorem row8 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    bad n 8 x ↔ (x 0).val + (x 3).val + (x 5).val = (x 1).val + (x 2).val + (x 4).val := by
  have h : triple 8 = {0,3,5} := by decide
  have hc : (triple 8)ᶜ = {1,2,4} := by decide
  rw [bad, hc, h]
  simp (disch := decide) only [sum_insert, sum_singleton]
  omega

private theorem row9 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    bad n 9 x ↔ (x 0).val + (x 4).val + (x 5).val = (x 1).val + (x 2).val + (x 3).val := by
  have h : triple 9 = {0,4,5} := by decide
  have hc : (triple 9)ᶜ = {1,2,3} := by decide
  rw [bad, hc, h]
  simp (disch := decide) only [sum_insert, sum_singleton]
  omega

private theorem relations0 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 0, bad n i x) ↔ True := by
  have h : mask 0 = ∅ := by decide +kernel
  simp [h]

theorem class0 (n : ℕ) : interCount n (mask 0) = (n+1)^6 := by
  let Y := Fin 6 → Fin (n+1)
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => ![x 0,x 1,x 2,x 3,x 4,x 5]
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y 0,y 1,y 2,y 3,y 4,y 5]
  unfold interCount
  refine (card_transport _ (fun _ => True : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_free n 6)
  · intro x hx
    rw [relations0] at hx
    trivial
  · intro y hy
    rw [relations0]
    simp at *
  · intro x hx
    rw [relations0] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G]
  · intro y _
    funext i; fin_cases i <;> rfl

private theorem relations1 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 1, bad n i x) ↔ ((x 0).val + (x 1).val + (x 2).val = (x 3).val + (x 4).val + (x 5).val) := by
  have h : mask 1 = {0} := by decide +kernel
  simp [h, row0]

theorem class1 (n : ℕ) : interCount n (mask 1) = (n+1)^0 * equalCount 3 n := by
  let Y := (Fin 0 → Fin (n+1)) × ((Fin 3 → Fin (n+1)) × (Fin 3 → Fin (n+1)))
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => (![], ![x 0,x 1,x 2], ![x 3,x 4,x 5])
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y.2.1 0,y.2.1 1,y.2.1 2,y.2.2 0,y.2.2 1,y.2.2 2]
  unfold interCount
  refine (card_transport _ (fun y => (∑ i, (y.2.1 i).val) = ∑ i, (y.2.2 i).val : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_eq n 3 0)
  · intro x hx
    rw [relations1] at hx
    simp [F, Fin.sum_univ_succ] at * ; omega
  · intro y hy
    rw [relations1]
    simp [G, Fin.sum_univ_succ] at * ; omega
  · intro x hx
    rw [relations1] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G]
  · intro y _
    rcases y with ⟨u,v,w⟩
    apply Prod.ext
    · funext i; fin_cases i
    · apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

private theorem relations3 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 3, bad n i x) ↔ ((x 0).val + (x 1).val + (x 2).val = (x 3).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 3).val = (x 2).val + (x 4).val + (x 5).val) := by
  have h : mask 3 = {0,1} := by decide +kernel
  simp [h, row0, row1]

theorem class3 (n : ℕ) : interCount n (mask 3) = (n+1)^1 * equalCount 2 n := by
  let Y := (Fin 1 → Fin (n+1)) × ((Fin 2 → Fin (n+1)) × (Fin 2 → Fin (n+1)))
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => (![x 2], ![x 0,x 1], ![x 4,x 5])
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y.2.1 0,y.2.1 1,y.1 0,y.1 0,y.2.2 0,y.2.2 1]
  unfold interCount
  refine (card_transport _ (fun y => (∑ i, (y.2.1 i).val) = ∑ i, (y.2.2 i).val : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_eq n 2 1)
  · intro x hx
    rw [relations3] at hx
    simp [F, Fin.sum_univ_succ] at * ; omega
  · intro y hy
    rw [relations3]
    simp [G, Fin.sum_univ_succ] at * ; omega
  · intro x hx
    rw [relations3] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G] ; omega
  · intro y _
    rcases y with ⟨u,v,w⟩
    apply Prod.ext
    · funext i; fin_cases i ; rfl
    · apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

private theorem relations7 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 7, bad n i x) ↔ ((x 0).val + (x 1).val + (x 2).val = (x 3).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 3).val = (x 2).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 4).val = (x 2).val + (x 3).val + (x 5).val) := by
  have h : mask 7 = {0,1,2} := by decide +kernel
  simp [h, row0, row1, row2]

theorem class7 (n : ℕ) : interCount n (mask 7) = (n+1)^0 * equalCount 2 n := by
  let Y := (Fin 0 → Fin (n+1)) × ((Fin 2 → Fin (n+1)) × (Fin 2 → Fin (n+1)))
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => (![], ![x 0,x 1], ![x 5,x 2])
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y.2.1 0,y.2.1 1,y.2.2 1,y.2.2 1,y.2.2 1,y.2.2 0]
  unfold interCount
  refine (card_transport _ (fun y => (∑ i, (y.2.1 i).val) = ∑ i, (y.2.2 i).val : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_eq n 2 0)
  · intro x hx
    rw [relations7] at hx
    simp [F, Fin.sum_univ_succ] at * ; omega
  · intro y hy
    rw [relations7]
    simp [G, Fin.sum_univ_succ] at * ; omega
  · intro x hx
    rw [relations7] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G] <;> omega
  · intro y _
    rcases y with ⟨u,v,w⟩
    apply Prod.ext
    · funext i; fin_cases i
    · apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

private theorem relations15 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 15, bad n i x) ↔ ((x 0).val + (x 1).val + (x 2).val = (x 3).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 3).val = (x 2).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 4).val = (x 2).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 5).val = (x 2).val + (x 3).val + (x 4).val) := by
  have h : mask 15 = {0,1,2,3} := by decide +kernel
  simp [h, row0, row1, row2, row3]

theorem class15 (n : ℕ) : interCount n (mask 15) = midCount n := by
  let Y := Fin 3 → Fin (n+1)
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => ![x 2,x 0,x 1]
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y 1,y 2,y 0,y 0,y 0,y 0]
  unfold interCount
  refine (card_transport _ (fun y => 2*(y 0).val=(y 1).val+(y 2).val : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_mid n)
  · intro x hx
    rw [relations15] at hx
    simp [F] at * ; omega
  · intro y hy
    rw [relations15]
    simp [G] at * ; omega
  · intro x hx
    rw [relations15] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G] <;> omega
  · intro y _
    funext i; fin_cases i <;> rfl

private theorem relations21 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 21, bad n i x) ↔ ((x 0).val + (x 1).val + (x 2).val = (x 3).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 4).val = (x 2).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 3).val = (x 1).val + (x 4).val + (x 5).val) := by
  have h : mask 21 = {0,2,4} := by decide +kernel
  simp [h, row0, row2, row4]

theorem class21 (n : ℕ) : interCount n (mask 21) = (n+1)^3 := by
  let Y := Fin 3 → Fin (n+1)
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => ![x 2,x 1,x 0]
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y 2,y 1,y 0,y 1,y 0,y 2]
  unfold interCount
  refine (card_transport _ (fun _ => True : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_free n 3)
  · intro x hx
    rw [relations21] at hx
    trivial
  · intro y hy
    rw [relations21]
    simp [G] at * ; omega
  · intro x hx
    rw [relations21] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G] <;> omega
  · intro y _
    funext i; fin_cases i <;> rfl

private theorem relations23 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 23, bad n i x) ↔ ((x 0).val + (x 1).val + (x 2).val = (x 3).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 3).val = (x 2).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 4).val = (x 2).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 3).val = (x 1).val + (x 4).val + (x 5).val) := by
  have h : mask 23 = {0,1,2,4} := by decide +kernel
  simp [h, row0, row1, row2, row4]

theorem class23 (n : ℕ) : interCount n (mask 23) = (n+1)^2 := by
  let Y := Fin 2 → Fin (n+1)
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => ![x 1,x 0]
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y 1,y 0,y 0,y 0,y 0,y 1]
  unfold interCount
  refine (card_transport _ (fun _ => True : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_free n 2)
  · intro x hx
    rw [relations23] at hx
    trivial
  · intro y hy
    rw [relations23]
    simp [G] at * ; omega
  · intro x hx
    rw [relations23] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G] <;> omega
  · intro y _
    funext i; fin_cases i <;> rfl

private theorem relations31 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 31, bad n i x) ↔ ((x 0).val + (x 1).val + (x 2).val = (x 3).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 3).val = (x 2).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 4).val = (x 2).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 5).val = (x 2).val + (x 3).val + (x 4).val) ∧ ((x 0).val + (x 2).val + (x 3).val = (x 1).val + (x 4).val + (x 5).val) := by
  have h : mask 31 = {0,1,2,3,4} := by decide +kernel
  simp [h, row0, row1, row2, row3, row4]

theorem class31 (n : ℕ) : interCount n (mask 31) = (n+1)^1 := by
  let Y := Fin 1 → Fin (n+1)
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => ![x 0]
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y 0,y 0,y 0,y 0,y 0,y 0]
  unfold interCount
  refine (card_transport _ (fun _ => True : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_free n 1)
  · intro x hx
    rw [relations31] at hx
    trivial
  · intro y hy
    rw [relations31]
    simp [G] at *
  · intro x hx
    rw [relations31] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G] <;> omega
  · intro y _
    funext i; fin_cases i ; rfl

private theorem relations54 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 54, bad n i x) ↔ ((x 0).val + (x 1).val + (x 3).val = (x 2).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 4).val = (x 2).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 3).val = (x 1).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 4).val = (x 1).val + (x 3).val + (x 5).val) := by
  have h : mask 54 = {1,2,4,5} := by decide +kernel
  simp [h, row1, row2, row4, row5]

theorem class54 (n : ℕ) : interCount n (mask 54) = (n+1)^3 := by
  let Y := Fin 3 → Fin (n+1)
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => ![x 3,x 1,x 0]
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y 2,y 1,y 1,y 0,y 0,y 2]
  unfold interCount
  refine (card_transport _ (fun _ => True : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_free n 3)
  · intro x hx
    rw [relations54] at hx
    trivial
  · intro y hy
    rw [relations54]
    simp [G] at * ; omega
  · intro x hx
    rw [relations54] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G] <;> omega
  · intro y _
    funext i; fin_cases i <;> rfl

private theorem relations55 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 55, bad n i x) ↔ ((x 0).val + (x 1).val + (x 2).val = (x 3).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 3).val = (x 2).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 4).val = (x 2).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 3).val = (x 1).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 4).val = (x 1).val + (x 3).val + (x 5).val) := by
  have h : mask 55 = {0,1,2,4,5} := by decide +kernel
  simp [h, row0, row1, row2, row4, row5]

theorem class55 (n : ℕ) : interCount n (mask 55) = (n+1)^2 := by
  let Y := Fin 2 → Fin (n+1)
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => ![x 1,x 0]
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y 1,y 0,y 0,y 0,y 0,y 1]
  unfold interCount
  refine (card_transport _ (fun _ => True : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_free n 2)
  · intro x hx
    rw [relations55] at hx
    trivial
  · intro y hy
    rw [relations55]
    simp [G] at * ; omega
  · intro x hx
    rw [relations55] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G] <;> omega
  · intro y _
    funext i; fin_cases i <;> rfl

private theorem relations59 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 59, bad n i x) ↔ ((x 0).val + (x 1).val + (x 2).val = (x 3).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 3).val = (x 2).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 5).val = (x 2).val + (x 3).val + (x 4).val) ∧ ((x 0).val + (x 2).val + (x 3).val = (x 1).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 4).val = (x 1).val + (x 3).val + (x 5).val) := by
  have h : mask 59 = {0,1,3,4,5} := by decide +kernel
  simp [h, row0, row1, row3, row4, row5]

theorem class59 (n : ℕ) : interCount n (mask 59) = (n+1)^1 := by
  let Y := Fin 1 → Fin (n+1)
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => ![x 0]
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y 0,y 0,y 0,y 0,y 0,y 0]
  unfold interCount
  refine (card_transport _ (fun _ => True : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_free n 1)
  · intro x hx
    rw [relations59] at hx
    trivial
  · intro y hy
    rw [relations59]
    simp [G] at *
  · intro x hx
    rw [relations59] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G] <;> omega
  · intro y _
    funext i; fin_cases i ; rfl

private theorem relations63 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 63, bad n i x) ↔ ((x 0).val + (x 1).val + (x 2).val = (x 3).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 3).val = (x 2).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 4).val = (x 2).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 5).val = (x 2).val + (x 3).val + (x 4).val) ∧ ((x 0).val + (x 2).val + (x 3).val = (x 1).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 4).val = (x 1).val + (x 3).val + (x 5).val) := by
  have h : mask 63 = {0,1,2,3,4,5} := by decide +kernel
  simp [h, row0, row1, row2, row3, row4, row5]

theorem class63 (n : ℕ) : interCount n (mask 63) = (n+1)^1 := by
  let Y := Fin 1 → Fin (n+1)
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => ![x 0]
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y 0,y 0,y 0,y 0,y 0,y 0]
  unfold interCount
  refine (card_transport _ (fun _ => True : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_free n 1)
  · intro x hx
    rw [relations63] at hx
    trivial
  · intro y hy
    rw [relations63]
    simp [G] at *
  · intro x hx
    rw [relations63] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G] <;> omega
  · intro y _
    funext i; fin_cases i ; rfl

private theorem relations126 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 126, bad n i x) ↔ ((x 0).val + (x 1).val + (x 3).val = (x 2).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 4).val = (x 2).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 5).val = (x 2).val + (x 3).val + (x 4).val) ∧ ((x 0).val + (x 2).val + (x 3).val = (x 1).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 4).val = (x 1).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 5).val = (x 1).val + (x 3).val + (x 4).val) := by
  have h : mask 126 = {1,2,3,4,5,6} := by decide +kernel
  simp [h, row1, row2, row3, row4, row5, row6]

theorem class126 (n : ℕ) : interCount n (mask 126) = (n+1)^2 := by
  let Y := Fin 2 → Fin (n+1)
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => ![x 1,x 0]
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y 1,y 0,y 0,y 1,y 1,y 1]
  unfold interCount
  refine (card_transport _ (fun _ => True : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_free n 2)
  · intro x hx
    rw [relations126] at hx
    trivial
  · intro y hy
    rw [relations126]
    simp [G] at * ; omega
  · intro x hx
    rw [relations126] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G] <;> omega
  · intro y _
    funext i; fin_cases i <;> rfl

private theorem relations127 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 127, bad n i x) ↔ ((x 0).val + (x 1).val + (x 2).val = (x 3).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 3).val = (x 2).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 4).val = (x 2).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 5).val = (x 2).val + (x 3).val + (x 4).val) ∧ ((x 0).val + (x 2).val + (x 3).val = (x 1).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 4).val = (x 1).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 5).val = (x 1).val + (x 3).val + (x 4).val) := by
  have h : mask 127 = {0,1,2,3,4,5,6} := by decide +kernel
  simp [h, row0, row1, row2, row3, row4, row5, row6]

theorem class127 (n : ℕ) : interCount n (mask 127) = (n+1)^1 := by
  let Y := Fin 1 → Fin (n+1)
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => ![x 0]
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y 0,y 0,y 0,y 0,y 0,y 0]
  unfold interCount
  refine (card_transport _ (fun _ => True : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_free n 1)
  · intro x hx
    rw [relations127] at hx
    trivial
  · intro y hy
    rw [relations127]
    simp [G] at *
  · intro x hx
    rw [relations127] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G] <;> omega
  · intro y _
    funext i; fin_cases i ; rfl

private theorem relations207 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 207, bad n i x) ↔ ((x 0).val + (x 1).val + (x 2).val = (x 3).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 3).val = (x 2).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 4).val = (x 2).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 5).val = (x 2).val + (x 3).val + (x 4).val) ∧ ((x 0).val + (x 2).val + (x 5).val = (x 1).val + (x 3).val + (x 4).val) ∧ ((x 0).val + (x 3).val + (x 4).val = (x 1).val + (x 2).val + (x 5).val) := by
  have h : mask 207 = {0,1,2,3,6,7} := by decide +kernel
  simp [h, row0, row1, row2, row3, row6, row7]

theorem class207 (n : ℕ) : interCount n (mask 207) = (n+1)^1 := by
  let Y := Fin 1 → Fin (n+1)
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => ![x 0]
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y 0,y 0,y 0,y 0,y 0,y 0]
  unfold interCount
  refine (card_transport _ (fun _ => True : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_free n 1)
  · intro x hx
    rw [relations207] at hx
    trivial
  · intro y hy
    rw [relations207]
    simp [G] at *
  · intro x hx
    rw [relations207] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G] <;> omega
  · intro y _
    funext i; fin_cases i ; rfl

private theorem relations223 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 223, bad n i x) ↔ ((x 0).val + (x 1).val + (x 2).val = (x 3).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 3).val = (x 2).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 4).val = (x 2).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 5).val = (x 2).val + (x 3).val + (x 4).val) ∧ ((x 0).val + (x 2).val + (x 3).val = (x 1).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 5).val = (x 1).val + (x 3).val + (x 4).val) ∧ ((x 0).val + (x 3).val + (x 4).val = (x 1).val + (x 2).val + (x 5).val) := by
  have h : mask 223 = {0,1,2,3,4,6,7} := by decide +kernel
  simp [h, row0, row1, row2, row3, row4, row6, row7]

theorem class223 (n : ℕ) : interCount n (mask 223) = (n+1)^1 := by
  let Y := Fin 1 → Fin (n+1)
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => ![x 0]
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y 0,y 0,y 0,y 0,y 0,y 0]
  unfold interCount
  refine (card_transport _ (fun _ => True : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_free n 1)
  · intro x hx
    rw [relations223] at hx
    trivial
  · intro y hy
    rw [relations223]
    simp [G] at *
  · intro x hx
    rw [relations223] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G] <;> omega
  · intro y _
    funext i; fin_cases i ; rfl

private theorem relations255 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 255, bad n i x) ↔ ((x 0).val + (x 1).val + (x 2).val = (x 3).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 3).val = (x 2).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 4).val = (x 2).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 5).val = (x 2).val + (x 3).val + (x 4).val) ∧ ((x 0).val + (x 2).val + (x 3).val = (x 1).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 4).val = (x 1).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 5).val = (x 1).val + (x 3).val + (x 4).val) ∧ ((x 0).val + (x 3).val + (x 4).val = (x 1).val + (x 2).val + (x 5).val) := by
  have h : mask 255 = {0,1,2,3,4,5,6,7} := by decide +kernel
  simp [h, row0, row1, row2, row3, row4, row5, row6, row7]

theorem class255 (n : ℕ) : interCount n (mask 255) = (n+1)^1 := by
  let Y := Fin 1 → Fin (n+1)
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => ![x 0]
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y 0,y 0,y 0,y 0,y 0,y 0]
  unfold interCount
  refine (card_transport _ (fun _ => True : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_free n 1)
  · intro x hx
    rw [relations255] at hx
    trivial
  · intro y hy
    rw [relations255]
    simp [G] at *
  · intro x hx
    rw [relations255] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G] <;> omega
  · intro y _
    funext i; fin_cases i ; rfl

private theorem relations511 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 511, bad n i x) ↔ ((x 0).val + (x 1).val + (x 2).val = (x 3).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 3).val = (x 2).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 4).val = (x 2).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 5).val = (x 2).val + (x 3).val + (x 4).val) ∧ ((x 0).val + (x 2).val + (x 3).val = (x 1).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 4).val = (x 1).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 5).val = (x 1).val + (x 3).val + (x 4).val) ∧ ((x 0).val + (x 3).val + (x 4).val = (x 1).val + (x 2).val + (x 5).val) ∧ ((x 0).val + (x 3).val + (x 5).val = (x 1).val + (x 2).val + (x 4).val) := by
  have h : mask 511 = {0,1,2,3,4,5,6,7,8} := by decide +kernel
  simp [h, row0, row1, row2, row3, row4, row5, row6, row7, row8]

theorem class511 (n : ℕ) : interCount n (mask 511) = (n+1)^1 := by
  let Y := Fin 1 → Fin (n+1)
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => ![x 0]
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y 0,y 0,y 0,y 0,y 0,y 0]
  unfold interCount
  refine (card_transport _ (fun _ => True : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_free n 1)
  · intro x hx
    rw [relations511] at hx
    trivial
  · intro y hy
    rw [relations511]
    simp [G] at *
  · intro x hx
    rw [relations511] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G] <;> omega
  · intro y _
    funext i; fin_cases i ; rfl

private theorem relations1023 (n : ℕ) (x : Fin 6 → Fin (n+1)) :
    (∀ i ∈ mask 1023, bad n i x) ↔ ((x 0).val + (x 1).val + (x 2).val = (x 3).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 3).val = (x 2).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 4).val = (x 2).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 1).val + (x 5).val = (x 2).val + (x 3).val + (x 4).val) ∧ ((x 0).val + (x 2).val + (x 3).val = (x 1).val + (x 4).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 4).val = (x 1).val + (x 3).val + (x 5).val) ∧ ((x 0).val + (x 2).val + (x 5).val = (x 1).val + (x 3).val + (x 4).val) ∧ ((x 0).val + (x 3).val + (x 4).val = (x 1).val + (x 2).val + (x 5).val) ∧ ((x 0).val + (x 3).val + (x 5).val = (x 1).val + (x 2).val + (x 4).val) ∧ ((x 0).val + (x 4).val + (x 5).val = (x 1).val + (x 2).val + (x 3).val) := by
  have h : mask 1023 = {0,1,2,3,4,5,6,7,8,9} := by decide +kernel
  simp [h, row0, row1, row2, row3, row4, row5, row6, row7, row8, row9]

theorem class1023 (n : ℕ) : interCount n (mask 1023) = (n+1)^1 := by
  let Y := Fin 1 → Fin (n+1)
  let F : (Fin 6 → Fin (n+1)) → Y := fun x => ![x 0]
  let G : Y → (Fin 6 → Fin (n+1)) := fun y => ![y 0,y 0,y 0,y 0,y 0,y 0]
  unfold interCount
  refine (card_transport _ (fun _ => True : Y → Prop) F G ?_ ?_ ?_ ?_).trans (card_free n 1)
  · intro x hx
    rw [relations1023] at hx
    trivial
  · intro y hy
    rw [relations1023]
    simp [G] at *
  · intro x hx
    rw [relations1023] at hx
    funext i
    apply Fin.ext
    fin_cases i <;> simp [F, G] <;> omega
  · intro y _
    funext i; fin_cases i ; rfl

end A247996Classes

namespace A247996Generating

open PowerSeries OMA.S_oeis_a247996

def closed (n : ℕ) : ℚ :=
  (2 * n ^ 6 + n ^ 5 + 35 * n ^ 4 - 5 * n ^ 3 + 10 * n ^ 2 + 36 * n) / 2 -
    if n % 2 = 0 then 0 else 15 / 2

private theorem coefficient_step (m : ℕ) :
    closed (m+8) - 6*closed (m+7) + 14*closed (m+6) - 14*closed (m+5) +
      14*closed (m+3) - 14*closed (m+2) + 6*closed (m+1) - closed m = 0 := by
  have h8 : (m+8)%2=0 ↔ m%2=0 := by omega
  have h7 : (m+7)%2=0 ↔ ¬m%2=0 := by omega
  have h6 : (m+6)%2=0 ↔ m%2=0 := by omega
  have h5 : (m+5)%2=0 ↔ ¬m%2=0 := by omega
  have h3 : (m+3)%2=0 ↔ ¬m%2=0 := by omega
  have h2 : (m+2)%2=0 ↔ m%2=0 := by omega
  have h1 : (m+1)%2=0 ↔ ¬m%2=0 := by omega
  simp only [closed,h8,h7,h6,h5,h3,h2,h1,Nat.cast_add,Nat.cast_ofNat]
  by_cases hm : m%2=0 <;> simp only [hm,not_true_eq_false,not_false_eq_true,if_false,if_true] <;> ring

private theorem denominator :
    (1-X : ℚ⟦X⟧)^7 * (1+X) =
      1 - C (6:ℚ) * X^1 + C (14:ℚ) * X^2 - C (14:ℚ) * X^3 +
        C (14:ℚ) * X^5 - C (14:ℚ) * X^6 + C (6:ℚ) * X^7 - X^8 := by
  simp only [map_ofNat]
  ring

private theorem numerator :
    (4*X*(8+51*X+91*X^2+106*X^3+21*X^4+83*X^5) : ℚ⟦X⟧) =
      C (32:ℚ) * X^1 + C (204:ℚ) * X^2 + C (364:ℚ) * X^3 +
        C (424:ℚ) * X^4 + C (84:ℚ) * X^5 + C (332:ℚ) * X^6 := by
  simp only [map_ofNat]
  ring

private theorem coeff_mul_scaled_shift (s : ℚ⟦X⟧) (c : ℚ) (k n : ℕ) :
    coeff n (s * (C c * X^k)) = c * (if k ≤ n then coeff (n-k) s else 0) := by
  rw [← mul_assoc, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mul_C,mul_comm]

theorem closed_series :
    mk closed * ((1-X)^7*(1+X)) =
      4*X*(8+51*X+91*X^2+106*X^3+21*X^4+83*X^5) := by
  rw [denominator,numerator]
  apply PowerSeries.ext
  intro n
  simp only [mul_add,mul_sub,mul_one,map_add,map_sub,coeff_mul_scaled_shift,
    coeff_mk,coeff_mul_X_pow']
  rcases lt_or_ge n 8 with hn | hn
  · interval_cases n <;> norm_num [closed]
  · obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
    have ge1 : 1 ≤ 8+m := by omega
    have ge2 : 2 ≤ 8+m := by omega
    have ge3 : 3 ≤ 8+m := by omega
    have ge5 : 5 ≤ 8+m := by omega
    have ge6 : 6 ≤ 8+m := by omega
    have ge7 : 7 ≤ 8+m := by omega
    have ge8 : 8 ≤ 8+m := by omega
    have nz1 : 8+m ≠ 1 := by omega
    have nz2 : 8+m ≠ 2 := by omega
    have nz3 : 8+m ≠ 3 := by omega
    have nz4 : 8+m ≠ 4 := by omega
    have nz5 : 8+m ≠ 5 := by omega
    have nz6 : 8+m ≠ 6 := by omega
    rw [show 8+m-1=m+7 by omega,show 8+m-2=m+6 by omega,show 8+m-3=m+5 by omega,
      show 8+m-5=m+3 by omega,show 8+m-6=m+2 by omega,show 8+m-7=m+1 by omega,
      show 8+m-8=m by omega]
    simpa [ge1,ge2,ge3,ge5,ge6,ge7,ge8,nz1,nz2,nz3,nz4,nz5,nz6,Nat.add_comm 8 m] using
      coefficient_step m

/-- The parity polynomial determines the requested generating function. -/
theorem series_of_closed (h : ∀ n : ℕ, (a n : ℚ) = closed n) :
    mk (fun n => if n = 0 then 0 else (a n : ℚ)) * ((1-X)^7*(1+X)) =
      4*X*(8+51*X+91*X^2+106*X^3+21*X^4+83*X^5) := by
  have he : (fun n => if n = 0 then 0 else (a n : ℚ)) = closed := by
    funext n
    by_cases hn : n=0
    · subst n
      norm_num [closed]
    · simp [hn,h]
  rw [he]
  exact closed_series

end A247996Generating

namespace A247996Generating

open OMA.S_oeis_a247996

/-- Express the grouped intersections in terms of rational closed forms. -/
theorem grouped_polynomial (n : ℕ) :
    let q : ℚ := (n : ℚ) + 1
    let e₂ := (2*q^3+q)/3
    let e₃ := (11*q^5+5*q^3+4*q)/20
    let b := (q^2 + if n % 2 = 0 then 1 else 0)/2
    q^6 - 10*e₃ + (45*q-60)*e₂ - 45*q^3 + 105*q^2 - 51*q + 15*b = closed n := by
  dsimp only
  unfold closed
  by_cases h : n%2 = 0 <;> simp only [h,if_true,if_false] <;> ring

/-- The two parity formulas follow from the single normalized expression. -/
theorem even_formula (h : ∀ n : ℕ, (a n : ℚ) = closed n) (n : ℕ) (hn : Even n) :
    (a n : ℚ) = (2 * n ^ 6 + n ^ 5 + 35 * n ^ 4 - 5 * n ^ 3 + 10 * n ^ 2 + 36 * n) / 2 := by
  rw [h]
  simp [closed, Nat.even_iff.mp hn]

theorem odd_formula (h : ∀ n : ℕ, (a n : ℚ) = closed n) (n : ℕ) (hn : Odd n) :
    (a n : ℚ) = (2 * n ^ 6 + n ^ 5 + 35 * n ^ 4 - 5 * n ^ 3 + 10 * n ^ 2 + 36 * n - 15) / 2 := by
  rw [h]
  have ho : n%2 ≠ 0 := by have := Nat.odd_iff.mp hn; omega
  simp only [closed,if_neg ho]
  ring

end A247996Generating

namespace A247996Aggregate

open Finset A247996IE A247996Base OMA.S_oeis_a247996

def weight (m : Fin 1024) : ℤ := (-1 : ℤ)^(mask m).card

def coefficient : Fin 19 → ℤ :=
  ![1,-10,45,-60,15,-60,180,-90,15,-90,-72,180,15,-60,15,-60,45,-10,1]

def modelCount (n : ℕ) : Fin 19 → ℕ :=
  let q := n+1
  ![q^6,equalCount 3 n,q*equalCount 2 n,equalCount 2 n,midCount n,q^3,q^2,q,q^3,q^2,q,q,q^2,q,q,q,q,q,q]

/-- Group the signed inclusion-exclusion terms by the finite orbit index. -/
theorem grouped (n : ℕ) (tag : Fin 1024 → Fin 19) (sign : Fin 19 → ℤ)
    (pop : Fin 19 → ℕ)
    (hterm : ∀ m, weight m * (interCount n (mask m) : ℤ) =
      sign (tag m) * (modelCount n (tag m) : ℤ))
    (hpop : ∀ i, (univ.filter (fun m => tag m = i)).card = pop i)
    (hcoef : ∀ i, (pop i : ℤ) * sign i = coefficient i) :
    (a n : ℤ) = (n+1)^6 - 10*(equalCount 3 n : ℤ) +
      (45*(n+1)-60)*(equalCount 2 n : ℤ) -
      45*(n+1)^3 + 105*(n+1)^2 - 51*(n+1) + 15*(midCount n : ℤ) := by
  classical
  rw [a_eq_mask_sum]
  change (∑ m : Fin 1024, weight m * (interCount n (mask m) : ℤ)) = _
  simp only [hterm]
  let f (m : Fin 1024) := sign (tag m) * (modelCount n (tag m) : ℤ)
  have hf := Finset.sum_fiberwise_eq_sum_filter
    (univ : Finset (Fin 1024)) (univ : Finset (Fin 19)) tag f
  have expand (i : Fin 19) :
      (∑ m : Fin 1024 with tag m = i, f m) = coefficient i * (modelCount n i : ℤ) := by
    calc
      _ = ∑ _m : Fin 1024 with tag _m = i, sign i * (modelCount n i : ℤ) := by
        apply sum_congr rfl
        intro m hm
        simp only [f,(mem_filter.mp hm).2]
      _ = _ := by rw [sum_const,hpop,nsmul_eq_mul,←mul_assoc,hcoef]
  simp only [filter_true_of_mem (fun _ _ => mem_univ _),expand] at hf
  change ∑ m, f m = _
  rw [←hf]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,coefficient,modelCount,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_one]
  ring

end A247996Aggregate

namespace A247996Aggregate

open A247996IE A247996Orbit A247996Classes

theorem coefficient_rep : ∀ i : Fin 19, (pop i : ℤ) * weight (rep i) = coefficient i := by
  decide +kernel

theorem model_rep (n : ℕ) (i : Fin 19) :
    interCount n (mask (rep i)) = modelCount n i := by
  fin_cases i
  · exact class0 n
  · have h := class1 n
    rw [pow_zero,one_mul] at h
    exact h
  · have h := class3 n
    rw [pow_one] at h
    exact h
  · have h := class7 n
    rw [pow_zero,one_mul] at h
    exact h
  · exact class15 n
  · exact class21 n
  · exact class23 n
  · have h := class31 n
    rw [pow_one] at h
    exact h
  · exact class54 n
  · exact class55 n
  · have h := class59 n
    rw [pow_one] at h
    exact h
  · have h := class63 n
    rw [pow_one] at h
    exact h
  · exact class126 n
  · have h := class127 n
    rw [pow_one] at h
    exact h
  · have h := class207 n
    rw [pow_one] at h
    exact h
  · have h := class223 n
    rw [pow_one] at h
    exact h
  · have h := class255 n
    rw [pow_one] at h
    exact h
  · have h := class511 n
    rw [pow_one] at h
    exact h
  · have h := class1023 n
    rw [pow_one] at h
    exact h

end A247996Aggregate

namespace A247996Generating

open A247996Base OMA.S_oeis_a247996

/-- The signed sum of the intersections implies the parity formulas and the generating function. -/
theorem of_grouped
    (h : ∀ n : ℕ, (a n : ℤ) = (n+1)^6 - 10*(equalCount 3 n : ℤ) +
      (45*(n+1)-60)*(equalCount 2 n : ℤ) -
      45*(n+1)^3 + 105*(n+1)^2 - 51*(n+1) + 15*(midCount n : ℤ)) :
    type_of% @OMA.S_oeis_a247996.main := by
  have hs (n : ℕ) : (a n : ℚ) = closed n := by
    have hq : (a n : ℚ) = (n+1)^6 - 10*(equalCount 3 n : ℚ) +
        (45*(n+1)-60)*(equalCount 2 n : ℚ) -
        45*(n+1)^3 + 105*(n+1)^2 - 51*(n+1) + 15*(midCount n : ℚ) := by
      exact_mod_cast h n
    rw [equal2,equal3,A247996Base.midpoint] at hq
    exact hq.trans (grouped_polynomial n)
  exact ⟨series_of_closed hs, fun n _ hn => even_formula hs n hn, fun n hn => odd_formula hs n hn⟩

end A247996Generating

theorem OMA.solution : type_of% @OMA.S_oeis_a247996.main := by
  apply A247996Generating.of_grouped
  intro n
  refine A247996Aggregate.grouped n A247996Orbit.tag
    (fun i => A247996Aggregate.weight (A247996Orbit.rep i))
    A247996Orbit.pop ?_ A247996Orbit.population A247996Aggregate.coefficient_rep
  intro m
  simpa only [A247996Aggregate.weight, A247996Aggregate.model_rep n (A247996Orbit.tag m)] using
    A247996Orbit.signed_orbit n m
