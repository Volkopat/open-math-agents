import OMAStatements.S_oeis_a001784
import Mathlib

/-!
# The fixed-excess associated Stirling recurrences

Credit: @VestigeClub.
Source: https://oeis.org/A001784. The recurrences are due to R. J. Mathar;
the closed factorial formula is due to Václav Kotešovec.

A fixed-point-free permutation on 2n+1 letters with n-1 cycles has excess
three above transpositions. Its non-transposition cycles must be one
5-cycle, one 4-cycle and one 3-cycle, or three 3-cycles. We prove this
classification and count the three disjoint cycle types using the standard
cycle-type cardinality theorem. The resulting factorial formula implies
the first-order recurrence; three adjacent instances give the other one.
-/


namespace AssociatedStirling

theorem lower_sum (m : Multiset ℕ) (d : ℕ) (h : ∀ x ∈ m, d ≤ x) :
    d*m.card ≤ m.sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [Multiset.card_cons, Multiset.sum_cons, Nat.mul_add, Nat.mul_one]
    omega

theorem add_single (s : Multiset ℕ) (a : ℕ) : s + {a} = a ::ₘ s := by
  rw [Multiset.add_comm, Multiset.singleton_add]

theorem excess_three (m : Multiset ℕ) (hmin : ∀ x ∈ m, 2 ≤ x)
    (hsum : m.sum = 2*m.card+3) :
    m = 5 ::ₘ Multiset.replicate (m.card-1) 2 ∨
    m = 4 ::ₘ 3 ::ₘ Multiset.replicate (m.card-2) 2 ∨
    m = 3 ::ₘ 3 ::ₘ 3 ::ₘ Multiset.replicate (m.card-3) 2 := by
  classical
  let r := m.filter (fun x => x ≠ 2)
  have hd : m = Multiset.replicate (m.count 2) 2 + r := by
    simpa only [Multiset.filter_eq', r] using
      (Multiset.filter_add_not (p := fun x => x=2) m).symm
  have hr : ∀ x ∈ r, 3 ≤ x := by
    intro x hx
    obtain ⟨hm,hne⟩ := Multiset.mem_filter.mp hx
    have := hmin x hm
    omega
  have hs : r.sum = 2*r.card+3 := by
    have hsc := congrArg Multiset.sum hd
    have hcc := congrArg Multiset.card hd
    simp at hsc hcc
    omega
  have hc : r.card ≤ 3 := by
    have := lower_sum r 3 hr
    omega
  have hc' : r.card=0 ∨ r.card=1 ∨ r.card=2 ∨ r.card=3 := by omega
  rcases hc' with hc | hc | hc | hc
  · have hz := Multiset.card_eq_zero.mp hc
    simp [hz] at hs
  · obtain ⟨x,hx⟩ := Multiset.card_eq_one.mp hc
    have he : x=5 := by simpa [hx] using hs
    subst x
    left
    have hmc : m.card = m.count 2+1 := by
      have hh := congrArg Multiset.card hd
      simpa [hx] using hh
    rw [show m.card-1=m.count 2 by omega]
    simpa [hx, add_single, Multiset.add_cons, Multiset.add_zero] using hd
  · obtain ⟨x,y,hxy⟩ := Multiset.card_eq_two.mp hc
    have hx : 3 ≤ x := hr x (by simp [hxy])
    have hy : 3 ≤ y := hr y (by simp [hxy])
    have he : x+y=7 := by simpa [hxy] using hs
    have hcases : (x=4 ∧ y=3) ∨ (x=3 ∧ y=4) := by omega
    right; left
    have hmc : m.card = m.count 2+2 := by
      have hh := congrArg Multiset.card hd
      simpa [hxy, add_assoc] using hh
    rw [show m.card-2=m.count 2 by omega]
    rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simpa [hxy, add_single, Multiset.add_cons, Multiset.add_zero, Multiset.cons_swap] using hd
  · obtain ⟨x,y,z,hxyz⟩ := Multiset.card_eq_three.mp hc
    have hx : 3 ≤ x := hr x (by simp [hxyz])
    have hy : 3 ≤ y := hr y (by simp [hxyz])
    have hz : 3 ≤ z := hr z (by simp [hxyz])
    have he : x+y+z=9 := by simpa [hxyz, add_assoc] using hs
    have hx3 : x=3 := by omega
    have hy3 : y=3 := by omega
    have hz3 : z=3 := by omega
    subst x; subst y; subst z
    right; right
    have hmc : m.card = m.count 2+3 := by
      have hh := congrArg Multiset.card hd
      simpa [hxyz, add_assoc] using hh
    rw [show m.card-3=m.count 2 by omega]
    simpa [hxyz, add_single, Multiset.add_cons, Multiset.add_zero] using hd

end AssociatedStirling

namespace AssociatedStirling
open Equiv

def five (k : ℕ) : Multiset ℕ := 5 ::ₘ Multiset.replicate k 2
def fourThree (k : ℕ) : Multiset ℕ := 4 ::ₘ 3 ::ₘ Multiset.replicate k 2
def threeThreeThree (k : ℕ) : Multiset ℕ := 3 ::ₘ 3 ::ₘ 3 ::ₘ Multiset.replicate k 2

def typeCount (N : ℕ) (m : Multiset ℕ) : ℕ :=
  (Finset.univ.filter fun s : Equiv.Perm (Fin N) => s.cycleType=m).card

def weight (m : Multiset ℕ) : ℕ := m.prod * ∏ i ∈ m.toFinset, (m.count i).factorial

theorem weight_five (k : ℕ) : weight (five k) = 5*2^k*k.factorial := by
  classical
  by_cases hk : k=0
  · subst k; norm_num [weight, five]
  · simp [weight, five, hk, Multiset.count_replicate] <;> ring_nf <;> simp

theorem weight_fourThree (k : ℕ) : weight (fourThree k) = 12*2^k*k.factorial := by
  classical
  by_cases hk : k=0
  · subst k; norm_num [weight, fourThree]
  · simp [weight, fourThree, hk, Multiset.count_replicate] <;> ring_nf <;> simp

theorem weight_threeThreeThree (k : ℕ) : weight (threeThreeThree k) = 162*2^k*k.factorial := by
  classical
  by_cases hk : k=0
  · subst k; norm_num [weight, threeThreeThree]
  · simp [weight, threeThreeThree, hk, Multiset.count_replicate] <;> ring_nf <;> simp

theorem typeCount_mul (N : ℕ) (m : Multiset ℕ) (hs : m.sum=N) (hm : ∀ x ∈ m, 2≤x) :
    typeCount N m * weight m = N.factorial := by
  have h := Equiv.Perm.card_of_cycleType_mul_eq (Fin N) m
  simp only [Fintype.card_fin] at h
  rw [if_pos (show m.sum ≤ N ∧ ∀ a ∈ m, 2 ≤ a from ⟨by omega, hm⟩)] at h
  simpa [typeCount, weight, hs] using h

theorem nofixed_iff_sum (N : ℕ) (s : Equiv.Perm (Fin N)) :
    (∀ x, s x ≠ x) ↔ s.cycleType.sum=N := by
  constructor
  · intro h
    rw [Equiv.Perm.sum_cycleType]
    have he : s.support = Finset.univ := by ext x; simp [h]
    simp [he]
  · intro h
    have he : s.support = Finset.univ := Finset.eq_univ_of_card s.support (by simpa [← s.sum_cycleType] using h)
    intro x
    have hx : x ∈ s.support := by simp [he]
    simpa using hx

theorem perm_types (n : ℕ) (hn : 2≤n) (s : Equiv.Perm (Fin (2*n+1)))
    (hf : ∀ x, s x ≠ x) (hc : s.cycleType.card=n-1) :
    s.cycleType = five (n-2) ∨ s.cycleType = fourThree (n-3) ∨
      s.cycleType = threeThreeThree (n-4) := by
  have hs := (nofixed_iff_sum _ s).mp hf
  have he : s.cycleType.sum = 2*s.cycleType.card+3 := by omega
  have hh := excess_three s.cycleType (fun x hx => Equiv.Perm.two_le_of_mem_cycleType hx) he
  simpa only [hc, five, fourThree, threeThreeThree, Nat.sub_sub, show 1+1=2 from rfl,
    show 1+2=3 from rfl, show 1+3=4 from rfl] using hh

end AssociatedStirling

namespace AssociatedStirling
open OMA.S_oeis_a001784

 theorem types_distinct (i j k : ℕ) :
    five i ≠ fourThree j ∧ five i ≠ threeThreeThree k ∧ fourThree j ≠ threeThreeThree k := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hh := congrArg (Multiset.count 5) h
    simp [five, fourThree, Multiset.count_replicate] at hh
  · intro h
    have hh := congrArg (Multiset.count 5) h
    simp [five, threeThreeThree, Multiset.count_replicate] at hh
  · intro h
    have hh := congrArg (Multiset.count 4) h
    simp [fourThree, threeThreeThree, Multiset.count_replicate] at hh

 theorem perm_types_iff (n : ℕ) (hn : 2≤n) (s : Equiv.Perm (Fin (2*n+1))) :
    ((∀ x, s x ≠ x) ∧ s.cycleType.card=n-1) ↔
    s.cycleType = five (n-2) ∨ s.cycleType = fourThree (n-3) ∨
      s.cycleType = threeThreeThree (n-4) := by
  constructor
  · rintro ⟨hf,hc⟩
    exact perm_types n (by omega) s hf hc
  · intro h
    have hs : s.cycleType.sum=2*n+1 ∧ s.cycleType.card=n-1 := by
      have hl := s.sum_cycleType_le
      simp only [Fintype.card_fin] at hl
      rcases h with h | h | h <;> rw [h] at hl ⊢ <;>
        simp [five, fourThree, threeThreeThree] at hl ⊢ <;> omega
    exact ⟨(nofixed_iff_sum _ s).mpr hs.1, hs.2⟩

 theorem assocStirling_sum (n : ℕ) (hn : 2≤n) :
    assocStirling (2*n+1) (n-1) = typeCount (2*n+1) (five (n-2)) +
      typeCount (2*n+1) (fourThree (n-3)) + typeCount (2*n+1) (threeThreeThree (n-4)) := by
  classical
  let s0 := Finset.univ.filter (fun s : Equiv.Perm (Fin (2*n+1)) => s.cycleType=five (n-2))
  let s1 := Finset.univ.filter (fun s : Equiv.Perm (Fin (2*n+1)) => s.cycleType=fourThree (n-3))
  let s2 := Finset.univ.filter (fun s : Equiv.Perm (Fin (2*n+1)) => s.cycleType=threeThreeThree (n-4))
  have hd := types_distinct (n-2) (n-3) (n-4)
  have d01 : Disjoint s0 s1 := by
    apply Finset.disjoint_left.mpr
    intro s h0 h1
    exact hd.1 ((Finset.mem_filter.mp h0).2.symm.trans (Finset.mem_filter.mp h1).2)
  have d02 : Disjoint s0 s2 := by
    apply Finset.disjoint_left.mpr
    intro s h0 h2
    exact hd.2.1 ((Finset.mem_filter.mp h0).2.symm.trans (Finset.mem_filter.mp h2).2)
  have d12 : Disjoint s1 s2 := by
    apply Finset.disjoint_left.mpr
    intro s h1 h2
    exact hd.2.2 ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have heq : (Finset.univ.filter (fun s : Equiv.Perm (Fin (2*n+1)) =>
      (∀ x, s x ≠ x) ∧ s.cycleType.card=n-1)) = (s0 ∪ s1) ∪ s2 := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, s0,s1,s2]
    rw [perm_types_iff n hn s]
    tauto
  rw [assocStirling, Nat.card_eq_fintype_card, Fintype.card_subtype, heq,
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d02,d12⟩),
    Finset.card_union_of_disjoint d01]
  rfl

end AssociatedStirling

namespace AssociatedStirling
open OMA.S_oeis_a001784

theorem a_two : a 2 = 24 := by
  rw [a, if_neg (by decide), assocStirling_sum 2 (by decide)]
  norm_num [typeCount, Equiv.Perm.card_of_cycleType, five, fourThree, threeThreeThree]

theorem a_three : a 3 = 924 := by
  rw [a, if_neg (by decide), assocStirling_sum 3 (by decide)]
  norm_num [typeCount, Equiv.Perm.card_of_cycleType, five, fourThree, threeThreeThree]

theorem formula_shift (k : ℕ) :
    (a (k+4) : ℚ) * (810*2^(k+2)*((k+2).factorial : ℚ)) =
      ((2*(k+4)+1).factorial : ℚ)*(20*(k+4 : ℚ)^2+35*(k+4)+12) := by
  let N := 2*(k+4)+1
  have h5 := typeCount_mul N (five (k+2)) (by simp [N,five]; omega)
    (by intro x hx; simp [five, Multiset.mem_replicate] at hx; omega)
  have h43 := typeCount_mul N (fourThree (k+1)) (by simp [N,fourThree]; omega)
    (by intro x hx; simp [fourThree, Multiset.mem_replicate] at hx; omega)
  have h333 := typeCount_mul N (threeThreeThree k) (by simp [N,threeThreeThree]; omega)
    (by intro x hx; simp [threeThreeThree, Multiset.mem_replicate] at hx; omega)
  rw [weight_five] at h5
  rw [weight_fourThree] at h43
  rw [weight_threeThreeThree] at h333
  have e5 : (typeCount N (five (k+2)) : ℚ) * (5*2^(k+2)*((k+2).factorial : ℚ)) = (N.factorial : ℚ) := by exact_mod_cast h5
  have e43 : (typeCount N (fourThree (k+1)) : ℚ) * (12*2^(k+1)*((k+1).factorial : ℚ)) = (N.factorial : ℚ) := by exact_mod_cast h43
  have e333 : (typeCount N (threeThreeThree k) : ℚ) * (162*2^k*(k.factorial : ℚ)) = (N.factorial : ℚ) := by exact_mod_cast h333
  have ha : (a (k+4) : ℚ) = (typeCount N (five (k+2)) : ℚ) +
      typeCount N (fourThree (k+1)) + typeCount N (threeThreeThree k) := by
    rw [a, if_neg (by omega), assocStirling_sum (k+4) (by omega)]
    simp only [show k+4-2=k+2 by omega, show k+4-3=k+1 by omega, show k+4-4=k by omega]
    push_cast
    rfl
  rw [ha]
  have f1 : ((k+1).factorial : ℚ) = (k+1)*(k.factorial : ℚ) := by simp [Nat.factorial_succ]
  have f2 : ((k+2).factorial : ℚ) = (k+2)*(k+1)*(k.factorial : ℚ) := by simp [Nat.factorial_succ]; ring
  rw [f2] at e5 ⊢
  rw [f1] at e43
  simp only [pow_succ] at e5 e43 ⊢
  dsimp [N] at e5 e43 e333
  push_cast
  linear_combination 162*e5 + (135*(k+2 : ℚ))*e43 + (20*(k+2 : ℚ)*(k+1))*e333

theorem formula (n : ℕ) (hn : 2≤n) :
    (a n : ℚ) * (810*2^(n-2)*((n-2).factorial : ℚ)) =
      ((2*n+1).factorial : ℚ)*(20*(n : ℚ)^2+35*n+12) := by
  by_cases h2 : n=2
  · subst n; norm_num [a_two]
  by_cases h3 : n=3
  · subst n; norm_num [a_three]
  have hh := formula_shift (n-4)
  have he : n-4+4=n := by omega
  rw [he] at hh
  have hcq : ((n-4 : ℕ) : ℚ)+4 = (n : ℚ) := by
    rw [Nat.cast_sub (by omega : 4 ≤ n)]
    norm_num
  rw [hcq] at hh
  simpa only [show n-4+2=n-2 by omega] using hh

end AssociatedStirling

namespace AssociatedStirling
open OMA.S_oeis_a001784

def P (x : ℚ) : ℚ := 20*x^2+35*x+12

theorem second_shift (k : ℕ) :
    ((k:ℚ)+1)*P (k+2)*(a (k+3):ℚ) -
      ((k:ℚ)+3)*(2*((k:ℚ)+3)+1)*P (k+3)*(a (k+2):ℚ) = 0 := by
  have h0 := formula (k+3) (by omega)
  have h1 := formula (k+2) (by omega)
  rw [show k+3-2=k+1 by omega] at h0
  rw [show k+2-2=k by omega] at h1
  have hf : ((2*(k+3)+1).factorial : ℚ) =
      (2*((k:ℚ)+3)+1)*(2*((k:ℚ)+3))*((2*(k+2)+1).factorial : ℚ) := by
    rw [show 2*(k+3)+1=(2*(k+2)+1)+2 by omega]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  rw [hf, Nat.factorial_succ] at h0
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_mul, pow_succ] at h0 h1
  apply mul_left_cancel₀ (show (2*(810*2^k*(k.factorial:ℚ))) ≠ 0 by positivity)
  rw [mul_zero]
  dsimp [P]
  linear_combination (20*((k:ℚ)+2)^2+35*(k+2)+12)*h0 -
    2*((k:ℚ)+3)*(2*((k:ℚ)+3)+1)*(20*((k:ℚ)+3)^2+35*(k+3)+12)*h1

theorem second_Q (n : ℕ) (hn : 3≤n) :
    ((n:ℚ)-2)*(20*(n:ℚ)^2-5*n-3)*(a n:ℚ) -
      (n:ℚ)*(2*(n:ℚ)+1)*(20*(n:ℚ)^2+35*n+12)*(a (n-1):ℚ) = 0 := by
  have h := second_shift (n-3)
  have he : n-3+3=n := by omega
  have he' : n-3+2=n-1 := by omega
  rw [he, he'] at h
  rw [Nat.cast_sub hn] at h
  norm_num only [Nat.cast_ofNat] at h
  dsimp [P] at h
  linear_combination h

end AssociatedStirling

namespace AssociatedStirling
open OMA.S_oeis_a001784

def Acoeff (x : ℚ) : ℚ := (x-2)*(20*x^2-5*x-3)
def Bcoeff (x : ℚ) : ℚ := x*(2*x+1)*(20*x^2+35*x+12)

theorem Acoeff_pos (x : ℚ) (hx : 3≤x) : 0<Acoeff x := by
  unfold Acoeff
  apply mul_pos
  · linarith
  · nlinarith [sq_nonneg (x-3)]

set_option maxHeartbeats 1000000 in
theorem ratio_combination (x u v w z : ℚ) (hx : 5≤x)
    (h0 : Acoeff x*u-Bcoeff x*v=0)
    (h1 : Acoeff (x-1)*v-Bcoeff (x-1)*w=0)
    (h2 : Acoeff (x-2)*w-Bcoeff (x-2)*z=0) :
    480*(x+1)*u+30*(-32*x^2-14821*x+42287)*v+
      (878700*x^2-403433*x+5134227)*w+(911423*x-656446)*(2*x-3)*z=0 := by
  have hA0 := Acoeff_pos x (by linarith)
  have hA1 := Acoeff_pos (x-1) (by linarith)
  have hA2 := Acoeff_pos (x-2) (by linarith)
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (ne_of_gt hA0) (ne_of_gt hA1)) (ne_of_gt hA2))
  rw [mul_zero]
  let c0 := 480*(x+1)
  let c1 := 30*(-32*x^2-14821*x+42287)
  let c2 := 878700*x^2-403433*x+5134227
  let u0 := c0*(((x-1)-2)*(20*(x-1)^2-5*(x-1)-3))*(((x-2)-2)*(20*(x-2)^2-5*(x-2)-3))
  let u1 := (c1*((x-2)*(20*x^2-5*x-3))+c0*(x*(2*x+1)*(20*x^2+35*x+12)))*(((x-2)-2)*(20*(x-2)^2-5*(x-2)-3))
  let u2 := c2*((x-2)*(20*x^2-5*x-3))*(((x-1)-2)*(20*(x-1)^2-5*(x-1)-3))+(c1*((x-2)*(20*x^2-5*x-3))+c0*(x*(2*x+1)*(20*x^2+35*x+12)))*((x-1)*(2*(x-1)+1)*(20*(x-1)^2+35*(x-1)+12))
  dsimp [Acoeff, Bcoeff] at h0 h1 h2 ⊢
  linear_combination u0*h0+u1*h1+u2*h2

 theorem first_Q (n : ℕ) (hn : 4≤n) :
    480*((n:ℚ)+1)*(a n:ℚ)+30*(-32*(n:ℚ)^2-14821*n+42287)*(a (n-1):ℚ)+
      (878700*(n:ℚ)^2-403433*n+5134227)*(a (n-2):ℚ)+
      (911423*(n:ℚ)-656446)*(2*(n:ℚ)-3)*(a (n-3):ℚ)=0 := by
  by_cases h4 : n=4
  · subst n
    have hf := formula 4 (by omega)
    norm_num at hf
    have ha4 : (a 4 : ℚ)=26432 := by linarith
    norm_num [ha4, a_three, a_two, show a 1=0 by rfl]
  have hn5 : 5≤n := by omega
  have h0 := second_Q n (by omega)
  have h1 := second_Q (n-1) (by omega)
  have h2 := second_Q (n-2) (by omega)
  rw [show n-1-1=n-2 by omega, Nat.cast_sub (by omega : 1≤n)] at h1
  rw [show n-2-1=n-3 by omega, Nat.cast_sub (by omega : 2≤n)] at h2
  norm_num only [Nat.cast_one, Nat.cast_ofNat] at h1 h2
  apply ratio_combination (n:ℚ) (a n:ℚ) (a (n-1):ℚ) (a (n-2):ℚ) (a (n-3):ℚ) (by exact_mod_cast hn5)
  · exact h0
  · exact h1
  · exact h2

end AssociatedStirling

theorem OMA.solution : type_of% @OMA.S_oeis_a001784.main := by
  constructor
  · intro n hn
    exact_mod_cast AssociatedStirling.first_Q n hn
  · intro n hn
    exact_mod_cast AssociatedStirling.second_Q n hn
