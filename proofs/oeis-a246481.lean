import OMAStatements.S_oeis_a246481
import Mathlib

/-! Colin Barker's conjectures for OEIS A246481. Fix the three middle
entries of the array. Each endpoint independently avoids their complements.
The number of distinct middle entries sets the weight of each admissible
triple. Counting equal-coordinate pairs and all-equal triples gives both
parity polynomials, then the ordinary generating function. -/

open Finset OMA.S_oeis_a246481

private lemma array_good_iff {n : ℕ} (l x y z r : Fin (n+1)) :
    good ![l,x,y,z,r] = true ↔
    (x.val + y.val ≠ n ∧ x.val + z.val ≠ n ∧ y.val + z.val ≠ n) ∧
    (l.val + x.val ≠ n ∧ l.val + y.val ≠ n ∧ l.val + z.val ≠ n) ∧
    (r.val + x.val ≠ n ∧ r.val + y.val ≠ n ∧ r.val + z.val ≠ n) := by
  simp only [good, decide_eq_true_eq]
  constructor
  · intro H
    have A := H 0 (by decide) 0 (by decide) 1 (by decide) (by decide)
    have B := H 0 (by decide) 0 (by decide) 2 (by decide) (by decide)
    have C := H 0 (by decide) 0 (by decide) 3 (by decide) (by decide)
    have D := H 0 (by decide) 1 (by decide) 2 (by decide) (by decide)
    have E := H 0 (by decide) 1 (by decide) 3 (by decide) (by decide)
    have F := H 0 (by decide) 2 (by decide) 3 (by decide) (by decide)
    have G := H 1 (by decide) 0 (by decide) 3 (by decide) (by decide)
    have I := H 1 (by decide) 1 (by decide) 3 (by decide) (by decide)
    have J := H 1 (by decide) 2 (by decide) 3 (by decide) (by decide)
    change l.val + x.val ≠ n at A
    change l.val + y.val ≠ n at B
    change l.val + z.val ≠ n at C
    change x.val + y.val ≠ n at D
    change x.val + z.val ≠ n at E
    change y.val + z.val ≠ n at F
    change x.val + r.val ≠ n at G
    change y.val + r.val ≠ n at I
    change z.val + r.val ≠ n at J
    exact ⟨⟨D,E,F⟩, ⟨A,B,C⟩, by simpa only [Nat.add_comm r.val] using And.intro G (And.intro I J)⟩
  · rintro ⟨⟨D,E,F⟩, ⟨A,B,C⟩, ⟨G,I,J⟩⟩ i hi s hs t ht hst
    rw [Nat.add_comm r.val x.val] at G
    rw [Nat.add_comm r.val y.val] at I
    rw [Nat.add_comm r.val z.val] at J
    interval_cases i <;> interval_cases s <;> interval_cases t <;>
      assumption


private lemma array_allowed_count {n : ℕ} (x y z : Fin (n+1)) :
    (∑ l : Fin (n+1), if l.val + x.val ≠ n ∧ l.val + y.val ≠ n ∧ l.val + z.val ≠ n
      then 1 else 0) = n+1-({x,y,z} : Finset (Fin (n+1))).card := by
  classical
  let S : Finset (Fin (n+1)) := {x,y,z}
  have h (u v : Fin (n+1)) : u.val + v.val ≠ n ↔ u.rev ≠ v := by
    rw [Ne, Ne, Fin.ext_iff]
    rw [Fin.val_rev]
    have := u.isLt
    omega
  simp_rw [h]
  calc
    _ = ∑ u : Fin (n+1), if u.rev ∈ Sᶜ then 1 else 0 := by
      apply sum_congr rfl
      intro u _
      simp [S]
    _ = ∑ u : Fin (n+1), if u ∈ Sᶜ then 1 else 0 :=
      Equiv.sum_comp Fin.revPerm (fun u => if u ∈ Sᶜ then 1 else 0)
    _ = _ := by rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_compl, Fintype.card_fin]

private theorem array_endpoints (n : ℕ) :
    a n = ↑(∑ x : Fin (n+1), ∑ y : Fin (n+1), ∑ z : Fin (n+1),
      if x.val + y.val ≠ n ∧ x.val + z.val ≠ n ∧ y.val + z.val ≠ n then
        (n+1 - ({x,y,z} : Finset (Fin (n+1))).card)^2 else 0 : ℕ) := by
  classical
  let A := Fin (n+1)
  let e : (A × A × A × A × A) ≃ (Fin 5 → A) := {
    toFun := fun ⟨x,y,z,l,r⟩ => ![l,x,y,z,r]
    invFun := fun u => (u 1,u 2,u 3,u 0,u 4)
    left_inv := fun ⟨_,_,_,_,_⟩ => rfl
    right_inv := by intro f; funext i; fin_cases i <;> rfl }
  unfold a
  congr 1
  rw [Finset.card_filter, ← Equiv.sum_comp e]
  simp only [Fintype.sum_prod_type, e, Equiv.coe_fn_mk]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  dsimp [A] at x y z ⊢
  simp_rw [array_good_iff]
  by_cases hm : x.val + y.val ≠ n ∧ x.val + z.val ≠ n ∧ y.val + z.val ≠ n
  · simp only [hm]
    rw [← array_allowed_count x y z, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hl : l.val + x.val ≠ n ∧ l.val + y.val ≠ n ∧ l.val + z.val ≠ n <;> simp [hl,hm]
  · simp [hm]

open Finset

private def array_mid_ok {n : ℕ} (x y z : Fin (n+1)) : Prop :=
  x.val + y.val ≠ n ∧ x.val + z.val ≠ n ∧ y.val + z.val ≠ n

private instance {n : ℕ} (x y z : Fin (n+1)) : Decidable (array_mid_ok x y z) := by
  unfold array_mid_ok
  infer_instance

private lemma array_mid_pair {n : ℕ} (x y : Fin (n+1)) :
    x.val + y.val ≠ n ↔ y ≠ x.rev := by
  rw [Ne, Ne, Fin.ext_iff, Fin.val_rev]
  have := x.isLt
  omega

private lemma array_mid_fixed (n : ℕ) :
    (∑ x : Fin (n+1), if x ≠ x.rev then (1:ℤ) else 0) =
    (n:ℤ)+1 - (if Even n then 1 else 0) := by
  classical
  by_cases he : Even n
  · obtain ⟨k,hk⟩ := he
    let c : Fin (n+1) := ⟨k,by omega⟩
    have h (x : Fin (n+1)) : x = x.rev ↔ x = c := by
      rw [Fin.ext_iff, Fin.ext_iff, Fin.val_rev]
      change _ ↔ x.val = k
      have := x.isLt
      omega
    have h' (x : Fin (n+1)) : (if x ≠ x.rev then (1:ℤ) else 0) =
        1 - (if x = c then 1 else 0) := by
      by_cases hx : x=c <;> simp [Ne, h, hx]
    simp_rw [h']
    rw [Finset.sum_sub_distrib]
    have he' : Even n := ⟨k,hk⟩
    simp [he']
  · have h (x : Fin (n+1)) : x ≠ x.rev := by
      intro eq
      have hh := congrArg Fin.val eq
      rw [Fin.val_rev] at hh
      have := x.isLt
      exact he ⟨x.val, by omega⟩
    simp [h,he]

private lemma array_mid_sum_z {n : ℕ} (x y : Fin (n+1)) :
    (∑ z : Fin (n+1), if array_mid_ok x y z then (1:ℤ) else 0) =
      if y = x.rev then 0 else
        ((n:ℤ)+1-2) + (if y = x then 1 else 0) := by
  classical
  simp only [array_mid_ok, array_mid_pair]
  by_cases bad : y = x.rev
  · simp [bad]
  by_cases xy : y = x
  · subst y
    have h (z : Fin (n+1)) : (if x ≠ x.rev ∧ z ≠ x.rev ∧ z ≠ x.rev then (1:ℤ) else 0) =
        1 - (if z = x.rev then 1 else 0) := by
      by_cases hz : z = x.rev <;> simp [bad,hz]
    simp_rw [h]
    rw [sum_sub_distrib]
    simp [bad]
    ring
  · have hr : y.rev ≠ x.rev := fun h => xy (Fin.rev_inj.mp h)
    have h (z : Fin (n+1)) : (if y ≠ x.rev ∧ z ≠ x.rev ∧ z ≠ y.rev then (1:ℤ) else 0) =
        1 - (if z = x.rev then 1 else 0) - (if z = y.rev then 1 else 0) := by
      by_cases hz : z = x.rev <;> by_cases hz' : z = y.rev <;>
        simp_all
    simp_rw [h]
    rw [sum_sub_distrib, sum_sub_distrib]
    simp [bad, xy]
    ring

private lemma array_mid_total (n : ℕ) :
    (∑ x : Fin (n+1), ∑ y : Fin (n+1), ∑ z : Fin (n+1),
      if array_mid_ok x y z then (1:ℤ) else 0) =
    ((n:ℤ)+1)*((n:ℤ)+1-1)*((n:ℤ)+1-2) +
      (((n:ℤ)+1) - (if Even n then 1 else 0)) := by
  classical
  simp_rw [array_mid_sum_z]
  have h (x y : Fin (n+1)) :
      (if y = x.rev then (0:ℤ) else ((n:ℤ)+1-2) + (if y=x then 1 else 0)) =
      ((n:ℤ)+1-2) - (if y = x.rev then (n:ℤ)+1-2 else 0) +
        (if y=x then (if x ≠ x.rev then 1 else 0) else 0) := by
    by_cases h : y=x <;> by_cases g : y=x.rev <;> simp_all
  simp_rw [h, sum_add_distrib, sum_sub_distrib]
  simp only [Finset.sum_ite_eq', mem_univ, if_true, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one, array_mid_fixed]
  ring

private lemma array_mid_xy (n : ℕ) :
    (∑ x : Fin (n+1), ∑ y : Fin (n+1), ∑ z : Fin (n+1),
      if array_mid_ok x y z ∧ x=y then (1:ℤ) else 0) =
    (((n:ℤ)+1) - (if Even n then 1 else 0)) * ((n:ℤ)+1-1) := by
  classical
  have h (x y : Fin (n+1)) :
      (∑ z : Fin (n+1), if array_mid_ok x y z ∧ x=y then (1:ℤ) else 0) =
        (if y=x then ((if x ≠ x.rev then (1:ℤ) else 0) * ((n:ℤ)+1-1)) else 0) := by
    by_cases e : x=y
    · subst y
      simp only [and_true, if_true, array_mid_sum_z]
      by_cases g : x=x.rev
      · rw [if_pos g, if_neg (not_not_intro g), zero_mul]
      · rw [if_neg g, if_pos g, one_mul]
        ring
    · simp [e,Ne.symm e]
  simp_rw [h]
  simp only [Finset.sum_ite_eq', mem_univ, if_true, ← Finset.sum_mul, array_mid_fixed]

private lemma array_mid_xz (n : ℕ) :
    (∑ x : Fin (n+1), ∑ y : Fin (n+1), ∑ z : Fin (n+1),
      if array_mid_ok x y z ∧ x=z then (1:ℤ) else 0) =
    (((n:ℤ)+1) - (if Even n then 1 else 0)) * ((n:ℤ)+1-1) := by
  classical
  rw [← array_mid_xy]
  apply sum_congr rfl
  intro x _
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro z _
  have hp : array_mid_ok x z y ↔ array_mid_ok x y z := by unfold array_mid_ok; omega
  simp only [hp]

private lemma array_mid_yz (n : ℕ) :
    (∑ x : Fin (n+1), ∑ y : Fin (n+1), ∑ z : Fin (n+1),
      if array_mid_ok x y z ∧ y=z then (1:ℤ) else 0) =
    (((n:ℤ)+1) - (if Even n then 1 else 0)) * ((n:ℤ)+1-1) := by
  classical
  rw [← array_mid_xy, sum_comm]
  apply sum_congr rfl
  intro x _
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro z _
  have hp : array_mid_ok z x y ↔ array_mid_ok x y z := by unfold array_mid_ok; omega
  simp only [hp]

private lemma array_mid_xyz (n : ℕ) :
    (∑ x : Fin (n+1), ∑ y : Fin (n+1), ∑ z : Fin (n+1),
      if array_mid_ok x y z ∧ x=y ∧ y=z then (1:ℤ) else 0) =
    (((n:ℤ)+1) - (if Even n then 1 else 0)) := by
  classical
  have h (x y z : Fin (n+1)) :
      (if array_mid_ok x y z ∧ x=y ∧ y=z then (1:ℤ) else 0) =
        if z=y then (if y=x then (if x ≠ x.rev then 1 else 0) else 0) else 0 := by
    by_cases g : x=y
    · subst y
      by_cases g : x=z
      · subst z
        simp [array_mid_ok, array_mid_pair]
      · simp [g,Ne.symm g]
    · simp [g,Ne.symm g]
  simp_rw [h]
  simp only [sum_ite_eq', mem_univ, if_true, array_mid_fixed]

open Finset OMA.S_oeis_a246481

/-- Equalities between the three middle entries determine the endpoint weight. -/
private theorem array_weight_expansion (n : ℕ) (hn : 5 ≤ n)
    (P : Fin (n+1) → Fin (n+1) → Fin (n+1) → Prop) [∀ x y z, Decidable (P x y z)] :
    let N : ℤ := (n:ℤ)+1
    let v₁ := (N-1)^2
    let v₂ := (N-2)^2
    let v₃ := (N-3)^2
    let C := fun (p : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℤ) =>
      ∑ x, ∑ y, ∑ z, p x y z
    (↑(∑ x, ∑ y, ∑ z, if P x y z then (n+1-({x,y,z} : Finset (Fin (n+1))).card)^2 else 0 : ℕ) : ℤ) =
      v₃*C (fun x y z => if P x y z then 1 else 0) +
      (v₂-v₃)*(C (fun x y z => if P x y z ∧ x=y then 1 else 0) +
        C (fun x y z => if P x y z ∧ x=z then 1 else 0) +
        C (fun x y z => if P x y z ∧ y=z then 1 else 0)) +
      (v₁-3*v₂+2*v₃)*C (fun x y z => if P x y z ∧ x=y ∧ y=z then 1 else 0) := by
  classical
  intro N v₁ v₂ v₃ C
  have eqW (x y z : Fin (n+1)) :
      ((if P x y z then (n+1-({x,y,z} : Finset (Fin (n+1))).card)^2 else 0 : ℕ):ℤ) =
        v₃*(if P x y z then 1 else 0) +
        ((v₂-v₃)*(if P x y z ∧ x=y then 1 else 0) +
         (v₂-v₃)*(if P x y z ∧ x=z then 1 else 0) +
         (v₂-v₃)*(if P x y z ∧ y=z then 1 else 0)) +
        (v₁-3*v₂+2*v₃)*(if P x y z ∧ x=y ∧ y=z then 1 else 0) := by
    by_cases hp : P x y z
    · by_cases hxy : x=y
      · subst y
        by_cases hxz : x=z
        · subst z
          simp [hp, v₁,v₂,v₃,N]
          ring
        · simp [hp,hxz,v₁,v₂,v₃,N,card_pair hxz]
          congr 1
          omega
      · by_cases hxz : x=z
        · subst z
          simp [hp,hxy,Ne.symm hxy,v₁,v₂,v₃,N,card_pair (Ne.symm hxy)]
          congr 1
          omega
        · by_cases hyz : y=z
          · subst z
            simp [hp,hxy,v₁,v₂,v₃,N,card_pair hxy]
            congr 1
            omega
          · have hcard : ({x,y,z} : Finset (Fin (n+1))).card = 3 := by
              rw [card_insert_of_notMem (by simp [hxy,hxz]),card_pair hyz]
            simp [hp,hxy,hxz,hyz,v₁,v₂,v₃,N,hcard]
            congr 1
            omega
    · simp [hp]
  simp only [C,Nat.cast_sum] at *
  simp_rw [eqW]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  ring

open OMA.S_oeis_a246481

/-- The three summands count by the number of distinct middle values.
The indicator f records the unique self-complementary symbol at even n. -/
private theorem array246481_polys
    (counts : ∀ n : ℕ, 1 ≤ n →
      let N : ℤ := (n:ℤ)+1
      let f : ℤ := if Even n then 1 else 0
      let q := N-f
      a n = q*(N-1)^2 + 3*q*(N-2)*(N-2)^2 + q*(q-2)*(q-4+3*f)*(N-3)^2) :
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = 5*(n:ℚ)-11*(n:ℚ)^2+10*(n:ℚ)^3-4*(n:ℚ)^4+(n:ℚ)^5) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = 9-10*(n:ℚ)-4*(n:ℚ)^2+10*(n:ℚ)^3-4*(n:ℚ)^4+(n:ℚ)^5) := by
  constructor <;> intro n hn h
  · rw [counts n hn,if_pos h]
    push_cast
    ring
  · have noEven : ¬ Even n := by
      obtain ⟨k,hk⟩ := h
      rintro ⟨j,hj⟩
      omega
    rw [counts n hn,if_neg noEven]
    push_cast
    ring

open Finset OMA.S_oeis_a246481

private theorem array246481_small
    (endpoints : ∀ n : ℕ,
      a n = ↑(∑ x : Fin (n+1), ∑ y : Fin (n+1), ∑ z : Fin (n+1),
        if x.val + y.val ≠ n ∧ x.val + z.val ≠ n ∧ y.val + z.val ≠ n then
          (n+1 - ({x,y,z} : Finset (Fin (n+1))).card)^2 else 0 : ℕ))
    (n : ℕ) (hn : 1 ≤ n) (hs : n < 5) :
    let N : ℤ := (n:ℤ)+1
    let f : ℤ := if Even n then 1 else 0
    let q := N-f
    a n = q*(N-1)^2 + 3*q*(N-2)*(N-2)^2 + q*(q-2)*(q-4+3*f)*(N-3)^2 := by
  dsimp only
  rw [endpoints n]
  interval_cases n <;> decide +kernel

open OMA.S_oeis_a246481 PowerSeries

set_option maxHeartbeats 3000000 in
private lemma array246481_conclusion
    (he : ∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) =
      5*(n:ℚ) - 11*(n:ℚ)^2 + 10*(n:ℚ)^3 - 4*(n:ℚ)^4 + (n:ℚ)^5)
    (ho : ∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) =
      9 - 10*(n:ℚ) - 4*(n:ℚ)^2 + 10*(n:ℚ)^3 - 4*(n:ℚ)^4 + (n:ℚ)^5) :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 6 * (1 + X) ^ 3 : PowerSeries ℚ) = 2 * X * (1 + 4 * X + 45 * X ^ 2 + 52 * X ^ 3 + 191 * X ^ 4 + 72 * X ^ 5 + 115 * X ^ 6)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = 5 * (n : ℚ) - 11 * (n : ℚ) ^ 2 + 10 * (n : ℚ) ^ 3 - 4 * (n : ℚ) ^ 4 + (n : ℚ) ^ 5) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = 9 - 10 * (n : ℚ) - 4 * (n : ℚ) ^ 2 + 10 * (n : ℚ) ^ 3 - 4 * (n : ℚ) ^ 4 + (n : ℚ) ^ 5) := by
  refine ⟨?_, he, ho⟩
  let P : ℚ → ℚ := fun x => 5*x - 11*x^2 + 10*x^3 - 4*x^4 + x^5
  let Q : ℚ → ℚ := fun x => 9 - 10*x - 4*x^2 + 10*x^3 - 4*x^4 + x^5
  let b (n : ℕ) : ℚ := if n < 1 then 0 else (a n : ℚ)
  have hb (n : ℕ) : b n = if n%2=0 then P n else Q n := by
    rcases n with _ | n
    · norm_num [b, P]
    · simp only [b, show ¬ n+1 < 1 by omega, if_false]
      by_cases h : (n+1)%2=0
      · rw [if_pos h]
        exact he _ (by omega) (Nat.even_iff.mpr h)
      · rw [if_neg h]
        exact ho _ (by omega) (Nat.odd_iff.mpr (by omega))
  let A := PowerSeries.mk b
  have lhs : A*((1-X)^6*(1+X)^3) =
      A - C 3 * (A*X^1) + C 8 * (A*X^3) - C 6 * (A*X^4) -
      C 6 * (A*X^5) + C 8 * (A*X^6) - C 3 * (A*X^8) + A*X^9 := by
    norm_num [map_ofNat]
    ring
  have rhs : 2*X*(1 + 4*X + 45*X^2 + 52*X^3 + 191*X^4 + 72*X^5 + 115*X^6) =
      C (2 : ℚ)*X^1 + C 8*X^2 + C 90*X^3 + C 104*X^4 +
      C 382*X^5 + C 144*X^6 + C 230*X^7 := by
    norm_num [map_ofNat]
    ring
  change A*((1-X)^6*(1+X)^3) = _
  rw [lhs, rhs]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk,
    coeff_C]
  by_cases hlarge : 9 ≤ n
  · simp (disch := omega) only [if_pos, if_neg]
    simp only [hb]
    by_cases h : n%2=0 <;> simp (disch := omega) only [if_pos, if_neg] <;>
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_ofNat] <;>
      dsimp only [P, Q] <;> ring
  · interval_cases n <;> norm_num [hb, P, Q]

theorem OMA.solution : type_of% @OMA.S_oeis_a246481.main := by
  apply And.elim array246481_conclusion
  apply array246481_polys
  intro n hn
  by_cases hs : n < 5
  · exact array246481_small array_endpoints n hn hs
  rw [array_endpoints]
  have H := array_weight_expansion n (by omega) (@array_mid_ok n)
  dsimp only at H ⊢
  rw [array_mid_total,array_mid_xy,array_mid_xz,array_mid_yz,array_mid_xyz] at H
  exact H.trans (by split_ifs <;> ring)
