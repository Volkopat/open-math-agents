import OMAStatements.S_oeis_a245872

/-!
# Five-entry arrays with a complementary pair in each triple

This proves Colin Barker's parity formulas and generating function for
R. H. Hardin's OEIS A245872 (https://oeis.org/A245872).

Fix the three interior entries b,c,d and write m = n+1. If b and c
sum to n, the first entry is free. Otherwise it must be the complement
of b or c, giving one or two choices according as b=c or b≠c. The last
entry has the analogous count. Summing over the valid middle triples
gives 5m²−2m−8 for each center c, with an additional 2m+4 when 2c=n.
The unique possible fixed center accounts for the two parity formulas.
-/

namespace Arrays245

theorem rev_iff_add {n : ℕ} (x y : Fin (n+1)) :
    x.rev = y ↔ x.val + y.val = n := by
  rw [Fin.ext_iff, Fin.val_rev]
  omega

theorem card_rev_fixed (n : ℕ) :
    (Finset.univ.filter (fun x : Fin (n+1) => x.rev = x)).card = if Even n then 1 else 0 := by
  split_ifs with he
  · obtain ⟨t, ht⟩ := he
    let z : Fin (n+1) := ⟨t,by omega⟩
    have hs : (Finset.univ.filter fun x : Fin (n+1) => x.rev=x) = {z} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [rev_iff_add, Fin.ext_iff]
      change x.val+x.val=n ↔ x.val=t
      omega
    rw [hs, Finset.card_singleton]
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have t := (rev_iff_add x x).mp (Finset.mem_filter.mp hx).2
    exact he ⟨x.val,t.symm⟩

theorem sum_rev_fixed {R : Type*} [AddCommMonoid R] (n : ℕ) (a b : R) :
    (∑ x : Fin (n+1), if x.rev=x then a else b) = if Even n then a+n • b else (n+1) • b := by
  have part := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun x : Fin (n+1) => x.rev=x)
  rw [card_rev_fixed, Finset.card_univ, Fintype.card_fin] at part
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, card_rev_fixed]
  by_cases he : Even n
  · simp only [if_pos he, one_nsmul] at part ⊢
    have hcard : (Finset.univ.filter (fun x : Fin (n+1) => ¬x.rev=x)).card = n := by omega
    rw [hcard]
  · simp only [if_neg he, zero_nsmul, zero_add] at part ⊢
    rw [part]

theorem sum_fixed_even {n : ℕ} (hn : Even n) (v : ℤ) :
    (∑ c : Fin (n+1), if c=c.rev then v else 0) = v := by
  simpa [eq_comm,hn] using sum_rev_fixed n v 0

theorem sum_fixed_odd {n : ℕ} (hn : Odd n) (v : ℤ) :
    (∑ c : Fin (n+1), if c=c.rev then v else 0) = 0 := by
  simpa [eq_comm,Nat.not_even_iff_odd.mpr hn] using sum_rev_fixed n v 0

end Arrays245

namespace Arrays245
open Finset OMA.S_oeis_a245872

private theorem all_three (P : ℕ → Prop) :
    (∀ i<3, P i) ↔ P 0 ∧ P 1 ∧ P 2 := by
  constructor
  · exact fun h => ⟨h 0 (by decide),h 1 (by decide),h 2 (by decide)⟩
  · rintro ⟨h0,h1,h2⟩ i hi
    interval_cases i <;> assumption

private theorem exists_three (P : ℕ → Prop) :
    (∃ i<3, P i) ↔ P 0 ∨ P 1 ∨ P 2 := by
  constructor
  · rintro ⟨i,hi,h⟩
    interval_cases i <;> tauto
  · rintro (h|h|h)
    · exact ⟨0,by decide,h⟩
    · exact ⟨1,by decide,h⟩
    · exact ⟨2,by decide,h⟩

private theorem sum_to_rev {n : ℕ} (b c : Fin (n+1)) :
    b.val+c.val=n ↔ b=c.rev := by
  rw [Fin.ext_iff,Fin.val_rev]
  have := c.isLt
  omega

private theorem dual_eq {n : ℕ} (b c : Fin (n+1)) : b=c.rev ↔ c=b.rev := by
  rw [←sum_to_rev,←sum_to_rev,add_comm]

theorem good_windows {n : ℕ} (u b c d v : Fin (n+1)) :
    good ![u,b,c,d,v] = true ↔
    (b=c.rev ∨ u=b.rev ∨ u=c.rev) ∧ (b=c.rev ∨ d=c.rev ∨ d=b.rev) ∧
    (d=c.rev ∨ v=d.rev ∨ v=c.rev) := by
  simp only [good, decide_eq_true_eq, all_three, exists_three]
  norm_num [OMA.S_oeis_a245872.get, sum_to_rev]
  grind [dual_eq]

private theorem end_choices {n : ℕ} (b c : Fin (n+1)) :
    (∑ x : Fin (n+1),if b=c.rev ∨ x=b.rev ∨ x=c.rev then (1:ℤ) else 0) =
      if b=c.rev then (n:ℤ)+1 else if b=c then 1 else 2 := by
  by_cases h : b=c.rev
  · simp [h]
  simp only [h,false_or,if_false]
  by_cases e : b=c
  · subst b; simp
  have he : b.rev ≠ c.rev := fun h => e (Fin.rev_injective h)
  rw [if_neg e]
  calc
    _ = ∑ x : Fin (n+1), ((if x=b.rev then (1:ℤ) else 0)+(if x=c.rev then 1 else 0)) := by
      apply sum_congr rfl
      intro x _
      by_cases h₁ : x=b.rev <;> by_cases h₂ : x=c.rev <;> simp_all
    _ = 2 := by rw [sum_add_distrib]; simp

theorem count_middle (n : ℕ) :
    a n = ∑ c : Fin (n+1), ∑ b : Fin (n+1), ∑ d : Fin (n+1),
      if b=c.rev ∨ d=c.rev ∨ d=b.rev then
        (if b=c.rev then (↑n+1 : ℤ) else if b=c then 1 else 2) *
        (if d=c.rev then (↑n+1 : ℤ) else if d=c then 1 else 2) else 0 := by
  let A := Fin (n+1)
  let E : (Fin 5 → A) ≃ A × A × A × A × A :=
    { toFun := fun x => (x 2,x 1,x 3,x 0,x 4)
      invFun := fun ⟨c,b,d,u,v⟩ => ![u,b,c,d,v]
      left_inv := by intro x; funext i; fin_cases i <;> rfl
      right_inv := by rintro ⟨c,b,d,u,v⟩; rfl }
  let W (x : Fin 5 → A) : ℤ := if good x then 1 else 0
  change (↑((univ.filter (fun x : Fin 5 → A => good x)).card) : ℤ) = _
  have ha : (↑((univ.filter (fun x : Fin 5 → A => good x)).card) : ℤ) = ∑ x,W x := by
    rw [card_filter]
    simp [W]
  rw [ha,←E.symm.sum_comp W]
  simp only [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro d _
  change (∑ u : Fin (n+1),∑ v : Fin (n+1),if good ![u,b,c,d,v] then (1:ℤ) else 0)=_
  simp only [good_windows]
  by_cases hm : b=c.rev ∨ d=c.rev ∨ d=b.rev
  · rw [if_pos hm,←end_choices b c,←end_choices d c,sum_mul]
    apply sum_congr rfl
    intro u _
    rw [mul_sum]
    apply sum_congr rfl
    intro v _
    by_cases hl : b=c.rev ∨ u=b.rev ∨ u=c.rev <;>
      by_cases hr : d=c.rev ∨ v=d.rev ∨ v=c.rev <;> simp [hm,hl,hr]
  · simp [hm]

end Arrays245

namespace Arrays245

private theorem middle_weight_sum {n : ℕ} (c : Fin (n + 1)) :
    (∑ b : Fin (n + 1), (if b = c.rev then ((n : ℤ) + 1) else if b = c then (1 : ℤ) else 2)) =
      3 * ((n : ℤ) + 1) - 2 - (if c = c.rev then 0 else 1) := by
  have w (b : Fin (n + 1)) : (if b = c.rev then ((n : ℤ) + 1) else if b = c then (1 : ℤ) else 2) =
      (2 + (if b = c.rev then ((n : ℤ) + 1) - 2 else 0)) -
        (if b = c then (if c = c.rev then 0 else 1) else 0) := by
    split_ifs <;> grind
  simp_rw [w]
  simp [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

private theorem middle_outside_sum {n : ℕ} (c : Fin (n + 1)) :
    (∑ b : Fin (n + 1), (if b = c.rev ∨ b = c then 0 else (4 : ℤ))) =
      4 * ((n : ℤ) + 1) - 4 - (if c = c.rev then 0 else 4) := by
  have w (b : Fin (n + 1)) : (if b = c.rev ∨ b = c then 0 else (4 : ℤ)) =
      4 - (if b = c.rev then 4 else 0) -
        (if b = c then (if c = c.rev then 0 else 4) else 0) := by
    split_ifs <;> grind
  simp_rw [w]
  simp [Finset.sum_sub_distrib]
  ring

private theorem middle_row {n : ℕ} (b c : Fin (n + 1)) :
    (∑ d : Fin (n + 1), if b = c.rev ∨ d = c.rev ∨ d = b.rev then
      (if b = c.rev then ((n : ℤ) + 1) else if b = c then (1 : ℤ) else 2) * (if d = c.rev then ((n : ℤ) + 1) else if d = c then (1 : ℤ) else 2) else 0) =
      (if b = c.rev then ((n : ℤ) + 1) * (∑ d : Fin (n + 1), (if d = c.rev then ((n : ℤ) + 1) else if d = c then (1 : ℤ) else 2)) - ((n : ℤ) + 1)^2 else 0) +
        (if b = c.rev then ((n : ℤ) + 1) else if b = c then (1 : ℤ) else 2) * ((n : ℤ) + 1) + (if b = c.rev ∨ b = c then 0 else 4) := by
  by_cases hb : b = c.rev
  · simp [hb, Finset.mul_sum]
    ring
  · have h (d : Fin (n + 1)) :
        (if b = c.rev ∨ d = c.rev ∨ d = b.rev then (if b = c.rev then ((n : ℤ) + 1) else if b = c then (1 : ℤ) else 2) * (if d = c.rev then ((n : ℤ) + 1) else if d = c then (1 : ℤ) else 2) else 0) =
          (if d = c.rev then (if b = c.rev then ((n : ℤ) + 1) else if b = c then (1 : ℤ) else 2) * ((n : ℤ) + 1) else 0) +
            (if d = b.rev then (if b = c then 0 else 4) else 0) := by
        by_cases hd : d = c.rev
        · subst d
          by_cases hbc : b = c
          · simp [hbc]
          · have hn : c.rev ≠ b.rev := fun h => hbc (Fin.rev_injective h.symm)
            simp [hn]
        · by_cases hr : d = b.rev
          · have hbc : b ≠ c := by rintro rfl; exact hd hr
            have hdc : d ≠ c := by
              rintro rfl
              exact hb (by simpa using (congrArg Fin.rev hr).symm)
            have hg : b = c.rev ∨ d = c.rev ∨ d = b.rev := Or.inr (Or.inr hr)
            simp only [if_pos hg, if_neg hb, if_neg hbc, if_neg hd, if_neg hdc, if_pos hr, zero_add]
            rfl
          · simp [hb, hd, hr]
    simp_rw [h]
    simp [hb, Finset.sum_add_distrib]

theorem middle_center {n : ℕ} (c : Fin (n + 1)) :
    (∑ b : Fin (n + 1), ∑ d : Fin (n + 1), if b = c.rev ∨ d = c.rev ∨ d = b.rev then
      (if b = c.rev then ((n : ℤ) + 1) else if b = c then (1 : ℤ) else 2) * (if d = c.rev then ((n : ℤ) + 1) else if d = c then (1 : ℤ) else 2) else 0) =
      (5 * ((n : ℤ) + 1)^2 - 2 * ((n : ℤ) + 1) - 8) + (if c = c.rev then 2 * ((n : ℤ) + 1) + 4 else 0) := by
  simp_rw [middle_row]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, middle_weight_sum, middle_outside_sum]
  split_ifs <;> ring


theorem middle_even (n : ℕ) (hn : Even n) :
    (∑ c : Fin (n + 1), ∑ b : Fin (n + 1), ∑ d : Fin (n + 1),
      if b = c.rev ∨ d = c.rev ∨ d = b.rev then (if b = c.rev then ((n : ℤ) + 1) else if b = c then (1 : ℤ) else 2) * (if d = c.rev then ((n : ℤ) + 1) else if d = c then (1 : ℤ) else 2) else 0) = 1 + 5 * (n : ℤ) + 13 * (n : ℤ)^2 + 5 * (n : ℤ)^3 := by
  simp_rw [middle_center]
  rw [Finset.sum_add_distrib, sum_fixed_even hn]
  simp
  ring

theorem middle_odd (n : ℕ) (hn : Odd n) :
    (∑ c : Fin (n + 1), ∑ b : Fin (n + 1), ∑ d : Fin (n + 1),
      if b = c.rev ∨ d = c.rev ∨ d = b.rev then (if b = c.rev then ((n : ℤ) + 1) else if b = c then (1 : ℤ) else 2) * (if d = c.rev then ((n : ℤ) + 1) else if d = c then (1 : ℤ) else 2) else 0) = -5 + 3 * (n : ℤ) + 13 * (n : ℤ)^2 + 5 * (n : ℤ)^3 := by
  simp_rw [middle_center]
  rw [Finset.sum_add_distrib, sum_fixed_odd hn]
  simp
  ring

end Arrays245

namespace Arrays245
open OMA.S_oeis_a245872 PowerSeries

theorem series_of_formulas
    (he : ∀ n : ℕ, 1 ≤ n → Even n →
      (a n : ℚ) = 1 + 5 * (n : ℚ) + 13 * (n : ℚ)^2 + 5 * (n : ℚ)^3)
    (ho : ∀ n : ℕ, 1 ≤ n → Odd n →
      (a n : ℚ) = -5 + 3 * (n : ℚ) + 13 * (n : ℚ)^2 + 5 * (n : ℚ)^3) :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) *
       ((1-X)^4*(1+X)^2 : PowerSeries ℚ) =
      X * (16 + 71*X + 34*X^2 - 2*X^3 + 2*X^4 - X^5) := by
  let S : PowerSeries ℚ := PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ))
  have vals (n : ℕ) : coeff n S = if n < 1 then 0 else if n%2=0 then
      1+5*(n:ℚ)+13*(n:ℚ)^2+5*(n:ℚ)^3 else -5+3*(n:ℚ)+13*(n:ℚ)^2+5*(n:ℚ)^3 := by
    simp only [S,coeff_mk]
    split_ifs with h1 h2
    · rfl
    · exact he n (by omega) (Nat.even_iff.mpr h2)
    · exact ho n (by omega) (Nat.odd_iff.mpr (by omega))
  have left : S*((1-X)^4*(1+X)^2) =
      S - (S*X^1 + S*X^1) - S*X^2 + (S*X^3+S*X^3+S*X^3+S*X^3)
        - S*X^4 - (S*X^5+S*X^5) + S*X^6 := by ring
  have right : X * (16+71*X+34*X^2-2*X^3+2*X^4-X^5 : PowerSeries ℚ) =
      C (16:ℚ)*X^1 + C (71:ℚ)*X^2 + C (34:ℚ)*X^3 -
      C (2:ℚ)*X^4 + C (2:ℚ)*X^5 - C (1:ℚ)*X^6 := by
    simp only [map_ofNat,map_one]; ring
  change S*_ = _
  rw [left,right]
  ext n
  simp only [map_add,map_sub,coeff_mul_X_pow',coeff_C,vals]
  by_cases h : n < 7
  · interval_cases n <;> norm_num
  · by_cases par : n%2=0
    all_goals
      simp (disch := omega) only [if_pos,if_neg,Nat.cast_sub]
      push_cast
      ring

end Arrays245

namespace Arrays245
open OMA.S_oeis_a245872

/-- The entry also records the associated sixth-order empirical recurrence. -/
theorem sixth_order_of_formulas
    (ev : ∀ n : ℕ, Even n → a n=1+5*(n:ℤ)+13*(n:ℤ)^2+5*(n:ℤ)^3)
    (od : ∀ n : ℕ, Odd n → a n= -5+3*(n:ℤ)+13*(n:ℤ)^2+5*(n:ℤ)^3)
    (n : ℕ) : a (n+6)=2*a (n+5)+a (n+4)-4*a (n+3)+a (n+2)+2*a (n+1)-a n := by
  have coeff (i : ℕ) : a i=if i%2=0 then 1+5*(i:ℤ)+13*(i:ℤ)^2+5*(i:ℤ)^3
        else -5+3*(i:ℤ)+13*(i:ℤ)^2+5*(i:ℤ)^3 := by
    split_ifs with hi
    · exact ev i (Nat.even_iff.mpr hi)
    · exact od i (Nat.odd_iff.mpr (by omega))
  simp only [coeff]
  by_cases h : n%2=0
  all_goals
    simp (disch := omega) only [if_pos,if_neg]
    push_cast
    ring

end Arrays245

namespace Arrays245
open OMA.S_oeis_a245872

theorem arrays_even (n : ℕ) (hn : Even n) :
    a n=1+5*(n:ℤ)+13*(n:ℤ)^2+5*(n:ℤ)^3 :=
  (count_middle n).trans (middle_even n hn)

theorem arrays_odd (n : ℕ) (hn : Odd n) :
    a n= -5+3*(n:ℤ)+13*(n:ℤ)^2+5*(n:ℤ)^3 :=
  (count_middle n).trans (middle_odd n hn)

theorem arrays_sixth_order (n : ℕ) :
    a (n+6)=2*a (n+5)+a (n+4)-4*a (n+3)+a (n+2)+2*a (n+1)-a n :=
  sixth_order_of_formulas arrays_even arrays_odd n

end Arrays245

open Arrays245 OMA.S_oeis_a245872

theorem OMA.solution : type_of% @OMA.S_oeis_a245872.main := by
  have ev (n : ℕ) (_ : 1≤n) (hn : Even n) :
      (a n : ℚ)=1+5*(n:ℚ)+13*(n:ℚ)^2+5*(n:ℚ)^3 := by
    exact_mod_cast arrays_even n hn
  have od (n : ℕ) (_ : 1≤n) (hn : Odd n) :
      (a n : ℚ)= -5+3*(n:ℚ)+13*(n:ℚ)^2+5*(n:ℚ)^3 := by
    exact_mod_cast arrays_odd n hn
  exact ⟨series_of_formulas ev od,ev,od⟩
