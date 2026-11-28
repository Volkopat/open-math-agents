import OMAStatements.S_oeis_a187029
import Mathlib

/-!
# The generating function of four-square queen tours

Every admissible relative tour has coordinate spans at most six, since its
three moves each change a coordinate by at most two. Its translation count
on a board of side at least six is consequently a quadratic polynomial.
Summing gives the third-difference recurrence. The kernel computes the
initial values from all ordered triples of moves, grouped by the first move.
These initial values and the recurrence determine the generating function.

Source: R. H. Hardin and Colin Barker, OEIS A187029, https://oeis.org/A187029.
-/
namespace OMA.QueenTours
open OMA.S_oeis_a187029 Finset

private lemma smallMove : ∀ i : Fin 16,
    (-2 ≤ (move i).1 ∧ (move i).1 ≤ 2) ∧ (-2 ≤ (move i).2 ∧ (move i).2 ≤ 2) := by
  decide +kernel

private lemma short (a b c : ℤ) (ha : -2 ≤ a ∧ a ≤ 2)
    (hb : -2 ≤ b ∧ b ≤ 2) (hc : -2 ≤ c ∧ c ≤ 2) : extent a (a+b) (a+b+c) ≤ 6 := by
  unfold extent
  omega

private lemma bounded (i j k : Fin 16) (w h : ℕ) (hspan : spans i j k = some (w,h)) :
    w ≤ 6 ∧ h ≤ 6 := by
  unfold spans at hspan
  dsimp only at hspan
  split at hspan
  · cases hspan
    exact ⟨short _ _ _ (smallMove i).1 (smallMove j).1 (smallMove k).1,
      short _ _ _ (smallMove i).2 (smallMove j).2 (smallMove k).2⟩
  · contradiction

private theorem recur (n : ℕ) (hn : 6 ≤ n) :
    (term (n+3) : ℤ) + 3*term (n+1) = 3*term (n+2) + term n := by
  simp only [term,Nat.cast_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  cases hs : spans i j k with
  | none => simp [placements]
  | some d =>
    obtain ⟨w,h⟩ := d
    obtain ⟨hw,hh⟩ := bounded i j k w h hs
    simp only [placements,Nat.cast_mul,Nat.cast_sub (show w ≤ n+3 by omega),
      Nat.cast_sub (show h ≤ n+3 by omega),Nat.cast_sub (show w ≤ n+2 by omega),
      Nat.cast_sub (show h ≤ n+2 by omega),Nat.cast_sub (show w ≤ n+1 by omega),
      Nat.cast_sub (show h ≤ n+1 by omega),Nat.cast_sub (show w ≤ n by omega),
      Nat.cast_sub (show h ≤ n by omega),Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
    ring

private lemma slice0 : ∀ n : Fin 9, (∑ j : Fin 16, ∑ k : Fin 16, placements n.val (spans 0 j k)) = (![0,0,2,96,497,1335,2630,4359,6522] : Fin 9 → ℕ) n := by decide +kernel
private lemma slice1 : ∀ n : Fin 9, (∑ j : Fin 16, ∑ k : Fin 16, placements n.val (spans 1 j k)) = (![0,0,4,146,646,1605,3018,4869,7158] : Fin 9 → ℕ) n := by decide +kernel
private lemma slice2 : ∀ n : Fin 9, (∑ j : Fin 16, ∑ k : Fin 16, placements n.val (spans 2 j k)) = (![0,0,2,96,497,1335,2630,4359,6522] : Fin 9 → ℕ) n := by decide +kernel
private lemma slice3 : ∀ n : Fin 9, (∑ j : Fin 16, ∑ k : Fin 16, placements n.val (spans 3 j k)) = (![0,0,4,146,646,1605,3018,4869,7158] : Fin 9 → ℕ) n := by decide +kernel
private lemma slice4 : ∀ n : Fin 9, (∑ j : Fin 16, ∑ k : Fin 16, placements n.val (spans 4 j k)) = (![0,0,4,146,646,1605,3018,4869,7158] : Fin 9 → ℕ) n := by decide +kernel
private lemma slice5 : ∀ n : Fin 9, (∑ j : Fin 16, ∑ k : Fin 16, placements n.val (spans 5 j k)) = (![0,0,2,96,497,1335,2630,4359,6522] : Fin 9 → ℕ) n := by decide +kernel
private lemma slice6 : ∀ n : Fin 9, (∑ j : Fin 16, ∑ k : Fin 16, placements n.val (spans 6 j k)) = (![0,0,4,146,646,1605,3018,4869,7158] : Fin 9 → ℕ) n := by decide +kernel
private lemma slice7 : ∀ n : Fin 9, (∑ j : Fin 16, ∑ k : Fin 16, placements n.val (spans 7 j k)) = (![0,0,2,96,497,1335,2630,4359,6522] : Fin 9 → ℕ) n := by decide +kernel
private lemma slice8 : ∀ n : Fin 9, (∑ j : Fin 16, ∑ k : Fin 16, placements n.val (spans 8 j k)) = (![0,0,0,24,211,764,1765,3241,5161] : Fin 9 → ℕ) n := by decide +kernel
private lemma slice9 : ∀ n : Fin 9, (∑ j : Fin 16, ∑ k : Fin 16, placements n.val (spans 9 j k)) = (![0,0,0,70,410,1188,2424,4121,6254] : Fin 9 → ℕ) n := by decide +kernel
private lemma slice10 : ∀ n : Fin 9, (∑ j : Fin 16, ∑ k : Fin 16, placements n.val (spans 10 j k)) = (![0,0,0,24,211,764,1765,3241,5161] : Fin 9 → ℕ) n := by decide +kernel
private lemma slice11 : ∀ n : Fin 9, (∑ j : Fin 16, ∑ k : Fin 16, placements n.val (spans 11 j k)) = (![0,0,0,70,410,1188,2424,4121,6254] : Fin 9 → ℕ) n := by decide +kernel
private lemma slice12 : ∀ n : Fin 9, (∑ j : Fin 16, ∑ k : Fin 16, placements n.val (spans 12 j k)) = (![0,0,0,70,410,1188,2424,4121,6254] : Fin 9 → ℕ) n := by decide +kernel
private lemma slice13 : ∀ n : Fin 9, (∑ j : Fin 16, ∑ k : Fin 16, placements n.val (spans 13 j k)) = (![0,0,0,24,211,764,1765,3241,5161] : Fin 9 → ℕ) n := by decide +kernel
private lemma slice14 : ∀ n : Fin 9, (∑ j : Fin 16, ∑ k : Fin 16, placements n.val (spans 14 j k)) = (![0,0,0,70,410,1188,2424,4121,6254] : Fin 9 → ℕ) n := by decide +kernel
private lemma slice15 : ∀ n : Fin 9, (∑ j : Fin 16, ∑ k : Fin 16, placements n.val (spans 15 j k)) = (![0,0,0,24,211,764,1765,3241,5161] : Fin 9 → ℕ) n := by decide +kernel
private lemma smallValues (n : Fin 9) : term n.val = (![0,0,24,1344,7056,19568,39348,66360,100380] : Fin 9 → ℕ) n := by
  unfold term
  let f (i : Fin 16) := ∑ j : Fin 16, ∑ k : Fin 16, placements n.val (spans i j k)
  change ∑ i : Fin 16, f i = _
  rw [show (Finset.univ : Finset (Fin 16)) = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15} by decide]
  simp (disch := decide) only [Finset.sum_insert,Finset.sum_singleton]
  dsimp only [f]
  rw [slice0 n, slice1 n, slice2 n, slice3 n, slice4 n, slice5 n, slice6 n, slice7 n, slice8 n, slice9 n, slice10 n, slice11 n, slice12 n, slice13 n, slice14 n, slice15 n]
  fin_cases n <;> decide

open PowerSeries in
set_option maxHeartbeats 1500000 in
private theorem generating (a : ℕ → ℕ)
    (initial : ∀ n : Fin 9, a n.val = (![0,0,24,1344,7056,19568,39348,66360,100380] : Fin 9 → ℕ) n)
    (rec : ∀ n ≥ 6, (a (n+3) : ℤ) + 3*a (n+1) = 3*a (n+2) + a n) :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X)^3 =
      4*X^2*(6 + 318*X + 774*X^2 + 602*X^3 + 117*X^4 - 9*X^5 - 56*X^6) := by
  let F := PowerSeries.mk (fun n => (a n : ℤ))
  change F * _ = _
  have left : F * (1-X)^3 = F - (3:ℤ) • (F*X^1) + (3:ℤ) • (F*X^2) - F*X^3 := by
    simp only [zsmul_eq_mul,Int.cast_ofNat]; ring
  have right : (4*X^2*(6+318*X+774*X^2+602*X^3+117*X^4-9*X^5-56*X^6) : PowerSeries ℤ) =
      (24:ℤ) • X^2 + (1272:ℤ) • X^3 + (3096:ℤ) • X^4 + (2408:ℤ) • X^5 +
      (468:ℤ) • X^6 - (36:ℤ) • X^7 - (224:ℤ) • X^8 := by
    simp only [zsmul_eq_mul,Int.cast_ofNat]; ring
  rw [left,right]
  apply PowerSeries.ext
  intro n
  simp only [map_add,map_sub,map_zsmul]
  simp only [coeff_X_pow,coeff_mul_X_pow',F,coeff_mk,zsmul_eq_mul,Int.cast_id]
  by_cases hn : n ≤ 8
  · have v0 := initial 0
    have v1 := initial 1
    have v2 := initial 2
    have v3 := initial 3
    have v4 := initial 4
    have v5 := initial 5
    have v6 := initial 6
    have v7 := initial 7
    have v8 := initial 8
    change a 0 = 0 at v0
    change a 1 = 0 at v1
    change a 2 = 24 at v2
    change a 3 = 1344 at v3
    change a 4 = 7056 at v4
    change a 5 = 19568 at v5
    change a 6 = 39348 at v6
    change a 7 = 66360 at v7
    change a 8 = 100380 at v8
    interval_cases n <;> norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8]
  · have h := rec (n-3) (by omega)
    rw [show n-3+3=n by omega,show n-3+1=n-2 by omega,show n-3+2=n-1 by omega] at h
    simp only [if_pos (show 1 ≤ n by omega),if_pos (show 2 ≤ n by omega),if_pos (show 3 ≤ n by omega),
      if_neg (show n ≠ 2 by omega),if_neg (show n ≠ 3 by omega),if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega),if_neg (show n ≠ 6 by omega),if_neg (show n ≠ 7 by omega),
      if_neg (show n ≠ 8 by omega),mul_zero,add_zero,sub_zero]
    linarith


theorem result : type_of% @OMA.S_oeis_a187029.main := by
  refine ⟨generating term smallValues recur, ?_⟩
  intro n hn
  have h := recur (n-3) (by omega)
  rw [show n-3+3=n by omega,show n-3+1=n-2 by omega,show n-3+2=n-1 by omega] at h
  linarith

end OMA.QueenTours

theorem OMA.solution : type_of% @OMA.S_oeis_a187029.main := OMA.QueenTours.result
