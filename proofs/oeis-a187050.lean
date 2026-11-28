import OMAStatements.S_oeis_a187050
import Mathlib

/-!
# The generating function and recurrence for six-square bishop tours

Group the relative tours by their first directed move. A multiplicity table
records how many completions have each pair of bounding-box spans. Inserting
an entry into the table preserves the weighted sum of its placements.
The eight finite certificates are checked by the kernel. They yield the
quadratic count 16752 n² − 163720 n + 397436 for n ≥ 10. The finite initial
values and its third difference give Barker's offset-one generating function.

Source: R. H. Hardin and Colin Barker, OEIS A187050, https://oeis.org/A187050.
-/
namespace OMA.BishopTours
open OMA.S_oeis_a187050

abbrev Span := ℕ × ℕ
abbrev Entry := Span × ℕ

private def insertSpan (s : Span) : List Entry → List Entry
  | [] => [(s,1)]
  | (p,k)::rest =>
    if p=s then (p,k+1)::rest
    else if 11*s.1+s.2 < 11*p.1+p.2 then (s,1)::(p,k)::rest
    else (p,k)::insertSpan s rest

private def value (f : Span → ℕ) (entries : List Entry) :=
  (entries.map (fun e => e.2*f e.1)).sum

private theorem value_insert (f : Span → ℕ) (s : Span) (xs : List Entry) :
    value f (insertSpan s xs) = f s + value f xs := by
  induction xs with
  | nil => simp [value,insertSpan]
  | cons e xs ih =>
    obtain ⟨p,k⟩ := e
    by_cases h : p=s
    · subst p
      simp [insertSpan,value,add_mul]
      omega
    · by_cases order : 11*s.1+s.2 < 11*p.1+p.2
      · simp [insertSpan,h,order,value]
      · simp only [insertSpan,if_neg h,if_neg order,value,List.map_cons,List.sum_cons] at *
        omega

private theorem value_fold (f : Span → ℕ) (xs : List Span) (entries : List Entry) :
    value f (xs.foldl (fun a s => insertSpan s a) entries) =
      (xs.map f).sum + value f entries := by
  induction xs generalizing entries with
  | nil => simp
  | cons s xs ih =>
    rw [List.foldl_cons,ih,value_insert]
    simp [add_assoc,add_left_comm,add_comm]

private def tally (xs : List Span) : List Entry :=
  xs.foldl (fun a s => insertSpan s a) []

private theorem tally_value (f : Span → ℕ) (xs : List Span) :
    (xs.map f).sum = value f (tally xs) := by
  rw [tally,value_fold]
  simp [value]


private def shortMoves : List Entry :=
  [((1,5),2), ((2,3),12), ((2,4),60), ((2,5),54), ((2,6),46), ((2,7),22), ((2,8),8), ((2,9),2), ((3,3),68), ((3,4),210), ((3,5),200), ((3,6),138), ((3,7),80), ((3,8),26), ((3,9),2), ((4,4),138), ((4,5),232), ((4,6),172), ((4,7),98), ((4,8),46), ((4,9),10), ((5,5),84), ((5,6),112), ((5,7),76), ((5,8),34), ((5,9),6), ((6,6),33), ((6,7),38), ((6,8),22), ((6,9),6), ((7,7),12), ((7,8),12), ((7,9),2), ((8,8),5), ((8,9),2), ((9,9),1)]

private def longMoves : List Entry :=
  [((2,3),8), ((2,4),30), ((2,5),18), ((2,6),28), ((2,7),10), ((2,8),14), ((2,9),2), ((2,10),2), ((3,3),38), ((3,4),122), ((3,5),154), ((3,6),106), ((3,7),92), ((3,8),34), ((3,9),20), ((4,4),122), ((4,5),200), ((4,6),200), ((4,7),94), ((4,8),82), ((4,9),26), ((4,10),12), ((5,5),121), ((5,6),112), ((5,7),132), ((5,8),34), ((5,9),40), ((6,6),71), ((6,7),34), ((6,8),60), ((6,9),10), ((6,10),12), ((7,7),29), ((7,8),8), ((7,9),20), ((8,8),9), ((8,9),2), ((8,10),4), ((9,9),4), ((10,10),1)]

set_option maxRecDepth 30000 in
private theorem cert0 : tally (shapes 4 (-1,-1) [(-1,-1),0]) = shortMoves := by decide +kernel
set_option maxRecDepth 30000 in
private theorem cert1 : tally (shapes 4 (-1,1) [(-1,1),0]) = shortMoves := by decide +kernel
set_option maxRecDepth 30000 in
private theorem cert2 : tally (shapes 4 (1,-1) [(1,-1),0]) = shortMoves := by decide +kernel
set_option maxRecDepth 30000 in
private theorem cert3 : tally (shapes 4 (1,1) [(1,1),0]) = shortMoves := by decide +kernel
set_option maxRecDepth 30000 in
private theorem cert4 : tally (shapes 4 (-2,-2) [(-2,-2),0]) = longMoves := by decide +kernel
set_option maxRecDepth 30000 in
private theorem cert5 : tally (shapes 4 (-2,2) [(-2,2),0]) = longMoves := by decide +kernel
set_option maxRecDepth 30000 in
private theorem cert6 : tally (shapes 4 (2,-2) [(2,-2),0]) = longMoves := by decide +kernel
set_option maxRecDepth 30000 in
private theorem cert7 : tally (shapes 4 (2,2) [(2,2),0]) = longMoves := by decide +kernel


private theorem first_layer (f : Point → List Point → List Span) :
  directions.flatMap (fun d => let q := (0:Point)+d; if q ∈ [0] then [] else f q [q,0]) =
    f (-1,-1) [(-1,-1),0] ++
    f (-1,1) [(-1,1),0] ++
    f (1,-1) [(1,-1),0] ++
    f (1,1) [(1,1),0] ++
    f (-2,-2) [(-2,-2),0] ++
    f (-2,2) [(-2,2),0] ++
    f (2,-2) [(2,-2),0] ++
    f (2,2) [(2,2),0] ++ [] := by
  simp only [directions,List.flatMap_cons,List.flatMap_nil,zero_add,List.mem_singleton]
  norm_num

private theorem split_shapes : shapes 5 0 [0] =
  shapes 4 (-1,-1) [(-1,-1),0] ++
  shapes 4 (-1,1) [(-1,1),0] ++
  shapes 4 (1,-1) [(1,-1),0] ++
  shapes 4 (1,1) [(1,1),0] ++
  shapes 4 (-2,-2) [(-2,-2),0] ++
  shapes 4 (-2,2) [(-2,2),0] ++
  shapes 4 (2,-2) [(2,-2),0] ++
  shapes 4 (2,2) [(2,2),0] ++ [] := first_layer (shapes 4)

private theorem count (n : ℕ) :
    term n = 4*(value (placements n) shortMoves + value (placements n) longMoves) := by
  rw [term,split_shapes]
  simp only [List.map_append,List.sum_append,List.map_nil,List.sum_nil,add_zero]
  rw [tally_value _ (shapes 4 (-1,-1) [(-1,-1),0]),cert0]
  rw [tally_value _ (shapes 4 (-1,1) [(-1,1),0]),cert1]
  rw [tally_value _ (shapes 4 (1,-1) [(1,-1),0]),cert2]
  rw [tally_value _ (shapes 4 (1,1) [(1,1),0]),cert3]
  rw [tally_value _ (shapes 4 (-2,-2) [(-2,-2),0]),cert4]
  rw [tally_value _ (shapes 4 (-2,2) [(-2,2),0]),cert5]
  rw [tally_value _ (shapes 4 (2,-2) [(2,-2),0]),cert6]
  rw [tally_value _ (shapes 4 (2,2) [(2,2),0]),cert7]
  ring

private theorem quadratic (n : ℕ) (hn : 10 ≤ n) :
    (term n : ℤ) = 16752*(n:ℤ)^2-163720*n+397436 := by
  rw [count]
  simp only [value,shortMoves,longMoves,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,placements]
  simp (disch := omega) only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub,Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero]
  ring

private theorem recur_shift (k : ℕ) (hk : 9 ≤ k) :
    (term (k+3+1):ℤ) + 3*term (k+1+1) = 3*term (k+2+1) + term (k+1) := by
  rw [quadratic _ (by omega),quadratic _ (by omega),quadratic _ (by omega),quadratic _ (by omega)]
  push_cast
  ring

private theorem smallValues (n : Fin 12) : term (n.val+1) = (![0,0,0,584,6952,29500,79088,162320,281320,435436,623508,845084] : Fin 12 → ℕ) n := by
  rw [count]
  revert n
  decide +kernel


open PowerSeries in
private theorem series_of_recurrence (a : ℕ → ℕ)
    (initial : ∀ n : Fin 12, a n.val = (![0,0,0,584,6952,29500,79088,162320,281320,435436,623508,845084] : Fin 12 → ℕ) n)
    (rec : ∀ n ≥ 9, (a (n+3):ℤ) + 3*a (n+1) = 3*a (n+2) + a n) :
    PowerSeries.mk (fun k => (a k : ℤ)) * (1-X)^3 = 4*X^3*(146+1300*X+2599*X^2+2715*X^3+1651*X^4+531*X^5-163*X^6-290*X^7-113*X^8) := by
  let F := PowerSeries.mk (fun n => (a n:ℤ))
  change F*_ = _
  have left : F*(1-X)^3 = F-(3:ℤ) • (F*X^1)+(3:ℤ) • (F*X^2)-F*X^3 := by
    simp only [zsmul_eq_mul,Int.cast_ofNat]; ring
  have right : (4*X^3*(146+1300*X+2599*X^2+2715*X^3+1651*X^4+531*X^5-163*X^6-290*X^7-113*X^8) : PowerSeries ℤ) = (584:ℤ) • X^3 + (5200:ℤ) • X^4 + (10396:ℤ) • X^5 + (10860:ℤ) • X^6 + (6604:ℤ) • X^7 + (2124:ℤ) • X^8 - (652:ℤ) • X^9 - (1160:ℤ) • X^10 - (452:ℤ) • X^11 := by
    simp only [zsmul_eq_mul,Int.cast_ofNat]; ring
  rw [left,right]
  apply PowerSeries.ext
  intro n
  simp only [map_add,map_sub,map_zsmul]
  simp only [coeff_X_pow,coeff_mul_X_pow',F,coeff_mk,zsmul_eq_mul,Int.cast_id]
  by_cases hn : n ≤ 11
  · have h0 : a 0 = 0 := initial 0
    have h1 : a 1 = 0 := initial 1
    have h2 : a 2 = 0 := initial 2
    have h3 : a 3 = 584 := initial 3
    have h4 : a 4 = 6952 := initial 4
    have h5 : a 5 = 29500 := initial 5
    have h6 : a 6 = 79088 := initial 6
    have h7 : a 7 = 162320 := initial 7
    have h8 : a 8 = 281320 := initial 8
    have h9 : a 9 = 435436 := initial 9
    have h10 : a 10 = 623508 := initial 10
    have h11 : a 11 = 845084 := initial 11
    interval_cases n <;> norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  · have h := rec (n-3) (by omega)
    rw [show n-3+3=n by omega,show n-3+1=n-2 by omega,show n-3+2=n-1 by omega] at h
    simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega),
      if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 5 by omega), if_neg (show n ≠ 6 by omega), if_neg (show n ≠ 7 by omega), if_neg (show n ≠ 8 by omega), if_neg (show n ≠ 9 by omega), if_neg (show n ≠ 10 by omega), if_neg (show n ≠ 11 by omega),
      mul_zero,add_zero,sub_zero]
    linarith only [h]

theorem result : type_of% @OMA.S_oeis_a187050.main := by
  refine ⟨series_of_recurrence (fun k => term (k+1)) smallValues recur_shift,?_⟩
  intro n hn
  have e := recur_shift (n-4) (by omega)
  rw [show n-4+3+1=n by omega,show n-4+2+1=n-1 by omega,
    show n-4+1+1=n-2 by omega,show n-4+1=n-3 by omega] at e
  linarith only [e]

end OMA.BishopTours

theorem OMA.solution : type_of% @OMA.S_oeis_a187050.main := OMA.BishopTours.result
