import OMAStatements.S_oeis_a202808
import Mathlib

namespace OMA.Array202808

open OMA.S_oeis_a202808
open Matrix PowerSeries
open scoped PowerSeries

private def transition : Matrix Row Row ℤ := fun i j => if follows i j then 1 else 0

private def v (n : ℕ) (r : Row) : ℤ := (gridFrom n r).card

private theorem step (n : ℕ) : v (n+1) = transition *ᵥ v n := by
  funext r
  change ((gridFrom (n+1) r).card : ℤ) = _
  rw [gridFrom, Finset.card_map,Finset.card_sigma,Nat.cast_sum,Finset.sum_filter]
  simp only [Matrix.mulVec,dotProduct,transition,ite_mul,one_mul,zero_mul,v]

private theorem value (n : ℕ) : a (n+1) = v n 0 := rfl

private def initial : Fin 14 → Row → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![10, 14, 14, 14, 17, 14, 14, 14, 10, 9, 12, 11, 11, 12, 9, 8, 7, 4, 6, 7, 6, 5, 5, 3, 3, 2, 1],
    ![121, 169, 157, 154, 168, 115, 117, 95, 50, 81, 99, 77, 79, 71, 40, 37, 25, 10, 32, 31, 20, 18, 14, 6, 6, 3, 1],
    ![1177, 1445, 1151, 1174, 1088, 609, 635, 426, 175, 525, 543, 349, 373, 281, 125, 119, 65, 20, 121, 98, 50, 47, 30, 10, 10, 4, 1],
    ![8232, 8818, 6024, 6388, 5134, 2404, 2555, 1460, 490, 2456, 2201, 1194, 1319, 859, 315, 305, 140, 35, 356, 249, 105, 101, 55, 15, 15, 5, 1],
    ![43483, 41417, 24665, 26981, 19242, 7727, 8324, 4149, 1176, 9040, 7199, 3373, 3819, 2199, 686, 671, 266, 56, 881, 545, 196, 191, 91, 21, 21, 6, 1],
    ![185051, 159561, 84181, 94341, 60735, 21347, 23215, 10274, 2520, 27918, 20117, 8295, 9566, 4949, 1344, 1323, 462, 84, 1925, 1071, 336, 330, 140, 28, 28, 7, 1],
    ![666610, 527495, 249875, 285406, 167949, 52503, 57483, 22896, 4950, 75494, 49858, 18362, 21474, 10102, 2430, 2402, 750, 120, 3830, 1940, 540, 533, 204, 36, 36, 8, 1],
    ![2105474, 1544667, 664192, 770232, 418206, 117768, 129570, 46947, 9075, 183995, 112425, 37419, 44241, 19101, 4125, 4089, 1155, 165, 7083, 3297, 825, 817, 285, 45, 45, 9, 1],
    ![5980085, 4099143, 1614274, 1895190, 956428, 245113, 270655, 89980, 15730, 412467, 234862, 71323, 85063, 33958, 6655, 6610, 1705, 220, 12352, 5323, 1210, 1201, 385, 55, 55, 10, 1],
    ![15560519, 10026131, 3642926, 4320525, 2038553, 479468, 530882, 163097, 26026, 863159, 460647, 128645, 154517, 57387, 10296, 10241, 2431, 286, 20526, 8239, 1716, 1706, 506, 66, 66, 11, 1],
    ![37618385, 22894702, 7722925, 9237592, 4094883, 890110, 987636, 282074, 41405, 1705067, 856857, 221519, 267631, 92951, 15379, 15313, 3367, 364, 32759, 12310, 2366, 2355, 650, 78, 78, 12, 1],
    ![85418437, 49299016, 15520805, 18699057, 7819565, 1580241, 1756274, 468702, 63700, 3206762, 1523457, 366652, 445159, 145223, 22295, 22217, 4550, 455, 50518, 17849, 3185, 3173, 819, 91, 91, 13, 1],
    ![183739050, 100899280, 29783625, 36104849, 14293579, 2699152, 3003755, 752363, 95200, 5781010, 2605097, 586509, 715079, 219961, 31500, 31409, 6020, 560, 75635, 25221, 4200, 4187, 1015, 105, 105, 14, 1]]

private theorem initial_step :
    ∀ k : Fin 13, ∀ i : Row,
      initial k.succ i = (transition *ᵥ initial k.castSucc) i := by
  decide +kernel

private theorem initial_eq (k : Fin 14) : v k.val = initial k := by
  induction k using Fin.induction with
  | zero =>
    funext i
    simp only [v, gridFrom,Finset.card_singleton,Nat.cast_one]
    fin_cases i <;> rfl
  | succ k ih =>
    rw [Fin.val_succ, step]
    change transition *ᵥ v k.castSucc.val = initial k.succ
    conv_lhs => rw [ih]
    exact funext fun i => (initial_step k i).symm

private theorem differences (n : ℕ) :
    v (n+13) = (13:ℕ) • v (n+12) - (78:ℕ) • v (n+11) + (286:ℕ) • v (n+10) - (715:ℕ) • v (n+9) + (1287:ℕ) • v (n+8) - (1716:ℕ) • v (n+7) + (1716:ℕ) • v (n+6) - (1287:ℕ) • v (n+5) + (715:ℕ) • v (n+4) - (286:ℕ) • v (n+3) + (78:ℕ) • v (n+2) - (13:ℕ) • v (n+1) + v n := by
  induction n with
  | zero =>
    have e0 : v 0 = initial 0 := initial_eq 0
    have e1 : v 1 = initial 1 := initial_eq 1
    have e2 : v 2 = initial 2 := initial_eq 2
    have e3 : v 3 = initial 3 := initial_eq 3
    have e4 : v 4 = initial 4 := initial_eq 4
    have e5 : v 5 = initial 5 := initial_eq 5
    have e6 : v 6 = initial 6 := initial_eq 6
    have e7 : v 7 = initial 7 := initial_eq 7
    have e8 : v 8 = initial 8 := initial_eq 8
    have e9 : v 9 = initial 9 := initial_eq 9
    have e10 : v 10 = initial 10 := initial_eq 10
    have e11 : v 11 = initial 11 := initial_eq 11
    have e12 : v 12 = initial 12 := initial_eq 12
    have e13 : v 13 = initial 13 := initial_eq 13
    simp only [Nat.zero_add,e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11,e12,e13]
    exact funext ((by decide +kernel) : ∀ i : Row, _)
  | succ n ih =>
    apply Eq.trans (step (n+13))
    conv_lhs => rw [ih]
    simp only [mulVec_add, mulVec_sub, mulVec_smul, ← step]

private theorem recurrence (n : ℕ) (hn : 13 < n) :
    a n = 13*a (n-1) - 78*a (n-2) + 286*a (n-3) - 715*a (n-4) + 1287*a (n-5) - 1716*a (n-6) + 1716*a (n-7) - 1287*a (n-8) + 715*a (n-9) - 286*a (n-10) + 78*a (n-11) - 13*a (n-12) + a (n-13) := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+14 := ⟨n-14,by omega⟩
  simpa [value,nsmul_eq_mul] using congrFun (differences m) 0

private theorem generating : (((1-X)^13 : ℤ⟦X⟧) * mk a = X * (1 - 3*X + 69*X^2 + 98*X^3 + 224*X^4 - 470*X^5 + 607*X^6 - 459*X^7 + 228*X^8 - 71*X^9 + 13*X^10 - X^11)) := by
  let S := mk a
  change _ * S = _
  have lhs : (1-X)^13 * S = S - (13:ℕ) • (S*X^1) + (78:ℕ) • (S*X^2) - (286:ℕ) • (S*X^3) + (715:ℕ) • (S*X^4) - (1287:ℕ) • (S*X^5) + (1716:ℕ) • (S*X^6) - (1716:ℕ) • (S*X^7) + (1287:ℕ) • (S*X^8) - (715:ℕ) • (S*X^9) + (286:ℕ) • (S*X^10) - (78:ℕ) • (S*X^11) + (13:ℕ) • (S*X^12) - (S*X^13) := by simp only [nsmul_eq_mul]; ring
  have rhs : (X * (1 - 3*X + 69*X^2 + 98*X^3 + 224*X^4 - 470*X^5 + 607*X^6 - 459*X^7 + 228*X^8 - 71*X^9 + 13*X^10 - X^11) : ℤ⟦X⟧) = X^1 - (3:ℕ) • X^2 + (69:ℕ) • X^3 + (98:ℕ) • X^4 + (224:ℕ) • X^5 - (470:ℕ) • X^6 + (607:ℕ) • X^7 - (459:ℕ) • X^8 + (228:ℕ) • X^9 - (71:ℕ) • X^10 + (13:ℕ) • X^11 - X^12 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases hn : 13 < n
  · have h := recurrence n hn
    simp only [nsmul_eq_mul,if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),
      if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega),
      if_pos (show 6 ≤ n by omega),
      if_pos (show 7 ≤ n by omega),
      if_pos (show 8 ≤ n by omega),
      if_pos (show 9 ≤ n by omega),
      if_pos (show 10 ≤ n by omega),
      if_pos (show 11 ≤ n by omega),
      if_pos (show 12 ≤ n by omega),
      if_pos (show 13 ≤ n by omega),
      if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega),
      if_neg (show n ≠ 6 by omega),
      if_neg (show n ≠ 7 by omega),
      if_neg (show n ≠ 8 by omega),
      if_neg (show n ≠ 9 by omega),
      if_neg (show n ≠ 10 by omega),
      if_neg (show n ≠ 11 by omega),
      if_neg (show n ≠ 12 by omega)]
    omega
  · have e0 : a 0 = 0 := rfl
    have e1 : a 1 = 1 := (value 0).trans (congrFun (initial_eq 0) 0)
    have e2 : a 2 = 10 := (value 1).trans (congrFun (initial_eq 1) 0)
    have e3 : a 3 = 121 := (value 2).trans (congrFun (initial_eq 2) 0)
    have e4 : a 4 = 1177 := (value 3).trans (congrFun (initial_eq 3) 0)
    have e5 : a 5 = 8232 := (value 4).trans (congrFun (initial_eq 4) 0)
    have e6 : a 6 = 43483 := (value 5).trans (congrFun (initial_eq 5) 0)
    have e7 : a 7 = 185051 := (value 6).trans (congrFun (initial_eq 6) 0)
    have e8 : a 8 = 666610 := (value 7).trans (congrFun (initial_eq 7) 0)
    have e9 : a 9 = 2105474 := (value 8).trans (congrFun (initial_eq 8) 0)
    have e10 : a 10 = 5980085 := (value 9).trans (congrFun (initial_eq 9) 0)
    have e11 : a 11 = 15560519 := (value 10).trans (congrFun (initial_eq 10) 0)
    have e12 : a 12 = 37618385 := (value 11).trans (congrFun (initial_eq 11) 0)
    have e13 : a 13 = 85418437 := (value 12).trans (congrFun (initial_eq 12) 0)
    interval_cases n <;> norm_num [e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11,e12,e13]

theorem result : type_of% @OMA.S_oeis_a202808.main := ⟨recurrence, generating⟩

end OMA.Array202808

theorem OMA.solution : type_of% @OMA.S_oeis_a202808.main := OMA.Array202808.result
