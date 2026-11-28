import OMAStatements.S_arxiv_2608_20875
import Mathlib

namespace OMA.P_arxiv_2608_20875

open OMA.S_arxiv_2608_20875

def A_int (i j : Fin 7) : ℤ :=
  match i.val with
  | 0 => match j.val with | 0 => 2637574 | 1 => -2056325 | 2 => -1288538 | 3 => -396406 | 4 => -288502 | 5 => -8085 | 6 => -1279879 | _ => 0
  | 1 => match j.val with | 0 => 0 | 1 => 1866224 | 2 => -1923472 | 3 => -740431 | 4 => 60623 | 5 => 258085 | 6 => 90208 | _ => 0
  | 2 => match j.val with | 0 => 0 | 1 => 0 | 2 => -1032491 | 3 => 1618361 | 4 => -174526 | 5 => 659957 | 6 => -2543788 | _ => 0
  | 3 => match j.val with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => -2508534 | 4 => 1630470 | 5 => -174725 | 6 => 2331754 | _ => 0
  | 4 => match j.val with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => -5000000 | 4 => -2508534 | 5 => -2528099 | 6 => -703944 | _ => 0
  | 5 => match j.val with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => -2563746 | 6 => -4534252 | _ => 0
  | 6 => match j.val with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 1733590 | 6 => -2563746 | _ => 0
  | _ => 0

def K_int (i j : Fin 7) : ℤ :=
  match i.val with
  | 0 => match j.val with | 0 => 0 | 1 => -41 | 2 => 98 | 3 => 747 | 4 => -270 | 5 => 472 | 6 => -156 | _ => 0
  | 1 => match j.val with | 0 => 41 | 1 => 0 | 2 => -94 | 3 => 437 | 4 => 239 | 5 => 164 | 6 => -378 | _ => 0
  | 2 => match j.val with | 0 => -98 | 1 => 94 | 2 => 0 | 3 => 3098 | 4 => 1426 | 5 => 2050 | 6 => 1996 | _ => 0
  | 3 => match j.val with | 0 => -747 | 1 => -437 | 2 => -3098 | 3 => 0 | 4 => -3244 | 5 => -8398 | 6 => -10000 | _ => 0
  | 4 => match j.val with | 0 => 270 | 1 => -239 | 2 => -1426 | 3 => 3244 | 4 => 0 | 5 => 128 | 6 => -9241 | _ => 0
  | 5 => match j.val with | 0 => -472 | 1 => -164 | 2 => -2050 | 3 => 8398 | 4 => -128 | 5 => 0 | 6 => -5795 | _ => 0
  | 6 => match j.val with | 0 => 156 | 1 => 378 | 2 => -1996 | 3 => 10000 | 4 => 9241 | 5 => 5795 | 6 => 0 | _ => 0
  | _ => 0

def t_sep : ℤ := 130550654419869
def S_scale : ℤ := 1000

def symPair (k : Fin 28) : Fin 7 × Fin 7 :=
  match k.val with
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 3)
  | 4 => (0, 4)
  | 5 => (0, 5)
  | 6 => (0, 6)
  | 7 => (1, 1)
  | 8 => (1, 2)
  | 9 => (1, 3)
  | 10 => (1, 4)
  | 11 => (1, 5)
  | 12 => (1, 6)
  | 13 => (2, 2)
  | 14 => (2, 3)
  | 15 => (2, 4)
  | 16 => (2, 5)
  | 17 => (2, 6)
  | 18 => (3, 3)
  | 19 => (3, 4)
  | 20 => (3, 5)
  | 21 => (3, 6)
  | 22 => (4, 4)
  | 23 => (4, 5)
  | 24 => (4, 6)
  | 25 => (5, 5)
  | 26 => (5, 6)
  | 27 => (6, 6)
  | _ => (0, 0)

def W_int (k : Fin 28) : ℤ :=
  let pq := symPair k
  if pq.1 = pq.2 then 1 else 2

/-- Entry `(i, j)` of the `k`-th basis matrix `B_k` of `Sym_7`
(`E_{pp}` if `p = q`, or `E_{pq} + E_{qp}` if `p < q`). -/
def B_int (k : Fin 28) (i j : Fin 7) : ℤ :=
  let pq := symPair k
  if pq.1 = pq.2 then
    if i = pq.1 ∧ j = pq.1 then 1 else 0
  else
    if (i = pq.1 ∧ j = pq.2) ∨ (i = pq.2 ∧ j = pq.1) then 1 else 0

/-- Exact integer entry `(i, j)` of `L_{A_int}(B_k) = A_int * B_k + B_k * A_intᵀ`. -/
def L_int (k : Fin 28) (i j : Fin 7) : ℤ :=
  let pq := symPair k
  if pq.1 = pq.2 then
    (if j = pq.1 then A_int i pq.1 else 0) + (if i = pq.1 then A_int j pq.1 else 0)
  else
    (if j = pq.2 then A_int i pq.1 else 0) + (if j = pq.1 then A_int i pq.2 else 0) +
    (if i = pq.1 then A_int j pq.2 else 0) + (if i = pq.2 then A_int j pq.1 else 0)

def G_int (a b : Fin 28) : ℤ :=
  ∑ i : Fin 7, ∑ j : Fin 7, L_int a i j * L_int b i j

def M_int (a b : Fin 28) : ℤ :=
  (if a = b then t_sep * W_int a else 0) - G_int a b

def R_int (i j : Fin 28) : ℤ :=
  match i.val with
  | 0 => match j.val with | 0 => 10135258620 | 1 => 2140531212 | 2 => 1341303445 | 3 => 412638769 | 4 => 300316115 | 5 => 8416080 | 6 => 1332289861 | _ => 0
  | 1 => match j.val with | 1 => 14108052714 | 2 => 273329372 | 3 => 179023918 | 4 => -252474178 | 5 => -170770686 | 6 => -1005932872 | 7 => 1312905843 | 8 => 822695376 | 9 => 253094114 | 10 => 184200436 | 11 => 5162046 | 12 => 817166848 | _ => 0
  | 2 => match j.val with | 2 => 15493034293 | 3 => -689932451 | 4 => -66308436 | 5 => -73066137 | 6 => 26093145 | 7 => -533751020 | 8 => 91611768 | 9 => -102893320 | 10 => -74885165 | 11 => -2098587 | 12 => -332212428 | 13 => 266985847 | 14 => 82135561 | 15 => 59777787 | 16 => 1675217 | 17 => 265191697 | _ => 0
  | 3 => match j.val with | 3 => 14262765045 | 4 => 66070467 | 5 => -1894859601 | 6 => -116048441 | 7 => -255800838 | 8 => 326972307 | 9 => -12103233 | 10 => -1477632393 | 11 => -1005750 | 12 => -159213218 | 13 => 305329400 | 14 => 117247244 | 15 => -835065049 | 16 => 1915806 | 17 => 303277580 | 18 => 7172835 | 19 => -272710333 | 20 => 146295 | 21 => 23158986 | 22 => -202276346 | 23 => -5668606 | 24 => -897356856 | _ => 0
  | 4 => match j.val with | 4 => 15974581152 | 5 => 93064324 | 6 => -653698572 | 7 => 35199965 | 8 => -23121327 | 9 => 426395642 | 10 => 44122864 | 11 => 138398 | 12 => 21908840 | 13 => -28309763 | 14 => 254227542 | 15 => 18215225 | 16 => -177631 | 17 => -28119521 | 18 => 80889900 | 19 => 66424920 | 20 => 1649811 | 21 => 261169821 | 22 => 5497552 | 23 => 154064 | 24 => 24388743 | _ => 0
  | 5 => match j.val with | 5 => 15414208444 | 6 => 38831946 | 7 => 49216763 | 8 => 269114122 | 9 => -35089898 | 10 => -845083810 | 11 => 19891486 | 12 => 493170514 | 13 => 149307566 | 14 => 17999699 | 15 => -500445024 | 16 => 13280019 | 17 => 438140259 | 18 => -8593404 | 19 => -170495543 | 20 => 3621989 | 21 => 61419610 | 22 => -119533880 | 23 => -586203 | 24 => -465393230 | 25 => 77448 | 26 => 14078826 | 27 => 287888339 | _ => 0
  | 6 => match j.val with | 6 => 13614920897 | 7 => 124644868 | 8 => -689807235 | 9 => 748970847 | 10 => -203129736 | 11 => -1369224559 | 12 => 98562262 | 13 => -481190637 | 14 => 306231234 | 15 => -245981620 | 16 => -861312257 | 17 => -464809285 | 18 => 139750078 | 19 => 59180004 | 20 => -261195063 | 21 => 455256890 | 22 => -30952577 | 23 => -193038116 | 24 => -134370894 | 25 => -5385405 | 26 => -852442760 | 27 => 13059389 | _ => 0
  | 7 => match j.val with | 7 => 10298994950 | 8 => 794755085 | 9 => 330131207 | 10 => -216864012 | 11 => -174609289 | 12 => -705440210 | 13 => 26627209 | 14 => 2507725 | 15 => -12336585 | 16 => 10495686 | 17 => 24904085 | 18 => -1748588 | 19 => -6901929 | 20 => 3141832 | 21 => -6120732 | 22 => -4096984 | 23 => 2197749 | 24 => -18521159 | 25 => 64807 | 26 => 10249515 | 27 => -1533812 | _ => 0
  | 8 => match j.val with | 8 => 15204010827 | 9 => -614192218 | 10 => 40324434 | 11 => 3261022 | 12 => 101553917 | 13 => -171678461 | 14 => -15207514 | 15 => -68719045 | 16 => -70404942 | 17 => -394405964 | 18 => 6552737 | 19 => 12029422 | 20 => -12079421 | 21 => 19786972 | 22 => 5284061 | 23 => -8740520 | 24 => 22444630 | 25 => -249095 | 26 => -39460367 | 27 => -4423001 | _ => 0
  | 9 => match j.val with | 9 => 13884120994 | 10 => -265413346 | 11 => -1858188602 | 12 => 246933550 | 13 => 469628919 | 14 => -411339920 | 15 => -1391094507 | 16 => -17013785 | 17 => -9794705 | 18 => -195635307 | 19 => -618346963 | 20 => 34923850 | 21 => -402152792 | 22 => 45017167 | 23 => 195848275 | 24 => 70946431 | 25 => 278148 | 26 => 44030794 | 27 => -136079 | _ => 0
  | 10 => match j.val with | 10 => 15593616560 | 11 => -212258305 | 12 => -655567562 | 13 => -2129613 | 14 => 394485624 | 15 => -629829887 | 16 => -4494575 | 17 => 50999952 | 18 => 153273512 | 19 => -223373278 | 20 => -56498389 | 21 => -15131001 | 22 => -96463820 | 23 => 19431676 | 24 => -441304525 | 25 => -59676 | 26 => -9347309 | 27 => 15759791 | _ => 0
  | 11 => match j.val with | 11 => 15042464029 | 12 => -205516719 | 13 => 183166615 | 14 => 2939512 | 15 => -854485767 | 16 => -633764458 | 17 => 392484777 | 18 => -26494850 | 19 => -321496854 | 20 => -191274591 | 21 => 164150261 | 22 => 21855256 | 23 => 20418602 | 24 => 6989569 | 25 => 21268464 | 26 => -473219758 | 27 => -19795545 | _ => 0
  | 12 => match j.val with | 12 => 13429032184 | 13 => -723625418 | 14 => 414665430 | 15 => -185328070 | 16 => -1203751520 | 17 => -549765652 | 18 => 266905725 | 19 => -101101319 | 20 => -593919755 | 21 => -226695480 | 22 => 3107912 | 23 => 67207808 | 24 => -89083780 | 25 => 174641900 | 26 => 83319401 | 27 => -392839284 | _ => 0
  | 13 => match j.val with | 13 => 10692954943 | 14 => 317854938 | 15 => -34816332 | 16 => 235740215 | 17 => -1350770765 | 18 => 33666658 | 19 => 38995300 | 20 => -50467124 | 21 => 19498665 | 22 => 4001236 | 23 => -13061487 | 24 => 17193859 | 25 => 11194420 | 26 => -27407289 | 27 => -29735792 | _ => 0
  | 14 => match j.val with | 14 => 12753001629 | 15 => -1798320653 | 16 => -2331360901 | 17 => 2020726416 | 18 => 569683089 | 19 => 1121446094 | 20 => 472412622 | 21 => -1666117501 | 22 => -129951703 | 23 => 526017298 | 24 => -1964575044 | 25 => -5822699 | 26 => 20192681 | 27 => 12302141 | _ => 0
  | 15 => match j.val with | 15 => 14571971949 | 16 => -1516162536 | 17 => -752089030 | 18 => -299581822 | 19 => 589162629 | 20 => -111717007 | 21 => 342265421 | 22 => -150621531 | 23 => 470275555 | 24 => -1763873860 | 25 => 2711053 | 26 => -34547174 | 27 => 6043604 | _ => 0
  | 16 => match j.val with | 16 => 13906755316 | 17 => -949124961 | 18 => 133341081 | 19 => 815290565 | 20 => 566835320 | 21 => -694127690 | 22 => -102184628 | 23 => 247658516 | 24 => -1418370185 | 25 => 426100429 | 26 => -1759625396 | 27 => 603044786 | _ => 0
  | 17 => match j.val with | 17 => 11566964184 | 18 => -737690647 | 19 => 204328753 | 20 => 921031175 | 21 => 1956043674 | 22 => -7591860 | 23 => -104328338 | 24 => -313958484 | 25 => 562222259 | 26 => -1669349146 | 27 => -1821250688 | _ => 0
  | 18 => match j.val with | 18 => 6898797444 | 19 => -4912095738 | 20 => -4100154646 | 21 => 3797855508 | 22 => 2372747260 | 23 => -285639902 | 24 => 3477387209 | 25 => 45870454 | 26 => -133786583 | 27 => -192144694 | _ => 0
  | 19 => match j.val with | 19 => 8132845686 | 20 => -5580140665 | 21 => -451317384 | 22 => -2639983804 | 23 => -6932010233 | 24 => 4652070665 | 25 => -25510065 | 26 => 129367257 | 27 => -132037970 | _ => 0
  | 20 => match j.val with | 20 => 9124547348 | 21 => -1594680942 | 22 => 366293056 | 23 => -8191751681 | 24 => 298564779 | 25 => -3223990864 | 26 => 2959115449 | 27 => -933103425 | _ => 0
  | 21 => match j.val with | 21 => 6929040087 | 22 => -1083265231 | 23 => 2603491437 | 24 => -6355956156 | 25 => -1109475720 | 26 => 30183909 | 27 => 3902504879 | _ => 0
  | 22 => match j.val with | 22 => 9262983200 | 23 => -3914061502 | 24 => -2183344324 | 25 => -16288681 | 26 => -65253203 | 27 => 514413831 | _ => 0
  | 23 => match j.val with | 23 => 5784796987 | 24 => 2491946155 | 25 => -8416820289 | 26 => 2981198268 | 27 => -2530735729 | _ => 0
  | 24 => match j.val with | 24 => 6193194836 | 25 => -1183348074 | 26 => -6912398582 | 27 => 2880466729 | _ => 0
  | 25 => match j.val with | 25 => 26416304 | 26 => -25389432 | 27 => 23101012 | _ => 0
  | 26 => match j.val with | 26 => 2327739 | 27 => -753540 | _ => 0
  | 27 => match j.val with | 27 => 5211965 | _ => 0
  | _ => 0

def E_int (a b : Fin 28) : ℤ :=
  S_scale * S_scale * M_int a b - ∑ k : Fin 28, R_int k a * R_int k b

def lyap_int (A X : Fin 7 → Fin 7 → ℤ) (i j : Fin 7) : ℤ :=
  (∑ m : Fin 7, A i m * X m j) + (∑ m : Fin 7, X i m * A j m)

def frobSq_int (X : Fin 7 → Fin 7 → ℤ) : ℤ :=
  ∑ i : Fin 7, ∑ j : Fin 7, X i j * X i j

def A_real : Matrix (Fin 7) (Fin 7) ℝ := Matrix.of fun i j => (A_int i j : ℝ)
def K_real : Matrix (Fin 7) (Fin 7) ℝ := Matrix.of fun i j => (K_int i j : ℝ)

private lemma K_frob_pos : 0 < frobSq_int K_int := by decide

private lemma K_beats_sep : t_sep * frobSq_int K_int < frobSq_int (lyap_int A_int K_int) := by
  decide

private lemma lyap_B_eq_L (k : Fin 28) (i j : Fin 7) :
    lyap_int A_int (B_int k) i j = L_int k i j := by
  revert k i j
  decide

private lemma B_symm_basis (S : Matrix (Fin 7) (Fin 7) ℝ) (hS : S.transpose = S) (i j : Fin 7) :
    S i j = ∑ k : Fin 28, S (symPair k).1 (symPair k).2 * (B_int k i j : ℝ) := by
  have huniq : ∀ i j : Fin 7, ∃ k : Fin 28,
      (∀ k' : Fin 28, B_int k' i j = if k' = k then 1 else 0) ∧
      ((symPair k = (i, j)) ∨ (symPair k = (j, i))) := by
    decide
  obtain ⟨k, hk, hpair⟩ := huniq i j
  rw [Finset.sum_eq_single k]
  · rw [hk k, if_pos rfl, Int.cast_one, mul_one]
    rcases hpair with h1 | h2
    · rw [h1]
    · rw [h2]; exact congrFun (congrFun hS j) i
  · intro k' _ hne; rw [hk k', if_neg hne, Int.cast_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

private lemma B_orth (a b : Fin 28) :
    (∑ i : Fin 7, ∑ j : Fin 7, B_int a i j * B_int b i j) = if a = b then W_int a else 0 := by
  revert a b
  decide

private lemma lyap_sym_expand (S : Matrix (Fin 7) (Fin 7) ℝ) (hS : S.transpose = S) (i j : Fin 7) :
    lyap A_real S i j =
      ∑ k : Fin 28, S (symPair k).1 (symPair k).2 * (L_int k i j : ℝ) := by
  let s : Fin 28 → ℝ := fun k => S (symPair k).1 (symPair k).2
  change (∑ m : Fin 7, A_real i m * S m j) + (∑ m : Fin 7, S i m * A_real j m) =
    ∑ k : Fin 28, s k * (L_int k i j : ℝ)
  have h1 : (∑ m : Fin 7, A_real i m * S m j) =
      ∑ k : Fin 28, s k * (∑ m : Fin 7, (A_int i m : ℝ) * (B_int k m j : ℝ)) := by
    trans ∑ m : Fin 7, ∑ k : Fin 28, A_real i m * (s k * (B_int k m j : ℝ))
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [B_symm_basis S hS m j, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    change (A_int i m : ℝ) * (s k * (B_int k m j : ℝ)) = s k * ((A_int i m : ℝ) * (B_int k m j : ℝ))
    ring
  have h2 : (∑ m : Fin 7, S i m * A_real j m) =
      ∑ k : Fin 28, s k * (∑ m : Fin 7, (B_int k i m : ℝ) * (A_int j m : ℝ)) := by
    trans ∑ m : Fin 7, ∑ k : Fin 28, s k * (B_int k i m : ℝ) * A_real j m
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [B_symm_basis S hS i m, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    change s k * (B_int k i m : ℝ) * (A_int j m : ℝ) = s k * ((B_int k i m : ℝ) * (A_int j m : ℝ))
    ring
  rw [h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_add]
  congr 1
  have hL := lyap_B_eq_L k i j
  have hL' : ((lyap_int A_int (B_int k) i j : ℤ) : ℝ) = (L_int k i j : ℝ) := by exact_mod_cast hL
  rw [← hL']
  unfold lyap_int
  push_cast
  rfl

private lemma sum_7_7_28_28 (f : Fin 7 → Fin 7 → Fin 28 → Fin 28 → ℝ) :
    (∑ i : Fin 7, ∑ j : Fin 7, ∑ a : Fin 28, ∑ b : Fin 28, f i j a b) =
      ∑ a : Fin 28, ∑ b : Fin 28, ∑ i : Fin 7, ∑ j : Fin 7, f i j a b := by
  calc (∑ i : Fin 7, ∑ j : Fin 7, ∑ a : Fin 28, ∑ b : Fin 28, f i j a b)
      = ∑ i : Fin 7, ∑ a : Fin 28, ∑ j : Fin 7, ∑ b : Fin 28, f i j a b := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a : Fin 28, ∑ i : Fin 7, ∑ j : Fin 7, ∑ b : Fin 28, f i j a b := Finset.sum_comm
    _ = ∑ a : Fin 28, ∑ i : Fin 7, ∑ b : Fin 28, ∑ j : Fin 7, f i j a b := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a : Fin 28, ∑ b : Fin 28, ∑ i : Fin 7, ∑ j : Fin 7, f i j a b := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_comm

private lemma frobSq_sym_eq (S : Matrix (Fin 7) (Fin 7) ℝ) (hS : S.transpose = S) :
    frobSq S = ∑ a : Fin 28, (W_int a : ℝ) * (S (symPair a).1 (symPair a).2) ^ 2 := by
  let s : Fin 28 → ℝ := fun k => S (symPair k).1 (symPair k).2
  unfold frobSq
  calc ∑ i : Fin 7, ∑ j : Fin 7, (S i j) ^ 2
      = ∑ i : Fin 7, ∑ j : Fin 7,
          (∑ a : Fin 28, s a * (B_int a i j : ℝ)) * (∑ b : Fin 28, s b * (B_int b i j : ℝ)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [sq, ← B_symm_basis S hS i j]
    _ = ∑ a : Fin 28, ∑ b : Fin 28,
          s a * s b * (∑ i : Fin 7, ∑ j : Fin 7, (B_int a i j : ℝ) * (B_int b i j : ℝ)) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [sum_7_7_28_28]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ a : Fin 28, (W_int a : ℝ) * (s a) ^ 2 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_eq_single a]
        · have ho : ((∑ i : Fin 7, ∑ j : Fin 7, B_int a i j * B_int a i j : ℤ) : ℝ) =
              ((if a = a then W_int a else 0 : ℤ) : ℝ) := by exact_mod_cast B_orth a a
          simp only [↓reduceIte, Int.cast_sum, Int.cast_mul] at ho
          rw [ho]; ring
        · intro b _ hba
          have ho : ((∑ i : Fin 7, ∑ j : Fin 7, B_int a i j * B_int b i j : ℤ) : ℝ) =
              ((if a = b then W_int a else 0 : ℤ) : ℝ) := by exact_mod_cast B_orth a b
          simp only [hba.symm, ↓reduceIte, Int.cast_zero, Int.cast_sum, Int.cast_mul] at ho
          rw [ho, mul_zero]
        · intro h; exact absurd (Finset.mem_univ a) h

private lemma frobSq_lyap_sym_eq (S : Matrix (Fin 7) (Fin 7) ℝ) (hS : S.transpose = S) :
    frobSq (lyap A_real S) =
      ∑ a : Fin 28, ∑ b : Fin 28,
        (G_int a b : ℝ) * S (symPair a).1 (symPair a).2 * S (symPair b).1 (symPair b).2 := by
  let s : Fin 28 → ℝ := fun k => S (symPair k).1 (symPair k).2
  unfold frobSq
  calc ∑ i : Fin 7, ∑ j : Fin 7, (lyap A_real S i j) ^ 2
      = ∑ i : Fin 7, ∑ j : Fin 7,
          (∑ a : Fin 28, s a * (L_int a i j : ℝ)) * (∑ b : Fin 28, s b * (L_int b i j : ℝ)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [sq, ← lyap_sym_expand S hS i j]
    _ = ∑ a : Fin 28, ∑ b : Fin 28,
          (∑ i : Fin 7, ∑ j : Fin 7, (L_int a i j : ℝ) * (L_int b i j : ℝ)) * s a * s b := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [sum_7_7_28_28]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ a : Fin 28, ∑ b : Fin 28, (G_int a b : ℝ) * s a * s b := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        congr 2
        unfold G_int
        push_cast
        rfl

private lemma dd_row_0 : (∑ b ∈ Finset.univ.erase (0 : Fin 28), |E_int 0 b|) ≤ E_int 0 0 := by decide
private lemma dd_row_1 : (∑ b ∈ Finset.univ.erase (1 : Fin 28), |E_int 1 b|) ≤ E_int 1 1 := by decide
private lemma dd_row_2 : (∑ b ∈ Finset.univ.erase (2 : Fin 28), |E_int 2 b|) ≤ E_int 2 2 := by decide
private lemma dd_row_3 : (∑ b ∈ Finset.univ.erase (3 : Fin 28), |E_int 3 b|) ≤ E_int 3 3 := by decide
private lemma dd_row_4 : (∑ b ∈ Finset.univ.erase (4 : Fin 28), |E_int 4 b|) ≤ E_int 4 4 := by decide
private lemma dd_row_5 : (∑ b ∈ Finset.univ.erase (5 : Fin 28), |E_int 5 b|) ≤ E_int 5 5 := by decide
private lemma dd_row_6 : (∑ b ∈ Finset.univ.erase (6 : Fin 28), |E_int 6 b|) ≤ E_int 6 6 := by decide
private lemma dd_row_7 : (∑ b ∈ Finset.univ.erase (7 : Fin 28), |E_int 7 b|) ≤ E_int 7 7 := by decide
private lemma dd_row_8 : (∑ b ∈ Finset.univ.erase (8 : Fin 28), |E_int 8 b|) ≤ E_int 8 8 := by decide
private lemma dd_row_9 : (∑ b ∈ Finset.univ.erase (9 : Fin 28), |E_int 9 b|) ≤ E_int 9 9 := by decide
private lemma dd_row_10 : (∑ b ∈ Finset.univ.erase (10 : Fin 28), |E_int 10 b|) ≤ E_int 10 10 := by decide
private lemma dd_row_11 : (∑ b ∈ Finset.univ.erase (11 : Fin 28), |E_int 11 b|) ≤ E_int 11 11 := by decide
private lemma dd_row_12 : (∑ b ∈ Finset.univ.erase (12 : Fin 28), |E_int 12 b|) ≤ E_int 12 12 := by decide
private lemma dd_row_13 : (∑ b ∈ Finset.univ.erase (13 : Fin 28), |E_int 13 b|) ≤ E_int 13 13 := by decide
private lemma dd_row_14 : (∑ b ∈ Finset.univ.erase (14 : Fin 28), |E_int 14 b|) ≤ E_int 14 14 := by decide
private lemma dd_row_15 : (∑ b ∈ Finset.univ.erase (15 : Fin 28), |E_int 15 b|) ≤ E_int 15 15 := by decide
private lemma dd_row_16 : (∑ b ∈ Finset.univ.erase (16 : Fin 28), |E_int 16 b|) ≤ E_int 16 16 := by decide
private lemma dd_row_17 : (∑ b ∈ Finset.univ.erase (17 : Fin 28), |E_int 17 b|) ≤ E_int 17 17 := by decide
private lemma dd_row_18 : (∑ b ∈ Finset.univ.erase (18 : Fin 28), |E_int 18 b|) ≤ E_int 18 18 := by decide
private lemma dd_row_19 : (∑ b ∈ Finset.univ.erase (19 : Fin 28), |E_int 19 b|) ≤ E_int 19 19 := by decide
private lemma dd_row_20 : (∑ b ∈ Finset.univ.erase (20 : Fin 28), |E_int 20 b|) ≤ E_int 20 20 := by decide
private lemma dd_row_21 : (∑ b ∈ Finset.univ.erase (21 : Fin 28), |E_int 21 b|) ≤ E_int 21 21 := by decide
private lemma dd_row_22 : (∑ b ∈ Finset.univ.erase (22 : Fin 28), |E_int 22 b|) ≤ E_int 22 22 := by decide
private lemma dd_row_23 : (∑ b ∈ Finset.univ.erase (23 : Fin 28), |E_int 23 b|) ≤ E_int 23 23 := by decide
private lemma dd_row_24 : (∑ b ∈ Finset.univ.erase (24 : Fin 28), |E_int 24 b|) ≤ E_int 24 24 := by decide
private lemma dd_row_25 : (∑ b ∈ Finset.univ.erase (25 : Fin 28), |E_int 25 b|) ≤ E_int 25 25 := by decide
private lemma dd_row_26 : (∑ b ∈ Finset.univ.erase (26 : Fin 28), |E_int 26 b|) ≤ E_int 26 26 := by decide
private lemma dd_row_27 : (∑ b ∈ Finset.univ.erase (27 : Fin 28), |E_int 27 b|) ≤ E_int 27 27 := by decide

private lemma E_int_dd (a : Fin 28) :
    (∑ b ∈ Finset.univ.erase a, |E_int a b|) ≤ E_int a a := by
  match a with
  | ⟨0, _⟩ => exact dd_row_0
  | ⟨1, _⟩ => exact dd_row_1
  | ⟨2, _⟩ => exact dd_row_2
  | ⟨3, _⟩ => exact dd_row_3
  | ⟨4, _⟩ => exact dd_row_4
  | ⟨5, _⟩ => exact dd_row_5
  | ⟨6, _⟩ => exact dd_row_6
  | ⟨7, _⟩ => exact dd_row_7
  | ⟨8, _⟩ => exact dd_row_8
  | ⟨9, _⟩ => exact dd_row_9
  | ⟨10, _⟩ => exact dd_row_10
  | ⟨11, _⟩ => exact dd_row_11
  | ⟨12, _⟩ => exact dd_row_12
  | ⟨13, _⟩ => exact dd_row_13
  | ⟨14, _⟩ => exact dd_row_14
  | ⟨15, _⟩ => exact dd_row_15
  | ⟨16, _⟩ => exact dd_row_16
  | ⟨17, _⟩ => exact dd_row_17
  | ⟨18, _⟩ => exact dd_row_18
  | ⟨19, _⟩ => exact dd_row_19
  | ⟨20, _⟩ => exact dd_row_20
  | ⟨21, _⟩ => exact dd_row_21
  | ⟨22, _⟩ => exact dd_row_22
  | ⟨23, _⟩ => exact dd_row_23
  | ⟨24, _⟩ => exact dd_row_24
  | ⟨25, _⟩ => exact dd_row_25
  | ⟨26, _⟩ => exact dd_row_26
  | ⟨27, _⟩ => exact dd_row_27
  | ⟨_ + 28, h⟩ => exact absurd h (by omega)

private lemma E_int_symm (a b : Fin 28) : E_int a b = E_int b a := by
  unfold E_int M_int G_int
  have h1 : (if a = b then t_sep * W_int a else 0) = if b = a then t_sep * W_int b else 0 := by
    by_cases h : a = b
    · subst h; simp
    · have h' : b ≠ a := Ne.symm h; simp [h, h']
  have h2 : (∑ i : Fin 7, ∑ j : Fin 7, L_int a i j * L_int b i j) =
      ∑ i : Fin 7, ∑ j : Fin 7, L_int b i j * L_int a i j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h3 : (∑ k : Fin 28, R_int k a * R_int k b) = ∑ k : Fin 28, R_int k b * R_int k a := by
    refine Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [h1, h2, h3]

private lemma quad_E_nonneg (s : Fin 28 → ℝ) :
    0 ≤ ∑ a : Fin 28, ∑ b : Fin 28, (E_int a b : ℝ) * s a * s b := by
  -- Use `2 * (E a b) * s a * s b ≥ -|E a b| * (s a ^ 2 + s b ^ 2)` for `a ≠ b`
  have hpair : ∀ a b : Fin 28, a ≠ b →
      -(|(E_int a b : ℝ)| * ((s a) ^ 2 + (s b) ^ 2)) ≤ 2 * ((E_int a b : ℝ) * s a * s b) := by
    intro a b _
    have hsq : 0 ≤ (|s a| - |s b|) ^ 2 := sq_nonneg _
    have habs : 2 * |s a * s b| ≤ (s a) ^ 2 + (s b) ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_abs (s a), sq_abs (s b)]
    have h1 : -(|(E_int a b : ℝ)| * (2 * |s a * s b|)) ≤ 2 * ((E_int a b : ℝ) * s a * s b) := by
      have := neg_abs_le ((E_int a b : ℝ) * (s a * s b))
      rw [abs_mul] at this
      linarith
    have h2 : |(E_int a b : ℝ)| * (2 * |s a * s b|) ≤ |(E_int a b : ℝ)| * ((s a) ^ 2 + (s b) ^ 2) :=
      mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    linarith
  have h2 : 0 ≤ 2 * ∑ a : Fin 28, ∑ b : Fin 28, (E_int a b : ℝ) * s a * s b := by
    have hsplit :
        2 * ∑ a : Fin 28, ∑ b : Fin 28, (E_int a b : ℝ) * s a * s b =
          ∑ a : Fin 28, (2 * (E_int a a : ℝ) * (s a) ^ 2 +
            ∑ b ∈ Finset.univ.erase a, 2 * ((E_int a b : ℝ) * s a * s b)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), mul_add, Finset.mul_sum]
      congr 1; ring
    rw [hsplit]
    have hge :
        ∑ a : Fin 28, (2 * (E_int a a : ℝ) * (s a) ^ 2 +
          ∑ b ∈ Finset.univ.erase a, -(|(E_int a b : ℝ)| * ((s a) ^ 2 + (s b) ^ 2))) ≤
        ∑ a : Fin 28, (2 * (E_int a a : ℝ) * (s a) ^ 2 +
          ∑ b ∈ Finset.univ.erase a, 2 * ((E_int a b : ℝ) * s a * s b)) := by
      refine Finset.sum_le_sum fun a _ => add_le_add le_rfl ?_
      refine Finset.sum_le_sum fun b hb => hpair a b (Finset.ne_of_mem_erase hb).symm
    refine le_trans ?_ hge
    -- Show the lower bound equals `2 * ∑ a, (E a a - ∑_{b ≠ a} |E a b|) * (s a)^2 ≥ 0`
    have hsum_symm :
        (∑ a : Fin 28, ∑ b ∈ Finset.univ.erase a, |(E_int a b : ℝ)| * (s b) ^ 2) =
        (∑ a : Fin 28, ∑ b ∈ Finset.univ.erase a, |(E_int a b : ℝ)| * (s a) ^ 2) := by
      have hrewrite : ∀ f : Fin 28 → Fin 28 → ℝ,
          (∑ a : Fin 28, ∑ b ∈ Finset.univ.erase a, f a b) =
          ∑ a : Fin 28, ∑ b : Fin 28, if a = b then 0 else f a b := by
        intro f
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), if_pos rfl, zero_add]
        refine Finset.sum_congr rfl fun b hb => (if_neg (Finset.ne_of_mem_erase hb).symm).symm
      rw [hrewrite, hrewrite, Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases h : a = b
      · subst h; simp
      · have h' : b ≠ a := Ne.symm h
        simp only [h, h', ↓reduceIte]
        rw [E_int_symm b a]
    have hlow :
        ∑ a : Fin 28, (2 * (E_int a a : ℝ) * (s a) ^ 2 +
          ∑ b ∈ Finset.univ.erase a, -(|(E_int a b : ℝ)| * ((s a) ^ 2 + (s b) ^ 2))) =
        2 * ∑ a : Fin 28, ((E_int a a : ℝ) - ∑ b ∈ Finset.univ.erase a, |(E_int a b : ℝ)|) * (s a) ^ 2 := by
      rw [Finset.mul_sum]
      simp_rw [mul_add, neg_add, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      rw [hsum_symm]
      simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul]
      ring
    rw [hlow]
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun a _ => mul_nonneg ?_ (sq_nonneg _))
    have hdd : ((∑ b ∈ Finset.univ.erase a, |E_int a b| : ℤ) : ℝ) ≤ (E_int a a : ℝ) := by
      exact_mod_cast E_int_dd a
    simp only [Int.cast_sum, Int.cast_abs] at hdd
    linarith
  linarith

lemma sym_le_sep (S : Matrix (Fin 7) (Fin 7) ℝ) (hS : S.transpose = S) :
    frobSq (lyap A_real S) ≤ (t_sep : ℝ) * frobSq S := by
  let s : Fin 28 → ℝ := fun k => S (symPair k).1 (symPair k).2
  have hS2 : (0 : ℝ) < (S_scale : ℝ) * (S_scale : ℝ) := by norm_num [S_scale]
  suffices h : 0 ≤ (S_scale : ℝ) * (S_scale : ℝ) * ((t_sep : ℝ) * frobSq S - frobSq (lyap A_real S)) by
    have hdiff : 0 ≤ (t_sep : ℝ) * frobSq S - frobSq (lyap A_real S) :=
      nonneg_of_mul_nonneg_right h hS2
    linarith
  have hid :
      (S_scale : ℝ) * (S_scale : ℝ) * ((t_sep : ℝ) * frobSq S - frobSq (lyap A_real S)) =
        (∑ k : Fin 28, (∑ a : Fin 28, (R_int k a : ℝ) * s a) ^ 2) +
        (∑ a : Fin 28, ∑ b : Fin 28, (E_int a b : ℝ) * s a * s b) := by
    have hM : (t_sep : ℝ) * frobSq S - frobSq (lyap A_real S) =
        ∑ a : Fin 28, ∑ b : Fin 28, (M_int a b : ℝ) * s a * s b := by
      rw [frobSq_sym_eq S hS, frobSq_lyap_sym_eq S hS, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hdiag : (t_sep : ℝ) * ((W_int a : ℝ) * (s a) ^ 2) =
          ∑ b : Fin 28, ((if a = b then t_sep * W_int a else 0 : ℤ) : ℝ) * s a * s b := by
        rw [Finset.sum_eq_single a]
        · simp only [↓reduceIte, Int.cast_mul]; ring
        · intro b _ hba; simp [hba.symm]
        · intro h; exact absurd (Finset.mem_univ a) h
      rw [hdiag, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      unfold M_int
      push_cast
      ring
    rw [hM]
    have hR : (∑ k : Fin 28, (∑ a : Fin 28, (R_int k a : ℝ) * s a) ^ 2) =
        ∑ a : Fin 28, ∑ b : Fin 28,
          (∑ k : Fin 28, (R_int k a : ℝ) * (R_int k b : ℝ)) * s a * s b := by
      calc ∑ k : Fin 28, (∑ a : Fin 28, (R_int k a : ℝ) * s a) ^ 2
          = ∑ k : Fin 28, ∑ a : Fin 28, ∑ b : Fin 28,
              (R_int k a : ℝ) * (R_int k b : ℝ) * s a * s b := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [sq, Finset.sum_mul]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => by ring
        _ = ∑ a : Fin 28, ∑ b : Fin 28, ∑ k : Fin 28,
              (R_int k a : ℝ) * (R_int k b : ℝ) * s a * s b := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            simp_rw [Finset.sum_mul]
    rw [hR, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold E_int
    push_cast
    ring
  rw [hid]
  exact add_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _) (quad_E_nonneg s)

lemma K_strict_gt : (t_sep : ℝ) * frobSq K_real < frobSq (lyap A_real K_real) := by
  have hK : frobSq K_real = (frobSq_int K_int : ℝ) := by
    unfold frobSq frobSq_int K_real
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change ((K_int i j : ℝ)) ^ 2 = (K_int i j : ℝ) * (K_int i j : ℝ)
    rw [sq]
  have hLK : frobSq (lyap A_real K_real) = (frobSq_int (lyap_int A_int K_int) : ℝ) := by
    unfold frobSq frobSq_int
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hij : lyap A_real K_real i j = (lyap_int A_int K_int i j : ℝ) := by
      unfold lyap lyap_int A_real K_real
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
      push_cast
      rfl
    rw [hij, sq]
  rw [hK, hLK]
  exact_mod_cast K_beats_sep

lemma frobSq_pos_of_ne_zero {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (h : frobSq S ≠ 0) :
    0 < frobSq S := by
  have hge : 0 ≤ frobSq S :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  exact lt_of_le_of_ne hge (Ne.symm h)

lemma K_frob_real_pos : 0 < frobSq K_real := by
  have hK : frobSq K_real = (frobSq_int K_int : ℝ) := by
    unfold frobSq frobSq_int K_real
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      change ((K_int i j : ℝ)) ^ 2 = _; rw [sq]
  rw [hK]
  exact_mod_cast K_frob_pos

end OMA.P_arxiv_2608_20875

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2608_20875.main) := by
  intro h
  obtain ⟨S, hSsym, hSne, hmax⟩ := h 7 (by norm_num) OMA.P_arxiv_2608_20875.A_real
  have hSpos : 0 < OMA.S_arxiv_2608_20875.frobSq S :=
    OMA.P_arxiv_2608_20875.frobSq_pos_of_ne_zero hSne
  have hKpos : 0 < OMA.S_arxiv_2608_20875.frobSq OMA.P_arxiv_2608_20875.K_real :=
    OMA.P_arxiv_2608_20875.K_frob_real_pos
  have hle_sep := OMA.P_arxiv_2608_20875.sym_le_sep S hSsym
  have hlt_K := OMA.P_arxiv_2608_20875.K_strict_gt
  have hK_le_S := hmax OMA.P_arxiv_2608_20875.K_real
  have h1 : OMA.S_arxiv_2608_20875.frobSq (OMA.S_arxiv_2608_20875.lyap OMA.P_arxiv_2608_20875.A_real S) *
      OMA.S_arxiv_2608_20875.frobSq OMA.P_arxiv_2608_20875.K_real ≤
      (OMA.P_arxiv_2608_20875.t_sep : ℝ) * OMA.S_arxiv_2608_20875.frobSq S *
      OMA.S_arxiv_2608_20875.frobSq OMA.P_arxiv_2608_20875.K_real :=
    mul_le_mul_of_nonneg_right hle_sep (le_of_lt hKpos)
  have h2 : (OMA.P_arxiv_2608_20875.t_sep : ℝ) *
      OMA.S_arxiv_2608_20875.frobSq OMA.P_arxiv_2608_20875.K_real *
      OMA.S_arxiv_2608_20875.frobSq S <
      OMA.S_arxiv_2608_20875.frobSq (OMA.S_arxiv_2608_20875.lyap OMA.P_arxiv_2608_20875.A_real
        OMA.P_arxiv_2608_20875.K_real) * OMA.S_arxiv_2608_20875.frobSq S :=
    mul_lt_mul_of_pos_right hlt_K hSpos
  linarith
