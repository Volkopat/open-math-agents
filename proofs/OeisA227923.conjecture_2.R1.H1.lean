import OMAReductions.R_OeisA227923_conjecture_2_R1
import Mathlib

-- Step OeisA227923.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA227923.conjecture_2.R1
-- Credit: @prathameshnium. Finite check for 5 ≤ n ≤ 1004.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 5881.

/-! Step OeisA227923.conjecture_2.R1.H1. -/

namespace OMA.AOeisA227923_conjecture_2Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `78` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 78 2

theorem noDiv_sound (p : ℕ) : ∀ f d, noDiv p f d = true → ∀ m, d ≤ m → m * m ≤ p → ¬ m ∣ p := by
  intro f
  induction f with
  | zero => intro d h; simp [noDiv] at h
  | succ f ih =>
    intro d h m hdm hmm hdiv
    simp only [noDiv] at h
    by_cases h1 : Nat.blt p (d * d) = true
    · rw [Nat.blt_eq] at h1
      have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · rw [if_neg h1] at h
      by_cases h2 : Nat.beq (p % d) 0 = true
      · rw [if_pos h2] at h; exact Bool.false_ne_true h
      · rw [if_neg h2] at h
        rcases Nat.eq_or_lt_of_le hdm with h3 | h3
        · subst h3
          exact h2 (by rw [Nat.beq_eq]; exact Nat.mod_eq_zero_of_dvd hdiv)
        · exact ih (d + 1) h m h3 hmm hdiv

theorem isPrimeB_sound (p : ℕ) (h : isPrimeB p = true) : p.Prime := by
  simp only [isPrimeB, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨h2, h⟩ := h
  have hnd := noDiv_sound p 78 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [x, y] => (decide (1 < x) && (decide (1 < y) && (decide (x ≠ y) && (decide (x + y = n) && (isPrimeB (6 * x - 1) && (isPrimeB (12 * x - 1) && (isPrimeB (6 * y - 1) && isPrimeB (6 * y + 1))))))))
  | _ => false

def good (n : ℕ) (w : List ℕ) : Bool := (Nat.beq n 13) || core n w

/-- `checkList n l`: entry `i` of `l` is a witness that `good (n + i) _` holds. -/
def checkList : ℕ → List (List ℕ) → Bool
  | _, [] => true
  | n, x :: xs => good n x && checkList (n + 1) xs

theorem checkList_sound : ∀ (l : List (List ℕ)) (n : ℕ), checkList n l = true →
    ∀ i, i < l.length → ∃ x, good (n + i) x = true := by
  intro l
  induction l with
  | nil => intro n _ i hi; simp at hi
  | cons x xs ih =>
    intro n h i hi
    simp only [checkList, Bool.and_eq_true] at h
    cases i with
    | zero => exact ⟨x, by simpa using h.1⟩
    | succ i =>
      obtain ⟨y, hy⟩ := ih (n + 1) h.2 i (by simpa using hi)
      exact ⟨y, by rw [show n + (i + 1) = n + 1 + i by omega]; exact hy⟩

theorem core_sound (n : ℕ) (w : List ℕ) (h : core n w = true) :
    ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x ≠ y ∧ x + y = n ∧
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime := by
  unfold core at h
  split at h
  next x y =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
    exact ⟨x, y, a0, a1, a2, a3, isPrimeB_sound _ a4, isPrimeB_sound _ a5, isPrimeB_sound _ a6, isPrimeB_sound _ a7⟩
  next => exact absurd h Bool.false_ne_true

theorem good_sound (n : ℕ) (w : List ℕ) (hn : n > 4) (h13 : n ≠ 13)
    (h : good n w = true) : ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x ≠ y ∧ x + y = n ∧
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime := by
  simp only [good, Bool.or_eq_true] at h
  rcases h with h | h
  · rw [Nat.beq_eq] at h; exact absurd h h13
  · exact core_sound n w h

/-! One witness for each `n = 5, …, 1004`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[2, 3], [4, 2], [2, 5], [5, 3], [2, 7], [7, 3], [4, 7], [2, 10], [], [2, 12], [5, 10], [4, 12], [5, 12], [15, 3], [2, 17], [2, 18], [4, 17], [4, 18], [5, 18], [7, 17], [2, 23], [9, 17], [2, 25], [5, 23], [4, 25]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 5 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[5, 25], [14, 17], [2, 30], [15, 18], [2, 32], [2, 33], [4, 32], [4, 33], [5, 33], [7, 32], [2, 38], [9, 32], [2, 40], [5, 38], [4, 40], [5, 40], [14, 32], [2, 45], [15, 33], [2, 47], [5, 45], [4, 47], [5, 47], [15, 38], [2, 52]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 30 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[15, 40], [4, 52], [5, 52], [40, 18], [7, 52], [2, 58], [9, 52], [4, 58], [5, 58], [19, 45], [7, 58], [14, 52], [9, 58], [30, 38], [22, 47], [30, 40], [19, 52], [2, 70], [15, 58], [2, 72], [5, 70], [4, 72], [5, 72], [40, 38], [2, 77]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 55 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[22, 58], [4, 77], [5, 77], [60, 23], [7, 77], [15, 70], [9, 77], [15, 72], [30, 58], [2, 87], [32, 58], [4, 87], [5, 87], [60, 33], [7, 87], [70, 25], [9, 87], [2, 95], [40, 58], [4, 95], [5, 95], [14, 87], [2, 100], [70, 33], [4, 100]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 80 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[2, 103], [19, 87], [4, 103], [5, 103], [2, 107], [7, 103], [4, 107], [2, 110], [110, 3], [4, 110], [5, 110], [9, 107], [7, 110], [15, 103], [9, 110], [82, 38], [14, 107], [15, 107], [85, 38], [14, 110], [15, 110], [19, 107], [32, 95], [70, 58], [19, 110]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 105 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[30, 100], [99, 32], [22, 110], [30, 103], [39, 95], [32, 103], [29, 107], [2, 135], [120, 18], [2, 137], [2, 138], [4, 137], [4, 138], [5, 138], [7, 137], [2, 143], [9, 137], [4, 143], [5, 143], [2, 147], [7, 143], [4, 147], [5, 147], [15, 138], [7, 147]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 130 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[60, 95], [9, 147], [14, 143], [15, 143], [22, 137], [22, 138], [14, 147], [15, 147], [60, 103], [29, 135], [22, 143], [19, 147], [29, 138], [30, 138], [22, 147], [32, 138], [99, 72], [2, 170], [30, 143], [2, 172], [5, 170], [4, 172], [2, 175], [40, 138], [2, 177]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 155 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[5, 175], [4, 177], [5, 177], [40, 143], [2, 182], [15, 170], [4, 182], [5, 182], [85, 103], [7, 182], [15, 175], [9, 182], [15, 177], [135, 58], [2, 192], [60, 135], [4, 192], [5, 192], [60, 138], [7, 192], [30, 170], [9, 192], [30, 172], [60, 143], [22, 182]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 180 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[30, 175], [14, 192], [2, 205], [70, 138], [4, 205], [5, 205], [19, 192], [7, 205], [70, 143], [9, 205], [2, 213], [39, 177], [2, 215], [5, 213], [2, 217], [5, 215], [4, 217], [2, 220], [85, 138], [4, 220], [5, 220], [9, 217], [7, 220], [15, 213], [9, 220]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 205 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[15, 215], [14, 217], [15, 217], [175, 58], [14, 220], [15, 220], [19, 217], [22, 215], [135, 103], [19, 220], [2, 238], [49, 192], [4, 238], [5, 238], [2, 242], [7, 238], [4, 242], [5, 242], [110, 138], [2, 247], [2, 248], [4, 247], [4, 248], [5, 248], [7, 247]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 230 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[7, 248], [9, 247], [9, 248], [120, 138], [39, 220], [22, 238], [14, 247], [14, 248], [15, 248], [22, 242], [60, 205], [19, 247], [19, 248], [30, 238], [22, 247], [2, 268], [29, 242], [2, 270], [5, 268], [4, 270], [5, 270], [29, 247], [7, 270], [30, 248], [9, 270]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 255 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[2, 278], [39, 242], [4, 278], [5, 278], [14, 270], [2, 283], [39, 247], [4, 283], [5, 283], [2, 287], [7, 283], [4, 287], [5, 287], [15, 278], [7, 287], [47, 248], [9, 287], [14, 283], [15, 283], [29, 270], [2, 298], [14, 287], [4, 298], [5, 298], [99, 205]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 280 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[7, 298], [19, 287], [9, 298], [30, 278], [22, 287], [32, 278], [204, 107], [14, 298], [15, 298], [2, 312], [2, 313], [4, 312], [4, 313], [5, 313], [7, 312], [7, 313], [9, 312], [9, 313], [40, 283], [2, 322], [42, 283], [4, 322], [2, 325], [15, 313], [4, 325]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 305 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[5, 325], [9, 322], [7, 325], [85, 248], [9, 325], [2, 333], [14, 322], [4, 333], [5, 333], [14, 325], [2, 338], [19, 322], [4, 338], [5, 338], [19, 325], [7, 338], [99, 247], [9, 338], [15, 333], [2, 347], [2, 348], [4, 347], [4, 348], [5, 348], [2, 352]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 330 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[7, 348], [4, 352], [2, 355], [60, 298], [2, 357], [5, 355], [4, 357], [5, 357], [15, 348], [7, 357], [32, 333], [9, 357], [15, 352], [30, 338], [14, 355], [15, 355], [14, 357], [15, 357], [40, 333], [19, 355], [2, 373], [19, 357], [4, 373], [5, 373], [22, 357]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 355 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[2, 378], [29, 352], [4, 378], [5, 378], [29, 355], [7, 378], [29, 357], [2, 385], [15, 373], [4, 385], [5, 385], [39, 352], [2, 390], [15, 378], [4, 390], [5, 390], [39, 357], [7, 390], [60, 338], [2, 397], [15, 385], [4, 397], [5, 397], [30, 373], [7, 397]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 380 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[15, 390], [9, 397], [22, 385], [30, 378], [19, 390], [32, 378], [14, 397], [15, 397], [40, 373], [29, 385], [30, 385], [19, 397], [32, 385], [40, 378], [22, 397], [30, 390], [74, 347], [32, 390], [85, 338], [39, 385], [40, 385], [29, 397], [2, 425], [215, 213], [4, 425]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 405 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[5, 425], [74, 357], [7, 425], [60, 373], [2, 432], [110, 325], [4, 432], [5, 432], [60, 378], [7, 432], [15, 425], [9, 432], [85, 357], [70, 373], [19, 425], [2, 443], [14, 432], [4, 443], [5, 443], [124, 325], [2, 448], [19, 432], [4, 448], [5, 448], [2, 452]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 430 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[7, 448], [4, 452], [2, 455], [15, 443], [4, 455], [5, 455], [9, 452], [7, 455], [15, 448], [9, 455], [22, 443], [14, 452], [2, 465], [120, 348], [2, 467], [5, 465], [4, 467], [5, 467], [30, 443], [7, 467], [32, 443], [9, 467], [22, 455], [30, 448], [14, 465]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 455 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[15, 465], [14, 467], [15, 467], [40, 443], [19, 465], [30, 455], [19, 467], [22, 465], [40, 448], [22, 467], [42, 448], [39, 452], [40, 452], [120, 373], [29, 465], [30, 465], [29, 467], [2, 495], [120, 378], [4, 495], [5, 495], [49, 452], [2, 500], [60, 443], [4, 500]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 480 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[5, 500], [39, 467], [7, 500], [60, 448], [9, 500], [15, 495], [114, 397], [47, 465], [70, 443], [14, 500], [15, 500], [49, 467], [22, 495], [70, 448], [19, 500], [72, 448], [124, 397], [2, 520], [175, 348], [4, 520], [5, 520], [74, 452], [7, 520], [85, 443], [9, 520]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 505 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[2, 528], [99, 432], [4, 528], [5, 528], [14, 520], [7, 528], [184, 352], [9, 528], [205, 333], [19, 520], [40, 500], [74, 467], [14, 528], [15, 528], [2, 542], [2, 543], [4, 542], [4, 543], [5, 543], [7, 542], [7, 543], [9, 542], [2, 550], [110, 443], [4, 550]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 530 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[5, 550], [14, 542], [2, 555], [15, 543], [4, 555], [5, 555], [19, 542], [2, 560], [120, 443], [2, 562], [5, 560], [4, 562], [2, 565], [40, 528], [4, 565], [5, 565], [9, 562], [7, 565], [30, 543], [9, 565], [15, 560], [14, 562], [15, 562], [135, 443], [2, 577]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 555 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[2, 578], [4, 577], [4, 578], [5, 578], [7, 577], [7, 578], [9, 577], [9, 578], [60, 528], [29, 560], [2, 588], [14, 577], [2, 590], [5, 588], [4, 590], [2, 593], [19, 577], [4, 593], [5, 593], [2, 597], [7, 593], [4, 597], [5, 597], [15, 588], [7, 597]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 580 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[15, 590], [9, 597], [14, 593], [15, 593], [19, 590], [22, 588], [14, 597], [15, 597], [70, 543], [2, 612], [22, 593], [4, 612], [5, 612], [30, 588], [7, 612], [30, 590], [9, 612], [29, 593], [30, 593], [47, 577], [32, 593], [14, 612], [15, 612], [40, 588], [32, 597]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 605 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[2, 628], [19, 612], [4, 628], [5, 628], [22, 612], [7, 628], [39, 597], [9, 628], [60, 578], [2, 637], [47, 593], [4, 637], [5, 637], [15, 628], [2, 642], [85, 560], [4, 642], [5, 642], [60, 588], [7, 642], [22, 628], [9, 642], [15, 637], [60, 593], [42, 612]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 630 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[2, 653], [14, 642], [2, 655], [5, 653], [4, 655], [5, 655], [19, 642], [7, 655], [70, 593], [9, 655], [72, 593], [29, 637], [14, 653], [15, 653], [2, 667], [15, 655], [4, 667], [2, 670], [85, 588], [4, 670], [5, 670], [9, 667], [2, 675], [85, 593], [4, 675]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 655 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[5, 675], [14, 667], [7, 675], [30, 653], [2, 682], [15, 670], [4, 682], [5, 682], [60, 628], [7, 682], [2, 688], [9, 682], [4, 688], [5, 688], [19, 675], [2, 693], [14, 682], [4, 693], [5, 693], [29, 670], [7, 693], [19, 682], [9, 693], [15, 688], [22, 682]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 680 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[2, 703], [39, 667], [2, 705], [5, 703], [2, 707], [5, 705], [4, 707], [2, 710], [60, 653], [2, 712], [5, 710], [4, 712], [5, 712], [15, 703], [7, 712], [15, 705], [9, 712], [15, 707], [30, 693], [14, 710], [2, 723], [14, 712], [4, 723], [5, 723], [19, 710]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 705 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[7, 723], [19, 712], [9, 723], [30, 703], [22, 712], [30, 705], [29, 707], [14, 723], [15, 723], [2, 737], [30, 710], [4, 737], [5, 737], [40, 703], [7, 737], [22, 723], [9, 737], [40, 707], [60, 688], [2, 747], [40, 710], [4, 747], [5, 747], [30, 723], [7, 747]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 730 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[2, 753], [9, 747], [4, 753], [5, 753], [22, 737], [2, 758], [14, 747], [4, 758], [5, 758], [82, 682], [7, 758], [19, 747], [9, 758], [15, 753], [22, 747], [47, 723], [159, 612], [14, 758], [15, 758], [99, 675], [2, 773], [29, 747], [2, 775], [5, 773], [4, 775]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 755 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[5, 775], [74, 707], [7, 775], [30, 753], [9, 775], [32, 753], [39, 747], [14, 773], [15, 773], [2, 787], [15, 775], [4, 787], [5, 787], [40, 753], [7, 787], [22, 773], [9, 787], [22, 775], [40, 758], [124, 675], [2, 798], [14, 787], [2, 800], [5, 798], [4, 800]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 780 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[5, 800], [19, 787], [7, 800], [85, 723], [9, 800], [107, 703], [74, 737], [14, 798], [15, 798], [14, 800], [15, 800], [29, 787], [19, 798], [60, 758], [19, 800], [22, 798], [74, 747], [22, 800], [70, 753], [2, 822], [72, 753], [4, 822], [5, 822], [30, 798], [7, 822]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 805 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[2, 828], [9, 822], [4, 828], [5, 828], [47, 787], [7, 828], [14, 822], [2, 835], [40, 798], [2, 837], [5, 835], [4, 837], [5, 837], [15, 828], [7, 837], [47, 798], [9, 837], [19, 828], [260, 588], [14, 835], [15, 835], [14, 837], [2, 850], [260, 593], [4, 850]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 830 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[5, 850], [19, 837], [7, 850], [30, 828], [9, 850], [32, 828], [39, 822], [40, 822], [110, 753], [14, 850], [15, 850], [29, 837], [30, 837], [40, 828], [19, 850], [42, 828], [49, 822], [22, 850], [120, 753], [2, 872], [40, 835], [4, 872], [5, 872], [120, 758], [7, 872]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 855 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[30, 850], [9, 872], [2, 880], [85, 798], [4, 880], [5, 880], [14, 872], [7, 880], [60, 828], [9, 880], [40, 850], [19, 872], [42, 850], [120, 773], [14, 880], [15, 880], [74, 822], [47, 850], [70, 828], [19, 880], [72, 828], [29, 872], [22, 880], [215, 688], [32, 872]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 880 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[2, 903], [159, 747], [4, 903], [5, 903], [2, 907], [7, 903], [4, 907], [5, 907], [85, 828], [7, 907], [2, 913], [9, 907], [4, 913], [5, 913], [2, 917], [7, 913], [4, 917], [2, 920], [170, 753], [4, 920], [5, 920], [9, 917], [7, 920], [15, 913], [9, 920]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 905 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[172, 758], [14, 917], [15, 917], [30, 903], [14, 920], [15, 920], [19, 917], [30, 907], [110, 828], [19, 920], [60, 880], [204, 737], [2, 940], [30, 913], [2, 942], [2, 943], [4, 942], [4, 943], [5, 943], [7, 942], [7, 943], [9, 942], [9, 943], [40, 913], [14, 940]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 930 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[15, 940], [14, 942], [14, 943], [15, 943], [2, 957], [40, 920], [4, 957], [5, 957], [60, 903], [7, 957], [22, 943], [9, 957], [47, 920], [170, 798], [29, 940], [30, 940], [14, 957], [15, 957], [30, 943], [32, 942], [32, 943], [19, 957], [2, 975], [205, 773], [4, 975]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 955 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[2, 978], [39, 942], [2, 980], [5, 978], [4, 980], [5, 980], [29, 957], [7, 980], [85, 903], [9, 980], [15, 975], [49, 942], [14, 978], [15, 978], [14, 980], [15, 980], [39, 957], [19, 978], [85, 913], [19, 980], [22, 978], [264, 737], [22, 980], [60, 943], [29, 975]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 980 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `5 ≤ n ≤ 1004` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 5 ≤ n) (h2 : n ≤ 1004) : ∃ x, good n x = true := by
  by_cases c0 : n < 30
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 55
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 80
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 105
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 130
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 155
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 180
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 205
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 230
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 255
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 280
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 305
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 330
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 355
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 380
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 405
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 430
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 455
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 480
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 505
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 530
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 555
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 580
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 605
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 630
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 655
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 680
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 705
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 730
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 755
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 780
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 805
  · exact chunk ok31 len31 (by omega) (by omega)
  by_cases c32 : n < 830
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 855
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 880
  · exact chunk ok34 len34 (by omega) (by omega)
  by_cases c35 : n < 905
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 930
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 955
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 980
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.AOeisA227923_conjecture_2Tab

open OMA.AOeisA227923_conjecture_2Tab in
theorem OMA.solution : OMA.R_OeisA227923_conjecture_2_R1.H1 := by
  intro n hn h13 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact good_sound n w hn h13 hw
