import OMAReductions.R_OeisA227923_conjecture_4_R1
import Mathlib

-- Step OeisA227923.conjecture_4.R1.H1: hypothesis H1 of reduction OeisA227923.conjecture_4.R1
-- Credit: @prathameshnium. Finite check for 2 ≤ n ≤ 1001.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 5987.

/-! Step OeisA227923.conjecture_4.R1.H1. -/

namespace OMA.AOeisA227923_conjecture_4Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `79` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 79 2

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
  have hnd := noDiv_sound p 79 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [x, y] => (decide (0 < x) && (decide (0 < y) && (decide (x + y = n) && (isPrimeB (6 * x - 1) && (isPrimeB (12 * x - 1) && (isPrimeB (6 * y - 1) && isPrimeB (6 * y + 5)))))))
  | _ => false

def good (n : ℕ) (w : List ℕ) : Bool := core n w

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
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 5).Prime := by
  unfold core at h
  split at h
  next x y =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := h
    exact ⟨x, y, a0, a1, a2, isPrimeB_sound _ a3, isPrimeB_sound _ a4, isPrimeB_sound _ a5, isPrimeB_sound _ a6⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 2, …, 1001`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[1, 1], [1, 2], [1, 3], [1, 4], [2, 4], [4, 3], [1, 7], [1, 8], [1, 9], [2, 9], [4, 8], [4, 9], [5, 9], [1, 14], [2, 14], [9, 8], [1, 17], [1, 18], [2, 18], [4, 17], [4, 18], [1, 22], [2, 22], [7, 18], [4, 22]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 2 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[5, 22], [14, 14], [1, 28], [1, 29], [2, 29], [4, 28], [1, 32], [2, 32], [7, 28], [4, 32], [5, 32], [9, 29], [1, 38], [1, 39], [2, 39], [4, 38], [1, 42], [1, 43], [1, 44], [2, 44], [4, 43], [4, 44], [5, 44], [7, 43], [7, 44]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 27 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[9, 43], [1, 52], [2, 52], [47, 8], [4, 52], [5, 52], [14, 44], [1, 58], [1, 59], [2, 59], [4, 58], [4, 59], [5, 59], [1, 64], [2, 64], [9, 58], [4, 64], [5, 64], [32, 38], [7, 64], [14, 58], [9, 64], [15, 59], [1, 74], [2, 74]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 52 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[19, 58], [1, 77], [2, 77], [22, 58], [4, 77], [5, 77], [9, 74], [7, 77], [1, 84], [2, 84], [29, 58], [4, 84], [5, 84], [32, 58], [7, 84], [15, 77], [9, 84], [1, 93], [1, 94], [2, 94], [4, 93], [4, 94], [1, 98], [1, 99], [2, 99]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 77 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[4, 98], [4, 99], [5, 99], [7, 98], [7, 99], [9, 98], [1, 107], [1, 108], [1, 109], [2, 109], [4, 108], [4, 109], [1, 113], [2, 113], [7, 109], [4, 113], [5, 113], [42, 77], [7, 113], [14, 107], [9, 113], [14, 109], [15, 109], [32, 93], [19, 107]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 102 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[14, 113], [15, 113], [22, 107], [22, 108], [22, 109], [19, 113], [39, 94], [40, 94], [22, 113], [29, 107], [29, 108], [1, 137], [2, 137], [32, 108], [4, 137], [5, 137], [30, 113], [1, 143], [2, 143], [9, 137], [4, 143], [1, 147], [2, 147], [7, 143], [4, 147]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 127 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[5, 147], [40, 113], [7, 147], [42, 113], [9, 147], [14, 143], [1, 157], [1, 158], [2, 158], [4, 157], [4, 158], [1, 162], [1, 163], [2, 163], [4, 162], [4, 163], [5, 163], [7, 162], [1, 169], [2, 169], [9, 163], [4, 169], [5, 169], [32, 143], [7, 169]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 152 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[14, 163], [9, 169], [22, 157], [22, 158], [19, 162], [19, 163], [1, 182], [1, 183], [1, 184], [2, 184], [4, 183], [4, 184], [5, 184], [7, 183], [7, 184], [9, 183], [9, 184], [32, 162], [32, 163], [14, 182], [14, 183], [1, 197], [1, 198], [2, 198], [4, 197]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 177 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[4, 198], [5, 198], [1, 203], [1, 204], [2, 204], [4, 203], [4, 204], [5, 204], [7, 203], [7, 204], [9, 203], [9, 204], [1, 213], [1, 214], [2, 214], [4, 213], [1, 217], [2, 217], [7, 213], [4, 217], [5, 217], [9, 214], [7, 217], [22, 203], [9, 217]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 202 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[14, 213], [1, 227], [1, 228], [2, 228], [4, 227], [4, 228], [5, 228], [7, 227], [7, 228], [9, 227], [9, 228], [40, 198], [1, 238], [1, 239], [2, 239], [4, 238], [4, 239], [5, 239], [7, 238], [7, 239], [9, 238], [1, 247], [1, 248], [1, 249], [2, 249]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 227 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[4, 248], [4, 249], [5, 249], [7, 248], [7, 249], [9, 248], [9, 249], [32, 227], [1, 259], [2, 259], [14, 248], [4, 259], [5, 259], [82, 183], [7, 259], [19, 248], [1, 267], [1, 268], [1, 269], [2, 269], [4, 268], [4, 269], [5, 269], [7, 268], [7, 269]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 252 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[9, 268], [9, 269], [30, 249], [32, 248], [14, 267], [14, 268], [14, 269], [15, 269], [47, 238], [19, 267], [19, 268], [19, 269], [22, 267], [22, 268], [22, 269], [109, 183], [109, 184], [47, 247], [47, 248], [29, 267], [29, 268], [29, 269], [30, 269], [32, 268], [32, 269]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 277 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[74, 228], [99, 204], [107, 197], [107, 198], [39, 267], [39, 268], [39, 269], [40, 269], [42, 268], [42, 269], [74, 238], [1, 312], [2, 312], [47, 268], [4, 312], [5, 312], [1, 317], [1, 318], [2, 318], [4, 317], [4, 318], [5, 318], [7, 317], [7, 318], [9, 317]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 302 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[9, 318], [60, 268], [60, 269], [1, 329], [2, 329], [14, 318], [4, 329], [1, 333], [2, 333], [7, 329], [4, 333], [5, 333], [22, 317], [7, 333], [29, 312], [9, 333], [14, 329], [15, 329], [1, 344], [2, 344], [14, 333], [1, 347], [2, 347], [32, 318], [4, 347]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 327 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[5, 347], [9, 344], [7, 347], [22, 333], [9, 347], [39, 318], [14, 344], [15, 344], [42, 318], [14, 347], [15, 347], [19, 344], [47, 317], [32, 333], [19, 347], [49, 318], [39, 329], [1, 368], [2, 368], [42, 329], [4, 368], [5, 368], [1, 373], [2, 373], [29, 347]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 352 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[4, 373], [5, 373], [1, 378], [2, 378], [114, 267], [4, 378], [5, 378], [40, 344], [7, 378], [39, 347], [9, 378], [15, 373], [42, 347], [1, 389], [2, 389], [14, 378], [1, 392], [2, 392], [22, 373], [4, 392], [5, 392], [9, 389], [7, 392], [1, 399], [2, 399]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 377 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[29, 373], [1, 402], [1, 403], [2, 403], [4, 402], [4, 403], [1, 407], [2, 407], [7, 403], [4, 407], [5, 407], [14, 399], [7, 407], [42, 373], [9, 407], [14, 403], [15, 403], [30, 389], [42, 378], [14, 407], [15, 407], [175, 248], [22, 402], [1, 424], [2, 424]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 402 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[49, 378], [4, 424], [5, 424], [247, 183], [7, 424], [29, 403], [9, 424], [32, 402], [32, 403], [29, 407], [30, 407], [14, 424], [15, 424], [72, 368], [39, 402], [39, 403], [19, 424], [1, 443], [2, 443], [22, 424], [4, 443], [5, 443], [1, 448], [1, 449], [2, 449]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 427 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[4, 448], [4, 449], [5, 449], [7, 448], [7, 449], [9, 448], [9, 449], [60, 399], [82, 378], [72, 389], [14, 448], [14, 449], [15, 449], [22, 443], [42, 424], [19, 448], [19, 449], [70, 399], [22, 448], [22, 449], [29, 443], [30, 443], [1, 473], [2, 473], [74, 402]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 452 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[4, 473], [5, 473], [30, 449], [7, 473], [32, 449], [9, 473], [40, 443], [1, 483], [1, 484], [2, 484], [4, 483], [4, 484], [5, 484], [7, 483], [7, 484], [9, 483], [9, 484], [1, 493], [1, 494], [2, 494], [4, 493], [4, 494], [5, 494], [7, 493], [7, 494]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 477 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[9, 493], [9, 494], [175, 329], [22, 483], [22, 484], [14, 493], [14, 494], [15, 494], [107, 403], [109, 402], [19, 493], [19, 494], [30, 484], [1, 514], [2, 514], [74, 443], [4, 514], [5, 514], [47, 473], [7, 514], [29, 493], [9, 514], [30, 494], [32, 493], [32, 494]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 502 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[120, 407], [14, 514], [15, 514], [47, 483], [47, 484], [39, 493], [19, 514], [40, 494], [1, 534], [2, 534], [135, 402], [4, 534], [5, 534], [47, 493], [7, 534], [49, 493], [1, 542], [2, 542], [72, 473], [4, 542], [5, 542], [14, 534], [7, 542], [107, 443], [9, 542]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 527 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[109, 443], [19, 534], [40, 514], [1, 554], [2, 554], [15, 542], [4, 554], [5, 554], [242, 318], [7, 554], [114, 448], [9, 554], [22, 542], [72, 493], [32, 534], [74, 493], [14, 554], [1, 568], [2, 568], [29, 542], [4, 568], [5, 568], [32, 542], [7, 568], [22, 554]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 552 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[9, 568], [1, 577], [2, 577], [107, 473], [4, 577], [5, 577], [15, 568], [7, 577], [252, 333], [9, 577], [19, 568], [74, 514], [1, 588], [1, 589], [2, 589], [4, 588], [4, 589], [5, 589], [7, 588], [7, 589], [9, 588], [9, 589], [22, 577], [32, 568], [47, 554]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 577 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[14, 588], [14, 589], [1, 603], [2, 603], [29, 577], [4, 603], [5, 603], [32, 577], [7, 603], [22, 589], [9, 603], [1, 612], [2, 612], [47, 568], [4, 612], [5, 612], [15, 603], [7, 612], [32, 588], [9, 612], [19, 603], [109, 514], [47, 577], [22, 603], [14, 612]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 602 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[15, 612], [1, 627], [2, 627], [42, 588], [4, 627], [5, 627], [30, 603], [1, 633], [2, 633], [9, 627], [4, 633], [5, 633], [85, 554], [7, 633], [14, 627], [9, 633], [40, 603], [32, 612], [42, 603], [19, 627], [14, 633], [15, 633], [22, 627], [47, 603], [39, 612]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 627 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[19, 633], [1, 652], [1, 653], [1, 654], [2, 654], [4, 653], [4, 654], [5, 654], [7, 653], [7, 654], [9, 653], [9, 654], [110, 554], [32, 633], [14, 652], [14, 653], [1, 667], [1, 668], [1, 669], [2, 669], [4, 668], [4, 669], [5, 669], [7, 668], [7, 669]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 652 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[9, 668], [9, 669], [410, 269], [1, 679], [2, 679], [14, 668], [4, 679], [5, 679], [32, 653], [7, 679], [19, 668], [9, 679], [1, 688], [1, 689], [2, 689], [4, 688], [4, 689], [5, 689], [7, 688], [7, 689], [9, 688], [9, 689], [30, 669], [32, 668], [22, 679]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 677 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[14, 688], [1, 702], [2, 702], [72, 633], [4, 702], [5, 702], [19, 689], [7, 702], [1, 709], [2, 709], [60, 652], [4, 709], [5, 709], [1, 714], [2, 714], [15, 702], [4, 714], [5, 714], [32, 688], [7, 714], [70, 652], [9, 714], [15, 709], [72, 653], [47, 679]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 702 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[39, 688], [14, 714], [15, 714], [42, 688], [22, 709], [30, 702], [1, 732], [2, 732], [47, 688], [4, 732], [5, 732], [29, 709], [7, 732], [72, 668], [9, 732], [40, 702], [1, 742], [1, 743], [2, 743], [4, 742], [4, 743], [5, 743], [7, 742], [7, 743], [9, 742]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 727 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[9, 743], [39, 714], [1, 753], [2, 753], [14, 742], [4, 753], [5, 753], [70, 689], [7, 753], [19, 742], [9, 753], [49, 714], [22, 742], [22, 743], [99, 667], [14, 753], [15, 753], [60, 709], [82, 688], [29, 742], [19, 753], [30, 743], [1, 773], [1, 774], [2, 774]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 752 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[4, 773], [4, 774], [5, 774], [1, 779], [2, 779], [9, 773], [4, 779], [5, 779], [32, 753], [7, 779], [14, 773], [9, 779], [15, 774], [47, 743], [49, 742], [19, 773], [14, 779], [15, 779], [22, 773], [22, 774], [109, 688], [19, 779], [1, 798], [1, 799], [2, 799]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 777 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[4, 798], [4, 799], [5, 799], [7, 798], [7, 799], [9, 798], [9, 799], [30, 779], [242, 568], [32, 779], [14, 798], [1, 812], [2, 812], [42, 773], [4, 812], [5, 812], [19, 799], [7, 812], [22, 798], [9, 812], [49, 773], [1, 822], [1, 823], [2, 823], [4, 822]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 802 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[4, 823], [5, 823], [1, 828], [2, 828], [9, 822], [4, 828], [5, 828], [22, 812], [1, 834], [2, 834], [9, 828], [4, 834], [5, 834], [42, 798], [7, 834], [14, 828], [9, 834], [22, 822], [22, 823], [47, 799], [19, 828], [1, 847], [2, 847], [22, 828], [4, 847]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 827 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[5, 847], [19, 834], [7, 847], [32, 823], [9, 847], [29, 828], [30, 828], [1, 858], [2, 858], [14, 847], [4, 858], [5, 858], [30, 834], [7, 858], [19, 847], [9, 858], [40, 828], [22, 847], [42, 828], [49, 822], [14, 858], [1, 872], [2, 872], [47, 828], [4, 872]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 852 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[5, 872], [99, 779], [7, 872], [1, 879], [2, 879], [60, 822], [4, 879], [1, 883], [1, 884], [2, 884], [4, 883], [4, 884], [5, 884], [7, 883], [7, 884], [9, 883], [9, 884], [15, 879], [72, 823], [49, 847], [14, 883], [1, 897], [1, 898], [1, 899], [2, 899]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 877 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[4, 898], [4, 899], [5, 899], [7, 898], [7, 899], [9, 898], [9, 899], [30, 879], [82, 828], [14, 897], [14, 898], [1, 912], [1, 913], [2, 913], [4, 912], [4, 913], [1, 917], [2, 917], [7, 913], [4, 917], [5, 917], [39, 884], [7, 917], [42, 883], [9, 917]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 902 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[14, 913], [15, 913], [30, 899], [32, 898], [14, 917], [15, 917], [49, 884], [22, 912], [22, 913], [19, 917], [39, 898], [39, 899], [22, 917], [42, 898], [29, 912], [29, 913], [1, 942], [2, 942], [32, 913], [4, 942], [5, 942], [49, 899], [7, 942], [127, 823], [9, 942]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 927 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[39, 913], [1, 952], [2, 952], [42, 913], [4, 952], [5, 952], [60, 898], [7, 952], [47, 913], [9, 952], [49, 913], [135, 828], [22, 942], [82, 883], [14, 952], [15, 952], [1, 967], [1, 968], [2, 968], [4, 967], [4, 968], [5, 968], [7, 967], [1, 974], [2, 974]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 952 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[9, 968], [1, 977], [2, 977], [82, 898], [4, 977], [5, 977], [9, 974], [1, 983], [2, 983], [9, 977], [4, 983], [5, 983], [15, 974], [7, 983], [14, 977], [9, 983], [19, 974], [42, 952], [82, 913], [19, 977], [14, 983], [1, 997], [2, 997], [32, 968], [4, 997]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 977 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `2 ≤ n ≤ 1001` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 2 ≤ n) (h2 : n ≤ 1001) : ∃ x, good n x = true := by
  by_cases c0 : n < 27
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 52
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 77
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 102
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 127
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 152
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 177
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 202
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 227
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 252
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 277
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 302
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 327
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 352
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 377
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 402
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 427
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 452
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 477
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 502
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 527
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 552
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 577
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 602
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 627
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 652
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 677
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 702
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 727
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 752
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 777
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 802
  · exact chunk ok31 len31 (by omega) (by omega)
  by_cases c32 : n < 827
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 852
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 877
  · exact chunk ok34 len34 (by omega) (by omega)
  by_cases c35 : n < 902
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 927
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 952
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 977
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.AOeisA227923_conjecture_4Tab

open OMA.AOeisA227923_conjecture_4Tab in
theorem OMA.solution : OMA.R_OeisA227923_conjecture_4_R1.H1 := by
  intro n hn hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
