import OMAReductions.R_OeisA227923_conjecture_3_R1
import Mathlib

-- Step OeisA227923.conjecture_3.R1.H1: hypothesis H1 of reduction OeisA227923.conjecture_3.R1
-- Credit: @prathameshnium. Finite check for 2 ≤ n ≤ 1001.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 7703.

/-! Step OeisA227923.conjecture_3.R1.H1. -/

namespace OMA.AOeisA227923_conjecture_3Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `89` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 89 2

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
  have hnd := noDiv_sound p 89 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [x, y] => (decide (0 < x) && (decide (0 < y) && (decide (x + y = n) && (isPrimeB (6 * x - 1) && (isPrimeB (12 * x - 1) && (isPrimeB (6 * y + 1) && isPrimeB (6 * y + 5)))))))
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
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y + 1).Prime ∧ (6 * y + 5).Prime := by
  unfold core at h
  split at h
  next x y =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := h
    exact ⟨x, y, a0, a1, a2, isPrimeB_sound _ a3, isPrimeB_sound _ a4, isPrimeB_sound _ a5, isPrimeB_sound _ a6⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 2, …, 1001`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[1, 1], [1, 2], [1, 3], [2, 3], [4, 2], [1, 6], [1, 7], [2, 7], [4, 6], [4, 7], [1, 11], [2, 11], [1, 13], [2, 13], [5, 11], [1, 16], [1, 17], [1, 18], [2, 18], [4, 17], [1, 21], [2, 21], [7, 17], [4, 21], [5, 21]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 2 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[9, 18], [1, 27], [2, 27], [9, 21], [4, 27], [5, 27], [1, 32], [2, 32], [14, 21], [4, 32], [5, 32], [1, 37], [1, 38], [2, 38], [4, 37], [4, 38], [5, 38], [7, 37], [7, 38], [9, 37], [1, 46], [2, 46], [22, 27], [4, 46], [5, 46]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 27 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[1, 51], [1, 52], [2, 52], [4, 51], [4, 52], [5, 52], [7, 51], [1, 58], [2, 58], [9, 52], [4, 58], [5, 58], [1, 63], [2, 63], [14, 52], [1, 66], [2, 66], [32, 37], [4, 66], [5, 66], [9, 63], [7, 66], [1, 73], [2, 73], [30, 46]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 52 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[1, 76], [1, 77], [2, 77], [4, 76], [4, 77], [1, 81], [2, 81], [1, 83], [2, 83], [5, 81], [4, 83], [5, 83], [72, 17], [7, 83], [14, 77], [9, 83], [30, 63], [42, 52], [14, 81], [15, 81], [14, 83], [15, 83], [22, 77], [19, 81], [49, 52]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 77 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[19, 83], [1, 102], [2, 102], [22, 83], [4, 102], [5, 102], [1, 107], [2, 107], [29, 81], [4, 107], [5, 107], [1, 112], [2, 112], [32, 83], [4, 112], [5, 112], [42, 76], [7, 112], [39, 81], [9, 112], [15, 107], [40, 83], [1, 123], [2, 123], [14, 112]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 102 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[1, 126], [2, 126], [1, 128], [2, 128], [5, 126], [4, 128], [5, 128], [22, 112], [7, 128], [29, 107], [9, 128], [1, 137], [2, 137], [14, 126], [4, 137], [5, 137], [1, 142], [1, 143], [2, 143], [4, 142], [1, 146], [1, 147], [2, 147], [4, 146], [4, 147]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 127 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[1, 151], [2, 151], [7, 147], [4, 151], [5, 151], [1, 156], [2, 156], [22, 137], [4, 156], [5, 156], [1, 161], [2, 161], [22, 142], [4, 161], [5, 161], [30, 137], [7, 161], [1, 168], [2, 168], [15, 156], [4, 168], [5, 168], [32, 142], [7, 168], [15, 161]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 152 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[9, 168], [22, 156], [32, 147], [19, 161], [30, 151], [1, 181], [1, 182], [2, 182], [4, 181], [4, 182], [5, 182], [7, 181], [7, 182], [9, 181], [9, 182], [49, 143], [32, 161], [47, 147], [14, 181], [14, 182], [15, 182], [30, 168], [172, 27], [19, 181], [19, 182]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 177 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[60, 142], [1, 202], [2, 202], [49, 156], [4, 202], [5, 202], [40, 168], [7, 202], [29, 181], [9, 202], [30, 182], [32, 181], [1, 213], [2, 213], [14, 202], [1, 216], [1, 217], [2, 217], [4, 216], [4, 217], [5, 217], [7, 216], [7, 217], [9, 216], [9, 217]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 202 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[14, 213], [15, 213], [47, 182], [14, 216], [14, 217], [15, 217], [72, 161], [32, 202], [19, 216], [19, 217], [109, 128], [1, 237], [1, 238], [2, 238], [4, 237], [1, 241], [2, 241], [7, 237], [4, 241], [5, 241], [9, 238], [1, 247], [1, 248], [2, 248], [4, 247]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 227 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[4, 248], [5, 248], [7, 247], [7, 248], [9, 247], [9, 248], [42, 216], [1, 258], [2, 258], [14, 247], [1, 261], [2, 261], [1, 263], [2, 263], [5, 261], [1, 266], [2, 266], [1, 268], [2, 268], [5, 266], [4, 268], [5, 268], [72, 202], [7, 268], [15, 261]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 252 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[9, 268], [1, 277], [2, 277], [14, 266], [4, 277], [5, 277], [1, 282], [2, 282], [19, 266], [4, 282], [5, 282], [22, 266], [7, 282], [22, 268], [9, 282], [15, 277], [30, 263], [47, 247], [29, 266], [14, 282], [15, 282], [1, 297], [2, 297], [32, 268], [4, 297]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 277 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[5, 297], [40, 263], [7, 297], [39, 266], [9, 297], [30, 277], [40, 268], [32, 277], [42, 268], [14, 297], [1, 311], [1, 312], [2, 312], [4, 311], [4, 312], [5, 312], [7, 311], [7, 312], [9, 311], [9, 312], [40, 282], [60, 263], [42, 282], [14, 311], [14, 312]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 302 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[15, 312], [60, 268], [32, 297], [19, 311], [19, 312], [74, 258], [1, 332], [1, 333], [2, 333], [4, 332], [4, 333], [5, 333], [7, 332], [7, 333], [9, 332], [9, 333], [32, 311], [32, 312], [82, 263], [14, 332], [14, 333], [1, 347], [2, 347], [39, 311], [4, 347]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 327 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[5, 347], [42, 311], [7, 347], [22, 333], [9, 347], [1, 356], [2, 356], [47, 312], [4, 356], [5, 356], [15, 347], [7, 356], [32, 332], [9, 356], [19, 347], [70, 297], [1, 367], [2, 367], [14, 356], [4, 367], [5, 367], [40, 333], [1, 373], [2, 373], [9, 367]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 352 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[4, 373], [5, 373], [1, 378], [2, 378], [14, 367], [4, 378], [1, 382], [2, 382], [7, 378], [4, 382], [5, 382], [15, 373], [7, 382], [124, 266], [9, 382], [1, 391], [2, 391], [47, 347], [4, 391], [5, 391], [1, 396], [2, 396], [1, 398], [2, 398], [5, 396]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 377 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[4, 398], [5, 398], [22, 382], [7, 398], [15, 391], [1, 406], [2, 406], [42, 367], [4, 406], [5, 406], [14, 398], [1, 412], [2, 412], [9, 406], [4, 412], [5, 412], [22, 396], [7, 412], [14, 406], [9, 412], [40, 382], [32, 391], [1, 423], [2, 423], [14, 412]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 402 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[4, 423], [5, 423], [47, 382], [7, 423], [19, 412], [9, 423], [42, 391], [22, 412], [29, 406], [30, 406], [1, 436], [2, 436], [72, 367], [4, 436], [5, 436], [19, 423], [7, 436], [1, 443], [2, 443], [40, 406], [4, 443], [1, 447], [1, 448], [2, 448], [4, 447]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 427 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[1, 451], [2, 451], [7, 447], [4, 451], [5, 451], [9, 448], [7, 451], [1, 458], [2, 458], [14, 447], [4, 458], [5, 458], [82, 382], [7, 458], [15, 451], [1, 466], [2, 466], [22, 447], [4, 466], [5, 466], [14, 458], [1, 472], [2, 472], [9, 466], [4, 472]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 452 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[1, 476], [2, 476], [7, 472], [4, 476], [5, 476], [39, 443], [7, 476], [72, 412], [9, 476], [14, 472], [15, 472], [22, 466], [42, 447], [14, 476], [15, 476], [49, 443], [1, 492], [2, 492], [19, 476], [4, 492], [5, 492], [22, 476], [7, 492], [42, 458], [9, 492]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 477 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[30, 472], [60, 443], [1, 503], [2, 503], [14, 492], [1, 506], [2, 506], [127, 382], [4, 506], [5, 506], [9, 503], [7, 506], [1, 513], [2, 513], [40, 476], [4, 513], [5, 513], [47, 472], [7, 513], [15, 506], [9, 513], [47, 476], [32, 492], [19, 506], [60, 466]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 502 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[14, 513], [1, 527], [2, 527], [72, 458], [4, 527], [1, 531], [2, 531], [7, 527], [4, 531], [5, 531], [1, 536], [2, 536], [47, 492], [4, 536], [5, 536], [15, 527], [1, 542], [2, 542], [9, 536], [4, 542], [5, 542], [42, 506], [7, 542], [14, 536], [9, 542]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 527 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[39, 513], [22, 531], [1, 553], [2, 553], [14, 542], [4, 553], [1, 557], [2, 557], [7, 553], [4, 557], [5, 557], [32, 531], [7, 557], [29, 536], [9, 557], [14, 553], [15, 553], [42, 527], [39, 531], [14, 557], [15, 557], [42, 531], [32, 542], [22, 553], [19, 557]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 552 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[1, 576], [1, 577], [2, 577], [4, 576], [4, 577], [5, 577], [7, 576], [7, 577], [9, 576], [9, 577], [30, 557], [82, 506], [1, 588], [2, 588], [14, 577], [4, 588], [5, 588], [247, 347], [7, 588], [19, 577], [9, 588], [22, 576], [22, 577], [47, 553], [70, 531]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 577 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[14, 588], [1, 602], [2, 602], [29, 576], [4, 602], [5, 602], [32, 576], [7, 602], [22, 588], [9, 602], [70, 542], [1, 612], [2, 612], [39, 576], [4, 612], [1, 616], [2, 616], [7, 612], [4, 616], [5, 616], [109, 513], [7, 616], [22, 602], [9, 616], [14, 612]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 602 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[15, 612], [40, 588], [72, 557], [14, 616], [15, 616], [30, 602], [1, 632], [2, 632], [19, 616], [4, 632], [5, 632], [22, 616], [7, 632], [109, 531], [9, 632], [1, 641], [2, 641], [32, 612], [4, 641], [5, 641], [1, 646], [2, 646], [47, 602], [4, 646], [5, 646]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 627 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[1, 651], [2, 651], [1, 653], [2, 653], [5, 651], [4, 653], [1, 657], [2, 657], [7, 653], [4, 657], [5, 657], [22, 641], [7, 657], [14, 651], [9, 657], [14, 653], [1, 667], [2, 667], [19, 651], [4, 667], [5, 667], [22, 651], [7, 667], [22, 653], [9, 667]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 652 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[120, 557], [32, 646], [22, 657], [29, 651], [14, 667], [15, 667], [30, 653], [72, 612], [32, 653], [19, 667], [30, 657], [42, 646], [1, 688], [2, 688], [40, 651], [4, 688], [1, 692], [2, 692], [7, 688], [4, 692], [5, 692], [47, 651], [7, 692], [47, 653], [9, 692]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 677 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[14, 688], [15, 688], [47, 657], [152, 553], [14, 692], [15, 692], [120, 588], [42, 667], [22, 688], [19, 692], [110, 602], [60, 653], [22, 692], [74, 641], [49, 667], [29, 688], [30, 688], [107, 612], [32, 688], [29, 692], [30, 692], [70, 653], [32, 692], [72, 653], [85, 641]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 702 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[39, 688], [40, 688], [72, 657], [42, 688], [39, 692], [40, 692], [82, 651], [42, 692], [47, 688], [85, 651], [49, 688], [85, 653], [47, 692], [99, 641], [49, 692], [1, 741], [2, 741], [252, 492], [4, 741], [5, 741], [135, 612], [7, 741], [82, 667], [9, 741], [110, 641]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 727 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[60, 692], [1, 752], [1, 753], [2, 753], [4, 752], [4, 753], [5, 753], [7, 752], [7, 753], [9, 752], [9, 753], [22, 741], [72, 692], [114, 651], [14, 752], [14, 753], [15, 753], [242, 527], [29, 741], [19, 752], [19, 753], [32, 741], [1, 773], [2, 773], [109, 667]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 752 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[4, 773], [5, 773], [252, 527], [7, 773], [29, 752], [9, 773], [30, 753], [32, 752], [32, 753], [135, 651], [14, 773], [15, 773], [1, 788], [2, 788], [39, 752], [4, 788], [5, 788], [42, 752], [7, 788], [184, 612], [9, 788], [1, 797], [1, 798], [2, 798], [4, 797]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 777 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[4, 798], [1, 802], [2, 802], [7, 798], [4, 802], [5, 802], [120, 688], [7, 802], [22, 788], [9, 802], [14, 798], [15, 798], [322, 492], [42, 773], [14, 802], [15, 802], [30, 788], [22, 797], [22, 798], [19, 802], [49, 773], [1, 822], [2, 822], [72, 753], [4, 822]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 802 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[5, 822], [30, 798], [1, 828], [2, 828], [9, 822], [4, 828], [5, 828], [1, 833], [2, 833], [14, 822], [4, 833], [5, 833], [42, 797], [7, 833], [19, 822], [9, 833], [15, 828], [22, 822], [47, 798], [49, 797], [1, 846], [2, 846], [47, 802], [4, 846], [5, 846]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 827 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[19, 833], [7, 846], [32, 822], [9, 846], [205, 651], [29, 828], [30, 828], [107, 752], [14, 846], [15, 846], [1, 861], [2, 861], [42, 822], [4, 861], [5, 861], [39, 828], [7, 861], [47, 822], [9, 861], [49, 822], [1, 871], [1, 872], [2, 872], [4, 871], [4, 872]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 852 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[5, 872], [7, 871], [7, 872], [9, 871], [9, 872], [49, 833], [22, 861], [82, 802], [14, 871], [14, 872], [15, 872], [42, 846], [642, 247], [19, 871], [19, 872], [1, 891], [2, 891], [22, 872], [4, 891], [5, 891], [99, 798], [7, 891], [242, 657], [9, 891], [29, 872]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 877 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[30, 872], [1, 902], [2, 902], [14, 891], [4, 902], [1, 906], [2, 906], [7, 902], [4, 906], [5, 906], [40, 872], [7, 906], [1, 913], [2, 913], [14, 902], [4, 913], [1, 917], [2, 917], [7, 913], [4, 917], [1, 921], [2, 921], [7, 917], [4, 921], [5, 921]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 902 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[14, 913], [7, 921], [1, 928], [2, 928], [14, 917], [4, 928], [5, 928], [32, 902], [7, 928], [15, 921], [9, 928], [32, 906], [22, 917], [19, 921], [39, 902], [1, 941], [1, 942], [2, 942], [4, 941], [4, 942], [5, 942], [7, 941], [1, 948], [2, 948], [9, 942]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 927 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[4, 948], [5, 948], [82, 872], [7, 948], [14, 942], [1, 956], [2, 956], [42, 917], [4, 956], [5, 956], [14, 948], [7, 956], [1, 963], [2, 963], [49, 917], [4, 963], [5, 963], [172, 797], [7, 963], [15, 956], [9, 963], [32, 941], [1, 973], [2, 973], [70, 906]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 952 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[1, 976], [2, 976], [107, 872], [4, 976], [5, 976], [9, 973], [7, 976], [42, 942], [9, 976], [30, 956], [14, 973], [1, 987], [2, 987], [14, 976], [4, 987], [5, 987], [30, 963], [7, 987], [19, 976], [9, 987], [49, 948], [22, 976], [82, 917], [72, 928], [14, 987]]
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

end OMA.AOeisA227923_conjecture_3Tab

open OMA.AOeisA227923_conjecture_3Tab in
theorem OMA.solution : OMA.R_OeisA227923_conjecture_3_R1.H1 := by
  intro n hn hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
