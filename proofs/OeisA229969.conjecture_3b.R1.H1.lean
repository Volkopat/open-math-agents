import OMAReductions.R_OeisA229969_conjecture_3b_R1
import Mathlib

-- Step OeisA229969.conjecture_3b.R1.H1: hypothesis H1 of reduction OeisA229969.conjecture_3b.R1
-- Credit: @prathameshnium. Finite check for 3 ≤ n ≤ 1002.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 647641.

/-! Step OeisA229969.conjecture_3b.R1.H1. -/

namespace OMA.AOeisA229969_conjecture_3bTab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `806` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 806 2

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
  have hnd := noDiv_sound p 806 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [x, y, z] => (decide (0 < x) && (decide (0 < y) && (decide (0 < z) && (decide (x + y + z = n) && ((decide (x = 1) || (decide (x = 2) || decide (x = 3))) && (isPrimeB (2 * x + 1) && (isPrimeB (2 * y + 1) && (isPrimeB (2 * z + 1) && isPrimeB (2 * x * y * z + 1)))))))))
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
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      x ∈ ({1, 2, 3} : Finset ℕ) ∧
      (2 * x + 1).Prime ∧ (2 * y + 1).Prime ∧ (2 * z + 1).Prime ∧
      (2 * x * y * z + 1).Prime := by
  unfold core at h
  split at h
  next x y z =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
    exact ⟨x, y, z, a0, a1, a2, a3, (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact a4), isPrimeB_sound _ a5, isPrimeB_sound _ a6, isPrimeB_sound _ a7, isPrimeB_sound _ a8⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 3, …, 1002`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[1, 1, 1], [1, 1, 2], [1, 1, 3], [1, 2, 3], [1, 1, 5], [1, 1, 6], [1, 3, 5], [1, 1, 8], [1, 1, 9], [1, 2, 9], [1, 1, 11], [2, 3, 9], [1, 3, 11], [1, 1, 14], [1, 1, 15], [1, 2, 15], [1, 9, 9], [1, 1, 18], [1, 2, 18], [1, 1, 20], [1, 1, 21], [1, 5, 18], [1, 1, 23], [2, 6, 18], [1, 3, 23]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 3 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[1, 1, 26], [3, 5, 21], [1, 3, 26], [1, 1, 29], [1, 1, 30], [1, 6, 26], [1, 3, 30], [1, 1, 33], [1, 6, 29], [1, 1, 35], [1, 1, 36], [1, 3, 35], [1, 6, 33], [1, 1, 39], [1, 2, 39], [1, 1, 41], [3, 15, 26], [1, 8, 36], [1, 1, 44], [2, 6, 39], [1, 21, 26], [1, 15, 33], [1, 1, 48], [1, 2, 48], [1, 1, 50]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 28 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[1, 1, 51], [1, 14, 39], [1, 1, 53], [1, 1, 54], [1, 6, 50], [1, 1, 56], [3, 5, 51], [1, 3, 56], [1, 9, 51], [2, 6, 54], [1, 6, 56], [2, 14, 48], [1, 1, 63], [1, 9, 56], [1, 1, 65], [2, 3, 63], [1, 5, 63], [1, 1, 68], [1, 1, 69], [1, 2, 69], [1, 21, 51], [2, 3, 69], [1, 5, 69], [1, 1, 74], [1, 1, 75]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 53 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[1, 36, 41], [2, 2, 75], [1, 1, 78], [1, 2, 78], [1, 18, 63], [1, 1, 81], [1, 8, 75], [1, 1, 83], [2, 6, 78], [1, 3, 83], [1, 1, 86], [2, 18, 69], [1, 6, 83], [1, 1, 89], [1, 1, 90], [1, 6, 86], [1, 3, 90], [2, 30, 63], [1, 6, 89], [1, 1, 95], [1, 1, 96], [1, 3, 95], [1, 1, 98], [1, 1, 99], [1, 2, 99]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 78 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[1, 6, 96], [2, 33, 69], [1, 5, 99], [1, 36, 69], [1, 1, 105], [1, 2, 105], [1, 3, 105], [2, 18, 90], [1, 5, 105], [1, 30, 81], [1, 1, 111], [1, 44, 69], [1, 1, 113], [1, 1, 114], [1, 2, 114], [1, 1, 116], [2, 18, 99], [1, 8, 111], [1, 1, 119], [1, 1, 120], [1, 26, 96], [1, 9, 114], [2, 18, 105], [1, 5, 120], [1, 1, 125]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 103 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[2, 15, 111], [1, 3, 125], [1, 1, 128], [2, 15, 114], [1, 3, 128], [1, 1, 131], [2, 18, 114], [1, 3, 131], [1, 1, 134], [1, 1, 135], [1, 2, 135], [1, 3, 135], [1, 1, 138], [1, 6, 134], [1, 1, 140], [1, 1, 141], [1, 5, 138], [1, 6, 138], [2, 3, 141], [1, 11, 135], [1, 1, 146], [2, 9, 138], [1, 3, 146], [1, 9, 141], [2, 9, 141]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 128 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[1, 6, 146], [1, 18, 135], [1, 1, 153], [1, 2, 153], [1, 1, 155], [1, 1, 156], [1, 5, 153], [1, 1, 158], [2, 3, 156], [1, 6, 155], [1, 6, 156], [3, 6, 155], [1, 9, 155], [1, 30, 135], [1, 1, 165], [1, 2, 165], [1, 3, 165], [1, 1, 168], [1, 2, 168], [1, 3, 168], [2, 3, 168], [1, 18, 155], [1, 1, 173], [1, 1, 174], [1, 3, 173]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 153 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[1, 1, 176], [2, 3, 174], [1, 5, 174], [1, 1, 179], [2, 6, 174], [1, 6, 176], [1, 30, 153], [1, 1, 183], [1, 2, 183], [1, 33, 153], [1, 1, 186], [1, 5, 183], [1, 3, 186], [1, 1, 189], [1, 2, 189], [1, 1, 191], [2, 3, 189], [1, 11, 183], [1, 1, 194], [2, 30, 165], [1, 6, 191], [1, 33, 165], [1, 1, 198], [1, 11, 189], [1, 1, 200]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 178 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[2, 3, 198], [1, 3, 200], [1, 6, 198], [1, 1, 204], [1, 8, 198], [1, 51, 156], [2, 9, 198], [1, 11, 198], [1, 1, 209], [1, 1, 210], [1, 96, 116], [1, 9, 204], [2, 3, 210], [1, 26, 189], [1, 1, 215], [1, 1, 216], [1, 3, 215], [1, 3, 216], [1, 1, 219], [1, 2, 219], [1, 1, 221], [2, 39, 183], [1, 3, 221], [1, 1, 224], [2, 15, 210]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 203 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[1, 96, 131], [1, 9, 219], [1, 1, 228], [1, 6, 224], [1, 1, 230], [1, 1, 231], [1, 3, 230], [1, 1, 233], [2, 30, 204], [1, 3, 233], [1, 51, 186], [2, 9, 228], [1, 6, 233], [1, 1, 239], [2, 9, 231], [1, 21, 221], [1, 15, 228], [1, 1, 243], [1, 14, 231], [1, 1, 245], [2, 3, 243], [1, 3, 245], [1, 6, 243], [1, 1, 249], [1, 2, 249]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 228 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[1, 1, 251], [2, 33, 219], [1, 11, 243], [1, 1, 254], [2, 51, 204], [1, 36, 221], [1, 9, 249], [2, 30, 228], [1, 6, 254], [1, 1, 260], [1, 1, 261], [1, 18, 245], [1, 3, 261], [2, 33, 231], [1, 6, 260], [1, 36, 231], [2, 18, 249], [1, 8, 261], [1, 21, 249], [1, 1, 270], [1, 11, 261], [1, 3, 270], [1, 1, 273], [1, 2, 273], [1, 120, 156]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 253 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[2, 6, 270], [1, 5, 273], [1, 1, 278], [2, 6, 273], [1, 3, 278], [1, 1, 281], [2, 9, 273], [1, 11, 273], [1, 1, 284], [1, 1, 285], [1, 6, 281], [1, 15, 273], [1, 1, 288], [1, 2, 288], [1, 18, 273], [2, 3, 288], [1, 8, 285], [1, 1, 293], [2, 75, 219], [1, 3, 293], [1, 1, 296], [2, 9, 288], [1, 3, 296], [1, 1, 299], [1, 1, 300]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 278 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[1, 2, 300], [1, 3, 300], [1, 1, 303], [1, 2, 303], [1, 18, 288], [1, 1, 306], [1, 8, 300], [1, 1, 308], [1, 1, 309], [1, 2, 309], [1, 6, 306], [2, 3, 309], [1, 6, 308], [1, 6, 309], [1, 1, 315], [1, 11, 306], [1, 9, 309], [2, 15, 303], [1, 99, 221], [1, 1, 320], [1, 1, 321], [1, 15, 308], [1, 1, 323], [2, 3, 321], [1, 20, 306]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 303 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[1, 1, 326], [2, 78, 249], [1, 6, 323], [1, 1, 329], [1, 1, 330], [1, 2, 330], [1, 30, 303], [2, 48, 285], [1, 5, 330], [1, 15, 321], [1, 1, 336], [1, 8, 330], [1, 1, 338], [2, 36, 303], [1, 3, 338], [1, 1, 341], [2, 39, 303], [1, 6, 338], [1, 15, 330], [1, 1, 345], [1, 2, 345], [1, 39, 309], [2, 18, 330], [1, 35, 315], [1, 1, 350]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 328 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[2, 15, 336], [1, 8, 345], [1, 9, 345], [1, 1, 354], [1, 6, 350], [1, 141, 216], [2, 54, 303], [1, 5, 354], [1, 1, 359], [2, 39, 321], [1, 21, 341], [1, 9, 354], [1, 1, 363], [1, 2, 363], [1, 3, 363], [1, 1, 366], [1, 5, 363], [1, 6, 363], [1, 1, 369], [1, 41, 330], [1, 1, 371], [2, 99, 273], [1, 5, 369], [1, 21, 354], [1, 1, 375]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 353 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[1, 11, 366], [1, 3, 375], [1, 1, 378], [1, 9, 371], [1, 1, 380], [2, 6, 375], [1, 3, 380], [1, 15, 369], [1, 1, 384], [1, 6, 380], [1, 1, 386], [2, 114, 273], [1, 9, 380], [1, 15, 375], [2, 15, 375], [1, 21, 371], [1, 90, 303], [1, 1, 393], [1, 9, 386], [1, 30, 366], [2, 33, 363], [1, 5, 393], [1, 1, 398], [2, 6, 393], [1, 3, 398]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 378 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[2, 8, 393], [2, 9, 393], [1, 11, 393], [1, 1, 404], [1, 1, 405], [1, 2, 405], [1, 78, 330], [2, 3, 405], [1, 5, 405], [1, 1, 410], [1, 1, 411], [1, 8, 405], [1, 1, 413], [1, 1, 414], [1, 2, 414], [1, 6, 411], [2, 3, 414], [1, 6, 413], [1, 1, 419], [2, 9, 411], [1, 11, 411], [1, 30, 393], [2, 30, 393], [1, 11, 414], [1, 21, 405]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 403 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[1, 1, 426], [1, 14, 414], [1, 1, 428], [1, 1, 429], [1, 5, 426], [1, 1, 431], [2, 54, 378], [1, 20, 414], [1, 9, 426], [2, 120, 315], [1, 51, 386], [1, 9, 429], [1, 1, 438], [1, 2, 438], [1, 1, 440], [1, 1, 441], [1, 15, 428], [1, 1, 443], [2, 6, 438], [1, 3, 443], [1, 141, 306], [2, 63, 384], [1, 8, 441], [1, 39, 411], [2, 9, 441]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 428 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[1, 26, 426], [1, 75, 378], [1, 1, 453], [1, 29, 426], [1, 1, 455], [2, 3, 453], [1, 3, 455], [1, 6, 453], [1, 1, 459], [1, 21, 440], [1, 21, 441], [2, 33, 429], [1, 5, 459], [1, 1, 464], [2, 39, 426], [1, 36, 431], [1, 9, 459], [1, 1, 468], [1, 2, 468], [1, 1, 470], [2, 156, 315], [1, 9, 464], [1, 1, 473], [2, 15, 459], [1, 6, 470]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 453 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[1, 1, 476], [2, 18, 459], [1, 3, 476], [1, 51, 429], [2, 21, 459], [1, 51, 431], [1, 120, 363], [1, 1, 483], [1, 2, 483], [1, 1, 485], [2, 33, 453], [1, 5, 483], [1, 1, 488], [2, 6, 483], [1, 6, 485], [1, 1, 491], [2, 9, 483], [1, 6, 488], [1, 36, 459], [1, 1, 495], [1, 21, 476], [1, 3, 495], [1, 1, 498], [1, 2, 498], [1, 18, 483]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 478 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[2, 96, 405], [1, 63, 440], [1, 21, 483], [1, 1, 504], [1, 2, 504], [1, 1, 506], [2, 9, 498], [1, 3, 506], [1, 1, 509], [1, 1, 510], [1, 6, 506], [1, 3, 510], [2, 3, 510], [1, 5, 510], [1, 1, 515], [1, 1, 516], [1, 8, 510], [1, 9, 510], [1, 1, 519], [1, 26, 495], [1, 81, 441], [2, 3, 519], [1, 14, 510], [1, 1, 524], [1, 1, 525]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 503 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[1, 11, 516], [1, 9, 519], [2, 3, 525], [1, 14, 516], [1, 1, 530], [1, 1, 531], [1, 3, 530], [1, 3, 531], [1, 1, 534], [1, 2, 534], [1, 6, 531], [2, 18, 519], [1, 29, 510], [1, 21, 519], [2, 21, 519], [1, 26, 516], [1, 9, 534], [1, 1, 543], [1, 14, 531], [1, 1, 545], [1, 1, 546], [1, 3, 545], [1, 1, 548], [2, 3, 546], [1, 8, 543]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 528 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[1, 1, 551], [2, 18, 534], [1, 3, 551], [1, 1, 554], [2, 219, 336], [1, 51, 506], [1, 33, 525], [1, 1, 558], [1, 14, 546], [1, 15, 546], [1, 1, 561], [1, 5, 558], [1, 21, 543], [1, 1, 564], [1, 8, 558], [1, 6, 561], [2, 9, 558], [1, 5, 564], [1, 9, 561], [2, 6, 564], [1, 11, 561], [1, 15, 558], [2, 48, 525], [1, 11, 564], [1, 1, 575]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 553 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[1, 1, 576], [1, 35, 543], [1, 3, 576], [2, 33, 546], [1, 20, 561], [1, 1, 581], [2, 18, 564], [1, 26, 558], [1, 9, 576], [1, 1, 585], [1, 2, 585], [1, 3, 585], [2, 90, 498], [1, 5, 585], [1, 1, 590], [2, 138, 453], [1, 3, 590], [1, 1, 593], [2, 9, 585], [1, 3, 593], [1, 1, 596], [2, 33, 564], [1, 14, 585], [1, 15, 585], [1, 1, 600]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 578 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[1, 56, 546], [1, 18, 585], [2, 120, 483], [1, 9, 596], [1, 21, 585], [1, 1, 606], [1, 8, 600], [1, 1, 608], [2, 9, 600], [1, 15, 596], [1, 1, 611], [2, 48, 564], [1, 6, 608], [1, 1, 614], [1, 1, 615], [1, 6, 611], [1, 3, 615], [1, 1, 618], [1, 2, 618], [1, 3, 618], [2, 3, 618], [1, 48, 575], [1, 6, 618], [1, 1, 624], [1, 33, 593]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 603 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[1, 21, 606], [2, 3, 624], [1, 11, 618], [1, 1, 629], [2, 15, 615], [1, 26, 606], [1, 15, 618], [2, 18, 615], [1, 6, 629], [1, 36, 600], [2, 18, 618], [1, 53, 585], [1, 1, 638], [1, 1, 639], [1, 2, 639], [1, 1, 641], [2, 3, 639], [1, 3, 641], [1, 1, 644], [1, 1, 645], [1, 51, 596], [1, 9, 639], [1, 1, 648], [1, 2, 648], [1, 1, 650]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 628 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[1, 1, 651], [1, 5, 648], [1, 1, 653], [2, 36, 618], [1, 3, 653], [1, 51, 606], [2, 114, 543], [1, 9, 650], [1, 1, 659], [1, 1, 660], [1, 11, 651], [1, 15, 648], [1, 1, 663], [1, 14, 651], [1, 15, 651], [2, 21, 645], [1, 9, 659], [1, 153, 516], [2, 6, 663], [1, 18, 653], [1, 111, 561], [2, 9, 663], [1, 14, 660], [1, 15, 660], [2, 51, 624]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 653 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[1, 36, 641], [1, 15, 663], [2, 18, 660], [1, 39, 641], [1, 1, 680], [2, 18, 663], [1, 30, 653], [1, 1, 683], [2, 33, 651], [1, 3, 683], [1, 1, 686], [2, 39, 648], [1, 9, 680], [1, 51, 639], [1, 1, 690], [1, 6, 686], [1, 69, 624], [2, 30, 663], [1, 56, 639], [1, 33, 663], [2, 6, 690], [1, 18, 680], [1, 9, 690], [1, 1, 699], [1, 2, 699]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 678 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[1, 51, 651], [2, 3, 699], [1, 5, 699], [1, 1, 704], [2, 54, 651], [1, 21, 686], [1, 9, 699], [2, 18, 690], [1, 30, 680], [1, 48, 663], [1, 1, 711], [1, 23, 690], [1, 1, 713], [1, 1, 714], [1, 2, 714], [1, 1, 716], [2, 18, 699], [1, 3, 716], [1, 1, 719], [2, 6, 714], [1, 11, 711], [1, 9, 714], [1, 1, 723], [1, 6, 719], [1, 1, 725]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 703 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[1, 1, 726], [1, 14, 714], [1, 3, 726], [1, 1, 729], [1, 2, 729], [1, 6, 726], [2, 9, 723], [1, 8, 726], [1, 21, 714], [1, 1, 735], [1, 11, 726], [1, 138, 600], [2, 3, 735], [1, 5, 735], [1, 1, 740], [1, 1, 741], [1, 3, 740], [1, 1, 743], [1, 1, 744], [1, 5, 741], [1, 1, 746], [2, 3, 744], [1, 90, 659], [1, 1, 749], [2, 15, 735]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 728 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[1, 176, 576], [1, 135, 618], [2, 90, 663], [1, 11, 744], [1, 1, 755], [2, 30, 726], [1, 15, 743], [1, 33, 726], [2, 15, 744], [1, 15, 746], [1, 1, 761], [2, 18, 744], [1, 3, 761], [1, 21, 744], [1, 1, 765], [1, 2, 765], [1, 3, 765], [2, 3, 765], [1, 15, 755], [1, 6, 765], [1, 1, 771], [1, 8, 765], [1, 30, 744], [1, 1, 774], [1, 11, 765]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 753 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[1, 1, 776], [2, 48, 729], [1, 3, 776], [1, 1, 779], [2, 36, 744], [1, 11, 771], [1, 9, 774], [1, 1, 783], [1, 6, 779], [1, 1, 785], [2, 3, 783], [1, 14, 774], [1, 6, 783], [1, 1, 789], [1, 6, 785], [1, 1, 791], [2, 63, 729], [1, 15, 779], [1, 69, 726], [2, 30, 765], [1, 26, 771], [1, 99, 699], [1, 1, 798], [1, 11, 789], [1, 1, 800]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 778 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[2, 18, 783], [1, 3, 800], [1, 1, 803], [1, 1, 804], [1, 2, 804], [1, 1, 806], [2, 3, 804], [1, 9, 800], [1, 1, 809], [1, 1, 810], [1, 21, 791], [1, 3, 810], [1, 1, 813], [1, 2, 813], [1, 6, 810], [2, 6, 810], [1, 9, 809], [1, 1, 818], [2, 21, 798], [1, 3, 818], [1, 51, 771], [2, 9, 813], [1, 6, 818], [1, 21, 804], [2, 21, 804]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 803 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[1, 51, 776], [1, 15, 813], [1, 1, 828], [1, 2, 828], [1, 3, 828], [1, 1, 831], [1, 29, 804], [1, 1, 833], [1, 1, 834], [1, 3, 833], [1, 6, 831], [2, 3, 834], [1, 8, 831], [1, 6, 834], [2, 9, 831], [1, 51, 791], [1, 9, 834], [2, 15, 828], [1, 14, 831], [1, 36, 810], [1, 1, 846], [1, 30, 818], [1, 1, 848], [1, 1, 849], [1, 5, 846]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 828 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[1, 111, 741], [2, 48, 804], [1, 6, 848], [1, 1, 854], [2, 81, 774], [1, 296, 561], [1, 30, 828], [2, 48, 810], [1, 11, 849], [1, 1, 860], [1, 1, 861], [1, 9, 854], [1, 3, 861], [2, 3, 861], [1, 6, 860], [1, 1, 866], [2, 18, 849], [1, 3, 866], [1, 81, 789], [1, 1, 870], [1, 111, 761], [1, 39, 834], [1, 1, 873], [1, 14, 861], [1, 78, 798]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 853 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[1, 1, 876], [1, 5, 873], [1, 6, 873], [1, 1, 879], [1, 2, 879], [1, 6, 876], [2, 33, 849], [1, 11, 873], [1, 36, 849], [2, 15, 870], [1, 11, 876], [1, 9, 879], [1, 1, 888], [1, 29, 861], [1, 21, 870], [1, 1, 891], [1, 44, 849], [1, 1, 893], [1, 1, 894], [1, 35, 861], [1, 21, 876], [2, 3, 894], [1, 5, 894], [1, 6, 894], [1, 1, 900]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 878 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[1, 11, 891], [1, 15, 888], [2, 15, 888], [1, 5, 900], [1, 1, 905], [2, 6, 900], [1, 3, 905], [1, 15, 894], [2, 9, 900], [1, 6, 905], [1, 1, 911], [2, 39, 873], [1, 21, 893], [1, 21, 894], [1, 1, 915], [1, 111, 806], [1, 18, 900], [2, 105, 813], [1, 5, 915], [1, 51, 870], [2, 6, 915], [1, 29, 894], [1, 1, 923], [2, 9, 915], [1, 21, 905]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 903 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[1, 36, 891], [2, 48, 879], [1, 14, 915], [1, 30, 900], [1, 1, 930], [1, 41, 891], [1, 3, 930], [1, 1, 933], [1, 2, 933], [1, 1, 935], [1, 1, 936], [1, 15, 923], [1, 1, 938], [1, 1, 939], [1, 8, 933], [1, 81, 861], [2, 9, 933], [1, 5, 939], [1, 1, 944], [2, 135, 810], [1, 11, 936], [1, 9, 939], [2, 48, 900], [1, 6, 944], [1, 1, 950]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 928 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[2, 21, 930], [1, 3, 950], [1, 1, 953], [2, 78, 876], [1, 18, 938], [1, 1, 956], [2, 63, 894], [1, 3, 956], [1, 21, 939], [2, 21, 939], [1, 26, 936], [1, 33, 930], [2, 33, 930], [1, 9, 956], [1, 1, 965], [1, 1, 966], [1, 3, 965], [1, 120, 849], [2, 3, 966], [1, 5, 966], [1, 6, 966], [2, 39, 933], [1, 35, 939], [1, 1, 974], [1, 1, 975]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 953 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[1, 21, 956], [1, 3, 975], [2, 3, 975], [1, 6, 974], [1, 6, 975], [2, 210, 771], [1, 8, 975], [1, 9, 975], [2, 54, 930], [1, 21, 965], [1, 1, 986], [2, 48, 939], [1, 15, 974], [1, 1, 989], [2, 99, 891], [1, 6, 986], [1, 99, 894], [1, 1, 993], [1, 9, 986], [1, 96, 900], [1, 1, 996], [1, 5, 993], [1, 1, 998], [1, 1, 999], [1, 8, 993]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 978 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `3 ≤ n ≤ 1002` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 3 ≤ n) (h2 : n ≤ 1002) : ∃ x, good n x = true := by
  by_cases c0 : n < 28
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 53
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 78
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 103
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 128
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 153
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 178
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 203
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 228
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 253
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 278
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 303
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 328
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 353
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 378
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 403
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 428
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 453
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 478
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 503
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 528
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 553
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 578
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 603
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 628
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 653
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 678
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 703
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 728
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 753
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 778
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 803
  · exact chunk ok31 len31 (by omega) (by omega)
  by_cases c32 : n < 828
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 853
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 878
  · exact chunk ok34 len34 (by omega) (by omega)
  by_cases c35 : n < 903
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 928
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 953
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 978
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.AOeisA229969_conjecture_3bTab

open OMA.AOeisA229969_conjecture_3bTab in
theorem OMA.solution : OMA.R_OeisA229969_conjecture_3b_R1.H1 := by
  intro n hn hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
