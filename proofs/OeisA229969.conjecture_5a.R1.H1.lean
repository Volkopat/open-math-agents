import OMAReductions.R_OeisA229969_conjecture_5a_R1
import Mathlib

-- Step OeisA229969.conjecture_5a.R1.H1: hypothesis H1 of reduction OeisA229969.conjecture_5a.R1
-- Credit: @prathameshnium. Finite check for 6 ≤ n ≤ 1005.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 175391.

/-! Step OeisA229969.conjecture_5a.R1.H1. -/

namespace OMA.AOeisA229969_conjecture_5aTab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `420` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 420 2

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
  have hnd := noDiv_sound p 420 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [x, y, z] => (decide (0 < x) && (decide (0 < y) && (decide (0 < z) && (decide (x + y + z = n) && ((decide (x = 2) || (decide (x = 6) || decide (x = 10))) && (isPrimeB (x * y - 1) && (isPrimeB (x * z - 1) && isPrimeB (y * z - 1))))))))
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
      x ∈ ({2, 6, 10} : Finset ℕ) ∧
      (x * y - 1).Prime ∧ (x * z - 1).Prime ∧ (y * z - 1).Prime := by
  unfold core at h
  split at h
  next x y z =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
    exact ⟨x, y, z, a0, a1, a2, a3, (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact a4), isPrimeB_sound _ a5, isPrimeB_sound _ a6, isPrimeB_sound _ a7⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 6, …, 1005`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[2, 2, 2], [2, 2, 3], [2, 2, 4], [2, 3, 4], [2, 2, 6], [2, 2, 7], [2, 4, 6], [2, 2, 9], [2, 2, 10], [2, 3, 10], [2, 2, 12], [2, 6, 9], [2, 4, 12], [2, 2, 15], [2, 2, 16], [2, 3, 16], [6, 4, 12], [2, 2, 19], [6, 8, 10], [2, 2, 21], [2, 2, 22], [2, 4, 21], [2, 2, 24], [2, 3, 24], [2, 6, 22]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 6 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[2, 2, 27], [6, 12, 14], [2, 4, 27], [2, 2, 30], [2, 2, 31], [2, 10, 24], [6, 1, 30], [2, 2, 34], [2, 3, 34], [2, 2, 36], [2, 2, 37], [2, 16, 24], [6, 4, 33], [2, 2, 40], [2, 7, 36], [2, 2, 42], [2, 15, 30], [2, 4, 42], [2, 2, 45], [2, 6, 42], [2, 4, 45], [6, 4, 42], [2, 2, 49], [2, 10, 42], [2, 2, 51]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 31 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[2, 2, 52], [2, 6, 49], [2, 2, 54], [2, 2, 55], [2, 6, 52], [2, 2, 57], [2, 24, 36], [2, 4, 57], [6, 18, 40], [2, 21, 42], [2, 30, 34], [6, 1, 60], [2, 2, 64], [2, 3, 64], [2, 2, 66], [2, 3, 66], [2, 4, 66], [2, 2, 69], [2, 2, 70], [2, 7, 66], [6, 10, 60], [2, 9, 66], [2, 6, 70], [2, 2, 75], [2, 2, 76]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 56 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[2, 3, 76], [10, 24, 48], [2, 2, 79], [2, 12, 70], [6, 7, 72], [2, 2, 82], [2, 9, 76], [2, 2, 84], [2, 3, 84], [2, 6, 82], [2, 2, 87], [2, 6, 84], [2, 4, 87], [2, 2, 90], [2, 2, 91], [2, 4, 90], [6, 4, 87], [2, 30, 66], [2, 15, 82], [2, 2, 96], [2, 2, 97], [2, 4, 96], [2, 2, 99], [2, 2, 100], [2, 12, 91]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 81 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[6, 30, 70], [2, 6, 99], [2, 6, 100], [6, 10, 93], [2, 2, 106], [2, 3, 106], [6, 22, 84], [2, 12, 99], [2, 22, 90], [6, 1, 108], [2, 2, 112], [2, 9, 106], [2, 2, 114], [2, 2, 115], [2, 22, 96], [2, 2, 117], [2, 6, 114], [2, 4, 117], [2, 2, 120], [2, 2, 121], [2, 4, 120], [6, 4, 117], [2, 6, 120], [2, 7, 120], [2, 2, 126]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 106 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[2, 15, 114], [2, 4, 126], [2, 2, 129], [2, 12, 120], [2, 7, 126], [2, 2, 132], [2, 6, 129], [2, 10, 126], [2, 2, 135], [2, 2, 136], [2, 10, 129], [6, 12, 124], [2, 2, 139], [2, 10, 132], [2, 2, 141], [2, 2, 142], [2, 4, 141], [6, 28, 114], [2, 12, 135], [2, 16, 132], [2, 2, 147], [2, 24, 126], [2, 4, 147], [6, 28, 120], [2, 6, 147]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 131 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[2, 22, 132], [6, 3, 148], [2, 2, 154], [2, 3, 154], [2, 2, 156], [2, 2, 157], [2, 34, 126], [2, 2, 159], [2, 42, 120], [2, 6, 157], [6, 40, 120], [2, 6, 159], [2, 10, 156], [6, 25, 138], [2, 2, 166], [2, 15, 154], [6, 4, 162], [2, 2, 169], [2, 30, 142], [6, 42, 127], [2, 84, 90], [2, 6, 169], [2, 2, 174], [2, 2, 175], [2, 42, 136]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 156 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[2, 2, 177], [2, 54, 126], [2, 6, 175], [2, 2, 180], [2, 6, 177], [2, 4, 180], [6, 12, 169], [2, 2, 184], [2, 7, 180], [6, 12, 172], [2, 2, 187], [2, 6, 184], [6, 12, 175], [2, 2, 190], [2, 3, 190], [2, 2, 192], [2, 15, 180], [2, 12, 184], [2, 2, 195], [2, 6, 192], [2, 9, 190], [6, 12, 184], [2, 2, 199], [2, 70, 132], [2, 2, 201]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 181 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[2, 84, 120], [2, 6, 199], [6, 64, 138], [2, 2, 205], [2, 42, 166], [10, 3, 198], [2, 30, 180], [2, 6, 205], [2, 2, 210], [2, 2, 211], [2, 4, 210], [6, 7, 204], [2, 6, 210], [2, 12, 205], [2, 2, 216], [2, 2, 217], [2, 4, 216], [6, 3, 214], [2, 2, 220], [2, 3, 220], [2, 2, 222], [2, 30, 195], [2, 4, 222], [2, 2, 225], [2, 12, 216]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 206 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[2, 7, 222], [6, 42, 184], [2, 2, 229], [6, 8, 220], [2, 2, 231], [2, 2, 232], [2, 6, 229], [2, 2, 234], [2, 3, 234], [2, 22, 216], [6, 15, 220], [2, 30, 210], [2, 7, 234], [2, 2, 240], [2, 3, 240], [2, 10, 234], [6, 1, 240], [2, 2, 244], [2, 27, 220], [2, 2, 246], [2, 24, 225], [2, 4, 246], [6, 9, 238], [2, 2, 250], [2, 7, 246]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 231 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[2, 2, 252], [2, 9, 246], [2, 6, 250], [2, 2, 255], [2, 6, 252], [2, 4, 255], [6, 18, 238], [2, 9, 252], [2, 12, 250], [2, 2, 261], [2, 2, 262], [2, 10, 255], [6, 12, 250], [2, 15, 252], [2, 6, 262], [6, 1, 264], [2, 24, 246], [2, 9, 262], [6, 28, 240], [2, 2, 271], [2, 42, 232], [6, 1, 270], [2, 2, 274], [2, 3, 274], [10, 24, 246]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 256 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[2, 27, 252], [2, 30, 250], [2, 2, 279], [2, 30, 252], [2, 12, 271], [2, 2, 282], [2, 24, 261], [2, 24, 262], [2, 2, 285], [2, 2, 286], [2, 3, 286], [6, 22, 264], [2, 2, 289], [2, 10, 282], [6, 25, 264], [2, 54, 240], [2, 6, 289], [2, 2, 294], [2, 3, 294], [2, 36, 262], [2, 2, 297], [2, 66, 234], [2, 4, 297], [2, 2, 300], [2, 2, 301]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 281 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[2, 10, 294], [6, 12, 289], [2, 2, 304], [2, 3, 304], [6, 40, 264], [2, 2, 307], [2, 6, 304], [2, 2, 309], [2, 2, 310], [2, 3, 310], [6, 40, 270], [2, 21, 294], [2, 16, 300], [6, 1, 312], [2, 2, 316], [2, 3, 316], [6, 64, 252], [2, 21, 300], [2, 12, 310], [2, 2, 321], [2, 2, 322], [2, 4, 321], [2, 2, 324], [2, 3, 324], [2, 6, 322]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 306 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[2, 2, 327], [2, 30, 300], [2, 4, 327], [2, 2, 330], [2, 2, 331], [2, 4, 330], [6, 9, 322], [2, 6, 330], [2, 7, 330], [6, 4, 330], [2, 2, 337], [2, 10, 330], [2, 2, 339], [2, 90, 252], [2, 16, 327], [2, 2, 342], [2, 21, 324], [2, 4, 342], [6, 3, 340], [2, 2, 346], [2, 7, 342], [6, 12, 334], [2, 27, 324], [2, 70, 282], [2, 2, 351]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 331 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[2, 24, 330], [2, 54, 301], [6, 12, 340], [2, 2, 355], [2, 16, 342], [6, 10, 345], [2, 66, 294], [2, 6, 355], [2, 2, 360], [2, 12, 351], [2, 4, 360], [6, 4, 357], [2, 2, 364], [2, 3, 364], [6, 42, 322], [2, 2, 367], [2, 66, 304], [6, 12, 355], [2, 2, 370], [2, 3, 370], [2, 2, 372], [2, 15, 360], [2, 4, 372], [6, 18, 355], [2, 2, 376]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 356 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[2, 9, 370], [6, 28, 348], [2, 2, 379], [2, 10, 372], [2, 2, 381], [2, 12, 372], [2, 4, 381], [6, 4, 378], [2, 2, 385], [2, 156, 232], [2, 2, 387], [2, 30, 360], [2, 6, 385], [6, 10, 378], [2, 42, 351], [2, 34, 360], [6, 1, 390], [2, 2, 394], [2, 3, 394], [6, 4, 390], [2, 12, 387], [2, 36, 364], [2, 2, 399], [2, 30, 372], [2, 27, 376]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 381 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[6, 60, 340], [2, 6, 399], [2, 30, 376], [2, 2, 405], [2, 2, 406], [2, 3, 406], [6, 4, 402], [2, 12, 399], [2, 40, 372], [2, 2, 411], [2, 2, 412], [2, 10, 405], [2, 2, 414], [2, 2, 415], [2, 12, 406], [6, 25, 390], [2, 120, 300], [2, 7, 414], [2, 2, 420], [2, 3, 420], [2, 10, 414], [6, 18, 403], [2, 12, 414], [2, 7, 420], [6, 72, 352]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 406 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[2, 2, 427], [2, 24, 406], [2, 2, 429], [2, 2, 430], [2, 3, 430], [2, 2, 432], [2, 15, 420], [2, 6, 430], [6, 1, 432], [2, 6, 432], [2, 7, 432], [6, 12, 424], [2, 2, 439], [2, 22, 420], [2, 2, 441], [2, 2, 442], [2, 6, 439], [2, 2, 444], [2, 87, 360], [2, 16, 432], [6, 1, 444], [2, 6, 444], [2, 10, 441], [6, 40, 408], [2, 66, 387]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 431 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[2, 12, 442], [6, 1, 450], [2, 2, 454], [2, 3, 454], [2, 2, 456], [2, 3, 456], [2, 4, 456], [6, 18, 439], [2, 2, 460], [2, 7, 456], [6, 30, 430], [2, 21, 444], [2, 22, 444], [2, 2, 465], [2, 12, 456], [2, 9, 460], [6, 22, 444], [2, 2, 469], [2, 12, 460], [2, 2, 471], [2, 42, 432], [2, 10, 465], [2, 2, 474], [6, 3, 470], [2, 66, 412]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 456 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[2, 2, 477], [2, 6, 474], [2, 4, 477], [6, 70, 408], [2, 6, 477], [2, 30, 454], [6, 1, 480], [2, 2, 484], [2, 3, 484], [2, 2, 486], [2, 15, 474], [2, 6, 484], [2, 2, 489], [2, 210, 282], [2, 37, 456], [2, 2, 492], [2, 9, 486], [2, 12, 484], [6, 58, 435], [2, 2, 496], [2, 3, 496], [6, 12, 484], [2, 2, 499], [2, 10, 492], [6, 4, 495]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 481 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[2, 12, 492], [2, 9, 496], [6, 12, 490], [2, 2, 505], [2, 22, 486], [2, 2, 507], [2, 54, 456], [2, 4, 507], [2, 2, 510], [2, 2, 511], [2, 4, 510], [6, 4, 507], [2, 24, 492], [2, 40, 477], [2, 2, 516], [2, 2, 517], [2, 4, 516], [6, 15, 502], [2, 2, 520], [2, 3, 520], [6, 30, 490], [2, 9, 516], [2, 6, 520], [2, 2, 525], [2, 2, 526]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 506 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[2, 4, 525], [6, 22, 504], [2, 21, 510], [2, 90, 442], [2, 2, 531], [2, 2, 532], [2, 9, 526], [6, 4, 528], [2, 2, 535], [2, 6, 532], [6, 100, 435], [2, 30, 510], [2, 6, 535], [6, 10, 528], [2, 27, 516], [2, 24, 520], [6, 9, 532], [2, 2, 544], [2, 22, 525], [2, 2, 546], [2, 2, 547], [2, 40, 510], [2, 2, 549], [2, 42, 510], [2, 7, 546]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 531 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[2, 2, 552], [2, 24, 531], [2, 4, 552], [2, 2, 555], [2, 12, 546], [2, 7, 552], [6, 28, 528], [2, 2, 559], [2, 10, 552], [6, 1, 558], [2, 2, 562], [2, 16, 549], [6, 12, 550], [2, 2, 565], [2, 6, 562], [6, 45, 520], [2, 24, 546], [2, 6, 565], [6, 78, 490], [2, 27, 546], [2, 22, 552], [6, 39, 532], [2, 156, 420], [2, 12, 565], [2, 2, 576]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 556 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[2, 2, 577], [2, 36, 544], [6, 12, 565], [2, 90, 492], [2, 6, 577], [2, 2, 582], [2, 30, 555], [2, 24, 562], [6, 18, 565], [2, 2, 586], [2, 7, 582], [6, 18, 568], [2, 9, 582], [2, 40, 552], [2, 2, 591], [2, 12, 582], [2, 9, 586], [2, 2, 594], [2, 132, 465], [2, 16, 582], [2, 2, 597], [2, 54, 546], [2, 7, 594], [6, 10, 588], [2, 2, 601]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 581 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[2, 10, 594], [6, 19, 582], [2, 12, 594], [2, 52, 555], [6, 42, 562], [2, 2, 607], [2, 34, 576], [2, 2, 609], [2, 282, 330], [2, 12, 601], [2, 2, 612], [2, 21, 594], [2, 4, 612], [2, 2, 615], [2, 2, 616], [2, 3, 616], [6, 4, 612], [2, 2, 619], [2, 40, 582], [6, 7, 612], [2, 42, 582], [2, 16, 609], [6, 40, 582], [2, 2, 625], [2, 16, 612]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 606 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[6, 240, 385], [2, 36, 594], [2, 15, 616], [2, 2, 630], [2, 3, 630], [2, 22, 612], [6, 28, 603], [2, 6, 630], [2, 7, 630], [6, 22, 612], [2, 9, 630], [2, 10, 630], [2, 2, 639], [2, 2, 640], [2, 27, 616], [2, 2, 642], [2, 6, 639], [2, 16, 630], [2, 2, 645], [2, 2, 646], [2, 4, 645], [6, 12, 634], [2, 2, 649], [2, 22, 630], [2, 2, 651]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 631 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[2, 2, 652], [2, 9, 646], [2, 2, 654], [2, 15, 642], [2, 6, 652], [6, 1, 654], [2, 6, 654], [2, 9, 652], [2, 2, 660], [2, 2, 661], [2, 12, 652], [6, 3, 658], [2, 2, 664], [2, 42, 625], [6, 12, 652], [2, 9, 660], [2, 10, 660], [6, 28, 639], [2, 12, 660], [2, 21, 652], [6, 60, 610], [2, 36, 639], [2, 16, 660], [6, 18, 655], [2, 96, 582]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 656 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[2, 19, 660], [6, 22, 654], [2, 21, 660], [2, 22, 660], [2, 2, 681], [2, 54, 630], [2, 34, 651], [2, 2, 684], [2, 132, 555], [2, 76, 612], [2, 2, 687], [2, 174, 516], [2, 7, 684], [6, 30, 658], [2, 2, 691], [2, 30, 664], [6, 3, 688], [2, 54, 642], [2, 10, 687], [6, 60, 634], [2, 12, 687], [2, 40, 660], [6, 28, 669], [2, 2, 700], [2, 3, 700]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 681 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[6, 10, 690], [2, 51, 654], [2, 66, 640], [2, 2, 705], [2, 126, 582], [2, 4, 705], [6, 94, 612], [2, 6, 705], [2, 52, 660], [6, 4, 705], [2, 2, 712], [2, 15, 700], [2, 2, 714], [2, 2, 715], [2, 6, 712], [2, 2, 717], [2, 6, 714], [2, 6, 715], [2, 2, 720], [2, 252, 471], [2, 4, 720], [6, 18, 703], [2, 2, 724], [2, 7, 720], [2, 2, 726]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 706 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[2, 2, 727], [2, 4, 726], [6, 45, 682], [2, 2, 730], [2, 7, 726], [6, 210, 520], [2, 15, 720], [2, 16, 720], [6, 10, 723], [2, 2, 736], [2, 3, 736], [6, 4, 732], [2, 15, 726], [2, 42, 700], [2, 2, 741], [2, 2, 742], [2, 4, 741], [2, 2, 744], [2, 2, 745], [2, 6, 742], [2, 2, 747], [2, 6, 744], [2, 21, 730], [2, 2, 750], [2, 6, 747]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 731 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[2, 4, 750], [6, 19, 732], [2, 36, 720], [2, 27, 730], [2, 2, 756], [2, 3, 756], [2, 4, 756], [6, 4, 753], [2, 12, 750], [2, 21, 742], [2, 2, 762], [2, 9, 756], [2, 10, 756], [6, 10, 753], [2, 2, 766], [2, 3, 766], [6, 64, 702], [2, 9, 762], [2, 30, 742], [6, 22, 747], [2, 2, 772], [2, 30, 745], [6, 30, 742], [2, 2, 775], [2, 22, 756]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 756 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[2, 2, 777], [2, 24, 756], [2, 6, 775], [2, 2, 780], [2, 3, 780], [2, 4, 780], [6, 7, 774], [2, 2, 784], [2, 3, 784], [2, 2, 786], [2, 3, 786], [2, 6, 784], [6, 3, 784], [2, 2, 790], [2, 7, 786], [2, 2, 792], [2, 15, 780], [2, 4, 792], [6, 40, 753], [2, 6, 792], [2, 9, 790], [6, 4, 792], [2, 2, 799], [2, 10, 792], [2, 2, 801]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 781 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[2, 24, 780], [2, 4, 801], [2, 2, 804], [2, 2, 805], [2, 16, 792], [2, 2, 807], [2, 30, 780], [2, 10, 801], [2, 2, 810], [2, 2, 811], [2, 10, 804], [6, 12, 799], [2, 2, 814], [2, 3, 814], [6, 100, 714], [2, 27, 792], [2, 34, 786], [2, 2, 819], [2, 12, 810], [2, 16, 807], [6, 210, 610], [2, 15, 810], [2, 12, 814], [6, 1, 822], [2, 66, 762]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 806 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[2, 24, 805], [6, 28, 798], [2, 2, 829], [2, 42, 790], [6, 1, 828], [2, 2, 832], [2, 6, 829], [2, 2, 834], [2, 2, 835], [2, 66, 772], [6, 60, 775], [2, 6, 834], [2, 6, 835], [6, 18, 820], [2, 42, 801], [2, 30, 814], [6, 1, 840], [2, 12, 834], [2, 15, 832], [6, 4, 840], [2, 2, 847], [2, 36, 814], [2, 2, 849], [2, 2, 850], [2, 3, 850]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 831 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[6, 220, 630], [2, 36, 819], [2, 6, 850], [2, 2, 855], [2, 246, 612], [2, 9, 850], [6, 82, 774], [2, 54, 807], [2, 70, 792], [2, 2, 861], [2, 2, 862], [2, 51, 814], [6, 42, 820], [2, 12, 855], [2, 6, 862], [2, 2, 867], [2, 90, 780], [2, 4, 867], [6, 18, 850], [2, 2, 871], [2, 12, 862], [6, 9, 862], [2, 2, 874], [2, 3, 874], [6, 12, 862]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 856 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[2, 2, 877], [2, 100, 780], [6, 4, 873], [2, 2, 880], [2, 6, 877], [6, 40, 840], [2, 24, 861], [2, 6, 880], [6, 18, 865], [2, 96, 792], [2, 9, 880], [6, 28, 858], [2, 2, 889], [2, 12, 880], [6, 4, 885], [2, 2, 892], [2, 6, 889], [2, 2, 894], [2, 2, 895], [2, 6, 892], [6, 10, 885], [2, 114, 786], [2, 7, 894], [6, 40, 858], [2, 2, 901]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 881 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[2, 70, 834], [6, 3, 898], [2, 192, 714], [2, 12, 895], [2, 2, 906], [2, 75, 834], [2, 4, 906], [6, 7, 900], [2, 192, 720], [2, 21, 892], [2, 2, 912], [2, 21, 894], [2, 10, 906], [6, 1, 912], [2, 2, 916], [2, 27, 892], [6, 94, 822], [2, 27, 894], [2, 30, 892], [6, 12, 907], [2, 120, 804], [2, 9, 916], [2, 2, 924], [2, 15, 912], [2, 16, 912]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 906 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[6, 60, 865], [2, 36, 894], [2, 19, 912], [6, 100, 828], [2, 2, 931], [2, 10, 924], [6, 9, 922], [2, 2, 934], [2, 3, 934], [2, 2, 936], [2, 2, 937], [2, 16, 924], [2, 2, 939], [2, 2, 940], [2, 3, 940], [6, 40, 900], [2, 9, 936], [2, 6, 940], [2, 2, 945], [2, 36, 912], [2, 4, 945], [6, 4, 942], [2, 6, 945], [2, 12, 940], [2, 2, 951]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 931 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[2, 42, 912], [2, 4, 951], [2, 2, 954], [2, 3, 954], [2, 52, 906], [2, 2, 957], [2, 156, 804], [2, 21, 940], [6, 78, 880], [2, 6, 957], [2, 10, 954], [6, 49, 912], [2, 12, 954], [2, 22, 945], [2, 2, 966], [2, 2, 967], [2, 4, 966], [6, 22, 945], [2, 180, 792], [2, 6, 967], [6, 120, 850], [2, 9, 966], [2, 42, 934], [2, 2, 975], [2, 2, 976]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 956 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[2, 3, 976], [6, 64, 912], [2, 6, 975], [2, 70, 912], [6, 1, 978], [2, 30, 954], [2, 9, 976], [6, 4, 978], [2, 12, 975], [2, 232, 756], [2, 2, 987], [2, 54, 936], [2, 4, 987], [2, 2, 990], [2, 3, 990], [2, 70, 924], [6, 3, 988], [2, 2, 994], [2, 30, 967], [6, 10, 984], [2, 2, 997], [2, 34, 966], [2, 2, 999], [2, 2, 1000], [2, 3, 1000]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 981 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `6 ≤ n ≤ 1005` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 6 ≤ n) (h2 : n ≤ 1005) : ∃ x, good n x = true := by
  by_cases c0 : n < 31
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 56
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 81
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 106
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 131
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 156
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 181
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 206
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 231
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 256
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 281
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 306
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 331
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 356
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 381
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 406
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 431
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 456
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 481
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 506
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 531
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 556
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 581
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 606
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 631
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 656
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 681
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 706
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 731
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 756
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 781
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 806
  · exact chunk ok31 len31 (by omega) (by omega)
  by_cases c32 : n < 831
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 856
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 881
  · exact chunk ok34 len34 (by omega) (by omega)
  by_cases c35 : n < 906
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 931
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 956
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 981
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.AOeisA229969_conjecture_5aTab

open OMA.AOeisA229969_conjecture_5aTab in
theorem OMA.solution : OMA.R_OeisA229969_conjecture_5a_R1.H1 := by
  intro n hn hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
