import OMAReductions.R_OeisA229969_conjecture_3a_R1
import Mathlib

-- Step OeisA229969.conjecture_3a.R1.H1: hypothesis H1 of reduction OeisA229969.conjecture_3a.R1
-- Credit: @prathameshnium. Finite check for 7 ≤ n ≤ 1006.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 1208591.

/-! Step OeisA229969.conjecture_3a.R1.H1. -/

namespace OMA.AOeisA229969_conjecture_3aTab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `1101` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 1101 2

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
  have hnd := noDiv_sound p 1101 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [x, y, z] => (decide (0 < x) && (decide (0 < y) && (decide (0 < z) && (decide (x + y + z = n) && ((decide (x = 2) || (decide (x = 3) || decide (x = 4))) && (isPrimeB (2 * x - 1) && (isPrimeB (2 * y - 1) && (isPrimeB (2 * z - 1) && isPrimeB (2 * x * y * z - 1)))))))))
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
      x ∈ ({2, 3, 4} : Finset ℕ) ∧
      (2 * x - 1).Prime ∧ (2 * y - 1).Prime ∧ (2 * z - 1).Prime ∧
      (2 * x * y * z - 1).Prime := by
  unfold core at h
  split at h
  next x y z =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
    exact ⟨x, y, z, a0, a1, a2, a3, (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact a4), isPrimeB_sound _ a5, isPrimeB_sound _ a6, isPrimeB_sound _ a7, isPrimeB_sound _ a8⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 7, …, 1006`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[2, 2, 3], [2, 2, 4], [2, 3, 4], [2, 2, 6], [2, 3, 6], [2, 3, 7], [2, 2, 9], [2, 2, 10], [2, 6, 7], [3, 3, 10], [3, 4, 10], [2, 4, 12], [3, 6, 10], [2, 2, 16], [2, 3, 16], [3, 4, 15], [2, 2, 19], [2, 3, 19], [2, 2, 21], [2, 3, 21], [2, 3, 22], [2, 2, 24], [2, 6, 21], [2, 4, 24], [3, 7, 21]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 7 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[4, 9, 19], [2, 4, 27], [2, 2, 30], [2, 3, 30], [2, 4, 30], [3, 3, 31], [2, 2, 34], [2, 6, 31], [3, 7, 30], [2, 3, 36], [2, 3, 37], [3, 4, 36], [2, 6, 36], [2, 3, 40], [3, 3, 40], [2, 3, 42], [2, 10, 36], [2, 2, 45], [2, 21, 27], [2, 4, 45], [3, 12, 37], [2, 9, 42], [2, 3, 49], [3, 3, 49], [2, 9, 45]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 32 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[2, 15, 40], [2, 2, 54], [2, 2, 55], [2, 3, 55], [3, 6, 52], [2, 3, 57], [2, 4, 57], [3, 4, 57], [2, 6, 57], [2, 9, 55], [3, 7, 57], [2, 12, 54], [2, 15, 52], [3, 3, 64], [4, 12, 55], [2, 15, 55], [3, 4, 66], [2, 3, 69], [2, 3, 70], [3, 3, 70], [2, 30, 45], [2, 7, 69], [2, 2, 75], [2, 2, 76], [2, 3, 76]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 57 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[3, 3, 76], [2, 2, 79], [2, 3, 79], [3, 12, 70], [2, 9, 75], [2, 3, 82], [3, 6, 79], [2, 42, 45], [2, 9, 79], [3, 12, 76], [4, 4, 84], [2, 7, 84], [2, 2, 90], [2, 2, 91], [2, 3, 91], [3, 3, 91], [2, 21, 75], [2, 15, 82], [3, 7, 90], [2, 3, 96], [2, 3, 97], [3, 10, 90], [2, 3, 99], [2, 4, 99], [3, 6, 97]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 82 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[2, 15, 90], [2, 6, 100], [3, 7, 99], [2, 21, 87], [2, 30, 79], [3, 3, 106], [2, 12, 99], [2, 6, 106], [3, 30, 82], [2, 15, 99], [3, 24, 90], [2, 2, 114], [2, 2, 115], [2, 4, 114], [3, 3, 115], [2, 30, 90], [2, 4, 117], [3, 6, 115], [2, 2, 121], [2, 3, 121], [3, 4, 120], [2, 6, 120], [2, 6, 121], [3, 7, 120], [2, 3, 126]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 107 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[2, 10, 120], [2, 2, 129], [2, 6, 126], [2, 4, 129], [4, 6, 126], [2, 3, 132], [2, 4, 132], [3, 4, 132], [2, 2, 136], [2, 69, 70], [3, 3, 136], [2, 9, 132], [2, 3, 139], [3, 7, 135], [2, 24, 120], [2, 10, 135], [3, 6, 139], [2, 15, 132], [2, 6, 142], [3, 12, 136], [3, 34, 115], [2, 4, 147], [3, 4, 147], [2, 6, 147], [2, 19, 135]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 132 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[3, 7, 147], [2, 2, 154], [2, 3, 154], [3, 10, 147], [2, 3, 156], [3, 27, 132], [3, 19, 141], [2, 3, 159], [2, 4, 159], [3, 6, 157], [2, 45, 120], [2, 7, 159], [3, 12, 154], [2, 2, 166], [2, 10, 159], [3, 10, 159], [2, 45, 126], [2, 3, 169], [3, 3, 169], [2, 15, 159], [2, 40, 135], [3, 9, 166], [2, 2, 175], [2, 3, 175], [3, 36, 142]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 157 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[3, 10, 169], [2, 7, 174], [2, 2, 180], [2, 9, 174], [2, 4, 180], [3, 7, 177], [2, 2, 184], [2, 3, 184], [3, 7, 180], [2, 30, 159], [2, 3, 187], [3, 10, 180], [2, 45, 147], [2, 24, 169], [3, 27, 166], [2, 15, 180], [2, 12, 184], [2, 2, 195], [2, 3, 195], [2, 4, 195], [3, 4, 195], [2, 6, 195], [2, 27, 175], [2, 2, 201], [2, 3, 201]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 182 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[2, 15, 190], [3, 10, 195], [2, 15, 192], [2, 3, 205], [3, 21, 187], [2, 15, 195], [2, 6, 205], [3, 12, 199], [2, 21, 192], [2, 3, 211], [3, 3, 211], [2, 6, 210], [2, 7, 210], [3, 7, 210], [2, 3, 216], [3, 87, 132], [3, 9, 211], [2, 2, 220], [2, 7, 216], [3, 66, 157], [2, 3, 222], [2, 6, 220], [3, 6, 220], [2, 3, 225], [2, 9, 220]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 207 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[3, 4, 225], [2, 2, 229], [2, 7, 225], [2, 2, 231], [2, 75, 159], [2, 10, 225], [2, 2, 234], [2, 12, 225], [2, 9, 229], [3, 37, 201], [2, 15, 225], [2, 7, 234], [3, 9, 232], [2, 3, 240], [2, 19, 225], [3, 12, 232], [2, 2, 244], [2, 3, 244], [3, 3, 244], [2, 24, 225], [2, 30, 220], [3, 4, 246], [2, 2, 250], [2, 3, 250], [3, 7, 246]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 232 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[2, 3, 252], [2, 10, 246], [2, 2, 255], [2, 6, 252], [2, 4, 255], [3, 9, 250], [2, 15, 246], [2, 10, 252], [2, 2, 261], [2, 24, 240], [2, 40, 225], [3, 4, 261], [2, 6, 261], [2, 6, 262], [3, 6, 262], [2, 15, 255], [2, 9, 262], [3, 40, 231], [2, 12, 261], [2, 3, 271], [3, 3, 271], [2, 21, 255], [2, 16, 261], [3, 3, 274], [2, 84, 195]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 257 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[2, 55, 225], [3, 9, 271], [2, 3, 279], [2, 4, 279], [3, 51, 232], [2, 90, 195], [2, 12, 274], [3, 7, 279], [2, 2, 286], [2, 10, 279], [3, 3, 286], [2, 2, 289], [2, 3, 289], [3, 7, 285], [2, 9, 285], [2, 10, 285], [2, 2, 294], [2, 3, 294], [2, 4, 294], [3, 36, 262], [2, 15, 285], [2, 4, 297], [2, 2, 300], [2, 6, 297], [2, 4, 300]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 282 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[3, 3, 301], [2, 9, 297], [2, 21, 286], [3, 3, 304], [2, 9, 300], [2, 55, 255], [3, 9, 301], [3, 10, 301], [2, 3, 310], [3, 96, 217], [2, 75, 240], [2, 12, 304], [3, 6, 310], [2, 84, 234], [2, 9, 310], [3, 10, 309], [2, 12, 309], [2, 6, 316], [3, 40, 282], [2, 3, 321], [2, 3, 322], [2, 2, 324], [2, 6, 321], [2, 6, 322], [3, 12, 316]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 307 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[2, 3, 327], [2, 4, 327], [3, 9, 322], [2, 2, 331], [2, 4, 330], [3, 4, 330], [2, 6, 330], [2, 7, 330], [3, 7, 330], [2, 45, 294], [2, 30, 310], [2, 2, 339], [2, 96, 246], [2, 6, 337], [3, 12, 331], [2, 120, 225], [2, 4, 342], [3, 15, 331], [2, 2, 346], [2, 55, 294], [3, 19, 330], [2, 24, 327], [2, 10, 342], [3, 45, 307], [2, 3, 351]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 332 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[2, 45, 310], [3, 4, 351], [2, 6, 351], [2, 3, 355], [3, 3, 355], [3, 22, 337], [2, 15, 346], [2, 2, 360], [2, 36, 327], [2, 34, 330], [3, 70, 294], [2, 15, 351], [2, 7, 360], [3, 3, 364], [2, 9, 360], [3, 69, 300], [3, 6, 364], [2, 21, 351], [2, 6, 367], [3, 3, 370], [2, 3, 372], [2, 12, 364], [3, 21, 355], [2, 27, 351], [2, 15, 364]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 357 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[3, 9, 370], [2, 42, 339], [2, 3, 379], [3, 15, 367], [2, 75, 309], [2, 135, 250], [3, 21, 364], [2, 2, 385], [2, 7, 381], [3, 7, 381], [2, 3, 387], [2, 6, 385], [3, 6, 385], [2, 12, 381], [2, 9, 385], [3, 7, 387], [2, 9, 387], [2, 21, 376], [3, 42, 355], [2, 69, 330], [2, 15, 385], [2, 2, 399], [2, 3, 399], [2, 16, 387], [3, 22, 381]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 382 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[2, 75, 330], [2, 7, 399], [3, 30, 376], [2, 21, 387], [2, 3, 406], [3, 3, 406], [2, 6, 405], [2, 6, 406], [3, 42, 370], [2, 3, 411], [2, 3, 412], [3, 16, 399], [2, 2, 415], [2, 6, 412], [3, 6, 412], [2, 90, 330], [2, 9, 412], [2, 2, 420], [2, 3, 420], [2, 4, 420], [3, 4, 420], [2, 6, 420], [2, 12, 415], [3, 12, 415], [2, 90, 339]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 407 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[2, 70, 360], [3, 19, 411], [2, 3, 429], [2, 4, 429], [3, 22, 411], [2, 75, 360], [2, 4, 432], [3, 9, 427], [2, 9, 429], [2, 10, 429], [3, 7, 432], [2, 2, 439], [2, 12, 430], [2, 2, 441], [3, 31, 412], [2, 3, 442], [3, 6, 439], [2, 15, 432], [2, 4, 444], [3, 7, 441], [2, 195, 255], [2, 19, 432], [3, 10, 441], [2, 24, 429], [2, 15, 439]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 432 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[3, 15, 439], [2, 2, 454], [2, 27, 430], [3, 3, 454], [2, 3, 456], [2, 30, 430], [3, 19, 441], [2, 30, 432], [2, 3, 460], [3, 21, 442], [3, 10, 454], [2, 51, 415], [2, 2, 465], [2, 36, 432], [2, 15, 454], [3, 4, 465], [2, 6, 465], [2, 12, 460], [2, 2, 471], [2, 3, 471], [2, 55, 420], [3, 6, 469], [2, 21, 456], [2, 4, 474], [3, 36, 442]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 457 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[2, 225, 255], [2, 10, 471], [3, 4, 477], [2, 6, 477], [2, 10, 474], [3, 10, 474], [2, 12, 474], [2, 3, 484], [3, 10, 477], [2, 15, 474], [2, 135, 355], [2, 2, 489], [2, 3, 489], [2, 4, 489], [3, 7, 486], [2, 3, 492], [2, 7, 489], [3, 4, 492], [2, 2, 496], [2, 10, 489], [3, 7, 492], [2, 30, 471], [2, 3, 499], [3, 70, 432], [2, 15, 489]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 482 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[2, 45, 460], [3, 9, 496], [2, 21, 486], [2, 22, 486], [3, 22, 486], [2, 225, 285], [2, 4, 507], [2, 2, 510], [2, 36, 477], [2, 3, 511], [3, 4, 510], [2, 6, 510], [2, 6, 511], [2, 2, 516], [2, 30, 489], [2, 3, 517], [3, 21, 499], [2, 2, 520], [2, 7, 516], [3, 12, 511], [2, 195, 330], [2, 6, 520], [3, 6, 520], [2, 3, 525], [2, 3, 526]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 507 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[3, 3, 526], [2, 21, 510], [2, 7, 525], [3, 112, 420], [2, 9, 525], [2, 70, 465], [3, 4, 531], [2, 6, 531], [2, 7, 531], [3, 3, 535], [2, 120, 420], [2, 16, 525], [3, 6, 535], [2, 57, 486], [2, 9, 535], [3, 12, 532], [2, 15, 531], [2, 12, 535], [3, 3, 544], [2, 3, 546], [2, 3, 547], [2, 2, 549], [2, 6, 546], [2, 4, 549], [3, 271, 282]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 532 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[2, 135, 420], [2, 4, 552], [3, 7, 549], [2, 3, 555], [2, 34, 525], [3, 10, 549], [2, 30, 531], [2, 10, 552], [3, 3, 559], [2, 9, 555], [2, 55, 510], [3, 6, 559], [2, 2, 565], [2, 3, 565], [3, 3, 565], [2, 210, 360], [2, 9, 562], [3, 9, 562], [2, 27, 546], [2, 19, 555], [3, 9, 565], [2, 21, 555], [2, 52, 525], [3, 22, 555], [2, 3, 576]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 557 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[2, 55, 525], [3, 15, 565], [2, 30, 552], [2, 7, 576], [3, 6, 577], [2, 3, 582], [2, 4, 582], [3, 4, 582], [2, 6, 582], [2, 30, 559], [3, 7, 582], [2, 66, 525], [2, 10, 582], [3, 10, 582], [2, 69, 525], [2, 40, 555], [2, 2, 594], [2, 3, 594], [2, 7, 591], [3, 7, 591], [2, 135, 465], [2, 4, 597], [3, 4, 597], [2, 6, 597], [2, 3, 601]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 582 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[3, 7, 597], [2, 9, 597], [2, 6, 601], [3, 55, 552], [2, 195, 414], [2, 3, 607], [2, 2, 609], [2, 3, 609], [2, 4, 609], [3, 6, 607], [2, 90, 525], [2, 4, 612], [2, 2, 615], [2, 21, 597], [2, 4, 615], [3, 3, 616], [2, 2, 619], [2, 6, 616], [3, 15, 607], [2, 135, 489], [2, 70, 555], [3, 6, 619], [2, 2, 625], [2, 3, 625], [3, 12, 616]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 607 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[2, 15, 615], [2, 16, 615], [2, 2, 630], [2, 3, 630], [2, 4, 630], [3, 9, 625], [2, 21, 615], [2, 75, 562], [3, 7, 630], [2, 9, 630], [2, 255, 385], [3, 10, 630], [2, 2, 640], [2, 4, 639], [3, 3, 640], [2, 3, 642], [2, 4, 642], [3, 6, 640], [2, 2, 646], [2, 9, 640], [3, 84, 565], [2, 12, 639], [2, 7, 645], [3, 3, 649], [2, 45, 609]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 632 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[2, 3, 652], [2, 2, 654], [2, 42, 615], [2, 4, 654], [3, 12, 646], [2, 15, 645], [2, 7, 654], [2, 2, 660], [2, 3, 660], [2, 4, 660], [3, 3, 661], [2, 12, 654], [2, 15, 652], [3, 15, 652], [2, 15, 654], [2, 10, 660], [3, 21, 649], [2, 75, 597], [2, 12, 661], [3, 12, 661], [3, 10, 664], [2, 15, 661], [3, 12, 664], [2, 69, 609], [2, 15, 664]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 657 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[3, 19, 660], [2, 21, 660], [2, 66, 616], [3, 22, 660], [2, 3, 681], [2, 55, 630], [2, 2, 684], [2, 42, 645], [2, 24, 664], [3, 36, 652], [2, 3, 687], [2, 10, 681], [3, 4, 687], [2, 2, 691], [2, 3, 691], [3, 3, 691], [2, 12, 684], [2, 10, 687], [3, 37, 660], [2, 15, 684], [2, 180, 520], [3, 9, 691], [2, 21, 681], [2, 154, 549], [3, 16, 687]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 682 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[2, 45, 660], [2, 54, 652], [2, 2, 705], [2, 27, 681], [2, 4, 705], [3, 9, 700], [2, 24, 687], [2, 7, 705], [3, 187, 525], [2, 54, 660], [2, 3, 712], [2, 2, 714], [2, 66, 651], [2, 4, 714], [3, 31, 687], [2, 15, 705], [2, 4, 717], [3, 4, 717], [2, 6, 717], [2, 4, 720], [3, 7, 717], [2, 2, 724], [2, 12, 715], [2, 2, 726], [2, 9, 720]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 707 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[2, 15, 715], [3, 16, 714], [2, 2, 730], [2, 7, 726], [3, 6, 727], [2, 120, 615], [2, 6, 730], [3, 12, 724], [2, 12, 726], [2, 3, 736], [3, 9, 730], [2, 195, 546], [2, 30, 712], [2, 2, 741], [2, 24, 720], [2, 40, 705], [3, 4, 741], [2, 6, 741], [2, 4, 744], [3, 6, 742], [2, 3, 747], [2, 9, 742], [3, 7, 744], [2, 3, 750], [2, 10, 744]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 732 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[3, 27, 727], [2, 9, 747], [2, 10, 747], [2, 2, 756], [2, 45, 714], [2, 15, 745], [3, 4, 756], [2, 6, 756], [2, 16, 747], [3, 7, 756], [2, 120, 645], [2, 40, 726], [3, 4, 762], [2, 6, 762], [2, 19, 750], [3, 7, 762], [2, 9, 762], [2, 16, 756], [3, 22, 750], [2, 24, 750], [2, 30, 745], [3, 19, 756], [2, 2, 775], [2, 12, 766], [3, 6, 772]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 757 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[2, 3, 777], [2, 9, 772], [3, 9, 772], [2, 21, 762], [2, 4, 780], [3, 4, 780], [2, 2, 784], [2, 7, 780], [2, 2, 786], [2, 3, 786], [2, 15, 775], [3, 40, 750], [2, 15, 777], [2, 3, 790], [3, 31, 762], [2, 45, 750], [2, 4, 792], [3, 6, 790], [2, 21, 777], [2, 9, 790], [3, 19, 780], [2, 21, 780], [2, 3, 799], [3, 30, 772], [2, 54, 750]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 782 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[2, 55, 750], [3, 19, 786], [2, 27, 780], [2, 52, 756], [3, 3, 805], [2, 180, 630], [2, 4, 807], [3, 6, 805], [2, 3, 810], [2, 4, 810], [3, 7, 807], [2, 24, 792], [2, 3, 814], [3, 7, 810], [2, 15, 804], [2, 15, 805], [2, 2, 819], [2, 66, 756], [2, 4, 819], [3, 12, 811], [2, 210, 615], [2, 16, 810], [3, 19, 807], [2, 9, 819], [2, 19, 810]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 807 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[3, 10, 819], [2, 24, 807], [2, 27, 805], [3, 27, 805], [2, 15, 819], [2, 90, 745], [3, 16, 819], [2, 2, 835], [2, 27, 811], [3, 27, 811], [2, 120, 720], [2, 12, 829], [3, 6, 835], [2, 24, 819], [2, 9, 835], [3, 15, 829], [2, 12, 834], [2, 15, 832], [3, 37, 810], [2, 45, 804], [2, 3, 847], [2, 2, 849], [2, 45, 807], [2, 6, 847], [3, 3, 850]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 832 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[2, 45, 810], [2, 6, 850], [3, 9, 847], [2, 3, 855], [2, 4, 855], [3, 69, 790], [2, 12, 849], [2, 30, 832], [3, 30, 832], [2, 3, 861], [2, 3, 862], [3, 4, 861], [2, 6, 861], [2, 7, 861], [3, 7, 861], [3, 37, 832], [2, 10, 861], [3, 4, 867], [2, 2, 871], [2, 40, 834], [3, 24, 850], [2, 2, 874], [2, 3, 874], [3, 3, 874], [2, 30, 849]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 857 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[2, 30, 850], [3, 154, 726], [2, 2, 880], [2, 3, 880], [3, 16, 867], [2, 75, 810], [2, 15, 871], [3, 12, 874], [2, 27, 861], [2, 34, 855], [3, 54, 835], [2, 24, 867], [2, 3, 889], [3, 3, 889], [2, 45, 849], [2, 120, 775], [2, 2, 894], [2, 2, 895], [2, 3, 895], [3, 21, 877], [2, 120, 780], [2, 7, 894], [3, 7, 894], [2, 2, 901], [2, 10, 894]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 882 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[3, 3, 901], [2, 129, 777], [2, 30, 877], [2, 2, 906], [2, 15, 894], [2, 15, 895], [3, 49, 861], [2, 45, 867], [2, 7, 906], [3, 12, 901], [2, 195, 720], [2, 4, 912], [3, 55, 861], [2, 12, 906], [2, 69, 850], [3, 3, 916], [2, 9, 912], [2, 10, 912], [3, 117, 805], [2, 30, 894], [2, 175, 750], [3, 9, 916], [2, 3, 924], [2, 4, 924], [3, 12, 916]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 907 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[2, 75, 855], [2, 15, 916], [3, 19, 912], [2, 21, 912], [2, 3, 931], [3, 10, 924], [2, 12, 924], [2, 6, 931], [2, 2, 936], [2, 15, 924], [2, 3, 937], [3, 6, 934], [2, 135, 807], [2, 3, 940], [3, 327, 616], [2, 195, 750], [2, 30, 916], [2, 2, 945], [2, 12, 936], [2, 15, 934], [3, 4, 945], [2, 6, 945], [2, 7, 945], [2, 2, 951], [2, 3, 951]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 932 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[2, 10, 945], [3, 19, 936], [2, 3, 954], [2, 4, 954], [3, 21, 937], [2, 3, 957], [2, 7, 954], [3, 10, 951], [2, 129, 834], [2, 24, 940], [3, 7, 957], [2, 15, 951], [2, 55, 912], [2, 2, 966], [2, 45, 924], [2, 30, 940], [3, 16, 954], [2, 27, 945], [2, 19, 954], [3, 231, 742], [3, 112, 862], [2, 10, 966], [3, 19, 957], [2, 3, 975], [2, 34, 945]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 957 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[3, 4, 975], [2, 6, 975], [2, 7, 975], [3, 7, 975], [2, 9, 975], [2, 45, 940], [3, 34, 951], [2, 36, 951], [2, 49, 939], [3, 12, 976], [2, 45, 945], [2, 4, 987], [2, 2, 990], [2, 6, 987], [2, 19, 975], [3, 7, 987], [2, 2, 994], [2, 3, 994], [3, 3, 994], [2, 45, 954], [2, 190, 810], [3, 10, 990], [2, 3, 999], [2, 27, 976], [3, 37, 966]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 982 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `7 ≤ n ≤ 1006` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 7 ≤ n) (h2 : n ≤ 1006) : ∃ x, good n x = true := by
  by_cases c0 : n < 32
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 57
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 82
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 107
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 132
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 157
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 182
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 207
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 232
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 257
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 282
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 307
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 332
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 357
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 382
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 407
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 432
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 457
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 482
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 507
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 532
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 557
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 582
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 607
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 632
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 657
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 682
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 707
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 732
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 757
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 782
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 807
  · exact chunk ok31 len31 (by omega) (by omega)
  by_cases c32 : n < 832
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 857
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 882
  · exact chunk ok34 len34 (by omega) (by omega)
  by_cases c35 : n < 907
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 932
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 957
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 982
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.AOeisA229969_conjecture_3aTab

open OMA.AOeisA229969_conjecture_3aTab in
theorem OMA.solution : OMA.R_OeisA229969_conjecture_3a_R1.H1 := by
  intro n hn hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
