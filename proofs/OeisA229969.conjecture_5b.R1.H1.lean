import OMAReductions.R_OeisA229969_conjecture_5b_R1
import Mathlib

-- Step OeisA229969.conjecture_5b.R1.H1: hypothesis H1 of reduction OeisA229969.conjecture_5b.R1
-- Credit: @prathameshnium. Finite check for 3 ≤ n ≤ 1002.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 241921.

/-! Step OeisA229969.conjecture_5b.R1.H1. -/

namespace OMA.AOeisA229969_conjecture_5bTab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `493` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 493 2

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
  have hnd := noDiv_sound p 493 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [x, y, z] => (decide (0 < x) && (decide (0 < y) && (decide (0 < z) && (decide (x + y + z = n) && ((decide (x = 1) || (decide (x = 2) || decide (x = 6))) && (isPrimeB (x * y + 1) && (isPrimeB (x * z + 1) && isPrimeB (y * z + 1))))))))
  | _ => false

def good (n : ℕ) (w : List ℕ) : Bool := (Nat.beq n 16) || core n w

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
      x ∈ ({1, 2, 6} : Finset ℕ) ∧
      (x * y + 1).Prime ∧ (x * z + 1).Prime ∧ (y * z + 1).Prime := by
  unfold core at h
  split at h
  next x y z =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
    exact ⟨x, y, z, a0, a1, a2, a3, (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact a4), isPrimeB_sound _ a5, isPrimeB_sound _ a6, isPrimeB_sound _ a7⟩
  next => exact absurd h Bool.false_ne_true

theorem good_sound (n : ℕ) (w : List ℕ) (hn : n > 2) (hne : n ≠ 16)
    (h : good n w = true) : ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      x ∈ ({1, 2, 6} : Finset ℕ) ∧
      (x * y + 1).Prime ∧ (x * z + 1).Prime ∧ (y * z + 1).Prime := by
  simp only [good, Bool.or_eq_true] at h
  rcases h with h | h
  · rw [Nat.beq_eq] at h; exact absurd h hne
  · exact core_sound n w h

/-! One witness for each `n = 3, …, 1002`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[1, 1, 1], [1, 1, 2], [1, 2, 2], [1, 1, 4], [2, 2, 3], [1, 1, 6], [1, 2, 6], [2, 2, 6], [2, 3, 6], [1, 1, 10], [1, 6, 6], [1, 1, 12], [1, 4, 10], [], [1, 6, 10], [1, 1, 16], [1, 6, 12], [1, 1, 18], [1, 2, 18], [2, 2, 18], [1, 4, 18], [1, 1, 22], [1, 6, 18], [2, 6, 18], [1, 4, 22]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 3 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[6, 6, 16], [1, 10, 18], [1, 1, 28], [2, 3, 26], [1, 1, 30], [1, 2, 30], [2, 2, 30], [2, 15, 18], [2, 14, 20], [1, 6, 30], [1, 1, 36], [1, 2, 36], [2, 2, 36], [1, 12, 28], [1, 1, 40], [2, 2, 39], [1, 1, 42], [1, 16, 28], [2, 14, 30], [1, 6, 40], [1, 1, 46], [1, 12, 36], [2, 18, 30], [1, 10, 40], [2, 2, 48]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 28 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[1, 6, 46], [1, 1, 52], [2, 2, 51], [6, 10, 40], [1, 10, 46], [2, 2, 54], [1, 6, 52], [1, 1, 58], [1, 18, 42], [1, 1, 60], [1, 4, 58], [2, 6, 56], [1, 4, 60], [2, 8, 56], [2, 2, 63], [1, 1, 66], [1, 22, 46], [2, 14, 54], [1, 10, 60], [1, 1, 70], [1, 6, 66], [1, 1, 72], [1, 4, 70], [2, 6, 68], [1, 6, 70]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 53 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[2, 2, 74], [1, 6, 72], [1, 1, 78], [1, 2, 78], [2, 2, 78], [1, 4, 78], [1, 1, 82], [2, 2, 81], [2, 30, 54], [2, 2, 83], [2, 36, 50], [1, 16, 72], [1, 1, 88], [1, 12, 78], [6, 10, 76], [1, 4, 88], [2, 2, 90], [1, 16, 78], [2, 20, 74], [1, 36, 60], [1, 1, 96], [1, 2, 96], [2, 2, 96], [1, 28, 72], [1, 1, 100]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 78 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[1, 6, 96], [1, 1, 102], [1, 4, 100], [2, 8, 96], [1, 4, 102], [1, 1, 106], [1, 6, 102], [1, 1, 108], [1, 28, 82], [2, 20, 90], [1, 4, 108], [1, 1, 112], [2, 2, 111], [6, 40, 70], [1, 4, 112], [2, 2, 114], [1, 6, 112], [2, 2, 116], [1, 12, 108], [6, 6, 110], [1, 16, 106], [2, 2, 120], [1, 28, 96], [2, 8, 116], [2, 5, 120]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 103 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[1, 1, 126], [1, 22, 106], [2, 14, 114], [1, 18, 112], [1, 1, 130], [1, 6, 126], [2, 18, 114], [1, 4, 130], [2, 6, 128], [1, 30, 106], [1, 1, 136], [1, 36, 102], [1, 1, 138], [1, 2, 138], [2, 2, 138], [1, 16, 126], [2, 2, 140], [1, 6, 138], [2, 6, 138], [1, 10, 136], [2, 26, 120], [1, 10, 138], [1, 1, 148], [1, 12, 138], [1, 1, 150]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 128 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[1, 4, 148], [2, 6, 146], [1, 4, 150], [2, 26, 128], [2, 2, 153], [1, 1, 156], [1, 2, 156], [2, 2, 156], [1, 12, 148], [2, 2, 158], [1, 6, 156], [1, 1, 162], [2, 23, 140], [2, 8, 156], [1, 60, 106], [1, 1, 166], [1, 12, 156], [6, 38, 126], [1, 22, 148], [2, 2, 168], [1, 6, 166], [1, 1, 172], [1, 36, 138], [2, 6, 168], [1, 40, 136]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 153 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[2, 2, 174], [1, 6, 172], [1, 1, 178], [1, 18, 162], [1, 1, 180], [1, 10, 172], [2, 26, 156], [1, 6, 178], [2, 8, 176], [1, 60, 126], [2, 90, 96], [1, 16, 172], [2, 2, 186], [1, 10, 180], [1, 1, 190], [1, 12, 180], [1, 1, 192], [1, 4, 190], [2, 8, 186], [1, 4, 192], [1, 1, 196], [1, 6, 192], [1, 1, 198], [1, 2, 198], [2, 2, 198]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 178 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[1, 12, 190], [2, 2, 200], [1, 66, 138], [2, 48, 156], [1, 16, 190], [2, 2, 204], [1, 70, 138], [2, 8, 200], [1, 12, 198], [1, 1, 210], [1, 2, 210], [2, 2, 210], [1, 16, 198], [2, 14, 200], [1, 36, 180], [2, 30, 186], [1, 40, 178], [2, 2, 216], [1, 22, 198], [2, 20, 200], [1, 12, 210], [1, 1, 222], [1, 58, 166], [2, 30, 194], [1, 16, 210]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 203 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[1, 1, 226], [1, 78, 150], [1, 1, 228], [1, 2, 228], [2, 2, 228], [1, 10, 222], [1, 1, 232], [1, 36, 198], [2, 18, 216], [1, 4, 232], [2, 6, 230], [1, 10, 228], [1, 1, 238], [1, 30, 210], [1, 1, 240], [1, 4, 238], [2, 44, 198], [1, 6, 238], [2, 14, 230], [1, 36, 210], [2, 30, 216], [1, 10, 238], [2, 20, 228], [1, 12, 238], [1, 1, 250]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 228 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[1, 30, 222], [2, 114, 138], [1, 28, 226], [2, 44, 210], [1, 30, 226], [1, 1, 256], [1, 30, 228], [2, 30, 228], [1, 22, 238], [2, 50, 210], [1, 12, 250], [1, 1, 262], [1, 36, 228], [2, 36, 228], [1, 4, 262], [6, 62, 200], [1, 36, 232], [1, 1, 268], [1, 60, 210], [1, 1, 270], [1, 2, 270], [2, 2, 270], [1, 6, 268], [2, 20, 254], [1, 6, 270]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 253 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[1, 1, 276], [1, 28, 250], [2, 8, 270], [1, 12, 268], [1, 1, 280], [1, 6, 276], [1, 1, 282], [1, 16, 268], [2, 6, 278], [1, 4, 282], [2, 2, 284], [1, 6, 282], [2, 18, 270], [1, 10, 280], [2, 2, 288], [1, 12, 280], [1, 1, 292], [1, 18, 276], [2, 96, 198], [1, 16, 280], [2, 86, 210], [1, 6, 292], [2, 2, 296], [1, 18, 282], [2, 30, 270]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 278 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[1, 46, 256], [2, 2, 300], [1, 36, 268], [2, 26, 278], [1, 36, 270], [1, 1, 306], [1, 2, 306], [2, 2, 306], [1, 42, 268], [1, 1, 310], [1, 30, 282], [1, 1, 312], [1, 46, 268], [2, 14, 300], [1, 4, 312], [1, 1, 316], [1, 6, 312], [2, 30, 288], [1, 148, 172], [2, 120, 200], [1, 10, 312], [2, 2, 320], [2, 2, 321], [2, 36, 288], [1, 70, 256]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 303 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[2, 20, 306], [1, 12, 316], [2, 2, 326], [1, 108, 222], [1, 1, 330], [1, 2, 330], [2, 2, 330], [1, 4, 330], [2, 8, 326], [1, 30, 306], [1, 1, 336], [1, 2, 336], [2, 2, 336], [1, 10, 330], [2, 2, 338], [1, 6, 336], [2, 6, 336], [1, 28, 316], [2, 6, 338], [1, 10, 336], [1, 1, 346], [1, 42, 306], [1, 1, 348], [1, 40, 310], [2, 30, 320]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 328 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[1, 72, 280], [1, 1, 352], [1, 6, 348], [2, 168, 186], [1, 4, 352], [2, 2, 354], [1, 6, 352], [1, 1, 358], [1, 12, 348], [2, 30, 330], [1, 4, 358], [2, 8, 354], [1, 16, 348], [2, 44, 320], [1, 126, 240], [1, 1, 366], [1, 2, 366], [2, 2, 366], [1, 12, 358], [2, 20, 350], [1, 36, 336], [1, 1, 372], [1, 28, 346], [2, 48, 326], [1, 4, 372]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 353 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[2, 50, 326], [1, 66, 312], [1, 1, 378], [1, 2, 378], [2, 2, 378], [1, 16, 366], [1, 1, 382], [1, 6, 378], [2, 6, 378], [1, 40, 346], [2, 2, 384], [1, 6, 382], [1, 1, 388], [1, 60, 330], [2, 120, 270], [1, 4, 388], [2, 54, 338], [1, 36, 358], [2, 8, 386], [1, 60, 336], [1, 1, 396], [1, 10, 388], [2, 18, 380], [1, 12, 388], [1, 1, 400]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 378 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[1, 6, 396], [2, 36, 366], [1, 4, 400], [2, 6, 398], [1, 96, 310], [2, 2, 404], [1, 42, 366], [1, 1, 408], [1, 10, 400], [6, 46, 360], [1, 12, 400], [2, 2, 410], [1, 18, 396], [2, 48, 366], [1, 100, 316], [2, 2, 414], [1, 22, 396], [1, 1, 418], [1, 42, 378], [1, 1, 420], [1, 112, 310], [2, 8, 414], [1, 16, 408], [2, 14, 410], [1, 6, 420]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 403 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[2, 90, 336], [1, 46, 382], [2, 2, 426], [1, 10, 420], [1, 1, 430], [1, 96, 336], [1, 1, 432], [1, 4, 430], [2, 54, 380], [1, 36, 400], [2, 50, 386], [1, 6, 432], [1, 1, 438], [1, 2, 438], [2, 2, 438], [1, 4, 438], [1, 1, 442], [1, 78, 366], [2, 18, 426], [1, 46, 400], [2, 20, 426], [1, 18, 430], [1, 1, 448], [1, 30, 420], [6, 56, 390]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 428 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[1, 10, 442], [2, 14, 438], [1, 6, 448], [2, 44, 410], [1, 36, 420], [1, 1, 456], [1, 10, 448], [2, 20, 438], [1, 28, 432], [1, 1, 460], [1, 126, 336], [1, 1, 462], [1, 148, 316], [2, 78, 386], [1, 10, 456], [1, 1, 466], [1, 60, 408], [2, 114, 354], [1, 22, 448], [2, 2, 468], [1, 6, 466], [2, 2, 470], [1, 18, 456], [2, 174, 300], [1, 166, 310]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 453 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[2, 140, 336], [1, 16, 462], [1, 1, 478], [1, 18, 462], [2, 210, 270], [1, 4, 478], [2, 6, 476], [1, 18, 466], [2, 14, 470], [1, 30, 456], [1, 1, 486], [1, 22, 466], [2, 18, 470], [1, 12, 478], [1, 1, 490], [1, 6, 486], [2, 114, 378], [1, 16, 478], [2, 30, 464], [1, 10, 486], [2, 20, 476], [1, 36, 462], [1, 1, 498], [1, 2, 498], [2, 2, 498]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 478 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[1, 4, 498], [1, 1, 502], [1, 66, 438], [2, 198, 306], [1, 16, 490], [2, 2, 504], [1, 18, 490], [1, 1, 508], [1, 102, 408], [6, 6, 500], [1, 10, 502], [2, 2, 510], [1, 6, 508], [2, 8, 506], [1, 60, 456], [2, 6, 510], [1, 10, 508], [2, 2, 516], [1, 22, 498], [1, 1, 520], [1, 36, 486], [1, 1, 522], [1, 4, 520], [2, 8, 516], [1, 4, 522]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 503 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[2, 2, 524], [1, 66, 462], [2, 18, 510], [1, 22, 508], [2, 120, 410], [1, 30, 502], [2, 2, 530], [1, 36, 498], [2, 30, 504], [1, 46, 490], [2, 2, 534], [1, 16, 522], [2, 8, 530], [1, 18, 522], [1, 1, 540], [1, 100, 442], [2, 8, 534], [1, 4, 540], [2, 56, 488], [1, 180, 366], [1, 1, 546], [1, 2, 546], [2, 2, 546], [1, 30, 520], [2, 2, 548]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 528 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[1, 12, 540], [2, 18, 534], [1, 46, 508], [2, 44, 510], [1, 16, 540], [1, 1, 556], [1, 12, 546], [2, 48, 510], [1, 52, 508], [2, 2, 558], [1, 16, 546], [1, 1, 562], [1, 18, 546], [2, 18, 546], [1, 100, 466], [2, 2, 564], [1, 6, 562], [1, 1, 568], [1, 138, 432], [1, 1, 570], [1, 4, 568], [2, 8, 564], [1, 4, 570], [2, 26, 548], [1, 30, 546]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 553 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[1, 1, 576], [1, 2, 576], [2, 2, 576], [1, 10, 570], [2, 50, 530], [1, 6, 576], [2, 6, 576], [1, 28, 556], [2, 50, 534], [1, 40, 546], [1, 1, 586], [1, 150, 438], [2, 30, 558], [1, 22, 568], [2, 120, 470], [1, 6, 586], [1, 1, 592], [1, 18, 576], [2, 18, 576], [1, 10, 586], [2, 6, 590], [1, 30, 568], [1, 1, 598], [1, 60, 540], [1, 1, 600]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 578 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[1, 2, 600], [2, 2, 600], [1, 148, 456], [2, 50, 554], [1, 36, 570], [1, 1, 606], [1, 2, 606], [2, 2, 606], [1, 12, 598], [2, 2, 608], [1, 6, 606], [1, 1, 612], [1, 106, 508], [2, 18, 596], [1, 16, 600], [1, 1, 616], [1, 6, 612], [1, 1, 618], [1, 2, 618], [2, 2, 618], [1, 4, 618], [2, 14, 608], [1, 6, 618], [2, 6, 618], [1, 70, 556]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 603 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[2, 2, 624], [1, 12, 616], [2, 14, 614], [1, 12, 618], [1, 1, 630], [1, 16, 616], [2, 8, 624], [1, 4, 630], [2, 20, 614], [1, 30, 606], [2, 30, 606], [1, 22, 616], [2, 14, 624], [1, 10, 630], [1, 1, 640], [1, 12, 630], [1, 1, 642], [1, 46, 598], [2, 26, 618], [1, 30, 616], [1, 1, 646], [1, 6, 642], [2, 30, 618], [1, 58, 592], [2, 2, 648]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 628 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[1, 6, 646], [1, 1, 652], [1, 156, 498], [2, 6, 648], [1, 4, 652], [2, 56, 600], [1, 12, 646], [1, 1, 658], [1, 162, 498], [1, 1, 660], [1, 2, 660], [2, 2, 660], [1, 46, 618], [2, 68, 596], [1, 96, 570], [2, 120, 546], [1, 10, 658], [2, 8, 660], [1, 28, 642], [2, 20, 650], [1, 60, 612], [1, 1, 672], [1, 16, 658], [2, 14, 660], [1, 4, 672]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 653 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[1, 1, 676], [1, 72, 606], [2, 30, 648], [1, 28, 652], [2, 30, 650], [1, 6, 676], [1, 1, 682], [1, 78, 606], [2, 78, 606], [1, 4, 682], [2, 140, 546], [1, 6, 682], [2, 2, 686], [1, 18, 672], [1, 1, 690], [1, 2, 690], [2, 2, 690], [1, 36, 658], [2, 14, 680], [1, 36, 660], [2, 36, 660], [1, 40, 658], [2, 8, 690], [1, 18, 682], [1, 1, 700]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 678 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[1, 30, 672], [2, 78, 624], [1, 4, 700], [2, 14, 690], [1, 6, 700], [2, 2, 704], [1, 18, 690], [1, 1, 708], [1, 10, 700], [2, 200, 510], [1, 4, 708], [2, 26, 686], [1, 108, 606], [2, 156, 558], [1, 196, 520], [2, 2, 714], [1, 18, 700], [1, 1, 718], [1, 78, 642], [2, 210, 510], [1, 22, 700], [2, 6, 716], [1, 16, 708], [2, 20, 704], [1, 36, 690]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 703 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[1, 1, 726], [1, 2, 726], [2, 2, 726], [1, 30, 700], [2, 140, 590], [1, 6, 726], [1, 1, 732], [1, 16, 718], [2, 18, 716], [1, 46, 690], [2, 20, 716], [1, 12, 726], [1, 1, 738], [1, 22, 718], [2, 50, 690], [1, 4, 738], [1, 1, 742], [1, 198, 546], [2, 168, 576], [1, 4, 742], [2, 2, 744], [1, 22, 726], [2, 2, 746], [1, 18, 732], [1, 1, 750]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 728 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[1, 70, 682], [2, 8, 744], [1, 4, 750], [2, 50, 704], [1, 66, 690], [1, 1, 756], [1, 112, 646], [2, 114, 644], [1, 78, 682], [1, 1, 760], [1, 12, 750], [2, 48, 714], [1, 4, 760], [2, 48, 716], [1, 6, 760], [2, 50, 716], [1, 42, 726], [1, 1, 768], [1, 52, 718], [6, 6, 760], [1, 16, 756], [1, 1, 772], [1, 228, 546], [2, 48, 726], [1, 4, 772]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 753 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[2, 2, 774], [1, 10, 768], [2, 2, 776], [1, 30, 750], [2, 120, 660], [1, 130, 652], [2, 6, 776], [1, 16, 768], [2, 44, 740], [1, 240, 546], [1, 1, 786], [1, 70, 718], [2, 14, 774], [1, 52, 738], [2, 320, 470], [1, 66, 726], [2, 18, 774], [1, 196, 598], [2, 48, 746], [1, 36, 760], [1, 1, 796], [1, 12, 786], [2, 54, 744], [1, 28, 772], [2, 2, 798]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 778 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[1, 16, 786], [2, 2, 800], [1, 18, 786], [2, 6, 798], [1, 46, 760], [2, 2, 804], [1, 22, 786], [1, 1, 808], [1, 42, 768], [1, 1, 810], [1, 2, 810], [2, 2, 810], [1, 238, 576], [2, 8, 806], [1, 6, 810], [2, 6, 810], [1, 10, 808], [2, 8, 810], [1, 10, 810], [1, 1, 820], [1, 12, 810], [1, 1, 822], [1, 148, 676], [2, 6, 818], [1, 210, 616]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 803 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[1, 1, 826], [1, 6, 822], [1, 1, 828], [1, 2, 828], [2, 2, 828], [1, 4, 828], [2, 56, 776], [1, 6, 828], [2, 6, 828], [1, 16, 820], [2, 2, 834], [1, 78, 760], [1, 1, 838], [1, 18, 822], [6, 26, 810], [1, 16, 826], [2, 8, 834], [1, 16, 828], [2, 26, 818], [1, 60, 786], [2, 120, 726], [1, 28, 820], [2, 2, 846], [1, 22, 828], [2, 2, 848]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 828 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[1, 96, 756], [1, 1, 852], [1, 136, 718], [2, 26, 828], [1, 30, 826], [1, 1, 856], [1, 6, 852], [1, 1, 858], [1, 40, 820], [2, 120, 740], [1, 4, 858], [1, 1, 862], [1, 108, 756], [2, 90, 774], [1, 4, 862], [2, 20, 846], [1, 10, 858], [2, 2, 866], [1, 240, 630], [6, 56, 810], [1, 16, 856], [2, 2, 870], [1, 16, 858], [2, 14, 860], [1, 270, 606]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 853 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[1, 1, 876], [1, 2, 876], [2, 2, 876], [1, 28, 852], [1, 1, 880], [1, 30, 852], [1, 1, 882], [1, 238, 646], [2, 30, 854], [1, 4, 882], [1, 1, 886], [1, 12, 876], [2, 18, 870], [1, 28, 862], [2, 2, 888], [1, 10, 882], [2, 44, 848], [1, 126, 768], [2, 48, 846], [1, 10, 886], [2, 2, 894], [1, 22, 876], [2, 98, 800], [1, 18, 882], [2, 90, 810]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 878 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[1, 16, 886], [2, 2, 900], [1, 96, 808], [2, 50, 854], [1, 96, 810], [1, 1, 906], [1, 70, 838], [2, 14, 894], [1, 28, 882], [1, 1, 910], [1, 6, 906], [2, 78, 834], [1, 28, 886], [2, 14, 900], [1, 60, 856], [2, 116, 800], [1, 42, 876], [1, 1, 918], [1, 40, 880], [2, 120, 800], [1, 4, 918], [2, 56, 866], [1, 66, 858], [2, 30, 894], [1, 16, 910]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 903 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[2, 50, 876], [1, 10, 918], [1, 1, 928], [1, 78, 852], [6, 6, 920], [1, 22, 910], [2, 2, 930], [1, 6, 928], [2, 68, 866], [1, 60, 876], [1, 1, 936], [1, 2, 936], [2, 2, 936], [1, 58, 882], [1, 1, 940], [1, 312, 630], [2, 216, 726], [1, 4, 940], [2, 8, 936], [1, 6, 940], [1, 1, 946], [1, 30, 918], [2, 18, 930], [1, 448, 502], [2, 440, 510]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 928 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[1, 66, 886], [1, 1, 952], [1, 36, 918], [2, 78, 876], [1, 10, 946], [2, 6, 950], [1, 12, 946], [2, 2, 956], [1, 42, 918], [2, 30, 930], [1, 10, 952], [2, 6, 956], [1, 18, 946], [2, 8, 956], [1, 30, 936], [1, 1, 966], [1, 2, 966], [2, 2, 966], [1, 18, 952], [1, 1, 970], [1, 66, 906], [2, 228, 744], [1, 4, 970], [2, 18, 956], [1, 6, 970]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 953 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[1, 1, 976], [1, 12, 966], [2, 48, 930], [1, 100, 880], [6, 6, 970], [1, 6, 976], [1, 1, 982], [1, 18, 966], [2, 18, 966], [1, 4, 982], [2, 56, 930], [1, 36, 952], [2, 2, 986], [1, 108, 882], [1, 1, 990], [1, 22, 970], [2, 26, 966], [1, 18, 976], [2, 44, 950], [1, 420, 576], [1, 1, 996], [1, 2, 996], [2, 2, 996], [1, 10, 990], [2, 2, 998]]
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

end OMA.AOeisA229969_conjecture_5bTab

open OMA.AOeisA229969_conjecture_5bTab in
theorem OMA.solution : OMA.R_OeisA229969_conjecture_5b_R1.H1 := by
  intro n hn hne hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact good_sound n w hn hne hw
