import OMAReductions.R_OeisA232194_conjecture_6_R1
import Mathlib

-- Step OeisA232194.conjecture_6.R1.H1: hypothesis H1 of reduction OeisA232194.conjecture_6.R1
-- Credit: @prathameshnium. Finite check for 5 < n ≤ 1000.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 82872901.

/-! Step OeisA232194.conjecture_6.R1.H1. -/

namespace OMA.AOeisA232194_C6Tab

/-- `noDiv p f d = true` means: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test, with a fixed divisor budget `9105` (enough for every number checked
here; a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 9105 2

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
  have hnd := noDiv_sound p 9105 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness `x`. -/
def good (n q : ℕ) : Bool := Nat.ble 1 q && (Nat.blt q n && (isPrimeB (n - q) && isPrimeB (n * q ^ 2 + 1)))

/-- `checkList n l`: entry `i` of `l` is a witness that `good (n + i) _` holds. -/
def checkList : ℕ → List ℕ → Bool
  | _, [] => true
  | n, x :: xs => good n x && checkList (n + 1) xs

theorem checkList_sound : ∀ (l : List ℕ) (n : ℕ), checkList n l = true →
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

/-! One witness for each `n = 6, …, 1000`, in chunks of 25 so each kernel check stays small. -/
def w0 : List ℕ := [1, 2, 3, 2, 5, 6, 1, 2, 3, 2, 5, 6, 1, 8, 3, 4, 3, 6, 5, 2, 15, 4, 5, 12, 1]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 6 w0 = true := by decide +kernel

def w1 : List ℕ := [20, 9, 10, 3, 24, 25, 14, 9, 2, 29, 30, 1, 2, 3, 2, 5, 6, 5, 2, 9, 10, 5, 24, 7, 14]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 31 w1 = true := by decide +kernel

def w2 : List ℕ := [15, 10, 5, 30, 1, 50, 9, 4, 3, 6, 19, 8, 21, 2, 3, 24, 1, 2, 15, 4, 5, 36, 5, 20, 9]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 56 w2 = true := by decide +kernel

def w3 : List ℕ := [10, 3, 12, 13, 6, 39, 8, 9, 18, 11, 30, 3, 4, 5, 12, 29, 14, 15, 2, 11, 30, 1, 6, 3, 2]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 81 w3 = true := by decide +kernel

def w4 : List ℕ := [45, 6, 1, 8, 3, 4, 3, 12, 5, 2, 9, 4, 39, 12, 7, 24, 9, 10, 15, 66, 29, 18, 45, 50, 3]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 106 w4 = true := by decide +kernel

def w5 : List ℕ := [84, 5, 6, 27, 4, 29, 6, 1, 2, 27, 34, 3, 12, 7, 8, 9, 16, 11, 78, 1, 80, 21, 2, 5, 6]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 131 w5 = true := by decide +kernel

def w6 : List ℕ := [25, 6, 9, 8, 33, 24, 5, 6, 15, 2, 35, 30, 5, 2, 3, 34, 9, 6, 7, 2, 69, 4, 5, 108, 1]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 156 w6 = true := by decide +kernel

def w7 : List ℕ := [30, 45, 2, 3, 6, 5, 6, 39, 8, 9, 24, 1, 2, 3, 4, 15, 30, 1, 2, 3, 4, 5, 6, 5, 8]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 181 w7 = true := by decide +kernel

def w8 : List ℕ := [15, 8, 11, 12, 11, 14, 15, 2, 35, 18, 19, 18, 27, 22, 21, 24, 11, 24, 45, 14, 45, 30, 1, 18, 39]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 206 w8 = true := by decide +kernel

def w9 : List ℕ := [4, 3, 6, 5, 2, 69, 4, 15, 48, 1, 14, 3, 4, 5, 6, 5, 6, 9, 8, 17, 24, 11, 2, 3, 28]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 231 w9 = true := by decide +kernel

def w10 : List ℕ := [15, 18, 19, 48, 3, 4, 5, 30, 13, 2, 75, 4, 5, 12, 1, 14, 21, 2, 3, 6, 65, 6, 21, 2, 3]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 256 w10 = true := by decide +kernel

def w11 : List ℕ := [90, 1, 14, 3, 4, 5, 6, 11, 12, 33, 10, 15, 12, 17, 2, 15, 20, 5, 60, 19, 20, 21, 32, 23, 48]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 281 w11 = true := by decide +kernel

def w12 : List ℕ := [25, 66, 69, 2, 3, 84, 1, 20, 33, 8, 5, 24, 5, 2, 39, 94, 9, 30, 7, 48, 9, 76, 17, 90, 19]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 306 w12 = true := by decide +kernel

def w13 : List ℕ := [14, 69, 20, 17, 18, 29, 24, 21, 62, 3, 84, 25, 12, 27, 34, 9, 66, 1, 32, 69, 20, 3, 84, 47, 6]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 331 w13 = true := by decide +kernel

def w14 : List ℕ := [9, 26, 5, 78, 49, 30, 3, 26, 15, 12, 35, 14, 21, 10, 3, 114, 13, 24, 63, 8, 69, 18, 61, 12, 27]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 356 w14 = true := by decide +kernel

def w15 : List ℕ := [44, 33, 186, 5, 12, 39, 14, 29, 42, 43, 24, 3, 10, 5, 6, 79, 8, 159, 2, 17, 144, 13, 2, 3, 4]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 381 w15 = true := by decide +kernel

def w16 : List ℕ := [5, 6, 7, 8, 9, 14, 3, 12, 35, 26, 15, 16, 125, 18, 1, 54, 21, 2, 5, 36, 5, 6, 69, 8, 33]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 406 w16 = true := by decide +kernel

def w17 : List ℕ := [174, 1, 2, 3, 2, 15, 6, 17, 8, 39, 10, 9, 12, 13, 12, 45, 14, 15, 18, 7, 30, 63, 14, 5, 6]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 431 w17 = true := by decide +kernel

def w18 : List ℕ := [119, 26, 57, 38, 11, 234, 1, 14, 3, 2, 9, 24, 5, 2, 3, 4, 5, 6, 7, 54, 9, 10, 11, 48, 37]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 456 w18 = true := by decide +kernel

def w19 : List ℕ := [50, 3, 20, 5, 18, 19, 24, 27, 58, 23, 90, 5, 2, 3, 28, 5, 78, 11, 20, 33, 10, 3, 186, 5, 6]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 481 w19 = true := by decide +kernel

def w20 : List ℕ := [39, 16, 9, 42, 19, 24, 93, 4, 47, 6, 25, 14, 9, 32, 11, 54, 1, 20, 33, 16, 5, 6, 7, 8, 27]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 506 w20 = true := by decide +kernel

def w21 : List ℕ := [10, 9, 12, 13, 12, 225, 14, 107, 18, 17, 20, 21, 20, 77, 24, 239, 56, 27, 58, 3, 60, 109, 12, 63, 8]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 531 w21 = true := by decide +kernel

def w22 : List ℕ := [15, 54, 17, 2, 39, 20, 5, 6, 17, 8, 75, 10, 11, 12, 1, 24, 63, 2, 3, 18, 5, 6, 9, 8, 11]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 556 w22 = true := by decide +kernel

def w23 : List ℕ := [90, 5, 14, 117, 8, 119, 96, 17, 2, 21, 14, 15, 24, 23, 2, 39, 20, 5, 12, 1, 14, 3, 4, 3, 12]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 581 w23 = true := by decide +kernel

def w24 : List ℕ := [29, 14, 39, 2, 9, 54, 19, 26, 105, 38, 29, 18, 1, 2, 3, 20, 5, 30, 5, 6, 9, 8, 11, 30, 11]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 606 w24 = true := by decide +kernel

def w25 : List ℕ := [14, 33, 62, 33, 126, 5, 36, 69, 8, 21, 324, 1, 12, 75, 4, 29, 6, 17, 18, 3, 10, 5, 6, 13, 2]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 631 w25 = true := by decide +kernel

def w26 : List ℕ := [69, 4, 5, 180, 1, 84, 9, 10, 23, 18, 5, 8, 15, 22, 11, 30, 25, 14, 15, 16, 35, 24, 19, 32, 3]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 656 w26 = true := by decide +kernel

def w27 : List ℕ := [74, 9, 30, 85, 2, 69, 4, 29, 42, 7, 60, 9, 16, 3, 42, 5, 20, 15, 38, 9, 84, 19, 26, 3, 14]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 681 w27 = true := by decide +kernel

def w28 : List ℕ := [45, 6, 7, 8, 51, 64, 21, 12, 5, 6, 69, 44, 57, 60, 11, 60, 21, 14, 15, 84, 35, 44, 27, 2, 3]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 706 w28 = true := by decide +kernel

def w29 : List ℕ := [90, 5, 14, 117, 8, 9, 18, 5, 12, 87, 40, 3, 24, 53, 6, 45, 4, 5, 48, 17, 24, 9, 52, 27, 54]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 731 w29 = true := by decide +kernel

def w30 : List ℕ := [65, 6, 15, 2, 3, 330, 5, 12, 45, 4, 9, 66, 7, 60, 117, 10, 3, 30, 13, 6, 219, 4, 51, 120, 19]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 756 w30 = true := by decide +kernel

def w31 : List ℕ := [20, 21, 10, 15, 12, 25, 44, 15, 28, 17, 174, 5, 6, 75, 34, 39, 138, 37, 12, 147, 44, 5, 6, 7, 8]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 781 w31 = true := by decide +kernel

def w32 : List ℕ := [9, 10, 47, 90, 1, 54, 3, 2, 27, 54, 65, 8, 75, 10, 23, 180, 1, 14, 3, 2, 39, 30, 1, 72, 9]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 806 w32 = true := by decide +kernel

def w33 : List ℕ := [4, 3, 6, 7, 8, 75, 8, 11, 12, 11, 14, 33, 14, 5, 24, 19, 24, 21, 20, 29, 54, 25, 24, 255, 26]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 831 w33 = true := by decide +kernel

def w34 : List ℕ := [35, 30, 1, 20, 3, 40, 3, 6, 5, 2, 45, 4, 5, 42, 13, 44, 15, 34, 45, 12, 65, 18, 15, 2, 21]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 856 w34 = true := by decide +kernel

def w35 : List ℕ := [54, 1, 2, 75, 2, 75, 66, 11, 2, 3, 10, 9, 120, 83, 74, 9, 40, 35, 12, 19, 14, 39, 16, 47, 18]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 881 w35 = true := by decide +kernel

def w36 : List ℕ := [155, 20, 21, 2, 3, 234, 25, 6, 33, 34, 5, 6, 7, 62, 9, 40, 39, 42, 13, 6, 69, 16, 9, 18, 49]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 906 w36 = true := by decide +kernel

def w37 : List ℕ := [20, 3, 4, 75, 24, 49, 30, 9, 10, 3, 84, 13, 14, 33, 4, 39, 18, 41, 2, 129, 4, 5, 66, 7, 2]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 931 w37 = true := by decide +kernel

def w38 : List ℕ := [69, 4, 21, 78, 7, 50, 15, 104, 35, 138, 79, 26, 21, 2, 3, 24, 35, 92, 33, 4, 89, 24, 49, 2, 3]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 956 w38 = true := by decide +kernel

def w39 : List ℕ := [10, 5, 54, 13, 48, 9, 34, 11, 42, 13, 114, 21, 16, 27, 12, 55, 14, 69, 32, 3]
theorem len39 : w39.length = 20 := rfl
theorem ok39 : checkList 981 w39 = true := by decide +kernel

theorem chunk {l : List ℕ} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `6 ≤ n ≤ 1000` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 6 ≤ n) (h2 : n ≤ 1000) : ∃ x, good n x = true := by
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

theorem good_sound (n q : ℕ) (h : good n q = true) :
    ∃ p q : ℕ, 0 < q ∧ p + q = n ∧ p.Prime ∧ (n * q ^ 2 + 1).Prime := by
  simp only [good, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨n - q, q, by omega, by omega, isPrimeB_sound _ h3, isPrimeB_sound _ h4⟩

end OMA.AOeisA232194_C6Tab

open OMA.AOeisA232194_C6Tab in
theorem OMA.solution : OMA.R_OeisA232194_conjecture_6_R1.H1 := by
  intro n hn hB
  obtain ⟨q, hq⟩ := cover n (by omega) (by omega)
  exact good_sound n q hq
