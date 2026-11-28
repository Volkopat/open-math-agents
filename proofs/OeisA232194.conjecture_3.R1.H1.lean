import OMAReductions.R_OeisA232194_conjecture_3_R1
import Mathlib

-- Step OeisA232194.conjecture_3.R1.H1: hypothesis H1 of reduction OeisA232194.conjecture_3.R1
-- Credit: @prathameshnium. Finite check for 0 < n ≤ 1000, n ∉ {1, 30, 54}.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 675863.

/-! Step OeisA232194.conjecture_3.R1.H1. -/

namespace OMA.AOeisA232194_C3Tab

/-- `noDiv p f d = true` means: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test, with a fixed divisor budget `824` (enough for every number checked
here; a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 824 2

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
  have hnd := noDiv_sound p 824 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness `x`. -/
def good (n x : ℕ) : Bool := Nat.beq n 30 || (Nat.beq n 54 || (Nat.ble 1 x && (Nat.blt x n && (isPrimeB (n * x + (n - x)) && isPrimeB (n * (n - x) + x)))))

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

/-! One witness for each `n = 2, …, 1000`, in chunks of 25 so each kernel check stays small. -/
def w0 : List ℕ := [1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 5, 5, 5, 7, 3, 6, 5, 9, 9, 8, 5, 8, 5, 12, 3]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 2 w0 = true := by decide +kernel

def w1 : List ℕ := [11, 13, 14, 0, 13, 11, 13, 13, 17, 17, 15, 5, 11, 13, 12, 1, 20, 21, 14, 21, 20, 23, 24, 17, 23]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 27 w1 = true := by decide +kernel

def w2 : List ℕ := [25, 23, 0, 26, 23, 22, 9, 26, 13, 26, 5, 23, 31, 24, 31, 32, 23, 28, 27, 35, 35, 28, 23, 34, 37]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 52 w2 = true := by decide +kernel

def w3 : List ℕ := [27, 29, 36, 33, 26, 37, 35, 31, 42, 41, 40, 23, 30, 43, 38, 41, 34, 41, 44, 47, 46, 39, 40, 43, 47]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 77 w3 = true := by decide +kernel

def w4 : List ℕ := [41, 44, 35, 29, 23, 45, 49, 44, 47, 47, 45, 29, 55, 54, 51, 47, 55, 54, 53, 50, 27, 55, 51, 56, 55]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 102 w4 = true := by decide +kernel

def w5 : List ℕ := [55, 23, 56, 51, 54, 61, 65, 65, 58, 59, 47, 65, 56, 51, 67, 51, 69, 49, 72, 69, 71, 45, 29, 67, 74]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 127 w5 = true := by decide +kernel

def w6 : List ℕ := [5, 58, 69, 69, 71, 56, 35, 79, 69, 78, 71, 78, 81, 68, 73, 72, 13, 84, 77, 83, 77, 69, 53, 86, 57]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 152 w6 = true := by decide +kernel

def w7 : List ℕ := [86, 83, 51, 77, 90, 57, 89, 85, 87, 91, 90, 89, 73, 79, 90, 91, 95, 93, 97, 89, 96, 65, 96, 11, 94]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 177 w7 = true := by decide +kernel

def w8 : List ℕ := [67, 99, 83, 86, 95, 95, 103, 98, 103, 95, 101, 95, 103, 98, 67, 87, 99, 83, 87, 107, 91, 104, 111, 89, 97]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 202 w8 = true := by decide +kernel

def w9 : List ℕ := [110, 109, 110, 83, 107, 111, 99, 101, 111, 111, 106, 93, 98, 101, 116, 117, 110, 109, 117, 109, 115, 105, 110, 119, 117]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 227 w9 = true := by decide +kernel

def w10 : List ℕ := [101, 123, 35, 124, 75, 101, 103, 124, 119, 118, 67, 105, 115, 128, 101, 130, 69, 125, 41, 121, 107, 125, 133, 122, 137]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 252 w10 = true := by decide +kernel

def w11 : List ℕ := [126, 83, 139, 121, 125, 121, 125, 89, 131, 141, 132, 133, 140, 143, 131, 35, 114, 143, 143, 125, 140, 125, 140, 137, 143]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 277 w11 = true := by decide +kernel

def w12 : List ℕ := [147, 139, 123, 131, 145, 152, 149, 154, 143, 150, 107, 135, 125, 157, 151, 156, 109, 156, 119, 155, 145, 158, 133, 146, 137]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 302 w12 = true := by decide +kernel

def w13 : List ℕ := [161, 145, 164, 161, 162, 77, 163, 153, 159, 131, 166, 153, 154, 103, 164, 155, 164, 159, 169, 165, 167, 149, 148, 141, 166]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 327 w13 = true := by decide +kernel

def w14 : List ℕ := [147, 140, 175, 166, 155, 127, 173, 150, 173, 177, 75, 173, 155, 162, 181, 151, 165, 173, 161, 185, 181, 185, 161, 187, 143]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 352 w14 = true := by decide +kernel

def w15 : List ℕ := [152, 103, 188, 153, 188, 177, 180, 173, 186, 183, 161, 193, 156, 187, 195, 81, 194, 141, 194, 163, 187, 195, 199, 199, 191]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 377 w15 = true := by decide +kernel

def w16 : List ℕ := [47, 200, 195, 191, 191, 177, 175, 203, 137, 203, 201, 200, 199, 196, 185, 196, 189, 204, 173, 200, 191, 199, 175, 209, 187]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 402 w16 = true := by decide +kernel

def w17 : List ℕ := [197, 209, 203, 213, 210, 101, 210, 215, 211, 189, 210, 209, 210, 219, 211, 215, 168, 221, 209, 201, 215, 195, 206, 211, 221]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 427 w17 = true := by decide +kernel

def w18 : List ℕ := [207, 188, 209, 219, 217, 227, 215, 205, 203, 230, 215, 229, 225, 214, 231, 230, 179, 225, 221, 217, 217, 228, 229, 236, 237]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 452 w18 = true := by decide +kernel

def w19 : List ℕ := [190, 195, 206, 187, 236, 221, 188, 223, 203, 241, 222, 125, 236, 239, 236, 115, 243, 219, 229, 239, 230, 229, 246, 231, 244]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 477 w19 = true := by decide +kernel

def w20 : List ℕ := [247, 243, 251, 249, 251, 236, 133, 248, 191, 254, 255, 244, 251, 254, 199, 250, 135, 248, 239, 255, 247, 255, 221, 256, 241]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 502 w20 = true := by decide +kernel

def w21 : List ℕ := [230, 203, 264, 219, 254, 221, 263, 241, 262, 261, 257, 235, 258, 269, 259, 255, 250, 265, 272, 209, 272, 93, 229, 273, 272]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 527 w21 = true := by decide +kernel

def w22 : List ℕ := [271, 260, 275, 268, 271, 275, 275, 279, 279, 274, 237, 264, 271, 276, 263, 277, 279, 260, 271, 249, 285, 278, 209, 287, 269]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 552 w22 = true := by decide +kernel

def w23 : List ℕ := [286, 209, 286, 289, 290, 257, 273, 285, 287, 261, 272, 253, 281, 287, 284, 277, 285, 265, 283, 269, 265, 265, 278, 259, 293]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 577 w23 = true := by decide +kernel

def w24 : List ℕ := [297, 293, 293, 299, 301, 276, 299, 304, 303, 303, 301, 289, 269, 298, 295, 287, 233, 293, 263, 289, 305, 264, 283, 304, 305]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 602 w24 = true := by decide +kernel

def w25 : List ℕ := [296, 245, 309, 313, 311, 311, 278, 289, 308, 277, 306, 303, 289, 319, 320, 287, 320, 293, 317, 317, 320, 299, 321, 323, 319]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 627 w25 = true := by decide +kernel

def w26 : List ℕ := [321, 294, 319, 317, 311, 317, 319, 323, 317, 327, 321, 313, 319, 324, 329, 330, 333, 334, 329, 333, 335, 333, 309, 326, 331]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 652 w26 = true := by decide +kernel

def w27 : List ℕ := [327, 293, 334, 309, 329, 325, 335, 325, 333, 341, 316, 295, 339, 329, 343, 341, 298, 345, 297, 341, 286, 285, 343, 321, 342]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 677 w27 = true := by decide +kernel

def w28 : List ℕ := [317, 350, 345, 322, 335, 306, 343, 343, 341, 326, 335, 329, 325, 332, 357, 320, 289, 348, 331, 352, 291, 353, 279, 341, 355]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 702 w28 = true := by decide +kernel

def w29 : List ℕ := [356, 269, 355, 351, 354, 347, 363, 341, 361, 353, 365, 325, 336, 339, 365, 281, 354, 353, 362, 293, 371, 359, 366, 343, 374]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 727 w29 = true := by decide +kernel

def w30 : List ℕ := [327, 373, 369, 356, 353, 372, 323, 350, 371, 377, 347, 370, 371, 358, 381, 282, 283, 373, 353, 382, 297, 270, 373, 384, 383]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 752 w30 = true := by decide +kernel

def w31 : List ℕ := [377, 383, 371, 383, 390, 387, 373, 333, 377, 377, 382, 293, 388, 389, 377, 301, 394, 381, 383, 381, 377, 383, 388, 399, 398]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 777 w31 = true := by decide +kernel

def w32 : List ℕ := [377, 380, 365, 397, 393, 400, 333, 383, 401, 400, 401, 394, 395, 402, 385, 371, 333, 409, 403, 392, 385, 408, 383, 404, 393]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 802 w32 = true := by decide +kernel

def w33 : List ℕ := [360, 409, 403, 347, 394, 407, 405, 359, 416, 395, 322, 385, 414, 337, 401, 405, 374, 403, 404, 391, 417, 423, 401, 381, 398]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 827 w33 = true := by decide +kernel

def w34 : List ℕ := [415, 425, 425, 419, 427, 426, 355, 425, 419, 407, 421, 420, 413, 411, 425, 415, 419, 434, 433, 424, 387, 430, 431, 426, 401]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 852 w34 = true := by decide +kernel

def w35 : List ℕ := [416, 299, 425, 409, 440, 355, 438, 399, 382, 399, 441, 439, 433, 443, 434, 397, 440, 413, 443, 429, 382, 423, 425, 419, 436]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 877 w35 = true := by decide +kernel

def w36 : List ℕ := [447, 449, 445, 437, 385, 450, 425, 454, 367, 453, 365, 423, 453, 443, 449, 440, 419, 454, 453, 452, 387, 459, 461, 461, 461]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 902 w36 = true := by decide +kernel

def w37 : List ℕ := [451, 429, 464, 449, 463, 465, 440, 461, 467, 457, 462, 435, 461, 451, 462, 445, 423, 471, 463, 471, 456, 413, 474, 461, 455]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 927 w37 = true := by decide +kernel

def w38 : List ℕ := [465, 473, 415, 462, 473, 476, 453, 446, 421, 454, 465, 464, 425, 441, 467, 462, 449, 440, 447, 467, 431, 479, 471, 484, 483]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 952 w38 = true := by decide +kernel

def w39 : List ℕ := [461, 439, 488, 467, 487, 437, 489, 485, 488, 485, 460, 449, 444, 493, 488, 311, 490, 481, 486, 497, 465, 405, 460, 417]
theorem len39 : w39.length = 24 := rfl
theorem ok39 : checkList 977 w39 = true := by decide +kernel

theorem chunk {l : List ℕ} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `2 ≤ n ≤ 1000` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 2 ≤ n) (h2 : n ≤ 1000) : ∃ x, good n x = true := by
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

theorem good_sound (n x : ℕ) (h30 : n ≠ 30) (h54 : n ≠ 54) (h : good n x = true) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ (n * x + y).Prime ∧ (n * y + x).Prime := by
  simp only [good, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq] at h
  rcases h with h | h | ⟨h1, h2, h3, h4⟩
  · exact absurd h h30
  · exact absurd h h54
  · exact ⟨x, n - x, by omega, by omega, by omega, isPrimeB_sound _ h3, isPrimeB_sound _ h4⟩

end OMA.AOeisA232194_C3Tab

open OMA.AOeisA232194_C3Tab in
theorem OMA.solution : OMA.R_OeisA232194_conjecture_3_R1.H1 := by
  intro n hn hB hne
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
  obtain ⟨h1, h30, h54⟩ := hne
  obtain ⟨x, hx⟩ := cover n (by omega) (by omega)
  exact good_sound n x h30 h54 hx
