import OMAReductions.R_OeisA232194_conjecture_5_R1
import Mathlib

-- Step OeisA232194.conjecture_5.R1.H1: hypothesis H1 of reduction OeisA232194.conjecture_5.R1
-- Credit: @prathameshnium. Finite check for 1 < n ≤ 1000, n ≠ 8.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 31646701.

/-! Step OeisA232194.conjecture_5.R1.H1. -/

namespace OMA.AOeisA232194_C5Tab

/-- `noDiv p f d = true` means: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test, with a fixed divisor budget `5627` (enough for every number checked
here; a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 5627 2

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
  have hnd := noDiv_sound p 5627 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness `x`. -/
def good (n x : ℕ) : Bool := Nat.beq n 8 || (Nat.ble 1 x && (Nat.blt x n && isPrimeB (x ^ 4 + n * (n - x))))

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
def w0 : List ℕ := [1, 1, 1, 2, 1, 1, 0, 1, 3, 5, 5, 1, 5, 1, 1, 2, 1, 4, 3, 1, 1, 2, 17, 1, 5]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 2 w0 = true := by decide +kernel

def w1 : List ℕ := [2, 1, 5, 17, 4, 3, 2, 1, 2, 5, 7, 5, 2, 13, 6, 1, 3, 5, 2, 9, 2, 5, 9, 21, 1]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 27 w1 = true := by decide +kernel

def w2 : List ℕ := [37, 2, 5, 1, 3, 13, 3, 6, 1, 4, 3, 1, 19, 2, 5, 1, 5, 2, 1, 3, 1, 7, 17, 4, 1]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 52 w2 = true := by decide +kernel

def w3 : List ℕ := [3, 1, 1, 9, 1, 9, 6, 11, 6, 3, 2, 3, 2, 1, 3, 3, 7, 9, 3, 13, 3, 3, 2, 3, 5]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 77 w3 = true := by decide +kernel

def w4 : List ℕ := [1, 4, 17, 2, 1, 2, 7, 4, 69, 1, 3, 3, 31, 6, 9, 4, 1, 12, 1, 9, 9, 5, 75, 3, 11]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 102 w4 = true := by decide +kernel

def w5 : List ℕ := [4, 5, 4, 9, 9, 1, 9, 5, 2, 3, 3, 5, 1, 17, 5, 3, 3, 1, 13, 3, 4, 1, 12, 11, 4]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 127 w5 = true := by decide +kernel

def w6 : List ℕ := [9, 4, 1, 6, 1, 7, 3, 2, 7, 5, 1, 3, 5, 4, 13, 6, 1, 1, 9, 4, 7, 2, 1, 3, 3]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 152 w6 = true := by decide +kernel

def w7 : List ℕ := [5, 3, 2, 11, 3, 5, 4, 19, 3, 25, 7, 9, 4, 1, 5, 5, 1, 9, 4, 45, 3, 5, 6, 17, 14]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 177 w7 = true := by decide +kernel

def w8 : List ℕ := [13, 2, 5, 3, 9, 2, 19, 5, 1, 4, 3, 4, 21, 12, 1, 4, 5, 5, 7, 3, 5, 12, 5, 11, 9]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 202 w8 = true := by decide +kernel

def w9 : List ℕ := [3, 23, 6, 3, 8, 1, 12, 35, 4, 9, 5, 15, 2, 7, 4, 29, 2, 9, 9, 1, 1, 5, 4, 13, 6]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 227 w9 = true := by decide +kernel

def w10 : List ℕ := [5, 3, 9, 13, 3, 2, 5, 4, 9, 10, 3, 2, 5, 6, 3, 1, 15, 6, 19, 4, 33, 4, 15, 8, 13]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 252 w10 = true := by decide +kernel

def w11 : List ℕ := [3, 5, 1, 3, 6, 19, 6, 5, 4, 3, 5, 5, 1, 3, 4, 7, 5, 1, 9, 9, 4, 3, 2, 11, 4]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 277 w11 = true := by decide +kernel

def w12 : List ℕ := [3, 8, 21, 2, 11, 6, 5, 5, 1, 5, 7, 4, 5, 4, 9, 5, 13, 4, 21, 4, 9, 6, 5, 6, 3]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 302 w12 = true := by decide +kernel

def w13 : List ℕ := [2, 3, 6, 1, 3, 9, 5, 39, 3, 13, 6, 9, 2, 3, 5, 5, 4, 5, 1, 13, 5, 19, 4, 3, 4]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 327 w13 = true := by decide +kernel

def w14 : List ℕ := [3, 3, 5, 7, 15, 2, 1, 5, 11, 9, 21, 5, 9, 6, 5, 3, 3, 7, 1, 6, 7, 10, 21, 2, 13]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 352 w14 = true := by decide +kernel

def w15 : List ℕ := [5, 5, 4, 9, 5, 1, 5, 5, 4, 3, 2, 13, 5, 7, 4, 11, 4, 19, 2, 5, 7, 3, 5, 3, 5]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 377 w15 = true := by decide +kernel

def w16 : List ℕ := [11, 4, 39, 1, 1, 5, 5, 4, 9, 5, 9, 5, 5, 1, 3, 1, 25, 5, 13, 13, 5, 4, 7, 9, 19]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 402 w16 = true := by decide +kernel

def w17 : List ℕ := [6, 5, 7, 3, 5, 5, 4, 11, 1, 3, 6, 11, 12, 9, 8, 3, 5, 5, 4, 5, 4, 1, 24, 47, 3]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 427 w17 = true := by decide +kernel

def w18 : List ℕ := [11, 5, 7, 8, 5, 1, 5, 10, 9, 6, 17, 12, 9, 11, 9, 5, 5, 12, 41, 10, 13, 5, 5, 6, 9]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 452 w18 = true := by decide +kernel

def w19 : List ℕ := [5, 3, 5, 17, 4, 5, 4, 9, 3, 19, 3, 5, 5, 1, 5, 19, 4, 9, 4, 1, 5, 7, 9, 17, 4]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 477 w19 = true := by decide +kernel

def w20 : List ℕ := [9, 6, 19, 12, 21, 19, 19, 5, 11, 9, 5, 5, 19, 3, 5, 6, 5, 5, 3, 5, 7, 4, 5, 2, 1]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 502 w20 = true := by decide +kernel

def w21 : List ℕ := [5, 13, 9, 9, 1, 3, 3, 5, 6, 9, 4, 1, 6, 11, 1, 11, 5, 7, 2, 5, 12, 9, 5, 3, 5]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 527 w21 = true := by decide +kernel

def w22 : List ℕ := [1, 24, 5, 7, 9, 12, 19, 6, 23, 1, 3, 5, 31, 7, 9, 5, 1, 9, 11, 9, 5, 1, 15, 3, 23]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 552 w22 = true := by decide +kernel

def w23 : List ℕ := [4, 5, 7, 1, 5, 11, 1, 5, 1, 9, 6, 11, 6, 33, 4, 3, 6, 7, 6, 21, 10, 7, 2, 7, 3]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 577 w23 = true := by decide +kernel

def w24 : List ℕ := [11, 5, 1, 6, 1, 6, 11, 11, 1, 5, 7, 1, 21, 4, 13, 5, 5, 9, 3, 11, 1, 5, 11, 7, 9]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 602 w24 = true := by decide +kernel

def w25 : List ℕ := [4, 7, 5, 13, 6, 9, 5, 31, 6, 1, 6, 3, 2, 7, 11, 5, 1, 15, 7, 31, 5, 11, 6, 11, 4]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 627 w25 = true := by decide +kernel

def w26 : List ℕ := [3, 5, 5, 4, 5, 4, 15, 5, 17, 9, 5, 2, 27, 3, 13, 9, 9, 5, 21, 3, 1, 4, 21, 4, 15]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 652 w26 = true := by decide +kernel

def w27 : List ℕ := [2, 7, 10, 9, 5, 27, 3, 5, 16, 3, 7, 15, 5, 31, 9, 5, 5, 27, 3, 13, 1, 5, 5, 33, 9]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 677 w27 = true := by decide +kernel

def w28 : List ℕ := [1, 4, 5, 11, 3, 12, 13, 7, 11, 5, 13, 5, 25, 4, 3, 4, 7, 6, 7, 6, 5, 8, 9, 12, 5]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 702 w28 = true := by decide +kernel

def w29 : List ℕ := [3, 3, 2, 21, 5, 5, 12, 9, 2, 1, 8, 5, 7, 9, 5, 9, 12, 5, 4, 5, 5, 1, 6, 11, 3]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 727 w29 = true := by decide +kernel

def w30 : List ℕ := [11, 5, 37, 6, 1, 3, 5, 20, 3, 5, 1, 3, 11, 19, 19, 9, 5, 6, 9, 8, 37, 3, 7, 6, 23]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 752 w30 = true := by decide +kernel

def w31 : List ℕ := [5, 15, 12, 19, 4, 47, 8, 45, 6, 1, 7, 9, 4, 31, 5, 5, 7, 5, 7, 9, 6, 13, 6, 9, 14]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 777 w31 = true := by decide +kernel

def w32 : List ℕ := [1, 6, 5, 6, 23, 5, 9, 9, 7, 10, 5, 5, 7, 11, 5, 9, 5, 4, 1, 14, 17, 3, 5, 17, 3]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 802 w32 = true := by decide +kernel

def w33 : List ℕ := [6, 5, 10, 23, 5, 9, 6, 11, 9, 21, 5, 7, 14, 1, 6, 15, 2, 19, 9, 11, 3, 5, 7, 13, 5]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 827 w33 = true := by decide +kernel

def w34 : List ℕ := [7, 4, 5, 8, 9, 6, 1, 16, 9, 5, 9, 5, 5, 3, 9, 5, 15, 2, 19, 6, 5, 4, 9, 6, 5]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 852 w34 = true := by decide +kernel

def w35 : List ℕ := [10, 9, 1, 7, 5, 19, 12, 5, 13, 19, 9, 17, 4, 3, 5, 3, 2, 11, 6, 5, 7, 1, 9, 1, 9]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 877 w35 = true := by decide +kernel

def w36 : List ℕ := [5, 5, 25, 12, 13, 15, 9, 5, 19, 5, 5, 4, 21, 4, 9, 6, 25, 1, 21, 1, 21, 6, 17, 12, 15]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 902 w36 = true := by decide +kernel

def w37 : List ℕ := [7, 9, 6, 7, 6, 15, 8, 19, 23, 5, 6, 5, 5, 3, 20, 5, 4, 11, 4, 3, 30, 5, 9, 9, 1]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 927 w37 = true := by decide +kernel

def w38 : List ℕ := [9, 5, 31, 3, 9, 5, 3, 6, 7, 1, 5, 7, 21, 2, 11, 6, 15, 7, 7, 5, 5, 6, 5, 1, 21]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 952 w38 = true := by decide +kernel

def w39 : List ℕ := [5, 5, 12, 9, 8, 3, 6, 29, 6, 11, 19, 9, 5, 13, 3, 9, 1, 1, 6, 29, 6, 11, 2, 3]
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

theorem good_sound (n x : ℕ) (h8 : n ≠ 8) (h : good n x = true) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ (x ^ 4 + n * y).Prime := by
  simp only [good, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq] at h
  rcases h with h | ⟨h1, h2, h3⟩
  · exact absurd h h8
  · exact ⟨x, n - x, by omega, by omega, by omega, isPrimeB_sound _ h3⟩

end OMA.AOeisA232194_C5Tab

open OMA.AOeisA232194_C5Tab in
theorem OMA.solution : OMA.R_OeisA232194_conjecture_5_R1.H1 := by
  intro n hn hB h8
  obtain ⟨x, hx⟩ := cover n (by omega) (by omega)
  exact good_sound n x h8 hx
