import OMAReductions.R_OeisA219023_conjecture_2_R1
import Mathlib

-- Step OeisA219023.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA219023.conjecture_2.R1
-- Credit: @prathameshnium. Finite check for 3513 ≤ n ≤ 3568.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 12731659.

/-! Step OeisA219023.conjecture_2.R1.H1. -/

namespace OMA.AOeisA219023_conjecture_2Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `3570` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 3570 2

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
  have hnd := noDiv_sound p 3570 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [p] => (isPrimeB (p) && (decide (n < p) && (decide (p < 2 * n) && (isPrimeB (n ^ 2 - n + p) && isPrimeB (n ^ 2 + n - p)))))
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
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p < 2 * n ∧
      Nat.Prime (n ^ 2 - n + p) ∧ Nat.Prime (n ^ 2 + n - p) := by
  unfold core at h
  split at h
  next p =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4⟩ := h
    exact ⟨p, isPrimeB_sound _ a0, a1, a2, isPrimeB_sound _ a3, isPrimeB_sound _ a4⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 3513, …, 3568`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[3581], [3559], [3797], [3613], [4909], [3923], [3989], [3907], [3719], [4127], [4861], [3581], [4007], [4231], [4019], [4243], [3847], [3671], [3733], [4957], [3671], [3607], [3643], [3701], [3697]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 3513 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[3583], [3557], [4007], [3613], [3917], [3581], [3697], [3593], [3613], [4519], [3821], [3677], [3613], [3881], [3677], [3613], [3911], [3557], [4129], [4337], [4651], [4021], [3623], [3919], [5737]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 3538 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[4943], [3877], [3853], [3863], [4327], [4603]]
theorem len2 : w2.length = 6 := rfl
theorem ok2 : checkList 3563 w2 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `3513 ≤ n ≤ 3568` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 3513 ≤ n) (h2 : n ≤ 3568) : ∃ x, good n x = true := by
  by_cases c0 : n < 3538
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 3563
  · exact chunk ok1 len1 (by omega) (by omega)
  exact chunk ok2 len2 (by omega) (by omega)

end OMA.AOeisA219023_conjecture_2Tab

open OMA.AOeisA219023_conjecture_2Tab in
theorem OMA.solution : OMA.R_OeisA219023_conjecture_2_R1.H1 := by
  intro n hn hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
