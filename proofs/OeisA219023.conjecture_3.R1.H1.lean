import OMAReductions.R_OeisA219023_conjecture_3_R1
import Mathlib

-- Step OeisA219023.conjecture_3.R1.H1: hypothesis H1 of reduction OeisA219023.conjecture_3.R1
-- Credit: @prathameshnium. Finite check for 1829 ≤ n ≤ 1934.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 3742891.

/-! Step OeisA219023.conjecture_3.R1.H1. -/

namespace OMA.AOeisA219023_conjecture_3Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `1936` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 1936 2

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
  have hnd := noDiv_sound p 1936 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [p] => (isPrimeB (p) && (decide (p < n) && (isPrimeB (n ^ 2 - n - p) && isPrimeB (n ^ 2 + n + p))))
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
    ∃ p : ℕ, p.Prime ∧ p < n ∧
      Nat.Prime (n ^ 2 - n - p) ∧ Nat.Prime (n ^ 2 + n + p) := by
  unfold core at h
  split at h
  next p =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3⟩ := h
    exact ⟨p, isPrimeB_sound _ a0, a1, isPrimeB_sound _ a2, isPrimeB_sound _ a3⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 1829, …, 1934`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[271], [109], [101], [43], [17], [101], [13], [31], [131], [577], [373], [251], [271], [41], [179], [61], [11], [29], [283], [127], [179], [73], [89], [263], [7]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 1829 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[59], [23], [757], [41], [5], [79], [191], [677], [271], [239], [461], [61], [17], [1283], [67], [43], [29], [109], [73], [1049], [1381], [73], [29], [13], [227]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 1854 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[11], [283], [401], [71], [307], [359], [131], [109], [191], [29], [139], [71], [191], [271], [5], [11], [157], [59], [101], [577], [61], [47], [7], [613], [47]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 1879 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[61], [23], [47], [523], [79], [29], [157], [79], [23], [19], [61], [347], [67], [13], [17], [79], [73], [101], [241], [967], [131], [61], [17], [941], [277]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 1904 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[53], [59], [67], [13], [587], [601]]
theorem len4 : w4.length = 6 := rfl
theorem ok4 : checkList 1929 w4 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `1829 ≤ n ≤ 1934` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 1829 ≤ n) (h2 : n ≤ 1934) : ∃ x, good n x = true := by
  by_cases c0 : n < 1854
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 1879
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 1904
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 1929
  · exact chunk ok3 len3 (by omega) (by omega)
  exact chunk ok4 len4 (by omega) (by omega)

end OMA.AOeisA219023_conjecture_3Tab

open OMA.AOeisA219023_conjecture_3Tab in
theorem OMA.solution : OMA.R_OeisA219023_conjecture_3_R1.H1 := by
  intro n hn hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
