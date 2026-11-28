import OMAReductions.R_DubnerConjecture_dubner_conjecture_R1
import Mathlib

/-! Every even `n` with `4208 < n ≤ 10000` is `p + (n - p)` with both twin primes. The witnesses
`p` are stored in chunks of 100 (chunk `j` covers `n = b + 2 i`, `b = 4210 + 200 j`); primality is
checked by trial division up to the square root (`ptest`, proved sound from
`Nat.prime_def_le_sqrt`) and each chunk by one kernel computation. -/

namespace OMA.Step_DubnerConjecture_R1_H1

/-- Trial division by `2, …, ⌊√n⌋`. -/
def ptest (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range' 2 (Nat.sqrt n - 1)).all (fun d => n % d != 0)

theorem ptest_sound {n : ℕ} (h : ptest n = true) : n.Prime := by
  unfold ptest at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'_1,
    bne_iff_ne, ne_eq] at h
  obtain ⟨h2, hall⟩ := h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm2 hmle hdvd => ?_⟩
  exact hall m ⟨hm2, by omega⟩ (Nat.mod_eq_zero_of_dvd hdvd)

/-- `p` is prime and `p - 2` or `p + 2` is prime. -/
def ttest (p : ℕ) : Bool := ptest p && (ptest (p - 2) || ptest (p + 2))

theorem ttest_sound {p : ℕ} (h : ttest p = true) : DubnerConjecture.IsTwinPrime p := by
  unfold ttest at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  exact ⟨ptest_sound h.1, h.2.elim (fun h => Or.inl (ptest_sound h)) (fun h => Or.inr (ptest_sound h))⟩

/-- Turn a checked chunk into the statement for its range. -/
theorem cover (b L : ℕ) (W : List ℕ)
    (hW : ∀ i < L, (decide (W.getD i 0 ≤ b + 2 * i) && ttest (W.getD i 0) &&
      ttest (b + 2 * i - W.getD i 0)) = true)
    (n : ℕ) (h1 : b ≤ n) (h2 : n < b + 2 * L) (hb : Even b) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n := by
  obtain ⟨r, hr⟩ := hev
  obtain ⟨s, hs⟩ := hb
  have hi : (n - b) / 2 < L := by omega
  have hn : n = b + 2 * ((n - b) / 2) := by omega
  have h := hW _ hi
  rw [← hn] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hle, hp⟩, hq⟩ := h
  exact ⟨_, _, ttest_sound hp, ttest_sound hq, by omega⟩

def W0 : List ℕ := [191, 191, 193, 59, 59, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 11, 11, 13, 17, 17, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 137, 137, 139, 29, 29, 31, 149, 149, 151, 41, 41, 43, 59, 59, 61, 107, 107, 109, 59, 59, 61, 107, 107, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 101, 101, 103, 29, 29, 31, 101, 101, 103, 41, 41, 43, 227, 227, 229, 149, 149, 151, 59, 59, 61, 311, 311, 313, 71]

theorem c0 (n : ℕ) (h1 : 4210 ≤ n) (h2 : n < 4410) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 4210 100 W0 (by decide +kernel) n h1 h2 (by decide) hev

def W1 : List ℕ := [71, 73, 197, 197, 199, 149, 149, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 107, 107, 109, 29, 29, 31, 197, 197, 199, 41, 41, 43, 197, 197, 199, 137, 137, 139, 59, 59, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 347, 347, 349, 29, 29, 31, 179, 179, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 59, 59, 61, 29, 29, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 149, 149, 151, 29, 29, 31, 101, 101, 103, 41, 41, 43, 827, 827, 829, 179, 179, 181, 59, 59]

theorem c1 (n : ℕ) (h1 : 4410 ≤ n) (h2 : n < 4610) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 4410 100 W1 (by decide +kernel) n h1 h2 (by decide) hev

def W2 : List ℕ := [61, 191, 191, 193, 71, 71, 73, 107, 107, 109, 149, 149, 151, 419, 419, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 191, 191, 193, 29, 29, 31, 137, 137, 139, 41, 41, 43, 59, 59, 61, 281, 281, 283, 59, 59, 61, 197, 197, 199, 71, 71, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 107, 107, 109, 29, 29, 31, 107, 107, 109, 41, 41, 43, 347, 347, 349, 137, 137, 139, 59, 59, 61, 137, 137, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7]

theorem c2 (n : ℕ) (h1 : 4610 ≤ n) (h2 : n < 4810) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 4610 100 W2 (by decide +kernel) n h1 h2 (by decide) hev

def W3 : List ℕ := [11, 11, 13, 17, 17, 19, 101, 101, 103, 29, 29, 31, 197, 197, 199, 41, 41, 43, 59, 59, 61, 431, 431, 433, 59, 59, 61, 227, 227, 229, 71, 71, 73, 227, 227, 229, 461, 461, 463, 101, 101, 103, 107, 107, 109, 101, 101, 103, 107, 107, 109, 191, 191, 193, 197, 197, 199, 137, 137, 139, 281, 281, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 617, 617, 619, 29, 29, 31, 179, 179, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 59, 59, 61, 29, 29, 31, 71, 71, 73, 41]

theorem c3 (n : ℕ) (h1 : 4810 ≤ n) (h2 : n < 5010) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 4810 100 W3 (by decide +kernel) n h1 h2 (by decide) hev

def W4 : List ℕ := [41, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 827, 827, 829, 29, 29, 31, 269, 269, 271, 41, 41, 43, 59, 59, 61, 107, 107, 109, 59, 59, 61, 569, 569, 571, 71, 71, 73, 311, 311, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 101, 101, 103, 29, 29, 31, 347, 347, 349, 41, 41, 43, 137, 137, 139, 431, 431, 433, 59, 59, 61, 197, 197, 199, 71, 71, 73, 659, 659, 661, 461, 461, 463, 179, 179, 181, 227, 227, 229, 101, 101, 103, 107, 107]

theorem c4 (n : ℕ) (h1 : 5010 ≤ n) (h2 : n < 5210) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 5010 100 W4 (by decide +kernel) n h1 h2 (by decide) hev

def W5 : List ℕ := [109, 191, 191, 193, 197, 197, 199, 1667, 1667, 1669, 431, 431, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 617, 617, 619, 29, 29, 31, 617, 617, 619, 41, 41, 43, 179, 179, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 71, 71, 73, 29, 29, 31, 347, 347, 349, 41, 41, 43, 227, 227, 229, 101, 101, 103, 59, 59, 61, 827, 827, 829, 71, 71, 73, 347, 347, 349, 431, 431, 433, 137, 137, 139, 827, 827, 829, 101, 101, 103, 107, 107, 109, 461, 461, 463, 431, 431, 433, 617, 617, 619]

theorem c5 (n : ℕ) (h1 : 5210 ≤ n) (h2 : n < 5410) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 5210 100 W5 (by decide +kernel) n h1 h2 (by decide) hev

def W6 : List ℕ := [179, 179, 181, 137, 137, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 419, 419, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 827, 827, 829, 29, 29, 31, 59, 59, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 59, 59, 3, 3, 5, 7, 11, 11, 13, 17, 17, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 41, 41, 43, 29, 29, 31, 137, 137, 139, 41, 41, 43, 149, 149, 151, 71, 71, 73, 59, 59, 61, 107, 107, 109, 71, 71, 73, 179, 179, 181, 101, 101, 103, 107]

theorem c6 (n : ℕ) (h1 : 5410 ≤ n) (h2 : n < 5610) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 5410 100 W6 (by decide +kernel) n h1 h2 (by decide) hev

def W7 : List ℕ := [107, 109, 137, 137, 139, 101, 101, 103, 107, 107, 109, 191, 191, 193, 137, 137, 3, 3, 5, 7, 11, 11, 3, 3, 5, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 29, 29, 31, 29, 29, 31, 41, 41, 43, 41, 41, 43, 227, 227, 229, 59, 59, 61, 59, 59, 61, 71, 71, 73, 71, 71, 73, 1607, 1607, 1609, 101, 101, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 107, 107, 109, 29, 29, 31, 137, 137, 139, 41, 41, 43, 137, 137, 139, 137, 137, 139, 59, 59, 61, 149, 149]

theorem c7 (n : ℕ) (h1 : 5610 ≤ n) (h2 : n < 5810) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 5610 100 W7 (by decide +kernel) n h1 h2 (by decide) hev

def W8 : List ℕ := [151, 71, 71, 73, 179, 179, 181, 347, 347, 349, 179, 179, 181, 179, 179, 181, 101, 101, 103, 107, 107, 3, 3, 5, 7, 11, 11, 13, 17, 17, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 461, 461, 463, 29, 29, 31, 1277, 1277, 1279, 41, 41, 43, 59, 59, 61, 191, 191, 193, 59, 59, 61, 1427, 1427, 1429, 71, 71, 73, 107, 107, 109, 311, 311, 313, 101, 101, 103, 107, 107, 109, 101, 101, 103, 107, 107, 109, 1061, 1061, 1063, 149, 149, 151, 137, 137, 139]

theorem c8 (n : ℕ) (h1 : 5810 ≤ n) (h2 : n < 6010) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 5810 100 W8 (by decide +kernel) n h1 h2 (by decide) hev

def W9 : List ℕ := [269, 269, 271, 137, 137, 139, 281, 281, 283, 149, 149, 151, 617, 617, 619, 191, 191, 193, 179, 179, 181, 311, 311, 313, 179, 179, 181, 197, 197, 199, 191, 191, 193, 197, 197, 199, 431, 431, 433, 239, 239, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 461, 461, 463, 29, 29, 31, 1487, 1487, 1489, 41, 41, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 1607, 1607, 1609, 29, 29, 31, 1619, 1619, 1621, 41, 41, 43, 311, 311, 313, 1667, 1667, 1669, 59, 59, 61, 107, 107, 3, 3, 5, 7, 11]

theorem c9 (n : ℕ) (h1 : 6010 ≤ n) (h2 : n < 6210) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 6010 100 W9 (by decide +kernel) n h1 h2 (by decide) hev

def W10 : List ℕ := [11, 13, 17, 17, 19, 569, 569, 571, 29, 29, 31, 101, 101, 103, 41, 41, 43, 827, 827, 829, 599, 599, 601, 59, 59, 61, 521, 521, 523, 71, 71, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 641, 641, 643, 29, 29, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 191, 191, 193, 29, 29, 31, 137, 137, 139, 41, 41, 43, 149, 149, 151, 1871, 1871, 1873, 59, 59, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 641, 641, 643, 29, 29, 31, 197, 197, 199, 41, 41, 43, 107, 107]

theorem c10 (n : ℕ) (h1 : 6210 ≤ n) (h2 : n < 6410) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 6210 100 W10 (by decide +kernel) n h1 h2 (by decide) hev

def W11 : List ℕ := [109, 281, 281, 283, 59, 59, 61, 227, 227, 229, 71, 71, 73, 137, 137, 139, 311, 311, 313, 149, 149, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 821, 821, 823, 29, 29, 31, 617, 617, 619, 41, 41, 43, 137, 137, 139, 1061, 1061, 1063, 59, 59, 61, 857, 857, 859, 71, 71, 73, 227, 227, 229, 881, 881, 883, 179, 179, 181, 347, 347, 349, 101, 101, 3, 3, 5, 7, 11, 11, 13, 17, 17, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 41, 41, 43, 29, 29, 31, 2087, 2087, 2089]

theorem c11 (n : ℕ) (h1 : 6410 ≤ n) (h2 : n < 6610) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 6410 100 W11 (by decide +kernel) n h1 h2 (by decide) hev

def W12 : List ℕ := [41, 41, 43, 347, 347, 349, 71, 71, 73, 59, 59, 61, 1667, 1667, 1669, 71, 71, 73, 197, 197, 199, 101, 101, 103, 107, 107, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 1031, 1031, 1033, 29, 29, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 857, 857, 859, 29, 29, 31, 857, 857, 859, 41, 41, 43, 59, 59, 61, 1277, 1277, 1279, 59, 59, 3, 3, 5, 7, 11, 11, 13, 17, 17, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 11, 11, 13, 17]

theorem c12 (n : ℕ) (h1 : 6610 ≤ n) (h2 : n < 6810) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 6610 100 W12 (by decide +kernel) n h1 h2 (by decide) hev

def W13 : List ℕ := [17, 19, 617, 617, 619, 29, 29, 31, 137, 137, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 59, 59, 61, 29, 29, 31, 71, 71, 73, 41, 41, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 101, 101, 103, 29, 29, 31, 1427, 1427, 1429, 41, 41, 43, 137, 137, 139, 1481, 1481, 1483, 59, 59, 61, 107, 107, 109, 71, 71, 73, 857, 857, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 191, 191, 193, 29, 29, 31, 2027, 2027, 2029, 41, 41, 43, 59, 59]

theorem c13 (n : ℕ) (h1 : 6810 ≤ n) (h2 : n < 7010) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 6810 100 W13 (by decide +kernel) n h1 h2 (by decide) hev

def W14 : List ℕ := [61, 311, 311, 313, 59, 59, 61, 197, 197, 199, 71, 71, 73, 347, 347, 349, 281, 281, 283, 101, 101, 103, 107, 107, 109, 101, 101, 103, 107, 107, 109, 281, 281, 283, 419, 419, 421, 137, 137, 139, 311, 311, 313, 137, 137, 139, 311, 311, 313, 149, 149, 151, 1697, 1697, 1699, 419, 419, 421, 179, 179, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 191, 191, 193, 29, 29, 31, 461, 461, 463, 41, 41, 43, 227, 227, 229, 311, 311, 313, 59, 59, 61, 431, 431, 433, 71, 71, 73, 1787, 1787, 1789]

theorem c14 (n : ℕ) (h1 : 7010 ≤ n) (h2 : n < 7210) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 7010 100 W14 (by decide +kernel) n h1 h2 (by decide) hev

def W15 : List ℕ := [419, 419, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 107, 107, 109, 29, 29, 31, 419, 419, 421, 41, 41, 43, 311, 311, 313, 137, 137, 139, 59, 59, 61, 149, 149, 151, 71, 71, 73, 419, 419, 421, 347, 347, 349, 431, 431, 433, 179, 179, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 461, 461, 3, 3, 5, 7, 11, 11, 13, 17, 17, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 41, 41, 43, 29, 29, 31, 3167, 3167, 3169, 41, 41, 43, 269, 269, 271, 71, 71, 73, 59]

theorem c15 (n : ℕ) (h1 : 7210 ≤ n) (h2 : n < 7410) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 7210 100 W15 (by decide +kernel) n h1 h2 (by decide) hev

def W16 : List ℕ := [59, 61, 107, 107, 109, 71, 71, 73, 599, 599, 601, 101, 101, 103, 107, 107, 109, 137, 137, 139, 101, 101, 103, 107, 107, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 149, 149, 151, 29, 29, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 179, 179, 181, 29, 29, 31, 191, 191, 193, 41, 41, 43, 227, 227, 229, 191, 191, 193, 59, 59, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 821, 821, 823, 29, 29, 3, 3, 5, 7, 11, 11, 13, 17, 17]

theorem c16 (n : ℕ) (h1 : 7410 ≤ n) (h2 : n < 7610) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 7410 100 W16 (by decide +kernel) n h1 h2 (by decide) hev

def W17 : List ℕ := [19, 281, 281, 283, 29, 29, 31, 137, 137, 139, 41, 41, 43, 149, 149, 151, 311, 311, 313, 59, 59, 61, 107, 107, 109, 71, 71, 73, 107, 107, 109, 461, 461, 463, 191, 191, 193, 137, 137, 139, 101, 101, 103, 107, 107, 109, 1151, 1151, 1153, 149, 149, 151, 227, 227, 229, 1019, 1019, 1021, 137, 137, 139, 521, 521, 523, 149, 149, 151, 197, 197, 199, 191, 191, 193, 197, 197, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 191, 191, 193, 29, 29, 31, 461, 461, 463, 41, 41, 43, 347, 347, 349]

theorem c17 (n : ℕ) (h1 : 7610 ≤ n) (h2 : n < 7810) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 7610 100 W17 (by decide +kernel) n h1 h2 (by decide) hev

def W18 : List ℕ := [461, 461, 463, 59, 59, 61, 1031, 1031, 1033, 71, 71, 73, 347, 347, 349, 281, 281, 283, 1019, 1019, 1021, 521, 521, 523, 101, 101, 103, 107, 107, 109, 281, 281, 283, 419, 419, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 311, 311, 313, 29, 29, 31, 1151, 1151, 1153, 41, 41, 43, 617, 617, 619, 599, 599, 601, 59, 59, 61, 1151, 1151, 1153, 71, 71, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 641, 641, 643, 29, 29, 31, 107, 107, 109, 41, 41, 43, 239, 239, 241, 1301, 1301, 1303, 59]

theorem c18 (n : ℕ) (h1 : 7810 ≤ n) (h2 : n < 8010) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 7810 100 W18 (by decide +kernel) n h1 h2 (by decide) hev

def W19 : List ℕ := [59, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 821, 821, 823, 29, 29, 31, 3257, 3257, 3259, 41, 41, 43, 107, 107, 109, 1301, 1301, 1303, 59, 59, 61, 197, 197, 199, 71, 71, 73, 137, 137, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 101, 101, 103, 29, 29, 31, 2381, 2381, 2383, 41, 41, 43, 827, 827, 829, 191, 191, 193, 59, 59, 61, 821, 821, 823, 71, 71, 73, 617, 617, 619, 821, 821, 823, 227, 227, 229, 1481, 1481, 1483, 101, 101, 103, 107, 107, 109, 191, 191, 193, 197, 197]

theorem c19 (n : ℕ) (h1 : 8010 ≤ n) (h2 : n < 8210) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 8010 100 W19 (by decide +kernel) n h1 h2 (by decide) hev

def W20 : List ℕ := [199, 881, 881, 883, 269, 269, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 1427, 1427, 1429, 29, 29, 31, 179, 179, 181, 41, 41, 43, 59, 59, 61, 197, 197, 199, 59, 59, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 227, 227, 229, 29, 29, 31, 107, 107, 109, 41, 41, 43, 107, 107, 109, 857, 857, 859, 59, 59, 61, 137, 137, 139, 71, 71, 73, 137, 137, 139, 617, 617, 619, 149, 149, 151, 827, 827, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19]

theorem c20 (n : ℕ) (h1 : 8210 ≤ n) (h2 : n < 8410) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 8210 100 W20 (by decide +kernel) n h1 h2 (by decide) hev

def W21 : List ℕ := [179, 179, 181, 29, 29, 31, 191, 191, 193, 41, 41, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 2711, 2711, 2713, 29, 29, 31, 2267, 2267, 2269, 41, 41, 43, 599, 599, 601, 191, 191, 193, 59, 59, 61, 107, 107, 109, 71, 71, 73, 419, 419, 421, 281, 281, 283, 227, 227, 229, 137, 137, 139, 101, 101, 103, 107, 107, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 269, 269, 271, 29, 29, 31, 281, 281, 283, 41, 41, 43, 197, 197, 199, 641, 641, 643, 59, 59, 3, 3, 5, 7, 11]

theorem c21 (n : ℕ) (h1 : 8410 ≤ n) (h2 : n < 8610) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 8410 100 W21 (by decide +kernel) n h1 h2 (by decide) hev

def W22 : List ℕ := [11, 13, 17, 17, 19, 191, 191, 193, 29, 29, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 419, 419, 421, 29, 29, 31, 431, 431, 433, 41, 41, 43, 137, 137, 139, 461, 461, 463, 59, 59, 61, 461, 461, 463, 71, 71, 73, 107, 107, 109, 281, 281, 283, 179, 179, 181, 431, 431, 433, 101, 101, 103, 107, 107, 109, 311, 311, 313, 149, 149, 151, 461, 461, 463, 809, 809, 811, 137, 137, 139, 821, 821, 823, 149, 149, 151, 1451, 1451, 1453, 191, 191, 193, 197, 197, 199, 569, 569, 571, 179, 179]

theorem c22 (n : ℕ) (h1 : 8610 ≤ n) (h2 : n < 8810) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 8610 100 W22 (by decide +kernel) n h1 h2 (by decide) hev

def W23 : List ℕ := [181, 521, 521, 523, 191, 191, 3, 3, 5, 7, 11, 11, 13, 17, 17, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 41, 41, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 347, 347, 349, 29, 29, 31, 59, 59, 61, 41, 41, 43, 71, 71, 73, 827, 827, 829, 59, 59, 61, 107, 107, 109, 71, 71, 73, 101, 101, 103, 107, 107, 109, 521, 521, 523, 137, 137, 139, 101, 101, 103, 107, 107, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 3251, 3251, 3253, 29, 29, 3, 3, 5, 7]

theorem c23 (n : ℕ) (h1 : 8810 ≤ n) (h2 : n < 9010) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 8810 100 W23 (by decide +kernel) n h1 h2 (by decide) hev

def W24 : List ℕ := [11, 11, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 197, 197, 199, 29, 29, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 227, 227, 229, 29, 29, 31, 107, 107, 109, 41, 41, 43, 227, 227, 229, 1607, 1607, 1609, 59, 59, 61, 107, 107, 109, 71, 71, 73, 107, 107, 109, 1667, 1667, 1669, 269, 269, 271, 137, 137, 139, 101, 101, 103, 107, 107, 109, 617, 617, 619, 149, 149, 151, 197, 197, 199, 311, 311, 313, 137, 137, 139, 347, 347, 349, 149, 149, 151, 197, 197, 199, 191, 191, 193, 197]

theorem c24 (n : ℕ) (h1 : 9010 ≤ n) (h2 : n < 9210) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 9010 100 W24 (by decide +kernel) n h1 h2 (by decide) hev

def W25 : List ℕ := [197, 199, 617, 617, 619, 179, 179, 181, 227, 227, 229, 191, 191, 193, 197, 197, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 1031, 1031, 1033, 29, 29, 31, 1787, 1787, 1789, 41, 41, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 1427, 1427, 1429, 29, 29, 31, 347, 347, 349, 41, 41, 43, 1319, 1319, 1321, 1787, 1787, 1789, 59, 59, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 827, 827, 829, 29, 29, 31, 137, 137, 139, 41, 41, 43, 107, 107, 109, 857, 857, 859, 59, 59, 61, 569, 569]

theorem c25 (n : ℕ) (h1 : 9210 ≤ n) (h2 : n < 9410) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 9210 100 W25 (by decide +kernel) n h1 h2 (by decide) hev

def W26 : List ℕ := [571, 71, 71, 73, 137, 137, 3, 3, 5, 7, 11, 11, 3, 3, 5, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 29, 29, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 857, 857, 859, 29, 29, 31, 59, 59, 61, 41, 41, 43, 71, 71, 73, 1427, 1427, 1429, 59, 59, 61, 107, 107, 109, 71, 71, 73, 101, 101, 103, 107, 107, 109, 269, 269, 271, 137, 137, 139, 101, 101, 103, 107, 107, 109, 137, 137, 139, 149, 149, 151, 149, 149, 151, 311, 311, 313, 137, 137, 139, 2657, 2657, 2659]

theorem c26 (n : ℕ) (h1 : 9410 ≤ n) (h2 : n < 9610) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 9410 100 W26 (by decide +kernel) n h1 h2 (by decide) hev

def W27 : List ℕ := [149, 149, 151, 179, 179, 181, 191, 191, 193, 191, 191, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 191, 191, 193, 29, 29, 31, 227, 227, 229, 41, 41, 43, 239, 239, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 71, 71, 73, 29, 29, 31, 281, 281, 283, 41, 41, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 281, 281, 283, 29, 29, 31, 1667, 1667, 1669, 41, 41, 43, 137, 137, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 71, 71, 73, 29, 29, 31, 461, 461, 463, 41]

theorem c27 (n : ℕ) (h1 : 9610 ≤ n) (h2 : n < 9810) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 9610 100 W27 (by decide +kernel) n h1 h2 (by decide) hev

def W28 : List ℕ := [41, 43, 137, 137, 139, 101, 101, 103, 59, 59, 61, 821, 821, 823, 71, 71, 73, 2087, 2087, 2089, 419, 419, 421, 137, 137, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 419, 419, 421, 29, 29, 31, 431, 431, 433, 41, 41, 43, 137, 137, 139, 191, 191, 193, 59, 59, 61, 461, 461, 463, 71, 71, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 521, 521, 523, 29, 29, 31, 107, 107, 109, 41, 41, 43, 347, 347, 349, 521, 521, 523, 59, 59, 61, 137, 137, 139, 71]

theorem c28 (n : ℕ) (h1 : 9810 ≤ n) (h2 : n < 10002) (hev : Even n) :
    ∃ p q : ℕ, DubnerConjecture.IsTwinPrime p ∧ DubnerConjecture.IsTwinPrime q ∧ p + q = n :=
  cover 9810 96 W28 (by decide +kernel) n h1 h2 (by decide) hev

end OMA.Step_DubnerConjecture_R1_H1

open OMA.Step_DubnerConjecture_R1_H1 in
theorem OMA.solution : OMA.R_DubnerConjecture_dubner_conjecture_R1.H1 := by
  intro n hn1 hn2 hev
  have hev' := hev
  obtain ⟨r, hr⟩ := hev'
  by_cases h0 : n < 4410
  · exact c0 n (by omega) h0 hev
  by_cases h1 : n < 4610
  · exact c1 n (by omega) h1 hev
  by_cases h2 : n < 4810
  · exact c2 n (by omega) h2 hev
  by_cases h3 : n < 5010
  · exact c3 n (by omega) h3 hev
  by_cases h4 : n < 5210
  · exact c4 n (by omega) h4 hev
  by_cases h5 : n < 5410
  · exact c5 n (by omega) h5 hev
  by_cases h6 : n < 5610
  · exact c6 n (by omega) h6 hev
  by_cases h7 : n < 5810
  · exact c7 n (by omega) h7 hev
  by_cases h8 : n < 6010
  · exact c8 n (by omega) h8 hev
  by_cases h9 : n < 6210
  · exact c9 n (by omega) h9 hev
  by_cases h10 : n < 6410
  · exact c10 n (by omega) h10 hev
  by_cases h11 : n < 6610
  · exact c11 n (by omega) h11 hev
  by_cases h12 : n < 6810
  · exact c12 n (by omega) h12 hev
  by_cases h13 : n < 7010
  · exact c13 n (by omega) h13 hev
  by_cases h14 : n < 7210
  · exact c14 n (by omega) h14 hev
  by_cases h15 : n < 7410
  · exact c15 n (by omega) h15 hev
  by_cases h16 : n < 7610
  · exact c16 n (by omega) h16 hev
  by_cases h17 : n < 7810
  · exact c17 n (by omega) h17 hev
  by_cases h18 : n < 8010
  · exact c18 n (by omega) h18 hev
  by_cases h19 : n < 8210
  · exact c19 n (by omega) h19 hev
  by_cases h20 : n < 8410
  · exact c20 n (by omega) h20 hev
  by_cases h21 : n < 8610
  · exact c21 n (by omega) h21 hev
  by_cases h22 : n < 8810
  · exact c22 n (by omega) h22 hev
  by_cases h23 : n < 9010
  · exact c23 n (by omega) h23 hev
  by_cases h24 : n < 9210
  · exact c24 n (by omega) h24 hev
  by_cases h25 : n < 9410
  · exact c25 n (by omega) h25 hev
  by_cases h26 : n < 9610
  · exact c26 n (by omega) h26 hev
  by_cases h27 : n < 9810
  · exact c27 n (by omega) h27 hev
  exact c28 n (by omega) (by omega) hev
