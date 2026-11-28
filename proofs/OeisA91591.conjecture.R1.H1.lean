import OMAReductions.R_OeisA91591_conjecture_R1
import Mathlib

-- Step OeisA91591.conjecture.R1.H1: hypothesis H1 of reduction OeisA91591.conjecture.R1
-- Finite check: for every 122 < n ≤ 400, a listed witness p gives a twin pair
-- p, p + 2 with n ^ 2 < p and p + 2 < (n + 1) ^ 2. Both primes are certified by trial division, run by
-- decide +kernel.

namespace OMA.A91591H1

/-- `noDivFrom p d fuel = true` means no `e ≥ d` with `e * e ≤ p` divides `p`
(`false` when the fuel runs out). -/
def noDivFrom (p : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | d, fuel + 1 => if p < d * d then true else (p % d != 0) && noDivFrom p (d + 1) fuel

lemma noDivFrom_spec (p : ℕ) : ∀ fuel d, noDivFrom p d fuel = true →
    ∀ e, d ≤ e → e * e ≤ p → ¬ e ∣ p := by
  intro fuel
  induction fuel with
  | zero => intro d h; simp [noDivFrom] at h
  | succ f ih =>
    intro d h e hde hep hdvd
    simp only [noDivFrom] at h
    split_ifs at h with hlt
    · have : d * d ≤ e * e := Nat.mul_le_mul hde hde
      omega
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      obtain ⟨hmod, hrest⟩ := h
      rcases Nat.eq_or_lt_of_le hde with rfl | hlt'
      · exact hmod (Nat.mod_eq_zero_of_dvd hdvd)
      · exact ih (d + 1) hrest e hlt' hep hdvd

def isPrimeB (p : ℕ) : Bool := decide (2 ≤ p) && noDivFrom p 2 p

lemma isPrimeB_spec (p : ℕ) (h : isPrimeB p = true) : p.Prime := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hnd⟩ := h
  by_contra hnp
  have hm := Nat.minFac_sq_le_self (by omega) hnp
  have hmp := Nat.minFac_prime (show p ≠ 1 by omega)
  rw [sq] at hm
  exact noDivFrom_spec p p 2 hnd (Nat.minFac p) hmp.two_le hm (Nat.minFac_dvd p)

/-- `findP n p fuel = true` means some `q ≥ p`, `q < p + fuel`, is a twin pair start strictly
between `n ^ 2` and `(n + 1) ^ 2` passing the trial division. -/
def findP (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | p, fuel + 1 =>
    (decide (n ^ 2 < p) && decide (p + 2 < (n + 1) ^ 2) && isPrimeB p && isPrimeB (p + 2)) ||
      findP n (p + 1) fuel

lemma findP_spec (n : ℕ) : ∀ fuel p, findP n p fuel = true →
    ∃ q, n ^ 2 < q ∧ q + 2 < (n + 1) ^ 2 ∧ q.Prime ∧ (q + 2).Prime := by
  intro fuel
  induction fuel with
  | zero => intro p h; simp [findP] at h
  | succ f ih =>
    intro p h
    simp only [findP, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | h
    · exact ⟨p, h1, h2, isPrimeB_spec _ h3, isPrimeB_spec _ h4⟩
    · exact ih (p + 1) h

/-- For `123 ≤ n ≤ 400`, entry `n - 123` is the least twin prime start above `n ^ 2`. -/
def wl : List ℕ := [
  15137, 15581, 15641, 15887, 16139, 16451, 16649, 16901, 17189, 17489,
  17747, 17957, 18251, 18521, 18911, 19079, 19379, 19697, 19889, 20231,
  20477, 20747, 21059, 21317, 21611, 22037, 22271, 22541, 22859, 23201,
  23537, 23741, 24107, 24371, 24917, 24977, 25301, 25601, 25931, 26249,
  26681, 26951, 27239, 27581, 27917, 28277, 28571, 29021, 29387, 29669,
  30011, 30389, 30839, 31079, 31391, 31721, 32057, 32411, 32801, 33149,
  33587, 34031, 34259, 34649, 35051, 35447, 35729, 36107, 36527, 36899,
  37307, 37691, 38237, 38447, 38921, 39227, 39827, 40037, 40427, 40847,
  41231, 41759, 42071, 42461, 42899, 43319, 43781, 44129, 44531, 45119,
  45587, 45821, 46271, 46679, 47147, 47657, 48119, 48407, 48857, 49331,
  49739, 50261, 50891, 51131, 51719, 52067, 52541, 52901, 53549, 53897,
  54401, 54917, 55331, 55817, 56207, 56711, 57191, 57791, 58109, 58601,
  59051, 59627, 60089, 60647, 61151, 61559, 62129, 62927, 63029, 63587,
  64151, 64577, 65027, 65537, 66107, 66569, 67139, 67757, 68207, 68711,
  69191, 69737, 70379, 70841, 71327, 71879, 72467, 73037, 73607, 74099,
  74609, 75167, 75707, 76259, 76829, 77417, 78137, 78437, 78977, 79559,
  80147, 80669, 81281, 81899, 82469, 83219, 83561, 84179, 84809, 85331,
  85931, 86531, 87119, 87629, 88259, 88811, 89519, 90017, 90617, 91367,
  91811, 92459, 93131, 93701, 94307, 94949, 95789, 96179, 96737, 97367,
  98009, 98639, 99257, 99989, 100517, 101159, 101837, 102407, 103067, 103811,
  104381, 105227, 105767, 106277, 106961, 107717, 108287, 108947, 109619, 110321,
  110921, 111731, 112247, 112919, 113621, 114599, 115019, 115601, 116531, 117041,
  117671, 118409, 119087, 119771, 120689, 121169, 121949, 122501, 123377, 124121,
  124769, 125507, 126227, 126857, 127607, 128201, 128939, 129629, 130367, 131111,
  131777, 132527, 133277, 133979, 134837, 135431, 136397, 136949, 137867, 138401,
  139199, 139967, 140627, 141497, 142157, 142979, 143651, 144407, 145511, 145931,
  146891, 147671, 148301, 149057, 149837, 150587, 151337, 152417, 152897, 153887,
  154571, 155381, 156059, 156899, 157637, 158747, 159347, 160031]

def cond (n : ℕ) : Bool := decide (n ≤ 122) || decide (400 < n) || findP n (wl.getD (n - 123) 0) 1

/-- `chk k lo` checks `cond` on `[lo, lo + 2 ^ k)` (binary splitting). -/
def chk : ℕ → ℕ → Bool
  | 0, lo => cond lo
  | k + 1, lo => chk k lo && chk k (lo + 2 ^ k)

lemma chk_spec : ∀ k lo, chk k lo = true → ∀ n, lo ≤ n → n < lo + 2 ^ k → cond n = true := by
  intro k
  induction k with
  | zero =>
    intro lo h n h1 h2
    simp only [pow_zero] at h2
    obtain rfl : n = lo := by omega
    simpa [chk] using h
  | succ k ih =>
    intro lo h n h1 h2
    simp only [chk, Bool.and_eq_true] at h
    by_cases hn : n < lo + 2 ^ k
    · exact ih lo h.1 n h1 hn
    · exact ih (lo + 2 ^ k) h.2 n (by omega) (by rw [pow_succ] at h2; omega)

theorem chk_ok : chk 9 0 = true := by decide +kernel

theorem h1 : ∀ n : ℕ, 122 < n → n ≤ 400 → OeisA91591.a n > 0 := by
  intro n hn hle
  have hc := chk_spec 9 0 chk_ok n (Nat.zero_le n) (by norm_num; omega)
  have e1 : decide (n ≤ 122) = false := by simp; omega
  have e2 : decide (400 < n) = false := by simp; omega
  simp only [cond, e1, e2, Bool.false_or] at hc
  obtain ⟨q, hq1, hq2, hp, hp2⟩ := findP_spec n _ _ hc
  unfold OeisA91591.a
  refine Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hq1, by omega⟩, hp, hp2, hq2⟩⟩

end OMA.A91591H1

theorem OMA.solution : OMA.R_OeisA91591_conjecture_R1.H1 := OMA.A91591H1.h1
