import OMAReductions.R_Lemoine_lemoine_conjecture_R1
import Mathlib

/-! Every odd `n` with `6 < n ≤ 10001` is `p + 2 q` with `p, q` prime, by a kernel-checked
search. -/

namespace OMA.Step_Lemoine_lemoine_conjecture_R1_H1

/-- Trial division of `n` by `d, d + 1, ...`, for at most `fuel` divisors, succeeding once
`d * d > n`. Running out of fuel counts as failure. -/
def noDiv (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, d => if n < d * d then true else (n % d != 0) && noDiv n fuel (d + 1)

theorem noDiv_spec (n : ℕ) : ∀ fuel d : ℕ, noDiv n fuel d = true →
    ∀ m : ℕ, d ≤ m → m * m ≤ n → ¬ m ∣ n := by
  intro fuel
  induction fuel with
  | zero => intro d h; simp [noDiv] at h
  | succ fuel ih =>
    intro d h m hdm hmn hdiv
    unfold noDiv at h
    by_cases hlt : n < d * d
    · have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · rw [if_neg hlt] at h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rcases Nat.eq_or_lt_of_le hdm with rfl | hlt'
      · exact h.1 (Nat.mod_eq_zero_of_dvd hdiv)
      · exact ih (d + 1) h.2 m hlt' hmn hdiv

/-- The product of the primes up to `1000`. -/
def P1000 : ℕ := 19590340644999083431262508198206381046123972390589368223882605328968666316379870661851951648789482321596229559115436019149189529725215266728292282990852649023362731392404017939142010958261393634959471483757196721672243410067118516227661133135192488848989914892157188308679896875137439519338903968094905549750386407106033836586660683539201011635917900039904495065203299749542985993134669814805318474080581207891125910

theorem small_hit : ∀ m : ℕ, m ≤ 1000 → 2 ≤ m → Nat.gcd m P1000 ≠ 1 := by decide +kernel

/-- A Boolean primality test for `n < 1001 ^ 2`: trial division up to `1000`, and above it
coprimality with the primes up to `1000`. -/
def isPrimeB (n : ℕ) : Bool :=
  if n ≤ 1000 then decide (2 ≤ n) && noDiv n n 2
  else decide (n < 1002001) && Nat.gcd n P1000 == 1

theorem isPrimeB_spec {n : ℕ} (h : isPrimeB n = true) : Nat.Prime n := by
  unfold isPrimeB at h
  split_ifs at h with hn
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h2, hd⟩ := h
    by_contra hnp
    have hsq := Nat.minFac_sq_le_self (by omega) hnp
    have hne : n ≠ 1 := by omega
    have hmin := (Nat.minFac_prime hne).two_le
    exact noDiv_spec n n 2 hd (Nat.minFac n) hmin (by nlinarith) (Nat.minFac_dvd n)
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨h2, hg⟩ := h
    by_contra hnp
    have hsq := Nat.minFac_sq_le_self (by omega) hnp
    have hne : n ≠ 1 := by omega
    have hmin := (Nat.minFac_prime hne).two_le
    have hle : Nat.minFac n ≤ 1000 := by nlinarith
    apply small_hit (Nat.minFac n) hle hmin
    exact Nat.eq_one_of_dvd_one (hg ▸ Nat.gcd_dvd_gcd_of_dvd_left P1000 (Nat.minFac_dvd n))

/-- Scan `d, d + 1, ...` (at most `fuel` values) for a prime below `hi`. -/
def findPr (hi : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, d => (decide (d < hi) && isPrimeB d) || findPr hi fuel (d + 1)

theorem findPr_spec (hi : ℕ) : ∀ fuel d : ℕ, findPr hi fuel d = true →
    ∃ p : ℕ, d ≤ p ∧ p < hi ∧ Nat.Prime p := by
  intro fuel
  induction fuel with
  | zero => intro d h; simp [findPr] at h
  | succ fuel ih =>
    intro d h
    simp only [findPr, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact ⟨d, le_rfl, h1, isPrimeB_spec h2⟩
    · obtain ⟨p, hp1, hp2, hp3⟩ := ih (d + 1) h
      exact ⟨p, by omega, hp2, hp3⟩

/-- `test x` holds for every `x` in `[s, s + c)`. -/
def checkFrom (test : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => true
  | c + 1, s => test s && checkFrom test c (s + 1)

theorem checkFrom_spec (test : ℕ → Bool) : ∀ c s : ℕ, checkFrom test c s = true →
    ∀ n : ℕ, s ≤ n → n < s + c → test n = true := by
  intro c
  induction c with
  | zero => intro s _ n h1 h2; omega
  | succ c ih =>
    intro s h n h1 h2
    simp only [checkFrom, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact ih (s + 1) h.2 n hlt (by omega)

/-- Search `q = d, d + 1, ...` (at most `fuel` values) with `q` and `n - 2 q` prime. -/
def findQ (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, d => (isPrimeB d && isPrimeB (n - 2 * d)) || findQ n fuel (d + 1)

theorem findQ_spec (n : ℕ) : ∀ fuel d : ℕ, findQ n fuel d = true →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + 2 * q = n := by
  intro fuel
  induction fuel with
  | zero => intro d h; simp [findQ] at h
  | succ fuel ih =>
    intro d h
    simp only [findQ, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | h
    · have hp := isPrimeB_spec h2
      have := hp.two_le
      exact ⟨n - 2 * d, d, hp, isPrimeB_spec h1, by omega⟩
    · exact ih (d + 1) h

/-- Odd `n` is `p + 2 q`, or `n` is even. -/
def lemB (n : ℕ) : Bool := n % 2 == 0 || findQ n n 2

theorem check_lem : checkFrom lemB 9995 7 = true := by decide +kernel

theorem lem (n : ℕ) (h6 : 6 < n) (ho : Odd n) (h : n ≤ 10001) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + 2 * q = n := by
  have hb := checkFrom_spec lemB 9995 7 check_lem n h6 (by omega)
  simp only [lemB, Bool.or_eq_true, beq_iff_eq] at hb
  rcases hb with hb | hb
  · exact absurd hb (Nat.odd_iff.mp ho ▸ by decide)
  · exact findQ_spec n n 2 hb

end OMA.Step_Lemoine_lemoine_conjecture_R1_H1

theorem OMA.solution : OMA.R_Lemoine_lemoine_conjecture_R1.H1 :=
  fun n h6 ho h => OMA.Step_Lemoine_lemoine_conjecture_R1_H1.lem n h6 ho h
