import OMAStatements.S_oeis_a259226
import Mathlib

namespace OMA.A259226Proof

open OMA.S_oeis_a259226

/-! ### A structurally recursive primality test (odd trial division) -/

/-- Trial division of `n` by `d, d + 2, d + 4, ...` with fuel: `true` once `n < d * d` is reached, `false` at a
divisor. -/
def trial (n : ℕ) : ℕ → ℕ → Bool
  | 0, d => decide (n < d * d)
  | f + 1, d => if n < d * d then true else if n % d = 0 then false else trial n f (d + 2)

/-- Primality by odd trial division (fuel `n`). -/
def isPrimeB (n : ℕ) : Bool :=
  decide (n = 2) || (decide (3 ≤ n) && decide (n % 2 = 1) && trial n n 3)

/-- A number `n ≥ 2` with no divisor `e` in `[2, d)` and `n < d * d` is prime. -/
theorem prime_of_no_small_dvd (n d : ℕ) (hn : 2 ≤ n) (hinv : ∀ e, 2 ≤ e → e < d → ¬ e ∣ n)
    (hlt : n < d * d) : n.Prime := by
  by_contra hnp
  have hm := Nat.minFac_prime (show n ≠ 1 by omega)
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hmd : n.minFac < d := by
    by_contra hge
    have := Nat.mul_self_le_mul_self (Nat.not_lt.mp hge)
    rw [pow_two] at hsq
    omega
  exact hinv n.minFac hm.two_le hmd (Nat.minFac_dvd n)

theorem trial_sound (n : ℕ) (hn : 2 ≤ n) (hodd : n % 2 = 1) :
    ∀ f d, 3 ≤ d → d % 2 = 1 → (∀ e, 2 ≤ e → e < d → ¬ e ∣ n) → trial n f d = true → n.Prime := by
  intro f
  induction f with
  | zero =>
    intro d _ _ hinv h
    exact prime_of_no_small_dvd n d hn hinv (by simpa [trial] using h)
  | succ f ih =>
    intro d hd3 hdo hinv h
    simp only [trial] at h
    by_cases h1 : n < d * d
    · exact prime_of_no_small_dvd n d hn hinv h1
    · rw [if_neg h1] at h
      by_cases h2 : n % d = 0
      · rw [if_pos h2] at h
        exact absurd h (by decide)
      · rw [if_neg h2] at h
        apply ih (d + 2) (by omega) (by omega) _ h
        intro e he2 hed hdvd
        rcases (show e < d ∨ e = d ∨ e = d + 1 by omega) with hlt | heq | heq
        · exact hinv e he2 hlt hdvd
        · subst heq
          exact h2 (Nat.mod_eq_zero_of_dvd hdvd)
        · subst heq
          have h2d : 2 ∣ d + 1 := by omega
          have := Nat.dvd_trans h2d hdvd
          omega

theorem trial_complete (n : ℕ) (hp : n.Prime) : ∀ f d, 3 ≤ d → n < d + f → trial n f d = true := by
  intro f
  induction f with
  | zero =>
    intro d hd3 hlt
    have : d ≤ d * d := Nat.le_mul_self d
    simp [trial]
    omega
  | succ f ih =>
    intro d hd3 hlt
    simp only [trial]
    by_cases h1 : n < d * d
    · rw [if_pos h1]
    · rw [if_neg h1]
      by_cases h2 : n % d = 0
      · exfalso
        have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero h2
        rcases hp.eq_one_or_self_of_dvd d hdvd with h | h
        · omega
        · subst h
          have := hp.two_le
          have : d * d ≥ d * 3 := Nat.mul_le_mul_left d hd3
          omega
      · rw [if_neg h2]
        exact ih (d + 2) (by omega) (by omega)

theorem isPrimeB_iff (n : ℕ) : isPrimeB n = true ↔ n.Prime := by
  unfold isPrimeB
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨⟨h3, hodd⟩, ht⟩)
    · subst h; exact Nat.prime_two
    · apply trial_sound n (by omega) hodd n 3 le_rfl rfl _ ht
      intro e he2 he3 hdvd
      have : e = 2 := by omega
      subst this
      omega
  · intro hp
    rcases hp.eq_two_or_odd with h | h
    · exact Or.inl h
    · right
      have := hp.two_le
      exact ⟨⟨by omega, h⟩, trial_complete n hp n 3 le_rfl (by omega)⟩

/-! ### A fast primality test below `334 ^ 2`: coprime to the primes below `334` -/

/-- All of `P 0, …, P (m - 1)` hold. -/
def checkAll (P : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | m + 1 => P m && checkAll P m

theorem checkAll_true (P : ℕ → Bool) : ∀ m, checkAll P m = true → ∀ p, p < m → P p = true
  | 0, _, p, hp => absurd hp (Nat.not_lt_zero p)
  | m + 1, h, p, hp => by
    have h1 : P m = true ∧ checkAll P m = true := by simpa [checkAll] using h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp' | hp'
    · exact checkAll_true P m h1.2 p hp'
    · rw [hp']; exact h1.1

/-- The primes below `334`. -/
def smallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107,
    109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229,
    233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331]

/-- Their product. -/
def bigM : ℕ := smallPrimes.prod

theorem smallPrimes_check :
    checkAll (fun m => !isPrimeB m || decide (m ∈ smallPrimes)) 334 = true := by
  decide +kernel

theorem smallPrimes_mem (m : ℕ) (hm : m < 334) (hp : m.Prime) : m ∈ smallPrimes := by
  have h : (!isPrimeB m || decide (m ∈ smallPrimes)) = true := checkAll_true _ 334 smallPrimes_check m hm
  rw [(isPrimeB_iff m).mpr hp] at h
  simpa using h

theorem smallPrimes_bound : smallPrimes.all (fun p => decide (0 < p) && decide (p < 334)) = true := by
  decide +kernel

/-- Primality test: trial division below `334`, coprimality with `bigM` from `334` on (exact below `334 ^ 2`). -/
def isPrimeG (n : ℕ) : Bool := if n < 334 then isPrimeB n else decide (Nat.gcd n bigM = 1)

theorem isPrimeG_iff (n : ℕ) (hn : n < 111556) : isPrimeG n = true ↔ n.Prime := by
  unfold isPrimeG
  by_cases h : n < 334
  · rw [if_pos h]
    exact isPrimeB_iff n
  · rw [if_neg h]
    simp only [decide_eq_true_eq]
    constructor
    · intro hg
      by_contra hnp
      have hm := Nat.minFac_prime (show n ≠ 1 by omega)
      have hsq := Nat.minFac_sq_le_self (by omega) hnp
      have hlt : n.minFac < 334 := by
        by_contra hge
        have := Nat.mul_self_le_mul_self (Nat.not_lt.mp hge)
        rw [pow_two] at hsq
        omega
      have hdM : n.minFac ∣ bigM := List.dvd_prod (smallPrimes_mem _ hlt hm)
      have hd1 : n.minFac ∣ Nat.gcd n bigM := Nat.dvd_gcd (Nat.minFac_dvd n) hdM
      rw [hg] at hd1
      exact hm.one_lt.ne' (Nat.dvd_one.mp hd1)
    · intro hp
      have hc : Nat.Coprime n bigM := by
        unfold bigM
        rw [Nat.coprime_list_prod_right_iff]
        intro p hpL
        have hb := List.all_eq_true.mp smallPrimes_bound p hpL
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hdvd
        have := Nat.le_of_dvd hb.1 hdvd
        omega
      exact hc

/-! ### Counting primes by halving -/

/-- Number of `k ∈ [lo, lo + len)` with `P k`, by halving `len` (depth `f`; exact when `len ≤ 2 ^ f`). -/
def cntH (P : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, len => if len = 0 then 0 else if P lo then 1 else 0
  | f + 1, lo, len => cntH P f lo (len / 2) + cntH P f (lo + len / 2) (len - len / 2)

theorem cntH_eq (P : ℕ → Bool) : ∀ f lo len, len ≤ 2 ^ f →
    cntH P f lo len = Nat.count (fun k => P (lo + k) = true) len := by
  intro f
  induction f with
  | zero =>
    intro lo len h
    rcases (show len = 0 ∨ len = 1 by simp at h; omega) with h0 | h1
    · subst h0; simp [cntH]
    · subst h1; simp [cntH, Nat.count_one]
  | succ f ih =>
    intro lo len h
    have hp : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
    have h1 : len / 2 ≤ 2 ^ f := by omega
    have h2 : len - len / 2 ≤ 2 ^ f := by omega
    have e := Nat.count_add (fun k => P (lo + k) = true) (len / 2) (len - len / 2)
    rw [show len / 2 + (len - len / 2) = len by omega] at e
    rw [e]
    show cntH P f lo (len / 2) + cntH P f (lo + len / 2) (len - len / 2) = _
    rw [ih lo _ h1, ih (lo + len / 2) _ h2]
    simp only [Nat.add_assoc]

theorem count_prime_eq (n : ℕ) (hn : n ≤ 111556) :
    Nat.count Nat.Prime n = Nat.count (fun k => isPrimeG (0 + k) = true) n := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  apply Finset.filter_congr
  intro x hx
  rw [Nat.zero_add, isPrimeG_iff x (by simp at hx; omega)]

set_option maxHeartbeats 0 in
/-- Kernel computation: `10537` primes below `111031`. -/
theorem cnt_big : cntH isPrimeG 17 0 111031 = 10537 := by
  decide +kernel

theorem count_111031 : Nat.count Nat.Prime 111031 = 10537 := by
  rw [count_prime_eq 111031 (by norm_num), ← cntH_eq isPrimeG 17 0 111031 (by norm_num)]
  exact cnt_big

theorem prime_111031 : Nat.Prime 111031 := (isPrimeB_iff _).mp (by decide +kernel)

theorem prime_136973 : Nat.Prime 136973 := (isPrimeB_iff _).mp (by decide +kernel)

/-- `prime(10538) = 111031`. -/
theorem nthPrime_10538 : nthPrime 10538 = 111031 := by
  unfold nthPrime
  rw [show 10538 - 1 = Nat.count Nat.Prime 111031 by rw [count_111031]]
  exact Nat.nth_count prime_111031

/-! ### No prime `p < 136973` has `p + 111031` a square -/

/-- `s * s - 111031` is not prime for `s, s + 1, ..., s + k - 1`. -/
def compAll : ℕ → ℕ → Bool
  | 0, _ => true
  | k + 1, s => !isPrimeB (s * s - 111031) && compAll k (s + 1)

theorem compAll_spec : ∀ k s, compAll k s = true →
    ∀ t, s ≤ t → t < s + k → isPrimeB (t * t - 111031) = false := by
  intro k
  induction k with
  | zero => intro s _ t h1 h2; omega
  | succ k ih =>
    intro s h t h1 h2
    simp only [compAll, Bool.and_eq_true] at h
    rcases (show t = s ∨ s + 1 ≤ t by omega) with ht | ht
    · subst ht; simpa using h.1
    · exact ih (s + 1) h.2 t ht (by omega)

/-- `s * s - 111031` is composite for `334 ≤ s ≤ 497`. -/
theorem comp_range : compAll 164 334 = true := by decide +kernel

/-- Every prime `p` with `p + 111031` a square is at least `136973`. -/
theorem lower (p : ℕ) (hp : p.Prime) (hsq : IsSquare (p + 111031)) : 136973 ≤ p := by
  obtain ⟨s, hs⟩ := hsq
  by_contra hlt
  have h2 := hp.two_le
  have hs1 : s < 498 := by
    by_contra h
    have := Nat.mul_self_le_mul_self (Nat.not_lt.mp h)
    omega
  have hs2 : 334 ≤ s := by
    by_contra h
    have := Nat.mul_self_le_mul_self (show s ≤ 333 by omega)
    omega
  have hpe : p = s * s - 111031 := by omega
  have hf := compAll_spec 164 334 comp_range s hs2 (by omega)
  rw [← hpe, (isPrimeB_iff p).mpr hp] at hf
  exact absurd hf (by decide)

theorem sq_248004 : IsSquare (136973 + 111031) := ⟨498, by norm_num⟩

theorem A157480_10538 : A157480 10538 = 136973 := by
  unfold A157480
  rw [nthPrime_10538]
  apply le_antisymm
  · apply Nat.sInf_le
    exact ⟨prime_136973, sq_248004⟩
  · apply le_csInf
    · exact ⟨136973, prime_136973, sq_248004⟩
    · rintro p ⟨hp, hsq⟩
      exact lower p hp hsq

theorem A259232_10538 : A259232 10538 = 136973 := by
  unfold A259232
  rw [nthPrime_10538]
  apply le_antisymm
  · apply Nat.sInf_le
    exact ⟨prime_136973, by norm_num, sq_248004⟩
  · apply le_csInf
    · exact ⟨136973, prime_136973, by norm_num, sq_248004⟩
    · rintro p ⟨hp, _, hsq⟩
      exact lower p hp hsq

/-- `10538` is a term of A259226. -/
theorem term_10538 : InA259226 10538 := by
  refine ⟨by norm_num, ⟨136973, prime_136973, ?_⟩, ?_⟩
  · rw [nthPrime_10538]
    exact sq_248004
  · rw [A157480_10538, A259232_10538]

end OMA.A259226Proof

/-- The conjecture fails: `10538 > 9867` is a term of A259226 (`prime(10538) = 111031`,
`A157480(10538) = A259232(10538) = 136973`). -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a259226.main) := by
  intro h
  have := h.1 10538 OMA.A259226Proof.term_10538
  omega
