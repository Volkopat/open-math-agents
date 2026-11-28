import FormalConjectures.ErdosProblems.«141»
import Mathlib

-- Reduction Erdos141.erdos_141.R1 of Erdős Problem 141
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 141: consecutive primes in arithmetic progression, the first four lengths

The target asks, for every `k ≥ 3`, for `k` consecutive primes forming an arithmetic
progression. Consecutive primes are written through `Nat.nth Nat.Prime`, so a witness must also
pin down the index of its first term.

Proved below, with no hypothesis:

* `count_step`: if `q` is the next prime after the prime `p`, then the prime count up to `q`
  exceeds the prime count up to `p` by one.
* `cpap`, a certificate lemma: if `p + n d` is prime for every `n < k` and every number strictly
  between two consecutive terms is composite, then the terms are `k` consecutive primes in
  arithmetic progression. The index of the first term is the number of primes below `p`, and
  `Nat.nth_count` identifies each term with the prime of the right index, so no prime count has
  to be computed.
* the cases `k = 3, 4, 5, 6`, with the progressions `3, 5, 7`, then `251 + 6 n`, then
  `9843019 + 30 n` and `121174811 + 30 n`; primality of the terms and compositeness of every
  number in the gaps are checked by `norm_num`.

Progressions of consecutive primes are known for every length up to `10` (the longest found by
large computer searches), while length `11` is open. The two hypotheses split what is left
along this line; each is a special case of the target.

* `H1`: lengths `7` to `10`, the range settled by computation.
* `H2`: every length `k ≥ 11`, the open range.
-/

namespace OMA.R_Erdos141_erdos_141_R1

open Nat Erdos141

/-- Lengths `7` to `10`: there are `k` consecutive primes in arithmetic progression. -/
def H1 : Prop :=
  ∀ k : ℕ, 7 ≤ k → k ≤ 10 → ∃ s : Set ℕ, s.IsAPAndPrimeProgressionOfLength k

/-- Every length `k ≥ 11`: there are `k` consecutive primes in arithmetic progression. -/
def H2 : Prop :=
  ∀ k : ℕ, 11 ≤ k → ∃ s : Set ℕ, s.IsAPAndPrimeProgressionOfLength k

/-- If `q` is the next prime after the prime `p`, the prime count goes up by one. -/
lemma count_step {p q : ℕ} (hp : p.Prime) (hpq : p < q)
    (hgap : ∀ m, p < m → m < q → ¬ m.Prime) :
    Nat.count Nat.Prime q = Nat.count Nat.Prime p + 1 := by
  have h1 : Nat.count Nat.Prime (p + 1) = Nat.count Nat.Prime p + 1 := by
    rw [Nat.count_succ, if_pos hp]
  have h2 : Nat.count Nat.Prime q = Nat.count Nat.Prime (p + 1) +
      Nat.count (fun k => Nat.Prime (p + 1 + k)) (q - (p + 1)) := by
    rw [← Nat.count_add]
    congr 1
    omega
  have h3 : Nat.count (fun k => Nat.Prime (p + 1 + k)) (q - (p + 1)) = 0 := by
    rw [Nat.count_eq_card_filter_range, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k hk
    rw [Finset.mem_range] at hk
    exact hgap _ (by omega) (by omega)
  rw [h2, h1, h3]

/-- Certificate: `k` primes `p + n d` with only composites strictly between consecutive terms
are `k` consecutive primes in arithmetic progression. -/
lemma cpap {p d k : ℕ} (hd : 0 < d) (hprime : ∀ n < k, (p + n * d).Prime)
    (hgap : ∀ n, n + 1 < k → ∀ m, p + n * d < m → m < p + (n + 1) * d → ¬ m.Prime) :
    ∃ s : Set ℕ, s.IsAPAndPrimeProgressionOfLength k := by
  have hcount : ∀ n < k, Nat.count Nat.Prime (p + n * d) = Nat.count Nat.Prime p + n := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      have hlt : p + n * d < p + (n + 1) * d := by nlinarith
      rw [count_step (hprime n (by omega)) hlt (hgap n hn), ih (by omega)]
      omega
  set s : Set ℕ := {x | ∃ n : ℕ, ∃ _ : (n : ℕ∞) < (k : ℕ∞), p + n • d = x} with hs
  have hinj : Function.Injective (fun n : ℕ => p + n * d) := by
    intro a b hab
    have : a * d = b * d := by simpa using hab
    exact Nat.eq_of_mul_eq_mul_right hd this
  have hsF : s = ((Finset.range k).image (fun n : ℕ => p + n * d) : Set ℕ) := by
    ext x
    simp only [hs, Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_range, Set.mem_image,
      Set.mem_Iio, smul_eq_mul, Nat.cast_lt]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, rfl⟩
  have hcard : ENat.card s = (k : ℕ∞) := by
    rw [hsF]
    change Set.encard _ = _
    rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hinj,
      Finset.card_range]
  refine ⟨s, ⟨p, d, hcard, rfl⟩, ⟨Nat.count Nat.Prime p, hcard, ?_⟩⟩
  ext x
  simp only [hs, Set.mem_ofPred_eq, smul_eq_mul]
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hn' : n < k := by exact_mod_cast hn
    refine ⟨n, hn, ?_⟩
    rw [← hcount n hn', Nat.nth_count (hprime n hn')]
  · rintro ⟨n, hn, rfl⟩
    have hn' : n < k := by exact_mod_cast hn
    refine ⟨n, hn, ?_⟩
    rw [← hcount n hn', Nat.nth_count (hprime n hn')]

/-- Length `3`: the primes `3, 5, 7`. -/
lemma case3 : ∃ s : Set ℕ, s.IsAPAndPrimeProgressionOfLength 3 := by
  apply cpap (p := 3) (d := 2) (by norm_num)
  · intro n hn
    interval_cases n <;> norm_num
  · intro n hn m h1 h2
    have hn' : n < 2 := by omega
    interval_cases n <;> (norm_num at h1 h2; interval_cases m; norm_num)

/-- Length `4`: the primes `251, 257, 263, 269`. -/
lemma case4 : ∃ s : Set ℕ, s.IsAPAndPrimeProgressionOfLength 4 := by
  apply cpap (p := 251) (d := 6) (by norm_num)
  · intro n hn
    interval_cases n <;> norm_num
  · intro n hn m h1 h2
    have hn' : n < 3 := by omega
    interval_cases n <;> (norm_num at h1 h2; interval_cases m <;> norm_num)

/-- Length `5`: the primes `9843019 + 30 n` for `n < 5`. -/
lemma case5 : ∃ s : Set ℕ, s.IsAPAndPrimeProgressionOfLength 5 := by
  apply cpap (p := 9843019) (d := 30) (by norm_num)
  · intro n hn
    interval_cases n <;> norm_num
  · intro n hn m h1 h2
    have hn' : n < 4 := by omega
    interval_cases n <;> (norm_num at h1 h2; interval_cases m <;> norm_num)

/-- Length `6`: the primes `121174811 + 30 n` for `n < 6`. -/
lemma case6 : ∃ s : Set ℕ, s.IsAPAndPrimeProgressionOfLength 6 := by
  apply cpap (p := 121174811) (d := 30) (by norm_num)
  · intro n hn
    interval_cases n <;> norm_num
  · intro n hn m h1 h2
    have hn' : n < 5 := by omega
    interval_cases n <;> (norm_num at h1 h2; interval_cases m <;> norm_num)

theorem main : H1 → H2 → type_of% @Erdos141.erdos_141 := by
  intro h1 h2 k hk
  rcases (show k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ (7 ≤ k ∧ k ≤ 10) ∨ 11 ≤ k by omega) with
    h | h | h | h | h | h
  · subst h
    exact case3
  · subst h
    exact case4
  · subst h
    exact case5
  · subst h
    exact case6
  · exact h1 k h.1 h.2
  · exact h2 k h

end OMA.R_Erdos141_erdos_141_R1
