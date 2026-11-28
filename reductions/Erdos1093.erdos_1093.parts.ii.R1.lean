import FormalConjectures.ErdosProblems.«1093»
import Mathlib

-- Reduction Erdos1093.erdos_1093.parts.ii.R1 of Erdős Problem 1093 — ii
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 1093 (ii): from the pairs (k, n) to the values of k

Call `C(n, k)` exceptional when `2 k ≤ n` and every prime factor of `C(n, k)` exceeds `k` (the
setting of Erdős, Lacampagne and Selfridge). Its deficiency counts the `i < k` for which `n - i`
is `k`-smooth.

Proved below, with no hypothesis:

* `smooth_term_dvd`: a `k`-smooth term `n - i` of `n (n - 1) ⋯ (n - k + 1) = k! C(n, k)` is coprime
  to `C(n, k)`, so it divides `k!`. All the `k`-smooth terms are distinct factors of that product,
  so their product divides `k!` (`smooth_terms_prod_dvd`).
* `pow_deficiency_le`: hence an exceptional `C(n, k)` of deficiency `d` has `(n + 1 - k) ^ d ≤ k!`,
  and `succ_pow_deficiency_le`: `(k + 1) ^ d ≤ k!`, which bounds the deficiency by
  `log k! / log (k + 1) < k`.
* `bound`: deficiency at least `2` gives `(n + 1 - k)^2 ≤ k!`. So each `k` occurs with only finitely
  many `n` (at most `k + √(k!)`, and at most `k + (k!)^(1/d)` for deficiency `d`).
* `five_le`: no exceptional `C(n, k)` of deficiency at least `2` has `k ≤ 4`.
* `eight_le`: with the tables `table5`, `table6`, `table7` (for `k = 5, 6, 7` every `n` left by
  `bound` gives a `C(n, k)` with a prime factor at most `k`), no exceptional `C(n, k)` of
  deficiency at least `2` has `k ≤ 7`. This is sharp: `C(44, 8)` is exceptional of deficiency `2`.
* `ten_le`: with `table8`, `table9` and the cube bound `(n + 1 - k) ^ 3 ≤ k!`, no exceptional
  `C(n, k)` of deficiency at least `3` has `k ≤ 9`. Also sharp: `C(46, 10)` has deficiency `3`.

So the finiteness of the pairs is the finiteness of the set of `k` that occur. The two
hypotheses split that set by the deficiency; each is a special case of the target.

* `H1`: only finitely many `k` occur with an exceptional `C(n, k)` of deficiency exactly `2`.
* `H2`: only finitely many `k` occur with an exceptional `C(n, k)` of deficiency at least `3`.
-/

namespace OMA.R_Erdos1093_erdos_1093_parts_ii_R1

open Erdos1093 Finset Nat

/-- Only finitely many `k` occur with an exceptional binomial coefficient `C(n, k)` (`2 k ≤ n`,
every prime factor above `k`) of deficiency exactly `2`. -/
def H1 : Prop :=
  {k : ℕ | ∃ n : ℕ, 2 * k ≤ n ∧ deficiency n k = 2 ∧
    ∀ p, p.Prime → p ∣ choose n k → k < p}.Finite

/-- Only finitely many `k` occur with an exceptional binomial coefficient `C(n, k)` of deficiency
at least `3`. -/
def H2 : Prop :=
  {k : ℕ | ∃ n : ℕ, 2 * k ≤ n ∧ 2 < deficiency n k ∧
    ∀ p, p.Prime → p ∣ choose n k → k < p}.Finite

/-- A `k`-smooth number is coprime to a binomial coefficient all of whose prime factors exceed
`k`. -/
lemma coprime_smooth {m n k : ℕ} (hs : m ∈ smoothNumbers (k + 1))
    (hC : ∀ p, p.Prime → p ∣ choose n k → k < p) : Nat.Coprime m (choose n k) := by
  apply Nat.coprime_of_dvd
  intro p hp hpm hpC
  have h1 := (mem_smoothNumbers'.1 hs) p hp hpm
  have h2 := hC p hp hpC
  omega

/-- A `k`-smooth term `n - i` (`i < k`) of an exceptional `C(n, k)` divides `k!`. -/
lemma smooth_term_dvd {n k i : ℕ} (hi : i < k)
    (hC : ∀ p, p.Prime → p ∣ choose n k → k < p)
    (hs : n - i ∈ smoothNumbers (k + 1)) : (n - i) ∣ k ! := by
  have hprod : (n - i) ∣ ∏ t ∈ range k, (n - t) :=
    Finset.dvd_prod_of_mem (fun t => n - t) (mem_range.2 hi)
  rw [← descFactorial_eq_prod_range, descFactorial_eq_factorial_mul_choose] at hprod
  exact (coprime_smooth hs hC).dvd_of_dvd_mul_right hprod

/-- All the `k`-smooth terms `n - i` (`i < k`) of an exceptional `C(n, k)` together: their
product divides `k!`. -/
lemma smooth_terms_prod_dvd {n k : ℕ} (hC : ∀ p, p.Prime → p ∣ choose n k → k < p) :
    (∏ i ∈ (range k).filter (fun i => n - i ∈ smoothNumbers (k + 1)), (n - i)) ∣ k ! := by
  have hprod : (∏ i ∈ (range k).filter (fun i => n - i ∈ smoothNumbers (k + 1)), (n - i)) ∣
      ∏ t ∈ range k, (n - t) :=
    Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  rw [← descFactorial_eq_prod_range, descFactorial_eq_factorial_mul_choose] at hprod
  have hcop : Nat.Coprime
      (∏ i ∈ (range k).filter (fun i => n - i ∈ smoothNumbers (k + 1)), (n - i)) (choose n k) := by
    apply Nat.Coprime.prod_left
    intro i hi
    exact coprime_smooth (Finset.mem_filter.1 hi).2 hC
  exact hcop.dvd_of_dvd_mul_right hprod

/-- An exceptional `C(n, k)` (`2 k ≤ n`) of deficiency `d` has `(n + 1 - k) ^ d ≤ k!`. -/
lemma pow_deficiency_le {n k : ℕ} (hk : 2 * k ≤ n)
    (hC : ∀ p, p.Prime → p ∣ choose n k → k < p) :
    (n + 1 - k) ^ deficiency n k ≤ k ! := by
  unfold deficiency
  calc (n + 1 - k) ^ ((range k).filter (fun i => n - i ∈ smoothNumbers (k + 1))).card
      ≤ ∏ i ∈ (range k).filter (fun i => n - i ∈ smoothNumbers (k + 1)), (n - i) := by
        apply Finset.pow_card_le_prod
        intro i hi
        have hik := mem_range.1 (Finset.mem_filter.1 hi).1
        omega
    _ ≤ k ! := Nat.le_of_dvd (Nat.factorial_pos k) (smooth_terms_prod_dvd hC)

/-- The deficiency `d` of an exceptional `C(n, k)` satisfies `(k + 1) ^ d ≤ k!`. -/
lemma succ_pow_deficiency_le {n k : ℕ} (hk : 2 * k ≤ n)
    (hC : ∀ p, p.Prime → p ∣ choose n k → k < p) :
    (k + 1) ^ deficiency n k ≤ k ! :=
  (Nat.pow_le_pow_left (by omega) _).trans (pow_deficiency_le hk hC)

/-- An exceptional `C(n, k)` of deficiency at least `2` has `(n + 1 - k)^2 ≤ k!`. -/
lemma bound {n k : ℕ} (hk : 2 * k ≤ n) (hd : 1 < deficiency n k)
    (hC : ∀ p, p.Prime → p ∣ choose n k → k < p) :
    (n + 1 - k) * (n + 1 - k) ≤ k ! := by
  have h1 : 0 < n + 1 - k := by omega
  calc (n + 1 - k) * (n + 1 - k) = (n + 1 - k) ^ 2 := (sq _).symm
    _ ≤ (n + 1 - k) ^ deficiency n k := Nat.pow_le_pow_right h1 hd
    _ ≤ k ! := pow_deficiency_le hk hC

/-- No exceptional `C(n, k)` of deficiency at least `2` has `k ≤ 4`. -/
lemma five_le {n k : ℕ} (hk : 2 * k ≤ n) (hd : 1 < deficiency n k)
    (hC : ∀ p, p.Prime → p ∣ choose n k → k < p) : 5 ≤ k := by
  by_contra h
  have h4 : k ≤ 4 := by omega
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0
    simp [deficiency] at hd
  · have hk1 : k + 1 ≤ n + 1 - k := by omega
    have h3 := (Nat.mul_le_mul hk1 hk1).trans (bound hk hd hC)
    interval_cases k <;> simp [Nat.factorial] at h3

/-- `t * t ≤ c < (m + 1) * (m + 1)` forces `t ≤ m`. -/
lemma le_of_mul_self_le {t m c : ℕ} (h : t * t ≤ c) (hc : c < (m + 1) * (m + 1)) : t ≤ m := by
  by_contra hlt
  have h1 : m + 1 ≤ t := by omega
  exact absurd (hc.trans_le ((Nat.mul_le_mul h1 h1).trans h)) (lt_irrefl c)

/-- Table for `k = 5`: for `10 ≤ n ≤ 14`, `C(n, 5)` has a prime factor at most `5`. -/
lemma table5 : ∀ n, n ≤ 14 → 10 ≤ n →
    (n.descFactorial 5 / 5 !) % 2 = 0 ∨ (n.descFactorial 5 / 5 !) % 3 = 0 ∨
      (n.descFactorial 5 / 5 !) % 5 = 0 := by
  decide

/-- Table for `k = 6`: for `12 ≤ n ≤ 31`, `C(n, 6)` has a prime factor at most `5`. -/
lemma table6 : ∀ n, n ≤ 31 → 12 ≤ n →
    (n.descFactorial 6 / 6 !) % 2 = 0 ∨ (n.descFactorial 6 / 6 !) % 3 = 0 ∨
      (n.descFactorial 6 / 6 !) % 5 = 0 := by
  decide

/-- Table for `k = 7`: for `14 ≤ n ≤ 76`, `C(n, 7)` has a prime factor at most `7`. -/
lemma table7 : ∀ n, n ≤ 76 → 14 ≤ n →
    (n.descFactorial 7 / 7 !) % 2 = 0 ∨ (n.descFactorial 7 / 7 !) % 3 = 0 ∨
      (n.descFactorial 7 / 7 !) % 5 = 0 ∨ (n.descFactorial 7 / 7 !) % 7 = 0 := by
  decide

/-- No exceptional `C(n, k)` of deficiency at least `2` has `k ≤ 7`. This is sharp: `C(44, 8)`
is exceptional of deficiency `2` (the first example of Erdős, Lacampagne and Selfridge; a
computation, not used here). -/
lemma eight_le {n k : ℕ} (hk : 2 * k ≤ n) (hd : 1 < deficiency n k)
    (hC : ∀ p, p.Prime → p ∣ choose n k → k < p) : 8 ≤ k := by
  have h5 := five_le hk hd hC
  have hb := bound hk hd hC
  by_contra h
  have hk7 : k ≤ 7 := by omega
  have hch : choose n k = n.descFactorial k / k ! := Nat.choose_eq_descFactorial_div_factorial n k
  have small : ∀ p, p.Prime → p ≤ k → (n.descFactorial k / k !) % p = 0 → False := by
    intro p hp hpk hmod
    have hdvd : p ∣ choose n k := by
      rw [hch]
      exact Nat.dvd_of_mod_eq_zero hmod
    have := hC p hp hdvd
    omega
  interval_cases k
  · have hn : n + 1 - 5 ≤ 10 := le_of_mul_self_le hb (by decide)
    rcases table5 n (by omega) (by omega) with h' | h' | h'
    · exact small 2 Nat.prime_two (by norm_num) h'
    · exact small 3 Nat.prime_three (by norm_num) h'
    · exact small 5 Nat.prime_five (by norm_num) h'
  · have hn : n + 1 - 6 ≤ 26 := le_of_mul_self_le hb (by decide)
    rcases table6 n (by omega) (by omega) with h' | h' | h'
    · exact small 2 Nat.prime_two (by norm_num) h'
    · exact small 3 Nat.prime_three (by norm_num) h'
    · exact small 5 Nat.prime_five (by norm_num) h'
  · have hn : n + 1 - 7 ≤ 70 := le_of_mul_self_le hb (by decide)
    rcases table7 n (by omega) (by omega) with h' | h' | h' | h'
    · exact small 2 Nat.prime_two (by norm_num) h'
    · exact small 3 Nat.prime_three (by norm_num) h'
    · exact small 5 Nat.prime_five (by norm_num) h'
    · exact small 7 (by norm_num) (by norm_num) h'

/-- `t ^ 3 ≤ c < (m + 1) ^ 3` forces `t ≤ m`. -/
lemma le_of_cube_le {t m c : ℕ} (h : t ^ 3 ≤ c) (hc : c < (m + 1) ^ 3) : t ≤ m := by
  by_contra hlt
  have h1 : m + 1 ≤ t := by omega
  exact absurd (hc.trans_le ((Nat.pow_le_pow_left h1 3).trans h)) (lt_irrefl c)

/-- Table for `k = 8`: for `16 ≤ n ≤ 41`, `C(n, 8)` has a prime factor at most `7`. -/
lemma table8 : ∀ n, n ≤ 41 → 16 ≤ n →
    (n.descFactorial 8 / 8 !) % 2 = 0 ∨ (n.descFactorial 8 / 8 !) % 3 = 0 ∨
      (n.descFactorial 8 / 8 !) % 5 = 0 ∨ (n.descFactorial 8 / 8 !) % 7 = 0 := by
  decide

/-- Table for `k = 9`: for `18 ≤ n ≤ 79`, `C(n, 9)` has a prime factor at most `7`. -/
lemma table9 : ∀ n, n ≤ 79 → 18 ≤ n →
    (n.descFactorial 9 / 9 !) % 2 = 0 ∨ (n.descFactorial 9 / 9 !) % 3 = 0 ∨
      (n.descFactorial 9 / 9 !) % 5 = 0 ∨ (n.descFactorial 9 / 9 !) % 7 = 0 := by
  decide

/-- No exceptional `C(n, k)` of deficiency at least `3` has `k ≤ 9`. This is sharp: `C(46, 10)`
is exceptional of deficiency `3` (a computation, not used here). -/
lemma ten_le {n k : ℕ} (hk : 2 * k ≤ n) (hd : 2 < deficiency n k)
    (hC : ∀ p, p.Prime → p ∣ choose n k → k < p) : 10 ≤ k := by
  have h8 := eight_le hk (by omega) hC
  have h3 : (n + 1 - k) ^ 3 ≤ k ! :=
    (Nat.pow_le_pow_right (by omega) hd).trans (pow_deficiency_le hk hC)
  by_contra h
  have hk9 : k ≤ 9 := by omega
  have hch : choose n k = n.descFactorial k / k ! := Nat.choose_eq_descFactorial_div_factorial n k
  have small : ∀ p, p.Prime → p ≤ k → (n.descFactorial k / k !) % p = 0 → False := by
    intro p hp hpk hmod
    have hdvd : p ∣ choose n k := by
      rw [hch]
      exact Nat.dvd_of_mod_eq_zero hmod
    have := hC p hp hdvd
    omega
  interval_cases k
  · have hn : n + 1 - 8 ≤ 34 := le_of_cube_le h3 (by decide)
    rcases table8 n (by omega) (by omega) with h' | h' | h' | h'
    · exact small 2 Nat.prime_two (by norm_num) h'
    · exact small 3 Nat.prime_three (by norm_num) h'
    · exact small 5 Nat.prime_five (by norm_num) h'
    · exact small 7 (by norm_num) (by norm_num) h'
  · have hn : n + 1 - 9 ≤ 71 := le_of_cube_le h3 (by decide)
    rcases table9 n (by omega) (by omega) with h' | h' | h' | h'
    · exact small 2 Nat.prime_two (by norm_num) h'
    · exact small 3 Nat.prime_three (by norm_num) h'
    · exact small 5 Nat.prime_five (by norm_num) h'
    · exact small 7 (by norm_num) (by norm_num) h'

theorem main : H1 → H2 → type_of% @Erdos1093.erdos_1093.parts.ii := by
  intro h1 h2
  have hK : {k : ℕ | ∃ n : ℕ, 2 * k ≤ n ∧ 1 < deficiency n k ∧
      ∀ p, p.Prime → p ∣ choose n k → k < p}.Finite := by
    refine (h1.union h2).subset ?_
    rintro k ⟨n, hn, hd, hC⟩
    rcases Nat.lt_or_ge 2 (deficiency n k) with h | h
    · exact Or.inr ⟨n, hn, h, hC⟩
    · exact Or.inl ⟨n, hn, by omega, hC⟩
  obtain ⟨B, hB⟩ := hK.bddAbove
  refine ((Set.finite_Iic B).prod (Set.finite_Iic (B ! + B))).subset ?_
  rintro ⟨k, n⟩ ⟨hn, hd, hC⟩
  have hkB : k ≤ B := hB ⟨n, hn, hd, hC⟩
  have hlin : n + 1 - k ≤ k ! := (Nat.le_mul_self _).trans (bound hn hd hC)
  have hfac : k ! ≤ B ! := Nat.factorial_le hkB
  refine ⟨hkB, ?_⟩
  show n ≤ B ! + B
  omega

end OMA.R_Erdos1093_erdos_1093_parts_ii_R1
