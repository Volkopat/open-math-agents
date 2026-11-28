import OMAStatements.S_oeis_a257230

-- Credit: @Alewawa

/-!
For consecutive primes p < q, positivity of the sequence is equivalent to
q - p < Nat.sqrt q. Partition a square interval at k(k+1). Pairs whose endpoints
lie in the same open part already obey the gap bound from its length. The remaining
cases reduce to bracketing squares and products of consecutive integers with primes.
-/

open OMA.S_oeis_a257230

namespace OMA.R_oeis_a257230_R1

private theorem next_prime_gt {n : ℕ} (hn : 1 ≤ n) : prime n < prime (n + 1) := by
  unfold prime
  exact Nat.nth_strictMono Nat.infinite_setOfPred_prime (by omega)

private theorem a_negative_iff {n : ℕ} (hn : 1 ≤ n) :
    a n < 0 ↔ prime (n+1) < (prime (n+1) - prime n)^2 := by
  have h := (next_prime_gt hn).le
  rw [a, Int.floor_lt]
  push_cast
  rw [sub_lt_zero, ← Nat.cast_sub h, Real.sqrt_lt (by positivity) (by positivity)]
  norm_cast

private theorem a_positive_of_gap {n : ℕ}
    (hn : 1 ≤ n) (hgap : prime (n+1) - prime n < (prime (n+1)).sqrt) :
    0 < a n := by
  have h := (next_prime_gt hn).le
  have hs : (↑(prime (n+1) - prime n + 1) : ℝ) ≤ Real.sqrt (prime (n+1)) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    exact_mod_cast Nat.le_sqrt'.mp (Nat.succ_le_of_lt hgap)
  have hform : (1 : ℤ) ≤ a n := by
    rw [a, Int.le_floor, Int.cast_one]
    push_cast at hs
    rw [Nat.cast_sub h] at hs
    linarith
  omega

set_option maxRecDepth 16000 in
private theorem nth_prime_initial {k : ℕ} (hk : k ≤ 30) :
    Nat.nth Nat.Prime k =
      ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127] : List ℕ)[k]! := by
  let L : List ℕ :=
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
      59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127]
  have htable : ∀ i : Fin 31, (L[i.val]!).Prime ∧ Nat.count Nat.Prime L[i.val]! = i.val := by
    decide
  obtain ⟨hprime, hcount⟩ := htable ⟨k, by omega⟩
  simpa only [hcount] using Nat.nth_count hprime

set_option maxRecDepth 16000 in
/-- Negative terms among the first thirty, certified with kernel arithmetic. -/
private theorem initial_signs {n : ℕ} (hn : 1 ≤ n) (h30 : n ≤ 30) :
    a n < 0 ↔ n = 4 ∨ n = 9 ∨ n = 30 := by
  rw [a_negative_iff hn]
  unfold prime
  rw [Nat.add_sub_cancel, nth_prime_initial h30, nth_prime_initial (by omega : n - 1 ≤ 30)]
  let L : List ℕ :=
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
      59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127]
  have htable : ∀ i : Fin 31, 1 ≤ i.val →
      (L[i.val]! < (L[i.val]! - L[i.val - 1]!)^2 ↔
        i.val = 4 ∨ i.val = 9 ∨ i.val = 30) := by decide
  exact htable ⟨n, by omega⟩ hn

private theorem between_not_prime {n r : ℕ} (hn : 1 ≤ n)
    (hl : prime n < r) (hr : r < prime (n+1)) (hp : r.Prime) : False := by
  unfold prime at hl hr
  have he := Nat.nth_count hp
  rw [← he] at hl hr
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hl' := hmono.lt_iff_lt.mp hl
  have hr' := hmono.lt_iff_lt.mp hr
  omega

private theorem gap_le_of_bracket {n b p q : ℕ} (hn : 1 ≤ n)
    (hL : prime n < b) (hR : b < prime (n+1))
    (hp : p.Prime) (hq : q.Prime) (hpL : p < b) (hqR : b < q) :
    prime (n+1) - prime n ≤ q - p := by
  have hpl : p ≤ prime n := by
    by_contra! hh
    exact between_not_prime hn hh (hpL.trans hR) hp
  have hqr : prime (n+1) ≤ q := by
    by_contra! hh
    exact between_not_prime hn (hL.trans hqR) hh hq
  omega

private theorem gap_of_a_positive {n : ℕ} (hn : 1 ≤ n) (ha : 0 < a n) :
    prime (n+1) - prime n < (prime (n+1)).sqrt := by
  have hpq := (next_prime_gt hn).le
  have hf : (1 : ℤ) ≤ a n := by omega
  rw [a, Int.le_floor, Int.cast_one] at hf
  have hs : (↑(prime (n+1) - prime n + 1) : ℝ) ≤ Real.sqrt (prime (n+1)) := by
    push_cast
    rw [Nat.cast_sub hpq]
    linarith
  have hsq := (Real.le_sqrt (by positivity) (by positivity)).mp hs
  exact Nat.lt_of_succ_le (Nat.le_sqrt'.mpr (by exact_mod_cast hsq))

/-- A short gap across a boundary at most k(k+1) is contained below the next square. -/
private theorem bracket_from_positivity {k c : ℕ} (hc : 132 ≤ c) (hck : c ≤ k*(k+1))
    (hcomp : ¬ c.Prime) (hpos : ∀ n : ℕ, 30 < n → 0 < a n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < c ∧ c < q ∧ q-p < k := by
  let n := Nat.count Nat.Prime c
  have hinf := Nat.infinite_setOfPred_prime
  have h127 : Nat.nth Nat.Prime 30 = 127 := nth_prime_initial (by norm_num)
  have hn : 30 < n := (Nat.lt_nth_iff_count_lt hinf).mpr (h127 ▸ by omega)
  let p := prime n
  let q := prime (n+1)
  have hp : p.Prime := Nat.nth_mem_of_infinite hinf _
  have hq : q.Prime := Nat.nth_mem_of_infinite hinf _
  have hpL : p < c := (Nat.lt_nth_iff_count_lt hinf).mp (by change n-1 < n; omega)
  have hqR : c < q := by
    have hle : c ≤ q := by
      unfold q prime
      rw [Nat.add_sub_cancel]
      exact Nat.le_nth_count hinf c
    refine hle.lt_of_ne fun h => hcomp ?_
    rwa [h]
  have hgap : q-p < q.sqrt := gap_of_a_positive (by omega) (hpos n hn)
  have hsqrt : q.sqrt ≤ k := by
    by_contra! hs
    let u := q.sqrt
    have hu : k + 1 ≤ u := by omega
    have hu' : k ≤ u - 1 := by omega
    have hmul : k*(k+1) ≤ (u-1)*u := Nat.mul_le_mul hu' hu
    have hsq : u^2 ≤ q := Nat.sqrt_le' q
    have hu_pos : 1 ≤ u := by omega
    have hbound : (u-1)*u + u = u^2 := by
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_self _), pow_two]
    change q-p < u at hgap
    omega
  exact ⟨p, q, hp, hq, hpL, hqR, hgap.trans_le hsqrt⟩

/-- Close bracketing primes at square boundaries. -/
def H1 : Prop :=
  ∀ k : ℕ, 12 ≤ k → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < k^2 ∧ k^2 < q ∧ q-p < k

/-- Close bracketing primes at boundaries that are products of consecutive integers. -/
def H2 : Prop :=
  ∀ k : ℕ, 11 ≤ k →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < k*(k+1) ∧ k*(k+1) < q ∧ q-p < k

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a257230.main := by
  intro h1 h2
  have hpos (n : ℕ) (hn : 30 < n) : 0 < a n := by
    have hn1 : 1 ≤ n := by omega
    let p := prime n
    let q := prime (n+1)
    have hpq : p < q := next_prime_gt hn1
    have hp : p.Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
    have hq : q.Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
    have h127 : 127 ≤ p := by
      change 127 ≤ Nat.nth Nat.Prime (n-1)
      have htable : Nat.nth Nat.Prime 30 = 127 := by
        exact nth_prime_initial (by norm_num : (30 : ℕ) ≤ 30)
      rw [← htable]
      exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (by omega)
    let k := q.sqrt
    have hk : 11 ≤ k := Nat.le_sqrt'.mpr (by norm_num; omega)
    have hkL : k^2 < q := by
      apply (Nat.sqrt_le' q).lt_of_ne
      intro he
      exact (Nat.Prime.not_prime_pow (by norm_num : 2 ≤ 2)) (he.symm ▸ hq)
    have hkR : q < (k+1)^2 := Nat.lt_succ_sqrt' q
    have hmid : k*(k+1) = k^2 + k := by ring
    have hnext : (k+1)^2 = k*(k+1) + k + 1 := by ring
    have hnp : ¬ (k*(k+1)).Prime := Nat.not_prime_mul (by omega) (by omega)
    apply a_positive_of_gap hn1
    change q - p < k
    by_cases hpL : p < k^2
    · have hk12 : 12 ≤ k := by
        by_contra! h
        have h11 : k = 11 := by omega
        rw [h11] at hpL
        norm_num at hpL
        omega
      obtain ⟨a, b, ha, hb, haL, hbR, hgap⟩ := h1 k hk12
      exact (gap_le_of_bracket hn1 hpL hkL ha hb haL hbR).trans_lt hgap
    · have hpL' : k^2 < p := by
        apply (le_of_not_gt hpL).lt_of_ne
        intro he
        exact (Nat.Prime.not_prime_pow (by norm_num : 2 ≤ 2)) (he.symm ▸ hp)
      by_cases hqL : q ≤ k*(k+1)
      · omega
      · have hqR : k*(k+1) < q := by omega
        by_cases hpM : p < k*(k+1)
        · obtain ⟨a, b, ha, hb, haL, hbR, hgap⟩ := h2 k hk
          exact (gap_le_of_bracket hn1 hpM hqR ha hb haL hbR).trans_lt hgap
        · have hpM' : k*(k+1) < p := by
            apply (le_of_not_gt hpM).lt_of_ne
            intro he
            exact hnp (he.symm ▸ hp)
          omega
  refine ⟨hpos, fun n hn => ?_⟩
  by_cases h30 : n ≤ 30
  · exact initial_signs hn h30
  · have h := hpos n (by omega)
    omega

/-- The boundary estimates capture the exact infinite part of the conjecture. -/
theorem boundary_equiv : (H1 ∧ H2) ↔ (type_of% @OMA.S_oeis_a257230.main) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact main h1 h2
  · intro h
    constructor
    · intro k hk
      have hc : 132 ≤ k^2 := (by norm_num : 132 ≤ (12 : ℕ)^2).trans
        (Nat.pow_le_pow_left hk 2)
      have hck : k^2 ≤ k*(k+1) := by rw [pow_two]; exact Nat.mul_le_mul_left k (by omega)
      exact bracket_from_positivity hc hck (Nat.Prime.not_prime_pow (by norm_num)) h.1
    · intro k hk
      have hc : 132 ≤ k*(k+1) := Nat.mul_le_mul hk (by omega : 12 ≤ k+1)
      exact bracket_from_positivity hc le_rfl (Nat.not_prime_mul (by omega) (by omega)) h.1

end OMA.R_oeis_a257230_R1
