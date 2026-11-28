import OMAStatements.S_oeis_a280739

-- Problem: A280739: a(n) is the smallest composite number > a(n-1) for which the sum of the prime factors (counted with multiplicity) is n.
-- Upstream: formal-conjectures statements/oeis-a280739.lean:0 (declaration OMA.S_oeis_a280739.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: p^3 <= 3^p for every natural number p, so c^3 <= 3^(sopfr c) for every c (multiply
-- over the prime factors of c). Hence a(n-1)^3 <= 3^(n-1) for every n. For n >= 4 the
-- composite number c = 9*3^k, 4*3^k or 6*3^k (n = 3k+6, 3k+4 or 3k+5) has sopfr c = n and
-- c^3 > 3^(n-1), so c > a(n-1) and c lies in the set that defines a(n).

namespace H03A280739

open OMA.S_oeis_a280739

theorem cube_le (p : ℕ) : p ^ 3 ≤ 3 ^ p := by
  induction p with
  | zero => norm_num
  | succ k ih =>
    rcases Nat.lt_or_ge k 3 with h | h
    · interval_cases k <;> norm_num
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      have e : 3 * (j + 3) ^ 3 = (j + 3 + 1) ^ 3 + (2 * j ^ 3 + 15 * j ^ 2 + 33 * j + 17) := by
        ring
      have h1 : (j + 3 + 1) ^ 3 ≤ 3 * (j + 3) ^ 3 := by
        rw [e]
        exact Nat.le_add_right _ _
      calc (j + 3 + 1) ^ 3 ≤ 3 * (j + 3) ^ 3 := h1
        _ ≤ 3 * 3 ^ (j + 3) := Nat.mul_le_mul_left 3 ih
        _ = 3 ^ (j + 3 + 1) := by ring

theorem list_cube (L : List ℕ) : L.prod ^ 3 ≤ 3 ^ L.sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [List.prod_cons, List.sum_cons, mul_pow, pow_add (3 : ℕ) p L.sum]
    exact Nat.mul_le_mul (cube_le p) ih

theorem cube_sopfr (c : ℕ) : c ^ 3 ≤ 3 ^ sopfr c := by
  rcases Nat.eq_zero_or_pos c with h | h
  · subst h
    norm_num
  · have e := Nat.prod_primeFactorsList (by omega : c ≠ 0)
    have l := list_cube (Nat.primeFactorsList c)
    rw [e] at l
    exact l

theorem a_cube (n : ℕ) : a n ^ 3 ≤ 3 ^ n := by
  cases n with
  | zero =>
    have h0 : a 0 = 0 := rfl
    rw [h0]
    norm_num
  | succ m =>
    have hs : a (m + 1) = sInf (cands (a m) (m + 1)) := rfl
    rw [hs]
    rcases (cands (a m) (m + 1)).eq_empty_or_nonempty with h | h
    · rw [h, Nat.sInf_empty]
      norm_num
    · have hm : 1 < sInf (cands (a m) (m + 1)) ∧ ¬ (sInf (cands (a m) (m + 1))).Prime ∧
          a m < sInf (cands (a m) (m + 1)) ∧ sopfr (sInf (cands (a m) (m + 1))) = m + 1 :=
        Nat.sInf_mem h
      have hc := cube_sopfr (sInf (cands (a m) (m + 1)))
      rw [hm.2.2.2] at hc
      exact hc

theorem sopfr_23 (i j : ℕ) : sopfr (2 ^ i * 3 ^ j) = 2 * i + 3 * j := by
  have h := Nat.perm_primeFactorsList_mul (pow_ne_zero i (by norm_num : (2 : ℕ) ≠ 0))
    (pow_ne_zero j (by norm_num : (3 : ℕ) ≠ 0))
  show (Nat.primeFactorsList (2 ^ i * 3 ^ j)).sum = 2 * i + 3 * j
  rw [h.sum_eq, List.sum_append, Nat.prime_two.primeFactorsList_pow,
    Nat.prime_three.primeFactorsList_pow, List.sum_replicate_nat, List.sum_replicate_nat]
  ring

theorem witness (n : ℕ) (hn : 4 ≤ n) :
    ∃ c, 1 < c ∧ ¬ c.Prime ∧ sopfr c = n ∧ 3 ^ (n - 1) < c ^ 3 := by
  obtain ⟨k, hk | hk | hk⟩ : ∃ k, n = 3 * k + 6 ∨ n = 3 * k + 4 ∨ n = 3 * k + 5 :=
    ⟨(n - 4) / 3, by omega⟩
  · have hp : 0 < 3 ^ k := by positivity
    have hq : 0 < (3 ^ k) ^ 3 := by positivity
    refine ⟨9 * 3 ^ k, by omega, ?_, ?_, ?_⟩
    · rw [show 9 * 3 ^ k = 3 * (3 * 3 ^ k) by ring]
      exact Nat.not_prime_mul (by norm_num) (by omega)
    · rw [show 9 * 3 ^ k = 2 ^ 0 * 3 ^ (k + 2) by ring, sopfr_23]
      omega
    · rw [hk, show 3 * k + 6 - 1 = 3 * k + 5 by omega]
      have e1 : (9 * 3 ^ k) ^ 3 = 729 * (3 ^ k) ^ 3 := by ring
      have e2 : 3 ^ (3 * k + 5) = 243 * (3 ^ k) ^ 3 := by ring
      rw [e1, e2]
      omega
  · have hp : 0 < 3 ^ k := by positivity
    have hq : 0 < (3 ^ k) ^ 3 := by positivity
    refine ⟨4 * 3 ^ k, by omega, ?_, ?_, ?_⟩
    · rw [show 4 * 3 ^ k = 2 * (2 * 3 ^ k) by ring]
      exact Nat.not_prime_mul (by norm_num) (by omega)
    · rw [show 4 * 3 ^ k = 2 ^ 2 * 3 ^ k by ring, sopfr_23]
      omega
    · rw [hk, show 3 * k + 4 - 1 = 3 * k + 3 by omega]
      have e1 : (4 * 3 ^ k) ^ 3 = 64 * (3 ^ k) ^ 3 := by ring
      have e2 : 3 ^ (3 * k + 3) = 27 * (3 ^ k) ^ 3 := by ring
      rw [e1, e2]
      omega
  · have hp : 0 < 3 ^ k := by positivity
    have hq : 0 < (3 ^ k) ^ 3 := by positivity
    refine ⟨6 * 3 ^ k, by omega, ?_, ?_, ?_⟩
    · rw [show 6 * 3 ^ k = 2 * (3 * 3 ^ k) by ring]
      exact Nat.not_prime_mul (by norm_num) (by omega)
    · rw [show 6 * 3 ^ k = 2 ^ 1 * 3 ^ (k + 1) by ring, sopfr_23]
      omega
    · rw [hk, show 3 * k + 5 - 1 = 3 * k + 4 by omega]
      have e1 : (6 * 3 ^ k) ^ 3 = 216 * (3 ^ k) ^ 3 := by ring
      have e2 : 3 ^ (3 * k + 4) = 81 * (3 ^ k) ^ 3 := by ring
      rw [e1, e2]
      omega

end H03A280739

open OMA.S_oeis_a280739 H03A280739 in
theorem OMA.solution : type_of% @OMA.S_oeis_a280739.main := by
  intro n hn
  obtain ⟨c, h1, h2, h3, h4⟩ := witness n hn
  have hlt : a (n - 1) < c := by
    rcases Nat.lt_or_ge (a (n - 1)) c with h | h
    · exact h
    · have h5 := Nat.pow_le_pow_left h 3
      have h6 := a_cube (n - 1)
      exact absurd h4 (not_lt.mpr (le_trans h5 h6))
  refine ⟨c, ?_⟩
  show 1 < c ∧ ¬ c.Prime ∧ a (n - 1) < c ∧ sopfr c = n
  exact ⟨h1, h2, hlt, h3⟩
