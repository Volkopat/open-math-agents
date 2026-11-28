import OMAStatements.S_oeis_a182508
import Mathlib

namespace OMA.P182508

open OMA.S_oeis_a182508

lemma a_succ_succ (n : ℕ) : a (n + 2) = (a n + a (n + 1) + (n + 2)) &&& (n + 2) := by
  rw [a]

lemma a_le (n : ℕ) : a n ≤ n := by
  match n with
  | 0 => simp [a]
  | 1 => simp [a]
  | (n + 2) => rw [a_succ_succ]; exact Nat.and_le_right

lemma and_mod_two (x y : ℕ) : (x &&& y) % 2 = x % 2 &&& y % 2 := by
  have h := @Nat.and_mod_two_pow x y 1
  simpa using h

lemma and_mod_four (x y : ℕ) : (x &&& y) % 4 = x % 4 &&& y % 4 := by
  have h := @Nat.and_mod_two_pow x y 2
  simpa using h

/-- Terms with even index are even. -/
lemma a_even (n : ℕ) : a (2 * n) % 2 = 0 := by
  rcases n with _ | n
  · simp [a]
  · have e : 2 * (n + 1) = 2 * n + 2 := by ring
    rw [e, a_succ_succ, and_mod_two]
    have : (2 * n + 2) % 2 = 0 := by omega
    rw [this, Nat.and_zero]

/-- Terms with index 4n+1 are odd, terms with index 4n+3 are even. -/
lemma parity (n : ℕ) : a (4 * n + 1) % 2 = 1 ∧ a (4 * n + 3) % 2 = 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h4 : a (4 * n + 4) % 2 = 0 := by
      have := a_even (2 * n + 2)
      rwa [show 2 * (2 * n + 2) = 4 * n + 4 by ring] at this
    have h6 : a (4 * n + 6) % 2 = 0 := by
      have := a_even (2 * n + 3)
      rwa [show 2 * (2 * n + 3) = 4 * n + 6 by ring] at this
    have h5 : a (4 * n + 5) % 2 = 1 := by
      rw [show 4 * n + 5 = (4 * n + 3) + 2 by ring, a_succ_succ, and_mod_two]
      have hx : (a (4 * n + 3) + a (4 * n + 3 + 1) + (4 * n + 3 + 2)) % 2 = 1 := by
        rw [show 4 * n + 3 + 1 = 4 * n + 4 by ring]
        omega
      have hy : (4 * n + 3 + 2) % 2 = 1 := by omega
      rw [hx, hy]
      rfl
    refine ⟨by rw [show 4 * (n + 1) + 1 = 4 * n + 5 by ring]; exact h5, ?_⟩
    rw [show 4 * (n + 1) + 3 = (4 * n + 5) + 2 by ring, a_succ_succ, and_mod_two]
    have hx : (a (4 * n + 5) + a (4 * n + 5 + 1) + (4 * n + 5 + 2)) % 2 = 0 := by
      rw [show 4 * n + 5 + 1 = 4 * n + 6 by ring]
      omega
    rw [hx, Nat.zero_and]

/-- The bitwise step used at the start of a block [2^j, 2^(j+1)). -/
lemma and_block (j x y c : ℕ) (hx : x < 2 ^ j) (hy : y < 2 ^ j) :
    (x + 2 ^ j * c) &&& (y + 2 ^ j) = (x &&& y) + 2 ^ j * (c % 2) := by
  have hP : 0 < 2 ^ j := by positivity
  have hA1 : (x + 2 ^ j * c) / 2 ^ j = c := by
    rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hx, zero_add]
  have hA2 : (x + 2 ^ j * c) % 2 ^ j = x := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  have hB1 : (y + 2 ^ j) / 2 ^ j = 1 := by
    have := Nat.add_mul_div_left y 1 hP
    rw [mul_one, Nat.div_eq_of_lt hy, zero_add] at this
    exact this
  have hB2 : (y + 2 ^ j) % 2 ^ j = y := by
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hy]
  have key := Nat.div_add_mod ((x + 2 ^ j * c) &&& (y + 2 ^ j)) (2 ^ j)
  rw [Nat.and_div_two_pow, Nat.and_mod_two_pow, hA1, hA2, hB1, hB2, Nat.and_one_is_mod] at key
  rw [← key]
  ring

/-- a(2^j) is 0 or 2^j. -/
lemma a_two_pow (j : ℕ) (hj : 1 ≤ j) : ∃ e, e ≤ 1 ∧ a (2 ^ j) = 2 ^ j * e := by
  have h2 : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  obtain ⟨P, hP⟩ : ∃ P, 2 ^ j = P + 2 := ⟨2 ^ j - 2, by omega⟩
  refine ⟨(Nat.testBit (a P + a (P + 1) + (P + 2)) j).toNat, Bool.toNat_le _, ?_⟩
  rw [hP, a_succ_succ, ← hP, Nat.and_two_pow, mul_comm]

/-- The pattern of the top bit at the start of a block. -/
def f (e r : ℕ) : ℕ := if r = 0 then e else if r = 1 then 1 - e else 0

lemma block (j : ℕ) (hj : 2 ≤ j) (e : ℕ) (he : e ≤ 1) (h0 : a (2 ^ j) = 2 ^ j * e) :
    ∀ m, 3 * m ≤ 2 ^ j → a (2 ^ j + m) = a m + 2 ^ j * f e (m % 3) := by
  have h4 : 4 ≤ 2 ^ j := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    match m with
    | 0 => simp [a, h0, f]
    | 1 =>
      -- a(2^j - 1) is even, since 2^j - 1 = 4 t + 3
      obtain ⟨t, rfl⟩ : ∃ t, j = t + 2 := ⟨j - 2, by omega⟩
      have ht : 2 ^ (t + 2) = 4 * 2 ^ t := by ring
      have ht1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
      obtain ⟨Q, hQ⟩ : ∃ Q, 2 ^ (t + 2) = Q + 1 := ⟨2 ^ (t + 2) - 1, by omega⟩
      have hQe : a Q % 2 = 0 := by
        have := (parity (2 ^ t - 1)).2
        rwa [show 4 * (2 ^ t - 1) + 3 = Q by omega] at this
      have hQle := a_le Q
      have hQlt : a Q + 1 < 2 ^ (t + 2) := by
        have : a Q ≠ Q := by
          intro h
          have : Q % 2 = 1 := by omega
          omega
        omega
      have e1 : 2 ^ (t + 2) + 1 = Q + 2 := by omega
      rw [e1, a_succ_succ, show Q + 1 = 2 ^ (t + 2) by omega, h0]
      rw [show a Q + 2 ^ (t + 2) * e + (Q + 2) = (a Q + 1) + 2 ^ (t + 2) * (e + 1) by
          rw [show Q + 2 = 2 ^ (t + 2) + 1 by omega]; ring,
        show Q + 2 = 1 + 2 ^ (t + 2) by omega]
      rw [and_block (t + 2) _ _ _ hQlt (by omega), Nat.and_one_is_mod]
      have : (a Q + 1) % 2 = 1 := by omega
      rw [this]
      interval_cases e <;> simp [a, f]
    | (m + 2) =>
      have ih0 := ih m (by omega) (by omega)
      have ih1 := ih (m + 1) (by omega) (by omega)
      have hx : a m + a (m + 1) + (m + 2) < 2 ^ j := by
        have := a_le m
        have := a_le (m + 1)
        omega
      have hy : m + 2 < 2 ^ j := by omega
      rw [show 2 ^ j + (m + 2) = (2 ^ j + m) + 2 by ring, a_succ_succ,
        show 2 ^ j + m + 1 = 2 ^ j + (m + 1) by ring, ih0, ih1]
      rw [show a m + 2 ^ j * f e (m % 3) + (a (m + 1) + 2 ^ j * f e ((m + 1) % 3)) + (2 ^ j + m + 2)
          = (a m + a (m + 1) + (m + 2)) + 2 ^ j * (f e (m % 3) + f e ((m + 1) % 3) + 1) by ring,
        show 2 ^ j + m + 2 = (m + 2) + 2 ^ j by ring]
      rw [and_block j _ _ _ hx hy, ← a_succ_succ]
      congr 2
      have hr : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases hr with hr | hr | hr
      · have h1 : (m + 1) % 3 = 1 := by omega
        have h2 : (m + 2) % 3 = 2 := by omega
        rw [hr, h1, h2]
        interval_cases e <;> simp [f]
      · have h1 : (m + 1) % 3 = 2 := by omega
        have h2 : (m + 2) % 3 = 0 := by omega
        rw [hr, h1, h2]
        interval_cases e <;> simp [f]
      · have h1 : (m + 1) % 3 = 0 := by omega
        have h2 : (m + 2) % 3 = 1 := by omega
        rw [hr, h1, h2]
        interval_cases e <;> simp [f]

set_option maxRecDepth 100000 in
lemma a_8 : a 8 = 0 := by decide

set_option maxRecDepth 100000 in
lemma a_65 : a 65 = 1 := by decide

lemma no_three_mod_four (n : ℕ) : a n % 4 ≠ 3 := by
  match n with
  | 0 => simp [a]
  | 1 => simp [a]
  | (m + 2) =>
    intro h
    have h' := h
    rw [a_succ_succ, and_mod_four] at h'
    have key : ∀ u < 4, ∀ v < 4, (u &&& v) = 3 → v = 3 := by decide
    have hv : (m + 2) % 4 = 3 := key _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num)) h'
    obtain ⟨q, hq⟩ : ∃ q, m + 2 = 4 * q + 3 := ⟨(m + 2) / 4, by omega⟩
    have := (parity q).2
    rw [← hq] at this
    omega

theorem sol : type_of% @OMA.S_oeis_a182508.main := by
  refine ⟨?_, ?_, ?_⟩
  · apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨e, he, h0⟩ := a_two_pow (N + 5) (by omega)
    have hb := block (N + 5) (by omega) e he h0 8
    have hp : 32 ≤ 2 ^ (N + 5) := by
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ (N + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hN : N < 2 ^ (N + 5) := lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
    refine ⟨2 ^ (N + 5) + 8, ?_, by omega⟩
    show a (2 ^ (N + 5) + 8) = 0
    rw [hb (by omega), a_8]
    simp [f]
  · apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨e, he, h0⟩ := a_two_pow (N + 8) (by omega)
    have hb := block (N + 8) (by omega) e he h0 65
    have hp : 256 ≤ 2 ^ (N + 8) := by
      calc 256 = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ (N + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hN : N < 2 ^ (N + 8) := lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
    refine ⟨2 ^ (N + 8) + 65, ?_, by omega⟩
    show a (2 ^ (N + 8) + 65) = 1
    rw [hb (by omega), a_65]
    simp [f]
  · intro n k hk h
    obtain ⟨t, rfl⟩ : ∃ t, k = t + 2 := ⟨k - 2, by omega⟩
    have ht : 2 ^ (t + 2) = 4 * 2 ^ t := by ring
    have ht1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    have h3 : a n % 4 = 3 := by omega
    exact no_three_mod_four n h3

end OMA.P182508

theorem OMA.solution : type_of% @OMA.S_oeis_a182508.main := OMA.P182508.sol

