import OMAStatements.S_oeis_a120437
import Mathlib

-- Problem: A120437: Differences of A037314 (sum of base-3 digits of n = sum of base-9 digits of n).
-- Upstream: formal-conjectures statements/oeis-a120437.lean:0 (declaration OMA.S_oeis_a120437.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! From the digit recursion b(3 m + r) = 9 b(m) + r for r < 3 one gets a(3 m + 1) = 1,
a(3 m + 2) = 1 and a(3 (m + 1)) = 9 a(m + 1) - 2. The second clause is the last identity at
m + 1 = 3^(k-1). The third clause follows by induction on k, splitting n by its residue modulo 3:
subtracting 3^(k-1) keeps the residue, and for n = 3 q it reduces to the same claim for q. -/

namespace A120437Aux

open OMA.S_oeis_a120437

theorem b_rec (m r : ℕ) (hr : r < 3) : b (3 * m + r) = 9 * b m + r := by
  unfold b
  rcases Nat.eq_zero_or_pos (3 * m + r) with h | h
  · have hm : m = 0 := by omega
    have hr0 : r = 0 := by omega
    subst hm
    subst hr0
    simp
  · rw [Nat.digits_def' (by norm_num) h, Nat.ofDigits_cons]
    have h1 : (3 * m + r) % 3 = r := by omega
    have h2 : (3 * m + r) / 3 = m := by omega
    rw [h1, h2]
    ring

theorem a_one_mod (m : ℕ) : a (3 * m + 1) = 1 := by
  unfold a
  have h1 := b_rec m 1 (by norm_num)
  have h0 := b_rec m 0 (by norm_num)
  have e : 3 * m + 1 - 1 = 3 * m + 0 := by omega
  rw [e, h1, h0]
  push_cast
  ring

theorem a_two_mod (m : ℕ) : a (3 * m + 2) = 1 := by
  unfold a
  have h2 := b_rec m 2 (by norm_num)
  have h1 := b_rec m 1 (by norm_num)
  have e : 3 * m + 2 - 1 = 3 * m + 1 := by omega
  rw [e, h2, h1]
  push_cast
  ring

theorem a_zero_mod (m : ℕ) : a (3 * (m + 1)) = 9 * a (m + 1) - 2 := by
  unfold a
  have h0 : b (3 * (m + 1)) = 9 * b (m + 1) := by
    have := b_rec (m + 1) 0 (by norm_num)
    simpa using this
  have h2 := b_rec m 2 (by norm_num)
  have e2 : 3 * (m + 1) - 1 = 3 * m + 2 := by omega
  have e3 : m + 1 - 1 = m := by omega
  rw [e2, e3, h2, h0]
  push_cast
  ring

theorem shift : ∀ k n : ℕ, 3 ^ k < n → n < 3 ^ (k + 1) → a n = a (n - 3 ^ k) := by
  intro k
  induction k with
  | zero =>
    intro n h1 h2
    have hn : n = 2 := by
      simp at h1 h2
      omega
    subst hn
    have e1 := a_two_mod 0
    have e2 := a_one_mod 0
    simp only [Nat.mul_zero, Nat.zero_add] at e1 e2
    simp only [pow_zero]
    rw [e1]
    exact e2.symm
  | succ j ih =>
    intro n h1 h2
    have hp : 3 ^ (j + 1) = 3 * 3 ^ j := by ring
    have hp2 : 3 ^ (j + 1 + 1) = 9 * 3 ^ j := by ring
    have hpos : 0 < 3 ^ j := by positivity
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ n = 3 * q + r :=
      ⟨n / 3, n % 3, Nat.mod_lt _ (by norm_num), by omega⟩
    rw [hp2] at h2
    rw [hp] at h1 ⊢
    interval_cases r
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hq1 : 3 ^ j < q' + 1 := by omega
      have hq2 : q' + 1 < 3 ^ (j + 1) := by omega
      obtain ⟨s, hs⟩ : ∃ s, q' + 1 - 3 ^ j = s + 1 := ⟨q' - 3 ^ j, by omega⟩
      have e : 3 * (q' + 1) + 0 - 3 * 3 ^ j = 3 * (s + 1) := by omega
      rw [e, add_zero, a_zero_mod, a_zero_mod, ih (q' + 1) hq1 hq2, hs]
    · have e : 3 * q + 1 - 3 * 3 ^ j = 3 * (q - 3 ^ j) + 1 := by omega
      rw [e, a_one_mod, a_one_mod]
    · have e : 3 * q + 2 - 3 * 3 ^ j = 3 * (q - 3 ^ j) + 2 := by omega
      rw [e, a_two_mod, a_two_mod]

end A120437Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a120437.main := by
  refine ⟨?_, ?_, ?_⟩
  · have := A120437Aux.a_one_mod 0
    simpa using this
  · intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m, 3 ^ j = m + 1 := ⟨3 ^ j - 1, by
      have : 0 < 3 ^ j := by positivity
      omega⟩
    have e : 3 ^ (j + 1) = 3 * (m + 1) := by rw [pow_succ, hm]; ring
    rw [e, Nat.add_sub_cancel, hm]
    exact A120437Aux.a_zero_mod m
  · intro k n hk h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel] at h1 ⊢
    exact A120437Aux.shift j n h1 h2
