import OMAStatements.S_oeis_a165968

-- Problem: A165968: Number of pairings disjoint to a given pairing, and containing a given pair not in the given pairing.
-- Upstream: formal-conjectures statements/oeis-a165968.lean:0 (declaration OMA.S_oeis_a165968.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Put d(k) = (2k+1)!!, S(m) = Sum_{k ≤ m} (-1)^(m+k) C(m,k) d(k) and
U(m) = Sum_{k ≤ m} (-1)^(m+k) C(m,k) d(k+1), so that a(m+2) = S(m). Pascal's rule gives
S(m+1) = U(m) - S(m). From d(k+1) = (2k+3) d(k) and (k+1) C(m+1,k+1) = (m+1) C(m,k) one gets
U(m+1) = 2(m+1) U(m) + 3 S(m+1). Eliminating U gives S(m+2) = (2m+4) S(m+1) + (2m+2) S(m). -/

namespace A165968Aux

open OMA.S_oeis_a165968

/-- d(k) = (2k+1)!!. -/
def d (k : ℕ) : ℤ := (Nat.doubleFactorial (2 * k + 1) : ℤ)

def S (m : ℕ) : ℤ := ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m + k) * (m.choose k : ℤ) * d k

def U (m : ℕ) : ℤ := ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m + k) * (m.choose k : ℤ) * d (k + 1)

theorem hd (k : ℕ) : d (k + 1) = (2 * (k : ℤ) + 3) * d k := by
  unfold d
  have e : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
  rw [e, Nat.doubleFactorial_add_two]
  push_cast
  ring

theorem claim1 (m : ℕ) : S (m + 1) = U m - S m := by
  have hS1 : S (m + 1) = ∑ k ∈ Finset.range (m + 1),
      (-1 : ℤ) ^ (m + 1 + (k + 1)) * ((m + 1).choose (k + 1) : ℤ) * d (k + 1) +
      (-1 : ℤ) ^ (m + 1 + 0) * ((m + 1).choose 0 : ℤ) * d 0 := by
    unfold S
    exact Finset.sum_range_succ' _ _
  have hS : S m = ∑ k ∈ Finset.range m,
      (-1 : ℤ) ^ (m + (k + 1)) * (m.choose (k + 1) : ℤ) * d (k + 1) +
      (-1 : ℤ) ^ (m + 0) * (m.choose 0 : ℤ) * d 0 := by
    unfold S
    exact Finset.sum_range_succ' _ _
  have hU : U m = ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m + k) * (m.choose k : ℤ) * d (k + 1) := rfl
  have h1 : ∑ k ∈ Finset.range (m + 1),
      (-1 : ℤ) ^ (m + 1 + (k + 1)) * ((m + 1).choose (k + 1) : ℤ) * d (k + 1) =
      ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m + k) * (m.choose k : ℤ) * d (k + 1) +
      ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m + k) * (m.choose (k + 1) : ℤ) * d (k + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hp : (-1 : ℤ) ^ (m + 1 + (k + 1)) = (-1) ^ (m + k) := by
      have e : m + 1 + (k + 1) = m + k + 2 := by ring
      rw [e, pow_add]
      norm_num
    rw [hp, Nat.choose_succ_succ']
    push_cast
    ring
  have h2 : ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m + k) * (m.choose (k + 1) : ℤ) * d (k + 1) =
      -∑ k ∈ Finset.range m, (-1 : ℤ) ^ (m + (k + 1)) * (m.choose (k + 1) : ℤ) * d (k + 1) := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self, ← Finset.sum_neg_distrib]
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    have hp : (-1 : ℤ) ^ (m + (k + 1)) = -(-1) ^ (m + k) := by
      have e : m + (k + 1) = m + k + 1 := by ring
      rw [e, pow_succ]
      ring
    rw [hp]
    ring
  have hp0 : (-1 : ℤ) ^ (m + 1 + 0) = -(-1) ^ (m + 0) := by
    have e : m + 1 + 0 = m + 0 + 1 := by ring
    rw [e, pow_succ]
    ring
  rw [hS1, hS, hU, h1, h2, hp0]
  simp only [Nat.choose_zero_right, Nat.cast_one]
  ring

theorem claim2 (m : ℕ) : U (m + 1) = 2 * ((m : ℤ) + 1) * U m + 3 * S (m + 1) := by
  have hU1 : U (m + 1) = ∑ k ∈ Finset.range (m + 1 + 1),
      (-1 : ℤ) ^ (m + 1 + k) * ((m + 1).choose k : ℤ) * d (k + 1) := rfl
  have e1 : ∑ k ∈ Finset.range (m + 1 + 1),
      (-1 : ℤ) ^ (m + 1 + k) * ((m + 1).choose k : ℤ) * d (k + 1) =
      2 * ∑ k ∈ Finset.range (m + 1 + 1),
        (-1 : ℤ) ^ (m + 1 + k) * (k : ℤ) * ((m + 1).choose k : ℤ) * d k + 3 * S (m + 1) := by
    unfold S
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hd k]
    ring
  have k1 : ∑ k ∈ Finset.range (m + 1 + 1),
      (-1 : ℤ) ^ (m + 1 + k) * (k : ℤ) * ((m + 1).choose k : ℤ) * d k =
      ∑ k ∈ Finset.range (m + 1),
        (-1 : ℤ) ^ (m + 1 + (k + 1)) * ((k + 1 : ℕ) : ℤ) * ((m + 1).choose (k + 1) : ℤ) * d (k + 1) +
      (-1 : ℤ) ^ (m + 1 + 0) * ((0 : ℕ) : ℤ) * ((m + 1).choose 0 : ℤ) * d 0 :=
    Finset.sum_range_succ' _ _
  have k2 : ∑ k ∈ Finset.range (m + 1),
      (-1 : ℤ) ^ (m + 1 + (k + 1)) * ((k + 1 : ℕ) : ℤ) * ((m + 1).choose (k + 1) : ℤ) * d (k + 1) =
      ((m : ℤ) + 1) * U m := by
    unfold U
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hc : ((k : ℤ) + 1) * ((m + 1).choose (k + 1) : ℤ) = ((m : ℤ) + 1) * (m.choose k : ℤ) := by
      have h : (m + 1) * m.choose k = (m + 1).choose (k + 1) * (k + 1) :=
        Nat.add_one_mul_choose_eq m k
      have hz : (((m + 1) * m.choose k : ℕ) : ℤ) = (((m + 1).choose (k + 1) * (k + 1) : ℕ) : ℤ) := by
        rw [h]
      push_cast at hz
      linear_combination -hz
    have hp : (-1 : ℤ) ^ (m + 1 + (k + 1)) = (-1) ^ (m + k) := by
      have e : m + 1 + (k + 1) = m + k + 2 := by ring
      rw [e, pow_add]
      norm_num
    rw [hp]
    push_cast
    linear_combination ((-1 : ℤ) ^ (m + k) * d (k + 1)) * hc
  rw [hU1, e1, k1, k2]
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
  ring

theorem Srec (m : ℕ) : S (m + 2) = (2 * (m : ℤ) + 4) * S (m + 1) + (2 * (m : ℤ) + 2) * S m := by
  have c1 : S (m + 2) = U (m + 1) - S (m + 1) := claim1 (m + 1)
  have c2 := claim2 m
  have c0 := claim1 m
  linear_combination c1 + c2 - 2 * ((m : ℤ) + 1) * c0

theorem aS (j : ℕ) : a (j + 2) = S j := by
  have h : ¬ (j + 2 < 2) := by omega
  have e1 : j + 2 - 1 = j + 1 := rfl
  have e2 : j + 2 - 2 = j := rfl
  unfold a S d
  rw [if_neg h, e1, e2]
  apply Finset.sum_congr rfl
  intro k _
  have hp : (-1 : ℤ) ^ (j + 2 + k) = (-1) ^ (j + k) := by
    have e : j + 2 + k = j + k + 2 := by ring
    rw [e, pow_add]
    norm_num
  rw [hp]

theorem s0 : S 0 = 1 := by
  simp [S, d]

theorem s1 : S 1 = 2 := by
  simp [S, d, Finset.sum_range_succ, Nat.doubleFactorial]

end A165968Aux

open A165968Aux OMA.S_oeis_a165968 in
theorem OMA.solution : type_of% @OMA.S_oeis_a165968.main := by
  intro n hn
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · have e : n = 2 := by omega
    subst e
    have a3 : a (2 + 1) = S 1 := aS 1
    have a2 : a 2 = S 0 := aS 0
    rw [a3, a2, s0, s1]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have a4 : a (m + 3 + 1) = S (m + 2) := aS (m + 2)
    have a3 : a (m + 3) = S (m + 1) := aS (m + 1)
    have a2 : a (m + 3 - 1) = S m := aS m
    rw [a4, a3, a2]
    push_cast
    linear_combination Srec m
