import OMAStatements.S_oeis_a049608
import Mathlib

namespace OMA.S_oeis_a049608

/- Ratio lemmas for creative-telescoping term proofs (paste inside the helper namespace; needs `import Mathlib`).
   All in ℚ.  Atoms: x = C(N,k).  Typical use: express every binomial of the sum as (rational function)*x, then field_simp; ring. -/
lemma ch_succ (N k : ℕ) (hk : k ≤ N + 1) :   -- C(N,k)*(N+1) = C(N+1,k)*(N+1-k)
    (Nat.choose N k : ℚ) * ((N : ℚ) + 1) = Nat.choose (N + 1) k * (((N : ℚ) + 1) - k) := by
  have h := Nat.choose_mul_succ_eq N k
  have h' : ((Nat.choose N k * (N + 1) : ℕ) : ℚ) = ((Nat.choose (N + 1) k * (N + 1 - k) : ℕ) : ℚ) := by rw [h]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk] at h'
  push_cast at h'
  exact h'

lemma ch_up (N k : ℕ) :                      -- C(N+1,k+1)*(k+1) = (N+1)*C(N,k)
    ((Nat.choose (N + 1) (k + 1) : ℚ)) * ((k : ℚ) + 1) = ((N : ℚ) + 1) * Nat.choose N k := by
  have h := Nat.add_one_mul_choose_eq N k
  have h' : (((N + 1) * Nat.choose N k : ℕ) : ℚ) = ((Nat.choose (N + 1) (k + 1) * (k + 1) : ℕ) : ℚ) := by rw [h]
  push_cast at h'
  linarith

lemma ch_right (N k : ℕ) (hk : k ≤ N) :      -- C(N,k+1)*(k+1) = (N-k)*C(N,k)
    (Nat.choose N (k + 1) : ℚ) * ((k : ℚ) + 1) = ((N : ℚ) - k) * (Nat.choose N k : ℚ) := by
  have h := Nat.choose_succ_right_eq N k
  have h' : ((Nat.choose N (k + 1) * (k + 1) : ℕ) : ℚ) = ((Nat.choose N k * (N - k) : ℕ) : ℚ) := by rw [h]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk] at h'
  push_cast at h'
  linarith

/-- C(N,k) = C(N+1,k)*(N+1-k)/(N+1), for all k (both sides vanish for k > N+1). -/
lemma ch_down (N k : ℕ) :
    (Nat.choose N k : ℚ) = (Nat.choose (N + 1) k : ℚ) * (((N : ℚ) + 1) - k) / ((N : ℚ) + 1) := by
  rw [eq_div_iff (by positivity)]
  rcases Nat.lt_or_ge (N + 1) k with h | h
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp
  · have := ch_succ N k h
    linarith

/-- C(N,k+1) = (N-k)*C(N,k)/(k+1), for all k. -/
lemma ch_next (N k : ℕ) :
    (Nat.choose N (k + 1) : ℚ) = ((N : ℚ) - k) * (Nat.choose N k : ℚ) / ((k : ℚ) + 1) := by
  rw [eq_div_iff (by positivity)]
  rcases Nat.lt_or_ge N k with h | h
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp
  · exact ch_right N k h

/-- C(N+1,k) = C(N,k)*(N+1)/(N+1-k) for k ≤ N. -/
lemma ch_upN (N k : ℕ) (hk : k ≤ N) :
    (Nat.choose (N + 1) k : ℚ) = (Nat.choose N k : ℚ) * ((N : ℚ) + 1) / (((N : ℚ) + 1) - k) := by
  have : ((N : ℚ) + 1) - k ≠ 0 := by
    have : (k : ℚ) ≤ N := by exact_mod_cast hk
    linarith
  rw [eq_div_iff this]
  have := ch_succ N k (by omega)
  linarith

/-- support extension: sum over range N of a term that vanishes for k > n equals the sum over range (n+1). -/
lemma sum_ext {f : ℕ → ℚ} (n N : ℕ) (hN : n + 1 ≤ N) (hf : ∀ k, n < k → f k = 0) :
    ∑ k ∈ Finset.range N, f k = ∑ k ∈ Finset.range (n + 1), f k := by
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hN)
  intro k _ hk
  exact hf k (by simpa using hk)

noncomputable def Fq (m k : ℕ) : ℚ := (Nat.choose (m + 3 + k) k : ℚ) * (Nat.choose m k : ℚ)
noncomputable def GG (m k : ℕ) : ℚ :=
  (k : ℚ) ^ 2 * (((m : ℚ) + 3) * ((m : ℚ) + 5) * (2 * (m : ℚ) + 5) * (2 * (m : ℚ) + 7))
    * ((Nat.choose (m + 5 + k) k : ℚ) * (Nat.choose (m + 2) k : ℚ))
    / (((m : ℚ) + 2) * ((k : ℚ) + m + 4) * ((k : ℚ) + m + 5))

set_option maxRecDepth 100000 in
lemma term (m k : ℕ) :
    (-(((m : ℚ) + 1) * ((m : ℚ) + 4) * (2 * (m : ℚ) + 7)) / 2) * Fq m k
    + (6 * ((m : ℚ) + 2) * ((m : ℚ) + 3) * ((m : ℚ) + 4)) * Fq (m + 1) k
    + (-(((m : ℚ) + 2) * ((m : ℚ) + 5) * (2 * (m : ℚ) + 5)) / 2) * Fq (m + 2) k
    = GG m (k + 1) - GG m k := by
  have a1 := ch_down (m + 4 + k) k
  have a2 := ch_down (m + 3 + k) k
  have b1 := ch_down (m + 1) k
  have b0 := ch_down m k
  rw [show m + 4 + k + 1 = m + 5 + k by ring] at a1
  rw [show m + 3 + k + 1 = m + 4 + k by ring] at a2
  rw [show m + 1 + 1 = m + 2 by ring] at b1
  have u1 := ch_up (m + 5 + k) k
  have n1 := ch_next (m + 2) k
  have e1 : m + 1 + 3 + k = m + 4 + k := by ring
  have e2 : m + 2 + 3 + k = m + 5 + k := by ring
  have e3 : m + 5 + (k + 1) = m + 5 + k + 1 := by ring
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  have h1 : ((m : ℚ) + 5 + k) ≠ 0 := by positivity
  have h2 : ((m : ℚ) + 4 + k) ≠ 0 := by positivity
  have h3 : ((m : ℚ) + 6 + k) ≠ 0 := by positivity
  have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hm2 : ((m : ℚ) + 2) ≠ 0 := by positivity
  have hq : ((k : ℚ) + m + 4) ≠ 0 := by positivity
  have hq' : ((k : ℚ) + m + 5) ≠ 0 := by positivity
  have hq'' : ((k : ℚ) + 1 + m + 4) ≠ 0 := by positivity
  have hq3 : ((k : ℚ) + 1 + m + 5) ≠ 0 := by positivity
  have u1' : (Nat.choose (m + 5 + k + 1) (k + 1) : ℚ) = ((m : ℚ) + 5 + k + 1) * (Nat.choose (m + 5 + k) k : ℚ) / ((k : ℚ) + 1) := by
    rw [eq_div_iff hk]; push_cast at u1; linarith
  push_cast at a1 a2 n1
  unfold Fq GG
  rw [e1, e2, e3, u1', n1, b0, b1, a2, a1]
  push_cast
  generalize (Nat.choose (m + 5 + k) k : ℚ) = y
  generalize (Nat.choose (m + 2) k : ℚ) = z
  field_simp
  ring

noncomputable def Sq (m : ℕ) : ℚ := ∑ k ∈ Finset.range (m + 1), Fq m k

lemma ext3 (m i : ℕ) (hi : i ≤ 2) :
    Sq (m + i) = ∑ k ∈ Finset.range (m + 3), Fq (m + i) k := by
  unfold Sq; symm
  apply sum_ext (f := fun k => Fq (m + i) k) (m + i) (m + 3) (by omega)
  intro k hk; simp [Fq, Nat.choose_eq_zero_of_lt hk]

lemma rec_S (m : ℕ) :
    (-(((m : ℚ) + 1) * ((m : ℚ) + 4) * (2 * (m : ℚ) + 7)) / 2) * Sq m
    + (6 * ((m : ℚ) + 2) * ((m : ℚ) + 3) * ((m : ℚ) + 4)) * Sq (m + 1)
    + (-(((m : ℚ) + 2) * ((m : ℚ) + 5) * (2 * (m : ℚ) + 5)) / 2) * Sq (m + 2) = 0 := by
  have s0 := ext3 m 0 (by omega)
  simp only [Nat.add_zero] at s0
  rw [s0, ext3 m 1 (by omega), ext3 m 2 (by omega)]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun k _ => term m k)]
  rw [Finset.sum_range_sub (fun k => GG m k)]
  have h0 : GG m 0 = 0 := by simp [GG]
  have h1 : GG m (m + 3) = 0 := by
    simp [GG, Nat.choose_eq_zero_of_lt (show m + 2 < m + 3 by omega)]
  rw [h0, h1]; ring

lemma a_cast (m : ℕ) : (a (m + 1) : ℚ) = Sq m := by
  unfold a T Sq Fq
  push_cast
  simp

end OMA.S_oeis_a049608

theorem OMA.solution : type_of% @OMA.S_oeis_a049608.main := by
  intro n hn
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    norm_num [OMA.S_oeis_a049608.a, OMA.S_oeis_a049608.T, Finset.sum_range_succ, Nat.choose]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have h := OMA.S_oeis_a049608.rec_S m
    rw [show m + 3 - 1 = m + 1 + 1 from rfl, show m + 3 - 2 = m + 1 from rfl]
    have c0 := OMA.S_oeis_a049608.a_cast (m + 2)
    have c1 := OMA.S_oeis_a049608.a_cast (m + 1)
    have c2 := OMA.S_oeis_a049608.a_cast m
    have : (((((m + 3 : ℕ) : ℤ) - 1) * (2 * ((m + 3 : ℕ) : ℤ) - 1) * (((m + 3 : ℕ) : ℤ) + 2) * OMA.S_oeis_a049608.a (m + 3)
        - 12 * ((m + 3 : ℕ) : ℤ) * (((m + 3 : ℕ) : ℤ) - 1) * (((m + 3 : ℕ) : ℤ) + 1) * OMA.S_oeis_a049608.a (m + 1 + 1)
        + (((m + 3 : ℕ) : ℤ) - 2) * (2 * ((m + 3 : ℕ) : ℤ) + 1) * (((m + 3 : ℕ) : ℤ) + 1) * OMA.S_oeis_a049608.a (m + 1) : ℤ) : ℚ) = 0 := by
      push_cast
      rw [show m + 3 = m + 2 + 1 from rfl] at c0 ⊢
      rw [c0, c1, c2]
      push_cast
      linear_combination (-2 : ℚ) * h
    exact_mod_cast this
