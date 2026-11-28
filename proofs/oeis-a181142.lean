import OMAStatements.S_oeis_a181142
import Mathlib

namespace OMA.S_oeis_a181142

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

noncomputable def Fq (m k : ℕ) : ℚ := (Nat.choose m k : ℚ) * (-2) ^ k * ((2 * (m + 1) - k).factorial : ℚ)
def Pp (m k : ℚ) : ℚ := k ^ 2 * (m + 1) ^ 2 + 2 * k ^ 2 * (m + 1) + k ^ 2 - 2 * k * (m + 1) ^ 3 - 5 * k * (m + 1) ^ 2
  - 6 * k * (m + 1) - 5 * k - 4 * (m + 1) ^ 3 - 12 * (m + 1) ^ 2 - 10 * (m + 1) - 2
noncomputable def GG (m k : ℕ) : ℚ :=
  -((k : ℚ) * Pp m k * (Nat.choose (m + 2) k : ℚ) * (-2) ^ k * ((2 * m + 6 - k).factorial : ℚ))
    / (((m : ℚ) + 2) * (2 * (m : ℚ) + 6 - k) * (2 * (m : ℚ) + 5 - k) * (2 * (m : ℚ) + 4 - k))

lemma fsucc (N : ℕ) : ((N + 1).factorial : ℚ) = ((N : ℚ) + 1) * (N.factorial : ℚ) := by
  rw [Nat.factorial_succ]; push_cast; ring

set_option maxRecDepth 100000 in
lemma term (m k : ℕ) (hk : k ≤ m + 2) :
    (4 * ((m : ℚ) + 1) * ((m : ℚ) + 3) ^ 2) * Fq m k
    + (2 * (2 * (m : ℚ) + 5) * ((m : ℚ) ^ 2 + 5 * m + 5)) * Fq (m + 1) k
    + (-((m : ℚ) + 2)) * Fq (m + 2) k = GG m (k + 1) - GG m k := by
  obtain ⟨s, hs⟩ : ∃ s, 2 * m + 2 = s + k := ⟨2 * m + 2 - k, by omega⟩
  have hs' : (s : ℚ) = 2 * (m : ℚ) + 2 - k := by
    have : ((2 * m + 2 : ℕ) : ℚ) = ((s + k : ℕ) : ℚ) := by rw [hs]
    push_cast at this; linarith
  have hkq : (k : ℚ) ≤ (m : ℚ) + 2 := by exact_mod_cast hk
  have f0 : 2 * (m + 1) - k = s := by omega
  have f1 : 2 * (m + 1 + 1) - k = s + 2 := by omega
  have f2 : 2 * (m + 2 + 1) - k = s + 4 := by omega
  have g0 : 2 * m + 6 - k = s + 4 := by omega
  have g1 : 2 * m + 6 - (k + 1) = s + 3 := by omega
  have e1 := ch_down (m + 1) k
  have e0 := ch_down m k
  have e2 := ch_next (m + 2) k
  rw [show m + 1 + 1 = m + 2 by ring] at e1
  push_cast at e1
  unfold Fq GG Pp
  rw [f0, f1, f2, g0, g1, show m + 1 + 1 = m + 2 by ring]
  have w2 := fsucc (s + 1)
  have w3 := fsucc (s + 2)
  have w4 := fsucc (s + 3)
  have w1 := fsucc s
  rw [show s + 1 + 1 = s + 2 by ring] at w2
  rw [show s + 2 + 1 = s + 3 by ring] at w3
  rw [show s + 3 + 1 = s + 4 by ring] at w4
  push_cast at w1 w2 w3 w4
  have d1 : (2 * (m : ℚ) + 6 - k) = (s : ℚ) + 4 := by rw [hs']; ring
  have d2 : (2 * (m : ℚ) + 5 - k) = (s : ℚ) + 3 := by rw [hs']; ring
  have d3 : (2 * (m : ℚ) + 4 - k) = (s : ℚ) + 2 := by rw [hs']; ring
  have d4 : (2 * (m : ℚ) + 6 - ((k : ℚ) + 1)) = (s : ℚ) + 3 := by rw [hs']; ring
  have d5 : (2 * (m : ℚ) + 5 - ((k : ℚ) + 1)) = (s : ℚ) + 2 := by rw [hs']; ring
  have d6 : (2 * (m : ℚ) + 4 - ((k : ℚ) + 1)) = (s : ℚ) + 1 := by rw [hs']; ring
  have hs1 : (s : ℚ) + 1 ≠ 0 := by positivity
  have hs2 : (s : ℚ) + 2 ≠ 0 := by positivity
  have hs3 : (s : ℚ) + 3 ≠ 0 := by positivity
  have hs4 : (s : ℚ) + 4 ≠ 0 := by positivity
  have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hm2 : ((m : ℚ) + 2) ≠ 0 := by positivity
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  rw [e0, e1, e2, w4, w3, w2, w1, pow_succ (-2 : ℚ) k]
  push_cast
  simp only [d1, d2, d3, d4, d5, d6]
  generalize (Nat.choose (m + 2) k : ℚ) = x
  generalize ((-2 : ℚ) ^ k) = t
  generalize (s.factorial : ℚ) = w
  field_simp
  simp only [hs']
  ring

noncomputable def Aq (m : ℕ) : ℚ := ∑ k ∈ Finset.range (m + 1), Fq m k

lemma ext3 (m i : ℕ) (hi : i ≤ 2) :
    Aq (m + i) = ∑ k ∈ Finset.range (m + 3), Fq (m + i) k := by
  unfold Aq; symm
  apply sum_ext (f := fun k => Fq (m + i) k) (m + i) (m + 3) (by omega)
  intro k hk; simp [Fq, Nat.choose_eq_zero_of_lt hk]

lemma rec_A (m : ℕ) :
    (4 * ((m : ℚ) + 1) * ((m : ℚ) + 3) ^ 2) * Aq m
    + (2 * (2 * (m : ℚ) + 5) * ((m : ℚ) ^ 2 + 5 * m + 5)) * Aq (m + 1)
    + (-((m : ℚ) + 2)) * Aq (m + 2) = 0 := by
  have s0 := ext3 m 0 (by omega)
  simp only [Nat.add_zero] at s0
  rw [s0, ext3 m 1 (by omega), ext3 m 2 (by omega)]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun k hk => term m k (by have := Finset.mem_range.mp hk; omega))]
  rw [Finset.sum_range_sub (fun k => GG m k)]
  have h0 : GG m 0 = 0 := by simp [GG]
  have h1 : GG m (m + 3) = 0 := by
    simp [GG]
  rw [h0, h1]; ring

lemma a_cast (m : ℕ) : (a (m + 1) : ℚ) = Aq m := by
  unfold a Aq Fq
  push_cast
  simp

end OMA.S_oeis_a181142

theorem OMA.solution : type_of% @OMA.S_oeis_a181142.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := OMA.S_oeis_a181142.rec_A m
  rw [show m + 3 - 1 = m + 1 + 1 from rfl, show m + 3 - 2 = m + 1 from rfl]
  have c2 := OMA.S_oeis_a181142.a_cast (m + 1)
  have c1 := OMA.S_oeis_a181142.a_cast m
  have c0 : (OMA.S_oeis_a181142.a (m + 3) : ℚ) = OMA.S_oeis_a181142.Aq (m + 2) := OMA.S_oeis_a181142.a_cast (m + 2)
  have : (((-((m + 3 : ℕ) : ℤ) + 1) * OMA.S_oeis_a181142.a (m + 3)
      + 2 * (2 * ((m + 3 : ℕ) : ℤ) - 1) * (((m + 3 : ℕ) : ℤ) ^ 2 - ((m + 3 : ℕ) : ℤ) - 1) * OMA.S_oeis_a181142.a (m + 1 + 1)
      + 4 * ((m + 3 : ℕ) : ℤ) ^ 2 * (((m + 3 : ℕ) : ℤ) - 2) * OMA.S_oeis_a181142.a (m + 1) : ℤ) : ℚ) = 0 := by
    push_cast
    rw [c0, c2, c1]
    linear_combination h
  exact_mod_cast this
