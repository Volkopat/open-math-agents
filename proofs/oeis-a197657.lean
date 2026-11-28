import OMAStatements.S_oeis_a197657
import Mathlib

namespace OMA.S_oeis_a197657

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

/- Franel numbers: f(n) = Σ_k C(n,k)^3 satisfies 8(n+1)^2 f(n) + (7n^2+21n+16) f(n+1) - (n+2)^2 f(n+2) = 0.
   Certificate found by zeil.py (F = binomial(n,k)^3, order 2).  Needs ratio_lemmas.lean above it. -/
def PF (m k : ℚ) : ℚ := 4 * k ^ 3 - 18 * k ^ 2 * m - 30 * k ^ 2 + 27 * k * m ^ 2 + 93 * k * m + 78 * k
  - 14 * m ^ 3 - 74 * m ^ 2 - 128 * m - 72
noncomputable def GF (m k : ℕ) : ℚ :=
  -((k : ℚ) ^ 3 * PF m k * (Nat.choose (m + 2) k : ℚ) ^ 3) / (((m : ℚ) + 1) * ((m : ℚ) + 2) ^ 3)

lemma franel_term (m k : ℕ) :
    8 * ((m : ℚ) + 1) ^ 2 * (Nat.choose m k : ℚ) ^ 3
    + (7 * (m : ℚ) ^ 2 + 21 * m + 16) * (Nat.choose (m + 1) k : ℚ) ^ 3
    - ((m : ℚ) + 2) ^ 2 * (Nat.choose (m + 2) k : ℚ) ^ 3 = GF m (k + 1) - GF m k := by
  have e1 := ch_down (m + 1) k
  have e0 := ch_down m k
  have e2 := ch_next (m + 2) k
  push_cast at e1 e2
  have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hm2 : ((m : ℚ) + 2) ≠ 0 := by positivity
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  unfold GF PF
  rw [e0, e1, e2]
  push_cast
  field_simp
  ring

noncomputable def fq (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℚ) ^ 3

lemma franel_rec (m : ℕ) :
    8 * ((m : ℚ) + 1) ^ 2 * fq m + (7 * (m : ℚ) ^ 2 + 21 * m + 16) * fq (m + 1)
      - ((m : ℚ) + 2) ^ 2 * fq (m + 2) = 0 := by
  have h : ∀ n : ℕ, fq n = ∑ k ∈ Finset.range (m + 3), (Nat.choose n k : ℚ) ^ 3 ∨ n > m + 2 := by
    intro n; by_cases hn : n ≤ m + 2
    · left; unfold fq; symm
      apply sum_ext (f := fun k => (Nat.choose n k : ℚ) ^ 3) n (m + 3) (by omega)
      intro k hk; simp [Nat.choose_eq_zero_of_lt hk]
    · right; omega
  have s0 : fq m = ∑ k ∈ Finset.range (m + 3), (Nat.choose m k : ℚ) ^ 3 := (h m).resolve_right (by omega)
  have s1 : fq (m + 1) = ∑ k ∈ Finset.range (m + 3), (Nat.choose (m + 1) k : ℚ) ^ 3 := (h (m + 1)).resolve_right (by omega)
  have s2 : fq (m + 2) = ∑ k ∈ Finset.range (m + 3), (Nat.choose (m + 2) k : ℚ) ^ 3 := (h (m + 2)).resolve_right (by omega)
  rw [s0, s1, s2, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun k _ => franel_term m k)]
  rw [Finset.sum_range_sub (fun k => GF m k)]
  have h0 : GF m 0 = 0 := by simp [GF]
  have h1 : GF m (m + 3) = 0 := by
    simp [GF, Nat.choose_eq_zero_of_lt (show m + 2 < m + 3 by omega)]
  rw [h0, h1]; ring

lemma franel_cast (n : ℕ) : (franel n : ℚ) = fq n := by
  unfold franel fq; push_cast; rfl

lemma rec_q (m : ℕ) :
    (((m + 3 : ℕ) : ℚ) + 1) ^ 2 * a (m + 3) - 3 * (((m + 3 : ℕ) : ℚ) + 1) * (2 * ((m + 3 : ℕ) : ℚ) + 1) * a (m + 2)
      - 3 * ((m + 3 : ℕ) : ℚ) * (5 * ((m + 3 : ℕ) : ℚ) - 7) * a (m + 1)
      - 8 * (((m + 3 : ℕ) : ℚ) - 2) ^ 2 * a m = 0 := by
  have r0 := franel_rec m
  have r1 := franel_rec (m + 1)
  have r2 := franel_rec (m + 2)
  have hm2 : ((m : ℚ) + 2) ≠ 0 := by positivity
  have hm3 : ((m : ℚ) + 3) ≠ 0 := by positivity
  have hm4 : ((m : ℚ) + 4) ≠ 0 := by positivity
  have hm5 : ((m : ℚ) + 5) ≠ 0 := by positivity
  push_cast at r1 r2 ⊢
  have f2 : fq (m + 2) = (8 * ((m : ℚ) + 1) ^ 2 * fq m + (7 * (m : ℚ) ^ 2 + 21 * m + 16) * fq (m + 1)) / ((m : ℚ) + 2) ^ 2 := by
    rw [eq_div_iff (by positivity)]; linarith
  have f3 : fq (m + 3) = (8 * ((m : ℚ) + 1 + 1) ^ 2 * fq (m + 1) + (7 * ((m : ℚ) + 1) ^ 2 + 21 * ((m : ℚ) + 1) + 16) * fq (m + 2)) / ((m : ℚ) + 1 + 2) ^ 2 := by
    rw [eq_div_iff (by positivity)]
    have : fq (m + 1 + 2) = fq (m + 3) := rfl
    rw [← this]; linarith
  have f4 : fq (m + 4) = (8 * ((m : ℚ) + 2 + 1) ^ 2 * fq (m + 2) + (7 * ((m : ℚ) + 2) ^ 2 + 21 * ((m : ℚ) + 2) + 16) * fq (m + 3)) / ((m : ℚ) + 2 + 2) ^ 2 := by
    rw [eq_div_iff (by positivity)]
    have : fq (m + 2 + 2) = fq (m + 4) := rfl
    rw [← this]; linarith
  unfold a
  simp only [franel_cast]
  have e1 : m + 3 + 1 = m + 4 := rfl
  rw [e1]
  simp only [show m + 2 + 1 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl, franel_cast]
  push_cast
  rw [f4, f3, f2]
  field_simp
  ring

end OMA.S_oeis_a197657

theorem OMA.solution : type_of% @OMA.S_oeis_a197657.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := OMA.S_oeis_a197657.rec_q m
  rw [show m + 3 - 1 = m + 2 from rfl, show m + 3 - 2 = m + 1 from rfl, show m + 3 - 3 = m from rfl]
  exact h
