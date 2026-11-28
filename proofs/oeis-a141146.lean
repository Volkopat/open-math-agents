import OMAStatements.S_oeis_a141146
import Mathlib

namespace OMA.S_oeis_a141146

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

noncomputable def Fq (m k : ℕ) : ℚ :=
  (Nat.choose m (2 * k) : ℚ) * (Nat.choose (2 * k) k : ℚ) * (Nat.choose (m + k) (k + 1) : ℚ) * ((2 : ℚ) ^ m / 4 ^ k)
noncomputable def GG (m k : ℕ) : ℚ :=
  6 * (k : ℚ) ^ 2 * ((k : ℚ) + 1) * ((m : ℚ) + 1) * (3 * (m : ℚ) + 4)
    / (((m : ℚ) + 2) * ((k : ℚ) + m + 1) * ((k : ℚ) + m + 2))
    * ((Nat.choose (m + 2) (2 * k) : ℚ) * (Nat.choose (2 * k) k : ℚ) * (Nat.choose (m + 2 + k) (k + 1) : ℚ)
      * ((2 : ℚ) ^ (m + 2) / 4 ^ k))

lemma cb_succ (k : ℕ) : (Nat.choose (2 * (k + 1)) (k + 1) : ℚ) = 2 * (2 * (k : ℚ) + 1) * (Nat.choose (2 * k) k : ℚ) / ((k : ℚ) + 1) := by
  have := Nat.succ_mul_centralBinom_succ k
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at this
  have h' : (((k + 1) * Nat.choose (2 * (k + 1)) (k + 1) : ℕ) : ℚ) = ((2 * (2 * k + 1) * Nat.choose (2 * k) k : ℕ) : ℚ) := by
    rw [this]
  push_cast at h'
  rw [eq_div_iff (by positivity)]; linarith

set_option maxRecDepth 100000 in
lemma term (m k : ℕ) :
    (8 * ((m : ℚ) + 1) ^ 2) * Fq m k + (7 * (m : ℚ) ^ 2 + 29 * m + 28) * Fq (m + 1) k
    + (-(((m : ℚ) + 1) * ((m : ℚ) + 4))) * Fq (m + 2) k = GG m (k + 1) - GG m k := by
  have r1 : (Nat.choose (m + 1) (2 * k) : ℚ) = (Nat.choose (m + 2) (2 * k) : ℚ) * (((m : ℚ) + 2) - (2 * k : ℕ)) / ((m : ℚ) + 2) := by
    have := ch_down (m + 1) (2 * k)
    rw [show m + 1 + 1 = m + 2 by ring] at this
    push_cast at this ⊢
    rw [this]; ring
  have r0 : (Nat.choose m (2 * k) : ℚ) = (Nat.choose (m + 1) (2 * k) : ℚ) * (((m : ℚ) + 1) - (2 * k : ℕ)) / ((m : ℚ) + 1) := ch_down m (2 * k)
  have y1 : (Nat.choose (m + 1 + k) (k + 1) : ℚ) = (Nat.choose (m + 2 + k) (k + 1) : ℚ) * (((m : ℚ) + 1)) / ((m : ℚ) + 2 + k) := by
    have := ch_down (m + 1 + k) (k + 1)
    rw [show m + 1 + k + 1 = m + 2 + k by ring] at this
    push_cast at this ⊢
    have e : ((m : ℚ) + 1 + k + 1 - (k + 1)) = (m : ℚ) + 1 := by ring
    rw [e] at this
    rw [this]; congr 1; ring
  have y0 : (Nat.choose (m + k) (k + 1) : ℚ) = (Nat.choose (m + 1 + k) (k + 1) : ℚ) * (m : ℚ) / ((m : ℚ) + 1 + k) := by
    have := ch_down (m + k) (k + 1)
    rw [show m + k + 1 = m + 1 + k by ring] at this
    push_cast at this ⊢
    have e : ((m : ℚ) + k + 1 - (k + 1)) = (m : ℚ) := by ring
    rw [e] at this
    rw [this]; congr 1; ring
  have n1 := ch_next (m + 2) (2 * k)
  have n2 := ch_next (m + 2) (2 * k + 1)
  have u1 := ch_up (m + 2 + k) (k + 1)
  have cb := cb_succ k
  have e1 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
  have e2 : m + 2 + (k + 1) = m + 2 + k + 1 := by ring
  have e3 : m + 1 + 1 = m + 2 := by ring
  have p1 : (2 : ℚ) ^ (m + 1) = 2 ^ m * 2 := by ring
  have p2 : (2 : ℚ) ^ (m + 2) = 2 ^ m * 4 := by ring
  have p3 : (4 : ℚ) ^ (k + 1) = 4 ^ k * 4 := by ring
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hk2 : ((k : ℚ) + 1 + 1) ≠ 0 := by positivity
  have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hm2 : ((m : ℚ) + 2) ≠ 0 := by positivity
  have hq1 : ((m : ℚ) + 2 + k) ≠ 0 := by positivity
  have hq2 : ((m : ℚ) + 1 + k) ≠ 0 := by positivity
  have hq3 : ((k : ℚ) + m + 1) ≠ 0 := by positivity
  have hq4 : ((k : ℚ) + m + 2) ≠ 0 := by positivity
  have hq5 : ((m : ℚ) + 2 + k + 1) ≠ 0 := by positivity
  have hq6 : ((k : ℚ) + 1 + m + 1) ≠ 0 := by positivity
  have hq7 : ((k : ℚ) + 1 + m + 2) ≠ 0 := by positivity
  have h2k1 : (2 * (k : ℚ) + 1) ≠ 0 := by positivity
  have h2k2 : (2 * (k : ℚ) + 1 + 1) ≠ 0 := by positivity
  have u1' : (Nat.choose (m + 2 + k + 1) (k + 1 + 1) : ℚ) = ((m : ℚ) + 2 + k + 1) * (Nat.choose (m + 2 + k) (k + 1) : ℚ) / ((k : ℚ) + 1 + 1) := by
    rw [eq_div_iff hk2]; push_cast at u1; linarith
  have hv : (4 : ℚ) ^ k ≠ 0 := by positivity
  unfold Fq GG
  rw [cb, e1, e2, e3, n2, n1, u1', r0, r1, y0, y1, p1, p2, p3]
  push_cast
  generalize (Nat.choose (m + 2) (2 * k) : ℚ) = x
  generalize (Nat.choose (2 * k) k : ℚ) = c
  generalize (Nat.choose (m + 2 + k) (k + 1) : ℚ) = y
  generalize ((2 : ℚ) ^ m) = u
  generalize hvv : ((4 : ℚ) ^ k) = v at hv ⊢
  field_simp
  ring

noncomputable def Aq (m : ℕ) : ℚ := ∑ k ∈ Finset.range (m + 1), Fq m k

lemma Fq_zero (m k : ℕ) (hk : m < 2 * k) : Fq m k = 0 := by
  unfold Fq; rw [Nat.choose_eq_zero_of_lt hk]; simp

lemma ext3 (m i : ℕ) (hi : i ≤ 2) :
    Aq (m + i) = ∑ k ∈ Finset.range (m + 3), Fq (m + i) k := by
  unfold Aq; symm
  apply sum_ext (f := fun k => Fq (m + i) k) (m + i) (m + 3) (by omega)
  intro k hk; exact Fq_zero _ _ (by omega)

lemma rec_A (m : ℕ) :
    (8 * ((m : ℚ) + 1) ^ 2) * Aq m + (7 * (m : ℚ) ^ 2 + 29 * m + 28) * Aq (m + 1)
    + (-(((m : ℚ) + 1) * ((m : ℚ) + 4))) * Aq (m + 2) = 0 := by
  have s0 := ext3 m 0 (by omega)
  simp only [Nat.add_zero] at s0
  rw [s0, ext3 m 1 (by omega), ext3 m 2 (by omega)]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun k _ => term m k)]
  rw [Finset.sum_range_sub (fun k => GG m k)]
  have h0 : GG m 0 = 0 := by simp [GG]
  have h1 : GG m (m + 3) = 0 := by
    rw [GG, Nat.choose_eq_zero_of_lt (show m + 2 < 2 * (m + 3) by omega)]; simp
  rw [h0, h1]; ring

lemma a_cast (m : ℕ) : (a (m + 1) : ℚ) = Aq m := by
  unfold a
  push_cast
  try simp only [Nat.add_sub_cancel]
  set f : ℕ → ℚ := fun k => (Nat.choose m (2 * k) : ℚ) * (Nat.choose (2 * k) k : ℚ) * (Nat.choose (m + k) (k + 1) : ℚ) * (2 : ℚ) ^ (m - 2 * k) with hf
  have h1 : ∑ k ∈ Finset.range (m + 1), f k = ∑ k ∈ Finset.range ((m + 1) / 2 + 1), f k :=
    sum_ext (f := f) ((m + 1) / 2) (m + 1) (by omega)
      (fun k hk => by simp only [hf]; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)
  have h2 : ∑ k ∈ Finset.range ((m + 1) / 2 + 1), f k = ∑ k ∈ Finset.range (m + 1), f k := h1.symm
  show ∑ k ∈ Finset.range ((m + 1) / 2 + 1), f k = Aq m
  rw [h2]
  unfold Aq
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : 2 * k ≤ m
  · obtain ⟨d, hd⟩ : ∃ d, m = 2 * k + d := ⟨m - 2 * k, by omega⟩
    simp only [hf, Fq]
    rw [show m - 2 * k = d by omega, hd, pow_add]
    have : (4 : ℚ) ^ k = (2 : ℚ) ^ (2 * k) := by rw [pow_mul]; norm_num
    rw [this]
    have h2k : (2 : ℚ) ^ (2 * k) ≠ 0 := by positivity
    field_simp
  · have hlt : m < 2 * k := by omega
    simp only [hf]
    rw [Nat.choose_eq_zero_of_lt hlt, Fq_zero m k hlt]; simp

end OMA.S_oeis_a141146

theorem OMA.solution : type_of% @OMA.S_oeis_a141146.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := OMA.S_oeis_a141146.rec_A m
  rw [show m + 3 - 1 = m + 1 + 1 from rfl, show m + 3 - 2 = m + 1 from rfl]
  have c2 := OMA.S_oeis_a141146.a_cast (m + 1)
  have c1 := OMA.S_oeis_a141146.a_cast m
  have c0 : (OMA.S_oeis_a141146.a (m + 3) : ℚ) = OMA.S_oeis_a141146.Aq (m + 2) := OMA.S_oeis_a141146.a_cast (m + 2)
  have : (((-(((m + 3 : ℕ) : ℤ) + 1) * (((m + 3 : ℕ) : ℤ) - 2)) * OMA.S_oeis_a141146.a (m + 3)
      + (7 * ((m + 3 : ℕ) : ℤ) ^ 2 - 13 * ((m + 3 : ℕ) : ℤ) + 4) * OMA.S_oeis_a141146.a (m + 1 + 1)
      + 8 * (((m + 3 : ℕ) : ℤ) - 2) ^ 2 * OMA.S_oeis_a141146.a (m + 1) : ℤ) : ℚ) = 0 := by
    push_cast
    rw [c0, c2, c1]
    linear_combination h
  have e : (-(((m + 3 : ℕ) : ℤ) + 1) * (((m + 3 : ℕ) : ℤ) - 2)) * OMA.S_oeis_a141146.a (m + 3)
      + (7 * ((m + 3 : ℕ) : ℤ) ^ 2 - 13 * ((m + 3 : ℕ) : ℤ) + 4) * OMA.S_oeis_a141146.a (m + 1 + 1)
      + 8 * (((m + 3 : ℕ) : ℤ) - 2) ^ 2 * OMA.S_oeis_a141146.a (m + 1) = 0 := by exact_mod_cast this
  exact e
