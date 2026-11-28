import OMAStatements.S_oeis_a027179
import Mathlib

namespace OMA.S_oeis_a027179

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

lemma cb_succ (k : ℕ) : (Nat.choose (2 * (k + 1)) (k + 1) : ℚ) = 2 * (2 * (k : ℚ) + 1) * (Nat.choose (2 * k) k : ℚ) / ((k : ℚ) + 1) := by
  have := Nat.succ_mul_centralBinom_succ k
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at this
  have h' : (((k + 1) * Nat.choose (2 * (k + 1)) (k + 1) : ℕ) : ℚ) = ((2 * (2 * k + 1) * Nat.choose (2 * k) k : ℕ) : ℚ) := by
    rw [this]
  push_cast at h'
  rw [eq_div_iff (by positivity)]; linarith

noncomputable def Sm (N K : ℕ) : ℚ := ∑ i ∈ Finset.range (K + 1), (Nat.choose N i : ℚ)

lemma psum (N K : ℕ) : Sm (N + 1) K = 2 * Sm N K - (Nat.choose N K : ℚ) := by
  induction K with
  | zero => simp [Sm]; ring
  | succ K ih =>
    simp only [Sm] at ih ⊢
    rw [Finset.sum_range_succ (fun i => (Nat.choose (N + 1) i : ℚ)) (K + 1), ih,
      Finset.sum_range_succ (fun i => (Nat.choose N i : ℚ)) (K + 1), Nat.choose_succ_succ]
    push_cast; ring

lemma half (p : ℕ) : Sm (2 * p + 1) p = 4 ^ p := by
  have := Nat.sum_range_choose_halfway p
  unfold Sm; exact_mod_cast this

lemma hc (p : ℕ) : 2 * (Nat.choose (2 * p + 1) (p + 1) : ℚ) = (Nat.choose (2 * p + 2) (p + 1) : ℚ) := by
  have h1 := Nat.choose_succ_succ' (2 * p + 1) p
  have h2 := Nat.choose_symm_half p
  rw [show 2 * p + 1 + 1 = 2 * p + 2 by ring] at h1
  rw [h1, ← h2]; push_cast; ring

lemma sm_e1 (p : ℕ) : Sm (2 * p + 1) (p + 1) = 4 ^ p + (Nat.choose (2 * p + 1) (p + 1) : ℚ) := by
  unfold Sm
  rw [Finset.sum_range_succ]
  have := half p
  unfold Sm at this
  rw [this]

lemma sm_e2 (p : ℕ) : Sm (2 * p + 2) (p + 1) = 2 * 4 ^ p + (Nat.choose (2 * p + 1) (p + 1) : ℚ) := by
  have h := psum (2 * p + 1) (p + 1)
  rw [show 2 * p + 1 + 1 = 2 * p + 2 by ring] at h
  rw [h, sm_e1]; ring

lemma sm_e3 (p : ℕ) : Sm (2 * p) p = (4 ^ p + (Nat.choose (2 * p) p : ℚ)) / 2 := by
  have h := psum (2 * p) p
  rw [half p] at h
  linarith

lemma sh (N K : ℕ) : ∑ k ∈ Finset.range (K + 1), (Nat.choose N (k + 1) : ℚ) = Sm N (K + 1) - 1 := by
  unfold Sm
  rw [Finset.sum_range_succ' (fun i => (Nat.choose N i : ℚ)) (K + 1)]
  simp

lemma a_formula (n : ℕ) : (a n : ℚ) = Sm (n + 2) (n / 2 + 1) + Sm (n + 1) (n / 2) + Sm (n + 1) (n / 2 + 1)
    + Sm n (n / 2) - 4 * ((n / 2 : ℕ) + 1) - 2 := by
  have t00 : t 0 0 = 5 := by decide
  unfold a T
  rw [t00]
  push_cast
  simp only [t]
  push_cast
  have e : ∀ k : ℕ, ((Nat.choose (n + 2) (k + 1) : ℚ) + (Nat.choose (n + 1) k : ℚ) + (Nat.choose (n + 1) (k + 1) : ℚ) + (Nat.choose n k : ℚ) - 5 + 1)
      = (Nat.choose (n + 2) (k + 1) : ℚ) + (Nat.choose (n + 1) k : ℚ) + (Nat.choose (n + 1) (k + 1) : ℚ) + (Nat.choose n k : ℚ) - 4 := by
    intro k; ring
  simp only [e]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, sh, sh]
  simp [Sm]
  ring

lemma aE (p : ℕ) : (a (2 * p) : ℚ) = 9 / 2 * 4 ^ p + (Nat.choose (2 * (p + 1)) (p + 1) : ℚ)
    + (Nat.choose (2 * p) p : ℚ) / 2 - 2 - 4 * ((p : ℚ) + 1) := by
  have h := a_formula (2 * p)
  have e : 2 * p / 2 = p := by omega
  rw [e] at h
  rw [h, sm_e2, sm_e1, sm_e3, half]
  have := hc p
  rw [show 2 * (p + 1) = 2 * p + 2 by ring, ← this]
  have h2 : (2 * p + 1 : ℕ) = 2 * p + 1 := rfl
  rw [show 2 * p + 2 = 2 * p + 1 + 1 by ring] at *
  push_cast
  ring

lemma aO (p : ℕ) : (a (2 * p + 1) : ℚ) = 9 * 4 ^ p - 4 * (p : ℚ) - 6 := by
  have h := a_formula (2 * p + 1)
  have e : (2 * p + 1) / 2 = p := by omega
  rw [e] at h
  have s1 : Sm (2 * p + 1 + 2) (p + 1) = 4 ^ (p + 1) := by
    have := half (p + 1)
    rw [show 2 * (p + 1) + 1 = 2 * p + 1 + 2 by ring] at this
    exact this
  have s2 : Sm (2 * p + 1 + 1) (p + 1) = 2 * 4 ^ p + (Nat.choose (2 * p + 1) (p + 1) : ℚ) := by
    rw [show 2 * p + 1 + 1 = 2 * p + 2 by ring]; exact sm_e2 p
  have s3 : Sm (2 * p + 1 + 1) p = 2 * 4 ^ p - (Nat.choose (2 * p + 1) (p + 1) : ℚ) := by
    have : Sm (2 * p + 2) (p + 1) = Sm (2 * p + 2) p + (Nat.choose (2 * p + 2) (p + 1) : ℚ) := by
      unfold Sm; rw [Finset.sum_range_succ]
    have h3 := sm_e2 p
    have h4 := hc p
    rw [show 2 * p + 1 + 1 = 2 * p + 2 by ring]
    linarith
  rw [h, s1, s2, s3, half]
  push_cast
  ring

end OMA.S_oeis_a027179

theorem OMA.solution : type_of% @OMA.S_oeis_a027179.main := by
  intro n hn
  have cbs : ∀ j : ℕ, (Nat.choose (2 * (j + 1)) (j + 1) : ℚ) = 2 * (2 * (j : ℚ) + 1) * (Nat.choose (2 * j) j : ℚ) / ((j : ℚ) + 1) :=
    fun j => OMA.S_oeis_a027179.cb_succ j
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨q, rfl⟩ : ∃ q, k = q + 3 := ⟨k - 3, by omega⟩
    rw [show 2 * (q + 3) - 1 = 2 * (q + 2) + 1 by omega, show 2 * (q + 3) - 2 = 2 * (q + 2) by omega,
      show 2 * (q + 3) - 3 = 2 * (q + 1) + 1 by omega, show 2 * (q + 3) - 4 = 2 * (q + 1) by omega,
      show 2 * (q + 3) - 5 = 2 * q + 1 by omega, show 2 * (q + 3) - 6 = 2 * q by omega]
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [OMA.S_oeis_a027179.aE (q + 3), OMA.S_oeis_a027179.aO (q + 2), OMA.S_oeis_a027179.aE (q + 2), OMA.S_oeis_a027179.aO (q + 1),
      OMA.S_oeis_a027179.aE (q + 1), OMA.S_oeis_a027179.aO q, OMA.S_oeis_a027179.aE q]
    rw [show q + 3 + 1 = q + 3 + 1 from rfl, cbs (q + 3), cbs (q + 2), cbs (q + 1), cbs q]
    push_cast
    have h1 : ((q : ℚ) + 1) ≠ 0 := by positivity
    have h2 : ((q : ℚ) + 2) ≠ 0 := by positivity
    have h3 : ((q : ℚ) + 3) ≠ 0 := by positivity
    have h4 : ((q : ℚ) + 4) ≠ 0 := by positivity
    have h1' : ((q : ℚ) + 1 + 1) ≠ 0 := by positivity
    have h2' : ((q : ℚ) + 2 + 1) ≠ 0 := by positivity
    have h3' : ((q : ℚ) + 3 + 1) ≠ 0 := by positivity
    field_simp
    ring
  · obtain ⟨q, rfl⟩ : ∃ q, k = q + 3 := ⟨k - 3, by omega⟩
    rw [show 2 * (q + 3) + 1 - 1 = 2 * (q + 3) by omega, show 2 * (q + 3) + 1 - 2 = 2 * (q + 2) + 1 by omega,
      show 2 * (q + 3) + 1 - 3 = 2 * (q + 2) by omega, show 2 * (q + 3) + 1 - 4 = 2 * (q + 1) + 1 by omega,
      show 2 * (q + 3) + 1 - 5 = 2 * (q + 1) by omega, show 2 * (q + 3) + 1 - 6 = 2 * q + 1 by omega]
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [OMA.S_oeis_a027179.aO (q + 3), OMA.S_oeis_a027179.aE (q + 3), OMA.S_oeis_a027179.aO (q + 2), OMA.S_oeis_a027179.aE (q + 2),
      OMA.S_oeis_a027179.aO (q + 1), OMA.S_oeis_a027179.aE (q + 1), OMA.S_oeis_a027179.aO q]
    rw [cbs (q + 3), cbs (q + 2), cbs (q + 1), cbs q]
    push_cast
    have h1 : ((q : ℚ) + 1) ≠ 0 := by positivity
    have h2 : ((q : ℚ) + 2) ≠ 0 := by positivity
    have h3 : ((q : ℚ) + 3) ≠ 0 := by positivity
    have h4 : ((q : ℚ) + 4) ≠ 0 := by positivity
    have h1' : ((q : ℚ) + 1 + 1) ≠ 0 := by positivity
    have h2' : ((q : ℚ) + 2 + 1) ≠ 0 := by positivity
    have h3' : ((q : ℚ) + 3 + 1) ≠ 0 := by positivity
    field_simp
    ring
