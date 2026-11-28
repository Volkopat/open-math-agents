import OMAStatements.S_oeis_a332553
import Mathlib

namespace OMA.A332553Proof

open OMA.S_oeis_a332553

lemma two_mul_T (i : ℕ) : 2 * T i = i * (i + 1) := by
  unfold T
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self i).two_dvd

lemma T_eq_iff (n k m : ℕ) :
    T n + T k = T m ↔ n * (n + 1) + k * (k + 1) = m * (m + 1) := by
  have h1 := two_mul_T n
  have h2 := two_mul_T k
  have h3 := two_mul_T m
  constructor
  · intro h
    omega
  · intro h
    omega

lemma T_succ (N : ℕ) : T (N + 1) = T N + (N + 1) := by
  have h1 := two_mul_T (N + 1)
  have h2 := two_mul_T N
  linarith

lemma exists_sol (n : ℕ) (hn : 2 ≤ n) : ∃ k, 0 < k ∧ ∃ m, T n + T k = T m := by
  have h := two_mul_T n
  have h6 : 2 * 3 ≤ n * (n + 1) := Nat.mul_le_mul hn (by omega)
  have h3 : 3 ≤ T n := by omega
  refine ⟨T n - 1, by omega, T n, ?_⟩
  have h4 := T_succ (T n - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ T n)] at h4
  omega

lemma k_spec (n : ℕ) (hn : 2 ≤ n) : 0 < A082183 n ∧ ∃ m, T n + T (A082183 n) = T m := by
  have hne : ({k : ℕ | 0 < k ∧ ∃ m : ℕ, T n + T k = T m} : Set ℕ).Nonempty := exists_sol n hn
  have h := Nat.sInf_mem hne
  rw [Set.mem_ofPred_eq] at h
  exact h

lemma k_min (n k' m' : ℕ) (hk : 0 < k') (h : T n + T k' = T m') : A082183 n ≤ k' := by
  have hmem : k' ∈ {k : ℕ | 0 < k ∧ ∃ m : ℕ, T n + T k = T m} := by
    rw [Set.mem_ofPred_eq]
    exact ⟨hk, m', h⟩
  exact Nat.sInf_le hmem

lemma m_spec (n : ℕ) (hn : 2 ≤ n) : T n + T (A082183 n) = T (A082184 n) := by
  obtain ⟨_, hm⟩ := k_spec n hn
  have hne : ({m : ℕ | T n + T (A082183 n) = T m} : Set ℕ).Nonempty := hm
  have h := Nat.sInf_mem hne
  rw [Set.mem_ofPred_eq] at h
  exact h

/-- The triple structure: with `A = n + k - m`, `δ = m - k`, `c = m - n` one has
`A (A + 1) = 2 δ c`, all three positive. -/
lemma core_arith (n k m : ℕ) (hn : 2 ≤ n) (hk : 0 < k)
    (heq : n * (n + 1) + k * (k + 1) = m * (m + 1)) :
    ∃ A δ c : ℕ, 1 ≤ A ∧ 1 ≤ δ ∧ 1 ≤ c ∧ n = A + δ ∧ k = A + c ∧ m = A + δ + c ∧
      A * (A + 1) = 2 * δ * c := by
  have h1 : n < m := by
    by_contra h
    rw [not_lt] at h
    have e1 : m * (m + 1) ≤ n * (n + 1) := Nat.mul_le_mul h (by omega)
    have e2 : 1 * (1 + 1) ≤ k * (k + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have h2 : k < m := by
    by_contra h
    rw [not_lt] at h
    have e1 : m * (m + 1) ≤ k * (k + 1) := Nat.mul_le_mul h (by omega)
    have e2 : 2 * (2 + 1) ≤ n * (n + 1) := Nat.mul_le_mul hn (by omega)
    omega
  have h3 : m < n + k := by
    by_contra h
    rw [not_lt] at h
    have e1 : (n + k) * (n + k + 1) ≤ m * (m + 1) := Nat.mul_le_mul h (by omega)
    have e2 : 2 * 1 ≤ n * k := Nat.mul_le_mul hn (by omega)
    linarith
  obtain ⟨A, hA⟩ : ∃ A, A = n + k - m := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = m - k := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = m - n := ⟨_, rfl⟩
  have en : n = A + δ := by omega
  have ek : k = A + c := by omega
  have em : m = A + δ + c := by omega
  refine ⟨A, δ, c, by omega, by omega, by omega, en, ek, em, ?_⟩
  rw [en, ek, em] at heq
  linarith

lemma a_core (n : ℕ) (hn : 2 ≤ n) :
    ∃ A δ c : ℕ, 1 ≤ A ∧ 1 ≤ δ ∧ 1 ≤ c ∧ n = A + δ ∧ A082183 n = A + c ∧
      A * (A + 1) = 2 * δ * c ∧ a n = (A : ℤ) := by
  obtain ⟨hk, -⟩ := k_spec n hn
  have hm := (T_eq_iff _ _ _).1 (m_spec n hn)
  obtain ⟨A, δ, c, hA, hδ, hc, en, ek, em, hid⟩ :=
    core_arith n (A082183 n) (A082184 n) hn hk hm
  refine ⟨A, δ, c, hA, hδ, hc, en, ek, hid, ?_⟩
  unfold a
  omega

/-- For `n ≥ 2`, `a n = A ≥ 1` with `2 n ≤ A (A + 3)`, and either `n = T(A+1) - 1` or `4 n ≤ A (A + 5)`;
also `A < A082183 n`. -/
lemma a_bound (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : ℕ, 1 ≤ A ∧ a n = (A : ℤ) ∧ 2 * n ≤ A * (A + 3) ∧
      (2 * (n + 1) = (A + 1) * (A + 2) ∨ 4 * n ≤ A * (A + 5)) ∧ A + 1 ≤ A082183 n := by
  obtain ⟨A, δ, c, hA, hδ, hc, en, ek, hid, ha⟩ := a_core n hn
  refine ⟨A, hA, ha, ?_, ?_, by omega⟩
  · have h1 : δ * 1 ≤ δ * c := Nat.mul_le_mul (le_refl δ) hc
    rw [en]
    linarith
  · rcases Nat.lt_or_ge c 2 with h | h
    · left
      have hc1 : c = 1 := by omega
      rw [hc1] at hid
      rw [en]
      linarith
    · right
      have h2 : δ * 2 ≤ δ * c := Nat.mul_le_mul (le_refl δ) h
      rw [en]
      linarith

/-- Conjecture 2 in `ℕ` form: if `2 (n + 1) < j (j + 1)` then `2 n < (j + 2) A`. -/
lemma conj2_nat (j n A : ℕ) (hj : 2 ≤ j) (hlt : 2 * (n + 1) < j * (j + 1)) (hA : 1 ≤ A)
    (hB1 : 2 * n ≤ A * (A + 3)) (hB2 : 2 * (n + 1) = (A + 1) * (A + 2) ∨ 4 * n ≤ A * (A + 5)) :
    2 * n < (j + 2) * A := by
  rcases Nat.lt_or_ge (A + 1) j with h | h
  · have h1 : A * (A + 4) ≤ A * (j + 2) := Nat.mul_le_mul (le_refl A) (by omega)
    linarith
  · rcases Nat.lt_or_ge A j with h' | h'
    · have hAj : j = A + 1 := by omega
      rw [hAj] at hlt ⊢
      rcases hB2 with h2 | h2
      · exfalso
        linarith
      · have h3 : 1 * 1 ≤ A * A := Nat.mul_le_mul hA hA
        linarith
    · have h1 : (j + 2) * j ≤ (j + 2) * A := Nat.mul_le_mul (le_refl _) h'
      linarith

/-- Between two consecutive record places: if `2 (n + 1) < (j + 1) (j + 2)` then `2 n ≤ (j + 2) A`. -/
lemma gap_nat (j n A : ℕ) (hj : 2 ≤ j) (hhi : 2 * (n + 1) < (j + 1) * (j + 2)) (_hA : 1 ≤ A)
    (hB1 : 2 * n ≤ A * (A + 3)) (hB2 : 2 * (n + 1) = (A + 1) * (A + 2) ∨ 4 * n ≤ A * (A + 5)) :
    2 * n ≤ (j + 2) * A := by
  rcases Nat.lt_or_ge (A + 1) j with h | h
  · have h1 : A * (A + 3) ≤ A * (j + 2) := Nat.mul_le_mul (le_refl A) (by omega)
    linarith
  · rcases Nat.lt_or_ge A j with h' | h'
    · have hAj : j = A + 1 := by omega
      rw [hAj]
      linarith
    · rcases Nat.lt_or_ge j A with h'' | h''
      · have h1 : (j + 2) * (j + 1) ≤ (j + 2) * A := Nat.mul_le_mul (le_refl _) (by omega)
        linarith
      · have hAj : A = j := by omega
        rw [hAj] at hB2 ⊢
        rcases hB2 with h2 | h2
        · exfalso
          linarith
        · have h3 : 2 * j ≤ j * j := Nat.mul_le_mul hj (le_refl j)
          linarith

lemma N_spec (j : ℕ) (hj : 2 ≤ j) :
    2 * (j * (j + 1) / 2 - 1 + 1) = j * (j + 1) ∧ 2 ≤ j * (j + 1) / 2 - 1 := by
  have h := two_mul_T j
  have h6 : 2 * 3 ≤ j * (j + 1) := Nat.mul_le_mul hj (by omega)
  unfold T at h
  omega

/-- At `N = T_j - 1`: `a N = j - 1`. -/
lemma val_at (j N : ℕ) (hj : 2 ≤ j) (hN : 2 * (N + 1) = j * (j + 1)) :
    ∃ A : ℕ, a N = (A : ℤ) ∧ A + 1 = j ∧ 2 * N = A * (A + 3) := by
  have h6 : 2 * 3 ≤ j * (j + 1) := Nat.mul_le_mul hj (by omega)
  have hN2 : 2 ≤ N := by omega
  obtain ⟨A, hA, ha, hB1, -, hk⟩ := a_bound N hN2
  have hsol : T N + T j = T (N + 1) := by
    have h1 := T_succ N
    have h2 := two_mul_T j
    omega
  have hkj := k_min N j (N + 1) (by omega) hsol
  have hAj : A + 1 = j := by
    by_contra hne
    have hlt : A + 2 ≤ j := by omega
    have h3 : (A + 2) * (A + 3) ≤ j * (j + 1) := Nat.mul_le_mul hlt (by omega)
    linarith
  refine ⟨A, ha, hAj, ?_⟩
  rw [← hAj] at hN
  linarith

lemma val_q (j N : ℕ) (hj : 2 ≤ j) (hN : 2 * (N + 1) = j * (j + 1)) :
    (N : ℚ) / (a N : ℚ) = (j : ℚ) / 2 + 1 := by
  obtain ⟨A, ha, hAj, h2⟩ := val_at j N hj hN
  have hA : 1 ≤ A := by omega
  have hq : (2 : ℚ) * (N : ℚ) = (A : ℚ) * ((A : ℚ) + 3) := by exact_mod_cast h2
  have hjq : (j : ℚ) = (A : ℚ) + 1 := by exact_mod_cast hAj.symm
  have hApos : (0 : ℚ) < (A : ℚ) := by exact_mod_cast hA
  rw [ha, Int.cast_natCast, div_eq_iff hApos.ne', hjq]
  linear_combination (1 / 2 : ℚ) * hq

lemma ratio_lt (j n : ℕ) (hj : 2 ≤ j) (hn : 2 ≤ n) (hlt : 2 * (n + 1) < j * (j + 1)) :
    (n : ℚ) / (a n : ℚ) < (j : ℚ) / 2 + 1 := by
  obtain ⟨A, hA, ha, hB1, hB2, -⟩ := a_bound n hn
  have key := conj2_nat j n A hj hlt hA hB1 hB2
  have keyq : (2 : ℚ) * (n : ℚ) < ((j : ℚ) + 2) * (A : ℚ) := by exact_mod_cast key
  have hApos : (0 : ℚ) < (A : ℚ) := by exact_mod_cast hA
  rw [ha, Int.cast_natCast, div_lt_iff₀ hApos]
  have e : ((j : ℚ) / 2 + 1) * (A : ℚ) = (((j : ℚ) + 2) * (A : ℚ)) / 2 := by ring
  rw [e, lt_div_iff₀ (by norm_num : (0 : ℚ) < 2)]
  linarith

lemma ratio_le (j n : ℕ) (hj : 2 ≤ j) (hn : 2 ≤ n) (hhi : 2 * (n + 1) < (j + 1) * (j + 2)) :
    (n : ℚ) / (a n : ℚ) ≤ (j : ℚ) / 2 + 1 := by
  obtain ⟨A, hA, ha, hB1, hB2, -⟩ := a_bound n hn
  have key := gap_nat j n A hj hhi hA hB1 hB2
  have keyq : (2 : ℚ) * (n : ℚ) ≤ ((j : ℚ) + 2) * (A : ℚ) := by exact_mod_cast key
  have hApos : (0 : ℚ) < (A : ℚ) := by exact_mod_cast hA
  rw [ha, Int.cast_natCast, div_le_iff₀ hApos]
  have e : ((j : ℚ) / 2 + 1) * (A : ℚ) = (((j : ℚ) + 2) * (A : ℚ)) / 2 := by ring
  rw [e, le_div_iff₀ (by norm_num : (0 : ℚ) < 2)]
  linarith

lemma conj2 (j : ℕ) (hj : 2 ≤ j) (n : ℕ) (hn : 2 ≤ n) (hlt : n < T j - 1) :
    (a n : ℚ) > 2 * (n : ℚ) / ((j : ℚ) + 2) := by
  obtain ⟨A, hA, ha, hB1, hB2, -⟩ := a_bound n hn
  have hT := two_mul_T j
  have hlt' : 2 * (n + 1) < j * (j + 1) := by omega
  have key := conj2_nat j n A hj hlt' hA hB1 hB2
  have keyq : (2 : ℚ) * (n : ℚ) < ((j : ℚ) + 2) * (A : ℚ) := by exact_mod_cast key
  rw [ha, Int.cast_natCast, gt_iff_lt, div_lt_iff₀ (by positivity)]
  linarith

lemma exists_j (n : ℕ) (hn : 2 ≤ n) :
    ∃ j, 2 ≤ j ∧ j * (j + 1) ≤ 2 * (n + 1) ∧ 2 * (n + 1) < (j + 1) * (j + 2) := by
  have hP : ∃ j, 2 * (n + 1) < (j + 1) * (j + 2) := by
    refine ⟨n, ?_⟩
    have h1 : (n + 1) * 2 ≤ (n + 1) * n := Nat.mul_le_mul (le_refl (n + 1)) hn
    linarith
  obtain ⟨j, hspec, hmin⟩ : ∃ j, 2 * (n + 1) < (j + 1) * (j + 2) ∧
      ∀ i, i < j → ¬ 2 * (n + 1) < (i + 1) * (i + 2) :=
    ⟨Nat.find hP, Nat.find_spec hP, fun i hi => Nat.find_min hP hi⟩
  have hj : 2 ≤ j := by
    by_contra h
    have h' : (j + 1) * (j + 2) ≤ 2 * 3 := Nat.mul_le_mul (by omega) (by omega)
    omega
  refine ⟨j, hj, ?_, hspec⟩
  have h4 := hmin (j - 1) (by omega)
  rw [show j - 1 + 1 = j by omega, show j - 1 + 2 = j + 1 by omega] at h4
  omega

lemma records (n : ℕ) : IsRecord n ↔ ∃ j : ℕ, 2 ≤ j ∧ n = j * (j + 1) / 2 - 1 := by
  unfold IsRecord
  constructor
  · rintro ⟨hn, hrec⟩
    obtain ⟨j, hj, hlo, hhi⟩ := exists_j n hn
    refine ⟨j, hj, ?_⟩
    obtain ⟨hN, hN2⟩ := N_spec j hj
    rcases Nat.lt_or_ge (j * (j + 1)) (2 * (n + 1)) with h | h
    · exfalso
      have hlt : j * (j + 1) / 2 - 1 < n := by omega
      have h1 := hrec _ hN2 hlt
      have h0 := val_q j _ hj hN
      have h2 := ratio_le j n hj hn hhi
      linarith
    · omega
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨hN, hN2⟩ := N_spec j hj
    refine ⟨hN2, fun n' hn' hlt => ?_⟩
    have h0 := val_q j _ hj hN
    have h1 := ratio_lt j n' hj hn' (by omega)
    linarith

end OMA.A332553Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a332553.main := by
  refine ⟨⟨fun n => OMA.A332553Proof.records n, fun j hj => ?_⟩,
    fun j hj n hn hlt => OMA.A332553Proof.conj2 j hj n hn hlt⟩
  exact OMA.A332553Proof.val_q j _ hj (OMA.A332553Proof.N_spec j hj).1
