import OMAStatements.S_oeis_a329278

-- Problem: A329278: Irregular table read by rows. The n-th row is the permutation of {0, 1, 2, ..., 2^n-1} given by T(n,k) = k*(k+1)/2 (mod 2^n).
-- Upstream: formal-conjectures statements/oeis-a329278.lean:0 (declaration OMA.S_oeis_a329278.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: T(n,k+1) = (T(n,k) + k + 1) mod 2^n wraps around exactly at a descent, so
-- T(n,j) + 2^n * (descents before j) = j(j+1)/2; at j = 2^n - 1, T = 2^(n-1) gives the count.

open OMA.S_oeis_a329278 in
theorem OMA.solution : type_of% @OMA.S_oeis_a329278.main := by
  have htri : ∀ k : ℕ, (k + 1) * (k + 1 + 1) / 2 = k * (k + 1) / 2 + (k + 1) := by
    intro k
    rw [show (k + 1) * (k + 1 + 1) = k * (k + 1) + (k + 1) * 2 by ring,
      Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]
  have gen : ∀ N r s : ℕ, r < N → s < N →
      (r + s) % N + N * (if (r + s) % N < r then 1 else 0) = r + s := by
    intro N r s hr hs
    by_cases h : r + s < N
    · rw [Nat.mod_eq_of_lt h, if_neg (show ¬ (r + s < r) by omega), mul_zero, add_zero]
    · have hle : N ≤ r + s := by omega
      have hmod : (r + s) % N = r + s - N := by
        have e := Nat.add_mod_right (r + s - N) N
        rw [show r + s - N + N = r + s by omega] at e
        rw [e]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hmod, if_pos (show r + s - N < r by omega), mul_one, Nat.sub_add_cancel hle]
  have hfin : ∀ p q : ℕ, p + 1 + (2 * p + 2) * q = (2 * p + 1) * (p + 1) → q = p := by
    intro p q h
    have h1 : ((p : ℤ) + 1) + (2 * (p : ℤ) + 2) * (q : ℤ) = (2 * (p : ℤ) + 1) * ((p : ℤ) + 1) := by
      exact_mod_cast h
    have h2 : (2 * (p : ℤ) + 2) * (q : ℤ) = (2 * (p : ℤ) + 2) * (p : ℤ) := by
      linear_combination h1
    have h3 : (q : ℤ) = (p : ℤ) := mul_left_cancel₀ (by positivity) h2
    exact_mod_cast h3
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpos : 0 < 2 ^ (m + 1) := by positivity
  have hstep : ∀ j : ℕ, j + 1 < 2 ^ (m + 1) →
      T (m + 1) (j + 1) + 2 ^ (m + 1) * (if T (m + 1) (j + 1) < T (m + 1) j then 1 else 0)
        = T (m + 1) j + (j + 1) := by
    intro j hj
    have e1 : T (m + 1) (j + 1) = (T (m + 1) j + (j + 1)) % 2 ^ (m + 1) := by
      show (j + 1) * (j + 1 + 1) / 2 % 2 ^ (m + 1)
        = (j * (j + 1) / 2 % 2 ^ (m + 1) + (j + 1)) % 2 ^ (m + 1)
      rw [htri j, Nat.mod_add_mod]
    have hr : T (m + 1) j < 2 ^ (m + 1) := by
      unfold T
      exact Nat.mod_lt _ hpos
    rw [e1]
    exact gen _ _ _ hr hj
  have key : ∀ j : ℕ, j < 2 ^ (m + 1) →
      T (m + 1) j + 2 ^ (m + 1) *
          (∑ k ∈ Finset.range j, if T (m + 1) (k + 1) < T (m + 1) k then 1 else 0)
        = j * (j + 1) / 2 := by
    intro j
    induction j with
    | zero =>
      intro _
      simp [T]
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have hs := hstep j hj
      rw [Finset.sum_range_succ, mul_add (2 ^ (m + 1)), htri j]
      omega
  have hD : descents (m + 1) = ∑ k ∈ Finset.range (2 ^ (m + 1) - 1),
      (if T (m + 1) (k + 1) < T (m + 1) k then 1 else 0) := by
    unfold descents
    rw [Finset.card_filter]
  have h0 : 0 < 2 ^ m := by positivity
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ m = M + 1 := ⟨2 ^ m - 1, by omega⟩
  have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  have hN : 2 ^ (m + 1) = 2 * M + 2 := by omega
  have hq : (2 * M + 1) * (2 * M + 1 + 1) / 2 = (2 * M + 1) * (M + 1) := by
    rw [show (2 * M + 1) * (2 * M + 1 + 1) = 2 * ((2 * M + 1) * (M + 1)) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have hT : T (m + 1) (2 * M + 1) = M + 1 := by
    show (2 * M + 1) * (2 * M + 1 + 1) / 2 % 2 ^ (m + 1) = M + 1
    rw [hq, hN, show (2 * M + 1) * (M + 1) = M + 1 + (2 * M + 2) * M by ring,
      Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hk := key (2 * M + 1) (by omega)
  rw [hT, hN, hq] at hk
  rw [hD, show m + 1 - 1 = m by omega, hM, show M + 1 - 1 = M by omega, hN,
    show 2 * M + 2 - 1 = 2 * M + 1 by omega]
  exact hfin M _ hk
