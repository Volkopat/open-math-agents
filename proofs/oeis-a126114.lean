import OMAStatements.S_oeis_a126114

-- Problem: A126114: Ultimate fixed-point under the mapping n->f(n), where f(n)=n if n is square else f(n)=n-Floor(Sqrt(n)).
-- Upstream: formal-conjectures statements/oeis-a126114.lean:0 (declaration OMA.S_oeis_a126114.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: squares are fixed points of f. For 1 <= j <= 2m, m*m + j is not a square and
-- f(m*m + j) = m*m + j - m. If 1 <= j <= m, two steps lead from m*m + j to (m-1)*(m-1) + j, so
-- the orbit reaches j*j + j and then the square j*j. With k(k+1) < n <= (k+1)(k+2) and
-- X = n - k(k+1): X <= k gives n = k*k + (k + X), one step to k*k + X, value X^2; X = k+1 gives
-- n = (k+1)^2; X > k+1 gives n = (k+1)^2 + (X-k-1) with X-k-1 <= k+1, value (X-k-1)^2.

open OMA.S_oeis_a126114 in
theorem OMA.solution : type_of% @OMA.S_oeis_a126114.main := by
  have step : ∀ n v : ℕ, (∃ J : ℕ, ∀ i : ℕ, J ≤ i → f^[i] (f n) = v) →
      ∃ J : ℕ, ∀ i : ℕ, J ≤ i → f^[i] n = v := by
    rintro n v ⟨J, hJ⟩
    refine ⟨J + 1, fun i hi => ?_⟩
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    exact hJ i' (by omega)
  have fsq : ∀ r : ℕ, f (r * r) = r * r := by
    intro r
    unfold f
    rw [if_pos (show IsSquare (r * r) from ⟨r, rfl⟩)]
  have fix : ∀ r : ℕ, ∃ J : ℕ, ∀ i : ℕ, J ≤ i → f^[i] (r * r) = r * r :=
    fun r => ⟨0, fun i _ => Function.iterate_fixed (fsq r) i⟩
  have fmid : ∀ m j c : ℕ, 1 ≤ j → j ≤ m + m → m * m + j = c + m → f (m * m + j) = c := by
    intro m j c h1 h2 h3
    have e : (m + 1) * (m + 1) = m * m + m + m + 1 := by ring
    have hns : ¬ IsSquare (m * m + j) := by
      rintro ⟨r, hr⟩
      exact Nat.not_exists_sq (by omega : m * m < m * m + j)
        (by omega : m * m + j < (m + 1) * (m + 1)) ⟨r, hr.symm⟩
    unfold f
    rw [if_neg hns, Nat.sqrt_add_eq m h2]
    omega
  have L1 : ∀ d j : ℕ, 1 ≤ j →
      ∃ J : ℕ, ∀ i : ℕ, J ≤ i → f^[i] ((j + d) * (j + d) + j) = j * j := by
    intro d
    induction d with
    | zero =>
      intro j hj
      apply step
      rw [Nat.add_zero, fmid j j (j * j) hj (by omega) rfl]
      exact fix j
    | succ d ih =>
      intro j hj
      apply step
      rw [fmid (j + (d + 1)) j ((j + d) * (j + d) + ((j + d) + j)) hj (by omega) (by ring)]
      apply step
      rw [fmid (j + d) ((j + d) + j) ((j + d) * (j + d) + j) (by omega) (by omega) (by ring)]
      exact ih j hj
  intro n k _ h1 h2
  have ht : ∀ q : ℕ, 2 * t q = q * (q + 1) := fun q =>
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self q)
  rw [ht] at h1 h2 ⊢
  have e2 : (k + 1) * (k + 1 + 1) = k * (k + 1) + (k + 1) + (k + 1) := by ring
  obtain ⟨x, rfl⟩ : ∃ x, n = k * (k + 1) + x := ⟨n - k * (k + 1), by omega⟩
  rw [Nat.add_sub_cancel_left]
  by_cases hx : x ≤ k + 1
  · rw [if_pos hx]
    by_cases hk : x = k + 1
    · subst hk
      rw [show k * (k + 1) + (k + 1) = (k + 1) * (k + 1) by ring, Nat.pow_two]
      exact fix (k + 1)
    · rw [show k * (k + 1) + x = k * k + (k + x) by ring]
      apply step
      rw [fmid k (k + x) (k * k + x) (by omega) (by omega) (by ring)]
      obtain ⟨d, rfl⟩ : ∃ d, k = x + d := ⟨k - x, by omega⟩
      rw [Nat.pow_two]
      exact L1 d x (by omega)
  · rw [if_neg hx]
    obtain ⟨y, rfl⟩ : ∃ y, x = k + 1 + y := ⟨x - (k + 1), by omega⟩
    rw [show k + 1 + y - k - 1 = y by omega,
      show k * (k + 1) + (k + 1 + y) = (k + 1) * (k + 1) + y by ring]
    obtain ⟨d, hd⟩ : ∃ d, k + 1 = y + d := ⟨k + 1 - y, by omega⟩
    rw [hd, Nat.pow_two]
    exact L1 d y (by omega)
