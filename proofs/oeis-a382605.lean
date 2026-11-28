import OMAStatements.S_oeis_a382605

/-!
Parity and explicit polynomial witness proof for OEIS A382605 / A154708:
both folds n and inA154708 n force Even (total n), which for n > 0 means
n % 4 = 0 or n % 4 = 3, where explicit linear witnesses satisfy both.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a382605.main := by
  have htotal : ∀ k : ℕ, 2 * OMA.S_oeis_a382605.total k = k * (k + 1) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [OMA.S_oeis_a382605.total, Nat.mul_add, ih]
      ring
  have hfolds_even : ∀ n : ℕ,
      OMA.S_oeis_a382605.folds n → Even (OMA.S_oeis_a382605.total n) := by
    rintro n ⟨i, j, _, _, hij⟩
    exact ⟨OMA.S_oeis_a382605.total j - OMA.S_oeis_a382605.total i, by omega⟩
  have hA_even : ∀ n : ℕ,
      OMA.S_oeis_a382605.inA154708 n → Even (OMA.S_oeis_a382605.total n) := by
    rintro n ⟨b, c, _, _, hbc⟩
    have h2 : 2 * OMA.S_oeis_a382605.total n + b ^ 2 = c ^ 2 := by
      rw [htotal n]
      exact hbc
    let qb := b / 2
    let rb := b % 2
    let qc := c / 2
    let rc := c % 2
    have hbd : b = 2 * qb + rb := (Nat.div_add_mod b 2).symm
    have hcd : c = 2 * qc + rc := (Nat.div_add_mod c 2).symm
    rcases (by omega : rb = 0 ∨ rb = 1) with hrb | hrb <;>
      rcases (by omega : rc = 0 ∨ rc = 1) with hrc | hrc
    · have heq : 2 * OMA.S_oeis_a382605.total n + 4 * (qb * qb) = 4 * (qc * qc) := by
        rw [hbd, hcd, hrb, hrc] at h2
        nlinarith
      exact ⟨OMA.S_oeis_a382605.total n / 2, by omega⟩
    · have heq : 2 * OMA.S_oeis_a382605.total n + 4 * (qb * qb) = 4 * (qc * qc + qc) + 1 := by
        rw [hbd, hcd, hrb, hrc] at h2
        nlinarith
      omega
    · have heq : 2 * OMA.S_oeis_a382605.total n + 4 * (qb * qb + qb) + 1 = 4 * (qc * qc) := by
        rw [hbd, hcd, hrb, hrc] at h2
        nlinarith
      omega
    · have heq : 2 * OMA.S_oeis_a382605.total n + 4 * (qb * qb + qb) = 4 * (qc * qc + qc) := by
        rw [hbd, hcd, hrb, hrc] at h2
        nlinarith
      exact ⟨OMA.S_oeis_a382605.total n / 2, by omega⟩
  have heven_mod4 : ∀ n : ℕ, Even (OMA.S_oeis_a382605.total n) → n % 4 = 0 ∨ n % 4 = 3 := by
    intro n hev
    obtain ⟨k, hk⟩ := hev
    have h2 : 2 * OMA.S_oeis_a382605.total n = n * (n + 1) := htotal n
    have hdiv : n = 4 * (n / 4) + n % 4 := (Nat.div_add_mod n 4).symm
    rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with hr | hr | hr | hr
    · exact Or.inl hr
    · exfalso
      have heq : 4 * k = 4 * (4 * (n / 4) ^ 2 + 3 * (n / 4)) + 2 := by
        rw [hk, ← two_mul] at h2
        rw [hr] at hdiv
        nlinarith
      omega
    · exfalso
      have heq : 4 * k = 4 * (4 * (n / 4) ^ 2 + 5 * (n / 4) + 1) + 2 := by
        rw [hk, ← two_mul] at h2
        rw [hr] at hdiv
        nlinarith
      omega
    · exact Or.inr hr
  have heven_witness : ∀ n : ℕ, 0 < n → Even (OMA.S_oeis_a382605.total n) →
      OMA.S_oeis_a382605.folds n ∧ OMA.S_oeis_a382605.inA154708 n := by
    intro n hn hev
    rcases heven_mod4 n hev with hr | hr
    · obtain ⟨m, hm_eq⟩ : ∃ m : ℕ, n = 4 * m := ⟨n / 4, by omega⟩
      have hm : 1 ≤ m := by omega
      subst hm_eq
      refine ⟨⟨m, 3 * m, by omega, by omega, ?_⟩,
        ⟨3 * m + 1, 5 * m + 1, by omega, by omega, ?_⟩⟩
      · have h4 : 2 * (2 * OMA.S_oeis_a382605.total (3 * m)) =
            2 * OMA.S_oeis_a382605.total (4 * m) + 2 * (2 * OMA.S_oeis_a382605.total m) := by
          rw [htotal, htotal, htotal]
          ring
        omega
      · ring
    · obtain ⟨m, hm_eq⟩ : ∃ m : ℕ, n = 4 * m + 3 := ⟨n / 4, by omega⟩
      subst hm_eq
      refine ⟨⟨m, 3 * m + 2, by omega, by omega, ?_⟩,
        ⟨3 * m + 2, 5 * m + 4, by omega, by omega, ?_⟩⟩
      · have h4 : 2 * (2 * OMA.S_oeis_a382605.total (3 * m + 2)) =
            2 * OMA.S_oeis_a382605.total (4 * m + 3) + 2 * (2 * OMA.S_oeis_a382605.total m) := by
          rw [htotal, htotal, htotal]
          ring
        omega
      · ring
  intro n hn
  refine ⟨⟨hfolds_even n, fun h => (heven_witness n hn h).1⟩,
    ⟨fun h => (heven_witness n hn (hfolds_even n h)).2,
      fun h => (heven_witness n hn (hA_even n h)).1⟩⟩
