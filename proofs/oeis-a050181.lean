import OMAStatements.S_oeis_a050181

-- Problem: A050181: T(2n+3, n), array T as in A051168; a count of Lyndon words.
-- Upstream: formal-conjectures statements/oeis-a050181.lean:0 (declaration OMA.S_oeis_a050181.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: gcd(2n+3, n) = gcd(3, n), so a(n) = h(n) - [3 | n] E(n/3) with h(k) = C(2k+3,k)/(2k+3) and E(j) = C(2j+1,j)/(6j+3); both have rational ratios h(k+1)/h(k) and E(j+1)/E(j); h satisfies the recurrence by a rational identity, and the E parts cancel in each residue class of n mod 3.

open OMA.S_oeis_a050181 in
theorem OMA.solution : type_of% @OMA.S_oeis_a050181.main := by
  obtain ⟨h, hh⟩ : ∃ h : ℕ → ℚ, ∀ k : ℕ,
      h k = ((2 * k + 3).choose k : ℚ) / (2 * (k : ℚ) + 3) := ⟨_, fun _ => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℚ, ∀ j : ℕ,
      E j = ((2 * j + 1).choose j : ℚ) / (6 * (j : ℚ) + 3) := ⟨_, fun _ => rfl⟩
  have hC : ∀ k : ℕ, ((2 * k + 3).choose k : ℚ)
      = ((2 * k + 3).factorial : ℚ) / ((k.factorial : ℚ) * ((k + 3).factorial : ℚ)) := by
    intro k
    have h1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k + 3 by omega)
    rw [show 2 * k + 3 - k = k + 3 by omega] at h1
    rw [eq_div_iff (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k + 3)))), ← mul_assoc]
    exact_mod_cast h1
  have hCE : ∀ j : ℕ, ((2 * j + 1).choose j : ℚ)
      = ((2 * j + 1).factorial : ℚ) / ((j.factorial : ℚ) * ((j + 1).factorial : ℚ)) := by
    intro j
    have h1 := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j + 1 by omega)
    rw [show 2 * j + 1 - j = j + 1 by omega] at h1
    rw [eq_div_iff (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (j + 1)))), ← mul_assoc]
    exact_mod_cast h1
  have hr : ∀ k : ℕ, h (k + 1)
      = 2 * ((k : ℚ) + 2) * (2 * (k : ℚ) + 3) / (((k : ℚ) + 1) * ((k : ℚ) + 4)) * h k := by
    intro k
    rw [hh (k + 1), hh k, hC (k + 1), hC k,
      show 2 * (k + 1) + 3 = 2 * k + 3 + 1 + 1 by ring, Nat.factorial_succ (2 * k + 3 + 1),
      Nat.factorial_succ (2 * k + 3), show k + 1 + 3 = k + 3 + 1 by ring,
      Nat.factorial_succ (k + 3), Nat.factorial_succ k]
    push_cast
    field
  have hEr : ∀ j : ℕ, ((j : ℚ) + 2) * E (j + 1) = 2 * (2 * (j : ℚ) + 1) * E j := by
    intro j
    rw [hE (j + 1), hE j, hCE (j + 1), hCE j,
      show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring, Nat.factorial_succ (2 * j + 1 + 1),
      Nat.factorial_succ (2 * j + 1), Nat.factorial_succ (j + 1), Nat.factorial_succ j]
    push_cast
    field
  have A0 : ∀ j : ℕ, a (3 * j) = h (3 * j) - E j := by
    intro j
    have g : Nat.gcd (2 * (3 * j) + 3) (3 * j) = 3 := by
      rw [Nat.gcd_mul_right_add_left]
      exact Nat.gcd_eq_left (dvd_mul_right 3 j)
    unfold a T
    rw [g, Nat.Prime.divisors Nat.prime_three, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 3),
      ArithmeticFunction.moebius_apply_one, ArithmeticFunction.moebius_apply_prime Nat.prime_three,
      Nat.div_one, Nat.div_one, show (2 * (3 * j) + 3) / 3 = 2 * j + 1 by omega,
      show 3 * j / 3 = j by omega, hh, hE]
    push_cast
    field
  have A1 : ∀ j : ℕ, a (3 * j + 1) = h (3 * j + 1) := by
    intro j
    have g : Nat.gcd (2 * (3 * j + 1) + 3) (3 * j + 1) = 1 := by
      rw [Nat.gcd_mul_right_add_left, Nat.gcd_rec, show (3 * j + 1) % 3 = 1 by omega,
        Nat.gcd_one_left]
    unfold a T
    rw [g, Nat.divisors_one, Finset.sum_singleton, ArithmeticFunction.moebius_apply_one,
      Nat.div_one, Nat.div_one, hh]
    push_cast
    field
  have g23 : Nat.gcd 2 3 = 1 := by norm_num
  have A2 : ∀ j : ℕ, a (3 * j + 2) = h (3 * j + 2) := by
    intro j
    have g : Nat.gcd (2 * (3 * j + 2) + 3) (3 * j + 2) = 1 := by
      rw [Nat.gcd_mul_right_add_left, Nat.gcd_rec, show (3 * j + 2) % 3 = 2 by omega, g23]
    unfold a T
    rw [g, Nat.divisors_one, Finset.sum_singleton, ArithmeticFunction.moebius_apply_one,
      Nat.div_one, Nat.div_one, hh]
    push_cast
    field
  have Lh : ∀ m : ℕ,
      -(((m : ℚ) + 5) - 1) * (((m : ℚ) + 5) + 3) * (((m : ℚ) + 5) + 2) * h (m + 5)
      + 2 * (3 * ((m : ℚ) + 5) - 4) * (((m : ℚ) + 5) + 2) * (((m : ℚ) + 5) + 1) * h (m + 4)
      - 4 * ((m : ℚ) + 5) * (((m : ℚ) + 5) + 1) * (2 * ((m : ℚ) + 5) - 5) * h (m + 3)
      + 2 * (((m : ℚ) + 5) - 1) * (((m : ℚ) + 5) + 2) * (2 * ((m : ℚ) + 5) - 3) * h (m + 2)
      - 4 * (2 * ((m : ℚ) + 5) - 5) * (3 * ((m : ℚ) + 5) - 4) * (((m : ℚ) + 5) + 1) * h (m + 1)
      + 8 * ((m : ℚ) + 5) * (2 * ((m : ℚ) + 5) - 5) * (2 * ((m : ℚ) + 5) - 7) * h m = 0 := by
    intro m
    have q1 := hr m
    have q2 := hr (m + 1)
    have q3 := hr (m + 2)
    have q4 := hr (m + 3)
    have q5 := hr (m + 4)
    rw [show m + 1 + 1 = m + 2 by ring] at q2
    rw [show m + 2 + 1 = m + 3 by ring] at q3
    rw [show m + 3 + 1 = m + 4 by ring] at q4
    rw [show m + 4 + 1 = m + 5 by ring] at q5
    push_cast at q2 q3 q4 q5
    rw [q5, q4, q3, q2, q1]
    field
  intro n hn
  obtain ⟨j, rfl | rfl | rfl⟩ : ∃ j, n = 3 * j + 5 ∨ n = 3 * j + 6 ∨ n = 3 * j + 7 :=
    ⟨(n - 5) / 3, by omega⟩
  · rw [show 3 * j + 5 - 1 = 3 * j + 4 by omega, show 3 * j + 5 - 2 = 3 * j + 3 by omega,
      show 3 * j + 5 - 3 = 3 * j + 2 by omega, show 3 * j + 5 - 4 = 3 * j + 1 by omega,
      show 3 * j + 5 - 5 = 3 * j by omega]
    have b5 := A2 (j + 1)
    have b4 := A1 (j + 1)
    have b3 := A0 (j + 1)
    rw [show 3 * (j + 1) + 2 = 3 * j + 5 by ring] at b5
    rw [show 3 * (j + 1) + 1 = 3 * j + 4 by ring] at b4
    rw [show 3 * (j + 1) = 3 * j + 3 by ring] at b3
    rw [b5, b4, b3, A2 j, A1 j, A0 j]
    have LH := Lh (3 * j)
    have R := hEr j
    push_cast at LH ⊢
    apply mul_left_cancel₀ (show (j : ℚ) + 2 ≠ 0 by positivity)
    linear_combination ((j : ℚ) + 2) * LH
      + 4 * (3 * (j : ℚ) + 5) * (3 * (j : ℚ) + 6) * (2 * (3 * (j : ℚ) + 5) - 5) * R
  · rw [show 3 * j + 6 - 1 = 3 * j + 5 by omega, show 3 * j + 6 - 2 = 3 * j + 4 by omega,
      show 3 * j + 6 - 3 = 3 * j + 3 by omega, show 3 * j + 6 - 4 = 3 * j + 2 by omega,
      show 3 * j + 6 - 5 = 3 * j + 1 by omega]
    have b6 := A0 (j + 2)
    have b5 := A2 (j + 1)
    have b4 := A1 (j + 1)
    have b3 := A0 (j + 1)
    rw [show 3 * (j + 2) = 3 * j + 6 by ring] at b6
    rw [show 3 * (j + 1) + 2 = 3 * j + 5 by ring] at b5
    rw [show 3 * (j + 1) + 1 = 3 * j + 4 by ring] at b4
    rw [show 3 * (j + 1) = 3 * j + 3 by ring] at b3
    rw [b6, b5, b4, b3, A2 j, A1 j]
    have LH := Lh (3 * j + 1)
    rw [show 3 * j + 1 + 5 = 3 * j + 6 by ring, show 3 * j + 1 + 4 = 3 * j + 5 by ring,
      show 3 * j + 1 + 3 = 3 * j + 4 by ring, show 3 * j + 1 + 2 = 3 * j + 3 by ring,
      show 3 * j + 1 + 1 = 3 * j + 2 by ring] at LH
    have R := hEr (j + 1)
    rw [show j + 1 + 1 = j + 2 by ring] at R
    push_cast at LH R ⊢
    apply mul_left_cancel₀ (show (j : ℚ) + 3 ≠ 0 by positivity)
    linear_combination ((j : ℚ) + 3) * LH
      + (3 * (j : ℚ) + 6 - 1) * (3 * (j : ℚ) + 6 + 3) * (3 * (j : ℚ) + 6 + 2) * R
  · rw [show 3 * j + 7 - 1 = 3 * j + 6 by omega, show 3 * j + 7 - 2 = 3 * j + 5 by omega,
      show 3 * j + 7 - 3 = 3 * j + 4 by omega, show 3 * j + 7 - 4 = 3 * j + 3 by omega,
      show 3 * j + 7 - 5 = 3 * j + 2 by omega]
    have b7 := A1 (j + 2)
    have b6 := A0 (j + 2)
    have b5 := A2 (j + 1)
    have b4 := A1 (j + 1)
    have b3 := A0 (j + 1)
    rw [show 3 * (j + 2) + 1 = 3 * j + 7 by ring] at b7
    rw [show 3 * (j + 2) = 3 * j + 6 by ring] at b6
    rw [show 3 * (j + 1) + 2 = 3 * j + 5 by ring] at b5
    rw [show 3 * (j + 1) + 1 = 3 * j + 4 by ring] at b4
    rw [show 3 * (j + 1) = 3 * j + 3 by ring] at b3
    rw [b7, b6, b5, b4, b3, A2 j]
    have LH := Lh (3 * j + 2)
    rw [show 3 * j + 2 + 5 = 3 * j + 7 by ring, show 3 * j + 2 + 4 = 3 * j + 6 by ring,
      show 3 * j + 2 + 3 = 3 * j + 5 by ring, show 3 * j + 2 + 2 = 3 * j + 4 by ring,
      show 3 * j + 2 + 1 = 3 * j + 3 by ring] at LH
    have R := hEr (j + 1)
    rw [show j + 1 + 1 = j + 2 by ring] at R
    push_cast at LH R ⊢
    apply mul_left_cancel₀ (show (j : ℚ) + 3 ≠ 0 by positivity)
    linear_combination ((j : ℚ) + 3) * LH
      - 2 * (3 * (3 * (j : ℚ) + 7) - 4) * (3 * (j : ℚ) + 7 + 2) * (3 * (j : ℚ) + 7 + 1) * R
