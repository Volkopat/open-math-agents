import OMAStatements.S_oeis_a306825

-- Problem: A306825: Primitive part of A001353(n).
-- Upstream: formal-conjectures statements/oeis-a306825.lean:0 (declaration OMA.S_oeis_a306825.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for a prime p the divisors are 1 and p, so a(p) = U(p) with U = A001353. U(2) = 4,
-- and the addition formula U(m+n+1) = U(m+1)U(n+1) - U(m)U(n) gives
-- U(2m+1) = (U(m+1) - U(m)) * (U(m+1) + U(m)), where both factors are at least 2 for m >= 1
-- because U(n+1) >= 3U(n) >= 0. So a(p) is never prime, and the set of such p is empty.

open OMA.S_oeis_a306825 in
theorem OMA.solution : type_of% @OMA.S_oeis_a306825.main := by
  have U1 : U 1 = 1 := rfl
  have U2 : U 2 = 4 := rfl
  have Urec : ∀ n : ℕ, U (n + 1 + 1) = 4 * U (n + 1) - U n := fun n => rfl
  have mono : ∀ n : ℕ, 0 ≤ U n ∧ 3 * U n ≤ U (n + 1) := by
    intro n
    induction n with
    | zero =>
      show (0 : ℤ) ≤ 0 ∧ (3 : ℤ) * 0 ≤ 1
      norm_num
    | succ k ih =>
      obtain ⟨i1, i2⟩ := ih
      have e := Urec k
      exact ⟨by omega, by omega⟩
  have pos : ∀ m : ℕ, 1 ≤ U (m + 1) := by
    intro m
    induction m with
    | zero =>
      show (1 : ℤ) ≤ 1
      exact le_refl 1
    | succ k ih =>
      obtain ⟨_, h2⟩ := mono (k + 1)
      omega
  have addf : ∀ m n : ℕ, U (m + n + 1) = U (m + 1) * U (n + 1) - U m * U n ∧
      U (m + (n + 1) + 1) = U (m + 1) * U (n + 1 + 1) - U m * U (n + 1) := by
    intro m n
    induction n with
    | zero =>
      have a1 : U (m + 0 + 1) = U (m + 1) := rfl
      have a2 : U (m + (0 + 1) + 1) = 4 * U (m + 1) - U m := rfl
      have a3 : U (0 + 1) = 1 := rfl
      have a4 : U (0 + 1 + 1) = 4 := rfl
      have a5 : U 0 = 0 := rfl
      rw [a1, a2, a3, a4, a5]
      constructor
      · ring
      · ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have e1 : U (m + (k + 1 + 1) + 1) = 4 * U (m + (k + 1) + 1) - U (m + k + 1) := rfl
      have e2 := Urec (k + 1)
      have e3 := Urec k
      linear_combination e1 + 4 * ih.2 - ih.1 - U (m + 1) * e2 + U m * e3
  have aprime : ∀ p : ℕ, p.Prime → a p = (U p : ℚ) := by
    intro p hp
    unfold a
    rw [Nat.Prime.divisors hp, Finset.prod_pair (Nat.Prime.one_lt hp).ne, Nat.div_one,
      Nat.div_self hp.pos, ArithmeticFunction.moebius_apply_one, U1]
    simp
  have key : ∀ p : ℕ, p.Prime → ¬ ∃ q : ℕ, q.Prime ∧ a p = q := by
    rintro p hp ⟨q, hq, hpq⟩
    rw [aprime p hp] at hpq
    have hz : U p = (q : ℤ) := by exact_mod_cast hpq
    obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : ℤ, 2 ≤ x ∧ 2 ≤ y ∧ U p = x * y := by
      rcases hp.eq_two_or_odd' with h2 | hodd
      · subst h2
        exact ⟨2, 2, le_refl 2, le_refl 2, by norm_num [U2]⟩
      · obtain ⟨m, hm⟩ := hodd
        have hm1 : 1 ≤ m := by
          have := hp.two_le
          omega
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        refine ⟨U (j + 1 + 1) - U (j + 1), U (j + 1 + 1) + U (j + 1), ?_, ?_, ?_⟩
        · have h1 := pos j
          obtain ⟨_, h2⟩ := mono (j + 1)
          omega
        · have h1 := pos j
          obtain ⟨_, h2⟩ := mono (j + 1)
          omega
        · rw [hm, show 2 * (j + 1) + 1 = j + 1 + (j + 1) + 1 by omega, (addf (j + 1) (j + 1)).1]
          ring
    obtain ⟨x', rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ x by omega)
    obtain ⟨y', rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ y by omega)
    have hq' : q = x' * y' := by
      have h3 : (q : ℤ) = (x' : ℤ) * (y' : ℤ) := hz.symm.trans hxy
      exact_mod_cast h3
    rw [hq'] at hq
    exact Nat.not_prime_mul (by omega) (by omega) hq
  refine ⟨?_, key⟩
  exact Set.not_infinite.mpr
    (Set.Finite.subset Set.finite_empty (fun p hp => absurd hp.2 (key p hp.1)))
