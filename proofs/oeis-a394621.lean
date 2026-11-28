import OMAStatements.S_oeis_a394621

-- Problem: A394621: Numbers k of the form k = p1 + p2 = x^2 + y^2 + p1^2, where p1 and p2 are primes, x, y are integers.
-- Upstream: formal-conjectures statements/oeis-a394621.lean:0 (declaration OMA.S_oeis_a394621.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for an odd term one of p1, p2 is 2. If p2 = 2 then x^2 + y^2 = p1 + 2 - p1^2 < 0
-- for p1 >= 3, impossible; so p1 = 2, k - 2 = p2 is prime and k - 4 = x^2 + y^2. Every even
-- k >= 4 is a value of A145979: n = 4m + 2 gives 4m + 4, and n = 2m + 1 gives 4m + 6.

open OMA.S_oeis_a394621 in
theorem OMA.solution : type_of% @OMA.S_oeis_a394621.main := by
  have hodd : ∀ k : ℕ, IsTerm k → Odd k →
      ∃ a b : ℕ, k = a ^ 2 + b ^ 2 + 4 ∧ (k - 2).Prime := by
    intro k hk hko
    obtain ⟨p1, p2, hp1, hp2, hsum, x, y, hxy⟩ := hk
    obtain ⟨j, hj⟩ := hko
    have hp1two : p1 = 2 := by
      rcases hp1.eq_two_or_odd with h1 | h1
      · exact h1
      · exfalso
        rcases hp2.eq_two_or_odd with h2 | h2
        · have h3 : 3 ≤ p1 := by
            have := hp1.two_le
            omega
          have h3z : (3 : ℤ) ≤ (p1 : ℤ) := by exact_mod_cast h3
          rw [hsum, h2] at hxy
          push_cast at hxy
          nlinarith [sq_nonneg x, sq_nonneg y,
            mul_nonneg (sub_nonneg.mpr h3z) (sub_nonneg.mpr h3z)]
        · omega
    subst hp1two
    have hp2two := hp2.two_le
    push_cast at hxy
    have hxy' : (k : ℤ) = ((x.natAbs ^ 2 + y.natAbs ^ 2 + 4 : ℕ) : ℤ) := by
      simp only [Nat.cast_add, Nat.cast_pow, Int.natAbs_pow_two, Nat.cast_ofNat]
      linear_combination hxy
    have hxy'' : k = x.natAbs ^ 2 + y.natAbs ^ 2 + 4 := Nat.cast_inj.mp hxy'
    refine ⟨x.natAbs, y.natAbs, hxy'', ?_⟩
    rw [show k - 2 = p2 by omega]
    exact hp2
  refine ⟨?_, ?_, ?_⟩
  · intro k hk hko
    obtain ⟨a, b, hab, hpr⟩ := hodd k hk hko
    show (k - 2).Prime ∧ ∃ x y : ℕ, k - 2 = x ^ 2 + y ^ 2 + 2
    exact ⟨hpr, a, b, by omega⟩
  · intro k hk hko
    obtain ⟨a, b, hab, _⟩ := hodd k hk hko
    show ∃ x y : ℕ, k - 4 = x ^ 2 + y ^ 2
    exact ⟨a, b, by omega⟩
  · intro k hk hke
    obtain ⟨p1, p2, hp1, hp2, hsum, _⟩ := hk
    have h1 := hp1.two_le
    have h2 := hp2.two_le
    obtain ⟨j, hj⟩ := hke
    have h24 : Nat.gcd 2 4 = 2 := by decide
    have h14 : Nat.gcd 1 4 = 1 := by decide
    have h34 : Nat.gcd 3 4 = 1 := by decide
    obtain ⟨m, hm | hm⟩ : ∃ m : ℕ, k = 4 * m + 4 ∨ k = 4 * m + 6 := ⟨(k - 4) / 4, by omega⟩
    · have hg : Nat.gcd (4 * m + 2) 4 = 2 := by
        rw [Nat.gcd_comm, Nat.gcd_rec, show (4 * m + 2) % 4 = 2 by omega, h24]
      refine ⟨4 * m + 2, ?_⟩
      show (2 * (4 * m + 2) + 4) / Nat.gcd (4 * m + 2) 4 = k
      rw [hg]
      omega
    · have hg : Nat.gcd (2 * m + 1) 4 = 1 := by
        rw [Nat.gcd_comm, Nat.gcd_rec]
        rcases (show (2 * m + 1) % 4 = 1 ∨ (2 * m + 1) % 4 = 3 by omega) with h | h
        · rw [h, h14]
        · rw [h, h34]
      refine ⟨2 * m + 1, ?_⟩
      show (2 * (2 * m + 1) + 4) / Nat.gcd (2 * m + 1) 4 = k
      rw [hg, Nat.div_one]
      omega
