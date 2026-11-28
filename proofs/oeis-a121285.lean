import OMAStatements.S_oeis_a121285

-- Problem: A121285: a(0) = 1; for n>0, a(n) = (n+3)*2^(n-2)-n*binomial(n-1, floor( (n-1)/2 ))-(n-1)*binomial(n-2,floor((n-2)/2)).
-- Upstream: formal-conjectures statements/oeis-a121285.lean:0 (declaration OMA.S_oeis_a121285.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: c(i) = C(i, floor(i/2)) satisfies (i+3) c(i+2) = 2 c(i+1) + 4(i+1) c(i) (two parity cases); for n >= 5 the claim is a polynomial combination of three such relations, and n = 3, 4 are computed.

open OMA.S_oeis_a121285 in
theorem OMA.solution : type_of% @OMA.S_oeis_a121285.main := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℚ, ∀ i : ℕ, c i = ((i.choose (i / 2) : ℕ) : ℚ) := ⟨_, fun _ => rfl⟩
  have hsym : ∀ t : ℕ, ((2 * t + 2).choose (t + 1) : ℚ) = 2 * ((2 * t + 1).choose t : ℚ) := by
    intro t
    have h1 := Nat.choose_succ_succ' (2 * t + 1) t
    rw [Nat.choose_symm_half, show 2 * t + 1 + 1 = 2 * t + 2 by omega] at h1
    rw [h1]
    push_cast
    ring
  have hR : ∀ i : ℕ, ((i : ℚ) + 3) * c (i + 2) = 2 * c (i + 1) + 4 * ((i : ℚ) + 1) * c i := by
    intro i
    obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [hc, hc, hc, show (2 * t + 2) / 2 = t + 1 by omega, show (2 * t + 1) / 2 = t by omega,
        show 2 * t / 2 = t by omega]
      have z1 := hsym t
      have h2 := Nat.add_one_mul_choose_eq (2 * t) t
      rw [Nat.choose_symm_half] at h2
      have z2 : ((2 * t + 1).choose t : ℚ) * ((t : ℚ) + 1)
          = (2 * (t : ℚ) + 1) * ((2 * t).choose t : ℚ) := by
        exact_mod_cast h2.symm
      push_cast
      linear_combination (2 * (t : ℚ) + 3) * z1 + 4 * z2
    · rw [show 2 * t + 1 + 2 = 2 * t + 3 by omega, show 2 * t + 1 + 1 = 2 * t + 2 by omega,
        hc, hc, hc, show (2 * t + 3) / 2 = t + 1 by omega, show (2 * t + 2) / 2 = t + 1 by omega,
        show (2 * t + 1) / 2 = t by omega]
      have z1 := hsym t
      have h3 := Nat.choose_mul_succ_eq (2 * t + 2) (t + 1)
      rw [show 2 * t + 2 + 1 - (t + 1) = t + 2 by omega, show 2 * t + 2 + 1 = 2 * t + 3 by omega]
        at h3
      have z3 : ((2 * t + 3).choose (t + 1) : ℚ) * ((t : ℚ) + 2)
          = ((2 * t + 2).choose (t + 1) : ℚ) * (2 * (t : ℚ) + 3) := by
        exact_mod_cast h3.symm
      push_cast
      linear_combination 2 * z3 + 4 * ((t : ℚ) + 1) * z1
  have ha : ∀ k : ℕ, a (k + 2)
      = ((k : ℚ) + 5) * 2 ^ (k + 2) / 4 - ((k : ℚ) + 2) * c (k + 1) - ((k : ℚ) + 1) * c k := by
    intro k
    unfold a
    rw [if_neg (by omega), show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega, hc, hc]
    push_cast
    ring
  intro n hn
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> norm_num [a]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega]
  have A5 := ha (m + 3)
  have A4 := ha (m + 2)
  have A3 := ha (m + 1)
  have A2 := ha m
  have H2 := hR (m + 2)
  have H1 := hR (m + 1)
  have H0 := hR m
  rw [show m + 3 + 2 = m + 5 by omega, show m + 3 + 1 = m + 4 by omega] at A5
  rw [show m + 2 + 2 = m + 4 by omega, show m + 2 + 1 = m + 3 by omega] at A4 H2
  rw [show m + 1 + 2 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega] at A3 H1
  push_cast at A5 A4 A3 H2 H1 ⊢
  linear_combination (-((m : ℚ) + 4) * (3 * ((m : ℚ) + 5) ^ 2 - 27 * ((m : ℚ) + 5) + 56)) * A5
    + 2 * (m : ℚ) * (3 * ((m : ℚ) + 5) ^ 2 - 12 * ((m : ℚ) + 5) + 5) * A4
    + 4 * (3 * ((m : ℚ) + 5) ^ 3 - 33 * ((m : ℚ) + 5) ^ 2 + 110 * ((m : ℚ) + 5) - 118) * A3
    - 8 * ((m : ℚ) + 2) * (3 * ((m : ℚ) + 5) ^ 2 - 21 * ((m : ℚ) + 5) + 32) * A2
    + ((m : ℚ) + 4) * (3 * ((m : ℚ) + 5) ^ 2 - 27 * ((m : ℚ) + 5) + 56) * H2
    + (((m : ℚ) + 6) * (3 * ((m : ℚ) + 5) ^ 2 - 27 * ((m : ℚ) + 5) + 56)
        - 2 * (m : ℚ) * (3 * ((m : ℚ) + 5) ^ 2 - 12 * ((m : ℚ) + 5) + 5)) * H1
    - 2 * ((m : ℚ) + 2) * (3 * ((m : ℚ) + 5) ^ 2 - 21 * ((m : ℚ) + 5) + 32) * H0
