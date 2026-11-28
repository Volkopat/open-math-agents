import OMAStatements.S_oeis_a144652

-- Problem: A144652: Triangle, read by rows, where T(m,n) = floor((2mn+m+n)/2) with m >= n >= 1.
-- Upstream: formal-conjectures statements/oeis-a144652.lean:0 (declaration OMA.S_oeis_a144652.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: if 4h+1 (at least 5) is not prime, it is p*q with 1 < p < 4h+1 (p its least prime
-- factor); p and q are odd, so p = 2a+1 and q = 2b+1 with a, b >= 1, and 2ab+a+b = 2h, so
-- T(max(a,b), min(a,b)) = h and h is a term.

open OMA.S_oeis_a144652 in
theorem OMA.solution : type_of% @OMA.S_oeis_a144652.main := by
  intro h hh H
  by_contra hp
  have h2 : 2 ≤ 4 * h + 1 := by omega
  obtain ⟨p, q, hq, hp2, hlt⟩ : ∃ p q : ℕ, 4 * h + 1 = p * q ∧ 2 ≤ p ∧ p < 4 * h + 1 := by
    obtain ⟨q, hq⟩ := Nat.minFac_dvd (4 * h + 1)
    exact ⟨Nat.minFac (4 * h + 1), q, hq,
      (Nat.minFac_prime (show 4 * h + 1 ≠ 1 by omega)).two_le,
      (Nat.not_prime_iff_minFac_lt h2).mp hp⟩
  obtain ⟨a, ha⟩ : ∃ a, p = 2 * a ∨ p = 2 * a + 1 := ⟨p / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, q = 2 * b ∨ q = 2 * b + 1 := ⟨q / 2, by omega⟩
  rcases ha with rfl | rfl
  · have e1 : 4 * h + 1 = 2 * (a * q) := by
      rw [hq]
      ring
    omega
  · rcases hb with rfl | rfl
    · have e1 : 4 * h + 1 = 2 * ((2 * a + 1) * b) := by
        rw [hq]
        ring
      omega
    · have e1 : 4 * h + 1 = 4 * (a * b) + 2 * a + 2 * b + 1 := by
        rw [hq]
        ring
      have ha1 : 1 ≤ a := by omega
      have hb1 : 1 ≤ b := by
        by_contra hb0
        have hb0' : b = 0 := by omega
        subst hb0'
        have e2 : 4 * h + 1 = 2 * a + 1 := by
          rw [hq]
          ring
        omega
      rcases le_total a b with hab | hab
      · apply H
        refine ⟨b, a, ha1, hab, ?_⟩
        have e3 : 2 * b * a = 2 * (a * b) := by ring
        unfold T
        omega
      · apply H
        refine ⟨a, b, hb1, hab, ?_⟩
        have e3 : 2 * a * b = 2 * (a * b) := by ring
        unfold T
        omega
