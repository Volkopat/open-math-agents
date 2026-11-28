import OMAStatements.S_oeis_a278720

-- Problem: A278720: The p-defect p - N(p) of the congruence y^2 == x^3 + 4*x (mod p) for primes p, where N(p) is the number of solutions given by A276730.
-- Upstream: formal-conjectures statements/oeis-a278720.lean:0 (declaration OMA.S_oeis_a278720.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for p == 3 (mod 4) write chi for the quadratic character of ZMod p. The number of
-- y with y^2 = c is chi(c) + 1, so N(p) = p + S with S = sum over x of chi(x^3 + 4x). Since
-- (-x)^3 + 4(-x) = -(x^3 + 4x) and chi(-1) = -1 (-1 is not a square), the substitution x -> -x
-- gives S = -S, so S = 0 and N(p) = p. For p = 2 the two solutions (0,0), (1,1) are counted
-- by decide.

open OMA.S_oeis_a278720 in
theorem OMA.solution : type_of% @OMA.S_oeis_a278720.main := by
  have key3 : ∀ p : ℕ, p.Prime → p % 4 = 3 →
      Nat.card {q : ZMod p × ZMod p // q.2 ^ 2 = q.1 ^ 3 + 4 * q.1} = p := by
    intro p hp h3
    have := Fact.mk hp
    have : NeZero p := ⟨hp.ne_zero⟩
    have hF : ringChar (ZMod p) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      omega
    have hn1 : quadraticChar (ZMod p) (-1) = -1 := by
      apply quadraticChar_neg_one_iff_not_isSquare.mpr
      rw [FiniteField.isSquare_neg_one_iff, ZMod.card]
      omega
    have hsq : ∀ c : ZMod p,
        (((Finset.univ.filter (fun y : ZMod p => y ^ 2 = c)).card : ℕ) : ℤ) =
          quadraticChar (ZMod p) c + 1 := by
      intro c
      have h := quadraticChar_card_sqrts hF c
      rw [Set.toFinset_ofPred] at h
      exact h
    have hS : ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + 4 * x) = 0 := by
      have h1 : ∑ x : ZMod p, quadraticChar (ZMod p) ((-x) ^ 3 + 4 * (-x)) =
          ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + 4 * x) :=
        Equiv.sum_comp (Equiv.neg (ZMod p)) (fun x => quadraticChar (ZMod p) (x ^ 3 + 4 * x))
      have h2 : ∀ x : ZMod p, quadraticChar (ZMod p) ((-x) ^ 3 + 4 * (-x)) =
          -quadraticChar (ZMod p) (x ^ 3 + 4 * x) := by
        intro x
        rw [show (-x) ^ 3 + 4 * (-x) = (-1) * (x ^ 3 + 4 * x) by ring, map_mul, hn1]
        ring
      simp only [h2, Finset.sum_neg_distrib] at h1
      linarith
    have hcount : Fintype.card {q : ZMod p × ZMod p // q.2 ^ 2 = q.1 ^ 3 + 4 * q.1} =
        ∑ x : ZMod p, (Finset.univ.filter (fun y : ZMod p => y ^ 2 = x ^ 3 + 4 * x)).card := by
      rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
      simp only [Finset.card_filter]
    have h5 : ((∑ x : ZMod p,
        (Finset.univ.filter (fun y : ZMod p => y ^ 2 = x ^ 3 + 4 * x)).card : ℕ) : ℤ) = (p : ℤ) := by
      rw [Nat.cast_sum, Finset.sum_congr rfl (fun (x : ZMod p) _ => hsq (x ^ 3 + 4 * x)),
        Finset.sum_add_distrib, hS]
      simp [ZMod.card]
    rw [Nat.card_eq_fintype_card, hcount]
    exact_mod_cast h5
  have key2 : Nat.card {q : ZMod 2 × ZMod 2 // q.2 ^ 2 = q.1 ^ 3 + 4 * q.1} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  intro n _ h
  have hp : (Nat.nth Nat.Prime (n - 1)).Prime := Nat.prime_nth_prime (n - 1)
  have hN : N (Nat.nth Nat.Prime (n - 1)) = Nat.nth Nat.Prime (n - 1) := by
    unfold N
    rcases h with h2 | h3
    · have hp2 : Nat.nth Nat.Prime (n - 1) = 2 := by
        rcases hp.eq_two_or_odd with h | h
        · exact h
        · omega
      rw [hp2]
      exact key2
    · exact key3 _ hp h3
  unfold a
  rw [hN, sub_self]
