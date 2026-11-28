import OMAStatements.S_oeis_a363152

-- Problem oeis-a363152: the denominator a(n) of Sum_{j=0..2n} B'_j B'_{2n-j} (Bernoulli numbers with B'_1 = 1/2)
-- is never divisible by the cube of a prime.
-- Upstream: statements/oeis-a363152.lean (declaration OMA.S_oeis_a363152.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: let P be the product of the primes below 2n + 2. By the von Staudt-Clausen theorem, B_{2k} plus the sum
-- of 1/q over certain primes q < 2k + 2 is an integer, so P * B'_j is an integer for every j <= 2n (for j = 1 use
-- that 2 divides P, and B'_j = 0 for odd j > 1). Hence P^2 times the sum is an integer and a(n) divides P^2.
-- P is squarefree, so no cube of a prime divides P^2.

open Finset

private lemma squarefree_prod_primes_a363152 (s : Finset ℕ) :
    (∀ p ∈ s, p.Prime) → Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp
  | insert a s ha ih =>
    intro hs
    rw [Finset.prod_insert ha, Nat.squarefree_mul_iff]
    have hpa : a.Prime := hs a (Finset.mem_insert_self a s)
    refine ⟨?_, Irreducible.squarefree hpa, ih (fun p hp => hs p (Finset.mem_insert_of_mem hp))⟩
    apply Nat.Coprime.prod_right
    intro q hq
    refine (Nat.coprime_primes hpa (hs q (Finset.mem_insert_of_mem hq))).mpr ?_
    rintro rfl
    exact ha hq

private lemma int_mul_bernoulli'_a363152 (n P : ℕ)
    (hP : ∀ q : ℕ, q.Prime → q < 2 * n + 2 → q ∣ P) (j : ℕ) (hj : j ≤ 2 * n) :
    ∃ z : ℤ, (P : ℚ) * bernoulli' j = z := by
  have key : ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime ∧ q < 2 * n + 2) →
      ∃ w : ℤ, (P : ℚ) * ∑ q ∈ S, (1 : ℚ) / q = w := by
    intro S hS
    refine ⟨((∑ q ∈ S, P / q : ℕ) : ℤ), ?_⟩
    rw [Finset.mul_sum, Int.cast_natCast, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro q hq
    obtain ⟨hqp, hql⟩ := hS q hq
    rw [Nat.cast_div (hP q hqp hql) (Nat.cast_ne_zero.mpr hqp.ne_zero)]
    ring
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
  · rcases k with _ | k
    · refine ⟨(P : ℤ), ?_⟩
      rw [show 2 * 0 = 0 from rfl, bernoulli'_zero]
      simp
    · have hne1 : 2 * (k + 1) ≠ 1 := by omega
      have hb : bernoulli' (2 * (k + 1)) = bernoulli (2 * (k + 1)) :=
        (bernoulli_eq_bernoulli'_of_ne_one hne1).symm
      obtain ⟨z₀, hz₀⟩ := Bernoulli.vonStaudt_clausen (k + 1)
      obtain ⟨S, hS, hz₁⟩ : ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime ∧ q < 2 * (k + 1) + 2) ∧
          (z₀ : ℚ) = bernoulli (2 * (k + 1)) + ∑ q ∈ S, (1 : ℚ) / q :=
        ⟨_, fun q hq => by
          rw [Finset.mem_filter, Finset.mem_range] at hq
          exact ⟨hq.2.1, hq.1⟩, hz₀⟩
      obtain ⟨w, hw⟩ := key S (fun q hq => ⟨(hS q hq).1, by have := (hS q hq).2; omega⟩)
      refine ⟨(P : ℤ) * z₀ - w, ?_⟩
      have hB : bernoulli (2 * (k + 1)) = (z₀ : ℚ) - ∑ q ∈ S, (1 : ℚ) / q := by
        rw [hz₁]
        ring
      rw [hb, hB, mul_sub, hw]
      simp
  · rcases k with _ | k
    · obtain ⟨c, hc⟩ := hP 2 Nat.prime_two (by omega)
      refine ⟨(c : ℤ), ?_⟩
      rw [show 2 * 0 + 1 = 1 from rfl, bernoulli'_one, hc]
      push_cast
      ring
    · refine ⟨0, ?_⟩
      rw [bernoulli'_eq_zero_of_odd ⟨k + 1, rfl⟩ (by omega)]
      simp

theorem OMA.solution : type_of% @OMA.S_oeis_a363152.main := by
  intro n p hp hdvd
  unfold OMA.S_oeis_a363152.a at hdvd
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ, P = ∏ q ∈ (range (2 * n + 2)).filter Nat.Prime, q := ⟨_, rfl⟩
  have hPsq : Squarefree P := by
    rw [hPdef]
    exact squarefree_prod_primes_a363152 _ (fun q hq => (Finset.mem_filter.mp hq).2)
  have hPdvd : ∀ q : ℕ, q.Prime → q < 2 * n + 2 → q ∣ P := by
    intro q hq hlt
    rw [hPdef]
    exact Finset.dvd_prod_of_mem (fun q => q) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hq⟩)
  have hP0 : P ≠ 0 := hPsq.ne_zero
  have hint : ∀ j : ℕ, ∃ z : ℤ, j ≤ 2 * n → (P : ℚ) * bernoulli' j = z := by
    intro j
    by_cases hj : j ≤ 2 * n
    · obtain ⟨z, hz⟩ := int_mul_bernoulli'_a363152 n P hPdvd j hj
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose z hz using hint
  have hne : (((P ^ 2 : ℕ) : ℤ) : ℚ) ≠ 0 := by
    have h2 := pow_ne_zero 2 hP0
    exact_mod_cast h2
  have hs : (∑ j ∈ range (2 * n + 1), bernoulli' j * bernoulli' (2 * n - j))
      = Rat.divInt (∑ j ∈ range (2 * n + 1), z j * z (2 * n - j)) ((P ^ 2 : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div, eq_div_iff hne]
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [← hz j (by omega), ← hz (2 * n - j) (by omega)]
    ring
  rw [hs] at hdvd
  have hden : (Rat.divInt (∑ j ∈ range (2 * n + 1), z j * z (2 * n - j)) ((P ^ 2 : ℕ) : ℤ)).den ∣ P ^ 2 :=
    Int.natCast_dvd_natCast.mp (Rat.den_dvd _ _)
  have hp3 : p ^ 3 ∣ P ^ 2 := dvd_trans hdvd hden
  have hpP : p ∣ P := hp.dvd_of_dvd_pow (dvd_trans (dvd_pow_self p (by norm_num)) hp3)
  obtain ⟨m, hm⟩ := hpP
  have h1 : p ^ 2 * p ∣ p ^ 2 * m ^ 2 := by
    have e1 : p ^ 2 * p = p ^ 3 := by ring
    have e2 : p ^ 2 * m ^ 2 = P ^ 2 := by rw [hm]; ring
    rw [e1, e2]
    exact hp3
  have h3 : p ∣ m ^ 2 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos 2) h1
  obtain ⟨c, hc⟩ := hp.dvd_of_dvd_pow h3
  have h5 : p * p ∣ P := ⟨c, by rw [hm, hc]; ring⟩
  have hunit := hPsq p h5
  rw [Nat.isUnit_iff] at hunit
  exact hp.one_lt.ne' hunit
