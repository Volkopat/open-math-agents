import OMAStatements.S_oeis_a007921

/-!
# Differences of two primes in OEIS A007921

If the difference is odd, the smaller prime must be 2. For a positive even
difference `k`, either `k + 3` or `k + 5` being prime gives an explicit pair.
For the remaining differences, the two primes have the same nonzero residue
modulo 3 when `3 ∣ k`. Otherwise the smaller prime is congruent to `k` modulo 3.

The theorem `unbounded_minimum_start` shows why a finite list of smaller primes
cannot cover either remaining case. It applies in every residue class with an even
representative, including 0, 2 and 4 modulo 6.
-/

namespace OMA.R_oeis_a007921_R1

open OMA.S_oeis_a007921

/-- Even differences divisible by 3 for which 5 cannot be the smaller prime. -/
def H1 : Prop :=
  ∀ k : ℕ, 0 < k → Even k → 3 ∣ k → ¬ (k + 5).Prime →
    ∃ q : ℕ, 7 ≤ q ∧ q.Prime ∧ (q + k).Prime

/-- Other even differences after excluding 3 and 5 as the smaller prime. -/
def H2 : Prop :=
  ∀ k : ℕ, 0 < k → Even k → ¬ 3 ∣ k → ¬ (k + 3).Prime → ¬ (k + 5).Prime →
    ∃ q : ℕ, 7 ≤ q ∧ q % 3 = k % 3 ∧ q.Prime ∧ (q + k).Prime

/-- An odd positive difference of two primes has smaller prime 2. -/
lemma odd_gap (k : ℕ) (hk : Odd k) : IsPrimeDiff k ↔ (k + 2).Prime := by
  constructor
  · rintro ⟨p, q, hp, hq, rfl⟩
    have hq2 : q = 2 := by
      rcases hk with ⟨j, hj⟩
      have := hp.eq_two_or_odd
      have := hq.eq_two_or_odd
      have := hq.two_le
      omega
    simpa [hq2, Nat.add_comm] using hp
  · intro hp
    exact ⟨k + 2, 2, hp, Nat.prime_two, Nat.add_comm _ _⟩

private lemma even_gap (h1 : H1) (h2 : H2) (k : ℕ) (hk : 0 < k) (he : Even k) :
    IsPrimeDiff k := by
  by_cases h3 : (k + 3).Prime
  · exact ⟨k + 3, 3, h3, by decide, Nat.add_comm _ _⟩
  by_cases h5 : (k + 5).Prime
  · exact ⟨k + 5, 5, h5, by decide, Nat.add_comm _ _⟩
  by_cases hd : 3 ∣ k
  · obtain ⟨q, _, hq, hp⟩ := h1 k hk he hd h5
    exact ⟨q + k, q, hp, hq, rfl⟩
  · obtain ⟨q, _, _, hq, hp⟩ := h2 k hk he hd h3 h5
    exact ⟨q + k, q, hp, hq, rfl⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a007921.main := by
  intro h1 h2 k hk
  rcases k.even_or_odd with he | ho
  · constructor
    · intro h
      exact False.elim (h (even_gap h1 h2 k hk he))
    · intro h
      exact False.elim ((Nat.not_odd_iff_even.mpr he) h.1)
  · constructor
    · intro h
      exact ⟨ho, fun hp => h ((odd_gap k ho).mpr hp)⟩
    · intro h hgap
      exact h.2 ((odd_gap k ho).mp hgap)

private lemma prime_mod_three {p : ℕ} (hp : p.Prime) (h : 3 < p) : p % 3 ≠ 0 := by
  intro hz
  have heq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hp).mp
    (Nat.dvd_of_mod_eq_zero hz)
  omega

/-- A solution of the conjecture supplies exactly the witnesses required by both steps. -/
theorem converse (hall : type_of% @OMA.S_oeis_a007921.main) : H1 ∧ H2 := by
  have large_start (k : ℕ) (hk : 0 < k) (he : Even k)
      (h3 : ¬ (k + 3).Prime) (h5 : ¬ (k + 5).Prime) :
      ∃ q : ℕ, 7 ≤ q ∧ q.Prime ∧ (q + k).Prime := by
    have hgap : IsPrimeDiff k := by
      by_contra h
      exact (Nat.not_odd_iff_even.mpr he) ((hall k hk).mp h).1
    obtain ⟨p, q, hp, hq, rfl⟩ := hgap
    refine ⟨q, ?_, hq, hp⟩
    have hn3 : q ≠ 3 := fun h => h3 (by simpa [h, Nat.add_comm] using hp)
    have hn5 : q ≠ 5 := fun h => h5 (by simpa [h, Nat.add_comm] using hp)
    rcases he with ⟨t, ht⟩
    have := hq.eq_two_or_odd
    have := hp.eq_two_or_odd
    have := hq.two_le
    omega
  constructor
  · intro k hk he hd h5
    apply large_start k hk he _ h5
    intro hp
    have hdiv : 3 ∣ k + 3 := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hp).mp hdiv
    omega
  · intro k hk he hd h3 h5
    obtain ⟨q, h7, hq, hp⟩ := large_start k hk he h3 h5
    refine ⟨q, h7, ?_, hq, hp⟩
    have := prime_mod_three hq (by omega)
    have := prime_mod_three hp (by omega)
    omega

/-- For even `a`, some residue `r` and its translate `r + a` are both units modulo `m`. -/
private lemma coprime_pair (m a : ℕ) (hm : m ≠ 0) (ha : Even a) :
    ∃ r : ℕ, r.Coprime m ∧ (r + a).Coprime m := by
  -- For a prime divisor of m, exactly one of a and b is divisible by that prime.
  let S := m.primeFactors.filter (fun p => ¬ p ∣ a)
  let b := ∏ p ∈ S, p
  have hab : a.Coprime b := by
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    obtain ⟨hpM, hpa⟩ := Finset.mem_filter.mp hp
    exact ((Nat.prime_of_mem_primeFactors hpM).coprime_iff_not_dvd.mpr hpa).symm
  have aux (c : ℕ) (hc : c = 1 ∨ c = 2) : (b + c * a).Coprime m := by
    apply Nat.Coprime.symm
    refine Nat.coprime_of_dvd ?_
    intro p hp hpm hsum
    by_cases hpa : p ∣ a
    · have hpb : p ∣ b := (Nat.dvd_add_iff_left (dvd_mul_of_dvd_right hpa c)).mpr hsum
      exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpa hpb hab
    · have hps : p ∈ S := Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpm, hm⟩, hpa⟩
      have hpb : p ∣ b := Finset.dvd_prod_of_mem id hps
      have hprod : p ∣ c * a := (Nat.dvd_add_iff_right hpb).mpr hsum
      have hpc := (hp.dvd_mul.mp hprod).resolve_right hpa
      rcases hc with rfl | rfl
      · exact hp.not_dvd_one hpc
      · have hp2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpc
        exact hpa (hp2 ▸ ha.two_dvd)
  exact ⟨b + a, by simpa using aux 1 (Or.inl rfl),
    by simpa [two_mul, Nat.add_assoc] using aux 2 (Or.inr rfl)⟩

/-- In each residue class with an even representative modulo a positive modulus, there is a fixed
prime `q > B` and arbitrarily large even differences `k` with `q + k` prime. At the same time, every
`k + s` with `2 ≤ s ≤ B` is composite, so no such `s` can be the smaller prime. -/
theorem unbounded_minimum_start (m a B : ℕ) (hm : 0 < m) (ha : Even a) :
    ∃ q > B, q.Prime ∧ ∀ N : ℕ, ∃ k > N, Even k ∧ Nat.ModEq m k a ∧
      (q + k).Prime ∧ ∀ s : ℕ, 2 ≤ s → s ≤ B → ¬ (k + s).Prime := by
  -- If k is congruent to a modulo M, then a + s divides k + s for 2 ≤ s ≤ B.
  let M := m * (a + B).factorial
  have hM : M ≠ 0 := Nat.mul_ne_zero hm.ne' (Nat.factorial_ne_zero _)
  obtain ⟨r, hr, hra⟩ := coprime_pair M a hM ha
  -- Dirichlet gives one fixed smaller prime q and unbounded larger primes p.
  obtain ⟨q, hqB, hq, hqr⟩ := Nat.forall_exists_prime_gt_and_modEq (max B 2) hM hr
  refine ⟨q, by omega, hq, ?_⟩
  intro N
  obtain ⟨p, hpN, hp, hpr⟩ := Nat.forall_exists_prime_gt_and_modEq (q + max N a) hM hra
  let k := p - q
  have hqk : q + k = p := by dsimp [k]; omega
  have hkN : N < k := by dsimp [k]; omega
  have hka : a < k := by dsimp [k]; omega
  have hkM : Nat.ModEq M k a := hqr.add_left_cancel (hqk ▸ hpr)
  have he : Even k := by
    have := hq.eq_two_or_odd
    have := hp.eq_two_or_odd
    rw [Nat.even_iff]
    omega
  refine ⟨k, hkN, he, hkM.of_dvd (dvd_mul_right m _), hqk ▸ hp, ?_⟩
  intro s hs hsB hprime
  have hd : a + s ∣ M :=
    dvd_mul_of_dvd_right (Nat.dvd_factorial (by omega) (by omega)) m
  have hks : a + s ∣ k + s := ((hkM.add_right s).dvd_iff hd).mpr (dvd_refl _)
  have := hprime.eq_one_or_self_of_dvd _ hks
  omega

end OMA.R_oeis_a007921_R1
