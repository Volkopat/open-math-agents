import OMAStatements.S_oeis_a051250

-- Problem: OEIS A051250, Zumkeller's conjecture: 60 is the largest number whose reduced
-- residue system consists of 1 and prime powers only
-- Statement: statements/oeis-a051250.lean (declaration OMA.S_oeis_a051250.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let n > 60 be a term, and let p < q be the two least primes that do not divide n.
-- The number p q is coprime to n and is not a prime power, so n < p q. Each prime below q
-- other than p divides n, so the product of the primes below q divides p n, and it is less
-- than p^2 q < q^3. But the product of the primes up to x is at least (x + 1)^3 for x >= 12
-- (by Bertrand's postulate and induction), so q <= 11, p <= 7 and n < 77. For 61 <= n <= 76 a
-- product of two primes that is coprime to n is a counterexample.

namespace OMA.A051250

open Finset

/-- Every k in the reduced residue system of n is 1 or a prime power. -/
def IsTerm' (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ n → Nat.Coprime k n → k = 1 ∨ IsPrimePow k

lemma primorial_mono {x y : ℕ} (h : x ≤ y) : primorial x ≤ primorial y := by
  unfold primorial
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  · intro p hp _
    exact (Finset.mem_filter.mp hp).2.one_le

/-- The primorial grows faster than the cube. -/
lemma primorial_ge (x : ℕ) (hx : 12 ≤ x) : (x + 1) ^ 3 ≤ primorial x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases h24 : x < 24
    · by_cases h12 : x = 12
      · subst h12
        decide
      · have h13 : primorial 13 ≤ primorial x := primorial_mono (by omega)
        have hv : (24 : ℕ) ^ 3 ≤ primorial 13 := by decide
        have hle : (x + 1) ^ 3 ≤ 24 ^ 3 := Nat.pow_le_pow_left (by omega) 3
        omega
    · set y := x / 2 with hy
      have hy12 : 12 ≤ y := by omega
      have ihy := ih y (by omega) hy12
      obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul y (by omega)
      have hpx : p ≤ x := by omega
      have hmul : primorial y * p ≤ primorial x := by
        have hdis : p ∉ (range (y + 1)).filter Nat.Prime := by
          simp only [mem_filter, mem_range, not_and]
          intro h
          omega
        have hsub : insert p ((range (y + 1)).filter Nat.Prime)
            ⊆ (range (x + 1)).filter Nat.Prime := by
          intro r hr
          rcases Finset.mem_insert.mp hr with rfl | hr
          · simp only [mem_filter, mem_range]
            exact ⟨by omega, hp⟩
          · simp only [mem_filter, mem_range] at hr ⊢
            exact ⟨by omega, hr.2⟩
        have h1 : ∏ r ∈ insert p ((range (y + 1)).filter Nat.Prime), r ≤ primorial x := by
          unfold primorial
          apply Finset.prod_le_prod_of_subset_of_one_le' hsub
          intro r hr _
          exact (Finset.mem_filter.mp hr).2.one_le
        rw [Finset.prod_insert hdis] at h1
        unfold primorial at h1 ⊢
        rw [mul_comm]
        exact h1
      have h8 : (x + 1) ^ 3 ≤ 8 * (y + 1) ^ 3 := by
        have : x + 1 ≤ 2 * (y + 1) := by omega
        calc (x + 1) ^ 3 ≤ (2 * (y + 1)) ^ 3 := Nat.pow_le_pow_left this 3
          _ = 8 * (y + 1) ^ 3 := by ring
      calc (x + 1) ^ 3 ≤ 8 * (y + 1) ^ 3 := h8
        _ ≤ p * (y + 1) ^ 3 := Nat.mul_le_mul_right _ (by omega)
        _ ≤ p * primorial y := Nat.mul_le_mul_left _ ihy
        _ = primorial y * p := by ring
        _ ≤ primorial x := hmul

lemma not_primePow_mul (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ¬ IsPrimePow (p * q) := by
  rw [isPrimePow_iff_unique_prime_dvd]
  rintro ⟨r, -, hr⟩
  have h1 := hr p ⟨hp, Dvd.intro q rfl⟩
  have h2 := hr q ⟨hq, Dvd.intro_left p rfl⟩
  exact hpq (h1.trans h2.symm)

theorem upper (n : ℕ) (hn : 1 ≤ n) (hterm : IsTerm' n) : n ≤ 60 := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  -- the two least primes that do not divide `n`
  have hex1 : ∃ p : ℕ, p.Prime ∧ ¬ p ∣ n := by
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (n + 1)
    exact ⟨p, hp2, fun h => by have := Nat.le_of_dvd (by omega) h; omega⟩
  obtain ⟨p, ⟨hp, hpn⟩, hpmin'⟩ : ∃ p : ℕ, (p.Prime ∧ ¬ p ∣ n) ∧
      ∀ r : ℕ, r < p → ¬ (r.Prime ∧ ¬ r ∣ n) :=
    ⟨Nat.find hex1, Nat.find_spec hex1, fun r hr => Nat.find_min hex1 hr⟩
  have hpmin : ∀ r : ℕ, r.Prime → r < p → r ∣ n := by
    intro r hr hlt
    by_contra h
    exact hpmin' r hlt ⟨hr, h⟩
  have hex2 : ∃ q : ℕ, q.Prime ∧ p < q ∧ ¬ q ∣ n := by
    obtain ⟨q, hq1, hq2⟩ := Nat.exists_infinite_primes (n + p + 1)
    exact ⟨q, hq2, by omega, fun h => by have := Nat.le_of_dvd (by omega) h; omega⟩
  obtain ⟨q, ⟨hq, hpq, hqn⟩, hqmin'⟩ : ∃ q : ℕ, (q.Prime ∧ p < q ∧ ¬ q ∣ n) ∧
      ∀ r : ℕ, r < q → ¬ (r.Prime ∧ p < r ∧ ¬ r ∣ n) :=
    ⟨Nat.find hex2, Nat.find_spec hex2, fun r hr => Nat.find_min hex2 hr⟩
  have hqmin : ∀ r : ℕ, r.Prime → p < r → r < q → r ∣ n := by
    intro r hr h1 h2
    by_contra h
    exact hqmin' r h2 ⟨hr, h1, h⟩
  -- `n < p * q`
  have hnpq : n < p * q := by
    by_contra hle
    rw [not_lt] at hle
    have hcop : Nat.Coprime (p * q) n :=
      Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn)
        ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqn)
    have h2 : 2 ≤ p := hp.two_le
    have h3 : 2 ≤ q := hq.two_le
    rcases hterm (p * q) (by nlinarith) hle hcop with h1 | h1
    · nlinarith
    · exact not_primePow_mul p q hp hq (by omega) h1
  -- the primorial of `q - 1` divides `p * n`
  have hdvd : primorial (q - 1) ∣ p * n := by
    unfold primorial
    have hpmem : p ∈ (range (q - 1 + 1)).filter Nat.Prime := by
      simp only [mem_filter, mem_range]
      exact ⟨by omega, hp⟩
    rw [← Finset.mul_prod_erase _ _ hpmem]
    apply Nat.mul_dvd_mul_left
    apply Finset.prod_primes_dvd
    · intro r hr
      exact Nat.prime_iff.mp (Finset.mem_filter.mp (Finset.mem_of_mem_erase hr)).2
    · intro r hr
      have hrp : r ≠ p := Finset.ne_of_mem_erase hr
      have hr2 := Finset.mem_filter.mp (Finset.mem_of_mem_erase hr)
      have hrq : r < q := by
        have := Finset.mem_range.mp hr2.1
        omega
      rcases Nat.lt_or_gt_of_ne hrp with h | h
      · exact hpmin r hr2.2 h
      · exact hqmin r hr2.2 h hrq
  have hle : primorial (q - 1) ≤ p * n :=
    Nat.le_of_dvd (Nat.mul_pos hp.pos (by omega)) hdvd
  have hq11 : q ≤ 11 := by
    by_contra hq12
    rw [not_le] at hq12
    have h13 : 13 ≤ q := by
      by_contra h
      have : q = 12 := by omega
      rw [this] at hq
      norm_num at hq
    have hge := primorial_ge (q - 1) (by omega)
    rw [show q - 1 + 1 = q by omega] at hge
    have h1 : p * n < p * (p * q) := Nat.mul_lt_mul_of_pos_left hnpq hp.pos
    have h2 : p * (p * q) ≤ q * (q * q) := by
      have : p ≤ q := hpq.le
      calc p * (p * q) ≤ q * (p * q) := Nat.mul_le_mul_right _ this
        _ ≤ q * (q * q) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ this)
    have h3 : q ^ 3 = q * (q * q) := by ring
    omega
  have hp7 : p ≤ 7 := by
    by_contra hp8
    rw [not_le] at hp8
    have : p = 8 ∨ p = 9 ∨ p = 10 := by omega
    rcases this with h | h | h <;> rw [h] at hp <;> norm_num at hp
  have hn77 : n < 77 := by
    have : p * q ≤ 7 * 11 := Nat.mul_le_mul hp7 hq11
    omega
  clear hpmin hqmin hpmin' hqmin' hdvd hle hex1 hex2 hnpq
  interval_cases n
  · rcases hterm (2 * 3) (by norm_num) (by norm_num) (by decide) with h | h
    · norm_num at h
    · exact not_primePow_mul 2 3 (by norm_num) (by norm_num) (by norm_num) h
  · rcases hterm (3 * 5) (by norm_num) (by norm_num) (by decide) with h | h
    · norm_num at h
    · exact not_primePow_mul 3 5 (by norm_num) (by norm_num) (by norm_num) h
  · rcases hterm (2 * 5) (by norm_num) (by norm_num) (by decide) with h | h
    · norm_num at h
    · exact not_primePow_mul 2 5 (by norm_num) (by norm_num) (by norm_num) h
  · rcases hterm (3 * 5) (by norm_num) (by norm_num) (by decide) with h | h
    · norm_num at h
    · exact not_primePow_mul 3 5 (by norm_num) (by norm_num) (by norm_num) h
  · rcases hterm (2 * 3) (by norm_num) (by norm_num) (by decide) with h | h
    · norm_num at h
    · exact not_primePow_mul 2 3 (by norm_num) (by norm_num) (by norm_num) h
  · rcases hterm (5 * 7) (by norm_num) (by norm_num) (by decide) with h | h
    · norm_num at h
    · exact not_primePow_mul 5 7 (by norm_num) (by norm_num) (by norm_num) h
  · rcases hterm (2 * 3) (by norm_num) (by norm_num) (by decide) with h | h
    · norm_num at h
    · exact not_primePow_mul 2 3 (by norm_num) (by norm_num) (by norm_num) h
  · rcases hterm (3 * 5) (by norm_num) (by norm_num) (by decide) with h | h
    · norm_num at h
    · exact not_primePow_mul 3 5 (by norm_num) (by norm_num) (by norm_num) h
  · rcases hterm (2 * 5) (by norm_num) (by norm_num) (by decide) with h | h
    · norm_num at h
    · exact not_primePow_mul 2 5 (by norm_num) (by norm_num) (by norm_num) h
  · rcases hterm (3 * 11) (by norm_num) (by norm_num) (by decide) with h | h
    · norm_num at h
    · exact not_primePow_mul 3 11 (by norm_num) (by norm_num) (by norm_num) h
  · rcases hterm (2 * 3) (by norm_num) (by norm_num) (by decide) with h | h
    · norm_num at h
    · exact not_primePow_mul 2 3 (by norm_num) (by norm_num) (by norm_num) h
  · rcases hterm (5 * 7) (by norm_num) (by norm_num) (by decide) with h | h
    · norm_num at h
    · exact not_primePow_mul 5 7 (by norm_num) (by norm_num) (by norm_num) h
  · rcases hterm (2 * 3) (by norm_num) (by norm_num) (by decide) with h | h
    · norm_num at h
    · exact not_primePow_mul 2 3 (by norm_num) (by norm_num) (by norm_num) h
  · rcases hterm (3 * 5) (by norm_num) (by norm_num) (by decide) with h | h
    · norm_num at h
    · exact not_primePow_mul 3 5 (by norm_num) (by norm_num) (by norm_num) h
  · rcases hterm (2 * 7) (by norm_num) (by norm_num) (by decide) with h | h
    · norm_num at h
    · exact not_primePow_mul 2 7 (by norm_num) (by norm_num) (by norm_num) h
  · rcases hterm (3 * 5) (by norm_num) (by norm_num) (by decide) with h | h
    · norm_num at h
    · exact not_primePow_mul 3 5 (by norm_num) (by norm_num) (by norm_num) h

theorem term60 : IsTerm' 60 := by
  intro k hk1 hk hc
  interval_cases k
  · exact Or.inl rfl
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact Or.inr (Nat.prime_iff.mp (by norm_num : Nat.Prime 7)).isPrimePow
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact Or.inr (Nat.prime_iff.mp (by norm_num : Nat.Prime 11)).isPrimePow
  · exact absurd hc (by decide)
  · exact Or.inr (Nat.prime_iff.mp (by norm_num : Nat.Prime 13)).isPrimePow
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact Or.inr (Nat.prime_iff.mp (by norm_num : Nat.Prime 17)).isPrimePow
  · exact absurd hc (by decide)
  · exact Or.inr (Nat.prime_iff.mp (by norm_num : Nat.Prime 19)).isPrimePow
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact Or.inr (Nat.prime_iff.mp (by norm_num : Nat.Prime 23)).isPrimePow
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact Or.inr (Nat.prime_iff.mp (by norm_num : Nat.Prime 29)).isPrimePow
  · exact absurd hc (by decide)
  · exact Or.inr (Nat.prime_iff.mp (by norm_num : Nat.Prime 31)).isPrimePow
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact Or.inr (Nat.prime_iff.mp (by norm_num : Nat.Prime 37)).isPrimePow
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact Or.inr (Nat.prime_iff.mp (by norm_num : Nat.Prime 41)).isPrimePow
  · exact absurd hc (by decide)
  · exact Or.inr (Nat.prime_iff.mp (by norm_num : Nat.Prime 43)).isPrimePow
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact Or.inr (Nat.prime_iff.mp (by norm_num : Nat.Prime 47)).isPrimePow
  · exact absurd hc (by decide)
  · right
    have h7 : IsPrimePow (7 ^ 2) :=
      (Nat.prime_iff.mp (by norm_num : Nat.Prime 7)).isPrimePow.pow (by norm_num)
    simpa using h7
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact Or.inr (Nat.prime_iff.mp (by norm_num : Nat.Prime 53)).isPrimePow
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact Or.inr (Nat.prime_iff.mp (by norm_num : Nat.Prime 59)).isPrimePow
  · exact absurd hc (by decide)

theorem result : IsTerm' 60 ∧ ∀ n : ℕ, 1 ≤ n → IsTerm' n → n ≤ 60 :=
  ⟨term60, upper⟩

theorem final : IsGreatest {n : ℕ | OMA.S_oeis_a051250.IsTerm n} 60 := by
  constructor
  · refine ⟨by norm_num, ?_⟩
    intro k hk1 hk hc
    rcases term60 k (by omega) (by omega) hc with h | h
    · omega
    · exact h
  · intro n hn
    obtain ⟨hpos, hall⟩ := hn
    apply upper n hpos
    intro k hk1 hkn hc
    by_cases h1 : k = 1
    · exact Or.inl h1
    · by_cases hk : k = n
      · subst hk
        have := (Nat.coprime_self k).mp hc
        exact Or.inl this
      · exact Or.inr (hall k (by omega) (by omega) hc)

end OMA.A051250

theorem OMA.solution : type_of% @OMA.S_oeis_a051250.main :=
  OMA.A051250.final
