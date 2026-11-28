import OMAStatements.S_oeis_a058383

/-!
# Proof of `oeis-a058383` (Benoit Cloitre's conjecture on OEIS A058383)

For every `x ≥ 7`, both `φ(x)` and `φ(x - 1)` are even, which rules out `x % 6 ∈ {0, 2, 3, 5}`
since `(4 * x - 3) / 3` is odd in those residue classes. When `x % 6 = 4`, the bounds
`φ(2k) ≤ k` and `φ(3k) ≤ 2k` give `φ(x) + φ(x - 1) ≤ 7m + 4 < 8m + 4 = (4 * x - 3) / 3`.
When `x = 6m + 1`, `φ(x) ≤ 6m` (equality iff `x` is prime) and `φ(6m) ≤ 2m` (equality iff
`6m = 2^a * 3^b` with `a, b > 0`), yielding the exact characterization.
-/

-- Problem: A058383: Primes of form 1+(2^a)*(3^b), a>0, b>0.
-- Upstream: formal-conjectures statements/oeis-a058383.lean:0 (declaration OMA.S_oeis_a058383.main)
-- Credit: @umarsxlim

namespace OeisA058383Proof

lemma totient_two_mul_le : ∀ k : ℕ, (2 * k).totient ≤ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · simp
    · by_cases h2 : 2 ∣ k + 1
      · obtain ⟨j, hj⟩ := h2
        have hj_lt : j < k + 1 := by omega
        have hstep := Nat.totient_mul_of_prime_of_dvd Nat.prime_two (⟨j, hj⟩ : 2 ∣ k + 1)
        rw [hstep, hj]
        have := ih j hj_lt
        omega
      · have hstep := Nat.totient_mul_of_prime_of_not_dvd Nat.prime_two h2
        have hle := Nat.totient_le (k + 1)
        omega

lemma totient_three_mul_le : ∀ k : ℕ, (3 * k).totient ≤ 2 * k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · simp
    · by_cases h3 : 3 ∣ k + 1
      · obtain ⟨j, hj⟩ := h3
        have hj_lt : j < k + 1 := by omega
        have hstep := Nat.totient_mul_of_prime_of_dvd Nat.prime_three (⟨j, hj⟩ : 3 ∣ k + 1)
        rw [hstep, hj]
        have := ih j hj_lt
        omega
      · have hstep := Nat.totient_mul_of_prime_of_not_dvd Nat.prime_three h3
        have hle := Nat.totient_le (k + 1)
        omega

lemma totient_six_mul_le_and_eq :
    ∀ m : ℕ, 1 ≤ m →
      (6 * m).totient ≤ 2 * m ∧
      ((6 * m).totient = 2 * m → ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 6 * m = 2 ^ a * 3 ^ b) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases hm1 : m = 1
    · subst hm1
      have h6 : (6 * 1).totient = 2 := by decide
      exact ⟨by omega, fun _ => ⟨1, 1, by omega, by omega, by norm_num⟩⟩
    · by_cases h2 : 2 ∣ m
      · obtain ⟨j, rfl⟩ := h2
        have hj1 : 1 ≤ j := by omega
        have hjlt : j < 2 * j := by omega
        obtain ⟨hle, heq⟩ := ih j hjlt hj1
        have hrew : 6 * (2 * j) = 2 * (6 * j) := by ring
        have hdvd : 2 ∣ 6 * j := ⟨3 * j, by ring⟩
        have htot : (6 * (2 * j)).totient = 2 * (6 * j).totient := by
          rw [hrew, Nat.totient_mul_of_prime_of_dvd Nat.prime_two hdvd]
        refine ⟨by omega, fun h => ?_⟩
        obtain ⟨a, b, ha, hb, hab⟩ := heq (by omega)
        refine ⟨a + 1, b, by omega, hb, ?_⟩
        calc 6 * (2 * j) = 2 * (6 * j) := by ring
          _ = 2 * (2 ^ a * 3 ^ b) := by rw [hab]
          _ = 2 ^ (a + 1) * 3 ^ b := by ring
      · by_cases h3 : 3 ∣ m
        · obtain ⟨j, rfl⟩ := h3
          have hj1 : 1 ≤ j := by omega
          have hjlt : j < 3 * j := by omega
          obtain ⟨hle, heq⟩ := ih j hjlt hj1
          have hrew : 6 * (3 * j) = 3 * (6 * j) := by ring
          have hdvd : 3 ∣ 6 * j := ⟨2 * j, by ring⟩
          have htot : (6 * (3 * j)).totient = 3 * (6 * j).totient := by
            rw [hrew, Nat.totient_mul_of_prime_of_dvd Nat.prime_three hdvd]
          refine ⟨by omega, fun h => ?_⟩
          obtain ⟨a, b, ha, hb, hab⟩ := heq (by omega)
          refine ⟨a, b + 1, ha, by omega, ?_⟩
          calc 6 * (3 * j) = 3 * (6 * j) := by ring
            _ = 3 * (2 ^ a * 3 ^ b) := by rw [hab]
            _ = 2 ^ a * 3 ^ (b + 1) := by ring
        · have hcop2 : Nat.Coprime 2 m := Nat.prime_two.coprime_iff_not_dvd.mpr h2
          have hcop3 : Nat.Coprime 3 m := Nat.prime_three.coprime_iff_not_dvd.mpr h3
          have hcop6 : Nat.Coprime 6 m := by
            rw [show (6 : ℕ) = 2 * 3 by norm_num]
            exact hcop2.mul_left hcop3
          have htot : (6 * m).totient = 2 * m.totient := by
            rw [Nat.totient_mul hcop6]
            have : (6 : ℕ).totient = 2 := by decide
            rw [this]
          have hlt : m.totient < m := Nat.totient_lt m (by omega)
          exact ⟨by omega, fun h => by omega⟩

lemma totient_two_pow_mul_three_pow {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    3 * (2 ^ a * 3 ^ b).totient = 2 ^ a * 3 ^ b := by
  have hcop : Nat.Coprime (2 ^ a) (3 ^ b) := (by decide : Nat.Coprime 2 3).pow a b
  rw [Nat.totient_mul hcop, Nat.totient_prime_pow Nat.prime_two ha,
    Nat.totient_prime_pow Nat.prime_three hb]
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  change 3 * (2 ^ a' * 1 * (3 ^ b' * 2)) = 2 ^ (a' + 1) * 3 ^ (b' + 1)
  ring

end OeisA058383Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a058383.main := by
  intro x hx
  constructor
  · intro heq
    obtain ⟨u, hu⟩ := Nat.totient_even (by omega : 3 ≤ x)
    obtain ⟨v, hv⟩ := Nat.totient_even (by omega : 3 ≤ x - 1)
    have hmod : x % 6 = 0 ∨ x % 6 = 1 ∨ x % 6 = 2 ∨ x % 6 = 3 ∨ x % 6 = 4 ∨ x % 6 = 5 := by
      omega
    rcases hmod with hr | hr | hr | hr | hr | hr
    · omega
    · set m := x / 6
      have hx_eq : x = 6 * m + 1 := by omega
      have hxm1 : x - 1 = 6 * m := by omega
      have hm1 : 1 ≤ m := by omega
      have h1 : x.totient < x := Nat.totient_lt x (by omega)
      obtain ⟨h2le, h2eq⟩ := OeisA058383Proof.totient_six_mul_le_and_eq m hm1
      rw [hxm1] at heq
      have hxt : x.totient = x - 1 := by omega
      have h6t : (6 * m).totient = 2 * m := by omega
      have hprime : x.Prime := (Nat.totient_eq_iff_prime (by omega)).mp hxt
      obtain ⟨a, b, ha, hb, hab⟩ := h2eq h6t
      exact ⟨hprime, a, b, ha, hb, by omega⟩
    · omega
    · omega
    · set m := x / 6
      have hx_eq : x = 2 * (3 * m + 2) := by omega
      have hxm1 : x - 1 = 3 * (2 * m + 1) := by omega
      have hm1 : 1 ≤ m := by omega
      have h1 : x.totient ≤ 3 * m + 2 := by
        rw [hx_eq]
        exact OeisA058383Proof.totient_two_mul_le (3 * m + 2)
      have h2 : (x - 1).totient ≤ 2 * (2 * m + 1) := by
        rw [hxm1]
        exact OeisA058383Proof.totient_three_mul_le (2 * m + 1)
      omega
    · omega
  · rintro ⟨hp, a, b, ha, hb, rfl⟩
    rw [Nat.totient_prime hp]
    simp only [Nat.add_sub_cancel_left]
    have htot := OeisA058383Proof.totient_two_pow_mul_three_pow ha hb
    omega
