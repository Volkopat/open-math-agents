import OMAReductions.R_oeis_a060318_R2

-- Step oeis-a060318.R2.H1: hypothesis H1 of reduction oeis-a060318.R2
-- Credit: @ptc-prover-bot
--
-- Proof idea. Write the three exponents as a < b < c. Since n > 8, c is at least 6.
-- Reducing modulo 729 = 3^6 (where 2 has order 486) fixes n mod 486 from the exponents
-- below 6. Then modulo the primes 7, 19, 73, 163, 487 (the order of 2 divides 486 for each,
-- and the order of 3 divides 972) the exponents mod 18, 36, 324 or 972 are tested by `decide`.
-- Every case is excluded.

namespace OMA.A060318H1

/-- Periodicity of powers modulo `m`. -/
theorem pow_mod_period (x L m k : ℕ) (hm : 1 < m) (h : x ^ L % m = 1) :
    x ^ k % m = x ^ (k % L) % m := by
  calc x ^ k % m = x ^ (L * (k / L) + k % L) % m := by rw [Nat.div_add_mod]
    _ = ((x ^ L) ^ (k / L) * x ^ (k % L)) % m := by rw [pow_add, pow_mul]
    _ = (((x ^ L) ^ (k / L) % m) * (x ^ (k % L) % m)) % m := Nat.mul_mod _ _ _
    _ = x ^ (k % L) % m := by
      rw [Nat.pow_mod (x ^ L) (k / L) m, h, one_pow, Nat.mod_eq_of_lt hm, one_mul, Nat.mod_mod]

/-- The residue test at the prime `p`. -/
abbrev G (p r A B C : ℕ) : Prop := 2 ^ r % p = (1 + 3 ^ A % p + 3 ^ B % p + 3 ^ C % p) % p

theorem modp (p L n a b c : ℕ) (hp : 1 < p) (h2 : 2 ^ 486 % p = 1) (h3 : 3 ^ L % p = 1)
    (h : 2 ^ n = 1 + 3 ^ a + 3 ^ b + 3 ^ c) : G p (n % 486) (a % L) (b % L) (c % L) := by
  unfold G
  rw [← pow_mod_period 2 486 p n hp h2, ← pow_mod_period 3 L p a hp h3,
    ← pow_mod_period 3 L p b hp h3, ← pow_mod_period 3 L p c hp h3, h]
  exact ((((Nat.ModEq.refl 1).add (Nat.mod_modEq (3 ^ a) p).symm).add
    (Nat.mod_modEq (3 ^ b) p).symm).add (Nat.mod_modEq (3 ^ c) p).symm)

theorem big (k : ℕ) (hk : 6 ≤ k) : 3 ^ k = 729 * 3 ^ (k - 6) := by
  rw [show (729 : ℕ) = 3 ^ 6 by norm_num, ← pow_add]
  congr 1
  omega

theorem two729 (n : ℕ) : 2 ^ n % 729 = 2 ^ (n % 486) % 729 :=
  pow_mod_period 2 486 729 n (by norm_num) (by decide +kernel)

theorem caseA : ∀ r ∈ List.range 486, 2 ^ r % 729 = 1 → ∀ A ∈ List.range 18,
    ∀ B ∈ List.range 18, ∀ C ∈ List.range 18, ¬ (G 7 r A B C ∧ G 19 r A B C) := by
  decide +kernel

theorem caseB36 : ∀ e ∈ ([0, 1, 3, 4, 5] : List ℕ), ∀ r < 486, 2 ^ r % 729 = (1 + 3 ^ e) % 729 →
    ∀ B < 36, ∀ C < 36, ¬ (G 7 r e B C ∧ G 19 r e B C ∧ G 73 r e B C) := by
  decide +kernel

theorem caseB2 : ∀ r ∈ List.range 486, 2 ^ r % 729 = (1 + 3 ^ 2) % 729 →
    ∀ B ∈ List.range 324, ∀ C ∈ List.range 324, ¬ (G 7 r 2 B C ∧ G 19 r 2 B C ∧ G 73 r 2 B C ∧ G 163 r 2 B C) := by
  decide +kernel

theorem caseC : ∀ a ∈ List.range 6, ∀ b ∈ List.range 6, a < b → ∀ r ∈ List.range 486,
    2 ^ r % 729 = (1 + 3 ^ a + 3 ^ b) % 729 → ∀ C ∈ List.range 972, ¬ (G 7 r a b C ∧ G 19 r a b C ∧ G 73 r a b C ∧ G 163 r a b C ∧ G 487 r a b C) := by
  decide +kernel

theorem core (n a b c : ℕ) (hab : a < b) (hbc : b < c) (hn : 9 ≤ n)
    (h : 2 ^ n = 1 + 3 ^ a + 3 ^ b + 3 ^ c) : False := by
  have h512 : 2 ^ 9 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hc6 : 6 ≤ c := by
    by_contra hc
    have ha3 : 3 ^ a ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb4 : 3 ^ b ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hc5 : 3 ^ c ≤ 3 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [h] at h512
    norm_num at h512 ha3 hb4 hc5
    omega
  have h729 := two729 n
  rw [h] at h729
  have hrn : n % 486 < 486 := Nat.mod_lt _ (by norm_num)
  rw [big c hc6] at h729
  rcases lt_or_ge a 6 with ha | ha
  · rcases lt_or_ge b 6 with hb | hb
    · -- exponents a < b < 6 are exact, c is large
      have e : (1 + 3 ^ a + 3 ^ b + 729 * 3 ^ (c - 6)) % 729 = (1 + 3 ^ a + 3 ^ b) % 729 :=
        Nat.add_mul_mod_self_left _ _ _
      rw [e] at h729
      refine caseC a (List.mem_range.mpr ha) b (List.mem_range.mpr hb) hab (n % 486)
        (List.mem_range.mpr hrn) h729.symm (c % 972)
        (List.mem_range.mpr (Nat.mod_lt _ (by norm_num))) ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := modp 7 972 n a b c (by norm_num) (by decide +kernel) (by decide +kernel) h
        rwa [Nat.mod_eq_of_lt (by omega : a < 972), Nat.mod_eq_of_lt (by omega : b < 972)] at this
      · have := modp 19 972 n a b c (by norm_num) (by decide +kernel) (by decide +kernel) h
        rwa [Nat.mod_eq_of_lt (by omega : a < 972), Nat.mod_eq_of_lt (by omega : b < 972)] at this
      · have := modp 73 972 n a b c (by norm_num) (by decide +kernel) (by decide +kernel) h
        rwa [Nat.mod_eq_of_lt (by omega : a < 972), Nat.mod_eq_of_lt (by omega : b < 972)] at this
      · have := modp 163 972 n a b c (by norm_num) (by decide +kernel) (by decide +kernel) h
        rwa [Nat.mod_eq_of_lt (by omega : a < 972), Nat.mod_eq_of_lt (by omega : b < 972)] at this
      · have := modp 487 972 n a b c (by norm_num) (by decide +kernel) (by decide +kernel) h
        rwa [Nat.mod_eq_of_lt (by omega : a < 972), Nat.mod_eq_of_lt (by omega : b < 972)] at this
    · -- a < 6 exact, b and c large
      rw [big b hb] at h729
      have e : (1 + 3 ^ a + 729 * 3 ^ (b - 6) + 729 * 3 ^ (c - 6)) % 729 = (1 + 3 ^ a) % 729 := by
        rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]
      rw [e] at h729
      by_cases ha2 : a = 2
      · subst ha2
        refine caseB2 (n % 486) (List.mem_range.mpr hrn) h729.symm (b % 324)
          (List.mem_range.mpr (Nat.mod_lt _ (by norm_num))) (c % 324)
          (List.mem_range.mpr (Nat.mod_lt _ (by norm_num))) ⟨?_, ?_, ?_, ?_⟩
        · exact modp 7 324 n 2 b c (by norm_num) (by decide +kernel) (by decide +kernel) h
        · exact modp 19 324 n 2 b c (by norm_num) (by decide +kernel) (by decide +kernel) h
        · exact modp 73 324 n 2 b c (by norm_num) (by decide +kernel) (by decide +kernel) h
        · exact modp 163 324 n 2 b c (by norm_num) (by decide +kernel) (by decide +kernel) h
      · have hmem : a ∈ ([0, 1, 3, 4, 5] : List ℕ) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          omega
        refine caseB36 a hmem (n % 486) hrn h729.symm (b % 36) (Nat.mod_lt _ (by norm_num))
          (c % 36) (Nat.mod_lt _ (by norm_num)) ⟨?_, ?_, ?_⟩
        · have := modp 7 36 n a b c (by norm_num) (by decide +kernel) (by decide +kernel) h
          rwa [Nat.mod_eq_of_lt (by omega : a < 36)] at this
        · have := modp 19 36 n a b c (by norm_num) (by decide +kernel) (by decide +kernel) h
          rwa [Nat.mod_eq_of_lt (by omega : a < 36)] at this
        · have := modp 73 36 n a b c (by norm_num) (by decide +kernel) (by decide +kernel) h
          rwa [Nat.mod_eq_of_lt (by omega : a < 36)] at this
  · -- all three exponents large
    rw [big b (by omega), big a ha] at h729
    have e : (1 + 729 * 3 ^ (a - 6) + 729 * 3 ^ (b - 6) + 729 * 3 ^ (c - 6)) % 729 = 1 := by
      rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]
    rw [e] at h729
    exact caseA (n % 486) (List.mem_range.mpr hrn) h729.symm (a % 18)
      (List.mem_range.mpr (Nat.mod_lt _ (by norm_num))) (b % 18)
      (List.mem_range.mpr (Nat.mod_lt _ (by norm_num))) (c % 18)
      (List.mem_range.mpr (Nat.mod_lt _ (by norm_num)))
      ⟨modp 7 18 n a b c (by norm_num) (by decide +kernel) (by decide +kernel) h,
        modp 19 18 n a b c (by norm_num) (by decide +kernel) (by decide +kernel) h⟩

theorem sorted (n x y z : ℕ) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hn : 9 ≤ n)
    (h : 2 ^ n = 1 + (3 ^ x + 3 ^ y + 3 ^ z)) : False := by
  rcases lt_trichotomy x y with h1 | h1 | h1 <;> rcases lt_trichotomy y z with h2 | h2 | h2 <;>
    rcases lt_trichotomy x z with h3 | h3 | h3
  all_goals first
    | omega
    | exact core n x y z h1 h2 hn (by rw [h]; ring)
    | exact core n x z y h3 (by omega) hn (by rw [h]; ring)
    | exact core n y x z h1 h3 hn (by rw [h]; ring)
    | exact core n y z x h2 h3 hn (by rw [h]; ring)
    | exact core n z x y h3 h1 hn (by rw [h]; ring)
    | exact core n z y x h2 h1 hn (by rw [h]; ring)

end OMA.A060318H1

theorem OMA.solution : OMA.R_oeis_a060318_R2.H1 := by
  intro s n hs hn heq
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hs
  rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
    Finset.sum_singleton] at heq
  exact OMA.A060318H1.sorted n x y z hxy hxz hyz (by omega) (by rw [heq]; ring)

