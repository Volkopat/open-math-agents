import OMAReductions.R_oeis_a004432_R1

/-!
# Reduction of `oeis-a004432.R1.H1` (odd exceptional cores) to squarefree congruence classes

Every odd integer `s` factors as `s = k ^ 2 * m` with `m` squarefree and `k` odd. If `s` is a
sum of three squares, then `s % 8 ∈ {1, 3, 5}`, and since `k ^ 2 % 8 = 1`, we have
`m % 8 ∈ {1, 3, 5}` as well. Because `IsSumOfThreeDistinctNonzeroSquares` is preserved under
multiplication by nonzero squares, any odd non-representable `s = k ^ 2 * m` forces its
squarefree core `m` to be non-representable as well, hence one of the 24 squarefree odd cores
in `exceptions`, partitioned by residue modulo 8 into `H1`, `H2`, and `H3`.

Inside `main`, we completely classify all odd `{3, 5}`-smooth square multiples of all 24 cores
(showing only `9, 25, 27, 99` remain in `exceptions`, with explicit witnesses ruling out all
other multiples `9 * m`, `25 * m`, `81 * m`, `225`, `625`) and isolate the prime-square
multiplication theorem for primes `p ≥ 7` as `H4`.

Note: `oeis-a004432.R1.H1` is open unconditionally (Halter-Koch, *Acta Arithmetica* 42 (1982),
11–20 proved completeness up to at most one large exception, conditional on GRH / absence of a
Siegel zero). `H1`, `H2`, `H3` separate the three arithmetic regimes modulo 8 (`m ≡ 5 (mod 8)`
admits only `y^2 + z^2`, `m ≡ 3 (mod 8)` only `x^2 + 2y^2`, `m ≡ 1 (mod 8)` both), while `H4`
is a self-contained elementary theorem provable via Lagrange's four-square theorem.

Credit: @Rickxscz
-/

namespace OMA.R_oeis_a004432_R1_H1_R1

open OMA.S_oeis_a004432

/-- Squarefree cores `s ≡ 1 (mod 8)` that are not sums of three distinct nonzero squares
must belong to the 9 listed exceptions. -/
def H1 : Prop :=
  ∀ s : ℕ, Squarefree s → s % 8 = 1 →
    ¬ IsSumOfThreeDistinctNonzeroSquares s →
      s ∈ ({1, 17, 33, 57, 73, 97, 177, 193, 697} : Finset ℕ)

/-- Squarefree cores `s ≡ 3 (mod 8)` that are not sums of three distinct nonzero squares
must belong to the 11 listed exceptions. -/
def H2 : Prop :=
  ∀ s : ℕ, Squarefree s → s % 8 = 3 →
    ¬ IsSumOfThreeDistinctNonzeroSquares s →
      s ∈ ({3, 11, 19, 43, 51, 67, 123, 163, 187, 267, 627} : Finset ℕ)

/-- Squarefree cores `s ≡ 5 (mod 8)` that are not sums of three distinct nonzero squares
must belong to the 4 listed exceptions. -/
def H3 : Prop :=
  ∀ s : ℕ, Squarefree s → s % 8 = 5 →
    ¬ IsSumOfThreeDistinctNonzeroSquares s →
      s ∈ ({5, 13, 37, 85} : Finset ℕ)

/-- Multiplying any of the 24 squarefree odd cores by `p ^ 2` for a prime `p ≥ 7` always yields
a sum of three distinct nonzero squares. -/
def H4 : Prop :=
  ∀ p : ℕ, p.Prime → 7 ≤ p →
    ∀ m ∈ ({1, 3, 5, 11, 13, 17, 19, 33, 37, 43, 51, 57, 67, 73, 85, 97,
            123, 163, 177, 187, 193, 267, 627, 697} : Finset ℕ),
      IsSumOfThreeDistinctNonzeroSquares (p ^ 2 * m)

section Proof

private lemma odd_sum_three_squares_mod_eight {s : ℕ} (hodd : s % 2 = 1)
    (h3 : IsSumOfThreeSquares s) :
    s % 8 = 1 ∨ s % 8 = 3 ∨ s % 8 = 5 := by
  obtain ⟨a, b, c, rfl⟩ := h3
  have table : ∀ x y z : Fin 8,
      (x.val ^ 2 + y.val ^ 2 + z.val ^ 2) % 8 ≠ 7 := by decide
  have hm := (((Nat.mod_modEq a 8).pow 2).add ((Nat.mod_modEq b 8).pow 2)).add
    ((Nat.mod_modEq c 8).pow 2)
  change _ % 8 = (a ^ 2 + b ^ 2 + c ^ 2) % 8 at hm
  have hne7 : (a ^ 2 + b ^ 2 + c ^ 2) % 8 ≠ 7 := by
    rw [← hm]
    exact table ⟨a % 8, Nat.mod_lt _ (by decide)⟩
      ⟨b % 8, Nat.mod_lt _ (by decide)⟩ ⟨c % 8, Nat.mod_lt _ (by decide)⟩
  omega

private lemma scale_distinct {k m : ℕ} (hk : 0 < k)
    (hm : IsSumOfThreeDistinctNonzeroSquares m) :
    IsSumOfThreeDistinctNonzeroSquares (k ^ 2 * m) := by
  obtain ⟨a, b, c, ha, hab, hbc, rfl⟩ := hm
  refine ⟨k * a, k * b, k * c, Nat.mul_pos hk ha,
    Nat.mul_lt_mul_of_pos_left hab hk, Nat.mul_lt_mul_of_pos_left hbc hk, ?_⟩
  ring

private lemma odd_sq_mod_eight {k : ℕ} (hk : k % 2 = 1) : k ^ 2 % 8 = 1 := by
  have hm : (k % 8) ^ 2 % 8 = k ^ 2 % 8 := (Nat.mod_modEq k 8).pow 2
  rw [← hm]
  have h8 : k % 8 = 1 ∨ k % 8 = 3 ∨ k % 8 = 5 ∨ k % 8 = 7 := by omega
  rcases h8 with h | h | h | h <;> rw [h] <;> decide

private lemma sqfree_mul_sq (s : ℕ) (hs : 0 < s) :
    ∃ k m : ℕ, 0 < k ∧ Squarefree m ∧ s = k ^ 2 * m := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    by_cases hsf : Squarefree s
    · exact ⟨1, s, by omega, hsf, by ring⟩
    · rw [Squarefree] at hsf
      push Not at hsf
      obtain ⟨x, hx, hnu⟩ := hsf
      have hx0 : x ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hx
        exact absurd (zero_dvd_iff.mp hx) (by omega)
      have hx1 : x ≠ 1 := fun h1 => hnu (by rw [h1]; exact isUnit_one)
      have hx2 : 2 ≤ x := by omega
      obtain ⟨t, ht⟩ := hx
      have ht0 : 0 < t := by
        by_contra! h
        have : t = 0 := by omega
        rw [this, mul_zero] at ht
        omega
      have hts : t < s := by
        have h4 : 4 ≤ x * x := by nlinarith
        nlinarith
      obtain ⟨k', m, hk', hmsf, hteq⟩ := ih t hts ht0
      refine ⟨x * k', m, Nat.mul_pos (by omega) hk', hmsf, ?_⟩
      rw [ht, hteq]
      ring

private lemma three_five_smooth_or_ge_seven (k : ℕ) (hk : 0 < k) (hodd : k % 2 = 1) :
    (∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧ p ∣ k) ∨ (∃ a b : ℕ, k = 3 ^ a * 5 ^ b) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk1 : k = 1
    · exact Or.inr ⟨0, 0, by simp [hk1]⟩
    · have hp : k.minFac.Prime := Nat.minFac_prime hk1
      have hdvd : k.minFac ∣ k := Nat.minFac_dvd k
      have hne2 : k.minFac ≠ 2 := by
        intro h2
        rw [h2] at hdvd
        omega
      by_cases h3 : k.minFac = 3
      · rw [h3] at hdvd
        obtain ⟨k', rfl⟩ := hdvd
        have hk'0 : 0 < k' := by omega
        have hk'lt : k' < 3 * k' := by omega
        have hk'odd : k' % 2 = 1 := by omega
        rcases ih k' hk'lt hk'0 hk'odd with ⟨p, hpp, hp7, hpk'⟩ | ⟨a, b, rfl⟩
        · exact Or.inl ⟨p, hpp, hp7, dvd_mul_of_dvd_right hpk' 3⟩
        · exact Or.inr ⟨a + 1, b, by rw [pow_succ', mul_assoc]⟩
      · by_cases h5 : k.minFac = 5
        · rw [h5] at hdvd
          obtain ⟨k', rfl⟩ := hdvd
          have hk'0 : 0 < k' := by omega
          have hk'lt : k' < 5 * k' := by omega
          have hk'odd : k' % 2 = 1 := by omega
          rcases ih k' hk'lt hk'0 hk'odd with ⟨p, hpp, hp7, hpk'⟩ | ⟨a, b, rfl⟩
          · exact Or.inl ⟨p, hpp, hp7, dvd_mul_of_dvd_right hpk' 5⟩
          · exact Or.inr ⟨a, b + 1, by rw [pow_succ', mul_left_comm]⟩
        · have hge2 : 2 ≤ k.minFac := hp.two_le
          have hne4 : k.minFac ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by decide)
          have hne6 : k.minFac ≠ 6 := fun h => by rw [h] at hp; exact absurd hp (by decide)
          exact Or.inl ⟨k.minFac, hp, by omega, hdvd⟩

private lemma mul_nine_distinct {m : ℕ}
    (hm : m ∈ ({5, 13, 17, 19, 33, 37, 43, 51, 57, 67, 73, 85, 97,
                123, 163, 177, 187, 193, 267, 627, 697} : Finset ℕ)) :
    IsSumOfThreeDistinctNonzeroSquares (9 * m) := by
  fin_cases hm
  all_goals first
  | exact ⟨2, 4, 5, by decide, by decide, by decide, by decide⟩
  | exact ⟨1, 4, 10, by decide, by decide, by decide, by decide⟩
  | exact ⟨2, 7, 10, by decide, by decide, by decide, by decide⟩
  | exact ⟨1, 7, 11, by decide, by decide, by decide, by decide⟩
  | exact ⟨1, 10, 14, by decide, by decide, by decide, by decide⟩
  | exact ⟨4, 11, 14, by decide, by decide, by decide, by decide⟩
  | exact ⟨1, 5, 19, by decide, by decide, by decide, by decide⟩
  | exact ⟨1, 13, 17, by decide, by decide, by decide, by decide⟩
  | exact ⟨2, 5, 22, by decide, by decide, by decide, by decide⟩
  | exact ⟨5, 7, 23, by decide, by decide, by decide, by decide⟩
  | exact ⟨1, 16, 20, by decide, by decide, by decide, by decide⟩
  | exact ⟨2, 19, 20, by decide, by decide, by decide, by decide⟩
  | exact ⟨1, 14, 26, by decide, by decide, by decide, by decide⟩
  | exact ⟨5, 11, 31, by decide, by decide, by decide, by decide⟩
  | exact ⟨1, 25, 29, by decide, by decide, by decide, by decide⟩
  | exact ⟨7, 10, 38, by decide, by decide, by decide, by decide⟩
  | exact ⟨5, 17, 37, by decide, by decide, by decide, by decide⟩
  | exact ⟨2, 17, 38, by decide, by decide, by decide, by decide⟩
  | exact ⟨5, 13, 47, by decide, by decide, by decide, by decide⟩
  | exact ⟨5, 17, 73, by decide, by decide, by decide, by decide⟩
  | exact ⟨2, 37, 70, by decide, by decide, by decide, by decide⟩

private lemma mul_twentyfive_distinct {m : ℕ}
    (hm : m ∈ ({3, 5, 11, 13, 17, 19, 33, 37, 43, 51, 57, 67, 73, 85, 97,
                123, 163, 177, 187, 193, 267, 627, 697} : Finset ℕ)) :
    IsSumOfThreeDistinctNonzeroSquares (25 * m) := by
  fin_cases hm
  all_goals first
  | exact ⟨1, 5, 7, by decide, by decide, by decide, by decide⟩
  | exact ⟨3, 4, 10, by decide, by decide, by decide, by decide⟩
  | exact ⟨1, 7, 15, by decide, by decide, by decide, by decide⟩
  | exact ⟨6, 8, 15, by decide, by decide, by decide, by decide⟩
  | exact ⟨1, 10, 18, by decide, by decide, by decide, by decide⟩
  | exact ⟨3, 5, 21, by decide, by decide, by decide, by decide⟩
  | exact ⟨2, 14, 25, by decide, by decide, by decide, by decide⟩
  | exact ⟨3, 4, 30, by decide, by decide, by decide, by decide⟩
  | exact ⟨3, 15, 29, by decide, by decide, by decide, by decide⟩
  | exact ⟨1, 7, 35, by decide, by decide, by decide, by decide⟩
  | exact ⟨1, 20, 32, by decide, by decide, by decide, by decide⟩
  | exact ⟨3, 21, 35, by decide, by decide, by decide, by decide⟩
  | exact ⟨5, 6, 42, by decide, by decide, by decide, by decide⟩
  | exact ⟨6, 8, 45, by decide, by decide, by decide, by decide⟩
  | exact ⟨2, 30, 39, by decide, by decide, by decide, by decide⟩
  | exact ⟨1, 7, 55, by decide, by decide, by decide, by decide⟩
  | exact ⟨5, 9, 63, by decide, by decide, by decide, by decide⟩
  | exact ⟨2, 14, 65, by decide, by decide, by decide, by decide⟩
  | exact ⟨3, 21, 65, by decide, by decide, by decide, by decide⟩
  | exact ⟨6, 42, 55, by decide, by decide, by decide, by decide⟩
  | exact ⟨7, 49, 65, by decide, by decide, by decide, by decide⟩
  | exact ⟨1, 7, 125, by decide, by decide, by decide, by decide⟩
  | exact ⟨6, 42, 125, by decide, by decide, by decide, by decide⟩

private lemma smooth_case {a b m : ℕ}
    (hm : m ∈ ({1, 3, 5, 11, 13, 17, 19, 33, 37, 43, 51, 57, 67, 73, 85, 97,
                123, 163, 177, 187, 193, 267, 627, 697} : Finset ℕ))
    (hnd : ¬ IsSumOfThreeDistinctNonzeroSquares ((3 ^ a * 5 ^ b) ^ 2 * m)) :
    (3 ^ a * 5 ^ b) ^ 2 * m ∈ exceptions := by
  by_cases hb : b = 0
  · subst hb
    by_cases ha : a = 0
    · subst ha
      simp only [pow_zero, mul_one, one_pow, one_mul]
      fin_cases hm <;> decide
    · by_cases hm3 : m = 1 ∨ m = 3 ∨ m = 11
      · by_cases ha1 : a = 1
        · subst ha1
          rcases hm3 with rfl | rfl | rfl <;> decide
        · have ha2 : 2 ≤ a := by omega
          exfalso
          apply hnd
          have heq : (3 ^ a * 5 ^ 0) ^ 2 * m = (3 ^ (a - 2)) ^ 2 * (81 * m) := by
            have hpow : 3 ^ a = 3 ^ (a - 2) * 3 ^ 2 := by
              rw [← pow_add, Nat.sub_add_cancel ha2]
            rw [pow_zero, mul_one, hpow]
            ring
          rw [heq]
          apply scale_distinct (by positivity)
          rcases hm3 with rfl | rfl | rfl
          · exact ⟨1, 4, 8, by decide, by decide, by decide, by decide⟩
          · exact ⟨5, 7, 13, by decide, by decide, by decide, by decide⟩
          · exact ⟨1, 7, 29, by decide, by decide, by decide, by decide⟩
      · exfalso
        apply hnd
        have ha1 : 1 ≤ a := by omega
        have heq : (3 ^ a * 5 ^ 0) ^ 2 * m = (3 ^ (a - 1)) ^ 2 * (9 * m) := by
          have hpow : 3 ^ a = 3 ^ (a - 1) * 3 ^ 1 := by
            rw [← pow_add, Nat.sub_add_cancel ha1]
          rw [pow_zero, mul_one, hpow]
          ring
        rw [heq]
        apply scale_distinct (by positivity)
        apply mul_nine_distinct
        fin_cases hm
        all_goals first | (exfalso; exact hm3 (by decide)) | decide
  · have hb1 : 1 ≤ b := by omega
    by_cases hm1 : m = 1
    · subst hm1
      by_cases ha : a = 0
      · subst ha
        by_cases hb1' : b = 1
        · subst hb1'; decide
        · have hb2 : 2 ≤ b := by omega
          exfalso
          apply hnd
          have heq : (3 ^ 0 * 5 ^ b) ^ 2 * 1 = (5 ^ (b - 2)) ^ 2 * 625 := by
            have hpow : 5 ^ b = 5 ^ (b - 2) * 5 ^ 2 := by
              rw [← pow_add, Nat.sub_add_cancel hb2]
            rw [pow_zero, one_mul, mul_one, hpow]
            ring
          rw [heq]
          exact scale_distinct (by positivity)
            ⟨9, 12, 20, by decide, by decide, by decide, by decide⟩
      · have ha1 : 1 ≤ a := by omega
        exfalso
        apply hnd
        have heq : (3 ^ a * 5 ^ b) ^ 2 * 1 = (3 ^ (a - 1) * 5 ^ (b - 1)) ^ 2 * 225 := by
          have hpa : 3 ^ a = 3 ^ (a - 1) * 3 ^ 1 := by
            rw [← pow_add, Nat.sub_add_cancel ha1]
          have hpb : 5 ^ b = 5 ^ (b - 1) * 5 ^ 1 := by
            rw [← pow_add, Nat.sub_add_cancel hb1]
          rw [hpa, hpb]
          ring
        rw [heq]
        exact scale_distinct (by positivity)
          ⟨2, 5, 14, by decide, by decide, by decide, by decide⟩
    · exfalso
      apply hnd
      have heq : (3 ^ a * 5 ^ b) ^ 2 * m = (3 ^ a * 5 ^ (b - 1)) ^ 2 * (25 * m) := by
        have hpb : 5 ^ b = 5 ^ (b - 1) * 5 ^ 1 := by
          rw [← pow_add, Nat.sub_add_cancel hb1]
        rw [hpb]
        ring
      rw [heq]
      apply scale_distinct (by positivity)
      apply mul_twentyfive_distinct
      fin_cases hm
      all_goals first | (exfalso; exact hm1 rfl) | decide

theorem main : H1 → H2 → H3 → H4 → OMA.R_oeis_a004432_R1.H1 := by
  intro h1 h2 h3 h4 s hodd hsum hnd
  have hs0 : 0 < s := by omega
  obtain ⟨k, m, hk0, hmsf, hseq⟩ := sqfree_mul_sq s hs0
  have hk_odd : k % 2 = 1 := by
    by_contra h
    have hk2 : k % 2 = 0 := by omega
    have h4 : (k ^ 2 * m) % 2 = 0 := by
      rw [Nat.mul_mod, Nat.pow_mod, hk2]
      simp
    rw [← hseq] at h4
    omega
  have hm_nd : ¬ IsSumOfThreeDistinctNonzeroSquares m := fun hm =>
    hnd (hseq ▸ scale_distinct hk0 hm)
  have hm_mod : m % 8 = s % 8 := by
    have hk2m : k ^ 2 % 8 = 1 := odd_sq_mod_eight hk_odd
    have hmul : (k ^ 2 * m) % 8 = (k ^ 2 % 8 * (m % 8)) % 8 := Nat.mul_mod _ _ _
    rw [← hseq, hk2m, one_mul, Nat.mod_mod] at hmul
    exact hmul.symm
  have hs8 : s % 8 = 1 ∨ s % 8 = 3 ∨ s % 8 = 5 := odd_sum_three_squares_mod_eight hodd hsum
  have hm_mem : m ∈ ({1, 3, 5, 11, 13, 17, 19, 33, 37, 43, 51, 57, 67, 73, 85, 97,
                      123, 163, 177, 187, 193, 267, 627, 697} : Finset ℕ) := by
    rcases hs8 with h8 | h8 | h8
    · have h := h1 m hmsf (hm_mod.trans h8) hm_nd
      fin_cases h <;> decide
    · have h := h2 m hmsf (hm_mod.trans h8) hm_nd
      fin_cases h <;> decide
    · have h := h3 m hmsf (hm_mod.trans h8) hm_nd
      fin_cases h <;> decide
  rcases three_five_smooth_or_ge_seven k hk0 hk_odd with ⟨p, hp, hp7, hpk⟩ | ⟨a, b, rfl⟩
  · exfalso
    obtain ⟨q, rfl⟩ := hpk
    have hq0 : 0 < q := by
      by_contra! h
      have : q = 0 := by omega
      subst this
      omega
    have heq : (p * q) ^ 2 * m = q ^ 2 * (p ^ 2 * m) := by ring
    apply hnd
    rw [hseq, heq]
    exact scale_distinct hq0 (h4 p hp hp7 m hm_mem)
  · rw [hseq] at hnd ⊢
    exact smooth_case hm_mem hnd

end Proof

end OMA.R_oeis_a004432_R1_H1_R1
