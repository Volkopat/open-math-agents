import OMAStatements.S_oeis_a037097

/-!
# Proof of OEIS A037097

We prove that for all `n ≥ 3`, `(X + 1)^(2^(n - 2) - 1)` divides `column n (2^(n - 1))`
in `(ZMod 2)[X]`, and consequently `column n (2^(n - 1)) = (X + 1)^(2^(n - 2) - 1) * quotient n`.

Proof outline:
1. By induction on `m ≥ 1`, `3^(2^m) ≡ 1 + 2^(m + 2) [MOD 2^(m + 3)]`.
   Setting `m = n - 2` (for `n ≥ 3`), `3^(2^(n - 2)) = 1 + 2^n * (2 * q + 1)`.
2. For every `k : ℕ`, since `3^k` is odd,
   `3^(k + 2^(n - 2)) = 3^k * 3^(2^(n - 2)) ≡ 3^k + 2^n [MOD 2^(n + 1)]`,
   so bit `n` flips: `digit n (k + 2^(n - 2)) = digit n k + 1` in `ZMod 2`.
3. Splitting `column n (2^(n - 1))` at `M = 2^(n - 2)` gives
   `column n (2 * M) = (1 + X^M) * column n M + X^M * (∑ k ∈ range M, X^k)`.
4. In characteristic 2, `(X + 1)^M = X^M + 1`, and
   `(X + 1) * (∑ k ∈ range M, X^k) = X^M + 1 = (X + 1)^M`,
   hence `∑ k ∈ range M, X^k = (X + 1)^(M - 1)`.
   Therefore `(X + 1)^(M - 1)` divides both summands, hence divides `column n (2 * M)`.
5. The second conjunct follows directly from `EuclideanDomain.mul_div_cancel'` (since
   `(X + 1)^(M - 1) ≠ 0`).
-/

namespace OMA.A037097Proof

open OMA.S_oeis_a037097 Polynomial Finset

private lemma three_pow_two_pow_mod :
    ∀ m : ℕ, 1 ≤ m → 3 ^ (2 ^ m) % 2 ^ (m + 3) = 1 + 2 ^ (m + 2) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hq : ∃ q : ℕ, 3 ^ (2 ^ m) = 1 + 2 ^ (m + 2) + 2 ^ (m + 3) * q := by
      refine ⟨3 ^ (2 ^ m) / 2 ^ (m + 3), ?_⟩
      have hdiv := Nat.div_add_mod (3 ^ (2 ^ m)) (2 ^ (m + 3))
      rw [ih] at hdiv
      omega
    obtain ⟨q, hq⟩ := hq
    have hsq : 3 ^ (2 ^ (m + 1)) = (3 ^ (2 ^ m)) ^ 2 := by
      rw [← pow_mul, pow_succ]
    rw [hsq, hq]
    have hpow1 : 2 ^ (m + 3) = 2 * 2 ^ (m + 2) := by rw [pow_succ]; ring
    have hpow2 : 2 ^ (m + 1 + 3) = 2 * 2 ^ (m + 3) := by
      rw [show m + 1 + 3 = (m + 3) + 1 by omega, pow_succ]; ring
    have hpow3 : (2 ^ (m + 2)) ^ 2 = 2 ^ (m + 1 + 3) * 2 ^ m := by
      rw [← pow_mul, ← pow_add]
      congr 1; omega
    have hexp : (1 + 2 ^ (m + 2) + 2 ^ (m + 3) * q) ^ 2 =
        (1 + 2 ^ (m + 1 + 2)) + 2 ^ (m + 1 + 3) *
          (2 ^ m + q + 2 ^ (m + 2) * q + 2 ^ (m + 2) * q ^ 2) := by
      have h1 : 2 ^ (m + 1 + 2) = 2 * 2 ^ (m + 2) := by
        rw [show m + 1 + 2 = (m + 2) + 1 by omega, pow_succ]; ring
      have h3 : 2 ^ (m + 1 + 3) = 4 * 2 ^ (m + 2) := by omega
      calc (1 + 2 ^ (m + 2) + 2 ^ (m + 3) * q) ^ 2
          = (1 + 2 * 2 ^ (m + 2)) + (2 ^ (m + 2)) ^ 2 +
              4 * 2 ^ (m + 2) * (q + 2 ^ (m + 2) * q + 2 ^ (m + 2) * q ^ 2) := by
                rw [hpow1]; ring
        _ = (1 + 2 ^ (m + 1 + 2)) + 2 ^ (m + 1 + 3) *
              (2 ^ m + q + 2 ^ (m + 2) * q + 2 ^ (m + 2) * q ^ 2) := by
                rw [hpow3, h1, h3]; ring
    rw [hexp, Nat.add_mul_mod_self_left]
    refine Nat.mod_eq_of_lt ?_
    have h1 : 2 ^ (m + 1 + 3) = 2 * 2 ^ (m + 1 + 2) := by
      rw [show m + 1 + 3 = (m + 1 + 2) + 1 by omega, pow_succ]; ring
    have h2 : 2 ≤ 2 ^ (m + 1 + 2) := by
      have : 2 ^ 1 ≤ 2 ^ (m + 1 + 2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    omega

private lemma digit_shift (n k : ℕ) (hn : 3 ≤ n) :
    digit n (k + 2 ^ (n - 2)) = digit n k + 1 := by
  unfold digit
  have hmod := three_pow_two_pow_mod (n - 2) (by omega)
  have he1 : n - 2 + 2 = n := by omega
  have he2 : n - 2 + 3 = n + 1 := by omega
  rw [he1, he2] at hmod
  obtain ⟨q, hq⟩ : ∃ q : ℕ, 3 ^ (2 ^ (n - 2)) = 1 + 2 ^ n + 2 ^ (n + 1) * q := by
    refine ⟨3 ^ (2 ^ (n - 2)) / 2 ^ (n + 1), ?_⟩
    have hdiv := Nat.div_add_mod (3 ^ (2 ^ (n - 2))) (2 ^ (n + 1))
    rw [hmod] at hdiv; omega
  have h3odd : 3 ^ k % 2 = 1 := by
    induction k with
    | zero => decide
    | succ k ih => rw [pow_succ]; omega
  obtain ⟨r, hr⟩ : ∃ r : ℕ, 3 ^ k = 2 * r + 1 := ⟨3 ^ k / 2, by omega⟩
  have hmul : 3 ^ (k + 2 ^ (n - 2)) =
      3 ^ k + 2 ^ n + 2 ^ (n + 1) * (r + 3 ^ k * q) := by
    rw [pow_add, hq]
    have h2n1 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    calc 3 ^ k * (1 + 2 ^ n + 2 ^ (n + 1) * q)
        = 3 ^ k + 3 ^ k * 2 ^ n + 2 * 2 ^ n * (3 ^ k * q) := by rw [h2n1]; ring
      _ = 3 ^ k + (2 * r + 1) * 2 ^ n + 2 * 2 ^ n * (3 ^ k * q) := by rw [hr]
      _ = 3 ^ k + 2 ^ n + 2 ^ (n + 1) * (r + 3 ^ k * q) := by rw [h2n1]; ring
  have hdiv : 3 ^ (k + 2 ^ (n - 2)) / 2 ^ n =
      3 ^ k / 2 ^ n + 1 + 2 * (r + 3 ^ k * q) := by
    rw [hmul]
    have h2p : 0 < 2 ^ n := by positivity
    have hre : 3 ^ k + 2 ^ n + 2 ^ (n + 1) * (r + 3 ^ k * q) =
        3 ^ k + 2 ^ n * (1 + 2 * (r + 3 ^ k * q)) := by
      have h2n1 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
      rw [h2n1]; ring
    rw [hre, Nat.add_mul_div_left _ _ h2p]
    omega
  rw [hdiv]
  have hbit : (3 ^ k / 2 ^ n + 1 + 2 * (r + 3 ^ k * q)) % 2 = (3 ^ k / 2 ^ n % 2 + 1) % 2 := by
    omega
  rw [hbit]
  rcases Nat.mod_two_eq_zero_or_one (3 ^ k / 2 ^ n) with h | h <;> simp [h] <;> decide

private lemma char2_add_one_pow_two_pow :
    ∀ m : ℕ, ((X + 1 : R) ^ (2 ^ m)) = X ^ (2 ^ m) + 1 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_mul, ih]
    have htwo : (2 : R) = 0 := by
      have h0 : ((2 : ZMod 2) : ZMod 2) = 0 := by decide
      simpa [h0] using (map_ofNat (C : ZMod 2 →+* R) 2).symm
    calc (X ^ (2 ^ m) + 1) ^ 2
        = X ^ (2 ^ m) * X ^ (2 ^ m) + 2 * X ^ (2 ^ m) + 1 := by ring
      _ = X ^ (2 ^ m * 2) + 1 := by rw [htwo, zero_mul, add_zero, ← pow_add, mul_two]

private lemma geom_sum_eq_pow (m : ℕ) :
    (∑ k ∈ Finset.range (2 ^ m), (X : R) ^ k) = (X + 1 : R) ^ (2 ^ m - 1) := by
  have hne : (X + 1 : R) ≠ 0 := by
    intro h
    have h1 := congrArg (fun p : R => p.coeff 1) h
    simp [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_one] at h1
  have hmul : (X + 1 : R) * (∑ k ∈ Finset.range (2 ^ m), (X : R) ^ k) =
      (X + 1 : R) * (X + 1 : R) ^ (2 ^ m - 1) := by
    have hpos : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
    rw [← pow_succ', Nat.sub_add_cancel hpos, char2_add_one_pow_two_pow]
    have hneg : (-1 : R) = 1 := by
      have h0 : ((2 : ZMod 2) : ZMod 2) = 0 := by decide
      have h2 : (2 : R) = 0 := by simpa [h0] using (map_ofNat (C : ZMod 2 →+* R) 2).symm
      calc (-1 : R) = -1 + 2 := by rw [h2, add_zero]
        _ = 1 := by ring
    have hsub : (X + 1 : R) = X - 1 := by rw [sub_eq_add_neg, hneg]
    have hsub2 : (X ^ (2 ^ m) + 1 : R) = X ^ (2 ^ m) - 1 := by rw [sub_eq_add_neg, hneg]
    rw [hsub, hsub2]
    simpa [mul_comm] using geom_sum_mul (X : R) (2 ^ m)
  exact mul_left_cancel₀ hne hmul

theorem result : type_of% @OMA.S_oeis_a037097.main := by
  intro n hn
  let M := 2 ^ (n - 2)
  have h2M : 2 ^ (n - 1) = M + M := by
    dsimp [M]
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]; ring
  have hdvd : (X + 1 : R) ^ (M - 1) ∣ column n (2 ^ (n - 1)) := by
    unfold column
    rw [h2M, Finset.sum_range_add]
    have hsecond : ∑ k ∈ Finset.range M, C (digit n (M + k)) * X ^ (M + k) =
        X ^ M * (∑ k ∈ Finset.range M, C (digit n k) * X ^ k) +
        X ^ M * (∑ k ∈ Finset.range M, (X : R) ^ k) := by
      rw [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [add_comm M k, digit_shift n k hn, map_add, map_one, pow_add]
      ring
    rw [hsecond]
    have hcomb : (∑ k ∈ Finset.range M, C (digit n k) * X ^ k) +
        (X ^ M * (∑ k ∈ Finset.range M, C (digit n k) * X ^ k) +
         X ^ M * (∑ k ∈ Finset.range M, (X : R) ^ k)) =
        (X ^ M + 1) * (∑ k ∈ Finset.range M, C (digit n k) * X ^ k) +
        X ^ M * (∑ k ∈ Finset.range M, (X : R) ^ k) := by ring
    rw [hcomb]
    have hMpos : 1 ≤ M := Nat.one_le_pow (n - 2) 2 (by decide)
    rw [← char2_add_one_pow_two_pow (n - 2), geom_sum_eq_pow (n - 2)]
    refine ⟨(X + 1) * (∑ k ∈ Finset.range M, C (digit n k) * X ^ k) + X ^ M, ?_⟩
    have hpow : (X + 1 : R) ^ M = (X + 1 : R) ^ (M - 1) * (X + 1) := by
      rw [← pow_succ, Nat.sub_add_cancel hMpos]
    rw [hpow]; ring
  refine ⟨hdvd, ?_⟩
  unfold OMA.S_oeis_a037097.quotient
  have hne : (X + 1 : R) ^ (2 ^ (n - 2) - 1) ≠ 0 := by
    refine pow_ne_zero _ ?_
    intro h
    have h1 := congrArg (fun p : R => p.coeff 1) h
    simp [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_one] at h1
  exact (EuclideanDomain.mul_div_cancel' hne hdvd).symm

end OMA.A037097Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a037097.main := OMA.A037097Proof.result
