import OMAReductions.R_Erdos699_erdos_699_R1

-- Reduction Erdos699.erdos_699.R1.H2.R1 of step Erdos699.erdos_699.R1.H2
-- Credit: @rickmanelius

/-!
# Erdős 699, far range: the prime-counting regime

The step asks, for `3 ≤ i < j ≤ n / 2` with `n ≤ j ^ 2` and `3 i < 2 j`, for a prime `p ≥ i` and
digit positions `a, b ≥ 1` with `n mod p ^ a < i mod p ^ a` and `n mod p ^ b < j mod p ^ b`.
By Kummer's theorem these are carries, so the step says that some prime `p ≥ i` divides both
`C(n, i)` and `C(n, j)`.

Proved below with no hypothesis (`counting_regime`): the step holds whenever
`j ^ i < n ^ (i - π'(i))`, where `π'(i)` is the number of primes below `i`. Suppose no prime
`p ≥ i` divides `g = gcd(C(n, i), C(n, j))`. Then
* `C(n, i)` divides `g * C(j, i)`, from `C(n, j) C(j, i) = C(n, i) C(n - i, j - i)`;
* `g ≤ n ^ π'(i)`, since every prime factor of `g` is below `i` and, by Kummer, the exact power
  of a prime dividing `C(n, i)` is at most `n`;
* `C(j, i) * n ^ i ≤ C(n, i) * j ^ i`, as each factor `(n - t) / (j - t)` is at least `n / j`.
Together these give `n ^ (i - π'(i)) ≤ j ^ i`. Otherwise a prime `p ≥ i` divides both binomials,
and its first carry in each gives the two digit positions (`carry_of_dvd`).

This sharpens the square bound `n ≤ j ^ 2` of the parent reduction, which amounts to
`2 π'(i) ≤ i`, to `n ≤ j ^ (i / (i - π'(i)))`. The exponent is `3/2` at `i = 33`, `4/3` at
`i = 100`, about `1.2` at `i = 1000`, and it tends to `1` like `1 + 1 / log i`.

What is left is split at `n = j ^ (3/2)`:
* `H1`: the far range with `n ^ 2 ≤ j ^ 3`;
* `H2`: the far range with `j ^ 3 < n ^ 2` where the prime-counting bound does not apply,
  `n ^ (i - π'(i)) ≤ j ^ i`. These two conditions force `3 π'(i) > i`, so `H2` only concerns the
  indices `4 ≤ i ≤ 26` and `i = 32` (a direct count of primes up to `2 * 10 ^ 6`, and
  `π(x) < 1.26 x / log x` beyond).
-/

namespace OMA.R_Erdos699_erdos_699_R1_H2_R1

/-- The far range at or below `j ^ (3/2)`: `n ^ 2 ≤ j ^ 3`. -/
def H1 : Prop := ∀ n i j : ℕ, 3 ≤ i → i < j → j ≤ n / 2 → n ^ 2 ≤ j ^ 3 →
    3 * i < 2 * j → ∃ p a b : ℕ, p.Prime ∧ i ≤ p ∧ 0 < a ∧ 0 < b ∧
      n % p ^ a < i % p ^ a ∧ n % p ^ b < j % p ^ b

/-- The far range above `j ^ (3/2)` that the prime-counting bound misses:
`j ^ 3 < n ^ 2` and `n ^ (i - π'(i)) ≤ j ^ i` (possible only for `4 ≤ i ≤ 26` and `i = 32`). -/
def H2 : Prop := ∀ n i j : ℕ, 3 ≤ i → i < j → j ≤ n / 2 → n ≤ j ^ 2 → j ^ 3 < n ^ 2 →
    n ^ (i - Nat.primeCounting' i) ≤ j ^ i →
    3 * i < 2 * j → ∃ p a b : ℕ, p.Prime ∧ i ≤ p ∧ 0 < a ∧ 0 < b ∧
      n % p ^ a < i % p ^ a ∧ n % p ^ b < j % p ^ b

/-- `C(j, i) * n ^ i ≤ C(n, i) * j ^ i` for `j ≤ n`, by induction on `i` through
`C(m, k + 1) * (k + 1) = C(m, k) * (m - k)`. -/
lemma choose_ratio {j n : ℕ} (hjn : j ≤ n) :
    ∀ i : ℕ, j.choose i * n ^ i ≤ n.choose i * j ^ i
  | 0 => by simp
  | k + 1 => by
    have ih := choose_ratio hjn k
    have hstep : (j - k) * n ≤ (n - k) * j := by
      rcases Nat.lt_or_ge j k with h | h
      · rw [Nat.sub_eq_zero_of_le h.le, Nat.zero_mul]
        exact Nat.zero_le _
      · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h
        obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hjn
        rw [show k + a - k = a by omega, show k + a + b - k = a + b by omega]
        nlinarith [Nat.zero_le (b * k)]
    have hj := Nat.choose_succ_right_eq j k
    have hn := Nat.choose_succ_right_eq n k
    have hmul : (j.choose (k + 1) * n ^ (k + 1)) * (k + 1) ≤
        (n.choose (k + 1) * j ^ (k + 1)) * (k + 1) := by
      calc (j.choose (k + 1) * n ^ (k + 1)) * (k + 1)
          = (j.choose (k + 1) * (k + 1)) * (n ^ k * n) := by ring
        _ = (j.choose k * (j - k)) * (n ^ k * n) := by rw [hj]
        _ = (j.choose k * n ^ k) * ((j - k) * n) := by ring
        _ ≤ (n.choose k * j ^ k) * ((n - k) * j) := Nat.mul_le_mul ih hstep
        _ = (n.choose k * (n - k)) * (j ^ k * j) := by ring
        _ = (n.choose (k + 1) * (k + 1)) * (j ^ k * j) := by rw [hn]
        _ = (n.choose (k + 1) * j ^ (k + 1)) * (k + 1) := by ring
    exact Nat.le_of_mul_le_mul_right hmul (Nat.succ_pos k)

/-- `C(n, i)` divides `gcd(C(n, i), C(n, j)) * C(j, i)` (Erdős and Szekeres), because
`C(n, j) * C(j, i) = C(n, i) * C(n - i, j - i)`. -/
lemma choose_dvd_gcd {n i j : ℕ} (hij : i ≤ j) :
    n.choose i ∣ Nat.gcd (n.choose i) (n.choose j) * j.choose i := by
  rw [← Nat.gcd_mul_right]
  refine Nat.dvd_gcd (Dvd.intro _ rfl) ?_
  rw [Nat.choose_mul hij]
  exact Dvd.intro _ rfl

/-- A nonzero divisor `g` of `C(n, i)`, `i ≤ n`, is at most `n ^ ω(g)`: by Kummer the exact power
of a prime `p` dividing `C(n, i)` is at most `p ^ log_p n ≤ n`. -/
lemma le_pow_card_primeFactors {g n i : ℕ} (hn : n ≠ 0) (hg : g ≠ 0) (hin : i ≤ n)
    (hgd : g ∣ n.choose i) : g ≤ n ^ g.primeFactors.card := by
  have hc : n.choose i ≠ 0 := (Nat.choose_pos hin).ne'
  have hle : ∀ p ∈ g.primeFactors, p ^ g.factorization p ≤ n := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    calc p ^ g.factorization p ≤ p ^ (n.choose i).factorization p :=
          Nat.pow_le_pow_right hpp.pos ((Nat.factorization_le_iff_dvd hg hc).2 hgd p)
      _ ≤ p ^ Nat.log p n := Nat.pow_le_pow_right hpp.pos Nat.factorization_choose_le_log
      _ ≤ n := Nat.pow_log_le_self p hn
  calc g = ∏ p ∈ g.primeFactors, p ^ g.factorization p :=
        Nat.prod_primeFactors_pow_factorization hg
    _ ≤ ∏ _p ∈ g.primeFactors, n := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hle
    _ = n ^ g.primeFactors.card := Finset.prod_const n

/-- If every prime factor of `g` is below `i`, then `g` has at most `π'(i)` prime factors. -/
lemma card_primeFactors_le_primeCounting' {g i : ℕ} (h : ∀ p ∈ g.primeFactors, p < i) :
    g.primeFactors.card ≤ Nat.primeCounting' i := by
  show g.primeFactors.card ≤ Nat.count Nat.Prime i
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨h p hp, Nat.prime_of_mem_primeFactors hp⟩

/-- Kummer: a prime `p` dividing `C(n, k)`, `k ≤ n`, has a carry, that is a digit position
`a ≥ 1` with `n mod p ^ a < k mod p ^ a`. -/
lemma carry_of_dvd {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hd : p ∣ n.choose k) :
    ∃ a, 0 < a ∧ n % p ^ a < k % p ^ a := by
  have hpos : 0 < (n.choose k).factorization p :=
    hp.factorization_pos_of_dvd (Nat.choose_pos hkn).ne' hd
  rw [Nat.factorization_choose hp hkn (Nat.lt_succ_self _)] at hpos
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter, Finset.mem_Ico] at ha
  obtain ⟨⟨ha1, -⟩, hcarry⟩ := ha
  refine ⟨a, ha1, ?_⟩
  have hq : 0 < p ^ a := pow_pos hp.pos a
  have h1 := Nat.mod_lt k hq
  have h2 := Nat.mod_lt (n - k) hq
  have hsum : n % p ^ a = (k % p ^ a + (n - k) % p ^ a) % p ^ a := by
    rw [← Nat.add_mod, Nat.add_sub_of_le hkn]
  have hsub : (k % p ^ a + (n - k) % p ^ a) % p ^ a = k % p ^ a + (n - k) % p ^ a - p ^ a := by
    rw [Nat.mod_eq_sub_mod hcarry, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The prime-counting regime: if `1 ≤ i < j ≤ n` and `j ^ i < n ^ (i - π'(i))`, then some prime
`p ≥ i` divides both `C(n, i)` and `C(n, j)`. -/
theorem counting_regime {n i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hjn : j ≤ n)
    (hreg : j ^ i < n ^ (i - Nat.primeCounting' i)) :
    ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ n.choose i ∧ p ∣ n.choose j := by
  by_contra hno
  have hin : i ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hA : 0 < n.choose i := Nat.choose_pos hin
  have hB : 0 < j.choose i := Nat.choose_pos hij.le
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd (n.choose i) (n.choose j) := ⟨_, rfl⟩
  have hgpos : 0 < g := hg ▸ Nat.gcd_pos_of_pos_left _ hA
  have hsmall : ∀ p ∈ g.primeFactors, p < i := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ Nat.gcd (n.choose i) (n.choose j) := hg ▸ Nat.dvd_of_mem_primeFactors hp
    by_contra hge
    exact hno ⟨p, hpp, Nat.le_of_not_lt hge, dvd_trans hpd (Nat.gcd_dvd_left _ _),
      dvd_trans hpd (Nat.gcd_dvd_right _ _)⟩
  have hc := card_primeFactors_le_primeCounting' hsmall
  have hgle : g ≤ n ^ g.primeFactors.card :=
    le_pow_card_primeFactors hn0 hgpos.ne' hin (hg ▸ Nat.gcd_dvd_left _ _)
  have h1 : n.choose i ≤ g * j.choose i :=
    Nat.le_of_dvd (Nat.mul_pos hgpos hB) (hg ▸ choose_dvd_gcd hij.le)
  have h2 := choose_ratio hjn i
  have hP : Nat.primeCounting' i ≤ i := Nat.count_le _
  have h3 : j.choose i * n ^ i ≤ j.choose i * (n ^ Nat.primeCounting' i * j ^ i) := by
    calc j.choose i * n ^ i ≤ n.choose i * j ^ i := h2
      _ ≤ g * j.choose i * j ^ i := Nat.mul_le_mul_right _ h1
      _ ≤ n ^ g.primeFactors.card * j.choose i * j ^ i :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hgle)
      _ ≤ n ^ Nat.primeCounting' i * j.choose i * j ^ i :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hnpos hc))
      _ = j.choose i * (n ^ Nat.primeCounting' i * j ^ i) := by ring
  have h4 : n ^ i ≤ n ^ Nat.primeCounting' i * j ^ i := Nat.le_of_mul_le_mul_left h3 hB
  have h5 : n ^ Nat.primeCounting' i * n ^ (i - Nat.primeCounting' i) = n ^ i := by
    rw [← pow_add, Nat.add_sub_cancel' hP]
  have h6 : n ^ Nat.primeCounting' i * n ^ (i - Nat.primeCounting' i) ≤
      n ^ Nat.primeCounting' i * j ^ i := by
    rw [h5]
    exact h4
  have h7 : n ^ (i - Nat.primeCounting' i) ≤ j ^ i :=
    Nat.le_of_mul_le_mul_left h6 (pow_pos hnpos _)
  exact absurd hreg (not_lt.mpr h7)

theorem main : H1 → H2 → OMA.R_Erdos699_erdos_699_R1.H2 := by
  intro h1 h2 n i j hi hij hjn hsq hfar
  by_cases hreg : j ^ i < n ^ (i - Nat.primeCounting' i)
  · have hjn' : j ≤ n := le_trans hjn (Nat.div_le_self n 2)
    obtain ⟨p, hp, hip, hdi, hdj⟩ := counting_regime (by omega) hij hjn' hreg
    obtain ⟨a, ha, hca⟩ := carry_of_dvd hp (by omega) hdi
    obtain ⟨b, hb, hcb⟩ := carry_of_dvd hp hjn' hdj
    exact ⟨p, a, b, hp, hip, ha, hb, hca, hcb⟩
  · by_cases hlow : n ^ 2 ≤ j ^ 3
    · exact h1 n i j hi hij hjn hlow hfar
    · exact h2 n i j hi hij hjn hsq (not_le.mp hlow) (not_lt.mp hreg) hfar

end OMA.R_Erdos699_erdos_699_R1_H2_R1
