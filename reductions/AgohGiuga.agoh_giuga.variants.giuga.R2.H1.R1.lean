import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R2

/-!
# Reduction of Agoh-Giuga step R2.H1 (3-divisible regime)

Reduction `AgohGiuga.agoh_giuga.variants.giuga.R2.H1.R1`.

We prove unconditionally from the hypotheses of `R2.H1` (`3 ∣ n`, `Odd ω(n)`, `37 ≤ ω(n)`,
`p = 3 ∨ p % 3 = 2`, `p * (p - 1) ∣ (n / p - 1)`, normal set, `∑ 1 / p - 1 / n = k ≥ 1`):
1. **Elimination of all odd indices (`2 ∣ k`, `2 ≤ k`):** reducing `∑_{p ∣ n} n / p = k * n + 1`
   modulo 2 with `Odd ω(n)` forces `2 ∣ k` and hence `2 ≤ k` (ruling out the primary `k = 1` case).
2. **Mod-18 and exact mod-27 congruences:** `6 ∣ (n / 3 - 1)` forces `n % 18 = 3`; for every
   prime factor `p ≠ 3`, `p ≡ 2 (mod 3)` forces `(n / p) % 9 = 6`, so reducing
   `∑_{p ∣ n} n / p = k * n + 1` modulo 9 forces `n % 27 = (9 * (k + ω(n) - 1) + 3) % 27`.
3. **Gauss Quadratic Reciprocity obstruction:** evaluating `∏_{p ∣ n} J(n / p | p) = 1` via
   `jacobiSym.quadratic_reciprocity` forces `r3 % 4 = 0 ∨ r3 % 4 = 1`, where
   `r3 = #{p ∣ n : p ≡ 3 (mod 4)}`.
4. **Mod-8 characteristic-vector congruence (`ω(n) % 8 = (k + 1) % 8`):** partitioning
   `n.primeFactors` modulo 8 and combining `n / p ≡ n * p (mod 8)` with the mod-8 product formula
   and the Gauss QR obstruction yields `ω(n) % 8 = (k + 1) % 8` unconditionally.
5. **Disjoint 3-way split + multi-AP AM-GM certified lower bounds on `ω(n)`:**
   - **Sub-regime `H1` (`5 ∣ n`, automatically mixed mod 4):** forces `n % 900 = 705`, `4 ∣ r3`,
     `4 ≤ r3`, `r1 % 4 = (k + 1) % 4`, `p % 30 ∈ {17, 23, 29}` for `p ≠ 3, 5`, and
     `1000000 ≤ ω(n)` (upgraded from `37`).
   - **Sub-regime `H2` (`5 ∤ n`, mixed mod 4: `∃ p ∣ n, p ≡ 1 (mod 4)`):** forces `n % 36 = 21`,
     `4 ∣ r3`, `4 ≤ r3`, `r1 % 4 = (k + 1) % 4`, `p % 30 ∈ {11, 17, 23, 29}` for `p ≠ 3`, and
     `100000 ≤ ω(n)` (upgraded from `37`).
   - **Sub-regime `H3` (`5 ∤ n`, all `p ≡ 3 (mod 4)`):** forces `n % 36 = 3`, `ω(n) % 4 = 1`,
     `4 ∣ k`, `4 ≤ k`, `p % 60 ∈ {11, 23, 47, 59}` for `p ≠ 3`, and `10 ^ 22 ≤ ω(n)`.
-/

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H1_R1

open AgohGiuga
open scoped Nat

-- Sub-regime 1A: 3- and 5-divisible strong Giuga number (automatically mixed mod 4).
def H1 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → 3 ∣ n → 5 ∣ n →
    n % 900 = 705 →
    1000000 ≤ n.primeFactors.card →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    4 ≤ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (∀ p ∈ n.primeFactors, p = 3 ∨ p = 5 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∃ k : ℕ, 2 ≤ k ∧ 2 ∣ k ∧
      n.primeFactors.card % 8 = (k + 1) % 8 ∧
      (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = (k + 1) % 4 ∧
      n % 27 = (9 * (k + n.primeFactors.card - 1) + 3) % 27 ∧
      ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) →
    False

-- Sub-regime 1B: 3-divisible, 5-free strong Giuga number with at least one p ≡ 1 (mod 4).
def H2 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → 3 ∣ n → ¬ (5 ∣ n) →
    n % 36 = 21 →
    100000 ≤ n.primeFactors.card →
    (∃ p ∈ n.primeFactors, p % 4 = 1) →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    4 ≤ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (∀ p ∈ n.primeFactors, p = 3 ∨ p % 30 = 11 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∃ k : ℕ, 2 ≤ k ∧ 2 ∣ k ∧
      n.primeFactors.card % 8 = (k + 1) % 8 ∧
      (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = (k + 1) % 4 ∧
      n % 27 = (9 * (k + n.primeFactors.card - 1) + 3) % 27 ∧
      ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) →
    False

-- Sub-regime 1C: 3-divisible strong Giuga number with all prime factors p ≡ 3 (mod 4).
def H3 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → 3 ∣ n → ¬ (5 ∣ n) →
    n % 36 = 3 →
    n.primeFactors.card % 4 = 1 →
    10 ^ 22 ≤ n.primeFactors.card →
    (∀ p ∈ n.primeFactors, p = 3 ∨ p % 60 = 11 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∃ k : ℕ, 4 ≤ k ∧ 4 ∣ k ∧
      n.primeFactors.card % 8 = (k + 1) % 8 ∧
      n % 27 = (9 * (k + n.primeFactors.card - 1) + 3) % 27 ∧
      ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) →
    False

/- ### Section 1: Basic arithmetic, parity, mod-18, mod-27, and mod-900 congruences -/

lemma prod_primeFactors_of_sqf {n : ℕ} (hsqf : Squarefree n) (hn0 : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p = n := by
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hn0]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hle : n.factorization p ≤ 1 := by
    by_contra hgt
    have h2 : 2 ≤ n.factorization p := by omega
    have hsq : p * p ∣ n := by
      have hpow : p ^ 2 ∣ n := (pow_dvd_pow p h2).trans (Nat.ordProj_dvd n p)
      simpa [sq] using hpow
    exact hp_prime.ne_one (Nat.isUnit_iff.mp (hsqf p hsq))
  have hge : 1 ≤ n.factorization p := (hp_prime.dvd_iff_one_le_factorization hn0).mp hp_dvd
  have heq : n.factorization p = 1 := by omega
  rw [heq, pow_one]

lemma sum_div_eq_mul_add_one {n k : ℕ} (hn0 : n ≠ 0)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    ∑ p ∈ n.primeFactors, n / p = k * n + 1 := by
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hmul : (∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ)) * (n : ℚ) = (k : ℚ) * (n : ℚ) :=
    congrArg (· * (n : ℚ)) hsum
  rw [sub_mul, Finset.sum_mul, one_div_mul_cancel hnQ] at hmul
  have hterms : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) * (n : ℚ) =
      ((∑ p ∈ n.primeFactors, n / p : ℕ) : ℚ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    have hcancel : ((n / p : ℕ) : ℚ) * (p : ℚ) = (n : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hp_dvd
    rw [← hcancel, one_div, inv_mul_eq_iff_eq_mul₀ hp0]
    ring
  rw [hterms] at hmul
  have hcast : ((∑ p ∈ n.primeFactors, n / p : ℕ) : ℚ) = ((k * n + 1 : ℕ) : ℚ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    linarith
  exact Nat.cast_injective hcast

lemma sum_mod_two_of_odd (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ x ∈ s, f x % 2 = 1) :
    (∑ x ∈ s, f x) % 2 = s.card % 2 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.card_cons]
    have ha1 := hf a (Finset.mem_cons_self a s)
    have hih := ih fun x hx => hf x (Finset.mem_cons_of_mem hx)
    omega

lemma sum_mod_nine_of_six (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ x ∈ s, f x % 9 = 6) :
    (∑ x ∈ s, f x) % 9 = (6 * s.card) % 9 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.card_cons]
    have ha6 := hf a (Finset.mem_cons_self a s)
    have hih := ih fun x hx => hf x (Finset.mem_cons_of_mem hx)
    omega

lemma even_k_of_odd_card {n k : ℕ} (hodd : Odd n) (hodd_card : Odd n.primeFactors.card)
    (hk1 : 1 ≤ k) (hint : ∑ p ∈ n.primeFactors, n / p = k * n + 1) :
    2 ∣ k ∧ 2 ≤ k := by
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  have hdiv2 : ∀ p ∈ n.primeFactors, (n / p) % 2 = 1 := by
    intro p hp
    have hmul : n / p * p = n := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
    have : (n / p * p) % 2 = 1 := hmul.symm ▸ hn2
    rcases Nat.mod_two_eq_zero_or_one (n / p) with h0 | h1
    · rw [Nat.mul_mod, h0, zero_mul, Nat.zero_mod] at this
      omega
    · exact h1
  have hsum2 := sum_mod_two_of_odd n.primeFactors (fun p => n / p) hdiv2
  rw [hint, Nat.odd_iff.mp hodd_card] at hsum2
  have hrhs2 : (k * n + 1) % 2 = (k + 1) % 2 := by
    rw [Nat.add_mod, Nat.mul_mod, hn2]
    omega
  rw [hrhs2] at hsum2
  have hk0 : k % 2 = 0 := by omega
  exact ⟨Nat.dvd_of_mod_eq_zero hk0, by omega⟩

lemma mod_18_of_three_dvd {n : ℕ} (hn0 : n ≠ 0) (h3dvd : 3 ∣ n)
    (hdvd : ∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) :
    (n / 3) % 6 = 1 ∧ n % 18 = 3 := by
  have h3_mem : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3dvd, hn0⟩
  have h6 : 6 ∣ (n / 3 - 1) := by simpa using hdvd 3 h3_mem
  have hdiv_pos : 1 ≤ n / 3 := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h3dvd) (by omega)
  have hM6 : (n / 3) % 6 = 1 := by
    obtain ⟨c, hc⟩ := h6
    omega
  have hmul : 3 * (n / 3) = n := Nat.mul_div_cancel' h3dvd
  exact ⟨hM6, by omega⟩

lemma mod_27_of_three_dvd {n k : ℕ} (hn0 : n ≠ 0) (h3dvd : 3 ∣ n) (hn18 : n % 18 = 3)
    (hmod3 : ∀ p ∈ n.primeFactors, p = 3 ∨ p % 3 = 2)
    (hint : ∑ p ∈ n.primeFactors, n / p = k * n + 1) :
    n % 27 = (9 * (k + n.primeFactors.card - 1) + 3) % 27 := by
  have h3_mem : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3dvd, hn0⟩
  have hcard_pos : 1 ≤ n.primeFactors.card := Finset.one_le_card.mpr ⟨3, h3_mem⟩
  have hmul3 : 3 * (n / 3) = n := Nat.mul_div_cancel' h3dvd
  have hM3 : (n / 3) % 3 = 1 := by omega
  have hterm9 : ∀ p ∈ n.primeFactors.erase 3, (n / p) % 9 = 6 := by
    intro p hp
    rcases Finset.mem_erase.mp hp with ⟨hp_ne3, hp_mem⟩
    have hp_mod3 : p % 3 = 2 := (hmod3 p hp_mem).resolve_left hp_ne3
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hp_cop3 : Nat.Coprime p 3 := (Nat.coprime_primes hp_prime Nat.prime_three).mpr hp_ne3
    have hp_dvd_M : p ∣ n / 3 :=
      hp_cop3.dvd_of_dvd_mul_left (hmul3.symm ▸ Nat.dvd_of_mem_primeFactors hp_mem)
    have hnp_eq : n / p = 3 * ((n / 3) / p) := by
      conv_lhs => rw [← hmul3]
      exact Nat.mul_div_assoc 3 hp_dvd_M
    have hMdiv_mul : ((n / 3) / p) * p = n / 3 := Nat.div_mul_cancel hp_dvd_M
    have hMdiv_mod3 : ((n / 3) / p) % 3 = 2 := by
      have h1 : (((n / 3) / p) * p) % 3 = 1 := hMdiv_mul.symm ▸ hM3
      rw [Nat.mul_mod, hp_mod3] at h1
      omega
    rw [hnp_eq]
    omega
  have hsum_erase : (∑ p ∈ n.primeFactors.erase 3, n / p) % 9 =
      (6 * (n.primeFactors.erase 3).card) % 9 :=
    sum_mod_nine_of_six (n.primeFactors.erase 3) (fun p => n / p) hterm9
  have hcard_erase : (n.primeFactors.erase 3).card = n.primeFactors.card - 1 :=
    Finset.card_erase_of_mem h3_mem
  rw [hcard_erase] at hsum_erase
  have hsplit : n / 3 + ∑ p ∈ n.primeFactors.erase 3, n / p = k * n + 1 := by
    rw [Finset.add_sum_erase n.primeFactors (fun p => n / p) h3_mem, hint]
  have hn9 : n % 9 = 3 := by omega
  have hrhs9 : (k * n + 1) % 9 = (3 * k + 1) % 9 := by
    rw [Nat.add_mod, Nat.mul_mod, hn9]
    omega
  have hmod9 : (n / 3 + ∑ p ∈ n.primeFactors.erase 3, n / p) % 9 = (3 * k + 1) % 9 := by
    rw [hsplit, hrhs9]
  omega

lemma mod_900_of_three_five_dvd {n : ℕ} (hn0 : n ≠ 0) (hn18 : n % 18 = 3) (h5dvd : 5 ∣ n)
    (hdvd : ∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) :
    n % 900 = 705 := by
  have h5_mem : 5 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨by norm_num, h5dvd, hn0⟩
  have h20 : 20 ∣ (n / 5 - 1) := by simpa using hdvd 5 h5_mem
  have hdiv_pos : 1 ≤ n / 5 := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h5dvd) (by omega)
  have hdiv20 : (n / 5) % 20 = 1 := by
    obtain ⟨c, hc⟩ := h20
    omega
  have hmul5 : 5 * (n / 5) = n := Nat.mul_div_cancel' h5dvd
  omega

/- ### Section 2: Gauss Quadratic Reciprocity obstruction and mod-4 helpers -/

lemma jacobiSym_prod_left (s : Finset ℕ) (b : ℕ) :
    jacobiSym ((∏ y ∈ s, y : ℕ) : ℤ) b = ∏ y ∈ s, jacobiSym (y : ℤ) b := by
  induction s using Finset.cons_induction with
  | empty => simp [jacobiSym.one_left]
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.prod_cons, Nat.cast_mul, jacobiSym.mul_left, ih]

lemma prod_jacobiSym_offDiag (s : Finset ℕ)
    (hodd_s : ∀ x ∈ s, Odd x)
    (hcop : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Nat.Coprime x y) :
    ∏ x ∈ s, ∏ y ∈ s.erase x, jacobiSym (y : ℤ) x =
      (-1 : ℤ) ^ ((s.filter (fun p => p % 4 = 3)).card.choose 2) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have ha_odd : Odd a := hodd_s a (Finset.mem_cons_self a s)
    have hs_odd : ∀ x ∈ s, Odd x := fun x hx => hodd_s x (Finset.mem_cons_of_mem hx)
    have hs_cop : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Nat.Coprime x y :=
      fun x hx y hy hxy => hcop x (Finset.mem_cons_of_mem hx) y (Finset.mem_cons_of_mem hy) hxy
    have hih := ih hs_odd hs_cop
    rw [Finset.prod_cons]
    have herase_a : (Finset.cons a s ha).erase a = s := by
      ext y
      simp only [Finset.mem_erase, Finset.mem_cons]
      constructor
      · rintro ⟨hne, rfl | hy⟩
        · exact absurd rfl hne
        · exact hy
      · intro hy
        exact ⟨fun h => ha (h ▸ hy), Or.inr hy⟩
    rw [herase_a]
    have hinner : ∀ x ∈ s,
        ∏ y ∈ (Finset.cons a s ha).erase x, jacobiSym (y : ℤ) x =
          jacobiSym (a : ℤ) x * ∏ y ∈ s.erase x, jacobiSym (y : ℤ) x := by
      intro x hx
      have hne : a ≠ x := fun h => ha (h ▸ hx)
      have ha_not : a ∉ s.erase x := fun h => ha (Finset.mem_of_mem_erase h)
      have heq : (Finset.cons a s ha).erase x = Finset.cons a (s.erase x) ha_not := by
        ext y
        simp only [Finset.mem_erase, Finset.mem_cons]
        constructor
        · rintro ⟨hyx, rfl | hys⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hyx, hys⟩
        · rintro (rfl | ⟨hyx, hys⟩)
          · exact ⟨hne, Or.inl rfl⟩
          · exact ⟨hyx, Or.inr hys⟩
      rw [heq, Finset.prod_cons]
    rw [Finset.prod_congr rfl hinner, Finset.prod_mul_distrib, ← mul_assoc,
      ← Finset.prod_mul_distrib, hih]
    have hpair : ∀ y ∈ s,
        jacobiSym (y : ℤ) a * jacobiSym (a : ℤ) y = (-1 : ℤ) ^ (y / 2 * (a / 2)) := by
      intro y hy
      have hy_odd : Odd y := hs_odd y hy
      have hne : a ≠ y := fun h => ha (h ▸ hy)
      have hcop_ay : Nat.Coprime a y :=
        hcop a (Finset.mem_cons_self a s) y (Finset.mem_cons_of_mem hy) hne
      have hgcd : (a : ℤ).gcd y = 1 := by
        change Nat.gcd (a : ℤ).natAbs (y : ℤ).natAbs = 1
        simpa using hcop_ay.gcd_eq_one
      rw [jacobiSym.quadratic_reciprocity hy_odd ha_odd, mul_assoc, ← sq,
        jacobiSym.sq_one hgcd, mul_one]
    rw [Finset.prod_congr rfl hpair]
    have ha2 : a % 2 = 1 := Nat.odd_iff.mp ha_odd
    by_cases ha3 : a % 4 = 3
    · have hterm : ∀ y ∈ s,
          (-1 : ℤ) ^ (y / 2 * (a / 2)) = if y % 4 = 3 then (-1 : ℤ) else 1 := by
        intro y hy
        have hy2 : y % 2 = 1 := Nat.odd_iff.mp (hs_odd y hy)
        by_cases hy3 : y % 4 = 3
        · rw [if_pos hy3]
          have hy_div : (y / 2) % 2 = 1 := by omega
          have ha_div : (a / 2) % 2 = 1 := by omega
          have hodd_prod : Odd (y / 2 * (a / 2)) := by
            rw [Nat.odd_iff, Nat.mul_mod, hy_div, ha_div]
          exact hodd_prod.neg_one_pow
        · rw [if_neg hy3]
          have hy_div : (y / 2) % 2 = 0 := by omega
          have heven_prod : Even (y / 2 * (a / 2)) := by
            rw [Nat.even_iff, Nat.mul_mod, hy_div, zero_mul, Nat.zero_mod]
          exact heven_prod.neg_one_pow
      rw [Finset.prod_congr rfl hterm, Finset.prod_ite, Finset.prod_const,
        Finset.prod_const_one, mul_one, ← pow_add]
      have hfilt : ((Finset.cons a s ha).filter (fun p => p % 4 = 3)).card =
          (s.filter (fun p => p % 4 = 3)).card + 1 := by
        rw [Finset.filter_cons, if_pos ha3, Finset.card_cons]
      rw [hfilt, Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    · have hterm : ∀ y ∈ s, (-1 : ℤ) ^ (y / 2 * (a / 2)) = 1 := by
        intro y _
        have ha_div : (a / 2) % 2 = 0 := by omega
        have heven_prod : Even (y / 2 * (a / 2)) := by
          rw [Nat.even_iff, Nat.mul_mod, ha_div, mul_zero, Nat.zero_mod]
        exact heven_prod.neg_one_pow
      rw [Finset.prod_congr rfl hterm, Finset.prod_const_one, one_mul]
      have hfilt : ((Finset.cons a s ha).filter (fun p => p % 4 = 3)).card =
          (s.filter (fun p => p % 4 = 3)).card := by
        rw [Finset.filter_cons, if_neg ha3]
      rw [hfilt]

lemma qr_r3_mod_four {n : ℕ} (hsqf : Squarefree n) (hodd : Odd n)
    (hdvd : ∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) :
    (n.primeFactors.filter (fun p => p % 4 = 3)).card % 4 = 0 ∨
      (n.primeFactors.filter (fun p => p % 4 = 3)).card % 4 = 1 := by
  have hn0 : n ≠ 0 := hsqf.ne_zero
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  have hodd_pf : ∀ p ∈ n.primeFactors, Odd p := by
    intro p hp
    have hmul : n / p * p = n := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
    have : (n / p * p) % 2 = 1 := hmul.symm ▸ hn2
    rcases Nat.mod_two_eq_zero_or_one p with h0 | h1
    · rw [Nat.mul_mod, h0, mul_zero, Nat.zero_mod] at this
      omega
    · exact Nat.odd_iff.mpr h1
  have hcop_pf : ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, p ≠ q → Nat.Coprime p q := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq
  have hprod_eq := prod_jacobiSym_offDiag n.primeFactors hodd_pf hcop_pf
  have hprod_n : ∏ p ∈ n.primeFactors, p = n := prod_primeFactors_of_sqf hsqf hn0
  have hlhs : ∏ p ∈ n.primeFactors, ∏ q ∈ n.primeFactors.erase p, jacobiSym (q : ℤ) p = 1 := by
    refine Finset.prod_eq_one fun p hp => ?_
    rw [← jacobiSym_prod_left]
    have herase_prod : ∏ q ∈ n.primeFactors.erase p, q = n / p := by
      have hpmul : p * ∏ q ∈ n.primeFactors.erase p, q = n := by
        rw [Finset.mul_prod_erase n.primeFactors (fun q => q) hp]
        exact hprod_n
      have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
      exact Nat.eq_div_of_mul_eq_right hp0.ne' hpmul
    rw [herase_prod]
    have hp_dvd_sub : p ∣ (n / p - 1) := dvd_trans (dvd_mul_right p (p - 1)) (hdvd p hp)
    have hdiv_pos : 1 ≤ n / p := by
      have hp_le : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_primeFactors hp)
      exact Nat.div_pos hp_le (Nat.prime_of_mem_primeFactors hp).pos
    have hmod_nat : (n / p) % p = 1 % p := by
      obtain ⟨c, hc⟩ := hp_dvd_sub
      have hnp : n / p = p * c + 1 := by omega
      rw [hnp, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
    have hmod_int : ((n / p : ℕ) : ℤ) % (p : ℕ) = (1 : ℤ) % (p : ℕ) := by
      exact_mod_cast hmod_nat
    rw [jacobiSym.mod_left' hmod_int, jacobiSym.one_left]
  rw [hlhs] at hprod_eq
  set r3 := (n.primeFactors.filter (fun p => p % 4 = 3)).card
  have heven_choose : Even (r3.choose 2) := by
    by_contra hnot
    have hodd_c : Odd (r3.choose 2) := Nat.not_even_iff_odd.mp hnot
    rw [hodd_c.neg_one_pow] at hprod_eq
    omega
  rw [Nat.choose_two_right, Nat.even_iff] at heven_choose
  have hcase : r3 % 4 = 0 ∨ r3 % 4 = 1 ∨ r3 % 4 = 2 ∨ r3 % 4 = 3 := by omega
  rcases hcase with h0 | h1 | h2 | h3
  · exact Or.inl h0
  · exact Or.inr h1
  · exfalso
    set q := r3 / 4
    have hq : r3 = 4 * q + 2 := by omega
    have hq1 : r3 - 1 = 4 * q + 1 := by omega
    have hmul : r3 * (r3 - 1) = 2 * ((2 * q + 1) * (4 * q + 1)) := by
      rw [hq1, hq]
      ring
    have hdiv : r3 * (r3 - 1) / 2 = (2 * q + 1) * (4 * q + 1) := by
      rw [hmul, Nat.mul_div_cancel_left _ (by omega)]
    have h1' : (2 * q + 1) % 2 = 1 := by omega
    have h2' : (4 * q + 1) % 2 = 1 := by omega
    rw [hdiv, Nat.mul_mod, h1', h2'] at heven_choose
    omega
  · exfalso
    set q := r3 / 4
    have hq : r3 = 4 * q + 3 := by omega
    have hq1 : r3 - 1 = 4 * q + 2 := by omega
    have hmul : r3 * (r3 - 1) = 2 * ((4 * q + 3) * (2 * q + 1)) := by
      rw [hq1, hq]
      ring
    have hdiv : r3 * (r3 - 1) / 2 = (4 * q + 3) * (2 * q + 1) := by
      rw [hmul, Nat.mul_div_cancel_left _ (by omega)]
    have h1' : (4 * q + 3) % 2 = 1 := by omega
    have h2' : (2 * q + 1) % 2 = 1 := by omega
    rw [hdiv, Nat.mul_mod, h1', h2'] at heven_choose
    omega

lemma prod_mod_four_of_odd (s : Finset ℕ) (hodd : ∀ p ∈ s, Odd p) :
    (∏ p ∈ s, p) % 4 = if (s.filter (fun p => p % 4 = 3)).card % 2 = 0 then 1 else 3 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have ha_odd := hodd a (Finset.mem_cons_self a s)
    have hs_odd : ∀ p ∈ s, Odd p := fun p hp => hodd p (Finset.mem_cons_of_mem hp)
    have hih := ih hs_odd
    have ha2 : a % 2 = 1 := Nat.odd_iff.mp ha_odd
    rw [Finset.prod_cons, Nat.mul_mod, hih, Finset.filter_cons]
    by_cases ha3 : a % 4 = 3
    · rw [if_pos ha3, Finset.card_cons, ha3]
      split_ifs <;> omega
    · rw [if_neg ha3]
      have ha1 : a % 4 = 1 := by omega
      rw [ha1]
      split_ifs <;> omega

lemma sum_mod_four_split (s : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ p ∈ s, (p % 4 = 1 → f p % 4 = 1) ∧ (p % 4 = 3 → f p % 4 = 3))
    (hodd : ∀ p ∈ s, Odd p) :
    (∑ p ∈ s, f p) % 4 =
      ((s.filter (fun p => p % 4 = 1)).card + 3 * (s.filter (fun p => p % 4 = 3)).card) % 4 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have ha_odd := hodd a (Finset.mem_cons_self a s)
    have ha2 : a % 2 = 1 := Nat.odd_iff.mp ha_odd
    have hs_odd : ∀ p ∈ s, Odd p := fun p hp => hodd p (Finset.mem_cons_of_mem hp)
    have hih := ih (fun p hp => hf p (Finset.mem_cons_of_mem hp)) hs_odd
    have hfa := hf a (Finset.mem_cons_self a s)
    rw [Finset.sum_cons, Finset.filter_cons, Finset.filter_cons]
    by_cases ha1 : a % 4 = 1
    · have ha3 : ¬ (a % 4 = 3) := by omega
      rw [if_pos ha1, if_neg ha3, Finset.card_cons]
      have := hfa.1 ha1
      omega
    · have ha3 : a % 4 = 3 := by omega
      rw [if_neg ha1, if_pos ha3, Finset.card_cons]
      have := hfa.2 ha3
      omega

lemma card_eq_r1_add_r3 (s : Finset ℕ) (hodd : ∀ p ∈ s, Odd p) :
    s.card = (s.filter (fun p => p % 4 = 1)).card + (s.filter (fun p => p % 4 = 3)).card := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have ha2 : a % 2 = 1 := Nat.odd_iff.mp (hodd a (Finset.mem_cons_self a s))
    have hih := ih fun p hp => hodd p (Finset.mem_cons_of_mem hp)
    rw [Finset.card_cons, Finset.filter_cons, Finset.filter_cons]
    by_cases ha1 : a % 4 = 1
    · have ha3 : ¬ (a % 4 = 3) := by omega
      rw [if_pos ha1, if_neg ha3, Finset.card_cons]
      omega
    · have ha3 : a % 4 = 3 := by omega
      rw [if_neg ha1, if_pos ha3, Finset.card_cons]
      omega

/- ### Section 3: Mod-8 characteristic-vector congruence ω(n) ≡ k + 1 (mod 8) -/

lemma odd_sq_mod_eight {m : ℕ} (hm : Odd m) : (m * m) % 8 = 1 := by
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
  have hcase : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by omega
  rcases hcase with h | h | h | h <;> rw [Nat.mul_mod, h]

lemma card_eq_mod_eight (s : Finset ℕ) (hodd : ∀ p ∈ s, Odd p) :
    s.card = (s.filter (fun p => p % 8 = 1)).card + (s.filter (fun p => p % 8 = 3)).card +
      (s.filter (fun p => p % 8 = 5)).card + (s.filter (fun p => p % 8 = 7)).card := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have ha2 : a % 2 = 1 := Nat.odd_iff.mp (hodd a (Finset.mem_cons_self a s))
    have hih := ih fun p hp => hodd p (Finset.mem_cons_of_mem hp)
    rw [Finset.card_cons, Finset.filter_cons, Finset.filter_cons,
      Finset.filter_cons, Finset.filter_cons]
    have hcase : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
    rcases hcase with h | h | h | h
    · rw [if_pos h, if_neg (by omega), if_neg (by omega), if_neg (by omega), Finset.card_cons]
      omega
    · rw [if_neg (by omega), if_pos h, if_neg (by omega), if_neg (by omega), Finset.card_cons]
      omega
    · rw [if_neg (by omega), if_neg (by omega), if_pos h, if_neg (by omega), Finset.card_cons]
      omega
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h, Finset.card_cons]
      omega

lemma r3_eq_c3_add_c7 (s : Finset ℕ) (hodd : ∀ p ∈ s, Odd p) :
    (s.filter (fun p => p % 4 = 3)).card =
      (s.filter (fun p => p % 8 = 3)).card + (s.filter (fun p => p % 8 = 7)).card := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have ha2 : a % 2 = 1 := Nat.odd_iff.mp (hodd a (Finset.mem_cons_self a s))
    have hih := ih fun p hp => hodd p (Finset.mem_cons_of_mem hp)
    rw [Finset.filter_cons, Finset.filter_cons, Finset.filter_cons]
    have hcase : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
    rcases hcase with h | h | h | h
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact hih
    · rw [if_pos (by omega), if_pos h, if_neg (by omega), Finset.card_cons, Finset.card_cons]
      omega
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact hih
    · rw [if_pos (by omega), if_neg (by omega), if_pos h, Finset.card_cons, Finset.card_cons]
      omega

lemma prod_mod_eight_of_odd (s : Finset ℕ) (hodd : ∀ p ∈ s, Odd p) :
    (∏ p ∈ s, p) % 8 =
      if ((s.filter (fun p => p % 8 = 3)).card + (s.filter (fun p => p % 8 = 7)).card) % 2 = 0
      then
        if ((s.filter (fun p => p % 8 = 3)).card + (s.filter (fun p => p % 8 = 5)).card) % 2 = 0
        then 1 else 5
      else
        if ((s.filter (fun p => p % 8 = 3)).card + (s.filter (fun p => p % 8 = 5)).card) % 2 = 0
        then 7 else 3 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have ha2 : a % 2 = 1 := Nat.odd_iff.mp (hodd a (Finset.mem_cons_self a s))
    have hih := ih fun p hp => hodd p (Finset.mem_cons_of_mem hp)
    rw [Finset.prod_cons, Nat.mul_mod, hih, Finset.filter_cons, Finset.filter_cons,
      Finset.filter_cons]
    have hcase : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
    rcases hcase with h | h | h | h
    · have h3 : a % 8 ≠ 3 := by omega
      have h5 : a % 8 ≠ 5 := by omega
      have h7 : a % 8 ≠ 7 := by omega
      rw [if_neg h3, if_neg h7, if_neg h5, h]
      split_ifs <;> omega
    · have h5 : a % 8 ≠ 5 := by omega
      have h7 : a % 8 ≠ 7 := by omega
      rw [if_pos h, if_neg h7, if_neg h5, Finset.card_cons, h]
      split_ifs <;> omega
    · have h3 : a % 8 ≠ 3 := by omega
      have h7 : a % 8 ≠ 7 := by omega
      rw [if_neg h3, if_neg h7, if_pos h, Finset.card_cons, h]
      split_ifs <;> omega
    · have h3 : a % 8 ≠ 3 := by omega
      have h5 : a % 8 ≠ 5 := by omega
      rw [if_neg h3, if_pos h, if_neg h5, Finset.card_cons, h]
      split_ifs <;> omega

lemma sum_mod_eight_of_mul (s : Finset ℕ) (n : ℕ) (f : ℕ → ℕ)
    (hodd : ∀ p ∈ s, Odd p) (hf : ∀ p ∈ s, f p % 8 = (n * p) % 8) :
    (∑ p ∈ s, f p) % 8 =
      (n * ((s.filter (fun p => p % 8 = 1)).card +
        3 * (s.filter (fun p => p % 8 = 3)).card +
        5 * (s.filter (fun p => p % 8 = 5)).card +
        7 * (s.filter (fun p => p % 8 = 7)).card)) % 8 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have ha2 : a % 2 = 1 := Nat.odd_iff.mp (hodd a (Finset.mem_cons_self a s))
    have hfa := hf a (Finset.mem_cons_self a s)
    have hih := ih (fun p hp => hodd p (Finset.mem_cons_of_mem hp))
      (fun p hp => hf p (Finset.mem_cons_of_mem hp))
    rw [Finset.sum_cons, Finset.filter_cons, Finset.filter_cons,
      Finset.filter_cons, Finset.filter_cons]
    have hcase : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
    rcases hcase with h | h | h | h
    · rw [if_pos h, if_neg (by omega), if_neg (by omega), if_neg (by omega), Finset.card_cons]
      set c1 := (s.filter (fun p => p % 8 = 1)).card
      set c3 := (s.filter (fun p => p % 8 = 3)).card
      set c5 := (s.filter (fun p => p % 8 = 5)).card
      set c7 := (s.filter (fun p => p % 8 = 7)).card
      have hfa' : f a % 8 = (n * 1) % 8 := by
        rw [hfa, Nat.mul_mod n a 8, Nat.mul_mod n 1 8, h]
      have hlin : n * (c1 + 1 + 3 * c3 + 5 * c5 + 7 * c7) =
          n * 1 + n * (c1 + 3 * c3 + 5 * c5 + 7 * c7) := by ring
      rw [hlin, Nat.add_mod (f a), hfa', hih, ← Nat.add_mod]
    · rw [if_neg (by omega), if_pos h, if_neg (by omega), if_neg (by omega), Finset.card_cons]
      set c1 := (s.filter (fun p => p % 8 = 1)).card
      set c3 := (s.filter (fun p => p % 8 = 3)).card
      set c5 := (s.filter (fun p => p % 8 = 5)).card
      set c7 := (s.filter (fun p => p % 8 = 7)).card
      have hfa' : f a % 8 = (n * 3) % 8 := by
        rw [hfa, Nat.mul_mod n a 8, Nat.mul_mod n 3 8, h]
      have hlin : n * (c1 + 3 * (c3 + 1) + 5 * c5 + 7 * c7) =
          n * 3 + n * (c1 + 3 * c3 + 5 * c5 + 7 * c7) := by ring
      rw [hlin, Nat.add_mod (f a), hfa', hih, ← Nat.add_mod]
    · rw [if_neg (by omega), if_neg (by omega), if_pos h, if_neg (by omega), Finset.card_cons]
      set c1 := (s.filter (fun p => p % 8 = 1)).card
      set c3 := (s.filter (fun p => p % 8 = 3)).card
      set c5 := (s.filter (fun p => p % 8 = 5)).card
      set c7 := (s.filter (fun p => p % 8 = 7)).card
      have hfa' : f a % 8 = (n * 5) % 8 := by
        rw [hfa, Nat.mul_mod n a 8, Nat.mul_mod n 5 8, h]
      have hlin : n * (c1 + 3 * c3 + 5 * (c5 + 1) + 7 * c7) =
          n * 5 + n * (c1 + 3 * c3 + 5 * c5 + 7 * c7) := by ring
      rw [hlin, Nat.add_mod (f a), hfa', hih, ← Nat.add_mod]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h, Finset.card_cons]
      set c1 := (s.filter (fun p => p % 8 = 1)).card
      set c3 := (s.filter (fun p => p % 8 = 3)).card
      set c5 := (s.filter (fun p => p % 8 = 5)).card
      set c7 := (s.filter (fun p => p % 8 = 7)).card
      have hfa' : f a % 8 = (n * 7) % 8 := by
        rw [hfa, Nat.mul_mod n a 8, Nat.mul_mod n 7 8, h]
      have hlin : n * (c1 + 3 * c3 + 5 * c5 + 7 * (c7 + 1)) =
          n * 7 + n * (c1 + 3 * c3 + 5 * c5 + 7 * c7) := by ring
      rw [hlin, Nat.add_mod (f a), hfa', hih, ← Nat.add_mod]

lemma omega_mod_eight_eq_k_add_one {n k : ℕ} (hsqf : Squarefree n) (hodd : Odd n)
    (hdvd : ∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1))
    (hint : ∑ p ∈ n.primeFactors, n / p = k * n + 1) :
    n.primeFactors.card % 8 = (k + 1) % 8 := by
  have hn0 : n ≠ 0 := hsqf.ne_zero
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  have hodd_pf : ∀ p ∈ n.primeFactors, Odd p := by
    intro p hp
    have hmul : n / p * p = n := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
    have : (n / p * p) % 2 = 1 := hmul.symm ▸ hn2
    rcases Nat.mod_two_eq_zero_or_one p with h0 | h1
    · rw [Nat.mul_mod, h0, mul_zero, Nat.zero_mod] at this
      omega
    · exact Nat.odd_iff.mpr h1
  have hdiv_mod8 : ∀ p ∈ n.primeFactors, (n / p) % 8 = (n * p) % 8 := by
    intro p hp
    have hmul : n / p * p = n := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
    have hpp : (p * p) % 8 = 1 := odd_sq_mod_eight (hodd_pf p hp)
    calc (n / p) % 8
        = ((n / p) % 8 * 1) % 8 := by omega
      _ = ((n / p) % 8 * ((p * p) % 8)) % 8 := by rw [hpp]
      _ = (n / p * (p * p)) % 8 := (Nat.mul_mod (n / p) (p * p) 8).symm
      _ = (n / p * p * p) % 8 := by rw [mul_assoc]
      _ = (n * p) % 8 := by rw [hmul]
  set c1 := (n.primeFactors.filter (fun p => p % 8 = 1)).card
  set c3 := (n.primeFactors.filter (fun p => p % 8 = 3)).card
  set c5 := (n.primeFactors.filter (fun p => p % 8 = 5)).card
  set c7 := (n.primeFactors.filter (fun p => p % 8 = 7)).card
  set S := c1 + 3 * c3 + 5 * c5 + 7 * c7
  have hsum8 : (k * n + 1) % 8 = (n * S) % 8 := by
    rw [← hint]
    exact sum_mod_eight_of_mul n.primeFactors n (fun p => n / p) hodd_pf hdiv_mod8
  have hnn : (n * n) % 8 = 1 := odd_sq_mod_eight hodd
  have hS_eq : S % 8 = (k + n) % 8 := by
    have hmul_eq : (n * (k * n + 1)) % 8 = (n * (n * S)) % 8 := by
      rw [Nat.mul_mod, hsum8, ← Nat.mul_mod]
    have hlhs : (n * (k * n + 1)) % 8 = (k + n) % 8 := by
      have hre : n * (k * n + 1) = k * (n * n) + n := by ring
      rw [hre, Nat.add_mod, Nat.mul_mod, hnn]
      omega
    have hrhs : (n * (n * S)) % 8 = S % 8 := by
      rw [← mul_assoc, Nat.mul_mod, hnn]
      omega
    omega
  have hprod_n : ∏ p ∈ n.primeFactors, p = n := prod_primeFactors_of_sqf hsqf hn0
  have hn_mod8 : n % 8 =
      if (c3 + c7) % 2 = 0 then (if (c3 + c5) % 2 = 0 then 1 else 5)
      else (if (c3 + c5) % 2 = 0 then 7 else 3) := by
    conv_lhs => rw [← hprod_n]
    exact prod_mod_eight_of_odd n.primeFactors hodd_pf
  have hcard : n.primeFactors.card = c1 + c3 + c5 + c7 :=
    card_eq_mod_eight n.primeFactors hodd_pf
  have hqr := qr_r3_mod_four hsqf hodd hdvd
  rw [r3_eq_c3_add_c7 n.primeFactors hodd_pf] at hqr
  split_ifs at hn_mod8 <;> omega

/- ### Section 4: Multi-AP logarithmic-harmonic bounds and AM-GM inequalities -/

lemma exp_nat_eq_pow (m : ℕ) : Real.exp (m : ℝ) = (Real.exp 1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ, Real.exp_add, ih, pow_succ]

lemma inv_le_log_diff {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    1 / (a + d) ≤ (1 / d) * (Real.log (a + d) - Real.log a) := by
  have had : 0 < a + d := by linarith
  have hdiv_pos : 0 < a / (a + d) := div_pos ha had
  have hlog := Real.log_le_sub_one_of_pos hdiv_pos
  rw [Real.log_div ha.ne' had.ne'] at hlog
  have hsub : a / (a + d) - 1 = -d / (a + d) := by
    field_simp [had.ne']
    ring
  rw [hsub, neg_div] at hlog
  have hmul : d / (a + d) ≤ Real.log (a + d) - Real.log a := by linarith
  have hstep := mul_le_mul_of_nonneg_left hmul (le_of_lt (one_div_pos.mpr hd))
  have hlhs : 1 / d * (d / (a + d)) = 1 / (a + d) := by
    field_simp [hd.ne', had.ne']
  rwa [hlhs] at hstep

lemma sum_inv_ap_le_log (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) :
    ∑ i ∈ Finset.range (m + 1), (1 / ((a + d * i : ℕ) : ℝ)) ≤
      1 / (a : ℝ) + (1 / (d : ℝ)) * (Real.log ((a + d * m : ℕ) : ℝ) - Real.log (a : ℝ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have ham : (0 : ℝ) < ((a + d * m : ℕ) : ℝ) := by positivity
    have hdR : (0 : ℝ) < (d : ℝ) := by positivity
    have hstep := inv_le_log_diff ham hdR
    have hcast : ((a + d * m : ℕ) : ℝ) + (d : ℝ) = ((a + d * (m + 1) : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hcast] at hstep
    linarith

lemma sum_inv_finset_ap_le (s : Finset ℕ) (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hs : ∀ x ∈ s, a ≤ x ∧ x % d = a % d) (hne : 0 < s.card) :
    ∑ x ∈ s, (1 / (x : ℝ)) ≤
      1 / (a : ℝ) + (1 / (d : ℝ)) * (Real.log ((a + d * (s.card - 1) : ℕ) : ℝ) - Real.log (a : ℝ)) := by
  let e : Fin s.card ↪o ℕ := s.orderEmbOfFin rfl
  have himg : Finset.univ.image e = s := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      exact Finset.orderEmbOfFin_mem s rfl i
    · rw [Finset.card_image_of_injective _ e.injective, Finset.card_fin]
  have hsum_e : ∑ x ∈ s, (1 / (x : ℝ)) = ∑ i : Fin s.card, (1 / (e i : ℝ)) := by
    conv_lhs => rw [← himg]
    rw [Finset.sum_image (fun i _ j _ h => e.injective h)]
  have hbound : ∀ i : ℕ, (hi : i < s.card) → a + d * i ≤ e ⟨i, hi⟩ := by
    intro i
    induction i with
    | zero =>
      intro hi
      simpa using (hs (e ⟨0, hi⟩) (Finset.orderEmbOfFin_mem s rfl ⟨0, hi⟩)).1
    | succ i ih =>
      intro hi
      have hi' : i < s.card := by omega
      have hprev := ih hi'
      have hlt : e ⟨i, hi'⟩ < e ⟨i + 1, hi⟩ := e.strictMono (by exact Nat.lt_succ_self i)
      have hmod1 := (hs (e ⟨i, hi'⟩) (Finset.orderEmbOfFin_mem s rfl ⟨i, hi'⟩)).2
      have hmod2 := (hs (e ⟨i + 1, hi⟩) (Finset.orderEmbOfFin_mem s rfl ⟨i + 1, hi⟩)).2
      have hmod_eq : e ⟨i, hi'⟩ % d = e ⟨i + 1, hi⟩ % d := hmod1.trans hmod2.symm
      have hdiv1 := (Nat.div_add_mod (e ⟨i, hi'⟩) d).symm
      have hdiv2 := (Nat.div_add_mod (e ⟨i + 1, hi⟩) d).symm
      have hq_lt : e ⟨i, hi'⟩ / d < e ⟨i + 1, hi⟩ / d := by
        by_contra hle
        have hq_le : e ⟨i + 1, hi⟩ / d ≤ e ⟨i, hi'⟩ / d := Nat.le_of_not_lt hle
        have hmul_le : d * (e ⟨i + 1, hi⟩ / d) ≤ d * (e ⟨i, hi'⟩ / d) :=
          Nat.mul_le_mul_left d hq_le
        omega
      have hmul_step : d * (e ⟨i, hi'⟩ / d) + d ≤ d * (e ⟨i + 1, hi⟩ / d) := by
        have h1 : e ⟨i, hi'⟩ / d + 1 ≤ e ⟨i + 1, hi⟩ / d := hq_lt
        have h2 := Nat.mul_le_mul_left d h1
        linarith
      have hdiff : e ⟨i, hi'⟩ + d ≤ e ⟨i + 1, hi⟩ := by omega
      have hmul_succ : a + d * (i + 1) = a + d * i + d := by ring
      omega
  have hle_sum : ∑ i : Fin s.card, (1 / (e i : ℝ)) ≤
      ∑ i ∈ Finset.range s.card, (1 / ((a + d * i : ℕ) : ℝ)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (1 / ((a + d * i : ℕ) : ℝ))) s.card]
    refine Finset.sum_le_sum fun i _ => ?_
    have hpos : (0 : ℝ) < ((a + d * i.val : ℕ) : ℝ) := by positivity
    have hleR : ((a + d * i.val : ℕ) : ℝ) ≤ (e i : ℝ) := by
      exact_mod_cast hbound i.val i.isLt
    exact one_div_le_one_div_of_le hpos hleR
  have hcard : s.card = (s.card - 1) + 1 := by omega
  calc ∑ x ∈ s, (1 / (x : ℝ))
      = ∑ i : Fin s.card, (1 / (e i : ℝ)) := hsum_e
    _ ≤ ∑ i ∈ Finset.range s.card, (1 / ((a + d * i : ℕ) : ℝ)) := hle_sum
    _ = ∑ i ∈ Finset.range ((s.card - 1) + 1), (1 / ((a + d * i : ℕ) : ℝ)) := by rw [← hcard]
    _ ≤ 1 / (a : ℝ) + (1 / (d : ℝ)) *
          (Real.log ((a + d * (s.card - 1) : ℕ) : ℝ) - Real.log (a : ℝ)) :=
        sum_inv_ap_le_log a d (s.card - 1) ha hd

lemma sum_inv_finset_ap_le_add (s : Finset ℕ) (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hs : ∀ x ∈ s, a ≤ x ∧ x % d = a % d) :
    ∑ x ∈ s, (1 / (x : ℝ)) ≤
      1 / (a : ℝ) + (1 / (d : ℝ)) * (Real.log (((a + d * s.card : ℕ) : ℝ) / (a : ℝ))) := by
  have haR : (0 : ℝ) < (a : ℝ) := by positivity
  have hdR : (0 : ℝ) < (d : ℝ) := by positivity
  have hpos_card : (0 : ℝ) < ((a + d * s.card : ℕ) : ℝ) := by positivity
  rw [Real.log_div hpos_card.ne' haR.ne']
  by_cases hne : 0 < s.card
  · have h1 := sum_inv_finset_ap_le s a d ha hd hs hne
    have hpos_sub : (0 : ℝ) < ((a + d * (s.card - 1) : ℕ) : ℝ) := by positivity
    have hle_arg : ((a + d * (s.card - 1) : ℕ) : ℝ) ≤ ((a + d * s.card : ℕ) : ℝ) := by
      exact_mod_cast (show a + d * (s.card - 1) ≤ a + d * s.card by
        have := Nat.mul_le_mul_left d (Nat.sub_le s.card 1)
        omega)
    have hlog := Real.log_le_log hpos_sub hle_arg
    have hmul : (1 / (d : ℝ)) * (Real.log ((a + d * (s.card - 1) : ℕ) : ℝ) - Real.log (a : ℝ)) ≤
        (1 / (d : ℝ)) * (Real.log ((a + d * s.card : ℕ) : ℝ) - Real.log (a : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  · have hcard0 : s.card = 0 := by omega
    have hemp : s = ∅ := Finset.card_eq_zero.mp hcard0
    subst hemp
    simp

lemma sum_real_gt_k {n k : ℕ} (hn0 : n ≠ 0)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    (k : ℝ) < ∑ p ∈ n.primeFactors, (1 / (p : ℝ)) := by
  have hq : (k : ℚ) < ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) := by
    have hn_pos : (0 : ℚ) < 1 / (n : ℚ) :=
      one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0))
    linarith
  have hr : ((k : ℚ) : ℝ) < ((∑ p ∈ n.primeFactors, (1 / (p : ℚ)) : ℚ) : ℝ) := by
    exact_mod_cast hq
  simpa [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using hr

lemma mul3_le_cube {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    27 * (a * b * c) ≤ (a + b + c) ^ 3 := by
  have hid : (a + b + c) ^ 3 - 27 * (a * b * c) =
      (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / 2 +
        3 * a * (b - c) ^ 2 + 3 * b * (c - a) ^ 2 + 3 * c * (a - b) ^ 2 := by ring
  have hnn : 0 ≤ (a + b + c) ^ 3 - 27 * (a * b * c) := by
    rw [hid]
    positivity
  linarith

lemma mul4_le_pow_four {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    256 * (a * b * c * d) ≤ (a + b + c + d) ^ 4 := by
  have h1 : 4 * (a * b) ≤ (a + b) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have h2 : 4 * (c * d) ≤ (c + d) ^ 2 := by nlinarith [sq_nonneg (c - d)]
  have h12 : 16 * (a * b * c * d) ≤ ((a + b) * (c + d)) ^ 2 := by
    have hmul := mul_le_mul h1 h2 (by positivity) (by positivity)
    linarith [show (4 * (a * b)) * (4 * (c * d)) = 16 * (a * b * c * d) by ring,
      show (a + b) ^ 2 * (c + d) ^ 2 = ((a + b) * (c + d)) ^ 2 by ring]
  have h3 : 4 * ((a + b) * (c + d)) ≤ (a + b + c + d) ^ 2 := by
    nlinarith [sq_nonneg (a + b - c - d)]
  have h3sq : (4 * ((a + b) * (c + d))) ^ 2 ≤ ((a + b + c + d) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h3 2
  have hre1 : (4 * ((a + b) * (c + d))) ^ 2 = 16 * ((a + b) * (c + d)) ^ 2 := by ring
  have hre2 : ((a + b + c + d) ^ 2) ^ 2 = (a + b + c + d) ^ 4 := by ring
  rw [hre1, hre2] at h3sq
  linarith

lemma exp_gt_pow_27_10 (m : ℕ) (hm : 0 < m) : (27 / 10 : ℝ) ^ m < Real.exp (m : ℝ) := by
  have hbase : (27 / 10 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  calc (27 / 10 : ℝ) ^ m
      < (Real.exp 1) ^ m := pow_lt_pow_left₀ hbase (by positivity) hm.ne'
    _ = Real.exp (m : ℝ) := (exp_nat_eq_pow m).symm

lemma card_ge_1000000_of_three_five {n k : ℕ} (hn0 : n ≠ 0) (hk2 : 2 ≤ k)
    (h3dvd : 3 ∣ n) (h5dvd : 5 ∣ n)
    (hres : ∀ p ∈ n.primeFactors, p = 3 ∨ p = 5 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    1000000 ≤ n.primeFactors.card := by
  by_contra hlt
  have h3_mem : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3dvd, hn0⟩
  have h5_mem : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, h5dvd, hn0⟩
  have h5_er : 5 ∈ n.primeFactors.erase 3 := Finset.mem_erase.mpr ⟨by omega, h5_mem⟩
  set S := (n.primeFactors.erase 3).erase 5
  have hS_card : S.card = n.primeFactors.card - 2 := by
    rw [Finset.card_erase_of_mem h5_er, Finset.card_erase_of_mem h3_mem]
    omega
  have hS_le : S.card ≤ 999997 := by omega
  have hsum_split : ∑ p ∈ n.primeFactors, (1 / (p : ℝ)) =
      1 / (3 : ℝ) + 1 / (5 : ℝ) + ∑ p ∈ S, (1 / (p : ℝ)) := by
    have h1 := Finset.add_sum_erase n.primeFactors (fun p => (1 / (p : ℝ))) h3_mem
    have h2 := Finset.add_sum_erase (n.primeFactors.erase 3) (fun p => (1 / (p : ℝ))) h5_er
    simp only [Nat.cast_ofNat] at h1 h2
    linarith
  have hsum_real := sum_real_gt_k hn0 hsum
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hS_gt : (22 / 15 : ℝ) < ∑ p ∈ S, (1 / (p : ℝ)) := by linarith
  set S17 := S.filter (fun p => p % 30 = 17)
  set S23 := S.filter (fun p => p % 30 = 23)
  set S29 := S.filter (fun p => p % 30 = 29)
  have hS_res : ∀ p ∈ S, p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29 := by
    intro p hp
    rcases Finset.mem_erase.mp hp with ⟨hp5, hp3'⟩
    rcases Finset.mem_erase.mp hp3' with ⟨hp3, hp_mem⟩
    rcases hres p hp_mem with rfl | rfl | h17 | h23 | h29
    · exact absurd rfl hp3
    · exact absurd rfl hp5
    · exact Or.inl h17
    · exact Or.inr (Or.inl h23)
    · exact Or.inr (Or.inr h29)
  have hdisj23 : Disjoint S23 S29 := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by omega)
  have hdisj1 : Disjoint S17 (S23 ∪ S29) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp23
    have h1 := (Finset.mem_filter.mp hp1).2
    rcases Finset.mem_union.mp hp23 with h2 | h3
    · have := (Finset.mem_filter.mp h2).2; omega
    · have := (Finset.mem_filter.mp h3).2; omega
  have hunion : S17 ∪ (S23 ∪ S29) = S := by
    ext p
    simp only [S17, S23, S29, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    · intro hp
      rcases hS_res p hp with h17 | h23 | h29
      · exact Or.inl ⟨hp, h17⟩
      · exact Or.inr (Or.inl ⟨hp, h23⟩)
      · exact Or.inr (Or.inr ⟨hp, h29⟩)
  have hcard_sum : S17.card + S23.card + S29.card = S.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj23]
    omega
  have hsum_part : ∑ p ∈ S, (1 / (p : ℝ)) =
      ∑ p ∈ S17, (1 / (p : ℝ)) + ∑ p ∈ S23, (1 / (p : ℝ)) + ∑ p ∈ S29, (1 / (p : ℝ)) := by
    rw [← hunion, Finset.sum_union hdisj1, Finset.sum_union hdisj23]
    ring
  have hb17 := sum_inv_finset_ap_le_add S17 17 30 (by omega) (by omega) (fun p hp => by
    have h := (Finset.mem_filter.mp hp).2; exact ⟨by omega, by omega⟩)
  have hb23 := sum_inv_finset_ap_le_add S23 23 30 (by omega) (by omega) (fun p hp => by
    have h := (Finset.mem_filter.mp hp).2; exact ⟨by omega, by omega⟩)
  have hb29 := sum_inv_finset_ap_le_add S29 29 30 (by omega) (by omega) (fun p hp => by
    have h := (Finset.mem_filter.mp hp).2; exact ⟨by omega, by omega⟩)
  set A1 : ℝ := ((17 + 30 * S17.card : ℕ) : ℝ)
  set A2 : ℝ := ((23 + 30 * S23.card : ℕ) : ℝ)
  set A3 : ℝ := ((29 + 30 * S29.card : ℕ) : ℝ)
  have hA1 : 0 < A1 := by positivity
  have hA2 : 0 < A2 := by positivity
  have hA3 : 0 < A3 := by positivity
  have hlog_add : Real.log (A1 / 17) + Real.log (A2 / 23) + Real.log (A3 / 29) =
      Real.log ((A1 * A2 * A3) / (17 * 23 * 29)) := by
    rw [← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1
    ring
  have hsumA : A1 + A2 + A3 ≤ 3 * (23 + 10 * 999997 : ℝ) := by
    have hNat : (17 + 30 * S17.card) + (23 + 30 * S23.card) + (29 + 30 * S29.card) ≤
        3 * (23 + 10 * 999997) := by omega
    have hR : ((17 + 30 * S17.card : ℕ) : ℝ) + ((23 + 30 * S23.card : ℕ) : ℝ) +
        ((29 + 30 * S29.card : ℕ) : ℝ) ≤ ((3 * (23 + 10 * 999997) : ℕ) : ℝ) := by
      exact_mod_cast hNat
    have hcast : ((3 * (23 + 10 * 999997) : ℕ) : ℝ) = 3 * (23 + 10 * 999997 : ℝ) := by norm_num
    linarith
  have hprod_le : A1 * A2 * A3 ≤ (23 + 10 * 999997 : ℝ) ^ 3 := by
    have hamgm := mul3_le_cube hA1.le hA2.le hA3.le
    have hcube : (A1 + A2 + A3) ^ 3 ≤ (3 * (23 + 10 * 999997 : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hsumA 3
    have hre : (3 * (23 + 10 * 999997 : ℝ)) ^ 3 = 27 * (23 + 10 * 999997 : ℝ) ^ 3 := by ring
    linarith
  have hlog_lt : Real.log ((A1 * A2 * A3) / (17 * 23 * 29)) < 79 / 2 := by
    set X : ℝ := (23 + 10 * 999997 : ℝ) ^ 3 / (17 * 23 * 29)
    have hXpos : 0 < X := by positivity
    have harg_le : (A1 * A2 * A3) / (17 * 23 * 29) ≤ X :=
      div_le_div_of_nonneg_right hprod_le (by positivity)
    have h1 : Real.log ((A1 * A2 * A3) / (17 * 23 * 29)) ≤ Real.log X :=
      Real.log_le_log (by positivity) harg_le
    have h2log : 2 * Real.log X < 79 := by
      have hsq : Real.log (X ^ 2) = 2 * Real.log X := by simp [Real.log_pow]
      rw [← hsq, Real.log_lt_iff_lt_exp (pow_pos hXpos 2)]
      have hexp := exp_gt_pow_27_10 79 (by omega)
      have hnum : X ^ 2 ≤ (27 / 10 : ℝ) ^ 79 := by
        dsimp [X]
        norm_num
      have hcast79 : ((79 : ℕ) : ℝ) = (79 : ℝ) := by norm_num
      rw [hcast79] at hexp
      exact lt_of_le_of_lt hnum hexp
    have hXlt : Real.log X < 79 / 2 :=
      (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (mul_comm 2 (Real.log X) ▸ h2log)
    exact lt_of_le_of_lt h1 hXlt
  have hcomb : ∑ p ∈ S, (1 / (p : ℝ)) ≤
      (1 / (17 : ℝ) + 1 / (23 : ℝ) + 1 / (29 : ℝ)) +
        (1 / (30 : ℝ)) * (Real.log (A1 / 17) + Real.log (A2 / 23) + Real.log (A3 / 29)) := by
    rw [hsum_part]
    simp only [Nat.cast_ofNat] at hb17 hb23 hb29
    linarith only [hb17, hb23, hb29]
  rw [hlog_add] at hcomb
  linarith only [hS_gt, hcomb, hlog_lt]

lemma card_ge_100000_of_three_not_five {n k : ℕ} (hn0 : n ≠ 0) (hk2 : 2 ≤ k) (h3dvd : 3 ∣ n)
    (hres : ∀ p ∈ n.primeFactors, p = 3 ∨ p % 30 = 11 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    100000 ≤ n.primeFactors.card := by
  by_contra hlt
  have h3_mem : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3dvd, hn0⟩
  set S := n.primeFactors.erase 3
  have hS_card : S.card = n.primeFactors.card - 1 := Finset.card_erase_of_mem h3_mem
  have hS_le : S.card ≤ 99998 := by omega
  have hsum_split : ∑ p ∈ n.primeFactors, (1 / (p : ℝ)) =
      1 / (3 : ℝ) + ∑ p ∈ S, (1 / (p : ℝ)) := by
    have h1 := Finset.add_sum_erase n.primeFactors (fun p => (1 / (p : ℝ))) h3_mem
    simp only [Nat.cast_ofNat] at h1
    linarith
  have hsum_real := sum_real_gt_k hn0 hsum
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hS_gt : (5 / 3 : ℝ) < ∑ p ∈ S, (1 / (p : ℝ)) := by linarith
  set S11 := S.filter (fun p => p % 30 = 11)
  set S17 := S.filter (fun p => p % 30 = 17)
  set S23 := S.filter (fun p => p % 30 = 23)
  set S29 := S.filter (fun p => p % 30 = 29)
  have hS_res : ∀ p ∈ S, p % 30 = 11 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29 := by
    intro p hp
    rcases Finset.mem_erase.mp hp with ⟨hp3, hp_mem⟩
    exact (hres p hp_mem).resolve_left hp3
  have hdisj34 : Disjoint S23 S29 := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by omega)
  have hdisj2 : Disjoint S17 (S23 ∪ S29) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2
    rcases Finset.mem_union.mp hp2 with h2 | h3
    · have := (Finset.mem_filter.mp h2).2; omega
    · have := (Finset.mem_filter.mp h3).2; omega
  have hdisj1 : Disjoint S11 (S17 ∪ (S23 ∪ S29)) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2
    rcases Finset.mem_union.mp hp2 with h2 | h34
    · have := (Finset.mem_filter.mp h2).2; omega
    · rcases Finset.mem_union.mp h34 with h3 | h4
      · have := (Finset.mem_filter.mp h3).2; omega
      · have := (Finset.mem_filter.mp h4).2; omega
  have hunion : S11 ∪ (S17 ∪ (S23 ∪ S29)) = S := by
    ext p
    simp only [S11, S17, S23, S29, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    · intro hp
      rcases hS_res p hp with h11 | h17 | h23 | h29
      · exact Or.inl ⟨hp, h11⟩
      · exact Or.inr (Or.inl ⟨hp, h17⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hp, h23⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hp, h29⟩))
  have hcard_sum : S11.card + S17.card + S23.card + S29.card = S.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj2,
      Finset.card_union_of_disjoint hdisj34]
    omega
  have hsum_part : ∑ p ∈ S, (1 / (p : ℝ)) =
      ∑ p ∈ S11, (1 / (p : ℝ)) + ∑ p ∈ S17, (1 / (p : ℝ)) +
        ∑ p ∈ S23, (1 / (p : ℝ)) + ∑ p ∈ S29, (1 / (p : ℝ)) := by
    rw [← hunion, Finset.sum_union hdisj1, Finset.sum_union hdisj2, Finset.sum_union hdisj34]
    ring
  have hb11 := sum_inv_finset_ap_le_add S11 11 30 (by omega) (by omega) (fun p hp => by
    have h := (Finset.mem_filter.mp hp).2; exact ⟨by omega, by omega⟩)
  have hb17 := sum_inv_finset_ap_le_add S17 17 30 (by omega) (by omega) (fun p hp => by
    have h := (Finset.mem_filter.mp hp).2; exact ⟨by omega, by omega⟩)
  have hb23 := sum_inv_finset_ap_le_add S23 23 30 (by omega) (by omega) (fun p hp => by
    have h := (Finset.mem_filter.mp hp).2; exact ⟨by omega, by omega⟩)
  have hb29 := sum_inv_finset_ap_le_add S29 29 30 (by omega) (by omega) (fun p hp => by
    have h := (Finset.mem_filter.mp hp).2; exact ⟨by omega, by omega⟩)
  set A1 : ℝ := ((11 + 30 * S11.card : ℕ) : ℝ)
  set A2 : ℝ := ((17 + 30 * S17.card : ℕ) : ℝ)
  set A3 : ℝ := ((23 + 30 * S23.card : ℕ) : ℝ)
  set A4 : ℝ := ((29 + 30 * S29.card : ℕ) : ℝ)
  have hA1 : 0 < A1 := by positivity
  have hA2 : 0 < A2 := by positivity
  have hA3 : 0 < A3 := by positivity
  have hA4 : 0 < A4 := by positivity
  have hlog_add : Real.log (A1 / 11) + Real.log (A2 / 17) + Real.log (A3 / 23) + Real.log (A4 / 29) =
      Real.log ((A1 * A2 * A3 * A4) / (11 * 17 * 23 * 29)) := by
    rw [← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1
    ring
  have hsumA : A1 + A2 + A3 + A4 ≤ (80 + 30 * 99998 : ℝ) := by
    have hNat : (11 + 30 * S11.card) + (17 + 30 * S17.card) + (23 + 30 * S23.card) +
        (29 + 30 * S29.card) ≤ 80 + 30 * 99998 := by omega
    have hR : ((11 + 30 * S11.card : ℕ) : ℝ) + ((17 + 30 * S17.card : ℕ) : ℝ) +
        ((23 + 30 * S23.card : ℕ) : ℝ) + ((29 + 30 * S29.card : ℕ) : ℝ) ≤
        ((80 + 30 * 99998 : ℕ) : ℝ) := by exact_mod_cast hNat
    have hcast : ((80 + 30 * 99998 : ℕ) : ℝ) = (80 + 30 * 99998 : ℝ) := by norm_num
    linarith
  have hprod_le : 256 * (A1 * A2 * A3 * A4) ≤ (80 + 30 * 99998 : ℝ) ^ 4 := by
    have hamgm := mul4_le_pow_four hA1.le hA2.le hA3.le hA4.le
    have hpow := pow_le_pow_left₀ (by positivity) hsumA 4
    linarith
  have hlog_lt : Real.log ((A1 * A2 * A3 * A4) / (11 * 17 * 23 * 29)) < 43 := by
    rw [Real.log_lt_iff_lt_exp (by positivity)]
    have hexp := exp_gt_pow_27_10 43 (by omega)
    have harg : (A1 * A2 * A3 * A4) / (11 * 17 * 23 * 29) ≤
        (80 + 30 * 99998 : ℝ) ^ 4 / (256 * 11 * 17 * 23 * 29) := by
      have hdiv := div_le_div_of_nonneg_right hprod_le (by positivity : (0 : ℝ) ≤ 256 * 11 * 17 * 23 * 29)
      have hre : (256 * (A1 * A2 * A3 * A4)) / (256 * 11 * 17 * 23 * 29) =
          (A1 * A2 * A3 * A4) / (11 * 17 * 23 * 29) := by ring
      rwa [hre] at hdiv
    have hnum : (80 + 30 * 99998 : ℝ) ^ 4 / (256 * 11 * 17 * 23 * 29) ≤ (27 / 10 : ℝ) ^ 43 := by
      norm_num
    have hcast43 : ((43 : ℕ) : ℝ) = (43 : ℝ) := by norm_num
    rw [hcast43] at hexp
    exact lt_of_le_of_lt (harg.trans hnum) hexp
  have hcomb : ∑ p ∈ S, (1 / (p : ℝ)) ≤
      (1 / (11 : ℝ) + 1 / (17 : ℝ) + 1 / (23 : ℝ) + 1 / (29 : ℝ)) +
        (1 / (30 : ℝ)) *
          (Real.log (A1 / 11) + Real.log (A2 / 17) + Real.log (A3 / 23) + Real.log (A4 / 29)) := by
    rw [hsum_part]
    simp only [Nat.cast_ofNat] at hb11 hb17 hb23 hb29
    linarith
  rw [hlog_add] at hcomb
  linarith

lemma card_ge_10_pow_22_of_three_all_mod4_3 {n k : ℕ} (hn0 : n ≠ 0) (hk4 : 4 ≤ k) (h3dvd : 3 ∣ n)
    (hres : ∀ p ∈ n.primeFactors, p = 3 ∨ p % 60 = 11 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    10 ^ 22 ≤ n.primeFactors.card := by
  by_contra hlt
  have h3_mem : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3dvd, hn0⟩
  set S := n.primeFactors.erase 3
  have hS_card : S.card = n.primeFactors.card - 1 := Finset.card_erase_of_mem h3_mem
  have hS_le : S.card ≤ 10 ^ 22 - 2 := by omega
  have hsum_split : ∑ p ∈ n.primeFactors, (1 / (p : ℝ)) =
      1 / (3 : ℝ) + ∑ p ∈ S, (1 / (p : ℝ)) := by
    have h1 := Finset.add_sum_erase n.primeFactors (fun p => (1 / (p : ℝ))) h3_mem
    simp only [Nat.cast_ofNat] at h1
    linarith
  have hsum_real := sum_real_gt_k hn0 hsum
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4
  have hS_gt : (11 / 3 : ℝ) < ∑ p ∈ S, (1 / (p : ℝ)) := by linarith
  set S11 := S.filter (fun p => p % 60 = 11)
  set S23 := S.filter (fun p => p % 60 = 23)
  set S47 := S.filter (fun p => p % 60 = 47)
  set S59 := S.filter (fun p => p % 60 = 59)
  have hS_res : ∀ p ∈ S, p % 60 = 11 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59 := by
    intro p hp
    rcases Finset.mem_erase.mp hp with ⟨hp3, hp_mem⟩
    exact (hres p hp_mem).resolve_left hp3
  have hdisj34 : Disjoint S47 S59 := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by omega)
  have hdisj2 : Disjoint S23 (S47 ∪ S59) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2
    rcases Finset.mem_union.mp hp2 with h2 | h3
    · have := (Finset.mem_filter.mp h2).2; omega
    · have := (Finset.mem_filter.mp h3).2; omega
  have hdisj1 : Disjoint S11 (S23 ∪ (S47 ∪ S59)) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2
    rcases Finset.mem_union.mp hp2 with h2 | h34
    · have := (Finset.mem_filter.mp h2).2; omega
    · rcases Finset.mem_union.mp h34 with h3 | h4
      · have := (Finset.mem_filter.mp h3).2; omega
      · have := (Finset.mem_filter.mp h4).2; omega
  have hunion : S11 ∪ (S23 ∪ (S47 ∪ S59)) = S := by
    ext p
    simp only [S11, S23, S47, S59, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    · intro hp
      rcases hS_res p hp with h11 | h23 | h47 | h59
      · exact Or.inl ⟨hp, h11⟩
      · exact Or.inr (Or.inl ⟨hp, h23⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hp, h47⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hp, h59⟩))
  have hcard_sum : S11.card + S23.card + S47.card + S59.card = S.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj2,
      Finset.card_union_of_disjoint hdisj34]
    omega
  have hsum_part : ∑ p ∈ S, (1 / (p : ℝ)) =
      ∑ p ∈ S11, (1 / (p : ℝ)) + ∑ p ∈ S23, (1 / (p : ℝ)) +
        ∑ p ∈ S47, (1 / (p : ℝ)) + ∑ p ∈ S59, (1 / (p : ℝ)) := by
    rw [← hunion, Finset.sum_union hdisj1, Finset.sum_union hdisj2, Finset.sum_union hdisj34]
    ring
  have hb11 := sum_inv_finset_ap_le_add S11 11 60 (by omega) (by omega) (fun p hp => by
    have h := (Finset.mem_filter.mp hp).2; exact ⟨by omega, by omega⟩)
  have hb23 := sum_inv_finset_ap_le_add S23 23 60 (by omega) (by omega) (fun p hp => by
    have h := (Finset.mem_filter.mp hp).2; exact ⟨by omega, by omega⟩)
  have hb47 := sum_inv_finset_ap_le_add S47 47 60 (by omega) (by omega) (fun p hp => by
    have h := (Finset.mem_filter.mp hp).2; exact ⟨by omega, by omega⟩)
  have hb59 := sum_inv_finset_ap_le_add S59 59 60 (by omega) (by omega) (fun p hp => by
    have h := (Finset.mem_filter.mp hp).2; exact ⟨by omega, by omega⟩)
  set A1 : ℝ := ((11 + 60 * S11.card : ℕ) : ℝ)
  set A2 : ℝ := ((23 + 60 * S23.card : ℕ) : ℝ)
  set A3 : ℝ := ((47 + 60 * S47.card : ℕ) : ℝ)
  set A4 : ℝ := ((59 + 60 * S59.card : ℕ) : ℝ)
  have hA1 : 0 < A1 := by positivity
  have hA2 : 0 < A2 := by positivity
  have hA3 : 0 < A3 := by positivity
  have hA4 : 0 < A4 := by positivity
  have hlog_add : Real.log (A1 / 11) + Real.log (A2 / 23) + Real.log (A3 / 47) + Real.log (A4 / 59) =
      Real.log ((A1 * A2 * A3 * A4) / (11 * 23 * 47 * 59)) := by
    rw [← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1
    ring
  have hsumA : A1 + A2 + A3 + A4 ≤ (140 + 60 * (10 ^ 22 - 2) : ℝ) := by
    have hNat : (11 + 60 * S11.card) + (23 + 60 * S23.card) + (47 + 60 * S47.card) +
        (59 + 60 * S59.card) ≤ 140 + 60 * (10 ^ 22 - 2) := by omega
    have hR : ((11 + 60 * S11.card : ℕ) : ℝ) + ((23 + 60 * S23.card : ℕ) : ℝ) +
        ((47 + 60 * S47.card : ℕ) : ℝ) + ((59 + 60 * S59.card : ℕ) : ℝ) ≤
        ((140 + 60 * (10 ^ 22 - 2) : ℕ) : ℝ) := by exact_mod_cast hNat
    have hcast : ((140 + 60 * (10 ^ 22 - 2) : ℕ) : ℝ) = (140 + 60 * (10 ^ 22 - 2) : ℝ) := by
      norm_num
    exact hcast ▸ hR
  have hprod_le : 256 * (A1 * A2 * A3 * A4) ≤ (140 + 60 * (10 ^ 22 - 2) : ℝ) ^ 4 := by
    have hamgm := mul4_le_pow_four hA1.le hA2.le hA3.le hA4.le
    have hpow := pow_le_pow_left₀ (by positivity) hsumA 4
    exact hamgm.trans hpow
  have hlog_lt : Real.log ((A1 * A2 * A3 * A4) / (11 * 23 * 47 * 59)) < 208 := by
    rw [Real.log_lt_iff_lt_exp (by positivity)]
    have hexp := exp_gt_pow_27_10 208 (by omega)
    have hdenom : (104 : ℝ) ^ 4 ≤ 256 * (11 * 23 * 47 * 59 : ℝ) := by norm_num
    have hstep1 : (A1 * A2 * A3 * A4) / (11 * 23 * 47 * 59) ≤
        ((140 + 60 * (10 ^ 22 - 2) : ℝ) / 104) ^ 4 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : (A1 * A2 * A3 * A4) * (104 : ℝ) ^ 4 ≤
          (A1 * A2 * A3 * A4) * (256 * (11 * 23 * 47 * 59 : ℝ)) :=
        mul_le_mul_of_nonneg_left hdenom (by positivity)
      have h2 : (A1 * A2 * A3 * A4) * (256 * (11 * 23 * 47 * 59 : ℝ)) =
          (256 * (A1 * A2 * A3 * A4)) * (11 * 23 * 47 * 59 : ℝ) := by ring
      have h3 : (256 * (A1 * A2 * A3 * A4)) * (11 * 23 * 47 * 59 : ℝ) ≤
          (140 + 60 * (10 ^ 22 - 2) : ℝ) ^ 4 * (11 * 23 * 47 * 59 : ℝ) :=
        mul_le_mul_of_nonneg_right hprod_le (by positivity)
      exact h1.trans (h2.le.trans h3)
    have hbase52 : (140 + 60 * (10 ^ 22 - 2) : ℝ) / 104 ≤ (27 / 10 : ℝ) ^ 52 := by norm_num
    have hstep2 : ((140 + 60 * (10 ^ 22 - 2) : ℝ) / 104) ^ 4 ≤ (27 / 10 : ℝ) ^ 208 := by
      calc ((140 + 60 * (10 ^ 22 - 2) : ℝ) / 104) ^ 4
          ≤ ((27 / 10 : ℝ) ^ 52) ^ 4 := pow_le_pow_left₀ (by positivity) hbase52 4
        _ = (27 / 10 : ℝ) ^ 208 := by ring
    have hcast208 : ((208 : ℕ) : ℝ) = (208 : ℝ) := by norm_num
    rw [hcast208] at hexp
    exact lt_of_le_of_lt (hstep1.trans hstep2) hexp
  have hcomb : ∑ p ∈ S, (1 / (p : ℝ)) ≤
      (1 / (11 : ℝ) + 1 / (23 : ℝ) + 1 / (47 : ℝ) + 1 / (59 : ℝ)) +
        (1 / (60 : ℝ)) *
          (Real.log (A1 / 11) + Real.log (A2 / 23) + Real.log (A3 / 47) + Real.log (A4 / 59)) := by
    rw [hsum_part]
    simp only [Nat.cast_ofNat] at hb11 hb23 hb47 hb59
    linarith only [hb11, hb23, hb47, hb59]
  rw [hlog_add] at hcomb
  linarith only [hS_gt, hcomb, hlog_lt]

/- ### Section 5: Residue helpers and main reduction theorem -/

lemma mod30_of_three_five {p : ℕ} (h2 : p % 2 = 1) (h3 : p % 3 = 2)
    (h50 : p % 5 ≠ 0) (h51 : p % 5 ≠ 1) :
    p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29 := by
  have h5 : p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
  rcases h5 with h5 | h5 | h5
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

lemma mod30_of_three_not_five {p : ℕ} (h2 : p % 2 = 1) (h3 : p % 3 = 2) (h50 : p % 5 ≠ 0) :
    p % 30 = 11 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29 := by
  omega

lemma mod60_of_three_all_mod4_3 {p : ℕ} (h4 : p % 4 = 3) (h3 : p % 3 = 2) (h50 : p % 5 ≠ 0) :
    p % 60 = 11 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59 := by
  omega

theorem main : H1 → H2 → H3 → OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2.H1 := by
  intro h1 h2 h3 n hcomp hsqf hodd h3dvd hodd_card _hcard37 hmod3 hdvd hnorm ⟨k, hk1, hsum⟩
  have hn0 : n ≠ 0 := hsqf.ne_zero
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  have h3_mem : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3dvd, hn0⟩
  have hodd_pf : ∀ p ∈ n.primeFactors, Odd p := by
    intro p hp
    have hmul : n / p * p = n := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
    have : (n / p * p) % 2 = 1 := hmul.symm ▸ hn2
    rcases Nat.mod_two_eq_zero_or_one p with h0 | h1
    · rw [Nat.mul_mod, h0, mul_zero, Nat.zero_mod] at this
      omega
    · exact Nat.odd_iff.mpr h1
  have hint : ∑ p ∈ n.primeFactors, n / p = k * n + 1 := sum_div_eq_mul_add_one hn0 hsum
  obtain ⟨hk_even, hk2⟩ := even_k_of_odd_card hodd hodd_card hk1 hint
  obtain ⟨_, hn18⟩ := mod_18_of_three_dvd hn0 h3dvd hdvd
  have hn27 : n % 27 = (9 * (k + n.primeFactors.card - 1) + 3) % 27 :=
    mod_27_of_three_dvd hn0 h3dvd hn18 hmod3 hint
  have hqr := qr_r3_mod_four hsqf hodd hdvd
  have hmod8 : n.primeFactors.card % 8 = (k + 1) % 8 :=
    omega_mod_eight_eq_k_add_one hsqf hodd hdvd hint
  have hprod_n : ∏ p ∈ n.primeFactors, p = n := prod_primeFactors_of_sqf hsqf hn0
  have hn_mod4 : n % 4 =
      if (n.primeFactors.filter (fun p => p % 4 = 3)).card % 2 = 0 then 1 else 3 := by
    conv_lhs => rw [← hprod_n]
    exact prod_mod_four_of_odd n.primeFactors hodd_pf
  have hr3_pos : 1 ≤ (n.primeFactors.filter (fun p => p % 4 = 3)).card :=
    Finset.one_le_card.mpr ⟨3, Finset.mem_filter.mpr ⟨h3_mem, by norm_num⟩⟩
  by_cases h5dvd : 5 ∣ n
  · have h5_mem : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, h5dvd, hn0⟩
    have hn900 : n % 900 = 705 := mod_900_of_three_five_dvd hn0 hn18 h5dvd hdvd
    have hn4 : n % 4 = 1 := by omega
    have hr3_even : (n.primeFactors.filter (fun p => p % 4 = 3)).card % 2 = 0 := by
      by_contra hne
      rw [if_neg hne] at hn_mod4
      omega
    have hr3_dvd4 : 4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card := by
      rcases hqr with h0 | h1
      · exact Nat.dvd_of_mod_eq_zero h0
      · omega
    have hr3_ge4 : 4 ≤ (n.primeFactors.filter (fun p => p % 4 = 3)).card := by
      have h0 : (n.primeFactors.filter (fun p => p % 4 = 3)).card % 4 = 0 :=
        Nat.mod_eq_zero_of_dvd hr3_dvd4
      omega
    have hsum4_terms : ∀ p ∈ n.primeFactors,
        (p % 4 = 1 → (n / p) % 4 = 1) ∧ (p % 4 = 3 → (n / p) % 4 = 3) := by
      intro p hp
      have hmul : n / p * p = n := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
      have hprod4 : (n / p * p) % 4 = 1 := hmul.symm ▸ hn4
      rw [Nat.mul_mod] at hprod4
      constructor
      · intro hp1; rw [hp1] at hprod4; omega
      · intro hp3; rw [hp3] at hprod4; omega
    have hsum4 := sum_mod_four_split n.primeFactors (fun p => n / p) hsum4_terms hodd_pf
    rw [hint] at hsum4
    have hrhs4 : (k * n + 1) % 4 = (k + 1) % 4 := by
      rw [Nat.add_mod, Nat.mul_mod, hn4]
      omega
    have hr3_0 : (n.primeFactors.filter (fun p => p % 4 = 3)).card % 4 = 0 :=
      Nat.mod_eq_zero_of_dvd hr3_dvd4
    have hr1_mod4 : (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = (k + 1) % 4 := by
      rw [hrhs4] at hsum4
      omega
    have hres30 : ∀ p ∈ n.primeFactors,
        p = 3 ∨ p = 5 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29 := by
      intro p hp
      by_cases hp3 : p = 3
      · exact Or.inl hp3
      · by_cases hp5 : p = 5
        · exact Or.inr (Or.inl hp5)
        · have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
          have hp2 : p % 2 = 1 := Nat.odd_iff.mp (hodd_pf p hp)
          have hp_mod3 : p % 3 = 2 := (hmod3 p hp).resolve_left hp3
          have hp_not_dvd5 : ¬ (5 ∣ p) := by
            intro h5p
            exact hp5 (((Nat.prime_dvd_prime_iff_eq (by norm_num) hp_prime).mp h5p).symm)
          have hp_mod5_ne0 : p % 5 ≠ 0 := fun h0 => hp_not_dvd5 (Nat.dvd_of_mod_eq_zero h0)
          have hp_not_5_sub : ¬ (5 ∣ p - 1) := hnorm 5 h5_mem p hp
          have hp_pos : 1 ≤ p := hp_prime.one_le
          have hp_mod5_ne1 : p % 5 ≠ 1 := fun h1 =>
            hp_not_5_sub (Nat.dvd_of_mod_eq_zero (by omega))
          exact Or.inr (Or.inr (mod30_of_three_five hp2 hp_mod3 hp_mod5_ne0 hp_mod5_ne1))
    have hcard1m := card_ge_1000000_of_three_five hn0 hk2 h3dvd h5dvd hres30 hsum
    exact h1 n hcomp hsqf hodd h3dvd h5dvd hn900 hcard1m hr3_dvd4 hr3_ge4 hres30 hdvd hnorm
      ⟨k, hk2, hk_even, hmod8, hr1_mod4, hn27, hsum⟩
  · by_cases hex1 : ∃ p ∈ n.primeFactors, p % 4 = 1
    · obtain ⟨p0, hp0, hp0_mod4⟩ := hex1
      have hp0_pred : 4 ∣ (p0 - 1) := by omega
      have hdiv_sub : 4 ∣ (n / p0 - 1) :=
        dvd_trans hp0_pred (dvd_trans (dvd_mul_left (p0 - 1) p0) (hdvd p0 hp0))
      have hdiv_pos : 1 ≤ n / p0 :=
        Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_primeFactors hp0))
          (Nat.prime_of_mem_primeFactors hp0).pos
      have hdiv_mod4 : (n / p0) % 4 = 1 := by
        obtain ⟨c, hc⟩ := hdiv_sub
        omega
      have hn4 : n % 4 = 1 := by
        have hmul : n / p0 * p0 = n := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp0)
        rw [← hmul, Nat.mul_mod, hdiv_mod4, hp0_mod4]
      have hn36 : n % 36 = 21 := by omega
      have hr3_even : (n.primeFactors.filter (fun p => p % 4 = 3)).card % 2 = 0 := by
        by_contra hne
        rw [if_neg hne] at hn_mod4
        omega
      have hr3_dvd4 : 4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card := by
        rcases hqr with h0 | h1
        · exact Nat.dvd_of_mod_eq_zero h0
        · omega
      have hr3_ge4 : 4 ≤ (n.primeFactors.filter (fun p => p % 4 = 3)).card := by
        have h0 : (n.primeFactors.filter (fun p => p % 4 = 3)).card % 4 = 0 :=
          Nat.mod_eq_zero_of_dvd hr3_dvd4
        omega
      have hsum4_terms : ∀ p ∈ n.primeFactors,
          (p % 4 = 1 → (n / p) % 4 = 1) ∧ (p % 4 = 3 → (n / p) % 4 = 3) := by
        intro p hp
        have hmul : n / p * p = n := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
        have hprod4 : (n / p * p) % 4 = 1 := hmul.symm ▸ hn4
        rw [Nat.mul_mod] at hprod4
        constructor
        · intro hp1; rw [hp1] at hprod4; omega
        · intro hp3; rw [hp3] at hprod4; omega
      have hsum4 := sum_mod_four_split n.primeFactors (fun p => n / p) hsum4_terms hodd_pf
      rw [hint] at hsum4
      have hrhs4 : (k * n + 1) % 4 = (k + 1) % 4 := by
        rw [Nat.add_mod, Nat.mul_mod, hn4]
        omega
      have hr3_0 : (n.primeFactors.filter (fun p => p % 4 = 3)).card % 4 = 0 :=
        Nat.mod_eq_zero_of_dvd hr3_dvd4
      have hr1_mod4 : (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = (k + 1) % 4 := by
        rw [hrhs4] at hsum4
        omega
      have hres30 : ∀ p ∈ n.primeFactors,
          p = 3 ∨ p % 30 = 11 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29 := by
        intro p hp
        by_cases hp3 : p = 3
        · exact Or.inl hp3
        · have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
          have hp2 : p % 2 = 1 := Nat.odd_iff.mp (hodd_pf p hp)
          have hp_mod3 : p % 3 = 2 := (hmod3 p hp).resolve_left hp3
          have hp_ne5 : p ≠ 5 := fun h => h5dvd (h ▸ Nat.dvd_of_mem_primeFactors hp)
          have hp_not_dvd5 : ¬ (5 ∣ p) := by
            intro h5p
            exact hp_ne5 (((Nat.prime_dvd_prime_iff_eq (by norm_num) hp_prime).mp h5p).symm)
          have hp_mod5_ne0 : p % 5 ≠ 0 := fun h0 => hp_not_dvd5 (Nat.dvd_of_mod_eq_zero h0)
          exact Or.inr (mod30_of_three_not_five hp2 hp_mod3 hp_mod5_ne0)
      have hcard100k := card_ge_100000_of_three_not_five hn0 hk2 h3dvd hres30 hsum
      exact h2 n hcomp hsqf hodd h3dvd h5dvd hn36 hcard100k ⟨p0, hp0, hp0_mod4⟩
        hr3_dvd4 hr3_ge4 hres30 hdvd hnorm ⟨k, hk2, hk_even, hmod8, hr1_mod4, hn27, hsum⟩
    · have hall3 : ∀ p ∈ n.primeFactors, p % 4 = 3 := by
        intro p hp
        have hp2 : p % 2 = 1 := Nat.odd_iff.mp (hodd_pf p hp)
        have hp1 : p % 4 ≠ 1 := fun h => hex1 ⟨p, hp, h⟩
        omega
      have hfilt_eq : n.primeFactors.filter (fun p => p % 4 = 3) = n.primeFactors :=
        Finset.filter_true_of_mem hall3
      rw [hfilt_eq] at hqr hn_mod4
      have hcard_odd : n.primeFactors.card % 2 = 1 := Nat.odd_iff.mp hodd_card
      have hcard_mod4 : n.primeFactors.card % 4 = 1 := by
        rcases hqr with h0 | h1
        · omega
        · exact h1
      have hn4 : n % 4 = 3 := by
        have hne : ¬ (n.primeFactors.card % 2 = 0) := by omega
        rw [if_neg hne] at hn_mod4
        exact hn_mod4
      have hn36 : n % 36 = 3 := by omega
      have hk_dvd4 : 4 ∣ k := Nat.dvd_of_mod_eq_zero (by omega)
      have hk4 : 4 ≤ k := by
        have : k % 4 = 0 := Nat.mod_eq_zero_of_dvd hk_dvd4
        omega
      have hres60 : ∀ p ∈ n.primeFactors,
          p = 3 ∨ p % 60 = 11 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59 := by
        intro p hp
        by_cases hp3 : p = 3
        · exact Or.inl hp3
        · have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
          have hp4 : p % 4 = 3 := hall3 p hp
          have hp_mod3 : p % 3 = 2 := (hmod3 p hp).resolve_left hp3
          have hp_ne5 : p ≠ 5 := fun h => h5dvd (h ▸ Nat.dvd_of_mem_primeFactors hp)
          have hp_not_dvd5 : ¬ (5 ∣ p) := by
            intro h5p
            exact hp_ne5 (((Nat.prime_dvd_prime_iff_eq (by norm_num) hp_prime).mp h5p).symm)
          have hp_mod5_ne0 : p % 5 ≠ 0 := fun h0 => hp_not_dvd5 (Nat.dvd_of_mod_eq_zero h0)
          exact Or.inr (mod60_of_three_all_mod4_3 hp4 hp_mod3 hp_mod5_ne0)
      have hcard22 := card_ge_10_pow_22_of_three_all_mod4_3 hn0 hk4 h3dvd hres60 hsum
      exact h3 n hcomp hsqf hodd h3dvd h5dvd hn36 hcard_mod4 hcard22 hres60 hdvd hnorm
        ⟨k, hk4, hk_dvd4, hmod8, hn27, hsum⟩

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H1_R1
