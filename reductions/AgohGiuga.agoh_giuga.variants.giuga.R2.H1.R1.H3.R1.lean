import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H1_R1

-- Reduction AgohGiuga.agoh_giuga.variants.giuga.R2.H1.R1.H3.R1 of step AgohGiuga.agoh_giuga.variants.giuga.R2.H1.R1.H3
-- Credit: @subham-n, @Alewawa
-- uses note #86629
-- uses note #88332
-- uses note #88948

/-!
# Reduction of Agoh-Giuga step R2.H1.R1.H3

Reduction `AgohGiuga.agoh_giuga.variants.giuga.R2.H1.R1.H3.R1`:
combines exact mod-5/mod-180 structure, cofactor balance/size/LCM/discriminant obstructions,
and self-contained Selberg Lambda-squared sieve bounds across k = 4 (with/without p ≡ 11 mod 60),
k = 8, and 12 ≤ k.
-/

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H1_R1_H3_R1

open scoped BigOperators

/- ## Section 1: Exact mod-5, mod-180, and prime-count congruences -/

private lemma prod_pf_of_sqf {n : ℕ} (hn : Squarefree n) (hn0 : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p = n := by
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
  rw [Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hle : n.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hn0).mp hn p
  have hpos : 0 < n.factorization p := Nat.Prime.factorization_pos_of_dvd
    (Nat.prime_of_mem_primeFactors hp) hn0 (Nat.dvd_of_mem_primeFactors hp)
  have heq : n.factorization p = 1 := by omega
  simp [heq]

private lemma sum_div_eq_mul_add_one_loc {n k : ℕ} (hn0 : n ≠ 0)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    ∑ p ∈ n.primeFactors, n / p = k * n + 1 := by
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hmul : ∑ p ∈ n.primeFactors, ((n / p : ℕ) : ℚ) = (k * n + 1 : ℕ) := by
    have h1 : (n : ℚ) * (∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ)) = (n : ℚ) * (k : ℚ) := by
      rw [hsum]
    rw [mul_sub, Finset.mul_sum, mul_one_div_cancel hnQ] at h1
    have h2 : ∑ p ∈ n.primeFactors, (n : ℚ) * (1 / (p : ℚ)) =
        ∑ p ∈ n.primeFactors, ((n / p : ℕ) : ℚ) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
      rw [mul_one_div, Nat.cast_div hdvd hp0]
    rw [h2] at h1
    push_cast
    linarith
  exact_mod_cast hmul

private lemma sum_real_gt_k_loc {n k : ℕ} (hn0 : n ≠ 0)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    (k : ℝ) < ∑ p ∈ n.primeFactors, (1 / (p : ℝ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hq : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) = (k : ℚ) + 1 / (n : ℚ) := by linarith
  have hr : ∑ p ∈ n.primeFactors, (1 / (p : ℝ)) = (k : ℝ) + 1 / (n : ℝ) := by
    have := congrArg (Rat.cast (K := ℝ)) hq
    simpa [Rat.cast_sum] using this
  rw [hr]
  linarith [one_div_pos.mpr hnpos]

private lemma mod_180_of_p60_eq_11 {n p : ℕ} (hn0 : n ≠ 0) (hn36 : n % 36 = 3)
    (hp : p ∈ n.primeFactors) (hp11 : p % 60 = 11)
    (hdvd : p * (p - 1) ∣ (n / p - 1)) :
    n % 5 = 1 ∧ n % 180 = 111 := by
  have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have h5_pred : 5 ∣ p - 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have h5_np : 5 ∣ n / p - 1 := h5_pred.trans ((dvd_mul_left (p - 1) p).trans hdvd)
  have hnp_pos : 1 ≤ n / p :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hp_dvd)
      (Nat.prime_of_mem_primeFactors hp).pos
  have hnp5 : (n / p) % 5 = 1 := by
    obtain ⟨c, hc⟩ := h5_np
    omega
  have hn5 : n % 5 = 1 := by
    rw [← Nat.div_mul_cancel hp_dvd, Nat.mul_mod, hnp5, show p % 5 = 1 by omega]
  exact ⟨hn5, by omega⟩

private lemma mod5_sum_count_of_exists_11 {n k : ℕ} (hn0 : n ≠ 0) (h3 : 3 ∣ n)
    (hn5 : n % 5 = 1)
    (hprimes : ∀ p ∈ n.primeFactors, p = 3 ∨ p % 60 = 11 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59)
    (hint : ∑ p ∈ n.primeFactors, n / p = k * n + 1) :
    ((n.primeFactors.filter (fun p => p % 60 = 11)).card +
      2 * (n.primeFactors.filter (fun p => p % 60 = 23)).card +
      3 * (n.primeFactors.filter (fun p => p % 60 = 47)).card +
      4 * (n.primeFactors.filter (fun p => p % 60 = 59)).card + 1) % 5 = k % 5 := by
  have h3mem : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, h3, hn0⟩
  let S := n.primeFactors.erase 3
  let S11 := n.primeFactors.filter (fun p => p % 60 = 11)
  let S23 := n.primeFactors.filter (fun p => p % 60 = 23)
  let S47 := n.primeFactors.filter (fun p => p % 60 = 47)
  let S59 := n.primeFactors.filter (fun p => p % 60 = 59)
  have hS_part : S = S11 ∪ (S23 ∪ (S47 ∪ S59)) := by
    ext p
    simp only [S, S11, S23, S47, S59, Finset.mem_erase, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hp3, hpm⟩
      rcases hprimes p hpm with rfl | h11 | h23 | h47 | h59
      · exact absurd rfl hp3
      · exact Or.inl ⟨hpm, h11⟩
      · exact Or.inr (Or.inl ⟨hpm, h23⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hpm, h47⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hpm, h59⟩))
    · rintro (⟨hpm, h11⟩ | ⟨hpm, h23⟩ | ⟨hpm, h47⟩ | ⟨hpm, h59⟩) <;>
        exact ⟨by omega, hpm⟩
  have hdisj34 : Disjoint S47 S59 := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
  have hdisj2 : Disjoint S23 (S47 ∪ S59) := Finset.disjoint_left.mpr fun p h1 h2 => by
    have ha := (Finset.mem_filter.mp h1).2
    rcases Finset.mem_union.mp h2 with hb | hc
    · have := (Finset.mem_filter.mp hb).2; omega
    · have := (Finset.mem_filter.mp hc).2; omega
  have hdisj1 : Disjoint S11 (S23 ∪ (S47 ∪ S59)) := Finset.disjoint_left.mpr fun p h1 h2 => by
    have ha := (Finset.mem_filter.mp h1).2
    rcases Finset.mem_union.mp h2 with hb | hcd
    · have := (Finset.mem_filter.mp hb).2; omega
    · rcases Finset.mem_union.mp hcd with hc | hd
      · have := (Finset.mem_filter.mp hc).2; omega
      · have := (Finset.mem_filter.mp hd).2; omega
  have hterm_mod5 : ∀ (s : Finset ℕ) (c : ℕ), (∀ p ∈ s, (n / p) % 5 = c % 5) →
      (∑ p ∈ s, n / p) % 5 = (c * s.card) % 5 := by
    intro s c hc
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.card_cons]
      have ha' := hc a (Finset.mem_cons_self a s)
      have ih' := ih fun x hx => hc x (Finset.mem_cons_of_mem hx)
      rw [Nat.add_mod, ha', ih', mul_add, mul_one, Nat.add_mod (c * s.card) c 5,
        Nat.add_comm ((c * s.card) % 5) (c % 5)]
  have hnp5 : ∀ p ∈ n.primeFactors, ∀ r, p % 5 = r →
      (n / p * p) % 5 = 1 := fun p hp _ _ => by
    rw [Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp), hn5]
  have h3_mod : (n / 3) % 5 = 2 := by
    have h1 := hnp5 3 h3mem 3 rfl
    rw [Nat.mul_mod] at h1
    omega
  have h11_mod : ∀ p ∈ S11, (n / p) % 5 = 1 := fun p hp => by
    have h1 := hnp5 p (Finset.mem_filter.mp hp).1 1 (by have := (Finset.mem_filter.mp hp).2; omega)
    have h2 : p % 5 = 1 := by have := (Finset.mem_filter.mp hp).2; omega
    rw [Nat.mul_mod, h2] at h1; omega
  have h23_mod : ∀ p ∈ S23, (n / p) % 5 = 2 := fun p hp => by
    have h1 := hnp5 p (Finset.mem_filter.mp hp).1 3 (by have := (Finset.mem_filter.mp hp).2; omega)
    have h2 : p % 5 = 3 := by have := (Finset.mem_filter.mp hp).2; omega
    rw [Nat.mul_mod, h2] at h1; omega
  have h47_mod : ∀ p ∈ S47, (n / p) % 5 = 3 := fun p hp => by
    have h1 := hnp5 p (Finset.mem_filter.mp hp).1 2 (by have := (Finset.mem_filter.mp hp).2; omega)
    have h2 : p % 5 = 2 := by have := (Finset.mem_filter.mp hp).2; omega
    rw [Nat.mul_mod, h2] at h1; omega
  have h59_mod : ∀ p ∈ S59, (n / p) % 5 = 4 := fun p hp => by
    have h1 := hnp5 p (Finset.mem_filter.mp hp).1 4 (by have := (Finset.mem_filter.mp hp).2; omega)
    have h2 : p % 5 = 4 := by have := (Finset.mem_filter.mp hp).2; omega
    rw [Nat.mul_mod, h2] at h1; omega
  have hs11 : (∑ p ∈ S11, n / p) % 5 = S11.card % 5 := by
    simpa [one_mul] using hterm_mod5 S11 1 h11_mod
  have hs23 := hterm_mod5 S23 2 h23_mod
  have hs47 := hterm_mod5 S47 3 h47_mod
  have hs59 := hterm_mod5 S59 4 h59_mod
  have hsum_split : ∑ p ∈ n.primeFactors, n / p =
      n / 3 + (∑ p ∈ S11, n / p + (∑ p ∈ S23, n / p + (∑ p ∈ S47, n / p + ∑ p ∈ S59, n / p))) := by
    rw [← Finset.add_sum_erase n.primeFactors (fun p => n / p) h3mem]
    change n / 3 + ∑ p ∈ S, n / p = _
    rw [hS_part, Finset.sum_union hdisj1, Finset.sum_union hdisj2, Finset.sum_union hdisj34]
  have hmod5_eq : (∑ p ∈ n.primeFactors, n / p) % 5 = (k * n + 1) % 5 := congrArg (· % 5) hint
  rw [hsum_split] at hmod5_eq
  rw [Nat.add_mod, h3_mod,
    Nat.add_mod (∑ p ∈ S11, n / p) _ 5, hs11,
    Nat.add_mod (∑ p ∈ S23, n / p) _ 5, hs23,
    Nat.add_mod (∑ p ∈ S47, n / p) _ 5, hs47, hs59] at hmod5_eq
  have hrhs5 : (k * n + 1) % 5 = (k + 1) % 5 := by
    rw [Nat.add_mod, Nat.mul_mod, hn5, mul_one]; simp
  rw [hrhs5] at hmod5_eq
  have hcomb : (S11.card + 2 * S23.card + 3 * S47.card + 4 * S59.card + 1) % 5 =
      ((2 + (S11.card % 5 + (2 * S23.card % 5 + (3 * S47.card % 5 + 4 * S59.card % 5) % 5) % 5) % 5) % 5 + 4) % 5 := by
    omega
  rw [hcomb, hmod5_eq]
  omega

/- ## Section 2: Cofactor balance, LCM reciprocal bound, and quadratic discriminant obstruction -/

private lemma three_lt_pf_bound {n : ℕ} (hn0 : n ≠ 0) (hsqf : Squarefree n) (h3 : 3 ∣ n)
    (hprimes : ∀ p ∈ n.primeFactors, p = 3 ∨ p % 60 = 11 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59) :
    10 ^ (n.primeFactors.card - 1) < n := by
  have h3mem : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, h3, hn0⟩
  let S := n.primeFactors.erase 3
  have hprod : ∏ p ∈ n.primeFactors, p = n := prod_pf_of_sqf hsqf hn0
  have hsplit : n = 3 * ∏ p ∈ S, p := by
    rw [← hprod, ← Finset.mul_prod_erase n.primeFactors (fun p => p) h3mem]
  have hS_ge11 : ∀ p ∈ S, 11 ≤ p := fun p hp => by
    rcases Finset.mem_erase.mp hp with ⟨hp3, hpm⟩
    rcases hprimes p hpm with rfl | h11 | h23 | h47 | h59 <;> first | exact absurd rfl hp3 | omega
  have hprod_ge : 10 ^ S.card ≤ ∏ p ∈ S, p := by
    calc 10 ^ S.card = ∏ _p ∈ S, 10 := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod' fun p hp => by have := hS_ge11 p hp; omega
  have hScard : S.card = n.primeFactors.card - 1 := Finset.card_erase_of_mem h3mem
  rw [hScard] at hprod_ge
  have hpos : 0 < 10 ^ (n.primeFactors.card - 1) := by positivity
  omega

-- From @Alewawa, note #88332
private lemma twice_halfKorseltLcm_dvd {s : Finset ℕ} {n : ℕ} (h3 : 3 ∈ s)
    (hodd : ∀ r ∈ s, Odd r) (hk : ∀ r ∈ s, r - 1 ∣ n - 1) :
    2 * (s.lcm fun r => (r - 1) / 2) ∣ n - 1 := by
  obtain ⟨w, hw⟩ := hk 3 h3
  change n - 1 = 2 * w at hw
  rw [hw]
  apply Nat.mul_dvd_mul_left
  refine Finset.lcm_dvd ?_
  intro r hr
  obtain ⟨x, hx⟩ := hk r hr
  obtain ⟨_, _⟩ := hodd r hr
  have hh : r - 1 = 2 * ((r - 1) / 2) := by omega
  rw [hh, mul_assoc] at hx
  exact ⟨x, Nat.eq_of_mul_eq_mul_left (by decide) (hw.symm.trans hx)⟩

-- From @Alewawa, note #88948
private lemma cofactor_discriminant_square {m a p q L : ℤ}
    (h : a * (p * q) + 1 = m * (p + q)) (hK : L ∣ m * (p * q) - 1) :
    L ∣ (m ^ 2 * (q - p)) ^ 2 - ((a + m) ^ 2 - 4 * m ^ 3) := by
  obtain ⟨u, hu⟩ := hK
  have hsum : m ^ 2 * (p + q) = a + m + a * (L * u) := by
    linear_combination -m * h + a * hu
  have hv : m ^ 4 * (p * q) = m ^ 3 * (1 + L * u) := by
    linear_combination m ^ 3 * hu
  refine ⟨u * (a ^ 2 * (L * u) + 2 * a * (a + m) - 4 * m ^ 3), ?_⟩
  calc
    _ = (m ^ 2 * (p + q)) ^ 2 - 4 * (m ^ 4 * (p * q)) -
        ((a + m) ^ 2 - 4 * m ^ 3) := by ring
    _ = _ := by rw [hsum, hv]; ring

private lemma not_prime_dvd_finset_lcm {q : ℕ} (hq : q.Prime) (s : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ r ∈ s, ¬ (q ∣ f r)) : ¬ (q ∣ s.lcm f) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa using hq.not_dvd_one
  | @insert a s has ih =>
    rw [Finset.lcm_insert]
    intro hdvd
    have hmul : q ∣ f a * s.lcm f := hdvd.trans (Nat.lcm_dvd_mul (f a) (s.lcm f))
    rcases hq.dvd_mul.mp hmul with ha | hs
    · exact hf a (Finset.mem_insert_self a s) ha
    · exact ih (fun r hr => hf r (Finset.mem_insert_of_mem hr)) hs

private lemma geom_alt_pos (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (e : ℕ) :
    0 < ∑ i ∈ Finset.range (e + 1), ((-1 : ℚ) ^ i / (ℓ : ℚ) ^ i) := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    match e with
    | 0 => simp
    | 1 =>
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      have hℓR : (2 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ
      have hpos : (0 : ℚ) < (ℓ : ℚ) := by linarith
      have hinv : (1 : ℚ) / (ℓ : ℚ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hℓR
      have hterm : (-1 : ℚ) ^ 1 / (ℓ : ℚ) ^ 1 = -(1 / (ℓ : ℚ)) := by ring
      simp only [pow_zero, div_one, hterm]
      linarith
    | e' + 2 =>
      have hsplit : ∑ i ∈ Finset.range (e' + 2 + 1), ((-1 : ℚ) ^ i / (ℓ : ℚ) ^ i) =
          (1 - 1 / (ℓ : ℚ)) + (1 / (ℓ : ℚ) ^ 2) * ∑ j ∈ Finset.range (e' + 1), ((-1 : ℚ) ^ j / (ℓ : ℚ) ^ j) := by
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
        have hstep : ∑ x ∈ Finset.range (e' + 1), ((-1 : ℚ) ^ (x + 1 + 1) / (ℓ : ℚ) ^ (x + 1 + 1)) =
            (1 / (ℓ : ℚ) ^ 2) * ∑ j ∈ Finset.range (e' + 1), ((-1 : ℚ) ^ j / (ℓ : ℚ) ^ j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          have hℓ0 : (ℓ : ℚ) ≠ 0 := by positivity
          rw [pow_add, pow_add, pow_add, pow_add]
          field_simp [hℓ0]
        rw [hstep]
        simp only [pow_zero, div_one]
        ring
      rw [hsplit]
      have hℓR : (2 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ
      have h1 : 0 < 1 - 1 / (ℓ : ℚ) := by
        have hinv : (1 : ℚ) / (ℓ : ℚ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hℓR
        linarith
      have h2 : 0 < (1 / (ℓ : ℚ) ^ 2) := by positivity
      have h3 := ih e' (by omega)
      nlinarith

private lemma sum_div_chi3_pos (x : ℕ) (hx0 : x ≠ 0) (hx3 : ¬ (3 ∣ x)) :
    0 < ∑ d ∈ x.divisors, (if d % 3 = 1 then (1 : ℚ) else if d % 3 = 2 then -1 else 0) / (d : ℚ) := by
  let chi3 : ℕ → ℚ := fun d => if d % 3 = 1 then 1 else if d % 3 = 2 then -1 else 0
  have hchi_mul : ∀ a b : ℕ, chi3 (a * b) = chi3 a * chi3 b := by
    intro a b
    dsimp only [chi3]
    have ha : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
      simp [Nat.mul_mod, ha, hb]
  change 0 < ∑ d ∈ x.divisors, chi3 d / (d : ℚ)
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases hx1 : x = 1
    · subst hx1; norm_num [chi3]
    · have hxgt : 1 < x := by omega
      let ℓ := x.minFac
      have hℓ_pr : ℓ.Prime := Nat.minFac_prime hx1
      have hℓ_dvd : ℓ ∣ x := Nat.minFac_dvd x
      have hℓ_ne3 : ℓ ≠ 3 := fun h => hx3 (h ▸ hℓ_dvd)
      let e := x.factorization ℓ
      have he_pos : 1 ≤ e := hℓ_pr.factorization_pos_of_dvd hx0 hℓ_dvd
      have hpow_dvd : ℓ ^ e ∣ x := Nat.ordProj_dvd x ℓ
      let y := x / ℓ ^ e
      have hy0 : y ≠ 0 := by
        have hle : ℓ ^ e ≤ x := Nat.le_of_dvd (Nat.pos_of_ne_zero hx0) hpow_dvd
        have hpos : 0 < ℓ ^ e := pow_pos hℓ_pr.pos e
        exact (Nat.div_pos hle hpos).ne'
      have hy3 : ¬ (3 ∣ y) := fun h3y => hx3 (h3y.trans (Nat.div_dvd_of_dvd hpow_dvd))
      have hylt : y < x := by
        have h1lt : 1 < ℓ ^ e := one_lt_pow₀ hℓ_pr.one_lt (by omega)
        exact Nat.div_lt_self (Nat.pos_of_ne_zero hx0) h1lt
      have hy_ndvd : ¬ (ℓ ∣ y) := by
        intro hdiv
        have hpow1 : ℓ ^ (e + 1) ∣ x := by
          have : ℓ ^ (e + 1) = ℓ ^ e * ℓ := pow_succ ℓ e
          rw [this]
          exact Nat.mul_dvd_of_dvd_div hpow_dvd hdiv
        have hle1 : e + 1 ≤ x.factorization ℓ := (hℓ_pr.pow_dvd_iff_le_factorization hx0).mp hpow1
        omega
      have hxy_eq : x = ℓ ^ e * y := (Nat.mul_div_cancel' hpow_dvd).symm
      have hdiv_prod : (∑ i ∈ Finset.range (e + 1), (chi3 ℓ) ^ i / (ℓ : ℚ) ^ i) *
            (∑ v ∈ y.divisors, chi3 v / (v : ℚ)) =
          ∑ d ∈ x.divisors, chi3 d / (d : ℚ) := by
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        rw [← Finset.sum_product']
        refine Finset.sum_bij (fun (p : ℕ × ℕ) _ => ℓ ^ p.1 * p.2) ?_ ?_ ?_ ?_
        · intro p hp
          rw [Finset.mem_product, Finset.mem_range, Nat.mem_divisors] at hp
          rw [Nat.mem_divisors]
          refine ⟨?_, hx0⟩
          rw [hxy_eq]
          exact mul_dvd_mul (pow_dvd_pow ℓ (by omega)) hp.2.1
        · intro p1 hp1 p2 hp2 heq
          rw [Finset.mem_product, Finset.mem_range, Nat.mem_divisors] at hp1 hp2
          have hv1_ndvd : ¬ (ℓ ∣ p1.2) := fun h => hy_ndvd (h.trans hp1.2.1)
          have hv2_ndvd : ¬ (ℓ ∣ p2.2) := fun h => hy_ndvd (h.trans hp2.2.1)
          have hi_eq : p1.1 = p2.1 := by
            by_contra hne
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · have hsub : ℓ ^ p1.1 * p1.2 = ℓ ^ p1.1 * (ℓ ^ (p2.1 - p1.1) * p2.2) := by
                rw [heq, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]
              have hcancel : p1.2 = ℓ ^ (p2.1 - p1.1) * p2.2 :=
                mul_left_cancel₀ (pow_pos hℓ_pr.pos p1.1).ne' hsub
              have hℓ_p1 : ℓ ∣ p1.2 := by
                rw [hcancel]
                exact dvd_mul_of_dvd_left (dvd_pow_self ℓ (by omega)) p2.2
              exact hv1_ndvd hℓ_p1
            · have hsub : ℓ ^ p2.1 * p2.2 = ℓ ^ p2.1 * (ℓ ^ (p1.1 - p2.1) * p1.2) := by
                rw [← heq, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hgt.le]
              have hcancel : p2.2 = ℓ ^ (p1.1 - p2.1) * p1.2 :=
                mul_left_cancel₀ (pow_pos hℓ_pr.pos p2.1).ne' hsub
              have hℓ_p2 : ℓ ∣ p2.2 := by
                rw [hcancel]
                exact dvd_mul_of_dvd_left (dvd_pow_self ℓ (by omega)) p1.2
              exact hv2_ndvd hℓ_p2
          have hv_eq : p1.2 = p2.2 := mul_left_cancel₀ (pow_pos hℓ_pr.pos p1.1).ne' (hi_eq ▸ heq)
          exact Prod.ext hi_eq hv_eq
        · intro d hd
          rw [Nat.mem_divisors] at hd
          have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hx0 hd.1
          let i := d.factorization ℓ
          let v := d / ℓ ^ i
          have hiv : ℓ ^ i * v = d := Nat.mul_div_cancel' (Nat.ordProj_dvd d ℓ)
          have hi_le : i ≤ e := (hℓ_pr.pow_dvd_iff_le_factorization hx0).mp ((Nat.ordProj_dvd d ℓ).trans hd.1)
          have hv_ndvd : ¬ (ℓ ∣ v) := by
            intro hdiv
            have hpow1 : ℓ ^ (i + 1) ∣ d := by
              rw [pow_succ]; exact Nat.mul_dvd_of_dvd_div (Nat.ordProj_dvd d ℓ) hdiv
            have hle1 : i + 1 ≤ d.factorization ℓ := (hℓ_pr.pow_dvd_iff_le_factorization hd0).mp hpow1
            omega
          have hv_dvd_y : v ∣ y := by
            have hv_dvd_x : v ∣ ℓ ^ e * y := hxy_eq ▸ (Nat.div_dvd_of_dvd (Nat.ordProj_dvd d ℓ)).trans hd.1
            have hcop_v : Nat.Coprime v (ℓ ^ e) := ((hℓ_pr.coprime_iff_not_dvd.mpr hv_ndvd).pow_left e).symm
            exact hcop_v.dvd_of_dvd_mul_left hv_dvd_x
          exact ⟨(i, v), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
            Nat.mem_divisors.mpr ⟨hv_dvd_y, hy0⟩⟩, hiv⟩
        · intro p _
          have hpow_chi : chi3 (ℓ ^ p.1) = (chi3 ℓ) ^ p.1 := by
            induction p.1 with
            | zero => simp [chi3]
            | succ j ih_pow => rw [pow_succ, hchi_mul, ih_pow, pow_succ]
          rw [hchi_mul, hpow_chi, Nat.cast_mul, Nat.cast_pow, mul_div_mul_comm]
      have hfactor1 : 0 < ∑ i ∈ Finset.range (e + 1), (chi3 ℓ) ^ i / (ℓ : ℚ) ^ i := by
        have hℓ3 : ℓ % 3 = 1 ∨ ℓ % 3 = 2 := by
          have : ¬ (3 ∣ ℓ) := fun h => hℓ_ne3 ((Nat.prime_dvd_prime_iff_eq (by decide) hℓ_pr).mp h).symm
          omega
        rcases hℓ3 with h1 | h2
        · have hchi1 : chi3 ℓ = 1 := by simp [chi3, h1]
          simp_rw [hchi1, one_pow]
          have hℓpos : (0 : ℚ) < (ℓ : ℚ) := by exact_mod_cast hℓ_pr.pos
          exact Finset.sum_pos (fun i _ => div_pos one_pos (pow_pos hℓpos i))
            ⟨0, Finset.mem_range.mpr (by omega)⟩
        · have hchi2 : chi3 ℓ = -1 := by simp [chi3, h2]
          simp_rw [hchi2]
          exact geom_alt_pos ℓ hℓ_pr.two_le e
      have hfactor2 : 0 < ∑ v ∈ y.divisors, chi3 v / (v : ℚ) := ih y hylt hy0 hy3
      rw [← hdiv_prod]
      exact mul_pos hfactor1 hfactor2

private lemma cofactor_balance_and_mod24 {n k p q m D A : ℕ}
    (hm_pos : 0 < m) (h3m : 3 ∣ m) (hm4 : m % 4 = 3)
    (hp4 : p % 4 = 3) (hq4 : q % 4 = 3) (hp3 : p % 3 = 2) (hq3 : q % 3 = 2)
    (hpq : p < q) (hp_gt2 : 2 ≤ p)
    (_hm_eq : m * (p * q) = n) (hA_def : A = m - D % m)
    (hsum_rel : k * m * (p * q) + 1 = m * (p + q) + p * q * D) :
    A * (p * q) + 1 = m * (p + q) ∧ A * p < 2 * m ∧ A % 24 = 17 := by
  have hD_lt_km : D < k * m := by
    have h1 : 1 ≤ m * (p + q) := by nlinarith
    by_contra hle
    have hkml : k * m ≤ D := by omega
    have hmul : k * m * (p * q) ≤ D * (p * q) := Nat.mul_le_mul_right _ hkml
    nlinarith
  let A' := k * m - D
  have hA'_pos : 0 < A' := by omega
  have hA'_bal : A' * (p * q) + 1 = m * (p + q) := by
    have hkD : A' + D = k * m := Nat.sub_add_cancel hD_lt_km.le
    have hmul : (A' + D) * (p * q) = k * m * (p * q) := congrArg (· * (p * q)) hkD
    have hadd : (A' + D) * (p * q) = A' * (p * q) + p * q * D := by ring
    linarith
  have hA'_p : A' * p < 2 * m := by
    have hlt1 : A' * (p * q) < m * (p + q) := by omega
    have hlt2 : m * (p + q) < 2 * m * q := by nlinarith only [hm_pos, hpq]
    have hlt3 : A' * p * q < 2 * m * q := by linarith
    exact Nat.lt_of_mul_lt_mul_right hlt3
  have hA'_lt_m : A' < m := by
    have h2p : A' * 2 ≤ A' * p := Nat.mul_le_mul_left A' hp_gt2
    omega
  have hA'_eq : A' = A := by
    have hD_mod_ne0 : D % m ≠ 0 := by
      intro h0
      obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h0
      have hkc_le : c ≤ k := by nlinarith only [hD_lt_km, hc, hm_pos]
      have hsub : A' = m * (k - c) := by
        dsimp only [A']
        rw [hc, mul_comm k m, ← Nat.mul_sub]
      have hkc_pos : 1 ≤ k - c := by
        by_contra h0'; have : k - c = 0 := by omega
        rw [this, mul_zero] at hsub; omega
      have hle_m : m ≤ A' := by rw [hsub]; exact Nat.le_mul_of_pos_right m hkc_pos
      omega
    have hdiv_D : D = m * (D / m) + D % m := (Nat.div_add_mod D m).symm
    have hDm_lt : D / m < k := by
      have hdm_le : m * (D / m) ≤ D := by rw [mul_comm]; exact Nat.div_mul_le_self D m
      by_contra hge
      have hk_le : k ≤ D / m := by omega
      have hkm_le : k * m ≤ m * (D / m) := by nlinarith only [hk_le]
      omega
    have h1 : D % m < m := Nat.mod_lt D hm_pos
    have hA_sub : A' = m * (k - D / m - 1) + (m - D % m) := by
      have hk_eq : k = (k - D / m - 1) + (D / m) + 1 := by omega
      have hkm_eq : k * m = m * (k - D / m - 1) + m * (D / m) + m := by
        calc k * m = ((k - D / m - 1) + (D / m) + 1) * m := by rw [← hk_eq]
          _ = m * (k - D / m - 1) + m * (D / m) + m := by ring
      have hadd : A' + (m * (D / m) + D % m) = m * (k - D / m - 1) + m * (D / m) + m := by
        rw [← hdiv_D]; dsimp only [A']; rw [Nat.sub_add_cancel hD_lt_km.le, hkm_eq]
      omega
    have hkc0 : k - D / m - 1 = 0 := by
      by_contra hne
      have : 1 ≤ k - D / m - 1 := by omega
      have hmul : m ≤ m * (k - D / m - 1) := Nat.le_mul_of_pos_right m this
      omega
    rw [hkc0, mul_zero, zero_add] at hA_sub
    exact hA_sub.trans hA_def.symm
  have hbal : A * (p * q) + 1 = m * (p + q) := hA'_eq ▸ hA'_bal
  have hAp_lt_2m : A * p < 2 * m := hA'_eq ▸ hA'_p
  have hA24 : A % 24 = 17 := by
    have hA3 : A % 3 = 2 := by
      have hm3 : m % 3 = 0 := Nat.mod_eq_zero_of_dvd h3m
      have hlhs3 := congrArg (· % 3) hbal
      rw [Nat.add_mod, Nat.mul_mod A (p * q), Nat.mul_mod p q, hp3, hq3,
        Nat.mul_mod m (p + q), Nat.add_mod p q, hp3, hq3, hm3] at hlhs3
      omega
    have hA8 : A % 8 = 1 := by
      have hp8 : p % 8 = 3 ∨ p % 8 = 7 := by omega
      have hq8 : q % 8 = 3 ∨ q % 8 = 7 := by omega
      have hm8 : m % 8 = 3 ∨ m % 8 = 7 := by omega
      have hlhs8 := congrArg (· % 8) hbal
      rw [Nat.add_mod, Nat.mul_mod A (p * q), Nat.mul_mod p q,
        Nat.mul_mod m (p + q), Nat.add_mod p q] at hlhs8
      rcases hp8 with hp8 | hp8 <;> rcases hq8 with hq8 | hq8 <;> rcases hm8 with hm8 | hm8 <;>
        simp [hp8, hq8, hm8] at hlhs8 <;> omega
    omega
  exact ⟨hbal, hAp_lt_2m, hA24⟩

private lemma cofactor_size_and_diff_bounds {n m p q A u t : ℕ}
    (_hm_pos : 0 < m) (hn9 : n % 9 = 3) (hm4 : m % 4 = 3)
    (hp4 : p % 4 = 3) (hq4 : q % 4 = 3) (hp3 : p % 3 = 2) (hq3 : q % 3 = 2)
    (hp_gt17 : 17 ≤ p) (hpq : p < q)
    (hm_eq : m * (p * q) = n)
    (hbal : A * (p * q) + 1 = m * (p + q)) (hAp_lt_2m : A * p < 2 * m) (hA24 : A % 24 = 17)
    (hmp : m * p = q * (q - 1) * u + 1) (hmq : m * q = p * (p - 1) * t + 1) :
    p < A ^ 2 ∧ m < A ^ 3 ∧ 16 * q < m ∧ n < A ^ 8 ∧ 30 * A * ((q - p) / 2) ^ 2 < m ^ 2 := by
  have hm_pq : m * (p + q) = m * q + m * p := by ring
  have hAp_eq : A * p = m + (q - 1) * u := by
    have h1 : (A * p) * q = (m + (q - 1) * u) * q := by
      have hmul : A * (p * q) = m * q + q * (q - 1) * u := by linarith [hbal, hm_pq, hmp]
      calc (A * p) * q = A * (p * q) := by ring
        _ = m * q + q * (q - 1) * u := hmul
        _ = (m + (q - 1) * u) * q := by ring
    exact mul_right_cancel₀ (by omega : q ≠ 0) h1
  have hAq_eq : A * q = m + (p - 1) * t := by
    have h1 : (A * q) * p = (m + (p - 1) * t) * p := by
      have hmul : A * (p * q) = m * p + p * (p - 1) * t := by linarith [hbal, hm_pq, hmq]
      calc (A * q) * p = A * (p * q) := by ring
        _ = m * p + p * (p - 1) * t := hmul
        _ = (m + (p - 1) * t) * p := by ring
    exact mul_right_cancel₀ (by omega : p ≠ 0) h1
  have hu18 : u % 18 = 16 := by
    have hu2 : u % 2 = 0 := by
      have h1 := congrArg (· % 4) hmp
      rw [Nat.mul_mod m p, hm4, hp4, Nat.add_mod, Nat.mul_mod (q * (q - 1)) u,
        Nat.mul_mod q (q - 1)] at h1
      have hq1_4 : (q - 1) % 4 = 2 := by omega
      rw [hq4, hq1_4] at h1
      omega
    have hu9 : u % 9 = 7 := by
      have hnq9 : n = q * (q * (q - 1) * u + 1) := by
        rw [← hmp]
        calc n = m * (p * q) := hm_eq.symm
          _ = q * (m * p) := by ring
      have h1 := congrArg (· % 9) hnq9
      rw [hn9] at h1
      have hq9 : q % 9 = 2 ∨ q % 9 = 5 ∨ q % 9 = 8 := by omega
      rcases hq9 with hq9 | hq9 | hq9
      · have hq1_9 : (q - 1) % 9 = 1 := by omega
        rw [Nat.mul_mod q (q * (q - 1) * u + 1), Nat.add_mod,
          Nat.mul_mod (q * (q - 1)) u, Nat.mul_mod q (q - 1), hq9, hq1_9] at h1
        omega
      · have hq1_9 : (q - 1) % 9 = 4 := by omega
        rw [Nat.mul_mod q (q * (q - 1) * u + 1), Nat.add_mod,
          Nat.mul_mod (q * (q - 1)) u, Nat.mul_mod q (q - 1), hq9, hq1_9] at h1
        omega
      · have hq1_9 : (q - 1) % 9 = 7 := by omega
        rw [Nat.mul_mod q (q * (q - 1) * u + 1), Nat.add_mod,
          Nat.mul_mod (q * (q - 1)) u, Nat.mul_mod q (q - 1), hq9, hq1_9] at h1
        omega
    omega
  have hu16 : 16 ≤ u := by omega
  have h2u_lt_A : 2 * u < A := by
    have hqu_lt_m : (q - 1) * u < m := by nlinarith only [hAp_eq, hAp_lt_2m]
    have hrew : 2 * u * (q - 1) = 2 * ((q - 1) * u) := by ring
    have h1 : 2 * u * (q - 1) < A * p := by linarith [hAp_eq, hqu_lt_m, hrew]
    have h2 : A * p ≤ A * (q - 1) := Nat.mul_le_mul_left A (by omega)
    have h3 : 2 * u * (q - 1) < A * (q - 1) := lt_of_lt_of_le h1 h2
    exact Nat.lt_of_mul_lt_mul_right h3
  have h16q_lt_m : 16 * q < m := by
    have h1 : 16 * (q * (q - 1)) ≤ u * (q * (q - 1)) := Nat.mul_le_mul_right _ hu16
    have hlt : 16 * q * (q - 1) < m * p := by
      have : 16 * q * (q - 1) = 16 * (q * (q - 1)) := by ring
      linarith [hmp, h1, this]
    have h2 : m * p ≤ m * (q - 1) := Nat.mul_le_mul_left m (by omega)
    exact Nat.lt_of_mul_lt_mul_right (lt_of_lt_of_le hlt h2)
  have hp_lt_A2 : p < A ^ 2 := by
    let d := Nat.gcd (p - 1) (q - 1)
    let x := (p - 1) / d
    let y := (q - 1) / d
    have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left _ (by omega)
    have hdx : d * x = p - 1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have hdy : d * y = q - 1 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    have hcop_xy : Nat.Coprime x y := Nat.coprime_div_gcd_div_gcd hd_pos
    have hd_dvd_A1 : d ∣ A - 1 := by
      have hd_dvd_Z : (d : ℤ) ∣ (A : ℤ) - 1 := by
        have hdp : (d : ℤ) ∣ (p : ℤ) - 1 := by
          have h := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left (p - 1) (q - 1))
          rwa [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at h
        have hdq : (d : ℤ) ∣ (q : ℤ) - 1 := by
          have h := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right (p - 1) (q - 1))
          rwa [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one] at h
        have hmpZ : (m : ℤ) * (p : ℤ) = (q : ℤ) * ((q : ℤ) - 1) * (u : ℤ) + 1 := by
          have h := hmp
          zify [show 1 ≤ q by omega] at h
          exact h
        have hApZ : (A : ℤ) * (p : ℤ) = (m : ℤ) + ((q : ℤ) - 1) * (u : ℤ) := by
          have h := hAp_eq
          zify [show 1 ≤ q by omega] at h
          exact h
        obtain ⟨ap, hap⟩ := hdp
        obtain ⟨aq, haq⟩ := hdq
        have hdm1 : (d : ℤ) ∣ (m : ℤ) - 1 := by
          refine ⟨(q : ℤ) * (u : ℤ) * aq - (m : ℤ) * ap, ?_⟩
          linear_combination hmpZ + (q : ℤ) * (u : ℤ) * haq - (m : ℤ) * hap
        obtain ⟨am, ham⟩ := hdm1
        refine ⟨(u : ℤ) * aq + am - (A : ℤ) * ap, ?_⟩
        linear_combination hApZ + (u : ℤ) * haq + ham - (A : ℤ) * hap
      have h17A : 1 ≤ A := by omega
      have hd_nat : (d : ℤ) ∣ ((A - 1 : ℕ) : ℤ) := by
        rwa [Nat.cast_sub h17A, Nat.cast_one]
      exact Int.natCast_dvd_natCast.mp hd_nat
    have hdiff_eq : (A + u) * (q - 1) = (A + t) * (p - 1) := by
      have hAp_Z : (A : ℤ) * (p : ℤ) = (m : ℤ) + ((q : ℤ) - 1) * (u : ℤ) := by
        have h := hAp_eq
        zify [show 1 ≤ q by omega] at h
        exact h
      have hAq_Z : (A : ℤ) * (q : ℤ) = (m : ℤ) + ((p : ℤ) - 1) * (t : ℤ) := by
        have h := hAq_eq
        zify [show 1 ≤ p by omega] at h
        exact h
      have hZ : ((A + u : ℕ) : ℤ) * ((q - 1 : ℕ) : ℤ) = ((A + t : ℕ) : ℤ) * ((p - 1 : ℕ) : ℤ) := by
        zify [show 1 ≤ q by omega, show 1 ≤ p by omega]
        linear_combination hAq_Z - hAp_Z
      exact_mod_cast hZ
    have hxy_eq : d * ((A + u) * y) = d * ((A + t) * x) := by
      calc d * ((A + u) * y) = (A + u) * (d * y) := by ring
        _ = (A + u) * (q - 1) := by rw [hdy]
        _ = (A + t) * (p - 1) := hdiff_eq
        _ = (A + t) * (d * x) := by rw [hdx]
        _ = d * ((A + t) * x) := by ring
    have hxy_cancel : (A + u) * y = (A + t) * x := mul_left_cancel₀ hd_pos.ne' hxy_eq
    have hx_dvd : x ∣ A + u := hcop_xy.dvd_of_dvd_mul_right ⟨A + t, by linarith [hxy_cancel]⟩
    have hx3 : ¬ (3 ∣ x) := fun h3x => by
      have : 3 ∣ p - 1 := hdx ▸ dvd_mul_of_dvd_right h3x d
      omega
    have h3_dvd_Au : 3 ∣ A + u := Nat.dvd_of_mod_eq_zero (by omega)
    have h3x_dvd : 3 * x ∣ A + u :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr hx3).mul_dvd_of_dvd_of_dvd h3_dvd_Au hx_dvd
    have hd_le : d ≤ A - 1 := Nat.le_of_dvd (by omega) hd_dvd_A1
    have h3x_le : 3 * x ≤ A + u := Nat.le_of_dvd (by omega) h3x_dvd
    have h2x_lt : 2 * x < A := by omega
    have hmul : d * (2 * x) ≤ (A - 1) * (2 * x) := Nat.mul_le_mul_right _ hd_le
    have hmul2 : (A - 1) * (2 * x) < (A - 1) * A := Nat.mul_lt_mul_of_pos_left h2x_lt (by omega)
    have hp_eq : p = d * x + 1 := by omega
    have h2p_lt : 2 * p < (A - 1) * A + 2 := by
      calc 2 * p = d * (2 * x) + 2 := by rw [hp_eq]; ring
        _ ≤ (A - 1) * (2 * x) + 2 := Nat.add_le_add_right hmul 2
        _ < (A - 1) * A + 2 := Nat.add_lt_add_right hmul2 2
    have hA_ge17 : 17 ≤ A := by omega
    have hA_sq : (A - 1) * A + 2 ≤ 2 * A ^ 2 := by
      have : A - 1 ≤ A := by omega
      nlinarith only [hA_ge17, this]
    omega
  have hm_lt_A3 : m < A ^ 3 := by
    have hm_lt_Ap : m < A * p := by
      have : 1 ≤ (q - 1) * u := Nat.mul_pos (by omega) (by omega)
      omega
    have hlt : A * p < A * A ^ 2 := Nat.mul_lt_mul_of_pos_left hp_lt_A2 (by omega)
    linarith [hlt, show A * A ^ 2 = A ^ 3 by ring]
  have hn_lt_A8 : n < A ^ 8 := by
    have hq_lt_A3 : q < A ^ 3 := by omega
    calc n = m * (p * q) := hm_eq.symm
      _ < A ^ 3 * (A ^ 2 * A ^ 3) := by
          have h1 : p * q < A ^ 2 * A ^ 3 :=
            mul_lt_mul'' hp_lt_A2 hq_lt_A3 (Nat.zero_le p) (Nat.zero_le q)
          exact mul_lt_mul'' hm_lt_A3 h1 (Nat.zero_le m) (Nat.zero_le (p * q))
      _ = A ^ 8 := by ring
  have hdiff_bound : 30 * A * ((q - p) / 2) ^ 2 < m ^ 2 := by
    let s := (q - p) / 2
    have h2s : 2 * s = q - p := by dsimp only [s]; omega
    have h2s_lt : 2 * s < q := by omega
    have h4s2 : 4 * s ^ 2 < q ^ 2 := by nlinarith only [h2s_lt]
    have hq18 : 18 ≤ q := by omega
    have h15q2_16 : 15 * q ^ 2 < 16 * q * (q - 1) := by
      have h1 : 15 * q < 16 * (q - 1) := by omega
      have h2 := Nat.mul_lt_mul_of_pos_left h1 (by omega : 0 < q)
      calc 15 * q ^ 2 = q * (15 * q) := by ring
        _ < q * (16 * (q - 1)) := h2
        _ = 16 * q * (q - 1) := by ring
    have h16_uq : 16 * q * (q - 1) ≤ u * (q * (q - 1)) := by
      have h1 := Nat.mul_le_mul_right (q * (q - 1)) hu16
      linarith [show 16 * (q * (q - 1)) = 16 * q * (q - 1) by ring]
    have h15q2 : 15 * q ^ 2 < m * p := by
      have hrew : u * (q * (q - 1)) = q * (q - 1) * u := by ring
      linarith [h15q2_16, h16_uq, hmp, hrew]
    have h60 : 60 * A * p * s ^ 2 < 2 * m ^ 2 * p := by
      have hAp_pos : 0 < 15 * A * p := Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega)
      calc 60 * A * p * s ^ 2 = 15 * A * p * (4 * s ^ 2) := by ring
        _ < 15 * A * p * q ^ 2 := Nat.mul_lt_mul_of_pos_left h4s2 hAp_pos
        _ = (A * p) * (15 * q ^ 2) := by ring
        _ < (2 * m) * (m * p) := mul_lt_mul'' hAp_lt_2m h15q2 (by positivity) (by positivity)
        _ = 2 * m ^ 2 * p := by ring
    have hrew1 : 60 * A * p * s ^ 2 = (30 * A * s ^ 2) * (2 * p) := by ring
    have hrew2 : 2 * m ^ 2 * p = m ^ 2 * (2 * p) := by ring
    rw [hrew1, hrew2] at h60
    exact Nat.lt_of_mul_lt_mul_right h60
  exact ⟨hp_lt_A2, hm_lt_A3, h16q_lt_m, hn_lt_A8, hdiff_bound⟩

private lemma two_largest_cofactor_package {n k : ℕ}
    (hsqf : Squarefree n) (hodd : Odd n) (h3 : 3 ∣ n)
    (hn36 : n % 36 = 3)
    (hcard22 : 10 ^ 22 ≤ n.primeFactors.card)
    (hprimes : ∀ p ∈ n.primeFactors, p = 3 ∨ p % 60 = 11 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59)
    (hdvd : ∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1))
    (hk4 : 4 ≤ k)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    ∃ p q : ℕ, p ∈ n.primeFactors ∧ q ∈ n.primeFactors ∧ p < q ∧
      (∀ r ∈ n.primeFactors, r ≤ q) ∧ (∀ r ∈ n.primeFactors.erase q, r ≤ p) ∧
      let m := n / (p * q)
      let D := ∑ r ∈ m.primeFactors, m / r
      let A := m - D % m
      let L := m.primeFactors.lcm (fun r => (r - 1) / 2)
      A * (p * q) + 1 = m * (p + q) ∧ A % 24 = 17 ∧
      p < A ^ 2 ∧ m < A ^ 3 ∧ 16 * q < m ∧ n < A ^ 8 ∧ 10 ^ (n.primeFactors.card - 1) < n ∧
      2 * L ∣ n - 1 ∧ ¬ (3 ∣ L) ∧ ((∀ r ∈ n.primeFactors, r % 60 ≠ 11) → ¬ (5 ∣ L)) ∧
      (5497 : ℚ) / 375 < ∑ d ∈ L.divisors, (1 / (d : ℚ)) ∧
      ((L : ℤ) ∣ (((m : ℤ) ^ 2 * ((q : ℤ) - p)) ^ 2 - (((A : ℤ) + m) ^ 2 - 4 * (m : ℤ) ^ 3))) ∧
      30 * A * ((q - p) / 2) ^ 2 < m ^ 2 := by
  have hn0 : n ≠ 0 := hsqf.ne_zero
  have hnon : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  let q := n.primeFactors.max' hnon
  have hq_mem : q ∈ n.primeFactors := Finset.max'_mem _ hnon
  have hq_max : ∀ r ∈ n.primeFactors, r ≤ q := fun r hr => Finset.le_max' _ r hr
  have hnon_er : (n.primeFactors.erase q).Nonempty := by
    have hcard_er : (n.primeFactors.erase q).card = n.primeFactors.card - 1 :=
      Finset.card_erase_of_mem hq_mem
    exact Finset.card_pos.mp (by omega)
  let p := (n.primeFactors.erase q).max' hnon_er
  have hp_er : p ∈ n.primeFactors.erase q := Finset.max'_mem _ hnon_er
  have hp_ne_q : p ≠ q := (Finset.mem_erase.mp hp_er).1
  have hp_mem : p ∈ n.primeFactors := (Finset.mem_erase.mp hp_er).2
  have hp_max : ∀ r ∈ n.primeFactors.erase q, r ≤ p := fun r hr => Finset.le_max' _ r hr
  have hp_lt_q : p < q := lt_of_le_of_ne (hq_max p hp_mem) hp_ne_q
  have hp_pr : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hq_pr : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have hp_ge : 10 ^ 22 - 1 ≤ p := by
    have hsub : n.primeFactors.erase q ⊆ Finset.Icc 1 p := fun r hr => by
      have hr_mem : r ∈ n.primeFactors := (Finset.mem_erase.mp hr).2
      exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hr_mem).pos, hp_max r hr⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hq_mem, Nat.card_Icc] at hle
    omega
  have hp_1000 : 1000 < p := by omega
  have hq_1000 : 1000 < q := by omega
  have hp_mod60 : p % 60 = 11 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59 := by
    rcases hprimes p hp_mem with h3eq | h11 | h23 | h47 | h59
    · omega
    · exact Or.inl h11
    · exact Or.inr (Or.inl h23)
    · exact Or.inr (Or.inr (Or.inl h47))
    · exact Or.inr (Or.inr (Or.inr h59))
  have hq_mod60 : q % 60 = 11 ∨ q % 60 = 23 ∨ q % 60 = 47 ∨ q % 60 = 59 := by
    rcases hprimes q hq_mem with h3eq | h11 | h23 | h47 | h59
    · omega
    · exact Or.inl h11
    · exact Or.inr (Or.inl h23)
    · exact Or.inr (Or.inr (Or.inl h47))
    · exact Or.inr (Or.inr (Or.inr h59))
  have hp4 : p % 4 = 3 := by omega
  have hq4 : q % 4 = 3 := by omega
  have hp3 : p % 3 = 2 := by omega
  have hq3 : q % 3 = 2 := by omega
  have hpq_cop : Nat.Coprime p q := (Nat.coprime_primes hp_pr hq_pr).mpr hp_ne_q
  have hpq_dvd : p * q ∣ n :=
    hpq_cop.mul_dvd_of_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp_mem)
      (Nat.dvd_of_mem_primeFactors hq_mem)
  let m := n / (p * q)
  have hm_eq : m * (p * q) = n := Nat.div_mul_cancel hpq_dvd
  have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpq_dvd)
    (Nat.mul_pos hp_pr.pos hq_pr.pos)
  have hm0 : m ≠ 0 := hm_pos.ne'
  have hm_pf_eq : m.primeFactors = (n.primeFactors.erase q).erase p := by
    have h1 : n.primeFactors = (m * p).primeFactors ∪ q.primeFactors := by
      rw [← hm_eq, ← mul_assoc, Nat.primeFactors_mul (mul_ne_zero hm0 hp_pr.ne_zero) hq_pr.ne_zero]
    have hmp_cop : Nat.Coprime (m * p) q := by
      have hsq_pq : Squarefree ((m * p) * q) := by rwa [mul_assoc, hm_eq]
      exact (Nat.squarefree_mul_iff.mp hsq_pq).1
    have hq_not_mp : q ∉ (m * p).primeFactors := fun hq_in =>
      (hq_pr.coprime_iff_not_dvd.mp hmp_cop.symm) (Nat.dvd_of_mem_primeFactors hq_in)
    have h2 : n.primeFactors.erase q = (m * p).primeFactors := by
      rw [h1, hq_pr.primeFactors, Finset.union_comm, Finset.singleton_union,
        Finset.erase_insert hq_not_mp]
    have hmp_sqf : Squarefree (m * p) :=
      hsqf.squarefree_of_dvd ⟨q, by rw [← hm_eq, mul_assoc]⟩
    have hm_p_cop : Nat.Coprime m p := (Nat.squarefree_mul_iff.mp hmp_sqf).1
    have hp_not_m : p ∉ m.primeFactors := fun hp_in =>
      (hp_pr.coprime_iff_not_dvd.mp hm_p_cop.symm) (Nat.dvd_of_mem_primeFactors hp_in)
    rw [h2, Nat.primeFactors_mul hm0 hp_pr.ne_zero, hp_pr.primeFactors, Finset.union_comm,
      Finset.singleton_union, Finset.erase_insert hp_not_m]
  have hm_pf_sub : m.primeFactors ⊆ n.primeFactors := fun r hr => by
    rw [hm_pf_eq] at hr
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).2
  have h3_in_m : 3 ∈ m.primeFactors := by
    rw [hm_pf_eq]
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
      Nat.mem_primeFactors.mpr ⟨by decide, h3, hn0⟩⟩⟩
  have h3_dvd_m : 3 ∣ m := Nat.dvd_of_mem_primeFactors h3_in_m
  have hm4 : m % 4 = 3 := by
    have hn4 : n % 4 = 3 := by omega
    rw [← hm_eq, Nat.mul_mod, show (p * q) % 4 = 1 by rw [Nat.mul_mod, hp4, hq4]] at hn4
    omega
  let D := ∑ r ∈ m.primeFactors, m / r
  let A := m - D % m
  have hint : ∑ r ∈ n.primeFactors, n / r = k * n + 1 := sum_div_eq_mul_add_one_loc hn0 hsum
  have hnq_eq : n / q = m * p := by
    rw [← hm_eq, ← mul_assoc, Nat.mul_div_cancel _ hq_pr.pos]
  have hnp_eq : n / p = m * q := by
    rw [← hm_eq, mul_comm p q, ← mul_assoc, Nat.mul_div_cancel _ hp_pr.pos]
  have hsum_rel : ∑ r ∈ n.primeFactors, n / r = m * (p + q) + p * q * D := by
    have h1 := (Finset.add_sum_erase n.primeFactors (fun r => n / r) hq_mem).symm
    have h2 := (Finset.add_sum_erase (n.primeFactors.erase q) (fun r => n / r) hp_er).symm
    rw [← hm_pf_eq] at h2
    have hm_terms : ∑ r ∈ m.primeFactors, n / r = p * q * D := by
      dsimp only [D]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr_dvd : r ∣ m := Nat.dvd_of_mem_primeFactors hr
      calc n / r = (m * (p * q)) / r := by rw [hm_eq]
        _ = (p * q * m) / r := by rw [mul_comm m (p * q)]
        _ = p * q * (m / r) := Nat.mul_div_assoc (p * q) hr_dvd
    rw [h1, h2, hnq_eq, hnp_eq, hm_terms]
    ring
  have hbal_eq : k * m * (p * q) + 1 = m * (p + q) + p * q * D := by
    calc k * m * (p * q) + 1 = k * n + 1 := by rw [← hm_eq]; ring
      _ = ∑ r ∈ n.primeFactors, n / r := hint.symm
      _ = m * (p + q) + p * q * D := hsum_rel
  obtain ⟨hbal, hAp_lt_2m, hA24⟩ := cofactor_balance_and_mod24 hm_pos h3_dvd_m hm4 hp4 hq4 hp3 hq3
    hp_lt_q (by omega) hm_eq rfl hbal_eq
  obtain ⟨u, hu⟩ := hdvd q hq_mem
  rw [hnq_eq] at hu
  have hmp_pos : 1 ≤ m * p := Nat.mul_pos hm_pos hp_pr.pos
  have hmp_eq : m * p = q * (q - 1) * u + 1 := by omega
  obtain ⟨t, ht⟩ := hdvd p hp_mem
  rw [hnp_eq] at ht
  have hmq_pos : 1 ≤ m * q := Nat.mul_pos hm_pos hq_pr.pos
  have hmq_eq : m * q = p * (p - 1) * t + 1 := by omega
  obtain ⟨hp_lt_A2, hm_lt_A3, h16q_lt_m, hn_lt_A8, hdiff_bound⟩ := cofactor_size_and_diff_bounds
    hm_pos (by omega : n % 9 = 3) hm4 hp4 hq4 hp3 hq3 (by omega) hp_lt_q hm_eq hbal hAp_lt_2m hA24
    hmp_eq hmq_eq
  let L := m.primeFactors.lcm (fun r => (r - 1) / 2)
  have h2L_dvd : 2 * L ∣ n - 1 := by
    refine twice_halfKorseltLcm_dvd h3_in_m (fun r hr => ?_) (fun r hr => ?_)
    · have hr_mem : r ∈ n.primeFactors := hm_pf_sub hr
      have hr_dvd : r ∣ n := Nat.dvd_of_mem_primeFactors hr_mem
      have hr2 : r % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one r with h0 | h1
        · have : n % 2 = 0 := by rw [← Nat.div_mul_cancel hr_dvd, Nat.mul_mod, h0]; simp
          have : n % 2 = 1 := Nat.odd_iff.mp hodd
          omega
        · exact h1
      exact Nat.odd_iff.mpr hr2
    · have hr_mem : r ∈ n.primeFactors := hm_pf_sub hr
      have hr_pr : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
      have hr_dvd : r ∣ n := Nat.dvd_of_mem_primeFactors hr_mem
      have hr1_np : r - 1 ∣ n / r - 1 := (dvd_mul_left (r - 1) r).trans (hdvd r hr_mem)
      have hn_pos : 1 ≤ n := by omega
      have hnp_pos : 1 ≤ n / r := Nat.div_pos (Nat.le_of_dvd hn_pos hr_dvd) hr_pr.pos
      have hid : n - 1 = r * (n / r - 1) + (r - 1) := by
        have hmul : r * (n / r) = n := Nat.mul_div_cancel' hr_dvd
        zify [hr_pr.one_lt.le, hnp_pos, hn_pos]
        have hmulZ : (r : ℤ) * ((n / r : ℕ) : ℤ) = (n : ℤ) := by exact_mod_cast hmul
        linarith
      rw [hid]
      exact dvd_add (dvd_mul_of_dvd_right hr1_np r) (dvd_refl _)
  have hL3 : ¬ (3 ∣ L) := by
    refine not_prime_dvd_finset_lcm Nat.prime_three m.primeFactors (fun r => (r - 1) / 2) ?_
    intro r hr
    by_cases hr3 : r = 3
    · subst hr3; decide
    · have hr_mem : r ∈ n.primeFactors := hm_pf_sub hr
      rcases hprimes r hr_mem with h | h11 | h23 | h47 | h59 <;> first | exact absurd h hr3 | omega
  have hL5_of : (∀ r ∈ n.primeFactors, r % 60 ≠ 11) → ¬ (5 ∣ L) := fun hno11 => by
    refine not_prime_dvd_finset_lcm (by decide) m.primeFactors (fun r => (r - 1) / 2) ?_
    intro r hr
    have hr_mem : r ∈ n.primeFactors := hm_pf_sub hr
    have hne11 := hno11 r hr_mem
    rcases hprimes r hr_mem with rfl | h11 | h23 | h47 | h59
    · decide
    · exact absurd h11 hne11
    · omega
    · omega
    · omega
  have hL0 : L ≠ 0 := by
    intro h0
    rw [Finset.lcm_eq_zero_iff] at h0
    rcases h0 with ⟨r, hr, hr0⟩
    have hr3 : 3 ≤ r := by
      have hr_mem := hm_pf_sub hr
      rcases hprimes r hr_mem with rfl | h11 | h23 | h47 | h59 <;> omega
    omega
  have hL_sum : (5497 : ℚ) / 375 < ∑ d ∈ L.divisors, (1 / (d : ℚ)) := by
    let Sm := m.primeFactors.erase 3
    let f : ℕ → ℕ := fun r => (r - 1) / 2
    have hSm_res : ∀ r ∈ Sm, r % 12 = 11 := fun r hr => by
      rcases Finset.mem_erase.mp hr with ⟨hr3, hr_m⟩
      rcases hprimes r (hm_pf_sub hr_m) with rfl | h11 | h23 | h47 | h59 <;>
        first | exact absurd rfl hr3 | omega
    let D2 := L.divisors.filter (fun d => d % 3 = 2)
    let D1 := L.divisors.filter (fun d => d % 3 = 1)
    have hmap : ∀ r ∈ Sm, f r ∈ D2 := fun r hr => by
      have hr12 := hSm_res r hr
      have hr_m : r ∈ m.primeFactors := (Finset.mem_erase.mp hr).2
      have hfdvd : f r ∣ L := Finset.dvd_lcm hr_m
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hfdvd, hL0⟩, by dsimp only [f]; omega⟩
    have hinj : ∀ r1 ∈ Sm, ∀ r2 ∈ Sm, f r1 = f r2 → r1 = r2 := fun r1 hr1 r2 hr2 heq => by
      have h1 := hSm_res r1 hr1
      have h2 := hSm_res r2 hr2
      dsimp only [f] at heq
      omega
    have hSm_le_D2 : ∑ r ∈ Sm, (1 / (r : ℚ)) ≤ (1 / 2 : ℚ) * ∑ d ∈ D2, (1 / (d : ℚ)) := by
      have hterm_le : ∑ r ∈ Sm, (1 / (r : ℚ)) ≤ ∑ r ∈ Sm, (1 / (2 * (f r : ℚ))) := by
        refine Finset.sum_le_sum fun r hr => ?_
        have hr12 := hSm_res r hr
        have hf_pos : (0 : ℚ) < 2 * (f r : ℚ) := by
          have : 1 ≤ f r := by dsimp only [f]; omega
          positivity
        have hle : 2 * f r ≤ r := by dsimp only [f]; omega
        exact one_div_le_one_div_of_le hf_pos (by exact_mod_cast hle)
      have himg : ∑ r ∈ Sm, (1 / (2 * (f r : ℚ))) = (1 / 2 : ℚ) * ∑ d ∈ Sm.image f, (1 / (d : ℚ)) := by
        rw [Finset.mul_sum, Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun r _ => by ring
      have hsub : Sm.image f ⊆ D2 := fun d hd => by
        rcases Finset.mem_image.mp hd with ⟨r, hr, rfl⟩
        exact hmap r hr
      have hsum_img : ∑ d ∈ Sm.image f, (1 / (d : ℚ)) ≤ ∑ d ∈ D2, (1 / (d : ℚ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      linarith
    have hchi_pos := sum_div_chi3_pos L hL0 hL3
    have hD_part : D1 ∪ D2 = L.divisors := by
      ext d
      simp only [D1, D2, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hd, _⟩ | ⟨hd, _⟩) <;> exact hd
      · intro hd
        have hd3 : ¬ (3 ∣ d) := fun h3d => hL3 (h3d.trans (Nat.dvd_of_mem_divisors hd))
        have : d % 3 = 1 ∨ d % 3 = 2 := by omega
        rcases this with h1 | h2 <;> [exact Or.inl ⟨hd, h1⟩; exact Or.inr ⟨hd, h2⟩]
    have hD_disj : Disjoint D1 D2 := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    have hchi_eq : ∑ d ∈ L.divisors, (if d % 3 = 1 then (1 : ℚ) else if d % 3 = 2 then -1 else 0) / (d : ℚ) =
        (∑ d ∈ D1, (1 / (d : ℚ))) - ∑ d ∈ D2, (1 / (d : ℚ)) := by
      rw [← hD_part, Finset.sum_union hD_disj]
      have hs1 : ∑ d ∈ D1, (if d % 3 = 1 then (1 : ℚ) else if d % 3 = 2 then -1 else 0) / (d : ℚ) =
          ∑ d ∈ D1, (1 / (d : ℚ)) := Finset.sum_congr rfl fun d hd => by
        rw [(Finset.mem_filter.mp hd).2]; simp
      have hs2 : ∑ d ∈ D2, (if d % 3 = 1 then (1 : ℚ) else if d % 3 = 2 then -1 else 0) / (d : ℚ) =
          - ∑ d ∈ D2, (1 / (d : ℚ)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd2 := (Finset.mem_filter.mp hd).2
        simp [hd2, neg_div]
      rw [hs1, hs2, sub_eq_add_neg]
    have hsum_div_eq : ∑ d ∈ L.divisors, (1 / (d : ℚ)) =
        (∑ d ∈ D1, (1 / (d : ℚ))) + ∑ d ∈ D2, (1 / (d : ℚ)) := by
      rw [← hD_part, Finset.sum_union hD_disj]
    have hD2_half : ∑ d ∈ D2, (1 / (d : ℚ)) < (1 / 2 : ℚ) * ∑ d ∈ L.divisors, (1 / (d : ℚ)) := by
      linarith
    have hSm_lt_quarter : ∑ r ∈ Sm, (1 / (r : ℚ)) < (1 / 4 : ℚ) * ∑ d ∈ L.divisors, (1 / (d : ℚ)) := by
      linarith
    have hn_sum_split : ∑ r ∈ n.primeFactors, (1 / (r : ℚ)) =
        1 / (3 : ℚ) + 1 / (p : ℚ) + 1 / (q : ℚ) + ∑ r ∈ Sm, (1 / (r : ℚ)) := by
      have h1 := (Finset.add_sum_erase n.primeFactors (fun r => (1 / (r : ℚ))) hq_mem).symm
      have h2 := (Finset.add_sum_erase (n.primeFactors.erase q) (fun r => (1 / (r : ℚ))) hp_er).symm
      rw [← hm_pf_eq] at h2
      have h3 := (Finset.add_sum_erase m.primeFactors (fun r => (1 / (r : ℚ))) h3_in_m).symm
      push_cast at h1 h2 h3 ⊢
      linarith
    have hsum_gt4 : (4 : ℚ) < ∑ r ∈ n.primeFactors, (1 / (r : ℚ)) := by
      have hnpos : (0 : ℚ) < 1 / (n : ℚ) := one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0))
      have hk4q : (4 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk4
      linarith
    have hp_inv : 1 / (p : ℚ) < 1 / (1000 : ℚ) :=
      one_div_lt_one_div_of_lt (by norm_num) (by exact_mod_cast hp_1000)
    have hq_inv : 1 / (q : ℚ) < 1 / (1000 : ℚ) :=
      one_div_lt_one_div_of_lt (by norm_num) (by exact_mod_cast hq_1000)
    linarith
  have hdisc : (L : ℤ) ∣ (((m : ℤ) ^ 2 * ((q : ℤ) - p)) ^ 2 - (((A : ℤ) + m) ^ 2 - 4 * (m : ℤ) ^ 3)) := by
    have hbalZ : (A : ℤ) * ((p : ℤ) * q) + 1 = m * ((p : ℤ) + q) := by exact_mod_cast hbal
    have hKZ : (L : ℤ) ∣ (m : ℤ) * ((p : ℤ) * q) - 1 := by
      have hL_dvd_n1 : L ∣ n - 1 := (dvd_mul_left L 2).trans h2L_dvd
      have hn_pos : 1 ≤ n := by omega
      have h1Z : (L : ℤ) ∣ ((n - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hL_dvd_n1
      rw [Nat.cast_sub hn_pos, Nat.cast_one] at h1Z
      have hnm : (n : ℤ) = (m : ℤ) * ((p : ℤ) * q) := by exact_mod_cast hm_eq.symm
      rwa [← hnm]
    exact cofactor_discriminant_square hbalZ hKZ
  exact ⟨p, q, hp_mem, hq_mem, hp_lt_q, hq_max, hp_max,
    hbal, hA24, hp_lt_A2, hm_lt_A3, h16q_lt_m, hn_lt_A8,
    three_lt_pf_bound hn0 hsqf h3 hprimes, h2L_dvd, hL3, hL5_of, hL_sum, hdisc, hdiff_bound⟩

/- ## Section 3: Self-contained Selberg Lambda^2 sieve mod 60 -/

private lemma sqf_coprime_div {u r : ℕ} (hu : Squarefree u) (hr : r ∣ u) :
    Nat.Coprime r (u / r) := by
  by_contra hnc
  have hg1 : Nat.gcd r (u / r) ≠ 1 := hnc
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg1
  have hpr : p ∣ r := hpg.trans (Nat.gcd_dvd_left r (u / r))
  have hpq : p ∣ u / r := hpg.trans (Nat.gcd_dvd_right r (u / r))
  have hpp : p * p ∣ r * (u / r) := mul_dvd_mul hpr hpq
  rw [Nat.mul_div_cancel' hr] at hpp
  exact hp.ne_one (Nat.isUnit_iff.mp (hu p hpp))

private lemma sum_inv_totient_divisors {d : ℕ} (hd : Squarefree d) (hd0 : d ≠ 0) :
    ∑ t ∈ d.divisors, (1 / (t.totient : ℝ)) = (d : ℝ) / (d.totient : ℝ) := by
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd0
  have hdt_pos : (0 : ℝ) < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd_pos)
  rw [eq_div_iff hdt_pos.ne']
  have hterm : ∀ t ∈ d.divisors, (1 / (t.totient : ℝ)) * (d.totient : ℝ) = ((d / t).totient : ℝ) := by
    intro t ht
    obtain ⟨htd, _⟩ := Nat.mem_divisors.mp ht
    have hcop : Nat.Coprime t (d / t) := sqf_coprime_div hd htd
    have hmul : d.totient = t.totient * (d / t).totient := by
      conv_lhs => rw [← Nat.mul_div_cancel' htd]
      exact Nat.totient_mul hcop
    have hpos : 0 < t := by
      by_contra h0
      have ht0 : t = 0 := by omega
      rw [ht0, zero_dvd_iff] at htd
      exact hd0 htd
    have htt : (0 : ℝ) < (t.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hpos)
    rw [hmul, Nat.cast_mul, one_div, inv_mul_cancel_left₀ htt.ne']
  rw [Finset.sum_mul, Finset.sum_congr rfl hterm]
  have hbij : ∑ t ∈ d.divisors, ((d / t).totient : ℝ) = ∑ u ∈ d.divisors, (u.totient : ℝ) := by
    refine Finset.sum_bij (fun t _ => d / t) ?_ ?_ ?_ ?_
    · intro t ht
      obtain ⟨htd, _⟩ := Nat.mem_divisors.mp ht
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd htd, hd0⟩
    · intro t1 ht1 t2 ht2 heq
      obtain ⟨h1, _⟩ := Nat.mem_divisors.mp ht1
      obtain ⟨h2, _⟩ := Nat.mem_divisors.mp ht2
      have := congrArg (· * (d / t2)) (Nat.mul_div_cancel' h1)
      have h1' : d * (d / t2) = t1 * (d / t1) * (d / t2) := by
        rw [Nat.mul_div_cancel' h1]
      calc t1 = t1 * (d / t1) / (d / t1) := by
            rw [Nat.mul_div_cancel _ (Nat.div_pos (Nat.le_of_dvd hd_pos h1) (Nat.pos_of_ne_zero (fun h => hd0 (zero_dvd_iff.mp (h ▸ h1)))))]
        _ = d / (d / t1) := by rw [Nat.mul_div_cancel' h1]
        _ = d / (d / t2) := by rw [heq]
        _ = t2 := Nat.div_div_self h2 hd0
    · intro u hu
      obtain ⟨hud, _⟩ := Nat.mem_divisors.mp hu
      exact ⟨d / u, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hud, hd0⟩, Nat.div_div_self hud hd0⟩
    · intro _ _; rfl
  rw [hbij]
  exact_mod_cast Nat.sum_totient d

private lemma primeFactors_mul_prime {r p : ℕ} (hr0 : r ≠ 0) (hp : p.Prime) (_hpr : ¬ p ∣ r) :
    (p * r).primeFactors = insert p r.primeFactors := by
  rw [Nat.primeFactors_mul hp.ne_zero hr0, hp.primeFactors, Finset.singleton_union]

private lemma sum_mu_divisors_sqf {u : ℕ} (hu : Squarefree u) (hu0 : u ≠ 0) :
    ∑ r ∈ u.divisors, (-1 : ℝ) ^ r.primeFactors.card = if u = 1 then 1 else 0 := by
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hu1 : u = 1
    · subst hu1; simp
    · rw [if_neg hu1]
      have hu_gt : 1 < u := by omega
      obtain ⟨p, hp, hpu⟩ := Nat.exists_prime_and_dvd hu_gt.ne'
      let r0 := u / p
      have hpr0 : r0 ≠ 0 := fun h => by
        have := Nat.mul_div_cancel' hpu
        rw [show u / p = r0 from rfl, h, mul_zero] at this
        exact hu0 this.symm
      have hr0_sqf : Squarefree r0 := hu.squarefree_of_dvd (Nat.div_dvd_of_dvd hpu)
      have hr0_lt : r0 < u := Nat.div_lt_self (Nat.pos_of_ne_zero hu0) hp.one_lt
      have hr0_gt1 : r0 ≠ 1 ∨ r0 = 1 := ne_or_eq r0 1
      have hp_ndvd : ¬ p ∣ r0 := fun hd => hp.ne_one (Nat.isUnit_iff.mp (hu p (by
        have := Nat.mul_dvd_mul_left p hd
        rwa [Nat.mul_div_cancel' hpu] at this)))
      have hu_eq : u = p * r0 := (Nat.mul_div_cancel' hpu).symm
      have hdiv_split : u.divisors = r0.divisors ∪ r0.divisors.image (fun d => p * d) := by
        ext d
        simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
        constructor
        · rintro ⟨hdu, _⟩
          by_cases hpd : p ∣ d
          · right
            refine ⟨d / p, ⟨?_, hpr0⟩, Nat.mul_div_cancel' hpd⟩
            have := Nat.mul_dvd_mul_left p (Nat.div_dvd_of_dvd hpd)
            have hdiv : p * (d / p) ∣ p * r0 := by rw [Nat.mul_div_cancel' hpd, ← hu_eq]; exact hdu
            exact (Nat.mul_dvd_mul_iff_left hp.pos).mp hdiv
          · left
            refine ⟨?_, hpr0⟩
            have hcop : Nat.Coprime d p := (hp.coprime_iff_not_dvd.mpr hpd).symm
            exact hcop.dvd_of_dvd_mul_left (hu_eq ▸ hdu)
        · rintro (⟨hdr, _⟩ | ⟨d, ⟨hdr, _⟩, rfl⟩)
          · exact ⟨hdr.trans (Nat.div_dvd_of_dvd hpu), hu0⟩
          · rw [hu_eq]
            exact ⟨mul_dvd_mul_left p hdr, mul_ne_zero hp.ne_zero hpr0⟩
      have hdisj : Disjoint r0.divisors (r0.divisors.image (fun d => p * d)) := by
        rw [Finset.disjoint_left]
        intro d hd1 hd2
        rcases Finset.mem_image.mp hd2 with ⟨d0, _, rfl⟩
        rw [Nat.mem_divisors] at hd1
        exact hp_ndvd ((dvd_mul_right p d0).trans hd1.1)
      have hinj : ∀ d1 ∈ r0.divisors, ∀ d2 ∈ r0.divisors, p * d1 = p * d2 → d1 = d2 :=
        fun d1 _ d2 _ heq => mul_left_cancel₀ hp.ne_zero heq
      have hterm : ∀ d ∈ r0.divisors,
          (-1 : ℝ) ^ (p * d).primeFactors.card = - (-1 : ℝ) ^ d.primeFactors.card := by
        intro d hd
        rw [Nat.mem_divisors] at hd
        have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hpr0 hd.1
        have hndvd_d : ¬ p ∣ d := fun hpd => hp_ndvd (hpd.trans hd.1)
        rw [primeFactors_mul_prime hd0 hp hndvd_d]
        have hp_not_mem : p ∉ d.primeFactors := fun h =>
          hndvd_d (Nat.dvd_of_mem_primeFactors h)
        rw [Finset.card_insert_of_notMem hp_not_mem, pow_succ]
        ring
      rw [hdiv_split, Finset.sum_union hdisj, Finset.sum_image hinj,
        Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
      ring

private lemma coprime_60_iff_30 (m : ℕ) : Nat.Coprime m 60 ↔ Nat.Coprime m 30 := by
  constructor
  · intro h; exact h.coprime_dvd_right (by decide : 30 ∣ 60)
  · intro h
    have h2 : Nat.Coprime m 2 := h.coprime_dvd_right (by decide : 2 ∣ 30)
    simpa [show (60 : ℕ) = 30 * 2 by decide] using h.mul_right h2

private lemma block_count_mod60_dvd (X m r : ℕ) (hm1 : 1 ≤ m) (hm30 : Nat.Coprime m 30)
    (hr : r < 60) :
    X / (60 * m) ≤ ((Finset.Icc 1 X).filter (fun n => n % 60 = r ∧ m ∣ n)).card ∧
    ((Finset.Icc 1 X).filter (fun n => n % 60 = r ∧ m ∣ n)).card ≤ X / (60 * m) + 1 := by
  have hm60 : Nat.Coprime m 60 := (coprime_60_iff_30 m).mpr hm30
  have hm60' : Nat.Coprime 60 m := hm60.symm
  let cr := Nat.chineseRemainder hm60' r 0
  let a0 := cr.val % (60 * m)
  have hMpos : 0 < 60 * m := by positivity
  have ha0_lt : a0 < 60 * m := Nat.mod_lt _ hMpos
  have ha0_mod60 : a0 % 60 = r := by
    have h1 : cr.val % 60 = r % 60 := cr.2.1
    change (cr.val % (60 * m)) % 60 = r
    rw [Nat.mod_mod_of_dvd cr.val (dvd_mul_right 60 m), h1, Nat.mod_eq_of_lt hr]
  have ha0_dvdm : m ∣ a0 := by
    have h1 : cr.val % m = 0 % m := cr.2.2
    rw [Nat.dvd_iff_mod_eq_zero]
    change (cr.val % (60 * m)) % m = 0
    rw [Nat.mod_mod_of_dvd cr.val (dvd_mul_left m 60), h1, Nat.zero_mod]
  have hiff : ∀ n : ℕ, (n % 60 = r ∧ m ∣ n) ↔ n % (60 * m) = a0 := fun n => by
    constructor
    · rintro ⟨hn60, hnm⟩
      have hmod60 : n ≡ a0 [MOD 60] := by change n % 60 = a0 % 60; rw [hn60, ha0_mod60]
      have hmodm : n ≡ a0 [MOD m] := by
        change n % m = a0 % m
        rw [Nat.mod_eq_zero_of_dvd hnm, Nat.mod_eq_zero_of_dvd ha0_dvdm]
      have hmodM : n ≡ a0 [MOD 60 * m] := (Nat.modEq_and_modEq_iff_modEq_mul hm60').mp ⟨hmod60, hmodm⟩
      change n % (60 * m) = a0 % (60 * m) at hmodM
      rwa [Nat.mod_eq_of_lt ha0_lt] at hmodM
    · intro hM
      refine ⟨?_, ?_⟩
      · have : n % 60 = (n % (60 * m)) % 60 := (Nat.mod_mod_of_dvd _ (dvd_mul_right 60 m)).symm
        rw [this, hM, ha0_mod60]
      · have hmodm : n % m = (n % (60 * m)) % m := (Nat.mod_mod_of_dvd _ (dvd_mul_left m 60)).symm
        rw [Nat.dvd_iff_mod_eq_zero, hmodm, hM]
        exact Nat.mod_eq_zero_of_dvd ha0_dvdm
  let B := (Finset.Icc 1 X).filter (fun n => n % 60 = r ∧ m ∣ n)
  let Q := X / (60 * m)
  constructor
  · have hlower_fn : Finset.image (fun q => q * (60 * m) + if a0 = 0 then (60 * m) else a0)
        (Finset.range Q) ⊆ B := by
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨q, hq, rfl⟩
      rw [Finset.mem_range] at hq
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, (hiff _).mpr ?_⟩
      · by_cases ha : a0 = 0
        · simp [ha]; omega
        · simp [ha]; omega
      · have hqX : (q + 1) * (60 * m) ≤ Q * (60 * m) := Nat.mul_le_mul_right _ hq
        have hQX : Q * (60 * m) ≤ X := Nat.div_mul_le_self X (60 * m)
        by_cases ha : a0 = 0
        · simp [ha]
          linarith [add_one_mul q (60 * m), hqX, hQX]
        · simp [ha]
          have ha_le : a0 ≤ 60 * m := ha0_lt.le
          linarith [add_one_mul q (60 * m), hqX, hQX, ha_le]
      · by_cases ha : a0 = 0
        · simp [ha]
        · simp [ha, Nat.add_mod, Nat.mod_eq_of_lt ha0_lt]
    have hinj : Function.Injective (fun q => q * (60 * m) + if a0 = 0 then (60 * m) else a0) := by
      intro q1 q2 heq
      exact mul_right_cancel₀ hMpos.ne' (Nat.add_right_cancel heq)
    calc Q = (Finset.range Q).card := (Finset.card_range Q).symm
      _ = ((Finset.range Q).image _).card := (Finset.card_image_of_injective _ hinj).symm
      _ ≤ B.card := Finset.card_le_card hlower_fn
  · have himg : B.image (fun n => (n - 1) / (60 * m)) ⊆ Finset.range (Q + 1) := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨n, hn, rfl⟩
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Finset.mem_range]
      have : (n - 1) / (60 * m) ≤ X / (60 * m) := Nat.div_le_div_right (by omega)
      omega
    have hinj : ∀ n1 ∈ B, ∀ n2 ∈ B, (n1 - 1) / (60 * m) = (n2 - 1) / (60 * m) → n1 = n2 := by
      intro n1 hn1 n2 hn2 heq
      rw [Finset.mem_filter, Finset.mem_Icc] at hn1 hn2
      have hm1' := (hiff n1).mp hn1.2
      have hm2' := (hiff n2).mp hn2.2
      by_cases ha : a0 = 0
      · have hd1 : (60 * m) ∣ n1 := Nat.dvd_of_mod_eq_zero (by rwa [ha] at hm1')
        have hd2 : (60 * m) ∣ n2 := Nat.dvd_of_mod_eq_zero (by rwa [ha] at hm2')
        obtain ⟨k1, hk1⟩ := hd1
        obtain ⟨k2, hk2⟩ := hd2
        have hk1_pos : 1 ≤ k1 := by
          by_contra hk; have : k1 = 0 := by omega
          rw [this, mul_zero] at hk1; omega
        have hk2_pos : 1 ≤ k2 := by
          by_contra hk; have : k2 = 0 := by omega
          rw [this, mul_zero] at hk2; omega
        have hq1 : (n1 - 1) / (60 * m) = k1 - 1 := by
          rw [hk1]
          have hsub : 60 * m * k1 - 1 = (60 * m) * (k1 - 1) + (60 * m - 1) := by
            conv_lhs => rw [show k1 = (k1 - 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
            omega
          rw [hsub, Nat.mul_add_div hMpos, Nat.div_eq_of_lt (by omega)]; ring
        have hq2 : (n2 - 1) / (60 * m) = k2 - 1 := by
          rw [hk2]
          have hsub : 60 * m * k2 - 1 = (60 * m) * (k2 - 1) + (60 * m - 1) := by
            conv_lhs => rw [show k2 = (k2 - 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
            omega
          rw [hsub, Nat.mul_add_div hMpos, Nat.div_eq_of_lt (by omega)]; ring
        rw [hq1, hq2] at heq
        have hk : k1 = k2 := by omega
        rw [hk1, hk2, hk]
      · have h1pos : 1 ≤ a0 := by omega
        have hn1_eq : n1 = (60 * m) * (n1 / (60 * m)) + a0 := by
          rw [← hm1']; exact (Nat.div_add_mod n1 (60 * m)).symm
        have hn2_eq : n2 = (60 * m) * (n2 / (60 * m)) + a0 := by
          rw [← hm2']; exact (Nat.div_add_mod n2 (60 * m)).symm
        have hdiv0 : (a0 - 1) / (60 * m) = 0 := Nat.div_eq_of_lt (by omega)
        have hq1 : (n1 - 1) / (60 * m) = n1 / (60 * m) := by
          have hsub : n1 - 1 = (60 * m) * (n1 / (60 * m)) + (a0 - 1) := by
            conv_lhs => rw [hn1_eq]
            omega
          rw [hsub, Nat.mul_add_div hMpos, hdiv0]; ring
        have hq2 : (n2 - 1) / (60 * m) = n2 / (60 * m) := by
          have hsub : n2 - 1 = (60 * m) * (n2 / (60 * m)) + (a0 - 1) := by
            conv_lhs => rw [hn2_eq]
            omega
          rw [hsub, Nat.mul_add_div hMpos, hdiv0]; ring
        rw [hq1, hq2] at heq
        rw [hn1_eq, hn2_eq, heq]
    calc B.card = (B.image (fun n => (n - 1) / (60 * m))).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range (Q + 1)).card := Finset.card_le_card himg
      _ = Q + 1 := Finset.card_range (Q + 1)

private lemma block_count_mod60_err (R : Finset ℕ) (hR : ∀ r ∈ R, r < 60)
    (X m : ℕ) (hm1 : 1 ≤ m) (hm30 : Nat.Coprime m 30) :
    |(((Finset.Icc 1 X).filter (fun n => n % 60 ∈ R ∧ m ∣ n)).card : ℝ) -
      (R.card : ℝ) * (X : ℝ) / (60 * (m : ℝ))| ≤ (R.card : ℝ) := by
  let A := Finset.Icc 1 X
  let F : ℕ → Finset ℕ := fun r => A.filter (fun n => n % 60 = r ∧ m ∣ n)
  let B := A.filter (fun n => n % 60 ∈ R ∧ m ∣ n)
  have hB : B = R.biUnion F := by
    ext n
    simp only [B, F, Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨hnA, hnR, hmd⟩
      exact ⟨n % 60, hnR, hnA, rfl, hmd⟩
    · rintro ⟨r, hrR, hnA, rfl, hmd⟩
      exact ⟨hnA, hrR, hmd⟩
  have hdisj : Set.PairwiseDisjoint (R : Set ℕ) F := by
    intro r1 _ r2 _ hne
    exact Finset.disjoint_filter.mpr fun n _ h1 h2 => hne (h1.1.symm.trans h2.1)
  have hcard : B.card = ∑ r ∈ R, (F r).card := by
    rw [hB, Finset.card_biUnion hdisj]
  have herr : ∀ r ∈ R, |((F r).card : ℝ) - (X : ℝ) / (60 * (m : ℝ))| ≤ 1 := fun r hr => by
    obtain ⟨hl, hu⟩ := block_count_mod60_dvd X m r hm1 hm30 (hR r hr)
    have hMpos : 0 < 60 * m := by omega
    have hq1 : (X / (60 * m) : ℕ) * (60 * m) ≤ X := Nat.div_mul_le_self X (60 * m)
    have hq2 : X < (X / (60 * m) + 1) * (60 * m) := by linarith [Nat.lt_mul_div_succ X hMpos]
    have hq1R : ((X / (60 * m) : ℕ) : ℝ) * (60 * (m : ℝ)) ≤ (X : ℝ) := by exact_mod_cast hq1
    have hq2R : (X : ℝ) < (((X / (60 * m) : ℕ) : ℝ) + 1) * (60 * (m : ℝ)) := by exact_mod_cast hq2
    have hdiv_lo : (X : ℝ) / (60 * (m : ℝ)) - 1 < ((X / (60 * m) : ℕ) : ℝ) := by
      have : (X : ℝ) / (60 * (m : ℝ)) < ((X / (60 * m) : ℕ) : ℝ) + 1 :=
        (div_lt_iff₀ (by positivity)).mpr hq2R
      linarith
    have hdiv_hi : ((X / (60 * m) : ℕ) : ℝ) ≤ (X : ℝ) / (60 * (m : ℝ)) :=
      (le_div_iff₀ (by positivity)).mpr hq1R
    have hlR : ((X / (60 * m) : ℕ) : ℝ) ≤ ((F r).card : ℝ) := by exact_mod_cast hl
    have huR : ((F r).card : ℝ) ≤ ((X / (60 * m) : ℕ) : ℝ) + 1 := by exact_mod_cast hu
    rw [abs_le]
    constructor <;> linarith
  have hcast : (B.card : ℝ) - (R.card : ℝ) * (X : ℝ) / (60 * (m : ℝ)) =
      ∑ r ∈ R, (((F r).card : ℝ) - (X : ℝ) / (60 * (m : ℝ))) := by
    rw [hcard, Nat.cast_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hcast]
  calc |∑ r ∈ R, (((F r).card : ℝ) - (X : ℝ) / (60 * (m : ℝ)))|
      ≤ ∑ r ∈ R, |((F r).card : ℝ) - (X : ℝ) / (60 * (m : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ R, (1 : ℝ) := Finset.sum_le_sum herr
    _ = (R.card : ℝ) := by simp

private lemma selberg_pi60_le (R : Finset ℕ) (hR : ∀ r ∈ R, r < 60) (X z : ℕ) (hz : 1 ≤ z) :
    (((Finset.Icc 1 X).filter (fun p => p.Prime ∧ p % 60 ∈ R)).card : ℝ) ≤
      (z : ℝ) +
      (R.card : ℝ) * (X : ℝ) / (60 * ∑ d ∈ (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30),
        (1 / (d.totient : ℝ))) +
      (R.card : ℝ) * (((Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)).card : ℝ) ^ 2 := by
  let D := (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)
  let L : ℝ := ∑ l ∈ D, (1 / (l.totient : ℝ))
  let mu : ℕ → ℝ := fun n => (-1 : ℝ) ^ n.primeFactors.card
  let lam : ℕ → ℝ := fun d =>
    (mu d * (d : ℝ)) / (L * (d.totient : ℝ)) *
      ∑ m ∈ D.filter (fun m => d * m ≤ z ∧ Nat.Coprime m d), (1 / (m.totient : ℝ))
  have h1D : 1 ∈ D := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_refl 1, hz⟩, squarefree_one, Nat.coprime_one_left 30⟩
  have hD_pos : ∀ d ∈ D, 1 ≤ d ∧ d ≤ z ∧ Squarefree d ∧ Nat.Coprime d 30 := fun d hd => by
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    exact ⟨hd.1.1, hd.1.2, hd.2.1, hd.2.2⟩
  have hL_ge : 1 ≤ L := by
    have hterm : ∀ l ∈ D, (0 : ℝ) ≤ 1 / (l.totient : ℝ) := fun l _ => by positivity
    calc (1 : ℝ) = 1 / ((1 : ℕ).totient : ℝ) := by simp
      _ ≤ ∑ l ∈ D, (1 / (l.totient : ℝ)) := Finset.single_le_sum hterm h1D
  have hL_pos : 0 < L := lt_of_lt_of_le one_pos hL_ge
  have hlam1 : lam 1 = 1 := by
    have hf : D.filter (fun m => 1 * m ≤ z ∧ Nat.Coprime m 1) = D := by
      ext m; simp only [Finset.mem_filter, one_mul, Nat.coprime_one_right_eq_true, and_true]
      constructor
      · intro hm; exact hm.1
      · intro hm; exact ⟨hm, (hD_pos m hm).2.1⟩
    simp only [lam, hf, Nat.primeFactors_one, Finset.card_empty, pow_zero, Nat.cast_one,
      mul_one, Nat.totient_one, mu]
    rw [one_div, inv_mul_cancel₀ hL_pos.ne']
  have hlam_abs : ∀ d ∈ D, |lam d| ≤ 1 := fun d hd => by
    obtain ⟨hd1, hdz, hdSqf, hd30⟩ := hD_pos d hd
    have hd0 : d ≠ 0 := by omega
    have hdt_pos : (0 : ℝ) < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd1)
    let Mset := D.filter (fun m => d * m ≤ z ∧ Nat.Coprime m d)
    have hprod_le_L : (∑ t ∈ d.divisors, (1 / (t.totient : ℝ))) *
        (∑ m ∈ Mset, (1 / (m.totient : ℝ))) ≤ L := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_product']
      let Pset := d.divisors ×ˢ Mset
      have hmap : Pset.image (fun x => x.1 * x.2) ⊆ D := by
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨⟨t, m⟩, htm, rfl⟩
        rw [Finset.mem_product, Nat.mem_divisors] at htm
        rcases htm with ⟨⟨htd, _⟩, hmM⟩
        rw [Finset.mem_filter] at hmM
        rcases hmM with ⟨hmD, hdmz, hcmd⟩
        obtain ⟨hm1, _, hmSqf, hm30⟩ := hD_pos m hmD
        have ht1 : 1 ≤ t := by
          by_contra h0; have : t = 0 := by omega
          rw [this, zero_dvd_iff] at htd; exact hd0 htd
        have htSqf : Squarefree t := hdSqf.squarefree_of_dvd htd
        have ht30 : Nat.Coprime t 30 := hd30.coprime_dvd_left htd
        have hctm : Nat.Coprime t m := hcmd.symm.coprime_dvd_left htd
        rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨Nat.mul_pos ht1 hm1, ?_⟩, ?_, ht30.mul_left hm30⟩
        · exact (Nat.mul_le_mul_right m (Nat.le_of_dvd hd1 htd)).trans hdmz
        · exact (Nat.squarefree_mul hctm).mpr ⟨htSqf, hmSqf⟩
      have hinj : ∀ x ∈ Pset, ∀ y ∈ Pset, x.1 * x.2 = y.1 * y.2 → x = y := by
        rintro ⟨t1, m1⟩ hx ⟨t2, m2⟩ hy heq
        rw [Finset.mem_product, Nat.mem_divisors] at hx hy
        have h1d := hx.1.1
        have h2d := hy.1.1
        rw [Finset.mem_filter] at hx hy
        have hc1 : Nat.Coprime d m1 := hx.2.2.2.symm
        have hc2 : Nat.Coprime d m2 := hy.2.2.2.symm
        have hg1 : Nat.gcd d (t1 * m1) = t1 := by
          rw [Nat.Coprime.gcd_mul_right_cancel_right t1 hc1.symm, Nat.gcd_eq_right h1d]
        have hg2 : Nat.gcd d (t2 * m2) = t2 := by
          rw [Nat.Coprime.gcd_mul_right_cancel_right t2 hc2.symm, Nat.gcd_eq_right h2d]
        have ht_eq : t1 = t2 := by rw [← hg1, heq, hg2]
        have ht1_pos : 0 < t1 := by
          by_contra h0; have : t1 = 0 := by omega
          rw [this, zero_dvd_iff] at h1d; exact hd0 h1d
        have hm_eq : m1 = m2 := by
          rw [ht_eq] at heq
          have : 0 < t2 := ht_eq ▸ ht1_pos
          exact mul_left_cancel₀ this.ne' heq
        exact Prod.ext ht_eq hm_eq
      have hterm_eq : ∀ x ∈ Pset, (1 / (x.1.totient : ℝ)) * (1 / (x.2.totient : ℝ)) =
          1 / ((x.1 * x.2).totient : ℝ) := fun ⟨t, m⟩ htm => by
        rw [Finset.mem_product, Nat.mem_divisors, Finset.mem_filter] at htm
        have hcop : Nat.Coprime t m := htm.2.2.2.symm.coprime_dvd_left htm.1.1
        rw [Nat.totient_mul hcop]; push_cast; ring
      calc ∑ x ∈ Pset, (1 / (x.1.totient : ℝ)) * (1 / (x.2.totient : ℝ))
          = ∑ x ∈ Pset, (1 / ((x.1 * x.2).totient : ℝ)) := Finset.sum_congr rfl hterm_eq
        _ = ∑ u ∈ Pset.image (fun x => x.1 * x.2), (1 / (u.totient : ℝ)) :=
            (Finset.sum_image (f := fun u : ℕ => 1 / (u.totient : ℝ)) hinj).symm
        _ ≤ ∑ u ∈ D, (1 / (u.totient : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hmap fun _ _ _ => by positivity
    rw [sum_inv_totient_divisors hdSqf hd0] at hprod_le_L
    have hmu_abs : |mu d| = 1 := by simp [mu]
    have hsum_nn : 0 ≤ ∑ m ∈ Mset, (1 / (m.totient : ℝ)) := Finset.sum_nonneg fun _ _ => by positivity
    have hlam_abs_eq : |lam d| = ((d : ℝ) / (L * (d.totient : ℝ))) *
        ∑ m ∈ Mset, (1 / (m.totient : ℝ)) := by
      simp only [lam, abs_mul, abs_div, hmu_abs, one_mul]
      have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by positivity
      rw [abs_of_nonneg hd_nn, abs_of_nonneg hL_pos.le,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d.totient : ℝ)), abs_of_nonneg hsum_nn]
    rw [hlam_abs_eq]
    have h1 : ((d : ℝ) / (L * (d.totient : ℝ))) * ∑ m ∈ Mset, (1 / (m.totient : ℝ)) =
        (((d : ℝ) / (d.totient : ℝ)) * ∑ m ∈ Mset, (1 / (m.totient : ℝ))) / L := by ring
    rw [h1]
    exact (div_le_one hL_pos).mpr hprod_le_L
  have hdiag : ∀ l ∈ D, ∑ d ∈ D.filter (fun d => l ∣ d), lam d / (d : ℝ) =
      mu l / (L * (l.totient : ℝ)) := fun l hl => by
    obtain ⟨hl1, hlz, hlSqf, hl30⟩ := hD_pos l hl
    have hl0 : l ≠ 0 := by omega
    have hlt_pos : (0 : ℝ) < (l.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hl1)
    let P_pairs := (D ×ˢ D).filter (fun x => l * (x.1 * x.2) ≤ z ∧
      Nat.Coprime x.1 l ∧ Nat.Coprime x.2 (l * x.1))
    let S_inner := ∑ d ∈ D.filter (fun d => l ∣ d), lam d / (d : ℝ)
    have hstep1 : S_inner = (mu l / (L * (l.totient : ℝ))) *
        ∑ x ∈ P_pairs, mu x.1 / ((x.1.totient : ℝ) * (x.2.totient : ℝ)) := by
      have hbij : ∑ d ∈ D.filter (fun d => l ∣ d), lam d / (d : ℝ) =
          ∑ r ∈ D.filter (fun r => l * r ≤ z ∧ Nat.Coprime r l),
            (mu (l * r) / (L * ((l * r).totient : ℝ))) *
              ∑ m ∈ D.filter (fun m => l * r * m ≤ z ∧ Nat.Coprime m (l * r)),
                (1 / (m.totient : ℝ)) := by
        refine Finset.sum_bij (fun d _ => d / l) ?_ ?_ ?_ ?_
        · intro d hd
          rw [Finset.mem_filter] at hd
          rcases hd with ⟨hdD, hld⟩
          obtain ⟨hd1, hdz, hdSqf, hd30⟩ := hD_pos d hdD
          have hr1 : 1 ≤ d / l := Nat.div_pos (Nat.le_of_dvd hd1 hld) hl1
          have hrz : d / l ≤ z := (Nat.div_le_self d l).trans hdz
          have hrSqf : Squarefree (d / l) := hdSqf.squarefree_of_dvd (Nat.div_dvd_of_dvd hld)
          have hr30 : Nat.Coprime (d / l) 30 := hd30.coprime_dvd_left (Nat.div_dvd_of_dvd hld)
          have hcl : Nat.Coprime (d / l) l := (sqf_coprime_div hdSqf hld).symm
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr1, hrz⟩, hrSqf, hr30⟩, ?_, hcl⟩
          rw [Nat.mul_div_cancel' hld]; exact hdz
        · intro d1 hd1 d2 hd2 heq
          rw [Finset.mem_filter] at hd1 hd2
          have := congrArg (fun x => l * x) heq
          simpa [Nat.mul_div_cancel' hd1.2, Nat.mul_div_cancel' hd2.2] using this
        · intro r hr
          rw [Finset.mem_filter] at hr
          rcases hr with ⟨hrD, hlr_z, hcl⟩
          obtain ⟨hr1, _, hrSqf, hr30⟩ := hD_pos r hrD
          refine ⟨l * r, ?_, Nat.mul_div_cancel_left r hl1⟩
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hl1 hr1, hlr_z⟩,
            (Nat.squarefree_mul hcl.symm).mpr ⟨hlSqf, hrSqf⟩, hl30.mul_left hr30⟩, dvd_mul_right l r⟩
        · intro d hd
          rw [Finset.mem_filter] at hd
          obtain ⟨hd1, _, _, _⟩ := hD_pos d hd.1
          have hdl : l * (d / l) = d := Nat.mul_div_cancel' hd.2
          have hdt_pos : (0 : ℝ) < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd1)
          have hd_ne : (d : ℝ) ≠ 0 := by positivity
          dsimp only [lam]
          rw [hdl]
          field_simp [hd_ne, hL_pos.ne', hdt_pos.ne']
      change S_inner = _ at hbij
      rw [hbij]
      have hterm_r : ∀ r ∈ D.filter (fun r => l * r ≤ z ∧ Nat.Coprime r l),
          (mu (l * r) / (L * ((l * r).totient : ℝ))) *
            ∑ m ∈ D.filter (fun m => l * r * m ≤ z ∧ Nat.Coprime m (l * r)), (1 / (m.totient : ℝ)) =
          (mu l / (L * (l.totient : ℝ))) *
            ∑ m ∈ D.filter (fun m => l * r * m ≤ z ∧ Nat.Coprime m (l * r)),
              (mu r / ((r.totient : ℝ) * (m.totient : ℝ))) := by
        intro r hr
        rw [Finset.mem_filter] at hr
        rcases hr with ⟨hrD, _, hrl⟩
        obtain ⟨hr1, _, _, _⟩ := hD_pos r hrD
        have hmu_lr : mu (l * r) = mu l * mu r := by
          have hr0 : r ≠ 0 := by omega
          dsimp only [mu]
          rw [Nat.primeFactors_mul hl0 hr0,
            Finset.card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hrl.symm), pow_add]
        have htot_lr : (l * r).totient = l.totient * r.totient := Nat.totient_mul hrl.symm
        rw [hmu_lr, htot_lr]
        simp_rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [Finset.mem_filter] at hm
        obtain ⟨hm1, _, _, _⟩ := hD_pos m hm.1
        push_cast
        have hrt_pos : (0 : ℝ) < (r.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr1)
        have hmt_pos : (0 : ℝ) < (m.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hm1)
        field_simp [hL_pos.ne', hlt_pos.ne', hrt_pos.ne', hmt_pos.ne']
      rw [Finset.sum_congr rfl hterm_r, ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_sigma']
      refine Finset.sum_bij (fun x _ => (x.1, x.2)) ?_ ?_ ?_ ?_
      · intro x hx
        obtain ⟨hx1, hx2⟩ := Finset.mem_sigma.mp hx
        obtain ⟨hx1D, _, hx1_cop⟩ := Finset.mem_filter.mp hx1
        obtain ⟨hx2D, hx2_mul, hx2_cop⟩ := Finset.mem_filter.mp hx2
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx1D, hx2D⟩,
          by simpa [mul_assoc] using hx2_mul, hx1_cop, hx2_cop⟩
      · rintro ⟨r1, m1⟩ _ ⟨r2, m2⟩ _ heq
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rfl
      · rintro ⟨r, m⟩ hrm
        rw [Finset.mem_filter, Finset.mem_product] at hrm
        obtain ⟨hm1, _, _, _⟩ := hD_pos m hrm.1.2
        have hlr : l * r ≤ l * (r * m) := Nat.mul_le_mul_left l (Nat.le_mul_of_pos_right r hm1)
        refine ⟨Sigma.mk r m, Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨hrm.1.1, hlr.trans hrm.2.1, hrm.2.2.1⟩,
          Finset.mem_filter.mpr ⟨hrm.1.2, by simpa [mul_assoc] using hrm.2.1, hrm.2.2.2⟩⟩, rfl⟩
      · intro x _; rfl
    have hstep2 : ∑ x ∈ P_pairs, mu x.1 / ((x.1.totient : ℝ) * (x.2.totient : ℝ)) =
        ∑ u ∈ D.filter (fun u => l * u ≤ z ∧ Nat.Coprime u l),
          (1 / (u.totient : ℝ)) * ∑ r ∈ u.divisors, mu r := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_sigma']
      refine Finset.sum_bij (fun x _ => Sigma.mk (x.1 * x.2) x.1) ?_ ?_ ?_ ?_
      · rintro ⟨r, m⟩ hrm
        rw [Finset.mem_filter, Finset.mem_product] at hrm
        obtain ⟨hr1, _, hrSqf, hr30⟩ := hD_pos r hrm.1.1
        obtain ⟨hm1, _, hmSqf, hm30⟩ := hD_pos m hrm.1.2
        have hcml : Nat.Coprime m l := hrm.2.2.2.coprime_dvd_right (dvd_mul_right l r)
        have hcmr : Nat.Coprime m r := hrm.2.2.2.coprime_dvd_right (dvd_mul_left r l)
        have hrmD : r * m ∈ D := Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hr1 hm1,
            (Nat.le_mul_of_pos_left (r * m) hl1).trans hrm.2.1⟩,
           (Nat.squarefree_mul hcmr.symm).mpr ⟨hrSqf, hmSqf⟩, hr30.mul_left hm30⟩
        exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨hrmD, hrm.2.1, hrm.2.2.1.mul_left hcml⟩,
          Nat.mem_divisors.mpr ⟨dvd_mul_right r m, (Nat.mul_pos hr1 hm1).ne'⟩⟩
      · rintro ⟨r1, m1⟩ h1 ⟨r2, m2⟩ h2 heq
        rw [Finset.mem_filter, Finset.mem_product] at h1 h2
        obtain ⟨hr1, _, _, _⟩ := hD_pos r1 h1.1.1
        have hr_eq : r1 = r2 := congrArg (fun x : Σ _ : ℕ, ℕ => x.2) heq
        have hmul_eq : r1 * m1 = r2 * m2 := congrArg Sigma.fst heq
        rw [hr_eq] at hmul_eq
        have hr2_pos : 0 < r2 := by omega
        exact Prod.ext hr_eq (mul_left_cancel₀ hr2_pos.ne' hmul_eq)
      · rintro ⟨u, r⟩ hur
        rw [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hur
        rcases hur with ⟨⟨huD, hluz, hcul⟩, hru, hu0⟩
        obtain ⟨hu1, huz, huSqf, hu30⟩ := hD_pos u huD
        have hr1 : 1 ≤ r := by
          by_contra h0; have : r = 0 := by omega
          rw [this, zero_dvd_iff] at hru; exact hu0 hru
        have hm1 : 1 ≤ u / r := Nat.div_pos (Nat.le_of_dvd hu1 hru) hr1
        have hrD : r ∈ D := Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hr1, (Nat.le_of_dvd hu1 hru).trans huz⟩,
           huSqf.squarefree_of_dvd hru, hu30.coprime_dvd_left hru⟩
        have hmD : u / r ∈ D := Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hm1, (Nat.div_le_self u r).trans huz⟩,
           huSqf.squarefree_of_dvd (Nat.div_dvd_of_dvd hru),
           hu30.coprime_dvd_left (Nat.div_dvd_of_dvd hru)⟩
        have hcr_m : Nat.Coprime (u / r) r := (sqf_coprime_div huSqf hru).symm
        have hcr_l : Nat.Coprime r l := hcul.coprime_dvd_left hru
        have hcm_l : Nat.Coprime (u / r) l := hcul.coprime_dvd_left (Nat.div_dvd_of_dvd hru)
        refine ⟨(r, u / r), ?_, Sigma.ext (Nat.mul_div_cancel' hru) (by simp)⟩
        rw [Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨hrD, hmD⟩, ?_, hcr_l, hcm_l.mul_right hcr_m⟩
        rwa [Nat.mul_div_cancel' hru]
      · rintro ⟨r, m⟩ hrm
        rw [Finset.mem_filter, Finset.mem_product] at hrm
        have hcmr : Nat.Coprime r m := (hrm.2.2.2.coprime_dvd_right (dvd_mul_left r l)).symm
        rw [Nat.totient_mul hcmr]; push_cast; ring
    have hstep3 : ∑ u ∈ D.filter (fun u => l * u ≤ z ∧ Nat.Coprime u l),
        (1 / (u.totient : ℝ)) * ∑ r ∈ u.divisors, mu r = 1 := by
      have hterm_u : ∀ u ∈ D.filter (fun u => l * u ≤ z ∧ Nat.Coprime u l),
          (1 / (u.totient : ℝ)) * ∑ r ∈ u.divisors, mu r = if u = 1 then (1 : ℝ) else 0 := by
        intro u hu
        rw [Finset.mem_filter] at hu
        obtain ⟨hu1, _, huSqf, _⟩ := hD_pos u hu.1
        rw [sum_mu_divisors_sqf huSqf (by omega)]
        by_cases hu_eq : u = 1
        · subst hu_eq; simp
        · simp [hu_eq]
      rw [Finset.sum_congr rfl hterm_u, Finset.sum_ite_eq']
      have h1mem : 1 ∈ D.filter (fun u => l * u ≤ z ∧ Nat.Coprime u l) :=
        Finset.mem_filter.mpr ⟨h1D, by simpa using hlz, Nat.coprime_one_left l⟩
      simp [h1mem]
    change S_inner = mu l / (L * (l.totient : ℝ))
    rw [hstep1, hstep2, hstep3, mul_one]
  let P60 := (Finset.Icc 1 X).filter (fun p => p.Prime ∧ p % 60 ∈ R)
  let A60 := (Finset.Icc 1 X).filter (fun n => n % 60 ∈ R)
  have hP_split : P60.card ≤ z + (P60.filter (fun p => z < p)).card := by
    have hsub : P60 = P60.filter (fun p => p ≤ z) ∪ P60.filter (fun p => z < p) := by
      ext p
      simp only [Finset.mem_union, Finset.mem_filter]
      by_cases hpz : p ≤ z
      · simp [hpz, show ¬ z < p by omega]
      · simp [hpz, show z < p by omega]
    have hle_z : (P60.filter (fun p => p ≤ z)).card ≤ z := by
      have hs : P60.filter (fun p => p ≤ z) ⊆ Finset.Icc 1 z := fun p hp => by
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hp
        exact Finset.mem_Icc.mpr ⟨hp.1.1.1, hp.2⟩
      exact (Finset.card_le_card hs).trans (by simp)
    have hcard_le := Finset.card_union_le (P60.filter (fun p => p ≤ z)) (P60.filter (fun p => z < p))
    rw [← hsub] at hcard_le
    omega
  have hP_le_R : ((P60.filter (fun p => z < p)).card : ℝ) ≤
      ∑ n ∈ A60, (∑ d ∈ D, (if d ∣ n then lam d else 0)) ^ 2 := by
    have hP_sub : P60.filter (fun p => z < p) ⊆ A60 := fun p hp => by
      rw [Finset.mem_filter, Finset.mem_filter] at hp
      exact Finset.mem_filter.mpr ⟨hp.1.1, hp.1.2.2⟩
    have hwt : ∀ n ∈ P60.filter (fun p => z < p),
        (1 : ℝ) ≤ (∑ d ∈ D, (if d ∣ n then lam d else 0)) ^ 2 := fun p hp => by
      rw [Finset.mem_filter, Finset.mem_filter] at hp
      have hp_prime : p.Prime := hp.1.2.1
      have hzp : z < p := hp.2
      have hterm : ∀ d ∈ D, (if d ∣ p then lam d else 0) = (if d = 1 then (1 : ℝ) else 0) := by
        intro d hd
        obtain ⟨hd1, hdz, _, _⟩ := hD_pos d hd
        by_cases hdp : d ∣ p
        · have hd1_eq : d = 1 := by
            rcases (Nat.dvd_prime hp_prime).mp hdp with rfl | rfl
            · rfl
            · omega
          rw [hd1_eq]; simp [hlam1]
        · have hdne : d ≠ 1 := fun h => hdp (h ▸ one_dvd p)
          simp [hdp, hdne]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
      simp [h1D]
    calc ((P60.filter (fun p => z < p)).card : ℝ)
        = ∑ _n ∈ P60.filter (fun p => z < p), (1 : ℝ) := by simp
      _ ≤ ∑ n ∈ P60.filter (fun p => z < p), (∑ d ∈ D, (if d ∣ n then lam d else 0)) ^ 2 :=
          Finset.sum_le_sum hwt
      _ ≤ ∑ n ∈ A60, (∑ d ∈ D, (if d ∣ n then lam d else 0)) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hP_sub fun _ _ _ => sq_nonneg _
  have hQ_expand : ∑ n ∈ A60, (∑ d ∈ D, (if d ∣ n then lam d else 0)) ^ 2 =
      ∑ d1 ∈ D, ∑ d2 ∈ D, lam d1 * lam d2 *
        ((A60.filter (fun n => Nat.lcm d1 d2 ∣ n)).card : ℝ) := by
    have hsq : ∀ n : ℕ, (∑ d ∈ D, (if d ∣ n then lam d else 0)) ^ 2 =
        ∑ d1 ∈ D, ∑ d2 ∈ D, (if Nat.lcm d1 d2 ∣ n then lam d1 * lam d2 else 0) := fun n => by
      rw [sq, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d1 _ => Finset.sum_congr rfl fun d2 _ => ?_
      by_cases h1 : d1 ∣ n <;> by_cases h2 : d2 ∣ n <;> simp [h1, h2, Nat.lcm_dvd_iff]
    rw [Finset.sum_congr rfl (fun n _ => hsq n), Finset.sum_comm]
    refine Finset.sum_congr rfl fun d1 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d2 _ => ?_
    rw [← Finset.sum_filter]
    simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hQ_bound : ∑ d1 ∈ D, ∑ d2 ∈ D, lam d1 * lam d2 *
      ((A60.filter (fun n => Nat.lcm d1 d2 ∣ n)).card : ℝ) ≤
      (R.card : ℝ) * (X : ℝ) / 60 * (∑ d1 ∈ D, ∑ d2 ∈ D, (lam d1 * lam d2) / (Nat.lcm d1 d2 : ℝ)) +
      (R.card : ℝ) * (D.card : ℝ) ^ 2 := by
    have hpair : ∀ d1 ∈ D, ∀ d2 ∈ D,
        lam d1 * lam d2 * ((A60.filter (fun n => Nat.lcm d1 d2 ∣ n)).card : ℝ) ≤
        (R.card : ℝ) * (X : ℝ) / 60 * ((lam d1 * lam d2) / (Nat.lcm d1 d2 : ℝ)) + (R.card : ℝ) := by
      intro d1 hd1 d2 hd2
      obtain ⟨h11, _, _, h130⟩ := hD_pos d1 hd1
      obtain ⟨h21, _, _, h230⟩ := hD_pos d2 hd2
      have hm1 : 1 ≤ Nat.lcm d1 d2 := Nat.one_le_iff_ne_zero.mpr (Nat.lcm_ne_zero (by omega) (by omega))
      have hm30 : Nat.Coprime (Nat.lcm d1 d2) 30 := (h130.mul_left h230).coprime_dvd_left (Nat.lcm_dvd_mul d1 d2)
      have herr := block_count_mod60_err R hR X (Nat.lcm d1 d2) hm1 hm30
      have hA_eq : A60.filter (fun n => Nat.lcm d1 d2 ∣ n) =
          (Finset.Icc 1 X).filter (fun n => n % 60 ∈ R ∧ Nat.lcm d1 d2 ∣ n) := by
        ext n; simp only [A60, Finset.mem_filter]; tauto
      rw [hA_eq]
      have hlam_p : |lam d1 * lam d2| ≤ 1 := by
        rw [abs_mul]; nlinarith [hlam_abs d1 hd1, hlam_abs d2 hd2, abs_nonneg (lam d1), abs_nonneg (lam d2)]
      let err := (((Finset.Icc 1 X).filter (fun n => n % 60 ∈ R ∧ Nat.lcm d1 d2 ∣ n)).card : ℝ) -
        (R.card : ℝ) * (X : ℝ) / (60 * (Nat.lcm d1 d2 : ℝ))
      have herr_mul : lam d1 * lam d2 * err ≤ (R.card : ℝ) := by
        have h1 : lam d1 * lam d2 * err ≤ |lam d1 * lam d2| * |err| := by
          rw [← abs_mul]; exact le_abs_self _
        have h2 : |lam d1 * lam d2| * |err| ≤ 1 * (R.card : ℝ) :=
          mul_le_mul hlam_p herr (abs_nonneg _) (by positivity)
        linarith
      have hsub_eq : lam d1 * lam d2 * (((Finset.Icc 1 X).filter (fun n =>
          n % 60 ∈ R ∧ Nat.lcm d1 d2 ∣ n)).card : ℝ) -
          (R.card : ℝ) * (X : ℝ) / 60 * ((lam d1 * lam d2) / (Nat.lcm d1 d2 : ℝ)) = lam d1 * lam d2 * err := by
        dsimp only [err]; ring
      linarith [hsub_eq, herr_mul]
    calc ∑ d1 ∈ D, ∑ d2 ∈ D, lam d1 * lam d2 * ((A60.filter (fun n => Nat.lcm d1 d2 ∣ n)).card : ℝ)
        ≤ ∑ d1 ∈ D, ∑ d2 ∈ D, ((R.card : ℝ) * (X : ℝ) / 60 * ((lam d1 * lam d2) / (Nat.lcm d1 d2 : ℝ)) + (R.card : ℝ)) :=
          Finset.sum_le_sum fun d1 hd1 => Finset.sum_le_sum fun d2 hd2 => hpair d1 hd1 d2 hd2
      _ = (R.card : ℝ) * (X : ℝ) / 60 * (∑ d1 ∈ D, ∑ d2 ∈ D, (lam d1 * lam d2) / (Nat.lcm d1 d2 : ℝ)) +
            (R.card : ℝ) * (D.card : ℝ) ^ 2 := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
          ring
  have hQ_eval : ∑ d1 ∈ D, ∑ d2 ∈ D, (lam d1 * lam d2) / (Nat.lcm d1 d2 : ℝ) = 1 / L := by
    have hsplit_lcm : ∀ d1 ∈ D, ∀ d2 ∈ D,
        (lam d1 * lam d2) / (Nat.lcm d1 d2 : ℝ) =
        ∑ l ∈ D, (if l ∣ d1 ∧ l ∣ d2 then
          (l.totient : ℝ) * (lam d1 / (d1 : ℝ)) * (lam d2 / (d2 : ℝ)) else 0) := by
      intro d1 hd1 d2 hd2
      obtain ⟨h11, h1z, h1Sqf, h130⟩ := hD_pos d1 hd1
      obtain ⟨h21, _, _, _⟩ := hD_pos d2 hd2
      have hgcd_ne0 : Nat.gcd d1 d2 ≠ 0 := Nat.gcd_ne_zero_left (by omega)
      have hgcd_lcm : (Nat.gcd d1 d2 : ℝ) * (Nat.lcm d1 d2 : ℝ) = (d1 : ℝ) * (d2 : ℝ) := by
        exact_mod_cast Nat.gcd_mul_lcm d1 d2
      have hd1_ne0 : (d1 : ℝ) ≠ 0 := by positivity
      have hd2_ne0 : (d2 : ℝ) ≠ 0 := by positivity
      have hlcm_ne0 : (Nat.lcm d1 d2 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.lcm_ne_zero (by omega) (by omega))
      have h1 : (lam d1 * lam d2) / (Nat.lcm d1 d2 : ℝ) =
          (Nat.gcd d1 d2 : ℝ) * ((lam d1 / (d1 : ℝ)) * (lam d2 / (d2 : ℝ))) := by
        field_simp [hlcm_ne0, hd1_ne0, hd2_ne0]
        linear_combination (lam d1 * lam d2) * hgcd_lcm.symm
      rw [h1]
      have hdiv_eq : (Nat.gcd d1 d2).divisors = D.filter (fun l => l ∣ d1 ∧ l ∣ d2) := by
        ext l
        rw [Nat.mem_divisors, Nat.dvd_gcd_iff, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hl_d1, hl_d2⟩, _⟩
          have hl1 : 1 ≤ l := by
            by_contra h0; have : l = 0 := by omega
            rw [this, zero_dvd_iff] at hl_d1; omega
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hl1, (Nat.le_of_dvd h11 hl_d1).trans h1z⟩,
            h1Sqf.squarefree_of_dvd hl_d1, h130.coprime_dvd_left hl_d1⟩, hl_d1, hl_d2⟩
        · rintro ⟨_, hl_d1, hl_d2⟩
          exact ⟨⟨hl_d1, hl_d2⟩, hgcd_ne0⟩
      have htot : (Nat.gcd d1 d2 : ℝ) = ∑ l ∈ D.filter (fun l => l ∣ d1 ∧ l ∣ d2), (l.totient : ℝ) := by
        rw [← hdiv_eq]; exact_mod_cast (Nat.sum_totient (Nat.gcd d1 d2)).symm
      rw [htot, Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun d1 hd1 => Finset.sum_congr rfl fun d2 hd2 => hsplit_lcm d1 hd1 d2 hd2]
    have hswap1 : (∑ d1 ∈ D, ∑ d2 ∈ D, ∑ l ∈ D, (if l ∣ d1 ∧ l ∣ d2 then
        (l.totient : ℝ) * (lam d1 / (d1 : ℝ)) * (lam d2 / (d2 : ℝ)) else 0)) =
        ∑ l ∈ D, (l.totient : ℝ) * (∑ d1 ∈ D.filter (fun d => l ∣ d), lam d1 / (d1 : ℝ)) *
          (∑ d2 ∈ D.filter (fun d => l ∣ d), lam d2 / (d2 : ℝ)) := by
      have h1 : ∀ d1 ∈ D, (∑ d2 ∈ D, ∑ l ∈ D, (if l ∣ d1 ∧ l ∣ d2 then
          (l.totient : ℝ) * (lam d1 / (d1 : ℝ)) * (lam d2 / (d2 : ℝ)) else 0)) =
          ∑ l ∈ D, (if l ∣ d1 then (l.totient : ℝ) * (lam d1 / (d1 : ℝ)) *
            ∑ d2 ∈ D.filter (fun d => l ∣ d), lam d2 / (d2 : ℝ) else 0) := by
        intro d1 _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        by_cases hld1 : l ∣ d1
        · simp only [hld1, true_and, ↓reduceIte, Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun d2 _ => ?_
          split_ifs <;> ring
        · simp only [hld1, false_and, ↓reduceIte, Finset.sum_const_zero]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Finset.sum_filter, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [hswap1]
    have hterm_l : ∀ l ∈ D,
        (l.totient : ℝ) * (∑ d1 ∈ D.filter (fun d => l ∣ d), lam d1 / (d1 : ℝ)) *
          (∑ d2 ∈ D.filter (fun d => l ∣ d), lam d2 / (d2 : ℝ)) =
        (1 / L ^ 2) * (1 / (l.totient : ℝ)) := fun l hl => by
      obtain ⟨hl1, _, _, _⟩ := hD_pos l hl
      have hlt_pos : (0 : ℝ) < (l.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hl1)
      rw [hdiag l hl]
      have hmu2 : mu l * mu l = 1 := by simp [mu, ← pow_add, ← two_mul]
      calc (l.totient : ℝ) * (mu l / (L * (l.totient : ℝ))) * (mu l / (L * (l.totient : ℝ)))
          = (mu l * mu l) * ((l.totient : ℝ) / ((L * (l.totient : ℝ)) * (L * (l.totient : ℝ)))) := by ring
        _ = 1 * ((l.totient : ℝ) / ((L * (l.totient : ℝ)) * (L * (l.totient : ℝ)))) := by rw [hmu2]
        _ = (1 / L ^ 2) * (1 / (l.totient : ℝ)) := by field_simp [hL_pos.ne', hlt_pos.ne']
    rw [Finset.sum_congr rfl hterm_l, ← Finset.mul_sum]
    change (1 / L ^ 2) * L = 1 / L
    field_simp [hL_pos.ne']
  have hP_cardR : (P60.card : ℝ) ≤ (z : ℝ) + ((P60.filter (fun p => z < p)).card : ℝ) := by
    exact_mod_cast hP_split
  have hR_bound : ((P60.filter (fun p => z < p)).card : ℝ) ≤
      (R.card : ℝ) * (X : ℝ) / 60 * (1 / L) + (R.card : ℝ) * (D.card : ℝ) ^ 2 := by
    calc ((P60.filter (fun p => z < p)).card : ℝ)
        ≤ ∑ n ∈ A60, (∑ d ∈ D, (if d ∣ n then lam d else 0)) ^ 2 := hP_le_R
      _ = ∑ d1 ∈ D, ∑ d2 ∈ D, lam d1 * lam d2 *
            ((A60.filter (fun n => Nat.lcm d1 d2 ∣ n)).card : ℝ) := hQ_expand
      _ ≤ (R.card : ℝ) * (X : ℝ) / 60 * (∑ d1 ∈ D, ∑ d2 ∈ D, (lam d1 * lam d2) / (Nat.lcm d1 d2 : ℝ)) +
            (R.card : ℝ) * (D.card : ℝ) ^ 2 := hQ_bound
      _ = (R.card : ℝ) * (X : ℝ) / 60 * (1 / L) + (R.card : ℝ) * (D.card : ℝ) ^ 2 := by rw [hQ_eval]
  calc (P60.card : ℝ) ≤ (z : ℝ) + ((P60.filter (fun p => z < p)).card : ℝ) := hP_cardR
    _ ≤ (z : ℝ) + ((R.card : ℝ) * (X : ℝ) / 60 * (1 / L) + (R.card : ℝ) * (D.card : ℝ) ^ 2) := by
        linarith [hR_bound]
    _ = (z : ℝ) + (R.card : ℝ) * (X : ℝ) / (60 * L) + (R.card : ℝ) * (D.card : ℝ) ^ 2 := by ring

/- ## Section 4: Finite L(z) bounds, analytic L(z) lower bound, and asymptotic pi60 bounds -/

private lemma d_eq_fast {z : ℕ} (hz : z ≤ 300) :
    (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30) =
    (Finset.Icc 1 z).filter (fun d => Nat.Coprime d 30 ∧ d % 49 ≠ 0 ∧ d % 121 ≠ 0 ∧
      d % 169 ≠ 0 ∧ d % 289 ≠ 0) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, hdSqf, hd30⟩
    refine ⟨h1, hd30, ?_, ?_, ?_, ?_⟩
    · intro h49; exact (by decide : ¬ IsUnit 7) (hdSqf 7 (by omega))
    · intro h121; exact (by decide : ¬ IsUnit 11) (hdSqf 11 (by omega))
    · intro h169; exact (by decide : ¬ IsUnit 13) (hdSqf 13 (by omega))
    · intro h289; exact (by decide : ¬ IsUnit 17) (hdSqf 17 (by omega))
  · rintro ⟨h1, hd30, h49, h121, h169, h289⟩
    refine ⟨h1, ?_, hd30⟩
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp ⟨k, hpk⟩
    have hp17 : p ≤ 17 := by
      by_contra hp18
      have : 18 ≤ p := by omega
      have h18 : 324 ≤ p * p := by nlinarith
      have hpos_k : 1 ≤ k := by
        by_contra hk; have : k = 0 := by omega
        rw [this, mul_zero] at hpk; omega
      have : 324 ≤ d := by nlinarith
      omega
    have hndvd : p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 := by
      refine ⟨?_, ?_, ?_⟩ <;> intro hpeq <;> subst hpeq
      · have : 2 ∣ Nat.gcd d 30 := Nat.dvd_gcd ⟨2 * k, by linarith⟩ (by decide)
        rw [hd30] at this; exact absurd this (by decide)
      · have : 3 ∣ Nat.gcd d 30 := Nat.dvd_gcd ⟨3 * k, by linarith⟩ (by decide)
        rw [hd30] at this; exact absurd this (by decide)
      · have : 5 ∣ Nat.gcd d 30 := Nat.dvd_gcd ⟨5 * k, by linarith⟩ (by decide)
        rw [hd30] at this; exact absurd this (by decide)
    have hcases : p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 := by
      have hpr := hp
      have hplt : p < 18 := by omega
      interval_cases p <;> first | exact absurd hpr (by decide) | omega
    rcases hcases with rfl | rfl | rfl | rfl <;> omega

private lemma sum_inv_totient_ge_of_nat (D : Finset ℕ) (S : ℕ)
    (hS : S ≤ ∑ d ∈ D, 1000000 / d.totient) :
    (S : ℝ) / 1000000 ≤ ∑ d ∈ D, (1 / (d.totient : ℝ)) := by
  have h1 : (S : ℝ) ≤ ∑ d ∈ D, (1000000 / d.totient : ℕ) := by exact_mod_cast hS
  have h2 : ∀ d ∈ D, ((1000000 / d.totient : ℕ) : ℝ) ≤ 1000000 * (1 / (d.totient : ℝ)) := fun d _ => by
    by_cases hdt : d.totient = 0
    · simp [hdt]
    · have hpos : (0 : ℝ) < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hdt)
      rw [mul_one_div, le_div_iff₀ hpos]
      exact_mod_cast Nat.div_mul_le_self 1000000 d.totient
  have h3 : (S : ℝ) ≤ 1000000 * ∑ d ∈ D, (1 / (d.totient : ℝ)) := by
    rw [Finset.mul_sum]
    push_cast at h1
    exact h1.trans (Finset.sum_le_sum h2)
  linarith

private lemma d29_bound :
    ((Finset.Icc 1 29).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)).card = 8 ∧
    (1549222 : ℝ) / 1000000 ≤
      ∑ d ∈ (Finset.Icc 1 29).filter (fun d => Squarefree d ∧ Nat.Coprime d 30),
        (1 / (d.totient : ℝ)) := by
  rw [d_eq_fast (by decide)]
  let D := (Finset.Icc 1 29).filter (fun d => Nat.Coprime d 30 ∧ d % 49 ≠ 0 ∧ d % 121 ≠ 0 ∧
    d % 169 ≠ 0 ∧ d % 289 ≠ 0)
  have hdec : D.card = 8 ∧ ∑ d ∈ D, 1000000 / d.totient = 1549222 := by decide +kernel
  exact ⟨hdec.1, sum_inv_totient_ge_of_nat D 1549222 (le_of_eq hdec.2.symm)⟩

private lemma d100_bound :
    ((Finset.Icc 1 100).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)).card = 25 ∧
    (1854689 : ℝ) / 1000000 ≤
      ∑ d ∈ (Finset.Icc 1 100).filter (fun d => Squarefree d ∧ Nat.Coprime d 30),
        (1 / (d.totient : ℝ)) := by
  rw [d_eq_fast (by decide)]
  let D := (Finset.Icc 1 100).filter (fun d => Nat.Coprime d 30 ∧ d % 49 ≠ 0 ∧ d % 121 ≠ 0 ∧
    d % 169 ≠ 0 ∧ d % 289 ≠ 0)
  have hdec : D.card = 25 ∧ ∑ d ∈ D, 1000000 / d.totient = 1854689 := by decide +kernel
  exact ⟨hdec.1, sum_inv_totient_ge_of_nat D 1854689 (le_of_eq hdec.2.symm)⟩

private lemma d300_bound :
    ((Finset.Icc 1 300).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)).card = 76 ∧
    (2151904 : ℝ) / 1000000 ≤
      ∑ d ∈ (Finset.Icc 1 300).filter (fun d => Squarefree d ∧ Nat.Coprime d 30),
        (1 / (d.totient : ℝ)) := by
  rw [d_eq_fast (by decide)]
  let D := (Finset.Icc 1 300).filter (fun d => Nat.Coprime d 30 ∧ d % 49 ≠ 0 ∧ d % 121 ≠ 0 ∧
    d % 169 ≠ 0 ∧ d % 289 ≠ 0)
  have hdec : D.card = 76 ∧ ∑ d ∈ D, 1000000 / d.totient = 2151904 := by decide +kernel
  exact ⟨hdec.1, sum_inv_totient_ge_of_nat D 2151904 (le_of_eq hdec.2.symm)⟩

private lemma log_lt_of_pow_lt {a : ℝ} {p q : ℕ} (ha : 0 < a) (hq : 0 < q)
    (h : a ^ q < (2.718 : ℝ) ^ p) :
    Real.log a < (p : ℝ) / (q : ℝ) := by
  have he : (2.718 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have hexp : Real.exp 1 ^ p = Real.exp (p : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
  have hlt : a ^ q < Real.exp (p : ℝ) := by
    by_cases hp : p = 0
    · subst hp; simp at h ⊢; exact h
    · exact h.trans ((pow_lt_pow_left₀ he (by norm_num) hp).trans_eq hexp)
  have hlog := Real.log_lt_log (pow_pos ha q) hlt
  rw [Real.log_pow, Real.log_exp] at hlog
  exact (lt_div_iff₀ (Nat.cast_pos.mpr hq)).mpr (by linarith)

private lemma log_ten_gt : (23 / 10 : ℝ) < Real.log 10 := by
  have he : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  have hpow : (2.7182818286 : ℝ) ^ 23 < (10 : ℝ) ^ 10 := by norm_num
  have hexp23 : Real.exp 1 ^ 23 = Real.exp ((23 : ℕ) : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
  have hlt : Real.exp (23 : ℝ) < (10 : ℝ) ^ 10 := by
    calc Real.exp (23 : ℝ) = Real.exp ((23 : ℕ) : ℝ) := by norm_num
      _ = Real.exp 1 ^ 23 := hexp23.symm
      _ < (2.7182818286 : ℝ) ^ 23 := pow_lt_pow_left₀ he (Real.exp_pos 1).le (by decide)
      _ < (10 : ℝ) ^ 10 := hpow
  have hlog := Real.log_lt_log (Real.exp_pos 23) hlt
  rw [Real.log_exp, Real.log_pow] at hlog
  push_cast at hlog
  linarith

private lemma sqf_prod_of_primes (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    Squarefree (∏ p ∈ F, p) ∧ (∏ p ∈ F, p).primeFactors = F ∧
      (∏ p ∈ F, p).totient = ∏ p ∈ F, (p - 1) := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    have hp := hF p (Finset.mem_insert_self p s)
    obtain ⟨ih1, ih2, ih3⟩ := ih (fun q hq => hF q (Finset.mem_insert_of_mem hq))
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hqs => ?_
      have hq := hF q (Finset.mem_insert_of_mem hqs)
      exact (hp.coprime_iff_not_dvd).mpr fun hdiv => by
        have := (Nat.Prime.dvd_iff_eq hq hp.ne_one).mp hdiv
        subst this; exact hps hqs
    have hs0 : (∏ q ∈ s, q) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hqs =>
      (hF q (Finset.mem_insert_of_mem hqs)).ne_zero
    rw [Finset.prod_insert hps, Finset.prod_insert hps]
    refine ⟨?_, ?_, ?_⟩
    · exact (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, ih1⟩
    · rw [Nat.primeFactors_mul hp.ne_zero hs0, hp.primeFactors, ih2, Finset.singleton_union]
    · rw [Nat.totient_mul hcop, Nat.totient_prime hp, ih3]

private lemma sum_inv_primes_subset_le (z : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∀ M : Finset ℕ, (∀ m ∈ M, 1 ≤ m ∧ m ≤ z ∧ m.primeFactors ⊆ S) →
      ∑ m ∈ M, (1 / (m : ℝ)) ≤ ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1)) := by
  induction S using Finset.induction_on with
  | empty =>
    intro M hM
    have hsub : M ⊆ {1} := fun m hm => by
      obtain ⟨hm1, _, hmp⟩ := hM m hm
      rw [Finset.subset_empty] at hmp
      have hm_eq : m = 1 := by
        by_contra hm_ne1
        obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hm_ne1
        have hmem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩
        rw [hmp] at hmem; simp at hmem
      simp [hm_eq]
    calc ∑ m ∈ M, (1 / (m : ℝ)) ≤ ∑ m ∈ ({1} : Finset ℕ), (1 / (m : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = 1 := by simp
      _ = ∏ p ∈ ∅, ((p : ℝ) / ((p : ℝ) - 1)) := by simp
  | @insert p s hps ih =>
    intro M hM
    have hp := hS p (Finset.mem_insert_self p s)
    have hss : ∀ q ∈ s, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hmaps : ∀ m ∈ M, padicValNat p m ∈ Finset.range (z + 1) := fun m hm => by
      obtain ⟨hm1, hmz, _⟩ := hM m hm
      rw [Finset.mem_range]
      have hpow : p ^ padicValNat p m ∣ m := pow_padicValNat_dvd
      have hle_m : p ^ padicValNat p m ≤ m := Nat.le_of_dvd hm1 hpow
      have hk_lt : padicValNat p m < p ^ padicValNat p m := by
        calc padicValNat p m < 2 ^ padicValNat p m := Nat.lt_two_pow_self
          _ ≤ p ^ padicValNat p m := Nat.pow_le_pow_left hp.two_le _
      omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hfiber : ∀ k ∈ Finset.range (z + 1),
        ∑ m ∈ M.filter (fun m => padicValNat p m = k), (1 / (m : ℝ)) ≤
          (1 / (p : ℝ)) ^ k * ∏ q ∈ s, ((q : ℝ) / ((q : ℝ) - 1)) := by
      intro k _
      let Mk := M.filter (fun m => padicValNat p m = k)
      let Mk' := Mk.image (fun m => m / p ^ k)
      have hM'_prop : ∀ m' ∈ Mk', 1 ≤ m' ∧ m' ≤ z ∧ m'.primeFactors ⊆ s := by
        intro m' hm'
        rcases Finset.mem_image.mp hm' with ⟨m, hm, rfl⟩
        rw [Finset.mem_filter] at hm
        obtain ⟨hm1, hmz, hmp⟩ := hM m hm.1
        have hpk : p ^ k ∣ m := hm.2 ▸ pow_padicValNat_dvd
        have hpk_pos : 0 < p ^ k := pow_pos hp.pos k
        refine ⟨Nat.div_pos (Nat.le_of_dvd hm1 hpk) hpk_pos, (Nat.div_le_self m _).trans hmz, ?_⟩
        intro q hq
        have hqm : q ∈ m.primeFactors := Nat.mem_primeFactors.mpr
          ⟨Nat.prime_of_mem_primeFactors hq,
           (Nat.dvd_of_mem_primeFactors hq).trans (Nat.div_dvd_of_dvd hpk), by omega⟩
        rcases Finset.mem_insert.mp (hmp hqm) with rfl | hqs
        · exfalso
          have hp_m' : q ∣ m / q ^ k := Nat.dvd_of_mem_primeFactors hq
          have hpk1 : q ^ (k + 1) ∣ m := by
            have := mul_dvd_mul_left (q ^ k) hp_m'
            rwa [Nat.mul_div_cancel' hpk, ← pow_succ] at this
          have hle_k1 : k + 1 ≤ padicValNat q m := by
            have : Fact q.Prime := ⟨hp⟩
            exact (padicValNat_dvd_iff_le (by omega)).mp hpk1
          omega
        · exact hqs
      have hinj : ∀ m1 ∈ Mk, ∀ m2 ∈ Mk, m1 / p ^ k = m2 / p ^ k → m1 = m2 := by
        intro m1 hm1 m2 hm2 heq
        rw [Finset.mem_filter] at hm1 hm2
        have h1 : p ^ k ∣ m1 := hm1.2 ▸ pow_padicValNat_dvd
        have h2 : p ^ k ∣ m2 := hm2.2 ▸ pow_padicValNat_dvd
        rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
      have hterm : ∀ m ∈ Mk, (1 / (m : ℝ)) = (1 / (p : ℝ)) ^ k * (1 / ((m / p ^ k : ℕ) : ℝ)) := by
        intro m hm
        rw [Finset.mem_filter] at hm
        have h1 : p ^ k ∣ m := hm.2 ▸ pow_padicValNat_dvd
        have hmul : (m : ℝ) = (p : ℝ) ^ k * ((m / p ^ k : ℕ) : ℝ) := by
          exact_mod_cast (Nat.mul_div_cancel' h1).symm
        rw [hmul]; simp [mul_comm]
      calc ∑ m ∈ Mk, (1 / (m : ℝ))
          = (1 / (p : ℝ)) ^ k * ∑ m ∈ Mk, (1 / ((m / p ^ k : ℕ) : ℝ)) := by
              rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
        _ = (1 / (p : ℝ)) ^ k * ∑ m' ∈ Mk', (1 / (m' : ℝ)) := by
              rw [Finset.sum_image hinj]
        _ ≤ (1 / (p : ℝ)) ^ k * ∏ q ∈ s, ((q : ℝ) / ((q : ℝ) - 1)) :=
              mul_le_mul_of_nonneg_left (ih hss Mk' hM'_prop) (by positivity)
    have hgeom : ∑ k ∈ Finset.range (z + 1), (1 / (p : ℝ)) ^ k ≤ (p : ℝ) / ((p : ℝ) - 1) := by
      have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
      have hr_lt : (1 / (p : ℝ)) < 1 := div_lt_one (by positivity) |>.mpr hp1
      have h1r : 0 < 1 - (1 / (p : ℝ)) := sub_pos.mpr hr_lt
      rw [geom_sum_eq hr_lt.ne]
      have hnum : (1 / (p : ℝ)) ^ (z + 1) - 1 ≥ -1 := by
        have : 0 ≤ (1 / (p : ℝ)) ^ (z + 1) := by positivity
        linarith
      have hsub : 1 - (1 / (p : ℝ)) ^ (z + 1) ≤ 1 := by linarith
      calc ((1 / (p : ℝ)) ^ (z + 1) - 1) / (1 / (p : ℝ) - 1)
          = (1 - (1 / (p : ℝ)) ^ (z + 1)) / (1 - 1 / (p : ℝ)) := by
              rw [← neg_sub (1 : ℝ) ((1 / (p : ℝ)) ^ (z + 1)), ← neg_sub (1 : ℝ) (1 / (p : ℝ)), neg_div_neg_eq]
        _ ≤ 1 / (1 - 1 / (p : ℝ)) := div_le_div_of_nonneg_right hsub h1r.le
        _ = (p : ℝ) / ((p : ℝ) - 1) := by field_simp [show (p : ℝ) ≠ 0 by positivity]
    calc ∑ k ∈ Finset.range (z + 1), ∑ m ∈ M.filter (fun m => padicValNat p m = k), (1 / (m : ℝ))
        ≤ ∑ k ∈ Finset.range (z + 1), (1 / (p : ℝ)) ^ k * ∏ q ∈ s, ((q : ℝ) / ((q : ℝ) - 1)) :=
          Finset.sum_le_sum hfiber
      _ = (∑ k ∈ Finset.range (z + 1), (1 / (p : ℝ)) ^ k) * ∏ q ∈ s, ((q : ℝ) / ((q : ℝ) - 1)) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ ((p : ℝ) / ((p : ℝ) - 1)) * ∏ q ∈ s, ((q : ℝ) / ((q : ℝ) - 1)) := by
          refine mul_le_mul_of_nonneg_right hgeom ?_
          refine Finset.prod_nonneg fun q hq => ?_
          have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (hss q hq).one_lt
          have : (0 : ℝ) < (q : ℝ) - 1 := by linarith
          positivity
      _ = ∏ q ∈ insert p s, ((q : ℝ) / ((q : ℝ) - 1)) :=
          (Finset.prod_insert (f := fun q : ℕ => (q : ℝ) / ((q : ℝ) - 1)) hps).symm

private lemma analytic_L_lower {z : ℕ} (hz : 10 ≤ z) :
    Real.log ((z : ℝ) + 1) + 1 / 2 ≤
      (15 / 4 : ℝ) * ∑ d ∈ (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30),
        (1 / (d.totient : ℝ)) := by
  let D := (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)
  let skel : ℕ → ℕ := fun n => ∏ p ∈ n.primeFactors.filter (fun p => Nat.Coprime p 30), p
  have hmaps : ∀ n ∈ Finset.Icc 1 z, skel n ∈ D := fun n hn => by
    rw [Finset.mem_Icc] at hn
    let Fn := n.primeFactors.filter (fun p => Nat.Coprime p 30)
    have hFn : ∀ p ∈ Fn, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    obtain ⟨hsqf, _, _⟩ := sqf_prod_of_primes Fn hFn
    have hcop : Nat.Coprime (skel n) 30 := Nat.Coprime.prod_left fun p hp =>
      (Finset.mem_filter.mp hp).2
    have hdvd : skel n ∣ n := by
      have hn0 : n ≠ 0 := by omega
      have : ∀ F : Finset ℕ, (∀ p ∈ F, p.Prime ∧ p ∣ n) → (∏ p ∈ F, p) ∣ n := fun F hF => by
        induction F using Finset.induction_on with
        | empty => simp
        | @insert p s hps ih =>
          rw [Finset.prod_insert hps]
          have hps' := ih fun q hq => hF q (Finset.mem_insert_of_mem hq)
          have hpp := hF p (Finset.mem_insert_self p s)
          have hc : Nat.Coprime p (∏ q ∈ s, q) := Nat.Coprime.prod_right fun q hq => by
            have hqp := hF q (Finset.mem_insert_of_mem hq)
            exact (hpp.1.coprime_iff_not_dvd).mpr fun hd => by
              have := (Nat.Prime.dvd_iff_eq hqp.1 hpp.1.ne_one).mp hd
              subst this; exact hps hq
          exact hc.mul_dvd_of_dvd_of_dvd hpp.2 hps'
      exact this Fn fun p hp => by
        rw [Finset.mem_filter] at hp
        exact ⟨Nat.prime_of_mem_primeFactors hp.1, Nat.dvd_of_mem_primeFactors hp.1⟩
    have hs1 : 1 ≤ skel n := Nat.one_le_iff_ne_zero.mpr (ne_zero_of_dvd_ne_zero (by omega) hdvd)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hs1, (Nat.le_of_dvd hn.1 hdvd).trans hn.2⟩,
      hsqf, hcop⟩
  have hharmonic : ∑ n ∈ Finset.Icc 1 z, (1 / (n : ℝ)) ≤ (15 / 4 : ℝ) * ∑ d ∈ D, (1 / (d.totient : ℝ)) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
    have hfiber : ∀ s ∈ D, ∑ n ∈ (Finset.Icc 1 z).filter (fun n => skel n = s), (1 / (n : ℝ)) ≤
        (15 / 4 : ℝ) * (1 / (s.totient : ℝ)) := fun s hs => by
      rw [Finset.mem_filter, Finset.mem_Icc] at hs
      obtain ⟨⟨hs1, _⟩, hsSqf, hs30⟩ := hs
      let Ns := (Finset.Icc 1 z).filter (fun n => skel n = s)
      let Ms := Ns.image (fun n => n / s)
      have hsdvd : ∀ n ∈ Ns, s ∣ n := fun n hn => by
        rw [Finset.mem_filter] at hn
        rw [← hn.2]
        have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn.1).1; omega
        have : ∀ F : Finset ℕ, (∀ p ∈ F, p.Prime ∧ p ∣ n) → (∏ p ∈ F, p) ∣ n := fun F hF => by
          induction F using Finset.induction_on with
          | empty => simp
          | @insert p t hpt ih =>
            rw [Finset.prod_insert hpt]
            have hpt' := ih fun q hq => hF q (Finset.mem_insert_of_mem hq)
            have hpp := hF p (Finset.mem_insert_self p t)
            have hc : Nat.Coprime p (∏ q ∈ t, q) := Nat.Coprime.prod_right fun q hq => by
              have hqp := hF q (Finset.mem_insert_of_mem hq)
              exact (hpp.1.coprime_iff_not_dvd).mpr fun hd => by
                have := (Nat.Prime.dvd_iff_eq hqp.1 hpp.1.ne_one).mp hd
                subst this; exact hpt hq
            exact hc.mul_dvd_of_dvd_of_dvd hpp.2 hpt'
        exact this _ fun p hp => by
          rw [Finset.mem_filter] at hp
          exact ⟨Nat.prime_of_mem_primeFactors hp.1, Nat.dvd_of_mem_primeFactors hp.1⟩
      have hinj : ∀ n1 ∈ Ns, ∀ n2 ∈ Ns, n1 / s = n2 / s → n1 = n2 := fun n1 h1 n2 h2 heq => by
        rw [← Nat.mul_div_cancel' (hsdvd n1 h1), ← Nat.mul_div_cancel' (hsdvd n2 h2), heq]
      have hterm : ∀ n ∈ Ns, (1 / (n : ℝ)) = (1 / (s : ℝ)) * (1 / ((n / s : ℕ) : ℝ)) := fun n hn => by
        have hm : (n : ℝ) = (s : ℝ) * ((n / s : ℕ) : ℝ) := by
          exact_mod_cast (Nat.mul_div_cancel' (hsdvd n hn)).symm
        rw [hm]; simp [mul_comm]
      have hS_primes : ∀ p ∈ ({2, 3, 5} : Finset ℕ) ∪ s.primeFactors, p.Prime := fun p hp => by
        rw [Finset.mem_union] at hp
        rcases hp with h | h
        · simp at h; rcases h with rfl | rfl | rfl <;> decide
        · exact Nat.prime_of_mem_primeFactors h
      have hMs_prop : ∀ m ∈ Ms, 1 ≤ m ∧ m ≤ z ∧ m.primeFactors ⊆ {2, 3, 5} ∪ s.primeFactors := by
        intro m hm
        rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
        have hsn := hsdvd n hn
        rw [Finset.mem_filter, Finset.mem_Icc] at hn
        refine ⟨Nat.div_pos (Nat.le_of_dvd hn.1.1 hsn) hs1, (Nat.div_le_self n s).trans hn.1.2, ?_⟩
        intro q hq
        have hqp := Nat.prime_of_mem_primeFactors hq
        have hqn : q ∣ n := (Nat.dvd_of_mem_primeFactors hq).trans (Nat.div_dvd_of_dvd hsn)
        rw [Finset.mem_union]
        by_cases hq235 : q = 2 ∨ q = 3 ∨ q = 5
        · left; simp; tauto
        · right
          have hq30 : Nat.Coprime q 30 := by
            refine (hqp.coprime_iff_not_dvd).mpr fun hd30 => ?_
            have hle30 : q ≤ 30 := Nat.le_of_dvd (by decide) hd30
            have hlt31 : q < 31 := by omega
            interval_cases q <;> first | exact absurd hqp (by decide) | omega
          have hq_mem : q ∈ n.primeFactors.filter (fun p => Nat.Coprime p 30) :=
            Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hqp, hqn, by omega⟩, hq30⟩
          have hqs : q ∣ s := by
            rw [← hn.2]
            exact Finset.dvd_prod_of_mem id hq_mem
          exact Nat.mem_primeFactors.mpr ⟨hqp, hqs, by omega⟩
      have hsum_Ms := sum_inv_primes_subset_le z ({2, 3, 5} ∪ s.primeFactors) hS_primes Ms hMs_prop
      have hdisj235 : Disjoint ({2, 3, 5} : Finset ℕ) s.primeFactors :=
        Finset.disjoint_left.mpr fun p h1 h2 => by
          have hps := Nat.dvd_of_mem_primeFactors h2
          simp at h1
          rcases h1 with rfl | rfl | rfl
          · exact absurd (Nat.dvd_gcd hps (by decide : 2 ∣ 30)) (by rw [hs30]; decide)
          · exact absurd (Nat.dvd_gcd hps (by decide : 3 ∣ 30)) (by rw [hs30]; decide)
          · exact absurd (Nat.dvd_gcd hps (by decide : 5 ∣ 30)) (by rw [hs30]; decide)
      have hprod_split : ∏ p ∈ ({2, 3, 5} : Finset ℕ) ∪ s.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) =
          (15 / 4 : ℝ) * ((s : ℝ) / (s.totient : ℝ)) := by
        rw [Finset.prod_union hdisj235]
        have h15_4 : ∏ p ∈ ({2, 3, 5} : Finset ℕ), ((p : ℝ) / ((p : ℝ) - 1)) = (15 / 4 : ℝ) := by
          norm_num
        have hsp : ∏ p ∈ s.primeFactors, p = s := prod_pf_of_sqf hsSqf (by omega)
        have hspf := fun p (hp : p ∈ s.primeFactors) => Nat.prime_of_mem_primeFactors hp
        obtain ⟨_, _, htot_s⟩ := sqf_prod_of_primes s.primeFactors hspf
        rw [hsp] at htot_s
        have htot_eq : ∏ p ∈ s.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) = (s : ℝ) / (s.totient : ℝ) := by
          have h1 : ∏ p ∈ s.primeFactors, (p : ℝ) = (s : ℝ) := by
            calc ∏ p ∈ s.primeFactors, (p : ℝ)
                = ((∏ p ∈ s.primeFactors, p : ℕ) : ℝ) := (Nat.cast_prod _ _).symm
              _ = (s : ℝ) := by exact_mod_cast hsp
          have h2 : ∏ p ∈ s.primeFactors, ((p : ℝ) - 1) = (s.totient : ℝ) := by
            have : ∀ p ∈ s.primeFactors, (p : ℝ) - 1 = ((p - 1 : ℕ) : ℝ) := fun p hp => by
              have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
              rw [Nat.cast_sub hp1, Nat.cast_one]
            calc ∏ p ∈ s.primeFactors, ((p : ℝ) - 1)
                = ∏ p ∈ s.primeFactors, ((p - 1 : ℕ) : ℝ) := Finset.prod_congr rfl this
              _ = ((∏ p ∈ s.primeFactors, (p - 1) : ℕ) : ℝ) := (Nat.cast_prod _ _).symm
              _ = (s.totient : ℝ) := by rw [← htot_s]
          rw [Finset.prod_div_distrib, h1, h2]
        rw [h15_4, htot_eq]
      calc ∑ n ∈ Ns, (1 / (n : ℝ))
          = (1 / (s : ℝ)) * ∑ n ∈ Ns, (1 / ((n / s : ℕ) : ℝ)) := by
              rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
        _ = (1 / (s : ℝ)) * ∑ m ∈ Ms, (1 / (m : ℝ)) := by rw [Finset.sum_image hinj]
        _ ≤ (1 / (s : ℝ)) * ((15 / 4 : ℝ) * ((s : ℝ) / (s.totient : ℝ))) := by
              rw [← hprod_split]
              exact mul_le_mul_of_nonneg_left hsum_Ms (by positivity)
        _ = (15 / 4 : ℝ) * (1 / (s.totient : ℝ)) := by
              have hs_ne : (s : ℝ) ≠ 0 := by positivity
              field_simp [hs_ne]
    exact Finset.sum_le_sum hfiber
  have hlog_sub : ∀ n : ℕ, 1 ≤ n → Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
    intro n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have h1 := Real.log_le_sub_one_of_pos (div_pos hn1_pos hn_pos)
    rw [Real.log_div hn1_pos.ne' hn_pos.ne'] at h1
    have : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by field_simp [hn_pos.ne']; ring
    linarith
  have hIoc_tele : ∀ b : ℕ, 10 ≤ b →
      Real.log ((b : ℝ) + 1) - Real.log 11 ≤ ∑ n ∈ Finset.Ioc 10 b, (1 / (n : ℝ)) := by
    intro b hb
    induction b, hb using Nat.le_induction with
    | base => simp; norm_num
    | succ b hb ih =>
      have hsplit : Finset.Ioc 10 (b + 1) = insert (b + 1) (Finset.Ioc 10 b) := by
        ext x; simp only [Finset.mem_insert, Finset.mem_Ioc]; omega
      have hnot : b + 1 ∉ Finset.Ioc 10 b := by simp
      rw [hsplit, Finset.sum_insert hnot]
      have hstep := hlog_sub (b + 1) (by omega)
      push_cast at hstep ⊢
      linarith
  have hsplit_Icc : Finset.Icc 1 z = Finset.Icc 1 10 ∪ Finset.Ioc 10 z := by
    ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 1 10) (Finset.Ioc 10 z) := Finset.disjoint_left.mpr fun n h1 h2 => by
    simp at h1 h2; omega
  have h10 : ∑ n ∈ (Finset.Icc 1 10 : Finset ℕ), (1 / (n : ℝ)) = (7381 : ℝ) / 2520 := by
    have hq : ∑ n ∈ (Finset.Icc 1 10 : Finset ℕ), (1 / (n : ℚ)) = 7381 / 2520 := by
      norm_num [Finset.sum_Icc_succ_top]
    have hr := congrArg (Rat.cast (K := ℝ)) hq
    simpa [Rat.cast_sum] using hr
  have hlog11 : Real.log (11 : ℝ) < (12 : ℝ) / 5 :=
    log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
  have hlog_lower : Real.log ((z : ℝ) + 1) + 1 / 2 ≤ ∑ n ∈ Finset.Icc 1 z, (1 / (n : ℝ)) := by
    rw [hsplit_Icc, Finset.sum_union hdisj, h10]
    linarith [hIoc_tele z hz]
  exact hlog_lower.trans hharmonic

private lemma card_D_le (z : ℕ) :
    ((Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)).card ≤ 8 * (z / 30 + 1) := by
  let R8 : Finset ℕ := (Finset.range 30).filter (fun r => Nat.Coprime r 30)
  have hR8 : R8.card = 8 := by decide
  let D := (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)
  have himg : D.image (fun d => (d / 30, d % 30)) ⊆ Finset.range (z / 30 + 1) ×ˢ R8 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨d, hd, rfl⟩
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    rw [Finset.mem_product, Finset.mem_range]
    refine ⟨Nat.lt_succ_of_le (Nat.div_le_div_right hd.1.2),
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt d (by decide)), ?_⟩⟩
    change Nat.gcd (d % 30) 30 = 1
    rw [← Nat.gcd_rec 30 d, Nat.gcd_comm]
    exact hd.2.2
  have hinj : ∀ d1 ∈ D, ∀ d2 ∈ D, (d1 / 30, d1 % 30) = (d2 / 30, d2 % 30) → d1 = d2 := by
    intro d1 _ d2 _ heq
    have hq : d1 / 30 = d2 / 30 := (Prod.ext_iff.mp heq).1
    have hr : d1 % 30 = d2 % 30 := (Prod.ext_iff.mp heq).2
    omega
  calc D.card = (D.image (fun d => (d / 30, d % 30))).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (z / 30 + 1) ×ˢ R8).card := Finset.card_le_card himg
    _ = (z / 30 + 1) * 8 := by rw [Finset.card_product, Finset.card_range, hR8]
    _ = 8 * (z / 30 + 1) := mul_comm _ _

private lemma log_div_sqrt_le {X X0 : ℝ} (hX0 : 10 ≤ X0) (hX : X0 ≤ X)
    {x0_hi : ℝ} (hx0 : Real.log X0 ≤ x0_hi) :
    Real.log X / Real.sqrt X ≤ x0_hi / Real.sqrt X0 := by
  have hX0pos : 0 < X0 := by linarith
  have hXpos : 0 < X := by linarith
  let u := Real.sqrt (X / X0)
  have hu1 : 1 ≤ u := by
    rw [Real.le_sqrt' (by positivity), one_pow, one_le_div hX0pos]; exact hX
  have hu_pos : 0 < u := by linarith
  have hlog_u : Real.log (X / X0) ≤ 2 * (u - 1) := by
    have hsq : X / X0 = u * u := (Real.mul_self_sqrt (div_pos hXpos hX0pos).le).symm
    rw [hsq, Real.log_mul hu_pos.ne' hu_pos.ne']
    linarith [Real.log_le_sub_one_of_pos hu_pos]
  have h2_le : 2 ≤ Real.log X0 := by
    have hpow : (2.7182818286 : ℝ) ^ 2 < 10 := by norm_num
    have hexp2 : Real.exp (2 : ℝ) < 10 := by
      have he : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
      have h1 : Real.exp 1 ^ 2 = Real.exp (2 : ℕ) := by rw [← Real.exp_nat_mul, mul_one]
      have h2 := (pow_lt_pow_left₀ he (Real.exp_pos 1).le (by decide)).trans hpow
      simpa [h1] using h2
    have hl10 : (2 : ℝ) < Real.log 10 := by
      have := Real.log_lt_log (Real.exp_pos 2) hexp2
      rwa [Real.log_exp] at this
    exact hl10.le.trans (Real.log_le_log (by norm_num) hX0)
  have hlogX : Real.log X ≤ Real.log X0 * u := by
    have hdiv : X = X0 * (X / X0) := (mul_div_cancel₀ X hX0pos.ne').symm
    have hmul : Real.log X = Real.log X0 + Real.log (X / X0) := by
      conv_lhs => rw [hdiv]
      exact Real.log_mul hX0pos.ne' (div_pos hXpos hX0pos).ne'
    have h2u : 2 * (u - 1) ≤ Real.log X0 * (u - 1) :=
      mul_le_mul_of_nonneg_right h2_le (by linarith)
    linarith
  have hsqrtX : Real.sqrt X = Real.sqrt X0 * u := by
    rw [← Real.sqrt_mul hX0pos.le, mul_div_cancel₀ X hX0pos.ne']
  have hsqrt_pos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXpos
  have hsqrt0_pos : 0 < Real.sqrt X0 := Real.sqrt_pos.mpr hX0pos
  calc Real.log X / Real.sqrt X
      ≤ (Real.log X0 * u) / (Real.sqrt X0 * u) := by
          rw [← hsqrtX]
          exact div_le_div_of_nonneg_right hlogX hsqrt_pos.le
    _ = Real.log X0 / Real.sqrt X0 := by field_simp [hu_pos.ne', hsqrt0_pos.ne']
    _ ≤ x0_hi / Real.sqrt X0 := div_le_div_of_nonneg_right hx0 hsqrt0_pos.le

private lemma pi60_le_of_params (R : Finset ℕ) (hR : ∀ r ∈ R, r < 60)
    (X0 : ℕ) (hX0_10 : 10 ≤ X0) (X : ℕ) (hX : X0 ≤ X)
    (x0_lo x0_hi logx0_hi eps1 C_target : ℝ)
    (hx0_lo_2 : 2 ≤ x0_lo) (hx0_lo : x0_lo ≤ Real.log (X0 : ℝ))
    (hx0_hi : Real.log (X0 : ℝ) ≤ x0_hi)
    (hlogx0 : Real.log x0_lo ≤ logx0_hi)
    (hb_neg : (1 / 2 : ℝ) - 11 / 12 - (logx0_hi - 1) / 2 ≤ 0)
    (hL_pos_c : 0 < (4 / 15 : ℝ) * ((1 / 2 : ℝ) * (1 - 1 / x0_lo) +
      ((1 / 2 : ℝ) - 11 / 12 - (logx0_hi - 1) / 2) / x0_lo))
    (heps1_pos : 0 < eps1) (heps1 : x0_hi / (X0 : ℝ) ≤ eps1 ^ 2)
    (hS_min : 28 ≤ (1 : ℝ) / eps1)
    (hC : (R.card : ℝ) / (60 * ((4 / 15 : ℝ) * ((1 / 2 : ℝ) * (1 - 1 / x0_lo) +
      ((1 / 2 : ℝ) - 11 / 12 - (logx0_hi - 1) / 2) / x0_lo))) +
      (64 / 5625 : ℝ) * (R.card : ℝ) +
      (2 / 5 + (128 / 75 : ℝ) * (R.card : ℝ)) * eps1 +
      64 * (R.card : ℝ) * eps1 ^ 2 ≤ C_target) :
    (((Finset.Icc 1 X).filter (fun p => p.Prime ∧ p % 60 ∈ R)).card : ℝ) ≤
      C_target * (X : ℝ) / Real.log (X : ℝ) := by
  have hX0R : (10 : ℝ) ≤ (X0 : ℝ) := by exact_mod_cast hX0_10
  have hXR : (X0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
  have hlog_ge : x0_lo ≤ Real.log (X : ℝ) := hx0_lo.trans (Real.log_le_log (by linarith) hXR)
  have hlog_pos : 0 < Real.log (X : ℝ) := by linarith
  have hx0_hi_nn : 0 ≤ x0_hi := (Real.log_nonneg (by linarith : (1 : ℝ) ≤ (X0 : ℝ))).trans hx0_hi
  have hlog_sqrt := log_div_sqrt_le hX0R hXR hx0_hi
  have hlog_div_X : Real.log (X : ℝ) / (X : ℝ) ≤ eps1 ^ 2 := by
    have hsqX : Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) = (X : ℝ) := Real.mul_self_sqrt hXpos.le
    have hsq0 : Real.sqrt (X0 : ℝ) * Real.sqrt (X0 : ℝ) = (X0 : ℝ) := Real.mul_self_sqrt (by linarith)
    have hsqrt_le : Real.sqrt (X0 : ℝ) ≤ Real.sqrt (X : ℝ) := Real.sqrt_le_sqrt hXR
    have h1 : Real.log (X : ℝ) / (X : ℝ) =
        (Real.log (X : ℝ) / Real.sqrt (X : ℝ)) / Real.sqrt (X : ℝ) := by
      rw [div_div, hsqX]
    have h2 : (x0_hi / Real.sqrt (X0 : ℝ)) / Real.sqrt (X0 : ℝ) = x0_hi / (X0 : ℝ) := by
      rw [div_div, hsq0]
    rw [h1]
    calc (Real.log (X : ℝ) / Real.sqrt (X : ℝ)) / Real.sqrt (X : ℝ)
        ≤ (x0_hi / Real.sqrt (X0 : ℝ)) / Real.sqrt (X : ℝ) :=
          div_le_div_of_nonneg_right hlog_sqrt (Real.sqrt_nonneg _)
      _ ≤ (x0_hi / Real.sqrt (X0 : ℝ)) / Real.sqrt (X0 : ℝ) :=
          div_le_div_of_nonneg_left (div_nonneg hx0_hi_nn (Real.sqrt_nonneg _))
            (Real.sqrt_pos.mpr (by linarith)) hsqrt_le
      _ = x0_hi / (X0 : ℝ) := h2
      _ ≤ eps1 ^ 2 := heps1
  let S := Real.sqrt ((X : ℝ) / Real.log (X : ℝ))
  have hS_pos : 0 < S := Real.sqrt_pos.mpr (div_pos hXpos hlog_pos)
  have hS_sq : S ^ 2 = (X : ℝ) / Real.log (X : ℝ) := Real.sq_sqrt (div_pos hXpos hlog_pos).le
  have hinvS : 1 / S ≤ eps1 := by
    have h1 : (1 / S) ^ 2 ≤ eps1 ^ 2 := by
      rw [div_pow, one_pow, hS_sq, one_div_div]
      exact hlog_div_X
    have h1nn : 0 ≤ 1 / S := by positivity
    nlinarith [sq_nonneg (eps1 - 1 / S)]
  have hS_28 : 28 ≤ S := by
    have : (1 / eps1) ≤ S := by
      rw [div_le_iff₀ heps1_pos]
      have := mul_le_mul_of_nonneg_right hinvS hS_pos.le
      rw [one_div_mul_cancel hS_pos.ne'] at this
      linarith
    linarith
  let z := Nat.floor ((2 / 5 : ℝ) * S)
  have hz_11 : (11 : ℝ) ≤ (2 / 5 : ℝ) * S := by linarith
  have hz_10 : 10 ≤ z := by
    have h11 : 11 ≤ z := Nat.le_floor hz_11
    omega
  have hz_1 : 1 ≤ z := by omega
  let D := (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)
  let L : ℝ := ∑ d ∈ D, (1 / (d.totient : ℝ))
  have hsel := selberg_pi60_le R hR X z hz_1
  change (((Finset.Icc 1 X).filter (fun p => p.Prime ∧ p % 60 ∈ R)).card : ℝ) ≤
      (z : ℝ) + (R.card : ℝ) * (X : ℝ) / (60 * L) + (R.card : ℝ) * (D.card : ℝ) ^ 2 at hsel
  have hL_an : Real.log ((z : ℝ) + 1) + 1 / 2 ≤ (15 / 4 : ℝ) * L := analytic_L_lower hz_10
  have hx0_pos : 0 < x0_lo := by linarith
  have hlog_log_le : Real.log (Real.log (X : ℝ)) ≤ logx0_hi - 1 + Real.log (X : ℝ) / x0_lo := by
    have htan := Real.log_le_sub_one_of_pos (div_pos hlog_pos hx0_pos)
    rw [Real.log_div hlog_pos.ne' hx0_pos.ne'] at htan
    linarith
  have hlog5_2 : Real.log (5 / 2 : ℝ) < 11 / 12 :=
    log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
  have hlog_z1 : Real.log ((2 / 5 : ℝ) * S) ≤ Real.log ((z : ℝ) + 1) := by
    refine Real.log_le_log (by positivity) ?_
    exact (Nat.lt_floor_add_one ((2 / 5 : ℝ) * S)).le
  have hlog_25S : Real.log ((2 / 5 : ℝ) * S) =
      -Real.log (5 / 2 : ℝ) + (1 / 2 : ℝ) * (Real.log (X : ℝ) - Real.log (Real.log (X : ℝ))) := by
    have h1 : (2 / 5 : ℝ) = (5 / 2 : ℝ)⁻¹ := by norm_num
    rw [Real.log_mul (by norm_num) hS_pos.ne', h1, Real.log_inv]
    have hSlog : Real.log S = (1 / 2 : ℝ) * (Real.log (X : ℝ) - Real.log (Real.log (X : ℝ))) := by
      simp only [S]
      rw [Real.log_sqrt (div_pos hXpos hlog_pos).le, Real.log_div hXpos.ne' hlog_pos.ne']
      ring
    rw [hSlog]
  let b_const := (1 / 2 : ℝ) - 11 / 12 - (logx0_hi - 1) / 2
  let L_coef := (4 / 15 : ℝ) * ((1 / 2 : ℝ) * (1 - 1 / x0_lo) + b_const / x0_lo)
  have hL_ge : L_coef * Real.log (X : ℝ) ≤ L := by
    have h15_4 : (1 / 2 : ℝ) * (1 - 1 / x0_lo) * Real.log (X : ℝ) + b_const ≤ (15 / 4 : ℝ) * L := by
      have hsub : -11 / 12 + (1 / 2 : ℝ) * (Real.log (X : ℝ) - (logx0_hi - 1 + Real.log (X : ℝ) / x0_lo)) +
          1 / 2 ≤ Real.log ((z : ℝ) + 1) + 1 / 2 := by
        linarith [hlog5_2, hlog_z1, hlog_25S, hlog_log_le]
      calc (1 / 2 : ℝ) * (1 - 1 / x0_lo) * Real.log (X : ℝ) + b_const
          = -11 / 12 + (1 / 2 : ℝ) * (Real.log (X : ℝ) - (logx0_hi - 1 + Real.log (X : ℝ) / x0_lo)) + 1 / 2 := by
            simp only [b_const]; ring
        _ ≤ Real.log ((z : ℝ) + 1) + 1 / 2 := hsub
        _ ≤ (15 / 4 : ℝ) * L := hL_an
    have hb_mul : (b_const / x0_lo) * Real.log (X : ℝ) ≤ b_const := by
      have hdiv : 1 ≤ Real.log (X : ℝ) / x0_lo := (one_le_div hx0_pos).mpr hlog_ge
      have hneg : b_const * (Real.log (X : ℝ) / x0_lo) ≤ b_const * 1 :=
        mul_le_mul_of_nonpos_left hdiv hb_neg
      simpa [div_mul_eq_mul_div, mul_div_assoc] using hneg
    have hcomb : (15 / 4 : ℝ) * L_coef * Real.log (X : ℝ) ≤ (15 / 4 : ℝ) * L := by
      have heq : (15 / 4 : ℝ) * L_coef * Real.log (X : ℝ) =
          (1 / 2 : ℝ) * (1 - 1 / x0_lo) * Real.log (X : ℝ) + (b_const / x0_lo) * Real.log (X : ℝ) := by
        simp only [L_coef]; ring
      linarith
    linarith
  have hmain_term : (R.card : ℝ) * (X : ℝ) / (60 * L) ≤ ((R.card : ℝ) / (60 * L_coef)) * S ^ 2 := by
    have hL_pos : 0 < L := by
      have : 0 < L_coef * Real.log (X : ℝ) := mul_pos hL_pos_c hlog_pos
      linarith
    rw [hS_sq]
    have h1 : (R.card : ℝ) * (X : ℝ) / (60 * L) ≤ (R.card : ℝ) * (X : ℝ) / (60 * (L_coef * Real.log (X : ℝ))) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    calc (R.card : ℝ) * (X : ℝ) / (60 * L)
        ≤ (R.card : ℝ) * (X : ℝ) / (60 * (L_coef * Real.log (X : ℝ))) := h1
      _ = ((R.card : ℝ) / (60 * L_coef)) * ((X : ℝ) / Real.log (X : ℝ)) := by ring
  have hz_le : (z : ℝ) ≤ (2 / 5 : ℝ) * S := Nat.floor_le (by positivity)
  have hD_le : (D.card : ℝ) ≤ (8 / 75 : ℝ) * S + 8 := by
    have hc := card_D_le z
    have hdiv30 : ((z / 30 : ℕ) : ℝ) ≤ (z : ℝ) / 30 := by
      rw [le_div_iff₀ (by norm_num)]
      exact_mod_cast Nat.div_mul_le_self z 30
    have h1 : (D.card : ℝ) ≤ 8 * ((z : ℝ) / 30 + 1) := by
      have hcr : (D.card : ℝ) ≤ 8 * (((z / 30 : ℕ) : ℝ) + 1) := by exact_mod_cast hc
      linarith
    linarith
  have hD_nn : (0 : ℝ) ≤ (D.card : ℝ) := by positivity
  have hR_nn : (0 : ℝ) ≤ (R.card : ℝ) := by positivity
  have hD_sq : (D.card : ℝ) ^ 2 ≤ (64 / 5625 : ℝ) * S ^ 2 + (128 / 75 : ℝ) * S + 64 := by
    have hsq : (D.card : ℝ) ^ 2 ≤ ((8 / 75 : ℝ) * S + 8) ^ 2 :=
      pow_le_pow_left₀ hD_nn hD_le 2
    linarith [show ((8 / 75 : ℝ) * S + 8) ^ 2 = (64 / 5625 : ℝ) * S ^ 2 + (128 / 75 : ℝ) * S + 64 by ring]
  have herr_term : (z : ℝ) + (R.card : ℝ) * (D.card : ℝ) ^ 2 ≤
      ((64 / 5625 : ℝ) * (R.card : ℝ)) * S ^ 2 +
      (2 / 5 + (128 / 75 : ℝ) * (R.card : ℝ)) * S + 64 * (R.card : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hD_sq hR_nn
    calc (z : ℝ) + (R.card : ℝ) * (D.card : ℝ) ^ 2
        ≤ (2 / 5 : ℝ) * S + (R.card : ℝ) * ((64 / 5625 : ℝ) * S ^ 2 + (128 / 75 : ℝ) * S + 64) :=
          add_le_add hz_le hmul
      _ = ((64 / 5625 : ℝ) * (R.card : ℝ)) * S ^ 2 +
            (2 / 5 + (128 / 75 : ℝ) * (R.card : ℝ)) * S + 64 * (R.card : ℝ) := by ring
  have hS_bound : S ≤ eps1 * S ^ 2 := by
    calc S = (1 / S) * S ^ 2 := by field_simp [hS_pos.ne']
      _ ≤ eps1 * S ^ 2 := mul_le_mul_of_nonneg_right hinvS (sq_nonneg S)
  have h1_bound : (1 : ℝ) ≤ eps1 ^ 2 * S ^ 2 := by
    have h1 : (1 / S) ^ 2 ≤ eps1 ^ 2 := pow_le_pow_left₀ (by positivity) hinvS 2
    calc (1 : ℝ) = (1 / S) ^ 2 * S ^ 2 := by field_simp [hS_pos.ne']
      _ ≤ eps1 ^ 2 * S ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg S)
  have hcoef1 : (2 / 5 + (128 / 75 : ℝ) * (R.card : ℝ)) * S ≤
      (2 / 5 + (128 / 75 : ℝ) * (R.card : ℝ)) * eps1 * S ^ 2 := by
    have hc1 := mul_le_mul_of_nonneg_left hS_bound (by positivity : (0 : ℝ) ≤ 2 / 5 + (128 / 75 : ℝ) * (R.card : ℝ))
    linarith only [hc1]
  have hcoef2 : 64 * (R.card : ℝ) ≤ 64 * (R.card : ℝ) * eps1 ^ 2 * S ^ 2 := by
    have hc2 := mul_le_mul_of_nonneg_left h1_bound (by positivity : (0 : ℝ) ≤ 64 * (R.card : ℝ))
    linarith only [hc2]
  have herr_S2 : (z : ℝ) + (R.card : ℝ) * (D.card : ℝ) ^ 2 ≤
      ((64 / 5625 : ℝ) * (R.card : ℝ) + (2 / 5 + (128 / 75 : ℝ) * (R.card : ℝ)) * eps1 +
        64 * (R.card : ℝ) * eps1 ^ 2) * S ^ 2 := by
    calc (z : ℝ) + (R.card : ℝ) * (D.card : ℝ) ^ 2
        ≤ ((64 / 5625 : ℝ) * (R.card : ℝ)) * S ^ 2 +
            (2 / 5 + (128 / 75 : ℝ) * (R.card : ℝ)) * S + 64 * (R.card : ℝ) := herr_term
      _ ≤ ((64 / 5625 : ℝ) * (R.card : ℝ)) * S ^ 2 +
            (2 / 5 + (128 / 75 : ℝ) * (R.card : ℝ)) * eps1 * S ^ 2 +
            64 * (R.card : ℝ) * eps1 ^ 2 * S ^ 2 := add_le_add (add_le_add le_rfl hcoef1) hcoef2
      _ = ((64 / 5625 : ℝ) * (R.card : ℝ) + (2 / 5 + (128 / 75 : ℝ) * (R.card : ℝ)) * eps1 +
            64 * (R.card : ℝ) * eps1 ^ 2) * S ^ 2 := by ring
  have hcomb_S2 : (((Finset.Icc 1 X).filter (fun p => p.Prime ∧ p % 60 ∈ R)).card : ℝ) ≤ C_target * S ^ 2 := by
    have hstep1 : (((Finset.Icc 1 X).filter (fun p => p.Prime ∧ p % 60 ∈ R)).card : ℝ) ≤
        ((R.card : ℝ) / (60 * L_coef) + (64 / 5625 : ℝ) * (R.card : ℝ) +
          (2 / 5 + (128 / 75 : ℝ) * (R.card : ℝ)) * eps1 +
          64 * (R.card : ℝ) * eps1 ^ 2) * S ^ 2 := by
      calc (((Finset.Icc 1 X).filter (fun p => p.Prime ∧ p % 60 ∈ R)).card : ℝ)
          ≤ (z : ℝ) + (R.card : ℝ) * (X : ℝ) / (60 * L) + (R.card : ℝ) * (D.card : ℝ) ^ 2 := hsel
        _ = (R.card : ℝ) * (X : ℝ) / (60 * L) + ((z : ℝ) + (R.card : ℝ) * (D.card : ℝ) ^ 2) := by ring
        _ ≤ ((R.card : ℝ) / (60 * L_coef)) * S ^ 2 +
              ((64 / 5625 : ℝ) * (R.card : ℝ) + (2 / 5 + (128 / 75 : ℝ) * (R.card : ℝ)) * eps1 +
                64 * (R.card : ℝ) * eps1 ^ 2) * S ^ 2 := add_le_add hmain_term herr_S2
        _ = ((R.card : ℝ) / (60 * L_coef) + (64 / 5625 : ℝ) * (R.card : ℝ) +
              (2 / 5 + (128 / 75 : ℝ) * (R.card : ℝ)) * eps1 +
              64 * (R.card : ℝ) * eps1 ^ 2) * S ^ 2 := by ring
    exact hstep1.trans (mul_le_mul_of_nonneg_right hC (sq_nonneg S))
  calc (((Finset.Icc 1 X).filter (fun p => p.Prime ∧ p % 60 ∈ R)).card : ℝ)
      ≤ C_target * S ^ 2 := hcomb_S2
    _ = C_target * (X : ℝ) / Real.log (X : ℝ) := by rw [hS_sq]; ring

private lemma pi60_4_le_10_pow_7 (X : ℕ) (hX : 10 ^ 7 ≤ X) :
    (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
      p % 60 ∈ ({11, 23, 47, 59} : Finset ℕ))).card : ℝ) ≤
      (71 / 100 : ℝ) * (X : ℝ) / Real.log (X : ℝ) := by
  have hx0_lo : (161 / 10 : ℝ) ≤ Real.log ((10 ^ 7 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
  have hx0_hi : Real.log ((10 ^ 7 : ℕ) : ℝ) ≤ 371 / 23 := by
    have h53 : Real.log (10 : ℝ) < 53 / 23 :=
      log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith
  have hlogx0 : Real.log (161 / 10 : ℝ) ≤ 14 / 5 :=
    (log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le
  have hRc : (({11, 23, 47, 59} : Finset ℕ).card : ℝ) = 4 := by norm_num
  exact pi60_le_of_params ({11, 23, 47, 59} : Finset ℕ) (by decide) (10 ^ 7) (by decide) X hX
    (161 / 10) (371 / 23) (14 / 5) (1 / 500) (71 / 100)
    (by norm_num) hx0_lo hx0_hi hlogx0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [hRc]; norm_num)

private lemma pi60_4_le_10_pow_8 (X : ℕ) (hX : 10 ^ 8 ≤ X) :
    (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
      p % 60 ∈ ({11, 23, 47, 59} : Finset ℕ))).card : ℝ) ≤
      (69 / 100 : ℝ) * (X : ℝ) / Real.log (X : ℝ) := by
  have hx0_lo : (92 / 5 : ℝ) ≤ Real.log ((10 ^ 8 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
  have hx0_hi : Real.log ((10 ^ 8 : ℕ) : ℝ) ≤ 424 / 23 := by
    have h53 : Real.log (10 : ℝ) < 53 / 23 :=
      log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith
  have hlogx0 : Real.log (92 / 5 : ℝ) ≤ 44 / 15 :=
    (log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le
  have hRc : (({11, 23, 47, 59} : Finset ℕ).card : ℝ) = 4 := by norm_num
  exact pi60_le_of_params ({11, 23, 47, 59} : Finset ℕ) (by decide) (10 ^ 8) (by decide) X hX
    (92 / 5) (424 / 23) (44 / 15) (1 / 1000) (69 / 100)
    (by norm_num) hx0_lo hx0_hi hlogx0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [hRc]; norm_num)

private lemma pi60_4_le_10_pow_10 (X : ℕ) (hX : 10 ^ 10 ≤ X) :
    (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
      p % 60 ∈ ({11, 23, 47, 59} : Finset ℕ))).card : ℝ) ≤
      (33 / 50 : ℝ) * (X : ℝ) / Real.log (X : ℝ) := by
  have hx0_lo : (23 : ℝ) ≤ Real.log ((10 ^ 10 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
  have hx0_hi : Real.log ((10 ^ 10 : ℕ) : ℝ) ≤ 530 / 23 := by
    have h53 : Real.log (10 : ℝ) < 53 / 23 :=
      log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith
  have hlogx0 : Real.log (23 : ℝ) ≤ 22 / 7 :=
    (log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le
  have hRc : (({11, 23, 47, 59} : Finset ℕ).card : ℝ) = 4 := by norm_num
  exact pi60_le_of_params ({11, 23, 47, 59} : Finset ℕ) (by decide) (10 ^ 10) (by decide) X hX
    23 (530 / 23) (22 / 7) (1 / 10000) (33 / 50)
    (by norm_num) hx0_lo hx0_hi hlogx0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [hRc]; norm_num)

private lemma pi60_4_le_10_pow_14 (X : ℕ) (hX : 10 ^ 14 ≤ X) :
    (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
      p % 60 ∈ ({11, 23, 47, 59} : Finset ℕ))).card : ℝ) ≤
      (63 / 100 : ℝ) * (X : ℝ) / Real.log (X : ℝ) := by
  have hx0_lo : (161 / 5 : ℝ) ≤ Real.log ((10 ^ 14 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
  have hx0_hi : Real.log ((10 ^ 14 : ℕ) : ℝ) ≤ 742 / 23 := by
    have h53 : Real.log (10 : ℝ) < 53 / 23 :=
      log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith
  have hlogx0 : Real.log (161 / 5 : ℝ) ≤ 7 / 2 :=
    (log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le
  have hRc : (({11, 23, 47, 59} : Finset ℕ).card : ℝ) = 4 := by norm_num
  exact pi60_le_of_params ({11, 23, 47, 59} : Finset ℕ) (by decide) (10 ^ 14) (by decide) X hX
    (161 / 5) (742 / 23) (7 / 2) (1 / 100000) (63 / 100)
    (by norm_num) hx0_lo hx0_hi hlogx0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [hRc]; norm_num)

private lemma pi60_4_le_10_pow_20 (X : ℕ) (hX : 10 ^ 20 ≤ X) :
    (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
      p % 60 ∈ ({11, 23, 47, 59} : Finset ℕ))).card : ℝ) ≤
      (61 / 100 : ℝ) * (X : ℝ) / Real.log (X : ℝ) := by
  have hx0_lo : (46 : ℝ) ≤ Real.log ((10 ^ 20 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
  have hx0_hi : Real.log ((10 ^ 20 : ℕ) : ℝ) ≤ 1060 / 23 := by
    have h53 : Real.log (10 : ℝ) < 53 / 23 :=
      log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith
  have hlogx0 : Real.log (46 : ℝ) ≤ 39 / 10 :=
    (log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le
  have hRc : (({11, 23, 47, 59} : Finset ℕ).card : ℝ) = 4 := by norm_num
  exact pi60_le_of_params ({11, 23, 47, 59} : Finset ℕ) (by decide) (10 ^ 20) (by decide) X hX
    46 (1060 / 23) (39 / 10) (1 / 1000000) (61 / 100)
    (by norm_num) hx0_lo hx0_hi hlogx0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [hRc]; norm_num)

private lemma pi60_3_le_10_pow_7 (X : ℕ) (hX : 10 ^ 7 ≤ X) :
    (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
      p % 60 ∈ ({23, 47, 59} : Finset ℕ))).card : ℝ) ≤
      (27 / 50 : ℝ) * (X : ℝ) / Real.log (X : ℝ) := by
  have hx0_lo : (161 / 10 : ℝ) ≤ Real.log ((10 ^ 7 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
  have hx0_hi : Real.log ((10 ^ 7 : ℕ) : ℝ) ≤ 371 / 23 := by
    have h53 : Real.log (10 : ℝ) < 53 / 23 :=
      log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith
  have hlogx0 : Real.log (161 / 10 : ℝ) ≤ 14 / 5 :=
    (log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le
  have hRc : (({23, 47, 59} : Finset ℕ).card : ℝ) = 3 := by norm_num
  exact pi60_le_of_params ({23, 47, 59} : Finset ℕ) (by decide) (10 ^ 7) (by decide) X hX
    (161 / 10) (371 / 23) (14 / 5) (1 / 500) (27 / 50)
    (by norm_num) hx0_lo hx0_hi hlogx0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [hRc]; norm_num)

private lemma pi60_3_le_10_pow_8 (X : ℕ) (hX : 10 ^ 8 ≤ X) :
    (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
      p % 60 ∈ ({23, 47, 59} : Finset ℕ))).card : ℝ) ≤
      (13 / 25 : ℝ) * (X : ℝ) / Real.log (X : ℝ) := by
  have hx0_lo : (92 / 5 : ℝ) ≤ Real.log ((10 ^ 8 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
  have hx0_hi : Real.log ((10 ^ 8 : ℕ) : ℝ) ≤ 424 / 23 := by
    have h53 : Real.log (10 : ℝ) < 53 / 23 :=
      log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith
  have hlogx0 : Real.log (92 / 5 : ℝ) ≤ 44 / 15 :=
    (log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le
  have hRc : (({23, 47, 59} : Finset ℕ).card : ℝ) = 3 := by norm_num
  exact pi60_le_of_params ({23, 47, 59} : Finset ℕ) (by decide) (10 ^ 8) (by decide) X hX
    (92 / 5) (424 / 23) (44 / 15) (1 / 1000) (13 / 25)
    (by norm_num) hx0_lo hx0_hi hlogx0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [hRc]; norm_num)

private lemma pi60_3_le_10_pow_10 (X : ℕ) (hX : 10 ^ 10 ≤ X) :
    (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
      p % 60 ∈ ({23, 47, 59} : Finset ℕ))).card : ℝ) ≤
      (49 / 100 : ℝ) * (X : ℝ) / Real.log (X : ℝ) := by
  have hx0_lo : (23 : ℝ) ≤ Real.log ((10 ^ 10 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
  have hx0_hi : Real.log ((10 ^ 10 : ℕ) : ℝ) ≤ 530 / 23 := by
    have h53 : Real.log (10 : ℝ) < 53 / 23 :=
      log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith
  have hlogx0 : Real.log (23 : ℝ) ≤ 22 / 7 :=
    (log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le
  have hRc : (({23, 47, 59} : Finset ℕ).card : ℝ) = 3 := by norm_num
  exact pi60_le_of_params ({23, 47, 59} : Finset ℕ) (by decide) (10 ^ 10) (by decide) X hX
    23 (530 / 23) (22 / 7) (1 / 10000) (49 / 100)
    (by norm_num) hx0_lo hx0_hi hlogx0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [hRc]; norm_num)

private lemma pi60_3_le_10_pow_14 (X : ℕ) (hX : 10 ^ 14 ≤ X) :
    (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
      p % 60 ∈ ({23, 47, 59} : Finset ℕ))).card : ℝ) ≤
      (47 / 100 : ℝ) * (X : ℝ) / Real.log (X : ℝ) := by
  have hx0_lo : (161 / 5 : ℝ) ≤ Real.log ((10 ^ 14 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
  have hx0_hi : Real.log ((10 ^ 14 : ℕ) : ℝ) ≤ 742 / 23 := by
    have h53 : Real.log (10 : ℝ) < 53 / 23 :=
      log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith
  have hlogx0 : Real.log (161 / 5 : ℝ) ≤ 7 / 2 :=
    (log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le
  have hRc : (({23, 47, 59} : Finset ℕ).card : ℝ) = 3 := by norm_num
  exact pi60_le_of_params ({23, 47, 59} : Finset ℕ) (by decide) (10 ^ 14) (by decide) X hX
    (161 / 5) (742 / 23) (7 / 2) (1 / 100000) (47 / 100)
    (by norm_num) hx0_lo hx0_hi hlogx0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [hRc]; norm_num)

private lemma pi60_3_le_10_pow_20 (X : ℕ) (hX : 10 ^ 20 ≤ X) :
    (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
      p % 60 ∈ ({23, 47, 59} : Finset ℕ))).card : ℝ) ≤
      (23 / 50 : ℝ) * (X : ℝ) / Real.log (X : ℝ) := by
  have hx0_lo : (46 : ℝ) ≤ Real.log ((10 ^ 20 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
  have hx0_hi : Real.log ((10 ^ 20 : ℕ) : ℝ) ≤ 1060 / 23 := by
    have h53 : Real.log (10 : ℝ) < 53 / 23 :=
      log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith
  have hlogx0 : Real.log (46 : ℝ) ≤ 39 / 10 :=
    (log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le
  have hRc : (({23, 47, 59} : Finset ℕ).card : ℝ) = 3 := by norm_num
  exact pi60_le_of_params ({23, 47, 59} : Finset ℕ) (by decide) (10 ^ 20) (by decide) X hX
    46 (1060 / 23) (39 / 10) (1 / 1000000) (23 / 50)
    (by norm_num) hx0_lo hx0_hi hlogx0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [hRc]; norm_num)

private lemma prime_le_100_cases {q : ℕ} (hq : q.Prime) (hq100 : q ≤ 100) :
    q ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97} : Finset ℕ) := by
  have hlt : q < 101 := by omega
  interval_cases q <;> first | exact absurd hq (by decide) | decide

private lemma prime_le_97_gt10_cases {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (h97 : p ≤ 97) :
    p ∈ ({11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97} : Finset ℕ) := by
  have hlt : p < 98 := by omega
  interval_cases p <;> first | exact absurd hp (by decide) | decide

private lemma p60_10000_data_gen (R : Finset ℕ) (hR_gt10 : ∀ r ∈ R, 11 ≤ r ∧ r < 60)
    (cnt sum_val : ℕ)
    (hdec : let P97 : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97}
      let P11_97 : Finset ℕ := {11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97}
      let T := ((Finset.Icc 1 10000).filter (fun p => p % 60 ∈ R)).filter (fun p =>
        p ∈ P11_97 ∨ (2 ≤ p ∧ ∀ q ∈ P97, p % q ≠ 0))
      T.card = cnt ∧ ∑ p ∈ T, (1000000 + p - 1) / p = sum_val) :
    cnt ≤ ((Finset.Icc 1 10000).filter (fun p => p.Prime ∧ p % 60 ∈ R)).card ∧
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ≤ 10000 ∧ p % 60 ∈ R) →
      ∑ p ∈ S, (1 / (p : ℝ)) ≤ (sum_val : ℝ) / 1000000 := by
  let P97 : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97}
  let P11_97 : Finset ℕ := {11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97}
  let T := ((Finset.Icc 1 10000).filter (fun p => p % 60 ∈ R)).filter (fun p =>
    p ∈ P11_97 ∨ (2 ≤ p ∧ ∀ q ∈ P97, p % q ≠ 0))
  have hP97_pr : ∀ q ∈ P97, q.Prime := by decide
  have hP97_le : ∀ q ∈ P97, q ≤ 97 := by decide
  have hP11_pr : ∀ q ∈ P11_97, q.Prime := by decide
  have hT_dec : T.card = cnt ∧ ∑ p ∈ T, (1000000 + p - 1) / p = sum_val := hdec
  have hT_eq : T = (Finset.Icc 1 10000).filter (fun p => p.Prime ∧ p % 60 ∈ R) := by
    ext p
    simp only [T, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, h10k⟩, hmod⟩, hcond⟩
      refine ⟨⟨h1, h10k⟩, ?_, hmod⟩
      rcases hcond with hp11 | ⟨hp2, hdiv⟩
      · exact hP11_pr p hp11
      · by_contra hnp
        let q := p.minFac
        have hq_pr : q.Prime := Nat.minFac_prime (by omega)
        have hq_sq : q * q ≤ p := by
          have := Nat.minFac_sq_le_self (by omega) hnp
          simpa [sq] using this
        have hq_le : q ≤ 100 := by
          by_contra h101
          have : 101 ≤ q := by omega
          have : 10201 ≤ q * q := by nlinarith
          omega
        have hq_mem : q ∈ P97 := prime_le_100_cases hq_pr hq_le
        have hqm : p % q = 0 := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd p)
        exact hdiv q hq_mem hqm
    · rintro ⟨⟨h1, h10k⟩, hp, hmod⟩
      refine ⟨⟨⟨h1, h10k⟩, hmod⟩, ?_⟩
      by_cases hp97 : p ≤ 97
      · left
        have hp_ge11 : 11 ≤ p := by
          have := (hR_gt10 (p % 60) hmod).1
          omega
        exact prime_le_97_gt10_cases hp hp_ge11 hp97
      · right
        refine ⟨hp.two_le, fun q hq hmod0 => ?_⟩
        have hqp : q ∣ p := Nat.dvd_of_mod_eq_zero hmod0
        have hq_eq : p = q := (Nat.Prime.dvd_iff_eq hp (hP97_pr q hq).ne_one).mp hqp
        have hq_le := hP97_le q hq
        omega
  constructor
  · rw [← hT_eq]; exact le_of_eq hT_dec.1.symm
  · intro S hS
    have hsub : S ⊆ T := by
      intro p hpS
      obtain ⟨hp, hp10k, hmod⟩ := hS p hpS
      rw [hT_eq, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hp.one_lt.le, hp10k⟩, hp, hmod⟩
    have hsum_le : ∑ p ∈ S, (1 / (p : ℝ)) ≤ ∑ p ∈ T, (1 / (p : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    have hT_le : ∑ p ∈ T, (1 / (p : ℝ)) ≤ (sum_val : ℝ) / 1000000 := by
      have hterm : ∀ p ∈ T, (1 / (p : ℝ)) ≤ (((1000000 + p - 1) / p : ℕ) : ℝ) / 1000000 := by
        intro p hp
        have hp_pos : 0 < p := by
          rw [hT_eq, Finset.mem_filter] at hp; exact hp.2.1.pos
        have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_pos
        have hnat : 1000000 ≤ p * ((1000000 + p - 1) / p) := by
          have hlt := Nat.lt_mul_div_succ (1000000 + p - 1) hp_pos
          have heq : p * ((1000000 + p - 1) / p + 1) = p * ((1000000 + p - 1) / p) + p := by ring
          rw [heq] at hlt
          omega
        have hreal : (1000000 : ℝ) ≤ (p : ℝ) * (((1000000 + p - 1) / p : ℕ) : ℝ) := by
          exact_mod_cast hnat
        rw [div_le_div_iff₀ hpR (by norm_num)]
        linarith
      calc ∑ p ∈ T, (1 / (p : ℝ))
          ≤ ∑ p ∈ T, (((1000000 + p - 1) / p : ℕ) : ℝ) / 1000000 := Finset.sum_le_sum hterm
        _ = (∑ p ∈ T, (((1000000 + p - 1) / p : ℕ) : ℝ)) / 1000000 := (Finset.sum_div _ _ _).symm
        _ = (sum_val : ℝ) / 1000000 := by
            have : (∑ p ∈ T, (((1000000 + p - 1) / p : ℕ) : ℝ)) = (sum_val : ℝ) := by
              exact_mod_cast hT_dec.2
            rw [this]
    exact hsum_le.trans hT_le

private lemma p60_4_10000_data :
    307 ≤ ((Finset.Icc 1 10000).filter (fun p => p.Prime ∧
      p % 60 ∈ ({11, 23, 47, 59} : Finset ℕ))).card ∧
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ≤ 10000 ∧ p % 60 ∈ ({11, 23, 47, 59} : Finset ℕ)) →
      ∑ p ∈ S, (1 / (p : ℝ)) ≤ (368796 : ℝ) / 1000000 := by
  exact p60_10000_data_gen ({11, 23, 47, 59} : Finset ℕ) (by decide) 307 368796 (by decide +kernel)

private lemma p60_3_10000_data :
    229 ≤ ((Finset.Icc 1 10000).filter (fun p => p.Prime ∧
      p % 60 ∈ ({23, 47, 59} : Finset ℕ))).card ∧
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ≤ 10000 ∧ p % 60 ∈ ({23, 47, 59} : Finset ℕ)) →
      ∑ p ∈ S, (1 / (p : ℝ)) ≤ (218945 : ℝ) / 1000000 := by
  exact p60_10000_data_gen ({23, 47, 59} : Finset ℕ) (by decide) 229 218945 (by decide +kernel)
private lemma sum_Ioc_split {f : ℕ → ℝ} {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∑ j ∈ Finset.Ioc a c, f j = (∑ j ∈ Finset.Ioc a b, f j) + ∑ j ∈ Finset.Ioc b c, f j := by
  have hunion : Finset.Ioc a c = Finset.Ioc a b ∪ Finset.Ioc b c := by
    ext j; simp only [Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Ioc a b) (Finset.Ioc b c) :=
    Finset.disjoint_left.mpr fun j h1 h2 => by simp at h1 h2; omega
  rw [hunion, Finset.sum_union hdisj]

private lemma sum_Ioc_sub_shift_le (K a b : ℕ) (ha : K + 2 ≤ a) (hab : a ≤ b) :
    ∑ j ∈ Finset.Ioc a b, (1 / ((j : ℝ) - (K : ℝ))) ≤
      Real.log ((b : ℝ) - (K : ℝ)) - Real.log ((a : ℝ) - (K : ℝ)) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    have hsplit : Finset.Ioc a (b + 1) = insert (b + 1) (Finset.Ioc a b) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Ioc]; omega
    have hnot : b + 1 ∉ Finset.Ioc a b := by simp
    rw [hsplit, Finset.sum_insert hnot]
    have hstep : 1 / (((b + 1 : ℕ) : ℝ) - (K : ℝ)) ≤
        Real.log (((b + 1 : ℕ) : ℝ) - (K : ℝ)) - Real.log ((b : ℝ) - (K : ℝ)) := by
      have hbK : (1 : ℝ) ≤ (b : ℝ) - (K : ℝ) := by
        have : K + 2 ≤ b := ha.trans hb
        have : ((K + 2 : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast this
        push_cast at this; linarith
      have hp1 : (0 : ℝ) < ((b + 1 : ℕ) : ℝ) - (K : ℝ) := by push_cast; linarith
      have htan := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < (b : ℝ) - (K : ℝ)) hp1)
      rw [Real.log_div (by linarith) hp1.ne'] at htan
      have heq : ((b : ℝ) - (K : ℝ)) / (((b + 1 : ℕ) : ℝ) - (K : ℝ)) - 1 =
          -(1 / (((b + 1 : ℕ) : ℝ) - (K : ℝ))) := by
        push_cast; field_simp [show (b : ℝ) + 1 - (K : ℝ) ≠ 0 by linarith]; ring
      linarith
    linarith

private lemma sum_Ioc_log_log_le (c : ℝ) (hc : 1 ≤ c) (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ j ∈ Finset.Ioc a b, (1 / ((j : ℝ) * Real.log (c * (j : ℝ)))) ≤
      Real.log (Real.log (c * (b : ℝ))) - Real.log (Real.log (c * (a : ℝ))) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    have hsplit : Finset.Ioc a (b + 1) = insert (b + 1) (Finset.Ioc a b) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Ioc]; omega
    have hnot : b + 1 ∉ Finset.Ioc a b := by simp
    rw [hsplit, Finset.sum_insert hnot]
    have hstep : 1 / (((b + 1 : ℕ) : ℝ) * Real.log (c * ((b + 1 : ℕ) : ℝ))) ≤
        Real.log (Real.log (c * ((b + 1 : ℕ) : ℝ))) - Real.log (Real.log (c * (b : ℝ))) := by
      have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (ha.trans hb)
      have hbp : (0 : ℝ) < (b : ℝ) := by linarith
      have hbp1 : (0 : ℝ) < ((b + 1 : ℕ) : ℝ) := by positivity
      have h1 : 1 / ((b + 1 : ℕ) : ℝ) ≤ Real.log (c * ((b + 1 : ℕ) : ℝ)) - Real.log (c * (b : ℝ)) := by
        have hlogdiff : Real.log (c * ((b + 1 : ℕ) : ℝ)) - Real.log (c * (b : ℝ)) =
            Real.log ((b + 1 : ℕ) : ℝ) - Real.log (b : ℝ) := by
          rw [Real.log_mul (by linarith) hbp1.ne', Real.log_mul (by linarith) hbp.ne']
          ring
        rw [hlogdiff]
        have htan := Real.log_le_sub_one_of_pos (div_pos hbp hbp1)
        rw [Real.log_div hbp.ne' hbp1.ne'] at htan
        have heq : (b : ℝ) / ((b + 1 : ℕ) : ℝ) - 1 = -(1 / ((b + 1 : ℕ) : ℝ)) := by
          push_cast; field_simp [hbp1.ne']; ring
        linarith
      have hx_pos : 0 < Real.log (c * (b : ℝ)) := by
        have h2le : 2 ≤ c * (b : ℝ) := by nlinarith
        exact (Real.log_pos (by norm_num)).trans_le (Real.log_le_log (by norm_num) h2le)
      have hy_pos : 0 < Real.log (c * ((b + 1 : ℕ) : ℝ)) := by
        have h2le : 2 ≤ c * ((b + 1 : ℕ) : ℝ) := by push_cast; nlinarith
        exact (Real.log_pos (by norm_num)).trans_le (Real.log_le_log (by norm_num) h2le)
      have h2 := Real.log_le_sub_one_of_pos (div_pos hx_pos hy_pos)
      rw [Real.log_div hx_pos.ne' hy_pos.ne'] at h2
      have h3 : (Real.log (c * ((b + 1 : ℕ) : ℝ)) - Real.log (c * (b : ℝ))) /
          Real.log (c * ((b + 1 : ℕ) : ℝ)) ≤
          Real.log (Real.log (c * ((b + 1 : ℕ) : ℝ))) - Real.log (Real.log (c * (b : ℝ))) := by
        have heq : (Real.log (c * ((b + 1 : ℕ) : ℝ)) - Real.log (c * (b : ℝ))) /
            Real.log (c * ((b + 1 : ℕ) : ℝ)) =
            1 - Real.log (c * (b : ℝ)) / Real.log (c * ((b + 1 : ℕ) : ℝ)) := by
          field_simp [hy_pos.ne']
        linarith
      have h4 : 1 / (((b + 1 : ℕ) : ℝ) * Real.log (c * ((b + 1 : ℕ) : ℝ))) =
          (1 / ((b + 1 : ℕ) : ℝ)) / Real.log (c * ((b + 1 : ℕ) : ℝ)) := by ring
      rw [h4]
      exact (div_le_div_of_nonneg_right h1 hy_pos.le).trans h3
    linarith

private lemma asymp_rank_inv_le_clean (R : Finset ℕ) (X0 : ℕ) (C : ℝ) (hC_pos : 0 < C)
    (hlogX0 : 10 * C ≤ Real.log (X0 : ℝ))
    (hpi : ∀ X, X0 ≤ X →
      (((Finset.Icc 1 X).filter (fun p => p.Prime ∧ p % 60 ∈ R)).card : ℝ) ≤
        C * (X : ℝ) / Real.log (X : ℝ))
    {j q : ℕ} (hj_gt : (((Finset.Icc 1 X0).filter (fun p => p.Prime ∧ p % 60 ∈ R)).card : ℝ) < (j : ℝ))
    (hq : j ≤ ((Finset.Icc 1 q).filter (fun p => p.Prime ∧ p % 60 ∈ R)).card)
    (hj1 : 1 ≤ j) (hq1 : 1 ≤ q) :
    1 / (q : ℝ) ≤ C / ((j : ℝ) * Real.log (10 * (j : ℝ))) := by
  have hX0q : X0 ≤ q := by
    by_contra hlt
    have hqlt : q ≤ X0 := by omega
    have hsub : (Finset.Icc 1 q).filter (fun p => p.Prime ∧ p % 60 ∈ R) ⊆
        (Finset.Icc 1 X0).filter (fun p => p.Prime ∧ p % 60 ∈ R) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.trans hqlt⟩, hp.2⟩
    have hcard : ((Finset.Icc 1 q).filter (fun p => p.Prime ∧ p % 60 ∈ R)).card ≤
        ((Finset.Icc 1 X0).filter (fun p => p.Prime ∧ p % 60 ∈ R)).card := Finset.card_le_card hsub
    have hcardR : (((Finset.Icc 1 q).filter (fun p => p.Prime ∧ p % 60 ∈ R)).card : ℝ) < (j : ℝ) :=
      lt_of_le_of_lt (by exact_mod_cast hcard) hj_gt
    have hjR : (j : ℝ) ≤ ((Finset.Icc 1 q).filter (fun p => p.Prime ∧ p % 60 ∈ R)).card := by exact_mod_cast hq
    linarith
  have hjR : (j : ℝ) ≤ C * (q : ℝ) / Real.log (q : ℝ) :=
    (by exact_mod_cast hq : (j : ℝ) ≤ _).trans (hpi q hX0q)
  have hX0_pos : (0 : ℝ) < (X0 : ℝ) := by
    by_contra h0
    have : X0 = 0 := by
      have hle : X0 ≤ 0 := by exact_mod_cast (by linarith : (X0 : ℝ) ≤ 0)
      omega
    rw [this, Nat.cast_zero, Real.log_zero] at hlogX0; linarith
  have hlogq : 10 * C ≤ Real.log (q : ℝ) := hlogX0.trans (Real.log_le_log hX0_pos (by exact_mod_cast hX0q))
  have hlogq_pos : 0 < Real.log (q : ℝ) := by linarith
  have hq_ge : (1 / C) * (j : ℝ) * Real.log (q : ℝ) ≤ (q : ℝ) := by
    have h1 := (le_div_iff₀ hlogq_pos).mp hjR
    calc (1 / C) * (j : ℝ) * Real.log (q : ℝ) = (j : ℝ) * Real.log (q : ℝ) / C := by ring
      _ ≤ (C * (q : ℝ)) / C := div_le_div_of_nonneg_right h1 hC_pos.le
      _ = (q : ℝ) := by field_simp [hC_pos.ne']
  have h10j : 10 * (j : ℝ) ≤ (q : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlogq (by positivity : 0 ≤ (1 / C) * (j : ℝ))
    have heq : (1 / C) * (j : ℝ) * (10 * C) = 10 * (j : ℝ) := by field_simp [hC_pos.ne']
    linarith
  have hjpos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr hj1
  have h10j_log : Real.log (10 * (j : ℝ)) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by positivity) h10j
  have h10j_pos : 0 < Real.log (10 * (j : ℝ)) := by
    have hj1R : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    have : 2 ≤ 10 * (j : ℝ) := by linarith
    exact (Real.log_pos (by norm_num)).trans_le (Real.log_le_log (by norm_num) this)
  have hq_ge' : ((j : ℝ) * Real.log (10 * (j : ℝ))) / C ≤ (q : ℝ) := by
    have : (1 / C) * (j : ℝ) * Real.log (10 * (j : ℝ)) ≤ (1 / C) * (j : ℝ) * Real.log (q : ℝ) :=
      mul_le_mul_of_nonneg_left h10j_log (by positivity)
    have hdiv_eq : ((j : ℝ) * Real.log (10 * (j : ℝ))) / C =
        (1 / C) * (j : ℝ) * Real.log (10 * (j : ℝ)) := by ring
    linarith
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq1
  rw [div_le_div_iff₀ hq_pos (by positivity)]
  have h1 : (j : ℝ) * Real.log (10 * (j : ℝ)) ≤ (q : ℝ) * C :=
    (div_le_iff₀ hC_pos).mp hq_ge'
  linarith

private lemma tail_fin_sel_bound (R : Finset ℕ) (hR : ∀ r ∈ R, r < 60)
    (q j z c_D : ℕ) (L_lo div_coef : ℝ) (hz1 : 1 ≤ z) (hLlo_pos : 0 < L_lo)
    (hdiv_pos : 0 < div_coef) (hcoef : (R.card : ℝ) / 60 = 1 / div_coef)
    (hcD : ((Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)).card = c_D)
    (hLL : L_lo ≤ ∑ d ∈ (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30),
      (1 / (d.totient : ℝ)))
    (hjk : z + R.card * c_D ^ 2 < j)
    (hj_rk : j ≤ ((Finset.Icc 1 q).filter (fun p => p.Prime ∧ p % 60 ∈ R)).card)
    (hq_pos : 0 < q) :
    1 / (q : ℝ) ≤ 1 / (div_coef * L_lo * ((j : ℝ) - ((z : ℝ) + (R.card : ℝ) * (c_D : ℝ) ^ 2))) := by
  have hsel := selberg_pi60_le R hR q z hz1
  rw [hcD] at hsel
  have hsum_pos : 0 < ∑ d ∈ (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30),
      (1 / (d.totient : ℝ)) := lt_of_lt_of_le hLlo_pos hLL
  have hqR_nn : (0 : ℝ) ≤ (R.card : ℝ) * (q : ℝ) := by positivity
  have hdiv1 : (R.card : ℝ) * (q : ℝ) /
      (60 * ∑ d ∈ (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30),
        (1 / (d.totient : ℝ))) ≤
      (R.card : ℝ) * (q : ℝ) / (60 * L_lo) :=
    div_le_div_of_nonneg_left hqR_nn (by positivity) (by linarith only [hLL])
  have hdiv2 : (R.card : ℝ) * (q : ℝ) / (60 * L_lo) = (q : ℝ) / (div_coef * L_lo) := by
    calc (R.card : ℝ) * (q : ℝ) / (60 * L_lo)
        = ((R.card : ℝ) / 60) * ((q : ℝ) / L_lo) := by ring
      _ = (1 / div_coef) * ((q : ℝ) / L_lo) := by rw [hcoef]
      _ = (q : ℝ) / (div_coef * L_lo) := by ring
  have h1 : (j : ℝ) ≤ ((Finset.Icc 1 q).filter (fun p => p.Prime ∧ p % 60 ∈ R)).card := by
    exact_mod_cast hj_rk
  have hjR : (j : ℝ) ≤ (z : ℝ) + (q : ℝ) / (div_coef * L_lo) + (R.card : ℝ) * (c_D : ℝ) ^ 2 := by
    linarith only [h1, hsel, hdiv1, hdiv2]
  have hdiff_pos : (0 : ℝ) < (j : ℝ) - ((z : ℝ) + (R.card : ℝ) * (c_D : ℝ) ^ 2) := by
    have hlt : ((z + R.card * c_D ^ 2 : ℕ) : ℝ) < (j : ℝ) := by exact_mod_cast hjk
    push_cast at hlt
    linarith only [hlt]
  have hq_ge : div_coef * L_lo * ((j : ℝ) - ((z : ℝ) + (R.card : ℝ) * (c_D : ℝ) ^ 2)) ≤ (q : ℝ) := by
    have hsub : (j : ℝ) - ((z : ℝ) + (R.card : ℝ) * (c_D : ℝ) ^ 2) ≤ (q : ℝ) / (div_coef * L_lo) := by
      linarith only [hjR]
    have hmul := (le_div_iff₀ (mul_pos hdiv_pos hLlo_pos)).mp hsub
    rwa [mul_comm] at hmul
  exact one_div_le_one_div_of_le (mul_pos (mul_pos hdiv_pos hLlo_pos) hdiff_pos) hq_ge

private lemma tail_Ioc_shift_bound (ub : ℕ → ℝ) (K a b p q : ℕ) (coef rhs : ℝ)
    (ha : K + 2 ≤ a) (hab : a ≤ b) (hcoef : 0 ≤ coef) (hq : 0 < q)
    (hterm : ∀ j ∈ Finset.Ioc a b, ub j = coef * (1 / ((j : ℝ) - (K : ℝ))))
    (hlog : (((b - K : ℕ) : ℝ) / ((a - K : ℕ) : ℝ)) ^ q < (2.718 : ℝ) ^ p)
    (hrhs : coef * ((p : ℝ) / (q : ℝ)) = rhs) :
    ∑ j ∈ Finset.Ioc a b, ub j ≤ rhs := by
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have htele := sum_Ioc_sub_shift_le K a b ha hab
  have haK : (0 : ℝ) < (a : ℝ) - (K : ℝ) := by
    have : K + 2 ≤ a := ha
    have : ((K + 2 : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast this
    push_cast at this; linarith only [this]
  have hbK : (0 : ℝ) < (b : ℝ) - (K : ℝ) := by
    have : K + 2 ≤ b := ha.trans hab
    have : ((K + 2 : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast this
    push_cast at this; linarith only [this]
  have hsub_a : ((a - K : ℕ) : ℝ) = (a : ℝ) - (K : ℝ) := by rw [Nat.cast_sub (by omega)]
  have hsub_b : ((b - K : ℕ) : ℝ) = (b : ℝ) - (K : ℝ) := by rw [Nat.cast_sub (by omega)]
  have hdiv_eq : Real.log ((b : ℝ) - (K : ℝ)) - Real.log ((a : ℝ) - (K : ℝ)) =
      Real.log (((b - K : ℕ) : ℝ) / ((a - K : ℕ) : ℝ)) := by
    rw [hsub_a, hsub_b, Real.log_div hbK.ne' haK.ne']
  have hlog_pos : (0 : ℝ) < ((b - K : ℕ) : ℝ) / ((a - K : ℕ) : ℝ) := by
    rw [hsub_a, hsub_b]; exact div_pos hbK haK
  have hlog_lt := log_lt_of_pow_lt hlog_pos hq hlog
  have h1 : Real.log ((b : ℝ) - (K : ℝ)) - Real.log ((a : ℝ) - (K : ℝ)) ≤ (p : ℝ) / (q : ℝ) := by
    linarith only [hdiv_eq, hlog_lt]
  calc coef * ∑ j ∈ Finset.Ioc a b, (1 / ((j : ℝ) - (K : ℝ)))
      ≤ coef * (Real.log ((b : ℝ) - (K : ℝ)) - Real.log ((a : ℝ) - (K : ℝ))) :=
        mul_le_mul_of_nonneg_left htele hcoef
    _ ≤ coef * ((p : ℝ) / (q : ℝ)) := mul_le_mul_of_nonneg_left h1 hcoef
    _ = rhs := hrhs

private lemma tail_Ioc_loglog_bound (ub : ℕ → ℝ) (a b e1 e2 : ℕ) (C L : ℝ)
    (ha : 2 ≤ a) (hab : a ≤ b) (hC : 0 ≤ C) (he1 : 0 < e1) (he2 : 0 < e2)
    (ha_eq : (10 : ℝ) * (a : ℝ) = (10 : ℝ) ^ e1)
    (hb_eq : (10 : ℝ) * (b : ℝ) = (10 : ℝ) ^ e2)
    (hterm : ∀ j ∈ Finset.Ioc a b, ub j = C * (1 / ((j : ℝ) * Real.log (10 * (j : ℝ)))))
    (hlog : Real.log ((e2 : ℝ) / (e1 : ℝ)) ≤ L) :
    ∑ j ∈ Finset.Ioc a b, ub j ≤ C * L := by
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have htele := sum_Ioc_log_log_le 10 (by norm_num) a b ha hab
  have hlp : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  have he1_pos : (0 : ℝ) < (e1 : ℝ) := by exact_mod_cast he1
  have he2_pos : (0 : ℝ) < (e2 : ℝ) := by exact_mod_cast he2
  have hdiv_eq : Real.log (Real.log (10 * (b : ℝ))) - Real.log (Real.log (10 * (a : ℝ))) =
      Real.log ((e2 : ℝ) / (e1 : ℝ)) := by
    rw [ha_eq, hb_eq, Real.log_pow, Real.log_pow,
      ← Real.log_div (mul_pos he2_pos hlp).ne' (mul_pos he1_pos hlp).ne']
    congr 1
    field_simp [hlp.ne', he1_pos.ne']
  exact mul_le_mul_of_nonneg_left (by linarith only [htele, hdiv_eq, hlog]) hC

private lemma tail_Ioc_top_bound (ub : ℕ → ℝ) (X_hi E : ℕ) (C tail_log_hi : ℝ)
    (hE : 20 ≤ E) (hXhi_ge : 10 ^ 19 ≤ X_hi) (hXhi_le : X_hi ≤ 1001 * 10 ^ (E - 3))
    (hC : 0 ≤ C)
    (hterm : ∀ j ∈ Finset.Ioc 10000000000000000000 X_hi,
      ub j = C * (1 / ((j : ℝ) * Real.log (10 * (j : ℝ)))))
    (htail_log : Real.log (((E + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) -
      Real.log (20 * Real.log 10) ≤ tail_log_hi) :
    ∑ j ∈ Finset.Ioc 10000000000000000000 X_hi, ub j ≤ C * tail_log_hi := by
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have htele := sum_Ioc_log_log_le 10 (by norm_num) 10000000000000000000 X_hi (by norm_num) hXhi_ge
  have hXpos : 0 < X_hi := lt_of_lt_of_le (by norm_num) hXhi_ge
  have h10X_le : Real.log (10 * (X_hi : ℝ)) ≤ ((E + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000 := by
    have hle_R : (10 : ℝ) * (X_hi : ℝ) ≤ (1001 / 1000 : ℝ) * (10 : ℝ) ^ (E + 1) := by
      have h1 : (X_hi : ℝ) ≤ (1001 : ℝ) * (10 : ℝ) ^ (E - 3) := by exact_mod_cast hXhi_le
      have hpow : (10 : ℝ) ^ (E + 1) = (10 : ℝ) ^ (E - 3) * (10 : ℝ) ^ 4 := by
        rw [← pow_add, show E - 3 + 4 = E + 1 by omega]
      have hE1 : (10 : ℝ) * (1001 : ℝ) * (10 : ℝ) ^ (E - 3) =
          (1001 / 1000 : ℝ) * (10 : ℝ) ^ (E + 1) := by rw [hpow]; ring
      nlinarith only [h1, hE1]
    have hXhiR : (0 : ℝ) < (X_hi : ℝ) := by exact_mod_cast hXpos
    have hlog_le : Real.log (10 * (X_hi : ℝ)) ≤ Real.log ((1001 / 1000 : ℝ) * (10 : ℝ) ^ (E + 1)) :=
      Real.log_le_log (by positivity) hle_R
    conv_rhs at hlog_le => rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h1001 : Real.log (1001 / 1000 : ℝ) ≤ 1 / 1000 := by
      linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1001 / 1000)]
    linarith only [hlog_le, h1001]
  have hlog20_eq : Real.log (Real.log (10 * ((10000000000000000000 : ℕ) : ℝ))) =
      Real.log (20 * Real.log 10) := by
    have h10_20 : (10 : ℝ) * ((10000000000000000000 : ℕ) : ℝ) = (10 : ℝ) ^ 20 := by norm_num
    rw [h10_20, Real.log_pow]
    norm_num
  have h2le : (2 : ℝ) ≤ 10 * (X_hi : ℝ) := by
    have : (1 : ℝ) ≤ (X_hi : ℝ) := by exact_mod_cast hXpos
    linarith only [this]
  have hlog_pos2 : 0 < Real.log (10 * (X_hi : ℝ)) :=
    (Real.log_pos (by norm_num)).trans_le (Real.log_le_log (by norm_num) h2le)
  have hlog_top : Real.log (Real.log (10 * (X_hi : ℝ))) ≤
      Real.log (((E + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) :=
    Real.log_le_log hlog_pos2 h10X_le
  have hdiff : Real.log (Real.log (10 * (X_hi : ℝ))) -
      Real.log (Real.log (10 * ((10000000000000000000 : ℕ) : ℝ))) ≤ tail_log_hi := by
    linarith only [hlog20_eq, hlog_top, htail_log]
  exact mul_le_mul_of_nonneg_left (htele.trans hdiff) hC

private lemma tail_term_le_4 (P_gt : Finset ℕ) (hP_gt : ∀ p ∈ P_gt, p.Prime ∧ 10000 < p ∧
    p % 60 ∈ ({11, 23, 47, 59} : Finset ℕ)) :
    let q : Fin P_gt.card ↪o ℕ := P_gt.orderEmbOfFin rfl
    ∀ i : Fin P_gt.card, (1 / ((q i : ℕ) : ℝ)) ≤
      (let j := 308 + (i : ℕ)
      if j ≤ 800 then (1 : ℝ) / 10000
      else if j ≤ 10000 then (1000000 : ℝ) / (23238330 * ((j : ℝ) - 285))
      else if j ≤ 100000 then (1000000 : ℝ) / (27820335 * ((j : ℝ) - 2600))
      else if j ≤ 1000000 then (1000000 : ℝ) / (32278560 * ((j : ℝ) - 23404))
      else if j ≤ 10000000 then (71 / 100 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
      else if j ≤ 1000000000 then (69 / 100 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
      else if j ≤ 10000000000000 then (33 / 50 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
      else if j ≤ 10000000000000000000 then (63 / 100 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
      else (61 / 100 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))) := by
  let R4 : Finset ℕ := {11, 23, 47, 59}
  have hR4 : ∀ r ∈ R4, r < 60 := by decide
  have hR4_4 : R4.card = 4 := by decide
  have hR4_coef : (R4.card : ℝ) / 60 = 1 / 15 := by
    have : (R4.card : ℝ) = 4 := by exact_mod_cast hR4_4
    rw [this]; norm_num
  have hpi7_lt : (((Finset.Icc 1 (10 ^ 7)).filter (fun p => p.Prime ∧ p % 60 ∈ R4)).card : ℝ) < (1000001 : ℝ) := by
    have h1 := pi60_4_le_10_pow_7 (10 ^ 7) (le_refl _)
    have hlog : (161 / 10 : ℝ) ≤ Real.log ((10 ^ 7 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
    have h2 : (71 / 100 : ℝ) * ((10 ^ 7 : ℕ) : ℝ) / Real.log ((10 ^ 7 : ℕ) : ℝ) ≤
        (71 / 100 : ℝ) * ((10 ^ 7 : ℕ) : ℝ) / (161 / 10) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog
    have h3 : (71 / 100 : ℝ) * ((10 ^ 7 : ℕ) : ℝ) / (161 / 10) < 1000001 := by norm_num
    exact (h1.trans h2).trans_lt h3
  have hpi8_lt : (((Finset.Icc 1 (10 ^ 8)).filter (fun p => p.Prime ∧ p % 60 ∈ R4)).card : ℝ) < (10000001 : ℝ) := by
    have h1 := pi60_4_le_10_pow_8 (10 ^ 8) (le_refl _)
    have hlog : (92 / 5 : ℝ) ≤ Real.log ((10 ^ 8 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
    have h2 : (69 / 100 : ℝ) * ((10 ^ 8 : ℕ) : ℝ) / Real.log ((10 ^ 8 : ℕ) : ℝ) ≤
        (69 / 100 : ℝ) * ((10 ^ 8 : ℕ) : ℝ) / (92 / 5) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog
    have h3 : (69 / 100 : ℝ) * ((10 ^ 8 : ℕ) : ℝ) / (92 / 5) < 10000001 := by norm_num
    exact (h1.trans h2).trans_lt h3
  have hpi10_lt : (((Finset.Icc 1 (10 ^ 10)).filter (fun p => p.Prime ∧ p % 60 ∈ R4)).card : ℝ) < (1000000001 : ℝ) := by
    have h1 := pi60_4_le_10_pow_10 (10 ^ 10) (le_refl _)
    have hlog : (23 : ℝ) ≤ Real.log ((10 ^ 10 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
    have h2 : (33 / 50 : ℝ) * ((10 ^ 10 : ℕ) : ℝ) / Real.log ((10 ^ 10 : ℕ) : ℝ) ≤
        (33 / 50 : ℝ) * ((10 ^ 10 : ℕ) : ℝ) / 23 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog
    have h3 : (33 / 50 : ℝ) * ((10 ^ 10 : ℕ) : ℝ) / 23 < 1000000001 := by norm_num
    exact (h1.trans h2).trans_lt h3
  have hpi14_lt : (((Finset.Icc 1 (10 ^ 14)).filter (fun p => p.Prime ∧ p % 60 ∈ R4)).card : ℝ) <
      (10000000000001 : ℝ) := by
    have h1 := pi60_4_le_10_pow_14 (10 ^ 14) (le_refl _)
    have hlog : (161 / 5 : ℝ) ≤ Real.log ((10 ^ 14 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
    have h2 : (63 / 100 : ℝ) * ((10 ^ 14 : ℕ) : ℝ) / Real.log ((10 ^ 14 : ℕ) : ℝ) ≤
        (63 / 100 : ℝ) * ((10 ^ 14 : ℕ) : ℝ) / (161 / 5) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog
    have h3 : (63 / 100 : ℝ) * ((10 ^ 14 : ℕ) : ℝ) / (161 / 5) < 10000000000001 := by norm_num
    exact (h1.trans h2).trans_lt h3
  have hpi20_lt : (((Finset.Icc 1 (10 ^ 20)).filter (fun p => p.Prime ∧ p % 60 ∈ R4)).card : ℝ) <
      (10000000000000000001 : ℝ) := by
    have h1 := pi60_4_le_10_pow_20 (10 ^ 20) (le_refl _)
    have hlog : (46 : ℝ) ≤ Real.log ((10 ^ 20 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
    have h2 : (61 / 100 : ℝ) * ((10 ^ 20 : ℕ) : ℝ) / Real.log ((10 ^ 20 : ℕ) : ℝ) ≤
        (61 / 100 : ℝ) * ((10 ^ 20 : ℕ) : ℝ) / 46 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog
    have h3 : (61 / 100 : ℝ) * ((10 ^ 20 : ℕ) : ℝ) / 46 < 10000000000000000001 := by norm_num
    exact (h1.trans h2).trans_lt h3
  intro q i
  let j := 308 + (i : ℕ)
  have hrank : 308 + (i : ℕ) ≤ ((Finset.Icc 1 (q i)).filter (fun p => p.Prime ∧ p % 60 ∈ R4)).card := by
    have hq_mem : q i ∈ P_gt := Finset.orderEmbOfFin_mem P_gt rfl i
    obtain ⟨_, hq_gt, _⟩ := hP_gt (q i) hq_mem
    let T0 := (Finset.Icc 1 10000).filter (fun p => p.Prime ∧ p % 60 ∈ R4)
    let Qi : Finset ℕ := (Finset.range ((i : ℕ) + 1)).attach.image
      (fun k => q ⟨k.1, by have := Finset.mem_range.mp k.2; omega⟩)
    have hT0_sub : T0 ⊆ (Finset.Icc 1 (q i)).filter (fun p => p.Prime ∧ p % 60 ∈ R4) := fun p hp => by
      rw [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.trans hq_gt.le⟩, hp.2⟩
    have hQi_sub : Qi ⊆ (Finset.Icc 1 (q i)).filter (fun p => p.Prime ∧ p % 60 ∈ R4) := fun p hp => by
      rcases Finset.mem_image.mp hp with ⟨k, _, rfl⟩
      have hk_le : (⟨k.1, by have := Finset.mem_range.mp k.2; omega⟩ : Fin P_gt.card) ≤ i :=
        Fin.mk_le_mk.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp k.2))
      obtain ⟨hk_pr, _, hk_mod⟩ := hP_gt (q ⟨k.1, by have := Finset.mem_range.mp k.2; omega⟩)
        (Finset.orderEmbOfFin_mem P_gt rfl _)
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hk_pr.one_lt.le, q.monotone hk_le⟩, hk_pr, hk_mod⟩
    have hdisj : Disjoint T0 Qi := Finset.disjoint_left.mpr fun p h1 h2 => by
      rw [Finset.mem_filter, Finset.mem_Icc] at h1
      rcases Finset.mem_image.mp h2 with ⟨k, _, rfl⟩
      obtain ⟨_, hk_gt, _⟩ := hP_gt (q ⟨k.1, by have := Finset.mem_range.mp k.2; omega⟩)
        (Finset.orderEmbOfFin_mem P_gt rfl _)
      omega
    have hQi_card : Qi.card = (i : ℕ) + 1 := by
      have hinj : Function.Injective (fun k : {x // x ∈ Finset.range ((i : ℕ) + 1)} =>
          q ⟨k.1, by have := Finset.mem_range.mp k.2; omega⟩) := by
        intro k1 k2 heq
        have hfk := q.injective heq
        have hv : k1.1 = k2.1 := by simpa using congrArg Fin.val hfk
        exact Subtype.ext hv
      rw [Finset.card_image_of_injective _ hinj, Finset.card_attach, Finset.card_range]
    have hT0_card : 307 ≤ T0.card := p60_4_10000_data.1
    calc 308 + (i : ℕ) = 307 + ((i : ℕ) + 1) := by ring
      _ ≤ T0.card + Qi.card := by omega
      _ = (T0 ∪ Qi).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ _ := Finset.card_le_card (Finset.union_subset hT0_sub hQi_sub)
  obtain ⟨hq_pr, hq_gt, _⟩ := hP_gt (q i) (Finset.orderEmbOfFin_mem P_gt rfl i)
  change 1 / ((q i : ℕ) : ℝ) ≤ _
  by_cases h1 : j ≤ 800
  · rw [if_pos h1]
    have : (10000 : ℝ) ≤ ((q i : ℕ) : ℝ) := by exact_mod_cast hq_gt.le
    exact one_div_le_one_div_of_le (by norm_num) this
  · rw [if_neg h1]
    by_cases h2 : j ≤ 10000
    · rw [if_pos h2]
      have hfin := tail_fin_sel_bound R4 hR4 (q i) j 29 8 (1549222 / 1000000) 15 (by decide)
        (by norm_num) (by norm_num) hR4_coef d29_bound.1 d29_bound.2 (by rw [hR4_4]; omega) hrank hq_pr.pos
      rw [show ((R4.card : ℝ) * ((8 : ℕ) : ℝ) ^ 2) = 4 * 64 by rw [show (R4.card : ℝ) = 4 by exact_mod_cast hR4_4]; norm_num,
        show ((29 : ℕ) : ℝ) + 4 * 64 = 285 by norm_num] at hfin
      refine hfin.trans_eq ?_
      rw [show (15 : ℝ) * (1549222 / 1000000) * ((j : ℝ) - 285) = (23238330 * ((j : ℝ) - 285)) / 1000000 by ring,
        one_div_div]
    · rw [if_neg h2]
      by_cases h3 : j ≤ 100000
      · rw [if_pos h3]
        have hfin := tail_fin_sel_bound R4 hR4 (q i) j 100 25 (1854689 / 1000000) 15 (by decide)
          (by norm_num) (by norm_num) hR4_coef d100_bound.1 d100_bound.2 (by rw [hR4_4]; omega) hrank hq_pr.pos
        rw [show ((R4.card : ℝ) * ((25 : ℕ) : ℝ) ^ 2) = 4 * 625 by rw [show (R4.card : ℝ) = 4 by exact_mod_cast hR4_4]; norm_num,
          show ((100 : ℕ) : ℝ) + 4 * 625 = 2600 by norm_num] at hfin
        refine hfin.trans_eq ?_
        rw [show (15 : ℝ) * (1854689 / 1000000) * ((j : ℝ) - 2600) = (27820335 * ((j : ℝ) - 2600)) / 1000000 by ring,
          one_div_div]
      · rw [if_neg h3]
        by_cases h4 : j ≤ 1000000
        · rw [if_pos h4]
          have hfin := tail_fin_sel_bound R4 hR4 (q i) j 300 76 (2151904 / 1000000) 15 (by decide)
            (by norm_num) (by norm_num) hR4_coef d300_bound.1 d300_bound.2 (by rw [hR4_4]; omega) hrank hq_pr.pos
          rw [show ((R4.card : ℝ) * ((76 : ℕ) : ℝ) ^ 2) = 4 * 5776 by rw [show (R4.card : ℝ) = 4 by exact_mod_cast hR4_4]; norm_num,
            show ((300 : ℕ) : ℝ) + 4 * 5776 = 23404 by norm_num] at hfin
          refine hfin.trans_eq ?_
          rw [show (15 : ℝ) * (2151904 / 1000000) * ((j : ℝ) - 23404) = (32278560 * ((j : ℝ) - 23404)) / 1000000 by ring,
            one_div_div]
        · rw [if_neg h4]
          by_cases h5 : j ≤ 10000000
          · rw [if_pos h5]
            have hlog : 10 * (71 / 100 : ℝ) ≤ Real.log ((10 ^ 7 : ℕ) : ℝ) := by
              rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
            have hjgt : (((Finset.Icc 1 (10 ^ 7)).filter (fun p => p.Prime ∧ p % 60 ∈ R4)).card : ℝ) < (j : ℝ) := by
              have : (1000001 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 1000001 ≤ j)
              linarith only [hpi7_lt, this]
            exact asymp_rank_inv_le_clean R4 (10 ^ 7) (71 / 100) (by norm_num) hlog
              pi60_4_le_10_pow_7 hjgt hrank (by omega) hq_pr.pos
          · rw [if_neg h5]
            by_cases h6 : j ≤ 1000000000
            · rw [if_pos h6]
              have hlog : 10 * (69 / 100 : ℝ) ≤ Real.log ((10 ^ 8 : ℕ) : ℝ) := by
                rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
              have hjgt : (((Finset.Icc 1 (10 ^ 8)).filter (fun p => p.Prime ∧ p % 60 ∈ R4)).card : ℝ) < (j : ℝ) := by
                have : (10000001 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 10000001 ≤ j)
                linarith only [hpi8_lt, this]
              exact asymp_rank_inv_le_clean R4 (10 ^ 8) (69 / 100) (by norm_num) hlog
                pi60_4_le_10_pow_8 hjgt hrank (by omega) hq_pr.pos
            · rw [if_neg h6]
              by_cases h7 : j ≤ 10000000000000
              · rw [if_pos h7]
                have hlog : 10 * (33 / 50 : ℝ) ≤ Real.log ((10 ^ 10 : ℕ) : ℝ) := by
                  rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
                have hjgt : (((Finset.Icc 1 (10 ^ 10)).filter (fun p => p.Prime ∧ p % 60 ∈ R4)).card : ℝ) < (j : ℝ) := by
                  have : (1000000001 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 1000000001 ≤ j)
                  linarith only [hpi10_lt, this]
                exact asymp_rank_inv_le_clean R4 (10 ^ 10) (33 / 50) (by norm_num) hlog
                  pi60_4_le_10_pow_10 hjgt hrank (by omega) hq_pr.pos
              · rw [if_neg h7]
                by_cases h8 : j ≤ 10000000000000000000
                · rw [if_pos h8]
                  have hlog : 10 * (63 / 100 : ℝ) ≤ Real.log ((10 ^ 14 : ℕ) : ℝ) := by
                    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
                  have hjgt : (((Finset.Icc 1 (10 ^ 14)).filter (fun p => p.Prime ∧ p % 60 ∈ R4)).card : ℝ) <
                      (j : ℝ) := by
                    have : (10000000000001 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 10000000000001 ≤ j)
                    linarith only [hpi14_lt, this]
                  exact asymp_rank_inv_le_clean R4 (10 ^ 14) (63 / 100) (by norm_num) hlog
                    pi60_4_le_10_pow_14 hjgt hrank (by omega) hq_pr.pos
                · rw [if_neg h8]
                  have hlog : 10 * (61 / 100 : ℝ) ≤ Real.log ((10 ^ 20 : ℕ) : ℝ) := by
                    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
                  have hjgt : (((Finset.Icc 1 (10 ^ 20)).filter (fun p => p.Prime ∧ p % 60 ∈ R4)).card : ℝ) <
                      (j : ℝ) := by
                    have : (10000000000000000001 : ℝ) ≤ (j : ℝ) := by
                      exact_mod_cast (by omega : 10000000000000000001 ≤ j)
                    linarith only [hpi20_lt, this]
                  exact asymp_rank_inv_le_clean R4 (10 ^ 20) (61 / 100) (by norm_num) hlog
                    pi60_4_le_10_pow_20 hjgt hrank (by omega) hq_pr.pos

private lemma tail_term_le_3 (P_gt : Finset ℕ) (hP_gt : ∀ p ∈ P_gt, p.Prime ∧ 10000 < p ∧
    p % 60 ∈ ({23, 47, 59} : Finset ℕ)) :
    let q : Fin P_gt.card ↪o ℕ := P_gt.orderEmbOfFin rfl
    ∀ i : Fin P_gt.card, (1 / ((q i : ℕ) : ℝ)) ≤
      (let j := 230 + (i : ℕ)
      if j ≤ 800 then (1 : ℝ) / 10000
      else if j ≤ 10000 then (1000000 : ℝ) / (30984440 * ((j : ℝ) - 221))
      else if j ≤ 100000 then (1000000 : ℝ) / (37093780 * ((j : ℝ) - 1975))
      else if j ≤ 1000000 then (1000000 : ℝ) / (43038080 * ((j : ℝ) - 17628))
      else if j ≤ 10000000 then (27 / 50 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
      else if j ≤ 1000000000 then (13 / 25 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
      else if j ≤ 10000000000000 then (49 / 100 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
      else if j ≤ 10000000000000000000 then (47 / 100 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
      else (23 / 50 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))) := by
  let R3 : Finset ℕ := {23, 47, 59}
  have hR3 : ∀ r ∈ R3, r < 60 := by decide
  have hR3_3 : R3.card = 3 := by decide
  have hR3_coef : (R3.card : ℝ) / 60 = 1 / 20 := by
    have : (R3.card : ℝ) = 3 := by exact_mod_cast hR3_3
    rw [this]; norm_num
  have hpi7_lt : (((Finset.Icc 1 (10 ^ 7)).filter (fun p => p.Prime ∧ p % 60 ∈ R3)).card : ℝ) < (1000001 : ℝ) := by
    have h1 := pi60_3_le_10_pow_7 (10 ^ 7) (le_refl _)
    have hlog : (161 / 10 : ℝ) ≤ Real.log ((10 ^ 7 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
    have h2 : (27 / 50 : ℝ) * ((10 ^ 7 : ℕ) : ℝ) / Real.log ((10 ^ 7 : ℕ) : ℝ) ≤
        (27 / 50 : ℝ) * ((10 ^ 7 : ℕ) : ℝ) / (161 / 10) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog
    have h3 : (27 / 50 : ℝ) * ((10 ^ 7 : ℕ) : ℝ) / (161 / 10) < 1000001 := by norm_num
    exact (h1.trans h2).trans_lt h3
  have hpi8_lt : (((Finset.Icc 1 (10 ^ 8)).filter (fun p => p.Prime ∧ p % 60 ∈ R3)).card : ℝ) < (10000001 : ℝ) := by
    have h1 := pi60_3_le_10_pow_8 (10 ^ 8) (le_refl _)
    have hlog : (92 / 5 : ℝ) ≤ Real.log ((10 ^ 8 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
    have h2 : (13 / 25 : ℝ) * ((10 ^ 8 : ℕ) : ℝ) / Real.log ((10 ^ 8 : ℕ) : ℝ) ≤
        (13 / 25 : ℝ) * ((10 ^ 8 : ℕ) : ℝ) / (92 / 5) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog
    have h3 : (13 / 25 : ℝ) * ((10 ^ 8 : ℕ) : ℝ) / (92 / 5) < 10000001 := by norm_num
    exact (h1.trans h2).trans_lt h3
  have hpi10_lt : (((Finset.Icc 1 (10 ^ 10)).filter (fun p => p.Prime ∧ p % 60 ∈ R3)).card : ℝ) < (1000000001 : ℝ) := by
    have h1 := pi60_3_le_10_pow_10 (10 ^ 10) (le_refl _)
    have hlog : (23 : ℝ) ≤ Real.log ((10 ^ 10 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
    have h2 : (49 / 100 : ℝ) * ((10 ^ 10 : ℕ) : ℝ) / Real.log ((10 ^ 10 : ℕ) : ℝ) ≤
        (49 / 100 : ℝ) * ((10 ^ 10 : ℕ) : ℝ) / 23 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog
    have h3 : (49 / 100 : ℝ) * ((10 ^ 10 : ℕ) : ℝ) / 23 < 1000000001 := by norm_num
    exact (h1.trans h2).trans_lt h3
  have hpi14_lt : (((Finset.Icc 1 (10 ^ 14)).filter (fun p => p.Prime ∧ p % 60 ∈ R3)).card : ℝ) <
      (10000000000001 : ℝ) := by
    have h1 := pi60_3_le_10_pow_14 (10 ^ 14) (le_refl _)
    have hlog : (161 / 5 : ℝ) ≤ Real.log ((10 ^ 14 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
    have h2 : (47 / 100 : ℝ) * ((10 ^ 14 : ℕ) : ℝ) / Real.log ((10 ^ 14 : ℕ) : ℝ) ≤
        (47 / 100 : ℝ) * ((10 ^ 14 : ℕ) : ℝ) / (161 / 5) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog
    have h3 : (47 / 100 : ℝ) * ((10 ^ 14 : ℕ) : ℝ) / (161 / 5) < 10000000000001 := by norm_num
    exact (h1.trans h2).trans_lt h3
  have hpi20_lt : (((Finset.Icc 1 (10 ^ 20)).filter (fun p => p.Prime ∧ p % 60 ∈ R3)).card : ℝ) <
      (10000000000000000001 : ℝ) := by
    have h1 := pi60_3_le_10_pow_20 (10 ^ 20) (le_refl _)
    have hlog : (46 : ℝ) ≤ Real.log ((10 ^ 20 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
    have h2 : (23 / 50 : ℝ) * ((10 ^ 20 : ℕ) : ℝ) / Real.log ((10 ^ 20 : ℕ) : ℝ) ≤
        (23 / 50 : ℝ) * ((10 ^ 20 : ℕ) : ℝ) / 46 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog
    have h3 : (23 / 50 : ℝ) * ((10 ^ 20 : ℕ) : ℝ) / 46 < 10000000000000000001 := by norm_num
    exact (h1.trans h2).trans_lt h3
  intro q i
  let j := 230 + (i : ℕ)
  have hrank : 230 + (i : ℕ) ≤ ((Finset.Icc 1 (q i)).filter (fun p => p.Prime ∧ p % 60 ∈ R3)).card := by
    have hq_mem : q i ∈ P_gt := Finset.orderEmbOfFin_mem P_gt rfl i
    obtain ⟨_, hq_gt, _⟩ := hP_gt (q i) hq_mem
    let T0 := (Finset.Icc 1 10000).filter (fun p => p.Prime ∧ p % 60 ∈ R3)
    let Qi : Finset ℕ := (Finset.range ((i : ℕ) + 1)).attach.image
      (fun k => q ⟨k.1, by have := Finset.mem_range.mp k.2; omega⟩)
    have hT0_sub : T0 ⊆ (Finset.Icc 1 (q i)).filter (fun p => p.Prime ∧ p % 60 ∈ R3) := fun p hp => by
      rw [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.trans hq_gt.le⟩, hp.2⟩
    have hQi_sub : Qi ⊆ (Finset.Icc 1 (q i)).filter (fun p => p.Prime ∧ p % 60 ∈ R3) := fun p hp => by
      rcases Finset.mem_image.mp hp with ⟨k, _, rfl⟩
      have hk_le : (⟨k.1, by have := Finset.mem_range.mp k.2; omega⟩ : Fin P_gt.card) ≤ i :=
        Fin.mk_le_mk.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp k.2))
      obtain ⟨hk_pr, _, hk_mod⟩ := hP_gt (q ⟨k.1, by have := Finset.mem_range.mp k.2; omega⟩)
        (Finset.orderEmbOfFin_mem P_gt rfl _)
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hk_pr.one_lt.le, q.monotone hk_le⟩, hk_pr, hk_mod⟩
    have hdisj : Disjoint T0 Qi := Finset.disjoint_left.mpr fun p h1 h2 => by
      rw [Finset.mem_filter, Finset.mem_Icc] at h1
      rcases Finset.mem_image.mp h2 with ⟨k, _, rfl⟩
      obtain ⟨_, hk_gt, _⟩ := hP_gt (q ⟨k.1, by have := Finset.mem_range.mp k.2; omega⟩)
        (Finset.orderEmbOfFin_mem P_gt rfl _)
      omega
    have hQi_card : Qi.card = (i : ℕ) + 1 := by
      have hinj : Function.Injective (fun k : {x // x ∈ Finset.range ((i : ℕ) + 1)} =>
          q ⟨k.1, by have := Finset.mem_range.mp k.2; omega⟩) := by
        intro k1 k2 heq
        have hfk := q.injective heq
        have hv : k1.1 = k2.1 := by simpa using congrArg Fin.val hfk
        exact Subtype.ext hv
      rw [Finset.card_image_of_injective _ hinj, Finset.card_attach, Finset.card_range]
    have hT0_card : 229 ≤ T0.card := p60_3_10000_data.1
    calc 230 + (i : ℕ) = 229 + ((i : ℕ) + 1) := by ring
      _ ≤ T0.card + Qi.card := by omega
      _ = (T0 ∪ Qi).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ _ := Finset.card_le_card (Finset.union_subset hT0_sub hQi_sub)
  obtain ⟨hq_pr, hq_gt, _⟩ := hP_gt (q i) (Finset.orderEmbOfFin_mem P_gt rfl i)
  change 1 / ((q i : ℕ) : ℝ) ≤ _
  by_cases h1 : j ≤ 800
  · rw [if_pos h1]
    have : (10000 : ℝ) ≤ ((q i : ℕ) : ℝ) := by exact_mod_cast hq_gt.le
    exact one_div_le_one_div_of_le (by norm_num) this
  · rw [if_neg h1]
    by_cases h2 : j ≤ 10000
    · rw [if_pos h2]
      have hfin := tail_fin_sel_bound R3 hR3 (q i) j 29 8 (1549222 / 1000000) 20 (by decide)
        (by norm_num) (by norm_num) hR3_coef d29_bound.1 d29_bound.2 (by rw [hR3_3]; omega) hrank hq_pr.pos
      rw [show ((R3.card : ℝ) * ((8 : ℕ) : ℝ) ^ 2) = 3 * 64 by rw [show (R3.card : ℝ) = 3 by exact_mod_cast hR3_3]; norm_num,
        show ((29 : ℕ) : ℝ) + 3 * 64 = 221 by norm_num] at hfin
      refine hfin.trans_eq ?_
      rw [show (20 : ℝ) * (1549222 / 1000000) * ((j : ℝ) - 221) = (30984440 * ((j : ℝ) - 221)) / 1000000 by ring,
        one_div_div]
    · rw [if_neg h2]
      by_cases h3 : j ≤ 100000
      · rw [if_pos h3]
        have hfin := tail_fin_sel_bound R3 hR3 (q i) j 100 25 (1854689 / 1000000) 20 (by decide)
          (by norm_num) (by norm_num) hR3_coef d100_bound.1 d100_bound.2 (by rw [hR3_3]; omega) hrank hq_pr.pos
        rw [show ((R3.card : ℝ) * ((25 : ℕ) : ℝ) ^ 2) = 3 * 625 by rw [show (R3.card : ℝ) = 3 by exact_mod_cast hR3_3]; norm_num,
          show ((100 : ℕ) : ℝ) + 3 * 625 = 1975 by norm_num] at hfin
        refine hfin.trans_eq ?_
        rw [show (20 : ℝ) * (1854689 / 1000000) * ((j : ℝ) - 1975) = (37093780 * ((j : ℝ) - 1975)) / 1000000 by ring,
          one_div_div]
      · rw [if_neg h3]
        by_cases h4 : j ≤ 1000000
        · rw [if_pos h4]
          have hfin := tail_fin_sel_bound R3 hR3 (q i) j 300 76 (2151904 / 1000000) 20 (by decide)
            (by norm_num) (by norm_num) hR3_coef d300_bound.1 d300_bound.2 (by rw [hR3_3]; omega) hrank hq_pr.pos
          rw [show ((R3.card : ℝ) * ((76 : ℕ) : ℝ) ^ 2) = 3 * 5776 by rw [show (R3.card : ℝ) = 3 by exact_mod_cast hR3_3]; norm_num,
            show ((300 : ℕ) : ℝ) + 3 * 5776 = 17628 by norm_num] at hfin
          refine hfin.trans_eq ?_
          rw [show (20 : ℝ) * (2151904 / 1000000) * ((j : ℝ) - 17628) = (43038080 * ((j : ℝ) - 17628)) / 1000000 by ring,
            one_div_div]
        · rw [if_neg h4]
          by_cases h5 : j ≤ 10000000
          · rw [if_pos h5]
            have hlog : 10 * (27 / 50 : ℝ) ≤ Real.log ((10 ^ 7 : ℕ) : ℝ) := by
              rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
            have hjgt : (((Finset.Icc 1 (10 ^ 7)).filter (fun p => p.Prime ∧ p % 60 ∈ R3)).card : ℝ) < (j : ℝ) := by
              have : (1000001 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 1000001 ≤ j)
              linarith only [hpi7_lt, this]
            exact asymp_rank_inv_le_clean R3 (10 ^ 7) (27 / 50) (by norm_num) hlog
              pi60_3_le_10_pow_7 hjgt hrank (by omega) hq_pr.pos
          · rw [if_neg h5]
            by_cases h6 : j ≤ 1000000000
            · rw [if_pos h6]
              have hlog : 10 * (13 / 25 : ℝ) ≤ Real.log ((10 ^ 8 : ℕ) : ℝ) := by
                rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
              have hjgt : (((Finset.Icc 1 (10 ^ 8)).filter (fun p => p.Prime ∧ p % 60 ∈ R3)).card : ℝ) < (j : ℝ) := by
                have : (10000001 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 10000001 ≤ j)
                linarith only [hpi8_lt, this]
              exact asymp_rank_inv_le_clean R3 (10 ^ 8) (13 / 25) (by norm_num) hlog
                pi60_3_le_10_pow_8 hjgt hrank (by omega) hq_pr.pos
            · rw [if_neg h6]
              by_cases h7 : j ≤ 10000000000000
              · rw [if_pos h7]
                have hlog : 10 * (49 / 100 : ℝ) ≤ Real.log ((10 ^ 10 : ℕ) : ℝ) := by
                  rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
                have hjgt : (((Finset.Icc 1 (10 ^ 10)).filter (fun p => p.Prime ∧ p % 60 ∈ R3)).card : ℝ) < (j : ℝ) := by
                  have : (1000000001 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 1000000001 ≤ j)
                  linarith only [hpi10_lt, this]
                exact asymp_rank_inv_le_clean R3 (10 ^ 10) (49 / 100) (by norm_num) hlog
                  pi60_3_le_10_pow_10 hjgt hrank (by omega) hq_pr.pos
              · rw [if_neg h7]
                by_cases h8 : j ≤ 10000000000000000000
                · rw [if_pos h8]
                  have hlog : 10 * (47 / 100 : ℝ) ≤ Real.log ((10 ^ 14 : ℕ) : ℝ) := by
                    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
                  have hjgt : (((Finset.Icc 1 (10 ^ 14)).filter (fun p => p.Prime ∧ p % 60 ∈ R3)).card : ℝ) <
                      (j : ℝ) := by
                    have : (10000000000001 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 10000000000001 ≤ j)
                    linarith only [hpi14_lt, this]
                  exact asymp_rank_inv_le_clean R3 (10 ^ 14) (47 / 100) (by norm_num) hlog
                    pi60_3_le_10_pow_14 hjgt hrank (by omega) hq_pr.pos
                · rw [if_neg h8]
                  have hlog : 10 * (23 / 50 : ℝ) ≤ Real.log ((10 ^ 20 : ℕ) : ℝ) := by
                    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
                  have hjgt : (((Finset.Icc 1 (10 ^ 20)).filter (fun p => p.Prime ∧ p % 60 ∈ R3)).card : ℝ) <
                      (j : ℝ) := by
                    have : (10000000000000000001 : ℝ) ≤ (j : ℝ) := by
                      exact_mod_cast (by omega : 10000000000000000001 ≤ j)
                    linarith only [hpi20_lt, this]
                  exact asymp_rank_inv_le_clean R3 (10 ^ 20) (23 / 50) (by norm_num) hlog
                    pi60_3_le_10_pow_20 hjgt hrank (by omega) hq_pr.pos

private lemma selberg_tail_sum_4_le (X_hi E : ℕ) (hE : 20 ≤ E)
    (hXhi_ge : 10 ^ 19 ≤ X_hi) (hXhi_le : X_hi ≤ 1001 * 10 ^ (E - 3))
    {P_gt : Finset ℕ} (hP_gt : ∀ p ∈ P_gt, p.Prime ∧ 10000 < p ∧
      p % 60 ∈ ({11, 23, 47, 59} : Finset ℕ))
    (hm : 307 + P_gt.card ≤ X_hi)
    {tail_log_hi : ℝ}
    (htail_log : Real.log (((E + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) - Real.log (20 * Real.log 10) ≤ tail_log_hi) :
    ∑ p ∈ P_gt, (1 / (p : ℝ)) ≤ (2681 : ℝ) / 2500 + (61 / 100 : ℝ) * tail_log_hi := by
  let m := P_gt.card
  let q : Fin m ↪o ℕ := P_gt.orderEmbOfFin rfl
  have hsum_eq : ∑ p ∈ P_gt, (1 / (p : ℝ)) = ∑ i : Fin m, (1 / ((q i : ℕ) : ℝ)) := by
    have himg_eq : Finset.univ.image q = P_gt := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
        exact Finset.orderEmbOfFin_mem P_gt rfl i
      · rw [Finset.card_image_of_injective _ q.injective, Finset.card_fin]
    rw [← himg_eq, Finset.sum_image (fun i1 _ i2 _ heq => q.injective heq)]
  let ub : ℕ → ℝ := fun j =>
    if j ≤ 800 then (1 : ℝ) / 10000
    else if j ≤ 10000 then (1000000 : ℝ) / (23238330 * ((j : ℝ) - 285))
    else if j ≤ 100000 then (1000000 : ℝ) / (27820335 * ((j : ℝ) - 2600))
    else if j ≤ 1000000 then (1000000 : ℝ) / (32278560 * ((j : ℝ) - 23404))
    else if j ≤ 10000000 then (71 / 100 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
    else if j ≤ 1000000000 then (69 / 100 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
    else if j ≤ 10000000000000 then (33 / 50 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
    else if j ≤ 10000000000000000000 then (63 / 100 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
    else (61 / 100 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
  have hub_nn : ∀ j : ℕ, 308 ≤ j → 0 ≤ ub j := fun j hj => by
    simp only [ub]
    split_ifs <;> try positivity
    · have : (285 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 285 < j)
      have : (0 : ℝ) < (j : ℝ) - 285 := by linarith only [this]
      positivity
    · have : (2600 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 2600 < j)
      have : (0 : ℝ) < (j : ℝ) - 2600 := by linarith only [this]
      positivity
    · have : (23404 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 23404 < j)
      have : (0 : ℝ) < (j : ℝ) - 23404 := by linarith only [this]
      positivity
    all_goals
      have hj10 : (2 : ℝ) ≤ 10 * (j : ℝ) := by exact_mod_cast (by omega : 2 ≤ 10 * j)
      have := (Real.log_pos (by norm_num)).trans_le (Real.log_le_log (by norm_num) hj10)
      positivity
  have hterm_le : ∀ i : Fin m, (1 / ((q i : ℕ) : ℝ)) ≤ ub (308 + (i : ℕ)) :=
    tail_term_le_4 P_gt hP_gt
  have hsum_ub : ∑ i : Fin m, ub (308 + (i : ℕ)) ≤ ∑ j ∈ Finset.Ioc 307 X_hi, ub j := by
    have hbij : ∑ i : Fin m, ub (308 + (i : ℕ)) = ∑ j ∈ Finset.Ioc 307 (307 + m), ub j := by
      refine Finset.sum_bij (fun i _ => 308 + (i : ℕ)) ?_ ?_ ?_ ?_
      · intro i _; rw [Finset.mem_Ioc]; omega
      · intro i1 _ i2 _ heq; ext; omega
      · intro j hj
        rw [Finset.mem_Ioc] at hj
        refine ⟨⟨j - 308, by omega⟩, Finset.mem_univ _, by simp; omega⟩
      · intro i _; rfl
    rw [hbij]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right hm) fun j hj _ => ?_
    rw [Finset.mem_Ioc] at hj
    exact hub_nn j (by omega)
  have hsub_307_800 : ∑ j ∈ Finset.Ioc 307 800, ub j = (493 : ℝ) / 10000 := by
    have hterm : ∀ j ∈ Finset.Ioc 307 800, ub j = (1 : ℝ) / 10000 := fun j hj => by
      rw [Finset.mem_Ioc] at hj; simp [ub, hj.2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ioc]
    norm_num
  have hsub_800_10k : ∑ j ∈ Finset.Ioc 800 10000, ub j ≤ (3000000 : ℝ) / 23238330 :=
    tail_Ioc_shift_bound ub 285 800 10000 3 1 (1000000 / 23238330) _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun j hj => by
        rw [Finset.mem_Ioc] at hj
        have h1 : ¬ j ≤ 800 := by omega
        dsimp only [ub]; rw [if_neg h1, if_pos hj.2, div_eq_mul_inv, mul_inv_rev]; ring) (by norm_num) (by norm_num)
  have hsub_10k_100k : ∑ j ∈ Finset.Ioc 10000 100000, ub j ≤ (13000000 : ℝ) / 139101675 :=
    tail_Ioc_shift_bound ub 2600 10000 100000 13 5 (1000000 / 27820335) _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun j hj => by
        rw [Finset.mem_Ioc] at hj
        have h1 : ¬ j ≤ 800 := by omega
        have h2 : ¬ j ≤ 10000 := by omega
        dsimp only [ub]; rw [if_neg h1, if_neg h2, if_pos hj.2, div_eq_mul_inv, mul_inv_rev]; ring) (by norm_num) (by norm_num)
  have hsub_100k_1M : ∑ j ∈ Finset.Ioc 100000 1000000, ub j ≤ (23000000 : ℝ) / 290507040 :=
    tail_Ioc_shift_bound ub 23404 100000 1000000 23 9 (1000000 / 32278560) _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun j hj => by
        rw [Finset.mem_Ioc] at hj
        have h1 : ¬ j ≤ 800 := by omega
        have h2 : ¬ j ≤ 10000 := by omega
        have h3 : ¬ j ≤ 100000 := by omega
        dsimp only [ub]; rw [if_neg h1, if_neg h2, if_neg h3, if_pos hj.2, div_eq_mul_inv, mul_inv_rev]; ring) (by norm_num) (by norm_num)
  have hsub_1M_10M : ∑ j ∈ Finset.Ioc 1000000 10000000, ub j ≤ (71 : ℝ) / 100 * (1 / 7) :=
    tail_Ioc_loglog_bound ub 1000000 10000000 7 8 (71 / 100) (1 / 7)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun j hj => by
        rw [Finset.mem_Ioc] at hj
        have h1 : ¬ j ≤ 800 := by omega
        have h2 : ¬ j ≤ 10000 := by omega
        have h3 : ¬ j ≤ 100000 := by omega
        have h4 : ¬ j ≤ 1000000 := by omega
        simp [ub, h1, h2, h3, h4, hj.2]; ring)
      (by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (8 : ℝ) / 7)])
  have hsub_10M_1G : ∑ j ∈ Finset.Ioc 10000000 1000000000, ub j ≤ (69 : ℝ) / 100 * (3 / 13) :=
    tail_Ioc_loglog_bound ub 10000000 1000000000 8 10 (69 / 100) (3 / 13)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun j hj => by
        rw [Finset.mem_Ioc] at hj
        have h1 : ¬ j ≤ 800 := by omega
        have h2 : ¬ j ≤ 10000 := by omega
        have h3 : ¬ j ≤ 100000 := by omega
        have h4 : ¬ j ≤ 1000000 := by omega
        have h5 : ¬ j ≤ 10000000 := by omega
        simp [ub, h1, h2, h3, h4, h5, hj.2]; ring)
      ((log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le)
  have hsub_1G_10T : ∑ j ∈ Finset.Ioc 1000000000 10000000000000, ub j ≤ (33 : ℝ) / 50 * (5 / 14) :=
    tail_Ioc_loglog_bound ub 1000000000 10000000000000 10 14 (33 / 50) (5 / 14)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun j hj => by
        rw [Finset.mem_Ioc] at hj
        have h1 : ¬ j ≤ 800 := by omega
        have h2 : ¬ j ≤ 10000 := by omega
        have h3 : ¬ j ≤ 100000 := by omega
        have h4 : ¬ j ≤ 1000000 := by omega
        have h5 : ¬ j ≤ 10000000 := by omega
        have h6 : ¬ j ≤ 1000000000 := by omega
        simp [ub, h1, h2, h3, h4, h5, h6, hj.2]; ring)
      ((log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le)
  have hsub_10T_10E : ∑ j ∈ Finset.Ioc 10000000000000 10000000000000000000, ub j ≤ (63 : ℝ) / 100 * (5 / 14) :=
    tail_Ioc_loglog_bound ub 10000000000000 10000000000000000000 14 20 (63 / 100) (5 / 14)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun j hj => by
        rw [Finset.mem_Ioc] at hj
        have h1 : ¬ j ≤ 800 := by omega
        have h2 : ¬ j ≤ 10000 := by omega
        have h3 : ¬ j ≤ 100000 := by omega
        have h4 : ¬ j ≤ 1000000 := by omega
        have h5 : ¬ j ≤ 10000000 := by omega
        have h6 : ¬ j ≤ 1000000000 := by omega
        have h7 : ¬ j ≤ 10000000000000 := by omega
        simp [ub, h1, h2, h3, h4, h5, h6, h7, hj.2]; ring)
      ((log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le)
  have hsub_10E_Xhi : ∑ j ∈ Finset.Ioc 10000000000000000000 X_hi, ub j ≤ (61 / 100 : ℝ) * tail_log_hi :=
    tail_Ioc_top_bound ub X_hi E (61 / 100) tail_log_hi hE hXhi_ge hXhi_le (by norm_num) (fun j hj => by
      rw [Finset.mem_Ioc] at hj
      have h1 : ¬ j ≤ 800 := by omega
      have h2 : ¬ j ≤ 10000 := by omega
      have h3 : ¬ j ≤ 100000 := by omega
      have h4 : ¬ j ≤ 1000000 := by omega
      have h5 : ¬ j ≤ 10000000 := by omega
      have h6 : ¬ j ≤ 1000000000 := by omega
      have h7 : ¬ j ≤ 10000000000000 := by omega
      have h8 : ¬ j ≤ 10000000000000000000 := by omega
      simp [ub, h1, h2, h3, h4, h5, h6, h7, h8]; ring) htail_log
  have hcomb : ∑ j ∈ Finset.Ioc 307 X_hi, ub j ≤ (2681 : ℝ) / 2500 + (61 / 100 : ℝ) * tail_log_hi := by
    rw [sum_Ioc_split (by norm_num : 307 ≤ 800) (by omega : 800 ≤ X_hi)]
    rw [sum_Ioc_split (by norm_num : 800 ≤ 10000) (by omega : 10000 ≤ X_hi)]
    rw [sum_Ioc_split (by norm_num : 10000 ≤ 100000) (by omega : 100000 ≤ X_hi)]
    rw [sum_Ioc_split (by norm_num : 100000 ≤ 1000000) (by omega : 1000000 ≤ X_hi)]
    rw [sum_Ioc_split (by norm_num : 1000000 ≤ 10000000) (by omega : 10000000 ≤ X_hi)]
    rw [sum_Ioc_split (by norm_num : 10000000 ≤ 1000000000) (by omega : 1000000000 ≤ X_hi)]
    rw [sum_Ioc_split (by norm_num : 1000000000 ≤ 10000000000000) (by omega : 10000000000000 ≤ X_hi)]
    rw [sum_Ioc_split (by norm_num : 10000000000000 ≤ 10000000000000000000) hXhi_ge]
    have hnum_sum : (493 : ℝ) / 10000 + 3000000 / 23238330 + 13000000 / 139101675 +
        23000000 / 290507040 + (71 / 100) * (1 / 7) + (69 / 100) * (3 / 13) +
        (33 / 50) * (5 / 14) + (63 / 100) * (5 / 14) ≤ 2681 / 2500 := by
      norm_num
    linarith only [hsub_307_800, hsub_800_10k, hsub_10k_100k, hsub_100k_1M, hsub_1M_10M,
      hsub_10M_1G, hsub_1G_10T, hsub_10T_10E, hsub_10E_Xhi, hnum_sum]
  calc ∑ p ∈ P_gt, (1 / (p : ℝ)) = ∑ i : Fin m, (1 / ((q i : ℕ) : ℝ)) := hsum_eq
    _ ≤ ∑ i : Fin m, ub (308 + (i : ℕ)) := Finset.sum_le_sum fun i _ => hterm_le i
    _ ≤ ∑ j ∈ Finset.Ioc 307 X_hi, ub j := hsum_ub
    _ ≤ (2681 : ℝ) / 2500 + (61 / 100 : ℝ) * tail_log_hi := hcomb

private lemma selberg_tail_sum_3_le (X_hi E : ℕ) (hE : 20 ≤ E)
    (hXhi_ge : 10 ^ 19 ≤ X_hi) (hXhi_le : X_hi ≤ 1001 * 10 ^ (E - 3))
    {P_gt : Finset ℕ} (hP_gt : ∀ p ∈ P_gt, p.Prime ∧ 10000 < p ∧
      p % 60 ∈ ({23, 47, 59} : Finset ℕ))
    (hm : 229 + P_gt.card ≤ X_hi)
    {tail_log_hi : ℝ}
    (htail_log : Real.log (((E + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) - Real.log (20 * Real.log 10) ≤ tail_log_hi) :
    ∑ p ∈ P_gt, (1 / (p : ℝ)) ≤ (815527 : ℝ) / 1000000 + (23 / 50 : ℝ) * tail_log_hi := by
  let m := P_gt.card
  let q : Fin m ↪o ℕ := P_gt.orderEmbOfFin rfl
  have hsum_eq : ∑ p ∈ P_gt, (1 / (p : ℝ)) = ∑ i : Fin m, (1 / ((q i : ℕ) : ℝ)) := by
    have himg_eq : Finset.univ.image q = P_gt := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
        exact Finset.orderEmbOfFin_mem P_gt rfl i
      · rw [Finset.card_image_of_injective _ q.injective, Finset.card_fin]
    rw [← himg_eq, Finset.sum_image (fun i1 _ i2 _ heq => q.injective heq)]
  let ub : ℕ → ℝ := fun j =>
    if j ≤ 800 then (1 : ℝ) / 10000
    else if j ≤ 10000 then (1000000 : ℝ) / (30984440 * ((j : ℝ) - 221))
    else if j ≤ 100000 then (1000000 : ℝ) / (37093780 * ((j : ℝ) - 1975))
    else if j ≤ 1000000 then (1000000 : ℝ) / (43038080 * ((j : ℝ) - 17628))
    else if j ≤ 10000000 then (27 / 50 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
    else if j ≤ 1000000000 then (13 / 25 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
    else if j ≤ 10000000000000 then (49 / 100 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
    else if j ≤ 10000000000000000000 then (47 / 100 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
    else (23 / 50 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
  have hub_nn : ∀ j : ℕ, 230 ≤ j → 0 ≤ ub j := fun j hj => by
    simp only [ub]
    split_ifs <;> try positivity
    · have : (221 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 221 < j)
      have : (0 : ℝ) < (j : ℝ) - 221 := by linarith only [this]
      positivity
    · have : (1975 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 1975 < j)
      have : (0 : ℝ) < (j : ℝ) - 1975 := by linarith only [this]
      positivity
    · have : (17628 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 17628 < j)
      have : (0 : ℝ) < (j : ℝ) - 17628 := by linarith only [this]
      positivity
    all_goals
      have hj10 : (2 : ℝ) ≤ 10 * (j : ℝ) := by exact_mod_cast (by omega : 2 ≤ 10 * j)
      have := (Real.log_pos (by norm_num)).trans_le (Real.log_le_log (by norm_num) hj10)
      positivity
  have hterm_le : ∀ i : Fin m, (1 / ((q i : ℕ) : ℝ)) ≤ ub (230 + (i : ℕ)) :=
    tail_term_le_3 P_gt hP_gt
  have hsum_ub : ∑ i : Fin m, ub (230 + (i : ℕ)) ≤ ∑ j ∈ Finset.Ioc 229 X_hi, ub j := by
    have hbij : ∑ i : Fin m, ub (230 + (i : ℕ)) = ∑ j ∈ Finset.Ioc 229 (229 + m), ub j := by
      refine Finset.sum_bij (fun i _ => 230 + (i : ℕ)) ?_ ?_ ?_ ?_
      · intro i _; rw [Finset.mem_Ioc]; omega
      · intro i1 _ i2 _ heq; ext; omega
      · intro j hj
        rw [Finset.mem_Ioc] at hj
        refine ⟨⟨j - 230, by omega⟩, Finset.mem_univ _, by simp; omega⟩
      · intro i _; rfl
    rw [hbij]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right hm) fun j hj _ => ?_
    rw [Finset.mem_Ioc] at hj
    exact hub_nn j (by omega)
  have hsub_229_800 : ∑ j ∈ Finset.Ioc 229 800, ub j = (571 : ℝ) / 10000 := by
    have hterm : ∀ j ∈ Finset.Ioc 229 800, ub j = (1 : ℝ) / 10000 := fun j hj => by
      rw [Finset.mem_Ioc] at hj; simp [ub, hj.2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ioc]
    norm_num
  have hsub_800_10k : ∑ j ∈ Finset.Ioc 800 10000, ub j ≤ (17000000 : ℝ) / 185906640 :=
    tail_Ioc_shift_bound ub 221 800 10000 17 6 (1000000 / 30984440) _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun j hj => by
        rw [Finset.mem_Ioc] at hj
        have h1 : ¬ j ≤ 800 := by omega
        dsimp only [ub]; rw [if_neg h1, if_pos hj.2, div_eq_mul_inv, mul_inv_rev]; ring) (by norm_num) (by norm_num)
  have hsub_10k_100k : ∑ j ∈ Finset.Ioc 10000 100000, ub j ≤ (23000000 : ℝ) / 333844020 :=
    tail_Ioc_shift_bound ub 1975 10000 100000 23 9 (1000000 / 37093780) _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun j hj => by
        rw [Finset.mem_Ioc] at hj
        have h1 : ¬ j ≤ 800 := by omega
        have h2 : ¬ j ≤ 10000 := by omega
        dsimp only [ub]; rw [if_neg h1, if_neg h2, if_pos hj.2, div_eq_mul_inv, mul_inv_rev]; ring) (by norm_num) (by norm_num)
  have hsub_100k_1M : ∑ j ∈ Finset.Ioc 100000 1000000, ub j ≤ (5000000 : ℝ) / 86076160 :=
    tail_Ioc_shift_bound ub 17628 100000 1000000 5 2 (1000000 / 43038080) _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun j hj => by
        rw [Finset.mem_Ioc] at hj
        have h1 : ¬ j ≤ 800 := by omega
        have h2 : ¬ j ≤ 10000 := by omega
        have h3 : ¬ j ≤ 100000 := by omega
        dsimp only [ub]; rw [if_neg h1, if_neg h2, if_neg h3, if_pos hj.2, div_eq_mul_inv, mul_inv_rev]; ring) (by norm_num) (by norm_num)
  have hsub_1M_10M : ∑ j ∈ Finset.Ioc 1000000 10000000, ub j ≤ (27 : ℝ) / 50 * (1 / 7) :=
    tail_Ioc_loglog_bound ub 1000000 10000000 7 8 (27 / 50) (1 / 7)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun j hj => by
        rw [Finset.mem_Ioc] at hj
        have h1 : ¬ j ≤ 800 := by omega
        have h2 : ¬ j ≤ 10000 := by omega
        have h3 : ¬ j ≤ 100000 := by omega
        have h4 : ¬ j ≤ 1000000 := by omega
        simp [ub, h1, h2, h3, h4, hj.2]; ring)
      (by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (8 : ℝ) / 7)])
  have hsub_10M_1G : ∑ j ∈ Finset.Ioc 10000000 1000000000, ub j ≤ (13 : ℝ) / 25 * (3 / 13) :=
    tail_Ioc_loglog_bound ub 10000000 1000000000 8 10 (13 / 25) (3 / 13)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun j hj => by
        rw [Finset.mem_Ioc] at hj
        have h1 : ¬ j ≤ 800 := by omega
        have h2 : ¬ j ≤ 10000 := by omega
        have h3 : ¬ j ≤ 100000 := by omega
        have h4 : ¬ j ≤ 1000000 := by omega
        have h5 : ¬ j ≤ 10000000 := by omega
        simp [ub, h1, h2, h3, h4, h5, hj.2]; ring)
      ((log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le)
  have hsub_1G_10T : ∑ j ∈ Finset.Ioc 1000000000 10000000000000, ub j ≤ (49 : ℝ) / 100 * (5 / 14) :=
    tail_Ioc_loglog_bound ub 1000000000 10000000000000 10 14 (49 / 100) (5 / 14)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun j hj => by
        rw [Finset.mem_Ioc] at hj
        have h1 : ¬ j ≤ 800 := by omega
        have h2 : ¬ j ≤ 10000 := by omega
        have h3 : ¬ j ≤ 100000 := by omega
        have h4 : ¬ j ≤ 1000000 := by omega
        have h5 : ¬ j ≤ 10000000 := by omega
        have h6 : ¬ j ≤ 1000000000 := by omega
        simp [ub, h1, h2, h3, h4, h5, h6, hj.2]; ring)
      ((log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le)
  have hsub_10T_10E : ∑ j ∈ Finset.Ioc 10000000000000 10000000000000000000, ub j ≤ (47 : ℝ) / 100 * (5 / 14) :=
    tail_Ioc_loglog_bound ub 10000000000000 10000000000000000000 14 20 (47 / 100) (5 / 14)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun j hj => by
        rw [Finset.mem_Ioc] at hj
        have h1 : ¬ j ≤ 800 := by omega
        have h2 : ¬ j ≤ 10000 := by omega
        have h3 : ¬ j ≤ 100000 := by omega
        have h4 : ¬ j ≤ 1000000 := by omega
        have h5 : ¬ j ≤ 10000000 := by omega
        have h6 : ¬ j ≤ 1000000000 := by omega
        have h7 : ¬ j ≤ 10000000000000 := by omega
        simp [ub, h1, h2, h3, h4, h5, h6, h7, hj.2]; ring)
      ((log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le)
  have hsub_10E_Xhi : ∑ j ∈ Finset.Ioc 10000000000000000000 X_hi, ub j ≤ (23 / 50 : ℝ) * tail_log_hi :=
    tail_Ioc_top_bound ub X_hi E (23 / 50) tail_log_hi hE hXhi_ge hXhi_le (by norm_num) (fun j hj => by
      rw [Finset.mem_Ioc] at hj
      have h1 : ¬ j ≤ 800 := by omega
      have h2 : ¬ j ≤ 10000 := by omega
      have h3 : ¬ j ≤ 100000 := by omega
      have h4 : ¬ j ≤ 1000000 := by omega
      have h5 : ¬ j ≤ 10000000 := by omega
      have h6 : ¬ j ≤ 1000000000 := by omega
      have h7 : ¬ j ≤ 10000000000000 := by omega
      have h8 : ¬ j ≤ 10000000000000000000 := by omega
      simp [ub, h1, h2, h3, h4, h5, h6, h7, h8]; ring) htail_log
  have hcomb : ∑ j ∈ Finset.Ioc 229 X_hi, ub j ≤ (815527 : ℝ) / 1000000 + (23 / 50 : ℝ) * tail_log_hi := by
    rw [sum_Ioc_split (by norm_num : 229 ≤ 800) (by omega : 800 ≤ X_hi)]
    rw [sum_Ioc_split (by norm_num : 800 ≤ 10000) (by omega : 10000 ≤ X_hi)]
    rw [sum_Ioc_split (by norm_num : 10000 ≤ 100000) (by omega : 100000 ≤ X_hi)]
    rw [sum_Ioc_split (by norm_num : 100000 ≤ 1000000) (by omega : 1000000 ≤ X_hi)]
    rw [sum_Ioc_split (by norm_num : 1000000 ≤ 10000000) (by omega : 10000000 ≤ X_hi)]
    rw [sum_Ioc_split (by norm_num : 10000000 ≤ 1000000000) (by omega : 1000000000 ≤ X_hi)]
    rw [sum_Ioc_split (by norm_num : 1000000000 ≤ 10000000000000) (by omega : 10000000000000 ≤ X_hi)]
    rw [sum_Ioc_split (by norm_num : 10000000000000 ≤ 10000000000000000000) hXhi_ge]
    have hnum_sum : (571 : ℝ) / 10000 + 17000000 / 185906640 + 23000000 / 333844020 +
        5000000 / 86076160 + (27 / 50) * (1 / 7) + (13 / 25) * (3 / 13) +
        (49 / 100) * (5 / 14) + (47 / 100) * (5 / 14) ≤ 815527 / 1000000 := by
      norm_num
    linarith only [hsub_229_800, hsub_800_10k, hsub_10k_100k, hsub_100k_1M, hsub_1M_10M,
      hsub_10M_1G, hsub_1G_10T, hsub_10T_10E, hsub_10E_Xhi, hnum_sum]
  calc ∑ p ∈ P_gt, (1 / (p : ℝ)) = ∑ i : Fin m, (1 / ((q i : ℕ) : ℝ)) := hsum_eq
    _ ≤ ∑ i : Fin m, ub (230 + (i : ℕ)) := Finset.sum_le_sum fun i _ => hterm_le i
    _ ≤ ∑ j ∈ Finset.Ioc 229 X_hi, ub j := hsum_ub
    _ ≤ (815527 : ℝ) / 1000000 + (23 / 50 : ℝ) * tail_log_hi := hcomb
private lemma card_ge_4_of_sum_gt {n k E : ℕ} (hn0 : n ≠ 0) (h3 : 3 ∣ n)
    (hprimes : ∀ p ∈ n.primeFactors, p = 3 ∨ p % 60 = 11 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59)
    (hsum : (k : ℝ) < ∑ p ∈ n.primeFactors, (1 / (p : ℝ)))
    (hE : 20 ≤ E) {tail_log_hi : ℝ}
    (htail_log : Real.log (((E + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) - Real.log (20 * Real.log 10) ≤ tail_log_hi)
    (hcontra : (1 / 3 : ℝ) + (368796 : ℝ) / 1000000 + (2681 : ℝ) / 2500 + (61 / 100 : ℝ) * tail_log_hi ≤ (k : ℝ)) :
    10 ^ E ≤ n.primeFactors.card := by
  by_contra hlt
  have hcard_lt : n.primeFactors.card < 10 ^ E := by omega
  let R4 : Finset ℕ := {11, 23, 47, 59}
  let P := n.primeFactors.filter (fun p => p % 60 ∈ R4)
  have hpart : n.primeFactors = insert 3 P := by
    ext p
    simp only [P, R4, Finset.mem_insert, Finset.mem_filter]
    constructor
    · intro hp
      rcases hprimes p hp with rfl | h11 | h23 | h47 | h59
      · left; rfl
      · right; exact ⟨hp, by simp [h11]⟩
      · right; exact ⟨hp, by simp [h23]⟩
      · right; exact ⟨hp, by simp [h47]⟩
      · right; exact ⟨hp, by simp [h59]⟩
    · rintro (rfl | ⟨hp, _⟩)
      · exact Nat.mem_primeFactors.mpr ⟨by decide, h3, hn0⟩
      · exact hp
  have hnot3 : 3 ∉ P := by simp [P, R4]
  have hsum_split : ∑ p ∈ n.primeFactors, (1 / (p : ℝ)) =
      (1 / 3 : ℝ) + ∑ p ∈ P, (1 / (p : ℝ)) := by
    rw [hpart, Finset.sum_insert hnot3]
    norm_num
  have hcard_split : n.primeFactors.card = 1 + P.card := by
    rw [hpart, Finset.card_insert_of_notMem hnot3]
    ring
  let P_le := P.filter (fun p => p ≤ 10000)
  let P_gt := P.filter (fun p => 10000 < p)
  have hP_split : P = P_le ∪ P_gt := by
    ext p
    simp only [P_le, P_gt, Finset.mem_union, Finset.mem_filter]
    by_cases hp : p ≤ 10000
    · simp [hp, show ¬ 10000 < p by omega]
    · simp [hp, show 10000 < p by omega]
  have hP_disj : Disjoint P_le P_gt := Finset.disjoint_left.mpr fun p h1 h2 => by
    simp [P_le, P_gt] at h1 h2; omega
  have hsum_P : ∑ p ∈ P, (1 / (p : ℝ)) =
      (∑ p ∈ P_le, (1 / (p : ℝ))) + ∑ p ∈ P_gt, (1 / (p : ℝ)) := by
    rw [hP_split, Finset.sum_union hP_disj]
  have hPle_sum : ∑ p ∈ P_le, (1 / (p : ℝ)) ≤ (368796 : ℝ) / 1000000 :=
    p60_4_10000_data.2 P_le fun p hp => by
      rw [Finset.mem_filter, Finset.mem_filter] at hp
      exact ⟨Nat.prime_of_mem_primeFactors hp.1.1, hp.2, hp.1.2⟩
  let X_hi := 1001 * 10 ^ (E - 3)
  have hXhi_ge : 10 ^ 19 ≤ X_hi := by
    have hpow : 10 ^ 17 ≤ 10 ^ (E - 3) := Nat.pow_le_pow_right (by decide) (by omega)
    calc 10 ^ 19 = 100 * 10 ^ 17 := by norm_num
      _ ≤ 1001 * 10 ^ 17 := by omega
      _ ≤ 1001 * 10 ^ (E - 3) := Nat.mul_le_mul_left 1001 hpow
  have hm_le : 307 + P_gt.card ≤ X_hi := by
    have hPgt_le : P_gt.card ≤ P.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hpow17 : 10 ^ 17 ≤ 10 ^ (E - 3) := Nat.pow_le_pow_right (by decide) (by omega)
    have h307 : 307 ≤ 10 ^ (E - 3) := by omega
    have hE_eq : 10 ^ E = 1000 * 10 ^ (E - 3) := by
      rw [show 1000 = 10 ^ 3 by decide, ← pow_add, show 3 + (E - 3) = E by omega]
    calc 307 + P_gt.card ≤ 10 ^ (E - 3) + 10 ^ E := by omega
      _ = 1001 * 10 ^ (E - 3) := by rw [hE_eq]; ring
  have hPgt_sum := selberg_tail_sum_4_le X_hi E hE hXhi_ge (le_refl _) (fun p hp => by
    rw [Finset.mem_filter, Finset.mem_filter] at hp
    exact ⟨Nat.prime_of_mem_primeFactors hp.1.1, hp.2, hp.1.2⟩) hm_le htail_log
  linarith [hsum, hsum_split, hsum_P, hPle_sum, hPgt_sum, hcontra]

private lemma card_ge_3_of_sum_gt {n k E : ℕ} (hn0 : n ≠ 0) (h3 : 3 ∣ n)
    (hprimes : ∀ p ∈ n.primeFactors, p = 3 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59)
    (hsum : (k : ℝ) < ∑ p ∈ n.primeFactors, (1 / (p : ℝ)))
    (hE : 20 ≤ E) {tail_log_hi : ℝ}
    (htail_log : Real.log (((E + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) - Real.log (20 * Real.log 10) ≤ tail_log_hi)
    (hcontra : (1 / 3 : ℝ) + (218945 : ℝ) / 1000000 + (815527 : ℝ) / 1000000 + (23 / 50 : ℝ) * tail_log_hi ≤ (k : ℝ)) :
    10 ^ E ≤ n.primeFactors.card := by
  by_contra hlt
  have hcard_lt : n.primeFactors.card < 10 ^ E := by omega
  let R3 : Finset ℕ := {23, 47, 59}
  let P := n.primeFactors.filter (fun p => p % 60 ∈ R3)
  have hpart : n.primeFactors = insert 3 P := by
    ext p
    simp only [P, R3, Finset.mem_insert, Finset.mem_filter]
    constructor
    · intro hp
      rcases hprimes p hp with rfl | h23 | h47 | h59
      · left; rfl
      · right; exact ⟨hp, by simp [h23]⟩
      · right; exact ⟨hp, by simp [h47]⟩
      · right; exact ⟨hp, by simp [h59]⟩
    · rintro (rfl | ⟨hp, _⟩)
      · exact Nat.mem_primeFactors.mpr ⟨by decide, h3, hn0⟩
      · exact hp
  have hnot3 : 3 ∉ P := by simp [P, R3]
  have hsum_split : ∑ p ∈ n.primeFactors, (1 / (p : ℝ)) =
      (1 / 3 : ℝ) + ∑ p ∈ P, (1 / (p : ℝ)) := by
    rw [hpart, Finset.sum_insert hnot3]
    norm_num
  have hcard_split : n.primeFactors.card = 1 + P.card := by
    rw [hpart, Finset.card_insert_of_notMem hnot3]
    ring
  let P_le := P.filter (fun p => p ≤ 10000)
  let P_gt := P.filter (fun p => 10000 < p)
  have hP_split : P = P_le ∪ P_gt := by
    ext p
    simp only [P_le, P_gt, Finset.mem_union, Finset.mem_filter]
    by_cases hp : p ≤ 10000
    · simp [hp, show ¬ 10000 < p by omega]
    · simp [hp, show 10000 < p by omega]
  have hP_disj : Disjoint P_le P_gt := Finset.disjoint_left.mpr fun p h1 h2 => by
    simp [P_le, P_gt] at h1 h2; omega
  have hsum_P : ∑ p ∈ P, (1 / (p : ℝ)) =
      (∑ p ∈ P_le, (1 / (p : ℝ))) + ∑ p ∈ P_gt, (1 / (p : ℝ)) := by
    rw [hP_split, Finset.sum_union hP_disj]
  have hPle_sum : ∑ p ∈ P_le, (1 / (p : ℝ)) ≤ (218945 : ℝ) / 1000000 :=
    p60_3_10000_data.2 P_le fun p hp => by
      rw [Finset.mem_filter, Finset.mem_filter] at hp
      exact ⟨Nat.prime_of_mem_primeFactors hp.1.1, hp.2, hp.1.2⟩
  let X_hi := 1001 * 10 ^ (E - 3)
  have hXhi_ge : 10 ^ 19 ≤ X_hi := by
    have hpow : 10 ^ 17 ≤ 10 ^ (E - 3) := Nat.pow_le_pow_right (by decide) (by omega)
    calc 10 ^ 19 = 100 * 10 ^ 17 := by norm_num
      _ ≤ 1001 * 10 ^ 17 := by omega
      _ ≤ 1001 * 10 ^ (E - 3) := Nat.mul_le_mul_left 1001 hpow
  have hm_le : 229 + P_gt.card ≤ X_hi := by
    have hPgt_le : P_gt.card ≤ P.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hpow17 : 10 ^ 17 ≤ 10 ^ (E - 3) := Nat.pow_le_pow_right (by decide) (by omega)
    have h229 : 229 ≤ 10 ^ (E - 3) := by omega
    have hE_eq : 10 ^ E = 1000 * 10 ^ (E - 3) := by
      rw [show 1000 = 10 ^ 3 by decide, ← pow_add, show 3 + (E - 3) = E by omega]
    calc 229 + P_gt.card ≤ 10 ^ (E - 3) + 10 ^ E := by omega
      _ = 1001 * 10 ^ (E - 3) := by rw [hE_eq]; ring
  have hPgt_sum := selberg_tail_sum_3_le X_hi E hE hXhi_ge (le_refl _) (fun p hp => by
    rw [Finset.mem_filter, Finset.mem_filter] at hp
    exact ⟨Nat.prime_of_mem_primeFactors hp.1.1, hp.2, hp.1.2⟩) hm_le htail_log
  linarith [hsum, hsum_split, hsum_P, hPle_sum, hPgt_sum, hcontra]

private lemma tail_log_bound_of_pow (E p q : ℕ) (hq : 0 < q)
    (hpow : (((E + 1 : ℕ) * 2300 + 1 : ℕ) : ℝ) ^ q / ((46000 : ℝ) ^ q) < (2.718 : ℝ) ^ p) :
    Real.log (((E + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) - Real.log (20 * Real.log 10) ≤ (p : ℝ) / (q : ℝ) := by
  have hlp : (23 / 10 : ℝ) < Real.log 10 := log_ten_gt
  have hnum_pos : 0 < (20 : ℝ) * Real.log 10 := by linarith
  rw [← Real.log_div (by positivity) hnum_pos.ne']
  have heq : (((E + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) / (20 * Real.log 10) =
      ((E + 1 : ℕ) : ℝ) / 20 + (1 / 1000) / (20 * Real.log 10) := by
    field_simp [hnum_pos.ne']
  have hdiv : (1 / 1000 : ℝ) / (20 * Real.log 10) < (1 / 1000) / (20 * (23 / 10)) :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) (by linarith)
  have hratio : (((E + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) / (20 * Real.log 10) <
      (((E + 1 : ℕ) * 2300 + 1 : ℕ) : ℝ) / 46000 := by
    push_cast at heq ⊢
    linarith only [heq, hdiv]
  have hlog1 := Real.log_lt_log (div_pos (by positivity) hnum_pos) hratio
  have ha_pos : (0 : ℝ) < (((E + 1 : ℕ) * 2300 + 1 : ℕ) : ℝ) / 46000 := by positivity
  have hpow' : ((((E + 1 : ℕ) * 2300 + 1 : ℕ) : ℝ) / 46000) ^ q < (2.718 : ℝ) ^ p := by
    rw [div_pow]; exact hpow
  have hlog2 := log_lt_of_pow_lt ha_pos hq hpow'
  linarith

private lemma card_ge_k4_R4 {n : ℕ} (hn0 : n ≠ 0) (h3 : 3 ∣ n)
    (hprimes : ∀ p ∈ n.primeFactors, p = 3 ∨ p % 60 = 11 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 4) :
    10 ^ 700 ≤ n.primeFactors.card := by
  have hreal := sum_real_gt_k_loc hn0 hsum
  have hlog : Real.log (((700 + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) - Real.log (20 * Real.log 10) ≤
      (25 : ℝ) / 7 := by
    exact_mod_cast tail_log_bound_of_pow 700 25 7 (by decide) (by norm_num)
  exact card_ge_4_of_sum_gt hn0 h3 hprimes (by push_cast at hreal ⊢; exact hreal)
    (by decide) hlog (by norm_num)

private lemma card_ge_k4_R3 {n : ℕ} (hn0 : n ≠ 0) (h3 : 3 ∣ n)
    (hprimes : ∀ p ∈ n.primeFactors, p = 3 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 4) :
    10 ^ 5500 ≤ n.primeFactors.card := by
  have hreal := sum_real_gt_k_loc hn0 hsum
  have hlog : Real.log (((5500 + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) - Real.log (20 * Real.log 10) ≤
      (45 : ℝ) / 8 := by
    exact_mod_cast tail_log_bound_of_pow 5500 45 8 (by decide) (by norm_num)
  exact card_ge_3_of_sum_gt hn0 h3 hprimes (by push_cast at hreal ⊢; exact hreal)
    (by decide) hlog (by norm_num)

private lemma card_ge_k8_R4 {n : ℕ} (hn0 : n ≠ 0) (h3 : 3 ∣ n)
    (hprimes : ∀ p ∈ n.primeFactors, p = 3 ∨ p % 60 = 11 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 8) :
    10 ^ 500000 ≤ n.primeFactors.card := by
  have hreal := sum_real_gt_k_loc hn0 hsum
  have hlog : Real.log (((500000 + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) - Real.log (20 * Real.log 10) ≤
      (71 : ℝ) / 7 := by
    exact_mod_cast tail_log_bound_of_pow 500000 71 7 (by decide) (by norm_num)
  exact card_ge_4_of_sum_gt hn0 h3 hprimes (by push_cast at hreal ⊢; exact hreal)
    (by decide) hlog (by norm_num)

private lemma card_ge_k12_R4 {n k : ℕ} (hn0 : n ≠ 0) (h3 : 3 ∣ n)
    (hprimes : ∀ p ∈ n.primeFactors, p = 3 ∨ p % 60 = 11 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59)
    (hk12 : 12 ≤ k)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    10 ^ 350000000 ≤ n.primeFactors.card := by
  have hreal := sum_real_gt_k_loc hn0 hsum
  have hk_real : (12 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk12
  have hreal12 : (12 : ℝ) < ∑ p ∈ n.primeFactors, (1 / (p : ℝ)) := lt_of_le_of_lt hk_real hreal
  have hlog : Real.log (((350000000 + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) - Real.log (20 * Real.log 10) ≤
      (167 : ℝ) / 10 := by
    exact_mod_cast tail_log_bound_of_pow 350000000 167 10 (by decide) (by norm_num)
  exact card_ge_4_of_sum_gt hn0 h3 hprimes hreal12 (by decide) hlog (by norm_num)

/- ## Section 5: Reduction hypotheses and main theorem -/

def H1 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → 3 ∣ n → ¬ (5 ∣ n) →
    n % 180 = 111 →
    n.primeFactors.card % 8 = 5 →
    10 ^ 700 ≤ n.primeFactors.card →
    (∃ p ∈ n.primeFactors, p % 60 = 11) →
    (∀ p ∈ n.primeFactors, p = 3 ∨ p % 60 = 11 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    n % 27 = (9 * (n.primeFactors.card + 3) + 3) % 27 →
    ((n.primeFactors.filter (fun p => p % 60 = 11)).card +
      2 * (n.primeFactors.filter (fun p => p % 60 = 23)).card +
      3 * (n.primeFactors.filter (fun p => p % 60 = 47)).card +
      4 * (n.primeFactors.filter (fun p => p % 60 = 59)).card + 1) % 5 = 4 →
    ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 4 →
    (∃ p q : ℕ, p ∈ n.primeFactors ∧ q ∈ n.primeFactors ∧ p < q ∧
      (∀ r ∈ n.primeFactors, r ≤ q) ∧ (∀ r ∈ n.primeFactors.erase q, r ≤ p) ∧
      let m := n / (p * q)
      let D := ∑ r ∈ m.primeFactors, m / r
      let A := m - D % m
      let L := m.primeFactors.lcm (fun r => (r - 1) / 2)
      A * (p * q) + 1 = m * (p + q) ∧ A % 24 = 17 ∧
      p < A ^ 2 ∧ m < A ^ 3 ∧ 16 * q < m ∧ n < A ^ 8 ∧ 10 ^ (n.primeFactors.card - 1) < n ∧
      2 * L ∣ n - 1 ∧ ¬ (3 ∣ L) ∧ (5497 : ℚ) / 375 < ∑ d ∈ L.divisors, (1 / (d : ℚ)) ∧
      ((L : ℤ) ∣ (((m : ℤ) ^ 2 * ((q : ℤ) - p)) ^ 2 - (((A : ℤ) + m) ^ 2 - 4 * (m : ℤ) ^ 3))) ∧
      30 * A * ((q - p) / 2) ^ 2 < m ^ 2) →
    False

def H2 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → 3 ∣ n → ¬ (5 ∣ n) →
    n % 36 = 3 →
    n.primeFactors.card % 8 = 5 →
    10 ^ 5500 ≤ n.primeFactors.card →
    (∀ p ∈ n.primeFactors, p = 3 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    n % 27 = (9 * (n.primeFactors.card + 3) + 3) % 27 →
    ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 4 →
    (∃ p q : ℕ, p ∈ n.primeFactors ∧ q ∈ n.primeFactors ∧ p < q ∧
      (∀ r ∈ n.primeFactors, r ≤ q) ∧ (∀ r ∈ n.primeFactors.erase q, r ≤ p) ∧
      let m := n / (p * q)
      let D := ∑ r ∈ m.primeFactors, m / r
      let A := m - D % m
      let L := m.primeFactors.lcm (fun r => (r - 1) / 2)
      A * (p * q) + 1 = m * (p + q) ∧ A % 24 = 17 ∧
      p < A ^ 2 ∧ m < A ^ 3 ∧ 16 * q < m ∧ n < A ^ 8 ∧ 10 ^ (n.primeFactors.card - 1) < n ∧
      2 * L ∣ n - 1 ∧ ¬ (3 ∣ L) ∧ ¬ (5 ∣ L) ∧ (5497 : ℚ) / 375 < ∑ d ∈ L.divisors, (1 / (d : ℚ)) ∧
      ((L : ℤ) ∣ (((m : ℤ) ^ 2 * ((q : ℤ) - p)) ^ 2 - (((A : ℤ) + m) ^ 2 - 4 * (m : ℤ) ^ 3))) ∧
      30 * A * ((q - p) / 2) ^ 2 < m ^ 2) →
    False

def H3 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → 3 ∣ n → ¬ (5 ∣ n) →
    n % 36 = 3 →
    n.primeFactors.card % 8 = 1 →
    10 ^ 500000 ≤ n.primeFactors.card →
    ((∃ p ∈ n.primeFactors, p % 60 = 11) → n % 180 = 111) →
    (∀ p ∈ n.primeFactors, p = 3 ∨ p % 60 = 11 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    n % 27 = (9 * (n.primeFactors.card + 7) + 3) % 27 →
    ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 8 →
    (∃ p q : ℕ, p ∈ n.primeFactors ∧ q ∈ n.primeFactors ∧ p < q ∧
      (∀ r ∈ n.primeFactors, r ≤ q) ∧ (∀ r ∈ n.primeFactors.erase q, r ≤ p) ∧
      let m := n / (p * q)
      let D := ∑ r ∈ m.primeFactors, m / r
      let A := m - D % m
      let L := m.primeFactors.lcm (fun r => (r - 1) / 2)
      A * (p * q) + 1 = m * (p + q) ∧ A % 24 = 17 ∧
      p < A ^ 2 ∧ m < A ^ 3 ∧ 16 * q < m ∧ n < A ^ 8 ∧ 10 ^ (n.primeFactors.card - 1) < n ∧
      2 * L ∣ n - 1 ∧ ¬ (3 ∣ L) ∧ ((∀ r ∈ n.primeFactors, r % 60 ≠ 11) → ¬ (5 ∣ L)) ∧
      (5497 : ℚ) / 375 < ∑ d ∈ L.divisors, (1 / (d : ℚ)) ∧
      ((L : ℤ) ∣ (((m : ℤ) ^ 2 * ((q : ℤ) - p)) ^ 2 - (((A : ℤ) + m) ^ 2 - 4 * (m : ℤ) ^ 3))) ∧
      30 * A * ((q - p) / 2) ^ 2 < m ^ 2) →
    False

def H4 : Prop :=
  ∀ n k : ℕ, n.Composite → Squarefree n → Odd n → 3 ∣ n → ¬ (5 ∣ n) →
    n % 36 = 3 →
    12 ≤ k → 4 ∣ k →
    n.primeFactors.card % 8 = (k + 1) % 8 →
    10 ^ 350000000 ≤ n.primeFactors.card →
    ((∃ p ∈ n.primeFactors, p % 60 = 11) → n % 180 = 111) →
    (∀ p ∈ n.primeFactors, p = 3 ∨ p % 60 = 11 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    n % 27 = (9 * (k + n.primeFactors.card - 1) + 3) % 27 →
    ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ) →
    (∃ p q : ℕ, p ∈ n.primeFactors ∧ q ∈ n.primeFactors ∧ p < q ∧
      (∀ r ∈ n.primeFactors, r ≤ q) ∧ (∀ r ∈ n.primeFactors.erase q, r ≤ p) ∧
      let m := n / (p * q)
      let D := ∑ r ∈ m.primeFactors, m / r
      let A := m - D % m
      let L := m.primeFactors.lcm (fun r => (r - 1) / 2)
      A * (p * q) + 1 = m * (p + q) ∧ A % 24 = 17 ∧
      p < A ^ 2 ∧ m < A ^ 3 ∧ 16 * q < m ∧ n < A ^ 8 ∧ 10 ^ (n.primeFactors.card - 1) < n ∧
      2 * L ∣ n - 1 ∧ ¬ (3 ∣ L) ∧ ((∀ r ∈ n.primeFactors, r % 60 ≠ 11) → ¬ (5 ∣ L)) ∧
      (5497 : ℚ) / 375 < ∑ d ∈ L.divisors, (1 / (d : ℚ)) ∧
      ((L : ℤ) ∣ (((m : ℤ) ^ 2 * ((q : ℤ) - p)) ^ 2 - (((A : ℤ) + m) ^ 2 - 4 * (m : ℤ) ^ 3))) ∧
      30 * A * ((q - p) / 2) ^ 2 < m ^ 2) →
    False

theorem main : H1 → H2 → H3 → H4 → OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H1_R1.H3 := by
  intro hH1 hH2 hH3 hH4 n hcomp hsqf hodd h3 h5 hn36 _ hcard22 hprimes hdvd hno_dvd hkex
  rcases hkex with ⟨k, hk4, hk4dvd, hcard8, hn27, hsum⟩
  have hn0 : n ≠ 0 := hsqf.ne_zero
  have h180_imp : (∃ p ∈ n.primeFactors, p % 60 = 11) → n % 180 = 111 := by
    rintro ⟨p, hp, hp11⟩
    exact (mod_180_of_p60_eq_11 hn0 hn36 hp hp11 (hdvd p hp)).2
  have hpkg := two_largest_cofactor_package hsqf hodd h3 hn36 hcard22 hprimes hdvd hk4 hsum
  have hk_cases : k = 4 ∨ k = 8 ∨ 12 ≤ k := by
    rcases hk4dvd with ⟨c, rfl⟩
    have hc1 : c = 1 ∨ c = 2 ∨ 3 ≤ c := by omega
    rcases hc1 with rfl | rfl | hc3
    · left; norm_num
    · right; left; norm_num
    · right; right; omega
  rcases hk_cases with rfl | rfl | hk12
  · have hsum4 : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 4 := by
      simpa using hsum
    have hcard8_5 : n.primeFactors.card % 8 = 5 := by
      simpa using hcard8
    have hn27_4 : n % 27 = (9 * (n.primeFactors.card + 3) + 3) % 27 := by
      rwa [show 4 + n.primeFactors.card - 1 = n.primeFactors.card + 3 by omega] at hn27
    by_cases h11 : ∃ p ∈ n.primeFactors, p % 60 = 11
    · rcases h11 with ⟨p, hp, hp11⟩
      obtain ⟨hn5, hn180⟩ := mod_180_of_p60_eq_11 hn0 hn36 hp hp11 (hdvd p hp)
      have hint : ∑ p ∈ n.primeFactors, n / p = 4 * n + 1 :=
        sum_div_eq_mul_add_one_loc hn0 hsum4
      have hmod5 := mod5_sum_count_of_exists_11 hn0 h3 hn5 hprimes hint
      have hmod5_4 : ((n.primeFactors.filter (fun p => p % 60 = 11)).card +
          2 * (n.primeFactors.filter (fun p => p % 60 = 23)).card +
          3 * (n.primeFactors.filter (fun p => p % 60 = 47)).card +
          4 * (n.primeFactors.filter (fun p => p % 60 = 59)).card + 1) % 5 = 4 := by
        simpa using hmod5
      have hcard700 := card_ge_k4_R4 hn0 h3 hprimes hsum4
      have hpkg1 : ∃ p q : ℕ, p ∈ n.primeFactors ∧ q ∈ n.primeFactors ∧ p < q ∧
          (∀ r ∈ n.primeFactors, r ≤ q) ∧ (∀ r ∈ n.primeFactors.erase q, r ≤ p) ∧
          let m := n / (p * q)
          let D := ∑ r ∈ m.primeFactors, m / r
          let A := m - D % m
          let L := m.primeFactors.lcm (fun r => (r - 1) / 2)
          A * (p * q) + 1 = m * (p + q) ∧ A % 24 = 17 ∧
          p < A ^ 2 ∧ m < A ^ 3 ∧ 16 * q < m ∧ n < A ^ 8 ∧ 10 ^ (n.primeFactors.card - 1) < n ∧
          2 * L ∣ n - 1 ∧ ¬ (3 ∣ L) ∧ (5497 : ℚ) / 375 < ∑ d ∈ L.divisors, (1 / (d : ℚ)) ∧
          ((L : ℤ) ∣ (((m : ℤ) ^ 2 * ((q : ℤ) - p)) ^ 2 - (((A : ℤ) + m) ^ 2 - 4 * (m : ℤ) ^ 3))) ∧
          30 * A * ((q - p) / 2) ^ 2 < m ^ 2 := by
        rcases hpkg with ⟨p', q', hp', hq', hlt', hm1', hm2', h1, h2, h3', h4', h5', h6', h7', h8', h9', _, h11', h12', h13'⟩
        exact ⟨p', q', hp', hq', hlt', hm1', hm2', h1, h2, h3', h4', h5', h6', h7', h8', h9', h11', h12', h13'⟩
      exact hH1 n hcomp hsqf hodd h3 h5 hn180 hcard8_5 hcard700 ⟨p, hp, hp11⟩
        hprimes hdvd hno_dvd hn27_4 hmod5_4 hsum4 hpkg1
    · have hno11 : ∀ r ∈ n.primeFactors, r % 60 ≠ 11 := fun r hr h11r => h11 ⟨r, hr, h11r⟩
      have hprimes3 : ∀ p ∈ n.primeFactors, p = 3 ∨ p % 60 = 23 ∨ p % 60 = 47 ∨ p % 60 = 59 := fun p hp => by
        rcases hprimes p hp with rfl | h11p | h23 | h47 | h59
        · exact Or.inl rfl
        · exact absurd h11p (hno11 p hp)
        · exact Or.inr (Or.inl h23)
        · exact Or.inr (Or.inr (Or.inl h47))
        · exact Or.inr (Or.inr (Or.inr h59))
      have hcard5500 := card_ge_k4_R3 hn0 h3 hprimes3 hsum4
      have hpkg2 : ∃ p q : ℕ, p ∈ n.primeFactors ∧ q ∈ n.primeFactors ∧ p < q ∧
          (∀ r ∈ n.primeFactors, r ≤ q) ∧ (∀ r ∈ n.primeFactors.erase q, r ≤ p) ∧
          let m := n / (p * q)
          let D := ∑ r ∈ m.primeFactors, m / r
          let A := m - D % m
          let L := m.primeFactors.lcm (fun r => (r - 1) / 2)
          A * (p * q) + 1 = m * (p + q) ∧ A % 24 = 17 ∧
          p < A ^ 2 ∧ m < A ^ 3 ∧ 16 * q < m ∧ n < A ^ 8 ∧ 10 ^ (n.primeFactors.card - 1) < n ∧
          2 * L ∣ n - 1 ∧ ¬ (3 ∣ L) ∧ ¬ (5 ∣ L) ∧ (5497 : ℚ) / 375 < ∑ d ∈ L.divisors, (1 / (d : ℚ)) ∧
          ((L : ℤ) ∣ (((m : ℤ) ^ 2 * ((q : ℤ) - p)) ^ 2 - (((A : ℤ) + m) ^ 2 - 4 * (m : ℤ) ^ 3))) ∧
          30 * A * ((q - p) / 2) ^ 2 < m ^ 2 := by
        rcases hpkg with ⟨p', q', hp', hq', hlt', hm1', hm2', h1, h2, h3', h4', h5', h6', h7', h8', h9', h10', h11', h12', h13'⟩
        exact ⟨p', q', hp', hq', hlt', hm1', hm2', h1, h2, h3', h4', h5', h6', h7', h8', h9', h10' hno11, h11', h12', h13'⟩
      exact hH2 n hcomp hsqf hodd h3 h5 hn36 hcard8_5 hcard5500 hprimes3 hdvd hno_dvd hn27_4 hsum4 hpkg2
  · have hsum8 : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 8 := by
      simpa using hsum
    have hcard8_1 : n.primeFactors.card % 8 = 1 := by
      simpa using hcard8
    have hn27_8 : n % 27 = (9 * (n.primeFactors.card + 7) + 3) % 27 := by
      rwa [show 8 + n.primeFactors.card - 1 = n.primeFactors.card + 7 by omega] at hn27
    have hcard500k := card_ge_k8_R4 hn0 h3 hprimes hsum8
    exact hH3 n hcomp hsqf hodd h3 h5 hn36 hcard8_1 hcard500k h180_imp hprimes hdvd hno_dvd hn27_8 hsum8 hpkg
  · have hcard350m := card_ge_k12_R4 hn0 h3 hprimes hk12 hsum
    exact hH4 n k hcomp hsqf hodd h3 h5 hn36 hk12 hk4dvd hcard8 hcard350m h180_imp hprimes hdvd hno_dvd hn27 hsum hpkg

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H1_R1_H3_R1
