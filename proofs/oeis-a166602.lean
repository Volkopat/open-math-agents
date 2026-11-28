import OMAStatements.S_oeis_a166602

/-!
Proof of R. J. Mathar's conjecture on OEIS A166602 (Nov 06, 2025):
For every `k ≥ 1`, `(∑_{i=1}^k i^2) ∣ (∏_{i=1}^k i^2)` iff `k = 1` or `k! * B_{2k} ∈ ℤ`.

Both sides (for `k ≥ 2`) are shown equivalent to `¬ (k + 1).Prime ∧ ¬ (2 * k + 1).Prime`:
1. Since `6 * ∑_{i=1}^k i^2 = k * (k + 1) * (2 * k + 1)` and `∏_{i=1}^k i^2 = (k!)^2`, the
   divisibility is equivalent to `(k + 1) * (2 * k + 1) ∣ 6 * k! * (k - 1)!`. For `k ≥ 4`,
   primality of `k + 1` or `2 * k + 1` gives a prime `> k` and `> 3`, impossible; conversely
   when both are composite, each splits into two factors `≤ k - 1`, and `gcd(k+1, 2k+1) = 1`.
2. By Mathlib's `Bernoulli.vonStaudt_clausen`, `B_{2k} + ∑_{p prime, (p-1)|2k} 1/p ∈ ℤ`.
   Multiplying by `k!`, every prime `p ≤ k` gives an integer term `k!/p`, while the only
   possible primes `p > k` with `(p - 1) ∣ 2 * k` are `k + 1` and `2 * k + 1`. If either is
   prime, clearing the other denominators shows the sum cannot be an integer.
-/

namespace A166602Proof

open Finset

private lemma six_mul_sum_sq (k : ℕ) :
    6 * (∑ i ∈ Finset.Icc 1 k, i ^ 2) = k * (k + 1) * (2 * k + 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : n + 1 ∉ Finset.Icc 1 n := by
      simp only [Finset.mem_Icc]
      omega
    rw [hIcc, Finset.sum_insert hnot, Nat.mul_add, ih]
    ring

private lemma prod_sq_eq (k : ℕ) :
    ∏ i ∈ Finset.Icc 1 k, i ^ 2 = k.factorial * k.factorial := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : n + 1 ∉ Finset.Icc 1 n := by
      simp only [Finset.mem_Icc]
      omega
    rw [hIcc, Finset.prod_insert hnot, ih, Nat.factorial_succ]
    ring

private lemma dvd_iff_not_prime {k : ℕ} (hk : 1 ≤ k) :
    (∑ i ∈ Finset.Icc 1 k, i ^ 2) ∣ (∏ i ∈ Finset.Icc 1 k, i ^ 2) ↔
      k = 1 ∨ (¬ (k + 1).Prime ∧ ¬ (2 * k + 1).Prime) := by
  have hsum : 6 * (∑ i ∈ Finset.Icc 1 k, i ^ 2) = k * (k + 1) * (2 * k + 1) := six_mul_sum_sq k
  have hprod : ∏ i ∈ Finset.Icc 1 k, i ^ 2 = k.factorial * k.factorial := prod_sq_eq k
  have hiff : (∑ i ∈ Finset.Icc 1 k, i ^ 2) ∣ (∏ i ∈ Finset.Icc 1 k, i ^ 2) ↔
      (k + 1) * (2 * k + 1) ∣ 6 * (k.factorial * (k - 1).factorial) := by
    have hkfac : k.factorial = k * (k - 1).factorial := by
      cases k with
      | zero => omega
      | succ m => simp [Nat.factorial_succ]
    constructor
    · intro hd
      have h6 : 6 * (∑ i ∈ Finset.Icc 1 k, i ^ 2) ∣ 6 * (∏ i ∈ Finset.Icc 1 k, i ^ 2) :=
        Nat.mul_dvd_mul_left 6 hd
      rw [hsum, hprod] at h6
      have hrew : 6 * (k.factorial * k.factorial) = k * (6 * (k.factorial * (k - 1).factorial)) := by
        nth_rw 2 [hkfac]; ring
      have hl : k * (k + 1) * (2 * k + 1) = k * ((k + 1) * (2 * k + 1)) := by ring
      rw [hrew, hl] at h6
      exact (Nat.mul_dvd_mul_iff_left (by omega : 0 < k)).mp h6
    · intro hd
      have hmul : k * ((k + 1) * (2 * k + 1)) ∣ k * (6 * (k.factorial * (k - 1).factorial)) :=
        Nat.mul_dvd_mul_left k hd
      have hrew : k * (6 * (k.factorial * (k - 1).factorial)) = 6 * (∏ i ∈ Finset.Icc 1 k, i ^ 2) := by
        rw [hprod]; nth_rw 2 [hkfac]; ring
      have hl : k * ((k + 1) * (2 * k + 1)) = 6 * (∑ i ∈ Finset.Icc 1 k, i ^ 2) := by
        rw [hsum]; ring
      rw [hl, hrew] at hmul
      exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 6)).mp hmul
  rw [hiff]
  rcases eq_or_ne k 1 with rfl | hk1
  · simp
  rcases eq_or_ne k 2 with rfl | hk2
  · constructor
    · intro h; exfalso; norm_num at h
    · rintro (h | ⟨h1, _⟩)
      · omega
      · exact (h1 (by decide)).elim
  rcases eq_or_ne k 3 with rfl | hk3
  · constructor
    · intro h; exfalso; norm_num at h
    · rintro (h | ⟨_, h2⟩)
      · omega
      · exact (h2 (by decide)).elim
  have hk4 : 4 ≤ k := by omega
  constructor
  · intro hd
    right
    constructor
    · intro hp
      have hd1 : k + 1 ∣ 6 * (k.factorial * (k - 1).factorial) :=
        dvd_trans (dvd_mul_right _ _) hd
      rcases hp.dvd_mul.mp hd1 with h6 | hfac
      · have hle : k + 1 ≤ 6 := Nat.le_of_dvd (by decide) h6
        have h56 : k + 1 = 5 ∨ k + 1 = 6 := by omega
        rcases h56 with h5 | h6'
        · rw [h5] at h6; norm_num at h6
        · rw [h6'] at hp; exact (by decide : ¬ Nat.Prime 6) hp
      · rcases hp.dvd_mul.mp hfac with hf1 | hf2
        · have := hp.dvd_factorial.mp hf1; omega
        · have := hp.dvd_factorial.mp hf2; omega
    · intro hp
      have hd2 : 2 * k + 1 ∣ 6 * (k.factorial * (k - 1).factorial) :=
        dvd_trans (dvd_mul_left _ _) hd
      rcases hp.dvd_mul.mp hd2 with h6 | hfac
      · have := Nat.le_of_dvd (by decide) h6; omega
      · rcases hp.dvd_mul.mp hfac with hf1 | hf2
        · have := hp.dvd_factorial.mp hf1; omega
        · have := hp.dvd_factorial.mp hf2; omega
  · rintro (h | ⟨hnp1, hnp2⟩)
    · exact (hk1 h).elim
    · have hcop : Nat.Coprime (k + 1) (2 * k + 1) := by
        apply Nat.coprime_of_dvd'
        intro p _ h1 h2
        have h3 : p ∣ 2 * (k + 1) - (2 * k + 1) := Nat.dvd_sub (dvd_mul_of_dvd_right h1 2) h2
        have h4 : 2 * (k + 1) - (2 * k + 1) = 1 := by omega
        rwa [h4] at h3
      have hd1 : k + 1 ∣ k.factorial * (k - 1).factorial := by
        let a := (k + 1).minFac
        have ha_prime : a.Prime := Nat.minFac_prime (by omega)
        have ha_dvd : a ∣ k + 1 := Nat.minFac_dvd (k + 1)
        obtain ⟨b, hb⟩ := ha_dvd
        have ha_lt : a < k + 1 := by
          have hle : a ≤ k + 1 := Nat.le_of_dvd (by omega) ⟨b, hb⟩
          have hne : a ≠ k + 1 := fun heq => hnp1 (heq ▸ ha_prime)
          omega
        have ha2 : 2 ≤ a := ha_prime.two_le
        have hb2 : 2 ≤ b := by
          by_contra! hlt
          have : b = 0 ∨ b = 1 := by omega
          rcases this with rfl | rfl <;> omega
        have ha_le1 : a + 1 ≤ k := by
          have : a * 2 ≤ a * b := Nat.mul_le_mul_left a hb2
          omega
        have hb_le1 : b + 1 ≤ k := by
          have : 2 * b ≤ a * b := Nat.mul_le_mul_right b ha2
          omega
        have hb_le : b ≤ k - 1 := by omega
        rw [hb]
        exact Nat.mul_dvd_mul (Nat.dvd_factorial (by omega) (by omega))
          (Nat.dvd_factorial (by omega) hb_le)
      have hd2 : 2 * k + 1 ∣ k.factorial * (k - 1).factorial := by
        let c := (2 * k + 1).minFac
        have hc_prime : c.Prime := Nat.minFac_prime (by omega)
        have hc_dvd : c ∣ 2 * k + 1 := Nat.minFac_dvd (2 * k + 1)
        obtain ⟨d, hd⟩ := hc_dvd
        have hc_ne2 : c ≠ 2 := by
          intro h2
          rw [h2] at hd
          omega
        have hc3 : 3 ≤ c := by
          have := hc_prime.two_le; omega
        have hc_lt : c < 2 * k + 1 := by
          have hle : c ≤ 2 * k + 1 := Nat.le_of_dvd (by omega) ⟨d, hd⟩
          have hne : c ≠ 2 * k + 1 := fun heq => hnp2 (heq ▸ hc_prime)
          omega
        have hd_ne2 : d ≠ 2 := by
          intro h2; rw [h2] at hd; omega
        have hd3 : 3 ≤ d := by
          by_contra! hlt
          have : d = 0 ∨ d = 1 ∨ d = 2 := by omega
          rcases this with rfl | rfl | rfl <;> omega
        have hc_le1 : c + 1 ≤ k := by
          have : c * 3 ≤ c * d := Nat.mul_le_mul_left c hd3
          omega
        have hd_le1 : d + 1 ≤ k := by
          have : 3 * d ≤ c * d := Nat.mul_le_mul_right d hc3
          omega
        have hd_le : d ≤ k - 1 := by omega
        rw [hd]
        exact Nat.mul_dvd_mul (Nat.dvd_factorial (by omega) (by omega))
          (Nat.dvd_factorial (by omega) hd_le)
      exact dvd_trans (hcop.mul_dvd_of_dvd_of_dvd hd1 hd2) (dvd_mul_left _ _)

private lemma mem_int_range_iff_sub {x : ℚ} {m : ℤ} :
    x ∈ Set.range (Int.cast : ℤ → ℚ) ↔ (m : ℚ) - x ∈ Set.range (Int.cast : ℤ → ℚ) := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨m - z, by push_cast; linarith⟩
  · rintro ⟨z, hz⟩
    exact ⟨m - z, by push_cast; linarith⟩

private lemma bernoulli_int_iff_not_prime {k : ℕ} (hk : 1 ≤ k) :
    (k.factorial : ℚ) * bernoulli (2 * k) ∈ Set.range (Int.cast : ℤ → ℚ) ↔
      ¬ (k + 1).Prime ∧ ¬ (2 * k + 1).Prime := by
  let S : Finset ℕ := (Finset.range (2 * k + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ 2 * k)
  obtain ⟨m, hm⟩ := Bernoulli.vonStaudt_clausen k
  have hsum_eq : (k.factorial : ℚ) * bernoulli (2 * k) =
      ((k.factorial : ℤ) * m : ℤ) - ∑ p ∈ S, (k.factorial : ℚ) / (p : ℚ) := by
    have hmul : (k.factorial : ℚ) * (bernoulli (2 * k) + ∑ p ∈ S, (1 : ℚ) / p) =
        (k.factorial : ℚ) * (m : ℚ) := by
      rw [hm]
    rw [mul_add, Finset.mul_sum] at hmul
    have hrew : ∑ p ∈ S, (k.factorial : ℚ) * ((1 : ℚ) / (p : ℚ)) =
        ∑ p ∈ S, (k.factorial : ℚ) / (p : ℚ) := by
      apply Finset.sum_congr rfl
      intro p _; ring
    rw [hrew] at hmul
    push_cast
    linarith
  have hmem_iff : (k.factorial : ℚ) * bernoulli (2 * k) ∈ Set.range (Int.cast : ℤ → ℚ) ↔
      (∑ p ∈ S, (k.factorial : ℚ) / (p : ℚ)) ∈ Set.range (Int.cast : ℤ → ℚ) := by
    rw [hsum_eq, ← mem_int_range_iff_sub (m := (k.factorial : ℤ) * m)]
  rw [hmem_iff]
  have hprime_not_int : ∀ q ∈ S, k < q →
      (∑ p ∈ S, (k.factorial : ℚ) / (p : ℚ)) ∉ Set.range (Int.cast : ℤ → ℚ) := by
    intro q hqS hkq ⟨z, hz⟩
    have hq_prime : q.Prime := (Finset.mem_filter.mp hqS).2.1
    let P : ℕ := ∏ p ∈ S.erase q, p
    have hq_ndvd_P : ¬ q ∣ P := by
      intro hd
      rw [hq_prime.prime.dvd_finsetProd_iff] at hd
      obtain ⟨p, hp, hqp⟩ := hd
      have hp_prime : p.Prime := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)).2.1
      have hne : p ≠ q := (Finset.mem_erase.mp hp).1
      exact hne ((Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp hqp).symm
    have hq_ndvd_fac : ¬ q ∣ k.factorial := by
      intro hd
      have := hq_prime.dvd_factorial.mp hd
      omega
    have hrest_int : ∃ w : ℤ,
        (P : ℚ) * (∑ p ∈ S.erase q, (k.factorial : ℚ) / (p : ℚ)) = (w : ℚ) := by
      rw [Finset.mul_sum]
      have hterm : ∀ p ∈ S.erase q, ∃ t : ℤ, (P : ℚ) * ((k.factorial : ℚ) / (p : ℚ)) = (t : ℚ) := by
        intro p hp
        have hp_dvd : p ∣ P := Finset.dvd_prod_of_mem _ hp
        obtain ⟨r, hr⟩ := hp_dvd
        have hp_ne : (p : ℚ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)).2.1.ne_zero
        refine ⟨(r * k.factorial : ℕ), ?_⟩
        have hP : (P : ℚ) = (p : ℚ) * (r : ℚ) := by exact_mod_cast hr
        rw [hP]
        push_cast
        field_simp [hp_ne]
      choose f hf using hterm
      refine ⟨∑ p ∈ (S.erase q).attach, f p.1 p.2, ?_⟩
      rw [Int.cast_sum, ← Finset.sum_attach (S.erase q) (fun p => (P : ℚ) * ((k.factorial : ℚ) / (p : ℚ)))]
      apply Finset.sum_congr rfl
      intro p _
      exact hf p.1 p.2
    obtain ⟨w, hw⟩ := hrest_int
    have hsplit : ∑ p ∈ S, (k.factorial : ℚ) / (p : ℚ) =
        (k.factorial : ℚ) / (q : ℚ) + ∑ p ∈ S.erase q, (k.factorial : ℚ) / (p : ℚ) :=
      (Finset.add_sum_erase S _ hqS).symm
    have hPz : (P : ℚ) * ((k.factorial : ℚ) / (q : ℚ)) = ((P : ℤ) * z - w : ℤ) := by
      have h1 : (P : ℚ) * (∑ p ∈ S, (k.factorial : ℚ) / (p : ℚ)) = (P : ℚ) * (z : ℚ) := by
        rw [← hz]
      rw [hsplit, mul_add, hw] at h1
      push_cast
      linarith
    have hq_ne : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq_prime.ne_zero
    have hmulZ : ((P * k.factorial : ℕ) : ℤ) = (q : ℤ) * ((P : ℤ) * z - w) := by
      have hQ : ((P * k.factorial : ℕ) : ℚ) = (q : ℚ) * (((P : ℤ) * z - w : ℤ) : ℚ) := by
        have := congrArg (fun x => (q : ℚ) * x) hPz
        push_cast at this ⊢
        field_simp [hq_ne] at this
        linarith
      exact_mod_cast hQ
    have hqdvd : q ∣ P * k.factorial := by
      have hZ : (q : ℤ) ∣ ((P * k.factorial : ℕ) : ℤ) := ⟨(P : ℤ) * z - w, hmulZ⟩
      exact Int.ofNat_dvd.mp hZ
    rcases hq_prime.dvd_mul.mp hqdvd with h1 | h2
    · exact hq_ndvd_P h1
    · exact hq_ndvd_fac h2
  constructor
  · intro hint
    constructor
    · intro hp1
      have hmem : k + 1 ∈ S := by
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hp1, ⟨2, by omega⟩⟩
      exact hprime_not_int (k + 1) hmem (by omega) hint
    · intro hp2
      have hmem : 2 * k + 1 ∈ S := by
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hp2, ⟨1, by omega⟩⟩
      exact hprime_not_int (2 * k + 1) hmem (by omega) hint
  · rintro ⟨hnp1, hnp2⟩
    have hall_le : ∀ p ∈ S, p ≤ k := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_range] at hp
      obtain ⟨_, hp_prime, d, hd⟩ := hp
      by_contra! hgt
      have hp1 : k ≤ p - 1 := by omega
      rcases eq_or_ne d 0 with rfl | hd0
      · simp at hd; omega
      rcases eq_or_ne d 1 with rfl | hd1
      · have : p = 2 * k + 1 := by omega
        exact hnp2 (this ▸ hp_prime)
      rcases eq_or_ne d 2 with rfl | hd2
      · have : p = k + 1 := by omega
        exact hnp1 (this ▸ hp_prime)
      have hd3 : 3 ≤ d := by omega
      nlinarith
    have hterm : ∀ p ∈ S, ∃ t : ℤ, (k.factorial : ℚ) / (p : ℚ) = (t : ℚ) := by
      intro p hp
      have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2.1
      have hp_le : p ≤ k := hall_le p hp
      obtain ⟨r, hr⟩ := Nat.dvd_factorial hp_prime.pos hp_le
      have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp_prime.ne_zero
      refine ⟨(r : ℤ), ?_⟩
      have hfac : (k.factorial : ℚ) = (p : ℚ) * (r : ℚ) := by exact_mod_cast hr
      rw [hfac]
      field_simp [hp_ne]
      simp
    choose f hf using hterm
    refine ⟨∑ p ∈ S.attach, f p.1 p.2, ?_⟩
    rw [Int.cast_sum, ← Finset.sum_attach S]
    apply Finset.sum_congr rfl
    intro p _
    exact (hf p.1 p.2).symm

theorem solve : ∀ k : ℕ, 1 ≤ k →
    ((∑ i ∈ Finset.Icc 1 k, i ^ 2) ∣ (∏ i ∈ Finset.Icc 1 k, i ^ 2) ↔
      k = 1 ∨ (k.factorial : ℚ) * bernoulli (2 * k) ∈ Set.range (Int.cast : ℤ → ℚ)) := by
  intro k hk
  rw [dvd_iff_not_prime hk, bernoulli_int_iff_not_prime hk]

end A166602Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a166602.main :=
  A166602Proof.solve
