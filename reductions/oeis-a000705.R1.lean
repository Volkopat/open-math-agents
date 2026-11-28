import OMAStatements.S_oeis_a000705

namespace OMA.R_oeis_a000705_R1

/-- Adjacent supported points with increasing horizontal coordinates share a support line. -/
theorem adjacent_common_support (A B : ℕ → ℝ)
    (hB : ∀ i j : ℕ, 1 ≤ i → i < j → B i < B j)
    {m n : ℕ} (hmpos : 1 ≤ m) (hnpos : 1 ≤ n) (hmn : m < n)
    (hm : ∃ α : ℝ, 0 < α ∧ ∀ k : ℕ, 1 ≤ k →
      A k - α * B k ≤ A m - α * B m)
    (hn : ∃ β : ℝ, 0 < β ∧ ∀ k : ℕ, 1 ≤ k →
      A k - β * B k ≤ A n - β * B n)
    (hnext : ∀ j : ℕ, m < j → j < n →
      ¬ (∃ t : ℝ, 0 < t ∧ ∀ k : ℕ, 1 ≤ k →
        A k - t * B k ≤ A j - t * B j)) :
    ∃ t : ℝ, 0 < t ∧
      (∀ k : ℕ, 1 ≤ k → A k - t * B k ≤ A m - t * B m) ∧
      (∀ k : ℕ, 1 ≤ k → A k - t * B k ≤ A n - t * B n) := by
  classical
  obtain ⟨α, hαpos, hα⟩ := hm
  obtain ⟨β, hβpos, hβ⟩ := hn
  have hD : 0 < B n - B m := sub_pos.mpr (hB m n hmpos hmn)
  let t := (A n - A m) / (B n - B m)
  have hβt : β ≤ t := by
    apply (le_div_iff₀ hD).mpr
    have := hβ m hmpos
    nlinarith
  have htα : t ≤ α := by
    apply (div_le_iff₀ hD).mpr
    have := hα n hnpos
    nlinarith
  have htpos : 0 < t := lt_of_lt_of_le hβpos hβt
  have heq : A m - t * B m = A n - t * B n := by
    have hx : t * (B n - B m) = A n - A m :=
      div_mul_cancel₀ _ (ne_of_gt hD)
    nlinarith
  have hleft (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) :
      A k - t * B k ≤ A m - t * B m := by
    have hBk : B k ≤ B m := by
      rcases lt_or_eq_of_le hkm with hlt | rfl
      · exact le_of_lt (hB k m hk hlt)
      · exact le_rfl
    have := hα k hk
    nlinarith [mul_nonneg (sub_nonneg.mpr htα) (sub_nonneg.mpr hBk)]
  have hright (k : ℕ) (hnk : n ≤ k) :
      A k - t * B k ≤ A n - t * B n := by
    have hBk : B n ≤ B k := by
      rcases lt_or_eq_of_le hnk with hlt | rfl
      · exact le_of_lt (hB n k hnpos hlt)
      · exact le_rfl
    have := hβ k (hnpos.trans hnk)
    nlinarith [mul_nonneg (sub_nonneg.mpr hβt) (sub_nonneg.mpr hBk)]
  obtain ⟨j, hj, hmax⟩ := (Finset.Icc 1 n).exists_max_image
    (fun k => A k - t * B k) ⟨n, Finset.mem_Icc.mpr ⟨hnpos, le_rfl⟩⟩
  have hjpos : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
  have hnj := hmax n (Finset.mem_Icc.mpr ⟨hnpos, le_rfl⟩)
  have hjmax (k : ℕ) (hk : 1 ≤ k) :
      A k - t * B k ≤ A j - t * B j := by
    by_cases hkn : k ≤ n
    · exact hmax k (Finset.mem_Icc.mpr ⟨hk, hkn⟩)
    · exact (hright k (by omega)).trans hnj
  have hjm : A j - t * B j ≤ A m - t * B m := by
    by_cases h : j ≤ m
    · exact hleft j hjpos h
    · have hj_eq : j = n := by
        by_contra hne
        exact hnext j (by omega) (by omega) ⟨t, htpos, hjmax⟩
      simpa [hj_eq] using le_of_eq heq.symm
  refine ⟨t, htpos, ?_, ?_⟩
  · intro k hk
    exact (hjmax k hk).trans hjm
  · intro k hk
    exact ((hjmax k hk).trans hjm).trans (le_of_eq heq)

/-- Taking logarithms converts the divisor objective into an affine score. -/
theorem log_score_le_iff {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (ε : ℝ) :
    Real.log (m.divisors.card : ℝ) - ε * Real.log (m : ℝ) ≤
      Real.log (n.divisors.card : ℝ) - ε * Real.log (n : ℝ) ↔
    (m.divisors.card : ℝ) / (m : ℝ) ^ ε ≤
      (n.divisors.card : ℝ) / (n : ℝ) ^ ε := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmd : 0 < (m.divisors.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr (Nat.nonempty_divisors.mpr (by omega : m ≠ 0)))
  have hnd : 0 < (n.divisors.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr (Nat.nonempty_divisors.mpr (by omega : n ≠ 0)))
  have hmp := Real.rpow_pos_of_pos hm0 ε
  have hnp := Real.rpow_pos_of_pos hn0 ε
  rw [← Real.log_le_log_iff (div_pos hmd hmp) (div_pos hnd hnp),
    Real.log_div (ne_of_gt hmd) (ne_of_gt hmp),
    Real.log_div (ne_of_gt hnd) (ne_of_gt hnp),
    Real.log_rpow hm0, Real.log_rpow hn0]

open OMA.S_oeis_a000705

/-- Consecutive SHC integers share a positive maximizing exponent. -/
theorem shc_common_exponent (m n : ℕ) (hm : IsSHC m) (hn : IsSHC n)
    (hmn : m < n) (hnext : ∀ k, m < k → k < n → ¬ IsSHC k) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ k : ℕ, 1 ≤ k →
        (k.divisors.card : ℝ) / (k : ℝ) ^ ε ≤
          (m.divisors.card : ℝ) / (m : ℝ) ^ ε) ∧
      (∀ k : ℕ, 1 ≤ k →
        (k.divisors.card : ℝ) / (k : ℝ) ^ ε ≤
          (n.divisors.card : ℝ) / (n : ℝ) ^ ε) := by
  have hB (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
      Real.log (i : ℝ) < Real.log (j : ℝ) :=
    Real.log_lt_log (by exact_mod_cast (show 0 < i by omega)) (by exact_mod_cast hij)
  have hm' : ∃ α : ℝ, 0 < α ∧ ∀ k : ℕ, 1 ≤ k →
      Real.log (k.divisors.card : ℝ) - α * Real.log (k : ℝ) ≤
        Real.log (m.divisors.card : ℝ) - α * Real.log (m : ℝ) := by
    obtain ⟨α, hα, hmax⟩ := hm.2
    exact ⟨α, hα, fun k hk => (log_score_le_iff hk hm.1 α).mpr (hmax k hk)⟩
  have hn' : ∃ β : ℝ, 0 < β ∧ ∀ k : ℕ, 1 ≤ k →
      Real.log (k.divisors.card : ℝ) - β * Real.log (k : ℝ) ≤
        Real.log (n.divisors.card : ℝ) - β * Real.log (n : ℝ) := by
    obtain ⟨β, hβ, hmax⟩ := hn.2
    exact ⟨β, hβ, fun k hk => (log_score_le_iff hk hn.1 β).mpr (hmax k hk)⟩
  have hnext' (j : ℕ) (hmj : m < j) (hjn : j < n) :
      ¬ (∃ t : ℝ, 0 < t ∧ ∀ k : ℕ, 1 ≤ k →
        Real.log (k.divisors.card : ℝ) - t * Real.log (k : ℝ) ≤
          Real.log (j.divisors.card : ℝ) - t * Real.log (j : ℝ)) := by
    rintro ⟨t, ht, hmax⟩
    apply hnext j hmj hjn
    have hj : 1 ≤ j := by omega
    exact ⟨hj, t, ht, fun k hk => (log_score_le_iff hk hj t).mp (hmax k hk)⟩
  obtain ⟨t, ht, hmt, hnt⟩ := adjacent_common_support
    (fun k => Real.log (k.divisors.card : ℝ)) (fun k => Real.log (k : ℝ))
    hB hm.1 hn.1 hmn hm' hn' hnext'
  exact ⟨t, ht, fun k hk => (log_score_le_iff hk hm.1 t).mp (hmt k hk),
    fun k hk => (log_score_le_iff hk hn.1 t).mp (hnt k hk)⟩

/-- The integer equation obtained by clearing a rational exponent is rigid. -/
theorem threshold_power_equation {p a r s : ℕ} (hp : p.Prime)
    (hr : 0 < r) (hs : 0 < s)
    (h : p ^ r * a ^ s = (a + 1) ^ s) :
    p = 2 ∧ a = 1 ∧ r = s := by
  have hcop : Nat.Coprime a (a + 1) := by simp
  have had : a ^ s ∣ (a + 1) ^ s :=
    ⟨p ^ r, by simpa [Nat.mul_comm] using h.symm⟩
  have ha : a = 1 := Nat.eq_one_of_dvd_coprimes (hcop.pow_right s)
    dvd_rfl ((dvd_pow_self a (Nat.ne_of_gt hs)).trans had)
  have heq : p ^ r = 2 ^ s := by simpa [ha] using h
  have hpdiv : p ∣ 2 := hp.dvd_of_dvd_pow
    (heq ▸ dvd_pow_self p (Nat.ne_of_gt hr))
  have hp2 : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp hpdiv).resolve_left hp.ne_one
  refine ⟨hp2, ha, ?_⟩
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) (hp2 ▸ heq)

/-- At a positive rational exponent the only threshold is p=2, a=1, epsilon=1. -/
theorem rational_threshold_unique {p a r s : ℕ} (hp : p.Prime)
    (ha : 0 < a) (hr : 0 < r) (hs : 0 < s)
    (h : (p : ℝ) ^ ((r : ℝ) / (s : ℝ)) = ((a : ℝ) + 1) / (a : ℝ)) :
    p = 2 ∧ a = 1 ∧ r = s := by
  have hs0 : (s : ℝ) ≠ 0 := by positivity
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  have hpow := congrArg (fun x : ℝ => x ^ s) h
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p), div_mul_cancel₀ _ hs0,
    Real.rpow_natCast, div_pow] at hpow
  have hreal : (p : ℝ) ^ r * (a : ℝ) ^ s = ((a : ℝ) + 1) ^ s :=
    (eq_div_iff (pow_ne_zero s ha0)).mp hpow
  have hnat : p ^ r * a ^ s = (a + 1) ^ s := by exact_mod_cast hreal
  exact threshold_power_equation hp hr hs hnat

/-- Distinct primes cannot have simultaneous ties at a positive rational exponent. -/
theorem no_rational_threshold_collision {p q a b r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hs : 0 < s)
    (hpa : (p : ℝ) ^ ((r : ℝ) / (s : ℝ)) = ((a : ℝ) + 1) / (a : ℝ)) :
    (q : ℝ) ^ ((r : ℝ) / (s : ℝ)) ≠ ((b : ℝ) + 1) / (b : ℝ) := by
  intro hqb
  have hp2 := (rational_threshold_unique hp ha hr hs hpa).1
  have hq2 := (rational_threshold_unique hq hb hr hs hqb).1
  exact hpq (hp2.trans hq2.symm)

/- Local prime factors classify two distinct global maximizers. -/
def H1 : Prop :=
∀ m n : ℕ, 1 ≤ m → 1 ≤ n → m < n →
    ∀ ε : ℝ, 0 < ε →
    (∀ k : ℕ, 1 ≤ k →
      (k.divisors.card : ℝ) / (k : ℝ) ^ ε ≤
        (m.divisors.card : ℝ) / (m : ℝ) ^ ε) →
    (∀ k : ℕ, 1 ≤ k →
      (k.divisors.card : ℝ) / (k : ℝ) ^ ε ≤
        (n.divisors.card : ℝ) / (n : ℝ) ^ ε) →
    (∃ p : ℕ, p.Prime ∧ n = p * m) ∨
      ∃ p q a b : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧
        0 < a ∧ 0 < b ∧
        (p : ℝ) ^ ε = ((a : ℝ) + 1) / (a : ℝ) ∧
        (q : ℝ) ^ ε = ((b : ℝ) + 1) / (b : ℝ)

/- Distinct primes cannot tie together; the rational case is proved above. -/
def H2 : Prop :=
∀ p q a b : ℕ, p.Prime → q.Prime → p ≠ q →
    0 < a → 0 < b → ∀ ε : ℝ, 0 < ε →
    (p : ℝ) ^ ε = ((a : ℝ) + 1) / (a : ℝ) →
    (q : ℝ) ^ ε ≠ ((b : ℝ) + 1) / (b : ℝ)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a000705.main := by
  intro h1 h2 m n hm hn hmn hnext
  obtain ⟨ε, hε, hmε, hnε⟩ := shc_common_exponent m n hm hn hmn hnext
  rcases h1 m n hm.1 hn.1 hmn ε hε hmε hnε with hprime | hcollision
  · exact hprime
  · obtain ⟨p, q, a, b, hp, hq, hpq, ha, hb, hpa, hqb⟩ := hcollision
    exact False.elim (h2 p q a b hp hq hpq ha hb ε hε hpa hqb)

end OMA.R_oeis_a000705_R1
