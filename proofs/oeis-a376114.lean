import OMAStatements.S_oeis_a376114

/-!
# Doubling the terms of OEIS A376114 gives A181795

For odd `u`, the odd divisors of `2^s * u` are the divisors of `u`,
and the number of even divisors is `s * u.divisors.card`.
When the latter divides the number and the odd divisor count is odd,
the same count already divides half the number.

Sources: https://oeis.org/A376114 and https://oeis.org/A181795.
Credit: @Solitude1312
-/

open OMA.S_oeis_a376114

namespace OMA.DivisorCounts

private lemma odd_product {f : ℕ → ℕ} (S : Finset ℕ) :
    Odd (∏ i ∈ S, f i) ↔ ∀ i ∈ S, Odd (f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih => simp [hx, Nat.odd_mul, ih]

private lemma odd_count_iff_square {n : ℕ} (hn : n ≠ 0) :
    Odd n.divisors.card ↔ IsSquare n := by
  rw [Nat.card_divisors hn, odd_product]
  constructor
  · intro h
    refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
    rw [← pow_two, ← Finset.prod_pow]
    calc
      n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := Nat.prod_primeFactors_pow_factorization hn
      _ = _ := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [← pow_mul]
        have := (Nat.odd_iff.mp (h p hp))
        congr 1
        omega
  · rintro ⟨x, rfl⟩ p _
    have hx : x ≠ 0 := by aesop
    rw [Nat.factorization_mul hx hx, Finsupp.add_apply]
    exact ⟨x.factorization p, by omega⟩

private lemma odd_divisors (s : ℕ) {u : ℕ} (hu : Odd u) :
    ((2 ^ s * u).divisors.filter Odd) = u.divisors := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, _⟩, ho⟩
    exact ⟨(ho.coprime_two_right.pow_right s).dvd_of_dvd_mul_left hd, hu.pos.ne'⟩
  · rintro ⟨hd, _⟩
    refine ⟨⟨dvd_mul_of_dvd_right hd _, by positivity⟩, ?_⟩
    exact Nat.coprime_two_left.mp (hu.coprime_two_left.of_dvd_right hd)

private lemma divisor_count (s : ℕ) {u : ℕ} (hu : Odd u) :
    (2 ^ s * u).divisors.card = (s + 1) * u.divisors.card := by
  rw [(hu.coprime_two_left.pow_left s).card_divisors_mul,
    ← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two]

private lemma even_divisor_count (s : ℕ) {u : ℕ} (hu : Odd u) :
    ((2 ^ s * u).divisors.filter Even).card = s * u.divisors.card := by
  have h := Finset.card_filter_add_card_filter_not (s := (2 ^ s * u).divisors) Even
  simp only [Nat.not_even_iff_odd, odd_divisors s hu, divisor_count s hu, Nat.add_mul,
    one_mul] at h
  omega

/-- The power of two in `s` has exponent at most `s - 1`. -/
private lemma halve_divisibility {s u d : ℕ} (hs : 0 < s) (hd : Odd d)
    (h : s * d ∣ 2 ^ s * u) : s * d ∣ 2 ^ (s - 1) * u := by
  obtain ⟨v, w, hw, hsw⟩ := Nat.exists_eq_two_pow_mul_odd hs.ne'
  have hv : v ≤ s - 1 := by
    have hpow : 2 ^ v ≤ s := by
      rw [hsw]
      exact Nat.le_mul_of_pos_right _ hw.pos
    have := v.lt_two_pow_self
    omega
  have hsd : s * d = 2 ^ v * (w * d) := by rw [hsw, Nat.mul_assoc]
  rw [hsd] at h ⊢
  have hwdu : w * d ∣ u :=
    (((hw.mul hd).coprime_two_right).pow_right s).dvd_of_dvd_mul_left
      ((dvd_mul_left (w * d) (2 ^ v)).trans h)
  exact Nat.mul_dvd_mul (pow_dvd_pow 2 hv) hwdu

private lemma counts_at (s : ℕ) {u : ℕ} (hu : Odd u) :
    inA181795 (2 ^ s * u) ↔ Odd u.divisors.card ∧ Even s ∧
      s * u.divisors.card ∣ 2 ^ s * u := by
  simp only [inA181795, odd_divisors s hu, even_divisor_count s hu]
  constructor
  · rintro ⟨_, ho, _, he, hd⟩
    exact ⟨ho, (Nat.even_mul.mp he).resolve_right (Nat.not_even_iff_odd.mpr ho), hd⟩
  · rintro ⟨ho, he, hd⟩
    exact ⟨Nat.mul_pos (by positivity) hu.pos, ho,
      (dvd_mul_left u.divisors.card s).trans hd, he.mul_right _, hd⟩

private lemma double_pow (s u : ℕ) : 2 * (2 ^ s * u) = 2 ^ (s + 1) * u := by
  rw [pow_succ]
  ring

/-- Doubling gives an exact correspondence of the two sets of positive terms. -/
private lemma membership (k : ℕ) :
    inA181795 k ↔ ∃ m : ℕ, inA376114 m ∧ 2 * m = k := by
  constructor
  · intro hk
    have hk0 : 0 < k := hk.1
    obtain ⟨s, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk0.ne'
    obtain ⟨ho, he, hd⟩ := (counts_at s hu).mp hk
    have hs : 0 < s := by
      by_contra! hz
      have hz' : s = 0 := by omega
      simp [hz', hu.pos.ne'] at hd
    obtain ⟨j, hj⟩ := he
    have hs' : s = 2 * (j - 1) + 2 := by omega
    obtain ⟨r, hr⟩ := (odd_count_iff_square hu.pos.ne').mp ho
    refine ⟨2 ^ (s - 1) * u,
      ⟨Nat.mul_pos (by positivity) hu.pos, ⟨2 ^ (j - 1) * r, ?_⟩, ?_⟩, ?_⟩
    · rw [show s - 1 = (j - 1) + (j - 1) + 1 by omega, pow_succ, pow_add, hr]
      ring
    · rw [divisor_count _ hu, Nat.sub_add_cancel hs]
      exact halve_divisibility hs ho hd
    · rw [double_pow, Nat.sub_add_cancel hs]
  · rintro ⟨m, ⟨hm, ⟨t, rfl⟩, hd⟩, rfl⟩
    have ht : t ≠ 0 := by aesop
    obtain ⟨b, v, hv, rfl⟩ := Nat.exists_eq_two_pow_mul_odd ht
    have hv2 : Odd (v ^ 2) := hv.pow
    have hm' : 2 * (2 ^ b * v) ^ 2 = 2 ^ (2 * b + 1) * v ^ 2 := by
      rw [two_mul b, pow_succ, pow_add]
      ring
    rw [hm', double_pow, counts_at _ hv2]
    refine ⟨(odd_count_iff_square (pow_ne_zero _ hv.pos.ne')).mpr ⟨v, pow_two v⟩,
      ⟨b + 1, by omega⟩, ?_⟩
    rw [hm', divisor_count _ hv2] at hd
    exact hd.trans (double_pow (2 * b + 1) (v ^ 2) ▸ dvd_mul_left _ 2)

private lemma infinite_counts : (Set.ofPred inA181795).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro b
  let s := 2 ^ (b + 1)
  refine ⟨2 ^ s, ?_, ?_⟩
  · change inA181795 (2 ^ s)
    rw [← Nat.mul_one (2 ^ s), counts_at s (by decide : Odd 1)]
    simp only [Nat.divisors_one, Finset.card_singleton, mul_one]
    refine ⟨by decide, ⟨2 ^ b, ?_⟩, pow_dvd_pow 2 (b + 1).lt_two_pow_self.le⟩
    dsimp [s]
    rw [pow_succ]
    omega
  · exact (lt_trans (Nat.lt_succ_self b) (b + 1).lt_two_pow_self).trans s.lt_two_pow_self

lemma nth_equal (i : ℕ) : 2 * Nat.nth inA376114 i = Nat.nth inA181795 i := by
  let f := fun m : ℕ => 2 * m
  have hf : StrictMono f := by intro a b hab; dsimp [f]; omega
  have hr : ∀ k, inA181795 k → k ∈ Set.range f := by
    intro k hk
    obtain ⟨m, _, hm⟩ := (membership k).mp hk
    exact ⟨m, hm⟩
  have he : (fun m => inA181795 (f m)) = inA376114 := by
    funext m
    apply propext
    rw [membership]
    constructor
    · rintro ⟨x, hx, eq⟩
      have : x = m := hf.injective eq
      simpa [this] using hx
    · exact fun h => ⟨m, h, rfl⟩
  have hn := Nat.nth_comp_of_strictMono (p := inA181795) (n := i) hf hr
    (fun hfin => (infinite_counts hfin).elim)
  rw [he] at hn
  exact hn

end OMA.DivisorCounts

theorem OMA.solution : type_of% @OMA.S_oeis_a376114.main := by
  intro n _
  have := OMA.DivisorCounts.nth_equal (n - 1)
  omega
