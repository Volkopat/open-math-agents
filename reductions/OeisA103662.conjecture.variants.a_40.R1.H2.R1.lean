import OMAReductions.R_OeisA103662_conjecture_variants_a_40_R1

/-!
# Decimal prefix and suffix restrictions for the fortieth-power problem

At precision d at most 40 times the 2-adic valuation of the base, the odd
part modulo 5^(d-1) determines the decimal suffix of the power. A separate
criterion detects zero digits from intervals containing the leading part of
the base. The remaining cases have 2-adic valuation one and at least two.
-/

namespace OMA.R_OeisA103662_conjecture_variants_a_40_R1_H2_R1

private lemma fifth_power_lift {x M t : ℕ} (hM : 5 ∣ M) :
    (x + M * t) ^ 5 ≡ x ^ 5 [MOD M * 5] := by
  obtain ⟨w, rfl⟩ := hM
  let z := 5 * w * t
  have heq : (x + z) ^ 5 =
      x ^ 5 + (5 * w * 5) *
        (t * (x ^ 4 + 2 * x ^ 3 * z + 2 * x ^ 2 * z ^ 2 + x * z ^ 3 + w * t * z ^ 3)) := by
    dsimp only [z]
    ring
  change (x + z) ^ 5 % (5 * w * 5) = x ^ 5 % (5 * w * 5)
  rw [heq, Nat.add_mul_mod_self_left]

private lemma pow40_suffix {k m d : ℕ} (hd : 2 ≤ d) (hd2 : d ≤ 40 * k) :
    ((2 ^ k * m) ^ 40) % 10 ^ d =
      ((2 ^ k * (m % 5 ^ (d - 1))) ^ 40) % 10 ^ d := by
  let M := 5 ^ (d - 1)
  let a := 2 ^ k * (m % M)
  let t := 2 ^ k * (m / M)
  have heq : 2 ^ k * m = a + M * t := by
    calc
      2 ^ k * m = 2 ^ k * (m % M + M * (m / M)) :=
        congrArg (fun n => 2 ^ k * n) (Nat.mod_add_div m M).symm
      _ = a + M * t := by dsimp only [a, t]; ring
  have h5M : 5 ∣ M := dvd_pow (dvd_refl _) (by omega : d - 1 ≠ 0)
  have hM : 5 ^ d = M * 5 := by
    dsimp only [M]
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)]
  have h5 : (2 ^ k * m) ^ 40 ≡ a ^ 40 [MOD 5 ^ d] := by
    have h := (fifth_power_lift (x := a) (t := t) h5M).pow 8
    rw [← heq, ← hM, ← pow_mul, ← pow_mul] at h
    exact h
  have htwo (u : ℕ) : 2 ^ d ∣ (2 ^ k * u) ^ 40 := by
    rw [mul_pow, ← pow_mul]
    exact (pow_dvd_pow 2 (show d ≤ k * 40 by omega)).trans (dvd_mul_right _ _)
  have h2 : (2 ^ k * m) ^ 40 ≡ a ^ 40 [MOD 2 ^ d] :=
    (Nat.modEq_zero_iff_dvd.mpr (htwo m)).trans
      (Nat.modEq_zero_iff_dvd.mpr (htwo (m % M))).symm
  have hcop : (2 ^ d).Coprime (5 ^ d) :=
    ((by decide : Nat.Coprime 2 5).pow_left d).pow_right d
  have h := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h2, h5⟩
  rw [← mul_pow] at h
  exact h

private lemma padded_suffix_of_no_zero {n d : ℕ} (hd : 1 ≤ d) (hn : 10 ^ d ≤ n)
    (hno : 0 ∉ Nat.digits 10 n) :
    10 ^ (d - 1) ≤ n % 10 ^ d ∧ 0 ∉ Nat.digits 10 (n % 10 ^ d) := by
  let s := n % 10 ^ d
  let len := (Nat.digits 10 s).length
  have hlen : len ≤ d := (Nat.digits_length_le_iff (by decide) s).mpr
    (Nat.mod_lt n (by positivity))
  have hquot : 0 < n / 10 ^ d := Nat.div_pos hn (by positivity)
  have hsplit : Nat.digits 10 s ++ List.replicate (d - len) 0 ++ Nat.digits 10 (n / 10 ^ d) =
      Nat.digits 10 n := by
    have h := Nat.digits_append_zeroes_append_digits (b := 10) (k := d - len) (n := s)
      (by decide) hquot
    change _ = Nat.digits 10 (s + 10 ^ (len + (d - len)) * (n / 10 ^ d)) at h
    rw [Nat.add_sub_of_le hlen] at h
    exact h.trans (congrArg (Nat.digits 10) (Nat.mod_add_div n (10 ^ d)))
  have hs : d ≤ len := by
    by_contra! hlt
    have hm : 0 ∈ List.replicate (d - len) (0 : ℕ) := List.mem_replicate.mpr ⟨by omega, rfl⟩
    exact hno (hsplit ▸ (List.mem_append_left _ (List.mem_append_right _ hm)))
  refine ⟨(Nat.lt_digits_length_iff (by decide) s).mp (by omega), ?_⟩
  intro hm
  exact hno (hsplit ▸ (List.mem_append_left _ (List.mem_append_left _ hm)))

private lemma suffix_filter {k m : ℕ} (hno : 0 ∉ Nat.digits 10 ((2 ^ k * m) ^ 40)) :
    ∀ d : ℕ, 2 ≤ d → d ≤ 40 * k → 10 ^ d ≤ (2 ^ k * m) ^ 40 →
      let r := ((2 ^ k * (m % 5 ^ (d - 1))) ^ 40) % 10 ^ d
      10 ^ (d - 1) ≤ r ∧ 0 ∉ Nat.digits 10 r := by
  intro d hd hd2 hn
  have h := padded_suffix_of_no_zero (show 1 ≤ d by omega) hn hno
  rw [pow40_suffix hd hd2] at h
  exact h

private lemma zero_of_leading_interval {b A s i q : ℕ}
    (hlo : A * 10 ^ s ≤ b) (hhi : b < (A + 1) * 10 ^ s)
    (hpowlo : q * 10 ^ i ≤ A ^ 40) (hpowhi : (A + 1) ^ 40 ≤ (q + 1) * 10 ^ i)
    (hq : 0 < q) (hzero : q % 10 = 0) : 0 ∈ Nat.digits 10 (b ^ 40) := by
  have hmul (c : ℕ) : (c * 10 ^ s) ^ 40 = c ^ 40 * 10 ^ (40 * s) := by
    rw [mul_pow, ← pow_mul, mul_comm s 40]
  have hl : q * 10 ^ (i + 40 * s) ≤ b ^ 40 := calc
    _ = (q * 10 ^ i) * 10 ^ (40 * s) := by rw [pow_add, mul_assoc]
    _ ≤ A ^ 40 * 10 ^ (40 * s) := Nat.mul_le_mul_right _ hpowlo
    _ = (A * 10 ^ s) ^ 40 := (hmul A).symm
    _ ≤ b ^ 40 := Nat.pow_le_pow_left hlo 40
  have hu : b ^ 40 < (q + 1) * 10 ^ (i + 40 * s) := calc
    _ < ((A + 1) * 10 ^ s) ^ 40 := Nat.pow_lt_pow_left hhi (by decide)
    _ = (A + 1) ^ 40 * 10 ^ (40 * s) := hmul (A + 1)
    _ ≤ ((q + 1) * 10 ^ i) * 10 ^ (40 * s) := Nat.mul_le_mul_right _ hpowhi
    _ = _ := by rw [pow_add, mul_assoc]
  have hpos : 0 < 10 ^ (i + 40 * s) := by positivity
  have heq : b ^ 40 / 10 ^ (i + 40 * s) = q := by
    have hqlo := (Nat.le_div_iff_mul_le hpos).mpr hl
    have hqhi := (Nat.div_lt_iff_lt_mul hpos).mpr hu
    omega
  exact OMA.R_OeisA103662_conjecture_variants_a_40_R1.zero_mem_digits_of_div_mod_zero
    (heq.symm ▸ hq) (by rw [heq]; exact hzero)

/-- Bases of 2-adic valuation one after the prefix and suffix tests. -/
def H1 : Prop :=
  ∀ m : ℕ, 1 < m → ¬ (2 ∣ m) → ¬ (5 ∣ m) →
    let b := 2 * m
    (∀ d : ℕ, 2 ≤ d → d ≤ 40 → 10 ^ d ≤ b ^ 40 →
      let r := ((2 * (m % 5 ^ (d - 1))) ^ 40) % 10 ^ d
      10 ^ (d - 1) ≤ r ∧ 0 ∉ Nat.digits 10 r) →
    (∀ A s i q : ℕ, A * 10 ^ s ≤ b → b < (A + 1) * 10 ^ s →
      q * 10 ^ i ≤ A ^ 40 → (A + 1) ^ 40 ≤ (q + 1) * 10 ^ i → 0 < q → q % 10 ≠ 0) →
    0 ∈ Nat.digits 10 (b ^ 40)

/-- Bases of higher 2-adic valuation after the same tests at higher suffix precision. -/
def H2 : Prop :=
  ∀ k m : ℕ, 2 ≤ k → 1 < m → ¬ (2 ∣ m) → ¬ (5 ∣ m) →
    let b := 2 ^ k * m
    (∀ d : ℕ, 2 ≤ d → d ≤ 40 * k → 10 ^ d ≤ b ^ 40 →
      let r := ((2 ^ k * (m % 5 ^ (d - 1))) ^ 40) % 10 ^ d
      10 ^ (d - 1) ≤ r ∧ 0 ∉ Nat.digits 10 r) →
    (∀ A s i q : ℕ, A * 10 ^ s ≤ b → b < (A + 1) * 10 ^ s →
      q * 10 ^ i ≤ A ^ 40 → (A + 1) ^ 40 ≤ (q + 1) * 10 ^ i → 0 < q → q % 10 ≠ 0) →
    0 ∈ Nat.digits 10 (b ^ 40)

theorem main : H1 → H2 → OMA.R_OeisA103662_conjecture_variants_a_40_R1.H2 := by
  intro h1 h2 k m hk hm hm2 hm5
  by_contra hno
  have hsuffix := suffix_filter hno
  have hleading (A s i q : ℕ) (hlo : A * 10 ^ s ≤ 2 ^ k * m)
      (hhi : 2 ^ k * m < (A + 1) * 10 ^ s) (hpowlo : q * 10 ^ i ≤ A ^ 40)
      (hpowhi : (A + 1) ^ 40 ≤ (q + 1) * 10 ^ i) (hq : 0 < q) : q % 10 ≠ 0 :=
    fun hz => hno (zero_of_leading_interval hlo hhi hpowlo hpowhi hq hz)
  by_cases hk1 : k = 1
  · subst k
    apply hno
    simpa only [pow_one] using h1 m hm hm2 hm5
      (by simpa only [pow_one, mul_one] using hsuffix) (by simpa only [pow_one] using hleading)
  · exact hno (h2 k m (by omega) hm hm2 hm5 hsuffix hleading)

end OMA.R_OeisA103662_conjecture_variants_a_40_R1_H2_R1
