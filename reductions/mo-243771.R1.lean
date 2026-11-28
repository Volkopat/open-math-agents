import OMAStatements.S_mo_243771

/-!
Wilson's theorem proves the assertion modulo `p²` with `q = p` and `m = 2p - 1`.
Modulo `p`, the Wilson product pairs factorial indices `k` and `p - 1 - k`.
For `p ≡ 3 (mod 4)` the midpoint factorial is a sign, so it cannot contribute a prime.
-/

open scoped Nat

namespace OMA.R_mo_243771_R1

/-- Compare the shifted factorial with the prime modulo its square. -/
private lemma factorial_prime_sq_iff (p r : ℕ) (hp : p.Prime) :
    (p + r).factorial ≡ p [MOD p ^ 2] ↔ (r.factorial : ZMod p) = -1 := by
  let : Fact p.Prime := ⟨hp⟩
  let block := (p + 1).ascFactorial r
  have hblock : block ≡ r.factorial [MOD p] := by
    dsimp only [block]
    rw [Nat.ascFactorial_eq_prod_range, ← Finset.prod_range_add_one_eq_factorial]
    apply Nat.ModEq.prod
    intro i _
    simp [Nat.ModEq, Nat.add_mod, Nat.add_comm]
  have hsplit : (p + r).factorial = p * ((p - 1).factorial * block) := by
    rw [← Nat.mul_assoc, Nat.mul_factorial_pred hp.ne_zero]
    exact (Nat.factorial_mul_ascFactorial p r).symm
  calc
    _ ↔ (p - 1).factorial * block ≡ 1 [MOD p] := by
      simpa only [Nat.mul_one, ← pow_two, ← hsplit] using
        (Nat.ModEq.mul_left_cancel_iff' (a := (p - 1).factorial * block)
          (b := 1) (m := p) hp.ne_zero)
    _ ↔ _ := by
      rw [← ZMod.natCast_eq_natCast_iff] at hblock ⊢
      rw [Nat.cast_mul, hblock, ZMod.wilsons_lemma, neg_one_mul, Nat.cast_one, neg_eq_iff_eq_neg]

private lemma prime_sq_factorial_witness :
    ∀ p : ℕ, p.Prime → ∃ q m : ℕ, q.Prime ∧ q < p ^ 2 ∧ 2 < m ∧ m < p ^ 2 ∧
      q ≡ m.factorial [MOD p ^ 2] := by
  intro p hp
  have hp2 := hp.two_le
  refine ⟨p, 2 * p - 1, hp, by nlinarith, by omega, ?_, ?_⟩
  · rw [pow_two]
    exact (Nat.sub_lt (by omega) Nat.one_pos).trans_le (Nat.mul_le_mul_right p hp2)
  · rw [show 2 * p - 1 = p + (p - 1) by omega]
    let : Fact p.Prime := ⟨hp⟩
    exact ((factorial_prime_sq_iff p (p - 1) hp).mpr (ZMod.wilsons_lemma p)).symm

/-- Reflect a factorial index around the midpoint of the Wilson product. -/
private lemma factorial_reflection (p k : ℕ) (hp : p.Prime) (hk : k ≤ p - 1) :
    ((p - 1 - k).factorial : ZMod p) * (k.factorial : ZMod p) = (-1) ^ (k + 1) := by
  let : Fact p.Prime := ⟨hp⟩
  have h := congrArg (fun a : ℕ => (a : ZMod p))
    (Nat.factorial_mul_descFactorial hk)
  push_cast at h
  rw [ZMod.cast_descFactorial (hk.trans (Nat.sub_le _ _)), ZMod.wilsons_lemma] at h
  have hsign : (-1 : ZMod p) ^ k * (-1) ^ k = 1 := by
    rw [← mul_pow]
    simp
  calc
    _ = (((-1 : ZMod p) ^ k) * (-1) ^ k) *
        (((p - 1 - k).factorial : ZMod p) * (k.factorial : ZMod p)) := by rw [hsign, one_mul]
    _ = (-1 : ZMod p) ^ k * (((p - 1 - k).factorial : ZMod p) *
        ((-1 : ZMod p) ^ k * (k.factorial : ZMod p))) := by ring
    _ = _ := by rw [h, pow_succ]

private lemma prime_cast_ne_signs {p q : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hq : q.Prime) (hqp : q < p) : (q : ZMod p) ≠ 1 ∧ (q : ZMod p) ≠ -1 := by
  have hq2 := hq.two_le
  constructor
  · intro h
    have he := (ZMod.natCast_eq_natCast_iff q 1 p).mp (by simpa using h)
    simp only [Nat.ModEq, Nat.mod_eq_of_lt hqp, Nat.mod_eq_of_lt (by omega : 1 < p)] at he
    omega
  · intro h
    have hz : ((q + 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_add, Nat.cast_one, h, neg_add_cancel]
    have hle := Nat.le_of_dvd (by omega : 0 < q + 1) ((ZMod.natCast_eq_zero_iff _ _).mp hz)
    obtain ⟨a, ha⟩ := hp.odd_of_ne_two (by omega)
    obtain ⟨b, hb⟩ := hq.odd_of_ne_two (by omega)
    omega

private lemma two_le_reflected_index {p q k : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hq : q.Prime) (hqp : q < p)
    (h : (q : ZMod p) * (k.factorial : ZMod p) = (-1) ^ (k + 1)) : 2 ≤ k := by
  by_contra! hk
  obtain hk0 | hk1 : k = 0 ∨ k = 1 := by omega
  · exact (prime_cast_ne_signs hp hp5 hq hqp).2 (by simpa [hk0] using h)
  · exact (prime_cast_ne_signs hp hp5 hq hqp).1 (by simpa [hk1] using h)

private lemma index_lt_midpoint {p q k : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hp3 : p % 4 = 3)
    (hq : q.Prime) (hqp : q < p) (hk : k ≤ (p - 1) / 2)
    (h : (2 < k ∧ q ≡ k.factorial [MOD p]) ∨
      (q : ZMod p) * (k.factorial : ZMod p) = (-1) ^ (k + 1)) : k < (p - 1) / 2 := by
  let : Fact p.Prime := ⟨hp⟩
  by_contra! hnk
  have hflip := factorial_reflection p k hp (by omega)
  rw [show p - 1 - k = k by omega] at hflip
  have hsign : (-1 : ZMod p) ^ (k + 1) = 1 := by
    rw [show k + 1 = 2 * ((p + 1) / 4) by omega, pow_mul]
    simp
  have hsq : (k.factorial : ZMod p) ^ 2 = 1 := by
    rw [pow_two]
    exact hflip.trans hsign
  have hfac : (k.factorial : ZMod p) ≠ 0 := by
    intro hz
    simp [hz] at hsq
  have he : (q : ZMod p) = (k.factorial : ZMod p) := by
    rcases h with ⟨_, hm⟩ | hr
    · exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
    · exact mul_right_cancel₀ hfac (hr.trans hflip.symm)
  have hqsq : (q : ZMod p) ^ 2 = 1 := by rw [he]; exact hsq
  have hne := prime_cast_ne_signs hp hp5 hq hqp
  exact (sq_eq_one_iff.mp hqsq).elim hne.1 hne.2

private lemma prime_factorial_short_iff (p : ℕ) (hp : p.Prime) (hp5 : 5 < p) :
    (∃ q m : ℕ, q.Prime ∧ q < p ∧ 2 < m ∧ m < p ∧ q ≡ m.factorial [MOD p]) ↔
      ∃ q k : ℕ, q.Prime ∧ q < p ∧ 2 ≤ k ∧ k ≤ (p - 1) / 2 ∧
        ((2 < k ∧ q ≡ k.factorial [MOD p]) ∨
          (q : ZMod p) * (k.factorial : ZMod p) = (-1) ^ (k + 1)) := by
  let : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨q, m, hq, hqp, hm2, hmp, hm⟩
    by_cases hk : m ≤ (p - 1) / 2
    · exact ⟨q, m, hq, hqp, by omega, hk, Or.inl ⟨hm2, hm⟩⟩
    · have hr := factorial_reflection p (p - 1 - m) hp (by omega)
      rw [show p - 1 - (p - 1 - m) = m by omega,
        ← (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm] at hr
      exact ⟨q, p - 1 - m, hq, hqp, two_le_reflected_index hp hp5 hq hqp hr,
        by omega, Or.inr hr⟩
  · rintro ⟨q, k, hq, hqp, _, hk, hdirect | hreflected⟩
    · exact ⟨q, k, hq, hqp, hdirect.1, by omega, hdirect.2⟩
    · refine ⟨q, p - 1 - k, hq, hqp, by omega, by omega,
        (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_⟩
      have hfac : (k.factorial : ZMod p) ≠ 0 := by
        intro h
        have hle : p ≤ k := hp.dvd_factorial.mp ((ZMod.natCast_eq_zero_iff _ _).mp h)
        omega
      exact mul_right_cancel₀ hfac (hreflected.trans (factorial_reflection p k hp (by omega)).symm)

/-- Prime factorial residues for primes congruent to 1 modulo 4, using the first half. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → 5 < p → p % 4 = 1 →
    ∃ q k : ℕ, q.Prime ∧ q < p ∧ 2 ≤ k ∧ k ≤ (p - 1) / 2 ∧
      ((2 < k ∧ q ≡ k.factorial [MOD p]) ∨
        (q : ZMod p) * (k.factorial : ZMod p) = (-1) ^ (k + 1))

/-- Prime factorial residues for primes congruent to 3 modulo 4, below the midpoint. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 5 < p → p % 4 = 3 →
    ∃ q k : ℕ, q.Prime ∧ q < p ∧ 2 ≤ k ∧ k < (p - 1) / 2 ∧
      ((2 < k ∧ q ≡ k.factorial [MOD p]) ∨
        (q : ZMod p) * (k.factorial : ZMod p) = (-1) ^ (k + 1))

/-- The two residue classes give an exact reformulation of the modulo-`p` part. -/
lemma modulo_prime_iff :
    H1 ∧ H2 ↔ ∀ p : ℕ, p.Prime → 5 < p → ∃ q m : ℕ,
      q.Prime ∧ q < p ∧ 2 < m ∧ m < p ∧ q ≡ m.factorial [MOD p] := by
  constructor
  · rintro ⟨h1, h2⟩ p hp hp5
    obtain ⟨a, ha⟩ := hp.odd_of_ne_two (by omega)
    apply (prime_factorial_short_iff p hp hp5).mpr
    obtain hp1 | hp3 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    · exact h1 p hp hp5 hp1
    · obtain ⟨q, k, hq, hqp, hk2, hk, h⟩ := h2 p hp hp5 hp3
      exact ⟨q, k, hq, hqp, hk2, hk.le, h⟩
  · intro h
    refine ⟨fun p hp hp5 _ => (prime_factorial_short_iff p hp hp5).mp (h p hp hp5), ?_⟩
    intro p hp hp5 hp3
    obtain ⟨q, k, hq, hqp, hk2, hk, hm⟩ :=
      (prime_factorial_short_iff p hp hp5).mp (h p hp hp5)
    exact ⟨q, k, hq, hqp, hk2, index_lt_midpoint hp hp5 hp3 hq hqp hk hm, hm⟩

theorem main : H1 → H2 → type_of% @OMA.S_mo_243771.main := by
  intro h1 h2
  exact ⟨modulo_prime_iff.mp ⟨h1, h2⟩, prime_sq_factorial_witness⟩

end OMA.R_mo_243771_R1
