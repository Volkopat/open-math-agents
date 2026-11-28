import OMAReductions.R_oeis_a089305_R1

-- Reduction oeis-a089305.R1.H2.R1 of step oeis-a089305.R1.H2
-- Credit: @Progren

namespace OMA.R_oeis_a089305_R1_H2_R1

private theorem dvd_m2_of_order_three {n p : ℕ} (hp : p.Prime)
    (hord : orderOf (n : ZMod p) = 3) : p ∣ n * (n + 1) + 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have h3 : (n : ZMod p) ^ 3 = 1 := by
    rw [← hord, pow_orderOf_eq_one]
  have h1 : (n : ZMod p) ≠ 1 := by
    intro he
    rw [he, orderOf_one] at hord
    omega
  have hfac : ((n : ZMod p) - 1) * ((n : ZMod p) ^ 2 + n + 1) = 0 := by
    linear_combination h3
  have hzero : (n : ZMod p) ^ 2 + n + 1 = 0 :=
    (mul_eq_zero.1 hfac).resolve_left (sub_ne_zero.2 h1)
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  linear_combination hzero

-- Consecutive ascending-factorial+1 candidates are always pairwise coprime.
theorem no_common_factor_succ {n m r : ℕ} (hm : 0 < m) (hr : r.Prime)
    (h₁ : r ∣ n.ascFactorial m + 1) (h₂ : r ∣ n.ascFactorial (m + 1) + 1) : False := by
  let : Fact r.Prime := ⟨hr⟩
  have h1z : (n.ascFactorial m : ZMod r) = -1 := by
    have hz := (ZMod.natCast_eq_zero_iff _ _).2 h₁
    push_cast at hz
    exact eq_neg_of_add_eq_zero_left hz
  have h2z : ((n.ascFactorial (m + 1) : ℕ) : ZMod r) + 1 = 0 := by
    have hz := (ZMod.natCast_eq_zero_iff _ _).2 h₂
    simpa using hz
  rw [Nat.ascFactorial_succ, Nat.cast_mul, h1z] at h2z
  have hnm : ((n + (m - 1) : ℕ) : ZMod r) = 0 := by
    have hsub : n + m = n + (m - 1) + 1 := by omega
    rw [hsub] at h2z
    push_cast at h2z ⊢
    linear_combination -h2z
  have hd : r ∣ n + (m - 1) := (ZMod.natCast_eq_zero_iff _ _).1 hnm
  have hprod : n + (m - 1) ∣ n.ascFactorial m := by
    rw [Nat.ascFactorial_eq_prod_range]
    exact Finset.dvd_prod_of_mem (fun j => n + j) (Finset.mem_range.2 (by omega))
  exact hr.not_dvd_one ((Nat.dvd_add_iff_right (hd.trans hprod)).2 h₁)

-- Any prime divisor of n.ascFactorial m + 1 for m ≥ 5 is at least 7.
theorem prime_ge_seven_of_dvd_ascFactorial {n m r : ℕ} (hm : 5 ≤ m) (hr : r.Prime)
    (hd : r ∣ n.ascFactorial m + 1) : 7 ≤ r := by
  obtain ⟨ha, hend, _⟩ := (OMA.R_oeis_a089305_R1.dvd_iff_wilson_complement (by omega) hr).1 hd
  have h6 : 6 ≤ r := by omega
  have hne6 : r ≠ 6 := by
    intro h
    subst h
    exact absurd hr (by decide)
  omega

-- A prime of order 3 for n can divide n.ascFactorial 5 + 1 only if p ∈ {7, 37}.
theorem dvd_p5_of_order_three {n p : ℕ} (hp : p.Prime)
    (hord : orderOf (n : ZMod p) = 3) (hd : p ∣ n.ascFactorial 5 + 1) :
    p = 7 ∨ p = 37 := by
  let : Fact p.Prime := ⟨hp⟩
  have h2 : p ∣ n * (n + 1) + 1 := dvd_m2_of_order_three hp hord
  have ha := (ZMod.natCast_eq_zero_iff _ _).2 h2
  have hb := (ZMod.natCast_eq_zero_iff _ _).2 hd
  have hasc : n.ascFactorial 5 = n * (n + 1) * (n + 2) * (n + 3) * (n + 4) := by
    simp only [Nat.ascFactorial_succ, Nat.ascFactorial_zero]; ring
  rw [hasc] at hb
  push_cast at ha hb
  have hlin : (17 * (n : ZMod p) + 15) = 0 := by
    linear_combination -hb + ((n : ZMod p) ^ 3 + 9 * (n : ZMod p) ^ 2 + 25 * (n : ZMod p) + 16) * ha
  have h259 : (259 : ZMod p) = 0 := by
    linear_combination 289 * ha - (17 * (n : ZMod p) + 2) * hlin
  have hd259 : p ∣ 7 * 37 := (ZMod.natCast_eq_zero_iff 259 p).1 h259
  rcases hp.dvd_mul.1 hd259 with h7 | h37
  · left
    exact ((show Nat.Prime 7 by decide).eq_one_or_self_of_dvd p h7).resolve_left hp.ne_one
  · right
    exact ((show Nat.Prime 37 by decide).eq_one_or_self_of_dvd p h37).resolve_left hp.ne_one

private theorem binary_power {M : Type*} [Monoid M] (g : M) (k : ℕ) :
    npowBinRec k g = g ^ k := by
  induction k with
  | zero => rw [npowBinRec_zero, pow_zero]
  | succ k ih => rw [npowBinRec_succ, ih, pow_succ]

private theorem certified_prime (n m g : ℕ) (hn : 0 < n) (hm : 2 ≤ m)
    (cert :
      let u := n.ascFactorial m
      let a : ZMod (u + 1) := g
      npowBinRec u a = 1 ∧
        ∀ q : Fin (n + m), q.val.Prime → q.val ∣ u → npowBinRec (u / q.val) a ≠ 1) :
    (n.ascFactorial m + 1).Prime := by
  apply lucas_primality _ (g : ZMod (n.ascFactorial m + 1))
  · simpa only [Nat.add_sub_cancel, binary_power] using cert.1
  · intro q hq hd
    simp only [Nat.add_sub_cancel] at hd ⊢
    have hprod := hd
    rw [Nat.ascFactorial_eq_prod_range, hq.prime.dvd_finsetProd_iff] at hprod
    obtain ⟨i, hi, hiq⟩ := hprod
    have hlt := Finset.mem_range.1 hi
    have hle := Nat.le_of_dvd (show 0 < n + i by omega) hiq
    simpa only [binary_power] using cert.2 ⟨q, by omega⟩ hq hd

-- Lucas primality witnesses (m, g) for all n ∈ [101, 160] with n % 3 ≠ 1.
-- Entries with m = 2 or m = 3 refute the compositeness hypotheses of H2;
-- entries with m ≥ 5 directly produce a prime candidate.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem mid_starts {n p q : ℕ} (hlo : 100 < n) (hhi : n ≤ 160) (h3 : n % 3 ≠ 1)
    (hp : p.Prime) (hpn : p ≤ n) (hord : orderOf (n : ZMod p) = 3)
    (hq : q.Prime) (hqs : q ^ 2 ≤ n * (n + 1) * (n + 2) + 1)
    (hqd : q ∣ n * (n + 1) * (n + 2) + 1) :
    ∃ m : ℕ, 5 ≤ m ∧ (n.ascFactorial m + 1).Prime := by
  let witnesses : List (ℕ × ℕ) :=
    [(2, 3), (6, 29), (70, 191), (2, 2), (21, 53), (6, 13), (2, 2), (2, 13),
      (14, 37), (24, 74), (5, 11), (2, 5), (2, 19), (8, 37), (6, 19), (10, 17),
      (69, 283), (5, 22), (3, 17), (3, 15), (2, 7), (14, 43), (13, 79), (3, 33),
      (7, 53), (2, 3), (3, 22), (2, 3), (2, 5), (7, 38), (3, 11), (2, 5),
      (40, 67), (2, 3), (17, 58), (2, 2), (2, 17), (25, 62), (25, 109), (12, 29)]
  have checked : ∀ j : Fin 40,
      let t := 101 + 3 * (j.val / 2) + j.val % 2
      let w := witnesses[j.val]!
      let u := t.ascFactorial w.1
      let a : ZMod (u + 1) := w.2
      (w.1 = 2 ∨ w.1 = 3 ∨ 5 ≤ w.1) ∧ npowBinRec u a = 1 ∧
        ∀ r : Fin (t + w.1), r.val.Prime → r.val ∣ u → npowBinRec (u / r.val) a ≠ 1 := by
    dsimp only [witnesses]
    decide +kernel
  have hrem : (n - 101) % 3 < 2 := by omega
  let idx : ℕ := 2 * ((n - 101) / 3) + (n - 101) % 3
  have hidx : idx < 40 := by dsimp only [idx]; omega
  have hn_eq : 101 + 3 * (idx / 2) + idx % 2 = n := by dsimp only [idx]; omega
  have cert := checked ⟨idx, hidx⟩
  dsimp only at cert
  rw [hn_eq] at cert
  set w := witnesses[idx]!
  have hprime : (n.ascFactorial w.1 + 1).Prime := by
    apply certified_prime n w.1 w.2 (by omega)
    · rcases cert.1 with h | h | h <;> omega
    · exact cert.2
  rcases cert.1 with hm2 | hm3 | hm5
  · exfalso
    rw [hm2] at hprime
    have heq : n.ascFactorial 2 + 1 = n * (n + 1) + 1 := by
      simp only [Nat.ascFactorial_succ, Nat.ascFactorial_zero]; ring
    rw [heq] at hprime
    have hpd : p ∣ n * (n + 1) + 1 := dvd_m2_of_order_three hp hord
    rcases hprime.eq_one_or_self_of_dvd p hpd with h | h
    · exact hp.ne_one h
    · nlinarith
  · exfalso
    rw [hm3] at hprime
    have heq : n.ascFactorial 3 + 1 = n * (n + 1) * (n + 2) + 1 := by
      simp only [Nat.ascFactorial_succ, Nat.ascFactorial_zero]; ring
    rw [heq] at hprime
    rcases hprime.eq_one_or_self_of_dvd q hqd with h | h
    · exact hq.ne_one h
    · have := hq.two_le; nlinarith
  · exact ⟨w.1, hm5, hprime⟩

-- Remaining case n > 160, n ≡ 0 (mod 3), with lengths m = 5 and m = 6 eliminated
-- and two coprime prime divisors s, w ≥ 7 of P_5(n) and P_6(n).
def H1 : Prop :=
  ∀ n p q s w : ℕ, 160 < n → n % 3 = 0 →
    p.Prime → p ≤ n → p % 3 = 1 → orderOf (n : ZMod p) = 3 →
    q.Prime → p ≠ q → q ^ 2 ≤ n * (n + 1) * (n + 2) + 1 →
    q ∣ n * (n + 1) * (n + 2) + 1 →
    s.Prime → 7 ≤ s → s ^ 2 ≤ n.ascFactorial 5 + 1 → s ∣ n.ascFactorial 5 + 1 →
    w.Prime → 7 ≤ w → s ≠ w → w ^ 2 ≤ n.ascFactorial 6 + 1 → w ∣ n.ascFactorial 6 + 1 →
    ∃ m : ℕ, 7 ≤ m ∧ ∀ r : ℕ, r.Prime → r ^ 2 ≤ n.ascFactorial m + 1 →
      let a := n % r
      let t := r - (a + m)
      0 < a → a + m ≤ r → ((a - 1).factorial : ZMod r) * t.factorial * (-1) ^ t ≠ 1

-- Remaining case n > 160, n ≡ 2 (mod 3), with lengths m = 5 and m = 6 eliminated
-- and two coprime prime divisors s, w ≥ 7 of P_5(n) and P_6(n).
def H2 : Prop :=
  ∀ n p q s w : ℕ, 160 < n → n % 3 = 2 →
    p.Prime → p ≤ n → p % 3 = 1 → orderOf (n : ZMod p) = 3 →
    q.Prime → p ≠ q → q ^ 2 ≤ n * (n + 1) * (n + 2) + 1 →
    q ∣ n * (n + 1) * (n + 2) + 1 →
    s.Prime → 7 ≤ s → s ^ 2 ≤ n.ascFactorial 5 + 1 → s ∣ n.ascFactorial 5 + 1 →
    w.Prime → 7 ≤ w → s ≠ w → w ^ 2 ≤ n.ascFactorial 6 + 1 → w ∣ n.ascFactorial 6 + 1 →
    ∃ m : ℕ, 7 ≤ m ∧ ∀ r : ℕ, r.Prime → r ^ 2 ≤ n.ascFactorial m + 1 →
      let a := n % r
      let t := r - (a + m)
      0 < a → a + m ≤ r → ((a - 1).factorial : ZMod r) * t.factorial * (-1) ^ t ≠ 1

theorem main : H1 → H2 → OMA.R_oeis_a089305_R1.H2 := by
  intro h₁ h₂ n p q hn h3 hp hpn hp3 hord hq hpq hqs hqd
  by_cases hmid : n ≤ 160
  · obtain ⟨m, hm, hprime⟩ := mid_starts hn hmid h3 hp hpn hord hq hqs hqd
    exact ⟨m, hm, (OMA.R_oeis_a089305_R1.prime_iff_wilson_sieve (by omega) (by omega)).1 hprime⟩
  by_cases h5 : (n.ascFactorial 5 + 1).Prime
  · exact ⟨5, by omega, (OMA.R_oeis_a089305_R1.prime_iff_wilson_sieve (by omega) (by omega)).1 h5⟩
  by_cases h6 : (n.ascFactorial 6 + 1).Prime
  · exact ⟨6, by omega, (OMA.R_oeis_a089305_R1.prime_iff_wilson_sieve (by omega) (by omega)).1 h6⟩
  have hpos5 : 0 < n.ascFactorial 5 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact Nat.ascFactorial_pos k 5
  have hpos6 : 0 < n.ascFactorial 6 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact Nat.ascFactorial_pos k 6
  let s := (n.ascFactorial 5 + 1).minFac
  have hs : s.Prime := Nat.minFac_prime (by omega)
  have hsd : s ∣ n.ascFactorial 5 + 1 := Nat.minFac_dvd _
  have hss : s ^ 2 ≤ n.ascFactorial 5 + 1 := Nat.minFac_sq_le_self (by positivity) h5
  have hs7 : 7 ≤ s := prime_ge_seven_of_dvd_ascFactorial (by omega) hs hsd
  let w := (n.ascFactorial 6 + 1).minFac
  have hw : w.Prime := Nat.minFac_prime (by omega)
  have hwd : w ∣ n.ascFactorial 6 + 1 := Nat.minFac_dvd _
  have hws : w ^ 2 ≤ n.ascFactorial 6 + 1 := Nat.minFac_sq_le_self (by positivity) h6
  have hw7 : 7 ≤ w := prime_ge_seven_of_dvd_ascFactorial (by omega) hw hwd
  have hsw : s ≠ w := fun h => no_common_factor_succ (by omega) hs hsd (h ▸ hwd)
  have hcases : n % 3 = 0 ∨ n % 3 = 2 := by omega
  rcases hcases with h30 | h32
  · obtain ⟨m, hm, hres⟩ :=
      h₁ n p q s w (by omega) h30 hp hpn hp3 hord hq hpq hqs hqd hs hs7 hss hsd hw hw7 hsw hws hwd
    exact ⟨m, by omega, hres⟩
  · obtain ⟨m, hm, hres⟩ :=
      h₂ n p q s w (by omega) h32 hp hpn hp3 hord hq hpq hqs hqd hs hs7 hss hsd hw hw7 hsw hws hwd
    exact ⟨m, by omega, hres⟩

end OMA.R_oeis_a089305_R1_H2_R1
