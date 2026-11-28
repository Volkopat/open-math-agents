import OMAReductions.R_mse_3587363_R1

-- Reduction mse-3587363.R1.H2.R1 of step mse-3587363.R1.H2
-- Credit: @lettucrisp

namespace OMA.R_mse_3587363_R1_H2_R1

private theorem extend_factor (d x n : ℕ) (hx : 0 < x) (hxn : x ≤ n)
    (hd : d ∣ (x - 1).factorial) : d * x ∣ n.factorial := by
  have h : d * x ∣ x.factorial := by
    conv_rhs => rw [← Nat.sub_add_cancel (show 1 ≤ x by omega), Nat.factorial_succ]
    simpa [Nat.sub_add_cancel (show 1 ≤ x by omega), Nat.mul_comm] using
      Nat.mul_dvd_mul_left x hd
  exact h.trans (Nat.factorial_dvd_factorial hxn)

private theorem pair_dvd (r s n : ℕ) (hr : 0 < r) (hrs : r < s) (hs : s ≤ n) :
    r*s ∣ n.factorial :=
  extend_factor r s n (by omega) hs (Nat.dvd_factorial hr (by omega))

theorem square_dvd_of_composite {k n : ℕ} (hk : 4 < k) (hkn : k ≤ n)
    (hc : ¬ k.Prime) : k ^ 2 ∣ n.factorial := by
  obtain ⟨r, ⟨s, heq⟩, hr, hrk⟩ := Nat.exists_dvd_of_not_prime2 (by omega : 1 < k) hc
  have hs : 1 < s := by
    by_contra! h
    interval_cases s <;> simp_all
  have hsk : s < k := by nlinarith
  have hd : k ∣ (k-1).factorial := by
    rcases lt_trichotomy r s with h | h | h
    · rw [heq]
      exact pair_dvd r s _ (by omega) h (by omega)
    · subst s
      have hr3 : 3 ≤ r := by nlinarith
      have htwo : 2*r < k := by nlinarith
      have hpair := pair_dvd r (2*r) (k-1) (by omega) (by omega) (by omega)
      apply dvd_trans _ hpair
      exact ⟨2, by nlinarith⟩
    · rw [heq, Nat.mul_comm r s]
      exact pair_dvd s r _ (by omega) h (by rw [Nat.mul_comm s r]; omega)
  simpa [pow_two] using extend_factor k k n (by omega) hkn hd

theorem powers_of_square_dvd {n k a b : ℕ} (hk : 0 < k)
    (hd : k ^ 2 ∣ n.factorial) (he : n.factorial + k = a ^ b) :
    ∃ c d : ℕ, k = c ^ b ∧ n.factorial / k + 1 = d ^ b := by
  obtain ⟨t, ht⟩ := hd
  have he' : k * (k*t + 1) = a^b := by rw [← he, ht]; ring
  have hcop : k.Coprime (k*t + 1) := by simp
  have left := exists_eq_pow_of_mul_eq_pow (a := k) (b := k*t+1)
    (by rw [show gcd k (k*t+1) = 1 from hcop.gcd_eq_one]; exact isUnit_one) he'
  obtain ⟨c, hc⟩ := left
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (a := k*t+1) (b := k)
    (by rw [show gcd (k*t+1) k = 1 from hcop.symm.gcd_eq_one]; exact isUnit_one) (mul_comm k _ ▸ he')
  refine ⟨c,d,hc,?_⟩
  rwa [ht, pow_two, Nat.mul_assoc, Nat.mul_div_cancel_left _ hk]


private theorem square_dvd_power {p a b : ℕ} (hp : p.Prime)
    (hb : 2 ≤ b) (h : p ∣ a ^ b) : p ^ 2 ∣ a ^ b :=
  (pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow h) 2).trans (pow_dvd_pow a hb)

/-- For a prime offset p and n=p+j, Wilson forces j! = 1 modulo p. -/
theorem prime_offset {p j a b : ℕ} (hp : p.Prime) (hb : 2 ≤ b)
    (he : (p+j).factorial + p = a^b) : (j.factorial : ZMod p) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let q := (p-1).factorial * (p+1).ascFactorial j
  have hfac : (p+j).factorial = p*q := by
    rw [← Nat.factorial_mul_ascFactorial]
    have hstep : p.factorial = p*(p-1).factorial := by
      simpa [Nat.sub_add_cancel hp.one_le] using Nat.factorial_succ (p-1)
    rw [hstep, mul_assoc]
  have he' : p*(q+1) = a^b := by rw [← he, hfac]; ring
  have hd : p ^ 2 ∣ p*(q+1) := by
    rw [he']
    exact square_dvd_power hp hb (he' ▸ dvd_mul_right p (q+1))
  obtain ⟨t, ht⟩ := hd
  have hqt : q+1 = p*t := Nat.eq_of_mul_eq_mul_left hp.pos (by rw [ht]; ring)
  have hz : ((q+1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 ⟨t, hqt⟩
  have hasc (i : ℕ) : ((p+1).ascFactorial i : ZMod p) = (i.factorial : ZMod p) := by
    induction i with
    | zero => simp
    | succ i ih => simp [Nat.ascFactorial_succ, Nat.factorial_succ, ih, add_comm]
  simp only [q, Nat.cast_add, Nat.cast_one, Nat.cast_mul, ZMod.wilsons_lemma, hasc,
    neg_one_mul] at hz
  linear_combination -hz

/-- Every counterexample has a prime offset, or two coprime factors that
are both powers with the original exponent. -/
theorem counterexample_cases {n k a b : ℕ} (hk : 3 < k) (hkn : k < n)
    (hb : 2 ≤ b) (he : n.factorial + k = a^b) :
    (k.Prime ∧ n < 2*k ∧ ((n-k).factorial : ZMod k) = 1) ∨
    (¬ k.Prime ∧ ∃ c d : ℕ, k = c^b ∧ n.factorial / k + 1 = d^b) := by
  by_cases hp : k.Prime
  · left
    have hsum : k + (n-k) = n := by omega
    refine ⟨hp, ?_, prime_offset hp hb (by rwa [hsum])⟩
    by_contra! hn
    have hd : k^2 ∣ n.factorial := by
      apply dvd_trans _ (pair_dvd k (2*k) n hp.pos (by omega) hn)
      exact ⟨2, by ring⟩
    have hpow := square_dvd_power hp hb (he ▸ dvd_add (Nat.dvd_factorial hp.pos hkn.le) (dvd_refl k))
    rw [← he] at hpow
    have hbad := (Nat.dvd_add_right hd).mp hpow
    have := Nat.le_of_dvd hp.pos hbad
    nlinarith [hp.two_le]
  · right
    refine ⟨hp, powers_of_square_dvd (by omega) ?_ he⟩
    by_cases hk4 : k = 4
    · subst k
      by_cases hn : 6 ≤ n
      · exact dvd_trans (by decide : 4^2 ∣ Nat.factorial 6) (Nat.factorial_dvd_factorial hn)
      · have : n = 5 := by omega
        subst n
        have h124 : 124 = a^b := by simpa [Nat.factorial] using he
        have hd := square_dvd_power (by decide : Nat.Prime 31) hb
          (h124 ▸ (by decide : 31 ∣ 124))
        rw [← h124] at hd
        exact False.elim ((by decide : ¬ 31^2 ∣ 124) hd)
    · exact square_dvd_of_composite (by omega) hkn.le hp

/-- At prime offset p, Wilson's theorem restricts the excess j to j! ≡ 1 mod p. -/
def H1 : Prop :=
  ∀ p j a b : ℕ, p.Prime → 3 < p → 0 < j → j < p →
    (j.factorial : ZMod p) = 1 → 2 ≤ b → (p+j).factorial + p ≠ a^b

/-- At composite offset, the offset and the base must have the forms c^b and c*d. -/
def H2 : Prop :=
  ∀ n c d b : ℕ, 2 ≤ b → 3 < c^b → c^b < n →
    n.factorial + c^b ≠ (c*d)^b

theorem main : H1 → H2 → OMA.R_mse_3587363_R1.H2 := by
  intro prime_case power_case n k a b hk hb he hkn _
  rcases counterexample_cases hk hkn hb he with ⟨hp, hn, hj⟩ | ⟨_, c, d, hc, hd⟩
  · apply prime_case k (n-k) a b hp hk (by omega) (by omega) hj hb
    rwa [show k + (n-k) = n by omega]
  · have hdvd := Nat.dvd_factorial (show 0 < k by omega) hkn.le
    apply power_case n c d b hb (hc ▸ hk) (hc ▸ hkn)
    rw [mul_pow, ← hc, ← hd, Nat.mul_add, Nat.mul_div_cancel' hdvd, Nat.mul_one]

end OMA.R_mse_3587363_R1_H2_R1
