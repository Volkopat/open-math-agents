import FormalConjectures.OEIS.«238585»

/-! A cube-root sieve and a large-prime-factor criterion for the shifted prime product. -/

-- Credit: @Pixelstorm44
namespace OMA.R_OeisA238585_conjecture_4_R1

open scoped Classical

/-- At least one shift survives removal of all primes through the cube root of 2q.
Such a survivor has at most two prime factors counted with multiplicity. The
four-prime sieve below already handles the range 2q < 11^3. -/
def H1 : Prop := ∀ n : ℕ, 3 < n →
  let q := Nat.nth Nat.Prime (n - 1)
  let s := fun p : ℕ => Nat.nth Nat.Prime (p - 1) + q + 1
  11 ^ 3 ≤ 2 * q → ∃ p < n, p.Prime ∧ ∀ d : ℕ, d.Prime → d ∣ s p → 2 * q < d ^ 3

/-- Whenever the sifted product is nonempty, it has a prime divisor above
(2q)^(2/3). Products of two surviving prime factors cannot supply this divisor. -/
def H2 : Prop := ∀ n : ℕ, 3 < n →
  let q := Nat.nth Nat.Prime (n - 1)
  let s := fun p : ℕ => Nat.nth Nat.Prime (p - 1) + q + 1
  let A := (Finset.range n).filter fun p => p.Prime ∧
    ∀ d : ℕ, d.Prime → d ∣ s p → 2 * q < d ^ 3
  A.Nonempty → ∃ r : ℕ, r.Prime ∧ (2 * q) ^ 2 < r ^ 3 ∧ r ∣ ∏ p ∈ A, s p

set_option maxRecDepth 4096 in
/-- Of the three shifts coming from prime indices 3, 5 and 7, one always
survives sieving by 2, 3, 5 and 7. -/
theorem fixed_wheel {q : ℕ} (hq : q.Prime) (hbig : 7 < q) :
    (q+6).Coprime 210 ∨ (q+12).Coprime 210 ∨ (q+18).Coprime 210 := by
  have h6 := hq.coprime_iff_not_dvd.mpr (show ¬ q ∣ 6 by
    intro hd
    have := Nat.le_of_dvd (by decide : 0 < 6) hd
    omega)
  have small : ∀ a : Fin 210, a.val.Coprime 6 →
      (a.val+6).Coprime 210 ∨ (a.val+12).Coprime 210 ∨ (a.val+18).Coprime 210 := by
    decide
  let a : Fin 210 := ⟨q % 210, Nat.mod_lt _ (by decide)⟩
  have ha : a.val + 210 * (q / 210) = q := Nat.mod_add_div _ _
  have h6' : a.val.Coprime 6 := by
    apply (Nat.coprime_add_mul_left_left a.val 6 (35 * (q / 210))).mp
    convert h6 using 1
    omega
  have lift (k : ℕ) (hk : (a.val+k).Coprime 210) : (q+k).Coprime 210 := by
    have he : a.val + k + 210 * (q / 210) = q + k := by omega
    exact he ▸ (Nat.coprime_add_mul_left_left (a.val+k) 210 _).mpr hk
  exact (small a h6').imp (lift 6) (Or.imp (lift 12) (lift 18))

/-- The cube-root sieve has a survivor whenever 2q is below 11^3. -/
theorem early_survivor {n : ℕ} (hn : 3 < n)
    (hcut : 2 * Nat.nth Nat.Prime (n - 1) < 11 ^ 3) :
    ∃ p < n, p.Prime ∧ ∀ d : ℕ, d.Prime →
      d ∣ Nat.nth Nat.Prime (p - 1) + Nat.nth Nat.Prime (n - 1) + 1 →
      2 * Nat.nth Nat.Prime (n - 1) < d ^ 3 := by
  let q := Nat.nth Nat.Prime (n-1)
  have rough {x : ℕ} (hx : x.Coprime 210) {d : ℕ} (hd : d.Prime) (hdx : d ∣ x) :
      2*q < d^3 := by
    by_cases h : 11 ≤ d
    · exact hcut.trans_le (Nat.pow_le_pow_left h 3)
    · have hd210 : d ∣ 210 := by interval_cases d <;> first | decide | contradiction
      have := Nat.eq_one_of_dvd_coprimes hx hdx hd210
      exact (hd.ne_one this).elim
  by_cases hbig : 7 < n
  · have hqbig : 7 < q := by
      rw [← Nat.nth_prime_three_eq_seven]
      exact Nat.nth_strictMono Nat.infinite_setOfPred_prime (show 3 < n-1 by omega)
    change ∃ p < n, p.Prime ∧ ∀ d : ℕ, d.Prime →
      d ∣ Nat.nth Nat.Prime (p - 1) + q + 1 → 2*q < d^3
    rcases fixed_wheel (Nat.prime_nth_prime _) hqbig with h | h | h
    · refine ⟨3, by omega, by decide, ?_⟩
      simpa only [Nat.reduceSub, Nat.nth_prime_two_eq_five, Nat.add_comm 5 q, Nat.add_assoc,
        Nat.reduceAdd] using fun d hd hdx => @rough (q+6) h d hd hdx
    · refine ⟨5, by omega, by decide, ?_⟩
      simpa only [Nat.reduceSub, Nat.nth_prime_four_eq_eleven, Nat.add_comm 11 q, Nat.add_assoc,
        Nat.reduceAdd] using fun d hd hdx => @rough (q+12) h d hd hdx
    · refine ⟨7, by omega, by decide, ?_⟩
      simpa only [Nat.reduceSub, Nat.nth_prime_six_eq_seventeen, Nat.add_comm 17 q, Nat.add_assoc,
        Nat.reduceAdd] using fun d hd hdx => @rough (q+18) h d hd hdx
  · have cert {q s : ℕ} (hp : s.Prime) (hb : 2*q < s^3) (d : ℕ) (hd : d.Prime)
        (hds : d ∣ s) : 2*q < d^3 := by
      rcases (Nat.dvd_prime hp).mp hds with he | he
      · exact (hd.ne_one he).elim
      · exact he.symm ▸ hb
    interval_cases n
    · refine ⟨2, by decide, by decide, ?_⟩
      simpa only [Nat.reduceSub, Nat.nth_prime_one_eq_three, Nat.nth_prime_three_eq_seven,
        Nat.reduceAdd] using cert (q := 7) (s := 11) (by decide) (by decide)
    · refine ⟨3, by decide, by decide, ?_⟩
      simpa only [Nat.reduceSub, Nat.nth_prime_two_eq_five, Nat.nth_prime_four_eq_eleven,
        Nat.reduceAdd] using cert (q := 11) (s := 17) (by decide) (by decide)
    · refine ⟨2, by decide, by decide, ?_⟩
      simpa only [Nat.reduceSub, Nat.nth_prime_one_eq_three, Nat.nth_prime_five_eq_thirteen,
        Nat.reduceAdd] using cert (q := 13) (s := 17) (by decide) (by decide)
    · refine ⟨3, by decide, by decide, ?_⟩
      simpa only [Nat.reduceSub, Nat.nth_prime_two_eq_five, Nat.nth_prime_six_eq_seventeen,
        Nat.reduceAdd] using cert (q := 17) (s := 23) (by decide) (by decide)

private theorem shift_upper {n p : ℕ} (hp : p.Prime) (hlt : p < n) :
    Nat.nth Nat.Prime (p - 1) + Nat.nth Nat.Prime (n - 1) + 1 ≤
    2 * Nat.nth Nat.Prime (n - 1) := by
  have hp2 := hp.two_le
  have he := Nat.nth_strictMono Nat.infinite_setOfPred_prime (show p - 1 < n - 1 by omega)
  change Nat.nth Nat.Prime (p - 1) < Nat.nth Nat.Prime (n - 1) at he
  omega

private theorem large_factor {x M r : ℕ} (hx : 0 < x) (hu : x ≤ M)
    (hrough : ∀ d : ℕ, d.Prime → d ∣ x → M < d ^ 3)
    (hr : r.Prime) (hsize : M ^ 2 < r ^ 3) (hdvd : r ∣ x) : x.Prime := by
  obtain ⟨k, hk⟩ := hdvd
  have hk1 : k = 1 := by
    by_contra hne
    obtain ⟨d, hd, hdk⟩ := Nat.exists_prime_and_dvd hne
    have hkm : k ∣ x := hk ▸ dvd_mul_left k r
    have hsmall := hrough d hd (hdk.trans hkm)
    have hkpos : 0 < k := by
      by_contra! hz
      simp [Nat.eq_zero_of_le_zero hz] at hk
      omega
    have hdk' := Nat.le_of_dvd hkpos hdk
    have hle : r * d ≤ M := (Nat.mul_le_mul_left r hdk').trans (hk ▸ hu)
    have hbad := Nat.mul_lt_mul_of_lt_of_lt hsize hsmall
    rw [← mul_pow] at hbad
    have hpow := Nat.pow_le_pow_left hle 3
    nlinarith only [hpow, hbad]
  simpa [hk, hk1] using hr

theorem main : H1 → H2 → type_of% @OeisA238585.conjecture_4 := by
  intro h₁ h₂ n hn
  have hex : ∃ i < n, i.Prime ∧ ∀ d : ℕ, d.Prime →
      d ∣ Nat.nth Nat.Prime (i - 1) + Nat.nth Nat.Prime (n - 1) + 1 →
      2 * Nat.nth Nat.Prime (n - 1) < d ^ 3 := by
    by_cases hc : 11 ^ 3 ≤ 2 * Nat.nth Nat.Prime (n - 1)
    · exact h₁ n hn hc
    · exact early_survivor hn (Nat.lt_of_not_ge hc)
  obtain ⟨i, hi, hip, hs⟩ := hex
  obtain ⟨r, hr, hsize, hprod⟩ := h₂ n hn ⟨i,
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hip, hs⟩⟩
  obtain ⟨p, hmem, hdvd⟩ := (hr.prime.dvd_finsetProd_iff _).mp hprod
  obtain ⟨hpn, hp, hrough⟩ := Finset.mem_filter.mp hmem
  have hlt := Finset.mem_range.mp hpn
  exact ⟨p, hlt, hp, large_factor (by positivity) (shift_upper hp hlt) hrough hr hsize hdvd⟩

/-- A prime witness meets both strict sieve thresholds. -/
theorem converse (h : type_of% @OeisA238585.conjecture_4) : H1 ∧ H2 := by
  have bounds {x q : ℕ} (hq : 2 ≤ q) (hx : q < x) (hx4 : 4 ≤ x) :
      2 * q < x ^ 3 ∧ (2 * q) ^ 2 < x ^ 3 := by
    have hsquare : q ^ 2 < x ^ 2 := by gcongr
    have hstrong : (2 * q) ^ 2 < x ^ 3 := by
      nlinarith only [hsquare, Nat.mul_le_mul_right (x ^ 2) hx4]
    exact ⟨by nlinarith only [hstrong, hq], hstrong⟩
  constructor <;> intro n hn
  all_goals
    obtain ⟨p, hlt, hp, hprime⟩ := h n hn
    let q := Nat.nth Nat.Prime (n - 1)
    let x := Nat.nth Nat.Prime (p - 1) + q + 1
    change x.Prime at hprime
    have hq : 2 ≤ q := (Nat.prime_nth_prime _).two_le
    have hs : 2 ≤ Nat.nth Nat.Prime (p - 1) := (Nat.prime_nth_prime _).two_le
    obtain ⟨hsmall, hlarge⟩ := bounds (x := x) hq (by dsimp [x]; omega) (by dsimp [x]; omega)
    have hrough (d : ℕ) (hd : d.Prime) (hdvd : d ∣ x) : 2 * q < d ^ 3 := by
      rcases (Nat.dvd_prime hprime).mp hdvd with he | he
      · exact (hd.ne_one he).elim
      · exact he.symm ▸ hsmall
  · dsimp only
    intro _
    exact ⟨p, hlt, hp, hrough⟩
  · dsimp only
    intro _
    exact ⟨x, hprime, hlarge, Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hlt, hp, hrough⟩)⟩

end OMA.R_OeisA238585_conjecture_4_R1
