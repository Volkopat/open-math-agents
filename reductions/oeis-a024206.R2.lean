import OMAStatements.S_oeis_a024206

-- Reduction oeis-a024206.R2 of OEIS A024206
-- Credit: @Pixelstorm44

namespace OMA.R_oeis_a024206_R2

open OMA.S_oeis_a024206

/-- A square root of the discriminant cannot be a proper power, even of a composite base. -/
def H1 : Prop := ∀ p b k : ℕ, p.Prime → 2 ≤ b → 2 ≤ k →
  (b ^ k) ^ 2 ≠ 4 * primorial p + 1

/-- The remaining obstruction: two distinct primes above p dividing the sum of
consecutive complementary divisors of p#. -/
def H2 : Prop := ∀ p d r s : ℕ, p.Prime → d * (d + 1) = primorial p →
  r.Prime → s.Prime → p < r → p < s → r ∣ 2 * d + 1 → s ∣ 2 * d + 1 → r = s

section

private theorem two_mod_four {p : ℕ} (hp : p.Prime) : primorial p % 4 = 2 := by
  have h := Nat.prime_two.dvd_primorial_iff.mpr hp.two_le
  have hn := Nat.squarefree_iff_prime_squarefree.mp (squarefree_primorial p) 2 Nat.prime_two
  change ¬4 ∣ primorial p at hn
  omega

/-- Raising to the characteristic lifts a residue of one to one modulo its square. -/
private theorem lift_one {l : ℕ} (hl : l.Prime) (x : ℤ) (h : (l : ℤ) ∣ x^l - 1) :
    (l : ℤ)^2 ∣ x^l - 1 := by
  have hf := (Int.ModEq.pow_prime_eq_self hl x).dvd
  have hx : (l : ℤ) ∣ x - 1 := by
    have sum := dvd_add hf h
    rwa [show x - x ^ l + (x ^ l - 1) = x - 1 by ring] at sum
  have hs := dvd_geom_sum₂_self (n := l) (x := x) (y := (1 : ℤ)) hx
  have ht := mul_dvd_mul hs hx
  rw [geom_sum₂_mul] at ht
  simpa [pow_two] using ht

private theorem prime_exponent {p b l : ℕ} (hp : p.Prime) (hb : 2 ≤ b)
    (hl : l.Prime) (he : (b^l)^2 = 4 * primorial p + 1) : False := by
  have rearrange : (b^2)^l = (b^l)^2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hle : l ≤ p := by
    by_contra! h
    have h₁ := Nat.pow_le_pow_right (n := 4) (by decide) (show p+1 ≤ l by omega)
    have h₂ := Nat.pow_le_pow_left (show 4 ≤ b^2 by nlinarith) l
    rw [pow_succ] at h₁
    have h₃ := primorial_lt_four_pow p hp.ne_zero
    omega
  have hd := hl.dvd_primorial_iff.mpr hle
  have hfree := Nat.squarefree_iff_prime_squarefree.mp (squarefree_primorial p) l hl
  by_cases hl2 : l = 2
  · subst l
    have hm := two_mod_four hp
    have mod16 : (b^2)^2 % 16 = 9 := by omega
    rw [← pow_mul, Nat.pow_mod] at mod16
    have hr := Nat.mod_lt b (by decide : 0 < 16)
    interval_cases b % 16 <;> norm_num at mod16
  have eqZ : ((b : ℤ)^2)^l - 1 = 4 * (primorial p : ℤ) := by
    have hn := rearrange.trans he
    have hz : ((b : ℤ)^2)^l = 4 * (primorial p : ℤ) + 1 := by exact_mod_cast hn
    omega
  have hdZ : (l : ℤ) ∣ (primorial p : ℤ) := by exact_mod_cast hd
  have hd' : (l : ℤ) ∣ ((b : ℤ)^2)^l - 1 := eqZ ▸ dvd_mul_of_dvd_right hdZ 4
  have hsq := lift_one hl ((b : ℤ)^2) hd'
  rw [eqZ] at hsq
  have hnat : l^2 ∣ 4 * primorial p := by exact_mod_cast hsq
  have hcop : l.Coprime 2 := (Nat.coprime_primes hl Nat.prime_two).mpr hl2
  have hc : (l^2).Coprime 4 := (hcop.pow_left 2).pow_right 2
  exact hfree (by simpa [pow_two] using hc.dvd_of_dvd_mul_left hnat)

/-- Unconditional proof of H1. The size bound places each prime exponent inside
the primorial. An odd prime exponent would then occur twice in it. -/
theorem no_proper_power : H1 := by
  intro p b k hp hb hk he
  obtain ⟨l, hl, m, hm⟩ := Nat.exists_prime_and_dvd (show k ≠ 1 by omega)
  have hmpos : 0 < m := by by_contra! h; simp [show m = 0 by omega] at hm; omega
  have hb' : 2 ≤ b^m := le_trans hb (by simpa using Nat.pow_le_pow_right (by omega : 0 < b) hmpos)
  apply prime_exponent hp hb' hl
  rwa [← pow_mul b m l, Nat.mul_comm m l, ← hm]

private theorem consecutive {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (h : a n + 1 = primorial p) :
    ∃ d, n+1 = 2*d+1 ∧ d*(d+1) = primorial p := by
  unfold a at h
  have hl : 4 ≤ (n+1)^2 := by nlinarith
  have hfloor : (n+1)^2 / 4 = primorial p := by omega
  let d := (n+1)/2
  have hcases : n+1 = 2*d ∨ n+1 = 2*d+1 := by dsimp [d]; omega
  rcases hcases with hq | hq
  · rw [hq, mul_pow] at hfloor
    have hs : d^2 = primorial p := by omega
    have hm := two_mod_four hp
    rw [← hs, Nat.pow_mod] at hm
    have hr := Nat.mod_lt d (by decide : 0 < 4)
    interval_cases d % 4 <;> norm_num at hm
  · refine ⟨d, hq, ?_⟩
    rw [hq, show (2*d+1)^2 = 4*(d*(d+1))+1 by ring] at hfloor
    omega

end

/-- The elementary step identified in @marcusbuffett's first reduction. -/
theorem discriminant_and_divisors (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime)
    (h : a n + 1 = primorial p) :
    Odd (n+1) ∧ (n+1)^2 = 4 * primorial p + 1 ∧
      ∀ r : ℕ, r.Prime → r ∣ n+1 → p < r := by
  obtain ⟨d, hq, hd⟩ := consecutive hp hn h
  have disc : (n+1)^2 = 4 * primorial p + 1 := by rw [hq, ← hd]; ring
  have large : ∀ r : ℕ, r.Prime → r ∣ n+1 → p < r := by
    intro r hr hdiv
    by_contra! small
    have ha := dvd_mul_of_dvd_right (hr.dvd_primorial_iff.mpr small) 4
    have hb := dvd_pow hdiv (by decide : 2 ≠ 0)
    rw [disc] at hb
    exact hr.not_dvd_one ((Nat.dvd_add_right ha).mp hb)
  exact ⟨⟨d, hq⟩, disc, large⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a024206.main := by
  intro h₁ h₂ n p hn hp h
  obtain ⟨d, hq, hd⟩ := consecutive hp hn h
  obtain ⟨_, disc, large⟩ := discriminant_and_divisors n p hn hp h
  let r := (n+1).minFac
  have hr : r.Prime := Nat.minFac_prime (by omega)
  have hrdiv : r ∣ n+1 := Nat.minFac_dvd _
  have unique : ∃! s : ℕ, s.Prime ∧ s ∣ n+1 := by
    refine ⟨r, ⟨hr, hrdiv⟩, ?_⟩
    rintro s ⟨hs, hsdiv⟩
    exact h₂ p d s r hp hd hs hr (large s hs hsdiv) (large r hr hrdiv)
      (hq ▸ hsdiv) (hq ▸ hrdiv)
  obtain ⟨b,k,hb,hk,hbk⟩ := (isPrimePow_nat_iff _).mp (isPrimePow_iff_unique_prime_dvd.mpr unique)
  have hkle : k ≤ 1 := by
    by_contra! hlarge
    exact h₁ p b k hp hb.two_le hlarge (hbk ▸ disc)
  simp [show k = 1 by omega] at hbk
  exact hbk ▸ hb

end OMA.R_oeis_a024206_R2
