import OMAReductions.R_oeis_a397683_R1

-- Following @luciusacarr (#27449), retain the five residue-order obstructions.
-- Replace the custom seventh-power lifting induction with the general library
-- lemma used in @sntntHb's H3 proof (#28139), and use finite-field power APIs.
-- H4 := ∀ k : ℕ, 1 ≤ k → f (7 ^ k) = 0

/-! Let `x, x + 1` be units modulo `7^k` with common order `d`. Reducing modulo `7`,
`x^d ≡ (x+1)^d ≡ 1`. Lifting the exponent for `7` shows that if `z^o ≡ 1 (mod 7)` then
`z^(o·7^(k-1)) ≡ 1 (mod 7^k)`, so `d ∣ o·7^(k-1)`. For each residue `x mod 7 ∈ {1,…,5}` the
orders modulo `7` of `x` and `x+1` (`1/3, 3/6, 6/3, 3/6, 6/2`) differ in a prime `q ∈ {2,3}`
coprime to `7`, which divides `d` but not `o·7^(k-1)`. -/

open OMA.S_oeis_a397683

namespace OMA.S397683H4

theorem lte7 (a : ℤ) (ha : (7 : ℤ) ∣ a - 1) : ∀ i : ℕ, (7 : ℤ) ^ (i + 1) ∣ a ^ (7 ^ i) - 1 := by
  intro i
  simpa using dvd_sub_pow_of_dvd_sub ha i

theorem up (z o k : ℕ) (hk : 1 ≤ k) (h : (z : ZMod 7) ^ o = 1) :
    (z : ZMod (7 ^ k)) ^ (o * 7 ^ (k - 1)) = 1 := by
  have h7 : (7 : ℤ) ∣ ((z : ℤ) ^ o) - 1 := by
    have h0 : ((((z : ℤ) ^ o - 1 : ℤ)) : ZMod 7) = 0 := by
      push_cast; rw [h]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp h0
  have hd := lte7 _ h7 (k - 1)
  rw [show k - 1 + 1 = k by omega, ← pow_mul] at hd
  have h0 : ((((z : ℤ) ^ (o * 7 ^ (k - 1)) - 1 : ℤ)) : ZMod (7 ^ k)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hd
  push_cast at h0
  exact sub_eq_zero.mp h0

theorem down (z d k : ℕ) (hk : 1 ≤ k) (h : (z : ZMod (7 ^ k)) ^ d = 1) : (z : ZMod 7) ^ d = 1 := by
  have h7 : 7 ∣ 7 ^ k := dvd_pow_self 7 (by omega)
  have hmap := congrArg (ZMod.castHom h7 (ZMod 7)) h
  rwa [map_pow, map_natCast, map_one] at hmap

theorem cast_mod (z : ℕ) : (z : ZMod 7) = ((z % 7 : ℕ) : ZMod 7) := (ZMod.natCast_mod z 7).symm

theorem pow_mod6 (a : ZMod 7) (ha : a ≠ 0) (d : ℕ) : a ^ d = a ^ (d % 6) := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact pow_eq_pow_mod d (ZMod.pow_card_sub_one_eq_one ha)

theorem not_dvd_mul (q o k : ℕ) (hq : q.Prime) (hq7 : q ≠ 7) (hqo : ¬ q ∣ o) :
    ¬ q ∣ o * 7 ^ (k - 1) := by
  intro h
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact hqo h
  · have := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
    exact hq7 this

end OMA.S397683H4

open OMA.S397683H4 in
theorem OMA.solution : OMA.R_oeis_a397683_R1.H4 := by
  intro k hk
  have hne : 7 ^ k ≠ 1 := by
    have : 7 ≤ 7 ^ k := by
      calc 7 = 7 ^ 1 := by norm_num
        _ ≤ 7 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  unfold f
  rw [if_neg hne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro x - ⟨hx, hx1, hord⟩
  have h7dvd : 7 ∣ 7 ^ k := dvd_pow_self 7 (by omega)
  have hx7 : ¬ 7 ∣ x := fun h =>
    absurd (Nat.dvd_gcd h h7dvd) (by rw [hx]; norm_num)
  have hx17 : ¬ 7 ∣ x + 1 := fun h =>
    absurd (Nat.dvd_gcd h h7dvd) (by rw [hx1]; norm_num)
  obtain ⟨d, hd⟩ : ∃ d, d = orderOf (x : ZMod (7 ^ k)) := ⟨_, rfl⟩
  have hpx : (x : ZMod (7 ^ k)) ^ d = 1 := by rw [hd]; exact pow_orderOf_eq_one _
  have hpx1 : (((x + 1 : ℕ) : ZMod (7 ^ k))) ^ d = 1 := by
    rw [hd, hord]; exact pow_orderOf_eq_one _
  have dx := down x d k hk hpx
  have dx1 := down (x + 1) d k hk hpx1
  rw [cast_mod] at dx dx1
  have hdx : ∀ o, ((x % 7 : ℕ) : ZMod 7) ^ o = 1 → d ∣ o * 7 ^ (k - 1) := fun o ho => by
    rw [hd]
    exact orderOf_dvd_of_pow_eq_one (up x o k hk (by rw [cast_mod]; exact ho))
  have hdx1 : ∀ o, (((x + 1) % 7 : ℕ) : ZMod 7) ^ o = 1 → d ∣ o * 7 ^ (k - 1) := fun o ho => by
    rw [hd, hord]
    exact orderOf_dvd_of_pow_eq_one (up (x + 1) o k hk (by rw [cast_mod]; exact ho))
  have hr : x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 := by omega
  have h6 : d % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rcases hr with hr | hr | hr | hr | hr
  · -- x ≡ 1, x+1 ≡ 2 : 3 ∣ d, d ∣ 7^(k-1)
    have hm : (x + 1) % 7 = 2 := by omega
    rw [hm] at dx1
    rw [pow_mod6 _ (by decide)] at dx1
    have h3 : 3 ∣ d := by
      interval_cases h : d % 6 <;> first | omega | (exfalso; revert dx1; decide)
    have := hdx 1 (by rw [hr]; norm_num)
    exact not_dvd_mul 3 1 k (by norm_num) (by norm_num) (by norm_num) (h3.trans this)
  · -- x ≡ 2 (order 3), x+1 ≡ 3 (order 6)
    have hm : (x + 1) % 7 = 3 := by omega
    rw [hm] at dx1
    rw [pow_mod6 _ (by decide)] at dx1
    have h2 : 2 ∣ d := by
      interval_cases h : d % 6 <;> first | omega | (exfalso; revert dx1; decide)
    have := hdx 3 (by rw [hr]; decide)
    exact not_dvd_mul 2 3 k (by norm_num) (by norm_num) (by norm_num) (h2.trans this)
  · -- x ≡ 3 (order 6), x+1 ≡ 4 (order 3)
    have hm : (x + 1) % 7 = 4 := by omega
    rw [hr] at dx
    rw [pow_mod6 _ (by decide)] at dx
    have h2 : 2 ∣ d := by
      interval_cases h : d % 6 <;> first | omega | (exfalso; revert dx; decide)
    have := hdx1 3 (by rw [hm]; decide)
    exact not_dvd_mul 2 3 k (by norm_num) (by norm_num) (by norm_num) (h2.trans this)
  · -- x ≡ 4 (order 3), x+1 ≡ 5 (order 6)
    have hm : (x + 1) % 7 = 5 := by omega
    rw [hm] at dx1
    rw [pow_mod6 _ (by decide)] at dx1
    have h2 : 2 ∣ d := by
      interval_cases h : d % 6 <;> first | omega | (exfalso; revert dx1; decide)
    have := hdx 3 (by rw [hr]; decide)
    exact not_dvd_mul 2 3 k (by norm_num) (by norm_num) (by norm_num) (h2.trans this)
  · -- x ≡ 5 (order 6), x+1 ≡ 6 (order 2)
    have hm : (x + 1) % 7 = 6 := by omega
    rw [hr] at dx
    rw [pow_mod6 _ (by decide)] at dx
    have h3 : 3 ∣ d := by
      interval_cases h : d % 6 <;> first | omega | (exfalso; revert dx; decide)
    have := hdx1 2 (by rw [hm]; decide)
    exact not_dvd_mul 3 2 k (by norm_num) (by norm_num) (by norm_num) (h3.trans this)
