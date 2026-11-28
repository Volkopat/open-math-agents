import OMAReductions.R_mse_3202090_R1
import Mathlib
-- Credit: @LordMike

theorem qs_key (r s k : ℕ) (hr : r.Prime) (hs : s.Prime) (hro : Odd r) (hne : r ≠ s)
    (hk : 1 ≤ k) (hv : padicValNat r (s ^ k - 1) = 1) :
    ¬ r ^ 2 ∣ s ^ (r - 1) - 1 ∧ ¬ r ∣ k := by
  have : Fact r.Prime := ⟨hr⟩
  have hrs : ¬ r ∣ s := fun h => hne ((Nat.prime_dvd_prime_iff_eq hr hs).1 h)
  have hcast : ∀ j, r ∣ s ^ j - 1 ↔ ((s : ZMod r)) ^ j = 1 := by
    intro j
    have h1 : 1 ≤ s ^ j := Nat.one_le_pow _ _ hs.pos
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one, sub_eq_zero]
  have hs0 : (s : ZMod r) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hdr : orderOf (s : ZMod r) ∣ r - 1 := ZMod.orderOf_dvd_card_sub_one hs0
  generalize hd : orderOf (s : ZMod r) = d at hdr
  have hr1 : 0 < r - 1 := by have := hr.two_le; omega
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdr hr1
  have hdle : d ≤ r - 1 := Nat.le_of_dvd hr1 hdr
  have hrk : r ∣ s ^ k - 1 := dvd_of_one_le_padicValNat (by omega)
  have hdk : d ∣ k := hd ▸ orderOf_dvd_of_pow_eq_one ((hcast k).1 hrk)
  have hsd : (s : ZMod r) ^ d = 1 := hd ▸ pow_orderOf_eq_one _
  have hrsd : r ∣ s ^ d - 1 := (hcast d).2 hsd
  have hlt : 1 < s ^ d := Nat.one_lt_pow hdpos.ne' hs.one_lt
  have hnd : ¬ r ∣ s ^ d := by
    intro h
    have h2 := Nat.dvd_sub h hrsd
    have h3 : s ^ d - (s ^ d - 1) = 1 := by omega
    rw [h3] at h2
    exact hr.one_lt.ne' (Nat.dvd_one.1 h2)
  have hlte : ∀ j, j ≠ 0 → padicValNat r ((s ^ d) ^ j - 1) =
      padicValNat r (s ^ d - 1) + padicValNat r j := by
    intro j hj
    have := padicValNat.pow_sub_pow (x := s ^ d) (y := 1) (p := r) hro hlt
      (by simpa using hrsd) hnd hj
    simpa using this
  have hv1 : 1 ≤ padicValNat r (s ^ d - 1) := one_le_padicValNat_of_dvd (by omega) hrsd
  have hnr : ∀ j, 0 < j → j ≤ r - 1 → padicValNat r j = 0 := by
    intro j hj hjr
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    have := Nat.le_of_dvd hj h
    omega
  obtain ⟨j, hj⟩ := hdk
  have hj0 : j ≠ 0 := by rintro rfl; omega
  have e := hlte j hj0
  rw [← pow_mul, ← hj, hv] at e
  have hvj : padicValNat r j = 0 := by omega
  have hvd : padicValNat r (s ^ d - 1) = 1 := by omega
  constructor
  · obtain ⟨j', hj'⟩ := hdr
    have hj'0 : j' ≠ 0 := by rintro rfl; omega
    have hjle : j' ≤ r - 1 := by
      have : j' ≤ d * j' := Nat.le_mul_of_pos_left j' hdpos
      omega
    have e' := hlte j' hj'0
    rw [← pow_mul, ← hj', hnr j' (Nat.pos_of_ne_zero hj'0) hjle, hvd] at e'
    have hne0 : s ^ (r - 1) - 1 ≠ 0 := by
      have : 1 < s ^ (r - 1) := Nat.one_lt_pow (by omega) hs.one_lt
      omega
    rw [padicValNat_dvd_iff_le hne0]
    omega
  · intro hrk2
    rw [hj] at hrk2
    rcases (Nat.Prime.dvd_mul hr).1 hrk2 with h | h
    · have := Nat.le_of_dvd hdpos h
      omega
    · have := one_le_padicValNat_of_dvd hj0 h
      omega

theorem qs_val (r s j k : ℕ) (hr : r.Prime) (hs : s.Prime) (hne : r ≠ s) (hj : 1 < j) (hk : 1 < k)
    (h : r ^ j - r = s ^ k - s) : padicValNat r (s ^ (k - 1) - 1) = 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact s.Prime := ⟨hs⟩
  have hrs : ¬ r ∣ s := fun h => hne ((Nat.prime_dvd_prime_iff_eq hr hs).1 h)
  have h1 : r ^ j - r = r * (r ^ (j - 1) - 1) := by
    rw [Nat.mul_sub_one, ← pow_succ']
    congr 2
    omega
  have h2 : s ^ k - s = s * (s ^ (k - 1) - 1) := by
    rw [Nat.mul_sub_one, ← pow_succ']
    congr 2
    omega
  have hA : 1 < r ^ (j - 1) := Nat.one_lt_pow (by omega) hr.one_lt
  have hB : 1 < s ^ (k - 1) := Nat.one_lt_pow (by omega) hs.one_lt
  have hnd : ¬ r ∣ r ^ (j - 1) - 1 := by
    intro hd
    have hd2 : r ∣ r ^ (j - 1) := dvd_pow_self r (by omega)
    have h3 := Nat.dvd_sub hd2 hd
    have h4 : r ^ (j - 1) - (r ^ (j - 1) - 1) = 1 := by omega
    rw [h4] at h3
    exact hr.one_lt.ne' (Nat.dvd_one.1 h3)
  have hL : padicValNat r (r ^ j - r) = 1 := by
    rw [h1, padicValNat.mul hr.ne_zero (by omega), padicValNat.self hr.one_lt,
      padicValNat.eq_zero_of_not_dvd hnd]
  rw [h, h2, padicValNat.mul hs.ne_zero (by omega), padicValNat.eq_zero_of_not_dvd hrs] at hL
  omega

theorem OMA.solution : OMA.R_mse_3202090_R1.H1 := by
  intro p q n m hp hq op oq lt hn hm h
  have hne : p ≠ q := by omega
  have v1 := qs_val p q n m hp hq hne hn hm h
  have v2 := qs_val q p m n hq hp hne.symm hm hn h.symm
  obtain ⟨a1, a2⟩ := qs_key p q (m - 1) hp hq op hne (by omega) v1
  obtain ⟨b1, b2⟩ := qs_key q p (n - 1) hq hp oq hne.symm (by omega) v2
  exact ⟨a1, b1, a2, b2⟩
