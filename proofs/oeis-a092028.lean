import OMAStatements.S_oeis_a092028
import Mathlib

/-!
# OEIS A092028: the least `m > 1` with `m ∣ n^m - 1` is the least prime factor of `n - 1`

Let `r` be the least prime factor of `n - 1` (`n ≥ 3`). Since `n ≡ 1 (mod r)` we get
`r ∣ n^r - 1`, so `r` is admissible.

Conversely let `m > 1` with `m ∣ n^m - 1` and let `q` be the least prime factor of `m`.
Then `n^m = 1` in `ZMod q`, and `n^(q-1) = 1` by Fermat, so the order `d` of `n` divides both
`m` and `q - 1`. Every prime factor of `m` is at least `q`, so `gcd(m, q - 1) = 1` and `d = 1`,
i.e. `q ∣ n - 1`. Hence `m ≥ q ≥ r`.
-/

open OMA.S_oeis_a092028

namespace OMA.A092028

/-- `m ∣ n^m - 1` (for `n ≥ 1`) says `n^m = 1` modulo any divisor `q` of `m`. -/
lemma pow_eq_one {n m q : ℕ} (hn : 1 ≤ n) (hq : q ∣ m) (h : m ∣ n ^ m - 1) :
    (n : ZMod q) ^ m = 1 := by
  have h1 : ((n ^ m - 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (hq.trans h)
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hn)] at h1
  push_cast at h1
  exact sub_eq_zero.mp h1

/-- Every admissible `m` is at least the least prime factor of `n - 1`. -/
lemma ge_minFac {n m : ℕ} (hn : 3 ≤ n) (hm : 1 < m) (h : m ∣ n ^ m - 1) :
    (n - 1).minFac ≤ m := by
  have hq : (m.minFac).Prime := Nat.minFac_prime (by omega)
  have : Fact (m.minFac).Prime := ⟨hq⟩
  have hpow : (n : ZMod m.minFac) ^ m = 1 := pow_eq_one (by omega) (Nat.minFac_dvd m) h
  -- `n` is a unit modulo `q`
  have hn0 : (n : ZMod m.minFac) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hpow
    exact zero_ne_one hpow
  have hd1 : orderOf (n : ZMod m.minFac) ∣ m := orderOf_dvd_of_pow_eq_one hpow
  have hd2 : orderOf (n : ZMod m.minFac) ∣ m.minFac - 1 := ZMod.orderOf_dvd_card_sub_one hn0
  -- the order is `1`
  have hord : orderOf (n : ZMod m.minFac) = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : m.minFac ≤ p := Nat.minFac_le_of_dvd hp.two_le (hpd.trans hd1)
    have h2 : p ≤ m.minFac - 1 :=
      Nat.le_of_dvd (by have := hq.two_le; omega) (hpd.trans hd2)
    have := hq.two_le
    omega
  have hone : (n : ZMod m.minFac) = 1 := orderOf_eq_one_iff.mp hord
  -- so `q ∣ n - 1`
  have hdvd : m.minFac ∣ n - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (by omega), hone]
    simp
  calc (n - 1).minFac ≤ m.minFac := Nat.minFac_le_of_dvd hq.two_le hdvd
    _ ≤ m := Nat.minFac_le (by omega)

/-- The least prime factor of `n - 1` is admissible. -/
lemma minFac_mem {n : ℕ} (hn : 3 ≤ n) :
    1 < (n - 1).minFac ∧ (n - 1).minFac ∣ n ^ (n - 1).minFac - 1 := by
  have hr : ((n - 1).minFac).Prime := Nat.minFac_prime (by omega)
  refine ⟨hr.one_lt, ?_⟩
  have h1 : (n - 1).minFac ∣ n - 1 := Nat.minFac_dvd _
  have h2 : n - 1 ∣ n ^ (n - 1).minFac - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow n 1 (n - 1).minFac
  exact h1.trans h2

end OMA.A092028

open OMA.A092028 in
theorem OMA.solution : type_of% @OMA.S_oeis_a092028.main := by
  intro n hn
  have hmem := minFac_mem hn
  have heq : a n = (n - 1).minFac := by
    unfold a
    refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ ?_)
    rintro m ⟨hm1, hm2⟩
    exact ge_minFac hn hm1 hm2
  rw [heq]
  exact ⟨Nat.minFac_prime (by omega), rfl⟩
