import OMAStatements.S_oeis_a123723
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Classification of the multiples of four in A123723

Translation by 2q and reflection show that all squares modulo 4q are
represented by 0,1,...,q. If q=uv is composite, the two representatives
u+v and |u-v| have the same square. For odd prime q a collision would
force the sum or difference of two representatives of the same parity
to equal q. The prime 2 can be checked directly.

Source: https://oeis.org/A123723. Credit: @Solitude1312
-/

open OMA.S_oeis_a123723

namespace OMA.A123723

private lemma shifted (q k : ℕ) : (k + 2 * q) ^ 2 ≡ k ^ 2 [MOD 4 * q] := by
  apply Nat.modEq_iff_dvd.mpr
  refine ⟨-((k : ℤ) + q), ?_⟩
  push_cast
  ring

private lemma mirrored (q k : ℕ) (hk : k ≤ 2 * q) :
    (2 * q - k) ^ 2 ≡ k ^ 2 [MOD 4 * q] := by
  apply Nat.modEq_iff_dvd.mpr
  refine ⟨(k : ℤ) - q, ?_⟩
  push_cast [hk]
  ring

private lemma folded (q : ℕ) (hq : 0 < q) :
    squares (4 * q) = (Finset.range (q + 1)).image (fun k => k ^ 2 % (4 * q)) := by
  have small (j : ℕ) (hj : j < 2 * q) : ∃ t ≤ q, t ^ 2 ≡ j ^ 2 [MOD 4 * q] := by
    by_cases h : j ≤ q
    · exact ⟨j, h, Nat.ModEq.rfl⟩
    · exact ⟨2 * q - j, by omega, mirrored q j hj.le⟩
  ext s
  unfold squares
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    by_cases h : k < 2 * q
    · obtain ⟨t, ht, he⟩ := small k h
      exact ⟨t, by omega, he⟩
    · let j := k - 2 * q
      have hj : j < 2 * q := by dsimp [j]; omega
      have hk' : k = j + 2 * q := by dsimp [j]; omega
      obtain ⟨t, ht, he⟩ := small j hj
      exact ⟨t, by omega, hk' ▸ he.trans (shifted q j).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, by omega, rfl⟩

private lemma collision (u v : ℕ) (hv : 2 ≤ v) (hvu : v ≤ u) :
    ¬ Set.InjOn (fun k : ℕ => k ^ 2 % (4 * (u * v))) (Finset.range (u * v + 1)) := by
  intro hinj
  have hu := Nat.mul_le_mul_left u hv
  have hsum : u + v ≤ u * v := by omega
  have hmod : (u - v) ^ 2 ≡ (u + v) ^ 2 [MOD 4 * (u * v)] := by
    apply Nat.modEq_iff_dvd.mpr
    refine ⟨1, ?_⟩
    push_cast [hvu]
    ring
  have he := hinj (x₁ := u - v) (x₂ := u + v)
    (Finset.mem_range.mpr (by omega)) (Finset.mem_range.mpr (by omega)) hmod
  omega

private lemma prime_of_full_count {q : ℕ} (hq : 2 ≤ q)
    (hcount : (squares (4 * q)).card = q + 1) : q.Prime := by
  rw [folded q (by omega)] at hcount
  have hi := Finset.card_image_iff.mp (hcount.trans (Finset.card_range (q + 1)).symm)
  by_contra hn
  obtain ⟨u, v, hu, hv, he⟩ := (Nat.not_prime_iff_exists_mul_eq hq).mp hn
  have hu2 : 2 ≤ u := by
    by_contra! h
    rcases (show u = 0 ∨ u = 1 by omega) with rfl | rfl <;> simp_all
  have hv2 : 2 ≤ v := by
    by_contra! h
    rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl <;> simp_all
  rcases le_total v u with huv | hvu
  · exact collision u v hv2 huv (he ▸ hi)
  · have he' : v * u = q := (Nat.mul_comm v u).trans he
    exact collision v u hu2 hvu (he' ▸ hi)

private lemma only_multiple {p z : ℕ} (hz : 0 < z) (hlt : z < 2 * p) (hd : p ∣ z) :
    z = p := by
  obtain ⟨k, hk⟩ := hd
  have hklt : k < 2 := by
    by_contra! h
    have := Nat.mul_le_mul_left p h
    omega
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> simp_all

private lemma full_count_of_prime {p : ℕ} (hp : p.Prime) :
    (squares (4 * p)).card = p + 1 := by
  by_cases hp2 : p = 2
  · subst p
    decide
  have hodd := hp.odd_of_ne_two hp2
  have ordered (x y : ℕ) (hlt : x < y) (hy : y ≤ p) (hm : x ^ 2 ≡ y ^ 2 [MOD 4 * p]) : False := by
    have hpar := hm.of_dvd (show 2 ∣ 4 * p from ⟨2*p, by ring⟩)
    have sq_mod_two (z : ℕ) : z ^ 2 % 2 = z % 2 := by
      rw [Nat.pow_mod]
      rcases Nat.mod_two_eq_zero_or_one z with h | h <;> rw [h]
    change x ^ 2 % 2 = y ^ 2 % 2 at hpar
    rw [sq_mod_two, sq_mod_two] at hpar
    have hfactor : y ^ 2 - x ^ 2 = (y - x) * (y + x) := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlt.le
      rw [hd, Nat.add_sub_cancel_left]
      apply Nat.sub_eq_of_eq_add
      ring
    have hdiv := (Nat.modEq_iff_dvd' (Nat.pow_le_pow_left hlt.le 2)).mp hm
    rw [hfactor] at hdiv
    have hprime := hp.dvd_mul.mp ((show p ∣ 4 * p from dvd_mul_left _ _).trans hdiv)
    obtain ⟨t, ht⟩ := hodd
    rcases hprime with hd | hd
    · have := only_multiple (show 0 < y - x by omega) (by omega) hd
      omega
    · have := only_multiple (show 0 < y + x by omega) (by omega) hd
      omega
  rw [folded p hp.pos]
  refine (Finset.card_image_of_injOn ?_).trans (Finset.card_range _)
  intro x hx y hy he
  have hx' := Finset.mem_range.mp hx
  have hy' := Finset.mem_range.mp hy
  by_contra hn
  rcases lt_or_gt_of_ne hn with h | h
  · exact ordered x y h (by omega) he
  · exact ordered y x h (by omega) he.symm

/-- For every q>1, not only the listed ones, the bound is attained
exactly when q is prime. -/
theorem classification (q : ℕ) (hq : 1 < q) :
    (squares (4 * q)).card = q + 1 ↔ q.Prime :=
  ⟨prime_of_full_count hq, full_count_of_prime⟩

lemma conjecture (m : ℕ) (hm : qualifies m) (hi : 4 ≤ preceding m) (hd : 4 ∣ m) :
    (m / 4).Prime := by
  have hr : preceding m ≤ m - 1 := by
    classical
    unfold preceding
    simpa using (Finset.card_filter_le (Finset.Ico 1 m) qualifies)
  obtain ⟨q, he⟩ := hd
  have hq : 1 < q := by omega
  have hc := hm.2
  rw [he, show (4 * q + 4) / 4 = q + 1 by omega] at hc
  rw [he, Nat.mul_div_cancel_left _ (by decide)]
  exact (classification q hq).mp hc

end OMA.A123723

theorem OMA.solution : type_of% @OMA.S_oeis_a123723.main := by
  exact OMA.A123723.conjecture
