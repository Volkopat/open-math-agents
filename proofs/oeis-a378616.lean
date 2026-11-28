import OMAStatements.S_oeis_a378616
import Mathlib
open OMA.S_oeis_a378616

namespace A378616

lemma primePow_pred_iff {p : ℕ} (hp : p.Prime) :
    IsPrimePow (p - 1) ↔ ∃ m : ℕ, p = 2 ^ (2 ^ m) + 1 := by
  have hp2 := hp.two_le
  constructor
  · intro h
    obtain ⟨r, k, hr, hk, hrk⟩ := (isPrimePow_nat_iff _).mp h
    have hpe : p = r ^ k + 1 := by omega
    rcases hp.eq_two_or_odd with h2 | hodd
    · exfalso
      have h3 : 2 ≤ r ^ k := by
        calc 2 ≤ r := hr.two_le
          _ = r ^ 1 := (pow_one r).symm
          _ ≤ r ^ k := Nat.pow_le_pow_right hr.pos hk
      omega
    · have heven : 2 ∣ r ^ k := by omega
      have h2r : 2 ∣ r := Nat.Prime.dvd_of_dvd_pow Nat.prime_two heven
      have hr2 : r = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h2r).symm
      subst hr2
      have hprime : (2 ^ k + 1).Prime := by rw [← hpe]; exact hp
      obtain ⟨m, hm⟩ := Nat.pow_of_pow_add_prime (by norm_num) (by omega) hprime
      exact ⟨m, by rw [hpe, hm]⟩
  · rintro ⟨m, hm⟩
    have h1 : p - 1 = 2 ^ (2 ^ m) := by omega
    rw [h1]
    exact (isPrimePow_nat_iff _).mpr ⟨2, 2 ^ m, Nat.prime_two, by positivity, rfl⟩

lemma key (p : ℕ) (hp : p.Prime) :
    Nat.findGreatest (fun k => ¬ IsPrimePow k) p = p - 1 ↔ ¬ IsPrimePow (p - 1) := by
  have h2 := hp.two_le
  rw [Nat.findGreatest_eq_iff]
  constructor
  · rintro ⟨-, h, -⟩
    exact h (by omega)
  · intro h
    refine ⟨Nat.sub_le _ _, fun _ => h, ?_⟩
    intro k hk1 hk2
    have hkp : k = p := by omega
    rw [hkp]
    exact not_not.mpr hp.isPrimePow

end A378616

theorem OMA.solution : type_of% @OMA.S_oeis_a378616.main := by
  intro n hn
  have hp : (prime n).Prime := Nat.prime_nth_prime _
  have k1 : a n = prime n - 1
      ↔ ¬ IsPrimePow (prime n - 1) := A378616.key _ hp
  rw [k1, A378616.primePow_pred_iff hp]
  unfold InA159611
  constructor
  · intro h hh
    exact h hh.2
  · intro h hh
    exact h ⟨hn, hh⟩
