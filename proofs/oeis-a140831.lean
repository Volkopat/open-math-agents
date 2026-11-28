import OMAStatements.S_oeis_a140831
import Mathlib.Tactic
-- Credit: @Denyven
theorem OMA.solution : type_of% @OMA.S_oeis_a140831.main := by
  have H (p q : ℕ) {n : ℕ} (hn : 0 < n) : p.Prime ∧ q.Prime ∧ p < q ∧ q < p ^ 2 → p ^ 2 ∣ n ∧ q ∣ n ∧ ¬ q ^ 2 ∣ n → OMA.S_oeis_a140831.inversion n := by
    rintro ⟨hp, hq, hpq, hpow⟩ ⟨hpd, hqd, hqnd⟩
    have := (hp.pow_dvd_iff_le_factorization hn.ne').1 hpd
    have := (hq.dvd_iff_one_le_factorization hn.ne').1 hqd
    have := mt (hq.pow_dvd_iff_le_factorization hn.ne').2 hqnd
    refine ⟨hn, p, q, hp, hq, hpq, (dvd_pow_self p two_ne_zero).trans hpd, hqd, ?_⟩
    rw [show n.factorization q = 1 by omega, pow_one]
    exact hpow.trans_le (pow_le_pow_right' hp.one_le ‹_›)
  exact Set.infinite_of_forall_exists_gt fun a => ⟨3324 + 44100 * a, ⟨H 2 3 (by omega) (by decide) (by omega), H 5 7 (by omega) (by decide) (by omega)⟩, by omega⟩
