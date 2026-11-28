import OMAStatements.S_oeis_a270361
import Mathlib

/-
A270361: for an odd prime p there is at most one odd prime q < p with p*q - 1 a square.

If p*q = m^2 + 1 with p, q odd and q < p, then m is even and m < p. Given two such
pairs (q, m) and (q', m'), p divides m^2 - m'^2 = (m - m')(m + m'). If p divides m - m',
then m = m' because both are below p, hence q = q'. Otherwise p divides m + m', and
0 < m + m' < 2p gives m + m' = p, which is impossible: m + m' is even and p is odd.
-/

namespace OMA.P270361

lemma key (p q m : ℕ) (hp : p.Prime) (ho : Odd p) (hq : q.Prime) (hqo : Odd q) (hqp : q < p)
    (hm : p * q - 1 = m * m) : Even m ∧ m < p ∧ p * q = m * m + 1 := by
  have h1 : p * q = m * m + 1 := by
    have : 0 < p * q := Nat.mul_pos hp.pos hq.pos
    omega
  refine ⟨?_, ?_, h1⟩
  · by_contra hne
    rw [Nat.not_even_iff_odd] at hne
    have h2 : Odd (m * m + 1) := h1 ▸ ho.mul hqo
    exact (Nat.not_even_iff_odd.2 h2) ((hne.mul hne).add_one)
  · by_contra hge
    nlinarith [Nat.mul_le_mul (not_lt.1 hge) (not_lt.1 hge), Nat.mul_lt_mul_of_pos_left hqp hp.pos]

lemma main' : ∀ p : ℕ, p.Prime → Odd p →
    {q : ℕ | q.Prime ∧ Odd q ∧ q < p ∧ IsSquare (p * q - 1)}.Subsingleton := by
  intro p hp ho q ⟨hq, hqo, hqp, m, hm⟩ q' ⟨hq', hqo', hqp', m', hm'⟩
  obtain ⟨he, hl, h1⟩ := key p q m hp ho hq hqo hqp hm
  obtain ⟨he', hl', h1'⟩ := key p q' m' hp ho hq' hqo' hqp' hm'
  have e1 : (p : ℤ) * q = m * m + 1 := by exact_mod_cast h1
  have e2 : (p : ℤ) * q' = m' * m' + 1 := by exact_mod_cast h1'
  have hd : (p : ℤ) ∣ ((m : ℤ) - m') * (m + m') := ⟨(q : ℤ) - q', by linear_combination e2 - e1⟩
  rcases (Nat.prime_iff_prime_int.1 hp).dvd_or_dvd hd with h | h
  · have h0 : (m : ℤ) - m' = 0 :=
      Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    have hmm : m = m' := by omega
    subst hmm
    exact Nat.eq_of_mul_eq_mul_left hp.pos (h1.trans h1'.symm)
  · exfalso
    have h' : p ∣ m + m' := by exact_mod_cast h
    obtain ⟨k, hk⟩ := h'
    obtain ⟨a, ha⟩ := he
    obtain ⟨b, hb⟩ := he'
    obtain ⟨c, hc⟩ := ho
    have h2 := hp.two_le
    have h3 := hq.two_le
    have hk1 : k = 1 := by
      have hk2 : k < 2 := by
        by_contra hk2
        nlinarith [Nat.mul_le_mul_left p (not_lt.1 hk2)]
      interval_cases k
      · have : m = 0 := by omega
        subst this
        nlinarith
      · rfl
    subst hk1
    omega

end OMA.P270361

theorem OMA.solution : type_of% @OMA.S_oeis_a270361.main := OMA.P270361.main'
