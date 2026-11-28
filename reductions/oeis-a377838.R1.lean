import OMAStatements.S_oeis_a377838

/-! Sieve the possible prime divisors of a primorial candidate. -/

namespace OMA.R_oeis_a377838_R1

/-- Sieve condition when the first candidate is composite and p is one modulo three. -/
def H1 : Prop := ∀ p : ℕ, p.Prime → p % 3 = 1 → ¬ (2*p+1).Prime →
  ∃ q : ℕ, q.Prime ∧ 3 ≤ q ∧ q < p ∧
    ∀ r : ℕ, r.Prime → q < r → r ≠ p → r ≤ Nat.sqrt (p*primorial q+1) →
      ¬ r ∣ p*primorial q+1

/-- After the candidates at two and three fail, sieve primes above three. -/
def H2 : Prop := ∀ p : ℕ, p.Prime → p % 3 = 2 → 2 < p →
  ¬ (2*p+1).Prime → ¬ (6*p+1).Prime →
  ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ q < p ∧
    ∀ r : ℕ, r.Prime → q < r → r ≠ p → r ≤ Nat.sqrt (p*primorial q+1) →
      ¬ r ∣ p*primorial q+1

lemma sieved {p q : ℕ} (hp : 0 < p)
    (sieve : ∀ r : ℕ, r.Prime → q < r → r ≠ p → r ≤ Nat.sqrt (p*primorial q+1) →
      ¬ r ∣ p*primorial q+1) : (p*primorial q+1).Prime := by
  have hpos := Nat.mul_pos hp (primorial_pos q)
  apply Nat.prime_def_le_sqrt.mpr
  refine ⟨by omega, ?_⟩
  intro m hm hms hdiv
  let r := m.minFac
  have hr : r.Prime := Nat.minFac_prime (by omega)
  have hrm : r ∣ m := Nat.minFac_dvd _
  have hd := dvd_trans hrm hdiv
  have hbad : ¬ r ∣ p*primorial q := by
    intro h
    have := Nat.dvd_sub hd h
    simp at this
    exact hr.ne_one this
  have hq : q < r := by
    by_contra! h
    exact hbad (dvd_mul_of_dvd_right (hr.dvd_primorial_iff.mpr h) p)
  have hne : r ≠ p := by
    intro heq
    exact hbad (heq ▸ dvd_mul_right p (primorial q))
  exact sieve r hr hq hne ((Nat.le_of_dvd (by omega) hrm).trans hms) hd

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a377838.main := by
  intro first second p hp hgt
  have atTwo : primorial 2 = 2 := by decide
  have atThree : primorial 3 = 6 := by decide
  by_cases h : (2*p+1).Prime
  · exact ⟨2,by decide,hgt,by simpa [atTwo,Nat.mul_comm] using h⟩
  by_cases h3 : p=3
  · subst p
    exact (h (by decide)).elim
  have gt : 3 < p := by omega
  by_cases hh : (6*p+1).Prime
  · exact ⟨3,by decide,gt,by simpa [atThree,Nat.mul_comm] using hh⟩
  have hn : p%3 ≠ 0 := by
    intro hz
    have := (Nat.dvd_prime_two_le hp (by decide : 2 ≤ 3)).mp (Nat.dvd_of_mod_eq_zero hz)
    omega
  by_cases h1 : p%3=1
  · obtain ⟨q,hq,_,hlt,hs⟩ := first p hp h1 h
    exact ⟨q,hq,hlt,sieved hp.pos hs⟩
  · obtain ⟨q,hq,_,hlt,hs⟩ := second p hp (by omega) hgt h hh
    exact ⟨q,hq,hlt,sieved hp.pos hs⟩

end OMA.R_oeis_a377838_R1
