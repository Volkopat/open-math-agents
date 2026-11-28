import OMAStatements.S_oeis_a158509
import Mathlib

/-
A158509: if P = prime(n-1) has P + 5 a square and P + 5 = prime(n+1) - 1, then
prime(n) = P + 2, P ends in 1 and prime(n) ends in 3.

Let Q = prime(n) and R = prime(n+1) = P + 6, so P < Q < P + 6. P is odd (P = 2 gives 7, not a
square), hence Q is P + 2 or P + 4. With P + 5 = m^2, P + 4 = (m - 1)(m + 1) is composite, so
Q = P + 2. Modulo 10 a square is 0, 1, 4, 5, 6 or 9, so the odd number P = m^2 - 5 ends in 1, 5
or 9. It cannot end in 5 (then P = 5 and 10 is not a square) or in 9 (then 5 divides R = P + 6).
-/

namespace OMA.P158509

lemma core (P Q R m : ℕ) (hP : P.Prime) (hQ : Q.Prime) (hR : R.Prime) (hPQ : P < Q) (hQR : Q < R)
    (hm : P + 5 = m * m) (heq : P + 5 = R - 1) :
    Q = P + 2 ∧ P % 10 = 1 ∧ Q % 10 = 3 := by
  have hR6 : R = P + 6 := by
    have := hR.two_le
    omega
  have hP2 : P ≠ 2 := by
    rintro rfl
    have h3 : m < 3 := by nlinarith
    interval_cases m <;> omega
  have hPodd : P % 2 = 1 := hP.eq_two_or_odd.resolve_left hP2
  have hQodd : Q % 2 = 1 := hQ.eq_two_or_odd.resolve_left (by have := hP.two_le; omega)
  have hQ2 : Q = P + 2 := by
    rcases (by omega : Q = P + 2 ∨ Q = P + 4) with h | h
    · exact h
    · exfalso
      obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by
        rcases Nat.eq_zero_or_pos m with rfl | h0
        · omega
        · omega⟩
      have ht : t * (t + 2) = P + 4 := by nlinarith
      have ht2 : 2 ≤ t := by
        by_contra hlt
        have : t ≤ 1 := by omega
        interval_cases t <;> omega
      rw [h, ← ht] at hQ
      exact Nat.not_prime_mul (by omega) (by omega) hQ
  have h10 : (m * m) % 10 = ((m % 10) * (m % 10)) % 10 := Nat.mul_mod m m 10
  have hlt : m % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hP5 : P % 10 ≠ 5 := by
    intro h5
    have hd : 5 ∣ P := by omega
    have hP5' : 5 = P := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hP).1 hd
    subst hP5'
    have h4 : m < 4 := by nlinarith
    interval_cases m <;> omega
  have hP9 : P % 10 ≠ 9 := by
    intro h9
    have hd : 5 ∣ R := by omega
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hR).1 hd
    omega
  have hP1 : P % 10 = 1 := by
    interval_cases hmm : m % 10 <;> omega
  exact ⟨hQ2, hP1, by omega⟩

lemma main' (prime : ℕ → ℕ) (hprime : ∀ k, prime k = Nat.nth Nat.Prime (k - 1)) :
    ∀ n : ℕ, 2 ≤ n → IsSquare (prime (n - 1) + 5) → prime (n - 1) + 5 = prime (n + 1) - 1 →
      prime n = prime (n - 1) + 2 ∧ prime (n - 1) % 10 = 1 ∧ prime n % 10 = 3 := by
  intro n hn hsq heq
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  simp only [hprime] at hsq heq ⊢
  rw [show j + 2 - 1 - 1 = j by omega] at hsq heq ⊢
  rw [show j + 2 + 1 - 1 = j + 2 by omega] at heq
  rw [show j + 2 - 1 = j + 1 by omega]
  obtain ⟨m, hm⟩ := hsq
  exact core _ _ _ m (Nat.prime_nth_prime j) (Nat.prime_nth_prime (j + 1))
    (Nat.prime_nth_prime (j + 2))
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime (by omega))
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime (by omega)) hm heq

end OMA.P158509

theorem OMA.solution : type_of% @OMA.S_oeis_a158509.main := OMA.P158509.main' OMA.S_oeis_a158509.prime (fun _ => rfl)
