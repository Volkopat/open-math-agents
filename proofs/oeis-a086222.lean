import OMAStatements.S_oeis_a086222
import Mathlib

namespace A086222
open OMA.S_oeis_a086222 in
lemma count_gen {n : ℕ} (f : Fin n → ℕ) (N : ℕ) (J : Fin n → Fin n → Fin n) (top : Fin n)
    (hdiv : N.divisors = Finset.univ.image f) (hmono : StrictMono f)
    (hlcm : ∀ i j, Nat.lcm (f i) (f j) = f (J i j)) (htop : f top = N) :
    a N = ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n,
      if i ≤ j ∧ j ≤ l ∧ J i (J j l) = top then 1 else 0 := by
  unfold a
  rw [hdiv, Finset.sum_image hmono.injective.injOn]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_image hmono.injective.injOn]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_image hmono.injective.injOn]
  apply Finset.sum_congr rfl
  intro l _
  have e1 : f i ≤ f j ↔ i ≤ j := hmono.le_iff_le
  have e2 : f j ≤ f l ↔ j ≤ l := hmono.le_iff_le
  have e3 : Nat.lcm (f i) (Nat.lcm (f j) (f l)) = N ↔ J i (J j l) = top := by
    rw [hlcm j l, hlcm i, ← htop]
    exact hmono.injective.eq_iff
  exact if_congr (and_congr e1 (and_congr e2 e3)) rfl rfl

open OMA.S_oeis_a086222 in
def Jpq (i j : Fin 4) : Fin 4 :=
  if i = 0 then j else if j = 0 then i else if i = j then i else 3

open OMA.S_oeis_a086222 in
def Jmax (i j : Fin 3) : Fin 3 := if i ≤ j then j else i

open OMA.S_oeis_a086222 in
lemma tally_pq : (∑ i : Fin 4, ∑ j : Fin 4, ∑ l : Fin 4,
    if i ≤ j ∧ j ≤ l ∧ Jpq i (Jpq j l) = 3 then 1 else 0) = 13 := by decide

open OMA.S_oeis_a086222 in
lemma tally_sq : (∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
    if i ≤ j ∧ j ≤ l ∧ Jmax i (Jmax j l) = 2 then 1 else 0) = 6 := by decide

open OMA.S_oeis_a086222 in
lemma count_pq (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hlt : p < q) : a (p * q) = 13 := by
  have h1p : 1 < p := hp.one_lt
  have hqpq : q < p * q := by nlinarith
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hlt.ne
  have hdiv : (p * q).divisors = Finset.univ.image ![1, p, q, p * q] := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hd, -⟩
      obtain ⟨y, z, hy, hz, rfl⟩ := (Nat.dvd_mul).mp hd
      rcases (Nat.dvd_prime hp).mp hy with rfl | rfl <;>
        rcases (Nat.dvd_prime hq).mp hz with rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨2, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨3, by simp⟩
    · rintro ⟨i, rfl⟩
      refine ⟨?_, Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
      fin_cases i
      · simp
      · exact Dvd.intro _ rfl
      · exact Dvd.intro_left _ rfl
      · simp
  have hmono : StrictMono ![1, p, q, p * q] := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    · simpa using h1p
    · simpa using hlt
    · simpa using hqpq
  have hlcm : ∀ i j : Fin 4,
      Nat.lcm (![1, p, q, p * q] i) (![1, p, q, p * q] j) = ![1, p, q, p * q] (Jpq i j) := by
    have l1 : Nat.lcm p q = p * q := hcop.lcm_eq_mul
    have l2 : Nat.lcm q p = p * q := by
      rw [Nat.lcm_comm]
      exact l1
    have l3 : Nat.lcm p (p * q) = p * q := Nat.lcm_eq_right (Dvd.intro _ rfl)
    have l4 : Nat.lcm (p * q) p = p * q := Nat.lcm_eq_left (Dvd.intro _ rfl)
    have l5 : Nat.lcm q (p * q) = p * q := Nat.lcm_eq_right (Dvd.intro_left _ rfl)
    have l6 : Nat.lcm (p * q) q = p * q := Nat.lcm_eq_left (Dvd.intro_left _ rfl)
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Jpq, l1, l2, l3, l4, l5, l6]
  rw [count_gen ![1, p, q, p * q] (p * q) Jpq 3 hdiv hmono hlcm (by simp)]
  exact tally_pq

open OMA.S_oeis_a086222 in
lemma count_sq (p : ℕ) (hp : p.Prime) : a (p ^ 2) = 6 := by
  have h1p : 1 < p := hp.one_lt
  have hpp : p < p ^ 2 := by nlinarith
  have hdiv : (p ^ 2).divisors = Finset.univ.image ![1, p, p ^ 2] := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hd, -⟩
      obtain ⟨m, hm, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
      interval_cases m
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨2, by simp⟩
    · rintro ⟨i, rfl⟩
      refine ⟨?_, pow_ne_zero 2 hp.ne_zero⟩
      fin_cases i
      · simp
      · show p ∣ p ^ 2
        exact Dvd.intro p (by ring)
      · simp
  have hmono : StrictMono ![1, p, p ^ 2] := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    · simpa using h1p
    · simpa using hpp
  have hlcm : ∀ i j : Fin 3,
      Nat.lcm (![1, p, p ^ 2] i) (![1, p, p ^ 2] j) = ![1, p, p ^ 2] (Jmax i j) := by
    have l3 : Nat.lcm p (p ^ 2) = p ^ 2 := Nat.lcm_eq_right (Dvd.intro p (by ring))
    have l4 : Nat.lcm (p ^ 2) p = p ^ 2 := Nat.lcm_eq_left (Dvd.intro p (by ring))
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Jmax, l3, l4]
  rw [count_gen ![1, p, p ^ 2] (p ^ 2) Jmax 2 hdiv hmono hlcm (by simp)]
  exact tally_sq

end A086222

theorem OMA.solution : type_of% @OMA.S_oeis_a086222.main := by
  refine ⟨?_, fun p hp => A086222.count_sq p hp⟩
  intro p q hp hq hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact A086222.count_pq p q hp hq h
  · rw [mul_comm]
    exact A086222.count_pq q p hq hp h
