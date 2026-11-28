import OMAReductions.R_Grimm_grimm_conjecture_R1

/-!
# Proof of `Grimm.grimm_conjecture.R1.H1`

Grimm's conjecture for runs of at most three consecutive composites `n, …, n + k - 1`:
- `k = 1`: pick any prime factor of `n`.
- `k = 2`: any prime factors of `n` and `n + 1` are distinct since `gcd(n, n + 1) = 1`.
- `k = 3`:
  - If `n` is odd, any prime factors of `n`, `n + 1`, `n + 2` are pairwise distinct (any common
    prime divisor of `n` and `n + 2` divides `2`, impossible since `n` is odd).
  - If `n = 2 * m` is even, then `m ≥ 2` (as `n` is composite), and either `m` or `m + 1` is an
    odd integer `≥ 2`, supplying an odd prime dividing either `n` or `n + 2`; pairing it with `2`
    for the other even term and any prime dividing `n + 1` gives three distinct primes.
-/

namespace OMA.P_Grimm_H1

private lemma dvd_not_eq_of_succ {p n : ℕ} (hp : p.Prime) (h1 : p ∣ n) (h2 : p ∣ n + 1) : False := by
  have hdvd : p ∣ 1 := (Nat.dvd_add_right h1).mp h2
  exact hp.ne_one (Nat.eq_one_of_dvd_one hdvd)

private lemma exists_prime_dvd_of_composite {m : ℕ} (hm : m.Composite) :
    ∃ p : ℕ, p.Prime ∧ p ∣ m :=
  Nat.exists_prime_and_dvd (by have := hm.1; omega)

private lemma exists_odd_prime_dvd {m : ℕ} (hm : 2 ≤ m) (hodd : ¬ 2 ∣ m) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ m := by
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  refine ⟨p, hp, ?_, hpm⟩
  intro hp2
  subst hp2
  exact hodd hpm

private lemma exists_odd_prime_even_pair {n : ℕ} (hn : n.Composite) (heven : 2 ∣ n) :
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ n) ∨ (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ n + 2) := by
  obtain ⟨m, rfl⟩ := heven
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hm1 : m = 1 := by have := hn.1; omega
    subst hm1
    exact hn.2 Nat.prime_two
  by_cases hm_even : 2 ∣ m
  · right
    have hm1_odd : ¬ 2 ∣ m + 1 := by
      intro h
      exact dvd_not_eq_of_succ Nat.prime_two hm_even h
    obtain ⟨p, hp, hp2, hpm⟩ := exists_odd_prime_dvd (by omega : 2 ≤ m + 1) hm1_odd
    refine ⟨p, hp, hp2, dvd_trans hpm ⟨2, by ring⟩⟩
  · left
    obtain ⟨p, hp, hp2, hpm⟩ := exists_odd_prime_dvd hm2 hm_even
    refine ⟨p, hp, hp2, dvd_trans hpm ⟨2, by ring⟩⟩

private lemma mk_three {n p0 p1 p2 : ℕ}
    (hp0 : p0.Prime) (hp1 : p1.Prime) (hp2 : p2.Prime)
    (hd0 : p0 ∣ n) (hd1 : p1 ∣ n + 1) (hd2 : p2 ∣ n + 2)
    (h01 : p0 ≠ p1) (h02 : p0 ≠ p2) (h12 : p1 ≠ p2) :
    ∃ ps : Fin 3 ↪ ℕ, ∀ i : Fin 3, (ps i).Prime ∧ ps i ∣ n + i := by
  let f : Fin 3 → ℕ := ![p0, p1, p2]
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢
    · exact False.elim (h01 hij)
    · exact False.elim (h02 hij)
    · exact False.elim (h01 hij.symm)
    · exact False.elim (h12 hij)
    · exact False.elim (h02 hij.symm)
    · exact False.elim (h12 hij.symm)
  refine ⟨⟨f, hinj⟩, fun i => ?_⟩
  fin_cases i
  · exact ⟨hp0, by simpa [f] using hd0⟩
  · exact ⟨hp1, by simpa [f] using hd1⟩
  · exact ⟨hp2, by simpa [f] using hd2⟩

theorem h1_proof : OMA.R_Grimm_grimm_conjecture_R1.H1 := by
  intro n k _ hk1 hk3 hcomp
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk_cases with rfl | rfl | rfl
  · obtain ⟨p0, hp0, hd0⟩ := exists_prime_dvd_of_composite (hcomp ⟨0, by omega⟩)
    refine ⟨⟨fun _ => p0, fun i j _ => Fin.ext (by omega)⟩, fun i => ?_⟩
    fin_cases i
    exact ⟨hp0, by change p0 ∣ n + (0 : Fin 1); simpa using hd0⟩
  · obtain ⟨p0, hp0, hd0⟩ := exists_prime_dvd_of_composite (hcomp ⟨0, by omega⟩)
    obtain ⟨p1, hp1, hd1⟩ := exists_prime_dvd_of_composite (hcomp ⟨1, by omega⟩)
    have h01 : p0 ≠ p1 := fun heq => dvd_not_eq_of_succ hp0 hd0 (by simpa [heq] using hd1)
    let f : Fin 2 → ℕ := ![p0, p1]
    have hinj : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢
      · exact False.elim (h01 hij)
      · exact False.elim (h01 hij.symm)
    refine ⟨⟨f, hinj⟩, fun i => ?_⟩
    fin_cases i
    · exact ⟨hp0, by simpa [f] using hd0⟩
    · exact ⟨hp1, by simpa [f] using hd1⟩
  · have hc0 : n.Composite := by simpa using hcomp ⟨0, by omega⟩
    have hc1 : (n + 1).Composite := by simpa using hcomp ⟨1, by omega⟩
    have hc2 : (n + 2).Composite := by simpa using hcomp ⟨2, by omega⟩
    obtain ⟨p1, hp1, hd1⟩ := exists_prime_dvd_of_composite hc1
    by_cases heven : 2 ∣ n
    · have hp1_ne2 : p1 ≠ 2 := fun heq => dvd_not_eq_of_succ Nat.prime_two heven (heq ▸ hd1)
      have hd2_even : 2 ∣ n + 2 := dvd_add heven (dvd_refl 2)
      rcases exists_odd_prime_even_pair hc0 heven with ⟨p0, hp0, hp0_ne2, hd0⟩ | ⟨p2, hp2, hp2_ne2, hd2⟩
      · have h01 : p0 ≠ p1 := fun heq => dvd_not_eq_of_succ hp0 hd0 (heq ▸ hd1)
        exact mk_three hp0 hp1 Nat.prime_two hd0 hd1 hd2_even h01 hp0_ne2 hp1_ne2
      · have h12 : p1 ≠ p2 := fun heq => dvd_not_eq_of_succ hp1 hd1 (heq ▸ hd2)
        exact mk_three Nat.prime_two hp1 hp2 heven hd1 hd2 hp1_ne2.symm hp2_ne2.symm h12
    · obtain ⟨p0, hp0, hd0⟩ := exists_prime_dvd_of_composite hc0
      obtain ⟨p2, hp2, hd2⟩ := exists_prime_dvd_of_composite hc2
      have h01 : p0 ≠ p1 := fun heq => dvd_not_eq_of_succ hp0 hd0 (heq ▸ hd1)
      have h12 : p1 ≠ p2 := fun heq => dvd_not_eq_of_succ hp1 hd1 (heq ▸ hd2)
      have h02 : p0 ≠ p2 := by
        intro heq
        have hdvd2 : p0 ∣ 2 := (Nat.dvd_add_right hd0).mp (heq ▸ hd2)
        have hp0_eq2 : p0 = 2 := (Nat.prime_dvd_prime_iff_eq hp0 Nat.prime_two).mp hdvd2
        exact heven (hp0_eq2 ▸ hd0)
      exact mk_three hp0 hp1 hp2 hd0 hd1 hd2 h01 h02 h12

end OMA.P_Grimm_H1

theorem OMA.solution : OMA.R_Grimm_grimm_conjecture_R1.H1 :=
  OMA.P_Grimm_H1.h1_proof
