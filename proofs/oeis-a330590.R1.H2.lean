import OMAReductions.R_oeis_a330590_R1

/-!
For OEIS A330590, every prime p with p−1 dividing n−1 divides x^n−x
for every integer x. Each subset of these primes therefore gives a
universal divisor by taking its product. Prime factorization recovers
the original subset.
-/

open Finset OMA.S_oeis_a330590

private theorem prime_dvd_power_sub {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n)
    (hd : p - 1 ∣ n - 1) (x : ℤ) : (p : ℤ) ∣ x ^ n - x ^ 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  let a : ZMod p := x
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_pow, Int.cast_pow, sub_eq_zero]
  change a ^ n = a ^ 1
  by_cases ha : a = 0
  · rw [ha, zero_pow (by omega : n ≠ 0), pow_one]
  · let u := Units.mk0 a ha
    have hu := pow_card_eq_one (x := u)
    rw [Fintype.card_units, ZMod.card p] at hu
    have hua : a ^ (p - 1) = 1 := by
      exact congrArg Units.val hu
    obtain ⟨k, hk⟩ := hd
    calc
      _ = a ^ ((p - 1) * k + 1) := by
        rw [show (p - 1) * k + 1 = n by omega]
      _ = _ := by rw [pow_add, pow_mul, hua, one_pow, one_mul]

theorem OMA.solution : OMA.R_oeis_a330590_R1.H2 := by
  intro n hn
  let D := (Nat.divisors (n - 1)).filter (fun d => (d + 1).Prime)
  let P := D.image (fun d => d + 1)
  let F := P.powerset.image (fun Q => ∏ p ∈ Q, p)
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ p - 1 ∣ n - 1 := by
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hp
    obtain ⟨hd, hp⟩ := mem_filter.mp hd
    exact ⟨hp, by simpa using (Nat.mem_divisors.mp hd).1⟩
  have hPcard : P.card = A067513 (n - 1) := by
    exact card_image_of_injective D (fun _ _ h => by omega)
  have hRecover (Q : Finset ℕ) (hQ : Q ∈ P.powerset) :
      (∏ p ∈ Q, p).primeFactors = Q :=
    Nat.primeFactors_prod (fun p hp => (hP p (mem_powerset.mp hQ hp)).1)
  have hFcard : F.card = 2 ^ A067513 (n - 1) := by
    dsimp only [F]
    rw [card_image_of_injOn, card_powerset, hPcard]
    intro Q hQ R hR h
    exact (hRecover Q hQ).symm.trans ((congrArg Nat.primeFactors h).trans (hRecover R hR))
  let U : Set ℕ := {m | 0 < m ∧ ∀ x : ℤ, (m : ℤ) ∣ x ^ n - x ^ 1}
  have hF : (F : Set ℕ) ⊆ U := by
    intro m hm
    obtain ⟨Q, hQ, rfl⟩ := mem_image.mp hm
    have hQ' (p : ℕ) (hp : p ∈ Q) : p.Prime ∧ p - 1 ∣ n - 1 :=
      hP p (mem_powerset.mp hQ hp)
    refine ⟨Finset.prod_pos (fun p hp => (hQ' p hp).1.pos), ?_⟩
    intro x
    rw [Nat.cast_prod]
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hne
      exact ((Nat.coprime_primes (hQ' p hp).1 (hQ' q hq).1).mpr hne).isCoprime
    · intro p hp
      exact prime_dvd_power_sub (hQ' p hp).1 hn (hQ' p hp).2 x
  have h2 : 0 < (2 : ℤ) ^ n - 2 ^ 1 := by
    have hpow : (2 : ℤ) ^ 2 ≤ (2 : ℤ) ^ n :=
      pow_le_pow_right₀ (by decide) hn
    norm_num at hpow ⊢
    omega
  have hU : U.Finite := by
    apply (Set.finite_Icc (a := 1) (b := ((2 : ℤ) ^ n - 2 ^ 1).toNat)).subset
    intro m hm
    have hm0 : 0 < m := hm.1
    have hdvd := Int.le_of_dvd h2 (hm.2 2)
    exact ⟨by omega, by omega⟩
  change 2 ^ A067513 (n - 1) ≤ U.ncard
  rw [← hFcard, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hF hU
