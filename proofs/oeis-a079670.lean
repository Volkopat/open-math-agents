import OMAStatements.S_oeis_a079670
import Mathlib

namespace OMA.A079670Proof

/-- If `s ^ 2 = 5` then `(1 + s)^n - (1 - s)^n = 2^n * s * F(n)` (and the same at `n + 1`). -/
theorem binet_aux {R : Type*} [CommRing R] (s : R) (hs : s ^ 2 = 5) (n : ℕ) :
    ((1 + s) ^ n - (1 - s) ^ n = 2 ^ n * s * (Nat.fib n : R)) ∧
      ((1 + s) ^ (n + 1) - (1 - s) ^ (n + 1) = 2 ^ (n + 1) * s * (Nat.fib (n + 1) : R)) := by
  induction n with
  | zero =>
    refine ⟨by simp, ?_⟩
    simp
    ring
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hf : (Nat.fib (n + 1 + 1) : R) = Nat.fib n + Nat.fib (n + 1) := by
      rw [show n + 1 + 1 = n + 2 from rfl, Nat.fib_add_two, Nat.cast_add]
    rw [hf]
    linear_combination (2 : R) * ih.2 + 4 * ih.1 + ((1 + s) ^ n - (1 - s) ^ n) * hs

/-- Frobenius step: in characteristic `q` with `s ^ 2 = 5` and `5 ^ (q / 2) = -1`,
`2 ^ (q + 1) * s * F(q + 1) = 0`. -/
theorem fib_frob {R : Type*} [CommRing R] (q : ℕ) [hq : Fact q.Prime] [CharP R q] (hq2 : q ≠ 2)
    (s : R) (hs : s ^ 2 = 5) (h5 : (5 : R) ^ (q / 2) = -1) :
    (2 : R) ^ (q + 1) * s * (Nat.fib (q + 1) : R) = 0 := by
  have hodd : q % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hq.out).mpr hq2
  have hq' : q = 2 * (q / 2) + 1 := by omega
  have hsq : s ^ q = -s := by
    calc s ^ q = s ^ (2 * (q / 2) + 1) := by rw [← hq']
      _ = (s ^ 2) ^ (q / 2) * s := by rw [pow_succ s (2 * (q / 2)), pow_mul s 2 (q / 2)]
      _ = -s := by rw [hs, h5]; ring
  have hA : (1 + s) ^ q = 1 - s := by rw [add_pow_char, one_pow, hsq]; ring
  have hB : (1 - s) ^ q = 1 + s := by rw [sub_pow_char, one_pow, hsq]; ring
  rw [← (binet_aux s hs (q + 1)).1, pow_succ, pow_succ, hA, hB]
  ring

/-- If `5` is not a square mod the odd prime `q` (`q ≠ 5`), then `q ∣ F(q + 1)`. -/
theorem dvd_fib_succ (q : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2) (hq5 : q ≠ 5)
    (h : ¬ IsSquare (5 : ZMod q)) : q ∣ Nat.fib (q + 1) := by
  have h50 : (5 : ZMod q) ≠ 0 := by
    intro h0
    have h0' : ((5 : ℕ) : ZMod q) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h0'
    exact hq5 ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_five).mp h0')
  have h20 : (2 : ZMod q) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h0'
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).mp h0')
  have h5 : (5 : ZMod q) ^ (q / 2) = -1 := by
    rcases ZMod.pow_div_two_eq_neg_one_or_one q h50 with h1 | h1
    · exact absurd ((ZMod.euler_criterion q h50).mpr h1) h
    · exact h1
  have : CharP (QuadraticAlgebra (ZMod q) 5 0) q :=
    charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective q
  have hs : (⟨0, 1⟩ : QuadraticAlgebra (ZMod q) 5 0) ^ 2 = 5 := by
    ext <;> simp [sq, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  have h5' : (5 : QuadraticAlgebra (ZMod q) 5 0) ^ (q / 2) = -1 := by
    have e5 : algebraMap (ZMod q) (QuadraticAlgebra (ZMod q) 5 0) 5 = 5 := by
      ext <;> simp [QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
    have h5m := congrArg (algebraMap (ZMod q) (QuadraticAlgebra (ZMod q) 5 0)) h5
    simpa [e5] using h5m
  have key := fib_frob (R := QuadraticAlgebra (ZMod q) 5 0) q hq2 ⟨0, 1⟩ hs h5'
  have key2 : algebraMap (ZMod q) (QuadraticAlgebra (ZMod q) 5 0)
      ((2 : ZMod q) ^ (q + 1) * 5 * (Nat.fib (q + 1) : ZMod q)) = 0 := by
    simp only [map_mul, map_pow, map_ofNat, map_natCast]
    linear_combination (⟨0, 1⟩ : QuadraticAlgebra (ZMod q) 5 0) * key -
      (2 : QuadraticAlgebra (ZMod q) 5 0) ^ (q + 1) *
        (Nat.fib (q + 1) : QuadraticAlgebra (ZMod q) 5 0) * hs
  have key3 : (2 : ZMod q) ^ (q + 1) * 5 * (Nat.fib (q + 1) : ZMod q) = 0 :=
    QuadraticAlgebra.algebraMap_injective
      (key2.trans (map_zero (algebraMap (ZMod q) (QuadraticAlgebra (ZMod q) 5 0))).symm)
  have hpow : (2 : ZMod q) ^ (q + 1) ≠ 0 := pow_ne_zero _ h20
  have hF : (Nat.fib (q + 1) : ZMod q) = 0 := by
    rcases mul_eq_zero.mp key3 with h1 | h1
    · exact absurd h1 (mul_ne_zero hpow h50)
    · exact h1
  exact (ZMod.natCast_eq_zero_iff _ _).mp hF

/-- Every prime factor `q` of `gcd(2^p - 1, F(p))`, `p` an odd prime, satisfies `8 p ∣ q - 1`. -/
theorem key (p q : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (h1 : q ∣ 2 ^ p - 1) (h2 : q ∣ Nat.fib p) : 8 * p ∣ q - 1 := by
  have := Fact.mk hq
  have := Fact.mk hp
  have hpodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr hp2
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h2p : 2 ∣ 2 ^ p := dvd_pow_self 2 hp.ne_zero
    have h1p : 1 ≤ 2 ^ p := Nat.one_le_two_pow
    omega
  have h2p : (2 : ZMod q) ^ p = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (2 ^ p - 1) q).mpr h1
    rw [Nat.cast_sub Nat.one_le_two_pow] at h
    push_cast at h
    exact sub_eq_zero.mp h
  have h20 : (2 : ZMod q) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at h2p
    exact zero_ne_one h2p
  have h21 : (2 : ZMod q) ≠ 1 := by
    intro h
    have h' : (1 : ZMod q) = 0 := by linear_combination h
    exact one_ne_zero h'
  have hpq : p ∣ q - 1 := by
    have h' := ZMod.orderOf_dvd_card_sub_one h20
    rwa [orderOf_eq_prime h2p h21] at h'
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := ⟨p / 2, by omega⟩
  have hfib : (Nat.fib (m + 1) : ZMod q) ^ 2 + (Nat.fib m : ZMod q) ^ 2 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff (Nat.fib p) q).mpr h2
    rw [hm, Nat.fib_two_mul_add_one] at h
    push_cast at h
    exact h
  have hb : (Nat.fib m : ZMod q) ≠ 0 := by
    intro hb0
    have ha0 : (Nat.fib (m + 1) : ZMod q) = 0 := by
      rw [hb0] at hfib
      simpa using hfib
    rw [ZMod.natCast_eq_zero_iff] at hb0 ha0
    have hg := Nat.dvd_gcd hb0 ha0
    rw [(Nat.fib_coprime_fib_succ m).gcd_eq_one] at hg
    exact hq.not_dvd_one hg
  have hneg : ((Nat.fib (m + 1) : ZMod q) / (Nat.fib m : ZMod q)) ^ 2 = -1 := by
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hb)]
    linear_combination hfib
  have hq4 : q % 4 ≠ 3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one hneg
  have h2sq : IsSquare (2 : ZMod q) := ⟨2 ^ (m + 1), by
    rw [← pow_add, show m + 1 + (m + 1) = p + 1 by omega, pow_succ, h2p, one_mul]⟩
  have hq8 := (ZMod.exists_sq_eq_two_iff hq2).mp h2sq
  have h8 : 8 ∣ q - 1 := by omega
  have hcop : Nat.Coprime 8 p := by
    have h2c : Nat.Coprime 2 p := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hpodd)
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact Nat.Coprime.pow_left 3 h2c
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h8 hpq

/-- A nonzero number all of whose prime factors are `≡ 1 (mod N)` is `≡ 1 (mod N)`. -/
theorem modEq_one_of_primes (N : ℕ) :
    ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → q ∣ n → q ≡ 1 [MOD N]) → n ≡ 1 [MOD N] := by
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; exact Nat.ModEq.refl 1
  | prime q hq => intro _ h; exact h q hq dvd_rfl
  | mul a b iha ihb =>
    intro hab h
    have ha : a ≠ 0 := left_ne_zero_of_mul hab
    have hb : b ≠ 0 := right_ne_zero_of_mul hab
    have h' := (iha ha fun q hq hqa => h q hq (dvd_mul_of_dvd_left hqa b)).mul
      (ihb hb fun q hq hqb => h q hq (dvd_mul_of_dvd_right hqb a))
    rwa [mul_one] at h'

/-- `2` and `3` are not squares mod `5`. -/
theorem not_isSquare_two_three :
    ¬ IsSquare ((2 : ℕ) : ZMod 5) ∧ ¬ IsSquare ((3 : ℕ) : ZMod 5) := by
  decide

theorem main_aux (p : ℕ) (hp : p.Prime) (hG : 1 < Nat.gcd (2 ^ p - 1) (Nat.fib p)) :
    8 * p ∣ Nat.gcd (2 ^ p - 1) (Nat.fib p) - 1 ∧
      (p % 10 ≠ 1 → 1 < (Nat.gcd (2 ^ p - 1) (Nat.fib p) - 1) / (8 * p)) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hG (by decide)
  have hp5 : p ≠ 5 := by
    rintro rfl
    exact absurd hG (by decide)
  have hpodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr hp2
  have hp2' := hp.two_le
  obtain ⟨G, hGdef⟩ : ∃ G, G = Nat.gcd (2 ^ p - 1) (Nat.fib p) := ⟨_, rfl⟩
  rw [← hGdef] at hG ⊢
  have hGa : G ∣ 2 ^ p - 1 := by rw [hGdef]; exact Nat.gcd_dvd_left _ _
  have hGb : G ∣ Nat.fib p := by rw [hGdef]; exact Nat.gcd_dvd_right _ _
  have hfac : ∀ q : ℕ, q.Prime → q ∣ G → 8 * p ∣ q - 1 := fun q hq hqG =>
    key p q hp hp2 hq (dvd_trans hqG hGa) (dvd_trans hqG hGb)
  have hmod : G ≡ 1 [MOD 8 * p] := by
    apply modEq_one_of_primes (8 * p) G (by omega)
    intro q hq hqG
    exact ((Nat.modEq_iff_dvd' hq.one_lt.le).mpr (hfac q hq hqG)).symm
  have hdvd : 8 * p ∣ G - 1 := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
  refine ⟨hdvd, fun h10 => ?_⟩
  obtain ⟨c, hc⟩ := hdvd
  have hp0 : 0 < 8 * p := by omega
  rw [hc, Nat.mul_div_cancel_left c hp0]
  by_contra hc1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    omega
  have hc1' : c = 1 := by omega
  subst hc1'
  rw [mul_one] at hc
  have hGval : G = 8 * p + 1 := by omega
  -- `G` is prime: its least prime factor is `≡ 1 (mod 8 p)`, hence `≥ 8 p + 1 = G`.
  have hqprime := Nat.minFac_prime (show G ≠ 1 by omega)
  have hqdvd := Nat.minFac_dvd G
  have hqle := Nat.minFac_le (show 0 < G by omega)
  have h8q := hfac _ hqprime hqdvd
  have hqge := Nat.le_of_dvd (by have := hqprime.two_le; omega) h8q
  have hGprime : G.Prime := by
    have hmin : G.minFac = G := by omega
    rw [← hmin]
    exact hqprime
  have := Fact.mk hGprime
  have hG2 : G ≠ 2 := by omega
  have hG5 : G % 5 ≠ 0 := by
    intro h
    have h5 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hGprime).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have hp5' : p % 5 ≠ 0 := by
    intro h
    have h5 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have h23 : G % 5 = 2 ∨ G % 5 = 3 := by omega
  -- `5` is not a square mod `G`, by quadratic reciprocity (`5 % 4 = 1`).
  have hnsq : ¬ IsSquare (5 : ZMod G) := by
    intro hsq
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have h5' : IsSquare ((5 : ℕ) : ZMod G) := by exact_mod_cast hsq
    have hG5sq := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := G)
      (by norm_num) hG2).mpr h5'
    have e : ((G : ℕ) : ZMod 5) = ((G % 5 : ℕ) : ZMod 5) := (ZMod.natCast_mod G 5).symm
    rw [e] at hG5sq
    rcases h23 with h | h
    · rw [h] at hG5sq
      exact not_isSquare_two_three.1 hG5sq
    · rw [h] at hG5sq
      exact not_isSquare_two_three.2 hG5sq
  have hfibG : G ∣ Nat.fib (G + 1) := dvd_fib_succ G hG2 (by omega) hnsq
  have hgcd : Nat.gcd p (G + 1) = 1 := by
    rcases Nat.coprime_or_dvd_of_prime hp (G + 1) with h | h
    · exact h
    · exfalso
      rw [hGval, show 8 * p + 1 + 1 = p * 8 + 2 by ring] at h
      have h2' : p ∣ 2 := (Nat.dvd_add_right (Nat.dvd_mul_right p 8)).mp h
      have := Nat.le_of_dvd (by norm_num) h2'
      omega
  have hg := Nat.dvd_gcd hGb hfibG
  rw [← Nat.fib_gcd, hgcd, Nat.fib_one] at hg
  exact hGprime.not_dvd_one hg

end OMA.A079670Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a079670.main := by
  intro p hpA
  have hpA' : p.Prime ∧ 1 < Nat.gcd (2 ^ p - 1) (Nat.fib p) := hpA
  exact OMA.A079670Proof.main_aux p hpA'.1 hpA'.2
