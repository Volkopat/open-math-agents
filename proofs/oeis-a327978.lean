import OMAStatements.S_oeis_a327978

namespace OMA.A327978

def pm (a m : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | f+1, e => (if e % 2 = 1 then a else 1) * pm a m f (e/2) ^ 2 % m

theorem pm_eq (a m : ℕ) : ∀ f e, e < 2^f → pm a m f e ≡ a^e [MOD m]
  | 0, e, h => by
    obtain rfl : e = 0 := by simpa using h
    rfl
  | f+1, e, h => by
    have ih := pm_eq a m f (e/2) (by rw [pow_succ] at h; omega)
    have hx : (if e % 2 = 1 then a else 1) ≡ a^(e%2) [MOD m] := by
      rcases Nat.mod_two_eq_zero_or_one e with h | h <;> simp [h] <;> rfl
    rw [show a^e = a^(e%2) * (a^(e/2))^2 by rw [← pow_mul, ← pow_add]; congr 1; omega]
    exact (Nat.mod_modEq _ _).trans (hx.mul (ih.pow 2))

theorem L (p a : ℕ) (l : List ℕ) (hl : ∀ q ∈ l, q.Prime)
    (h : 1 < p ∧ p < 2^99 ∧ l.prod ^ 99 % (p-1) = 0 ∧ pm a p 99 (p-1) = 1 ∧
      l.all (fun q => pm a p 99 ((p-1)/q) ≠ 1) := by decide +kernel) : p.Prime := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  have k (e) (he : e ≤ p - 1) : (a : ZMod p)^e = 1 ↔ pm a p 99 e = 1 := by
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', ← pm_eq a p 99 e (by omega),
      Nat.one_mod_eq_one.mpr (by omega), show pm a p 99 e % p = pm a p 99 e from Nat.mod_mod _ _]
  refine lucas_primality p a ((k _ le_rfl).mpr h3) fun q hq hd => ?_
  obtain ⟨r, hr, hqr⟩ := (Prime.dvd_prod_iff hq.prime).mp
    (hq.dvd_of_dvd_pow (hd.trans (Nat.dvd_of_mod_eq_zero h2)))
  rw [(Nat.prime_dvd_prime_iff_eq hq (hl r hr)).mp hqr, Ne, k _ (Nat.div_le_self _ _)]
  simpa using List.all_eq_true.mp h4 r hr

theorem prime_39139476251 : Nat.Prime 39139476251 := L _ 2 [2,5,7,31,313,461] (by norm_num)
theorem prime_4227063435109 : Nat.Prime 4227063435109 :=
  L _ 2 [2,3,39139476251] (by simp [prime_39139476251]; norm_num)
theorem prime_2380299617 : Nat.Prime 2380299617 := L _ 3 [2,74384363] (by norm_num)

open OMA.S_oeis_a327978

theorem derivative_of_factors (n : ℕ) (l : List ℕ) (hp : l.prod = n)
    (hs : ∀ p ∈ l, p.Prime) : arithmeticDerivative n = (l.map (fun p => n / p)).sum := by
  exact ((Nat.primeFactorsList_unique hp hs).map (fun p => n / p)).sum_eq.symm

-- A multiple of five whose derivative is the product of the primes through 43.
theorem multiple_of_five : arithmeticDerivative 32442711864461575 = primorial 43 := by
  have h := derivative_of_factors 32442711864461575 [5, 5, 307, 4227063435109]
    (by decide) (by simp [prime_4227063435109]; norm_num)
  rw [h]
  decide +kernel

-- A multiple of three other than nine whose derivative is the product of the primes through 47.
theorem multiple_of_three : arithmeticDerivative 922334641167462111 = primorial 47 := by
  have h := derivative_of_factors 922334641167462111 [3, 3, 43054087, 2380299617]
    (by decide) (by simp [prime_2380299617]; norm_num)
  rw [h]
  decide +kernel

end OMA.A327978

open OMA.S_oeis_a327978 OMA.A327978

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a327978.main) := by
  intro h
  have hf := h 32442711864461575 (by rw [multiple_of_five]; decide) ⟨43, multiple_of_five⟩
  exact hf.1 (by decide)
