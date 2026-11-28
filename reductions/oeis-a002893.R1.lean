import OMAStatements.S_oeis_a002893

/-!
# Prime-power degrees in Sun's irreducibility conjecture

For A002893, reciprocal Eisenstein settles every power of two. At an odd
prime p the translated Eisenstein argument settles powers of p whenever
2^(p-1) is not 1 modulo p². The same odd-prime criterion also applies to
the Apéry polynomial of A005259. The remaining hypotheses concern
Wieferich prime powers and degrees with more than one prime divisor.
-/

open Polynomial Finset

namespace OMA.R_oeis_a002893_R1

namespace PrimePower

theorem choose_sq_dvd {p : ℕ} (hp : p.Prime) {r k : ℕ}
    (h0 : 0 < k) (hk : k < p ^ r) : p ^ 2 ∣ (p ^ r).choose k ^ 2 :=
  pow_dvd_pow_of_dvd (hp.dvd_choose_pow h0.ne' hk.ne) 2

/-- Modulo the square of a prime, the central entry above a prime-power index
has just the two endpoint contributions in Vandermonde's identity. -/
theorem centralChoose_cast {p : ℕ} (hp : p.Prime) (r : ℕ) :
    (((2 * (p ^ r)).choose (p ^ r) : ℕ) : ZMod (p ^ 2)) = 2 := by
  have hpos : 0 < p ^ r := pow_pos hp.pos _
  rw [← Nat.sum_range_choose_sq, Nat.cast_sum, Finset.sum_range_succ]
  have hsum : (∑ k ∈ Finset.range (p ^ r), (((p ^ r).choose k ^ 2 : ℕ) : ZMod (p ^ 2))) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k hk hne
      exact (ZMod.natCast_eq_zero_iff ..).mpr (choose_sq_dvd hp (Nat.pos_of_ne_zero hne) (Finset.mem_range.mp hk))
    · intro h
      exact (h (Finset.mem_range.mpr hpos)).elim
  rw [hsum]
  norm_num

/-- Above the first power of a prime, the powers of Frobenius agree on a
rational integer prime to that prime, modulo its square. -/
theorem primePowerExponent_mod_prime_sq {p b : ℕ} (hp : p.Prime) (hb : b.Coprime p) (r : ℕ) :
    b ^ (p ^ (r + 1)) ≡ b ^ p [MOD p ^ 2] := by
  have htot : (p ^ 2).totient = p * (p - 1) := by
    simpa using Nat.totient_prime_pow_succ hp 1
  have hp2 : 1 < p ^ 2 := one_lt_pow₀ hp.one_lt (by decide)
  have hbase : b ^ (p * p) ≡ b ^ p [MOD p ^ 2] := by
    have he : p * p = p + (p ^ 2).totient := by
      rw [htot, Nat.add_comm p, ← Nat.mul_add_one, Nat.sub_one_add_one hp.ne_zero]
    change b ^ (p * p) % (p ^ 2) = b ^ p % (p ^ 2)
    rw [he, Nat.pow_add_totient_mod_eq hp2 (hb.pow_right 2)]
  induction r with
  | zero => simp only [Nat.zero_add, pow_one]; exact Nat.ModEq.refl _
  | succ r ih =>
    rw [pow_succ p (r+1), pow_mul]
    exact (ih.pow p).trans (by simpa [pow_mul] using hbase)

/-- The usual non-Wieferich hypothesis at base b controls every prime-power
degree, not just degree p. -/
theorem nonWieferich_primePowers {p b : ℕ} (hp : p.Prime) (hb : b.Coprime p)
    (hnw : ¬ b ^ (p-1) ≡ 1 [MOD p ^ 2]) (r : ℕ) :
    ¬ b ^ (p ^ (r+1)) ≡ b [MOD p ^ 2] := by
  intro h
  have h1 := (primePowerExponent_mod_prime_sq hp hb r).symm.trans h
  have he : p - 1 + 1 = p := Nat.sub_one_add_one hp.ne_zero
  have h2 : b ^ (p-1) * b ≡ 1 * b [MOD p ^ 2] := by
    simpa only [← pow_succ, he, one_mul] using h1
  exact hnw (Nat.ModEq.cancel_right_of_coprime (hb.pow_right 2).symm h2)

/-- At an odd prime, a base and its square are Wieferich simultaneously. -/
theorem nonWieferich_square_base {p b : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hb : b.Coprime p) (hnw : ¬ b ^ (p-1) ≡ 1 [MOD p ^ 2]) :
    ¬ (b ^ 2) ^ (p-1) ≡ 1 [MOD p ^ 2] := by
  let a := b ^ (p-1)
  have hfermat : a ≡ 1 [MOD p] := Nat.ModEq.pow_card_sub_one_eq_one hp hb
  have hcop2 : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).mpr hodd.symm
  have hcop : (a+1).Coprime p := by
    change (a+1).gcd p = 1
    exact (hfermat.add_right 1).gcd_eq.trans hcop2
  intro h
  have hsq : a^2 ≡ 1 [MOD p ^ 2] := by
    simpa only [a, ← pow_mul, mul_comm 2 (p-1)] using h
  have hprod : a * (a+1) ≡ 1 * (a+1) [MOD p ^ 2] := by
    simpa [pow_two, Nat.mul_add, Nat.add_comm 1 a] using hsq.add_right a
  exact hnw (Nat.ModEq.cancel_right_of_coprime (hcop.pow_right 2).symm hprod)

/-- Lift the unique simple choice of shift modulo p using a unit modulo p².
Its value at the shifted origin detects failure of the Wieferich congruence. -/
theorem primePowerShift {p b c : ℕ} (hp : p.Prime) (ho : p ≠ 2)
    (hb : b.Coprime p) (r : ℕ) (hend : (c : ZMod (p ^ 2)) = b)
    (hw : ¬ b ^ (p ^ r) ≡ b [MOD p ^ 2]) :
    ∃ t : ℤ, (1 + (c : ZMod p) * (t : ZMod p) ^ (p ^ r) = 0) ∧
          (1 + (c : ZMod (p^2)) * (t : ZMod (p^2)) ^ (p ^ r) ≠ 0) := by
  let : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let u := ZMod.unitOfCoprime b (hb.pow_right 2)
  let t : ℤ := ((-((u⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))).val : ℕ)
  have ht : (t : ZMod (p^2)) = -((u⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2)) := by
    simp [t]
  have hu : (u : ZMod (p^2)) = b := by simp [u]
  have hprod : (c : ZMod (p^2)) * (t : ZMod (p^2)) = -1 := by
    rw [hend, ← hu, ht, mul_neg, Units.mul_inv]
  let π := ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)
  have hprod₁ := congrArg π hprod
  have h1 : (c : ZMod p) * (t : ZMod p) = -1 := by simpa [π] using hprod₁
  refine ⟨t, ?_, ?_⟩
  · rw [ZMod.pow_card_pow, h1]; simp
  · intro bad
    have hn : Odd (p ^ r) := (hp.odd_of_ne_two ho).pow
    rw [hend, ← hu, ht, hn.neg_pow, mul_neg] at bad
    have hi : (u : ZMod (p^2)) * (↑u⁻¹ : ZMod (p^2)) ^ (p ^ r) = 1 := by
      linear_combination -bad
    have hEq := congrArg (fun x : ZMod (p ^ 2) => x * (u : ZMod (p^2)) ^ (p ^ r)) hi
    simp only [mul_assoc, ← mul_pow, Units.inv_mul, one_pow, mul_one, one_mul] at hEq
    apply hw
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    simpa [Nat.cast_pow, ← hu] using hEq.symm

private lemma coeff_seriesPoly (R : Type*) [CommRing R] (a : ℕ → ℕ) (N k : ℕ) :
    ((∑ j ∈ Finset.range (N + 1), C (a j : R) * X ^ j)).coeff k = if k ≤ N then (a k : R) else 0 := by
  simp [finsetSum_coeff, coeff_X_pow]

private lemma map_seriesPoly {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : ℕ → ℕ) (N : ℕ) :
    ((∑ j ∈ Finset.range (N + 1), C (a j : R) * X ^ j)).map φ = (∑ j ∈ Finset.range (N + 1), C (a j : S) * X ^ j) := by
  simp [Polynomial.map_sum]

private lemma sparse_mod (m d : ℕ) (hdiv : m ∣ d) (a : ℕ → ℕ) (N : ℕ) (hN : 0 < N)
    (h0 : a 0 = 1) (hm : ∀ k, 0 < k → k < N → d ∣ a k) :
    (∑ j ∈ Finset.range (N + 1), C (a j : (ZMod m)) * X ^ j) = 1 + C (a N : ZMod m) * X ^ N := by
  ext k
  rw [coeff_seriesPoly, coeff_add, coeff_C_mul, coeff_X_pow, coeff_one]
  by_cases hk : k = 0
  · subst k
    simp [h0, Nat.ne_of_lt hN]
  by_cases he : k = N
  · subst k
    simp [hk]
  by_cases hl : k ≤ N
  · have hz : (a k : ZMod m) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (hdiv.trans (hm k (by omega) (by omega)))
    simp [hk, he, hl, hz]
  · simp [hk, he, hl]

theorem sparseIrreducible {p : ℕ} (hp : p.Prime) (a : ℕ → ℕ) (r : ℕ) (t : ℤ) (h0 : a 0 = 1)
    (hm : ∀ k, 0 < k → k < p ^ r → p ^ 2 ∣ a k)
    (hroot : 1 + (a (p ^ r) : ZMod p) * (t : ZMod p) ^ (p ^ r) = 0)
    (hlift : 1 + (a (p ^ r) : ZMod (p ^ 2)) * (t : ZMod (p ^ 2)) ^ (p ^ r) ≠ 0) :
    Irreducible (∑ k ∈ Finset.range (p ^ r + 1), C (a k : ℚ) * X ^ k) := by
  let : Fact p.Prime := ⟨hp⟩
  let N := p ^ r
  let f := (∑ j ∈ Finset.range (N + 1), C (a j : ℤ) * X ^ j)
  have hN : 0 < N := pow_pos hp.pos _
  have hleading : (a N : ZMod p) ≠ 0 := by
    intro hz
    change 1 + (a N : ZMod p) * _ = 0 at hroot
    simp [hz] at hroot
  have hlN : a N ≠ 0 := by
    intro hz
    simp [hz] at hleading
  have hdeg : f.natDegree = N := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro k hk
      simp [f, not_le.mpr hk]
    · simpa [f, coeff_seriesPoly] using hlN
  have hlead : f.leadingCoeff = (a N : ℤ) := by
    rw [← coeff_natDegree, hdeg]; simp [f]
  have hprim : f.IsPrimitive := by
    apply isPrimitive_iff_isUnit_of_C_dvd.mpr
    intro b hb
    apply isUnit_iff_dvd_one.mpr
    simpa [f, coeff_seriesPoly, h0] using (C_dvd_iff_dvd_coeff _ _).mp hb 0
  rw [← map_seriesPoly (Int.castRingHom ℚ)]
  apply (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp
  apply generalizedEisenstein (K := ZMod p) (q := X - C t) (p := N)
    (by simpa using irreducible_X_sub_C ((t : ZMod p))) (monic_X_sub_C _) hprim
    (hdeg ▸ hN)
  · simpa [hlead] using hleading
  · rw [show f = (∑ j ∈ Finset.range (N + 1), C (a j : ℤ) * X ^ j) from rfl, map_seriesPoly,
      sparse_mod p (p ^ 2) (dvd_pow_self p (by decide)) a N hN h0 hm]
    change _ = C ((algebraMap ℤ (ZMod p)) f.leadingCoeff) * _
    rw [hlead]
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    simp only [eq_intCast, Int.cast_natCast]
    change _ = C (a N : ZMod p) * ((X - C (t : ZMod p)) ^ (p ^ r))
    rw [sub_pow_char_pow, ← C_pow, mul_sub, ← C_mul]
    have eq : (a N : ZMod p) * (t : ZMod p) ^ N = -1 := by
      change 1 + (a N : ZMod p) * (t : ZMod p) ^ N = 0 at hroot
      linear_combination hroot
    change 1 + _ = _ - C ((a N : ZMod p) * (t : ZMod p) ^ N)
    rw [eq, map_neg, map_one]
    ring
  · rw [modByMonic_X_sub_C_eq_C_eval, map_C, ne_eq, C_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
    change f.eval t ∉ RingHom.ker (Int.castRingHom (ZMod p)) ^ 2
    rw [ZMod.ker_intCastRingHom, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hd
    have hz : ((f.eval t : ℤ) : ZMod (p ^ 2)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (by exact_mod_cast hd)
    have hev := eval_map_apply (p := f) (Int.castRingHom (ZMod (p ^ 2))) t
    rw [show f = (∑ j ∈ Finset.range (N + 1), C (a j : ℤ) * X ^ j) from rfl, map_seriesPoly,
        sparse_mod (p ^ 2) (p ^ 2) dvd_rfl a N hN h0 hm] at hev
    apply hlift
    calc
      _ = ((f.eval t : ℤ) : ZMod (p ^ 2)) := by simpa [f] using hev
      _ = 0 := hz

/-- A sparse polynomial at a prime-power degree is irreducible when its
leading residue is a unit that fails the base-b Wieferich congruence. -/
theorem irreducible_of_nonWieferich {p b : ℕ} (hp : p.Prime) (ho : p ≠ 2)
    (hb : b.Coprime p) (hw : ¬ b ^ (p - 1) ≡ 1 [MOD p ^ 2]) (r : ℕ)
    (a : ℕ → ℕ) (h0 : a 0 = 1)
    (hm : ∀ k, 0 < k → k < p ^ (r + 1) → p ^ 2 ∣ a k)
    (hc : (a (p ^ (r + 1)) : ZMod (p ^ 2)) = b) :
    Irreducible (∑ k ∈ Finset.range (p ^ (r + 1) + 1), C (a k : ℚ) * X ^ k) := by
  obtain ⟨t, h₁, h₂⟩ := primePowerShift hp ho hb (r + 1) hc (nonWieferich_primePowers hp hb hw r)
  exact sparseIrreducible hp a (r + 1) t h0 hm h₁ h₂

/-- Both Sun coefficient families have p²-divisible interior coefficients.
Vandermonde gives endpoint 2 for A002893 and endpoint 4 for A005259. -/
theorem sun_primePower {p : ℕ} (hp : p.Prime) (ho : p ≠ 2)
    (hw : ¬ 2 ^ (p - 1) ≡ 1 [MOD p ^ 2]) (r : ℕ) :
    Irreducible (OMA.S_oeis_a002893.g (p ^ (r + 1))) := by
  let N := p ^ (r + 1)
  let a := fun k : ℕ => (N.choose k) ^ 2 * (2 * k).choose k
  have hc : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).mpr ho.symm
  apply irreducible_of_nonWieferich hp ho hc hw r a (by simp [a])
  · intro k hk hkN
    exact dvd_mul_of_dvd_left (choose_sq_dvd hp hk hkN) _
  · simpa [a, N] using centralChoose_cast hp (r+1)

/-- Written in precisely the rational-coefficient form of A005259's
aperyPoly, so this corollary can also be checked against its canonical module. -/
theorem apery_primePower {p : ℕ} (hp : p.Prime) (ho : p ≠ 2)
    (hw : ¬ 2 ^ (p - 1) ≡ 1 [MOD p ^ 2]) (r : ℕ) :
    let N := p ^ (r + 1)
    Irreducible (∑ k ∈ Finset.range (N + 1),
      C ((N.choose k : ℚ) ^ 2 * ((N+k).choose k : ℚ) ^ 2) * X ^ k) := by
  let N := p ^ (r + 1)
  let a := fun k : ℕ => (N.choose k)^2 * ((N+k).choose k)^2
  have hc : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).mpr ho.symm
  have h := irreducible_of_nonWieferich hp ho (hc.pow_left 2)
    (nonWieferich_square_base hp ho hc hw) r a (by simp [a])
    (fun k hk hkN => dvd_mul_of_dvd_left (choose_sq_dvd hp hk hkN) _)
  have hEnd : (a N : ZMod (p ^ 2)) = ((2^2 : ℕ) : ZMod (p ^ 2)) := by
    simp only [a, N, Nat.choose_self, one_pow, one_mul, ← two_mul, Nat.cast_pow]
    rw [centralChoose_cast hp (r+1)]
    norm_num
  simpa [a, N] using h hEnd

/-- Specialize to all requested powers of three, including degree one. -/
theorem apery_three_pow (r : ℕ) :
    let N := 3 ^ r
    Irreducible (∑ k ∈ Finset.range (N+1),
      C ((N.choose k : ℚ) ^ 2 * ((N+k).choose k : ℚ) ^ 2) * X ^ k) := by
  cases r with
  | zero =>
    convert (irreducible_C_mul_X_add_C (by norm_num : (4 : ℚ) ≠ 0) isRelPrime_one_right :
        Irreducible (C (4 : ℚ) * X + C 1)) using 1
    norm_num [Finset.sum_range_succ, Nat.choose, add_comm]
    exact (Polynomial.C_eq_natCast 4).symm
  | succ r => exact apery_primePower Nat.prime_three (by decide) (by decide) r


private theorem expansion_coeff {R : Type*} [CommSemiring R] (N : ℕ) (a : ℕ → R) (i : ℕ) :
    (∑ k ∈ range (N+1), C (a k) * X^k).coeff i = if i ≤ N then a i else 0 := by
  classical
  simp [finsetSum_coeff, Finset.mem_range]

private theorem reciprocal_reindex {R : Type*} [CommSemiring R] (N : ℕ) (a : ℕ → R) :
    (∑ k ∈ range (N+1), C (a k) * X^(N-k)) = ∑ k ∈ range (N+1), C (a (N-k)) * X^k := by
  rw [← Finset.sum_range_reflect (fun k => C (a k) * X^(N-k)) (N+1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  congr 2
  omega

theorem irreducible_of_reciprocal (N : ℕ) (a : ℕ → ℕ) (h0 : a 0 = 1) (hN : a N ≠ 0)
    (h : Irreducible (∑ k ∈ range (N+1), C (a k : ℚ) * X^(N-k))) :
    Irreducible (∑ k ∈ range (N+1), C (a k : ℚ) * X^k) := by
  classical
  let P : ℚ[X] := ∑ k ∈ range (N+1), C (a k : ℚ) * X^k
  have hc (i : ℕ) : P.coeff i = if i ≤ N then (a i : ℚ) else 0 :=
    expansion_coeff N (fun k => (a k : ℚ)) i
  have hd : P.natDegree = N := natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun i hi => by simp [hc, hi.not_ge])
    (by simp [hc, hN])
  have ht : P.natTrailingDegree = 0 := Nat.le_zero.mp <|
    natTrailingDegree_le_of_ne_zero (by simp [hc, h0] : P.coeff 0 ≠ 0)
  have href : P.mirror = ∑ k ∈ range (N+1), C (a k : ℚ) * X^(N-k) := by
    rw [reciprocal_reindex]
    ext i
    by_cases hi : i ≤ N
    · rw [coeff_mirror, hd, ht, add_zero, revAt_le hi, hc, if_pos (Nat.sub_le N i),
          expansion_coeff, if_pos hi]
    · rw [coeff_eq_zero_of_natDegree_lt (by simpa [mirror_natDegree, hd] using Nat.lt_of_not_ge hi),
          expansion_coeff, if_neg hi]
  let e : ℚ[X] ≃* ℚ[X] :=
    { toFun := Polynomial.mirror, invFun := Polynomial.mirror,
      left_inv := Polynomial.mirror_mirror, right_inv := Polynomial.mirror_mirror,
      map_mul' := fun x y => Polynomial.mirror_mul_of_domain x y }
  apply (MulEquiv.irreducible_iff e (x := P)).mp
  simpa only [show e P = P.mirror from rfl, href] using h


private theorem reciprocal_eisenstein_two (N : ℕ) (a : ℕ → ℕ) (hpos : 0 < N)
    (h0 : a 0 = 1) (hN : a N ≠ 0)
    (he : ∀ i, 0 < i → i ≤ N → 2 ∣ a i) (htop : ¬ 4 ∣ a N) :
    Irreducible (∑ k ∈ range (N+1), C (a k : ℚ) * X^k) := by
  classical
  apply irreducible_of_reciprocal N a h0 hN
  rw [reciprocal_reindex]
  let P : ℤ[X] := ∑ k ∈ range (N+1), C (a (N-k) : ℤ) * X^k
  have hc (i : ℕ) : P.coeff i = if i ≤ N then (a (N-i) : ℤ) else 0 :=
    expansion_coeff N (fun k => (a (N-k) : ℤ)) i
  have hd : P.natDegree = N := natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun i hi => by simp [hc, hi.not_ge])
    (by simp [hc, h0])
  have hm : P.Monic := by simp [Monic, leadingCoeff, hd, hc, h0]
  have hE : P.IsEisensteinAt (Ideal.span {(2 : ℤ)}) := by
    constructor
    · rw [hm.leadingCoeff, Ideal.mem_span_singleton]
      decide
    · intro i hi
      rw [hd] at hi
      rw [hc, if_pos hi.le, Ideal.mem_span_singleton]
      exact_mod_cast he (N-i) (Nat.sub_pos_of_lt hi) (Nat.sub_le N i)
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, hc, if_pos (Nat.zero_le _),
        Nat.sub_zero]
      norm_num1
      exact_mod_cast htop
  have hZ : Irreducible P := hE.irreducible
    (Ideal.isPrime_span_singleton_of_prime Int.prime_two) hm.isPrimitive (hd ▸ hpos)
  have hQ := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hm.isPrimitive).mp hZ
  simpa [P, Polynomial.map_sum] using hQ

theorem barrucand_irreducible_two_pow (r : ℕ) :
    let N := 2^r
    Irreducible (∑ k ∈ range (N+1), C (((N.choose k)^2 * (2*k).choose k : ℕ) : ℚ) * X^k) := by
  let N := 2^r
  have hN : 0 < N := pow_pos (by decide) r
  apply reciprocal_eisenstein_two N (fun k => (N.choose k)^2 * (2*k).choose k) hN
  · simp
  · simp only [Nat.choose_self, one_pow, one_mul]
    exact (Nat.choose_pos (by omega : N ≤ 2*N)).ne'
  · intro i hi _
    exact dvd_mul_of_dvd_right (Nat.two_dvd_centralBinom_of_one_le hi) _
  · simp only [Nat.choose_self, one_pow, one_mul]
    have hc := centralChoose_cast Nat.prime_two r
    change (((2*N).choose N : ℕ) : ZMod 4) = 2 at hc
    intro hd
    have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [hc] at hz
    exact (by decide : (2 : ZMod 4) ≠ 0) hz

end PrimePower

open PrimePower

/-- Prime powers still uncovered by the base-2 Wieferich test. -/
def H1 : Prop := ∀ p : ℕ, p.Prime → p ≠ 2 → 2 ^ (p - 1) ≡ 1 [MOD p ^ 2] →
  ∀ r : ℕ, Irreducible (OMA.S_oeis_a002893.g (p ^ (r + 1)))

/-- Degrees greater than one that are not powers of a prime. -/
def H2 : Prop := ∀ n : ℕ, 1 < n → (∀ p r : ℕ, p.Prime → n ≠ p ^ (r + 1)) →
  Irreducible (OMA.S_oeis_a002893.g n)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a002893.main := by
  intro h₁ h₂ n hn
  by_cases hone : n = 1
  · subst n
    simpa only [pow_zero, OMA.S_oeis_a002893.g] using barrucand_irreducible_two_pow 0
  by_cases hex : ∃ p r : ℕ, p.Prime ∧ n = p ^ (r + 1)
  · obtain ⟨p, r, hp, rfl⟩ := hex
    by_cases htwo : p = 2
    · subst p
      exact barrucand_irreducible_two_pow (r + 1)
    by_cases hw : 2 ^ (p - 1) ≡ 1 [MOD p ^ 2]
    · exact h₁ p hp htwo hw r
    · exact sun_primePower hp htwo hw r
  · exact h₂ n (by omega) (fun p r hp he => hex ⟨p, r, hp, he⟩)

end OMA.R_oeis_a002893_R1
