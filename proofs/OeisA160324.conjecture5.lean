import FormalConjectures.OEIS.«160324»
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum.Prime

/-! Disproof of a conjecture of Zhi-Wei Sun on three consecutive polygonal orders.
Credit: @cjchaffin, with Codex (GPT-6.2 Astra).
For m = 33 the witnesses (1019^(160k+2) - 392089) / 35904 are unbounded.
A prime divisor with odd multiplicity obstructs a representation by the three orders. -/

open scoped BigOperators

namespace A160324Disproof

private theorem inert_dvd_components {q u v : ℕ} (hq : q.Prime)
    (hq8 : q % 8 = 5 ∨ q % 8 = 7) (hd : q ∣ v ^ 2 + 2 * u ^ 2) :
    q ∣ u ∧ q ∣ v := by
  let : Fact q.Prime := ⟨hq⟩
  have hq₂ : q ≠ 2 := by omega
  have hz := (ZMod.natCast_eq_zero_iff (v ^ 2 + 2 * u ^ 2) q).mpr hd
  push_cast at hz
  have hu : (u : ZMod q) = 0 := by
    by_contra h
    have hnot : ¬ IsSquare (-2 : ZMod q) := by
      rw [ZMod.exists_sq_eq_neg_two_iff hq₂]
      omega
    apply hnot
    refine ⟨(v : ZMod q) / u, ?_⟩
    rw [← pow_two, div_pow]
    symm
    apply (div_eq_iff (pow_ne_zero 2 h)).mpr
    linear_combination hz
  have hv : (v : ZMod q) = 0 := by
    rw [hu, zero_pow (by decide), mul_zero, add_zero] at hz
    rw [pow_two, mul_eq_zero] at hz
    exact hz.elim id id
  exact ⟨(ZMod.natCast_eq_zero_iff u q).mp hu, (ZMod.natCast_eq_zero_iff v q).mp hv⟩

theorem norm_even_factor {q : ℕ} (hq : q.Prime) (hq8 : q % 8 = 5 ∨ q % 8 = 7)
    {u v : ℕ} (hn : 0 < v ^ 2 + 2 * u ^ 2) :
    Even ((v ^ 2 + 2 * u ^ 2).factorization q) := by
  generalize hN : v ^ 2 + 2 * u ^ 2 = N at hn ⊢
  induction N using Nat.strong_induction_on generalizing u v with
  | h N ih =>
    by_cases hd : q ∣ N
    · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := inert_dvd_components hq hq8 (hN.symm ▸ hd)
      have hEq : N = q ^ 2 * (b ^ 2 + 2 * a ^ 2) := by
        rw [← hN, ha, hb]
        ring
      have hpos : 0 < b ^ 2 + 2 * a ^ 2 := by
        have hp := Nat.pos_of_ne_zero (show b ^ 2 + 2 * a ^ 2 ≠ 0 by
          intro h; rw [hEq, h, mul_zero] at hn; omega)
        exact hp
      have hLt : b ^ 2 + 2 * a ^ 2 < N := by
        rw [hEq]
        have hq2 : 1 < q ^ 2 := by have := hq.two_le; nlinarith
        simpa using Nat.mul_lt_mul_of_pos_right hq2 hpos
      have he := ih (b ^ 2 + 2 * a ^ 2) hLt (u := a) (v := b) rfl hpos
      rw [hEq, Nat.factorization_mul (pow_ne_zero 2 hq.ne_zero) hpos.ne',
        Finsupp.add_apply, Nat.factorization_pow_self hq]
      exact (by decide : Even (2 : ℕ)).add he
    · rw [Nat.factorization_eq_zero_of_not_dvd hd]
      decide

theorem inert_prime_of_mod_eight {a : ℕ} (ha : a % 8 = 5) :
    ∃ q, q.Prime ∧ q ∣ a ∧ (q % 8 = 5 ∨ q % 8 = 7) ∧ ¬ Even (a.factorization q) := by
  by_contra! h
  have ha₀ : a ≠ 0 := by omega
  have ha₁ : a % 2 = 1 := by omega
  have hc : ZMod.χ₈' a = (-1 : ℤ) := by
    rw [ZMod.χ₈'_nat_eq_if_mod_eight, ha, ha₁]
    decide
  have hprod : ZMod.χ₈' a =
      ∏ q ∈ a.primeFactors, ZMod.χ₈' (q : ZMod 8) ^ a.factorization q := by
    nth_rw 1 [Nat.prod_primeFactors_pow_factorization ha₀]
    simp only [Nat.cast_prod, Nat.cast_pow, map_prod, map_pow]
  have hOne : (∏ q ∈ a.primeFactors, ZMod.χ₈' (q : ZMod 8) ^ a.factorization q) = 1 := by
    apply Finset.prod_eq_one
    intro q hq
    have hqp := (Nat.mem_primeFactors.mp hq).1
    have hd := (Nat.mem_primeFactors.mp hq).2.1
    have hq₁ : q % 2 = 1 := by
      by_contra! he
      have hdiv : 2 ∣ q := by omega
      have hdivA := hdiv.trans hd
      omega
    rw [ZMod.χ₈'_nat_eq_if_mod_eight, hq₁, if_neg (by decide)]
    split_ifs with hg
    · simp
    · have hq8 : q % 8 = 5 ∨ q % 8 = 7 := by omega
      obtain ⟨t, ht⟩ := h q hqp hd hq8
      rw [ht, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [hprod, hOne] at hc
  omega

theorem no_norm_product {a b u v e : ℕ} (ha : a % 8 = 5) (hb : 0 < b)
    (hn : 0 < v ^ 2 + 2 * u ^ 2) (hs : a + 2 * b = 1019 ^ e) :
    a * b ≠ 17 * (v ^ 2 + 2 * u ^ 2) := by
  intro hprod
  obtain ⟨q, hq, hqa, hq8, ho⟩ := inert_prime_of_mod_eight ha
  have hq₁ : q ≠ 1 := hq.ne_one
  have h17 : ¬ q ∣ 17 := by
    intro h
    have he := ((by decide : Nat.Prime 17).dvd_iff_eq hq₁).mp h
    omega
  have hqb : ¬q ∣ b := by
    intro h
    have hd : q ∣ 1019 ^ e := by
      rw [← hs]
      exact dvd_add hqa (h.trans (dvd_mul_left _ _))
    have hdiv := hq.dvd_of_dvd_pow hd
    have he := ((by norm_num : Nat.Prime 1019).dvd_iff_eq hq₁).mp hdiv
    omega
  have hfact := congrArg (fun x : ℕ => x.factorization q) hprod
  have ha₀ : a ≠ 0 := by omega
  rw [Nat.factorization_mul ha₀ hb.ne', Nat.factorization_mul (by decide) hn.ne',
    Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hqb,
    Nat.factorization_eq_zero_of_not_dvd h17, add_zero, zero_add] at hfact
  exact ho (hfact.symm ▸ norm_even_factor hq hq8 hn)

end A160324Disproof

/- An unbounded family of obstructions for polygonal orders 34, 35, and 36. -/

open Filter

namespace A160324Disproof

private theorem twice_polygonal (k x : ℕ) (hk : 2 ≤ k) :
    2 * (OeisA160324.polygonalNumber k x : ℤ) =
      ((k : ℤ) - 2) * (x : ℤ) * ((x : ℤ) - 1) + 2 * (x : ℤ) := by
  cases x with
  | zero => simp [OeisA160324.polygonalNumber]
  | succ x =>
    have hd := Nat.mul_div_cancel' (x + 1).even_mul_pred_self.two_dvd
    have hf := congrArg (fun n : ℕ => (n : ℤ)) hd
    push_cast [Nat.cast_sub (show 1 ≤ x + 1 by omega)] at hf
    unfold OeisA160324.polygonalNumber
    push_cast [Nat.cast_sub hk]
    linear_combination ((k : ℤ) - 2) * hf

private def rootValue (k : ℕ) := 1019 ^ (80 * k + 1)

private def witness (k : ℕ) := (rootValue k ^ 2 - 392089) / 35904

private theorem root_congruence (k : ℕ) : rootValue k ≡ 1019 [MOD 35904] := by
  have h : (1019 : ℕ) ^ 80 ≡ 1 [MOD 35904] := by decide
  unfold rootValue
  rw [pow_succ, pow_mul]
  simpa only [one_pow, one_mul] using (h.pow k).mul (Nat.ModEq.refl (1019 : ℕ))

private theorem root_lower (k : ℕ) : 1019 ≤ rootValue k := by
  unfold rootValue
  rw [pow_succ]
  exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))

private theorem witness_equation (k : ℕ) :
    rootValue k ^ 2 = 392089 + 35904 * witness k := by
  have hr := root_lower k
  have hbound : 392089 ≤ rootValue k ^ 2 := by nlinarith
  have hmod : 392089 ≡ rootValue k ^ 2 [MOD 35904] :=
    (by decide : 392089 ≡ 1019 ^ 2 [MOD 35904]).trans ((root_congruence k).pow 2).symm
  have hd := (Nat.modEq_iff_dvd' hbound).mp hmod
  have he := Nat.mul_div_cancel' hd
  unfold witness
  omega

private theorem root_mod_sixteen (k : ℕ) : ((rootValue k : ℤ) % 16) = 11 := by
  have h := (root_congruence k).of_dvd (by decide : (16 : ℕ) ∣ 35904)
  have hh : rootValue k % 16 = (11 : ℕ) := h
  exact_mod_cast hh

private theorem witness_no_representation (k x y z : ℕ) :
    witness k ≠ OeisA160324.polygonalNumber 34 x +
      OeisA160324.polygonalNumber 35 y + OeisA160324.polygonalNumber 36 z := by
  intro h
  let s : ℤ := rootValue k
  let t : ℤ := 544 * ((x : ℤ) + z) - 511
  let u : ℤ := 32 * (x : ℤ) - 34 * (z : ℤ) + 1
  let v : ℤ := 66 * (y : ℤ) - 31
  have hn := congrArg (fun n : ℕ => (n : ℤ)) h
  push_cast at hn
  have hsum : 2 * (witness k : ℤ) =
      32 * (x : ℤ) * ((x : ℤ) - 1) + 2 * (x : ℤ) +
      (33 * (y : ℤ) * ((y : ℤ) - 1) + 2 * (y : ℤ)) +
      (34 * (z : ℤ) * ((z : ℤ) - 1) + 2 * (z : ℤ)) := by
    have hx := twice_polygonal 34 x (by decide)
    have hy := twice_polygonal 35 y (by decide)
    have hz := twice_polygonal 36 z (by decide)
    norm_num at hx hy hz
    linear_combination 2 * hn + hx + hy + hz
  have hsq : s ^ 2 = 392089 + 35904 * (witness k : ℤ) := by
    dsimp [s]
    exact_mod_cast witness_equation k
  have hnorm : (s - t) * (s + t) = 136 * (v ^ 2 + 2 * u ^ 2) := by
    dsimp [t, u, v]
    linear_combination hsq + 17952 * hsum
  have hv : v ≠ 0 := by dsimp [v]; omega
  have hNpos : 0 < v ^ 2 + 2 * u ^ 2 := by nlinarith [sq_pos_of_ne_zero hv, sq_nonneg u]
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1019) (root_lower k))
  have hpos : 0 < s - t ∧ 0 < s + t := by
    have hpp : 0 < (s - t) * (s + t) := by rw [hnorm]; positivity
    rcases mul_pos_iff.mp hpp with hh | hh
    · exact hh
    · exfalso; linarith [hh.1, hh.2]
  let A := (s - t) / 2
  let B := (s + t) / 4
  have hsm : s % 16 = 11 := root_mod_sixteen k
  have htm : t % 16 = 1 := by dsimp [t]; omega
  have hA : 2 * A = s - t := by dsimp [A]; omega
  have hB : 4 * B = s + t := by dsimp [B]; omega
  have hAmod : A % 8 = 5 := by dsimp [A]; omega
  have hAz : 0 < A := by omega
  have hBz : 0 < B := by omega
  have hAB : A * B = 17 * (v ^ 2 + 2 * u ^ 2) := by
    have he : 8 * (A * B) = 8 * (17 * (v ^ 2 + 2 * u ^ 2)) := by
      linear_combination hnorm + (s + t) * hA + 2 * A * hB
    exact mul_left_cancel₀ (by decide : (8 : ℤ) ≠ 0) he
  have hNatA : (A.toNat : ℤ) = A := Int.toNat_of_nonneg hAz.le
  have hNatB : (B.toNat : ℤ) = B := Int.toNat_of_nonneg hBz.le
  have ha₈ : A.toNat % 8 = 5 := by
    have hf : ((A.toNat : ℤ) % 8) = 5 := by rw [hNatA]; exact hAmod
    exact_mod_cast hf
  have hb₀ : 0 < B.toNat := by
    have hf : (0 : ℤ) < (B.toNat : ℤ) := by rw [hNatB]; exact hBz
    exact_mod_cast hf
  have hn_cast : ((v.natAbs ^ 2 + 2 * u.natAbs ^ 2 : ℕ) : ℤ) =
      v ^ 2 + 2 * u ^ 2 := by
    push_cast
    rw [sq_abs, sq_abs]
  have hN₀ : 0 < v.natAbs ^ 2 + 2 * u.natAbs ^ 2 := by
    have hf : 0 < ((v.natAbs ^ 2 + 2 * u.natAbs ^ 2 : ℕ) : ℤ) := by rw [hn_cast]; exact hNpos
    exact_mod_cast hf
  have hsumN : A.toNat + 2 * B.toNat = 1019 ^ (80 * k + 1) := by
    have hs' : A + 2 * B = (1019 ^ (80 * k + 1) : ℕ) := by change A + 2 * B = s; omega
    rw [← hNatA, ← hNatB] at hs'
    exact_mod_cast hs'
  have hprodN : A.toNat * B.toNat = 17 * (v.natAbs ^ 2 + 2 * u.natAbs ^ 2) := by
    apply Int.ofNat.inj
    change ((A.toNat * B.toNat : ℕ) : ℤ) =
      ((17 * (v.natAbs ^ 2 + 2 * u.natAbs ^ 2) : ℕ) : ℤ)
    rw [Nat.cast_mul, Nat.cast_mul, hNatA, hNatB, hn_cast]
    exact hAB
  exact no_norm_product ha₈ hb₀ hN₀ hsumN hprodN

private theorem witnesses_unbounded (N : ℕ) : ∃ k, N ≤ witness k := by
  let k := 392089 + 35904 * N + 1
  have hpow : 80 * k + 1 < rootValue k := by
    unfold rootValue
    exact Nat.lt_pow_self (by decide)
  have hs : 0 < rootValue k := by omega
  have hsq : rootValue k ≤ rootValue k ^ 2 := by
    simpa only [pow_two] using Nat.le_mul_of_pos_left (rootValue k) hs
  have he := witness_equation k
  have hr : 392089 + 35904 * N < rootValue k := by
    have hk : 392089 + 35904 * N < 80 * k + 1 := by dsimp [k]; omega
    exact hk.trans hpow
  refine ⟨k, ?_⟩
  omega

end A160324Disproof

theorem OMA.disproof : ¬ (type_of% @OeisA160324.conjecture5) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h 33 (by decide))
  obtain ⟨k, hk⟩ := A160324Disproof.witnesses_unbounded N
  obtain ⟨x, y, z, hr⟩ := hN (A160324Disproof.witness k) hk
  exact A160324Disproof.witness_no_representation k x y z hr
