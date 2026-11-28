import OMAStatements.S_oeis_a246133

/-!
# Reduction of A246133 to its odd composite case

Credit: @Pampasgras

The target says: for `n > 3`, `n ^ 3 ∣ C(2n, n) - 2` if and only if `n` is prime.
This file proves everything that is known and leaves only the open part as hypotheses.

Proved here, with no hypothesis:
* `wolstenholme`: for a prime `p > 3`, `p ^ 3 ∣ C(2p, p) - 2` (Wolstenholme's theorem). This is the
  whole direction `n` prime → `a n = 0`.
* `even_case`: an even `n > 3` never satisfies the divisibility, because `C(2n, n)` is never `2`
  modulo `8` for even `n ≥ 2`.
* `three_pow_case`: a power `3 ^ k`, `k ≥ 2`, never satisfies it, because `C(2·3^k, 3^k) ≡ 20`
  modulo `27`.

Left open (the conjecture that no composite `n` has `a n = 0`, restricted to odd `n`):
* `H1`: prime powers `p ^ k` with `p ≥ 5`, `k ≥ 2`.
* `H2`: odd numbers with at least two distinct prime factors.

Proof of `wolstenholme`. Work in `ZMod (p ^ 3)`. With `F = (p-1)!` and `Q = ∏_{k=1}^{p-1} (p + k)` one
has `C(2p, p) * F = 2 * Q`. Reflecting `k ↦ p - k` gives `Q ^ 2 = ∏ (p + k) (2p - k)` and
`F ^ 2 = ∏ k (p - k)`. By Fermat, `(p + k) (2p - k) = k (p - k) (1 - 2 p^2 k^(p-3))` modulo `p ^ 3`.
Since `(2 p^2)^2 = 0`, the product of the last factors is `1 - 2 p^2 ∑ k^(p-3)`, and `p` divides the
power sum `∑_{k<p} k^(p-3)` because `0 < p - 3 < p - 1`. So `Q ^ 2 = F ^ 2`, hence `C(2p, p) ^ 2 = 4`,
and `C(2p, p) ≡ 2` modulo `p` (Lucas) selects the root `2`.
-/

namespace OMA.R_oeis_a246133_R1

open Finset

/-! ## Part 1: Wolstenholme's theorem -/

/-- First-order expansion of a product when `ε * ε = 0`. -/
theorem prod_one_sub_of_sq_zero {R ι : Type*} [CommRing R] (ε : R) (h : ε * ε = 0)
    (s : Finset ι) (b : ι → R) :
    ∏ k ∈ s, (1 - ε * b k) = 1 - ε * ∑ k ∈ s, b k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    linear_combination (b a * ∑ k ∈ s, b k) * h

/-- Power sums below `p - 1` vanish modulo `p`. -/
theorem dvd_sum_pow (p : ℕ) (hp : p.Prime) (i : ℕ) (hi0 : 0 < i) (hi : i < p - 1) :
    p ∣ ∑ k ∈ Ico 1 p, k ^ i := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have h := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) i (by rwa [ZMod.card])
  have h2 : ∑ k ∈ range p, ((k : ℕ) : ZMod p) ^ i = ∑ x : ZMod p, x ^ i := by
    refine Finset.sum_nbij' (fun k => (k : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
    · intro k _; exact Finset.mem_univ _
    · intro x _; exact Finset.mem_range.2 (ZMod.val_lt x)
    · intro k hk; exact ZMod.val_natCast_of_lt (Finset.mem_range.1 hk)
    · intro x _; exact ZMod.natCast_zmod_val x
    · intro k _; rfl
  rw [h, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hp.pos] at h2
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  simpa [hi0.ne'] using h2

/-- Fermat, lifted: `p ^ 2 * k ^ (p - 1) = p ^ 2` in `ZMod (p ^ 3)`. -/
theorem fermat_lift (p : ℕ) (hp : p.Prime) (k : ℕ) (hk1 : 1 ≤ k) (hkp : k < p) :
    (p : ZMod (p ^ 3)) ^ 2 * (k : ZMod (p ^ 3)) ^ (p - 1) = (p : ZMod (p ^ 3)) ^ 2 := by
  have hcop : Nat.Coprime k p := (Nat.coprime_of_lt_prime (by omega) hkp hp).symm
  have h1 : k ^ (p - 1) ≡ 1 [MOD p] := by
    have := Nat.ModEq.pow_totient hcop
    rwa [Nat.totient_prime hp] at this
  have hle : 1 ≤ k ^ (p - 1) := Nat.one_le_pow _ _ hk1
  have h2 : p ∣ k ^ (p - 1) - 1 := (Nat.modEq_iff_dvd' hle).1 h1.symm
  obtain ⟨t, ht⟩ := h2
  have h3 : k ^ (p - 1) = 1 + p * t := by omega
  have hp3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
    have := ZMod.natCast_self (p ^ 3)
    push_cast at this
    exact this
  have h4 : (k : ZMod (p ^ 3)) ^ (p - 1) = 1 + (p : ZMod (p ^ 3)) * (t : ZMod (p ^ 3)) := by
    have := congrArg (Nat.cast : ℕ → ZMod (p ^ 3)) h3
    push_cast at this
    exact this
  rw [h4]
  linear_combination (t : ZMod (p ^ 3)) * hp3

/-- `C(2(m+1), m+1) * m! = 2 * ∏_{k=1}^{m} (m + 1 + k)`. -/
theorem cb_mul_fact (m : ℕ) :
    Nat.centralBinom (m + 1) * m.factorial = 2 * ∏ k ∈ Ico 1 (m + 1), (m + 1 + k) := by
  have h1 := Nat.ascFactorial_eq_factorial_mul_choose (m + 1) (m + 1)
  rw [Nat.ascFactorial_eq_prod_range, Finset.prod_range_succ] at h1
  have h2 : ∏ k ∈ Ico 1 (m + 1), (m + 1 + k) = ∏ i ∈ range m, (m + 1 + 1 + i) := by
    rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    exact Finset.prod_congr rfl (fun i _ => by ring)
  have h3 : (m + 1 + (m + 1)).choose (m + 1) = Nat.centralBinom (m + 1) := by
    rw [Nat.centralBinom_eq_two_mul_choose, two_mul]
  rw [h3, Nat.factorial_succ] at h1
  rw [h2]
  have h4 : (m + 1) * (Nat.centralBinom (m + 1) * m.factorial) =
      (m + 1) * (2 * ∏ i ∈ range m, (m + 1 + 1 + i)) := by
    linarith
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) h4

/-- **Wolstenholme's theorem** for the central binomial coefficient. -/
theorem wolstenholme (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    p ^ 3 ∣ Nat.centralBinom p - 2 := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have h1p : 1 ≤ p := hp.one_le
  have hp3z : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
    have := ZMod.natCast_self (p ^ 3)
    push_cast at this
    exact this
  have hA : Nat.centralBinom p * (p - 1).factorial = 2 * ∏ k ∈ Ico 1 p, (p + k) := by
    have := cb_mul_fact (p - 1)
    rwa [Nat.sub_add_cancel h1p] at this
  have hQ' : ∏ k ∈ Ico 1 p, (p + (p - k)) = ∏ k ∈ Ico 1 p, (p + k) := by
    have := Finset.prod_Ico_reflect (fun j => p + j) 1 (m := p) (n := p) (Nat.le_succ p)
    simpa using this
  have hF : ∏ k ∈ Ico 1 p, k = (p - 1).factorial := by
    have := Finset.prod_Ico_id_eq_factorial (p - 1)
    rwa [Nat.sub_add_cancel h1p] at this
  have hF' : ∏ k ∈ Ico 1 p, (p - k) = (p - 1).factorial := by
    have := Finset.prod_Ico_reflect (fun j => j) 1 (m := p) (n := p) (Nat.le_succ p)
    rw [← hF]
    simpa using this
  obtain ⟨t, ht⟩ := dvd_sum_pow p hp (p - 3) (by omega) (by omega)
  have hterm : ∀ k ∈ Ico 1 p,
      ((p + k : ℕ) : ZMod (p ^ 3)) * ((p + (p - k) : ℕ) : ZMod (p ^ 3)) =
      ((k : ℕ) : ZMod (p ^ 3)) * ((p - k : ℕ) : ZMod (p ^ 3)) *
        (1 - 2 * (p : ZMod (p ^ 3)) ^ 2 * ((k : ℕ) : ZMod (p ^ 3)) ^ (p - 3)) := by
    intro k hk
    obtain ⟨hk1, hkp⟩ := Finset.mem_Ico.1 hk
    have hf := fermat_lift p hp k hk1 hkp
    have he : p - 1 = (p - 3) + 2 := by omega
    rw [he, pow_add] at hf
    push_cast [Nat.cast_sub hkp.le]
    linear_combination (-2) * hf + 2 * (k : ZMod (p ^ 3)) ^ (p - 3 + 1) * hp3z
  have e2 : ∏ k ∈ Ico 1 p,
      (1 - 2 * (p : ZMod (p ^ 3)) ^ 2 * ((k : ℕ) : ZMod (p ^ 3)) ^ (p - 3)) = 1 := by
    rw [prod_one_sub_of_sq_zero (2 * (p : ZMod (p ^ 3)) ^ 2)
      (by linear_combination (4 * (p : ZMod (p ^ 3))) * hp3z)]
    have hs : (∑ k ∈ Ico 1 p, ((k : ℕ) : ZMod (p ^ 3)) ^ (p - 3)) =
        (p : ZMod (p ^ 3)) * (t : ZMod (p ^ 3)) := by
      have := congrArg (Nat.cast : ℕ → ZMod (p ^ 3)) ht
      push_cast at this
      exact this
    rw [hs]
    linear_combination (-2 * (t : ZMod (p ^ 3))) * hp3z
  have hprod : ((∏ k ∈ Ico 1 p, (p + k) : ℕ) : ZMod (p ^ 3)) ^ 2 =
      (((p - 1).factorial : ℕ) : ZMod (p ^ 3)) ^ 2 := by
    have e1 : ((∏ k ∈ Ico 1 p, (p + k) : ℕ) : ZMod (p ^ 3)) ^ 2 =
        ∏ k ∈ Ico 1 p,
          (((p + k : ℕ) : ZMod (p ^ 3)) * ((p + (p - k) : ℕ) : ZMod (p ^ 3))) := by
      rw [Finset.prod_mul_distrib, ← Nat.cast_prod, ← Nat.cast_prod, hQ', sq]
    rw [e1, Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      ← Nat.cast_prod, ← Nat.cast_prod, hF, hF', e2]
    ring
  have hAR : ((Nat.centralBinom p : ℕ) : ZMod (p ^ 3)) *
      (((p - 1).factorial : ℕ) : ZMod (p ^ 3)) =
      2 * ((∏ k ∈ Ico 1 p, (p + k) : ℕ) : ZMod (p ^ 3)) := by
    have := congrArg (Nat.cast : ℕ → ZMod (p ^ 3)) hA
    push_cast at this ⊢
    exact this
  have hFunit : IsUnit (((p - 1).factorial : ℕ) : ZMod (p ^ 3)) := by
    rw [ZMod.isUnit_iff_coprime]
    refine Nat.Coprime.pow_right 3 ?_
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 (by rw [hp.dvd_factorial]; omega)).symm
  have hsq : ((Nat.centralBinom p : ℕ) : ZMod (p ^ 3)) ^ 2 = 4 := by
    have h : (((p - 1).factorial : ℕ) : ZMod (p ^ 3)) ^ 2 *
        ((Nat.centralBinom p : ℕ) : ZMod (p ^ 3)) ^ 2 =
        (((p - 1).factorial : ℕ) : ZMod (p ^ 3)) ^ 2 * 4 := by
      linear_combination
        (((Nat.centralBinom p : ℕ) : ZMod (p ^ 3)) * (((p - 1).factorial : ℕ) : ZMod (p ^ 3)) +
          2 * ((∏ k ∈ Ico 1 p, (p + k) : ℕ) : ZMod (p ^ 3))) * hAR + 4 * hprod
    exact (hFunit.pow 2).mul_left_cancel h
  have hmod : Nat.centralBinom p ≡ 2 [MOD p] := by
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 * p) (k := p) (p := p)
    rw [Nat.mul_mod_left, Nat.mod_self, Nat.mul_div_cancel _ hp.pos, Nat.div_self hp.pos] at h
    rw [Nat.centralBinom_eq_two_mul_choose]
    simpa using h
  have h2le : 2 ≤ Nat.centralBinom p := Nat.two_le_centralBinom p hp.pos
  have hdvd : p ∣ Nat.centralBinom p - 2 := (Nat.modEq_iff_dvd' h2le).1 hmod.symm
  have hnd : ¬ p ∣ Nat.centralBinom p + 2 := by
    intro h
    have h4 : p ∣ 4 := by
      have := Nat.dvd_sub h hdvd
      have e : Nat.centralBinom p + 2 - (Nat.centralBinom p - 2) = 4 := by omega
      rwa [e] at this
    have hle := Nat.le_of_dvd (by norm_num) h4
    have h4' : p = 4 := by omega
    rw [h4'] at hp
    exact absurd hp (by norm_num)
  have hunit2 : IsUnit ((Nat.centralBinom p + 2 : ℕ) : ZMod (p ^ 3)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right 3 ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm
  have hz : ((Nat.centralBinom p - 2 : ℕ) : ZMod (p ^ 3)) = 0 := by
    have h : ((Nat.centralBinom p + 2 : ℕ) : ZMod (p ^ 3)) *
        ((Nat.centralBinom p - 2 : ℕ) : ZMod (p ^ 3)) =
        ((Nat.centralBinom p + 2 : ℕ) : ZMod (p ^ 3)) * 0 := by
      push_cast [Nat.cast_sub h2le]
      linear_combination hsq
    exact hunit2.mul_left_cancel h
  exact (ZMod.natCast_eq_zero_iff _ _).1 hz

/-! ## Part 2: the even case -/

/-- `C(4m, 2m) * D(m)^2 = C(2m, m) * D(2m)`, where `D(m)` is the product of the first `m` odd numbers. -/
theorem cb_double (m : ℕ) :
    Nat.centralBinom (2 * m) * (∏ i ∈ range m, (2 * i + 1)) ^ 2 =
      Nat.centralBinom m * ∏ i ∈ range (2 * m), (2 * i + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := Nat.succ_mul_centralBinom_succ (2 * m + 1)
    have h2 := Nat.succ_mul_centralBinom_succ (2 * m)
    have h3 := Nat.succ_mul_centralBinom_succ m
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_succ]
    generalize (∏ i ∈ range m, (2 * i + 1)) = D at ih ⊢
    generalize (∏ i ∈ range (2 * m), (2 * i + 1)) = E at ih ⊢
    generalize Nat.centralBinom (2 * m + 1 + 1) = A at h1 ⊢
    generalize Nat.centralBinom (2 * m + 1) = B at h1 h2
    generalize Nat.centralBinom (2 * m) = C at h2 ih
    generalize Nat.centralBinom (m + 1) = c1 at h3 ⊢
    generalize Nat.centralBinom m = c0 at h3 ih
    apply Nat.eq_of_mul_eq_mul_left (show 0 < (2 * m + 2) * (2 * m + 1) by positivity)
    zify at h1 h2 h3 ih ⊢
    linear_combination (2 * (m : ℤ) + 1) ^ 3 * (D : ℤ) ^ 2 * h1 +
      2 * (4 * (m : ℤ) + 3) * (2 * (m : ℤ) + 1) ^ 2 * (D : ℤ) ^ 2 * h2 +
      4 * (4 * (m : ℤ) + 3) * (4 * (m : ℤ) + 1) * (2 * (m : ℤ) + 1) ^ 2 * ih -
      2 * (2 * (m : ℤ) + 1) * (E : ℤ) * (4 * (m : ℤ) + 1) * (4 * (m : ℤ) + 3) * h3

theorem odd_prod_odd (m : ℕ) : Odd (∏ i ∈ range m, (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.prod_range_succ]; exact ih.mul ⟨m, rfl⟩

theorem odd_sq_mod_eight (x : ℕ) (hx : Odd x) : x ^ 2 % 8 = 1 := by
  have h8 : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by
    obtain ⟨y, rfl⟩ := hx
    omega
  rcases h8 with h | h | h | h <;> simp [Nat.pow_mod, h]

theorem prod_odd_four (j : ℕ) : (∏ i ∈ range (4 * j), (2 * i + 1)) % 8 = 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 4 * (j + 1) = 4 * j + 1 + 1 + 1 + 1 by ring, Finset.prod_range_succ,
      Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
    have h0 : (∏ i ∈ range (4 * j), (2 * i + 1)) ≡ 1 [MOD 8] := ih
    have ha : 2 * (4 * j) + 1 ≡ 1 [MOD 8] := by unfold Nat.ModEq; omega
    have hb : 2 * (4 * j + 1) + 1 ≡ 3 [MOD 8] := by unfold Nat.ModEq; omega
    have hc : 2 * (4 * j + 1 + 1) + 1 ≡ 5 [MOD 8] := by unfold Nat.ModEq; omega
    have hd : 2 * (4 * j + 1 + 1 + 1) + 1 ≡ 7 [MOD 8] := by unfold Nat.ModEq; omega
    exact (((h0.mul ha).mul hb).mul hc).mul hd

theorem prod_odd_four_add_two (j : ℕ) : (∏ i ∈ range (4 * j + 2), (2 * i + 1)) % 8 = 3 := by
  rw [show 4 * j + 2 = 4 * j + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ]
  have h0 : (∏ i ∈ range (4 * j), (2 * i + 1)) ≡ 1 [MOD 8] := prod_odd_four j
  have ha : 2 * (4 * j) + 1 ≡ 1 [MOD 8] := by unfold Nat.ModEq; omega
  have hb : 2 * (4 * j + 1) + 1 ≡ 3 [MOD 8] := by unfold Nat.ModEq; omega
  exact (h0.mul ha).mul hb

theorem four_dvd_cb_odd (j : ℕ) (hj : 1 ≤ j) : 4 ∣ Nat.centralBinom (2 * j + 1) := by
  have h := Nat.succ_mul_centralBinom_succ (2 * j)
  obtain ⟨e, he⟩ := Nat.two_dvd_centralBinom_of_one_le (n := 2 * j) (by omega)
  have h4 : 4 ∣ Nat.centralBinom (2 * j + 1) * (2 * j + 1) := by
    refine ⟨(2 * (2 * j) + 1) * e, ?_⟩
    rw [mul_comm, h, he]
    ring
  have hc : Nat.Coprime 4 (2 * j + 1) := by
    have : Nat.Coprime (2 ^ 2) (2 * j + 1) := (Nat.coprime_two_left.2 ⟨j, rfl⟩).pow_left 2
    simpa using this
  exact hc.dvd_of_dvd_mul_right h4

/-- The central binomial coefficient at an even positive argument is never `2` modulo `8`. -/
theorem cb_even_mod_eight : ∀ m : ℕ, 1 ≤ m → Nat.centralBinom (2 * m) % 8 ≠ 2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hdbl := cb_double m
    have hD : ((∏ i ∈ range m, (2 * i + 1)) ^ 2) % 8 = 1 :=
      odd_sq_mod_eight _ (odd_prod_odd m)
    have key : Nat.centralBinom (2 * m) % 8 =
        (Nat.centralBinom m * ∏ i ∈ range (2 * m), (2 * i + 1)) % 8 := by
      rw [← hdbl, Nat.mul_mod, hD, mul_one, Nat.mod_mod]
    rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
    · have hE : (∏ i ∈ range (2 * (2 * j)), (2 * i + 1)) % 8 = 1 := by
        rw [show 2 * (2 * j) = 4 * j by ring]
        exact prod_odd_four j
      rw [Nat.mul_mod, hE, mul_one, Nat.mod_mod] at key
      rw [key]
      exact ih j (by omega) (by omega)
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · decide
      · have hE : (∏ i ∈ range (2 * (2 * j + 1)), (2 * i + 1)) % 8 = 3 := by
          rw [show 2 * (2 * j + 1) = 4 * j + 2 by ring]
          exact prod_odd_four_add_two j
        have h4 := four_dvd_cb_odd j hj
        rw [Nat.mul_mod, hE] at key
        omega

theorem even_case (n : ℕ) (hn : 3 < n) (he : Even n) : ¬ n ^ 3 ∣ Nat.centralBinom n - 2 := by
  obtain ⟨m, hm⟩ := he
  have hm' : n = 2 * m := by omega
  subst hm'
  intro h
  have h8 : 8 ∣ (2 * m) ^ 3 := ⟨m ^ 3, by ring⟩
  have h8' : 8 ∣ Nat.centralBinom (2 * m) - 2 := h8.trans h
  have h2 := Nat.two_le_centralBinom (2 * m) (by omega)
  have := cb_even_mod_eight m (by omega)
  omega

/-! ## Part 3: powers of three -/

/-- `C(6m, 3m) * P(m)^2 = C(2m, m) * P(2m)`, where `P(m) = ∏_{i<m} (3i+1)(3i+2)` is the product of the
numbers below `3m` that are prime to `3`. -/
theorem cb_triple (m : ℕ) :
    Nat.centralBinom (3 * m) * (∏ i ∈ range m, ((3 * i + 1) * (3 * i + 2))) ^ 2 =
      Nat.centralBinom m * ∏ i ∈ range (2 * m), ((3 * i + 1) * (3 * i + 2)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := Nat.succ_mul_centralBinom_succ (3 * m + 1 + 1)
    have h2 := Nat.succ_mul_centralBinom_succ (3 * m + 1)
    have h3 := Nat.succ_mul_centralBinom_succ (3 * m)
    have h4 := Nat.succ_mul_centralBinom_succ m
    rw [show 3 * (m + 1) = 3 * m + 1 + 1 + 1 by ring, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
      Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
    generalize (∏ i ∈ range m, ((3 * i + 1) * (3 * i + 2))) = P at ih ⊢
    generalize (∏ i ∈ range (2 * m), ((3 * i + 1) * (3 * i + 2))) = Q at ih ⊢
    generalize Nat.centralBinom (3 * m + 1 + 1 + 1) = A3 at h1 ⊢
    generalize Nat.centralBinom (3 * m + 1 + 1) = A2 at h1 h2
    generalize Nat.centralBinom (3 * m + 1) = A1 at h2 h3
    generalize Nat.centralBinom (3 * m) = A0 at h3 ih
    generalize Nat.centralBinom (m + 1) = c1 at h4 ⊢
    generalize Nat.centralBinom m = c0 at h4 ih
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 3 * m + 1 + 1 + 1 by positivity)
    zify at h1 h2 h3 h4 ih ⊢
    linear_combination
      (P : ℤ) ^ 2 * (3 * (m : ℤ) + 1) ^ 2 * (3 * (m : ℤ) + 2) ^ 2 * h1 +
      2 * (6 * (m : ℤ) + 5) * (P : ℤ) ^ 2 * (3 * (m : ℤ) + 1) ^ 2 * (3 * (m : ℤ) + 2) * h2 +
      4 * (6 * (m : ℤ) + 5) * (6 * (m : ℤ) + 3) * (P : ℤ) ^ 2 * (3 * (m : ℤ) + 1) *
        (3 * (m : ℤ) + 2) * h3 +
      8 * (6 * (m : ℤ) + 5) * (6 * (m : ℤ) + 3) * (6 * (m : ℤ) + 1) * (3 * (m : ℤ) + 1) *
        (3 * (m : ℤ) + 2) * ih -
      3 * (Q : ℤ) * (6 * (m : ℤ) + 1) * (6 * (m : ℤ) + 2) * (6 * (m : ℤ) + 4) *
        (6 * (m : ℤ) + 5) * h4

/-- Nine consecutive integers: the six that are prime to `3` multiply to `-1` modulo `27`. -/
theorem block_mod : ∀ y : ZMod 27,
    (9 * y + 1) * (9 * y + 2) * ((9 * y + 4) * (9 * y + 5)) * ((9 * y + 7) * (9 * y + 8)) = -1 := by
  decide

theorem prod_three_block (j : ℕ) :
    ((∏ i ∈ range (3 * j), ((3 * i + 1) * (3 * i + 2)) : ℕ) : ZMod 27) = (-1) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 3 * (j + 1) = 3 * j + 1 + 1 + 1 by ring, Finset.prod_range_succ,
      Finset.prod_range_succ, Finset.prod_range_succ, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, ih,
      pow_succ]
    have hb := block_mod (j : ZMod 27)
    push_cast
    linear_combination (-1 : ZMod 27) ^ j * hb

/-- `C(18m, 9m) ≡ C(6m, 3m)` modulo `27`. -/
theorem cb_nine_mod (m : ℕ) :
    ((Nat.centralBinom (3 * (3 * m)) : ℕ) : ZMod 27) =
      ((Nat.centralBinom (3 * m) : ℕ) : ZMod 27) := by
  have h0 := cb_triple (3 * m)
  rw [show 2 * (3 * m) = 3 * (2 * m) by ring] at h0
  have h := congrArg (Nat.cast : ℕ → ZMod 27) h0
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, prod_three_block m, prod_three_block (2 * m)] at h
  have e1 : ((-1 : ZMod 27) ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    simp
  have e2 : (-1 : ZMod 27) ^ (2 * m) = 1 := by
    rw [pow_mul]
    simp
  rw [e1, e2, mul_one, mul_one] at h
  exact h

theorem cb_three_pow_mod (k : ℕ) (hk : 1 ≤ k) :
    ((Nat.centralBinom (3 ^ k) : ℕ) : ZMod 27) = 20 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · rw [show Nat.centralBinom (3 ^ (0 + 1)) = 20 by decide]
      norm_num
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have h9 := cb_nine_mod (3 ^ j)
      rw [show 3 ^ (j + 1 + 1) = 3 * (3 * 3 ^ j) by ring, h9, show 3 * 3 ^ j = 3 ^ (j + 1) by ring]
      exact ih (by omega)

/-- No power `3 ^ k` with `k ≥ 2` satisfies the divisibility: `C(2·3^k, 3^k) ≡ 20` modulo `27`. -/
theorem three_pow_case (k : ℕ) (hk : 2 ≤ k) :
    ¬ (3 ^ k) ^ 3 ∣ Nat.centralBinom (3 ^ k) - 2 := by
  intro h
  have h27 : 27 ∣ (3 ^ k) ^ 3 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact ⟨(3 ^ j) ^ 3, by ring⟩
  have hd : 27 ∣ Nat.centralBinom (3 ^ k) - 2 := h27.trans h
  have h2 := Nat.two_le_centralBinom (3 ^ k) (by positivity)
  have hz : ((Nat.centralBinom (3 ^ k) - 2 : ℕ) : ZMod 27) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hd
  rw [Nat.cast_sub h2, cb_three_pow_mod k (by omega)] at hz
  push_cast at hz
  revert hz
  decide

/-! ## The reduction -/

/-- Open: a prime power `p ^ k` with `p ≥ 5` and `k ≥ 2` never satisfies the divisibility.
(By the Jacobsthal-Kazandzidis congruence, not formalized here, this is the statement that no prime
`p ≥ 5` has `p ^ 6 ∣ C(2p, p) - 2`.) -/
def H1 : Prop :=
  ∀ p k : ℕ, p.Prime → 5 ≤ p → 2 ≤ k → ¬ (p ^ k) ^ 3 ∣ Nat.centralBinom (p ^ k) - 2

/-- Open: an odd number with at least two distinct prime factors never satisfies the divisibility. -/
def H2 : Prop :=
  ∀ n : ℕ, Odd n → 1 < n → ¬ IsPrimePow n → ¬ n ^ 3 ∣ Nat.centralBinom n - 2

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a246133.main := by
  intro h1 h2 n hn
  have key : OMA.S_oeis_a246133.a n = 0 ↔ n ^ 3 ∣ Nat.centralBinom n - 2 := by
    unfold OMA.S_oeis_a246133.a
    exact ⟨Nat.dvd_of_mod_eq_zero, Nat.mod_eq_zero_of_dvd⟩
  rw [key]
  constructor
  · intro hd
    by_contra hnp
    rcases Nat.even_or_odd n with he | ho
    · exact even_case n hn he hd
    · by_cases hpp : IsPrimePow n
      · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
        have hp2 : p ≠ 2 := by
          rintro rfl
          exact (Nat.not_even_iff_odd.2 ho) (Nat.even_pow.2 ⟨even_two, hk.ne'⟩)
        have hk2 : 2 ≤ k := by
          by_contra hlt
          have hk1 : k = 1 := by omega
          rw [hk1, pow_one] at hnp
          exact hnp hp
        by_cases hp3 : p = 3
        · rw [hp3] at hd
          exact three_pow_case k hk2 hd
        · have hp5 : 5 ≤ p := by
            have h2le := hp.two_le
            by_contra hlt
            have hp4 : p = 4 := by omega
            rw [hp4] at hp
            exact absurd hp (by norm_num)
          exact h1 p k hp hp5 hk2 hd
      · exact h2 n ho (by omega) hpp hd
  · intro hp
    exact wolstenholme n hp hn

end OMA.R_oeis_a246133_R1
