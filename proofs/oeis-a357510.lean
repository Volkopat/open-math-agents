import OMAStatements.S_oeis_a357510
import Mathlib

/-!
# Proof of the conjecture of OEIS A357510 (Peter Bala, Oct 01 2022)

`a(n) = Sum_{k = 0..n} k * binomial(n,k)^2 * binomial(n+k,k)^2`, and the claim is
`a(p-1) == 0 (mod p^4)` for every prime `p >= 5`.

## Proof

Put `T_k = C(p-1,k) * C(p-1+k,k)`. For all `n`, `m` the integer identity

  `((m+1)!)^2 * C(n,m+1) * C(n+m+1,m+1) = (n+1) * (n-m) * prod_{i<m} ((n+1)^2 - (i+1)^2)`

holds (induction on `m`). With `n = p - 1` and `k = m + 1 < p` the right side is divisible by `p` and
`(k!)^2` is not, so `T_k = p * b_k` and `(k!)^2 * b_k = (p-k) * prod_{i<k-1} (p^2 - (i+1)^2)`.
Modulo `p^2` the product is `(-1)^(k-1) * ((k-1)!)^2`; cancelling the unit `((k-1)!)^2` and squaring
gives `k^4 * b_k^2 = (p-k)^2 = k^2 - 2*p*k`, hence `k * b_k^2 = 1/k - 2*p/k^2` in `ZMod (p^2)`.

In `ZMod (p^2)`, `1/k + 1/(p-k) = -p/k^2`, so the reflection `k -> p-k` gives
`2 * sum_{k=1}^{p-1} 1/k = -p * sum_{k=1}^{p-1} 1/k^2`. In `ZMod p` the sum of `1/k^2` over the
nonzero residues is `0` for `p >= 5` (`x -> 2*x` permutes them and `3` is invertible), so
`p * sum 1/k^2 = 0` in `ZMod (p^2)`. Therefore `2 * sum_{k=1}^{p-1} k * b_k^2 = -5 * p * sum 1/k^2 = 0`
in `ZMod (p^2)`, and `2` is a unit: `p^2` divides `sum_{k=1}^{p-1} k * b_k^2`. Finally
`a(p-1) = sum_k k * T_k^2 = p^2 * sum_{k=1}^{p-1} k * b_k^2` is divisible by `p^4`.
-/

/-- `((m+1)!)^2 * C(n,m+1) * C(n+m+1,m+1) = (n+1) * (n-m) * prod_{i<m} ((n+1)^2 - (i+1)^2)` in the
integers, for all `n` and `m`. -/
private lemma fact_sq_mul_choose (n m : ℕ) :
    ((m + 1).factorial : ℤ) ^ 2 * (n.choose (m + 1) : ℤ) * ((n + (m + 1)).choose (m + 1) : ℤ) =
      ((n : ℤ) + 1) * ((n : ℤ) - m) *
        ∏ i ∈ Finset.range m, (((n : ℤ) + 1) ^ 2 - ((i : ℤ) + 1) ^ 2) := by
  induction m with
  | zero =>
    simp only [zero_add, Nat.factorial_one, Nat.choose_one_right, Finset.range_zero,
      Finset.prod_empty]
    push_cast
    ring
  | succ m ih =>
    have h1 : (n.choose (m + 1 + 1) : ℤ) * ((m : ℤ) + 2) =
        (n.choose (m + 1) : ℤ) * ((n : ℤ) - ((m : ℤ) + 1)) := by
      rcases Nat.lt_or_ge n (m + 1) with h | h
      · rw [Nat.choose_eq_zero_of_lt (show n < m + 1 + 1 by omega), Nat.choose_eq_zero_of_lt h]
        simp
      · have hc := congrArg (Nat.cast (R := ℤ)) (Nat.choose_succ_right_eq n (m + 1))
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h] at hc
        push_cast at hc
        linear_combination hc
    have h2 : ((n + (m + 1 + 1)).choose (m + 1 + 1) : ℤ) * ((m : ℤ) + 2) =
        ((n + (m + 1)).choose (m + 1) : ℤ) * ((n : ℤ) + m + 2) := by
      have hn : (n + (m + 1) + 1) * (n + (m + 1)).choose (m + 1) =
          (n + (m + 1 + 1)).choose (m + 1 + 1) * (m + 1 + 1) :=
        Nat.add_one_mul_choose_eq (n + (m + 1)) (m + 1)
      have hc := congrArg (Nat.cast (R := ℤ)) hn
      push_cast at hc
      linear_combination -hc
    rw [Finset.prod_range_succ, Nat.factorial_succ (m + 1)]
    push_cast
    linear_combination
      (((m + 1).factorial : ℤ) ^ 2 * ((n + (m + 1 + 1)).choose (m + 1 + 1) : ℤ) *
          ((m : ℤ) + 2)) * h1 +
        (((m + 1).factorial : ℤ) ^ 2 * (n.choose (m + 1) : ℤ) * ((n : ℤ) - ((m : ℤ) + 1))) * h2 +
        (((n : ℤ) - ((m : ℤ) + 1)) * ((n : ℤ) + m + 2)) * ih

private lemma p_sq_zero (p : ℕ) : ((p : ZMod (p ^ 2)) ^ 2) = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

private lemma coprime_p2 {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    Nat.Coprime k (p ^ 2) :=
  ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk0 hkp)).symm).pow_right 2

private lemma mul_inv_p2 {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    (k : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ = 1 :=
  ZMod.coe_mul_inv_eq_one k (coprime_p2 hp hk0 hkp)

/-- Modulo `p^2` the product `prod_{i<m} (p^2 - (i+1)^2)` is `(-1)^m * (m!)^2`. -/
private lemma prod_zmod (p m : ℕ) :
    ∏ i ∈ Finset.range m, ((p : ZMod (p ^ 2)) ^ 2 - ((i : ZMod (p ^ 2)) + 1) ^ 2) =
      (-1 : ZMod (p ^ 2)) ^ m * ((m.factorial : ℕ) : ZMod (p ^ 2)) ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    push_cast
    linear_combination
      ((-1 : ZMod (p ^ 2)) ^ m * ((m.factorial : ℕ) : ZMod (p ^ 2)) ^ 2) * p_sq_zero p

/-- For `k = m + 1 < p`: `C(p-1,k) * C(p-1+k,k) = p * b` with `k^4 * b^2 = k^2 - 2*p*k` modulo `p^2`. -/
private lemma key_zmod {p : ℕ} (hp : p.Prime) (m : ℕ) (hm : m + 1 < p) :
    ∃ b : ℤ, ((p - 1).choose (m + 1) : ℤ) * ((p - 1 + (m + 1)).choose (m + 1) : ℤ) = (p : ℤ) * b ∧
      ((m + 1 : ℕ) : ZMod (p ^ 2)) ^ 4 * (b : ZMod (p ^ 2)) ^ 2 =
        ((m + 1 : ℕ) : ZMod (p ^ 2)) ^ 2 -
          2 * (p : ZMod (p ^ 2)) * ((m + 1 : ℕ) : ZMod (p ^ 2)) := by
  have hA := fact_sq_mul_choose (p - 1) m
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub hp.one_le]
    simp
  rw [hp1, sub_add_cancel] at hA
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnd : ¬ (p : ℤ) ∣ ((m + 1).factorial : ℤ) ^ 2 := by
    intro h
    have h' : p ∣ (m + 1).factorial := Int.natCast_dvd_natCast.mp (hpZ.dvd_of_dvd_pow h)
    have h'' := hp.dvd_factorial.mp h'
    omega
  have hdvd : (p : ℤ) ∣
      ((p - 1).choose (m + 1) : ℤ) * ((p - 1 + (m + 1)).choose (m + 1) : ℤ) := by
    have h : (p : ℤ) ∣ ((m + 1).factorial : ℤ) ^ 2 *
        (((p - 1).choose (m + 1) : ℤ) * ((p - 1 + (m + 1)).choose (m + 1) : ℤ)) := by
      rw [← mul_assoc, hA, mul_assoc]
      exact dvd_mul_right _ _
    exact (hpZ.dvd_or_dvd h).resolve_left hnd
  obtain ⟨b, hb⟩ := hdvd
  refine ⟨b, hb, ?_⟩
  have hX : ((m + 1).factorial : ℤ) ^ 2 * b =
      ((p : ℤ) - 1 - m) * ∏ i ∈ Finset.range m, ((p : ℤ) ^ 2 - ((i : ℤ) + 1) ^ 2) := by
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    apply mul_left_cancel₀ hp0
    linear_combination hA - ((m + 1).factorial : ℤ) ^ 2 * hb
  have hXR := congrArg (Int.cast (R := ZMod (p ^ 2))) hX
  push_cast at hXR
  rw [prod_zmod] at hXR
  have hfac : (((m + 1).factorial : ℕ) : ZMod (p ^ 2)) =
      ((m : ZMod (p ^ 2)) + 1) * ((m.factorial : ℕ) : ZMod (p ^ 2)) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfac] at hXR
  have hkm : ((m + 1 : ℕ) : ZMod (p ^ 2)) = (m : ZMod (p ^ 2)) + 1 := by
    push_cast
    ring
  rw [hkm]
  have hu : IsUnit ((m.factorial : ℕ) : ZMod (p ^ 2)) :=
    (ZMod.isUnit_iff_coprime _ _).mpr
      (((hp.coprime_iff_not_dvd.mpr (fun hd => by
        have := hp.dvd_factorial.mp hd
        omega)).symm).pow_right 2)
  have h' : ((m : ZMod (p ^ 2)) + 1) ^ 2 * (b : ZMod (p ^ 2)) =
      ((p : ZMod (p ^ 2)) - ((m : ZMod (p ^ 2)) + 1)) * (-1 : ZMod (p ^ 2)) ^ m := by
    apply (hu.pow 2).mul_left_cancel
    linear_combination hXR
  have hs : ((-1 : ZMod (p ^ 2)) ^ m) ^ 2 = 1 := by
    rw [← pow_mul]
    exact Even.neg_one_pow ⟨m, by ring⟩
  linear_combination
    (((m : ZMod (p ^ 2)) + 1) ^ 2 * (b : ZMod (p ^ 2)) +
        ((p : ZMod (p ^ 2)) - ((m : ZMod (p ^ 2)) + 1)) * (-1 : ZMod (p ^ 2)) ^ m) * h' +
      ((p : ZMod (p ^ 2)) - ((m : ZMod (p ^ 2)) + 1)) ^ 2 * hs + p_sq_zero p

/-- `sum_{k=1}^{p-1} k^(-2) = 0` in `ZMod p` for a prime `p >= 5`. -/
private lemma sum_inv_sq_zmod_p {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 p).mp h')
    omega
  have h3ne : (3 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 3 p).mp h')
    omega
  have hbij : ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2 = ∑ x : ZMod p, (x⁻¹) ^ 2 := by
    symm
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
    simp only [inv_zero, zero_pow (two_ne_zero), zero_add]
    refine Finset.sum_nbij (fun x => x.val) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
      simp only [Finset.mem_Icc]
      have hpos : 0 < x.val := Nat.pos_of_ne_zero fun h => hx ((ZMod.val_eq_zero x).mp h)
      have hlt : x.val < p := x.val_lt
      omega
    · intro x _ y _ h
      exact ZMod.val_injective p h
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_Icc] at hk
      refine ⟨(k : ZMod p), ?_, ZMod.val_natCast_of_lt (by omega)⟩
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true]
      intro h0
      exact Nat.not_dvd_of_pos_of_lt hk.1 (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h0)
    · intro x _
      rw [ZMod.natCast_zmod_val]
  rw [hbij]
  have hscale : ∑ x : ZMod p, ((2 * x)⁻¹) ^ 2 = ∑ x : ZMod p, (x⁻¹) ^ 2 :=
    Equiv.sum_comp (Equiv.mulLeft₀ (2 : ZMod p) h2ne) (fun x => (x⁻¹) ^ 2)
  have h4 : ∑ x : ZMod p, ((2 * x)⁻¹) ^ 2 =
      ((2 : ZMod p)⁻¹) ^ 2 * ∑ x : ZMod p, (x⁻¹) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => by rw [mul_inv, mul_pow]
  rw [h4] at hscale
  have h22 : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h2ne
  have h3s : (3 : ZMod p) * ∑ x : ZMod p, (x⁻¹) ^ 2 = 0 := by
    linear_combination (-4 : ZMod p) * hscale +
      ((2 * (2 : ZMod p)⁻¹ + 1) * ∑ x : ZMod p, (x⁻¹) ^ 2) * h22
  exact (mul_eq_zero.mp h3s).resolve_left h3ne

/-- An element of `ZMod (p^2)` that reduces to `0` modulo `p` is killed by `p`. -/
private lemma p_mul_eq_zero_of_castHom {p : ℕ} (hp : p.Prime) (w : ZMod (p ^ 2))
    (h : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) w = 0) :
    (p : ZMod (p ^ 2)) * w = 0 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h
  have hval : p ∣ w.val := (ZMod.natCast_eq_zero_iff _ _).mp h
  rw [← ZMod.natCast_zmod_val w, ← Nat.cast_mul]
  apply (ZMod.natCast_eq_zero_iff _ _).mpr
  exact dvd_trans (dvd_of_eq (sq p)) (mul_dvd_mul_left p hval)

/-- `p * sum_{k=1}^{p-1} k^(-2) = 0` in `ZMod (p^2)` for a prime `p >= 5`. -/
private lemma p_mul_sum_inv_sq {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ZMod (p ^ 2)) * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  apply p_mul_eq_zero_of_castHom hp
  rw [map_sum]
  refine Eq.trans ?_ (sum_inv_sq_zmod_p hp hp5)
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_Icc] at hk
  have hm := congrArg (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))
    (mul_inv_p2 hp (k := k) (by omega) (by omega))
  simp only [map_mul, map_one, map_natCast] at hm
  have hkne : (k : ZMod p) ≠ 0 := fun h =>
    Nat.not_dvd_of_pos_of_lt hk.1 (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h)
  rw [map_pow]
  congr 1
  exact mul_left_cancel₀ hkne (by rw [hm, mul_inv_cancel₀ hkne])

/-- `1/k + 1/(p-k) = -p/k^2` in `ZMod (p^2)`. -/
private lemma inv_add_inv_reflect {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    (k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ =
      -((p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 2) := by
  have h1 := mul_inv_p2 hp hk0 hkp
  have h2 := mul_inv_p2 hp (k := p - k) (by omega) (by omega)
  have hcast : ((p - k : ℕ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) - (k : ZMod (p ^ 2)) :=
    Nat.cast_sub (by omega)
  rw [hcast] at h2 ⊢
  linear_combination
    (1 + (p : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹) *
        (-(k : ZMod (p ^ 2))⁻¹ * h2 -
          ((p : ZMod (p ^ 2)) - (k : ZMod (p ^ 2)))⁻¹ * h1) +
      (((k : ZMod (p ^ 2))⁻¹) ^ 2 * ((p : ZMod (p ^ 2)) - (k : ZMod (p ^ 2)))⁻¹) * p_sq_zero p

/-- `2 * sum_{k=1}^{p-1} 1/k = -p * sum_{k=1}^{p-1} 1/k^2` in `ZMod (p^2)`. -/
private lemma two_mul_sum_inv {p : ℕ} (hp : p.Prime) :
    2 * ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ =
      -((p : ZMod (p ^ 2)) * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2) := by
  have hrefl : ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ =
      ∑ k ∈ Finset.Icc 1 (p - 1), ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ := by
    refine Finset.sum_nbij (fun k => p - k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro x hx y hy h
      simp only [Finset.mem_coe, Finset.mem_Icc] at hx hy
      dsimp only at h
      omega
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_Icc] at hk
      exact ⟨p - k, by simp only [Finset.mem_coe, Finset.mem_Icc]; omega, by dsimp only; omega⟩
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      rw [Nat.sub_sub_self (by omega)]
  have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
      (k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ =
        -((p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 2) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    exact inv_add_inv_reflect hp (by omega) (by omega)
  calc 2 * ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹
      = ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ +
          ∑ k ∈ Finset.Icc 1 (p - 1), ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ := by
        rw [← hrefl, two_mul]
    _ = ∑ k ∈ Finset.Icc 1 (p - 1),
          ((k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹) :=
        Finset.sum_add_distrib.symm
    _ = ∑ k ∈ Finset.Icc 1 (p - 1), -((p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 2) :=
        Finset.sum_congr rfl hterm
    _ = -((p : ZMod (p ^ 2)) * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2) := by
        rw [Finset.sum_neg_distrib, Finset.mul_sum]

/-- The sum `sum_{k=1}^{p-1} k * b_k^2` vanishes in `ZMod (p^2)`. -/
private lemma sum_zmod_zero {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (b : ℕ → ℤ)
    (hb : ∀ k ∈ Finset.Icc 1 (p - 1),
      (k : ZMod (p ^ 2)) ^ 4 * ((b k : ℤ) : ZMod (p ^ 2)) ^ 2 =
        (k : ZMod (p ^ 2)) ^ 2 - 2 * (p : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))) :
    ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2)) * ((b k : ℤ) : ZMod (p ^ 2)) ^ 2 = 0 := by
  have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
      (k : ZMod (p ^ 2)) * ((b k : ℤ) : ZMod (p ^ 2)) ^ 2 =
        (k : ZMod (p ^ 2))⁻¹ - 2 * ((p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 2) := by
    intro k hk
    have hbk := hb k hk
    simp only [Finset.mem_Icc] at hk
    have h1 := mul_inv_p2 hp (k := k) (by omega) (by omega)
    linear_combination ((k : ZMod (p ^ 2))⁻¹) ^ 3 * hbk +
      (-(k : ZMod (p ^ 2)) * ((b k : ℤ) : ZMod (p ^ 2)) ^ 2 *
            (((k : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹) ^ 2 +
              (k : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ + 1) +
          (k : ZMod (p ^ 2))⁻¹ * ((k : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ + 1) -
          2 * (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 2) * h1
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hW := two_mul_sum_inv hp
  have hF := p_mul_sum_inv_sq hp hp5
  have h2u : IsUnit (2 : ZMod (p ^ 2)) := by
    have h := (ZMod.isUnit_iff_coprime 2 (p ^ 2)).mpr (coprime_p2 hp (by norm_num) (by omega))
    exact_mod_cast h
  apply h2u.mul_left_cancel
  rw [mul_zero]
  linear_combination hW - 5 * hF

theorem OMA.solution : type_of% @OMA.S_oeis_a357510.main := by
  intro p hp hp5
  have hex : ∀ k : ℕ, ∃ b : ℤ, 1 ≤ k → k < p →
      (((p - 1).choose k : ℤ) * ((p - 1 + k).choose k : ℤ) = (p : ℤ) * b ∧
        (k : ZMod (p ^ 2)) ^ 4 * (b : ZMod (p ^ 2)) ^ 2 =
          (k : ZMod (p ^ 2)) ^ 2 - 2 * (p : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))) := by
    intro k
    by_cases hk : 1 ≤ k ∧ k < p
    · obtain ⟨hk1, hkp⟩ := hk
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      obtain ⟨b, h1, h2⟩ := key_zmod hp m hkp
      exact ⟨b, fun _ _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
  choose b hb using hex
  have hsum : OMA.S_oeis_a357510.a (p - 1) =
      (p : ℤ) ^ 2 * ∑ k ∈ Finset.Icc 1 (p - 1), (k : ℤ) * (b k) ^ 2 := by
    unfold OMA.S_oeis_a357510.a
    have hsub : Finset.Icc 1 (p - 1) ⊆ Finset.range (p - 1 + 1) := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      simp only [Finset.mem_range]
      omega
    have hzero : ∀ k ∈ Finset.range (p - 1 + 1), k ∉ Finset.Icc 1 (p - 1) →
        (k : ℤ) * ((p - 1).choose k : ℤ) ^ 2 * ((p - 1 + k).choose k : ℤ) ^ 2 = 0 := by
      intro k hk hk'
      simp only [Finset.mem_range] at hk
      have hk0 : k = 0 := by
        by_contra hne
        exact hk' (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rw [hk0]
      simp
    rw [Finset.mul_sum, ← Finset.sum_subset hsub hzero]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    obtain ⟨h1, -⟩ := hb k hk.1 (by omega)
    have hsq : (k : ℤ) * ((p - 1).choose k : ℤ) ^ 2 * ((p - 1 + k).choose k : ℤ) ^ 2 =
        (k : ℤ) * (((p - 1).choose k : ℤ) * ((p - 1 + k).choose k : ℤ)) ^ 2 := by ring
    rw [hsq, h1]
    ring
  have hS : ((p : ℤ) ^ 2) ∣ ∑ k ∈ Finset.Icc 1 (p - 1), (k : ℤ) * (b k) ^ 2 := by
    have hz := sum_zmod_zero hp hp5 b (fun k hk => by
      simp only [Finset.mem_Icc] at hk
      exact (hb k hk.1 (by omega)).2)
    have hcast : ((∑ k ∈ Finset.Icc 1 (p - 1), (k : ℤ) * (b k) ^ 2 : ℤ) : ZMod (p ^ 2)) = 0 := by
      push_cast
      exact hz
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
    exact_mod_cast h
  rw [hsum]
  have hp4 : (p : ℤ) ^ 4 = (p : ℤ) ^ 2 * (p : ℤ) ^ 2 := by ring
  rw [hp4]
  exact mul_dvd_mul_left _ hS
