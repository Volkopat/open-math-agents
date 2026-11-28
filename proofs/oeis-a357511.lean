import OMAStatements.S_oeis_a357511
import Mathlib

/-!
# OEIS A357511: `a(p-1) == 0 (mod p^4)` for every prime `p >= 7` (conjecture of Peter Bala, 2022)

`a(n)` is the numerator of `s(n) = Sum_{k=1..n} (1/k) * C(n,k)^2 * C(n+k,k)^2`.

Proof. Put `n = p - 1`, `T_k = C(p-1,k) * C(p-1+k,k)` and work in `R = ZMod (p^2)`.

1. `(k!)^2 * T_k = p * (p-k) * prod_{i<k-1} (p^2 - (i+1)^2)` in the integers, so `T_k = p * b_k` with
   `(k!)^2 * b_k = (p-k) * prod_{i<k-1} (p^2 - (i+1)^2)`.
2. In `R` the product is `(-1)^(k-1) * ((k-1)!)^2`, hence `k^4 * b_k^2 = (p-k)^2 = k^2 - 2*p*k` and
   `(1/k) * b_k^2 = 1/k^3 - 2*p/k^4`.
3. `1/k^3 + 1/(p-k)^3 = -3*p/k^4` in `R`, so by the reflection `k -> p-k`,
   `2 * Sum 1/k^3 = -3 * p * Sum 1/k^4`.
4. `Sum_{k=1..p-1} 1/k^4 = 0` in `ZMod p` for `p >= 7` (the sum of `x^4` over the field vanishes as
   `4 < p - 1`), hence `p * Sum 1/k^4 = 0` in `R`.
5. So `Sum (1/k) * b_k^2 = 0` in `R`. With `D = (p-1)!` and `c_k = D / k` (an integer),
   `s(p-1) * D = p^2 * Sum c_k * b_k^2` and `Sum c_k * b_k^2 = D * Sum (1/k) * b_k^2 = 0` in `R`,
   so `s(p-1) * D = p^4 * N` for an integer `N`.
6. `num(s) * D = p^4 * N * den(s)` and `p` does not divide `D`, so `p^4` divides the numerator.
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

/-- For `k = m + 1 < p`: `C(p-1,k) * C(p-1+k,k) = p * b` with `k^4 * b^2 = k^2 - 2*p*k` modulo
`p^2`. -/
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

/-- A sum over `k = 1..p-1` of a function of the residue of `k` is the sum over the whole field,
when the function vanishes at `0`. -/
private lemma sum_Icc_eq_sum_univ {p : ℕ} [Fact p.Prime] (f : ZMod p → ZMod p) (hf : f 0 = 0) :
    ∑ k ∈ Finset.Icc 1 (p - 1), f (k : ZMod p) = ∑ x : ZMod p, f x := by
  symm
  rw [← Finset.sum_erase Finset.univ hf]
  refine Finset.sum_nbij (fun x => x.val) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
    have hpos : 0 < x.val := Nat.pos_of_ne_zero fun h => hx ((ZMod.val_eq_zero x).mp h)
    have hlt : x.val < p := x.val_lt
    exact Finset.mem_Icc.mpr ⟨hpos, by omega⟩
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

/-- `sum_{k=1}^{p-1} k^(-4) = 0` in `ZMod p` for a prime `p >= 7`. -/
private lemma sum_inv_pow4_zmod_p {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 4 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  refine (sum_Icc_eq_sum_univ (fun x : ZMod p => (x⁻¹) ^ 4) (by simp)).trans ?_
  have hinv : ∑ x : ZMod p, (x⁻¹) ^ 4 = ∑ x : ZMod p, x ^ 4 :=
    Equiv.sum_comp (Equiv.inv (ZMod p)) (fun x => x ^ 4)
  rw [hinv]
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) 4 (by rw [ZMod.card]; omega)

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

/-- `p * sum_{k=1}^{p-1} k^(-4) = 0` in `ZMod (p^2)` for a prime `p >= 7`. -/
private lemma p_mul_sum_inv_pow4 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p : ZMod (p ^ 2)) * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 4 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  apply p_mul_eq_zero_of_castHom hp
  rw [map_sum]
  refine Eq.trans ?_ (sum_inv_pow4_zmod_p hp hp7)
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

/-- Ring identity behind the reflection `k -> p - k`: if `x * u = 1`, `(y - x) * v = 1` and
`y^2 = 0`, then `u^3 + v^3 = -3 * y * u^4`. -/
private lemma ring_reflect {R : Type*} [CommRing R] (x y u v : R) (h1 : x * u = 1)
    (h2 : (y - x) * v = 1) (h0 : y ^ 2 = 0) : u ^ 3 + v ^ 3 = -(3 * (y * u ^ 4)) := by
  have hv : v = -u - y * u ^ 2 := by
    linear_combination (-v * (1 + y * u)) * h1 + (v * u ^ 2) * h0 + (-u - y * u ^ 2) * h2
  rw [hv]
  linear_combination (-(3 * u ^ 5 + y * u ^ 6)) * h0

/-- Ring identity: if `x * u = 1` and `x^4 * c^2 = x^2 - 2*y*x`, then
`u * c^2 = u^3 - 2 * y * u^4`. -/
private lemma ring_term {R : Type*} [CommRing R] (x y u c : R) (h1 : x * u = 1)
    (hb : x ^ 4 * c ^ 2 = x ^ 2 - 2 * y * x) : u * c ^ 2 = u ^ 3 - 2 * (y * u ^ 4) := by
  linear_combination u ^ 5 * hb +
    (-(u * c ^ 2) * ((x * u) ^ 3 + (x * u) ^ 2 + x * u + 1) + u ^ 3 * (x * u + 1) -
      2 * y * u ^ 4) * h1

/-- `1/k^3 + 1/(p-k)^3 = -3*p/k^4` in `ZMod (p^2)`. -/
private lemma inv_cube_add_reflect {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    ((k : ZMod (p ^ 2))⁻¹) ^ 3 + (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ 3 =
      -(3 * ((p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 4)) := by
  have h1 := mul_inv_p2 hp hk0 hkp
  have h2 := mul_inv_p2 hp (k := p - k) (by omega) (by omega)
  have hcast : ((p - k : ℕ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) - (k : ZMod (p ^ 2)) :=
    Nat.cast_sub (by omega)
  rw [hcast] at h2 ⊢
  exact ring_reflect _ _ _ _ h1 h2 (p_sq_zero p)

/-- `2 * sum_{k=1}^{p-1} 1/k^3 = -3 * p * sum_{k=1}^{p-1} 1/k^4` in `ZMod (p^2)`. -/
private lemma two_mul_sum_inv_cube {p : ℕ} (hp : p.Prime) :
    2 * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 3 =
      -(3 * ((p : ZMod (p ^ 2)) * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 4)) := by
  have hrefl : ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 3 =
      ∑ k ∈ Finset.Icc 1 (p - 1), (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ 3 := by
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
      ((k : ZMod (p ^ 2))⁻¹) ^ 3 + (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ 3 =
        -(3 * ((p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 4)) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    exact inv_cube_add_reflect hp (by omega) (by omega)
  calc 2 * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 3
      = ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 3 +
          ∑ k ∈ Finset.Icc 1 (p - 1), (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ 3 := by
        rw [← hrefl, two_mul]
    _ = ∑ k ∈ Finset.Icc 1 (p - 1),
          (((k : ZMod (p ^ 2))⁻¹) ^ 3 + (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ 3) :=
        Finset.sum_add_distrib.symm
    _ = ∑ k ∈ Finset.Icc 1 (p - 1),
          -(3 * ((p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 4)) :=
        Finset.sum_congr rfl hterm
    _ = -(3 * ((p : ZMod (p ^ 2)) *
          ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 4)) := by
        rw [Finset.sum_neg_distrib, Finset.mul_sum, Finset.mul_sum]

/-- The sum `sum_{k=1}^{p-1} (1/k) * b_k^2` vanishes in `ZMod (p^2)`. -/
private lemma sum_zmod_zero {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (b : ℕ → ℤ)
    (hb : ∀ k ∈ Finset.Icc 1 (p - 1),
      (k : ZMod (p ^ 2)) ^ 4 * ((b k : ℤ) : ZMod (p ^ 2)) ^ 2 =
        (k : ZMod (p ^ 2)) ^ 2 - 2 * (p : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))) :
    ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ * ((b k : ℤ) : ZMod (p ^ 2)) ^ 2 = 0 := by
  have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
      (k : ZMod (p ^ 2))⁻¹ * ((b k : ℤ) : ZMod (p ^ 2)) ^ 2 =
        ((k : ZMod (p ^ 2))⁻¹) ^ 3 - 2 * ((p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 4) := by
    intro k hk
    have hbk := hb k hk
    simp only [Finset.mem_Icc] at hk
    have h1 := mul_inv_p2 hp (k := k) (by omega) (by omega)
    exact ring_term _ _ _ _ h1 hbk
  have hsum : ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ * ((b k : ℤ) : ZMod (p ^ 2)) ^ 2 =
      ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 3 -
        2 * ((p : ZMod (p ^ 2)) * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 4) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [hsum]
  have hW := two_mul_sum_inv_cube hp
  have hF := p_mul_sum_inv_pow4 hp hp7
  have h2u : IsUnit (2 : ZMod (p ^ 2)) := by
    have h := (ZMod.isUnit_iff_coprime 2 (p ^ 2)).mpr (coprime_p2 hp (by norm_num) (by omega))
    exact_mod_cast h
  apply h2u.mul_left_cancel
  rw [mul_zero]
  linear_combination hW - 7 * hF

/-- If `q * D = p^4 * N` with `D` prime to `p`, then `p^4` divides the numerator of `q`. -/
private lemma num_dvd_aux {p : ℕ} (q : ℚ) (D : ℕ) (N : ℤ) (hD : Nat.Coprime p D)
    (hq : q * (D : ℚ) = (p : ℚ) ^ 4 * (N : ℚ)) : ((p : ℤ) ^ 4) ∣ q.num := by
  have h3 : q * (q.den : ℚ) = (q.num : ℚ) := Rat.mul_den_eq_num q
  have h2 : ((q.num * (D : ℤ) : ℤ) : ℚ) = (((p : ℤ) ^ 4 * (N * (q.den : ℤ)) : ℤ) : ℚ) := by
    push_cast
    linear_combination (q.den : ℚ) * hq - (D : ℚ) * h3
  have h4 : q.num * (D : ℤ) = (p : ℤ) ^ 4 * (N * (q.den : ℤ)) := Int.cast_injective h2
  have hcop : IsCoprime ((p : ℤ) ^ 4) (D : ℤ) := (Nat.isCoprime_iff_coprime.mpr hD).pow_left
  exact hcop.dvd_of_dvd_mul_right (Dvd.intro _ h4.symm)

theorem OMA.solution : type_of% @OMA.S_oeis_a357511.main := by
  intro p hp hp7
  -- the integers `b k` with `C(p-1,k) * C(p-1+k,k) = p * b k`
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
  -- the integers `c k = (p-1)! / k`
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ, ∀ k ∈ Finset.Icc 1 (p - 1), k * c k = (p - 1).factorial :=
    ⟨fun k => (p - 1).factorial / k, fun k hk => by
      simp only [Finset.mem_Icc] at hk
      exact Nat.mul_div_cancel' (Nat.dvd_factorial (by omega) hk.2)⟩
  -- `p^2` divides `sum c_k * b_k^2`
  have hS : ((p : ℤ) ^ 2) ∣ ∑ k ∈ Finset.Icc 1 (p - 1), (c k : ℤ) * (b k) ^ 2 := by
    have hz := sum_zmod_zero hp hp7 b (fun k hk => by
      simp only [Finset.mem_Icc] at hk
      exact (hb k hk.1 (by omega)).2)
    have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
        (c k : ZMod (p ^ 2)) * ((b k : ℤ) : ZMod (p ^ 2)) ^ 2 =
          (((p - 1).factorial : ℕ) : ZMod (p ^ 2)) *
            ((k : ZMod (p ^ 2))⁻¹ * ((b k : ℤ) : ZMod (p ^ 2)) ^ 2) := by
      intro k hk
      have h2 : (k : ZMod (p ^ 2)) * (c k : ZMod (p ^ 2)) =
          (((p - 1).factorial : ℕ) : ZMod (p ^ 2)) := by
        rw [← Nat.cast_mul, hc k hk]
      simp only [Finset.mem_Icc] at hk
      have h1 := mul_inv_p2 hp (k := k) (by omega) (by omega)
      linear_combination (-(c k : ZMod (p ^ 2)) * ((b k : ℤ) : ZMod (p ^ 2)) ^ 2) * h1 +
        ((k : ZMod (p ^ 2))⁻¹ * ((b k : ℤ) : ZMod (p ^ 2)) ^ 2) * h2
    have hcast : ((∑ k ∈ Finset.Icc 1 (p - 1), (c k : ℤ) * (b k) ^ 2 : ℤ) : ZMod (p ^ 2)) = 0 := by
      push_cast
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hz, mul_zero]
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
    exact_mod_cast h
  obtain ⟨N, hN⟩ := hS
  have hNq : ∑ k ∈ Finset.Icc 1 (p - 1), (c k : ℚ) * (b k : ℚ) ^ 2 = (p : ℚ) ^ 2 * (N : ℚ) := by
    have h := congrArg (Int.cast (R := ℚ)) hN
    push_cast at h
    exact h
  -- `s(p-1) * (p-1)! = p^2 * sum c_k * b_k^2`
  have hsum : OMA.S_oeis_a357511.s (p - 1) * (((p - 1).factorial : ℕ) : ℚ) =
      (p : ℚ) ^ 2 * ∑ k ∈ Finset.Icc 1 (p - 1), (c k : ℚ) * (b k : ℚ) ^ 2 := by
    unfold OMA.S_oeis_a357511.s
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hD : (((p - 1).factorial : ℕ) : ℚ) = (k : ℚ) * (c k : ℚ) := by
      rw [← Nat.cast_mul, hc k hk]
    simp only [Finset.mem_Icc] at hk
    obtain ⟨h1, -⟩ := hb k hk.1 (by omega)
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h1q : ((p - 1).choose k : ℚ) * ((p - 1 + k).choose k : ℚ) = (p : ℚ) * (b k : ℚ) := by
      exact_mod_cast h1
    rw [hD]
    calc 1 / (k : ℚ) * ((p - 1).choose k : ℚ) ^ 2 * ((p - 1 + k).choose k : ℚ) ^ 2 *
          ((k : ℚ) * (c k : ℚ))
        = (1 / (k : ℚ) * (k : ℚ)) * (c k : ℚ) *
            (((p - 1).choose k : ℚ) * ((p - 1 + k).choose k : ℚ)) ^ 2 := by ring
      _ = (p : ℚ) ^ 2 * ((c k : ℚ) * (b k : ℚ) ^ 2) := by
          rw [one_div_mul_cancel hk0, h1q]
          ring
  have hq : OMA.S_oeis_a357511.s (p - 1) * (((p - 1).factorial : ℕ) : ℚ) =
      (p : ℚ) ^ 4 * (N : ℚ) := by
    rw [hsum, hNq]
    ring
  have hcop : Nat.Coprime p (p - 1).factorial :=
    hp.coprime_iff_not_dvd.mpr (fun hd => by
      have := hp.dvd_factorial.mp hd
      omega)
  exact num_dvd_aux _ _ N hcop hq
