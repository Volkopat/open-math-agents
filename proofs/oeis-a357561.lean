import OMAStatements.S_oeis_a357561
import Mathlib

/-!
# OEIS A357561: two conjectures of Peter Bala (2022)

`S_m(n)` is the numerator of `s_m(n) = Sum_{k=1..n} (-1)^(n+k) * (1/k^m) * C(n,k) * C(n+k,k)^2`
and `a(n) = S_3(n)`.

1. For odd `m` and every prime `p > m + 4`: `S_m(p-1) == 0 (mod p^4)`.
2. `a(p-1) == 0 (mod p^4)` for `p = 5` and every prime `p >= 11`.

Proof of 1. Work in `R = ZMod (p^2)`; write `u_k` for the inverse of `k` and
`H_n = Sum_{j=1..n} u_j`.

* `C(p-1,k) = (-1)^k * (1 - p*H_k)` in `R` for `k < p` (induction on `k`).
* `C(p+j,j) = 1 + p*H_j` in `R` for `j < p` (induction on `j`), and `C(p+j,j+1) * (j+1) = C(p+j,j) * p`,
  so `C(p-1+k,k) = p * e_k` with `e_k = u_k * (1 + p*H_(k-1))` in `R`.
* Hence `C(p-1,k) * C(p-1+k,k)^2 = p^2 * t_k` with
  `t_k = (-1)^k * u_k^2 * (1 + p*H_(k-1) - p*u_k)` in `R`.
* With `D = (p-1)!` and `c_k = (D/k)^m`:
  `s_m(p-1) * D^m = p^2 * Sum (-1)^(p-1+k) * c_k * t_k`, and in `R` the last sum equals
  `D^m * (Sum u_k^(m+2) + p * Sum u_k^(m+2)*H_(k-1) - p * Sum u_k^(m+3))`.
* `Sum_{k=1..p-1} k^(-d) = 0` in `ZMod p` for `0 < d < p-1`; so `p * Sum u_k^(m+3) = 0` in `R`.
* For odd `d`: `u_k^d + u_(p-k)^d = -d*p*u_k^(d+1)` in `R`, so `2 * Sum u_k^d = -d*p*Sum u_k^(d+1) = 0`.
* In `ZMod p` the harmonic numbers satisfy `G_(p-1-r) = G_r`, and the reflection `k -> p-k` gives
  `2 * Sum k^(-d) * G_(k-1) = -Sum k^(-d-1) = 0` for odd `d`; so `p * Sum u_k^(m+2)*H_(k-1) = 0` in `R`.
* So `s_m(p-1) * D^m = p^4 * N`; as `p` does not divide `D^m`, `p^4` divides the numerator.

Claim 2 is the case `m = 3` for `p >= 11`, and `s_3(4) = -15625/432 = -5^6/432` for `p = 5`.
-/

/-! ### Ring identities (all with `P^2 = 0`) -/

private lemma ring_step1 {R : Type*} [CommRing R] (C x u s h P : R) (hinv : x * u = 1)
    (hch : C * x = s * (1 - P * h) * (P - x)) (h0 : P ^ 2 = 0) :
    C = s * (-1) * (1 - P * (h + u)) := by
  linear_combination (-C - s * (1 - P * h)) * hinv + u * hch - s * h * u * h0

private lemma ring_step2 {R : Type*} [CommRing R] (C' C x u h P : R) (hinv : x * u = 1)
    (hch : (P + x) * C = C' * x) (ih : C = 1 + P * h) (h0 : P ^ 2 = 0) :
    C' = 1 + P * (h + u) := by
  linear_combination (C - C') * hinv - u * hch + (u * P + 1) * ih + u * h * h0

private lemma ring_step3 {R : Type*} [CommRing R] (e x u c : R) (hinv : x * u = 1)
    (h : e * x = c) : e = u * c := by
  linear_combination (-e) * hinv + u * h

private lemma ring_term {R : Type*} [CommRing R] (s u h P : R) (h0 : P ^ 2 = 0) :
    s * (1 - P * (h + u)) * (u * (1 + P * h)) ^ 2 = s * u ^ 2 * (1 + P * h - P * u) := by
  linear_combination (s * u ^ 2 * (-h ^ 2 - 2 * h * u - P * h ^ 3 - P * h ^ 2 * u)) * h0

private lemma one_add_pow_of_sq_zero {R : Type*} [CommRing R] (P c : R) (h0 : P ^ 2 = 0)
    (d : ℕ) : (1 + P * c) ^ d = 1 + (d : R) * P * c := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (d : R) * c ^ 2 * h0

/-- Reflection `k -> p - k`: if `x * u = 1`, `(P - x) * v = 1`, `P^2 = 0` and `d` is odd, then
`u^d + v^d = -d * P * u^(d+1)`. -/
private lemma ring_reflect {R : Type*} [CommRing R] (x P u v : R) (h1 : x * u = 1)
    (h2 : (P - x) * v = 1) (h0 : P ^ 2 = 0) (d : ℕ) (hd : Odd d) :
    u ^ d + v ^ d = -((d : R) * (P * u ^ (d + 1))) := by
  have hv : v = (-u) * (1 + P * u) := by
    linear_combination (-v * (1 + P * u)) * h1 + (v * u ^ 2) * h0 + (-u - P * u ^ 2) * h2
  rw [hv, mul_pow, hd.neg_pow, one_add_pow_of_sq_zero P u h0 d, pow_succ]
  ring

private lemma ring_final {R : Type*} [CommRing R] (x u cK Dm s1 s2 h P : R) (m : ℕ)
    (h1 : x * u = 1) (hck : x ^ m * cK = Dm) (hs : s1 * s2 = 1) :
    s1 * (cK * (s2 * u ^ 2 * (1 + P * h - P * u))) =
      Dm * (u ^ (m + 2) + P * (u ^ (m + 2) * h) - P * u ^ (m + 3)) := by
  have hxu : x ^ m * u ^ m = 1 := by rw [← mul_pow, h1, one_pow]
  have hcK : cK = Dm * u ^ m := by linear_combination (-cK) * hxu + u ^ m * hck
  rw [hcK]
  linear_combination (Dm * u ^ m * u ^ 2 * (1 + P * h - P * u)) * hs

private lemma neg_one_pow_add_mul_cancel {R : Type*} [CommRing R] (n k : ℕ) (hn : Even n) :
    (-1 : R) ^ (n + k) * (-1 : R) ^ k = 1 := by
  rw [← pow_add]
  obtain ⟨r, hr⟩ := hn
  exact Even.neg_one_pow ⟨r + k, by omega⟩

/-! ### Basic facts on `ZMod (p^2)` -/

private lemma p_sq_zero (p : ℕ) : ((p : ZMod (p ^ 2)) ^ 2) = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

private lemma coprime_p2 {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    Nat.Coprime k (p ^ 2) :=
  ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk0 hkp)).symm).pow_right 2

private lemma mul_inv_p2 {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    (k : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ = 1 :=
  ZMod.coe_mul_inv_eq_one k (coprime_p2 hp hk0 hkp)

/-- The harmonic number `H_n = Sum_{j=1..n} 1/j` in `ZMod (p^2)`. -/
private def H (p n : ℕ) : ZMod (p ^ 2) := ∑ j ∈ Finset.Icc 1 n, (j : ZMod (p ^ 2))⁻¹

private lemma H_succ (p n : ℕ) :
    H p (n + 1) = H p n + ((n + 1 : ℕ) : ZMod (p ^ 2))⁻¹ := by
  unfold H
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- `C(p-1,k) = (-1)^k * (1 - p*H_k)` in `ZMod (p^2)` for `k < p`. -/
private lemma choose_pred_zmod {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : k < p) :
    (((p - 1).choose k : ℕ) : ZMod (p ^ 2)) =
      (-1 : ZMod (p ^ 2)) ^ k * (1 - (p : ZMod (p ^ 2)) * H p k) := by
  induction k with
  | zero => simp [H]
  | succ k ih =>
    have ih' := ih (by omega)
    have hch : (p - 1).choose (k + 1) * (k + 1) = (p - 1).choose k * (p - (k + 1)) := by
      have h := Nat.choose_succ_right_eq (p - 1) k
      rwa [show p - 1 - k = p - (k + 1) by omega] at h
    have hchZ : (((p - 1).choose (k + 1) : ℕ) : ZMod (p ^ 2)) * ((k + 1 : ℕ) : ZMod (p ^ 2)) =
        (-1 : ZMod (p ^ 2)) ^ k * (1 - (p : ZMod (p ^ 2)) * H p k) *
          ((p : ZMod (p ^ 2)) - ((k + 1 : ℕ) : ZMod (p ^ 2))) := by
      rw [← ih', ← Nat.cast_sub (show k + 1 ≤ p by omega), ← Nat.cast_mul, ← Nat.cast_mul, hch]
    rw [H_succ, pow_succ (-1 : ZMod (p ^ 2)) k]
    exact ring_step1 _ _ _ _ _ _ (mul_inv_p2 hp (by omega) hk) hchZ (p_sq_zero p)

/-- `C(p+j,j) = 1 + p*H_j` in `ZMod (p^2)` for `j < p`. -/
private lemma choose_add_zmod {p : ℕ} (hp : p.Prime) (j : ℕ) (hj : j < p) :
    (((p + j).choose j : ℕ) : ZMod (p ^ 2)) = 1 + (p : ZMod (p ^ 2)) * H p j := by
  induction j with
  | zero => simp [H]
  | succ j ih =>
    have ih' := ih (by omega)
    have hch : (p + (j + 1)) * (p + j).choose j = (p + (j + 1)).choose (j + 1) * (j + 1) :=
      Nat.add_one_mul_choose_eq (p + j) j
    have hchZ : ((p : ZMod (p ^ 2)) + ((j + 1 : ℕ) : ZMod (p ^ 2))) *
        (((p + j).choose j : ℕ) : ZMod (p ^ 2)) =
        (((p + (j + 1)).choose (j + 1) : ℕ) : ZMod (p ^ 2)) * ((j + 1 : ℕ) : ZMod (p ^ 2)) := by
      rw [← Nat.cast_add, ← Nat.cast_mul, ← Nat.cast_mul, hch]
    rw [H_succ]
    exact ring_step2 _ _ _ _ _ _ (mul_inv_p2 hp (by omega) hj) hchZ ih' (p_sq_zero p)

/-- For `j + 1 < p`: `C(p+j,j+1) = p * e` with `e = (j+1)^(-1) * (1 + p*H_j)` in `ZMod (p^2)`. -/
private lemma choose_div_zmod {p : ℕ} (hp : p.Prime) (j : ℕ) (hj : j + 1 < p) :
    ∃ e : ℕ, (p + j).choose (j + 1) = p * e ∧
      (e : ZMod (p ^ 2)) =
        ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹ * (1 + (p : ZMod (p ^ 2)) * H p j) := by
  have hch : (p + j).choose (j + 1) * (j + 1) = (p + j).choose j * p := by
    have h := Nat.choose_succ_right_eq (p + j) j
    rwa [Nat.add_sub_cancel] at h
  have hcop : Nat.Coprime p (j + 1) :=
    hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hj)
  have hd : p ∣ (p + j).choose (j + 1) * (j + 1) := by
    rw [hch]
    exact dvd_mul_left p _
  obtain ⟨e, he⟩ := hcop.dvd_of_dvd_mul_right hd
  have he2 : e * (j + 1) = (p + j).choose j := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    rw [← mul_assoc, ← he, hch]
    exact mul_comm _ _
  refine ⟨e, he, ?_⟩
  have heZ : (e : ZMod (p ^ 2)) * ((j + 1 : ℕ) : ZMod (p ^ 2)) =
      1 + (p : ZMod (p ^ 2)) * H p j := by
    rw [← choose_add_zmod hp j (by omega), ← Nat.cast_mul, he2]
  exact ring_step3 _ _ _ _ (mul_inv_p2 hp (by omega) hj) heZ

/-- For `k = j + 1 < p`: `C(p-1,k) * C(p-1+k,k)^2 = p^2 * t` with
`t = (-1)^k * k^(-2) * (1 + p*H_(k-1) - p/k)` in `ZMod (p^2)`. -/
private lemma key_term {p : ℕ} (hp : p.Prime) (j : ℕ) (hj : j + 1 < p) :
    ∃ t : ℤ, ((p - 1).choose (j + 1) : ℤ) * ((p - 1 + (j + 1)).choose (j + 1) : ℤ) ^ 2 =
        (p : ℤ) ^ 2 * t ∧
      (t : ZMod (p ^ 2)) = (-1 : ZMod (p ^ 2)) ^ (j + 1) *
        (((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹) ^ 2 *
          (1 + (p : ZMod (p ^ 2)) * H p j -
            (p : ZMod (p ^ 2)) * ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹) := by
  obtain ⟨e, he, heR⟩ := choose_div_zmod hp j hj
  have hidx : p - 1 + (j + 1) = p + j := by
    have := hp.pos
    omega
  refine ⟨((p - 1).choose (j + 1) : ℤ) * (e : ℤ) ^ 2, ?_, ?_⟩
  · rw [hidx, he]
    push_cast
    ring
  · rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_natCast,
      choose_pred_zmod hp (j + 1) hj, heR, H_succ]
    exact ring_term _ _ _ _ (p_sq_zero p)

/-! ### Power sums modulo `p` and their lifts to `ZMod (p^2)` -/

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

/-- `Sum_{k=1..p-1} k^(-d) = 0` in `ZMod p` for `0 < d < p - 1`. -/
private lemma sum_inv_pow_zmod_p {p : ℕ} (hp : p.Prime) (d : ℕ) (hd0 : 0 < d) (hd : d < p - 1) :
    ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ d = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : (fun x : ZMod p => (x⁻¹) ^ d) 0 = 0 := by
    show ((0 : ZMod p)⁻¹) ^ d = 0
    rw [inv_zero, zero_pow hd0.ne']
  refine (sum_Icc_eq_sum_univ (fun x : ZMod p => (x⁻¹) ^ d) hf).trans ?_
  have hinv : ∑ x : ZMod p, (x⁻¹) ^ d = ∑ x : ZMod p, x ^ d :=
    Equiv.sum_comp (Equiv.inv (ZMod p)) (fun x => x ^ d)
  rw [hinv]
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) d (by rw [ZMod.card]; exact hd)

/-- The reduction `ZMod (p^2) → ZMod p` sends the inverse of `k` to the inverse of `k`. -/
private lemma castHom_inv {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) ((k : ZMod (p ^ 2))⁻¹) =
      (k : ZMod p)⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  have hm := congrArg (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))
    (mul_inv_p2 hp hk0 hkp)
  simp only [map_mul, map_one, map_natCast] at hm
  have hkne : (k : ZMod p) ≠ 0 := fun h =>
    Nat.not_dvd_of_pos_of_lt hk0 hkp ((ZMod.natCast_eq_zero_iff k p).mp h)
  exact mul_left_cancel₀ hkne (by rw [hm, mul_inv_cancel₀ hkne])

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

/-- `p * Sum_{k=1..p-1} k^(-d) = 0` in `ZMod (p^2)` for `0 < d < p - 1`. -/
private lemma p_mul_sum_inv_pow {p : ℕ} (hp : p.Prime) (d : ℕ) (hd0 : 0 < d) (hd : d < p - 1) :
    (p : ZMod (p ^ 2)) * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ d = 0 := by
  apply p_mul_eq_zero_of_castHom hp
  rw [map_sum]
  refine Eq.trans ?_ (sum_inv_pow_zmod_p hp d hd0 hd)
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_Icc] at hk
  rw [map_pow, castHom_inv hp (by omega) (by omega)]

/-- The reflection `k -> p - k` of a sum over `k = 1..p-1`. -/
private lemma sum_reflect {M : Type*} [AddCommMonoid M] (p : ℕ) (f : ℕ → M) :
    ∑ k ∈ Finset.Icc 1 (p - 1), f k = ∑ k ∈ Finset.Icc 1 (p - 1), f (p - k) := by
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

/-- `Sum_{k=1..p-1} k^(-d) = 0` in `ZMod (p^2)` for odd `d` with `d + 1 < p - 1`. -/
private lemma sum_inv_odd_pow_p2 {p : ℕ} (hp : p.Prime) (d : ℕ) (hd : Odd d)
    (hdp : d + 1 < p - 1) :
    ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ d = 0 := by
  have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
      ((k : ZMod (p ^ 2))⁻¹) ^ d + (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ d =
        -((d : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ (d + 1))) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have h1 := mul_inv_p2 hp (k := k) (by omega) (by omega)
    have h2 := mul_inv_p2 hp (k := p - k) (by omega) (by omega)
    have hcast : ((p - k : ℕ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) - (k : ZMod (p ^ 2)) :=
      Nat.cast_sub (by omega)
    rw [hcast] at h2 ⊢
    exact ring_reflect _ _ _ _ h1 h2 (p_sq_zero p) d hd
  have h2S : 2 * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ d = 0 := by
    calc 2 * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ d
        = ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ d +
            ∑ k ∈ Finset.Icc 1 (p - 1), (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ d := by
          rw [two_mul]
          congr 1
          exact sum_reflect p (fun k => ((k : ZMod (p ^ 2))⁻¹) ^ d)
      _ = ∑ k ∈ Finset.Icc 1 (p - 1),
            (((k : ZMod (p ^ 2))⁻¹) ^ d + (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ d) :=
          Finset.sum_add_distrib.symm
      _ = ∑ k ∈ Finset.Icc 1 (p - 1),
            -((d : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ (d + 1))) :=
          Finset.sum_congr rfl hterm
      _ = -((d : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) *
            ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ (d + 1))) := by
          rw [Finset.sum_neg_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = 0 := by
          rw [p_mul_sum_inv_pow hp (d + 1) (by omega) hdp, mul_zero, neg_zero]
  have h2u : IsUnit (2 : ZMod (p ^ 2)) := by
    have h := (ZMod.isUnit_iff_coprime 2 (p ^ 2)).mpr (coprime_p2 hp (by norm_num) (by omega))
    exact_mod_cast h
  exact h2u.mul_left_cancel (by rw [h2S, mul_zero])

/-- The harmonic number `G_r = Sum_{j=1..r} 1/j` in `ZMod p`. -/
private def G (p r : ℕ) : ZMod p := ∑ j ∈ Finset.Icc 1 r, (j : ZMod p)⁻¹

private lemma G_succ (p r : ℕ) : G p (r + 1) = G p r + ((r + 1 : ℕ) : ZMod p)⁻¹ := by
  unfold G
  rw [Finset.sum_Icc_succ_top (by omega)]

private lemma cast_sub_zmod_p (p k : ℕ) (hk : k ≤ p) :
    ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
  rw [Nat.cast_sub hk, ZMod.natCast_self, zero_sub]

/-- `G_(p-1-r) = G_r` in `ZMod p` for `r <= p - 1`. -/
private lemma G_symm {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (r : ℕ) (hr : r ≤ p - 1) :
    G p (p - 1 - r) = G p r := by
  have : Fact p.Prime := ⟨hp⟩
  induction r with
  | zero =>
    have h := sum_inv_pow_zmod_p hp 1 one_pos (by omega)
    simp only [pow_one] at h
    show G p (p - 1) = G p 0
    unfold G
    rw [h]
    simp
  | succ r ih =>
    have h1 := ih (by omega)
    have h2 := G_succ p (p - 1 - (r + 1))
    rw [show p - 1 - (r + 1) + 1 = p - (r + 1) by omega,
      cast_sub_zmod_p p (r + 1) (by omega), inv_neg] at h2
    rw [show p - 1 - r = p - (r + 1) by omega] at h1
    rw [G_succ p r]
    linear_combination h1 - h2

/-- `Sum_{k=1..p-1} k^(-d) * G_(k-1) = 0` in `ZMod p` for odd `d` with `d + 1 < p - 1`. -/
private lemma sum_inv_odd_pow_mul_G {p : ℕ} (hp : p.Prime) (d : ℕ) (hd : Odd d)
    (hdp : d + 1 < p - 1) :
    ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ d * G p (k - 1) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
      (((p - k : ℕ) : ZMod p)⁻¹) ^ d * G p (p - k - 1) =
        -(((k : ZMod p)⁻¹) ^ d * G p (k - 1)) - ((k : ZMod p)⁻¹) ^ (d + 1) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hs := G_symm hp (by omega) k hk.2
    have hk1 := G_succ p (k - 1)
    rw [show k - 1 + 1 = k by omega] at hk1
    rw [show p - k - 1 = p - 1 - k by omega, hs, hk1, cast_sub_zmod_p p k (by omega), inv_neg,
      hd.neg_pow, pow_succ ((k : ZMod p)⁻¹) d]
    ring
  have hS : ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ d * G p (k - 1) =
      ∑ k ∈ Finset.Icc 1 (p - 1),
        (-(((k : ZMod p)⁻¹) ^ d * G p (k - 1)) - ((k : ZMod p)⁻¹) ^ (d + 1)) :=
    (sum_reflect p (fun k => ((k : ZMod p)⁻¹) ^ d * G p (k - 1))).trans
      (Finset.sum_congr rfl hterm)
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    sum_inv_pow_zmod_p hp (d + 1) (by omega) hdp, sub_zero] at hS
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 p).mp h')
    omega
  have h2S : (2 : ZMod p) *
      ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ d * G p (k - 1) = 0 := by
    linear_combination hS
  exact (mul_eq_zero.mp h2S).resolve_left h2ne

private lemma castHom_H {p : ℕ} (hp : p.Prime) (r : ℕ) (hr : r < p) :
    ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) (H p r) = G p r := by
  unfold H G
  rw [map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_Icc] at hj
  exact castHom_inv hp (by omega) (by omega)

/-- `p * Sum_{k=1..p-1} k^(-d) * H_(k-1) = 0` in `ZMod (p^2)` for odd `d` with `d + 1 < p - 1`. -/
private lemma p_mul_sum_inv_odd_pow_mul_H {p : ℕ} (hp : p.Prime) (d : ℕ) (hd : Odd d)
    (hdp : d + 1 < p - 1) :
    (p : ZMod (p ^ 2)) *
      ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ d * H p (k - 1) = 0 := by
  apply p_mul_eq_zero_of_castHom hp
  rw [map_sum]
  refine Eq.trans ?_ (sum_inv_odd_pow_mul_G hp d hd hdp)
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_Icc] at hk
  rw [map_mul, map_pow, castHom_inv hp (by omega) (by omega), castHom_H hp (k - 1) (by omega)]

/-! ### The numerator -/

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

/-- Claim 1: for odd `m` and every prime `p > m + 4`, `p^4` divides `S_m(p-1)`. -/
private lemma general (m p : ℕ) (hm : Odd m) (hp : p.Prime) (hmp : m + 4 < p) :
    ((p : ℤ) ^ 4) ∣ OMA.S_oeis_a357561.S m (p - 1) := by
  have hpev : Even (p - 1) := hp.even_sub_one (by omega)
  -- the integers `t k` with `C(p-1,k) * C(p-1+k,k)^2 = p^2 * t k`
  have hex : ∀ k : ℕ, ∃ t : ℤ, 1 ≤ k → k < p →
      (((p - 1).choose k : ℤ) * ((p - 1 + k).choose k : ℤ) ^ 2 = (p : ℤ) ^ 2 * t ∧
        (t : ZMod (p ^ 2)) = (-1 : ZMod (p ^ 2)) ^ k * ((k : ZMod (p ^ 2))⁻¹) ^ 2 *
          (1 + (p : ZMod (p ^ 2)) * H p (k - 1) -
            (p : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹)) := by
    intro k
    by_cases hk : 1 ≤ k ∧ k < p
    · obtain ⟨hk1, hkp⟩ := hk
      have h := key_term hp (k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at h
      obtain ⟨t, h1, h2⟩ := h
      exact ⟨t, fun _ _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
  choose t ht using hex
  -- the integers `c k = ((p-1)! / k)^m`
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ, ∀ k ∈ Finset.Icc 1 (p - 1),
      k ^ m * c k = (p - 1).factorial ^ m :=
    ⟨fun k => ((p - 1).factorial / k) ^ m, fun k hk => by
      simp only [Finset.mem_Icc] at hk
      show k ^ m * ((p - 1).factorial / k) ^ m = (p - 1).factorial ^ m
      rw [← mul_pow, Nat.mul_div_cancel' (Nat.dvd_factorial (by omega) hk.2)]⟩
  -- `p^2` divides `Sum (-1)^(p-1+k) * c_k * t_k`
  have hS : ((p : ℤ) ^ 2) ∣
      ∑ k ∈ Finset.Icc 1 (p - 1), (-1 : ℤ) ^ (p - 1 + k) * ((c k : ℤ) * t k) := by
    have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
        (-1 : ZMod (p ^ 2)) ^ (p - 1 + k) * ((c k : ZMod (p ^ 2)) * ((t k : ℤ) : ZMod (p ^ 2))) =
          (((p - 1).factorial ^ m : ℕ) : ZMod (p ^ 2)) *
            (((k : ZMod (p ^ 2))⁻¹) ^ (m + 2) +
              (p : ZMod (p ^ 2)) * (((k : ZMod (p ^ 2))⁻¹) ^ (m + 2) * H p (k - 1)) -
              (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ (m + 3)) := by
      intro k hk
      have hck := congrArg (Nat.cast (R := ZMod (p ^ 2))) (hc k hk)
      rw [Nat.cast_mul, Nat.cast_pow] at hck
      simp only [Finset.mem_Icc] at hk
      have h1 := mul_inv_p2 hp (k := k) (by omega) (by omega)
      rw [(ht k hk.1 (by omega)).2]
      exact ring_final _ _ _ _ _ _ _ _ m h1 hck (neg_one_pow_add_mul_cancel (p - 1) k hpev)
    have hA := sum_inv_odd_pow_p2 hp (m + 2) (hm.add_even even_two) (by omega)
    have hB := p_mul_sum_inv_odd_pow_mul_H hp (m + 2) (hm.add_even even_two) (by omega)
    have hC := p_mul_sum_inv_pow hp (m + 3) (by omega) (by omega)
    have hcast : ((∑ k ∈ Finset.Icc 1 (p - 1), (-1 : ℤ) ^ (p - 1 + k) * ((c k : ℤ) * t k) : ℤ) :
        ZMod (p ^ 2)) = 0 := by
      push_cast
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hA, hB, hC]
      ring
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
    exact_mod_cast h
  obtain ⟨N, hN⟩ := hS
  have hNq : ∑ k ∈ Finset.Icc 1 (p - 1), (-1 : ℚ) ^ (p - 1 + k) * ((c k : ℚ) * (t k : ℚ)) =
      (p : ℚ) ^ 2 * (N : ℚ) := by
    have h := congrArg (Int.cast (R := ℚ)) hN
    push_cast at h
    exact h
  -- `s_m(p-1) * ((p-1)!)^m = p^2 * Sum (-1)^(p-1+k) * c_k * t_k`
  have hsum : OMA.S_oeis_a357561.s m (p - 1) * (((p - 1).factorial ^ m : ℕ) : ℚ) =
      (p : ℚ) ^ 2 *
        ∑ k ∈ Finset.Icc 1 (p - 1), (-1 : ℚ) ^ (p - 1 + k) * ((c k : ℚ) * (t k : ℚ)) := by
    unfold OMA.S_oeis_a357561.s
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hD : (((p - 1).factorial ^ m : ℕ) : ℚ) = (k : ℚ) ^ m * (c k : ℚ) := by
      rw [← Nat.cast_pow, ← Nat.cast_mul, hc k hk]
    simp only [Finset.mem_Icc] at hk
    obtain ⟨h1, -⟩ := ht k hk.1 (by omega)
    have hk0 : (k : ℚ) ^ m ≠ 0 := pow_ne_zero m (Nat.cast_ne_zero.mpr (by omega))
    have h1q : ((p - 1).choose k : ℚ) * ((p - 1 + k).choose k : ℚ) ^ 2 =
        (p : ℚ) ^ 2 * (t k : ℚ) := by
      exact_mod_cast h1
    rw [hD]
    calc (-1 : ℚ) ^ (p - 1 + k) * (1 / (k : ℚ) ^ m) * ((p - 1).choose k : ℚ) *
          ((p - 1 + k).choose k : ℚ) ^ 2 * ((k : ℚ) ^ m * (c k : ℚ))
        = (-1 : ℚ) ^ (p - 1 + k) * ((1 / (k : ℚ) ^ m) * (k : ℚ) ^ m) * (c k : ℚ) *
            (((p - 1).choose k : ℚ) * ((p - 1 + k).choose k : ℚ) ^ 2) := by ring
      _ = (p : ℚ) ^ 2 * ((-1 : ℚ) ^ (p - 1 + k) * ((c k : ℚ) * (t k : ℚ))) := by
          rw [one_div_mul_cancel hk0, h1q]
          ring
  have hq : OMA.S_oeis_a357561.s m (p - 1) * (((p - 1).factorial ^ m : ℕ) : ℚ) =
      (p : ℚ) ^ 4 * (N : ℚ) := by
    rw [hsum, hNq]
    ring
  have hcop : Nat.Coprime p ((p - 1).factorial ^ m) :=
    (hp.coprime_iff_not_dvd.mpr (fun hd => by
      have := hp.dvd_factorial.mp hd
      omega)).pow_right m
  show ((p : ℤ) ^ 4) ∣ (OMA.S_oeis_a357561.s m (p - 1)).num
  exact num_dvd_aux _ _ N hcop hq

/-- The case `p = 5` of claim 2: `s_3(4) = -15625/432` and `15625 = 5^6`. -/
private lemma case_five : (((5 : ℕ) : ℤ) ^ 4) ∣ OMA.S_oeis_a357561.a (5 - 1) := by
  have hs : OMA.S_oeis_a357561.s 3 4 * ((432 : ℕ) : ℚ) =
      ((5 : ℕ) : ℚ) ^ 4 * ((-25 : ℤ) : ℚ) := by
    unfold OMA.S_oeis_a357561.s
    rw [show (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} by decide]
    norm_num [Finset.sum_insert, Nat.choose]
  show (((5 : ℕ) : ℤ) ^ 4) ∣ (OMA.S_oeis_a357561.s 3 4).num
  exact num_dvd_aux (OMA.S_oeis_a357561.s 3 4) 432 (-25) (by norm_num) hs

theorem OMA.solution : type_of% @OMA.S_oeis_a357561.main := by
  refine ⟨fun m p hm hp hmp => general m p hm hp hmp, ?_⟩
  rintro p hp (rfl | h11)
  · exact case_five
  · exact general 3 p ⟨1, rfl⟩ hp (by omega)
