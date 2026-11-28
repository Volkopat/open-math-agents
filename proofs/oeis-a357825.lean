import OMAStatements.S_oeis_a357825
import Mathlib

/-!
# A357825: `a(2*p-1) == 1 (mod p^3)` for every prime `p >= 5` (conjecture of Peter Bala, Mar 20 2023)

`a(n) = Sum_{j=0..floor(n/2)} b(n, n-2*j)^n`, where `b(x,y)` counts the semi-Dyck paths from `(0,0)`
to `(x,y)`.

Proof. Put `n = 2*p - 1` and work in `R = ZMod (p^3)`, where `P = p` satisfies `P^3 = 0`.

* L0 (ballot numbers). By induction on `x`: `b x x = 1` and
  `b x (x - 2*(j+1)) + C(x,j) = C(x,j+1)` for `2*(j+1) <= x + 1`. Hence
  `a(n) = 1 + Sum_{k < p-1} (C(n,k+1) - C(n,k))^n`.
* L1, L2. With `x_k = 1/(k+1)`, `H k = Sum_{i<k} x_i`, `Hq k = Sum_{i<k} x_i^2` and
  `G k = Prod_{i<k} (1 - 2*P*x_i)`: `G k = 1 - 2*P*H k + 2*P^2*((H k)^2 - Hq k)`, and
  `C(n,k) = (-1)^k * G k` in `R` for `k < p` (from `C(n,k+1)*(k+1) = C(n,k)*(n-k)`).
* L3. `C(n,k+1) - C(n,k) = 2*(-1)^(k+1) * e_k` with `e_k = G k * (1 - P*x_k) = 1 + P*w_k`.
* L4. `(1 + P*w)^(2p-1) = 1 - P*w + P^2*(w^2 + 2*w)`, from `(1 + P*w)^p = 1 + P^2*w` and the inverse
  `1 - P*w + P^2*w^2`. So
  `e_k^n = 1 + P*(2*H k + x_k) + P^2*((H k)^2 + (H (k+1))^2 + 2*Hq k - 2*(2*H k + x_k))`.
* L5 (telescoping). `Sum_{k<m} (-1)^(k+1) * (e_k^n - 1)
  = (-1)^m * (P*H m + P^2*((H m)^2 + Hq m - 2*H m)) - P^2 * Q m`, `Q m = Sum_{k<m} (-1)^(k+1)*x_k^2`.
* L6. `P^2 * Hq (p-1) = 0`: modulo `p` the sum of the inverse squares of the nonzero residues is
  the sum of their squares, which vanishes because `2 < p - 1`.
* L7. `P * H (p-1) = 0` (Wolstenholme): pairing `j` with `p - j` gives
  `2*P*H (p-1) = -P^2 * Hq (p-1)`.
* L8. `P^2 * Q (p-1) = 0`: the pairing `j <-> p - j` changes the sign.

Since `p - 1` is even, `Sum_{k<p-1} (-1)^(k+1) = 0`, and the signed sum of the `e_k^n` vanishes in `R`;
therefore `a(n) = 1 + 2^n * 0 = 1` in `ZMod (p^3)`.
-/

namespace A357825

open Finset OMA.S_oeis_a357825

/-! ## L0: the ballot formula for the path counts -/

private lemma b_zero (y : ℤ) : b 0 y = if y = 0 then 1 else 0 := by
  rw [b]

private lemma b_succ (x : ℕ) (y : ℤ) :
    b (x + 1) y = if y < 0 ∨ ((x : ℤ) + 1) < y then 0 else b x (y - 1) + b x (y + 1) := by
  rw [b]

private lemma b_of_lt (x : ℕ) (y : ℤ) (h : (x : ℤ) < y) : b x y = 0 := by
  cases x with
  | zero =>
    rw [b_zero, if_neg]
    intro h0
    rw [h0] at h
    simp at h
  | succ x =>
    rw [b_succ, if_pos]
    right
    push_cast at h
    exact h

private lemma b_of_neg (x : ℕ) (y : ℤ) (h : y < 0) : b x y = 0 := by
  cases x with
  | zero =>
    rw [b_zero, if_neg]
    omega
  | succ x =>
    rw [b_succ, if_pos (Or.inl h)]

private lemma b_ballot (x : ℕ) :
    b x (x : ℤ) = 1 ∧
      ∀ j : ℕ, 2 * (j + 1) ≤ x + 1 →
        b x ((x : ℤ) - 2 * ((j : ℤ) + 1)) + x.choose j = x.choose (j + 1) := by
  induction x with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [b_zero]; simp
    · intro j hj
      omega
  | succ x ih =>
    obtain ⟨ihA, ihB⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [b_succ, if_neg (by push_cast; omega)]
      have h1 : ((x + 1 : ℕ) : ℤ) - 1 = (x : ℤ) := by push_cast; ring
      rw [h1, ihA, b_of_lt x _ (by push_cast; omega)]
    · intro j hj
      by_cases hb : 2 * (j + 1) = x + 2
      · rw [b_of_neg _ _ (by push_cast; omega), zero_add]
        have hx : x + 1 = 2 * j + 1 := by omega
        rw [hx]
        exact (Nat.choose_symm_half j).symm
      · have hle : 2 * (j + 1) ≤ x + 1 := by omega
        rw [b_succ, if_neg (by push_cast; omega)]
        have e1 : ((x + 1 : ℕ) : ℤ) - 2 * ((j : ℤ) + 1) - 1 = (x : ℤ) - 2 * ((j : ℤ) + 1) := by
          push_cast; ring
        rw [e1]
        have hB1 := ihB j hle
        cases j with
        | zero =>
          have e2 : ((x + 1 : ℕ) : ℤ) - 2 * (((0 : ℕ) : ℤ) + 1) + 1 = (x : ℤ) := by
            push_cast; ring
          rw [e2, ihA]
          simp only [Nat.choose_zero_right, zero_add, Nat.choose_one_right] at hB1 ⊢
          omega
        | succ j' =>
          have e2 : ((x + 1 : ℕ) : ℤ) - 2 * (((j' + 1 : ℕ) : ℤ) + 1) + 1 =
              (x : ℤ) - 2 * ((j' : ℤ) + 1) := by
            push_cast; ring
          rw [e2]
          have hB2 := ihB j' (by omega)
          have p1 : (x + 1).choose (j' + 1) = x.choose j' + x.choose (j' + 1) :=
            Nat.choose_succ_succ x j'
          have p2 : (x + 1).choose (j' + 1 + 1) = x.choose (j' + 1) + x.choose (j' + 1 + 1) :=
            Nat.choose_succ_succ x (j' + 1)
          omega

private lemma a_eq (n : ℕ) :
    a n = 1 + ∑ k ∈ range (n / 2), ((n.choose (k + 1) : ℤ) - (n.choose k : ℤ)) ^ n := by
  unfold a
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · have h0 : (n : ℤ) - 2 * ((0 : ℕ) : ℤ) = (n : ℤ) := by simp
    rw [h0, (b_ballot n).1]
    simp
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    have hB := (b_ballot n).2 k (by omega)
    have h1 : (n : ℤ) - 2 * ((k + 1 : ℕ) : ℤ) = (n : ℤ) - 2 * ((k : ℤ) + 1) := by
      push_cast; ring
    rw [h1]
    have hBz : ((b n ((n : ℤ) - 2 * ((k : ℤ) + 1)) : ℕ) : ℤ) + (n.choose k : ℤ) =
        (n.choose (k + 1) : ℤ) := by
      exact_mod_cast hB
    rw [← hBz]
    ring

/-! ## Algebra in a commutative ring with `P ^ 3 = 0` -/

section alg

variable {R : Type*} [CommRing R]

private def Hs (x : ℕ → R) (k : ℕ) : R := ∑ i ∈ range k, x i

private def Hq (x : ℕ → R) (k : ℕ) : R := ∑ i ∈ range k, x i ^ 2

private def Gs (P : R) (x : ℕ → R) (k : ℕ) : R := ∏ i ∈ range k, (1 - 2 * P * x i)

private def Qs (x : ℕ → R) (k : ℕ) : R := ∑ i ∈ range k, (-1) ^ (i + 1) * x i ^ 2

private lemma Hs_succ (x : ℕ → R) (k : ℕ) : Hs x (k + 1) = Hs x k + x k := by
  unfold Hs; rw [sum_range_succ]

private lemma Hq_succ (x : ℕ → R) (k : ℕ) : Hq x (k + 1) = Hq x k + x k ^ 2 := by
  unfold Hq; rw [sum_range_succ]

private lemma Gs_succ (P : R) (x : ℕ → R) (k : ℕ) :
    Gs P x (k + 1) = Gs P x k * (1 - 2 * P * x k) := by
  unfold Gs; rw [prod_range_succ]

private lemma Qs_succ (x : ℕ → R) (k : ℕ) :
    Qs x (k + 1) = Qs x k + (-1) ^ (k + 1) * x k ^ 2 := by
  unfold Qs; rw [sum_range_succ]

/-- L1 -/
private lemma Gs_eq (P : R) (h3 : P ^ 3 = 0) (x : ℕ → R) (k : ℕ) :
    Gs P x k = 1 - 2 * P * Hs x k + 2 * P ^ 2 * (Hs x k ^ 2 - Hq x k) := by
  induction k with
  | zero => simp [Gs, Hs, Hq]
  | succ k ih =>
    rw [Gs_succ, ih, Hs_succ, Hq_succ]
    linear_combination (-4 * x k * (Hs x k ^ 2 - Hq x k)) * h3

private lemma one_add_pow_of_cube (y : R) (hy : y ^ 3 = 0) (m : ℕ) :
    (1 + y) ^ m = 1 + (m : R) * y + (m.choose 2 : R) * y ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hc : (m + 1).choose 2 = m.choose 1 + m.choose 2 := Nat.choose_succ_succ m 1
    rw [pow_succ, ih, hc, Nat.choose_one_right]
    push_cast
    linear_combination (m.choose 2 : R) * hy

private lemma pow_p {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (P w : R) (hpP : (p : R) = P)
    (h3 : P ^ 3 = 0) : (1 + P * w) ^ p = 1 + P ^ 2 * w := by
  have hy : (P * w) ^ 3 = 0 := by rw [mul_pow, h3, zero_mul]
  rw [one_add_pow_of_cube _ hy p]
  obtain ⟨c, hc⟩ := hp.dvd_choose_self (k := 2) (by norm_num) hp2
  rw [hc]
  push_cast
  rw [hpP]
  linear_combination (c : R) * w ^ 2 * h3

/-- L4 -/
private lemma pow_two_p_sub_one {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (P w : R)
    (hpP : (p : R) = P) (h3 : P ^ 3 = 0) :
    (1 + P * w) ^ (2 * p - 1) = 1 - P * w + P ^ 2 * (w ^ 2 + 2 * w) := by
  have hinv : (1 + P * w) * (1 - P * w + P ^ 2 * w ^ 2) = 1 := by
    linear_combination w ^ 3 * h3
  have h2p : (1 + P * w) ^ (2 * p - 1) * (1 + P * w) = (1 + P ^ 2 * w) ^ 2 := by
    rw [← pow_succ, show 2 * p - 1 + 1 = p * 2 by omega, pow_mul, pow_p hp hp2 P w hpP h3]
  calc (1 + P * w) ^ (2 * p - 1)
      = (1 + P * w) ^ (2 * p - 1) * ((1 + P * w) * (1 - P * w + P ^ 2 * w ^ 2)) := by
        rw [hinv, mul_one]
    _ = ((1 + P * w) ^ (2 * p - 1) * (1 + P * w)) * (1 - P * w + P ^ 2 * w ^ 2) := by ring
    _ = (1 + P ^ 2 * w) ^ 2 * (1 - P * w + P ^ 2 * w ^ 2) := by rw [h2p]
    _ = 1 - P * w + P ^ 2 * (w ^ 2 + 2 * w) := by
        linear_combination
          (P ^ 3 * w ^ 4 - P ^ 2 * w ^ 3 + P * (2 * w ^ 3 + w ^ 2) - 2 * w ^ 2) * h3

/-- L3 + L4 -/
private lemma e_pow {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (P : R) (hpP : (p : R) = P)
    (h3 : P ^ 3 = 0) (x : ℕ → R) (k : ℕ) :
    (Gs P x k * (1 - P * x k)) ^ (2 * p - 1) =
      1 + (P * (2 * Hs x k + x k) +
        P ^ 2 * (Hs x k ^ 2 + Hs x (k + 1) ^ 2 + 2 * Hq x k - 2 * (2 * Hs x k + x k))) := by
  have hw : Gs P x k * (1 - P * x k) =
      1 + P * (-(2 * Hs x k + x k) +
        P * (2 * Hs x k ^ 2 - 2 * Hq x k + 2 * Hs x k * x k)) := by
    rw [Gs_eq P h3]
    linear_combination (-2 * x k * (Hs x k ^ 2 - Hq x k)) * h3
  rw [hw, pow_two_p_sub_one hp hp2 P _ hpP h3, Hs_succ]
  linear_combination
    (-2 * (2 * Hs x k + x k) * (2 * Hs x k ^ 2 - 2 * Hq x k + 2 * Hs x k * x k) +
      P * (2 * Hs x k ^ 2 - 2 * Hq x k + 2 * Hs x k * x k) ^ 2 +
      2 * (2 * Hs x k ^ 2 - 2 * Hq x k + 2 * Hs x k * x k)) * h3

/-- L5 -/
private lemma tele (P : R) (x : ℕ → R) (m : ℕ) :
    ∑ k ∈ range m, (-1) ^ (k + 1) *
        (P * (2 * Hs x k + x k) +
          P ^ 2 * (Hs x k ^ 2 + Hs x (k + 1) ^ 2 + 2 * Hq x k - 2 * (2 * Hs x k + x k))) =
      (-1) ^ m * (P * Hs x m + P ^ 2 * (Hs x m ^ 2 + Hq x m - 2 * Hs x m)) - P ^ 2 * Qs x m := by
  induction m with
  | zero => simp [Hs, Hq, Qs]
  | succ m ih =>
    rw [sum_range_succ, ih, Hs_succ, Hq_succ, Qs_succ]
    ring

private lemma sum_signs (j : ℕ) : ∑ k ∈ range (2 * j), (-1 : R) ^ (k + 1) = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : (-1 : R) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
    have e1 : (-1 : R) ^ (2 * j + 1) = -1 := by rw [pow_succ, h1]; ring
    have e2 : (-1 : R) ^ (2 * j + 1 + 1) = 1 := by rw [pow_succ, e1]; ring
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, e1, e2]
    ring

/-- The whole signed sum, for an even number `2 * j` of terms. -/
private lemma signed_sum {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (P : R) (hpP : (p : R) = P)
    (h3 : P ^ 3 = 0) (x : ℕ → R) (j : ℕ) :
    ∑ k ∈ range (2 * j), (-1) ^ (k + 1) * (Gs P x k * (1 - P * x k)) ^ (2 * p - 1) =
      P * Hs x (2 * j) + P ^ 2 * (Hs x (2 * j) ^ 2 + Hq x (2 * j) - 2 * Hs x (2 * j)) -
        P ^ 2 * Qs x (2 * j) := by
  have h1 : (-1 : R) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
  have hterm : ∀ k ∈ range (2 * j),
      (-1 : R) ^ (k + 1) * (Gs P x k * (1 - P * x k)) ^ (2 * p - 1) =
        (-1) ^ (k + 1) + (-1) ^ (k + 1) *
          (P * (2 * Hs x k + x k) +
            P ^ 2 * (Hs x k ^ 2 + Hs x (k + 1) ^ 2 + 2 * Hq x k - 2 * (2 * Hs x k + x k))) := by
    intro k _
    rw [e_pow hp hp2 P hpP h3]
    ring
  rw [sum_congr rfl hterm, sum_add_distrib, sum_signs, tele, h1]
  ring

end alg

/-! ## The ring `ZMod (p ^ 3)` -/

private def xi (p k : ℕ) : ZMod (p ^ 3) := ((k + 1 : ℕ) : ZMod (p ^ 3))⁻¹

private lemma P_cube (p : ℕ) : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

private lemma unit_mul_inv {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k + 1 < p) :
    ((k + 1 : ℕ) : ZMod (p ^ 3)) * xi p k = 1 := by
  unfold xi
  exact ZMod.coe_mul_inv_eq_one (k + 1)
    ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos k) hk)).symm.pow_right 3)

private lemma two_cancel {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) {t : ZMod (p ^ 3)}
    (h : 2 * t = 0) : t = 0 := by
  have hu := unit_mul_inv hp (k := 1) (by omega)
  push_cast at hu
  linear_combination (xi p 1) * h - t * hu

/-- L2 -/
private lemma choose_eq {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : k < p) :
    (((2 * p - 1).choose k : ℕ) : ZMod (p ^ 3)) =
      (-1) ^ k * Gs (p : ZMod (p ^ 3)) (xi p) k := by
  induction k with
  | zero => simp [Gs]
  | succ k ih =>
    have ih' := ih (by omega)
    have hch : (2 * p - 1).choose (k + 1) * (k + 1) =
        (2 * p - 1).choose k * (2 * p - 1 - k) :=
      Nat.choose_succ_right_eq (2 * p - 1) k
    have hsub : 2 * p - 1 - k + (k + 1) = 2 * p := by omega
    have hch' : (2 * p - 1).choose (k + 1) * (k + 1) + (2 * p - 1).choose k * (k + 1) =
        (2 * p - 1).choose k * (2 * p) := by
      rw [hch, ← mul_add, hsub]
    have hZ : (((2 * p - 1).choose (k + 1) : ℕ) : ZMod (p ^ 3)) *
          ((k + 1 : ℕ) : ZMod (p ^ 3)) +
        (((2 * p - 1).choose k : ℕ) : ZMod (p ^ 3)) * ((k + 1 : ℕ) : ZMod (p ^ 3)) =
        (((2 * p - 1).choose k : ℕ) : ZMod (p ^ 3)) * (2 * (p : ZMod (p ^ 3))) := by
      exact_mod_cast congrArg (Nat.cast (R := ZMod (p ^ 3))) hch'
    have hu := unit_mul_inv hp hk
    rw [Gs_succ]
    rw [ih'] at hZ
    linear_combination (xi p k) * hZ -
      ((((2 * p - 1).choose (k + 1) : ℕ) : ZMod (p ^ 3)) +
        (-1) ^ k * Gs (p : ZMod (p ^ 3)) (xi p) k) * hu

/-- Pairing `k + 1` with `p - (k + 1)`. -/
private lemma refl_facts {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k + 1 < p) :
    (p : ZMod (p ^ 3)) ^ 2 * xi p (p - 1 - 1 - k) = -((p : ZMod (p ^ 3)) ^ 2 * xi p k) ∧
    (p : ZMod (p ^ 3)) * (xi p k + xi p (p - 1 - 1 - k)) =
      -((p : ZMod (p ^ 3)) ^ 2 * xi p k ^ 2) ∧
    (p : ZMod (p ^ 3)) ^ 2 * xi p (p - 1 - 1 - k) ^ 2 = (p : ZMod (p ^ 3)) ^ 2 * xi p k ^ 2 := by
  have h3 := P_cube p
  have hy := unit_mul_inv hp hk
  have hz := unit_mul_inv hp (k := p - 1 - 1 - k) (by omega)
  have hcast : ((p - 1 - 1 - k + 1 : ℕ) : ZMod (p ^ 3)) =
      (p : ZMod (p ^ 3)) - ((k + 1 : ℕ) : ZMod (p ^ 3)) := by
    rw [eq_sub_iff_add_eq, ← Nat.cast_add]
    congr 1
    omega
  rw [hcast] at hz
  have r1 : (p : ZMod (p ^ 3)) ^ 2 * xi p (p - 1 - 1 - k) =
      -((p : ZMod (p ^ 3)) ^ 2 * xi p k) := by
    linear_combination (xi p k * xi p (p - 1 - 1 - k)) * h3 -
      ((p : ZMod (p ^ 3)) ^ 2 * xi p (p - 1 - 1 - k)) * hy -
      ((p : ZMod (p ^ 3)) ^ 2 * xi p k) * hz
  refine ⟨r1, ?_, ?_⟩
  · linear_combination (xi p k) * r1 - ((p : ZMod (p ^ 3)) * xi p k) * hz -
      ((p : ZMod (p ^ 3)) * xi p (p - 1 - 1 - k)) * hy
  · linear_combination (xi p (p - 1 - 1 - k) - xi p k) * r1

/-- L7 -/
private lemma P_mul_Hs {p : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (h6 : (p : ZMod (p ^ 3)) ^ 2 * Hq (xi p) (p - 1) = 0) :
    (p : ZMod (p ^ 3)) * Hs (xi p) (p - 1) = 0 := by
  apply two_cancel hp hp2
  have hrefl : Hs (xi p) (p - 1) = ∑ k ∈ range (p - 1), xi p (p - 1 - 1 - k) := by
    unfold Hs
    exact (sum_range_reflect (xi p) (p - 1)).symm
  calc (2 : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) * Hs (xi p) (p - 1))
      = (p : ZMod (p ^ 3)) *
          (Hs (xi p) (p - 1) + ∑ k ∈ range (p - 1), xi p (p - 1 - 1 - k)) := by
        rw [← hrefl]; ring
    _ = ∑ k ∈ range (p - 1), (p : ZMod (p ^ 3)) * (xi p k + xi p (p - 1 - 1 - k)) := by
        unfold Hs
        rw [← sum_add_distrib, mul_sum]
    _ = ∑ k ∈ range (p - 1), -((p : ZMod (p ^ 3)) ^ 2 * xi p k ^ 2) := by
        refine sum_congr rfl fun k hk => ?_
        rw [mem_range] at hk
        exact (refl_facts hp (by omega)).2.1
    _ = -((p : ZMod (p ^ 3)) ^ 2 * Hq (xi p) (p - 1)) := by
        unfold Hq
        rw [sum_neg_distrib, mul_sum]
    _ = 0 := by rw [h6, neg_zero]

/-- L8 -/
private lemma Psq_mul_Qs {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    (p : ZMod (p ^ 3)) ^ 2 * Qs (xi p) (p - 1) = 0 := by
  apply two_cancel hp hp2
  have hrefl : Qs (xi p) (p - 1) =
      ∑ k ∈ range (p - 1), (-1) ^ (p - 1 - 1 - k + 1) * xi p (p - 1 - 1 - k) ^ 2 := by
    unfold Qs
    exact (sum_range_reflect (fun i => (-1 : ZMod (p ^ 3)) ^ (i + 1) * xi p i ^ 2) (p - 1)).symm
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  calc 2 * ((p : ZMod (p ^ 3)) ^ 2 * Qs (xi p) (p - 1))
      = (p : ZMod (p ^ 3)) ^ 2 * Qs (xi p) (p - 1) +
          (p : ZMod (p ^ 3)) ^ 2 *
            ∑ k ∈ range (p - 1), (-1) ^ (p - 1 - 1 - k + 1) * xi p (p - 1 - 1 - k) ^ 2 := by
        rw [← hrefl]; ring
    _ = ∑ k ∈ range (p - 1),
          ((p : ZMod (p ^ 3)) ^ 2 * ((-1) ^ (k + 1) * xi p k ^ 2) +
            (p : ZMod (p ^ 3)) ^ 2 *
              ((-1) ^ (p - 1 - 1 - k + 1) * xi p (p - 1 - 1 - k) ^ 2)) := by
        unfold Qs
        rw [mul_sum, mul_sum, ← sum_add_distrib]
    _ = ∑ k ∈ range (p - 1), (0 : ZMod (p ^ 3)) := by
        refine sum_congr rfl fun k hk => ?_
        rw [mem_range] at hk
        have r3 := (refl_facts hp (k := k) (by omega)).2.2
        have hpk : (-1 : ZMod (p ^ 3)) ^ (p - 1 - 1 - k + 1) * (-1) ^ (k + 1) = -1 := by
          rw [← pow_add, show p - 1 - 1 - k + 1 + (k + 1) = p by omega]
          exact hodd.neg_one_pow
        have hsq : ((-1 : ZMod (p ^ 3)) ^ (k + 1)) * ((-1) ^ (k + 1)) = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]
          norm_num
        have hsign : (-1 : ZMod (p ^ 3)) ^ (p - 1 - 1 - k + 1) = -(-1) ^ (k + 1) := by
          linear_combination ((-1 : ZMod (p ^ 3)) ^ (k + 1)) * hpk -
            ((-1 : ZMod (p ^ 3)) ^ (p - 1 - 1 - k + 1)) * hsq
        rw [hsign]
        linear_combination (-(-1 : ZMod (p ^ 3)) ^ (k + 1)) * r3
    _ = 0 := by simp

private lemma cast_zero_imp {p : ℕ} (hp : p.Prime) (t : ZMod (p ^ 3))
    (h : ZMod.castHom (dvd_pow_self p (by norm_num : (3 : ℕ) ≠ 0)) (ZMod p) t = 0) :
    (p : ZMod (p ^ 3)) ^ 2 * t = 0 := by
  have : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h
  obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff _ _).mp h
  rw [← ZMod.natCast_zmod_val t, hc, ← Nat.cast_pow, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  exact ⟨c, by ring⟩

private lemma sum_inv_sq_zmod {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ k ∈ range (p - 1), (((k + 1 : ℕ) : ZMod p)⁻¹) ^ 2 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hall : ∑ y : ZMod p, (y⁻¹) ^ 2 = 0 := by
    have h1 : ∑ y : ZMod p, (y⁻¹) ^ 2 = ∑ y : ZMod p, y ^ 2 :=
      Equiv.sum_comp (Equiv.inv (ZMod p)) (fun y => y ^ 2)
    rw [h1]
    exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2 (by rw [ZMod.card]; omega)
  have hbij : ∑ i ∈ range p, (((i : ℕ) : ZMod p)⁻¹) ^ 2 = ∑ y : ZMod p, (y⁻¹) ^ 2 := by
    refine Finset.sum_nbij' (fun i => ((i : ℕ) : ZMod p)) (fun y => y.val) ?_ ?_ ?_ ?_ ?_
    · intro i _; exact mem_univ _
    · intro y _; exact mem_range.mpr (ZMod.val_lt y)
    · intro i hi; exact ZMod.val_natCast_of_lt (mem_range.mp hi)
    · intro y _; exact ZMod.natCast_zmod_val y
    · intro i _; rfl
  have hr : range p = range (p - 1 + 1) := by
    congr 1
    omega
  have hsplit : ∑ i ∈ range p, (((i : ℕ) : ZMod p)⁻¹) ^ 2 =
      ∑ k ∈ range (p - 1), (((k + 1 : ℕ) : ZMod p)⁻¹) ^ 2 + (((0 : ℕ) : ZMod p)⁻¹) ^ 2 := by
    rw [hr, Finset.sum_range_succ']
  have h0 : (((0 : ℕ) : ZMod p)⁻¹) ^ 2 = 0 := by simp
  rw [hbij, hall, h0, add_zero] at hsplit
  exact hsplit.symm

/-- L6 -/
private lemma Psq_mul_Hq {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ZMod (p ^ 3)) ^ 2 * Hq (xi p) (p - 1) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  apply cast_zero_imp hp
  unfold Hq
  rw [map_sum]
  refine Eq.trans ?_ (sum_inv_sq_zmod hp h5)
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  rw [map_pow]
  congr 1
  have hm := congrArg (ZMod.castHom (dvd_pow_self p (by norm_num : (3 : ℕ) ≠ 0)) (ZMod p))
    (unit_mul_inv hp (k := k) (by omega))
  rw [map_mul, map_one, map_natCast] at hm
  exact eq_inv_of_mul_eq_one_right hm

/-! ## The theorem -/

private lemma main_thm (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ((p : ℤ) ^ 3) ∣ (a (2 * p - 1) - 1) := by
  have hp2 : 2 < p := by omega
  have h3 := P_cube p
  have hn2 : (2 * p - 1) / 2 = p - 1 := by omega
  obtain ⟨j, hj⟩ : ∃ j, p - 1 = 2 * j := by
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega)
    exact ⟨m, by omega⟩
  have hS : ∑ k ∈ range (p - 1), (-1 : ZMod (p ^ 3)) ^ (k + 1) *
      (Gs (p : ZMod (p ^ 3)) (xi p) k * (1 - (p : ZMod (p ^ 3)) * xi p k)) ^ (2 * p - 1) = 0 := by
    have h6 := Psq_mul_Hq hp h5
    have h7 := P_mul_Hs hp hp2 h6
    have h8 := Psq_mul_Qs hp hp2
    rw [hj] at h6 h7 h8 ⊢
    rw [signed_sum hp hp2 (p : ZMod (p ^ 3)) rfl h3 (xi p) j]
    linear_combination
      (1 + (p : ZMod (p ^ 3)) * Hs (xi p) (2 * j) - 2 * (p : ZMod (p ^ 3))) * h7 + h6 - h8
  have hterm : ∀ k ∈ range (p - 1),
      ((((2 * p - 1).choose (k + 1) : ℕ) : ZMod (p ^ 3)) -
          (((2 * p - 1).choose k : ℕ) : ZMod (p ^ 3))) ^ (2 * p - 1) =
        2 ^ (2 * p - 1) * ((-1) ^ (k + 1) *
          (Gs (p : ZMod (p ^ 3)) (xi p) k * (1 - (p : ZMod (p ^ 3)) * xi p k)) ^ (2 * p - 1)) := by
    intro k hk
    rw [mem_range] at hk
    rw [choose_eq hp (k + 1) (by omega), choose_eq hp k (by omega), Gs_succ]
    have hsgn : ((-1 : ZMod (p ^ 3)) ^ (k + 1)) ^ (2 * p - 1) = (-1) ^ (k + 1) := by
      rw [pow_right_comm, Odd.neg_one_pow ⟨p - 1, by omega⟩]
    have hfac : (-1 : ZMod (p ^ 3)) ^ (k + 1) *
          (Gs (p : ZMod (p ^ 3)) (xi p) k * (1 - 2 * (p : ZMod (p ^ 3)) * xi p k)) -
        (-1) ^ k * Gs (p : ZMod (p ^ 3)) (xi p) k =
        2 * ((-1) ^ (k + 1) *
          (Gs (p : ZMod (p ^ 3)) (xi p) k * (1 - (p : ZMod (p ^ 3)) * xi p k))) := by
      ring
    rw [hfac, mul_pow, mul_pow, hsgn]
  have hcast : ((a (2 * p - 1) - 1 : ℤ) : ZMod (p ^ 3)) = 0 := by
    have hsum : ((a (2 * p - 1) - 1 : ℤ) : ZMod (p ^ 3)) =
        ∑ k ∈ range (p - 1),
          ((((2 * p - 1).choose (k + 1) : ℕ) : ZMod (p ^ 3)) -
            (((2 * p - 1).choose k : ℕ) : ZMod (p ^ 3))) ^ (2 * p - 1) := by
      rw [a_eq, hn2]
      push_cast
      ring
    rw [hsum, sum_congr rfl hterm, ← mul_sum, hS, mul_zero]
  have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  exact_mod_cast hdvd

end A357825

theorem OMA.solution : type_of% @OMA.S_oeis_a357825.main := by
  intro p hp h5
  exact A357825.main_thm p hp h5
