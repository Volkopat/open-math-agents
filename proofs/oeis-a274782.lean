import OMAStatements.S_oeis_a274782
import Mathlib

/-!
Proof of Peter Bala's supercongruence for A274782:
`a(n p^r) ≡ a(n p^(r-1)) (mod p^(2r))` for primes `p ≥ 5`.

Outline.
1. `ident`: `2 a(n) = ∑_{a,b,c} F(n;a,b,c) E(b-c)` with
   `F(n;a,b,c) = C(n,k)^2 C(n-k,a) C(k,b) C(k,c)`, `k = a+b+c`, and `E` of period 6
   (`E(d) = ζ^d + ζ^(-d)` for a primitive sixth root of unity `ζ`). It comes from the
   Legendre identity `∑ C(n,j) C(n+j,j) y^j = ∑ C(n,k)^2 y^(n-k) (1+y)^k`, the
   substitution `y = x + x^2`, and `1 + x + x^2 = (1 + ζ x)(1 + ζ' x)`.
2. `JW`: with `f(m) = (pm)!/(p^m m!)`, `f(B+C) ≡ f(B) f(C) (mod p^(2m+2))` when `p^m`
   divides `B` and `C`; so `C(pA,pB)` and `C(A,B)` agree up to a unit `≡ 1 (mod p^(2m+2))`.
3. `key`: valuation bound for `F` on triples whose common `p`-power is exactly `p^t`.
4. `claimB` and the main theorem: triples not all divisible by `p` contribute `0`, the
   others reduce to the sum for `n p^(r-1)`, and `E(p d) = E(d)`; divide by 2.
-/

open Finset Polynomial

namespace A274782

lemma NI (n j : ℕ) : ∑ k ∈ range (n + 1), n.choose k ^ 2 *
    (if n - k ≤ j then k.choose (j - (n - k)) else 0) = n.choose j * (n + j).choose j := by
  rw [← Finset.sum_range_reflect]
  have h : ∀ i ∈ range (n + 1), n.choose (n + 1 - 1 - i) ^ 2 *
      (if n - (n + 1 - 1 - i) ≤ j then (n + 1 - 1 - i).choose (j - (n - (n + 1 - 1 - i))) else 0)
      = if i ≤ j then n.choose i ^ 2 * (n - i).choose (j - i) else 0 := by
    intro i hi
    rw [mem_range] at hi
    have e1 : n + 1 - 1 - i = n - i := by omega
    have e2 : n - (n - i) = i := by omega
    rw [e1, e2, Nat.choose_symm (by omega)]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h, ← Finset.sum_filter]
  have hsub : (range (n + 1)).filter (· ≤ j) ⊆ range (j + 1) := by
    intro i; simp only [mem_filter, mem_range]; omega
  rw [Finset.sum_subset hsub (by
    intro i hi hni
    simp only [mem_filter, mem_range, not_and] at hi hni
    rw [Nat.choose_eq_zero_of_lt (by omega : n < i)]; simp)]
  have h2 : ∀ i ∈ range (j + 1), n.choose i ^ 2 * (n - i).choose (j - i)
      = n.choose j * (n.choose i * j.choose i) := by
    intro i hi
    rw [mem_range] at hi
    have := Nat.choose_mul (n := n) (k := j) (s := i) (by omega)
    rw [sq, mul_assoc, ← this]; ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
  congr 1
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [mem_range] at hi
  rw [Nat.choose_symm (by omega)]

lemma P1 (R : Type*) [CommRing R] (n : ℕ) :
    ∑ j ∈ range (n + 1), C ((n.choose j * (n + j).choose j : ℕ) : R) * X ^ j =
      ∑ k ∈ range (n + 1), C ((n.choose k ^ 2 : ℕ) : R) * (X ^ (n - k) * (1 + X) ^ k) := by
  ext j
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow_mul', coeff_one_add_X_pow, coeff_X_pow,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
  have := NI n j
  have h : ∑ k ∈ range (n + 1),
      (if n - k ≤ j then ((n.choose k ^ 2 : ℕ) : R) * ((k.choose (j - (n - k)) : ℕ) : R) else 0)
      = ((n.choose j * (n + j).choose j : ℕ) : R) := by
    rw [← this]; push_cast; refine Finset.sum_congr rfl (fun k _ => ?_); split_ifs <;> simp
  rw [h]
  split_ifs with hj
  · rfl
  · simp only [mem_range, not_lt] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega : n < j)]; simp


def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k * (n + k).choose k * k.choose (n - k)

lemma P2 (R : Type*) [CommRing R] (n : ℕ) : ((a n : ℕ) : R) = ∑ k ∈ range (n + 1),
    ((n.choose k ^ 2 : ℕ) : R) * ((1 + X) ^ (n - k) * (1 + (X + X ^ 2)) ^ k : R[X]).coeff k := by
  have h := congrArg (aeval (X + X ^ 2 : R[X])) (P1 R n)
  simp only [map_sum, map_mul, map_pow, aeval_C, aeval_X, map_add, map_one,
    algebraMap_eq] at h
  have h2 := congrArg (coeff · n) h
  simp only [finsetSum_coeff, coeff_C_mul] at h2
  have hq : ∀ j, (X + X ^ 2 : R[X]) ^ j = X ^ j * (1 + X) ^ j := fun j => by
    rw [← mul_pow]; ring
  simp only [hq, mul_assoc, coeff_X_pow_mul', coeff_one_add_X_pow] at h2
  have hL : ∀ j ∈ range (n + 1), ((n.choose j * (n + j).choose j : ℕ) : R) *
      (if j ≤ n then ((j.choose (n - j) : ℕ) : R) else 0) =
      ((n.choose j * (n + j).choose j * j.choose (n - j) : ℕ) : R) := by
    intro j hj; rw [mem_range] at hj; rw [if_pos (by omega)]; push_cast; ring
  have hR : ∀ k ∈ range (n + 1), ((n.choose k ^ 2 : ℕ) : R) *
      (if n - k ≤ n then ((1 + X) ^ (n - k) * (1 + (X + X ^ 2)) ^ k : R[X]).coeff (n - (n - k))
        else 0) =
      ((n.choose k ^ 2 : ℕ) : R) * ((1 + X) ^ (n - k) * (1 + (X + X ^ 2)) ^ k : R[X]).coeff k := by
    intro k hk; rw [mem_range] at hk; rw [if_pos (by omega), show n - (n - k) = k by omega]
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR] at h2
  unfold a; rw [Nat.cast_sum]; exact h2


def F (X a b c : ℕ) : ℕ :=
  X.choose (a + b + c) ^ 2 * (X - (a + b + c)).choose a * (a + b + c).choose b *
    (a + b + c).choose c

lemma expand {R : Type*} [CommRing R] (z : R) (m L : ℕ) (h : m < L) :
    (1 + C z * X) ^ m = ∑ b ∈ range L, C ((m.choose b : R) * z ^ b) * X ^ b := by
  rw [add_comm, add_pow]
  have e : ∑ b ∈ range (m + 1), (C z * X) ^ b * 1 ^ (m - b) * (m.choose b : R[X]) =
      ∑ b ∈ range (m + 1), C ((m.choose b : R) * z ^ b) * X ^ b :=
    sum_congr rfl (fun b _ => by
      rw [mul_pow, one_pow, mul_one, ← C_eq_natCast, C_mul, C_pow]; ring)
  rw [e]
  apply Finset.sum_subset (range_subset_range.mpr (by omega))
  intro b hb hnb
  simp only [mem_range, not_lt] at hb hnb
  rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma coeff_triple {R : Type*} [CommRing R] (A B D : ℕ → R) (L k : ℕ) :
    ((∑ a ∈ range L, C (A a) * X ^ a) * ((∑ b ∈ range L, C (B b) * X ^ b) *
      (∑ c ∈ range L, C (D c) * X ^ c))).coeff k =
      ∑ a ∈ range L, ∑ b ∈ range L, ∑ c ∈ range L,
        if k = a + b + c then A a * B b * D c else 0 := by
  rw [Finset.sum_mul_sum, Finset.sum_mul, finsetSum_coeff]
  refine sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum, finsetSum_coeff]
  refine sum_congr rfl (fun b _ => ?_)
  rw [Finset.mul_sum, finsetSum_coeff]
  refine sum_congr rfl (fun c _ => ?_)
  rw [show C (A a) * X ^ a * (C (B b) * X ^ b * (C (D c) * X ^ c)) =
    C (A a * B b * D c) * X ^ (a + b + c) by simp only [C_mul, pow_add]; ring, coeff_C_mul_X_pow]

def T3 (m k a b c : ℕ) : ℕ := if k = a + b + c then m.choose a * k.choose b * k.choose c else 0

lemma T3_swap (m k a b c : ℕ) : T3 m k a c b = T3 m k a b c := by
  unfold T3; rw [show a + c + b = a + b + c by ring]; split_ifs <;> ring

lemma P3 {R : Type*} [CommRing R] (z w : R) (h1 : z + w = 1) (h2 : z * w = 1) (m k L : ℕ)
    (hm : m < L) (hk : k < L) :
    ((1 + X) ^ m * (1 + (X + X ^ 2)) ^ k : R[X]).coeff k =
      ∑ a ∈ range L, ∑ b ∈ range L, ∑ c ∈ range L, ((T3 m k a b c : ℕ) : R) * (z ^ b * w ^ c) := by
  have hf : (1 + (X + X ^ 2) : R[X]) = (1 + C z * X) * (1 + C w * X) := by
    have : (1 + C z * X) * (1 + C w * X) = 1 + C (z + w) * X + C (z * w) * X ^ 2 := by
      simp only [C_add, C_mul]; ring
    rw [this, h1, h2, C_1]; ring
  have e1 : (1 + X : R[X]) ^ m = ∑ a ∈ range L, C ((m.choose a : R) * 1 ^ a) * X ^ a := by
    rw [← expand 1 m L hm]; simp
  rw [hf, mul_pow, e1, expand z k L hk, expand w k L hk, coeff_triple]
  refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => sum_congr rfl (fun c _ => ?_)))
  unfold T3
  split_ifs <;> push_cast <;> ring

def E (d : ℤ) : ℤ :=
  if d % 6 = 0 then 2 else if d % 6 = 3 then -2 else if d % 6 = 1 ∨ d % 6 = 5 then 1 else -1

lemma E_rec (d : ℤ) : E (d + 2) = E (d + 1) - E d := by unfold E; split_ifs <;> omega

lemma E_neg (d : ℤ) : E (-d) = E d := by unfold E; split_ifs <;> omega

lemma E_mul (p d : ℤ) (hp : p % 6 = 1 ∨ p % 6 = 5) : E (p * d) = E d := by
  unfold E; rw [Int.mul_emod]; rcases hp with h | h <;> rw [h] <;> split_ifs <;> omega

lemma zw_pow {R : Type*} [CommRing R] (z w : R) (h1 : z + w = 1) (h2 : z * w = 1) (d : ℕ) :
    z ^ d + w ^ d = ((E d : ℤ) : R) := by
  have hz : z ^ 2 = z - 1 := by linear_combination z * h1 - h2
  have hw : w ^ 2 = w - 1 := by linear_combination w * h1 - h2
  have key : ∀ d : ℕ, z ^ d + w ^ d = ((E d : ℤ) : R) ∧
      z ^ (d + 1) + w ^ (d + 1) = ((E ((d + 1 : ℕ) : ℤ) : ℤ) : R) := by
    intro d
    induction d with
    | zero => constructor <;> norm_num [E, h1]
    | succ d ih =>
      refine ⟨ih.2, ?_⟩
      have e : z ^ (d + 2) + w ^ (d + 2) = (z ^ (d + 1) + w ^ (d + 1)) - (z ^ d + w ^ d) := by
        linear_combination z ^ d * hz + w ^ d * hw
      rw [show d + 1 + 1 = d + 2 by ring, e, ih.1, ih.2]
      have := E_rec (d : ℤ)
      push_cast
      rw [this]; push_cast; ring
  exact (key d).1

lemma swapE {R : Type*} [CommRing R] (z w : R) (h1 : z + w = 1) (h2 : z * w = 1) (b c : ℕ) :
    z ^ b * w ^ c + z ^ c * w ^ b = ((E ((b : ℤ) - c) : ℤ) : R) := by
  rcases le_total c b with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have : z ^ (c + d) * w ^ c + z ^ c * w ^ (c + d) = (z * w) ^ c * (z ^ d + w ^ d) := by ring
    rw [this, h2, one_pow, one_mul, zw_pow z w h1 h2]
    congr 2; push_cast; ring
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have : z ^ b * w ^ (b + d) + z ^ (b + d) * w ^ b = (z * w) ^ b * (z ^ d + w ^ d) := by ring
    rw [this, h2, one_pow, one_mul, zw_pow z w h1 h2,
      show ((b : ℕ) : ℤ) - ((b + d : ℕ) : ℤ) = -(d : ℤ) by push_cast; ring, E_neg]


lemma ident_R {R : Type*} [CommRing R] (z w : R) (h1 : z + w = 1) (h2 : z * w = 1) (n : ℕ) :
    2 * ((a n : ℕ) : R) = ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), ∑ c ∈ range (n + 1),
      ((F n a b c : ℕ) : R) * ((E ((b : ℤ) - c) : ℤ) : R) := by
  rw [P2 R n, Finset.mul_sum]
  have hk : ∀ k ∈ range (n + 1), 2 * (((n.choose k ^ 2 : ℕ) : R) *
      ((1 + X) ^ (n - k) * (1 + (X + X ^ 2)) ^ k : R[X]).coeff k) =
      ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), ∑ c ∈ range (n + 1),
        if k = a + b + c then ((F n a b c : ℕ) : R) * ((E ((b : ℤ) - c) : ℤ) : R) else 0 := by
    intro k hk
    rw [mem_range] at hk
    rw [P3 z w h1 h2 (n - k) k (n + 1) (by omega) hk]
    have hsym : ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), ∑ c ∈ range (n + 1),
        ((T3 (n - k) k a b c : ℕ) : R) * (z ^ b * w ^ c) =
        ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), ∑ c ∈ range (n + 1),
        ((T3 (n - k) k a b c : ℕ) : R) * (z ^ c * w ^ b) := by
      refine sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_comm]
      refine sum_congr rfl (fun b _ => sum_congr rfl (fun c _ => ?_))
      rw [T3_swap]
    have h2S : 2 * (∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), ∑ c ∈ range (n + 1),
        ((T3 (n - k) k a b c : ℕ) : R) * (z ^ b * w ^ c)) =
        ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), ∑ c ∈ range (n + 1),
        ((T3 (n - k) k a b c : ℕ) : R) * ((E ((b : ℤ) - c) : ℤ) : R) := by
      rw [two_mul]
      nth_rewrite 2 [hsym]
      rw [← sum_add_distrib]; refine sum_congr rfl (fun a _ => ?_)
      rw [← sum_add_distrib]; refine sum_congr rfl (fun b _ => ?_)
      rw [← sum_add_distrib]; refine sum_congr rfl (fun c _ => ?_)
      rw [← mul_add, swapE z w h1 h2]
    rw [mul_left_comm, h2S, mul_sum]
    refine sum_congr rfl (fun a _ => ?_)
    rw [mul_sum]; refine sum_congr rfl (fun b _ => ?_)
    rw [mul_sum]; refine sum_congr rfl (fun c _ => ?_)
    unfold T3
    split_ifs with hs
    · subst hs; unfold F; push_cast; ring
    · simp
  rw [Finset.sum_congr rfl hk, Finset.sum_comm]
  refine sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]; refine sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_comm]; refine sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_ite_eq']
  split_ifs with hs
  · rfl
  · simp only [mem_range, not_lt] at hs
    unfold F; rw [Nat.choose_eq_zero_of_lt (by omega : n < a + b + c)]; simp

lemma ident (n : ℕ) : 2 * (a n : ℤ) = ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1),
    ∑ c ∈ range (n + 1), (F n a b c : ℤ) * E ((b : ℤ) - c) := by
  have hz : (⟨1 / 2, Real.sqrt 3 / 2⟩ : ℂ) + ⟨1 / 2, -(Real.sqrt 3 / 2)⟩ = 1 := by
    apply Complex.ext <;> simp <;> norm_num
  have hzw : (⟨1 / 2, Real.sqrt 3 / 2⟩ : ℂ) * ⟨1 / 2, -(Real.sqrt 3 / 2)⟩ = 1 := by
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> nlinarith [h3]
  have := ident_R _ _ hz hzw n
  have h' : (((2 * (a n : ℤ) : ℤ)) : ℂ) = ((∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1),
      ∑ c ∈ range (n + 1), (F n a b c : ℤ) * E ((b : ℤ) - c) : ℤ) : ℂ) := by
    push_cast; exact this
  exact_mod_cast h'

lemma sq_dvd_eval_sub (G : ℤ[X]) (y z d : ℤ) (hz : z ≠ 0) (hG : G.eval z = G.eval 0)
    (hy : d ∣ y) (hzd : d ∣ z) : d ^ 2 ∣ G.eval y - G.eval 0 := by
  obtain ⟨Q, hQ⟩ : X ∣ G - C (G.eval 0) := by
    rw [X_dvd_iff]; simp [coeff_zero_eq_eval_zero]
  have hev : ∀ t, G.eval t - G.eval 0 = t * Q.eval t := by
    intro t; have := congrArg (eval t) hQ; simpa using this
  have hQz : Q.eval z = 0 := by
    have := hev z; rw [hG, sub_self] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hz
  have h1 : z ∣ Q.eval 0 := by
    have := sub_dvd_eval_sub 0 z Q
    rw [hQz, sub_zero, zero_sub, neg_dvd] at this; exact this
  have h2 : y ∣ Q.eval y - Q.eval 0 := by simpa using sub_dvd_eval_sub y 0 Q
  have h3 : d ∣ Q.eval y := by
    have := dvd_add (hy.trans h2) (hzd.trans h1); simpa using this
  rw [hev y, sq]; exact mul_dvd_mul hy h3

def g (p : ℕ) (x : ℤ) : ℤ := ∏ l ∈ range (p - 1), (x + ((l : ℤ) + 1))

def f (p m : ℕ) : ℤ := ∏ i ∈ range m, g p (p * i)

lemma g_symm (p : ℕ) (hp : Odd p) (x : ℤ) : g p (-p - x) = g p x := by
  unfold g
  rw [← Finset.prod_range_reflect]
  have h : ∀ j ∈ range (p - 1),
      (-(p:ℤ) - x + (((p - 1 - 1 - j : ℕ) : ℤ) + 1)) = -(x + ((j : ℤ) + 1)) := by
    intro j hj
    rw [mem_range] at hj
    have : ((p - 1 - 1 - j : ℕ) : ℤ) = (p : ℤ) - 2 - j := by omega
    rw [this]; ring
  rw [Finset.prod_congr rfl h, Finset.prod_neg, card_range]
  have he : Even (p - 1) := Nat.Odd.sub_odd hp odd_one
  rw [he.neg_one_pow, one_mul]

noncomputable def Gp (p C : ℕ) : ℤ[X] := ∏ i ∈ range C, ∏ l ∈ range (p - 1), (X + Polynomial.C ((p:ℤ) * i + l + 1))

lemma Gp_eval (p C : ℕ) (x : ℤ) : (Gp p C).eval x = ∏ i ∈ range C, g p (x + p * i) := by
  unfold Gp g
  rw [eval_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [eval_prod]
  refine Finset.prod_congr rfl (fun l _ => ?_)
  simp only [eval_add, eval_X, eval_C]; ring

lemma Gp_symm (p C : ℕ) (hp : Odd p) : (Gp p C).eval (-((p:ℤ) * C)) = (Gp p C).eval 0 := by
  rw [Gp_eval, Gp_eval, ← Finset.prod_range_reflect]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  rw [mem_range] at hi
  have : ((C - 1 - i : ℕ) : ℤ) = (C : ℤ) - 1 - i := by omega
  rw [this, show (-((p:ℤ) * C) + p * ((C:ℤ) - 1 - i)) = -(p:ℤ) - (p:ℤ) * i by ring, g_symm p hp,
    zero_add]

lemma f_add (p B C : ℕ) : f p (B + C) = f p B * (Gp p C).eval ((p : ℤ) * B) := by
  unfold f
  rw [prod_range_add, Gp_eval]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  congr 1; push_cast; ring

lemma f_zero (p : ℕ) : f p 0 = 1 := by simp [f]

lemma f_eval0 (p C : ℕ) : (Gp p C).eval 0 = f p C := by
  rw [Gp_eval]; unfold f; simp

lemma JW (p : ℕ) (hp : Odd p) (m B C : ℕ) (hB : p ^ m ∣ B) (hC : p ^ m ∣ C) :
    (p : ℤ) ^ (2 * m + 2) ∣ f p (B + C) - f p B * f p C := by
  rcases Nat.eq_zero_or_pos C with rfl | hC0
  · simp [f_zero]
  rw [f_add, ← f_eval0 p C, ← mul_sub]
  apply Dvd.dvd.mul_left
  have hp0 : (p : ℤ) ≠ 0 := by
    have : p ≠ 0 := by rintro rfl; simp at hp
    exact_mod_cast this
  have key := sq_dvd_eval_sub (Gp p C) (p * B) (-(p * C)) ((p : ℤ) ^ (m + 1))
    (by have : (C : ℤ) ≠ 0 := by exact_mod_cast hC0.ne'
        exact neg_ne_zero.mpr (mul_ne_zero hp0 this))
    (Gp_symm p C hp)
    (by rw [pow_succ', ]; exact mul_dvd_mul_left _ (by exact_mod_cast hB))
    (by rw [pow_succ', dvd_neg]; exact mul_dvd_mul_left _ (by exact_mod_cast hC))
  rw [← pow_mul, show (m + 1) * 2 = 2 * m + 2 by ring] at key
  exact key

lemma fact_add (n j : ℕ) :
    (((n + j).factorial : ℕ) : ℤ) = (n.factorial : ℤ) * ∏ l ∈ range j, ((n : ℤ) + l + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← add_assoc, Nat.factorial_succ, prod_range_succ]
    push_cast
    rw [ih]; ring

lemma fact_mul (p : ℕ) (hp : 0 < p) (m : ℕ) :
    (((p * m).factorial : ℕ) : ℤ) = (p : ℤ) ^ m * (m.factorial : ℤ) * f p m := by
  induction m with
  | zero => simp [f_zero]
  | succ m ih =>
    rw [show p * (m + 1) = p * m + p by ring, fact_add, ih]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [prod_range_succ]
    unfold f
    rw [prod_range_succ, Nat.factorial_succ]
    unfold g
    simp only [Nat.add_sub_cancel]
    push_cast
    have : ∏ x ∈ range q, (((q:ℤ) + 1) * m + x + 1) = ∏ l ∈ range q, (((q:ℤ) + 1) * m + (l + 1)) :=
      Finset.prod_congr rfl (fun _ _ => by ring)
    rw [this]; ring

lemma choose_rel (p : ℕ) (hp : 0 < p) (A B : ℕ) (hBA : B ≤ A) :
    ((p * A).choose (p * B) : ℤ) * (f p B * f p (A - B)) = (A.choose B : ℤ) * f p A := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.mul_le_mul_left p hBA)
  have h2 := Nat.choose_mul_factorial_mul_factorial hBA
  rw [← Nat.mul_sub] at h1
  have h1' : (((p * A).choose (p * B) * (p * B).factorial * (p * (A - B)).factorial : ℕ) : ℤ)
      = (((p * A).factorial : ℕ) : ℤ) := by rw [h1]
  have h2' : ((A.choose B * B.factorial * (A - B).factorial : ℕ) : ℤ) = ((A.factorial : ℕ) : ℤ) := by
    rw [h2]
  push_cast at h1' h2'
  rw [fact_mul p hp, fact_mul p hp, fact_mul p hp] at h1'
  rw [← h2'] at h1'
  have hne : (p : ℤ) ^ A * ((B.factorial : ℤ) * ((A - B).factorial : ℤ)) ≠ 0 := by
    have : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
    have h3 : (B.factorial : ℤ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos B).ne'
    have h4 : ((A - B).factorial : ℤ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    exact mul_ne_zero (pow_ne_zero _ this) (mul_ne_zero h3 h4)
  apply mul_right_cancel₀ hne
  have hpow : (p : ℤ) ^ A = (p : ℤ) ^ B * (p : ℤ) ^ (A - B) := by
    rw [← pow_add, Nat.add_sub_cancel' hBA]
  rw [hpow] at h1' ⊢; linear_combination h1'

lemma f_coprime (p : ℕ) (hp : p.Prime) (m : ℕ) : IsCoprime (p : ℤ) (f p m) := by
  unfold f g
  apply IsCoprime.prod_right
  intro i _
  apply IsCoprime.prod_right
  intro l hl
  rw [mem_range] at hl
  have h : IsCoprime (p : ℤ) ((l : ℤ) + 1) := by
    have : Nat.Coprime p (l + 1) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    have := Nat.isCoprime_iff_coprime.mpr this
    exact_mod_cast this
  have := h.add_mul_left_right (i : ℤ)
  rw [show (p : ℤ) * i + ((l : ℤ) + 1) = (l : ℤ) + 1 + p * i by ring]; exact this

/-- `Rel q X Y`: `X * U = Y * V` with `U` a `p`-unit and `U ≡ V [q]`. -/
def Rel (p q X Y : ℤ) : Prop := ∃ U V : ℤ, IsCoprime p U ∧ q ∣ V - U ∧ X * U = Y * V

lemma Rel.mul {p q X Y X' Y' : ℤ} (h : Rel p q X Y) (h' : Rel p q X' Y') :
    Rel p q (X * X') (Y * Y') := by
  obtain ⟨U, V, hU, hq, e⟩ := h
  obtain ⟨U', V', hU', hq', e'⟩ := h'
  refine ⟨U * U', V * V', hU.mul_right hU', ?_, ?_⟩
  · have : V * V' - U * U' = V * (V' - U') + U' * (V - U) := by ring
    rw [this]; exact dvd_add (hq'.mul_left _) (hq.mul_left _)
  · linear_combination (X' * U') * e + (Y * V) * e'

lemma Rel.choose (p : ℕ) (hp : p.Prime) (hodd : Odd p) (m A B : ℕ) (hA : p ^ m ∣ A)
    (hB : p ^ m ∣ B) :
    Rel p ((p : ℤ) ^ (2 * m + 2)) ((p * A).choose (p * B)) (A.choose B) := by
  by_cases hBA : B ≤ A
  · refine ⟨f p B * f p (A - B), f p A, (f_coprime p hp B).mul_right (f_coprime p hp _), ?_,
      choose_rel p hp.pos A B hBA⟩
    have := JW p hodd m B (A - B) hB (Nat.dvd_sub hA hB)
    rwa [Nat.add_sub_cancel' hBA] at this
  · push Not at hBA
    refine ⟨1, 1, isCoprime_one_right, by simp, ?_⟩
    rw [Nat.choose_eq_zero_of_lt hBA, Nat.choose_eq_zero_of_lt
      (Nat.mul_lt_mul_of_pos_left hBA hp.pos)]

lemma Rel.final {p X Y : ℤ} {s e : ℕ} (h : Rel p (p ^ e) X Y) (hY : p ^ s ∣ Y) :
    p ^ (s + e) ∣ X - Y := by
  obtain ⟨U, V, hU, hq, eq⟩ := h
  have h1 : (X - Y) * U = Y * (V - U) := by linear_combination eq
  have h2 : p ^ (s + e) ∣ (X - Y) * U := by rw [h1, pow_add]; exact mul_dvd_mul hY hq
  exact (hU.pow_left).dvd_of_dvd_mul_right h2



lemma V {p : ℕ} (hp : p.Prime) {m k α β k'' : ℕ} (hm : p ^ α ∣ m) (hk : k = p ^ β * k'')
    (hk'' : ¬ p ∣ k'') : p ^ (α - β) ∣ m.choose k := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    rcases mul_eq_zero.mp hk.symm with h | h
    · exact (pow_ne_zero _ hp.ne_zero) h
    · exact hk'' (h ▸ dvd_zero p)
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rcases m with _ | m'
  · simp
  have e := Nat.add_one_mul_choose_eq m' k'
  by_cases hαβ : β ≤ α
  · have h1 : p ^ α ∣ (m' + 1).choose (k' + 1) * (k' + 1) := e ▸ dvd_mul_of_dvd_left hm _
    generalize (m' + 1).choose (k' + 1) = Cm at h1 ⊢
    rw [hk] at h1
    have : p ^ (α - β) * p ^ β = p ^ α := by rw [← pow_add, Nat.sub_add_cancel hαβ]
    rw [← this, mul_comm (p ^ β) k'', ← mul_assoc] at h1
    have h2 := Nat.dvd_of_mul_dvd_mul_right (pow_pos hp.pos _) h1
    exact (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hk'')).dvd_of_dvd_mul_right h2
  · rw [Nat.sub_eq_zero_of_le (by omega)]; simp

lemma two_of_three {q a b c : ℕ} (h : q ∣ a + b + c) (hn : ¬ (q ∣ a ∧ q ∣ b ∧ q ∣ c)) :
    (¬ q ∣ a ∧ ¬ q ∣ b) ∨ (¬ q ∣ a ∧ ¬ q ∣ c) ∨ (¬ q ∣ b ∧ ¬ q ∣ c) := by
  have i1 : q ∣ a → q ∣ b → q ∣ c := fun ha hb => (Nat.dvd_add_right (dvd_add ha hb)).mp h
  have i2 : q ∣ a → q ∣ c → q ∣ b := fun ha hc => by
    have : q ∣ (a + c) + b := by rwa [show a + c + b = a + b + c by ring]
    exact (Nat.dvd_add_right (dvd_add ha hc)).mp this
  have i3 : q ∣ b → q ∣ c → q ∣ a := fun hb hc => by
    have : q ∣ (b + c) + a := by rwa [show b + c + a = a + b + c by ring]
    exact (Nat.dvd_add_right (dvd_add hb hc)).mp this
  tauto

lemma key {p : ℕ} (hp : p.Prime) {L t X a b c : ℕ} (hX : p ^ L ∣ X) (ha : p ^ t ∣ a)
    (hb : p ^ t ∣ b) (hc : p ^ t ∣ c)
    (hn : ¬ (p ^ (t + 1) ∣ a ∧ p ^ (t + 1) ∣ b ∧ p ^ (t + 1) ∣ c)) (htL : t ≤ L) :
    p ^ (2 * (L - t)) ∣ F X a b c := by
  unfold F
  set K := a + b + c with hKdef
  by_cases hKX : X < K
  · rw [Nat.choose_eq_zero_of_lt hKX]; simp
  push Not at hKX
  have hK0 : K ≠ 0 := by
    intro h0
    have : a = 0 ∧ b = 0 ∧ c = 0 := by omega
    obtain ⟨rfl, rfl, rfl⟩ := this
    exact hn ⟨dvd_zero _, dvd_zero _, dvd_zero _⟩
  obtain ⟨β, K'', hK'', hKe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hK0 p hp.ne_one
  have htK : p ^ t ∣ K := dvd_add (dvd_add ha hb) hc
  have htβ : t ≤ β := by
    by_contra hlt
    push Not at hlt
    have : p ^ (β + 1) ∣ p ^ β * K'' := hKe ▸ (pow_dvd_pow p hlt).trans htK
    rw [pow_succ] at this
    exact hK'' (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) this)
  have h1 : p ^ (L - β) ∣ X.choose K := V hp hX hKe hK''
  by_cases hβ : β = t
  · subst hβ
    have : p ^ (2 * (L - β)) ∣ X.choose K ^ 2 := by
      rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd h1 2
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right this _) _) _
  by_cases hLt : L = t
  · subst hLt; simp
  set κ := min β L with hκdef
  have hκ1 : t + 1 ≤ κ := by omega
  have hκX : p ^ κ ∣ X := (pow_dvd_pow p (min_le_right _ _)).trans hX
  have hκK : p ^ κ ∣ K := by
    rw [hKe]; exact Dvd.dvd.mul_right (pow_dvd_pow p (min_le_left _ _)) _
  have hκXK : p ^ κ ∣ X - K := Nat.dvd_sub hκX hκK
  have hLβ : L - β = L - κ := by omega
  rw [hLβ] at h1
  have hsq : p ^ (2 * (L - κ)) ∣ X.choose K ^ 2 := by
    rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd h1 2
  have h3 : p ^ (t + 1) ∣ K := (pow_dvd_pow p hκ1).trans hκK
  have hV : ∀ x Y, p ^ t ∣ x → ¬ p ^ (t + 1) ∣ x → p ^ κ ∣ Y → p ^ (κ - t) ∣ Y.choose x := by
    intro x Y hx hx' hY
    obtain ⟨x'', rfl⟩ := hx
    refine V hp hY rfl ?_
    intro hd; apply hx'; rw [pow_succ]; exact mul_dvd_mul_left _ hd
  have hexp : 2 * (L - t) = 2 * (L - κ) + (κ - t) + (κ - t) := by omega
  rw [hexp, pow_add, pow_add]
  rcases two_of_three h3 hn with ⟨ha', hb'⟩ | ⟨ha', hc'⟩ | ⟨hb', hc'⟩
  · have := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hsq (hV a _ ha ha' hκXK)) (hV b _ hb hb' hκK))
      (one_dvd (K.choose c))
    simpa using this
  · have := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hsq (hV a _ ha ha' hκXK)) (one_dvd (K.choose b)))
      (hV c _ hc hc' hκK)
    simpa using this
  · have := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hsq (one_dvd ((X - K).choose a)))
      (hV b _ hb hb' hκK)) (hV c _ hc hc' hκK)
    simpa using this

lemma dich (p a b c : ℕ) : ∀ L, (p ^ L ∣ a ∧ p ^ L ∣ b ∧ p ^ L ∣ c) ∨
    ∃ t < L, (p ^ t ∣ a ∧ p ^ t ∣ b ∧ p ^ t ∣ c) ∧
      ¬ (p ^ (t + 1) ∣ a ∧ p ^ (t + 1) ∣ b ∧ p ^ (t + 1) ∣ c) := by
  intro L
  induction L with
  | zero => left; simp
  | succ L ih =>
    rcases ih with h | ⟨t, ht, h1, h2⟩
    · by_cases h' : p ^ (L + 1) ∣ a ∧ p ^ (L + 1) ∣ b ∧ p ^ (L + 1) ∣ c
      · left; exact h'
      · right; exact ⟨L, by omega, h, h'⟩
    · right; exact ⟨t, by omega, h1, h2⟩

lemma claimB {p : ℕ} (hp : p.Prime) (hodd : Odd p) {r M : ℕ} (hr : 0 < r)
    (hM : p ^ (r - 1) ∣ M) (a b c : ℕ) :
    (p : ℤ) ^ (2 * r) ∣ (F (p * M) (p * a) (p * b) (p * c) : ℤ) - (F M a b c : ℤ) := by
  have hrel : ∀ m, m ≤ r - 1 → p ^ m ∣ a → p ^ m ∣ b → p ^ m ∣ c →
      Rel p ((p : ℤ) ^ (2 * m + 2)) (F (p * M) (p * a) (p * b) (p * c)) (F M a b c) := by
    intro m hm ha hb hc
    have hMm : p ^ m ∣ M := (pow_dvd_pow p hm).trans hM
    have hK : p ^ m ∣ a + b + c := dvd_add (dvd_add ha hb) hc
    have hMK : p ^ m ∣ M - (a + b + c) := Nat.dvd_sub hMm hK
    have e1 : p * a + p * b + p * c = p * (a + b + c) := by ring
    have e2 : p * M - p * (a + b + c) = p * (M - (a + b + c)) := (Nat.mul_sub _ _ _).symm
    unfold F
    rw [e1, e2]
    push_cast
    have r1 := Rel.choose p hp hodd m M _ hMm hK
    rw [sq, sq]
    exact (((r1.mul r1).mul (Rel.choose p hp hodd m _ _ hMK ha)).mul
      (Rel.choose p hp hodd m _ _ hK hb)).mul (Rel.choose p hp hodd m _ _ hK hc)
  rcases dich p a b c (r - 1) with ⟨ha, hb, hc⟩ | ⟨t, ht, ⟨ha, hb, hc⟩, hn⟩
  · have := Rel.final (s := 0) (hrel (r - 1) le_rfl ha hb hc) (by simp)
    rwa [show 0 + (2 * (r - 1) + 2) = 2 * r by omega] at this
  · have hk := key hp hM ha hb hc hn ht.le
    have hk' : (p : ℤ) ^ (2 * (r - 1 - t)) ∣ (F M a b c : ℤ) := by exact_mod_cast hk
    have := Rel.final (hrel t ht.le ha hb hc) hk'
    rwa [show 2 * (r - 1 - t) + (2 * t + 2) = 2 * r by omega] at this


lemma nest (L : ℕ) (g : ℕ → ℕ → ℕ → ℤ) :
    ∑ a ∈ range L, ∑ b ∈ range L, ∑ c ∈ range L, g a b c =
      ∑ x ∈ range L ×ˢ (range L ×ˢ range L), g x.1 x.2.1 x.2.2 := by
  rw [Finset.sum_product]; refine sum_congr rfl (fun a _ => ?_); rw [Finset.sum_product]

lemma filter_eq (p M : ℕ) (hp : 0 < p) :
    (range (p * M + 1) ×ˢ (range (p * M + 1) ×ˢ range (p * M + 1))).filter
      (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2) =
    (range (M + 1) ×ˢ (range (M + 1) ×ˢ range (M + 1))).image
      (fun x => (p * x.1, p * x.2.1, p * x.2.2)) := by
  have h1 : ∀ y, p * y < p * M + 1 ↔ y < M + 1 := by
    intro y; constructor
    · intro h; by_contra h'; push Not at h'; nlinarith
    · intro h; nlinarith
  ext ⟨a, b, c⟩
  simp only [mem_filter, mem_product, mem_range, mem_image, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨⟨ha, hb, hc⟩, ⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩
    exact ⟨a', b', c', ⟨(h1 a').mp ha, (h1 b').mp hb, (h1 c').mp hc⟩, rfl, rfl, rfl⟩
  · rintro ⟨a', b', c', ⟨ha, hb, hc⟩, rfl, rfl, rfl⟩
    exact ⟨⟨(h1 a').mpr ha, (h1 b').mpr hb, (h1 c').mpr hc⟩, dvd_mul_right _ _,
      dvd_mul_right _ _, dvd_mul_right _ _⟩

theorem mainThm : ∀ n r p : ℕ, 0 < n → 0 < r → p.Prime → 5 ≤ p →
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (2 * r)] := by
  intro n r p hn hr hp hp5
  have hN : n * p ^ r = p * (n * p ^ (r - 1)) := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]; ring
  generalize hMdef : n * p ^ (r - 1) = M at hN ⊢
  have hMv : p ^ (r - 1) ∣ M := by rw [← hMdef]; exact dvd_mul_left _ _
  have hNv : p ^ r ∣ p * M := hN ▸ dvd_mul_left _ _
  rw [hN]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hp6 : (p : ℤ) % 6 = 1 ∨ (p : ℤ) % 6 = 5 := by
    have h2 : ¬ 2 ∣ p := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h; omega
    have h3 : ¬ 3 ∣ p := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h; omega
    omega
  rw [Nat.modEq_iff_dvd]
  have hc : IsCoprime ((p : ℤ) ^ (2 * r)) 2 := by
    apply IsCoprime.pow_left
    have : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
    exact_mod_cast Nat.isCoprime_iff_coprime.mpr this
  suffices h : (p : ℤ) ^ (2 * r) ∣ 2 * (a (p * M) : ℤ) - 2 * (a M : ℤ) by
    rw [← mul_sub] at h
    have := hc.dvd_of_dvd_mul_left h
    push_cast
    rw [← neg_sub]; exact this.neg_right
  rw [ident, ident, nest, nest]
  rw [← Finset.sum_filter_add_sum_filter_not _
    (fun x : ℕ × ℕ × ℕ => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2)]
  rw [filter_eq p M hp.pos, Finset.sum_image (by
    intro x _ y _ hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2, h3⟩ := hxy
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left hp.pos h1)
      (Prod.ext (Nat.eq_of_mul_eq_mul_left hp.pos h2) (Nat.eq_of_mul_eq_mul_left hp.pos h3)))]
  rw [show ∀ A B C : ℤ, A + B - C = (A - C) + B from fun A B C => by ring,
    ← Finset.sum_sub_distrib]
  apply dvd_add
  · apply Finset.dvd_sum
    intro x _
    rw [show ((p * x.2.1 : ℕ) : ℤ) - ((p * x.2.2 : ℕ) : ℤ) = (p : ℤ) * ((x.2.1 : ℤ) - x.2.2) by
      push_cast; ring, E_mul _ _ hp6, ← sub_mul]
    exact Dvd.dvd.mul_right (claimB hp hodd hr hMv _ _ _) _
  · apply Finset.dvd_sum
    intro x hx
    rw [mem_filter] at hx
    have hk := key (L := r) (t := 0) (X := p * M) hp hNv (by simp) (by simp) (by simp)
      (by simpa using hx.2) (Nat.zero_le _)
    have hk' : (p : ℤ) ^ (2 * r) ∣ (F (p * M) x.1 x.2.1 x.2.2 : ℤ) := by
      rw [Nat.sub_zero] at hk; exact_mod_cast hk
    exact Dvd.dvd.mul_right hk' _

end A274782

theorem OMA.solution : type_of% @OMA.S_oeis_a274782.main := by
  exact A274782.mainThm
