import OMAReductions.R_Erdos338_erdos_338_variants_squares_R1_H2_R1

/-!
# Proof of `Erdos338.erdos_338.variants.squares.R1.H2.R1.H1`

We prove that for every odd natural number `m ≥ 1`,
  `m ≤ 2 * #{v : Fin 4 → Fin (m + 1) | ∑ i, (v i : ℕ)^2 = m}`.

Proof via the Hurwitz quaternion ring `H` in the integral basis `(1, i, j, ω)` where
`ω = (1 + i + j + k) / 2`, so `(x, y, z, w) ∈ ℤ⁴` represents `x + y i + z j + w ω`,
whose doubled `(1, i, j, k)` coordinates are `(2x + w, 2y + w, 2z + w, w)`:
1. For every odd `m ≥ 1`, there exist `u, v : ZMod m` with `u^2 + v^2 + 1 = 0`.
2. This yields a surjective ring homomorphism `φ : H → Matrix (Fin 2) (Fin 2) (ZMod m)` with
   `det (φ α) = (N α : ZMod m)`.
3. Since `H` is left-Euclidean, for each `t : ZMod m` the left ideal `J_t = {α ∈ H | φ α *ᵥ ![1, t] = 0}`
   is principal `H · α_t`. From `m ∈ J_t` (`m = γ * α_t`) and `β_t ∈ J_t` (`φ β_t = ![![-t, 1], ![0, 0]]`),
   both `N α_t` and `N γ` are divisible by `m` and satisfy `N γ * N α_t = m^2`, forcing `N α_t = m`.
4. The `m` ideals `J_t` are pairwise distinct, and each `α_t` has 8 distinct Lipschitz left-associates
   in `J_t`, yielding at least `8 * m` signed representations `(x₀, x₁, x₂, x₃) ∈ ℤ⁴` of `m` as a sum
   of four squares.
5. Taking absolute values maps at most `2^4 = 16` signed tuples to each unsigned tuple in
   `Fin 4 → Fin (m + 1)`, giving `8 * m ≤ 16 * card`, i.e., `m ≤ 2 * card`.
-/

namespace Erdos338H1Proof

open Finset Filter Matrix

/- ## Step 1: `u^2 + v^2 + 1 = 0` in `ZMod m` for all odd `m` -/

private lemma exists_sq_add_sq_add_one_prime_pow (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ k : ℕ, 1 ≤ k → ∃ u v : ℤ, (p ^ k : ℤ) ∣ (u ^ 2 + v ^ 2 + 1) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1 : ZMod p)
      refine ⟨a.val, b.val, ?_⟩
      rw [pow_one]
      have h0 : ((a.val ^ 2 + b.val ^ 2 + 1 : ℤ) : ZMod p) = 0 := by
        push_cast
        simp only [ZMod.natCast_zmod_val]
        linear_combination hab
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0
    · obtain ⟨u, v, huv⟩ := ih (by omega)
      obtain ⟨t, ht⟩ := huv
      have hnotboth : ¬ ((p : ℤ) ∣ u ∧ (p : ℤ) ∣ v) := by
        rintro ⟨hu, hv⟩
        have h1 : (p : ℤ) ∣ (u ^ 2 + v ^ 2 + 1) :=
          (dvd_pow_self (p : ℤ) (by omega : k ≠ 0)).trans ⟨t, ht⟩
        have h2 : (p : ℤ) ∣ (u ^ 2 + v ^ 2) := dvd_add (dvd_pow hu (by decide)) (dvd_pow hv (by decide))
        have h3 : (p : ℤ) ∣ 1 := by
          have : (1 : ℤ) = (u ^ 2 + v ^ 2 + 1) - (u ^ 2 + v ^ 2) := by ring
          rw [this]; exact dvd_sub h1 h2
        have h4 : p ∣ 1 := Int.ofNat_dvd.mp h3
        exact hp.ne_one (Nat.dvd_one.mp h4)
      have lift : ∀ a b : ℤ, a ^ 2 + b ^ 2 + 1 = (p : ℤ) ^ k * t → ¬ (p : ℤ) ∣ a →
          ∃ a' : ℤ, (p : ℤ) ^ (k + 1) ∣ (a' ^ 2 + b ^ 2 + 1) := by
        intro a b hab hpa
        have : Fact p.Prime := ⟨hp⟩
        have h2a : (2 * (a : ZMod p)) ≠ 0 := by
          intro h0
          have h0' : ((2 * a : ℤ) : ZMod p) = 0 := by push_cast; exact h0
          have hdvd : (p : ℤ) ∣ 2 * a := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0'
          have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
          rcases hp_int.dvd_or_dvd hdvd with h2 | ha
          · have : p ∣ 2 := Int.ofNat_dvd.mp h2
            rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h2'
            · exact hp.ne_one h1
            · exact hp2 h2'
          · exact hpa ha
        let c : ℤ := ((-(t : ZMod p) * (2 * (a : ZMod p))⁻¹)).val
        refine ⟨a + c * (p : ℤ) ^ k, ?_⟩
        have hc : (p : ℤ) ∣ (t + 2 * a * c) := by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
          have hc_cast : (c : ZMod p) = -(t : ZMod p) * (2 * (a : ZMod p))⁻¹ := by
            simp only [c, Int.cast_natCast, ZMod.natCast_zmod_val]
          push_cast
          rw [hc_cast]
          have hmul : (2 * (a : ZMod p)) * (2 * (a : ZMod p))⁻¹ = 1 :=
            mul_inv_cancel₀ h2a
          linear_combination -(t : ZMod p) * hmul
        obtain ⟨s, hs⟩ := hc
        refine ⟨s + c ^ 2 * (p : ℤ) ^ (k - 1), ?_⟩
        have hpk : (p : ℤ) ^ k * (p : ℤ) ^ k = (p : ℤ) ^ (k + 1) * (p : ℤ) ^ (k - 1) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        calc (a + c * (p : ℤ) ^ k) ^ 2 + b ^ 2 + 1
            = (a ^ 2 + b ^ 2 + 1) + 2 * a * c * (p : ℤ) ^ k + c ^ 2 * ((p : ℤ) ^ k * (p : ℤ) ^ k) := by ring
          _ = (p : ℤ) ^ k * (t + 2 * a * c) + c ^ 2 * ((p : ℤ) ^ (k + 1) * (p : ℤ) ^ (k - 1)) := by
              rw [hab, hpk]; ring
          _ = (p : ℤ) ^ k * ((p : ℤ) * s) + c ^ 2 * ((p : ℤ) ^ (k + 1) * (p : ℤ) ^ (k - 1)) := by rw [hs]
          _ = (p : ℤ) ^ (k + 1) * (s + c ^ 2 * (p : ℤ) ^ (k - 1)) := by rw [pow_succ]; ring
      by_cases hpu : (p : ℤ) ∣ u
      · have hpv : ¬ (p : ℤ) ∣ v := fun hv => hnotboth ⟨hpu, hv⟩
        obtain ⟨v', hv'⟩ := lift v u (by linear_combination ht) hpv
        exact ⟨u, v', by rwa [add_comm (u ^ 2) (v' ^ 2)]⟩
      · obtain ⟨u', hu'⟩ := lift u v ht hpu
        exact ⟨u', v, hu'⟩

private lemma exists_sq_add_sq_add_one_zmod (m : ℕ) (hm : Odd m) :
    ∃ u v : ZMod m, u ^ 2 + v ^ 2 + 1 = 0 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm1 : m = 1
    · subst hm1; exact ⟨0, 0, by decide⟩
    have hm_gt : 1 < m := by rcases hm with ⟨k, rfl⟩; omega
    let p := m.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpm : p ∣ m := Nat.minFac_dvd m
    have hp2 : p ≠ 2 := by
      intro h2
      have : 2 ∣ m := h2 ▸ hpm
      rcases hm with ⟨k, rfl⟩; omega
    let k := m.factorization p
    have hk : 1 ≤ k := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpm
    have hpk_dvd : p ^ k ∣ m := Nat.ordProj_dvd m p
    let m' := m / p ^ k
    have hm_eq : p ^ k * m' = m := Nat.mul_div_cancel' hpk_dvd
    have hcop : Nat.Coprime (p ^ k) m' :=
      (Nat.coprime_ordCompl hp (show m ≠ 0 by omega)).pow_left k
    have hm'_odd : Odd m' := by
      rcases Nat.even_or_odd m' with ⟨r, hr⟩ | ho
      · exfalso
        have h2m : 2 ∣ m := by rw [← hm_eq]; exact dvd_mul_of_dvd_right ⟨r, by omega⟩ _
        rcases hm with ⟨s, rfl⟩; omega
      · exact ho
    have hm'_lt : m' < m := by
      have h1 : 1 < p ^ k := one_lt_pow₀ hp.one_lt (by omega)
      have hm'_pos : 0 < m' := Nat.pos_of_ne_zero (by intro h0; rw [h0, mul_zero] at hm_eq; omega)
      nlinarith
    obtain ⟨u1z, v1z, h1⟩ := exists_sq_add_sq_add_one_prime_pow p hp hp2 k hk
    let u1 : ZMod (p ^ k) := (u1z : ZMod (p ^ k))
    let v1 : ZMod (p ^ k) := (v1z : ZMod (p ^ k))
    have h1' : u1 ^ 2 + v1 ^ 2 + 1 = 0 := by
      have h1'' : ((u1z ^ 2 + v1z ^ 2 + 1 : ℤ) : ZMod (p ^ k)) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h1
      simpa [u1, v1] using h1''
    obtain ⟨u2, v2, h2⟩ := ih m' hm'_lt hm'_odd
    let e1 : ZMod m ≃+* ZMod (p ^ k) × ZMod m' :=
      (ZMod.ringEquivCongr hm_eq.symm).trans (ZMod.chineseRemainder hcop)
    refine ⟨e1.symm (u1, u2), e1.symm (v1, v2), ?_⟩
    apply e1.injective
    simp only [map_add, map_pow, map_one, map_zero, RingEquiv.apply_symm_apply]
    exact Prod.ext h1' h2

/- ## Step 2: The Hurwitz integer ring `H` in the `(1, i, j, ω)` basis -/

/-- Hurwitz integers `x + y i + z j + w ω` where `ω = (1 + i + j + k) / 2`.
The doubled `(1, i, j, k)` coordinates are `(2x + w, 2y + w, 2z + w, w)`. -/
structure H where
  x : ℤ
  y : ℤ
  z : ℤ
  w : ℤ
deriving DecidableEq

namespace H

lemma mk_eq {p q : H} (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) (hw : p.w = q.w) : p = q := by
  cases p; cases q; simp_all

def zero : H := ⟨0, 0, 0, 0⟩
def one : H := ⟨1, 0, 0, 0⟩
def ofInt (n : ℤ) : H := ⟨n, 0, 0, 0⟩
def ofLip (a b c d : ℤ) : H := ⟨a - d, b - d, c - d, 2 * d⟩

def add (p q : H) : H := ⟨p.x + q.x, p.y + q.y, p.z + q.z, p.w + q.w⟩
def neg (p : H) : H := ⟨-p.x, -p.y, -p.z, -p.w⟩
def sub (p q : H) : H := ⟨p.x - q.x, p.y - q.y, p.z - q.z, p.w - q.w⟩

def mul (p q : H) : H :=
  ⟨p.x * q.x - p.y * q.y - p.z * q.z - p.y * q.z + p.z * q.y - p.y * q.w - p.w * q.z - p.w * q.w,
   p.x * q.y + p.y * q.x - p.y * q.z + p.z * q.y + p.w * q.y + p.z * q.w - p.w * q.z,
   p.x * q.z + p.z * q.x - p.y * q.z + p.z * q.y - p.y * q.w + p.z * q.w + p.w * q.y,
   p.x * q.w + p.y * q.w - p.z * q.w + p.w * q.x - p.w * q.y + p.w * q.z + p.w * q.w +
     2 * p.y * q.z - 2 * p.z * q.y⟩

def conj (p : H) : H := ⟨p.x + p.w, -p.y, -p.z, -p.w⟩

def norm (p : H) : ℤ := p.x ^ 2 + p.y ^ 2 + p.z ^ 2 + p.w ^ 2 + p.x * p.w + p.y * p.w + p.z * p.w

instance : Zero H := ⟨zero⟩
instance : One H := ⟨one⟩
instance : Add H := ⟨add⟩
instance : Neg H := ⟨neg⟩
instance : Sub H := ⟨sub⟩
instance : Mul H := ⟨mul⟩

@[simp] lemma zero_x : (0 : H).x = 0 := rfl
@[simp] lemma zero_y : (0 : H).y = 0 := rfl
@[simp] lemma zero_z : (0 : H).z = 0 := rfl
@[simp] lemma zero_w : (0 : H).w = 0 := rfl
@[simp] lemma one_x : (1 : H).x = 1 := rfl
@[simp] lemma one_y : (1 : H).y = 0 := rfl
@[simp] lemma one_z : (1 : H).z = 0 := rfl
@[simp] lemma one_w : (1 : H).w = 0 := rfl
@[simp] lemma add_x (p q : H) : (p + q).x = p.x + q.x := rfl
@[simp] lemma add_y (p q : H) : (p + q).y = p.y + q.y := rfl
@[simp] lemma add_z (p q : H) : (p + q).z = p.z + q.z := rfl
@[simp] lemma add_w (p q : H) : (p + q).w = p.w + q.w := rfl
@[simp] lemma sub_x (p q : H) : (p - q).x = p.x - q.x := rfl
@[simp] lemma sub_y (p q : H) : (p - q).y = p.y - q.y := rfl
@[simp] lemma sub_z (p q : H) : (p - q).z = p.z - q.z := rfl
@[simp] lemma sub_w (p q : H) : (p - q).w = p.w - q.w := rfl
@[simp] lemma neg_x (p : H) : (-p).x = -p.x := rfl
@[simp] lemma neg_y (p : H) : (-p).y = -p.y := rfl
@[simp] lemma neg_z (p : H) : (-p).z = -p.z := rfl
@[simp] lemma neg_w (p : H) : (-p).w = -p.w := rfl
@[simp] lemma mul_x (p q : H) :
    (p * q).x = p.x * q.x - p.y * q.y - p.z * q.z - p.y * q.z + p.z * q.y - p.y * q.w - p.w * q.z - p.w * q.w := rfl
@[simp] lemma mul_y (p q : H) :
    (p * q).y = p.x * q.y + p.y * q.x - p.y * q.z + p.z * q.y + p.w * q.y + p.z * q.w - p.w * q.z := rfl
@[simp] lemma mul_z (p q : H) :
    (p * q).z = p.x * q.z + p.z * q.x - p.y * q.z + p.z * q.y - p.y * q.w + p.z * q.w + p.w * q.y := rfl
@[simp] lemma mul_w (p q : H) :
    (p * q).w = p.x * q.w + p.y * q.w - p.z * q.w + p.w * q.x - p.w * q.y + p.w * q.z + p.w * q.w +
      2 * p.y * q.z - 2 * p.z * q.y := rfl

lemma mul_assoc' (p q r : H) : p * q * r = p * (q * r) := by
  apply mk_eq <;> simp only [mul_x, mul_y, mul_z, mul_w] <;> ring

lemma one_mul' (p : H) : 1 * p = p := by
  apply mk_eq <;> simp only [mul_x, mul_y, mul_z, mul_w, one_x, one_y, one_z, one_w] <;> ring

lemma mul_one' (p : H) : p * 1 = p := by
  apply mk_eq <;> simp only [mul_x, mul_y, mul_z, mul_w, one_x, one_y, one_z, one_w] <;> ring

lemma mul_zero' (p : H) : p * 0 = 0 := by
  apply mk_eq <;> simp only [mul_x, mul_y, mul_z, mul_w, zero_x, zero_y, zero_z, zero_w] <;> ring

lemma zero_mul' (p : H) : 0 * p = 0 := by
  apply mk_eq <;> simp only [mul_x, mul_y, mul_z, mul_w, zero_x, zero_y, zero_z, zero_w] <;> ring

lemma add_mul' (p q r : H) : (p + q) * r = p * r + q * r := by
  apply mk_eq <;> simp only [mul_x, mul_y, mul_z, mul_w, add_x, add_y, add_z, add_w] <;> ring

lemma mul_add' (p q r : H) : p * (q + r) = p * q + p * r := by
  apply mk_eq <;> simp only [mul_x, mul_y, mul_z, mul_w, add_x, add_y, add_z, add_w] <;> ring

lemma sub_mul' (p q r : H) : (p - q) * r = p * r - q * r := by
  apply mk_eq <;> simp only [mul_x, mul_y, mul_z, mul_w, sub_x, sub_y, sub_z, sub_w] <;> ring

lemma mul_sub' (p q r : H) : p * (q - r) = p * q - p * r := by
  apply mk_eq <;> simp only [mul_x, mul_y, mul_z, mul_w, sub_x, sub_y, sub_z, sub_w] <;> ring

lemma ofInt_mul (n : ℤ) (p : H) : ofInt n * p = ⟨n * p.x, n * p.y, n * p.z, n * p.w⟩ := by
  apply mk_eq <;> simp only [mul_x, mul_y, mul_z, mul_w, ofInt] <;> ring

lemma mul_ofInt (p : H) (n : ℤ) : p * ofInt n = ⟨p.x * n, p.y * n, p.z * n, p.w * n⟩ := by
  apply mk_eq <;> simp only [mul_x, mul_y, mul_z, mul_w, ofInt] <;> ring

lemma ofInt_comm (n : ℤ) (p : H) : ofInt n * p = p * ofInt n := by
  rw [ofInt_mul, mul_ofInt]; apply mk_eq <;> ring

lemma mul_conj (p : H) : p * conj p = ofInt (norm p) := by
  apply mk_eq <;> simp only [mul_x, mul_y, mul_z, mul_w, conj, ofInt, norm] <;> ring

lemma conj_mul_self (p : H) : conj p * p = ofInt (norm p) := by
  apply mk_eq <;> simp only [mul_x, mul_y, mul_z, mul_w, conj, ofInt, norm] <;> ring

lemma norm_mul (p q : H) : norm (p * q) = norm p * norm q := by
  simp only [mul_x, mul_y, mul_z, mul_w, norm]; ring

lemma four_norm (p : H) :
    4 * norm p = (2 * p.x + p.w) ^ 2 + (2 * p.y + p.w) ^ 2 + (2 * p.z + p.w) ^ 2 + p.w ^ 2 := by
  simp only [norm]; ring

lemma norm_nonneg (p : H) : 0 ≤ norm p := by
  have h := four_norm p
  nlinarith [sq_nonneg (2 * p.x + p.w), sq_nonneg (2 * p.y + p.w),
             sq_nonneg (2 * p.z + p.w), sq_nonneg p.w]

lemma norm_eq_zero_iff (p : H) : norm p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have h4 := four_norm p
    have h0 : (2 * p.x + p.w) ^ 2 + (2 * p.y + p.w) ^ 2 + (2 * p.z + p.w) ^ 2 + p.w ^ 2 = 0 := by
      linarith
    have hx : 2 * p.x + p.w = 0 := by nlinarith [sq_nonneg (2 * p.x + p.w), sq_nonneg (2 * p.y + p.w), sq_nonneg (2 * p.z + p.w), sq_nonneg p.w]
    have hy : 2 * p.y + p.w = 0 := by nlinarith [sq_nonneg (2 * p.x + p.w), sq_nonneg (2 * p.y + p.w), sq_nonneg (2 * p.z + p.w), sq_nonneg p.w]
    have hz : 2 * p.z + p.w = 0 := by nlinarith [sq_nonneg (2 * p.x + p.w), sq_nonneg (2 * p.y + p.w), sq_nonneg (2 * p.z + p.w), sq_nonneg p.w]
    have hw : p.w = 0 := by nlinarith [sq_nonneg (2 * p.x + p.w), sq_nonneg (2 * p.y + p.w), sq_nonneg (2 * p.z + p.w), sq_nonneg p.w]
    apply mk_eq <;> simp only [zero_x, zero_y, zero_z, zero_w] <;> omega
  · rintro rfl; simp [norm]

lemma norm_pos_iff (p : H) : 0 < norm p ↔ p ≠ 0 := by
  have h := norm_nonneg p
  constructor
  · intro hp h0; rw [(norm_eq_zero_iff p).mpr h0] at hp; omega
  · intro hne
    rcases lt_or_eq_of_le h with hlt | heq
    · exact hlt
    · exact absurd ((norm_eq_zero_iff p).mp heq.symm) hne

lemma mul_right_cancel' {p q r : H} (hr : r ≠ 0) (h : p * r = q * r) : p = q := by
  have h1 : (p - q) * r = 0 := by rw [sub_mul', h]; apply mk_eq <;> simp
  have h2 : norm (p - q) * norm r = 0 := by
    rw [← norm_mul, h1, (norm_eq_zero_iff 0).mpr rfl]
  have hrn : norm r ≠ 0 := ne_of_gt ((norm_pos_iff r).mpr hr)
  have hpq : norm (p - q) = 0 := (mul_eq_zero.mp h2).resolve_right hrn
  have hsub : p - q = 0 := (norm_eq_zero_iff (p - q)).mp hpq
  apply mk_eq
  · have := congrArg H.x hsub; simp at this; omega
  · have := congrArg H.y hsub; simp at this; omega
  · have := congrArg H.z hsub; simp at this; omega
  · have := congrArg H.w hsub; simp at this; omega

lemma norm_ofInt (n : ℤ) : norm (ofInt n) = n ^ 2 := by
  simp [norm, ofInt]

lemma norm_ofLip (a b c d : ℤ) : norm (ofLip a b c d) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  simp [norm, ofLip]; ring

/-- Left-Euclidean division in `H`: for `β ≠ 0`, `∃ q r, α = q * β + r ∧ norm r < norm β`. -/
lemma left_div (α β : H) (hβ : β ≠ 0) : ∃ q r : H, α = q * β + r ∧ norm r < norm β := by
  set d := norm β
  have hd : 0 < d := (norm_pos_iff β).mpr hβ
  set c := α * conj β
  set a0 := 2 * c.x + c.w
  set a1 := 2 * c.y + c.w
  set a2 := 2 * c.z + c.w
  set a3 := c.w
  set k0 := (a0 + d) / (2 * d)
  set k1 := (a1 + d) / (2 * d)
  set k2 := (a2 + d) / (2 * d)
  set k3 := (a3 + d) / (2 * d)
  have hr0 : -d ≤ a0 - 2 * d * k0 ∧ a0 - 2 * d * k0 < d := by
    have h0 : (a0 + d) % (2 * d) + 2 * d * k0 = a0 + d := Int.emod_add_mul_ediv (a0 + d) (2 * d)
    have h1 := Int.emod_nonneg (a0 + d) (show 2 * d ≠ 0 by omega)
    have h2 := Int.emod_lt_of_pos (a0 + d) (show 0 < 2 * d by omega)
    constructor <;> linarith
  have hr1 : -d ≤ a1 - 2 * d * k1 ∧ a1 - 2 * d * k1 < d := by
    have h0 : (a1 + d) % (2 * d) + 2 * d * k1 = a1 + d := Int.emod_add_mul_ediv (a1 + d) (2 * d)
    have h1 := Int.emod_nonneg (a1 + d) (show 2 * d ≠ 0 by omega)
    have h2 := Int.emod_lt_of_pos (a1 + d) (show 0 < 2 * d by omega)
    constructor <;> linarith
  have hr2 : -d ≤ a2 - 2 * d * k2 ∧ a2 - 2 * d * k2 < d := by
    have h0 : (a2 + d) % (2 * d) + 2 * d * k2 = a2 + d := Int.emod_add_mul_ediv (a2 + d) (2 * d)
    have h1 := Int.emod_nonneg (a2 + d) (show 2 * d ≠ 0 by omega)
    have h2 := Int.emod_lt_of_pos (a2 + d) (show 0 < 2 * d by omega)
    constructor <;> linarith
  have hr3 : -d ≤ a3 - 2 * d * k3 ∧ a3 - 2 * d * k3 < d := by
    have h0 : (a3 + d) % (2 * d) + 2 * d * k3 = a3 + d := Int.emod_add_mul_ediv (a3 + d) (2 * d)
    have h1 := Int.emod_nonneg (a3 + d) (show 2 * d ≠ 0 by omega)
    have h2 := Int.emod_lt_of_pos (a3 + d) (show 0 < 2 * d by omega)
    constructor <;> linarith
  have from_q : ∀ q : H, 4 * norm (c - q * ofInt d) < 4 * d ^ 2 →
      ∃ r : H, α = q * β + r ∧ norm r < d := by
    intro q hq
    refine ⟨α - q * β, ?_, ?_⟩
    · apply mk_eq <;> simp
    · have hprod : (α - q * β) * conj β = c - q * ofInt d := by
        rw [sub_mul', mul_assoc', mul_conj]
      have hn : norm (α - q * β) * d = norm (c - q * ofInt d) := by
        have hnc := norm_mul (α - q * β) (conj β)
        have hconj : norm (conj β) = d := by simp [norm, conj, d]; ring
        rw [hprod, hconj] at hnc
        exact hnc.symm
      nlinarith
  by_cases hall : a0 - 2 * d * k0 = -d ∧ a1 - 2 * d * k1 = -d ∧ a2 - 2 * d * k2 = -d ∧ a3 - 2 * d * k3 = -d
  · refine ⟨⟨k0 - k3, k1 - k3, k2 - k3, 2 * k3 - 1⟩, ?_⟩
    apply from_q
    rw [four_norm]
    simp only [sub_x, sub_y, sub_z, sub_w, mul_ofInt]
    have e0 : 2 * (c.x - (k0 - k3) * d) + (c.w - (2 * k3 - 1) * d) = 0 := by
      have := hall.1; dsimp only [a0] at this; linarith
    have e1 : 2 * (c.y - (k1 - k3) * d) + (c.w - (2 * k3 - 1) * d) = 0 := by
      have := hall.2.1; dsimp only [a1] at this; linarith
    have e2 : 2 * (c.z - (k2 - k3) * d) + (c.w - (2 * k3 - 1) * d) = 0 := by
      have := hall.2.2.1; dsimp only [a2] at this; linarith
    have e3 : c.w - (2 * k3 - 1) * d = 0 := by
      have := hall.2.2.2; dsimp only [a3] at this; linarith
    rw [e0, e1, e2, e3]; nlinarith
  · refine ⟨⟨k0 - k3, k1 - k3, k2 - k3, 2 * k3⟩, ?_⟩
    apply from_q
    rw [four_norm]
    simp only [sub_x, sub_y, sub_z, sub_w, mul_ofInt]
    have e0 : 2 * (c.x - (k0 - k3) * d) + (c.w - 2 * k3 * d) = a0 - 2 * d * k0 := by
      dsimp only [a0]; ring
    have e1 : 2 * (c.y - (k1 - k3) * d) + (c.w - 2 * k3 * d) = a1 - 2 * d * k1 := by
      dsimp only [a1]; ring
    have e2 : 2 * (c.z - (k2 - k3) * d) + (c.w - 2 * k3 * d) = a2 - 2 * d * k2 := by
      dsimp only [a2]; ring
    have e3 : c.w - 2 * k3 * d = a3 - 2 * d * k3 := by
      dsimp only [a3]; ring
    rw [e0, e1, e2, e3]
    have s0 : (a0 - 2 * d * k0) ^ 2 ≤ d ^ 2 := by nlinarith
    have s1 : (a1 - 2 * d * k1) ^ 2 ≤ d ^ 2 := by nlinarith
    have s2 : (a2 - 2 * d * k2) ^ 2 ≤ d ^ 2 := by nlinarith
    have s3 : (a3 - 2 * d * k3) ^ 2 ≤ d ^ 2 := by nlinarith
    by_cases h0 : a0 - 2 * d * k0 = -d
    · by_cases h1 : a1 - 2 * d * k1 = -d
      · by_cases h2 : a2 - 2 * d * k2 = -d
        · have h3 : a3 - 2 * d * k3 ≠ -d := fun h3 => hall ⟨h0, h1, h2, h3⟩
          have h3' : -d < a3 - 2 * d * k3 := by omega
          have s3' : (a3 - 2 * d * k3) ^ 2 < d ^ 2 := by nlinarith
          linarith
        · have h2' : -d < a2 - 2 * d * k2 := by omega
          have s2' : (a2 - 2 * d * k2) ^ 2 < d ^ 2 := by nlinarith
          linarith
      · have h1' : -d < a1 - 2 * d * k1 := by omega
        have s1' : (a1 - 2 * d * k1) ^ 2 < d ^ 2 := by nlinarith
        linarith
    · have h0' : -d < a0 - 2 * d * k0 := by omega
      have s0' : (a0 - 2 * d * k0) ^ 2 < d ^ 2 := by nlinarith
      linarith

/-- Every `α ∈ H` has a left unit associate `u * α` (`norm u = 1`) that is Lipschitz (`(u * α).w % 2 = 0`). -/
lemma exists_left_unit_lip (α : H) : ∃ u : H, norm u = 1 ∧ (u * α).w % 2 = 0 := by
  by_cases hw : α.w % 2 = 0
  · refine ⟨1, by simp [norm], ?_⟩
    rw [one_mul']; exact hw
  · by_cases hxyz : (α.x - α.y + α.z) % 2 = 0
    · refine ⟨⟨1, 0, 0, -1⟩, by simp [norm], ?_⟩
      simp only [mul_w]
      omega
    · refine ⟨⟨0, 0, 0, 1⟩, by simp [norm], ?_⟩
      simp only [mul_w]
      omega

/-- Extract Lipschitz integer coordinates from `α` with `α.w % 2 = 0`. -/
def toLipTuple (α : H) : Fin 4 → ℤ :=
  ![α.x + α.w / 2, α.y + α.w / 2, α.z + α.w / 2, α.w / 2]

lemma toLipTuple_sq_sum (α : H) (hw : α.w % 2 = 0) :
    ∑ i : Fin 4, (toLipTuple α i) ^ 2 = norm α := by
  set q := α.w / 2 with hq
  have hw2 : α.w = 2 * q := by omega
  simp only [Fin.sum_univ_four, toLipTuple, Matrix.cons_val_zero, Matrix.cons_val_one,
             Matrix.cons_val, norm, ← hq]
  rw [hw2]; ring

lemma toLipTuple_inj {α β : H} (hα : α.w % 2 = 0) (hβ : β.w % 2 = 0)
    (h : toLipTuple α = toLipTuple β) : α = β := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [toLipTuple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2 h3
  apply mk_eq <;> omega

/-- The 8 Lipschitz units `{±1, ±i, ±j, ±k}` in `H`. -/
def lipUnit : Fin 8 → H
  | 0 => ⟨1, 0, 0, 0⟩
  | 1 => ⟨-1, 0, 0, 0⟩
  | 2 => ⟨0, 1, 0, 0⟩
  | 3 => ⟨0, -1, 0, 0⟩
  | 4 => ⟨0, 0, 1, 0⟩
  | 5 => ⟨0, 0, -1, 0⟩
  | 6 => ⟨-1, -1, -1, 2⟩
  | 7 => ⟨1, 1, 1, -2⟩

lemma lipUnit_norm (i : Fin 8) : norm (lipUnit i) = 1 := by
  fin_cases i <;> decide

lemma lipUnit_inj : Function.Injective lipUnit := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [lipUnit]

lemma lipUnit_mul_even (i : Fin 8) (α : H) (hα : α.w % 2 = 0) : (lipUnit i * α).w % 2 = 0 := by
  fin_cases i <;> simp only [lipUnit, mul_w] <;> omega

end H

/- ## Step 3: Surjective ring hom `φ : H → Matrix (Fin 2) (Fin 2) (ZMod m)` and ideals `J_t` -/

section ModM

variable {m : ℕ} (k : ℕ) (hm : m = 2 * k + 1) (u v : ZMod m)

private def inv2 (k : ℕ) (_hm : m = 2 * k + 1) : ZMod m := ((k + 1 : ℕ) : ZMod m)

private lemma two_mul_inv2 (k : ℕ) (hm : m = 2 * k + 1) : (2 : ZMod m) * inv2 k hm = 1 := by
  unfold inv2
  have h : (2 : ZMod m) * ((k + 1 : ℕ) : ZMod m) = ((2 * k + 1 + 1 : ℕ) : ZMod m) := by
    push_cast; ring
  rw [h, ← hm, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]

private def psi (u v : ZMod m) (a b c d : ZMod m) : Matrix (Fin 2) (Fin 2) (ZMod m) :=
  ![![a + b * u + d * v, b * v - c - d * u],
    ![b * v + c - d * u, a - b * u - d * v]]

private lemma psi_mul (huv : u ^ 2 + v ^ 2 + 1 = 0) (a1 b1 c1 d1 a2 b2 c2 d2 : ZMod m) :
    psi u v (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2)
            (a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2)
            (a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2)
            (a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2) =
    psi u v a1 b1 c1 d1 * psi u v a2 b2 c2 d2 := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
  · simp [psi]
    first
    | linear_combination -(b1 * b2 + d1 * d2) * huv
    | linear_combination (b1 * d2 - d1 * b2) * huv
    | linear_combination -(b1 * d2 - d1 * b2) * huv

private lemma psi_det (huv : u ^ 2 + v ^ 2 + 1 = 0) (a b c d : ZMod m) :
    (psi u v a b c d).det = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  rw [Matrix.det_fin_two]
  simp only [psi, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination -(b ^ 2 + d ^ 2) * huv

private def phi (k : ℕ) (hm : m = 2 * k + 1) (u v : ZMod m) (α : H) :
    Matrix (Fin 2) (Fin 2) (ZMod m) :=
  inv2 k hm • psi u v ((2 * α.x + α.w : ℤ) : ZMod m) ((2 * α.y + α.w : ℤ) : ZMod m)
                      ((2 * α.z + α.w : ℤ) : ZMod m) ((α.w : ℤ) : ZMod m)

private lemma phi_zero : phi k hm u v 0 = 0 := by
  ext i j; simp only [phi, Matrix.smul_apply, smul_eq_mul]; fin_cases i <;> fin_cases j <;> simp [psi]

private lemma phi_add (α β : H) : phi k hm u v (α + β) = phi k hm u v α + phi k hm u v β := by
  ext i j; simp only [phi, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [psi] <;> ring

private lemma phi_sub (α β : H) : phi k hm u v (α - β) = phi k hm u v α - phi k hm u v β := by
  ext i j; simp only [phi, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [psi] <;> ring

private lemma phi_ofInt (n : ℤ) :
    phi k hm u v (H.ofInt n) = ![![(n : ZMod m), 0], ![0, (n : ZMod m)]] := by
  have h2 := two_mul_inv2 k hm
  ext i j; simp only [phi, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [psi, H.ofInt] <;>
    linear_combination (n : ZMod m) * h2

private lemma phi_ofLip (a b c d : ℤ) :
    phi k hm u v (H.ofLip a b c d) = psi u v (a : ZMod m) (b : ZMod m) (c : ZMod m) (d : ZMod m) := by
  have h2 := two_mul_inv2 k hm
  ext i j; simp only [phi, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [psi, H.ofLip] <;>
    first
    | linear_combination ((a : ZMod m) + b * u + d * v) * h2
    | linear_combination ((b : ZMod m) * v - c - d * u) * h2
    | linear_combination ((b : ZMod m) * v + c - d * u) * h2
    | linear_combination ((a : ZMod m) - b * u - d * v) * h2

private lemma phi_mul (huv : u ^ 2 + v ^ 2 + 1 = 0) (α β : H) :
    phi k hm u v (α * β) = phi k hm u v α * phi k hm u v β := by
  have h2 := two_mul_inv2 k hm
  set a1 : ZMod m := ((2 * α.x + α.w : ℤ) : ZMod m)
  set b1 : ZMod m := ((2 * α.y + α.w : ℤ) : ZMod m)
  set c1 : ZMod m := ((2 * α.z + α.w : ℤ) : ZMod m)
  set d1 : ZMod m := ((α.w : ℤ) : ZMod m)
  set a2 : ZMod m := ((2 * β.x + β.w : ℤ) : ZMod m)
  set b2 : ZMod m := ((2 * β.y + β.w : ℤ) : ZMod m)
  set c2 : ZMod m := ((2 * β.z + β.w : ℤ) : ZMod m)
  set d2 : ZMod m := ((β.w : ℤ) : ZMod m)
  have hA : (2 : ZMod m) * ((2 * (α * β).x + (α * β).w : ℤ) : ZMod m) =
      a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2 := by
    simp only [a1, b1, c1, d1, a2, b2, c2, d2, H.mul_x, H.mul_w]; push_cast; ring
  have hB : (2 : ZMod m) * ((2 * (α * β).y + (α * β).w : ℤ) : ZMod m) =
      a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2 := by
    simp only [a1, b1, c1, d1, a2, b2, c2, d2, H.mul_y, H.mul_w]; push_cast; ring
  have hC : (2 : ZMod m) * ((2 * (α * β).z + (α * β).w : ℤ) : ZMod m) =
      a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2 := by
    simp only [a1, b1, c1, d1, a2, b2, c2, d2, H.mul_z, H.mul_w]; push_cast; ring
  have hD : (2 : ZMod m) * (((α * β).w : ℤ) : ZMod m) =
      a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2 := by
    simp only [a1, b1, c1, d1, a2, b2, c2, d2, H.mul_w]; push_cast; ring
  have hpsi := psi_mul u v huv a1 b1 c1 d1 a2 b2 c2 d2
  have hscale : (2 : ZMod m) • psi u v ((2 * (α * β).x + (α * β).w : ℤ) : ZMod m)
      ((2 * (α * β).y + (α * β).w : ℤ) : ZMod m)
      ((2 * (α * β).z + (α * β).w : ℤ) : ZMod m) (((α * β).w : ℤ) : ZMod m) =
      psi u v a1 b1 c1 d1 * psi u v a2 b2 c2 d2 := by
    rw [← hpsi, ← hA, ← hB, ← hC, ← hD]
    ext i j; simp only [Matrix.smul_apply, smul_eq_mul]; fin_cases i <;> fin_cases j <;> simp [psi] <;> ring
  have hleft : phi k hm u v (α * β) =
      (inv2 k hm * inv2 k hm) • (psi u v a1 b1 c1 d1 * psi u v a2 b2 c2 d2) := by
    rw [← hscale, smul_smul, show inv2 k hm * inv2 k hm * 2 = inv2 k hm by linear_combination inv2 k hm * h2]
    rfl
  rw [hleft, phi, phi, smul_mul_assoc, mul_smul_comm, smul_smul]

private lemma phi_det (huv : u ^ 2 + v ^ 2 + 1 = 0) (α : H) :
    (phi k hm u v α).det = ((H.norm α : ℤ) : ZMod m) := by
  have h2 := two_mul_inv2 k hm
  simp only [phi, Matrix.det_smul, Fintype.card_fin, psi_det u v huv]
  have h4 : ((2 * α.x + α.w : ℤ) : ZMod m) ^ 2 + ((2 * α.y + α.w : ℤ) : ZMod m) ^ 2 +
      ((2 * α.z + α.w : ℤ) : ZMod m) ^ 2 + ((α.w : ℤ) : ZMod m) ^ 2 =
      ((4 * H.norm α : ℤ) : ZMod m) := by
    rw [H.four_norm]; push_cast; ring
  rw [h4]
  push_cast
  have h4e : inv2 k hm ^ 2 * 4 = 1 := by linear_combination (2 * inv2 k hm + 1) * h2
  linear_combination ((H.norm α : ℤ) : ZMod m) * h4e

private lemma phi_surj (huv : u ^ 2 + v ^ 2 + 1 = 0) (p q r s : ZMod m) :
    ∃ α : H, phi k hm u v α = ![![p, q], ![r, s]] := by
  have : NeZero m := ⟨by omega⟩
  have h2 := two_mul_inv2 k hm
  set e := inv2 k hm
  set x0 : ZMod m := (p + s) * e
  set y0 : ZMod m := (-u * (p - s) - v * (q + r)) * e
  set z0 : ZMod m := (r - q) * e
  set w0 : ZMod m := (-v * (p - s) + u * (q + r)) * e
  refine ⟨H.ofLip (x0.val : ℤ) (y0.val : ℤ) (z0.val : ℤ) (w0.val : ℤ), ?_⟩
  rw [phi_ofLip k hm u v]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [psi, x0, y0, z0, w0]
    first
    | linear_combination p * h2 - (p - s) * e * huv
    | linear_combination q * h2 - (q + r) * e * huv
    | linear_combination r * h2 - (q + r) * e * huv
    | linear_combination s * h2 + (p - s) * e * huv

/-- For each `t : ZMod m`, there exists `α : H` with `H.norm α = m` and `phi α *ᵥ ![1, t] = 0`,
and such that `∀ β, phi β *ᵥ ![1, t] = 0 → ∃ δ, β = δ * α`. -/
private lemma exists_ideal_gen (huv : u ^ 2 + v ^ 2 + 1 = 0) (hm_pos : 0 < m) (t : ZMod m) :
    ∃ α : H, H.norm α = (m : ℤ) ∧
      phi k hm u v α *ᵥ ![1, t] = 0 ∧
      ∀ β : H, phi k hm u v β *ᵥ ![1, t] = 0 → ∃ δ : H, β = δ * α := by
  let inJ (β : H) : Prop := phi k hm u v β *ᵥ ![1, t] = 0
  have hm_inJ : inJ (H.ofInt (m : ℤ)) := by
    simp only [inJ, phi_ofInt k hm u v, Int.cast_natCast, ZMod.natCast_self]
    ext i; fin_cases i <;> simp [Matrix.mulVec]
  have hex : ∃ n : ℕ, 0 < n ∧ ∃ α : H, inJ α ∧ H.norm α = (n : ℤ) := by
    refine ⟨m ^ 2, by positivity, H.ofInt (m : ℤ), hm_inJ, ?_⟩
    rw [H.norm_ofInt]; push_cast; ring
  classical
  let n0 := Nat.find hex
  have hn0 := Nat.find_spec hex
  obtain ⟨hn0_pos, α, hα_inJ, hα_norm⟩ := hn0
  have hα_ne : α ≠ 0 := (H.norm_pos_iff α).mp (by omega)
  have hdiv : ∀ β : H, inJ β → ∃ δ : H, β = δ * α := by
    intro β hβ
    obtain ⟨q, r, hqr, hr_lt⟩ := H.left_div β α hα_ne
    have hr_inJ : inJ r := by
      have hr_eq : r = β - q * α := by
        rw [hqr]; apply H.mk_eq <;> simp
      simp only [inJ, hr_eq, phi_sub k hm u v, phi_mul k hm u v huv, Matrix.sub_mulVec,
                 ← Matrix.mulVec_mulVec]
      have h1 : phi k hm u v β *ᵥ ![1, t] = 0 := hβ
      have h2 : phi k hm u v α *ᵥ ![1, t] = 0 := hα_inJ
      rw [h1, h2, Matrix.mulVec_zero, sub_self]
    by_cases hr0 : r = 0
    · refine ⟨q, ?_⟩; rw [hqr, hr0]; apply H.mk_eq <;> simp
    · exfalso
      have hr_pos : 0 < H.norm r := (H.norm_pos_iff r).mpr hr0
      have hlt : (H.norm r).toNat < n0 := by omega
      exact Nat.find_min hex hlt ⟨by omega, r, hr_inJ, by omega⟩
  -- Express `m = γ * α`
  obtain ⟨γ, hγ⟩ := hdiv (H.ofInt (m : ℤ)) hm_inJ
  -- Express `β_t` with `phi β_t = ![![-t, 1], ![0, 0]]` as `δ * α`
  obtain ⟨βt, hβt⟩ := phi_surj k hm u v huv (-t) 1 0 0
  have hβt_inJ : inJ βt := by
    simp only [inJ, hβt]
    ext i; fin_cases i <;> simp [Matrix.mulVec]
  obtain ⟨δ, hδ⟩ := hdiv βt hβt_inJ
  -- Show `m ∣ H.norm α` from `det (phi α) = 0`
  have hdet_α : (phi k hm u v α).det = 0 := by
    have h0 := congrFun hα_inJ 0
    have h1 := congrFun hα_inJ 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
               Matrix.cons_val_one, Pi.zero_apply] at h0 h1
    simp only [Matrix.det_fin_two]
    linear_combination (phi k hm u v α 1 1) * h0 - (phi k hm u v α 0 1) * h1
  have hm_dvd_α : (m : ℤ) ∣ H.norm α := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← phi_det k hm u v huv α, hdet_α]
  -- Show `α * γ = H.ofInt m` by cancelling `α` on the right
  have hαγ : α * γ = H.ofInt (m : ℤ) := by
    apply H.mul_right_cancel' hα_ne
    rw [H.mul_assoc', ← hγ, H.ofInt_comm]
  -- Show `phi βt * phi γ = 0`, hence `det (phi γ) = 0`, hence `m ∣ H.norm γ`
  have hβtγ : phi k hm u v βt * phi k hm u v γ = 0 := by
    rw [hδ, phi_mul k hm u v huv, Matrix.mul_assoc, ← phi_mul k hm u v huv, hαγ,
        phi_ofInt k hm u v]
    have hzero : (![![((m : ℤ) : ZMod m), 0], ![0, ((m : ℤ) : ZMod m)]] : Matrix (Fin 2) (Fin 2) (ZMod m)) = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [hzero]
    exact Matrix.mul_zero _
  have hdet_γ : (phi k hm u v γ).det = 0 := by
    have h00 := congrFun (congrFun hβtγ 0) 0
    have h01 := congrFun (congrFun hβtγ 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] at h00 h01
    rw [hβt] at h00 h01
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h01
    simp only [Matrix.det_fin_two]
    linear_combination (phi k hm u v γ 0 0) * h01 - (phi k hm u v γ 0 1) * h00
  have hm_dvd_γ : (m : ℤ) ∣ H.norm γ := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← phi_det k hm u v huv γ, hdet_γ]
  -- Combine `m ∣ norm α`, `m ∣ norm γ`, and `norm γ * norm α = m^2`
  have hprod : H.norm γ * H.norm α = (m : ℤ) ^ 2 := by
    rw [← H.norm_mul, ← hγ, H.norm_ofInt]
  obtain ⟨c1, hc1⟩ := hm_dvd_α
  obtain ⟨c2, hc2⟩ := hm_dvd_γ
  have hc_prod : c2 * c1 = 1 := by
    have : (m : ℤ) ^ 2 * (c2 * c1) = (m : ℤ) ^ 2 * 1 := by
      calc (m : ℤ) ^ 2 * (c2 * c1) = ((m : ℤ) * c2) * ((m : ℤ) * c1) := by ring
        _ = H.norm γ * H.norm α := by rw [← hc2, ← hc1]
        _ = (m : ℤ) ^ 2 * 1 := by rw [hprod]; ring
    exact mul_left_cancel₀ (by positivity : (m : ℤ) ^ 2 ≠ 0) this
  have hc1_pos : 0 < c1 := by nlinarith [(H.norm_pos_iff α).mpr hα_ne]
  have hc1_eq : c1 = 1 := Int.eq_one_of_mul_eq_one_left (by omega) hc_prod
  have hnorm_eq : H.norm α = (m : ℤ) := by rw [hc1, hc1_eq, mul_one]
  exact ⟨α, hnorm_eq, hα_inJ, hdiv⟩

end ModM

/- ## Steps 4 & 5: Counting signed and unsigned 4-square representations -/

private lemma odd_four_squares_card_lower (m : ℕ) (hm : Odd m) :
    m ≤ 2 * ((univ : Finset (Fin 4 → Fin (m + 1))).filter
      fun v => ∑ i, ((v i : ℕ) ^ 2) = m).card := by
  classical
  rcases hm with ⟨k, rfl⟩
  set m := 2 * k + 1 with hm_eq
  have hm_pos : 0 < m := by omega
  have : NeZero m := ⟨by omega⟩
  obtain ⟨u, v, huv⟩ := exists_sq_add_sq_add_one_zmod m ⟨k, hm_eq⟩
  -- For each `t : ZMod m`, choose a Lipschitz generator `L t ∈ J_t` of norm `m`
  have hgen : ∀ t : ZMod m, ∃ L : H, H.norm L = (m : ℤ) ∧ L.w % 2 = 0 ∧
      phi k hm_eq u v L *ᵥ ![1, t] = 0 ∧
      ∀ β : H, phi k hm_eq u v β *ᵥ ![1, t] = 0 → ∃ δ : H, β = δ * L := by
    intro t
    obtain ⟨α, hnorm, hinJ, hdiv⟩ := exists_ideal_gen k hm_eq u v huv hm_pos t
    obtain ⟨u0, hu0_norm, hu0_lip⟩ := H.exists_left_unit_lip α
    refine ⟨u0 * α, ?_, hu0_lip, ?_, ?_⟩
    · rw [H.norm_mul, hu0_norm, one_mul, hnorm]
    · rw [phi_mul k hm_eq u v huv, ← Matrix.mulVec_mulVec, hinJ, Matrix.mulVec_zero]
    · intro β hβ
      obtain ⟨δ, rfl⟩ := hdiv β hβ
      refine ⟨δ * H.conj u0, ?_⟩
      rw [H.mul_assoc', ← H.mul_assoc' (H.conj u0) u0 α, H.conj_mul_self, hu0_norm,
          show H.ofInt 1 = 1 from rfl, H.one_mul']
  choose L hL_norm hL_lip hL_inJ hL_div using hgen
  -- Map `(t, i) : ZMod m × Fin 8` to signed 4-tuples `H.toLipTuple (H.lipUnit i * L t)`
  let f : ZMod m × Fin 8 → (Fin 4 → ℤ) := fun p => H.toLipTuple (H.lipUnit p.2 * L p.1)
  have hf_inj : Function.Injective f := by
    rintro ⟨t1, i1⟩ ⟨t2, i2⟩ heq
    have he1 : (H.lipUnit i1 * L t1).w % 2 = 0 := H.lipUnit_mul_even i1 (L t1) (hL_lip t1)
    have he2 : (H.lipUnit i2 * L t2).w % 2 = 0 := H.lipUnit_mul_even i2 (L t2) (hL_lip t2)
    have hH : H.lipUnit i1 * L t1 = H.lipUnit i2 * L t2 := H.toLipTuple_inj he1 he2 heq
    have ht : t1 = t2 := by
      by_contra hne
      obtain ⟨β1, hβ1⟩ := phi_surj k hm_eq u v huv (-t1) 1 0 0
      have hβ1_inJ1 : phi k hm_eq u v β1 *ᵥ ![1, t1] = 0 := by
        rw [hβ1]; ext i; fin_cases i <;> simp [Matrix.mulVec]
      obtain ⟨δ1, hδ1⟩ := hL_div t1 β1 hβ1_inJ1
      have hL1_inJ2 : phi k hm_eq u v (L t1) *ᵥ ![1, t2] = 0 := by
        have hL1_eq : L t1 = (H.conj (H.lipUnit i1) * H.lipUnit i2) * L t2 := by
          rw [H.mul_assoc', ← hH, ← H.mul_assoc', H.conj_mul_self, H.lipUnit_norm,
              show H.ofInt 1 = 1 from rfl, H.one_mul']
        rw [hL1_eq, phi_mul k hm_eq u v huv, ← Matrix.mulVec_mulVec, hL_inJ t2, Matrix.mulVec_zero]
      have hβ1_inJ2 : phi k hm_eq u v β1 *ᵥ ![1, t2] = 0 := by
        rw [hδ1, phi_mul k hm_eq u v huv, ← Matrix.mulVec_mulVec, hL1_inJ2, Matrix.mulVec_zero]
      rw [hβ1] at hβ1_inJ2
      have h0 := congrFun hβ1_inJ2 0
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
                 Matrix.cons_val_one, Pi.zero_apply] at h0
      exact hne (by linear_combination -h0)
    subst ht
    have hL_ne : L t1 ≠ 0 := (H.norm_pos_iff (L t1)).mp (by rw [hL_norm]; omega)
    have hui : H.lipUnit i1 = H.lipUnit i2 := H.mul_right_cancel' hL_ne hH
    exact Prod.ext rfl (H.lipUnit_inj hui)
  -- Image `S_signed` has cardinality `8 * m`
  let S_signed : Finset (Fin 4 → ℤ) := univ.image f
  have hS_signed_card : S_signed.card = 8 * m := by
    rw [card_image_of_injective _ hf_inj, card_univ, Fintype.card_prod, ZMod.card, Fintype.card_fin]
    ring
  -- Map each signed tuple `x ∈ S_signed` to its unsigned tuple `g x : Fin 4 → Fin (m + 1)`
  let T : Finset (Fin 4 → Fin (m + 1)) :=
    univ.filter fun w => ∑ i, ((w i : ℕ) ^ 2) = m
  have hf_sq : ∀ x ∈ S_signed, ∑ i : Fin 4, (x i) ^ 2 = (m : ℤ) := by
    intro x hx
    rcases mem_image.mp hx with ⟨⟨t, j⟩, _, rfl⟩
    rw [H.toLipTuple_sq_sum _ (H.lipUnit_mul_even j (L t) (hL_lip t)),
        H.norm_mul, H.lipUnit_norm, one_mul, hL_norm]
  let g : (Fin 4 → ℤ) → (Fin 4 → Fin (m + 1)) := fun x i =>
    ⟨(x i).natAbs % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
  have hg_val : ∀ x ∈ S_signed, ∀ i : Fin 4, ((g x i : ℕ) : ℕ) = (x i).natAbs := by
    intro x hx i
    have hsum := hf_sq x hx
    have hle : (x i) ^ 2 ≤ (m : ℤ) := by
      have := Finset.single_le_sum (f := fun j : Fin 4 => (x j) ^ 2)
        (fun j _ => sq_nonneg (x j)) (mem_univ i)
      linarith
    have habs : (x i).natAbs < m + 1 := by
      have hsq : ((x i).natAbs : ℤ) ^ 2 ≤ (m : ℤ) := by
        rw [Int.natAbs_sq]; exact hle
      have hsq' : (x i).natAbs ^ 2 ≤ m := by exact_mod_cast hsq
      nlinarith
    exact Nat.mod_eq_of_lt habs
  have hg_mem : ∀ x ∈ S_signed, g x ∈ T := by
    intro x hx
    simp only [T, mem_filter, mem_univ, true_and]
    have hsum := hf_sq x hx
    have hcast : ((∑ i : Fin 4, (g x i : ℕ) ^ 2 : ℕ) : ℤ) = (m : ℤ) := by
      rw [Nat.cast_sum, ← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hg_val x hx i]
      push_cast
      exact sq_abs (x i)
    exact_mod_cast hcast
  -- Each fiber `{x ∈ S_signed | g x = w}` has card ≤ 16 (bounded by `Fin 4 → Bool`)
  have hfiber : ∀ w ∈ T, (S_signed.filter fun x => g x = w).card ≤ 16 := by
    intro w _
    let decode : (Fin 4 → Bool) → (Fin 4 → ℤ) := fun s i =>
      if s i then ((w i : ℕ) : ℤ) else -((w i : ℕ) : ℤ)
    have hsub : S_signed.filter (fun x => g x = w) ⊆ univ.image decode := by
      intro x hx
      rw [mem_filter] at hx
      rw [mem_image]
      refine ⟨fun i => decide (0 ≤ x i), mem_univ _, ?_⟩
      ext i
      have hwi : (w i : ℕ) = (x i).natAbs := by
        rw [← hx.2]; exact hg_val x hx.1 i
      simp only [decode, hwi]
      by_cases h0 : 0 ≤ x i
      · simp [h0, Int.natAbs_of_nonneg h0]
      · simp [h0, abs_of_neg (show x i < 0 by omega)]
    calc (S_signed.filter fun x => g x = w).card
        ≤ (univ.image decode).card := card_le_card hsub
      _ ≤ (univ : Finset (Fin 4 → Bool)).card := card_image_le
      _ = 16 := by decide
  -- Sum over fibers: `8 * m = S_signed.card ≤ 16 * T.card`, hence `m ≤ 2 * T.card`
  have hbound : S_signed.card ≤ 16 * T.card := by
    calc S_signed.card
        = ∑ w ∈ T, (S_signed.filter fun x => g x = w).card := by
            rw [← Finset.card_biUnion]
            · congr 1; ext x; simp only [mem_biUnion, mem_filter]
              exact ⟨fun hx => ⟨g x, hg_mem x hx, hx, rfl⟩, fun ⟨_, _, hx, _⟩ => hx⟩
            · intro w1 _ w2 _ hne
              change Disjoint _ _
              rw [Finset.disjoint_left]
              intro x hx1 hx2
              rw [mem_filter] at hx1 hx2
              exact hne (hx1.2.symm.trans hx2.2)
      _ ≤ ∑ _w ∈ T, 16 := Finset.sum_le_sum fun w hw => hfiber w hw
      _ = 16 * T.card := by simp [mul_comm]
  change m ≤ 2 * T.card
  omega

end Erdos338H1Proof

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_squares_R1_H2_R1.H1 := by
  rw [OMA.R_Erdos338_erdos_338_variants_squares_R1_H2_R1.H1]
  exact Filter.Eventually.of_forall fun m hm => Erdos338H1Proof.odd_four_squares_card_lower m hm

