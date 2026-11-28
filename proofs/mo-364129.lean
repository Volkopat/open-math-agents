import OMAStatements.S_mo_364129

-- Problem: Simultaneous vanishing Q-linear relations between N-th roots of unity
-- Upstream: statements/mo-364129.lean (declaration OMA.S_mo_364129.main)
-- Credit: @FrancoisCharroin
-- Proof via reindexing by r^-1 and discrete Fourier inversion on ZMod N.

namespace OMA.Mo364129

lemma zeta_pow_mod {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (a : ℕ) :
    ζ ^ (a % N) = ζ ^ a := by
  have hdiv : N * (a / N) + a % N = a := Nat.div_add_mod a N
  calc
    ζ ^ (a % N) = 1 ^ (a / N) * ζ ^ (a % N) := by simp
    _ = (ζ ^ N) ^ (a / N) * ζ ^ (a % N) := by rw [hζ.pow_eq_one]
    _ = ζ ^ (N * (a / N) + a % N) := by rw [pow_add, pow_mul]
    _ = ζ ^ a := by rw [hdiv]

lemma zeta_pow_add {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, zeta_pow_mod hζ, pow_add]

lemma sum_zeta_mul {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (m : ZMod N) :
    ∑ n : ZMod N, ζ ^ (m * n).val = if m = 0 then (N : ℂ) else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [ZMod.card]
  · simp only [hm, ite_false]
    have hm_pos : 0 < m.val := by
      rcases Nat.eq_zero_or_pos m.val with h0 | hpos
      · exfalso
        apply hm
        have hcast : ((m.val : ℕ) : ZMod N) = m := ZMod.natCast_zmod_val m
        rw [h0, Nat.cast_zero] at hcast
        exact hcast.symm
      · exact hpos
    have hm_lt : m.val < N := ZMod.val_lt m
    have hne1 : ζ ^ m.val ≠ 1 := by
      intro h1
      have hdvd : N ∣ m.val := (hζ.pow_eq_one_iff_dvd m.val).mp h1
      have hle : N ≤ m.val := Nat.le_of_dvd hm_pos hdvd
      omega
    have hshift :
        ζ ^ m.val * ∑ n : ZMod N, ζ ^ (m * n).val = ∑ n : ZMod N, ζ ^ (m * n).val := by
      rw [Finset.mul_sum]
      have h1 : ∀ n : ZMod N, ζ ^ m.val * ζ ^ (m * n).val = ζ ^ (m * (n + 1)).val := by
        intro n
        rw [← zeta_pow_add hζ, mul_add, mul_one, add_comm]
      simp_rw [h1]
      exact Equiv.sum_comp (Equiv.addRight (1 : ZMod N)) (fun n => ζ ^ (m * n).val)
    have hmul : (ζ ^ m.val - 1) * ∑ n : ZMod N, ζ ^ (m * n).val = 0 := by
      linear_combination hshift
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne1)

def mulInvEquiv {N : ℕ} (r : (ZMod N)ˣ) : ZMod N ≃ ZMod N where
  toFun j := (r⁻¹ : (ZMod N)ˣ).val * j
  invFun i := (r : ZMod N) * i
  left_inv j := by
    change (r : ZMod N) * ((r⁻¹ : (ZMod N)ˣ).val * j) = j
    rw [← mul_assoc]
    have h : (r : ZMod N) * (r⁻¹ : (ZMod N)ˣ).val = 1 := Units.mul_inv r
    rw [h, one_mul]
  right_inv i := by
    change (r⁻¹ : (ZMod N)ˣ).val * ((r : ZMod N) * i) = i
    rw [← mul_assoc]
    have h : (r⁻¹ : (ZMod N)ˣ).val * (r : ZMod N) = 1 := Units.inv_mul r
    rw [h, one_mul]

lemma sum_rewrite {N : ℕ} [NeZero N] (ζ : ℂ) (v : ZMod N → ℚ) (r : (ZMod N)ˣ) (n : ZMod N) :
    ∑ i : ZMod N, (v i : ℂ) * (ζ ^ ((r : ZMod N) * i * n).val - ζ ^ (i * n).val) =
      ∑ j : ZMod N, ((v ((r⁻¹ : (ZMod N)ˣ).val * j) - v j : ℚ) : ℂ) * ζ ^ (j * n).val := by
  have hsplit :
      ∑ i : ZMod N, (v i : ℂ) * (ζ ^ ((r : ZMod N) * i * n).val - ζ ^ (i * n).val) =
        (∑ i : ZMod N, (v i : ℂ) * ζ ^ ((r : ZMod N) * i * n).val) -
          ∑ i : ZMod N, (v i : ℂ) * ζ ^ (i * n).val := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  rw [hsplit]
  have h1 :
      ∑ i : ZMod N, (v i : ℂ) * ζ ^ ((r : ZMod N) * i * n).val =
        ∑ j : ZMod N, (v ((r⁻¹ : (ZMod N)ˣ).val * j) : ℂ) * ζ ^ (j * n).val := by
    rw [← Equiv.sum_comp (mulInvEquiv r)]
    refine Finset.sum_congr rfl fun j _ => ?_
    change (v ((r⁻¹ : (ZMod N)ˣ).val * j) : ℂ) *
        ζ ^ ((r : ZMod N) * ((r⁻¹ : (ZMod N)ˣ).val * j) * n).val =
      (v ((r⁻¹ : (ZMod N)ˣ).val * j) : ℂ) * ζ ^ (j * n).val
    have hr : (r : ZMod N) * ((r⁻¹ : (ZMod N)ˣ).val * j) = j := by
      rw [← mul_assoc]
      have h : (r : ZMod N) * (r⁻¹ : (ZMod N)ˣ).val = 1 := Units.mul_inv r
      rw [h, one_mul]
    rw [hr]
  rw [h1, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Rat.cast_sub, sub_mul]

lemma fourier_zero {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (w : ZMod N → ℚ) (hw : ∀ n : ZMod N, ∑ j : ZMod N, (w j : ℂ) * ζ ^ (j * n).val = 0) :
    ∀ k : ZMod N, w k = 0 := by
  intro k
  have hsum0 :
      ∑ n : ZMod N, ζ ^ ((-k) * n).val * (∑ j : ZMod N, (w j : ℂ) * ζ ^ (j * n).val) = 0 := by
    simp [hw]
  have hswap :
      ∑ n : ZMod N, ζ ^ ((-k) * n).val * (∑ j : ZMod N, (w j : ℂ) * ζ ^ (j * n).val) =
        ∑ j : ZMod N, (w j : ℂ) * ∑ n : ZMod N, ζ ^ ((j - k) * n).val := by
    calc
      ∑ n : ZMod N, ζ ^ ((-k) * n).val * (∑ j : ZMod N, (w j : ℂ) * ζ ^ (j * n).val)
          = ∑ n : ZMod N, ∑ j : ZMod N, (w j : ℂ) * (ζ ^ ((-k) * n).val * ζ ^ (j * n).val) := by
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j : ZMod N, ∑ n : ZMod N, (w j : ℂ) * ζ ^ ((j - k) * n).val := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n _ => ?_
            rw [← zeta_pow_add hζ]
            have hjk : (-k) * n + j * n = (j - k) * n := by ring
            rw [hjk]
      _ = ∑ j : ZMod N, (w j : ℂ) * ∑ n : ZMod N, ζ ^ ((j - k) * n).val := by
            refine Finset.sum_congr rfl fun j _ => (Finset.mul_sum ..).symm
  rw [hswap] at hsum0
  have heval :
      ∑ j : ZMod N, (w j : ℂ) * ∑ n : ZMod N, ζ ^ ((j - k) * n).val = (w k : ℂ) * (N : ℂ) := by
    have hterm :
        ∀ j : ZMod N,
          (w j : ℂ) * ∑ n : ZMod N, ζ ^ ((j - k) * n).val =
            if j = k then (w k : ℂ) * (N : ℂ) else 0 := by
      intro j
      rw [sum_zeta_mul hζ]
      by_cases hjk : j = k
      · subst hjk; simp
      · have hne : j - k ≠ 0 := sub_ne_zero.mpr hjk
        simp [hjk, hne]
    simp_rw [hterm]
    simp
  rw [heval] at hsum0
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hwkC : (w k : ℂ) = 0 := (mul_eq_zero.mp hsum0).resolve_right hN
  exact Rat.cast_eq_zero.mp hwkC

end OMA.Mo364129

theorem OMA.solution : type_of% @OMA.S_mo_364129.main := by
  intro N _ ζ hζ Γ v _
  constructor
  · intro hsum r hr i
    have hr' : r⁻¹ ∈ Γ := Γ.inv_mem hr
    have hall : ∀ n : ZMod N,
        ∑ j : ZMod N, ((v (((r⁻¹)⁻¹ : (ZMod N)ˣ).val * j) - v j : ℚ) : ℂ) * ζ ^ (j * n).val = 0 := by
      intro n
      by_cases hn : n = 0
      · subst hn
        simp only [mul_zero, ZMod.val_zero, pow_zero, mul_one, Rat.cast_sub]
        rw [Finset.sum_sub_distrib]
        have hcomp :
            ∑ j : ZMod N, (v (((r⁻¹)⁻¹ : (ZMod N)ˣ).val * j) : ℂ) = ∑ j : ZMod N, (v j : ℂ) :=
          Equiv.sum_comp (OMA.Mo364129.mulInvEquiv r⁻¹) (fun x => (v x : ℂ))
        rw [hcomp, sub_self]
      · rw [← OMA.Mo364129.sum_rewrite ζ v r⁻¹ n]
        exact hsum n hn r⁻¹ hr'
    have hzero := OMA.Mo364129.fourier_zero hζ _ hall i
    have hinv : (((r⁻¹)⁻¹ : (ZMod N)ˣ).val : ZMod N) = (r : ZMod N) := by simp
    rw [hinv] at hzero
    exact sub_eq_zero.mp hzero
  · intro hinv n _ r hr
    rw [OMA.Mo364129.sum_rewrite ζ v r n]
    have hr' : r⁻¹ ∈ Γ := Γ.inv_mem hr
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj : v ((r⁻¹ : (ZMod N)ˣ).val * j) = v j := hinv r⁻¹ hr' j
    rw [hj, sub_self, Rat.cast_zero, zero_mul]
