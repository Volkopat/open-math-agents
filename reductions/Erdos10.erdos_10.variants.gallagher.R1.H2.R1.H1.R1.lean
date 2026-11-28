import OMAReductions.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1
import Mathlib

-- Reduction Erdos10.erdos_10.variants.gallagher.R1.H2.R1.H1.R1 of step Erdos10.erdos_10.variants.gallagher.R1.H2.R1.H1
-- Credit: @Aijy0264561

/-! Split Gallagher's averaged prime-pair estimate into an analytic and an
arithmetic part, both over the explicit block family `Q(k, B)`: one binary
exponent from each of the `k` disjoint blocks `[jB, (j+1)B)`, `j < k`. A member
is the multiset `{0·B + f 0, …, (k-1)·B + f (k-1)}` for `f : Fin k → range B`;
its exponents are distinct, so different members have different shift sums,
and an exponential sum over the family factors as a product of `k` block sums.

* The first hypothesis is the analytic input: averaged over all ordered pairs of
  distinct members of `Q(k, B)`, the correlation of the odd-prime weight at the
  shift difference is at most `(1+η)` times the truncated singular series
  model `N * G_R(d)`, up to `η * N * |Q|²`, once `R` and then `k` are large.
* The second hypothesis is Gallagher's arithmetic lemma: for `k` large the mean
  of `G_R` over shift differences of `Q(k, B)` is at most `1 + ε` for all large
  `B`. Here `G_R(d)` is the product over primes `2 < p ≤ R` of `p/(p-1)` when
  `p ∣ d` and `p(p-2)/(p-1)²` otherwise. Writing each local factor as
  `1 + (p-1)⁻² · ∑_{r ≠ 0 mod p} e(r d / p)`, the mean is `1` plus a finite
  combination of `|Q|⁻² |∑_{t ∈ Q} e(θ s_t)|²` with `θ ∉ ℤ` of odd
  denominator; each such sum is a product of `k` block sums of `e(θ 2^i)`,
  periodic in `i` with mean of modulus `< 1` (as `e(θ) ≠ e(2θ)`).

`main` chooses `B = log₂ (N / c) / k` for a constant `c` depending on `k` and
`ε`, checks the size conditions of the target and chains the two bounds. -/

open Finset Filter Real
open scoped Classical

namespace OMA.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1_H1_R1

/-- Analytic input: prime-pair correlations averaged over differences of
`k`-fold block binary sums follow the truncated singular series model. -/
def H1 : Prop :=
  let v := fun j : ℕ => if (2*j+1).Prime then Real.log (2*j+1 : ℕ)/2 else 0
  let s : Multiset ℕ → ℕ := fun t => (t.map (fun i : ℕ => 2^i)).sum
  let G : ℕ → ℕ → ℝ := fun R d =>
    ∏ p ∈ (Finset.range (R+1)).filter (fun p => p.Prime ∧ 2 < p),
      (if p ∣ d then (p:ℝ)/((p:ℝ)-1) else (p:ℝ)*((p:ℝ)-2)/((p:ℝ)-1)^2)
  ∀ η : ℝ, 0 < η → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∀ᶠ N : ℕ in atTop, ∀ B : ℕ, k*2^(k*B) ≤ N → N ≤ 4^(k*B) →
      let Q : Finset (Multiset ℕ) := (Fintype.piFinset (fun _ : Fin k => Finset.range B)).image
        (fun f => Finset.univ.val.map (fun j : Fin k => (j:ℕ)*B + f j))
      (∑ t ∈ Q, ∑ u ∈ Q.erase t, ∑ j ∈ Finset.range N, v j*v (j+Nat.dist (s t) (s u))) ≤
        (1+η)*N*(∑ t ∈ Q, ∑ u ∈ Q.erase t, G R (Nat.dist (s t) (s u))) + η*N*(Q.card:ℝ)^2

/-- Arithmetic input (Gallagher): the truncated singular series has mean at most
`1 + ε` over differences of `k`-fold block binary sums, for some large `k`. -/
def H2 : Prop :=
  let s : Multiset ℕ → ℕ := fun t => (t.map (fun i : ℕ => 2^i)).sum
  let G : ℕ → ℕ → ℝ := fun R d =>
    ∏ p ∈ (Finset.range (R+1)).filter (fun p => p.Prime ∧ 2 < p),
      (if p ∣ d then (p:ℝ)/((p:ℝ)-1) else (p:ℝ)*((p:ℝ)-2)/((p:ℝ)-1)^2)
  ∀ ε : ℝ, 0 < ε → ∀ R k₁ : ℕ, ∃ k : ℕ, k₁ ≤ k ∧ ∀ᶠ B : ℕ in atTop,
    let Q : Finset (Multiset ℕ) := (Fintype.piFinset (fun _ : Fin k => Finset.range B)).image
      (fun f => Finset.univ.val.map (fun j : Fin k => (j:ℕ)*B + f j))
    (∑ t ∈ Q, ∑ u ∈ Q.erase t, G R (Nat.dist (s t) (s u))) ≤ (1+ε)*(Q.card:ℝ)^2

/-- The exponent of block `j`: below `B` the block index is recovered by division. -/
lemma block_div {B j r : ℕ} (hr : r < B) : (j*B + r) / B = j := by
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le r) hr
  rw [add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hr, zero_add]

lemma block_inj {k B : ℕ} {f : Fin k → ℕ} (hf : ∀ j, f j < B) :
    Function.Injective (fun j : Fin k => (j:ℕ)*B + f j) := by
  intro a b h
  have h' : ((a:ℕ)*B + f a) / B = ((b:ℕ)*B + f b) / B := congrArg (· / B) h
  rw [block_div (hf a), block_div (hf b)] at h'
  exact Fin.ext h'

lemma mem_pi {k B : ℕ} {f : Fin k → ℕ}
    (hf : f ∈ Fintype.piFinset (fun _ : Fin k => Finset.range B)) : ∀ j, f j < B := by
  intro j; exact mem_range.1 (Fintype.mem_piFinset.1 hf j)

lemma card_family (k B : ℕ) :
    ((Fintype.piFinset (fun _ : Fin k => Finset.range B)).image
      (fun f => Finset.univ.val.map (fun j : Fin k => (j:ℕ)*B + f j))).card = B^k := by
  rw [card_image_of_injOn, Fintype.card_piFinset]
  · simp
  intro f hf g hg hfg
  have hf' := mem_pi (mem_coe.1 hf)
  have hg' := mem_pi (mem_coe.1 hg)
  funext j
  have hmem : (j:ℕ)*B + f j ∈ Finset.univ.val.map (fun j : Fin k => (j:ℕ)*B + g j) := by
    have : (j:ℕ)*B + f j ∈ Finset.univ.val.map (fun j : Fin k => (j:ℕ)*B + f j) :=
      Multiset.mem_map.2 ⟨j, Finset.mem_univ_val j, rfl⟩
    simpa only [hfg] using this
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hmem
  have hdiv := congrArg (· / B) hi
  simp only [block_div (hf' j), block_div (hg' i)] at hdiv
  have hij : i = j := Fin.ext hdiv
  subst hij
  omega

lemma injOn_family (k B : ℕ) :
    Set.InjOn (fun t : Multiset ℕ => (t.map (fun i : ℕ => 2^i)).sum)
      ↑((Fintype.piFinset (fun _ : Fin k => Finset.range B)).image
        (fun f => Finset.univ.val.map (fun j : Fin k => (j:ℕ)*B + f j))) := by
  intro x hx y hy hxy
  simp only [coe_image, Set.mem_image, mem_coe] at hx hy
  obtain ⟨f, hf, rfl⟩ := hx
  obtain ⟨g, hg, rfl⟩ := hy
  set Sf : Finset ℕ := Finset.univ.map ⟨_, block_inj (mem_pi hf)⟩
  set Sg : Finset ℕ := Finset.univ.map ⟨_, block_inj (mem_pi hg)⟩
  have hSf : Sf.val = Finset.univ.val.map (fun j : Fin k => (j:ℕ)*B + f j) := rfl
  have hSg : Sg.val = Finset.univ.val.map (fun j : Fin k => (j:ℕ)*B + g j) := rfl
  have h : ∑ i ∈ Sf, 2^i = ∑ i ∈ Sg, 2^i := by
    change (Sf.val.map (fun i : ℕ => 2^i)).sum = (Sg.val.map (fun i : ℕ => 2^i)).sum
    rw [hSf, hSg]; exact hxy
  have := Finset.geomSum_injective (le_refl 2) h
  rw [← hSf, ← hSg, this]

lemma mem_family {k B : ℕ} {t : Multiset ℕ}
    (ht : t ∈ (Fintype.piFinset (fun _ : Fin k => Finset.range B)).image
      (fun f => Finset.univ.val.map (fun j : Fin k => (j:ℕ)*B + f j))) :
    Multiset.card t = k ∧ (t.map (fun i : ℕ => 2^i)).sum ≤ k * 2^(k*B) := by
  obtain ⟨f, hf, rfl⟩ := mem_image.1 ht
  have hf' := mem_pi hf
  refine ⟨by simp, ?_⟩
  rw [Multiset.map_map]
  have h : (Finset.univ.val.map ((fun i : ℕ => 2^i) ∘ (fun j : Fin k => (j:ℕ)*B + f j))).sum =
      ∑ j : Fin k, 2^((j:ℕ)*B + f j) := rfl
  rw [h]
  have hle : ∀ j ∈ (Finset.univ : Finset (Fin k)), 2^((j:ℕ)*B + f j) ≤ 2^(k*B) := by
    intro j _
    apply Nat.pow_le_pow_right (by norm_num)
    have h1 := hf' j
    have h2 : (j:ℕ) + 1 ≤ k := j.isLt
    nlinarith
  have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin k)) _ _ hle
  simpa using this

lemma log_le_of_le_four_pow {N M : ℕ} (h : N ≤ 4^M) :
    Real.log (2*(N:ℝ)+1) ≤ 2*((M:ℝ)+1) := by
  have hN : (N:ℝ) ≤ 4^M := by exact_mod_cast h
  have h1 : (1:ℝ) ≤ 4^M := one_le_pow₀ (by norm_num)
  have h2 : 2*(N:ℝ)+1 ≤ 4^(M+1) := by rw [pow_succ]; linarith
  have h4 : Real.log 4 ≤ 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith [Real.log_two_lt_d9]
  calc Real.log (2*(N:ℝ)+1) ≤ Real.log (4^(M+1)) := Real.log_le_log (by positivity) h2
    _ = ((M:ℝ)+1) * Real.log 4 := by rw [Real.log_pow]; push_cast; ring
    _ ≤ ((M:ℝ)+1) * 2 := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 2*((M:ℝ)+1) := by ring

lemma pow_large {k : ℕ} (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, 4*(((k*B:ℕ):ℝ)+1)^2 ≤ ε * ((B^k:ℕ):ℝ) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_ge_atTop (⌈4 * ((k:ℝ)+1)^2 / ε⌉₊)] with B hB1 hB2
  have hB : (1:ℝ) ≤ B := by exact_mod_cast hB1
  have hBε : 4 * ((k:ℝ)+1)^2 ≤ ε * B := by
    have h1 : 4 * ((k:ℝ)+1)^2 / ε ≤ ⌈4 * ((k:ℝ)+1)^2 / ε⌉₊ := Nat.le_ceil _
    have h2 : ((⌈4 * ((k:ℝ)+1)^2 / ε⌉₊ : ℕ) : ℝ) ≤ (B:ℝ) := Nat.cast_le.mpr hB2
    rw [div_le_iff₀ hε] at h1
    nlinarith
  push_cast
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hsq : ((k:ℝ)*B+1)^2 ≤ ((k:ℝ)+1)^2 * (B:ℝ)^2 := by
    have hl : (k:ℝ)*B+1 ≤ ((k:ℝ)+1)*B := by nlinarith
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hl 2
  have hcube : (B:ℝ)^3 ≤ (B:ℝ)^k := pow_le_pow_right₀ hB hk
  have e1 : 4*((k:ℝ)*B+1)^2 ≤ 4*((k:ℝ)+1)^2 * (B:ℝ)^2 := by nlinarith
  have e2 : 4*((k:ℝ)+1)^2 * (B:ℝ)^2 ≤ ε * B * (B:ℝ)^2 :=
    mul_le_mul_of_nonneg_right hBε (by positivity)
  have e3 : ε * B * (B:ℝ)^2 = ε * (B:ℝ)^3 := by ring
  have e4 : ε * (B:ℝ)^3 ≤ ε * (B:ℝ)^k := mul_le_mul_of_nonneg_left hcube hε.le
  linarith

lemma combine {off Gs Qc N η ε : ℝ} (h1 : off ≤ (1+η)*N*Gs + η*N*Qc^2)
    (h2 : Gs ≤ (1+η)*Qc^2) (hN : 0 ≤ N) (hη : 0 < η) (hη1 : η ≤ 1) (hη4 : η ≤ ε/4) :
    off ≤ (1+ε)*N*Qc^2 := by
  have hQ : 0 ≤ Qc^2 := sq_nonneg Qc
  have e1 : (1+η)*N*Gs ≤ (1+η)*N*((1+η)*Qc^2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e2 : ((1+η)*(1+η) + η) * (N * Qc^2) ≤ (1+ε) * (N * Qc^2) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (mul_nonneg hN hQ)
  have e3 : (1+η)*N*((1+η)*Qc^2) + η*N*Qc^2 = ((1+η)*(1+η) + η) * (N * Qc^2) := by ring
  have e4 : (1+ε) * (N * Qc^2) = (1+ε)*N*Qc^2 := by ring
  linarith

theorem main : H1 → H2 → OMA.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1.H1 := by
  intro hA hB
  unfold OMA.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1.H1
  unfold H1 at hA
  unfold H2 at hB
  dsimp only at hA hB ⊢
  intro ε hε
  set η : ℝ := min 1 (ε/4) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη4 : η ≤ ε/4 := min_le_right _ _
  obtain ⟨R₀, hR⟩ := hA η hη
  obtain ⟨k₀, hk₀⟩ := hR R₀ le_rfl
  obtain ⟨k, hkk, hBk⟩ := hB η hη R₀ (max k₀ 3)
  have hAk := hk₀ k (le_trans (le_max_left _ _) hkk)
  have hk3 : 3 ≤ k := le_trans (le_max_right _ _) hkk
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.1 hBk
  obtain ⟨B₁, hB₁⟩ := eventually_atTop.1 (pow_large hk3 hε)
  set c : ℕ := k * (⌈1/ε⌉₊ + 1) with hcdef
  have hc : 0 < c := Nat.mul_pos (by omega) (Nat.succ_pos _)
  have hkc : k ≤ c := Nat.le_mul_of_pos_right k (Nat.succ_pos _)
  have hεc : (k:ℝ) ≤ ε * c := by
    have h1 : 1/ε ≤ (⌈1/ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : 1 ≤ ε * ((⌈1/ε⌉₊ : ℝ) + 1) := by
      rw [div_le_iff₀ hε] at h1; nlinarith
    have h3 : (c:ℝ) = k * ((⌈1/ε⌉₊ : ℝ) + 1) := by rw [hcdef]; push_cast; ring
    rw [h3]
    have hk0 : (0:ℝ) ≤ k := by positivity
    nlinarith
  set L : ℕ := max (max B₀ B₁) (c + k) with hLdef
  refine ⟨k, ?_⟩
  filter_upwards [hAk, eventually_ge_atTop (c * 2^(k*L))] with N hN hNL
  set ℓ : ℕ := Nat.log 2 (N / c) with hℓdef
  set B : ℕ := ℓ / k with hBdef
  have hk0 : 0 < k := by omega
  have hLle : 2^(k*L) ≤ N / c := (Nat.le_div_iff_mul_le hc).2 (by rw [mul_comm]; exact hNL)
  have hkLℓ : k*L ≤ ℓ := Nat.le_log_of_pow_le one_lt_two hLle
  have hLB : L ≤ B := (Nat.le_div_iff_mul_le hk0).2 (by rw [mul_comm]; exact hkLℓ)
  have hNc0 : N / c ≠ 0 := by have := Nat.one_le_two_pow (n := k*L); omega
  have h2ℓ : 2^ℓ ≤ N / c := Nat.pow_log_le_self 2 hNc0
  have hkBℓ : k*B ≤ ℓ := Nat.mul_div_le ℓ k
  have hℓkB : ℓ + 1 ≤ k*B + k := by
    have := Nat.div_add_mod ℓ k
    have := Nat.mod_lt ℓ hk0
    rw [hBdef]; omega
  have h2kB : 2^(k*B) ≤ N / c := le_trans (Nat.pow_le_pow_right (by norm_num) hkBℓ) h2ℓ
  have hcM : c * 2^(k*B) ≤ N := by
    have := (Nat.le_div_iff_mul_le hc).1 h2kB; rw [mul_comm]; exact this
  have hkM : k * 2^(k*B) ≤ N := le_trans (Nat.mul_le_mul_right _ hkc) hcM
  have hN4 : N ≤ 4^(k*B) := by
    have h1 : N < c * (N / c + 1) := by
      have := Nat.div_add_mod N c
      have := Nat.mod_lt N hc
      nlinarith
    have h2 : N / c + 1 ≤ 2^(ℓ+1) := Nat.lt_pow_succ_log_self one_lt_two _
    have h2' : 2^(ℓ+1) ≤ 2^(k*B+k) := Nat.pow_le_pow_right (by norm_num) hℓkB
    have h3 : c * 2^k ≤ 2^(k*B) := by
      have a1 : c < 2^c := Nat.lt_two_pow_self
      have a2 : c + k ≤ L := le_max_right _ _
      have a3 : L ≤ k*B := le_trans hLB (Nat.le_mul_of_pos_left B hk0)
      calc c * 2^k ≤ 2^c * 2^k := Nat.mul_le_mul_right _ a1.le
        _ = 2^(c+k) := (pow_add 2 c k).symm
        _ ≤ 2^(k*B) := Nat.pow_le_pow_right (by norm_num) (le_trans a2 a3)
    have h4 : (4:ℕ)^(k*B) = 2^(k*B) * 2^(k*B) := by rw [show (4:ℕ) = 2*2 by rfl, mul_pow]
    rw [h4]
    calc N ≤ c * (N / c + 1) := h1.le
      _ ≤ c * 2^(k*B+k) := Nat.mul_le_mul_left _ (le_trans h2 h2')
      _ = (c * 2^k) * 2^(k*B) := by rw [pow_add]; ring
      _ ≤ 2^(k*B) * 2^(k*B) := Nat.mul_le_mul_right _ h3
  have hB0 : B₀ ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLB
  have hB1 : B₁ ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLB
  have hBpos : 0 < B := lt_of_lt_of_le (by omega : 0 < L) hLB
  have hoff := hN B hkM hN4
  have hG := hB₀ B hB0
  have hpw := hB₁ B hB1
  refine ⟨(Fintype.piFinset (fun _ : Fin k => Finset.range B)).image
      (fun f => Finset.univ.val.map (fun j : Fin k => (j:ℕ)*B + f j)),
    ?_, ?_, injOn_family k B, ?_, ?_⟩
  · rw [← Finset.card_pos, card_family]; exact pow_pos hBpos k
  · intro t ht
    obtain ⟨hcard, hs⟩ := mem_family ht
    refine ⟨hcard.le, ?_⟩
    have hs' : (((t.map (fun i : ℕ => 2^i)).sum : ℕ) : ℝ) ≤ (k:ℝ) * 2^(k*B) := by
      have := Nat.cast_le (α := ℝ) |>.mpr hs
      push_cast at this ⊢
      exact this
    have hcM' : (c:ℝ) * 2^(k*B) ≤ N := by exact_mod_cast hcM
    have hp : (0:ℝ) ≤ 2^(k*B) := by positivity
    calc (((t.map (fun i : ℕ => 2^i)).sum : ℕ) : ℝ) ≤ (k:ℝ) * 2^(k*B) := hs'
      _ ≤ ε * c * 2^(k*B) := mul_le_mul_of_nonneg_right hεc hp
      _ = ε * (c * 2^(k*B)) := by ring
      _ ≤ ε * N := mul_le_mul_of_nonneg_left hcM' hε.le
  · rw [card_family]
    have hl0 : 0 ≤ Real.log (2*(N:ℝ)+1) :=
      Real.log_nonneg (by linarith [show (0:ℝ) ≤ N from Nat.cast_nonneg N])
    have hl := log_le_of_le_four_pow hN4
    calc Real.log (2*(N:ℝ)+1)^2 ≤ (2*(((k*B:ℕ):ℝ)+1))^2 := pow_le_pow_left₀ hl0 hl 2
      _ = 4*(((k*B:ℕ):ℝ)+1)^2 := by ring
      _ ≤ ε * ((B^k:ℕ):ℝ) := hpw
  · exact combine hoff hG (Nat.cast_nonneg N) hη hη1 hη4

end OMA.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1_H1_R1
