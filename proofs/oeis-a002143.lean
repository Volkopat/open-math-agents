import OMAStatements.S_oeis_a002143
import Mathlib

/-!
# Proof of OEIS A002143 (Zhi-Wei Sun cosecant class-number formula)

For every prime `p > 3` with `p ≡ 3 (mod 8)`,
`2 * h(-p) * √p = ∑ k ∈ Icc 1 ((p - 1) / 2), 1 / sin (2 * π * k ^ 2 / p)`.

Proof outline (completely self-contained):
1. Trigonometric identity: pairing `k` with `(p - k)` and substituting `r ≡ k^2 (mod p)` converts
   the cosecant sum into `∑ r ∈ Icc 1 (p - 1), legendreSym p r * cot (π * r / p)`.
2. Gauss sum and Dirichlet L-value: evaluating the discrete sine Gauss sum `G = ∑ (r/p) sin(2πr/p)`
   gives `G^2 = p` (avoiding the sign determination of the Gauss sum),
   `∑ (r/p) cot(πr/p) = -(2G/p) ∑ a (a/p)`, and via Abel radial limits of `∑ (n/p) t^n / n`,
   `G * L(1, χ_p) = -(π/p) ∑ a (a/p)`. Combining eliminates `G` to yield
   `∑ k, csc(2π k^2 / p) = (2p / π) * L(1, χ_p)`.
3. Binary quadratic forms: SL_2(ℤ) reduction, uniqueness of reduced forms, trivial automorphism
   group `{±I}` for prime `p > 3`, primitive-representation bijection, CRT, and Hensel lifting
   establish `R(n) = 2 * ∑_{d | n} legendreSym p d` for all `n ≥ 1`.
4. Dirichlet class number formula: comparing the hyperbola asymptotic
   `X⁻¹ ∑_{n ≤ X} R(n) → 2 * L(1, χ_p)` with the 1D Riemann-sum ellipse lattice-point count
   `X⁻¹ ∑_{n ≤ X} R(n) → h(-p) * (2π / √p)` yields `L(1, χ_p) = π * h(-p) / √p`,
   completing the proof.

Credit: @PrimordialAA
-/

namespace OMA.A002143Proof

open Real Complex Filter Finset
open scoped Topology

/-! ### Part 1: Legendre symbol helpers and trigonometric identity -/

lemma legendreSym_congr (p : ℕ) [Fact p.Prime] {a b : ℤ} (h : (a : ZMod p) = (b : ZMod p)) :
    legendreSym p a = legendreSym p b := by
  simp only [legendreSym, h]

lemma abs_legendreSym_le_one (p : ℕ) [Fact p.Prime] (a : ℤ) :
    |(legendreSym p a : ℝ)| ≤ 1 := by
  by_cases h : (a : ZMod p) = 0
  · rw [(legendreSym.eq_zero_iff p a).mpr h]; simp
  · rcases legendreSym.eq_one_or_neg_one p h with h1 | h1 <;> rw [h1] <;> norm_num

lemma legendre_neg_one_of_mod8 (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3) :
    legendreSym p (-1) = -1 := by
  have hp2 : p ≠ 2 := by omega
  have h4 : p % 4 = 3 := by omega
  have hodd : p % 2 = 1 := by omega
  rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_eq_if_mod_four]
  simp [h4, hodd]

lemma legendre_two_of_mod8 (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3) :
    legendreSym p 2 = -1 := by
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := by omega
  rw [legendreSym.at_two hp2, ZMod.χ₈_nat_eq_if_mod_eight]
  simp [h8, hodd]

lemma legendre_sub_self (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3) {r : ℕ} (hr : r ≤ p) :
    legendreSym p ((p - r : ℕ) : ℤ) = -legendreSym p (r : ℤ) := by
  have h1 : (((p - r : ℕ) : ℤ) : ZMod p) = -((r : ℤ) : ZMod p) := by
    rw [Int.cast_natCast, Nat.cast_sub hr, ZMod.natCast_self, zero_sub, Int.cast_natCast]
  have h2 : legendreSym p ((p - r : ℕ) : ℤ) = legendreSym p (-(r : ℤ)) :=
    legendreSym_congr p (by simpa using h1)
  rw [h2, show -(r : ℤ) = (-1) * (r : ℤ) by ring, legendreSym.mul, legendre_neg_one_of_mod8 p h8]
  ring

lemma sum_legendre_Icc_eq_zero (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3) :
    ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) = 0 := by
  have hrev : ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) =
      ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p ((p - r : ℕ) : ℤ) : ℝ) := by
    refine Finset.sum_bij (fun r _ => p - r) ?_ ?_ ?_ ?_
    · intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega
    · intro r₁ hr₁ r₂ hr₂ h; simp only [Finset.mem_Icc] at hr₁ hr₂; omega
    · intro r hr; simp only [Finset.mem_Icc] at hr
      exact ⟨p - r, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro r hr; simp only [Finset.mem_Icc] at hr
      rw [Nat.sub_sub_self (by omega)]
  have hneg : ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p ((p - r : ℕ) : ℤ) : ℝ) =
      -∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    simp only [Finset.mem_Icc] at hr
    rw [legendre_sub_self p h8 (by omega)]
    push_cast
    ring
  linarith

lemma cot_add_int_mul_pi (x : ℝ) (k : ℤ) : Real.cot (x + k * π) = Real.cot x := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
    Real.cos_add_int_mul_pi, Real.sin_add_int_mul_pi]
  have hne : ((-1 : ℝ) ^ k) ≠ 0 := by positivity
  field_simp [hne]

lemma sin_two_pi_mul_div_ne_zero {p r : ℕ} (hp : p.Prime) (h2 : p ≠ 2)
    (hr1 : 1 ≤ r) (hr2 : r ≤ p - 1) :
    Real.sin (2 * π * (r : ℝ) / p) ≠ 0 := by
  intro h
  rw [Real.sin_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h1 : (2 * r : ℝ) = (k : ℝ) * (p : ℝ) := by
    have hmul : (k : ℝ) * π * (p : ℝ) = 2 * π * (r : ℝ) := by
      have := congrArg (· * (p : ℝ)) hk
      simpa [div_mul_cancel₀ _ hp0] using this
    nlinarith [Real.pi_pos]
  have h2z : (2 * r : ℤ) = k * (p : ℤ) := by exact_mod_cast h1
  have hp_dvd : p ∣ 2 * r := Int.natCast_dvd_natCast.mp ⟨k, by push_cast; linarith⟩
  rcases hp.dvd_mul.mp hp_dvd with hp2 | hpr
  · exact h2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hp2) hp.two_le)
  · have := Nat.le_of_dvd (by omega) hpr; omega

lemma inv_sin_two_mul_eq_cot_sub_cot {θ : ℝ} (hs : Real.sin (2 * θ) ≠ 0) :
    1 / Real.sin (2 * θ) = Real.cot θ - Real.cot (2 * θ) := by
  have hs1 : Real.sin θ ≠ 0 := fun h => hs (by rw [Real.sin_two_mul, h]; ring)
  have hc : Real.cos θ ≠ 0 := fun h => hs (by rw [Real.sin_two_mul, h]; ring)
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.sin_two_mul, Real.cos_two_mul]
  field_simp [hs1, hc]
  ring

lemma csc_sq_sum_eq_legendre_csc_sum (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3) :
    2 * ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), 1 / Real.sin (2 * π * (k : ℝ) ^ 2 / p) =
      ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) / Real.sin (2 * π * (r : ℝ) / p) := by
  have hp : p.Prime := Fact.out
  have hp_pos : 0 < p := hp.pos
  set QR : Finset ℕ := (Finset.Icc 1 (p - 1)).filter fun r => legendreSym p r = 1
  set QNR : Finset ℕ := (Finset.Icc 1 (p - 1)).filter fun r => legendreSym p r = -1
  have hsq : ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), 1 / Real.sin (2 * π * (k : ℝ) ^ 2 / p) =
      ∑ r ∈ QR, 1 / Real.sin (2 * π * (r : ℝ) / p) := by
    refine Finset.sum_bij (fun k _ => k ^ 2 % p) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      have hk_ndvd : ¬ p ∣ k := fun h => by have := Nat.le_of_dvd (by omega) h; omega
      have hsq_ndvd : ¬ p ∣ k ^ 2 := fun h => hk_ndvd (hp.dvd_of_dvd_pow h)
      have hmod_pos : 0 < k ^ 2 % p := Nat.pos_of_ne_zero (fun h => hsq_ndvd (Nat.dvd_of_mod_eq_zero h))
      have hmod_lt : k ^ 2 % p ≤ p - 1 := by have := Nat.mod_lt (k ^ 2) hp_pos; omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmod_pos, hmod_lt⟩, ?_⟩
      have hmod_eq : (((k ^ 2 % p : ℕ) : ℤ) : ZMod p) = (k : ZMod p) * (k : ZMod p) := by
        rw [Int.cast_natCast, ZMod.natCast_mod, Nat.cast_pow, sq]
      have hne0 : (((k ^ 2 % p : ℕ) : ℤ) : ZMod p) ≠ 0 := by
        intro h
        have hd : p ∣ k ^ 2 % p := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using h)
        have := Nat.le_of_dvd hmod_pos hd; omega
      rw [legendreSym.eq_one_iff p hne0]
      exact ⟨(k : ZMod p), hmod_eq⟩
    · intro k₁ hk₁ k₂ hk₂ heq
      simp only [Finset.mem_Icc] at hk₁ hk₂
      have hzm : (k₁ : ZMod p) ^ 2 = (k₂ : ZMod p) ^ 2 := by
        have h1 : ((k₁ ^ 2 % p : ℕ) : ZMod p) = ((k₂ ^ 2 % p : ℕ) : ZMod p) := congrArg Nat.cast heq
        simpa [ZMod.natCast_mod] using h1
      have hfac : ((k₁ : ZMod p) - (k₂ : ZMod p)) * ((k₁ : ZMod p) + (k₂ : ZMod p)) = 0 := by
        linear_combination hzm
      rcases mul_eq_zero.mp hfac with hsub | hadd
      · have heqz : (k₁ : ZMod p) = (k₂ : ZMod p) := sub_eq_zero.mp hsub
        have h1 : k₁ % p = k₂ % p := by
          simpa [ZMod.val_natCast] using congrArg ZMod.val heqz
        rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
      · have h0 : ((k₁ + k₂ : ℕ) : ZMod p) = 0 := by simpa using hadd
        have hdvd : p ∣ k₁ + k₂ := (ZMod.natCast_eq_zero_iff _ _).mp h0
        have := Nat.le_of_dvd (by omega) hdvd; omega
    · intro r hr
      simp only [QR, Finset.mem_filter, Finset.mem_Icc] at hr
      have hr0 : ((r : ℤ) : ZMod p) ≠ 0 := by
        intro h
        have hdvd : p ∣ r := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using h)
        have := Nat.le_of_dvd (by omega) hdvd; omega
      obtain ⟨u, hu⟩ := (legendreSym.eq_one_iff p hr0).mp hr.2
      have hu0 : u ≠ 0 := fun h => hr0 (by rw [hu, h, mul_zero])
      have huv_pos : 0 < u.val := Nat.pos_of_ne_zero (fun h => hu0 ((ZMod.val_eq_zero u).mp h))
      have huv_lt : u.val < p := u.val_lt
      by_cases hle : u.val ≤ (p - 1) / 2
      · refine ⟨u.val, Finset.mem_Icc.mpr ⟨huv_pos, hle⟩, ?_⟩
        have h1 : ((u.val ^ 2 : ℕ) : ZMod p) = (r : ZMod p) := by
          rw [Nat.cast_pow, ZMod.natCast_zmod_val, sq]; simpa using hu.symm
        have h2 : ((u.val ^ 2 : ℕ) : ZMod p).val = (r : ZMod p).val := congrArg ZMod.val h1
        rw [ZMod.val_natCast, ZMod.val_natCast] at h2
        exact h2.trans (Nat.mod_eq_of_lt (by omega))
      · refine ⟨p - u.val, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        have h1 : (((p - u.val) ^ 2 : ℕ) : ZMod p) = (r : ZMod p) := by
          rw [Nat.cast_pow, Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub, neg_sq,
            ZMod.natCast_zmod_val, sq]
          simpa using hu.symm
        have h2 : (((p - u.val) ^ 2 : ℕ) : ZMod p).val = (r : ZMod p).val := congrArg ZMod.val h1
        rw [ZMod.val_natCast, ZMod.val_natCast] at h2
        exact h2.trans (Nat.mod_eq_of_lt (by omega))
    · intro k _
      congr 1
      set q := k ^ 2 / p
      have hdiv : (k : ℝ) ^ 2 = ((k ^ 2 % p : ℕ) : ℝ) + (q : ℝ) * (p : ℝ) := by
        have hnat : k ^ 2 = k ^ 2 % p + p * q := (Nat.mod_add_div (k ^ 2) p).symm
        have h' : ((k ^ 2 : ℕ) : ℝ) = ((k ^ 2 % p + p * q : ℕ) : ℝ) := congrArg Nat.cast hnat
        push_cast at h'
        linarith
      have harg : 2 * π * (k : ℝ) ^ 2 / p =
          2 * π * ((k ^ 2 % p : ℕ) : ℝ) / p + (q : ℤ) * (2 * π) := by
        have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
        rw [hdiv, Int.cast_natCast]
        field_simp [hp0]
      rw [harg, Real.sin_add_int_mul_two_pi]
  have hpart : Finset.Icc 1 (p - 1) = QR ∪ QNR := by
    ext r
    simp only [QR, QNR, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro hr
      have hr0 : ((r : ℤ) : ZMod p) ≠ 0 := by
        intro h
        have hdvd : p ∣ r := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using h)
        have := Nat.le_of_dvd (by omega) hdvd; omega
      rcases legendreSym.eq_one_or_neg_one p hr0 with h1 | h1
      · exact Or.inl ⟨hr, h1⟩
      · exact Or.inr ⟨hr, h1⟩
    · rintro (⟨hr, _⟩ | ⟨hr, _⟩) <;> exact hr
  have hdisj : Disjoint QR QNR := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    simp only [QR, QNR, Finset.mem_filter] at h1 h2; omega
  have hqnr : ∑ r ∈ QNR, (legendreSym p r : ℝ) / Real.sin (2 * π * (r : ℝ) / p) =
      ∑ r ∈ QR, 1 / Real.sin (2 * π * (r : ℝ) / p) := by
    refine Finset.sum_bij (fun r _ => p - r) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [QR, QNR, Finset.mem_filter, Finset.mem_Icc] at hr ⊢
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [legendre_sub_self p h8 (by omega), hr.2]; norm_num
    · intro r₁ hr₁ r₂ hr₂ h
      simp only [QNR, Finset.mem_filter, Finset.mem_Icc] at hr₁ hr₂; omega
    · intro r hr
      simp only [QR, QNR, Finset.mem_filter, Finset.mem_Icc] at hr ⊢
      refine ⟨p - r, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      rw [legendre_sub_self p h8 (by omega), hr.2]
    · intro r hr
      simp only [QNR, Finset.mem_filter, Finset.mem_Icc] at hr
      rw [hr.2]
      have harg : 2 * π * (r : ℝ) / p = 2 * π - 2 * π * ((p - r : ℕ) : ℝ) / p := by
        have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
        rw [Nat.cast_sub (by omega)]
        field_simp [hp0]
        ring
      rw [harg, Real.sin_two_pi_sub]
      push_cast; ring
  have hqr : ∑ r ∈ QR, (legendreSym p r : ℝ) / Real.sin (2 * π * (r : ℝ) / p) =
      ∑ r ∈ QR, 1 / Real.sin (2 * π * (r : ℝ) / p) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    simp only [QR, Finset.mem_filter] at hr
    rw [hr.2]; norm_num
  rw [hsq, hpart, Finset.sum_union hdisj, hqr, hqnr]
  ring

theorem trig_csc_eq_cot (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3) :
    ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), 1 / Real.sin (2 * π * (k : ℝ) ^ 2 / p) =
      ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) * Real.cot (π * (r : ℝ) / p) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp_pos : 0 < p := hp.pos
  have h1 := csc_sq_sum_eq_legendre_csc_sum p h8
  have hsplit : ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) / Real.sin (2 * π * (r : ℝ) / p) =
      ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) * Real.cot (π * (r : ℝ) / p) -
      ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) * Real.cot (2 * π * (r : ℝ) / p) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    simp only [Finset.mem_Icc] at hr
    have hne := sin_two_pi_mul_div_ne_zero hp hp2 hr.1 hr.2
    have hθ : 2 * (π * (r : ℝ) / p) = 2 * π * (r : ℝ) / p := by ring
    have hcot := inv_sin_two_mul_eq_cot_sub_cot (θ := π * (r : ℝ) / p) (by rwa [hθ])
    rw [hθ] at hcot
    rw [div_eq_mul_one_div, hcot]; ring
  have hdouble : ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) * Real.cot (2 * π * (r : ℝ) / p) =
      -∑ u ∈ Finset.Icc 1 (p - 1), (legendreSym p u : ℝ) * Real.cot (π * (u : ℝ) / p) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun r _ => (2 * r) % p) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [Finset.mem_Icc] at hr ⊢
      have hndvd : ¬ p ∣ 2 * r := fun h => by
        rcases hp.dvd_mul.mp h with h2 | hrp
        · exact hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h2) hp.two_le)
        · have := Nat.le_of_dvd (by omega) hrp; omega
      have hpos : 0 < (2 * r) % p := Nat.pos_of_ne_zero (fun h => hndvd (Nat.dvd_of_mod_eq_zero h))
      have hlt := Nat.mod_lt (2 * r) hp_pos; omega
    · intro r₁ hr₁ r₂ hr₂ heq
      simp only [Finset.mem_Icc] at hr₁ hr₂
      have hz : (2 : ZMod p) * (r₁ : ZMod p) = (2 : ZMod p) * (r₂ : ZMod p) := by
        have h' : (((2 * r₁) % p : ℕ) : ZMod p) = (((2 * r₂) % p : ℕ) : ZMod p) := congrArg Nat.cast heq
        simpa [ZMod.natCast_mod] using h'
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h
        have hd := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
        exact hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hd) hp.two_le)
      have hr_eq : (r₁ : ZMod p) = (r₂ : ZMod p) := mul_left_cancel₀ h2ne hz
      have hmod : r₁ % p = r₂ % p := by rw [← ZMod.val_natCast, ← ZMod.val_natCast, hr_eq]
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
    · intro u hu
      simp only [Finset.mem_Icc] at hu
      by_cases heven : u % 2 = 0
      · refine ⟨u / 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        rw [show 2 * (u / 2) = u by omega, Nat.mod_eq_of_lt (by omega)]
      · refine ⟨(u + p) / 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        rw [show 2 * ((u + p) / 2) = u + p by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      have hleg : legendreSym p ((2 * r % p : ℕ) : ℤ) = -legendreSym p (r : ℤ) := by
        have h1 : legendreSym p ((2 * r % p : ℕ) : ℤ) = legendreSym p (2 * (r : ℤ)) :=
          legendreSym_congr p (by simp)
        rw [h1, legendreSym.mul, legendre_two_of_mod8 p h8]; ring
      have hcot : Real.cot (2 * π * (r : ℝ) / p) = Real.cot (π * ((2 * r % p : ℕ) : ℝ) / p) := by
        have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
        set q := 2 * r / p
        have hdiv : (2 * r : ℝ) = ((2 * r % p : ℕ) : ℝ) + (q : ℝ) * (p : ℝ) := by
          have hnat : 2 * r = 2 * r % p + p * q := (Nat.mod_add_div (2 * r) p).symm
          have h' : ((2 * r : ℕ) : ℝ) = ((2 * r % p + p * q : ℕ) : ℝ) := congrArg Nat.cast hnat
          push_cast at h'; linarith
        have harg : 2 * π * (r : ℝ) / p =
            π * ((2 * r % p : ℕ) : ℝ) / p + (q : ℤ) * π := by
          rw [Int.cast_natCast]; field_simp [hp0]; linarith
        rw [harg, cot_add_int_mul_pi]
      rw [hleg, hcot]; push_cast; ring
  linarith

/-! ### Part 2: Finite Fourier identity, Gauss sum square, and Abel limit for L(1, χ) -/

/-- The real sine Gauss sum `G_p = ∑_{r=1}^{p-1} (r/p) sin(2πr/p)`. -/
noncomputable def sineGauss (p : ℕ) [Fact p.Prime] : ℝ :=
  ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) * Real.sin (2 * π * (r : ℝ) / p)

/-- Complex exponential `e(x) = exp(2π i x)`. -/
noncomputable def eC (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

lemma eC_add (x y : ℝ) : eC (x + y) = eC x * eC y := by
  simp only [eC, Complex.ofReal_add, mul_add, Complex.exp_add]

lemma eC_nat_mul (n : ℕ) (x : ℝ) : eC (n * x) = eC x ^ n := by
  simp only [eC, Complex.ofReal_mul, Complex.ofReal_natCast, ← Complex.exp_nat_mul]
  congr 1; ring

lemma eC_int (k : ℤ) : eC k = 1 := by
  simp only [eC, Complex.ofReal_intCast]
  rw [show (2 : ℂ) * π * Complex.I * k = k * (2 * π * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

lemma eC_eq_cos_add_sin_mul_I (x : ℝ) :
    eC x = (Real.cos (2 * π * x) : ℂ) + (Real.sin (2 * π * x) : ℂ) * Complex.I := by
  simp only [eC]
  rw [show (2 : ℂ) * π * Complex.I * x = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma eC_im (x : ℝ) : (eC x).im = Real.sin (2 * π * x) := by
  rw [eC_eq_cos_add_sin_mul_I]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]

lemma eC_re (x : ℝ) : (eC x).re = Real.cos (2 * π * x) := by
  rw [eC_eq_cos_add_sin_mul_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

lemma norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  simp only [eC]
  rw [show (2 : ℂ) * π * Complex.I * x = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I (2 * π * x)

lemma sum_eC_div_p (p : ℕ) (hp : 0 < p) (m : ℤ) :
    ∑ r ∈ Finset.range p, eC ((m * r : ℤ) / (p : ℝ)) = if (p : ℤ) ∣ m then (p : ℂ) else 0 := by
  split_ifs with hdvd
  · obtain ⟨k, rfl⟩ := hdvd
    have h1 : ∀ r ∈ Finset.range p, eC (((p : ℤ) * k * r : ℤ) / (p : ℝ)) = 1 := by
      intro r _
      have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
      have harg : (((p : ℤ) * k * r : ℤ) : ℝ) / (p : ℝ) = ((k * r : ℤ) : ℝ) := by
        push_cast; field_simp [hp0]
      rw [harg, eC_int]
    rw [Finset.sum_congr rfl h1]; simp
  · set ζ : ℂ := eC ((m : ℝ) / (p : ℝ))
    have hterm : ∀ r ∈ Finset.range p, eC ((m * r : ℤ) / (p : ℝ)) = ζ ^ r := by
      intro r _
      have harg : ((m * r : ℤ) : ℝ) / (p : ℝ) = (r : ℕ) * ((m : ℝ) / (p : ℝ)) := by
        push_cast; ring
      rw [harg, eC_nat_mul]
    rw [Finset.sum_congr rfl hterm]
    have hζp : ζ ^ p = 1 := by
      rw [← eC_nat_mul]
      have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
      have : (p : ℝ) * ((m : ℝ) / (p : ℝ)) = (m : ℝ) := by field_simp [hp0]
      rw [this, eC_int]
    have hζ1 : ζ ≠ 1 := by
      intro h
      simp only [ζ, eC] at h
      rw [Complex.exp_eq_one_iff] at h
      obtain ⟨k, hk⟩ := h
      have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
      have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hm : (((m : ℝ) / (p : ℝ) : ℝ) : ℂ) = (k : ℂ) := by
        apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero)
        linear_combination hk
      have hmr : (m : ℝ) = (k : ℝ) * (p : ℝ) := by
        have hmr' : (m : ℝ) / (p : ℝ) = (k : ℝ) := by exact_mod_cast hm
        exact (div_eq_iff hp0).mp hmr'
      have hmz : m = (p : ℤ) * k := by
        have : m = k * (p : ℤ) := by exact_mod_cast hmr
        linarith
      exact hdvd ⟨k, hmz⟩
    have : (ζ - 1) * ∑ r ∈ Finset.range p, ζ ^ r = 0 := by
      rw [mul_comm, geom_sum_mul, hζp, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hζ1)

lemma sineGauss_shift (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3) (a : ℤ) :
    ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) * Real.sin (2 * π * (a * r : ℤ) / p) =
      (legendreSym p a : ℝ) * sineGauss p := by
  have hp : p.Prime := Fact.out
  have hp_pos : 0 < p := hp.pos
  by_cases ha : (p : ℤ) ∣ a
  · obtain ⟨k, rfl⟩ := ha
    have hleg : legendreSym p ((p : ℤ) * k) = 0 := by
      rw [legendreSym.eq_zero_iff]; simp
    rw [hleg, Int.cast_zero, zero_mul]
    refine Finset.sum_eq_zero fun r _ => ?_
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have harg : 2 * π * (((p : ℤ) * k * r : ℤ) : ℝ) / p = ((k * r : ℤ) : ℝ) * (2 * π) := by
      push_cast; field_simp [hp0]
    rw [harg]
    have : Real.sin (((k * r : ℤ) : ℝ) * (2 * π)) = 0 := by
      simpa using Real.sin_add_int_mul_two_pi 0 (k * r)
    rw [this, mul_zero]
  · set a0 : ℕ := (a % (p : ℤ)).toNat
    have ha_mod_pos : 0 < a % (p : ℤ) := by
      have hnn := Int.emod_nonneg a (Int.natCast_ne_zero.mpr hp.ne_zero)
      have hne : a % (p : ℤ) ≠ 0 := fun h => ha (Int.dvd_of_emod_eq_zero h)
      omega
    have ha0_pos : 1 ≤ a0 := by omega
    have ha0_lt : a0 < p := by
      have := Int.emod_lt_of_pos a (Int.natCast_pos.mpr hp_pos); omega
    have ha0_cast : (a0 : ℤ) = a % (p : ℤ) := Int.toNat_of_nonneg (by omega)
    have hleg_a : legendreSym p a = legendreSym p (a0 : ℤ) := by
      rw [ha0_cast, legendreSym.mod]
    have ha0_ne0 : (a0 : ZMod p) ≠ 0 := by
      intro h
      have hd := (ZMod.natCast_eq_zero_iff a0 p).mp h
      have := Nat.le_of_dvd (by omega) hd; omega
    have ha0_ne0' : ((a0 : ℤ) : ZMod p) ≠ 0 := by simpa using ha0_ne0
    have hleg_sq : (legendreSym p (a0 : ℤ) : ℝ) ^ 2 = 1 := by
      rcases legendreSym.eq_one_or_neg_one p ha0_ne0' with h | h <;> rw [h] <;> norm_num
    rw [hleg_a, sineGauss, Finset.mul_sum]
    refine Finset.sum_bij (fun r _ => (a0 * r) % p) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [Finset.mem_Icc] at hr ⊢
      have hndvd : ¬ p ∣ a0 * r := fun h => by
        rcases hp.dvd_mul.mp h with h1 | h2
        · have := Nat.le_of_dvd (by omega) h1; omega
        · have := Nat.le_of_dvd (by omega) h2; omega
      have hpos : 0 < (a0 * r) % p := Nat.pos_of_ne_zero (fun h => hndvd (Nat.dvd_of_mod_eq_zero h))
      have hlt := Nat.mod_lt (a0 * r) hp_pos; omega
    · intro r₁ hr₁ r₂ hr₂ heq
      simp only [Finset.mem_Icc] at hr₁ hr₂
      have hz : (a0 : ZMod p) * (r₁ : ZMod p) = (a0 : ZMod p) * (r₂ : ZMod p) := by
        have h' : (((a0 * r₁) % p : ℕ) : ZMod p) = (((a0 * r₂) % p : ℕ) : ZMod p) := congrArg Nat.cast heq
        simpa [ZMod.natCast_mod] using h'
      have hr_eq := mul_left_cancel₀ ha0_ne0 hz
      have hmod : r₁ % p = r₂ % p := by rw [← ZMod.val_natCast, ← ZMod.val_natCast, hr_eq]
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
    · intro u hu
      simp only [Finset.mem_Icc] at hu
      set v : ZMod p := (a0 : ZMod p)⁻¹ * (u : ZMod p)
      have hv0 : v ≠ 0 := by
        apply mul_ne_zero (inv_ne_zero ha0_ne0)
        intro h
        have hd := (ZMod.natCast_eq_zero_iff u p).mp h
        have := Nat.le_of_dvd (by omega) hd; omega
      have hv_pos : 1 ≤ v.val := Nat.pos_of_ne_zero (fun h => hv0 ((ZMod.val_eq_zero v).mp h))
      refine ⟨v.val, Finset.mem_Icc.mpr ⟨hv_pos, by have := v.val_lt; omega⟩, ?_⟩
      have h1 : (((a0 * v.val) : ℕ) : ZMod p) = (u : ZMod p) := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val]
        simp [v, mul_inv_cancel_left₀ ha0_ne0]
      have h2 : (((a0 * v.val) : ℕ) : ZMod p).val = (u : ZMod p).val := congrArg ZMod.val h1
      rw [ZMod.val_natCast, ZMod.val_natCast] at h2
      exact h2.trans (Nat.mod_eq_of_lt (by omega))
    · intro r _
      have hsin : Real.sin (2 * π * ((a * (r : ℤ) : ℤ) : ℝ) / p) =
          Real.sin (2 * π * ((a0 * r % p : ℕ) : ℝ) / p) := by
        have hcong : (p : ℤ) ∣ (a * (r : ℤ) - ((a0 * r % p : ℕ) : ℤ)) := by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
          have ha_zm : (a : ZMod p) = (a0 : ZMod p) := by
            have := congrArg (Int.cast (R := ZMod p)) ha0_cast
            simpa [ZMod.intCast_mod] using this.symm
          push_cast
          rw [ha_zm, sub_self]
        obtain ⟨k, hk⟩ := hcong
        have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
        set m0 : ℕ := a0 * r % p
        have hkr : ((a * (r : ℤ) : ℤ) : ℝ) = (m0 : ℝ) + (p : ℝ) * (k : ℝ) := by
          have hz : a * (r : ℤ) = (m0 : ℤ) + (p : ℤ) * k := by linarith
          have hr' := congrArg (Int.cast (R := ℝ)) hz
          simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hr'
        have harg : 2 * π * ((a * (r : ℤ) : ℤ) : ℝ) / p =
            2 * π * (m0 : ℝ) / p + k * (2 * π) := by
          rw [hkr]; field_simp [hp0]
        rw [harg, Real.sin_add_int_mul_two_pi]
      have hleg_r : (legendreSym p (r : ℤ) : ℝ) =
          (legendreSym p (a0 : ℤ) : ℝ) * (legendreSym p ((a0 * r % p : ℕ) : ℤ) : ℝ) := by
        have h1 : legendreSym p ((a0 * r % p : ℕ) : ℤ) =
            legendreSym p (a0 : ℤ) * legendreSym p (r : ℤ) := by
          rw [← legendreSym.mul]
          exact legendreSym_congr p (by simp)
        rw [h1]; push_cast
        calc
          (legendreSym p (r : ℤ) : ℝ)
              = (legendreSym p (a0 : ℤ) : ℝ) ^ 2 * (legendreSym p (r : ℤ) : ℝ) := by
                  rw [hleg_sq, one_mul]
          _ = (legendreSym p (a0 : ℤ) : ℝ) * ((legendreSym p (a0 : ℤ) : ℝ) * (legendreSym p (r : ℤ) : ℝ)) := by
                  ring
      rw [hsin, hleg_r, mul_assoc]

lemma sineGauss_sq (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3) :
    (sineGauss p) ^ 2 = p := by
  have hp : p.Prime := Fact.out
  have hp_pos : 0 < p := hp.pos
  set τ : ℂ := ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℂ) * eC ((r : ℝ) / p)
  have hcos : ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) * Real.cos (2 * π * (r : ℝ) / p) = 0 := by
    have hrev : ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) * Real.cos (2 * π * (r : ℝ) / p) =
        ∑ r ∈ Finset.Icc 1 (p - 1),
          (legendreSym p ((p - r : ℕ) : ℤ) : ℝ) * Real.cos (2 * π * ((p - r : ℕ) : ℝ) / p) := by
      refine Finset.sum_bij (fun r _ => p - r) ?_ ?_ ?_ ?_
      · intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega
      · intro r₁ hr₁ r₂ hr₂ h; simp only [Finset.mem_Icc] at hr₁ hr₂; omega
      · intro r hr; simp only [Finset.mem_Icc] at hr; exact ⟨p - r, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro r hr; simp only [Finset.mem_Icc] at hr; rw [Nat.sub_sub_self (by omega)]
    have hneg : ∑ r ∈ Finset.Icc 1 (p - 1),
        (legendreSym p ((p - r : ℕ) : ℤ) : ℝ) * Real.cos (2 * π * ((p - r : ℕ) : ℝ) / p) =
        -∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) * Real.cos (2 * π * (r : ℝ) / p) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun r hr => ?_
      simp only [Finset.mem_Icc] at hr
      rw [legendre_sub_self p h8 (by omega)]
      have harg : 2 * π * ((p - r : ℕ) : ℝ) / p = 2 * π - 2 * π * (r : ℝ) / p := by
        have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
        rw [Nat.cast_sub (by omega)]; field_simp [hp0]
      rw [harg, Real.cos_two_pi_sub]; push_cast; ring
    linarith
  have hτ_eq : τ = Complex.I * (sineGauss p : ℂ) := by
    apply Complex.ext
    · rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, one_mul, sub_zero, Complex.re_sum]
      trans (∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) * Real.cos (2 * π * (r : ℝ) / p))
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero, eC_re]
        ring_nf
      · exact hcos
    · rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, one_mul, zero_add, Complex.im_sum, sineGauss]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero, eC_im]
      ring_nf
  have hτ_sq : τ ^ 2 = -(p : ℂ) := by
    simp only [τ]
    rw [sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    have hinner : ∀ r ∈ Finset.Icc 1 (p - 1),
        ∑ s ∈ Finset.Icc 1 (p - 1),
          (legendreSym p r : ℂ) * eC ((r : ℝ) / p) * ((legendreSym p s : ℂ) * eC ((s : ℝ) / p)) =
        ∑ t ∈ Finset.Icc 1 (p - 1),
          (legendreSym p t : ℂ) * eC (((1 + (t : ℤ)) * (r : ℤ) : ℤ) / (p : ℝ)) := by
      intro r hr
      simp only [Finset.mem_Icc] at hr
      have hr_ne0 : (r : ZMod p) ≠ 0 := by
        intro h
        have hd := (ZMod.natCast_eq_zero_iff r p).mp h
        have := Nat.le_of_dvd (by omega) hd; omega
      have hr_ne0' : ((r : ℤ) : ZMod p) ≠ 0 := by simpa using hr_ne0
      have hleg_r_sq : (legendreSym p (r : ℤ) : ℂ) ^ 2 = 1 := by
        rcases legendreSym.eq_one_or_neg_one p hr_ne0' with h | h <;> rw [h] <;> norm_num
      refine Finset.sum_bij (fun s _ => ((s : ZMod p) * (r : ZMod p)⁻¹).val) ?_ ?_ ?_ ?_
      · intro s hs
        simp only [Finset.mem_Icc] at hs ⊢
        have hs_ne0 : (s : ZMod p) ≠ 0 := by
          intro h
          have hd := (ZMod.natCast_eq_zero_iff s p).mp h
          have := Nat.le_of_dvd (by omega) hd; omega
        have hne : (s : ZMod p) * (r : ZMod p)⁻¹ ≠ 0 := mul_ne_zero hs_ne0 (inv_ne_zero hr_ne0)
        have hpos : 1 ≤ ((s : ZMod p) * (r : ZMod p)⁻¹).val :=
          Nat.pos_of_ne_zero (fun h => hne ((ZMod.val_eq_zero _).mp h))
        exact ⟨hpos, by have := ZMod.val_lt ((s : ZMod p) * (r : ZMod p)⁻¹); omega⟩
      · intro s₁ hs₁ s₂ hs₂ heq
        simp only [Finset.mem_Icc] at hs₁ hs₂
        have hz : (s₁ : ZMod p) * (r : ZMod p)⁻¹ = (s₂ : ZMod p) * (r : ZMod p)⁻¹ :=
          ZMod.val_injective p heq
        have hs_eq : (s₁ : ZMod p) = (s₂ : ZMod p) := mul_right_cancel₀ (inv_ne_zero hr_ne0) hz
        have hmod : s₁ % p = s₂ % p := by rw [← ZMod.val_natCast, ← ZMod.val_natCast, hs_eq]
        rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
      · intro t ht
        simp only [Finset.mem_Icc] at ht
        have ht_ne0 : (t : ZMod p) ≠ 0 := by
          intro h
          have hd := (ZMod.natCast_eq_zero_iff t p).mp h
          have := Nat.le_of_dvd (by omega) hd; omega
        set s : ℕ := ((t : ZMod p) * (r : ZMod p)).val
        have hs_ne : (t : ZMod p) * (r : ZMod p) ≠ 0 := mul_ne_zero ht_ne0 hr_ne0
        have hs_pos : 1 ≤ s := Nat.pos_of_ne_zero (fun h => hs_ne ((ZMod.val_eq_zero _).mp h))
        refine ⟨s, Finset.mem_Icc.mpr ⟨hs_pos, by have := ZMod.val_lt ((t : ZMod p) * (r : ZMod p)); omega⟩, ?_⟩
        have hval : ((s : ZMod p) * (r : ZMod p)⁻¹) = (t : ZMod p) := by
          simp only [s, ZMod.natCast_zmod_val, mul_inv_cancel_right₀ hr_ne0]
        rw [hval, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      · intro s _
        set t : ℕ := ((s : ZMod p) * (r : ZMod p)⁻¹).val
        have ht_mod : (t : ZMod p) * (r : ZMod p) = (s : ZMod p) := by
          simp only [t, ZMod.natCast_zmod_val]
          exact inv_mul_cancel_right₀ hr_ne0 _
        have hleg_s : (legendreSym p (r : ℤ) : ℂ) * (legendreSym p (s : ℤ) : ℂ) =
            (legendreSym p (t : ℤ) : ℂ) := by
          have hs_leg : legendreSym p (s : ℤ) = legendreSym p (t : ℤ) * legendreSym p (r : ℤ) := by
            rw [← legendreSym.mul]
            exact legendreSym_congr p (by simpa using ht_mod.symm)
          rw [hs_leg]; push_cast
          linear_combination (legendreSym p (t : ℤ) : ℂ) * hleg_r_sq
        have heC : eC ((r : ℝ) / p) * eC ((s : ℝ) / p) =
            eC (((1 + (t : ℤ)) * (r : ℤ) : ℤ) / (p : ℝ)) := by
          rw [← eC_add]
          have hcong : (p : ℤ) ∣ ((r : ℤ) + (s : ℤ) - (1 + (t : ℤ)) * (r : ℤ)) := by
            rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
            push_cast; linear_combination ht_mod.symm
          obtain ⟨k, hk⟩ := hcong
          have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
          have hkr : (r : ℝ) + (s : ℝ) = (((1 + (t : ℤ)) * (r : ℤ) : ℤ) : ℝ) + (p : ℝ) * (k : ℝ) := by
            have hz : (r : ℤ) + (s : ℤ) = (1 + (t : ℤ)) * (r : ℤ) + (p : ℤ) * k := by linarith
            have hr' := congrArg (Int.cast (R := ℝ)) hz
            simpa using hr'
          have harg : (r : ℝ) / p + (s : ℝ) / p =
              (((1 + (t : ℤ)) * (r : ℤ) : ℤ) : ℝ) / (p : ℝ) + (k : ℤ) := by
            field_simp [hp0]; linarith
          rw [harg, eC_add, eC_int, mul_one]
        calc
          (legendreSym p (r : ℤ) : ℂ) * eC ((r : ℝ) / p) * ((legendreSym p (s : ℤ) : ℂ) * eC ((s : ℝ) / p))
              = ((legendreSym p (r : ℤ) : ℂ) * (legendreSym p (s : ℤ) : ℂ)) *
                  (eC ((r : ℝ) / p) * eC ((s : ℝ) / p)) := by ring
          _ = (legendreSym p (t : ℤ) : ℂ) * eC (((1 + (t : ℤ)) * (r : ℤ) : ℤ) / (p : ℝ)) := by
              rw [hleg_s, heC]
    rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
    have houter : ∀ t ∈ Finset.Icc 1 (p - 1),
        ∑ r ∈ Finset.Icc 1 (p - 1),
          (legendreSym p t : ℂ) * eC (((1 + (t : ℤ)) * (r : ℤ) : ℤ) / (p : ℝ)) =
        (legendreSym p t : ℂ) * ((if t = p - 1 then (p : ℂ) else 0) - 1) := by
      intro t ht
      simp only [Finset.mem_Icc] at ht
      rw [← Finset.mul_sum]; congr 1
      have hrange : Finset.range p = insert 0 (Finset.Icc 1 (p - 1)) := by
        ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      have h0 : (0 : ℕ) ∉ Finset.Icc 1 (p - 1) := by simp
      have hsum := sum_eC_div_p p hp_pos (1 + (t : ℤ))
      rw [hrange, Finset.sum_insert h0] at hsum
      have he0 : eC (((1 + (t : ℤ)) * (0 : ℕ) : ℤ) / (p : ℝ)) = 1 := by simpa using eC_int 0
      rw [he0] at hsum
      have hdvd_iff : (p : ℤ) ∣ (1 + (t : ℤ)) ↔ t = p - 1 := by
        constructor
        · intro h
          have h3 := Int.le_of_dvd (by omega) h; omega
        · rintro rfl; exact ⟨1, by omega⟩
      rw [if_congr hdvd_iff rfl rfl] at hsum
      linear_combination hsum
    rw [Finset.sum_congr rfl houter]
    have hsplit : ∑ t ∈ Finset.Icc 1 (p - 1),
        (legendreSym p t : ℂ) * ((if t = p - 1 then (p : ℂ) else 0) - 1) =
        (legendreSym p ((p - 1 : ℕ) : ℤ) : ℂ) * (p : ℂ) -
        ∑ t ∈ Finset.Icc 1 (p - 1), (legendreSym p t : ℂ) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, mul_one]; congr 1
      rw [Finset.sum_eq_single (p - 1)]
      · simp
      · intro t _ hne; simp [hne]
      · intro h; exfalso; apply h; simp only [Finset.mem_Icc]; omega
    rw [hsplit]
    have hsum0 : ∑ t ∈ Finset.Icc 1 (p - 1), (legendreSym p t : ℂ) = 0 := by
      have := congrArg Complex.ofReal (sum_legendre_Icc_eq_zero p h8)
      simpa using this
    have hpm1 : legendreSym p ((p - 1 : ℕ) : ℤ) = -1 := by
      rw [legendre_sub_self p h8 hp.one_le, Nat.cast_one, legendreSym.at_one]
    rw [hsum0, hpm1]; simp
  have hsqC : ((sineGauss p : ℂ) ^ 2) = (p : ℂ) := by
    have h1 : (Complex.I * (sineGauss p : ℂ)) ^ 2 = -(p : ℂ) := by
      rw [← hτ_eq]; exact hτ_sq
    rw [mul_pow, Complex.I_sq] at h1
    linear_combination -h1
  exact_mod_cast hsqC

lemma sum_mul_sin_eq_cot (p r : ℕ) (hp : p.Prime) (hr1 : 1 ≤ r) (hr2 : r ≤ p - 1) :
    ∑ a ∈ Finset.Icc 1 (p - 1), (a : ℝ) * Real.sin (2 * π * (a * r : ℤ) / p) =
      -(p : ℝ) / 2 * Real.cot (π * (r : ℝ) / p) := by
  set ζ : ℂ := eC ((r : ℝ) / p)
  have hζp : ζ ^ p = 1 := by
    rw [← eC_nat_mul]
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have : (p : ℝ) * ((r : ℝ) / p) = (r : ℝ) := by field_simp [hp0]
    rw [this]; exact eC_int r
  have hζ1 : ζ ≠ 1 := by
    intro h
    simp only [ζ, eC] at h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨k, hk⟩ := h
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hrk : (((r : ℝ) / p : ℝ) : ℂ) = (k : ℂ) := by
      apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero)
      linear_combination hk
    have hrr : (r : ℝ) = (k : ℝ) * (p : ℝ) := by
      have : (r : ℝ) / p = (k : ℝ) := by exact_mod_cast hrk
      exact (div_eq_iff hp0).mp this
    have hrz : (r : ℤ) = k * (p : ℤ) := by exact_mod_cast hrr
    have hdvd : p ∣ r := Int.natCast_dvd_natCast.mp ⟨k, by linarith⟩
    have := Nat.le_of_dvd (by omega) hdvd; omega
  have halg : (ζ - 1) * ∑ a ∈ Finset.Icc 1 (p - 1), (a : ℂ) * ζ ^ a = (p : ℂ) := by
    have hsum0 : ∑ a ∈ Finset.range p, ζ ^ a = 0 := by
      have h1 : (ζ - 1) * ∑ a ∈ Finset.range p, ζ ^ a = 0 := by
        rw [mul_comm, geom_sum_mul, hζp, sub_self]
      exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hζ1)
    have hid : ∀ n : ℕ, (ζ - 1) * ∑ a ∈ Finset.range n, (a : ℂ) * ζ ^ a =
        (n : ℂ) * ζ ^ n - ∑ a ∈ Finset.range n, ζ ^ (a + 1) := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ]; push_cast; ring
    have hrange_eq : ∑ a ∈ Finset.range p, (a : ℂ) * ζ ^ a =
        ∑ a ∈ Finset.Icc 1 (p - 1), (a : ℂ) * ζ ^ a := by
      have hrange : Finset.range p = insert 0 (Finset.Icc 1 (p - 1)) := by
        ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hrange, Finset.sum_insert (by simp)]; simp
    have hshift : ∑ a ∈ Finset.range p, ζ ^ (a + 1) = 0 := by
      simp_rw [pow_succ']; rw [← Finset.mul_sum, hsum0, mul_zero]
    rw [← hrange_eq, hid p, hζp, hshift]; ring
  have hval : ∑ a ∈ Finset.Icc 1 (p - 1), (a : ℂ) * ζ ^ a = (p : ℂ) / (ζ - 1) :=
    eq_div_of_mul_eq (sub_ne_zero.mpr hζ1) (by rw [mul_comm]; exact halg)
  have him_lhs : (∑ a ∈ Finset.Icc 1 (p - 1), (a : ℂ) * ζ ^ a).im =
      ∑ a ∈ Finset.Icc 1 (p - 1), (a : ℝ) * Real.sin (2 * π * (a * r : ℤ) / p) := by
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    congr 1; rw [← eC_nat_mul, eC_im]; congr 1; push_cast; ring
  have him_rhs : ((p : ℂ) / (ζ - 1)).im = -(p : ℝ) / 2 * Real.cot (π * (r : ℝ) / p) := by
    set θ : ℝ := π * (r : ℝ) / p
    have hsin_ne : Real.sin θ ≠ 0 := by
      have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr (by omega)
      have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
      have hpos : 0 < θ := div_pos (mul_pos Real.pi_pos hr_pos) hp_pos
      have hlt : θ < π := by
        simp only [θ]
        rw [div_lt_iff₀ hp_pos]
        have : (r : ℝ) < (p : ℝ) := by exact_mod_cast (show r < p by omega)
        nlinarith [Real.pi_pos]
      exact (Real.sin_pos_of_pos_of_lt_pi hpos hlt).ne'
    have hζ_trig : ζ = (Real.cos (2 * θ) : ℂ) + (Real.sin (2 * θ) : ℂ) * Complex.I := by
      have := eC_eq_cos_add_sin_mul_I ((r : ℝ) / p)
      have harg : 2 * π * ((r : ℝ) / p) = 2 * θ := by simp only [θ]; ring
      rwa [harg] at this
    set aR : ℝ := -2 * Real.sin θ ^ 2
    set bR : ℝ := 2 * Real.sin θ * Real.cos θ
    have hsub : ζ - 1 = (aR : ℂ) + (bR : ℂ) * Complex.I := by
      rw [hζ_trig]
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, mul_zero, mul_one,
          sub_zero, add_zero, aR]
        rw [Real.cos_two_mul, Real.sin_sq]; ring
      · simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_im, mul_zero, mul_one,
          add_zero, sub_zero, zero_add, bR]
        rw [Real.sin_two_mul]
    rw [hsub, Complex.div_im, Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, zero_sub]
    have hre : ((aR : ℂ) + (bR : ℂ) * Complex.I).re = aR := by simp
    have him : ((aR : ℂ) + (bR : ℂ) * Complex.I).im = bR := by simp
    have hns : Complex.normSq ((aR : ℂ) + (bR : ℂ) * Complex.I) = 4 * Real.sin θ ^ 2 := by
      rw [Complex.normSq_apply, hre, him]
      have hsc := Real.sin_sq_add_cos_sq θ
      simp only [aR, bR]; nlinarith
    rw [him, hns, Real.cot_eq_cos_div_sin]
    simp only [bR]
    field_simp [hsin_ne]
    ring
  rw [← him_lhs, hval, him_rhs]

theorem cot_sum_eq_gauss_mul_weighted (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3) :
    ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) * Real.cot (π * (r : ℝ) / p) =
      -(2 * sineGauss p / p) * ∑ a ∈ Finset.Icc 1 (p - 1), (a : ℝ) * (legendreSym p a : ℝ) := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h1 : ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) *
      (-(p : ℝ) / 2 * Real.cot (π * (r : ℝ) / p)) =
      ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) *
        ∑ a ∈ Finset.Icc 1 (p - 1), (a : ℝ) * Real.sin (2 * π * (a * r : ℤ) / p) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    simp only [Finset.mem_Icc] at hr
    rw [sum_mul_sin_eq_cot p r hp hr.1 hr.2]
  have h2 : ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) *
        ∑ a ∈ Finset.Icc 1 (p - 1), (a : ℝ) * Real.sin (2 * π * (a * r : ℤ) / p) =
      sineGauss p * ∑ a ∈ Finset.Icc 1 (p - 1), (a : ℝ) * (legendreSym p a : ℝ) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    calc
      ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) * ((a : ℝ) * Real.sin (2 * π * (a * r : ℤ) / p))
          = (a : ℝ) * ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) * Real.sin (2 * π * (a * r : ℤ) / p) := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => by ring
      _ = (a : ℝ) * ((legendreSym p a : ℝ) * sineGauss p) := by rw [sineGauss_shift p h8 a]
      _ = sineGauss p * ((a : ℝ) * (legendreSym p a : ℝ)) := by ring
  have h3 : ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) *
      (-(p : ℝ) / 2 * Real.cot (π * (r : ℝ) / p)) =
      -(p : ℝ) / 2 * ∑ r ∈ Finset.Icc 1 (p - 1), (legendreSym p r : ℝ) * Real.cot (π * (r : ℝ) / p) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => by ring
  rw [h3, h2] at h1
  field_simp [hp0] at h1 ⊢
  linarith

/-! ### Part 2b: Partial sums of L(1, χ), Abel limit, and elimination of Gauss sum sign -/

/-- Partial sum of `L(1, χ_p)` up to `N`. -/
noncomputable def LPartial (p : ℕ) [Fact p.Prime] (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (legendreSym p n : ℝ) / n

/-- Partial sum of `χ_p` up to `N`. -/
noncomputable def chiSum (p : ℕ) [Fact p.Prime] (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (legendreSym p n : ℝ)

lemma sum_legendre_block_eq_zero (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3) (m : ℕ) :
    ∑ k ∈ Finset.range p, (legendreSym p ((m + k : ℕ) : ℤ) : ℝ) = 0 := by
  have hp : p.Prime := Fact.out
  have hp_pos : 0 < p := hp.pos
  have h0 : ∑ k ∈ Finset.range p, (legendreSym p (k : ℤ) : ℝ) = 0 := by
    have hrange : Finset.range p = insert 0 (Finset.Icc 1 (p - 1)) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hrange, Finset.sum_insert (by simp)]
    simp [sum_legendre_Icc_eq_zero p h8]
  rw [← h0]
  refine Finset.sum_bij (fun k _ => (m + k) % p) ?_ ?_ ?_ ?_
  · intro k _; exact Finset.mem_range.mpr (Nat.mod_lt _ hp_pos)
  · intro k₁ hk₁ k₂ hk₂ heq
    simp only [Finset.mem_range] at hk₁ hk₂
    have hz : ((m + k₁ : ℕ) : ZMod p) = ((m + k₂ : ℕ) : ZMod p) := by
      have h' : (((m + k₁) % p : ℕ) : ZMod p) = (((m + k₂) % p : ℕ) : ZMod p) := congrArg Nat.cast heq
      simpa [ZMod.natCast_mod] using h'
    push_cast at hz
    have hkeq : (k₁ : ZMod p) = (k₂ : ZMod p) := add_left_cancel hz
    have hmod : k₁ % p = k₂ % p := by rw [← ZMod.val_natCast, ← ZMod.val_natCast, hkeq]
    rwa [Nat.mod_eq_of_lt hk₁, Nat.mod_eq_of_lt hk₂] at hmod
  · intro u hu
    simp only [Finset.mem_range] at hu
    set v : ZMod p := (u : ZMod p) - (m : ZMod p)
    refine ⟨v.val, Finset.mem_range.mpr v.val_lt, ?_⟩
    have h1 : ((m + v.val : ℕ) : ZMod p) = (u : ZMod p) := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val]; simp [v]
    have h2 : ((m + v.val : ℕ) : ZMod p).val = (u : ZMod p).val := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hu] at h2
    exact h2
  · intro k _
    congr 1
    exact legendreSym_congr p (by simp)

lemma abs_chiSum_le (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3) (N : ℕ) :
    |chiSum p N| ≤ p := by
  have hp : p.Prime := Fact.out
  have hp_pos : 0 < p := hp.pos
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hlt : N < p
    · calc
        |chiSum p N| ≤ ∑ n ∈ Finset.Icc 1 N, |(legendreSym p n : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) :=
            Finset.sum_le_sum fun n _ => abs_legendreSym_le_one p (n : ℤ)
        _ = (N : ℝ) := by simp
        _ ≤ (p : ℝ) := by exact_mod_cast hlt.le
    · have hge : p ≤ N := Nat.le_of_not_lt hlt
      have hsplit : chiSum p N = chiSum p (N - p) +
          ∑ k ∈ Finset.range p, (legendreSym p (((N - p + 1) + k : ℕ) : ℤ) : ℝ) := by
        simp only [chiSum]
        have hIcc : Finset.Icc 1 N = Finset.Icc 1 (N - p) ∪ Finset.Icc (N - p + 1) N := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
        have hdisj : Disjoint (Finset.Icc 1 (N - p)) (Finset.Icc (N - p + 1) N) := by
          rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
        rw [hIcc, Finset.sum_union hdisj]
        congr 1
        refine Finset.sum_bij (fun x _ => x - (N - p + 1)) ?_ ?_ ?_ ?_
        · intro x hx; simp only [Finset.mem_Icc, Finset.mem_range] at hx ⊢; omega
        · intro x₁ hx₁ x₂ hx₂ h; simp only [Finset.mem_Icc] at hx₁ hx₂; omega
        · intro k hk; simp only [Finset.mem_range] at hk
          exact ⟨N - p + 1 + k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro x hx; simp only [Finset.mem_Icc] at hx
          rw [show N - p + 1 + (x - (N - p + 1)) = x by omega]
      rw [hsplit, sum_legendre_block_eq_zero p h8, add_zero]
      exact ih (N - p) (by omega)

/-- Summation by parts on `Icc (M + 1) N` against a nonincreasing nonnegative function `f`. -/
lemma abel_sum_Icc_bound (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3)
    {M N : ℕ} (hMN : M ≤ N) {f : ℕ → ℝ}
    (hf_nonneg : ∀ n, 0 ≤ f n) (hf_anti : ∀ n, M + 1 ≤ n → f (n + 1) ≤ f n) :
    |∑ n ∈ Finset.Icc (M + 1) N, (legendreSym p n : ℝ) * f n| ≤ 2 * (p : ℝ) * f (M + 1) := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  by_cases hEq : M = N
  · subst hEq
    have : Finset.Icc (M + 1) M = ∅ := by ext x; simp
    rw [this, Finset.sum_empty, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hp0) (hf_nonneg _)
  have hlt : M < N := Nat.lt_of_le_of_ne hMN hEq
  have hdiff : ∀ n : ℕ, 1 ≤ n → (legendreSym p n : ℝ) = chiSum p n - chiSum p (n - 1) := by
    intro n hn
    simp only [chiSum]
    have hIcc : Finset.Icc 1 n = insert n (Finset.Icc 1 (n - 1)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    ring
  have habel : ∑ n ∈ Finset.Icc (M + 1) N, (legendreSym p n : ℝ) * f n =
      chiSum p N * f N - chiSum p M * f (M + 1) +
        ∑ n ∈ Finset.Icc (M + 1) (N - 1), chiSum p n * (f n - f (n + 1)) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show M + 1 ≤ N by omega)
    clear hMN hEq hlt
    induction k with
    | zero =>
      simp only [add_zero, Finset.Icc_self, Finset.sum_singleton, Nat.add_sub_cancel]
      have hEmp : Finset.Icc (M + 1) M = ∅ := by ext x; simp
      rw [hEmp, Finset.sum_empty, add_zero, hdiff (M + 1) (by omega), Nat.add_sub_cancel]
      ring
    | succ k ih =>
      have hIcc1 : Finset.Icc (M + 1) (M + 1 + (k + 1)) =
          insert (M + 1 + (k + 1)) (Finset.Icc (M + 1) (M + 1 + k)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hIcc2 : Finset.Icc (M + 1) (M + 1 + (k + 1) - 1) =
          insert (M + 1 + k) (Finset.Icc (M + 1) (M + 1 + k - 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc1, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih,
        hIcc2, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega),
        hdiff (M + 1 + (k + 1)) (by omega)]
      have hsub : M + 1 + (k + 1) - 1 = M + 1 + k := by omega
      rw [hsub, show M + 1 + k + 1 = M + 1 + (k + 1) by omega]
      ring
  rw [habel]
  have htele : ∑ n ∈ Finset.Icc (M + 1) (N - 1), (f n - f (n + 1)) = f (M + 1) - f N := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show M + 1 ≤ N by omega)
    clear hMN hEq hlt habel hf_anti
    induction k with
    | zero => simp
    | succ k ih =>
      have hIcc2 : Finset.Icc (M + 1) (M + 1 + (k + 1) - 1) =
          insert (M + 1 + k) (Finset.Icc (M + 1) (M + 1 + k - 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc2, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih,
        show M + 1 + k + 1 = M + 1 + (k + 1) by omega]
      ring
  have hsum_bound : |∑ n ∈ Finset.Icc (M + 1) (N - 1), chiSum p n * (f n - f (n + 1))| ≤
      (p : ℝ) * (f (M + 1) - f N) := by
    calc
      |∑ n ∈ Finset.Icc (M + 1) (N - 1), chiSum p n * (f n - f (n + 1))|
          ≤ ∑ n ∈ Finset.Icc (M + 1) (N - 1), |chiSum p n * (f n - f (n + 1))| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Icc (M + 1) (N - 1), (p : ℝ) * (f n - f (n + 1)) := by
            refine Finset.sum_le_sum fun n hn => ?_
            simp only [Finset.mem_Icc] at hn
            rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hf_anti n hn.1))]
            exact mul_le_mul_of_nonneg_right (abs_chiSum_le p h8 n) (sub_nonneg.mpr (hf_anti n hn.1))
      _ = (p : ℝ) * ∑ n ∈ Finset.Icc (M + 1) (N - 1), (f n - f (n + 1)) := by rw [← Finset.mul_sum]
      _ = (p : ℝ) * (f (M + 1) - f N) := by rw [htele]
  have h1 : |chiSum p N * f N| ≤ (p : ℝ) * f N := by
    rw [abs_mul, abs_of_nonneg (hf_nonneg N)]
    exact mul_le_mul_of_nonneg_right (abs_chiSum_le p h8 N) (hf_nonneg N)
  have h2 : |chiSum p M * f (M + 1)| ≤ (p : ℝ) * f (M + 1) := by
    rw [abs_mul, abs_of_nonneg (hf_nonneg (M + 1))]
    exact mul_le_mul_of_nonneg_right (abs_chiSum_le p h8 M) (hf_nonneg (M + 1))
  have htri1 := abs_add_le (chiSum p N * f N - chiSum p M * f (M + 1))
    (∑ n ∈ Finset.Icc (M + 1) (N - 1), chiSum p n * (f n - f (n + 1)))
  have htri2 := abs_sub (chiSum p N * f N) (chiSum p M * f (M + 1))
  linarith

lemma cauchySeq_LPartial (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3) :
    CauchySeq (LPartial p) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * (p : ℝ) / ε)
  refine ⟨N₀, fun m hm n hn => ?_⟩
  wlog hle : m ≤ n generalizing m n
  · rw [Real.dist_eq, abs_sub_comm]
    exact this n hn m hm (le_of_not_ge hle)
  rw [Real.dist_eq, abs_sub_comm]
  have hsub : LPartial p n - LPartial p m =
      ∑ k ∈ Finset.Icc (m + 1) n, (legendreSym p k : ℝ) * ((k : ℝ)⁻¹) := by
    simp only [LPartial, div_eq_mul_inv]
    have hIcc : Finset.Icc 1 n = Finset.Icc 1 m ∪ Finset.Icc (m + 1) n := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Icc (m + 1) n) := by
      rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
    rw [hIcc, Finset.sum_union hdisj]; ring
  rw [hsub]
  have hb := abel_sum_Icc_bound p h8 hle (f := fun k : ℕ => (k : ℝ)⁻¹)
    (fun k => inv_nonneg.mpr (Nat.cast_nonneg k))
    (fun k hk => inv_anti₀ (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast Nat.le_succ k))
  have hpos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hgt : 2 * (p : ℝ) / ε < ((m + 1 : ℕ) : ℝ) := by
    have : (N₀ : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (show N₀ < m + 1 by omega)
    linarith
  have hlt : 2 * (p : ℝ) * (((m + 1 : ℕ) : ℝ)⁻¹) < ε := by
    rw [← div_eq_mul_inv, div_lt_iff₀ hpos]
    exact (div_lt_iff₀ hε).mp hgt |>.trans_eq (mul_comm _ _)
  exact lt_of_le_of_lt hb hlt

/-- The limit value `L(1, χ_p) = lim_{N → ∞} ∑_{n=1}^N (n/p)/n`. -/
noncomputable def LVal (p : ℕ) [Fact p.Prime] : ℝ :=
  limUnder atTop (LPartial p)

lemma tendsto_LPartial (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3) :
    Tendsto (LPartial p) atTop (𝓝 (LVal p)) :=
  (cauchySeq_tendsto_of_complete (cauchySeq_LPartial p h8)).choose_spec |> fun h => by
    have heq : LVal p = (cauchySeq_tendsto_of_complete (cauchySeq_LPartial p h8)).choose :=
      tendsto_nhds_unique (tendsto_nhds_limUnder ⟨_, h⟩) h
    rwa [heq]

/-- Abel power series `F_p(t) = ∑' n, (n/p)/n * t^n` for `0 < t < 1`. -/
noncomputable def abelF (p : ℕ) [Fact p.Prime] (t : ℝ) : ℝ :=
  ∑' n : ℕ, (legendreSym p n : ℝ) / n * t ^ n

lemma summable_abelF (p : ℕ) [Fact p.Prime] {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun n : ℕ => (legendreSym p n : ℝ) / n * t ^ n) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => t ^ n)
    (summable_geometric_of_lt_one ht0 ht1) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg (pow_nonneg ht0 n)]
  by_cases hn : n = 0
  · subst hn; simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hchi := abs_legendreSym_le_one p (n : ℤ)
    have hdiv : |(legendreSym p n : ℝ)| / |(n : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), div_le_one (by linarith)]
      linarith
    nlinarith [pow_nonneg ht0 n]

lemma abelF_eq_one_sub_mul_tsum (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    abelF p t = (1 - t) * ∑' n : ℕ, LPartial p n * t ^ n := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ n, |LPartial p n| ≤ B := by
    obtain ⟨C, hC⟩ := (tendsto_LPartial p h8).bddAbove_range
    obtain ⟨D, hD⟩ := (tendsto_LPartial p h8).bddBelow_range
    refine ⟨max |C| |D| + 1, fun n => ?_⟩
    have h1 : LPartial p n ≤ C := hC ⟨n, rfl⟩
    have h2 : D ≤ LPartial p n := hD ⟨n, rfl⟩
    rw [abs_le]
    constructor <;> linarith [le_abs_self C, neg_abs_le D, le_max_left |C| |D|, le_max_right |C| |D|]
  have hsumL : Summable (fun n : ℕ => LPartial p n * t ^ n) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => B * t ^ n)
      ((summable_geometric_of_lt_one ht0 ht1).mul_left B) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht0 n)]
    exact mul_le_mul_of_nonneg_right (hB n) (pow_nonneg ht0 n)
  have hsumL_shift : Summable (fun n : ℕ => LPartial p n * t ^ (n + 1)) := by
    simpa [pow_succ, mul_assoc] using hsumL.mul_right t
  have hL0 : LPartial p 0 = 0 := by simp [LPartial]
  have hstep : ∀ n : ℕ, (legendreSym p ((n + 1 : ℕ) : ℤ) : ℝ) / ((n + 1 : ℕ) : ℝ) * t ^ (n + 1) =
      LPartial p (n + 1) * t ^ (n + 1) - LPartial p n * t ^ (n + 1) := by
    intro n
    have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    simp only [LPartial]
    rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    ring
  have h1 : abelF p t = ∑' n : ℕ, (legendreSym p ((n + 1 : ℕ) : ℤ) : ℝ) / ((n + 1 : ℕ) : ℝ) * t ^ (n + 1) := by
    rw [abelF, (summable_abelF p ht0 ht1).tsum_eq_zero_add]
    simp only [Nat.cast_zero, div_zero, zero_mul, zero_add]
  have h2 : (∑' n : ℕ, LPartial p (n + 1) * t ^ (n + 1)) = ∑' n : ℕ, LPartial p n * t ^ n := by
    rw [hsumL.tsum_eq_zero_add, hL0, zero_mul, zero_add]
  have h3 : (∑' n : ℕ, LPartial p n * t ^ (n + 1)) = t * ∑' n : ℕ, LPartial p n * t ^ n := by
    simp_rw [pow_succ', ← mul_assoc, mul_comm _ t, mul_assoc]
    rw [tsum_mul_left]
  rw [h1]
  simp_rw [hstep]
  have hsum_succ : Summable (fun n : ℕ => LPartial p (n + 1) * t ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hsumL
  rw [hsum_succ.tsum_sub hsumL_shift, h2, h3]
  ring

lemma tendsto_abelF (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3) :
    Tendsto (abelF p) (𝓝[<] 1) (𝓝 (LVal p)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp (tendsto_LPartial p h8) (ε / 2) (by linarith)
  set C : ℝ := ∑ n ∈ Finset.range N₀, |LPartial p n - LVal p|
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set δ : ℝ := min (1 / 2) (ε / (2 * (C + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  filter_upwards [Ioo_mem_nhdsLT (show 1 - δ < 1 by linarith)] with t ⟨htlo, ht1⟩
  have ht0 : 0 ≤ t := by
    have : δ ≤ 1 / 2 := min_le_left _ _
    linarith
  have h1t : 0 < 1 - t := by linarith
  rw [Real.dist_eq, abelF_eq_one_sub_mul_tsum p h8 ht0 ht1]
  have hgeom : (1 - t) * ∑' n : ℕ, t ^ n = 1 := by
    rw [tsum_geometric_of_lt_one ht0 ht1]; field_simp [h1t.ne']
  have hL : Summable (fun n : ℕ => LPartial p n * t ^ n) := by
    obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ n, |LPartial p n| ≤ M := by
      obtain ⟨U, hU⟩ := (tendsto_LPartial p h8).bddAbove_range
      obtain ⟨L, hL'⟩ := (tendsto_LPartial p h8).bddBelow_range
      refine ⟨max |U| |L| + 1, fun n => ?_⟩
      have h1 : LPartial p n ≤ U := hU ⟨n, rfl⟩
      have h2 : L ≤ LPartial p n := hL' ⟨n, rfl⟩
      rw [abs_le]; constructor <;> linarith [le_abs_self U, neg_abs_le L, le_max_left |U| |L|, le_max_right |U| |L|]
    refine Summable.of_norm_bounded (g := fun n : ℕ => M * t ^ n)
      ((summable_geometric_of_lt_one ht0 ht1).mul_left M) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht0 n)]
    exact mul_le_mul_of_nonneg_right (hM n) (pow_nonneg ht0 n)
  have hV : Summable (fun n : ℕ => LVal p * t ^ n) :=
    (summable_geometric_of_lt_one ht0 ht1).mul_left (LVal p)
  have hsum_diff : Summable (fun n : ℕ => (LPartial p n - LVal p) * t ^ n) := by
    simpa [sub_mul] using hL.sub hV
  have hrew : (1 - t) * (∑' n : ℕ, LPartial p n * t ^ n) - LVal p =
      (1 - t) * ∑' n : ℕ, (LPartial p n - LVal p) * t ^ n := by
    have hsub : (∑' n : ℕ, (LPartial p n - LVal p) * t ^ n) =
        (∑' n : ℕ, LPartial p n * t ^ n) - (∑' n : ℕ, LVal p * t ^ n) := by
      simp_rw [sub_mul]; exact hL.tsum_sub hV
    rw [hsub, tsum_mul_left, mul_sub]
    have : (1 - t) * (LVal p * ∑' n : ℕ, t ^ n) = LVal p := by
      rw [← mul_assoc, mul_comm (1 - t), mul_assoc, hgeom, mul_one]
    linarith
  rw [hrew, abs_mul, abs_of_pos h1t]
  rw [← hsum_diff.sum_add_tsum_nat_add N₀]
  have hhead : |∑ n ∈ Finset.range N₀, (LPartial p n - LVal p) * t ^ n| ≤ C := by
    calc
      |∑ n ∈ Finset.range N₀, (LPartial p n - LVal p) * t ^ n|
          ≤ ∑ n ∈ Finset.range N₀, |(LPartial p n - LVal p) * t ^ n| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range N₀, |LPartial p n - LVal p| := by
            refine Finset.sum_le_sum fun n _ => ?_
            rw [abs_mul, abs_of_nonneg (pow_nonneg ht0 n)]
            have htpow : t ^ n ≤ 1 := pow_le_one₀ ht0 ht1.le
            nlinarith [abs_nonneg (LPartial p n - LVal p)]
  have htail_bound_pt : ∀ k : ℕ, |(LPartial p (k + N₀) - LVal p) * t ^ (k + N₀)| ≤ (ε / 2) * t ^ k := by
    intro k
    rw [abs_mul, abs_of_nonneg (pow_nonneg ht0 _)]
    have hk := hN₀ (k + N₀) (by omega)
    rw [Real.dist_eq] at hk
    have hpow : t ^ (k + N₀) ≤ t ^ k := by
      rw [pow_add]; nlinarith [pow_nonneg ht0 k, pow_le_one₀ ht0 ht1.le (n := N₀)]
    nlinarith [pow_nonneg ht0 (k + N₀)]
  have htail_sum : Summable (fun k : ℕ => ‖(LPartial p (k + N₀) - LVal p) * t ^ (k + N₀)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => by simpa only [Real.norm_eq_abs] using htail_bound_pt k)
      ((summable_geometric_of_lt_one ht0 ht1).mul_left (ε / 2))
  have htail : |∑' k : ℕ, (LPartial p (k + N₀) - LVal p) * t ^ (k + N₀)| ≤
      (ε / 2) * ∑' k : ℕ, t ^ k := by
    calc
      |∑' k : ℕ, (LPartial p (k + N₀) - LVal p) * t ^ (k + N₀)|
          = ‖∑' k : ℕ, (LPartial p (k + N₀) - LVal p) * t ^ (k + N₀)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' k : ℕ, ‖(LPartial p (k + N₀) - LVal p) * t ^ (k + N₀)‖ := norm_tsum_le_tsum_norm htail_sum
      _ ≤ ∑' k : ℕ, (ε / 2) * t ^ k :=
            htail_sum.tsum_le_tsum (fun k => by simpa only [Real.norm_eq_abs] using htail_bound_pt k)
              ((summable_geometric_of_lt_one ht0 ht1).mul_left _)
      _ = (ε / 2) * ∑' k : ℕ, t ^ k := tsum_mul_left
  have htri := abs_add_le (∑ n ∈ Finset.range N₀, (LPartial p n - LVal p) * t ^ n)
    (∑' k : ℕ, (LPartial p (k + N₀) - LVal p) * t ^ (k + N₀))
  have htail_mul : (1 - t) * ((ε / 2) * ∑' k : ℕ, t ^ k) = ε / 2 := by
    rw [← mul_assoc, mul_comm (1 - t), mul_assoc, hgeom, mul_one]
  have hhead_mul : (1 - t) * C < ε / 2 := by
    have hlt1 : 1 - t < ε / (2 * (C + 1)) := lt_of_lt_of_le (by linarith) (min_le_right _ _)
    have hmul : (1 - t) * (C + 1) < ε / 2 := by
      have := (lt_div_iff₀ (show (0 : ℝ) < 2 * (C + 1) by linarith)).mp hlt1
      linarith
    nlinarith
  calc
    (1 - t) * |∑ n ∈ Finset.range N₀, (LPartial p n - LVal p) * t ^ n +
        ∑' k : ℕ, (LPartial p (k + N₀) - LVal p) * t ^ (k + N₀)|
        ≤ (1 - t) * (C + (ε / 2) * ∑' k : ℕ, t ^ k) :=
          mul_le_mul_of_nonneg_left (le_trans htri (add_le_add hhead htail)) h1t.le
    _ = (1 - t) * C + (1 - t) * ((ε / 2) * ∑' k : ℕ, t ^ k) := mul_add _ _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

lemma one_sub_eC_mem_slitPlane {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    1 - eC x ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  rw [Complex.sub_re, Complex.one_re, eC_re]
  have hcos : Real.cos (2 * π * x) < 1 := by
    by_contra h
    have hge : 1 ≤ Real.cos (2 * π * x) := not_lt.mp h
    have heq : Real.cos (2 * π * x) = 1 := le_antisymm (Real.cos_le_one _) hge
    rw [Real.cos_eq_one_iff] at heq
    obtain ⟨k, hk⟩ := heq
    have hkx : (k : ℝ) = x := by nlinarith [Real.pi_pos]
    have hk0 : (0 : ℤ) < k := by exact_mod_cast (show (0 : ℝ) < k by linarith)
    have hk1 : k < 1 := by exact_mod_cast (show (k : ℝ) < 1 by linarith)
    omega
  linarith

lemma neg_log_one_sub_eC_im {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (-Complex.log (1 - eC x)).im = π / 2 - π * x := by
  rw [Complex.neg_im, Complex.log_im]
  set θ : ℝ := π * x
  have hθ0 : 0 < θ := mul_pos Real.pi_pos hx0
  have hθ1 : θ < π := by nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθ1
  have hfac : 1 - eC x = ((2 * Real.sin θ : ℝ) : ℂ) * Complex.exp (((θ - π / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [eC_eq_cos_add_sin_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
    have h2 : 2 * π * x = 2 * θ := by simp only [θ]; ring
    rw [h2, Real.cos_two_mul, Real.sin_two_mul]
    have hsc := Real.sin_sq_add_cos_sq θ
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, sub_zero, add_zero]
      nlinarith
    · simp only [Complex.sub_im, Complex.one_im, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, add_zero, zero_sub]
      ring
  rw [hfac, Complex.arg_real_mul _ (by linarith), Complex.arg_exp_mul_I]
  have hmem : θ - π / 2 ∈ Set.Ioc (-π) (-π + 2 * π) := ⟨by linarith, by linarith⟩
  rw [(toIocMod_eq_self Real.two_pi_pos).mpr hmem]
  simp only [θ]; ring

lemma sineGauss_mul_LVal (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3) :
    sineGauss p * LVal p = -(π / p) * ∑ a ∈ Finset.Icc 1 (p - 1), (a : ℝ) * (legendreSym p a : ℝ) := by
  have hp : p.Prime := Fact.out
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hFt : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      sineGauss p * abelF p t =
        ∑ a ∈ Finset.Icc 1 (p - 1),
          (legendreSym p a : ℝ) * (-Complex.log (1 - (t : ℂ) * eC ((a : ℝ) / p))).im := by
    intro t ⟨ht0, ht1⟩
    rw [abelF, ← tsum_mul_left]
    have hterm : ∀ n : ℕ,
        sineGauss p * ((legendreSym p n : ℝ) / n * t ^ n) =
        ∑ a ∈ Finset.Icc 1 (p - 1),
          (legendreSym p a : ℝ) * (Real.sin (2 * π * (n * a : ℤ) / p) * (t ^ n / n)) := by
      intro n
      have hs := sineGauss_shift p h8 (n : ℤ)
      calc
        sineGauss p * ((legendreSym p n : ℝ) / n * t ^ n)
            = ((legendreSym p n : ℝ) * sineGauss p) * (t ^ n / n) := by ring
        _ = (∑ a ∈ Finset.Icc 1 (p - 1), (legendreSym p a : ℝ) * Real.sin (2 * π * (n * a : ℤ) / p)) * (t ^ n / n) := by
            rw [← hs]
        _ = ∑ a ∈ Finset.Icc 1 (p - 1),
              (legendreSym p a : ℝ) * (Real.sin (2 * π * (n * a : ℤ) / p) * (t ^ n / n)) := by
            rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ => by ring
    simp_rw [hterm]
    have hsum_a : ∀ a ∈ Finset.Icc 1 (p - 1),
        Summable (fun n : ℕ => (legendreSym p a : ℝ) * (Real.sin (2 * π * (n * a : ℤ) / p) * (t ^ n / n))) := by
      intro a _
      refine Summable.of_norm_bounded (g := fun n : ℕ => t ^ n)
        (summable_geometric_of_lt_one ht0.le ht1) fun n => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_of_nonneg (pow_nonneg ht0.le n)]
      by_cases hn : n = 0
      · subst hn; simp
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hchi := abs_legendreSym_le_one p (a : ℤ)
        have hsin : |Real.sin (2 * π * (n * a : ℤ) / p)| ≤ 1 := Real.abs_sin_le_one _
        have hdiv : t ^ n / |(n : ℝ)| ≤ t ^ n := by
          rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
          exact div_le_self (pow_nonneg ht0.le n) hn1
        have hprod : |(legendreSym p a : ℝ)| * |Real.sin (2 * π * (n * a : ℤ) / p)| ≤ 1 := by
          nlinarith [abs_nonneg (legendreSym p a : ℝ), abs_nonneg (Real.sin (2 * π * (n * a : ℤ) / p))]
        nlinarith [pow_nonneg ht0.le n, div_nonneg (pow_nonneg ht0.le n) (abs_nonneg (n : ℝ))]
    rw [Summable.tsum_finsetSum hsum_a]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [tsum_mul_left]
    congr 1
    set z : ℂ := (t : ℂ) * eC ((a : ℝ) / p)
    have hznorm : ‖z‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, norm_eC, mul_one]
      exact ht1
    have hlog := Complex.hasSum_taylorSeries_neg_log hznorm
    have him : ∑' n : ℕ, (z ^ n / (n : ℂ)).im = (-Complex.log (1 - z)).im := by
      simpa only [Complex.imCLM_apply] using (Complex.imCLM.hasSum hlog).tsum_eq
    rw [← him]
    refine tsum_congr fun n => ?_
    simp only [z, mul_pow, ← eC_nat_mul]
    rw [show ((t : ℂ) ^ n * eC ((n : ℕ) * ((a : ℝ) / p))) / (n : ℂ) =
      (((t ^ n / n : ℝ) : ℂ)) * eC ((n : ℕ) * ((a : ℝ) / p)) by push_cast; ring]
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, eC_im]
    rw [mul_comm]; congr 2; push_cast; ring
  have hlim_lhs : Tendsto (fun t => sineGauss p * abelF p t) (𝓝[<] 1) (𝓝 (sineGauss p * LVal p)) :=
    (tendsto_abelF p h8).const_mul (sineGauss p)
  have hlim_rhs : Tendsto
      (fun t : ℝ => ∑ a ∈ Finset.Icc 1 (p - 1),
        (legendreSym p a : ℝ) * (-Complex.log (1 - (t : ℂ) * eC ((a : ℝ) / p))).im)
      (𝓝[<] 1)
      (𝓝 (∑ a ∈ Finset.Icc 1 (p - 1), (legendreSym p a : ℝ) * (π / 2 - π * ((a : ℝ) / p)))) := by
    refine tendsto_finsetSum _ fun a ha => ?_
    simp only [Finset.mem_Icc] at ha
    have ha0 : 0 < (a : ℝ) / p := div_pos (Nat.cast_pos.mpr (by omega)) hp_pos
    have ha1 : (a : ℝ) / p < 1 := by
      rw [div_lt_one hp_pos]; exact_mod_cast (show a < p by omega)
    have hslit := one_sub_eC_mem_slitPlane ha0 ha1
    have hcont : ContinuousAt (fun t : ℝ => (-Complex.log (1 - (t : ℂ) * eC ((a : ℝ) / p))).im) 1 := by
      have h1 : ContinuousAt (fun t : ℝ => (1 : ℂ) - (t : ℂ) * eC ((a : ℝ) / p)) 1 :=
        (continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)).continuousAt
      have h2 : ContinuousAt Complex.log ((1 : ℂ) - ((1 : ℝ) : ℂ) * eC ((a : ℝ) / p)) := by
        simpa only [Complex.ofReal_one, one_mul] using continuousAt_clog hslit
      have h3 : ContinuousAt (fun t : ℝ => Complex.log ((1 : ℂ) - (t : ℂ) * eC ((a : ℝ) / p))) 1 :=
        ContinuousAt.comp (g := Complex.log) (f := fun t : ℝ => (1 : ℂ) - (t : ℂ) * eC ((a : ℝ) / p)) h2 h1
      exact Complex.continuous_im.continuousAt.comp h3.neg
    have htend : Tendsto (fun t : ℝ => (-Complex.log (1 - (t : ℂ) * eC ((a : ℝ) / p))).im)
        (𝓝[<] 1) (𝓝 (π / 2 - π * ((a : ℝ) / p))) := by
      have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
      simpa [one_mul, neg_log_one_sub_eC_im ha0 ha1] using h
    exact htend.const_mul _
  have heq : sineGauss p * LVal p =
      ∑ a ∈ Finset.Icc 1 (p - 1), (legendreSym p a : ℝ) * (π / 2 - π * ((a : ℝ) / p)) := by
    refine tendsto_nhds_unique (hlim_lhs.congr' ?_) hlim_rhs
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hFt t ht
  rw [heq]
  have hsum_split : ∑ a ∈ Finset.Icc 1 (p - 1), (legendreSym p a : ℝ) * (π / 2 - π * ((a : ℝ) / p)) =
      (π / 2) * ∑ a ∈ Finset.Icc 1 (p - 1), (legendreSym p a : ℝ) -
      (π / p) * ∑ a ∈ Finset.Icc 1 (p - 1), (a : ℝ) * (legendreSym p a : ℝ) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => by ring
    · refine Finset.sum_congr rfl fun a _ => by ring
  rw [hsum_split, sum_legendre_Icc_eq_zero p h8, mul_zero, zero_sub]
  ring

theorem csc_sum_eq_two_mul_p_div_pi_mul_LVal (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3) :
    ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), 1 / Real.sin (2 * π * (k : ℝ) ^ 2 / p) =
      2 * (p : ℝ) / π * LVal p := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpi : π ≠ 0 := Real.pi_ne_zero
  rw [trig_csc_eq_cot p h8, cot_sum_eq_gauss_mul_weighted p h8]
  have hG2 := sineGauss_sq p h8
  have hGL := sineGauss_mul_LVal p h8
  have hW : ∑ a ∈ Finset.Icc 1 (p - 1), (a : ℝ) * (legendreSym p a : ℝ) =
      -(p : ℝ) / π * (sineGauss p * LVal p) := by
    field_simp [hp0, hpi] at hGL ⊢
    linarith
  rw [hW]
  have hcalc : -(2 * sineGauss p / (p : ℝ)) * (-(p : ℝ) / π * (sineGauss p * LVal p)) =
      2 * (sineGauss p ^ 2) / π * LVal p := by
    field_simp [hp0, hpi]
  rw [hcalc, hG2]

end OMA.A002143Proof

namespace OMA.A002143Part3

open Finset

/-- Reduced primitive positive definite forms of discriminant `-p`. -/
noncomputable def RedForms (p : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (1 : ℤ) p ×ˢ Finset.Icc (-(p : ℤ)) p ×ˢ Finset.Icc (1 : ℤ) p).filter fun t =>
    t.2.1 ^ 2 - 4 * t.1 * t.2.2 = -(p : ℤ) ∧ |t.2.1| ≤ t.1 ∧ t.1 ≤ t.2.2 ∧
      Int.gcd (Int.gcd t.1 t.2.1) t.2.2 = 1 ∧
      ((|t.2.1| = t.1 ∨ t.1 = t.2.2) → 0 ≤ t.2.1)

/-- Positive definite integer binary quadratic form of discriminant `-p`. -/
def IsPosForm (p : ℕ) (f : ℤ × ℤ × ℤ) : Prop :=
  0 < f.1 ∧ f.2.1 ^ 2 - 4 * f.1 * f.2.2 = -(p : ℤ)

/-- Reduced positive definite form of discriminant `-p`. -/
def IsRedForm (p : ℕ) (f : ℤ × ℤ × ℤ) : Prop :=
  IsPosForm p f ∧ |f.2.1| ≤ f.1 ∧ f.1 ≤ f.2.2 ∧ ((|f.2.1| = f.1 ∨ f.1 = f.2.2) → 0 ≤ f.2.1)

/-- Evaluate `a x^2 + b x y + c y^2`. -/
def evalForm (f : ℤ × ℤ × ℤ) (x y : ℤ) : ℤ := f.1 * x ^ 2 + f.2.1 * x * y + f.2.2 * y ^ 2

/-- Action of `M = [[α, β], [γ, δ]]` on `f = (a, b, c)`. -/
def actForm (f : ℤ × ℤ × ℤ) (α β γ δ : ℤ) : ℤ × ℤ × ℤ :=
  (evalForm f α γ,
   2 * f.1 * α * β + f.2.1 * (α * δ + β * γ) + 2 * f.2.2 * γ * δ,
   evalForm f β δ)

lemma evalForm_actForm (f : ℤ × ℤ × ℤ) (α β γ δ x y : ℤ) :
    evalForm (actForm f α β γ δ) x y = evalForm f (α * x + β * y) (γ * x + δ * y) := by
  simp only [actForm, evalForm]; ring

lemma disc_actForm (f : ℤ × ℤ × ℤ) (α β γ δ : ℤ) (hdet : α * δ - β * γ = 1) :
    (actForm f α β γ δ).2.1 ^ 2 - 4 * (actForm f α β γ δ).1 * (actForm f α β γ δ).2.2 =
      f.2.1 ^ 2 - 4 * f.1 * f.2.2 := by
  simp only [actForm, evalForm]
  have h : (2 * f.1 * α * β + f.2.1 * (α * δ + β * γ) + 2 * f.2.2 * γ * δ) ^ 2 -
      4 * (f.1 * α ^ 2 + f.2.1 * α * γ + f.2.2 * γ ^ 2) *
        (f.1 * β ^ 2 + f.2.1 * β * δ + f.2.2 * δ ^ 2) =
      (f.2.1 ^ 2 - 4 * f.1 * f.2.2) * (α * δ - β * γ) ^ 2 := by ring
  rw [h, hdet, one_pow, mul_one]

lemma actForm_comp (f : ℤ × ℤ × ℤ) (α₁ β₁ γ₁ δ₁ α₂ β₂ γ₂ δ₂ : ℤ) :
    actForm (actForm f α₁ β₁ γ₁ δ₁) α₂ β₂ γ₂ δ₂ =
      actForm f (α₁ * α₂ + β₁ * γ₂) (α₁ * β₂ + β₁ * δ₂)
                (γ₁ * α₂ + δ₁ * γ₂) (γ₁ * β₂ + δ₁ * δ₂) := by
  simp only [actForm, evalForm]; ext <;> ring

lemma actForm_id (f : ℤ × ℤ × ℤ) : actForm f 1 0 0 1 = f := by
  rcases f with ⟨a, b, c⟩; simp [actForm, evalForm]

lemma actForm_neg_id (f : ℤ × ℤ × ℤ) : actForm f (-1) 0 0 (-1) = f := by
  rcases f with ⟨a, b, c⟩; simp [actForm, evalForm]

lemma actForm_inv_cancel (f : ℤ × ℤ × ℤ) (α β γ δ : ℤ) (hdet : α * δ - β * γ = 1) :
    actForm (actForm f α β γ δ) δ (-β) (-γ) α = f := by
  rw [actForm_comp]
  have h1 : α * δ + β * (-γ) = 1 := by linarith
  have h2 : α * (-β) + β * α = 0 := by ring
  have h3 : γ * δ + δ * (-γ) = 0 := by ring
  have h4 : γ * (-β) + δ * α = 1 := by linarith
  rw [h1, h2, h3, h4, actForm_id]

lemma evalForm_pos_of_posForm {p : ℕ} (hp : 0 < p) {f : ℤ × ℤ × ℤ} {x y : ℤ}
    (hf : IsPosForm p f) (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < evalForm f x y := by
  have hid : 4 * f.1 * evalForm f x y = (2 * f.1 * x + f.2.1 * y) ^ 2 + (p : ℤ) * y ^ 2 := by
    simp only [evalForm]; nlinarith [hf.2]
  have hpos : 0 < (2 * f.1 * x + f.2.1 * y) ^ 2 + (p : ℤ) * y ^ 2 := by
    rcases hxy with hx | hy
    · by_cases hy0 : y = 0
      · subst hy0; simp only [mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0)]
        exact sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hf.1.ne') hx)
      · have : 0 < (p : ℤ) * y ^ 2 := mul_pos (Int.natCast_pos.mpr hp) (sq_pos_of_ne_zero hy0)
        nlinarith [sq_nonneg (2 * f.1 * x + f.2.1 * y)]
    · have : 0 < (p : ℤ) * y ^ 2 := mul_pos (Int.natCast_pos.mpr hp) (sq_pos_of_ne_zero hy)
      nlinarith [sq_nonneg (2 * f.1 * x + f.2.1 * y)]
  nlinarith [hf.1]

lemma actForm_isPosForm {p : ℕ} (hp : 0 < p) {f : ℤ × ℤ × ℤ} {α β γ δ : ℤ}
    (hf : IsPosForm p f) (hdet : α * δ - β * γ = 1) :
    IsPosForm p (actForm f α β γ δ) := by
  refine ⟨?_, ?_⟩
  · have hne : α ≠ 0 ∨ γ ≠ 0 := by
      by_contra h
      have h1 : α = 0 := not_not.mp (not_or.mp h).1
      have h2 : γ = 0 := not_not.mp (not_or.mp h).2
      rw [h1, h2] at hdet; norm_num at hdet
    exact evalForm_pos_of_posForm hp hf hne
  · rw [disc_actForm f α β γ δ hdet, hf.2]

lemma isPosForm_c_pos {p : ℕ} (hp : 0 < p) {f : ℤ × ℤ × ℤ} (hf : IsPosForm p f) : 0 < f.2.2 := by
  have : 4 * f.1 * f.2.2 = f.2.1 ^ 2 + (p : ℤ) := by linarith [hf.2]
  have hpz : (0 : ℤ) < p := Int.natCast_pos.mpr hp
  nlinarith [hf.1, sq_nonneg f.2.1]

lemma isPosForm_gcd_eq_one {p : ℕ} (hp : p.Prime) {f : ℤ × ℤ × ℤ} (hf : IsPosForm p f) :
    Int.gcd (Int.gcd f.1 f.2.1) f.2.2 = 1 := by
  set d : ℕ := Int.gcd (Int.gcd f.1 f.2.1) f.2.2
  have hd_ab : (d : ℤ) ∣ Int.gcd f.1 f.2.1 := Int.gcd_dvd_left _ _
  have hd_c : (d : ℤ) ∣ f.2.2 := Int.gcd_dvd_right _ _
  have hd_a : (d : ℤ) ∣ f.1 := dvd_trans hd_ab (Int.gcd_dvd_left _ _)
  have hd_b : (d : ℤ) ∣ f.2.1 := dvd_trans hd_ab (Int.gcd_dvd_right _ _)
  obtain ⟨a', ha'⟩ := hd_a
  obtain ⟨b', hb'⟩ := hd_b
  obtain ⟨c', hc'⟩ := hd_c
  have hdsq : (d : ℤ) ^ 2 ∣ (p : ℤ) := by
    refine ⟨4 * a' * c' - b' ^ 2, ?_⟩
    have := hf.2; rw [ha', hb', hc'] at this; linarith
  have hdsq_nat : d ^ 2 ∣ p := Int.natCast_dvd_natCast.mp (by simpa using hdsq)
  rcases hp.eq_one_or_self_of_dvd d (dvd_trans (dvd_pow_self d (by norm_num)) hdsq_nat) with h1 | hdp
  · exact h1
  · exfalso; rw [hdp] at hdsq_nat
    have := Nat.le_of_dvd hp.pos hdsq_nat
    nlinarith [hp.two_le]

lemma mem_RedForms_iff {p : ℕ} (hp : p.Prime) (f : ℤ × ℤ × ℤ) :
    f ∈ RedForms p ↔ IsRedForm p f := by
  rcases f with ⟨a, b, c⟩
  simp only [RedForms, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, IsRedForm, IsPosForm]
  constructor
  · rintro ⟨⟨⟨ha1, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩, hdisc, hba, hac, _, hbdry⟩
    exact ⟨⟨by omega, hdisc⟩, hba, hac, hbdry⟩
  · rintro ⟨⟨ha0, hdisc⟩, hba, hac, hbdry⟩
    have hc0 : 0 < c := isPosForm_c_pos hp.pos (f := (a, b, c)) ⟨ha0, hdisc⟩
    have hgcd := isPosForm_gcd_eq_one hp (f := (a, b, c)) ⟨ha0, hdisc⟩
    have hba2 : b ^ 2 ≤ a ^ 2 := sq_le_sq.mpr (by rw [abs_of_pos ha0]; exact hba)
    have ha_le : a ≤ p := by
      have : 3 * a ^ 2 ≤ (p : ℤ) := by nlinarith
      nlinarith
    have hb_lo : -(p : ℤ) ≤ b := by have := abs_le.mp hba; omega
    have hb_hi : b ≤ p := by have := abs_le.mp hba; omega
    have hc_le : c ≤ p := by
      have : 4 * a * c = b ^ 2 + (p : ℤ) := by linarith
      have : 3 * a ^ 2 ≤ (p : ℤ) := by nlinarith
      have : 4 * c ≤ 4 * a * c := by nlinarith
      nlinarith
    exact ⟨⟨⟨by omega, ha_le⟩, ⟨hb_lo, hb_hi⟩, ⟨by omega, hc_le⟩⟩, hdisc, hba, hac, hgcd, hbdry⟩

/-- Every positive definite form of discriminant `-p` is `SL₂(ℤ)`-equivalent to a reduced form. -/
theorem exists_redForm_equiv {p : ℕ} (hp : 0 < p) {f : ℤ × ℤ × ℤ} (hf : IsPosForm p f) :
    ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧ IsRedForm p (actForm f α β γ δ) := by
  suffices ∀ (n : ℕ) (f : ℤ × ℤ × ℤ), f.1.toNat = n → IsPosForm p f →
      ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧ IsRedForm p (actForm f α β γ δ) by
    exact this f.1.toNat f rfl hf
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f hfn hf
    rcases f with ⟨a, b, c⟩
    simp only [IsPosForm] at hf
    set k : ℤ := (a - b) / (2 * a)
    set b1 : ℤ := b + 2 * a * k
    have hT_det : (1 : ℤ) * 1 - k * 0 = 1 := by ring
    set f1 := actForm (a, b, c) 1 k 0 1
    have hf1 : IsPosForm p f1 := actForm_isPosForm hp hf hT_det
    set c1 : ℤ := f1.2.2
    have hf1_eq : f1 = (a, b1, c1) := by
      simp only [f1, actForm, evalForm, b1, c1]; ext <;> ring
    have hb1_bounds : -a < b1 ∧ b1 ≤ a := by
      have h2a : 0 < 2 * a := by linarith [hf.1]
      have hrem := Int.emod_nonneg (a - b) h2a.ne'
      have hlt := Int.emod_lt_of_pos (a - b) h2a
      have hdiv := Int.mul_ediv_add_emod (a - b) (2 * a)
      have hb1_eq : b1 = a - (a - b) % (2 * a) := by simp only [b1, k]; linarith
      omega
    have hb1_abs : |b1| ≤ a := abs_le.mpr ⟨by omega, hb1_bounds.2⟩
    have hc1_pos : 0 < c1 := isPosForm_c_pos hp hf1
    by_cases hac : a ≤ c1
    · by_cases hflip : a = c1 ∧ b1 < 0
      · refine ⟨k, -1, 1, 0, by ring, ?_⟩
        have hcomp : actForm (a, b, c) k (-1) 1 0 = actForm f1 0 (-1) 1 0 := by
          simp only [f1, actForm_comp]; congr 1 <;> ring
        have hS : actForm f1 0 (-1) 1 0 = (c1, -b1, a) := by
          rw [hf1_eq]; simp only [actForm, evalForm]; ext <;> ring
        rw [hcomp, hS]
        refine ⟨⟨hc1_pos, ?_⟩, ?_, ?_, ?_⟩
        · dsimp only; have := hf1.2; rw [hf1_eq] at this; linarith
        · dsimp only; rw [abs_neg]; omega
        · dsimp only; omega
        · dsimp only; intro _; omega
      · refine ⟨1, k, 0, 1, hT_det, ?_⟩
        change IsRedForm p f1
        rw [hf1_eq]
        refine ⟨by rwa [← hf1_eq], hb1_abs, hac, ?_⟩
        dsimp only
        rintro (habs | heq)
        · rcases (abs_eq hf.1.le).mp habs with hpos | hneg <;> omega
        · by_contra hlt; exact hflip ⟨heq, not_le.mp hlt⟩
    · have hc1_lt : c1 < a := not_le.mp hac
      have hS_det : (0 : ℤ) * 0 - (-1) * 1 = 1 := by ring
      set f2 := actForm f1 0 (-1) 1 0
      have hf2 : IsPosForm p f2 := actForm_isPosForm hp hf1 hS_det
      have hf2_eq : f2 = (c1, -b1, a) := by
        simp only [f2]; rw [hf1_eq]; simp only [actForm, evalForm]; ext <;> ring
      have hlt_nat : f2.1.toNat < n := by rw [hf2_eq]; simp only; omega
      obtain ⟨α₂, β₂, γ₂, δ₂, hdet₂, hred₂⟩ := ih f2.1.toNat hlt_nat f2 rfl hf2
      refine ⟨k * α₂ + (-1) * γ₂, k * β₂ + (-1) * δ₂, α₂, β₂, ?_, ?_⟩
      · linear_combination hdet₂
      · have hcomp : actForm (a, b, c) (k * α₂ + (-1) * γ₂) (k * β₂ + (-1) * δ₂) α₂ β₂ =
            actForm f2 α₂ β₂ γ₂ δ₂ := by
          simp only [f2, f1, actForm_comp]; congr 1 <;> ring
        rw [hcomp]; exact hred₂

lemma evalForm_ge_c_of_redForm {p : ℕ} {f : ℤ × ℤ × ℤ} {x y : ℤ}
    (hf : IsRedForm p f) (hy : y ≠ 0) : f.2.2 ≤ evalForm f x y := by
  rcases f with ⟨a, b, c⟩
  simp only [IsRedForm, IsPosForm, evalForm] at hf ⊢
  have ha0 : 0 < a := hf.1.1
  have hba : |b| ≤ a := hf.2.1
  have hac : a ≤ c := hf.2.2.1
  have hxy : -(|b| * |x| * |y|) ≤ b * x * y := by
    have h1 := neg_abs_le (b * x * y); rw [abs_mul, abs_mul] at h1; exact h1
  have hba_xy : |b| * |x| * |y| ≤ a * |x| * |y| :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hba (abs_nonneg x)) (abs_nonneg y)
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hy2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  have hx_nn : 0 ≤ |x| := abs_nonneg x
  have hy1 : 1 ≤ |y| := Int.one_le_abs hy
  have hy2_ge : 1 ≤ |y| ^ 2 := by nlinarith
  by_cases hle : |x| ≤ |y|
  · have h1 : a * |x| ^ 2 - a * |x| * |y| + a * |y| ^ 2 ≥ a := by
      have hid : a * |x| ^ 2 - a * |x| * |y| + a * |y| ^ 2 =
          a * (|y| - |x|) ^ 2 + a * |x| * |y| := by ring
      have hsq : 0 ≤ a * (|y| - |x|) ^ 2 := mul_nonneg ha0.le (sq_nonneg _)
      by_cases hx0 : |x| = 0
      · rw [hx0]; nlinarith
      · have hx1 : 1 ≤ |x| := by omega
        have hprod : 1 ≤ |x| * |y| := by nlinarith
        nlinarith
    have h2 : (c - a) * |y| ^ 2 ≥ c - a := by nlinarith
    nlinarith
  · have h1 : |y| ≤ |x| := by omega
    have h2 : 0 ≤ a * |x| * (|x| - |y|) := mul_nonneg (mul_nonneg ha0.le hx_nn) (by omega)
    have h3 : c ≤ c * |y| ^ 2 := by nlinarith
    nlinarith

lemma redForm_equiv_eq_and_unit {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {f f' : ℤ × ℤ × ℤ} {α β γ δ : ℤ}
    (hf : IsRedForm p f) (hf' : IsRedForm p f')
    (hdet : α * δ - β * γ = 1) (hact : actForm f α β γ δ = f') :
    f' = f ∧ ((α = 1 ∧ β = 0 ∧ γ = 0 ∧ δ = 1) ∨ (α = -1 ∧ β = 0 ∧ γ = 0 ∧ δ = -1)) := by
  have hmain : ∀ {f f' : ℤ × ℤ × ℤ} {α β γ δ : ℤ},
      IsRedForm p f → IsRedForm p f' →
      α * δ - β * γ = 1 → actForm f α β γ δ = f' → f'.1 ≤ f.1 →
      f' = f ∧ ((α = 1 ∧ β = 0 ∧ γ = 0 ∧ δ = 1) ∨ (α = -1 ∧ β = 0 ∧ γ = 0 ∧ δ = -1)) := by
    intro f f' α β γ δ hf hf' hdet hact hle
    rcases f with ⟨a, b, c⟩
    rcases f' with ⟨a', b', c'⟩
    have ha'_eq : evalForm (a, b, c) α γ = a' := by
      have := congrArg Prod.fst hact; simpa [actForm] using this
    have hb'_eq : 2 * a * α * β + b * (α * δ + β * γ) + 2 * c * γ * δ = b' := by
      have := congrArg (fun t => t.2.1) hact; simpa [actForm] using this
    have hc'_eq : evalForm (a, b, c) β δ = c' := by
      have := congrArg (fun t => t.2.2) hact; simpa [actForm] using this
    by_cases hγ : γ = 0
    · subst hγ
      have hαδ : α * δ = 1 := by linarith
      have hα_cases : (α = 1 ∧ δ = 1) ∨ (α = -1 ∧ δ = -1) :=
        Int.mul_eq_one_iff_eq_one_or_neg_one.mp hαδ
      have ha_eq : a' = a := by
        rw [← ha'_eq, evalForm]
        rcases hα_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> ring
      have hβ0 : β = 0 := by
        have hb_rel : b' = b + 2 * a * (α * β) := by
          rcases hα_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
        have ha0 : 0 < a := hf.1.1
        have hba : |b| ≤ a := hf.2.1
        have hba' : |b'| ≤ a := by rw [← ha_eq]; exact hf'.2.1
        have hb_gt : -a < b := by
          have := abs_le.mp hba
          by_contra h
          have hneg : b = -a := by omega
          have h0 : 0 ≤ b := hf.2.2.2 (Or.inl (by rw [hneg, abs_neg, abs_of_pos ha0]))
          omega
        have hb'_gt : -a < b' := by
          have := abs_le.mp hba'
          by_contra h
          have hneg : b' = -a := by omega
          have h0 : 0 ≤ b' := hf'.2.2.2 (Or.inl (by rw [hneg, ha_eq, abs_neg, abs_of_pos ha0]))
          omega
        have hdiff : |b' - b| < 2 * a := by
          have := abs_le.mp hba; have := abs_le.mp hba'; rw [abs_lt]; omega
        have hαβ0 : α * β = 0 := by
          have h1 : |2 * a * (α * β)| < 2 * a := by
            have : b' - b = 2 * a * (α * β) := by linarith
            rwa [← this]
          rw [abs_mul, abs_of_pos (by linarith : 0 < 2 * a)] at h1
          have h2 : |α * β| < 1 := by nlinarith
          have h3 : 0 ≤ |α * β| := abs_nonneg _
          exact abs_eq_zero.mp (by omega)
        rcases mul_eq_zero.mp hαβ0 with hα0 | hβ
        · rcases hα_cases with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
        · exact hβ
      subst hβ0
      rcases hα_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [actForm_id] at hact; exact ⟨hact.symm, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
      · rw [actForm_neg_id] at hact; exact ⟨hact.symm, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
    · exfalso
      have hge := evalForm_ge_c_of_redForm (x := α) hf hγ
      dsimp only at hge hle
      have hac : a ≤ c := hf.2.2.1
      have ha_eq_c : a = c := by omega
      have ha'_eq_a : a' = a := by omega
      have ha0 : 0 < a := hf.1.1
      have hb_nn : 0 ≤ b := hf.2.2.2 (Or.inr ha_eq_c)
      have hb_pos : 0 < b := by
        by_contra h
        have hb0 : b = 0 := by omega
        have h4 : 4 * a ^ 2 = (p : ℤ) := by
          have hdisc := hf.1.2; dsimp only at hdisc; rw [hb0, ← ha_eq_c] at hdisc; nlinarith
        have h2nat : 2 ∣ p := Int.natCast_dvd_natCast.mp ⟨2 * a ^ 2, by push_cast; linarith⟩
        rcases hp.eq_one_or_self_of_dvd 2 h2nat with h1 | h2p <;> omega
      have hb_lt : b < a := by
        have hle_b : b ≤ a := (abs_le.mp hf.2.1).2
        by_contra h
        have hba : b = a := by omega
        have h3 : 3 * a ^ 2 = (p : ℤ) := by
          have hdisc := hf.1.2; dsimp only at hdisc; rw [hba, ← ha_eq_c] at hdisc; nlinarith
        have h3nat : 3 ∣ p := Int.natCast_dvd_natCast.mp ⟨a ^ 2, by push_cast; linarith⟩
        rcases hp.eq_one_or_self_of_dvd 3 h3nat with h1 | h3p <;> omega
      have hα0 : α = 0 := by
        by_contra hα_ne
        have hα1 : 1 ≤ |α| := Int.one_le_abs hα_ne
        have hγ1 : 1 ≤ |γ| := Int.one_le_abs hγ
        have hxy : -(b * |α| * |γ|) ≤ b * α * γ := by
          have h1 := neg_abs_le (b * α * γ)
          rw [abs_mul, abs_mul, abs_of_pos hb_pos] at h1; exact h1
        have hstrict : a < evalForm (a, b, c) α γ := by
          simp only [evalForm, ← ha_eq_c]
          have hsq1 : α ^ 2 = |α| ^ 2 := (sq_abs α).symm
          have hsq2 : γ ^ 2 = |γ| ^ 2 := (sq_abs γ).symm
          have hsq_nn : 0 ≤ (|α| - |γ|) ^ 2 := sq_nonneg _
          have hprod : 1 ≤ |α| * |γ| := by nlinarith
          nlinarith
        omega
      subst hα0
      have hβγ : β * γ = -1 := by linarith
      have hb'_rel : b' = -b + 2 * a * (γ * δ) := by
        rw [← ha_eq_c] at hb'_eq
        linear_combination -hb'_eq + b * hβγ
      have hba' : |b'| ≤ a := by rw [← ha'_eq_a]; exact hf'.2.1
      have hγδ0 : γ * δ = 0 := by
        have hbounds := abs_le.mp hba'
        by_cases hpos : 1 ≤ γ * δ
        · have : 2 * a * (γ * δ) ≥ 2 * a := by nlinarith
          omega
        · by_cases hneg : γ * δ ≤ -1
          · have : 2 * a * (γ * δ) ≤ -2 * a := by nlinarith
            omega
          · omega
      have hδ0 : δ = 0 := (mul_eq_zero.mp hγδ0).resolve_left hγ
      subst hδ0
      have hb'_eq_neg : b' = -b := by linarith
      have hc'_eq_a : c' = a := by
        rw [← hc'_eq, evalForm]
        have hβ_sq : β ^ 2 = 1 := by
          rcases Int.mul_eq_neg_one_iff_eq_one_or_neg_one.mp hβγ with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
        rw [hβ_sq]; ring
      have hb'_nn : 0 ≤ b' := hf'.2.2.2 (Or.inr (show a' = c' by omega))
      omega
  by_cases hle : f'.1 ≤ f.1
  · exact hmain hf hf' hdet hact hle
  · have hdet_inv : δ * α - (-β) * (-γ) = 1 := by linarith
    have hact_inv : actForm f' δ (-β) (-γ) α = f := by
      rw [← hact]; exact actForm_inv_cancel f α β γ δ hdet
    obtain ⟨heq, hunit⟩ := hmain hf' hf hdet_inv hact_inv (by omega)
    refine ⟨heq.symm, ?_⟩
    rcases hunit with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩

/-! ### Representation sets and bijection for primitive representations -/

/-- All representations `(f, (x, y))` of `n` by reduced forms of discriminant `-p`. -/
noncomputable def repSet (p n : ℕ) : Finset ((ℤ × ℤ × ℤ) × ℤ × ℤ) :=
  (RedForms p ×ˢ Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ)) ×ˢ
      Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ))).filter fun t =>
    evalForm t.1 t.2.1 t.2.2 = (n : ℤ)

/-- Primitive representations `(f, (x, y))` of `n` (`gcd(x, y) = 1`). -/
noncomputable def primRepSet (p n : ℕ) : Finset ((ℤ × ℤ × ℤ) × ℤ × ℤ) :=
  (repSet p n).filter fun t => Int.gcd t.2.1 t.2.2 = 1

/-- Roots `b ∈ [0, 2n)` of `b^2 + p ≡ 0 (mod 4n)`. -/
def quadRootSet (p n : ℕ) : Finset ℕ :=
  (Finset.range (2 * n)).filter fun b => 4 * n ∣ b ^ 2 + p

lemma rep_coords_bound {p n : ℕ} (hp : p.Prime) {f : ℤ × ℤ × ℤ} {x y : ℤ}
    (hf : IsRedForm p f) (heval : evalForm f x y = (n : ℤ)) :
    |x| ≤ 2 * (n : ℤ) ∧ |y| ≤ 2 * (n : ℤ) := by
  have hmem := (mem_RedForms_iff hp f).mpr hf
  simp only [RedForms, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hmem
  have ha_le : f.1 ≤ p := hmem.1.1.2
  have hc_le : f.2.2 ≤ p := hmem.1.2.2.2
  have hpy : (p : ℤ) * y ^ 2 ≤ 4 * f.1 * (n : ℤ) := by
    have : 4 * f.1 * evalForm f x y = (2 * f.1 * x + f.2.1 * y) ^ 2 + (p : ℤ) * y ^ 2 := by
      simp only [evalForm]; nlinarith [hf.1.2]
    rw [heval] at this; nlinarith [sq_nonneg (2 * f.1 * x + f.2.1 * y)]
  have hpx : (p : ℤ) * x ^ 2 ≤ 4 * f.2.2 * (n : ℤ) := by
    have : 4 * f.2.2 * evalForm f x y = (f.2.1 * x + 2 * f.2.2 * y) ^ 2 + (p : ℤ) * x ^ 2 := by
      simp only [evalForm]; nlinarith [hf.1.2]
    rw [heval] at this; nlinarith [sq_nonneg (f.2.1 * x + 2 * f.2.2 * y)]
  have hpz : (0 : ℤ) < p := Int.natCast_pos.mpr hp.pos
  have hy2 : y ^ 2 ≤ 4 * (n : ℤ) := by nlinarith
  have hx2 : x ^ 2 ≤ 4 * (n : ℤ) := by nlinarith
  constructor
  · have : |x| ^ 2 ≤ (2 * (n : ℤ)) ^ 2 := by
      rw [sq_abs]
      by_cases hn0 : n = 0
      · subst hn0; simp at hx2 ⊢; nlinarith [sq_nonneg x]
      · have hn1 : (1 : ℤ) ≤ n := by omega
        nlinarith
    nlinarith [abs_nonneg x]
  · have : |y| ^ 2 ≤ (2 * (n : ℤ)) ^ 2 := by
      rw [sq_abs]
      by_cases hn0 : n = 0
      · subst hn0; simp at hy2 ⊢; nlinarith [sq_nonneg y]
      · have hn1 : (1 : ℤ) ≤ n := by omega
        nlinarith
    nlinarith [abs_nonneg y]

lemma mem_repSet_iff {p n : ℕ} (hp : p.Prime) (t : (ℤ × ℤ × ℤ) × ℤ × ℤ) :
    t ∈ repSet p n ↔ t.1 ∈ RedForms p ∧ evalForm t.1 t.2.1 t.2.2 = (n : ℤ) := by
  simp only [repSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hf, _, _⟩, hev⟩; exact ⟨hf, hev⟩
  · rintro ⟨hf, hev⟩
    have hb := rep_coords_bound hp ((mem_RedForms_iff hp t.1).mp hf) hev
    exact ⟨⟨hf, abs_le.mp hb.1, abs_le.mp hb.2⟩, hev⟩

theorem primRepSet_card_eq_two_mul_quadRootSet_card {p n : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hn : 0 < n) :
    (primRepSet p n).card = 2 * (quadRootSet p n).card := by
  have hbez : ∀ (x y : ℤ), Int.gcd x y = 1 → ∃ β δ : ℤ, x * δ - β * y = 1 := by
    intro x y h
    refine ⟨-Int.gcdB x y, Int.gcdA x y, ?_⟩
    have := Int.gcd_eq_gcd_ab x y
    rw [h] at this; push_cast at this; linarith
  let φ : ((ℤ × ℤ × ℤ) × ℤ × ℤ) → ℕ := fun t =>
    if h : Int.gcd t.2.1 t.2.2 = 1 then
      let β := (hbez t.2.1 t.2.2 h).choose
      let δ := (hbez t.2.1 t.2.2 h).choose_spec.choose
      (((actForm t.1 t.2.1 β t.2.2 δ).2.1) % (2 * (n : ℤ))).toNat
    else 0
  have hφ_indep : ∀ (f : ℤ × ℤ × ℤ) (x y β₁ δ₁ β₂ δ₂ : ℤ),
      evalForm f x y = (n : ℤ) →
      x * δ₁ - β₁ * y = 1 → x * δ₂ - β₂ * y = 1 →
      (actForm f x β₁ y δ₁).2.1 % (2 * (n : ℤ)) =
        (actForm f x β₂ y δ₂).2.1 % (2 * (n : ℤ)) := by
    intro f x y β₁ δ₁ β₂ δ₂ hev hd1 hd2
    set k : ℤ := δ₁ * β₂ - β₁ * δ₂
    have hβ2 : β₂ = β₁ + k * x := by simp only [k]; linear_combination -β₂ * hd1 + β₁ * hd2
    have hδ2 : δ₂ = δ₁ + k * y := by simp only [k]; linear_combination -δ₂ * hd1 + δ₁ * hd2
    have hshift : (actForm f x β₂ y δ₂).2.1 = (actForm f x β₁ y δ₁).2.1 + 2 * (n : ℤ) * k := by
      rw [hβ2, hδ2]; simp only [actForm, evalForm] at hev ⊢; linear_combination 2 * k * hev
    rw [hshift]; simp [Int.add_mul_emod_self_left]
  have hφ_mem : ∀ t ∈ primRepSet p n, φ t ∈ quadRootSet p n := by
    intro t ht
    simp only [primRepSet, Finset.mem_filter, mem_repSet_iff hp] at ht
    rcases ht with ⟨⟨hf, hev⟩, hgcd⟩
    have hred := (mem_RedForms_iff hp t.1).mp hf
    simp only [φ, dif_pos hgcd]
    set β := (hbez t.2.1 t.2.2 hgcd).choose
    set δ := (hbez t.2.1 t.2.2 hgcd).choose_spec.choose
    have hdet : t.2.1 * δ - β * t.2.2 = 1 := (hbez t.2.1 t.2.2 hgcd).choose_spec.choose_spec
    set f' := actForm t.1 t.2.1 β t.2.2 δ
    have hdisc : f'.2.1 ^ 2 - 4 * (n : ℤ) * f'.2.2 = -(p : ℤ) := by
      have h1 := disc_actForm t.1 t.2.1 β t.2.2 δ hdet
      have hf1 : f'.1 = (n : ℤ) := hev
      change f'.2.1 ^ 2 - 4 * f'.1 * f'.2.2 = t.1.2.1 ^ 2 - 4 * t.1.1 * t.1.2.2 at h1
      rw [hf1, hred.1.2] at h1; exact h1
    set r : ℤ := f'.2.1 % (2 * (n : ℤ))
    have h2n_pos : (0 : ℤ) < 2 * (n : ℤ) := by omega
    have hr_nn : 0 ≤ r := Int.emod_nonneg _ h2n_pos.ne'
    have hr_lt : r < 2 * (n : ℤ) := Int.emod_lt_of_pos _ h2n_pos
    simp only [quadRootSet, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have hcast : ((r.toNat : ℤ)) = r := Int.toNat_of_nonneg hr_nn
    have h4n_dvd : (4 * (n : ℤ)) ∣ r ^ 2 + (p : ℤ) := by
      set q : ℤ := f'.2.1 / (2 * (n : ℤ))
      have hq : f'.2.1 = 2 * (n : ℤ) * q + r := by
        simp only [q, r]; linarith [Int.mul_ediv_add_emod f'.2.1 (2 * (n : ℤ))]
      refine ⟨f'.2.2 - (n : ℤ) * q ^ 2 - q * r, ?_⟩
      rw [hq] at hdisc; linarith
    exact Int.natCast_dvd_natCast.mp (by push_cast; rwa [hcast])
  rw [Finset.card_eq_sum_card_fiberwise hφ_mem]
  have hfiber : ∀ b ∈ quadRootSet p n, ({t ∈ primRepSet p n | φ t = b}).card = 2 := by
    intro b hb
    simp only [quadRootSet, Finset.mem_filter, Finset.mem_range] at hb
    obtain ⟨hb_lt, ⟨c_nat, hc_nat⟩⟩ := hb
    have hpos : IsPosForm p ((n : ℤ), (b : ℤ), (c_nat : ℤ)) := by
      refine ⟨by omega, ?_⟩
      have hz : ((b ^ 2 + p : ℕ) : ℤ) = ((4 * n * c_nat : ℕ) : ℤ) := congrArg Nat.cast hc_nat
      push_cast at hz; linarith
    obtain ⟨α, β, γ, δ, hdet, hred⟩ := exists_redForm_equiv hp.pos hpos
    set f := actForm ((n : ℤ), (b : ℤ), (c_nat : ℤ)) α β γ δ
    have hf_mem : f ∈ RedForms p := (mem_RedForms_iff hp f).mpr hred
    have hinv_det : δ * α - (-β) * (-γ) = 1 := by linarith
    have hinv_act : actForm f δ (-β) (-γ) α = ((n : ℤ), (b : ℤ), (c_nat : ℤ)) :=
      actForm_inv_cancel ((n : ℤ), (b : ℤ), (c_nat : ℤ)) α β γ δ hdet
    set t₁ : (ℤ × ℤ × ℤ) × ℤ × ℤ := (f, (δ, -γ))
    set t₂ : (ℤ × ℤ × ℤ) × ℤ × ℤ := (f, (-δ, γ))
    have ht1_ne_t2 : t₁ ≠ t₂ := by
      intro heq
      have h1 : δ = -δ := congrArg (fun t => t.2.1) heq
      have h2 : -γ = γ := congrArg (fun t => t.2.2) heq
      have hδ0 : δ = 0 := by omega
      have hγ0 : γ = 0 := by omega
      rw [hδ0, hγ0] at hdet; norm_num at hdet
    have hgcd_d_g : Int.gcd δ (-γ) = 1 := by
      have hdvd : ((Int.gcd δ (-γ) : ℕ) : ℤ) ∣ 1 := by
        rw [← hinv_det]
        exact dvd_sub (dvd_mul_of_dvd_left (Int.gcd_dvd_left δ (-γ)) α)
          (dvd_mul_of_dvd_right (Int.gcd_dvd_right δ (-γ)) (-β))
      exact Nat.eq_one_of_dvd_one (Int.natCast_dvd_natCast.mp (by simpa using hdvd))
    have ht1_mem : t₁ ∈ ({t ∈ primRepSet p n | φ t = b} : Finset _) := by
      simp only [Finset.mem_filter, primRepSet, mem_repSet_iff hp]
      have hev1 : evalForm f δ (-γ) = (n : ℤ) := by
        have := congrArg Prod.fst hinv_act; simpa [actForm] using this
      refine ⟨⟨⟨hf_mem, hev1⟩, hgcd_d_g⟩, ?_⟩
      change (if h : Int.gcd δ (-γ) = 1 then _ else 0) = b
      rw [dif_pos hgcd_d_g]
      dsimp only
      have hmod := hφ_indep f δ (-γ)
        ((hbez δ (-γ) hgcd_d_g).choose) ((hbez δ (-γ) hgcd_d_g).choose_spec.choose)
        (-β) α hev1 ((hbez δ (-γ) hgcd_d_g).choose_spec.choose_spec) hinv_det
      rw [hmod, hinv_act]
      have hbmod : (b : ℤ) % (2 * (n : ℤ)) = (b : ℤ) := Int.emod_eq_of_lt (by omega) (by omega)
      rw [hbmod]; omega
    have hgcd_neg : Int.gcd (-δ) γ = 1 := by
      have : Int.gcd (-δ) γ = Int.gcd δ (-γ) := by simp [Int.gcd]
      rw [this]; exact hgcd_d_g
    have ht2_mem : t₂ ∈ ({t ∈ primRepSet p n | φ t = b} : Finset _) := by
      simp only [Finset.mem_filter, primRepSet, mem_repSet_iff hp]
      have hinv_act2 : actForm f (-δ) β γ (-α) = ((n : ℤ), (b : ℤ), (c_nat : ℤ)) := by
        rw [← actForm_neg_id f, actForm_comp]
        convert hinv_act using 1 <;> ring
      have hev2 : evalForm f (-δ) γ = (n : ℤ) := by
        have := congrArg Prod.fst hinv_act2; simpa [actForm] using this
      refine ⟨⟨⟨hf_mem, hev2⟩, hgcd_neg⟩, ?_⟩
      change (if h : Int.gcd (-δ) γ = 1 then _ else 0) = b
      rw [dif_pos hgcd_neg]
      dsimp only
      have hdet2 : (-δ) * (-α) - β * γ = 1 := by linarith
      have hmod := hφ_indep f (-δ) γ
        ((hbez (-δ) γ hgcd_neg).choose) ((hbez (-δ) γ hgcd_neg).choose_spec.choose)
        β (-α) hev2 ((hbez (-δ) γ hgcd_neg).choose_spec.choose_spec) hdet2
      rw [hmod, hinv_act2]
      have hbmod : (b : ℤ) % (2 * (n : ℤ)) = (b : ℤ) := Int.emod_eq_of_lt (by omega) (by omega)
      rw [hbmod]; omega
    have hset_eq : ({t ∈ primRepSet p n | φ t = b} : Finset _) = {t₁, t₂} := by
      ext t
      constructor
      · intro ht
        simp only [Finset.mem_filter, primRepSet, mem_repSet_iff hp] at ht
        rcases ht with ⟨⟨⟨hft_mem, hevt⟩, hgcd_t⟩, hφt⟩
        have hred_t := (mem_RedForms_iff hp t.1).mp hft_mem
        simp only [φ, dif_pos hgcd_t] at hφt
        set βt := (hbez t.2.1 t.2.2 hgcd_t).choose
        set δt := (hbez t.2.1 t.2.2 hgcd_t).choose_spec.choose
        have hdet_t : t.2.1 * δt - βt * t.2.2 = 1 := (hbez t.2.1 t.2.2 hgcd_t).choose_spec.choose_spec
        set ft := actForm t.1 t.2.1 βt t.2.2 δt
        have h2n_pos : (0 : ℤ) < 2 * (n : ℤ) := by omega
        have hft_mod : ft.2.1 % (2 * (n : ℤ)) = (b : ℤ) := by
          have hnn := Int.emod_nonneg ft.2.1 h2n_pos.ne'; omega
        set q : ℤ := ft.2.1 / (2 * (n : ℤ))
        have hft_b : ft.2.1 = (b : ℤ) + 2 * (n : ℤ) * q := by
          simp only [q]; linarith [Int.mul_ediv_add_emod ft.2.1 (2 * (n : ℤ))]
        set β' := βt + (-q) * t.2.1
        set δ' := δt + (-q) * t.2.2
        have hdet' : t.2.1 * δ' - β' * t.2.2 = 1 := by simp only [β', δ']; linear_combination hdet_t
        have hact' : actForm t.1 t.2.1 β' t.2.2 δ' = ((n : ℤ), (b : ℤ), (c_nat : ℤ)) := by
          have hcomp : actForm t.1 t.2.1 β' t.2.2 δ' = actForm ft 1 (-q) 0 1 := by
            simp only [ft, actForm_comp, β', δ']; congr 1 <;> ring
          have h1 : (actForm t.1 t.2.1 β' t.2.2 δ').1 = (n : ℤ) := hevt
          have h2 : (actForm t.1 t.2.1 β' t.2.2 δ').2.1 = (b : ℤ) := by
            rw [hcomp]; simp only [actForm, evalForm]
            have hft1 : ft.1 = (n : ℤ) := hevt
            rw [hft1, hft_b]; ring
          have hdisc' := disc_actForm t.1 t.2.1 β' t.2.2 δ' hdet'
          rw [h1, h2, hred_t.1.2] at hdisc'
          have h3 : (actForm t.1 t.2.1 β' t.2.2 δ').2.2 = (c_nat : ℤ) := by
            have := hpos.2; nlinarith
          exact Prod.ext h1 (Prod.ext h2 h3)
        set M11 := t.2.1 * α + β' * γ
        set M12 := t.2.1 * β + β' * δ
        set M21 := t.2.2 * α + δ' * γ
        set M22 := t.2.2 * β + δ' * δ
        have hMdet : M11 * M22 - M12 * M21 = 1 := by
          simp only [M11, M12, M21, M22]
          have : (t.2.1 * α + β' * γ) * (t.2.2 * β + δ' * δ) -
              (t.2.1 * β + β' * δ) * (t.2.2 * α + δ' * γ) =
              (t.2.1 * δ' - β' * t.2.2) * (α * δ - β * γ) := by ring
          rw [this, hdet', hdet, mul_one]
        have hMact : actForm t.1 M11 M12 M21 M22 = f := by
          simp only [f, ← hact', actForm_comp, M11, M12, M21, M22]
        obtain ⟨hf_eq, hunit⟩ := redForm_equiv_eq_and_unit hp hp3 hred_t hred hMdet hMact
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hunit with ⟨h11, h12, h21, h22⟩ | ⟨h11, h12, h21, h22⟩
        · left
          have hx : t.2.1 = δ := by
            have : M11 * δ - M12 * γ = t.2.1 * (α * δ - β * γ) := by simp only [M11, M12]; ring
            rw [h11, h12, hdet] at this; linarith
          have hy : t.2.2 = -γ := by
            have : M21 * δ - M22 * γ = t.2.2 * (α * δ - β * γ) := by simp only [M21, M22]; ring
            rw [h21, h22, hdet] at this; linarith
          exact Prod.ext hf_eq.symm (Prod.ext hx hy)
        · right
          have hx : t.2.1 = -δ := by
            have : M11 * δ - M12 * γ = t.2.1 * (α * δ - β * γ) := by simp only [M11, M12]; ring
            rw [h11, h12, hdet] at this; linarith
          have hy : t.2.2 = γ := by
            have : M21 * δ - M22 * γ = t.2.2 * (α * δ - β * γ) := by simp only [M21, M22]; ring
            rw [h21, h22, hdet] at this; linarith
          exact Prod.ext hf_eq.symm (Prod.ext hx hy)
      · intro ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact ht1_mem
        · exact ht2_mem
    rw [hset_eq, Finset.card_pair ht1_ne_t2]
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, mul_comm]

/-! ### Part 3b: Grouping by gcd and multiplicativity of quadratic root count -/

lemma repSet_card_eq_sum_primRepSet_card {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    (repSet p n).card =
      ∑ d ∈ n.divisors.filter (fun d => d ^ 2 ∣ n), (primRepSet p (n / d ^ 2)).card := by
  have hmaps : ∀ t ∈ repSet p n, Int.gcd t.2.1 t.2.2 ∈ n.divisors.filter (fun d => d ^ 2 ∣ n) := by
    intro t ht
    rw [mem_repSet_iff hp] at ht
    set d := Int.gcd t.2.1 t.2.2
    have hne : t.2.1 ≠ 0 ∨ t.2.2 ≠ 0 := by
      by_contra h
      have hx : t.2.1 = 0 := not_not.mp (not_or.mp h).1
      have hy : t.2.2 = 0 := not_not.mp (not_or.mp h).2
      have := ht.2; rw [hx, hy] at this; simp [evalForm] at this; omega
    have hd_pos : 0 < d := by
      rcases hne with hx | hy
      · exact Nat.pos_of_ne_zero fun h => hx (Int.gcd_eq_zero_iff.mp h).1
      · exact Nat.pos_of_ne_zero fun h => hy (Int.gcd_eq_zero_iff.mp h).2
    have hdx0 : (d : ℤ) ∣ t.2.1 := Int.gcd_dvd_left t.2.1 t.2.2
    have hdy0 : (d : ℤ) ∣ t.2.2 := Int.gcd_dvd_right t.2.1 t.2.2
    obtain ⟨x', hx'⟩ := hdx0
    obtain ⟨y', hy'⟩ := hdy0
    have hev : (d : ℤ) ^ 2 * evalForm t.1 x' y' = (n : ℤ) := by
      have hscal : (d : ℤ) ^ 2 * evalForm t.1 x' y' = evalForm t.1 ((d : ℤ) * x') ((d : ℤ) * y') := by
        simp only [evalForm]; ring
      rw [hscal, ← hx', ← hy', ht.2]
    have hev_pos : 0 < evalForm t.1 x' y' := by
      have hd2_pos : (0 : ℤ) < (d : ℤ) ^ 2 := sq_pos_of_pos (Int.natCast_pos.mpr hd_pos)
      nlinarith
    have hd2_dvd : d ^ 2 ∣ n := by
      refine ⟨(evalForm t.1 x' y').toNat, ?_⟩
      have hz : ((d ^ 2 * (evalForm t.1 x' y').toNat : ℕ) : ℤ) = (n : ℤ) := by
        push_cast; rw [Int.toNat_of_nonneg hev_pos.le]; exact hev
      exact_mod_cast hz.symm
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_trans (dvd_pow_self d (by norm_num)) hd2_dvd, hn.ne'⟩, hd2_dvd⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Finset.mem_filter, Nat.mem_divisors] at hd
  rcases hd with ⟨⟨_, _⟩, hd2⟩
  have hd_pos : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    rw [hd0] at hd2; simp at hd2; omega
  refine Finset.card_bij (fun t _ => (t.1, (t.2.1 / (d : ℤ), t.2.2 / (d : ℤ)))) ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_filter, mem_repSet_iff hp] at ht
    rcases ht with ⟨⟨hf, hev⟩, hgcd⟩
    simp only [primRepSet, Finset.mem_filter, mem_repSet_iff hp]
    have hdx : (d : ℤ) ∣ t.2.1 := hgcd ▸ Int.gcd_dvd_left t.2.1 t.2.2
    have hdy : (d : ℤ) ∣ t.2.2 := hgcd ▸ Int.gcd_dvd_right t.2.1 t.2.2
    have hmul_x : (d : ℤ) * (t.2.1 / (d : ℤ)) = t.2.1 := Int.mul_ediv_cancel' hdx
    have hmul_y : (d : ℤ) * (t.2.2 / (d : ℤ)) = t.2.2 := Int.mul_ediv_cancel' hdy
    have hev' : evalForm t.1 (t.2.1 / (d : ℤ)) (t.2.2 / (d : ℤ)) = ((n / d ^ 2 : ℕ) : ℤ) := by
      have h1 : (d : ℤ) ^ 2 * evalForm t.1 (t.2.1 / (d : ℤ)) (t.2.2 / (d : ℤ)) = (n : ℤ) := by
        have hscal : (d : ℤ) ^ 2 * evalForm t.1 (t.2.1 / (d : ℤ)) (t.2.2 / (d : ℤ)) =
            evalForm t.1 ((d : ℤ) * (t.2.1 / (d : ℤ))) ((d : ℤ) * (t.2.2 / (d : ℤ))) := by
          simp only [evalForm]; ring
        rw [hscal, hmul_x, hmul_y, hev]
      have h2 : (d : ℤ) ^ 2 * ((n / d ^ 2 : ℕ) : ℤ) = (n : ℤ) := by
        exact_mod_cast Nat.mul_div_cancel' hd2
      have hd2_ne : (d : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (Int.natCast_ne_zero.mpr hd_pos.ne')
      exact mul_left_cancel₀ hd2_ne (h1.trans h2.symm)
    have hgcd' : Int.gcd (t.2.1 / (d : ℤ)) (t.2.2 / (d : ℤ)) = 1 := by
      have h1 : Int.gcd ((d : ℤ) * (t.2.1 / (d : ℤ))) ((d : ℤ) * (t.2.2 / (d : ℤ))) =
          d * Int.gcd (t.2.1 / (d : ℤ)) (t.2.2 / (d : ℤ)) := by
        rw [Int.gcd_mul_left]; simp
      rw [hmul_x, hmul_y, hgcd] at h1
      exact Nat.eq_of_mul_eq_mul_left hd_pos (by omega)
    exact ⟨⟨hf, hev'⟩, hgcd'⟩
  · intro t₁ ht₁ t₂ ht₂ heq
    simp only [Finset.mem_filter] at ht₁ ht₂
    have hdx1 : (d : ℤ) ∣ t₁.2.1 := ht₁.2 ▸ Int.gcd_dvd_left _ _
    have hdy1 : (d : ℤ) ∣ t₁.2.2 := ht₁.2 ▸ Int.gcd_dvd_right _ _
    have hdx2 : (d : ℤ) ∣ t₂.2.1 := ht₂.2 ▸ Int.gcd_dvd_left _ _
    have hdy2 : (d : ℤ) ∣ t₂.2.2 := ht₂.2 ▸ Int.gcd_dvd_right _ _
    have hf_eq : t₁.1 = t₂.1 := (Prod.mk.inj heq).1
    have hxy_eq := Prod.mk.inj (Prod.mk.inj heq).2
    have hx_eq : t₁.2.1 / (d : ℤ) = t₂.2.1 / (d : ℤ) := hxy_eq.1
    have hy_eq : t₁.2.2 / (d : ℤ) = t₂.2.2 / (d : ℤ) := hxy_eq.2
    have hx : t₁.2.1 = t₂.2.1 := by
      rw [← Int.mul_ediv_cancel' hdx1, ← Int.mul_ediv_cancel' hdx2, hx_eq]
    have hy : t₁.2.2 = t₂.2.2 := by
      rw [← Int.mul_ediv_cancel' hdy1, ← Int.mul_ediv_cancel' hdy2, hy_eq]
    exact Prod.ext hf_eq (Prod.ext hx hy)
  · intro u hu
    simp only [primRepSet, Finset.mem_filter, mem_repSet_iff hp] at hu
    rcases hu with ⟨⟨hf, hev⟩, hgcd⟩
    refine ⟨(u.1, ((d : ℤ) * u.2.1, (d : ℤ) * u.2.2)), ?_, ?_⟩
    · simp only [Finset.mem_filter, mem_repSet_iff hp]
      have hev' : evalForm u.1 ((d : ℤ) * u.2.1) ((d : ℤ) * u.2.2) = (n : ℤ) := by
        have hscal : evalForm u.1 ((d : ℤ) * u.2.1) ((d : ℤ) * u.2.2) =
            (d : ℤ) ^ 2 * evalForm u.1 u.2.1 u.2.2 := by simp only [evalForm]; ring
        rw [hscal, hev]
        exact_mod_cast Nat.mul_div_cancel' hd2
      have hgcd' : Int.gcd ((d : ℤ) * u.2.1) ((d : ℤ) * u.2.2) = d := by
        rw [Int.gcd_mul_left, hgcd]; simp
      exact ⟨⟨hf, hev'⟩, hgcd'⟩
    · have hd_ne : (d : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hd_pos.ne'
      simp [Int.mul_ediv_cancel_left _ hd_ne]

/-- Solutions `b ∈ ZMod m` to `b^2 = -p`. -/
def quadRootZMod (p m : ℕ) [NeZero m] : Finset (ZMod m) :=
  Finset.univ.filter fun b : ZMod m => b ^ 2 = -(p : ZMod m)

lemma two_mul_quadRootSet_card (p m : ℕ) (hm : 0 < m) :
    haveI : NeZero (4 * m) := ⟨by omega⟩
    2 * (quadRootSet p m).card = (quadRootZMod p (4 * m)).card := by
  haveI : NeZero (4 * m) := ⟨by omega⟩
  have hmaps : ∀ x ∈ quadRootZMod p (4 * m), x.val % (2 * m) ∈ quadRootSet p m := by
    intro x hx
    simp only [quadRootZMod, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [quadRootSet, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ (by omega), ?_⟩
    have hx_dvd : 4 * m ∣ x.val ^ 2 + p := by
      rw [← ZMod.natCast_eq_zero_iff]; push_cast
      rw [ZMod.natCast_zmod_val, hx, neg_add_cancel]
    have hdiff : x.val = x.val % (2 * m) + (2 * m) * (x.val / (2 * m)) :=
      (Nat.mod_add_div x.val (2 * m)).symm
    set r := x.val % (2 * m)
    set q := x.val / (2 * m)
    have hsq : x.val ^ 2 + p = (r ^ 2 + p) + 4 * m * (r * q + m * q ^ 2) := by
      rw [hdiff]; ring
    rw [hsq] at hx_dvd
    exact (Nat.dvd_add_left ⟨r * q + m * q ^ 2, rfl⟩).mp hx_dvd
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ b ∈ quadRootSet p m,
      ({x ∈ quadRootZMod p (4 * m) | x.val % (2 * m) = b}).card = 2 := by
    intro b hb
    simp only [quadRootSet, Finset.mem_filter, Finset.mem_range] at hb
    rcases hb with ⟨hb_lt, hdvd⟩
    set x₁ : ZMod (4 * m) := (b : ZMod (4 * m))
    set x₂ : ZMod (4 * m) := ((b + 2 * m : ℕ) : ZMod (4 * m))
    have hx1_val : x₁.val = b := by
      simp only [x₁, ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
    have hx2_val : x₂.val = b + 2 * m := by
      simp only [x₂, ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
    have hne : x₁ ≠ x₂ := by
      intro h; have := congrArg ZMod.val h; rw [hx1_val, hx2_val] at this; omega
    have hx1_sq : x₁ ^ 2 = -(p : ZMod (4 * m)) := by
      have h0 : ((b ^ 2 + p : ℕ) : ZMod (4 * m)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      have h1 : x₁ ^ 2 + (p : ZMod (4 * m)) = 0 := by simpa [x₁] using h0
      exact eq_neg_of_add_eq_zero_left h1
    have hx2_sq : x₂ ^ 2 = -(p : ZMod (4 * m)) := by
      have hdvd2 : 4 * m ∣ (b + 2 * m) ^ 2 + p := by
        have : (b + 2 * m) ^ 2 + p = (b ^ 2 + p) + 4 * m * (b + m) := by ring
        rw [this]; exact dvd_add hdvd ⟨b + m, rfl⟩
      have h0 : (((b + 2 * m) ^ 2 + p : ℕ) : ZMod (4 * m)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd2
      have h1 : x₂ ^ 2 + (p : ZMod (4 * m)) = 0 := by simpa [x₂] using h0
      exact eq_neg_of_add_eq_zero_left h1
    have heq : ({x ∈ quadRootZMod p (4 * m) | x.val % (2 * m) = b} : Finset _) = {x₁, x₂} := by
      ext x
      simp only [Finset.mem_filter, quadRootZMod, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hmod⟩
        have hlt : x.val < 4 * m := x.val_lt
        have hq_lt : x.val / (2 * m) < 2 := Nat.div_lt_of_lt_mul (by omega)
        have hdiv := Nat.mod_add_div x.val (2 * m)
        rw [hmod] at hdiv
        have hq : x.val / (2 * m) = 0 ∨ x.val / (2 * m) = 1 := by
          generalize hqv : x.val / (2 * m) = qv at hq_lt ⊢; omega
        rcases hq with hq0 | hq1
        · left; apply ZMod.val_injective; rw [hq0, mul_zero, add_zero] at hdiv; rw [hx1_val, hdiv]
        · right; apply ZMod.val_injective; rw [hq1, mul_one] at hdiv; rw [hx2_val, hdiv]
      · rintro (rfl | rfl)
        · exact ⟨hx1_sq, by rw [hx1_val]; exact Nat.mod_eq_of_lt hb_lt⟩
        · exact ⟨hx2_sq, by rw [hx2_val, Nat.add_mod_right]; exact Nat.mod_eq_of_lt hb_lt⟩
    rw [heq, Finset.card_pair hne]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]

lemma quadRootZMod_mul (p : ℕ) {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂] (hcop : Nat.Coprime m₁ m₂) :
    (quadRootZMod p (m₁ * m₂)).card = (quadRootZMod p m₁).card * (quadRootZMod p m₂).card := by
  let e := ZMod.chineseRemainder hcop
  rw [← Finset.card_product]
  refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
  · intro x hx
    simp only [quadRootZMod, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hx ⊢
    have hmap : e (x ^ 2) = e (-(p : ZMod (m₁ * m₂))) := congrArg e hx
    simp only [map_pow, map_neg, map_natCast] at hmap
    exact ⟨congrArg Prod.fst hmap, congrArg Prod.snd hmap⟩
  · intro x₁ _ x₂ _ h; exact e.injective h
  · intro y hy
    simp only [quadRootZMod, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    simp only [quadRootZMod, Finset.mem_filter, Finset.mem_univ, true_and]
    apply e.injective
    simp only [map_pow, map_neg, map_natCast, e.apply_symm_apply]
    exact Prod.ext hy.1 hy.2

lemma quadRootZMod_four {p : ℕ} (h4 : p % 4 = 3) : (quadRootZMod p 4).card = 2 := by
  have hp4 : (p : ZMod 4) = 3 := by rw [← ZMod.natCast_mod p 4, h4]; rfl
  have hneg : -(p : ZMod 4) = 1 := by rw [hp4]; decide
  have heq : quadRootZMod p 4 = {(1 : ZMod 4), (3 : ZMod 4)} := by
    ext x
    simp only [quadRootZMod, Finset.mem_filter, Finset.mem_univ, true_and, hneg,
      Finset.mem_insert, Finset.mem_singleton]
    revert x; decide
  rw [heq]; decide

lemma quadRootSet_card_of_odd {p m : ℕ} [NeZero m] (h4 : p % 4 = 3) (hodd : Odd m) :
    (quadRootSet p m).card = (quadRootZMod p m).card := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hcop : Nat.Coprime 4 m := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr
      (fun h => by obtain ⟨k, hk⟩ := hodd; omega)).pow_left 2
  have h := two_mul_quadRootSet_card p m hm
  rw [quadRootZMod_mul p hcop, quadRootZMod_four h4] at h
  omega

lemma quadRootZMod_card_congr {p m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂] (h : m₁ = m₂) :
    (quadRootZMod p m₁).card = (quadRootZMod p m₂).card := by
  subst h; rfl

lemma quadRootSet_card_mul {p : ℕ} (h4 : p % 4 = 3) {m₁ m₂ : ℕ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hcop : Nat.Coprime m₁ m₂) :
    (quadRootSet p (m₁ * m₂)).card = (quadRootSet p m₁).card * (quadRootSet p m₂).card := by
  have hodd_one : Odd m₁ ∨ Odd m₂ := by
    by_contra h
    have he1 : 2 ∣ m₁ := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp (not_or.mp h).1)
    have he2 : 2 ∣ m₂ := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp (not_or.mp h).2)
    have hd := Nat.dvd_gcd he1 he2
    rw [hcop.gcd_eq_one] at hd; omega
  have hstep : ∀ {a b : ℕ}, 0 < a → 0 < b → Nat.Coprime a b → Odd b →
      (quadRootSet p (a * b)).card = (quadRootSet p a).card * (quadRootSet p b).card := by
    intro a b ha hb hcab hb_odd
    have : NeZero a := ⟨ha.ne'⟩
    have : NeZero b := ⟨hb.ne'⟩
    have : NeZero (4 * a) := ⟨by omega⟩
    have : NeZero (4 * (a * b)) := ⟨by positivity⟩
    have h4b : Nat.Coprime 4 b := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact (Nat.prime_two.coprime_iff_not_dvd.mpr
        (fun h => by obtain ⟨k, hk⟩ := hb_odd; omega)).pow_left 2
    have h4ab : Nat.Coprime (4 * a) b := h4b.mul_left hcab
    have h1 := two_mul_quadRootSet_card p (a * b) (Nat.mul_pos ha hb)
    have h2 := two_mul_quadRootSet_card p a ha
    have h3 := quadRootSet_card_of_odd (p := p) h4 hb_odd
    have hcongr : (quadRootZMod p (4 * (a * b))).card = (quadRootZMod p ((4 * a) * b)).card :=
      quadRootZMod_card_congr (mul_assoc 4 a b).symm
    have hmul := quadRootZMod_mul p h4ab
    rw [hcongr, hmul, ← h2, ← h3] at h1
    nlinarith
  rcases hodd_one with ho1 | ho2
  · rw [mul_comm, hstep hm₂ hm₁ hcop.symm ho1, mul_comm]
  · exact hstep hm₁ hm₂ hcop ho2

lemma quadRootSet_card_one {p : ℕ} (h4 : p % 4 = 3) : (quadRootSet p 1).card = 1 := by
  have h := quadRootSet_card_of_odd (p := p) (m := 1) h4 odd_one
  rw [h]
  have heq : quadRootZMod p 1 = {0} := by
    ext x
    simp only [quadRootZMod, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun _ => Subsingleton.elim x 0, fun _ => Subsingleton.elim _ _⟩
  rw [heq]; simp

lemma quadRootSet_card_two_pow {p k : ℕ} (h8 : p % 8 = 3) (hk : 1 ≤ k) :
    (quadRootSet p (2 ^ k)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro b hb
  simp only [quadRootSet, Finset.mem_filter] at hb
  have h8dvd : 8 ∣ 4 * 2 ^ k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    refine ⟨2 ^ j, ?_⟩; ring
  have h8b : 8 ∣ b ^ 2 + p := dvd_trans h8dvd hb.2
  have hmod : (b ^ 2 + p) % 8 = 0 := Nat.mod_eq_zero_of_dvd h8b
  have hb8 : (b % 8) ^ 2 % 8 = (b ^ 2) % 8 := by
    rw [sq, sq, ← Nat.mul_mod]
  have h3 : ((b % 8) ^ 2 + 3) % 8 = 0 := by
    rw [Nat.add_mod, hb8, ← h8, Nat.mod_mod, ← Nat.add_mod]; exact hmod
  have hlt : b % 8 < 8 := Nat.mod_lt b (by norm_num)
  interval_cases (b % 8) <;> omega

lemma quadRootSet_card_p {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 3) :
    (quadRootSet p p).card = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [quadRootSet_card_of_odd h4 (Nat.odd_iff.mpr (by omega))]
  have heq : quadRootZMod p p = {(0 : ZMod p)} := by
    ext x
    simp only [quadRootZMod, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      ZMod.natCast_self, neg_zero, sq_eq_zero_iff]
  rw [heq]; simp

lemma quadRootSet_card_p_pow {p k : ℕ} (hp : p.Prime) (h4 : p % 4 = 3) (hk : 2 ≤ k) :
    (quadRootSet p (p ^ k)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro b hb
  simp only [quadRootSet, Finset.mem_filter] at hb
  have hp2 : p ^ 2 ∣ 4 * p ^ k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    refine ⟨4 * p ^ j, ?_⟩; ring
  have hp2_sum : p ^ 2 ∣ b ^ 2 + p := dvd_trans hp2 hb.2
  have hp_sum : p ∣ b ^ 2 + p := dvd_trans (dvd_pow_self p (by norm_num)) hp2_sum
  have hp_b2 : p ∣ b ^ 2 := (Nat.dvd_add_left (dvd_refl p)).mp hp_sum
  have hp_b : p ∣ b := hp.dvd_of_dvd_pow hp_b2
  obtain ⟨r, rfl⟩ := hp_b
  have hp2_b2 : p ^ 2 ∣ (p * r) ^ 2 := ⟨r ^ 2, by ring⟩
  have hp2_p : p ^ 2 ∣ p := (Nat.dvd_add_right hp2_b2).mp hp2_sum
  have := Nat.le_of_dvd hp.pos hp2_p
  nlinarith [hp.two_le]

lemma quadRootZMod_prime_odd {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (h4 : p % 4 = 3) (hq2 : q ≠ 2) (hqp : q ≠ p) :
    ((quadRootZMod p q).card : ℤ) = 1 + legendreSym p q := by
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hrec : legendreSym q (-(p : ℤ)) = legendreSym p q := by
    have hqr := legendreSym.quadratic_reciprocity hq2 hp2 hqp
    rw [show -(p : ℤ) = (-1) * (p : ℤ) by ring, legendreSym.mul, legendreSym.at_neg_one hq2]
    have hq_odd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left hq2
    have h1 : (-1 : ℤ) ^ (q / 2 * (p / 2)) = (-1 : ℤ) ^ (q / 2) := by
      have hp_half : p / 2 % 2 = 1 := by omega
      rw [mul_comm, pow_mul]
      have : ((-1 : ℤ) ^ (p / 2)) = -1 := by
        rw [neg_one_pow_eq_pow_mod_two, hp_half, pow_one]
      rw [this]
    have h2 : ZMod.χ₄ q = (-1 : ℤ) ^ (q / 2) := by
      rw [ZMod.χ₄_nat_eq_if_mod_four]
      have : q % 4 = 1 ∨ q % 4 = 3 := by omega
      rcases this with hq1 | hq3
      · have hq2' : q / 2 % 2 = 0 := by omega
        simp [hq_odd, hq1, neg_one_pow_eq_pow_mod_two, hq2']
      · have hq2' : q / 2 % 2 = 1 := by omega
        simp [hq_odd, hq3, neg_one_pow_eq_pow_mod_two, hq2']
    have hqp_ne0 : ((p : ℤ) : ZMod q) ≠ 0 := by
      intro h
      have hd := (ZMod.natCast_eq_zero_iff p q).mp (by simpa using h)
      rcases hp.eq_one_or_self_of_dvd q hd with h1 | h2
      · exact hq.ne_one h1
      · exact hqp h2
    have hsq : legendreSym q (p : ℤ) * legendreSym q (p : ℤ) = 1 := by
      rcases legendreSym.eq_one_or_neg_one q hqp_ne0 with h | h <;> rw [h] <;> norm_num
    calc
      ZMod.χ₄ q * legendreSym q (p : ℤ)
          = (-1 : ℤ) ^ (q / 2 * (p / 2)) * legendreSym q (p : ℤ) := by rw [h2, h1]
      _ = (legendreSym p (q : ℤ) * legendreSym q (p : ℤ)) * legendreSym q (p : ℤ) := by rw [← hqr]
      _ = legendreSym p (q : ℤ) * (legendreSym q (p : ℤ) * legendreSym q (p : ℤ)) := by ring
      _ = legendreSym p (q : ℤ) := by rw [hsq, mul_one]
  have hne0 : ((-(p : ℤ) : ℤ) : ZMod q) ≠ 0 := by
    intro h
    have hd : q ∣ p := (ZMod.natCast_eq_zero_iff p q).mp (by simpa using neg_eq_zero.mp (by simpa using h))
    rcases hp.eq_one_or_self_of_dvd q hd with h1 | h2
    · exact hq.ne_one h1
    · exact hqp h2
  rw [← hrec]
  rcases legendreSym.eq_one_or_neg_one q hne0 with h1 | hm1
  · rw [h1]
    obtain ⟨u, hu⟩ := (legendreSym.eq_one_iff q hne0).mp h1
    have hu_sq : u ^ 2 = -(p : ZMod q) := by simpa [sq] using hu.symm
    have hu_ne0 : u ≠ 0 := fun h => hne0 (by rw [hu, h, mul_zero])
    have hu_ne_neg : u ≠ -u := by
      intro h
      have h2u : (2 : ZMod q) * u = 0 := by linear_combination h
      have h2ne : (2 : ZMod q) ≠ 0 := by
        intro h2z
        have hd := (ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using h2z)
        exact hq2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hd) hq.two_le)
      exact hu_ne0 ((mul_eq_zero.mp h2u).resolve_left h2ne)
    have heq : quadRootZMod p q = {u, -u} := by
      ext x
      simp only [quadRootZMod, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hx
        have hfac : (x - u) * (x + u) = 0 := by linear_combination hx - hu_sq
        rcases mul_eq_zero.mp hfac with hs | ha
        · left; exact sub_eq_zero.mp hs
        · right; exact eq_neg_of_add_eq_zero_left ha
      · rintro (rfl | rfl)
        · exact hu_sq
        · rw [neg_sq]; exact hu_sq
    rw [heq, Finset.card_pair hu_ne_neg]; norm_num
  · rw [hm1]
    have hempty : quadRootZMod p q = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      simp only [quadRootZMod, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hsq : IsSquare ((-(p : ℤ) : ℤ) : ZMod q) := ⟨x, by simpa [sq] using hx.symm⟩
      have := (legendreSym.eq_one_iff q hne0).mpr hsq
      omega
    rw [hempty]; simp

lemma quadRootZMod_prime_pow_hensel {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) (hk : 1 ≤ k) :
    haveI : NeZero (q ^ (k + 1)) := ⟨pow_ne_zero (k + 1) hq.ne_zero⟩
    haveI : NeZero (q ^ k) := ⟨pow_ne_zero k hq.ne_zero⟩
    (quadRootZMod p (q ^ (k + 1))).card = (quadRootZMod p (q ^ k)).card := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero (q ^ k) := ⟨pow_ne_zero k hq.ne_zero⟩
  haveI : NeZero (q ^ (k + 1)) := ⟨pow_ne_zero (k + 1) hq.ne_zero⟩
  let proj : ZMod (q ^ (k + 1)) →+* ZMod (q ^ k) :=
    ZMod.castHom (pow_dvd_pow q (Nat.le_succ k)) (ZMod (q ^ k))
  have hmaps : ∀ x ∈ quadRootZMod p (q ^ (k + 1)), proj x ∈ quadRootZMod p (q ^ k) := by
    intro x hx
    simp only [quadRootZMod, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have := congrArg proj hx
    simpa [map_pow, map_neg, map_natCast] using this
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ r ∈ quadRootZMod p (q ^ k),
      ({x ∈ quadRootZMod p (q ^ (k + 1)) | proj x = r}).card = 1 := by
    intro r hr
    simp only [quadRootZMod, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    set r0 : ℕ := r.val
    have hr0_lt : r0 < q ^ k := r.val_lt
    have hr0_dvd : q ^ k ∣ r0 ^ 2 + p := by
      rw [← ZMod.natCast_eq_zero_iff]; push_cast
      rw [ZMod.natCast_zmod_val, hr, neg_add_cancel]
    set s : ℕ := (r0 ^ 2 + p) / q ^ k
    have hs_eq : r0 ^ 2 + p = q ^ k * s := (Nat.mul_div_cancel' hr0_dvd).symm
    have h2r0_ne : ((2 * r0 : ℕ) : ZMod q) ≠ 0 := by
      intro h
      have hd := (ZMod.natCast_eq_zero_iff (2 * r0) q).mp h
      rcases hq.dvd_mul.mp hd with h2 | hr0
      · exact hq2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h2) hq.two_le)
      · have hq_sum : q ∣ r0 ^ 2 + p := dvd_trans (dvd_pow_self q (by omega)) hr0_dvd
        have hq_r2 : q ∣ r0 ^ 2 := dvd_trans hr0 (dvd_pow_self r0 (by norm_num))
        have hq_p : q ∣ p := (Nat.dvd_add_right hq_r2).mp hq_sum
        rcases hp.eq_one_or_self_of_dvd q hq_p with h1 | h2
        · exact hq.ne_one h1
        · exact hqp h2
    set tZ : ZMod q := -(s : ZMod q) * ((2 * r0 : ℕ) : ZMod q)⁻¹
    set t0 : ℕ := tZ.val
    have ht0_lt : t0 < q := tZ.val_lt
    set lift0 : ZMod (q ^ (k + 1)) := ((r0 + t0 * q ^ k : ℕ) : ZMod (q ^ (k + 1)))
    have hcond : ∀ t : ℕ, t < q →
        (q ^ (k + 1) ∣ (r0 + t * q ^ k) ^ 2 + p ↔ t = t0) := by
      intro t ht
      have hexp : (r0 + t * q ^ k) ^ 2 + p =
          q ^ k * (s + 2 * r0 * t) + q ^ (k + 1) * (t ^ 2 * q ^ (k - 1)) := by
        have h2k : q ^ (2 * k) = q ^ (k + 1) * q ^ (k - 1) := by
          rw [← pow_add]; congr 1; omega
        calc
          (r0 + t * q ^ k) ^ 2 + p = (r0 ^ 2 + p) + 2 * r0 * t * q ^ k + t ^ 2 * (q ^ k) ^ 2 := by ring
          _ = q ^ k * s + 2 * r0 * t * q ^ k + t ^ 2 * q ^ (2 * k) := by rw [hs_eq, ← pow_mul, mul_comm k 2]
          _ = q ^ k * (s + 2 * r0 * t) + q ^ (k + 1) * (t ^ 2 * q ^ (k - 1)) := by rw [h2k]; ring
      rw [hexp, Nat.dvd_add_left ⟨t ^ 2 * q ^ (k - 1), rfl⟩,
        pow_succ, Nat.mul_dvd_mul_iff_left (pow_pos hq.pos k), ← ZMod.natCast_eq_zero_iff]
      push_cast
      constructor
      · intro h
        have ht_eq : (t : ZMod q) = tZ := by
          have hmul : ((2 * r0 : ℕ) : ZMod q) * (t : ZMod q) = -(s : ZMod q) := by
            push_cast; linear_combination h
          have := congrArg (· * ((2 * r0 : ℕ) : ZMod q)⁻¹) hmul
          simp only [tZ]
          rw [mul_comm (((2 * r0 : ℕ) : ZMod q)), mul_assoc, mul_inv_cancel₀ h2r0_ne, mul_one] at this
          exact this
        have hval : (t : ZMod q).val = tZ.val := congrArg ZMod.val ht_eq
        rwa [ZMod.val_natCast, Nat.mod_eq_of_lt ht] at hval
      · rintro rfl
        have htz : (t0 : ZMod q) = tZ := ZMod.natCast_zmod_val tZ
        rw [htz]; simp only [tZ]
        have : (2 : ZMod q) * (r0 : ZMod q) = ((2 * r0 : ℕ) : ZMod q) := by push_cast; rfl
        rw [this]
        have hmul : ((2 * r0 : ℕ) : ZMod q) * (-(s : ZMod q) * ((2 * r0 : ℕ) : ZMod q)⁻¹) = -(s : ZMod q) := by
          rw [mul_comm (-(s : ZMod q)), ← mul_assoc, mul_inv_cancel₀ h2r0_ne, one_mul]
        rw [hmul, add_neg_cancel]
    have hset : ({x ∈ quadRootZMod p (q ^ (k + 1)) | proj x = r} : Finset _) = {lift0} := by
      ext x
      simp only [Finset.mem_filter, quadRootZMod, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hx_sq, hx_proj⟩
        have hx_lt : x.val < q ^ k * q := by simpa [pow_succ] using x.val_lt
        have hx_mod : x.val % q ^ k = r0 := by
          have h1 : proj (x.val : ZMod (q ^ (k + 1))) = r := by rwa [ZMod.natCast_zmod_val]
          have h2 : (x.val : ZMod (q ^ k)) = r := by simpa [proj] using h1
          have h3 := congrArg ZMod.val h2
          rwa [ZMod.val_natCast] at h3
        set t : ℕ := x.val / q ^ k
        have ht_lt : t < q := Nat.div_lt_of_lt_mul (by linarith)
        have hx_eq : x.val = r0 + t * q ^ k := by
          have := Nat.mod_add_div x.val (q ^ k); rw [hx_mod, mul_comm] at this; exact this.symm
        have hdvd : q ^ (k + 1) ∣ (r0 + t * q ^ k) ^ 2 + p := by
          rw [← hx_eq, ← ZMod.natCast_eq_zero_iff]; push_cast
          rw [ZMod.natCast_zmod_val, hx_sq, neg_add_cancel]
        have ht_eq : t = t0 := (hcond t ht_lt).mp hdvd
        apply ZMod.val_injective
        rw [hx_eq, ht_eq]
        simp only [lift0, ZMod.val_natCast]
        have hlt_lift : r0 + t0 * q ^ k < q ^ (k + 1) := by
          rw [pow_succ]
          have : (t0 + 1) * q ^ k ≤ q * q ^ k := Nat.mul_le_mul_right _ ht0_lt
          nlinarith
        exact (Nat.mod_eq_of_lt hlt_lift).symm
      · rintro rfl
        refine ⟨?_, ?_⟩
        · have hdvd := (hcond t0 ht0_lt).mpr rfl
          have h0 : (((r0 + t0 * q ^ k) ^ 2 + p : ℕ) : ZMod (q ^ (k + 1))) = 0 :=
            (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
          have h1 : lift0 ^ 2 + (p : ZMod (q ^ (k + 1))) = 0 := by simpa [lift0] using h0
          exact eq_neg_of_add_eq_zero_left h1
        · have hproj_nat : proj lift0 = ((r0 + t0 * q ^ k : ℕ) : ZMod (q ^ k)) := by
            simp only [lift0, map_natCast]
          rw [hproj_nat, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero]
          exact ZMod.natCast_zmod_val r
    rw [hset]; simp
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_one]

lemma quadRootSet_card_odd_prime_pow {p q k : ℕ} [Fact p.Prime] [Fact q.Prime]
    (h4 : p % 4 = 3) (hq2 : q ≠ 2) (hqp : q ≠ p) (hk : 1 ≤ k) :
    ((quadRootSet p (q ^ k)).card : ℤ) = 1 + legendreSym p q := by
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  have : NeZero (q ^ k) := ⟨pow_ne_zero k hq.ne_zero⟩
  have hodd : Odd (q ^ k) := Odd.pow (Nat.odd_iff.mpr (hq.eq_two_or_odd.resolve_left hq2))
  rw [quadRootSet_card_of_odd h4 hodd]
  have hind : ∀ j : ℕ, ∀ [NeZero (q ^ (j + 1))],
      ((quadRootZMod p (q ^ (j + 1))).card : ℤ) = 1 + legendreSym p q := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [quadRootZMod_card_congr (pow_one q)]
      exact quadRootZMod_prime_odd (p := p) (q := q) h4 hq2 hqp
    | succ j ih =>
      intro _
      have : NeZero (q ^ (j + 1)) := ⟨pow_ne_zero _ hq.ne_zero⟩
      rw [quadRootZMod_prime_pow_hensel hp hq hq2 hqp (by omega : 1 ≤ j + 1)]
      exact ih
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have : NeZero (q ^ (j + 1)) := ⟨pow_ne_zero _ hq.ne_zero⟩
  rw [quadRootZMod_card_congr (show q ^ (1 + j) = q ^ (j + 1) by rw [add_comm])]
  exact hind j

lemma legendreSym_pow (p : ℕ) [Fact p.Prime] (a : ℤ) (k : ℕ) :
    legendreSym p (a ^ k) = (legendreSym p a) ^ k := by
  induction k with
  | zero => simp [legendreSym.at_one]
  | succ k ih => rw [pow_succ, pow_succ, legendreSym.mul, ih]

lemma sum_neg_one_pow_range (e : ℕ) :
    ∑ i ∈ Finset.range (e + 1), (-1 : ℤ) ^ i = if e % 2 = 0 then 1 else 0 := by
  induction e with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hk : k % 2 = 0
    · have hk1 : (k + 1) % 2 = 1 := by omega
      have hpow : (-1 : ℤ) ^ (k + 1) = -1 := by rw [neg_one_pow_eq_pow_mod_two, hk1, pow_one]
      simp [hk, hk1, hpow]
    · have hk1 : (k + 1) % 2 = 0 := by omega
      have hpow : (-1 : ℤ) ^ (k + 1) = 1 := by rw [neg_one_pow_eq_pow_mod_two, hk1, pow_zero]
      simp [hk, hk1, hpow]

lemma nat_gcd_mul_of_coprime (d a b : ℕ) (hcop : Nat.Coprime a b) :
    Nat.gcd d (a * b) = Nat.gcd d a * Nat.gcd d b := by
  by_cases hd0 : d = 0
  · subst hd0; simp
  have hcg : Nat.Coprime (Nat.gcd d a) (Nat.gcd d b) :=
    (hcop.coprime_dvd_left (Nat.gcd_dvd_right d a)).coprime_dvd_right (Nat.gcd_dvd_right d b)
  apply Nat.dvd_antisymm
  · have ha : Nat.gcd d (a * b) ∣ Nat.gcd (d * b) (a * b) :=
      Nat.dvd_gcd (dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) b) (Nat.gcd_dvd_right _ _)
    rw [Nat.gcd_mul_right] at ha
    have hd1 : Nat.gcd d a ∣ Nat.gcd d (a * b) :=
      Nat.dvd_gcd (Nat.gcd_dvd_left d a) (dvd_mul_of_dvd_left (Nat.gcd_dvd_right d a) b)
    have hda_pos : 0 < Nat.gcd d a := Nat.pos_of_ne_zero fun h => hd0 (Nat.gcd_eq_zero_iff.mp h).1
    have hda : Nat.gcd d (a * b) / Nat.gcd d a ∣ b :=
      (Nat.mul_dvd_mul_iff_left hda_pos).mp (by rwa [Nat.mul_div_cancel' hd1])
    have hdb : Nat.gcd d (a * b) / Nat.gcd d a ∣ Nat.gcd d b :=
      Nat.dvd_gcd (dvd_trans (Nat.div_dvd_of_dvd hd1) (Nat.gcd_dvd_left _ _)) hda
    rw [← Nat.mul_div_cancel' hd1]
    exact Nat.mul_dvd_mul_left _ hdb
  · exact hcg.mul_dvd_of_dvd_of_dvd
      (Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) b))
      (Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) a))

/-- Final Part 3 theorem: `R(n) = 2 * ∑_{d | n} legendreSym p d` for all `n ≥ 1`. -/
theorem repSet_card_eq_two_mul_sum_legendre {p n : ℕ} [Fact p.Prime]
    (hp3 : 3 < p) (h8 : p % 8 = 3) (hn : 0 < n) :
    ((repSet p n).card : ℤ) = 2 * ∑ d ∈ n.divisors, legendreSym p d := by
  have hp : p.Prime := Fact.out
  have h4 : p % 4 = 3 := by omega
  set F : ℕ → ℤ := fun m =>
    ∑ d ∈ m.divisors.filter (fun d => d ^ 2 ∣ m), ((quadRootSet p (m / d ^ 2)).card : ℤ)
  set G : ℕ → ℤ := fun m => ∑ d ∈ m.divisors, legendreSym p d
  have hLHS : ((repSet p n).card : ℤ) = 2 * F n := by
    rw [repSet_card_eq_sum_primRepSet_card hp hn]
    simp only [F, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    have hd_pos : 0 < d := by
      by_contra h
      have hd0 : d = 0 := by omega
      rw [hd0] at hd; simp at hd
    have hq_pos : 0 < n / d ^ 2 := Nat.div_pos (Nat.le_of_dvd hn hd.2) (pow_pos hd_pos 2)
    rw [primRepSet_card_eq_two_mul_quadRootSet_card hp hp3 hq_pos]
    push_cast; rfl
  rw [hLHS]; congr 1
  have hF_mul : ∀ {a b : ℕ}, 0 < a → 0 < b → Nat.Coprime a b → F (a * b) = F a * F b := by
    intro a b ha hb hcop
    dsimp only [F]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_product']
    refine (Finset.sum_bij (fun (xy : ℕ × ℕ) _ => xy.1 * xy.2) ?_ ?_ ?_ ?_).symm
    · intro xy hxy
      simp only [Finset.mem_product, Finset.mem_filter, Nat.mem_divisors] at hxy ⊢
      rcases hxy with ⟨⟨⟨h1, _⟩, h1sq⟩, ⟨⟨h2, _⟩, h2sq⟩⟩
      exact ⟨⟨mul_dvd_mul h1 h2, (Nat.mul_pos ha hb).ne'⟩, by rw [mul_pow]; exact mul_dvd_mul h1sq h2sq⟩
    · intro xy₁ hxy₁ xy₂ hxy₂ heq
      simp only [Finset.mem_product, Finset.mem_filter, Nat.mem_divisors] at hxy₁ hxy₂
      have hc1 : Nat.Coprime xy₁.1 xy₂.2 := hcop.coprime_dvd_left hxy₁.1.1.1 |>.coprime_dvd_right hxy₂.2.1.1
      have hc2 : Nat.Coprime xy₂.1 xy₁.2 := hcop.coprime_dvd_left hxy₂.1.1.1 |>.coprime_dvd_right hxy₁.2.1.1
      have hd1 : xy₁.1 ∣ xy₂.1 := hc1.dvd_of_dvd_mul_right ⟨xy₁.2, heq.symm⟩
      have hd2 : xy₂.1 ∣ xy₁.1 := hc2.dvd_of_dvd_mul_right ⟨xy₂.2, heq⟩
      have h1 : xy₁.1 = xy₂.1 := Nat.dvd_antisymm hd1 hd2
      have hpos1 : 0 < xy₁.1 := Nat.pos_of_dvd_of_pos hxy₁.1.1.1 ha
      have h2 : xy₁.2 = xy₂.2 := Nat.eq_of_mul_eq_mul_left hpos1 (h1 ▸ heq)
      exact Prod.ext h1 h2
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd
      set d₁ := Nat.gcd d a
      set d₂ := Nat.gcd d b
      have hd_eq : d = d₁ * d₂ := by
        have := nat_gcd_mul_of_coprime d a b hcop
        rw [Nat.gcd_eq_left hd.1.1] at this; exact this
      have hd1_sq : d₁ ^ 2 ∣ a := by
        have h1 : d₁ ^ 2 ∣ a * b := dvd_trans (pow_dvd_pow_of_dvd (Nat.gcd_dvd_left d a) 2) hd.2
        have hc : Nat.Coprime (d₁ ^ 2) b := (hcop.coprime_dvd_left (Nat.gcd_dvd_right d a)).pow_left 2
        exact hc.dvd_of_dvd_mul_right h1
      have hd2_sq : d₂ ^ 2 ∣ b := by
        have h2 : d₂ ^ 2 ∣ a * b := dvd_trans (pow_dvd_pow_of_dvd (Nat.gcd_dvd_left d b) 2) hd.2
        have hc : Nat.Coprime (d₂ ^ 2) a := (hcop.symm.coprime_dvd_left (Nat.gcd_dvd_right d b)).pow_left 2
        exact hc.dvd_of_dvd_mul_left h2
      refine ⟨(d₁, d₂), ?_, hd_eq.symm⟩
      simp only [Finset.mem_product, Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨⟨Nat.gcd_dvd_right d a, ha.ne'⟩, hd1_sq⟩, ⟨⟨Nat.gcd_dvd_right d b, hb.ne'⟩, hd2_sq⟩⟩
    · intro xy hxy
      simp only [Finset.mem_product, Finset.mem_filter, Nat.mem_divisors] at hxy
      rcases hxy with ⟨⟨⟨h1, _⟩, h1sq⟩, ⟨⟨h2, _⟩, h2sq⟩⟩
      have hdiv_eq : a * b / (xy.1 * xy.2) ^ 2 = (a / xy.1 ^ 2) * (b / xy.2 ^ 2) := by
        rw [mul_pow]
        have h1pos : 0 < xy.1 ^ 2 := pow_pos (Nat.pos_of_dvd_of_pos h1 ha) 2
        have h2pos : 0 < xy.2 ^ 2 := pow_pos (Nat.pos_of_dvd_of_pos h2 hb) 2
        exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos h1pos h2pos) (by
          rw [Nat.mul_div_cancel' (mul_dvd_mul h1sq h2sq)]
          calc
            a * b = (xy.1 ^ 2 * (a / xy.1 ^ 2)) * (xy.2 ^ 2 * (b / xy.2 ^ 2)) := by
              rw [Nat.mul_div_cancel' h1sq, Nat.mul_div_cancel' h2sq]
            _ = xy.1 ^ 2 * xy.2 ^ 2 * (a / xy.1 ^ 2 * (b / xy.2 ^ 2)) := by ring)
      have hqa : 0 < a / xy.1 ^ 2 := Nat.div_pos (Nat.le_of_dvd ha h1sq) (pow_pos (Nat.pos_of_dvd_of_pos h1 ha) 2)
      have hqb : 0 < b / xy.2 ^ 2 := Nat.div_pos (Nat.le_of_dvd hb h2sq) (pow_pos (Nat.pos_of_dvd_of_pos h2 hb) 2)
      have hqcop : Nat.Coprime (a / xy.1 ^ 2) (b / xy.2 ^ 2) :=
        hcop.coprime_dvd_left (Nat.div_dvd_of_dvd h1sq) |>.coprime_dvd_right (Nat.div_dvd_of_dvd h2sq)
      rw [hdiv_eq, quadRootSet_card_mul h4 hqa hqb hqcop]; push_cast; rfl
  have hG_mul : ∀ {a b : ℕ}, 0 < a → 0 < b → Nat.Coprime a b → G (a * b) = G a * G b := by
    intro a b ha hb hcop
    dsimp only [G]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_product']
    refine (Finset.sum_bij (fun (xy : ℕ × ℕ) _ => xy.1 * xy.2) ?_ ?_ ?_ ?_).symm
    · intro xy hxy
      simp only [Finset.mem_product, Nat.mem_divisors] at hxy ⊢
      exact ⟨mul_dvd_mul hxy.1.1 hxy.2.1, (Nat.mul_pos ha hb).ne'⟩
    · intro xy₁ hxy₁ xy₂ hxy₂ heq
      simp only [Finset.mem_product, Nat.mem_divisors] at hxy₁ hxy₂
      have hc1 : Nat.Coprime xy₁.1 xy₂.2 := hcop.coprime_dvd_left hxy₁.1.1 |>.coprime_dvd_right hxy₂.2.1
      have hc2 : Nat.Coprime xy₂.1 xy₁.2 := hcop.coprime_dvd_left hxy₂.1.1 |>.coprime_dvd_right hxy₁.2.1
      have h1 : xy₁.1 = xy₂.1 := Nat.dvd_antisymm
        (hc1.dvd_of_dvd_mul_right ⟨xy₁.2, heq.symm⟩) (hc2.dvd_of_dvd_mul_right ⟨xy₂.2, heq⟩)
      exact Prod.ext h1 (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_dvd_of_pos hxy₁.1.1 ha) (h1 ▸ heq))
    · intro d hd
      simp only [Nat.mem_divisors] at hd
      refine ⟨(Nat.gcd d a, Nat.gcd d b), ?_, ?_⟩
      · simp only [Finset.mem_product, Nat.mem_divisors]
        exact ⟨⟨Nat.gcd_dvd_right d a, ha.ne'⟩, ⟨Nat.gcd_dvd_right d b, hb.ne'⟩⟩
      · have := nat_gcd_mul_of_coprime d a b hcop
        rw [Nat.gcd_eq_left hd.1] at this; exact this.symm
    · intro xy _
      rw [Nat.cast_mul, legendreSym.mul]
  have hFG_pp : ∀ (q e : ℕ), q.Prime → F (q ^ e) = G (q ^ e) := by
    intro q e hq
    haveI : Fact q.Prime := ⟨hq⟩
    have hG_val : G (q ^ e) = ∑ i ∈ Finset.range (e + 1), (legendreSym p q) ^ i := by
      simp only [G, Nat.divisors_prime_pow hq, Finset.sum_map]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Function.Embedding.coeFn_mk, Nat.cast_pow, legendreSym_pow]
    have hF_val : F (q ^ e) = ∑ j ∈ Finset.range (e / 2 + 1), ((quadRootSet p (q ^ (e - 2 * j))).card : ℤ) := by
      simp only [F]
      refine (Finset.sum_bij (fun j _ => q ^ j) ?_ ?_ ?_ ?_).symm
      · intro j hj
        simp only [Finset.mem_range, Finset.mem_filter, Nat.mem_divisors] at hj ⊢
        refine ⟨⟨pow_dvd_pow q (by omega), (pow_pos hq.pos e).ne'⟩, ?_⟩
        rw [← pow_mul, mul_comm]; exact pow_dvd_pow q (by omega)
      · intro j₁ _ j₂ _ heq
        exact Nat.pow_right_injective hq.two_le heq
      · intro d hd
        simp only [Finset.mem_filter, Nat.mem_divisors] at hd
        obtain ⟨j, _, rfl⟩ := (Nat.dvd_prime_pow hq).mp hd.1.1
        have h2j : 2 * j ≤ e := by
          have hd2 : q ^ (2 * j) ∣ q ^ e := by
            have := hd.2; rw [← pow_mul, mul_comm] at this; exact this
          exact (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp hd2
        exact ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
      · intro j hj
        simp only [Finset.mem_range] at hj
        have hdiv : q ^ e / (q ^ j) ^ 2 = q ^ (e - 2 * j) := by
          rw [← pow_mul, mul_comm j 2]; exact Nat.pow_div (by omega) hq.pos
        rw [hdiv]
    rw [hF_val, hG_val]
    by_cases hq2 : q = 2
    · subst hq2
      have hleg2 : legendreSym p ((2 : ℕ) : ℤ) = -1 := by
        have hp2 : p ≠ 2 := by omega
        have hodd : p % 2 = 1 := by omega
        rw [Nat.cast_ofNat, legendreSym.at_two hp2, ZMod.χ₈_nat_eq_if_mod_eight]; simp [h8, hodd]
      rw [hleg2, sum_neg_one_pow_range]
      split_ifs with hev
      · rw [Finset.sum_eq_single (e / 2)]
        · rw [show e - 2 * (e / 2) = 0 by omega, pow_zero, quadRootSet_card_one h4]; simp
        · intro j hj hne
          simp only [Finset.mem_range] at hj
          rw [quadRootSet_card_two_pow h8 (by omega)]; simp
        · intro h; simp at h
      · refine Finset.sum_eq_zero fun j hj => ?_
        simp only [Finset.mem_range] at hj
        rw [quadRootSet_card_two_pow h8 (by omega)]; simp
    · by_cases hqp : q = p
      · rcases hqp with rfl
        have hlegp : legendreSym q (q : ℤ) = 0 := by rw [legendreSym.eq_zero_iff]; simp
        rw [hlegp]
        have hRHS' : ∑ i ∈ Finset.range (e + 1), (0 : ℤ) ^ i = 1 := by
          rw [Finset.sum_eq_single 0]
          · simp
          · intro i _ hi; simp [zero_pow hi]
          · intro h; simp at h
        have hLHS' : ∑ j ∈ Finset.range (e / 2 + 1), ((quadRootSet q (q ^ (e - 2 * j))).card : ℤ) = 1 := by
          rw [Finset.sum_eq_single (e / 2)]
          · by_cases hev : e % 2 = 0
            · rw [show e - 2 * (e / 2) = 0 by omega, pow_zero, quadRootSet_card_one h4]; simp
            · rw [show e - 2 * (e / 2) = 1 by omega, pow_one, quadRootSet_card_p hq h4]; simp
          · intro j hj hne
            simp only [Finset.mem_range] at hj
            rw [quadRootSet_card_p_pow hq h4 (by omega)]; simp
          · intro h; simp at h
        rw [hLHS', hRHS']
      · have hq_ne0 : ((q : ℤ) : ZMod p) ≠ 0 := by
          intro h
          have hd := (ZMod.natCast_eq_zero_iff q p).mp (by simpa using h)
          rcases hq.eq_one_or_self_of_dvd p hd with h1 | h2
          · exact hp.ne_one h1
          · exact hqp h2.symm
        rcases legendreSym.eq_one_or_neg_one p hq_ne0 with h1 | hm1
        · rw [h1]
          have hRHS' : ∑ i ∈ Finset.range (e + 1), (1 : ℤ) ^ i = (e + 1 : ℤ) := by simp
          rw [hRHS']
          by_cases hev : e % 2 = 0
          · rw [Finset.range_add_one, Finset.sum_insert Finset.notMem_range_self,
              show e - 2 * (e / 2) = 0 by omega, pow_zero, quadRootSet_card_one h4]
            have hrest : ∑ j ∈ Finset.range (e / 2), ((quadRootSet p (q ^ (e - 2 * j))).card : ℤ) =
                ∑ _j ∈ Finset.range (e / 2), (2 : ℤ) := by
              refine Finset.sum_congr rfl fun j hj => ?_
              simp only [Finset.mem_range] at hj
              rw [quadRootSet_card_odd_prime_pow h4 hq2 hqp (by omega), h1]; norm_num
            rw [hrest, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; omega
          · have hrest : ∑ j ∈ Finset.range (e / 2 + 1), ((quadRootSet p (q ^ (e - 2 * j))).card : ℤ) =
                ∑ _j ∈ Finset.range (e / 2 + 1), (2 : ℤ) := by
              refine Finset.sum_congr rfl fun j hj => ?_
              simp only [Finset.mem_range] at hj
              rw [quadRootSet_card_odd_prime_pow h4 hq2 hqp (by omega), h1]; norm_num
            rw [hrest, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; omega
        · rw [hm1, sum_neg_one_pow_range]
          split_ifs with hev
          · rw [Finset.sum_eq_single (e / 2)]
            · rw [show e - 2 * (e / 2) = 0 by omega, pow_zero, quadRootSet_card_one h4]; simp
            · intro j hj hne
              simp only [Finset.mem_range] at hj
              rw [quadRootSet_card_odd_prime_pow h4 hq2 hqp (by omega), hm1]; norm_num
            · intro h; simp at h
          · refine Finset.sum_eq_zero fun j hj => ?_
            simp only [Finset.mem_range] at hj
            rw [quadRootSet_card_odd_prime_pow h4 hq2 hqp (by omega), hm1]; norm_num
  clear hLHS
  have hmain : ∀ k : ℕ, 0 < k → F k = G k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases hk1 : k = 1
      · subst hk1; simpa using hFG_pp 2 0 Nat.prime_two
      · set q := k.minFac
        have hq : q.Prime := Nat.minFac_prime hk1
        set e := k.factorization q
        have he_pos : 0 < e := Nat.Prime.factorization_pos_of_dvd hq hk.ne' (Nat.minFac_dvd k)
        have hqe_dvd : q ^ e ∣ k := Nat.ordProj_dvd k q
        set m := k / q ^ e
        have hkm : k = q ^ e * m := (Nat.mul_div_cancel' hqe_dvd).symm
        have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hk hqe_dvd) (pow_pos hq.pos e)
        have hcop : Nat.Coprime (q ^ e) m := by
          refine Nat.Coprime.pow_left e (hq.coprime_iff_not_dvd.mpr fun hqm => ?_)
          have hqe1 : q ^ (e + 1) ∣ k := by
            obtain ⟨r, hr⟩ := hqm; refine ⟨r, ?_⟩; rw [hkm, hr, pow_succ]; ring
          have hle := (hq.pow_dvd_iff_le_factorization hk.ne').mp hqe1
          omega
        have hm_lt : m < k := by
          have hqe_gt : 1 < q ^ e := one_lt_pow₀ hq.one_lt he_pos.ne'
          nlinarith
        rw [hkm, hF_mul (pow_pos hq.pos e) hm_pos hcop, hG_mul (pow_pos hq.pos e) hm_pos hcop,
          hFG_pp q e hq, ih m hm_lt hm_pos]
  exact hmain n hn

end OMA.A002143Part3

open scoped Real BigOperators
open Filter Topology

namespace OMA.A002143Part4

/-! ### Step 4A: Hyperbola asymptotic for ∑_{n=1}^X R(n) / X → 2 * L(1, χ) -/

lemma floor_div_approx (X d : ℕ) (hd : 0 < d) :
    |(((X / d : ℕ) : ℝ)) - (X : ℝ) / (d : ℝ)| ≤ 1 := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have h1 : (X / d : ℕ) * d ≤ X := Nat.div_mul_le_self X d
  have h2 : X < ((X / d : ℕ) + 1) * d := by
    have := Nat.lt_div_mul_add (a := X) hd
    linarith
  have h1R : ((X / d : ℕ) : ℝ) * (d : ℝ) ≤ (X : ℝ) := by exact_mod_cast h1
  have h2R : (X : ℝ) < (((X / d : ℕ) : ℝ) + 1) * (d : ℝ) := by exact_mod_cast h2
  have hle1 : ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / (d : ℝ) := (le_div_iff₀ hd_pos).mpr h1R
  have hlt2 : (X : ℝ) / (d : ℝ) < ((X / d : ℕ) : ℝ) + 1 := (div_lt_iff₀ hd_pos).mpr h2R
  rw [abs_le]
  constructor <;> linarith

lemma sum_Icc_sum_divisors_eq (X : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, f d =
      ∑ d ∈ Finset.Icc 1 X, f d * ((X / d : ℕ) : ℝ) := by
  calc
    ∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, f d
        = ∑ n ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 X, if d ∣ n then f d else 0 := by
          refine Finset.sum_congr rfl fun n hn => ?_
          simp only [Finset.mem_Icc] at hn
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext d
          simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
          constructor
          · rintro ⟨hdn, _⟩
            exact ⟨⟨Nat.pos_of_dvd_of_pos hdn hn.1, le_trans (Nat.le_of_dvd hn.1 hdn) hn.2⟩, hdn⟩
          · rintro ⟨_, hdn⟩
            exact ⟨hdn, by omega⟩
    _ = ∑ d ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X, if d ∣ n then f d else 0 :=
          Finset.sum_comm
    _ = ∑ d ∈ Finset.Icc 1 X, f d * ((X / d : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun d hd => ?_
          simp only [Finset.mem_Icc] at hd
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
          congr 1
          have hcard : (Finset.filter (fun n => d ∣ n) (Finset.Icc 1 X)).card = X / d := by
            have hIcc : (Finset.Icc 1 (X / d)).card = X / d := by rw [Nat.card_Icc, Nat.add_sub_cancel]
            rw [← hIcc]
            refine Finset.card_bij (fun n _ => n / d) ?_ ?_ ?_
            · intro n hn
              simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
              exact ⟨Nat.div_pos (Nat.le_of_dvd hn.1.1 hn.2) hd.1, Nat.div_le_div_right hn.1.2⟩
            · intro n₁ hn₁ n₂ hn₂ heq
              simp only [Finset.mem_filter] at hn₁ hn₂
              rw [← Nat.mul_div_cancel' hn₁.2, ← Nat.mul_div_cancel' hn₂.2, heq]
            · intro k hk
              simp only [Finset.mem_Icc] at hk
              refine ⟨d * k, ?_, Nat.mul_div_cancel_left k hd.1⟩
              simp only [Finset.mem_filter, Finset.mem_Icc]
              exact ⟨⟨by nlinarith [hd.1, hk.1],
                le_trans (Nat.mul_le_mul_left d hk.2) (Nat.mul_div_le X d)⟩, dvd_mul_right d k⟩
          rw [hcard]

lemma tendsto_hyperbola_sum {p : ℕ} [Fact p.Prime]
    (LVal : ℝ)
    (hL : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (legendreSym p n : ℝ) / (n : ℝ)) atTop (𝓝 LVal))
    (habel : ∀ {M N : ℕ} {f : ℕ → ℝ}, M < N →
      (∀ n, M + 1 ≤ n → n ≤ N → 0 ≤ f n) →
      (∀ n, M + 1 ≤ n → n + 1 ≤ N → f (n + 1) ≤ f n) →
      |∑ n ∈ Finset.Icc (M + 1) N, (legendreSym p n : ℝ) * f n| ≤ 2 * (p : ℝ) * f (M + 1)) :
    Tendsto (fun X : ℕ =>
      (∑ n ∈ Finset.Icc 1 X, (2 : ℝ) * ∑ d ∈ n.divisors, (legendreSym p d : ℝ)) / (X : ℝ))
      atTop (𝓝 (2 * LVal)) := by
  have hsqrt_tendsto : Tendsto (fun X : ℕ => Nat.sqrt X) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b * b, fun n hn => ?_⟩
    exact Nat.le_sqrt.mpr hn
  have hL_sqrt : Tendsto (fun X : ℕ =>
      ∑ d ∈ Finset.Icc 1 (Nat.sqrt X), (legendreSym p d : ℝ) / (d : ℝ)) atTop (𝓝 LVal) :=
    hL.comp hsqrt_tendsto
  have hdiff_zero : Tendsto (fun X : ℕ =>
      (∑ d ∈ Finset.Icc 1 X, (legendreSym p d : ℝ) * ((X / d : ℕ) : ℝ)) / (X : ℝ) -
      ∑ d ∈ Finset.Icc 1 (Nat.sqrt X), (legendreSym p d : ℝ) / (d : ℝ)) atTop (𝓝 0) := by
    have hbound : ∀ X : ℕ, 1 ≤ X →
        |(∑ d ∈ Finset.Icc 1 X, (legendreSym p d : ℝ) * ((X / d : ℕ) : ℝ)) / (X : ℝ) -
          ∑ d ∈ Finset.Icc 1 (Nat.sqrt X), (legendreSym p d : ℝ) / (d : ℝ)| ≤
        (2 * (p : ℝ) + 1) / Real.sqrt (X : ℝ) := by
      intro X hX
      set M := Nat.sqrt X
      have hMX : M ≤ X := Nat.sqrt_le_self X
      have hM_le_sqrt : (M : ℝ) ≤ Real.sqrt (X : ℝ) := by
        rw [Real.le_sqrt (Nat.cast_nonneg M) (Nat.cast_nonneg X), sq]
        exact_mod_cast Nat.sqrt_le X
      have hX_pos : (0 : ℝ) < (X : ℝ) := Nat.cast_pos.mpr hX
      have hsqrt_pos : (0 : ℝ) < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hX_pos
      have hsplit : ∑ d ∈ Finset.Icc 1 X, (legendreSym p d : ℝ) * ((X / d : ℕ) : ℝ) =
          (∑ d ∈ Finset.Icc 1 M, (legendreSym p d : ℝ) * ((X / d : ℕ) : ℝ)) +
          (∑ d ∈ Finset.Icc (M + 1) X, (legendreSym p d : ℝ) * ((X / d : ℕ) : ℝ)) := by
        have hunion : Finset.Icc 1 X = Finset.Icc 1 M ∪ Finset.Icc (M + 1) X := by
          ext d; simp only [Finset.mem_Icc, Finset.mem_union]; omega
        rw [hunion, Finset.sum_union]
        rw [Finset.disjoint_left]
        intro d hd1 hd2; simp only [Finset.mem_Icc] at hd1 hd2; omega
      have hhead : |∑ d ∈ Finset.Icc 1 M, (legendreSym p d : ℝ) * ((X / d : ℕ) : ℝ) -
          (X : ℝ) * ∑ d ∈ Finset.Icc 1 M, (legendreSym p d : ℝ) / (d : ℝ)| ≤ (M : ℝ) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        calc
          |∑ d ∈ Finset.Icc 1 M, ((legendreSym p d : ℝ) * ((X / d : ℕ) : ℝ) -
              (X : ℝ) * ((legendreSym p d : ℝ) / (d : ℝ)))|
              ≤ ∑ d ∈ Finset.Icc 1 M, |(legendreSym p d : ℝ) * ((X / d : ℕ) : ℝ) -
                  (X : ℝ) * ((legendreSym p d : ℝ) / (d : ℝ))| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _d ∈ Finset.Icc 1 M, (1 : ℝ) := by
              refine Finset.sum_le_sum fun d hd => ?_
              simp only [Finset.mem_Icc] at hd
              have hfac : (legendreSym p d : ℝ) * ((X / d : ℕ) : ℝ) -
                  (X : ℝ) * ((legendreSym p d : ℝ) / (d : ℝ)) =
                  (legendreSym p d : ℝ) * (((X / d : ℕ) : ℝ) - (X : ℝ) / (d : ℝ)) := by ring
              rw [hfac, abs_mul]
              have hleg : |(legendreSym p d : ℝ)| ≤ 1 := by
                by_cases h0 : ((d : ℤ) : ZMod p) = 0
                · rw [(legendreSym.eq_zero_iff p d).mpr h0]; norm_num
                · rcases legendreSym.eq_one_or_neg_one p h0 with h | h <;> rw [h] <;> norm_num
              have hfl := floor_div_approx X d hd.1
              nlinarith [abs_nonneg (legendreSym p d : ℝ), abs_nonneg (((X / d : ℕ) : ℝ) - (X : ℝ) / (d : ℝ))]
          _ = (M : ℝ) := by simp
      have htail : |∑ d ∈ Finset.Icc (M + 1) X, (legendreSym p d : ℝ) * ((X / d : ℕ) : ℝ)| ≤
          2 * (p : ℝ) * Real.sqrt (X : ℝ) := by
        by_cases hlt : M < X
        · have hb := habel hlt (f := fun d => ((X / d : ℕ) : ℝ))
            (fun d _ _ => Nat.cast_nonneg _)
            (fun d _ _ => Nat.cast_le.mpr (Nat.div_le_div_left (by omega) (by omega)))
          have hdiv_le : ((X / (M + 1) : ℕ) : ℝ) ≤ Real.sqrt (X : ℝ) := by
            have hM1 : Real.sqrt (X : ℝ) < (M + 1 : ℝ) := by
              rw [Real.sqrt_lt' (by positivity), sq]
              have := Nat.lt_succ_sqrt X
              exact_mod_cast this
            have hle1 : ((X / (M + 1) : ℕ) : ℝ) ≤ (X : ℝ) / (M + 1 : ℝ) := by
              rw [le_div_iff₀ (by positivity)]
              exact_mod_cast Nat.div_mul_le_self X (M + 1)
            have hle2 : (X : ℝ) / (M + 1 : ℝ) ≤ Real.sqrt (X : ℝ) := by
              rw [div_le_iff₀ (by positivity)]
              calc
                (X : ℝ) = Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) := (Real.mul_self_sqrt (Nat.cast_nonneg X)).symm
                _ ≤ Real.sqrt (X : ℝ) * (M + 1 : ℝ) := by nlinarith
            exact le_trans hle1 hle2
          have hp_nn : (0 : ℝ) ≤ 2 * (p : ℝ) := by positivity
          exact le_trans hb (mul_le_mul_of_nonneg_left hdiv_le hp_nn)
        · have hempty : Finset.Icc (M + 1) X = ∅ := by
            rw [Finset.Icc_eq_empty_iff]; omega
          rw [hempty, Finset.sum_empty, abs_zero]
          positivity
      have hrew : (∑ d ∈ Finset.Icc 1 X, (legendreSym p d : ℝ) * ((X / d : ℕ) : ℝ)) / (X : ℝ) -
          ∑ d ∈ Finset.Icc 1 M, (legendreSym p d : ℝ) / (d : ℝ) =
          ((∑ d ∈ Finset.Icc 1 M, (legendreSym p d : ℝ) * ((X / d : ℕ) : ℝ) -
            (X : ℝ) * ∑ d ∈ Finset.Icc 1 M, (legendreSym p d : ℝ) / (d : ℝ)) +
          (∑ d ∈ Finset.Icc (M + 1) X, (legendreSym p d : ℝ) * ((X / d : ℕ) : ℝ))) / (X : ℝ) := by
        rw [hsplit]; field_simp [hX_pos.ne']; ring
      rw [hrew, abs_div, abs_of_pos hX_pos]
      calc
        |(∑ d ∈ Finset.Icc 1 M, (legendreSym p d : ℝ) * ((X / d : ℕ) : ℝ) -
            (X : ℝ) * ∑ d ∈ Finset.Icc 1 M, (legendreSym p d : ℝ) / (d : ℝ)) +
          (∑ d ∈ Finset.Icc (M + 1) X, (legendreSym p d : ℝ) * ((X / d : ℕ) : ℝ))| / (X : ℝ)
            ≤ (|∑ d ∈ Finset.Icc 1 M, (legendreSym p d : ℝ) * ((X / d : ℕ) : ℝ) -
                (X : ℝ) * ∑ d ∈ Finset.Icc 1 M, (legendreSym p d : ℝ) / (d : ℝ)| +
              |∑ d ∈ Finset.Icc (M + 1) X, (legendreSym p d : ℝ) * ((X / d : ℕ) : ℝ)|) / (X : ℝ) := by
              gcongr; exact abs_add_le _ _
        _ ≤ ((M : ℝ) + 2 * (p : ℝ) * Real.sqrt (X : ℝ)) / (X : ℝ) := by gcongr
        _ ≤ (Real.sqrt (X : ℝ) + 2 * (p : ℝ) * Real.sqrt (X : ℝ)) / (X : ℝ) := by gcongr
        _ = (2 * (p : ℝ) + 1) / Real.sqrt (X : ℝ) := by
            rw [div_eq_div_iff hX_pos.ne' hsqrt_pos.ne']
            have hXeq : Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) = (X : ℝ) :=
              Real.mul_self_sqrt (Nat.cast_nonneg X)
            linear_combination (2 * (p : ℝ) + 1) * hXeq
    have hrhs : Tendsto (fun X : ℕ => (2 * (p : ℝ) + 1) / Real.sqrt (X : ℝ)) atTop (𝓝 0) := by
      have hsq : Tendsto (fun X : ℕ => Real.sqrt (X : ℝ)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      simpa using (tendsto_const_nhds (x := 2 * (p : ℝ) + 1)).div_atTop hsq
    refine squeeze_zero_norm' (a := fun X : ℕ => (2 * (p : ℝ) + 1) / Real.sqrt (X : ℝ)) ?_ hrhs
    filter_upwards [eventually_ge_atTop 1] with X hX
    exact hbound X hX
  have hsum_tendsto : Tendsto (fun X : ℕ =>
      (∑ d ∈ Finset.Icc 1 X, (legendreSym p d : ℝ) * ((X / d : ℕ) : ℝ)) / (X : ℝ))
      atTop (𝓝 LVal) := by
    have := hdiff_zero.add hL_sqrt
    simpa [sub_add_cancel] using this
  have h2 := hsum_tendsto.const_mul (2 : ℝ)
  refine h2.congr fun X => ?_
  rw [← Finset.mul_sum, sum_Icc_sum_divisors_eq, mul_div_assoc]

/-! ### Step 4B: 1D Riemann sum on ellipses → 2π / √p per reduced form -/

lemma card_int_Icc_real_approx {u v : ℝ} (huv : u ≤ v) :
    |((Finset.Icc ⌈u⌉ ⌊v⌋).card : ℝ) - (v - u)| ≤ 1 := by
  by_cases hle : ⌈u⌉ ≤ ⌊v⌋
  · have hcard : ((Finset.Icc ⌈u⌉ ⌊v⌋).card : ℝ) = (⌊v⌋ : ℝ) - (⌈u⌉ : ℝ) + 1 := by
      rw [Int.card_Icc]
      have hnn : 0 ≤ ⌊v⌋ + 1 - ⌈u⌉ := by omega
      have hz : ((⌊v⌋ + 1 - ⌈u⌉).toNat : ℤ) = ⌊v⌋ + 1 - ⌈u⌉ := Int.toNat_of_nonneg hnn
      have hr : (((⌊v⌋ + 1 - ⌈u⌉).toNat : ℕ) : ℝ) = ((⌊v⌋ + 1 - ⌈u⌉ : ℤ) : ℝ) := by
        exact_mod_cast hz
      rw [hr]; push_cast; ring
    rw [hcard]
    have h1 : (⌊v⌋ : ℝ) ≤ v := Int.floor_le v
    have h2 : v - 1 < (⌊v⌋ : ℝ) := by linarith [Int.lt_floor_add_one v]
    have h3 : u ≤ (⌈u⌉ : ℝ) := Int.le_ceil u
    have h4 : (⌈u⌉ : ℝ) < u + 1 := Int.ceil_lt_add_one u
    rw [abs_le]; constructor <;> linarith
  · have hlt : ⌊v⌋ < ⌈u⌉ := not_le.mp hle
    have hempty : Finset.Icc ⌈u⌉ ⌊v⌋ = ∅ := Finset.Icc_eq_empty_of_lt hlt
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (sub_nonneg.mpr huv)]
    have h1 : (⌊v⌋ : ℝ) + 1 ≤ (⌈u⌉ : ℝ) := by exact_mod_cast hlt
    have h2 : v < (⌊v⌋ : ℝ) + 1 := Int.lt_floor_add_one v
    have h3 : (⌈u⌉ : ℝ) < u + 1 := Int.ceil_lt_add_one u
    linarith

lemma integral_sqrt_one_sub_sq_zero_one :
    ∫ t in (0 : ℝ)..1, Real.sqrt (1 - t ^ 2) = π / 4 := by
  have hfull : ∫ t in (-1 : ℝ)..1, Real.sqrt (1 - t ^ 2) = π / 2 := integral_sqrt_one_sub_sq
  have hcont : Continuous (fun t : ℝ => Real.sqrt (1 - t ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) (-1) 0)
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
  have heven : ∫ t in (-1 : ℝ)..0, Real.sqrt (1 - t ^ 2) = ∫ t in (0 : ℝ)..1, Real.sqrt (1 - t ^ 2) := by
    have := intervalIntegral.integral_comp_neg (f := fun t : ℝ => Real.sqrt (1 - t ^ 2)) (a := 0) (b := 1)
    simpa [neg_sq] using this.symm
  linarith

lemma riemann_sqrt_one_sub_sq_approx {R : ℝ} (hR : 1 ≤ R) :
    |(1 / R) * ∑ y ∈ Finset.Icc (-(⌊R⌋₊ : ℤ)) (⌊R⌋₊ : ℤ),
        Real.sqrt (1 - ((y : ℝ) / R) ^ 2) - π / 2| ≤ 1 / R := by
  set Y : ℕ := ⌊R⌋₊
  set g : ℝ → ℝ := fun t => Real.sqrt (1 - t ^ 2)
  have hR_pos : 0 < R := by linarith
  have hcont : Continuous g := Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2))
  have hg_anti : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → g t ≤ g s := by
    intro s t hs hst
    apply Real.sqrt_le_sqrt
    nlinarith
  have hg_nn : ∀ t : ℝ, 0 ≤ g t := fun t => Real.sqrt_nonneg _
  have hg_zero : ∀ t : ℝ, 1 ≤ t → g t = 0 := fun t ht =>
    Real.sqrt_eq_zero_of_nonpos (by nlinarith)
  have hY_le : (Y : ℝ) ≤ R := Nat.floor_le hR_pos.le
  have hR_lt : R < (Y + 1 : ℝ) := Nat.lt_floor_add_one R
  -- Step 1: Lower bound π / 4 ≤ (1 / R) * ∑_{k=0}^Y g(k / R)
  have hlower : π / 4 ≤ (1 / R) * ∑ k ∈ Finset.range (Y + 1), g ((k : ℝ) / R) := by
    have hstep : ∀ k ∈ Finset.range (Y + 1),
        ∫ t in ((k : ℝ) / R)..(((k + 1 : ℕ) : ℝ) / R), g t ≤ (1 / R) * g ((k : ℝ) / R) := by
      intro k _
      have hab : (k : ℝ) / R ≤ ((k + 1 : ℕ) : ℝ) / R := by
        apply div_le_div_of_nonneg_right _ hR_pos.le; push_cast; linarith
      have hbd : ∀ t ∈ Set.Icc ((k : ℝ) / R) (((k + 1 : ℕ) : ℝ) / R), g t ≤ g ((k : ℝ) / R) := by
        intro t ht
        exact hg_anti (div_nonneg (Nat.cast_nonneg k) hR_pos.le) ht.1
      calc
        ∫ t in ((k : ℝ) / R)..(((k + 1 : ℕ) : ℝ) / R), g t
            ≤ ∫ _t in ((k : ℝ) / R)..(((k + 1 : ℕ) : ℝ) / R), g ((k : ℝ) / R) := by
              refine intervalIntegral.integral_mono_on hab
                (hcont.intervalIntegrable _ _) intervalIntegrable_const hbd
        _ = (((k + 1 : ℕ) : ℝ) / R - (k : ℝ) / R) * g ((k : ℝ) / R) := by
              rw [intervalIntegral.integral_const, smul_eq_mul]
        _ = (1 / R) * g ((k : ℝ) / R) := by push_cast; ring
    have hsum_int : ∑ k ∈ Finset.range (Y + 1),
        ∫ t in ((k : ℝ) / R)..(((k + 1 : ℕ) : ℝ) / R), g t =
        ∫ t in (0 : ℝ)..(((Y + 1 : ℕ) : ℝ) / R), g t := by
      have htel := intervalIntegral.sum_integral_adjacent_intervals
        (f := g) (μ := MeasureTheory.volume) (a := fun k : ℕ => (k : ℝ) / R) (n := Y + 1)
        (fun k _ => hcont.intervalIntegrable (μ := MeasureTheory.volume) _ _)
      simpa using htel
    have hge_int : π / 4 ≤ ∫ t in (0 : ℝ)..(((Y + 1 : ℕ) : ℝ) / R), g t := by
      rw [← integral_sqrt_one_sub_sq_zero_one]
      have h1le : (1 : ℝ) ≤ ((Y + 1 : ℕ) : ℝ) / R := by
        rw [one_le_div hR_pos]; exact_mod_cast hR_lt.le
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
        (hcont.intervalIntegrable (μ := MeasureTheory.volume) 1 (((Y + 1 : ℕ) : ℝ) / R))
      have htail_nn : 0 ≤ ∫ t in (1 : ℝ)..(((Y + 1 : ℕ) : ℝ) / R), g t :=
        intervalIntegral.integral_nonneg h1le fun t _ => hg_nn t
      linarith
    calc
      π / 4 ≤ ∫ t in (0 : ℝ)..(((Y + 1 : ℕ) : ℝ) / R), g t := hge_int
      _ = ∑ k ∈ Finset.range (Y + 1), ∫ t in ((k : ℝ) / R)..(((k + 1 : ℕ) : ℝ) / R), g t :=
          hsum_int.symm
      _ ≤ ∑ k ∈ Finset.range (Y + 1), (1 / R) * g ((k : ℝ) / R) := Finset.sum_le_sum hstep
      _ = (1 / R) * ∑ k ∈ Finset.range (Y + 1), g ((k : ℝ) / R) := (Finset.mul_sum _ _ _).symm
  -- Step 2: Upper bound (1 / R) * ∑_{k=0}^Y g(k / R) ≤ π / 4 + 1 / R
  have hupper : (1 / R) * ∑ k ∈ Finset.range (Y + 1), g ((k : ℝ) / R) ≤ π / 4 + 1 / R := by
    have hsplit0 : ∑ k ∈ Finset.range (Y + 1), g ((k : ℝ) / R) =
        g 0 + ∑ k ∈ Finset.range Y, g (((k + 1 : ℕ) : ℝ) / R) := by
      rw [Finset.sum_range_succ']; simp [add_comm]
    have hg0 : g 0 = 1 := by simp [g]
    have hstep : ∀ k ∈ Finset.range Y,
        (1 / R) * g (((k + 1 : ℕ) : ℝ) / R) ≤
        ∫ t in ((k : ℝ) / R)..(((k + 1 : ℕ) : ℝ) / R), g t := by
      intro k _
      have hab : (k : ℝ) / R ≤ ((k + 1 : ℕ) : ℝ) / R := by
        apply div_le_div_of_nonneg_right _ hR_pos.le; push_cast; linarith
      have hbd : ∀ t ∈ Set.Icc ((k : ℝ) / R) (((k + 1 : ℕ) : ℝ) / R),
          g (((k + 1 : ℕ) : ℝ) / R) ≤ g t := by
        intro t ht
        exact hg_anti (le_trans (div_nonneg (Nat.cast_nonneg k) hR_pos.le) ht.1) ht.2
      calc
        (1 / R) * g (((k + 1 : ℕ) : ℝ) / R)
            = (((k + 1 : ℕ) : ℝ) / R - (k : ℝ) / R) * g (((k + 1 : ℕ) : ℝ) / R) := by
              push_cast; ring
        _ = ∫ _t in ((k : ℝ) / R)..(((k + 1 : ℕ) : ℝ) / R), g (((k + 1 : ℕ) : ℝ) / R) := by
              rw [intervalIntegral.integral_const, smul_eq_mul]
        _ ≤ ∫ t in ((k : ℝ) / R)..(((k + 1 : ℕ) : ℝ) / R), g t :=
              intervalIntegral.integral_mono_on hab intervalIntegrable_const
                (hcont.intervalIntegrable _ _) hbd
    have hsum_int : ∑ k ∈ Finset.range Y,
        ∫ t in ((k : ℝ) / R)..(((k + 1 : ℕ) : ℝ) / R), g t =
        ∫ t in (0 : ℝ)..((Y : ℝ) / R), g t := by
      have htel := intervalIntegral.sum_integral_adjacent_intervals
        (f := g) (μ := MeasureTheory.volume) (a := fun k : ℕ => (k : ℝ) / R) (n := Y)
        (fun k _ => hcont.intervalIntegrable (μ := MeasureTheory.volume) _ _)
      simpa using htel
    have hle_int : ∫ t in (0 : ℝ)..((Y : ℝ) / R), g t ≤ π / 4 := by
      rw [← integral_sqrt_one_sub_sq_zero_one]
      have hY1 : (Y : ℝ) / R ≤ 1 := (div_le_one hR_pos).mpr hY_le
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 ((Y : ℝ) / R))
        (hcont.intervalIntegrable (μ := MeasureTheory.volume) ((Y : ℝ) / R) 1)
      have htail_nn : 0 ≤ ∫ t in ((Y : ℝ) / R)..1, g t :=
        intervalIntegral.integral_nonneg hY1 fun t _ => hg_nn t
      linarith
    have hsum_le : (1 / R) * ∑ k ∈ Finset.range Y, g (((k + 1 : ℕ) : ℝ) / R) ≤ π / 4 := by
      calc
        (1 / R) * ∑ k ∈ Finset.range Y, g (((k + 1 : ℕ) : ℝ) / R)
            = ∑ k ∈ Finset.range Y, (1 / R) * g (((k + 1 : ℕ) : ℝ) / R) := Finset.mul_sum _ _ _
        _ ≤ ∑ k ∈ Finset.range Y, ∫ t in ((k : ℝ) / R)..(((k + 1 : ℕ) : ℝ) / R), g t :=
            Finset.sum_le_sum hstep
        _ = ∫ t in (0 : ℝ)..((Y : ℝ) / R), g t := hsum_int
        _ ≤ π / 4 := hle_int
    rw [hsplit0, hg0, mul_add, mul_one]
    linarith
  -- Step 3: Pair negative and positive y
  have hsym : ∑ y ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ), g ((y : ℝ) / R) =
      2 * (∑ k ∈ Finset.range (Y + 1), g ((k : ℝ) / R)) - 1 := by
    have hunion : Finset.Icc (-(Y : ℤ)) (Y : ℤ) =
        Finset.Icc (-(Y : ℤ)) (-1) ∪ Finset.Icc (0 : ℤ) (Y : ℤ) := by
      ext y; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc (-(Y : ℤ)) (-1)) (Finset.Icc (0 : ℤ) (Y : ℤ)) := by
      rw [Finset.disjoint_left]; intro y h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
    rw [hunion, Finset.sum_union hdisj]
    have hpos : ∑ y ∈ Finset.Icc (0 : ℤ) (Y : ℤ), g ((y : ℝ) / R) =
        ∑ k ∈ Finset.range (Y + 1), g ((k : ℝ) / R) := by
      refine Finset.sum_bij (fun y _ => y.toNat) ?_ ?_ ?_ ?_
      · intro y hy; simp only [Finset.mem_Icc, Finset.mem_range] at hy ⊢; omega
      · intro y₁ hy₁ y₂ hy₂ heq; simp only [Finset.mem_Icc] at hy₁ hy₂; omega
      · intro k hk; simp only [Finset.mem_range] at hk
        refine ⟨(k : ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simp⟩
      · intro y hy; simp only [Finset.mem_Icc] at hy
        have : ((y.toNat : ℕ) : ℝ) = (y : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hy.1
        rw [this]
    have hneg : ∑ y ∈ Finset.Icc (-(Y : ℤ)) (-1), g ((y : ℝ) / R) =
        ∑ k ∈ Finset.range (Y + 1), g ((k : ℝ) / R) - 1 := by
      have h0 : ∑ k ∈ Finset.range (Y + 1), g ((k : ℝ) / R) =
          1 + ∑ k ∈ Finset.Icc 1 Y, g ((k : ℝ) / R) := by
        rw [Finset.sum_range_succ']
        have hg0 : g ((0 : ℕ) / R) = 1 := by simp [g]
        rw [hg0, add_comm]
        congr 1
        refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
        · intro k hk; simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢; omega
        · intro k₁ _ k₂ _ h; omega
        · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
          exact ⟨k - 1, by omega, by omega⟩
        · intro k _; rfl
      rw [h0, add_sub_cancel_left]
      refine Finset.sum_bij (fun y _ => (-y).toNat) ?_ ?_ ?_ ?_
      · intro y hy; simp only [Finset.mem_Icc] at hy ⊢; omega
      · intro y₁ hy₁ y₂ hy₂ heq; simp only [Finset.mem_Icc] at hy₁ hy₂; omega
      · intro k hk; simp only [Finset.mem_Icc] at hk
        refine ⟨-(k : ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simp⟩
      · intro y hy; simp only [Finset.mem_Icc] at hy
        have : (((-y).toNat : ℕ) : ℝ) = -(y : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega)
        rw [this, neg_div]
        simp only [g, neg_sq]
    rw [hpos, hneg]; ring
  rw [hsym, mul_sub, mul_one, ← mul_assoc, mul_comm (1 / R) 2, mul_assoc]
  rw [abs_le]; constructor <;> linarith

/-- Boxed ellipse set of lattice points `(x, y)` with `a*x^2 + b*x*y + c*y^2 ≤ X`. -/
noncomputable def ellipseBox (a b c : ℤ) (X : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-2 * (X : ℤ)) (2 * (X : ℤ)) ×ˢ Finset.Icc (-2 * (X : ℤ)) (2 * (X : ℤ))).filter
    (fun xy : ℤ × ℤ => a * xy.1 ^ 2 + b * xy.1 * xy.2 + c * xy.2 ^ 2 ≤ (X : ℤ))

lemma ellipseBox_card_fiber_eq {p : ℕ} {a b c : ℤ} {X : ℕ}
    (hp : 0 < p) (ha : 0 < a) (hdisc : b ^ 2 - 4 * a * c = -(p : ℤ))
    (hba : |b| ≤ a) (hac : a ≤ c) (hXp : p ≤ X) :
    (ellipseBox a b c X).card =
      ∑ y ∈ Finset.Icc (-(⌊Real.sqrt (4 * (a : ℝ) * (X : ℝ) / (p : ℝ))⌋₊ : ℤ))
        (⌊Real.sqrt (4 * (a : ℝ) * (X : ℝ) / (p : ℝ))⌋₊ : ℤ),
        (Finset.Icc
          ⌈(-(b : ℝ) * (y : ℝ) - Real.sqrt (4 * (a : ℝ) * (X : ℝ) - (p : ℝ) * (y : ℝ) ^ 2)) / (2 * (a : ℝ))⌉
          ⌊(-(b : ℝ) * (y : ℝ) + Real.sqrt (4 * (a : ℝ) * (X : ℝ) - (p : ℝ) * (y : ℝ) ^ 2)) / (2 * (a : ℝ))⌋).card := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have ha_pos : (0 : ℝ) < (a : ℝ) := Int.cast_pos.mpr ha
  have hX1 : 1 ≤ X := le_trans hp hXp
  have h4a_le_p : (a : ℤ) ≤ (p : ℤ) := by
    have hb2 : b ^ 2 ≤ a ^ 2 := sq_le_sq.mpr (by rwa [abs_of_pos ha])
    nlinarith
  set R : ℝ := Real.sqrt (4 * (a : ℝ) * (X : ℝ) / (p : ℝ))
  have hR_pos : 0 < R := Real.sqrt_pos.mpr (by positivity)
  have hR_sq : R ^ 2 = 4 * (a : ℝ) * (X : ℝ) / (p : ℝ) := Real.sq_sqrt (by positivity)
  set Y : ℕ := ⌊R⌋₊
  have hY_le : (Y : ℝ) ≤ R := Nat.floor_le hR_pos.le
  have hmaps : ∀ xy ∈ ellipseBox a b c X, xy.2 ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ) := by
    intro xy hxy
    simp only [ellipseBox, Finset.mem_filter] at hxy
    have hcs : (2 * a * xy.1 + b * xy.2) ^ 2 + (p : ℤ) * xy.2 ^ 2 ≤ 4 * a * (X : ℤ) := by
      nlinarith [hxy.2, hdisc]
    have hpy : (p : ℝ) * (xy.2 : ℝ) ^ 2 ≤ 4 * (a : ℝ) * (X : ℝ) := by
      have h1 : (p : ℤ) * xy.2 ^ 2 ≤ 4 * a * (X : ℤ) := by nlinarith [sq_nonneg (2 * a * xy.1 + b * xy.2)]
      exact_mod_cast h1
    have hy_sq : (xy.2 : ℝ) ^ 2 ≤ R ^ 2 := by rw [hR_sq, le_div_iff₀ hp_pos]; linarith
    have hy_abs : |(xy.2 : ℝ)| ≤ R := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hR_pos.le]; exact Real.sqrt_le_sqrt hy_sq
    have hy_nat : xy.2.natAbs ≤ Y := by
      refine Nat.le_floor ?_
      have : (xy.2.natAbs : ℝ) = |(xy.2 : ℝ)| := by rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
      linarith
    simp only [Finset.mem_Icc]; omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun y hy => ?_
  simp only [Finset.mem_Icc] at hy
  have hy_abs : |(y : ℝ)| ≤ R := by
    have : |(y : ℝ)| ≤ (Y : ℝ) := abs_le.mpr ⟨by exact_mod_cast hy.1, by exact_mod_cast hy.2⟩
    linarith
  have hdisc_nn : 0 ≤ 4 * (a : ℝ) * (X : ℝ) - (p : ℝ) * (y : ℝ) ^ 2 := by
    have hsq : (y : ℝ) ^ 2 ≤ R ^ 2 := by nlinarith [abs_le.mp hy_abs]
    rw [hR_sq, le_div_iff₀ hp_pos] at hsq; linarith
  set D := Real.sqrt (4 * (a : ℝ) * (X : ℝ) - (p : ℝ) * (y : ℝ) ^ 2)
  set u := (-(b : ℝ) * (y : ℝ) - D) / (2 * (a : ℝ))
  set v := (-(b : ℝ) * (y : ℝ) + D) / (2 * (a : ℝ))
  refine Finset.card_bij (fun xy _ => xy.1) ?_ ?_ ?_
  · intro xy hxy
    simp only [Finset.mem_filter, ellipseBox] at hxy
    rcases hxy with ⟨⟨_, hev⟩, rfl⟩
    have hcs : (2 * (a : ℝ) * (xy.1 : ℝ) + (b : ℝ) * (xy.2 : ℝ)) ^ 2 ≤ D ^ 2 := by
      rw [Real.sq_sqrt hdisc_nn]
      have hz : (2 * a * xy.1 + b * xy.2) ^ 2 + (p : ℤ) * xy.2 ^ 2 ≤ 4 * a * (X : ℤ) := by
        nlinarith [hev, hdisc]
      have hr : (2 * (a : ℝ) * (xy.1 : ℝ) + (b : ℝ) * (xy.2 : ℝ)) ^ 2 +
          (p : ℝ) * (xy.2 : ℝ) ^ 2 ≤ 4 * (a : ℝ) * (X : ℝ) := by exact_mod_cast hz
      linarith
    have habs : |2 * (a : ℝ) * (xy.1 : ℝ) + (b : ℝ) * (xy.2 : ℝ)| ≤ D :=
      abs_le_of_sq_le_sq hcs (Real.sqrt_nonneg _)
    have hbounds := abs_le.mp habs
    have hu : u ≤ (xy.1 : ℝ) := by rw [div_le_iff₀ (by linarith)]; linarith
    have hv : (xy.1 : ℝ) ≤ v := by rw [le_div_iff₀ (by linarith)]; linarith
    exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr hu, Int.le_floor.mpr hv⟩
  · intro xy₁ hxy₁ xy₂ hxy₂ heq
    simp only [Finset.mem_filter] at hxy₁ hxy₂
    exact Prod.ext heq (hxy₁.2.trans hxy₂.2.symm)
  · intro x hx
    simp only [Finset.mem_Icc] at hx
    have hu : u ≤ (x : ℝ) := le_trans (Int.le_ceil u) (Int.cast_le.mpr hx.1)
    have hv : (x : ℝ) ≤ v := le_trans (Int.cast_le.mpr hx.2) (Int.floor_le v)
    have hlin1 : -D ≤ 2 * (a : ℝ) * (x : ℝ) + (b : ℝ) * (y : ℝ) := by
      have := (div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (a : ℝ))).mp hu; linarith
    have hlin2 : 2 * (a : ℝ) * (x : ℝ) + (b : ℝ) * (y : ℝ) ≤ D := by
      have := (le_div_iff₀ (by linarith : (0 : ℝ) < 2 * (a : ℝ))).mp hv; linarith
    have hcsR : (2 * (a : ℝ) * (x : ℝ) + (b : ℝ) * (y : ℝ)) ^ 2 + (p : ℝ) * (y : ℝ) ^ 2 ≤
        4 * (a : ℝ) * (X : ℝ) := by
      have hsq : (2 * (a : ℝ) * (x : ℝ) + (b : ℝ) * (y : ℝ)) ^ 2 ≤ D ^ 2 := by
        nlinarith only [hlin1, hlin2]
      rw [Real.sq_sqrt hdisc_nn] at hsq; linarith
    have hcsZ : (2 * a * x + b * y) ^ 2 + (p : ℤ) * y ^ 2 ≤ 4 * a * (X : ℤ) := by exact_mod_cast hcsR
    have hev : a * x ^ 2 + b * x * y + c * y ^ 2 ≤ (X : ℤ) := by
      nlinarith only [hcsZ, hdisc, ha]
    have hX1Z : (1 : ℤ) ≤ (X : ℤ) := by exact_mod_cast hX1
    have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
    have hy_box : -2 * (X : ℤ) ≤ y ∧ y ≤ 2 * (X : ℤ) := by
      have hy2 : y ^ 2 ≤ 4 * (X : ℤ) := by
        have h1 : (p : ℤ) * y ^ 2 ≤ 4 * a * (X : ℤ) := by
          nlinarith only [hcsZ, sq_nonneg (2 * a * x + b * y)]
        nlinarith only [h1, h4a_le_p, hpZ, hX1Z]
      have h4X : 4 * (X : ℤ) ≤ (2 * (X : ℤ)) ^ 2 := by nlinarith only [hX1Z]
      exact abs_le.mp (abs_le_of_sq_le_sq (le_trans hy2 h4X) (by omega))
    have hx_box : -2 * (X : ℤ) ≤ x ∧ x ≤ 2 * (X : ℤ) := by
      have haX : (1 : ℤ) ≤ a * (X : ℤ) := by nlinarith only [ha, hX1Z]
      have hlinZ : (2 * a * x + b * y) ^ 2 ≤ (2 * a * (X : ℤ)) ^ 2 := by
        have h1 : (2 * a * x + b * y) ^ 2 ≤ 4 * a * (X : ℤ) := by
          nlinarith only [hcsZ, hpZ, sq_nonneg y]
        have h2 : 4 * a * (X : ℤ) ≤ (2 * a * (X : ℤ)) ^ 2 := by nlinarith only [haX]
        exact le_trans h1 h2
      have hlin_abs : |2 * a * x + b * y| ≤ 2 * a * (X : ℤ) :=
        abs_le_of_sq_le_sq hlinZ (by nlinarith only [ha, hX1Z])
      have hlin_b := abs_le.mp hlin_abs
      have hby : |b * y| ≤ 2 * a * (X : ℤ) := by
        rw [abs_mul]
        have hyabs : |y| ≤ 2 * (X : ℤ) := abs_le.mpr hy_box
        have hmul := mul_le_mul hba hyabs (abs_nonneg y) (by omega)
        linarith
      have hby_b := abs_le.mp hby
      have h2ax_lo : -(4 * a * (X : ℤ)) ≤ 2 * a * x := by linarith
      have h2ax_hi : 2 * a * x ≤ 4 * a * (X : ℤ) := by linarith
      exact ⟨by nlinarith only [ha, h2ax_lo], by nlinarith only [ha, h2ax_hi]⟩
    refine ⟨(x, y), ?_, rfl⟩
    simp only [Finset.mem_filter, ellipseBox, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨hx_box, hy_box⟩, hev⟩, trivial⟩

lemma ellipseBox_card_approx {p : ℕ} {a b c : ℤ} {X : ℕ}
    (hp : 0 < p) (ha : 0 < a) (hdisc : b ^ 2 - 4 * a * c = -(p : ℤ))
    (hba : |b| ≤ a) (hac : a ≤ c) (hXp : p ≤ X) :
    |(((ellipseBox a b c X).card - 1 : ℕ) : ℝ) / (X : ℝ) - 2 * π / Real.sqrt (p : ℝ)| ≤
      (2 * Real.sqrt (4 * (a : ℝ) * (X : ℝ) / (p : ℝ)) + 2) / (X : ℝ) +
        4 / (Real.sqrt (p : ℝ) * Real.sqrt (4 * (a : ℝ) * (X : ℝ) / (p : ℝ))) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have ha_pos : (0 : ℝ) < (a : ℝ) := Int.cast_pos.mpr ha
  have hsqrt_p : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp_pos
  have hX1 : 1 ≤ X := le_trans hp hXp
  have hX_pos : (0 : ℝ) < (X : ℝ) := Nat.cast_pos.mpr hX1
  have hE_pos : 1 ≤ (ellipseBox a b c X).card := by
    apply Finset.card_pos.mpr
    refine ⟨(0, 0), ?_⟩
    simp only [ellipseBox, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by simp⟩
  set R : ℝ := Real.sqrt (4 * (a : ℝ) * (X : ℝ) / (p : ℝ))
  have hR_ge1 : 1 ≤ R := by
    rw [Real.le_sqrt (by norm_num) (by positivity), le_div_iff₀ hp_pos]
    have h1a : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have hpX : (p : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXp
    nlinarith
  have hR_pos : 0 < R := by linarith
  have hR_sq : R ^ 2 = 4 * (a : ℝ) * (X : ℝ) / (p : ℝ) := Real.sq_sqrt (by positivity)
  set Y : ℕ := ⌊R⌋₊
  have hY_le : (Y : ℝ) ≤ R := Nat.floor_le hR_pos.le
  have h4aX : 4 * (a : ℝ) * (X : ℝ) = (p : ℝ) * R ^ 2 := by rw [hR_sq]; field_simp [hp_pos.ne']
  have hE_card := ellipseBox_card_fiber_eq hp ha hdisc hba hac hXp
  set S : ℝ := (1 / R) * ∑ y ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ), Real.sqrt (1 - ((y : ℝ) / R) ^ 2)
  have hfiber_approx : |((ellipseBox a b c X).card : ℝ) -
      (4 * (X : ℝ) / Real.sqrt (p : ℝ)) * S| ≤ 2 * (Y : ℝ) + 1 := by
    rw [hE_card, Nat.cast_sum]
    simp only [S]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hle_sum : ∑ y ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ),
        |((Finset.Icc
            ⌈(-(b : ℝ) * (y : ℝ) - Real.sqrt (4 * (a : ℝ) * (X : ℝ) - (p : ℝ) * (y : ℝ) ^ 2)) / (2 * (a : ℝ))⌉
            ⌊(-(b : ℝ) * (y : ℝ) + Real.sqrt (4 * (a : ℝ) * (X : ℝ) - (p : ℝ) * (y : ℝ) ^ 2)) / (2 * (a : ℝ))⌋).card : ℝ) -
          (4 * (X : ℝ) / Real.sqrt (p : ℝ)) * ((1 / R) * Real.sqrt (1 - ((y : ℝ) / R) ^ 2))| ≤
        ∑ _y ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ), (1 : ℝ) := by
      refine Finset.sum_le_sum fun y _ => ?_
      set D := Real.sqrt (4 * (a : ℝ) * (X : ℝ) - (p : ℝ) * (y : ℝ) ^ 2)
      set u := (-(b : ℝ) * (y : ℝ) - D) / (2 * (a : ℝ))
      set v := (-(b : ℝ) * (y : ℝ) + D) / (2 * (a : ℝ))
      have huv : u ≤ v := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        linarith [Real.sqrt_nonneg (4 * (a : ℝ) * (X : ℝ) - (p : ℝ) * (y : ℝ) ^ 2)]
      have hD_eq : D = Real.sqrt (p : ℝ) * R * Real.sqrt (1 - ((y : ℝ) / R) ^ 2) := by
        have hrad : 4 * (a : ℝ) * (X : ℝ) - (p : ℝ) * (y : ℝ) ^ 2 =
            ((p : ℝ) * R ^ 2) * (1 - ((y : ℝ) / R) ^ 2) := by
          rw [h4aX]; field_simp [hR_pos.ne']
        change Real.sqrt (4 * (a : ℝ) * (X : ℝ) - (p : ℝ) * (y : ℝ) ^ 2) = _
        rw [hrad, Real.sqrt_mul (by positivity), Real.sqrt_mul hp_pos.le, Real.sqrt_sq hR_pos.le]
      have hvu : v - u = (4 * (X : ℝ) / Real.sqrt (p : ℝ)) * ((1 / R) * Real.sqrt (1 - ((y : ℝ) / R) ^ 2)) := by
        have hvu1 : v - u = D / (a : ℝ) := by simp only [u, v]; field_simp [ha_pos.ne']; ring
        rw [hvu1, hD_eq]
        have hp_eq : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) := Real.mul_self_sqrt hp_pos.le
        rw [div_eq_iff ha_pos.ne']
        have h1 : (4 * (X : ℝ) / Real.sqrt (p : ℝ)) * ((1 / R) * Real.sqrt (1 - ((y : ℝ) / R) ^ 2)) * (a : ℝ) =
            (4 * (a : ℝ) * (X : ℝ)) / (Real.sqrt (p : ℝ) * R) * Real.sqrt (1 - ((y : ℝ) / R) ^ 2) := by ring
        rw [h1, h4aX]
        congr 1
        rw [eq_div_iff (mul_ne_zero hsqrt_p.ne' hR_pos.ne')]
        linear_combination R ^ 2 * hp_eq
      rw [← hvu]
      exact card_int_Icc_real_approx huv
    refine le_trans hle_sum ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Int.card_Icc]
    have hnn : 0 ≤ (Y : ℤ) + 1 - (-(Y : ℤ)) := by omega
    have hz : (((Y : ℤ) + 1 - (-(Y : ℤ))).toNat : ℤ) = (Y : ℤ) + 1 - (-(Y : ℤ)) :=
      Int.toNat_of_nonneg hnn
    have hr : ((((Y : ℤ) + 1 - (-(Y : ℤ))).toNat : ℕ) : ℝ) = (((Y : ℤ) + 1 - (-(Y : ℤ)) : ℤ) : ℝ) := by
      exact_mod_cast hz
    rw [hr]; push_cast; ring_nf; rfl
  have hriem := riemann_sqrt_one_sub_sq_approx hR_ge1
  have hcast_sub : (((ellipseBox a b c X).card - 1 : ℕ) : ℝ) = ((ellipseBox a b c X).card : ℝ) - 1 := by
    rw [Nat.cast_sub hE_pos, Nat.cast_one]
  rw [hcast_sub]
  have hrew : (((ellipseBox a b c X).card : ℝ) - 1) / (X : ℝ) - 2 * π / Real.sqrt (p : ℝ) =
      ((((ellipseBox a b c X).card : ℝ) - (4 * (X : ℝ) / Real.sqrt (p : ℝ)) * S) - 1) / (X : ℝ) +
        (4 / Real.sqrt (p : ℝ)) * (S - π / 2) := by
    field_simp [hX_pos.ne', hsqrt_p.ne']; ring
  rw [hrew]
  have h4p : 0 < 4 / Real.sqrt (p : ℝ) := by positivity
  calc
    |((((ellipseBox a b c X).card : ℝ) - (4 * (X : ℝ) / Real.sqrt (p : ℝ)) * S) - 1) / (X : ℝ) +
        (4 / Real.sqrt (p : ℝ)) * (S - π / 2)|
        ≤ |((((ellipseBox a b c X).card : ℝ) - (4 * (X : ℝ) / Real.sqrt (p : ℝ)) * S) - 1) / (X : ℝ)| +
            |(4 / Real.sqrt (p : ℝ)) * (S - π / 2)| := abs_add_le _ _
    _ = |(((ellipseBox a b c X).card : ℝ) - (4 * (X : ℝ) / Real.sqrt (p : ℝ)) * S) - 1| / (X : ℝ) +
            (4 / Real.sqrt (p : ℝ)) * |S - π / 2| := by
          rw [abs_div, abs_of_pos hX_pos, abs_mul, abs_of_pos h4p]
    _ ≤ (|((ellipseBox a b c X).card : ℝ) - (4 * (X : ℝ) / Real.sqrt (p : ℝ)) * S| + 1) / (X : ℝ) +
            (4 / Real.sqrt (p : ℝ)) * (1 / R) := by
          gcongr
          · simpa only [abs_one] using
              abs_sub (((ellipseBox a b c X).card : ℝ) - (4 * (X : ℝ) / Real.sqrt (p : ℝ)) * S) 1
    _ ≤ (2 * (Y : ℝ) + 1 + 1) / (X : ℝ) + (4 / Real.sqrt (p : ℝ)) * (1 / R) := by gcongr
    _ ≤ (2 * R + 2) / (X : ℝ) + 4 / (Real.sqrt (p : ℝ) * R) := by
          have h1 : (4 / Real.sqrt (p : ℝ)) * (1 / R) = 4 / (Real.sqrt (p : ℝ) * R) := by ring
          have h2 : 2 * (Y : ℝ) + 1 + 1 ≤ 2 * R + 2 := by linarith
          rw [h1]; gcongr

/-- Lattice point count in the ellipse `a*x^2 + b*x*y + c*y^2 ≤ X` divided by `X` tends to `2π / √p`. -/
lemma tendsto_ellipse_card_div {p : ℕ} {a b c : ℤ}
    (hp : 0 < p) (ha : 0 < a) (hdisc : b ^ 2 - 4 * a * c = -(p : ℤ))
    (hba : |b| ≤ a) (hac : a ≤ c) :
    Tendsto (fun X : ℕ => (((ellipseBox a b c X).card - 1 : ℕ) : ℝ) / (X : ℝ))
      atTop (𝓝 (2 * π / Real.sqrt (p : ℝ))) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have ha_pos : (0 : ℝ) < (a : ℝ) := Int.cast_pos.mpr ha
  have hsqrt_p : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp_pos
  have hR_tendsto : Tendsto (fun X : ℕ => Real.sqrt (4 * (a : ℝ) * (X : ℝ) / (p : ℝ))) atTop atTop := by
    have hlin : Tendsto (fun X : ℕ => (4 * (a : ℝ) / (p : ℝ)) * (X : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop
    have hlin' : Tendsto (fun X : ℕ => 4 * (a : ℝ) * (X : ℝ) / (p : ℝ)) atTop atTop :=
      hlin.congr fun X => by ring
    exact Real.tendsto_sqrt_atTop.comp hlin'
  have ht1 : Tendsto (fun X : ℕ =>
      (2 * Real.sqrt (4 * (a : ℝ) * (X : ℝ) / (p : ℝ)) + 2) / (X : ℝ)) atTop (𝓝 0) := by
    have hsqrt_X : Tendsto (fun X : ℕ => Real.sqrt (X : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have ha1 : Tendsto (fun X : ℕ => (2 * Real.sqrt (4 * (a : ℝ) / (p : ℝ))) / Real.sqrt (X : ℝ))
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := 2 * Real.sqrt (4 * (a : ℝ) / (p : ℝ)))).div_atTop hsqrt_X
    have ha2 : Tendsto (fun X : ℕ => (2 : ℝ) / (X : ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (2 : ℝ))).div_atTop tendsto_natCast_atTop_atTop
    have hsum := ha1.add ha2
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with X hX
    have hX_pos : (0 : ℝ) < (X : ℝ) := Nat.cast_pos.mpr hX
    have hsqrt_X_pos : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hX_pos
    have hmul : Real.sqrt (4 * (a : ℝ) * (X : ℝ) / (p : ℝ)) =
        Real.sqrt (4 * (a : ℝ) / (p : ℝ)) * Real.sqrt (X : ℝ) := by
      rw [show 4 * (a : ℝ) * (X : ℝ) / (p : ℝ) = (4 * (a : ℝ) / (p : ℝ)) * (X : ℝ) by ring,
        Real.sqrt_mul (by positivity)]
    rw [hmul, add_div]
    congr 1
    rw [div_eq_div_iff hsqrt_X_pos.ne' hX_pos.ne']
    have hsqX : Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) = (X : ℝ) := Real.mul_self_sqrt hX_pos.le
    linear_combination (2 * Real.sqrt (4 * (a : ℝ) / (p : ℝ))) * hsqX.symm
  have ht2 : Tendsto (fun X : ℕ =>
      4 / (Real.sqrt (p : ℝ) * Real.sqrt (4 * (a : ℝ) * (X : ℝ) / (p : ℝ)))) atTop (𝓝 0) := by
    have hden : Tendsto (fun X : ℕ =>
        Real.sqrt (p : ℝ) * Real.sqrt (4 * (a : ℝ) * (X : ℝ) / (p : ℝ))) atTop atTop :=
      Tendsto.const_mul_atTop hsqrt_p hR_tendsto
    simpa using (tendsto_const_nhds (x := (4 : ℝ))).div_atTop hden
  have hrhs : Tendsto (fun X : ℕ =>
      (2 * Real.sqrt (4 * (a : ℝ) * (X : ℝ) / (p : ℝ)) + 2) / (X : ℝ) +
      4 / (Real.sqrt (p : ℝ) * Real.sqrt (4 * (a : ℝ) * (X : ℝ) / (p : ℝ)))) atTop (𝓝 0) := by
    simpa using ht1.add ht2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' (a := fun X : ℕ =>
      (2 * Real.sqrt (4 * (a : ℝ) * (X : ℝ) / (p : ℝ)) + 2) / (X : ℝ) +
      4 / (Real.sqrt (p : ℝ) * Real.sqrt (4 * (a : ℝ) * (X : ℝ) / (p : ℝ)))) ?_ hrhs
  filter_upwards [eventually_ge_atTop p] with X hXp
  simpa only [Real.norm_eq_abs, abs_abs] using ellipseBox_card_approx hp ha hdisc hba hac hXp

end OMA.A002143Part4

namespace OMA.A002143Final

open scoped Real BigOperators
open Filter Topology
open OMA.A002143Proof OMA.A002143Part3 OMA.A002143Part4

lemma sum_repSet_card_eq_sum_ellipseBox {p : ℕ} (hp : p.Prime) (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, (repSet p n).card =
      ∑ f ∈ RedForms p, ((ellipseBox f.1 f.2.1 f.2.2 X).card - 1) := by
  have hzero_mem : ∀ f ∈ RedForms p, ((0 : ℤ), (0 : ℤ)) ∈ ellipseBox f.1 f.2.1 f.2.2 X := by
    intro f _
    simp only [ellipseBox, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by simp⟩
  have hrhs : ∑ f ∈ RedForms p, ((ellipseBox f.1 f.2.1 f.2.2 X).card - 1) =
      ∑ f ∈ RedForms p, ((ellipseBox f.1 f.2.1 f.2.2 X).erase (0, 0)).card := by
    refine Finset.sum_congr rfl fun f hf => ?_
    exact (Finset.card_erase_of_mem (hzero_mem f hf)).symm
  rw [hrhs, ← Finset.card_sigma, ← Finset.card_sigma]
  refine Finset.card_bij
    (fun (s : Σ _ : ℕ, (ℤ × ℤ × ℤ) × ℤ × ℤ) _ => (⟨s.2.1, s.2.2⟩ : Σ _ : ℤ × ℤ × ℤ, ℤ × ℤ))
    ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_sigma, Finset.mem_Icc, mem_repSet_iff hp] at hs
    rcases hs with ⟨⟨hn1, hnX⟩, hf, hev⟩
    simp only [Finset.mem_sigma, Finset.mem_erase, ellipseBox, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Icc]
    refine ⟨hf, ?_, ?_, ?_⟩
    · intro h0
      rw [h0] at hev
      simp only [evalForm] at hev
      omega
    · have hb := rep_coords_bound hp ((mem_RedForms_iff hp s.2.1).mp hf) hev
      have hxb := abs_le.mp hb.1
      have hyb := abs_le.mp hb.2
      exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
    · change evalForm s.2.1 s.2.2.1 s.2.2.2 ≤ (X : ℤ)
      rw [hev]; exact_mod_cast hnX
  · intro s₁ hs₁ s₂ hs₂ heq
    simp only [Finset.mem_sigma, mem_repSet_iff hp] at hs₁ hs₂
    have hf_eq : s₁.2.1 = s₂.2.1 := congrArg Sigma.fst heq
    have hxy_eq : s₁.2.2 = s₂.2.2 := by
      have := (Sigma.mk.inj_iff.mp heq).2
      exact eq_of_heq this
    have hn_eq : s₁.1 = s₂.1 := by
      have hz : (s₁.1 : ℤ) = (s₂.1 : ℤ) := by
        rw [← hs₁.2.2, ← hs₂.2.2, hf_eq, hxy_eq]
      exact_mod_cast hz
    cases s₁; cases s₂
    dsimp only at hn_eq hf_eq hxy_eq
    subst hn_eq
    congr 1
    exact Prod.ext hf_eq hxy_eq
  · intro u hu
    simp only [Finset.mem_sigma, Finset.mem_erase, ellipseBox, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Icc] at hu
    rcases hu with ⟨hf, hne0, _, hev_le⟩
    have hred := (mem_RedForms_iff hp u.1).mp hf
    have hev_le' : evalForm u.1 u.2.1 u.2.2 ≤ (X : ℤ) := hev_le
    have hev_pos : 0 < evalForm u.1 u.2.1 u.2.2 := by
      have ha0 : 0 < u.1.1 := hred.1.1
      have hdisc := hred.1.2
      have hcs : 4 * u.1.1 * evalForm u.1 u.2.1 u.2.2 =
          (2 * u.1.1 * u.2.1 + u.1.2.1 * u.2.2) ^ 2 + (p : ℤ) * u.2.2 ^ 2 := by
        simp only [evalForm]; nlinarith [hdisc]
      have hp0 : (0 : ℤ) < (p : ℤ) := Int.natCast_pos.mpr hp.pos
      have hpos_rhs : 0 < (2 * u.1.1 * u.2.1 + u.1.2.1 * u.2.2) ^ 2 + (p : ℤ) * u.2.2 ^ 2 := by
        by_cases hy0 : u.2.2 = 0
        · have hx0 : u.2.1 ≠ 0 := fun hx => hne0 (Prod.ext hx hy0)
          rw [hy0]; simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
          have : 2 * u.1.1 * u.2.1 ≠ 0 := by
            intro h; rcases mul_eq_zero.mp h with h1 | h2
            · omega
            · exact hx0 h2
          exact sq_pos_of_ne_zero this
        · have : 0 < (p : ℤ) * u.2.2 ^ 2 := mul_pos hp0 (sq_pos_of_ne_zero hy0)
          nlinarith [sq_nonneg (2 * u.1.1 * u.2.1 + u.1.2.1 * u.2.2)]
      nlinarith
    set n : ℕ := (evalForm u.1 u.2.1 u.2.2).toNat
    have hn_cast : (n : ℤ) = evalForm u.1 u.2.1 u.2.2 := Int.toNat_of_nonneg hev_pos.le
    refine ⟨⟨n, (u.1, u.2)⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_Icc, mem_repSet_iff hp]
    refine ⟨⟨by omega, by omega⟩, hf, hn_cast.symm⟩

theorem dirichlet_class_number_formula (p : ℕ) [Fact p.Prime] (hp3 : 3 < p) (h8 : p % 8 = 3) :
    LVal p = ((RedForms p).card : ℝ) * π / Real.sqrt (p : ℝ) := by
  have hp : p.Prime := Fact.out
  have h1 : Tendsto (fun X : ℕ =>
      ((∑ n ∈ Finset.Icc 1 X, (repSet p n).card : ℕ) : ℝ) / (X : ℝ))
      atTop (𝓝 (2 * LVal p)) := by
    have hhyp := tendsto_hyperbola_sum (p := p) (LVal p) (tendsto_LPartial p h8)
      (fun {M N f} hlt hnn hanti => by
        have hf_all : ∀ n, 0 ≤ (if M + 1 ≤ n ∧ n ≤ N then f n else 0) := by
          intro n; split_ifs with h
          · exact hnn n h.1 h.2
          · exact le_rfl
        have hanti_all : ∀ n, M + 1 ≤ n →
            (if M + 1 ≤ n + 1 ∧ n + 1 ≤ N then f (n + 1) else 0) ≤
            (if M + 1 ≤ n ∧ n ≤ N then f n else 0) := by
          intro n hn
          by_cases h1 : M + 1 ≤ n + 1 ∧ n + 1 ≤ N <;> by_cases h2 : M + 1 ≤ n ∧ n ≤ N
          · simp only [h1, h2, and_self, ↓reduceIte]; exact hanti n hn h1.2
          · omega
          · simp only [h1, h2, and_self, ↓reduceIte]; exact hnn n h2.1 h2.2
          · simp only [h1, h2, ↓reduceIte, le_rfl]
        have hb := abel_sum_Icc_bound p h8 hlt.le hf_all hanti_all
        have hsum_eq : ∑ n ∈ Finset.Icc (M + 1) N, (legendreSym p n : ℝ) *
            (if M + 1 ≤ n ∧ n ≤ N then f n else 0) =
            ∑ n ∈ Finset.Icc (M + 1) N, (legendreSym p n : ℝ) * f n := by
          refine Finset.sum_congr rfl fun n hn => ?_
          simp only [Finset.mem_Icc] at hn; simp [hn.1, hn.2]
        rw [hsum_eq] at hb
        simpa [show M + 1 ≤ M + 1 ∧ M + 1 ≤ N by omega] using hb)
    refine hhyp.congr fun X => ?_
    congr 1
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Icc] at hn
    have hz := repSet_card_eq_two_mul_sum_legendre (p := p) (n := n) hp3 h8 hn.1
    have hr : (((repSet p n).card : ℤ) : ℝ) = ((2 * ∑ d ∈ n.divisors, legendreSym p d : ℤ) : ℝ) := by
      exact_mod_cast hz
    simpa [Int.cast_sum] using hr.symm
  have h2 : Tendsto (fun X : ℕ =>
      ((∑ n ∈ Finset.Icc 1 X, (repSet p n).card : ℕ) : ℝ) / (X : ℝ))
      atTop (𝓝 (((RedForms p).card : ℝ) * (2 * π / Real.sqrt (p : ℝ)))) := by
    have hsum : Tendsto (fun X : ℕ =>
        ∑ f ∈ RedForms p, (((ellipseBox f.1 f.2.1 f.2.2 X).card - 1 : ℕ) : ℝ) / (X : ℝ))
        atTop (𝓝 (∑ _f ∈ RedForms p, (2 * π / Real.sqrt (p : ℝ)))) := by
      refine tendsto_finsetSum _ fun f hf => ?_
      have hred := (mem_RedForms_iff hp f).mp hf
      exact tendsto_ellipse_card_div hp.pos hred.1.1 hred.1.2 hred.2.1 hred.2.2.1
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    refine hsum.congr fun X => ?_
    rw [sum_repSet_card_eq_sum_ellipseBox hp X, Nat.cast_sum, Finset.sum_div]
  have heq : 2 * LVal p = ((RedForms p).card : ℝ) * (2 * π / Real.sqrt (p : ℝ)) :=
    tendsto_nhds_unique h1 h2
  linarith [show ((RedForms p).card : ℝ) * (2 * π / Real.sqrt (p : ℝ)) =
    2 * (((RedForms p).card : ℝ) * π / Real.sqrt (p : ℝ)) by ring]

end OMA.A002143Final

theorem OMA.solution : type_of% @OMA.S_oeis_a002143.main := by
  intro p hp hp3 h8
  have : Fact p.Prime := ⟨hp⟩
  have hcard : OMA.S_oeis_a002143.h (-(p : ℤ)) = (OMA.A002143Part3.RedForms p).card := by
    simp [OMA.S_oeis_a002143.h, OMA.A002143Part3.RedForms]
  rw [hcard, OMA.A002143Proof.csc_sum_eq_two_mul_p_div_pi_mul_LVal p h8,
    OMA.A002143Final.dirichlet_class_number_formula p hp3 h8]
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hsqrt_ne : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp_pos).ne'
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hp_sq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt hp_pos.le
  field_simp [hsqrt_ne, hpi_ne]
  nlinarith [hp_sq]
