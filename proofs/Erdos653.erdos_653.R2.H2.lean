import OMAReductions.R_Erdos653_erdos_653_R2
import Mathlib

/-!
# A fixed bin width for the distance-count construction of Erdős 653

The grid, projection estimates and finite jitter inequalities below are adapted from
Liam Kruer and Jensen Kohlmeyer (gus), Conjectures.io, verified submission
257ce6dd-e3e5-4169-9d7e-2811092977ca, Main.lean, SHA-256
f3b51c0df8d3c8fb5ad2b71b01474345fc3dece2d1bd37c9d60b45acc711fde4.
https://conjectures.io/results/257ce6dd-e3e5-4169-9d7e-2811092977ca/solution

We use two rounded affine slopes directly, which makes both rounding errors
uniformly bounded. We choose the variance tolerance and the bin width before
the grid size, then realize the integer scores by bounded strip shifts.
-/

/-! Exact grid displacement counts and finite maximum-norm kernel estimates. -/

noncomputable section

namespace DistanceCounts
namespace GridPairs

open Finset
open scoped Classical

abbrev Grid (L : ℕ) := Fin L × Fin L

def displacement {L : ℕ} (p : Grid L × Grid L) : ℤ × ℤ :=
  ((p.2.1 : ℤ) - p.1.1, (p.2.2 : ℤ) - p.1.2)

def radius (d : ℤ × ℤ) : ℕ := max d.1.natAbs d.2.natAbs

def rho (L : ℕ) (d : ℤ × ℤ) : ℝ := (radius d : ℝ) / L

def multiplicity (L : ℕ) (d : ℤ × ℤ) : ℕ :=
  (L - d.1.natAbs) * (L - d.2.natAbs)

def coordinateFiber (L : ℕ) (d : ℤ) : Finset (Fin L × Fin L) :=
  univ.filter (fun p => (p.2 : ℤ) - p.1 = d)

lemma coordinateFiber_card (L : ℕ) (d : ℤ) :
    (coordinateFiber L d).card = L - d.natAbs := by
  classical
  have hcount : (coordinateFiber L d).card =
      (Ico (max 0 (-d)) (min (L : ℤ) (L - d))).card := by
    apply card_bij (fun p _ => (p.1 : ℤ))
    · intro p hp
      have hp' := (mem_filter.mp hp).2
      have h₁ := p.1.isLt
      have h₂ := p.2.isLt
      simp only [mem_Ico]
      omega
    · intro p hp q hq hpq
      have hp' := (mem_filter.mp hp).2
      have hq' := (mem_filter.mp hq).2
      apply Prod.ext <;> apply Fin.ext <;> omega
    · intro x hx
      simp only [mem_Ico] at hx
      have hx0 : 0 ≤ x := by omega
      have hy0 : 0 ≤ x + d := by omega
      let p : Fin L × Fin L :=
        (⟨x.toNat, by omega⟩, ⟨(x + d).toNat, by omega⟩)
      have hp : p ∈ coordinateFiber L d := by
        simp only [coordinateFiber, mem_filter, mem_univ, true_and]
        dsimp [p]
        omega
      exact ⟨p, hp, by dsimp [p]; omega⟩
  rw [hcount, Int.card_Ico]
  have hd := Int.natCast_natAbs d
  by_cases h : 0 ≤ d
  · rw [abs_of_nonneg h] at hd
    omega
  · rw [abs_of_neg (lt_of_not_ge h)] at hd
    omega

/-- The histogram is derived from actual ordered pairs of grid points. -/
lemma multiplicity_eq_card (L : ℕ) (d : ℤ × ℤ) :
    multiplicity L d =
      (univ.filter (fun p : Grid L × Grid L => displacement p = d)).card := by
  classical
  have h : (univ.filter (fun p : Grid L × Grid L => displacement p = d)).card =
      ((coordinateFiber L d.1) ×ˢ (coordinateFiber L d.2)).card := by
    apply card_bij (fun p _ => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
    · intro p hp
      have h := (mem_filter.mp hp).2
      simpa [coordinateFiber, displacement] using (Prod.ext_iff.mp h)
    · intro p hp q hq h
      rcases p with ⟨⟨a,b⟩,⟨c,e⟩⟩
      rcases q with ⟨⟨a',b'⟩,⟨c',e'⟩⟩
      simpa only [Prod.mk.injEq, and_assoc, and_left_comm, and_comm] using h
    · intro p hp
      refine ⟨((p.1.1, p.2.1), (p.1.2, p.2.2)), ?_, rfl⟩
      simpa [coordinateFiber, displacement, Prod.ext_iff] using hp
  rw [h, card_product, coordinateFiber_card, coordinateFiber_card]
  rfl

def displacements (L : ℕ) : Finset (ℤ × ℤ) :=
  univ.image (@displacement L)

/-- Exact finite summation by displacement, with both diagonal and boundary multiplicities. -/
lemma sum_by_displacement (L : ℕ) (f : ℤ × ℤ → ℝ) :
    (∑ p : Grid L × Grid L, f (displacement p)) =
      ∑ d ∈ displacements L, (multiplicity L d : ℝ) * f d := by
  classical
  rw [← sum_fiberwise_of_maps_to
    (show Set.MapsTo (@displacement L) (univ : Finset (Grid L × Grid L))
      (displacements L) from fun p hp => mem_image_of_mem _ hp)]
  apply sum_congr rfl
  intro d hd
  rw [multiplicity_eq_card]
  calc
    (∑ p ∈ univ.filter (fun p : Grid L × Grid L => displacement p = d),
      f (displacement p)) =
        ∑ _p ∈ univ.filter (fun p : Grid L × Grid L => displacement p = d), f d := by
          apply sum_congr rfl
          intro p hp
          rw [(mem_filter.mp hp).2]
    _ = _ := by simp

lemma multiplicity_le (L : ℕ) (d : ℤ × ℤ) : multiplicity L d ≤ L ^ 2 := by
  unfold multiplicity
  calc
    (L - d.1.natAbs) * (L - d.2.natAbs) ≤ L * L :=
      Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    _ = _ := by ring

lemma radius_pos_iff (d : ℤ × ℤ) : 0 < radius d ↔ d ≠ 0 := by
  rcases d with ⟨x,y⟩
  simp [radius, Int.natAbs_pos, Prod.ext_iff]
  tauto

lemma radius_le_iff (d : ℤ × ℤ) (k : ℕ) :
    radius d ≤ k ↔ -(k : ℤ) ≤ d.1 ∧ d.1 ≤ k ∧ -(k : ℤ) ≤ d.2 ∧ d.2 ≤ k := by
  have hx := Int.natCast_natAbs d.1
  have hy := Int.natCast_natAbs d.2
  rw [abs_eq_max_neg] at hx hy
  simp only [radius, max_le_iff]
  omega

def square (k : ℕ) : Finset (ℤ × ℤ) :=
  (Icc (-(k : ℤ)) k) ×ˢ (Icc (-(k : ℤ)) k)

lemma mem_square (d : ℤ × ℤ) (k : ℕ) : d ∈ square k ↔ radius d ≤ k := by
  simp only [square, mem_product, mem_Icc, radius_le_iff]
  tauto

lemma square_card (k : ℕ) : (square k).card = (2 * k + 1) ^ 2 := by
  have h : ((k : ℤ) + 1 - -(k : ℤ)).toNat = 2 * k + 1 := by omega
  simp only [square, card_product, Int.card_Icc, h, pow_two]

lemma square_mono {j k : ℕ} (h : j ≤ k) : square j ⊆ square k := by
  intro d hd
  rw [mem_square] at hd ⊢
  omega

def shell (k : ℕ) : Finset (ℤ × ℤ) :=
  (square k).filter (fun d => radius d = k ∧ d ≠ 0)

lemma mem_shell (d : ℤ × ℤ) (k : ℕ) :
    d ∈ shell k ↔ radius d = k ∧ d ≠ 0 := by
  simp only [shell, mem_filter, mem_square]
  exact ⟨fun h => h.2, fun h => ⟨h.1.le, h⟩⟩

lemma shell_eq_sdiff {k : ℕ} (hk : 0 < k) :
    shell k = square k \ square (k - 1) := by
  ext d
  rw [mem_shell, mem_sdiff, mem_square, mem_square, ← radius_pos_iff]
  omega

/-- The exact maximum-norm shell count. -/
lemma shell_card (k : ℕ) : (shell k).card = 8 * k := by
  by_cases hk : k = 0
  · subst k
    have h : shell 0 = ∅ := by
      ext d
      simp only [mem_shell, notMem_empty, iff_false]
      rintro ⟨hd, hd0⟩
      have hpos := (radius_pos_iff d).mpr hd0
      omega
    simp [h]
  · rw [shell_eq_sdiff (Nat.pos_of_ne_zero hk), card_sdiff_of_subset
      (square_mono (Nat.sub_le _ _)), square_card, square_card]
    have h : k - 1 + 1 = k := by omega
    have heq : (2 * k + 1) ^ 2 = (2 * (k - 1) + 1) ^ 2 + 8 * k := by
      nlinarith
    omega

/-- Normalized singular sum over an arbitrary finite collection of displacements.
The value at zero is defined to be zero; all estimates below exclude zero explicitly. -/
def kernelSum (L : ℕ) (s : Finset (ℤ × ℤ)) : ℝ :=
  (∑ d ∈ s, (multiplicity L d : ℝ) / rho L d) / (L : ℝ) ^ 4


lemma kernelSum_mono (L : ℕ) {s t : Finset (ℤ × ℤ)} (h : s ⊆ t) :
    kernelSum L s ≤ kernelSum L t := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact sum_le_sum_of_subset_of_nonneg h (fun d hd hs => by unfold rho; positivity)

lemma kernelSum_le_unweighted (L : ℕ) (hL : 0 < L) (s : Finset (ℤ × ℤ)) :
    kernelSum L s ≤ (∑ d ∈ s, (radius d : ℝ)⁻¹) / L := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  unfold kernelSum rho
  calc
    (∑ d ∈ s, (multiplicity L d : ℝ) / ((radius d : ℝ) / L)) / (L : ℝ)^4 ≤
        (∑ d ∈ s, (L : ℝ)^2 / ((radius d : ℝ) / L)) / (L : ℝ)^4 := by
      gcongr with d hd
      exact_mod_cast multiplicity_le L d
    _ = (∑ d ∈ s, (radius d : ℝ)⁻¹) / L := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      rw [← mul_sum, ← mul_sum]
      field_simp [hL'.ne']
      <;> ring


def inStrip (m : ℕ) (d : ℤ × ℤ) : Prop :=
  d.1.natAbs ≤ m ∨ d.2.natAbs ≤ m

def strips (N m : ℕ) : Finset (ℤ × ℤ) :=
  ((square N).erase 0).filter (inStrip m)

lemma mem_strips (N m : ℕ) (d : ℤ × ℤ) :
    d ∈ strips N m ↔ d ≠ 0 ∧ radius d ≤ N ∧ inStrip m d := by
  simp only [strips, mem_filter, mem_erase, mem_square]
  tauto

lemma abs_le_interval (z : ℤ) (m : ℕ) :
    z.natAbs ≤ m ↔ z ∈ Icc (-(m : ℤ)) m := by
  have hz := Int.natCast_natAbs z
  rw [abs_eq_max_neg] at hz
  simp only [mem_Icc]
  omega

lemma natAbs_eq_endpoints (z : ℤ) (k : ℕ) :
    z.natAbs = k ↔ z = -(k : ℤ) ∨ z = k := by
  have hz := Int.natCast_natAbs z
  rw [abs_eq_max_neg] at hz
  omega

/-- Outside the small square, each of the two strips has at most
`4 m + 2` points in a shell; their union has at most `8 m + 4`. -/
lemma strip_shell_card (m k : ℕ) :
    ((shell k).filter (inStrip m)).card ≤ 8 * min k m + 4 := by
  classical
  by_cases hkm : k ≤ m
  · rw [min_eq_left hkm]
    exact (card_filter_le _ _).trans (by rw [shell_card]; omega)
  · have hmk : m < k := by omega
    rw [min_eq_right (by omega)]
    let v : Finset (ℤ × ℤ) :=
      (Icc (-(m : ℤ)) m) ×ˢ {-(k : ℤ), (k : ℤ)}
    let h : Finset (ℤ × ℤ) :=
      ({-(k : ℤ), (k : ℤ)} : Finset ℤ) ×ˢ (Icc (-(m : ℤ)) m)
    have hsub : (shell k).filter (inStrip m) ⊆ v ∪ h := by
      intro d hd
      obtain ⟨hd, hs⟩ := mem_filter.mp hd
      have hk := ((mem_shell d k).mp hd).1
      dsimp [radius] at hk
      rcases hs with hx | hy
      · have hyk : d.2.natAbs = k := by omega
        apply mem_union.mpr
        left
        apply mem_product.mpr
        refine ⟨(abs_le_interval _ _).mp hx, ?_⟩
        simpa only [mem_insert, mem_singleton] using (natAbs_eq_endpoints _ _).mp hyk
      · have hxk : d.1.natAbs = k := by omega
        apply mem_union.mpr
        right
        apply mem_product.mpr
        refine ⟨?_, (abs_le_interval _ _).mp hy⟩
        simpa only [mem_insert, mem_singleton] using (natAbs_eq_endpoints _ _).mp hxk
    have hint : (Icc (-(m : ℤ)) m).card = 2 * m + 1 := by
      rw [Int.card_Icc]
      omega
    have hp : ({-(k : ℤ), (k : ℤ)} : Finset ℤ).card ≤ 2 := card_le_two
    calc
      ((shell k).filter (inStrip m)).card ≤ (v ∪ h).card := card_le_card hsub
      _ ≤ v.card + h.card := card_union_le _ _
      _ ≤ (2 * m + 1) * 2 + 2 * (2 * m + 1) := by
        dsimp [v, h]
        rw [card_product, card_product, hint]
        exact Nat.add_le_add (Nat.mul_le_mul_left _ hp) (Nat.mul_le_mul_right _ hp)
      _ = 8 * m + 4 := by ring

def harmonicR (N : ℕ) : ℝ := ∑ k ∈ Icc 1 N, (k : ℝ)⁻¹

lemma harmonicR_eq (N : ℕ) : harmonicR N = (harmonic N : ℝ) := by
  simp only [harmonicR, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

lemma harmonicR_upper (N : ℕ) : harmonicR N ≤ 1 + Real.log N := by
  rw [harmonicR_eq]
  exact harmonic_le_one_add_log N

lemma harmonicR_lower (N : ℕ) : Real.log (N + 1 : ℕ) ≤ harmonicR N := by
  rw [harmonicR_eq]
  exact log_add_one_le_harmonic N

lemma sum_min_div (N m : ℕ) (hm : m ≤ N) :
    (∑ k ∈ Icc 1 N, ((min k m : ℕ) : ℝ) / k) =
      m + (m : ℝ) * (harmonicR N - harmonicR m) := by
  classical
  have hs : Icc 1 m ⊆ Icc 1 N := by
    intro k hk
    simp only [mem_Icc] at hk ⊢
    omega
  rw [← sum_sdiff hs]
  have hsmall : (∑ k ∈ Icc 1 m, ((min k m : ℕ) : ℝ) / k) = m := by
    calc
      (∑ k ∈ Icc 1 m, ((min k m : ℕ) : ℝ) / k) = ∑ _k ∈ Icc 1 m, (1 : ℝ) := by
        apply sum_congr rfl
        intro k hk
        have hk' := mem_Icc.mp hk
        rw [min_eq_left hk'.2, div_self (by exact_mod_cast (show k ≠ 0 by omega))]
      _ = _ := by simp
  have hlarge : (∑ k ∈ Icc 1 N \ Icc 1 m, ((min k m : ℕ) : ℝ) / k) =
      (m : ℝ) * (harmonicR N - harmonicR m) := by
    calc
      (∑ k ∈ Icc 1 N \ Icc 1 m, ((min k m : ℕ) : ℝ) / k) =
          ∑ k ∈ Icc 1 N \ Icc 1 m, (m : ℝ) * (k : ℝ)⁻¹ := by
        apply sum_congr rfl
        intro k hk
        simp only [mem_sdiff, mem_Icc] at hk
        rw [min_eq_right (by omega), div_eq_mul_inv]
      _ = (m : ℝ) * (harmonicR N - harmonicR m) := by
        rw [← mul_sum, sum_sdiff_eq_sub hs]
        rfl
  rw [hsmall, hlarge]
  ring

lemma strip_inverse_bound (N m : ℕ) (hm : m ≤ N) :
    (∑ d ∈ strips N m, (radius d : ℝ)⁻¹) ≤
      8 * (m + (m : ℝ) * (harmonicR N - harmonicR m)) + 4 * harmonicR N := by
  classical
  have hmap : Set.MapsTo radius (strips N m : Finset (ℤ × ℤ)) (Icc 1 N) := by
    intro d hd
    obtain ⟨hd0, hdN, hdm⟩ := (mem_strips N m d).mp hd
    exact mem_Icc.mpr ⟨(radius_pos_iff d).mpr hd0, hdN⟩
  rw [← sum_fiberwise_of_maps_to hmap]
  calc
    (∑ k ∈ Icc 1 N, ∑ d ∈ (strips N m).filter (fun d => radius d = k),
        (radius d : ℝ)⁻¹) ≤
        ∑ k ∈ Icc 1 N, (8 * ((min k m : ℕ) : ℝ) + 4) / k := by
      apply sum_le_sum
      intro k hk
      have hk' := mem_Icc.mp hk
      have hf : (strips N m).filter (fun d => radius d = k) =
          (shell k).filter (inStrip m) := by
        ext d
        simp only [mem_filter, mem_strips, mem_shell]
        constructor
        · rintro ⟨⟨hd0, hdN, hdm⟩, hdk⟩
          exact ⟨⟨hdk, hd0⟩, hdm⟩
        · rintro ⟨⟨hdk, hd0⟩, hdm⟩
          exact ⟨⟨hd0, hdk.trans_le hk'.2, hdm⟩, hdk⟩
      rw [hf]
      calc
        (∑ d ∈ (shell k).filter (inStrip m), (radius d : ℝ)⁻¹) =
            (((shell k).filter (inStrip m)).card : ℝ) / k := by
          calc
            (∑ d ∈ (shell k).filter (inStrip m), (radius d : ℝ)⁻¹) =
                ∑ _d ∈ (shell k).filter (inStrip m), (k : ℝ)⁻¹ := by
              apply sum_congr rfl
              intro d hd
              rw [((mem_shell d k).mp (mem_filter.mp hd).1).1]
            _ = _ := by simp [div_eq_mul_inv]
        _ ≤ (8 * ((min k m : ℕ) : ℝ) + 4) / k := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact_mod_cast strip_shell_card m k
    _ = 8 * (m + (m : ℝ) * (harmonicR N - harmonicR m)) + 4 * harmonicR N := by
      calc
        (∑ k ∈ Icc 1 N, (8 * ((min k m : ℕ) : ℝ) + 4) / k) =
            8 * (∑ k ∈ Icc 1 N, ((min k m : ℕ) : ℝ) / k) + 4 * harmonicR N := by
          unfold harmonicR
          rw [mul_sum, mul_sum, ← sum_add_distrib]
          apply sum_congr rfl
          intro k hk
          simp only [div_eq_mul_inv]
          ring
        _ = _ := by rw [sum_min_div N m hm]


lemma harmonic_tail_log_bound (L m : ℕ) (hL : 0 < L) (r : ℝ)
    (hr : 0 < r) (hm : r * L < m + 1) :
    harmonicR L - harmonicR m ≤ 1 + |Real.log r| := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hp : 0 < r * (L : ℝ) := mul_pos hr hL'
  have hlog : Real.log (r * L) ≤ Real.log ((m : ℝ) + 1) :=
    Real.log_le_log hp hm.le
  rw [Real.log_mul hr.ne' hL'.ne'] at hlog
  have hup := harmonicR_upper L
  have hlo := harmonicR_lower m
  push_cast at hlo
  have habs := neg_le_abs (Real.log r)
  linarith

/-- Uniform finite strip domination. No limiting hypothesis or assumed histogram
enters the bound. The constant `20` is independent of both `L` and `r`. -/
lemma strips_bound (L : ℕ) (hL : 0 < L) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    kernelSum L (strips L ⌊r * L⌋₊) ≤
      20 * (r * (1 + |Real.log r|) + (1 + Real.log L) / L) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  let m := ⌊r * L⌋₊
  have hm0 : (m : ℝ) ≤ r * L := Nat.floor_le (mul_nonneg hr.le hL'.le)
  have hm1 : r * L < (m : ℝ) + 1 := Nat.lt_floor_add_one (r * L)
  have hmL : m ≤ L := by
    have h : (m : ℝ) ≤ L := hm0.trans (by nlinarith)
    exact_mod_cast h
  have ht := harmonic_tail_log_bound L m hL r hr hm1
  have hlogL : 0 ≤ Real.log (L : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hL)
  have hH := harmonicR_upper L
  have habs := abs_nonneg (Real.log r)
  have hmcast : (0 : ℝ) ≤ m := by positivity
  have hcoeff : (m : ℝ) * (harmonicR L - harmonicR m) ≤
      (m : ℝ) * (1 + |Real.log r|) := mul_le_mul_of_nonneg_left ht hmcast
  have hscale : (m : ℝ) * (1 + |Real.log r|) ≤
      (r * L) * (1 + |Real.log r|) :=
    mul_le_mul_of_nonneg_right hm0 (by positivity)
  calc
    kernelSum L (strips L m) ≤ (∑ d ∈ strips L m, (radius d : ℝ)⁻¹) / L :=
      kernelSum_le_unweighted L hL _
    _ ≤ (8 * (m + (m : ℝ) * (harmonicR L - harmonicR m)) +
        4 * harmonicR L) / L :=
      div_le_div_of_nonneg_right (strip_inverse_bound L m hmL) hL'.le
    _ ≤ 20 * (r * (1 + |Real.log r|) + (1 + Real.log L) / L) := by
      apply (div_le_iff₀ hL').mpr
      have heq : (20 * (r * (1 + |Real.log r|) + (1 + Real.log L) / L)) * L =
          20 * (r * L * (1 + |Real.log r|) + (1 + Real.log L)) := by
        field_simp [hL'.ne']
        <;> ring
      rw [heq]
      nlinarith [mul_nonneg hr.le habs, mul_nonneg (mul_nonneg hr.le habs) hL'.le]

lemma displacements_subset_square (L : ℕ) : displacements L ⊆ square L := by
  intro d hd
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hd
  rw [mem_square]
  unfold radius displacement
  exact max_le
    (Int.natAbs_coe_sub_coe_le_of_le p.2.1.isLt.le p.1.1.isLt.le)
    (Int.natAbs_coe_sub_coe_le_of_le p.2.2.isLt.le p.1.2.isLt.le)


lemma coordinate_cutoff_iff (L : ℕ) (hL : 0 < L) (r : ℝ) (hr : 0 ≤ r) (z : ℤ) :
    (z.natAbs : ℝ) / L ≤ r ↔ z.natAbs ≤ ⌊r * L⌋₊ := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  rw [div_le_iff₀ hL', Nat.le_floor_iff (mul_nonneg hr hL'.le)]

/-- The two coordinate strips in the requested normalized coordinates. -/
lemma actual_strips_bound (L : ℕ) (hL : 0 < L) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    kernelSum L ((displacements L).filter (fun d => d ≠ 0 ∧
      ((d.1.natAbs : ℝ) / L ≤ r ∨ (d.2.natAbs : ℝ) / L ≤ r))) ≤
      20 * (r * (1 + |Real.log r|) + (1 + Real.log L) / L) := by
  apply (kernelSum_mono L ?_).trans (strips_bound L hL r hr hr1)
  intro d hd
  obtain ⟨hd, hd0, hdr⟩ := mem_filter.mp hd
  apply (mem_strips L ⌊r * L⌋₊ d).mpr
  refine ⟨hd0, (mem_square d L).mp (displacements_subset_square L hd), ?_⟩
  unfold inStrip
  simpa only [coordinate_cutoff_iff L hL r hr.le] using hdr


end GridPairs
end DistanceCounts
end

/-! Finite witness indices inside the unchanged full block/grid index space. -/

noncomputable section

namespace DistanceCounts.FineIndex

open scoped Classical

/-- This only reindexes possible witnesses; it does not modify the ambient configuration. -/
def witnessEquiv {K L : ℕ} (good : Finset (Fin K)) :
    Fin (good.card * L ^ 2) ≃ good × GridPairs.Grid L :=
  (Fintype.equivFinOfCardEq (by
    simp only [Fintype.card_prod, Fintype.card_coe, GridPairs.Grid, Fintype.card_fin, pow_two])).symm

def ambient {K L : ℕ} (good : Finset (Fin K)) (i : Fin (good.card * L ^ 2)) :
    Fin K × GridPairs.Grid L :=
  ⟨(witnessEquiv good i).1.val, (witnessEquiv good i).2⟩

theorem ambient_injective {K L : ℕ} (good : Finset (Fin K)) :
    Function.Injective (ambient (L := L) good) := by
  intro i j hij
  apply (witnessEquiv good).injective
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun x : Fin K × GridPairs.Grid L => x.1) hij
  · exact congrArg (fun x : Fin K × GridPairs.Grid L => x.2) hij

theorem ambient_mem {K L : ℕ} (good : Finset (Fin K)) (i : Fin (good.card * L ^ 2)) :
    (ambient good i).1 ∈ good := (witnessEquiv good i).1.property

def group {K L : ℕ} (good : Finset (Fin K)) (i : Fin (good.card * L ^ 2)) : Fin K × Fin L :=
  ⟨(ambient good i).1, (ambient good i).2.2⟩

end DistanceCounts.FineIndex
end

/-! Lebesgue interval laws, their convolution density, and finite integer periodization. -/

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace DistanceCounts.ProjectionDensity

/-- Lebesgue density of normalized restricted volume on `[0,a)`, for `a > 0`. -/
def box (a : ℝ) : ℝ → ℝ := (Ico 0 a).indicator (fun _ => 1 / a)

/-- The underlying continuous law: scaled restricted Lebesgue measure, not counting measure. -/
def uniformIntervalMeasure (a : ℝ) : Measure ℝ :=
  (ENNReal.ofReal a)⁻¹ • volume.restrict (Ico 0 a)

theorem uniformIntervalMeasure_probability {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (uniformIntervalMeasure a) := by
  constructor
  simp [uniformIntervalMeasure, Measure.smul_apply, ha.ne',
    ENNReal.inv_mul_cancel, ENNReal.ofReal_ne_zero_iff.mpr ha]

/-- Integration against the continuous uniform law is integration against `box`. -/
theorem integral_uniformIntervalMeasure {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) :
    ∫ x, f x ∂uniformIntervalMeasure a = ∫ x, box a x * f x := by
  have he : (fun x => box a x * f x) =
      (Ico 0 a).indicator (fun x => (1 / a) * f x) := by
    funext x
    exact (Set.indicator_mul_left (Ico 0 a) (fun _ => 1 / a) f).symm
  rw [he, integral_indicator measurableSet_Ico, integral_const_mul]
  simp [uniformIntervalMeasure, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal ha.le, smul_eq_mul, one_div]

/-- The explicit convolution of two interval densities. -/
def density (a b x : ℝ) : ℝ :=
  max 0 (min (min a b) (min x (a + b - x))) / (a * b)

theorem measurable_box (a : ℝ) : Measurable (box a) :=
  measurable_const.indicator measurableSet_Ico

theorem box_nonneg {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 ≤ box a x := by
  by_cases hx : x ∈ Ico 0 a <;> simp [box, hx, le_of_lt ha]

theorem box_le {a : ℝ} (ha : 0 < a) (x : ℝ) : box a x ≤ 1 / a := by
  by_cases hx : x ∈ Ico 0 a <;> simp [box, hx, le_of_lt ha]

theorem integrable_box (a : ℝ) : Integrable (box a) := by
  exact (integrableOn_const (by simp : volume (Ico (0 : ℝ) a) ≠ ⊤)).integrable_indicator
    measurableSet_Ico

theorem integral_box {a : ℝ} (ha : 0 < a) : ∫ x, box a x = 1 := by
  simp [box, integral_indicator_const, Real.volume_real_Ico, max_eq_left ha.le,
    ha.ne', smul_eq_mul]


/-- Endpoint choices disappear only almost everywhere, not pointwise. -/
theorem box_product_ae (a b x : ℝ) :
    (fun t => box a t * box b (x - t)) =ᵐ[volume]
      (Ioo (max 0 (x - b)) (min a x)).indicator (fun _ => 1 / (a * b)) := by
  have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by
    apply ae_iff.mpr
    simp
  have hx : ∀ᵐ t : ℝ, t ≠ x := by
    apply ae_iff.mpr
    simp
  filter_upwards [h0, hx] with t ht0 htx
  have hm : (t ∈ Ico 0 a ∧ x - t ∈ Ico 0 b) ↔
      t ∈ Ioo (max 0 (x - b)) (min a x) := by
    simp only [mem_Ico, mem_Ioo, max_lt_iff, lt_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨lt_of_le_of_ne h1 (Ne.symm ht0), by linarith⟩,
        h2, lt_of_le_of_ne (by linarith) htx⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1.le, h3⟩, by linarith, by linarith⟩
  by_cases h1 : t ∈ Ico 0 a <;> by_cases h2 : x - t ∈ Ico 0 b <;>
    simp [box, ← hm, h1, h2, one_div, mul_inv, mul_comm]


theorem overlap_length (a b x : ℝ) :
    min a x - max 0 (x - b) = min (min a b) (min x (a + b - x)) := by
  simp only [min_def, max_def]
  split_ifs <;> linarith

theorem density_eq_integral (a b x : ℝ) :
    density a b x = ∫ t, box a t * box b (x - t) := by
  rw [integral_congr_ae (box_product_ae a b x), integral_indicator_const,
    Real.volume_real_Ioo, overlap_length]
  · simp only [density, smul_eq_mul, div_eq_mul_inv, one_mul, max_comm]
  · exact measurableSet_Ioo

theorem density_eq_convolution (a b : ℝ) :
    density a b = convolution (box a) (box b) (ContinuousLinearMap.mul ℝ ℝ) volume := by
  funext x
  exact density_eq_integral a b x

theorem density_eq_integral_swap (a b x : ℝ) :
    density a b x = ∫ t, box a (x - t) * box b t := by
  rw [density_eq_convolution]
  exact convolution_mul_swap

theorem integrable_density (a b : ℝ) : Integrable (density a b) := by
  rw [density_eq_convolution]
  exact (integrable_box a).integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (integrable_box b)

theorem integral_density {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x, density a b x = 1 := by
  rw [density_eq_convolution, integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (integrable_box a) (integrable_box b), integral_box ha, integral_box hb]
  simp

theorem density_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    0 ≤ density a b x := by
  exact div_nonneg (le_max_left _ _) (mul_pos ha hb).le

theorem density_eq_zero_of_notMem (a b x : ℝ) (hx : x ∉ Icc 0 (a + b)) :
    density a b x = 0 := by
  have h : min (min a b) (min x (a + b - x)) ≤ 0 := by
    have h1 := min_le_right (min a b) (min x (a + b - x))
    have h2 := min_le_left x (a + b - x)
    have h3 := min_le_right x (a + b - x)
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx <;> linarith
  simp [density, max_eq_left h]


theorem continuous_density (a b : ℝ) : Continuous (density a b) := by
  unfold density
  fun_prop

/-- The sharp spatial Lipschitz bound, rather than the also sufficient `2/(a*b)`. -/
theorem density_abs_sub_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    |density a b x - density a b y| ≤ |x - y| / (a * b) := by
  have h1 : |min x (a + b - x) - min y (a + b - y)| ≤ |x - y| := by
    have he : a + b - x - (a + b - y) = -(x - y) := by ring
    simpa only [he, abs_neg, max_self] using
      abs_min_sub_min_le_max x (a + b - x) y (a + b - y)
  have h2 : |min (min a b) (min x (a + b - x)) -
      min (min a b) (min y (a + b - y))| ≤ |x - y| := by
    exact (abs_min_sub_min_le_max _ _ _ _).trans
      (max_le (by simpa using abs_nonneg (x - y)) h1)
  have h3 : |max 0 (min (min a b) (min x (a + b - x))) -
      max 0 (min (min a b) (min y (a + b - y)))| ≤ |x - y| := by
    exact (abs_max_sub_max_le_max _ _ _ _).trans
      (max_le (by simpa using abs_nonneg (x - y)) h2)
  unfold density
  rw [← sub_div, abs_div, abs_of_pos (mul_pos ha hb)]
  exact div_le_div_of_nonneg_right h3 (mul_pos ha hb).le

theorem lipschitzWith_density {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    LipschitzWith (NNReal.mk (a * b)⁻¹ (by positivity)) (density a b) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_mk, div_eq_mul_inv, mul_comm] using
    density_abs_sub_le ha hb x y

/-- Distinct integer translates of an interval of length at most one are disjoint. -/
theorem integer_translate_unique {a s : ℝ} (ha : a ≤ 1) {j k : ℤ}
    (hj : s - (j : ℝ) ∈ Ico 0 a) (hk : s - (k : ℝ) ∈ Ico 0 a) : j = k := by
  have hjk : (j : ℝ) < (k : ℝ) + 1 := by
    have := hj.1
    have := hk.2
    linarith
  have hkj : (k : ℝ) < (j : ℝ) + 1 := by
    have := hk.1
    have := hj.2
    linarith
  have h1 : j < k + 1 := by exact_mod_cast hjk
  have h2 : k < j + 1 := by exact_mod_cast hkj
  omega

theorem sum_box_integer_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (D : Finset ℤ) (s : ℝ) : ∑ k ∈ D, box a (s - (k : ℝ)) ≤ 1 / a := by
  classical
  by_cases h : ∃ k ∈ D, s - (k : ℝ) ∈ Ico 0 a
  · obtain ⟨k, hk, hks⟩ := h
    rw [Finset.sum_eq_single k]
    · exact box_le ha _
    · intro j hj hjk
      have hjs : s - (j : ℝ) ∉ Ico 0 a :=
        fun hjs => hjk (integer_translate_unique ha1 hjs hks)
      simp [box, hjs]
    · exact fun hnot => (hnot hk).elim
  · have hz : ∀ k ∈ D, box a (s - (k : ℝ)) = 0 := by
      intro k hk
      have hks : s - (k : ℝ) ∉ Ico 0 a := fun hks => h ⟨k, hk, hks⟩
      simp [box, hks]
    rw [Finset.sum_eq_zero hz]
    positivity

theorem integrable_box_product_swap {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    Integrable (fun t => box a (x - t) * box b t) := by
  apply ((integrable_box b).const_mul (1 / a)).mono'
  · exact (((measurable_box a).comp (measurable_const.sub measurable_id)).mul
      (measurable_box b)).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (box_nonneg ha _) (box_nonneg hb _))]
    exact mul_le_mul_of_nonneg_right (box_le ha _) (box_nonneg hb _)

/-- Finite periodization needs no consecutiveness assumption on the integer shifts. -/
theorem sum_density_integer_le {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b)
    (D : Finset ℤ) (s : ℝ) : ∑ k ∈ D, density a b (s - (k : ℝ)) ≤ 1 / a := by
  have hi : ∀ k ∈ D, Integrable
      (fun t => box a (s - (k : ℝ) - t) * box b t) :=
    fun k _ => integrable_box_product_swap ha hb _
  calc
    ∑ k ∈ D, density a b (s - (k : ℝ)) =
        ∑ k ∈ D, ∫ t, box a (s - (k : ℝ) - t) * box b t := by
      apply Finset.sum_congr rfl
      intro k hk
      exact density_eq_integral_swap a b _
    _ = ∫ t, ∑ k ∈ D, box a (s - (k : ℝ) - t) * box b t :=
      (integral_finsetSum D hi).symm
    _ ≤ ∫ t, (1 / a) * box b t := by
      apply integral_mono (integrable_finsetSum D hi) ((integrable_box b).const_mul _)
      intro t
      dsimp only
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (box_nonneg hb t)
      simpa only [sub_right_comm] using sum_box_integer_le ha ha1 D (s - t)
    _ = 1 / a := by rw [integral_const_mul, integral_box hb, mul_one]

end DistanceCounts.ProjectionDensity
end

/-! Continuous parameter laws and their averaged pair kernels. No empirical measure or
Riemann-sum assertion is made in this file. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace DistanceCounts.ParameterKernel

open ProjectionDensity

/-- The coordinates are `r ∈ [0,δ)` and `s ∈ [0,1)`, with normalized Lebesgue laws. -/
def parameterMeasure (δ : ℝ) : Measure (ℝ × ℝ) :=
  (uniformIntervalMeasure δ).prod (uniformIntervalMeasure 1)

def projection (δ u v : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 - δ + p.1) * u + (1 + p.2) * v

theorem parameterMeasure_probability {δ : ℝ} (hδ : 0 < δ) :
    IsProbabilityMeasure (parameterMeasure δ) := by
  letI := uniformIntervalMeasure_probability hδ
  letI := uniformIntervalMeasure_probability (by norm_num : (0 : ℝ) < 1)
  unfold parameterMeasure
  infer_instance

/-- The normalized triangular approximate identity. -/
def kernel (h x : ℝ) : ℝ := h⁻¹ * max 0 (1 - |x| / h)

theorem kernel_nonneg {h : ℝ} (hh : 0 < h) (x : ℝ) : 0 ≤ kernel h x := by
  exact mul_nonneg (inv_nonneg.mpr hh.le) (le_max_left _ _)

theorem kernel_le {h : ℝ} (hh : 0 < h) (x : ℝ) : kernel h x ≤ h⁻¹ := by
  unfold kernel
  calc
    h⁻¹ * max 0 (1 - |x| / h) ≤ h⁻¹ * 1 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hh.le)
      exact max_le (by norm_num) (by linarith [div_nonneg (abs_nonneg x) hh.le])
    _ = h⁻¹ := mul_one _

theorem kernel_eq_zero {h x : ℝ} (hh : 0 < h) (hx : h ≤ |x|) :
    kernel h x = 0 := by
  have : 1 ≤ |x| / h := (le_div_iff₀ hh).mpr (by simpa using hx)
  simp [kernel, max_eq_left (by linarith : 1 - |x| / h ≤ 0)]

theorem continuous_kernel (h : ℝ) : Continuous (kernel h) := by
  unfold kernel
  fun_prop

theorem kernel_hasCompactSupport {h : ℝ} (hh : 0 < h) :
    HasCompactSupport (kernel h) := by
  apply HasCompactSupport.intro (K := Icc (-h) h) isCompact_Icc
  intro x hx
  apply kernel_eq_zero hh
  by_contra hn
  exact hx (abs_le.mp (le_of_lt (lt_of_not_ge hn)))

theorem integrable_kernel {h : ℝ} (hh : 0 < h) : Integrable (kernel h) :=
  (continuous_kernel h).integrable_of_hasCompactSupport (kernel_hasCompactSupport hh)

/-- Reuse the already computed convolution, rather than integrate a new tent function. -/
theorem kernel_eq_density {h : ℝ} (hh : 0 < h) (x : ℝ) :
    kernel h x = density h h (x + h) := by
  have hm : min (min h h) (min (x + h) (h + h - (x + h))) = h - |x| := by
    rw [min_self]
    rcases le_total 0 x with hx | hx
    · have hi : min (x + h) (h + h - (x + h)) = h + h - (x + h) :=
        min_eq_right (by linarith)
      have ho : min h (h + h - (x + h)) = h + h - (x + h) :=
        min_eq_right (by linarith)
      rw [hi, ho, abs_of_nonneg hx]
      ring
    · have hi : min (x + h) (h + h - (x + h)) = x + h :=
        min_eq_left (by linarith)
      have ho : min h (x + h) = x + h :=
        min_eq_right (by linarith)
      rw [hi, ho, abs_of_nonpos hx]
      ring
  unfold kernel density
  rw [hm]
  by_cases hx : |x| ≤ h
  · rw [max_eq_right (by apply sub_nonneg.mpr; exact (div_le_one hh).mpr hx),
      max_eq_right (sub_nonneg.mpr hx)]
    field_simp [hh.ne']
    <;> ring
  · have h1 : 1 - |x| / h ≤ 0 := by
      have : 1 ≤ |x| / h := (le_div_iff₀ hh).mpr (by simpa using le_of_not_ge hx)
      linarith
    simp [max_eq_left h1, max_eq_left (by linarith : h - |x| ≤ 0)]

theorem integral_kernel {h : ℝ} (hh : 0 < h) : ∫ x, kernel h x = 1 := by
  simp_rw [kernel_eq_density hh]
  rw [integral_add_right_eq_self, integral_density hh hh]

theorem integral_kernel_translate {h : ℝ} (hh : 0 < h) (z : ℝ) :
    ∫ x, kernel h (x - z) = 1 := by
  rw [integral_sub_right_eq_self, integral_kernel hh]

/-- Interval-integral version of the continuous uniform law. -/
theorem integral_uniform_eq_interval {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) :
    ∫ x, f x ∂uniformIntervalMeasure a = a⁻¹ * ∫ x in (0 : ℝ)..a, f x := by
  rw [integral_uniformIntervalMeasure ha]
  have he : (fun x => box a x * f x) = (Ico 0 a).indicator (fun x => a⁻¹ * f x) := by
    funext x
    simp [box, Set.indicator, one_div]
  rw [he, integral_indicator measurableSet_Ico, integral_const_mul,
    integral_Ico_eq_integral_Ioc, intervalIntegral.integral_of_le ha.le]

/-- An affine image of a continuous uniform law, including negative slopes. -/
theorem integral_uniform_affine {a u : ℝ} (ha : 0 < a) (hu : u ≠ 0)
    (c : ℝ) (f : ℝ → ℝ) :
    (∫ r, f (c + u * r) ∂uniformIntervalMeasure a) =
      ∫ x, box (a * |u|) x * f (c + min (a * u) 0 + x) := by
  have hw : 0 < a * |u| := mul_pos ha (abs_pos.mpr hu)
  rw [← integral_uniformIntervalMeasure hw, integral_uniform_eq_interval ha,
    integral_uniform_eq_interval hw, intervalIntegral.integral_comp_add_mul _ hu,
    intervalIntegral.integral_comp_add_left]
  simp only [mul_zero, add_zero, smul_eq_mul]
  rcases lt_or_gt_of_ne hu with hu | hu
  · rw [abs_of_neg hu, min_eq_left (mul_neg_of_pos_of_neg ha hu).le]
    have he : c + a * u + a * -u = c := by ring
    rw [he, intervalIntegral.integral_symm]
    have he' : c + u * a = c + a * u := by ring
    rw [he']
    field_simp [ha.ne', hu.ne]
    <;> ring
  · rw [abs_of_pos hu, min_eq_right (mul_pos ha hu).le]
    simp only [add_zero]
    have he : c + u * a = c + a * u := by ring
    rw [he]
    field_simp [ha.ne', hu.ne']
    <;> ring

/-- The lower endpoint of the projection interval. -/
def leftEndpoint (δ u v : ℝ) : ℝ :=
  (1 - δ) * u + v + min (δ * u) 0 + min v 0

/-- The density when neither displacement coordinate vanishes. -/
def pairDensity (δ u v x : ℝ) : ℝ :=
  density (δ * |u|) |v| (x - leftEndpoint δ u v)


theorem integrable_pairDensity (δ u v : ℝ) : Integrable (pairDensity δ u v) :=
  (integrable_density _ _).comp_sub_right _


/-- Joint regularity holds on the entire open nondegenerate parameter region. -/
theorem continuousAt_pairDensity {δ u v x : ℝ} (hδ : 0 < δ) (hu : u ≠ 0) (hv : v ≠ 0) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ × ℝ => pairDensity p.1 p.2.1 p.2.2.1 p.2.2.2)
      (δ, u, v, x) := by
  have hden : δ * |u| * |v| ≠ 0 :=
    (mul_pos (mul_pos hδ (abs_pos.mpr hu)) (abs_pos.mpr hv)).ne'
  unfold pairDensity density leftEndpoint
  fun_prop (disch := exact hden)

/-- A spatial error estimate that is uniform when the two widths are bounded below. -/
theorem pairDensity_abs_sub_le {δ u v : ℝ} (hδ : 0 < δ) (hu : u ≠ 0) (hv : v ≠ 0)
    (x y : ℝ) :
    |pairDensity δ u v x - pairDensity δ u v y| ≤ |x - y| / (δ * |u| * |v|) := by
  unfold pairDensity
  simpa only [sub_sub_sub_cancel_right] using density_abs_sub_le
    (mul_pos hδ (abs_pos.mpr hu)) (abs_pos.mpr hv)
    (x - leftEndpoint δ u v) (y - leftEndpoint δ u v)

/-- Fubini and translation identify convolution against every bounded continuous test function. -/
theorem integral_boxes_add (a b c : ℝ) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) :
    (∫ x, box a x * ∫ y, box b y * f (c + x + y)) =
      ∫ z, density a b (z - c) * f z := by
  have hi : Integrable (fun p : ℝ × ℝ =>
      box a p.2 * box b (p.1 - p.2) * f (c + p.1)) (volume.prod volume) := by
    exact ((integrable_box a).convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
      (integrable_box b)).mul_bdd
      (hf.comp (continuous_const.add continuous_fst)).aestronglyMeasurable
      (Eventually.of_forall fun p => hM _)
  symm
  calc
    (∫ z, density a b (z - c) * f z) =
        ∫ z, density a b z * f (c + z) := by
      rw [← integral_add_left_eq_self (f := fun z => density a b (z - c) * f z) c]
      simp only [add_sub_cancel_left]
    _ = ∫ z, ∫ t, box a t * box b (z - t) * f (c + z) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [density_eq_integral, integral_mul_const]
    _ = ∫ t, ∫ z, box a t * box b (z - t) * f (c + z) :=
      integral_integral_swap hi
    _ = ∫ t, box a t * ∫ y, box b y * f (c + t + y) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [← integral_add_right_eq_self
        (fun z => box a t * box b (z - t) * f (c + z)) t]
      simp only [add_sub_cancel_right]
      rw [← integral_const_mul]
      congr 1
      funext y
      have he : c + (y + t) = c + t + y := by ring
      rw [he, mul_assoc]

/-- The actual projection law, tested against arbitrary bounded continuous real functions. -/
theorem integral_projection {δ u v : ℝ} (hδ : 0 < δ) (hu : u ≠ 0) (hv : v ≠ 0)
    {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) :
    (∫ p, f (projection δ u v p) ∂parameterMeasure δ) =
      ∫ x, pairDensity δ u v x * f x := by
  letI := uniformIntervalMeasure_probability hδ
  letI := uniformIntervalMeasure_probability (by norm_num : (0 : ℝ) < 1)
  have hi : Integrable (fun p => f (projection δ u v p)) (parameterMeasure δ) := by
    letI := parameterMeasure_probability hδ
    apply Integrable.of_bound (C := M)
    · exact (hf.comp (by unfold projection; fun_prop)).aestronglyMeasurable
    · exact Eventually.of_forall fun p => hM _
  rw [parameterMeasure, integral_prod _ hi]
  let c := (1 - δ) * u + v
  have houter :
      (∫ r, ∫ s, f (projection δ u v (r, s)) ∂uniformIntervalMeasure 1
          ∂uniformIntervalMeasure δ) =
      ∫ x, box (δ * |u|) x *
        ∫ s, f (c + (min (δ * u) 0 + x) + v * s) ∂uniformIntervalMeasure 1 := by
    convert integral_uniform_affine hδ hu 0
      (fun t => ∫ s, f (c + t + v * s) ∂uniformIntervalMeasure 1) using 1
    · congr 1
      funext r
      congr 1
      funext s
      congr 1
      dsimp [projection, c]
      ring
    · simp only [zero_add]
  rw [houter]
  calc
    (∫ x, box (δ * |u|) x *
        ∫ s, f (c + (min (δ * u) 0 + x) + v * s) ∂uniformIntervalMeasure 1) =
      ∫ x, box (δ * |u|) x *
        ∫ y, box |v| y * f (leftEndpoint δ u v + x + y) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [integral_uniform_affine (by norm_num : (0 : ℝ) < 1) hv]
      simp only [one_mul]
      congr 2
      funext y
      congr 2
      dsimp [leftEndpoint, c]
      ring
    _ = ∫ x, pairDensity δ u v x * f x :=
      integral_boxes_add _ _ _ hf hM

theorem integrable_projection_test {δ : ℝ} (hδ : 0 < δ) (u v : ℝ)
    {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) :
    Integrable (fun p => f (projection δ u v p)) (parameterMeasure δ) := by
  letI := parameterMeasure_probability hδ
  exact Integrable.of_bound (hf.comp (by unfold projection; fun_prop)).aestronglyMeasurable
    M (Eventually.of_forall fun p => hM _)


theorem integral_uniform_kernel_le {a u h : ℝ} (ha : 0 < a) (hu : u ≠ 0)
    (hh : 0 < h) (c z : ℝ) :
    (∫ r, kernel h (c + u * r - z) ∂uniformIntervalMeasure a) ≤ 1 / (a * |u|) := by
  rw [integral_uniform_affine ha hu c (fun t => kernel h (t - z))]
  let d := c + min (a * u) 0 - z
  have he : ∀ x, c + min (a * u) 0 + x - z = d + x := by
    intro x
    dsimp [d]
    ring
  simp_rw [he]
  have hw : 0 < a * |u| := mul_pos ha (abs_pos.mpr hu)
  have hi : Integrable (fun x => box (a * |u|) x * kernel h (d + x)) :=
    (integrable_box _).mul_bdd
      ((continuous_kernel h).comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg hh _)]
        exact kernel_le hh _)
  calc
    (∫ x, box (a * |u|) x * kernel h (d + x)) ≤
        ∫ x, (1 / (a * |u|)) * kernel h (d + x) :=
      integral_mono hi ((integrable_kernel hh).comp_add_left d |>.const_mul _)
        (fun x => mul_le_mul_of_nonneg_right (box_le hw _) (kernel_nonneg hh _))
    _ = 1 / (a * |u|) := by
      rw [integral_const_mul, integral_add_left_eq_self, integral_kernel hh, mul_one]

def averagedKernel (δ u v h z : ℝ) : ℝ :=
  ∫ p, kernel h (projection δ u v p - z) ∂parameterMeasure δ

theorem averagedKernel_nonneg {h : ℝ} (hh : 0 < h) (δ u v z : ℝ) :
    0 ≤ averagedKernel δ u v h z :=
  integral_nonneg fun p => kernel_nonneg hh _

theorem integrable_parameter_kernel {δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h)
    (u v z : ℝ) :
    Integrable (fun p => kernel h (projection δ u v p - z)) (parameterMeasure δ) :=
  integrable_projection_test hδ u v
    ((continuous_kernel h).comp (continuous_id.sub continuous_const))
    (fun x => by
      change ‖kernel h (x - z)‖ ≤ h⁻¹
      rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg hh _)]
      exact kernel_le hh _)

/-- Conditioning on the first coordinate; no hypothesis on the second displacement. -/
theorem averagedKernel_le_left {δ u h : ℝ} (hδ : 0 < δ) (hu : u ≠ 0)
    (hh : 0 < h) (v z : ℝ) :
    averagedKernel δ u v h z ≤ 1 / (δ * |u|) := by
  letI := uniformIntervalMeasure_probability hδ
  letI := uniformIntervalMeasure_probability (by norm_num : (0 : ℝ) < 1)
  have hi := integrable_parameter_kernel hδ hh u v z
  unfold averagedKernel parameterMeasure
  rw [integral_prod_symm _ hi]
  calc
    (∫ s, ∫ r, kernel h (projection δ u v (r, s) - z)
        ∂uniformIntervalMeasure δ ∂uniformIntervalMeasure 1) ≤
        ∫ _ : ℝ, 1 / (δ * |u|) ∂uniformIntervalMeasure 1 := by
      apply integral_mono hi.integral_prod_right (integrable_const _)
      intro s
      change (∫ r, kernel h (projection δ u v (r, s) - z)
        ∂uniformIntervalMeasure δ) ≤ 1 / (δ * |u|)
      calc
        (∫ r, kernel h (projection δ u v (r, s) - z) ∂uniformIntervalMeasure δ) =
            ∫ r, kernel h ((1 - δ) * u + (1 + s) * v + u * r - z)
              ∂uniformIntervalMeasure δ := by
          apply integral_congr_ae
          filter_upwards with r
          apply congrArg (kernel h)
          dsimp [projection]
          ring
        _ ≤ 1 / (δ * |u|) :=
          integral_uniform_kernel_le hδ hu hh ((1 - δ) * u + (1 + s) * v) z
    _ = 1 / (δ * |u|) := by simp

/-- Conditioning on the second coordinate; no hypothesis on the first displacement. -/
theorem averagedKernel_le_right {δ v h : ℝ} (hδ : 0 < δ) (hv : v ≠ 0)
    (hh : 0 < h) (u z : ℝ) :
    averagedKernel δ u v h z ≤ 1 / |v| := by
  letI := uniformIntervalMeasure_probability hδ
  letI := uniformIntervalMeasure_probability (by norm_num : (0 : ℝ) < 1)
  have hi := integrable_parameter_kernel hδ hh u v z
  unfold averagedKernel parameterMeasure
  rw [integral_prod _ hi]
  calc
    (∫ r, ∫ s, kernel h (projection δ u v (r, s) - z)
        ∂uniformIntervalMeasure 1 ∂uniformIntervalMeasure δ) ≤
        ∫ _ : ℝ, 1 / |v| ∂uniformIntervalMeasure δ := by
      apply integral_mono hi.integral_prod_left (integrable_const _)
      intro r
      change (∫ s, kernel h (projection δ u v (r, s) - z)
        ∂uniformIntervalMeasure 1) ≤ 1 / |v|
      calc
        (∫ s, kernel h (projection δ u v (r, s) - z) ∂uniformIntervalMeasure 1) =
            ∫ s, kernel h ((1 - δ + r) * u + v + v * s - z)
              ∂uniformIntervalMeasure 1 := by
          apply integral_congr_ae
          filter_upwards with s
          apply congrArg (kernel h)
          dsimp [projection]
          ring
        _ ≤ 1 / |v| := by
          simpa only [one_mul] using
            integral_uniform_kernel_le (by norm_num : (0 : ℝ) < 1) hv hh
              ((1 - δ + r) * u + v) z
    _ = 1 / |v| := by simp

/-- Uniform in the bandwidth and in an arbitrary real translation, including axial pairs. -/
theorem averagedKernel_le {δ u v h : ℝ} (hδ : 0 < δ) (huv : u ≠ 0 ∨ v ≠ 0)
    (hh : 0 < h) (z : ℝ) :
    averagedKernel δ u v h z ≤ (1 + δ⁻¹) / max |u| |v| := by
  rcases le_total |u| |v| with hcmp | hcmp
  · have hv : v ≠ 0 := by
      intro hv
      simp only [hv, abs_zero, abs_nonpos_iff] at hcmp
      exact huv.elim (fun hu => hu hcmp) (fun hv' => hv' hv)
    rw [max_eq_right hcmp]
    exact (averagedKernel_le_right hδ hv hh u z).trans
      (div_le_div_of_nonneg_right (by have := inv_nonneg.mpr hδ.le; linarith)
        (abs_nonneg v))
  · have hu : u ≠ 0 := by
      intro hu
      simp only [hu, abs_zero, abs_nonpos_iff] at hcmp
      exact huv.elim (fun hu' => hu' hu) (fun hv => hv hcmp)
    rw [max_eq_left hcmp]
    calc
      averagedKernel δ u v h z ≤ 1 / (δ * |u|) := averagedKernel_le_left hδ hu hh v z
      _ = δ⁻¹ / |u| := by simp only [div_eq_mul_inv, mul_inv, one_mul]
      _ ≤ (1 + δ⁻¹) / |u| :=
        div_le_div_of_nonneg_right (by linarith) (abs_nonneg u)

/-- In the non-axial case the parameter average is convolution against the explicit law. -/
theorem averagedKernel_eq_integral {δ u v h : ℝ} (hδ : 0 < δ) (hu : u ≠ 0)
    (hv : v ≠ 0) (hh : 0 < h) (z : ℝ) :
    averagedKernel δ u v h z = ∫ x, pairDensity δ u v x * kernel h (x - z) :=
  integral_projection hδ hu hv
    ((continuous_kernel h).comp (continuous_id.sub continuous_const))
    (fun x => by
      change ‖kernel h (x - z)‖ ≤ h⁻¹
      rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg hh _)]
      exact kernel_le hh _)

/-- A quantitative approximate-identity estimate, uniform in the target. -/
theorem averagedKernel_error {δ u v h : ℝ} (hδ : 0 < δ) (hu : u ≠ 0)
    (hv : v ≠ 0) (hh : 0 < h) (z : ℝ) :
    |averagedKernel δ u v h z - pairDensity δ u v z| ≤ h / (δ * |u| * |v|) := by
  have hD : 0 < δ * |u| * |v| :=
    mul_pos (mul_pos hδ (abs_pos.mpr hu)) (abs_pos.mpr hv)
  have hk : Integrable (fun x => kernel h (x - z)) := (integrable_kernel hh).comp_sub_right z
  have hp : Integrable (fun x => pairDensity δ u v x * kernel h (x - z)) :=
    (integrable_pairDensity _ _ _).mul_bdd
      ((continuous_kernel h).comp (continuous_id.sub continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg hh _)]
        exact kernel_le hh _)
  have he : (∫ x, (pairDensity δ u v x - pairDensity δ u v z) * kernel h (x - z)) =
      averagedKernel δ u v h z - pairDensity δ u v z := by
    simp_rw [sub_mul]
    rw [integral_sub hp (hk.const_mul _), integral_const_mul, integral_kernel_translate hh,
      mul_one, ← averagedKernel_eq_integral hδ hu hv hh]
  rw [← he, ← Real.norm_eq_abs]
  calc
    ‖∫ x, (pairDensity δ u v x - pairDensity δ u v z) * kernel h (x - z)‖ ≤
        ∫ x, (h / (δ * |u| * |v|)) * kernel h (x - z) := by
      apply norm_integral_le_of_norm_le (hk.const_mul _)
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_nonneg hh _)]
      by_cases hx : |x - z| ≤ h
      · exact mul_le_mul_of_nonneg_right
          ((pairDensity_abs_sub_le hδ hu hv x z).trans
            (div_le_div_of_nonneg_right hx hD.le)) (kernel_nonneg hh _)
      · rw [kernel_eq_zero hh (le_of_not_ge hx)]
        simp
    _ = h / (δ * |u| * |v|) := by
      rw [integral_const_mul, integral_kernel_translate hh, mul_one]

/-- Perturbations and smoothing errors are simultaneous, not iterated limits. -/
theorem averagedKernel_perturbed_error {δ u v h : ℝ} (hδ : 0 < δ) (hu : u ≠ 0)
    (hv : v ≠ 0) (hh : 0 < h) (z e : ℝ) :
    |averagedKernel δ u v h (z + e) - pairDensity δ u v z| ≤
      (h + |e|) / (δ * |u| * |v|) := by
  calc
    |averagedKernel δ u v h (z + e) - pairDensity δ u v z| ≤
        |averagedKernel δ u v h (z + e) - pairDensity δ u v (z + e)| +
          |pairDensity δ u v (z + e) - pairDensity δ u v z| := abs_sub_le _ _ _
    _ ≤ h / (δ * |u| * |v|) + |e| / (δ * |u| * |v|) := by
      apply add_le_add (averagedKernel_error hδ hu hv hh _)
      simpa only [add_sub_cancel_left] using pairDensity_abs_sub_le hδ hu hv (z + e) z
    _ = (h + |e|) / (δ * |u| * |v|) := (add_div _ _ _).symm

/-- Uniform error on every region a positive distance from either coordinate axis.
No upper bound on the displacements or target is necessary for this estimate. -/
theorem averagedKernel_uniform_error {δ η u v h : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hu : η ≤ |u|) (hv : η ≤ |v|) (hh : 0 < h) (z e : ℝ) :
    |averagedKernel δ u v h (z + e) - pairDensity δ u v z| ≤
      (h + |e|) / (δ * η * η) := by
  have hu0 : u ≠ 0 := abs_pos.mp (hη.trans_le hu)
  have hv0 : v ≠ 0 := abs_pos.mp (hη.trans_le hv)
  have hD : δ * η * η ≤ δ * |u| * |v| :=
    mul_le_mul (mul_le_mul_of_nonneg_left hu hδ.le) hv hη.le
      (mul_nonneg hδ.le (abs_nonneg u))
  exact (averagedKernel_perturbed_error hδ hu0 hv0 hh z e).trans
    (div_le_div_of_nonneg_left (add_nonneg hh.le (abs_nonneg e))
      (mul_pos (mul_pos hδ hη) hη) hD)

/-- Joint limit in bandwidth and translation perturbation for a nondegenerate fixed pair. -/
theorem tendsto_averagedKernel {ι : Type*} {l : Filter ι} {δ u v : ℝ}
    (hδ : 0 < δ) (hu : u ≠ 0) (hv : v ≠ 0) (z : ℝ)
    {h e : ι → ℝ} (hh : ∀ᶠ i in l, 0 < h i)
    (hh0 : Tendsto h l (𝓝 0)) (he0 : Tendsto e l (𝓝 0)) :
    Tendsto (fun i => averagedKernel δ u v (h i) (z + e i)) l
      (𝓝 (pairDensity δ u v z)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _)
  · filter_upwards [hh] with i hi
    simpa only [Real.norm_eq_abs] using averagedKernel_perturbed_error hδ hu hv hi z (e i)
  · have habs : Tendsto (fun i => |e i|) l (𝓝 (0 : ℝ)) := by
      simpa only [abs_zero] using he0.abs
    simpa only [zero_add, zero_div] using
      (hh0.add habs).div_const (δ * |u| * |v|)

/- The remaining mesoscopic theorem must connect these continuous parameter averages to
the empirical pair measures, justify the off-axis Riemann sums, and control the discarded
near-diagonal/near-axis pairs. No such empirical convergence or final L² assertion is
included among the conclusions above. -/

end DistanceCounts.ParameterKernel
end

/-! Finite empirical box smoothing with Lebesgue measure. -/

noncomputable section

open Set MeasureTheory

namespace DistanceCounts.EmpiricalEnergy

open ProjectionDensity

/-- Translate a half-open box without changing its endpoint convention. -/
theorem box_translate (h a t : ℝ) :
    box h (t - a) = (Ico a (a + h)).indicator (fun _ => 1 / h) t := by
  have hm : t - a ∈ Ico 0 h ↔ t ∈ Ico a (a + h) := by
    simp only [mem_Ico]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simp only [box, Set.indicator, hm]

/-- Actual interval intersection: no reflection of a half-open interval is used.
Thus this identity is even pointwise, and does not identify differing endpoints. -/
theorem box_overlap (h a b t : ℝ) :
    box h (t - a) * box h (t - b) =
      (Ico (max a b) (min (a + h) (b + h))).indicator (fun _ => 1 / (h * h)) t := by
  have hm : (t ∈ Ico a (a + h) ∧ t ∈ Ico b (b + h)) ↔
      t ∈ Ico (max a b) (min (a + h) (b + h)) := by
    simp only [mem_Ico, max_le_iff, lt_min_iff]
    tauto
  rw [box_translate, box_translate]
  by_cases ha : t ∈ Ico a (a + h) <;> by_cases hb : t ∈ Ico b (b + h) <;>
    simp [Set.indicator, ← hm, ha, hb, one_div, mul_inv]

theorem integrable_box_translate (h a : ℝ) : Integrable (fun t => box h (t - a)) :=
  (integrable_box h).comp_sub_right a

theorem integral_box_translate {h : ℝ} (hh : 0 < h) (a : ℝ) :
    ∫ t, box h (t - a) = 1 := by
  rw [integral_sub_right_eq_self, integral_box hh]

theorem integrable_box_overlap (h a b : ℝ) :
    Integrable (fun t => box h (t - a) * box h (t - b)) := by
  simp_rw [box_overlap]
  exact (integrableOn_const (by simp :
    volume (Ico (max a b) (min (a + h) (b + h))) ≠ ⊤)).integrable_indicator
    measurableSet_Ico

theorem overlap_length (h a b : ℝ) :
    min (a + h) (b + h) - max a b = h - |a - b| := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left (by linarith), max_eq_right hab, abs_of_nonpos (by linarith)]
    ring
  · rw [min_eq_right (by linarith), max_eq_left hba, abs_of_nonneg (by linarith)]
    ring

/-- The exact overlap is the existing normalized triangular kernel. -/
theorem integral_box_overlap {h : ℝ} (hh : 0 < h) (a b : ℝ) :
    (∫ t, box h (t - a) * box h (t - b)) = ParameterKernel.kernel h (a - b) := by
  simp_rw [box_overlap]
  rw [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico, overlap_length]
  simp only [smul_eq_mul, ParameterKernel.kernel]
  by_cases hab : |a - b| ≤ h
  · rw [max_eq_left (sub_nonneg.mpr hab),
      max_eq_right (sub_nonneg.mpr ((div_le_one hh).mpr hab))]
    field_simp [hh.ne']
    <;> ring
  · have h₁ : h - |a - b| ≤ 0 := by linarith
    have h₂ : 1 - |a - b| / h ≤ 0 := by
      have := (le_div_iff₀ hh).mpr (show 1 * h ≤ |a - b| by linarith)
      linarith
    simp [max_eq_right h₁, max_eq_left h₂]

theorem integrable_box_sub_abs (h a b : ℝ) :
    Integrable (fun t => |box h (t - a) - box h (t - b)|) :=
  ((integrable_box_translate h a).sub (integrable_box_translate h b)).abs

/-- The symmetric difference formula uses the actual half-open intervals. -/
theorem box_sub_abs {h : ℝ} (hh : 0 < h) (a b t : ℝ) :
    |box h (t - a) - box h (t - b)| =
      box h (t - a) + box h (t - b) - 2 * h * (box h (t - a) * box h (t - b)) := by
  by_cases ha : t - a ∈ Ico 0 h <;> by_cases hb : t - b ∈ Ico 0 h <;>
    simp [box, ha, hb, abs_of_pos hh, abs_neg] <;>
    field_simp [hh.ne'] <;> ring

theorem integral_box_sub_abs {h : ℝ} (hh : 0 < h) (a b : ℝ) :
    (∫ t, |box h (t - a) - box h (t - b)|) =
      2 - 2 * h * ParameterKernel.kernel h (a - b) := by
  simp_rw [box_sub_abs hh]
  rw [integral_sub
    (f := fun t : ℝ => box h (t - a) + box h (t - b))
    (g := fun t : ℝ => 2 * h * (box h (t - a) * box h (t - b)))
    ((integrable_box_translate h a).add (integrable_box_translate h b))
    ((integrable_box_overlap h a b).const_mul (2 * h)),
    integral_add (f := fun t : ℝ => box h (t - a))
      (g := fun t : ℝ => box h (t - b))
      (integrable_box_translate h a) (integrable_box_translate h b),
    integral_const_mul, integral_box_translate hh, integral_box_translate hh,
    integral_box_overlap hh]
  ring

theorem integral_box_sub_abs_le {h : ℝ} (hh : 0 < h) (a b : ℝ) :
    (∫ t, |box h (t - a) - box h (t - b)|) ≤ 2 * |a - b| / h := by
  rw [integral_box_sub_abs hh]
  have hk : 1 - h * ParameterKernel.kernel h (a - b) ≤ |a - b| / h := by
    unfold ParameterKernel.kernel
    rw [← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
    linarith [le_max_right (0 : ℝ) (1 - |a - b| / h)]
  calc
    2 - 2 * h * ParameterKernel.kernel h (a - b) =
        2 * (1 - h * ParameterKernel.kernel h (a - b)) := by ring
    _ ≤ 2 * (|a - b| / h) := mul_le_mul_of_nonneg_left hk (by norm_num)
    _ = 2 * |a - b| / h := by ring

section Finite

variable {I : Type*} [Fintype I]

/-- The actual finite empirical density, with one box of mass one per center. -/
def smoothed (z : I → ℝ) (h t : ℝ) : ℝ :=
  (Fintype.card I : ℝ)⁻¹ * ∑ i, box h (t - z i)

theorem smoothed_nonneg (z : I → ℝ) {h : ℝ} (hh : 0 < h) (t : ℝ) :
    0 ≤ smoothed z h t := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun i _ => box_nonneg hh _

theorem integrable_smoothed (z : I → ℝ) (h : ℝ) : Integrable (smoothed z h) := by
  exact (integrable_finsetSum Finset.univ
    (fun i _ => integrable_box_translate h (z i))).const_mul _

theorem integral_smoothed [Nonempty I] (z : I → ℝ) {h : ℝ} (hh : 0 < h) :
    ∫ t, smoothed z h t = 1 := by
  have hn : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty I)).ne'
  unfold smoothed
  rw [integral_const_mul, integral_finsetSum Finset.univ
    (fun i _ => integrable_box_translate h (z i))]
  simp [integral_box_translate hh, hn]

/-- Finite expansion, before taking any integral. -/
theorem smoothed_sq (z : I → ℝ) (h t : ℝ) :
    smoothed z h t ^ 2 = (Fintype.card I : ℝ)⁻¹ ^ 2 *
      ∑ i, ∑ j, box h (t - z i) * box h (t - z j) := by
  classical
  unfold smoothed
  rw [mul_pow]
  congr 1
  rw [pow_two, Finset.sum_mul_sum]

theorem integrable_smoothed_sq (z : I → ℝ) (h : ℝ) :
    Integrable (fun t => smoothed z h t ^ 2) := by
  simp_rw [smoothed_sq]
  exact (integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      integrable_box_overlap h (z i) (z j)))).const_mul _

/-- Exact Lebesgue self-energy, including the diagonal pairs. -/
theorem integral_smoothed_sq (z : I → ℝ) {h : ℝ} (hh : 0 < h) :
    (∫ t, smoothed z h t ^ 2) = (Fintype.card I : ℝ)⁻¹ ^ 2 *
      ∑ i, ∑ j, ParameterKernel.kernel h (z i - z j) := by
  simp_rw [smoothed_sq]
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => integrable_box_overlap h (z i) (z j)))]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum Finset.univ (fun j _ => integrable_box_overlap h (z i) (z j))]
  simp_rw [integral_box_overlap hh]

theorem integrable_smoothed_sub_abs (z w : I → ℝ) (h : ℝ) :
    Integrable (fun t => |smoothed z h t - smoothed w h t|) :=
  ((integrable_smoothed z h).sub (integrable_smoothed w h)).abs

/-- A sharper version retaining the mean displacement rather than its maximum. -/
theorem integral_smoothed_sub_abs_le_mean (z w : I → ℝ) {h : ℝ} (hh : 0 < h) :
    (∫ t, |smoothed z h t - smoothed w h t|) ≤
      (Fintype.card I : ℝ)⁻¹ * ∑ i, 2 * |z i - w i| / h := by
  classical
  calc
    (∫ t, |smoothed z h t - smoothed w h t|) ≤
        ∫ t, (Fintype.card I : ℝ)⁻¹ * ∑ i, |box h (t - z i) - box h (t - w i)| := by
      apply integral_mono (integrable_smoothed_sub_abs z w h)
        ((integrable_finsetSum Finset.univ
          (fun i _ => integrable_box_sub_abs h (z i) (w i))).const_mul _)
      intro t
      simp only [smoothed, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
        abs_of_nonneg (show 0 ≤ (Fintype.card I : ℝ)⁻¹ by positivity)]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ = (Fintype.card I : ℝ)⁻¹ * ∑ i, ∫ t, |box h (t - z i) - box h (t - w i)| := by
      rw [integral_const_mul, integral_finsetSum Finset.univ
        (fun i _ => integrable_box_sub_abs h (z i) (w i))]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ => integral_box_sub_abs_le hh (z i) (w i)) (by positivity)

theorem integral_smoothed_sub_abs_le [Nonempty I] (z w : I → ℝ)
    {h τ : ℝ} (hh : 0 < h) (hz : ∀ i, |z i - w i| ≤ τ) :
    (∫ t, |smoothed z h t - smoothed w h t|) ≤ 2 * τ / h := by
  have hn : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty I)).ne'
  calc
    _ ≤ (Fintype.card I : ℝ)⁻¹ * ∑ i, 2 * |z i - w i| / h :=
      integral_smoothed_sub_abs_le_mean z w hh
    _ ≤ (Fintype.card I : ℝ)⁻¹ * ∑ _i : I, 2 * τ / h := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun i _ =>
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hz i) (by norm_num)) hh.le
    _ = _ := by simp [hn, mul_assoc]

end Finite

/-- Integrability of the actual cross-term; global boundedness of the test is unnecessary. -/
theorem integrable_box_test {f : ℝ → ℝ} (hf : Integrable f) {h : ℝ}
    (hh : 0 < h) (a : ℝ) : Integrable (fun t => box h (t - a) * f t) := by
  exact hf.bdd_mul
    ((measurable_box h).comp (measurable_id.sub measurable_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (box_nonneg hh _)]
      exact box_le hh _)

/-- Testing a box against a Lipschitz function costs at most its width times the constant. -/
theorem integral_box_test_error {f : ℝ → ℝ} (hf : Integrable f)
    {K : NNReal} (hLip : LipschitzWith K f) {h : ℝ} (hh : 0 < h) (a : ℝ) :
    |(∫ t, box h (t - a) * f t) - f a| ≤ (K : ℝ) * h := by
  have he : (∫ t, box h (t - a) * (f t - f a)) =
      (∫ t, box h (t - a) * f t) - f a := by
    simp_rw [mul_sub]
    rw [integral_sub (f := fun t : ℝ => box h (t - a) * f t)
      (g := fun t : ℝ => box h (t - a) * f a)
      (integrable_box_test hf hh a)
      ((integrable_box_translate h a).mul_const (f a)), integral_mul_const,
      integral_box_translate hh, one_mul]
  rw [← he, ← Real.norm_eq_abs]
  calc
    ‖∫ t, box h (t - a) * (f t - f a)‖ ≤
        ∫ t, box h (t - a) * ((K : ℝ) * h) := by
      apply norm_integral_le_of_norm_le ((integrable_box_translate h a).mul_const _)
      filter_upwards with t
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (box_nonneg hh _)]
      by_cases ht : t - a ∈ Ico 0 h
      · apply mul_le_mul_of_nonneg_left _ (box_nonneg hh _)
        calc
          |f t - f a| ≤ (K : ℝ) * |t - a| := by
            simpa only [Real.dist_eq] using hLip.dist_le_mul t a
          _ ≤ (K : ℝ) * h := mul_le_mul_of_nonneg_left
            (by rw [abs_of_nonneg ht.1]; exact ht.2.le) K.coe_nonneg
      · simp [box, ht]
    _ = (K : ℝ) * h := by rw [integral_mul_const, integral_box_translate hh, one_mul]

section FiniteTest

variable {I : Type*} [Fintype I]

theorem integrable_smoothed_test (z : I → ℝ) {f : ℝ → ℝ} (hf : Integrable f)
    {h : ℝ} (hh : 0 < h) : Integrable (fun t => smoothed z h t * f t) := by
  simp only [smoothed, mul_assoc, Finset.sum_mul]
  exact (integrable_finsetSum Finset.univ (fun i _ => integrable_box_test hf hh (z i))).const_mul _

theorem integral_smoothed_test (z : I → ℝ) {f : ℝ → ℝ} (hf : Integrable f)
    {h : ℝ} (hh : 0 < h) :
    (∫ t, smoothed z h t * f t) =
      (Fintype.card I : ℝ)⁻¹ * ∑ i, ∫ t, box h (t - z i) * f t := by
  simp only [smoothed, mul_assoc, Finset.sum_mul]
  rw [integral_const_mul, integral_finsetSum Finset.univ
    (fun i _ => integrable_box_test hf hh (z i))]

/-- The cross-term estimate for the actual finite empirical average. -/
theorem integral_smoothed_test_error [Nonempty I] (z : I → ℝ)
    {f : ℝ → ℝ} (hf : Integrable f) {K : NNReal} (hLip : LipschitzWith K f)
    {h : ℝ} (hh : 0 < h) :
    |(∫ t, smoothed z h t * f t) - (Fintype.card I : ℝ)⁻¹ * ∑ i, f (z i)| ≤
      (K : ℝ) * h := by
  classical
  have hn : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty I)).ne'
  rw [integral_smoothed_test z hf hh, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (show 0 ≤ (Fintype.card I : ℝ)⁻¹ by positivity)]
  calc
    _ ≤ (Fintype.card I : ℝ)⁻¹ *
        ∑ i, |(∫ t, box h (t - z i) * f t) - f (z i)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (Fintype.card I : ℝ)⁻¹ * ∑ _i : I, (K : ℝ) * h :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ => integral_box_test_error hf hLip hh (z i)) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end FiniteTest

end DistanceCounts.EmpiricalEnergy
end

/-! Continuous cubature of the actual half-open square grid.  All distances in this file
are product-metric distances, not Euclidean distances on the plane. -/

noncomputable section

open Set MeasureTheory Filter Finset
open scoped Topology

namespace DistanceCounts.GridQuadrature

abbrev Point := ℝ × ℝ

/-- The actual grid, including the lower and excluding the upper endpoints. -/
def sample (L : ℕ) (p : GridPairs.Grid L) : Point :=
  ((p.1 : ℝ) / L, (p.2 : ℝ) / L)

def gridAverage (L : ℕ) (F : Point → ℝ) : ℝ :=
  (∑ p : GridPairs.Grid L, F (sample L p)) / (L : ℝ) ^ 2

/-- Ordered differences are `q - p`; the diagonal pairs are retained. -/
def gridPairAverage (L : ℕ) (F : Point → ℝ) : ℝ :=
  (∑ p : GridPairs.Grid L × GridPairs.Grid L,
    F (sample L p.2 - sample L p.1)) / (L : ℝ) ^ 4

def unitSquare : Set Point := Set.Icc 0 1 ×ˢ Set.Icc 0 1

def cellCoordinate (L : ℕ) (i : Fin L) (x : ℝ) : ℝ := ((i : ℝ) + x) / L

def cell (L : ℕ) (p : GridPairs.Grid L) (x : Point) : Point :=
  (cellCoordinate L p.1 x.1, cellCoordinate L p.2 x.2)

def pairCell (L : ℕ) (p : GridPairs.Grid L × GridPairs.Grid L)
    (x : Point × Point) : Point × Point := (cell L p.1 x.1, cell L p.2 x.2)

lemma isCompact_unitSquare : IsCompact unitSquare := isCompact_Icc.prod isCompact_Icc

lemma uniform_one_eq_restrict : ProjectionDensity.uniformIntervalMeasure 1 =
    volume.restrict (Icc (0 : ℝ) 1) := by
  simp [ProjectionDensity.uniformIntervalMeasure, restrict_Ico_eq_restrict_Icc]

lemma parameter_one_eq_restrict : ParameterKernel.parameterMeasure 1 =
    volume.restrict unitSquare := by
  rw [ParameterKernel.parameterMeasure, uniform_one_eq_restrict, Measure.prod_restrict]
  rfl

lemma parameter_pair_eq_restrict :
    (ParameterKernel.parameterMeasure 1).prod (ParameterKernel.parameterMeasure 1) =
      volume.restrict (unitSquare ×ˢ unitSquare) := by
  rw [parameter_one_eq_restrict, Measure.prod_restrict]
  rfl

lemma integrable_square {F : Point → ℝ} (hF : Continuous F) :
    Integrable F (ParameterKernel.parameterMeasure 1) := by
  rw [parameter_one_eq_restrict]
  exact hF.continuousOn.integrableOn_compact isCompact_unitSquare

lemma integrable_square_pair {G : Point × Point → ℝ} (hG : Continuous G) :
    Integrable G ((ParameterKernel.parameterMeasure 1).prod
      (ParameterKernel.parameterMeasure 1)) := by
  rw [parameter_pair_eq_restrict]
  exact hG.continuousOn.integrableOn_compact
    (isCompact_unitSquare.prod isCompact_unitSquare)

lemma integrable_difference {F : Point → ℝ} (hF : Continuous F) :
    Integrable (fun x : Point × Point => F (x.2 - x.1))
      ((ParameterKernel.parameterMeasure 1).prod (ParameterKernel.parameterMeasure 1)) :=
  integrable_square_pair (hF.comp (continuous_snd.sub continuous_fst))

/-- A change of variables in each of the `L` adjacent intervals.  This is an exact
partition identity, not a quadrature hypothesis. -/
lemma coordinate_cells (L : ℕ) (hL : 0 < L) {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ x in Icc (0 : ℝ) 1, f x) =
      (∑ i : Fin L, ∫ x in Icc (0 : ℝ) 1, f (cellCoordinate L i x)) / L := by
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hi (i : Fin L) :
      (∫ x in Icc (0 : ℝ) 1, f (cellCoordinate L i x)) =
        L * ∫ x in (i : ℝ) / L..((i : ℝ) + 1) / L, f x := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num :
      (0 : ℝ) ≤ 1)]
    have he : (fun x => f (cellCoordinate L i x)) =
        (fun x => f (x / L + (i : ℝ) / L)) := by
      funext x
      congr 1
      simp [cellCoordinate, add_div, add_comm]
    rw [he, intervalIntegral.integral_comp_div_add f hLr]
    simp only [zero_div, zero_add, smul_eq_mul]
    rw [show (1 : ℝ) / L + (i : ℝ) / L = ((i : ℝ) + 1) / L by ring]
  have hs : (∑ i : Fin L,
      ∫ x in (i : ℝ) / L..((i : ℝ) + 1) / L, f x) =
        ∫ x in (0 : ℝ)..1, f x := by
    rw [Fin.sum_univ_eq_sum_range
      (fun i : ℕ => ∫ x in (i : ℝ) / L..((i : ℝ) + 1) / L, f x)]
    have ht := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ) / L) (n := L)
      (fun k hk => hf.intervalIntegrable (μ := volume) _ _)
    simpa only [Nat.cast_zero, zero_div, Nat.cast_add, Nat.cast_one, div_self hLr] using ht
  simp_rw [hi]
  rw [← Finset.mul_sum, hs, mul_div_cancel_left₀ _ hLr,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc]

section Tensor

variable {A B I J : Type*}
  [MetricSpace A] [MeasureSpace A] [BorelSpace A] [SecondCountableTopology A]
  [LocallyCompactSpace A] [IsLocallyFiniteMeasure (volume : Measure A)]
  [SigmaFinite (volume : Measure A)]
  [MetricSpace B] [MeasureSpace B] [BorelSpace B] [SecondCountableTopology B]
  [LocallyCompactSpace B] [IsLocallyFiniteMeasure (volume : Measure B)]
  [SigmaFinite (volume : Measure B)] [Fintype I] [Fintype J]

/-- Exact cell decompositions tensorize.  Only compactly supported restrictions of
Lebesgue measure are used by its applications below. -/
private lemma tensor_cells {s : Set A} {t : Set B} (hs : IsCompact s) (ht : IsCompact t)
    {a b : ℝ} {c : I → A → A} {d : J → B → B}
    (hc : ∀ i, Continuous (c i)) (hd : ∀ j, Continuous (d j))
    (hca : ∀ f : A → ℝ, Continuous f →
      (∫ x in s, f x) = (∑ i, ∫ x in s, f (c i x)) / a)
    (hdb : ∀ f : B → ℝ, Continuous f →
      (∫ y in t, f y) = (∑ j, ∫ y in t, f (d j y)) / b)
    {F : A × B → ℝ} (hF : Continuous F) :
    (∫ z in s ×ˢ t, F z ∂(volume : Measure A).prod (volume : Measure B)) =
      (∑ p : I × J, ∫ z in s ×ˢ t, F (c p.1 z.1, d p.2 z.2)
        ∂(volume : Measure A).prod (volume : Measure B)) / (a * b) := by
  classical
  have hparam : Continuous (fun x => ∫ y in t, F (x, y)) :=
    continuous_parametric_integral_of_continuous
      (f := fun (x : A) (y : B) => F (x, y)) (μ := volume) hF ht
  have hparam' (i : I) (j : J) :
      Continuous (fun x => ∫ y in t, F (c i x, d j y)) :=
    continuous_parametric_integral_of_continuous
      (f := fun (x : A) (y : B) => F (c i x, d j y)) (μ := volume)
      (hF.comp (((hc i).comp continuous_fst).prodMk ((hd j).comp continuous_snd))) ht
  rw [setIntegral_prod _ (hF.continuousOn.integrableOn_compact (hs.prod ht)), hca _ hparam]
  have hinner (i : I) :
      (∫ x in s, ∫ y in t, F (c i x, y)) =
        (∑ j, ∫ z in s ×ˢ t, F (c i z.1, d j z.2)
          ∂(volume : Measure A).prod (volume : Measure B)) / b := by
    have he (x : A) := hdb (fun y => F (c i x, y))
      (hF.comp (continuous_const.prodMk continuous_id))
    simp_rw [he]
    rw [integral_div, integral_finsetSum _ (fun j hj =>
      (hparam' i j).continuousOn.integrableOn_compact hs)]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    symm
    apply setIntegral_prod
    exact (hF.comp (((hc i).comp continuous_fst).prodMk
      ((hd j).comp continuous_snd))).continuousOn.integrableOn_compact (hs.prod ht)
  simp_rw [hinner]
  rw [← Finset.sum_div, div_div, mul_comm b a, Fintype.sum_prod_type]

end Tensor

lemma square_cells (L : ℕ) (hL : 0 < L) {F : Point → ℝ} (hF : Continuous F) :
    (∫ x, F x ∂ParameterKernel.parameterMeasure 1) =
      (∑ p : GridPairs.Grid L, ∫ x, F (cell L p x)
        ∂ParameterKernel.parameterMeasure 1) / (L : ℝ) ^ 2 := by
  simp_rw [parameter_one_eq_restrict]
  have hμ : (volume : Measure Point) = (volume : Measure ℝ).prod volume := rfl
  simpa only [← hμ, unitSquare, cell, pow_two] using
    tensor_cells isCompact_Icc isCompact_Icc
      (c := cellCoordinate L) (d := cellCoordinate L)
      (fun i => by unfold cellCoordinate; fun_prop)
      (fun i => by unfold cellCoordinate; fun_prop)
      (fun f hf => coordinate_cells L hL hf)
      (fun f hf => coordinate_cells L hL hf) hF

lemma square_pair_cells (L : ℕ) (hL : 0 < L) {G : Point × Point → ℝ}
    (hG : Continuous G) :
    (∫ x, G x ∂(ParameterKernel.parameterMeasure 1).prod
      (ParameterKernel.parameterMeasure 1)) =
      (∑ p : GridPairs.Grid L × GridPairs.Grid L,
        ∫ x, G (pairCell L p x) ∂(ParameterKernel.parameterMeasure 1).prod
          (ParameterKernel.parameterMeasure 1)) / (L : ℝ) ^ 4 := by
  have hd (f : Point → ℝ) (hf : Continuous f) := square_cells L hL hf
  simp_rw [parameter_one_eq_restrict] at hd
  rw [parameter_pair_eq_restrict]
  have hp : (L : ℝ) ^ 2 * (L : ℝ) ^ 2 = (L : ℝ) ^ 4 := by ring
  have hμ : (volume : Measure (Point × Point)) = (volume : Measure Point).prod volume := rfl
  simpa only [← hμ, pairCell, hp] using
    tensor_cells isCompact_unitSquare isCompact_unitSquare
      (c := cell L) (d := cell L)
      (fun p => by unfold cell cellCoordinate; fun_prop)
      (fun p => by unfold cell cellCoordinate; fun_prop) hd hd hG

lemma cellCoordinate_mem {L : ℕ} (hL : 0 < L) (i : Fin L) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : cellCoordinate L i x ∈ Icc (0 : ℝ) 1 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hi : (i : ℝ) + 1 ≤ L := by
    exact_mod_cast (Nat.succ_le_iff.mpr i.isLt)
  constructor
  · exact div_nonneg (add_nonneg (by positivity) hx.1) hLr.le
  · apply (div_le_one hLr).mpr
    linarith [hx.2]

lemma sample_mem {L : ℕ} (hL : 0 < L) (p : GridPairs.Grid L) : sample L p ∈ unitSquare := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  simpa [sample, unitSquare, cellCoordinate, and_assoc, and_left_comm, and_comm] using
    And.intro (cellCoordinate_mem hL p.1 h0) (cellCoordinate_mem hL p.2 h0)

lemma cell_mem {L : ℕ} (hL : 0 < L) (p : GridPairs.Grid L) {x : Point}
    (hx : x ∈ unitSquare) : cell L p x ∈ unitSquare :=
  ⟨cellCoordinate_mem hL p.1 hx.1, cellCoordinate_mem hL p.2 hx.2⟩

lemma cellCoordinate_dist {L : ℕ} (hL : 0 < L) (i : Fin L) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    dist ((i : ℝ) / L) (cellCoordinate L i x) ≤ (L : ℝ)⁻¹ := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  rw [Real.dist_eq, cellCoordinate, ← sub_div, show (i : ℝ) - (i + x) = -x by ring,
    abs_div, abs_neg, abs_of_nonneg hx.1, abs_of_pos hLr, inv_eq_one_div]
  exact div_le_div_of_nonneg_right hx.2 hLr.le

/-- The product metric is the maximum of the two coordinate distances. -/
lemma sample_cell_dist {L : ℕ} (hL : 0 < L) (p : GridPairs.Grid L) {x : Point}
    (hx : x ∈ unitSquare) : dist (sample L p) (cell L p x) ≤ (L : ℝ)⁻¹ := by
  rw [Prod.dist_eq]
  exact max_le (cellCoordinate_dist hL p.1 hx.1) (cellCoordinate_dist hL p.2 hx.2)

lemma pair_sample_cell_dist {L : ℕ} (hL : 0 < L)
    (p : GridPairs.Grid L × GridPairs.Grid L) {x : Point × Point}
    (hx : x ∈ unitSquare ×ˢ unitSquare) :
    dist (sample L p.1, sample L p.2) (pairCell L p x) ≤ (L : ℝ)⁻¹ := by
  rw [Prod.dist_eq]
  exact max_le (sample_cell_dist hL p.1 hx.1) (sample_cell_dist hL p.2 hx.2)

section Error

variable {X I : Type*} [MeasurableSpace X] [Fintype I]

/-- The elementary coupling estimate for a finite exact cell decomposition. -/
private lemma cell_error {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} {z : I → X} {c : I → X → X} {D E : ℝ}
    (hD : 0 < D) (hcard : (Fintype.card I : ℝ) = D)
    (hc : ∀ i, Integrable (fun x => f (c i x)) μ)
    (hdecomp : (∫ x, f x ∂μ) = (∑ i, ∫ x, f (c i x) ∂μ) / D)
    (herror : ∀ i, ∀ᵐ x ∂μ, |f (z i) - f (c i x)| ≤ E) :
    |(∑ i, f (z i)) / D - ∫ x, f x ∂μ| ≤ E := by
  classical
  have he (i : I) : |f (z i) - ∫ x, f (c i x) ∂μ| ≤ E := by
    have hi := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun x => f (z i) - f (c i x))
      (by simpa only [Real.norm_eq_abs] using herror i)
    simpa only [integral_sub (integrable_const _) (hc i), integral_const,
      Measure.real, measure_univ, ENNReal.toReal_one, one_smul,
      Real.norm_eq_abs, mul_one] using hi
  rw [hdecomp, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hD]
  apply (div_le_iff₀ hD).mpr
  calc
    |∑ i, (f (z i) - ∫ x, f (c i x) ∂μ)| ≤
        ∑ i, |f (z i) - ∫ x, f (c i x) ∂μ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : I, E := Finset.sum_le_sum (fun i hi => he i)
    _ = E * D := by simp [hcard, mul_comm]

end Error

lemma square_ae_mem : ∀ᵐ x ∂ParameterKernel.parameterMeasure 1, x ∈ unitSquare := by
  rw [parameter_one_eq_restrict]
  exact ae_restrict_mem isCompact_unitSquare.measurableSet

lemma square_pair_ae_mem : ∀ᵐ x ∂(ParameterKernel.parameterMeasure 1).prod
    (ParameterKernel.parameterMeasure 1), x ∈ unitSquare ×ˢ unitSquare := by
  rw [parameter_pair_eq_restrict]
  exact ae_restrict_mem (isCompact_unitSquare.prod isCompact_unitSquare).measurableSet

/-- A modulus-of-continuity error bound; useful also for uniformly controlled families. -/
lemma gridAverage_error (L : ℕ) (hL : 0 < L) {F : Point → ℝ} (hF : Continuous F)
    {E : ℝ} (hE : ∀ u ∈ unitSquare, ∀ v ∈ unitSquare,
      dist u v ≤ (L : ℝ)⁻¹ → |F u - F v| ≤ E) :
    |gridAverage L F - ∫ x, F x ∂ParameterKernel.parameterMeasure 1| ≤ E := by
  letI := ParameterKernel.parameterMeasure_probability (by norm_num : (0 : ℝ) < 1)
  apply cell_error (μ := ParameterKernel.parameterMeasure 1)
    (c := cell L) (z := sample L) (by positivity)
    (by simp [GridPairs.Grid, Fintype.card_prod, pow_two])
    (fun p => integrable_square (hF.comp (by unfold cell cellCoordinate; fun_prop)))
    (square_cells L hL hF)
  intro p
  filter_upwards [square_ae_mem] with x hx
  exact hE _ (sample_mem hL p) _ (cell_mem hL p hx) (sample_cell_dist hL p hx)

lemma gridProduct_error (L : ℕ) (hL : 0 < L) {G : Point × Point → ℝ}
    (hG : Continuous G) {E : ℝ}
    (hE : ∀ u ∈ unitSquare ×ˢ unitSquare, ∀ v ∈ unitSquare ×ˢ unitSquare,
      dist u v ≤ (L : ℝ)⁻¹ → |G u - G v| ≤ E) :
    |(∑ p : GridPairs.Grid L × GridPairs.Grid L,
        G (sample L p.1, sample L p.2)) / (L : ℝ) ^ 4 -
      ∫ x, G x ∂(ParameterKernel.parameterMeasure 1).prod
        (ParameterKernel.parameterMeasure 1)| ≤ E := by
  letI := ParameterKernel.parameterMeasure_probability (by norm_num : (0 : ℝ) < 1)
  apply cell_error (μ := (ParameterKernel.parameterMeasure 1).prod
    (ParameterKernel.parameterMeasure 1))
    (c := pairCell L) (z := fun p => (sample L p.1, sample L p.2))
    (by positivity) (by simp [GridPairs.Grid, Fintype.card_prod]; ring)
    (fun p => integrable_square_pair (hG.comp (by unfold pairCell cell cellCoordinate; fun_prop)))
    (square_pair_cells L hL hG)
  intro p
  filter_upwards [square_pair_ae_mem] with x hx
  exact hE _ ⟨sample_mem hL p.1, sample_mem hL p.2⟩
    _ ⟨cell_mem hL p.1 hx.1, cell_mem hL p.2 hx.2⟩ (pair_sample_cell_dist hL p hx)


/-- The four-coordinate cubature theorem keeps every ordered pair. -/
theorem tendsto_gridProduct {G : Point × Point → ℝ} (hG : Continuous G) :
    Tendsto (fun L : ℕ => (∑ p : GridPairs.Grid L × GridPairs.Grid L,
      G (sample L p.1, sample L p.2)) / (L : ℝ) ^ 4) atTop
      (𝓝 (∫ x, G x ∂(ParameterKernel.parameterMeasure 1).prod
        (ParameterKernel.parameterMeasure 1))) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff_le.mp
    ((isCompact_unitSquare.prod isCompact_unitSquare).uniformContinuousOn_of_continuous
      hG.continuousOn) (ε / 2) (half_pos hε)
  have hinv : Tendsto (fun L : ℕ => (L : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hinv.eventually (gt_mem_nhds hδ))
  refine ⟨max N 1, fun L hL => ?_⟩
  have hpos : 0 < L := by omega
  have he := gridProduct_error L hpos hG (E := ε / 2)
    (fun u hu v hv huv => by
      simpa only [Real.dist_eq] using hmod u hu v hv (huv.trans (hN L (by omega)).le))
  exact lt_of_le_of_lt (by simpa only [Real.dist_eq] using he) (half_lt_self hε)

/-- In particular the ordered grid differences converge to the double-square law,
with orientation `v - u` and with no diagonal removed. -/
theorem tendsto_gridPairAverage {F : Point → ℝ} (hF : Continuous F) :
    Tendsto (fun L : ℕ => gridPairAverage L F) atTop
      (𝓝 (∫ u, ∫ v, F (v - u) ∂ParameterKernel.parameterMeasure 1
        ∂ParameterKernel.parameterMeasure 1)) := by
  letI := ParameterKernel.parameterMeasure_probability (by norm_num : (0 : ℝ) < 1)
  have h := tendsto_gridProduct (hF.comp (continuous_snd.sub continuous_fst))
  simp only [Function.comp_def, Pi.sub_apply] at h
  rw [integral_prod _ (integrable_difference hF)] at h
  exact h

/-- Lipschitz constants refer to the product metric. -/
theorem gridAverage_lipschitz_error (L : ℕ) (hL : 0 < L) {F : Point → ℝ}
    {K : NNReal} (hF : LipschitzWith K F) :
    |gridAverage L F - ∫ x, F x ∂ParameterKernel.parameterMeasure 1| ≤ (K : ℝ) / L := by
  apply gridAverage_error L hL hF.continuous
  intro u hu v hv huv
  calc
    |F u - F v| ≤ (K : ℝ) * dist u v := by
      simpa only [Real.dist_eq] using hF.dist_le_mul u v
    _ ≤ (K : ℝ) * (L : ℝ)⁻¹ := mul_le_mul_of_nonneg_left huv K.coe_nonneg
    _ = (K : ℝ) / L := (div_eq_mul_inv _ _).symm


end DistanceCounts.GridQuadrature
end

/-! Integrable near-axis domination in displacement coordinates.  The product norm
below is only an analytic device; pinned distances retain their Euclidean metric. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace DistanceCounts.ProjectionSingularity

/-- The displacement square, equipped with actual planar Lebesgue measure. -/
def differenceSquare : Set (ℝ × ℝ) := Icc (-1) 1 ×ˢ Icc (-1) 1

/-- Lean's inverse is zero at the origin; changing this single value does not
change any Lebesgue integral. -/
def invRadius (z : ℝ × ℝ) : ℝ := 1 / max |z.1| |z.2|

theorem invRadius_eq_inv_norm (z : ℝ × ℝ) : invRadius z = ‖z‖⁻¹ := by
  simp [invRadius, Prod.norm_def, Real.norm_eq_abs, one_div]

theorem invRadius_nonneg (z : ℝ × ℝ) : 0 ≤ invRadius z := by
  rw [invRadius_eq_inv_norm]
  exact inv_nonneg.mpr (norm_nonneg z)

theorem measurable_invRadius : Measurable invRadius := by
  have h : invRadius = fun z : ℝ × ℝ => ‖z‖⁻¹ := funext invRadius_eq_inv_norm
  rw [h]
  exact measurable_norm.inv

/-- The singularity is genuinely locally integrable in dimension two, by the
Haar-measure power theorem with exponent one and constant one. -/
theorem locallyIntegrable_invRadius : LocallyIntegrable invRadius := by
  apply locallyIntegrable_of_norm_le_rpow (C := (1 : ℝ)) (α := (1 : ℝ))
    (by simp : 1 ≤ Module.finrank ℝ (ℝ × ℝ))
    (by norm_num : (1 : ℝ) < Module.finrank ℝ (ℝ × ℝ))
  · exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (invRadius_nonneg z),
        invRadius_eq_inv_norm, Real.rpow_neg_one, one_mul]
  · exact measurable_invRadius.aestronglyMeasurable

theorem isCompact_differenceSquare : IsCompact differenceSquare :=
  isCompact_Icc.prod isCompact_Icc

theorem measurableSet_differenceSquare : MeasurableSet differenceSquare :=
  isCompact_differenceSquare.measurableSet

theorem integrableOn_invRadius : IntegrableOn invRadius differenceSquare :=
  locallyIntegrable_invRadius.integrableOn_isCompact isCompact_differenceSquare

/-- The exceptional axes are the actual coordinate axes, not abstract null sets. -/
def axes : Set (ℝ × ℝ) := {z | z.1 = 0 ∨ z.2 = 0}

theorem volume_fst_axis : volume {z : ℝ × ℝ | z.1 = 0} = 0 := by
  have hs : {z : ℝ × ℝ | z.1 = 0} = ({0} : Set ℝ) ×ˢ univ := by
    ext z
    simp
  rw [hs, Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem volume_snd_axis : volume {z : ℝ × ℝ | z.2 = 0} = 0 := by
  have hs : {z : ℝ × ℝ | z.2 = 0} = univ ×ˢ ({0} : Set ℝ) := by
    ext z
    simp
  rw [hs, Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem volume_axes : volume axes = 0 := by
  change volume ({z : ℝ × ℝ | z.1 = 0} ∪ {z : ℝ × ℝ | z.2 = 0}) = 0
  exact measure_union_null volume_fst_axis volume_snd_axis


/-- The union of the two closed coordinate strips of half-width `r`. -/
def nearAxes (r : ℝ) : Set (ℝ × ℝ) := {z | |z.1| ≤ r ∨ |z.2| ≤ r}


/-- One-dimensional continuous transition from zero at `r` to one at `2*r`. -/
def coordinateCutoff (r u : ℝ) : ℝ := min 1 (max 0 ((|u| - r) / r))

/-- The explicit continuous cutoff away from both coordinate axes. -/
def cutoff (r : ℝ) (z : ℝ × ℝ) : ℝ :=
  coordinateCutoff r z.1 * coordinateCutoff r z.2

theorem continuous_coordinateCutoff (r : ℝ) : Continuous (coordinateCutoff r) := by
  unfold coordinateCutoff
  fun_prop

theorem continuous_cutoff (r : ℝ) : Continuous (cutoff r) :=
  ((continuous_coordinateCutoff r).comp continuous_fst).mul
    ((continuous_coordinateCutoff r).comp continuous_snd)

theorem coordinateCutoff_nonneg (r u : ℝ) : 0 ≤ coordinateCutoff r u :=
  le_min (by norm_num) (le_max_left _ _)

theorem coordinateCutoff_le_one (r u : ℝ) : coordinateCutoff r u ≤ 1 :=
  min_le_left _ _

theorem cutoff_nonneg (r : ℝ) (z : ℝ × ℝ) : 0 ≤ cutoff r z :=
  mul_nonneg (coordinateCutoff_nonneg r z.1) (coordinateCutoff_nonneg r z.2)

theorem cutoff_le_one (r : ℝ) (z : ℝ × ℝ) : cutoff r z ≤ 1 :=
  mul_le_one₀ (coordinateCutoff_le_one r z.1) (coordinateCutoff_nonneg r z.2)
    (coordinateCutoff_le_one r z.2)

theorem coordinateCutoff_eq_zero {r u : ℝ} (hr : 0 < r) (hu : |u| ≤ r) :
    coordinateCutoff r u = 0 := by
  have h : (|u| - r) / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu) hr.le
  simp [coordinateCutoff, max_eq_left h]

theorem coordinateCutoff_eq_one {r u : ℝ} (hr : 0 < r) (hu : 2 * r ≤ |u|) :
    coordinateCutoff r u = 1 := by
  have h : 1 ≤ (|u| - r) / r := (le_div_iff₀ hr).mpr (by linarith)
  exact min_eq_left (h.trans (le_max_right _ _))

theorem cutoff_eq_zero {r : ℝ} (hr : 0 < r) {z : ℝ × ℝ} (hz : z ∈ nearAxes r) :
    cutoff r z = 0 := by
  rcases hz with hu | hv
  · simp [cutoff, coordinateCutoff_eq_zero hr hu]
  · simp [cutoff, coordinateCutoff_eq_zero hr hv]

theorem cutoff_eq_one {r : ℝ} (hr : 0 < r) {z : ℝ × ℝ}
    (hu : 2 * r ≤ |z.1|) (hv : 2 * r ≤ |z.2|) : cutoff r z = 1 := by
  simp [cutoff, coordinateCutoff_eq_one hr hu, coordinateCutoff_eq_one hr hv]

/-- Every nonzero value of the cutoff error lies in the strips of width `2*r`. -/
theorem support_one_sub_cutoff_subset {r : ℝ} (hr : 0 < r) :
    Function.support (fun z : ℝ × ℝ => 1 - cutoff r z) ⊆ nearAxes (2 * r) := by
  intro z hz
  change 1 - cutoff r z ≠ 0 at hz
  by_contra hn
  have hu : 2 * r ≤ |z.1| := le_of_lt (lt_of_not_ge (fun h => hn (Or.inl h)))
  have hv : 2 * r ≤ |z.2| := le_of_lt (lt_of_not_ge (fun h => hn (Or.inr h)))
  exact hz (by rw [cutoff_eq_one hr hu hv, sub_self])

end DistanceCounts.ProjectionSingularity
end

noncomputable section

open Set MeasureTheory Filter Finset
open scoped Topology

namespace DistanceCounts.EmpiricalPairKernel

open ParameterKernel GridQuadrature ProjectionSingularity

/-- The perturbation is a fixed grid function, not a function of the parameters. -/
def center (L : ℕ) (δ : ℝ) (η : GridPairs.Grid L → ℝ)
    (a : ℝ × ℝ) (p : GridPairs.Grid L) : ℝ :=
  projection δ (sample L p).1 (sample L p).2 a + η p

def pairValue (L : ℕ) (δ h : ℝ) (η : GridPairs.Grid L → ℝ)
    (p : GridPairs.Grid L × GridPairs.Grid L) : ℝ :=
  averagedKernel δ (sample L p.2 - sample L p.1).1
    (sample L p.2 - sample L p.1).2 h (η p.1 - η p.2)

/-- The actual parameter average of the normalized ordered pair energy. -/
def energy (L : ℕ) (δ h : ℝ) (η : GridPairs.Grid L → ℝ) : ℝ :=
  ∫ a, (∑ p : GridPairs.Grid L × GridPairs.Grid L,
    kernel h (center L δ η a p.2 - center L δ η a p.1)) / (L : ℝ)^4
    ∂parameterMeasure δ

/-- Cutoff is applied to the unperturbed spatial displacement, before averaging. -/
def cutoffEnergy (L : ℕ) (δ h r : ℝ) (η : GridPairs.Grid L → ℝ) : ℝ :=
  ∫ a, (∑ p : GridPairs.Grid L × GridPairs.Grid L,
    cutoff r (sample L p.2 - sample L p.1) *
      kernel h (center L δ η a p.2 - center L δ η a p.1)) / (L : ℝ)^4
    ∂parameterMeasure δ

def cutoffLimit (δ r : ℝ) (d : ℝ × ℝ) : ℝ :=
  cutoff r d * pairDensity δ d.1 d.2 0

lemma center_sub (L : ℕ) (δ : ℝ) (η : GridPairs.Grid L → ℝ)
    (a : ℝ × ℝ) (p : GridPairs.Grid L × GridPairs.Grid L) :
    center L δ η a p.2 - center L δ η a p.1 =
      projection δ (sample L p.2 - sample L p.1).1
        (sample L p.2 - sample L p.1).2 a - (η p.1 - η p.2) := by
  simp only [center, projection, Prod.fst_sub, Prod.snd_sub]
  ring

/-- Every ordered pair, including every diagonal pair, is retained. -/
theorem energy_formula (L : ℕ) {δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h)
    (η : GridPairs.Grid L → ℝ) :
    energy L δ h η = (∑ p, pairValue L δ h η p) / (L : ℝ)^4 := by
  unfold energy
  simp_rw [center_sub]
  rw [integral_div, integral_finsetSum _ (fun p hp =>
    integrable_parameter_kernel hδ hh _ _ _)]
  rfl

theorem cutoffEnergy_formula (L : ℕ) {δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h)
    (r : ℝ) (η : GridPairs.Grid L → ℝ) :
    cutoffEnergy L δ h r η = (∑ p : GridPairs.Grid L × GridPairs.Grid L,
      cutoff r (sample L p.2 - sample L p.1) * pairValue L δ h η p) /
        (L : ℝ)^4 := by
  unfold cutoffEnergy
  simp_rw [center_sub]
  rw [integral_div, integral_finsetSum _ (fun p hp =>
    (integrable_parameter_kernel hδ hh _ _ _).const_mul _)]
  simp_rw [integral_const_mul]
  rfl

/-- This pair energy is precisely the parameter-averaged empirical Lebesgue L² energy. -/
theorem energy_eq_integral_smoothed_sq (L : ℕ) {δ h : ℝ} (hh : 0 < h)
    (η : GridPairs.Grid L → ℝ) :
    energy L δ h η = ∫ a : ℝ × ℝ,
      (∫ t : ℝ, EmpiricalEnergy.smoothed (center L δ η a) h t ^ 2 ∂volume)
        ∂parameterMeasure δ := by
  unfold energy
  apply integral_congr_ae
  filter_upwards with a
  rw [EmpiricalEnergy.integral_smoothed_sq _ hh, Fintype.sum_prod_type]
  have hs : (∑ p : GridPairs.Grid L, ∑ q : GridPairs.Grid L,
      kernel h (center L δ η a q - center L δ η a p)) =
      ∑ p : GridPairs.Grid L, ∑ q : GridPairs.Grid L,
        kernel h (center L δ η a p - center L δ η a q) := Finset.sum_comm
  rw [hs]
  simp only [GridPairs.Grid, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
    div_eq_mul_inv, mul_pow, mul_inv, inv_pow]
  ring

theorem continuous_cutoffLimit {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) :
    Continuous (cutoffLimit δ r) := by
  apply continuous_iff_continuousAt.mpr
  intro d
  by_cases hu : d.1 = 0
  · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    have he : ∀ᶠ z : ℝ × ℝ in 𝓝 d, |z.1| < r :=
      (continuous_fst.abs.continuousAt).eventually (gt_mem_nhds (by simpa [hu] using hr))
    filter_upwards [he] with z hz
    simp [cutoffLimit, cutoff_eq_zero hr (Or.inl hz.le)]
  · by_cases hv : d.2 = 0
    · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
      have he : ∀ᶠ z : ℝ × ℝ in 𝓝 d, |z.2| < r :=
        (continuous_snd.abs.continuousAt).eventually (gt_mem_nhds (by simpa [hv] using hr))
      filter_upwards [he] with z hz
      simp [cutoffLimit, cutoff_eq_zero hr (Or.inr hz.le)]
    · have hp := (continuousAt_pairDensity (x := 0) hδ hu hv).comp
        (f := fun z : ℝ × ℝ => (δ, z.1, z.2, (0 : ℝ)))
        (show ContinuousAt (fun z : ℝ × ℝ => (δ, z.1, z.2, (0 : ℝ))) d by fun_prop)
      exact (continuous_cutoff r).continuousAt.mul hp

lemma pairValue_nonneg (L : ℕ) (δ : ℝ) {h : ℝ} (hh : 0 < h)
    (η : GridPairs.Grid L → ℝ) (p : GridPairs.Grid L × GridPairs.Grid L) :
    0 ≤ pairValue L δ h η p := averagedKernel_nonneg hh _ _ _ _

lemma perturbation_sub_le {L : ℕ} {η : GridPairs.Grid L → ℝ} {τ : ℝ}
    (hη : ∀ p, |η p| ≤ τ) (p : GridPairs.Grid L × GridPairs.Grid L) :
    |η p.1 - η p.2| ≤ 2 * τ := by
  have ha := abs_sub_le (η p.1) 0 (η p.2)
  simp only [sub_zero, zero_sub, abs_neg] at ha
  linarith [hη p.1, hη p.2]

/-- Quantitative off-axis estimate with no perturbation hypotheses hidden in a bound. -/
theorem cutoff_pair_error {L : ℕ} {δ h r τ : ℝ} (hδ : 0 < δ) (hh : 0 < h)
    (hr : 0 < r) (hτ : 0 ≤ τ) {η : GridPairs.Grid L → ℝ}
    (hη : ∀ p, |η p| ≤ τ) (p : GridPairs.Grid L × GridPairs.Grid L) :
    |cutoff r (sample L p.2 - sample L p.1) * pairValue L δ h η p -
      cutoffLimit δ r (sample L p.2 - sample L p.1)| ≤
      (h + 2 * τ) / (δ * r^2) := by
  let d := sample L p.2 - sample L p.1
  change |cutoff r d * pairValue L δ h η p - cutoff r d * pairDensity δ d.1 d.2 0| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg (cutoff_nonneg r d)]
  by_cases hz : d ∈ nearAxes r
  · rw [cutoff_eq_zero hr hz, zero_mul]
    positivity
  · have hu : r ≤ |d.1| := le_of_lt (lt_of_not_ge (fun hu => hz (Or.inl hu)))
    have hv : r ≤ |d.2| := le_of_lt (lt_of_not_ge (fun hv => hz (Or.inr hv)))
    have he : |pairValue L δ h η p - pairDensity δ d.1 d.2 0| ≤
        (h + 2 * τ) / (δ * r^2) := by
      calc
        _ ≤ (h + |η p.1 - η p.2|) / (δ * r * r) := by
          simpa only [pairValue, d, zero_add] using
            averagedKernel_uniform_error hδ hr hu hv hh 0 (η p.1 - η p.2)
        _ ≤ (h + 2 * τ) / (δ * r^2) := by
          rw [pow_two, ← mul_assoc]
          exact div_le_div_of_nonneg_right
            (show h + |η p.1 - η p.2| ≤ h + 2 * τ by
              linarith [perturbation_sub_le hη p]) (by positivity)
    exact (mul_le_mul_of_nonneg_left he (cutoff_nonneg r d)).trans
      (mul_le_of_le_one_left (by positivity) (cutoff_le_one r d))

theorem cutoffEnergy_error {L : ℕ} (hL : 0 < L) {δ h r τ : ℝ}
    (hδ : 0 < δ) (hh : 0 < h) (hr : 0 < r)
    {η : GridPairs.Grid L → ℝ} (hη : ∀ p, |η p| ≤ τ) :
    |cutoffEnergy L δ h r η - gridPairAverage L (cutoffLimit δ r)| ≤
      (h + 2 * τ) / (δ * r^2) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hτ : 0 ≤ τ := (abs_nonneg _).trans (hη (⟨0, hL⟩, ⟨0, hL⟩))
  rw [cutoffEnergy_formula L hδ hh, gridPairAverage, ← sub_div,
    ← Finset.sum_sub_distrib, abs_div, abs_of_pos (pow_pos hLr 4)]
  apply (div_le_iff₀ (pow_pos hLr 4)).mpr
  calc
    _ ≤ ∑ p : GridPairs.Grid L × GridPairs.Grid L,
        |cutoff r (sample L p.2 - sample L p.1) * pairValue L δ h η p -
          cutoffLimit δ r (sample L p.2 - sample L p.1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : GridPairs.Grid L × GridPairs.Grid L, (h + 2 * τ) / (δ * r^2) :=
      Finset.sum_le_sum fun p hp => cutoff_pair_error hδ hh hr hτ hη p
    _ = _ := by simp [GridPairs.Grid, Fintype.card_prod]; ring

/-- Closed strips of width `2*r`, on the actual displacement support. -/
def stripDisplacements (L : ℕ) (r : ℝ) : Finset (ℤ × ℤ) :=
  (GridPairs.displacements L).filter (fun d => d ≠ 0 ∧
    ((d.1.natAbs : ℝ) / L ≤ 2 * r ∨ (d.2.natAbs : ℝ) / L ≤ 2 * r))

def stripWeight (L : ℕ) (r : ℝ) (d : ℤ × ℤ) : ℝ :=
  if d ≠ 0 ∧ ((d.1.natAbs : ℝ) / L ≤ 2 * r ∨
    (d.2.natAbs : ℝ) / L ≤ 2 * r) then (GridPairs.rho L d)⁻¹ else 0

lemma sample_sub_abs {L : ℕ} (hL : 0 < L)
    (p : GridPairs.Grid L × GridPairs.Grid L) :
    |(sample L p.2 - sample L p.1).1| =
        ((GridPairs.displacement p).1.natAbs : ℝ) / L ∧
    |(sample L p.2 - sample L p.1).2| =
        ((GridPairs.displacement p).2.natAbs : ℝ) / L := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hc (z : ℤ) : (z.natAbs : ℝ) = |(z : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun n : ℤ => (n : ℝ)) (Int.natCast_natAbs z)
  constructor <;>
    simp [sample, ← sub_div, abs_div, abs_of_pos hLr,
      GridPairs.displacement, hc]

lemma sample_sub_radius {L : ℕ} (hL : 0 < L)
    (p : GridPairs.Grid L × GridPairs.Grid L) :
    max |(sample L p.2 - sample L p.1).1| |(sample L p.2 - sample L p.1).2| =
      GridPairs.rho L (GridPairs.displacement p) := by
  rw [(sample_sub_abs hL p).1, (sample_sub_abs hL p).2,
    max_div_div_right (by positivity)]
  simp [GridPairs.rho, GridPairs.radius, Nat.cast_max]

lemma displacement_eq_zero_iff {L : ℕ} (p : GridPairs.Grid L × GridPairs.Grid L) :
    GridPairs.displacement p = 0 ↔ p.1 = p.2 := by
  constructor
  · intro hp
    have h₁ : (p.2.1 : ℤ) - (p.1.1 : ℤ) = 0 := congrArg Prod.fst hp
    have h₂ : (p.2.2 : ℤ) - (p.1.2 : ℤ) = 0 := congrArg Prod.snd hp
    apply Prod.ext
    · apply Fin.ext
      exact (Int.natCast_inj.mp (Int.sub_eq_zero.mp h₁)).symm
    · apply Fin.ext
      exact (Int.natCast_inj.mp (Int.sub_eq_zero.mp h₂)).symm
  · intro hp
    change ((p.2.1 : ℤ) - p.1.1, (p.2.2 : ℤ) - p.1.2) = 0
    rw [hp]
    exact Prod.ext (Int.sub_self _) (Int.sub_self _)

lemma stripWeight_nonneg (L : ℕ) (r : ℝ) (d : ℤ × ℤ) : 0 ≤ stripWeight L r d := by
  unfold stripWeight GridPairs.rho
  split_ifs <;> positivity

lemma stripWeight_sum (L : ℕ) (r : ℝ) :
    (∑ p : GridPairs.Grid L × GridPairs.Grid L,
      stripWeight L r (GridPairs.displacement p)) / (L : ℝ)^4 =
      GridPairs.kernelSum L (stripDisplacements L r) := by
  rw [GridPairs.sum_by_displacement]
  unfold GridPairs.kernelSum stripDisplacements
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  unfold stripWeight
  split_ifs <;> simp [div_eq_mul_inv]

lemma pairValue_diagonal (L : ℕ) {δ h : ℝ} (hδ : 0 < δ)
    (η : GridPairs.Grid L → ℝ) (p : GridPairs.Grid L) :
    pairValue L δ h η (p,p) = h⁻¹ := by
  letI := parameterMeasure_probability hδ
  simp [pairValue, averagedKernel, projection, kernel]

/-- Pointwise diagonal/strip domination, including axial displacements and arbitrary jitter. -/
lemma pair_remainder_le {L : ℕ} (hL : 0 < L) {δ h r : ℝ}
    (hδ : 0 < δ) (hh : 0 < h) (hr : 0 < r)
    (η : GridPairs.Grid L → ℝ) (p : GridPairs.Grid L × GridPairs.Grid L) :
    (1 - cutoff r (sample L p.2 - sample L p.1)) * pairValue L δ h η p ≤
      (if p.1 = p.2 then h⁻¹ else 0) +
        (1 + δ⁻¹) * stripWeight L r (GridPairs.displacement p) := by
  have hC : 0 ≤ 1 + δ⁻¹ := by positivity
  have hK := pairValue_nonneg L δ hh η p
  by_cases hp : p.1 = p.2
  · have he : p = (p.1,p.1) := Prod.ext rfl hp.symm
    rw [he, pairValue_diagonal L hδ]
    simp [stripWeight, GridPairs.displacement, cutoff_eq_zero hr
      (show (0 : ℝ × ℝ) ∈ nearAxes r from Or.inl (by simpa using hr.le))]
  · rw [if_neg hp, zero_add]
    by_cases hc : 1 - cutoff r (sample L p.2 - sample L p.1) = 0
    · rw [hc, zero_mul]
      exact mul_nonneg hC (stripWeight_nonneg _ _ _)
    · have hd : GridPairs.displacement p ≠ 0 :=
        fun hd => hp ((displacement_eq_zero_iff p).mp hd)
      have hs := support_one_sub_cutoff_subset hr hc
      have hs' : ((GridPairs.displacement p).1.natAbs : ℝ) / L ≤ 2 * r ∨
          ((GridPairs.displacement p).2.natAbs : ℝ) / L ≤ 2 * r := by
        simpa only [nearAxes, Set.mem_setOf_eq, (sample_sub_abs hL p).1,
          (sample_sub_abs hL p).2] using hs
      rw [stripWeight, if_pos ⟨hd, hs'⟩]
      have huv : (sample L p.2 - sample L p.1).1 ≠ 0 ∨
          (sample L p.2 - sample L p.1).2 ≠ 0 := by
        by_contra hn
        push_neg at hn
        have hz := sample_sub_radius hL p
        rw [hn.1, hn.2, abs_zero, max_self] at hz
        have hrad : 0 < GridPairs.rho L (GridPairs.displacement p) := by
          unfold GridPairs.rho
          exact div_pos (by exact_mod_cast (GridPairs.radius_pos_iff _).mpr hd)
            (by exact_mod_cast hL)
        linarith
      have hc1 : 1 - cutoff r (sample L p.2 - sample L p.1) ≤ 1 :=
        sub_le_self _ (cutoff_nonneg r (sample L p.2 - sample L p.1))
      calc
        _ ≤ pairValue L δ h η p :=
          mul_le_of_le_one_left hK hc1
        _ ≤ (1 + δ⁻¹) / max |(sample L p.2 - sample L p.1).1|
            |(sample L p.2 - sample L p.1).2| := averagedKernel_le hδ huv hh _
        _ = _ := by rw [sample_sub_radius hL p]; rfl

theorem energy_sub_cutoff_nonneg (L : ℕ) {δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h)
    (r : ℝ) (η : GridPairs.Grid L → ℝ) :
    0 ≤ energy L δ h η - cutoffEnergy L δ h r η := by
  rw [energy_formula L hδ hh, cutoffEnergy_formula L hδ hh, ← sub_div,
    ← Finset.sum_sub_distrib]
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro p hp
  have := mul_nonneg (sub_nonneg.mpr (cutoff_le_one r (sample L p.2 - sample L p.1)))
    (pairValue_nonneg L δ hh η p)
  nlinarith

/-- The genuine diagonal contributes exactly `1/(L²*h)`; all other error is in actual strips. -/
theorem energy_sub_cutoff_le {L : ℕ} (hL : 0 < L) {δ h r : ℝ}
    (hδ : 0 < δ) (hh : 0 < h) (hr : 0 < r) (η : GridPairs.Grid L → ℝ) :
    energy L δ h η - cutoffEnergy L δ h r η ≤
      1 / ((L : ℝ)^2 * h) +
        (1 + δ⁻¹) * GridPairs.kernelSum L (stripDisplacements L r) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  rw [energy_formula L hδ hh, cutoffEnergy_formula L hδ hh, ← sub_div,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ (∑ p : GridPairs.Grid L × GridPairs.Grid L,
        ((if p.1 = p.2 then h⁻¹ else 0) +
          (1 + δ⁻¹) * stripWeight L r (GridPairs.displacement p))) / (L : ℝ)^4 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro p hp
      simpa only [sub_mul, one_mul] using pair_remainder_le hL hδ hh hr η p
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, add_div, mul_div_assoc,
        stripWeight_sum]
      congr 1
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, GridPairs.Grid, Fintype.card_prod,
        Fintype.card_fin, Nat.cast_mul]
      field_simp [hLr.ne', hh.ne']
      <;> ring

/-- Explicit uniform finite remainder. Closed width `2*r` allows exactly `r ≤ 1/2`. -/
theorem energy_sub_cutoff_le_explicit {L : ℕ} (hL : 0 < L) {δ h r : ℝ}
    (hδ : 0 < δ) (hh : 0 < h) (hr : 0 < r) (hr1 : r ≤ 1 / 2)
    (η : GridPairs.Grid L → ℝ) :
    energy L δ h η - cutoffEnergy L δ h r η ≤
      1 / ((L : ℝ)^2 * h) + (1 + δ⁻¹) *
        (20 * ((2 * r) * (1 + |Real.log (2 * r)|) + (1 + Real.log L) / L)) := by
  apply (energy_sub_cutoff_le hL hδ hh hr η).trans
  have hs : (1 + δ⁻¹) * GridPairs.kernelSum L (stripDisplacements L r) ≤
      (1 + δ⁻¹) *
        (20 * ((2 * r) * (1 + |Real.log (2 * r)|) + (1 + Real.log L) / L)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact GridPairs.actual_strips_bound L hL (2 * r) (by positivity) (by linarith)
  linarith

end DistanceCounts.EmpiricalPairKernel
end

/-! The actual difference law of independent uniform points of the unit square. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace DistanceCounts.SquareDifferenceLaw

open ParameterKernel ProjectionDensity ProjectionSingularity

/-- The probability space consists of two independent uniform square points. -/
def doubleSquareMeasure : Measure ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (parameterMeasure 1).prod (parameterMeasure 1)

/-- The actual displacement, with the order matching the ordered grid pairs. -/
def difference (pq : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ := pq.2 - pq.1

theorem measurable_difference : Measurable difference := by
  unfold difference
  fun_prop

def differenceMeasure : Measure (ℝ × ℝ) :=
  Measure.map difference doubleSquareMeasure

def weight (d : ℝ × ℝ) : ℝ := kernel 1 d.1 * kernel 1 d.2

theorem doubleSquareMeasure_probability : IsProbabilityMeasure doubleSquareMeasure := by
  letI := parameterMeasure_probability (by norm_num : (0 : ℝ) < 1)
  unfold doubleSquareMeasure
  infer_instance

theorem differenceMeasure_probability : IsProbabilityMeasure differenceMeasure := by
  letI := doubleSquareMeasure_probability
  exact Measure.isProbabilityMeasure_map measurable_difference.aemeasurable

theorem continuous_weight : Continuous weight :=
  ((continuous_kernel 1).comp continuous_fst).mul
    ((continuous_kernel 1).comp continuous_snd)

theorem weight_nonneg (d : ℝ × ℝ) : 0 ≤ weight d :=
  mul_nonneg (kernel_nonneg (by norm_num) _) (kernel_nonneg (by norm_num) _)

theorem weight_le_one (d : ℝ × ℝ) : weight d ≤ 1 := by
  apply mul_le_one₀
  · simpa using kernel_le (by norm_num : (0 : ℝ) < 1) d.1
  · exact kernel_nonneg (by norm_num) _
  · simpa using kernel_le (by norm_num : (0 : ℝ) < 1) d.2

theorem weight_eq_zero_of_not_mem {d : ℝ × ℝ} (hd : d ∉ differenceSquare) :
    weight d = 0 := by
  have h : ¬ (|d.1| ≤ 1 ∧ |d.2| ≤ 1) := by
    intro hh
    exact hd ⟨abs_le.mp hh.1, abs_le.mp hh.2⟩
  rcases not_and_or.mp h with h | h
  · rw [weight, kernel_eq_zero (by norm_num) (le_of_not_ge h), zero_mul]
  · rw [weight, kernel_eq_zero (by norm_num) (le_of_not_ge h), mul_zero]


/-- The one-dimensional law is extracted from the previously proved projection
formula. Its common translation by one is removed on both sides. -/
theorem integral_scalar_difference {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) :
    (∫ p, f (p.2 - p.1) ∂parameterMeasure 1) = ∫ x, kernel 1 x * f x := by
  have hp := integral_projection (δ := 1) (u := -1) (v := 1)
    (by norm_num) (by norm_num) (by norm_num)
    (f := fun x => f (x - 1)) (hf.comp (continuous_id.sub continuous_const))
    (fun x => hM (x - 1))
  have he (p : ℝ × ℝ) : projection 1 (-1) 1 p - 1 = p.2 - p.1 := by
    dsimp [projection]
    ring
  simp only [he] at hp
  have hd (x : ℝ) : pairDensity 1 (-1) 1 x = density 1 1 x := by
    norm_num [pairDensity, leftEndpoint]
  simp only [hd] at hp
  rw [hp, ← integral_add_right_eq_self (fun x => density 1 1 x * f (x - 1)) 1]
  simp only [add_sub_cancel_right, ← kernel_eq_density (by norm_num : (0 : ℝ) < 1)]

theorem scalar_differenceMeasure_eq :
    Measure.map (fun p : ℝ × ℝ => p.2 - p.1) (parameterMeasure 1) =
      volume.withDensity (fun x => ENNReal.ofReal (kernel 1 x)) := by
  letI := parameterMeasure_probability (by norm_num : (0 : ℝ) < 1)
  letI := isFiniteMeasure_withDensity_ofReal
    (integrable_kernel (by norm_num : (0 : ℝ) < 1)).hasFiniteIntegral
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map (by fun_prop) f.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_kernel 1).measurable.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal
    (kernel_nonneg (by norm_num : (0 : ℝ) < 1) _), smul_eq_mul]
  exact integral_scalar_difference f.continuous (fun x => f.norm_coe_le_norm x)

/-- Regrouping the four original coordinates is a measure-preserving operation;
this is proved by Tonelli, not by assuming transformed independence. -/
def regroup (pq : (ℝ × ℝ) × (ℝ × ℝ)) : (ℝ × ℝ) × (ℝ × ℝ) :=
  ((pq.1.1, pq.2.1), (pq.1.2, pq.2.2))

private theorem lintegral_four (μ : Measure ℝ) [SFinite μ]
    (f : ((ℝ × ℝ) × (ℝ × ℝ)) → ENNReal) (hf : Measurable f) :
    (∫⁻ z, f z ∂(μ.prod μ).prod (μ.prod μ)) =
      ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ d, f ((a, b), (c, d)) ∂μ ∂μ ∂μ ∂μ := by
  rw [lintegral_prod _ hf.aemeasurable]
  calc
    _ = ∫⁻ a, ∫⁻ b, ∫⁻ q, f ((a, b), q) ∂μ.prod μ ∂μ ∂μ :=
      lintegral_prod _ hf.lintegral_prod_right'.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro a
      apply lintegral_congr
      intro b
      exact lintegral_prod _ (hf.comp measurable_prodMk_left).aemeasurable

theorem map_regroup : Measure.map regroup doubleSquareMeasure = doubleSquareMeasure := by
  letI := uniformIntervalMeasure_probability (by norm_num : (0 : ℝ) < 1)
  apply Measure.ext_of_lintegral _
  intro f hf
  rw [lintegral_map hf (by unfold regroup; fun_prop)]
  change (∫⁻ z, f (regroup z)
      ∂((uniformIntervalMeasure 1).prod (uniformIntervalMeasure 1)).prod
        ((uniformIntervalMeasure 1).prod (uniformIntervalMeasure 1))) = _
  rw [lintegral_four (uniformIntervalMeasure 1) (fun z => f (regroup z))
    (hf.comp (by unfold regroup; fun_prop))]
  change _ = ∫⁻ z, f z
    ∂((uniformIntervalMeasure 1).prod (uniformIntervalMeasure 1)).prod
      ((uniformIntervalMeasure 1).prod (uniformIntervalMeasure 1))
  rw [lintegral_four _ _ hf]
  apply lintegral_congr
  intro a
  change (∫⁻ b, ∫⁻ c, ∫⁻ d, f ((a, c), (b, d))
      ∂uniformIntervalMeasure 1 ∂uniformIntervalMeasure 1 ∂uniformIntervalMeasure 1) = _
  have hg : Measurable (fun z : (ℝ × ℝ) × ℝ =>
      f ((a, z.1.2), (z.1.1, z.2))) := hf.comp (by fun_prop)
  exact lintegral_lintegral_swap hg.lintegral_prod_right'.aemeasurable

/-- The joint difference law is the product of the two scalar difference laws. -/
theorem differenceMeasure_eq_prod : differenceMeasure =
    (Measure.map (fun p : ℝ × ℝ => p.2 - p.1) (parameterMeasure 1)).prod
      (Measure.map (fun p : ℝ × ℝ => p.2 - p.1) (parameterMeasure 1)) := by
  letI := parameterMeasure_probability (by norm_num : (0 : ℝ) < 1)
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  change Measure.map difference doubleSquareMeasure =
    Measure.map (Prod.map (fun p : ℝ × ℝ => p.2 - p.1)
      (fun p : ℝ × ℝ => p.2 - p.1)) doubleSquareMeasure
  nth_rw 2 [← map_regroup]
  rw [Measure.map_map (by fun_prop) (by unfold regroup; fun_prop)]
  rfl

/-- Exact planar pushforward density of two independent uniform square points. -/
theorem differenceMeasure_eq_withDensity :
    differenceMeasure = volume.withDensity (fun d => ENNReal.ofReal (weight d)) := by
  rw [differenceMeasure_eq_prod, scalar_differenceMeasure_eq,
    prod_withDensity (continuous_kernel 1).measurable.ennreal_ofReal
      (continuous_kernel 1).measurable.ennreal_ofReal, ← Measure.volume_eq_prod]
  congr 1
  funext d
  exact (ENNReal.ofReal_mul (kernel_nonneg (by norm_num) _)).symm


theorem integrable_weight_invRadius : Integrable (fun d => weight d * invRadius d) := by
  have hi : Integrable (differenceSquare.indicator invRadius) :=
    (integrable_indicator_iff measurableSet_differenceSquare).mpr integrableOn_invRadius
  apply hi.mono' (continuous_weight.measurable.mul measurable_invRadius).aestronglyMeasurable
  apply ae_of_all
  intro d
  change ‖weight d * invRadius d‖ ≤ differenceSquare.indicator invRadius d
  rw [Real.norm_of_nonneg (mul_nonneg (weight_nonneg d) (invRadius_nonneg d))]
  by_cases hd : d ∈ differenceSquare
  · rw [indicator_of_mem hd]
    exact mul_le_of_le_one_left (invRadius_nonneg d) (weight_le_one d)
  · simp [indicator_of_notMem hd, weight_eq_zero_of_not_mem hd]

theorem integrable_invRadius_differenceMeasure : Integrable invRadius differenceMeasure := by
  rw [differenceMeasure_eq_withDensity,
    integrable_withDensity_iff_integrable_smul' continuous_weight.measurable.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simpa only [ENNReal.toReal_ofReal (weight_nonneg _), smul_eq_mul] using
    integrable_weight_invRadius


theorem differenceMeasure_axes : differenceMeasure axes = 0 := by
  rw [differenceMeasure_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _ volume_axes


end DistanceCounts.SquareDifferenceLaw
end

/-! The genuine square projection law and its triangular-kernel energy. -/

noncomputable section

open Set MeasureTheory Filter

namespace DistanceCounts.ContinuumEnergy

open ProjectionDensity ParameterKernel

/-- The ordinary linear projection of the uniform unit square. -/
def dot (a b : ℝ) (u : ℝ × ℝ) : ℝ := a * u.1 + b * u.2

theorem continuous_dot (a b : ℝ) : Continuous (dot a b) := by
  unfold dot
  fun_prop

/-- Removing the common translation from the actual parameter projection law. -/
theorem integral_dot {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) :
    (∫ u, f (dot a b u) ∂parameterMeasure 1) =
      ∫ t, density a b t * f t := by
  have hshift (u : ℝ × ℝ) : projection 1 a b u - b = dot a b u := by
    dsimp [projection, dot]
    ring
  have hpair : pairDensity 1 a b = fun t => density a b (t - b) := by
    funext t
    simp [pairDensity, leftEndpoint, abs_of_pos ha, abs_of_pos hb,
      min_eq_right ha.le, min_eq_right hb.le]
  calc
    (∫ u, f (dot a b u) ∂parameterMeasure 1) =
        ∫ u, f (projection 1 a b u - b) ∂parameterMeasure 1 := by
      simp_rw [hshift]
    _ = ∫ t, pairDensity 1 a b t * f (t - b) :=
      integral_projection (by norm_num) ha.ne' hb.ne'
        (hf.comp (continuous_id.sub continuous_const)) (fun t => hM (t - b))
    _ = ∫ t, density a b t * f t := by
      rw [hpair]
      exact integral_sub_right_eq_self (fun t => density a b t * f t) b


/-- The density bound does not require either side length to be at most one. -/
theorem density_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    density a b t ≤ 1 / a := by
  rw [density_eq_integral_swap]
  calc
    (∫ s, box a (t - s) * box b s) ≤ ∫ s, (1 / a) * box b s :=
      integral_mono (integrable_box_product_swap ha hb t)
        ((integrable_box b).const_mul _) (fun s =>
          mul_le_mul_of_nonneg_right (box_le ha _) (box_nonneg hb _))
    _ = 1 / a := by rw [integral_const_mul, integral_box hb, mul_one]

theorem integrable_density_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun t => density a b t ^ 2) := by
  simpa only [pow_two] using (integrable_density a b).mul_bdd
    (continuous_density a b).aestronglyMeasurable
    (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (density_nonneg ha hb t)]
      exact density_le ha hb t)

/-- Uniform domination for the later parameter integral. -/
theorem integral_density_sq_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t, density a b t ^ 2) ≤ 1 / a := by
  calc
    (∫ t, density a b t ^ 2) ≤ ∫ t, density a b t * (1 / a) := by
      apply integral_mono (integrable_density_sq ha hb) ((integrable_density a b).mul_const _)
      intro t
      change density a b t ^ 2 ≤ density a b t * (1 / a)
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left (density_le ha hb t) (density_nonneg ha hb t)
    _ = 1 / a := by rw [integral_mul_const, integral_density ha hb, one_mul]

/-- The density tested against the actual triangular kernel. -/
def densityKernel (a b h z : ℝ) : ℝ := ∫ t, density a b t * kernel h (t - z)

theorem integrable_density_kernel (a b : ℝ) {h : ℝ} (hh : 0 < h) (z : ℝ) :
    Integrable (fun t => density a b t * kernel h (t - z)) := by
  exact (integrable_density a b).mul_bdd
    ((continuous_kernel h).comp (continuous_id.sub continuous_const)).aestronglyMeasurable
    (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg hh _)]
      exact kernel_le hh _)

theorem densityKernel_eq_convolution (a b h : ℝ) :
    densityKernel a b h =
      convolution (density a b) (kernel h) (ContinuousLinearMap.mul ℝ ℝ) volume := by
  funext z
  rw [convolution_mul]
  unfold densityKernel
  apply integral_congr_ae
  filter_upwards with t
  simp only [kernel, abs_sub_comm]

theorem continuous_densityKernel (a b : ℝ) {h : ℝ} (hh : 0 < h) :
    Continuous (densityKernel a b h) := by
  rw [densityKernel_eq_convolution]
  exact (kernel_hasCompactSupport hh).continuous_convolution_right
    (L := ContinuousLinearMap.mul ℝ ℝ) (integrable_density a b).locallyIntegrable
    (continuous_kernel h)

theorem densityKernel_nonneg {a b h : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (z : ℝ) : 0 ≤ densityKernel a b h z :=
  integral_nonneg fun t => mul_nonneg (density_nonneg ha hb t) (kernel_nonneg hh _)

theorem densityKernel_le {a b h : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (z : ℝ) : densityKernel a b h z ≤ h⁻¹ := by
  calc
    densityKernel a b h z ≤ ∫ t, density a b t * h⁻¹ :=
      integral_mono (integrable_density_kernel a b hh z)
        ((integrable_density a b).mul_const _) (fun t =>
          mul_le_mul_of_nonneg_left (kernel_le hh _) (density_nonneg ha hb t))
    _ = h⁻¹ := by rw [integral_mul_const, integral_density ha hb, one_mul]

/-- Kernel support, mass one, and the sharp density Lipschitz estimate. -/
theorem densityKernel_error {a b h : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (z : ℝ) :
    |densityKernel a b h z - density a b z| ≤ h / (a * b) := by
  have hk : Integrable (fun t => kernel h (t - z)) :=
    (integrable_kernel hh).comp_sub_right z
  have he : (∫ t, (density a b t - density a b z) * kernel h (t - z)) =
      densityKernel a b h z - density a b z := by
    simp_rw [sub_mul]
    rw [integral_sub (integrable_density_kernel a b hh z) (hk.const_mul _),
      integral_const_mul, integral_kernel_translate hh, mul_one]
    rfl
  rw [← he, ← Real.norm_eq_abs]
  calc
    ‖∫ t, (density a b t - density a b z) * kernel h (t - z)‖ ≤
        ∫ t, (h / (a * b)) * kernel h (t - z) := by
      apply norm_integral_le_of_norm_le (hk.const_mul _)
      filter_upwards with t
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_nonneg hh _)]
      by_cases ht : |t - z| ≤ h
      · exact mul_le_mul_of_nonneg_right
          ((density_abs_sub_le ha hb t z).trans
            (div_le_div_of_nonneg_right ht (mul_pos ha hb).le)) (kernel_nonneg hh _)
      · rw [kernel_eq_zero hh (le_of_not_ge ht)]
        simp
    _ = h / (a * b) := by
      rw [integral_const_mul, integral_kernel_translate hh, mul_one]

/-- The genuine double unit-square energy, not a density-side definition. -/
def continuumEnergy (a b h : ℝ) : ℝ :=
  ∫ p, ∫ q, kernel h (dot a b q - dot a b p)
    ∂parameterMeasure 1 ∂parameterMeasure 1

theorem integrable_square_kernel (a b : ℝ) {h : ℝ} (hh : 0 < h) :
    Integrable (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
      kernel h (dot a b pq.2 - dot a b pq.1))
      ((parameterMeasure 1).prod (parameterMeasure 1)) := by
  letI := parameterMeasure_probability (by norm_num : (0 : ℝ) < 1)
  apply Integrable.of_bound (C := h⁻¹)
  · exact ((continuous_kernel h).comp
      (((continuous_dot a b).comp continuous_snd).sub
        ((continuous_dot a b).comp continuous_fst))).aestronglyMeasurable
  · filter_upwards with pq
    rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg hh _)]
    exact kernel_le hh _


theorem continuumEnergy_eq_prod (a b : ℝ) {h : ℝ} (hh : 0 < h) :
    continuumEnergy a b h =
      ∫ pq : (ℝ × ℝ) × (ℝ × ℝ), kernel h (dot a b pq.2 - dot a b pq.1)
        ∂(parameterMeasure 1).prod (parameterMeasure 1) := by
  letI := parameterMeasure_probability (by norm_num : (0 : ℝ) < 1)
  exact (integral_prod _ (integrable_square_kernel a b hh)).symm

theorem integrable_density_energy {a b h : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) : Integrable (fun t => density a b t * densityKernel a b h t) := by
  exact (integrable_density a b).mul_bdd (continuous_densityKernel a b hh).aestronglyMeasurable
    (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (densityKernel_nonneg ha hb hh t)]
      exact densityKernel_le ha hb hh t)

/-- Both square projections are performed against bounded continuous test functions. -/
theorem continuumEnergy_eq_integral {a b h : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) :
    continuumEnergy a b h = ∫ t, density a b t * densityKernel a b h t := by
  have hinner (p : ℝ × ℝ) :
      (∫ q, kernel h (dot a b q - dot a b p) ∂parameterMeasure 1) =
        densityKernel a b h (dot a b p) :=
    integral_dot ha hb ((continuous_kernel h).comp (continuous_id.sub continuous_const))
      (fun t => by
        change ‖kernel h (t - dot a b p)‖ ≤ h⁻¹
        rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg hh _)]
        exact kernel_le hh _)
  unfold continuumEnergy
  simp_rw [hinner]
  exact integral_dot ha hb (continuous_densityKernel a b hh) (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (densityKernel_nonneg ha hb hh t)]
    exact densityKernel_le ha hb hh t)


/-- Quantitative continuum approximation, with no density-law or energy-identity hypothesis. -/
theorem continuumEnergy_error {a b h : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) :
    |continuumEnergy a b h - ∫ t, density a b t ^ 2| ≤ h / (a * b) := by
  rw [continuumEnergy_eq_integral ha hb hh,
    ← integral_sub (integrable_density_energy ha hb hh) (integrable_density_sq ha hb),
    ← Real.norm_eq_abs]
  calc
    ‖∫ t, density a b t * densityKernel a b h t - density a b t ^ 2‖ ≤
        ∫ t, density a b t * (h / (a * b)) := by
      apply norm_integral_le_of_norm_le ((integrable_density a b).mul_const _)
      filter_upwards with t
      rw [show density a b t * densityKernel a b h t - density a b t ^ 2 =
        density a b t * (densityKernel a b h t - density a b t) by ring,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg (density_nonneg ha hb t)]
      exact mul_le_mul_of_nonneg_left (densityKernel_error ha hb hh t)
        (density_nonneg ha hb t)
    _ = h / (a * b) := by rw [integral_mul_const, integral_density ha hb, one_mul]

end DistanceCounts.ContinuumEnergy
end

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace DistanceCounts.ProjectionContinuumLimit

open ParameterKernel ProjectionDensity ProjectionSingularity SquareDifferenceLaw ContinuumEnergy

/-- The limiting pair density is the actual parameter projection density at zero. -/
def limitDensity (δ : ℝ) (d : ℝ × ℝ) : ℝ := pairDensity δ d.1 d.2 0

def limitEnergy (δ : ℝ) : ℝ := ∫ d, limitDensity δ d ∂differenceMeasure

/-- The canonical reference energy, without any alternative density convention. -/
def referenceEnergy (δ : ℝ) (a : ℝ × ℝ) : ℝ :=
  ∫ t, density (1 - δ + a.1) (1 + a.2) t ^ 2

theorem measurable_limitDensity (δ : ℝ) : Measurable (limitDensity δ) := by
  unfold limitDensity pairDensity density leftEndpoint
  fun_prop

theorem limitDensity_nonneg {δ : ℝ} (hδ : 0 < δ) (d : ℝ × ℝ) :
    0 ≤ limitDensity δ d := by
  unfold limitDensity pairDensity density
  exact div_nonneg (le_max_left _ _)
    (mul_nonneg (mul_nonneg hδ.le (abs_nonneg _)) (abs_nonneg _))

theorem ae_difference_coordinates_ne_zero :
    ∀ᵐ d ∂differenceMeasure, d.1 ≠ 0 ∧ d.2 ≠ 0 := by
  have h : ∀ᵐ d ∂differenceMeasure, d ∉ axes := by
    rw [ae_iff]
    simpa using differenceMeasure_axes
  filter_upwards [h] with d hd
  simpa only [axes, mem_setOf_eq, not_or] using hd

private theorem eventually_pos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h :=
  self_mem_nhdsWithin

theorem tendsto_averagedKernel_zero {δ : ℝ} (hδ : 0 < δ)
    {d : ℝ × ℝ} (hu : d.1 ≠ 0) (hv : d.2 ≠ 0) :
    Tendsto (fun h => averagedKernel δ d.1 d.2 h 0) (𝓝[>] 0)
      (𝓝 (limitDensity δ d)) := by
  simpa only [add_zero, limitDensity] using
    tendsto_averagedKernel (h := fun h : ℝ => h) (e := fun _ : ℝ => 0)
      hδ hu hv 0 eventually_pos
      (tendsto_id.mono_left nhdsWithin_le_nhds) tendsto_const_nhds

theorem limitDensity_le {δ : ℝ} (hδ : 0 < δ) {d : ℝ × ℝ}
    (hu : d.1 ≠ 0) (hv : d.2 ≠ 0) :
    limitDensity δ d ≤ (1 + δ⁻¹) * invRadius d := by
  apply le_of_tendsto (tendsto_averagedKernel_zero hδ hu hv)
  filter_upwards [eventually_pos] with h hh
  simpa only [invRadius, div_eq_mul_inv, one_mul] using
    averagedKernel_le hδ (Or.inl hu) hh (0 : ℝ)

theorem ae_limitDensity_le {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ d ∂differenceMeasure, limitDensity δ d ≤ (1 + δ⁻¹) * invRadius d := by
  filter_upwards [ae_difference_coordinates_ne_zero] with d hd
  exact limitDensity_le hδ hd.1 hd.2

theorem integrable_limitDensity {δ : ℝ} (hδ : 0 < δ) :
    Integrable (limitDensity δ) differenceMeasure := by
  apply (integrable_invRadius_differenceMeasure.const_mul (1 + δ⁻¹)).mono'
    (measurable_limitDensity δ).aestronglyMeasurable
  filter_upwards [ae_limitDensity_le hδ] with d hd
  simpa only [Real.norm_of_nonneg (limitDensity_nonneg hδ d)] using hd


theorem tendsto_cutoff {d : ℝ × ℝ} (hu : d.1 ≠ 0) (hv : d.2 ≠ 0) :
    Tendsto (fun r => cutoff r d) (𝓝[>] 0) (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_pos,
    (eventually_lt_nhds (half_pos (abs_pos.mpr hu))).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds (half_pos (abs_pos.mpr hv))).filter_mono nhdsWithin_le_nhds]
    with r hr hru hrv
  exact (cutoff_eq_one hr (by linarith) (by linarith)).symm

theorem tendsto_integral_cutoff_limitDensity {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun r => ∫ d, cutoff r d * limitDensity δ d ∂differenceMeasure)
      (𝓝[>] 0) (𝓝 (limitEnergy δ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (limitDensity δ)
  · exact Eventually.of_forall fun r =>
      ((continuous_cutoff r).measurable.mul (measurable_limitDensity δ)).aestronglyMeasurable
  · exact Eventually.of_forall fun r => ae_of_all _ fun d => by
      rw [Real.norm_of_nonneg (mul_nonneg (cutoff_nonneg r d) (limitDensity_nonneg hδ d))]
      exact mul_le_of_le_one_left (limitDensity_nonneg hδ d) (cutoff_le_one r d)
  · exact integrable_limitDensity hδ
  · filter_upwards [ae_difference_coordinates_ne_zero] with d hd
    simpa only [one_mul] using (tendsto_cutoff hd.1 hd.2).mul_const (limitDensity δ d)

/-- Joint measurability uses the actual bounded triangular kernel. -/
theorem measurable_joint_kernel (δ h : ℝ) :
    Measurable (fun da : (ℝ × ℝ) × (ℝ × ℝ) =>
      kernel h (projection δ da.1.1 da.1.2 da.2)) := by
  apply (continuous_kernel h).measurable.comp
  unfold projection
  fun_prop

theorem measurable_averagedKernel {δ : ℝ} (hδ : 0 < δ) (h : ℝ) :
    Measurable (fun d : ℝ × ℝ => averagedKernel δ d.1 d.2 h 0) := by
  letI := parameterMeasure_probability hδ
  simpa only [averagedKernel, sub_zero] using
    (measurable_joint_kernel δ h).stronglyMeasurable.integral_prod_right'.measurable

theorem integrable_joint_kernel {δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h) :
    Integrable (fun da : (ℝ × ℝ) × (ℝ × ℝ) =>
      kernel h (projection δ da.1.1 da.1.2 da.2))
      (differenceMeasure.prod (parameterMeasure δ)) := by
  letI := differenceMeasure_probability
  letI := parameterMeasure_probability hδ
  apply Integrable.of_bound (measurable_joint_kernel δ h).aestronglyMeasurable (h⁻¹)
  exact ae_of_all _ fun da => by
    rw [Real.norm_of_nonneg (kernel_nonneg hh _)]
    exact kernel_le hh _


theorem tendsto_integral_averagedKernel {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun h => ∫ d, averagedKernel δ d.1 d.2 h 0 ∂differenceMeasure)
      (𝓝[>] 0) (𝓝 (limitEnergy δ)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun d => (1 + δ⁻¹) * invRadius d)
  · exact Eventually.of_forall fun h => (measurable_averagedKernel hδ h).aestronglyMeasurable
  · filter_upwards [eventually_pos] with h hh
    filter_upwards [ae_difference_coordinates_ne_zero] with d hd
    rw [Real.norm_of_nonneg (averagedKernel_nonneg hh _ _ _ _)]
    simpa only [invRadius, div_eq_mul_inv, one_mul] using
      averagedKernel_le hδ (Or.inl hd.1) hh (0 : ℝ)
  · exact integrable_invRadius_differenceMeasure.const_mul _
  · filter_upwards [ae_difference_coordinates_ne_zero] with d hd
    exact tendsto_averagedKernel_zero hδ hd.1 hd.2

/-- Support is proved directly for the normalized restricted Lebesgue laws. -/
theorem ae_parameter_support {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ a ∂parameterMeasure δ, a.1 ∈ Icc 0 δ ∧ a.2 ∈ Icc 0 1 := by
  letI := uniformIntervalMeasure_probability hδ
  letI := uniformIntervalMeasure_probability (by norm_num : (0 : ℝ) < 1)
  have hi (b : ℝ) : ∀ᵐ x ∂uniformIntervalMeasure b, x ∈ Icc 0 b := by
    unfold uniformIntervalMeasure
    apply Measure.ae_smul_measure
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    exact ⟨hx.1, hx.2.le⟩
  unfold parameterMeasure
  apply (Measure.ae_prod_iff_ae_ae
    ((measurable_fst measurableSet_Icc).inter (measurable_snd measurableSet_Icc))).mpr
  filter_upwards [hi δ] with r hr
  filter_upwards [hi 1] with s hs
  exact ⟨hr, hs⟩

theorem measurable_referenceEnergy (δ : ℝ) : Measurable (referenceEnergy δ) := by
  have hm : Measurable (fun z : (ℝ × ℝ) × ℝ =>
      density (1 - δ + z.1.1) (1 + z.1.2) z.2 ^ 2) := by
    unfold density
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem referenceEnergy_nonneg (δ : ℝ) (a : ℝ × ℝ) : 0 ≤ referenceEnergy δ a :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem referenceEnergy_le {δ : ℝ} (hδ1 : δ < 1) {a : ℝ × ℝ}
    (ha : a.1 ∈ Icc 0 δ ∧ a.2 ∈ Icc 0 1) : referenceEnergy δ a ≤ 1 / (1 - δ) := by
  have hα : 0 < 1 - δ + a.1 := by linarith [ha.1.1]
  have hβ : 0 < 1 + a.2 := by linarith [ha.2.1]
  exact (integral_density_sq_le hα hβ).trans
    (one_div_le_one_div_of_le (by linarith) (by linarith [ha.1.1]))

theorem integrable_referenceEnergy {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    Integrable (referenceEnergy δ) (parameterMeasure δ) := by
  letI := parameterMeasure_probability hδ
  apply Integrable.of_bound (measurable_referenceEnergy δ).aestronglyMeasurable (1 / (1 - δ))
  filter_upwards [ae_parameter_support hδ] with a ha
  rw [Real.norm_of_nonneg (referenceEnergy_nonneg δ a)]
  exact referenceEnergy_le hδ1 ha

/-- Transport through the genuine pushforward displacement law. -/
theorem continuumEnergy_eq_difference (δ : ℝ) (a : ℝ × ℝ) {h : ℝ} (hh : 0 < h) :
    continuumEnergy (1 - δ + a.1) (1 + a.2) h =
      ∫ d, kernel h (projection δ d.1 d.2 a) ∂differenceMeasure := by
  rw [continuumEnergy_eq_prod _ _ hh]
  change (∫ pq, kernel h
      (dot (1 - δ + a.1) (1 + a.2) pq.2 - dot (1 - δ + a.1) (1 + a.2) pq.1)
      ∂doubleSquareMeasure) = _
  have hk : Continuous (fun d : ℝ × ℝ => kernel h (projection δ d.1 d.2 a)) := by
    apply (continuous_kernel h).comp
    unfold projection
    fun_prop
  rw [differenceMeasure, integral_map measurable_difference.aemeasurable
    hk.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with pq
  congr 1
  dsimp [dot, projection, difference]
  ring


theorem integrable_parameter_continuumEnergy {δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h) :
    Integrable (fun a : ℝ × ℝ => continuumEnergy (1 - δ + a.1) (1 + a.2) h)
      (parameterMeasure δ) := by
  letI := differenceMeasure_probability
  letI := parameterMeasure_probability hδ
  simp_rw [continuumEnergy_eq_difference δ _ hh]
  exact (integrable_joint_kernel hδ hh).integral_prod_right

/-- Bounded-kernel Fubini, before any limiting operation. -/
theorem integral_averagedKernel_eq_continuumEnergy {δ h : ℝ}
    (hδ : 0 < δ) (hh : 0 < h) :
    (∫ d, averagedKernel δ d.1 d.2 h 0 ∂differenceMeasure) =
      ∫ a, continuumEnergy (1 - δ + a.1) (1 + a.2) h ∂parameterMeasure δ := by
  letI := differenceMeasure_probability
  letI := parameterMeasure_probability hδ
  simp_rw [averagedKernel, sub_zero, continuumEnergy_eq_difference δ _ hh]
  exact integral_integral_swap (integrable_joint_kernel hδ hh)

theorem parameter_continuumEnergy_error {δ h : ℝ} (hδ1 : δ < 1) (hh : 0 < h)
    {a : ℝ × ℝ} (ha : a.1 ∈ Icc 0 δ ∧ a.2 ∈ Icc 0 1) :
    |continuumEnergy (1 - δ + a.1) (1 + a.2) h - referenceEnergy δ a| ≤ h / (1 - δ) := by
  have hα : 0 < 1 - δ + a.1 := by linarith [ha.1.1]
  have hβ : 0 < 1 + a.2 := by linarith [ha.2.1]
  have hab : 1 - δ ≤ (1 - δ + a.1) * (1 + a.2) := by
    nlinarith [ha.1.1, ha.2.1, mul_nonneg hα.le ha.2.1]
  exact (continuumEnergy_error hα hβ hh).trans
    (div_le_div_of_nonneg_left hh.le (by linarith) hab)

theorem integral_parameter_continuumEnergy_error {δ h : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hh : 0 < h) :
    |(∫ a, continuumEnergy (1 - δ + a.1) (1 + a.2) h ∂parameterMeasure δ) -
      ∫ a, referenceEnergy δ a ∂parameterMeasure δ| ≤ h / (1 - δ) := by
  letI := parameterMeasure_probability hδ
  rw [← integral_sub (integrable_parameter_continuumEnergy hδ hh)
    (integrable_referenceEnergy hδ hδ1), ← Real.norm_eq_abs]
  calc
    ‖∫ a, continuumEnergy (1 - δ + a.1) (1 + a.2) h - referenceEnergy δ a
        ∂parameterMeasure δ‖ ≤ ∫ _ : ℝ × ℝ, h / (1 - δ) ∂parameterMeasure δ := by
      apply norm_integral_le_of_norm_le (integrable_const _)
      filter_upwards [ae_parameter_support hδ] with a ha
      simpa only [Real.norm_eq_abs] using parameter_continuumEnergy_error hδ1 hh ha
    _ = h / (1 - δ) := by simp

theorem tendsto_integral_parameter_continuumEnergy {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    Tendsto (fun h => ∫ a, continuumEnergy (1 - δ + a.1) (1 + a.2) h ∂parameterMeasure δ)
      (𝓝[>] 0) (𝓝 (∫ a, referenceEnergy δ a ∂parameterMeasure δ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
  · filter_upwards [eventually_pos] with h hh
    simpa only [Real.norm_eq_abs] using integral_parameter_continuumEnergy_error hδ hδ1 hh
  · have hzero : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [zero_div] using hzero.div_const (1 - δ)

/-- The target is identified from the real parameter law and the real square law;
no continuum-density identity or spectral-limit assumption is an input. -/
theorem limitEnergy_eq_referenceEnergy {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    limitEnergy δ = ∫ a, referenceEnergy δ a ∂parameterMeasure δ := by
  apply tendsto_nhds_unique (tendsto_integral_averagedKernel hδ)
  apply (tendsto_integral_parameter_continuumEnergy hδ hδ1).congr'
  filter_upwards [eventually_pos] with h hh
  exact (integral_averagedKernel_eq_continuumEnergy hδ hh).symm


end DistanceCounts.ProjectionContinuumLimit
end

/-! Mesoscopic empirical energy at bandwidths with only `L² h → ∞`. -/

noncomputable section

namespace DistanceCounts.MesoscopicEnergy

open Filter MeasureTheory Set
open ParameterKernel EmpiricalPairKernel GridQuadrature ProjectionSingularity
open ProjectionContinuumLimit SquareDifferenceLaw
open scoped Topology

def cutoffIntegral (δ r : ℝ) : ℝ :=
  ∫ d, cutoffLimit δ r d ∂differenceMeasure

theorem tendsto_grid_cutoff {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) :
    Tendsto (fun L : ℕ => gridPairAverage L (cutoffLimit δ r)) atTop
      (𝓝 (cutoffIntegral δ r)) := by
  letI := parameterMeasure_probability (by norm_num : (0 : ℝ) < 1)
  have hc := continuous_cutoffLimit hδ hr
  have hq := tendsto_gridPairAverage hc
  rw [← integral_prod _ (integrable_difference hc)] at hq
  have hm : (∫ pq, cutoffLimit δ r (difference pq) ∂doubleSquareMeasure) =
      cutoffIntegral δ r := by
    unfold cutoffIntegral differenceMeasure
    rw [integral_map measurable_difference.aemeasurable hc.aestronglyMeasurable]
  change Tendsto (fun L : ℕ => gridPairAverage L (cutoffLimit δ r)) atTop
    (𝓝 (∫ pq, cutoffLimit δ r (difference pq) ∂doubleSquareMeasure)) at hq
  rw [hm] at hq
  exact hq

theorem tendsto_cutoffIntegral {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (cutoffIntegral δ) (𝓝[>] 0) (𝓝 (limitEnergy δ)) := by
  unfold cutoffIntegral cutoffLimit
  exact tendsto_integral_cutoff_limitDensity hδ

theorem tendsto_cutoffEnergy {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    {h τ : ℕ → ℝ} (η : (L : ℕ) → GridPairs.Grid L → ℝ)
    (hh : ∀ᶠ L in atTop, 0 < h L) (hh0 : Tendsto h atTop (𝓝 0))
    (hτ0 : Tendsto τ atTop (𝓝 0))
    (hη : ∀ᶠ L in atTop, ∀ p, |η L p| ≤ τ L) :
    Tendsto (fun L => cutoffEnergy L δ (h L) r (η L)) atTop
      (𝓝 (cutoffIntegral δ r)) := by
  have hb : Tendsto (fun L => (h L + 2 * τ L) / (δ * r ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add, zero_div] using
      (hh0.add (hτ0.const_mul 2)).div_const (δ * r ^ 2)
  have he : Tendsto (fun L => ‖cutoffEnergy L δ (h L) r (η L) -
      gridPairAverage L (cutoffLimit δ r)‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun L => norm_nonneg _) _ hb
    filter_upwards [hh, hη, eventually_gt_atTop 0] with L hLh hLη hL
    simpa only [Real.norm_eq_abs] using cutoffEnergy_error hL hδ hLh hr hLη
  have hd := tendsto_zero_iff_norm_tendsto_zero.mpr he
  simpa only [sub_add_cancel, zero_add] using hd.add (tendsto_grid_cutoff hδ hr)

def boundary (L : ℕ) : ℝ := (1 + Real.log (L : ℝ)) / L

theorem tendsto_boundary : Tendsto boundary atTop (𝓝 0) := by
  have hl := (isLittleO_log_rpow_rpow_atTop 1 (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hi : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hb : Tendsto (fun x : ℝ => (1 + Real.log x) / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, add_div, one_div, zero_add] using hi.add hl
  exact hb.comp tendsto_natCast_atTop_atTop

/-- This form is continuous even at zero and equals the genuine strip bound for positive radii. -/
def stripTail (δ r : ℝ) : ℝ :=
  20 * (1 + δ⁻¹) * (2 * r + |(2 * r) * Real.log (2 * r)|)

theorem tendsto_stripTail (δ : ℝ) : Tendsto (stripTail δ) (𝓝[>] 0) (𝓝 0) := by
  unfold stripTail
  have hc : Continuous (fun r : ℝ => 20 * (1 + δ⁻¹) *
      (2 * r + |(2 * r) * Real.log (2 * r)|)) :=
    continuous_const.mul ((continuous_const.mul continuous_id).add
      (Real.continuous_mul_log.comp (continuous_const.mul continuous_id)).abs)
  have ht := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa only [stripTail, mul_zero, Real.log_zero, abs_zero, zero_add] using ht

def remainder (δ : ℝ) (h : ℕ → ℝ) (L : ℕ) : ℝ :=
  1 / ((L : ℝ) ^ 2 * h L) + 20 * (1 + δ⁻¹) * boundary L

theorem tendsto_remainder (δ : ℝ) {h : ℕ → ℝ}
    (hg : Tendsto (fun L : ℕ => (L : ℝ) ^ 2 * h L) atTop atTop) :
    Tendsto (remainder δ h) atTop (𝓝 0) := by
  have hd := tendsto_inv_atTop_zero.comp hg
  unfold remainder
  simpa only [Function.comp_def, one_div, mul_zero, zero_add] using
    hd.add (tendsto_boundary.const_mul (20 * (1 + δ⁻¹)))

theorem energy_remainder_le {L : ℕ} (hL : 0 < L) {δ r : ℝ} {h : ℕ → ℝ}
    (hδ : 0 < δ) (hh : 0 < h L) (hr : 0 < r) (hr1 : r ≤ 1 / 2)
    (η : GridPairs.Grid L → ℝ) :
    energy L δ (h L) η - cutoffEnergy L δ (h L) r η ≤
      remainder δ h L + stripTail δ r := by
  apply (energy_sub_cutoff_le_explicit hL hδ hh hr hr1 η).trans_eq
  unfold remainder stripTail boundary
  rw [abs_mul, abs_of_pos (show 0 < 2 * r by positivity)]
  ring

/-- No assumption `L*h → ∞` appears. The diagonal condition is exactly `L²*h → ∞`. -/
theorem tendsto_energy {δ : ℝ} (hδ : 0 < δ)
    {h τ : ℕ → ℝ} (η : (L : ℕ) → GridPairs.Grid L → ℝ)
    (hh : ∀ᶠ L in atTop, 0 < h L) (hh0 : Tendsto h atTop (𝓝 0))
    (hg : Tendsto (fun L : ℕ => (L : ℝ) ^ 2 * h L) atTop atTop)
    (hτ0 : Tendsto τ atTop (𝓝 0))
    (hη : ∀ᶠ L in atTop, ∀ p, |η L p| ≤ τ L) :
    Tendsto (fun L => energy L δ (h L) (η L)) atTop (𝓝 (limitEnergy δ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he : 0 < ε / 4 := by positivity
  have hc := (Metric.tendsto_nhds.mp (tendsto_cutoffIntegral hδ)) (ε / 4) he
  have ht := (tendsto_stripTail δ).eventually (gt_mem_nhds he)
  have hrange : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 / 2 :=
    (show ∀ᶠ r : ℝ in 𝓝 0, r < 1 / 2 from
      gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hr1, hcr, htr⟩ := (hpos.and (hrange.and (hc.and ht))).exists
  have hcut := (Metric.tendsto_nhds.mp
    (tendsto_cutoffEnergy hδ hr η hh hh0 hτ0 hη)) (ε / 4) he
  have hrem := (tendsto_remainder δ hg).eventually (gt_mem_nhds he)
  filter_upwards [hh, eventually_gt_atTop 0, hcut, hrem] with L hLh hL hcL hrL
  have hn := energy_sub_cutoff_nonneg L hδ hLh r (η L)
  have hb := energy_remainder_le hL hδ hLh hr hr1.le (η L)
  have htri := abs_sub_le (energy L δ (h L) (η L))
    (cutoffEnergy L δ (h L) r (η L)) (limitEnergy δ)
  have htri' := abs_sub_le (cutoffEnergy L δ (h L) r (η L))
    (cutoffIntegral δ r) (limitEnergy δ)
  rw [abs_of_nonneg hn] at htri
  rw [Real.dist_eq] at hcL hcr ⊢
  linarith

theorem tendsto_energy_reference {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    {h τ : ℕ → ℝ} (η : (L : ℕ) → GridPairs.Grid L → ℝ)
    (hh : ∀ᶠ L in atTop, 0 < h L) (hh0 : Tendsto h atTop (𝓝 0))
    (hg : Tendsto (fun L : ℕ => (L : ℝ) ^ 2 * h L) atTop atTop)
    (hτ0 : Tendsto τ atTop (𝓝 0))
    (hη : ∀ᶠ L in atTop, ∀ p, |η L p| ≤ τ L) :
    Tendsto (fun L => energy L δ (h L) (η L)) atTop
      (𝓝 (∫ a, referenceEnergy δ a ∂parameterMeasure δ)) := by
  rw [← limitEnergy_eq_referenceEnergy hδ hδ1]
  exact tendsto_energy hδ η hh hh0 hg hτ0 hη

end DistanceCounts.MesoscopicEnergy
end

noncomputable section

open Set MeasureTheory Filter

namespace DistanceCounts.ProjectionCrossTerm

open ProjectionDensity ParameterKernel GridQuadrature ContinuumEnergy EmpiricalEnergy

/-- Fixed, deterministic perturbations of the genuine projected grid. -/
def centers (L : ℕ) (δ : ℝ) (η : GridPairs.Grid L → ℝ)
    (a : ℝ × ℝ) (p : GridPairs.Grid L) : ℝ :=
  projection δ (sample L p).1 (sample L p).2 a + η p

/-- The actual mixed Lebesgue integral, averaged over the parameter law. -/
def crossTerm (L : ℕ) (δ h : ℝ) (η : GridPairs.Grid L → ℝ) : ℝ :=
  ∫ a, ∫ t, smoothed (centers L δ η a) h t *
    density (1 - δ + a.1) (1 + a.2) t ∂volume ∂parameterMeasure δ

/-- Joint measurability is global, including parameters outside the probability support. -/
lemma measurable_cross_integrand (L : ℕ) (δ h : ℝ) (η : GridPairs.Grid L → ℝ) :
    Measurable (fun x : (ℝ × ℝ) × ℝ =>
      smoothed (centers L δ η x.1) h x.2 *
        density (1 - δ + x.1.1) (1 + x.1.2) x.2) := by
  apply Measurable.mul
  · unfold smoothed
    apply Measurable.mul measurable_const
    apply Finset.measurable_sum
    intro p hp
    apply (measurable_box h).comp
    unfold centers projection
    fun_prop
  · unfold density
    fun_prop

lemma measurable_reference_integrand (δ : ℝ) :
    Measurable (fun x : (ℝ × ℝ) × ℝ =>
      density (1 - δ + x.1.1) (1 + x.1.2) x.2 ^ 2) := by
  unfold density
  fun_prop

lemma integrable_cross_section (L : ℕ) (δ : ℝ) {h : ℝ} (hh : 0 < h)
    (η : GridPairs.Grid L → ℝ) (a : ℝ × ℝ) :
    Integrable (fun t => smoothed (centers L δ η a) h t *
      density (1 - δ + a.1) (1 + a.2) t) :=
  integrable_smoothed_test _ (integrable_density _ _) hh

lemma cross_section_nonneg (L : ℕ) (δ : ℝ) {h : ℝ} (hh : 0 < h)
    (η : GridPairs.Grid L → ℝ) {a : ℝ × ℝ}
    (ha : 0 < 1 - δ + a.1) (hb : 0 < 1 + a.2) :
    0 ≤ ∫ t, smoothed (centers L δ η a) h t *
      density (1 - δ + a.1) (1 + a.2) t :=
  integral_nonneg fun t => mul_nonneg (smoothed_nonneg _ hh t) (density_nonneg ha hb t)

lemma cross_section_le {L : ℕ} (hL : 0 < L) (δ : ℝ) {h : ℝ} (hh : 0 < h)
    (η : GridPairs.Grid L → ℝ) {a : ℝ × ℝ}
    (ha : 0 < 1 - δ + a.1) (hb : 0 < 1 + a.2) :
    (∫ t, smoothed (centers L δ η a) h t *
      density (1 - δ + a.1) (1 + a.2) t) ≤ 1 / (1 - δ + a.1) := by
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  calc
    _ ≤ ∫ t, smoothed (centers L δ η a) h t * (1 / (1 - δ + a.1)) :=
      integral_mono (integrable_cross_section L δ hh η a)
        ((integrable_smoothed _ h).mul_const _) (fun t =>
          mul_le_mul_of_nonneg_left (density_le ha hb t) (smoothed_nonneg _ hh t))
    _ = _ := by rw [integral_mul_const, integral_smoothed _ hh, one_mul]

/-- All parameter integrals below are genuine integrable functions, not default-zero integrals. -/
theorem integrable_cross_outer {L : ℕ} (hL : 0 < L) {δ h : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hh : 0 < h) (η : GridPairs.Grid L → ℝ) :
    Integrable (fun a => ∫ t, smoothed (centers L δ η a) h t *
      density (1 - δ + a.1) (1 + a.2) t) (parameterMeasure δ) := by
  letI := parameterMeasure_probability hδ
  apply Integrable.of_bound
    (measurable_cross_integrand L δ h η).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    (1 / (1 - δ))
  filter_upwards [ProjectionContinuumLimit.ae_parameter_support hδ] with a ha
  have hα : 0 < 1 - δ + a.1 := by linarith [ha.1.1]
  have hβ : 0 < 1 + a.2 := by linarith [ha.2.1]
  rw [Real.norm_eq_abs, abs_of_nonneg (cross_section_nonneg L δ hh η hα hβ)]
  exact (cross_section_le hL δ hh η hα hβ).trans
    (one_div_le_one_div_of_le (by linarith) (by linarith [ha.1.1]))

theorem integrable_reference_outer {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    Integrable (fun a : ℝ × ℝ => ∫ t,
      density (1 - δ + a.1) (1 + a.2) t ^ 2) (parameterMeasure δ) := by
  letI := parameterMeasure_probability hδ
  apply Integrable.of_bound
    (measurable_reference_integrand δ).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    (1 / (1 - δ))
  filter_upwards [ProjectionContinuumLimit.ae_parameter_support hδ] with a ha
  have hα : 0 < 1 - δ + a.1 := by linarith [ha.1.1]
  have hβ : 0 < 1 + a.2 := by linarith [ha.2.1]
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun t => sq_nonneg _)]
  exact (integral_density_sq_le hα hβ).trans
    (one_div_le_one_div_of_le (by linarith) (by linarith [ha.1.1]))

lemma lipschitz_dot_three {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ha1 : a ≤ 1) (hb2 : b ≤ 2) : LipschitzWith 3 (dot a b) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro u v
  have hu : |u.1 - v.1| ≤ dist u v := by
    rw [← Real.dist_eq, Prod.dist_eq]
    exact le_max_left _ _
  have hv : |u.2 - v.2| ≤ dist u v := by
    rw [← Real.dist_eq, Prod.dist_eq]
    exact le_max_right _ _
  rw [Real.dist_eq]
  change |dot a b u - dot a b v| ≤ 3 * dist u v
  calc
    _ = |a * (u.1 - v.1) + b * (u.2 - v.2)| := by congr 1; unfold dot; ring
    _ ≤ |a * (u.1 - v.1)| + |b * (u.2 - v.2)| := abs_add_le _ _
    _ = a * |u.1 - v.1| + b * |u.2 - v.2| := by
      rw [abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hb]
    _ ≤ a * dist u v + b * dist u v :=
      add_le_add (mul_le_mul_of_nonneg_left hu ha.le) (mul_le_mul_of_nonneg_left hv hb.le)
    _ ≤ 3 * dist u v := by nlinarith [show 0 ≤ dist u v from dist_nonneg]

/-- Smoothing, deterministic displacement, and square quadrature are controlled separately. -/
theorem section_error {L : ℕ} (hL : 0 < L) {a b h τ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ha1 : a ≤ 1) (hb2 : b ≤ 2) (hh : 0 < h)
    (η : GridPairs.Grid L → ℝ) (hη : ∀ p, |η p| ≤ τ) :
    |(∫ t, smoothed (fun p => dot a b (sample L p) + η p) h t * density a b t) -
      ∫ t, density a b t ^ 2| ≤ (h + τ + 3 / (L : ℝ)) / (a * b) := by
  classical
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  let z : GridPairs.Grid L → ℝ := fun p => dot a b (sample L p) + η p
  let N : ℝ := Fintype.card (GridPairs.Grid L)
  have hN : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (GridPairs.Grid L))).ne'
  have hcard : N = (L : ℝ) ^ 2 := by simp [N, GridPairs.Grid, pow_two]
  have hs := integral_smoothed_test_error z (integrable_density a b)
    (lipschitzWith_density ha hb) hh
  have hj : |N⁻¹ * ∑ p, density a b (z p) -
      N⁻¹ * ∑ p : GridPairs.Grid L, density a b (dot a b (sample L p))| ≤ τ / (a * b) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
      abs_of_nonneg (show 0 ≤ N⁻¹ by dsimp [N]; positivity)]
    calc
      _ ≤ N⁻¹ * ∑ p, |density a b (z p) - density a b (dot a b (sample L p))| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by dsimp [N]; positivity)
      _ ≤ N⁻¹ * ∑ _p : GridPairs.Grid L, τ / (a * b) := by
        apply mul_le_mul_of_nonneg_left _ (by dsimp [N]; positivity)
        apply Finset.sum_le_sum
        intro p hp
        exact (density_abs_sub_le ha hb _ _).trans
          (div_le_div_of_nonneg_right (by simpa [z] using hη p) (mul_pos ha hb).le)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change N⁻¹ * (N * (τ / (a * b))) = _
        rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  have hg := gridAverage_lipschitz_error L hL
    ((lipschitzWith_density ha hb).comp (lipschitz_dot_three ha hb ha1 hb2))
  have hid : (∫ u, density a b (dot a b u) ∂parameterMeasure 1) =
      ∫ t, density a b t ^ 2 := by
    simpa only [pow_two] using integral_dot ha hb (continuous_density a b)
      (fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (density_nonneg ha hb t)]
        exact density_le ha hb t)
  have hav : N⁻¹ * ∑ p : GridPairs.Grid L, density a b (dot a b (sample L p)) =
      gridAverage L (fun u => density a b (dot a b u)) := by
    rw [hcard]
    simp only [gridAverage, div_eq_mul_inv, mul_comm]
  change |gridAverage L (fun u => density a b (dot a b u)) -
    ∫ u, density a b (dot a b u) ∂parameterMeasure 1| ≤ _ at hg
  rw [hid] at hg
  calc
    _ ≤ |(∫ t, smoothed z h t * density a b t) - N⁻¹ * ∑ p, density a b (z p)| +
        |N⁻¹ * ∑ p, density a b (z p) - ∫ t, density a b t ^ 2| := abs_sub_le _ _ _
    _ ≤ (a * b)⁻¹ * h +
        (|N⁻¹ * ∑ p, density a b (z p) -
          N⁻¹ * ∑ p : GridPairs.Grid L, density a b (dot a b (sample L p))| +
        |N⁻¹ * ∑ p : GridPairs.Grid L, density a b (dot a b (sample L p)) -
          ∫ t, density a b t ^ 2|) :=
      add_le_add hs (abs_sub_le _ _ _)
    _ ≤ (a * b)⁻¹ * h + (τ / (a * b) + ((a * b)⁻¹ * 3) / (L : ℝ)) := by
      apply add_le_add (le_refl _)
      apply add_le_add hj
      rw [hav]
      simpa using hg
    _ = _ := by ring

/-- Uniform averaged cross-term error. No density-law or quadrature premise is required. -/
theorem crossTerm_error {L : ℕ} (hL : 0 < L) {δ h τ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hh : 0 < h)
    (η : GridPairs.Grid L → ℝ) (hη : ∀ p, |η p| ≤ τ) :
    |crossTerm L δ h η -
      ∫ a : ℝ × ℝ, ∫ t, density (1 - δ + a.1) (1 + a.2) t ^ 2
        ∂volume ∂parameterMeasure δ| ≤ (h + τ + 3 / (L : ℝ)) / (1 - δ) := by
  letI := parameterMeasure_probability hδ
  have hτ : 0 ≤ τ := (abs_nonneg (η (⟨0, hL⟩, ⟨0, hL⟩))).trans (hη _)
  have hC : 0 ≤ h + τ + 3 / (L : ℝ) := by positivity
  unfold crossTerm
  rw [← integral_sub (integrable_cross_outer hL hδ hδ1 hh η)
    (integrable_reference_outer hδ hδ1), ← Real.norm_eq_abs]
  have he : ∀ᵐ a ∂parameterMeasure δ,
      ‖(∫ t, smoothed (centers L δ η a) h t * density (1 - δ + a.1) (1 + a.2) t) -
        ∫ t, density (1 - δ + a.1) (1 + a.2) t ^ 2‖ ≤
          (h + τ + 3 / (L : ℝ)) / (1 - δ) := by
    filter_upwards [ProjectionContinuumLimit.ae_parameter_support hδ] with a ha
    have hα : 0 < 1 - δ + a.1 := by linarith [ha.1.1]
    have hβ : 0 < 1 + a.2 := by linarith [ha.2.1]
    have hprod : 1 - δ ≤ (1 - δ + a.1) * (1 + a.2) := by
      nlinarith [ha.1.1, ha.2.1, mul_nonneg hα.le ha.2.1]
    rw [Real.norm_eq_abs]
    have hs := section_error hL hα hβ (by linarith [ha.1.2])
      (by linarith [ha.2.2]) hh η hη
    change |(∫ t, smoothed (centers L δ η a) h t *
      density (1 - δ + a.1) (1 + a.2) t) -
      ∫ t, density (1 - δ + a.1) (1 + a.2) t ^ 2| ≤ _ at hs
    exact hs.trans (div_le_div_of_nonneg_left hC (by linarith) hprod)
  simpa using norm_integral_le_of_norm_le_const he

end DistanceCounts.ProjectionCrossTerm
end

/-! Expected Lebesgue L² convergence of the actual perturbed grid projection. -/

noncomputable section

namespace DistanceCounts.MesoscopicProjection

open Filter MeasureTheory Set
open ParameterKernel EmpiricalEnergy EmpiricalPairKernel ProjectionDensity
open ProjectionContinuumLimit
open scoped Topology

def squareError (L : ℕ) (δ h : ℝ) (η : GridPairs.Grid L → ℝ) (a : ℝ × ℝ) : ℝ :=
  ∫ t : ℝ, (smoothed (center L δ η a) h t -
    density (1 - δ + a.1) (1 + a.2) t) ^ 2

def expectedSquareError (L : ℕ) (δ h : ℝ) (η : GridPairs.Grid L → ℝ) : ℝ :=
  ∫ a, squareError L δ h η a ∂parameterMeasure δ

theorem squareError_nonneg (L : ℕ) (δ h : ℝ) (η : GridPairs.Grid L → ℝ) (a : ℝ × ℝ) :
    0 ≤ squareError L δ h η a := integral_nonneg fun _ => sq_nonneg _


theorem measurable_smoothed_joint (L : ℕ) (δ h : ℝ) (η : GridPairs.Grid L → ℝ) :
    Measurable (fun x : (ℝ × ℝ) × ℝ => smoothed (center L δ η x.1) h x.2) := by
  unfold smoothed
  apply Measurable.mul measurable_const
  apply Finset.measurable_sum
  intro p hp
  apply (measurable_box h).comp
  unfold EmpiricalPairKernel.center projection
  fun_prop

theorem self_energy_le {L : ℕ} (hL : 0 < L) {h : ℝ} (hh : 0 < h)
    (z : GridPairs.Grid L → ℝ) : (∫ t, smoothed z h t ^ 2) ≤ 1 / h := by
  let N : ℝ := Fintype.card (GridPairs.Grid L)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hN : N ≠ 0 := by
    dsimp [N]
    simp only [GridPairs.Grid, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    positivity
  rw [integral_smoothed_sq z hh]
  calc
    _ ≤ N⁻¹ ^ 2 * ∑ i : GridPairs.Grid L, ∑ j : GridPairs.Grid L, (1 / h) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
        simpa only [one_div] using kernel_le hh (z i - z j)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change N⁻¹ ^ 2 * (N * (N * (1 / h))) = 1 / h
      field_simp [hN]
      <;> ring

theorem integrable_self_outer {L : ℕ} (hL : 0 < L) {δ h : ℝ}
    (hδ : 0 < δ) (hh : 0 < h) (η : GridPairs.Grid L → ℝ) :
    Integrable (fun a => ∫ t, smoothed (center L δ η a) h t ^ 2) (parameterMeasure δ) := by
  letI := parameterMeasure_probability hδ
  have hm : Measurable (fun a : ℝ × ℝ =>
      ∫ t : ℝ, smoothed (center L δ η a) h t ^ 2) :=
    ((measurable_smoothed_joint L δ h η).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  apply Integrable.of_bound (μ := parameterMeasure δ) hm.aestronglyMeasurable (1 / h)
  apply ae_of_all
  intro a
  change ‖(∫ t : ℝ, smoothed (center L δ η a) h t ^ 2)‖ ≤ 1 / h
  have hn : 0 ≤ (∫ t : ℝ, smoothed (center L δ η a) h t ^ 2) :=
    integral_nonneg fun _ => sq_nonneg _
  calc
    _ = ∫ t : ℝ, smoothed (center L δ η a) h t ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
    _ ≤ _ := self_energy_le hL hh _

theorem ae_squareError_eq {L : ℕ} {δ h : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hh : 0 < h) (η : GridPairs.Grid L → ℝ) :
    ∀ᵐ a ∂parameterMeasure δ, squareError L δ h η a =
      (∫ t, smoothed (center L δ η a) h t ^ 2) -
      2 * (∫ t, smoothed (center L δ η a) h t *
        density (1 - δ + a.1) (1 + a.2) t) + referenceEnergy δ a := by
  filter_upwards [ae_parameter_support hδ] with a ha
  have hα : 0 < 1 - δ + a.1 := by linarith [ha.1.1]
  have hβ : 0 < 1 + a.2 := by linarith [ha.2.1]
  have hs := integrable_smoothed_sq (center L δ η a) h
  have hc : Integrable (fun t => smoothed (center L δ η a) h t *
      density (1 - δ + a.1) (1 + a.2) t) :=
    ProjectionCrossTerm.integrable_cross_section L δ hh η a
  have hf := ContinuumEnergy.integrable_density_sq hα hβ
  unfold squareError referenceEnergy
  calc
    _ = ∫ t, (smoothed (center L δ η a) h t ^ 2 -
        2 * (smoothed (center L δ η a) h t * density (1 - δ + a.1) (1 + a.2) t) +
        density (1 - δ + a.1) (1 + a.2) t ^ 2) := by
      apply integral_congr_ae
      exact ae_of_all _ fun _ => by ring
    _ = _ := by
      rw [← integral_const_mul (2 : ℝ), ← integral_sub hs (hc.const_mul 2)]
      exact integral_add (hs.sub (hc.const_mul 2)) hf

theorem integrable_squareError {L : ℕ} (hL : 0 < L) {δ h : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hh : 0 < h) (η : GridPairs.Grid L → ℝ) :
    Integrable (squareError L δ h η) (parameterMeasure δ) := by
  have hs := integrable_self_outer hL hδ hh η
  have hc : Integrable (fun a => ∫ t, smoothed (center L δ η a) h t *
      density (1 - δ + a.1) (1 + a.2) t) (parameterMeasure δ) :=
    ProjectionCrossTerm.integrable_cross_outer hL hδ hδ1 hh η
  have hf := integrable_referenceEnergy hδ hδ1
  exact ((hs.sub (hc.const_mul 2)).add hf).congr
    (Filter.EventuallyEq.symm (ae_squareError_eq hδ hδ1 hh η))

theorem expectedSquareError_eq {L : ℕ} (hL : 0 < L) {δ h : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hh : 0 < h) (η : GridPairs.Grid L → ℝ) :
    expectedSquareError L δ h η = energy L δ h η -
      2 * ProjectionCrossTerm.crossTerm L δ h η +
      ∫ a, referenceEnergy δ a ∂parameterMeasure δ := by
  have hs := integrable_self_outer hL hδ hh η
  have hc : Integrable (fun a => ∫ t, smoothed (center L δ η a) h t *
      density (1 - δ + a.1) (1 + a.2) t) (parameterMeasure δ) :=
    ProjectionCrossTerm.integrable_cross_outer hL hδ hδ1 hh η
  have hf := integrable_referenceEnergy hδ hδ1
  unfold expectedSquareError
  rw [integral_congr_ae (ae_squareError_eq hδ hδ1 hh η),
    energy_eq_integral_smoothed_sq L hh η]
  unfold ProjectionCrossTerm.crossTerm
  rw [show ProjectionCrossTerm.centers L δ η = EmpiricalPairKernel.center L δ η from rfl]
  rw [← integral_const_mul (2 : ℝ), ← integral_sub hs (hc.const_mul 2)]
  exact integral_add (hs.sub (hc.const_mul 2)) hf

theorem tendsto_crossTerm {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    {h τ : ℕ → ℝ} (η : (L : ℕ) → GridPairs.Grid L → ℝ)
    (hh : ∀ᶠ L in atTop, 0 < h L) (hh0 : Tendsto h atTop (𝓝 0))
    (hτ0 : Tendsto τ atTop (𝓝 0))
    (hη : ∀ᶠ L in atTop, ∀ p, |η L p| ≤ τ L) :
    Tendsto (fun L => ProjectionCrossTerm.crossTerm L δ (h L) (η L)) atTop
      (𝓝 (∫ a, referenceEnergy δ a ∂parameterMeasure δ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hi : Tendsto (fun L : ℕ => (L : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun L => (h L + τ L + 3 / (L : ℝ)) / (1 - δ))
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_mul, zero_add] using
      ((hh0.add hτ0).add (hi.const_mul 3)).div_const (1 - δ)
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hb
  filter_upwards [hh, hη, eventually_gt_atTop 0] with L hLh hLη hL
  simpa only [Real.norm_eq_abs, referenceEnergy] using
    ProjectionCrossTerm.crossTerm_error hL hδ hδ1 hLh (η L) hLη

/-- Actual expected squared error tends to zero at every mesoscopic bandwidth. -/
theorem tendsto_expectedSquareError {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    {h τ : ℕ → ℝ} (η : (L : ℕ) → GridPairs.Grid L → ℝ)
    (hh : ∀ᶠ L in atTop, 0 < h L) (hh0 : Tendsto h atTop (𝓝 0))
    (hg : Tendsto (fun L : ℕ => (L : ℝ) ^ 2 * h L) atTop atTop)
    (hτ0 : Tendsto τ atTop (𝓝 0))
    (hη : ∀ᶠ L in atTop, ∀ p, |η L p| ≤ τ L) :
    Tendsto (fun L => expectedSquareError L δ (h L) (η L)) atTop (𝓝 0) := by
  have hs := MesoscopicEnergy.tendsto_energy_reference hδ hδ1 η hh hh0 hg hτ0 hη
  have hc := tendsto_crossTerm hδ hδ1 η hh hh0 hτ0 hη
  have hf : Tendsto (fun _ : ℕ => ∫ a, referenceEnergy δ a ∂parameterMeasure δ)
      atTop (𝓝 (∫ a, referenceEnergy δ a ∂parameterMeasure δ)) := tendsto_const_nhds
  have hsum := (hs.sub (hc.const_mul 2)).add hf
  have hz : (∫ a, referenceEnergy δ a ∂parameterMeasure δ) -
      2 * (∫ a, referenceEnergy δ a ∂parameterMeasure δ) +
      (∫ a, referenceEnergy δ a ∂parameterMeasure δ) = 0 := by ring
  rw [hz] at hsum
  apply hsum.congr'
  filter_upwards [hh, eventually_gt_atTop 0] with L hLh hL
  exact (expectedSquareError_eq hL hδ hδ1 hLh (η L)).symm

end DistanceCounts.MesoscopicProjection
end

/-! Parameter-independent perturbations determined by the original pinned counts. -/

noncomputable section

namespace DistanceCounts.FineData

/-- The actual residual from the assigned coarse degree. -/
def error {K L : ℕ} (D : Fin K → ℤ) (Z0 : Fin K × GridPairs.Grid L → ℤ)
    (i : Fin K × GridPairs.Grid L) : ℝ :=
  (Z0 i : ℝ) - (D i.1 : ℝ) * (L : ℝ) ^ 2

/-- Include the exact integer-jitter unit-cell shift, which is deterministic as well. -/
def perturbation {K L : ℕ} (D : Fin K → ℤ) (Z0 : Fin K × GridPairs.Grid L → ℤ)
    (H : ℕ) (b : Fin K) (p : GridPairs.Grid L) : ℝ :=
  error D Z0 (b, p) / (L : ℝ) ^ 2 - (H : ℝ) / (L : ℝ) ^ 2 + 1 / (L : ℝ) ^ 2

theorem decomposition {K L : ℕ} (D : Fin K → ℤ)
    (Z0 : Fin K × GridPairs.Grid L → ℤ) (i : Fin K × GridPairs.Grid L) :
    (Z0 i : ℝ) = (D i.1 : ℝ) * (L : ℝ) ^ 2 + error D Z0 i := by
  unfold error
  ring

end DistanceCounts.FineData
end

noncomputable section
open Filter
open scoped Topology

namespace DistanceCounts.ConstructionScales

/-- The schedules are literal floors, including at the early scales where they vanish. -/
def N (K L : ℕ) : ℕ := K * L ^ 2
def H (L : ℕ) : ℕ := ⌊Real.sqrt (L : ℝ)⌋₊
def B (K L : ℕ) : ℕ := ⌊Real.sqrt (Real.log (N K L : ℝ))⌋₊
def ell (K L : ℕ) : ℕ := ⌊Real.log (N K L : ℝ) / (2 * Real.log 2)⌋₊
def h (L : ℕ) : ℝ := (H L : ℝ) / (L : ℝ) ^ 2
def E (L : ℕ) : ℝ := (L : ℝ) ^ (1 / 10 : ℝ)

private lemma tendsto_L : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop

private lemma eventually_L_pos : ∀ᶠ L : ℕ in atTop, (0 : ℝ) < L :=
  tendsto_L.eventually (eventually_gt_atTop 0)

lemma tendsto_N {K : ℕ} (hK : 0 < K) :
    Tendsto (fun L : ℕ => (N K L : ℝ)) atTop atTop := by
  simpa [N] using ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_L).const_mul_atTop
    (show (0 : ℝ) < K by exact_mod_cast hK)

lemma tendsto_logN {K : ℕ} (hK : 0 < K) :
    Tendsto (fun L : ℕ => Real.log (N K L : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_N hK)

private lemma tendsto_sqrtL :
    Tendsto (fun L : ℕ => Real.sqrt (L : ℝ)) atTop atTop := by
  simpa only [Function.comp_def, Real.sqrt_eq_rpow] using
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_L

private lemma tendsto_sqrtLogN {K : ℕ} (hK : 0 < K) :
    Tendsto (fun L : ℕ => Real.sqrt (Real.log (N K L : ℝ))) atTop atTop := by
  simpa only [Function.comp_def, Real.sqrt_eq_rpow] using
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp (tendsto_logN hK)


private lemma tendsto_ellReal {K : ℕ} (hK : 0 < K) :
    Tendsto (fun L : ℕ => Real.log (N K L : ℝ) / (2 * Real.log 2))
      atTop atTop :=
  (tendsto_logN hK).atTop_div_const (by positivity)

lemma tendsto_H : Tendsto H atTop atTop :=
  tendsto_nat_floor_atTop.comp tendsto_sqrtL

lemma tendsto_B {K : ℕ} (hK : 0 < K) : Tendsto (B K) atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_sqrtLogN hK)

lemma tendsto_ell {K : ℕ} (hK : 0 < K) : Tendsto (ell K) atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_ellReal hK)

lemma eventually_pos {K : ℕ} (hK : 0 < K) :
    ∀ᶠ L : ℕ in atTop, 0 < H L ∧ 0 < B K L ∧ 0 < ell K L := by
  filter_upwards [tendsto_H.eventually (eventually_gt_atTop 0),
    (tendsto_B hK).eventually (eventually_gt_atTop 0),
    (tendsto_ell hK).eventually (eventually_gt_atTop 0)] with L hH hB he
  exact ⟨hH, hB, he⟩

lemma tendsto_H_div_sqrt :
    Tendsto (fun L : ℕ => (H L : ℝ) / Real.sqrt L) atTop (𝓝 1) :=
  tendsto_nat_floor_div_atTop.comp tendsto_sqrtL

private lemma tendsto_rpow_ratio (a b : ℝ) (hab : a < b) :
    Tendsto (fun L : ℕ => (L : ℝ) ^ a / (L : ℝ) ^ b) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp tendsto_L
  apply ht.congr'
  filter_upwards [eventually_L_pos] with L hL
  change (L : ℝ) ^ (-(b - a)) = (L : ℝ) ^ a / (L : ℝ) ^ b
  rw [show -(b - a) = a - b by ring, Real.rpow_sub hL]

lemma tendsto_H_div_L :
    Tendsto (fun L : ℕ => (H L : ℝ) / L) atTop (𝓝 0) := by
  have ht := tendsto_H_div_sqrt.mul (tendsto_rpow_ratio (1 / 2) 1 (by norm_num))
  simp only [mul_zero, Real.rpow_one] at ht
  apply ht.congr'
  filter_upwards [eventually_L_pos] with L hL
  rw [← Real.sqrt_eq_rpow]
  field_simp [Real.sqrt_ne_zero'.mpr hL]

lemma tendsto_h : Tendsto h atTop (𝓝 0) := by
  have ht := tendsto_H_div_L.mul (tendsto_L.inv_tendsto_atTop)
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_L_pos] with L hL
  change (H L : ℝ) / (L : ℝ) * (L : ℝ)⁻¹ =
    (H L : ℝ) / (L : ℝ) ^ 2
  field_simp

lemma tendsto_square_mul_h :
    Tendsto (fun L : ℕ => (L : ℝ) ^ 2 * h L) atTop atTop := by
  apply (tendsto_natCast_atTop_atTop.comp tendsto_H).congr'
  filter_upwards [eventually_L_pos] with L hL
  dsimp [h]
  field_simp

lemma tendsto_E_div_sqrt :
    Tendsto (fun L : ℕ => E L / Real.sqrt L) atTop (𝓝 0) := by
  simpa [E, Real.sqrt_eq_rpow] using tendsto_rpow_ratio (1 / 10) (1 / 2) (by norm_num)

lemma tendsto_discrepancy_div_H :
    Tendsto (fun L : ℕ => (2 * E L + 1) / (H L : ℝ)) atTop (𝓝 0) := by
  have ht := ((tendsto_E_div_sqrt.const_mul 2).add
    tendsto_sqrtL.inv_tendsto_atTop).div tendsto_H_div_sqrt one_ne_zero
  simp only [mul_zero, add_zero, zero_div] at ht
  apply ht.congr'
  filter_upwards [eventually_L_pos] with L hL
  change (2 * (E L / Real.sqrt (L : ℝ)) + (Real.sqrt (L : ℝ))⁻¹) /
    ((H L : ℝ) / Real.sqrt (L : ℝ)) = (2 * E L + 1) / (H L : ℝ)
  field_simp [Real.sqrt_ne_zero'.mpr hL]
  <;> ring


private lemma logN_eq {K L : ℕ} (hK : 0 < K) (hL : (0 : ℝ) < L) :
    Real.log (N K L : ℝ) = Real.log (K : ℝ) + 2 * Real.log L := by
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  simp [N, Real.log_mul hKr (pow_ne_zero _ hL.ne'), Real.log_pow]

lemma tendsto_logN_div_rpow {K : ℕ} (hK : 0 < K) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun L : ℕ => Real.log (N K L : ℝ) / (L : ℝ) ^ r)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun L : ℕ => Real.log (L : ℝ) / (L : ℝ) ^ r)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero.comp tendsto_L
  have hconst := (tendsto_const_nhds (x := Real.log (K : ℝ))).div_atTop
    ((tendsto_rpow_atTop hr).comp tendsto_L)
  have ht := hconst.add (hlog.const_mul 2)
  simp only [mul_zero, add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_L_pos] with L hL
  change Real.log (K : ℝ) / (L : ℝ) ^ r +
    2 * (Real.log (L : ℝ) / (L : ℝ) ^ r) =
      Real.log (N K L : ℝ) / (L : ℝ) ^ r
  rw [logN_eq hK hL]
  ring

lemma eventually_B_le_logN {K : ℕ} (hK : 0 < K) :
    ∀ᶠ L : ℕ in atTop, (B K L : ℝ) ≤ Real.log (N K L : ℝ) := by
  filter_upwards [(tendsto_logN hK).eventually (eventually_ge_atTop 1)] with L hL
  apply (Nat.floor_le (Real.sqrt_nonneg _)).trans
  have hs := Real.sq_sqrt (show 0 ≤ Real.log (N K L : ℝ) by linarith)
  have hp := Real.sqrt_nonneg (Real.log (N K L : ℝ))
  nlinarith

lemma tendsto_B_div_rpow {K : ℕ} (hK : 0 < K) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun L : ℕ => (B K L : ℝ) / (L : ℝ) ^ r) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun L => by positivity))
    ((eventually_B_le_logN hK).mono (fun L hL =>
      div_le_div_of_nonneg_right hL (Real.rpow_nonneg (Nat.cast_nonneg L) r)))
    (tendsto_logN_div_rpow hK hr)


lemma tendsto_rowMoment {K : ℕ} (hK : 0 < K) :
    Tendsto (fun L : ℕ => (K : ℝ) * (B K L + 4 * E L + 2) *
      (1 + Real.log L) / L) atTop (𝓝 0) := by
  have hb : Tendsto (fun L : ℕ => (B K L : ℝ) / Real.sqrt L) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      tendsto_B_div_rpow hK (by norm_num : (0 : ℝ) < 1 / 2)
  have hl : Tendsto (fun L : ℕ => Real.log L / Real.sqrt L) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
        tendsto_L
  have ht := ((hb.add (tendsto_E_div_sqrt.const_mul 4)).add
    (tendsto_sqrtL.inv_tendsto_atTop.const_mul 2)).mul
    (tendsto_sqrtL.inv_tendsto_atTop.add hl) |>.const_mul (K : ℝ)
  simp only [mul_zero, add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_L_pos] with L hL
  have hs := Real.sq_sqrt hL.le
  have hs0 := (Real.sqrt_pos.mpr hL).ne'
  change (K : ℝ) *
    (((B K L : ℝ) / Real.sqrt (L : ℝ) + 4 * (E L / Real.sqrt (L : ℝ)) +
      2 * (Real.sqrt (L : ℝ))⁻¹) *
      ((Real.sqrt (L : ℝ))⁻¹ + Real.log (L : ℝ) / Real.sqrt (L : ℝ))) =
    (K : ℝ) * ((B K L : ℝ) + 4 * E L + 2) * (1 + Real.log (L : ℝ)) / (L : ℝ)
  calc
    _ = (K : ℝ) * ((B K L : ℝ) + 4 * E L + 2) * (1 + Real.log (L : ℝ)) /
        Real.sqrt (L : ℝ) ^ 2 := by
      field_simp [hs0]
      <;> ring
    _ = _ := by rw [hs]


end DistanceCounts.ConstructionScales
end

noncomputable section

namespace DistanceCounts.SkewParameters
open Set MeasureTheory
def alpha (δ : ℝ) (a : ℝ × ℝ) : ℝ := 1 - δ + a.1
def beta (a : ℝ × ℝ) : ℝ := 1 + a.2
def good (δ : ℝ) (_L : ℕ) (E : ℝ) : Set (ℝ × ℝ) :=
  {a | a ∈ Icc (0 : ℝ) δ ×ˢ Icc (0 : ℝ) 1 ∧ 1 ≤ E}
theorem measurableSet_good (δ : ℝ) (L : ℕ) (E : ℝ) : MeasurableSet (good δ L E) :=
  (measurableSet_Icc.prod measurableSet_Icc).inter (MeasurableSet.const _)
end DistanceCounts.SkewParameters
end

/-! Finite-bin covariance bounds for measurable independent integer-valued group jitters. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace DistanceCounts
namespace JitterVariance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The real-valued indicator that an integer random variable occupies a bin. -/
def binIndicator (W : Ω → ℤ) (j : ℤ) (ω : Ω) : ℝ :=
  if W ω = j then 1 else 0

lemma binIndicator_measurable {W : Ω → ℤ} (hW : Measurable W) (j : ℤ) :
    Measurable (binIndicator W j) :=
  (measurable_of_countable (fun z : ℤ => if z = j then (1 : ℝ) else 0)).comp hW

lemma binIndicator_nonneg (W : Ω → ℤ) (j : ℤ) (ω : Ω) :
    0 ≤ binIndicator W j ω := by
  unfold binIndicator
  split_ifs <;> norm_num

lemma binIndicator_le_one (W : Ω → ℤ) (j : ℤ) (ω : Ω) :
    binIndicator W j ω ≤ 1 := by
  unfold binIndicator
  split_ifs <;> norm_num

lemma binIndicator_memLp [IsFiniteMeasure μ] {W : Ω → ℤ}
    (hW : Measurable W) (j : ℤ) : MemLp (binIndicator W j) 2 μ := by
  exact memLp_of_bounded
    (Filter.Eventually.of_forall fun ω =>
      ⟨binIndicator_nonneg W j ω, binIndicator_le_one W j ω⟩)
    (binIndicator_measurable hW j).aestronglyMeasurable 2


/-- A pin contributes to at most one of the finitely many bins. -/
lemma sum_binIndicator_le_one (W : Ω → ℤ) (J : Finset ℤ) (ω : Ω) :
    (∑ j ∈ J, binIndicator W j ω) ≤ 1 := by
  classical
  simp only [binIndicator, Finset.sum_ite_eq]
  split_ifs <;> norm_num

/-- The sum of same-bin joint probabilities of any two pins is at most one. -/
lemma sum_joint_le_one [IsProbabilityMeasure μ] {U V : Ω → ℤ}
    (hU : Measurable U) (hV : Measurable V) (J : Finset ℤ) :
    (∑ j ∈ J, ∫ ω, binIndicator U j ω * binIndicator V j ω ∂μ) ≤ 1 := by
  have hint j : Integrable (fun ω => binIndicator U j ω * binIndicator V j ω) μ :=
    (binIndicator_memLp hU j).integrable_mul (binIndicator_memLp hV j)
  rw [← integral_finsetSum J (fun j _ => hint j)]
  calc
    (∫ ω, ∑ j ∈ J, binIndicator U j ω * binIndicator V j ω ∂μ)
        ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := by
      apply integral_mono (integrable_finsetSum J (fun j _ => hint j)) (integrable_const 1)
      intro ω
      calc
        (∑ j ∈ J, binIndicator U j ω * binIndicator V j ω)
            ≤ ∑ j ∈ J, binIndicator U j ω := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_of_le_one_right (binIndicator_nonneg U j ω)
            (binIndicator_le_one V j ω)
        _ ≤ 1 := sum_binIndicator_le_one U J ω
    _ = 1 := by simp

lemma covariance_binIndicator_le_joint [IsProbabilityMeasure μ] {U V : Ω → ℤ}
    (hU : Measurable U) (hV : Measurable V) (j : ℤ) :
    covariance (binIndicator U j) (binIndicator V j) μ ≤
      ∫ ω, binIndicator U j ω * binIndicator V j ω ∂μ := by
  rw [covariance_eq_sub (binIndicator_memLp hU j) (binIndicator_memLp hV j)]
  exact sub_le_self _ (mul_nonneg
    (integral_nonneg (binIndicator_nonneg U j))
    (integral_nonneg (binIndicator_nonneg V j)))

lemma sum_covariance_le_one [IsProbabilityMeasure μ] {U V : Ω → ℤ}
    (hU : Measurable U) (hV : Measurable V) (J : Finset ℤ) :
    (∑ j ∈ J, covariance (binIndicator U j) (binIndicator V j) μ) ≤ 1 :=
  (Finset.sum_le_sum fun j _ => covariance_binIndicator_le_joint hU hV j).trans
    (sum_joint_le_one hU hV J)


lemma covariance_binIndicator_nonpos [IsProbabilityMeasure μ] {U V : Ω → ℤ}
    (hU : Measurable U) (hV : Measurable V) (hdisjoint : ∀ ω, U ω ≠ V ω) (j : ℤ) :
    covariance (binIndicator U j) (binIndicator V j) μ ≤ 0 := by
  have hz : (fun ω => binIndicator U j ω * binIndicator V j ω) = 0 := by
    funext ω
    have := hdisjoint ω
    simp only [binIndicator, Pi.zero_apply]
    split_ifs <;> simp_all
  have h := covariance_binIndicator_le_joint (μ := μ) hU hV j
  rw [hz] at h
  change covariance (binIndicator U j) (binIndicator V j) μ ≤ ∫ _ω, (0 : ℝ) ∂μ at h
  simpa only [integral_zero] using h

lemma covariance_binIndicator_indep [IsProbabilityMeasure μ] {U V : Ω → ℤ}
    (hU : Measurable U) (hV : Measurable V) (hind : IndepFun U V μ) (j : ℤ) :
    covariance (binIndicator U j) (binIndicator V j) μ = 0 := by
  have hind' : IndepFun (binIndicator U j) (binIndicator V j) μ :=
    hind.comp
      (measurable_of_countable (fun z : ℤ => if z = j then (1 : ℝ) else 0))
      (measurable_of_countable (fun z : ℤ => if z = j then (1 : ℝ) else 0))
  exact hind'.covariance_eq_zero (binIndicator_memLp hU j) (binIndicator_memLp hV j)

/-- Real occupancy of bin `j` by all pins. -/
def occupancy {M : ℕ} (W : Fin M → Ω → ℤ) (j : ℤ) (ω : Ω) : ℝ :=
  ∑ i, binIndicator (W i) j ω

lemma occupancy_memLp [IsFiniteMeasure μ] {M : ℕ} {W : Fin M → Ω → ℤ}
    (hW : ∀ i, Measurable (W i)) (j : ℤ) : MemLp (occupancy W j) 2 μ :=
  memLp_finsetSum Finset.univ (fun i _ => binIndicator_memLp (hW i) j)

/-- Abstract finite-bin covariance bound. `near` is only required to contain
all same-group pairs which can occupy a bin together; independence is genuine
independence of the bin-valued random variables for different groups. -/
theorem finite_bin_variance_bound [IsProbabilityMeasure μ]
    {M : ℕ} {G : Type*} [DecidableEq G] (g : Fin M → G)
    (W : Fin M → Ω → ℤ) (hW : ∀ i, Measurable (W i))
    (near : Fin M → Fin M → Prop) [DecidableRel near]
    (hind : ∀ i k, g i ≠ g k → IndepFun (W i) (W k) μ)
    (hfar : ∀ i k, g i = g k → ¬ near i k → ∀ ω, W i ω ≠ W k ω)
    (J : Finset ℤ) :
    (∑ j ∈ J, variance (occupancy W j) μ) ≤ (M : ℝ) +
      ((Finset.univ.filter (fun p : Fin M × Fin M =>
        p.1 ≠ p.2 ∧ g p.1 = g p.2 ∧ near p.1 p.2)).card : ℝ) := by
  classical
  have hpair (i k : Fin M) :
      (∑ j ∈ J, covariance (binIndicator (W i) j) (binIndicator (W k) j) μ) ≤
        (if i = k then (1 : ℝ) else 0) +
        (if i ≠ k ∧ g i = g k ∧ near i k then (1 : ℝ) else 0) := by
    by_cases hik : i = k
    · simpa [hik] using sum_covariance_le_one (μ := μ) (hW i) (hW k) J
    by_cases hg : g i = g k
    · by_cases hn : near i k
      · simpa [hik, hg, hn] using sum_covariance_le_one (μ := μ) (hW i) (hW k) J
      · simp only [hik, hg, hn, not_false_eq_true, true_and, and_false,
          if_false, zero_add]
        exact Finset.sum_nonpos fun j _ =>
          covariance_binIndicator_nonpos (hW i) (hW k) (hfar i k hg hn) j
    · simp only [hik, hg, not_false_eq_true, true_and, false_and, and_false, if_false, zero_add]
      exact le_of_eq (Finset.sum_eq_zero fun j _ =>
        covariance_binIndicator_indep (hW i) (hW k) (hind i k hg) j)
  have hexpand (j : ℤ) : variance (occupancy W j) μ =
      ∑ i, ∑ k, covariance (binIndicator (W i) j) (binIndicator (W k) j) μ := by
    rw [← covariance_self (occupancy_memLp hW j).aestronglyMeasurable.aemeasurable]
    exact covariance_fun_sum_fun_sum
      (fun i => binIndicator_memLp (hW i) j) (fun i => binIndicator_memLp (hW i) j)
  calc
    (∑ j ∈ J, variance (occupancy W j) μ)
        = ∑ i, ∑ k, ∑ j ∈ J,
            covariance (binIndicator (W i) j) (binIndicator (W k) j) μ := by
      simp_rw [hexpand]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin M, ∑ k : Fin M,
        ((if i = k then (1 : ℝ) else 0) +
        (if i ≠ k ∧ g i = g k ∧ near i k then (1 : ℝ) else 0)) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hpair i k
    _ = (M : ℝ) +
        ((Finset.univ.filter (fun p : Fin M × Fin M =>
          p.1 ≠ p.2 ∧ g p.1 = g p.2 ∧ near p.1 p.2)).card : ℝ) := by
      simp only [Finset.sum_add_distrib]
      congr 1
      · simp
      · rw [← Fintype.sum_prod_type']
        simp

/-- Equal Euclidean-division bins force integer separation strictly below the width. -/
lemma abs_sub_lt_of_ediv_eq {a b B : ℤ} (hB : 0 < B) (h : a / B = b / B) :
    |a - b| < B := by
  have ha := Int.emod_add_mul_ediv a B
  have hb := Int.emod_add_mul_ediv b B
  have ha0 := Int.emod_nonneg a hB.ne'
  have hb0 := Int.emod_nonneg b hB.ne'
  have haB := Int.emod_lt_of_pos a hB
  have hbB := Int.emod_lt_of_pos b hB
  rw [h] at ha
  rw [abs_lt]
  constructor <;> omega

/-- The jittered level `Z i - q (g i)` is assigned its integer bin. -/
def jitterBin {M : ℕ} {G : Type*} (Z : Fin M → ℤ) (g : Fin M → G)
    (q : G → Ω → ℤ) (B : ℤ) (i : Fin M) (ω : Ω) : ℤ :=
  (Z i - q (g i) ω) / B

/-- The exact finite form of Proof.md (26), with ordered distinct near pairs.
No distributional assumption beyond measurable independent group jitters is needed. -/
theorem jitter_variance_bound [IsProbabilityMeasure μ]
    {M : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
    (Z : Fin M → ℤ) (g : Fin M → G) (q : G → Ω → ℤ)
    (hq : ∀ a, Measurable (q a)) (hind : iIndepFun q μ)
    (B : ℤ) (hB : 0 < B) (J : Finset ℤ) :
    (∑ j ∈ J, variance (occupancy (jitterBin Z g q B) j) μ) ≤ (M : ℝ) +
      ((Finset.univ.filter (fun p : Fin M × Fin M =>
        p.1 ≠ p.2 ∧ g p.1 = g p.2 ∧ |Z p.1 - Z p.2| < B)).card : ℝ) := by
  apply finite_bin_variance_bound g (jitterBin Z g q B)
    (fun i => (measurable_of_countable (fun z : ℤ => (Z i - z) / B)).comp (hq (g i)))
    (fun i k => |Z i - Z k| < B)
  · intro i k hik
    exact (hind.indepFun hik).comp
      (measurable_of_countable (fun z : ℤ => (Z i - z) / B))
      (measurable_of_countable (fun z : ℤ => (Z k - z) / B))
  · intro i k hg hn ω heq
    apply hn
    have h := abs_sub_lt_of_ediv_eq hB heq
    simpa only [hg, sub_sub_sub_cancel_right] using h

/-- Unordered pairs are represented canonically by increasing pin indices. -/
theorem ordered_near_count_eq_twice_unordered {M : ℕ} {G : Type*} [DecidableEq G]
    (Z : Fin M → ℤ) (g : Fin M → G) (B : ℤ) :
    (Finset.univ.filter (fun p : Fin M × Fin M =>
      p.1 ≠ p.2 ∧ g p.1 = g p.2 ∧ |Z p.1 - Z p.2| < B)).card =
    2 * (Finset.univ.filter (fun p : Fin M × Fin M =>
      p.1 < p.2 ∧ g p.1 = g p.2 ∧ |Z p.1 - Z p.2| < B)).card := by
  classical
  let u := Finset.univ.filter (fun p : Fin M × Fin M =>
    p.1 < p.2 ∧ g p.1 = g p.2 ∧ |Z p.1 - Z p.2| < B)
  let v := Finset.univ.filter (fun p : Fin M × Fin M =>
    p.2 < p.1 ∧ g p.1 = g p.2 ∧ |Z p.1 - Z p.2| < B)
  have hdisj : Disjoint u v := by
    simp only [u, v, Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
    intro p hp hq
    exact (lt_asymm hp.1 hq.1)
  have hunion : u ∪ v = Finset.univ.filter (fun p : Fin M × Fin M =>
      p.1 ≠ p.2 ∧ g p.1 = g p.2 ∧ |Z p.1 - Z p.2| < B) := by
    ext p
    simp only [u, v, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h)
      · exact ⟨ne_of_lt h.1, h.2⟩
      · exact ⟨ne_of_gt h.1, h.2⟩
    · intro h
      rcases lt_or_gt_of_ne h.1 with hlt | hgt
      · exact Or.inl ⟨hlt, h.2⟩
      · exact Or.inr ⟨hgt, h.2⟩
  have hcard : u.card = v.card := by
    apply Finset.card_equiv (Equiv.prodComm (Fin M) (Fin M))
    intro p
    simp only [u, v, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.prodComm_apply]
    dsimp only [Prod.swap]
    rw [abs_sub_comm (Z p.2) (Z p.1)]
    exact and_congr_right fun _ => and_congr_left fun _ => eq_comm
  rw [← hunion, Finset.card_union_of_disjoint hdisj, ← hcard]
  change u.card + u.card = 2 * u.card
  omega

/-- Equation (26) with the document's unordered-pair convention. -/
theorem jitter_variance_bound_unordered [IsProbabilityMeasure μ]
    {M : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
    (Z : Fin M → ℤ) (g : Fin M → G) (q : G → Ω → ℤ)
    (hq : ∀ a, Measurable (q a)) (hind : iIndepFun q μ)
    (B : ℤ) (hB : 0 < B) (J : Finset ℤ) :
    (∑ j ∈ J, variance (occupancy (jitterBin Z g q B) j) μ) ≤ (M : ℝ) +
      2 * ((Finset.univ.filter (fun p : Fin M × Fin M =>
        p.1 < p.2 ∧ g p.1 = g p.2 ∧ |Z p.1 - Z p.2| < B)).card : ℝ) := by
  have h := jitter_variance_bound Z g q hq hind B hB J
  rw [ordered_near_count_eq_twice_unordered Z g B] at h
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

end JitterVariance
end DistanceCounts
end

/-! Conditional same-row estimates for actual measurable integer levels.  The good set
and the levels can be dependent.  No construction of either is asserted here. -/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators

namespace DistanceCounts.RowPairAverage

open ProjectionDensity ParameterKernel

abbrev Pin (K L : ℕ) := Fin K × (Fin L × Fin L)

def group {K L : ℕ} (i : Pin K L) : Fin K × Fin L := (i.1, i.2.2)

/-- An honest real indicator of an open affine strip. -/
def stripIndicator (R : ℝ) : ℝ → ℝ := (Ioo (-R) R).indicator (fun _ => 1)

lemma stripIndicator_measurable (R : ℝ) : Measurable (stripIndicator R) :=
  measurable_const.indicator measurableSet_Ioo

lemma stripIndicator_bounds (R t : ℝ) :
    0 ≤ stripIndicator R t ∧ stripIndicator R t ≤ 1 := by
  simp only [stripIndicator, Set.indicator]
  split_ifs <;> norm_num

lemma stripIndicator_integrable (R : ℝ) : Integrable (stripIndicator R) :=
  (integrableOn_const (by simp : volume (Ioo (-R) R) ≠ ⊤)).integrable_indicator
    measurableSet_Ioo

lemma integral_stripIndicator {R : ℝ} (hR : 0 ≤ R) :
    (∫ t, stripIndicator R t) = 2 * R := by
  have hwidth : R - -R = 2 * R := by ring
  have hwidth_nonneg : 0 ≤ 2 * R := mul_nonneg (by norm_num) hR
  simp [stripIndicator, integral_indicator_const, Real.volume_real_Ioo,
    hwidth, max_eq_left hwidth_nonneg, smul_eq_mul]

/-- The normalized Lebesgue probability bound, for either sign of the slope.
The second parameter is integrated out, not treated as an independent good event. -/
theorem integral_affine_strip_le {δ R u : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R)
    (hu : u ≠ 0) (c : ℝ) :
    (∫ a, stripIndicator R (c + u * a.1) ∂parameterMeasure δ) ≤
      2 * R / (δ * |u|) := by
  letI := uniformIntervalMeasure_probability hδ
  letI := uniformIntervalMeasure_probability (by norm_num : (0 : ℝ) < 1)
  letI := parameterMeasure_probability hδ
  have hm : Measurable (fun a : ℝ × ℝ => stripIndicator R (c + u * a.1)) :=
    (stripIndicator_measurable R).comp (by fun_prop)
  have hi : Integrable (fun a : ℝ × ℝ => stripIndicator R (c + u * a.1))
      (parameterMeasure δ) :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (stripIndicator_bounds _ _).1]
      exact (stripIndicator_bounds _ _).2)
  rw [parameterMeasure, integral_prod _ hi]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  rw [integral_uniform_affine hδ hu c]
  let w := δ * |u|
  let d := c + min (δ * u) 0
  have hw : 0 < w := mul_pos hδ (abs_pos.mpr hu)
  have ht : Integrable (fun t => stripIndicator R (d + t)) :=
    (stripIndicator_integrable R).comp_add_left d
  have hmt : Measurable (fun t => stripIndicator R (d + t)) :=
    (stripIndicator_measurable R).comp (by fun_prop)
  have hprod : Integrable (fun t => box w t * stripIndicator R (d + t)) :=
    (integrable_box w).mul_bdd hmt.aestronglyMeasurable
      (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (stripIndicator_bounds _ _).1]
        exact (stripIndicator_bounds _ _).2)
  calc
    (∫ t, box w t * stripIndicator R (d + t)) ≤
        ∫ t, (1 / w) * stripIndicator R (d + t) :=
      integral_mono hprod (ht.const_mul _) fun t =>
        mul_le_mul_of_nonneg_right (box_le hw t) (stripIndicator_bounds _ _).1
    _ = 2 * R / (δ * |u|) := by
      rw [integral_const_mul, integral_add_left_eq_self, integral_stripIndicator hR]
      dsimp [w]
      ring


/-- Each horizontal displacement is counted at most once for a fixed pin. -/
lemma sum_inverse_row_difference_le (L : ℕ) (x : Fin L) :
    (∑ z : Fin L, |(x.val : ℝ) - z.val|⁻¹) ≤ 2 * (1 + Real.log L) := by
  classical
  let f : Fin L → ℤ := fun z => (z.val : ℤ) - (x.val : ℤ)
  have hf : Function.Injective f := by
    intro z w h
    apply Fin.ext
    have hsub : (z.val : ℤ) - (x.val : ℤ) = (w.val : ℤ) - (x.val : ℤ) := h
    have hval : (z.val : ℤ) = (w.val : ℤ) := by omega
    exact_mod_cast hval
  have hsub : Finset.univ.image f ⊆ Finset.Icc (-(L : ℤ)) L := by
    intro d hd
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hd
    have hx := x.isLt
    have hz := z.isLt
    simp only [Finset.mem_Icc, f]
    constructor <;> omega
  have heven : (fun d : ℤ => |(d : ℝ)|⁻¹).Even := by
    intro d
    simp
  have habs (n : ℕ) : |(n : ℝ) + 1| = (n : ℝ) + 1 :=
    abs_of_nonneg (by positivity)
  calc
    (∑ z : Fin L, |(x.val : ℝ) - z.val|⁻¹) =
        ∑ d ∈ Finset.univ.image f, |(d : ℝ)|⁻¹ := by
      rw [Finset.sum_image (fun _ _ _ _ h => hf h)]
      apply Finset.sum_congr rfl
      intro z _
      simp [f, abs_sub_comm]
    _ ≤ ∑ d ∈ Finset.Icc (-(L : ℤ)) L, |(d : ℝ)|⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = 2 * (harmonic L : ℝ) := by
      rw [Finset.sum_Icc_of_even_eq_range heven, Finset.sum_range_succ']
      simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
        nsmul_eq_mul, habs]
    _ ≤ 2 * (1 + Real.log L) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log L) (by norm_num)

/-- The coordinates are `(block,row,x,x')`; the diagonal is explicitly excluded. -/
def nearPairs {K L : ℕ} (Z : Pin K L → (ℝ × ℝ) → ℤ) (B : ℤ) (a : ℝ × ℝ) :
    Finset (Fin K × (Fin L × (Fin L × Fin L))) := by
  classical
  exact Finset.univ.filter fun p => p.2.2.1 ≠ p.2.2.2 ∧
    |Z (p.1, p.2.2.1, p.2.1) a - Z (p.1, p.2.2.2, p.2.1) a| < B

/-- Actual ordered distinct same-row count, as a real-valued finite cardinality. -/
def count {K L : ℕ} (Z : Pin K L → (ℝ × ℝ) → ℤ) (B : ℤ) (a : ℝ × ℝ) : ℝ :=
  (nearPairs Z B a).card

private def pairIndicator {K L : ℕ} (Z : Pin K L → (ℝ × ℝ) → ℤ)
    (B : ℤ) (good : Set (ℝ × ℝ)) (b : Fin K) (y x z : Fin L) :
    (ℝ × ℝ) → ℝ :=
  good.indicator (fun a => if x ≠ z ∧ |Z (b, x, y) a - Z (b, z, y) a| < B
    then 1 else 0)

private lemma pairIndicator_bounds {K L : ℕ} (Z : Pin K L → (ℝ × ℝ) → ℤ)
    (B : ℤ) (good : Set (ℝ × ℝ)) (b : Fin K) (y x z : Fin L) (a : ℝ × ℝ) :
    0 ≤ pairIndicator Z B good b y x z a ∧ pairIndicator Z B good b y x z a ≤ 1 := by
  classical
  simp only [pairIndicator, Set.indicator]
  split_ifs <;> norm_num

private lemma pairIndicator_measurable {K L : ℕ} {Z : Pin K L → (ℝ × ℝ) → ℤ}
    (hZ : ∀ i, Measurable (Z i)) (B : ℤ) {good : Set (ℝ × ℝ)}
    (hg : MeasurableSet good) (b : Fin K) (y x z : Fin L) :
    Measurable (pairIndicator Z B good b y x z) := by
  classical
  exact ((measurable_of_countable (fun t : ℤ =>
    if x ≠ z ∧ |t| < B then (1 : ℝ) else 0)).comp
      ((hZ (b, x, y)).sub (hZ (b, z, y)))).indicator hg

private lemma pairIndicator_integrable {K L : ℕ} {Z : Pin K L → (ℝ × ℝ) → ℤ}
    {δ : ℝ} (hδ : 0 < δ) (hZ : ∀ i, Measurable (Z i)) (B : ℤ)
    {good : Set (ℝ × ℝ)} (hg : MeasurableSet good) (b : Fin K) (y x z : Fin L) :
    Integrable (pairIndicator Z B good b y x z) (parameterMeasure δ) := by
  letI := parameterMeasure_probability hδ
  exact Integrable.of_bound (pairIndicator_measurable hZ B hg b y x z).aestronglyMeasurable
    1 (Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pairIndicator_bounds _ _ _ _ _ _ _ _).1]
      exact (pairIndicator_bounds _ _ _ _ _ _ _ _).2)

lemma good_count_eq_sum {K L : ℕ} (Z : Pin K L → (ℝ × ℝ) → ℤ) (B : ℤ)
    (good : Set (ℝ × ℝ)) (a : ℝ × ℝ) :
    good.indicator (count Z B) a = ∑ b, ∑ y, ∑ x, ∑ z, pairIndicator Z B good b y x z a := by
  classical
  by_cases ha : a ∈ good
  · simp only [Set.indicator_of_mem ha, pairIndicator, count, nearPairs,
      Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      Fintype.sum_prod_type]
  · simp [Set.indicator_of_notMem ha, pairIndicator, ha]


lemma integrable_good_count {K L : ℕ} {Z : Pin K L → (ℝ × ℝ) → ℤ}
    {δ : ℝ} (hδ : 0 < δ) (hZ : ∀ i, Measurable (Z i)) (B : ℤ)
    {good : Set (ℝ × ℝ)} (hg : MeasurableSet good) :
    Integrable (good.indicator (count Z B)) (parameterMeasure δ) := by
  simp_rw [show good.indicator (count Z B) = fun a =>
    ∑ b, ∑ y, ∑ x, ∑ z, pairIndicator Z B good b y x z a from
      funext (good_count_eq_sum Z B good)]
  exact integrable_finsetSum _ fun b _ => integrable_finsetSum _ fun y _ =>
    integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun z _ =>
      pairIndicator_integrable hδ hZ B hg b y x z


/-- The sole structural assumption: a bounded error in differences on a block-row.
The deterministic errors may be arbitrarily large; only their cancellation matters. -/
def RowDifference {K L : ℕ} (Z : Pin K L → (ℝ × ℝ) → ℤ) (e : Pin K L → ℝ)
    (good : Set (ℝ × ℝ)) (δ E : ℝ) : Prop :=
  ∀ a ∈ good, ∀ i j, group i = group j →
    |((Z i a - Z j a : ℤ) : ℝ) -
      ((1 - δ + a.1) * L * ((i.2.1.val : ℝ) - j.2.1.val) + (e i - e j))| ≤ 2 * E

/-- Actual near levels on the good event imply a real affine strip. -/
theorem near_implies_affine_strip {K L : ℕ} {Z : Pin K L → (ℝ × ℝ) → ℤ}
    {e : Pin K L → ℝ} {good : Set (ℝ × ℝ)} {δ E : ℝ} {B : ℤ}
    (hrow : RowDifference Z e good δ E) {a : ℝ × ℝ} (ha : a ∈ good)
    {i j : Pin K L} (hg : group i = group j) (hn : |Z i a - Z j a| < B) :
    |(1 - δ + a.1) * L * ((i.2.1.val : ℝ) - j.2.1.val) + (e i - e j)| <
      (B : ℝ) + 2 * E := by
  have h := hrow a ha i j hg
  have hn' : |((Z i a - Z j a : ℤ) : ℝ)| < (B : ℝ) := by exact_mod_cast hn
  have ht := abs_add_le ((Z i a - Z j a : ℤ) : ℝ)
    (((1 - δ + a.1) * L * ((i.2.1.val : ℝ) - j.2.1.val) + (e i - e j)) -
      ((Z i a - Z j a : ℤ) : ℝ))
  have he :
      ((Z i a - Z j a : ℤ) : ℝ) +
        (((1 - δ + a.1) * L * ((i.2.1.val : ℝ) - j.2.1.val) + (e i - e j)) -
          ((Z i a - Z j a : ℤ) : ℝ)) =
        (1 - δ + a.1) * L * ((i.2.1.val : ℝ) - j.2.1.val) + (e i - e j) := by ring
  rw [he, abs_sub_comm] at ht
  linarith

private theorem integral_pairIndicator_le {K L : ℕ} {Z : Pin K L → (ℝ × ℝ) → ℤ}
    {e : Pin K L → ℝ} {good : Set (ℝ × ℝ)} {δ E : ℝ} {B : ℤ}
    (hδ : 0 < δ) (hL : 0 < L) (hE : 0 ≤ E) (hB : 0 < B)
    (hZ : ∀ i, Measurable (Z i)) (hg : MeasurableSet good)
    (hrow : RowDifference Z e good δ E) (b : Fin K) (y x z : Fin L) :
    (∫ a, pairIndicator Z B good b y x z a ∂parameterMeasure δ) ≤
      (2 * ((B : ℝ) + 2 * E) / (δ * L)) * |(x.val : ℝ) - z.val|⁻¹ := by
  classical
  by_cases hxz : x = z
  · subst z
    simp [pairIndicator, Set.indicator]
  have hd : (x.val : ℝ) - z.val ≠ 0 := by
    intro h
    apply hxz
    apply Fin.ext
    exact_mod_cast (sub_eq_zero.mp h)
  have hL' : 0 < (L : ℝ) := by exact_mod_cast hL
  have hB' : 0 < (B : ℝ) := by exact_mod_cast hB
  let R : ℝ := (B : ℝ) + 2 * E
  let u : ℝ := L * ((x.val : ℝ) - z.val)
  let c : ℝ := (1 - δ) * L * ((x.val : ℝ) - z.val) +
    (e (b, x, y) - e (b, z, y))
  have hu : u ≠ 0 := mul_ne_zero hL'.ne' hd
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have he (a : ℝ × ℝ) : c + u * a.1 =
      (1 - δ + a.1) * L * ((x.val : ℝ) - z.val) +
        (e (b, x, y) - e (b, z, y)) := by dsimp [c, u]; ring
  have hpoint (a : ℝ × ℝ) : pairIndicator Z B good b y x z a ≤
      stripIndicator R (c + u * a.1) := by
    by_cases ha : a ∈ good
    · by_cases hn : |Z (b, x, y) a - Z (b, z, y) a| < B
      · have hs := near_implies_affine_strip hrow ha (i := (b, x, y))
          (j := (b, z, y)) rfl hn
        rw [← he a] at hs
        simp [pairIndicator, ha, hxz, hn, stripIndicator, Set.indicator,
          show -R < c + u * a.1 ∧ c + u * a.1 < R from abs_lt.mp hs]
      · simpa [pairIndicator, ha, hn] using (stripIndicator_bounds R (c + u * a.1)).1
    · simpa [pairIndicator, ha] using (stripIndicator_bounds R (c + u * a.1)).1
  letI := parameterMeasure_probability hδ
  have hi : Integrable (fun a : ℝ × ℝ => stripIndicator R (c + u * a.1))
      (parameterMeasure δ) :=
    Integrable.of_bound ((stripIndicator_measurable R).comp (by fun_prop)).aestronglyMeasurable
      1 (Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (stripIndicator_bounds _ _).1]
        exact (stripIndicator_bounds _ _).2)
  calc
    _ ≤ ∫ a, stripIndicator R (c + u * a.1) ∂parameterMeasure δ :=
      integral_mono (pairIndicator_integrable hδ hZ B hg b y x z) hi hpoint
    _ ≤ 2 * R / (δ * |u|) := integral_affine_strip_le hδ hR hu c
    _ = _ := by
      dsimp [R, u]
      rw [abs_mul, abs_of_pos hL']
      simp only [div_eq_mul_inv, mul_inv]
      ring


/-- Actual averaged ordered same-row count, with the absolute constant `4`.
All parameter restrictions occur inside the integrand. -/
theorem integral_good_count_le {K L : ℕ} {Z : Pin K L → (ℝ × ℝ) → ℤ}
    {e : Pin K L → ℝ} {good : Set (ℝ × ℝ)} {δ E : ℝ} {B : ℤ}
    (hδ : 0 < δ) (hL : 0 < L) (hE : 0 ≤ E) (hB : 0 < B)
    (hZ : ∀ i, Measurable (Z i)) (hg : MeasurableSet good)
    (hrow : RowDifference Z e good δ E) :
    (∫ a, good.indicator (count Z B) a ∂parameterMeasure δ) ≤
      4 / δ * K * L * ((B : ℝ) + 2 * E) * (1 + Real.log L) := by
  have hi := pairIndicator_integrable hδ hZ B hg
  have hL' : 0 < (L : ℝ) := by exact_mod_cast hL
  have hB' : 0 < (B : ℝ) := by exact_mod_cast hB
  let A : ℝ := 2 * ((B : ℝ) + 2 * E) / (δ * L)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  simp_rw [good_count_eq_sum]
  rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ fun y _ =>
    integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun z _ => hi b y x z)]
  simp_rw [integral_finsetSum _ (fun y _ => integrable_finsetSum _ fun x _ =>
    integrable_finsetSum _ fun z _ => hi _ y x z)]
  simp_rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ fun z _ => hi _ _ x z)]
  simp_rw [integral_finsetSum _ (fun z _ => hi _ _ _ z)]
  calc
    _ ≤ ∑ b : Fin K, ∑ y : Fin L, ∑ x : Fin L, ∑ z : Fin L,
        A * |(x.val : ℝ) - z.val|⁻¹ :=
      Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun y _ =>
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ =>
          integral_pairIndicator_le hδ hL hE hB hZ hg hrow b y x z
    _ ≤ ∑ _b : Fin K, ∑ _y : Fin L, ∑ _x : Fin L,
        A * (2 * (1 + Real.log L)) := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro y _
      apply Finset.sum_le_sum
      intro x _
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_inverse_row_difference_le L x) hA
    _ = 4 / δ * K * L * ((B : ℝ) + 2 * E) * (1 + Real.log L) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [A]
      field_simp
      <;> ring

/-- Injective reindexing cannot increase the ordered count appearing in
`JitterVariance.jitter_variance_bound`; selected pins do not remove original pins. -/
theorem reindexed_ordered_count_le {K L M : ℕ}
    (ι : Fin M → Pin K L) (hι : Function.Injective ι)
    (Z : Pin K L → (ℝ × ℝ) → ℤ) (B : ℤ) (a : ℝ × ℝ) :
    (Finset.univ.filter (fun p : Fin M × Fin M =>
      p.1 ≠ p.2 ∧ group (ι p.1) = group (ι p.2) ∧
        |Z (ι p.1) a - Z (ι p.2) a| < B)).card ≤ (nearPairs Z B a).card := by
  classical
  let f : Fin M × Fin M → Fin K × (Fin L × (Fin L × Fin L)) :=
    fun p => ((ι p.1).1, (ι p.1).2.2, (ι p.1).2.1, (ι p.2).2.1)
  have recover (p : Fin M × Fin M) (hg : group (ι p.1) = group (ι p.2)) :
      (ι p.1, ι p.2) =
        (((f p).1, (f p).2.2.1, (f p).2.1),
          ((f p).1, (f p).2.2.2, (f p).2.1)) := by
    have hb := congrArg Prod.fst hg
    have hy := congrArg Prod.snd hg
    dsimp [group] at hb hy
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact hb.symm
      · exact Prod.ext rfl hy.symm
  apply Finset.card_le_card_of_injOn f
  · intro p hp
    obtain ⟨hne, hg, hn⟩ := (Finset.mem_filter.mp hp).2
    have hr := recover p hg
    have hr₁ : ι p.1 = ((f p).1, (f p).2.2.1, (f p).2.1) :=
      congrArg Prod.fst hr
    have hr₂ : ι p.2 = ((f p).1, (f p).2.2.2, (f p).2.1) :=
      congrArg Prod.snd hr
    have hne' : (f p).2.2.1 ≠ (f p).2.2.2 := by
      intro hx
      apply hne
      apply hι
      rw [hr₁, hr₂, hx]
    have hn' := hn
    rw [hr₁, hr₂] at hn'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne', hn'⟩
  · intro p hp q hq hpq
    have hp' := recover p (Finset.mem_filter.mp hp).2.2.1
    have hq' := recover q (Finset.mem_filter.mp hq).2.2.1
    have hr : (ι p.1, ι p.2) = (ι q.1, ι q.2) := by
      rw [hp', hq', hpq]
    exact Prod.ext (hι (congrArg Prod.fst hr)) (hι (congrArg Prod.snd hr))

/-- Twice the canonically unordered count used in the jitter variance theorem
is bounded by the full original ordered row count, for every parameter. -/
theorem twice_reindexed_unordered_count_le {K L M : ℕ}
    (ι : Fin M → Pin K L) (hι : Function.Injective ι)
    (Z : Pin K L → (ℝ × ℝ) → ℤ) (B : ℤ) (a : ℝ × ℝ) :
    2 * ((Finset.univ.filter (fun p : Fin M × Fin M =>
      p.1 < p.2 ∧ group (ι p.1) = group (ι p.2) ∧
        |Z (ι p.1) a - Z (ι p.2) a| < B)).card : ℝ) ≤ count Z B a := by
  have h := reindexed_ordered_count_le ι hι Z B a
  rw [JitterVariance.ordered_near_count_eq_twice_unordered
    (fun i => Z (ι i) a) (fun i => group (ι i)) B] at h
  unfold count
  exact_mod_cast h

end DistanceCounts.RowPairAverage
end

noncomputable section

namespace DistanceCounts.SkewScores
open Set MeasureTheory SkewParameters
def score {B : Type*} {L : ℕ} (δ : ℝ) (Z : B × GridPairs.Grid L → ℤ)
    (i : B × GridPairs.Grid L) (a : ℝ × ℝ) : ℤ :=
  Z i + ⌊alpha δ a * L * i.2.1.val⌋ + ⌊beta a * L * i.2.2.val⌋
def floorError (δ : ℝ) (L : ℕ) (p : GridPairs.Grid L) (a : ℝ × ℝ) : ℝ :=
  -Int.fract (alpha δ a * L * p.1.val) - Int.fract (beta a * L * p.2.val)
theorem measurable_score {B : Type*} {L : ℕ} (δ : ℝ)
    (Z : B × GridPairs.Grid L → ℤ) (i : B × GridPairs.Grid L) :
    Measurable (score δ Z i) := by
  unfold score alpha beta
  fun_prop
theorem score_affine {B : Type*} {L : ℕ} (δ : ℝ)
    (Z : B × GridPairs.Grid L → ℤ) (i : B × GridPairs.Grid L) (a : ℝ × ℝ) :
    (score δ Z i a : ℝ) = (Z i : ℝ) + alpha δ a * L * i.2.1.val +
      beta a * L * i.2.2.val + floorError δ L i.2 a := by
  simp only [score, Int.cast_add, floorError, Int.fract]
  ring
theorem floorError_le {δ : ℝ} {L : ℕ} {E : ℝ} {a : ℝ × ℝ}
    (ha : a ∈ good δ L E) (q : GridPairs.Grid L) : |floorError δ L q a| ≤ 2 * E + 1 := by
  have hE : 1 ≤ E := ha.2
  unfold floorError
  apply abs_le.mpr
  constructor <;> linarith [Int.fract_nonneg (alpha δ a * L * q.1.val),
    Int.fract_lt_one (alpha δ a * L * q.1.val), Int.fract_nonneg (beta a * L * q.2.val),
    Int.fract_lt_one (beta a * L * q.2.val)]
theorem score_error_le {B : Type*} {δ : ℝ} {L : ℕ} {E : ℝ}
    (Z0 : B × GridPairs.Grid L → ℤ) {a : ℝ × ℝ}
    (ha : a ∈ good δ L E) (i : B × GridPairs.Grid L) :
    |(score δ Z0 i a : ℝ) - ((Z0 i : ℝ) + alpha δ a * L * i.2.1.val +
      beta a * L * i.2.2.val)| ≤ 2 * E + 1 := by
  rw [score_affine, add_sub_cancel_left]
  exact floorError_le ha i.2

/-- Deterministic coarse errors cancel correctly within a block-row. -/
theorem rowDifference {K L : ℕ} {δ E : ℝ}
    (Z0 : RowPairAverage.Pin K L → ℤ) (D : Fin K → ℝ)
    (e : RowPairAverage.Pin K L → ℝ)
    (hZ0 : ∀ i, (Z0 i : ℝ) = D i.1 * (L : ℝ) ^ 2 + e i) :
    RowPairAverage.RowDifference (score δ Z0) e (good δ L E) δ (2 * E + 1) := by
  intro a ha i j hij
  have hb : i.1 = j.1 := congrArg (fun x : Fin K × Fin L => x.1) hij
  have hy : i.2.2 = j.2.2 := congrArg (fun x : Fin K × Fin L => x.2) hij
  have heq : ((score δ Z0 i a - score δ Z0 j a : ℤ) : ℝ) -
      ((1 - δ + a.1) * L * ((i.2.1.val : ℝ) - j.2.1.val) + (e i - e j)) =
      floorError δ L i.2 a - floorError δ L j.2 a := by
    rw [Int.cast_sub, score_affine, score_affine, hZ0 i, hZ0 j, hb, hy]
    unfold alpha
    ring
  rw [heq]
  have hi := abs_le.mp (floorError_le ha i.2)
  have hj := abs_le.mp (floorError_le ha j.2)
  rw [abs_le]
  constructor <;> linarith [hi.1, hi.2, hj.1, hj.2]

/-- A fixed finite integer window, not a parameter-dependent choice of levels. -/
theorem score_range {B : Type*} {K L : ℕ} {δ E : ℝ}
    (Z0 : B × GridPairs.Grid L → ℤ) (D : B → ℝ)
    (e : B × GridPairs.Grid L → ℝ)
    (hZ0 : ∀ i, (Z0 i : ℝ) = D i.1 * (L : ℝ) ^ 2 + e i)
    (hD : ∀ b, 0 ≤ D b ∧ D b ≤ K)
    (he : ∀ i, |e i| ≤ (L : ℝ) ^ 2)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hE : 2 * E + 1 ≤ (L : ℝ) ^ 2)
    {a : ℝ × ℝ} (ha : a ∈ good δ L E) (i : B × GridPairs.Grid L) :
    -(2 * (L : ℤ) ^ 2) ≤ score δ Z0 i a ∧
      score δ Z0 i a ≤ ((K : ℤ) + 5) * (L : ℤ) ^ 2 := by
  have hα : 0 ≤ alpha δ a ∧ alpha δ a ≤ 1 := by
    unfold alpha
    constructor <;> linarith [ha.1.1.1, ha.1.1.2]
  have hβ : 0 ≤ beta a ∧ beta a ≤ 2 := by
    unfold beta
    constructor <;> linarith [ha.1.2.1, ha.1.2.2]
  have hx : (i.2.1.val : ℝ) ≤ L := by exact_mod_cast i.2.1.isLt.le
  have hy : (i.2.2.val : ℝ) ≤ L := by exact_mod_cast i.2.2.isLt.le
  have hAx0 : 0 ≤ alpha δ a * L * i.2.1.val :=
    mul_nonneg (mul_nonneg hα.1 (Nat.cast_nonneg L)) (Nat.cast_nonneg _)
  have hBy0 : 0 ≤ beta a * L * i.2.2.val :=
    mul_nonneg (mul_nonneg hβ.1 (Nat.cast_nonneg L)) (Nat.cast_nonneg _)
  have hAx : alpha δ a * L * i.2.1.val ≤ (L : ℝ) ^ 2 := by
    calc
      _ ≤ 1 * (L : ℝ) * L :=
        mul_le_mul
          (mul_le_mul_of_nonneg_right hα.2 (Nat.cast_nonneg L))
          hx (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have hBy : beta a * L * i.2.2.val ≤ 2 * (L : ℝ) ^ 2 := by
    calc
      _ ≤ 2 * (L : ℝ) * L :=
        mul_le_mul
          (mul_le_mul_of_nonneg_right hβ.2 (Nat.cast_nonneg L))
          hy (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have hD0 : 0 ≤ D i.1 * (L : ℝ) ^ 2 := mul_nonneg (hD i.1).1 (sq_nonneg _)
  have hDK : D i.1 * (L : ℝ) ^ 2 ≤ K * (L : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right (hD i.1).2 (sq_nonneg _)
  have herr := abs_le.mp (score_error_le Z0 ha i)
  have hei := abs_le.mp (he i)
  rw [hZ0 i] at herr
  have hlo : -(2 * (L : ℝ) ^ 2) ≤ (score δ Z0 i a : ℝ) := by
    linarith [herr.1, hei.1]
  have hhi : (score δ Z0 i a : ℝ) ≤ ((K : ℝ) + 5) * (L : ℝ) ^ 2 := by
    nlinarith [herr.2, hei.2]
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
end DistanceCounts.SkewScores
end

noncomputable section

namespace DistanceCounts.ProjectionGoodParameters
open Set MeasureTheory Filter ProjectionDensity ParameterKernel SkewParameters
open scoped Topology
theorem uniformIntervalMeasure_Icc {δ : ℝ} (hδ : 0 < δ) :
    uniformIntervalMeasure δ (Icc 0 δ) = 1 := by
  have hi : Icc (0 : ℝ) δ ∩ Ico 0 δ = Ico 0 δ :=
    inter_eq_right.mpr (fun _ hx => ⟨hx.1, hx.2.le⟩)
  simp [uniformIntervalMeasure, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Icc, hi, hδ.ne',
    ENNReal.inv_mul_cancel, ENNReal.ofReal_ne_zero_iff.mpr hδ]

theorem parameterMeasure_rectangle {δ : ℝ} (hδ : 0 < δ) :
    parameterMeasure δ (Icc (0 : ℝ) δ ×ˢ Icc (0 : ℝ) 1) = 1 := by
  letI := uniformIntervalMeasure_probability hδ
  letI := uniformIntervalMeasure_probability (by norm_num : (0 : ℝ) < 1)
  rw [parameterMeasure, Measure.prod_prod, uniformIntervalMeasure_Icc hδ,
    uniformIntervalMeasure_Icc (by norm_num : (0 : ℝ) < 1), mul_one]


theorem eventually_good_mass_ge_half {δ : ℝ} (hδ : 0 < δ) (_hδ1 : δ ≤ 1) :
    ∀ᶠ L : ℕ in atTop, (1 / 2 : ℝ) ≤ (parameterMeasure δ).real
      (good δ L ((L : ℝ) ^ (1 / 10 : ℝ))) := by
  filter_upwards [eventually_ge_atTop 1] with L hL
  have h : (1 : ℝ) ≤ (L : ℝ) ^ (1 / 10 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hL) (by norm_num)
  have he : (good δ L ((L : ℝ) ^ (1 / 10 : ℝ))) = Icc (0 : ℝ) δ ×ˢ Icc (0 : ℝ) 1 := by
    ext a; exact ⟨And.left, fun ha => ⟨ha, h⟩⟩
  rw [he, Measure.real, parameterMeasure_rectangle hδ]
  norm_num
end DistanceCounts.ProjectionGoodParameters
end

/-! First-moment selection inside a genuine positive-probability good event. -/

namespace DistanceCounts.ParameterSelection

open MeasureTheory Set

/-- No independence between the good event and the cost is assumed. -/
theorem exists_good_le_twice_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {good : Set Ω} {f : Ω → ℝ}
    (hgood : (1 / 2 : ℝ) ≤ μ.real good) (hf : Integrable f μ)
    (hf0 : 0 ≤ᵐ[μ] f) :
    ∃ a ∈ good, f a ≤ 2 * ∫ x, f x ∂μ := by
  have hpos : 0 < μ.real good := lt_of_lt_of_le (by norm_num) hgood
  have hn : μ good ≠ 0 := by
    intro hzero
    have hr : μ.real good = 0 := by simp only [measureReal_def, hzero, ENNReal.toReal_zero]
    linarith
  obtain ⟨a, ha, hfa⟩ := exists_le_setAverage hn (measure_ne_top μ good) hf.integrableOn
  rw [setAverage_eq, smul_eq_mul] at hfa
  have hinv : (μ.real good)⁻¹ ≤ (2 : ℝ) := by
    rw [← one_div]
    apply (div_le_iff₀ hpos).mpr
    linarith
  refine ⟨a, ha, hfa.trans ?_⟩
  calc
    (μ.real good)⁻¹ * (∫ x in good, f x ∂μ) ≤ (μ.real good)⁻¹ * ∫ x, f x ∂μ :=
      mul_le_mul_of_nonneg_left (setIntegral_le_integral hf hf0) (inv_nonneg.mpr hpos.le)
    _ ≤ 2 * ∫ x, f x ∂μ :=
      mul_le_mul_of_nonneg_right hinv (integral_nonneg_of_ae hf0)

end DistanceCounts.ParameterSelection

/-! A common numerical parameter is chosen before any geometric extension. -/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace DistanceCounts.FineParameterChoice

open ParameterKernel ConstructionScales

/-- A deterministic envelope, independent of the projection parameters. -/
def perturbationEnvelope (r : ℕ → ℝ) (L : ℕ) : ℝ :=
  |r L| + h L + 1 / (L : ℝ) ^ 2

theorem perturbation_le {K L : ℕ} (D : Fin K → ℤ)
    (Z0 : Fin K × GridPairs.Grid L → ℤ) {r : ℝ} (hL : 0 < L)
    (herr : ∀ i, |FineData.error D Z0 i| ≤ r * (L : ℝ) ^ 2)
    (b : Fin K) (p : GridPairs.Grid L) :
    |FineData.perturbation D Z0 (H L) b p| ≤ |r| + h L + 1 / (L : ℝ) ^ 2 := by
  have hm : 0 < (L : ℝ) ^ 2 := by positivity
  have he : |FineData.error D Z0 (b, p) / (L : ℝ) ^ 2| ≤ |r| := by
    rw [abs_div, abs_of_nonneg (sq_nonneg (L : ℝ))]
    apply (div_le_iff₀ hm).mpr
    exact (herr (b, p)).trans (mul_le_mul_of_nonneg_right (le_abs_self r) hm.le)
  have hh : 0 ≤ (H L : ℝ) / (L : ℝ) ^ 2 := by positivity
  have hu : 0 ≤ 1 / (L : ℝ) ^ 2 := by positivity
  calc
    _ ≤ |FineData.error D Z0 (b, p) / (L : ℝ) ^ 2 -
        (H L : ℝ) / (L : ℝ) ^ 2| + |1 / (L : ℝ) ^ 2| := abs_add_le _ _
    _ ≤ (|FineData.error D Z0 (b, p) / (L : ℝ) ^ 2| +
        |(H L : ℝ) / (L : ℝ) ^ 2|) + |1 / (L : ℝ) ^ 2| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ |r| + h L + 1 / (L : ℝ) ^ 2 := by
      rw [abs_of_nonneg hh, abs_of_nonneg hu]
      exact add_le_add (add_le_add he (le_refl (h L))) le_rfl

theorem tendsto_perturbationEnvelope {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (perturbationEnvelope r) atTop (𝓝 0) := by
  have hi : Tendsto (fun L : ℕ => 1 / (L : ℝ) ^ 2) atTop (𝓝 0) := by
    have hp : Tendsto (fun L : ℕ => (L : ℝ) ^ 2) atTop atTop := by
      simpa only [Function.comp_def] using
        (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp
          (tendsto_natCast_atTop_atTop :
            Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop)
    simpa only [Function.comp_def, one_div] using
      (tendsto_inv_atTop_zero :
        Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp hp
  unfold perturbationEnvelope
  simpa only [abs_zero, add_zero] using
    (hr.abs.add tendsto_h).add hi

private theorem eventually_h_pos : ∀ᶠ L : ℕ in atTop, 0 < h L := by
  filter_upwards [tendsto_H.eventually (eventually_gt_atTop 0),
    eventually_gt_atTop 0] with L hH hL
  unfold h
  positivity

/-- The sum includes every original block, not just a witness subset. -/
def empiricalCost {K L : ℕ} (δ : ℝ) (D : Fin K → ℤ)
    (Z0 : Fin K × GridPairs.Grid L → ℤ) (a : ℝ × ℝ) : ℝ :=
  ∑ b : Fin K, MesoscopicProjection.squareError L δ (h L)
    (FineData.perturbation D Z0 (H L) b) a

/-- The actual ordered distinct same-row count, restricted only in the integrand. -/
def nearCost {K L : ℕ} (δ : ℝ)
    (Z0 : Fin K × GridPairs.Grid L → ℤ) (a : ℝ × ℝ) : ℝ :=
  (SkewParameters.good δ L (E L)).indicator
    (RowPairAverage.count (SkewScores.score δ Z0) (B K L : ℤ)) a / (L : ℝ) ^ 2

/-- Both statistics are charged to one nonnegative cost, with no independence claim. -/
def cost {K L : ℕ} (δ : ℝ) (D : Fin K → ℤ)
    (Z0 : Fin K × GridPairs.Grid L → ℤ) (a : ℝ × ℝ) : ℝ :=
  empiricalCost δ D Z0 a + nearCost δ Z0 a

theorem empiricalCost_nonneg {K L : ℕ} (δ : ℝ) (D : Fin K → ℤ)
    (Z0 : Fin K × GridPairs.Grid L → ℤ) (a : ℝ × ℝ) :
    0 ≤ empiricalCost δ D Z0 a :=
  Finset.sum_nonneg fun b _ => MesoscopicProjection.squareError_nonneg _ _ _ _ _

theorem nearCost_nonneg {K L : ℕ} (δ : ℝ)
    (Z0 : Fin K × GridPairs.Grid L → ℤ) (a : ℝ × ℝ) :
    0 ≤ nearCost δ Z0 a := by
  apply div_nonneg _ (sq_nonneg _)
  exact Set.indicator_nonneg (fun a _ => Nat.cast_nonneg _) a

theorem cost_nonneg {K L : ℕ} (δ : ℝ) (D : Fin K → ℤ)
    (Z0 : Fin K × GridPairs.Grid L → ℤ) (a : ℝ × ℝ) :
    0 ≤ cost δ D Z0 a :=
  add_nonneg (empiricalCost_nonneg δ D Z0 a) (nearCost_nonneg δ Z0 a)

theorem integrable_empiricalCost {K L : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hL : 0 < L) (hh : 0 < h L)
    (D : Fin K → ℤ) (Z0 : Fin K × GridPairs.Grid L → ℤ) :
    Integrable (empiricalCost δ D Z0) (parameterMeasure δ) :=
  integrable_finsetSum _ fun b _ =>
    MesoscopicProjection.integrable_squareError hL hδ hδ1 hh _

theorem integrable_nearCost {K L : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Z0 : Fin K × GridPairs.Grid L → ℤ) :
    Integrable (nearCost δ Z0) (parameterMeasure δ) :=
  (RowPairAverage.integrable_good_count hδ (SkewScores.measurable_score δ Z0)
    (B K L : ℤ) (SkewParameters.measurableSet_good δ L (E L))).div_const _

theorem integrable_cost {K L : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hL : 0 < L) (hh : 0 < h L)
    (D : Fin K → ℤ) (Z0 : Fin K × GridPairs.Grid L → ℤ) :
    Integrable (cost δ D Z0) (parameterMeasure δ) :=
  (integrable_empiricalCost hδ hδ1 hL hh D Z0).add (integrable_nearCost hδ Z0)

/-- The coarse degree cancels within a row; only the literal floor errors remain. -/
theorem rowDifference {K L : ℕ} (δ : ℝ) (D : Fin K → ℤ)
    (Z0 : Fin K × GridPairs.Grid L → ℤ) :
    RowPairAverage.RowDifference (SkewScores.score δ Z0) (FineData.error D Z0)
      (SkewParameters.good δ L (E L)) δ (2 * E L + 1) :=
  SkewScores.rowDifference Z0 (fun b => (D b : ℝ)) (FineData.error D Z0)
    (FineData.decomposition D Z0)

theorem tendsto_integral_empiricalCost {K : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (D : Fin K → ℤ)
    (Z0 : (L : ℕ) → Fin K × GridPairs.Grid L → ℤ)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    (herr : ∀ᶠ L in atTop, ∀ i, |FineData.error D (Z0 L) i| ≤ r L * (L : ℝ) ^ 2) :
    Tendsto (fun L => ∫ a, empiricalCost δ D (Z0 L) a ∂parameterMeasure δ)
      atTop (𝓝 0) := by
  have hb (b : Fin K) : Tendsto (fun L =>
      MesoscopicProjection.expectedSquareError L δ (h L)
        (FineData.perturbation D (Z0 L) (H L) b)) atTop (𝓝 0) := by
    apply MesoscopicProjection.tendsto_expectedSquareError hδ hδ1 _
      eventually_h_pos tendsto_h tendsto_square_mul_h (tendsto_perturbationEnvelope hr)
    filter_upwards [herr, eventually_gt_atTop 0] with L he hL
    exact fun p => perturbation_le D (Z0 L) hL he b p
  have ht := tendsto_finset_sum (Finset.univ : Finset (Fin K)) (fun b _ => hb b)
  simp only [Finset.sum_const_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_h_pos, eventually_gt_atTop 0] with L hh hL
  symm
  exact integral_finsetSum _ fun b _ =>
    MesoscopicProjection.integrable_squareError hL hδ hδ1 hh _

theorem integral_nearCost_le {K L : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hL : 0 < L) (hB : 0 < B K L)
    (D : Fin K → ℤ) (Z0 : Fin K × GridPairs.Grid L → ℤ) :
    (∫ a, nearCost δ Z0 a ∂parameterMeasure δ) ≤
      (4 / δ) * ((K : ℝ) * ((B K L : ℝ) + 4 * E L + 2) *
        (1 + Real.log L) / L) := by
  have hE : 0 ≤ 2 * E L + 1 := by unfold E; positivity
  have hBi : (0 : ℤ) < B K L := by exact_mod_cast hB
  have hb := RowPairAverage.integral_good_count_le hδ hL hE hBi
    (SkewScores.measurable_score δ Z0) (SkewParameters.measurableSet_good δ L (E L))
    (rowDifference δ D Z0)
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  calc
    (∫ a : ℝ × ℝ, nearCost δ Z0 a ∂parameterMeasure δ) =
        (∫ a : ℝ × ℝ, (SkewParameters.good δ L (E L)).indicator
          (RowPairAverage.count (SkewScores.score δ Z0) (B K L : ℤ)) a
            ∂parameterMeasure δ) / (L : ℝ) ^ 2 := by
      simp only [nearCost, div_eq_mul_inv, integral_mul_const]
    _ ≤ (4 / δ * K * L * (((B K L : ℤ) : ℝ) + 2 * (2 * E L + 1)) *
        (1 + Real.log L)) / (L : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hb (sq_nonneg _)
    _ = _ := by push_cast; field_simp [hLr]; ring

theorem tendsto_integral_nearCost {K : ℕ} (hK : 0 < K) {δ : ℝ}
    (hδ : 0 < δ) (D : Fin K → ℤ)
    (Z0 : (L : ℕ) → Fin K × GridPairs.Grid L → ℤ) :
    Tendsto (fun L => ∫ a, nearCost δ (Z0 L) a ∂parameterMeasure δ)
      atTop (𝓝 0) := by
  have ht := (tendsto_rowMoment hK).const_mul (4 / δ)
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall fun L => integral_nonneg (nearCost_nonneg δ (Z0 L))) _ ht
  filter_upwards [eventually_pos hK, eventually_gt_atTop 0] with L hp hL
  exact integral_nearCost_le hδ hL hp.2.1 D (Z0 L)

theorem tendsto_integral_cost {K : ℕ} (hK : 0 < K) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (D : Fin K → ℤ)
    (Z0 : (L : ℕ) → Fin K × GridPairs.Grid L → ℤ)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    (herr : ∀ᶠ L in atTop, ∀ i, |FineData.error D (Z0 L) i| ≤ r L * (L : ℝ) ^ 2) :
    Tendsto (fun L => ∫ a, cost δ D (Z0 L) a ∂parameterMeasure δ)
      atTop (𝓝 0) := by
  have ht := (tendsto_integral_empiricalCost hδ hδ1 D Z0 hr herr).add
    (tendsto_integral_nearCost hK hδ D Z0)
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_h_pos, eventually_gt_atTop 0] with L hh hL
  exact (integral_add (integrable_empiricalCost hδ hδ1 hL hh D (Z0 L))
    (integrable_nearCost hδ (Z0 L))).symm

/-- An actual common parameter controls the full empirical sum and the actual
ordered near count. The envelope is nonnegative even at the early degenerate scales. -/
theorem exists_parameters {K : ℕ} (hK : 0 < K) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (D : Fin K → ℤ)
    (Z0 : (L : ℕ) → Fin K × GridPairs.Grid L → ℤ)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    (herr : ∀ᶠ L in atTop, ∀ i, |FineData.error D (Z0 L) i| ≤ r L * (L : ℝ) ^ 2) :
    ∃ ω : ℕ → ℝ, (∀ L, 0 ≤ ω L) ∧ Tendsto ω atTop (𝓝 0) ∧
      ∀ᶠ L in atTop, ∃ a ∈ SkewParameters.good δ L (E L),
        empiricalCost δ D (Z0 L) a ≤ ω L ∧
        RowPairAverage.count (SkewScores.score δ (Z0 L)) (B K L : ℤ) a /
          (L : ℝ) ^ 2 ≤ ω L := by
  letI := parameterMeasure_probability hδ
  let ω : ℕ → ℝ := fun L => 2 * ∫ a, cost δ D (Z0 L) a ∂parameterMeasure δ
  refine ⟨ω, (fun L => mul_nonneg (by norm_num)
    (integral_nonneg (cost_nonneg δ D (Z0 L)))), ?_, ?_⟩
  · simpa only [ω, mul_zero] using
      (tendsto_integral_cost hK hδ hδ1 D Z0 hr herr).const_mul 2
  · filter_upwards [ProjectionGoodParameters.eventually_good_mass_ge_half hδ hδ1.le,
      eventually_h_pos, eventually_gt_atTop 0] with L hg hh hL
    obtain ⟨a, ha, hc⟩ := ParameterSelection.exists_good_le_twice_integral hg
      (integrable_cost hδ hδ1 hL hh D (Z0 L))
      (Eventually.of_forall (cost_nonneg δ D (Z0 L)))
    change a ∈ SkewParameters.good δ L (E L) at ha
    change empiricalCost δ D (Z0 L) a + nearCost δ (Z0 L) a ≤ ω L at hc
    refine ⟨a, ha, ?_, ?_⟩
    · exact (le_add_of_nonneg_right (nearCost_nonneg δ (Z0 L) a)).trans hc
    · have hn : RowPairAverage.count (SkewScores.score δ (Z0 L)) (B K L : ℤ) a /
          (L : ℝ) ^ 2 = nearCost δ (Z0 L) a := by
        simp only [nearCost, Set.indicator_of_mem ha]
      rw [hn]
      exact (le_add_of_nonneg_left (empiricalCost_nonneg δ D (Z0 L) a)).trans hc

end DistanceCounts.FineParameterChoice
end

/-! Integer-bin occupancies and the exact continuous intensity of uniform integer jitter. -/

noncomputable section

namespace DistanceCounts.CountIntensity

open Finset MeasureTheory
open scoped Classical

/-- Actual occupancy after the integer levels have been chosen. -/
def binCount {M : ℕ} (Y : Fin M → ℤ) (B j : ℤ) : ℕ :=
  (univ.filter (fun i => Y i / B = j)).card

/-- The exact mean occupancy for a uniform shift from `0,...,H-1` at every pin. -/
def jitterMean {M : ℕ} (H : ℕ) (Z : Fin M → ℤ) (B j : ℤ) : ℝ :=
  (H : ℝ)⁻¹ * ∑ i : Fin M,
    ((univ.filter (fun r : Fin H => (Z i - (r.val : ℤ)) / B = j)).card : ℝ)

/-- Each possible integer output contributes its actual unit interval. -/
def intensity {M : ℕ} (H : ℕ) (Z : Fin M → ℤ) (t : ℝ) : ℝ :=
  ∑ i : Fin M, ProjectionDensity.box (H : ℝ) (t - ((Z i - (H : ℤ) + 1 : ℤ) : ℝ))

theorem binCount_cast {M : ℕ} (Y : Fin M → ℤ) (B j : ℤ) :
    (binCount Y B j : ℝ) = ∑ i : Fin M, if Y i / B = j then (1 : ℝ) else 0 := by
  simp only [binCount, Finset.sum_boole]


theorem intensity_nonneg {M H : ℕ} (hH : 0 < H) (Z : Fin M → ℤ) (t : ℝ) :
    0 ≤ intensity H Z t := by
  exact sum_nonneg fun _ _ => ProjectionDensity.box_nonneg (by exact_mod_cast hH) _

end DistanceCounts.CountIntensity
end

noncomputable section

namespace DistanceCounts.CountIntensity

open Set MeasureTheory
open scoped Classical

/-- The actual half-open unit cell of an integer output. -/
def unitCell (n : ℤ) : ℝ → ℝ :=
  (Ico (n : ℝ) ((n : ℝ) + 1)).indicator (fun _ => 1)

theorem integrable_unitCell (n : ℤ) : Integrable (unitCell n) := by
  exact (integrableOn_const (by simp :
    volume (Ico (n : ℝ) ((n : ℝ) + 1)) ≠ ⊤)).integrable_indicator measurableSet_Ico

theorem integral_unitCell (n : ℤ) : ∫ t, unitCell n t = 1 := by
  simp [unitCell, integral_indicator_const, Real.volume_real_Ico, smul_eq_mul]

private theorem adjacent_cells (a b c t : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    (Ico b c).indicator (fun _ : ℝ => (1 : ℝ)) t +
      (Ico a b).indicator (fun _ : ℝ => (1 : ℝ)) t =
        (Ico a c).indicator (fun _ : ℝ => (1 : ℝ)) t := by
  simp only [Set.indicator, mem_Ico]
  split_ifs <;> grind

/-- Exact pointwise tiling, including both endpoint conventions and negative centers. -/
theorem sum_unitCell (H : ℕ) (z : ℤ) (t : ℝ) :
    ∑ r : Fin H, unitCell (z - (r.val : ℤ)) t =
      (Ico ((z : ℝ) - H + 1) ((z : ℝ) + 1)).indicator (fun _ => 1) t := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    have he : (z : ℝ) - (↑(H + 1) : ℝ) + 1 = (z : ℝ) - H := by
      push_cast
      ring
    rw [he]
    have hc : unitCell (z - (H : ℤ)) t =
        (Ico ((z : ℝ) - H) ((z : ℝ) - H + 1)).indicator (fun _ => 1) t := by
      simp only [unitCell, Int.cast_sub, Int.cast_natCast]
    rw [hc]
    exact adjacent_cells _ _ _ _ (by linarith)
      (by have : (0 : ℝ) ≤ H := Nat.cast_nonneg H; linarith)

/-- The normalized long box is precisely the average of the integer-output cells. -/
theorem box_eq_mean_unitCell (H : ℕ) (z : ℤ) (t : ℝ) :
    ProjectionDensity.box (H : ℝ) (t - ((z - (H : ℤ) + 1 : ℤ) : ℝ)) =
      (H : ℝ)⁻¹ * ∑ r : Fin H, unitCell (z - (r.val : ℤ)) t := by
  rw [sum_unitCell, EmpiricalEnergy.box_translate]
  have ha : ((z - (H : ℤ) + 1 : ℤ) : ℝ) = (z : ℝ) - H + 1 := by
    simp only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_natCast]
  rw [ha]
  have hb : (z : ℝ) - H + 1 + H = (z : ℝ) + 1 := by ring
  rw [hb]
  by_cases ht : t ∈ Ico ((z : ℝ) - H + 1) ((z : ℝ) + 1) <;>
    simp [Set.indicator, ht, one_div]

/-- A unit cell never straddles an integer bin boundary. -/
theorem unitCell_mem_bin {B : ℤ} (hB : 0 < B) (j n : ℤ) {t : ℝ}
    (ht : t ∈ Ico (n : ℝ) ((n : ℝ) + 1)) :
    t ∈ Ico ((j * B : ℤ) : ℝ) (((j + 1) * B : ℤ) : ℝ) ↔ n / B = j := by
  rw [Int.ediv_eq_iff_of_pos hB]
  constructor
  · intro hj
    constructor
    · by_contra hn
      have hn' : n + 1 ≤ j * B := by omega
      have hn'' : (n : ℝ) + 1 ≤ ((j * B : ℤ) : ℝ) := by exact_mod_cast hn'
      linarith [ht.2, hj.1]
    · have hn : (n : ℝ) < (((j + 1) * B : ℤ) : ℝ) := lt_of_le_of_lt ht.1 hj.2
      have hn' : n < (j + 1) * B := by exact_mod_cast hn
      nlinarith
  · rintro ⟨hlo, hhi⟩
    have hlo' : ((j * B : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlo
    have hhi' : n + 1 ≤ (j + 1) * B := by nlinarith
    have hhi'' : (n : ℝ) + 1 ≤ (((j + 1) * B : ℤ) : ℝ) := by exact_mod_cast hhi'
    exact ⟨hlo'.trans ht.1, ht.2.trans_le hhi''⟩

/-- Exact cell/bin intersection, not an almost-everywhere replacement. -/
theorem bin_indicator_unitCell {B : ℤ} (hB : 0 < B) (j n : ℤ) (t : ℝ) :
    (Ico ((j * B : ℤ) : ℝ) (((j + 1) * B : ℤ) : ℝ)).indicator (unitCell n) t =
      if n / B = j then unitCell n t else 0 := by
  by_cases ht : t ∈ Ico (n : ℝ) ((n : ℝ) + 1)
  · have hm := unitCell_mem_bin hB j n ht
    by_cases hj : n / B = j
    · rw [Set.indicator_of_mem (hm.mpr hj), if_pos hj]
    · have hnot : t ∉ Ico ((j * B : ℤ) : ℝ) (((j + 1) * B : ℤ) : ℝ) :=
        fun h => hj (hm.mp h)
      rw [Set.indicator_of_notMem hnot, if_neg hj]
  · have hz : unitCell n t = 0 := Set.indicator_of_notMem ht _
    simp only [Set.indicator, hz, ite_self]

theorem integral_unitCell_bin {B : ℤ} (hB : 0 < B) (j n : ℤ) :
    (∫ t in Ico ((j * B : ℤ) : ℝ) (((j + 1) * B : ℤ) : ℝ), unitCell n t) =
      if n / B = j then (1 : ℝ) else 0 := by
  rw [← integral_indicator measurableSet_Ico]
  simp_rw [bin_indicator_unitCell hB]
  by_cases hj : n / B = j <;> simp [hj, integral_unitCell]

theorem measurable_intensity {M : ℕ} (H : ℕ) (Z : Fin M → ℤ) :
    Measurable (intensity H Z) := by
  exact Finset.measurable_sum Finset.univ fun i _ =>
    (ProjectionDensity.measurable_box _).comp (measurable_id.sub measurable_const)

theorem integrable_intensity {M : ℕ} (H : ℕ) (Z : Fin M → ℤ) :
    Integrable (intensity H Z) := by
  exact integrable_finsetSum Finset.univ fun i _ =>
    EmpiricalEnergy.integrable_box_translate _ _


/-- The discrete mean equals integration of its actual continuous intensity. -/
theorem jitterMean_eq_integral {M H : ℕ} (hH : 0 < H) (Z : Fin M → ℤ)
    {B : ℤ} (hB : 0 < B) (j : ℤ) :
    jitterMean H Z B j =
      ∫ t in Ico ((j * B : ℤ) : ℝ) (((j + 1) * B : ℤ) : ℝ), intensity H Z t := by
  unfold intensity
  rw [integral_finsetSum (μ := volume.restrict
      (Ico ((j * B : ℤ) : ℝ) (((j + 1) * B : ℤ) : ℝ)))
    (f := fun i : Fin M => fun t : ℝ =>
      ProjectionDensity.box (H : ℝ) (t - ((Z i - (H : ℤ) + 1 : ℤ) : ℝ)))
    Finset.univ (fun i _ =>
    (EmpiricalEnergy.integrable_box_translate _ _).integrableOn)]
  simp_rw [box_eq_mean_unitCell, integral_const_mul]
  rw [← Finset.mul_sum]
  unfold jitterMean
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum (μ := volume.restrict
      (Ico ((j * B : ℤ) : ℝ) (((j + 1) * B : ℤ) : ℝ)))
    (f := fun r : Fin H => fun t : ℝ => unitCell (Z i - (r.val : ℤ)) t)
    Finset.univ (fun r _ =>
    (integrable_unitCell (Z i - (r.val : ℤ))).integrableOn)]
  simp_rw [integral_unitCell_bin hB]
  simp only [Finset.sum_boole]

/-- The positive excess is integrable even though the constant function one is not. -/
theorem integrable_intensity_excess {M H : ℕ} (hH : 0 < H) (Z : Fin M → ℤ) :
    Integrable (fun t => max 0 (intensity H Z t - 1)) := by
  apply (integrable_intensity H Z).mono'
  · exact (measurable_const.max ((measurable_intensity H Z).sub measurable_const)).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact max_le (intensity_nonneg hH Z t) (by linarith)

/-- Distinct integer bins are genuinely disjoint, including their endpoints. -/
theorem intensity_bin_unique {B : ℤ} (hB : 0 < B) {j k : ℤ} {t : ℝ}
    (hj : t ∈ Ico ((j * B : ℤ) : ℝ) (((j + 1) * B : ℤ) : ℝ))
    (hk : t ∈ Ico ((k * B : ℤ) : ℝ) (((k + 1) * B : ℤ) : ℝ)) : j = k := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  push_cast at hj hk
  rcases lt_trichotomy j k with h | h | h
  · have h' : j + 1 ≤ k := by omega
    have h'' : (j : ℝ) + 1 ≤ k := by exact_mod_cast h'
    nlinarith [hj.2, hk.1]
  · exact h
  · have h' : k + 1 ≤ j := by omega
    have h'' : (k : ℝ) + 1 ≤ j := by exact_mod_cast h'
    nlinarith [hk.2, hj.1]

theorem integral_one_bin {B : ℤ} (hB : 0 < B) (j : ℤ) :
    (∫ _t : ℝ in Ico ((j * B : ℤ) : ℝ) (((j + 1) * B : ℤ) : ℝ), (1 : ℝ)) =
      (B : ℝ) := by
  rw [setIntegral_const, Real.volume_real_Ico]
  have he : (((j + 1) * B : ℤ) : ℝ) - ((j * B : ℤ) : ℝ) = (B : ℝ) := by
    push_cast
    ring
  rw [he, max_eq_left (show (0 : ℝ) ≤ B by exact_mod_cast hB.le)]
  simp

theorem jitterMean_excess_le_bin_integral {M H : ℕ} (hH : 0 < H)
    (Z : Fin M → ℤ) {B : ℤ} (hB : 0 < B) (j : ℤ) :
    max 0 (jitterMean H Z B j - (B : ℝ)) ≤
      ∫ t in Ico ((j * B : ℤ) : ℝ) (((j + 1) * B : ℤ) : ℝ),
        max 0 (intensity H Z t - 1) := by
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Ico ((j * B : ℤ) : ℝ) (((j + 1) * B : ℤ) : ℝ)) :=
    integrableOn_const (by simp)
  apply max_le
  · exact integral_nonneg fun t => le_max_left _ _
  · rw [jitterMean_eq_integral hH Z hB j, ← integral_one_bin hB j,
      ← integral_sub (integrable_intensity H Z).integrableOn hc]
    exact integral_mono ((integrable_intensity H Z).integrableOn.sub hc)
      (integrable_intensity_excess hH Z).integrableOn (fun t => le_max_right _ _)

/-- Expected overflow over any finite family of bins is bounded by the global
Lebesgue excess of the actual intensity. -/
theorem sum_jitterMean_excess_le_integral {M H : ℕ} (hH : 0 < H)
    (Z : Fin M → ℤ) {B : ℤ} (hB : 0 < B) (J : Finset ℤ) :
    ∑ j ∈ J, max 0 (jitterMean H Z B j - (B : ℝ)) ≤
      ∫ t, max 0 (intensity H Z t - 1) := by
  let f : ℝ → ℝ := fun t => max 0 (intensity H Z t - 1)
  have hf : Integrable f := integrable_intensity_excess hH Z
  have hnonneg : ∀ t, 0 ≤ f t := fun t => le_max_left _ _
  let g : ℤ → ℝ → ℝ := fun j =>
    (Ico ((j * B : ℤ) : ℝ) (((j + 1) * B : ℤ) : ℝ)).indicator f
  have hg : ∀ j, Integrable (g j) := fun j => hf.indicator measurableSet_Ico
  have hsum : ∀ t, ∑ j ∈ J, g j t ≤ f t := by
    intro t
    by_cases ht : ∃ k ∈ J,
        t ∈ Ico ((k * B : ℤ) : ℝ) (((k + 1) * B : ℤ) : ℝ)
    · obtain ⟨k, hk, hkt⟩ := ht
      rw [Finset.sum_eq_single k]
      · change
          (Ico ((k * B : ℤ) : ℝ) (((k + 1) * B : ℤ) : ℝ)).indicator f t ≤ f t
        rw [Set.indicator_of_mem hkt]
      · intro j hj hjk
        have hnot : t ∉ Ico ((j * B : ℤ) : ℝ) (((j + 1) * B : ℤ) : ℝ) :=
          fun hjt => hjk (intensity_bin_unique hB hjt hkt)
        exact Set.indicator_of_notMem hnot f
      · exact fun hnot => (hnot hk).elim
    · have hz : ∀ j ∈ J, g j t = 0 := by
        intro j hj
        have hnot : t ∉ Ico ((j * B : ℤ) : ℝ) (((j + 1) * B : ℤ) : ℝ) :=
          fun hjt => ht ⟨j, hj, hjt⟩
        exact Set.indicator_of_notMem hnot f
      rw [Finset.sum_eq_zero hz]
      exact hnonneg t
  calc
    _ ≤ ∑ j ∈ J, ∫ t in Ico ((j * B : ℤ) : ℝ) (((j + 1) * B : ℤ) : ℝ), f t :=
      Finset.sum_le_sum fun j _ => jitterMean_excess_le_bin_integral hH Z hB j
    _ = ∑ j ∈ J, ∫ t, g j t := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (integral_indicator (μ := volume) (f := f)
        (s := Ico ((j * B : ℤ) : ℝ) (((j + 1) * B : ℤ) : ℝ))
        measurableSet_Ico).symm
    _ = ∫ t, ∑ j ∈ J, g j t :=
      (integral_finsetSum J (fun j _ => hg j)).symm
    _ ≤ _ := integral_mono (integrable_finsetSum J (fun j _ => hg j)) hf hsum

end DistanceCounts.CountIntensity
end

/-! Pointwise excess bounds for actual finite families of translated projection laws. -/

noncomputable section

namespace DistanceCounts.AggregateDensity

open Set MeasureTheory
open ProjectionDensity EmpiricalEnergy EmpiricalPairKernel
open scoped BigOperators

/-- The actual parameter rectangle; allowing its boundary only strengthens the estimates. -/
def rectangle (δ : ℝ) : Set (ℝ × ℝ) := Icc 0 δ ×ˢ Icc 0 1

variable {J : Type*} [Fintype J]

/-- Only the designated witness blocks are summed; no operation on other points is involved. -/
def aggregate {L : ℕ} (D : J → ℤ) (h : ℝ) (w : J → GridPairs.Grid L → ℝ)
    (t : ℝ) : ℝ := ∑ j, smoothed (w j) h (t - (D j : ℝ))

def reference (D : J → ℤ) (δ : ℝ) (a : ℝ × ℝ) (t : ℝ) : ℝ :=
  ∑ j, density (1 - δ + a.1) (1 + a.2) (t - (D j : ℝ))

lemma parameter_bounds {δ : ℝ} (hδ1 : δ < 1) {a : ℝ × ℝ}
    (ha : a ∈ rectangle δ) :
    0 < 1 - δ + a.1 ∧ 1 - δ + a.1 ≤ 1 ∧ 0 < 1 + a.2 ∧ 1 + a.2 ≤ 2 := by
  rcases ha with ⟨⟨ha0, haδ⟩, ⟨hb0, hb1⟩⟩
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith


lemma integrable_reference (D : J → ℤ) (δ : ℝ) (a : ℝ × ℝ) :
    Integrable (reference D δ a) :=
  integrable_finsetSum _ fun j _ => (integrable_density _ _).comp_sub_right _

lemma reference_nonneg (D : J → ℤ) {δ : ℝ} (hδ1 : δ < 1) {a : ℝ × ℝ}
    (ha : a ∈ rectangle δ) (t : ℝ) : 0 ≤ reference D δ a t := by
  have hb := parameter_bounds hδ1 ha
  exact Finset.sum_nonneg fun j _ => density_nonneg hb.1 hb.2.2.1 _

lemma reference_le (D : J → ℤ) (hD : Function.Injective D) {δ : ℝ}
    (hδ1 : δ < 1) {a : ℝ × ℝ} (ha : a ∈ rectangle δ) (t : ℝ) :
    reference D δ a t ≤ 1 / (1 - δ + a.1) := by
  classical
  have hb := parameter_bounds hδ1 ha
  have hs := sum_density_integer_le hb.1 hb.2.1 hb.2.2.1
    (Finset.univ.image D) t
  rw [Finset.sum_image (fun i _ j _ hij => hD hij)] at hs
  exact hs

lemma reference_le_delta (D : J → ℤ) (hD : Function.Injective D) {δ : ℝ}
    (hδ1 : δ < 1) {a : ℝ × ℝ} (ha : a ∈ rectangle δ) (t : ℝ) :
    reference D δ a t ≤ 1 / (1 - δ) := by
  exact (reference_le D hD hδ1 ha t).trans
    (one_div_le_one_div_of_le (by linarith) (by linarith [ha.1.1]))

lemma integral_reference (D : J → ℤ) {δ : ℝ} (hδ1 : δ < 1)
    {a : ℝ × ℝ} (ha : a ∈ rectangle δ) :
    (∫ t, reference D δ a t) = (Fintype.card J : ℝ) := by
  have hb := parameter_bounds hδ1 ha
  change (∫ t, ∑ j, density (1 - δ + a.1) (1 + a.2) (t - (D j : ℝ))) = _
  rw [integral_finsetSum _ (fun j _ =>
    (integrable_density _ _).comp_sub_right (D j : ℝ))]
  simp_rw [integral_sub_right_eq_self, integral_density hb.1 hb.2.2.1]
  simp

/-- Positive excess is integrable without integrating the constant one over the line. -/
lemma integrable_excess {f : ℝ → ℝ} (hf : Integrable f) (hf0 : ∀ t, 0 ≤ f t) :
    Integrable (fun t => max 0 (f t - 1)) := by
  apply hf.mono'
  · exact (aemeasurable_const.max
      (hf.aestronglyMeasurable.aemeasurable.sub aemeasurable_const)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
      exact max_le (hf0 t) (by linarith)

lemma integral_reference_excess_le (D : J → ℤ) (hD : Function.Injective D)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {a : ℝ × ℝ}
    (ha : a ∈ rectangle δ) :
    (∫ t, max 0 (reference D δ a t - 1)) ≤ δ * (Fintype.card J : ℝ) := by
  calc
    _ ≤ ∫ t, δ * reference D δ a t := by
      apply integral_mono
        (integrable_excess (integrable_reference D δ a) (reference_nonneg D hδ1 ha))
        ((integrable_reference D δ a).const_mul δ)
      intro t
      have hbound := (le_div_iff₀ (show 0 < 1 - δ by linarith)).mp
        (reference_le_delta D hD hδ1 ha t)
      exact max_le (mul_nonneg hδ.le (reference_nonneg D hδ1 ha t)) (by nlinarith)
    _ = _ := by rw [integral_const_mul, integral_reference D hδ1 ha]

lemma center_mem {L : ℕ} (hL : 0 < L) {δ : ℝ} (hδ1 : δ < 1)
    {a : ℝ × ℝ} (ha : a ∈ rectangle δ) {η : GridPairs.Grid L → ℝ}
    (hη : ∀ p, |η p| ≤ 1) (p : GridPairs.Grid L) :
    center L δ η a p ∈ Icc (-1 : ℝ) 4 := by
  have hb := parameter_bounds hδ1 ha
  have hp := GridQuadrature.sample_mem hL p
  have hp1 : 0 ≤ (GridQuadrature.sample L p).1 ∧ (GridQuadrature.sample L p).1 ≤ 1 := hp.1
  have hp2 : 0 ≤ (GridQuadrature.sample L p).2 ∧ (GridQuadrature.sample L p).2 ≤ 1 := hp.2
  have he := abs_le.mp (hη p)
  have hu := mul_nonneg hb.1.le hp1.1
  have hv := mul_nonneg hb.2.2.1.le hp2.1
  have hu1 := mul_le_mul hb.2.1 hp1.2 hp1.1 (by norm_num : (0 : ℝ) ≤ 1)
  have hv1 := mul_le_mul hb.2.2.2 hp2.2 hp2.1 (by norm_num : (0 : ℝ) ≤ 2)
  dsimp [EmpiricalPairKernel.center, ParameterKernel.projection]
  constructor <;> nlinarith

lemma difference_eq_zero_of_notMem {L : ℕ} (hL : 0 < L) {δ h : ℝ}
    (hδ1 : δ < 1) (hh1 : h ≤ 1) {a : ℝ × ℝ} (ha : a ∈ rectangle δ)
    {η : GridPairs.Grid L → ℝ} (hη : ∀ p, |η p| ≤ 1)
    {t : ℝ} (ht : t ∉ Icc (-1 : ℝ) 5) :
    smoothed (center L δ η a) h t - density (1 - δ + a.1) (1 + a.2) t = 0 := by
  have hz : smoothed (center L δ η a) h t = 0 := by
    unfold smoothed
    have hz : ∀ p : GridPairs.Grid L, box h (t - center L δ η a p) = 0 := by
      intro p
      have hc := center_mem hL hδ1 ha hη p
      have hn : t - center L δ η a p ∉ Ico 0 h := by
        intro hm
        apply ht
        constructor <;> linarith [hc.1, hc.2, hm.1, hm.2]
      exact indicator_of_notMem hn _
    simp [hz]
  have hb := parameter_bounds hδ1 ha
  have hd : density (1 - δ + a.1) (1 + a.2) t = 0 := by
    apply density_eq_zero_of_notMem
    intro hm
    apply ht
    constructor <;> linarith [hm.1, hm.2, hb.2.1, hb.2.2.2]
  rw [hz, hd, sub_self]

lemma integrable_difference_sq {L : ℕ} {δ h : ℝ} (hδ1 : δ < 1)
    {a : ℝ × ℝ} (ha : a ∈ rectangle δ) (η : GridPairs.Grid L → ℝ) :
    Integrable (fun t => (smoothed (center L δ η a) h t -
      density (1 - δ + a.1) (1 + a.2) t)^2) := by
  have hb := parameter_bounds hδ1 ha
  apply (((integrable_smoothed_sq (center L δ η a) h).add
    (ContinuumEnergy.integrable_density_sq hb.1 hb.2.2.1)).const_mul 2).mono'
  · exact (((integrable_smoothed _ _).aestronglyMeasurable.sub
      (integrable_density _ _).aestronglyMeasurable).pow 2)
  · exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      change (smoothed (center L δ η a) h t -
        density (1 - δ + a.1) (1 + a.2) t)^2 ≤
        2 * ((smoothed (center L δ η a) h t)^2 +
          (density (1 - δ + a.1) (1 + a.2) t)^2)
      nlinarith [sq_nonneg (smoothed (center L δ η a) h t +
        density (1 - δ + a.1) (1 + a.2) t)]

/-- Cauchy--Schwarz on the actual support interval, proved with genuine integrable terms. -/
lemma integral_abs_sq_le_six {f : ℝ → ℝ} (hf : Integrable f)
    (hf2 : Integrable (fun t => f t ^ 2))
    (hs : ∀ t, t ∉ Icc (-1 : ℝ) 5 → f t = 0) :
    (∫ t, |f t|)^2 ≤ 6 * ∫ t, f t ^ 2 := by
  let A : ℝ := ∫ t, |f t|
  have hA : (∫ t in Icc (-1 : ℝ) 5, |f t|) = A :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by simp [hs t ht]
  have hE : (∫ t in Icc (-1 : ℝ) 5, f t ^ 2) = ∫ t, f t ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by simp [hs t ht]
  have hc : IntegrableOn (fun _ : ℝ => (A / 6)^2) (Icc (-1 : ℝ) 5) :=
    integrableOn_const (by simp)
  have hsub : IntegrableOn (fun t => f t ^ 2 - (2 * (A / 6)) * |f t|)
      (Icc (-1 : ℝ) 5) :=
    hf2.integrableOn.sub (hf.abs.integrableOn.const_mul _)
  have hi : (0 : ℝ) ≤ ∫ t in Icc (-1 : ℝ) 5, (|f t| - A / 6)^2 :=
    integral_nonneg (fun t : ℝ => sq_nonneg (|f t| - A / 6))
  have he : (fun t => (|f t| - A / 6)^2) =
      (fun t => f t ^ 2 - (2 * (A / 6)) * |f t| + (A / 6)^2) := by
    funext t
    nlinarith [sq_abs (f t)]
  rw [he, integral_add hsub hc,
    integral_sub hf2.integrableOn (hf.abs.integrableOn.const_mul _),
    integral_const_mul, hA, hE, setIntegral_const] at hi
  norm_num [Real.volume_real_Icc, smul_eq_mul] at hi
  dsimp [A] at hi ⊢
  nlinarith

lemma integral_difference_abs_le {L : ℕ} (hL : 0 < L) {δ h : ℝ}
    (hδ1 : δ < 1) (hh1 : h ≤ 1) {a : ℝ × ℝ} (ha : a ∈ rectangle δ)
    {η : GridPairs.Grid L → ℝ} (hη : ∀ p, |η p| ≤ 1) :
    (∫ t, |smoothed (center L δ η a) h t - density (1 - δ + a.1) (1 + a.2) t|) ≤
      Real.sqrt (6 * MesoscopicProjection.squareError L δ h η a) := by
  apply Real.le_sqrt_of_sq_le
  exact integral_abs_sq_le_six
    ((integrable_smoothed _ _).sub (integrable_density _ _))
    (integrable_difference_sq hδ1 ha η)
    (fun _ ht => difference_eq_zero_of_notMem hL hδ1 hh1 ha hη ht)

/-- Summing translated errors costs their L¹ sum, without any disjointness assumption. -/
lemma integral_excess_compare {f g : J → ℝ → ℝ}
    (hf : ∀ j, Integrable (f j)) (hg : ∀ j, Integrable (g j))
    (hf0 : ∀ j t, 0 ≤ f j t) (hg0 : ∀ j t, 0 ≤ g j t) :
    (∫ t, max 0 ((∑ j, f j t) - 1)) ≤
      (∫ t, max 0 ((∑ j, g j t) - 1)) + ∑ j, ∫ t, |f j t - g j t| := by
  have hfi := integrable_finsetSum Finset.univ (fun j _ => hf j)
  have hgi := integrable_finsetSum Finset.univ (fun j _ => hg j)
  have hge := integrable_excess hgi (fun t => Finset.sum_nonneg fun j _ => hg0 j t)
  have hdiff : Integrable (fun t : ℝ => ∑ j, |f j t - g j t|) :=
    integrable_finsetSum Finset.univ (fun j _ => ((hf j).sub (hg j)).abs)
  calc
    _ ≤ ∫ t, max 0 ((∑ j, g j t) - 1) + ∑ j, |f j t - g j t| := by
      apply integral_mono
        (integrable_excess hfi (fun t => Finset.sum_nonneg fun j _ => hf0 j t))
        (hge.add hdiff)
      intro t
      change max 0 ((∑ j, f j t) - 1) ≤
        max 0 ((∑ j, g j t) - 1) + ∑ j, |f j t - g j t|
      apply max_le
      · exact add_nonneg (le_max_left _ _) (Finset.sum_nonneg fun j _ => abs_nonneg _)
      · have hs : (∑ j, f j t) - ∑ j, g j t ≤ ∑ j, |f j t - g j t| := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_le_sum fun j _ => le_abs_self _
        linarith [le_max_right (0 : ℝ) ((∑ j, g j t) - 1)]
    _ = _ := by
      calc
        _ = (∫ t, max 0 ((∑ j, g j t) - 1)) +
            ∫ t, ∑ j, |f j t - g j t| := integral_add hge hdiff
        _ = _ := congrArg ((∫ t, max 0 ((∑ j, g j t) - 1)) + ·)
          (integral_finsetSum Finset.univ (fun j _ => ((hf j).sub (hg j)).abs))

lemma sum_sqrt_le (E : J → ℝ) (hE : ∀ j, 0 ≤ E j) :
    (∑ j, Real.sqrt (6 * E j)) ≤ Real.sqrt (6 * (Fintype.card J : ℝ) * ∑ j, E j) := by
  apply Real.le_sqrt_of_sq_le
  have hsqrt (j : J) : Real.sqrt (6 * E j) ^ 2 = 6 * E j :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (hE j))
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : J => (1 : ℝ)) (fun j => Real.sqrt (6 * E j))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, hsqrt] at hc
  simp_rw [← Finset.mul_sum] at hc
  nlinarith [hc]

/-- The finite-block intensity bound used before selecting common parameters. -/
theorem integral_aggregate_excess_le {L : ℕ} (hL : 0 < L)
    (D : J → ℤ) (hD : Function.Injective D) {δ h : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (η : J → GridPairs.Grid L → ℝ) (hη : ∀ j p, |η j p| ≤ 1)
    {a : ℝ × ℝ} (ha : a ∈ rectangle δ) :
    (∫ t, max 0 (aggregate D h (fun j => center L δ (η j) a) t - 1)) ≤
      δ * (Fintype.card J : ℝ) +
        Real.sqrt (6 * (Fintype.card J : ℝ) *
          ∑ j, MesoscopicProjection.squareError L δ h (η j) a) := by
  have hb := parameter_bounds hδ1 ha
  have hc := integral_excess_compare
    (f := fun j t => smoothed (center L δ (η j) a) h (t - (D j : ℝ)))
    (g := fun j t => density (1 - δ + a.1) (1 + a.2) (t - (D j : ℝ)))
    (fun j => (integrable_smoothed _ _).comp_sub_right _)
    (fun j => (integrable_density _ _).comp_sub_right _)
    (fun j t => smoothed_nonneg _ hh _) (fun j t => density_nonneg hb.1 hb.2.2.1 _)
  change (∫ t, max 0 (aggregate D h (fun j => center L δ (η j) a) t - 1)) ≤
    (∫ t, max 0 (reference D δ a t - 1)) + _ at hc
  refine hc.trans (add_le_add (integral_reference_excess_le D hD hδ hδ1 ha) ?_)
  calc
    _ ≤ ∑ j, Real.sqrt (6 * MesoscopicProjection.squareError L δ h (η j) a) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [integral_sub_right_eq_self (fun t =>
        |smoothed (center L δ (η j) a) h t - density (1 - δ + a.1) (1 + a.2) t|)]
      exact integral_difference_abs_le hL hδ1 hh1 ha (hη j)
    _ ≤ _ := sum_sqrt_le _ (fun j => MesoscopicProjection.squareError_nonneg _ _ _ _ _)

/-- The final floor correction is pointwise in the parameter and can depend on it arbitrarily. -/
theorem integral_aggregate_excess_le_stable {L : ℕ} (hL : 0 < L)
    (D : J → ℤ) (hD : Function.Injective D) {δ h ν : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (η : J → GridPairs.Grid L → ℝ) (hη : ∀ j p, |η j p| ≤ 1)
    {a : ℝ × ℝ} (ha : a ∈ rectangle δ)
    (w : J → GridPairs.Grid L → ℝ) (hw : ∀ j p, |w j p - center L δ (η j) a p| ≤ ν) :
    (∫ t, max 0 (aggregate D h w t - 1)) ≤
      δ * (Fintype.card J : ℝ) +
        Real.sqrt (6 * (Fintype.card J : ℝ) *
          ∑ j, MesoscopicProjection.squareError L δ h (η j) a) +
        2 * (Fintype.card J : ℝ) * ν / h := by
  letI : Nonempty (GridPairs.Grid L) := ⟨(⟨0, hL⟩, ⟨0, hL⟩)⟩
  have hc := integral_excess_compare
    (f := fun j t => smoothed (w j) h (t - (D j : ℝ)))
    (g := fun j t => smoothed (center L δ (η j) a) h (t - (D j : ℝ)))
    (fun j => (integrable_smoothed _ _).comp_sub_right _)
    (fun j => (integrable_smoothed _ _).comp_sub_right _)
    (fun j t => smoothed_nonneg _ hh _) (fun j t => smoothed_nonneg _ hh _)
  refine hc.trans (add_le_add (integral_aggregate_excess_le hL D hD hδ hδ1 hh hh1 η hη ha) ?_)
  calc
    _ ≤ ∑ _j : J, 2 * ν / h := by
      apply Finset.sum_le_sum
      intro j hj
      rw [integral_sub_right_eq_self (fun t =>
        |smoothed (w j) h t - smoothed (center L δ (η j) a) h t|)]
      exact integral_smoothed_sub_abs_le _ _ hh (hw j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end DistanceCounts.AggregateDensity
end

/-! Exact scaling from integer-jitter unit cells to the normalized empirical densities. -/

noncomputable section

namespace DistanceCounts.ProjectionScaling

open Set MeasureTheory ProjectionDensity EmpiricalEnergy
open scoped Classical

variable {J I : Type*} [Fintype J] [Fintype I]

theorem box_scaled {m : ℝ} (hm : 0 < m) (h x : ℝ) :
    box (m * h) (m * x) = m⁻¹ * box h x := by
  have h0 : 0 ≤ m * x ↔ 0 ≤ x := by
    simpa only [mul_zero] using (mul_le_mul_iff_right₀ hm (b := 0) (c := x))
  have hi : m * x ∈ Ico 0 (m * h) ↔ x ∈ Ico 0 h :=
    and_congr h0 (mul_lt_mul_iff_right₀ hm)
  by_cases hx : x ∈ Ico 0 h
  · simp only [box, Set.indicator_of_mem (hi.mpr hx), Set.indicator_of_mem hx,
      one_div, mul_inv_rev]
    ring
  · have hn : m * x ∉ Ico 0 (m * h) := fun hh => hx (hi.mp hh)
    simp only [box, Set.indicator_of_notMem hn, Set.indicator_of_notMem hx, mul_zero]

theorem box_rescale {m : ℝ} (hm : 0 < m) (H t c : ℝ) :
    box H (t - c) = m⁻¹ * box (H / m) (t / m - c / m) := by
  have h := box_scaled hm (H / m) ((t - c) / m)
  have hH : m * (H / m) = H := by field_simp [hm.ne']
  have hx : m * ((t - c) / m) = t - c := by field_simp [hm.ne']
  rw [hH, hx, sub_div] at h
  exact h

/-- The exact raw intensity of all integer outputs in the chosen groups. -/
def groupIntensity (H : ℕ) (Z : J → I → ℤ) (t : ℝ) : ℝ :=
  ∑ j, ∑ i, box (H : ℝ) (t - ((Z j i - (H : ℤ) + 1 : ℤ) : ℝ))

def normalizedCenter (H : ℕ) (Z : J → I → ℤ) (j : J) (i : I) : ℝ :=
  ((Z j i - (H : ℤ) + 1 : ℤ) : ℝ) / (Fintype.card I : ℝ)

theorem groupIntensity_eq [Nonempty I] (H : ℕ) (Z : J → I → ℤ) (t : ℝ) :
    groupIntensity H Z t = ∑ j,
      smoothed (normalizedCenter H Z j) ((H : ℝ) / Fintype.card I)
        (t / (Fintype.card I : ℝ)) := by
  have hm : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  unfold groupIntensity smoothed normalizedCenter
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact box_rescale hm _ _ _


theorem intensity_eq_groupIntensity {M H : ℕ} (e : Fin M ≃ J × I) (Y : Fin M → ℤ)
    (t : ℝ) : CountIntensity.intensity H Y t =
      groupIntensity H (fun j i => Y (e.symm (j, i))) t := by
  unfold CountIntensity.intensity groupIntensity
  calc
    _ = ∑ p : J × I, box (H : ℝ) (t - ((Y (e.symm p) - (H : ℤ) + 1 : ℤ) : ℝ)) :=
      Fintype.sum_equiv e _ _ (fun i => by simp only [e.symm_apply_apply])
    _ = _ := Fintype.sum_prod_type _

theorem integral_groupIntensity_excess [Nonempty I] (H : ℕ) (Z : J → I → ℤ) :
    (∫ t, max 0 (groupIntensity H Z t - 1)) = (Fintype.card I : ℝ) *
      ∫ t, max 0 ((∑ j, smoothed (normalizedCenter H Z j)
        ((H : ℝ) / Fintype.card I) t) - 1) := by
  simp_rw [groupIntensity_eq H Z]
  have h := Measure.integral_comp_div
    (fun t : ℝ => max 0 ((∑ j, smoothed (normalizedCenter H Z j)
      ((H : ℝ) / Fintype.card I) t) - 1)) (Fintype.card I : ℝ)
  simpa only [abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card I by positivity),
    smul_eq_mul] using h

theorem smoothed_shift (z : I → ℝ) (h c t : ℝ) :
    smoothed z h t = smoothed (fun i => z i - c) h (t - c) := by
  unfold smoothed
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

theorem integral_groupIntensity_excess_degrees {L H : ℕ}
    [Nonempty (GridPairs.Grid L)] (D : J → ℤ) (Z : J → GridPairs.Grid L → ℤ) :
    (∫ t, max 0 (groupIntensity H Z t - 1)) = ((L : ℝ) ^ 2) *
      ∫ t, max 0 (AggregateDensity.aggregate D ((H : ℝ) / (L : ℝ) ^ 2)
        (fun j i => normalizedCenter H Z j i - (D j : ℝ)) t - 1) := by
  rw [integral_groupIntensity_excess H Z]
  simp only [GridPairs.Grid, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  simp only [← pow_two]
  change (L : ℝ) ^ 2 * _ = (L : ℝ) ^ 2 * _
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro t
  have hs : (∑ j, smoothed (normalizedCenter H Z j)
      ((H : ℝ) / (L : ℝ) ^ 2) t) =
      AggregateDensity.aggregate D ((H : ℝ) / (L : ℝ) ^ 2)
        (fun j i => normalizedCenter H Z j i - (D j : ℝ)) t := by
    unfold AggregateDensity.aggregate
    apply Finset.sum_congr rfl
    intro j _
    exact smoothed_shift _ _ _ _
  exact congrArg (fun x : ℝ => max 0 (x - 1)) hs

/-- Normalization keeps the integer unit-cell shift and the common degree exactly. -/
theorem normalized_error {L : ℕ} (hL : 0 < L) (Z : ℤ) (D e α β H E : ℝ)
    (x y : Fin L)
    (he : |(Z : ℝ) - (D * (L : ℝ) ^ 2 + e + α * L * x + β * L * y)| ≤ E) :
    |((Z : ℝ) - H + 1) / (L : ℝ) ^ 2 - D -
      (α * ((x : ℝ) / L) + β * ((y : ℝ) / L) +
        (e / (L : ℝ) ^ 2 - H / (L : ℝ) ^ 2 + 1 / (L : ℝ) ^ 2))| ≤
      E / (L : ℝ) ^ 2 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hid : ((Z : ℝ) - H + 1) / (L : ℝ) ^ 2 - D -
      (α * ((x : ℝ) / L) + β * ((y : ℝ) / L) +
        (e / (L : ℝ) ^ 2 - H / (L : ℝ) ^ 2 + 1 / (L : ℝ) ^ 2)) =
      ((Z : ℝ) - (D * (L : ℝ) ^ 2 + e + α * L * x + β * L * y)) / (L : ℝ) ^ 2 := by
    field_simp [hLr.ne']
    <;> ring
  rw [hid, abs_div, abs_of_nonneg (sq_nonneg (L : ℝ))]
  exact div_le_div_of_nonneg_right he (sq_nonneg (L : ℝ))

end DistanceCounts.ProjectionScaling
end

/-! Selection of actual finite group jitters by the second-moment method. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace DistanceCounts.JitterSelection

/-- The coordinates of the finite product of uniform jitter laws are independent,
including after conversion to integer shifts. -/
theorem uniform_group_independent {G : Type*} [Fintype G] {H : ℕ}
    [Nonempty (Fin H)] [MeasurableSpace (Fin H)] [MeasurableSingletonClass (Fin H)] :
    iIndepFun (fun a (q : G → Fin H) => ((q a).val : ℤ))
      (Measure.pi (fun _ : G => (PMF.uniformOfFintype (Fin H)).toMeasure)) := by
  exact iIndepFun_pi (fun _ =>
    (measurable_of_countable (fun r : Fin H => (r.val : ℤ))).aemeasurable)

/-- The occupancy mean under the actual finite product law is the discrete
jitter mean, not a continuous-uniform approximation. -/
theorem uniform_occupancy_mean {M : ℕ} {G : Type*} [Fintype G] {H : ℕ}
    [Nonempty (Fin H)] [MeasurableSpace (Fin H)] [MeasurableSingletonClass (Fin H)]
    (Z : Fin M → ℤ) (g : Fin M → G) (B j : ℤ) :
    (∫ q : G → Fin H,
      JitterVariance.occupancy
        (JitterVariance.jitterBin Z g (fun a q => ((q a).val : ℤ)) B) j q
      ∂Measure.pi (fun _ : G => (PMF.uniformOfFintype (Fin H)).toMeasure)) =
      CountIntensity.jitterMean H Z B j := by
  classical
  let ν : Measure (Fin H) := (PMF.uniformOfFintype (Fin H)).toMeasure
  let μ : Measure (G → Fin H) := Measure.pi (fun _ : G => ν)
  have hpin (i : Fin M) :
      (∫ q : G → Fin H,
        JitterVariance.binIndicator
          (JitterVariance.jitterBin Z g (fun a q => ((q a).val : ℤ)) B i) j q ∂μ) =
        (H : ℝ)⁻¹ *
          ((Finset.univ.filter (fun r : Fin H => (Z i - (r.val : ℤ)) / B = j)).card : ℝ) := by
    let f : Fin H → ℝ := fun r => if (Z i - (r.val : ℤ)) / B = j then 1 else 0
    change (∫ q : G → Fin H, f (q (g i)) ∂μ) = _
    have hmap := (measurePreserving_eval (fun _ : G => ν) (g i)).map_eq
    calc
      (∫ q : G → Fin H, f (q (g i)) ∂μ) =
          ∫ r, f r ∂Measure.map (Function.eval (g i)) μ :=
        (integral_map (measurable_pi_apply (g i)).aemeasurable
          (measurable_of_countable f).aestronglyMeasurable).symm
      _ = ∫ r, f r ∂ν := by rw [hmap]
      _ = (H : ℝ)⁻¹ *
          ((Finset.univ.filter (fun r : Fin H => (Z i - (r.val : ℤ)) / B = j)).card : ℝ) := by
        simp only [ν, PMF.integral_eq_sum, PMF.uniformOfFintype_apply,
          Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast,
          smul_eq_mul, ← Finset.mul_sum]
        congr 1
        simp [f, Finset.sum_boole]
  change (∫ q, ∑ i : Fin M,
    JitterVariance.binIndicator
      (JitterVariance.jitterBin Z g (fun a q => ((q a).val : ℤ)) B i) j q ∂μ) = _
  rw [integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
  simp_rw [hpin]
  exact (Finset.mul_sum Finset.univ _ _).symm

/-- Positive-part Lipschitz control and finite Cauchy--Schwarz turn one
simultaneous squared-error bound into an overflow bound. -/
theorem overflow_le_of_sq_error {ι : Type*} (J : Finset ι)
    (x m : ι → ℝ) (b V : ℝ) (hV : (∑ j ∈ J, (x j - m j) ^ 2) ≤ V) :
    (∑ j ∈ J, max 0 (x j - b)) ≤
      (∑ j ∈ J, max 0 (m j - b)) + Real.sqrt ((J.card : ℝ) * V) := by
  have hpos (j : ι) : max 0 (x j - b) ≤ max 0 (m j - b) + |x j - m j| := by
    apply max_le
    · exact add_nonneg (le_max_left _ _) (abs_nonneg _)
    · have hm := le_max_right (0 : ℝ) (m j - b)
      have hx := le_abs_self (x j - m j)
      linarith
  have hcs : (∑ j ∈ J, |x j - m j|) ^ 2 ≤
      (J.card : ℝ) * ∑ j ∈ J, (x j - m j) ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs]
      using Finset.sum_mul_sq_le_sq_mul_sq J (fun _ => (1 : ℝ))
        (fun j => |x j - m j|)
  have herr : (∑ j ∈ J, |x j - m j|) ≤ Real.sqrt ((J.card : ℝ) * V) :=
    Real.le_sqrt_of_sq_le (hcs.trans (mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg _)))
  calc
    (∑ j ∈ J, max 0 (x j - b)) ≤
        ∑ j ∈ J, (max 0 (m j - b) + |x j - m j|) :=
      Finset.sum_le_sum fun j _ => hpos j
    _ = (∑ j ∈ J, max 0 (m j - b)) + ∑ j ∈ J, |x j - m j| :=
      Finset.sum_add_distrib
    _ ≤ _ := by linarith

/-- An actual choice of one integer jitter per group achieves the overflow
bound. The sample space is the finite function space `G → Fin H`, endowed in
the proof with the product of uniform probability laws. No pins are discarded. -/
theorem exists_jitter_overflow {M : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
    (H : ℕ) (hH : 0 < H) (Z : Fin M → ℤ) (g : Fin M → G)
    (B : ℤ) (hB : 0 < B) (J : Finset ℤ) :
    ∃ q : G → Fin H,
      (∑ j ∈ J, max 0 ((CountIntensity.binCount
        (fun i => Z i - ((q (g i)).val : ℤ)) B j : ℝ) - (B : ℝ))) ≤
      (∑ j ∈ J, max 0 (CountIntensity.jitterMean H Z B j - (B : ℝ))) +
        Real.sqrt ((J.card : ℝ) * ((M : ℝ) +
          2 * ((Finset.univ.filter (fun p : Fin M × Fin M =>
            p.1 < p.2 ∧ g p.1 = g p.2 ∧ |Z p.1 - Z p.2| < B)).card : ℝ))) := by
  classical
  letI : Nonempty (Fin H) := ⟨⟨0, hH⟩⟩
  letI : MeasurableSpace (Fin H) := ⊤
  letI : MeasurableSingletonClass (Fin H) := ⟨fun _ => trivial⟩
  let ν : Measure (Fin H) := (PMF.uniformOfFintype (Fin H)).toMeasure
  let μ : Measure (G → Fin H) := Measure.pi (fun _ : G => ν)
  let shifts : G → (G → Fin H) → ℤ := fun a q => ((q a).val : ℤ)
  let W := JitterVariance.jitterBin Z g shifts B
  let X := JitterVariance.occupancy W
  have hshift (a : G) : Measurable (shifts a) :=
    (measurable_of_countable (fun r : Fin H => (r.val : ℤ))).comp
      (measurable_pi_apply a)
  have hind : iIndepFun shifts μ := uniform_group_independent
  have hW (i : Fin M) : Measurable (W i) :=
    (measurable_of_countable (fun z : ℤ => (Z i - z) / B)).comp (hshift (g i))
  have hmean (j : ℤ) : (∫ q, X j q ∂μ) = CountIntensity.jitterMean H Z B j :=
    uniform_occupancy_mean Z g B j
  have hvar := JitterVariance.jitter_variance_bound_unordered
    (μ := μ) Z g shifts hshift hind B hB J
  let E : (G → Fin H) → ℝ := fun q =>
    ∑ j ∈ J, (X j q - CountIntensity.jitterMean H Z B j) ^ 2
  have hE : (∫ q, E q ∂μ) = ∑ j ∈ J, variance (X j) μ := by
    rw [show (∫ q, E q ∂μ) = ∑ j ∈ J,
      ∫ q, (X j q - CountIntensity.jitterMean H Z B j) ^ 2 ∂μ from
        integral_finsetSum J (fun _ _ => Integrable.of_finite)]
    apply Finset.sum_congr rfl
    intro j _
    rw [variance_eq_integral (JitterVariance.occupancy_memLp hW j).aestronglyMeasurable.aemeasurable,
      hmean]
  obtain ⟨q, hq⟩ := exists_le_integral (μ := μ) (f := E) Integrable.of_finite
  rw [hE] at hq
  have hchoice := overflow_le_of_sq_error J (fun j => X j q)
    (CountIntensity.jitterMean H Z B) (B : ℝ) _ (hq.trans hvar)
  have hX (j : ℤ) : X j q =
      (CountIntensity.binCount (fun i => Z i - ((q (g i)).val : ℤ)) B j : ℝ) := by
    simp only [CountIntensity.binCount_cast, X, W, shifts,
      JitterVariance.occupancy, JitterVariance.binIndicator, JitterVariance.jitterBin]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hij : (Z i - ((q (g i)).val : ℤ)) / B = j <;>
      simp only [hij, ite_true, ite_false]
  refine ⟨q, ?_⟩
  simpa only [hX] using hchoice

end DistanceCounts.JitterSelection
end

/-! Finite support of actual integer bins and capacity-limited witness selection.
The ambient index set and its geometric points are never changed. -/

noncomputable section

open scoped BigOperators

namespace DistanceCounts.FiniteBinWindow

/-- A finite window of Euclidean integer quotients, including negative levels. -/
def window (lo hi B : ℤ) : Finset ℤ := Finset.Icc (lo / B) (hi / B)

/-- Euclidean remainder bounds locate every integer in its actual bin. -/
theorem ediv_bounds (y : ℤ) {B : ℤ} (hB : 0 < B) :
    y / B * B ≤ y ∧ y < (y / B + 1) * B := by
  have heq := Int.emod_add_mul_ediv y B
  have hlo := Int.emod_nonneg y hB.ne'
  have hhi := Int.emod_lt_of_pos y hB
  constructor <;> nlinarith

/-- Monotonicity here uses Euclidean division, not truncation toward zero. -/
theorem ediv_mono {x y B : ℤ} (hB : 0 < B) (hxy : x ≤ y) :
    x / B ≤ y / B := by
  have hx := ediv_bounds x hB
  have hy := ediv_bounds y hB
  by_contra h
  have hstep : y / B + 1 ≤ x / B := by omega
  have hmul := mul_le_mul_of_nonneg_right hstep hB.le
  nlinarith [hx.1, hy.2]

theorem mem_window {lo hi B y : ℤ} (hB : 0 < B)
    (hy : lo ≤ y ∧ y ≤ hi) : y / B ∈ window lo hi B := by
  exact Finset.mem_Icc.mpr ⟨ediv_mono hB hy.1, ediv_mono hB hy.2⟩

/-- At most the range length divided by the bin width, plus two endpoint bins. -/
theorem card_window_le {lo hi B : ℤ} (hlo : lo ≤ hi) (hB : 0 < B) :
    ((window lo hi B).card : ℝ) ≤ ((hi : ℝ) - (lo : ℝ)) / (B : ℝ) + 2 := by
  have hquot := ediv_mono hB hlo
  have hcard : ((window lo hi B).card : ℤ) = hi / B + 1 - lo / B :=
    Int.card_Icc_of_le _ _ (by omega)
  have hcardR : ((window lo hi B).card : ℝ) =
      ((hi / B : ℤ) : ℝ) + 1 - ((lo / B : ℤ) : ℝ) := by
    exact_mod_cast hcard
  have hloR : (lo : ℝ) < (((lo / B : ℤ) : ℝ) + 1) * (B : ℝ) := by
    exact_mod_cast (ediv_bounds lo hB).2
  have hhiR : ((hi / B : ℤ) : ℝ) * (B : ℝ) ≤ (hi : ℝ) := by
    exact_mod_cast (ediv_bounds hi hB).1
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hbound : ((window lo hi B).card : ℝ) - 2 ≤
      ((hi : ℝ) - (lo : ℝ)) / (B : ℝ) := by
    apply (le_div_iff₀ hBR).2
    nlinarith
  linarith


end DistanceCounts.FiniteBinWindow
end

/-! Actual fixed-parameter jitters and unary corrections on the unchanged ambient pins. -/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace DistanceCounts.FineFixedCorrection

/-- A deterministic window containing every possible row-jittered score. -/
def binWindow (K L B : ℕ) : Finset ℤ :=
  FiniteBinWindow.window (-3 * (L : ℤ) ^ 2) (((K : ℤ) + 5) * (L : ℤ) ^ 2) B

theorem card_binWindow_le (K L : ℕ) {B : ℕ} (hB : 0 < B) :
    ((binWindow K L B).card : ℝ) ≤
      ((K : ℝ) + 8) * (L : ℝ) ^ 2 / B + 2 := by
  have hlo : -3 * (L : ℤ) ^ 2 ≤ ((K : ℤ) + 5) * (L : ℤ) ^ 2 := by
    have hp : 0 ≤ ((K : ℤ) + 8) * (L : ℤ) ^ 2 := by positivity
    nlinarith
  have h := FiniteBinWindow.card_window_le hlo (show (0 : ℤ) < B by exact_mod_cast hB)
  change ((binWindow K L B).card : ℝ) ≤ _ at h
  convert h using 1 <;> push_cast <;> ring

/-- The good event and the actual coarse residual imply the score range. -/
theorem score_range {K L : ℕ} {δ E : ℝ}
    (D : Fin K → ℤ) (Z0 : Fin K × GridPairs.Grid L → ℤ)
    (hD : ∀ b, 0 ≤ D b ∧ D b ≤ (K : ℤ))
    (he : ∀ i, |FineData.error D Z0 i| ≤ (L : ℝ) ^ 2)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hE : 2 * E + 1 ≤ (L : ℝ) ^ 2)
    {a : ℝ × ℝ} (ha : a ∈ SkewParameters.good δ L E)
    (i : Fin K × GridPairs.Grid L) :
    -(2 * (L : ℤ) ^ 2) ≤ SkewScores.score δ Z0 i a ∧
      SkewScores.score δ Z0 i a ≤ ((K : ℤ) + 5) * (L : ℤ) ^ 2 := by
  exact SkewScores.score_range Z0 (fun b => (D b : ℝ)) (FineData.error D Z0)
    (FineData.decomposition D Z0) (fun b => by exact_mod_cast hD b)
    he hδ hδ1 hE ha i

/-- Every outcome of the full row-jitter product lies in the same finite window. -/
theorem jitter_mem_binWindow {K L H B : ℕ} {δ E : ℝ}
    (D : Fin K → ℤ) (Z0 : Fin K × GridPairs.Grid L → ℤ)
    (good : Finset (Fin K))
    (hD : ∀ b, 0 ≤ D b ∧ D b ≤ (K : ℤ))
    (he : ∀ i, |FineData.error D Z0 i| ≤ (L : ℝ) ^ 2)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hE : 2 * E + 1 ≤ (L : ℝ) ^ 2)
    (hH : H ≤ L ^ 2) (hB : 0 < B)
    {a : ℝ × ℝ} (ha : a ∈ SkewParameters.good δ L E)
    (q : Fin K × Fin L → Fin H) (i : Fin (good.card * L ^ 2)) :
    (SkewScores.score δ Z0 (FineIndex.ambient good i) a -
      ((q (FineIndex.group good i)).val : ℤ)) / (B : ℤ) ∈ binWindow K L B := by
  apply FiniteBinWindow.mem_window (by exact_mod_cast hB)
  have hz := score_range D Z0 hD he hδ hδ1 hE ha (FineIndex.ambient good i)
  have hq : ((q (FineIndex.group good i)).val : ℤ) < (H : ℤ) := by
    exact_mod_cast (q (FineIndex.group good i)).isLt
  have hq0 : (0 : ℤ) ≤ (q (FineIndex.group good i)).val := by positivity
  have hHr : (H : ℤ) ≤ (L : ℤ) ^ 2 := by exact_mod_cast hH
  constructor <;> linarith

/-- Exact intensity scaling and stability, with the square errors summed over all
original blocks. Restricting the witness family only decreases that nonnegative sum. -/
theorem integral_intensity_excess_le {K L H : ℕ} {δ E ω : ℝ}
    (hL : 0 < L) (hH : 0 < H) (hHL : H ≤ L ^ 2)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (D : Fin K → ℤ) (Z0 : Fin K × GridPairs.Grid L → ℤ)
    (good : Finset (Fin K)) (hgood : Set.InjOn D good)
    (hη : ∀ b p, |FineData.perturbation D Z0 H b p| ≤ 1)
    {a : ℝ × ℝ} (ha : a ∈ SkewParameters.good δ L E)
    (hsquare : (∑ b : Fin K, MesoscopicProjection.squareError L δ
      ((H : ℝ) / (L : ℝ) ^ 2) (FineData.perturbation D Z0 H b) a) ≤ ω) :
    (∫ t, max 0 (CountIntensity.intensity H
      (fun i : Fin (good.card * L ^ 2) =>
        SkewScores.score δ Z0 (FineIndex.ambient good i) a) t - 1)) ≤
      (L : ℝ) ^ 2 * (δ * good.card + Real.sqrt (6 * good.card * ω) +
        2 * good.card * (2 * E + 1) / H) := by
  letI : Nonempty (GridPairs.Grid L) := ⟨(⟨0, hL⟩, ⟨0, hL⟩)⟩
  let Dg : good → ℤ := fun b => D b.val
  let Zg : good → GridPairs.Grid L → ℤ := fun b p => SkewScores.score δ Z0 (b.val, p) a
  let η : good → GridPairs.Grid L → ℝ := fun b => FineData.perturbation D Z0 H b.val
  let w : good → GridPairs.Grid L → ℝ := fun b p =>
    ProjectionScaling.normalizedCenter H Zg b p - (Dg b : ℝ)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hm : (0 : ℝ) < (L : ℝ) ^ 2 := sq_pos_of_pos hLr
  have hh : 0 < (H : ℝ) / (L : ℝ) ^ 2 := div_pos hHr hm
  have hh1 : (H : ℝ) / (L : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_one hm).2
    exact_mod_cast hHL
  have hDg : Function.Injective Dg := by
    intro b c hbc
    exact Subtype.ext (hgood b.property c.property hbc)
  have hw (b : good) (p : GridPairs.Grid L) :
      |w b p - EmpiricalPairKernel.center L δ (η b) a p| ≤
        (2 * E + 1) / (L : ℝ) ^ 2 := by
    have he := SkewScores.score_error_le Z0 ha (b.val, p)
    rw [FineData.decomposition D Z0 (b.val, p)] at he
    have hn := ProjectionScaling.normalized_error hL (Zg b p) (D b.val)
      (FineData.error D Z0 (b.val, p)) (SkewParameters.alpha δ a)
      (SkewParameters.beta a) H (2 * E + 1) p.1 p.2 he
    simpa [w, ProjectionScaling.normalizedCenter, Dg, η, FineData.perturbation,
      EmpiricalPairKernel.center, ParameterKernel.projection, GridQuadrature.sample,
      SkewParameters.alpha, SkewParameters.beta, GridPairs.Grid, pow_two] using hn
  have hsub : (∑ b : good, MesoscopicProjection.squareError L δ
      ((H : ℝ) / (L : ℝ) ^ 2) (η b) a) ≤ ω := by
    change (∑ b : good, MesoscopicProjection.squareError L δ
      ((H : ℝ) / (L : ℝ) ^ 2) (FineData.perturbation D Z0 H b.val) a) ≤ ω
    rw [Finset.sum_coe_sort good (fun b : Fin K => MesoscopicProjection.squareError L δ
      ((H : ℝ) / (L : ℝ) ^ 2) (FineData.perturbation D Z0 H b) a)]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good)
      (fun b _ _ => MesoscopicProjection.squareError_nonneg _ _ _ _ _)).trans hsquare
  have hstable := AggregateDensity.integral_aggregate_excess_le_stable hL Dg hDg
    hδ hδ1 hh hh1 η (fun b p => hη b.val p) ha.1 w hw
  have hsqrt : Real.sqrt (6 * (good.card : ℝ) *
      ∑ b : good, MesoscopicProjection.squareError L δ
        ((H : ℝ) / (L : ℝ) ^ 2) (η b) a) ≤ Real.sqrt (6 * good.card * ω) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsub (by positivity))
  simp only [Fintype.card_coe] at hstable
  have hcancel : 2 * (good.card : ℝ) * ((2 * E + 1) / (L : ℝ) ^ 2) /
      ((H : ℝ) / (L : ℝ) ^ 2) = 2 * good.card * (2 * E + 1) / H := by
    field_simp [hLr.ne', hHr.ne']
    <;> ring
  rw [hcancel] at hstable
  have hbound : (∫ t, max 0 (AggregateDensity.aggregate Dg
      ((H : ℝ) / (L : ℝ) ^ 2) w t - 1)) ≤
      δ * good.card + Real.sqrt (6 * good.card * ω) +
        2 * good.card * (2 * E + 1) / H := by
    linarith
  have hid (t : ℝ) : CountIntensity.intensity H
      (fun i : Fin (good.card * L ^ 2) =>
        SkewScores.score δ Z0 (FineIndex.ambient good i) a) t =
      ProjectionScaling.groupIntensity H Zg t := by
    rw [ProjectionScaling.intensity_eq_groupIntensity (FineIndex.witnessEquiv good)]
    simp only [FineIndex.ambient, Equiv.apply_symm_apply, Zg]
  simp_rw [hid]
  rw [ProjectionScaling.integral_groupIntensity_excess_degrees Dg Zg]
  exact mul_le_mul_of_nonneg_left hbound hm.le

theorem exists_bin_bound {K L H B : ℕ} {δ E ω : ℝ}
    (hK : 0 < K) (hL : 0 < L) (hH : 0 < H) (hB : 0 < B)
    (hHL : H ≤ L ^ 2) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hE0 : 0 ≤ E) (hE : 2 * E + 1 ≤ (L : ℝ) ^ 2) (hω : 0 ≤ ω)
    (D : Fin K → ℤ) (Z0 : Fin K × GridPairs.Grid L → ℤ)
    (good : Finset (Fin K)) (hgood : Set.InjOn D good)
    (hD : ∀ b, 0 ≤ D b ∧ D b ≤ (K : ℤ))
    (he : ∀ i, |FineData.error D Z0 i| ≤ (L : ℝ) ^ 2)
    (hη : ∀ b p, |FineData.perturbation D Z0 H b p| ≤ 1)
    {a : ℝ × ℝ} (ha : a ∈ SkewParameters.good δ L E)
    (hsquare : (∑ b : Fin K, MesoscopicProjection.squareError L δ
      ((H : ℝ) / (L : ℝ) ^ 2) (FineData.perturbation D Z0 H b) a) ≤ ω)
    (hnear : RowPairAverage.count (SkewScores.score δ Z0) (B : ℤ) a /
      (L : ℝ) ^ 2 ≤ ω) :
    ∃ q : Fin K × Fin L → Fin H,
      (∀ i : Fin (good.card * L ^ 2),
        (SkewScores.score δ Z0 (FineIndex.ambient good i) a - ((q (FineIndex.group good i)).val : ℤ)) /
          (B : ℤ) ∈ binWindow K L B) ∧
      (∑ j ∈ binWindow K L B, max 0 ((CountIntensity.binCount
        (fun i => SkewScores.score δ Z0 (FineIndex.ambient good i) a -
          ((q (FineIndex.group good i)).val : ℤ)) (B : ℤ) j : ℝ) - (B : ℝ))) ≤
        (L : ℝ) ^ 2 * (δ * good.card + Real.sqrt (6 * good.card * ω) +
          2 * good.card * (2 * E + 1) / H) +
        Real.sqrt (((binWindow K L B).card : ℝ) * (good.card * (L : ℝ) ^ 2 +
          2 * ω * (L : ℝ) ^ 2)) := by
  let Z : Fin (good.card * L ^ 2) → ℤ := fun i =>
    SkewScores.score δ Z0 (FineIndex.ambient good i) a
  let g : Fin (good.card * L ^ 2) → Fin K × Fin L := FineIndex.group good
  let J := binWindow K L B
  have hBz : (0 : ℤ) < B := by exact_mod_cast hB
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hm : (0 : ℝ) < (L : ℝ) ^ 2 := sq_pos_of_pos hLr
  have hraw := integral_intensity_excess_le hL hH hHL hδ hδ1
    D Z0 good hgood hη ha hsquare
  have hmean := CountIntensity.sum_jitterMean_excess_le_integral hH Z hBz J
  have hmeanBound : (∑ j ∈ J, max 0 (CountIntensity.jitterMean H Z (B : ℤ) j -
      (B : ℝ))) ≤ (L : ℝ) ^ 2 * (δ * good.card + Real.sqrt (6 * good.card * ω) +
        2 * good.card * (2 * E + 1) / H) := hmean.trans hraw
  have hpairs := RowPairAverage.twice_reindexed_unordered_count_le
    (FineIndex.ambient good) (FineIndex.ambient_injective good)
    (SkewScores.score δ Z0) (B : ℤ) a
  have hnear' := (div_le_iff₀ hm).mp hnear
  have hvariance : ((good.card * L ^ 2 : ℕ) : ℝ) +
      2 * ((Finset.univ.filter (fun p : Fin (good.card * L ^ 2) ×
        Fin (good.card * L ^ 2) => p.1 < p.2 ∧ g p.1 = g p.2 ∧
          |Z p.1 - Z p.2| < (B : ℤ))).card : ℝ) ≤
      good.card * (L : ℝ) ^ 2 + 2 * ω * (L : ℝ) ^ 2 := by
    change 2 * ((Finset.univ.filter (fun p : Fin (good.card * L ^ 2) ×
      Fin (good.card * L ^ 2) => p.1 < p.2 ∧ g p.1 = g p.2 ∧
      |Z p.1 - Z p.2| < (B : ℤ))).card : ℝ) ≤ _ at hpairs
    push_cast
    nlinarith [mul_nonneg hω hm.le]
  obtain ⟨q, hq⟩ := JitterSelection.exists_jitter_overflow H hH Z g (B : ℤ) hBz J
  have hsqrt := Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left hvariance (show (0 : ℝ) ≤ J.card by positivity))
  have hoverflow : (∑ j ∈ J, max 0 ((CountIntensity.binCount
      (fun i => Z i - ((q (g i)).val : ℤ)) (B : ℤ) j : ℝ) - (B : ℝ))) ≤
      (L : ℝ) ^ 2 * (δ * good.card + Real.sqrt (6 * good.card * ω) +
        2 * good.card * (2 * E + 1) / H) +
      Real.sqrt ((J.card : ℝ) * (good.card * (L : ℝ) ^ 2 +
        2 * ω * (L : ℝ) ^ 2)) := hq.trans (add_le_add hmeanBound hsqrt)
  have hsupport (i : Fin (good.card * L ^ 2)) :
      (Z i - ((q (g i)).val : ℤ)) / (B : ℤ) ∈ J :=
    jitter_mem_binWindow D Z0 good hD he hδ hδ1 hE hHL hB ha q i
  exact ⟨q, hsupport, hoverflow⟩
end DistanceCounts.FineFixedCorrection
end

noncomputable section
open Filter Finset MeasureTheory
open scoped Topology
namespace DistanceCounts.FixedWidth
open ConstructionScales

/-- Choose one width uniformly over the subsets of the K blocks. -/
private theorem choose_width (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ W : ℕ, 0 < W ∧ 2 * ((K : ℝ) + 8) * (K + 2) / W ≤ (δ / 4) ^ 2 := by
  obtain ⟨W, hW⟩ := exists_nat_gt (max 1 (2 * ((K : ℝ) + 8) * (K + 2) / (δ / 4) ^ 2))
  have hw : 0 < (W : ℝ) := (by norm_num : (0 : ℝ) < 1).trans
    ((le_max_left _ _).trans_lt hW)
  refine ⟨W, by exact_mod_cast hw, (div_le_iff₀ hw).mpr ?_⟩
  have h := (div_le_iff₀ (by positivity : 0 < (δ / 4) ^ 2)).mp ((le_max_right _ _).trans hW.le)
  linarith

/-- At a fixed width, the window contributes a bounded fraction of one block. -/
private theorem variance_bound {K L W G : ℕ} {δ ω : ℝ}
    (hδ : 0 < δ) (hw : 0 < W) (hWL : W ≤ L) (hG : G ≤ K)
    (hω : ω ≤ 1) (hwSize : 2 * ((K : ℝ) + 8) * (K + 2) / W ≤ (δ / 4)^2) :
    Real.sqrt (((FineFixedCorrection.binWindow K L W).card : ℝ) *
      (G * (L : ℝ)^2 + 2 * ω * (L : ℝ)^2)) ≤ (δ / 4) * (L : ℝ)^2 := by
  have hwr : 0 < (W : ℝ) := by exact_mod_cast hw
  have hwl : (W : ℝ) ≤ L := by exact_mod_cast hWL
  have hl : 1 ≤ (L : ℝ) := by exact_mod_cast (show 1 ≤ L by omega)
  have hsq : (L : ℝ) ≤ (L : ℝ)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hl) (Nat.cast_nonneg (α := ℝ) L)]
  have htwo : 2 ≤ ((K : ℝ) + 8) * (L : ℝ)^2 / W := by
    apply (le_div_iff₀ hwr).mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) K) (sq_nonneg (L : ℝ))]
  have hwin : ((FineFixedCorrection.binWindow K L W).card : ℝ) ≤
      2 * (((K : ℝ) + 8) * (L : ℝ)^2 / W) := by
    linarith [FineFixedCorrection.card_binWindow_le K L hw]
  have hG' : (G : ℝ) ≤ K := by exact_mod_cast hG
  have hmass : (G : ℝ) * (L : ℝ)^2 + 2 * ω * (L : ℝ)^2 ≤ ((K : ℝ) + 2) * (L : ℝ)^2 := by
    rw [← add_mul]; exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ ((FineFixedCorrection.binWindow K L W).card : ℝ) * (((K : ℝ) + 2) * (L : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ (2 * (((K : ℝ) + 8) * (L : ℝ)^2 / W)) * (((K : ℝ) + 2) * (L : ℝ)^2) :=
      mul_le_mul_of_nonneg_right hwin (by positivity)
    _ = (2 * ((K : ℝ) + 8) * (K + 2) / W) * ((L : ℝ)^2)^2 := by ring
    _ ≤ (δ / 4)^2 * ((L : ℝ)^2)^2 := mul_le_mul_of_nonneg_right hwSize (sq_nonneg _)
    _ = _ := by ring

private theorem near_count_mono {K L : ℕ} (Z : RowPairAverage.Pin K L → (ℝ × ℝ) → ℤ)
    {A B : ℤ} (h : A ≤ B) (a : ℝ × ℝ) :
    RowPairAverage.count Z A a ≤ RowPairAverage.count Z B a := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro p hp
  obtain ⟨_, hne, hh⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, hh.trans_le h⟩

/-- A fixed-width overflow estimate for the rounded affine projection. -/
private theorem integer_bins {K W : ℕ} {δ : ℝ} (hK : 0 < K) (hW : 0 < W)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hwSize : 2 * ((K : ℝ) + 8) * (K + 2) / W ≤ (δ / 4)^2)
    (good : Finset (Fin K)) (hg : 0 < good.card) (D : Fin K → ℤ)
    (Z : (L : ℕ) → Fin K × GridPairs.Grid L → ℤ) {r : ℕ → ℝ}
    (hI : Set.InjOn D good) (hD : ∀ b, 0 ≤ D b ∧ D b ≤ (K : ℤ))
    (hr : Tendsto r atTop (𝓝 0))
    (herr : ∀ᶠ L : ℕ in atTop, ∀ i, |FineData.error D (Z L) i| ≤ r L * (L : ℝ)^2) :
    ∀ᶠ L : ℕ in atTop, ∃ a ∈ SkewParameters.good (δ / 4) L (E L),
      ∃ q : Fin K × Fin L → Fin (H L),
      let Y := fun i : Fin (good.card * L ^ 2) =>
        SkewScores.score (δ / 4) (Z L) (FineIndex.ambient good i) a - ((q (FineIndex.group good i)).val : ℤ)
      (∀ i, Y i / (W : ℤ) ∈ FineFixedCorrection.binWindow K L W) ∧
      (∑ j ∈ FineFixedCorrection.binWindow K L W,
        max 0 ((CountIntensity.binCount Y (W : ℤ) j : ℝ) - (W : ℝ))) ≤
        δ * good.card * (L : ℝ)^2 := by
  have hd : 0 < δ / 4 := by positivity
  have hd1 : δ / 4 < 1 := by linarith
  obtain ⟨ω, hω, hωt, hparams⟩ := FineParameterChoice.exists_parameters hK hd hd1 D Z hr herr
  have hquad : Tendsto (fun L => Real.sqrt (6 * (good.card : ℝ) * ω L)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (hωt.const_mul (6 * (good.card : ℝ)))
  have hdisc : Tendsto (fun L => 2 * (good.card : ℝ) * (2 * E L + 1) / (H L : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using tendsto_discrepancy_div_H.const_mul (2 * (good.card : ℝ))
  have hG : good.card ≤ K := (Finset.card_le_univ good).trans_eq (Fintype.card_fin _)
  have hG1 : (1 : ℝ) ≤ good.card := by exact_mod_cast hg
  filter_upwards [hparams, herr, eventually_pos hK, eventually_ge_atTop W,
    (tendsto_B hK).eventually (eventually_ge_atTop W),
    (tendsto_h.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))),
    (tendsto_discrepancy_div_H.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))),
    (FineParameterChoice.tendsto_perturbationEnvelope hr).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    hr.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    hωt.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    hquad.eventually (gt_mem_nhds hd), hdisc.eventually (gt_mem_nhds hd)] with
    L hparam he hp hWL hWB hh hsmall hpert hr1 hω1 h1 h2
  have hL : 0 < L := hW.trans_le hWL
  have hs : 0 < (L : ℝ)^2 := by positivity
  have hH : 0 < (H L : ℝ) := by exact_mod_cast hp.1
  have hHLr : (H L : ℝ) ≤ (L : ℝ)^2 := (div_le_one hs).mp hh.le
  have hHL : H L ≤ L^2 := by exact_mod_cast hHLr
  have hE : 2 * E L + 1 ≤ (L : ℝ)^2 := ((div_le_one hH).mp hsmall.le).trans hHLr
  have her (i) : |FineData.error D (Z L) i| ≤ (L : ℝ)^2 :=
    (he i).trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hr1.le) hs.le])
  have hη (b : Fin K) (p : GridPairs.Grid L) : |FineData.perturbation D (Z L) (H L) b p| ≤ 1 :=
    (FineParameterChoice.perturbation_le D (Z L) hL he b p).trans hpert.le
  obtain ⟨a, ha, hsquare, hnear⟩ := hparam
  have hnear' := (div_le_div_of_nonneg_right (near_count_mono
    (SkewScores.score (δ / 4) (Z L)) (by exact_mod_cast hWB : (W : ℤ) ≤ B K L) a) hs.le).trans hnear
  obtain ⟨q, hsupport, hbound⟩ := FineFixedCorrection.exists_bin_bound hK hL hp.1 hW hHL hd hd1
    (by unfold E; positivity) hE (hω L) D (Z L) good hI hD her hη ha hsquare hnear'
  refine ⟨a, ha, q, hsupport, hbound.trans ?_⟩
  have hvar := variance_bound hδ hW hWL hG hω1.le hwSize
  have hcg : δ / 4 ≤ δ / 4 * (good.card : ℝ) := by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hG1)]
  have hsub : (δ / 4) * good.card + Real.sqrt (6 * good.card * ω L) +
      2 * good.card * (2 * E L + 1) / H L ≤ δ * good.card - δ / 4 := by linarith
  nlinarith only [mul_le_mul_of_nonneg_left hsub hs.le, hvar]

private theorem overflow_of_integer_bins {ι : Type*} [DecidableEq ι] {M W : ℕ}
    (S : Finset ι) (v : Fin M → ι) (hv : Function.Injective v) (hS : univ.image v = S)
    (s : ι → ℝ) (Y : Fin M → ℤ) (hs : ∀ i, s (v i) = (Y i : ℝ))
    (J : Finset ℤ) (hJ : ∀ i, Y i / (W : ℤ) ∈ J) :
    ((∑ j ∈ S.image (fun u => ⌊s u / W⌋),
      ((S.filter (fun u => ⌊s u / W⌋ = j)).card - W) : ℕ) : ℝ) ≤
    ∑ j ∈ J, max 0 ((CountIntensity.binCount Y W j : ℝ) - (W : ℝ)) := by
  classical
  have hb (i) : ⌊s (v i) / W⌋ = Y i / (W : ℤ) := by rw [hs, Int.floor_div_natCast, Int.floor_intCast]
  have hsub : S.image (fun u => ⌊s u / W⌋) ⊆ J := by
    rintro j hj
    rw [← hS, image_image] at hj
    obtain ⟨i, _, rfl⟩ := mem_image.mp hj
    simpa only [Function.comp_apply, hb] using hJ i
  have hc (j : ℤ) : (S.filter (fun u => ⌊s u / W⌋ = j)).card = CountIntensity.binCount Y W j := by
    rw [← hS, filter_image, card_image_of_injective _ hv]
    simp only [hb, CountIntensity.binCount]
  push_cast
  refine (sum_le_sum fun j _ => ?_).trans (sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => le_max_left (0 : ℝ) _))
  rw [hc]
  by_cases h : W ≤ CountIntensity.binCount Y W j
  · rw [Nat.cast_sub h]; exact le_max_right _ _
  · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero]; exact le_max_left _ _

/-- Compensation when replacing a real slope by its integer ceiling. -/
private def stripShift {L : ℕ} (a : ℝ) (j : Fin L) : ℕ :=
  (⌈a⌉ * (j.val : ℤ) - ⌊a * (j.val : ℝ)⌋).toNat

private theorem stripShift_spec {L : ℕ} (a : ℝ) (j : Fin L) :
    (stripShift a j : ℝ) = (⌈a⌉ : ℤ) * (j.val : ℝ) - (⌊a * (j.val : ℝ)⌋ : ℤ) ∧
      stripShift a j ≤ L := by
  have hj : (0 : ℝ) ≤ j.val := by positivity
  have hjL : (j.val : ℝ) + 1 ≤ L := by exact_mod_cast j.isLt
  have hlo := mul_le_mul_of_nonneg_right (Int.le_ceil a) hj
  have hhi := mul_le_mul_of_nonneg_right (Int.ceil_lt_add_one a).le hj
  let d : ℤ := ⌈a⌉ * (j.val : ℤ) - ⌊a * (j.val : ℝ)⌋
  have hd0 : 0 ≤ d := by
    have : (0 : ℝ) ≤ (d : ℝ) := by
      dsimp [d]; push_cast; linarith [Int.floor_le (a * (j.val : ℝ))]
    exact_mod_cast this
  have hdL : d ≤ (L : ℤ) := by
    have : (d : ℝ) ≤ L := by
      dsimp [d]; push_cast; nlinarith [Int.lt_floor_add_one (a * (j.val : ℝ))]
    exact_mod_cast this
  have he : (stripShift a j : ℤ) = d := Int.toNat_of_nonneg hd0
  exact ⟨by exact_mod_cast he, (Int.toNat_le.mpr hdL)⟩

private theorem rounded_score {K L H : ℕ} (Z : Fin K × GridPairs.Grid L → ℤ)
    (d : ℝ) (a : ℝ × ℝ) (q : Fin K × Fin L → Fin H) (u : Fin K × GridPairs.Grid L) :
    let A := SkewParameters.alpha d a * L
    let B := SkewParameters.beta a * L
    (Z u : ℝ) + (⌈A⌉ : ℤ) * (u.2.1.val : ℝ) + (⌈B⌉ : ℤ) * (u.2.2.val : ℝ) -
        (stripShift A u.2.1 : ℝ) - ((stripShift B u.2.2 + (q (u.1, u.2.2)).val : ℕ) : ℝ) =
      ((SkewScores.score d Z u a - ((q (u.1, u.2.2)).val : ℤ) : ℤ) : ℝ) := by
  dsimp only
  rw [Nat.cast_add, (stripShift_spec _ _).1, (stripShift_spec _ _).1]
  simp only [SkewScores.score, Int.cast_sub, Int.cast_add, Int.cast_natCast]
  ring

end DistanceCounts.FixedWidth
open DistanceCounts DistanceCounts.FixedWidth

theorem OMA.solution : OMA.R_Erdos653_erdos_653_R2.H2 := by
  classical
  intro t δ ht hδ hδ1
  let K := t ^ 2
  have hK : 0 < K := pow_pos ht _
  obtain ⟨W, hW, hwSize⟩ := choose_width K hδ
  refine ⟨W, hW, ?_⟩
  intro good D Z r hI hD hr herr
  by_cases hempty : good = ∅
  · subst good
    filter_upwards with L
    refine ⟨0, L, fun _ _ => 0, fun _ _ => 0, ⟨le_rfl, by positivity⟩,
      ⟨le_rfl, by linarith [Nat.cast_nonneg (α := ℝ) L]⟩, fun _ _ => ⟨Nat.zero_le _, Nat.zero_le _⟩, ?_⟩
    change ((∑ j ∈ ((∅ : Finset (Fin t × Fin t)).product (univ : Finset (GridPairs.Grid L))).image _,
      _ : ℕ) : ℝ) ≤ δ * ((∅ : Finset (Fin t × Fin t)).card : ℝ) * (L : ℝ)^2
    simp
  let e : (Fin t × Fin t) ≃ Fin K := Fintype.equivFinOfCardEq (by simp [K, pow_two])
  let g := good.map e.toEmbedding
  let D' : Fin K → ℤ := fun b => D (e.symm b)
  let Z' (L : ℕ) (u : Fin K × GridPairs.Grid L) := Z L (e.symm u.1, u.2)
  have hcard : g.card = good.card := card_map _
  have hin (b : Fin K) : b ∈ g ↔ e.symm b ∈ good := by
    constructor
    · intro h
      obtain ⟨x, hx, rfl⟩ := mem_map.mp h
      simpa using hx
    · intro h
      exact mem_map.mpr ⟨e.symm b, h, e.apply_symm_apply b⟩
  have hi' : Set.InjOn D' g := fun _ h₁ _ h₂ he =>
    e.symm.injective (hI ((hin _).mp h₁) ((hin _).mp h₂) he)
  have hd' (b : Fin K) : 0 ≤ D' b ∧ D' b ≤ (K : ℤ) := by
    simpa [D', K] using hD (e.symm b)
  have herr' : ∀ᶠ L : ℕ in atTop, ∀ u, |FineData.error D' (Z' L) u| ≤ r L * (L : ℝ)^2 := by
    filter_upwards [herr] with L h u
    exact h (e.symm u.1, u.2)
  have hg : 0 < g.card := hcard.symm ▸ Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
  filter_upwards [integer_bins hK hW hδ hδ1 hwSize g hg D' Z' hi' hd' hr herr',
    eventually_ge_atTop 1] with L hL hL1
  obtain ⟨a, ha, q, hsupport, hsum⟩ := hL
  let A := SkewParameters.alpha (δ / 4) a * L
  let B := SkewParameters.beta a * L
  have hLr : 0 ≤ (L : ℝ) := by positivity
  have hA : 0 ≤ A ∧ A ≤ L := by
    have h : 0 ≤ SkewParameters.alpha (δ / 4) a ∧ SkewParameters.alpha (δ / 4) a ≤ 1 := by
      unfold SkewParameters.alpha
      constructor <;> linarith [ha.1.1.1, ha.1.1.2]
    exact ⟨mul_nonneg h.1 hLr, by simpa [A] using mul_le_mul_of_nonneg_right h.2 hLr⟩
  have hB : (L : ℝ) ≤ B ∧ B ≤ 2 * (L : ℝ) := by
    have h : 1 ≤ SkewParameters.beta a ∧ SkewParameters.beta a ≤ 2 := by
      unfold SkewParameters.beta
      constructor <;> linarith [ha.1.2.1, ha.1.2.2]
    exact ⟨by simpa [B] using mul_le_mul_of_nonneg_right h.1 hLr,
      mul_le_mul_of_nonneg_right h.2 hLr⟩
  let wx (_ : Fin t × Fin t) (j : Fin L) := stripShift A j
  let wy (u : Fin t × Fin t) (j : Fin L) := stripShift B j + (q (e u, j)).val
  have hHL : ConstructionScales.H L ≤ L := by
    unfold ConstructionScales.H
    apply Nat.floor_le_of_le
    refine Real.sqrt_le_iff.mpr ⟨hLr, ?_⟩
    have h : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    nlinarith [mul_nonneg (sub_nonneg.mpr h) hLr]
  refine ⟨(⌈A⌉ : ℤ), (⌈B⌉ : ℤ), wx, wy,
    ⟨hA.1.trans (Int.le_ceil A), ?_⟩, ⟨hB.1.trans (Int.le_ceil B), ?_⟩, ?_, ?_⟩
  · exact_mod_cast (Int.ceil_le.mpr (by simpa using hA.2) : ⌈A⌉ ≤ (L : ℤ))
  · exact_mod_cast (Int.ceil_le.mpr (by exact_mod_cast hB.2) : ⌈B⌉ ≤ 2 * (L : ℤ))
  · intro u j
    have hq := (q (e u, j)).isLt
    dsimp only [wx, wy]
    have hx := (stripShift_spec A j).2
    have hy := (stripShift_spec B j).2
    omega
  · let decode : (Fin K × GridPairs.Grid L) ≃ ((Fin t × Fin t) × GridPairs.Grid L) :=
      e.symm.prodCongr (Equiv.refl _)
    have hdecode (u : Fin K × GridPairs.Grid L) : decode u = (e.symm u.1, u.2) := by
      cases u; rfl
    let v := decode ∘ FineIndex.ambient (L := L) g
    have hv : Function.Injective v := decode.injective.comp (FineIndex.ambient_injective g)
    have hvS : univ.image v = good.product (univ : Finset (GridPairs.Grid L)) := by
      apply eq_of_subset_of_card_le
      · intro u hu
        obtain ⟨i, _, rfl⟩ := mem_image.mp hu
        exact mem_product.mpr ⟨(hin _).mp (FineIndex.ambient_mem g i), mem_univ _⟩
      · simp [card_image_of_injective _ hv, hcard, GridPairs.Grid, pow_two]
    let s (u : (Fin t × Fin t) × GridPairs.Grid L) : ℝ :=
      Z L u + (⌈A⌉ : ℤ) * (u.2.1.val : ℝ) + (⌈B⌉ : ℤ) * (u.2.2.val : ℝ) -
        wx u.1 u.2.1 - wy u.1 u.2.2
    let Y (i : Fin (g.card * L^2)) := SkewScores.score (δ / 4) (Z' L) (FineIndex.ambient g i) a -
      ((q (FineIndex.group g i)).val : ℤ)
    have hmatch (i) : s (v i) = (Y i : ℝ) := by
      simpa [s, v, hdecode, Z', wx, wy, Y, A, B, FineIndex.group] using
        rounded_score (Z' L) (δ / 4) a q (FineIndex.ambient g i)
    have h := overflow_of_integer_bins _ v hv hvS s Y hmatch _ hsupport
    exact h.trans (hcard ▸ hsum)
end
