import OMAReductions.R_Fuglede_FugledeConjecture_variants_dim_1_R1
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
Small factors in the cyclic universal spectrum problem. Fourier orthogonality
settles two- and three-point complements. A half-circle of characters
settles a two-point fixed tile.
-/

open Finset AddChar ZMod
open scoped BigOperators ComplexConjugate

namespace OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1_H2_R1

private lemma halfplane_neg (z : ℂ) (hz : z ≠ 0) :
    (0 < (-z).re ∨ (-z).re = 0 ∧ 0 < (-z).im) ↔ ¬ (0 < z.re ∨ z.re = 0 ∧ 0 < z.im) := by
  have hnon : z.re ≠ 0 ∨ z.im ≠ 0 := by
    by_contra! h
    apply hz
    exact Complex.ext (by simpa using h.1) (by simpa using h.2)
  simp only [Complex.neg_re, Complex.neg_im, neg_pos, neg_eq_zero]
  rcases lt_trichotomy z.re 0 with hr | hr | hr
  · simp [hr, hr.ne, not_lt_of_gt hr]
  · have hi := hnon.resolve_left (by simp [hr])
    simp only [hr, lt_self_iff_false, true_and, false_or]
    exact ⟨fun h => not_lt_of_gt h, fun h => lt_of_le_of_ne (le_of_not_gt h) hi⟩
  · simp [hr, hr.ne', not_lt_of_gt hr]

private lemma phase_eq {L : ℕ} [NeZero L] (z w : ℤ)
    (h : (z : ZMod L) = (w : ZMod L)) :
    Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ)) =
    Complex.exp (2 * Real.pi * Complex.I * (w : ℂ) / (L : ℂ)) := by
  have hd : (L : ℤ) ∣ z-w := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa using sub_eq_zero.mpr h
  obtain ⟨k, hk⟩ := hd
  have hr : (z : ℂ) = (w : ℂ) + (L : ℂ) * (k : ℂ) := by
    exact_mod_cast (show z = w+(L:ℤ)*k by omega)
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have he : 2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ) =
      2 * Real.pi * Complex.I * (w : ℂ) / (L : ℂ) + (k:ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hr]
    field_simp [hL]
  rw [he, Complex.exp_add, Complex.exp_eq_one_iff.mpr ⟨k,rfl⟩, mul_one]

private lemma explicit_character (L : ℕ) [NeZero L] : ∃ c : AddChar (ZMod L) ℂ,
    ∀ z : ℤ, c (z : ZMod L) = Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ)) := by
  let f (z : ℤ) := Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))
  refine ⟨⟨fun u => f u.val, by simp [f], ?_⟩, ?_⟩
  · intro u v
    change f (u+v).val = f u.val * f v.val
    have h : f (u+v).val = f ((u.val : ℤ) + (v.val : ℤ)) :=
      phase_eq _ _ (by simp)
    rw [h]
    dsimp [f]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · intro z
    exact phase_eq _ _ (by simp)

section FiniteFourier

variable {L : ℕ} {χ : AddChar (ZMod L) ℂ}

private lemma tile_bijective {A B : Finset (ZMod L)}
    (h : ∀ z : ZMod L, ∃! p : A × B, (p.1.1 : ZMod L) + p.2.1 = z) :
    Function.Bijective (fun p : A × B => (p.1.1 : ZMod L) + p.2.1) := by
  constructor
  · intro p q hpq
    obtain ⟨r, _, hr⟩ := h (q.1.1 + q.2.1)
    exact (hr p hpq).trans (hr q rfl).symm
  · intro z
    obtain ⟨p, hp, _⟩ := h z
    exact ⟨p, hp⟩

private lemma char_ne_zero (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) (z : ZMod L) : χ z ≠ 0 := by
  rw [← ZMod.intCast_zmod_cast z, hχ]
  exact Complex.exp_ne_zero _

private lemma phase_conj {L : ℕ} (j : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * ((-j : ℤ) : ℂ) / (L : ℂ)) =
    conj (Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) / (L : ℂ))) := by
  rw [← Complex.exp_conj]
  apply congrArg Complex.exp
  simp only [Int.cast_neg, map_div₀, map_mul, map_ofNat, map_intCast, map_natCast,
    Complex.conj_ofReal, Complex.conj_I]
  ring

private lemma char_conj (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) (z : ZMod L) :
    χ (-z) = conj (χ z) := by
  rw [← ZMod.intCast_zmod_cast z, ← Int.cast_neg, hχ, hχ]
  exact phase_conj _

private lemma one_point {ℬ : Finset (Finset (ZMod L))}
    (h : ∀ B ∈ ℬ, B.card = 1) :
    ∃ Γ : Finset (ZMod L), (∀ B ∈ ℬ, Γ.card = B.card) ∧
      (∀ B ∈ ℬ, ∀ g ∈ Γ, ∀ j ∈ Γ, g ≠ j →
        ∑ b ∈ B, χ ((g-j)*b) = 0) := by
  refine ⟨{0}, fun B hB => by simp [h B hB], ?_⟩
  intro B hB g hg j hj hgj
  simp only [mem_singleton] at hg hj
  exact (hgj (hg.trans hj.symm)).elim

private lemma neg_coeff (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) {B : Finset (ZMod L)} {k : ZMod L}
    (h : (∑ b ∈ B, χ (k*b)) = 0) :
    (∑ b ∈ B, χ ((-k)*b)) = 0 := by
  simpa only [map_sum, map_zero, neg_mul, char_conj hχ] using congrArg conj h

private lemma double_coeff (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) {B : Finset (ZMod L)} (hB : B.card = 3) {k : ZMod L}
    (h : (∑ b ∈ B, χ (k*b)) = 0) :
    (∑ b ∈ B, χ ((k+k)*b)) = 0 := by
  obtain ⟨u,v,w,huv,huw,hvw,rfl⟩ := Finset.card_eq_three.mp hB
  let f (b : ZMod L) := χ (k*b)
  have hu : u ∉ ({v,w} : Finset (ZMod L)) := by simp [huv,huw]
  have hv : v ∉ ({w} : Finset (ZMod L)) := by simp [hvw]
  have hs : f u + (f v + f w) = 0 := by
    change (∑ b ∈ ({u,v,w} : Finset (ZMod L)), f b) = 0 at h
    rwa [Finset.sum_insert hu, Finset.sum_insert hv, Finset.sum_singleton] at h
  have hc : conj (f u) + (conj (f v) + conj (f w)) = 0 := by
    simpa only [map_add, map_zero] using congrArg conj hs
  have hunit (b) : f b * conj (f b) = 1 := by
    dsimp [f]
    rw [← char_conj hχ, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hp : f u * f v + f u * f w + f v * f w = 0 := by
    calc
      _ = f u * f v * f w * (conj (f u) + (conj (f v) + conj (f w))) := by
        linear_combination -(f v*f w)*hunit u - (f u*f w)*hunit v - (f u*f v)*hunit w
      _ = 0 := by rw [hc,mul_zero]
  rw [Finset.sum_insert hu, Finset.sum_insert hv, Finset.sum_singleton]
  simp only [add_mul, AddChar.map_add_eq_mul]
  change f u*f u + (f v*f v + f w*f w) = 0
  linear_combination (f u + (f v + f w))*hs - 2*hp

variable [NeZero L]

private lemma tile_card {A B : Finset (ZMod L)}
    (h : ∀ z : ZMod L, ∃! p : A × B, p.1.1 + p.2.1 = z) :
    A.card * B.card = L := by
  simpa using Fintype.card_congr (Equiv.ofBijective _ (tile_bijective h))

private lemma char_eq_one (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) {z : ZMod L} (h : χ z = 1) :
    z = 0 := by
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have hC : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  rw [← ZMod.intCast_zmod_cast z, hχ] at h
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
  have he : ((z.val : ℤ) : ℂ) = (L : ℂ) * (k : ℂ) := by
    apply mul_left_cancel₀ hC
    have hm := (div_eq_iff hL).mp hk
    rw [ZMod.cast_eq_val] at hm
    linear_combination hm
  have he' : (z.val : ℤ) = (L : ℤ) * k := by exact_mod_cast he
  simpa using congrArg (fun t : ℤ => (t : ZMod L)) he'

private lemma char_sum (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) (k : ZMod L) :
    (∑ z : ZMod L, χ (k*z)) = if k = 0 then (L : ℂ) else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [if_neg hk]
    let f (z : ZMod L) := χ (k*z)
    have h : (∑ z : ZMod L, f (z+1)) = ∑ z, f z :=
      Fintype.sum_equiv (Equiv.addRight _) _ _ (fun _ => rfl)
    have hp : (∑ z, f z) * χ k = ∑ z, f z := by
      simpa only [f, mul_add, mul_one, AddChar.map_add_eq_mul, Finset.sum_mul] using h
    have hz : (∑ z, f z) * (χ k-1) = 0 := by
      rw [mul_sub, mul_one, hp, sub_self]
    exact (mul_eq_zero.mp hz).resolve_right
      (sub_ne_zero.mpr (fun he => hk (char_eq_one hχ he)))

private lemma tile_fourier (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) {A B : Finset (ZMod L)}
    (h : ∀ z : ZMod L, ∃! p : A × B, p.1.1 + p.2.1 = z) {k : ZMod L} (hk : k ≠ 0) :
    (∑ a ∈ A, χ (k*a)) * (∑ b ∈ B, χ (k*b)) = 0 := by
  calc
    _ = ∑ a ∈ A, ∑ b ∈ B, χ (k*(a+b)) := by
      rw [Finset.sum_mul_sum]
      simp only [mul_add, AddChar.map_add_eq_mul]
    _ = ∑ z : ZMod L, χ (k*z) := by
      rw [← Finset.sum_coe_sort A]
      simp_rw [← Finset.sum_coe_sort B]
      let f (p : A × B) := χ (k*(p.1.1+p.2.1))
      calc
        _ = ∑ p : A × B, f p := (Fintype.sum_prod_type f).symm
        _ = _ := Fintype.sum_equiv (Equiv.ofBijective _ (tile_bijective h)) _ _ (fun _ => rfl)
    _ = 0 := by rw [char_sum hχ, if_neg hk]

private lemma coeff_ne_zero (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) {A : Finset (ZMod L)} (hA : 0 < A.card) (hproper : A.card < L) :
    ∃ k : ZMod L, k ≠ 0 ∧ (∑ a ∈ A, χ (k*a)) ≠ 0 := by
  classical
  by_contra! h
  have hproper' : A ≠ univ := by
    intro he
    simp [he] at hproper
  obtain ⟨x, hx⟩ : ∃ x, x ∉ A := by
    by_contra! hAll
    exact hproper' (Finset.eq_univ_of_forall hAll)
  have hz (k : ZMod L) :
      (∑ a ∈ A, χ (k*(a-x))) = if k = 0 then (A.card : ℂ) else 0 := by
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk]
      simp only [sub_eq_add_neg, mul_add, AddChar.map_add_eq_mul, ← Finset.sum_mul, h k hk, zero_mul]
  have hEq : (A.card : ℂ) = 0 := by
    calc
      _ = ∑ k : ZMod L, ∑ a ∈ A, χ (k*(a-x)) := by simp [hz]
      _ = ∑ a ∈ A, ∑ k : ZMod L, χ ((a-x)*k) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun k _ => by rw [mul_comm k]))
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        have hax : a ≠ x := fun he => hx (he ▸ ha)
        rw [char_sum hχ, if_neg (sub_ne_zero.mpr hax)]
  exact (Nat.cast_ne_zero.mpr hA.ne') hEq

private lemma char_exp (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) (g h b : ZMod L) :
    χ ((g-h)*b) =
      Complex.exp (2 * Real.pi * Complex.I *
        (((g.val : ℝ) - (h.val : ℝ)) * (b.val : ℝ) / (L : ℝ))) := by
  let z : ℤ := ((g.val : ℤ)-(h.val : ℤ))*(b.val : ℤ)
  have hz : (z : ZMod L) = (g-h)*b := by simp [z]
  rw [← hz, hχ]
  congr 1
  dsimp [z]
  push_cast
  ring

private lemma all_freqs (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) {ℬ : Finset (Finset (ZMod L))}
    (h : ∀ B ∈ ℬ, B.card = L) :
    ∃ Γ : Finset (ZMod L), (∀ B ∈ ℬ, Γ.card = B.card) ∧
      (∀ B ∈ ℬ, ∀ g ∈ Γ, ∀ j ∈ Γ, g ≠ j →
        ∑ b ∈ B, χ ((g-j)*b) = 0) := by
  refine ⟨univ, fun B hB => by simp [h B hB], ?_⟩
  intro B hB g hg j hj hgj
  rw [B.eq_univ_of_card (by simpa using h B hB)]
  exact (char_sum hχ (g-j)).trans (if_neg (sub_ne_zero.mpr hgj))

private lemma two_point_complements (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) {A : Finset (ZMod L)} {ℬ : Finset (Finset (ZMod L))}
    (hA : 0 < A.card) (hproper : A.card < L)
    (hcard : ∀ B ∈ ℬ, B.card = 2)
    (htile : ∀ B ∈ ℬ, ∀ z : ZMod L, ∃! p : A × B, p.1.1 + p.2.1 = z) :
    ∃ Γ : Finset (ZMod L), (∀ B ∈ ℬ, Γ.card = B.card) ∧
      (∀ B ∈ ℬ, ∀ g ∈ Γ, ∀ j ∈ Γ, g ≠ j →
        ∑ b ∈ B, χ ((g-j)*b) = 0) := by
  obtain ⟨k, hk, hcoeff⟩ := coeff_ne_zero hχ hA hproper
  refine ⟨{0,k}, fun B hB => by simp [hcard B hB, Ne.symm hk], ?_⟩
  intro B hB g hg j hj hgj
  have hpos : (∑ b ∈ B, χ (k*b)) = 0 :=
    (mul_eq_zero.mp (tile_fourier hχ (htile B hB) hk)).resolve_left hcoeff
  have hneg := neg_coeff hχ hpos
  simp only [mem_insert, mem_singleton] at hg hj
  rcases hg with rfl|rfl <;> rcases hj with rfl|rfl
  · exact (hgj rfl).elim
  · simpa only [zero_sub] using hneg
  · simpa only [sub_zero] using hpos
  · exact (hgj rfl).elim

private lemma three_point_complements (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) {A : Finset (ZMod L)} {ℬ : Finset (Finset (ZMod L))}
    (hA : 0 < A.card) (hproper : A.card < L) {B₀ : Finset (ZMod L)} (hB₀ : B₀ ∈ ℬ)
    (hcard : ∀ B ∈ ℬ, B.card = 3)
    (htile : ∀ B ∈ ℬ, ∀ z : ZMod L, ∃! p : A × B, p.1.1 + p.2.1 = z) :
    ∃ Γ : Finset (ZMod L), (∀ B ∈ ℬ, Γ.card = B.card) ∧
      (∀ B ∈ ℬ, ∀ g ∈ Γ, ∀ j ∈ Γ, g ≠ j →
        ∑ b ∈ B, χ ((g-j)*b) = 0) := by
  obtain ⟨k,hk,hA'⟩ := coeff_ne_zero hχ hA hproper
  have hpos (B) (hB : B ∈ ℬ) : (∑ b ∈ B, χ (k*b)) = 0 :=
    (mul_eq_zero.mp (tile_fourier hχ (htile B hB) hk)).resolve_left hA'
  have hdbl (B) (hB : B ∈ ℬ) : (∑ b ∈ B, χ ((k+k)*b)) = 0 :=
    double_coeff hχ (hcard B hB) (hpos B hB)
  have hk2 : k+k ≠ 0 := by
    intro he
    have h := hdbl B₀ hB₀
    simp [he,hcard B₀ hB₀] at h
  have hkd : k+k ≠ k := by
    intro he
    exact hk (add_left_cancel (show k+k = k+0 by simpa using he))
  refine ⟨{0,k,k+k}, fun B hB =>
    (Finset.card_eq_three.mpr ⟨0,k,k+k,hk.symm,hk2.symm,hkd.symm,rfl⟩).trans (hcard B hB).symm, ?_⟩
  intro B hB g hg j hj hgj
  simp only [mem_insert, mem_singleton] at hg hj
  rcases hg with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl
  · exact (hgj rfl).elim
  · simpa only [zero_sub] using neg_coeff hχ (hpos B hB)
  · simpa only [zero_sub] using neg_coeff hχ (hdbl B hB)
  · simpa only [sub_zero] using hpos B hB
  · exact (hgj rfl).elim
  · simpa only [sub_add_cancel_left] using neg_coeff hχ (hpos B hB)
  · simpa only [sub_zero] using hdbl B hB
  · simpa only [add_sub_cancel_right] using hpos B hB
  · exact (hgj rfl).elim

private lemma two_point_tile (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) {A : Finset (ZMod L)} {ℬ : Finset (Finset (ZMod L))}
    (hA : A.card = 2) {B₀ : Finset (ZMod L)} (hB₀ : B₀ ∈ ℬ)
    (htile : ∀ B ∈ ℬ, ∀ z : ZMod L, ∃! p : A × B, p.1.1 + p.2.1 = z) :
    ∃ Γ : Finset (ZMod L), (∀ B ∈ ℬ, Γ.card = B.card) ∧
      (∀ B ∈ ℬ, ∀ g ∈ Γ, ∀ j ∈ Γ, g ≠ j →
        ∑ b ∈ B, χ ((g-j)*b) = 0) := by
  classical
  obtain ⟨u, v, huv, hpair⟩ := Finset.card_eq_two.mp hA
  have hsize (B) (hB : B ∈ ℬ) : 2 * B.card = L := by
    simpa only [hA] using tile_card (htile B hB)
  have hpos : 0 < B₀.card := by have := hsize B₀ hB₀; have := NeZero.ne L; omega
  obtain ⟨η, hη, hηB⟩ := coeff_ne_zero hχ hpos (by have := hsize B₀ hB₀; omega)
  let ψ (g : ZMod L) := χ (g*(v-u))
  have hψadd (g j : ZMod L) : ψ (g+j) = ψ g * ψ j := by
    simp only [ψ, add_mul, AddChar.map_add_eq_mul]
  have hψne (g : ZMod L) : ψ g ≠ 0 := by
    dsimp [ψ]
    exact char_ne_zero hχ _
  have hfac (k : ZMod L) : (∑ a ∈ A, χ (k*a)) =
      χ (k*u)*(1+ψ k) := by
    rw [hpair, Finset.sum_insert (by simpa using huv), Finset.sum_singleton, mul_add, mul_one]
    have he : k*v = k*u + k*(v-u) := by ring
    rw [he, AddChar.map_add_eq_mul]
  have hpη : ψ η = -1 := by
    have hzero := (mul_eq_zero.mp (tile_fourier hχ (htile B₀ hB₀) hη)).resolve_right hηB
    rw [hfac] at hzero
    have hne : χ (η*u) ≠ 0 := by
      exact char_ne_zero hχ _
    have h := (mul_eq_zero.mp hzero).resolve_left hne
    exact add_eq_zero_iff_eq_neg.mp (by simpa only [add_comm] using h)
  let P (z : ℂ) : Prop := 0 < z.re ∨ z.re = 0 ∧ 0 < z.im
  have hshift (g : ZMod L) : P (ψ (g+η)) ↔ ¬ P (ψ g) := by
    rw [hψadd, hpη, mul_neg_one]
    exact halfplane_neg _ (hψne _)
  let Γ := (univ : Finset (ZMod L)).filter (fun g => P (ψ g))
  let Δ := (univ : Finset (ZMod L)).filter (fun g => ¬ P (ψ g))
  have sumCard : Γ.card + Δ.card = L := by
    simpa only [Γ, Δ, Finset.card_univ, ZMod.card] using
      Finset.card_filter_add_card_filter_not (s := (univ : Finset (ZMod L))) (fun g => P (ψ g))
  have sameCard : Γ.card = Δ.card := by
    apply Finset.card_bij (fun g _ => g+η)
    · intro g hg
      have hp := (mem_filter.mp hg).2
      exact mem_filter.mpr ⟨mem_univ _, fun h => (hshift g).mp h hp⟩
    · intro g _ j _ h
      exact add_right_cancel h
    · intro j hj
      have hp := (mem_filter.mp hj).2
      have hsum : j-η+η = j := sub_add_cancel _ _
      refine ⟨j-η, mem_filter.mpr ⟨mem_univ _, ?_⟩, hsum⟩
      by_contra h
      have hh := (hshift (j-η)).mpr h
      rw [hsum] at hh
      exact hp hh
  refine ⟨Γ, fun B hB => by have := hsize B hB; omega, ?_⟩
  intro B hB g hg j hj hgj
  have hne : ψ (g-j) ≠ -1 := by
    intro he
    have he' := hψadd (g-j) j
    rw [sub_add_cancel, he, neg_one_mul] at he'
    have h := (mem_filter.mp hg).2
    rw [he'] at h
    exact (halfplane_neg (ψ j) (hψne j)).mp h (mem_filter.mp hj).2
  apply (mul_eq_zero.mp (tile_fourier hχ (htile B hB) (sub_ne_zero.mpr hgj))).resolve_left
  rw [hfac]
  apply mul_ne_zero
  · exact char_ne_zero hχ _
  · intro h
    apply hne
    exact add_eq_zero_iff_eq_neg.mp (by simpa only [add_comm] using h)

end FiniteFourier

/-- Odd-order groups with fixed tile of size at least three and complements of size at least four. -/
def H1 : Prop :=
  ∀ (L : ℕ) [NeZero L], L % 2 = 1 →
     ∀ (χ : AddChar (ZMod L) ℂ), (∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) →
    ∀ (A : Finset (ZMod L)) (ℬ : Finset (Finset (ZMod L))), 3 ≤ A.card →
      (∀ B ∈ ℬ, 4 ≤ B.card ∧ ∀ z : ZMod L,
        ∃! p : A × B, p.1.1 + p.2.1 = z) →
      ∃ Γ : Finset (ZMod L), 0 ∈ Γ ∧ (∀ B ∈ ℬ, Γ.card = B.card) ∧
        (∀ B ∈ ℬ, ∀ g ∈ Γ, ∀ j ∈ Γ, g ≠ j →
          ∑ b ∈ B, χ ((g-j)*b) = 0)

/-- Even-order groups with fixed tile of size at least three and complements of size at least four. -/
def H2 : Prop :=
  ∀ (L : ℕ) [NeZero L], L % 2 = 0 →
     ∀ (χ : AddChar (ZMod L) ℂ), (∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) →
    ∀ (A : Finset (ZMod L)) (ℬ : Finset (Finset (ZMod L))), 3 ≤ A.card →
      (∀ B ∈ ℬ, 4 ≤ B.card ∧ ∀ z : ZMod L,
        ∃! p : A × B, p.1.1 + p.2.1 = z) →
      ∃ Γ : Finset (ZMod L), 0 ∈ Γ ∧ (∀ B ∈ ℬ, Γ.card = B.card) ∧
        (∀ B ∈ ℬ, ∀ g ∈ Γ, ∀ j ∈ Γ, g ≠ j →
          ∑ b ∈ B, χ ((g-j)*b) = 0)

theorem main : H1 → H2 → OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1.H2 := by
  intro hOdd hEven L hL A ℬ htile
  classical
  have : NeZero L := ⟨hL.ne'⟩
  obtain ⟨χ, hχ⟩ := explicit_character L
  by_cases hEmpty : ℬ = ∅
  · subst ℬ
    exact ⟨∅, by simp⟩
  obtain ⟨B₀, hB₀⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hc₀ := tile_card (htile B₀ hB₀)
  have ha : 0 < A.card := by
    by_contra! hn
    have hz : A.card = 0 := by omega
    simp only [hz, zero_mul] at hc₀
    omega
  have hb : 0 < B₀.card := by
    by_contra! hn
    have hz : B₀.card = 0 := by omega
    simp only [hz, mul_zero] at hc₀
    omega
  have hc (B) (hB : B ∈ ℬ) : B.card = B₀.card :=
    Nat.eq_of_mul_eq_mul_left ha ((tile_card (htile B hB)).trans hc₀.symm)
  have hs : ∃ Γ : Finset (ZMod L), (∀ B ∈ ℬ, Γ.card = B.card) ∧
      (∀ B ∈ ℬ, ∀ g ∈ Γ, ∀ j ∈ Γ, g ≠ j →
        ∑ b ∈ B, χ ((g-j)*b) = 0) := by
    by_cases ha₁ : A.card = 1
    · exact all_freqs hχ (fun B hB => by rw [hc B hB]; simpa [ha₁] using hc₀)
    by_cases hb₁ : B₀.card = 1
    · exact one_point (fun B hB => (hc B hB).trans hb₁)
    by_cases ha₂ : A.card = 2
    · exact two_point_tile hχ ha₂ hB₀ htile
    by_cases hb₂ : B₀.card = 2
    · have hproper : A.card < L := by rw [hb₂, Nat.mul_comm] at hc₀; omega
      exact two_point_complements hχ ha hproper (fun B hB => (hc B hB).trans hb₂) htile
    by_cases hb₃ : B₀.card = 3
    · have hproper : A.card < L := by rw [hb₃, Nat.mul_comm] at hc₀; omega
      exact three_point_complements hχ ha hproper hB₀ (fun B hB => (hc B hB).trans hb₃) htile
    have hb₄ (B) (hB : B ∈ ℬ) : 4 ≤ B.card := by rw [hc B hB]; omega
    have ht (B) (hB : B ∈ ℬ) := And.intro (hb₄ B hB) (htile B hB)
    by_cases he : L % 2 = 0
    · obtain ⟨Γ, _, hΓ⟩ := hEven L he χ hχ A ℬ (by omega) ht
      exact ⟨Γ, hΓ⟩
    · obtain ⟨Γ, _, hΓ⟩ := hOdd L (by omega) χ hχ A ℬ (by omega) ht
      exact ⟨Γ, hΓ⟩
  obtain ⟨Γ, hcard, horth⟩ := hs
  refine ⟨Γ, hcard, ?_⟩
  intro B hB g hg j hj hgj
  simpa only [char_exp hχ g j] using horth B hB g hg j hj hgj

end OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1_H2_R1
