import OMAStatements.S_mo_393843
import Mathlib

-- Original Lean proof by @AkiRA-COM-FP (PR #17739; statement #13354).
-- Multiset product bounds and root transport now use Mathlib directly.

open Polynomial Set
open scoped NNReal

open OMA.S_mo_393843

private theorem norm_int_as_natAbs (z : ℤ) : ‖(z : ℂ)‖ = (z.natAbs : ℝ) := by
  rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]

private theorem root_bound_int_polynomial (H : ℕ) {f : ℤ[X]} (hf : f ≠ 0)
    (hH : HasHeightAtMost f H) {z : ℂ} (hz : (f.map (algebraMap ℤ ℂ)).IsRoot z) :
    ‖z‖ ≤ (H : ℝ)+1 := by
  let F := f.map (algebraMap ℤ ℂ)
  have hF : F ≠ 0 := by
    intro he
    apply hf
    apply Polynomial.map_injective (algebraMap ℤ ℂ) (FaithfulSMul.algebraMap_injective ℤ ℂ)
    simpa [F] using he
  have hSize (i : ℕ) : ‖F.coeff i‖₊ ≤ (H : ℝ≥0) := by
    have h : ‖F.coeff i‖ ≤ (H : ℝ) := by
      dsimp only [F]
      rw [coeff_map]
      change ‖(f.coeff i : ℂ)‖ ≤ _
      rw [norm_int_as_natAbs]
      exact_mod_cast hH i
    exact_mod_cast h
  have hLC : (1 : ℝ≥0) ≤ ‖F.leadingCoeff‖₊ := by
    have h : (1 : ℝ) ≤ ‖F.leadingCoeff‖ := by
      dsimp only [F]
      rw [leadingCoeff_map_of_injective (FaithfulSMul.algebraMap_injective ℤ ℂ)]
      change (1 : ℝ) ≤ ‖(f.leadingCoeff : ℂ)‖
      rw [norm_int_as_natAbs]
      exact_mod_cast (Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr hf))
    exact_mod_cast h
  have hSup : (Finset.range F.natDegree).sup (fun i => ‖F.coeff i‖₊) ≤ (H : ℝ≥0) :=
    Finset.sup_le_iff.mpr (fun i _ => hSize i)
  have hDiv : (Finset.range F.natDegree).sup (fun i => ‖F.coeff i‖₊) / ‖F.leadingCoeff‖₊ ≤
      (H : ℝ≥0) := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hLC)).mpr
    exact hSup.trans (le_mul_of_one_le_right (by positivity) hLC)
  have hCau : F.cauchyBound ≤ (H : ℝ≥0)+1 := by
    rw [Polynomial.cauchyBound]
    exact add_le_add hDiv le_rfl
  have hRoot := (hz.norm_lt_cauchyBound hF).le.trans hCau
  exact_mod_cast hRoot

private theorem root_product_bound (H : ℕ) (G : ℂ[X])
    (hBound : ∀ z ∈ G.roots, ‖z‖ ≤ (H : ℝ)+1) :
    (G.roots.map (fun z => max 1 ‖z‖)).prod ≤ ((H : ℝ)+1)^G.natDegree := by
  have hR : (1 : ℝ) ≤ (H : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg H)
  have hProd : (G.roots.map (fun z => max 1 ‖z‖)).prod ≤
      ((H : ℝ) + 1) ^ G.roots.card := by
    simpa using Multiset.prod_map_le_prod_map₀ (fun z : ℂ => max 1 ‖z‖)
      (fun _ => (H : ℝ) + 1)
      (fun _ _ => le_trans zero_le_one (le_max_left _ _))
      (fun z hz => max_le hR (hBound z hz))
  exact hProd.trans (pow_le_pow_right₀ hR (card_roots' G))

private theorem factor_height_bound {d H : ℕ} {g : ℤ[X]} (hg : g ∈ boundedHeightFactors d H) :
    HasHeightAtMost g (H*(H+1)^d*2^d) := by
  classical
  obtain ⟨hDegree,f,hf,hH,hDvd⟩ := hg
  have hg0 : g ≠ 0 := by
    intro he
    apply hf
    simpa [he] using hDvd
  let F := f.map (algebraMap ℤ ℂ)
  let G := g.map (algebraMap ℤ ℂ)
  have hG0 : G ≠ 0 := by
    intro he
    apply hg0
    apply Polynomial.map_injective (algebraMap ℤ ℂ) (FaithfulSMul.algebraMap_injective ℤ ℂ)
    simpa [G] using he
  have hRoots (z : ℂ) (hz : z ∈ G.roots) : ‖z‖ ≤ (H : ℝ)+1 := by
    have hZ : G.IsRoot z := (mem_roots hG0).mp hz
    have hDiv : G ∣ F := map_dvd (Polynomial.mapRingHom (algebraMap ℤ ℂ)) hDvd
    exact root_bound_int_polynomial H hf hH (hZ.dvd hDiv)

  have hLC : ‖G.leadingCoeff‖ ≤ (H : ℝ) := by
    have hDiv : g.leadingCoeff.natAbs ∣ f.leadingCoeff.natAbs :=
      Int.natAbs_dvd_natAbs.mpr (leadingCoeff_dvd_leadingCoeff hDvd)
    have h := (Nat.le_of_dvd (Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr hf)) hDiv).trans
      (hH f.natDegree)
    dsimp only [G]
    rw [leadingCoeff_map_of_injective (FaithfulSMul.algebraMap_injective ℤ ℂ)]
    change ‖(g.leadingCoeff : ℂ)‖ ≤ _
    rw [norm_int_as_natAbs]
    exact_mod_cast h
  have hGD : G.natDegree = d :=
    (natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective ℤ ℂ) g).trans hDegree
  have hM : G.mahlerMeasure ≤ (H : ℝ)*((H : ℝ)+1)^d := by
    rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
    have hProd := root_product_bound H G hRoots
    rw [hGD] at hProd
    exact mul_le_mul hLC hProd
      (Multiset.prod_map_nonneg fun _ _ => le_trans zero_le_one (le_max_left _ _))
      (by positivity)

  intro i
  have hBig : ((g.coeff i).natAbs : ℝ) ≤ (H : ℝ)*((H : ℝ)+1)^d*2^d := by
    have h := norm_coeff_le_choose_mul_mahlerMeasure i G
    rw [hGD] at h
    dsimp only [G] at h
    rw [coeff_map] at h
    change ‖(g.coeff i : ℂ)‖ ≤ _ at h
    rw [norm_int_as_natAbs] at h
    refine h.trans ?_
    rw [mul_comm ((H : ℝ)*((H : ℝ)+1)^d)]
    have hChoose : ((d.choose i : ℕ) : ℝ) ≤ 2^d := by
      exact_mod_cast Nat.choose_le_two_pow d i
    exact mul_le_mul hChoose hM (mahlerMeasure_nonneg _) (by positivity)
  exact_mod_cast hBig

theorem OMA.solution : type_of% @OMA.S_mo_393843.main := by
  classical
  intro d H
  refine ⟨?_,fun g hg => factor_height_bound hg⟩
  let B : ℕ := H*(H+1)^d*2^d
  let choices : Finset ℤ := Finset.Icc (-(B : ℤ)) (B : ℤ)
  have hChoice (g : boundedHeightFactors d H) (i : Fin (d+1)) : g.val.coeff i.val ∈ choices := by
    have h : (g.val.coeff i.val).natAbs ≤ B := factor_height_bound g.property i.val
    apply Finset.mem_Icc.mpr
    omega
  let encode (g : boundedHeightFactors d H) (i : Fin (d+1)) : ↥choices :=
    ⟨g.val.coeff i.val,hChoice g i⟩
  have hEnc : Function.Injective encode := by
    intro g h he
    apply Subtype.ext
    apply Polynomial.ext
    intro i
    by_cases hi : i < d+1
    · exact congrArg Subtype.val (congrFun he (⟨i,hi⟩ : Fin (d+1)))
    · have hG := g.property.1
      have hH := h.property.1
      rw [coeff_eq_zero_of_natDegree_lt (show g.val.natDegree < i by omega),
        coeff_eq_zero_of_natDegree_lt (show h.val.natDegree < i by omega)]
  let _ : Finite (boundedHeightFactors d H) := Finite.of_injective encode hEnc
  exact Set.toFinite _
