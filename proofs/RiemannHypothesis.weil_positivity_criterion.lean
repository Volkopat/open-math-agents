import FormalConjectures.Paper.RiemannHypothesisEquivalents
import Mathlib
/-
Ported from https://github.com/ChironTheCentaur/rh-lab-rh-criteria (commit bfe38b29),
Copyright 2026 Sky (GitHub: ChironTheCentaur), licensed under the Apache License, Version 2.0.
Its Zeta23 part is taken from https://github.com/anthropics/zeta-23-lean (zeta23/Zeta23),
Copyright 2026 Anthropic, PBC, Apache License, Version 2.0; the files under Zeta23/FromPNTPlus
derive from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
Copyright the PrimeNumberTheoremAnd contributors, Apache License, Version 2.0, some of them in turn
from mathlib, Copyright the mathlib contributors, Apache License, Version 2.0.
The copied statement definitions are from google-deepmind/formal-conjectures, Copyright The Formal
Conjectures Authors, Apache License, Version 2.0.
Modifications: the import closure of the result was assembled into one file, unused declarations
were removed, local notations were expanded, attributes other than simp were dropped, a few proofs
were adapted to the pinned Mathlib, comments were removed and local names were shortened.
A copy of the Apache License, Version 2.0 is at https://www.apache.org/licenses/LICENSE-2.0.
-/
-- Zeta23.Defs
section
open scoped BigOperators ArithmeticFunction
open Complex MeasureTheory Set
noncomputable section
namespace Zeta23
def aD (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ u : ℝ, f u * Complex.exp (Complex.I * z * (u : ℂ))
def l (T : ℝ) : ℝ := Real.log (T / (2 * Real.pi))
def eD (T : ℝ) : ℝ := l T + 2 * Real.log 2 - 1
def mu (τ : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (Complex.digamma (1 / 4 + Complex.I * τ / 2)).re
    - Real.log Real.pi / (2 * Real.pi)
def aF (ρ : ℂ) : ℂ := (ρ - 1 / 2) / Complex.I
def reflect (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ
structure aV where
  carrier : Set ℂ
  mult : ℂ → ℕ
  one_le_mult : ∀ ρ ∈ carrier, 1 ≤ mult ρ
  strip : ∀ ρ ∈ carrier, 0 ≤ ρ.re ∧ ρ.re ≤ 1
  qH : ∀ ρ ∈ carrier, reflect ρ ∈ carrier
  kT : ∀ ρ ∈ carrier, mult (reflect ρ) = mult ρ
  dS : ∀ T₁ T₂ : ℝ, (carrier ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite
namespace aV
variable (Z : aV)
def window (T₁ T₂ : ℝ) : Set ℂ := Z.carrier ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}
def simple : Set ℂ := {ρ | Z.mult ρ = 1}
def N (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ Z.window T₁ T₂, Z.mult ρ
def dD (f g : ℝ → ℂ) (ρ : ℂ) : ℂ :=
  (Z.mult ρ : ℂ) * aD f (aF ρ) * (starRingEnd ℂ) (aD g ((starRingEnd ℂ) (aF ρ)))
def W (f g : ℝ → ℂ) : ℂ := ∑' ρ : Z.carrier, Z.dD f g ρ
end aV
namespace Params
variable (T : ℝ)
end Params
namespace aV
end aV
end Zeta23
end
end

-- Zeta23.tZ.ZP
section
noncomputable section
open Matrix Finset
open scoped ComplexOrder
namespace fq
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]
section Reindex
variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)
end Reindex
end fq
end
end

-- Zeta23.tZ.Sm
section
noncomputable section
open Matrix Finset Unitary
open scoped ComplexOrder
namespace fq
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]
section OX
variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)
end OX
end fq
end
end

-- Zeta23.tZ.Sylvester
section
noncomputable section
open Matrix Finset Submodule
open scoped ComplexOrder
namespace fq
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]
end fq
end
end

-- Zeta23.tZ.Inertia
section
noncomputable section
open Matrix Finset Submodule
open scoped ComplexOrder
namespace fq
variable {𝕜 : Type*} [RCLike 𝕜]
variable {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d] [DecidableEq d]
end fq
end
end

-- Zeta23.tZ.VonNeumann
section
noncomputable section
open Matrix Finset
open scoped ComplexOrder
namespace fq
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]
section Bilinear
end Bilinear
section Rearrangement
end Rearrangement
end fq
end
end

-- Zeta23.tZ.ZE
section
noncomputable section
open Matrix Finset
open scoped ComplexOrder
namespace fq
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]
section Elementary
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Elementary
end fq
end
end

-- Zeta23.tZ.Weyl
section
noncomputable section
open Matrix Finset
open scoped ComplexOrder
namespace fq
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]
end fq
end
end

-- Zeta23.tZ
section
end

-- Zeta23.Assembly.Inputs
section
noncomputable section
open Matrix fq
open scoped ComplexOrder
namespace Zeta23
namespace Assembly
variable (Z : aV) (T : ℝ)
end Assembly
end Zeta23
end
end

-- Zeta23.Tail.Basic
section
noncomputable section
namespace Zeta23
namespace Tail
structure jo {ι : Type*} (γ : ι → ℝ) (m : ι → ℕ) (A₀ : ℝ) : Prop where
  one_le : 1 ≤ A₀
  window : ∀ t : ℝ, ∀ s : Finset ι, (∀ ρ ∈ s, t < γ ρ ∧ γ ρ ≤ t + 1) →
    (∑ ρ ∈ s, (m ρ : ℝ)) ≤ A₀ * Real.log (|t| + 3)
lemma jo.zO {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ : ℝ}
    (h : jo γ m A₀) : 0 < A₀ := lt_of_lt_of_le one_pos h.one_le
end Tail
end Zeta23
end
end

-- Zeta23.Tail.acI
section
noncomputable section
open Finset Real
namespace Zeta23
namespace Tail
end Tail
end Zeta23
end
end

-- Zeta23.Tail.Count
section
noncomputable section
open Finset Real
namespace Zeta23
namespace Tail
lemma wT {ι : Type*} (s : Finset ι) (m : ι → ℕ) (key : ι → ℕ) (K : ℕ)
    {C : ℝ} (hkey : ∀ ρ ∈ s, key ρ < K)
    (hcount : ∀ j < K, ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) ≤ C) :
    ∑ ρ ∈ s, (m ρ : ℝ) ≤ K * C := by
  rw [← sum_fiberwise_of_maps_to (g := key) (t := range K)
    (fun ρ hρ => mem_range.mpr (hkey ρ hρ))]
  calc ∑ j ∈ range K, ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ)
      ≤ ∑ j ∈ range K, C := sum_le_sum fun j hj => hcount j (mem_range.mp hj)
    _ = K * C := by rw [sum_const, card_range, nsmul_eq_mul]
end Tail
end Zeta23
end
end

-- Zeta23.Tail.RankOne
section
noncomputable section
open Matrix Finset
open scoped ComplexOrder
namespace Zeta23
namespace Tail
open fq
variable {n : Type*} [Fintype n] [DecidableEq n]
end Tail
end Zeta23
end
end

-- Zeta23.Tail
section
noncomputable section
open Matrix Finset Complex
open scoped ComplexOrder
namespace Zeta23
namespace Tail
open fq
theorem jo.Ao (Z : aV) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    jo (fun ρ : Z.carrier => (ρ : ℂ).im) (fun ρ : Z.carrier => Z.mult ρ) A₀ where
  one_le := hA₀
  window t s hs := by
    classical
    refine le_trans ?_ (hloc t)
    have hfin : (Z.window t (t + 1)).Finite := Z.dS t (t + 1)
    unfold aV.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hsub : s.map (Function.Embedding.subtype _) ⊆ hfin.toFinset := by
      intro x hx
      rw [Finset.mem_map] at hx
      obtain ⟨ρ, hρ, rfl⟩ := hx
      rw [Set.Finite.mem_toFinset]
      exact ⟨ρ.2, hs ρ hρ⟩
    have h := Finset.sum_le_sum_of_subset (f := Z.mult) hsub
    rw [Finset.sum_map] at h
    exact_mod_cast h
section Concrete
variable (Z : aV) (T : ℝ)
variable {P T}
variable {Z}
end Concrete
section Series
variable {Z : aV} {T A₀ C₁ : ℝ}
namespace UQ
end UQ
end Series
section Hermitian
variable {T : ℝ}
variable {Z : aV} {A₀ C₁ : ℝ}
end Hermitian
section Export
open Filter
variable {Z : aV} {T A₀ C₁ : ℝ}
end Export
end Tail
end Zeta23
end
end

-- Zeta23.Prelude.QZ
section
end

-- Zeta23.Hypotheses
section
open scoped BigOperators ArithmeticFunction ComplexConjugate ContDiff
open Complex MeasureTheory Set
noncomputable section
namespace Zeta23
structure gX : Prop where
  even : ∀ τ : ℝ, mu (-τ) = mu τ
  smooth : ContDiff ℝ ∞ mu
  monotoneOn : MonotoneOn mu (Ici 0)
  GK : ∀ τ : ℝ, mu 0 ≤ mu τ
  qK : -1 < mu 0
  Sz : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
    |mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2
  XS : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| → |deriv mu τ| ≤ C / |τ|
  abx : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(∫ τ in T..(2 * T), mu τ) - T * eD T / (2 * Real.pi)| ≤ C / T
  ZG : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(∫ τ in T..(2 * T), mu τ ^ 2) - T * eD T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ C * (T * eD T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2
end Zeta23
end
end

-- Zeta23.Defs.Counting
section
open Set
noncomputable section
namespace Zeta23.aV
variable (Z : aV) (T₁ T₂ : ℝ)
lemma qX : (Z.window T₁ T₂).Finite := Z.dS T₁ T₂
lemma uj {s t : Set ℂ} (hst : s ⊆ t) (ht : t ⊆ Z.window T₁ T₂) :
    ∑ᶠ ρ ∈ s, Z.mult ρ ≤ ∑ᶠ ρ ∈ t, Z.mult ρ := by
  have htf : t.Finite := (Z.qX T₁ T₂).subset ht
  have hsf : s.Finite := htf.subset hst
  rw [finsum_mem_eq_finite_toFinset_sum _ hsf, finsum_mem_eq_finite_toFinset_sum _ htf]
  apply Finset.sum_le_sum_of_subset
  exact Set.Finite.toFinset_subset_toFinset.mpr hst
end Zeta23.aV
end
end

-- Zeta23.Statement
section
open scoped BigOperators ComplexConjugate
open Complex Set
noncomputable section
namespace Zeta23
def aO (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1
def bY (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat
def JX (T₁ T₂ : ℝ) : Set ℂ := {ρ | aO ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}
def mL (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ JX T₁ T₂, bY ρ
structure gI : Prop where
  one_le_mult : ∀ ρ, aO ρ → 1 ≤ bY ρ
  reflect_zero : ∀ ρ, aO ρ → aO (reflect ρ)
  kT : ∀ ρ, aO ρ → bY (reflect ρ) = bY ρ
  dS : ∀ T₁ T₂ : ℝ, ({ρ | aO ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite
def bT (hs : gI) : aV where
  carrier := {ρ | aO ρ}
  mult := bY
  one_le_mult := hs.one_le_mult
  strip := fun _ h => ⟨h.2.1.le, h.2.2.le⟩
  qH := hs.reflect_zero
  kT := hs.kT
  dS := hs.dS
section SD
variable (hs : gI) (T₁ T₂ : ℝ)
@[simp] lemma Sj : (bT hs).carrier = {ρ | aO ρ} := rfl
@[simp] lemma UR : (bT hs).mult = bY := rfl
@[simp] lemma SH : (bT hs).simple = {ρ | bY ρ = 1} := rfl
lemma Fj : (bT hs).window T₁ T₂ = JX T₁ T₂ := by
  ext ρ; simp [aV.window, JX]
@[simp] lemma EU : (bT hs).N T₁ T₂ = mL T₁ T₂ := by
  simp [aV.N, mL, Fj]
end SD
lemma aO.wW {ρ : ℂ} (h : aO ρ) :
    (¬∃ n : ℕ, ρ = -2 * (n + 1)) ∧ ρ ≠ 1 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨n, rfl⟩
    have := h.2.1
    simp at this
    linarith
  · rintro rfl
    simpa using h.2.2
end Zeta23
end
end

-- Zeta23.Statement.acJ
section
open Complex Set Filter Topology
noncomputable section
namespace Zeta23
lemma cD : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  intro s hs
  exact (differentiableAt_riemannZeta hs).differentiableWithinAt
lemma nZ : IsConnected ({1}ᶜ : Set ℂ) :=
  isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) 1
lemma lU {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ := by
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  refine cD.analyticOrderAt_ne_top_of_isPreconnected
    nZ.isPreconnected h2 hs ?_
  rw [(cD 2 h2).analyticOrderAt_eq_zero.mpr
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num))]
  exact ENat.zero_ne_top
theorem gI.DY : ∀ ρ, aO ρ → 1 ≤ bY ρ := by
  intro ρ h
  have Ml : ρ ≠ 1 := h.wW.2
  have han : AnalyticAt ℂ riemannZeta ρ := cD ρ Ml
  have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 := han.analyticOrderAt_ne_zero.mpr h.1
  have VY := lU Ml
  unfold bY
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp VY
  rw [← hn] at hne0 ⊢
  simp only [ENat.toNat_coe, ne_eq, Nat.cast_eq_zero] at hne0 ⊢
  omega
lemma jg (z : ℂ) :
    ∃ t ∈ 𝓝 z, (t ∩ {ρ : ℂ | ρ ≠ 1 ∧ riemannZeta ρ = 0}).Finite := by
  by_cases hz : z = 1
  · 
    subst hz
    have hres := riemannZeta_residue_one
    have hev : ∀ᶠ s in 𝓝[≠] (1 : ℂ), riemannZeta s ≠ 0 := by
      have : ∀ᶠ s in 𝓝[≠] (1 : ℂ), (s - 1) * riemannZeta s ≠ 0 :=
        hres.eventually_ne one_ne_zero
      exact this.mono fun s hs h => hs (by simp [h])
    rw [eventually_nhdsWithin_iff] at hev
    refine ⟨{s | s ∈ ({1}ᶜ : Set ℂ) → riemannZeta s ≠ 0}, hev, ?_⟩
    refine (Set.finite_empty).subset ?_
    rintro s ⟨hs, hs1, hz⟩
    exact hs hs1 hz
  · have Fk := (cD).eqOn_zero_or_eventually_ne_zero_of_preconnected
      nZ.isPreconnected
    rcases Fk with hzero | Fk
    · exfalso
      have : riemannZeta 2 = 0 := hzero (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ))
      exact riemannZeta_ne_zero_of_one_lt_re (by norm_num) this
    · rw [Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithin] at Fk
      obtain ⟨t, ht, hfin⟩ := Fk z hz
      refine ⟨t, ht, hfin.subset ?_⟩
      rintro s ⟨hst, hs1, hs0⟩
      exact ⟨hst, hs1, by simpa using hs0⟩
theorem gI.Bk (T₁ T₂ : ℝ) :
    ({ρ | aO ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite := by
  set K : Set ℂ := (Icc 0 1) ×ℂ (Icc T₁ T₂) with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  choose t ht hfin using jg
  obtain ⟨I, -, hcover⟩ := hKc.elim_nhds_subcover t (fun z _ => ht z)
  have Yb : (⋃ z ∈ I, (t z ∩ {ρ : ℂ | ρ ≠ 1 ∧ riemannZeta ρ = 0})).Finite :=
    I.finite_toSet.biUnion fun z _ => hfin z
  refine Yb.subset ?_
  rintro ρ ⟨hρ, hT₁, hT₂⟩
  have SI : ρ ∈ K := by
    refine ⟨⟨hρ.2.1.le, hρ.2.2.le⟩, ⟨hT₁.le, hT₂⟩⟩
  obtain ⟨z, hzI, Fo⟩ := mem_iUnion₂.mp (hcover SI)
  exact mem_iUnion₂.mpr ⟨z, hzI, Fo, hρ.wW.2, hρ.1⟩
theorem gI.OY
    (h₁ : ∀ ρ, aO ρ → aO (reflect ρ))
    (h₂ : ∀ ρ, aO ρ → bY (reflect ρ) = bY ρ) : gI :=
  ⟨gI.DY, h₁, h₂, gI.Bk⟩
end Zeta23
end
end

-- Zeta23.XT
section
open Complex
open scoped ComplexConjugate
namespace Zeta23
private lemma wX {s : ℂ} (hs : 1 < s.re) :
    conj (riemannZeta (conj s)) = riemannZeta s := by
  have hs' : (1 : ℝ) < (conj s).re := by rwa [Complex.conj_re]
  rw [zeta_eq_tsum_one_div_nat_cpow hs', zeta_eq_tsum_one_div_nat_cpow hs]
  have hstar : star (∑' (n : ℕ), (1 : ℂ) / (n : ℂ) ^ (conj s))
      = ∑' (n : ℕ), star ((1 : ℂ) / (n : ℂ) ^ (conj s)) := tsum_star
  calc conj (∑' (n : ℕ), (1 : ℂ) / (n : ℂ) ^ (conj s))
      = ∑' (n : ℕ), star ((1 : ℂ) / (n : ℂ) ^ (conj s)) := hstar
    _ = ∑' (n : ℕ), (1 : ℂ) / (n : ℂ) ^ s := by
        congr 1
        funext n
        have harg : ((n : ℂ)).arg ≠ Real.pi := by
          rw [Complex.natCast_arg]
          exact Ne.symm Real.pi_ne_zero
        have hpow : (n : ℂ) ^ (conj s) = conj ((n : ℂ) ^ s) := by
          have h := Complex.cpow_conj (n : ℂ) s harg
          rwa [Complex.conj_natCast] at h
        show star ((1 : ℂ) / (n : ℂ) ^ (conj s)) = 1 / (n : ℂ) ^ s
        rw [star_div₀, star_one, hpow]
        simp
theorem riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have UZ : IsPreconnected ({(1 : ℂ)}ᶜ) :=
    (isPathConnected_compl_singleton_of_one_lt_rank hrank 1).isConnected.isPreconnected
  have hζ : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    exact (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
  have ZQ : AnalyticOnNhd ℂ (fun z => conj (riemannZeta (conj z))) ({(1 : ℂ)}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    have hz1 : conj z ≠ 1 := by
      intro h
      have h2 := congrArg (starRingEnd ℂ) h
      simp only [Complex.conj_conj, map_one] at h2
      exact (by simpa using hz : z ≠ 1) h2
    have hd : DifferentiableAt ℂ riemannZeta (conj z) := differentiableAt_riemannZeta hz1
    have h3 := hd.conj_conj
    rw [Complex.conj_conj] at h3
    exact h3.differentiableWithinAt
  have h2mem : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hagree : (fun z => conj (riemannZeta (conj z))) =ᶠ[nhds (2 : ℂ)] riemannZeta := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by
      simp only [Set.mem_setOf_eq]
      norm_num
    filter_upwards [hopen.mem_nhds h2] with z hz
    exact wX hz
  have heq := ZQ.eqOn_of_preconnected_of_eventuallyEq hζ UZ h2mem hagree
  have h3 : conj (riemannZeta (conj s)) = riemannZeta s := heq (by simpa using hs)
  calc riemannZeta (conj s) = conj (conj (riemannZeta (conj s))) := (Complex.conj_conj _).symm
    _ = conj (riemannZeta s) := by rw [h3]
private lemma lV (w : ℂ) :
    Filter.Tendsto (fun z => conj z) (nhds (conj w)) (nhds w) := by
  have h := (Complex.continuous_conj).tendsto (conj w)
  rwa [Complex.conj_conj] at h
private lemma jU {f : ℂ → ℂ} {w : ℂ} (hf : AnalyticAt ℂ f w) :
    AnalyticAt ℂ (fun z => conj (f (conj z))) (conj w) := by
  rw [analyticAt_iff_eventually_differentiableAt] at hf ⊢
  filter_upwards [(lV w).eventually hf] with z hz
  have h2 := hz.conj_conj
  rw [Complex.conj_conj] at h2
  exact h2
theorem sI (f : ℂ → ℂ) (w : ℂ) :
    analyticOrderAt (fun z => conj (f (conj z))) (conj w) = analyticOrderAt f w := by
  by_cases hf : AnalyticAt ℂ f w
  · by_cases htop : analyticOrderAt f w = ⊤
    · rw [htop, analyticOrderAt_eq_top]
      filter_upwards [(lV w).eventually (analyticOrderAt_eq_top.mp htop)] with z hz
      simp [hz]
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
      rw [← hn]
      rw [Eq.comm, hf.analyticOrderAt_eq_natCast] at hn
      obtain ⟨g, hg, hgne, hfg⟩ := hn
      rw [(jU hf).analyticOrderAt_eq_natCast]
      refine ⟨fun z => conj (g (conj z)), jU hg, by simpa using hgne, ?_⟩
      filter_upwards [(lV w).eventually hfg] with z hz
      have : conj (f (conj z)) = conj ((conj z - w) ^ n * g (conj z)) := by rw [hz]; rfl
      rw [this]
      simp only [map_mul, map_pow, map_sub, Complex.conj_conj]
      rfl
  · have hf' : ¬ AnalyticAt ℂ (fun z => conj (f (conj z))) (conj w) := by
      intro hcon
      apply hf
      have h2 := jU hcon
      rw [Complex.conj_conj] at h2
      exact h2.congr (Filter.Eventually.of_forall fun u => by
        simp only [Complex.conj_conj])
    rw [analyticOrderAt_of_not_analyticAt hf, analyticOrderAt_of_not_analyticAt hf']
theorem sK {w : ℂ} (hw : w ≠ 1) :
    analyticOrderAt riemannZeta (conj w) = analyticOrderAt riemannZeta w := by
  have hne : conj w ≠ 1 := by
    intro h
    have h2 := congrArg (starRingEnd ℂ) h
    simp only [Complex.conj_conj, map_one] at h2
    exact hw h2
  have hcong : (fun z => conj (riemannZeta (conj z))) =ᶠ[nhds (conj w)] riemannZeta := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hne :
      conj w ∈ ({(1 : ℂ)}ᶜ))] with z hz
    rw [riemannZeta_conj (by simpa using hz), Complex.conj_conj]
  calc analyticOrderAt riemannZeta (conj w)
      = analyticOrderAt (fun z => conj (riemannZeta (conj z))) (conj w) :=
        (analyticOrderAt_congr hcong).symm
    _ = analyticOrderAt riemannZeta w := sI _ _
private noncomputable def zP (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)
private lemma wL : (2 * (Real.pi : ℂ)) ≠ 0 := by
  simp only [ne_eq, mul_eq_zero, not_or]
  exact ⟨two_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero⟩
private lemma Mr {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) : zP s ≠ 0 := by
  have hsne : ∀ m : ℕ, s ≠ -m := by
    intro m h
    rw [h] at h0
    simp only [Complex.neg_re, Complex.natCast_re] at h0
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg m))) h0
  have OZ : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero wL]
    exact Complex.exp_ne_zero _
  have hcos : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    intro hc
    rw [Complex.cos_eq_zero_iff] at hc
    obtain ⟨k, hk⟩ := hc
    have hπ : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have h2 : (Real.pi : ℂ) * s = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by
      linear_combination (2 : ℂ) * hk
    have hs_eq : s = ((2 * k + 1 : ℤ) : ℂ) := by
      have h3 := mul_left_cancel₀ hπ h2
      rw [h3]
      push_cast
      ring
    rw [hs_eq, Complex.intCast_re] at h0 h1
    have h0' : (0 : ℤ) < 2 * k + 1 := by exact_mod_cast h0
    have h1' : (2 * k + 1 : ℤ) < 1 := by exact_mod_cast h1
    omega
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hsne
  unfold zP
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero OZ) hΓ) hcos
private lemma GO {s : ℂ} (h0 : 0 < s.re) : AnalyticAt ℂ zP s := by
  have h1 : AnalyticAt ℂ (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ (-z)) s := by
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards with z
    exact (differentiableAt_id.neg).const_cpow (Or.inl wL)
  have h2 : AnalyticAt ℂ Complex.Gamma s := by
    rw [analyticAt_iff_eventually_differentiableAt]
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds h0] with z hz
    refine Complex.differentiableAt_Gamma z fun m => ?_
    intro h
    rw [h] at hz
    simp only [Complex.neg_re, Complex.natCast_re] at hz
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg m))) hz
  have h3 : AnalyticAt ℂ (fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z / 2)) s := by
    have hlin : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) * z / 2) s := by
      apply AnalyticAt.div_const
      exact analyticAt_const.mul analyticAt_id
    exact Complex.analyticAt_cos.comp hlin
  have h4 : AnalyticAt ℂ (fun z : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-z)) s :=
    analyticAt_const.mul h1
  exact (h4.mul h2).mul h3
theorem qv {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    analyticOrderAt riemannZeta (1 - w) = analyticOrderAt riemannZeta w := by
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hev : (riemannZeta ∘ (fun z : ℂ => 1 - z)) =ᶠ[nhds w]
      (zP * riemannZeta) := by
    filter_upwards [hopen.mem_nhds ⟨h0, h1⟩] with z hz
    have hzne : ∀ n : ℕ, z ≠ -n := by
      intro n h
      rw [h] at hz
      simp only [Complex.neg_re, Complex.natCast_re] at hz
      exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))) hz.1
    have Yc : z ≠ 1 := by
      intro h
      rw [h] at hz
      simp only [Complex.one_re] at hz
      exact lt_irrefl 1 hz.2
    show riemannZeta (1 - z) = zP z * riemannZeta z
    rw [riemannZeta_one_sub hzne Yc]
    unfold zP
    ring
  have hg : AnalyticAt ℂ (fun z : ℂ => 1 - z) w := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun z : ℂ => 1 - z) w ≠ 0 := by
    have : deriv (fun z : ℂ => 1 - z) w = -1 := by
      rw [deriv_const_sub]
      simp
    rw [this]
    simp
  have Uj := GO h0
  have Yd : analyticOrderAt zP w = 0 :=
    Uj.analyticOrderAt_eq_zero.mpr (Mr h0 h1)
  calc analyticOrderAt riemannZeta (1 - w)
      = analyticOrderAt (riemannZeta ∘ (fun z : ℂ => 1 - z)) w := by
        rw [analyticOrderAt_comp_of_deriv_ne_zero hg hg']
    _ = analyticOrderAt (zP * riemannZeta) w := analyticOrderAt_congr hev
    _ = analyticOrderAt zP w + analyticOrderAt riemannZeta w := by
        by_cases VZ : AnalyticAt ℂ riemannZeta w
        · exact analyticOrderAt_mul Uj VZ
        · exfalso
          exact VZ (by
            rw [analyticAt_iff_eventually_differentiableAt]
            have hne1 : w ≠ 1 := by
              intro h
              rw [h] at h1
              simp at h1
            filter_upwards [isOpen_compl_singleton.mem_nhds
              (by simpa using hne1 : w ∈ ({(1 : ℂ)}ᶜ))] with z hz
            exact differentiableAt_riemannZeta (by simpa using hz))
    _ = analyticOrderAt riemannZeta w := by rw [Yd, zero_add]
theorem DZ : ∀ ρ, aO ρ → aO (reflect ρ) := by
  rintro ρ ⟨hzero, h0, h1⟩
  have Yf : ∀ n : ℕ, ρ ≠ -n := by
    intro n h
    rw [h] at h0
    simp only [Complex.neg_re, Complex.natCast_re] at h0
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))) h0
  have Wa : ρ ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  have JY : (1 : ℂ) - ρ ≠ 1 := by
    intro h
    have : ρ = 0 := by
      have := congrArg (fun z => (1 : ℂ) - z) h
      simpa using this
    rw [this] at h0
    simp at h0
  have Fv : reflect ρ = conj (1 - ρ) := by
    unfold reflect
    rw [map_sub, map_one]
  constructor
  · 
    rw [Fv, riemannZeta_conj JY, riemannZeta_one_sub Yf Wa, hzero]
    simp
  constructor
  · 
    unfold reflect
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · 
    unfold reflect
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
theorem Eb : ∀ ρ, aO ρ → bY (reflect ρ) = bY ρ := by
  rintro ρ ⟨_, h0, h1⟩
  have JY : (1 : ℂ) - ρ ≠ 1 := by
    intro h
    have Mt : ρ = 0 := by
      have := congrArg (fun z => (1 : ℂ) - z) h
      simpa using this
    rw [Mt] at h0
    simp at h0
  have Fv : reflect ρ = conj (1 - ρ) := by
    unfold reflect
    rw [map_sub, map_one]
  unfold bY
  rw [Fv, sK JY, qv h0 h1]
end Zeta23
end

-- Zeta23.Statement.Yh
section
noncomputable section
namespace Zeta23
theorem Fw : gI := gI.OY DZ Eb
def aE : aV := bT Fw
@[simp] lemma wY : aE.carrier = {ρ | aO ρ} := rfl
@[simp] lemma QY : aE.mult = bY := rfl
@[simp] lemma jV (T₁ T₂ : ℝ) : aE.N T₁ T₂ = mL T₁ T₂ :=
  EU _ _ _
end Zeta23
end
end

-- Zeta23.iQ.Uk
section
open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory
lemma AnalyticOn.jO {C r R : ℝ} {f : ℂ → ℂ} {w : ℂ}
    (LZ : r ≤ R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (cond : ∀ z ∈ Metric.sphere 0 r, ‖f z‖ ≤ C)
    (ZR : w ∈ Metric.closedBall 0 r) :
    ‖f w‖ ≤ C := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := Metric.closedBall 0 r) Metric.isBounded_closedBall
  · apply DifferentiableOn.diffContOnCl
    rw [Metric.closure_closedBall]
    exact AnalyticOn.differentiableOn
      (AnalyticOn.mono analytic
        (Metric.closedBall_subset_closedBall LZ))
  · rw [frontier_closedBall']
    exact cond
  · rw [Metric.closure_closedBall]
    exact ZR
theorem Cv {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (Rpos : 0 < R) (LZ : r < R)
    (analytic : AnalyticOn ℂ f (Metric.ball 0 R))
    (zQ : f 0 = 0)
    (oC : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (GQ : z ∈ Metric.closedBall 0 r) :
    ‖f z‖ ≤ (2 * M * r) / (R - r) := by
  have Bm : ∀ ε > 0, ‖f z‖ ≤ (2 * (M + ε) * ‖z‖) / (R - ‖z‖) := by
    intro ε εpos;
    apply Complex.borelCaratheodory_zero;
    exacts [by linarith, analytic.differentiableOn, fun z hz => by rw [Set.mem_setOf_eq]; linarith [oC z hz], Rpos, by exact Metric.mem_ball.mpr ( lt_of_le_of_lt ( Metric.mem_closedBall.mp GQ ) LZ ), zQ]
  have JZ : ‖f z‖ ≤ (2 * M * ‖z‖) / (R - ‖z‖) := by
    have JZ : Filter.Tendsto (fun ε => (2 * (M + ε) * ‖z‖) / (R - ‖z‖)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 * M * ‖z‖) / (R - ‖z‖))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' ?_ _ _ (by ring_nf))
      exact ((continuous_const.mul (continuous_const.add continuous_id)).mul continuous_const).div_const _
    exact le_of_tendsto_of_tendsto tendsto_const_nhds JZ ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => Bm ε hε );
  rw [mem_closedBall_iff_norm, sub_zero] at GQ
  refine le_trans JZ ?_;
  gcongr
  · exact mul_nonneg (mul_nonneg (zero_le_two) (le_of_lt Mpos)) (le_trans (norm_nonneg z) GQ)
lemma zR {r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Ka : r < r') (DM : r' < R)
    (Pd : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hz : z ∈ Metric.closedBall 0 r) :
    deriv f z = (1 / (2 * Real.pi * I)) • ∮ w in C(0, r'), (w - z)⁻¹ ^ 2 • f w := by
  have Pe : z ∈ Metric.ball 0 r' :=
    Metric.mem_ball.mpr <| (Metric.mem_closedBall.mp hz).trans_lt Ka
  simp [← Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      Metric.isOpen_ball (Metric.closedBall_subset_ball DM) Pd Pe]
lemma GR {M r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (acv : 0 < r) (Ka : r < r') (DM : r' < R)
    (sO : AnalyticOn ℂ f (Metric.ball 0 R))
    (Kd : f 0 = 0)
    (Ra : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (Mv : z ∈ Metric.closedBall 0 r) :
    ‖(deriv f) z‖ ≤ 2 * M * (r') ^ 2 / ((R - r') * (r' - r) ^ 2) := by
  rw [zR Ka DM sO.differentiableOn  Mv, one_div]
  grw [circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by linarith) (C := 2 * M * r' / ((R - r') * (r' - r) ^ 2))]
  · exact le_of_eq (by ring)
  · intro z' hz'
    rw [smul_eq_mul, norm_mul]
    grw[Cv Mpos (by grind) DM sO Kd  Ra
      (Metric.sphere_subset_closedBall hz')]
    suffices ‖(z' - z)⁻¹ ^ 2‖ ≤ 1 / (r' - r) ^ 2 by
      grw [this]
      · exact le_of_eq (by field)
      · refine mul_nonneg (mul_nonneg ?_ ?_) (inv_nonneg.mpr ?_) <;> linarith
    have hdist : r' - r ≤ ‖z' - z‖ := by
      simp only [mem_sphere_iff_norm, sub_zero, Metric.mem_closedBall,
        dist_zero_right] at hz' Mv
      rw [← hz']
      have hzr : ‖z‖ ≤ r := by simpa [Complex.dist_eq] using Mv
      exact le_trans (by linarith) (norm_sub_norm_le z' z)
    rw [norm_pow, norm_inv, one_div, inv_pow]
    gcongr
theorem wZ {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (rpos : 0 < r) (LZ : r < R)
    (sO : AnalyticOn ℂ f (Metric.ball 0 R))
    (zQ : f 0 = 0)
    (oC : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (GQ : z ∈ Metric.closedBall 0 r) :
    ‖deriv f z‖ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
  have hr' : 2 * M * ((R + r) / 2) ^ 2 / ((R - (R + r) / 2) * ((R + r) / 2 - r) ^ 2) =
      4 * M * (R + r) ^ 2 / (R - r) ^ 3 := by field_simp; ring
  calc ‖deriv f z‖
      _ ≤ 4 * M * (R + r) ^ 2 / (R - r) ^ 3 := hr' ▸
          GR Mpos rpos (by linarith) (by linarith) sO zQ oC GQ
      _ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
          have : 16 * M * R ^ 2 = 4 * M * (2 * R) ^ 2 := by ring_nf
          rw [this]; bound
theorem yP {r R : ℝ} {B : ℂ → ℂ}
    (ZH : 0 < r) (r_lt_R : r < R)
    (kV : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (uq : ∀ z ∈ Metric.closedBall (0 : ℂ) R, B z ≠ 0) :
    ∃ (EW : ℂ → ℂ), (AnalyticOnNhd ℂ EW (Metric.ball 0 R)) ∧
      (EW 0 = 0) ∧
      (∀ z ∈ Metric.closedBall 0 r, (deriv EW) z = (deriv B) z / (B z)) ∧
      (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (EW z).re) := by
  obtain ⟨EW, hJB⟩ : ∃ EW : ℂ → ℂ, (∀ z ∈ Metric.ball 0 R, (HasDerivAt EW (deriv B z / B z) z)) ∧ EW 0 = 0 ∧ (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (EW z).re) := by
    set f : ℂ → ℂ := fun z => deriv B z / B z;
    have hf : AnalyticOnNhd ℂ f (Metric.ball 0 R) :=
      (kV.deriv.mono Metric.ball_subset_closedBall).div
        (kV.mono Metric.ball_subset_closedBall)
        (fun z hz => uq z <| Metric.ball_subset_closedBall hz)
    obtain ⟨J, hJ⟩ := DifferentiableOn.isExactOn_ball hf.differentiableOn
    refine ⟨fun z ↦ J z - J 0, fun z hz ↦ (hJ z hz).sub_const _, by simp, ?_⟩
    set H : ℂ → ℂ := fun z => Complex.exp (J z - J 0) / B z
    have Rb : ∀ z ∈ Metric.ball 0 R, HasDerivAt (fun z ↦ J z - J 0) (f z) z :=
      fun z hz ↦ (hJ z hz).sub_const _
    have Mw : ∀ z ∈ Metric.ball 0 R, HasDerivAt H 0 z := by
      intro z hz
      have := (Complex.hasDerivAt_exp _).comp z (Rb z hz)
      convert! this.div (kV.differentiableOn.differentiableAt
        (Metric.closedBall_mem_nhds_of_mem hz) |>.hasDerivAt)
        (uq z <| Metric.ball_subset_closedBall hz) using 1
      ring_nf!; grind
    have SJ : ∀ z ∈ Metric.ball 0 R, H z = H 0 := by
      intro z hz
      have SK : DifferentiableOn ℂ H (Metric.ball 0 R) :=
        fun z hz ↦ (Mw z hz).differentiableAt.differentiableWithinAt
      refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball 0 R) SK ?_ hz
        (Metric.mem_ball_self (Metric.pos_of_mem_ball hz))
      intro x hx
      rw [fderivWithin_of_isOpen Metric.isOpen_ball hx,
        ← ContinuousLinearMap.toSpanSingleton_zero]
      exact (Mw x hx).hasFDerivAt.fderiv
    have SM : ∀ z ∈ Metric.ball 0 R, Real.exp (J z - J 0).re = ‖B z‖ / ‖B 0‖ := by
      intro z hz
      have hc := SJ z hz
      simp only [H, sub_self, Complex.exp_zero, one_div] at hc
      rw [div_eq_iff (uq z (Metric.ball_subset_closedBall hz)), mul_comm] at hc
      rw [← Complex.norm_exp, ← norm_div, div_eq_mul_inv]
      exact enorm_eq_iff_norm_eq.mp (congrArg enorm hc)
    intro z hz
    have hBz := uq z (Metric.ball_subset_closedBall hz)
    have hB0 := uq 0 (by norm_num; linarith)
    rw [← Real.log_div (norm_ne_zero_iff.mpr hBz) (norm_ne_zero_iff.mpr hB0),
      ← SM z hz, Real.log_exp]
  have hmem : ∀ z, z ∈ Metric.ball (0 : ℂ) r → z ∈ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    apply Metric.mem_closedBall.mpr
    rw [Metric.mem_ball] at hz
    linarith
  refine ⟨EW, ?_, hJB.2.1, ?_, hJB.2.2⟩
  · intro z hz
    exact DifferentiableOn.analyticAt (fun w hw ↦ (hJB.1 w hw).differentiableAt.differentiableWithinAt) (IsOpen.mem_nhds Metric.isOpen_ball hz)
  · intro z hz
    exact (hJB.1 z (Metric.closedBall_subset_ball r_lt_R hz)).deriv
def bC (R : ℝ) (f : ℂ → ℂ) : Set ℂ := {ρ : ℂ | ‖ρ‖ ≤ R ∧ f ρ = 0}
lemma aP {r : ℝ} {f : ℂ → ℂ}
    (gJ : r < 1)
    (cW : (bC 1 f).Finite) :
    (bC r f).Finite := by
  apply Set.Finite.subset cW
  unfold bC
  refine setOf_subset_setOf.mpr ?_
  intro z hz
  exact ⟨by linarith, hz.2⟩
open Classical
noncomputable def sP (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if h1 : AnalyticAt ℂ f z then
    if h2 : analyticOrderAt f z ≠ ⊤ then
      (h1.analyticOrderAt_ne_top.mp h2).choose z
    else 0
  else 0
lemma rS {R : ℝ} {f : ℂ → ℂ} {ρ : ℂ}
    (aby : R < 1)
    (eO : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (cO : f 0 ≠ 0)
    (hρ : ρ ∈ bC R f) :
    ∃ Fy : ℂ → ℂ, AnalyticAt ℂ Fy ρ ∧ Fy ρ ≠ 0 ∧ sP f ρ = Fy ρ ∧
      f =ᶠ[nhds ρ] fun z ↦ (z - ρ) ^ analyticOrderNatAt f ρ * Fy z := by
  have Bp : 0 ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw[mem_closedBall_iff_norm, sub_zero, norm_zero]
    exact zero_le_one
  have rT : ρ ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw[mem_closedBall_iff_norm, sub_zero]
    linarith[hρ.1]
  have Ec : analyticOrderAt f 0 = 0 := by
    rw[analyticOrderAt_eq_zero]
    exact Or.symm (Decidable.not_or_of_imp fun a a_1 ↦ cO a)
  have xd : analyticOrderAt f ρ ≠ ⊤ := by
    refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected eO (Metric.isPreconnected_closedBall) Bp rT (lt_top_iff_ne_top.mp ?_)
    rw[Ec]
    exact ENat.top_pos
  have qZ : AnalyticAt ℂ f ρ := by exact (eO ρ rT)
  obtain ⟨Fy, yQ, f_eq⟩ := (qZ.analyticOrderAt_ne_top.mp xd).choose_spec
  set g := (qZ.analyticOrderAt_ne_top.mp xd).choose
  refine ⟨g, Fy, yQ, ?_, f_eq⟩
  simp only [sP, qZ, ↓reduceDIte, ne_eq, xd, not_false_eq_true,
    smul_eq_mul, g]
noncomputable def Cf (r : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if bR : (bC r f).Finite then
    if _ : z ∈ bC r f then
      sP f z / ∏ ρ ∈ (bR.toFinset \ {z}), (z - ρ) ^ (analyticOrderNatAt f ρ)
    else
      f z / ∏ ρ ∈ (bR.toFinset), (z - ρ) ^ (analyticOrderNatAt f ρ)
  else 1
lemma jt (s : Finset ℂ) (g : ℂ → ℕ) (w : ℂ) :
    AnalyticAt ℂ (fun z => ∏ ρ ∈ s, (z - ρ) ^ g ρ) w := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact analyticAt_const
  | @insert a s' hne ih =>
    have : (fun z => ∏ ρ ∈ insert a s', (z - ρ) ^ g ρ) = fun z => (z - a) ^ g a * ∏ ρ ∈ s', (z - ρ) ^ g ρ :=
      funext fun z => Finset.prod_insert hne
    rw [this]
    exact ((analyticAt_id.sub analyticAt_const).pow _).mul ih
lemma sW {r R : ℝ} {f : ℂ → ℂ}
    (r_lt_R : r < R) (kW : R < 1)
    (eO : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (cO : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (Cf r f) (Metric.closedBall (0 : ℂ) R) := by
  intro w hw
  unfold Cf
  by_cases bR : (bC r f).Finite
  · simp only [bR, ↓reduceDIte]
    by_cases oD : w ∈ bC r f
    · obtain ⟨ZI, Aw, Kh, OC⟩ := rS (by linarith) (eO.mono (Metric.closedBall_subset_closedBall (by linarith))) cO oD;
      have h_eq : ∀ᶠ z in nhds w, (if h : z ∈ bC r f then sP f z / ∏ ρ ∈ bR.toFinset \ {z}, (z - ρ) ^ analyticOrderNatAt f ρ else f z / ∏ ρ ∈ bR.toFinset, (z - ρ) ^ analyticOrderNatAt f ρ) = ZI z / ∏ ρ ∈ bR.toFinset \ {w}, (z - ρ) ^ analyticOrderNatAt f ρ := by
        filter_upwards [ OC.2, Aw.continuousAt.eventually_ne Kh ] with z hz hz';
        by_cases h : z = w
        · subst h
          rw [dif_pos oD]
          congr 1
          exact OC.1
        · have SN : z ∉ bC r f := by
            intro hmem
            have hfz : f z = 0 := hmem.2
            rw [hz] at hfz
            exact absurd hfz (mul_ne_zero (pow_ne_zero _ (sub_ne_zero_of_ne h)) hz')
          rw [dif_neg SN, hz]
          have Wb : w ∈ bR.toFinset := bR.mem_toFinset.mpr oD
          rw [Finset.prod_eq_prod_sdiff_singleton_mul Wb (fun ρ => (z - ρ) ^ analyticOrderNatAt f ρ)]
          rw [mul_comm ((z - w) ^ analyticOrderNatAt f w) (ZI z)]
          rw [mul_div_mul_right _ _ (pow_ne_zero _ (sub_ne_zero_of_ne h))]
      apply Aw.div _ _ |> fun h => h.congr _;
      · use fun z => ∏ ρ ∈ bR.toFinset \ { w }, ( z - ρ ) ^ analyticOrderNatAt f ρ;
      · exact jt _ _ _
      · simp only [Finset.prod_eq_zero_iff, ne_eq, pow_eq_zero_iff', Finset.mem_sdiff, Finite.mem_toFinset, Finset.mem_singleton, not_exists, not_and,
          Decidable.not_not, and_imp]
        intro x _ Wd
        exact fun Wf => absurd (sub_eq_zero.mp Wf).symm Wd
      · filter_upwards [ h_eq ] with z hz using hz.symm
    · apply AnalyticAt.congr _ _
      · exact fun z => f z / ∏ ρ ∈ bR.toFinset, ( z - ρ ) ^ analyticOrderNatAt f ρ
      · refine AnalyticAt.div ?_ ?_ ?_
        · exact eO w ( Metric.mem_closedBall.mpr <| le_trans hw.out <| by linarith )
        · exact jt _ _ _
        · simp only [ ne_eq, Finset.prod_eq_zero_iff, Finite.mem_toFinset, pow_eq_zero_iff',
          sub_eq_zero, ↓existsAndEq, true_and, not_and, Decidable.not_not]
          exact fun h => absurd h oD
      · filter_upwards [ IsOpen.mem_nhds ( isOpen_compl_iff.mpr bR.isClosed ) oD ] with z hz
        split_ifs with h
        · exact absurd h hz
        · rfl
  · simp only [bR, ↓reduceDIte]
    exact analyticAt_const
noncomputable def kZ (r R : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if bR : (bC r f).Finite then
    (Cf r f) z * (∏ ρ ∈ bR.toFinset, (R - z * (conj ρ) / R) ^ (analyticOrderNatAt f ρ))
  else 1
lemma Fz {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (kW : R < 1)
    (cW : (bC 1 f).Finite)
    (eO : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (cO : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (kZ r R f) (Metric.closedBall (0 : ℂ) R) := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have gJ : r < 1 := lt_trans r_lt_R kW
  unfold kZ
  by_cases bR : (bC r f).Finite
  · simp only [bR, ↓reduceDIte]
    refine AnalyticOnNhd.mul (sW r_lt_R kW eO cO) (Finset.analyticOnNhd_fun_prod (aP gJ cW).toFinset ?_)
    intro w hw
    refine AnalyticOnNhd.fun_pow (AnalyticOnNhd.sub (analyticOnNhd_const) (AnalyticOnNhd.div (AnalyticOnNhd.mul (analyticOnNhd_id) (analyticOnNhd_const)) (analyticOnNhd_const) ?_)) (analyticOrderAt f w).toNat
    intro w' hw'
    exact_mod_cast ne_of_gt R_pos
  · simp only [bR, ↓reduceDIte]
    exact analyticOnNhd_const
lemma Kj {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (gJ : r < 1) (r_lt_R : r < R)
    (cW : (bC 1 f).Finite)
    (cO : f 0 ≠ 0) :
    ‖kZ r R f 0‖ =
      ‖f 0‖ * (∏ ρ ∈ (aP gJ cW).toFinset, (R / ‖ρ‖) ^ (analyticOrderNatAt f ρ)) := by
  have LJ : ¬(0 ∈ bC r f) := by
    apply notMem_setOf_iff.mpr
    simp only [norm_zero, not_and]
    intro r
    exact mem_support.mp cO
  unfold kZ Cf
  simp only [aP gJ cW, LJ, ↓reduceDIte, zero_sub, zero_mul, zero_div, sub_zero,
    Complex.norm_mul, Complex.norm_div, norm_prod, norm_pow, norm_neg, norm_real, norm_eq_abs]
  rw[div_eq_mul_inv, mul_assoc, abs_of_pos (by linarith)]
  refine (mul_right_inj' (norm_ne_zero_iff.mpr cO)).mpr ?_
  rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  simp only [div_eq_inv_mul, mul_pow, inv_pow]
lemma Rd {B r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (kW : R < 1)
    (cW : (bC 1 f).Finite)
    (eO : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (cO : f 0 ≠ 0) (FH : ∀ (z : ℂ), ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ‖kZ r R f z‖ ≤ B := by
  have gJ : r < 1 := lt_trans r_lt_R kW
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  refine AnalyticOn.jO (Std.IsPreorder.le_refl R) (AnalyticOnNhd.analyticOn (Fz r_pos r_lt_R kW cW eO cO)) ?_ hz
  intro w hw
  rw[mem_sphere_iff_norm, sub_zero] at hw
  have Lk : ¬(w ∈ bC r f) := by
    apply notMem_setOf_iff.mpr
    intro acK
    linarith
  have Mz : ‖kZ r R f w‖ = ‖f w‖ := by
    unfold kZ Cf
    simp only [aP gJ cW, Lk, ↓reduceDIte, Complex.norm_mul, Complex.norm_div, norm_prod, norm_pow]
    rw[div_eq_mul_inv, mul_assoc, mul_right_eq_self₀]
    by_cases Ob : ‖f w‖ = 0
    · exact Or.inr Ob
    · apply Or.inl
      rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro w' Rg
      have hfact : (R : ℂ) - w * starRingEnd ℂ w' / R = (conj w - conj w') * w / R := by
        rw[sub_mul, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hw, ofReal_pow]
        field_simp
      rw [hfact, norm_div, norm_mul, ← map_sub, norm_conj, Complex.norm_real, hw, Real.norm_of_nonneg (le_of_lt R_pos)]
      field_simp
      rw[← div_pow, div_self, one_pow]
      rw[Set.Finite.mem_toFinset] at Rg
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun h => Lk (h ▸ Rg)))
  rw[Mz]
  exact FH w (le_of_eq hw)
theorem zS {B r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (gJ : r < 1) (r_lt_R : r < R) (kW : R < 1)
    (eO : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (GS : f 0 = 1)
    (cW : (bC 1 f).Finite) (FH : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∑ ρ ∈ (aP gJ cW).toFinset, analyticOrderNatAt f ρ ≤
      1 / Real.log (R / r) * Real.log B := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have xB : f 0 ≠ 0 := by rw [GS]; exact one_ne_zero
  have EY := Kj r_pos gJ r_lt_R cW xB
  rw[GS, norm_one, one_mul] at EY
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (Real.log_pos (by simp only [lt_div_iff₀ r_pos, one_mul, r_lt_R])), ← Real.log_pow]
  refine Real.log_le_log (pow_pos (div_pos R_pos r_pos) _) ?_
  calc (R / r) ^ ∑ ρ ∈ (aP gJ cW).toFinset, analyticOrderNatAt f ρ
      = ∏ ρ ∈ (aP gJ cW).toFinset, (R / r) ^ analyticOrderNatAt f ρ := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ ρ ∈ (aP gJ cW).toFinset, (R / ‖ρ‖) ^ analyticOrderNatAt f ρ := by
      apply Finset.prod_le_prod
      · intro ρ _
        exact pow_nonneg (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) _
      · intro ρ hρ
        have OD := (aP gJ cW).mem_toFinset.mp hρ
        refine pow_le_pow_left₀ (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) ?_ _
        refine div_le_div_of_nonneg_left (le_of_lt R_pos) (norm_pos_iff.mpr ?_) (OD.1)
        rintro rfl
        exact xB OD.2
    _ ≤ B := by
      rw[← EY]
      exact Rd r_pos r_lt_R kW cW eO
        xB FH (Metric.mem_closedBall_self (le_of_lt R_pos))
end

-- Zeta23.iQ.Auxiliary
section
namespace Complex
end Complex
lemma DifferentiableAt.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z :=
  hf.hasDerivAt.comp_ofReal.differentiableAt
lemma DifferentiableAt.ofReal_comp {z : ℝ} {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z :=
  hf.hasDerivAt.ofReal_comp.differentiableAt
lemma Differentiable.ofReal_comp {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) :=
  fun _ ↦ hf.differentiableAt.ofReal_comp
open Complex ContinuousLinearMap in
lemma HasDerivAt.tj {z : ℝ} {f : ℝ → ℝ} {u : ℂ}
    (hf : HasDerivAt (fun y ↦ (f y : ℂ)) u z) :
    ∃ u' : ℝ, u = u' ∧ HasDerivAt f u' z := by
  lift u to ℝ
  · have H := (imCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt.deriv
    simp only [Function.comp_def, imCLM_apply, ofReal_im, deriv_const] at H
    rwa [eq_comm, comp_apply, imCLM_apply, toSpanSingleton_apply_one] at H
  refine ⟨u, rfl, ?_⟩
  convert! (reCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt
  rw [comp_apply, toSpanSingleton_apply_one, reCLM_apply, ofReal_re]
lemma DifferentiableAt.oF {z : ℝ} {f : ℝ → ℝ} :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z ↔ DifferentiableAt ℝ f z := by
  refine ⟨fun H ↦ ?_, ofReal_comp⟩
  obtain ⟨u, _, hu₂⟩ := H.hasDerivAt.tj
  exact HasDerivAt.differentiableAt hu₂
lemma Differentiable.oF {f : ℝ → ℝ} :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) ↔ Differentiable ℝ f :=
  forall_congr' fun _ ↦ DifferentiableAt.oF
lemma deriv.ofReal_comp {z : ℝ} {f : ℝ → ℝ} :
    deriv (fun (y : ℝ) ↦ (f y : ℂ)) z = deriv f z := by
  by_cases hf : DifferentiableAt ℝ f z
  · exact hf.hasDerivAt.ofReal_comp.deriv
  · have hf' := mt DifferentiableAt.oF.mp hf
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hf',
      Complex.ofReal_zero]
end

-- Zeta23.iQ.Sobolev
section
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
 structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun
structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1
structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)
abbrev OE := W1 2 ℂ
section lemmas
lemma GU : ContDiff ℝ ∞ ofReal := by
  have key x : HasDerivAt ofReal 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const
end lemmas
namespace CS
variable {f : CS n E} {R x v : ℝ}
instance abz : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun
instance abA : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  GU.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩
lemma continuous (f : CS n E) : Continuous f := f.h1.continuous
noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv
lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt
end CS
namespace trunc
instance abB : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun
instance abC : Coe trunc (CS 2 ℝ) where coe := trunc.toCS
end trunc
namespace W1
instance abD : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun
lemma continuous (f : W1 n E) : Continuous f := f.smooth.continuous
lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)
noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)
lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  f.differentiable.differentiableAt.hasDerivAt
lemma nT {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih => simpa [iteratedDeriv_succ'] using! ih (f := SchwartzMap.derivCLM ℝ ℂ f)
noncomputable def Oc (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := nT
end W1
namespace OE
variable {f : OE}
noncomputable instance abf : Coe 𝓢(ℝ, ℂ) OE where coe := W1.Oc
def Yj (f : CS 2 ℂ) : OE := by
  refine ⟨f, f.h1, fun k hk => ?_⟩ ; match k with
  | 0 => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1 => simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv
instance abg : Coe (CS 2 ℂ) OE where coe := Yj
end OE
end

-- Zeta23.iQ.Fourier
section
open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators
local instance abh {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
section lemmas
end lemmas
end

-- Zeta23.iQ.Mathlib.Analysis.SpecialFunctions.Log.Basic
section
open Filter Real
end

-- Zeta23.iQ.Rectangle
section
open Complex Set Topology
open scoped Interval
variable {z w : ℂ} {c : ℝ}
namespace Rectangle
end Rectangle
def aZ (z w : ℂ) : Set ℂ :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]
theorem Set.Ee {a b : ℝ} : a ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (left_lt_sup.mp h2) (le_of_not_ge (inf_lt_left.mp h1))
theorem Set.Cw {a b : ℝ} : b ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (right_lt_sup.mp h2) (le_of_not_ge (inf_lt_right.mp h1))
theorem Set.pQ {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ a :=
  fun h ↦ Set.Ee (h ▸ hc)
theorem Set.oG {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ b :=
  fun h ↦ Set.Cw (h ▸ hc)
lemma jc (z w : ℂ) : aZ z w ⊆ Rectangle z w := by
  intro x hx
  obtain ⟨⟨h | h⟩ | h⟩ | h := hx
  · exact ⟨h.1, h.2 ▸ left_mem_uIcc⟩
  · exact ⟨h.1 ▸ left_mem_uIcc, h.2⟩
  · exact ⟨h.1, h.2 ▸ right_mem_uIcc⟩
  · exact ⟨h.1 ▸ right_mem_uIcc, h.2⟩
lemma lW {z w p : ℂ}
    (h : p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im) :
    Disjoint (aZ z w) {p} := by
  refine disjoint_singleton_right.mpr ?_
  simp_rw [aZ, Set.mem_union, not_or]
  exact ⟨⟨⟨fun hc ↦ h.2.2.1 hc.2, fun hc ↦ h.1 hc.1⟩, fun hc ↦ h.2.2.2 hc.2⟩,
    fun hc ↦ h.2.1 hc.1⟩
lemma gY {z w p : ℂ} :
    Rectangle z w ∈ 𝓝 p ↔ p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by
  simp_rw [← mem_interior_iff_mem_nhds, Rectangle, Complex.interior_reProdIm, uIoo, uIcc,
    interior_Icc]
lemma oH (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (aZ z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, aZ]
lemma oz (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (aZ z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, aZ]
lemma oI (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (aZ z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, aZ]
lemma oA (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (aZ z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, aZ]
theorem dG {z w p : ℂ}
    (hp : Rectangle z w ∈ 𝓝 p) :
    p ∉ aZ z w := by
  refine Set.disjoint_right.mp (lW ?_) rfl
  have h1 := gY.mp hp
  exact ⟨Set.pQ h1.1, Set.oG h1.1,
    Set.pQ h1.2, Set.oG h1.2⟩
end

-- Zeta23.iQ.Oa
section
open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics
open scoped Interval
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ} {x x₁ x₂ y y₁ y₂ σ : ℝ}
noncomputable def iw (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    ∫ x in x₁..x₂, f (x + y * I)
noncomputable def ju (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    I • ∫ y in y₁..y₂, f (x + y * I)
noncomputable def aY (f : ℂ → E) (z w : ℂ) : E :=
    iw f z.re w.re z.im - iw f z.re w.re w.im +
    ju f w.re z.im w.im - ju f z.re z.im w.im
noncomputable abbrev bF (f : ℂ → E) (z w : ℂ) : E :=
    (1 / (2 * π * I)) • aY f z w
abbrev iG (f : ℂ → E) (s : Set ℂ) : Prop :=
    DifferentiableOn ℂ f s
theorem iG.Bq [CompleteSpace E]
    {U : Set ℂ} (Wg : iG f U)
    (hU : Rectangle z w ⊆ U) :
    aY f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (Wg.mono hU)
theorem wc (h : Set.EqOn f g (aZ z w)) :
    aY f z w = aY g z w := by
  unfold aY ju
  congrm ?_ - ?_ + I • ?_ - I • ?_
  all_goals refine integral_congr fun _ _ ↦ h ?_
  · exact Or.inl <| Or.inl <| Or.inl ⟨by simpa, by simp⟩
  · exact Or.inl <| Or.inr ⟨by simpa, by simp⟩
  · exact Or.inr ⟨by simp, by simpa⟩
  · exact Or.inl <| Or.inl <| Or.inr ⟨by simp, by simpa⟩
theorem uO (h : Set.EqOn f g (aZ z w)) :
    bF f z w = bF g z w := by
  rw [bF, wc h]
def cQ (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im
theorem cQ.add {f g : ℂ → E}
    (hf : cQ f z w) (hg : cQ g z w) :
    aY (f + g) z w = aY f z w + aY g z w := by
  dsimp [aY, iw, ju]
  have h₁ := intervalIntegral.integral_add hf.1 hg.1
  have h₂ := intervalIntegral.integral_add hf.2.1 hg.2.1
  have h₃ := intervalIntegral.integral_add hf.2.2.1 hg.2.2.1
  have h₄ := intervalIntegral.integral_add hf.2.2.2 hg.2.2.2
  rw [h₁, h₂, h₃, h₄]
  module
omit [NormedSpace ℂ E] in
theorem ContinuousOn.ko (hf : ContinuousOn f (aZ z w)) :
    cQ f z w :=
  ⟨(hf.comp (by fun_prop) (oI z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (oA z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (oz z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (oH z w)).intervalIntegrable⟩
theorem aY.translate (f : ℂ → E) (z w p : ℂ) :
    aY (fun s => f (s - p)) z w = aY f (z - p) (w - p) := by
  simp_rw [aY, iw, ju, sub_re, sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  congr <;> ext <;> congr 1 <;> simp [Complex.ext_iff]
theorem aY.Pq (f : ℂ → E) (z w p : ℂ) :
    bF (fun s => f (s - p)) z w = bF f (z - p) (w - p) := by
  simp_rw [bF, aY.translate]
lemma Complex.LL : (x + y * I)⁻¹ = (x - I * y) / (x ^ 2 + y ^ 2) := by
  rw [Complex.inv_def, div_eq_mul_inv]
  congr <;> simp [conj_ofReal, normSq] <;> ring
lemma sq_add_sq_ne_zero (hy : y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  linarith [sq_nonneg x, sq_pos_iff.mpr hy]
lemma jK (hy : y ≠ 0) :
    Continuous fun x => x / (x ^ 2 + y ^ 2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const) (fun _ => sq_add_sq_ne_zero hy)
lemma qL (hy : y ≠ 0) :
    ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
    Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  let f (x : ℝ) : ℝ := Real.log (x ^ 2 + y ^ 2) / 2
  have e1 {x} := HasDerivAt.add_const (y ^ 2) (by simpa using hasDerivAt_pow 2 x)
  have e2 {x} : HasDerivAt f (x / (x ^ 2 + y ^ 2)) x := by
    convert! (e1.log (sq_add_sq_ne_zero hy)).div_const 2 using 1
    field_simp
  have e3 : deriv f = fun x => x / (x ^ 2 + y ^ 2) := funext (fun _ => e2.deriv)
  have e4 : Continuous (deriv f) := by simpa only [e3] using jK hy
  simp_rw [← e2.deriv]
  exact integral_deriv_eq_sub (fun _ _ => e2.differentiableAt) (e4.intervalIntegrable _ _)
lemma qw (hy : y ≠ 0) :
    ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) = Real.arctan (x₂ / y) - Real.arctan (x₁ / y) := by
  nth_rewrite 1 [← div_mul_cancel₀ x₁ hy, ← div_mul_cancel₀ x₂ hy]
  simp_rw [← mul_integral_comp_mul_right, ← intervalIntegral.integral_const_mul,
    ← integral_one_div_one_add_sq]
  exact integral_congr fun x _ => by
    field_simp
    ring
lemma gN (hy : y ≠ 0) :
    ∫ x : ℝ in x₁..x₂, A / (x + y * I) =
    A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2) -
    A * I * (Real.arctan (x₂ / y) - Real.arctan (x₁ / y)) := by
  have e1 {x : ℝ} : A / (x + y * I) = A * x / (x ^ 2 + y ^ 2) - A * I * y / (x ^ 2 + y ^ 2) := by
    ring_nf
    simp_rw [LL]
    ring
  have e2 : IntervalIntegrable (fun x ↦ A * x / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc]
    norm_cast
    exact continuous_const.mul (continuous_ofReal.comp (jK hy))
  have e3 : IntervalIntegrable (fun x ↦ A * I * y / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) (fun x => ?_)
    norm_cast
    exact sq_add_sq_ne_zero hy
  simp_rw [integral_congr (fun _ _ => e1), integral_sub e2 e3, mul_div_assoc]
  norm_cast
  simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    qL hy, qw hy]
lemma jv (hx : x ≠ 0) :
    ∫ y : ℝ in y₁..y₂, A / (x + y * I) =
    A / I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 - Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
    A / I * I * (Real.arctan (y₂ / -x) - Real.arctan (y₁ / -x)) := by
  have l1 {y : ℝ} : A / (x + y * I) = A / I / (y + ↑(-x) * I) := by
    have e1 : x + y * I ≠ 0 := by
      contrapose! hx
      simpa using congr_arg re hx
    have e2 : y + I * ↑(-x) ≠ 0 := by
      contrapose! hx
      simpa using congr_arg im hx
    field_simp [*]
    push_cast
    ring_nf
    simp
  have l2 : -x ≠ 0 := by rwa [neg_ne_zero]
  simp_rw [l1, gN l2]
lemma wA {z w c : ℂ}
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    aY (fun s => c / s) z w = 2 * I * π * c := by
  simp only [aY, iw, ju, smul_eq_mul]
  rw [jv h1.ne, jv h3.ne.symm]
  rw [gN h2.ne, gN h4.ne.symm]
  have l1 : z.im * w.re⁻¹ = (w.re * z.im⁻¹)⁻¹ := by group
  have l3 := arctan_inv_of_neg <| mul_neg_of_pos_of_neg h3 <| inv_lt_zero.mpr h2
  have l4 : w.im * z.re⁻¹ = (z.re * w.im⁻¹)⁻¹ := by group
  have l6 := arctan_inv_of_neg <| mul_neg_of_neg_of_pos h1 <| inv_pos.mpr h4
  have r1 : z.im * z.re⁻¹ = (z.re * z.im⁻¹)⁻¹ := by group
  have r3 := arctan_inv_of_pos <| mul_pos_of_neg_of_neg h1 <| inv_lt_zero.mpr h2
  have r4 : w.im * w.re⁻¹ = (w.re * w.im⁻¹)⁻¹ := by group
  have r6 := arctan_inv_of_pos <| mul_pos h3 <| inv_pos.mpr h4
  ring_nf
  simp only [one_div, inv_I, mul_neg, neg_mul, I_sq, neg_neg, arctan_neg, ofReal_neg,
    sub_neg_eq_add]
  rw [l1, l3, l4, l6, r1, r3, r4, r6]
  ring_nf
  simp only [I_sq, ofReal_sub, ofReal_mul, ofReal_ofNat, ofReal_div, ofReal_neg, ofReal_one]
  ring_nf
theorem tq
    (Pv : z.re ≤ w.re) (Pw : z.im ≤ w.im)
    (GW : Rectangle z w ∈ 𝓝 p) :
    bF (fun s => c / (s - p)) z w = c := by
  simp only [gY, uIoo_of_le Pv, uIoo_of_le Pw,
    mem_reProdIm, mem_Ioo] at GW
  rw [aY.Pq, bF]
  have : 1 / (2 * ↑π * I) * (2 * I * ↑π * c) = c := by
    field_simp
  rwa [wA]
  all_goals simp [*]
lemma Cz {f : ℂ → ℂ} {p : ℂ}
    (ME : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by
  simp only [isBigO_iff, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at ME
  obtain ⟨c, hc⟩ := ME
  dsimp [Filter.Eventually, nhdsWithin] at hc
  rw [mem_inf_principal'] at hc
  obtain ⟨U, hU, ⟨Rh, Wh⟩⟩ := mem_nhds_iff.mp hc
  use U
  constructor
  · exact IsOpen.mem_nhds Rh Wh
  · refine bddAbove_def.mpr ?_
    use c
    intro y hy
    simp only [Function.comp_apply, mem_image, Set.mem_sdiff, mem_singleton_iff] at hy
    obtain ⟨x, ⟨x_in_U, Vc⟩, fxy⟩ := hy
    rw [← fxy]
    simpa [Vc] using hU x_in_U
end

-- Zeta23.iQ.Vd
section
 public section
open Finset Interval MeasureTheory
variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}
noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2
lemma lP : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop
lemma Kk {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]
lemma qz (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp
lemma oB (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by first | exact RCLike.continuous_ofReal.comp_aestronglyMeasurable lP | exact (RCLike.continuous_ofReal.comp_aestronglyMeasurable lP).restrict) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact Kk (by linarith)
lemma nU (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (oB ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [qz _ hab h_cont.intervalIntegrable hf_diff]
theorem lX (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [nU ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring
end

-- Zeta23.iQ.Yk
section
open Complex Topology Filter Interval Set Asymptotics
lemma oK (a x s : ℂ) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, cpow_neg]
lemma zU (a x s : ℝ) (hx : 0 ≤ x) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, Real.rpow_neg hx]
noncomputable def iz (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)
lemma CJ (N : ℕ) (s : ℂ) : (iz) N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) := by
  simp_rw [iz, oK]; ring
lemma Real.mO (s : ℂ) {x : ℝ} (xpos : 0 < x) :
    DifferentiableAt ℝ (fun (x : ℝ) ↦ (x : ℂ) ^ s) x := by
  apply DifferentiableAt.comp_ofReal (e := fun z ↦ z ^ s)
  apply DifferentiableAt.cpow (by simp) (by simp) (by simp [xpos])
lemma Complex.GZ {s : ℂ} {x : ℝ} (x_ne : x ≠ 0) :
    1 / (x : ℂ) ^ s = (x : ℂ) ^ (-s) := by
  refine (eq_one_div_of_mul_eq_one_left ?_).symm
  rw [← cpow_add _ _ <| mod_cast x_ne, neg_add_cancel, cpow_zero]
lemma FI {φ : ℝ → ℂ} {a b : ℝ} (apos : 0 ≤ a) (a_lt_b : a < b)
    (HW : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (xG : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, φ n =
      (∫ x in a..b, φ x) + (⌊b⌋₊ + 1 / 2 - b) * φ b - (⌊a⌋₊ + 1 / 2 - a) * φ a
        - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  rw [uIcc_of_le a_lt_b.le] at HW
  convert lX apos a_lt_b.le (fun t ht ↦ (HW t ht).differentiableAt) xG using 1
  unfold B1
  push_cast
  suffices ∫ (x : ℝ) in a..b, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x = -∫ (t : ℝ) in a..b, deriv φ t * (↑t - ↑⌊t⌋₊ - 1 / 2) by
    rw [this]
    ring_nf!
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x hx ↦ ?_
  rw [uIcc_of_le a_lt_b.le, mem_Icc] at hx
  rw [← Int.natCast_floor_eq_floor (by linarith)]
  norm_cast
  push_cast
  ring
lemma lA {a b : ℕ} (ha : a ∈ Ioo 0 b) {x : ℝ} (x_in : x ∈ [[(a : ℝ), b]]) :
    0 < x := by
  rw [uIcc_of_le (by exact_mod_cast ha.2.le), mem_Icc] at x_in
  linarith [(by exact_mod_cast ha.1 : (0 : ℝ) < a)]
lemma Ie {a b : ℕ} {s : ℂ} (lB : s ≠ 1) (ha : a ∈ Ioo 0 b) :
    (∫ (x : ℝ) in a..b, 1 / (x : ℂ) ^ s) =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by
  convert integral_cpow (a := a) (b := b) (r := -s) ?_ using 1
  · refine intervalIntegral.integral_congr fun x hx ↦ GZ ?_
    exact (lA ha hx).ne'
  · norm_cast; ring_nf
  · right; refine ⟨(by grind), ?_⟩
    exact fun hx ↦ (lt_self_iff_false 0).mp <| lA ha hx
lemma CQ {s : ℂ} {x : ℝ} (xpos : 0 < x) :
    HasDerivAt (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x) x := by
  exact hasDerivAt_deriv_iff.mpr <|
    DifferentiableAt.div (differentiableAt_const _)
      (Real.mO s xpos) (by simp [cpow_eq_zero_iff, xpos.ne'])
lemma pU {s : ℂ} (jw : s ≠ 0) {x : ℝ} (xpos : 0 < x) :
    deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x = (fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))) x := by
  let r := -s - 1
  have yT : r + 1 ≠ 0 := fun hr ↦ by simp [neg_ne_zero.mpr jw, r] at hr
  have Ri : r ≠ -1 := fun hr ↦ (hr ▸ yT) <| by norm_num
  have MG := hasDerivAt_ofReal_cpow_const' xpos.ne' Ri
  have := MG.deriv ▸ deriv_const_mul (-s) (MG).differentiableAt
  convert! this using 2
  · ext y
    by_cases y_zero : (y : ℂ) = 0
    · simp only [y_zero, ne_eq, jw, not_false_eq_true, zero_cpow, div_zero,
      yT, zero_div, mul_zero]
    · have : (y : ℂ) ^ s ≠ 0 := fun hy ↦ y_zero ((cpow_eq_zero_iff _ _).mp hy).1
      simp only [one_div, sub_add_cancel, cpow_neg, neg_mul, r]
      field_simp
  · simp only [r]
    ring_nf
lemma wB {s : ℂ} (jw : s ≠ 0) {a b : ℕ} (ha : a ∈ Ioo 0 b) :
    ContinuousOn (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s)) [[a, b]] := by
  have : EqOn _ (fun (t : ℝ) ↦ -s * (t : ℂ) ^ (-(s + 1))) [[a, b]] :=
    fun x hx ↦ pU jw <| lA ha hx
  refine continuous_ofReal.continuousOn.cpow_const ?_ |>.const_smul (c := -s) |>.congr this
  exact fun x hx ↦ ofReal_mem_slitPlane.mpr <| lA ha hx
lemma MH {a b : ℕ} {s : ℂ} (lB : s ≠ 1) (jw : s ≠ 0) (ha : a ∈ Ioo 0 b) :
    ∑ n ∈ Finset.Ioc a b, 1 / (n : ℂ) ^ s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / b ^ (s)) - 1 / 2 * (1 / a ^ s)
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  let φ := fun (x : ℝ) ↦ 1 / (x : ℂ) ^ s
  let φ' := fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))
  have xpos : ∀ x ∈ [[(a : ℝ), b]], 0 < x := fun x hx ↦ lA ha hx
  have HW : ∀ x ∈ [[(a : ℝ), b]], HasDerivAt φ (deriv φ x) x :=
    fun x hx ↦ CQ (xpos x hx)
  have OH : ∀ x ∈ [[(a : ℝ), b]], deriv φ x = φ' x := by
    exact fun x hx ↦ pU jw (xpos x hx)
  have xG : ContinuousOn (deriv φ) [[a, b]] := wB jw ha
  convert FI (by linarith) (by exact_mod_cast ha.2) HW xG using 1
  · congr <;> simp only [Nat.floor_natCast]
  · rw [Nat.floor_natCast, Nat.floor_natCast, ← intervalIntegral.integral_const_mul]
    simp_rw [mul_div, ← mul_div, φ, Ie lB ha]
    conv => rhs; rw [sub_eq_add_neg]
    congr; any_goals norm_cast; simp only [one_div, add_sub_cancel_left]
    rw [← intervalIntegral.integral_neg, intervalIntegral.integral_congr]
    simp only [φ, one_div] at OH
    intro x hx; simp_rw [OH x hx, φ']; ring_nf
lemma oL {a b x : ℝ} (apos : 0 < a) (hx : x ∈ Icc a b) : 0 < x :=
  lt_of_lt_of_le apos hx.1
lemma qA {a b x : ℝ} (apos : 0 < a) (a_lt_b : a < b) (hx : x ∈ [[a, b]]) : 0 < x :=
  lt_of_lt_of_le apos (uIcc_of_le a_lt_b.le ▸ hx).1
lemma Km {a b : ℝ} {c : ℝ} (apos : 0 < a) (a_lt_b : a < b)
    (h : c ≠ 0 ∧ 0 ∉ [[a, b]]) :
    ∫ (x : ℝ) in a..b, 1 / x ^ (c+1) = (a ^ (-c) - b ^ (-c)) / c := by
  rw [(by ring : (a ^ (-c) - b ^ (-c)) / c = (b ^ (-c) - a ^ (-c)) / (-c))]
  have := integral_rpow (a := a) (b := b) (r := -c-1) (Or.inr ⟨by simp [h.1], h.2⟩)
  simp only [sub_add_cancel] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro x hx
  have : 0 ≤ x := (qA apos a_lt_b hx).le
  simp [zU _ _ _ this, sub_eq_add_neg, add_comm]
lemma lN (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2 :=
  abs_le.mpr ⟨(by linarith [Int.lt_floor_add_one x]), (by linarith [Int.floor_le x])⟩
lemma Ih (x : ℝ) (hx : 0 < x) (s : ℂ) :
      ‖(⌊x⌋ + 1 / 2 - (x : ℝ)) / (x : ℂ) ^ (s + 1)‖ =
      ‖⌊x⌋ + 1 / 2 - x‖ / x ^ ((s + 1).re) := by
  simp_rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, ← norm_real]
  simp
lemma Kp {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} :
  ∫ (x : ℝ) in a..b, ‖(↑⌊x⌋ + (1 : ℝ) / 2 - ↑x) / (x : ℂ) ^ (s + 1)‖ =
    ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s + 1).re := by
  apply intervalIntegral.integral_congr
  exact fun x hx ↦ Ih x (qA apos a_lt_b hx) s
lemma Ij {a b : ℝ} (apos : 0 < a) {s : ℂ} (x : ℝ)
  (h : x ∈ Icc a b) : |↑⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤ 1 / x ^ (s.re + 1) := by
  apply div_le_div_of_nonneg_right _ _
  · exact le_trans (lN x) (by norm_num)
  · apply Real.rpow_nonneg <| le_of_lt (oL apos h)
lemma wM {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (nO : 0 < s.re) :
  IntervalIntegrable (fun u ↦ 1 / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  refine continuousOn_const.div ?_ ?_ |>.intervalIntegrable_of_Icc (le_of_lt a_lt_b)
  · exact continuousOn_id.rpow_const fun x hx ↦ Or.inl (ne_of_gt <| oL apos hx)
  · exact fun x hx h ↦ by rw [Real.rpow_eq_zero] at h <;> linarith [oL apos hx]
open MeasureTheory in
lemma pJ : Measurable fun (u : ℝ) ↦ ↑⌊u⌋ + 1 / 2 - u := by
  refine Measurable.add ?_ measurable_const |>.sub measurable_id
  exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor
open MeasureTheory in
lemma Io {a b : ℝ} {s : ℂ} :
    let g : ℝ → ℝ := fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1);
    AEStronglyMeasurable g
      (Measure.restrict volume (Ι a b)) := by
  intro
  refine (Measurable.div ?_ <| measurable_id.pow_const _).aestronglyMeasurable
  exact _root_.continuous_abs.measurable.comp pJ
lemma Ip {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (nO : 0 < s.re) :
  IntervalIntegrable (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  set g : ℝ → ℝ := (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1))
  apply wM apos a_lt_b nO |>.mono_fun Io ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, one_div, norm_inv, abs_div, _root_.abs_abs]
  conv => rw [div_eq_mul_inv, ← one_div]; rhs; rw [← one_mul |x ^ (s.re + 1)|⁻¹]
  refine mul_le_mul ?_ (le_refl _) (by simp) <| by norm_num
  exact le_trans (lN x) <| by norm_num
lemma Kq {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (nO : 0 < s.re) :
  ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤
    ∫ (x : ℝ) in a..b, 1 / x ^ (s.re + 1) := by
  apply intervalIntegral.integral_mono_on (le_of_lt a_lt_b) ?_ ?_
  · exact Ij apos
  · exact Ip apos a_lt_b nO
  · exact wM apos a_lt_b nO
lemma LO {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (nO : 0 < s.re) :
    ∫ x in a..b, ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      (a ^ (-s.re) - b ^ (-s.re)) / s.re := by
  calc
    _ = ∫ x in a..b, |(⌊x⌋ + 1 / 2 - x)| / x ^ (s+1).re := Kp apos a_lt_b
    _ ≤ ∫ x in a..b, 1 / x ^ (s.re + 1) := Kq apos a_lt_b nO
    _ = (a ^ (-s.re) - b ^ (-s.re)) / s.re := ?_
  refine Km (c := s.re) apos a_lt_b ⟨ne_of_gt nO, ?_⟩
  exact fun h ↦ (lt_self_iff_false 0).mp <| qA apos a_lt_b h
lemma Finset.Py (M N : ℕ) : Finset.Ioc N M = Finset.Ico (N + 1) (M + 1) := by
  ext a; simp only [Finset.mem_Ioc, Finset.mem_Ico]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega
lemma xO {N : ℕ} {f : ℕ → ℂ} (hf : Summable f) :
    Tendsto (fun (k : ℕ) ↦ ∑ n ∈ Finset.Ico N k, f n) atTop (𝓝 (∑' (n : ℕ), f (n + N))) := by
  have := Summable.hasSum_iff_tendsto_nat hf (m := ∑' (n : ℕ), f n) |>.mp hf.hasSum
  have const := tendsto_const_nhds (α := ℕ) (x := ∑ i ∈ Finset.range N, f i) (f := atTop)
  have := Filter.Tendsto.sub this const
  rw [← hf.sum_add_tsum_nat_add N, add_comm, add_sub_cancel_right] at this
  apply this.congr'
  filter_upwards [Filter.mem_atTop (N + 1)]
  intro M hM
  rw [Finset.sum_Ico_eq_sub]
  linarith
lemma Complex.MJ {s : ℂ} (jP : 1 < s.re) :
    Tendsto (fun (x : ℕ) ↦ (x : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  have Iq : (1 - s).re ≠ 0 := by simp only [sub_re, one_re]; linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (Iq)]
  rw [(by simp only [sub_re, one_re, neg_sub] : (1 - s).re = - (s - 1).re)]
  apply (tendsto_rpow_neg_atTop _).comp tendsto_natCast_atTop_atTop; simp [jP]
lemma Complex.FJ {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun (x : ℕ) ↦ ((x : ℂ) ^ s)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_inv, Complex.norm_natCast_cpow_of_re_ne_zero _ <| ne_of_gt hs]
  apply Filter.Tendsto.inv_tendsto_atTop
  exact (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
lemma AH : ∃ C, ∀ (x : ℝ), ‖⌊x⌋ + 1 / 2 - x‖ ≤ C := by
  use 1 / 2; exact lN
lemma ML {N : ℕ} {s : ℂ} (jP : 1 < s.re) :
    Tendsto (fun k ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) atTop
    (𝓝 (∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s)) := by
  let f := fun (n : ℕ) ↦ 1 / (n : ℂ) ^ s
  have hf := summable_one_div_nat_cpow.mpr jP
  simp_rw [Finset.Py]
  convert xO (f := fun n ↦ f (n + 1)) (N := N) ?_ using 1
  · ext k
    rw [Finset.sum_Ico_add']
  · congr; ext n; simp only [one_div, Nat.cast_add, Nat.cast_one, f]
  · rwa [summable_nat_add_iff (k := 1)]
lemma gd {N : ℕ} (N_pos : 0 < N) {s : ℂ} (jP : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N)
    MeasureTheory.volume := by
  obtain ⟨c, hc⟩ := AH
  apply MeasureTheory.Integrable.bdd_mul (c := c) ?_ ?_
  · apply MeasureTheory.ae_of_all
    convert hc; simp only [← Complex.norm_real]; simp
  · apply integrableOn_Ioi_cpow_iff (by positivity) |>.mpr (by simp [jP])
  · refine Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor
lemma MO {N : ℕ} (N_pos : 0 < N) {s : ℂ} (jP : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  have jw : s ≠ 0 := fun hs ↦ by linarith [zero_re ▸ hs ▸ jP]
  have lB : s ≠ 1 := fun hs ↦ (lt_self_iff_false _).mp <| one_re ▸ hs ▸ jP
  apply tendsto_nhds_unique (X := ℂ) (Y := ℕ) (l := atTop)
    (f := fun k ↦ ((k : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) +
      1 / 2 * (1 / ↑k ^ s) - 1 / 2 * (1 / ↑N ^ s)
      + s * ∫ (x : ℝ) in (N : ℝ)..k, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
    (b := (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
  · apply Filter.Tendsto.congr'
      (f₁ := fun (k : ℕ) ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) (l₁ := atTop)
    · apply Filter.eventually_atTop.mpr
      use N + 1
      intro k hk
      exact MH (a := N) (b := k) lB jw ⟨N_pos, hk⟩
    · exact ML jP
  · apply (Tendsto.sub ?_ ?_).add (Tendsto.const_mul _ ?_)
    · rw [(by ring : -↑N ^ (1 - s) / (1 - s) = (0 - ↑N ^ (1 - s)) / (1 - s) + 0)]
      apply MJ jP |>.sub_const _ |>.div_const _ |>.add
      simp_rw [mul_comm_div, one_mul, one_div, (by congr; ring : 𝓝 (0 : ℂ) = 𝓝 ((0 : ℂ) / 2))]
      apply Tendsto.div_const <| FJ (by positivity)
    · simp_rw [mul_comm_div, one_mul, one_div, cpow_neg]; exact tendsto_const_nhds
    · exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := N)
        (b := (fun (n : ℕ) ↦ (n : ℝ)))
        (gd N_pos <| by positivity) tendsto_natCast_atTop_atTop
open MeasureTheory in
lemma LQ (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (nO : 0 < σ) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ N ^ (-σ) / σ := by
  apply le_trans (by apply norm_integral_le_integral_norm)
  apply le_of_tendsto (x := atTop (α := ℝ)) (f := fun (t : ℝ) ↦ ∫ (x : ℝ) in N..t,
    ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) ?_ ?_
  · apply intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := atTop) (b := id)
      (f := fun (x : ℝ) ↦ ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) N ?_ ?_ |>.congr' ?_
    · filter_upwards [Filter.mem_atTop ((N : ℝ))]
      intro u hu
      simp only [id_eq, intervalIntegral.integral_of_le hu, norm_div]
      apply setIntegral_congr_fun (by simp)
      intro x hx; beta_reduce
      iterate 2 (rw [norm_cpow_eq_rpow_re_of_pos (by linarith [hx.1])])
      simp
    · apply IntegrableOn.integrable ?_ |>.norm
      convert! gd (s := σ + t * I) Npos (by simp [nO]) using 1
      simp_rw [div_eq_mul_inv, cpow_neg]
    · exact fun ⦃_⦄ a ↦ a
  · filter_upwards [mem_atTop (N + 1 : ℝ)] with t ht
    have : (N ^ (-σ) - t ^ (-σ)) / σ ≤ N ^ (-σ) / σ :=
      div_le_div_iff_of_pos_right nO |>.mpr (by simp [Real.rpow_nonneg (by linarith)])
    apply le_trans ?_ this
    convert! LO (a := N) (b := t) (by positivity) (by linarith) ?_ <;> simp [nO]
lemma Iv : IsOpen {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  refine IsOpen.inter isOpen_ne ?_
  exact isOpen_lt (g := fun (z : ℂ) ↦ z.re) (by continuity) (by continuity)
open MeasureTheory in
lemma lQ {r : ℝ} (rneg : r < 0) {N : ℕ} (Npos : 0 < N) :
    IntegrableOn (fun (x : ℝ) ↦ ‖x ^ (r - 1)‖ * ‖Real.log x‖) <| Ioi N := by
  apply IntegrableOn.mono_set (hst := Set.Ioi_subset_Ici <| le_refl (N : ℝ))
  apply LocallyIntegrableOn.integrableOn_of_isBigO_atTop (g := fun x ↦ x ^ (r / 2 - 1))
  · apply ContinuousOn.abs ?_ |>.mul ?_ |>.locallyIntegrableOn (by simp)
    · apply ContinuousOn.rpow (by fun_prop) (by fun_prop)
      intro x hx; left; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
    · apply continuous_id.continuousOn.log ?_ |>.abs
      intro x hx; simp only [id_eq]; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
  · have := isLittleO_log_rpow_atTop (r := -r / 2) (by linarith) |>.isBigO
    rw [Asymptotics.isBigO_iff_eventually, Filter.eventually_atTop] at this
    obtain ⟨C, hC⟩ := this
    have hh := hC C (by simp)
    rw [Asymptotics.isBigO_atTop_iff_eventually_exists]
    have := Filter.eventually_atTop.mp hh
    obtain ⟨x₀, hx₀ ⟩ := this
    filter_upwards [hh, Filter.mem_atTop x₀, Filter.mem_atTop 1]
    intro x hx acL x_pos
    use C
    intro y hy
    simp only [norm_mul, Real.norm_eq_abs, _root_.abs_abs]
    simp only [Real.norm_eq_abs] at hx
    have y_pos : 0 < y := by linarith
    have : y ^ (r / 2 - 1) = y ^ (r - 1) * y ^ (-r / 2) := by
      rw [← Real.rpow_add y_pos]; ring_nf
    rw [this, abs_mul]
    have ZS : y ≥ x₀ := by linarith
    have := hx₀ y ZS
    simp only [Real.norm_eq_abs] at this
    rw [← mul_assoc, mul_comm C, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbc := this) (a := |y ^ (r - 1)|) (ha := by simp)
  · have := integrableOn_Ioi_rpow_iff (s := r / 2 - 1) (t := N) (by simp [Npos]) |>.mpr
      (by linarith [rneg])
    exact integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp this |>.1
open MeasureTheory in
lemma pL {N : ℕ} (Npos : 0 < N) {s : ℂ} (jP : 0 < s.re) :
    IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) * (-Real.log x)) (Ioi N)
    volume := by
  simp_rw [mul_assoc]
  obtain ⟨c, hc⟩ := AH
  apply Integrable.bdd_mul (c := c) ?_ ?_ ?_
  · simp only [neg_add_rev, mul_neg, add_comm, ← sub_eq_add_neg]
    apply integrable_norm_iff ?_ |>.mp ?_ |>.neg
    · apply ContinuousOn.mul ?_ ?_ |>.aestronglyMeasurable (by simp)
      · intro x hx
        apply ContinuousWithinAt.cpow ?_ continuous_const.continuousWithinAt ?_
        · exact RCLike.continuous_ofReal.continuousWithinAt
        · simp only [ofReal_mem_slitPlane]; linarith [mem_Ioi.mp hx]
      · apply RCLike.continuous_ofReal.continuousOn.comp ?_ (mapsTo_image _ _)
        refine continuous_id.continuousOn.log ?_
        intro x hx; simp only [id_eq]; linarith [mem_Ioi.mp hx]
    · simp only [norm_mul, norm_real]
      have := lQ (r := -s.re) (by linarith) Npos
      apply IntegrableOn.congr_fun this ?_ (by simp)
      intro x hx
      simp only [mul_eq_mul_right_iff, norm_eq_zero, Real.log_eq_zero]
      left
      have xpos : 0 < x := by linarith [mem_Ioi.mp hx]
      simp [norm_cpow_eq_rpow_re_of_pos xpos, Real.abs_rpow_of_nonneg xpos.le,
        abs_eq_self.mpr xpos.le]
  · apply Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (fun _ _ ↦ trivial) Int.measurable_floor
  · apply MeasureTheory.ae_of_all
    convert hc with _ x; simp only [← Complex.norm_real]; simp
open MeasureTheory in
lemma uW {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : s ∈ {s | 0 < s.re}) :
  HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
    (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by
  simp only [mem_setOf_eq] at hs
  set f : ℝ → ℂ := fun x ↦ (⌊x⌋ : ℂ) + 1 / 2 - x
  set F : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * f x
  set F' : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * (- Real.log x) * f x
  set ε := s.re / 2
  have ε_pos : 0 < ε := by aesop
  set bound : ℝ → ℝ := fun x ↦ |x ^ (- s.re / 2 - 1)| * |Real.log x|
  let μ : Measure ℝ := volume.restrict (Ioi (N : ℝ))
  have hF_meas : ∀ᶠ (z : ℂ) in 𝓝 s, AEStronglyMeasurable (F z) μ := by
    have : {z : ℂ | 0 < z.re} ∈ 𝓝 s := by
      rw [mem_nhds_iff]
      refine ⟨{z | 0 < z.re}, fun ⦃a⦄ a ↦ a, isOpen_lt continuous_const Complex.continuous_re, hs⟩
    filter_upwards [this] with z hz
    convert! gd Npos hz |>.aestronglyMeasurable using 1
    simp only [F, f]; ext x; ring_nf
  have hF_int : Integrable (F s) μ := by
    convert! gd Npos hs |>.integrable using 1
    simp only [F, f]; ext x; ring_nf
  have hF'_meas : AEStronglyMeasurable (F' s) μ := by
    convert! pL Npos hs |>.aestronglyMeasurable using 1
    simp only [F', f]; ext x; ring_nf
  have Iw : (Ioi (N : ℝ)) ⊆ {x | 1 < x} :=
      fun x hx ↦ lt_of_le_of_lt (by simp only [Nat.one_le_cast]; omega) <| mem_Ioi.mp hx
  have EZ : MeasurableSet {x : ℝ | 1 < x} := (isOpen_lt' 1).measurableSet
  have MQ :
    ∀ᵐ (x : ℝ) ∂volume.restrict {x | 1 < x}, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    filter_upwards [self_mem_ae_restrict EZ] with x hx
    intro z hz
    simp only [F', f, bound]
    calc _ = ‖(x : ℂ) ^ (-z - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := by
            simp only [mul_neg, one_div, neg_mul, norm_neg, norm_mul, norm_real, Real.norm_eq_abs,
              ← (by simp : (((⌊x⌋ + 2⁻¹ - x) : ℝ) : ℂ) = (⌊x⌋ : ℂ) + 2⁻¹ - ↑x),
              Complex.norm_real]
         _ = ‖x ^ (-z.re - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := ?_
         _ = |x ^ (-z.re - 1)| * |(Real.log x)| * |(⌊x⌋ + 1 / 2 - x)| := by simp
         _ ≤ _ := ?_
    · congr! 2
      simp only [Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos (by linarith),
        sub_re, neg_re, one_re]
      apply abs_eq_self.mpr ?_ |>.symm
      positivity
    · rw [mul_comm, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right ?_ <| abs_nonneg _
      simp only [Metric.mem_ball, ε, Complex.dist_eq] at hz
      apply le_trans (b := 1 * |x ^ (-z.re - 1)|)
      · apply mul_le_mul_of_nonneg_right (le_trans (lN _) (by norm_num)) <| abs_nonneg _
      · simp_rw [one_mul, Real.abs_rpow_of_nonneg (by linarith : 0 ≤ x)]
        apply Real.rpow_le_rpow_of_exponent_le <| le_abs.mpr (by left; exact hx.le)
        have := abs_le.mp <| le_trans (abs_re_le_norm (z-s)) hz.le
        simp only [sub_re, neg_le_sub_iff_le_add, tsub_le_iff_right] at this
        linarith [this.1]
  have h_bound : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    apply ae_restrict_of_ae_restrict_of_subset Iw
    exact MQ
  have bound_integrable : Integrable bound μ := by
    simp only [bound]
    convert! lQ (r := -s.re / 2) (by linarith) Npos using 0
  have h_diff : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, HasDerivAt (fun w ↦ F w x) (F' z x) z := by
    simp only [F, F', f]
    apply ae_restrict_of_ae_restrict_of_subset Iw
    filter_upwards [MQ, self_mem_ae_restrict EZ] with x _ ZT
    intro z hz
    convert! HasDerivAt.mul_const (c := fun (w : ℂ) ↦ (x : ℂ) ^ (-w-1))
      (c' := (x : ℂ) ^ (-z-1) * -Real.log x) (d := (⌊x⌋ : ℝ) + 1 / 2 - x) ?_ using 1
    convert! HasDerivAt.comp (h := fun w ↦ -w-1) (h' := -1) (h₂ := fun w ↦ x ^ w)
      (h₂' := x ^ (-z-1) * Real.log x) (x := z) ?_ ?_ using 0
    · simp only [mul_neg, mul_one]; congr! 2
    · convert! HasDerivAt.const_cpow (c := (x : ℂ)) (f := fun w ↦ w) (f' := 1) (x := -z-1)
        (hasDerivAt_id _) ?_ using 1
      · simp only [mul_one, mul_eq_mul_left_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq]
        left
        rw [Complex.ofReal_log]
        linarith
      · right
        intro h
        simp only [Metric.mem_ball, ε, Complex.dist_eq,
          neg_eq_iff_eq_neg.mp <| sub_eq_zero.mp h] at hz
        have := (abs_le.mp <| le_trans (abs_re_le_norm (-1-s)) hz.le).1
        simp only [sub_re, neg_re, one_re, neg_le_sub_iff_le_add, le_neg_add_iff_add_le] at this
        linarith
    · apply hasDerivAt_id _ |>.neg |>.sub_const
  convert! (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (x₀ := s)
    (s := Metric.ball s ε) (bound := bound) (μ := μ) (Metric.ball_mem_nhds s ε_pos)
    hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2 using 3
  · ext a; simp only [one_div, F, f]; ring_nf
  · simp only [one_div, mul_neg, neg_mul, neg_inj, F', f]; ring_nf
noncomputable def Rj (N : ℕ) (s : ℂ) : ℂ :=
    ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))
lemma tw {N : ℕ} (Npos : 0 < N) (s : ℂ) :
    HasDerivAt (fun x : ℂ ↦ -(N : ℂ) ^ (-x) / 2) (-((- Real.log N) * (N : ℂ) ^ (-s)) / 2) s := by
  convert! hasDerivAt_neg' s |>.const_cpow (c := N) (by aesop) |>.neg |>.div_const _ using 1
  simp [mul_comm]
lemma uY (N : ℕ) {z : ℂ} (z_ne_zero : z ≠ 0) :
    HasDerivAt (fun z ↦ -(N : ℂ) ^ z / z)
      (((N : ℂ) ^ z / z ^ 2) - (Real.log N * N ^ z / z)) z := by
  simp_rw [div_eq_mul_inv]
  convert! HasDerivAt.mul (c := fun z ↦ - (N : ℂ) ^ z) (d := fun z ↦ z⁻¹)
    (c' := - (N : ℂ) ^ z * Real.log N)
    (d' := - (z ^ 2)⁻¹) ?_ ?_ using 1
  · simp only [natCast_log, neg_mul, mul_neg, neg_neg]
    ring_nf
  · simp only [natCast_log, neg_mul]
    apply HasDerivAt.neg
    convert! HasDerivAt.const_cpow (c := (N : ℂ)) (f := id) (f' := 1) (x := z) (hasDerivAt_id z)
      (by simp [z_ne_zero]) using 1
    simp only [id_eq, mul_one]
  · exact hasDerivAt_inv z_ne_zero
lemma Iz {N : ℕ} (Npos : 0 < N) {s : ℂ} (Kr : 0 < s.re) (lB : s ≠ 1) :
    HasDerivAt ((iz) N) (Rj N s) s := by
  unfold iz Rj
  apply HasDerivAt.fun_sum ?_ |>.add ?_ |>.add ?_ |>.add ?_
  · intro n _
    convert! hasDerivAt_neg' s |>.const_cpow (c := n) (by aesop) using 1
    all_goals (ring_nf; simp [cpow_neg])
  · convert! HasDerivAt.comp (h₂ := fun z ↦ -(N : ℂ) ^ z / z) (h := fun z ↦ 1 - z) (h' := -1)
      (h₂' := ((N : ℂ) ^ (1 - s) / (1 - s) ^ 2 - Real.log (N : ℝ) * (N : ℂ) ^ (1 - s) / (1 - s)))
      (x := s) ?_ ?_ using 1
    · ring_nf
    · exact uY N (by rw [sub_ne_zero]; exact lB.symm)
    · convert! hasDerivAt_const s _ |>.sub (hasDerivAt_id _) using 1; simp
  · convert! tw Npos s using 1; simp only [natCast_log, neg_mul, neg_neg]
  · simp_rw [oK, neg_add, ← sub_eq_add_neg]
    convert! hasDerivAt_id s |>.mul <| uW Npos Kr using 1
lemma rD {N : ℕ} (N_pos : 0 < N) :
    iG ((iz) N) {s : ℂ | s ≠ 1 ∧ 0 < s.re} :=
  fun _ ⟨hs₁, hs₂⟩ ↦ (Iz N_pos hs₂ hs₁).differentiableAt.differentiableWithinAt
lemma tA :
    iG (riemannZeta) {s : ℂ | s ≠ 1} := by
  intro z hz
  simp only [mem_setOf_eq] at hz
  exact (differentiableAt_riemannZeta hz).differentiableWithinAt
lemma Br : IsPathConnected {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  use (2 : ℂ)
  constructor
  · simp
  intro w hw; simp only [ne_eq, mem_setOf_eq] at hw
  by_cases MS : w.im = 0
  · apply JoinedIn.trans (y := 1 + I)
    · let f : ℝ → ℂ := fun t ↦ (1 + I) * t + 2 * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re, one_re,
        I_re, add_zero, ofReal_re, one_mul, add_im, one_im, I_im, zero_add, ofReal_im, mul_zero,
        sub_zero, re_ofNat, sub_re, im_ofNat, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      refine ⟨?_, by linarith⟩
      intro h
      rw [Complex.ext_iff] at h; simp [(by apply And.right; simpa [MS] using h : x = 0)] at h
    · let f : ℝ → ℂ := fun t ↦ w * t + (1 + I) * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re,
        ofReal_re, ofReal_im, mul_zero, sub_zero, one_re, I_re, add_zero, sub_re, one_mul, add_im,
        one_im, I_im, zero_add, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      simp only [mem_setOf_eq]
      constructor
      · intro h
        refine hw.1 ?_
        rw [Complex.ext_iff] at h
        have : x = 1 := by linarith [(by apply And.right; simpa [MS] using h : 1 - x = 0)]
        rw [Complex.ext_iff, one_re, one_im]; exact ⟨by simpa [this, MS] using h, MS⟩
      · by_cases hxx : x = 0
        · simp only [hxx]; linarith
        · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
          have : 0 ≤ 1 - x := by linarith
          have := hw.2
          positivity
  · let f : ℝ → ℂ := fun t ↦ w * t + 2 * (1 - t)
    have cont : Continuous f := by continuity
    apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
    simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re, ofReal_re,
      ofReal_im, mul_zero, sub_zero, re_ofNat, sub_re, one_re, im_ofNat, sub_im, one_im, sub_self,
      f]
    intro x hx; simp only [mem_Icc] at hx
    constructor
    · intro h
      rw [Complex.ext_iff] at h;
      simp [(by apply And.right; simpa [MS] using h : x = 0)] at h
    · by_cases hxx : x = 0
      · simp only [hxx]; linarith
      · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
        have : 0 ≤ 1 - x := by linarith
        have := hw.2
        positivity
lemma Od {N : ℕ} (N_pos : 0 < N) {s : ℂ} (Kr : 0 < s.re) (lB : s ≠ 1) :
    (iz) N s = riemannZeta s := by
  let f := riemannZeta
  let g := (iz) N
  let U := {z : ℂ | z ≠ 1 ∧ 0 < z.re}
  have f_an : AnalyticOnNhd ℂ f U := by
    apply (tA.analyticOnNhd isOpen_ne).mono
    simp only [ne_eq, setOf_subset_setOf, and_imp, U]
    exact fun a ha _ ↦ ha
  have g_an : AnalyticOnNhd ℂ g U := (rD N_pos).analyticOnNhd Iv
  have Ve : IsPreconnected U := by
    apply IsConnected.isPreconnected
    apply (IsOpen.isConnected_iff_isPathConnected Iv).mpr Br
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have s_mem : s ∈ U := by simp [U, Kr, lB]
  convert (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq f_an g_an Ve h2 ?_ s_mem).symm
  have u_mem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) := by
    apply mem_nhds_iff.mpr
    use {z : ℂ | 1 < z.re}
    simp only [setOf_subset_setOf, imp_self, forall_const, mem_setOf_eq, re_ofNat,
      Nat.one_lt_ofNat, and_true, true_and]
    exact isOpen_lt (by continuity) (by continuity)
  filter_upwards [u_mem]
  intro z hz
  simp only [f,g, zeta_eq_tsum_one_div_nat_cpow hz, CJ]
  nth_rewrite 2 [neg_div]
  rw [← sub_eq_add_neg, ← MO N_pos hz,
    ← (summable_one_div_nat_cpow.mpr hz).sum_add_tsum_nat_add (N + 1)]
  norm_cast
open ArithmeticFunction (vonMangoldt)
end

-- Zeta23.kB.Yl
section
open Complex Set MeasureTheory Real
noncomputable section
namespace Zeta23
namespace kB
theorem tB {S : Set ℂ} (hS : (1 : ℂ) ∉ S) :
    AnalyticOnNhd ℂ riemannZeta S := by
  have h : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt) isOpen_compl_singleton
  exact h.mono (Set.subset_compl_singleton_iff.mpr hS)
theorem jL {s : ℂ} (hσ : 0 < s.re) (hs : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ / s.re := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hσ
  have hint := LQ 1 le_rfl (σ := s.re) (t := s.im) hσ
  rw [re_add_im] at hint
  simp only [Nat.cast_one, Real.one_rpow] at hint
  rw [← Od (N := 1) one_pos hσ hs]
  simp only [iz, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Complex.zero_cpow hs0, Nat.cast_one, Complex.one_cpow, div_one, div_zero, zero_add]
  set J := ∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ (s + 1) with hJ
  calc ‖(1 : ℂ) + -1 / (1 - s) + -1 / 2 + s * J‖
      = ‖(1 / 2 : ℂ) + -(1 / (1 - s)) + s * J‖ := by ring_nf
    _ ≤ ‖(1 / 2 : ℂ)‖ + ‖-(1 / (1 - s))‖ + ‖s * J‖ := norm_add₃_le
    _ = 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ * ‖J‖ := by
        simp [norm_neg]
    _ ≤ 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ * (1 / s.re) := by gcongr
    _ = 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ / s.re := by ring
theorem tD {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hσ : δ ≤ s.re)
    (ht : 1 ≤ |s.im|) : ‖riemannZeta s‖ ≤ (5 / 2 + δ⁻¹) * |s.im| := by
  have CX : 0 < s.re := lt_of_lt_of_le hδ hσ
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at ht
  have h := jL CX hs1
  have him : |s.im| ≤ ‖1 - s‖ := by
    simpa using Complex.abs_im_le_norm (1 - s)
  have h1 : 1 / ‖1 - s‖ ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have h2 : ‖s‖ / s.re ≤ 1 + δ⁻¹ * |s.im| := by
    have hn : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos CX] at hn
    calc ‖s‖ / s.re ≤ (s.re + |s.im|) / s.re := by gcongr
      _ = 1 + |s.im| / s.re := by field_simp
      _ ≤ 1 + |s.im| / δ := by gcongr
      _ = 1 + δ⁻¹ * |s.im| := by rw [div_eq_inv_mul]
  have h3 : (5 / 2 : ℝ) ≤ 5 / 2 * |s.im| := by nlinarith
  nlinarith [h, h1, h2, h3]
theorem Oe {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re → 1 ≤ |s.im| → ‖riemannZeta s‖ ≤ C * |s.im| := by
  refine ⟨5 / 2 + δ⁻¹, by positivity, fun s hσ ht => tD hδ hσ ht⟩
theorem Bv :
    ∃ A C : ℝ, 0 < C ∧ ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ A := by
  obtain ⟨C, hC, h⟩ := Oe (δ := 1 / 4) (by norm_num)
  refine ⟨1, C, hC, fun s h₁ _ h₃ => ?_⟩
  simpa [Real.rpow_one] using h s h₁ h₃
theorem zV (s : ℂ) (hσ : (0.15 : ℝ) ≤ s.re) (h1 : 1 ≤ ‖s - 1‖) :
    ‖riemannZeta s‖ ≤ 20 / 3 * (|s.im| + 3) ^ (1 : ℝ) := by
  rw [Real.rpow_one]
  have CX : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at h1
  have h := jL CX hs1
  have h1' : 1 / ‖1 - s‖ ≤ 1 := by
    rw [norm_sub_rev] at h1
    rw [div_le_one (by linarith)]
    exact h1
  have hσ' : (3 : ℝ) / 20 ≤ s.re := by
    have := hσ; norm_num at this ⊢; linarith
  have h2 : ‖s‖ / s.re ≤ 1 + 20 / 3 * |s.im| := by
    have hn : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos CX] at hn
    calc ‖s‖ / s.re ≤ (s.re + |s.im|) / s.re := by gcongr
      _ = 1 + |s.im| / s.re := by field_simp
      _ ≤ 1 + |s.im| / (3 / 20) := by gcongr
      _ = 1 + 20 / 3 * |s.im| := by ring
  have ht : 0 ≤ |s.im| := abs_nonneg _
  linarith [h, h1', h2, ht]
theorem Eh :
    ∃ A C : ℝ, 0 < C ∧ ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → 1 ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A :=
  ⟨1, 20 / 3, by norm_num, zV⟩
theorem jR {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
  have hs1 : 1 < s.re := by linarith
  set f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s with hf
  have hsum : Summable f := by
    have h0 := Complex.summable_one_div_nat_cpow.mpr hs1
    have := (summable_nat_add_iff 1).mpr h0
    simpa [f] using this
  have Ym : riemannZeta s = ∑' n, f n := zeta_eq_tsum_one_div_nat_add_one_cpow hs1
  have hf0 : f 0 = 1 := by simp [f]
  have hsplit : riemannZeta s - 1 = ∑' n, f (n + 1) := by
    rw [Ym, hsum.tsum_eq_zero_add, hf0]; ring
  have hle : ∀ n : ℕ, ‖f (n + 1)‖ ≤ 1 / ((n : ℝ) + 2) ^ 2 := by
    intro n
    have hpos : 0 < n + 2 := by omega
    have hf1 : f (n + 1) = 1 / ((n + 2 : ℕ) : ℂ) ^ s := by
      simp only [f]
      congr 2
      push_cast
      ring
    rw [hf1, norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hpos]
    have hbase : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hpos
    have hpow : ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hbase hs
    rw [Real.rpow_two] at hpow
    have h2pos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) ^ 2 := by positivity
    calc 1 / ((n + 2 : ℕ) : ℝ) ^ s.re ≤ 1 / ((n + 2 : ℕ) : ℝ) ^ 2 :=
          one_div_le_one_div_of_le h2pos hpow
      _ = 1 / ((n : ℝ) + 2) ^ 2 := by push_cast; ring
  have htwo : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    norm_num [Finset.sum_range_succ] at h
    exact h.congr_fun fun n => by ring
  rw [hsplit]
  have hsum' : Summable (fun n => f (n + 1)) := (summable_nat_add_iff 1).mpr hsum
  calc ‖∑' n, f (n + 1)‖ ≤ ∑' n, ‖f (n + 1)‖ := norm_tsum_le_tsum_norm hsum'.norm
    _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2 := hsum'.norm.tsum_le_tsum hle htwo.summable
    _ = Real.pi ^ 2 / 6 - 1 := htwo.tsum_eq
theorem nV {s : ℂ} (hs : 2 ≤ s.re) :
    2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta s‖ := by
  have h := jR hs
  have h' : ‖(1 : ℂ)‖ - ‖1 - riemannZeta s‖ ≤ ‖riemannZeta s‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) (1 - riemannZeta s)
  rw [norm_sub_rev] at h'
  simp only [norm_one] at h'
  linarith
lemma lY : (1 / 3 : ℝ) < 2 - Real.pi ^ 2 / 6 := by
  have := Real.pi_lt_d2
  nlinarith [Real.pi_pos]
theorem oM : ∀ t : ℝ, (1 / 3 : ℝ) ≤ ‖riemannZeta (2 + t * I)‖ := by
  intro t
  have h := nV (s := 2 + t * I) (by simp)
  linarith [lY]
theorem nW {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ Real.pi ^ 2 / 6 := by
  have h := jR hs
  have h' : ‖riemannZeta s‖ ≤ ‖riemannZeta s - 1‖ + ‖(1 : ℂ)‖ := by
    simpa using norm_le_norm_sub_add (riemannZeta s) (1 : ℂ)
  simp only [norm_one] at h'
  linarith
end kB
end Zeta23
end
end

-- Zeta23.kB.abj
section
open Set
noncomputable section
namespace Zeta23
@[simp] lemma Pz (ρ : ℂ) : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
@[simp] lemma PI (ρ : ℂ) : (reflect ρ).im = ρ.im := by simp [reflect]
@[simp] lemma reflect_reflect (ρ : ℂ) : reflect (reflect ρ) = ρ := by
  simp [reflect]
lemma Ej : Function.Injective reflect :=
  Function.LeftInverse.injective reflect_reflect
namespace aV
variable (Z : aV) (T₁ T₂ : ℝ)
lemma CY {ρ : ℂ} (h : ρ ∈ Z.window T₁ T₂) : reflect ρ ∈ Z.window T₁ T₂ :=
  ⟨Z.qH ρ h.1, by simpa [PI] using h.2⟩
theorem Ek :
    (Z.N T₁ T₂ : ℝ) ≤ 2 * ∑ᶠ ρ ∈ Z.window T₁ T₂ ∩ {ρ | 1 / 2 ≤ ρ.re}, (Z.mult ρ : ℝ) := by
  have hW : (Z.window T₁ T₂).Finite := Z.qX T₁ T₂
  set A := Z.window T₁ T₂ ∩ {ρ | ρ.re < 1 / 2} with Yn
  set B := Z.window T₁ T₂ ∩ {ρ | 1 / 2 ≤ ρ.re} with hBdef
  have hA : A.Finite := hW.subset inter_subset_left
  have hB : B.Finite := hW.subset inter_subset_left
  have ZV : Z.window T₁ T₂ = A ∪ B := by
    ext ρ
    simp only [Yn, hBdef, mem_union, mem_inter_iff, mem_setOf_eq]
    constructor
    · intro h
      rcases lt_or_ge ρ.re (1 / 2) with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro ρ ⟨_, h1⟩ ⟨_, h2⟩
    simp only [mem_setOf_eq] at h1 h2
    linarith
  have hN : Z.N T₁ T₂ = ∑ᶠ ρ ∈ A, Z.mult ρ + ∑ᶠ ρ ∈ B, Z.mult ρ := by
    unfold aV.N
    rw [ZV, finsum_mem_union hdisj hA hB]
  have himage : reflect '' A ⊆ B := by
    rintro _ ⟨ρ, ⟨ZW, hlt⟩, rfl⟩
    refine ⟨Z.CY T₁ T₂ ZW, ?_⟩
    simp only [mem_setOf_eq, Pz] at hlt ⊢
    linarith
  have hAB : ∑ᶠ ρ ∈ A, Z.mult ρ ≤ ∑ᶠ ρ ∈ B, Z.mult ρ := by
    calc ∑ᶠ ρ ∈ A, Z.mult ρ = ∑ᶠ ρ ∈ A, Z.mult (reflect ρ) :=
          finsum_mem_congr rfl (fun ρ hρ => (Z.kT ρ hρ.1.1).symm)
      _ = ∑ᶠ σ ∈ reflect '' A, Z.mult σ := (finsum_mem_image Ej.injOn).symm
      _ ≤ ∑ᶠ σ ∈ B, Z.mult σ := Z.uj T₁ T₂ himage inter_subset_left
  have hcast : (∑ᶠ ρ ∈ B, (Z.mult ρ : ℝ)) = ((∑ᶠ ρ ∈ B, Z.mult ρ : ℕ) : ℝ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hB, finsum_mem_eq_finite_toFinset_sum _ hB,
      Nat.cast_sum]
  rw [hcast, hN]
  have hAB' : ((∑ᶠ ρ ∈ A, Z.mult ρ : ℕ) : ℝ) ≤ ((∑ᶠ ρ ∈ B, Z.mult ρ : ℕ) : ℝ) := by
    exact_mod_cast hAB
  push_cast
  linarith
end aV
end Zeta23
end
end

-- Zeta23.kB.jo
section
open Complex Set Filter Topology Metric
noncomputable section
namespace Zeta23.kB
theorem kQ {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ {ρ : ℂ | ρ ≠ 1 ∧ riemannZeta ρ = 0}).Finite := by
  choose t ht hfin using jg
  obtain ⟨I, -, hcover⟩ := hK.elim_nhds_subcover t (fun z _ => ht z)
  refine (I.finite_toSet.biUnion fun z _ => hfin z).subset ?_
  rintro ρ ⟨SI, hρ⟩
  obtain ⟨z, hzI, Fo⟩ := mem_iUnion₂.mp (hcover SI)
  exact mem_iUnion₂.mpr ⟨z, hzI, Fo, hρ⟩
def CZ (s₀ c u : ℂ) (z : ℂ) : ℂ := riemannZeta (s₀ + c * z) * u
lemma nC {s₀ c z : ℂ} (h : s₀ + c * z ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ => riemannZeta (s₀ + c * z)) z := by
  have hζ : AnalyticAt ℂ riemannZeta (s₀ + c * z) := cD _ h
  have haff : AnalyticAt ℂ (fun z : ℂ => s₀ + c * z) z := by fun_prop
  exact hζ.comp_of_eq haff rfl
lemma IG {s₀ c u z : ℂ} (h : s₀ + c * z ≠ 1) : AnalyticAt ℂ (CZ s₀ c u) z := by
  have h1 := nC h
  have h2 : AnalyticAt ℂ (fun _ : ℂ => u) z := analyticAt_const
  have := h1.mul h2
  exact this
lemma wC {s₀ c u w : ℂ} (hc : c ≠ 0) (hu : u ≠ 0) (h : s₀ + c * w ≠ 1) :
    analyticOrderNatAt (CZ s₀ c u) w = bY (s₀ + c * w) := by
  unfold analyticOrderNatAt bY CZ
  congr 1
  have haff : AnalyticAt ℂ (fun z : ℂ => s₀ + c * z) w := by fun_prop
  have hcomp : AnalyticAt ℂ (fun z => riemannZeta (s₀ + c * z)) w := nC h
  have hmul : (fun z ↦ riemannZeta (s₀ + c * z) * u) =
      (fun z => riemannZeta (s₀ + c * z)) * fun _ => u := rfl
  rw [hmul, analyticOrderAt_mul hcomp analyticAt_const]
  have hconst : analyticOrderAt (fun _ : ℂ => u) w = 0 :=
    (analyticAt_const).analyticOrderAt_eq_zero.mpr hu
  rw [hconst, add_zero]
  have hderiv : deriv (fun z : ℂ => s₀ + c * z) w ≠ 0 := by
    rw [deriv_const_add, deriv_const_mul _ differentiableAt_id, deriv_id'']; simpa using hc
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := riemannZeta) haff hderiv
  simpa [Function.comp_def] using this
def uZ (t : ℝ) : ℝ := ∑ᶠ ρ ∈ aE.window t (t + 1) ∩ {ρ | 1/2 ≤ ρ.re}, (bY ρ : ℝ)
theorem FK :
    ∃ A₁ : ℝ, ∀ t : ℝ, 4 ≤ |t| → uZ t ≤ A₁ * Real.log (|t| + 3) := by
  obtain ⟨A, C, hC, hgrowth⟩ := Eh
  have hL := oM
  set A' : ℝ := max A 0 with hA'
  have Da : 0 ≤ A' := le_max_right _ _
  set r : ℝ := 0.84 with hr
  set R : ℝ := 0.95 with hR
  have abE : 0 < Real.log (R / r) := Real.log_pos (by norm_num [hr, hR])
  refine ⟨1 / Real.log (R / r) * (|Real.log (3 * C)| + 2 * A'), fun t ht => ?_⟩
  set c₀ : ℂ := 2 + (t + 1/2 : ℝ) * I with hc₀
  set κ : ℂ := ((19/10 : ℝ) : ℂ) with hκ
  have SO : κ ≠ 0 := by simp [hκ]
  have Kt : ‖κ‖ = 1.9 := by simp [hκ]; norm_num
  have OI : (1/3 : ℝ) ≤ ‖riemannZeta c₀‖ := by simpa [hc₀] using hL (t + 1/2)
  have Lq : riemannZeta c₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at OI; norm_num at OI
  set u : ℂ := (riemannZeta c₀)⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero Lq
  have hnu : ‖u‖ ≤ 3 := by
    rw [hu, norm_inv]; rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  set g : ℂ → ℂ := CZ c₀ κ u with hg
  have abF : |t + 1/2| ≤ ‖c₀ - 1‖ := by
    have : (c₀ - 1).im = t + 1/2 := by simp [hc₀]
    rw [← this]; exact Complex.abs_im_le_norm _
  have ht' : 3.5 ≤ |t + 1/2| := by
    rcases le_abs'.mp ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hdist : ∀ z : ℂ, ‖z‖ ≤ 1 → |t + 1/2| - 1.9 * ‖z‖ ≤ ‖c₀ + κ * z - 1‖ := by
    intro z hz
    have h1 : ‖c₀ - 1‖ - ‖κ * z‖ ≤ ‖c₀ + κ * z - 1‖ := by
      have := norm_sub_norm_le (c₀ - 1) (-(κ * z))
      rw [norm_neg] at this
      have e : c₀ - 1 - -(κ * z) = c₀ + κ * z - 1 := by ring
      rw [e] at this; linarith
    rw [norm_mul, Kt] at h1; linarith
  have hne1 : ∀ z : ℂ, ‖z‖ ≤ 1 → c₀ + κ * z ≠ 1 := by
    intro z hz h
    have := hdist z hz
    rw [h, sub_self, norm_zero] at this
    nlinarith
  have eO : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact IG (hne1 z hz)
  have hg0 : g 0 = 1 := by simp [hg, CZ, hu, Lq]
  have hfin : (bC 1 g).Finite := by
    have hK := kQ (isCompact_closedBall c₀ (1.9 : ℝ))
    refine (hK.image fun ρ => (ρ - c₀) / κ).subset ?_
    rintro z ⟨hz, hgz⟩
    refine ⟨c₀ + κ * z, ⟨?_, hne1 z hz, ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Kt]; nlinarith [norm_nonneg z]
    · simpa [hg, CZ, hu0] using hgz
    · show (c₀ + κ * z - c₀) / κ = z
      rw [add_sub_cancel_left, mul_div_cancel_left₀ _ SO]
  set B : ℝ := 3 * C * (|t| + 6) ^ A' with hB
  have acw : 0 < B := by positivity
  have hfz : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := hz.trans (by norm_num [hR])
    set s : ℂ := c₀ + κ * z with hs
    have hsre : (0.15:ℝ) ≤ s.re := by
      have : s.re = 2 + 1.9 * z.re := by norm_num [hs, hc₀, hκ]
      rw [this]
      obtain ⟨h1, -⟩ := abs_le.mp ((abs_re_le_norm z).trans hz)
      rw [hR] at h1; nlinarith
    have hs1 : 1 ≤ ‖s - 1‖ := by have := hdist z hz1; rw [hR] at hz; nlinarith
    have MW : |s.im| + 3 ≤ |t| + 6 := by
      have : s.im = t + 1/2 + 1.9 * z.im := by norm_num [hs, hc₀, hκ]
      rw [this]
      have hzi := (abs_im_le_norm z).trans hz; rw [hR] at hzi
      have h1 := abs_add_le (t + 1/2) (1.9 * z.im)
      have h2 : |1.9 * z.im| ≤ 1.9 * 0.95 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1.9)]; nlinarith
      have h3 : |t + 1/2| ≤ |t| + 1/2 := by simpa using abs_add_le t (1/2)
      linarith
    have h1 : ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A := hgrowth s hsre hs1
    have hbase : 1 ≤ |s.im| + 3 := by linarith [abs_nonneg s.im]
    have h2 : (|s.im| + 3) ^ A ≤ (|s.im| + 3) ^ A' := Real.rpow_le_rpow_of_exponent_le hbase (le_max_left _ _)
    have h3 : (|s.im| + 3) ^ A' ≤ (|t| + 6) ^ A' := Real.rpow_le_rpow (by linarith [abs_nonneg s.im]) MW Da
    calc ‖g z‖ = ‖riemannZeta s‖ * ‖u‖ := by simp [hg, CZ, hs]
      _ ≤ (C * (|t| + 6) ^ A') * 3 := by
          apply mul_le_mul (h1.trans ((mul_le_mul_of_nonneg_left (h2.trans h3) hC.le))) hnu (norm_nonneg _)
          positivity
      _ = B := by rw [hB]; ring
  have hZ := zS (B := B) (r := r) (R := R) (by norm_num [hr]) (by norm_num [hr])
    (by norm_num [hr, hR]) (by norm_num [hR]) eO hg0 hfin hfz
  set W : Set ℂ := aE.window t (t + 1) ∩ {ρ | 1/2 ≤ ρ.re} with hW
  have PO : W.Finite := (aE.qX t (t + 1)).subset inter_subset_left
  set φ : ℂ → ℂ := fun ρ => (ρ - c₀) / κ with hφ
  have IQ : Function.Injective φ := by
    intro a b h; simp only [hφ] at h
    have := congrArg (fun w => c₀ + κ * w) h
    simpa [mul_div_cancel₀ _ SO] using this
  have MY : ∀ ρ, c₀ + κ * φ ρ = ρ := by intro ρ; simp only [hφ]; field_simp; ring
  have Yo : ∀ ρ ∈ W, φ ρ ∈ (aP (by norm_num [hr] : r < 1) hfin).toFinset := by
    rintro ρ ⟨⟨SX, acM, acy⟩, Yp⟩
    simp only [Set.Finite.mem_toFinset]
    have hρ : aO ρ := SX
    refine ⟨?_, ?_⟩
    · 
      simp only [hφ, norm_div, Kt]
      rw [div_le_iff₀ (by norm_num), hr]
      have hre : (ρ - c₀).re = ρ.re - 2 := by simp [hc₀]
      have him : (ρ - c₀).im = ρ.im - (t + 1/2) := by simp [hc₀]
      have hsq : ‖ρ - c₀‖ ^ 2 ≤ (0.84 * 1.9) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
        have := hρ.2.2; have := Yp.out
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq
    · show g (φ ρ) = 0
      simp only [hg, CZ, MY]; rw [hρ.1, zero_mul]
  have Yq : ∀ ρ ∈ W, (bY ρ : ℝ) = (analyticOrderNatAt g (φ ρ) : ℝ) := by
    rintro ρ ⟨⟨SX, -, -⟩, -⟩
    have hρ : aO ρ := SX
    rw [wC SO hu0 (by rw [MY]; exact hρ.wW.2), MY]
  have hsum : uZ t ≤ ((∑ ρ' ∈ (aP (by norm_num [hr] : r < 1) hfin).toFinset,
      analyticOrderNatAt g ρ' : ℕ) : ℝ) := by
    unfold uZ
    rw [← hW, finsum_mem_eq_finite_toFinset_sum _ PO,
      Finset.sum_congr rfl (fun ρ hρ => Yq ρ (PO.mem_toFinset.mp hρ)),
      ← Finset.sum_image (f := fun w => (analyticOrderNatAt g w : ℝ))
        (fun a _ b _ h => IQ h)]
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro w hw
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hw
      exact Yo ρ (PO.mem_toFinset.mp hρ)
    · intros; positivity
  have PS : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith [abs_nonneg t]
  have Yr : Real.log (|t| + 6) ≤ 2 * Real.log (|t| + 3) := by
    rw [← Real.log_rpow (by positivity), Real.rpow_two]
    apply Real.log_le_log (by positivity); nlinarith [abs_nonneg t]
  have DN : Real.log B ≤ (|Real.log (3 * C)| + 2 * A') * Real.log (|t| + 3) := by
    rw [hB, Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity)]
    have h1 := le_abs_self (Real.log (3 * C))
    have h2 : |Real.log (3 * C)| ≤ |Real.log (3 * C)| * Real.log (|t| + 3) :=
      le_mul_of_one_le_right (abs_nonneg _) PS
    have h3 : A' * Real.log (|t| + 6) ≤ A' * (2 * Real.log (|t| + 3)) :=
      mul_le_mul_of_nonneg_left Yr Da
    linarith
  calc uZ t ≤ _ := hsum
    _ ≤ 1 / Real.log (R / r) * Real.log B := by exact_mod_cast hZ
    _ ≤ 1 / Real.log (R / r) * ((|Real.log (3 * C)| + 2 * A') * Real.log (|t| + 3)) :=
        mul_le_mul_of_nonneg_left DN (by positivity)
    _ = _ := by ring
theorem Oi (t : ℝ) (ht : |t| ≤ 4) : (mL t (t + 1) : ℝ) ≤ mL (-4) 5 := by
  obtain ⟨h1, h2⟩ := abs_le.mp ht
  have hsub : aE.window t (t + 1) ⊆ aE.window (-4) 5 := by
    rintro ρ ⟨hρ, ha, hb⟩; exact ⟨hρ, by linarith, by linarith⟩
  have h' : aE.N t (t + 1) ≤ aE.N (-4) 5 :=
    aE.uj (-4) 5 hsub subset_rfl
  rw [jV, jV] at h'
  exact_mod_cast h'
theorem oq : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ,
    (mL t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) := by
  obtain ⟨A₁, hA₁⟩ := FK
  set K : ℝ := (mL (-4) 5 : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨max 1 (max (2 * A₁) K), le_max_left _ _, fun t => ?_⟩
  have PS : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith [abs_nonneg t]
  have hhalf : (mL t (t + 1) : ℝ) ≤ 2 * uZ t := by
    have := aE.Ek t (t + 1)
    simpa [uZ, jV] using this
  rcases le_or_gt 4 |t| with ht | ht
  · calc (mL t (t + 1) : ℝ) ≤ 2 * uZ t := hhalf
      _ ≤ 2 * (A₁ * Real.log (|t| + 3)) := by
          have := hA₁ t ht; nlinarith
      _ = (2 * A₁) * Real.log (|t| + 3) := by ring
      _ ≤ max 1 (max (2 * A₁) K) * Real.log (|t| + 3) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact le_trans (le_max_left _ _) (le_max_right _ _)
  · calc (mL t (t + 1) : ℝ) ≤ K := Oi t ht.le
      _ ≤ K * Real.log (|t| + 3) := le_mul_of_one_le_right hK0 PS
      _ ≤ max 1 (max (2 * A₁) K) * Real.log (|t| + 3) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact le_trans (le_max_right _ _) (le_max_right _ _)
theorem rE : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ,
    (aE.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) := by
  simpa only [jV] using oq
end Zeta23.kB
end
end

-- Zeta23.IT
section
open MeasureTheory Complex Filter Set
open scoped Real FourierTransform Convolution ComplexConjugate ArithmeticFunction
noncomputable section
namespace Zeta23
namespace EF
def tilde (g : ℝ → ℂ) : ℝ → ℂ := fun u => conj (g (-u))
def gO (f g : ℝ → ℂ) : ℝ → ℂ := f ⋆[ContinuousLinearMap.mul ℝ ℂ] tilde g
end EF
namespace EF
def dL (r : ℝ) : ℝ := (Complex.digamma (1 / 4 + I * r / 2)).re - Real.log π
def nP (k : ℝ → ℂ) : ℂ :=
  aD k (I / 2) + aD k (-I / 2)
  - ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (k (Real.log n) + k (-Real.log n))
  + (1 / (2 * π) : ℂ) * ∫ r : ℝ, aD k r * (dL r : ℂ)
def Rk (Z : aV) : Prop :=
  ∀ k : ℝ → ℂ, ContDiff ℝ 2 k → HasCompactSupport k →
    Summable (fun ρ : Z.carrier => (Z.mult ρ : ℂ) * aD k (aF ρ)) ∧
    ∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * aD k (aF ρ) = nP k
theorem dW (c : ℂ) (f : ℝ → ℂ) : ∫ x, c * f x = c * ∫ x, f x :=
  integral_const_mul c f
theorem kJ (c : ℂ) (f : ℝ → ℂ) : ∫ x, f x * c = (∫ x, f x) * c :=
  integral_mul_const c f
theorem Kw (f : ℝ → ℂ) : ∫ x, conj (f x) = conj (∫ x, f x) := integral_conj
theorem iO (k : ℝ → ℂ) (τ : ℝ) :
    aD k τ = 𝓕 k (-τ / (2 * π)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold aD
  congr 1; ext u
  rw [smul_eq_mul, mul_comm (k u)]
  congr 1
  have : (-2 * π * u * (-τ / (2 * π))) = τ * u := by
    field_simp
  rw [this]
  push_cast
  ring_nf
theorem dY {k : ℝ → ℂ} (oN : Integrable (𝓕 k)) :
    Integrable (fun τ : ℝ => aD k τ) := by
  have : (fun τ : ℝ => aD k τ) = fun τ => (𝓕 k) ((-(1 / (2 * π))) * τ) := by
    ext τ; rw [iO, show -(1 / (2 * π)) * τ = -τ / (2 * π) by ring]
  rw [this]
  exact oN.comp_mul_left' (neg_ne_zero.mpr (by positivity))
theorem oO {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k)
    (oN : Integrable (𝓕 k)) (u : ℝ) :
    k u = (1 / (2 * π) : ℂ) * ∫ r : ℝ, aD k r * cexp (-I * r * u) := by
  have hinv := congrFun (hk.fourierInv_fourier_eq hki oN) u
  rw [← hinv, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  have key : (fun r : ℝ => aD k r * cexp (-I * r * u))
      = fun r => (fun v : ℝ => 𝓕 k v * cexp (2 * π * I * v * u)) ((-(1 / (2 * π))) * r) := by
    ext r
    rw [iO, show -(1 / (2 * π)) * r = -r / (2 * π) by ring]
    congr 1
    push_cast
    field_simp
  rw [key, Measure.integral_comp_mul_left (fun v : ℝ => 𝓕 k v * cexp (2 * π * I * v * u))]
  have habs : |(-(1 / (2 * π)) : ℝ)⁻¹| = 2 * π := by
    rw [inv_neg, abs_neg, one_div, inv_inv, abs_of_pos (by positivity)]
  rw [habs, Complex.real_smul, ← mul_assoc]
  have h2π : (1 / (2 * π) : ℂ) * ((2 * π : ℝ) : ℂ) = 1 := by
    push_cast; field_simp
  rw [h2π, one_mul]
  congr 1; ext v
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast; ring
theorem vh {g : ℝ → ℂ} (hg : Continuous g) : Continuous (tilde g) :=
  Complex.continuous_conj.comp (hg.comp continuous_neg)
theorem lT {g : ℝ → ℂ} (hgs : HasCompactSupport g) :
    HasCompactSupport (tilde g) :=
  (hgs.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (g := fun w : ℂ => conj w) (map_zero _)
theorem LV (g : ℝ → ℂ) (z : ℂ) :
    aD (tilde g) z = conj (aD g (conj z)) := by
  unfold aD tilde
  rw [← Kw, ← integral_neg_eq_self]
  congr 1; ext u
  simp only [map_mul, ← Complex.exp_conj, conj_conj, Complex.conj_I, Complex.conj_ofReal,
    Complex.ofReal_neg, neg_neg]
  ring_nf
theorem vk {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) (z : ℂ) :
    aD (gO f g) z = aD f z * conj (aD g (conj z)) := by
  rw [← LV]
  have hgt : Continuous (tilde g) := vh hg
  have aac : HasCompactSupport (tilde g) := lT hgs
  have hFc : Continuous (Function.uncurry fun (x t : ℝ) => f t * tilde g (x - t) * cexp (I * z * x)) := by
    change Continuous fun p : ℝ × ℝ => f p.2 * tilde g (p.1 - p.2) * cexp (I * z * p.1)
    fun_prop
  have hFs : HasCompactSupport
      (Function.uncurry fun (x t : ℝ) => f t * tilde g (x - t) * cexp (I * z * x)) := by
    refine HasCompactSupport.intro ((aac.isCompact.add hfs.isCompact).prod hfs.isCompact) ?_
    rintro ⟨x, t⟩ hxt
    change f t * tilde g (x - t) * cexp (I * z * x) = 0
    rw [mem_prod, not_and_or] at hxt
    rcases hxt with hx | ht
    · by_cases ht : t ∈ tsupport f
      · have hx' : x - t ∉ tsupport (tilde g) := fun h => hx ⟨x - t, h, t, ht, by ring⟩
        rw [image_eq_zero_of_notMem_tsupport hx']; simp
      · rw [image_eq_zero_of_notMem_tsupport ht]; simp
    · rw [image_eq_zero_of_notMem_tsupport ht]; simp
  have hFi : Integrable (Function.uncurry fun (x t : ℝ) => f t * tilde g (x - t) * cexp (I * z * x))
      (volume.prod volume) := hFc.integrable_of_hasCompactSupport hFs
  have hshift : ∀ t : ℝ, ∫ x : ℝ, tilde g (x - t) * cexp (I * z * x)
      = cexp (I * z * t) * ∫ v : ℝ, tilde g v * cexp (I * z * v) := by
    intro t
    rw [← dW,
      ← integral_sub_right_eq_self (fun v : ℝ => cexp (I * z * t) * (tilde g v * cexp (I * z * v))) t]
    congr 1; ext x
    simp only [Complex.ofReal_sub]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2; ring
  calc aD (gO f g) z
      = ∫ x : ℝ, (∫ t : ℝ, f t * tilde g (x - t)) * cexp (I * z * x) := by
        simp only [aD, gO, convolution_def, ContinuousLinearMap.mul_apply']
    _ = ∫ x : ℝ, ∫ t : ℝ, f t * tilde g (x - t) * cexp (I * z * x) := by
        congr 1; ext x; rw [← kJ]
    _ = ∫ t : ℝ, ∫ x : ℝ, f t * tilde g (x - t) * cexp (I * z * x) := integral_integral_swap hFi
    _ = ∫ t : ℝ, f t * cexp (I * z * t) * ∫ v : ℝ, tilde g v * cexp (I * z * v) := by
        congr 1; ext t
        rw [show (fun x : ℝ => f t * tilde g (x - t) * cexp (I * z * x))
            = fun x => f t * (tilde g (x - t) * cexp (I * z * x)) from funext fun _ => mul_assoc _ _ _,
          dW, hshift t]
        ring
    _ = aD f z * aD (tilde g) z := by
        simp only [aD]; rw [← kJ]
theorem jN {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : Continuous g)
    (hfs : HasCompactSupport f) :
    ContDiff ℝ 2 (gO f g) := by
  have := hfs.contDiff_convolution_left (n := 2) (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume)
    hf (vh hg).locallyIntegrable
  simpa [gO] using this
theorem fD {f g : ℝ → ℂ}
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    HasCompactSupport (gO f g) :=
  hfs.convolution _ (lT hgs)
theorem Bw (τ u : ℝ) : ‖cexp (-I * τ * u)‖ = 1 := by
  rw [Complex.norm_exp]; simp
theorem qM {k : ℝ → ℂ} (oN : Integrable (𝓕 k)) {E : ℝ → ℂ}
    (hE : Integrable E) :
    Integrable (Function.uncurry fun (u τ : ℝ) => aD k τ * cexp (-I * τ * u) * E u)
      (volume.prod volume) := by
  have hG : Integrable (fun p : ℝ × ℝ => E p.1 * aD k p.2) (volume.prod volume) :=
    hE.mul_prod (dY oN)
  refine hG.norm.mono' ?_ ?_
  · have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => aD k p.2) (volume.prod volume) :=
      (dY oN).aestronglyMeasurable.comp_snd
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => E p.1) (volume.prod volume) :=
      hE.aestronglyMeasurable.comp_fst
    have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ => cexp (-I * p.2 * p.1)) (volume.prod volume) :=
      (by fun_prop : Continuous fun p : ℝ × ℝ => cexp (-I * p.2 * p.1)).aestronglyMeasurable
    exact (h1.mul h3).mul h2
  · filter_upwards with p
    simp only [Function.uncurry, norm_mul, Bw, mul_one]
    exact le_of_eq (mul_comm _ _)
theorem yW {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k)
    (oN : Integrable (𝓕 k)) {E : ℝ → ℂ} (hE : Integrable E) :
    ∫ u : ℝ, k u * E u
      = (1 / (2 * π) : ℂ) * ∫ τ : ℝ, aD k τ * ∫ u : ℝ, E u * cexp (-I * τ * u) := by
  have hsub : (fun u : ℝ => k u * E u)
      = fun u : ℝ => (1 / (2 * π) : ℂ) * ∫ τ : ℝ, aD k τ * cexp (-I * τ * u) * E u := by
    ext u; rw [oO hk hki oN u, mul_assoc, ← kJ]
  rw [hsub, dW]
  congr 1
  rw [integral_integral_swap (qM oN hE)]
  congr 1; ext τ
  rw [← dW]
  congr 1; ext u; ring
end EF
end Zeta23
end
end

-- Zeta23.Poisson.abk
section
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
namespace Zeta23
theorem xP (f : ℝ → ℂ) (z : ℂ) : aD f z = ∫ u : ℝ, f u * cexp (I * z * u) := rfl
theorem IU (z : ℂ) (u : ℝ) : ‖cexp (I * z * u)‖ = Real.exp (-(z.im * u)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
theorem Db {z : ℂ} {u Λ : ℝ} (hu : |u| ≤ Λ) :
    ‖cexp (I * z * u)‖ ≤ Real.exp (|z.im| * Λ) := by
  rw [IU, Real.exp_le_exp]
  calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
    _ = |z.im| * |u| := abs_mul _ _
    _ ≤ |z.im| * Λ := by gcongr
theorem jz {f : ℝ → ℂ} {Λ : ℝ} (hfi : Integrable f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) (z : ℂ) :
    ‖aD f z‖ ≤ Real.exp (|z.im| * Λ) * ∫ u, ‖f u‖ := by
  rw [xP, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hfi.norm.const_mul _) (Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  by_cases hu : f u = 0
  · simp [hu]
  · rw [mul_comm]
    gcongr
    exact Db (hsupp u hu)
theorem AN {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hsupp : HasCompactSupport f) (z : ℂ) :
    aD (deriv f) z = -(I * z) * aD f z := by
  have hf' : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hfd : ∀ x, HasDerivAt f (deriv f x) x := fun x => (hf.differentiable (by norm_num) x).hasDerivAt
  have hv : ∀ x : ℝ, HasDerivAt (fun u : ℝ => cexp (I * z * u)) (I * z * cexp (I * z * x)) x := by
    intro x
    have h1 : HasDerivAt (fun u : ℝ => I * z * u) (I * z * 1) x :=
      ((hasDerivAt_id x).ofReal_comp).const_mul (I * z)
    simpa [mul_comm] using h1.cexp
  have hcv : Continuous (fun u : ℝ => cexp (I * z * u)) := by fun_prop
  have aad : Continuous (fun u : ℝ => I * z * cexp (I * z * u)) := by fun_prop
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := f)
    (v := fun u : ℝ => cexp (I * z * u)) (u' := deriv f)
    (v' := fun x : ℝ => I * z * cexp (I * z * x))
    (fun x _ => hfd x) (fun x _ => hv x)
    ((hf.continuous.mul aad).integrable_of_hasCompactSupport hsupp.mul_right)
    ((hf'.mul hcv).integrable_of_hasCompactSupport hsupp.deriv.mul_right)
    ((hf.continuous.mul hcv).integrable_of_hasCompactSupport hsupp.mul_right)
  have : (fun u : ℝ => f u * (I * z * cexp (I * z * u))) = fun u => (I * z) * (f u * cexp (I * z * u)) := by
    funext u; ring
  rw [this, integral_const_mul] at key
  have key' : I * z * aD f z = -aD (deriv f) z := by
    rw [xP, xP]; exact key
  linear_combination key'
theorem Bz {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    (z : ℂ) : aD (deriv (deriv f)) z = -z ^ 2 * aD f z := by
  have h1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  rw [AN h1 hsupp.deriv, AN (hf.of_le (by norm_num)) hsupp]
  ring_nf
  rw [I_sq]
  ring
theorem dV {E : Type*} [Zero E] {f : ℝ → E} {Λ : ℝ}
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) : HasCompactSupport f := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -Λ) (b := Λ)) ?_
  intro u hu
  exact abs_le.mp (hsupp u hu)
theorem kR {E : Type*} [Zero E] {f : ℝ → E} {Λ : ℝ}
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) : tsupport f ⊆ Icc (-Λ) Λ :=
  closure_minimal (fun u hu => abs_le.mp (hsupp u hu)) isClosed_Icc
theorem jE {f : ℝ → ℂ} {Λ : ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) (z : ℂ) :
    ‖aD f z‖ * ‖z‖ ^ 2 ≤ Real.exp (|z.im| * Λ) * ∫ u, ‖deriv (deriv f) u‖ := by
  have hcs : HasCompactSupport f := dV hsupp
  have hts := kR hsupp
  have Wi : ∀ u, deriv (deriv f) u ≠ 0 → |u| ≤ Λ := by
    intro u hu
    have : u ∈ tsupport f :=
      tsupport_deriv_subset (support_deriv_subset (Function.mem_support.mpr hu))
    exact abs_le.mpr (hts this)
  have hint : Integrable (deriv (deriv f)) :=
    (hf.deriv'.continuous_deriv le_rfl).integrable_of_hasCompactSupport hcs.deriv.deriv
  have := jz hint Wi z
  rw [Bz hf hcs, norm_mul, norm_neg, norm_pow, mul_comm] at this
  exact this
theorem kL {f : ℝ → ℂ} {Λ : ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) {z : ℂ} (hz : z ≠ 0) :
    ‖aD f z‖ ≤ Real.exp (|z.im| * Λ) * (∫ u, ‖deriv (deriv f) u‖) / ‖z‖ ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  exact jE hf hsupp z
end Zeta23
end

-- Zeta23.cw.Um
section
noncomputable section
namespace Zeta23
namespace cw
open Complex Set Filter MeasureTheory
lemma IZ (ρ : ℂ) : (aF ρ).re = ρ.im := by
  simp [aF, Complex.div_I]
lemma PW (ρ : ℂ) : (aF ρ).im = 1 / 2 - ρ.re := by
  simp [aF, Complex.div_I]
lemma xQ (ρ : ℂ) : |ρ.im| ≤ ‖aF ρ‖ := by
  rw [← IZ]; exact Complex.abs_re_le_norm _
lemma En {ρ : ℂ} (h : 0 ≤ ρ.re ∧ ρ.re ≤ 1) : |(aF ρ).im| ≤ 1 / 2 := by
  rw [PW, abs_le]; constructor <;> linarith [h.1, h.2]
lemma Rm (n : ℤ) (hn : n ≠ 0) :
    Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) ≤ 4 * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hn0 : (0 : ℝ) < |(n : ℝ)| := by linarith
  have h1 := Real.log_le_rpow_div (show (0:ℝ) ≤ |(n:ℝ)| + 3 by positivity)
    (show (0:ℝ) < 1/2 by norm_num)
  have h2 : (|(n : ℝ)| + 3) ^ (1 / 2 : ℝ) ≤ (4 * |(n : ℝ)|) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have h3 : (4 * |(n : ℝ)|) ^ (1 / 2 : ℝ) = 2 * |(n : ℝ)| ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hn0.le, show (4:ℝ) ^ (1/2:ℝ) = 2 by
      rw [show (4:ℝ) = 2 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num]
  have hA : Real.log (|(n : ℝ)| + 3) ≤ 4 * |(n : ℝ)| ^ (1 / 2 : ℝ) := by
    have : (|(n : ℝ)| + 3) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * (|(n : ℝ)| + 3) ^ (1 / 2 : ℝ) := by ring
    rw [this] at h1; rw [h3] at h2; linarith
  have hB : 1 / (1 + (n : ℝ) ^ 2) ≤ |(n : ℝ)| ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hn0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs,
      one_div]
    exact inv_anti₀ (by positivity) (by linarith)
  calc Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)
      = Real.log (|(n : ℝ)| + 3) * (1 / (1 + (n : ℝ) ^ 2)) := by ring
    _ ≤ (4 * |(n : ℝ)| ^ (1 / 2 : ℝ)) * |(n : ℝ)| ^ (-2 : ℝ) :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = 4 * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
        rw [mul_assoc, ← Real.rpow_add hn0]; norm_num
lemma Ja :
    Summable (fun n : ℤ => Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by
  refine Summable.of_norm_bounded_eventually
    ((Real.summable_abs_int_rpow (show (1:ℝ) < 3/2 by norm_num)).mul_left 4) ?_
  filter_upwards [eventually_cofinite_ne 0] with n hn
  have h0 : 0 ≤ Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) :=
    div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact Rm n hn
def totalWeight : ℝ := ∑' n : ℤ, Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)
def key (y : ℝ) : ℤ := ⌈y⌉ - 1
lemma Ro (y : ℝ) : (key y : ℝ) < y := by
  have := Int.ceil_lt_add_one y; unfold key; push_cast; linarith
lemma yZ (y : ℝ) : y ≤ (key y : ℝ) + 1 := by
  have := Int.le_ceil y; unfold key; push_cast; linarith
lemma LW {y : ℝ} {n : ℤ} (h1 : (n : ℝ) < y) (h2 : y ≤ (n : ℝ) + 1) :
    (1 + (n : ℝ) ^ 2) / 4 ≤ 1 + y ^ 2 := by
  rcases le_or_gt 0 (n : ℝ) with hn | hn
  · nlinarith
  · have hn' : n < 0 := by exact_mod_cast hn
    have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    have hy : ((n : ℝ) + 1) ^ 2 ≤ y ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h2) (by linarith : (0:ℝ) ≤ -(y + ((n : ℝ) + 1)))]
    nlinarith [hy, sq_nonneg ((n : ℝ) + 4 / 3)]
theorem BG (Z : aV) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (PX : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    Summable (fun ρ : Z.carrier =>
      (Z.mult ρ : ℝ) / (1 + Complex.normSq (aF ρ))) := by
  classical
  have Fd := Tail.jo.Ao Z hA₀ PX
  have hW := Ja
  refine summable_of_sum_le (c := 4 * A₀ * totalWeight) (fun ρ => div_nonneg (Nat.cast_nonneg _)
    (by linarith [Complex.normSq_nonneg (aF (ρ : ℂ))])) fun s => ?_
  set κ : Z.carrier → ℤ := fun ρ => key (ρ : ℂ).im with hκ
  rw [← Finset.sum_fiberwise_of_maps_to (g := κ) (t := s.image κ) (fun ρ hρ => Finset.mem_image_of_mem κ hρ)]
  have Wj : ∀ n ∈ s.image κ,
      ∑ ρ ∈ s with κ ρ = n, (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (aF ρ))
        ≤ 4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by
    intro n _
    have hwin := Fd.window n (s.filter fun ρ => κ ρ = n) (fun ρ hρ => by
      simp only [Finset.mem_filter] at hρ
      rw [← hρ.2]; exact ⟨Ro _, yZ _⟩)
    have hpt : ∀ ρ ∈ s.filter (fun ρ => κ ρ = n),
        (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (aF ρ))
          ≤ (4 / (1 + (n : ℝ) ^ 2)) * (Z.mult ρ : ℝ) := by
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      have h1 : (n : ℝ) < (ρ : ℂ).im := by rw [← hρ.2]; exact Ro _
      have h2 : (ρ : ℂ).im ≤ (n : ℝ) + 1 := by rw [← hρ.2]; exact yZ _
      have hge := LW h1 h2
      have hnorm : 1 + ((ρ : ℂ).im) ^ 2 ≤ 1 + Complex.normSq (aF ρ) := by
        rw [Complex.normSq_apply, IZ]; nlinarith [sq_nonneg ((aF (ρ:ℂ)).im)]
      have hm : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
      have hN0 : 0 < 1 + Complex.normSq (aF (ρ : ℂ)) := by
        linarith [Complex.normSq_nonneg (aF (ρ : ℂ))]
      have hinv : 1 / (1 + Complex.normSq (aF (ρ : ℂ))) ≤ 4 / (1 + (n : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ hN0 (by positivity)]; nlinarith [hge, hnorm]
      calc (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (aF ρ))
          = (Z.mult (ρ : ℂ) : ℝ) * (1 / (1 + Complex.normSq (aF (ρ : ℂ)))) := by ring
        _ ≤ (Z.mult (ρ : ℂ) : ℝ) * (4 / (1 + (n : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left hinv hm
        _ = (4 / (1 + (n : ℝ) ^ 2)) * (Z.mult ρ : ℝ) := by ring
    calc ∑ ρ ∈ s with κ ρ = n, (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (aF ρ))
        ≤ ∑ ρ ∈ s with κ ρ = n, (4 / (1 + (n : ℝ) ^ 2)) * (Z.mult ρ : ℝ) :=
          Finset.sum_le_sum hpt
      _ = (4 / (1 + (n : ℝ) ^ 2)) * ∑ ρ ∈ s with κ ρ = n, (Z.mult ρ : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (4 / (1 + (n : ℝ) ^ 2)) * (A₀ * Real.log (|(n:ℝ)| + 3)) :=
          mul_le_mul_of_nonneg_left hwin (by positivity)
      _ = 4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by ring
  calc ∑ n ∈ s.image κ, ∑ ρ ∈ s with κ ρ = n, (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (aF ρ))
      ≤ ∑ n ∈ s.image κ, 4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) :=
        Finset.sum_le_sum Wj
    _ = 4 * A₀ * ∑ n ∈ s.image κ, Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ 4 * A₀ * totalWeight := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact hW.sum_le_tsum _ fun n _ =>
          div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)
theorem vq (Z : aV) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (PX : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (bD : HasCompactSupport k) :
    Summable (fun ρ : Z.carrier =>
      (Z.mult ρ : ℂ) * aD k (aF ρ)) := by
  classical
  obtain ⟨r, hr⟩ := bD.isCompact.isBounded.subset_closedBall 0
  set Λ : ℝ := max r 0 with hΛ
  have hsupp : ∀ u, k u ≠ 0 → |u| ≤ Λ := by
    intro u hu
    have : u ∈ Metric.closedBall (0:ℝ) r := hr (subset_tsupport _ (Function.mem_support.mpr hu))
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  set C₂ : ℝ := ∫ u, ‖deriv (deriv k) u‖ with hC₂
  have Rq : 0 ≤ C₂ := integral_nonneg fun _ => norm_nonneg _
  set C : ℝ := 2 * Real.exp (Λ / 2) * C₂ with hC
  have hg := (BG Z hA₀ PX).mul_left C
  refine Summable.of_norm_bounded_eventually hg ?_
  have hfin : (Z.window (-1) 1).Finite := Z.dS _ _
  have hSfin : ((fun ρ : Z.carrier => (ρ : ℂ)) ⁻¹' (Z.window (-1) 1)).Finite :=
    hfin.preimage Subtype.val_injective.injOn
  filter_upwards [hSfin.compl_mem_cofinite] with ρ hρ
  simp only [Set.mem_compl_iff, Set.mem_preimage, aV.window, Set.mem_inter_iff,
    Set.mem_setOf_eq, not_and, not_le] at hρ
  have Rr : (ρ : ℂ) ∈ Z.carrier := ρ.2
  have him : 1 ≤ |(ρ : ℂ).im| := by
    by_contra h
    rw [not_le, abs_lt] at h
    exact absurd (hρ Rr h.1) (not_lt.mpr h.2.le)
  have hz1 : 1 ≤ ‖aF (ρ : ℂ)‖ := him.trans (xQ _)
  have hz0 : aF (ρ : ℂ) ≠ 0 := fun h => by rw [h, norm_zero] at hz1; linarith
  have vE := Z.strip _ Rr
  have acz : |(aF (ρ : ℂ)).im| ≤ 1 / 2 := En vE
  have hFT := kL hk hsupp hz0
  have acN : 0 ≤ Λ := le_max_right _ _
  rw [norm_mul, Complex.norm_natCast]
  have hm : (0:ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  have hkey : ‖aD k (aF (ρ : ℂ))‖ ≤ C * (1 / (1 + Complex.normSq (aF (ρ : ℂ)))) := by
    have hexp : Real.exp (|(aF (ρ:ℂ)).im| * Λ) ≤ Real.exp (Λ / 2) := by
      apply Real.exp_le_exp.mpr; nlinarith
    have hnsq : Complex.normSq (aF (ρ : ℂ)) = ‖aF (ρ : ℂ)‖ ^ 2 := Complex.normSq_eq_norm_sq _
    have h2 : 1 / ‖aF (ρ : ℂ)‖ ^ 2 ≤ 2 * (1 / (1 + Complex.normSq (aF (ρ : ℂ)))) := by
      rw [hnsq, div_le_iff₀ (by positivity)]
      have : 0 < 1 + ‖aF (ρ:ℂ)‖ ^ 2 := by positivity
      rw [show 2 * (1 / (1 + ‖aF (ρ:ℂ)‖ ^ 2)) * ‖aF (ρ:ℂ)‖ ^ 2
          = 2 * ‖aF (ρ:ℂ)‖ ^ 2 / (1 + ‖aF (ρ:ℂ)‖ ^ 2) by ring, le_div_iff₀ this]
      nlinarith
    calc ‖aD k (aF (ρ : ℂ))‖
        ≤ Real.exp (|(aF (ρ:ℂ)).im| * Λ) * C₂ / ‖aF (ρ : ℂ)‖ ^ 2 := hFT
      _ = Real.exp (|(aF (ρ:ℂ)).im| * Λ) * C₂ * (1 / ‖aF (ρ : ℂ)‖ ^ 2) := by ring
      _ ≤ Real.exp (Λ / 2) * C₂ * (2 * (1 / (1 + Complex.normSq (aF (ρ : ℂ))))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hexp Rq) h2 (by positivity) (by positivity)
      _ = C * (1 / (1 + Complex.normSq (aF (ρ : ℂ)))) := by rw [hC]; ring
  calc (Z.mult ρ : ℝ) * ‖aD k (aF (ρ : ℂ))‖
      ≤ (Z.mult ρ : ℝ) * (C * (1 / (1 + Complex.normSq (aF (ρ : ℂ))))) :=
        mul_le_mul_of_nonneg_left hkey hm
    _ = C * ((Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (aF (ρ : ℂ)))) := by
        ring
theorem oP (hs : gI) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (bD : HasCompactSupport k) :
    Summable (fun ρ : (bT hs).carrier =>
      ((bT hs).mult ρ : ℂ) * aD k (aF ρ)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.kB.oq
  exact vq (bT hs) hA₀ (fun t => by rw [EU]; exact hloc t) hk bD
end cw
end Zeta23
end
end

-- Zeta23.cw.Yt
section
noncomputable section
namespace Zeta23
namespace cw
open Complex Filter Topology
lemma kO {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℝ s := by
  have h1 : DifferentiableAt ℂ (fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2)) s :=
    (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h2 : DifferentiableAt ℂ (fun u : ℂ => Gamma (u / 2)) s := by
    refine (Complex.differentiableAt_Gamma _ fun m hm => ?_).comp s (differentiableAt_id.div_const _)
    have := congrArg Complex.re hm
    simp at this
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have : Gammaℝ = fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2) * Gamma (u / 2) := funext Gammaℝ_def
  rw [this]
  exact h1.mul h2
lemma pW {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gammaℝ s := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
  exact DifferentiableOn.analyticAt (fun u hu => (kO hu).differentiableWithinAt)
    (hopen.mem_nhds hs)
lemma jA {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta =ᶠ[𝓝 s] fun u => Gammaℝ u * riemannZeta u := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with u hu
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  have hΓ := Gammaℝ_ne_zero_of_re_pos hu
  rw [riemannZeta_def_of_ne_zero hu0]
  field_simp
lemma nD {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  DifferentiableOn.analyticAt (s := ({1}ᶜ : Set ℂ))
    (fun _ hu => (differentiableAt_riemannZeta hu).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hs)
theorem jF (s : ℂ) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) (vE : 0 < s.re) :
    logDeriv completedRiemannZeta s = logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s := by
  have hev := jA vE
  have heq : logDeriv completedRiemannZeta s = logDeriv (fun u => Gammaℝ u * riemannZeta u) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [heq]
  exact logDeriv_mul s (Gammaℝ_ne_zero_of_re_pos vE) hζ (kO vE)
    (differentiableAt_riemannZeta hs1)
theorem jB (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv completedRiemannZeta (1 - s) = -logDeriv completedRiemannZeta s := by
  have hcomp : completedRiemannZeta = completedRiemannZeta ∘ (fun u : ℂ => 1 - u) := by
    funext u; simp [completedRiemannZeta_one_sub]
  have hd : DifferentiableAt ℂ completedRiemannZeta (1 - s) :=
    differentiableAt_completedZeta (sub_ne_zero.mpr (Ne.symm hs1)) (by
      intro h; apply hs0; linear_combination -h)
  have hg : DifferentiableAt ℂ (fun u : ℂ => 1 - u) s := (differentiableAt_const _).sub differentiableAt_id
  have key := logDeriv_comp (x := s) hd hg
  rw [← hcomp] at key
  have hderiv : deriv (fun u : ℂ => 1 - u) s = -1 := by
    rw [deriv_const_sub, deriv_id'']
  rw [key, hderiv]
  ring
theorem tJ {ρ : ℂ} (h : 0 < ρ.re) (h' : ρ.re < 1) :
    (completedRiemannZeta ρ = 0 ↔ aO ρ) ∧
    analyticOrderAt completedRiemannZeta ρ = analyticOrderAt riemannZeta ρ := by
  have Ml : ρ ≠ 1 := fun e => by simp [e] at h'
  have hΓ : Gammaℝ ρ ≠ 0 := Gammaℝ_ne_zero_of_re_pos h
  have hev := jA h
  have hval : completedRiemannZeta ρ = Gammaℝ ρ * riemannZeta ρ := hev.eq_of_nhds
  have oQ := pW h
  have Yv := nD Ml
  refine ⟨?_, ?_⟩
  · rw [hval, mul_eq_zero, aO]
    constructor
    · rintro (aae | hz)
      · exact absurd aae hΓ
      · exact ⟨hz, h, h'⟩
    · rintro ⟨hz, -, -⟩
      exact Or.inr hz
  · rw [analyticOrderAt_congr hev]
    have hmul := analyticOrderAt_mul oQ Yv
    rw [show (Gammaℝ * riemannZeta) = (fun u => Gammaℝ u * riemannZeta u) from rfl] at hmul
    rw [hmul, oQ.analyticOrderAt_eq_zero.mpr hΓ, zero_add]
end cw
end Zeta23
end
end

-- Zeta23.gX
section
namespace Zeta23
open Complex
open scoped ContDiff
theorem vF (z : ℂ) :
    Complex.digamma ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Complex.digamma z) := by
  have hG : (starRingEnd ℂ) ∘ Complex.Gamma ∘ (starRingEnd ℂ) = Complex.Gamma := by
    funext w
    simp only [Function.comp_apply]
    rw [Complex.Gamma_conj]
    exact Complex.conj_conj _
  have hd : deriv Complex.Gamma ((starRingEnd ℂ) z)
      = (starRingEnd ℂ) (deriv Complex.Gamma z) := by
    conv_lhs => rw [← hG, deriv_conj_conj]
    simp only [Function.comp_apply, Complex.conj_conj]
  simp only [Complex.digamma_def, logDeriv_apply]
  rw [hd, Complex.Gamma_conj, ← map_div₀]
theorem OJ (τ : ℝ) : mu (-τ) = mu τ := by
  unfold mu
  have harg : (1 / 4 + Complex.I * ((-τ : ℝ) : ℂ) / 2 : ℂ)
      = (starRingEnd ℂ) (1 / 4 + Complex.I * (τ : ℂ) / 2) := by
    apply Complex.ext <;> simp [map_ofNat]
  rw [show ((-τ : ℝ) : ℂ) = -(τ : ℂ) by push_cast; ring] at harg ⊢
  rw [harg, vF]
  simp
private lemma vG {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -m := by
  intro m h
  rw [h] at hz
  simp only [Complex.neg_re, Complex.natCast_re] at hz
  exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg m))) hz
private lemma Dd {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.digamma z := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have Yw : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 0 < w.re} := fun w hw =>
    (Complex.differentiableAt_Gamma w (vG hw)).differentiableWithinAt
  have Uq := Yw.analyticOnNhd hU
  have h1 : AnalyticAt ℂ (deriv Complex.Gamma) z := (Uq z hz).deriv
  have h2 : AnalyticAt ℂ Complex.Gamma z := Uq z hz
  have h3 : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero (vG hz)
  have h4 := h1.div h2 h3
  exact h4.congr (by
    filter_upwards with w
    rw [Complex.digamma_def, logDeriv_apply]
    rfl)
theorem Dh : ContDiff ℝ ∞ mu := by
  have hc : ContDiff ℝ ∞ (fun τ : ℝ => (1 / 4 + Complex.I * (τ : ℂ) / 2 : ℂ)) := by
    have h1 : ContDiff ℝ ∞ (fun τ : ℝ => (τ : ℂ)) := Complex.ofRealCLM.contDiff
    have h2 : ContDiff ℝ ∞ (fun τ : ℝ => Complex.I * (τ : ℂ)) := contDiff_const.mul h1
    have h3 : ContDiff ℝ ∞ (fun τ : ℝ => Complex.I * (τ : ℂ) / 2) := by
      simpa [div_eq_mul_inv] using h2.mul contDiff_const
    exact contDiff_const.add h3
  refine contDiff_iff_contDiffAt.mpr fun τ => ?_
  have hz : (0 : ℝ) < (1 / 4 + Complex.I * (τ : ℂ) / 2 : ℂ).re := by
    simp
  have h4' : AnalyticAt ℝ Complex.digamma (1 / 4 + Complex.I * (τ : ℂ) / 2) :=
    AnalyticAt.restrictScalars (Dd hz)
  have h4 : ContDiffAt ℝ ∞ Complex.digamma (1 / 4 + Complex.I * (τ : ℂ) / 2) :=
    h4'.contDiffAt
  have h5 : ContDiffAt ℝ ∞
      (fun τ : ℝ => Complex.digamma (1 / 4 + Complex.I * (τ : ℂ) / 2)) τ :=
    h4.comp τ hc.contDiffAt
  have h6 : ContDiffAt ℝ ∞
      (fun τ : ℝ => (Complex.digamma (1 / 4 + Complex.I * (τ : ℂ) / 2)).re) τ :=
    (Complex.reCLM.contDiff.contDiffAt).comp τ h5
  have h7 : ContDiffAt ℝ ∞ mu τ := by
    have := (contDiffAt_const (c := (1 / (2 * Real.pi) : ℝ))).mul h6
    exact (this.sub contDiffAt_const)
  exact h7
end Zeta23
end

-- Zeta23.gX.Series
section
noncomputable section
namespace Zeta23
namespace fF
open Complex Filter Topology
def cV (n : ℕ) (z : ℂ) : ℂ := (1 + z / (n + 1)) * Complex.exp (-(z / (n + 1))) - 1
lemma rF (n : ℕ) (z : ℂ) :
    1 + cV n z = (1 + z / (n + 1)) * Complex.exp (-(z / (n + 1))) := by
  unfold cV
  ring
lemma jW (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
lemma AO {z : ℂ} {n : ℕ} (h : ‖z‖ ≤ (n : ℝ) + 1) :
    ‖cV n z‖ ≤ 3 * (‖z‖ / ((n : ℝ) + 1)) ^ 2 := by
  set w : ℂ := z / ((n : ℂ) + 1) with hwdef
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have Rw : ‖w‖ = ‖z‖ / ((n : ℝ) + 1) := by
    rw [hwdef, norm_div, jW]
  have hwn : ‖w‖ ≤ 1 := by
    rw [Rw, div_le_one hn1]
    exact h
  have hr : ‖Complex.exp (-w) - 1 + w‖ ≤ ‖w‖ ^ 2 := by
    have hx : ‖(-w : ℂ)‖ ≤ 1 := by rwa [norm_neg]
    have h2 := norm_exp_sub_one_sub_id_le hx
    rw [norm_neg] at h2
    calc ‖Complex.exp (-w) - 1 + w‖ = ‖Complex.exp (-w) - 1 - (-w)‖ := by ring_nf
      _ ≤ ‖w‖ ^ 2 := h2
  have hident : cV n z = (Complex.exp (-w) - 1 + w) - w ^ 2
      + w * (Complex.exp (-w) - 1 + w) := by
    unfold cV
    ring
  have aaf : ‖(w : ℂ) ^ 2‖ = ‖w‖ ^ 2 := norm_pow _ _
  calc ‖cV n z‖
      ≤ ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖ + ‖w * (Complex.exp (-w) - 1 + w)‖ := by
        rw [hident]
        exact norm_add_le _ _
    _ ≤ (‖w‖ ^ 2 + ‖w‖ ^ 2) + ‖w‖ * ‖w‖ ^ 2 := by
        have h1 : ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := by
          calc ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖
              ≤ ‖Complex.exp (-w) - 1 + w‖ + ‖(w : ℂ) ^ 2‖ := norm_sub_le _ _
            _ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := by
                rw [aaf]
                exact add_le_add hr le_rfl
        have h2 : ‖w * (Complex.exp (-w) - 1 + w)‖ ≤ ‖w‖ * ‖w‖ ^ 2 := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hr (norm_nonneg _)
        linarith
    _ ≤ 3 * ‖w‖ ^ 2 := by nlinarith [norm_nonneg w, hwn, sq_nonneg ‖w‖]
    _ = 3 * (‖z‖ / ((n : ℝ) + 1)) ^ 2 := by rw [Rw]
lemma wN (R : ℝ) : Summable (fun n : ℕ => 3 * (R / ((n : ℝ) + 1)) ^ 2) := by
  have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
    have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
      have := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
      have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
        funext n
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rwa [heq] at this
    have := (summable_nat_add_iff 1).mpr h2
    simpa [add_comm] using this
  have h3 : (fun n : ℕ => 3 * (R / ((n : ℝ) + 1)) ^ 2)
      = fun n : ℕ => (3 * R ^ 2) * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
    funext n
    rw [div_pow]
    ring
  rw [h3]
  exact h1.mul_left _
lemma BJ (z : ℂ) : Summable (fun n => ‖cV n z‖) := by
  refine (wN ‖z‖).of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_ge_atTop ⌈‖z‖⌉₊] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  refine AO ?_
  calc ‖z‖ ≤ (⌈‖z‖⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn
    _ ≤ (n : ℝ) + 1 := by linarith
lemma rG (z : ℂ) : Multipliable fun n => 1 + cV n z :=
  Complex.multipliable_one_add_of_summable ((BJ z).of_norm)
lemma vH (N : ℕ) :
    ((harmonic N : ℚ) : ℝ) = ∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1) := by
  rw [harmonic]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [one_div]
lemma Jb {z : ℂ} (_hz : z ∈ Complex.integerComplement) {N : ℕ} (hN : 1 ≤ N) :
    (Complex.GammaSeq z N)⁻¹
      = z * Complex.exp ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1))
            - Real.log N : ℝ) : ℂ) * z)
          * ∏ n ∈ Finset.range N, (1 + cV n z) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hprod : ∏ n ∈ Finset.range N, (1 + cV n z)
      = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
          * Complex.exp (-(∑ m ∈ Finset.range N, z / ((m : ℂ) + 1))) := by
    calc ∏ n ∈ Finset.range N, (1 + cV n z)
        = ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
            * Complex.exp (-(z / ((n : ℂ) + 1))) :=
          Finset.prod_congr rfl fun n _ => rF n z
      _ = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
            * ∏ n ∈ Finset.range N, Complex.exp (-(z / ((n : ℂ) + 1))) :=
          Finset.prod_mul_distrib
      _ = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
            * Complex.exp (∑ n ∈ Finset.range N, -(z / ((n : ℂ) + 1))) := by
          rw [Complex.exp_sum]
      _ = _ := by rw [← Finset.sum_neg_distrib]
  have aag : ((N.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hNz : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have OZ : (N : ℂ) ^ z = Complex.exp (((Real.log N : ℝ) : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero hNz]
    congr 2
    rw [show ((N : ℂ)) = (((N : ℝ) : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log hNR.le).symm
  have hdenom : ∏ j ∈ Finset.range (N + 1), (z + (j : ℂ))
      = z * ∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1)) := by
    rw [Finset.prod_range_succ']
    rw [Nat.cast_zero, add_zero, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun n _ => ?_
    push_cast
    ring
  have Ry : ((N.factorial : ℕ) : ℂ) = ∏ n ∈ Finset.range N, ((n : ℂ) + 1) := by
    rw [show N.factorial = ∏ n ∈ Finset.range N, (n + 1) from
      (Finset.prod_range_add_one_eq_factorial N).symm]
    push_cast
    rfl
  have hfrac : ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
      = (∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1))) / ((N.factorial : ℕ) : ℂ) := by
    have h1 : ∀ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
        = (z + ((n : ℂ) + 1)) / ((n : ℂ) + 1) := by
      intro n _
      have hne : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      field_simp
      ring
    rw [Finset.prod_congr rfl h1, Finset.prod_div_distrib, Ry]
  have SY : (((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ)
      = ∑ m ∈ Finset.range N, 1 / ((m : ℂ) + 1) := by
    push_cast
    rfl
  have Yx : ∑ m ∈ Finset.range N, z / ((m : ℂ) + 1)
      = z * ∑ m ∈ Finset.range N, 1 / ((m : ℂ) + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [Complex.GammaSeq, hprod, hfrac, hdenom, OZ, Yx, ← SY]
  rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub]
  set A : ℂ := ∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1)) with hA
  set E1 : ℂ := Complex.exp ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ) * z)
    with hE1
  set E2 : ℂ := Complex.exp (((Real.log N : ℝ) : ℂ) * z) with hE2
  have acA : E1 ≠ 0 := Complex.exp_ne_zero _
  have acB : E2 ≠ 0 := Complex.exp_ne_zero _
  have Vf : Complex.exp (-(z * (((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ)))
      = E1⁻¹ := by
    rw [hE1, ← Complex.exp_neg]
    congr 1
    ring
  rw [Vf]
  field_simp
theorem lZ {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    (Complex.Gamma z)⁻¹
      = z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
          * ∏' n : ℕ, (1 + cV n z) := by
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hL : Tendsto (fun N => (Complex.GammaSeq z N)⁻¹) atTop (𝓝 ((Complex.Gamma z)⁻¹)) :=
    (Complex.GammaSeq_tendsto_Gamma z).inv₀ (Complex.Gamma_ne_zero hzero)
  have aah : Tendsto (fun N : ℕ =>
      ((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    refine Real.tendsto_harmonic_sub_log.congr fun n => ?_
    rw [vH]
  have hexp : Tendsto (fun N : ℕ => Complex.exp
      ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z))
      atTop (𝓝 (Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z))) := by
    have h2 : Tendsto (fun N : ℕ =>
        ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ)))
        atTop (𝓝 ((Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp aah
    exact (Complex.continuous_exp.tendsto _).comp (h2.mul_const z)
  have hP : Tendsto (fun N => ∏ n ∈ Finset.range N, (1 + cV n z)) atTop
      (𝓝 (∏' n : ℕ, (1 + cV n z))) :=
    (rG z).hasProd.tendsto_prod_nat
  have hRHS : Tendsto (fun N : ℕ => z * Complex.exp
      ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z)
      * ∏ n ∈ Finset.range N, (1 + cV n z)) atTop
      (𝓝 (z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
        * ∏' n : ℕ, (1 + cV n z))) :=
    (tendsto_const_nhds.mul hexp).mul hP
  have heq : ∀ᶠ N in atTop, (Complex.GammaSeq z N)⁻¹
      = z * Complex.exp
        ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z)
      * ∏ n ∈ Finset.range N, (1 + cV n z) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact Jb hz hN
  exact tendsto_nhds_unique (hL.congr' heq) hRHS
lemma nF {z : ℂ} (hz : z ∈ Complex.integerComplement) (n : ℕ) :
    logDeriv (fun s => 1 + cV n s) z = 1 / (z + n + 1) - 1 / ((n : ℂ) + 1) := by
  have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
    have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
    push_cast at this ⊢
    convert this using 2
  have Wk : z + (n : ℂ) + 1 ≠ 0 := by
    rw [add_assoc]
    exact hzn
  have hfun : (fun s => 1 + cV n s)
      = fun s : ℂ => (1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) := by
    funext s
    exact rF n s
  rw [hfun]
  have h1z : (1 + z / ((n : ℂ) + 1)) ≠ 0 := by
    intro h
    apply hzn
    have h2 := congrArg (fun t => t * ((n : ℂ) + 1)) h
    simp only [add_mul, one_mul, zero_mul] at h2
    rw [div_mul_cancel₀ _ hn1] at h2
    rw [← h2]
    ring
  have hd1 : HasDerivAt (fun s : ℂ => 1 + s / ((n : ℂ) + 1)) (1 / ((n : ℂ) + 1)) z := by
    have h3 := ((hasDerivAt_id z).div_const ((n : ℂ) + 1)).const_add 1
    simpa [one_div] using h3
  have hd2 : HasDerivAt (fun s : ℂ => Complex.exp (-(s / ((n : ℂ) + 1))))
      (-(1 / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1)))) z := by
    have hlin : HasDerivAt (fun s : ℂ => -(s / ((n : ℂ) + 1))) (-(1 / ((n : ℂ) + 1))) z := by
      exact ((hasDerivAt_id z).div_const ((n : ℂ) + 1)).neg
    have h5 := hlin.cexp
    simpa [mul_comm] using h5
  have hprod : HasDerivAt
      (fun s : ℂ => (1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))))
      (1 / ((n : ℂ) + 1) * Complex.exp (-(z / ((n : ℂ) + 1)))
        + (1 + z / ((n : ℂ) + 1)) * (-(1 / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))))) z :=
    hd1.mul hd2
  unfold logDeriv
  rw [Pi.div_apply, hprod.deriv]
  have abI : Complex.exp (-(z / ((n : ℂ) + 1))) ≠ 0 := Complex.exp_ne_zero _
  have h3 : (1 : ℂ) + (n : ℂ) + z ≠ 0 := by
    intro h
    apply Wk
    linear_combination h
  field_simp [h3]
  have h4 : ((1 : ℂ) + (n : ℂ) + z) * ((1 + (n : ℂ) + z)⁻¹) = 1 := mul_inv_cancel₀ h3
  linear_combination (-z) * h4
theorem gQ {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
  refine Summable.of_norm ?_
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℕ => 2 * ‖z‖ * ((((n : ℝ) + 1) ^ 2)⁻¹)) ?_ ?_
  · have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
      have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
        have h3 := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
        have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
          funext n
          rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rwa [heq] at h3
      have h4 := (summable_nat_add_iff 1).mpr h2
      simpa [add_comm] using h4
    exact h1.mul_left _
  · rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_ge_atTop ⌈2 * ‖z‖⌉₊] with n hn
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
      have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
      push_cast at this ⊢
      convert this using 2
    have Wk : z + (n : ℂ) + 1 ≠ 0 := by
      rw [add_assoc]
      exact hzn
    have hident : 1 / ((n : ℂ) + 1) - 1 / (z + n + 1)
        = z / (((n : ℂ) + 1) * (z + n + 1)) := by
      field_simp
      ring
    have h2n : 2 * ‖z‖ ≤ (n : ℝ) := by
      calc 2 * ‖z‖ ≤ (⌈2 * ‖z‖⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (n : ℝ) := by exact_mod_cast hn
    have hlow : ((n : ℝ) + 1) / 2 ≤ ‖z + (n : ℂ) + 1‖ := by
      have h1 : ‖((n : ℂ) + 1)‖ - ‖z‖ ≤ ‖z + (n : ℂ) + 1‖ := by
        have h2 := norm_sub_le (z + (n : ℂ) + 1) z
        have h3 : (z + (n : ℂ) + 1) - z = ((n : ℂ) + 1) := by ring
        rw [h3] at h2
        linarith
      rw [jW] at h1
      linarith [norm_nonneg z]
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hident, norm_div, norm_mul,
      jW]
    calc ‖z‖ / (((n : ℝ) + 1) * ‖z + (n : ℂ) + 1‖)
        ≤ ‖z‖ / (((n : ℝ) + 1) * (((n : ℝ) + 1) / 2)) := by
          gcongr
      _ = 2 * ‖z‖ * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
          field_simp
theorem fG {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1))
      (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z) := by
  set γc : ℂ := ((Real.eulerMascheroniConstant : ℝ) : ℂ) with MZ
  have hz0 : z ≠ 0 := Complex.integerComplement.ne_zero hz
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have wO : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hzero
  have zj : IsOpen Complex.integerComplement := isOpen_compl_range_intCast
  set U : Set ℂ := Metric.ball (0 : ℂ) (‖z‖ + 1) with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := by
    rw [hU, Metric.mem_ball, dist_zero_right]
    linarith [norm_nonneg z]
  have htend : MultipliableLocallyUniformlyOn (fun n (s : ℂ) => 1 + cV n s) U := by
    refine Summable.multipliableLocallyUniformlyOn_nat_one_add hUopen
      (wN (‖z‖ + 1)) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop ⌈‖z‖ + 1⌉₊] with n hn x hx
      have hx1 : ‖x‖ ≤ ‖z‖ + 1 := by
        rw [hU, Metric.mem_ball, dist_zero_right] at hx
        linarith
      have hn1 : ‖z‖ + 1 ≤ (n : ℝ) + 1 := by
        calc ‖z‖ + 1 ≤ (⌈‖z‖ + 1⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn
          _ ≤ (n : ℝ) + 1 := by linarith
      calc ‖cV n x‖ ≤ 3 * (‖x‖ / ((n : ℝ) + 1)) ^ 2 :=
            AO (le_trans hx1 hn1)
        _ ≤ 3 * ((‖z‖ + 1) / ((n : ℝ) + 1)) ^ 2 := by
            gcongr
    · intro n
      have hc : Continuous (cV n) := by
        unfold cV
        fun_prop
      exact hc.continuousOn
  have hfne : ∀ n : ℕ, (fun s : ℂ => 1 + cV n s) z ≠ 0 := by
    intro n
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
      have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
      push_cast at this ⊢
      convert this using 2
    simp only [rF]
    apply mul_ne_zero _ (Complex.exp_ne_zero _)
    intro h
    apply hzn
    have h2 := congrArg (fun t => t * ((n : ℂ) + 1)) h
    simp only [add_mul, one_mul, zero_mul] at h2
    rw [div_mul_cancel₀ _ hn1] at h2
    rw [← h2]
    ring
  have hgne : z * Complex.exp (γc * z) ≠ 0 := mul_ne_zero hz0 (Complex.exp_ne_zero _)
  have Wn : (∏' n : ℕ, (1 + cV n z)) ≠ 0 := by
    intro h
    have h2 := lZ hz
    rw [← MZ, h, mul_zero] at h2
    exact inv_ne_zero wO h2
  have Dj : Summable fun n : ℕ => logDeriv (fun s => 1 + cV n s) z := by
    have hcongr : (fun n : ℕ => logDeriv (fun s => 1 + cV n s) z)
        = fun n : ℕ => -(1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
      funext n
      rw [nF hz n]
      ring
    rw [hcongr]
    exact (gQ hz).neg
  have Yy : logDeriv (fun s => ∏' n : ℕ, (1 + cV n s)) z
      = ∑' n : ℕ, logDeriv (fun s => 1 + cV n s) z := by
    refine logDeriv_tprod_eq_tsum hUopen hzU hfne ?_ Dj htend Wn
    intro n
    have hd : Differentiable ℂ fun s : ℂ => 1 + cV n s := by
      unfold cV
      fun_prop
    exact hd.differentiableOn
  have Rz : Differentiable ℂ fun s : ℂ => s * Complex.exp (γc * s) := by
    fun_prop
  have Dk : DifferentiableAt ℂ (fun s => ∏' n : ℕ, (1 + cV n s)) z := by
    have hev : (fun s : ℂ => (Complex.Gamma s)⁻¹ / (s * Complex.exp (γc * s)))
        =ᶠ[nhds z] (fun s => ∏' n : ℕ, (1 + cV n s)) := by
      filter_upwards [zj.mem_nhds hz] with s hs
      have h2 := lZ hs
      rw [← MZ] at h2
      have hsne : s * Complex.exp (γc * s) ≠ 0 :=
        mul_ne_zero (Complex.integerComplement.ne_zero hs) (Complex.exp_ne_zero _)
      rw [h2]
      exact mul_div_cancel_left₀ _ hsne
    have hd : DifferentiableAt ℂ
        (fun s : ℂ => (Complex.Gamma s)⁻¹ / (s * Complex.exp (γc * s))) z := by
      refine DifferentiableAt.div ?_ (Rz z) hgne
      exact Complex.differentiable_one_div_Gamma z
    exact hd.congr_of_eventuallyEq hev.symm
  have Wq : logDeriv (fun s => (Complex.Gamma s)⁻¹) z = -Complex.digamma z := by
    have h1 : logDeriv ((·⁻¹) ∘ Complex.Gamma) z
        = logDeriv (·⁻¹) (Complex.Gamma z) * deriv Complex.Gamma z := by
      refine logDeriv_comp ?_ (Complex.differentiableAt_Gamma z hzero)
      exact differentiableAt_inv wO
    rw [show (fun s => (Complex.Gamma s)⁻¹) = (·⁻¹) ∘ Complex.Gamma from rfl, h1, logDeriv_inv]
    rw [Complex.digamma_def, logDeriv_apply]
    field_simp
  have PY : (fun s => (Complex.Gamma s)⁻¹)
      =ᶠ[nhds z] fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + cV n s) := by
    filter_upwards [zj.mem_nhds hz] with s hs
    have h2 := lZ hs
    rw [← MZ] at h2
    rw [h2]
  have Wr : logDeriv (fun s => (Complex.Gamma s)⁻¹) z
      = logDeriv (fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + cV n s)) z := by
    unfold logDeriv
    rw [Pi.div_apply, Pi.div_apply, PY.deriv_eq, PY.eq_of_nhds]
  have hmul : logDeriv (fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + cV n s)) z
      = logDeriv (fun s : ℂ => s * Complex.exp (γc * s)) z
        + logDeriv (fun s => ∏' n : ℕ, (1 + cV n s)) z :=
    logDeriv_mul z hgne Wn (Rz z) Dk
  have aai : logDeriv (fun s : ℂ => s * Complex.exp (γc * s)) z = 1 / z + γc := by
    have hder : HasDerivAt (fun s : ℂ => s * Complex.exp (γc * s))
        (1 * Complex.exp (γc * z) + z * (γc * Complex.exp (γc * z))) z := by
      have h1 : HasDerivAt (fun s : ℂ => Complex.exp (γc * s)) (γc * Complex.exp (γc * z)) z := by
        have hlin : HasDerivAt (fun s : ℂ => γc * s) γc z := by
          simpa using (hasDerivAt_id z).const_mul γc
        have h5 := hlin.cexp
        simpa [mul_comm] using h5
      exact (hasDerivAt_id z).mul h1
    unfold logDeriv
    rw [Pi.div_apply, hder.deriv]
    have he : Complex.exp (γc * z) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  have hmain : -Complex.digamma z
      = (1 / z + γc) + ∑' n : ℕ, logDeriv (fun s => 1 + cV n s) z := by
    rw [← Wq, Wr, hmul, aai, Yy]
  have Yz : ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1))
      = Complex.digamma z + γc + 1 / z := by
    have h1 : ∑' n : ℕ, logDeriv (fun s => 1 + cV n s) z
        = ∑' n : ℕ, -(1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
      congr 1
      funext n
      rw [nF hz n]
      ring
    rw [h1, tsum_neg] at hmain
    linear_combination hmain
  have h := (gQ hz).hasSum
  rwa [Yz] at h
theorem Kz {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Complex.digamma z = -(Real.eulerMascheroniConstant : ℂ) - 1 / z
      + ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
  rw [(fG hz).tsum_eq]
  ring
end fF
end Zeta23
end
end

-- Zeta23.Analytic.Stirling
section
noncomputable section
namespace Zeta23
namespace Stirling
open Complex Filter Topology
theorem lC {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    DifferentiableAt ℂ Complex.digamma z := by
  have zj : IsOpen Complex.integerComplement := isOpen_compl_range_intCast
  have oQ : AnalyticAt ℂ Complex.Gamma z := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [zj.mem_nhds hz] with w hw
    refine Complex.differentiableAt_Gamma w fun m => ?_
    intro h
    exact hw ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have wO : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hzero
  have Je : AnalyticAt ℂ Complex.digamma z := by
    have h1 : AnalyticAt ℂ (deriv Complex.Gamma) z := oQ.deriv
    have h2 := h1.div oQ wO
    exact h2.congr (by
      filter_upwards with w
      rw [Complex.digamma_def, logDeriv_apply]
      rfl)
  exact Je.differentiableAt
theorem Jg {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    HasSum (fun n : ℕ => 1 / (z + n) ^ 2) (deriv Complex.digamma z) := by
  have zj : IsOpen Complex.integerComplement := isOpen_compl_range_intCast
  obtain ⟨ε, hε0, hball⟩ := Metric.isOpen_iff.mp zj z hz
  have hr0 : 0 < ε / 2 := by positivity
  set U : Set ℂ := Metric.ball z (ε / 2) with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := Metric.mem_ball_self hr0
  have hUsub : U ⊆ Complex.integerComplement :=
    subset_trans (Metric.ball_subset_ball (by linarith)) hball
  have hδ : ∀ n : ℕ, ε / 2 < ‖z + ((n : ℂ) + 1)‖ := by
    intro n
    by_contra hle
    push Not at hle
    have hmem : (-(((n : ℂ)) + 1)) ∈ Metric.ball z ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖-((n : ℂ) + 1) - z‖ = ‖z + ((n : ℂ) + 1)‖ := by
            rw [show -((n : ℂ) + 1) - z = -(z + ((n : ℂ) + 1)) by ring, norm_neg]
        _ ≤ ε / 2 := hle
        _ < ε := by linarith
    exact (hball hmem) ⟨-((n : ℤ) + 1), by push_cast; ring⟩
  set F : ℕ → ℂ → ℂ := fun n w => 1 / ((n : ℂ) + 1) - 1 / (w + n + 1) with hF
  set u : ℕ → ℝ := fun n =>
    (‖z‖ + ε / 2) / (((n : ℝ) + 1) * (‖z + ((n : ℂ) + 1)‖ - ε / 2)) with hu
  have OL : ∀ n : ℕ, ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    intro n
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have FL : ∀ (n : ℕ) (w : ℂ), w ∈ U → w + ((n : ℂ) + 1) ≠ 0 := by
    intro n w hw h0
    have hwz : ‖w - z‖ < ε / 2 := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hw
    have h1 : ‖z + ((n : ℂ) + 1)‖ = ‖z - w‖ := by
      rw [show z + ((n : ℂ) + 1) = (z - w) + (w + ((n : ℂ) + 1)) by ring, h0, add_zero]
    rw [norm_sub_rev] at h1
    have := hδ n
    linarith
  have hlow : ∀ (n : ℕ) (w : ℂ), w ∈ U →
      ‖z + ((n : ℂ) + 1)‖ - ε / 2 ≤ ‖w + ((n : ℂ) + 1)‖ := by
    intro n w hw
    have hwz : ‖z - w‖ < ε / 2 := by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact Metric.mem_ball.mp hw
    have h1 : ‖z + ((n : ℂ) + 1)‖ ≤ ‖w + ((n : ℂ) + 1)‖ + ‖z - w‖ := by
      calc ‖z + ((n : ℂ) + 1)‖ = ‖(w + ((n : ℂ) + 1)) + (z - w)‖ := by ring_nf
        _ ≤ ‖w + ((n : ℂ) + 1)‖ + ‖z - w‖ := norm_add_le _ _
    linarith
  have aaj : ∀ (n : ℕ) (w : ℂ), w ∈ U → ‖F n w‖ ≤ u n := by
    intro n w hw
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hw0 := FL n w hw
    have acO : w + (n : ℂ) + 1 ≠ 0 := by
      rw [add_assoc]
      exact hw0
    have hident : F n w = w / (((n : ℂ) + 1) * (w + ((n : ℂ) + 1))) := by
      rw [hF]
      simp only
      rw [show w + ((n : ℂ) + 1) = w + (n : ℂ) + 1 by ring]
      field_simp
      ring
    have hwb : ‖w‖ ≤ ‖z‖ + ε / 2 := by
      have hwz : ‖w - z‖ < ε / 2 := by
        rw [← dist_eq_norm]
        exact Metric.mem_ball.mp hw
      calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ε / 2 := by linarith
    have hdl := hlow n w hw
    have YA : (0 : ℝ) < ‖z + ((n : ℂ) + 1)‖ - ε / 2 := by
      have := hδ n
      linarith
    rw [hident, norm_div, norm_mul, OL n, hu]
    simp only
    gcongr
  have YB : Summable u := by
    refine Summable.of_norm_bounded_eventually
      (g := fun n : ℕ => 2 * (‖z‖ + ε / 2) * ((((n : ℝ) + 1) ^ 2)⁻¹)) ?_ ?_
    · have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
        have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
          have h3 := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
          have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
            funext n
            rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          rwa [heq] at h3
        have h4 := (summable_nat_add_iff 1).mpr h2
        simpa [add_comm] using h4
      exact h1.mul_left _
    · rw [Nat.cofinite_eq_atTop]
      filter_upwards [Filter.eventually_ge_atTop ⌈2 * (‖z‖ + ε / 2 + 1)⌉₊] with n hn
      have hn2 : 2 * (‖z‖ + ε / 2 + 1) ≤ (n : ℝ) := by
        calc 2 * (‖z‖ + ε / 2 + 1) ≤ (⌈2 * (‖z‖ + ε / 2 + 1)⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn
      have hzn : ((n : ℝ) + 1) / 2 ≤ ‖z + ((n : ℂ) + 1)‖ - ε / 2 := by
        have h1 : ‖((n : ℂ) + 1)‖ - ‖z‖ ≤ ‖z + ((n : ℂ) + 1)‖ := by
          have h2 := norm_sub_le (z + ((n : ℂ) + 1)) z
          have h3 : (z + ((n : ℂ) + 1)) - z = ((n : ℂ) + 1) := by ring
          rw [h3] at h2
          linarith
        rw [OL n] at h1
        have hz0 := norm_nonneg z
        linarith
      have YA : (0 : ℝ) < ‖z + ((n : ℂ) + 1)‖ - ε / 2 := by
        have h0 : (0 : ℝ) < ((n : ℝ) + 1) / 2 := by positivity
        linarith
      rw [hu, Real.norm_eq_abs]
      simp only
      rw [abs_of_nonneg (by positivity)]
      calc (‖z‖ + ε / 2) / (((n : ℝ) + 1) * (‖z + ((n : ℂ) + 1)‖ - ε / 2))
          ≤ (‖z‖ + ε / 2) / (((n : ℝ) + 1) * (((n : ℝ) + 1) / 2)) := by
            gcongr
        _ = 2 * (‖z‖ + ε / 2) * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
            field_simp
  have Ws : ∀ n : ℕ, DifferentiableOn ℂ (F n) U := by
    intro n
    rw [hF]
    simp only
    intro w hw
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.sub (differentiableAt_const _) ?_
    have hne : w + (n : ℂ) + 1 ≠ 0 := by
      rw [add_assoc]
      exact FL n w hw
    have h1 : DifferentiableAt ℂ (fun v : ℂ => v + (n : ℂ) + 1) w := by
      fun_prop
    exact (differentiableAt_const (1 : ℂ)).div h1 hne
  have hkey := hasSum_deriv_of_summable_norm YB Ws hUopen aaj hzU
  have YC : ∀ n : ℕ, F n = fun w => 1 / ((n : ℂ) + 1) - 1 / (w + ((n : ℂ) + 1)) := by
    intro n
    funext w
    rw [hF]
    simp only
    rw [add_assoc]
  have Oj : ∀ n : ℕ, deriv (F n) z = 1 / (z + ((n : ℂ) + 1)) ^ 2 := by
    intro n
    rw [YC n]
    have hne : z + ((n : ℂ) + 1) ≠ 0 := FL n z hzU
    have h1 : HasDerivAt (fun w : ℂ => w + ((n : ℂ) + 1)) 1 z := (hasDerivAt_id z).add_const _
    have h2 := h1.inv hne
    have h3 : HasDerivAt (fun w : ℂ => (w + ((n : ℂ) + 1))⁻¹)
        (-1 / (z + ((n : ℂ) + 1)) ^ 2) z := h2
    have h5 := h3.const_sub (1 / ((n : ℂ) + 1))
    have h6 : (fun w : ℂ => 1 / ((n : ℂ) + 1) - (w + ((n : ℂ) + 1))⁻¹)
        = fun w : ℂ => 1 / ((n : ℂ) + 1) - 1 / (w + ((n : ℂ) + 1)) := by
      funext w
      simp [one_div]
    rw [← h6]
    have h7 : HasDerivAt (fun w : ℂ => 1 / ((n : ℂ) + 1) - (w + ((n : ℂ) + 1))⁻¹)
        (1 / (z + ((n : ℂ) + 1)) ^ 2) z := by
      have heq : 1 / (z + ((n : ℂ) + 1)) ^ 2 = -(-1 / (z + ((n : ℂ) + 1)) ^ 2) := by
        ring
      rw [heq]
      exact h5
    exact h7.deriv
  have MZ : ∀ w : ℂ, w ∈ U → (∑' n : ℕ, F n w)
      = Complex.digamma w + (Real.eulerMascheroniConstant : ℂ) + 1 / w := by
    intro w hw
    exact (Zeta23.fF.fG (hUsub hw)).tsum_eq
  have KD : (fun w : ℂ => ∑' n : ℕ, F n w)
      =ᶠ[nhds z] fun w => Complex.digamma w + (Real.eulerMascheroniConstant : ℂ) + 1 / w := by
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    exact MZ w hw
  have hz0 : z ≠ 0 := Complex.integerComplement.ne_zero hz
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have oQ : AnalyticAt ℂ Complex.Gamma z := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    refine Complex.differentiableAt_Gamma w fun m => ?_
    intro h
    exact (hUsub hw) ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have wO : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hzero
  have Je : AnalyticAt ℂ Complex.digamma z := by
    have h1 : AnalyticAt ℂ (deriv Complex.Gamma) z := oQ.deriv
    have h2 := h1.div oQ wO
    exact h2.congr (by
      filter_upwards with w
      rw [Complex.digamma_def, logDeriv_apply]
      rfl)
  have SZ : DifferentiableAt ℂ Complex.digamma z := Je.differentiableAt
  have YD : HasDerivAt (fun w : ℂ => 1 / w) (-1 / z ^ 2) z := by
    have h1 := (hasDerivAt_id z).inv hz0
    have h2 : HasDerivAt (fun w : ℂ => w⁻¹) (-1 / z ^ 2) z := h1
    have h3 : (fun w : ℂ => 1 / w) = fun w : ℂ => w⁻¹ := by
      funext w
      rw [one_div]
    rw [h3]
    exact h2
  have YF : HasDerivAt
      (fun w => Complex.digamma w + (Real.eulerMascheroniConstant : ℂ) + 1 / w)
      (deriv Complex.digamma z + (-1 / z ^ 2)) z := by
    exact (SZ.hasDerivAt.add_const ((Real.eulerMascheroniConstant : ℝ) : ℂ)).add YD
  have PZ : deriv (fun w : ℂ => ∑' n : ℕ, F n w) z
      = deriv Complex.digamma z + (-1 / z ^ 2) := by
    rw [KD.deriv_eq]
    exact YF.deriv
  rw [PZ] at hkey
  have hfun : (fun n : ℕ => deriv (F n) z)
      = fun n : ℕ => 1 / (z + ((n : ℂ) + 1)) ^ 2 := funext Oj
  rw [hfun] at hkey
  have hshift : (fun n : ℕ => 1 / (z + ((n : ℂ) + 1)) ^ 2)
      = fun n : ℕ => (fun m : ℕ => 1 / (z + (m : ℂ)) ^ 2) (n + 1) := by
    funext n
    simp only
    push_cast
    ring_nf
  rw [hshift] at hkey
  have h0 : (fun m : ℕ => 1 / (z + (m : ℂ)) ^ 2) 0 = 1 / z ^ 2 := by
    simp
  have hfin := (hasSum_nat_add_iff (f := fun m : ℕ => 1 / (z + (m : ℂ)) ^ 2) 1).mp hkey
  have hval : deriv Complex.digamma z + -1 / z ^ 2
      + ∑ i ∈ Finset.range 1, (fun m : ℕ => 1 / (z + (m : ℂ)) ^ 2) i
      = deriv Complex.digamma z := by
    rw [Finset.sum_range_one]
    have h00 : (1 : ℂ) / (z + ((0 : ℕ) : ℂ)) ^ 2 = 1 / z ^ 2 := by
      norm_num
    rw [h00]
    ring
  rwa [hval] at hfin
end Stirling
end Zeta23
end
end

-- Zeta23.gX.Mu
section
noncomputable section
namespace Zeta23
namespace lD
open Complex Filter Topology
variable {a : ℝ}
lemma vI (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    ((a : ℂ) + Complex.I * (t : ℂ)) ∈ Complex.integerComplement := by
  rintro ⟨k, hk⟩
  have hre := congrArg Complex.re hk
  simp at hre
  have h0 : (0 : ℤ) < k := by
    have h : (0 : ℝ) < (k : ℝ) := by rw [hre]; exact ha0
    exact_mod_cast h
  have h1 : k < 1 := by
    have h : (k : ℝ) < 1 := by rw [hre]; exact ha1
    exact_mod_cast h
  omega
lemma Jh (t : ℝ) (n : ℕ) :
    ((1 : ℂ) / ((n : ℂ) + 1) - 1 / (((a : ℂ) + Complex.I * t) + n + 1)).re
      = 1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2) := by
  rw [Complex.sub_re]
  congr 1
  · rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      show (1 : ℂ) / ((((n : ℝ) + 1 : ℝ)) : ℂ) = ((((1 : ℝ) / ((n : ℝ) + 1)) : ℝ) : ℂ) by
        push_cast
        ring]
    exact Complex.ofReal_re _
  · rw [one_div, Complex.inv_re]
    have hre : (((a : ℂ) + Complex.I * t) + n + 1).re = (n : ℝ) + 1 + a := by
      simp
      ring
    have him : (((a : ℂ) + Complex.I * t) + n + 1).im = t := by simp
    rw [hre, Complex.normSq_apply, hre, him]
    ring
lemma RA (t : ℝ) :
    ((1 : ℂ) / ((a : ℂ) + Complex.I * t)).re = a / (a ^ 2 + t ^ 2) := by
  rw [one_div, Complex.inv_re]
  have hre : ((a : ℂ) + Complex.I * t).re = a := by simp
  have him : ((a : ℂ) + Complex.I * t).im = t := by simp
  rw [hre, Complex.normSq_apply, hre, him]
  ring
lemma mo (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    Summable (fun n : ℕ =>
      1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2)) := by
  have hs := Zeta23.fF.gQ (vI ha0 ha1 t)
  have hmap := hs.map Complex.reCLM Complex.continuous_re
  refine hmap.congr fun n => ?_
  exact Jh t n
theorem jf (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    (Complex.digamma ((a : ℂ) + Complex.I * t)).re
      = -Real.eulerMascheroniConstant - a / (a ^ 2 + t ^ 2)
        + ∑' n : ℕ,
          (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2)) := by
  have hmem := vI ha0 ha1 t
  have h := Zeta23.fF.Kz hmem
  have hre := congrArg Complex.re h
  rw [hre]
  rw [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
  congr 1
  · congr 1
    exact RA t
  · 
    have hs := Zeta23.fF.gQ hmem
    have hmap := Complex.reCLM.map_tsum hs
    rw [show (∑' n : ℕ, ((1 : ℂ) / ((n : ℂ) + 1)
        - 1 / (((a : ℂ) + Complex.I * t) + n + 1))).re
      = Complex.reCLM (∑' n : ℕ, ((1 : ℂ) / ((n : ℂ) + 1)
        - 1 / (((a : ℂ) + Complex.I * t) + n + 1))) from rfl, hmap]
    congr 1
    funext n
    exact Jh t n
theorem Jj (ha0 : 0 < a) (ha1 : a < 1) :
    MonotoneOn (fun t : ℝ => (Complex.digamma ((a : ℂ) + Complex.I * t)).re)
      (Set.Ici (0 : ℝ)) := by
  intro t₁ h₁ t₂ h₂ h12
  simp only
  rw [jf ha0 ha1, jf ha0 ha1]
  have ht1 : (0 : ℝ) ≤ t₁ := h₁
  have hsq : t₁ ^ 2 ≤ t₂ ^ 2 := by nlinarith
  have abJ : a / (a ^ 2 + t₂ ^ 2) ≤ a / (a ^ 2 + t₁ ^ 2) :=
    div_le_div_of_nonneg_left ha0.le (by positivity) (by linarith)
  have hterm : ∀ n : ℕ,
      (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t₁ ^ 2))
        ≤ 1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t₂ ^ 2) := by
    intro n
    have hna : (0 : ℝ) < (n : ℝ) + 1 + a := by positivity
    have h2 : ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t₂ ^ 2)
        ≤ ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t₁ ^ 2) :=
      div_le_div_of_nonneg_left hna.le (by positivity) (by linarith)
    linarith
  have hsum := (mo ha0 ha1 t₁).tsum_le_tsum hterm
    (mo ha0 ha1 t₂)
  linarith
lemma Mb (τ : ℝ) :
    Zeta23.mu τ = (1 / (2 * Real.pi))
        * (Complex.digamma ((((1 : ℝ) / 4 : ℝ) : ℂ) + Complex.I * ((τ / 2 : ℝ) : ℂ))).re
      - Real.log Real.pi / (2 * Real.pi) := by
  unfold Zeta23.mu
  congr 3
  push_cast
  ring
theorem rH : MonotoneOn Zeta23.mu (Set.Ici (0 : ℝ)) := by
  intro t₁ h₁ t₂ h₂ h12
  rw [Mb, Mb]
  have hmono := Jj (a := 1 / 4) (by norm_num) (by norm_num)
    (Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp h₁] : (0 : ℝ) ≤ t₁ / 2))
    (Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp h₂] : (0 : ℝ) ≤ t₂ / 2))
    (by linarith)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2π : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  have := mul_le_mul_of_nonneg_left hmono h2π
  linarith
theorem GK (τ : ℝ) : Zeta23.mu 0 ≤ Zeta23.mu τ := by
  have heven := Zeta23.OJ
  rcases le_total 0 τ with h | h
  · exact rH (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h) h
  · have h1 : Zeta23.mu τ = Zeta23.mu (-τ) := (heven τ).symm
    rw [h1]
    exact rH (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (by linarith)) (by linarith)
theorem qK : (-1 : ℝ) < Zeta23.mu 0 := by
  rw [Mb]
  rw [show ((0 : ℝ) / 2 : ℝ) = (0 : ℝ) by norm_num]
  have hre := jf (a := 1 / 4) (by norm_num) (by norm_num) 0
  rw [hre]
  have hS : (0 : ℝ) ≤ ∑' n : ℕ,
      (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + 1 / 4) / (((n : ℝ) + 1 + 1 / 4) ^ 2 + (0 : ℝ) ^ 2)) := by
    refine tsum_nonneg fun n => ?_
    have hna : (0 : ℝ) < (n : ℝ) + 1 + 1 / 4 := by positivity
    have h1 : ((n : ℝ) + 1 + 1 / 4) / (((n : ℝ) + 1 + 1 / 4) ^ 2 + (0 : ℝ) ^ 2)
        = 1 / ((n : ℝ) + 1 + 1 / 4) := by
      rw [show (((n : ℝ) + 1 + 1 / 4) ^ 2 + (0 : ℝ) ^ 2) = ((n : ℝ) + 1 + 1 / 4) ^ 2 by ring]
      rw [sq]
      rw [div_mul_eq_div_div]
      rw [div_self hna.ne']
    rw [h1]
    have h2 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h3 : 1 / ((n : ℝ) + 1 + 1 / 4) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le h2 (by linarith)
    linarith
  have hγ : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  have Wt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have Wv : Real.pi < 4 := Real.pi_lt_four
  have Jm : Real.log Real.pi < 1.4 := by
    have h1 : Real.log Real.pi < Real.log 4 := Real.log_lt_log Real.pi_pos Wv
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have h3 := Real.log_two_lt_d9
    nlinarith
  have Tf : (1 / 4 : ℝ) / ((1 / 4 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = 4 := by norm_num
  rw [Tf]
  set S : ℝ := ∑' n : ℕ,
    (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + 1 / 4) / (((n : ℝ) + 1 + 1 / 4) ^ 2 + (0 : ℝ) ^ 2))
    with hSdef
  have YG : 1 / (2 * Real.pi) * (-Real.eulerMascheroniConstant - 4 + S)
        - Real.log Real.pi / (2 * Real.pi)
      = (-Real.eulerMascheroniConstant - 4 + S - Real.log Real.pi) * (1 / (2 * Real.pi)) := by
    ring
  rw [YG]
  have hX : -(2 * Real.pi)
      < -Real.eulerMascheroniConstant - 4 + S - Real.log Real.pi := by
    have hnorm : (1.4 : ℝ) = 14 / 10 := by norm_num
    linarith
  calc (-1 : ℝ) = -(2 * Real.pi) * (1 / (2 * Real.pi)) := by
        field_simp
    _ < (-Real.eulerMascheroniConstant - 4 + S - Real.log Real.pi) * (1 / (2 * Real.pi)) :=
        mul_lt_mul_of_pos_right hX (by positivity)
lemma FN {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    ∑' n : ℕ, (((1 / 4 : ℝ) + n) ^ 2 + t ^ 2)⁻¹ ≤ 12 / |t| := by
  have ht0 : (0 : ℝ) < |t| := by linarith
  have acP : (0 : ℝ) < t ^ 2 := by
    have := sq_abs t
    nlinarith
  set N : ℕ := ⌈|t|⌉₊ + 2 with hN
  have hNt : |t| ≤ (N : ℝ) := by
    calc |t| ≤ (⌈|t|⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (N : ℝ) := by
          rw [hN]
          push_cast
          linarith
  have acQ : (N : ℝ) ≤ |t| + 3 := by
    rw [hN]
    push_cast
    have := Nat.ceil_lt_add_one (abs_nonneg t)
    linarith
  have Dj : Summable (fun n : ℕ => (((1 / 4 : ℝ) + n) ^ 2 + t ^ 2)⁻¹) := by
    refine Summable.of_norm_bounded_eventually
      (g := fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) ?_ ?_
    · have h3 := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
      have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
        funext n
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rwa [heq] at h3
    · rw [Nat.cofinite_eq_atTop]
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
      nlinarith
  rw [← Dj.sum_add_tsum_nat_add N]
  have hhead : ∑ i ∈ Finset.range N, (((1 / 4 : ℝ) + i) ^ 2 + t ^ 2)⁻¹
      ≤ (N : ℝ) * (t ^ 2)⁻¹ := by
    have h1 : ∀ i ∈ Finset.range N, (((1 / 4 : ℝ) + i) ^ 2 + t ^ 2)⁻¹ ≤ (t ^ 2)⁻¹ := by
      intro i _
      gcongr
      nlinarith [sq_nonneg ((1 / 4 : ℝ) + i)]
    calc ∑ i ∈ Finset.range N, (((1 / 4 : ℝ) + i) ^ 2 + t ^ 2)⁻¹
        ≤ ∑ _i ∈ Finset.range N, (t ^ 2)⁻¹ := Finset.sum_le_sum h1
      _ = (N : ℝ) * (t ^ 2)⁻¹ := by
          rw [Finset.sum_const, Finset.card_range]
          simp [nsmul_eq_mul]
  have htail : ∑' i : ℕ, (((1 / 4 : ℝ) + ((i + N : ℕ) : ℝ)) ^ 2 + t ^ 2)⁻¹
      ≤ ((N : ℝ) - 1)⁻¹ := by
    have hN2 : (2 : ℕ) ≤ N := by
      rw [hN]
      omega
    push_cast
    refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun K => ?_
    have hterm : ∀ i : ℕ, (((1 / 4 : ℝ) + (i + N)) ^ 2 + t ^ 2)⁻¹
        ≤ ((i : ℝ) + N - 1)⁻¹ - ((i : ℝ) + N)⁻¹ := by
      intro i
      have acR : (1 : ℝ) ≤ (i : ℝ) + N - 1 := by
        have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
        have := Nat.cast_nonneg (α := ℝ) i
        linarith
      have hpos1 : (0 : ℝ) < (i : ℝ) + N - 1 := by linarith
      have Ur : (0 : ℝ) < (i : ℝ) + N := by linarith
      have hsub : ((i : ℝ) + N - 1)⁻¹ - ((i : ℝ) + N)⁻¹
          = (((i : ℝ) + N - 1) * ((i : ℝ) + N))⁻¹ := by
        rw [inv_sub_inv hpos1.ne' Ur.ne']
        ring_nf
      rw [hsub]
      have hd1 : (0 : ℝ) < ((i : ℝ) + N - 1) * ((i : ℝ) + N) := mul_pos hpos1 Ur
      have hd2 : ((i : ℝ) + N - 1) * ((i : ℝ) + N)
          ≤ ((1 / 4 : ℝ) + ((i : ℝ) + (N : ℝ))) ^ 2 + t ^ 2 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) i, sq_nonneg t]
      have h3 := one_div_le_one_div_of_le hd1 hd2
      simpa [one_div] using h3
    calc ∑ i ∈ Finset.range K, (((1 / 4 : ℝ) + (i + N)) ^ 2 + t ^ 2)⁻¹
        ≤ ∑ i ∈ Finset.range K, (((i : ℝ) + N - 1)⁻¹ - ((i : ℝ) + N)⁻¹) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = ((N : ℝ) - 1)⁻¹ - ((K : ℝ) + N - 1)⁻¹ := by
          have Ww := Finset.sum_range_sub' (f := fun i : ℕ => ((i : ℝ) + N - 1)⁻¹) K
          simp only [Nat.cast_zero, zero_add] at Ww
          rw [← Ww]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hx : (((i + 1 : ℕ) : ℝ) + N - 1)⁻¹ = ((i : ℝ) + N)⁻¹ := by
            push_cast
            ring_nf
          rw [hx]
      _ ≤ ((N : ℝ) - 1)⁻¹ := by
          have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
          have : (0 : ℝ) < (K : ℝ) + N - 1 := by
            have := Nat.cast_nonneg (α := ℝ) K
            linarith
          have : (0 : ℝ) ≤ ((K : ℝ) + N - 1)⁻¹ := by positivity
          linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have h2 : (2 : ℕ) ≤ N := by
      rw [hN]
      omega
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
    linarith
  have aak : |t| ≤ (N : ℝ) - 1 := by
    rw [hN]
    push_cast
    have := Nat.le_ceil |t|
    linarith
  have Wz : ((N : ℝ) - 1)⁻¹ ≤ |t|⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le ht0 aak
  have WA : (N : ℝ) * (t ^ 2)⁻¹ ≤ 10 / |t| := by
    have hts : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    rw [hts]
    rw [div_eq_mul_inv]
    have h1 : (N : ℝ) ≤ 7 * |t| := by linarith
    calc (N : ℝ) * ((|t| ^ 2)⁻¹) ≤ 7 * |t| * ((|t| ^ 2)⁻¹) := by
          gcongr
      _ = 7 * |t|⁻¹ := by
          field_simp
      _ ≤ 10 * |t|⁻¹ := by
          have : (0 : ℝ) ≤ |t|⁻¹ := by positivity
          linarith
  calc (∑ i ∈ Finset.range N, (((1 / 4 : ℝ) + i) ^ 2 + t ^ 2)⁻¹)
        + ∑' i : ℕ, (((1 / 4 : ℝ) + ((i + N : ℕ) : ℝ)) ^ 2 + t ^ 2)⁻¹
      ≤ (N : ℝ) * (t ^ 2)⁻¹ + ((N : ℝ) - 1)⁻¹ := add_le_add hhead htail
    _ ≤ 10 / |t| + |t|⁻¹ := add_le_add WA Wz
    _ ≤ 12 / |t| := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have : (0 : ℝ) ≤ |t|⁻¹ := by positivity
        linarith
lemma zC (t : ℝ) :
    Summable (fun n : ℕ => (((1 / 4 : ℝ) + n) ^ 2 + t ^ 2)⁻¹) := by
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) ?_ ?_
  · have h3 := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
    have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
      funext n
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rwa [heq] at h3
  · rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    nlinarith
theorem KE : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| → |deriv Zeta23.mu τ| ≤ C / |τ| := by
  refine ⟨24 / Real.pi, fun τ hτ => ?_⟩
  have jQ : (0 : ℝ) < |τ| := by linarith
  set zA : ℂ := (1 / 4 : ℂ) + (Complex.I / 2) * (τ : ℂ) with hzA
  have Nb : zA = ((1 / 4 : ℝ) : ℂ) + Complex.I * ((τ / 2 : ℝ) : ℂ) := by
    rw [hzA]
    push_cast
    ring
  have hmem : zA ∈ Complex.integerComplement := by
    rw [Nb]
    exact vI (by norm_num) (by norm_num) (τ / 2)
  have SZ : DifferentiableAt ℂ Complex.digamma zA :=
    Zeta23.Stirling.lC hmem
  have Vg : HasDerivAt (fun x : ℝ => (1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ))
      (Complex.I / 2) τ := by
    have h1 : HasDerivAt (fun x : ℝ => ((x : ℝ) : ℂ)) 1 τ := Complex.ofRealCLM.hasDerivAt
    have h2 := (h1.const_mul (Complex.I / 2)).const_add ((1 / 4 : ℂ))
    simpa using h2
  have WB : HasDerivAt
      (fun x : ℝ => Complex.digamma ((1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ)))
      ((Complex.I / 2) • deriv Complex.digamma zA) τ := by
    have h3 := HasDerivAt.scomp τ SZ.hasDerivAt Vg
    exact h3
  have hre : HasDerivAt
      (fun x : ℝ => (Complex.digamma ((1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ))).re)
      (((Complex.I / 2) • deriv Complex.digamma zA).re) τ :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ WB)
  have aal : HasDerivAt Zeta23.mu
      (1 / (2 * Real.pi) * (((Complex.I / 2) • deriv Complex.digamma zA).re)) τ := by
    have h4 := (hre.const_mul (1 / (2 * Real.pi))).sub_const (Real.log Real.pi / (2 * Real.pi))
    have h5 : Zeta23.mu = fun x : ℝ =>
        1 / (2 * Real.pi) * (Complex.digamma ((1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ))).re
          - Real.log Real.pi / (2 * Real.pi) := by
      funext x
      unfold Zeta23.mu
      rw [show ((1 / 4 : ℂ) + Complex.I * (x : ℂ) / 2)
          = (1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ) from by ring]
    rw [h5]
    exact h4
  rw [aal.deriv]
  have htri := Zeta23.Stirling.Jg hmem
  have Jp : ∀ n : ℕ, ‖(1 : ℂ) / (zA + n) ^ 2‖
      = (((1 / 4 : ℝ) + n) ^ 2 + (τ / 2) ^ 2)⁻¹ := by
    intro n
    have Dm : (zA + n).re = (1 / 4 : ℝ) + n := by
      rw [Nb]
      simp
    have Tj : (zA + n).im = τ / 2 := by
      rw [Nb]
      simp
    rw [norm_div, norm_one, norm_pow, one_div]
    congr 1
    rw [show ‖zA + (n : ℂ)‖ ^ 2 = Complex.normSq (zA + n) from Complex.sq_norm _,
      Complex.normSq_apply, Dm, Tj]
    ring
  have KI : Summable (fun n : ℕ => ‖(1 : ℂ) / (zA + n) ^ 2‖) := by
    refine (zC (τ / 2)).congr fun n => ?_
    exact (Jp n).symm
  have ZJ : ‖deriv Complex.digamma zA‖ ≤ 24 / |τ| := by
    have h6 : deriv Complex.digamma zA = ∑' n : ℕ, (1 : ℂ) / (zA + n) ^ 2 := htri.tsum_eq.symm
    rw [h6]
    calc ‖∑' n : ℕ, (1 : ℂ) / (zA + n) ^ 2‖ ≤ ∑' n : ℕ, ‖(1 : ℂ) / (zA + n) ^ 2‖ :=
          norm_tsum_le_tsum_norm KI
      _ = ∑' n : ℕ, (((1 / 4 : ℝ) + n) ^ 2 + (τ / 2) ^ 2)⁻¹ := by
          congr 1
          funext n
          exact Jp n
      _ ≤ 12 / |τ / 2| := FN (by
          rw [abs_div]
          rw [show |(2 : ℝ)| = 2 by norm_num]
          linarith)
      _ = 24 / |τ| := by
          rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
          field_simp
          norm_num
  have hval : |(((Complex.I / 2) • deriv Complex.digamma zA).re)|
      ≤ ‖deriv Complex.digamma zA‖ / 2 := by
    calc |(((Complex.I / 2) • deriv Complex.digamma zA).re)|
        ≤ ‖(Complex.I / 2) • deriv Complex.digamma zA‖ := Complex.abs_re_le_norm _
      _ = ‖Complex.I / 2‖ * ‖deriv Complex.digamma zA‖ := norm_smul _ _
      _ = ‖deriv Complex.digamma zA‖ / 2 := by
          rw [norm_div, Complex.norm_I]
          rw [show ‖(2 : ℂ)‖ = 2 from by
            rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos (by norm_num)]]
          ring
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  calc 1 / (2 * Real.pi) * |(((Complex.I / 2) • deriv Complex.digamma zA).re)|
      ≤ 1 / (2 * Real.pi) * (‖deriv Complex.digamma zA‖ / 2) := by
        gcongr
    _ ≤ 1 / (2 * Real.pi) * ((24 / |τ|) / 2) := by
        gcongr
    _ ≤ (24 / Real.pi) / |τ| := by
        rw [div_div, div_mul_eq_mul_div, one_mul]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        ring_nf
        have e1 : Real.pi * Real.pi⁻¹ = 1 := mul_inv_cancel₀ hπ.ne'
        have e2 : |τ| * |τ|⁻¹ = 1 := mul_inv_cancel₀ jQ.ne'
        nlinarith [e1, e2]
end lD
end Zeta23
end
end

-- Zeta23.gX.oR
section
noncomputable section
namespace Zeta23
namespace oR
open Complex Filter Topology MeasureTheory intervalIntegral Set
theorem qB (c : ℂ) (f : ℝ → ℂ) (a b : ℝ) :
    ∫ x in a..b, f x * c = (∫ x in a..b, f x) * c :=
  intervalIntegral.integral_mul_const c f
theorem Dp {w : ℂ} (x : ℝ) : |w.im| ≤ ‖(x : ℂ) + w‖ := by
  have := Complex.abs_im_le_norm ((x : ℂ) + w)
  simpa using this
theorem Jq {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) : 0 < ((x : ℂ) + w).re := by
  simp; linarith
theorem Eo {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) :
    (x : ℂ) + w ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (Jq hw hx))
theorem add_ne_zero {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) + w ≠ 0 :=
  fun h => by have := Jq hw hx; rw [h] at this; simp at this
theorem Dq {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => Complex.log ((y : ℂ) + w)) (((x : ℂ) + w)⁻¹) x := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.log (z + w)) (((x : ℂ) + w)⁻¹) (x : ℂ) := by
    have := (Complex.hasDerivAt_log (Eo hw hx)).comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).add_const w)
    simpa [Function.comp_def] using this
  exact h1.comp_ofReal
theorem jS {w : ℂ} (hw : 0 < w.re) {m : ℝ} (hm : 0 ≤ m) :
    ∫ x in m..(m + 1), ((x : ℂ) + w)⁻¹
      = Complex.log (((m + 1 : ℝ) : ℂ) + w) - Complex.log ((m : ℂ) + w) := by
  have hcont : ContinuousOn (fun x : ℝ => ((x : ℂ) + w)⁻¹) (uIcc m (m + 1)) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact add_ne_zero hw (by linarith [hx.1])
  rw [integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => Complex.log ((y : ℂ) + w))
    (fun x hx => by
      rw [uIcc_of_le (by linarith)] at hx
      exact Dq hw (by linarith [hx.1]))
    (hcont.intervalIntegrable)]
theorem KM {w : ℂ} {x m : ℝ} (hxw : (x : ℂ) + w ≠ 0) (hmw : (m : ℂ) + w ≠ 0) :
    ((x : ℂ) + w)⁻¹
      = ((m : ℂ) + w)⁻¹ - ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2
        + ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w)) := by
  field_simp
  push_cast
  ring
def eps (w : ℂ) (m : ℝ) : ℂ :=
  ∫ x in m..(m + 1), ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))
theorem qd {w : ℂ} (hw : 0 < w.re) {m : ℝ} (hm : 0 ≤ m) :
    ∫ x in m..(m + 1), ((x : ℂ) + w)⁻¹
      = ((m : ℂ) + w)⁻¹ - (1 / 2 : ℂ) / ((m : ℂ) + w) ^ 2 + eps w m := by
  have hmw := add_ne_zero hw hm
  have hcongr : ∫ x in m..(m + 1), ((x : ℂ) + w)⁻¹ = ∫ x in m..(m + 1),
      (((m : ℂ) + w)⁻¹ - ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2
        + ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))) := by
    apply integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact KM (add_ne_zero hw (by linarith [hx.1])) hmw
  rw [hcongr]
  have hI : ∀ {f : ℝ → ℂ}, Continuous f → IntervalIntegrable f volume m (m + 1) :=
    fun hf => hf.intervalIntegrable _ _
  have hR : IntervalIntegrable (fun x : ℝ =>
      ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))) volume m (m + 1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact mul_ne_zero (pow_ne_zero _ hmw) (add_ne_zero hw (by linarith [hx.1]))
  have hmid : ∫ x in m..(m + 1), ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2
      = ((1 / 2 : ℝ) : ℂ) * ((((m : ℂ) + w) ^ 2)⁻¹) := by
    have e : (fun x : ℝ => ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2)
        = fun x : ℝ => ((x - m : ℝ) : ℂ) * ((((m : ℂ) + w) ^ 2)⁻¹) := by
      funext x; rw [div_eq_mul_inv]
    rw [e, qB, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_comp_sub_right (fun u : ℝ => u) m]
    simp only [sub_self, add_sub_cancel_left, integral_id]
    norm_num
  rw [integral_add ((hI (by fun_prop)).sub (hI (by fun_prop))) hR,
    integral_sub (hI (by fun_prop)) (hI (by fun_prop)), intervalIntegral.integral_const, hmid,
    show m + 1 - m = (1 : ℝ) by ring, one_smul]
  unfold eps
  push_cast
  ring
theorem Fe {w : ℂ} (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) {m : ℝ} (hm : 0 ≤ m) :
    ‖eps w m‖ ≤ 1 / (3 * ‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by
  have hmw := add_ne_zero hw hm
  have hM : 0 < ‖(m : ℂ) + w‖ := norm_pos_iff.mpr hmw
  have ht0 : 0 < |w.im| := by linarith
  unfold eps
  calc ‖∫ x in m..(m + 1), ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))‖
      ≤ ∫ x in m..(m + 1), ‖((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ x in m..(m + 1), (x - m) ^ 2 / (‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by
        apply intervalIntegral.integral_mono_on (by linarith)
        · refine (ContinuousOn.intervalIntegrable ?_).norm
          apply ContinuousOn.div (by fun_prop) (by fun_prop)
          intro x hx
          rw [uIcc_of_le (by linarith)] at hx
          exact mul_ne_zero (pow_ne_zero _ hmw) (add_ne_zero hw (by linarith [hx.1]))
        · exact (by fun_prop : Continuous fun x : ℝ => (x - m) ^ 2 / (‖(m : ℂ) + w‖ ^ 2 * |w.im|))
            |>.intervalIntegrable _ _
        · intro x hx
          have hx0 : 0 ≤ x := by linarith [hx.1]
          have hxw : |w.im| ≤ ‖(x : ℂ) + w‖ := Dp x
          rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            sq_abs]
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hxw (by positivity)
    _ = 1 / (3 * ‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 2) m]
        simp only [sub_self, add_sub_cancel_left, integral_pow]
        norm_num
        field_simp
section Seq
variable {w : ℂ}
theorem Nc (hw : 0 < w.re) (n : ℕ) : 0 < ((n : ℂ) + 1 + w).re := by
  simp; positivity
theorem nQ (hw : 0 < w.re) (n : ℕ) : (n : ℂ) + 1 + w ≠ 0 := fun h => by
  have := Nc hw n; rw [h] at this; simp at this
theorem AY (hw : 0 < w.re) (n : ℕ) : (n : ℝ) + 1 ≤ ‖(n : ℂ) + 1 + w‖ := by
  have h := Complex.re_le_norm ((n : ℂ) + 1 + w)
  simp at h; linarith
theorem Nh (hw : 0 < w.re) (n : ℕ) :
    ((n : ℂ) + 1 + w)⁻¹
      = (Complex.log (((n + 1 : ℕ) : ℂ) + 1 + w) - Complex.log ((n : ℂ) + 1 + w))
        + (1 / 2 : ℂ) / ((n : ℂ) + 1 + w) ^ 2 - eps w ((n : ℝ) + 1) := by
  have hm : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have h1 := qd hw hm
  have h2 := jS hw hm
  rw [h2] at h1
  have e1 : ((((n : ℝ) + 1 : ℝ)) : ℂ) + w = (n : ℂ) + 1 + w := by push_cast; ring
  have e2 : ((((n : ℝ) + 1 + 1 : ℝ)) : ℂ) + w = ((n + 1 : ℕ) : ℂ) + 1 + w := by push_cast; ring
  rw [e1, e2] at h1
  linear_combination (-1 : ℂ) * h1
def rho (w : ℂ) (n : ℕ) : ℂ := 1 / (((n : ℂ) + 1 + w) ^ 2 * ((n : ℂ) + 2 + w))
theorem Jt (hw : 0 < w.re) (n : ℕ) :
    1 / ((n : ℂ) + 1 + w) ^ 2
      = (((n : ℂ) + 1 + w)⁻¹ - (((n + 1 : ℕ) : ℂ) + 1 + w)⁻¹) + rho w n := by
  have h1 := nQ hw n
  have h2 := nQ hw (n + 1)
  have e : ((n + 1 : ℕ) : ℂ) + 1 + w = (n : ℂ) + 2 + w := by push_cast; ring
  rw [e] at h2 ⊢
  unfold rho
  field_simp
  ring
theorem xT (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (n : ℕ) :
    ‖rho w n‖ ≤ 1 / (‖(n : ℂ) + 1 + w‖ ^ 2 * |w.im|) := by
  have h1 := nQ hw n
  have hn2 : |w.im| ≤ ‖(n : ℂ) + 2 + w‖ := by
    have := Complex.abs_im_le_norm ((n : ℂ) + 2 + w); simpa using this
  have ht0 : 0 < |w.im| := by linarith
  unfold rho
  rw [norm_div, norm_one, norm_mul, norm_pow]
  apply div_le_div_of_nonneg_left zero_le_one (by positivity)
  exact mul_le_mul_of_nonneg_left hn2 (by positivity)
theorem mC (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (n : ℕ) :
    ‖eps w ((n : ℝ) + 1)‖ ≤ 1 / (3 * ‖(n : ℂ) + 1 + w‖ ^ 2 * |w.im|) := by
  have := Fe hw ht (m := (n : ℝ) + 1) (by positivity)
  rw [show ((((n : ℝ) + 1 : ℝ)) : ℂ) + w = (n : ℂ) + 1 + w by push_cast; ring] at this
  exact this
theorem KO (hw : 0 < w.re) (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1))
      = (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
        - (Complex.log ((N : ℂ) + 1 + w) - Complex.log ((0 : ℕ) + 1 + w : ℂ))
        - (1 / 2 : ℂ) * (((0 : ℕ) + 1 + w : ℂ)⁻¹ - ((N : ℂ) + 1 + w)⁻¹
            + ∑ n ∈ Finset.range N, rho w n)
        + ∑ n ∈ Finset.range N, eps w ((n : ℝ) + 1) := by
  rw [Finset.sum_sub_distrib]
  have hterm : ∀ n ∈ Finset.range N, (1 : ℂ) / (w + n + 1)
      = (Complex.log (((n + 1 : ℕ) : ℂ) + 1 + w) - Complex.log ((n : ℂ) + 1 + w))
        + (1 / 2 : ℂ) * ((((n : ℂ) + 1 + w)⁻¹ - (((n + 1 : ℕ) : ℂ) + 1 + w)⁻¹) + rho w n)
        - eps w ((n : ℝ) + 1) := by
    intro n _
    have A := Nh hw n
    have B := Jt hw n
    rw [show (1 : ℂ) / (w + n + 1) = ((n : ℂ) + 1 + w)⁻¹ by rw [one_div]; ring_nf]
    linear_combination A + (1 / 2 : ℂ) * B
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_range_sub (fun n => Complex.log ((n : ℂ) + 1 + w)) N, ← Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_range_sub' (fun n => ((n : ℂ) + 1 + w)⁻¹) N]
  push_cast
  ring
theorem FQ (hw : 0 < w.re) (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 + w.im ^ 2 ≤ ‖(n : ℂ) + 1 + w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : ((n : ℂ) + 1 + w).re = (n : ℝ) + 1 + w.re := by simp
  have him : ((n : ℂ) + 1 + w).im = w.im := by simp
  rw [hre, him]
  nlinarith
theorem vN (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (n : ℕ) :
    1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 2 * (1 / ((n : ℝ) + |w.im|) - 1 / ((n : ℝ) + 1 + |w.im|)) := by
  have h1 := FQ hw n
  have ht0 : 0 < |w.im| := by linarith
  have hpos : 0 < ((n : ℝ) + 1) ^ 2 + w.im ^ 2 := by positivity
  have YH : 1 / ((n : ℝ) + |w.im|) - 1 / ((n : ℝ) + 1 + |w.im|)
      = 1 / (((n : ℝ) + |w.im|) * ((n : ℝ) + 1 + |w.im|)) := by
    field_simp; ring
  rw [YH]
  have hsq : w.im ^ 2 = |w.im| ^ 2 := (sq_abs _).symm
  calc 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 1 / (((n : ℝ) + 1) ^ 2 + w.im ^ 2) :=
        div_le_div_of_nonneg_left zero_le_one hpos h1
    _ ≤ 2 * (1 / (((n : ℝ) + |w.im|) * ((n : ℝ) + 1 + |w.im|))) := by
        rw [hsq, ← div_eq_mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg ((n : ℝ) + 1 - |w.im|)]
theorem Dr (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 2 / |w.im| := by
  have ht0 : 0 < |w.im| := by linarith
  calc ∑ n ∈ Finset.range N, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2
      ≤ ∑ n ∈ Finset.range N, 2 * (1 / ((n : ℝ) + |w.im|) - 1 / ((n : ℝ) + 1 + |w.im|)) :=
        Finset.sum_le_sum fun n _ => vN hw ht n
    _ = 2 * (1 / |w.im| - 1 / ((N : ℝ) + |w.im|)) := by
        rw [← Finset.mul_sum, Finset.sum_congr rfl (fun (i : ℕ) _ => by
          rw [show ((i : ℝ) + 1 + |w.im|) = (((i + 1 : ℕ) : ℝ) + |w.im|) by push_cast; ring]),
          Finset.sum_range_sub' (fun n : ℕ => 1 / ((n : ℝ) + |w.im|)) N]
        push_cast
        ring
    _ ≤ 2 / |w.im| := by
        have : 0 ≤ 1 / ((N : ℝ) + |w.im|) := by positivity
        rw [div_eq_mul_one_div 2]
        linarith
theorem eW (hw : 0 < w.re) :
    Summable (fun n : ℕ => 1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (Real.summable_one_div_nat_pow.mpr one_lt_two)
    exact_mod_cast (summable_nat_add_iff 1).mpr this
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  exact div_le_div_of_nonneg_left zero_le_one (by positivity)
    (pow_le_pow_left₀ (by positivity) (AY hw n) 2)
theorem Ni (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) : Summable (rho w) := by
  refine Summable.of_norm_bounded ((eW hw).mul_left (1 / |w.im|)) fun n => ?_
  refine le_trans (xT hw ht n) (le_of_eq ?_)
  field_simp
theorem Nj (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    Summable (fun n : ℕ => eps w ((n : ℝ) + 1)) := by
  refine Summable.of_norm_bounded ((eW hw).mul_left (1 / (3 * |w.im|)))
    fun n => ?_
  refine le_trans (mC hw ht n) (le_of_eq ?_)
  field_simp
theorem rV (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) : Summable (fun n => ‖rho w n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((eW hw).mul_left (1 / |w.im|))
  refine le_trans (xT hw ht n) (le_of_eq ?_)
  field_simp
theorem rW (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    Summable (fun n : ℕ => ‖eps w ((n : ℝ) + 1)‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((eW hw).mul_left (1 / (3 * |w.im|)))
  refine le_trans (mC hw ht n) (le_of_eq ?_)
  field_simp
theorem qg (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 2 / |w.im| :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) (Dr hw ht)
theorem FU (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖∑' n, rho w n‖ ≤ 2 / w.im ^ 2 := by
  have ht0 : 0 < |w.im| := by linarith
  have hS := qg hw ht
  calc ‖∑' n, rho w n‖ ≤ ∑' n, ‖rho w n‖ := norm_tsum_le_tsum_norm (rV hw ht)
    _ ≤ ∑' n : ℕ, (1 / |w.im|) * (1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
        refine Summable.tsum_le_tsum (fun n => ?_) (rV hw ht)
          ((eW hw).mul_left _)
        refine le_trans (xT hw ht n) (le_of_eq ?_)
        field_simp
    _ = (1 / |w.im|) * ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 := tsum_mul_left
    _ ≤ (1 / |w.im|) * (2 / |w.im|) := by gcongr
    _ = 2 / w.im ^ 2 := by rw [← sq_abs]; field_simp
theorem FZ (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ ≤ (2 / 3) / w.im ^ 2 := by
  have ht0 : 0 < |w.im| := by linarith
  have hS := qg hw ht
  calc ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ ≤ ∑' n : ℕ, ‖eps w ((n : ℝ) + 1)‖ :=
        norm_tsum_le_tsum_norm (rW hw ht)
    _ ≤ ∑' n : ℕ, (1 / (3 * |w.im|)) * (1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
        refine Summable.tsum_le_tsum (fun n => ?_) (rW hw ht)
          ((eW hw).mul_left _)
        refine le_trans (mC hw ht n) (le_of_eq ?_)
        field_simp
    _ = (1 / (3 * |w.im|)) * ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 := tsum_mul_left
    _ ≤ (1 / (3 * |w.im|)) * (2 / |w.im|) := by gcongr
    _ = (2 / 3) / w.im ^ 2 := by rw [← sq_abs]; field_simp
theorem tK (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
      - Complex.log ((N : ℂ) + 1 + w)) atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  have hdecomp : ∀ N : ℕ, (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
      - Complex.log ((N : ℂ) + 1 + w)
      = (((harmonic N : ℚ) : ℝ) - Real.log ((N : ℝ) + 1) : ℝ)
        - Complex.log (1 + w / ((N : ℂ) + 1)) := by
    intro N
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hN1 : (N : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero N
    have hq' : 1 + w / ((N : ℂ) + 1) = ((N : ℂ) + 1 + w) / ((N : ℂ) + 1) := by
      field_simp
    have hq : 1 + w / ((N : ℂ) + 1) ≠ 0 := by
      rw [hq']; exact div_ne_zero (nQ hw N) hN1
    have hlog : Complex.log ((N : ℂ) + 1 + w)
        = Real.log ((N : ℝ) + 1) + Complex.log (1 + w / ((N : ℂ) + 1)) := by
      rw [← Complex.log_ofReal_mul hN hq, hq']
      congr 1
      push_cast
      field_simp
    rw [hlog, Zeta23.fF.vH]
    push_cast
    ring
  simp_rw [hdecomp]
  have h1 : Tendsto (fun N : ℕ => ((((harmonic N : ℚ) : ℝ) - Real.log ((N : ℝ) + 1) : ℝ) : ℂ))
      atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log_add_one
  have h2 : Tendsto (fun N : ℕ => Complex.log (1 + w / ((N : ℂ) + 1))) atTop (𝓝 0) := by
    have hq : Tendsto (fun N : ℕ => w / ((N : ℂ) + 1)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have : (fun N : ℕ => ‖w / ((N : ℂ) + 1)‖) = fun N : ℕ => ‖w‖ * (1 / ((N : ℝ) + 1)) := by
        funext N
        rw [norm_div, show ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        ring
      rw [this]
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ‖w‖
    have hcont : ContinuousAt Complex.log 1 := continuousAt_clog (by simp)
    have := hcont.tendsto.comp (by simpa using hq.const_add 1)
    simpa [Function.comp_def] using this
  simpa using h1.sub h2
theorem Ep (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => ((N : ℂ) + 1 + w)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun N => norm_nonneg _) (fun N => ?_)
  rw [norm_inv]
  have h := AY hw N
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le hpos h
theorem Qa (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    Complex.digamma w = Complex.log (1 + w) - 1 / w - (1 / 2 : ℂ) * (1 + w)⁻¹
      - (1 / 2 : ℂ) * (∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1) := by
  have hmem : w ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    have := congrArg Complex.im hk
    simp at this
    rw [← this] at ht; simp at ht; linarith
  have hL := (Zeta23.fF.fG hmem).tendsto_sum_nat
  have hR : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1)))
      atTop (𝓝 ((Real.eulerMascheroniConstant : ℂ) + Complex.log (1 + w)
        - (1 / 2 : ℂ) * ((1 + w)⁻¹ - 0 + ∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1))) := by
    have e : ∀ N : ℕ, ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1))
        = ((∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1)) - Complex.log ((N : ℂ) + 1 + w))
          + Complex.log (1 + w)
          - (1 / 2 : ℂ) * ((1 + w)⁻¹ - ((N : ℂ) + 1 + w)⁻¹ + ∑ n ∈ Finset.range N, rho w n)
          + ∑ n ∈ Finset.range N, eps w ((n : ℝ) + 1) := by
      intro N
      rw [KO hw N]
      push_cast
      ring
    simp_rw [e]
    refine (((tK hw).add tendsto_const_nhds).sub
      (((tendsto_const_nhds.sub (Ep hw)).add
        (Ni hw ht).hasSum.tendsto_sum_nat).const_mul _)).add
      (Nj hw ht).hasSum.tendsto_sum_nat
  have := tendsto_nhds_unique hL hR
  rw [sub_zero] at this
  linear_combination this
theorem BK (hw : 0 < w.re) :
    Complex.log (1 + w) - Complex.log w = w⁻¹ - (1 / 2 : ℂ) / w ^ 2 + eps w 0 := by
  have h1 := qd hw (m := 0) le_rfl
  have h2 := jS hw (m := 0) le_rfl
  rw [h2] at h1
  simpa [add_comm] using h1
theorem Ga (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) : ‖eps w 0‖ ≤ (1 / 3) / |w.im| ^ 3 := by
  have h := Fe hw ht (m := 0) le_rfl
  have ht0 : 0 < |w.im| := by linarith
  have hw' : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  simp only [Complex.ofReal_zero, zero_add] at h
  calc ‖eps w 0‖ ≤ 1 / (3 * ‖w‖ ^ 2 * |w.im|) := h
    _ ≤ 1 / (3 * |w.im| ^ 2 * |w.im|) := by
        apply div_le_div_of_nonneg_left zero_le_one (by positivity)
        gcongr
    _ = (1 / 3) / |w.im| ^ 3 := by field_simp
theorem vO (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w‖ ≤ 3 / w.im ^ 2 := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have h1w : 1 + w ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have ht0 : 0 < |w.im| := by linarith
  have hwn : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  have acS : |w.im| ≤ ‖1 + w‖ := by have := Complex.abs_im_le_norm (1 + w); simpa using this
  have hid := Qa hw ht
  have hlog := BK hw
  have key : Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w
      = -(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0
        - (1 / 2 : ℂ) * (∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1) := by
    rw [hid, show Complex.log (1 + w) = Complex.log w + (w⁻¹ - (1 / 2 : ℂ) / w ^ 2 + eps w 0) by
      rw [← hlog]; ring]
    field_simp
    ring
  rw [key]
  have hsq : |w.im| ^ 2 = w.im ^ 2 := sq_abs _
  have b1 : ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))‖ ≤ (1 / 2) / w.im ^ 2 := by
    rw [norm_div, norm_neg, norm_mul, norm_pow]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this, ← hsq]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have h1 : 1 ≤ ‖1 + w‖ := le_trans (by simp; linarith) (Complex.re_le_norm (1 + w))
    calc |w.im| ^ 2 = |w.im| ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖w‖ ^ 2 * ‖1 + w‖ := by gcongr
  have b2 : ‖eps w 0‖ ≤ (2 / 3) / w.im ^ 2 := by
    refine le_trans (Ga hw ht) ?_
    rw [← hsq, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : |w.im| ^ 3 = |w.im| ^ 2 * |w.im| := by ring
    rw [h3]
    have : 0 < |w.im| ^ 2 := by positivity
    nlinarith
  have b3 : ‖(1 / 2 : ℂ) * ∑' n, rho w n‖ ≤ 1 / w.im ^ 2 := by
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    have h := mul_le_mul_of_nonneg_left (FU hw ht) (by norm_num : (0:ℝ) ≤ 1 / 2)
    calc 1 / 2 * ‖∑' n, rho w n‖ ≤ 1 / 2 * (2 / w.im ^ 2) := h
      _ = 1 / w.im ^ 2 := by ring
  have b4 := FZ hw ht
  calc ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0 - (1 / 2 : ℂ) * ∑' n, rho w n
        + ∑' n : ℕ, eps w ((n : ℝ) + 1)‖
      ≤ ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))‖ + ‖eps w 0‖ + ‖(1 / 2 : ℂ) * ∑' n, rho w n‖
        + ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ := by
        have s1 := norm_add_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0 - (1 / 2 : ℂ) * ∑' n, rho w n)
          (∑' n : ℕ, eps w ((n : ℝ) + 1))
        have s2 := norm_sub_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0) ((1 / 2 : ℂ) * ∑' n, rho w n)
        have s3 := norm_add_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))) (eps w 0)
        linarith
    _ ≤ (1 / 2) / w.im ^ 2 + (2 / 3) / w.im ^ 2 + 1 / w.im ^ 2 + (2 / 3) / w.im ^ 2 := by
        gcongr
    _ ≤ 3 / w.im ^ 2 := by
        have hpos : 0 < w.im ^ 2 := by rw [← hsq]; positivity
        rw [show (1 / 2) / w.im ^ 2 + (2 / 3) / w.im ^ 2 + 1 / w.im ^ 2 + (2 / 3) / w.im ^ 2
          = (17 / 6) / w.im ^ 2 by ring]
        apply div_le_div_of_nonneg_right _ hpos.le
        norm_num
end Seq
section WC
theorem BL {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - (1 / 2) * Real.log (a ^ 2 + t ^ 2)|
      ≤ 4 / t ^ 2 := by
  set w : ℂ := (a : ℂ) + Complex.I * t with hwdef
  have hre : w.re = a := by simp [hwdef]
  have him : w.im = t := by simp [hwdef]
  have hw : 0 < w.re := by rw [hre]; exact ha0
  have ht' : 1 / 2 ≤ |w.im| := by rw [him]; exact ht
  have hmain := vO hw ht'
  rw [him] at hmain
  have ht0 : 0 < |t| := by linarith
  have ht2 : 0 < t ^ 2 := by rw [← sq_abs]; positivity
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have WD : (Complex.log w).re = (1 / 2) * Real.log (a ^ 2 + t ^ 2) := by
    rw [Complex.log_re, show ‖w‖ = Real.sqrt (a ^ 2 + t ^ 2) by
      rw [Complex.norm_eq_sqrt_sq_add_sq, hre, him], Real.log_sqrt (by positivity)]
    ring
  have WE : ((1 / 2 : ℂ) / w).re = a / (2 * (a ^ 2 + t ^ 2)) := by
    rw [show (1 / 2 : ℂ) / w = ((1 / 2 : ℝ) : ℂ) * w⁻¹ by push_cast; ring, Complex.re_ofReal_mul,
      Complex.inv_re, Complex.normSq_apply, hre, him]
    field_simp
  have hdiff : (Complex.digamma w).re - (1 / 2) * Real.log (a ^ 2 + t ^ 2)
      = (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re - a / (2 * (a ^ 2 + t ^ 2)) := by
    rw [Complex.add_re, Complex.sub_re, WD, WE]; ring
  rw [hdiff]
  have h1 : |(Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re| ≤ 3 / t ^ 2 :=
    le_trans (Complex.abs_re_le_norm _) hmain
  have h2 : |a / (2 * (a ^ 2 + t ^ 2))| ≤ 1 / t ^ 2 := by
    rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) ht2]
    nlinarith
  calc |(Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re - a / (2 * (a ^ 2 + t ^ 2))|
      ≤ |(Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re| + |a / (2 * (a ^ 2 + t ^ 2))| :=
        abs_sub _ _
    _ ≤ 3 / t ^ 2 + 1 / t ^ 2 := add_le_add h1 h2
    _ = 4 / t ^ 2 := by ring
theorem zW {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - Real.log (abs t)| ≤ 5 / t ^ 2 := by
  have h := BL ha0 ha1 ht
  have ht0 : 0 < |t| := by linarith
  have ht2 : 0 < t ^ 2 := by rw [← sq_abs]; positivity
  have hl : (1 / 2) * Real.log (a ^ 2 + t ^ 2) - Real.log (abs t)
      = (1 / 2) * Real.log (1 + a ^ 2 / t ^ 2) := by
    have htne : t ≠ 0 := fun h0 => by rw [h0] at ht0; simp at ht0
    have : a ^ 2 + t ^ 2 = t ^ 2 * (1 + a ^ 2 / t ^ 2) := by field_simp; ring
    rw [this, Real.log_mul ht2.ne' (by positivity), ← sq_abs, Real.log_pow]
    push_cast; ring
  have hb : |(1 / 2) * Real.log (a ^ 2 + t ^ 2) - Real.log (abs t)| ≤ 1 / t ^ 2 := by
    have hx0 : 0 ≤ a ^ 2 / t ^ 2 := by positivity
    have acC : 0 ≤ Real.log (1 + a ^ 2 / t ^ 2) := Real.log_nonneg (by linarith)
    have hlog := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 1 + a ^ 2 / t ^ 2)
    have ha2 : a ^ 2 / t ^ 2 ≤ 1 / t ^ 2 := by
      apply div_le_div_of_nonneg_right _ ht2.le; nlinarith
    rw [hl, abs_of_nonneg (by positivity)]
    linarith
  calc |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - Real.log (abs t)|
      ≤ |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - (1 / 2) * Real.log (a ^ 2 + t ^ 2)|
        + |(1 / 2) * Real.log (a ^ 2 + t ^ 2) - Real.log (abs t)| := abs_sub_le _ _ _
    _ ≤ 4 / t ^ 2 + 1 / t ^ 2 := add_le_add h hb
    _ = 5 / t ^ 2 := by ring
theorem Ol : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
    |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2 := by
  refine ⟨20 / (2 * Real.pi), fun τ hτ => ?_⟩
  have hπ := Real.pi_pos
  have ht : 1 / 2 ≤ |τ / 2| := by rw [abs_div, abs_two]; linarith
  have h := zW (a := 1 / 4) (by norm_num) (by norm_num) ht
  have jQ : 0 < |τ| := by linarith
  set D : ℝ := (Complex.digamma ((((1:ℝ) / 4 : ℝ)) + Complex.I * ((τ / 2 : ℝ) : ℂ))).re
    - Real.log |τ / 2| with hD
  have hD5 : |D| ≤ 5 / (τ / 2) ^ 2 := h
  have YI : Real.log (|τ| / (2 * Real.pi)) = Real.log |τ / 2| - Real.log Real.pi := by
    rw [abs_div, abs_two, Real.log_div jQ.ne' (by positivity), Real.log_div jQ.ne' two_ne_zero,
      Real.log_mul two_ne_zero hπ.ne']
    ring
  have key : Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))
      = (1 / (2 * Real.pi)) * D := by
    rw [Zeta23.lD.Mb τ, YI, hD]
    ring
  rw [key, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * Real.pi))]
  calc 1 / (2 * Real.pi) * |D| ≤ 1 / (2 * Real.pi) * (5 / (τ / 2) ^ 2) := by gcongr
    _ = 20 / (2 * Real.pi) / τ ^ 2 := by field_simp; ring
end WC
end oR
end Zeta23
end
end

-- Zeta23.IT.Bridge
section
open MeasureTheory Complex Filter Set
open scoped Real FourierTransform ComplexConjugate
noncomputable section
namespace Zeta23
namespace EF
theorem bZ {k : ℝ → ℂ} (bD : HasCompactSupport k) :
    ∃ Λ : ℝ, ∀ u, k u ≠ 0 → |u| ≤ Λ := by
  obtain ⟨R, hR⟩ := bD.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun u hu => ?_⟩
  have := hR (subset_tsupport _ (Function.mem_support.mpr hu))
  simpa [Real.norm_eq_abs] using this
theorem oT {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) {Λ : ℝ}
    (hΛ : ∀ u, k u ≠ 0 → |u| ≤ Λ) (w : ℝ) :
    ‖𝓕 k w‖ * (1 + w ^ 2)
      ≤ (∫ u, ‖k u‖) + (∫ u, ‖deriv (deriv k) u‖) / (4 * π ^ 2) := by
  have bD : HasCompactSupport k := Zeta23.dV hΛ
  have hki : Integrable k := hk.continuous.integrable_of_hasCompactSupport bD
  have YJ : 𝓕 k w = aD k ((-(2 * π * w) : ℝ) : ℂ) := by
    rw [iO]; field_simp
  have h1 := Zeta23.jz hki hΛ ((-(2 * π * w) : ℝ) : ℂ)
  have h2 := Zeta23.jE hk hΛ ((-(2 * π * w) : ℝ) : ℂ)
  simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] at h1 h2
  rw [YJ]
  have h2' : ‖aD k ((-(2 * π * w) : ℝ) : ℂ)‖ * w ^ 2
      ≤ (∫ u, ‖deriv (deriv k) u‖) / (4 * π ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    calc ‖aD k ((-(2 * π * w) : ℝ) : ℂ)‖ * w ^ 2 * (4 * π ^ 2)
        = ‖aD k ((-(2 * π * w) : ℝ) : ℂ)‖ * (-(2 * π * w)) ^ 2 := by ring
      _ ≤ ∫ u, ‖deriv (deriv k) u‖ := h2
  calc ‖aD k ((-(2 * π * w) : ℝ) : ℂ)‖ * (1 + w ^ 2)
      = ‖aD k ((-(2 * π * w) : ℝ) : ℂ)‖ + ‖aD k ((-(2 * π * w) : ℝ) : ℂ)‖ * w ^ 2 := by ring
    _ ≤ _ := add_le_add h1 h2'
theorem nY {k : ℝ → ℂ} (hki : Integrable k) : Continuous (𝓕 k) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by exact continuous_inner) hki
theorem dH {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (bD : HasCompactSupport k) : Integrable (𝓕 k) := by
  obtain ⟨Λ, hΛ⟩ := bZ bD
  have hki : Integrable k := hk.continuous.integrable_of_hasCompactSupport bD
  set K : ℝ := (∫ u, ‖k u‖) + (∫ u, ‖deriv (deriv k) u‖) / (4 * π ^ 2)
  refine ((integrable_inv_one_add_sq.const_mul K).mono'
    (nY hki).aestronglyMeasurable (Eventually.of_forall fun w => ?_))
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact oT hk hΛ w
theorem oW {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) {Λ : ℝ}
    (hΛ : ∀ u, k u ≠ 0 → |u| ≤ Λ) (τ : ℝ) :
    ‖aD k τ‖ * (1 + τ ^ 2) ≤ (∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖ := by
  have bD : HasCompactSupport k := Zeta23.dV hΛ
  have hki : Integrable k := hk.continuous.integrable_of_hasCompactSupport bD
  have h1 := Zeta23.jz hki hΛ (τ : ℂ)
  have h2 := Zeta23.jE hk hΛ (τ : ℂ)
  simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] at h1 h2
  calc ‖aD k τ‖ * (1 + τ ^ 2) = ‖aD k τ‖ + ‖aD k τ‖ * τ ^ 2 := by ring
    _ ≤ _ := add_le_add h1 h2
theorem wD (hΓ : gX) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ τ : ℝ, |mu τ| ≤ K₂ * (1 + |τ|) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := hΓ.Sz
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hΓ.smooth.continuous.continuousOn (s := Icc (-1 : ℝ) 1))
  have hπ : 0 < 1 / (2 * π) := by positivity
  have hL0 : 0 ≤ (1 / (2 * π)) * |Real.log (2 * π)| := mul_nonneg hπ.le (abs_nonneg _)
  set K₂ : ℝ := max M 0 + |C| + (1 / (2 * π)) * |Real.log (2 * π)| + 1 / π with hK₂
  have Vh : 0 ≤ K₂ := by
    have : 0 ≤ max M 0 := le_max_right _ _
    have : 0 ≤ 1 / π := by positivity
    positivity
  refine ⟨K₂, Vh, fun τ => ?_⟩
  have hb1 : 1 ≤ (1 + |τ|) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg τ]) (by norm_num)
  rcases le_or_gt |τ| 1 with hτ | hτ
  · 
    have := hM τ (abs_le.mp hτ)
    rw [Real.norm_eq_abs] at this
    calc |mu τ| ≤ max M 0 := this.trans (le_max_left _ _)
      _ ≤ K₂ * 1 := by
        rw [mul_one, hK₂]
        have : 0 ≤ 1 / π := by positivity
        linarith [abs_nonneg C]
      _ ≤ K₂ * (1 + |τ|) ^ (1 / 2 : ℝ) := by gcongr
  · 
    have hτ1 : 1 ≤ |τ| := hτ.le
    have hst := hC τ hτ1
    have hsq : 1 ≤ τ ^ 2 := by rw [← sq_abs]; nlinarith
    have WG : C / τ ^ 2 ≤ |C| := by
      calc C / τ ^ 2 ≤ |C| / τ ^ 2 := by gcongr; exact le_abs_self C
        _ ≤ |C| := div_le_self (abs_nonneg C) hsq
    have hlog : |Real.log (|τ| / (2 * π))| ≤ Real.log |τ| + |Real.log (2 * π)| := by
      rw [Real.log_div (by positivity) (by positivity)]
      calc abs (Real.log |τ| - Real.log (2 * π))
          ≤ abs (Real.log |τ|) + |Real.log (2 * π)| := abs_sub _ _
        _ = Real.log |τ| + |Real.log (2 * π)| := by rw [abs_of_nonneg (Real.log_nonneg hτ1)]
    have zX : Real.log |τ| ≤ 2 * (1 + |τ|) ^ (1 / 2 : ℝ) := by
      have := Real.log_le_rpow_div (abs_nonneg τ) (by norm_num : (0 : ℝ) < 1 / 2)
      have hmono : |τ| ^ (1 / 2 : ℝ) ≤ (1 + |τ|) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg τ) (by linarith) (by norm_num)
      calc Real.log |τ| ≤ |τ| ^ (1 / 2 : ℝ) / (1 / 2) := this
        _ = 2 * |τ| ^ (1 / 2 : ℝ) := by ring
        _ ≤ 2 * (1 + |τ|) ^ (1 / 2 : ℝ) := by gcongr
    have hmu : |mu τ| ≤ |C| + (1 / (2 * π)) * (Real.log |τ| + |Real.log (2 * π)|) := by
      have htri : |mu τ| ≤ |mu τ - 1 / (2 * π) * Real.log (|τ| / (2 * π))|
          + |1 / (2 * π) * Real.log (|τ| / (2 * π))| := by
        have := abs_add_le (mu τ - 1 / (2 * π) * Real.log (|τ| / (2 * π)))
          (1 / (2 * π) * Real.log (|τ| / (2 * π)))
        rwa [sub_add_cancel] at this
      calc |mu τ| ≤ C / τ ^ 2 + |1 / (2 * π) * Real.log (|τ| / (2 * π))| := by linarith
        _ ≤ |C| + (1 / (2 * π)) * (Real.log |τ| + |Real.log (2 * π)|) := by
          rw [abs_mul, abs_of_pos hπ]
          gcongr
    set b := (1 + |τ|) ^ (1 / 2 : ℝ) with hb
    calc |mu τ| ≤ |C| + (1 / (2 * π)) * (Real.log |τ| + |Real.log (2 * π)|) := hmu
      _ ≤ |C| + (1 / (2 * π)) * (2 * b + |Real.log (2 * π)|) := by gcongr
      _ = (|C| + (1 / (2 * π)) * |Real.log (2 * π)|) * 1 + (1 / π) * b := by ring
      _ ≤ (|C| + (1 / (2 * π)) * |Real.log (2 * π)|) * b + (1 / π) * b := by gcongr
      _ = (|C| + (1 / (2 * π)) * |Real.log (2 * π)| + 1 / π) * b := by ring
      _ ≤ K₂ * b := by
        gcongr; rw [hK₂]; linarith [le_max_right M 0]
theorem tL {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (bD : HasCompactSupport k)
    (hΓ : gX) : Integrable (fun τ : ℝ => aD k τ * (mu τ : ℂ)) := by
  obtain ⟨Λ, hΛ⟩ := bZ bD
  obtain ⟨K₂, hK₂, hmu⟩ := wD hΓ
  set K₁ : ℝ := (∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖ with hK₁
  have abl : 0 ≤ K₁ := by positivity
  have hmeas : AEStronglyMeasurable (fun τ : ℝ => aD k τ * (mu τ : ℂ)) :=
    (dY (dH hk bD)).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp hΓ.smooth.continuous).aestronglyMeasurable
  have hdom : Integrable (fun τ : ℝ => 2 * K₁ * K₂ * (1 + ‖τ‖) ^ (-(3 / 2) : ℝ)) :=
    (integrable_one_add_norm (by rw [Module.finrank_self]; norm_num)).const_mul _
  refine hdom.mono' hmeas (Eventually.of_forall fun τ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hb : 0 < 1 + |τ| := by linarith [abs_nonneg τ]
  have h1 : ‖aD k τ‖ * (1 + τ ^ 2) ≤ K₁ := oW hk hΛ τ
  have h2 : |mu τ| ≤ K₂ * (1 + |τ|) ^ (1 / 2 : ℝ) := hmu τ
  have hsq : (1 + |τ|) ^ (2 : ℝ) ≤ 2 * (1 + τ ^ 2) := by
    rw [Real.rpow_two]; nlinarith [sq_abs τ, sq_nonneg (1 - |τ|)]
  have key : (1 + |τ|) ^ (1 / 2 : ℝ) ≤ 2 * (1 + τ ^ 2) * (1 + |τ|) ^ (-(3 / 2) : ℝ) := by
    rw [show (1 / 2 : ℝ) = 2 + (-(3 / 2)) by norm_num, Real.rpow_add hb]
    exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hb.le _)
  calc ‖aD k τ‖ * |mu τ|
      ≤ ‖aD k τ‖ * (K₂ * (1 + |τ|) ^ (1 / 2 : ℝ)) := by gcongr
    _ ≤ ‖aD k τ‖ * (K₂ * (2 * (1 + τ ^ 2) * (1 + |τ|) ^ (-(3 / 2) : ℝ))) := by gcongr
    _ = (‖aD k τ‖ * (1 + τ ^ 2)) * (2 * K₂ * (1 + |τ|) ^ (-(3 / 2) : ℝ)) := by ring
    _ ≤ K₁ * (2 * K₂ * (1 + |τ|) ^ (-(3 / 2) : ℝ)) := by
        gcongr
    _ = 2 * K₁ * K₂ * (1 + |τ|) ^ (-(3 / 2) : ℝ) := by ring
end EF
end Zeta23
end
end

-- Zeta23.cw.VR
section
noncomputable section
namespace Zeta23
namespace cw
open Complex
theorem vF {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Complex.digamma (starRingEnd ℂ z) = starRingEnd ℂ (Complex.digamma z) := by
  have hz' : starRingEnd ℂ z ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    apply hz
    refine ⟨k, ?_⟩
    have := congrArg (starRingEnd ℂ) hk
    simpa using this
  have h1 := Zeta23.fF.fG hz
  have h2 := Zeta23.fF.fG hz'
  have h1c : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (starRingEnd ℂ z + n + 1))
      (starRingEnd ℂ (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z)) := by
    have := (Complex.hasSum_conj' ).mpr h1
    refine this.congr_fun fun n => ?_
    simp only [map_sub, map_div₀, map_one, map_add, map_natCast]
  have huniq := h2.unique h1c
  have e : starRingEnd ℂ (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z)
      = starRingEnd ℂ (Complex.digamma z) + (Real.eulerMascheroniConstant : ℂ)
        + 1 / starRingEnd ℂ z := by
    simp only [map_add, map_div₀, map_one, Complex.conj_ofReal]
  rw [e] at huniq
  linear_combination huniq
theorem gP {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = -((Real.log Real.pi : ℝ) : ℂ) / 2 + (1 / 2) * Complex.digamma (s / 2) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hs2 : 0 < (s / 2).re := by simp; linarith
  have hGne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs2
  have Vi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hπ]; exact Complex.exp_ne_zero _
  have hfun : Complex.Gammaℝ = fun s => (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s
      * (Complex.Gamma ∘ fun s : ℂ => s / 2) s := by
    funext s; rw [Complex.Gammaℝ_def]; rfl
  have Ut : HasDerivAt (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s := by
    have h := ((hasDerivAt_id s).neg.div_const 2).const_cpow (c := (Real.pi : ℂ)) (Or.inl hπ)
    convert h using 1
    · funext x; simp
    · simp
  have RB : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s :=
    Ut.differentiableAt
  have OM : DifferentiableAt ℂ Complex.Gamma (s / 2) := by
    apply Complex.differentiableAt_Gamma
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hhalf : DifferentiableAt ℂ (fun s : ℂ => s / 2) s := differentiableAt_id.div_const 2
  have Vk : DifferentiableAt ℂ (Complex.Gamma ∘ fun s : ℂ => s / 2) s := OM.comp s hhalf
  rw [hfun, logDeriv_mul s Vi (by exact hGne) RB Vk,
    logDeriv_comp (g := fun s : ℂ => s / 2) (x := s) OM hhalf, ← Complex.digamma_def]
  have h1 : logDeriv (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s = Complex.log Real.pi * (-1 / 2) := by
    rw [logDeriv_apply, Ut.deriv]
    field_simp
  have h2 : deriv (fun s : ℂ => s / 2) s = 1 / 2 := by
    have : HasDerivAt (fun s : ℂ => s / 2) (1 / 2) s := by
      simpa using (hasDerivAt_id s).div_const 2
    exact this.deriv
  rw [h1, h2, (Complex.ofReal_log Real.pi_pos.le).symm]
  ring
theorem KQ (t : ℝ) :
    logDeriv Complex.Gammaℝ (1/2 + t * I) + logDeriv Complex.Gammaℝ (1/2 - t * I)
      = (((Complex.digamma (1/4 + t/2 * I)).re - Real.log Real.pi : ℝ) : ℂ) := by
  have hp : 0 < ((1:ℂ)/2 + t * I).re := by simp
  have hm : 0 < ((1:ℂ)/2 - t * I).re := by simp
  rw [gP hp, gP hm]
  set w : ℂ := 1/4 + t/2 * I with hw
  have e1 : ((1:ℂ)/2 + t * I) / 2 = w := by rw [hw]; ring
  have e2 : ((1:ℂ)/2 - t * I) / 2 = starRingEnd ℂ w := by
    have : starRingEnd ℂ w = 1/4 - t/2 * I := by
      rw [hw, show (1:ℂ)/4 + (t:ℂ)/2 * I = ((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ) * I by push_cast; ring]
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [this]; ring
  have hwZ : w ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    have := congrArg Complex.re hk
    rw [hw] at this
    simp at this
    have h4 : (4 * k : ℤ) = (1 : ℤ) := by
      have : (4 : ℝ) * k = 1 := by rw [this]; norm_num
      exact_mod_cast this
    omega
  rw [e1, e2, vF hwZ]
  have hre : (1/2 : ℂ) * Complex.digamma w + (1/2 : ℂ) * starRingEnd ℂ (Complex.digamma w)
      = ((Complex.digamma w).re : ℂ) := by
    rw [← mul_add, Complex.add_conj]; push_cast; ring
  push_cast
  linear_combination hre
end cw
end Zeta23
end
end

-- Zeta23.cw.WH
section
noncomputable section
namespace Zeta23
namespace cw
open Complex MeasureTheory
open scoped ArithmeticFunction
def aW (k : ℝ → ℂ) (s : ℂ) : ℂ := aD k ((s - 1/2) / I)
def tilt (k : ℝ → ℂ) (b : ℝ) : ℝ → ℂ := fun u => k u * (Real.exp (b * u) : ℂ)
theorem rJ {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (b : ℝ) : ContDiff ℝ 2 (tilt k b) := by
  refine hk.mul ?_
  have : ContDiff ℝ 2 (fun u : ℝ => Real.exp (b * u)) := (Real.contDiff_exp.comp
    (contDiff_const.mul contDiff_id)).of_le le_top
  exact Complex.ofRealCLM.contDiff.comp this
theorem jG {k : ℝ → ℂ} (hk : HasCompactSupport k) (b : ℝ) :
    HasCompactSupport (tilt k b) := by
  refine hk.mul_right
theorem Nk (k : ℝ → ℂ) (c t : ℝ) :
    aW k (c + t * I) = aD (tilt k (c - 1/2)) t := by
  unfold aW tilt aD
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  have harg : I * ((↑c + ↑t * I - 1/2) / I) * ↑u = (((c - 1/2) * u : ℝ) : ℂ) + I * ↑t * ↑u := by
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    field_simp
    push_cast
    ring
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp]
  ring
theorem Gb {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (bD : HasCompactSupport k)
    (b y : ℝ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, aD (tilt k b) t * cexp (-I * t * y)
      = k y * (Real.exp (b * y) : ℂ) := by
  have hcont := (rJ hk b).continuous
  have hint : Integrable (tilt k b) (volume : Measure ℝ) :=
    hcont.integrable_of_hasCompactSupport (jG bD b)
  have hF := Zeta23.EF.dH (rJ hk b)
    (jG bD b)
  have h1 := Zeta23.EF.oO hcont hint hF y
  rw [← h1]
  rfl
theorem Er {k : ℝ → ℂ} {c : ℝ} (hc1 : 1 < c) (t : ℝ) :
    aW k (c + t * I) * (-logDeriv riemannZeta (c + t * I))
      = ∑' n : ℕ, aD (tilt k (c - 1/2)) t * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := by
  have hre : 1 < ((c : ℂ) + t * I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    simpa using hc1
  have h1 : -logDeriv riemannZeta ((c : ℂ) + t * I) = LSeries (fun n => (Λ n : ℂ)) ((c:ℂ) + t * I) := by
    have h2 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
    rw [logDeriv, Pi.div_apply, h2]
    ring
  rw [Nk, h1, LSeries, ← tsum_mul_left]
theorem BT {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (bD : HasCompactSupport k)
    {c : ℝ} (n : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        aD (tilt k (c - 1/2)) t * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n
      = ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hterm : ∀ t : ℝ, LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n
        = ((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ) * cexp (-I * t * Real.log n) := by
      intro t
      rw [LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv, ← Complex.cpow_neg]
      have hsplit : (-((c:ℂ) + t * I)) = (-(c:ℂ)) + (-(I * t)) := by ring
      rw [hsplit, Complex.cpow_add _ _ hnC]
      have h1 : (n:ℂ) ^ (-(c:ℂ)) = (((n:ℝ) ^ (-c) : ℝ) : ℂ) := by
        rw [show ((n:ℂ)) = (((n:ℝ):ℂ)) by push_cast; rfl,
          show (-(c:ℂ)) = ((-c : ℝ) : ℂ) by push_cast; rfl,
          ← Complex.ofReal_cpow hn0.le]
      have h2 : (n:ℂ) ^ (-(I * t)) = cexp (-I * t * Real.log n) := by
        rw [Complex.cpow_def_of_ne_zero hnC]
        congr 1
        rw [show ((n:ℂ)) = (((n:ℝ):ℂ)) by push_cast; rfl, ← Complex.ofReal_log hn0.le]
        ring
      rw [h1, h2]
      ring
    simp_rw [hterm]
    have hre : (fun t : ℝ => aD (tilt k (c - 1/2)) t
        * (((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ) * cexp (-I * t * Real.log n)))
        = fun t : ℝ => (((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ))
          * (aD (tilt k (c - 1/2)) t * cexp (-I * t * Real.log n)) := by
      funext t
      ring
    rw [hre, Zeta23.EF.dW]
    rw [show (1 / (2 * (Real.pi : ℂ))) * ((((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ))
        * ∫ t : ℝ, aD (tilt k (c - 1/2)) t * cexp (-I * t * Real.log n))
        = (((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ))
          * ((1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, aD (tilt k (c - 1/2)) t
            * cexp (-I * t * Real.log n)) from by ring]
    rw [Gb hk bD (c - 1/2) (Real.log n)]
    have hexp : Real.exp ((c - 1/2) * Real.log n) = (n:ℝ) ^ (c - 1/2) := by
      rw [Real.rpow_def_of_pos hn0]
      ring_nf
    have hpow : ((n:ℝ) ^ (-c) : ℝ) * ((n:ℝ) ^ (c - 1/2) : ℝ) = ((n:ℝ) ^ (-(1/2) : ℝ) : ℝ) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    have hsqrt : ((n:ℝ) ^ (-(1/2) : ℝ) : ℝ) = 1 / Real.sqrt n := by
      rw [Real.rpow_neg hn0.le, Real.sqrt_eq_rpow]
      exact (one_div _).symm
    calc ((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ)
        * (k (Real.log n) * ((Real.exp ((c - 1/2) * Real.log n) : ℝ) : ℂ))
        = ((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ)
          * (k (Real.log n) * (((n:ℝ) ^ (c - 1/2) : ℝ) : ℂ)) := by rw [hexp]
      _ = ((((Λ n : ℝ) * ((n:ℝ) ^ (-c) * (n:ℝ) ^ (c - 1/2)) : ℝ)) : ℂ) * k (Real.log n) := by
          push_cast
          ring
      _ = ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
          rw [hpow, hsqrt, mul_one_div]
theorem Ds {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (bD : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) :
    ∫ t : ℝ, (∑' n : ℕ, aD (tilt k (c - 1/2)) t
        * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n)
      = ∑' n : ℕ, ∫ t : ℝ, aD (tilt k (c - 1/2)) t
        * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := by
  have aam : ContDiff ℝ 2 (tilt k (c - 1/2)) := rJ hk _
  have aan : HasCompactSupport (tilt k (c - 1/2)) := jG bD _
  have aao := Zeta23.EF.dH aam aan
  have aap : Integrable (fun t : ℝ => aD (tilt k (c - 1/2)) t) :=
    Zeta23.EF.dY aao
  have hre : ∀ t : ℝ, ((c:ℂ) + t * I).re = c := by
    intro t
    simp
  have hnorm : ∀ (n : ℕ) (t : ℝ), ‖LSeries.term (fun n => (Λ n : ℂ)) ((c:ℂ) + t * I) n‖
      = if n = 0 then (0:ℝ) else (Λ n : ℝ) * ((n:ℝ) ^ (-c)) := by
    intro n t
    rw [LSeries.norm_term_eq, hre, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Real.rpow_neg (Nat.cast_nonneg n),
      div_eq_mul_inv]
  have hcont : ∀ n : ℕ, Continuous (fun t : ℝ =>
      LSeries.term (fun n => (Λ n : ℂ)) ((c:ℂ) + t * I) n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simpa [LSeries.term_zero] using continuous_const
    · simp only [LSeries.term_of_ne_zero hn]
      refine continuous_const.div ?_ (fun t => ?_)
      · refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
        exact_mod_cast hn
      · exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))
  have hint : ∀ n : ℕ, Integrable (fun t : ℝ => aD (tilt k (c - 1/2)) t
      * LSeries.term (fun n => (Λ n : ℂ)) ((c:ℂ) + t * I) n) := by
    intro n
    refine aap.mul_bdd (c := if n = 0 then (0:ℝ) else (Λ n : ℝ) * ((n:ℝ) ^ (-c)))
      (hcont n).aestronglyMeasurable ?_
    filter_upwards with t
    rw [hnorm n t]
  have heval : ∀ n : ℕ, (∫ t : ℝ, ‖aD (tilt k (c - 1/2)) t
      * LSeries.term (fun n => (Λ n : ℂ)) ((c:ℂ) + t * I) n‖)
      = (∫ t : ℝ, ‖aD (tilt k (c - 1/2)) t‖)
        * (if n = 0 then (0:ℝ) else (Λ n : ℝ) * ((n:ℝ) ^ (-c))) := by
    intro n
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [norm_mul, hnorm n t]
  have hcn : Summable (fun n : ℕ => if n = 0 then (0:ℝ) else (Λ n : ℝ) * ((n:ℝ) ^ (-c))) := by
    have hs : LSeriesSummable (fun n => (Λ n : ℂ)) (c : ℂ) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc1)
    have hns : Summable (fun n : ℕ => ‖LSeries.term (fun n => (Λ n : ℂ)) (c : ℂ) n‖) :=
      summable_norm_iff.mpr hs
    refine hns.congr fun n => ?_
    simpa using hnorm n 0
  have hsum : Summable (fun n : ℕ => ∫ t : ℝ, ‖aD (tilt k (c - 1/2)) t
      * LSeries.term (fun n => (Λ n : ℂ)) ((c:ℂ) + t * I) n‖) := by
    refine ((hcn.mul_left (∫ t : ℝ, ‖aD (tilt k (c - 1/2)) t‖)).congr fun n => ?_)
    rw [heval n]
  exact (MeasureTheory.hasSum_integral_of_summable_integral_norm hint hsum).tsum_eq.symm
theorem wP {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (bD : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, aW k (c + t * I) * (-logDeriv riemannZeta (c + t * I))
      = ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
  have h1 : ∀ t : ℝ, aW k (c + t * I) * (-logDeriv riemannZeta (c + t * I))
      = ∑' n : ℕ, aD (tilt k (c - 1/2)) t
        * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := fun t => Er hc1 t
  calc (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, aW k (c + t * I) * (-logDeriv riemannZeta (c + t * I))
      = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, ∑' n : ℕ, aD (tilt k (c - 1/2)) t
          * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := by
        rw [integral_congr_ae (Filter.Eventually.of_forall h1)]
    _ = (1 / (2 * Real.pi) : ℂ) * ∑' n : ℕ, ∫ t : ℝ, aD (tilt k (c - 1/2)) t
          * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := by
        rw [Ds hk bD hc1]
    _ = ∑' n : ℕ, (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, aD (tilt k (c - 1/2)) t
          * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := by
        rw [← tsum_mul_left]
    _ = ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) :=
        tsum_congr fun n => BT hk bD n
theorem jX : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1/4 ≤ s.re → s.re ≤ 1 →
    ‖Complex.digamma s‖ ≤ C * Real.log (2 + |s.im|) := by
  have hdiff : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ Complex.digamma s := by
    intro s hs
    have hzero : ∀ m : ℕ, s ≠ -(m : ℂ) := by
      intro m h
      rw [h] at hs
      simp only [Complex.neg_re, Complex.natCast_re] at hs
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have oQ : AnalyticAt ℂ Complex.Gamma s := by
      rw [Complex.analyticAt_iff_eventually_differentiableAt]
      filter_upwards [hopen.mem_nhds hs] with w hw
      refine Complex.differentiableAt_Gamma w fun m => ?_
      intro h
      rw [h] at hw
      simp only [Complex.neg_re, Complex.natCast_re] at hw
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have wO : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hzero
    have Je : AnalyticAt ℂ Complex.digamma s := by
      have h1 : AnalyticAt ℂ (deriv Complex.Gamma) s := oQ.deriv
      have h2 := h1.div oQ wO
      exact h2.congr (by
        filter_upwards with w
        rw [Complex.digamma_def, logDeriv_apply]
        rfl)
    exact Je.differentiableAt
  have hK : IsCompact (Complex.reProdIm (Set.Icc (1/4 : ℝ) 1) (Set.Icc (-(1/2) : ℝ) (1/2))) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have WI : ContinuousOn Complex.digamma
      (Complex.reProdIm (Set.Icc (1/4 : ℝ) 1) (Set.Icc (-(1/2) : ℝ) (1/2))) := by
    intro s hs
    have hsre : 1/4 ≤ s.re := (Complex.mem_reProdIm.mp hs).1.1
    exact ((hdiff s (by linarith)).continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn WI
  have hM0 : (0 : ℝ) ≤ M := by
    have h := hM (1/2 : ℂ) (by
      rw [Complex.mem_reProdIm]
      constructor
      · simp only [Complex.div_ofNat_re, Complex.one_re]
        norm_num
      · simp only [Complex.div_ofNat_im, Complex.one_im]
        norm_num)
    exact le_trans (norm_nonneg _) h
  have zX : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set K₀ : ℝ := 14 + Real.pi + Real.log 4 with hK₀
  have abL : (0 : ℝ) < K₀ := by positivity
  refine ⟨max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1, by positivity, fun s Dt Dm => ?_⟩
  have Gd : Real.log 2 ≤ Real.log (2 + |s.im|) := by
    apply Real.log_le_log (by norm_num)
    have := abs_nonneg s.im
    linarith
  have KR : (0 : ℝ) < Real.log (2 + |s.im|) := lt_of_lt_of_le zX Gd
  rcases le_or_gt (|s.im|) (1/2) with him | him
  · 
    have hsK : s ∈ Complex.reProdIm (Set.Icc (1/4 : ℝ) 1) (Set.Icc (-(1/2) : ℝ) (1/2)) := by
      rw [Complex.mem_reProdIm]
      refine ⟨⟨Dt, Dm⟩, ?_⟩
      rw [Set.mem_Icc]
      constructor <;> [linarith [neg_abs_le s.im]; linarith [le_abs_self s.im]]
    calc ‖Complex.digamma s‖ ≤ M := hM s hsK
      _ = (M / Real.log 2) * Real.log 2 := by
          field_simp
      _ ≤ (max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1) * Real.log (2 + |s.im|) := by
          apply mul_le_mul ?_ Gd zX.le (by positivity)
          calc M / Real.log 2 ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) := le_max_left _ _
            _ ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1 := by linarith
  · 
    have YK : (0 : ℝ) < s.re := by linarith
    have hst := Zeta23.oR.vO (w := s) YK (by linarith)
    have RD : (1/4 : ℝ) ≤ ‖s‖ :=
      le_trans Dt (le_trans (le_abs_self _) (Complex.abs_re_le_norm s))
    have DQ : (0 : ℝ) < ‖s‖ := by linarith
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, norm_zero] at DQ
      exact lt_irrefl 0 DQ
    have ZK : ‖s‖ ≤ 1 + |s.im| := by
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 1 + |s.im| := by
            have : |s.re| ≤ 1 := by
              rw [abs_le]
              constructor <;> linarith
            linarith
    have WJ : ‖Complex.log s‖ ≤ |Real.log ‖s‖| + Real.pi := by
      calc ‖Complex.log s‖ ≤ |(Complex.log s).re| + |(Complex.log s).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ ≤ |Real.log ‖s‖| + Real.pi := by
            rw [Complex.log_re, Complex.log_im]
            have := Complex.abs_arg_le_pi s
            linarith [abs_nonneg (Complex.arg s)]
    have Tk : |Real.log ‖s‖| ≤ Real.log 4 + Real.log (2 + |s.im|) := by
      rcases le_or_gt (Real.log ‖s‖) 0 with hneg | hpos
      · 
        have h1 : Real.log (1/4 : ℝ) ≤ Real.log ‖s‖ := Real.log_le_log (by norm_num) RD
        have h2 : Real.log (1/4 : ℝ) = -Real.log 4 := by
          rw [show (1/4 : ℝ) = 4⁻¹ by norm_num, Real.log_inv]
        rw [abs_of_nonpos hneg]
        have h3 : (0 : ℝ) ≤ Real.log (2 + |s.im|) := by
          apply Real.log_nonneg
          have := abs_nonneg s.im
          linarith
        linarith
      · rw [abs_of_pos hpos]
        have h1 : Real.log ‖s‖ ≤ Real.log (2 + |s.im|) := by
          apply Real.log_le_log DQ
          have := abs_nonneg s.im
          linarith
        have h2 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        linarith
    have WK : ‖(1/2 : ℂ) / s‖ ≤ 2 := by
      rw [norm_div]
      have h1 : ‖(1/2 : ℂ)‖ = 1/2 := by
        rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by norm_num)]
      rw [h1, div_le_iff₀ DQ]
      linarith
    have Tj : 3 / s.im ^ 2 ≤ 12 := by
      have h1 : (1/4 : ℝ) ≤ s.im ^ 2 := by
        have h2 : (1/2 : ℝ) ≤ |s.im| := him.le
        nlinarith [abs_nonneg s.im, sq_abs s.im]
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith
    have aaq : ‖Complex.digamma s‖
        ≤ Real.log (2 + |s.im|) + K₀ := by
      have h1 : ‖Complex.digamma s‖
          ≤ ‖Complex.digamma s - Complex.log s + (1/2 : ℂ) / s‖ + ‖Complex.log s‖
            + ‖(1/2 : ℂ) / s‖ := by
        have h2 : Complex.digamma s = (Complex.digamma s - Complex.log s + (1/2 : ℂ) / s)
            + Complex.log s - (1/2 : ℂ) / s := by ring
        calc ‖Complex.digamma s‖
            = ‖(Complex.digamma s - Complex.log s + (1/2 : ℂ) / s)
                + Complex.log s - (1/2 : ℂ) / s‖ := by rw [← h2]
          _ ≤ ‖(Complex.digamma s - Complex.log s + (1/2 : ℂ) / s) + Complex.log s‖
              + ‖(1/2 : ℂ) / s‖ := norm_sub_le _ _
          _ ≤ ‖Complex.digamma s - Complex.log s + (1/2 : ℂ) / s‖ + ‖Complex.log s‖
              + ‖(1/2 : ℂ) / s‖ := by
              have := norm_add_le (Complex.digamma s - Complex.log s + (1/2 : ℂ) / s)
                (Complex.log s)
              linarith
      rw [hK₀]
      have Wv : Real.pi < 4 := Real.pi_lt_four
      calc ‖Complex.digamma s‖
          ≤ ‖Complex.digamma s - Complex.log s + (1/2 : ℂ) / s‖ + ‖Complex.log s‖
            + ‖(1/2 : ℂ) / s‖ := h1
        _ ≤ 3 / s.im ^ 2 + (|Real.log ‖s‖| + Real.pi) + 2 := by
            have := hst
            linarith [WJ, WK]
        _ ≤ 12 + ((Real.log 4 + Real.log (2 + |s.im|)) + Real.pi) + 2 := by
            linarith [Tj, Tk]
        _ ≤ Real.log (2 + |s.im|) + (14 + Real.pi + Real.log 4) := by linarith
    calc ‖Complex.digamma s‖ ≤ Real.log (2 + |s.im|) + K₀ := aaq
      _ ≤ Real.log (2 + |s.im|) + (K₀ / Real.log 2) * Real.log (2 + |s.im|) := by
          have h3 : K₀ / Real.log 2 * Real.log 2 ≤ K₀ / Real.log 2 * Real.log (2 + |s.im|) :=
            mul_le_mul_of_nonneg_left Gd (by positivity)
          have h4 : K₀ / Real.log 2 * Real.log 2 = K₀ := by field_simp
          linarith
      _ = (1 + K₀ / Real.log 2) * Real.log (2 + |s.im|) := by ring
      _ ≤ (max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1) * Real.log (2 + |s.im|) := by
          apply mul_le_mul_of_nonneg_right ?_ KR.le
          calc (1 + K₀ / Real.log 2) ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) :=
                le_max_right _ _
            _ ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1 := by linarith
lemma jC {f : ℂ → ℂ} {σ : ℝ} (hf : ∀ t : ℝ, DifferentiableAt ℂ f (σ + t * I))
    {φ : ℝ → ℝ} (hφ : Integrable φ) (hb : ∀ t : ℝ, ‖f (σ + t * I)‖ ≤ φ t) :
    Integrable (fun t : ℝ => f (σ + t * I)) := by
  have hc : Continuous (fun t : ℝ => f (σ + t * I)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hg : Continuous (fun t : ℝ => (σ : ℂ) + t * I) := by fun_prop
    show ContinuousAt (f ∘ fun t : ℝ => (σ : ℂ) + t * I) t
    exact ContinuousAt.comp_of_eq (hf t).continuousAt hg.continuousAt rfl
  exact hφ.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)
theorem qo {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ f s)
    {φ : ℝ → ℝ} (hφ : Integrable φ)
    (hbound : ∀ (σ t : ℝ), a ≤ σ → σ ≤ b → ‖f (σ + t * I)‖ ≤ φ t)
    (Jv : Filter.Tendsto φ Filter.atTop (nhds 0))
    (Jw : Filter.Tendsto φ Filter.atBot (nhds 0)) :
    ∫ t : ℝ, f (b + t * I) = ∫ t : ℝ, f (a + t * I) := by
  have hint : ∀ σ : ℝ, a ≤ σ → σ ≤ b → Integrable (fun t : ℝ => f (σ + t * I)) := fun σ h1 h2 =>
    jC (fun t => hf _ (by simp [h1]) (by simp [h2])) hφ (fun t => hbound σ t h1 h2)
  have acD : ∀ t, 0 ≤ φ t := fun t => (norm_nonneg _).trans (hbound a t le_rfl hab)
  have Qb : ∀ R : ℝ, (∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I))
      = -I * ((∫ x in a..b, f (x + R * I)) - (∫ x in a..b, f (x + (-R) * I))) := by
    intro R
    have hdiff : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc (-R) R) := by
      intro z hz
      rw [Set.uIcc_of_le hab] at hz
      exact (hf z hz.1.1 hz.1.2).differentiableWithinAt
    have H := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) + (-R : ℝ) * I) ((b : ℂ) + (R : ℝ) * I) (by simpa using hdiff)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add, smul_eq_mul] at H
    have key : I * ((∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I)))
        = (∫ x in a..b, f (x + R * I)) - (∫ x in a..b, f (x + (-R) * I)) := by
      push_cast at H ⊢
      linear_combination H
    calc (∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I))
        = -(I * I) * ((∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I))) := by
          rw [I_mul_I]; ring
      _ = -I * (I * ((∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I)))) := by
          ring
      _ = _ := by rw [key]
  have hsmall : ∀ R : ℝ, ‖(∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I))‖
      ≤ (b - a) * (φ R + φ (-R)) := by
    intro R
    rw [Qb R, norm_mul, norm_neg, Complex.norm_I, one_mul]
    have h1 : ‖∫ x in a..b, f (x + R * I)‖ ≤ φ R * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => by
        rw [Set.uIoc_of_le hab] at hx
        exact hbound x R hx.1.le hx.2
    have h2 : ‖∫ x in a..b, f (x + (-R) * I)‖ ≤ φ (-R) * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => by
        rw [Set.uIoc_of_le hab] at hx
        have := hbound x (-R) hx.1.le hx.2
        simpa using this
    rw [abs_of_nonneg (by linarith)] at h1 h2
    calc ‖(∫ x in a..b, f (x + R * I)) - (∫ x in a..b, f (x + (-R) * I))‖
        ≤ ‖∫ x in a..b, f (x + R * I)‖ + ‖∫ x in a..b, f (x + (-R) * I)‖ := norm_sub_le _ _
      _ ≤ φ R * (b - a) + φ (-R) * (b - a) := add_le_add h1 h2
      _ = (b - a) * (φ R + φ (-R)) := by ring
  set g : ℝ → ℂ := fun R => (∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I)) with hg
  have Qc : Filter.Tendsto g Filter.atTop (nhds ((∫ t : ℝ, f (b + t * I)) - (∫ t : ℝ, f (a + t * I)))) := by
    apply Filter.Tendsto.sub
    · exact intervalIntegral_tendsto_integral (hint b hab le_rfl) Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
    · exact intervalIntegral_tendsto_integral (hint a le_rfl hab) Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  have YL : Filter.Tendsto g Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun R => norm_nonneg _) (fun R => hsmall R) ?_
    have : Filter.Tendsto (fun R => (b - a) * (φ R + φ (-R))) Filter.atTop (nhds ((b - a) * (0 + 0))) :=
      (Jv.add (Jw.comp Filter.tendsto_neg_atTop_atBot)).const_mul _
    simpa using this
  have := tendsto_nhds_unique Qc YL
  exact sub_eq_zero.mp this
theorem jI {k : ℝ → ℂ} (hk : Continuous k) (bD : HasCompactSupport k) :
    Differentiable ℂ (aD k) := by
  intro z₀
  obtain ⟨Λ₁, Nl⟩ := Zeta23.EF.bZ bD
  have WL : ∀ u : ℝ, k u ≠ 0 → |u| ≤ max Λ₁ 0 := fun u hu => (Nl u hu).trans (le_max_left _ _)
  have abm : (0:ℝ) ≤ max Λ₁ 0 := le_max_right _ _
  have Qd : Integrable (fun u : ℝ => ‖k u‖
      * (max Λ₁ 0 * Real.exp ((‖z₀‖ + 1) * max Λ₁ 0))) :=
    (hk.norm.integrable_of_hasCompactSupport bD.norm).mul_const _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (s := Metric.ball z₀ 1) (x₀ := z₀)
    (F := fun z (u : ℝ) => k u * cexp (I * z * u))
    (F' := fun z (u : ℝ) => k u * ((I : ℂ) * u) * cexp (I * z * u))
    (bound := fun u : ℝ => ‖k u‖ * (max Λ₁ 0 * Real.exp ((‖z₀‖ + 1) * max Λ₁ 0)))
    (Metric.ball_mem_nhds z₀ one_pos)
    (Filter.Eventually.of_forall fun z => (Continuous.aestronglyMeasurable (by fun_prop)))
    ((Continuous.integrable_of_hasCompactSupport (by fun_prop) bD.mul_right))
    (Continuous.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun u => fun z hz => ?_)
    Qd
    (Filter.Eventually.of_forall fun u => fun z hz => ?_)
  · exact ⟨_, key.2.hasFDerivAt⟩
  · rcases eq_or_ne (k u) 0 with hku | hku
    · simp [hku]
    · have hu := WL u hku
      have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
        have := norm_sub_norm_le z z₀
        rw [Metric.mem_ball, Complex.dist_eq] at hz
        linarith [le_of_lt hz]
      rw [norm_mul, norm_mul, Complex.norm_exp]
      have h1 : ‖(I : ℂ) * u‖ ≤ max Λ₁ 0 := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact hu
      have h2 : (I * z * u).re ≤ (‖z₀‖ + 1) * max Λ₁ 0 := by
        have hre : (I * z * u).re = -(z.im * u) := by
          simp [Complex.mul_re, Complex.mul_im]
        rw [hre]
        calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
          _ = |z.im| * |u| := abs_mul _ _
          _ ≤ (‖z₀‖ + 1) * max Λ₁ 0 := by
              refine mul_le_mul ?_ hu (abs_nonneg _) (by positivity)
              exact (Complex.abs_im_le_norm z).trans hz'
      calc ‖k u‖ * ‖(I : ℂ) * u‖ * Real.exp ((I * z * u).re)
          ≤ ‖k u‖ * (max Λ₁ 0) * Real.exp ((‖z₀‖ + 1) * max Λ₁ 0) := by
            refine mul_le_mul (mul_le_mul le_rfl h1 (norm_nonneg _) (norm_nonneg _))
              (Real.exp_le_exp.mpr h2) (Real.exp_nonneg _) (by positivity)
        _ = ‖k u‖ * (max Λ₁ 0 * Real.exp ((‖z₀‖ + 1) * max Λ₁ 0)) := by ring
  · have h1 : HasDerivAt (fun z : ℂ => I * z * (u:ℂ)) (I * u) z := by
      have := ((hasDerivAt_id z).const_mul (I : ℂ)).mul_const ((u:ℂ))
      simpa [mul_comm, mul_assoc, mul_left_comm] using this
    have h2 := h1.cexp
    have h3 := h2.const_mul (k u)
    exact h3.congr_deriv (by ring)
lemma Dv {x : ℝ} (hx : 0 ≤ x) :
    Real.log (2 + x) / (1 + x ^ 2) ≤ 6 * (1 + x) ^ (-(3 / 2 : ℝ)) := by
  have h1 := Real.log_le_rpow_div (show (0:ℝ) ≤ 2 + x by linarith) (show (0:ℝ) < 1/2 by norm_num)
  have h2 : (2 + x) ^ (1 / 2 : ℝ) ≤ (3 / 2) * (1 + x) ^ (1 / 2 : ℝ) := by
    have : (2 + x) ^ (1 / 2 : ℝ) ≤ ((9/4) * (1 + x)) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    rw [Real.mul_rpow (by norm_num) (by linarith)] at this
    rw [show ((9:ℝ)/4) ^ (1/2:ℝ) = 3/2 by
      rw [show (9:ℝ)/4 = (3/2) ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num] at this
    exact this
  have hlog : Real.log (2 + x) ≤ 3 * (1 + x) ^ (1 / 2 : ℝ) := by
    have : (2 + x) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * (2 + x) ^ (1 / 2 : ℝ) := by ring
    rw [this] at h1; linarith
  have hsq : 1 / (1 + x ^ 2) ≤ 2 * (1 + x) ^ (-2 : ℝ) := by
    rw [Real.rpow_neg (by linarith), Real.rpow_two, div_le_iff₀ (by positivity)]
    rw [show 2 * ((1 + x) ^ 2)⁻¹ * (1 + x ^ 2) = 2 * (1 + x ^ 2) / (1 + x) ^ 2 by ring,
      le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (x - 1)]
  have h0 : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
  calc Real.log (2 + x) / (1 + x ^ 2) = Real.log (2 + x) * (1 / (1 + x ^ 2)) := by ring
    _ ≤ (3 * (1 + x) ^ (1 / 2 : ℝ)) * (2 * (1 + x) ^ (-2 : ℝ)) :=
        mul_le_mul hlog hsq (by positivity) (by positivity)
    _ = 6 * ((1 + x) ^ (1 / 2 : ℝ) * (1 + x) ^ (-2 : ℝ)) := by ring
    _ = 6 * (1 + x) ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add (by linarith)]; norm_num
lemma wI {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hki : Integrable k) {Lam : ℝ}
    (aar : 0 ≤ Lam) (hsupp : ∀ u, k u ≠ 0 → |u| ≤ Lam) {z : ℂ} (hz : |z.im| ≤ 1) :
    ‖aD k z‖ ≤ 2 * Real.exp Lam * ((∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖) / (1 + z.re ^ 2) := by
  set N₀ := ∫ u, ‖k u‖ with hN₀
  set N₂ := ∫ u, ‖deriv (deriv k) u‖ with hN₂
  have Nm : 0 ≤ N₀ := integral_nonneg fun _ => norm_nonneg _
  have RH : 0 ≤ N₂ := integral_nonneg fun _ => norm_nonneg _
  have he : Real.exp (|z.im| * Lam) ≤ Real.exp Lam := Real.exp_le_exp.mpr (by nlinarith [abs_nonneg z.im])
  by_cases hre : z.re ^ 2 ≤ 1
  · have b0 := jz hki hsupp z
    calc ‖aD k z‖ ≤ Real.exp (|z.im| * Lam) * N₀ := b0
      _ ≤ Real.exp Lam * N₀ := mul_le_mul_of_nonneg_right he Nm
      _ ≤ 2 * Real.exp Lam * (N₀ + N₂) / (1 + z.re ^ 2) := by
          rw [le_div_iff₀ (by positivity)]
          have := Real.exp_pos Lam
          nlinarith [mul_nonneg this.le RH, mul_nonneg this.le Nm]
  · push Not at hre
    have hz0 : z ≠ 0 := fun h => by rw [h] at hre; simp at hre; linarith
    have b2 := kL hk hsupp hz0
    have hzn : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; nlinarith [sq_nonneg z.im]
    have hzpos : 0 < ‖z‖ ^ 2 := by linarith
    calc ‖aD k z‖ ≤ Real.exp (|z.im| * Lam) * N₂ / ‖z‖ ^ 2 := b2
      _ ≤ Real.exp Lam * N₂ / z.re ^ 2 := by
          gcongr
      _ ≤ 2 * Real.exp Lam * (N₀ + N₂) / (1 + z.re ^ 2) := by
          rw [div_le_div_iff₀ (by linarith) (by positivity)]
          have := Real.exp_pos Lam
          nlinarith [mul_nonneg this.le RH, mul_nonneg this.le Nm]
lemma tM : ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 2 →
    ‖logDeriv Complex.Gammaℝ (σ + t * I)‖ ≤ C * Real.log (2 + |t|) := by
  obtain ⟨C, hC, hψ⟩ := jX
  have abo : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  refine ⟨2 * Real.log Real.pi + C, by positivity, ?_⟩
  intro σ t h1 h2
  have hre : 0 < ((σ : ℂ) + t * I).re := by simp; linarith
  rw [gP hre]
  have hs2 : ((σ : ℂ) + t * I) / 2 = ((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  have Tm := hψ (((σ : ℂ) + t * I) / 2) (by rw [hs2]; simp; linarith) (by rw [hs2]; simp; linarith)
  have him : (((σ : ℂ) + t * I) / 2).im = t / 2 := by rw [hs2]; simp
  rw [him] at Tm
  have zX : Real.log 2 ≤ Real.log (2 + |t|) := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have abM : (1:ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have WM : Real.log (2 + |t / 2|) ≤ Real.log (2 + |t|) := by
    apply Real.log_le_log (by positivity)
    rw [abs_div, abs_two]; linarith [abs_nonneg t]
  have Jm : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  calc ‖-((Real.log Real.pi : ℝ) : ℂ) / 2 + 1 / 2 * Complex.digamma (((σ : ℂ) + t * I) / 2)‖
      ≤ ‖-((Real.log Real.pi : ℝ) : ℂ) / 2‖ + ‖1 / 2 * Complex.digamma (((σ : ℂ) + t * I) / 2)‖ :=
        norm_add_le _ _
    _ = Real.log Real.pi / 2 + (1 / 2) * ‖Complex.digamma (((σ : ℂ) + t * I) / 2)‖ := by
        rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Jm, norm_mul]
        norm_num
    _ ≤ Real.log Real.pi / 2 + (1 / 2) * (C * Real.log (2 + |t / 2|)) := by gcongr
    _ ≤ Real.log Real.pi * Real.log (2 + |t|) * 2 + C * Real.log (2 + |t|) := by
        nlinarith [hC.le, WM, Real.log_nonneg (show (1:ℝ) ≤ 2 + |t/2| by linarith [abs_nonneg (t/2)])]
    _ = (2 * Real.log Real.pi + C) * Real.log (2 + |t|) := by ring
theorem Gh {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (bD : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) :
    ∫ t : ℝ, (aW k (c + t * I) + aW k (1 - c - t * I)) * logDeriv Complex.Gammaℝ (c + t * I)
      = ∫ t : ℝ, aD k t
        * (logDeriv Complex.Gammaℝ (1/2 + t * I) + logDeriv Complex.Gammaℝ (1/2 - t * I)) := by
  set G := logDeriv Complex.Gammaℝ with hG
  have ZL : Differentiable ℂ (aW k) := by
    have h := jI hk.continuous bD
    show Differentiable ℂ (fun s => aD k ((s - 1/2) / I))
    exact h.comp ((differentiable_id.sub_const _).div_const I)
  have ZM : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ G s := by
    intro s hs
    have hA := pW hs
    have : G = fun z => deriv Gammaℝ z / Gammaℝ z := by funext z; rw [hG, logDeriv_apply]
    rw [this]
    exact hA.deriv.differentiableAt.div hA.differentiableAt (Gammaℝ_ne_zero_of_re_pos hs)
  set f₁ : ℂ → ℂ := fun s => aW k s * G s with hf₁
  set f₂ : ℂ → ℂ := fun s => aW k (1 - s) * G s with hf₂
  have Np : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → DifferentiableAt ℂ f₁ s := fun s h1 _ =>
    (ZL s).mul (ZM s (by linarith))
  have Nq : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → DifferentiableAt ℂ f₂ s := fun s h1 _ =>
    ((ZL (1 - s)).comp s ((differentiableAt_const _).sub differentiableAt_id)).mul (ZM s (by linarith))
  obtain ⟨WO, Vm⟩ := Zeta23.EF.bZ bD
  set Lam : ℝ := max WO 0 with aar
  have YM : 0 ≤ Lam := le_max_right _ _
  have hsupp : ∀ u, k u ≠ 0 → |u| ≤ Lam := fun u hu => (Vm u hu).trans (le_max_left _ _)
  have hki : Integrable k := hk.continuous.integrable_of_hasCompactSupport bD
  set N : ℝ := (∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖ with hN
  have hN0 : 0 ≤ N := add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  obtain ⟨CG, hCG, hGb⟩ := tM
  set M : ℝ := 2 * Real.exp Lam * N * CG * 6 with hM
  have hM0 : 0 ≤ M := by positivity
  set φ : ℝ → ℝ := fun t => M * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) with hφ
  have hφi : Integrable φ := by
    have := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3/2)
      (by rw [Module.finrank_self]; norm_num)).const_mul M
    exact this
  have RJ : Filter.Tendsto (fun x : ℝ => M * (1 + x) ^ (-(3 / 2 : ℝ))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => (1 + x) ^ (-(3 / 2 : ℝ))) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp (Filter.tendsto_atTop_add_const_left _ 1 Filter.tendsto_id)
    simpa using h1.const_mul M
  have Jv : Filter.Tendsto φ Filter.atTop (nhds 0) := by
    have : φ = (fun x : ℝ => M * (1 + x) ^ (-(3 / 2 : ℝ))) ∘ (fun t : ℝ => ‖t‖) := by
      funext t; simp [hφ]
    rw [this]
    exact RJ.comp (by simpa using Filter.tendsto_abs_atTop_atTop)
  have Jw : Filter.Tendsto φ Filter.atBot (nhds 0) := by
    have : φ = (fun x : ℝ => M * (1 + x) ^ (-(3 / 2 : ℝ))) ∘ (fun t : ℝ => ‖t‖) := by
      funext t; simp [hφ]
    rw [this]
    exact RJ.comp (by simpa using Filter.tendsto_abs_atBot_atTop)
  have hkey : ∀ (σ t : ℝ) (z : ℂ), 1 / 2 ≤ σ → σ ≤ c → |z.im| ≤ 1 → z.re ^ 2 = t ^ 2 →
      ‖aD k z‖ * ‖G (σ + t * I)‖ ≤ φ t := by
    intro σ t z h1 h2 hz hzt
    have hH := wI hk hki YM hsupp hz
    rw [hzt] at hH
    have hGG := hGb σ t h1 (by linarith)
    have hl := Dv (abs_nonneg t)
    calc ‖aD k z‖ * ‖G (σ + t * I)‖
        ≤ (2 * Real.exp Lam * N / (1 + t ^ 2)) * (CG * Real.log (2 + |t|)) :=
          mul_le_mul hH hGG (norm_nonneg _) (by positivity)
      _ = (2 * Real.exp Lam * N * CG) * (Real.log (2 + |t|) / (1 + |t| ^ 2)) := by
          rw [sq_abs]; ring
      _ ≤ (2 * Real.exp Lam * N * CG) * (6 * (1 + |t|) ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hl (by positivity)
      _ = φ t := by simp only [hφ, hM, Real.norm_eq_abs]; ring
  have hz₁ : ∀ σ t : ℝ, ((σ : ℂ) + t * I - 1 / 2) / I = (t : ℂ) + ((1 / 2 - σ : ℝ) : ℂ) * I := by
    intro σ t; field_simp; push_cast; ring_nf; simp [I_sq]; ring
  have hz₂ : ∀ σ t : ℝ, ((1 - ((σ : ℂ) + t * I)) - 1 / 2) / I = ((-t : ℝ) : ℂ) + ((σ - 1 / 2 : ℝ) : ℂ) * I := by
    intro σ t; field_simp; push_cast; ring_nf; simp [I_sq]; ring
  have hb₁ : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ c → ‖f₁ (σ + t * I)‖ ≤ φ t := by
    intro σ t h1 h2
    simp only [hf₁, aW, norm_mul]
    rw [hz₁]
    refine hkey σ t _ h1 h2 ?_ ?_
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add, add_zero]
      rw [abs_le]; constructor <;> linarith
    · simp
  have hb₂ : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ c → ‖f₂ (σ + t * I)‖ ≤ φ t := by
    intro σ t h1 h2
    simp only [hf₂, aW, norm_mul]
    rw [hz₂]
    refine hkey σ t _ h1 h2 ?_ ?_
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add, add_zero]
      rw [abs_le]; constructor <;> linarith
    · simp
  have hab : (1:ℝ) / 2 ≤ c := by linarith
  have hs₁ := qo hab Np hφi hb₁ Jv Jw
  have hs₂ := qo hab Nq hφi hb₂ Jv Jw
  have WQ : Integrable (fun t : ℝ => f₁ (c + t * I)) :=
    jC (fun t => Np _ (by simp; linarith) (by simp)) hφi (fun t => hb₁ c t hab le_rfl)
  have WR : Integrable (fun t : ℝ => f₂ (c + t * I)) :=
    jC (fun t => Nq _ (by simp; linarith) (by simp)) hφi (fun t => hb₂ c t hab le_rfl)
  have WS : Integrable (fun t : ℝ => f₁ ((1/2 : ℝ) + t * I)) :=
    jC (fun t => Np _ (by simp) (by simp; linarith)) hφi (fun t => hb₁ (1/2) t le_rfl hab)
  have WT : Integrable (fun t : ℝ => f₂ ((1/2 : ℝ) + t * I)) :=
    jC (fun t => Nq _ (by simp) (by simp; linarith)) hφi (fun t => hb₂ (1/2) t le_rfl hab)
  have hL : ∫ t : ℝ, (aW k (c + t * I) + aW k (1 - c - t * I)) * G (c + t * I)
      = (∫ t : ℝ, f₁ (c + t * I)) + ∫ t : ℝ, f₂ (c + t * I) := by
    rw [← integral_add WQ WR]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hf₁, hf₂]
    rw [show (1 : ℂ) - (↑c + ↑t * I) = 1 - ↑c - ↑t * I by ring]
    ring
  rw [hL, hs₁, hs₂]
  have e₁ : ∀ t : ℝ, f₁ ((1/2 : ℝ) + t * I) = aD k t * G (1/2 + t * I) := by
    intro t
    simp only [hf₁, aW]
    congr 2
    · push_cast; field_simp; ring
    · push_cast; ring
  have e₂ : ∀ t : ℝ, f₂ ((1/2 : ℝ) + t * I) = aD k (((-t : ℝ) : ℂ)) * G (1/2 + t * I) := by
    intro t
    simp only [hf₂, aW]
    congr 2
    · push_cast; field_simp; ring
    · push_cast; ring
  simp_rw [e₁, e₂]
  have hneg : ∫ t : ℝ, aD k (((-t : ℝ) : ℂ)) * G (1/2 + t * I)
      = ∫ t : ℝ, aD k t * G (1/2 - t * I) := by
    rw [← integral_neg_eq_self]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [neg_neg]
    push_cast
    ring_nf
  rw [hneg, ← integral_add]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    ring
  · have := WS; simp_rw [e₁] at this; exact this
  · have := WT; simp_rw [e₂] at this
    have h2 := this.comp_neg
    simp only [neg_neg] at h2
    refine (h2.congr (Filter.Eventually.of_forall fun t => ?_))
    push_cast; ring_nf
end cw
end Zeta23
end
end

-- Zeta23.cw.Landau
section
noncomputable section
namespace Zeta23
namespace cw
open Complex Set
section Tv
open Metric
lemma Jx {f : ℂ → ℂ} (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf0 : f 0 ≠ 0) {r : ℝ} (hr1 : r < 1) (hfin : (bC 1 f).Finite)
    {z : ℂ} (hz : ‖z‖ ≤ r) : Cf r f z ≠ 0 := by
  have nS := aP hr1 hfin
  by_cases hmem : z ∈ bC r f
  · 
    obtain ⟨Fy, _, Mt, hZF, _⟩ := rS hr1 hfa hf0 hmem
    unfold Cf
    rw [dif_pos nS, dif_pos hmem, hZF]
    apply div_ne_zero Mt
    refine Finset.prod_ne_zero_iff.mpr fun ρ hρ => ?_
    have hne : z ≠ ρ := by
      intro h
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hρ
      exact hρ.2 h.symm
    exact pow_ne_zero _ (sub_ne_zero.mpr hne)
  · unfold Cf
    rw [dif_pos nS, dif_neg hmem]
    have hfz : f z ≠ 0 := by
      intro h
      exact hmem ⟨hz, h⟩
    apply div_ne_zero hfz
    refine Finset.prod_ne_zero_iff.mpr fun ρ hρ => ?_
    have hρ' := nS.mem_toFinset.mp hρ
    have hne : z ≠ ρ := by
      rintro rfl
      exact hmem hρ'
    exact pow_ne_zero _ (sub_ne_zero.mpr hne)
lemma Gk {f : ℂ → ℂ} {r : ℝ} (hr1 : r < 1) (hfin : (bC 1 f).Finite)
    {z : ℂ} (hz : z ∉ bC r f) :
    f z = (∏ ρ ∈ (aP hr1 hfin).toFinset, (z - ρ) ^ analyticOrderNatAt f ρ)
      * Cf r f z := by
  have nS := aP hr1 hfin
  unfold Cf
  rw [dif_pos nS, dif_neg hz]
  rw [mul_div_cancel₀]
  refine Finset.prod_ne_zero_iff.mpr fun ρ hρ => ?_
  have hρ' := nS.mem_toFinset.mp hρ
  have hne : z ≠ ρ := by
    rintro rfl
    exact hz hρ'
  exact pow_ne_zero _ (sub_ne_zero.mpr hne)
lemma Dw {s : Finset ℂ} {m : ℂ → ℕ} {z : ℂ} (hz : ∀ ρ ∈ s, z ≠ ρ) :
    logDeriv (fun w => ∏ ρ ∈ s, (w - ρ) ^ m ρ) z = ∑ ρ ∈ s, (m ρ : ℂ) / (z - ρ) := by
  rw [logDeriv_prod (f := fun ρ w => (w - ρ) ^ m ρ)
    (fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hz ρ hρ))) (fun ρ _ => by fun_prop)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hd : HasDerivAt (fun w : ℂ => w - ρ) 1 z := (hasDerivAt_id z).sub_const ρ
  rw [logDeriv_fun_pow hd.differentiableAt, logDeriv_apply, hd.deriv]
  ring
lemma KS {f : ℂ → ℂ} (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf0 : f 0 ≠ 0) {r : ℝ} (hr1 : r < 1) (hfin : (bC 1 f).Finite)
    {z : ℂ} (hz : ‖z‖ < r) (hfz : f z ≠ 0) :
    logDeriv f z = (∑ ρ ∈ (aP hr1 hfin).toFinset,
        (analyticOrderNatAt f ρ : ℂ) / (z - ρ)) + logDeriv (Cf r f) z := by
  have nS := aP hr1 hfin
  set P0 : ℂ → ℂ := fun w => ∏ ρ ∈ nS.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ with hP0
  have hU : IsOpen (Metric.ball (0 : ℂ) r \ bC r f) :=
    Metric.isOpen_ball.sdiff nS.isClosed
  have hzU : z ∈ Metric.ball (0 : ℂ) r \ bC r f :=
    ⟨mem_ball_zero_iff.mpr hz, fun h => hfz h.2⟩
  have heq : f =ᶠ[nhds z] fun w => P0 w * Cf r f w := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    exact Gk hr1 hfin hw.2
  have hzne : ∀ ρ ∈ nS.toFinset, z ≠ ρ := by
    intro ρ hρ
    rintro rfl
    exact hfz (nS.mem_toFinset.mp hρ).2
  have aas : P0 z ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hzne ρ hρ))
  have aat : Cf r f z ≠ 0 := Jx hfa hf0 hr1 hfin hz.le
  have aau : DifferentiableAt ℂ P0 z :=
    DifferentiableAt.fun_finsetProd fun ρ _ =>
      ((differentiable_id.sub_const ρ).differentiableAt).pow _
  have aav : DifferentiableAt ℂ (Cf r f) z := by
    have hR : r < (r + 1) / 2 := by linarith
    have hR1 : (r + 1) / 2 < 1 := by linarith
    exact ((sW hR hR1 hfa hf0) z (by
      rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
      calc ‖z‖ ≤ r := hz.le
        _ ≤ (r + 1) / 2 := by linarith)).differentiableAt
  calc logDeriv f z = logDeriv (fun w => P0 w * Cf r f w) z := by
        unfold logDeriv
        simp only [Pi.div_apply]
        rw [heq.deriv_eq, heq.eq_of_nhds]
    _ = logDeriv P0 z + logDeriv (Cf r f) z := logDeriv_mul z aas aat aau aav
    _ = _ := by rw [hP0, Dw hzne]
lemma BU {f : ℂ → ℂ} {B : ℝ}
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0 : f 0 = 1)
    (hfin : (bC 1 f).Finite) (OO : 2 ≤ B)
    (hfB : ∀ w : ℂ, ‖w‖ ≤ 24/25 → ‖f w‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ 83/100) :
    ‖logDeriv (Cf (22/25) f) z‖ ≤ 44795000 * Real.log B := by
  have hf0' : f 0 ≠ 0 := by rw [hf0]; exact one_ne_zero
  have nS : (bC (22/25) f).Finite := aP (by norm_num) hfin
  have DN : 0 < Real.log B := Real.log_pos (by linarith)
  have hcount : ((∑ ρ ∈ (aP (by norm_num : (22/25 : ℝ) < 1) hfin).toFinset,
      analyticOrderNatAt f ρ : ℕ) : ℝ) ≤ 1 / Real.log ((24/25) / (22/25)) * Real.log B := by
    exact_mod_cast zS (by norm_num) (by norm_num)
      (by norm_num : (22/25:ℝ) < 24/25) (by norm_num) hfa hf0 hfin (fun w hw => hfB w hw)
  set K : ℕ := ∑ ρ ∈ (aP (by norm_num : (22/25 : ℝ) < 1) hfin).toFinset,
    analyticOrderNatAt f ρ with hK
  have hsphere : ∀ w : ℂ, ‖w‖ = 24/25 → ‖Cf (22/25) f w‖ ≤ B * (25/2 : ℝ) ^ K := by
    intro w hw
    have YN : w ∉ bC (22/25) f := by
      intro h
      have := h.1
      rw [hw] at this
      norm_num at this
    have kF := aP (by norm_num : (22/25 : ℝ) < 1) hfin
    have hdist : ∀ ρ ∈ kF.toFinset, (2/25 : ℝ) ≤ ‖w - ρ‖ := by
      intro ρ hρ
      have hρ' := kF.mem_toFinset.mp hρ
      calc (2/25 : ℝ) = 24/25 - 22/25 := by norm_num
        _ ≤ ‖w‖ - ‖ρ‖ := by
            have := hρ'.1
            rw [hw]
            linarith
        _ ≤ ‖w - ρ‖ := norm_sub_norm_le w ρ
    have Nr : ((2/25 : ℝ)) ^ K ≤ ‖∏ ρ ∈ kF.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ‖ := by
      rw [norm_prod, hK, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod (fun ρ _ => by positivity) (fun ρ hρ => ?_)
      rw [norm_pow]
      exact pow_le_pow_left₀ (by norm_num) (hdist ρ hρ) _
    unfold Cf
    rw [dif_pos kF, dif_neg YN]
    rw [norm_div]
    have RK : (0:ℝ) < ‖∏ ρ ∈ kF.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ‖ :=
      lt_of_lt_of_le (by positivity) Nr
    rw [div_le_iff₀ RK]
    calc ‖f w‖ ≤ B := hfB w (le_of_eq hw)
      _ = B * (25/2 : ℝ) ^ K * (2/25 : ℝ) ^ K := by
          rw [mul_assoc, ← mul_pow]
          norm_num
      _ ≤ B * (25/2 : ℝ) ^ K * ‖∏ ρ ∈ kF.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ‖ := by
          have hB0 : (0:ℝ) ≤ B * (25/2 : ℝ) ^ K := by positivity
          exact mul_le_mul_of_nonneg_left Nr hB0
  have hball : ∀ w : ℂ, ‖w‖ ≤ 24/25 → ‖Cf (22/25) f w‖ ≤ B * (25/2 : ℝ) ^ K := by
    intro w hw
    have aaw : AnalyticOn ℂ (Cf (22/25) f) (Metric.closedBall 0 (24/25)) :=
      ((sW (by norm_num : (22/25:ℝ) < 39/40) (by norm_num) hfa hf0').mono
        (Metric.closedBall_subset_closedBall (by norm_num))).analyticOn
    refine AnalyticOn.jO le_rfl aaw (fun v hv => ?_)
      (by rwa [Metric.mem_closedBall, Complex.dist_eq, sub_zero])
    refine hsphere v ?_
    rw [mem_sphere_iff_norm, sub_zero] at hv
    exact hv
  have aax : (1:ℝ) ≤ ‖Cf (22/25) f 0‖ := by
    have YO : (0:ℂ) ∉ bC (22/25) f := fun h => hf0' h.2
    have kF := aP (by norm_num : (22/25 : ℝ) < 1) hfin
    unfold Cf
    rw [dif_pos kF, dif_neg YO, norm_div, hf0, norm_one]
    rw [le_div_iff₀]
    · rw [one_mul, norm_prod]
      refine Finset.prod_le_one (fun ρ _ => by positivity) (fun ρ hρ => ?_)
      have hρ' := kF.mem_toFinset.mp hρ
      rw [norm_pow]
      refine pow_le_one₀ (norm_nonneg _) ?_
      rw [zero_sub, norm_neg]
      linarith [hρ'.1]
    · rw [norm_prod]
      refine Finset.prod_pos (fun ρ hρ => ?_)
      have hρ' := kF.mem_toFinset.mp hρ
      have Mt : ρ ≠ 0 := by
        rintro rfl
        exact hf0' hρ'.2
      rw [norm_pow, zero_sub, norm_neg]
      exact pow_pos (norm_pos_iff.mpr Mt) _
  obtain ⟨J, hJa, hJ0, hJd, aay⟩ := yP
    (by norm_num : (0:ℝ) < 17/20) (by norm_num : (17/20:ℝ) < 22/25)
    ((sW (by norm_num : (22/25:ℝ) < 9/10) (by norm_num) hfa hf0').mono
      (Metric.closedBall_subset_closedBall (by norm_num)))
    (fun v hv => Jx hfa hf0' (by norm_num) hfin
      (by rwa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] at hv))
  set M' : ℝ := (1 + Real.log (25/2) / Real.log ((24/25) / (22/25))) * Real.log B with hM'
  have WU : (0:ℝ) < Real.log ((24/25) / (22/25)) := Real.log_pos (by norm_num)
  have WV : 0 < M' := by
    rw [hM']
    have : (0:ℝ) < 1 + Real.log (25/2) / Real.log ((24/25) / (22/25)) := by positivity
    positivity
  have hre : ∀ v ∈ Metric.closedBall (0:ℂ) (17/20), (J v).re ≤ M' := by
    intro v hv
    rw [← (aay v (Metric.closedBall_subset_ball (by norm_num) hv))]
    have hv' : ‖v‖ ≤ 24/25 := by
      rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero] at hv
      linarith
    have h1 : Real.log ‖Cf (22/25) f v‖ ≤ Real.log (B * (25/2 : ℝ) ^ K) := by
      rcases eq_or_ne (Cf (22/25) f v) 0 with h | h
      · rw [h, norm_zero, Real.log_zero]
        refine Real.log_nonneg ?_
        calc (1:ℝ) = 1 * 1 := by ring
          _ ≤ B * (25/2 : ℝ) ^ K := by
              refine mul_le_mul (by linarith) (one_le_pow₀ (by norm_num)) (by norm_num)
                (by linarith)
      · exact Real.log_le_log (norm_pos_iff.mpr h) (hball v hv')
    have h2 : (0:ℝ) ≤ Real.log ‖Cf (22/25) f 0‖ := Real.log_nonneg aax
    have h3 : Real.log (B * (25/2 : ℝ) ^ K) = Real.log B + K * Real.log (25/2) := by
      rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
    have h4 : (K : ℝ) * Real.log (25/2) ≤ (Real.log B / Real.log ((24/25)/(22/25))) * Real.log (25/2) := by
      have YP : (0:ℝ) ≤ Real.log (25/2) := Real.log_nonneg (by norm_num)
      have aaz : (K:ℝ) ≤ Real.log B / Real.log ((24/25)/(22/25)) := by
        rw [div_eq_inv_mul, ← one_div]
        exact hcount
      exact mul_le_mul_of_nonneg_right aaz YP
    have h5 : Real.log ‖Cf (22/25) f v‖ - Real.log ‖Cf (22/25) f 0‖
        ≤ Real.log B + (K:ℝ) * Real.log (25/2) := by
      rw [← h3]
      linarith
    rw [hM']
    calc Real.log ‖Cf (22/25) f v‖ - Real.log ‖Cf (22/25) f 0‖
        ≤ Real.log B + (K:ℝ) * Real.log (25/2) := h5
      _ ≤ Real.log B + (Real.log B / Real.log ((24/25)/(22/25))) * Real.log (25/2) := by linarith
      _ = (1 + Real.log (25/2) / Real.log ((24/25) / (22/25))) * Real.log B := by
          field_simp
  have hbc := wZ WV (by norm_num : (0:ℝ) < 83/100)
    (by norm_num : (83/100:ℝ) < 17/20)
    ((hJa.mono (Metric.ball_subset_ball (by norm_num))).analyticOn) hJ0
    (fun v hv => hre v (Metric.ball_subset_closedBall hv))
    (by rwa [Metric.mem_closedBall, Complex.dist_eq, sub_zero])
  have hzmem : z ∈ Metric.closedBall (0:ℂ) (17/20) := by
    rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
    linarith
  have Vq : deriv J z = logDeriv (Cf (22/25) f) z := by
    rw [hJd z (by
      rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
      linarith), logDeriv]
    rfl
  rw [← Vq]
  refine hbc.trans ?_
  have YQ : M' ≤ 31 * Real.log B := by
    rw [hM']
    have h8 : Real.log (25/2) ≤ 30 * Real.log ((24/25) / (22/25)) := by
      have aaA : (25/2:ℝ) ≤ ((24/25)/(22/25)) ^ (30:ℕ) := by norm_num
      calc Real.log (25/2) ≤ Real.log (((24/25)/(22/25)) ^ (30:ℕ)) :=
            Real.log_le_log (by norm_num) aaA
        _ = 30 * Real.log ((24/25)/(22/25)) := by rw [Real.log_pow]; push_cast; ring
    have hcoef : 1 + Real.log (25/2) / Real.log ((24/25) / (22/25)) ≤ 31 := by
      have hd : Real.log (25/2) / Real.log ((24/25)/(22/25)) ≤ 30 :=
        (div_le_iff₀ WU).mpr (by linarith)
      linarith
    exact mul_le_mul_of_nonneg_right hcoef DN.le
  calc 16 * M' * (17/20:ℝ) ^ 2 / ((17/20:ℝ) - 83/100) ^ 3 = 1445000 * M' := by
        field_simp
        ring
    _ ≤ 1445000 * (31 * Real.log B) := by
        exact mul_le_mul_of_nonneg_left YQ (by norm_num)
    _ = 44795000 * Real.log B := by ring
theorem oX {f : ℂ → ℂ} {B : ℝ}
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0 : f 0 = 1)
    (hfin : (bC 1 f).Finite) (OO : 2 ≤ B)
    (hfB : ∀ w : ℂ, ‖w‖ ≤ 24/25 → ‖f w‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ 83/100) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ ρ ∈ (aP (by norm_num : (22/25:ℝ) < 1) hfin).toFinset,
        (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤ 44795000 * Real.log B := by
  have hf0' : f 0 ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hsplit := KS hfa hf0' (by norm_num : (22/25:ℝ) < 1) hfin
    (lt_of_le_of_lt hz (by norm_num)) hfz
  rw [hsplit]
  rw [add_sub_cancel_left]
  exact BU hfa hf0 hfin OO hfB hz
lemma Et {f : ℂ → ℂ}
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0 : f 0 ≠ 0) :
    (bC 1 f).Finite := by
  set U := Metric.closedBall (0 : ℂ) 1 with hU
  have h0U : (0 : ℂ) ∈ U := by
    rw [hU, Metric.mem_closedBall, dist_self]
    norm_num
  have Fk : {z : ℂ | f z ≠ 0} ∈ Filter.codiscreteWithin U := by
    rcases hfa.eqOn_zero_or_eventually_ne_zero_of_preconnected
        (by rw [hU]; exact Metric.isPreconnected_closedBall) with h | h
    · exact absurd (h h0U) hf0
    · exact h
  rw [codiscreteWithin_iff_locallyFiniteComplementWithin] at Fk
  have hsub1 : Metric.closedBall (0 : ℂ) 1 ⊆ U := subset_rfl
  choose t ht YS using fun z (hz : z ∈ Metric.closedBall (0:ℂ) 1) => Fk z (hsub1 hz)
  obtain ⟨s, hs⟩ := (isCompact_closedBall (0:ℂ) 1).elim_nhds_subcover'
    (fun z hz => t z hz) (fun z hz => ht z hz)
  refine Set.Finite.subset (Set.Finite.biUnion s.finite_toSet
    (fun z _ => YS z.1 z.2)) ?_
  intro ρ hρ
  have hρball : ρ ∈ Metric.closedBall (0:ℂ) 1 := by
    rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
    exact hρ.1
  obtain ⟨z, hz, Fo⟩ := Set.mem_iUnion₂.mp (hs hρball)
  refine Set.mem_biUnion hz ?_
  refine ⟨Fo, hsub1 hρball, ?_⟩
  simp only [Set.mem_setOf_eq, not_not]
  exact hρ.2
theorem oY {f : ℂ → ℂ} {s₀ : ℂ} {R B : ℝ}
    (hR : 0 < R) (hfa : AnalyticOnNhd ℂ f (Metric.closedBall s₀ R)) (hf0 : f s₀ ≠ 0)
    (OO : 2 ≤ B) (hfB : ∀ w ∈ Metric.closedBall s₀ (24/25 * R), ‖f w‖ ≤ B * ‖f s₀‖) :
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ Metric.closedBall s₀ (22/25 * R) | f ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ 1 / Real.log ((24/25) / (22/25)) * Real.log B) ∧
      ∀ s ∈ Metric.closedBall s₀ (83/100 * R), f s ≠ 0 →
        ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖
          ≤ 44795000 / R * Real.log B := by
  have ZO : (R : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hR
  set φ : ℂ → ℂ := fun w => s₀ + (R : ℂ) * w with hφ
  have Jy : ∀ {w : ℂ} {r : ℝ}, ‖w‖ ≤ r → φ w ∈ Metric.closedBall s₀ (r * R) := by
    intro w r hw
    rw [Metric.mem_closedBall, Complex.dist_eq, hφ]
    simp only [add_sub_cancel_left]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    calc R * ‖w‖ ≤ R * r := mul_le_mul_of_nonneg_left hw hR.le
      _ = r * R := mul_comm _ _
  set c : ℂ := (f s₀)⁻¹ with hc
  have hcne : c ≠ 0 := inv_ne_zero hf0
  set g : ℂ → ℂ := fun w => c * f (φ w) with hg
  have hφa : ∀ w : ℂ, AnalyticAt ℂ φ w := fun w => by
    rw [hφ]
    exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have WX : ∀ w : ℂ, deriv φ w = (R : ℂ) := by
    intro w
    rw [hφ]
    simp
  have IQ : Function.Injective φ := by
    intro a b hab
    rw [hφ] at hab
    simp only [add_right_inj] at hab
    exact mul_left_cancel₀ ZO hab
  have hga : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) := by
    intro w hw
    have hwn : ‖w‖ ≤ 1 := by rwa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] at hw
    have hmem : φ w ∈ Metric.closedBall s₀ R := by
      have := Jy (r := 1) hwn
      simpa using this
    exact analyticAt_const.mul ((hfa (φ w) hmem).comp (hφa w))
  have hg0 : g 0 = 1 := by
    rw [hg, hc]
    simp only [hφ, mul_zero, add_zero]
    exact inv_mul_cancel₀ hf0
  have aaB : g 0 ≠ 0 := by rw [hg0]; exact one_ne_zero
  have hfin : (bC 1 g).Finite := Et hga aaB
  have hgB : ∀ w : ℂ, ‖w‖ ≤ 24/25 → ‖g w‖ ≤ B := by
    intro w hw
    rw [hg]
    simp only
    rw [norm_mul, hc, norm_inv]
    rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hf0)]
    calc ‖f (φ w)‖ ≤ B * ‖f s₀‖ := hfB (φ w) (Jy hw)
      _ = ‖f s₀‖ * B := mul_comm _ _
  have Nu : ∀ ρg : ℂ, g ρg = 0 ↔ f (φ ρg) = 0 := by
    intro ρg
    rw [hg]
    simp only
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hcne
      · exact h
    · intro h
      rw [h, mul_zero]
  set Zg := (aP (by norm_num : (22/25 : ℝ) < 1) hfin).toFinset with hZg
  have JE : ∀ ρg : ℂ, ρg ∈ Zg ↔ (‖ρg‖ ≤ 22/25 ∧ f (φ ρg) = 0) := by
    intro ρg
    rw [hZg, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (Nu ρg).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (Nu ρg).mpr h2⟩
  have hord : ∀ ρg : ℂ, ‖ρg‖ ≤ 1 → analyticOrderNatAt g ρg = analyticOrderNatAt f (φ ρg) := by
    intro ρg Gm
    have hcomp : analyticOrderAt (f ∘ φ) ρg = analyticOrderAt f (φ ρg) :=
      analyticOrderAt_comp_of_deriv_ne_zero (hφa ρg) (by rw [WX]; exact ZO)
    have hsmul : analyticOrderAt g ρg = analyticOrderAt (f ∘ φ) ρg := by
      have heq : g = (fun _ : ℂ => c) • (f ∘ φ) := by
        funext w
        simp [hg, smul_eq_mul]
      rw [heq, analyticOrderAt_smul analyticAt_const
        (((hfa (φ ρg) (by simpa using Jy (r := 1) Gm)).comp (hφa ρg)))]
      rw [(analyticAt_const (v := c)).analyticOrderAt_eq_zero.mpr hcne, zero_add]
    rw [analyticOrderNatAt, analyticOrderNatAt, hsmul, hcomp]
  refine ⟨Zg.image φ, ?_, ?_, ?_⟩
  · ext ρ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Set.mem_setOf_eq]
    constructor
    · rintro ⟨ρg, Gm, rfl⟩
      obtain ⟨h1, h2⟩ := (JE ρg).mp Gm
      exact ⟨by simpa using Jy h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(ρ - s₀) / (R : ℂ), ?_, ?_⟩
      · rw [JE]
        constructor
        · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
            div_le_iff₀ hR]
          rw [Metric.mem_closedBall, Complex.dist_eq] at h1
          linarith [h1]
        · rw [show φ ((ρ - s₀) / (R:ℂ)) = ρ by rw [hφ]; field_simp; ring]
          exact h2
      · rw [hφ]; field_simp; ring
  · have hcount := zS (by norm_num) (by norm_num)
      (by norm_num : (22/25:ℝ) < 24/25) (by norm_num) hga hg0 hfin hgB
    rw [Finset.sum_image (fun a _ b _ hab => IQ hab)]
    have hcongr : ∀ ρg ∈ Zg, (analyticOrderNatAt f (φ ρg) : ℝ) = (analyticOrderNatAt g ρg : ℝ) := by
      intro ρg Gm
      rw [hord ρg (le_trans ((JE ρg).mp Gm).1 (by norm_num))]
    rw [Finset.sum_congr rfl hcongr]
    exact_mod_cast hcount
  · intro s hs hfs
    set w : ℂ := (s - s₀) / (R : ℂ) with hw
    have hφw : φ w = s := by rw [hφ, hw]; field_simp; ring
    have hwn : ‖w‖ ≤ 83/100 := by
      rw [hw, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_le_iff₀ hR]
      rw [Metric.mem_closedBall, Complex.dist_eq] at hs
      linarith [hs]
    have hgw : g w ≠ 0 := by
      rw [hg]
      simp only
      rw [hφw]
      exact mul_ne_zero hcne hfs
    have hunit := oX hga hg0 hfin OO hgB hwn hgw
    have JG : s ∈ Metric.closedBall s₀ R :=
      Metric.closedBall_subset_closedBall (by nlinarith) hs
    have hld : logDeriv g w = (R : ℂ) * logDeriv f s := by
      have hstep : logDeriv g w = logDeriv (f ∘ φ) w := by
        rw [hg]
        exact logDeriv_const_mul w c hcne
      have hdf : DifferentiableAt ℂ f (φ w) := by
        rw [hφw]
        exact (hfa s JG).differentiableAt
      rw [hstep, logDeriv_comp hdf (hφa w).differentiableAt, hφw, WX, mul_comm]
    have hsum : ∑ ρ ∈ Zg.image φ, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)
        = (R : ℂ)⁻¹ * ∑ ρg ∈ Zg, (analyticOrderNatAt g ρg : ℂ) / (w - ρg) := by
      rw [Finset.sum_image (fun a _ b _ hab => IQ hab), Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρg Gm => ?_
      have h34 : ‖ρg‖ ≤ 22/25 := ((JE ρg).mp Gm).1
      rw [hord ρg (by linarith)]
      have hsub : s - φ ρg = (R : ℂ) * (w - ρg) := by
        rw [← hφw, hφ]
        ring
      rw [hsub]
      rw [div_mul_eq_div_div_swap]
      field_simp
    rw [hsum]
    have aaC : logDeriv f s = (R:ℂ)⁻¹ * logDeriv g w := by
      rw [hld]
      field_simp
    rw [aaC, ← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR]
    rw [div_eq_inv_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hunit (inv_nonneg.mpr hR.le)
end Tv
theorem oZ : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 6 ≤ |t| →
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ Metric.closedBall (2 + t * I) (22/25 * (91/50)) | riemannZeta ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ C * Real.log (|t| + 3)) ∧
      ∀ s ∈ Metric.closedBall (2 + t * I) (3/2), riemannZeta s ≠ 0 →
        ‖logDeriv riemannZeta s - ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖
          ≤ C * Real.log (|t| + 3) := by
  obtain ⟨A, C₀, hC₀, hgrow⟩ := Zeta23.kB.Bv
  set A' : ℝ := max A 0 with hA'
  have Da : 0 ≤ A' := le_max_right _ _
  have hCpos : (0:ℝ) < (44795000 * 50 / 91) * (Real.log 3 + Real.log (C₀ + 2) + A' + 1) := by
    have h1 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h2 : (0:ℝ) ≤ Real.log (C₀ + 2) := Real.log_nonneg (by linarith)
    positivity
  refine ⟨(44795000 * 50 / 91) * (Real.log 3 + Real.log (C₀ + 2) + A' + 1), hCpos,
    fun t ht => ?_⟩
  set s₀ : ℂ := 2 + t * I with hs₀
  have Vr : s₀.re = 2 := by simp [hs₀]
  have abp : s₀.im = t := by simp [hs₀]
  have Vt : riemannZeta s₀ ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [Vr]; norm_num)
  have hlow : (1/3 : ℝ) ≤ ‖riemannZeta s₀‖ := Zeta23.kB.oM t
  have hone : (1 : ℂ) ∉ Metric.closedBall s₀ (91/50) := by
    intro h
    rw [Metric.mem_closedBall, Complex.dist_eq] at h
    have him : ((1 : ℂ) - s₀).im = -t := by simp [hs₀]
    have : |t| ≤ ‖(1 : ℂ) - s₀‖ := by
      calc |t| = |((1:ℂ) - s₀).im| := by rw [him, abs_neg]
        _ ≤ ‖(1:ℂ) - s₀‖ := Complex.abs_im_le_norm _
    linarith
  have hfa : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall s₀ (91/50)) :=
    Zeta23.kB.tB hone
  set B : ℝ := 3 * (C₀ * (|t| + 2) ^ A' + 2) with hB
  have ht2 : (1:ℝ) ≤ |t| + 2 := by linarith
  have Qe : (1:ℝ) ≤ (|t| + 2) ^ A' := Real.one_le_rpow ht2 Da
  have OO : 2 ≤ B := by
    rw [hB]
    nlinarith [mul_nonneg hC₀.le (le_trans zero_le_one Qe)]
  have hfB : ∀ w ∈ Metric.closedBall s₀ (24/25 * (91/50)), ‖riemannZeta w‖ ≤ B * ‖riemannZeta s₀‖ := by
    intro w hw
    rw [Metric.mem_closedBall, Complex.dist_eq] at hw
    have Dx : |w.re - 2| ≤ 24/25 * (91/50) := by
      have := Complex.abs_re_le_norm (w - s₀)
      have hre : (w - s₀).re = w.re - 2 := by simp [hs₀]
      rw [hre] at this
      linarith
    have Gp : |w.im - t| ≤ 24/25 * (91/50) := by
      have := Complex.abs_im_le_norm (w - s₀)
      have him : (w - s₀).im = w.im - t := by simp [hs₀]
      rw [him] at this
      linarith
    have Uv : 1 ≤ |w.im| := by
      have h3 : |t| - |w.im| ≤ |t - w.im| := abs_sub_abs_le_abs_sub t w.im
      have h4 : |t - w.im| = |w.im - t| := abs_sub_comm t w.im
      linarith [Gp]
    have YV : |w.im| ≤ |t| + 2 := by
      have := abs_sub_abs_le_abs_sub w.im t
      have h2 : |w.im| - |t| ≤ |w.im - t| := this
      linarith [Gp]
    have hbound : ‖riemannZeta w‖ ≤ C₀ * (|t| + 2) ^ A' + 2 := by
      rcases le_or_gt w.re 2 with Dm | Dm
      · have h14 : (1/4 : ℝ) ≤ w.re := by
          rw [abs_le] at Dx
          linarith
        have := hgrow w h14 Dm Uv
        calc ‖riemannZeta w‖ ≤ C₀ * |w.im| ^ A := this
          _ ≤ C₀ * (|t| + 2) ^ A' := by
              refine mul_le_mul_of_nonneg_left ?_ hC₀.le
              calc |w.im| ^ A ≤ |w.im| ^ A' :=
                    Real.rpow_le_rpow_of_exponent_le Uv (le_max_left _ _)
                _ ≤ (|t| + 2) ^ A' := Real.rpow_le_rpow (by linarith) YV Da
          _ ≤ C₀ * (|t| + 2) ^ A' + 2 := by linarith
      · have := Zeta23.kB.nW (s := w) (by linarith)
        have hπ : (Real.pi : ℝ) ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_gt_three]
        calc ‖riemannZeta w‖ ≤ Real.pi ^ 2 / 6 := this
          _ ≤ 2 := hπ
          _ ≤ C₀ * (|t| + 2) ^ A' + 2 := by
              nlinarith [mul_nonneg hC₀.le (le_trans zero_le_one Qe)]
    calc ‖riemannZeta w‖ ≤ C₀ * (|t| + 2) ^ A' + 2 := hbound
      _ = (B * (1/3)) := by rw [hB]; ring
      _ ≤ B * ‖riemannZeta s₀‖ := by
          refine mul_le_mul_of_nonneg_left hlow (by rw [hB]; positivity)
  obtain ⟨Z, YW, Vv, Tw⟩ := oY (f := riemannZeta)
    (by norm_num : (0:ℝ) < 91/50) hfa Vt OO hfB
  have WZ : (2:ℝ) ≤ Real.log (|t| + 3) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h1 := Real.exp_one_lt_d9
    calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      _ ≤ 2.7182818286 * 2.7182818286 := by nlinarith [Real.exp_pos 1]
      _ ≤ 9 := by norm_num
      _ ≤ |t| + 3 := by linarith
  have DN : Real.log B ≤ (Real.log 3 + Real.log (C₀ + 2) + A') * Real.log (|t| + 3) := by
    have h1 : B ≤ 3 * ((C₀ + 2) * (|t| + 2) ^ A') := by
      rw [hB]
      nlinarith [Qe, hC₀]
    have h2 : Real.log B ≤ Real.log (3 * ((C₀ + 2) * (|t| + 2) ^ A')) :=
      Real.log_le_log (by rw [hB]; positivity) h1
    rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),
      Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),
      Real.log_mul (by positivity : (C₀ + 2 : ℝ) ≠ 0) (by positivity),
      Real.log_rpow (by linarith : (0:ℝ) < |t| + 2)] at h2
    have h3 : Real.log (|t| + 2) ≤ Real.log (|t| + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    have h4 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h5 : (0:ℝ) ≤ Real.log (C₀ + 2) := Real.log_nonneg (by linarith)
    have hBeq : Real.log B = Real.log 3 + Real.log (C₀ * (|t| + 2) ^ A' + 2) := by
      rw [hB, Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity)]
    rw [hBeq]
    nlinarith [mul_nonneg Da (by linarith : (0:ℝ) ≤ Real.log (|t|+3) - Real.log (|t|+2)),
      mul_nonneg h4 (by linarith : (0:ℝ) ≤ Real.log (|t|+3) - 1),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ Real.log (|t|+3) - 1), WZ]
  have h4 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h5 : (0:ℝ) ≤ Real.log (C₀ + 2) := Real.log_nonneg (by linarith)
  refine ⟨Z, ?_, ?_, ?_⟩
  · rw [YW]
  · refine Vv.trans ?_
    have hratio : ((24/25 : ℝ))/(22/25) = 12/11 := by norm_num
    have aaD : (1:ℝ)/12 ≤ Real.log ((24/25)/(22/25)) := by
      rw [hratio]
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 11/12 by norm_num)
      rw [show (11/12:ℝ) = (12/11)⁻¹ by norm_num, Real.log_inv] at h
      linarith
    have KR : (0:ℝ) < Real.log ((24/25)/(22/25)) := by
      rw [hratio]
      exact Real.log_pos (by norm_num)
    have Vw : (0:ℝ) ≤ Real.log B := Real.log_nonneg (by linarith)
    calc 1 / Real.log ((24/25)/(22/25)) * Real.log B ≤ 12 * Real.log B := by
          refine mul_le_mul_of_nonneg_right ?_ Vw
          rw [div_le_iff₀ KR]
          linarith
      _ ≤ 12 * ((Real.log 3 + Real.log (C₀ + 2) + A') * Real.log (|t| + 3)) :=
          mul_le_mul_of_nonneg_left DN (by norm_num)
      _ ≤ 44795000 * 50 / 91 * (Real.log 3 + Real.log (C₀ + 2) + A' + 1) * Real.log (|t| + 3) := by
          nlinarith [WZ, Da]
  · intro s hs aaE
    have hs' : s ∈ Metric.closedBall s₀ (83/100 * (91/50)) :=
      Metric.closedBall_subset_closedBall (by norm_num) hs
    refine (Tw s hs' aaE).trans ?_
    calc 44795000 / (91/50) * Real.log B
        ≤ 44795000 / (91/50) * ((Real.log 3 + Real.log (C₀ + 2) + A') * Real.log (|t| + 3)) :=
          mul_le_mul_of_nonneg_left DN (by norm_num)
      _ ≤ (44795000 * 50 / 91) * (Real.log 3 + Real.log (C₀ + 2) + A' + 1) * Real.log (|t| + 3) := by
          nlinarith [WZ, Da]
end cw
end Zeta23
end
end

-- Zeta23.cw.XV
section
noncomputable section
namespace Zeta23
namespace cw
open Complex Set Filter Finset
lemma Gq (S : Finset ℝ) (a : ℝ) :
    ∃ R : ℝ, a ≤ R ∧ R ≤ a + 1 ∧ ∀ y ∈ S, 1 / (2 * ((S.card : ℝ) + 1)) ≤ |R - y| := by
  classical
  set n : ℕ := S.card with hn
  set δ : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδn : 2 * ((n : ℝ) + 1) * δ = 1 := by rw [hδ]; field_simp
  set cand : ℕ → ℝ := fun k => a + (2 * (k : ℝ) + 1) * δ with Qg
  by_contra hcon
  push Not at hcon
  have hbad : ∀ k ∈ Finset.range (n + 1), ∃ y ∈ S, |cand k - y| < δ := by
    intro k hk
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 : a ≤ cand k := by simp only [Qg]; nlinarith
    have h2 : cand k ≤ a + 1 := by
      simp only [Qg]
      have : (2 * (k : ℝ) + 1) * δ ≤ (2 * (n : ℝ) + 1) * δ := by gcongr
      nlinarith
    obtain ⟨y, hy, hlt⟩ := hcon (cand k) h1 h2
    exact ⟨y, hy, hlt⟩
  choose! f hf using hbad
  have hmaps : Set.MapsTo f (Finset.range (n + 1)) S := fun k hk => (hf k hk).1
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simp [hn]) hmaps
  have h1 := (hf x hx).2
  have h2 := (hf y hy).2
  rw [hfxy] at h1
  have hdist : |cand x - cand y| = 2 * |(x : ℝ) - y| * δ := by
    simp only [Qg]
    rw [show a + (2 * (x:ℝ) + 1) * δ - (a + (2 * (y:ℝ) + 1) * δ) = (2 * δ) * ((x:ℝ) - y) by ring,
      abs_mul, abs_of_pos (by positivity)]
    ring
  have hxy1 : (1 : ℝ) ≤ |(x : ℝ) - y| := by
    rcases Nat.lt_or_gt_of_ne hxy with h | h
    · have : (x : ℝ) + 1 ≤ y := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]; linarith
    · have : (y : ℝ) + 1 ≤ x := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
  have htri : |cand x - cand y| < 2 * δ := by
    calc |cand x - cand y| = |(cand x - f y) - (cand y - f y)| := by ring_nf
      _ ≤ |cand x - f y| + |cand y - f y| := abs_sub _ _
      _ < δ + δ := add_lt_add h1 h2
      _ = 2 * δ := by ring
  rw [hdist] at htri
  nlinarith
lemma xW (s ρ : ℂ) : |s.im - ρ.im| ≤ ‖s - ρ‖ := by
  rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
lemma mD {t r : ℝ} (hr : r < 2) {ρ : ℂ}
    (hρ : ρ ∈ Metric.closedBall (2 + t * I) r) (hz : riemannZeta ρ = 0) : aO ρ := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hρ
  have hre : |ρ.re - 2| ≤ r := by
    have := Complex.abs_re_le_norm (ρ - (2 + t * I))
    simp at this; linarith
  refine ⟨hz, by rw [abs_le] at hre; linarith, ?_⟩
  by_contra h
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
lemma vP {t r : ℝ} {ρ : ℂ} (hρ : ρ ∈ Metric.closedBall (2 + t * I) r) :
    |ρ.im - t| ≤ r := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hρ
  have := Complex.abs_im_le_norm (ρ - (2 + t * I))
  simp at this; linarith
lemma pC {A₀ : ℝ}
    (Fd : Tail.jo (fun ρ : aE.carrier => (ρ : ℂ).im)
      (fun ρ : aE.carrier => aE.mult ρ) A₀)
    {a : ℤ} (F : Finset aE.carrier)
    (hF : ∀ ρ ∈ F, (a : ℝ) < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ (a : ℝ) + 6) :
    ∑ ρ ∈ F, (aE.mult ρ : ℝ) ≤ 6 * (A₀ * Real.log (|(a : ℝ)| + 9)) := by
  classical
  have hA₀ := Fd.zO.le
  set key : aE.carrier → ℕ := fun ρ => (⌈(ρ : ℂ).im⌉ - a - 1).toNat with hkey
  have Ly : ∀ ρ ∈ F, ((a : ℝ) + key ρ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ (a : ℝ) + key ρ + 1)
      ∧ key ρ < 6 := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := hF ρ hρ
    have hc1 := Int.le_ceil (ρ : ℂ).im
    have hc2 := Int.ceil_lt_add_one (ρ : ℂ).im
    have hlo : a + 1 ≤ ⌈(ρ : ℂ).im⌉ := by
      have : (a : ℝ) < ⌈(ρ : ℂ).im⌉ := lt_of_lt_of_le h1 hc1
      have : a < ⌈(ρ : ℂ).im⌉ := by exact_mod_cast this
      omega
    have hhi : ⌈(ρ : ℂ).im⌉ ≤ a + 6 := by
      have : (⌈(ρ : ℂ).im⌉ : ℝ) < (a : ℝ) + 6 + 1 := by linarith
      have : ⌈(ρ : ℂ).im⌉ < a + 6 + 1 := by exact_mod_cast this
      omega
    have hk : ((key ρ : ℕ) : ℤ) = ⌈(ρ : ℂ).im⌉ - a - 1 := by
      simp only [hkey]; rw [Int.toNat_of_nonneg (by omega)]
    have hkR : ((key ρ : ℕ) : ℝ) = (⌈(ρ : ℂ).im⌉ : ℝ) - a - 1 := by exact_mod_cast hk
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    have : ((key ρ : ℕ) : ℤ) < 6 := by omega
    exact_mod_cast this
  have h := Tail.wT F (fun ρ => aE.mult ρ) key 6
    (C := A₀ * Real.log (|(a : ℝ)| + 9)) (fun ρ hρ => (Ly ρ hρ).2) (fun k hk => by
      have hw := Fd.window ((a : ℝ) + k) (F.filter fun ρ => key ρ = k) (fun ρ hρ => by
        simp only [Finset.mem_filter] at hρ
        have := (Ly ρ hρ.1).1
        rw [hρ.2] at this; exact this)
      refine hw.trans (mul_le_mul_of_nonneg_left ?_ hA₀)
      apply Real.log_le_log (by positivity)
      have : |(a : ℝ) + k| ≤ |(a : ℝ)| + k := by
        calc |(a:ℝ) + k| ≤ |(a:ℝ)| + |(k:ℝ)| := abs_add_le _ _
          _ = |(a:ℝ)| + k := by rw [Nat.abs_cast]
      have hk6 : (k : ℝ) < 6 := by exact_mod_cast hk
      linarith)
  simpa using h
lemma vQ (F : Finset aE.carrier) :
    (F.card : ℝ) ≤ ∑ ρ ∈ F, (aE.mult ρ : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun ρ _ => ?_
  exact_mod_cast aE.one_le_mult ρ ρ.2
theorem JH : ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 7 ≤ j →
    ∃ R : ℝ, (j : ℝ) ≤ R ∧ R ≤ (j : ℝ) + 1 ∧
    ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 →
      riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤ C * (Real.log ((j : ℝ) + 3)) ^ 2 := by
  classical
  obtain ⟨C, hC, hpf⟩ := oZ
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.kB.rE
  have Fd := Tail.jo.Ao aE hA₀ hloc
  refine ⟨2 * C * (48 * A₀ + 3), by positivity, fun j hj => ?_⟩
  have hj7 : (7 : ℝ) ≤ j := by exact_mod_cast hj
  set Lg : ℝ := Real.log ((j : ℝ) + 3) with hLg
  have Qj : 1 ≤ Lg := by
    rw [hLg, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have zX : Real.log 2 ≤ Lg := by
    rw [hLg]; exact Real.log_le_log (by norm_num) (by linarith)
  set Wp : Set ℂ := aE.window ((j : ℝ) - 3) ((j : ℝ) + 3) with hWp
  set Wm : Set ℂ := aE.window (-(j : ℝ) - 4) (-(j : ℝ) + 2) with hWm
  have Xb : ((fun ρ : aE.carrier => (ρ : ℂ)) ⁻¹' Wp).Finite :=
    (aE.dS _ _).preimage Subtype.val_injective.injOn
  have Xc : ((fun ρ : aE.carrier => (ρ : ℂ)) ⁻¹' Wm).Finite :=
    (aE.dS _ _).preimage Subtype.val_injective.injOn
  set Fp : Finset aE.carrier := Xb.toFinset with hFp
  set Fm : Finset aE.carrier := Xc.toFinset with hFm
  have OP : ∀ ρ : aE.carrier, ρ ∈ Fp ↔ (ρ : ℂ) ∈ Wp := fun ρ => by
    rw [hFp, Set.Finite.mem_toFinset]; rfl
  have OQ : ∀ ρ : aE.carrier, ρ ∈ Fm ↔ (ρ : ℂ) ∈ Wm := fun ρ => by
    rw [hFm, Set.Finite.mem_toFinset]; rfl
  set S : Finset ℝ := Fp.image (fun ρ : aE.carrier => (ρ : ℂ).im)
    ∪ Fm.image (fun ρ : aE.carrier => -(ρ : ℂ).im) with hS
  have abq : ∑ ρ ∈ Fp, (aE.mult ρ : ℝ) ≤ 6 * (A₀ * (2 * Lg)) := by
    have h := pC Fd (a := (j : ℤ) - 3) Fp (fun ρ hρ => by
      have := ((OP ρ).mp hρ).2; push_cast; constructor <;> linarith [this.1, this.2])
    refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ Fd.zO.le)
      (by norm_num))
    · have : |((j : ℤ) - 3 : ℤ)| = (j : ℤ) - 3 := abs_of_nonneg (by omega)
      have habs : |(((j:ℤ) - 3 : ℤ) : ℝ)| = (j : ℝ) - 3 := by
        rw [← Int.cast_abs, this]; push_cast; ring
      rw [habs]
      calc Real.log ((j:ℝ) - 3 + 9) ≤ Real.log (2 * ((j:ℝ) + 3)) :=
            Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 2 + Lg := by rw [Real.log_mul (by norm_num) (by linarith)]
        _ ≤ 2 * Lg := by linarith
  have hcountm : ∑ ρ ∈ Fm, (aE.mult ρ : ℝ) ≤ 6 * (A₀ * (2 * Lg)) := by
    have h := pC Fd (a := -(j : ℤ) - 4) Fm (fun ρ hρ => by
      have := ((OQ ρ).mp hρ).2; push_cast; constructor <;> linarith [this.1, this.2])
    refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ Fd.zO.le)
      (by norm_num))
    · have : |(-(j : ℤ) - 4 : ℤ)| = (j : ℤ) + 4 := by
        rw [abs_of_nonpos (by omega)]; ring
      have habs : |((-(j:ℤ) - 4 : ℤ) : ℝ)| = (j : ℝ) + 4 := by
        rw [← Int.cast_abs, this]; push_cast; ring
      rw [habs]
      calc Real.log ((j:ℝ) + 4 + 9) ≤ Real.log (((j:ℝ) + 3) ^ 2) := by
            apply Real.log_le_log (by linarith); nlinarith
        _ = 2 * Lg := by rw [Real.log_pow]; push_cast; ring
  have hcard : (S.card : ℝ) ≤ 24 * A₀ * Lg := by
    have h1 : S.card ≤ Fp.card + Fm.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
    have h1' : (S.card : ℝ) ≤ Fp.card + Fm.card := by exact_mod_cast h1
    linarith [vQ Fp, vQ Fm]
  obtain ⟨R, hR1, hR2, Tz⟩ := Gq S j
  set δ : ℝ := 1 / (2 * ((S.card : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have Xd : 1 / δ = 2 * ((S.card : ℝ) + 1) := by rw [hδ, one_div_one_div]
  refine ⟨R, hR1, hR2, fun s hs hσ1 hσ2 => ?_⟩
  have hR6 : (6 : ℝ) ≤ |R| := by rw [abs_of_nonneg (by linarith)]; linarith
  have acT : (6 : ℝ) ≤ |-R| := by rwa [abs_neg]
  have Uw : Real.log (|R| + 3) ≤ 2 * Lg := by
    rw [abs_of_nonneg (by linarith)]
    calc Real.log (R + 3) ≤ Real.log (2 * ((j:ℝ) + 3)) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2 + Lg := by rw [Real.log_mul (by norm_num) (by linarith)]
      _ ≤ 2 * Lg := by linarith
  have RM : s ∈ Metric.closedBall (2 + s.im * I) (3 / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : s - (2 + s.im * I) = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have Uz : ∀ ρ : ℂ, ρ ∈ Metric.closedBall (2 + s.im * I) (22/25 * (91/50)) →
      riemannZeta ρ = 0 → δ ≤ ‖s - ρ‖ := by
    intro ρ hρ hz
    have hnt := mD (by norm_num) hρ hz
    have him := vP hρ
    rw [abs_le] at him
    have KV : ρ ∈ aE.carrier := by rw [wY]; exact hnt
    refine le_trans ?_ (xW s ρ)
    rcases hs with JG | JG
    · 
      have hmem : (⟨ρ, KV⟩ : aE.carrier) ∈ Fp := by
        rw [OP]
        refine ⟨KV, ?_, ?_⟩ <;> rw [JG] at him <;> nlinarith
      have : ρ.im ∈ S := by
        rw [hS, Finset.mem_union]; left
        exact Finset.mem_image.mpr ⟨(⟨ρ, KV⟩ : aE.carrier), hmem, rfl⟩
      have := Tz _ this
      rwa [JG]
    · have hmem : (⟨ρ, KV⟩ : aE.carrier) ∈ Fm := by
        rw [OQ]
        refine ⟨KV, ?_, ?_⟩ <;> rw [JG] at him <;> nlinarith
      have : -ρ.im ∈ S := by
        rw [hS, Finset.mem_union]; right
        exact Finset.mem_image.mpr ⟨(⟨ρ, KV⟩ : aE.carrier), hmem, rfl⟩
      have := Tz _ this
      rw [JG, show |(-R) - ρ.im| = |R - (-ρ.im)| by rw [← abs_neg]; ring_nf]
      exact this
  have hζ : riemannZeta s ≠ 0 := by
    intro hz
    have h0 := Uz s (Metric.closedBall_subset_closedBall (by norm_num) RM) hz
    simp at h0; linarith
  refine ⟨hζ, ?_⟩
  have ht6 : (6 : ℝ) ≤ |s.im| := by rcases hs with h | h <;> rw [h] <;> assumption
  obtain ⟨Z, hZ, Qk, Tw⟩ := hpf s.im ht6
  have YZ := Tw s RM hζ
  have UA : Real.log (|s.im| + 3) ≤ 2 * Lg := by
    rcases hs with h | h
    · rw [h]; exact Uw
    · rw [h, abs_neg]; exact Uw
  have Mc : ∀ ρ ∈ Z, ρ ∈ Metric.closedBall (2 + s.im * I) (22/25 * (91/50)) ∧ riemannZeta ρ = 0 := by
    intro ρ hρ
    have : ρ ∈ (↑Z : Set ℂ) := hρ
    rw [hZ] at this
    exact this
  have Zb : ‖∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖
      ≤ (C * (2 * Lg)) * (1 / δ) := by
    calc ‖∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Z, ‖(analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / δ) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          obtain ⟨aaF, Fo⟩ := Mc ρ hρ
          have hd := Uz ρ aaF Fo
          have acU : 0 < ‖s - ρ‖ := lt_of_lt_of_le hδpos hd
          rw [norm_div, Complex.norm_natCast, div_eq_mul_one_div]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact one_div_le_one_div_of_le hδpos hd
      _ = (∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ)) * (1 / δ) := by rw [Finset.sum_mul]
      _ ≤ (C * (2 * Lg)) * (1 / δ) := by
          refine mul_le_mul_of_nonneg_right (Qk.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left UA hC.le
  have hmain : ‖logDeriv riemannZeta s‖ ≤ C * (2 * Lg) + (C * (2 * Lg)) * (1 / δ) := by
    have h1 : ‖logDeriv riemannZeta s‖
        ≤ ‖logDeriv riemannZeta s - ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖
          + ‖∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ := norm_le_norm_sub_add _ _
    have h2 := YZ.trans (mul_le_mul_of_nonneg_left UA hC.le)
    linarith [Zb]
  refine hmain.trans ?_
  rw [Xd]
  have hc := hcard
  have hA := Fd.zO.le
  have : C * (2 * Lg) + C * (2 * Lg) * (2 * ((S.card : ℝ) + 1))
      = 2 * C * Lg * (2 * (S.card : ℝ) + 3) := by ring
  rw [this]
  have hn : 2 * (S.card : ℝ) + 3 ≤ (48 * A₀ + 3) * Lg := by nlinarith
  calc 2 * C * Lg * (2 * (S.card : ℝ) + 3) ≤ 2 * C * Lg * ((48 * A₀ + 3) * Lg) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
    _ = 2 * C * (48 * A₀ + 3) * Real.log ((j : ℝ) + 3) ^ 2 := by rw [hLg]; ring
theorem Nv : ∃ Cg : ℝ, 0 < Cg ∧ ∃ R : ℕ → ℝ, ∀ j : ℕ,
    (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8 ∧
    ∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → 1 / 2 ≤ s.re → s.re ≤ 2 →
      riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤ Cg * (Real.log ((j : ℝ) + 10)) ^ 2 := by
  obtain ⟨C, hC, h⟩ := JH
  have hex : ∀ j : ℕ, ∃ R : ℝ, ((j + 7 : ℕ) : ℝ) ≤ R ∧ R ≤ ((j + 7 : ℕ) : ℝ) + 1 ∧
      ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 →
        riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤ C * (Real.log (((j + 7 : ℕ) : ℝ) + 3)) ^ 2 :=
    fun j => h (j + 7) (by omega)
  refine ⟨C, hC, fun j => (hex j).choose, fun j => ?_⟩
  dsimp only
  obtain ⟨hs1, hs2, hs3⟩ := (hex j).choose_spec
  have e : ((j + 7 : ℕ) : ℝ) = (j : ℝ) + 7 := by push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · calc (j : ℝ) + 7 = ((j + 7 : ℕ) : ℝ) := e.symm
      _ ≤ _ := hs1
  · exact hs2.trans (by rw [e]; linarith)
  · intro s him h1 h2
    have e3 : Real.log (((j + 7 : ℕ) : ℝ) + 3) = Real.log ((j : ℝ) + 10) := by rw [e]; ring_nf
    obtain ⟨h3, h4⟩ := hs3 s him h1 h2
    exact ⟨h3, by rwa [e3] at h4⟩
end cw
end Zeta23
end
end

-- Zeta23.Analytic.Sl
section
open Complex Set Topology Filter Asymptotics Real
noncomputable section
namespace Zeta23
namespace Analytic
theorem zD {f : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (S : Finset ℂ) (A : ℂ → ℂ)
    (hS : ∀ p ∈ S, Rectangle z w ∈ 𝓝 p)
    (Ql : iG f (Rectangle z w \ (S : Set ℂ)))
    (near : ∀ p ∈ S, (f - fun s => A p / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    bF f z w = ∑ p ∈ S, A p := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty =>
    simp only [Finset.coe_empty, sdiff_empty] at Ql
    rw [Finset.sum_empty]
    show (1 / (2 * π * I)) • aY f z w = 0
    rw [Ql.Bq subset_rfl, smul_zero]
  | @insert p S hpS ih =>
    have hp : Rectangle z w ∈ 𝓝 p := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, Rectangle z w ∈ 𝓝 q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    set P : ℂ → ℂ := fun s => A p / (s - p) with hP
    set f₁ : ℂ → ℂ := f - P with hf₁
    set f₂ : ℂ → ℂ := Function.update f₁ p (limUnder (𝓝[≠] p) f₁) with hf₂
    have Dk : ∀ s, s ≠ p → DifferentiableAt ℂ P s := by
      intro s hs
      have : s - p ≠ 0 := sub_ne_zero.mpr hs
      simp only [hP]
      fun_prop (disch := assumption)
    have Lz : iG f₁ (Rectangle z w \ ((insert p S : Finset ℂ) : Set ℂ)) := by
      refine Ql.sub ?_
      intro s hs
      apply (Dk s ?_).differentiableWithinAt
      intro h
      apply hs.2
      simp [h]
    have TB : IsClosed (S : Set ℂ) := S.finite_toSet.isClosed
    have hRS : Rectangle z w \ (S : Set ℂ) ∈ 𝓝 p := by
      apply Filter.inter_mem hp
      exact TB.isOpen_compl.mem_nhds (by simpa using hpS)
    obtain ⟨U, hU, hbdd⟩ := Cz (near p (Finset.mem_insert_self p S))
    have hV : U ∩ (Rectangle z w \ (S : Set ℂ)) ∈ 𝓝 p := Filter.inter_mem hU hRS
    have Xf : DifferentiableOn ℂ f₁ ((U ∩ (Rectangle z w \ (S : Set ℂ))) \ {p}) := by
      apply Lz.mono
      rintro s ⟨⟨_, JG, hsS⟩, hsp⟩
      refine ⟨JG, ?_⟩
      simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or]
      exact ⟨by simpa using hsp, by simpa using hsS⟩
    have Zd : BddAbove (norm ∘ f₁ '' ((U ∩ (Rectangle z w \ (S : Set ℂ))) \ {p})) :=
      hbdd.mono (image_mono (Set.sdiff_subset_sdiff_left inter_subset_left))
    have Xg : DifferentiableOn ℂ f₂ (U ∩ (Rectangle z w \ (S : Set ℂ))) :=
      differentiableOn_update_limUnder_of_bddAbove hV Xf Zd
    have DS : ∀ s, s ≠ p → f₂ s = f₁ s := fun s hs => Function.update_of_ne hs _ _
    have LD : iG f₂ (Rectangle z w \ (S : Set ℂ)) := by
      intro s hs
      by_cases hsp : s = p
      · rw [hsp]
        exact (Xg.differentiableAt hV).differentiableWithinAt
      · have h1 : DifferentiableWithinAt ℂ f₁
            (Rectangle z w \ ((insert p S : Finset ℂ) : Set ℂ)) s :=
          Lz s ⟨hs.1, by
            simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or]
            exact ⟨hsp, by simpa using hs.2⟩⟩
        have hset : (Rectangle z w \ ((insert p S : Finset ℂ) : Set ℂ))
            = (Rectangle z w \ (S : Set ℂ)) ∩ {p}ᶜ := by
          ext x
          simp only [Finset.coe_insert, Set.mem_sdiff, mem_insert_iff, Finset.mem_coe, not_or,
            mem_inter_iff, mem_compl_iff, mem_singleton_iff]
          tauto
        rw [hset] at h1
        have hpc : {p}ᶜ ∈ 𝓝[Rectangle z w \ (S : Set ℂ)] s :=
          mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hsp)
        rw [differentiableWithinAt_inter' hpc] at h1
        refine h1.congr_of_eventuallyEq ?_ (DS s hsp)
        filter_upwards [hpc] with x hx
        exact DS x hx
    have Vz : ∀ q ∈ S, (f₂ - fun s => A q / (s - q)) =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
      intro q hq
      have hqp : q ≠ p := fun h => hpS (h ▸ hq)
      have hev : ((f - fun s => A q / (s - q)) - P)
          =ᶠ[𝓝[≠] q] (f₂ - fun s => A q / (s - q)) := by
        have : {p}ᶜ ∈ 𝓝[≠] q :=
          mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hqp)
        filter_upwards [this] with s hs
        simp only [Pi.sub_apply, DS s hs, hf₁]
        ring
      have hPO : P =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
        have hc : ContinuousAt P q := (Dk q hqp).continuousAt
        exact (hc.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
      exact ((near q (Finset.mem_insert_of_mem hq)).sub hPO).congr' hev EventuallyEq.rfl
    have ih' := ih hS' LD Vz
    have zE : EqOn f (f₂ + P) (aZ z w) := by
      intro s hs
      have hsp : s ≠ p := fun h => dG hp (h ▸ hs)
      simp only [Pi.add_apply, DS s hsp, hf₁, Pi.sub_apply, sub_add_cancel]
    have hbS : ∀ s ∈ aZ z w, s ∈ Rectangle z w \ (S : Set ℂ) := fun s hs =>
      ⟨jc z w hs,
        fun hsS => dG (hS' s hsS) hs⟩
    have hi₂ : cQ f₂ z w :=
      ContinuousOn.ko (LD.continuousOn.mono hbS)
    have hiP : cQ P z w := by
      apply ContinuousOn.ko
      intro s hs
      have hsp : s ≠ p := fun h => dG hp (h ▸ hs)
      exact (Dk s hsp).continuousAt.continuousWithinAt
    rw [uO zE, Finset.sum_insert hpS]
    show (1 / (2 * π * I)) • aY (f₂ + P) z w = _
    rw [cQ.add hi₂ hiP, smul_add]
    show bF f₂ z w + bF P z w = _
    rw [ih', tq hre him hp, add_comm]
theorem jY {f g : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (Z P : Finset ℂ) (UC : Disjoint Z P)
    (JI : ∀ p ∈ P, Rectangle z w ∈ 𝓝 p)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w \ (P : Set ℂ)))
    (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (zE : ∀ s ∈ aZ z w, f s ≠ 0)
    (hZ : ∀ s ∈ Rectangle z w \ (P : Set ℂ), f s = 0 ↔ s ∈ Z) (JK : (Z : Set ℂ) ⊆ Rectangle z w)
    (m : ℂ → ℕ)
    (Qm : ∀ p ∈ P, ∃ c : ℂ, c ≠ 0 ∧ Tendsto (fun s => (s - p) ^ m p * f s) (𝓝[≠] p) (𝓝 c)) :
    bF (fun s => g s * logDeriv f s) z w
      = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * g ρ - ∑ p ∈ P, (m p : ℂ) * g p := by
  classical
  have Nw : ∀ ρ ∈ Z, ρ ∉ P := fun ρ hρ Ny => Finset.disjoint_left.mp UC hρ Ny
  have Mc : ∀ ρ ∈ Z, ρ ∈ Rectangle z w \ (P : Set ℂ) := fun ρ hρ =>
    ⟨JK hρ, by simpa using Nw ρ hρ⟩
  have Ze : ∀ ρ ∈ Z, Rectangle z w ∈ 𝓝 ρ := by
    intro ρ hρ
    have aaG : ρ ∈ Rectangle z w := JK hρ
    have Xh : ρ ∉ aZ z w := fun h => zE ρ h ((hZ ρ (Mc ρ hρ)).mpr hρ)
    obtain ⟨h1, h2⟩ := aaG
    have h1' : z.re ≤ ρ.re ∧ ρ.re ≤ w.re := by simpa [uIcc_of_le hre] using h1
    have h2' : z.im ≤ ρ.im ∧ ρ.im ≤ w.im := by simpa [uIcc_of_le him] using h2
    simp only [aZ, mem_union, mem_reProdIm, mem_singleton_iff, not_or] at Xh
    obtain ⟨⟨⟨hb1, hb2⟩, hb3⟩, hb4⟩ := Xh
    rw [gY, mem_reProdIm, uIoo_of_le hre, uIoo_of_le him]
    refine ⟨⟨lt_of_le_of_ne h1'.1 (fun h => hb2 ⟨h.symm, h2⟩),
      lt_of_le_of_ne h1'.2 (fun h => hb4 ⟨h, h2⟩)⟩,
      ⟨lt_of_le_of_ne h2'.1 (fun h => hb1 ⟨h1, h.symm⟩),
      lt_of_le_of_ne h2'.2 (fun h => hb3 ⟨h1, h⟩)⟩⟩
  let A : ℂ → ℂ := fun q => if q ∈ P then -((m q : ℂ) * g q) else (analyticOrderNatAt f q : ℂ) * g q
  have hint : ∀ q ∈ Z ∪ P, Rectangle z w ∈ 𝓝 q := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    exacts [Ze q hq, JI q hq]
  have key := zD (f := fun s => g s * logDeriv f s) hre him (Z ∪ P) A hint
    ?holo ?near
  · rw [key, Finset.sum_union UC]
    have Qk : ∑ q ∈ Z, A q = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * g ρ :=
      Finset.sum_congr rfl (fun q hq => by simp [A, Nw q hq])
    have Qo : ∑ q ∈ P, A q = -∑ p ∈ P, (m p : ℂ) * g p := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun q hq => by simp [A, hq])
    rw [Qk, Qo, sub_eq_add_neg]
  case holo =>
    intro s hs
    have hsP : s ∉ P := fun h => hs.2 (by simp [h])
    have UE : s ∉ Z := fun h => hs.2 (by simp [h])
    have KW : s ∈ Rectangle z w \ (P : Set ℂ) := ⟨hs.1, by simpa using hsP⟩
    have hfs : f s ≠ 0 := fun h => UE ((hZ s KW).mp h)
    have hfa := hf s KW
    have hga := hg s hs.1
    apply DifferentiableAt.differentiableWithinAt
    show DifferentiableAt ℂ (fun s => g s * (deriv f s / f s)) s
    exact hga.differentiableAt.mul (hfa.deriv.differentiableAt.div hfa.differentiableAt hfs)
  case near =>
    intro q hq
    rcases Finset.mem_union.mp hq with hρ | hp
    · 
      have Zj := Mc q hρ
      have hga := hg q (JK hρ)
      have hA : A q = (analyticOrderNatAt f q : ℂ) * g q := by simp [A, Nw q hρ]
      by_cases htop : analyticOrderAt f q = ⊤
      · 
        have h0 : ∀ᶠ s in 𝓝 q, f s = 0 := analyticOrderAt_eq_top.mp htop
        have hO : (fun _ : ℂ => (0 : ℂ)) =O[𝓝[≠] q] (1 : ℂ → ℂ) := isBigO_zero _ _
        refine hO.congr' ?_ EventuallyEq.rfl
        filter_upwards [mem_nhdsWithin_of_mem_nhds (h0.eventually_nhds)] with s hs
        have hs' : f =ᶠ[𝓝 s] fun _ => (0 : ℂ) := hs
        have hds : deriv f s = 0 := by
          rw [hs'.deriv_eq]; simp
        simp [hA, logDeriv_apply, hds, analyticOrderNatAt, htop]
      obtain ⟨h, hh, hh0, hfh⟩ := (hf q Zj).analyticOrderAt_ne_top.mp htop
      have Zk : ∀ᶠ s in 𝓝 q, h s ≠ 0 := hh.continuousAt.eventually_ne hh0
      have h2 : ∀ᶠ s in 𝓝 q, f =ᶠ[𝓝 s] (fun s => (s - q) ^ analyticOrderNatAt f q • h s) :=
        hfh.eventually_nhds
      have h3 : ∀ᶠ s in 𝓝 q, AnalyticAt ℂ h s := hh.eventually_analyticAt
      have hexp : ∀ᶠ s in 𝓝[≠] q,
          (analyticOrderNatAt f q : ℂ) * ((g s - g q) / (s - q)) + g s * logDeriv h s
            = ((fun s => g s * logDeriv f s) - fun s => A q / (s - q)) s := by
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds h2,
          mem_nhdsWithin_of_mem_nhds Zk, mem_nhdsWithin_of_mem_nhds h3]
          with s hs hfs hhs aaH
        have hsq : s - q ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
        have hld : logDeriv f s = (analyticOrderNatAt f q : ℂ) / (s - q) + logDeriv h s := by
          have e1 : logDeriv f s
              = logDeriv (fun s => (s - q) ^ analyticOrderNatAt f q * h s) s := by
            simp only [logDeriv_apply, hfs.deriv_eq, hfs.self_of_nhds, smul_eq_mul]
          rw [e1, logDeriv_mul (f := fun s : ℂ => (s - q) ^ analyticOrderNatAt f q) (g := h) s
            (pow_ne_zero _ hsq) hhs (by fun_prop) aaH.differentiableAt]
          have e2 : logDeriv (fun s : ℂ => (s - q) ^ analyticOrderNatAt f q) s
              = (analyticOrderNatAt f q : ℂ) / (s - q) := by
            rw [show (fun s : ℂ => (s - q) ^ analyticOrderNatAt f q)
                = (fun x : ℂ => x ^ analyticOrderNatAt f q) ∘ (fun s => s - q) from rfl,
              logDeriv_comp (by fun_prop) (by fun_prop), logDeriv_pow]
            simp
          rw [e2]
        simp only [Pi.sub_apply, hld, hA]
        ring
      have hslope : Tendsto (fun s => (g s - g q) / (s - q)) (𝓝[≠] q) (𝓝 (deriv g q)) := by
        have := hasDerivAt_iff_tendsto_slope.mp hga.differentiableAt.hasDerivAt
        simpa only [slope_fun_def_field] using this
      have hcont : Tendsto (fun s => g s * logDeriv h s) (𝓝[≠] q)
          (𝓝 (g q * logDeriv h q)) := by
        have : ContinuousAt (fun s => g s * logDeriv h s) q := by
          show ContinuousAt (fun s => g s * (deriv h s / h s)) q
          exact hga.continuousAt.mul (hh.deriv.continuousAt.div hh.continuousAt hh0)
        exact this.tendsto.mono_left nhdsWithin_le_nhds
      have hO : (fun s => (analyticOrderNatAt f q : ℂ) * ((g s - g q) / (s - q))
          + g s * logDeriv h s) =O[𝓝[≠] q] (1 : ℂ → ℂ) :=
        ((hslope.const_mul (analyticOrderNatAt f q : ℂ)).add hcont).isBigO_one ℂ
      exact hO.congr' hexp EventuallyEq.rfl
    · 
      obtain ⟨c, hc, hT⟩ := Qm q hp
      have hqR : q ∈ Rectangle z w := mem_of_mem_nhds (JI q hp)
      have hga := hg q hqR
      have hA : A q = -((m q : ℂ) * g q) := by simp [A, hp]
      set F : ℂ → ℂ := fun s => (s - q) ^ m q * f s with hF
      set G : ℂ → ℂ := Function.update F q c with hG
      have hGq : G q = c := Function.update_self _ _ _
      have hGF : ∀ s, s ≠ q → G s = F s := fun s hs => Function.update_of_ne hs _ _
      have hPc : ((P : Set ℂ) \ {q})ᶜ ∈ 𝓝 q :=
        (P.finite_toSet.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
      have JL : ∀ᶠ s in 𝓝[≠] q, s ≠ q ∧ s ∈ Rectangle z w \ (P : Set ℂ) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (JI q hp),
          mem_nhdsWithin_of_mem_nhds hPc, self_mem_nhdsWithin] with s h1 h2 h3
        have h3' : s ≠ q := by simpa using h3
        exact ⟨h3', h1, fun hsP => h2 ⟨hsP, by simpa using h3'⟩⟩
      have Xj : ∀ᶠ s in 𝓝[≠] q, DifferentiableAt ℂ G s := by
        filter_upwards [JL] with s ⟨hsq, KW⟩
        have hFs : DifferentiableAt ℂ F s :=
          ((differentiableAt_id.sub_const q).pow _).mul (hf s KW).differentiableAt
        refine hFs.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_compl_singleton.mem_nhds hsq] with x hx
        exact hGF x hx
      have Xk : ContinuousAt G q := by
        rw [hG, continuousAt_update_same]
        exact hT
      have Nz : AnalyticAt ℂ G q :=
        analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt Xj Xk
      have hG0 : G q ≠ 0 := by rwa [hGq]
      have hFne : ∀ᶠ s in 𝓝[≠] q, F s ≠ 0 := hT.eventually_ne hc
      have Zl : ∀ᶠ s in 𝓝 q, AnalyticAt ℂ G s := Nz.eventually_analyticAt
      have hexp : ∀ᶠ s in 𝓝[≠] q,
          g s * logDeriv G s - (m q : ℂ) * ((g s - g q) / (s - q))
            = ((fun s => g s * logDeriv f s) - fun s => A q / (s - q)) s := by
        filter_upwards [JL, hFne, mem_nhdsWithin_of_mem_nhds Zl] with s ⟨hsq, KW⟩ hFs hGs
        have aaI : s - q ≠ 0 := sub_ne_zero.mpr hsq
        have hfs : f s ≠ 0 := fun h => hFs (by simp [hF, h])
        have hfd : DifferentiableAt ℂ f s := (hf s KW).differentiableAt
        have aaJ : logDeriv F s = (m q : ℂ) / (s - q) + logDeriv f s := by
          rw [hF, logDeriv_mul (f := fun s : ℂ => (s - q) ^ m q) (g := f) s
            (pow_ne_zero _ aaI) hfs (by fun_prop) hfd]
          have e2 : logDeriv (fun s : ℂ => (s - q) ^ m q) s = (m q : ℂ) / (s - q) := by
            rw [show (fun s : ℂ => (s - q) ^ m q) = (fun x : ℂ => x ^ m q) ∘ (fun s => s - q)
                from rfl, logDeriv_comp (by fun_prop) (by fun_prop), logDeriv_pow]
            simp
          rw [e2]
        have Xl : G =ᶠ[𝓝 s] F := by
          filter_upwards [isOpen_compl_singleton.mem_nhds hsq] with x hx
          exact hGF x hx
        have aaK : logDeriv G s = logDeriv F s := by
          simp only [logDeriv_apply, Xl.deriv_eq, Xl.self_of_nhds]
        simp only [Pi.sub_apply, hA, aaK, aaJ]
        ring
      have hslope : Tendsto (fun s => (g s - g q) / (s - q)) (𝓝[≠] q) (𝓝 (deriv g q)) := by
        have := hasDerivAt_iff_tendsto_slope.mp hga.differentiableAt.hasDerivAt
        simpa only [slope_fun_def_field] using this
      have hcont : Tendsto (fun s => g s * logDeriv G s) (𝓝[≠] q)
          (𝓝 (g q * logDeriv G q)) := by
        have : ContinuousAt (fun s => g s * logDeriv G s) q := by
          show ContinuousAt (fun s => g s * (deriv G s / G s)) q
          exact hga.continuousAt.mul (Nz.deriv.continuousAt.div Nz.continuousAt hG0)
        exact this.tendsto.mono_left nhdsWithin_le_nhds
      have hO : (fun s => g s * logDeriv G s - (m q : ℂ) * ((g s - g q) / (s - q)))
          =O[𝓝[≠] q] (1 : ℂ → ℂ) :=
        (hcont.sub (hslope.const_mul (m q : ℂ))).isBigO_one ℂ
      exact hO.congr' hexp EventuallyEq.rfl
end Analytic
end Zeta23
end
end

-- Zeta23.kB.UF
section
open Complex Set Topology Filter Real
noncomputable section
namespace Zeta23
namespace kB
lemma jh {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta s := by
  have hopen : IsOpen (({0, 1} : Set ℂ)ᶜ) := (Set.toFinite _).isClosed.isOpen_compl
  have hdiff : DifferentiableOn ℂ completedRiemannZeta (({0, 1} : Set ℂ)ᶜ) := by
    intro z hz
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    exact (differentiableAt_completedZeta hz.1 hz.2).differentiableWithinAt
  exact hdiff.analyticAt (hopen.mem_nhds (by simp [h0, h1]))
lemma lG {s : ℂ} (hs : s ≠ 0) (hG : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  rw [riemannZeta_def_of_ne_zero hs]
  field_simp
lemma cE {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = 0 ↔ riemannZeta s = 0 := by
  have h0 : s ≠ 0 := fun h => by simp [h] at hs
  have hG := Gammaℝ_ne_zero_of_re_pos hs
  rw [lG h0 hG, mul_eq_zero]
  simp [hG]
lemma cP {s : ℂ} (hs : 1 ≤ s.re) :
    completedRiemannZeta s ≠ 0 := by
  rw [Ne, cE (by linarith)]
  exact riemannZeta_ne_zero_of_one_le_re hs
lemma gC {s : ℂ} (hs : s.re ≤ 0) :
    completedRiemannZeta s ≠ 0 := by
  rw [← completedRiemannZeta_one_sub]
  exact cP (by simp; linarith)
lemma kC {ρ : ℂ} (h : 0 < ρ.re) (h1 : ρ ≠ 1) :
    analyticOrderNatAt completedRiemannZeta ρ = bY ρ := by
  have h0 : ρ ≠ 0 := fun h' => by simp [h'] at h
  have hev : riemannZeta =ᶠ[𝓝 ρ] (completedRiemannZeta * fun s => (Gammaℝ s)⁻¹) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds h0] with s hs
    rw [Pi.mul_apply, riemannZeta_def_of_ne_zero hs, div_eq_mul_inv]
  have hΛ := jh h0 h1
  have UG : AnalyticAt ℂ (fun s => (Gammaℝ s)⁻¹) ρ := differentiable_Gammaℝ_inv.analyticAt ρ
  have hG0 : analyticOrderAt (fun s => (Gammaℝ s)⁻¹) ρ = 0 :=
    UG.analyticOrderAt_eq_zero.mpr (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos h))
  unfold bY analyticOrderNatAt
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hΛ UG, hG0, add_zero]
end kB
end Zeta23
end
end

-- Zeta23.cw.abr
section
noncomputable section
namespace Zeta23
namespace cw
open Complex Topology Filter Set
theorem Dz {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (bD : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) {R : ℝ} (hR : 7 ≤ R)
    (Me : ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 - c ≤ s.re → s.re ≤ c →
      completedRiemannZeta s ≠ 0) :
    ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ : ℂ | aO ρ ∧ -R < ρ.im ∧ ρ.im < R}) ∧
      bF (fun s => aW k s * logDeriv completedRiemannZeta s)
          ((1 - c : ℝ) - R * I) ((c : ℝ) + R * I)
        = (∑ ρ ∈ Z, (bY ρ : ℂ) * aW k ρ) - aW k 0 - aW k 1 := by
  classical
  set z : ℂ := (1 - c : ℝ) - R * I with UH
  set w : ℂ := (c : ℝ) + R * I with hwdef
  have hzre : z.re = 1 - c := by simp [UH]
  have hzim : z.im = -R := by simp [UH]
  have Dx : w.re = c := by simp [hwdef]
  have Gp : w.im = R := by simp [hwdef]
  have hre : z.re ≤ w.re := by rw [hzre, Dx]; linarith
  have him : z.im ≤ w.im := by rw [hzim, Gp]; linarith
  have hmem : ∀ s : ℂ, s ∈ Rectangle z w ↔
      (1 - c ≤ s.re ∧ s.re ≤ c) ∧ (-R ≤ s.im ∧ s.im ≤ R) := by
    intro s
    simp only [Rectangle, Complex.mem_reProdIm, hzre, hzim, Dx, Gp,
      Set.uIcc_of_le (show (1 - c : ℝ) ≤ c by linarith),
      Set.uIcc_of_le (show (-R : ℝ) ≤ R by linarith), Set.mem_Icc]
  set P : Finset ℂ := {0, 1} with DU
  have hfin := Fw.dS (-R) R
  set Z : Finset ℂ := hfin.toFinset with Zm
  have vT : ∀ ρ : ℂ, ρ ∈ Z ↔ (aO ρ ∧ -R < ρ.im ∧ ρ.im ≤ R) := by
    intro ρ
    rw [Zm, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2⟩
  have Zn : (Z : Set ℂ) = {ρ : ℂ | aO ρ ∧ -R < ρ.im ∧ ρ.im < R} := by
    ext ρ
    rw [Finset.mem_coe, vT]
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, lt_of_le_of_ne h3 ?_⟩
      intro h
      exact Me ρ (Or.inl h) (by linarith [h1.2.1]) (by linarith [h1.2.2])
        ((Zeta23.kB.cE h1.2.1).mpr h1.1)
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, h3.le⟩
  refine ⟨Z, Zn, ?_⟩
  have UC : Disjoint Z P := by
    rw [Finset.disjoint_left]
    intro ρ hρ Ny
    have h1 := ((vT ρ).mp hρ).1
    rw [DU] at Ny
    simp only [Finset.mem_insert, Finset.mem_singleton] at Ny
    rcases Ny with rfl | rfl
    · have h2 := h1.2.1
      rw [Complex.zero_re] at h2
      exact lt_irrefl _ h2
    · have h2 := h1.2.2
      rw [Complex.one_re] at h2
      exact lt_irrefl _ h2
  have JI : ∀ p ∈ P, Rectangle z w ∈ 𝓝 p := by
    intro p hp
    rw [gY, Complex.mem_reProdIm, Set.uIoo_of_le hre, Set.uIoo_of_le him,
      hzre, hzim, Dx, Gp]
    rw [DU] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · constructor
      · simp only [Complex.zero_re, Set.mem_Ioo]
        constructor <;> linarith
      · simp only [Complex.zero_im, Set.mem_Ioo]
        constructor <;> linarith
    · constructor
      · simp only [Complex.one_re, Set.mem_Ioo]
        constructor <;> linarith
      · simp only [Complex.one_im, Set.mem_Ioo]
        constructor <;> linarith
  have hf : AnalyticOnNhd ℂ completedRiemannZeta (Rectangle z w \ (P : Set ℂ)) := by
    rintro s ⟨_, hsP⟩
    rw [DU] at hsP
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hsP
    exact Zeta23.kB.jh hsP.1 hsP.2
  have hg : AnalyticOnNhd ℂ (aW k) (Rectangle z w) := by
    intro s _
    have hdiff : Differentiable ℂ (aW k) := by
      unfold aW
      exact (jI hk.continuous bD).comp
        ((differentiable_id.sub_const _).div_const _)
    exact hdiff.analyticAt s
  have zE : ∀ s ∈ aZ z w, completedRiemannZeta s ≠ 0 := by
    intro s hs h0
    have NA := jc z w hs
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp NA
    simp only [aZ, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
      hzre, hzim, Dx, Gp] at hs
    rcases hs with ((⟨_, h'⟩ | ⟨h', _⟩) | ⟨_, h'⟩) | ⟨h', _⟩
    · exact Me s (Or.inr h') hr1 hr2 h0
    · exact Zeta23.kB.gC (by rw [h']; linarith) h0
    · exact Me s (Or.inl h') hr1 hr2 h0
    · exact Zeta23.kB.cP (by rw [h']; linarith) h0
  have Xm : ∀ s ∈ Rectangle z w \ (P : Set ℂ), (completedRiemannZeta s = 0 ↔ s ∈ Z) := by
    rintro s ⟨NA, hsP⟩
    rw [DU] at hsP
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hsP
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp NA
    rw [vT]
    constructor
    · intro h0
      have RO : 0 < s.re := by
        by_contra hle
        exact Zeta23.kB.gC (by linarith) h0
      have Zo : s.re < 1 := by
        by_contra hge
        exact Zeta23.kB.cP (by linarith) h0
      have hnz : aO s :=
        ⟨(Zeta23.kB.cE RO).mp h0, RO, Zo⟩
      refine ⟨hnz, ?_, hi2⟩
      rcases lt_or_eq_of_le hi1 with h | h
      · exact h
      · exact absurd h0 (Me s (Or.inr h.symm) hr1 hr2)
    · rintro ⟨h1, _, _⟩
      exact (Zeta23.kB.cE h1.2.1).mpr h1.1
  have JK : (Z : Set ℂ) ⊆ Rectangle z w := by
    intro ρ hρ
    rw [Finset.mem_coe, vT] at hρ
    obtain ⟨h1, h2, h3⟩ := hρ
    exact (hmem ρ).mpr ⟨⟨by linarith [h1.2.1], by linarith [h1.2.2]⟩, h2.le, h3⟩
  have Qm : ∀ p ∈ P, ∃ cp : ℂ, cp ≠ 0 ∧
      Filter.Tendsto (fun s => (s - p) ^ (1 : ℕ) * completedRiemannZeta s)
        (nhdsWithin p {p}ᶜ) (nhds cp) := by
    intro p hp
    rw [DU] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · refine ⟨-1, by norm_num, ?_⟩
      have h := HurwitzZeta.completedHurwitzZetaEven_residue_zero (0 : UnitAddCircle)
      norm_num at h
      refine h.congr (fun s => ?_)
      simp [completedRiemannZeta]
    · refine ⟨1, one_ne_zero, ?_⟩
      refine completedRiemannZeta_residue_one.congr (fun s => ?_)
      simp
  have key := Zeta23.Analytic.jY hre him Z P UC JI hf hg
    zE Xm JK (fun _ => 1) Qm
  rw [key]
  have hord : ∀ ρ ∈ Z, (analyticOrderNatAt completedRiemannZeta ρ : ℂ) = (bY ρ : ℂ) := by
    intro ρ hρ
    have h1 := ((vT ρ).mp hρ).1
    rw [Zeta23.kB.kC h1.2.1
      (fun h' => by
        have h2 := h1.2.2
        rw [h', Complex.one_re] at h2
        exact lt_irrefl _ h2)]
  have Qo : ∑ p ∈ P, ((1 : ℕ) : ℂ) * aW k p = aW k 0 + aW k 1 := by
    rw [DU, Finset.sum_insert (by simp), Finset.sum_singleton]
    ring
  rw [Finset.sum_congr rfl (fun ρ hρ => by rw [hord ρ hρ]), Qo]
  ring
end cw
end Zeta23
end
end

-- Zeta23.cw.aaL
section
noncomputable section
namespace Zeta23
namespace cw
open Complex Topology Filter Set MeasureTheory
open scoped ArithmeticFunction
section RP
theorem RQ (k : ℝ → ℂ) (σ t : ℝ) :
    aW k ((σ : ℂ) + t * I) = aD k ((t : ℂ) + ((1 / 2 - σ : ℝ) : ℂ) * I) := by
  unfold aW
  congr 1
  apply Complex.ext <;> simp
theorem qI {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (bD : HasCompactSupport k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, -1 ≤ σ → σ ≤ 2 → ‖aW k ((σ : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨Λ₁, Nl⟩ := Zeta23.EF.bZ bD
  set B : ℝ := max Λ₁ 0 with hB
  have hsupp : ∀ u, k u ≠ 0 → |u| ≤ B := fun u hu => (Nl u hu).trans (le_max_left _ _)
  have hB0 : 0 ≤ B := le_max_right _ _
  have hki : Integrable k := hk.continuous.integrable_of_hasCompactSupport bD
  set A : ℝ := Real.exp (3 / 2 * B) * ((∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖) with hA
  have hI1 : 0 ≤ ∫ u, ‖k u‖ := integral_nonneg fun _ => norm_nonneg _
  have hI2 : 0 ≤ ∫ u, ‖deriv (deriv k) u‖ := integral_nonneg fun _ => norm_nonneg _
  have hA0 : 0 ≤ A := by positivity
  refine ⟨2 * A, by positivity, fun σ t hσ1 hσ2 => ?_⟩
  rw [RQ]
  set z : ℂ := (t : ℂ) + ((1 / 2 - σ : ℝ) : ℂ) * I with hz
  have hzim : z.im = 1 / 2 - σ := by simp [hz]
  have hzre : z.re = t := by simp [hz]
  have him : |z.im| ≤ 3 / 2 := by rw [hzim, abs_le]; constructor <;> linarith
  have hexp : Real.exp (|z.im| * B) ≤ Real.exp (3 / 2 * B) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right him hB0)
  have hzn : |t| ≤ ‖z‖ := by rw [← hzre]; exact Complex.abs_re_le_norm z
  have ht2 : 0 < 1 + t ^ 2 := by positivity
  by_cases ht : |t| ≤ 1
  · 
    have h1 := Zeta23.jz hki hsupp z
    calc ‖aD k z‖ ≤ Real.exp (|z.im| * B) * ∫ u, ‖k u‖ := h1
      _ ≤ Real.exp (3 / 2 * B) * ∫ u, ‖k u‖ := by gcongr
      _ ≤ A := by rw [hA]; nlinarith [Real.exp_pos (3 / 2 * B)]
      _ ≤ 2 * A / (1 + t ^ 2) := by
          rw [le_div_iff₀ ht2]
          have : t ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
          nlinarith
  · 
    push Not at ht
    have hz0 : z ≠ 0 := by
      intro h; rw [h] at hzn; simp at hzn; rw [hzn] at ht; simp at ht; linarith
    have h2 := Zeta23.kL hk hsupp hz0
    have acV : t ^ 2 ≤ ‖z‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hzn 2
    have ht1 : 1 ≤ t ^ 2 := by rw [← sq_abs]; nlinarith
    calc ‖aD k z‖ ≤ Real.exp (|z.im| * B) * (∫ u, ‖deriv (deriv k) u‖) / ‖z‖ ^ 2 := h2
      _ ≤ Real.exp (3 / 2 * B) * (∫ u, ‖deriv (deriv k) u‖) / t ^ 2 := by
          gcongr
      _ ≤ A / t ^ 2 := by
          gcongr; rw [hA]; nlinarith [Real.exp_pos (3 / 2 * B)]
      _ ≤ 2 * A / (1 + t ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) ht2]; nlinarith
theorem gR {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (bD : HasCompactSupport k) (σ : ℝ) :
    Continuous (fun t : ℝ => aW k ((σ : ℂ) + t * I)) := by
  have h := (jI hk.continuous bD).continuous
  unfold aW
  exact h.comp (by fun_prop)
theorem mJ {c : ℝ} (hc1 : 1 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, ‖logDeriv riemannZeta ((c : ℂ) + t * I)‖ ≤ M := by
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := fun t => by simp
  have hsum : Summable (fun n : ℕ => ‖LSeries.term (fun n => (Λ n : ℂ)) (c : ℂ) n‖) := by
    have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (c : ℂ)) (by simpa using hc1)
    exact summable_norm_iff.mpr h
  refine ⟨∑' n : ℕ, ‖LSeries.term (fun n => (Λ n : ℂ)) (c : ℂ) n‖,
    tsum_nonneg fun _ => norm_nonneg _, fun t => ?_⟩
  have Dt : 1 < ((c : ℂ) + t * I).re := by rw [hre]; exact hc1
  have h1 : logDeriv riemannZeta ((c : ℂ) + t * I)
      = -LSeries (fun n => (Λ n : ℂ)) ((c : ℂ) + t * I) := by
    have h2 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div Dt
    rw [logDeriv, Pi.div_apply, h2]; ring
  have hnorm : ∀ n : ℕ, ‖LSeries.term (fun n => (Λ n : ℂ)) ((c : ℂ) + t * I) n‖
      = ‖LSeries.term (fun n => (Λ n : ℂ)) (c : ℂ) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hre, Complex.ofReal_re]
  have hsum' : Summable (fun n : ℕ => ‖LSeries.term (fun n => (Λ n : ℂ)) ((c : ℂ) + t * I) n‖) := by
    simp_rw [hnorm]; exact hsum
  rw [h1, norm_neg, LSeries]
  calc ‖∑' n, LSeries.term (fun n => (Λ n : ℂ)) ((c : ℂ) + t * I) n‖
      ≤ ∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) ((c : ℂ) + t * I) n‖ := norm_tsum_le_tsum_norm hsum'
    _ = ∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) (c : ℂ) n‖ := by simp_rw [hnorm]
theorem jM {c : ℝ} (hc1 : 1 < c) :
    Continuous (fun t : ℝ => logDeriv riemannZeta ((c : ℂ) + t * I)) := by
  have hline : Continuous (fun t : ℝ => ((c : ℂ) + t * I)) := by fun_prop
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hs1 : ((c : ℂ) + t * I) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have Dt : 1 < ((c : ℂ) + t * I).re := by simp; linarith
  have hζ : riemannZeta ((c : ℂ) + t * I) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re Dt
  have han := nD hs1
  have hd : ContinuousAt (deriv riemannZeta) ((c : ℂ) + t * I) := han.deriv.continuousAt
  have hc : ContinuousAt riemannZeta ((c : ℂ) + t * I) := han.continuousAt
  have : ContinuousAt (fun s => deriv riemannZeta s / riemannZeta s) ((c : ℂ) + t * I) :=
    hd.div hc hζ
  show ContinuousAt ((fun s => deriv riemannZeta s / riemannZeta s) ∘ (fun t : ℝ => (c : ℂ) + t * I)) t
  exact ContinuousAt.comp this hline.continuousAt
theorem gW {φ : ℝ → ℂ} (hφc : Continuous φ) {C : ℝ}
    (hφ : ∀ t, ‖φ t‖ ≤ C / (1 + t ^ 2)) {c : ℝ} (hc1 : 1 < c) :
    Integrable (fun t : ℝ => φ t * logDeriv riemannZeta ((c : ℂ) + t * I)) := by
  obtain ⟨M, hM0, hM⟩ := mJ hc1
  have hC0 : 0 ≤ C := by
    have := le_trans (norm_nonneg _) (hφ 0); simpa using this
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul (C * M)))
    (hφc.mul (jM hc1)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  calc ‖φ t‖ * ‖logDeriv riemannZeta ((c : ℂ) + t * I)‖
      ≤ (C / (1 + t ^ 2)) * M := mul_le_mul (hφ t) (hM t) (norm_nonneg _) (by positivity)
    _ = C * M * (1 + t ^ 2)⁻¹ := by ring
theorem je {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (bD : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) :
    Integrable (fun t : ℝ => aW k ((c : ℂ) + t * I) * logDeriv riemannZeta ((c : ℂ) + t * I)) := by
  obtain ⟨C, hC0, hC⟩ := qI hk bD
  exact gW (gR hk bD c)
    (fun t => hC c t (by linarith) (by linarith)) hc1
theorem KX {x : ℝ} (hx : 0 ≤ x) : Real.log (2 + x) ≤ 5 * (1 + x ^ 2) ^ (1 / 4 : ℝ) := by
  have h2x : 0 < 2 + x := by linarith
  have h1 : Real.log (2 + x) ≤ 2 * Real.sqrt (2 + x) := by
    have hs : 0 < Real.sqrt (2 + x) := Real.sqrt_pos.mpr h2x
    have := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt h2x.le] at this
    linarith
  have h2 : Real.sqrt (2 + x) ≤ 3 / 2 + Real.sqrt x := by
    have hsx := Real.sq_sqrt hx
    have hs0 := Real.sqrt_nonneg x
    calc Real.sqrt (2 + x) ≤ Real.sqrt ((3 / 2 + Real.sqrt x) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 3 / 2 + Real.sqrt x := Real.sqrt_sq (by positivity)
  have hq0 : 0 ≤ (1 + x ^ 2 : ℝ) := by positivity
  have h3 : Real.sqrt x ≤ (1 + x ^ 2) ^ (1 / 4 : ℝ) := by
    have e : Real.sqrt x = (x ^ 2) ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul hx]; norm_num
    rw [e]
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have h4 : (1 : ℝ) ≤ (1 + x ^ 2) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by nlinarith) (by norm_num)
  linarith
theorem iW {σ : ℝ} (TD : 0 < σ) (hσ2 : σ ≤ 3 / 2) :
    Continuous (fun t : ℝ => logDeriv Complex.Gammaℝ ((σ : ℂ) + t * I)) := by
  have hfun : (fun t : ℝ => logDeriv Complex.Gammaℝ ((σ : ℂ) + t * I))
      = fun t : ℝ => -((Real.log Real.pi : ℝ) : ℂ) / 2
        + (1 / 2) * Complex.digamma (((σ : ℂ) + t * I) / 2) := by
    funext t
    exact gP (by simp; exact TD)
  rw [hfun]
  refine continuous_const.add (continuous_const.mul ?_)
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hz : ((σ : ℂ) + t * I) / 2 ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    have him := congrArg Complex.im hn
    simp at hre him
    have h1 : (0 : ℝ) < n := by rw [hre]; linarith
    have h2 : (n : ℝ) < 1 := by rw [hre]; linarith
    have : (0 : ℤ) < n := by exact_mod_cast h1
    have : n < (1 : ℤ) := by exact_mod_cast h2
    omega
  show ContinuousAt (Complex.digamma ∘ fun t : ℝ => ((σ : ℂ) + t * I) / 2) t
  exact ContinuousAt.comp (g := Complex.digamma) (f := fun t : ℝ => ((σ : ℂ) + t * I) / 2)
    (Zeta23.Stirling.lC hz).continuousAt
    (by fun_prop : Continuous fun t : ℝ => ((σ : ℂ) + t * I) / 2).continuousAt
theorem gG {φ : ℝ → ℂ} (hφc : Continuous φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ t, ‖φ t‖ ≤ C / (1 + t ^ 2)) {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 3 / 2) :
    Integrable (fun t : ℝ => φ t * logDeriv Complex.Gammaℝ ((σ : ℂ) + t * I)) := by
  obtain ⟨Cψ, Xn, hψ⟩ := jX
  set a : ℝ := Real.log Real.pi / 2 with ha
  set b : ℝ := Cψ / 2 with hb
  have ha0 : 0 ≤ a := by rw [ha]; have := Real.log_nonneg (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ Real.pi); linarith
  have hb0 : 0 ≤ b := by rw [hb]; linarith
  set K : ℝ := C * (a + 5 * b) with hK
  have aaM : Integrable (fun t : ℝ => K * ((1 : ℝ) + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)) :=
    (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (by rw [Module.finrank_self]; norm_num)).const_mul K
  refine Integrable.mono' aaM
    (hφc.mul (iW (by linarith) hσ2)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have TD : 0 < σ := by linarith
  have hq : 0 < (1 + t ^ 2 : ℝ) := by positivity
  have hL : ‖logDeriv Complex.Gammaℝ ((σ : ℂ) + t * I)‖ ≤ (a + 5 * b) * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
    rw [gP (by simp; exact TD)]
    have hw1 : 1 / 4 ≤ (((σ : ℂ) + t * I) / 2).re := by simp; linarith
    have hw2 : (((σ : ℂ) + t * I) / 2).re ≤ 1 := by simp; linarith
    have Tm := hψ _ hw1 hw2
    have him : |(((σ : ℂ) + t * I) / 2).im| = |t| / 2 := by simp [abs_div]
    rw [him] at Tm
    have hlog : Real.log (2 + |t| / 2) ≤ 5 * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
      have hlt : Real.log (2 + |t| / 2) ≤ Real.log (2 + |t|) :=
        Real.log_le_log (x := 2 + |t| / 2) (y := 2 + |t|) (by positivity) (by linarith [abs_nonneg t])
      refine le_trans hlt ?_
      have := KX (abs_nonneg t)
      rwa [sq_abs] at this
    have hone : (1 : ℝ) ≤ (1 + t ^ 2) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by nlinarith) (by norm_num)
    calc ‖-((Real.log Real.pi : ℝ) : ℂ) / 2 + 1 / 2 * Complex.digamma (((σ : ℂ) + t * I) / 2)‖
        ≤ ‖-((Real.log Real.pi : ℝ) : ℂ) / 2‖ + ‖(1 / 2 : ℂ) * Complex.digamma (((σ : ℂ) + t * I) / 2)‖ :=
          norm_add_le _ _
      _ ≤ a + b * Real.log (2 + |t| / 2) := by
          apply add_le_add
          · rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith),
              show ‖(2:ℂ)‖ = 2 by norm_num, ha]
          · rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num, hb]
            nlinarith
      _ ≤ a * (1 + t ^ 2) ^ (1 / 4 : ℝ) + b * (5 * (1 + t ^ 2) ^ (1 / 4 : ℝ)) := by
          apply add_le_add
          · nlinarith
          · exact mul_le_mul_of_nonneg_left hlog hb0
      _ = (a + 5 * b) * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by ring
  rw [norm_mul]
  have hH := hC t
  have hpow : (C / (1 + t ^ 2)) * ((a + 5 * b) * (1 + t ^ 2) ^ (1 / 4 : ℝ))
      = K * ((1 : ℝ) + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) := by
    rw [Real.norm_eq_abs, sq_abs, hK]
    have e : (1 + t ^ 2 : ℝ) ^ (-(3 / 2 : ℝ) / 2) = (1 + t ^ 2) ^ (1 / 4 : ℝ) / (1 + t ^ 2) := by
      rw [show (-(3 / 2 : ℝ) / 2) = (1 / 4 : ℝ) - 1 by norm_num, Real.rpow_sub hq, Real.rpow_one]
    rw [e]
    field_simp
  calc ‖φ t‖ * ‖logDeriv Complex.Gammaℝ ((σ : ℂ) + t * I)‖
      ≤ (C / (1 + t ^ 2)) * ((a + 5 * b) * (1 + t ^ 2) ^ (1 / 4 : ℝ)) :=
        mul_le_mul hH hL (norm_nonneg _) (by positivity)
    _ = K * ((1 : ℝ) + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) := hpow
theorem iE {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (bD : HasCompactSupport k) {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 3 / 2) :
    Integrable (fun t : ℝ => aW k ((σ : ℂ) + t * I) * logDeriv Complex.Gammaℝ ((σ : ℂ) + t * I)) := by
  obtain ⟨C, hC0, hC⟩ := qI hk bD
  exact gG (gR hk bD σ) hC0
    (fun t => hC σ t (by linarith) (by linarith)) hσ1 hσ2
end RP
section Heights
theorem lH {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) {R : ℝ}
    (hζ : ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 → riemannZeta s ≠ 0) :
    ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 - c ≤ s.re → s.re ≤ c → completedRiemannZeta s ≠ 0 := by
  have aux : ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 →
      completedRiemannZeta s ≠ 0 := by
    intro s him h1 h2 h0
    rcases lt_or_ge s.re 1 with hlt | hge
    · have hnt := ((tJ (by linarith) hlt).1).mp h0
      exact hζ s him h1 h2 hnt.1
    · exact Zeta23.kB.cP hge h0
  intro s him h1 h2
  rcases le_or_gt (1 / 2 : ℝ) s.re with hre | hre
  · exact aux s him hre (by linarith)
  · 
    have e : completedRiemannZeta s = completedRiemannZeta (1 - s) :=
      (completedRiemannZeta_one_sub s).symm
    rw [e]
    apply aux (1 - s)
    · rcases him with h | h
      · right; simp [h]
      · left; simp [h]
    · simp; linarith
    · simp; linarith
end Heights
section RU
variable {k : ℝ → ℂ}
def tO (k : ℝ → ℂ) (c : ℝ) (t : ℝ) : ℂ :=
  (aW k ((c : ℂ) + t * I) + aW k (1 - c - t * I)) * logDeriv completedRiemannZeta ((c : ℂ) + t * I)
theorem DA (c t : ℝ) : (1 : ℂ) - c - t * I = ((1 - c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
  push_cast; ring
theorem nI {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (bD : HasCompactSupport k) (c : ℝ) :
    Continuous (fun t : ℝ => aW k (1 - c - t * I)) := by
  have : (fun t : ℝ => aW k (1 - c - t * I))
      = (fun t : ℝ => aW k (((1 - c : ℝ) : ℂ) + t * I)) ∘ fun t : ℝ => -t := by
    funext t; simp only [Function.comp_apply, DA]
  rw [this]; exact (gR hk bD (1 - c)).comp continuous_neg
theorem jT {c : ℝ} (hc1 : 1 < c) (t : ℝ) :
    logDeriv completedRiemannZeta ((c : ℂ) + t * I)
      = logDeriv Complex.Gammaℝ ((c : ℂ) + t * I) + logDeriv riemannZeta ((c : ℂ) + t * I) := by
  have hre : ((c : ℂ) + t * I).re = c := by simp
  refine jF _ ?_ ?_ (by rw [hre]; linarith)
  · intro h; have := congrArg Complex.re h; simp at this; linarith
  · exact riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; exact hc1)
theorem Gt (hk : ContDiff ℝ 2 k) (bD : HasCompactSupport k) {c : ℝ}
    (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) : Integrable (tO k c) := by
  obtain ⟨C, hC0, hC⟩ := qI hk bD
  set φ : ℝ → ℂ := fun t => aW k ((c : ℂ) + t * I) + aW k (1 - c - t * I) with hφ
  have hφc : Continuous φ := (gR hk bD c).add (nI hk bD c)
  have Xo : ∀ t, ‖φ t‖ ≤ (2 * C) / (1 + t ^ 2) := by
    intro t
    have h1 := hC c t (by linarith) (by linarith)
    have h2 := hC (1 - c) (-t) (by linarith) (by linarith)
    rw [← DA] at h2
    rw [neg_sq] at h2
    calc ‖φ t‖ ≤ ‖aW k ((c : ℂ) + t * I)‖ + ‖aW k (1 - c - t * I)‖ := norm_add_le _ _
      _ ≤ C / (1 + t ^ 2) + C / (1 + t ^ 2) := add_le_add h1 h2
      _ = (2 * C) / (1 + t ^ 2) := by ring
  have hΓ := gG hφc (by positivity) Xo
    (by linarith : (1:ℝ) / 2 ≤ c) hc2
  have hζ := gW hφc Xo hc1
  refine (hΓ.add hζ).congr (Eventually.of_forall fun t => ?_)
  simp only [tO, hφ, jT hc1 t, Pi.add_apply]
  ring
theorem NC (hk : ContDiff ℝ 2 k) (bD : HasCompactSupport k) {c : ℝ}
    (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) (R : ℝ) :
    ju (fun s => aW k s * logDeriv completedRiemannZeta s) c (-R) R
      - ju (fun s => aW k s * logDeriv completedRiemannZeta s) (1 - c) (-R) R
      = I • ∫ t in (-R)..R, tO k c t := by
  set L := logDeriv completedRiemannZeta with hL
  have hLc : Continuous (fun t : ℝ => L ((c : ℂ) + t * I)) := by
    have : (fun t : ℝ => L ((c:ℂ) + t * I)) = fun t : ℝ => logDeriv Complex.Gammaℝ ((c : ℂ) + t * I)
        + logDeriv riemannZeta ((c : ℂ) + t * I) := funext (jT hc1)
    rw [this]
    exact (iW (by linarith) hc2).add (jM hc1)
  have hHc := gR hk bD c
  have hH2 : Continuous (fun t : ℝ => aW k (1 - c - t * I)) := nI hk bD c
  have hleft : ∀ y : ℝ, aW k (((1 - c : ℝ) : ℂ) + y * I) * L (((1 - c : ℝ) : ℂ) + y * I)
      = -(aW k (1 - c - ((-y : ℝ) : ℂ) * I) * L ((c : ℂ) + ((-y : ℝ) : ℂ) * I)) := by
    intro y
    have hs : ((1 - c : ℝ) : ℂ) + y * I = 1 - ((c : ℂ) + ((-y : ℝ) : ℂ) * I) := by push_cast; ring
    have h0 : (c : ℂ) + ((-y:ℝ):ℂ) * I ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have h1 : (c : ℂ) + ((-y:ℝ):ℂ) * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [hs, hL, jB _ h0 h1]
    have : (1:ℂ) - ((c : ℂ) + ((-y:ℝ):ℂ) * I) = 1 - c - ((-y : ℝ) : ℂ) * I := by ring
    rw [this]; ring
  have hI1 : IntervalIntegrable (fun t : ℝ => aW k ((c : ℂ) + t * I) * L ((c : ℂ) + t * I))
      volume (-R) R := (hHc.mul hLc).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun t : ℝ => aW k (1 - c - t * I) * L ((c : ℂ) + t * I))
      volume (-R) R := (hH2.mul hLc).intervalIntegrable _ _
  have Zp : (∫ y in (-R)..R, aW k (((1 - c : ℝ) : ℂ) + y * I) * L (((1 - c : ℝ) : ℂ) + y * I))
      = -∫ t in (-R)..R, aW k (1 - c - t * I) * L ((c : ℂ) + t * I) := by
    simp_rw [hleft]
    rw [intervalIntegral.integral_neg]
    have h := intervalIntegral.integral_comp_neg (a := -R) (b := R)
      (fun t : ℝ => aW k (1 - c - t * I) * L ((c : ℂ) + t * I))
    simp only [neg_neg] at h
    rw [← h]
  dsimp only [ju]
  rw [Zp, ← smul_sub, sub_neg_eq_add, ← intervalIntegral.integral_add hI1 hI2]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [tO]
  ring
theorem xZ (hk : ContDiff ℝ 2 k) (bD : HasCompactSupport k) {c : ℝ}
    (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) {R : ℕ → ℝ} (hR : ∀ j : ℕ, (j : ℝ) ≤ R j) :
    Tendsto (fun j : ℕ => ∫ t in (-R j)..R j, tO k c t) atTop (𝓝 (∫ t, tO k c t)) := by
  have UJ : Tendsto R atTop atTop :=
    tendsto_atTop_mono hR tendsto_natCast_atTop_atTop
  exact intervalIntegral_tendsto_integral (Gt hk bD hc1 hc2)
    (tendsto_neg_atTop_atBot.comp UJ) UJ
end RU
end cw
end Zeta23
end
end

-- Zeta23.cw.Horizontal
section
noncomputable section
namespace Zeta23
namespace cw
open Complex Topology Filter Set MeasureTheory
theorem Ew {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (bD : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) {Cg : ℝ} (hCg : 0 < Cg) {R : ℕ → ℝ}
    (hR : ∀ j : ℕ, (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8 ∧
      ∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → 1/2 ≤ s.re → s.re ≤ 2 →
        riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤ Cg * (Real.log ((j : ℝ) + 10)) ^ 2) :
    Tendsto (fun j : ℕ => iw (fun s => aW k s * logDeriv completedRiemannZeta s)
        (1 - c) c (R j)) atTop (𝓝 0)
    ∧ Tendsto (fun j : ℕ => iw (fun s => aW k s * logDeriv completedRiemannZeta s)
        (1 - c) c (-(R j))) atTop (𝓝 0) := by
  obtain ⟨CH, acW, hH⟩ := qI hk bD
  obtain ⟨Cψ, Xn, hψ⟩ := jX
  set Lg : ℕ → ℝ := fun j => Real.log ((j : ℝ) + 10) with RV
  have Qj : ∀ j : ℕ, 1 ≤ Lg j := fun j => by
    rw [RV, ← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have := Real.exp_one_lt_d9
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have Jm : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  set K : ℝ := Real.log Real.pi / 2 + Cψ + Cg with Zq
  have hK0 : 0 < K := by positivity
  have hright : ∀ (j : ℕ) (s : ℂ), (s.im = R j ∨ s.im = -R j) → 1/2 ≤ s.re → s.re ≤ 2 →
      ‖logDeriv completedRiemannZeta s‖ ≤ K * (Lg j) ^ 2 := by
    intro j s MW Dt Dm
    obtain ⟨hR1, hR2, hRs⟩ := hR j
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
    have Qr : 0 ≤ R j := by linarith
    have Qt : 7 ≤ |s.im| := by
      rcases MW with h | h
      · rw [h, abs_of_nonneg Qr]; linarith
      · rw [h, abs_neg, abs_of_nonneg Qr]; linarith
    have hs0 : s ≠ 0 := fun h => by rw [h] at Qt; norm_num at Qt
    have hs1 : s ≠ 1 := fun h => by rw [h] at Qt; norm_num at Qt
    obtain ⟨hζ, acX⟩ := hRs s MW Dt Dm
    have Xp : 0 < s.re := by linarith
    rw [jF s hs1 hζ Xp, gP Xp]
    have hψs : ‖Complex.digamma (s / 2)‖ ≤ Cψ * Real.log (2 + |(s / 2).im|) :=
      hψ (s / 2) (by simp; linarith) (by simp; linarith)
    have zX : Real.log (2 + |(s / 2).im|) ≤ Lg j := by
      have acY : |s.im| ≤ (j : ℝ) + 8 := by
        rcases MW with h | h
        · rw [h, abs_of_nonneg Qr]; exact hR2
        · rw [h, abs_neg, abs_of_nonneg Qr]; exact hR2
      have e : |(s / 2).im| = |s.im| / 2 := by simp [abs_div]
      rw [e, RV]
      exact Real.log_le_log (by positivity) (by linarith)
    have aaN : Lg j ≤ Lg j ^ 2 := by nlinarith [Qj j]
    calc ‖-((Real.log Real.pi : ℝ) : ℂ) / 2 + 1 / 2 * Complex.digamma (s / 2) + logDeriv riemannZeta s‖
        ≤ ‖-((Real.log Real.pi : ℝ) : ℂ) / 2‖ + ‖(1 / 2 : ℂ) * Complex.digamma (s / 2)‖
          + ‖logDeriv riemannZeta s‖ := norm_add₃_le
      _ = Real.log Real.pi / 2 + 1 / 2 * ‖Complex.digamma (s / 2)‖ + ‖logDeriv riemannZeta s‖ := by
          rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Jm, norm_mul]
          norm_num
      _ ≤ Real.log Real.pi / 2 * Lg j ^ 2 + Cψ * Lg j ^ 2 + Cg * Lg j ^ 2 := by
          have h1 : Real.log Real.pi / 2 ≤ Real.log Real.pi / 2 * Lg j ^ 2 := by
            have : (1:ℝ) ≤ Lg j ^ 2 := by nlinarith [Qj j]
            nlinarith
          have h2 : 1 / 2 * ‖Complex.digamma (s / 2)‖ ≤ Cψ * Lg j ^ 2 := by
            have := hψs.trans (mul_le_mul_of_nonneg_left (zX.trans aaN) Xn.le)
            nlinarith [norm_nonneg (Complex.digamma (s / 2))]
          linarith
      _ = K * Lg j ^ 2 := by rw [Zq]; ring
  have hall : ∀ (j : ℕ) (x y : ℝ), (y = R j ∨ y = -R j) → 1 - c ≤ x → x ≤ c →
      ‖logDeriv completedRiemannZeta ((x : ℂ) + y * I)‖ ≤ K * (Lg j) ^ 2 := by
    intro j x y hy hx1 hx2
    rcases le_or_gt (1/2 : ℝ) x with hx | hx
    · exact hright j _ (by rcases hy with h | h <;> simp [h]) (by simpa using hx)
        (by simp; linarith)
    · 
      set s' : ℂ := ((1 - x : ℝ) : ℂ) + (-y) * I with ND
      have TI : s'.im = -y := by simp [ND]
      have Xq : s'.re = 1 - x := by simp [ND]
      have hy0 : y ≠ 0 := by
        obtain ⟨hR1, -, -⟩ := hR j
        have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
        have UK : 0 < R j := by linarith
        rcases hy with h | h
        · rw [h]; exact UK.ne'
        · rw [h]; exact (neg_lt_zero.mpr UK).ne
      have aaO : s' ≠ 0 := fun h => hy0 (by
        have Xr := congrArg Complex.im h
        rw [TI] at Xr; simpa using Xr)
      have aaP : s' ≠ 1 := fun h => hy0 (by
        have Xt := congrArg Complex.im h
        rw [TI] at Xt; simpa using Xt)
      have e : ((x : ℂ) + y * I) = 1 - s' := by
        simp only [ND]; push_cast; ring
      rw [e, jB s' aaO aaP, norm_neg]
      refine hright j s' ?_ (by rw [Xq]; linarith) (by rw [Xq]; linarith)
      rw [TI]
      rcases hy with h | h
      · right; rw [h]
      · left; rw [h, neg_neg]
  have hint : ∀ (j : ℕ) (y : ℝ), (y = R j ∨ y = -R j) →
      ‖iw (fun s => aW k s * logDeriv completedRiemannZeta s) (1 - c) c y‖
        ≤ CH / (1 + (R j) ^ 2) * (K * Lg j ^ 2) * |c - (1 - c)| := by
    intro j y hy
    unfold iw
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hy2 : y ^ 2 = (R j) ^ 2 := by rcases hy with h | h <;> simp [h]
    dsimp only
    rw [norm_mul, ← hy2]
    exact mul_le_mul (hH x y (by linarith [hx.1]) (by linarith [hx.2]))
      (hall j x y hy hx.1.le hx.2) (norm_nonneg _) (by positivity)
  set b : ℕ → ℝ := fun j => CH / (1 + (R j) ^ 2) * (K * Lg j ^ 2) * |c - (1 - c)| with Mh
  have RW : ∀ j : ℕ, Lg j ^ 2 ≤ 4 * ((j : ℝ) + 10) := fun j => by
    have hy0 : (0 : ℝ) ≤ (j : ℝ) + 10 := by positivity
    have h := Real.log_le_rpow_div hy0 (by norm_num : (0:ℝ) < 1/2)
    have hsq : (((j : ℝ) + 10) ^ (1/2 : ℝ)) ^ 2 = (j : ℝ) + 10 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
    have h0 : 0 ≤ Lg j := (zero_le_one.trans (Qj j))
    calc Lg j ^ 2 ≤ (((j : ℝ) + 10) ^ (1/2 : ℝ) / (1/2)) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = 4 * ((j : ℝ) + 10) := by rw [div_pow, hsq]; ring
  have hb_le : ∀ j : ℕ, b j ≤ (8 * CH * K * |c - (1 - c)|) / ((j : ℝ) + 7) := fun j => by
    obtain ⟨hR1, hR2, -⟩ := hR j
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h1 : Lg j ^ 2 / (1 + R j ^ 2) ≤ 8 / ((j : ℝ) + 7) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hR7 : ((j : ℝ) + 7) ^ 2 ≤ R j ^ 2 := pow_le_pow_left₀ (by positivity) hR1 2
      nlinarith [RW j, hR7, mul_le_mul_of_nonneg_right (RW j) (show (0:ℝ) ≤ (j:ℝ) + 7 by positivity),
        sq_nonneg ((j:ℝ) + 7)]
    have e : b j = CH * K * |c - (1 - c)| * (Lg j ^ 2 / (1 + R j ^ 2)) := by
      rw [Mh]; ring
    rw [e]
    calc CH * K * |c - (1 - c)| * (Lg j ^ 2 / (1 + R j ^ 2))
        ≤ CH * K * |c - (1 - c)| * (8 / ((j : ℝ) + 7)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 8 * CH * K * |c - (1 - c)| / ((j : ℝ) + 7) := by ring
  have hb0 : ∀ j, 0 ≤ b j := fun j => by rw [Mh]; positivity
  have hb : Tendsto b atTop (𝓝 0) := by
    have hlim : Tendsto (fun j : ℕ => (8 * CH * K * |c - (1 - c)|) / ((j : ℝ) + 7)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    exact squeeze_zero hb0 hb_le hlim
  exact ⟨squeeze_zero_norm (fun j => hint j (R j) (Or.inl rfl)) hb,
    squeeze_zero_norm (fun j => hint j (-(R j)) (Or.inr rfl)) hb⟩
end cw
end Zeta23
end
end

-- Zeta23.cw.Xv
section
noncomputable section
namespace Zeta23
namespace cw
open Complex Topology Filter Set
theorem KY (hs : gI) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (bD : HasCompactSupport k)
    {R : ℕ → ℝ} (hR : ∀ j : ℕ, (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8)
    {Z : ℕ → Finset ℂ}
    (hZ : ∀ j : ℕ, ((Z j : Set ℂ) = {ρ : ℂ | aO ρ ∧ -R j < ρ.im ∧ ρ.im < R j})) :
    Tendsto (fun j : ℕ => ∑ ρ ∈ Z j, (bY ρ : ℂ) * aW k ρ) atTop
      (𝓝 (∑' ρ : (bT hs).carrier, ((bT hs).mult ρ : ℂ) * aW k ρ)) := by
  classical
  set g : (bT hs).carrier → ℂ := fun ρ => ((bT hs).mult ρ : ℂ) * aW k ρ with hg
  have hsum : Summable g := oP hs hk bD
  have Qv : ∀ j ρ, ρ ∈ Z j ↔ aO ρ ∧ -R j < ρ.im ∧ ρ.im < R j := by
    intro j ρ
    rw [← Finset.mem_coe, hZ j]
    rfl
  set s : ℕ → Finset (bT hs).carrier :=
    fun j => (Z j).subtype (· ∈ (bT hs).carrier) with acE
  have KD : ∀ j, ∑ x ∈ s j, g x = ∑ ρ ∈ Z j, (bY ρ : ℂ) * aW k ρ := by
    intro j
    have h1 := Finset.sum_subtype_eq_sum_filter (s := Z j)
      (p := (· ∈ (bT hs).carrier)) (fun ρ : ℂ => (bY ρ : ℂ) * aW k ρ)
    have h2 : (Z j).filter (· ∈ (bT hs).carrier) = Z j := by
      apply Finset.filter_true_of_mem
      intro ρ hρ
      exact ((Qv j ρ).mp hρ).1
    rw [h2] at h1
    rw [← h1]
    rfl
  have Xw : ∀ i j : ℕ, i ≤ j → R i ≤ R j := by
    intro i j hij
    rcases hij.eq_or_lt with h | h
    · rw [h]
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      linarith [(hR i).2, (hR j).1]
  have hmono : Monotone s := by
    intro i j hij x hx
    rw [Finset.mem_subtype, Qv] at hx ⊢
    obtain ⟨h1, h2, h3⟩ := hx
    have := Xw i j hij
    exact ⟨h1, by linarith, by linarith⟩
  have hexh : ∀ b : Finset (bT hs).carrier, ∃ j, b ≤ s j := by
    intro b
    set M : ℝ := ∑ x ∈ b, |((x : ℂ)).im| with hM
    have aaQ : ∀ x ∈ b, |((x : ℂ)).im| ≤ M := fun x hx =>
      Finset.single_le_sum (f := fun x : (bT hs).carrier => |((x : ℂ)).im|)
        (fun _ _ => abs_nonneg _) hx
    obtain ⟨j, hj⟩ := exists_nat_gt M
    refine ⟨j, fun x hx => ?_⟩
    rw [Finset.mem_subtype, Qv]
    have hx0 : aO (x : ℂ) := x.2
    have habs := abs_le.mp (aaQ x hx)
    have hRj := (hR j).1
    exact ⟨hx0, by linarith [habs.1], by linarith [habs.2]⟩
  have VA : Tendsto s atTop atTop := tendsto_atTop_atTop_of_monotone hmono hexh
  have hT : Tendsto (fun S : Finset (bT hs).carrier => ∑ x ∈ S, g x) atTop
      (𝓝 (∑' x, g x)) := by
    exact hsum.hasSum
  have := hT.comp VA
  refine this.congr (fun j => ?_)
  simp only [Function.comp_apply, KD]
end cw
end Zeta23
end
end

-- Zeta23.cw.TJ
section
noncomputable section
namespace Zeta23
namespace cw
open Complex Topology Filter Set MeasureTheory
theorem NR (c R : ℝ) :
    ((((1 - c : ℝ) : ℂ) - R * I).re = 1 - c) ∧ ((((1 - c : ℝ) : ℂ) - R * I).im = -R) ∧
    ((((c : ℝ) : ℂ) + R * I).re = c) ∧ ((((c : ℝ) : ℂ) + R * I).im = R) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
theorem DB (X : ℂ) :
    (1 / (2 * Real.pi * I) : ℂ) * (I * X) = (1 / (2 * Real.pi) : ℂ) * X := by
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  field_simp
theorem DE (hs : gI) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (bD : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (aW k ((c:ℂ) + t * I) + aW k (1 - c - t * I))
        * logDeriv completedRiemannZeta ((c:ℂ) + t * I)
      = (∑' ρ : (bT hs).carrier, ((bT hs).mult ρ : ℂ) * aW k ρ)
        - aW k 0 - aW k 1 := by
  obtain ⟨Cg, hCg, R, hR⟩ := Nv
  set f : ℂ → ℂ := fun s => aW k s * logDeriv completedRiemannZeta s with hf
  have Qb : ∀ j : ℕ, ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ : ℂ | aO ρ ∧ -R j < ρ.im ∧ ρ.im < R j}) ∧
      bF f (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I)
        = (∑ ρ ∈ Z, (bY ρ : ℂ) * aW k ρ) - aW k 0 - aW k 1 := by
    intro j
    obtain ⟨h1, h2, h3⟩ := hR j
    exact Dz hk bD hc1 hc2 (R := R j) (by linarith)
      (lH hc1 hc2 (fun s him hr1 hr2 => (h3 s him hr1 hr2).1))
  choose Z hZ hE using Qb
  obtain ⟨Zr, Zt⟩ := Ew hk bD hc1 hc2 hCg hR
  have Zu := KY hs hk bD (R := R) (fun j => ⟨(hR j).1, (hR j).2.1⟩) hZ
  have hV := xZ hk bD hc1 hc2 (R := R) (fun j => by linarith [(hR j).1])
  have hdec : ∀ j : ℕ, bF f (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I)
      = (1 / (2 * Real.pi * I) : ℂ) * (iw f (1 - c) c (-(R j)) - iw f (1 - c) c (R j))
        + (1 / (2 * Real.pi) : ℂ) * ∫ t in (-R j)..R j, tO k c t := by
    intro j
    obtain ⟨e1, e2, e3, e4⟩ := NR c (R j)
    rw [bF, aY, smul_eq_mul, e1, e2, e3, e4]
    have hv := NC hk bD hc1 hc2 (R j)
    rw [hf]
    rw [show ∀ A B V₁ V₂ : ℂ, A - B + V₁ - V₂ = (A - B) + (V₁ - V₂) from fun _ _ _ _ => by ring, hv,
      smul_eq_mul, mul_add, DB]
  have hL : Tendsto (fun j : ℕ => bF f (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I))
      atTop (𝓝 ((1 / (2 * Real.pi) : ℂ) * ∫ t, tO k c t)) := by
    have h := ((Zt.sub Zr).const_mul (1 / (2 * Real.pi * I) : ℂ)).add
      (hV.const_mul (1 / (2 * Real.pi) : ℂ))
    simp only [sub_zero, mul_zero, zero_add] at h
    refine h.congr fun j => ?_
    rw [hdec j]
  have hRt : Tendsto (fun j : ℕ => (∑ ρ ∈ Z j, (bY ρ : ℂ) * aW k ρ) - aW k 0 - aW k 1)
      atTop (𝓝 ((∑' ρ : (bT hs).carrier, ((bT hs).mult ρ : ℂ) * aW k ρ)
        - aW k 0 - aW k 1)) :=
    (Zu.sub_const _).sub_const _
  have hL' : Tendsto (fun j : ℕ => (∑ ρ ∈ Z j, (bY ρ : ℂ) * aW k ρ) - aW k 0 - aW k 1)
      atTop (𝓝 ((1 / (2 * Real.pi) : ℂ) * ∫ t, tO k c t)) :=
    hL.congr fun j => hE j
  have := tendsto_nhds_unique hL' hRt
  exact this
end cw
end Zeta23
end
end

-- Zeta23.cw.Main
section
noncomputable section
namespace Zeta23
namespace cw
open Complex MeasureTheory
open scoped ArithmeticFunction
theorem Qw (k : ℝ → ℂ) (c t : ℝ) :
    aW k (1 - c - t * I) = aW (fun u => k (-u)) ((c:ℂ) + t * I) := by
  rw [Nk]
  unfold aW tilt aD
  conv_rhs => rw [← integral_neg_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [neg_neg]
  have harg : I * ((1 - (c:ℂ) - t * I - 1/2) / I) * u
      = (((- ((c - 1/2) * u) : ℝ)) : ℂ) + I * ↑t * ↑(-u : ℝ) := by
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    field_simp
    push_cast
    ring
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp]
  push_cast
  ring
theorem Om (hs : gI) : Zeta23.EF.Rk (bT hs) := by
  intro k hk bD
  refine ⟨oP hs hk bD, ?_⟩
  have KZ : (1:ℝ) < 5/4 := by norm_num
  have Qy : (5/4:ℝ) ≤ 3/2 := by norm_num
  have NU : ContDiff ℝ 2 (fun u : ℝ => k (-u)) := hk.comp contDiff_neg
  have NV : HasCompactSupport (fun u : ℝ => k (-u)) := by
    have := bD.comp_homeomorph (Homeomorph.neg ℝ)
    exact this
  have Zv := DE hs hk bD KZ Qy
  have hsne : ∀ t : ℝ, ((5/4:ℝ) : ℂ) + t * I ≠ 0 ∧ ((5/4:ℝ) : ℂ) + t * I ≠ 1
      ∧ riemannZeta (((5/4:ℝ) : ℂ) + t * I) ≠ 0 ∧ 0 < ((((5/4:ℝ) : ℂ)) + t * I).re := by
    intro t
    have hre : ((((5/4:ℝ) : ℂ)) + t * I).re = 5/4 := by simp
    refine ⟨fun h => ?_, fun h => ?_, riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; norm_num), by
      rw [hre]; norm_num⟩
    · rw [h] at hre
      simp at hre
      linarith
    · rw [h] at hre
      simp at hre
      linarith
  have hsplit : ∀ t : ℝ, logDeriv completedRiemannZeta (((5/4:ℝ):ℂ) + t * I)
      = logDeriv Complex.Gammaℝ (((5/4:ℝ):ℂ) + t * I)
        + logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I) := by
    intro t
    obtain ⟨h0, h1, hζ, hpos⟩ := hsne t
    exact jF _ h1 hζ hpos
  have Qz : ∀ t : ℝ, aW k (1 - (5/4:ℝ) - t * I)
      = aW (fun u => k (-u)) (((5/4:ℝ):ℂ) + t * I) := fun t => Qw k (5/4) t
  have UL : Integrable (fun t : ℝ => aW k (((5/4:ℝ):ℂ) + t * I)
      * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I)) :=
    je hk bD KZ Qy
  have UN : Integrable (fun t : ℝ => aW k (1 - (5/4:ℝ) - t * I)
      * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I)) := by
    have heq : (fun t : ℝ => aW k (1 - (5/4:ℝ) - t * I)
        * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I))
        = fun t : ℝ => aW (fun u => k (-u)) (((5/4:ℝ):ℂ) + t * I)
          * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I) := by
      funext t
      rw [Qz t]
    rw [heq]
    exact je NU NV KZ Qy
  have Xx : Integrable (fun t : ℝ => (aW k (((5/4:ℝ):ℂ) + t * I)
      + aW k (1 - (5/4:ℝ) - t * I)) * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I)) := by
    refine (UL.add UN).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply]
    ring
  have VE : Integrable (fun t : ℝ => aW k (((5/4:ℝ):ℂ) + t * I)
      * logDeriv Complex.Gammaℝ (((5/4:ℝ):ℂ) + t * I)) :=
    iE hk bD (by norm_num) (by norm_num)
  have VF : Integrable (fun t : ℝ => aW k (1 - (5/4:ℝ) - t * I)
      * logDeriv Complex.Gammaℝ (((5/4:ℝ):ℂ) + t * I)) := by
    have heq : (fun t : ℝ => aW k (1 - (5/4:ℝ) - t * I)
        * logDeriv Complex.Gammaℝ (((5/4:ℝ):ℂ) + t * I))
        = fun t : ℝ => aW (fun u => k (-u)) (((5/4:ℝ):ℂ) + t * I)
          * logDeriv Complex.Gammaℝ (((5/4:ℝ):ℂ) + t * I) := by
      funext t
      rw [Qz t]
    rw [heq]
    exact iE NU NV (σ := 5/4) (by norm_num) (by norm_num)
  have Xy : Integrable (fun t : ℝ => (aW k (((5/4:ℝ):ℂ) + t * I)
      + aW k (1 - (5/4:ℝ) - t * I)) * logDeriv Complex.Gammaℝ (((5/4:ℝ):ℂ) + t * I)) := by
    refine (VE.add VF).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply]
    ring
  have RY : (∫ t : ℝ, (aW k (((5/4:ℝ):ℂ) + t * I) + aW k (1 - (5/4:ℝ) - t * I))
        * logDeriv completedRiemannZeta (((5/4:ℝ):ℂ) + t * I))
      = (∫ t : ℝ, (aW k (((5/4:ℝ):ℂ) + t * I) + aW k (1 - (5/4:ℝ) - t * I))
          * logDeriv Complex.Gammaℝ (((5/4:ℝ):ℂ) + t * I))
        + ∫ t : ℝ, (aW k (((5/4:ℝ):ℂ) + t * I) + aW k (1 - (5/4:ℝ) - t * I))
          * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I) := by
    rw [← integral_add Xy Xx]
    congr 1
    funext t
    show (aW k (((5/4:ℝ):ℂ) + t * I) + aW k (1 - (5/4:ℝ) - t * I))
      * logDeriv completedRiemannZeta (((5/4:ℝ):ℂ) + t * I) = _
    rw [hsplit t]
    ring
  have hζ1 : (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, aW k (((5/4:ℝ):ℂ) + t * I)
      * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I)
      = -∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
    have h := wP hk bD KZ
    have h2 : (∫ t : ℝ, aW k (((5/4:ℝ):ℂ) + t * I)
        * (-logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I)))
        = -∫ t : ℝ, aW k (((5/4:ℝ):ℂ) + t * I)
          * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I) := by
      rw [← integral_neg]
      congr 1
      funext t
      ring
    rw [h2] at h
    linear_combination -h
  have aaR : (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, aW k (1 - (5/4:ℝ) - t * I)
      * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I)
      = -∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (-Real.log n) := by
    have h := wP NU NV KZ
    have h2 : (∫ t : ℝ, aW (fun u => k (-u)) (((5/4:ℝ):ℂ) + t * I)
        * (-logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I)))
        = -∫ t : ℝ, aW k (1 - (5/4:ℝ) - t * I)
          * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I) := by
      rw [← integral_neg]
      congr 1
      funext t
      rw [Qz t]
      ring
    rw [h2] at h
    have h3 : (∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (fun u => k (-u)) (Real.log n))
        = ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (-Real.log n) := rfl
    rw [h3] at h
    linear_combination -h
  have VG : (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (aW k (((5/4:ℝ):ℂ) + t * I)
      + aW k (1 - (5/4:ℝ) - t * I)) * logDeriv Complex.Gammaℝ (((5/4:ℝ):ℂ) + t * I)
      = (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, aD k r * ((Zeta23.EF.dL r : ℝ) : ℂ) := by
    congr 1
    rw [Gh hk bD KZ Qy]
    congr 1
    funext t
    rw [KQ t]
    congr 2
    unfold Zeta23.EF.dL
    congr 3
    ring
  have Xz : aW k 0 = aD k (I / 2) := by
    unfold aW
    congr 1
    rw [div_eq_iff Complex.I_ne_zero, div_mul_eq_mul_div, Complex.I_mul_I]
    norm_num
  have XB : aW k 1 = aD k (-I / 2) := by
    unfold aW
    congr 1
    rw [div_eq_iff Complex.I_ne_zero]
    rw [show (-I / 2) * I = -(I * I) / 2 by ring, Complex.I_mul_I]
    norm_num
  obtain ⟨B₁, hB₁⟩ := Zeta23.EF.bZ bD
  have Bc : ∀ (g : ℝ → ℂ), (∀ u, g u ≠ 0 → |u| ≤ max B₁ 0) →
      Summable (fun n : ℕ => ((Λ n / Real.sqrt n : ℝ) : ℂ) * g (Real.log n)) := by
    intro g hg
    refine summable_of_hasFiniteSupport ?_
    have hsub : Function.support (fun n : ℕ => ((Λ n / Real.sqrt n : ℝ) : ℂ) * g (Real.log n))
        ⊆ Set.Iic ⌈Real.exp (max B₁ 0)⌉₊ := by
      intro n hn
      rw [Function.mem_support] at hn
      have hgne : g (Real.log n) ≠ 0 := by
        intro h
        rw [h, mul_zero] at hn
        exact hn rfl
      have hlog := hg _ hgne
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp at hn
      have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have : (n:ℝ) ≤ Real.exp (max B₁ 0) := by
        have h2 : Real.log n ≤ max B₁ 0 := (le_abs_self _).trans hlog
        calc (n:ℝ) = Real.exp (Real.log n) := (Real.exp_log (by linarith)).symm
          _ ≤ Real.exp (max B₁ 0) := Real.exp_le_exp.mpr h2
      rw [Set.mem_Iic]
      exact_mod_cast this.trans (Nat.le_ceil _)
    exact (Set.finite_Iic _).subset hsub
  have QC : Summable (fun n : ℕ => ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n)) :=
    Bc k (fun u hu => (hB₁ u hu).trans (le_max_left _ _))
  have QD : Summable (fun n : ℕ => ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (-Real.log n)) := by
    refine Bc (fun u => k (-u)) (fun u hu => ?_)
    have h2 := hB₁ (-u) hu
    rw [abs_neg] at h2
    exact h2.trans (le_max_left _ _)
  have XC : (∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n))
      + (∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (-Real.log n))
      = ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) := by
    rw [← Summable.tsum_add QC QD]
    refine tsum_congr fun n => ?_
    ring
  have TK : ∀ ρ : (bT hs).carrier,
      aD k (aF (ρ : ℂ)) = aW k (ρ : ℂ) := fun ρ => rfl
  rw [Zeta23.EF.nP]
  calc ∑' ρ : (bT hs).carrier, ((bT hs).mult ρ : ℂ) * aD k (aF (ρ:ℂ))
      = ∑' ρ : (bT hs).carrier, ((bT hs).mult ρ : ℂ) * aW k (ρ:ℂ) := by
        refine tsum_congr fun ρ => by rw [TK ρ]
    _ = (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (aW k (((5/4:ℝ):ℂ) + t * I)
          + aW k (1 - (5/4:ℝ) - t * I)) * logDeriv completedRiemannZeta (((5/4:ℝ):ℂ) + t * I))
        + aW k 0 + aW k 1 := by
        rw [Zv]
        ring
    _ = aD k (I / 2) + aD k (-I / 2)
        - (∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)))
        + (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, aD k r * ((Zeta23.EF.dL r : ℝ) : ℂ) := by
        rw [RY, mul_add, VG, Xz, XB]
        have VJ : (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (aW k (((5/4:ℝ):ℂ) + t * I)
            + aW k (1 - (5/4:ℝ) - t * I)) * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I))
            = -∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) := by
          have hsum2 : (∫ t : ℝ, (aW k (((5/4:ℝ):ℂ) + t * I) + aW k (1 - (5/4:ℝ) - t * I))
              * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I))
              = (∫ t : ℝ, aW k (((5/4:ℝ):ℂ) + t * I)
                  * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I))
                + ∫ t : ℝ, aW k (1 - (5/4:ℝ) - t * I)
                  * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I) := by
            rw [← integral_add UL UN]
            congr 1
            funext t
            ring
          rw [hsum2, mul_add, hζ1, aaR, ← XC]
          ring
        rw [VJ]
        ring
theorem ow : Zeta23.EF.Rk aE := Om Fw
end cw
end Zeta23
end
end

-- aR.LG
section
open Complex MeasureTheory Set
namespace aR.LG
end aR.LG
end

-- aR.vV
section
open Complex
noncomputable section
namespace aR.vV
lemma qO {s : ℂ} (hre : s.re ≤ 0) (hz : riemannZeta s = 0) :
    ∃ n : ℕ, s = -2 * (n + 1) := by
  have hs0 : s ≠ 0 := by
    rintro rfl; rw [riemannZeta_zero] at hz; norm_num at hz
  set w : ℂ := 1 - s with hw
  have Dx : 1 ≤ w.re := by simp [hw]; linarith
  have hwn : ∀ n : ℕ, w ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hw1 : w ≠ 1 := by
    intro h; apply hs0; rw [hw] at h; linear_combination -h
  have hfe := riemannZeta_one_sub hwn hw1
  rw [show 1 - w = s by simp [hw], hz] at hfe
  have h2π : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
    intro h
    exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) (cpow_eq_zero_iff _ _ |>.mp h).1
  have hΓ : Gamma w ≠ 0 := Gamma_ne_zero hwn
  have hζ : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re Dx
  have hcos : cos (Real.pi * w / 2) = 0 := by
    by_contra hc
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h2π) hΓ) hc) hζ) hfe.symm
  obtain ⟨k, hk⟩ := cos_eq_zero_iff.mp hcos
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hwk : w = 2 * k + 1 := by
    have := hk; field_simp at this; exact this
  have hsk : s = -2 * k := by rw [hw] at hwk; linear_combination -hwk
  have aaS : (k : ℝ) ≥ 1 := by
    have h1 := congrArg Complex.re hsk
    simp at h1
    have hk0 : k ≠ 0 := by rintro rfl; apply hs0; simpa using hsk
    have acZ : (0 : ℤ) ≤ k := by
      by_contra hneg; push Not at hneg
      have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
      linarith
    exact_mod_cast (show (1 : ℤ) ≤ k by omega)
  refine ⟨(k - 1).toNat, ?_⟩
  have hk1 : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by
    have : (1 : ℤ) ≤ k := by exact_mod_cast aaS
    omega)
  have : ((k - 1).toNat : ℂ) = (k : ℂ) - 1 := by exact_mod_cast hk1
  rw [this, hsk]; ring
theorem wJ (s : ℂ) :
    riemannZeta s = 0 ↔
      (∃ n : ℕ, s = -2 * (n + 1)) ∨ (0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0) := by
  constructor
  · intro hz
    rcases le_or_gt s.re 0 with h0 | h0
    · exact Or.inl (qO h0 hz)
    rcases lt_or_ge s.re 1 with h1 | h1
    · exact Or.inr ⟨h0, h1, hz⟩
    · exact absurd hz (riemannZeta_ne_zero_of_one_le_re h1)
  · rintro (⟨n, rfl⟩ | ⟨_, _, hz⟩)
    · exact riemannZeta_neg_two_mul_nat_add_one n
    · exact hz
end aR.vV
end
end

-- aR.VK
section
noncomputable section
open Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder
namespace aR.Weil
open Zeta23 Zeta23.EF
def bU (k : ℝ → ℂ) : ℂ := nP k
def dK (f : ℝ → ℂ) : ℝ → ℂ := gO f f
lemma BW {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ContDiff ℝ 2 (dK f) :=
  jN hf hf.continuous hfc
lemma qC {f : ℝ → ℂ} (hfc : HasCompactSupport f) :
    HasCompactSupport (dK f) :=
  fD hfc hfc
abbrev Z : aV := aE
lemma Fh {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (ρ : ℂ) :
    Z.dD f g ρ = (Z.mult ρ : ℂ) * aD (gO f g) (aF ρ) := by
  rw [aV.dD, vk hf hg hfc hgc, mul_assoc]
lemma iJ {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Summable (fun ρ : Z.carrier => Z.dD f g ρ) := by
  have h := (cw.ow (gO f g) (jN hf hg.continuous hfc)
    (fD hfc hgc)).1
  refine h.congr fun ρ => ?_
  rw [Fh hf.continuous hg.continuous hfc hgc]
theorem kP {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    bU (gO f g) = Z.W f g := by
  have h := (cw.ow (gO f g) (jN hf hg.continuous hfc)
    (fD hfc hgc)).2
  rw [bU, ← h, aV.W]
  exact tsum_congr fun ρ => (Fh hf.continuous hg.continuous hfc hgc ρ).symm
theorem dO {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    bU (dK f) = Z.W f f :=
  kP hf hf hfc hfc
lemma DG {ρ : ℂ} (h : ρ.re = 1 / 2) : conj (aF ρ) = aF ρ := by
  rw [Complex.conj_eq_iff_im]
  simp [aF, h]
lemma Gv (hRH : RiemannHypothesis) (ρ : Z.carrier) : (ρ : ℂ).re = 1 / 2 := by
  obtain ⟨h0, h1, h2⟩ := ρ.2
  refine hRH _ h0 ?_ ?_
  · rintro ⟨k, hk⟩
    rw [hk] at h1
    simp at h1
    linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  · intro h; rw [h, Complex.one_re] at h2; exact lt_irrefl _ h2
theorem mK (hRH : RiemannHypothesis) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    0 ≤ bU (dK f) := by
  rw [dO hf hfc, aV.W]
  have hterm : ∀ ρ : Z.carrier, Z.dD f f ρ
      = (((Z.mult ρ : ℝ) * Complex.normSq (aD f (aF ρ)) : ℝ) : ℂ) := by
    intro ρ
    rw [aV.dD, DG (Gv hRH ρ), mul_assoc,
      Complex.mul_conj]
    push_cast
    ring
  rw [tsum_congr hterm, ← Complex.ofReal_tsum]
  exact Complex.zero_le_real.2 (tsum_nonneg fun ρ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))
end aR.Weil
end
end

-- Zeta23.gX.acF
section
noncomputable section
namespace Zeta23
namespace JM
open MeasureTheory intervalIntegral
def yA : Prop := ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
  |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2
lemma Gw {T : ℝ} (hT : 0 < T) :
    ∫ τ in T..(2 * T), (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))
      = T * eD T / (2 * Real.pi) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have TN : ∀ τ ∈ Set.uIcc T (2 * T),
      HasDerivAt (fun x : ℝ => (1 / (2 * Real.pi)) * (x * Real.log (x / (2 * Real.pi)) - x))
        ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) τ := by
    intro τ hτ
    rw [Set.uIcc_of_le (by linarith)] at hτ
    have jQ : (0 : ℝ) < τ := lt_of_lt_of_le hT hτ.1
    have h1 : HasDerivAt (fun x : ℝ => x / (2 * Real.pi)) (1 / (2 * Real.pi)) τ :=
      (hasDerivAt_id τ).div_const _
    have h2 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi)))
        (1 / (2 * Real.pi) / (τ / (2 * Real.pi))) τ := by
      have h3 := (Real.hasDerivAt_log (by positivity : τ / (2 * Real.pi) ≠ 0)).comp τ h1
      have heq : 1 / (2 * Real.pi) / (τ / (2 * Real.pi))
          = (τ / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi)) := by ring
      rw [heq]
      exact h3
    have h4 : HasDerivAt (fun x : ℝ => x * Real.log (x / (2 * Real.pi)))
        (Real.log (τ / (2 * Real.pi)) + τ * (1 / (2 * Real.pi) / (τ / (2 * Real.pi)))) τ := by
      have h4a := (hasDerivAt_id τ).mul h2
      have heq : Real.log (τ / (2 * Real.pi)) + τ * (1 / (2 * Real.pi) / (τ / (2 * Real.pi)))
          = 1 * Real.log (τ / (2 * Real.pi))
            + τ * (1 / (2 * Real.pi) / (τ / (2 * Real.pi))) := by ring
      rw [heq]
      exact h4a
    have h5 := (h4.sub (hasDerivAt_id τ)).const_mul (1 / (2 * Real.pi))
    have Zw : τ ≠ 0 := jQ.ne'
    have heq : (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))
        = 1 / (2 * Real.pi) * (Real.log (τ / (2 * Real.pi))
            + τ * (1 / (2 * Real.pi) / (τ / (2 * Real.pi))) - 1) := by
      have hmul : τ * (1 / (2 * Real.pi) / (τ / (2 * Real.pi))) = 1 := by
        field_simp
      rw [hmul]
      ring
    rw [heq]
    exact h5
  have hcont : IntervalIntegrable
      (fun τ : ℝ => (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    refine ContinuousOn.mul continuousOn_const ?_
    intro τ hτ
    have jQ : (0 : ℝ) < τ := lt_of_lt_of_le hT hτ.1
    exact ((Real.continuousAt_log (by positivity)).comp
      (continuousAt_id.div_const _)).continuousWithinAt
  rw [integral_eq_sub_of_hasDerivAt TN hcont]
  have XD : Real.log (2 * T / (2 * Real.pi)) = Real.log 2 + Real.log (T / (2 * Real.pi)) := by
    rw [show 2 * T / (2 * Real.pi) = 2 * (T / (2 * Real.pi)) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  rw [XD]
  unfold eD l
  field_simp
  ring
theorem DH (hst : yA) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(∫ τ in T..(2 * T), Zeta23.mu τ) - T * eD T / (2 * Real.pi)| ≤ C / T := by
  obtain ⟨C, hC⟩ := hst
  have hC0 : 0 ≤ C := by
    have h := hC 1 (by norm_num)
    have := abs_nonneg (Zeta23.mu 1 - 1 / (2 * Real.pi) * Real.log (|1| / (2 * Real.pi)))
    nlinarith
  have Lb : Continuous Zeta23.mu := Zeta23.Dh.continuous
  refine ⟨C, 1, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have OT : IntervalIntegrable Zeta23.mu volume T (2 * T) :=
    Lb.intervalIntegrable _ _
  have DJ : IntervalIntegrable
      (fun τ : ℝ => (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    refine ContinuousOn.mul continuousOn_const ?_
    intro τ hτ
    have jQ : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
    exact ((Real.continuousAt_log (by positivity)).comp
      (continuousAt_id.div_const _)).continuousWithinAt
  have hsplit : (∫ τ in T..(2 * T), Zeta23.mu τ)
      = (∫ τ in T..(2 * T), (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
        + ∫ τ in T..(2 * T),
            (Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) := by
    rw [← intervalIntegral.integral_add DJ (OT.sub DJ)]
    congr 1
    funext τ
    ring
  rw [hsplit, Gw hT0]
  rw [add_sub_cancel_left]
  have TP : IntervalIntegrable
      (fun τ : ℝ => Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
      volume T (2 * T) := OT.sub DJ
  have hbound : ∀ τ ∈ Set.Icc T (2 * T),
      |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| ≤ C / τ ^ 2 := by
    intro τ hτ
    have hτ1 : (1 : ℝ) ≤ τ := le_trans hT hτ.1
    have habs : |τ| = τ := abs_of_pos (by linarith)
    have h := hC τ (by rwa [habs])
    rwa [habs] at h
  have Mj : IntervalIntegrable (fun τ : ℝ => C / τ ^ 2) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    intro τ hτ
    have jQ : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
    exact (continuousAt_const.div (continuousAt_pow _ _) (by positivity)).continuousWithinAt
  have QE : ∫ τ in T..(2 * T), C / τ ^ 2 = C / (2 * T) := by
    have QF : ∀ τ ∈ Set.uIcc T (2 * T),
        HasDerivAt (fun x : ℝ => -C / x) (C / τ ^ 2) τ := by
      intro τ hτ
      rw [Set.uIcc_of_le (by linarith)] at hτ
      have jQ : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
      have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-1 / τ ^ 2) τ := (hasDerivAt_id τ).inv jQ.ne'
      have h1 := hinv.const_mul (-C)
      have h3 : (fun x : ℝ => -C * x⁻¹) = fun x : ℝ => -C / x := by
        funext x
        ring
      rw [h3] at h1
      have heq : C / τ ^ 2 = -C * (-1 / τ ^ 2) := by ring
      rw [heq]
      exact h1
    rw [integral_eq_sub_of_hasDerivAt QF Mj]
    field_simp
    ring
  calc |∫ τ in T..(2 * T),
        (Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))|
      ≤ ∫ τ in T..(2 * T),
          |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| :=
        intervalIntegral.abs_integral_le_integral_abs (by linarith)
    _ ≤ ∫ τ in T..(2 * T), C / τ ^ 2 := by
        refine intervalIntegral.integral_mono_on (by linarith) TP.abs Mj ?_
        intro τ hτ
        exact hbound τ hτ
    _ = C / (2 * T) := QE
    _ ≤ C / T := by
        have h2 : (0 : ℝ) < 2 * T := by linarith
        rw [div_le_div_iff₀ h2 hT0]
        nlinarith
lemma BX {T : ℝ} (hT : 0 < T) :
    ∫ τ in T..(2 * T), Real.log (τ / (2 * Real.pi)) ^ 2
      = T * (eD T ^ 2 + 1 - 2 * Real.log 2 ^ 2) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have TN : ∀ τ ∈ Set.uIcc T (2 * T),
      HasDerivAt (fun x : ℝ =>
          x * (Real.log (x / (2 * Real.pi)) ^ 2 - 2 * Real.log (x / (2 * Real.pi)) + 2))
        (Real.log (τ / (2 * Real.pi)) ^ 2) τ := by
    intro τ hτ
    rw [Set.uIcc_of_le (by linarith)] at hτ
    have jQ : (0 : ℝ) < τ := lt_of_lt_of_le hT hτ.1
    have h1 : HasDerivAt (fun x : ℝ => x / (2 * Real.pi)) (1 / (2 * Real.pi)) τ :=
      (hasDerivAt_id τ).div_const _
    have h2 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi))) (1 / τ) τ := by
      have h3 := (Real.hasDerivAt_log (by positivity : τ / (2 * Real.pi) ≠ 0)).comp τ h1
      have heq : 1 / τ = (τ / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi)) := by
        rw [inv_div]
        field_simp
      rw [heq]
      exact h3
    have h4 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi)) ^ 2)
        (2 * Real.log (τ / (2 * Real.pi)) * (1 / τ)) τ := by
      have h5 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi)) ^ 2)
          ((2 : ℕ) * Real.log (τ / (2 * Real.pi)) ^ (2 - 1) * (1 / τ)) τ := h2.pow 2
      convert h5 using 1
      norm_num
    have h6 : HasDerivAt (fun x : ℝ =>
        Real.log (x / (2 * Real.pi)) ^ 2 - 2 * Real.log (x / (2 * Real.pi)) + 2)
        (2 * Real.log (τ / (2 * Real.pi)) * (1 / τ) - 2 * (1 / τ)) τ := by
      have h7 := (h4.sub (h2.const_mul 2)).add_const 2
      exact h7
    have h8 := (hasDerivAt_id τ).mul h6
    have Zw : τ ≠ 0 := jQ.ne'
    have heq : Real.log (τ / (2 * Real.pi)) ^ 2
        = 1 * (Real.log (τ / (2 * Real.pi)) ^ 2 - 2 * Real.log (τ / (2 * Real.pi)) + 2)
          + τ * (2 * Real.log (τ / (2 * Real.pi)) * (1 / τ) - 2 * (1 / τ)) := by
      field_simp
      ring
    rw [heq]
    exact h8
  have hcont : IntervalIntegrable
      (fun τ : ℝ => Real.log (τ / (2 * Real.pi)) ^ 2) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    intro τ hτ
    have jQ : (0 : ℝ) < τ := lt_of_lt_of_le hT hτ.1
    exact (((Real.continuousAt_log (by positivity)).comp
      (continuousAt_id.div_const _)).pow 2).continuousWithinAt
  rw [integral_eq_sub_of_hasDerivAt TN hcont]
  have XD : Real.log (2 * T / (2 * Real.pi)) = Real.log 2 + Real.log (T / (2 * Real.pi)) := by
    rw [show 2 * T / (2 * Real.pi) = 2 * (T / (2 * Real.pi)) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  rw [XD]
  unfold eD l
  ring
set_option maxHeartbeats 1600000 in
theorem zF (hst : yA) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(∫ τ in T..(2 * T), Zeta23.mu τ ^ 2) - T * eD T ^ 2 / (4 * Real.pi ^ 2)|
        ≤ C * (T * eD T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2 := by
  obtain ⟨C, hC⟩ := hst
  have hC0 : 0 ≤ C := by
    have h := hC 1 (by norm_num)
    have := abs_nonneg (Zeta23.mu 1 - 1 / (2 * Real.pi) * Real.log (|1| / (2 * Real.pi)))
    nlinarith
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have Lb : Continuous Zeta23.mu := Zeta23.Dh.continuous
  set C₂ : ℝ := C * (1 + C) + 1 with hC₂
  have Rq : (0 : ℝ) < C₂ := by nlinarith
  refine ⟨8 * (1 + 2 * Real.log 2 ^ 2) + 1,
    max (2 * Real.pi * Real.exp 4) (32 * Real.pi ^ 2 * C₂), fun T hT => ?_⟩
  set m : ℝ := Real.log 2 with hm
  have hm0 : (0 : ℝ) < m := Real.log_pos (by norm_num)
  have hm1 : m < 1 := by
    rw [hm]
    have := Real.log_two_lt_d9
    linarith
  have hT1 : 2 * Real.pi * Real.exp 4 ≤ T := le_trans (le_max_left _ _) hT
  have hT2 : 32 * Real.pi ^ 2 * C₂ ≤ T := le_trans (le_max_right _ _) hT
  have acG : (1 : ℝ) ≤ Real.exp 4 := by
    have := Real.add_one_le_exp (4 : ℝ)
    linarith
  have hT0 : (0 : ℝ) < T := by nlinarith [Real.exp_pos (4 : ℝ)]
  have hL4 : (4 : ℝ) ≤ l T := by
    unfold l
    rw [show (4 : ℝ) = Real.log (Real.exp 4) from (Real.log_exp 4).symm]
    apply Real.log_le_log (Real.exp_pos 4)
    rw [le_div_iff₀ (by positivity)]
    linarith
  set L : ℝ := l T with QG
  have hL0 : (0 : ℝ) < L := by linarith
  have abt : L ≤ T := by
    rw [QG]
    unfold l
    have h1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < T / (2 * Real.pi))
    have h2 : T / (2 * Real.pi) ≤ T := by
      rw [div_le_iff₀ (by positivity)]
      have Wt : (3 : ℝ) < Real.pi := Real.pi_gt_three
      nlinarith
    linarith
  have hell : eD T = L + 2 * m - 1 := by
    unfold eD
    rw [← QG, ← hm]
  have TQ : (0 : ℝ) < eD T := by
    rw [hell]
    nlinarith
  have VL : L / 2 ≤ eD T := by
    rw [hell]
    nlinarith
  have Zy : L ^ 2 / 4 ≤ eD T ^ 2 := by
    nlinarith [VL, hL0, TQ]
  have Oo : ∀ τ ∈ Set.Icc T (2 * T),
      |(1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| ≤ (L + m) / (2 * Real.pi) := by
    intro τ hτ
    have XE : T ≤ τ := hτ.1
    have jQ : (0 : ℝ) < τ := lt_of_lt_of_le hT0 XE
    have Oq : (0 : ℝ) ≤ Real.log (τ / (2 * Real.pi)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have VN : Real.log (τ / (2 * Real.pi)) ≤ L + m := by
      have h1 : Real.log (τ / (2 * Real.pi)) ≤ Real.log (2 * T / (2 * Real.pi)) := by
        apply Real.log_le_log (by positivity)
        gcongr
        exact hτ.2
      have h2 : Real.log (2 * T / (2 * Real.pi)) = m + L := by
        rw [show 2 * T / (2 * Real.pi) = 2 * (T / (2 * Real.pi)) by ring,
          Real.log_mul (by norm_num) (by positivity), hm, QG]
        rfl
      linarith
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi)),
      abs_of_nonneg Oq]
    rw [one_div, div_eq_mul_inv (L + m), mul_comm (L + m)]
    exact mul_le_mul_of_nonneg_left VN (by positivity)
  have QH : ∀ τ ∈ Set.Icc T (2 * T),
      |Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2|
        ≤ C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C) := by
    intro τ hτ
    have XE : T ≤ τ := hτ.1
    have hτ1 : (1 : ℝ) ≤ τ := by nlinarith
    have habs : |τ| = τ := abs_of_pos (by linarith)
    have TU := hC τ (by rwa [habs])
    rw [habs] at TU
    have hmb := Oo τ hτ
    have hsq : Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2
        = (Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
          * (Zeta23.mu τ + (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) := by
      ring
    rw [hsq, abs_mul]
    have hτ2 : (0 : ℝ) < τ ^ 2 := by positivity
    have WG : C / τ ^ 2 ≤ C := by
      rw [div_le_iff₀ hτ2]
      have ach : (1 : ℝ) ≤ τ ^ 2 := by nlinarith
      nlinarith
    have QI : |Zeta23.mu τ + (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))|
        ≤ 2 * ((L + m) / (2 * Real.pi)) + C := by
      have h4 := abs_sub_abs_le_abs_sub (Zeta23.mu τ)
        ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
      have h5 : |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| ≤ C :=
        le_trans TU WG
      have h3 : |Zeta23.mu τ| ≤ (L + m) / (2 * Real.pi) + C := by linarith
      calc |Zeta23.mu τ + (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))|
          ≤ |Zeta23.mu τ| + |(1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| :=
            abs_add_le _ _
        _ ≤ 2 * ((L + m) / (2 * Real.pi)) + C := by linarith
    exact mul_le_mul TU QI (abs_nonneg _) (by positivity)
  have NW : IntervalIntegrable (fun τ : ℝ => Zeta23.mu τ ^ 2) volume T (2 * T) :=
    (Lb.pow 2).intervalIntegrable _ _
  have zY : IntervalIntegrable
      (fun τ : ℝ => ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)
      volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    intro τ hτ
    have jQ : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
    exact ((continuousAt_const.mul ((Real.continuousAt_log (by positivity)).comp
      (continuousAt_id.div_const _))).pow 2).continuousWithinAt
  have XF : IntervalIntegrable
      (fun τ : ℝ => C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C)) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    intro τ hτ
    have jQ : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
    exact ((continuousAt_const.div (continuousAt_pow _ _) (by positivity)).mul
      continuousAt_const).continuousWithinAt
  have XG : ∫ τ in T..(2 * T), ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2
      = (1 / (4 * Real.pi ^ 2)) * (T * (eD T ^ 2 + 1 - 2 * m ^ 2)) := by
    rw [show (fun τ : ℝ => ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)
        = fun τ : ℝ => (1 / (4 * Real.pi ^ 2)) * Real.log (τ / (2 * Real.pi)) ^ 2
      from funext fun τ => by field_simp; ring]
    rw [intervalIntegral.integral_const_mul, BX hT0, hm]
  have hsplit : (∫ τ in T..(2 * T), Zeta23.mu τ ^ 2)
      = (∫ τ in T..(2 * T), ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)
        + ∫ τ in T..(2 * T),
            (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2) := by
    rw [← intervalIntegral.integral_add zY (NW.sub zY)]
    congr 1
    funext τ
    ring
  have QE : ∫ τ in T..(2 * T), C / τ ^ 2 = C / (2 * T) := by
    have QF : ∀ τ ∈ Set.uIcc T (2 * T),
        HasDerivAt (fun x : ℝ => -C / x) (C / τ ^ 2) τ := by
      intro τ hτ
      rw [Set.uIcc_of_le (by linarith)] at hτ
      have jQ : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
      have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-1 / τ ^ 2) τ :=
        (hasDerivAt_id τ).inv jQ.ne'
      have h1 := hinv.const_mul (-C)
      have h3 : (fun x : ℝ => -C * x⁻¹) = fun x : ℝ => -C / x := by
        funext x
        ring
      rw [h3] at h1
      have heq : C / τ ^ 2 = -C * (-1 / τ ^ 2) := by ring
      rw [heq]
      exact h1
    have Mj : IntervalIntegrable (fun τ : ℝ => C / τ ^ 2) volume T (2 * T) := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by linarith)]
      intro τ hτ
      have jQ : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
      exact (continuousAt_const.div (continuousAt_pow _ _)
        (by positivity)).continuousWithinAt
    rw [integral_eq_sub_of_hasDerivAt QF Mj]
    field_simp
    ring
  have Zz : |∫ τ in T..(2 * T),
      (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)|
      ≤ (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) := by
    have XH : ∫ τ in T..(2 * T), C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C)
        = (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) := by
      rw [show (fun τ : ℝ => C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C))
          = fun τ : ℝ => (2 * ((L + m) / (2 * Real.pi)) + C) * (C / τ ^ 2)
        from funext fun τ => by ring]
      rw [intervalIntegral.integral_const_mul, QE]
      ring
    calc |∫ τ in T..(2 * T),
          (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)|
        ≤ ∫ τ in T..(2 * T),
            |Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2| :=
          intervalIntegral.abs_integral_le_integral_abs (by linarith)
      _ ≤ ∫ τ in T..(2 * T), C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C) := by
          refine intervalIntegral.integral_mono_on (by linarith)
            (NW.sub zY).abs XF ?_
          intro τ hτ
          exact QH τ hτ
      _ = (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) := XH
  rw [hsplit, XG]
  set X : ℝ := T * eD T ^ 2 / (4 * Real.pi ^ 2) / L ^ 2 with hX
  have hX1 : T / (16 * Real.pi ^ 2) ≤ X := by
    rw [hX, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Zy, hT0.le, sq_nonneg L, mul_pos hT0 (mul_pos hπ hπ)]
  have hX0 : (0 : ℝ) < X := by
    rw [hX]
    positivity
  have htri : |(1 / (4 * Real.pi ^ 2)) * (T * (eD T ^ 2 + 1 - 2 * m ^ 2))
      + (∫ τ in T..(2 * T),
          (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2))
      - T * eD T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ |(1 / (4 * Real.pi ^ 2)) * (T * (eD T ^ 2 + 1 - 2 * m ^ 2))
          - T * eD T ^ 2 / (4 * Real.pi ^ 2)|
        + |∫ τ in T..(2 * T),
            (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)| := by
    have h1 := abs_add_le
      ((1 / (4 * Real.pi ^ 2)) * (T * (eD T ^ 2 + 1 - 2 * m ^ 2))
        - T * eD T ^ 2 / (4 * Real.pi ^ 2))
      (∫ τ in T..(2 * T),
        (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2))
    calc |(1 / (4 * Real.pi ^ 2)) * (T * (eD T ^ 2 + 1 - 2 * m ^ 2))
        + (∫ τ in T..(2 * T),
            (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2))
        - T * eD T ^ 2 / (4 * Real.pi ^ 2)|
        = |((1 / (4 * Real.pi ^ 2)) * (T * (eD T ^ 2 + 1 - 2 * m ^ 2))
            - T * eD T ^ 2 / (4 * Real.pi ^ 2))
          + ∫ τ in T..(2 * T),
              (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)| := by
          congr 1
          ring
      _ ≤ _ := h1
  have RZ : |(1 / (4 * Real.pi ^ 2)) * (T * (eD T ^ 2 + 1 - 2 * m ^ 2))
      - T * eD T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ 8 * (1 + 2 * m ^ 2) * X := by
    have h1 : (1 / (4 * Real.pi ^ 2)) * (T * (eD T ^ 2 + 1 - 2 * m ^ 2))
        - T * eD T ^ 2 / (4 * Real.pi ^ 2) = T * (1 - 2 * m ^ 2) / (4 * Real.pi ^ 2) := by
      ring
    rw [h1, abs_div, abs_mul, abs_of_pos hT0,
      abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi ^ 2)]
    have habs1 : |1 - 2 * m ^ 2| ≤ 1 + 2 * m ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg m]
    calc T * |1 - 2 * m ^ 2| / (4 * Real.pi ^ 2)
        ≤ T * (1 + 2 * m ^ 2) / (4 * Real.pi ^ 2) := by gcongr
      _ = 4 * (1 + 2 * m ^ 2) * (T / (16 * Real.pi ^ 2)) := by ring
      _ ≤ 4 * (1 + 2 * m ^ 2) * X := by
          gcongr
      _ ≤ 8 * (1 + 2 * m ^ 2) * X := by nlinarith [hX0, sq_nonneg m]
  have QJ : (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) ≤ 1 * X := by
    have Wt : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hb1 : 2 * ((L + m) / (2 * Real.pi)) ≤ L := by
      have h2a : (L + m) / (2 * Real.pi) ≤ (L + 1) / (2 * Real.pi) := by
        gcongr
      have h2b : (L + 1) / (2 * Real.pi) ≤ (L + 1) / 6 :=
        div_le_div_of_nonneg_left (by linarith) (by norm_num) (by nlinarith)
      have h3 : (L + 1) / 6 ≤ L / 2 := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith
      linarith
    have hb2 : 2 * ((L + m) / (2 * Real.pi)) + C ≤ (1 + C) * L := by
      have h4 : C ≤ C * L := by nlinarith
      nlinarith
    have hb3 : (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) ≤ C₂ * L / T := by
      have h5 : (0 : ℝ) ≤ 2 * ((L + m) / (2 * Real.pi)) + C := by positivity
      have h6 : (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C)
          ≤ (C / (2 * T)) * ((1 + C) * L) := by
        apply mul_le_mul_of_nonneg_left hb2 (by positivity)
      calc (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C)
          ≤ (C / (2 * T)) * ((1 + C) * L) := h6
        _ = (C * (1 + C)) * L / (2 * T) := by ring
        _ ≤ C₂ * L / T := by
            rw [div_le_div_iff₀ (by linarith) (by linarith)]
            have h7 : (0 : ℝ) ≤ C * (1 + C) := by nlinarith
            nlinarith [mul_nonneg (mul_nonneg h7 hL0.le) hT0.le, hL0.le, hT0.le]
    have hb4 : C₂ * L / T ≤ C₂ := by
      rw [div_le_iff₀ hT0]
      nlinarith
    have hb5 : C₂ ≤ T / (32 * Real.pi ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hb6 : T / (32 * Real.pi ^ 2) ≤ T / (16 * Real.pi ^ 2) := by
      apply div_le_div_of_nonneg_left hT0.le (by positivity)
      nlinarith
    rw [one_mul]
    calc (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C)
        ≤ C₂ * L / T := hb3
      _ ≤ C₂ := hb4
      _ ≤ T / (32 * Real.pi ^ 2) := hb5
      _ ≤ T / (16 * Real.pi ^ 2) := hb6
      _ ≤ X := hX1
  calc |(1 / (4 * Real.pi ^ 2)) * (T * (eD T ^ 2 + 1 - 2 * m ^ 2))
      + (∫ τ in T..(2 * T),
          (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2))
      - T * eD T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ |(1 / (4 * Real.pi ^ 2)) * (T * (eD T ^ 2 + 1 - 2 * m ^ 2))
          - T * eD T ^ 2 / (4 * Real.pi ^ 2)|
        + |∫ τ in T..(2 * T),
            (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)| := htri
    _ ≤ 8 * (1 + 2 * m ^ 2) * X + 1 * X := by
        have := le_trans Zz QJ
        linarith [RZ]
    _ = (8 * (1 + 2 * m ^ 2) + 1) * (T * eD T ^ 2 / (4 * Real.pi ^ 2)) / L ^ 2 := by
        rw [hX]
        ring
end JM
end Zeta23
end
end

-- Zeta23.gX.Complete
section
noncomputable section
namespace Zeta23
theorem yD (hst : JM.yA) : gX :=
  ⟨OJ, Dh, lD.rH, lD.GK, lD.qK,
    hst, lD.KE, JM.DH hst, JM.zF hst⟩
theorem QK : gX := yD oR.Ol
end Zeta23
end
end

-- aR.tP
section
open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate FourierTransform Real
noncomputable section
namespace aR.tP
open Zeta23 Zeta23.EF
def w (c τ : ℝ) : ℝ := 2 * c / (c ^ 2 + τ ^ 2)
lemma w_nonneg {c : ℝ} (hc : 0 ≤ c) (τ : ℝ) : 0 ≤ w c τ := by unfold w; positivity
lemma TW {c : ℝ} (hc : 0 < c) (τ : ℝ) : w c τ ≤ 2 / c := by
  unfold w
  rw [div_le_div_iff₀ (by positivity) hc]
  nlinarith [sq_nonneg τ]
lemma vW {c : ℝ} (hc : 0 < c) : Continuous (w c) := by
  unfold w
  exact continuous_const.div (by fun_prop) fun τ => by positivity
lemma Ez {c : ℝ} (hc : c ≠ 0) (τ : ℝ) : (c : ℂ) - I * τ ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this; exact hc this
lemma zG {c : ℝ} (hc : c ≠ 0) (τ : ℝ) : (-c : ℂ) - I * τ ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this; exact hc this
theorem vX {c : ℝ} (hc : 0 < c) (τ : ℝ) :
    ∫ u : ℝ, (Real.exp (-c * |u|) : ℂ) * cexp (-I * τ * u) = (w c τ : ℂ) := by
  have TY : IntegrableOn (fun u : ℝ => cexp ((c - I * τ) * u)) (Iic 0) :=
    integrableOn_exp_mul_complex_Iic (by simpa using hc) 0
  have hIoi : IntegrableOn (fun u : ℝ => cexp ((-c - I * τ) * u)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by simpa using hc) 0
  have QN : EqOn (fun u : ℝ => (Real.exp (-c * |u|) : ℂ) * cexp (-I * τ * u))
      (fun u : ℝ => cexp ((c - I * τ) * u)) (Iic 0) := by
    intro u hu
    simp only [mem_Iic] at hu
    simp only [abs_of_nonpos hu, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have QO : EqOn (fun u : ℝ => (Real.exp (-c * |u|) : ℂ) * cexp (-I * τ * u))
      (fun u : ℝ => cexp ((-c - I * τ) * u)) (Ioi 0) := by
    intro u hu
    simp only [mem_Ioi] at hu
    simp only [abs_of_pos hu, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) (TY.congr_fun QN.symm measurableSet_Iic)
    (hIoi.congr_fun QO.symm measurableSet_Ioi),
    setIntegral_congr_fun measurableSet_Iic QN, setIntegral_congr_fun measurableSet_Ioi QO,
    integral_exp_mul_complex_Iic (by simpa using hc) 0, integral_exp_mul_complex_Ioi (by simpa using hc) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have h1 := Ez hc.ne' τ
  have h2 := zG hc.ne' τ
  have h3 : (c : ℂ) ^ 2 + (τ : ℂ) ^ 2 ≠ 0 := by
    rw [show (c : ℂ) ^ 2 + (τ : ℂ) ^ 2 = ((c ^ 2 + τ ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact_mod_cast (by positivity : (c ^ 2 + τ ^ 2 : ℝ) ≠ 0)
  unfold w
  push_cast
  rw [neg_div, ← sub_eq_add_neg, div_sub_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) h3]
  ring_nf
  rw [Complex.I_sq]
  ring
theorem rO {c : ℝ} (hc : 0 < c) (τ : ℝ) :
    Integrable (fun u : ℝ => (Real.exp (-c * |u|) : ℂ) * cexp (-I * τ * u)) := by
  have TY : IntegrableOn (fun u : ℝ => cexp ((c - I * τ) * u)) (Iic 0) :=
    integrableOn_exp_mul_complex_Iic (by simpa using hc) 0
  have hIoi : IntegrableOn (fun u : ℝ => cexp ((-c - I * τ) * u)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by simpa using hc) 0
  have QN : EqOn (fun u : ℝ => (Real.exp (-c * |u|) : ℂ) * cexp (-I * τ * u))
      (fun u : ℝ => cexp ((c - I * τ) * u)) (Iic 0) := by
    intro u hu
    simp only [mem_Iic] at hu
    simp only [abs_of_nonpos hu, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have QO : EqOn (fun u : ℝ => (Real.exp (-c * |u|) : ℂ) * cexp (-I * τ * u))
      (fun u : ℝ => cexp ((-c - I * τ) * u)) (Ioi 0) := by
    intro u hu
    simp only [mem_Ioi] at hu
    simp only [abs_of_pos hu, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have := (TY.congr_fun QN.symm measurableSet_Iic).union
    (hIoi.congr_fun QO.symm measurableSet_Ioi)
  rwa [Iic_union_Ioi, integrableOn_univ] at this
theorem yF {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => (Real.exp (-c * |u|) : ℂ)) := by
  simpa using rO hc 0
theorem lJ {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k)
    (oN : Integrable (𝓕 k)) {c : ℝ} (hc : 0 < c) :
    ∫ u : ℝ, k u * (Real.exp (-c * |u|) : ℂ) = (1 / (2 * π) : ℂ) * ∫ τ : ℝ, aD k τ * (w c τ : ℂ) := by
  rw [yW hk hki oN (yF hc)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only
  rw [vX hc]
theorem LH {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k) (oN : Integrable (𝓕 k)) :
    k 0 = (1 / (2 * π) : ℂ) * ∫ τ : ℝ, aD k τ := by
  rw [oO hk hki oN 0]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp
def t (n : ℕ) (τ : ℝ) : ℝ := 1 / ((n : ℝ) + 1) - w (2 * n + 5 / 2) τ
lemma Aa (n : ℕ) (τ : ℝ) : 0 ≤ t n τ := by
  unfold t
  have h := TW (c := 2 * n + 5 / 2) (by positivity) τ
  have : 2 / (2 * (n : ℝ) + 5 / 2) ≤ 1 / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  linarith
lemma t_le (n : ℕ) (τ : ℝ) : t n τ ≤ 1 / ((n : ℝ) + 1) := by
  unfold t; linarith [w_nonneg (c := 2 * n + 5 / 2) (by positivity) τ]
lemma NX (n : ℕ) : Continuous (t n) := by
  unfold t; exact continuous_const.sub (vW (by positivity))
lemma Sd (τ : ℝ) : (1 / 4 : ℝ) / ((1 / 4) ^ 2 + (τ / 2) ^ 2) = w (1 / 2) τ := by
  unfold w; field_simp; ring
lemma OU (n : ℕ) (τ : ℝ) :
    ((n : ℝ) + 1 + 1 / 4) / (((n : ℝ) + 1 + 1 / 4) ^ 2 + (τ / 2) ^ 2) = w (2 * n + 5 / 2) τ := by
  unfold w; field_simp; ring
lemma QS (τ : ℝ) : Summable fun n => t n τ := by
  refine (lD.mo (a := 1 / 4) (by norm_num) (by norm_num) (τ / 2)).congr fun n => ?_
  rw [t, ← OU]
lemma wQ (τ : ℝ) :
    dL τ = -Real.eulerMascheroniConstant - Real.log π - w (1 / 2) τ + ∑' n : ℕ, t n τ := by
  have h := lD.jf (a := 1 / 4) (by norm_num) (by norm_num) (τ / 2)
  unfold dL
  rw [show (1 / 4 + I * (τ : ℂ) / 2) = ((1 / 4 : ℝ) : ℂ) + I * ((τ / 2 : ℝ) : ℂ) by push_cast; ring, h,
    Sd]
  have hs : ∑' n : ℕ, (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + 1 / 4) / (((n : ℝ) + 1 + 1 / 4) ^ 2 + (τ / 2) ^ 2))
      = ∑' n : ℕ, t n τ := tsum_congr fun n => by rw [t, OU]
  rw [hs]
  ring
lemma LX (τ : ℝ) : (mu τ : ℂ) = (1 / (2 * π) : ℂ) * (dL τ : ℂ) := by
  simp only [mu, dL]; push_cast; ring
theorem Gz {k : ℝ → ℂ} (hk2 : ContDiff ℝ 2 k) (bD : HasCompactSupport k) :
    (1 / (2 * π) : ℂ) * ∫ τ : ℝ, aD k τ * (dL τ : ℂ)
      = ((-Real.eulerMascheroniConstant - Real.log π : ℝ) : ℂ) * k 0
        - (∫ u : ℝ, k u * (Real.exp (-(1 / 2) * |u|) : ℂ))
        + ∑' n : ℕ, (k 0 / ((n : ℂ) + 1)
            - ∫ u : ℝ, k u * (Real.exp (-(2 * n + 5 / 2) * |u|) : ℂ)) := by
  have hk : Continuous k := hk2.continuous
  have hki : Integrable k := hk.integrable_of_hasCompactSupport bD
  have oN : Integrable (𝓕 k) := dH hk2 bD
  have hh : Integrable (fun τ : ℝ => aD k τ) := dY oN
  set h : ℝ → ℂ := fun τ => aD k τ with hhdef
  have hbdd : ∀ {g : ℝ → ℝ} {C : ℝ}, Continuous g → (∀ τ, |g τ| ≤ C) →
      Integrable (fun τ => h τ * (g τ : ℂ)) := by
    intro g C hg hC
    refine hh.mul_bdd (c := C) (by fun_prop) (Eventually.of_forall fun τ => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hC τ
  have hw0 : Integrable (fun τ => h τ * (w (1 / 2) τ : ℂ)) :=
    hbdd (vW (by norm_num)) fun τ => by
      rw [abs_of_nonneg (w_nonneg (by norm_num) τ)]; exact TW (by norm_num) τ
  have htn : ∀ n : ℕ, Integrable (fun τ => h τ * (t n τ : ℂ)) := fun n =>
    hbdd (NX n) fun τ => by rw [abs_of_nonneg (Aa n τ)]; exact t_le n τ
  have hμ : Integrable (fun τ : ℝ => aD k τ * (mu τ : ℂ)) := tL hk2 bD QK
  have hbr : Integrable (fun τ => h τ * (dL τ : ℂ)) := by
    refine (hμ.const_mul (2 * π : ℂ)).congr (Eventually.of_forall fun τ => ?_)
    simp only [hhdef, LX]
    field_simp
  set T : ℝ → ℝ := fun τ => ∑' n : ℕ, t n τ with hT
  have hTeq : ∀ τ, h τ * (T τ : ℂ) = h τ * (dL τ : ℂ)
      + ((Real.eulerMascheroniConstant + Real.log π : ℝ) : ℂ) * h τ + h τ * (w (1 / 2) τ : ℂ) := by
    intro τ; rw [wQ τ]; simp only [hT, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_tsum]; ring
  have UO : Integrable (fun τ => h τ * (T τ : ℂ)) :=
    ((hbr.add (hh.const_mul _)).add hw0).congr (Eventually.of_forall fun τ => (hTeq τ).symm)
  have hsum : Summable fun n : ℕ => ∫ τ, ‖h τ * (t n τ : ℂ)‖ := by
    refine summable_of_sum_range_le (c := ∫ τ, ‖h τ * (T τ : ℂ)‖)
      (fun n => integral_nonneg fun τ => norm_nonneg _) fun N => ?_
    rw [← integral_finsetSum _ fun n _ => (htn n).norm]
    refine integral_mono (integrable_finsetSum _ fun n _ => (htn n).norm) UO.norm fun τ => ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Aa _ τ)]
    rw [← Finset.mul_sum, abs_of_nonneg (tsum_nonneg fun n => Aa n τ)]
    exact mul_le_mul_of_nonneg_left
      ((QS τ).sum_le_tsum _ fun n _ => Aa n τ) (norm_nonneg _)
  have hswap : ∫ τ, h τ * (T τ : ℂ) = ∑' n : ℕ, ∫ τ, h τ * (t n τ : ℂ) := by
    rw [integral_tsum_of_summable_integral_norm htn hsum]
    congr 1; ext τ
    rw [hT, Complex.ofReal_tsum, tsum_mul_left]
  have hterm : ∀ n : ℕ, (1 / (2 * π) : ℂ) * ∫ τ, h τ * (t n τ : ℂ)
      = k 0 / ((n : ℂ) + 1) - ∫ u : ℝ, k u * (Real.exp (-(2 * n + 5 / 2) * |u|) : ℂ) := by
    intro n
    have hc : (0 : ℝ) < 2 * n + 5 / 2 := by positivity
    have hwc : Integrable (fun τ => h τ * (w (2 * n + 5 / 2) τ : ℂ)) :=
      hbdd (vW hc) fun τ => by rw [abs_of_nonneg (w_nonneg hc.le τ)]; exact TW hc τ
    have e : (fun τ => h τ * (t n τ : ℂ)) =
        fun τ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * h τ - h τ * (w (2 * n + 5 / 2) τ : ℂ) := by
      ext τ; simp only [t]; push_cast; ring
    rw [e, integral_sub (hh.const_mul _) hwc, dW, mul_sub,
      lJ hk hki oN hc, LH hk hki oN]
    push_cast
    ring
  have hsplit : (fun τ => h τ * (dL τ : ℂ)) = fun τ =>
      ((-Real.eulerMascheroniConstant - Real.log π : ℝ) : ℂ) * h τ - h τ * (w (1 / 2) τ : ℂ)
        + h τ * (T τ : ℂ) := by
    ext τ; rw [wQ τ]; simp only [hT, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_tsum]; ring
  have hB : Integrable (fun τ => ((-Real.eulerMascheroniConstant - Real.log π : ℝ) : ℂ) * h τ) :=
    hh.const_mul _
  have hA : Integrable (fun τ => ((-Real.eulerMascheroniConstant - Real.log π : ℝ) : ℂ) * h τ
      - h τ * (w (1 / 2) τ : ℂ)) := hB.sub hw0
  rw [hsplit, integral_add hA UO, integral_sub hB hw0,
    dW, hswap, mul_add, mul_sub, ← tsum_mul_left]
  simp only [hterm]
  rw [lJ hk hki oN (by norm_num : (0 : ℝ) < 1 / 2), LH hk hki oN]
  ring
def DX (k : ℝ → ℂ) : ℂ :=
  ((Real.log (4 * π) + Real.eulerMascheroniConstant : ℝ) : ℂ) * k 0 +
    ∫ x in Ioi (0 : ℝ), (k x + k (-x) - 2 * (Real.exp (-x / 2) : ℂ) * k 0) * (Real.exp (x / 2) : ℂ)
      / ((Real.exp x - Real.exp (-x) : ℝ) : ℂ)
lemma qP {k : ℝ → ℂ} (hk : Continuous k) (bD : HasCompactSupport k) (c : ℝ) :
    ∫ u : ℝ, k u * (Real.exp (-c * |u|) : ℂ)
      = ∫ x in Ioi (0 : ℝ), (k x + k (-x)) * (Real.exp (-c * x) : ℂ) := by
  set φ : ℝ → ℂ := fun u => k u * (Real.exp (-c * |u|) : ℂ) with hφ
  have hφi : Integrable φ :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport (bD.mul_right)
  have hφn : Integrable (fun x => φ (-x)) := hφi.comp_neg
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hφi.integrableOn hφi.integrableOn,
    ← neg_zero, ← integral_comp_neg_Ioi, neg_zero, add_comm,
    ← integral_add hφi.integrableOn hφn.integrableOn]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  simp only [hφ, abs_neg, abs_of_pos (show (0 : ℝ) < x from hx)]
  ring
lemma rP {a : ℝ} (ha : 0 < a) : ∫ x in Ioi (0 : ℝ), Real.exp (-a * x) = 1 / a := by
  rw [integral_exp_mul_Ioi (by linarith : -a < 0) 0]; simp
lemma wR (x : ℝ) (n : ℕ) :
    Real.exp (-(2 * ((n : ℝ) + 1)) * x) = Real.exp (-2 * x) ^ (n + 1) := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
lemma DK {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, Real.exp (-(2 * ((n : ℝ) + 1)) * x) = Real.exp (-2 * x) / (1 - Real.exp (-2 * x)) := by
  have h0 : 0 ≤ Real.exp (-2 * x) := (Real.exp_pos _).le
  have h1 : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  simp_rw [wR, pow_succ, tsum_mul_right, tsum_geometric_of_lt_one h0 h1]
  rw [div_eq_inv_mul]
lemma GA {x : ℝ} (hx : 0 < x) : Summable fun n : ℕ => Real.exp (-(2 * ((n : ℝ) + 1)) * x) := by
  have h0 : 0 ≤ Real.exp (-2 * x) := (Real.exp_pos _).le
  have h1 : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  simp_rw [wR, pow_succ]
  exact (summable_geometric_of_lt_one h0 h1).mul_right _
lemma geom_le {x : ℝ} (hx : 0 < x) :
    Real.exp (-2 * x) / (1 - Real.exp (-2 * x)) ≤ 1 / (2 * x * (1 + x)) := by
  have he := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * x)
  have hpos : 0 < Real.exp (2 * x) - 1 := by nlinarith
  have e : Real.exp (-2 * x) / (1 - Real.exp (-2 * x)) = 1 / (Real.exp (2 * x) - 1) := by
    rw [show -2 * x = -(2 * x) by ring, Real.exp_neg]
    have : Real.exp (2 * x) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
  rw [e, div_le_div_iff₀ hpos (by positivity)]
  nlinarith
lemma nJ {x : ℝ} (hx : 0 < x) : 0 ≤ Real.exp (-2 * x) / (1 - Real.exp (-2 * x)) := by
  have h1 : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  exact div_nonneg (Real.exp_pos _).le (by linarith)
lemma Ot {k : ℝ → ℂ} (hk2 : ContDiff ℝ 2 k) (bD : HasCompactSupport k) :
    ∃ L : ℝ, ∀ x : ℝ, 0 ≤ x →
      ‖2 * k 0 - (Real.exp (-x / 2) : ℂ) * (k x + k (-x))‖ ≤ L * x := by
  have hk1 : ContDiff ℝ 1 k := hk2.of_le (by norm_num)
  have hdk : Continuous (deriv k) := hk1.continuous_deriv le_rfl
  obtain ⟨M0, hM0⟩ := hk2.continuous.bounded_above_of_compact_support bD
  obtain ⟨M1, hM1⟩ := hdk.bounded_above_of_compact_support bD.deriv
  set F : ℝ → ℂ := fun x => 2 * k 0 - (Real.exp (-x / 2) : ℂ) * (k x + k (-x)) with hF
  set F' : ℝ → ℂ := fun x => -(((-(1 / 2) * Real.exp (-x / 2) : ℝ) : ℂ) * (k x + k (-x))
      + (Real.exp (-x / 2) : ℂ) * (deriv k x + (-1 : ℝ) • deriv k (-x))) with hF'
  have hder : ∀ x : ℝ, HasDerivAt F (F' x) x := by
    intro x
    have hkx : HasDerivAt k (deriv k x) x := (hk1.differentiable one_ne_zero x).hasDerivAt
    have hkn : HasDerivAt (fun y => k (-y)) ((-1 : ℝ) • deriv k (-x)) x := by
      have h1 : HasDerivAt k (deriv k (-x)) (-x) := (hk1.differentiable one_ne_zero (-x)).hasDerivAt
      have h2 : HasDerivAt (fun y : ℝ => -y) (-1) x := hasDerivAt_neg x
      exact h1.scomp x h2
    have he : HasDerivAt (fun y : ℝ => (Real.exp (-y / 2) : ℂ)) ((-(1 / 2) * Real.exp (-x / 2) : ℝ)) x := by
      have : HasDerivAt (fun y : ℝ => Real.exp (-y / 2)) (Real.exp (-x / 2) * (-1 / 2)) x :=
        (Real.hasDerivAt_exp _).comp x ((hasDerivAt_neg x).div_const 2)
      convert this.ofReal_comp using 1; push_cast; ring
    have := (hasDerivAt_const x (2 * k 0)).sub (he.mul (hkx.add hkn))
    refine this.congr_deriv ?_
    simp only [hF', zero_sub, Pi.add_apply]
  set C : ℝ := (1 / 2) * (2 * M0) + 2 * M1 with hC
  have hbd : ∀ x : ℝ, 0 ≤ x → ‖F' x‖ ≤ C := by
    intro x hx
    have he1 : Real.exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have he0 : 0 ≤ Real.exp (-x / 2) := (Real.exp_pos _).le
    simp only [hF', norm_neg]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonpos (by nlinarith), abs_of_nonneg he0]
    have h1 : ‖k x + k (-x)‖ ≤ 2 * M0 := (norm_add_le _ _).trans (by linarith [hM0 x, hM0 (-x)])
    have h2 : ‖deriv k x + (-1 : ℝ) • deriv k (-x)‖ ≤ 2 * M1 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_neg, norm_one, one_mul]; linarith [hM1 x, hM1 (-x)]
    have aaT : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0)
    have ada : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
    calc -(-(1 / 2) * Real.exp (-x / 2)) * ‖k x + k (-x)‖ + Real.exp (-x / 2) * ‖deriv k x + (-1 : ℝ) • deriv k (-x)‖
        ≤ (1 / 2) * (2 * M0) + 1 * (2 * M1) := by
          gcongr
          · nlinarith
        _ = C := by rw [hC]; ring
  refine ⟨C, fun x hx => ?_⟩
  have hF0 : F 0 = 0 := by simp [hF]; ring
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := F) (f' := F') (a := 0) (b := x)
    (fun y _ => (hder y).hasDerivWithinAt) (fun y hy => hbd y hy.1) x ⟨hx, le_rfl⟩
  rw [hF0, sub_zero, sub_zero] at this
  exact this
lemma jD :
    IntegrableOn (fun x => Real.exp (-x) / (1 + Real.exp (-x))) (Ioi 0) := by
  refine (exp_neg_integrableOn_Ioi 0 one_pos).mono' ?_ ?_
  · exact (Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity) :
      Continuous fun x : ℝ => Real.exp (-x) / (1 + Real.exp (-x))).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_pos _).le (by positivity)), neg_one_mul]
    exact div_le_self (Real.exp_pos _).le (by linarith [Real.exp_pos (-x)])
lemma GC : ∫ x in Ioi (0 : ℝ), Real.exp (-x) / (1 + Real.exp (-x)) = Real.log 2 := by
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x => -Real.log (1 + Real.exp (-x)))
      (Real.exp (-x) / (1 + Real.exp (-x))) x := by
    intro x _
    have h1 : HasDerivAt (fun x => 1 + Real.exp (-x)) (-Real.exp (-x)) x := by
      have := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).const_add 1
      simpa using this
    have := (h1.log (by positivity)).neg
    rw [neg_div, neg_neg] at this
    exact this
  have hint := jD
  have htend : Tendsto (fun x => -Real.log (1 + Real.exp (-x))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => 1 + Real.exp (-x)) atTop (𝓝 1) := by
      simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_add 1
    have := ((Real.continuousAt_log one_ne_zero).tendsto.comp h1).neg
    simpa using this
  have hc : Continuous fun x : ℝ => -Real.log (1 + Real.exp (-x)) :=
    ((by fun_prop : Continuous fun x : ℝ => 1 + Real.exp (-x)).log fun x => by positivity).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := fun x => -Real.log (1 + Real.exp (-x)))
    hc.continuousWithinAt hderiv hint htend]
  norm_num
lemma BZ {k : ℝ → ℂ} (hk2 : ContDiff ℝ 2 k) (bD : HasCompactSupport k) :
    IntegrableOn (fun x => ‖2 * k 0 - (Real.exp (-x / 2) : ℂ) * (k x + k (-x))‖ *
      (Real.exp (-2 * x) / (1 - Real.exp (-2 * x)))) (Ioi 0) := by
  obtain ⟨L, hL⟩ := Ot hk2 bD
  obtain ⟨M0, hM0⟩ := hk2.continuous.bounded_above_of_compact_support bD
  set B : ℝ → ℝ := fun x => ‖2 * k 0 - (Real.exp (-x / 2) : ℂ) * (k x + k (-x))‖ *
      (Real.exp (-2 * x) / (1 - Real.exp (-2 * x))) with hB
  have hcont : ContinuousOn B (Ioi 0) := by
    refine ContinuousOn.mul (Continuous.continuousOn (by
      have := hk2.continuous; fun_prop)) ?_
    refine (Continuous.continuousOn (by fun_prop)).div (Continuous.continuousOn (by fun_prop)) fun x hx => ?_
    have : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by simp only [mem_Ioi] at hx; linarith)
    linarith
  have hmeas : ∀ s ⊆ Ioi (0 : ℝ), MeasurableSet s → AEStronglyMeasurable B (volume.restrict s) :=
    fun s hs hsm => (hcont.mono hs).aestronglyMeasurable hsm
  set MF : ℝ := 2 * ‖k 0‖ + 2 * M0 with hMF
  have adb : 0 ≤ MF := by have := (norm_nonneg _).trans (hM0 0); positivity
  have XJ : ∀ x : ℝ, 0 ≤ x → ‖2 * k 0 - (Real.exp (-x / 2) : ℂ) * (k x + k (-x))‖ ≤ MF := by
    intro x hx
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he1 : Real.exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h1 : ‖k x + k (-x)‖ ≤ 2 * M0 := (norm_add_le _ _).trans (by linarith [hM0 x, hM0 (-x)])
    have aaT : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0)
    simp only [Complex.norm_ofNat]
    nlinarith [norm_nonneg (k x + k (-x)), Real.exp_pos (-x / 2)]
  have h01 : IntegrableOn B (Ioc 0 1) := by
    refine (integrableOn_const (C := |L| / 2) measure_Ioc_lt_top.ne).mono'
      (hmeas _ Ioc_subset_Ioi_self measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (nJ hx0))]
    calc B x ≤ (L * x) * (1 / (2 * x * (1 + x))) :=
          mul_le_mul (hL x hx0.le) (geom_le hx0) (nJ hx0) ((norm_nonneg _).trans (hL x hx0.le))
      _ = L / (2 * (1 + x)) := by field_simp
      _ ≤ |L| / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [le_abs_self L, abs_nonneg L]
  have h1i : IntegrableOn B (Ioi 1) := by
    have hdom : IntegrableOn (fun x : ℝ => MF / 2 * x ^ (-2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
    refine hdom.mono' (hmeas _ (Ioi_subset_Ioi zero_le_one) measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    have hx1 : 1 < x := hx
    have hx0 : 0 < x := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (nJ hx0)),
      Real.rpow_neg hx0.le, Real.rpow_two]
    calc B x ≤ MF * (1 / (2 * x * (1 + x))) :=
          mul_le_mul (XJ x hx0.le) (geom_le hx0) (nJ hx0) (by positivity)
      _ ≤ MF / 2 * (x ^ 2)⁻¹ := by
          rw [show MF / 2 * (x ^ 2)⁻¹ = MF * (1 / (2 * x * x)) by field_simp]
          gcongr
          nlinarith
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact h01.union h1i
lemma VO {x : ℝ} (hx : 0 < x) (k0 K : ℂ) :
    (K - 2 * (Real.exp (-x / 2) : ℂ) * k0) * (Real.exp (x / 2) : ℂ) / ((Real.exp x - Real.exp (-x) : ℝ) : ℂ)
      = -2 * k0 * ((Real.exp (-x) / (1 + Real.exp (-x)) : ℝ) : ℂ)
        - (2 * k0 - (Real.exp (-x / 2) : ℂ) * K) * ((Real.exp (-2 * x) / (1 - Real.exp (-2 * x)) : ℝ) : ℂ)
        + K * (Real.exp (-(1 / 2) * x) : ℂ) := by
  set a := Real.exp (-x / 2) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have e3 : Real.exp (-x) = a ^ 2 := by rw [ha, sq, ← Real.exp_add]; ring_nf
  have e1 : Real.exp (x / 2) = a⁻¹ := by rw [ha, ← Real.exp_neg]; ring_nf
  have e2 : Real.exp x = (a ^ 2)⁻¹ := by rw [← e3, ← Real.exp_neg, neg_neg]
  have e4 : Real.exp (-2 * x) = a ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← e3, sq, ← Real.exp_add]; ring_nf
  have e5 : Real.exp (-(1 / 2) * x) = a := by rw [ha]; ring_nf
  rw [e1, e2, e3, e4, e5]
  have h4 : (1 - a ^ 4 : ℝ) ≠ 0 := by nlinarith [pow_pos ha0 2, pow_pos ha0 4, pow_lt_one₀ ha0.le ha1 (by norm_num : 4 ≠ 0)]
  have h2 : (1 + a ^ 2 : ℝ) ≠ 0 := by positivity
  have hd : ((a ^ 2)⁻¹ - a ^ 2 : ℝ) ≠ 0 := by
    have : a ^ 2 < 1 := pow_lt_one₀ ha0.le ha1 (by norm_num)
    have : 1 < (a ^ 2)⁻¹ := one_lt_inv₀ (by positivity) |>.2 this
    nlinarith
  have hc4 : (1 - (a : ℂ) ^ 4) ≠ 0 := by exact_mod_cast h4
  have hc2 : (1 + (a : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h2
  have hcd : (((a : ℂ) ^ 2)⁻¹ - (a : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hd
  have hca : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  push_cast
  field_simp
  ring
theorem Cc {k : ℝ → ℂ} (hk2 : ContDiff ℝ 2 k) (bD : HasCompactSupport k) :
    ((-Real.eulerMascheroniConstant - Real.log π : ℝ) : ℂ) * k 0
        - (∫ u : ℝ, k u * (Real.exp (-(1 / 2) * |u|) : ℂ))
        + ∑' n : ℕ, (k 0 / ((n : ℂ) + 1)
            - ∫ u : ℝ, k u * (Real.exp (-(2 * n + 5 / 2) * |u|) : ℂ))
      = -DX k := by
  have hk : Continuous k := hk2.continuous
  set K : ℝ → ℂ := fun x => k x + k (-x) with hK
  set F : ℝ → ℂ := fun x => 2 * k 0 - (Real.exp (-x / 2) : ℂ) * K x with hF
  set g : ℝ → ℝ := fun x => Real.exp (-2 * x) / (1 - Real.exp (-2 * x)) with hg
  have hKc : Continuous K := hk.add (hk.comp continuous_neg)
  have aaU : HasCompactSupport K := bD.add (bD.comp_homeomorph (Homeomorph.neg ℝ))
  have hFc : Continuous F := by simp only [hF]; fun_prop
  obtain ⟨M0, hM0⟩ := hk.bounded_above_of_compact_support bD
  have hKe : ∀ c : ℝ, IntegrableOn (fun x => K x * (Real.exp (-c * x) : ℂ)) (Ioi 0) := fun c =>
    ((hKc.mul (by fun_prop)).integrable_of_hasCompactSupport aaU.mul_right).integrableOn
  have hE : ∀ n : ℕ, IntegrableOn (fun x : ℝ => (Real.exp (-(2 * ((n : ℝ) + 1)) * x) : ℂ)) (Ioi 0) :=
    fun n => (exp_neg_integrableOn_Ioi 0 (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1))).ofReal
  have XJ : ∀ x : ℝ, 0 < x → ‖F x‖ ≤ 2 * ‖k 0‖ + 2 * M0 := by
    intro x hx
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he1 : Real.exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h1 : ‖K x‖ ≤ 2 * M0 := (norm_add_le _ _).trans (by linarith [hM0 x, hM0 (-x)])
    simp only [Complex.norm_ofNat]
    nlinarith [norm_nonneg (K x), Real.exp_pos (-x / 2)]
  have hGn : ∀ n : ℕ, IntegrableOn (fun x => (Real.exp (-(2 * ((n : ℝ) + 1)) * x) : ℂ) * F x) (Ioi 0) := by
    intro n
    refine (hE n).mul_bdd (c := 2 * ‖k 0‖ + 2 * M0) hFc.aestronglyMeasurable ?_
    · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => XJ x hx)
  have hterm : ∀ n : ℕ, k 0 / ((n : ℂ) + 1) - ∫ u : ℝ, k u * (Real.exp (-(2 * n + 5 / 2) * |u|) : ℂ)
      = ∫ x in Ioi (0 : ℝ), (Real.exp (-(2 * ((n : ℝ) + 1)) * x) : ℂ) * F x := by
    intro n
    rw [qP hk bD]
    have hcm : ∀ (c : ℂ) (f : ℝ → ℂ), ∫ x in Ioi (0 : ℝ), c * f x = c * ∫ x in Ioi (0 : ℝ), f x :=
      fun c f => integral_const_mul c f
    have e : ∀ x : ℝ, (Real.exp (-(2 * ((n : ℝ) + 1)) * x) : ℂ) * F x
        = 2 * k 0 * (Real.exp (-(2 * ((n : ℝ) + 1)) * x) : ℂ) - K x * (Real.exp (-(2 * n + 5 / 2) * x) : ℂ) := by
      intro x
      simp only [hF]
      rw [show -(2 * (n : ℝ) + 5 / 2) * x = -(2 * ((n : ℝ) + 1)) * x + (-x / 2) by ring, Real.exp_add]
      push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => e x),
      integral_sub ((hE n).const_mul _) (hKe _), hcm, integral_complex_ofReal,
      rP (by positivity)]
    have : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    simp only [hK]
    push_cast
    field_simp
  have hBint := BZ hk2 bD
  have hsum : Summable fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖(Real.exp (-(2 * ((n : ℝ) + 1)) * x) : ℂ) * F x‖ := by
    refine summable_of_sum_range_le (c := ∫ x in Ioi (0 : ℝ), ‖F x‖ * g x)
      (fun n => integral_nonneg fun x => norm_nonneg _) fun N => ?_
    rw [← integral_finsetSum _ fun n _ => (hGn n).norm]
    refine setIntegral_mono_on (integrable_finsetSum _ fun n _ => (hGn n).norm) hBint measurableSet_Ioi
      fun x hx => ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← Finset.sum_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    show _ ≤ Real.exp (-2 * x) / (1 - Real.exp (-2 * x))
    rw [← DK hx]
    exact (GA hx).sum_le_tsum _ fun n _ => (Real.exp_pos _).le
  have hS : ∑' n : ℕ, (k 0 / ((n : ℂ) + 1) - ∫ u : ℝ, k u * (Real.exp (-(2 * n + 5 / 2) * |u|) : ℂ))
      = ∫ x in Ioi (0 : ℝ), F x * (g x : ℂ) := by
    simp_rw [hterm]
    rw [integral_tsum_of_summable_integral_norm hGn hsum]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [tsum_mul_right, ← Complex.ofReal_tsum, DK hx, mul_comm]
  have hP1 : IntegrableOn (fun x : ℝ => ((Real.exp (-x) / (1 + Real.exp (-x)) : ℝ) : ℂ)) (Ioi 0) :=
    jD.ofReal
  have hP2 : IntegrableOn (fun x => F x * (g x : ℂ)) (Ioi 0) := by
    refine hBint.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine hFc.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn ?_)
      refine (Continuous.continuousOn (by fun_prop)).div (Continuous.continuousOn (by fun_prop)) fun x hx => ?_
      have : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by simp only [mem_Ioi] at hx; linarith)
      linarith
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (nJ hx)]
  have hP3 := hKe (1 / 2)
  have hJ : ∫ x in Ioi (0 : ℝ), (k x + k (-x) - 2 * (Real.exp (-x / 2) : ℂ) * k 0) * (Real.exp (x / 2) : ℂ)
      / ((Real.exp x - Real.exp (-x) : ℝ) : ℂ)
      = -2 * k 0 * (Real.log 2 : ℂ) - (∫ x in Ioi (0 : ℝ), F x * (g x : ℂ))
        + ∫ x in Ioi (0 : ℝ), K x * (Real.exp (-(1 / 2) * x) : ℂ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => VO hx (k 0) (K x))]
    have hcm : ∀ (c : ℂ) (f : ℝ → ℂ), ∫ x in Ioi (0 : ℝ), c * f x = c * ∫ x in Ioi (0 : ℝ), f x :=
      fun c f => integral_const_mul c f
    have hQ1 : IntegrableOn (fun x : ℝ => -2 * k 0 * ((Real.exp (-x) / (1 + Real.exp (-x)) : ℝ) : ℂ)) (Ioi 0) :=
      hP1.const_mul _
    have hQ2 : IntegrableOn (fun x : ℝ => -2 * k 0 * ((Real.exp (-x) / (1 + Real.exp (-x)) : ℝ) : ℂ)
        - (2 * k 0 - (Real.exp (-x / 2) : ℂ) * K x) * ((Real.exp (-2 * x) / (1 - Real.exp (-2 * x)) : ℝ) : ℂ))
        (Ioi 0) := hQ1.sub hP2
    rw [integral_add hQ2 hP3, integral_sub hQ1 hP2, hcm, integral_complex_ofReal, GC]
  rw [hS, qP hk bD, DX, hJ]
  have hl : Real.log (4 * π) = 2 * Real.log 2 + Real.log π := by
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [hl]
  push_cast
  ring
theorem yI {k : ℝ → ℂ} (hk2 : ContDiff ℝ 2 k) (bD : HasCompactSupport k) :
    (1 / (2 * π) : ℂ) * ∫ τ : ℝ, aD k τ * (dL τ : ℂ) = -DX k := by
  rw [Gz hk2 bD, Cc hk2 bD]
end aR.tP
end
end

-- aR.XZ
section
noncomputable section
open Complex MeasureTheory Filter Topology Set Metric
namespace aR.Weil
def kG (Φ : ℝ → ℂ) (s : ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), Φ t * cexp (-s * t)
lemma sw (s : ℂ) (t : ℝ) : ‖cexp (-s * t)‖ = Real.exp (-s.re * t) := by
  rw [Complex.norm_exp]; simp
lemma Ac {Φ : ℝ → ℂ} {B : ℝ} (hΦ : Continuous Φ) (hB : ∀ t, 0 ≤ t → ‖Φ t‖ ≤ B)
    {s : ℂ} (hs : 0 < s.re) : IntegrableOn (fun t : ℝ => Φ t * cexp (-s * t)) (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hs).const_mul B) ?_ ?_
  · exact (hΦ.mul (by fun_prop)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, sw]
    exact mul_le_mul_of_nonneg_right (hB t (le_of_lt ht)) (Real.exp_pos _).le
theorem lK {Φ : ℝ → ℂ} {B : ℝ} (hΦ : Continuous Φ)
    (hB : ∀ t, 0 ≤ t → ‖Φ t‖ ≤ B) {s₁ : ℂ} (hs₁ : 0 < s₁.re) :
    DifferentiableAt ℂ (kG Φ) s₁ := by
  set σ := s₁.re with hσ
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 le_rfl)
  have hball : ∀ s ∈ ball s₁ (σ / 2), σ / 2 < s.re := by
    intro s hs
    have h1 : |s.re - s₁.re| < σ / 2 := by
      rw [mem_ball, dist_eq_norm] at hs
      calc |s.re - s₁.re| = |(s - s₁).re| := by simp
        _ ≤ ‖s - s₁‖ := Complex.abs_re_le_norm _
        _ < σ / 2 := hs
    rw [abs_lt] at h1
    linarith [h1.1]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (s : ℂ) (t : ℝ) => Φ t * cexp (-s * t))
    (F' := fun (s : ℂ) (t : ℝ) => Φ t * (-(t : ℂ) * cexp (-s * t)))
    (x₀ := s₁) (s := ball s₁ (σ / 2))
    (bound := fun t : ℝ => B * (4 / σ) * Real.exp (-(σ / 4) * t))
    (ball_mem_nhds s₁ (by linarith))
    (Eventually.of_forall fun s => (hΦ.mul (by fun_prop)).aestronglyMeasurable)
    (Ac hΦ hB hs₁)
    ((hΦ.mul (by fun_prop)).aestronglyMeasurable) ?_ ?_ ?_
  · exact key.2.differentiableAt
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht s hs => ?_)
    have ht' : (0 : ℝ) < t := ht
    have hre := hball s hs
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht',
      sw]
    have h1 : Real.exp (-s.re * t) ≤ Real.exp (-(σ / 2) * t) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h2 : t ≤ (4 / σ) * Real.exp ((σ / 4) * t) := by
      have := Real.add_one_le_exp ((σ / 4) * t)
      rw [div_mul_eq_mul_div, le_div_iff₀ hs₁]
      nlinarith
    have h3 : t * Real.exp (-(σ / 2) * t) ≤ (4 / σ) * Real.exp (-(σ / 4) * t) := by
      have e1 : Real.exp (-(σ / 2) * t) = Real.exp (-(σ / 4) * t) * Real.exp (-(σ / 4) * t) := by
        rw [← Real.exp_add]; congr 1; ring
      have e2 : Real.exp (σ / 4 * t) * Real.exp (-(σ / 4) * t) = 1 := by
        rw [← Real.exp_add, show σ / 4 * t + -(σ / 4) * t = 0 by ring, Real.exp_zero]
      have hpos := Real.exp_pos (-(σ / 4) * t)
      rw [e1, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ hpos.le
      calc t * Real.exp (-(σ / 4) * t)
          ≤ (4 / σ * Real.exp (σ / 4 * t)) * Real.exp (-(σ / 4) * t) :=
            mul_le_mul_of_nonneg_right h2 hpos.le
        _ = 4 / σ := by rw [mul_assoc, e2, mul_one]
    calc ‖Φ t‖ * (t * Real.exp (-s.re * t)) ≤ B * (t * Real.exp (-(σ / 2) * t)) := by
          refine mul_le_mul (hB t ht'.le) ?_ (by positivity) hB0
          exact mul_le_mul_of_nonneg_left h1 ht'.le
      _ ≤ B * ((4 / σ) * Real.exp (-(σ / 4) * t)) := mul_le_mul_of_nonneg_left h3 hB0
      _ = B * (4 / σ) * Real.exp (-(σ / 4) * t) := by ring
  · exact ((exp_neg_integrableOn_Ioi 0 (by linarith : (0 : ℝ) < σ / 4)).const_mul (B * (4 / σ)))
  · refine Eventually.of_forall fun t s _ => ?_
    have : HasDerivAt (fun s : ℂ => -s * (t : ℂ)) (-(t : ℂ)) s := by
      simpa using ((hasDerivAt_id s).neg.mul_const (t : ℂ))
    have h2 := this.cexp
    simpa [mul_comm, mul_assoc, mul_left_comm] using h2.const_mul (Φ t)
lemma vY {ι : Type*} (p : ι → ℂ) (q : ι → Prop) (s₁ : ℂ)
    (hfin : {i | q i ∧ ‖p i - s₁‖ < 1}.Finite) (hne : ∀ i, q i → p i ≠ s₁) :
    ∃ r, 0 < r ∧ ∀ i, q i → ∀ s ∈ ball s₁ r, r ≤ ‖s - p i‖ := by
  set T := p '' {i | q i ∧ ‖p i - s₁‖ < 1}
  have hT : T.Finite := hfin.image p
  have XK : s₁ ∉ T := by
    rintro ⟨i, hi, he⟩
    exact hne i hi.1 he
  obtain ⟨ε, hε, aaV⟩ := Metric.isOpen_iff.1 hT.isClosed.isOpen_compl s₁ XK
  refine ⟨min (ε / 2) (1 / 2), by positivity, fun i hi s hs => ?_⟩
  rw [mem_ball, dist_eq_norm] at hs
  have hsub : ‖p i - s₁‖ - ‖s - s₁‖ ≤ ‖s - p i‖ := by
    have h := norm_add_le (p i - s) (s - s₁)
    rw [show p i - s + (s - s₁) = p i - s₁ by ring, norm_sub_rev (p i) s] at h
    linarith
  have hr1 : min (ε / 2) (1 / 2) ≤ ε / 2 := min_le_left _ _
  have hr2 : min (ε / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  by_cases JL : ‖p i - s₁‖ < 1
  · have hmem : p i ∈ T := ⟨i, ⟨hi, JL⟩, rfl⟩
    have Tz : ε ≤ ‖p i - s₁‖ := by
      by_contra h
      exact aaV (by rw [mem_ball, dist_eq_norm]; exact not_le.1 h) hmem
    linarith
  · have := not_lt.1 JL
    linarith
theorem qu {ι : Type*} (p a : ι → ℂ) (q : ι → Prop) (s₁ : ℂ)
    (ha : Summable fun i => ‖a i‖) (hq : ∀ i, ¬ q i → a i = 0)
    (hfin : {i | q i ∧ ‖p i - s₁‖ < 1}.Finite) (hne : ∀ i, q i → p i ≠ s₁) :
    AnalyticAt ℂ (fun s => ∑' i, a i / (s - p i)) s₁ := by
  obtain ⟨r, hr, hiso⟩ := vY p q s₁ hfin hne
  refine DifferentiableOn.analyticAt ?_ (ball_mem_nhds s₁ hr)
  refine differentiableOn_tsum_of_summable_norm (u := fun i => ‖a i‖ / r) (ha.div_const r)
    (fun i => ?_) isOpen_ball (fun i w hw => ?_)
  · by_cases hi : q i
    · refine DifferentiableOn.div (differentiableOn_const _) (differentiableOn_id.sub_const _)
        fun w hw => ?_
      have := hiso i hi w hw
      intro h0
      rw [h0, norm_zero] at this
      linarith
    · simp only [hq i hi, zero_div]
      exact differentiableOn_const _
  · by_cases hi : q i
    · rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hr (hiso i hi w hw)
    · rw [hq i hi, zero_div, norm_zero]; positivity
def dN (w : ℂ) : ℂ := ((Real.exp w.re : ℝ) : ℂ) + (w.im : ℂ) * I
lemma lO (w : ℂ) : (dN w).re = Real.exp w.re := by
  simp only [dN, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]; ring
lemma qE (w : ℂ) : (dN w).im = w.im := by simp [dN]
lemma yJ : Continuous dN := by
  unfold dN; fun_prop
lemma zH : Function.Injective dN := by
  intro w v h
  apply Complex.ext
  · have := congrArg Complex.re h
    rw [lO, lO] at this
    exact Real.exp_injective this
  · have := congrArg Complex.im h
    rwa [qE, qE] at this
lemma pO {P : Set ℂ} (hP : P.Countable) :
    IsPreconnected ({s : ℂ | 0 < s.re} \ P) := by
  have hc : (dN ⁻¹' P).Countable := hP.preimage zH
  have hconn : IsConnected (dN ⁻¹' P)ᶜ :=
    hc.isConnected_compl_of_one_lt_rank (by simp [Complex.rank_real_complex])
  have himg : dN '' (dN ⁻¹' P)ᶜ = {s : ℂ | 0 < s.re} \ P := by
    ext s
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨show 0 < (dN w).re by rw [lO]; exact Real.exp_pos _, hw⟩
    · rintro ⟨hs, hsP⟩
      have hs' : (0 : ℝ) < s.re := hs
      have heq : dN ((Real.log s.re : ℂ) + (s.im : ℂ) * I) = s := by
        apply Complex.ext
        · rw [lO]; simp [Real.exp_log hs']
        · rw [qE]; simp
      refine ⟨(Real.log s.re : ℂ) + (s.im : ℂ) * I, ?_, heq⟩
      show dN _ ∉ P
      rw [heq]; exact hsP
  rw [← himg]
  exact hconn.isPreconnected.image _ yJ.continuousOn
lemma pD (p : ℂ) (t : ℝ) : ‖cexp (p * t)‖ = Real.exp (p.re * t) := by
  rw [Complex.norm_exp]; simp
theorem zK {ι : Type*} [Countable ι] (p a : ι → ℂ) (hp : Function.Injective p)
    (hre : ∀ i, |(p i).re| ≤ 1 / 2) (hfin : ∀ s₁ : ℂ, {i | ‖p i - s₁‖ < 1}.Finite)
    (ha : Summable fun i => ‖a i‖) {B : ℝ}
    (hB : ∀ t : ℝ, 0 ≤ t → ‖∑' i, a i * cexp (p i * t)‖ ≤ B) (i₀ : ι) (hi₀ : 0 < (p i₀).re) :
    a i₀ = 0 := by
  classical
  set Φ : ℝ → ℂ := fun t => ∑' i, a i * cexp (p i * t) with XL
  have hterm : ∀ i (t : ℝ), ‖a i * cexp (p i * t)‖ ≤ ‖a i‖ * Real.exp (|t| / 2) := by
    intro i t
    rw [norm_mul, pD]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    have h1 : (p i).re * t ≤ |(p i).re| * |t| := by
      rw [← abs_mul]; exact le_abs_self _
    have h2 : |(p i).re| * |t| ≤ 1 / 2 * |t| := mul_le_mul_of_nonneg_right (hre i) (abs_nonneg _)
    linarith
  have XM : Continuous Φ := by
    rw [continuous_iff_continuousAt]
    intro t₀
    have hon : ContinuousOn Φ (ball t₀ 1) := by
      refine continuousOn_tsum (u := fun i => ‖a i‖ * Real.exp ((|t₀| + 1) / 2))
        (fun i => by fun_prop) (ha.mul_right _) (fun i t ht => (hterm i t).trans ?_)
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
      rw [mem_ball, Real.dist_eq] at ht
      have := abs_sub_abs_le_abs_sub t t₀
      linarith
    exact hon.continuousAt (ball_mem_nhds t₀ one_pos)
  set G : ℂ → ℂ := fun s => ∑' i, a i / (s - p i) with ZA
  have hLG : ∀ s : ℂ, 1 / 2 < s.re → kG Φ s = G s := by
    intro s hs
    have hneg : ∀ i, (p i - s).re < 0 := by
      intro i
      have := (abs_le.1 (hre i)).2
      simp only [sub_re]; linarith
    have hpt : ∀ t : ℝ, Φ t * cexp (-s * t) = ∑' i, a i * cexp ((p i - s) * t) := by
      intro t
      rw [XL, ← tsum_mul_right]
      refine tsum_congr fun i => ?_
      rw [mul_assoc, ← Complex.exp_add]; congr 2; ring
    have hint : ∀ i, Integrable (fun t : ℝ => a i * cexp ((p i - s) * t)) (volume.restrict (Ioi 0)) :=
      fun i => (integrableOn_exp_mul_complex_Ioi (hneg i) 0).const_mul (a i)
    have Ud : ∀ i, ∫ t in Ioi (0 : ℝ), ‖a i * cexp ((p i - s) * t)‖
        = ‖a i‖ / (s.re - (p i).re) := by
      intro i
      simp_rw [norm_mul, pD]
      rw [integral_const_mul, integral_exp_mul_Ioi (hneg i) 0]
      simp only [mul_zero, Real.exp_zero, sub_re]
      rw [show s.re - (p i).re = -((p i).re - s.re) by ring, div_neg, neg_div, mul_neg,
        mul_one_div]
    have hsum : Summable fun i => ∫ t in Ioi (0 : ℝ), ‖a i * cexp ((p i - s) * t)‖ := by
      simp_rw [Ud]
      refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (ha.div_const (s.re - 1 / 2))
      · have := hneg i; simp only [sub_re] at this
        exact div_nonneg (norm_nonneg _) (by linarith)
      · have h1 := (abs_le.1 (hre i)).2
        exact div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) (by linarith)
    unfold kG
    simp_rw [hpt]
    rw [← integral_tsum_of_summable_integral_norm hint hsum]
    refine tsum_congr fun i => ?_
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (hneg i) 0]
    have hne : p i - s ≠ 0 := fun h => by have := hneg i; rw [h, zero_re] at this; exact lt_irrefl _ this
    have hne' : s - p i ≠ 0 := fun h => hne (by rw [← neg_sub, h, neg_zero])
    simp only [ofReal_zero, mul_zero, Complex.exp_zero]
    field_simp
    ring
  set V : Set ℂ := {s : ℂ | 0 < s.re} \ range p with acH
  have ZB : IsPreconnected V := pO (countable_range p)
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have aaW : AnalyticOnNhd ℂ (kG Φ) V := by
    intro s hs
    refine DifferentiableOn.analyticAt (s := {s : ℂ | 0 < s.re}) (fun z hz => ?_)
      (hopen.mem_nhds hs.1)
    exact (lK XM hB hz).differentiableWithinAt
  have Nz : AnalyticOnNhd ℂ G V := by
    intro s hs
    refine qu p a (fun _ => True) s ha (fun i h => absurd trivial h) ?_
      (fun i _ h => hs.2 ⟨i, h⟩)
    simpa using hfin s
  have h2V : (2 : ℂ) ∈ V := by
    refine ⟨by simp, ?_⟩
    rintro ⟨i, hi⟩
    have := (abs_le.1 (hre i)).2
    rw [hi] at this; norm_num at this
  have hev : kG Φ =ᶠ[𝓝 (2 : ℂ)] G := by
    have hmem : {s : ℂ | 1 / 2 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact Filter.eventually_of_mem hmem fun s hs => hLG s hs
  have hEq : EqOn (kG Φ) G V := aaW.eqOn_of_preconnected_of_eventuallyEq Nz ZB h2V hev
  set s₀ := p i₀ with hs₀
  obtain ⟨r, hr, hiso⟩ := vY p (fun i => i ≠ i₀) s₀
    ((hfin s₀).subset fun i hi => hi.2) (fun i hi h => hi (hp h))
  set a' : ι → ℂ := fun i => if i = i₀ then 0 else a i with NY
  have ha' : Summable fun i => ‖a' i‖ := by
    refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) ha
    by_cases h : i = i₀ <;> simp [NY, h]
  set G₀ : ℂ → ℂ := fun s => ∑' i, a' i / (s - p i) with Ue
  have VQ : AnalyticAt ℂ G₀ s₀ :=
    qu p a' (fun i => i ≠ i₀) s₀ ha'
      (fun i hi => by simp only [ne_eq, not_not] at hi; simp [NY, hi])
      ((hfin s₀).subset fun i hi => hi.2) (fun i hi h => hi (hp h))
  set r' := min r s₀.re with acq
  have hr' : 0 < r' := lt_min hr hi₀
  have hloc : ∀ s ∈ ball s₀ r', s ≠ s₀ →
      (s - s₀) * kG Φ s = a i₀ + (s - s₀) * G₀ s := by
    intro s hs hne
    have hsr : s ∈ ball s₀ r := ball_subset_ball (min_le_left _ _) hs
    have hsV : s ∈ V := by
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_eq_norm] at hs
        have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
        have h2 : ‖s - s₀‖ < s₀.re := lt_of_lt_of_le hs (min_le_right _ _)
        have h3 := (abs_le.1 h1).1
        show 0 < s.re
        simp only [sub_re] at h3
        linarith
      · rintro ⟨i, hi⟩
        by_cases h : i = i₀
        · exact hne (by rw [← hi, h])
        · have := hiso i h s hsr
          rw [← hi, sub_self, norm_zero] at this
          linarith
    rw [hEq hsV]
    have hsum : Summable (Function.update (fun i => a i / (s - p i)) i₀ 0) := by
      refine Summable.of_norm_bounded (ha.div_const r) fun i => ?_
      by_cases h : i = i₀
      · rw [h, Function.update_self, norm_zero]; positivity
      · rw [Function.update_of_ne h, norm_div]
        exact div_le_div_of_nonneg_left (norm_nonneg _) hr (hiso i h s hsr)
    have hsplit := hsum.tsum_eq_add_tsum_ite' i₀
    have hG : G s = a i₀ / (s - s₀) + G₀ s := by
      rw [ZA]
      simp only at hsplit ⊢
      rw [hsplit, Ue]
      congr 1
      refine tsum_congr fun i => ?_
      by_cases h : i = i₀ <;> simp [NY, h]
    rw [hG]
    have hne' : s - s₀ ≠ 0 := sub_ne_zero.2 hne
    field_simp
  have Qc : Tendsto (fun s => (s - s₀) * kG Φ s) (𝓝[≠] s₀) (𝓝 0) := by
    have hc : ContinuousAt (fun s => (s - s₀) * kG Φ s) s₀ :=
      (continuousAt_id.sub continuousAt_const).mul
        (lK XM hB hi₀).continuousAt
    have := hc.tendsto
    simp only [sub_self, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have ZC : Tendsto (fun s => a i₀ + (s - s₀) * G₀ s) (𝓝[≠] s₀) (𝓝 (a i₀)) := by
    have hc : ContinuousAt (fun s => a i₀ + (s - s₀) * G₀ s) s₀ :=
      continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul VQ.continuousAt)
    have := hc.tendsto
    simp only [sub_self, zero_mul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have PY : (fun s => (s - s₀) * kG Φ s) =ᶠ[𝓝[≠] s₀] fun s => a i₀ + (s - s₀) * G₀ s :=
    eventually_nhdsWithin_iff.2 (Filter.eventually_of_mem (ball_mem_nhds s₀ hr')
      fun s hs hne => hloc s hs hne)
  exact (tendsto_nhds_unique (Qc.congr' PY) ZC).symm
end aR.Weil
end
end

-- aR.XO
section
noncomputable section
open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate ComplexOrder ContDiff
namespace aR.Weil
open Zeta23 Zeta23.EF
lemma kM {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (z : ℂ) :
    Integrable (fun u : ℝ => f u * cexp (I * z * u)) :=
  (hf.mul (by fun_prop)).integrable_of_hasCompactSupport (hfc.mul_right)
lemma gT {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (c z : ℂ) :
    aD (fun u => f u + c * g u) z = aD f z + c * aD g z := by
  unfold aD
  rw [← integral_const_mul, ← integral_add (kM hf hfc z)
    ((kM hg hgc z).const_mul c)]
  congr 1; ext u; ring
def tr (t : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun u => f (u - t)
lemma jZ (t : ℝ) (f : ℝ → ℂ) (z : ℂ) :
    aD (tr t f) z = cexp (I * z * t) * aD f z := by
  unfold aD tr
  rw [← integral_const_mul, ← integral_sub_right_eq_self (fun v : ℝ => cexp (I * z * t) *
    (f v * cexp (I * z * v))) t]
  congr 1; ext u
  simp only [ofReal_sub]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2; ring
lemma kH {n : WithTop ℕ∞} {f : ℝ → ℂ} (hf : ContDiff ℝ n f) (t : ℝ) : ContDiff ℝ n (tr t f) :=
  hf.comp (contDiff_id.sub contDiff_const)
lemma dQ {f : ℝ → ℂ} (hfc : HasCompactSupport f) (t : ℝ) :
    HasCompactSupport (tr t f) :=
  hfc.comp_homeomorph (Homeomorph.addRight (-t))
lemma JN (ρ : ℂ) : aF (reflect ρ) = conj (aF ρ) := by
  unfold aF reflect
  rw [map_div₀, Complex.conj_I, map_sub]
  have h : (starRingEnd ℂ) (1 / 2) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  rw [h, div_neg, ← neg_div]
  congr 1; ring
lemma reflect_reflect (ρ : ℂ) : reflect (reflect ρ) = ρ := by
  unfold reflect; simp
def Ou : Equiv.Perm Z.carrier :=
  Function.Involutive.toPerm (fun ρ => ⟨reflect ρ, Z.qH ρ ρ.2⟩)
    (fun ρ => Subtype.ext (reflect_reflect ρ))
lemma GD (f g : ℝ → ℂ) (ρ : Z.carrier) :
    Z.dD g f (reflect ρ) = conj (Z.dD f g ρ) := by
  unfold aV.dD
  rw [Z.kT ρ ρ.2, JN, Complex.conj_conj]
  simp only [map_mul, Complex.conj_natCast, Complex.conj_conj]
  ring
theorem Se (f g : ℝ → ℂ) : Z.W g f = conj (Z.W f g) := by
  unfold aV.W
  rw [Complex.conj_tsum, ← Ou.tsum_eq]
  refine tsum_congr fun ρ => ?_
  exact GD f g ρ
lemma JO {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (c : ℂ) :
    Z.W (fun u => f u + c * g u) (fun u => f u + c * g u)
      = Z.W f f + conj c * Z.W f g + c * Z.W g f + c * conj c * Z.W g g := by
  have hpt : ∀ ρ : Z.carrier, Z.dD (fun u => f u + c * g u) (fun u => f u + c * g u) ρ
      = Z.dD f f ρ + conj c * Z.dD f g ρ + c * Z.dD g f ρ
        + c * conj c * Z.dD g g ρ := by
    intro ρ
    unfold aV.dD
    rw [gT hf.continuous hg.continuous hfc hgc,
      gT hf.continuous hg.continuous hfc hgc]
    simp only [map_add, map_mul]
    ring
  have s1 := iJ hf hf hfc hfc
  have s2 := (iJ hf hg hfc hgc).mul_left (conj c)
  have s3 := (iJ hg hf hgc hfc).mul_left c
  have s4 := (iJ hg hg hgc hgc).mul_left (c * conj c)
  unfold aV.W
  rw [tsum_congr hpt, Summable.tsum_add ((s1.add s2).add s3) s4,
    Summable.tsum_add (s1.add s2) s3, Summable.tsum_add s1 s2, tsum_mul_left, tsum_mul_left,
    tsum_mul_left]
lemma Bd (ρ : ℂ) : I * aF ρ = ρ - 1 / 2 := by
  unfold aF; field_simp
lemma GI (φ : ℝ → ℂ) (t : ℝ) (ρ : ℂ) :
    Z.dD (tr t φ) φ ρ = Z.dD φ φ ρ * cexp ((ρ - 1 / 2) * t) := by
  unfold aV.dD
  rw [jZ, ← Bd]
  ring
lemma Lc (φ : ℝ → ℂ) (t : ℝ) (ρ : ℂ) :
    Z.dD (tr t φ) (tr t φ) ρ = Z.dD φ φ ρ := by
  unfold aV.dD
  rw [jZ, jZ, map_mul, ← Complex.exp_conj]
  have h : cexp (I * aF ρ * t) * cexp (conj (I * conj (aF ρ) * t)) = 1 := by
    rw [← Complex.exp_add]
    simp only [map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
    rw [show I * aF ρ * t + -I * aF ρ * t = 0 by ring, Complex.exp_zero]
  calc _ = (Z.mult ρ : ℂ) * aD φ (aF ρ) * conj (aD φ (conj (aF ρ)))
        * (cexp (I * aF ρ * t) * cexp (conj (I * conj (aF ρ) * t))) := by ring
    _ = _ := by rw [h, mul_one]
lemma qQ {w b : ℂ}
    (h : ∀ c : ℂ, 0 ≤ (w + conj c * b + c * conj b + c * conj c * w).re) : ‖b‖ ≤ w.re := by
  by_cases hb : b = 0
  · have := h 0
    simp only [map_zero, zero_mul, add_zero, mul_zero] at this
    rw [hb, norm_zero]; exact this
  have hn : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hb
  have hn' : ‖b‖ ≠ 0 := norm_ne_zero_iff.2 hb
  set c : ℂ := -(b / ‖b‖)
  have hc : conj c = -(conj b / ‖b‖) := by
    simp only [c, map_neg, map_div₀, Complex.conj_ofReal]
  have e1 : conj c * b = -(‖b‖ : ℂ) := by
    rw [hc, neg_mul, div_mul_eq_mul_div, Complex.conj_mul']
    field_simp
  have e2 : c * conj b = -(‖b‖ : ℂ) := by
    simp only [c, neg_mul, div_mul_eq_mul_div, Complex.mul_conj']
    field_simp
  have e3 : c * conj c = 1 := by
    rw [hc]
    simp only [c, neg_mul_neg, div_mul_div_comm, Complex.mul_conj']
    field_simp
  have := h c
  rw [e1, e2, e3, one_mul] at this
  simp only [add_re, neg_re, ofReal_re] at this
  linarith
lemma ED : Z.carrier.Countable := by
  have : Z.carrier = ⋃ n : ℤ, Z.carrier ∩ {ρ | (n : ℝ) < ρ.im ∧ ρ.im ≤ n + 1} := by
    ext ρ
    simp only [mem_iUnion, mem_inter_iff, mem_setOf_eq]
    constructor
    · intro h
      refine ⟨⌈ρ.im⌉ - 1, h, ?_, ?_⟩
      · push_cast; linarith [Int.ceil_lt_add_one ρ.im]
      · push_cast; linarith [Int.le_ceil ρ.im]
    · rintro ⟨n, h, -⟩; exact h
  rw [this]
  exact countable_iUnion fun n => (Z.dS n (n + 1)).countable
instance abw : Countable Z.carrier := ED.to_subtype
lemma Ov (s₁ : ℂ) : {ρ : Z.carrier | ‖((ρ : ℂ) - 1 / 2) - s₁‖ < 1}.Finite := by
  have hw := Z.dS (s₁.im - 1) (s₁.im + 1)
  refine (hw.preimage Subtype.val_injective.injOn).subset fun ρ hρ => ?_
  simp only [mem_setOf_eq] at hρ
  refine ⟨ρ.2, ?_⟩
  have h1 : |(((ρ : ℂ) - 1 / 2) - s₁).im| ≤ ‖((ρ : ℂ) - 1 / 2) - s₁‖ := Complex.abs_im_le_norm _
  have h2 := abs_lt.1 (lt_of_le_of_lt h1 hρ)
  simp only [sub_im, one_div, inv_im, im_ofNat, normSq_ofNat] at h2
  simp only [mem_setOf_eq]
  constructor <;> linarith [h2.1, h2.2]
def bump : ℝ → ℂ := fun u => ((⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ)) u : ℂ)
lemma Bj : ContDiff ℝ ∞ bump :=
  ofRealCLM.contDiff.comp (ContDiffBump.contDiff _)
lemma nL : HasCompactSupport bump :=
  (ContDiffBump.hasCompactSupport _).comp_left (g := ((↑) : ℝ → ℂ)) ofReal_zero
lemma EH : aD bump 0 ≠ 0 := by
  have h : aD bump 0 = ((∫ u : ℝ, (⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ)) u : ℝ) : ℂ) := by
    unfold aD bump
    simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
    exact integral_ofReal
  rw [h, ofReal_ne_zero]
  exact (ContDiffBump.integral_pos _).ne'
lemma tQ {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ContinuousAt (aD f) 0 := by
  refine continuousAt_of_dominated (bound := fun u => ‖f u‖ * Real.exp |u|) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun z => (kM hf hfc z).aestronglyMeasurable
  · refine Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : ℂ) one_pos) fun z hz => ?_
    refine Eventually.of_forall fun u => ?_
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    rw [mem_ball_zero_iff] at hz
    have h1 : (I * z * u).re = -(z.im * u) := by simp
    rw [h1]
    have h2 : |z.im * u| ≤ |u| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) ((Complex.abs_im_le_norm z).trans hz.le)
    linarith [neg_abs_le (z.im * u)]
  · exact ((hf.norm.mul (Real.continuous_exp.comp continuous_abs)).integrable_of_hasCompactSupport
      (hfc.norm.mul_right))
  · exact Eventually.of_forall fun u => by fun_prop
def pH (l : ℝ) : ℝ → ℂ := fun u => bump (l * u)
lemma qU {l : ℝ} (hl : 0 < l) (z : ℂ) :
    aD (pH l) z = (l⁻¹ : ℂ) * aD bump (z / l) := by
  unfold aD pH
  have := Measure.integral_comp_mul_left (fun v : ℝ => bump v * cexp (I * (z / l) * v)) l
  have e : ∀ u : ℝ, bump (l * u) * cexp (I * z * u) = bump (l * u) * cexp (I * (z / l) * ↑(l * u)) := by
    intro u
    congr 2
    have : (l : ℂ) ≠ 0 := ofReal_ne_zero.2 hl.ne'
    push_cast
    field_simp
  simp_rw [e]
  rw [this, abs_of_pos (inv_pos.2 hl), Complex.real_smul]
  push_cast; ring
lemma Ci (l : ℝ) : ContDiff ℝ ∞ (pH l) :=
  Bj.comp (contDiff_const.mul contDiff_id)
lemma qG {l : ℝ} (hl : 0 < l) : HasCompactSupport (pH l) :=
  nL.comp_homeomorph (Homeomorph.mulLeft₀ l hl.ne')
lemma Cj (z w : ℂ) :
    ∃ φ : ℝ → ℂ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ aD φ z ≠ 0 ∧ aD φ w ≠ 0 := by
  have hc := tQ Bj.continuous nL
  have hlim : ∀ x : ℂ, Tendsto (fun l : ℝ => aD bump (x / l)) atTop (𝓝 (aD bump 0)) := by
    intro x
    refine hc.tendsto.comp ?_
    have : Tendsto (fun l : ℝ => (l : ℂ)⁻¹) atTop (𝓝 0) := by
      have h := (tendsto_inv_atTop_zero (𝕜 := ℝ))
      have h2 := (continuous_ofReal.tendsto 0).comp h
      rw [ofReal_zero] at h2
      exact h2.congr fun l => by simp
    simpa [div_eq_mul_inv] using this.const_mul x
  have hev : ∀ x : ℂ, ∀ᶠ l : ℝ in atTop, aD bump (x / l) ≠ 0 := fun x =>
    (hlim x).eventually (isOpen_ne.mem_nhds EH)
  obtain ⟨l, hl, hz, hw⟩ := ((eventually_gt_atTop 0).and ((hev z).and (hev w))).exists
  refine ⟨pH l, Ci l, qG hl, ?_, ?_⟩
  · rw [qU hl]
    exact mul_ne_zero (inv_ne_zero (ofReal_ne_zero.2 hl.ne')) hz
  · rw [qU hl]
    exact mul_ne_zero (inv_ne_zero (ofReal_ne_zero.2 hl.ne')) hw
lemma cZ {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 2 f :=
  hf.of_le (WithTop.coe_le_coe.2 le_top)
end aR.Weil
end
end

-- aR.aaX
section
namespace aR.Ld
open Real MeasureTheory
open scoped ArithmeticFunction.sigma CompactlySupported Convolution ContDiff
namespace RiemannHypothesis
noncomputable def weilArchimedean (f : ℝ → ℝ) : ℝ :=
  ((4 * π).log + eulerMascheroniConstant) * f 0 +
    ∫ x in Set.Ioi 0, (f x + f (-x) - 2 * exp (-x / 2) * f 0) * exp (x / 2) / (exp x - exp (-x))
noncomputable def weilNonArchimedean (p : ℕ) (f : ℝ → ℝ) : ℝ :=
    log p * ∑' m : ℕ, exp (-(m + 1) * log p / 2) * (f ((m + 1) * log p) + f (-(m + 1) * log p))
def IsTestFunction (g : ℝ → ℝ) : Prop := ∫ x, g x * exp (x / 2) = 0 ∧ ∫ x, g x * exp (-x / 2) = 0
end RiemannHypothesis
end aR.Ld
end

-- aR.vZ
section
noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real Convolution
namespace aR.vZ
open Zeta23 Zeta23.EF aR.tP aR.Weil
open aR.Ld.RiemannHypothesis (weilArchimedean weilNonArchimedean IsTestFunction)
def JQ (k : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))
theorem Cu {k : ℝ → ℂ} (hk2 : ContDiff ℝ 2 k) (bD : HasCompactSupport k) :
    bU k = aD k (I / 2) + aD k (-I / 2) - JQ k - DX k := by
  rw [bU, nP, yI hk2 bD, JQ]
  ring
lemma NZ (G : ℝ → ℝ) : DX (fun x => (G x : ℂ)) = (weilArchimedean G : ℂ) := by
  rw [DX, weilArchimedean]
  conv_rhs => rw [Complex.ofReal_add, Complex.ofReal_mul, ← integral_complex_ofReal]
  push_cast
  rfl
lemma fO (G : ℝ → ℝ) :
    aD (fun x => (G x : ℂ)) (I / 2) = ((∫ x, G x * Real.exp (-x / 2) : ℝ) : ℂ) := by
  rw [aD, ← integral_complex_ofReal]
  congr 1; ext u
  have : I * (I / 2) * (u : ℂ) = ((-u / 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [this, ← Complex.ofReal_exp]
  push_cast; ring
lemma eo (G : ℝ → ℝ) :
    aD (fun x => (G x : ℂ)) (-I / 2) = ((∫ x, G x * Real.exp (x / 2) : ℝ) : ℂ) := by
  rw [aD, ← integral_complex_ofReal]
  congr 1; ext u
  have : I * (-I / 2) * (u : ℂ) = ((u / 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [this, ← Complex.ofReal_exp]
  push_cast; ring
lemma qV (G : ℝ → ℝ) :
    IsTestFunction G ↔ aD (fun x => (G x : ℂ)) (I / 2) = 0 ∧ aD (fun x => (G x : ℂ)) (-I / 2) = 0 := by
  rw [fO, eo, Complex.ofReal_eq_zero, Complex.ofReal_eq_zero,
    IsTestFunction, and_comm]
lemma GJ {G : ℝ → ℝ} (hG : HasCompactSupport G) :
    ∃ N : ℕ, ∀ n, N ≤ n → ArithmeticFunction.vonMangoldt n / Real.sqrt n * (G (Real.log n) + G (-Real.log n)) = 0 := by
  obtain ⟨R, hR⟩ := hG.isCompact.isBounded.subset_closedBall 0
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp R)
  refine ⟨N, fun n hn => ?_⟩
  have hn' : Real.exp R < n := lt_of_lt_of_le hN (by exact_mod_cast hn)
  have hpos : (0 : ℝ) < n := (Real.exp_pos R).trans hn'
  have hlog : R < Real.log n := by rw [Real.lt_log_iff_exp_lt hpos]; exact hn'
  have hz : ∀ y : ℝ, R < |y| → G y = 0 := by
    intro y hy
    by_contra h
    have := hR (subset_tsupport G h)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith
  rw [hz _ (lt_of_lt_of_le hlog (le_abs_self _)),
    hz _ (by rw [abs_neg]; exact lt_of_lt_of_le hlog (le_abs_self _))]
  ring
theorem Ow {G : ℝ → ℝ} (hG : HasCompactSupport G) :
    ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * (G (Real.log n) + G (-Real.log n))
      = ∑' p : Nat.Primes, weilNonArchimedean p G := by
  set a : ℕ → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n / Real.sqrt n * (G (Real.log n) + G (-Real.log n)) with ha
  obtain ⟨N, hN⟩ := GJ hG
  set i : Nat.Primes × ℕ → ℕ := fun q => (q.1 : ℕ) ^ (q.2 + 1) with hi
  have hinj : Function.Injective i := by
    rintro ⟨p, m⟩ ⟨q, n⟩ h
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj p.2 q.2 h
    exact Prod.ext (Subtype.ext h1) h2
  have hsupp : Function.support a ⊆ Set.range i := by
    intro n hn
    have hΛ : ArithmeticFunction.vonMangoldt n ≠ 0 := by
      intro h0; apply hn; simp only [ha, h0, zero_div, zero_mul]
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hk
    exact ⟨(⟨p, hp⟩, m), by simp [hi]⟩
  rw [← hinj.tsum_eq hsupp]
  have hfin : ∀ q ∉ (Finset.range N).preimage i hinj.injOn, a (i q) = 0 := by
    intro q hq
    rw [Finset.mem_preimage, Finset.mem_range, not_lt] at hq
    exact hN _ hq
  have hsum : Summable fun q => a (i q) := summable_of_ne_finset_zero hfin
  rw [hsum.tsum_prod' (fun p => (hsum.comp_injective (Prod.mk_right_injective p)))]
  refine tsum_congr fun p => ?_
  rw [weilNonArchimedean, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have hp := p.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  simp only [ha, hi]
  rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero m),
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlog : Real.log ((((p : ℕ) ^ (m + 1) : ℕ) : ℝ)) = ((m : ℝ) + 1) * Real.log p := by
    push_cast; rw [Real.log_pow]; push_cast; ring
  have hsqrt : Real.sqrt ((((p : ℕ) ^ (m + 1) : ℕ) : ℝ)) = Real.exp (((m : ℝ) + 1) * Real.log p / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by exact_mod_cast pow_pos hp.pos _), hlog]
    ring_nf
  rw [hlog, hsqrt, div_eq_mul_inv, ← Real.exp_neg]
  ring_nf
lemma LY {G : ℝ → ℝ} (hG : HasCompactSupport G) :
    JQ (fun x => (G x : ℂ)) = ((∑' p : Nat.Primes, weilNonArchimedean p G : ℝ) : ℂ) := by
  rw [← Ow hG, JQ, Complex.ofReal_tsum]
  push_cast
  rfl
lemma wS (a b : ℝ → ℝ) (x : ℝ) :
    gO (fun u => (a u : ℂ)) (fun u => (b u : ℂ)) x = ((∫ t, a t * b (t - x) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  simp only [gO, convolution_def, ContinuousLinearMap.mul_apply', tilde, neg_sub, Complex.conj_ofReal]
  push_cast
  rfl
lemma Lh (g : ℝ → ℝ) (x : ℝ) : (g ⋆ fun y => g (-y)) x = ∫ t, g t * g (t - x) := by
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, neg_sub]
lemma EI (g : ℝ → ℝ) :
    dK (fun u => (g u : ℂ)) = fun x => (((g ⋆ fun y => g (-y)) x : ℝ) : ℂ) := by
  funext x
  rw [dK, wS, Lh]
end aR.vZ
end
end

-- aR.acr
section
noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate ContDiff Convolution CompactlySupported
namespace aR.qJ
open Zeta23 Zeta23.EF aR.tP aR.Weil aR.vZ
open aR.Ld.RiemannHypothesis (weilArchimedean weilNonArchimedean IsTestFunction)
def Q (G : ℝ → ℝ) : ℝ := weilArchimedean G + ∑' p : Nat.Primes, weilNonArchimedean p G
def Test (f : ℝ → ℂ) : Prop := aD f (I / 2) = 0 ∧ aD f (-I / 2) = 0
lemma kD {G : ℝ → ℝ} (hk2 : ContDiff ℝ 2 (fun x => (G x : ℂ)))
    (bD : HasCompactSupport (fun x => (G x : ℂ))) :
    bU (fun x => (G x : ℂ))
      = (((∫ x, G x * Real.exp (-x / 2)) + (∫ x, G x * Real.exp (x / 2)) - Q G : ℝ) : ℂ) := by
  have hG : HasCompactSupport G := by
    have := bD.comp_left (g := Complex.re) (by simp)
    simpa [Function.comp_def] using this
  rw [Cu hk2 bD, fO, eo, LY hG,
    NZ, Q]
  push_cast; ring
lemma iF {n : WithTop ℕ∞} {a : ℝ → ℝ} (ha : ContDiff ℝ n a) :
    ContDiff ℝ n (fun x => (a x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp ha
lemma dM {a : ℝ → ℝ} (ha : HasCompactSupport a) :
    HasCompactSupport (fun x => (a x : ℂ)) :=
  ha.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero
theorem pI {a : ℝ → ℝ} (ha : ContDiff ℝ 2 a) (hac : HasCompactSupport a)
    (ht : Test (fun x => (a x : ℂ))) :
    bU (dK (fun x => (a x : ℂ))) = -((Q (a ⋆ fun y => a (-y)) : ℝ) : ℂ) := by
  have hA := iF ha
  have hAc := dM hac
  have hk2 := BW hA hAc
  have bD := qC (f := fun x => (a x : ℂ)) hAc
  have hz : ∀ z : ℂ, z = I / 2 ∨ z = -I / 2 → aD (dK (fun x => (a x : ℂ))) z = 0 := by
    intro z hz
    rw [dK, vk hA.continuous hA.continuous hAc hAc]
    rcases hz with rfl | rfl
    · rw [ht.1, zero_mul]
    · rw [ht.2, zero_mul]
  have e1 := hz _ (Or.inl rfl)
  have e2 := hz _ (Or.inr rfl)
  rw [EI] at hk2 bD e1 e2 ⊢
  rw [kD hk2 bD]
  rw [fO, Complex.ofReal_eq_zero] at e1
  rw [eo, Complex.ofReal_eq_zero] at e2
  rw [e1, e2]; push_cast; ring
lemma Ox {a b : ℝ → ℝ} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b) :
    (Z.W (fun x => (a x : ℂ)) (fun x => (b x : ℂ))).im = 0 := by
  have hA := iF ha
  have hB := iF hb
  have hAc := dM hac
  have hBc := dM hbc
  have hk2 := jN hA hB.continuous hAc
  have bD := fD hAc hBc
  rw [← kP hA hB hAc hBc]
  have e : gO (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) = fun x => ((∫ t, a t * b (t - x) : ℝ) : ℂ) :=
    funext (wS a b)
  rw [e] at hk2 bD ⊢
  rw [kD hk2 bD, Complex.ofReal_im]
lemma EK (f : ℝ → ℂ) :
    aD f (I / 2) = ∫ x, f x * (Real.exp (-x / 2) : ℂ) := by
  rw [aD]; congr 1; ext u
  have : I * (I / 2) * (u : ℂ) = ((-u / 2 : ℝ) : ℂ) := by push_cast; ring_nf; rw [I_sq]; ring
  rw [this, ← Complex.ofReal_exp]
lemma zL (f : ℝ → ℂ) :
    aD f (-I / 2) = ∫ x, f x * (Real.exp (x / 2) : ℂ) := by
  rw [aD]; congr 1; ext u
  have : I * (-I / 2) * (u : ℂ) = ((u / 2 : ℝ) : ℂ) := by push_cast; ring_nf; rw [I_sq]; ring
  rw [this, ← Complex.ofReal_exp]
lemma qW {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (c : ℝ) :
    Integrable (fun x : ℝ => f x * (Real.exp (c * x) : ℂ)) :=
  (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
lemma QV {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (ht : Test f) :
    Test (fun x => ((f x).re : ℂ)) ∧ Test (fun x => ((f x).im : ℂ)) := by
  have i1 := qW hf hfc (-1 / 2)
  have i2 := qW hf hfc (1 / 2)
  have e1 : ∀ x : ℝ, -1 / 2 * x = -x / 2 := fun x => by ring
  have e2 : ∀ x : ℝ, 1 / 2 * x = x / 2 := fun x => by ring
  simp only [e1, e2] at i1 i2
  obtain ⟨h1, h2⟩ := ht
  rw [EK] at h1
  rw [zL] at h2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [fO, Complex.ofReal_eq_zero]
    have := integral_re i1; rw [h1] at this
    simp only [RCLike.re_to_complex, Complex.re_mul_ofReal, Complex.zero_re] at this
    exact this
  · rw [eo, Complex.ofReal_eq_zero]
    have := integral_re i2; rw [h2] at this
    simp only [RCLike.re_to_complex, Complex.re_mul_ofReal, Complex.zero_re] at this
    exact this
  · rw [fO, Complex.ofReal_eq_zero]
    have := integral_im i1; rw [h1] at this
    simp only [RCLike.im_to_complex, Complex.im_mul_ofReal, Complex.zero_im] at this
    exact this
  · rw [eo, Complex.ofReal_eq_zero]
    have := integral_im i2; rw [h2] at this
    simp only [RCLike.im_to_complex, Complex.im_mul_ofReal, Complex.zero_im] at this
    exact this
def aaY {a : ℝ → ℝ} (ha : Continuous a) (hac : HasCompactSupport a) : C_c(ℝ, ℝ) := ⟨⟨a, ha⟩, hac⟩
theorem JR
    (hFC : ∀ g : C_c(ℝ, ℝ), ContDiff ℝ ∞ g → IsTestFunction g → Q (g ⋆ fun x ↦ g (-x)) ≤ 0)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (ht : Test f) :
    0 ≤ (bU (dK f)).re := by
  set a : ℝ → ℝ := fun x => (f x).re with QW
  set b : ℝ → ℝ := fun x => (f x).im with Mh
  have ha : ContDiff ℝ ∞ a := Complex.reCLM.contDiff.comp hf
  have hb : ContDiff ℝ ∞ b := Complex.imCLM.contDiff.comp hf
  have hac : HasCompactSupport a := hfc.comp_left (g := Complex.re) Complex.zero_re
  have hbc : HasCompactSupport b := hfc.comp_left (g := Complex.im) Complex.zero_im
  have ha2 := cZ (iF ha)
  have hb2 := cZ (iF hb)
  have aaZ : ContDiff ℝ 2 a := ha.of_le (WithTop.coe_le_coe.2 le_top)
  have hb2' : ContDiff ℝ 2 b := hb.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨hta, htb⟩ := QV hf.continuous hfc ht
  have hsplit : f = fun u => (a u : ℂ) + I * (b u : ℂ) := by
    funext u; simp only [QW, Mh]; rw [mul_comm]; exact (Complex.re_add_im (f u)).symm
  have hQ : ∀ (c : ℝ → ℝ), ContDiff ℝ ∞ c → HasCompactSupport c → Test (fun x => (c x : ℂ)) →
      0 ≤ (bU (dK (fun x => (c x : ℂ)))).re := by
    intro c hc hcc htc
    rw [pI (hc.of_le (WithTop.coe_le_coe.2 le_top)) hcc htc, Complex.neg_re,
      Complex.ofReal_re, neg_nonneg]
    have := hFC (aaY hc.continuous hcc) hc ((qV c).2 htc)
    exact this
  have hW : bU (dK f)
      = bU (dK (fun x => (a x : ℂ))) + bU (dK (fun x => (b x : ℂ))) := by
    have XP : HasCompactSupport (fun x => (a x : ℂ)) := dM hac
    have hgc' : HasCompactSupport (fun x => (b x : ℂ)) := dM hbc
    rw [dO ha2 XP, dO hb2 hgc', hsplit,
      dO (by rw [← hsplit]; exact cZ hf)
        (by rw [← hsplit]; exact hfc),
      JO ha2 hb2 XP hgc', Se (fun x => (a x : ℂ)) (fun x => (b x : ℂ))]
    have hr := Ox aaZ hb2' hac hbc
    set w := Z.W (fun x => (a x : ℂ)) (fun x => (b x : ℂ))
    have hw : conj w = w := Complex.conj_eq_iff_im.2 hr
    rw [hw, Complex.conj_I]
    have : I * -I = 1 := by rw [mul_neg, I_mul_I, neg_neg]
    rw [this]; ring
  rw [hW, Complex.add_re]
  exact add_nonneg (hQ a ha hac hta) (hQ b hb hbc htb)
lemma Oy {φ : ℝ → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) (ht : Test φ) (t : ℝ) (c : ℂ) :
    Test (fun u => tr t φ u + c * φ u) := by
  have htr : Continuous (tr t φ) := hφ.comp (continuous_id.sub continuous_const)
  constructor
  · rw [gT htr hφ (dQ hφc t) hφc, jZ, ht.1]; ring
  · rw [gT htr hφ (dQ hφc t) hφc, jZ, ht.2]; ring
lemma EO (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f → Test f →
      0 ≤ (bU (dK f)).re)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (Uh : Test φ) (t : ℝ) :
    ‖Z.W (tr t φ) φ‖ ≤ (Z.W φ φ).re := by
  have hφ2 := cZ hφ
  have abb := cZ (kH hφ t)
  have XQ := dQ hφc t
  have abd : Z.W (tr t φ) (tr t φ) = Z.W φ φ := by
    unfold aV.W; exact tsum_congr fun ρ => Lc φ t ρ
  apply qQ
  intro c
  have hF : ContDiff ℝ ∞ (fun u => tr t φ u + c * φ u) := (kH hφ t).add (contDiff_const.mul hφ)
  have hFc : HasCompactSupport (fun u => tr t φ u + c * φ u) := XQ.add (hφc.mul_left)
  have h := hpos _ hF hFc (Oy hφ.continuous hφc Uh t c)
  rw [dO (cZ hF) hFc,
    JO abb hφ2 XQ hφc, abd, Se (tr t φ) φ] at h
  exact h
def mult (z : ℂ) : ℂ := cexp (I * z * ((-1 : ℝ) : ℂ)) + 1 * cexp (I * z * ((1 : ℝ) : ℂ)) + (-2 * Complex.cosh (1 / 2))
lemma mult_eq (z : ℂ) : mult z = 2 * (Complex.cos z - Complex.cos (1 / 2 * I)) := by
  rw [mult, Complex.cos_mul_I, Complex.cos]
  push_cast
  ring_nf
lemma Oz : mult (I / 2) = 0 := by
  rw [mult_eq, show I / 2 = 1 / 2 * I by ring]; ring
lemma JT : mult (-I / 2) = 0 := by
  rw [mult_eq, show -I / 2 = -(1 / 2 * I) by ring, Complex.cos_neg]; ring
lemma mult_ne_zero {z : ℂ} (hz : |z.im| < 1 / 2) : mult z ≠ 0 := by
  rw [mult_eq]
  intro h
  have h' : Complex.cos z = Complex.cos (1 / 2 * I) := by
    have := mul_eq_zero.1 h
    rcases this with h2 | h2
    · norm_num at h2
    · exact sub_eq_zero.1 h2
  obtain ⟨k, hk | hk⟩ := Complex.cos_eq_cos_iff.1 h'
  · have := congrArg Complex.im hk
    simp at this
    rw [abs_lt] at hz; linarith
  · have := congrArg Complex.im hk
    simp at this
    rw [abs_lt] at hz; linarith
lemma QX (ρ : ℂ) : (aF ρ).im = 1 / 2 - ρ.re := by
  have h := congrArg Complex.re (Bd ρ)
  simp at h
  linarith
theorem kS
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f → Test f →
      0 ≤ (bU (dK f)).re) : RiemannHypothesis := by
  intro s hs htriv hs1
  have vE : 0 < s.re ∧ s.re < 1 := by
    rcases (vV.wJ s).1 hs with h | h
    · exact absurd h htriv
    · exact ⟨h.1, h.2.1⟩
  by_contra hne
  obtain ⟨ρ₀, acu⟩ : ∃ ρ : Z.carrier, 1 / 2 < (ρ : ℂ).re := by
    have UE : s ∈ Z.carrier := ⟨hs, vE⟩
    rcases lt_or_gt_of_ne hne with h | h
    · refine ⟨⟨reflect s, Z.qH s UE⟩, ?_⟩
      show 1 / 2 < (1 - (starRingEnd ℂ) s).re
      rw [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
    · exact ⟨⟨s, UE⟩, h⟩
  have Ml : (ρ₀ : ℂ).re < 1 := ρ₀.2.2.2
  have hz0 : |(aF ρ₀).im| < 1 / 2 := by
    rw [QX, abs_lt]; constructor <;> linarith
  have hw0 : |(conj (aF ρ₀)).im| < 1 / 2 := by
    rw [Complex.conj_im, abs_neg]; exact hz0
  obtain ⟨φ₀, hφ₀, tW, hz, hw⟩ := Cj (aF ρ₀) (conj (aF ρ₀))
  set φ₁ : ℝ → ℂ := fun u => tr (-1) φ₀ u + 1 * tr 1 φ₀ u with hφ₁
  set φ : ℝ → ℂ := fun u => φ₁ u + (-2 * Complex.cosh (1 / 2)) * φ₀ u with XR
  have OV : ContDiff ℝ ∞ φ₁ := (kH hφ₀ _).add (contDiff_const.mul (kH hφ₀ _))
  have OW : HasCompactSupport φ₁ := (dQ tW _).add (dQ tW _).mul_left
  have hφ : ContDiff ℝ ∞ φ := OV.add (contDiff_const.mul hφ₀)
  have hφc : HasCompactSupport φ := OW.add tW.mul_left
  have hFT : ∀ z, aD φ z = mult z * aD φ₀ z := by
    intro z
    rw [XR, gT OV.continuous hφ₀.continuous OW tW, hφ₁,
      gT (kH hφ₀ _).continuous (kH hφ₀ _).continuous
        (dQ tW _) (dQ tW _), jZ, jZ, mult]
    ring
  have Uh : Test φ := ⟨by rw [hFT, Oz, zero_mul], by rw [hFT, JT, zero_mul]⟩
  have hzφ : aD φ (aF ρ₀) ≠ 0 := by rw [hFT]; exact mul_ne_zero (mult_ne_zero hz0) hz
  have abe : aD φ (conj (aF ρ₀)) ≠ 0 := by rw [hFT]; exact mul_ne_zero (mult_ne_zero hw0) hw
  have hφ2 := cZ hφ
  set a : Z.carrier → ℂ := fun ρ => Z.dD φ φ ρ with QW
  have ha : Summable fun ρ => ‖a ρ‖ := summable_norm_iff.2 (iJ hφ2 hφ2 hφc hφc)
  have ZD : ∀ t : ℝ, ∑' ρ : Z.carrier, a ρ * cexp (((ρ : ℂ) - 1 / 2) * t) = Z.W (tr t φ) φ := by
    intro t
    unfold aV.W
    exact tsum_congr fun ρ => (GI φ t ρ).symm
  have hzero := zK (fun ρ : Z.carrier => (ρ : ℂ) - 1 / 2) a
    (fun ρ ρ' h => Subtype.ext (by simpa using h))
    (fun ρ => by
      have h := Z.strip ρ ρ.2
      rw [abs_le]; simp only [sub_re, one_div, inv_re, re_ofNat, normSq_ofNat]
      constructor <;> norm_num <;> linarith [h.1, h.2])
    Ov ha (B := (Z.W φ φ).re)
    (fun t _ => by rw [ZD]; exact EO hpos hφ hφc Uh t) ρ₀
    (by simp only [sub_re, one_div, inv_re, re_ofNat, normSq_ofNat]; norm_num; linarith)
  have hm : (Z.mult ρ₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := Z.one_le_mult ρ₀ ρ₀.2; omega)
  have : a ρ₀ ≠ 0 := by
    simp only [QW, aV.dD]
    exact mul_ne_zero (mul_ne_zero hm hzφ) ((map_ne_zero _).2 abe)
  exact this hzero
theorem Lj (hRH : RiemannHypothesis) (g : C_c(ℝ, ℝ)) (hg : ContDiff ℝ ∞ g)
    (ht : IsTestFunction g) : Q (g ⋆ fun x ↦ g (-x)) ≤ 0 := by
  have hg2 : ContDiff ℝ 2 (g : ℝ → ℝ) := hg.of_le (WithTop.coe_le_coe.2 le_top)
  have h := mK hRH (cZ (iF hg))
    (dM g.hasCompactSupport)
  rw [pI hg2 g.hasCompactSupport ((qV g).1 ht),
    ← Complex.ofReal_neg, Complex.zero_le_real] at h
  linarith
end aR.qJ
namespace aR.Ld
open Real MeasureTheory
open scoped ArithmeticFunction.sigma CompactlySupported Convolution ContDiff
namespace RiemannHypothesis
theorem weil_positivity_criterion :
    RiemannHypothesis ↔ ∀ g : C_c(ℝ, ℝ), ContDiff ℝ ∞ g → IsTestFunction g →
      weilArchimedean (g ⋆ fun x ↦ g (-x)) +
        ∑' p : Nat.Primes, weilNonArchimedean p (g ⋆ fun x ↦ g (-x)) ≤ 0 := by
  constructor
  · exact fun hRH g hg ht => aR.qJ.Lj hRH g hg ht
  · intro h
    exact aR.qJ.kS fun f hf hfc ht =>
      aR.qJ.JR h hf hfc ht
end RiemannHypothesis
end aR.Ld
end
end

theorem OMA.solution : type_of% @RiemannHypothesis.weil_positivity_criterion :=
  aR.Ld.RiemannHypothesis.weil_positivity_criterion
