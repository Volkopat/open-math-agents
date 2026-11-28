import FormalConjectures.ErdosProblems.«393»

/-!
# Berend–Osgood density zero for the polynomial-factorial family

Reduction for `erdos_393.variants.berend_osgood`.

The target: for every `m`, the set `{n | f n = m}` has density zero.

- `H1` is the Berend–Osgood density-zero theorem for the family of polynomials
  `prod_{j in S} (X + j)` (degree ≥ 2): for each `m ≥ 1` and each `S ⊆ [0, m]`
  containing `0` and `m`, the set of `n` with `exists a, prod_{j in S}(a + j) = n!`
  has density zero. This is the deep step (G-functions, Chudnovsky) and is not
  in Mathlib.
- `H2` is the factorial-set characterization: for `m ≥ 1`, `f n = m` gives
  `exists S, exists a, S ⊆ [0, m], 0 ∈ S, m ∈ S, prod_{j in S}(a + j) = n!`.

`main` proves the target from `H1 → H2`: the `m = 0` case is finite (junk values),
and the `m ≥ 1` case is a finite union of density-zero sets (each Sol(S) is
density zero by `H1` and finite unions preserve density zero).
-/

namespace OMA.R_Erdos393_erdos_393_variants_berend_osgood_R1

open scoped Nat
open Filter

def H1 : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ S : Finset ℕ, S ⊆ Finset.Icc 0 m → 0 ∈ S → m ∈ S →
    {n : ℕ | ∃ a : ℕ, ∏ j ∈ S, (a + j) = n !}.HasDensity 0

def H2 : Prop :=
  ∀ m n : ℕ, 1 ≤ m → Erdos393.f n = m →
    ∃ a : ℕ, ∃ S : Finset ℕ, S ⊆ Finset.Icc 0 m ∧ 0 ∈ S ∧ m ∈ S ∧ ∏ j ∈ S, (a + j) = n !

/-- Finite unions of density-zero sets are density zero. -/
lemma union_hasDensity_zero (valid : Finset (Finset ℕ)) (F : Finset ℕ → Set ℕ)
    (hF : ∀ S ∈ valid, (F S).HasDensity 0) :
    (⋃ S ∈ valid, F S).HasDensity 0 := by
  have hbound : ∀ b : ℕ,
      ((⋃ S ∈ valid, F S) ∩ Set.Iio b).ncard ≤ ∑ S ∈ valid, (F S ∩ Set.Iio b).ncard := by
    intro b
    have hst : ((⋃ S ∈ valid, F S) ∩ Set.Iio b) = ⋃ S ∈ valid, (F S ∩ Set.Iio b) := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxS, hxb⟩ := hx
        obtain ⟨S, hxS'⟩ := Set.mem_iUnion.mp hxS
        obtain ⟨hSmem, hxSol⟩ := Set.mem_iUnion.mp hxS'
        exact Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨hSmem, ⟨hxSol, hxb⟩⟩⟩
      · intro hx
        obtain ⟨S, hxS'⟩ := Set.mem_iUnion.mp hx
        obtain ⟨hSmem, h⟩ := Set.mem_iUnion.mp hxS'
        obtain ⟨hxSol, hxb⟩ := h
        exact ⟨Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨hSmem, hxSol⟩⟩, hxb⟩
    rw [hst]
    exact Finset.set_ncard_biUnion_le valid _
  have hsum_aux : ∀ J : Finset (Finset ℕ), (∀ S ∈ J, (F S).HasDensity 0) →
      Tendsto (fun b : ℕ => ∑ S ∈ J, ((F S ∩ Set.Iio b).ncard / (Set.Iio b).ncard : ℝ)) atTop (nhds 0) := by
    intro J
    induction J using Finset.induction with
    | empty => intro _; simp
    | insert x s hx ih =>
      intro hJ
      simp only [Finset.sum_insert hx]
      have hx_dens : (F x).HasDensity 0 := hJ x (Finset.mem_insert.mpr (Or.inl rfl))
      simp only [Set.HasDensity, Set.partialDensity, Set.inter_univ, Set.univ_inter] at hx_dens
      have h := hx_dens.add (ih (fun S hS => hJ S (Finset.mem_insert.mpr (Or.inr hS))))
      simpa using h
  have hsum : Tendsto (fun b : ℕ => ∑ S ∈ valid, ((F S ∩ Set.Iio b).ncard / (Set.Iio b).ncard : ℝ)) atTop (nhds 0) :=
    hsum_aux valid hF
  set U : Set ℕ := ⋃ S ∈ valid, F S with hU
  simp only [Set.HasDensity, Set.partialDensity, Set.inter_univ, Set.univ_inter]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum ?_ ?_
  · exact fun b => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro b
    by_cases hb : b = 0
    · simp [hb]
    · have hpos : 0 < (Set.Iio b).ncard := by
        rw [Set.ncard_Iio_nat]
        exact Nat.pos_of_ne_zero hb
      have hnum : ((U ∩ Set.Iio b).ncard) ≤ ∑ S ∈ valid, (F S ∩ Set.Iio b).ncard := hbound b
      have hnumℝ : ((U ∩ Set.Iio b).ncard : ℝ) ≤ ∑ S ∈ valid, ((F S ∩ Set.Iio b).ncard : ℝ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast hnum
      calc ((U ∩ Set.Iio b).ncard / (Set.Iio b).ncard : ℝ)
          ≤ (∑ S ∈ valid, ((F S ∩ Set.Iio b).ncard : ℝ)) / (Set.Iio b).ncard :=
            div_le_div₀ (by positivity) hnumℝ (Nat.cast_pos.mpr hpos) le_rfl
        _ = ∑ S ∈ valid, ((F S ∩ Set.Iio b).ncard / (Set.Iio b).ncard : ℝ) := by
            rw [Finset.sum_div]

/-- A subset of a density-zero set is density zero. -/
lemma hasDensity_zero_of_subset {s t : Set ℕ} (hs : s ⊆ t) (ht : t.HasDensity 0) :
    s.HasDensity 0 := by
  simp only [Set.HasDensity, Set.partialDensity, Set.inter_univ, Set.univ_inter]
  simp only [Set.HasDensity, Set.partialDensity, Set.inter_univ, Set.univ_inter] at ht
  have hbound : ∀ b : ℕ, ((s ∩ Set.Iio b).ncard / (Set.Iio b).ncard : ℝ) ≤ ((t ∩ Set.Iio b).ncard / (Set.Iio b).ncard : ℝ) := by
    intro b
    by_cases hb : b = 0
    · simp [hb]
    · have hst : s ∩ Set.Iio b ⊆ t ∩ Set.Iio b := fun x hx => ⟨hs hx.1, hx.2⟩
      have hpos : 0 < (Set.Iio b).ncard := by
        rw [Set.ncard_Iio_nat]
        exact Nat.pos_of_ne_zero hb
      have hnum : (s ∩ Set.Iio b).ncard ≤ (t ∩ Set.Iio b).ncard :=
        Set.ncard_le_ncard hst
      exact div_le_div₀ (by positivity) (by exact_mod_cast hnum) (Nat.cast_pos.mpr hpos) le_rfl
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hbound

theorem main : H1 → H2 → type_of% @Erdos393.erdos_393.variants.berend_osgood := by
  intro H1 H2 m
  by_cases hm : m = 0
  · subst hm
    have hsub : {n : ℕ | Erdos393.f n = 0} ⊆ {0, 1} := by
      intro n hn
      by_cases hn2 : 2 ≤ n
      · have h := Erdos393.one_le_f n hn2
        rw [hn] at h
        exact absurd h (by omega)
      · interval_cases n <;> simp
    have hfin : {n : ℕ | Erdos393.f n = 0}.Finite := by
      have hfin1 : ({0, 1} : Set ℕ).Finite :=
        Set.Finite.insert 0 (Set.finite_singleton 1)
      exact hfin1.subset hsub
    exact Nat.hasDensity_zero_of_finite hfin
  · have hm' : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    set valid : Finset (Finset ℕ) :=
      Finset.filter (fun S => 0 ∈ S ∧ m ∈ S) (Finset.powerset (Finset.Icc 0 m)) with hvalid
    have hcl : {n : ℕ | Erdos393.f n = m} ⊆
        ⋃ S ∈ valid, {n : ℕ | ∃ a : ℕ, ∏ j ∈ S, (a + j) = n !} := by
      intro n hn
      obtain ⟨a, S, hS, h0, hmI, hprod⟩ := H2 m n hm' hn
      have hSpowerset : S ∈ Finset.powerset (Finset.Icc 0 m) := Finset.mem_powerset.mpr hS
      have hSm' : S ∈ valid := Finset.mem_filter.mpr ⟨hSpowerset, h0, hmI⟩
      exact Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨hSm', ⟨a, hprod⟩⟩⟩
    have hunion : (⋃ S ∈ valid, {n : ℕ | ∃ a : ℕ, ∏ j ∈ S, (a + j) = n !} : Set ℕ).HasDensity 0 :=
      union_hasDensity_zero valid (fun S => {n : ℕ | ∃ a : ℕ, ∏ j ∈ S, (a + j) = n !}) (fun S hS => by
        obtain ⟨hSpowerset, h0, hmI⟩ := Finset.mem_filter.mp hS
        exact H1 m hm' S (Finset.mem_powerset.mp hSpowerset) h0 hmI)
    exact hasDensity_zero_of_subset hcl hunion

end OMA.R_Erdos393_erdos_393_variants_berend_osgood_R1
