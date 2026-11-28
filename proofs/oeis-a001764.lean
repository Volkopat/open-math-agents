import OMAStatements.S_oeis_a001764
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Mathlib.Data.Finset.Sort

/-!
# OEIS A001764

The terminal-ascent count follows from the strict jump queue recurrences.
The indecomposable count follows from the PermPAL specification and tracked fusion.

* Strict jump queues: https://www.cs.otago.ac.nz/research/publications/oucs-2002-10.pdf
* PermPAL specification: https://permpal.com/perms/basis/0231_02143/
* Rule certificate: https://permpal.com/perms/raw_data/23600
-/

section

namespace A001764

open OMA.S_oeis_a001764
open scoped BigOperators

/-- The algebra in the final-ascent refinement of the strict jump queue.
These are the two generating-function equations with denominators cleared. -/
theorem ascentKernel {R : Type*} [CommRing R] [IsDomain R]
    {x t c l u f : R} (ht : t ≠ 0) (hz : 1 + x^2*c^3 ≠ 0)
    (hcat : c = 1 + x * c^2) (hroot : x = t * c)
    (hl : x * l = t * (l - f) + x^2 * u + x^2 * t)
    (hu : u = l + x * c * (u - f) + x^2 * c) :
    f = t * (c - 1) := by
  have hunit : c * (1 - x * c) = 1 := by
    linear_combination hcat
  have hkernel : (x - t) * (1 - x * c) - x^2 = 0 := by
    linear_combination (1 - x*c - x)*hroot + t*hunit
  have hbalance : (t * (1 - x*c) + x^3*c) * f =
      x^4*c + x^2*t*(1 - x*c) := by
    linear_combination (1 - x*c)*hl + x^2*hu - l*hkernel
  have htrial : (t * (1 - x*c) + x^3*c) * (x^2*c) =
      x^4*c + x^2*t*(1 - x*c) := by
    linear_combination (-x^3*c*(1 - x*c))*hroot + (x^2*t - x^3*c*t)*hunit
  have hidentity : (t * (1 - x*c) + x^3*c) * c = t * (1 + x^2*c^3) := by
    linear_combination t*hunit + x^2*c^2*hroot
  have hpower : x^2*c = t * (c - 1) := by
    linear_combination (x*c)*hroot - t*hcat
  have nonzero : t * (1 - x*c) + x^3*c ≠ 0 := by
    intro h
    rw [h, zero_mul] at hidentity
    exact (mul_ne_zero ht hz) hidentity.symm
  exact (mul_left_cancel₀ nonzero (hbalance.trans htrial.symm)).trans hpower

/-- A formal power series instance of the queue kernel. -/
theorem ascentSeriesKernel {x c l u f : PowerSeries ℤ}
    (hcat : c = 1 + x * c^2) (hroot : x = PowerSeries.X * c)
    (hl : x * l = PowerSeries.X * (l - f) + x^2 * u + x^2 * PowerSeries.X)
    (hu : u = l + x * c * (u - f) + x^2 * c) :
    f = PowerSeries.X * (c - 1) := by
  apply ascentKernel PowerSeries.X_ne_zero _ hcat hroot hl hu
  intro hz
  have hx : PowerSeries.constantCoeff x = 0 := by simp [hroot]
  have hh := congrArg (PowerSeries.constantCoeff (R := ℤ)) hz
  simp [hx] at hh

/-- The PermPAL cubic yields the ternary-tree equation for the shifted
indecomposable series once the first-block factorization is given. -/
theorem cubicToTernary {R : Type*} [CommRing R] [IsDomain R] {t F J : R}
    (ht : t ≠ 0) (hsum : F * (1 - t*J) = 1)
    (hpoly : (t^2 - t + 1) * F^3 + (t - 3) * F^2 + 3 * F - 1 = 0) :
    J = 1 + t*J^3 := by
  let z := 1 - t*J
  have hz : F*z = 1 := hsum
  have hnorm : (t^2 - t + 1) + (t-3)*z + 3*z^2 - z^3 = 0 := by
    calc
      _ = (t^2 - t + 1)*(F*z)^3 + (t-3)*(F*z)^2*z + 3*(F*z)*z^2 - z^3 := by
        rw [hz]
        ring
      _ = z^3 * ((t^2 - t + 1) * F^3 + (t - 3) * F^2 + 3 * F - 1) := by ring
      _ = 0 := by rw [hpoly, mul_zero]
  have hfactored : t^2 * (t*J^3 - J + 1) = 0 := by
    dsimp [z] at hnorm
    linear_combination hnorm
  have ht' := (mul_eq_zero.mp hfactored).resolve_left (pow_ne_zero 2 ht)
  linear_combination -ht'

/-- A series satisfying the ternary-tree equation is unique. -/
theorem ternarySeriesUnique {u v : PowerSeries ℤ}
    (hu : u = 1 + PowerSeries.X*u^3) (hv : v = 1 + PowerSeries.X*v^3) : u = v := by
  have hz : (u - v) * (1 - PowerSeries.X*(u^2 + u*v + v^2)) = 0 := by
    linear_combination hu - hv
  have hf : 1 - PowerSeries.X*(u^2 + u*v + v^2) ≠ 0 := by
    intro he
    have hh := congrArg (PowerSeries.constantCoeff (R := ℤ)) he
    simp at hh
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hf)

def reversePermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  Fin.revPerm.trans σ

theorem reversePermutation_involutive (n : ℕ) :
    Function.Involutive (@reversePermutation n) := by
  intro σ
  ext i
  simp [reversePermutation, Fin.revPerm]

theorem reverseAvoids {n k : ℕ} (σ : Equiv.Perm (Fin n)) (pattern : Fin k → ℕ) :
    Avoids (reversePermutation σ) (fun i => pattern i.rev) ↔ Avoids σ pattern := by
  have backwards {π : Equiv.Perm (Fin n)} {pat : Fin k → ℕ}
      (h : ¬ Avoids π pat) : ¬ Avoids (reversePermutation π) (fun i => pat i.rev) := by
    obtain ⟨pos, hm, hp⟩ := Classical.not_not.mp h
    intro havoid
    apply havoid
    refine ⟨fun i => (pos i.rev).rev, ?_, ?_⟩
    · intro i j hij
      exact Fin.rev_lt_rev.mpr (hm (Fin.rev_lt_rev.mpr hij))
    · intro i j
      simpa [reversePermutation, Fin.revPerm] using hp i.rev j.rev
  constructor
  · intro h
    by_contra! hh
    exact backwards hh h
  · intro h
    by_contra! hh
    have hr := backwards hh
    rw [reversePermutation_involutive n σ] at hr
    exact (show ¬ Avoids σ pattern by simpa only [Fin.rev_rev] using hr) h

/-- Position reversal transfers the exact second total-avoidance class
to the class with the published PermPAL cubic. -/
theorem secondClassReverse (n : ℕ) :
    Nat.card {σ : Equiv.Perm (Fin n) // Avoids σ ![2,4,3,1] ∧ Avoids σ ![4,5,2,3,1]} =
    Nat.card {σ : Equiv.Perm (Fin n) // Avoids σ ![1,3,4,2] ∧ Avoids σ ![1,3,2,5,4]} := by
  let rev : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) :=
    ⟨reversePermutation, reversePermutation, reversePermutation_involutive n,
      reversePermutation_involutive n⟩
  have h4 : (fun i : Fin 4 => (![2,4,3,1] : Fin 4 → ℕ) i.rev) = ![1,3,4,2] := by
    funext i
    fin_cases i <;> decide
  have h5 : (fun i : Fin 5 => (![4,5,2,3,1] : Fin 5 → ℕ) i.rev) = ![1,3,2,5,4] := by
    funext i
    fin_cases i <;> decide
  apply Nat.card_congr (rev.subtypeEquiv ?_)
  intro σ
  change _ ↔ Avoids (reversePermutation σ) ![1,3,4,2] ∧
    Avoids (reversePermutation σ) ![1,3,2,5,4]
  rw [← h4, ← h5, reverseAvoids, reverseAvoids]

/-- A sum cut in the exact upstream sense separates all right-side values too. -/
theorem rightOfSumCut {n cut : ℕ} {σ : Equiv.Perm (Fin n)}
    (hleft : ∀ i : Fin n, i.val < cut → (σ i).val < cut) :
    ∀ i : Fin n, cut ≤ i.val → cut ≤ (σ i).val := by
  classical
  let low := Finset.univ.filter fun i : Fin n => i.val < cut
  have hmem (i : Fin n) : i ∈ low ↔ i.val < cut := by simp [low]
  have hsub : low.image σ ⊆ low := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact (hmem _).mpr (hleft j ((hmem _).mp hj))
  have heq : low.image σ = low :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ σ.injective])
  intro i hi
  by_contra! hvalue
  obtain ⟨j, hj, hjvalue⟩ := Finset.mem_image.mp (show σ i ∈ low.image σ by
    rw [heq]
    exact (hmem _).mpr hvalue)
  have hji := σ.injective hjvalue
  exact (not_lt_of_ge hi) (hji ▸ ((hmem _).mp hj))

/-- An occurrence whose first pattern value exceeds its last one
must be entirely on one side of any direct-sum cut. -/
theorem occurrenceOneSide {n k : ℕ} {σ : Equiv.Perm (Fin n)}
    {pattern : Fin (k+1) → ℕ} (hend : pattern (Fin.last k) < pattern 0)
    {cut : ℕ} (hleft : ∀ i : Fin n, i.val < cut → (σ i).val < cut)
    {pos : Fin (k+1) → Fin n} (hpos : StrictMono pos)
    (hpat : ∀ i j, σ (pos i) < σ (pos j) ↔ pattern i < pattern j) :
    (∀ i, (pos i).val < cut) ∨ (∀ i, cut ≤ (pos i).val) := by
  by_cases h : (pos 0).val < cut
  · left
    have hlast : (pos (Fin.last k)).val < cut := by
      by_contra! hge
      have ha := hleft (pos 0) h
      have hb := rightOfSumCut hleft (pos (Fin.last k)) hge
      have hc := (hpat (Fin.last k) 0).mpr hend
      have hd : (σ (pos (Fin.last k))).val < (σ (pos 0)).val := hc
      omega
    intro i
    have hi : i ≤ Fin.last k := Fin.le_last i
    have hbound : (pos i).val ≤ (pos (Fin.last k)).val := hpos.monotone hi
    omega
  · right
    intro i
    have hi : (pos 0).val ≤ (pos i).val := hpos.monotone (Fin.zero_le i)
    omega

/-- Inverting the first-block recurrence makes total Wilf equivalence
equivalent to equality on the sum-indecomposables. -/
theorem firstBlockUnique {totalA totalB indecA indecB : ℕ → ℕ}
    (hA0 : totalA 0 = 1) (hB0 : totalB 0 = 1)
    (hA : ∀ n, totalA (n+1) = indecA (n+1) +
      ∑ i ∈ Finset.range n, indecA (i+1) * totalA (n-i))
    (hB : ∀ n, totalB (n+1) = indecB (n+1) +
      ∑ i ∈ Finset.range n, indecB (i+1) * totalB (n-i)) :
    (∀ n, totalA n = totalB n) ↔ (∀ n, 0 < n → indecA n = indecB n) := by
  constructor
  · intro htot n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
      have hs : (∑ i ∈ Finset.range m, indecA (i+1) * totalA (m-i)) =
          ∑ i ∈ Finset.range m, indecB (i+1) * totalB (m-i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        rw [ih (i+1) (by omega) (by omega), htot]
      have hb := htot (m+1)
      rw [hA, hB, hs] at hb
      exact Nat.add_right_cancel hb
  · intro hind n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => rw [hA0, hB0]
      | succ m =>
        rw [hA, hB, hind _ (by omega)]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [hind _ (by omega), ih (m-i) (by omega)]

theorem exactPatternEnds :
    (![4, 2, 3, 1] : Fin 4 → ℕ) (Fin.last 3) < (![4, 2, 3, 1] : Fin 4 → ℕ) 0 ∧
    (![4, 2, 5, 1, 3] : Fin 5 → ℕ) (Fin.last 4) < (![4, 2, 5, 1, 3] : Fin 5 → ℕ) 0 ∧
    (![2, 4, 3, 1] : Fin 4 → ℕ) (Fin.last 3) < (![2, 4, 3, 1] : Fin 4 → ℕ) 0 ∧
    (![4, 5, 2, 3, 1] : Fin 5 → ℕ) (Fin.last 4) < (![4, 5, 2, 3, 1] : Fin 5 → ℕ) 0 := by
  decide

end A001764

end

section

namespace A001764

open OMA.S_oeis_a001764

def SumCut {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) : Prop :=
  ∀ i : Fin n, i.val < k → (σ i).val < k

def directSum {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (m+n)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr σ τ).trans finSumFinEquiv)

@[simp] theorem directSum_left {m n : ℕ}
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) (i : Fin m) :
    directSum σ τ (Fin.castAdd n i) = Fin.castAdd n (σ i) := by
  simp [directSum]

@[simp] theorem directSum_right {m n : ℕ}
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    directSum σ τ (Fin.natAdd m i) = Fin.natAdd m (τ i) := by
  simp [directSum]

theorem directSum_cut {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    SumCut (directSum σ τ) m := by
  intro i hi
  let left : Fin m := ⟨i.val, hi⟩
  have hi' : i = Fin.castAdd n left := Fin.ext rfl
  rw [hi', directSum_left]
  exact (σ left).isLt

theorem directSum_small_cut {m n k : ℕ} (hk : k ≤ m)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    SumCut (directSum σ τ) k ↔ SumCut σ k := by
  constructor
  · intro h i hi
    simpa using h (Fin.castAdd n i) hi
  · intro h i hi
    let left : Fin m := ⟨i.val, by omega⟩
    have hi' : i = Fin.castAdd n left := Fin.ext rfl
    rw [hi', directSum_left]
    exact h left hi

noncomputable def leftBlock {m n : ℕ} {σ : Equiv.Perm (Fin (m+n))}
    (h : SumCut σ m) : Equiv.Perm (Fin m) :=
  Equiv.ofBijective (fun i : Fin m => ⟨(σ (Fin.castAdd n i)).val, h _ i.isLt⟩)
    (by
      have hinj : Function.Injective (fun i : Fin m =>
          (⟨(σ (Fin.castAdd n i)).val, h _ i.isLt⟩ : Fin m)) := by
        intro i j hij
        apply Fin.ext
        have hσ : σ (Fin.castAdd n i) = σ (Fin.castAdd n j) :=
          Fin.ext (congrArg (fun t : Fin m => t.val) hij)
        exact congrArg (fun t : Fin (m+n) => t.val) (σ.injective hσ)
      exact ⟨hinj, Finite.surjective_of_injective hinj⟩)

noncomputable def rightBlock {m n : ℕ} {σ : Equiv.Perm (Fin (m+n))}
    (h : SumCut σ m) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun i : Fin n => ⟨(σ (Fin.natAdd m i)).val - m, by
      have hi := (σ (Fin.natAdd m i)).isLt
      have hlo := rightOfSumCut h (Fin.natAdd m i) (by simp)
      omega⟩)
    (by
      have hlow (i : Fin n) : m ≤ (σ (Fin.natAdd m i)).val :=
        rightOfSumCut h _ (by simp)
      have hinj : Function.Injective (fun i : Fin n =>
          (⟨(σ (Fin.natAdd m i)).val - m, by
            have hi := (σ (Fin.natAdd m i)).isLt
            have hlo := hlow i
            omega⟩ : Fin n)) := by
        intro i j hij
        have hsub : (σ (Fin.natAdd m i)).val - m = (σ (Fin.natAdd m j)).val - m :=
          congrArg Fin.val hij
        have hσ : σ (Fin.natAdd m i) = σ (Fin.natAdd m j) :=
          Fin.ext (by have := hlow i; have := hlow j; omega)
        have hval := congrArg Fin.val (σ.injective hσ)
        simp only [Fin.val_natAdd] at hval
        exact Fin.ext (by omega)
      exact ⟨hinj, Finite.surjective_of_injective hinj⟩)

@[simp] theorem cast_leftBlock {m n : ℕ} {σ : Equiv.Perm (Fin (m+n))}
    (h : SumCut σ m) (i : Fin m) :
    Fin.castAdd n (leftBlock h i) = σ (Fin.castAdd n i) :=
  Fin.ext rfl

@[simp] theorem cast_rightBlock {m n : ℕ} {σ : Equiv.Perm (Fin (m+n))}
    (h : SumCut σ m) (i : Fin n) :
    Fin.natAdd m (rightBlock h i) = σ (Fin.natAdd m i) := by
  apply Fin.ext
  change m + ((σ (Fin.natAdd m i)).val - m) = _
  have hl := rightOfSumCut h (Fin.natAdd m i) (by simp)
  omega

theorem split_directSum {m n : ℕ} {σ : Equiv.Perm (Fin (m+n))} (h : SumCut σ m) :
    directSum (leftBlock h) (rightBlock h) = σ := by
  ext i
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  cases x <;> simp

theorem directSum_injective {m n : ℕ}
    {σ σ' : Equiv.Perm (Fin m)} {τ τ' : Equiv.Perm (Fin n)}
    (h : directSum σ τ = directSum σ' τ') : σ = σ' ∧ τ = τ' := by
  constructor
  · apply Equiv.ext
    intro i
    have hi := DFunLike.congr_fun h (Fin.castAdd n i)
    simpa using hi
  · apply Equiv.ext
    intro i
    have hi := DFunLike.congr_fun h (Fin.natAdd m i)
    simpa using hi

/-- An end-inverted pattern occurs in a direct sum exactly when it occurs in a block. -/
theorem directSum_avoids {m n k : ℕ} {p : Fin (k+1) → ℕ}
    (hend : p (Fin.last k) < p 0)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    Avoids (directSum σ τ) p ↔ Avoids σ p ∧ Avoids τ p := by
  constructor
  · intro h
    constructor
    · rintro ⟨pos, hpos, hpat⟩
      apply h
      refine ⟨fun i => Fin.castAdd n (pos i), ?_, ?_⟩
      · intro i j hij
        exact hpos hij
      · intro i j
        change directSum σ τ (Fin.castAdd n (pos i)) <
          directSum σ τ (Fin.castAdd n (pos j)) ↔ _
        rw [directSum_left, directSum_left]
        exact hpat i j
    · rintro ⟨pos, hpos, hpat⟩
      apply h
      refine ⟨fun i => Fin.natAdd m (pos i), ?_, ?_⟩
      · intro i j hij
        change m + (pos i).val < m + (pos j).val
        exact Nat.add_lt_add_left (hpos hij) m
      · intro i j
        change directSum σ τ (Fin.natAdd m (pos i)) <
          directSum σ τ (Fin.natAdd m (pos j)) ↔ _
        rw [directSum_right, directSum_right]
        change m + (τ (pos i)).val < m + (τ (pos j)).val ↔ _
        rw [Nat.add_lt_add_iff_left]
        exact hpat i j
  · rintro ⟨hl, hr⟩ ⟨pos, hpos, hpat⟩
    rcases occurrenceOneSide hend (directSum_cut σ τ) hpos hpat with hleft | hright
    · let f (i : Fin (k+1)) : Fin m := ⟨(pos i).val, hleft i⟩
      have hf (i) : pos i = Fin.castAdd n (f i) := Fin.ext rfl
      apply hl
      refine ⟨f, ?_, ?_⟩
      · intro i j hij
        exact hpos hij
      · intro i j
        have h := hpat i j
        rw [hf i, hf j, directSum_left, directSum_left] at h
        exact h
    · let f (i : Fin (k+1)) : Fin n :=
        ⟨(pos i).val - m, by have := (pos i).isLt; have := hright i; omega⟩
      have hf (i) : pos i = Fin.natAdd m (f i) := by
        apply Fin.ext
        change (pos i).val = m + ((pos i).val - m)
        have := hright i
        omega
      apply hr
      refine ⟨f, ?_, ?_⟩
      · intro i j hij
        have h := hpos hij
        rw [hf i, hf j] at h
        change m + (f i).val < m + (f j).val at h
        exact Nat.lt_of_add_lt_add_left h
      · intro i j
        have h := hpat i j
        rw [hf i, hf j, directSum_right, directSum_right] at h
        change m + (τ (f i)).val < m + (τ (f j)).val ↔ _ at h
        rwa [Nat.add_lt_add_iff_left] at h

def FirstCut {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) : Prop :=
  0 < k ∧ k ≤ n ∧ SumCut σ k ∧ ∀ j, 0 < j → j < k → ¬ SumCut σ j

theorem firstCut_unique {n k l : ℕ} {σ : Equiv.Perm (Fin n)}
    (hk : FirstCut σ k) (hl : FirstCut σ l) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · exact (hl.2.2.2 k hk.1 h hk.2.2.1).elim
  · exact h
  · exact (hk.2.2.2 l hl.1 h hl.2.2.1).elim

theorem firstCut_exists {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    ∃ k, FirstCut σ k := by
  classical
  have existsCut : ∃ k, 0 < k ∧ SumCut σ k :=
    ⟨n, hn, fun i _ => (σ i).isLt⟩
  obtain ⟨hpos, hcut⟩ := Nat.find_spec existsCut
  refine ⟨Nat.find existsCut, hpos, Nat.find_min' existsCut
      (show 0 < n ∧ SumCut σ n from ⟨hn, fun i _ => (σ i).isLt⟩), hcut, ?_⟩
  intro j hj hlt hcutj
  exact (not_le_of_gt hlt) (Nat.find_min' existsCut ⟨hj, hcutj⟩)

theorem directSum_firstCut {m n : ℕ} (hm : 0 < m)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    FirstCut (directSum σ τ) m ↔ SumIndecomposable σ := by
  constructor
  · intro h
    rintro ⟨j, hj, hlt, hcut⟩
    exact h.2.2.2 j hj hlt ((directSum_small_cut hlt.le σ τ).mpr hcut)
  · intro h
    refine ⟨hm, by omega, directSum_cut σ τ, ?_⟩
    intro j hj hlt hcut
    exact h ⟨j, hj, hlt, (directSum_small_cut hlt.le σ τ).mp hcut⟩

def Avoider {k l : ℕ} (p : Fin (k+1) → ℕ) (q : Fin (l+1) → ℕ) (n : ℕ) :=
  {σ : Equiv.Perm (Fin n) // Avoids σ p ∧ Avoids σ q}

def IndecAvoider {k l : ℕ} (p : Fin (k+1) → ℕ) (q : Fin (l+1) → ℕ) (n : ℕ) :=
  {σ : Equiv.Perm (Fin n) // Avoids σ p ∧ Avoids σ q ∧ SumIndecomposable σ}

def FirstCutAvoider {k l : ℕ} (p : Fin (k+1) → ℕ) (q : Fin (l+1) → ℕ)
    (n j : ℕ) :=
  {σ : Equiv.Perm (Fin n) // Avoids σ p ∧ Avoids σ q ∧ FirstCut σ j}

noncomputable def blocksAtCut {k l m n : ℕ} {p : Fin (k+1) → ℕ} {q : Fin (l+1) → ℕ}
    (hp : p (Fin.last k) < p 0) (hq : q (Fin.last l) < q 0) (hm : 0 < m) :
    FirstCutAvoider p q (m+n) m ≃ IndecAvoider p q m × Avoider p q n := by
  refine (Equiv.ofBijective (fun x : IndecAvoider p q m × Avoider p q n =>
    (⟨directSum x.1.val x.2.val,
      (directSum_avoids hp _ _).mpr ⟨x.1.property.1, x.2.property.1⟩,
      (directSum_avoids hq _ _).mpr ⟨x.1.property.2.1, x.2.property.2⟩,
      (directSum_firstCut hm _ _).mpr x.1.property.2.2⟩ :
        FirstCutAvoider p q (m+n) m)) ?_).symm
  constructor
  · intro a b hab
    obtain ⟨hl, hr⟩ := directSum_injective (congrArg Subtype.val hab)
    exact Prod.ext (Subtype.ext hl) (Subtype.ext hr)
  · intro x
    obtain ⟨σ, hpσ, hqσ, hf⟩ := x
    let hcut := hf.2.2.1
    have glue := split_directSum hcut
    have hp' := (directSum_avoids hp _ _).mp (glue ▸ hpσ)
    have hq' := (directSum_avoids hq _ _).mp (glue ▸ hqσ)
    have hi := (directSum_firstCut hm _ _).mp (glue ▸ hf)
    exact ⟨(⟨leftBlock hcut, hp'.1, hq'.1, hi⟩, ⟨rightBlock hcut, hp'.2, hq'.2⟩),
      Subtype.ext glue⟩


noncomputable def firstIndex {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) : Fin (n+1) :=
  let h := firstCut_exists (by omega : 0 < n+1) σ
  ⟨(Classical.choose h) - 1, by
    have hb := (Classical.choose_spec h).2.1
    omega⟩

theorem firstIndex_spec {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) :
    FirstCut σ ((firstIndex σ).val + 1) := by
  let h := firstCut_exists (by omega : 0 < n+1) σ
  have hs := Classical.choose_spec h
  change FirstCut σ (Classical.choose h - 1 + 1)
  rwa [Nat.sub_add_cancel hs.1]

theorem firstIndex_eq_iff {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) (i : Fin (n+1)) :
    firstIndex σ = i ↔ FirstCut σ (i.val+1) := by
  constructor
  · rintro rfl
    exact firstIndex_spec σ
  · intro h
    apply Fin.ext
    have hh := firstCut_unique (firstIndex_spec σ) h
    omega

noncomputable def firstBlockEquiv {k l : ℕ} {p : Fin (k+1) → ℕ} {q : Fin (l+1) → ℕ}
    (hp : p (Fin.last k) < p 0) (hq : q (Fin.last l) < q 0) (n : ℕ) :
    Avoider p q (n+1) ≃
      Σ i : Fin (n+1), IndecAvoider p q (i.val+1) × Avoider p q (n-i.val) := by
  let index (x : Avoider p q (n+1)) := firstIndex x.val
  refine (Equiv.sigmaFiberEquiv index).symm.trans (Equiv.sigmaCongrRight fun i => ?_)
  let fiber : {x : Avoider p q (n+1) // index x = i} ≃
      FirstCutAvoider p q (n+1) (i.val+1) :=
    { toFun := fun x => ⟨x.val.val, x.val.property.1, x.val.property.2,
        (firstIndex_eq_iff _ _).mp x.property⟩
      invFun := fun x => ⟨⟨x.val, x.property.1, x.property.2.1⟩,
        (firstIndex_eq_iff _ _).mpr x.property.2.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  have hi := i.isLt
  have hlen : (i.val+1)+(n-i.val) = n+1 := by omega
  have hcast : FirstCutAvoider p q (n+1) (i.val+1) ≃
      FirstCutAvoider p q ((i.val+1)+(n-i.val)) (i.val+1) :=
    Equiv.cast (congrArg (fun len => FirstCutAvoider p q len (i.val+1)) hlen.symm)
  exact fiber.trans (hcast.trans (blocksAtCut hp hq (by omega)))

theorem avoider_card_succ {k l : ℕ} {p : Fin (k+1) → ℕ} {q : Fin (l+1) → ℕ}
    (hp : p (Fin.last k) < p 0) (hq : q (Fin.last l) < q 0) (n : ℕ) :
    Nat.card (Avoider p q (n+1)) =
      ∑ i ∈ Finset.range (n+1), Nat.card (IndecAvoider p q (i+1)) * Nat.card (Avoider p q (n-i)) := by
  have (i : Fin (n+1)) : Finite (IndecAvoider p q (i.val+1) × Avoider p q (n-i.val)) := by
    unfold IndecAvoider Avoider
    infer_instance
  rw [Nat.card_congr (firstBlockEquiv hp hq n), Nat.card_sigma]
  simp only [Nat.card_prod]
  exact Fin.sum_univ_eq_sum_range (fun i =>
    Nat.card (IndecAvoider p q (i+1)) * Nat.card (Avoider p q (n-i))) (n+1)

theorem avoider_card_zero {k l : ℕ} (p : Fin (k+1) → ℕ) (q : Fin (l+1) → ℕ) :
    Nat.card (Avoider p q 0) = 1 := by
  let : Nonempty (Avoider p q 0) :=
    ⟨⟨Equiv.refl _, (by rintro ⟨pos, _, _⟩; exact Fin.elim0 (pos 0)),
      (by rintro ⟨pos, _, _⟩; exact Fin.elim0 (pos 0))⟩⟩
  let : Subsingleton (Avoider p q 0) :=
    ⟨fun x y => Subtype.ext (Equiv.ext fun i => Fin.elim0 i)⟩
  exact Nat.card_unique


open PowerSeries

noncomputable def totalSeries {k l : ℕ} (p : Fin (k+1) → ℕ) (q : Fin (l+1) → ℕ) :
    PowerSeries ℤ :=
  PowerSeries.mk fun n => (Nat.card (Avoider p q n) : ℤ)

/-- The coefficient at degree n counts the nonempty indecomposables at size n+1. -/
noncomputable def shiftedIndecSeries {k l : ℕ}
    (p : Fin (k+1) → ℕ) (q : Fin (l+1) → ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (Nat.card (IndecAvoider p q (n+1)) : ℤ)

theorem totalSeries_first_block {k l : ℕ} {p : Fin (k+1) → ℕ} {q : Fin (l+1) → ℕ}
    (hp : p (Fin.last k) < p 0) (hq : q (Fin.last l) < q 0) :
    totalSeries p q = 1 + X * (shiftedIndecSeries p q * totalSeries p q) := by
  ext d
  cases d with
  | zero =>
    rw [totalSeries, coeff_mk, avoider_card_zero]
    simp [coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    rw [map_add, coeff_one, if_neg (Nat.succ_ne_zero n), zero_add]
    rw [show (X : PowerSeries ℤ) = X ^ 1 by simp only [pow_one],
      coeff_X_pow_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [totalSeries, shiftedIndecSeries, coeff_mk]
    exact_mod_cast avoider_card_succ hp hq n

theorem totalSeries_factorization {k l : ℕ} {p : Fin (k+1) → ℕ} {q : Fin (l+1) → ℕ}
    (hp : p (Fin.last k) < p 0) (hq : q (Fin.last l) < q 0) :
    totalSeries p q * (1 - X * shiftedIndecSeries p q) = 1 := by
  linear_combination totalSeries_first_block hp hq

noncomputable abbrev secondTotal := totalSeries ![2,4,3,1] ![4,5,2,3,1]
noncomputable abbrev secondIndec := shiftedIndecSeries ![2,4,3,1] ![4,5,2,3,1]
noncomputable abbrev permPalTotal := totalSeries ![1,3,4,2] ![1,3,2,5,4]

theorem secondTotal_eq_permPalTotal : secondTotal = permPalTotal := by
  ext n
  simp only [totalSeries, coeff_mk]
  exact congrArg (fun t : ℕ => (t : ℤ)) (secondClassReverse n)

def PermPalCubic : Prop :=
  (X^2 - X + 1) * permPalTotal^3 + (X - 3) * permPalTotal^2 + 3 * permPalTotal - 1 = 0

theorem secondIndec_ternary_of_permPalCubic (h : PermPalCubic) :
    secondIndec = 1 + X * secondIndec^3 := by
  apply cubicToTernary (t := (X : PowerSeries ℤ)) (F := secondTotal) X_ne_zero
  · exact totalSeries_factorization exactPatternEnds.2.2.1 exactPatternEnds.2.2.2
  · unfold PermPalCubic at h
    rwa [secondTotal_eq_permPalTotal]

end A001764

end

section

namespace A001764

open PowerSeries
open OMA.S_oeis_a001764


/-- Eliminate the implicit derivative of the ternary-tree series to obtain
the second-order equation for its hypergeometric coefficients. -/
theorem ternary_ode {f : PowerSeries ℤ} (hf : f = 1 + X * f^3) :
    (4 * X - 27 * X^2) * (PowerSeries.derivative ℤ) ((PowerSeries.derivative ℤ) f) + (6 - 54 * X) * (PowerSeries.derivative ℤ) f - 6 * f = 0 := by
  let d := 3 - 2 * f
  have hx : X * f ^ 3 = f - 1 := by linear_combination -hf
  have hd₁ : d * (PowerSeries.derivative ℤ) f = f ^ 4 := by
    have h := congrArg (fun z : PowerSeries ℤ => (PowerSeries.derivative ℤ) z) hf
    simp only [map_add, derivative_one, Derivation.leibniz, smul_eq_mul, derivative_X,
      derivative_pow, zero_add, mul_one, Nat.reduceSub, Nat.cast_ofNat] at h
    dsimp [d]
    linear_combination f * h + 3 * (PowerSeries.derivative ℤ) f * hx
  have hconst : (PowerSeries.derivative ℤ) (3 : PowerSeries ℤ) = 0 ∧ (PowerSeries.derivative ℤ) (2 : PowerSeries ℤ) = 0 := by
    exact ⟨Derivation.map_natCast (PowerSeries.derivative ℤ) 3,
      Derivation.map_natCast (PowerSeries.derivative ℤ) 2⟩
  have hd₂ : d * (PowerSeries.derivative ℤ) ((PowerSeries.derivative ℤ) f) = 2 * ((PowerSeries.derivative ℤ) f)^2 + 4 * f^3 * (PowerSeries.derivative ℤ) f := by
    have hh := congrArg (fun z : PowerSeries ℤ => (PowerSeries.derivative ℤ) z) hd₁
    dsimp [d] at hh ⊢
    simp only [Derivation.leibniz, smul_eq_mul, map_sub, hconst.1, hconst.2, mul_zero,
      zero_sub, add_zero, derivative_pow, Nat.reduceSub, Nat.cast_ofNat] at hh
    linear_combination hh
  have hd₃ : d^3 * (PowerSeries.derivative ℤ) ((PowerSeries.derivative ℤ) f) = 2 * f^8 + 4 * f^7 * d := by
    calc
      _ = d^2 * (d * (PowerSeries.derivative ℤ) ((PowerSeries.derivative ℤ) f)) := by ring
      _ = 2 * (d * (PowerSeries.derivative ℤ) f)^2 + 4 * f^3 * d * (d * (PowerSeries.derivative ℤ) f) := by rw [hd₂]; ring
      _ = _ := by rw [hd₁]; ring
  have hP : (4 * X - 27 * X^2) * f^6 =
      4 * (f-1) * f^3 - 27 * (f-1)^2 := by
    calc
      _ = 4 * (X*f^3) * f^3 - 27 * (X*f^3)^2 := by ring
      _ = _ := by rw [hx]
  have hQ : (6 - 54 * X) * f^6 = 6*f^6 - 54*(f-1)*f^3 := by
    calc
      _ = 6*f^6 - 54*(X*f^3)*f^3 := by ring
      _ = _ := by rw [hx]
  have hzero : d^3 * f^6 *
      ((4 * X - 27 * X^2) * (PowerSeries.derivative ℤ) ((PowerSeries.derivative ℤ) f) + (6 - 54 * X) * (PowerSeries.derivative ℤ) f - 6 * f) = 0 := by
    calc
      _ = ((4*X-27*X^2)*f^6)*(d^3*(PowerSeries.derivative ℤ) ((PowerSeries.derivative ℤ) f)) +
          ((6-54*X)*f^6)*(d*(PowerSeries.derivative ℤ) f)*d^2 - 6*f^7*d^3 := by ring
      _ = 0 := by rw [hP, hQ, hd₃, hd₁]; dsimp [d]; ring
  have hf0 : constantCoeff f = 1 := by
    have hh := congrArg (constantCoeff (R := ℤ)) hf
    simpa using hh
  have hd0 : constantCoeff d = 1 := by
    norm_num [d, hf0, map_ofNat]
  have hfne : f ≠ 0 := by
    intro hh
    rw [hh, map_zero] at hf0
    norm_num at hf0
  have hdne : d ≠ 0 := by
    intro hh
    rw [hh, map_zero] at hd0
    norm_num at hd0
  exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero (pow_ne_zero _ hdne) (pow_ne_zero _ hfne))

theorem coeff_euler (f : PowerSeries ℤ) (n : ℕ) :
    coeff n (X * (PowerSeries.derivative ℤ) f) = n * coeff n f := by
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    have h := coeff_X_pow_mul ((PowerSeries.derivative ℤ) f) 1 n
    simp only [pow_one] at h
    rw [h, coeff_derivative, mul_comm]
    norm_cast

theorem ternary_coeff_recurrence {f : PowerSeries ℤ} (hf : f = 1 + X * f^3) (n : ℕ) :
    2 * (n+1 : ℤ) * (2*n+3) * coeff (n+1) f =
      3 * (3*n+2 : ℤ) * (3*n+1) * coeff n f := by
  have hE : X * (PowerSeries.derivative ℤ) (X * (PowerSeries.derivative ℤ) f) = X * (PowerSeries.derivative ℤ) f + X^2 * (PowerSeries.derivative ℤ) ((PowerSeries.derivative ℤ) f) := by
    rw [Derivation.leibniz, derivative_X, smul_eq_mul, smul_eq_mul]
    ring
  have hh : 4 • (X * (PowerSeries.derivative ℤ) ((PowerSeries.derivative ℤ) f)) + 6 • (PowerSeries.derivative ℤ) f -
      27 • (X * (PowerSeries.derivative ℤ) (X * (PowerSeries.derivative ℤ) f)) - 27 • (X * (PowerSeries.derivative ℤ) f) - 6 • f = 0 := by
    rw [hE]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    linear_combination ternary_ode hf
  have hc := congrArg (fun z : PowerSeries ℤ => coeff n z) hh
  simp only [map_add, map_sub, map_nsmul, map_zero] at hc
  simp only [coeff_euler, coeff_derivative, nsmul_eq_mul, Nat.cast_ofNat] at hc
  linear_combination hc

theorem ternary_coeff_factorial {f : PowerSeries ℤ} (hf : f = 1 + X * f^3) (n : ℕ) :
    coeff n f * ((Nat.factorial n : ℤ) * Nat.factorial (2*n+1)) = Nat.factorial (3*n) := by
  induction n with
  | zero =>
    have h := congrArg (constantCoeff (R := ℤ)) hf
    simpa [coeff_zero_eq_constantCoeff_apply] using h
  | succ n ih =>
    have hrec := ternary_coeff_recurrence hf n
    have h₂ : Nat.factorial (2*(n+1)+1) = (2*n+3)*(2*n+2)*Nat.factorial (2*n+1) := by
      rw [show 2*(n+1)+1 = (2*n+1)+1+1 by omega, Nat.factorial_succ, Nat.factorial_succ]
      ring
    have h₃ : Nat.factorial (3*(n+1)) =
        (3*n+3)*(3*n+2)*(3*n+1)*Nat.factorial (3*n) := by
      rw [show 3*(n+1) = 3*n+1+1+1 by omega,
        Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
      ring
    rw [h₂, h₃, Nat.factorial_succ]
    push_cast
    linear_combination
      ((n+1 : ℤ) * Nat.factorial n * Nat.factorial (2*n+1)) * hrec +
      (3*(n+1 : ℤ)*(3*n+2)*(3*n+1)) * ih

/-- Exact ternary coefficient extraction, including the upstream natural-number
division. This uses the differential equation rather than a Lagrange theorem. -/
theorem ternary_coeff_exact {f : PowerSeries ℤ} (hf : f = 1 + X * f^3) (n : ℕ) :
    coeff n f = (a n : ℤ) := by
  have hc₀ := Nat.choose_mul_factorial_mul_factorial (n := 3*n) (k := n) (by omega)
  rw [show 3*n-n = 2*n by omega] at hc₀
  have hc : ((3*n).choose n : ℤ) * (Nat.factorial n : ℤ) * Nat.factorial (2*n) =
      Nat.factorial (3*n) := by exact_mod_cast hc₀
  have hf₀ := ternary_coeff_factorial hf n
  rw [Nat.factorial_succ] at hf₀
  push_cast at hf₀
  have heq₀ : (coeff n f * (2*(n : ℤ)+1) - (3*n).choose n) *
      ((Nat.factorial n : ℤ) * Nat.factorial (2*n)) = 0 := by
    linear_combination hf₀ - hc
  have hne : (Nat.factorial n : ℤ) * Nat.factorial (2*n) ≠ 0 := by positivity
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp heq₀).resolve_right hne)
  rw [a, Int.natCast_div]
  apply Int.eq_ediv_of_mul_eq_left (by positivity)
  push_cast
  exact heq

/-- The exact second conjunct now depends only on the cubic for the actual
PermPAL avoidance class, rather than an additional coefficient identity. -/
theorem exact_second_conjunct_of_permPalCubic (h : PermPalCubic) :
    ∀ n : ℕ,
      Nat.card {σ : Equiv.Perm (Fin (n + 1)) //
        Avoids σ ![2, 4, 3, 1] ∧ Avoids σ ![4, 5, 2, 3, 1] ∧ SumIndecomposable σ} = a n := by
  intro n
  have hc := ternary_coeff_exact (secondIndec_ternary_of_permPalCubic h) n
  simp only [shiftedIndecSeries, coeff_mk] at hc
  exact_mod_cast hc

noncomputable def ascentSeries : PowerSeries ℤ :=
  PowerSeries.mk fun m =>
    match m with
    | 0 => 0
    | n+1 => (Nat.card {σ : Equiv.Perm (Fin (n+1)) //
        Avoids σ ![4,2,3,1] ∧ Avoids σ ![4,2,5,1,3] ∧ EndsWithAscent σ} : ℤ)

/-- Sufficient identities for the actual ascent series after the
specialization x = X * c of the strict jump-queue equations. -/
def JumpQueueIdentities : Prop :=
  ∃ c l u : PowerSeries ℤ,
    c = 1 + X*c^3 ∧
    (X*c)*l = X*(l-ascentSeries) + (X*c)^2*u + (X*c)^2*X ∧
    u = l + (X*c)*c*(u-ascentSeries) + (X*c)^2*c

theorem exact_first_conjunct_of_queue (h : JumpQueueIdentities) :
    ∀ n : ℕ, 0 < n →
      Nat.card {σ : Equiv.Perm (Fin (n + 1)) //
        Avoids σ ![4, 2, 3, 1] ∧ Avoids σ ![4, 2, 5, 1, 3] ∧ EndsWithAscent σ} = a n := by
  obtain ⟨c, l, u, hc, hl, hu⟩ := h
  have hcat : c = 1 + (X*c)*c^2 := by linear_combination hc
  have heq := ascentSeriesKernel hcat rfl hl hu
  intro n hn
  have hh := congrArg (fun s : PowerSeries ℤ => coeff (n+1) s) heq
  have hx := coeff_X_pow_mul (c-1) 1 n
  rw [pow_one] at hx
  rw [hx, map_sub, coeff_one, if_neg hn.ne', sub_zero] at hh
  have hcoeff := ternary_coeff_exact hc n
  rw [hcoeff] at hh
  simp only [ascentSeries, coeff_mk] at hh
  exact_mod_cast hh

theorem exact_a001764_of_class_specifications
    (hqueue : JumpQueueIdentities) (hpermpal : PermPalCubic) :
    type_of% @OMA.S_oeis_a001764.main :=
  ⟨exact_first_conjunct_of_queue hqueue, exact_second_conjunct_of_permPalCubic hpermpal⟩

end A001764

end

section

namespace A001764.Round4

open OMA.S_oeis_a001764

universe u

/-- The low part of an unlocked queue admits no 231 obstruction. -/
def Low231 {n : ℕ} (σ : Equiv.Perm (Fin n)) (q : ℕ) : Prop :=
  ¬ ∃ i j k, i < j ∧ j < k ∧
    (σ k).val < (σ i).val ∧ (σ i).val < (σ j).val ∧ (σ j).val < q

/-- The strict lock continues over future inputs. This is its second obstruction. -/
def Cross2413 {n : ℕ} (σ : Equiv.Perm (Fin n)) (q : ℕ) : Prop :=
  ¬ ∃ i j k l, i < j ∧ j < k ∧ k < l ∧
    (σ k).val < (σ i).val ∧ (σ i).val < (σ l).val ∧ (σ l).val < q ∧ q ≤ (σ j).val

def No4231 {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ¬ ∃ i j k l, i < j ∧ j < k ∧ k < l ∧
    (σ l).val < (σ j).val ∧ (σ j).val < (σ k).val ∧ (σ k).val < (σ i).val

def No42513 {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ¬ ∃ i j k l m, i < j ∧ j < k ∧ k < l ∧ l < m ∧
    (σ l).val < (σ j).val ∧ (σ j).val < (σ m).val ∧
    (σ m).val < (σ i).val ∧ (σ i).val < (σ k).val

/-- Unlocked queue with ranks below q already available, expressed as local forbidden configurations. -/
def QueueState {n : ℕ} (q : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  No4231 σ ∧ No42513 σ ∧ Low231 σ q ∧ Cross2413 σ q

private theorem pattern4231 {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    No4231 σ ↔ Avoids σ ![4,2,3,1] := by
  constructor
  · rintro h ⟨f, hf, hp⟩
    apply h
    exact ⟨f 0, f 1, f 2, f 3, hf (by decide), hf (by decide), hf (by decide),
      (hp 3 1).mpr (by decide), (hp 1 2).mpr (by decide), (hp 2 0).mpr (by decide)⟩
  · rintro h ⟨i,j,k,l,hij,hjk,hkl,ha,hb,hc⟩
    apply h
    refine ⟨![i,j,k,l], ?_, ?_⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all <;> omega
    · intro a b
      fin_cases a <;> fin_cases b <;> simp_all <;> omega

private theorem pattern42513 {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    No42513 σ ↔ Avoids σ ![4,2,5,1,3] := by
  constructor
  · rintro h ⟨f, hf, hp⟩
    apply h
    exact ⟨f 0, f 1, f 2, f 3, f 4, hf (by decide), hf (by decide), hf (by decide),
      hf (by decide), (hp 3 1).mpr (by decide), (hp 1 4).mpr (by decide),
      (hp 4 0).mpr (by decide), (hp 0 2).mpr (by decide)⟩
  · rintro h ⟨i,j,k,l,m,hij,hjk,hkl,hlm,ha,hb,hc,hd⟩
    apply h
    refine ⟨![i,j,k,l,m], ?_, ?_⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all <;> omega
    · intro a b
      fin_cases a <;> fin_cases b <;> simp_all <;> omega

theorem queueState_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    QueueState 0 σ ↔ Avoids σ ![4,2,3,1] ∧ Avoids σ ![4,2,5,1,3] := by
  simp only [QueueState, pattern4231, pattern42513]
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · rintro ⟨h4,h5⟩
    refine ⟨h4,h5,?_,?_⟩
    · rintro ⟨i,j,k,_,_,_,_,h⟩
      omega
    · rintro ⟨i,j,k,l,_,_,_,_,_,h,_⟩
      omega

theorem queueState_mono {n q r : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : QueueState r σ) (hqr : q ≤ r) : QueueState q σ := by
  obtain ⟨h4,h5,h3,hcross⟩ := h
  refine ⟨h4,h5,?_,?_⟩
  · rintro ⟨i,j,k,hij,hjk,hki,hvij,hj⟩
    exact h3 ⟨i,j,k,hij,hjk,hki,hvij,by omega⟩
  · rintro ⟨i,j,k,l,hij,hjk,hkl,hki,hil,hl,hj⟩
    by_cases hjr : (σ j).val < r
    · exact h3 ⟨i,j,k,hij,hjk,hki,by omega,hjr⟩
    · exact hcross ⟨i,j,k,l,hij,hjk,hkl,hki,hil,by omega,by omega⟩

/-- Enqueueing to the already selected next output is safe. Every newly
    anchored obstruction would have used that output as an ordinary anchor. -/
theorem queueState_raise {n q : ℕ} {σ : Equiv.Perm (Fin (n+1))}
    (h : QueueState q σ) :
    QueueState ((σ 0).val + 1) σ := by
  obtain ⟨h4,h5,_,_⟩ := h
  refine ⟨h4,h5,?_,?_⟩
  · rintro ⟨i,j,k,hij,hjk,hki,hvij,hj⟩
    have hneq : σ j ≠ σ 0 := fun he => by
      have := σ.injective he
      subst j
      exact (Fin.not_lt_zero i) hij
    have hvj : (σ j).val ≠ (σ 0).val := fun he => hneq (Fin.ext he)
    have hi : 0 < i := by
      by_contra! h
      have hi : i = 0 := Fin.ext (by simpa using h)
      rw [hi] at hvij
      change (σ 0).val < (σ j).val at hvij
      omega
    exact h4 ⟨0,i,j,k,hi,hij,hjk,hki,hvij,by omega⟩
  · rintro ⟨i,j,k,l,hij,hjk,hkl,hki,hil,hl,hj⟩
    have hneq : σ l ≠ σ 0 := fun he => by
      have := σ.injective he
      subst l
      exact (Fin.not_lt_zero k) hkl
    have hvl : (σ l).val ≠ (σ 0).val := fun he => hneq (Fin.ext he)
    have hi : 0 < i := by
      by_contra! h
      have hi : i = 0 := Fin.ext (by simpa using h)
      rw [hi] at hil
      omega
    exact h5 ⟨0,i,j,k,l,hi,hij,hjk,hkl,hki,hil,by omega,by omega⟩

/-- An early jump skips the rest of the low queue only after all smaller
    ranks have been output. Both obstructions are needed. -/
theorem earlyJump_before {n q : ℕ} [NeZero n] {σ : Equiv.Perm (Fin n)}
    (h : QueueState q σ) (hq : q ≤ n) (hhead : (σ 0).val + 1 < q)
    {a b : Fin n} (ha : (σ a).val < (σ 0).val)
    (hb : (σ 0).val < (σ b).val) : a < b := by
  obtain ⟨_,_,h3,hcross⟩ := h
  by_contra! hab
  have hba : b < a := lt_of_le_of_ne hab (fun he => by subst b; omega)
  have hb0 : 0 < b := by
    by_contra! he
    have he' : b = 0 := Fin.ext (by simpa using he)
    subst b
    omega
  by_cases hbl : (σ b).val < q
  · exact h3 ⟨0,b,a,hb0,hba,ha,hb,hbl⟩
  let c : Fin n := σ.symm ⟨(σ 0).val + 1, by omega⟩
  have hc : (σ c).val = (σ 0).val + 1 := by simp [c]
  have hc0 : 0 < c := by
    by_contra! he
    have he' : c = 0 := Fin.ext (by simpa using he)
    rw [he'] at hc
    omega
  by_cases hca : c < a
  · exact h3 ⟨0,c,a,hc0,hca,ha,by omega,by omega⟩
  have hac : a < c := lt_of_le_of_ne (le_of_not_gt hca) (fun he => by rw [he] at ha; omega)
  exact hcross ⟨0,b,a,c,hb0,hba,hac,ha,by omega,by omega,by omega⟩

theorem earlyJump_cut {n q : ℕ} [NeZero n] {σ : Equiv.Perm (Fin n)}
    (h : QueueState q σ) (hq : q ≤ n) (hhead : (σ 0).val + 1 < q) :
    SumCut σ ((σ 0).val + 1) := by
  intro i hi
  by_contra! hv
  have hi0 : 0 < i.val := by
    by_contra! he
    have hei : i = 0 := Fin.ext (Nat.eq_zero_of_le_zero he)
    rw [hei] at hv
    omega
  let pre : Fin ((σ 0).val + 1) → Fin n :=
    fun j => σ.symm ⟨j.val, by have := j.isLt; omega⟩
  have pre_val (j : Fin ((σ 0).val + 1)) : (σ (pre j)).val = j.val := by simp [pre]
  have pre_lt (j : Fin ((σ 0).val + 1)) : (pre j).val < i.val := by
    have hj := j.isLt
    by_cases he : j.val = (σ 0).val
    · have hh : pre j = 0 := σ.injective (Fin.ext ((pre_val j).trans he))
      simpa [hh]
    · exact earlyJump_before h hq hhead (by rw [pre_val]; omega) (by omega)
  let f : Fin ((σ 0).val+1) → Fin i.val := fun j => ⟨(pre j).val,pre_lt j⟩
  have hinj : Function.Injective f := by
    intro j k hjk
    have he : pre j = pre k := Fin.ext (congrArg (fun a : Fin i.val => a.val) hjk)
    apply Fin.ext
    rw [← pre_val j, ← pre_val k, he]
  have hcard := Fintype.card_le_of_injective f hinj
  simp at hcard
  omega

private def leftIndex {m n : ℕ} (i : Fin (m+n)) (h : i.val < m) : Fin m :=
  ⟨i.val, h⟩

private def rightIndex {m n : ℕ} (i : Fin (m+n)) (h : m ≤ i.val) : Fin n :=
  ⟨i.val-m, by have := i.isLt; omega⟩

private theorem leftIndex_eval {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (i : Fin (m+n)) (h : i.val < m) :
    (directSum σ τ i).val = (σ (leftIndex i h)).val := by
  have hi : Fin.castAdd n (leftIndex i h) = i := Fin.ext rfl
  calc
    (directSum σ τ i).val = (directSum σ τ (Fin.castAdd n (leftIndex i h))).val :=
      congrArg (fun t => (directSum σ τ t).val) hi.symm
    _ = _ := by simp

private theorem rightIndex_eval {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (i : Fin (m+n)) (h : m ≤ i.val) :
    (directSum σ τ i).val = m + (τ (rightIndex i h)).val := by
  have hi : Fin.natAdd m (rightIndex i h) = i := Fin.ext (by simp [rightIndex]; omega)
  nth_rw 1 [← hi]
  simp

private theorem low231_directSum {m n q : ℕ}
    (hq : m ≤ q) (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    Low231 (directSum σ τ) q ↔ Low231 σ m ∧ Low231 τ (q-m) := by
  constructor
  · intro h
    constructor
    · rintro ⟨i,j,k,hij,hjk,hki,hiv,hj⟩
      apply h
      refine ⟨Fin.castAdd n i,Fin.castAdd n j,Fin.castAdd n k,hij,hjk,?_,?_,?_⟩
      · simpa using hki
      · simpa using hiv
      · simp
        omega
    · rintro ⟨i,j,k,hij,hjk,hki,hiv,hj⟩
      apply h
      refine ⟨Fin.natAdd m i,Fin.natAdd m j,Fin.natAdd m k,
        by exact Nat.add_lt_add_left hij m,by exact Nat.add_lt_add_left hjk m,?_,?_,?_⟩
      · simpa using hki
      · simpa using hiv
      · simp
        omega
  · rintro ⟨hl,hr⟩ ⟨i,j,k,hij,hjk,hki,hiv,hj⟩
    have hij' : i.val < j.val := hij
    have hjk' : j.val < k.val := hjk
    by_cases hi : i.val < m
    · have hk : k.val < m := by
        by_contra! hk
        rw [leftIndex_eval σ τ i hi,rightIndex_eval σ τ k hk] at hki
        have := (σ (leftIndex i hi)).isLt
        omega
      have hlj : j.val < m := by omega
      simp only [leftIndex_eval σ τ i hi,leftIndex_eval σ τ j hlj,leftIndex_eval σ τ k hk] at hki hiv
      exact hl ⟨leftIndex i hi,leftIndex j hlj,leftIndex k hk,hij,hjk,hki,hiv,(σ _).isLt⟩
    · have hi' : m ≤ i.val := by omega
      have hj' : m ≤ j.val := by omega
      have hk' : m ≤ k.val := by omega
      simp only [rightIndex_eval σ τ i hi',rightIndex_eval σ τ j hj',rightIndex_eval σ τ k hk'] at hki hiv hj
      exact hr ⟨rightIndex i hi',rightIndex j hj',rightIndex k hk',
        by change i.val-m < j.val-m; omega, by change j.val-m < k.val-m; omega,by omega,by omega,by omega⟩

private theorem cross2413_directSum {m n q : ℕ}
    (hq : m ≤ q) (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    Cross2413 (directSum σ τ) q ↔ Cross2413 τ (q-m) := by
  constructor
  · rintro h ⟨i,j,k,l,hij,hjk,hkl,hki,hil,hl,hj⟩
    apply h
    refine ⟨Fin.natAdd m i,Fin.natAdd m j,Fin.natAdd m k,Fin.natAdd m l,
      Nat.add_lt_add_left hij m,Nat.add_lt_add_left hjk m,Nat.add_lt_add_left hkl m,?_,?_,?_,?_⟩
    · simpa using hki
    · simpa using hil
    · simp
      omega
    · simp
      omega
  · rintro h ⟨i,j,k,l,hij,hjk,hkl,hki,hil,hl,hj⟩
    have hij' : i.val < j.val := hij
    have hjk' : j.val < k.val := hjk
    have hkl' : k.val < l.val := hkl
    have hi : m ≤ i.val := by
      by_contra! hi
      have hk : k.val < m := by
        by_contra! hk
        rw [leftIndex_eval σ τ i hi,rightIndex_eval σ τ k hk] at hki
        have := (σ (leftIndex i hi)).isLt
        omega
      have hlj : j.val < m := by omega
      rw [leftIndex_eval σ τ j hlj] at hj
      have := (σ (leftIndex j hlj)).isLt
      omega
    have hj' : m ≤ j.val := by omega
    have hk' : m ≤ k.val := by omega
    have hl' : m ≤ l.val := by omega
    simp only [rightIndex_eval σ τ i hi,rightIndex_eval σ τ j hj',
      rightIndex_eval σ τ k hk',rightIndex_eval σ τ l hl'] at hki hil hl hj
    exact h ⟨rightIndex i hi,rightIndex j hj',rightIndex k hk',rightIndex l hl',
      by change i.val-m < j.val-m; omega, by change j.val-m < k.val-m; omega,
      by change k.val-m < l.val-m; omega,by omega,by omega,by omega,by omega⟩

theorem queueState_directSum {m n q : ℕ}
    (hq : m ≤ q) (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    QueueState q (directSum σ τ) ↔ Low231 σ m ∧ QueueState (q-m) τ := by
  have h4 : No4231 (directSum σ τ) ↔ No4231 σ ∧ No4231 τ := by
    simp only [pattern4231]
    exact directSum_avoids (by decide) σ τ
  have h5 : No42513 (directSum σ τ) ↔ No42513 σ ∧ No42513 τ := by
    simp only [pattern42513]
    exact directSum_avoids (by decide) σ τ
  simp only [QueueState, h4, h5, low231_directSum hq, cross2413_directSum hq]
  constructor
  · rintro ⟨⟨_,h4⟩,⟨_,h5⟩,⟨hl,hr⟩,hc⟩
    exact ⟨hl,h4,h5,hr,hc⟩
  · rintro ⟨hl,h4,h5,hr,hc⟩
    refine ⟨⟨?_,h4⟩,⟨?_,h5⟩,⟨hl,hr⟩,hc⟩
    · rintro ⟨i,j,k,l,hij,hjk,hkl,hlj,hjk',hki⟩
      exact hl ⟨j,k,l,hjk,hkl,hlj,hjk',(σ k).isLt⟩
    · rintro ⟨i,j,k,l,p,hij,hjk,hkl,hlp,hlj,hjp,hpi,hik⟩
      exact hl ⟨j,k,l,hjk,hkl,hlj,by omega,(σ k).isLt⟩

/-- Insert a given rank at the front, shifting the remaining ranks upward. -/
def frontInsert {n : ℕ} (r : Fin (n+1)) (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n+1)) :=
  (finSuccEquiv n).trans ((Equiv.optionCongr τ).trans (finSuccEquiv' r).symm)

@[simp] theorem frontInsert_zero {n : ℕ} (r : Fin (n+1)) (τ : Equiv.Perm (Fin n)) :
    frontInsert r τ 0 = r := by simp [frontInsert]

@[simp] theorem frontInsert_succ {n : ℕ} (r : Fin (n+1)) (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    frontInsert r τ i.succ = r.succAbove (τ i) := by simp [frontInsert]

private theorem succ_of_lt {n : ℕ} {i j : Fin (n+1)} (h : i < j) :
    ∃ k : Fin n, k.succ = j :=
  Fin.exists_succ_eq_of_ne_zero (fun he => by rw [he] at h; exact (Fin.not_lt_zero i) h)

private theorem value_above_compare {n : ℕ} (r : Fin (n+1)) (a b : Fin n) :
    (r.succAbove a).val < (r.succAbove b).val ↔ a.val < b.val :=
  Fin.succAbove_lt_succAbove_iff

private theorem value_below_inserted {n : ℕ} (r : Fin (n+1)) (a : Fin n) :
    (r.succAbove a).val < r.val ↔ a.val < r.val :=
  Fin.succAbove_lt_iff_castSucc_lt r a

private theorem inserted_below_value {n : ℕ} (r : Fin (n+1)) (a : Fin n) :
    r.val < (r.succAbove a).val ↔ r.val ≤ a.val :=
  Fin.lt_succAbove_iff_le_castSucc r a

private theorem avoiding4231_front {n : ℕ} (r : Fin (n+1))
    (τ : Equiv.Perm (Fin n)) : No4231 (frontInsert r τ) ↔ No4231 τ ∧ Low231 τ r.val := by
  constructor
  · intro h
    constructor
    · rintro ⟨i,j,k,l,hi,hj,hk,ha,hb,hc⟩
      apply h
      refine ⟨i.succ,j.succ,k.succ,l.succ, by simpa only [Fin.succ_lt_succ_iff] using hi, by simpa only [Fin.succ_lt_succ_iff] using hj, by simpa only [Fin.succ_lt_succ_iff] using hk, ?_,?_,?_⟩
      all_goals simp only [frontInsert_succ, value_above_compare]
      all_goals assumption
    · rintro ⟨i,j,k,hi,hj,ha,hb,hc⟩
      apply h
      refine ⟨0,i.succ,j.succ,k.succ,Fin.succ_pos _,by simpa only [Fin.succ_lt_succ_iff] using hi,by simpa only [Fin.succ_lt_succ_iff] using hj,?_,?_,?_⟩
      all_goals simp only [frontInsert_zero,frontInsert_succ,value_above_compare,value_below_inserted]
      all_goals assumption
  · rintro ⟨ho,hl⟩ ⟨i,j,k,l,hi,hj,hk,ha,hb,hc⟩
    obtain ⟨j,rfl⟩ := succ_of_lt hi
    obtain ⟨k,rfl⟩ := succ_of_lt hj
    obtain ⟨l,rfl⟩ := succ_of_lt hk
    simp only [frontInsert_succ,value_above_compare] at ha hb
    by_cases h : i = 0
    · subst i
      apply hl
      simp only [frontInsert_zero,frontInsert_succ,value_below_inserted] at hc
      exact ⟨j,k,l,by simpa only [Fin.succ_lt_succ_iff] using hj,by simpa only [Fin.succ_lt_succ_iff] using hk,ha,hb,hc⟩
    · obtain ⟨i,rfl⟩ := Fin.exists_succ_eq_of_ne_zero h
      simp only [frontInsert_succ,value_above_compare] at hc
      exact ho ⟨i,j,k,l,by simpa only [Fin.succ_lt_succ_iff] using hi,by simpa only [Fin.succ_lt_succ_iff] using hj,by simpa only [Fin.succ_lt_succ_iff] using hk,ha,hb,hc⟩

private theorem avoiding42513_front {n : ℕ} (r : Fin (n+1))
    (τ : Equiv.Perm (Fin n)) : No42513 (frontInsert r τ) ↔ No42513 τ ∧ Cross2413 τ r.val := by
  constructor
  · intro h
    constructor
    · rintro ⟨i,j,k,l,m,hi,hj,hk,hl,ha,hb,hc,hd⟩
      apply h
      refine ⟨i.succ,j.succ,k.succ,l.succ,m.succ,by simpa only [Fin.succ_lt_succ_iff] using hi,by simpa only [Fin.succ_lt_succ_iff] using hj,by simpa only [Fin.succ_lt_succ_iff] using hk,by simpa only [Fin.succ_lt_succ_iff] using hl,?_,?_,?_,?_⟩
      all_goals simp only [frontInsert_succ,value_above_compare]
      all_goals assumption
    · rintro ⟨i,j,k,l,hi,hj,hk,ha,hb,hc,hd⟩
      apply h
      refine ⟨0,i.succ,j.succ,k.succ,l.succ,Fin.succ_pos _,by simpa only [Fin.succ_lt_succ_iff] using hi,by simpa only [Fin.succ_lt_succ_iff] using hj,by simpa only [Fin.succ_lt_succ_iff] using hk,?_,?_,?_,?_⟩
      all_goals simp only [frontInsert_zero,frontInsert_succ,value_above_compare,value_below_inserted,inserted_below_value]
      all_goals assumption
  · rintro ⟨ho,hl⟩ ⟨i,j,k,l,m,hi,hj,hk,hll,ha,hb,hc,hd⟩
    obtain ⟨j,rfl⟩ := succ_of_lt hi
    obtain ⟨k,rfl⟩ := succ_of_lt hj
    obtain ⟨l,rfl⟩ := succ_of_lt hk
    obtain ⟨m,rfl⟩ := succ_of_lt hll
    simp only [frontInsert_succ,value_above_compare] at ha hb
    by_cases h : i = 0
    · subst i
      simp only [frontInsert_zero,frontInsert_succ,value_below_inserted,inserted_below_value] at hc hd
      exact hl ⟨j,k,l,m,by simpa only [Fin.succ_lt_succ_iff] using hj,by simpa only [Fin.succ_lt_succ_iff] using hk,by simpa only [Fin.succ_lt_succ_iff] using hll,ha,hb,hc,hd⟩
    · obtain ⟨i,rfl⟩ := Fin.exists_succ_eq_of_ne_zero h
      simp only [frontInsert_succ,value_above_compare] at hc hd
      exact ho ⟨i,j,k,l,m,by simpa only [Fin.succ_lt_succ_iff] using hi,by simpa only [Fin.succ_lt_succ_iff] using hj,by simpa only [Fin.succ_lt_succ_iff] using hk,by simpa only [Fin.succ_lt_succ_iff] using hll,ha,hb,hc,hd⟩

/-- Exact rear output equivalence. The head may itself be the next fresh input
    or already at the back of the queue. In either case all remaining lower
    ranks stay queued. -/
theorem queueState_frontInsert {n q : ℕ} (r : Fin (n+1)) (τ : Equiv.Perm (Fin n))
    (hq : q ≤ r.val+1) :
    QueueState q (frontInsert r τ) ↔ QueueState r.val τ := by
  constructor
  · intro h
    obtain ⟨ho4,hl⟩ := (avoiding4231_front r τ).mp h.1
    obtain ⟨ho5,hc⟩ := (avoiding42513_front r τ).mp h.2.1
    exact ⟨ho4,ho5,hl,hc⟩
  · rintro ⟨ho4,ho5,hl,hc⟩
    have ha : QueueState 0 (frontInsert r τ) := by
      apply (queueState_zero _).mpr
      exact ⟨(pattern4231 _).mp ((avoiding4231_front r τ).mpr ⟨ho4,hl⟩),
        (pattern42513 _).mp ((avoiding42513_front r τ).mpr ⟨ho5,hc⟩)⟩
    apply queueState_mono (queueState_raise ha)
    simpa using hq

end A001764.Round4

end

section

namespace A001764.Round4
open OMA.S_oeis_a001764

/-- Terminal ascents with a uniform convention at sizes zero and one. -/
def LastRise {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∃ i j, i.val + 1 = j.val ∧ j.val + 1 = n ∧ σ i < σ j

theorem lastRise_upstream {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) :
    LastRise σ ↔ EndsWithAscent σ := by
  constructor
  · rintro ⟨i,j,hij,hjn,hv⟩
    have h : j = Fin.last n := Fin.ext (by simp; omega)
    exact ⟨i,by omega,h ▸ hv⟩
  · rintro ⟨i,hi,hv⟩
    exact ⟨i,Fin.last n,hi,by simp,hv⟩

theorem lastRise_frontInsert {n : ℕ} (r : Fin (n+2))
    (τ : Equiv.Perm (Fin (n+1))) (hn : 0 < n) :
    LastRise (frontInsert r τ) ↔ LastRise τ := by
  constructor
  · rintro ⟨i,j,hi,hj,hv⟩
    have hiz : i ≠ 0 := fun he => by rw [he,Fin.val_zero] at hi; omega
    have hjz : j ≠ 0 := fun he => by rw [he,Fin.val_zero] at hj; omega
    obtain ⟨i,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hiz
    obtain ⟨j,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hjz
    refine ⟨i,j,by simp at hi; omega,by simp at hj; omega,?_⟩
    simpa only [frontInsert_succ,Fin.succAbove_lt_succAbove_iff] using hv
  · rintro ⟨i,j,hi,hj,hv⟩
    refine ⟨i.succ,j.succ,by simp; omega,by simp; omega,?_⟩
    simpa only [frontInsert_succ,Fin.succAbove_lt_succAbove_iff] using hv

theorem lastRise_directSum {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (hn : 1 < n) : LastRise (directSum σ τ) ↔ LastRise τ := by
  constructor
  · rintro ⟨i,j,hi,hj,hv⟩
    let i' : Fin n := ⟨i.val - m, by have := i.isLt; omega⟩
    let j' : Fin n := ⟨j.val - m, by have := j.isLt; omega⟩
    have hii : Fin.natAdd m i' = i := Fin.ext (by simp [i']; omega)
    have hjj : Fin.natAdd m j' = j := Fin.ext (by simp [j']; omega)
    rw [← hii,← hjj,directSum_right,directSum_right] at hv
    refine ⟨i',j',by simp [i']; simp [j']; omega,by simp [j']; omega,?_⟩
    change m + (τ i').val < m + (τ j').val at hv
    exact Nat.lt_of_add_lt_add_left hv
  · rintro ⟨i,j,hi,hj,hv⟩
    refine ⟨Fin.natAdd m i,Fin.natAdd m j,by simp; omega,by simp; omega,?_⟩
    rw [directSum_right,directSum_right]
    exact Nat.add_lt_add_left hv m

theorem lastRise_directSum_one {m : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin 1))
    (hm : 0 < m) : LastRise (directSum σ τ) := by
  let i : Fin m := ⟨m-1,by omega⟩
  refine ⟨Fin.castAdd 1 i,Fin.natAdd m 0,by simp [i]; omega,by simp,?_⟩
  rw [directSum_left,directSum_right]
  change (σ i).val < m + (τ 0).val
  have := (σ i).isLt
  omega

def eraseHead {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) : Equiv.Perm (Fin n) :=
  (finSuccAboveEquiv 0).trans ((σ.subtypeEquiv
    (fun i => show i ≠ 0 ↔ σ i ≠ σ 0 from (not_congr σ.injective.eq_iff).symm)).trans
      (finSuccAboveEquiv (σ 0)).symm)

theorem eraseHead_spec {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) (i : Fin n) :
    (σ 0).succAbove (eraseHead σ i) = σ i.succ := by
  change ((finSuccAboveEquiv (σ 0)) ((finSuccAboveEquiv (σ 0)).symm
      ⟨σ i.succ,fun h => i.succ_ne_zero (σ.injective h)⟩)).val = _
  rw [Equiv.apply_symm_apply]

theorem frontInsert_eraseHead {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) :
    frontInsert (σ 0) (eraseHead σ) = σ := by
  apply Equiv.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · rw [frontInsert_succ,eraseHead_spec]

theorem frontInsert_injective {n : ℕ} (r : Fin (n+1)) :
    Function.Injective (frontInsert r) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have hi := DFunLike.congr_fun h i.succ
  simp only [frontInsert_succ] at hi
  exact (Fin.strictMono_succAbove _).injective hi

/-- Bijection on actual terminal-ascent permutations with a fixed rear output rank. -/
def riseRearEquiv {n q : ℕ} (r : Fin (n+2)) (hq : q ≤ r.val+1) (hn : 0 < n) :
    {σ : Equiv.Perm (Fin (n+2)) // QueueState q σ ∧ LastRise σ ∧ σ 0 = r} ≃
    {τ : Equiv.Perm (Fin (n+1)) // QueueState r.val τ ∧ LastRise τ} where
  toFun σ :=
    ⟨eraseHead σ.val, by
      have hform : frontInsert r (eraseHead σ.val) = σ.val := by
        calc
          _ = frontInsert (σ.val 0) (eraseHead σ.val) :=
            congrArg (fun x => frontInsert x (eraseHead σ.val)) σ.property.2.2.symm
          _ = _ := frontInsert_eraseHead _
      exact ⟨(queueState_frontInsert r _ hq).mp (by rw [hform]; exact σ.property.1),
        (lastRise_frontInsert r _ hn).mp (by rw [hform]; exact σ.property.2.1)⟩⟩
  invFun τ := ⟨frontInsert r τ.val, (queueState_frontInsert r _ hq).mpr τ.property.1,
    (lastRise_frontInsert r _ hn).mpr τ.property.2, frontInsert_zero r _⟩
  left_inv σ := by
    apply Subtype.ext
    change frontInsert r (eraseHead σ.val) = σ.val
    calc
      _ = frontInsert (σ.val 0) (eraseHead σ.val) :=
        congrArg (fun x => frontInsert x (eraseHead σ.val)) σ.property.2.2.symm
      _ = _ := frontInsert_eraseHead _
  right_inv τ := by
    apply Subtype.ext
    apply frontInsert_injective r
    change frontInsert r (eraseHead (frontInsert r τ.val)) = _
    nth_rw 1 [← frontInsert_zero r τ.val]
    exact frontInsert_eraseHead _

abbrev Rising (q n : ℕ) :=
  {σ : Equiv.Perm (Fin n) // QueueState q σ ∧ LastRise σ}

abbrev RearRising (q n : ℕ) :=
  {σ : Equiv.Perm (Fin (n+1)) // QueueState q σ ∧ LastRise σ ∧ q ≤ (σ 0).val+1}

private def rearPartition {q n : ℕ} :
    RearRising (q+1) n ≃ RearRising (q+2) n ⊕
      {σ : Equiv.Perm (Fin (n+1)) // QueueState (q+1) σ ∧ LastRise σ ∧ (σ 0).val = q} where
  toFun σ :=
    if h : q+2 ≤ (σ.val 0).val+1 then
      Sum.inl ⟨σ.val,queueState_mono (queueState_raise σ.property.1) (by omega),σ.property.2.1,h⟩
    else Sum.inr ⟨σ.val,σ.property.1,σ.property.2.1,by have := σ.property.2.2; omega⟩
  invFun x := match x with
    | Sum.inl σ => ⟨σ.val,queueState_mono σ.property.1 (by omega),σ.property.2.1,
        by have := σ.property.2.2; omega⟩
    | Sum.inr σ => ⟨σ.val,σ.property.1,σ.property.2.1,by have := σ.property.2.2; omega⟩
  left_inv σ := by
    by_cases h : q+2 ≤ (σ.val 0).val+1
    · dsimp only
      rw [dif_pos h]
    · dsimp only
      rw [dif_neg h]
  right_inv x := by
    cases x with
    | inl σ =>
      dsimp only
      rw [dif_pos σ.property.2.2]
    | inr σ =>
      have he := σ.property.2.2
      dsimp only
      rw [dif_neg (show ¬q+2 ≤ (σ.val 0).val+1 by omega)]

/-- The refined rear-output recurrence in the entire non-boundary range.
    Here q+1 is the initial queue length and n+2 is the number still to emit. -/
theorem terminalRearRecurrence {q n : ℕ} (hn : 0 < n) (hq : q < n+2) :
    Nat.card (RearRising (q+1) (n+1)) =
    Nat.card (RearRising (q+2) (n+1)) + Nat.card (Rising q (n+1)) := by
  let r : Fin (n+2) := ⟨q,hq⟩
  have hcard := Nat.card_congr (rearPartition (q := q) (n := n+1))
  rw [Nat.card_sum] at hcard
  rw [hcard]
  congr 1
  let convert : {σ : Equiv.Perm (Fin (n+2)) // QueueState (q+1) σ ∧ LastRise σ ∧ (σ 0).val = q} ≃
    {σ : Equiv.Perm (Fin (n+2)) // QueueState (q+1) σ ∧ LastRise σ ∧ σ 0 = r} :=
    Equiv.subtypeEquivRight fun σ =>
      ⟨fun h => ⟨h.1,h.2.1,Fin.ext h.2.2⟩,
        fun h => ⟨h.1,h.2.1,congrArg Fin.val h.2.2⟩⟩
  exact Nat.card_congr (convert.trans (riseRearEquiv (q := q+1) r (by rfl) hn))

end A001764.Round4

end

section

namespace A001764.Round4
open OMA.S_oeis_a001764

private theorem directSum_zero_val {m n : ℕ} [NeZero (m+1+n)]
    (σ : Equiv.Perm (Fin (m+1))) (τ : Equiv.Perm (Fin n)) :
    (directSum σ τ 0).val = (σ 0).val := by
  have hz : Fin.castAdd n (0 : Fin (m+1)) = (0 : Fin (m+1+n)) := by ext; simp
  rw [← hz,directSum_left]
  simp

private theorem lastRise_positiveSuffix {m n : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (Fin (m+1))) (τ : Equiv.Perm (Fin n)) :
    LastRise (directSum σ τ) ↔ n = 1 ∨ LastRise τ := by
  by_cases h : n = 1
  · subst n
    simp [lastRise_directSum_one σ τ (by omega)]
  · rw [lastRise_directSum σ τ (by omega)]
    simp [h]

/-- If the left block is headed by its greatest rank, the Catalan condition
    on the block is precisely unrestricted 231 avoidance of its remaining entries. -/
theorem low231_frontMaximum {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    Low231 (frontInsert (Fin.last m) τ) (m+1) ↔ Low231 τ m := by
  constructor
  · rintro h ⟨i,j,k,hij,hjk,ha,hb,hj⟩
    apply h
    refine ⟨i.succ,j.succ,k.succ,by simpa using hij,by simpa using hjk,?_,?_,(frontInsert _ _ _).isLt⟩
    · change (frontInsert (Fin.last m) τ k.succ) < (frontInsert (Fin.last m) τ i.succ)
      rw [frontInsert_succ,frontInsert_succ]
      apply (Fin.succAbove_lt_succAbove_iff).mpr
      exact ha
    · change (frontInsert (Fin.last m) τ i.succ) < (frontInsert (Fin.last m) τ j.succ)
      rw [frontInsert_succ,frontInsert_succ]
      apply (Fin.succAbove_lt_succAbove_iff).mpr
      exact hb
  · rintro h ⟨i,j,k,hij,hjk,ha,hb,_⟩
    have hij0 : j ≠ 0 := fun he => by rw [he] at hij; exact (Fin.not_lt_zero _) hij
    have hjk0 : k ≠ 0 := fun he => by rw [he] at hjk; exact (Fin.not_lt_zero _) hjk
    obtain ⟨j,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hij0
    obtain ⟨k,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hjk0
    have hi0 : i ≠ 0 := fun he => by
      rw [he,frontInsert_zero] at hb
      have := (frontInsert (Fin.last m) τ j.succ).isLt
      simp only [Fin.val_last] at hb
      omega
    obtain ⟨i,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi0
    apply h
    refine ⟨i,j,k,by simpa using hij,by simpa using hjk,?_,?_,(τ j).isLt⟩
    · change frontInsert (Fin.last m) τ k.succ < frontInsert (Fin.last m) τ i.succ at ha
      rw [frontInsert_succ,frontInsert_succ] at ha
      exact (Fin.succAbove_lt_succAbove_iff).mp ha
    · change frontInsert (Fin.last m) τ i.succ < frontInsert (Fin.last m) τ j.succ at hb
      rw [frontInsert_succ,frontInsert_succ] at hb
      exact (Fin.succAbove_lt_succAbove_iff).mp hb

abbrev EarlyRising (q m n : ℕ) :=
  {σ : Equiv.Perm (Fin (m+1+n)) // QueueState q σ ∧ LastRise σ ∧ (σ 0).val = m}
abbrev CatalanBlock (m : ℕ) := {τ : Equiv.Perm (Fin m) // Low231 τ m}
abbrev RisingSuffix (q n : ℕ) := {τ : Equiv.Perm (Fin n) // QueueState q τ ∧ (n=1 ∨ LastRise τ)}

private theorem earlyCut {m n q : ℕ} (_hn : 0 < n) (hq : q ≤ m+1+n)
    (hmq : m+1 < q) (σ : EarlyRising q m n) :
    SumCut σ.val (m+1) := by
  have hh := σ.property.2.2
  simpa only [hh] using earlyJump_cut σ.property.1 hq (by omega)

private theorem earlyLeftHead {m n q : ℕ} (hn : 0 < n) (hq : q ≤ m+1+n)
    (hmq : m+1 < q) (σ : EarlyRising q m n) :
    leftBlock (earlyCut hn hq hmq σ) 0 = Fin.last m := by
  let cut := earlyCut hn hq hmq σ
  have h := congrArg (fun x => (x 0).val) (split_directSum cut)
  rw [directSum_zero_val] at h
  change (leftBlock cut 0).val = (σ.val 0).val at h
  exact Fin.ext (h.trans σ.property.2.2)

/-- Exact early-jump product on the actual permutations, including the one-output
    suffix that makes the last two values ascend across the block boundary. -/
noncomputable def riseEarlyEquiv {m n q : ℕ}
    (hn : 0 < n) (hq : q ≤ m+1+n) (hmq : m+1 < q) :
    EarlyRising q m n ≃ CatalanBlock m × RisingSuffix (q-(m+1)) n where
  toFun σ := by
    let cut := earlyCut hn hq hmq σ
    let lhs := leftBlock cut
    let rhs := rightBlock cut
    have heq : directSum lhs rhs = σ.val := split_directSum cut
    have h := (queueState_directSum (by omega : m+1 ≤ q) lhs rhs).mp (by
      rw [heq]; exact σ.property.1)
    have hhead : lhs 0 = Fin.last m := earlyLeftHead hn hq hmq σ
    have hleft : frontInsert (Fin.last m) (eraseHead lhs) = lhs := by
      calc
        _ = frontInsert (lhs 0) (eraseHead lhs) :=
          congrArg (fun x => frontInsert x (eraseHead lhs)) hhead.symm
        _ = lhs := frontInsert_eraseHead _
    exact ⟨⟨eraseHead lhs,(low231_frontMaximum _).mp (by rw [hleft]; exact h.1)⟩,
      ⟨rhs,h.2,(lastRise_positiveSuffix hn lhs rhs).mp (by rw [heq]; exact σ.property.2.1)⟩⟩
  invFun x := by
    let lhs := frontInsert (Fin.last m) x.1.val
    let rhs := x.2.val
    exact ⟨directSum lhs rhs,
      (queueState_directSum (by omega : m+1 ≤ q) lhs rhs).mpr
        ⟨(low231_frontMaximum _).mpr x.1.property,x.2.property.1⟩,
      (lastRise_positiveSuffix hn lhs rhs).mpr x.2.property.2,
      by rw [directSum_zero_val]; simp [lhs]⟩
  left_inv σ := by
    apply Subtype.ext
    let cut := earlyCut hn hq hmq σ
    let lhs := leftBlock cut
    let rhs := rightBlock cut
    have hhead : lhs 0 = Fin.last m := earlyLeftHead hn hq hmq σ
    have hleft : frontInsert (Fin.last m) (eraseHead lhs) = lhs := by
      calc
        _ = frontInsert (lhs 0) (eraseHead lhs) :=
          congrArg (fun x => frontInsert x (eraseHead lhs)) hhead.symm
        _ = lhs := frontInsert_eraseHead _
    change directSum (frontInsert (Fin.last m) (eraseHead lhs)) rhs = σ.val
    rw [hleft]
    exact split_directSum cut
  right_inv x := by
    let lhs := frontInsert (Fin.last m) x.1.val
    let rhs := x.2.val
    have hc : SumCut (directSum lhs rhs) (m+1) := directSum_cut lhs rhs
    have hparts := directSum_injective (split_directSum hc)
    apply Prod.ext
    · apply Subtype.ext
      change eraseHead (leftBlock hc) = x.1.val
      rw [hparts.1]
      apply frontInsert_injective (Fin.last m)
      change frontInsert (Fin.last m) (eraseHead lhs) = lhs
      calc
        _ = frontInsert (lhs 0) (eraseHead lhs) :=
          congrArg (fun y => frontInsert y (eraseHead lhs)) (frontInsert_zero _ _).symm
        _ = lhs := frontInsert_eraseHead _
    · apply Subtype.ext
      exact hparts.2

theorem terminalEarlyContribution {m n q : ℕ}
    (hn : 0 < n) (hq : q ≤ m+1+n) (hmq : m+1 < q) :
    Nat.card (EarlyRising q m n) =
      Nat.card (CatalanBlock m) * Nat.card (RisingSuffix (q-(m+1)) n) := by
  rw [Nat.card_congr (riseEarlyEquiv hn hq hmq),Nat.card_prod]

end A001764.Round4

end

section

namespace A001764.Round4
open OMA.S_oeis_a001764

/-- The first PermPAL point-placement marks the unique maximum, one column
    separating the unmarked points to its left and right. -/
def placeMaximum {n : ℕ} (c : Fin (n+1)) (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n+1)) :=
  (finSuccEquiv' c).trans ((Equiv.optionCongr τ).trans (finSuccEquiv' (Fin.last n)).symm)

@[simp] theorem placeMaximum_at {n : ℕ} (c : Fin (n+1)) (τ : Equiv.Perm (Fin n)) :
    placeMaximum c τ c = Fin.last n := by simp [placeMaximum]

@[simp] theorem placeMaximum_away {n : ℕ} (c : Fin (n+1)) (τ : Equiv.Perm (Fin n))
    (i : Fin n) : placeMaximum c τ (c.succAbove i) = (τ i).castSucc := by
  rw [show placeMaximum c τ (c.succAbove i) = (Fin.last n).succAbove (τ i) by simp [placeMaximum]]
  exact Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_last _)

def deleteMaximum {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) :
    Equiv.Perm (Fin n) :=
  (finSuccAboveEquiv (σ.symm (Fin.last n))).trans ((σ.subtypeEquiv
    (fun _ => not_congr σ.eq_symm_apply)).trans (finSuccAboveEquiv (Fin.last n)).symm)

theorem deleteMaximum_spec {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) (i : Fin n) :
    (deleteMaximum σ i).castSucc = σ ((σ.symm (Fin.last n)).succAbove i) := by
  rw [← Fin.succAbove_of_castSucc_lt (Fin.last n) _ (Fin.castSucc_lt_last _)]
  change ((finSuccAboveEquiv (Fin.last n)) ((finSuccAboveEquiv (Fin.last n)).symm
    ⟨σ ((σ.symm (Fin.last n)).succAbove i),?_⟩)).val = _
  rw [Equiv.apply_symm_apply]

theorem placeMaximum_deleteMaximum {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) :
    placeMaximum (σ.symm (Fin.last n)) (deleteMaximum σ) = σ := by
  apply Equiv.ext
  intro i
  refine Fin.succAboveCases (σ.symm (Fin.last n)) ?_ (fun j => ?_) i
  · simp
  · rw [placeMaximum_away,deleteMaximum_spec]

theorem placeMaximum_injective {n : ℕ} (c : Fin (n+1)) :
    Function.Injective (placeMaximum c) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have hi := DFunLike.congr_fun h (c.succAbove i)
  simp only [placeMaximum_away,Fin.castSucc_inj] at hi
  exact hi

/-- Occurrence after dropping the marked point of a pattern and its plot. The
    index condition is exactly the left/right column test in the placed grid. -/
def PatternAcrossMaximum {n k : ℕ} (τ : Equiv.Perm (Fin n)) (cut : Fin (n+1))
    (p : Fin (k+1) → ℕ) (peak : Fin (k+1)) : Prop :=
  ∃ f : Fin k → Fin n, StrictMono f ∧
    (∀ i j, τ (f i) < τ (f j) ↔ p (peak.succAbove i) < p (peak.succAbove j)) ∧
    ∀ i, (f i).val < cut.val ↔ i.val < peak.val

private def insertOccurrence {n k : ℕ} (cut : Fin (n+1)) (peak : Fin (k+1))
    (f : Fin k → Fin n) : Fin (k+1) → Fin (n+1) :=
  peak.insertNth cut (cut.succAbove ∘ f)

@[simp] private theorem insertOccurrence_at {n k : ℕ} (cut : Fin (n+1)) (peak : Fin (k+1))
    (f : Fin k → Fin n) : insertOccurrence cut peak f peak = cut := by
  simp [insertOccurrence]

@[simp] private theorem insertOccurrence_away {n k : ℕ} (cut : Fin (n+1)) (peak : Fin (k+1))
    (f : Fin k → Fin n) (i : Fin k) :
    insertOccurrence cut peak f (peak.succAbove i) = cut.succAbove (f i) := by
  simp [insertOccurrence]

/-- Exact obstructions after the one-point placement, for any pattern with a
    unique peak. Occurrences either avoid the mark or straddle its column. -/
theorem avoid_placeMaximum_iff {n k : ℕ} (τ : Equiv.Perm (Fin n)) (cut : Fin (n+1))
    (p : Fin (k+1) → ℕ) (peak : Fin (k+1)) (hp : ∀ i ≠ peak, p i < p peak) :
    Avoids (placeMaximum cut τ) p ↔ Avoids τ p ∧ ¬ PatternAcrossMaximum τ cut p peak := by
  constructor
  · intro h
    constructor
    · rintro ⟨f,hf,hr⟩
      apply h
      refine ⟨cut.succAbove ∘ f,(Fin.strictMono_succAbove cut).comp hf,?_⟩
      intro i j
      change placeMaximum cut τ (cut.succAbove (f i)) <
        placeMaximum cut τ (cut.succAbove (f j)) ↔ _
      simpa only [placeMaximum_away,Fin.castSucc_lt_castSucc_iff] using hr i j
    · rintro ⟨f,hf,hr,hcut⟩
      apply h
      refine ⟨insertOccurrence cut peak f, ?_, ?_⟩
      · intro i j hlt
        revert hlt
        refine Fin.succAboveCases peak ?_ (fun a => ?_) i
        · refine Fin.succAboveCases peak (by simp) (fun b => ?_) j
          intro hb
          simp only [insertOccurrence_at,insertOccurrence_away]
          apply (Fin.lt_succAbove_iff_le_castSucc _ _).mpr
          have hβ : ¬ b.val < peak.val := fun hh =>
            (not_lt_of_gt hb) ((Fin.succAbove_lt_iff_castSucc_lt _ _).mpr hh)
          have hfb : ¬ (f b).val < cut.val := fun hh => hβ ((hcut b).mp hh)
          exact Nat.le_of_not_gt hfb
        · refine Fin.succAboveCases peak ?_ (fun b => ?_) j
          · intro ha
            simp only [insertOccurrence_at,insertOccurrence_away]
            exact (Fin.succAbove_lt_iff_castSucc_lt _ _).mpr
              ((hcut a).mpr ((Fin.succAbove_lt_iff_castSucc_lt _ _).mp ha))
          · intro hab
            simpa only [insertOccurrence_away,Fin.succAbove_lt_succAbove_iff] using
              (hf ((Fin.succAbove_lt_succAbove_iff).mp hab))
      · intro i j
        refine Fin.succAboveCases peak ?_ (fun a => ?_) i
        · refine Fin.succAboveCases peak (by simp) (fun b => ?_) j
          have hb := hp (peak.succAbove b) (peak.succAbove_ne b)
          simp [not_lt_of_gt hb,Fin.le_last]
        · refine Fin.succAboveCases peak (by simp [hp _ (peak.succAbove_ne a)]) (fun b => ?_) j
          simpa only [insertOccurrence_away,placeMaximum_away,Fin.castSucc_lt_castSucc_iff] using hr a b
  · rintro ⟨ha,hp'⟩ ⟨g,hg,hr⟩
    by_cases hmark : g peak = cut
    · apply hp'
      have hne (i : Fin k) : g (peak.succAbove i) ≠ cut := by
        rw [← hmark]
        exact fun h => peak.succAbove_ne i (hg.injective h)
      let f (i : Fin k) : Fin n := (finSuccAboveEquiv cut).symm ⟨g (peak.succAbove i),hne i⟩
      have hf (i : Fin k) : cut.succAbove (f i) = g (peak.succAbove i) :=
        congrArg Subtype.val ((finSuccAboveEquiv cut).apply_symm_apply ⟨_,hne i⟩)
      refine ⟨f,?_,?_,?_⟩
      · intro i j hij
        apply (Fin.succAbove_lt_succAbove_iff).mp
        rw [hf,hf]
        exact hg ((Fin.strictMono_succAbove _) hij)
      · intro i j
        -- Use the selected indices only, avoiding rewriting the function g.
        have hh := hr (peak.succAbove i) (peak.succAbove j)
        rw [← hf i,← hf j,placeMaximum_away,placeMaximum_away] at hh
        exact (Fin.castSucc_lt_castSucc_iff).symm.trans hh
      · intro i
        change ((f i).castSucc < cut) ↔ i.castSucc < peak
        rw [← Fin.succAbove_lt_iff_castSucc_lt,← Fin.succAbove_lt_iff_castSucc_lt,hf,← hmark]
        exact hg.lt_iff_lt
    · apply ha
      have hne (i : Fin (k+1)) : g i ≠ cut := by
        intro he
        have hi : i ≠ peak := fun hp => hmark (hp ▸ he)
        have hh := (hr i peak).mpr (hp i hi)
        rw [he,placeMaximum_at] at hh
        exact (not_lt_of_ge (Fin.le_last _)) hh
      let f (i : Fin (k+1)) : Fin n := (finSuccAboveEquiv cut).symm ⟨g i,hne i⟩
      have hf (i : Fin (k+1)) : cut.succAbove (f i) = g i :=
        congrArg Subtype.val ((finSuccAboveEquiv cut).apply_symm_apply ⟨_,hne i⟩)
      refine ⟨f,?_,?_⟩
      · intro i j hij
        apply (Fin.succAbove_lt_succAbove_iff).mp
        rw [hf,hf]
        exact hg hij
      · intro i j
        have hh := hr i j
        rw [← hf i,← hf j,placeMaximum_away,placeMaximum_away] at hh
        exact (Fin.castSucc_lt_castSucc_iff).symm.trans hh



abbrev PermPalRoot (n : ℕ) := Avoider ![1,3,4,2] ![1,3,2,5,4] n

/-- The maximum lies in its own column. The two crossing patterns are the
    explicit obstructions left by deleting it from 1342 and 13254. -/
abbrev PermPalPlaced {n : ℕ} (cut : Fin (n+1)) :=
  {τ : Equiv.Perm (Fin n) //
    (Avoids τ ![1,3,4,2] ∧ Avoids τ ![1,3,2,5,4]) ∧
    ¬ PatternAcrossMaximum τ cut ![1,3,4,2] 2 ∧
    ¬ PatternAcrossMaximum τ cut ![1,3,2,5,4] 3}

private theorem peak1342 : ∀ i : Fin 4, i ≠ 2 → (![1,3,4,2] : Fin 4 → ℕ) i < 4 := by
  decide

private theorem peak13254 : ∀ i : Fin 5, i ≠ 3 → (![1,3,2,5,4] : Fin 5 → ℕ) i < 5 := by
  decide

theorem permPal_place_pred {n : ℕ} (cut : Fin (n+1)) (τ : Equiv.Perm (Fin n)) :
    (Avoids (placeMaximum cut τ) ![1,3,4,2] ∧ Avoids (placeMaximum cut τ) ![1,3,2,5,4]) ↔
    (Avoids τ ![1,3,4,2] ∧ Avoids τ ![1,3,2,5,4]) ∧
    ¬ PatternAcrossMaximum τ cut ![1,3,4,2] 2 ∧
    ¬ PatternAcrossMaximum τ cut ![1,3,2,5,4] 3 := by
  rw [avoid_placeMaximum_iff τ cut _ 2 (by exact peak1342),
      avoid_placeMaximum_iff τ cut _ 3 (by exact peak13254)]
  tauto

@[simp] theorem inverse_placeMaximum_peak {n : ℕ} (cut : Fin (n+1)) (τ : Equiv.Perm (Fin n)) :
    (placeMaximum cut τ).symm (Fin.last n) = cut := by
  apply (placeMaximum cut τ).injective
  simp

@[simp] theorem deleteMaximum_placeMaximum {n : ℕ} (cut : Fin (n+1)) (τ : Equiv.Perm (Fin n)) :
    deleteMaximum (placeMaximum cut τ) = τ := by
  apply placeMaximum_injective cut
  have h := placeMaximum_deleteMaximum (placeMaximum cut τ)
  simpa only [inverse_placeMaximum_peak] using h

/-- Exact dependent equivalence for the first maximum-placement and singleton
    factor rules of the actual (1342,13254)-avoidance class. -/
def permPalPlacedRootEquiv (n : ℕ) : PermPalRoot (n+1) ≃ (Σ cut : Fin (n+1), PermPalPlaced cut) where
  toFun σ :=
    ⟨σ.val.symm (Fin.last n),⟨deleteMaximum σ.val,(permPal_place_pred _ _).mp
      (by rw [placeMaximum_deleteMaximum]; exact σ.property)⟩⟩
  invFun x := ⟨placeMaximum x.1 x.2.val,(permPal_place_pred _ _).mpr x.2.property⟩
  left_inv σ := by
    apply Subtype.ext
    exact placeMaximum_deleteMaximum _
  right_inv x := by
    rcases x with ⟨cut,τ⟩
    apply Sigma.ext (inverse_placeMaximum_peak cut τ.val)
    dsimp only
    exact (Subtype.heq_iff_coe_eq (fun _ => by rw [inverse_placeMaximum_peak])).mpr
      (deleteMaximum_placeMaximum cut τ.val)

theorem permPalRoot_card_placed (n : ℕ) :
    Nat.card (PermPalRoot (n+1)) = ∑ c : Fin (n+1), Nat.card (PermPalPlaced c) := by
  rw [Nat.card_congr (permPalPlacedRootEquiv n),Nat.card_sigma]


private theorem noMarkedPatternAtLast {n k : ℕ} (τ : Equiv.Perm (Fin n))
    (p : Fin (k+1) → ℕ) (peak : Fin (k+1)) (j : Fin k) (hj : peak.val ≤ j.val) :
    ¬ PatternAcrossMaximum τ (Fin.last n) p peak := by
  rintro ⟨f,hf,hr,hc⟩
  exact (Nat.not_lt_of_ge hj) ((hc j).mp (f j).isLt)

/-- If the marked maximum has no points on its right, deletion leaves an
    arbitrary root avoider, as in the certificate's first requirement split. -/
def permPalPlacedLastEquiv (n : ℕ) : PermPalPlaced (Fin.last n) ≃ PermPalRoot n where
  toFun τ := ⟨τ.val,τ.property.1⟩
  invFun τ := ⟨τ.val,τ.property,
    noMarkedPatternAtLast τ.val _ 2 (2 : Fin 3) (by decide),
    noMarkedPatternAtLast τ.val _ 3 (3 : Fin 4) (by decide)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem permPalRoot_card_split (n : ℕ) :
    Nat.card (PermPalRoot (n+1)) = Nat.card (PermPalRoot n) +
      ∑ c : Fin n, Nat.card (PermPalPlaced c.castSucc) := by
  rw [permPalRoot_card_placed,Fin.sum_univ_castSucc,Nat.card_congr (permPalPlacedLastEquiv n),add_comm]


/-- The row/column separation at the second maximum placement. Points
    left of the global maximum and above the right-hand maximum come first. -/
theorem highLeft_precedes_lowLeft {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : Avoids σ ![1,3,4,2]) {high low global right : Fin n}
    (hh : high < global) (hl : low < global) (hg : global < right)
    (hv : σ low < σ right) (hw : σ right < σ high) (hz : σ high < σ global) :
    high < low := by
  by_contra! he
  have hne : low ≠ high := fun e => by subst low; exact (not_lt_of_ge hw.le) hv
  have hlt : low < high := lt_of_le_of_ne he hne
  apply h
  refine ⟨![low,high,global,right],?_,?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> omega
  · intro i j
    fin_cases i <;> fin_cases j <;> simp_all <;> omega

end A001764.Round4

end

section

namespace A001764.Round4
open OMA.S_oeis_a001764
open scoped BigOperators

theorem low231_exact {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    Low231 τ n ↔ Avoids τ ![2,3,1] := by
  constructor
  · rintro ho ⟨f,hf,hr⟩
    exact ho ⟨f 0,f 1,f 2,hf (by decide),hf (by decide),
      (hr 2 0).mpr (by decide),(hr 0 1).mpr (by decide),(τ (f 1)).isLt⟩
  · rintro ho ⟨a,b,c,hab,hbc,hca,hab',hb⟩
    apply ho
    refine ⟨![a,b,c],?_,?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
    · intro i j
      fin_cases i <;> fin_cases j <;> simp_all <;> omega

theorem cut_of_separated {n : ℕ} (τ : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n)
    (h : ∀ i j, i.val < k → k ≤ j.val → τ i < τ j) :
    SumCut τ k := by
  intro i hi
  by_contra! hni
  have hv (j : Fin k) : (τ.symm ⟨j.val,by have := j.isLt; omega⟩).val < k := by
    by_contra! hf
    have hc := h i _ hi hf
    simp at hc
    have hcn : (τ i).val < j.val := hc
    have hj := j.isLt
    omega
  let pre : Fin k → Fin k := fun j =>
    ⟨(τ.symm ⟨j.val,by have := j.isLt; omega⟩).val,hv j⟩
  have hp : Function.Injective pre := by
    intro a b hab
    have hval := congrArg (fun t : Fin k => t.val) hab
    apply Fin.ext
    have he : τ.symm ⟨a.val,by have := a.isLt; omega⟩ = τ.symm ⟨b.val,by have := b.isLt; omega⟩ :=
      Fin.ext hval
    exact congrArg (fun t : Fin n => t.val) (τ.symm.injective he)
  obtain ⟨j,hj⟩ := Finite.surjective_of_injective hp ⟨i.val,hi⟩
  have hji : τ.symm ⟨j.val,by have := j.isLt; omega⟩ = i :=
    Fin.ext (congrArg (fun t : Fin k => t.val) hj)
  have hval : (τ i).val = j.val := by rw [← hji]; simp
  have := j.isLt
  omega

private theorem cut_iff_no_marked231 {n : ℕ} (τ : Equiv.Perm (Fin n)) (c : Fin (n+1)) :
    SumCut τ c.val ↔ ¬ PatternAcrossMaximum τ c ![2,3,1] 1 := by
  constructor
  · rintro h ⟨f,hf,hr,hc⟩
    have h0 : (f 0).val < c.val := (hc 0).mpr (by decide)
    have h1 : c.val ≤ (f 1).val := Nat.le_of_not_gt
      (fun h => (by decide : ¬ (1 : Fin 2).val < (1 : Fin 3).val) ((hc 1).mp h))
    have hv := h (f 0) h0
    have hw := rightOfSumCut h (f 1) h1
    have hvw : (τ (f 1)).val < (τ (f 0)).val := (hr 1 0).mpr (by decide)
    omega
  · intro h
    apply cut_of_separated τ c.val (by have := c.isLt; omega)
    intro i j hi hj
    by_contra! hji
    have hij : i < j := by change i.val < j.val; omega
    have hn : τ j ≠ τ i := fun he => hij.ne ((τ.injective he).symm)
    have hji' : τ j < τ i := lt_of_le_of_ne hji hn
    apply h
    refine ⟨![i,j],?_,?_,?_⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    · intro a b
      fin_cases a <;> fin_cases b <;> simp_all [show ¬ τ i < τ j from not_lt_of_ge hji]
    · intro a
      fin_cases a <;> simp_all

private theorem peak231 : ∀ i : Fin 3, i ≠ 1 → (![2,3,1] : Fin 3 → ℕ) i < 3 := by
  decide

theorem low231_placeMaximum {n : ℕ} (c : Fin (n+1)) (τ : Equiv.Perm (Fin n)) :
    Low231 (placeMaximum c τ) (n+1) ↔ Low231 τ n ∧ SumCut τ c.val := by
  rw [low231_exact,low231_exact,avoid_placeMaximum_iff τ c _ 1 (by exact peak231),
    cut_iff_no_marked231]

private abbrev CatPlaced (n : ℕ) (c : Fin (n+1)) :=
  {τ : Equiv.Perm (Fin n) // Low231 τ n ∧ SumCut τ c.val}

private def catPlacedEquiv (n : ℕ) : CatalanBlock (n+1) ≃ (Σ c : Fin (n+1), CatPlaced n c) where
  toFun σ := ⟨σ.val.symm (Fin.last n),⟨deleteMaximum σ.val,(low231_placeMaximum _ _).mp
    (by rw [placeMaximum_deleteMaximum]; exact σ.property)⟩⟩
  invFun x := ⟨placeMaximum x.1 x.2.val,(low231_placeMaximum _ _).mpr x.2.property⟩
  left_inv σ := by apply Subtype.ext; exact placeMaximum_deleteMaximum _
  right_inv x := by
    rcases x with ⟨c,τ⟩
    apply Sigma.ext (inverse_placeMaximum_peak c τ.val)
    dsimp only
    exact (Subtype.heq_iff_coe_eq (fun _ => by rw [inverse_placeMaximum_peak])).mpr
      (deleteMaximum_placeMaximum c τ.val)

private theorem low231_directSum_unrestricted {a b : ℕ}
    (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)) :
    Low231 (directSum σ τ) (a+b) ↔ Low231 σ a ∧ Low231 τ b := by
  simp only [low231_exact]
  exact directSum_avoids (by decide) σ τ

private noncomputable def catCutProduct (a b : ℕ) :
    {τ : Equiv.Perm (Fin (a+b)) // Low231 τ (a+b) ∧ SumCut τ a} ≃
      CatalanBlock a × CatalanBlock b where
  toFun τ := by
    let h := τ.property.2
    have hb := (low231_directSum_unrestricted (leftBlock h) (rightBlock h)).mp
      (by rw [split_directSum h]; exact τ.property.1)
    exact ⟨⟨leftBlock h,hb.1⟩,⟨rightBlock h,hb.2⟩⟩
  invFun x := ⟨directSum x.1.val x.2.val,
    (low231_directSum_unrestricted _ _).mpr ⟨x.1.property,x.2.property⟩,
    directSum_cut _ _⟩
  left_inv τ := by apply Subtype.ext; exact split_directSum τ.property.2
  right_inv x := by
    have hh := directSum_injective (split_directSum (directSum_cut x.1.val x.2.val))
    exact Prod.ext (Subtype.ext hh.1) (Subtype.ext hh.2)

private theorem card_catPlaced (n : ℕ) (c : Fin (n+1)) :
    Nat.card (CatPlaced n c) = Nat.card (CatalanBlock c.val) * Nat.card (CatalanBlock (n-c.val)) := by
  have hsize : n = c.val+(n-c.val) := by have := c.isLt; omega
  have htransport {t u r : ℕ} (h : t=u) :
      Nat.card {τ : Equiv.Perm (Fin t) // Low231 τ t ∧ SumCut τ r} =
      Nat.card {τ : Equiv.Perm (Fin u) // Low231 τ u ∧ SumCut τ r} := by subst u; rfl
  change Nat.card {τ : Equiv.Perm (Fin n) // Low231 τ n ∧ SumCut τ c.val} = _
  rw [htransport hsize, Nat.card_congr (catCutProduct c.val (n-c.val)),Nat.card_prod]

theorem catalanBlock_card_recurrence (n : ℕ) :
    Nat.card (CatalanBlock (n+1)) =
      ∑ i : Fin (n+1), Nat.card (CatalanBlock i.val) * Nat.card (CatalanBlock (n-i.val)) := by
  rw [Nat.card_congr (catPlacedEquiv n),Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact card_catPlaced n i

theorem catalanBlock_card (n : ℕ) : Nat.card (CatalanBlock n) = catalan n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      have hall (σ : Equiv.Perm (Fin 0)) : Low231 σ 0 := by
        rintro ⟨i,_⟩
        exact Fin.elim0 i
      let e : CatalanBlock 0 ≃ Equiv.Perm (Fin 0) :=
        ⟨Subtype.val,fun σ => ⟨σ,hall σ⟩,fun _ => rfl,fun _ => rfl⟩
      rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_perm]
      simp
    | succ n =>
      rw [catalanBlock_card_recurrence,catalan_succ]
      apply Finset.sum_congr rfl
      intro i _
      rw [ih i.val i.isLt,ih (n-i.val) (by omega)]

end A001764.Round4

end

section

namespace A001764.Round4

open OMA.S_oeis_a001764
open scoped BigOperators

private abbrev EarlyClass (q n : ℕ) :=
  {σ : Equiv.Perm (Fin (n+1)) // QueueState q σ ∧ LastRise σ ∧ (σ 0).val+1 < q}

private def splitRearEarly (q n : ℕ) :
    Rising q (n+1) ≃ RearRising q n ⊕ EarlyClass q n where
  toFun σ :=
    if h : q ≤ (σ.val 0).val+1 then Sum.inl ⟨σ.val,σ.property.1,σ.property.2,h⟩
    else Sum.inr ⟨σ.val,σ.property.1,σ.property.2,by omega⟩
  invFun x := match x with
    | Sum.inl σ => ⟨σ.val,σ.property.1,σ.property.2.1⟩
    | Sum.inr σ => ⟨σ.val,σ.property.1,σ.property.2.1⟩
  left_inv σ := by
    by_cases h : q ≤ (σ.val 0).val+1
    · dsimp only
      rw [dif_pos h]
    · dsimp only
      rw [dif_neg h]
  right_inv x := by
    cases x with
    | inl σ =>
      dsimp only
      rw [dif_pos σ.property.2.2]
    | inr σ =>
      have hh := σ.property.2.2
      dsimp only
      rw [dif_neg (show ¬q ≤ (σ.val 0).val+1 by omega)]

private def earlyRank {q n : ℕ} (σ : EarlyClass q n) : Fin (q-1) :=
  ⟨(σ.val 0).val, by have := σ.property.2.2; omega⟩

private abbrev Slice (q size rank : ℕ) (hs : 0 < size) :=
  {σ : Equiv.Perm (Fin size) // QueueState q σ ∧ LastRise σ ∧ (σ ⟨0,hs⟩).val = rank}

private def earlyFiberEquiv {q n : ℕ} (m : Fin (q-1)) :
    {σ : EarlyClass q n // earlyRank σ = m} ≃ Slice q (n+1) m.val (by omega) where
  toFun σ := ⟨σ.val.val,σ.val.property.1,σ.val.property.2.1,congrArg Fin.val σ.property⟩
  invFun τ := ⟨⟨τ.val,τ.property.1,τ.property.2.1,by
      have hm := m.isLt
      have he := τ.property.2.2
      change (τ.val 0).val = m.val at he
      omega⟩,Fin.ext τ.property.2.2⟩
  left_inv σ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv τ := rfl

private theorem slice_card_transport {q a b r : ℕ} (h : a=b) (ha : 0 < a) (hb : 0 < b) :
    Nat.card (Slice q a r ha) = Nat.card (Slice q b r hb) := by
  subst b
  rfl

theorem terminalBlockRecurrence {q n : ℕ} (hq : q ≤ n+1) :
    Nat.card (Rising q (n+1)) = Nat.card (RearRising q n) +
      ∑ m : Fin (q-1), Nat.card (CatalanBlock m.val) *
        Nat.card (RisingSuffix (q-(m.val+1)) (n-m.val)) := by
  rw [Nat.card_congr (splitRearEarly q n),Nat.card_sum]
  congr 1
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (@earlyRank q n)),Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro m _
  have hm := m.isLt
  have hsize : n+1 = m.val+1+(n-m.val) := by omega
  rw [Nat.card_congr (earlyFiberEquiv m)]
  have he := slice_card_transport (q := q) (r := m.val) hsize (by omega) (by omega)
  rw [he]
  exact terminalEarlyContribution (by omega) (by omega) (by omega)

end A001764.Round4

end

section

namespace A001764.Round4

open OMA.S_oeis_a001764
open scoped BigOperators

private theorem no_three_indices {n : ℕ} (hn : n ≤ 2)
    {a b c : Fin n} (hab : a < b) (hbc : b < c) : False := by
  have h₁ : a.val < b.val := hab
  have h₂ : b.val < c.val := hbc
  have h₃ := c.isLt
  omega

private theorem shortQueue {n q : ℕ} (hn : n ≤ 2) (σ : Equiv.Perm (Fin n)) :
    QueueState q σ := by
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨_,_,_,_,hab,hbc,_⟩
    exact no_three_indices hn hab hbc
  · rintro ⟨_,_,_,_,_,hab,hbc,_⟩
    exact no_three_indices hn hab hbc
  · rintro ⟨_,_,_,hab,hbc,_⟩
    exact no_three_indices hn hab hbc
  · rintro ⟨_,_,_,_,hab,hbc,_⟩
    exact no_three_indices hn hab hbc

private theorem no_lastRise_small {n : ℕ} (hn : n ≤ 1)
    (σ : Equiv.Perm (Fin n)) : ¬ LastRise σ := by
  rintro ⟨i,j,hi,hj,_⟩
  omega

theorem rising_small {q n : ℕ} (hn : n ≤ 1) :
    Nat.card (Rising q n) = 0 := by
  let : IsEmpty (Rising q n) := ⟨fun σ => no_lastRise_small hn σ.val σ.property.2⟩
  exact Nat.card_of_isEmpty

private theorem risingSuffix_card {q n : ℕ} (hn : 0 < n) :
    Nat.card (RisingSuffix q n) = Nat.card (Rising q n) + (if n = 1 then 1 else 0) := by
  classical
  by_cases h : n = 1
  · subst n
    have e : RisingSuffix q 1 ≃ Equiv.Perm (Fin 1) :=
      ⟨Subtype.val,fun σ => ⟨σ,shortQueue (by decide) σ,Or.inl rfl⟩,fun _ => rfl,fun _ => rfl⟩
    rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_perm,rising_small (by decide)]
    simp
  · have he : RisingSuffix q n ≃ Rising q n :=
      Equiv.subtypeEquivRight (fun _ => by simp [h])
    rw [Nat.card_congr he]
    simp [h]

private theorem rise2_id (σ : Equiv.Perm (Fin 2)) (h : LastRise σ) : σ = Equiv.refl _ := by
  obtain ⟨i,j,hij,hj,hv⟩ := h
  have hi : i = 0 := Fin.ext (by change i.val = 0; omega)
  have hj' : j = 1 := Fin.ext (by change j.val = 1; omega)
  rw [hi,hj'] at hv
  have hv' : (σ 0).val < (σ 1).val := hv
  have h₀ := (σ 0).isLt
  have h₁ := (σ 1).isLt
  apply Equiv.ext
  intro a
  fin_cases a
  · apply Fin.ext
    change (σ 0).val = 0
    omega
  · apply Fin.ext
    change (σ 1).val = 1
    omega

private theorem rise_refl2 : LastRise (Equiv.refl (Fin 2)) :=
  ⟨0,1,by decide,by decide,by decide⟩

private theorem rear_two_card (q : ℕ) :
    Nat.card (RearRising q 1) = if q ≤ 1 then 1 else 0 := by
  classical
  split_ifs with h
  · apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨Equiv.refl _,shortQueue (by decide) _,rise_refl2,by simpa using h⟩,?_⟩
    intro x
    apply Subtype.ext
    exact rise2_id _ x.property.2.1
  · let : IsEmpty (RearRising q 1) := ⟨fun σ => h (by
      have hh := σ.property.2.2
      simpa [rise2_id _ σ.property.2.1] using hh)⟩
    exact Nat.card_of_isEmpty

private theorem rear_above {q n : ℕ} (h : n+1 < q) : Nat.card (RearRising q n) = 0 := by
  let : IsEmpty (RearRising q n) := ⟨fun σ => by
    have hh := σ.property.2.2
    have hv := (σ.val 0).isLt
    omega⟩
  exact Nat.card_of_isEmpty

private theorem terminalRearWithBoundary {q n : ℕ} (hq : q < n+2) :
    Nat.card (RearRising (q+1) (n+1)) =
    Nat.card (RearRising (q+2) (n+1)) + Nat.card (Rising q (n+1)) +
      (if q = 0 ∧ n = 0 then 1 else 0) := by
  cases n with
  | zero =>
    rw [rear_two_card,rear_two_card,rising_small (by decide)]
    have h : q+2 > 1 := by omega
    simp [not_le_of_gt h,show q+1 ≤ 1 ↔ q=0 by omega]
  | succ n =>
    rw [terminalRearRecurrence (by omega) hq]
    simp

/-- Unrestricted terminal-ascent completions of a queue of q low ranks with i
    later inputs, on the exact finite permutation type. -/
noncomputable def uCount (q i : ℕ) : ℕ := Nat.card (Rising q (q+i))

/-- The same count restricted to rear or future-input first outputs. -/
noncomputable def lCount (q i : ℕ) : ℕ :=
  match q+i with
  | 0 => 0
  | n+1 => Nat.card (RearRising q n)

theorem lCount_eq {q i n : ℕ} (h : q+i=n+1) :
    lCount q i = Nat.card (RearRising q n) := by simp [lCount,h]

theorem lCount_qzero (i : ℕ) : lCount 0 i = uCount 0 i := by
  cases i with
  | zero => simpa [lCount,uCount] using (rising_small (q := 0) (n := 0) (by decide)).symm
  | succ i =>
    rw [lCount_eq (n:=i) (by omega),uCount,zero_add]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun _ => by simp))

theorem lCount_recurrence (q i : ℕ) :
    lCount (q+1) i = (if i=0 then 0 else lCount (q+2) (i-1)) + uCount q i +
      (if q=0 ∧ i=1 then 1 else 0) := by
  cases hi : q+i with
  | zero =>
    have hq : q=0 := by omega
    have hi0 : i=0 := by omega
    subst q; subst i
    have he : Nat.card (RearRising 1 0) = 0 := by
      let : IsEmpty (RearRising 1 0) := ⟨fun σ => no_lastRise_small (by decide) σ.val σ.property.2.1⟩
      exact Nat.card_of_isEmpty
    simpa [lCount,uCount,rising_small (q:=0) (n:=0) (by decide)] using he
  | succ n =>
    have he := terminalRearWithBoundary (q := q) (n := n) (by omega)
    rw [lCount_eq (n:=n+1) (by omega),uCount,hi]
    have hb : (q=0 ∧ n=0) ↔ (q=0 ∧ i=1) := by omega
    simp only [← hb]
    by_cases hz : i=0
    · have hg : n+2 < q+2 := by omega
      rw [rear_above hg] at he
      simpa [hz] using he
    · rw [if_neg hz,lCount_eq (n:=n+1) (by omega)]
      exact he

theorem uCount_recurrence (q i : ℕ) :
    uCount q i = lCount q i +
      ∑ j : Fin (q-1), catalan j.val *
        (uCount (q-(j.val+1)) i + (if q-(j.val+1)=1 ∧ i=0 then 1 else 0)) := by
  classical
  cases hsize : q+i with
  | zero =>
    have hq : q=0 := by omega
    have hi : i=0 := by omega
    subst q; subst i
    unfold uCount lCount
    rw [show 0+0=0 by rfl,rising_small (by decide)]
    simp
  | succ n =>
    rw [uCount,hsize,terminalBlockRecurrence (by omega : q ≤ n+1),lCount_eq hsize]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have hj := j.isLt
    have hs : q-(j.val+1)+i = n-j.val := by omega
    have he : n-j.val=1 ↔ q-(j.val+1)=1 ∧ i=0 := by omega
    rw [catalanBlock_card,risingSuffix_card (by omega),uCount,hs]
    simp only [he]

theorem lCount_root_exact (n : ℕ) :
    lCount 0 (n+1) = Nat.card {σ : Equiv.Perm (Fin (n+1)) //
       Avoids σ ![4,2,3,1] ∧ Avoids σ ![4,2,5,1,3] ∧ EndsWithAscent σ} := by
  rw [lCount_qzero,uCount,zero_add]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun σ => by
    rw [queueState_zero,lastRise_upstream]
    tauto))

end A001764.Round4

end

section

namespace A001764.Round4

open PowerSeries
open scoped BigOperators

noncomputable def rows (r : ℕ → ℕ → ℕ) : PowerSeries (PowerSeries ℤ) :=
  PowerSeries.mk fun q => PowerSeries.mk fun i => (r q i : ℤ)

noncomputable def rZero : PowerSeries ℤ :=
  PowerSeries.mk fun i => (uCount 0 i : ℤ)

noncomputable def catZ : PowerSeries ℤ :=
  PowerSeries.map (Nat.castRingHom ℤ) catalanSeries

noncomputable def catOuter : PowerSeries (PowerSeries ℤ) :=
  PowerSeries.map PowerSeries.C catZ

noncomputable def xx : PowerSeries (PowerSeries ℤ) := X
noncomputable def tt : PowerSeries (PowerSeries ℤ) := PowerSeries.C X

private theorem coeff_rows (r : ℕ → ℕ → ℕ) (q i : ℕ) :
    coeff i (coeff q (rows r)) = (r q i : ℤ) := by simp [rows]

private theorem root_shift (i : ℕ) : lCount 0 (i+1) = lCount 1 i := by
  rw [lCount_eq (n:=i) (by omega),lCount_eq (n:=i) (by omega)]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun σ => by
    constructor
    · rintro ⟨h,rise,_⟩
      exact ⟨queueState_mono (queueState_raise h) (by omega),rise,by omega⟩
    · rintro ⟨h,rise,_⟩
      exact ⟨queueState_mono h (by omega),rise,by omega⟩))

/-- The two-variable rear-output identity on exact terminal-ascent counts. -/
theorem rear_series :
    xx * rows lCount =
      tt * (rows lCount - PowerSeries.C rZero) + xx^2 * rows uCount + xx^2 * tt := by
  ext q i
  simp only [xx,tt,map_add,PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul']
  cases q with
  | zero =>
    simp [rows,rZero,lCount_qzero]
  | succ q =>
    cases q with
    | zero =>
      cases i with
      | zero => simp [lCount,rows,rZero]
      | succ i =>
        simp [rows,rZero,root_shift]
    | succ q =>
      cases i with
      | zero =>
        by_cases hq : q=0 <;>
          simpa [hq,rows,rZero,PowerSeries.coeff_C,PowerSeries.coeff_X,apply_ite] using
            (congrArg (fun x : ℕ => (x : ℤ)) (lCount_recurrence q 0))
      | succ i =>
        by_cases hq : q=0 <;>
          simpa [hq,rows,rZero,PowerSeries.coeff_C,PowerSeries.coeff_X,apply_ite,add_comm,add_left_comm,add_assoc] using
            (congrArg (fun x : ℕ => (x : ℤ)) (lCount_recurrence q (i+1)))

private theorem norm_u_recurrence (q i : ℕ) :
    (uCount (q+1) i : ℤ) = (lCount (q+1) i : ℤ) +
      (∑ j ∈ Finset.range (q+1),
        (catalan j : ℤ) * ((uCount (q-j) i : ℤ) - (if q-j = 0 then (uCount 0 i : ℤ) else 0))) +
      (if 0 < q ∧ i = 0 then (catalan (q-1) : ℤ) else 0) := by
  have hNat := uCount_recurrence (q+1) i
  rw [show q+1-1=q by omega] at hNat
  have h := congrArg (fun x : ℕ => (x : ℤ)) hNat
  push_cast at h
  have h' : (uCount (q+1) i : ℤ) =
      (lCount (q+1) i : ℤ) +
      ∑ j ∈ Finset.range q, (catalan j : ℤ) *
        ((uCount (q-j) i : ℤ) + (if q-j=1 ∧ i=0 then 1 else 0)) := by
    have hh : (uCount (q+1) i : ℤ) =
        (lCount (q+1) i : ℤ) +
        ∑ j : Fin q, (catalan j.val : ℤ) *
          ((uCount (q-j.val) i : ℤ) + (if q-j.val=1 ∧ i=0 then 1 else 0)) := by
      exact h
    rw [Fin.sum_univ_eq_sum_range
      (fun j => (catalan j : ℤ) * ((uCount (q-j) i : ℤ) + (if q-j=1 ∧ i=0 then 1 else 0))) q] at hh
    exact hh
  rw [h',Finset.sum_range_succ]
  simp only [Nat.sub_self,if_true,sub_self,mul_zero,add_zero]
  simp_rw [mul_add,Finset.sum_add_distrib]
  ring_nf
  congr 2
  · apply Finset.sum_congr rfl
    intro j hj
    have hlt := Finset.mem_range.mp hj
    simp [show q-j ≠ 0 by omega]
  · by_cases hi : i=0
    · subst i
      by_cases hq : q=0
      · subst q
        simp
      · have hqp : 0 < q := Nat.pos_of_ne_zero hq
        simp only [and_true,if_pos hqp]
        rw [Finset.sum_eq_single (q-1)]
        · have he : q-(q-1)=1 := by omega
          simp [he]
        · intro j hj hne
          have hlt := Finset.mem_range.mp hj
          simp [show q-j ≠ 1 by omega]
        · intro hbad
          exact False.elim (hbad (Finset.mem_range.mpr (by omega)))
    · simp [hi]

private theorem cat_product_coeff (q i : ℕ) :
    coeff i (coeff q (catOuter * (rows uCount - PowerSeries.C rZero))) =
      ∑ j ∈ Finset.range (q+1),
        (catalan j : ℤ) * ((uCount (q-j) i : ℤ) - (if q-j=0 then (uCount 0 i : ℤ) else 0)) := by
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [catOuter,PowerSeries.coeff_map,PowerSeries.coeff_C_mul,map_sub,coeff_rows,
    catZ,PowerSeries.catalanSeries_coeff,PowerSeries.coeff_C,rZero]
  congr 2
  split <;> simp

private theorem cat_correction_coeff (q i : ℕ) :
    coeff i (coeff (q+1) (xx^2 * catOuter)) =
      (if 0 < q ∧ i = 0 then (catalan (q-1) : ℤ) else 0) := by
  unfold xx
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hq : q=0
  · simp [hq]
  · have h1 : 0 < q := by omega
    have h2 : 2 ≤ q+1 := by omega
    rw [if_pos h2]
    rw [show q+1-2=q-1 by omega]
    simp only [h1,true_and,catOuter,catZ,PowerSeries.coeff_map,PowerSeries.coeff_C,
      PowerSeries.catalanSeries_coeff]
    rfl

/-- The two-variable unrestricted-output identity, including the one-point
    suffix correction explicitly. -/
theorem unrestricted_series :
    rows uCount = rows lCount + xx * catOuter * (rows uCount - PowerSeries.C rZero) + xx^2 * catOuter := by
  ext q i
  cases q with
  | zero =>
    rw [show xx * catOuter * (rows uCount - PowerSeries.C rZero) =
          xx * (catOuter * (rows uCount - PowerSeries.C rZero)) by ac_rfl]
    simp [xx,PowerSeries.coeff_zero_eq_constantCoeff,lCount_qzero,rows]
  | succ q =>
    rw [show xx * catOuter * (rows uCount - PowerSeries.C rZero) =
          xx * (catOuter * (rows uCount - PowerSeries.C rZero)) by ac_rfl]
    simp only [map_add,coeff_rows]
    rw [show coeff (q+1) (xx*(catOuter*(rows uCount-PowerSeries.C rZero))) =
        coeff q (catOuter*(rows uCount-PowerSeries.C rZero)) from PowerSeries.coeff_succ_X_mul _ _,
      cat_product_coeff,cat_correction_coeff]
    exact norm_u_recurrence _ _

end A001764.Round4

end

section

namespace A001764.Round4
open PowerSeries
open scoped BigOperators

private theorem catZ_const : constantCoeff catZ = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,catZ,PowerSeries.coeff_map,PowerSeries.catalanSeries_coeff]
  simp

private theorem catZ_eq : catZ ^ 2 * X + 1 = catZ := by
  unfold catZ
  simpa only [map_pow,map_mul,PowerSeries.map_X,map_add,map_one] using
    congrArg (PowerSeries.map (Nat.castRingHom ℤ)) catalanSeries_sq_mul_X_add_one

/-- Construct the ternary parameter by taking the compositional inverse of
    the series x/C(x), where C is the Catalan series. -/
theorem exists_ternary_parameter :
    ∃ c : PowerSeries ℤ, c = 1+X*c^3 ∧ PowerSeries.subst (X*c) catZ = c := by
  let d : PowerSeries ℤ := X * invOfUnit catZ 1
  have hd0 : constantCoeff d = 0 := by simp [d]
  have hd1 : IsUnit (coeff 1 d) := by
    simp [d,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_zero_eq_constantCoeff,
      constantCoeff_invOfUnit]
  let w := substInvOfIsUnit d hd1
  have hw : PowerSeries.HasSubst w := HasSubst.substInvOfIsUnit _ _
  let c : PowerSeries ℤ := PowerSeries.subst w catZ
  have he : PowerSeries.subst w d = X :=
    subst_substInvOfIsUnit_right d hd0 hd1
  have hprod : d * catZ = X := by
    unfold d
    rw [mul_assoc,invOfUnit_mul catZ 1 (by simpa using catZ_const),mul_one]
  have hfactor := congrArg (PowerSeries.substAlgHom hw) hprod
  have hx : w = X*c := by
    simp only [map_mul,PowerSeries.coe_substAlgHom,he,PowerSeries.subst_X hw] at hfactor
    exact hfactor.symm
  have hcat := congrArg (PowerSeries.substAlgHom hw) catZ_eq
  simp only [map_mul,map_add,map_one,map_pow,PowerSeries.coe_substAlgHom,PowerSeries.subst_X hw] at hcat
  change c^2 * w + 1 = c at hcat
  refine ⟨c,?_,?_⟩
  · rw [hx] at hcat
    linear_combination -hcat
  · exact congrArg (fun z => PowerSeries.subst z catZ) hx.symm

private abbrev Biv := MvPowerSeries (Option Unit) ℤ
private noncomputable abbrev nested := MvPowerSeries.optionEquivLeft Unit ℤ

private def someEmbed : Unit ↪ Option Unit := ⟨Option.some,Option.some_injective _⟩
private def noneEmbed : Unit ↪ Option Unit := ⟨fun _ => none,fun a b _ => Subsingleton.elim a b⟩

private theorem nested_some (f : PowerSeries ℤ) :
    nested (MvPowerSeries.rename (fun u : Unit => some u) f) = PowerSeries.C f := by
  ext q i
  change MvPowerSeries.coeff (Finsupp.single () i) (PowerSeries.coeff q
    (nested (MvPowerSeries.rename (fun u : Unit => some u) f))) =
    PowerSeries.coeff i (PowerSeries.coeff q (PowerSeries.C f))
  rw [MvPowerSeries.coeff_coeff_optionEquivLeft,PowerSeries.coeff_C]
  by_cases hq : q = 0
  · subst q
    rw [if_pos rfl]
    have h : (Finsupp.single () i).optionElim 0 =
      Finsupp.embDomain someEmbed (Finsupp.single () i) := by
      ext u; cases u with
      | none => simp [someEmbed]
      | some u => cases u; simp [someEmbed]
    change MvPowerSeries.coeff _ (MvPowerSeries.rename someEmbed f) = _
    rw [h,MvPowerSeries.coeff_embDomain_rename]
    rfl
  · rw [if_neg hq,map_zero]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨v,hv⟩
    have h := congrArg (fun w : Option Unit →₀ ℕ => w none) hv
    change Finsupp.mapDomain someEmbed v none = _ at h
    rw [← Finsupp.embDomain_eq_mapDomain] at h
    exact hq (by simpa [someEmbed,Finsupp.embDomain_apply] using h.symm)

private theorem nested_none (f : PowerSeries ℤ) :
    nested (MvPowerSeries.rename (fun _ : Unit => none) f) = PowerSeries.map PowerSeries.C f := by
  ext q i
  change MvPowerSeries.coeff (Finsupp.single () i) (PowerSeries.coeff q
    (nested (MvPowerSeries.rename (fun _ : Unit => none) f))) =
    PowerSeries.coeff i (PowerSeries.coeff q (PowerSeries.map PowerSeries.C f))
  rw [MvPowerSeries.coeff_coeff_optionEquivLeft,PowerSeries.coeff_map,PowerSeries.coeff_C]
  by_cases hi : i = 0
  · subst i
    rw [if_pos rfl]
    have h : (Finsupp.single () 0).optionElim q =
      Finsupp.embDomain noneEmbed (Finsupp.single () q) := by
      ext u
      cases u with
      | none =>
        rw [Finsupp.optionElim_apply_none]
        change q = Finsupp.embDomain noneEmbed (Finsupp.single () q) (noneEmbed ())
        rw [Finsupp.embDomain_apply_self,Finsupp.single_eq_same]
      | some u => cases u; simp [noneEmbed]
    change MvPowerSeries.coeff _ (MvPowerSeries.rename noneEmbed f) = _
    rw [h,MvPowerSeries.coeff_embDomain_rename]
    rfl
  · rw [if_neg hi]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨v,hv⟩
    have h := congrArg (fun w : Option Unit →₀ ℕ => w (some ())) hv
    change Finsupp.mapDomain noneEmbed v (some ()) = _ at h
    rw [← Finsupp.embDomain_eq_mapDomain] at h
    exact hi (by simpa [noneEmbed,Finsupp.embDomain_apply] using h.symm)

private theorem subst_rename_one {f : Unit → Option Unit}
    {a : Option Unit → PowerSeries ℤ} (ha : MvPowerSeries.HasSubst a) (p : PowerSeries ℤ) :
    MvPowerSeries.substAlgHom ha (MvPowerSeries.rename f p) = PowerSeries.subst (a (f ())) p := by
  rw [MvPowerSeries.coe_substAlgHom,MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp (R := ℤ) (f := f)) ha]
  unfold PowerSeries.subst
  congr 1
  funext u
  cases u
  simp [MvPowerSeries.subst_X ha]

/-- The actual terminal-ascent counts satisfy the exact specialization used
    by the prior ternary coefficient proof. -/
theorem verified_jumpQueueIdentities : A001764.JumpQueueIdentities := by
  obtain ⟨c,hc,hcat⟩ := exists_ternary_parameter
  let a : Option Unit → PowerSeries ℤ := fun v => v.elim (X*c) (fun _ => X)
  have ha : MvPowerSeries.HasSubst a :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by
      change constantCoeff (a s) = 0
      cases s <;> simp [a,PowerSeries.constantCoeff_X])
  let ev : Biv →ₐ[ℤ] PowerSeries ℤ := MvPowerSeries.substAlgHom ha
  let l := nested.symm (rows lCount)
  let u := nested.symm (rows uCount)
  let x : Biv := MvPowerSeries.X none
  let t : Biv := MvPowerSeries.X (some ())
  let f : Biv := MvPowerSeries.rename (fun u : Unit => some u) rZero
  let cat : Biv := MvPowerSeries.rename (fun _ : Unit => none) catZ
  have hl : x*l = t*(l-f)+x^2*u+x^2*t := by
    apply nested.injective
    simpa [l,u,x,t,f,xx,tt,nested_some,map_add,map_mul,map_sub,map_pow,PowerSeries.X] using rear_series
  have hu : u = l+x*cat*(u-f)+x^2*cat := by
    apply nested.injective
    simpa [l,u,x,cat,f,xx,catOuter,nested_some,nested_none,map_add,map_mul,map_sub,map_pow] using
      unrestricted_series
  have hf : rZero = A001764.ascentSeries := by
    ext k
    cases k with
    | zero =>
      simp only [rZero,A001764.ascentSeries,coeff_mk,← lCount_qzero]
      rfl
    | succ k => simp only [rZero,A001764.ascentSeries,coeff_mk,← lCount_qzero,lCount_root_exact]
  have hx : ev x = X*c := MvPowerSeries.substAlgHom_X ha none
  have ht : ev t = X := MvPowerSeries.substAlgHom_X ha (some ())
  have hfr : ev f = A001764.ascentSeries := by
    rw [show ev f = PowerSeries.subst X rZero from subst_rename_one ha rZero]
    simpa only [PowerSeries.X_subst] using hf
  have hcr : ev cat = c := by
    rw [show ev cat = PowerSeries.subst (X*c) catZ from subst_rename_one ha catZ]
    exact hcat
  exact ⟨c,ev l,ev u,hc,
    by simpa only [map_add,map_mul,map_sub,map_pow,hx,ht,hfr] using congrArg ev hl,
    by simpa only [map_add,map_mul,map_sub,map_pow,hx,hfr,hcr] using congrArg ev hu⟩

theorem terminal_ascent_exact :
    ∀ n : ℕ, 0 < n →
      Nat.card {σ : Equiv.Perm (Fin (n+1)) //
        OMA.S_oeis_a001764.Avoids σ ![4,2,3,1] ∧
        OMA.S_oeis_a001764.Avoids σ ![4,2,5,1,3] ∧
        OMA.S_oeis_a001764.EndsWithAscent σ} = OMA.S_oeis_a001764.a n :=
  exact_first_conjunct_of_queue verified_jumpQueueIdentities


theorem exact_a001764_of_permPal_only (h : A001764.PermPalCubic) :
    type_of% @OMA.S_oeis_a001764.main :=
  ⟨terminal_ascent_exact,A001764.exact_second_conjunct_of_permPalCubic h⟩

end A001764.Round4

end

section

namespace A001764.Round4

open PowerSeries

/-- The specialized catalytic equations of PermPAL's 22-rule specification
    imply the cubic for the exact upstream permutation class. -/
theorem permPalCubic_of_kernel {k cat : PowerSeries ℤ}
    (hf : A001764.permPalTotal * (1-X*k) = 1)
    (hc : cat = 1 + X*k*cat^2)
    (hk : k-1 = X*k*(k+(k-1)*cat)) : A001764.PermPalCubic := by
  have hdiff : (k-cat)*(1-X*k*(1+cat))=0 := by
    linear_combination hk-hc
  have hfac : 1-X*k*(1+cat) ≠ 0 := by
    intro h
    have hz := congrArg (fun f : PowerSeries ℤ => constantCoeff f) h
    simp [PowerSeries.constantCoeff_X] at hz
  have hkc : k = cat := sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_right hfac)
  rw [← hkc] at hk
  have hternary : k = 1+X*k^3 := by linear_combination hk
  let I : PowerSeries ℤ := X*k
  let F := A001764.permPalTotal
  have hI : I^3-X*I+X^2=0 := by
    dsimp [I]
    linear_combination -X^2*hternary
  have hF : F*(1-I)=1 := hf
  have hIne : 1-I ≠ 0 := by
    intro h
    have hz := congrArg (fun f : PowerSeries ℤ => constantCoeff f) h
    simp [I,PowerSeries.constantCoeff_X] at hz
  have hres : ((X^2-X+1)*F^3+(X-3)*F^2+3*F-1)*(1-I)^3=0 := by
    calc
      _ = (X^2-X+1)*(F*(1-I))^3
          +(X-3)*(F*(1-I))^2*(1-I)
          +3*(F*(1-I))*(1-I)^2-(1-I)^3 := by ring
      _ = 0 := by rw [hF]; linear_combination hI
  exact (mul_eq_zero.mp hres).resolve_right (pow_ne_zero _ hIne)

theorem exact_a001764_of_permPal_kernel {k cat : PowerSeries ℤ}
    (hf : A001764.permPalTotal * (1-X*k) = 1)
    (hc : cat = 1 + X*k*cat^2)
    (hk : k-1 = X*k*(k+(k-1)*cat)) : type_of% @OMA.S_oeis_a001764.main :=
  exact_a001764_of_permPal_only (permPalCubic_of_kernel hf hc hk)

end A001764.Round4

end

section

namespace A001764.Round4
open OMA.S_oeis_a001764

/-- A further mark at a maximal entry strictly to the right of the deleted
    global maximum. The unmarked coordinates use the order of the reduced plot. -/
def RightPeak {n : ℕ} (τ : Equiv.Perm (Fin n)) (cut : Fin (n+1)) (peak : Fin n) : Prop :=
  cut.val ≤ peak.val ∧ ∀ j : Fin n, cut.val ≤ j.val → τ j ≤ τ peak

theorem rightPeak_exists {n : ℕ} (τ : Equiv.Perm (Fin n)) (cut : Fin (n+1))
    (hc : cut.val < n) : ∃ j : Fin n, RightPeak τ cut j := by
  classical
  let s := Finset.univ.filter fun j : Fin n => cut.val ≤ j.val
  have hs : s.Nonempty := ⟨⟨cut.val,hc⟩,by simp [s]⟩
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image s τ hs
  exact ⟨j,(Finset.mem_filter.mp hj).2,fun k hk => hmax k (by simp [s,hk])⟩

theorem rightPeak_unique {n : ℕ} (τ : Equiv.Perm (Fin n)) (cut : Fin (n+1))
    {a b : Fin n} (ha : RightPeak τ cut a) (hb : RightPeak τ cut b) : a=b :=
  τ.injective (le_antisymm (hb.2 a ha.1) (ha.2 b hb.1))

private theorem cut_of_value_separated {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n)
    (h : ∀ i j, (σ i).val < k → k ≤ (σ j).val → i < j) :
    SumCut σ k := by
  intro j hj
  by_contra! hval
  let pre : Fin k → Fin j.val := fun a =>
    ⟨(σ.symm ⟨a.val,by have := a.isLt; omega⟩).val, by
      apply h _ j _ hval
      simp⟩
  have hain : Function.Injective pre := by
    intro a b hab
    have he : σ.symm ⟨a.val,by have := a.isLt; omega⟩ =
        σ.symm ⟨b.val,by have := b.isLt; omega⟩ :=
      Fin.ext (congrArg (fun x : Fin j.val => x.val) hab)
    apply Fin.ext
    exact congrArg (fun x : Fin n => x.val) (σ.symm.injective he)
  have hcard := Fintype.card_le_of_injective pre hain
  simp at hcard
  omega

/-- All entries higher than the right-hand maximum form an initial high block.
    This is the row separation that permits its independent factor. -/
theorem permPal_high_block {n : ℕ} {cut : Fin (n+1)} (τ : PermPalPlaced cut)
    {peak : Fin n} (hpeak : RightPeak τ.val cut peak) :
    SumCut (τ.val.trans Fin.revPerm) (n-1-(τ.val peak).val) := by
  let k := n-1-(τ.val peak).val
  apply cut_of_value_separated _ k (by dsimp [k]; omega)
  intro i j hi hj
  have hi' : (τ.val peak).val < (τ.val i).val := by
    have hh := (τ.val i).isLt
    have hp := (τ.val peak).isLt
    change (τ.val i).rev.val < k at hi
    rw [Fin.val_rev] at hi
    dsimp [k] at hi
    omega
  have hj' : (τ.val j).val ≤ (τ.val peak).val := by
    have hh := (τ.val j).isLt
    have hp := (τ.val peak).isLt
    change k ≤ (τ.val j).rev.val at hj
    rw [Fin.val_rev] at hj
    dsimp [k] at hj
    omega
  have hiCut : i.val < cut.val := by
    by_contra! h
    have hh : (τ.val i).val ≤ (τ.val peak).val := hpeak.2 _ h
    omega
  by_contra! hle
  have hne : j ≠ i := fun h => by rw [h] at hj'; omega
  have hjI : j < i := lt_of_le_of_ne hle hne
  have hjiv : j.val < i.val := hjI
  have hjCut : j.val < cut.val := by omega
  have hje : (τ.val j).val ≠ (τ.val peak).val := by
    intro hv
    have e := τ.val.injective (Fin.ext hv)
    rw [e] at hjCut
    exact (Nat.not_lt_of_ge hpeak.1) hjCut
  have hip : i < peak := by
    change i.val < peak.val
    have := hpeak.1
    omega
  apply τ.property.2.1
  refine ⟨![j,i,peak],?_,?_,?_⟩
  · intro a b hlt
    fin_cases a <;> fin_cases b <;> simp_all <;> omega
  · intro a b
    have hjp : τ.val j < τ.val peak := by change (τ.val j).val < (τ.val peak).val; omega
    have hpi : τ.val peak < τ.val i := hi'
    have hp : (fun x : Fin 3 => (![1,3,4,2] : Fin 4 → ℕ)
        ((2 : Fin 4).succAbove x)) = ![1,3,2] := by decide
    change τ.val (![j,i,peak] a) < τ.val (![j,i,peak] b) ↔
      (fun x : Fin 3 => (![1,3,4,2] : Fin 4 → ℕ) ((2 : Fin 4).succAbove x)) a <
        (fun x : Fin 3 => (![1,3,4,2] : Fin 4 → ℕ) ((2 : Fin 4).succAbove x)) b
    rw [hp]
    fin_cases a <;> fin_cases b <;> simp_all <;> omega
  · intro a
    fin_cases a <;> simp_all [hpeak.1] <;> omega


theorem permPal_high_prefix_iff {n : ℕ} {cut : Fin (n+1)} (τ : PermPalPlaced cut)
    {peak : Fin n} (hpeak : RightPeak τ.val cut peak) (i : Fin n) :
    i.val < n-1-(τ.val peak).val ↔ (τ.val peak).val < (τ.val i).val := by
  let k := n-1-(τ.val peak).val
  have hcut : SumCut (τ.val.trans Fin.revPerm) k := permPal_high_block τ hpeak
  have hi := (τ.val i).isLt
  have hp := (τ.val peak).isLt
  constructor
  · intro h
    have hh := hcut i h
    change (τ.val i).rev.val < k at hh
    rw [Fin.val_rev] at hh
    dsimp [k] at hh
    omega
  · intro h
    by_contra! hn
    have hh := rightOfSumCut hcut i hn
    change k ≤ (τ.val i).rev.val at hh
    rw [Fin.val_rev] at hh
    dsimp [k] at hh
    omega

end A001764.Round4

end

section

namespace A001764.Round4
open OMA.S_oeis_a001764

/-- Concatenate plots with all values in the left block higher than the right. -/
def skewSum {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (m+n)) :=
  (directSum (σ.trans Fin.revPerm) (τ.trans Fin.revPerm)).trans Fin.revPerm

private theorem avoid_valueComplement {n k : ℕ} (σ : Equiv.Perm (Fin n)) (p : Fin k → ℕ)
    (bound : ℕ) (hb : ∀ i, p i ≤ bound) :
    Avoids (σ.trans Fin.revPerm) (fun i => bound-p i) ↔ Avoids σ p := by
  have v (f : Fin k → Fin n) (i j : Fin k) :
      (σ.trans Fin.revPerm) (f i) < (σ.trans Fin.revPerm) (f j) ↔ σ (f j) < σ (f i) :=
    Fin.rev_lt_rev
  have w (i j : Fin k) : bound-p i < bound-p j ↔ p j < p i := by
    have := hb i
    have := hb j
    omega
  constructor
  · rintro h ⟨f,hf,hr⟩
    exact h ⟨f,hf,fun i j => (v f i j).trans ((hr j i).trans (w i j).symm)⟩
  · rintro h ⟨f,hf,hr⟩
    exact h ⟨f,hf,fun i j => (v f j i).symm.trans ((hr j i).trans (w j i))⟩

/-- A pattern whose first value is lower than its last cannot cross a skew cut. -/
theorem skewSum_avoids {m n k : ℕ} {p : Fin (k+1) → ℕ}
    (hend : p 0 < p (Fin.last k)) (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    Avoids (skewSum σ τ) p ↔ Avoids σ p ∧ Avoids τ p := by
  let bound := ∑ i : Fin (k+1), p i
  have hp (i : Fin (k+1)) : p i ≤ bound := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  let c : Fin (k+1) → ℕ := fun i => bound-p i
  have hc (i : Fin (k+1)) : c i ≤ bound := Nat.sub_le _ _
  have he : (fun i => bound-c i) = p := by
    funext i
    have := hp i
    dsimp [c]
    omega
  have hcend : c (Fin.last k) < c 0 := by
    have := hp (Fin.last k)
    have := hp 0
    dsimp [c]
    omega
  unfold skewSum
  rw [← he]
  rw [avoid_valueComplement _ c bound hc,directSum_avoids hcend]
  rw [avoid_valueComplement σ p bound hp,avoid_valueComplement τ p bound hp,he]

theorem permPal_skewSum {m n : ℕ}
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    (Avoids (skewSum σ τ) ![1,3,4,2] ∧ Avoids (skewSum σ τ) ![1,3,2,5,4]) ↔
    (Avoids σ ![1,3,4,2] ∧ Avoids σ ![1,3,2,5,4]) ∧
    (Avoids τ ![1,3,4,2] ∧ Avoids τ ![1,3,2,5,4]) := by
  rw [skewSum_avoids (by decide) σ τ,skewSum_avoids (by decide) σ τ]
  tauto


/-- A cut in the complemented plot gives the two uniquely determined skew
    components of the original plot. -/
theorem skewSplit_of_complementCut {m n : ℕ} {σ : Equiv.Perm (Fin (m+n))}
    (h : SumCut (σ.trans Fin.revPerm) m) :
    skewSum ((leftBlock h).trans Fin.revPerm) ((rightBlock h).trans Fin.revPerm) = σ := by
  have involution {k : ℕ} (π : Equiv.Perm (Fin k)) :
      (π.trans Fin.revPerm).trans Fin.revPerm = π := by
    apply Equiv.ext
    intro i
    simp [Fin.revPerm_apply]
  unfold skewSum
  rw [involution,involution,split_directSum h,involution]

theorem high_split_components_avoid {m n : ℕ} {σ : Equiv.Perm (Fin (m+n))}
    (ha : Avoids σ ![1,3,4,2] ∧ Avoids σ ![1,3,2,5,4])
    (h : SumCut (σ.trans Fin.revPerm) m) :
    (Avoids ((leftBlock h).trans Fin.revPerm) ![1,3,4,2] ∧
       Avoids ((leftBlock h).trans Fin.revPerm) ![1,3,2,5,4]) ∧
    (Avoids ((rightBlock h).trans Fin.revPerm) ![1,3,4,2] ∧
       Avoids ((rightBlock h).trans Fin.revPerm) ![1,3,2,5,4]) := by
  apply (permPal_skewSum _ _).mp
  rwa [skewSplit_of_complementCut h]

end A001764.Round4

end

section

namespace A001764.Round4

private theorem skewSum_left_val {m n : ℕ}
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) (i : Fin m) :
    (skewSum σ τ (Fin.castAdd n i)).val = n+(σ i).val := by
  unfold skewSum
  simp only [Equiv.trans_apply,directSum_left,Fin.revPerm_apply,Fin.val_rev,Fin.val_castAdd]
  have := (σ i).isLt
  omega

private theorem skewSum_right_val {m n : ℕ}
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    (skewSum σ τ (Fin.natAdd m i)).val = (τ i).val := by
  unfold skewSum
  simp only [Equiv.trans_apply,directSum_right,Fin.revPerm_apply,Fin.val_rev,Fin.val_natAdd]
  have := (τ i).isLt
  omega

def shiftCut {n : ℕ} (m : ℕ) (cut : Fin (n+1)) : Fin (m+n+1) :=
  ⟨m+cut.val,by have := cut.isLt; omega⟩

/-- Once the high prefix has been detached, a straddling marked-pattern
    occurrence comes entirely from the low component. -/
theorem patternAcrossMaximum_skewSum {m n k : ℕ}
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) (cut : Fin (n+1))
    (p : Fin (k+2) → ℕ) (peak : Fin (k+2)) (hpeak : peak.val ≤ k)
    (hend : p (peak.succAbove 0) < p (peak.succAbove (Fin.last k))) :
    PatternAcrossMaximum (skewSum σ τ) (shiftCut m cut) p peak ↔
      PatternAcrossMaximum τ cut p peak := by
  constructor
  · rintro ⟨f,hf,hr,hc⟩
    have hl : m ≤ (f (Fin.last k)).val := by
      have hh := hc (Fin.last k)
      change (f (Fin.last k)).val < m+cut.val ↔ k < peak.val at hh
      by_contra! hn
      exact (Nat.not_lt_of_ge hpeak) (hh.mp (by omega))
    have h0 : m ≤ (f 0).val := by
      by_contra! h
      let l : Fin m := ⟨(f 0).val,h⟩
      let r : Fin n := ⟨(f (Fin.last k)).val-m,by have := (f (Fin.last k)).isLt; omega⟩
      have e₁ : Fin.castAdd n l = f 0 := Fin.ext rfl
      have e₂ : Fin.natAdd m r = f (Fin.last k) := Fin.ext (by simp [r]; omega)
      have hv : (skewSum σ τ (f 0)).val < (skewSum σ τ (f (Fin.last k))).val :=
        (hr 0 (Fin.last k)).mpr hend
      rw [← e₁,← e₂,skewSum_left_val,skewSum_right_val] at hv
      have := (τ r).isLt
      omega
    have hhigh (a : Fin (k+1)) : m ≤ (f a).val := by
      exact h0.trans (hf.monotone (Fin.zero_le a))
    let g (a : Fin (k+1)) : Fin n := ⟨(f a).val-m,by
      have := (f a).isLt
      have := hhigh a
      omega⟩
    have hfg (a : Fin (k+1)) : Fin.natAdd m (g a) = f a := Fin.ext (by
      have := hhigh a
      simp [g]
      omega)
    refine ⟨g,?_,?_,?_⟩
    · intro a b hab
      have hh : (f a).val < (f b).val := hf hab
      have := hhigh a
      have := hhigh b
      change (f a).val-m < (f b).val-m
      omega
    · intro a b
      have hv := hr a b
      rw [← hfg a,← hfg b] at hv
      change (skewSum σ τ (Fin.natAdd m (g a))).val <
        (skewSum σ τ (Fin.natAdd m (g b))).val ↔ _ at hv
      rwa [skewSum_right_val,skewSum_right_val] at hv
    · intro a
      have ht := hc a
      have h := hhigh a
      change (f a).val < m+cut.val ↔ a.val < peak.val at ht
      change (f a).val-m < cut.val ↔ a.val < peak.val
      omega
  · rintro ⟨f,hf,hr,hc⟩
    refine ⟨fun a => Fin.natAdd m (f a),?_,?_,?_⟩
    · intro a b hab
      exact Nat.add_lt_add_left (hf hab) m
    · intro a b
      change (skewSum σ τ (Fin.natAdd m (f a))).val <
        (skewSum σ τ (Fin.natAdd m (f b))).val ↔ _
      rw [skewSum_right_val,skewSum_right_val]
      exact hr a b
    · intro a
      change m+(f a).val < m+cut.val ↔ a.val < peak.val
      rw [Nat.add_lt_add_iff_left]
      exact hc a

abbrev PermPalAvoids {n : ℕ} (τ : Equiv.Perm (Fin n)) : Prop :=
  OMA.S_oeis_a001764.Avoids τ ![1,3,4,2] ∧ OMA.S_oeis_a001764.Avoids τ ![1,3,2,5,4]

abbrev PermPalPlacementCondition {n : ℕ} (τ : Equiv.Perm (Fin n)) (cut : Fin (n+1)) : Prop :=
  PermPalAvoids τ ∧ ¬ PatternAcrossMaximum τ cut ![1,3,4,2] 2 ∧
    ¬ PatternAcrossMaximum τ cut ![1,3,2,5,4] 3

theorem permPalPlaced_skewSum {m n : ℕ}
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) (cut : Fin (n+1)) :
    PermPalPlacementCondition (skewSum σ τ) (shiftCut m cut) ↔
      PermPalAvoids σ ∧ PermPalPlacementCondition τ cut := by
  unfold PermPalPlacementCondition PermPalAvoids
  rw [permPal_skewSum,
    patternAcrossMaximum_skewSum σ τ cut _ 2 (by decide) (by decide),
    patternAcrossMaximum_skewSum σ τ cut _ 3 (by decide) (by decide)]
  tauto

end A001764.Round4

end

section

namespace A001764.Round5

/-- A one-row gridded obstruction. The column labels refer to positions,
    while the ranks describe their relative values. -/
structure GridPattern where
  size : ℕ
  rank : Fin size → ℕ
  column : Fin size → ℕ
  deriving DecidableEq

def GridPattern.ofLists (r c : List ℕ) : GridPattern :=
  ⟨r.length, fun i => r[i.val], fun i => (getElem? c i.val).getD 0⟩

def gridOccurs {n : ℕ} (σ : Equiv.Perm (Fin n)) (col : Fin n → ℕ)
    (p : GridPattern) : Prop :=
  ∃ e : Fin p.size → Fin n, StrictMono e ∧
    (∀ i j, σ (e i) < σ (e j) ↔ p.rank i < p.rank j) ∧
    ∀ i, col (e i) = p.column i

def avoidsGrid {n : ℕ} (σ : Equiv.Perm (Fin n)) (col : Fin n → ℕ)
    (basis : List GridPattern) : Prop :=
  ∀ p ∈ basis, ¬ gridOccurs σ col p

def cols3 {n : ℕ} (a b : ℕ) (i : Fin n) : ℕ :=
  if i.val < a then 0 else if i.val < b then 1 else 2

def cols4 {n : ℕ} (d a b : ℕ) (i : Fin n) : ℕ :=
  if i.val < d then 0 else if i.val < a then 1 else if i.val < b then 2 else 3

/-- Lift an occurrence by putting its initial positions in the left split
    column up to t. The other columns shift one position right. -/
def GridPattern.split (p : GridPattern) (t : ℕ) : GridPattern :=
  ⟨p.size, p.rank, fun i =>
    if p.column i = 0 then if i.val < t then 0 else 1 else p.column i + 1⟩

def expandFusion (basis : List GridPattern) : List GridPattern :=
  basis.flatMap fun p => (List.range (p.size+1)).map p.split

private theorem prefixCut {n k : ℕ} {e : Fin k → Fin n} (he : StrictMono e)
    (d : ℕ) : ∃ t ≤ k, ∀ i, (e i).val < d ↔ i.val < t := by
  classical
  let Q := fun t : ℕ => k ≤ t ∨ ∃ i : Fin k, i.val = t ∧ d ≤ (e i).val
  have hQ : ∃ t, Q t := ⟨k,Or.inl le_rfl⟩
  have ht : Nat.find hQ ≤ k := Nat.find_min' hQ (Or.inl le_rfl)
  refine ⟨Nat.find hQ, ht, fun i => ⟨?_, ?_⟩⟩
  · intro hd
    by_contra! h
    obtain hbad | ⟨j,hj,hjd⟩ := Nat.find_spec hQ
    · omega
    · have hh : j ≤ i := by change j.val ≤ i.val; omega
      exact (Nat.not_lt_of_ge (hjd.trans (he.monotone hh))) hd
  · intro hi
    by_contra! hd
    exact (Nat.find_min hQ hi) (Or.inr ⟨i,rfl,hd⟩)

theorem gridOccurs_fused_iff {n d a b : ℕ} (σ : Equiv.Perm (Fin n))
    (hda : d ≤ a) (p : GridPattern) :
    gridOccurs σ (cols3 a b) p ↔
      ∃ t ≤ p.size, gridOccurs σ (cols4 d a b) (p.split t) := by
  constructor
  · rintro ⟨e,he,hr,hc⟩
    obtain ⟨t,ht,hprefix⟩ := prefixCut he d
    refine ⟨t,ht,e,he,hr,?_⟩
    intro i
    have h := hc i
    have hpre := hprefix i
    change cols4 d a b (e i) =
      (if p.column i = 0 then if i.val < t then 0 else 1 else p.column i + 1)
    by_cases hd : (e i).val < d
    · have ha : (e i).val < a := by omega
      have hi := hpre.mp hd
      simp [cols3,ha] at h
      simp [cols4,hd,hi,← h]
    · by_cases ha : (e i).val < a
      · have hi : ¬ i.val < t := fun hi => hd (hpre.mpr hi)
        simp [cols3,ha] at h
        simp [cols4,hd,ha,hi,← h]
      · by_cases hb : (e i).val < b
        · simp [cols3,ha,hb] at h
          simp [cols4,hd,ha,hb,← h]
        · simp [cols3,ha,hb] at h
          simp [cols4,hd,ha,hb,← h]
  · rintro ⟨t,ht,e,he,hr,hc⟩
    refine ⟨e,he,hr,?_⟩
    intro i
    have h := hc i
    change cols4 d a b (e i) =
      (if p.column i = 0 then if i.val < t then 0 else 1 else p.column i+1) at h
    by_cases hd : (e i).val < d
    · have ha : (e i).val < a := by omega
      simp [cols4,hd] at h
      split at h
      · rename_i hz; simpa [cols3,ha] using hz.symm
      · omega
    · by_cases ha : (e i).val < a
      · simp [cols4,hd,ha] at h
        split at h
        · rename_i hz; simpa [cols3,ha] using hz.symm
        · omega
      · by_cases hb : (e i).val < b
        · simp [cols4,hd,ha,hb] at h
          split at h
          · split at h <;> omega
          · simp [cols3,ha,hb]; omega
        · simp [cols4,hd,ha,hb] at h
          split at h
          · split at h <;> omega
          · simp [cols3,ha,hb]; omega

theorem avoidsGrid_fused_iff {n d a b : ℕ} (σ : Equiv.Perm (Fin n))
    (hda : d ≤ a) (basis : List GridPattern) :
    avoidsGrid σ (cols4 d a b) (expandFusion basis) ↔
      avoidsGrid σ (cols3 a b) basis := by
  constructor
  · intro h p hp hocc
    obtain ⟨t,ht,ho⟩ := (gridOccurs_fused_iff σ hda p).mp hocc
    apply h (p.split t) _ ho
    exact List.mem_flatMap.mpr ⟨p,hp,List.mem_map.mpr
      ⟨t,List.mem_range.mpr (by omega),rfl⟩⟩
  · intro h p hp ho
    obtain ⟨q,hq,hq'⟩ := List.mem_flatMap.mp hp
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hq'
    exact h q hq ((gridOccurs_fused_iff σ hda q).mpr
      ⟨t,by have := List.mem_range.mp ht; omega,ho⟩)


def trackedBasis : List GridPattern := [
  .ofLists [0, 2, 1] [0, 0, 0],
  .ofLists [0, 2, 1] [0, 0, 1],
  .ofLists [0, 2, 1] [0, 0, 2],
  .ofLists [0, 2, 1] [0, 1, 2],
  .ofLists [0, 2, 1] [1, 1, 2],
  .ofLists [0, 2, 1, 3] [0, 1, 1, 2],
  .ofLists [0, 2, 1, 3] [1, 1, 1, 2],
  .ofLists [0, 2, 3, 1] [0, 1, 1, 1],
  .ofLists [0, 2, 3, 1] [0, 2, 2, 2],
  .ofLists [0, 2, 3, 1] [1, 1, 1, 1],
  .ofLists [0, 2, 3, 1] [1, 2, 2, 2],
  .ofLists [0, 2, 3, 1] [2, 2, 2, 2],
  .ofLists [0, 2, 1, 4, 3] [0, 1, 1, 1, 1],
  .ofLists [0, 2, 1, 4, 3] [0, 2, 2, 2, 2],
  .ofLists [0, 2, 1, 4, 3] [1, 1, 1, 1, 1],
  .ofLists [0, 2, 1, 4, 3] [1, 2, 2, 2, 2],
  .ofLists [0, 2, 1, 4, 3] [2, 2, 2, 2, 2]
]

def splitBasis : List GridPattern := [
  .ofLists [0, 2, 1] [0, 0, 0],
  .ofLists [0, 2, 1] [0, 0, 1],
  .ofLists [0, 2, 1] [0, 0, 2],
  .ofLists [0, 2, 1] [0, 0, 3],
  .ofLists [0, 2, 1] [0, 1, 1],
  .ofLists [0, 2, 1] [0, 1, 2],
  .ofLists [0, 2, 1] [0, 1, 3],
  .ofLists [0, 2, 1] [0, 2, 3],
  .ofLists [0, 2, 1] [1, 1, 1],
  .ofLists [0, 2, 1] [1, 1, 2],
  .ofLists [0, 2, 1] [1, 1, 3],
  .ofLists [0, 2, 1] [1, 2, 3],
  .ofLists [0, 2, 1] [2, 2, 3],
  .ofLists [0, 2, 1, 3] [0, 2, 2, 3],
  .ofLists [0, 2, 1, 3] [1, 2, 2, 3],
  .ofLists [0, 2, 1, 3] [2, 2, 2, 3],
  .ofLists [0, 2, 3, 1] [0, 2, 2, 2],
  .ofLists [0, 2, 3, 1] [0, 3, 3, 3],
  .ofLists [0, 2, 3, 1] [1, 2, 2, 2],
  .ofLists [0, 2, 3, 1] [1, 3, 3, 3],
  .ofLists [0, 2, 3, 1] [2, 2, 2, 2],
  .ofLists [0, 2, 3, 1] [2, 3, 3, 3],
  .ofLists [0, 2, 3, 1] [3, 3, 3, 3],
  .ofLists [0, 2, 1, 4, 3] [0, 2, 2, 2, 2],
  .ofLists [0, 2, 1, 4, 3] [0, 3, 3, 3, 3],
  .ofLists [0, 2, 1, 4, 3] [1, 2, 2, 2, 2],
  .ofLists [0, 2, 1, 4, 3] [1, 3, 3, 3, 3],
  .ofLists [0, 2, 1, 4, 3] [2, 2, 2, 2, 2],
  .ofLists [0, 2, 1, 4, 3] [2, 3, 3, 3, 3],
  .ofLists [0, 2, 1, 4, 3] [3, 3, 3, 3, 3]
]

def GridPattern.code (p : GridPattern) : List (ℕ × ℕ) :=
  List.ofFn (fun i : Fin p.size => (p.rank i, p.column i))

theorem GridPattern.code_injective : Function.Injective code := by
  intro p q hp
  rcases p with ⟨m,r,c⟩
  rcases q with ⟨n,r',c'⟩
  have hmn : m = n := by simpa [code] using congrArg List.length hp
  subst n
  have hv (i : Fin m) : (r i,c i) = (r' i,c' i) := by
    have hg := congrArg (fun l : List (ℕ × ℕ) => getElem? l i.val) hp
    simpa [code, i.isLt] using hg
  congr
  · exact funext fun i => congrArg Prod.fst (hv i)
  · exact funext fun i => congrArg Prod.snd (hv i)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem certificate_splitBasis :
    (splitBasis.map GridPattern.code).toFinset =
      ((expandFusion trackedBasis).map GridPattern.code).toFinset := by decide +kernel

theorem rule9_avoidance_iff {n d a b : ℕ} (σ : Equiv.Perm (Fin n)) (hda : d ≤ a) :
    avoidsGrid σ (cols4 d a b) splitBasis ↔
      avoidsGrid σ (cols3 a b) trackedBasis := by
  rw [← avoidsGrid_fused_iff σ hda]
  unfold avoidsGrid
  have hin (L : List GridPattern) (p : GridPattern) :
      p.code ∈ (L.map GridPattern.code).toFinset ↔ p ∈ L := by
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨fun ⟨q,hq,he⟩ => GridPattern.code_injective he ▸ hq,
      fun hp => ⟨p,hp,rfl⟩⟩
  have hm (p : GridPattern) : p ∈ splitBasis ↔ p ∈ expandFusion trackedBasis := by
    rw [← hin, certificate_splitBasis, hin]
  simp only [hm]

end A001764.Round5

end

section

namespace A001764.Round5

abbrev Cuts (n : ℕ) := { ab : Fin (n+1) × Fin (n+1) // ab.1 ≤ ab.2 }
abbrev ThreeColumns (n : ℕ) := Equiv.Perm (Fin n) × Cuts n

def ThreeColumns.first {n : ℕ} (q : ThreeColumns n) : ℕ := q.2.val.1.val
def ThreeColumns.second {n : ℕ} (q : ThreeColumns n) : ℕ := q.2.val.2.val

/-- The source of rule 9 is the four-column F21 object; its tracking weight
    counts the points in the first, pre-fusion column only. -/
abbrev Rule9Source (n : ℕ) :=
  Σ q : ThreeColumns n, {d : Fin (q.first+1) //
    avoidsGrid q.1 (cols4 d.val q.first q.second) splitBasis}

/-- The target of rule 9 is F8. Its tracking weight counts all points in
    the newly fused first column. -/
abbrev Rule9Target (n : ℕ) :=
  {q : ThreeColumns n // avoidsGrid q.1 (cols3 q.first q.second) trackedBasis}

noncomputable instance (n : ℕ) : Fintype (Rule9Target n) := Fintype.ofFinite _
noncomputable instance (n : ℕ) : Fintype (Rule9Source n) := Fintype.ofFinite _

/-- Fusing the two left columns is reversible with a freely chosen cut in
    the merged column, including both extreme cuts. -/
def rule9Equiv (n : ℕ) :
    Rule9Source n ≃ (Σ q : Rule9Target n, Fin (q.val.first+1)) where
  toFun s :=
    ⟨⟨s.1,(rule9_avoidance_iff s.1.1 (by have := s.2.val.isLt; omega)).mp s.2.property⟩,
      s.2.val⟩
  invFun s :=
    ⟨s.1.val,⟨s.2,(rule9_avoidance_iff s.1.val.1
      (by have := s.2.isLt; omega)).mpr s.1.property⟩⟩
  left_inv s := by cases s; rfl
  right_inv s := by cases s; rfl

theorem rule9_tracker {n : ℕ} (s : Rule9Source n) :
    (rule9Equiv n s).2.val = s.2.val.val := rfl

/-- Per-size polynomial form of F21 = (k F8(k) − F8(1))/(k−1).
    Written without division so it also holds at k = 1. -/
theorem rule9_weighted_sum {R : Type*} [CommRing R] (k : R) (n : ℕ) :
    (k - 1) * (∑ s : Rule9Source n, k^s.2.val.val) =
      k * (∑ q : Rule9Target n, k^q.val.first) - (Nat.card (Rule9Target n) : R) := by
  classical
  have hs :
      (∑ s : Rule9Source n, k^s.2.val.val) =
        ∑ q : Rule9Target n, ∑ d : Fin (q.val.first+1), k^d.val := by
    calc
      _ = ∑ q : (Σ q : Rule9Target n, Fin (q.val.first+1)), k^q.2.val :=
        Fintype.sum_equiv (rule9Equiv n) _ _ (fun _ => rfl)
      _ = _ := Fintype.sum_sigma _
  have telescope (r : ℕ) : (k - 1) * (∑ i ∈ Finset.range r, k^i) = k^r - 1 := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring
  have hc : (Nat.card (Rule9Target n) : R) =
      ∑ _ : Rule9Target n, (1 : R) := by simp [Nat.card_eq_fintype_card]
  rw [hs, Finset.mul_sum, Finset.mul_sum, hc, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [Fin.sum_univ_eq_sum_range, telescope, pow_succ, mul_comm (k^q.val.first)]

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4 OMA.S_oeis_a001764

private theorem highVal {m n : ℕ} (σ : Equiv.Perm (Fin m))
    (τ : Equiv.Perm (Fin n)) (i : Fin m) :
    (skewSum σ τ (Fin.castAdd n i)).val = n+(σ i).val := by
  unfold skewSum
  simp only [Equiv.trans_apply,directSum_left,Fin.revPerm_apply,Fin.val_rev,Fin.val_castAdd]
  have := (σ i).isLt
  omega

private theorem lowVal {m n : ℕ} (σ : Equiv.Perm (Fin m))
    (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    (skewSum σ τ (Fin.natAdd m i)).val = (τ i).val := by
  unfold skewSum
  simp only [Equiv.trans_apply,directSum_right,Fin.revPerm_apply,Fin.val_rev,Fin.val_natAdd]
  have := (τ i).isLt
  omega

private theorem skewSum_injective {m n : ℕ}
    {σ σ' : Equiv.Perm (Fin m)} {τ τ' : Equiv.Perm (Fin n)}
    (h : skewSum σ τ = skewSum σ' τ') : σ = σ' ∧ τ = τ' := by
  constructor
  · ext i
    have he := congrArg (fun e : Equiv.Perm (Fin (m+n)) => (e (Fin.castAdd n i)).val) h
    rw [highVal,highVal,Nat.add_left_cancel_iff] at he
    exact he
  · ext i
    have he := congrArg (fun e : Equiv.Perm (Fin (m+n)) => (e (Fin.natAdd m i)).val) h
    rw [lowVal,lowVal] at he
    exact he

/-- The placement class F5, stratified by the value n of the maximum to the
    right of the first mark. There are exactly m larger unmarked entries. -/
abbrev PeakSlice (m n : ℕ) :=
  Σ cut : Fin (m+(n+1)+1), {τ : PermPalPlaced cut //
    ∃ peak : Fin (m+(n+1)), RightPeak τ.val cut peak ∧ (τ.val peak).val = n}

/-- The low component has size n+1 and its maximum is to the right of
    the marked insertion column. Its maximum is the second mark. -/
abbrev LowPlaced (n : ℕ) :=
  Σ cut : Fin (n+2), {τ : PermPalPlaced cut //
    cut.val ≤ (τ.val.symm (Fin.last n)).val}

private def combinePeakSlice {m n : ℕ}
    (x : PermPalRoot m × LowPlaced n) : PeakSlice m n := by
  rcases x with ⟨σ,cut,τ,hτ⟩
  let p := τ.val.symm (Fin.last n)
  let q := skewSum σ.val τ.val
  refine ⟨shiftCut m cut,⟨⟨q,(permPalPlaced_skewSum _ _ cut).mpr ⟨σ.property,τ.property⟩⟩,
    Fin.natAdd m p,⟨?_,?_⟩,?_⟩⟩
  · change m+cut.val ≤ m+p.val
    exact Nat.add_le_add_left hτ _
  · intro i hi
    change m+cut.val ≤ i.val at hi
    let j : Fin (n+1) := ⟨i.val-m,by have := i.isLt; omega⟩
    have ij : Fin.natAdd m j = i := Fin.ext (by simp [j]; omega)
    change (q i).val ≤ (q (Fin.natAdd m p)).val
    rw [← ij,lowVal,lowVal]
    have hp : τ.val p = Fin.last n := τ.val.apply_symm_apply _
    rw [hp]
    exact Nat.le_of_lt_succ (τ.val j).isLt
  · change (q (Fin.natAdd m p)).val = n
    rw [lowVal]
    simp [p]

private theorem peakSlice_ext {m n : ℕ} {x y : PeakSlice m n}
    (hc : x.1 = y.1) (hp : x.2.val.val = y.2.val.val) : x = y := by
  rcases x with ⟨c,τ⟩
  rcases y with ⟨d,ρ⟩
  dsimp only at hc hp
  subst d
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext (Subtype.ext hp)))

/-- Exact dependent product for the detached high prefix in the actual
    PermPAL placement class, preserving both the cut and right-peak rank. -/
noncomputable def peakSliceEquiv (m n : ℕ) :
    PeakSlice m n ≃ PermPalRoot m × LowPlaced n := by
  refine (Equiv.ofBijective combinePeakSlice ?_).symm
  constructor
  · rintro ⟨σ₁,c₁,τ₁,h₁⟩ ⟨σ₂,c₂,τ₂,h₂⟩ h
    have hc : shiftCut m c₁ = shiftCut m c₂ := congrArg Sigma.fst h
    have ec : c₁ = c₂ := by
      apply Fin.ext
      have hh := congrArg Fin.val hc
      change m+c₁.val = m+c₂.val at hh
      omega
    subst c₂
    have ht : skewSum σ₁.val τ₁.val = skewSum σ₂.val τ₂.val :=
      congrArg (fun z : PeakSlice m n => z.2.val.val) h
    obtain ⟨hs,ht⟩ := skewSum_injective ht
    exact Prod.ext (Subtype.ext hs) (Sigma.ext rfl (heq_of_eq (Subtype.ext (Subtype.ext ht))))
  · rintro ⟨c,τ,peak,hp,hv⟩
    have hcut := permPal_high_block τ hp
    rw [hv,show m+(n+1)-1-n = m by omega] at hcut
    let σ := (leftBlock hcut).trans Fin.revPerm
    let low :=  (rightBlock hcut).trans Fin.revPerm
    have hs : skewSum σ low = τ.val := skewSplit_of_complementCut hcut
    have hc : m ≤ c.val := by
      by_contra! hh
      let j : Fin (m+(n+1)) := ⟨c.val,by omega⟩
      have hj : j.val < m+(n+1)-1-(τ.val peak).val := by dsimp [j]; omega
      have hvj := (permPal_high_prefix_iff τ hp j).mp hj
      exact (not_lt_of_ge (hp.2 j le_rfl)) hvj
    let d : Fin (n+2) := ⟨c.val-m,by have := c.isLt; omega⟩
    have ed : shiftCut m d = c := Fin.ext (by
      change m+(c.val-m) = c.val
      omega)
    have ha : PermPalAvoids σ ∧ PermPalPlacementCondition low d := by
      apply (permPalPlaced_skewSum σ low d).mp
      rw [hs,ed]
      exact τ.property
    have hmp : m ≤ peak.val := hc.trans hp.1
    let i : Fin (n+1) := ⟨peak.val-m,by have := peak.isLt; omega⟩
    have hei : Fin.natAdd m i = peak := Fin.ext (by simp [i]; omega)
    have hvi : low i = Fin.last n := by
      apply Fin.ext
      change (low i).val = n
      rwa [← lowVal σ low i,hs,hei]
    have hi : low.symm (Fin.last n) = i := by rw [← hvi,Equiv.symm_apply_apply]
    have hd : d.val ≤ (low.symm (Fin.last n)).val := by
      rw [hi]
      change c.val-m ≤ peak.val-m
      exact Nat.sub_le_sub_right hp.1 m
    refine ⟨⟨⟨σ,ha.1⟩,d,⟨low,ha.2⟩,hd⟩,?_⟩
    exact peakSlice_ext ed hs

theorem peakSlice_card (m n : ℕ) :
    Nat.card (PeakSlice m n) = Nat.card (PermPalRoot m) * Nat.card (LowPlaced n) := by
  rw [Nat.card_congr (peakSliceEquiv m n), Nat.card_prod]

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4 OMA.S_oeis_a001764

/-- Add the two maximum markers in their actual columns. The marker of
    value n+1 comes before the marker of value n. -/
def twoMax {n : ℕ} (a b : Fin (n+1)) (σ : Equiv.Perm (Fin n)) :=
  placeMaximum a.castSucc (placeMaximum b σ)

inductive Site (n : ℕ) where
  | point : Fin n → Site n
  | global : Site n
  | right : Site n

def Site.index {n : ℕ} (a b : Fin (n+1)) : Site n → Fin (n+2)
  | .point i => a.castSucc.succAbove (b.succAbove i)
  | .global => a.castSucc
  | .right => a.castSucc.succAbove b

private theorem aboveVal {n : ℕ} (c : Fin (n+1)) (i : Fin n) :
    (c.succAbove i).val = i.val + if c.val ≤ i.val then 1 else 0 := by
  by_cases h : i.val < c.val
  · rw [Fin.succAbove_of_castSucc_lt c i h]
    simp [show ¬ c.val ≤ i.val by omega]
  · rw [Fin.succAbove_of_le_castSucc c i (by exact Nat.le_of_not_gt h)]
    simp [Nat.le_of_not_gt h]

def Site.col {n : ℕ} (a b : Fin (n+1)) : Site n → ℕ
  | .point i => 2 * cols3 a.val b.val i
  | .global => 1
  | .right => 3

def Site.val {n : ℕ} (σ : Equiv.Perm (Fin n)) : Site n → ℕ
  | .point i => (σ i).val
  | .global => n+1
  | .right => n

theorem Site.twoMax_value {n : ℕ} (a b : Fin (n+1)) (σ : Equiv.Perm (Fin n))
    (s : Site n) : (twoMax a b σ (s.index a b)).val = s.val σ := by
  cases s <;> simp [twoMax, Site.index, Site.val]

theorem Site.index_surjective {n : ℕ} (a b : Fin (n+1)) : Function.Surjective (Site.index a b) := by
  intro j
  refine Fin.succAboveCases a.castSucc ?_ (fun i => ?_) j
  · exact ⟨.global, rfl⟩
  · refine Fin.succAboveCases b ?_ (fun u => ?_) i
    · exact ⟨.right, rfl⟩
    · exact ⟨.point u,rfl⟩

/-- The exact order of marked and unmarked sites is determined by their
    column numbers and, within an unmarked column, by the original index. -/
def Site.before {n : ℕ} (a b : Fin (n+1)) (s t : Site n) : Prop :=
  s.col a b < t.col a b ∨
    ∃ i j, s = .point i ∧ t = .point j ∧ s.col a b = t.col a b ∧ i < j

theorem Site.before_iff {n : ℕ} {a b : Fin (n+1)} (hab : a ≤ b) (s t : Site n) :
    s.before a b t ↔ s.index a b < t.index a b := by
  have hmono : Monotone (cols3 a.val b.val : Fin n → ℕ) := by
    intro i j h
    have hv : i.val ≤ j.val := h
    unfold cols3
    first | split_ifs <;> omega | omega
  have hab' : a.val ≤ b.val := hab
  cases s <;> cases t
  · rename_i i j
    simp only [Site.before, Site.col, Site.index, Fin.succAbove_lt_succAbove_iff,
      Site.point.injEq]
    constructor
    · rintro (hl | ⟨_,_,rfl,rfl,_,h⟩)
      · by_contra! hn
        have hh := hmono hn
        omega
      · exact h
    · intro h
      rcases lt_or_eq_of_le (hmono h.le) with lt | eq
      · left; omega
      · right; exact ⟨i,j,rfl,rfl,by rw [eq],h⟩
  all_goals
    simp only [Site.before,Site.col,Site.index,reduceCtorEq,
      exists_false,false_and,and_false,or_false]
    simp only [Fin.lt_def, Fin.val_castSucc, aboveVal, cols3]
    first | split_ifs <;> omega | omega

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4 OMA.S_oeis_a001764

def marked (c : Fin 5) : Prop := c.val = 1 ∨ c.val = 3
instance (c : Fin 5) : Decidable (marked c) := by unfold marked; infer_instance

def level (c : Fin 5) : ℕ := if c.val = 1 then 2 else if c.val = 3 then 1 else 0

def Admissible {k : ℕ} (p : Fin k → ℕ) (s : Fin k → Fin 5) : Prop :=
  (∀ i j, i ≤ j → s i ≤ s j) ∧
  (∀ i j, s i = s j → marked (s i) → i = j) ∧
  (∀ i j, marked (s i) ∨ marked (s j) → (p i < p j ↔ level (s i) < level (s j)))

instance {k : ℕ} (p : Fin k → ℕ) (s : Fin k → Fin 5) : Decidable (Admissible p s) := by
  unfold Admissible
  infer_instance

def unmarked {k : ℕ} (s : Fin k → Fin 5) : Finset (Fin k) :=
  Finset.univ.filter fun i => ¬ marked (s i)

def projectIndex {k : ℕ} (s : Fin k → Fin 5) :
    Fin (unmarked s).card ↪o Fin k :=
  (unmarked s).orderEmbOfFin rfl

private theorem projectIndex_mem {k : ℕ} {s : Fin k → Fin 5} (i : Fin (unmarked s).card) :
    ¬ marked (s (projectIndex s i)) :=
  (Finset.mem_filter.mp ((unmarked s).orderEmbOfFin_mem rfl i)).2

def projectPattern {k : ℕ} (p : Fin k → ℕ) (s : Fin k → Fin 5) : GridPattern :=
  ⟨(unmarked s).card, fun i => p (projectIndex s i), fun i => (s (projectIndex s i)).val / 2⟩

/-- The two marked columns of the exact permutation, kept separate. -/
def Site.slot {n : ℕ} (a b : Fin (n+1)) (t : Site n) : Fin 5 :=
  ⟨t.col a b, by cases t <;> simp [Site.col,cols3] <;> split_ifs <;> decide⟩

private theorem Site.match_unmarked {n : ℕ} (a b : Fin (n+1)) (t : Site n) :
    ¬ marked (t.slot a b) ↔ ∃ i, t = .point i := by
  cases t <;> simp [Site.slot, Site.col, marked, cols3] <;> split_ifs <;> simp_all

private theorem Site.same_mark {n : ℕ} {a b : Fin (n+1)} {u v : Site n}
    (hs : u.slot a b = v.slot a b) (hm : marked (u.slot a b)) : u = v := by
  cases u <;> cases v <;> simp [Site.slot,Site.col,marked,cols3] at * <;>
    split_ifs at * <;> simp_all <;> omega

private theorem Site.mark_cmp {n : ℕ} (a b : Fin (n+1)) (σ : Equiv.Perm (Fin n))
    (u v : Site n) (hm : marked (u.slot a b) ∨ marked (v.slot a b)) :
    u.val σ < v.val σ ↔ level (u.slot a b) < level (v.slot a b) := by
  cases u <;> cases v <;>
    simp [Site.slot,Site.col,Site.val,marked,level,cols3] at * <;>
    split_ifs at * <;> simp_all
  all_goals
    first | omega | exact (σ _).isLt | exact Nat.lt_succ_of_lt (σ _).isLt

/-- Any forbidden occurrence in the actual twice-marked plot projects to a
    gridded occurrence with a valid allocation of its marker positions. -/
theorem occurrence_projects {n k : ℕ} {a b : Fin (n+1)} (hab : a ≤ b)
    (σ : Equiv.Perm (Fin n)) (p : Fin k → ℕ)
    (e : Fin k → Fin (n+2)) (he : StrictMono e)
    (hr : ∀ i j, twoMax a b σ (e i) < twoMax a b σ (e j) ↔ p i < p j) :
    ∃ s, Admissible p s ∧ gridOccurs σ (cols3 a.val b.val) (projectPattern p s) := by
  classical
  choose T hT using fun i => Site.index_surjective a b (e i)
  let s (i : Fin k) := (T i).slot a b
  have hm (i j : Fin k) (h : i < j) : (T i).before a b (T j) := by
    apply (Site.before_iff hab _ _).mpr
    rw [hT i,hT j]
    exact he h
  have hv (i j : Fin k) :
      (T i).val σ < (T j).val σ ↔ p i < p j := by
    have hh := hr i j
    rw [← hT i, ← hT j, Fin.lt_def, Site.twoMax_value, Site.twoMax_value] at hh
    exact hh
  refine ⟨s,⟨?_,?_,?_⟩,?_⟩
  · intro i j hij
    rcases lt_or_eq_of_le hij with h | rfl
    · rcases hm i j h with hl | ⟨_,_,_,_,hl,_⟩
      · exact hl.le
      · exact le_of_eq (Fin.ext hl)
    · rfl
  · intro i j hij hj
    exact he.injective (by rw [← hT i,← hT j,Site.same_mark hij hj])
  · intro i j hh
    exact (hv i j).symm.trans (Site.mark_cmp a b σ _ _ hh)
  have hpoint (i : Fin (unmarked s).card) :
      ∃ x, T (projectIndex s i) = .point x :=
    (Site.match_unmarked a b _).mp (projectIndex_mem i)
  choose g hg using hpoint
  refine ⟨g,?_,?_,?_⟩
  · intro i j hij
    have hlt := hm _ _ ((projectIndex s).strictMono hij)
    simpa only [hg i,hg j,Site.before_iff hab _ _,Site.index,
      Fin.succAbove_lt_succAbove_iff] using hlt
  · intro i j
    have hh := hv (projectIndex s i) (projectIndex s j)
    simpa only [hg i,hg j,Site.val,Fin.lt_def,projectPattern] using hh
  · intro i
    change cols3 a.val b.val (g i) = (s (projectIndex s i)).val / 2
    change cols3 a.val b.val (g i) = ((T (projectIndex s i)).slot a b).val / 2
    rw [hg i]
    simp [Site.slot,Site.col]

/-- A projected forbidden pattern lifts back to the actual twice-marked
    permutation when its marker allocation is admissible. -/
theorem occurrence_lifts {n k : ℕ} {a b : Fin (n+1)} (hab : a ≤ b)
    (σ : Equiv.Perm (Fin n)) (p : Fin k → ℕ) (s : Fin k → Fin 5)
    (hs : Admissible p s) :
    gridOccurs σ (cols3 a.val b.val) (projectPattern p s) →
      ¬ Avoids (twoMax a b σ) p := by
  classical
  rintro ⟨g,hg,hgr,hgc⟩ hbad
  let E := (unmarked s).orderIsoOfFin rfl
  let j (i : Fin k) (h : i ∈ unmarked s) : Fin (unmarked s).card := E.symm ⟨i,h⟩
  have j_spec (i : Fin k) (h : i ∈ unmarked s) : projectIndex s (j i h) = i := by
    exact congrArg Subtype.val (E.apply_symm_apply ⟨i,h⟩)
  have hj (i : Fin k) : i ∈ unmarked s ↔ ¬ marked (s i) := by simp [unmarked]
  let T (i : Fin k) : Site n :=
    if h : i ∈ unmarked s then .point (g (j i h))
    else if (s i).val = 1 then .global else .right
  have hp (i : Fin k) (h : i ∈ unmarked s) :
      T i = .point (g (j i h)) := by simp [T,h]
  have ht (i : Fin k) : (T i).slot a b = s i := by
    apply Fin.ext
    by_cases h : i ∈ unmarked s
    · rw [hp i h]
      have hh := hgc (j i h)
      change cols3 a.val b.val (g (j i h)) = (s (projectIndex s (j i h))).val / 2 at hh
      rw [j_spec i h] at hh
      have hn := (hj i).mp h
      have hb := (s i).isLt
      change 2 * cols3 a.val b.val (g (j i h)) = (s i).val
      rw [hh]
      unfold marked at hn
      omega
    · have hh : marked (s i) := by
        by_contra hn; exact h ((hj i).mpr hn)
      rcases hh with hh | hh
      · simp [T,h,hh,Site.slot,Site.col]
      · simp [T,h,hh,Site.slot,Site.col]
  apply hbad
  refine ⟨fun i => (T i).index a b,?_,?_⟩
  · intro i l hil
    apply (Site.before_iff hab _ _).mp
    rcases lt_or_eq_of_le (hs.1 i l hil.le) with hLt | hEq
    · exact Or.inl (by
        change ((T i).slot a b).val < ((T l).slot a b).val
        rw [ht,ht]
        exact hLt)
    · have notMark : ¬ marked (s i) := fun hm => (ne_of_lt hil) (hs.2.1 i l hEq hm)
      have hi := (hj i).mpr notMark
      have hl := (hj l).mpr (hEq ▸ notMark)
      have hSmall : j i hi < j l hl := by
        exact E.symm.strictMono hil
      refine Or.inr ⟨_,_,hp i hi,hp l hl,?_,hg hSmall⟩
      exact congrArg Fin.val ((ht i).trans (hEq.trans (ht l).symm))
  · intro i l
    rw [Fin.lt_def, Site.twoMax_value, Site.twoMax_value]
    by_cases hm : marked (s i) ∨ marked (s l)
    · have hs' := Site.mark_cmp a b σ (T i) (T l) (by rwa [ht,ht])
      rw [ht,ht] at hs'
      exact hs'.trans (hs.2.2 i l hm).symm
    · have hi := (hj i).mpr (fun hh => hm (Or.inl hh))
      have hl := (hj l).mpr (fun hh => hm (Or.inr hh))
      have ha := hgr (j i hi) (j l hl)
      change σ (g (j i hi)) < σ (g (j l hl)) ↔
        p (projectIndex s (j i hi)) < p (projectIndex s (j l hl)) at ha
      rw [j_spec i hi,j_spec l hl] at ha
      rw [hp i hi,hp l hl]
      exact ha

/-- The source side of the literal certificate is actual permutation avoidance. -/
theorem twoMax_avoids_iff {n k : ℕ} {a b : Fin (n+1)} (hab : a ≤ b)
    (σ : Equiv.Perm (Fin n)) (p : Fin k → ℕ) :
    Avoids (twoMax a b σ) p ↔
      ∀ s, Admissible p s → ¬ gridOccurs σ (cols3 a.val b.val) (projectPattern p s) := by
  constructor
  · intro h s hs hocc
    exact occurrence_lifts hab σ p s hs hocc h
  · rintro h ⟨e,he,hr⟩
    obtain ⟨s,hs,ho⟩ := occurrence_projects hab σ p e he hr
    exact h s hs ho

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4 OMA.S_oeis_a001764

def Subpattern (p q : GridPattern) : Prop :=
  ∃ j : Fin p.size → Fin q.size,
      (∀ i k, i < k → j i < j k) ∧
      (∀ i k, q.rank (j i) < q.rank (j k) ↔ p.rank i < p.rank k) ∧
      ∀ i, q.column (j i) = p.column i

theorem gridOccurs_of_subpattern {n : ℕ} {σ : Equiv.Perm (Fin n)}
    {col : Fin n → ℕ} {p q : GridPattern} (hp : Subpattern p q) :
    gridOccurs σ col q → gridOccurs σ col p := by
  rintro ⟨e,he,hr,hc⟩
  obtain ⟨j,hj,hs,hjcol⟩ := hp
  refine ⟨e ∘ j,he.comp hj,fun i k => (hr _ _).trans (hs _ _),?_⟩
  intro i
  exact (hc _).trans (hjcol _)




private def selectedList {k : ℕ} (s : Fin k → Fin 5) : List (Fin k) :=
  (List.finRange k).filter (fun i => decide (¬ marked (s i)))

private theorem selectedList_eq_sort {k : ℕ} (s : Fin k → Fin 5) :
    (unmarked s).sort = selectedList s :=
  (unmarked s).sortedLT_sort.eq_of_mem_iff
    (List.pairwise_filter.mpr ((List.sortedLT_finRange k).pairwise.imp
      (fun hij _ _ => hij))).sortedLT
    (by intro x; simp [unmarked,selectedList])

private def fastProjectPattern {k : ℕ} (p : Fin k → ℕ) (s : Fin k → Fin 5) : GridPattern :=
  ⟨(selectedList s).length,fun i => p ((selectedList s).get i),
    fun i => (s ((selectedList s).get i)).val/2⟩

private theorem projectPattern_eq_fast {k : ℕ} (p : Fin k → ℕ) (s : Fin k → Fin 5) :
    projectPattern p s = fastProjectPattern p s := by
  apply GridPattern.code_injective
  apply List.ext_getElem
  · simp [GridPattern.code, projectPattern, fastProjectPattern,
      ← selectedList_eq_sort s, Finset.length_sort]
  · intro i hi hi'
    simp only [GridPattern.code,List.getElem_ofFn,projectPattern,fastProjectPattern]
    have hs : projectIndex s ⟨i,by simpa [GridPattern.code,projectPattern] using hi⟩ =
        (selectedList s)[i]'(by simpa [GridPattern.code,fastProjectPattern] using hi') := by
      unfold projectIndex
      rw [Finset.orderEmbOfFin_apply]
      simp only [selectedList_eq_sort]
      rfl

    rw [hs]
    rfl

private def p4 : Fin 4 → ℕ := ![1, 3, 4, 2]
private def masks4 : List (Fin 4 → Fin 5) := [![0, 0, 0, 0], ![0, 0, 0, 2], ![0, 0, 0, 4], ![0, 0, 1, 2], ![0, 0, 1, 4], ![0, 0, 2, 2], ![0, 0, 2, 4], ![0, 0, 3, 4], ![0, 0, 4, 4], ![0, 2, 2, 2], ![0, 2, 2, 4], ![0, 2, 3, 4], ![0, 2, 4, 4], ![0, 4, 4, 4], ![2, 2, 2, 2], ![2, 2, 2, 4], ![2, 2, 3, 4], ![2, 2, 4, 4], ![2, 4, 4, 4], ![4, 4, 4, 4]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem masks4_complete :
    ∀ s, Admissible p4 s → s ∈ masks4 := by decide +kernel

private theorem cover4 (s : Fin 4 → Fin 5) (hs : Admissible p4 s) :
    ∃ p ∈ trackedBasis, Subpattern p (fastProjectPattern p4 s) := by
  have hm := masks4_complete s hs
  simp only [masks4,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · refine ⟨_, List.get_mem trackedBasis ⟨0, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨1, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨2, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨1, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨2, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨1, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨2, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨2, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨2, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨7, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨3, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨3, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨3, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨8, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨9, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨4, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨4, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨4, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨10, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨11, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel

private def p5 : Fin 5 → ℕ := ![1, 3, 2, 5, 4]
private def masks5 : List (Fin 5 → Fin 5) := [![0, 0, 0, 0, 0], ![0, 0, 0, 0, 2], ![0, 0, 0, 0, 4], ![0, 0, 0, 1, 2], ![0, 0, 0, 1, 3], ![0, 0, 0, 1, 4], ![0, 0, 0, 2, 2], ![0, 0, 0, 2, 4], ![0, 0, 0, 3, 4], ![0, 0, 0, 4, 4], ![0, 0, 2, 2, 2], ![0, 0, 2, 2, 4], ![0, 0, 2, 3, 4], ![0, 0, 2, 4, 4], ![0, 0, 4, 4, 4], ![0, 2, 2, 2, 2], ![0, 2, 2, 2, 4], ![0, 2, 2, 3, 4], ![0, 2, 2, 4, 4], ![0, 2, 4, 4, 4], ![0, 4, 4, 4, 4], ![2, 2, 2, 2, 2], ![2, 2, 2, 2, 4], ![2, 2, 2, 3, 4], ![2, 2, 2, 4, 4], ![2, 2, 4, 4, 4], ![2, 4, 4, 4, 4], ![4, 4, 4, 4, 4]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem masks5_complete :
    ∀ s, Admissible p5 s → s ∈ masks5 := by decide +kernel

private theorem cover5 (s : Fin 5 → Fin 5) (hs : Admissible p5 s) :
    ∃ p ∈ trackedBasis, Subpattern p (fastProjectPattern p5 s) := by
  have hm := masks5_complete s hs
  simp only [masks5,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · refine ⟨_, List.get_mem trackedBasis ⟨0, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨0, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨0, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨0, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨0, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨0, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨0, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨0, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨0, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨0, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨1, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨1, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨1, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨1, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨2, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨12, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨4, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨3, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨4, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨5, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨5, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨3, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨13, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨4, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨14, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨4, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨4, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨4, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨6, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨6, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨4, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨15, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨4, by decide +kernel⟩], ?_⟩
    decide +kernel
  · refine ⟨_, List.get_mem trackedBasis ⟨16, by decide⟩, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨4, by decide +kernel⟩], ?_⟩
    decide +kernel

private theorem basis_lifts :
    ∀ p ∈ trackedBasis,
      (∃ s, Admissible p4 s ∧ Subpattern (fastProjectPattern p4 s) p) ∨
      (∃ s, Admissible p5 s ∧ Subpattern (fastProjectPattern p5 s) p) := by
  intro p hp
  simp only [trackedBasis,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · right
    refine ⟨![0, 0, 0, 1, 3], by decide, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · left
    refine ⟨![0, 0, 1, 2], by decide, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · left
    refine ⟨![0, 0, 1, 4], by decide, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · left
    refine ⟨![0, 2, 3, 4], by decide, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · left
    refine ⟨![2, 2, 3, 4], by decide, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩], ?_⟩
    decide +kernel
  · right
    refine ⟨![0, 2, 2, 3, 4], by decide, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · right
    refine ⟨![2, 2, 2, 3, 4], by decide, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · left
    refine ⟨![0, 2, 2, 2], by decide, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · left
    refine ⟨![0, 4, 4, 4], by decide, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · left
    refine ⟨![2, 2, 2, 2], by decide, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · left
    refine ⟨![2, 4, 4, 4], by decide, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · left
    refine ⟨![4, 4, 4, 4], by decide, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩], ?_⟩
    decide +kernel
  · right
    refine ⟨![0, 2, 2, 2, 2], by decide, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨4, by decide +kernel⟩], ?_⟩
    decide +kernel
  · right
    refine ⟨![0, 4, 4, 4, 4], by decide, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨4, by decide +kernel⟩], ?_⟩
    decide +kernel
  · right
    refine ⟨![2, 2, 2, 2, 2], by decide, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨4, by decide +kernel⟩], ?_⟩
    decide +kernel
  · right
    refine ⟨![2, 4, 4, 4, 4], by decide, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨4, by decide +kernel⟩], ?_⟩
    decide +kernel
  · right
    refine ⟨![4, 4, 4, 4, 4], by decide, ![⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨4, by decide +kernel⟩], ?_⟩
    decide +kernel

/-- The raw three-column F8 class agrees exactly with the actual permutation
    class obtained by inserting the two maximum markers. -/
theorem root_of_twoMax_iff {n : ℕ} {a b : Fin (n+1)} (hab : a ≤ b)
    (σ : Equiv.Perm (Fin n)) :
    PermPalAvoids (twoMax a b σ) ↔
      avoidsGrid σ (cols3 a.val b.val) trackedBasis := by
  change (Avoids (twoMax a b σ) p4 ∧ Avoids (twoMax a b σ) p5) ↔ _
  rw [twoMax_avoids_iff hab,twoMax_avoids_iff hab]
  constructor
  · rintro ⟨h4,h5⟩ p hp hocc
    obtain ⟨s,hs,hl⟩ | ⟨s,hs,hl⟩ := basis_lifts p hp
    · exact h4 s hs (by rw [projectPattern_eq_fast]; exact gridOccurs_of_subpattern hl hocc)
    · exact h5 s hs (by rw [projectPattern_eq_fast]; exact gridOccurs_of_subpattern hl hocc)
  · intro h
    constructor
    · intro s hs hocc
      obtain ⟨p,hp,hsub⟩ := cover4 s hs
      rw [projectPattern_eq_fast] at hocc
      exact h p hp (gridOccurs_of_subpattern hsub hocc)
    · intro s hs hocc
      obtain ⟨p,hp,hsub⟩ := cover5 s hs
      rw [projectPattern_eq_fast] at hocc
      exact h p hp (gridOccurs_of_subpattern hsub hocc)

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4 OMA.S_oeis_a001764

private def attachRightMaximum {n : ℕ} (x : Rule9Target n) : LowPlaced n := by
  rcases x with ⟨⟨τ,⟨a,b⟩,hab⟩,ht⟩
  have hi := (root_of_twoMax_iff hab τ).mpr ht
  have hp : PermPalPlacementCondition (placeMaximum b τ) a.castSucc :=
    (permPal_place_pred _ _).mp hi
  exact ⟨a.castSucc,⟨placeMaximum b τ,hp⟩,by simpa only [inverse_placeMaximum_peak,Fin.val_castSucc] using (show a.val ≤ b.val from hab)⟩

/-- F8 is the actual low-component placement class, with its remaining
    maximum inserted and no additional restrictions. -/
noncomputable def lowPlacedEquiv (n : ℕ) : LowPlaced n ≃ Rule9Target n := by
  refine (Equiv.ofBijective attachRightMaximum ?_).symm
  constructor
  · rintro ⟨⟨τ,⟨a,b⟩,hab⟩,ht⟩ ⟨⟨τ',⟨a',b'⟩,hab'⟩,ht'⟩ he
    have h1 : a.castSucc = a'.castSucc := congrArg Sigma.fst he
    have h2 : placeMaximum b τ = placeMaximum b' τ' :=
      congrArg (fun x : LowPlaced n => x.2.val.val) he
    have ha : a=a' := Fin.castSucc_inj.mp h1
    have hb : b=b' := by
      simpa only [inverse_placeMaximum_peak] using
        congrArg (fun σ : Equiv.Perm (Fin (n+1)) => σ.symm (Fin.last n)) h2
    subst a'
    subst b'
    have hτ := placeMaximum_injective _ h2
    subst τ'
    rfl
  · rintro ⟨cut,placed,hplaced⟩
    let b := placed.val.symm (Fin.last n)
    let a : Fin (n+1) := ⟨cut.val,lt_of_le_of_lt hplaced b.isLt⟩
    have ha : a.castSucc = cut := Fin.ext rfl
    let τ := deleteMaximum placed.val
    have hh : placeMaximum b τ = placed.val := placeMaximum_deleteMaximum _
    have hab : a ≤ b := hplaced
    have hp : PermPalAvoids (twoMax a b τ) := by
      unfold twoMax
      rw [ha,hh]
      exact (permPal_place_pred _ _).mpr placed.property
    let x : Rule9Target n := ⟨⟨τ,⟨⟨a,b⟩,hab⟩⟩,(root_of_twoMax_iff hab τ).mp hp⟩
    refine ⟨x,?_⟩
    have ht : (attachRightMaximum x).1 = cut := ha
    have hv : (attachRightMaximum x).2.val.val = placed.val := hh
    generalize attachRightMaximum x = y at *
    rcases y with ⟨d,z⟩
    dsimp only at ht hv
    subst d
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext (Subtype.ext hv)))

theorem peakSlice_card_fused (m n : ℕ) :
    Nat.card (PeakSlice m n) =
      Nat.card (PermPalRoot m) * Nat.card (Rule9Target n) := by
  rw [peakSlice_card, Nat.card_congr (lowPlacedEquiv n)]

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4 OMA.S_oeis_a001764 PowerSeries

private abbrev OpenRight (n : ℕ) := Σ c : Fin n, PermPalPlaced c.castSucc

private abbrev AtRightRank (n r : ℕ) :=
  Σ c : Fin (n+1), {τ : PermPalPlaced c //
    ∃ p : Fin n, RightPeak τ.val c p ∧ (τ.val p).val = r}

private noncomputable def openPeak {n : ℕ} (x : OpenRight n) : Fin n :=
  Classical.choose (rightPeak_exists x.2.val x.1.castSucc x.1.isLt)

private theorem openPeak_spec {n : ℕ} (x : OpenRight n) :
    RightPeak x.2.val x.1.castSucc (openPeak x) :=
  Classical.choose_spec (rightPeak_exists x.2.val x.1.castSucc x.1.isLt)

private noncomputable def rankFiber {n : ℕ} (r : Fin n) :
    {x : OpenRight n // x.2.val (openPeak x) = r} ≃ AtRightRank n r.val := by
  classical
  refine Equiv.ofBijective (fun x =>
    (⟨x.val.1.castSucc,⟨x.val.2, openPeak x.val, openPeak_spec x.val,
      congrArg Fin.val x.property⟩⟩ : AtRightRank n r.val)) ?_
  constructor
  · rintro ⟨⟨a,v⟩,h⟩ ⟨⟨b,w⟩,h'⟩ he
    have hcut : a=b := Fin.castSucc_inj.mp (congrArg Sigma.fst he)
    subst b
    have hh : v.val = w.val := congrArg (fun z : AtRightRank n r.val => z.2.val.val) he
    exact Subtype.ext (Sigma.ext rfl (heq_of_eq (Subtype.ext hh)))
  · rintro ⟨c,τ,p,hp,hr⟩
    let q : Fin n := ⟨c.val,lt_of_le_of_lt hp.1 p.isLt⟩
    have hq : q.castSucc = c := Fin.ext rfl
    let τ' : PermPalPlaced q.castSucc := hq.symm ▸ τ
    have hcast {i j : Fin (n+1)} (e : i=j) (v : PermPalPlaced i) :
        (e ▸ v : PermPalPlaced j).val = v.val := by cases e; rfl
    have ht : τ'.val = τ.val := hcast hq.symm τ
    let x : OpenRight n := ⟨q,τ'⟩
    have hx : x.2.val (openPeak x) = r := by
      have hh := openPeak_spec x
      change RightPeak τ'.val q.castSucc (openPeak x) at hh
      rw [ht,hq] at hh
      have he := rightPeak_unique τ.val c hh hp
      apply Fin.ext
      change (τ'.val (openPeak x)).val = r.val
      rwa [ht,he]
    refine ⟨⟨x,hx⟩,?_⟩
    apply Sigma.ext hq
    have hok {x y : Fin (n+1)} (hxy : x=y) (v : {ρ : PermPalPlaced x //
        ∃ p : Fin n, RightPeak ρ.val x p ∧ (ρ.val p).val = r.val})
        (w : {ρ : PermPalPlaced y //
        ∃ p : Fin n, RightPeak ρ.val y p ∧ (ρ.val p).val = r.val})
        (hv : v.val.val=w.val.val) : HEq v w := by
      cases hxy
      exact heq_of_eq (Subtype.ext (Subtype.ext hv))
    exact hok hq _ _ ht

theorem rootCount_tracked (n : ℕ) :
    Nat.card (PermPalRoot (n+2)) = Nat.card (PermPalRoot (n+1)) +
      ∑ r : Fin (n+1), Nat.card (PermPalRoot (n-r.val)) * Nat.card (Rule9Target r.val) := by
  classical
  rw [permPalRoot_card_split (n+1)]
  have hsum : (∑ c : Fin (n+1), Nat.card (PermPalPlaced c.castSucc)) =
      Nat.card (OpenRight (n+1)) := by rw [Nat.card_sigma]
  rw [hsum,← Nat.card_congr (Equiv.sigmaFiberEquiv
    (fun x : OpenRight (n+1) => x.2.val (openPeak x))),Nat.card_sigma]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [Nat.card_congr (rankFiber r)]
  have hlen : n+1 = (n-r.val)+(r.val+1) := by have := r.isLt; omega
  have he : AtRightRank (n+1) r.val = PeakSlice (n-r.val) r.val :=
    congrArg (fun k => AtRightRank k r.val) hlen
  rw [he,peakSlice_card_fused]

noncomputable def trackedUnweighted : PowerSeries ℤ :=
  PowerSeries.mk fun n => (Nat.card (Rule9Target n) : ℤ)

/-- The exact univariate root equation F = 1 + XF + X²FH, with H the
    unweighted count of the fused class proved equivalent to the residual. -/
theorem permPal_root_equation :
    A001764.permPalTotal = 1 + X*A001764.permPalTotal +
      X^2*(A001764.permPalTotal*trackedUnweighted) := by
  ext d
  obtain _ | _ | n := d
  · simp [A001764.totalSeries,avoider_card_zero,coeff_zero_eq_constantCoeff_apply]
  · rw [map_add,coeff_X_pow_mul']; simp [A001764.totalSeries,avoider_card_zero]
    have h := permPalRoot_card_split 0
    simp at h
    exact_mod_cast (show Nat.card (PermPalRoot 1) = 1 by simpa [avoider_card_zero] using h)
  · rw [map_add,map_add,coeff_one,if_neg (by omega),zero_add,coeff_succ_X_mul,
      show n+1+1 = n+2 by omega,coeff_X_pow_mul,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [A001764.totalSeries, trackedUnweighted, coeff_mk]
    have h := rootCount_tracked n
    rw [← Fin.sum_univ_eq_sum_range]
    have hsum : (∑ i : Fin (n+1), Nat.card (PermPalRoot (n-i.val)) * Nat.card (Rule9Target i.val)) =
        ∑ i : Fin (n+1), Nat.card (PermPalRoot i.val) * Nat.card (Rule9Target (n-i.val)) := by
      apply Fintype.sum_equiv Fin.revPerm
      intro i
      have h1 : (Fin.revPerm i).val = n-i.val := by
        simp only [Fin.revPerm_apply,Fin.val_rev]
        omega
      have h2 : n - (Fin.revPerm i).val = i.val := by rw [h1]; have := i.isLt; omega
      rw [h2,h1]
    rw [hsum] at h
    exact_mod_cast h

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4

def suffixCell (c : ℕ) (left : Prop) [Decidable left] : ℕ :=
  if c = 2 ∧ ¬ left then 3 else c

abbrev splitRight (p : GridPattern) (t : ℕ) : GridPattern :=
  ⟨p.size,p.rank,fun i => suffixCell (p.column i) (i.val < t)⟩

abbrev dropRight {k : ℕ} (r c : Fin (k+1) → ℕ) (peak : Fin (k+1)) : GridPattern :=
  ⟨k, fun i => r (peak.succAbove i), fun i =>
    suffixCell (c (peak.succAbove i)) (i.val < peak.val)⟩

private theorem suffixCell_restore {c : ℕ} (hc : c ≤ 2) (left : Prop) [Decidable left] :
    min (suffixCell c left) 2 = c := by
  unfold suffixCell
  split <;> omega

private theorem cols4_suffix_eq {n : ℕ} {a b c : Fin (n+1)} (hab : a ≤ b) (hbc : b ≤ c)
    (i : Fin n) :
    cols4 a.val b.val c.val i = suffixCell (cols3 a.val b.val i) (i.val < c.val) := by
  have h₁ : a.val ≤ b.val := hab
  have h₂ : b.val ≤ c.val := hbc
  unfold cols4 cols3 suffixCell
  split_ifs <;> omega

private theorem suffixCols_insert {n : ℕ} {a b c : Fin (n+1)} (hbc : b ≤ c)
    (hab : a ≤ b) (i : Fin n) :
    cols3 a.val b.val (c.succAbove i) = cols3 a.val b.val i := by
  have h₁ : a.val ≤ b.val := hab
  have h₂ : b.val ≤ c.val := hbc
  by_cases h : i.val < c.val
  · rw [Fin.succAbove_of_castSucc_lt c i h]
    rfl
  · rw [Fin.succAbove_of_le_castSucc c i (Nat.le_of_not_gt h)]
    simp only [cols3,Fin.val_succ]
    split_ifs <;> omega

private theorem suffixCols_at {n : ℕ} {a b c : Fin (n+1)}
    (hab : a ≤ b) (hbc : b ≤ c) : cols3 (n := n+1) a.val b.val c = 2 := by
  have h₁ : a.val ≤ b.val := hab
  have h₂ : b.val ≤ c.val := hbc
  simp [cols3,not_lt_of_ge (h₁.trans h₂),not_lt_of_ge h₂]

private theorem prefixBefore {n k : ℕ} (g : Fin k → Fin n) (hg : StrictMono g)
    (c : ℕ) : ∃ t ≤ k, ∀ i, (g i).val < c ↔ i.val < t := by
  classical
  let P := fun t : ℕ => k ≤ t ∨ ∃ i : Fin k, i.val = t ∧ c ≤ (g i).val
  have h : ∃ t, P t := ⟨k,Or.inl le_rfl⟩
  have hm : Nat.find h ≤ k := Nat.find_min' h (Or.inl le_rfl)
  refine ⟨_,hm,fun i => ⟨?_,?_⟩⟩
  · intro hi
    by_contra! hn
    obtain hb | ⟨j,hj,hj'⟩ := Nat.find_spec h
    · omega
    · have hji : j ≤ i := by change j.val ≤ i.val; omega
      exact (Nat.not_lt_of_ge (hj'.trans (hg.monotone hji))) hi
  · intro hi
    by_contra! hn
    exact (Nat.find_min h hi) (Or.inr ⟨i,rfl,hn⟩)

private theorem suffixCell_infer {c : ℕ} (hc : c ≤ 2) (l r : Prop)
    [Decidable l] [Decidable r] :
    suffixCell c l = suffixCell c r → (c = 2 → (l ↔ r)) := by
  intro h h₂
  subst c
  by_cases hl : l <;> by_cases hr : r <;> simp_all [suffixCell]

/-- When the maximum is in the third column, the projected forbidden
    occurrences are precisely the unmarked and marked lifts below. -/
theorem suffixPlacement_occurs_iff {n k : ℕ} {a b c : Fin (n+1)} (hab : a ≤ b)
    (hbc : b ≤ c) (σ : Equiv.Perm (Fin n)) (r col : Fin (k+1) → ℕ)
    (peak : Fin (k+1)) (hpeak : ∀ i ≠ peak, r i < r peak)
    (hm : Monotone col) (hcol : ∀ i, col i ≤ 2) :
    gridOccurs (placeMaximum c σ) (cols3 a.val b.val) ⟨k+1,r,col⟩ ↔
      (∃ t ≤ k+1, gridOccurs σ (cols4 a.val b.val c.val)
        (splitRight ⟨k+1,r,col⟩ t)) ∨
      (col peak = 2 ∧ gridOccurs σ (cols4 a.val b.val c.val) (dropRight r col peak)) := by
  constructor
  · rintro ⟨g,hg,hr,hgrid⟩
    by_cases he : g peak = c
    · right
      refine ⟨?_,?_⟩
      · have hh := hgrid peak
        change cols3 a.val b.val (g peak) = col peak at hh
        rw [he,suffixCols_at hab hbc] at hh
        exact hh.symm
      have hne (i : Fin k) : g (peak.succAbove i) ≠ c := by
        rw [← he]
        exact fun h => peak.succAbove_ne i (hg.injective h)
      let f (i : Fin k) : Fin n := (finSuccAboveEquiv c).symm ⟨g (peak.succAbove i),hne i⟩
      have hf (i : Fin k) : c.succAbove (f i) = g (peak.succAbove i) :=
        congrArg Subtype.val ((finSuccAboveEquiv c).apply_symm_apply ⟨_,hne i⟩)
      refine ⟨f,?_,?_,?_⟩
      · intro i j hij
        apply (Fin.succAbove_lt_succAbove_iff).mp
        change c.succAbove (f i) < c.succAbove (f j)
        rw [hf,hf]
        exact hg ((Fin.strictMono_succAbove _) hij)
      · intro i j
        have hh := hr (peak.succAbove i) (peak.succAbove j)
        rw [← hf i,← hf j,placeMaximum_away,placeMaximum_away] at hh
        exact (Fin.castSucc_lt_castSucc_iff).symm.trans hh
      · intro i
        have hc := hgrid (peak.succAbove i)
        change cols3 a.val b.val (g (peak.succAbove i)) = col (peak.succAbove i) at hc
        rw [← hf,suffixCols_insert hbc hab] at hc
        have hl : (f i).val < c.val ↔ i.val < peak.val := by
          change (f i).castSucc < c ↔ i.castSucc < peak
          rw [← Fin.succAbove_lt_iff_castSucc_lt,← Fin.succAbove_lt_iff_castSucc_lt,hf,← he]
          exact hg.lt_iff_lt
        change cols4 a.val b.val c.val (f i) = suffixCell (col (peak.succAbove i)) (i.val < peak.val)
        rw [cols4_suffix_eq hab hbc,hc]
        simp [suffixCell,hl]
    · left
      have hne (i : Fin (k+1)) : g i ≠ c := by
        intro he'
        have hi : i ≠ peak := fun hp => he (hp ▸ he')
        have hh := (hr i peak).mpr (hpeak i hi)
        rw [he',placeMaximum_at] at hh
        exact (not_lt_of_ge (Fin.le_last _)) hh
      let f (i : Fin (k+1)) : Fin n := (finSuccAboveEquiv c).symm ⟨g i,hne i⟩
      have hf (i : Fin (k+1)) : c.succAbove (f i) = g i :=
        congrArg Subtype.val ((finSuccAboveEquiv c).apply_symm_apply ⟨_,hne i⟩)
      have hm' : StrictMono f := by
        intro i j hij
        apply (Fin.succAbove_lt_succAbove_iff).mp
        rw [hf,hf]
        exact hg hij
      obtain ⟨t,ht,hl⟩ := prefixBefore f hm' c.val
      refine ⟨t,ht,f,hm',?_,?_⟩
      · intro i j
        have hh := hr i j
        rw [← hf i,← hf j,placeMaximum_away,placeMaximum_away] at hh
        exact (Fin.castSucc_lt_castSucc_iff).symm.trans hh
      · intro i
        have hc := hgrid i
        change cols3 a.val b.val (g i) = col i at hc
        rw [← hf,suffixCols_insert hbc hab] at hc
        change cols4 a.val b.val c.val (f i) = suffixCell (col i) (i.val < t)
        rw [cols4_suffix_eq hab hbc,hc]
        simp [suffixCell,hl]
  · rintro (⟨t,ht,f,hf,hr,hg⟩ | ⟨hcPeak,f,hf,hr,hg⟩)
    · refine ⟨c.succAbove ∘ f,(Fin.strictMono_succAbove c).comp hf,?_,?_⟩
      · intro i j
        change placeMaximum c σ (c.succAbove (f i)) <
          placeMaximum c σ (c.succAbove (f j)) ↔ _
        simpa only [placeMaximum_away,Fin.castSucc_lt_castSucc_iff,splitRight] using hr i j
      · intro i
        change cols3 a.val b.val (c.succAbove (f i)) = col i
        rw [suffixCols_insert hbc hab]
        have hh := hg i
        change cols4 a.val b.val c.val (f i) = suffixCell (col i) (i.val < t) at hh
        rw [cols4_suffix_eq hab hbc] at hh
        have el : cols3 a.val b.val (f i) ≤ 2 := by unfold cols3; split_ifs <;> decide
        simpa only [suffixCell_restore el, suffixCell_restore (hcol i)] using congrArg (min · 2) hh
    · let g : Fin (k+1) → Fin (n+1) := peak.insertNth c (c.succAbove ∘ f)
      have gPeak : g peak = c := by simp [g]
      have gAway (i : Fin k) : g (peak.succAbove i) = c.succAbove (f i) := by simp [g,Function.comp_def]
      have originalCol (i : Fin k) : cols3 a.val b.val (f i) = col (peak.succAbove i) := by
        have hh := hg i
        change cols4 a.val b.val c.val (f i) = suffixCell (col (peak.succAbove i)) (i.val < peak.val) at hh
        rw [cols4_suffix_eq hab hbc] at hh
        have el : cols3 a.val b.val (f i) ≤ 2 := by unfold cols3; split_ifs <;> decide
        simpa only [suffixCell_restore el, suffixCell_restore (hcol _)] using congrArg (min · 2) hh
      have hcut (i : Fin k) : (f i).val < c.val ↔ i.val < peak.val := by
        by_cases h2 : col (peak.succAbove i) = 2
        · have hh := hg i
          change cols4 a.val b.val c.val (f i) = suffixCell (col (peak.succAbove i)) (i.val < peak.val) at hh
          rw [cols4_suffix_eq hab hbc,originalCol] at hh
          exact suffixCell_infer (hcol _) _ _ hh h2
        · have hi : i.castSucc < peak := by
            by_contra! h
            have h' : peak ≤ peak.succAbove i := (Fin.lt_succAbove_iff_le_castSucc _ _).mpr h |>.le
            have hh := hm h'
            rw [hcPeak] at hh
            exact h2 (le_antisymm (hcol _) hh)
          have hh : cols3 a.val b.val (f i) ≠ 2 := fun e => h2 ((originalCol i).symm.trans e)
          have hh' : (f i).val < c.val := by
            by_contra! hn
            have hb' : b.val ≤ c.val := hbc
            have ha' : a.val ≤ b.val := hab
            exact hh (by unfold cols3; split_ifs <;> omega)
          exact iff_of_true hh' hi
      refine ⟨g,?_,?_,?_⟩
      · intro i j hlt
        revert hlt
        refine Fin.succAboveCases peak ?_ (fun a' => ?_) i
        · refine Fin.succAboveCases peak (by simp) (fun b' => ?_) j
          intro hb'
          simp only [gPeak,gAway]
          apply (Fin.lt_succAbove_iff_le_castSucc _ _).mpr
          have hβ : ¬ b'.val < peak.val := fun hh =>
            (not_lt_of_gt hb') ((Fin.succAbove_lt_iff_castSucc_lt _ _).mpr hh)
          exact Nat.le_of_not_gt (fun hh => hβ ((hcut b').mp hh))
        · refine Fin.succAboveCases peak ?_ (fun b' => ?_) j
          · intro ha'
            simp only [gPeak,gAway]
            exact (Fin.succAbove_lt_iff_castSucc_lt _ _).mpr
              ((hcut a').mpr ((Fin.succAbove_lt_iff_castSucc_lt _ _).mp ha'))
          · intro hab'
            simpa only [gAway,Fin.succAbove_lt_succAbove_iff] using
              (hf ((Fin.succAbove_lt_succAbove_iff).mp hab'))
      · intro i j
        change placeMaximum c σ (g i) < placeMaximum c σ (g j) ↔ r i < r j
        refine Fin.succAboveCases peak ?_ (fun a' => ?_) i
        · refine Fin.succAboveCases peak (by simp) (fun b' => ?_) j
          have hb' := hpeak (peak.succAbove b') (peak.succAbove_ne b')
          simp [gPeak,gAway,not_lt_of_gt hb',Fin.le_last]
        · refine Fin.succAboveCases peak (by simp [gPeak,gAway,hpeak _ (peak.succAbove_ne a')]) (fun b' => ?_) j
          simpa only [gAway,placeMaximum_away,Fin.castSucc_lt_castSucc_iff,dropRight] using hr a' b'
      · intro i
        change cols3 a.val b.val (g i) = col i
        refine Fin.succAboveCases peak ?_ (fun a' => ?_) i
        · rw [gPeak,suffixCols_at hab hbc,hcPeak]
        · rw [gAway,suffixCols_insert hbc hab,originalCol]

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4





set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem maximumRight_avoids_iff {n : ℕ} {a b c : Fin (n+1)}
    (hab : a ≤ b) (hbc : b ≤ c) (σ : Equiv.Perm (Fin n)) :
    avoidsGrid (placeMaximum c σ) (cols3 a.val b.val) trackedBasis ↔
      avoidsGrid σ (cols4 a.val b.val c.val) splitBasis := by
  constructor
  · intro hg p hp ho
    simp only [splitBasis,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · apply hg _ (List.get_mem trackedBasis ⟨0, by decide⟩)
      have ge : ⟨3,![0, 2, 1],![0, 0, 0]⟩ = trackedBasis.get ⟨0, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 2) hab hbc σ ![0, 2, 1] ![0, 0, 0] 1 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨1, by decide⟩)
      have ge : ⟨3,![0, 2, 1],![0, 0, 1]⟩ = trackedBasis.get ⟨1, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 2) hab hbc σ ![0, 2, 1] ![0, 0, 1] 1 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨2, by decide⟩)
      have ge : ⟨3,![0, 2, 1],![0, 0, 2]⟩ = trackedBasis.get ⟨2, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 2) hab hbc σ ![0, 2, 1] ![0, 0, 2] 1 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨3,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨2, by decide⟩)
      have ge : ⟨3,![0, 2, 1],![0, 0, 2]⟩ = trackedBasis.get ⟨2, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 2) hab hbc σ ![0, 2, 1] ![0, 0, 2] 1 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨5, by decide⟩)
      have ge : ⟨4,![0, 2, 1, 3],![0, 1, 1, 2]⟩ = trackedBasis.get ⟨5, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 1, 3] ![0, 1, 1, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      right; refine ⟨by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨3, by decide⟩)
      have ge : ⟨3,![0, 2, 1],![0, 1, 2]⟩ = trackedBasis.get ⟨3, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 2) hab hbc σ ![0, 2, 1] ![0, 1, 2] 1 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨3,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨3, by decide⟩)
      have ge : ⟨3,![0, 2, 1],![0, 1, 2]⟩ = trackedBasis.get ⟨3, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 2) hab hbc σ ![0, 2, 1] ![0, 1, 2] 1 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨8, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![0, 2, 2, 2]⟩ = trackedBasis.get ⟨8, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 3, 1] ![0, 2, 2, 2] 2 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      right; refine ⟨by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨6, by decide⟩)
      have ge : ⟨4,![0, 2, 1, 3],![1, 1, 1, 2]⟩ = trackedBasis.get ⟨6, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 1, 3] ![1, 1, 1, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      right; refine ⟨by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨4, by decide⟩)
      have ge : ⟨3,![0, 2, 1],![1, 1, 2]⟩ = trackedBasis.get ⟨4, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 2) hab hbc σ ![0, 2, 1] ![1, 1, 2] 1 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨3,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨4, by decide⟩)
      have ge : ⟨3,![0, 2, 1],![1, 1, 2]⟩ = trackedBasis.get ⟨4, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 2) hab hbc σ ![0, 2, 1] ![1, 1, 2] 1 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨10, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![1, 2, 2, 2]⟩ = trackedBasis.get ⟨10, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 3, 1] ![1, 2, 2, 2] 2 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      right; refine ⟨by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨11, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![2, 2, 2, 2]⟩ = trackedBasis.get ⟨11, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 3, 1] ![2, 2, 2, 2] 2 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      right; refine ⟨by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨13, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![0, 2, 2, 2, 2]⟩ = trackedBasis.get ⟨13, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 4) hab hbc σ ![0, 2, 1, 4, 3] ![0, 2, 2, 2, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      right; refine ⟨by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨15, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![1, 2, 2, 2, 2]⟩ = trackedBasis.get ⟨15, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 4) hab hbc σ ![0, 2, 1, 4, 3] ![1, 2, 2, 2, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      right; refine ⟨by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨16, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![2, 2, 2, 2, 2]⟩ = trackedBasis.get ⟨16, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 4) hab hbc σ ![0, 2, 1, 4, 3] ![2, 2, 2, 2, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      right; refine ⟨by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨8, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![0, 2, 2, 2]⟩ = trackedBasis.get ⟨8, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 3, 1] ![0, 2, 2, 2] 2 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨4,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨8, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![0, 2, 2, 2]⟩ = trackedBasis.get ⟨8, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 3, 1] ![0, 2, 2, 2] 2 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨10, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![1, 2, 2, 2]⟩ = trackedBasis.get ⟨10, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 3, 1] ![1, 2, 2, 2] 2 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨4,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨10, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![1, 2, 2, 2]⟩ = trackedBasis.get ⟨10, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 3, 1] ![1, 2, 2, 2] 2 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨11, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![2, 2, 2, 2]⟩ = trackedBasis.get ⟨11, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 3, 1] ![2, 2, 2, 2] 2 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨4,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨11, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![2, 2, 2, 2]⟩ = trackedBasis.get ⟨11, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 3, 1] ![2, 2, 2, 2] 2 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨1,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨11, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![2, 2, 2, 2]⟩ = trackedBasis.get ⟨11, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 3, 1] ![2, 2, 2, 2] 2 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨13, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![0, 2, 2, 2, 2]⟩ = trackedBasis.get ⟨13, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 4) hab hbc σ ![0, 2, 1, 4, 3] ![0, 2, 2, 2, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨5,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨13, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![0, 2, 2, 2, 2]⟩ = trackedBasis.get ⟨13, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 4) hab hbc σ ![0, 2, 1, 4, 3] ![0, 2, 2, 2, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨15, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![1, 2, 2, 2, 2]⟩ = trackedBasis.get ⟨15, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 4) hab hbc σ ![0, 2, 1, 4, 3] ![1, 2, 2, 2, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨5,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨15, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![1, 2, 2, 2, 2]⟩ = trackedBasis.get ⟨15, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 4) hab hbc σ ![0, 2, 1, 4, 3] ![1, 2, 2, 2, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨16, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![2, 2, 2, 2, 2]⟩ = trackedBasis.get ⟨16, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 4) hab hbc σ ![0, 2, 1, 4, 3] ![2, 2, 2, 2, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨5,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨16, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![2, 2, 2, 2, 2]⟩ = trackedBasis.get ⟨16, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 4) hab hbc σ ![0, 2, 1, 4, 3] ![2, 2, 2, 2, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨1,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨16, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![2, 2, 2, 2, 2]⟩ = trackedBasis.get ⟨16, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (suffixPlacement_occurs_iff (k := 4) hab hbc σ ![0, 2, 1, 4, 3] ![2, 2, 2, 2, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩
  · intro hs p hp ho
    simp only [trackedBasis,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · change gridOccurs _ _ (trackedBasis.get ⟨0, by decide⟩) at ho
      have ge : ⟨3,![0, 2, 1],![0, 0, 0]⟩ = trackedBasis.get ⟨0, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (suffixPlacement_occurs_iff (k := 2) hab hbc σ ![0, 2, 1] ![0, 0, 0] 1 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem splitBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![0, 0, 0] (1 : Fin 3) ≠ 2) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨1, by decide⟩) at ho
      have ge : ⟨3,![0, 2, 1],![0, 0, 1]⟩ = trackedBasis.get ⟨1, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (suffixPlacement_occurs_iff (k := 2) hab hbc σ ![0, 2, 1] ![0, 0, 1] 1 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem splitBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![0, 0, 1] (1 : Fin 3) ≠ 2) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨2, by decide⟩) at ho
      have ge : ⟨3,![0, 2, 1],![0, 0, 2]⟩ = trackedBasis.get ⟨2, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (suffixPlacement_occurs_iff (k := 2) hab hbc σ ![0, 2, 1] ![0, 0, 2] 1 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem splitBasis ⟨3, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨3, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨3, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨2, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![0, 0, 2] (1 : Fin 3) ≠ 2) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨3, by decide⟩) at ho
      have ge : ⟨3,![0, 2, 1],![0, 1, 2]⟩ = trackedBasis.get ⟨3, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (suffixPlacement_occurs_iff (k := 2) hab hbc σ ![0, 2, 1] ![0, 1, 2] 1 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem splitBasis ⟨6, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨6, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨6, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨5, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![0, 1, 2] (1 : Fin 3) ≠ 2) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨4, by decide⟩) at ho
      have ge : ⟨3,![0, 2, 1],![1, 1, 2]⟩ = trackedBasis.get ⟨4, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (suffixPlacement_occurs_iff (k := 2) hab hbc σ ![0, 2, 1] ![1, 1, 2] 1 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem splitBasis ⟨10, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨10, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨10, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨9, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![1, 1, 2] (1 : Fin 3) ≠ 2) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨5, by decide⟩) at ho
      have ge : ⟨4,![0, 2, 1, 3],![0, 1, 1, 2]⟩ = trackedBasis.get ⟨5, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 1, 3] ![0, 1, 1, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem splitBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
      · exact hs _ (List.get_mem splitBasis ⟨4, by decide⟩)
          (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
    · change gridOccurs _ _ (trackedBasis.get ⟨6, by decide⟩) at ho
      have ge : ⟨4,![0, 2, 1, 3],![1, 1, 1, 2]⟩ = trackedBasis.get ⟨6, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 1, 3] ![1, 1, 1, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem splitBasis ⟨8, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨8, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨8, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨8, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨8, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
      · exact hs _ (List.get_mem splitBasis ⟨8, by decide⟩)
          (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
    · change gridOccurs _ _ (trackedBasis.get ⟨7, by decide⟩) at ho
      have ge : ⟨4,![0, 2, 3, 1],![0, 1, 1, 1]⟩ = trackedBasis.get ⟨7, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 3, 1] ![0, 1, 1, 1] 2 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem splitBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![0, 1, 1, 1] (2 : Fin 4) ≠ 2) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨8, by decide⟩) at ho
      have ge : ⟨4,![0, 2, 3, 1],![0, 2, 2, 2]⟩ = trackedBasis.get ⟨8, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 3, 1] ![0, 2, 2, 2] 2 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem splitBasis ⟨17, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨17, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨7, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨7, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨16, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
      · exact hs _ (List.get_mem splitBasis ⟨7, by decide⟩)
          (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
    · change gridOccurs _ _ (trackedBasis.get ⟨9, by decide⟩) at ho
      have ge : ⟨4,![0, 2, 3, 1],![1, 1, 1, 1]⟩ = trackedBasis.get ⟨9, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 3, 1] ![1, 1, 1, 1] 2 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem splitBasis ⟨8, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨8, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨8, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨8, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨8, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![1, 1, 1, 1] (2 : Fin 4) ≠ 2) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨10, by decide⟩) at ho
      have ge : ⟨4,![0, 2, 3, 1],![1, 2, 2, 2]⟩ = trackedBasis.get ⟨10, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 3, 1] ![1, 2, 2, 2] 2 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem splitBasis ⟨19, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨19, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨11, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨11, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨18, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
      · exact hs _ (List.get_mem splitBasis ⟨11, by decide⟩)
          (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
    · change gridOccurs _ _ (trackedBasis.get ⟨11, by decide⟩) at ho
      have ge : ⟨4,![0, 2, 3, 1],![2, 2, 2, 2]⟩ = trackedBasis.get ⟨11, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (suffixPlacement_occurs_iff (k := 3) hab hbc σ ![0, 2, 3, 1] ![2, 2, 2, 2] 2 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem splitBasis ⟨22, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨21, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨12, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨12, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨20, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
      · exact hs _ (List.get_mem splitBasis ⟨12, by decide⟩)
          (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
    · change gridOccurs _ _ (trackedBasis.get ⟨12, by decide⟩) at ho
      have ge : ⟨5,![0, 2, 1, 4, 3],![0, 1, 1, 1, 1]⟩ = trackedBasis.get ⟨12, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (suffixPlacement_occurs_iff (k := 4) hab hbc σ ![0, 2, 1, 4, 3] ![0, 1, 1, 1, 1] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem splitBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![0, 1, 1, 1, 1] (3 : Fin 5) ≠ 2) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨13, by decide⟩) at ho
      have ge : ⟨5,![0, 2, 1, 4, 3],![0, 2, 2, 2, 2]⟩ = trackedBasis.get ⟨13, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (suffixPlacement_occurs_iff (k := 4) hab hbc σ ![0, 2, 1, 4, 3] ![0, 2, 2, 2, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem splitBasis ⟨24, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨24, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨7, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨13, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨7, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨23, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
      · exact hs _ (List.get_mem splitBasis ⟨13, by decide⟩)
          (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
    · change gridOccurs _ _ (trackedBasis.get ⟨14, by decide⟩) at ho
      have ge : ⟨5,![0, 2, 1, 4, 3],![1, 1, 1, 1, 1]⟩ = trackedBasis.get ⟨14, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (suffixPlacement_occurs_iff (k := 4) hab hbc σ ![0, 2, 1, 4, 3] ![1, 1, 1, 1, 1] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem splitBasis ⟨8, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨8, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨8, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨8, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨8, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨8, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![1, 1, 1, 1, 1] (3 : Fin 5) ≠ 2) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨15, by decide⟩) at ho
      have ge : ⟨5,![0, 2, 1, 4, 3],![1, 2, 2, 2, 2]⟩ = trackedBasis.get ⟨15, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (suffixPlacement_occurs_iff (k := 4) hab hbc σ ![0, 2, 1, 4, 3] ![1, 2, 2, 2, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem splitBasis ⟨26, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨26, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨11, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨14, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨11, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨25, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
      · exact hs _ (List.get_mem splitBasis ⟨14, by decide⟩)
          (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
    · change gridOccurs _ _ (trackedBasis.get ⟨16, by decide⟩) at ho
      have ge : ⟨5,![0, 2, 1, 4, 3],![2, 2, 2, 2, 2]⟩ = trackedBasis.get ⟨16, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (suffixPlacement_occurs_iff (k := 4) hab hbc σ ![0, 2, 1, 4, 3] ![2, 2, 2, 2, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel) (by decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem splitBasis ⟨29, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨28, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨12, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨15, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨12, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem splitBasis ⟨27, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
      · exact hs _ (List.get_mem splitBasis ⟨15, by decide⟩)
          (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4 PowerSeries

/-- The branch F20 of the weighted class: its maximum belongs to the
    rightmost of the three columns. -/
abbrev RightMaximum (n : ℕ) :=
  {q : Rule9Target (n+1) // q.val.second ≤ (q.val.1.symm (Fin.last n)).val}

noncomputable instance (n : ℕ) : Fintype (RightMaximum n) := Fintype.ofFinite _

private def insertRightMaximum {n : ℕ} (s : Rule9Source n) : RightMaximum n := by
  rcases s with ⟨⟨σ,⟨a,b⟩,hab⟩,d,hs⟩
  have hda : d.val ≤ a.val := Nat.le_of_lt_succ (show d.val < a.val+1 from d.isLt)
  let c : Fin (n+1) := ⟨d.val,lt_of_le_of_lt hda a.isLt⟩
  have hca : c ≤ a := hda
  have h : avoidsGrid (placeMaximum b σ) (cols3 c.val a.val) trackedBasis :=
    (maximumRight_avoids_iff hca hab σ).mpr hs
  refine ⟨⟨⟨placeMaximum b σ,⟨⟨c.castSucc,a.castSucc⟩,hca⟩⟩,h⟩,?_⟩
  change a.val ≤ ((placeMaximum b σ).symm (Fin.last n)).val
  rwa [inverse_placeMaximum_peak]

/-- Deleting the maximum in the rightmost-column branch yields exactly
    the pre-fusion class. The two old cuts and the maximum position are
    the three cuts of the result. -/
noncomputable def rightMaximumEquiv (n : ℕ) : Rule9Source n ≃ RightMaximum n := by
  refine Equiv.ofBijective insertRightMaximum ?_
  constructor
  · rintro ⟨⟨σ,⟨a,b⟩,hab⟩,d,hs⟩ ⟨⟨σ',⟨a',b'⟩,hab'⟩,d',hs'⟩ he
    have hσ : placeMaximum b σ = placeMaximum b' σ' :=
      congrArg (fun z : RightMaximum n => z.val.val.1) he
    have ha : a.val=a'.val :=
      congrArg (fun z : RightMaximum n => z.val.val.second) he
    have hd : d.val=d'.val :=
      congrArg (fun z : RightMaximum n => z.val.val.first) he
    have hbb' : b=b' := by
      simpa only [inverse_placeMaximum_peak] using
        congrArg (fun p : Equiv.Perm (Fin (n+1)) => p.symm (Fin.last n)) hσ
    have haa' : a=a' := Fin.ext ha
    subst b'
    subst a'
    have hσ' := placeMaximum_injective _ hσ
    subst σ'
    have hdd' : d=d' := Fin.ext hd
    subst d'
    rfl
  · rintro ⟨⟨⟨σ,⟨left,right⟩,hcut⟩,ha⟩,hp⟩
    let b := σ.symm (Fin.last n)
    let a : Fin (n+1) := ⟨right.val,lt_of_le_of_lt hp b.isLt⟩
    have hla : left.val ≤ a.val := hcut
    let d : Fin (a.val+1) := ⟨left.val, Nat.lt_succ_of_le hla⟩
    let c : Fin (n+1) := ⟨left.val, lt_of_le_of_lt hla a.isLt⟩
    let π := deleteMaximum σ
    have hσ : placeMaximum b π = σ := placeMaximum_deleteMaximum _
    have hca : c ≤ a := hcut
    have hab : a ≤ b := hp
    have hh : avoidsGrid π (cols4 d.val a.val b.val) splitBasis := by
      apply (maximumRight_avoids_iff hca hab π).mp
      rw [hσ]
      exact ha
    refine ⟨⟨⟨π,⟨⟨a,b⟩,hab⟩⟩,⟨d,hh⟩⟩,?_⟩
    exact Subtype.ext (Subtype.ext (Prod.ext hσ (Subtype.ext (Prod.ext (Fin.ext rfl) (Fin.ext rfl)))))

theorem rightMaximum_tracker {n : ℕ} (s : Rule9Source n) :
    ((rightMaximumEquiv n s).val.val.first) = s.2.val.val := rfl

/-- Exact right-maximum contribution to the size n+1 weighted recurrence. -/
theorem rightMaximum_weighted_sum {R : Type*} [CommRing R] (k : R) (n : ℕ) :
    (k - 1) * (∑ s : RightMaximum n, k^s.val.val.first) =
      k * (∑ q : Rule9Target n, k^q.val.first) - (Nat.card (Rule9Target n) : R) := by
  classical
  rw [← Fintype.sum_equiv (rightMaximumEquiv n)
    (fun s => k^s.2.val.val) (fun t => k^t.val.val.first) (fun s => by rw [rightMaximum_tracker])]
  exact rule9_weighted_sum k n

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4 OMA.S_oeis_a001764

theorem skewValHigh {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (i : Fin m) : (skewSum σ τ (Fin.castAdd n i)).val = n+(σ i).val := by
  unfold skewSum
  simp only [Equiv.trans_apply,directSum_left,Fin.revPerm_apply,Fin.val_rev,Fin.val_castAdd]
  have := (σ i).isLt
  omega

theorem skewValLow {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (i : Fin n) : (skewSum σ τ (Fin.natAdd m i)).val = (τ i).val := by
  unfold skewSum
  simp only [Equiv.trans_apply,directSum_right,Fin.revPerm_apply,Fin.val_rev,Fin.val_natAdd]
  have := (τ i).isLt
  omega

theorem gridOccurs_skew {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (f : Fin (m+n) → ℕ) (p : GridPattern) (hn : 0 < p.size)
    (he : p.rank ⟨0,hn⟩ < p.rank ⟨p.size-1,by omega⟩) :
    gridOccurs (skewSum σ τ) f p ↔
      gridOccurs σ (f ∘ Fin.castAdd n) p ∨ gridOccurs τ (f ∘ Fin.natAdd m) p := by
  constructor
  · rintro ⟨g,hg,hr,hf⟩
    let a : Fin p.size := ⟨0,hn⟩
    let b : Fin p.size := ⟨p.size-1,by omega⟩
    have hfirst (i : Fin p.size) : a ≤ i := Nat.zero_le _
    have hlast (i : Fin p.size) : i ≤ b := by change i.val ≤ p.size-1; have := i.isLt; omega
    by_cases h : (g a).val < m
    · have hb : (g b).val < m := by
        by_contra! hbad
        let i : Fin m := ⟨(g a).val,h⟩
        let j : Fin n := ⟨(g b).val-m,by have := (g b).isLt; omega⟩
        have ei : Fin.castAdd n i = g a := Fin.ext rfl
        have ej : Fin.natAdd m j = g b := Fin.ext (by simp [j]; omega)
        have hlt := (hr a b).mpr he
        change (skewSum σ τ (g a)).val < (skewSum σ τ (g b)).val at hlt
        rw [← ei,← ej,skewValHigh,skewValLow] at hlt
        have := (τ j).isLt
        omega
      let l (i : Fin p.size) : Fin m := ⟨(g i).val,lt_of_le_of_lt (hg.monotone (hlast i)) hb⟩
      have el (i : Fin p.size) : Fin.castAdd n (l i) = g i := Fin.ext rfl
      left
      refine ⟨l,fun i j hij => hg hij,?_,fun i => ?_⟩
      · intro i j
        have hlt := hr i j
        change (skewSum σ τ (g i)).val < (skewSum σ τ (g j)).val ↔ _ at hlt
        rw [← el,← el,skewValHigh,skewValHigh,Nat.add_lt_add_iff_left] at hlt
        exact hlt
      · change f (Fin.castAdd n (l i)) = _
        rw [el]
        exact hf i
    · have ha (i : Fin p.size) : m ≤ (g i).val :=
        (Nat.le_of_not_gt h).trans (hg.monotone (hfirst i))
      let r (i : Fin p.size) : Fin n := ⟨(g i).val-m,by have := (g i).isLt; omega⟩
      have er (i : Fin p.size) : Fin.natAdd m (r i) = g i := Fin.ext (by have := ha i; simp [r]; omega)
      right
      refine ⟨r,?_,?_,fun i => ?_⟩
      · intro i j hij
        have hlt := hg hij
        rw [← er,← er] at hlt
        exact Nat.lt_of_add_lt_add_left hlt
      · intro i j
        have hlt := hr i j
        change (skewSum σ τ (g i)).val < (skewSum σ τ (g j)).val ↔ _ at hlt
        rw [← er,← er,skewValLow,skewValLow] at hlt
        exact hlt
      · change f (Fin.natAdd m (r i)) = _
        rw [er]
        exact hf i
  · rintro (⟨g,hg,hr,hc⟩ | ⟨g,hg,hr,hc⟩)
    · refine ⟨Fin.castAdd n ∘ g,fun i j h => hg h,?_,hc⟩
      intro i j
      change (skewSum σ τ (Fin.castAdd n (g i))).val < (skewSum σ τ (Fin.castAdd n (g j))).val ↔ _
      rw [skewValHigh,skewValHigh,Nat.add_lt_add_iff_left]
      exact hr i j
    · refine ⟨Fin.natAdd m ∘ g,fun i j h => Nat.add_lt_add_left (hg h) m,?_,hc⟩
      intro i j
      change (skewSum σ τ (Fin.natAdd m (g i))).val < (skewSum σ τ (Fin.natAdd m (g j))).val ↔ _
      rw [skewValLow,skewValLow]
      exact hr i j

private theorem trackedEndpoints (p : GridPattern) (hp : p ∈ trackedBasis) :
    ∃ h : 0<p.size, p.rank ⟨0,h⟩ < p.rank ⟨p.size-1,by omega⟩ := by
  simp only [trackedBasis,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ⟨by decide,by decide⟩

theorem trackedAvoids_skew {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (f : Fin (m+n) → ℕ) :
    avoidsGrid (skewSum σ τ) f trackedBasis ↔
      avoidsGrid σ (f ∘ Fin.castAdd n) trackedBasis ∧
      avoidsGrid τ (f ∘ Fin.natAdd m) trackedBasis := by
  constructor
  · intro h
    constructor
    · intro p hp ho
      obtain ⟨hn,he⟩ := trackedEndpoints p hp
      exact h p hp ((gridOccurs_skew σ τ f p hn he).mpr (Or.inl ho))
    · intro p hp ho
      obtain ⟨hn,he⟩ := trackedEndpoints p hp
      exact h p hp ((gridOccurs_skew σ τ f p hn he).mpr (Or.inr ho))
  · rintro ⟨hl,hr⟩ p hp ho
    obtain ⟨hn,he⟩ := trackedEndpoints p hp
    rcases (gridOccurs_skew σ τ f p hn he).mp ho with h | h
    · exact hl p hp h
    · exact hr p hp h

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4 OMA.S_oeis_a001764

private def first132 (j : ℕ) : GridPattern := .ofLists [0,2,1] [0,0,j]

private theorem first132_mem (j : ℕ) (hj : j ≤ 2) : first132 j ∈ trackedBasis := by
  interval_cases j <;> simp [first132,trackedBasis]

private theorem allZero_unique {p : GridPattern} (hp : p ∈ trackedBasis)
    (h : ∀ i, p.column i = 0) : p = first132 0 := by
  simp only [trackedBasis,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · rfl
  · exfalso; have hh := h ⟨2,by decide⟩
    change 1 = 0 at hh
    omega
  · exfalso; have hh := h ⟨2,by decide⟩
    change 2 = 0 at hh
    omega
  · exfalso; have hh := h ⟨2,by decide⟩
    change 2 = 0 at hh
    omega
  · exfalso; have hh := h ⟨2,by decide⟩
    change 2 = 0 at hh
    omega
  · exfalso; have hh := h ⟨3,by decide⟩
    change 2 = 0 at hh
    omega
  · exfalso; have hh := h ⟨3,by decide⟩
    change 2 = 0 at hh
    omega
  · exfalso; have hh := h ⟨3,by decide⟩
    change 1 = 0 at hh
    omega
  · exfalso; have hh := h ⟨3,by decide⟩
    change 2 = 0 at hh
    omega
  · exfalso; have hh := h ⟨3,by decide⟩
    change 1 = 0 at hh
    omega
  · exfalso; have hh := h ⟨3,by decide⟩
    change 2 = 0 at hh
    omega
  · exfalso; have hh := h ⟨3,by decide⟩
    change 2 = 0 at hh
    omega
  · exfalso; have hh := h ⟨4,by decide⟩
    change 1 = 0 at hh
    omega
  · exfalso; have hh := h ⟨4,by decide⟩
    change 2 = 0 at hh
    omega
  · exfalso; have hh := h ⟨4,by decide⟩
    change 1 = 0 at hh
    omega
  · exfalso; have hh := h ⟨4,by decide⟩
    change 2 = 0 at hh
    omega
  · exfalso; have hh := h ⟨4,by decide⟩
    change 2 = 0 at hh
    omega

private theorem first132Grid {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    gridOccurs σ (fun _ => 0) (first132 0) ↔ ¬ Avoids σ ![0,2,1] := by
  have hr : ((first132 0).rank : Fin 3 → ℕ) = ![0,2,1] := by
    funext i
    fin_cases i <;> rfl
  rw [Avoids,not_not]
  constructor
  · rintro ⟨e,h,hr',_⟩
    exact ⟨e,h,fun i j => by have hh := hr' i j; rwa [hr] at hh⟩
  · rintro ⟨e,h,hp⟩
    refine ⟨e,h,?_,?_⟩
    · intro i j
      rw [hr]
      exact hp i j
    · intro i
      fin_cases i <;> rfl

theorem tracked_firstColumn {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    avoidsGrid σ (fun _ => 0) trackedBasis ↔ Avoids σ ![0,2,1] := by
  constructor
  · intro h ho
    exact h _ (first132_mem 0 (by decide)) ((first132Grid σ).mpr (fun havo => havo ho))
  · intro h p hp hocc
    obtain ⟨e,he,hr,hc⟩ := hocc
    have h' : p = first132 0 := allZero_unique hp (fun i => (hc i).symm)
    exact (first132Grid σ).mp (h' ▸ ⟨e,he,hr,hc⟩) h

private theorem appendMax_avoids132 {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Avoids (placeMaximum (Fin.last n) σ) ![0,2,1] ↔ Avoids σ ![0,2,1] := by
  rw [avoid_placeMaximum_iff σ (Fin.last n) _ (1 : Fin 3) (by decide)]
  refine and_iff_left_of_imp ?_
  intro h ⟨f,_,_,hc⟩
  exact (by decide : ¬ (1 : ℕ) < 1) ((hc (1 : Fin 2)).mp (f 1).isLt)

/-- When the maximum of F8 is in column zero, it separates all preceding
    positions from all following positions by a skew cut. -/
theorem leftMax_value_separation {n : ℕ} (q : Rule9Target (n+1)) {i j : Fin (n+1)}
    (left : i < q.val.1.symm (Fin.last n)) (right : q.val.1.symm (Fin.last n) < j)
    (first : (q.val.1.symm (Fin.last n)).val < q.val.first) : q.val.1 j < q.val.1 i := by
  let σ := q.val.1
  let peak := σ.symm (Fin.last n)
  have hmax : σ peak = Fin.last n := σ.apply_symm_apply _
  have hi : i < peak := left
  have hj : peak < j := right
  have hcol : cols3 q.val.first q.val.second i = 0 := by
    have hi' : i.val < peak.val := hi
    simp [cols3,hi'.trans first]
  have hcp : cols3 q.val.first q.val.second peak = 0 := by
    have hp : peak.val < q.val.first := first
    exact if_pos hp
  by_contra! h
  have hj' : σ i < σ j := lt_of_le_of_ne h (fun he => (ne_of_lt (hi.trans hj)) (σ.injective he))
  have hpj : σ j < σ peak := by
    rw [hmax]
    exact lt_of_le_of_ne (Fin.le_last _) (fun he => (ne_of_gt hj) (σ.injective (he.trans hmax.symm)))
  let k := cols3 q.val.first q.val.second j
  have hk : k ≤ 2 := by dsimp [k]; unfold cols3; split_ifs <;> decide
  apply q.property (first132 k) (first132_mem _ hk)
  refine ⟨![i,peak,j],?_,?_,?_⟩
  · change StrictMono (![i,peak,j] : Fin 3 → Fin (n+1))
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [σ,peak] <;> omega
  · intro a b
    fin_cases a <;> fin_cases b <;> simp_all [first132,GridPattern.ofLists,σ,peak] <;> omega
  · intro a
    fin_cases a <;> simp [first132,GridPattern.ofLists,hcol,hcp,k]

/-- Exact avoidance equivalence for the high Catalan block, the singleton
    maximum and the lower tracked plot in the left-maximum branch. -/
theorem leftMax_product_iff {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (a b : Fin (n+1)) :
    avoidsGrid (skewSum (placeMaximum (Fin.last m) σ) τ)
        (cols3 (m+1+a.val) (m+1+b.val)) trackedBasis ↔
      Avoids σ ![0,2,1] ∧ avoidsGrid τ (cols3 a.val b.val) trackedBasis := by
  have hL : (cols3 (m+1+a.val) (m+1+b.val) : Fin ((m+1)+n) → ℕ) ∘
      Fin.castAdd n = (fun _ : Fin (m+1) => 0) := by
    funext i
    have h : (Fin.castAdd n i).val < m+1+a.val := by change i.val < _; have := i.isLt; omega
    exact if_pos h
  have hR : (cols3 (m+1+a.val) (m+1+b.val) : Fin ((m+1)+n) → ℕ) ∘
      Fin.natAdd (m+1) = cols3 a.val b.val := by
    funext i
    simp [Function.comp_def,cols3,Fin.val_natAdd]
  rw [trackedAvoids_skew, hL,hR,tracked_firstColumn,appendMax_avoids132]

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4 OMA.S_oeis_a001764

def maxPos {k : ℕ} (σ : Equiv.Perm (Fin k)) (h : 0 < k) : Fin k :=
  σ.symm ⟨k-1,by omega⟩

private theorem apply_maxPos {k : ℕ} (σ : Equiv.Perm (Fin k)) (h : 0 < k) :
    (σ (maxPos σ h)).val = k-1 := by simp [maxPos]

/-- The left-maximum branch, stratified by the number of entries before the
    maximum. The combined size is m+1+n and its maximum has index m. -/
abbrev LeftSlice (m n : ℕ) :=
  {q : Rule9Target ((m+1)+n) //
    (maxPos q.val.1 (by omega)).val = m ∧ m < q.val.first}

abbrev CatalanPlot (m : ℕ) := {σ : Equiv.Perm (Fin m) // Avoids σ ![0,2,1]}

private def shiftBoth {m n : ℕ} (f : Cuts n) : Cuts (m+n) :=
  ⟨(shiftCut m f.val.1,shiftCut m f.val.2),Nat.add_le_add_left f.2 m⟩

private def combineLeft {m n : ℕ} (x : CatalanPlot m × Rule9Target n) : LeftSlice m n := by
  rcases x with ⟨σ,⟨⟨τ,c⟩,ht⟩⟩
  let high := placeMaximum (Fin.last m) σ.val
  let all := skewSum high τ
  let out : Rule9Target ((m+1)+n) :=
    ⟨⟨all,shiftBoth (m := m+1) c⟩,(leftMax_product_iff σ.val τ c.val.1 c.val.2).mpr ⟨σ.2,ht⟩⟩
  refine ⟨out,?_,?_⟩
  · have hh : maxPos all (by omega) = Fin.castAdd n (Fin.last m) := by
      apply all.injective
      apply Fin.ext
      rw [apply_maxPos,skewValHigh,placeMaximum_at]
      simp
      omega
    change (maxPos all (by omega)).val = m
    rw [hh]
    rfl
  · change m < m+1+c.val.1.val
    omega

private theorem all_skewCut {m n : ℕ} (σ : Equiv.Perm (Fin (m+n)))
    (h : ∀ i : Fin m, ∀ j : Fin n, σ (Fin.natAdd m j) < σ (Fin.castAdd n i)) :
    SumCut (σ.trans Fin.revPerm) m := by
  intro i hi
  let e : Fin m := ⟨i.val,hi⟩
  let f : Fin n → Fin (σ i).val := fun j => ⟨(σ (Fin.natAdd m j)).val,h e j⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hv := congrArg Fin.val hab
    have hσ : σ (Fin.natAdd m a) = σ (Fin.natAdd m b) := Fin.ext hv
    exact Fin.natAdd_injective n m (σ.injective hσ)
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hc
  change (σ i).rev.val < m
  rw [Fin.val_rev]
  have := (σ i).isLt
  omega

theorem skew_injective {m n : ℕ}
    {σ σ' : Equiv.Perm (Fin m)} {τ τ' : Equiv.Perm (Fin n)}
    (h : skewSum σ τ = skewSum σ' τ') : σ=σ' ∧ τ=τ' := by
  constructor
  · apply Equiv.ext
    intro i
    apply Fin.ext
    have hh := congrArg (fun p : Equiv.Perm (Fin (m+n)) => (p (Fin.castAdd n i)).val) h
    rwa [skewValHigh,skewValHigh,Nat.add_left_cancel_iff] at hh
  · apply Equiv.ext
    intro i
    apply Fin.ext
    have hh := congrArg (fun p : Equiv.Perm (Fin (m+n)) => (p (Fin.natAdd m i)).val) h
    rwa [skewValLow,skewValLow] at hh

/-- Exact size-preserving left-maximum product underlying the Catalan
    contribution X k C(X k) G(k). -/
noncomputable def leftSliceEquiv (m n : ℕ) :
    LeftSlice m n ≃ CatalanPlot m × Rule9Target n := by
  refine (Equiv.ofBijective combineLeft ?_).symm
  constructor
  · rintro ⟨σ,⟨τ,c⟩,ht⟩ ⟨σ',⟨τ',c'⟩,ht'⟩ hh
    have hσ : skewSum (placeMaximum (Fin.last m) σ.val) τ =
        skewSum (placeMaximum (Fin.last m) σ'.val) τ' :=
      congrArg (fun z : LeftSlice m n => z.val.val.1) hh
    have hfirst : m+1+c.val.1.val = m+1+c'.val.1.val :=
      congrArg (fun z : LeftSlice m n => z.val.val.first) hh
    have hsecond : m+1+c.val.2.val = m+1+c'.val.2.val :=
      congrArg (fun z : LeftSlice m n => z.val.val.second) hh
    obtain ⟨hs,ht⟩ := skew_injective hσ
    have hc : c=c' := Subtype.ext (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
    exact Prod.ext (Subtype.ext (placeMaximum_injective _ hs)) (Subtype.ext (Prod.ext ht hc))
  · rintro ⟨⟨⟨all,c⟩,ha⟩,⟨hp,hc⟩⟩
    let q : Rule9Target ((m+1)+n) := ⟨⟨all,c⟩,ha⟩
    let peak := maxPos all (by omega)
    have he : peak.val = m := hp
    have hc' : m < c.val.1.val := hc
    have hcut : SumCut (all.trans Fin.revPerm) (m+1) := by
      apply all_skewCut
      intro i j
      by_cases hie : i.val=m
      · have hiEq : (Fin.castAdd n i) = peak := Fin.ext (by change i.val = peak.val; omega)
        rw [hiEq]
        change (all (Fin.natAdd (m+1) j)).val < (all peak).val
        rw [apply_maxPos]
        have hEq : Fin.natAdd (m+1) j ≠ peak := by
          intro hh
          have hv := congrArg Fin.val hh
          change m+1+j.val = peak.val at hv
          omega
        have hen : all (Fin.natAdd (m+1) j) ≠ all peak := fun hh => hEq (all.injective hh)
        have := (all (Fin.natAdd (m+1) j)).isLt
        have hne : (all (Fin.natAdd (m+1) j)).val ≠ (m+1)+n-1 :=
          fun hx => hen (Fin.ext (hx.trans (apply_maxPos all (by omega)).symm))
        omega
      · let k := m+n
        have elen : k+1 = (m+1)+n := by dsimp [k]; omega
        -- The positivity of the ambient size only fixes a definitional cast for the maximum.
        have sep {N : ℕ} (z : Rule9Target N) (hN : 0 < N) {a b : Fin N}
            (h1 : a < maxPos z.val.1 hN) (h2 : maxPos z.val.1 hN < b)
            (h3 : (maxPos z.val.1 hN).val < z.val.first) : z.val.1 b < z.val.1 a := by
          cases N with
          | zero => omega
          | succ N => exact leftMax_value_separation z h1 h2 h3
        apply sep q (by omega)
        · change i.val < peak.val
          have hi := i.isLt
          omega
        · change peak.val < m+1+j.val
          omega
        · change peak.val < c.val.1.val
          omega
    let high := (leftBlock hcut).trans Fin.revPerm
    let low := (rightBlock hcut).trans Fin.revPerm
    have glue : skewSum high low = all := skewSplit_of_complementCut hcut
    have hmLast : high (Fin.last m) = Fin.last m := by
      have hj : (Fin.castAdd n (Fin.last m)) = peak := Fin.ext (by change m=peak.val; omega)
      have hh := skewValHigh high low (Fin.last m)
      rw [glue,hj,apply_maxPos] at hh
      apply Fin.ext
      change (high (Fin.last m)).val = m
      omega
    have pos : high.symm (Fin.last m) = Fin.last m := by
      apply high.injective
      rw [Equiv.apply_symm_apply,hmLast]
    let hs := deleteMaximum high
    have heq : placeMaximum (Fin.last m) hs = high := by
      have h := placeMaximum_deleteMaximum high
      rwa [pos] at h
    let ca : Fin (n+1) := ⟨c.val.1.val-(m+1),by have := c.val.1.isLt; omega⟩
    let cb : Fin (n+1) := ⟨c.val.2.val-(m+1),by have := c.val.2.isLt; omega⟩
    have hcc : c.val.1.val ≤ c.val.2.val := c.2
    let cuts : Cuts n := ⟨(ca,cb),Nat.sub_le_sub_right hcc _⟩
    have hcEq : shiftBoth (m := m+1) cuts = c := by
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      · change m+1+(c.val.1.val-(m+1)) = c.val.1.val
        omega
      · change m+1+(c.val.2.val-(m+1)) = c.val.2.val
        omega
    have hx : Avoids hs ![0,2,1] ∧ avoidsGrid low (cols3 ca.val cb.val) trackedBasis := by
      apply (leftMax_product_iff hs low ca cb).mp
      rw [heq,glue]
      have hl : m+1+ca.val = c.val.1.val := congrArg (fun z : Cuts ((m+1)+n) => z.val.1.val) hcEq
      have hr : m+1+cb.val = c.val.2.val := congrArg (fun z : Cuts ((m+1)+n) => z.val.2.val) hcEq
      rw [hl,hr]
      exact ha
    refine ⟨⟨⟨hs,hx.1⟩,⟨⟨low,cuts⟩,hx.2⟩⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change skewSum (placeMaximum (Fin.last m) hs) low = all
      rw [heq,glue]
    · exact hcEq

/-- The marked maximum and every point in the detached Catalan block
    are counted by the first-column tracker. -/
theorem leftSlice_tracker {m n : ℕ} (x : CatalanPlot m × Rule9Target n) :
    ((leftSliceEquiv m n).symm x).val.val.first = m+1+x.2.val.first := by
  rcases x with ⟨σ,⟨τ,c⟩,ht⟩
  rfl

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4

def refineColumn (j col : ℕ) (left : Prop) [Decidable left] : ℕ :=
  if col < j ∨ (col = j ∧ left) then col else col+1

def coalesceColumn (j col : ℕ) : ℕ := if col ≤ j then col else col-1

theorem refine_restore (j col : ℕ) (left : Prop) [Decidable left] :
    coalesceColumn j (refineColumn j col left) = col := by
  unfold coalesceColumn refineColumn
  split_ifs <;> omega

theorem refine_at_split (j : ℕ) (l r : Prop) [Decidable l] [Decidable r] :
    refineColumn j j l = refineColumn j j r → (l ↔ r) := by
  intro h
  by_cases hl : l <;> by_cases hr : r <;> simp_all [refineColumn]

abbrev splitAtColumn (j : ℕ) (p : GridPattern) (t : ℕ) : GridPattern :=
  ⟨p.size,p.rank,fun i => refineColumn j (p.column i) (i.val < t)⟩

abbrev dropAtColumn {k : ℕ} (j : ℕ) (r c : Fin (k+1) → ℕ) (peak : Fin (k+1)) :
    GridPattern :=
  ⟨k,fun i => r (peak.succAbove i),fun i =>
    refineColumn j (c (peak.succAbove i)) (i.val < peak.val)⟩

/-- Inserting a maximum in any column and then projecting its forbidden
    occurrences gives the split-column and marked-column lifts. -/
theorem placeColumn_occurs_iff {n k : ℕ} (c : Fin (n+1)) (pivot : ℕ)
    (smallCol splitCol : Fin n → ℕ) (largeCol : Fin (n+1) → ℕ)
    (atMark : largeCol c = pivot)
    (keepCol : ∀ i, largeCol (c.succAbove i) = smallCol i)
    (splitsCol : ∀ i, splitCol i = refineColumn pivot (smallCol i) (i.val < c.val))
    (beforeSplit : ∀ i, smallCol i < pivot → i.val < c.val)
    (afterSplit : ∀ i, pivot < smallCol i → c.val ≤ i.val)
    (σ : Equiv.Perm (Fin n)) (r col : Fin (k+1) → ℕ)
    (peak : Fin (k+1)) (hpeak : ∀ i ≠ peak, r i < r peak)
    (hm : Monotone col) :
    gridOccurs (placeMaximum c σ) largeCol ⟨k+1,r,col⟩ ↔
      (∃ t ≤ k+1, gridOccurs σ splitCol (splitAtColumn pivot ⟨k+1,r,col⟩ t)) ∨
      (col peak = pivot ∧ gridOccurs σ splitCol (dropAtColumn pivot r col peak)) := by
  constructor
  · rintro ⟨g,hg,hr,hgrid⟩
    by_cases he : g peak = c
    · right
      refine ⟨?_,?_⟩
      · have hh := hgrid peak
        change largeCol (g peak) = col peak at hh
        rw [he,atMark] at hh
        exact hh.symm
      have hne (i : Fin k) : g (peak.succAbove i) ≠ c := by
        rw [← he]
        exact fun h => peak.succAbove_ne i (hg.injective h)
      let f (i : Fin k) : Fin n := (finSuccAboveEquiv c).symm ⟨g (peak.succAbove i),hne i⟩
      have hf (i : Fin k) : c.succAbove (f i) = g (peak.succAbove i) :=
        congrArg Subtype.val ((finSuccAboveEquiv c).apply_symm_apply ⟨_,hne i⟩)
      refine ⟨f,?_,?_,?_⟩
      · intro i j hij
        apply (Fin.succAbove_lt_succAbove_iff).mp
        change c.succAbove (f i) < c.succAbove (f j)
        rw [hf,hf]
        exact hg ((Fin.strictMono_succAbove _) hij)
      · intro i j
        have hh := hr (peak.succAbove i) (peak.succAbove j)
        rw [← hf i,← hf j,placeMaximum_away,placeMaximum_away] at hh
        exact (Fin.castSucc_lt_castSucc_iff).symm.trans hh
      · intro i
        have hc := hgrid (peak.succAbove i)
        change largeCol (g (peak.succAbove i)) = col (peak.succAbove i) at hc
        rw [← hf,keepCol] at hc
        have hl : (f i).val < c.val ↔ i.val < peak.val := by
          change (f i).castSucc < c ↔ i.castSucc < peak
          rw [← Fin.succAbove_lt_iff_castSucc_lt,← Fin.succAbove_lt_iff_castSucc_lt,hf,← he]
          exact hg.lt_iff_lt
        change splitCol (f i) = refineColumn pivot (col (peak.succAbove i)) (i.val < peak.val)
        rw [splitsCol,hc]
        simp [refineColumn,hl]
    · left
      have hne (i : Fin (k+1)) : g i ≠ c := by
        intro he'
        have hi : i ≠ peak := fun hp => he (hp ▸ he')
        have hh := (hr i peak).mpr (hpeak i hi)
        rw [he',placeMaximum_at] at hh
        exact (not_lt_of_ge (Fin.le_last _)) hh
      let f (i : Fin (k+1)) : Fin n := (finSuccAboveEquiv c).symm ⟨g i,hne i⟩
      have hf (i : Fin (k+1)) : c.succAbove (f i) = g i :=
        congrArg Subtype.val ((finSuccAboveEquiv c).apply_symm_apply ⟨_,hne i⟩)
      have hm' : StrictMono f := by
        intro i j hij
        apply (Fin.succAbove_lt_succAbove_iff).mp
        rw [hf,hf]
        exact hg hij
      obtain ⟨t,ht,hl⟩ := prefixBefore f hm' c.val
      refine ⟨t,ht,f,hm',?_,?_⟩
      · intro i j
        have hh := hr i j
        rw [← hf i,← hf j,placeMaximum_away,placeMaximum_away] at hh
        exact (Fin.castSucc_lt_castSucc_iff).symm.trans hh
      · intro i
        have hc := hgrid i
        change largeCol (g i) = col i at hc
        rw [← hf,keepCol] at hc
        change splitCol (f i) = refineColumn pivot (col i) (i.val < t)
        rw [splitsCol,hc]
        simp [refineColumn,hl]
  · rintro (⟨t,ht,f,hf,hr,hg⟩ | ⟨hcPeak,f,hf,hr,hg⟩)
    · refine ⟨c.succAbove ∘ f,(Fin.strictMono_succAbove c).comp hf,?_,?_⟩
      · intro i j
        change placeMaximum c σ (c.succAbove (f i)) <
          placeMaximum c σ (c.succAbove (f j)) ↔ _
        simpa only [placeMaximum_away,Fin.castSucc_lt_castSucc_iff,splitAtColumn] using hr i j
      · intro i
        change largeCol (c.succAbove (f i)) = col i
        rw [keepCol]
        have hh := hg i
        change splitCol (f i) = refineColumn pivot (col i) (i.val < t) at hh
        rw [splitsCol] at hh
        simpa only [refine_restore, refine_restore] using congrArg (coalesceColumn pivot) hh
    · let g : Fin (k+1) → Fin (n+1) := peak.insertNth c (c.succAbove ∘ f)
      have gPeak : g peak = c := by simp [g]
      have gAway (i : Fin k) : g (peak.succAbove i) = c.succAbove (f i) := by simp [g,Function.comp_def]
      have originalCol (i : Fin k) : smallCol (f i) = col (peak.succAbove i) := by
        have hh := hg i
        change splitCol (f i) = refineColumn pivot (col (peak.succAbove i)) (i.val < peak.val) at hh
        rw [splitsCol] at hh
        simpa only [refine_restore, refine_restore] using congrArg (coalesceColumn pivot) hh
      have hcut (i : Fin k) : (f i).val < c.val ↔ i.val < peak.val := by
        by_cases h2 : col (peak.succAbove i) = pivot
        · have hh := hg i
          change splitCol (f i) = refineColumn pivot (col (peak.succAbove i)) (i.val < peak.val) at hh
          rw [splitsCol,originalCol] at hh
          exact refine_at_split pivot _ _ (by simpa only [h2] using hh)
        · have hmono (i' j' : Fin (k+1)) (h : i' < j') : col i' ≤ col j' := hm h.le
          constructor
          · intro hfBefore
            by_contra! hn
            have hh := hm ((Fin.lt_succAbove_iff_le_castSucc _ _).mpr hn |>.le)
            rw [hcPeak] at hh
            have hh' : pivot < col (peak.succAbove i) := lt_of_le_of_ne hh (Ne.symm h2)
            exact (Nat.not_lt_of_ge (afterSplit (f i) (by rwa [originalCol]))) hfBefore
          · intro hi
            have hh := hmono _ _ ((Fin.succAbove_lt_iff_castSucc_lt _ _).mpr hi)
            rw [hcPeak] at hh
            have hh' : col (peak.succAbove i) < pivot := lt_of_le_of_ne hh h2
            exact beforeSplit (f i) (by rwa [originalCol])
      refine ⟨g,?_,?_,?_⟩
      · intro i j hlt
        revert hlt
        refine Fin.succAboveCases peak ?_ (fun a' => ?_) i
        · refine Fin.succAboveCases peak (by simp) (fun b' => ?_) j
          intro hb'
          simp only [gPeak,gAway]
          apply (Fin.lt_succAbove_iff_le_castSucc _ _).mpr
          have hβ : ¬ b'.val < peak.val := fun hh =>
            (not_lt_of_gt hb') ((Fin.succAbove_lt_iff_castSucc_lt _ _).mpr hh)
          exact Nat.le_of_not_gt (fun hh => hβ ((hcut b').mp hh))
        · refine Fin.succAboveCases peak ?_ (fun b' => ?_) j
          · intro ha'
            simp only [gPeak,gAway]
            exact (Fin.succAbove_lt_iff_castSucc_lt _ _).mpr
              ((hcut a').mpr ((Fin.succAbove_lt_iff_castSucc_lt _ _).mp ha'))
          · intro hab'
            simpa only [gAway,Fin.succAbove_lt_succAbove_iff] using
              (hf ((Fin.succAbove_lt_succAbove_iff).mp hab'))
      · intro i j
        change placeMaximum c σ (g i) < placeMaximum c σ (g j) ↔ r i < r j
        refine Fin.succAboveCases peak ?_ (fun a' => ?_) i
        · refine Fin.succAboveCases peak (by simp) (fun b' => ?_) j
          have hb' := hpeak (peak.succAbove b') (peak.succAbove_ne b')
          simp [gPeak,gAway,not_lt_of_gt hb',Fin.le_last]
        · refine Fin.succAboveCases peak (by simp [gPeak,gAway,hpeak _ (peak.succAbove_ne a')]) (fun b' => ?_) j
          simpa only [gAway,placeMaximum_away,Fin.castSucc_lt_castSucc_iff,dropAtColumn] using hr a' b'
      · intro i
        change largeCol (g i) = col i
        refine Fin.succAboveCases peak ?_ (fun a' => ?_) i
        · rw [gPeak,atMark,hcPeak]
        · rw [gAway,keepCol,originalCol]
end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4

theorem middlePlacement_occurs_iff {n k : ℕ} {a b c : Fin (n+1)} (hac : a ≤ c)
    (hcb : c ≤ b) (σ : Equiv.Perm (Fin n)) (r col : Fin (k+1) → ℕ)
    (peak : Fin (k+1)) (hpeak : ∀ i ≠ peak, r i < r peak) (hm : Monotone col) :
    gridOccurs (placeMaximum c σ) (cols3 a.val (b.val+1)) ⟨k+1,r,col⟩ ↔
      (∃ t ≤ k+1, gridOccurs σ (cols4 a.val c.val b.val)
        (splitAtColumn 1 ⟨k+1,r,col⟩ t)) ∨
      (col peak = 1 ∧ gridOccurs σ (cols4 a.val c.val b.val) (dropAtColumn 1 r col peak)) := by
  have ha : a.val ≤ c.val := hac
  have hb : c.val ≤ b.val := hcb
  apply placeColumn_occurs_iff c 1 (cols3 a.val b.val) (cols4 a.val c.val b.val)
    (cols3 a.val (b.val+1)) _ _ _ _ _ σ r col peak hpeak hm
  · simp [cols3,not_lt_of_ge ha,Nat.lt_succ_of_le hb]
  · intro i
    by_cases h : i.val < c.val
    · rw [Fin.succAbove_of_castSucc_lt c i h]
      simp only [cols3,Fin.val_castSucc]
      split_ifs <;> omega
    · rw [Fin.succAbove_of_le_castSucc c i (Nat.le_of_not_gt h)]
      simp only [cols3,Fin.val_succ]
      split_ifs <;> omega
  · intro i
    unfold cols3 cols4 refineColumn
    split_ifs <;> omega
  · intro i h
    unfold cols3 at h
    split_ifs at h <;> omega
  · intro i h
    unfold cols3 at h
    split_ifs at h <;> omega

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
def middleBasis : List GridPattern := [
  .ofLists [0, 1] [0, 3],
  .ofLists [0, 1] [1, 3],
  .ofLists [0, 2, 1] [0, 0, 0],
  .ofLists [0, 2, 1] [0, 0, 1],
  .ofLists [0, 2, 1] [0, 0, 2],
  .ofLists [0, 2, 1] [0, 1, 2],
  .ofLists [0, 2, 1] [1, 1, 2],
  .ofLists [0, 2, 1] [2, 2, 3],
  .ofLists [0, 2, 1, 3] [0, 1, 1, 2],
  .ofLists [0, 2, 1, 3] [1, 1, 1, 2],
  .ofLists [0, 2, 1, 3] [2, 2, 2, 3],
  .ofLists [0, 2, 3, 1] [0, 1, 1, 1],
  .ofLists [0, 2, 3, 1] [0, 2, 2, 2],
  .ofLists [0, 2, 3, 1] [1, 1, 1, 1],
  .ofLists [0, 2, 3, 1] [1, 2, 2, 2],
  .ofLists [0, 2, 3, 1] [2, 2, 2, 2],
  .ofLists [0, 2, 3, 1] [2, 3, 3, 3],
  .ofLists [0, 2, 3, 1] [3, 3, 3, 3],
  .ofLists [0, 2, 1, 4, 3] [0, 1, 1, 1, 1],
  .ofLists [0, 2, 1, 4, 3] [0, 2, 2, 2, 2],
  .ofLists [0, 2, 1, 4, 3] [1, 1, 1, 1, 1],
  .ofLists [0, 2, 1, 4, 3] [1, 2, 2, 2, 2],
  .ofLists [0, 2, 1, 4, 3] [2, 2, 2, 2, 2],
  .ofLists [0, 2, 1, 4, 3] [2, 3, 3, 3, 3],
  .ofLists [0, 2, 1, 4, 3] [3, 3, 3, 3, 3]
]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem maximumMiddle_avoids_iff {n : ℕ} {a b c : Fin (n+1)}
    (hac : a ≤ c) (hcb : c ≤ b) (σ : Equiv.Perm (Fin n)) :
    avoidsGrid (placeMaximum c σ) (cols3 a.val (b.val+1)) trackedBasis ↔
      avoidsGrid σ (cols4 a.val c.val b.val) middleBasis := by
  constructor
  · intro hg p hp ho
    simp only [middleBasis,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · apply hg _ (List.get_mem trackedBasis ⟨3, by decide⟩)
      have ge : ⟨3,![0, 2, 1],![0, 1, 2]⟩ = trackedBasis.get ⟨3, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 2) hac hcb σ ![0, 2, 1] ![0, 1, 2] 1 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      right; refine ⟨by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨4, by decide⟩)
      have ge : ⟨3,![0, 2, 1],![1, 1, 2]⟩ = trackedBasis.get ⟨4, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 2) hac hcb σ ![0, 2, 1] ![1, 1, 2] 1 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      right; refine ⟨by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨0, by decide⟩)
      have ge : ⟨3,![0, 2, 1],![0, 0, 0]⟩ = trackedBasis.get ⟨0, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 2) hac hcb σ ![0, 2, 1] ![0, 0, 0] 1 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨1, by decide⟩)
      have ge : ⟨3,![0, 2, 1],![0, 0, 1]⟩ = trackedBasis.get ⟨1, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 2) hac hcb σ ![0, 2, 1] ![0, 0, 1] 1 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨3,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨1, by decide⟩)
      have ge : ⟨3,![0, 2, 1],![0, 0, 1]⟩ = trackedBasis.get ⟨1, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 2) hac hcb σ ![0, 2, 1] ![0, 0, 1] 1 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨7, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![0, 1, 1, 1]⟩ = trackedBasis.get ⟨7, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 3) hac hcb σ ![0, 2, 3, 1] ![0, 1, 1, 1] 2 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      right; refine ⟨by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨9, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![1, 1, 1, 1]⟩ = trackedBasis.get ⟨9, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 3) hac hcb σ ![0, 2, 3, 1] ![1, 1, 1, 1] 2 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      right; refine ⟨by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨4, by decide⟩)
      have ge : ⟨3,![0, 2, 1],![1, 1, 2]⟩ = trackedBasis.get ⟨4, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 2) hac hcb σ ![0, 2, 1] ![1, 1, 2] 1 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨12, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![0, 1, 1, 1, 1]⟩ = trackedBasis.get ⟨12, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 4) hac hcb σ ![0, 2, 1, 4, 3] ![0, 1, 1, 1, 1] 3 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      right; refine ⟨by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨14, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![1, 1, 1, 1, 1]⟩ = trackedBasis.get ⟨14, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 4) hac hcb σ ![0, 2, 1, 4, 3] ![1, 1, 1, 1, 1] 3 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      right; refine ⟨by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨6, by decide⟩)
      have ge : ⟨4,![0, 2, 1, 3],![1, 1, 1, 2]⟩ = trackedBasis.get ⟨6, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 3) hac hcb σ ![0, 2, 1, 3] ![1, 1, 1, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨7, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![0, 1, 1, 1]⟩ = trackedBasis.get ⟨7, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 3) hac hcb σ ![0, 2, 3, 1] ![0, 1, 1, 1] 2 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨4,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨7, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![0, 1, 1, 1]⟩ = trackedBasis.get ⟨7, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 3) hac hcb σ ![0, 2, 3, 1] ![0, 1, 1, 1] 2 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨9, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![1, 1, 1, 1]⟩ = trackedBasis.get ⟨9, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 3) hac hcb σ ![0, 2, 3, 1] ![1, 1, 1, 1] 2 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨4,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨9, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![1, 1, 1, 1]⟩ = trackedBasis.get ⟨9, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 3) hac hcb σ ![0, 2, 3, 1] ![1, 1, 1, 1] 2 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨1,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨9, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![1, 1, 1, 1]⟩ = trackedBasis.get ⟨9, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 3) hac hcb σ ![0, 2, 3, 1] ![1, 1, 1, 1] 2 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨10, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![1, 2, 2, 2]⟩ = trackedBasis.get ⟨10, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 3) hac hcb σ ![0, 2, 3, 1] ![1, 2, 2, 2] 2 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨11, by decide⟩)
      have ge : ⟨4,![0, 2, 3, 1],![2, 2, 2, 2]⟩ = trackedBasis.get ⟨11, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 3) hac hcb σ ![0, 2, 3, 1] ![2, 2, 2, 2] 2 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨12, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![0, 1, 1, 1, 1]⟩ = trackedBasis.get ⟨12, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 4) hac hcb σ ![0, 2, 1, 4, 3] ![0, 1, 1, 1, 1] 3 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨5,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨12, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![0, 1, 1, 1, 1]⟩ = trackedBasis.get ⟨12, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 4) hac hcb σ ![0, 2, 1, 4, 3] ![0, 1, 1, 1, 1] 3 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨14, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![1, 1, 1, 1, 1]⟩ = trackedBasis.get ⟨14, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 4) hac hcb σ ![0, 2, 1, 4, 3] ![1, 1, 1, 1, 1] 3 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨5,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨14, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![1, 1, 1, 1, 1]⟩ = trackedBasis.get ⟨14, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 4) hac hcb σ ![0, 2, 1, 4, 3] ![1, 1, 1, 1, 1] 3 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨1,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨14, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![1, 1, 1, 1, 1]⟩ = trackedBasis.get ⟨14, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 4) hac hcb σ ![0, 2, 1, 4, 3] ![1, 1, 1, 1, 1] 3 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨15, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![1, 2, 2, 2, 2]⟩ = trackedBasis.get ⟨15, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 4) hac hcb σ ![0, 2, 1, 4, 3] ![1, 2, 2, 2, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩
    · apply hg _ (List.get_mem trackedBasis ⟨16, by decide⟩)
      have ge : ⟨5,![0, 2, 1, 4, 3],![2, 2, 2, 2, 2]⟩ = trackedBasis.get ⟨16, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge]
      apply (middlePlacement_occurs_iff (k := 4) hac hcb σ ![0, 2, 1, 4, 3] ![2, 2, 2, 2, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel)).mpr
      left; refine ⟨0,by decide,?_⟩
      apply gridOccurs_of_subpattern _ ho
      exact ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩
  · intro hs p hp ho
    simp only [trackedBasis,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · change gridOccurs _ _ (trackedBasis.get ⟨0, by decide⟩) at ho
      have ge : ⟨3,![0, 2, 1],![0, 0, 0]⟩ = trackedBasis.get ⟨0, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (middlePlacement_occurs_iff (k := 2) hac hcb σ ![0, 2, 1] ![0, 0, 0] 1 (by decide +kernel) (by unfold Monotone; decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem middleBasis ⟨2, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨2, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨2, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨2, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![0, 0, 0] (1 : Fin 3) ≠ 1) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨1, by decide⟩) at ho
      have ge : ⟨3,![0, 2, 1],![0, 0, 1]⟩ = trackedBasis.get ⟨1, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (middlePlacement_occurs_iff (k := 2) hac hcb σ ![0, 2, 1] ![0, 0, 1] 1 (by decide +kernel) (by unfold Monotone; decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem middleBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨4, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨3, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![0, 0, 1] (1 : Fin 3) ≠ 1) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨2, by decide⟩) at ho
      have ge : ⟨3,![0, 2, 1],![0, 0, 2]⟩ = trackedBasis.get ⟨2, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (middlePlacement_occurs_iff (k := 2) hac hcb σ ![0, 2, 1] ![0, 0, 2] 1 (by decide +kernel) (by unfold Monotone; decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![0, 0, 2] (1 : Fin 3) ≠ 1) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨3, by decide⟩) at ho
      have ge : ⟨3,![0, 2, 1],![0, 1, 2]⟩ = trackedBasis.get ⟨3, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (middlePlacement_occurs_iff (k := 2) hac hcb σ ![0, 2, 1] ![0, 1, 2] 1 (by decide +kernel) (by unfold Monotone; decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
      · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
          (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
    · change gridOccurs _ _ (trackedBasis.get ⟨4, by decide⟩) at ho
      have ge : ⟨3,![0, 2, 1],![1, 1, 2]⟩ = trackedBasis.get ⟨4, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (middlePlacement_occurs_iff (k := 2) hac hcb σ ![0, 2, 1] ![1, 1, 2] 1 (by decide +kernel) (by unfold Monotone; decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem middleBasis ⟨7, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
      · exact hs _ (List.get_mem middleBasis ⟨1, by decide⟩)
          (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
    · change gridOccurs _ _ (trackedBasis.get ⟨5, by decide⟩) at ho
      have ge : ⟨4,![0, 2, 1, 3],![0, 1, 1, 2]⟩ = trackedBasis.get ⟨5, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (middlePlacement_occurs_iff (k := 3) hac hcb σ ![0, 2, 1, 3] ![0, 1, 1, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![0, 1, 1, 2] (3 : Fin 4) ≠ 1) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨6, by decide⟩) at ho
      have ge : ⟨4,![0, 2, 1, 3],![1, 1, 1, 2]⟩ = trackedBasis.get ⟨6, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (middlePlacement_occurs_iff (k := 3) hac hcb σ ![0, 2, 1, 3] ![1, 1, 1, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem middleBasis ⟨10, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![1, 1, 1, 2] (3 : Fin 4) ≠ 1) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨7, by decide⟩) at ho
      have ge : ⟨4,![0, 2, 3, 1],![0, 1, 1, 1]⟩ = trackedBasis.get ⟨7, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (middlePlacement_occurs_iff (k := 3) hac hcb σ ![0, 2, 3, 1] ![0, 1, 1, 1] 2 (by decide +kernel) (by unfold Monotone; decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem middleBasis ⟨12, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨12, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨5, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨5, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨11, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
      · exact hs _ (List.get_mem middleBasis ⟨5, by decide⟩)
          (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
    · change gridOccurs _ _ (trackedBasis.get ⟨8, by decide⟩) at ho
      have ge : ⟨4,![0, 2, 3, 1],![0, 2, 2, 2]⟩ = trackedBasis.get ⟨8, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (middlePlacement_occurs_iff (k := 3) hac hcb σ ![0, 2, 3, 1] ![0, 2, 2, 2] 2 (by decide +kernel) (by unfold Monotone; decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![0, 2, 2, 2] (2 : Fin 4) ≠ 1) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨9, by decide⟩) at ho
      have ge : ⟨4,![0, 2, 3, 1],![1, 1, 1, 1]⟩ = trackedBasis.get ⟨9, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (middlePlacement_occurs_iff (k := 3) hac hcb σ ![0, 2, 3, 1] ![1, 1, 1, 1] 2 (by decide +kernel) (by unfold Monotone; decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem middleBasis ⟨15, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨14, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨6, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨6, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨13, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
      · exact hs _ (List.get_mem middleBasis ⟨6, by decide⟩)
          (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
    · change gridOccurs _ _ (trackedBasis.get ⟨10, by decide⟩) at ho
      have ge : ⟨4,![0, 2, 3, 1],![1, 2, 2, 2]⟩ = trackedBasis.get ⟨10, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (middlePlacement_occurs_iff (k := 3) hac hcb σ ![0, 2, 3, 1] ![1, 2, 2, 2] 2 (by decide +kernel) (by unfold Monotone; decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem middleBasis ⟨16, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![1, 2, 2, 2] (2 : Fin 4) ≠ 1) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨11, by decide⟩) at ho
      have ge : ⟨4,![0, 2, 3, 1],![2, 2, 2, 2]⟩ = trackedBasis.get ⟨11, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (middlePlacement_occurs_iff (k := 3) hac hcb σ ![0, 2, 3, 1] ![2, 2, 2, 2] 2 (by decide +kernel) (by unfold Monotone; decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem middleBasis ⟨17, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨17, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨17, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨17, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨17, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![2, 2, 2, 2] (2 : Fin 4) ≠ 1) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨12, by decide⟩) at ho
      have ge : ⟨5,![0, 2, 1, 4, 3],![0, 1, 1, 1, 1]⟩ = trackedBasis.get ⟨12, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (middlePlacement_occurs_iff (k := 4) hac hcb σ ![0, 2, 1, 4, 3] ![0, 1, 1, 1, 1] 3 (by decide +kernel) (by unfold Monotone; decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem middleBasis ⟨19, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨19, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨5, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨8, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨5, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨18, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
      · exact hs _ (List.get_mem middleBasis ⟨8, by decide⟩)
          (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
    · change gridOccurs _ _ (trackedBasis.get ⟨13, by decide⟩) at ho
      have ge : ⟨5,![0, 2, 1, 4, 3],![0, 2, 2, 2, 2]⟩ = trackedBasis.get ⟨13, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (middlePlacement_occurs_iff (k := 4) hac hcb σ ![0, 2, 1, 4, 3] ![0, 2, 2, 2, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨0, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![0, 2, 2, 2, 2] (3 : Fin 5) ≠ 1) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨14, by decide⟩) at ho
      have ge : ⟨5,![0, 2, 1, 4, 3],![1, 1, 1, 1, 1]⟩ = trackedBasis.get ⟨14, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (middlePlacement_occurs_iff (k := 4) hac hcb σ ![0, 2, 1, 4, 3] ![1, 1, 1, 1, 1] 3 (by decide +kernel) (by unfold Monotone; decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem middleBasis ⟨22, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨21, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨6, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨9, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨6, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨20, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
      · exact hs _ (List.get_mem middleBasis ⟨9, by decide⟩)
          (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ hp)
    · change gridOccurs _ _ (trackedBasis.get ⟨15, by decide⟩) at ho
      have ge : ⟨5,![0, 2, 1, 4, 3],![1, 2, 2, 2, 2]⟩ = trackedBasis.get ⟨15, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (middlePlacement_occurs_iff (k := 4) hac hcb σ ![0, 2, 1, 4, 3] ![1, 2, 2, 2, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem middleBasis ⟨23, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨1, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![1, 2, 2, 2, 2] (3 : Fin 5) ≠ 1) hb
    · change gridOccurs _ _ (trackedBasis.get ⟨16, by decide⟩) at ho
      have ge : ⟨5,![0, 2, 1, 4, 3],![2, 2, 2, 2, 2]⟩ = trackedBasis.get ⟨16, by decide⟩ := GridPattern.code_injective (by decide +kernel)
      rw [← ge] at ho
      rcases (middlePlacement_occurs_iff (k := 4) hac hcb σ ![0, 2, 1, 4, 3] ![2, 2, 2, 2, 2] 3 (by decide +kernel) (by unfold Monotone; decide +kernel)).mp ho with (⟨t,ht,hp⟩ | ⟨hb,hp⟩)
      · interval_cases t
        · exact hs _ (List.get_mem middleBasis ⟨24, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨24, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨24, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨24, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨24, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
        · exact hs _ (List.get_mem middleBasis ⟨24, by decide⟩)
            (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ hp)
      · exact (by decide : ![2, 2, 2, 2, 2] (3 : Fin 5) ≠ 1) hb

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4 OMA.S_oeis_a001764

private abbrev p01 (col : ℕ) := GridPattern.ofLists [0,1] [col,3]
private abbrev p223 := GridPattern.ofLists [0,2,1] [2,2,3]

private theorem firstPartAboveC {n a c b : ℕ} (σ : Equiv.Perm (Fin n))
    (hcb : c ≤ b) (h : avoidsGrid σ (cols4 a c b) middleBasis)
    {i j : Fin n} (hi : i.val < c) (hj : b ≤ j.val) (hac : a ≤ c) :
    σ j < σ i := by
  have hij : i < j := Nat.lt_of_lt_of_le hi (hcb.trans hj)
  by_contra! hn
  have hr : σ i < σ j := lt_of_le_of_ne hn (fun he => (ne_of_lt hij) (σ.injective he))
  have hj' : cols4 a c b j = 3 := by
    unfold cols4
    split_ifs <;> omega
  let ci := cols4 a c b i
  have hc : ci ≤ 1 := by dsimp [ci]; simp [cols4,hi]; split_ifs <;> decide
  have hp : p01 ci ∈ middleBasis := by
    change cols4 a c b i ≤ 1 at hc
    have hc' : ci = 0 ∨ ci = 1 := by omega
    rcases hc' with hz | ho
    · rw [hz]; simp [middleBasis]
    · rw [ho]; simp [middleBasis]
  apply h _ hp
  refine ⟨(![i,j] : Fin 2 → Fin n),?_ ,?_,?_⟩
  · change StrictMono (![i,j] : Fin 2 → Fin n)
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all <;> omega
  · change ∀ x y : Fin 2, σ ((![i,j] : Fin 2 → Fin n) x) <
        σ ((![i,j] : Fin 2 → Fin n) y) ↔ (p01 ci).rank x < (p01 ci).rank y
    intro x y
    fin_cases x <;> fin_cases y <;> simp_all [p01,p223,GridPattern.ofLists] <;> omega
  · change ∀ x : Fin 2, cols4 a c b ((![i,j] : Fin 2 → Fin n) x) = (p01 ci).column x
    intro x
    fin_cases x <;> simp [p01,GridPattern.ofLists,ci,hj']

private theorem prefix_of_rank_separation {n : ℕ} (σ : Equiv.Perm (Fin n))
    (k : ℕ) (hk : k ≤ n)
    (h : ∀ i j, (σ i).val < k → k ≤ (σ j).val → i < j) : SumCut σ k := by
  intro j hj
  by_contra! hval
  let pre : Fin k → Fin j.val := fun a =>
    ⟨(σ.symm ⟨a.val,by have := a.isLt; omega⟩).val, by
      apply h _ j _ hval
      simp⟩
  have hinj : Function.Injective pre := by
    intro a b hab
    have he : σ.symm ⟨a.val,by have := a.isLt; omega⟩ =
        σ.symm ⟨b.val,by have := b.isLt; omega⟩ :=
      Fin.ext (congrArg (fun x : Fin j.val => x.val) hab)
    apply Fin.ext
    exact congrArg (fun x : Fin n => x.val) (σ.symm.injective he)
  have hcard := Fintype.card_le_of_injective pre hinj
  simp at hcard
  omega

/-- The nonempty rightmost column in the middle-maximum branch has a
    right-hand peak. All entries higher than that peak detach in an
    initial high block. The cut lies between the two rightward cuts. -/
theorem middleHighCut {n a c b : ℕ} (σ : Equiv.Perm (Fin n))
    (hac : a ≤ c) (hcb : c ≤ b)
    (h : avoidsGrid σ (cols4 a c b) middleBasis) {p : Fin n}
    (hp : b ≤ p.val) (hpMax : ∀ i : Fin n, b ≤ i.val → σ i ≤ σ p) :
    let k := n-1-(σ p).val
    SumCut (σ.trans Fin.revPerm) k ∧ c ≤ k ∧ k ≤ b := by
  dsimp only
  let k := n-1-(σ p).val
  have valMap (i : Fin n) : ((σ.trans Fin.revPerm) i).val = n-1-(σ i).val := by
    change (σ i).rev.val = _
    rw [Fin.val_rev]
    omega
  have hpVal := (σ p).isLt
  have hh : SumCut (σ.trans Fin.revPerm) k := by
    apply prefix_of_rank_separation _ k (by dsimp [k]; omega)
    intro i j hi hj
    rw [valMap] at hi hj
    have hiV : σ p < σ i := by change (σ p).val < (σ i).val; dsimp [k] at hi; omega
    have hjV : σ j ≤ σ p := by
      change (σ j).val ≤ (σ p).val
      have := (σ j).isLt
      dsimp [k] at hj
      omega
    have hib : i.val < b := by
      by_contra! hbad
      exact (not_lt_of_ge (hpMax _ hbad)) hiV
    by_contra! hij
    have hne : j ≠ i := fun he => (not_lt_of_ge hjV) (he ▸ hiV)
    have hji : j < i := lt_of_le_of_ne hij hne
    have hjc : c ≤ j.val := by
      by_contra! hn
      exact (not_lt_of_ge hjV) (firstPartAboveC σ hcb h hn hp hac)
    have hjb : j.val < b := lt_trans hji hib
    have hic : c ≤ i.val := hjc.trans hji.le
    have hjp : j < p := Nat.lt_of_lt_of_le hjb hp
    have hjVp : σ j < σ p := lt_of_le_of_ne hjV
      (fun he => (ne_of_lt hjp) (σ.injective he))
    have hci : cols4 a c b i = 2 := by unfold cols4; split_ifs <;> omega
    have hcj : cols4 a c b j = 2 := by unfold cols4; split_ifs <;> omega
    have hcp : cols4 a c b p = 3 := by unfold cols4; split_ifs <;> omega
    apply h p223 (by simp [middleBasis])
    refine ⟨(![j,i,p] : Fin 3 → Fin n),?_,?_,?_⟩
    · change StrictMono (![j,i,p] : Fin 3 → Fin n)
      have hip : i < p := Nat.lt_of_lt_of_le hib hp
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all <;> omega
    · change ∀ x y : Fin 3, σ ((![j,i,p] : Fin 3 → Fin n) x) <
          σ ((![j,i,p] : Fin 3 → Fin n) y) ↔ p223.rank x < p223.rank y
      intro x y
      fin_cases x <;> fin_cases y <;> simp_all [p01,p223,GridPattern.ofLists] <;> omega
    · change ∀ x : Fin 3, cols4 a c b ((![j,i,p] : Fin 3 → Fin n) x) = p223.column x
      intro x
      fin_cases x <;> simp [p223, GridPattern.ofLists,hcj,hci,hcp]
  refine ⟨hh,?_,?_⟩
  · by_contra! hn
    let j : Fin n := ⟨k,by dsimp [k]; omega⟩
    have hi : j.val < c := hn
    have hp' := firstPartAboveC σ hcb h hi hp hac
    have hV := rightOfSumCut hh j (by rfl)
    rw [valMap] at hV
    change (σ p).val < (σ j).val at hp'
    have := (σ j).isLt
    dsimp [k] at hV
    omega
  · by_contra! hn
    let j : Fin n := ⟨b,lt_of_le_of_lt hp p.isLt⟩
    have hh' := hh j hn
    rw [valMap] at hh'
    have hp' : (σ j).val ≤ (σ p).val := hpMax j le_rfl
    have := (σ j).isLt
    dsimp [k] at hh'
    omega

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4 OMA.S_oeis_a001764

def hasOnly (P : ℕ → Bool) (p : GridPattern) : Bool :=
  p.code.all fun x => P x.2

theorem hasOnly_iff (P : ℕ → Bool) (p : GridPattern) :
    hasOnly P p = true ↔ ∀ i, P (p.column i) = true := by
  simp only [hasOnly,List.all_eq_true,GridPattern.code,List.mem_ofFn]
  constructor
  · intro h i
    exact h (p.rank i,p.column i) ⟨i,rfl⟩
  · rintro h _ ⟨i,rfl⟩
    exact h i

theorem restrict_avoids {n : ℕ} (σ : Equiv.Perm (Fin n))
    (col : Fin n → ℕ) (basis : List GridPattern) (P : ℕ → Bool)
    (hcol : ∀ j, P (col j) = true) :
    avoidsGrid σ col basis ↔ avoidsGrid σ col (basis.filter (hasOnly P)) := by
  constructor
  · intro h p hp ho
    exact h p (List.mem_filter.mp hp).1 ho
  · intro h p hp ho
    have hP : hasOnly P p = true := by
      apply (hasOnly_iff P p).mpr
      intro i
      obtain ⟨f,_,_,hf⟩ := ho
      rw [← hf]
      exact hcol _
    exact h p (List.mem_filter.mpr ⟨hp,hP⟩) ho

theorem avoids_code_equiv {p q : List GridPattern}
    (h : (p.map GridPattern.code).toFinset = (q.map GridPattern.code).toFinset)
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (col : Fin n → ℕ) :
    avoidsGrid σ col p ↔ avoidsGrid σ col q := by
  have hin (L : List GridPattern) (p : GridPattern) :
      p.code ∈ (L.map GridPattern.code).toFinset ↔ p ∈ L := by
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨fun ⟨q,hq,he⟩ => GridPattern.code_injective he ▸ hq,
      fun hp => ⟨p,hp,rfl⟩⟩
  unfold avoidsGrid
  have hm (r : GridPattern) : r ∈ p ↔ r ∈ q := by rw [← hin,h,hin]
  simp only [hm]

set_option maxRecDepth 8192 in
private theorem middle_first3 :
    ((middleBasis.filter (hasOnly fun i => decide (i ≤ 2))).map GridPattern.code).toFinset =
      (trackedBasis.map GridPattern.code).toFinset := by decide +kernel

theorem middle_high_avoids_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (a b : ℕ) :
    avoidsGrid σ (cols3 a b) middleBasis ↔ avoidsGrid σ (cols3 a b) trackedBasis :=
  (restrict_avoids σ _ _ (fun i => decide (i ≤ 2)) (by intro j; simp [cols3]; split_ifs <;> decide)).trans
    (avoids_code_equiv middle_first3 σ _)

theorem middle_emptyRight_avoids_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (a b : ℕ) :
    avoidsGrid σ (cols4 a b n) middleBasis ↔ avoidsGrid σ (cols3 a b) trackedBasis := by
  have he : (cols4 a b n : Fin n → ℕ) = cols3 a b := by
    funext i
    simp [cols4,cols3,i.isLt]
  rw [he,middle_high_avoids_iff]

/-- An arbitrary two-row factor with all high values before all low values:
    if a gridded basis pattern ends higher than it starts, any occurrence
    is confined to exactly one side of the skew cut. -/
private theorem middleEndpoints (p : GridPattern) (hp : p ∈ middleBasis) :
    ∃ h : 0<p.size, p.rank ⟨0,h⟩ < p.rank ⟨p.size-1,by omega⟩ := by
  simp only [middleBasis,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ⟨by decide,by decide⟩

theorem middleAvoids_skew {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (f : Fin (m+n) → ℕ) :
    avoidsGrid (skewSum σ τ) f middleBasis ↔
      avoidsGrid σ (f ∘ Fin.castAdd n) middleBasis ∧
      avoidsGrid τ (f ∘ Fin.natAdd m) middleBasis := by
  constructor
  · intro h
    constructor
    · intro p hp ho
      obtain ⟨hn,he⟩ := middleEndpoints p hp
      exact h p hp ((gridOccurs_skew σ τ f p hn he).mpr (Or.inl ho))
    · intro p hp ho
      obtain ⟨hn,he⟩ := middleEndpoints p hp
      exact h p hp ((gridOccurs_skew σ τ f p hn he).mpr (Or.inr ho))
  · rintro ⟨hl,hr⟩ p hp ho
    obtain ⟨hn,he⟩ := middleEndpoints p hp
    rcases (gridOccurs_skew σ τ f p hn he).mp ho with h | h
    · exact hl p hp h
    · exact hr p hp h

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4 OMA.S_oeis_a001764

def cols2 {n : ℕ} (b : ℕ) (i : Fin n) : ℕ := if i.val < b then 0 else 1

def middleLowBasis : List GridPattern := [
  .ofLists [0,2,1] [0,0,1],
  .ofLists [0,2,1,3] [0,0,0,1],
  .ofLists [0,2,3,1] [0,0,0,0],
  .ofLists [0,2,3,1] [0,1,1,1],
  .ofLists [0,2,3,1] [1,1,1,1],
  .ofLists [0,2,1,4,3] [0,0,0,0,0],
  .ofLists [0,2,1,4,3] [0,1,1,1,1],
  .ofLists [0,2,1,4,3] [1,1,1,1,1]]

private def downTwo (p : GridPattern) : GridPattern :=
  ⟨p.size,p.rank,fun i => p.column i-2⟩

set_option maxRecDepth 8192 in
private theorem lowBasis_code :
    (((middleBasis.filter (hasOnly fun i => decide (2 ≤ i))).map downTwo).map GridPattern.code).toFinset
      = (middleLowBasis.map GridPattern.code).toFinset := by decide +kernel

private theorem gridOccurs_down {n : ℕ} (σ : Equiv.Perm (Fin n))
    (f : Fin n → ℕ) (p : GridPattern) (hp : ∀ i, 2 ≤ p.column i) :
    gridOccurs σ (fun i => f i+2) p ↔ gridOccurs σ f (downTwo p) := by
  constructor
  · rintro ⟨e,hs,hr,hc⟩
    refine ⟨e,hs,hr,fun i => ?_⟩
    have h := hc i
    change f (e i) + 2 = p.column i at h
    change f (e i) = p.column i-2
    omega
  · rintro ⟨e,hs,hr,hc⟩
    refine ⟨e,hs,hr,fun i => ?_⟩
    have h := hc i
    change f (e i) = p.column i-2 at h
    change f (e i)+2 = p.column i
    have := hp i
    omega

theorem middle_low_avoids_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (b : ℕ) :
    avoidsGrid σ (fun i => cols2 b i+2) middleBasis ↔
      avoidsGrid σ (cols2 b) middleLowBasis := by
  let P : ℕ → Bool := fun p => decide (2 ≤ p)
  let B := middleBasis.filter (hasOnly P)
  have hr : avoidsGrid σ (fun i => cols2 b i+2) middleBasis ↔
      avoidsGrid σ (fun i => cols2 b i+2) B := by
    apply restrict_avoids
    intro j
    simp [P]
  rw [hr,← avoids_code_equiv lowBasis_code σ (cols2 b)]
  constructor
  · intro h p hp ho
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    have hq' : ∀ i, 2 ≤ q.column i := by
      simpa [P] using (hasOnly_iff P q).mp (List.mem_filter.mp hq).2
    exact h q hq ((gridOccurs_down _ _ q hq').mpr ho)
  · intro h p hp ho
    have hp' : ∀ i, 2 ≤ p.column i := by
      simpa [P] using (hasOnly_iff P p).mp (List.mem_filter.mp hp).2
    exact h (downTwo p) (List.mem_map.mpr ⟨p,hp,rfl⟩)
      ((gridOccurs_down _ _ p hp').mp ho)

private theorem oneMark_occurs_iff {n k : ℕ} (c : Fin (n+1))
    (σ : Equiv.Perm (Fin n)) (r : Fin (k+1) → ℕ)
    (peak : Fin (k+1)) (hpeak : ∀ i ≠ peak, r i < r peak) :
    ¬ Avoids (placeMaximum c σ) r ↔
      (∃ t ≤ k+1, gridOccurs σ (cols2 c.val)
        (splitAtColumn 0 ⟨k+1,r,fun _ => 0⟩ t)) ∨
      gridOccurs σ (cols2 c.val) (dropAtColumn 0 r (fun _ => 0) peak) := by
  classical
  have he (x : Equiv.Perm (Fin (n+1))) :
      ¬ Avoids x r ↔ gridOccurs x (fun _ => 0) ⟨k+1,r,fun _ => 0⟩ := by
    rw [Avoids,not_not]
    exact ⟨fun ⟨f,hs,hr⟩ => ⟨f,hs,hr,fun _ => rfl⟩,
      fun ⟨f,hs,hr,_⟩ => ⟨f,hs,hr⟩⟩
  rw [he]
  have hh := placeColumn_occurs_iff c 0 (fun _ => 0) (cols2 c.val)
    (fun _ => 0) rfl (fun _ => rfl) (by intro i; simp [cols2,refineColumn])
    (by omega) (by omega) σ r (fun _ => 0) peak hpeak (fun _ _ _ => le_rfl)
  simpa only [true_and] using hh

theorem middleLow_placement_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (c : Fin (n+1)) :
    avoidsGrid σ (cols2 c.val) middleLowBasis ↔ PermPalPlacementCondition σ c := by
  unfold PermPalPlacementCondition PermPalAvoids

  rw [← permPal_place_pred c σ]
  constructor
  · intro rhs
    constructor
    · by_contra hn
      obtain ⟨t,ht,h₀⟩ | h₀ := (oneMark_occurs_iff c σ ![1, 3, 4, 2] 2 (by decide)).mp hn
      · interval_cases t
        · exact rhs _ (List.get_mem middleLowBasis ⟨4,by decide⟩) (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩ h₀)
        · exact rhs _ (List.get_mem middleLowBasis ⟨3,by decide⟩) (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩ h₀)
        · exact rhs _ (List.get_mem middleLowBasis ⟨0,by decide⟩) (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩],by decide⟩ h₀)
        · exact rhs _ (List.get_mem middleLowBasis ⟨0,by decide⟩) (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩],by decide⟩ h₀)
        · exact rhs _ (List.get_mem middleLowBasis ⟨2,by decide⟩) (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩ h₀)
      · exact rhs _ (List.get_mem middleLowBasis ⟨0,by decide⟩) (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩ h₀)
    · by_contra hn
      obtain ⟨t,ht,h₀⟩ | h₀ := (oneMark_occurs_iff c σ ![1, 3, 2, 5, 4] 3 (by decide)).mp hn
      · interval_cases t
        · exact rhs _ (List.get_mem middleLowBasis ⟨7,by decide⟩) (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩ h₀)
        · exact rhs _ (List.get_mem middleLowBasis ⟨6,by decide⟩) (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩ h₀)
        · exact rhs _ (List.get_mem middleLowBasis ⟨0,by decide⟩) (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩ h₀)
        · exact rhs _ (List.get_mem middleLowBasis ⟨1,by decide⟩) (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩ h₀)
        · exact rhs _ (List.get_mem middleLowBasis ⟨0,by decide⟩) (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩ h₀)
        · exact rhs _ (List.get_mem middleLowBasis ⟨5,by decide⟩) (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩ h₀)
      · exact rhs _ (List.get_mem middleLowBasis ⟨1,by decide⟩) (gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩ h₀)
  · rintro ⟨h4,h5⟩ p hp ho
    simp only [middleLowBasis,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · apply (oneMark_occurs_iff c σ ![1, 3, 4, 2] 2 (by decide)).mpr ?_ h4
      right
      exact gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩],by decide⟩ ho
    · apply (oneMark_occurs_iff c σ ![1, 3, 2, 5, 4] 3 (by decide)).mpr ?_ h5
      right
      exact gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩ ho
    · apply (oneMark_occurs_iff c σ ![1, 3, 4, 2] 2 (by decide)).mpr ?_ h4
      left; refine ⟨4,by decide,?_⟩
      exact gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩ ho
    · apply (oneMark_occurs_iff c σ ![1, 3, 4, 2] 2 (by decide)).mpr ?_ h4
      left; refine ⟨1,by decide,?_⟩
      exact gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩ ho
    · apply (oneMark_occurs_iff c σ ![1, 3, 4, 2] 2 (by decide)).mpr ?_ h4
      left; refine ⟨0,by decide,?_⟩
      exact gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩],by decide⟩ ho
    · apply (oneMark_occurs_iff c σ ![1, 3, 2, 5, 4] 3 (by decide)).mpr ?_ h5
      left; refine ⟨5,by decide,?_⟩
      exact gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩ ho
    · apply (oneMark_occurs_iff c σ ![1, 3, 2, 5, 4] 3 (by decide)).mpr ?_ h5
      left; refine ⟨1,by decide,?_⟩
      exact gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩ ho
    · apply (oneMark_occurs_iff c σ ![1, 3, 2, 5, 4] 3 (by decide)).mpr ?_ h5
      left; refine ⟨0,by decide,?_⟩
      exact gridOccurs_of_subpattern ⟨![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],by decide⟩ ho

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4 OMA.S_oeis_a001764

theorem middleSkew_product_iff {m n : ℕ} (σ : Equiv.Perm (Fin m))
    (τ : Equiv.Perm (Fin n)) (a b : Fin (m+1)) (c : Fin (n+1)) :
    avoidsGrid (skewSum σ τ) (cols4 a.val b.val (m+c.val)) middleBasis ↔
      avoidsGrid σ (cols3 a.val b.val) trackedBasis ∧ PermPalPlacementCondition τ c := by
  have hL : (cols4 a.val b.val (m+c.val) : Fin (m+n) → ℕ) ∘
        Fin.castAdd n = cols3 a.val b.val := by
    funext i
    have hi : i.val < m+c.val := by have := i.isLt; omega
    simp [cols4,cols3,hi]
  have hR : (cols4 a.val b.val (m+c.val) : Fin (m+n) → ℕ) ∘
        Fin.natAdd m = (fun i : Fin n => cols2 c.val i+2) := by
    funext i
    have ha : a.val ≤ m := Nat.le_of_lt_succ a.isLt
    have hb : b.val ≤ m := Nat.le_of_lt_succ b.isLt
    have hi : m ≤ m+i.val := Nat.le_add_right _ _
    simp [cols4,cols2,not_lt_of_ge (ha.trans hi),not_lt_of_ge (hb.trans hi)]
    split_ifs <;> decide
  rw [middleAvoids_skew,hL,hR,middle_high_avoids_iff,middle_low_avoids_iff,middleLow_placement_iff]

structure MiddleCuts (n : ℕ) where
  left : Fin (n+1)
  center : Fin (n+1)
  right : Fin (n+1)
  hlc : left ≤ center
  hcr : center ≤ right
  deriving DecidableEq

abbrev MiddleClass (n : ℕ) :=
  {s : Equiv.Perm (Fin n) × MiddleCuts n //
    avoidsGrid s.1 (cols4 s.2.left.val s.2.center.val s.2.right.val) middleBasis}

/-- The middle branch after deleting its maximum, with the third column
    nonempty and its maximum constrained to have rank n. -/
abbrev MiddleSlice (m n : ℕ) :=
  {s : MiddleClass (m+(n+1)) // ∃ p : Fin (m+(n+1)),
    RightPeak s.val.1 s.val.2.right p ∧ (s.val.1 p).val = n}

private theorem middleSlice_ext {m n : ℕ} {u v : MiddleSlice m n}
    (hp : u.val.val.1 = v.val.val.1)
    (hc : u.val.val.2.left = v.val.val.2.left)
    (hd : u.val.val.2.center = v.val.val.2.center)
    (he : u.val.val.2.right = v.val.val.2.right) :
    u = v := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext hp
  rcases u with ⟨⟨⟨p,cl,cc,cr,hl,hr⟩,pu⟩,u⟩
  rcases v with ⟨⟨⟨q,dl,dc,dr,jl,jr⟩,pv⟩,v⟩
  dsimp only at hc hd he
  subst dl; subst dc; subst dr
  rfl

private def combineMiddle {m n : ℕ} (x : Rule9Target m × LowPlaced n) :
    MiddleSlice m n := by
  rcases x with ⟨⟨⟨σ,⟨a,b⟩,hab⟩,hs⟩,c,⟨τ,ht⟩,hc⟩
  let p := τ.symm (Fin.last n)
  let q := skewSum σ τ
  let cuts : MiddleCuts (m+(n+1)) :=
    ⟨⟨a.val,by have := a.isLt; omega⟩,⟨b.val,by have := b.isLt; omega⟩,shiftCut m c,hab,
      by change b.val ≤ m+c.val; have := b.isLt; omega⟩
  have hh : avoidsGrid q (cols4 cuts.left.val cuts.center.val cuts.right.val) middleBasis :=
    (middleSkew_product_iff σ τ a b c).mpr ⟨hs,ht⟩
  refine ⟨⟨⟨q,cuts⟩,hh⟩,Fin.natAdd m p,⟨Nat.add_le_add_left hc m,?_⟩,?_⟩
  · intro i hi
    change m+c.val ≤ i.val at hi
    let j : Fin (n+1) := ⟨i.val-m,by have := i.isLt; omega⟩
    have ij : Fin.natAdd m j = i := Fin.ext (by dsimp [j]; omega)
    change (q i).val ≤ (q (Fin.natAdd m p)).val
    rw [← ij,skewValLow,skewValLow]
    have hep : τ p = Fin.last n := τ.apply_symm_apply _
    rw [hep]
    exact Nat.le_of_lt_succ (τ j).isLt
  · change (q (Fin.natAdd m p)).val = n
    rw [skewValLow]
    simp [p]

/-- Exact product of the high tracked and low untracked factors in the
    middle-column branch when its third column is nonempty. -/
noncomputable def middleSliceEquiv (m n : ℕ) :
    MiddleSlice m n ≃ Rule9Target m × LowPlaced n := by
  refine (Equiv.ofBijective combineMiddle ?_).symm
  constructor
  · rintro ⟨⟨⟨σ,cuts⟩,hσ⟩,a,τ,hτ⟩ ⟨⟨⟨σ',cuts'⟩,hσ'⟩,b,τ',hτ'⟩ he
    have hh : skewSum σ τ.val = skewSum σ' τ'.val :=
      congrArg (fun x : MiddleSlice m n => x.val.val.1) he
    have h₁ : cuts.val.1.val = cuts'.val.1.val :=
      congrArg (fun x : MiddleSlice m n => x.val.val.2.left.val) he
    have h₂ : cuts.val.2.val = cuts'.val.2.val :=
      congrArg (fun x : MiddleSlice m n => x.val.val.2.center.val) he
    have hh' : m+a.val = m+b.val :=
      congrArg (fun x : MiddleSlice m n => x.val.val.2.right.val) he
    have hab : a=b := Fin.ext (by omega)
    subst b
    have eCuts : cuts=cuts' := Subtype.ext (Prod.ext (Fin.ext h₁) (Fin.ext h₂))
    have hh'' := skew_injective hh
    exact Prod.ext (Subtype.ext (Prod.ext hh''.1 eCuts))
      (Sigma.ext rfl (heq_of_eq (Subtype.ext (Subtype.ext hh''.2))))
  · rintro ⟨⟨⟨σ,cuts⟩,hh⟩,p,hp,hr⟩
    have hs := middleHighCut σ cuts.hlc cuts.hcr hh hp.1 hp.2
    dsimp only at hs
    rw [hr,show m+(n+1)-1-n=m by omega] at hs
    let high := (leftBlock hs.1).trans Fin.revPerm
    let low := (rightBlock hs.1).trans Fin.revPerm
    have hskew : skewSum high low = σ := skewSplit_of_complementCut hs.1
    let a : Fin (m+1) := ⟨cuts.left.val,Nat.lt_succ_of_le
      ((show cuts.left.val ≤ cuts.center.val from cuts.hlc).trans hs.2.1)⟩
    let b : Fin (m+1) := ⟨cuts.center.val,Nat.lt_succ_of_le hs.2.1⟩
    let c : Fin (n+2) := ⟨cuts.right.val-m,by have := cuts.right.isLt; omega⟩
    have hc : m+c.val = cuts.right.val := by change m+(cuts.right.val-m)=_; omega
    have ha : avoidsGrid high (cols3 a.val b.val) trackedBasis ∧ PermPalPlacementCondition low c := by
      apply (middleSkew_product_iff high low a b c).mp
      rw [hskew,hc]
      exact hh
    have hmp : m ≤ p.val := hs.2.2.trans hp.1
    let i : Fin (n+1) := ⟨p.val-m,by have := p.isLt; omega⟩
    have hei : Fin.natAdd m i = p := Fin.ext (by dsimp [i]; omega)
    have hvi : low i = Fin.last n := by
      apply Fin.ext
      change (low i).val = n
      rwa [← skewValLow high low i,hskew,hei]
    have hi : low.symm (Fin.last n) = i := by rw [← hvi,Equiv.symm_apply_apply]
    have hd : c.val ≤ (low.symm (Fin.last n)).val := by
      rw [hi]
      change cuts.right.val-m ≤ p.val-m
      exact Nat.sub_le_sub_right hp.1 m
    refine ⟨⟨⟨⟨high,⟨⟨a,b⟩,cuts.hlc⟩⟩,ha.1⟩,c,⟨low,ha.2⟩,hd⟩,?_⟩
    apply middleSlice_ext
    · exact hskew
    · exact Fin.ext rfl
    · exact Fin.ext rfl
    · exact Fin.ext hc

theorem middleSlice_tracker {m n : ℕ} (x : Rule9Target m × LowPlaced n) :
    ((middleSliceEquiv m n).symm x).val.val.2.left.val = x.1.val.first := by
  rcases x with ⟨⟨⟨σ,cuts⟩,hσ⟩,a,τ,hτ⟩
  rcases cuts with ⟨⟨l,r⟩,h⟩
  rcases τ with ⟨τ,hτ'⟩
  rfl

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4

abbrev MiddleMaximum (n : ℕ) :=
  {q : Rule9Target (n+1) // q.val.first ≤ (q.val.1.symm (Fin.last n)).val ∧
    (q.val.1.symm (Fin.last n)).val < q.val.second}

instance (n : ℕ) : Finite (MiddleCuts n) := by
  apply Finite.of_injective (fun x : MiddleCuts n => (x.left,x.center,x.right))
  rintro ⟨a,b,c,h,k⟩ ⟨a',b',c',h',k'⟩ he
  obtain ⟨ha,⟨hb,hc⟩⟩ := Prod.ext_iff.mp he |>.imp_right Prod.ext_iff.mp
  dsimp only at ha hb hc

  subst a'; subst b'; subst c'
  rfl

noncomputable instance (n : ℕ) : Fintype (MiddleClass n) := Fintype.ofFinite _
noncomputable instance (n : ℕ) : Fintype (MiddleMaximum n) := Fintype.ofFinite _

private def insertMiddleMaximum {n : ℕ} (s : MiddleClass n) : MiddleMaximum n := by
  rcases s with ⟨⟨σ, a,c,b,hac,hcb⟩,hs⟩
  have h : avoidsGrid (placeMaximum c σ) (cols3 a.val (b.val+1)) trackedBasis :=
    (maximumMiddle_avoids_iff hac hcb σ).mpr hs
  have hcut : a.castSucc ≤ b.succ := Nat.le_succ_of_le (hac.trans hcb)
  refine ⟨⟨⟨placeMaximum c σ,⟨⟨a.castSucc,b.succ⟩,hcut⟩⟩,h⟩,?_⟩
  change a.val ≤ ((placeMaximum c σ).symm (Fin.last n)).val ∧
    ((placeMaximum c σ).symm (Fin.last n)).val < b.val+1
  rw [inverse_placeMaximum_peak]
  exact ⟨hac,Nat.lt_succ_of_le hcb⟩

/-- Deleting a middle-column maximum is exactly PermPAL's remaining
    four-column class, with the left-column tracker unchanged. -/
noncomputable def middleMaximumEquiv (n : ℕ) : MiddleClass n ≃ MiddleMaximum n := by
  refine Equiv.ofBijective insertMiddleMaximum ?_
  constructor
  · rintro ⟨⟨σ,a,c,b,hac,hcb⟩,hs⟩ ⟨⟨σ',a',c',b',hac',hcb'⟩,hs'⟩ he
    have hσ : placeMaximum c σ = placeMaximum c' σ' :=
      congrArg (fun z : MiddleMaximum n => z.val.val.1) he
    have ha : a.val=a'.val :=
      congrArg (fun z : MiddleMaximum n => z.val.val.first) he
    have hb : b.val+1=b'.val+1 :=
      congrArg (fun z : MiddleMaximum n => z.val.val.second) he
    have hcc : c=c' := by
      simpa only [inverse_placeMaximum_peak] using
        congrArg (fun p : Equiv.Perm (Fin (n+1)) => p.symm (Fin.last n)) hσ
    have haa : a=a' := Fin.ext ha
    have hbb : b=b' := Fin.ext (by omega)
    subst c'; subst a'; subst b'
    have hσ' := placeMaximum_injective _ hσ
    subst σ'
    rfl
  · rintro ⟨⟨⟨σ,⟨left,right⟩,hcut⟩,ha⟩,⟨hl,hr⟩⟩
    let c := σ.symm (Fin.last n)
    let a : Fin (n+1) := ⟨left.val,lt_of_le_of_lt (show left.val ≤ c.val from hl) c.isLt⟩
    let b : Fin (n+1) := ⟨right.val-1,by have := right.isLt; omega⟩
    have hbr : b.val+1 = right.val := by
      have hr' : c.val < right.val := hr
      change right.val-1+1 = right.val
      omega
    let π := deleteMaximum σ
    have hσ : placeMaximum c π = σ := placeMaximum_deleteMaximum _
    have hac : a ≤ c := hl
    have hcb : c ≤ b := by
      change c.val ≤ right.val-1
      have hr' : c.val < right.val := hr
      omega
    have hh : avoidsGrid π (cols4 a.val c.val b.val) middleBasis := by
      apply (maximumMiddle_avoids_iff hac hcb π).mp
      rw [hσ,hbr]
      exact ha
    refine ⟨⟨⟨π,⟨a,c,b,hac,hcb⟩⟩,hh⟩,?_⟩
    exact Subtype.ext (Subtype.ext (Prod.ext hσ (Subtype.ext (Prod.ext (Fin.ext rfl) (Fin.ext hbr)))))

theorem middleMaximum_tracker {n : ℕ} (s : MiddleClass n) :
    (middleMaximumEquiv n s).val.val.first = s.val.2.left.val := by
  rcases s with ⟨⟨p,cuts⟩,hs⟩
  rcases cuts with ⟨a,c,b,hac,hcb⟩
  rfl

abbrev EmptyMiddle (n : ℕ) := {s : MiddleClass n // s.val.2.right = Fin.last n}

noncomputable instance (n : ℕ) : Fintype (EmptyMiddle n) := Fintype.ofFinite _

/-- Empty-right middle objects are exactly fused tracked objects. -/
def emptyMiddleEquiv (n : ℕ) : Rule9Target n ≃ EmptyMiddle n where
  toFun x :=
    ⟨⟨⟨x.val.1,⟨x.val.2.val.1,x.val.2.val.2,Fin.last n,x.val.2.property,Fin.le_last _⟩⟩,
      (middle_emptyRight_avoids_iff _ _ _).mpr x.property⟩,rfl⟩
  invFun x :=
    ⟨⟨x.val.val.1,⟨(x.val.val.2.left,x.val.val.2.center),x.val.val.2.hlc⟩⟩,
      (middle_emptyRight_avoids_iff _ _ _).mp (by
        have hh := x.val.property
        rw [x.property] at hh
        exact hh)⟩
  left_inv x := rfl
  right_inv x := by
    rcases x with ⟨⟨⟨p,a,b,c,hab,hbc⟩,h⟩,hc⟩
    change c = Fin.last n at hc
    subst c
    rfl

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4 OMA.S_oeis_a001764

noncomputable def trackedWeight {R : Type*} [CommRing R] (k : R) (n : ℕ) : R :=
  ∑ q : Rule9Target n, k^q.val.first

abbrev LeftMaximum (n : ℕ) :=
  {q : Rule9Target (n+1) // (q.val.1.symm (Fin.last n)).val < q.val.first}

noncomputable instance (n : ℕ) : Fintype (LeftMaximum n) := Fintype.ofFinite _

private abbrev LeftAt (s m : ℕ) (h : 0<s) :=
  {q : Rule9Target s // (maxPos q.val.1 h).val = m ∧ m < q.val.first}

private noncomputable instance (s m : ℕ) (h : 0<s) : Fintype (LeftAt s m h) :=
  Fintype.ofFinite _

private noncomputable def leftRank {n : ℕ} (x : LeftMaximum n) : Fin (n+1) :=
  x.val.val.1.symm (Fin.last n)

private def leftAtEquiv {n : ℕ} (r : Fin (n+1)) :
    {q : LeftMaximum n // leftRank q = r} ≃ LeftAt (n+1) r.val (by omega) where
  toFun x := ⟨x.val.val,congrArg Fin.val x.property,by
    rw [← congrArg Fin.val x.property]
    exact x.val.property⟩
  invFun x := ⟨⟨x.val, by
    change (maxPos x.val.val.1 (by omega)).val < x.val.val.first
    rw [x.property.1]
    exact x.property.2⟩,Fin.ext x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def leftAtWeight {R : Type*} [CommRing R] (k : R)
    (s m : ℕ) (h : 0<s) : R :=
  ∑ q : LeftAt s m h, k^q.val.val.first

private theorem leftAtWeight_congr {R : Type*} [CommRing R] (k : R)
    {s t m : ℕ} (h : 0<s) (h' : 0<t) (e : s=t) :
    leftAtWeight k s m h = leftAtWeight k t m h' := by cases e; rfl

private noncomputable instance (m : ℕ) : Fintype (CatalanPlot m) := Fintype.ofFinite _

private theorem catalanPlot_card (n : ℕ) : Nat.card (CatalanPlot n) = catalan n := by
  rw [← catalanBlock_card n]
  let rev : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) :=
    ⟨reversePermutation,reversePermutation,reversePermutation_involutive n,
      reversePermutation_involutive n⟩
  refine Nat.card_congr (Equiv.subtypeEquiv rev (fun σ => ?_))
  change Avoids σ ![0,2,1] ↔ Low231 (reversePermutation σ) n
  rw [low231_exact,← reverseAvoids σ (![0,2,1] : Fin 3 → ℕ)]
  have hr : ∀ i j : Fin 3, (![0,2,1] : Fin 3 → ℕ) i.rev < ![0,2,1] j.rev ↔
      (![2,3,1] : Fin 3 → ℕ) i < ![2,3,1] j := by decide
  simp only [Avoids,hr]

private theorem leftSlice_sum {R : Type*} [CommRing R] (k : R) (m n : ℕ) :
    leftAtWeight k (m+1+n) m (by omega) = (catalan m : R) * k^(m+1) * trackedWeight k n := by
  classical
  let e := (leftSliceEquiv m n).symm
  have h : (∑ x : CatalanPlot m × Rule9Target n, k^(m+1+x.2.val.first)) =
      leftAtWeight k (m+1+n) m (by omega) := by
    apply Fintype.sum_equiv e
    intro x
    rw [leftSlice_tracker]
  rw [← h, Fintype.sum_prod_type]
  have hg : (∑ q : Rule9Target n, k^(m+1+q.val.first)) =
      k^(m+1) * (∑ q : Rule9Target n, k^q.val.first) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_add]
  simp_rw [hg]
  unfold trackedWeight
  have hc : (∑ _ : CatalanPlot m, k^(m+1) * (∑ q : Rule9Target n, k^q.val.first)) =
      (Nat.card (CatalanPlot m) : R) * (k^(m+1) * (∑ q : Rule9Target n, k^q.val.first)) := by
    simp [Nat.card_eq_fintype_card, nsmul_eq_mul]
  simpa only [catalanPlot_card,mul_assoc] using hc

theorem leftMaximum_sum {R : Type*} [CommRing R] (k : R) (n : ℕ) :
    (∑ x : LeftMaximum n, k^x.val.val.first) =
      ∑ r : Fin (n+1), (catalan r.val : R) * k^(r.val+1) * trackedWeight k (n-r.val) := by
  classical
  have hs : (∑ x : LeftMaximum n, k^x.val.val.first) =
      ∑ r : Fin (n+1), leftAtWeight k (n+1) r.val (by omega) := by
    calc
      _ = ∑ s : (Σ r : Fin (n+1), {x : LeftMaximum n // leftRank x=r}), k^s.2.val.val.val.first :=
        Fintype.sum_equiv (Equiv.sigmaFiberEquiv leftRank).symm _ _ (by intro x; rfl)
      _ = ∑ r : Fin (n+1), ∑ q : {x : LeftMaximum n // leftRank x=r}, k^q.val.val.val.first :=
        Fintype.sum_sigma _
      _ = _ := Finset.sum_congr rfl (fun r _ => Fintype.sum_equiv (leftAtEquiv r) _ _ (by intro x; rfl))
  rw [hs]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = leftAtWeight k (r.val+1+(n-r.val)) r.val (by omega) :=
      leftAtWeight_congr k _ _ (show n+1 = r.val+1+(n-r.val) by have := r.isLt; omega)
    _ = _ := leftSlice_sum k r.val (n-r.val)

abbrev NonemptyMiddle (n : ℕ) := {s : MiddleClass n // s.val.2.right ≠ Fin.last n}

private noncomputable instance (n : ℕ) : Fintype (NonemptyMiddle n) := Fintype.ofFinite _

private theorem mRightNonempty {n : ℕ} (s : NonemptyMiddle n) :
    s.val.val.2.right.val < n := by
  have h : s.val.val.2.right ≠ Fin.last n := s.property
  have hne : s.val.val.2.right.val ≠ n := fun he => h (Fin.ext he)
  have := s.val.val.2.right.isLt
  omega

private noncomputable def mPeak {n : ℕ} (s : NonemptyMiddle n) : Fin n :=
  Classical.choose (rightPeak_exists s.val.val.1 _ (mRightNonempty s))

private theorem mPeak_spec {n : ℕ} (s : NonemptyMiddle n) :
    RightPeak s.val.val.1 s.val.val.2.right (mPeak s) :=
  Classical.choose_spec (rightPeak_exists s.val.val.1 _ (mRightNonempty s))

private abbrev MiddleAt (n r : ℕ) :=
  {s : MiddleClass n // ∃ p : Fin n, RightPeak s.val.1 s.val.2.right p ∧
    (s.val.1 p).val = r}

private noncomputable instance (n r : ℕ) : Fintype (MiddleAt n r) := Fintype.ofFinite _

private noncomputable def mRank {n : ℕ} (s : NonemptyMiddle n) : Fin n := s.val.val.1 (mPeak s)

private noncomputable def middleAtEquiv {n : ℕ} (r : Fin n) :
    {q : NonemptyMiddle n // mRank q = r} ≃ MiddleAt n r.val := by
  refine Equiv.ofBijective (fun q => ⟨q.val.val,mPeak q.val,mPeak_spec q.val,
    congrArg Fin.val q.property⟩) ?_
  constructor
  · intro q q' he
    have h := congrArg (fun x : MiddleAt n r.val => x.val) he
    exact Subtype.ext (Subtype.ext h)
  · rintro ⟨s,p,hp,hr⟩
    have hne : s.val.2.right ≠ Fin.last n := fun e => by
      have hh := hp.1
      rw [e] at hh
      exact (Nat.not_le_of_lt p.isLt) hh
    let x : NonemptyMiddle n := ⟨s,hne⟩
    have e := rightPeak_unique s.val.1 s.val.2.right (mPeak_spec x) hp
    have hh : mRank x = r := Fin.ext (by
      change (s.val.1 (mPeak x)).val = r.val
      rwa [e])
    exact ⟨⟨x,hh⟩,rfl⟩

private noncomputable def middleAtWeight {R : Type*} [CommRing R] (k : R) (s r : ℕ) : R :=
  ∑ q : MiddleAt s r, k^q.val.val.2.left.val

private theorem middleAtWeight_congr {R : Type*} [CommRing R] (k : R)
    {s t r : ℕ} (e : s=t) : middleAtWeight k s r = middleAtWeight k t r := by cases e; rfl

private noncomputable instance (n : ℕ) : Fintype (LowPlaced n) := Fintype.ofFinite _

private theorem middleSlice_sum {R : Type*} [CommRing R] (k : R) (m n : ℕ) :
    middleAtWeight k (m+(n+1)) n = trackedWeight k m * (Nat.card (Rule9Target n) : R) := by
  classical
  let e := (middleSliceEquiv m n).symm
  have h : (∑ x : Rule9Target m × LowPlaced n, k^x.1.val.first) =
      middleAtWeight k (m+(n+1)) n := by
    apply Fintype.sum_equiv e
    intro x
    rw [middleSlice_tracker]
  rw [← h, Fintype.sum_prod_type]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [← Finset.mul_sum,← Nat.card_eq_fintype_card (α := LowPlaced n),
    Nat.card_congr (lowPlacedEquiv n),mul_comm]
  rfl

theorem middleNonempty_sum {R : Type*} [CommRing R] (k : R) (n : ℕ) :
    (∑ x : NonemptyMiddle (n+1), k^x.val.val.2.left.val) =
      ∑ i : Fin (n+1), trackedWeight k (n-i.val) * (Nat.card (Rule9Target i.val) : R) := by
  classical
  have hs : (∑ x : NonemptyMiddle (n+1), k^x.val.val.2.left.val) =
      ∑ r : Fin (n+1), middleAtWeight k (n+1) r.val := by
    calc
      _ = ∑ x : (Σ r : Fin (n+1),{x : NonemptyMiddle (n+1) // mRank x=r}), k^x.2.val.val.val.2.left.val :=
        Fintype.sum_equiv (Equiv.sigmaFiberEquiv mRank).symm _ _ (by intro x; rfl)
      _ = ∑ r : Fin (n+1), ∑ x : {x : NonemptyMiddle (n+1) // mRank x=r}, k^x.val.val.val.2.left.val :=
        Fintype.sum_sigma _
      _ = _ := Finset.sum_congr rfl (fun r _ => Fintype.sum_equiv (middleAtEquiv r) _ _ (by intro x; rfl))
  rw [hs]
  apply Finset.sum_congr rfl
  intro r _
  rw [middleAtWeight_congr k (show n+1 = (n-r.val)+(r.val+1) by have := r.isLt; omega),
    middleSlice_sum]

private theorem middleClass_decompose {R : Type*} [CommRing R] (k : R) (n : ℕ) :
    (∑ x : MiddleClass n, k^x.val.2.left.val) =
      trackedWeight k n + ∑ x : NonemptyMiddle n, k^x.val.val.2.left.val := by
  classical
  let e := Equiv.sumCompl (fun x : MiddleClass n => x.val.2.right = Fin.last n)
  have hs : (∑ x : EmptyMiddle n ⊕ NonemptyMiddle n,
      Sum.elim (fun x : EmptyMiddle n => k^x.val.val.2.left.val)
        (fun x : NonemptyMiddle n => k^x.val.val.2.left.val) x) =
      ∑ x : MiddleClass n, k^x.val.2.left.val := by
    apply Fintype.sum_equiv e
    intro x
    rcases x with x | x <;> rfl
  rw [← hs, Fintype.sum_sum_type]
  congr 1
  exact Fintype.sum_equiv (emptyMiddleEquiv n).symm _ _ (fun _ => rfl)

private theorem middleMaximum_sum {R : Type*} [CommRing R] (k : R) (n : ℕ) :
    (∑ x : MiddleMaximum n, k^x.val.val.first) =
      trackedWeight k n + ∑ x : NonemptyMiddle n, k^x.val.val.2.left.val := by
  rw [← Fintype.sum_equiv (middleMaximumEquiv n)
    (fun x => k^x.val.2.left.val) (fun x => k^x.val.val.first)
    (fun x => by rw [middleMaximum_tracker])]
  exact middleClass_decompose k n

private def maxTrichotomyEquiv (n : ℕ) :
    LeftMaximum n ⊕ MiddleMaximum n ⊕ RightMaximum n ≃ Rule9Target (n+1) where
  toFun := Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val)
  invFun q :=
    if hl : (q.val.1.symm (Fin.last n)).val < q.val.first then .inl ⟨q,hl⟩
    else if hr : (q.val.1.symm (Fin.last n)).val < q.val.second then
      .inr (.inl ⟨q,Nat.le_of_not_gt hl,hr⟩)
    else .inr (.inr ⟨q,Nat.le_of_not_gt hr⟩)
  left_inv s := by
    rcases s with s | s | s
    · dsimp only
      split
      · rfl
      · rename_i hn
        exact (hn s.property).elim
    · dsimp only
      split
      · rename_i hm
        exact (not_lt_of_ge s.property.1 hm).elim
      · split
        · rfl
        · rename_i hn
          exact (hn s.property.2).elim
    · have h : s.val.val.first ≤ s.val.val.second := s.val.val.2.property
      dsimp only
      split
      · rename_i hm
        exact (not_lt_of_ge (h.trans s.property) hm).elim
      · split
        · rename_i hm
          exact (not_lt_of_ge s.property hm).elim
        · rfl
  right_inv s := by
    dsimp only
    split
    · rfl
    · split <;> rfl

private theorem trackedWeight_decompose {R : Type*} [CommRing R] (k : R) (n : ℕ) :
    trackedWeight k (n+1) = (∑ x : LeftMaximum n, k^x.val.val.first) +
      (∑ x : MiddleMaximum n, k^x.val.val.first) + ∑ x : RightMaximum n, k^x.val.val.first := by
  classical
  have h : (∑ x : LeftMaximum n ⊕ MiddleMaximum n ⊕ RightMaximum n,
      Sum.elim (fun x : LeftMaximum n => k^x.val.val.first)
        (Sum.elim (fun x : MiddleMaximum n => k^x.val.val.first)
          (fun x : RightMaximum n => k^x.val.val.first)) x) = trackedWeight k (n+1) := by
    apply Fintype.sum_equiv (maxTrichotomyEquiv n)
    intro x
    rcases x with x | x | x <;> rfl
  rw [← h,Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp [add_assoc]

/-- The full weighted coefficient recurrence, after clearing the geometric
    factor k−1 from the tracked fusion term. -/
theorem trackedWeight_succ {R : Type*} [CommRing R] (k : R) (n : ℕ) :
    (k-1)*(trackedWeight k (n+1) - trackedWeight k n -
      (∑ x : NonemptyMiddle n, k^x.val.val.2.left.val) -
      ∑ r : Fin (n+1), (catalan r.val : R) * k^(r.val+1) * trackedWeight k (n-r.val)) =
      k * trackedWeight k n - (Nat.card (Rule9Target n) : R) := by
  calc
    _ = (k-1) * (∑ x : RightMaximum n, k^x.val.val.first) := by
      rw [trackedWeight_decompose,leftMaximum_sum,middleMaximum_sum]
      ring
    _ = _ := rightMaximum_weighted_sum k n

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4 PowerSeries

abbrev Inner := PowerSeries ℤ
abbrev Outer := PowerSeries Inner

noncomputable abbrev mkY : Inner := 1+X
noncomputable abbrev gSeries : Outer := PowerSeries.mk (trackedWeight mkY)
noncomputable abbrev hSeries : Outer := PowerSeries.map PowerSeries.C trackedUnweighted
noncomputable def catSeries : Outer :=
  PowerSeries.rescale mkY (PowerSeries.map PowerSeries.C catZ)

private theorem trackedWeight_zero {R : Type*} [CommRing R] (k : R) :
    trackedWeight k 0 = 1 := by
  classical
  let c : Cuts 0 := ⟨(0,0),le_rfl⟩
  let empty : Rule9Target 0 := ⟨⟨Equiv.refl _,c⟩,by
    intro p hp ⟨e,_,_,_⟩
    have hpos : 0 < p.size := by
      simp only [trackedBasis,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide
    exact (e ⟨0,hpos⟩).elim0⟩
  letI : Unique (Rule9Target 0) := ⟨⟨empty⟩,fun x => by
    apply Subtype.ext
    apply Prod.ext
    · ext i
      exact i.elim0
    · apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> have h := x.val.2.val.1.isLt <;>
        have h' := x.val.2.val.2.isLt <;> change _ = 0 <;> omega⟩
  rw [trackedWeight,Fintype.sum_unique]
  change k^0 = 1
  simp

private theorem uncovered_zero {R : Type*} [CommRing R] (k : R) :
    ∑ x : NonemptyMiddle 0, k^x.val.val.2.left.val = 0 := by
  classical
  letI : IsEmpty (NonemptyMiddle 0) := ⟨fun x => x.property (Fin.ext (by
    change x.val.val.2.right.val = 0
    have h := x.val.val.2.right.isLt
    omega))⟩
  simp

theorem catSeries_identity :
    catSeries = 1 + (X : Outer)*PowerSeries.C mkY*catSeries^2 := by
  have he : catZ ^ 2 * (X : Inner) + 1 = catZ := by
    unfold catZ
    simpa only [map_pow,map_mul,PowerSeries.map_X,map_add,map_one] using
      congrArg (PowerSeries.map (Nat.castRingHom ℤ)) catalanSeries_sq_mul_X_add_one
  let f : Inner →+* Outer := (PowerSeries.rescale mkY).comp (PowerSeries.map PowerSeries.C)
  have hfcat : f catZ = catSeries := rfl
  have hfx : f X = PowerSeries.C mkY * X := by
    dsimp [f]
    rw [PowerSeries.map_X,PowerSeries.rescale_X]
  have h : f (catZ^2*X+1) = f catZ := congrArg f he
  rw [map_add,map_mul,map_pow,map_one,hfcat,hfx] at h
  calc
    catSeries = catSeries^2*(PowerSeries.C mkY*(X : Outer))+1 := h.symm
    _ = _ := by ac_rfl

private theorem coeffCatSeries (n : ℕ) :
    coeff n catSeries = mkY^n * (catalan n : Inner) := by
  rw [catSeries,PowerSeries.coeff_rescale,PowerSeries.coeff_map,catZ,PowerSeries.coeff_map,
    PowerSeries.catalanSeries_coeff]
  simp

private theorem coeffHSeries (n : ℕ) :
    coeff n hSeries = (Nat.card (Rule9Target n) : Inner) := by
  rw [PowerSeries.coeff_map,trackedUnweighted,coeff_mk]
  simp

private theorem coeffMiddle (n : ℕ) :
    coeff (n+1) ((X : Outer)^2 * (gSeries*hSeries)) =
      ∑ x : NonemptyMiddle n, mkY^x.val.val.2.left.val := by
  cases n with
  | zero => rw [uncovered_zero]; simp [PowerSeries.coeff_X_pow_mul']
  | succ n =>
    change coeff (n+2) _ = _
    rw [PowerSeries.coeff_X_pow_mul,
      PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      middleNonempty_sum,← Fin.sum_univ_eq_sum_range]
    simp only [gSeries,PowerSeries.coeff_mk,coeffHSeries]
    apply Fintype.sum_equiv Fin.revPerm
    intro i
    have h1 : (Fin.revPerm i).val = n-i.val := by simp only [Fin.revPerm_apply,Fin.val_rev]; omega
    have h2 : n - (Fin.revPerm i).val = i.val := by rw [h1]; have := i.isLt; omega
    rw [h2,h1]

private theorem coeffLeft (n : ℕ) :
    coeff (n+1) ((X : Outer) * (PowerSeries.C mkY * (catSeries*gSeries))) =
      ∑ r : Fin (n+1), (catalan r.val : Inner) * mkY^(r.val+1) * trackedWeight mkY (n-r.val) := by
  rw [coeff_succ_X_mul,PowerSeries.coeff_C_mul,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,← Fin.sum_univ_eq_sum_range,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp only [coeffCatSeries,gSeries,PowerSeries.coeff_mk,pow_succ]
  ring

/-- Actual bivariate PermPAL specification after multiplication by y−1.
    The inner series uses y=1+z to permit a formal substitution y=k
    with constant coefficient one. -/
theorem verified_tracked_series :
    PowerSeries.C (mkY-1) *
      (gSeries - 1 - (X : Outer)*gSeries - X^2*(gSeries*hSeries)
        - X*(PowerSeries.C mkY*(catSeries*gSeries))) =
    (X : Outer)*(PowerSeries.C mkY*gSeries-hSeries) := by
  apply PowerSeries.ext
  intro d
  cases d with
  | zero =>
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    have h := trackedWeight_zero mkY
    simp only [gSeries, ← PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.coeff_mk,h,sub_self,mul_zero]
  | succ n =>
    rw [PowerSeries.coeff_C_mul,map_sub,map_sub,map_sub,map_sub,coeff_one,
      if_neg (Nat.succ_ne_zero _),sub_zero,coeff_succ_X_mul,coeffMiddle,coeffLeft,
      coeff_succ_X_mul,map_sub,PowerSeries.coeff_C_mul,coeffHSeries]
    simpa only [gSeries,PowerSeries.coeff_mk] using trackedWeight_succ mkY n

end A001764.Round5

end

section

namespace A001764.Round5
open A001764.Round4 PowerSeries

private abbrev Biv := MvPowerSeries (Option Unit) ℤ
private noncomputable abbrev nested := MvPowerSeries.optionEquivLeft Unit ℤ

private def someEmbed : Unit ↪ Option Unit := ⟨Option.some,Option.some_injective _⟩
private def noneEmbed : Unit ↪ Option Unit := ⟨fun _ => none,fun a b _ => Subsingleton.elim a b⟩

private theorem nested_some (f : PowerSeries ℤ) :
    nested (MvPowerSeries.rename (fun u : Unit => some u) f) = PowerSeries.C f := by
  ext q i
  change MvPowerSeries.coeff (Finsupp.single () i) (PowerSeries.coeff q
    (nested (MvPowerSeries.rename (fun u : Unit => some u) f))) =
    PowerSeries.coeff i (PowerSeries.coeff q (PowerSeries.C f))
  rw [MvPowerSeries.coeff_coeff_optionEquivLeft,PowerSeries.coeff_C]
  by_cases hq : q = 0
  · subst q
    rw [if_pos rfl]
    have h : (Finsupp.single () i).optionElim 0 =
      Finsupp.embDomain someEmbed (Finsupp.single () i) := by
      ext u; cases u with
      | none => simp [someEmbed]
      | some u => cases u; simp [someEmbed]
    change MvPowerSeries.coeff _ (MvPowerSeries.rename someEmbed f) = _
    rw [h,MvPowerSeries.coeff_embDomain_rename]
    rfl
  · rw [if_neg hq,map_zero]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨v,hv⟩
    have h := congrArg (fun w : Option Unit →₀ ℕ => w none) hv
    change Finsupp.mapDomain someEmbed v none = _ at h
    rw [← Finsupp.embDomain_eq_mapDomain] at h
    exact hq (by simpa [someEmbed,Finsupp.embDomain_apply] using h.symm)

private theorem nested_none (f : PowerSeries ℤ) :
    nested (MvPowerSeries.rename (fun _ : Unit => none) f) = PowerSeries.map PowerSeries.C f := by
  ext q i
  change MvPowerSeries.coeff (Finsupp.single () i) (PowerSeries.coeff q
    (nested (MvPowerSeries.rename (fun _ : Unit => none) f))) =
    PowerSeries.coeff i (PowerSeries.coeff q (PowerSeries.map PowerSeries.C f))
  rw [MvPowerSeries.coeff_coeff_optionEquivLeft,PowerSeries.coeff_map,PowerSeries.coeff_C]
  by_cases hi : i = 0
  · subst i
    rw [if_pos rfl]
    have h : (Finsupp.single () 0).optionElim q =
      Finsupp.embDomain noneEmbed (Finsupp.single () q) := by
      ext u
      cases u with
      | none =>
        rw [Finsupp.optionElim_apply_none]
        change q = Finsupp.embDomain noneEmbed (Finsupp.single () q) (noneEmbed ())
        rw [Finsupp.embDomain_apply_self,Finsupp.single_eq_same]
      | some u => cases u; simp [noneEmbed]
    change MvPowerSeries.coeff _ (MvPowerSeries.rename noneEmbed f) = _
    rw [h,MvPowerSeries.coeff_embDomain_rename]
    rfl
  · rw [if_neg hi]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨v,hv⟩
    have h := congrArg (fun w : Option Unit →₀ ℕ => w (some ())) hv
    change Finsupp.mapDomain noneEmbed v (some ()) = _ at h
    rw [← Finsupp.embDomain_eq_mapDomain] at h
    exact hi (by simpa [noneEmbed,Finsupp.embDomain_apply] using h.symm)

private theorem subst_rename_one {f : Unit → Option Unit}
    {a : Option Unit → PowerSeries ℤ} (ha : MvPowerSeries.HasSubst a) (p : PowerSeries ℤ) :
    MvPowerSeries.substAlgHom ha (MvPowerSeries.rename f p) = PowerSeries.subst (a (f ())) p := by
  rw [MvPowerSeries.coe_substAlgHom,MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp (R := ℤ) (f := f)) ha]
  unfold PowerSeries.subst
  congr 1
  funext u
  cases u
  simp [MvPowerSeries.subst_X ha]

set_option maxHeartbeats 800000 in
/-- The actual class equations, specialized at the ternary parameter,
    give the published PermPAL cubic without a separate kernel-root existence argument. -/
theorem permPal_cubic_exact : A001764.PermPalCubic := by
  obtain ⟨k,hk,_⟩ := exists_ternary_parameter
  have hc₁ : (PowerSeries.constantCoeff k : ℤ) = 1 := by
    have h := congrArg (PowerSeries.constantCoeff (R := ℤ)) hk
    simpa [PowerSeries.constantCoeff_X] using h
  let a : Option Unit → PowerSeries ℤ := fun s => s.elim X (fun _ => k-1)
  have ha : MvPowerSeries.HasSubst a :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by
      change constantCoeff (a s) = 0
      cases s <;> simp [a,hc₁,PowerSeries.constantCoeff_X])
  let ev : Biv →ₐ[ℤ] PowerSeries ℤ := MvPowerSeries.substAlgHom ha
  let g : Biv := nested.symm gSeries
  let c : Biv := nested.symm catSeries
  let x : Biv := MvPowerSeries.rename (fun _ : Unit => none) (X : Inner)
  let y : Biv := MvPowerSeries.rename (fun u : Unit => some u) mkY
  let h : Biv := MvPowerSeries.rename (fun _ : Unit => none) trackedUnweighted
  have hG : (y-1)*(g-1-x*g-x^2*(g*h)-x*(y*(c*g))) = x*(y*g-h) := by
    apply nested.injective
    simpa [g,h,c,x,y,hSeries,nested_some,nested_none,PowerSeries.map_X,
      map_sub,map_mul,map_pow,map_one] using verified_tracked_series
  have hC : c = 1 + x*y*c^2 := by
    apply nested.injective
    simpa [c,x,y,nested_some,nested_none,PowerSeries.map_X,map_add,map_mul,map_pow,map_one]
      using catSeries_identity
  have hX : ev x = X := by
    rw [show ev x = PowerSeries.subst X X from subst_rename_one ha X]
    simp
  have hY : ev y = k := by
    rw [show ev y = PowerSeries.subst (k-1) mkY from subst_rename_one ha mkY]
    have hpos : PowerSeries.HasSubst (k-1) := by
      apply PowerSeries.HasSubst.of_constantCoeff_zero'
      simp [hc₁]
    change PowerSeries.subst (k-1) (1+X : Inner) = k
    rw [← PowerSeries.coe_substAlgHom hpos,map_add,map_one,PowerSeries.substAlgHom_X]
    abel
  have hH : ev h = trackedUnweighted := by
    rw [show ev h = PowerSeries.subst X trackedUnweighted from subst_rename_one ha trackedUnweighted]
    exact PowerSeries.X_subst _
  have hCe : ev c = 1 + X*k*(ev c)^2 := by
    simpa only [map_add,map_mul,map_pow,map_one,hX,hY] using congrArg ev hC
  have hcek : ev c = k := by
    have hDis : (ev c-k)*(1-X*k*(ev c+k)) = 0 := by
      linear_combination hCe-hk
    have hUnit : 1-X*k*(ev c+k) ≠ 0 := by
      intro he
      have hh := congrArg (PowerSeries.constantCoeff (R := ℤ)) he
      simp [PowerSeries.constantCoeff_X] at hh
    exact sub_eq_zero.mp ((mul_eq_zero.mp hDis).resolve_right hUnit)
  have hGe : (k-1)*(ev g-1-X*ev g-X^2*(ev g*trackedUnweighted)-
      X*(k*(k*ev g))) = X*(k*ev g-trackedUnweighted) := by
    simpa only [map_sub,map_mul,map_pow,map_one,hX,hY,hH,hcek] using congrArg ev hG
  have hKer : ((k-1)*(1-X-X^2*trackedUnweighted-X*k^2)-X*k)*ev g =
      k-1-X*trackedUnweighted := by linear_combination hGe
  have hKernelShape : (k-1)*(1-X-X^2*trackedUnweighted-X*k^2)-X*k =
      X*(k-1)*(k-1-X*trackedUnweighted) := by linear_combination hk
  rw [hKernelShape] at hKer
  have hV : (k-1-X*trackedUnweighted)*(1-X*(k-1)*ev g) = 0 := by
    linear_combination -hKer
  have hFactor : 1-X*(k-1)*ev g ≠ 0 := by
    intro he
    have hh := congrArg (PowerSeries.constantCoeff (R := ℤ)) he
    simp [PowerSeries.constantCoeff_X] at hh
  have hK : k = 1+X*trackedUnweighted := by
    have hh := (mul_eq_zero.mp hV).resolve_right hFactor
    linear_combination hh
  have hF : A001764.permPalTotal * (1-X*k) = 1 := by
    rw [hK]
    linear_combination permPal_root_equation
  exact @permPalCubic_of_kernel k k hF (by linear_combination hk) (by linear_combination hk)

theorem exact_a001764 : type_of% @OMA.S_oeis_a001764.main :=
  exact_a001764_of_permPal_only permPal_cubic_exact

end A001764.Round5

end

theorem OMA.solution : type_of% @OMA.S_oeis_a001764.main :=
  A001764.Round5.exact_a001764
