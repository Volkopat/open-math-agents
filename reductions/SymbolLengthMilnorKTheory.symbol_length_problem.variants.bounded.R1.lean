import FormalConjectures.Other.SymbolLengthMilnorKTheory
import Mathlib

/-!
Separate the first vanishing degree, degree two and the mod-two case from
the question of bounding the number of first slots in higher odd-prime degrees.
-/

namespace OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_bounded_R1

open MilnorK
open scoped BigOperators

private theorem grade_succ_eq_bot {F : Type*} [Field F] {p n : ℕ}
    (hz : grade F p n = ⊥) : grade F p (n + 1) = ⊥ := by
  rw [eq_bot_iff, MilnorK.grade, AddSubgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  have h := symbol_mem_grade F p (fun i : Fin n => a i.succ)
  rw [hz, AddSubgroup.mem_bot] at h
  rw [SetLike.mem_coe, AddSubgroup.mem_bot, symbol_succ, h, mul_zero]

private theorem grade_eq_bot_of_le {F : Type*} [Field F] {p m n : ℕ}
    (hz : grade F p m = ⊥) (hmn : m ≤ n) : grade F p n = ⊥ := by
  induction n, hmn using Nat.le_induction with
  | base => exact hz
  | succ n hn ih => exact grade_succ_eq_bot ih

private theorem bound_of_factors {F : Type*} [Field F] {p n B C : ℕ}
    (hB : B ∈ symbolLengthBounds F p n)
    (hC : ∀ z ∈ grade F p (n + 1),
      ∃ (a : Fin C → Fˣ) (b : Fin C → MilnorK F p),
        (∀ i, b i ∈ grade F p n) ∧ z = ∑ i, of p (a i) * b i) :
    C * B ∈ symbolLengthBounds F p (n + 1) := by
  classical
  intro z hz
  obtain ⟨a, b, hb, hsum⟩ := hC z hz
  choose k hk s hs using fun i => hB (b i) (hb i)
  let e := Fintype.equivFin (Σ i : Fin C, Fin (k i))
  let t (ij : Σ i : Fin C, Fin (k i)) : Fin (n + 1) → Fˣ :=
    Fin.cons (a ij.1) (s ij.1 ij.2)
  refine ⟨Fintype.card (Σ i : Fin C, Fin (k i)), ?_, fun j => t (e.symm j), ?_⟩
  · calc
      Fintype.card (Σ i : Fin C, Fin (k i)) = ∑ i, k i := by simp
      _ ≤ ∑ _ : Fin C, B := Finset.sum_le_sum fun i _ => hk i
      _ = C * B := by simp
  · calc
      z = ∑ i, of p (a i) * b i := hsum
      _ = ∑ ij : Σ i : Fin C, Fin (k i), symbol p (t ij) := by
        rw [Fintype.sum_sigma (fun ij => symbol p (t ij))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hs i, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [t, symbol_succ, Fin.cons_succ]
      _ = ∑ j, symbol p (t (e.symm j)) :=
        Fintype.sum_equiv e _ _ (fun ij => by simp)

/-- The first vanishing degree, from cohomological dimension and norm residue. -/
def H1 : Prop :=
  ∀ m p : ℕ, 0 < m → p.Prime → grade (MvRatFunc (Fin m) ℂ) p (m + 1) = ⊥

/-- Degree-two finiteness, a consequence of the symbol bound of Matzri. -/
def H2 : Prop :=
  ∀ m p : ℕ, 2 ≤ m → p.Prime →
    (symbolLengthBounds (MvRatFunc (Fin m) ℂ) p 2).Nonempty

/-- Higher mod-two finiteness, a consequence of the finite u-invariant. -/
def H3 : Prop :=
  ∀ m n : ℕ, 3 ≤ n → n ≤ m →
    (symbolLengthBounds (MvRatFunc (Fin m) ℂ) 2 n).Nonempty

/-- Bound the number of first slots required to represent a class in higher
odd-prime degree. Lower-degree factors can be arbitrary elements of their grade. -/
def H4 : Prop :=
  ∀ m n p : ℕ, 2 ≤ n → n + 1 ≤ m → p.Prime → p ≠ 2 →
    ∃ C : ℕ, ∀ z ∈ grade (MvRatFunc (Fin m) ℂ) p (n + 1),
      ∃ (a : Fin C → (MvRatFunc (Fin m) ℂ)ˣ)
        (b : Fin C → MilnorK (MvRatFunc (Fin m) ℂ) p),
        (∀ i, b i ∈ grade (MvRatFunc (Fin m) ℂ) p n) ∧
          z = ∑ i, of p (a i) * b i

theorem main : H1 → H2 → H3 → H4 →
    type_of% @SymbolLengthMilnorKTheory.symbol_length_problem.variants.bounded := by
  intro hVanish hDegreeTwo hModTwo hOdd m n p hp
  by_cases hnzero : n = 0
  · subst n
    exact ⟨p - 1, sub_one_mem_symbolLengthBounds_zero _ p hp.pos⟩
  by_cases hmzero : m = 0
  · subst m
    let e : ℂ ≃+* MvRatFunc (Fin 0) ℂ :=
      IsFractionRing.ringEquivOfRingEquiv (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0)).symm
    let _ : IsAlgClosed (MvRatFunc (Fin 0) ℂ) := IsAlgClosed.of_ringEquiv ℂ _ e
    exact ⟨0, SymbolLengthMilnorKTheory.symbol_length_problem.variants.isAlgClosed _
      n p (by omega) hp.pos⟩
  have hm : 0 < m := by omega
  clear hnzero
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hgt : m < n
    · exact ⟨0, (zero_mem_symbolLengthBounds_iff _ _).mpr
        (grade_eq_bot_of_le (hVanish m p hm hp) (by omega))⟩
    cases n with
    | zero => exact ⟨p - 1, sub_one_mem_symbolLengthBounds_zero _ p hp.pos⟩
    | succ n =>
      by_cases hzero : n = 0
      · subst n
        exact ⟨1, one_mem_symbolLengthBounds_one _ p⟩
      by_cases hone : n = 1
      · subst n
        exact hDegreeTwo m p (by omega) hp
      by_cases hp2 : p = 2
      · subst p
        exact hModTwo m (n + 1) (by omega) (by omega)
      obtain ⟨C, hC⟩ := hOdd m n p (by omega) (by omega) hp hp2
      obtain ⟨B, hB⟩ := ih n (by omega)
      exact ⟨C * B, bound_of_factors hB hC⟩

end OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_bounded_R1
