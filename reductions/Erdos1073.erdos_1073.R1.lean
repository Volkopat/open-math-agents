import FormalConjectures.ErdosProblems.«1073»
import Mathlib

-- Credit: @PetrouilFan
-- Reduction of Erdos 1073 by the factorization dichotomy.  The defining set of
-- A(x) splits into (i) squarefree semiprimes p*q with p,q distinct primes, whose
-- counting is the cross-prime factorial-residue correlation problem (H1), and
-- (ii) the complementary composites -- prime powers p^a with a >= 2 and integers
-- with at least three prime factors -- whose counting requires Wilson lifts and
-- higher-order common-witness intersections (H2).  These are genuinely different
-- open sub-problems; main partitions, applies the ncard union bound, and merges
-- the two exponents into one little-o exponent.

namespace OMA.R_Erdos1073_erdos_1073_R1

open Filter Asymptotics Set Nat

-- Squarefree semiprime part: pq | n!+1 with p < q distinct primes, i.e. an
-- intersection of the two factorial-residue sets W(p) and W(q).  This is the
-- cross-prime correlation problem (the numerically dominant class, 922 of the
-- first 960 certified examples are of this shape).
def H1 : Prop :=
  ∃ o1 : ℕ → ℝ, o1 =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ x : ℕ,
      ((({u : ℕ | u < x ∧ u.Composite ∧
        (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ u = p * q ∧
          ∃ n, n ! + 1 ≡ 0 [MOD u])} : Set ℕ).ncard : ℝ)
        ≤ (x : ℝ) ^ (o1 x))

-- Complementary part: prime powers p^a with a >= 2 (Wilson-prime lifts modulo
-- p^a) and composites with at least three prime factors (intersections of three
-- or more witness sets).  A genuinely different open counting problem.
def H2 : Prop :=
  ∃ o2 : ℕ → ℝ, o2 =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ x : ℕ,
      ((({u : ℕ | u < x ∧ u.Composite ∧
        ¬ (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ u = p * q) ∧
        ∃ n, n ! + 1 ≡ 0 [MOD u]} : Set ℕ).ncard : ℝ)
        ≤ (x : ℝ) ^ (o2 x))

theorem main : H1 → H2 → type_of% @Erdos1073.erdos_1073 := by
  intro h1 h2
  rcases h1 with ⟨o1, ho1, hb1⟩
  rcases h2 with ⟨o2, ho2, hb2⟩
  let SP : ℕ → Set ℕ := fun x =>
    {u | u < x ∧ u.Composite ∧
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ u = p * q ∧
        ∃ n, n ! + 1 ≡ 0 [MOD u]}
  let Rest : ℕ → Set ℕ := fun x =>
    {u | u < x ∧ u.Composite ∧
      ¬ (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ u = p * q) ∧
      ∃ n, n ! + 1 ≡ 0 [MOD u]}
  refine ⟨fun x => |o1 x| + |o2 x| + 4 / Real.log (x : ℝ), ?_, ?_⟩
  · have ht1 : Tendsto o1 atTop (nhds 0) := by
      have h := (Asymptotics.isLittleO_iff_tendsto (by intro x hx; norm_num at hx)).mp ho1
      simpa using h
    have ht2 : Tendsto o2 atTop (nhds 0) := by
      have h := (Asymptotics.isLittleO_iff_tendsto (by intro x hx; norm_num at hx)).mp ho2
      simpa using h
    have htlog : Tendsto (fun x : ℕ => 4 / Real.log (x : ℝ)) atTop (nhds 0) := by
      have hinv : Tendsto (fun x : ℕ => (Real.log (x : ℝ))⁻¹) atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      simpa [div_eq_mul_inv] using (hinv.const_mul 4)
    have hsum : Tendsto (fun x : ℕ => |o1 x| + |o2 x| + 4 / Real.log (x : ℝ)) atTop (nhds 0) := by
      simpa using (ht1.abs.add ht2.abs).add htlog
    rw [Asymptotics.isLittleO_iff_tendsto]
    · simpa using hsum
    · intro x hx
      norm_num at hx
  · intro x
    by_cases hx : x < 2
    · have hempty : ({u | u.Composite ∧ ∃ n, n ! + 1 ≡ 0 [MOD u] ∧ u < x} : Set ℕ) = ∅ := by
        ext u
        constructor
        · intro hu
          rcases hu with ⟨huc, n, hmod, hux⟩
          have hu2 : 2 ≤ u := by exact_mod_cast huc.1
          omega
        · intro hu
          simp at hu
      have hnonneg : (0 : ℝ) ≤ (x : ℝ) ^ (|o1 x| + |o2 x| + 4 / Real.log (x : ℝ)) :=
        Real.rpow_nonneg (by positivity) _
      have hA : Erdos1073.A x =
          ((({u | u.Composite ∧ ∃ n, n ! + 1 ≡ 0 [MOD u] ∧ u < x} : Set ℕ).ncard : ℝ)) := rfl
      rw [hA, hempty]
      simpa using hnonneg
    · have hxge : 2 ≤ x := by omega
      have hcover : ({u | u.Composite ∧ ∃ n, n ! + 1 ≡ 0 [MOD u] ∧ u < x} : Set ℕ) ⊆ SP x ∪ Rest x := by
        intro u hu
        rcases hu with ⟨huc, n, hmod, hux⟩
        by_cases hs : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ u = p * q
        · left
          rcases hs with ⟨p, q, hp, hq, hpq, hupq⟩
          exact ⟨hux, huc, p, q, hp, hq, hpq, hupq, ⟨n, hmod⟩⟩
        · right
          exact ⟨hux, huc, hs, ⟨n, hmod⟩⟩
      have hnunion :
          ((({u | u.Composite ∧ ∃ n, n ! + 1 ≡ 0 [MOD u] ∧ u < x} : Set ℕ).ncard : ℝ)
            ≤ (SP x).ncard + (Rest x).ncard) := by
        have hfin : (SP x ∪ Rest x).Finite := by
          refine (Finset.range x).finite_toSet.subset ?_
          intro u hu
          rcases hu with hu | hu
          · exact (by simpa [SP] using hu.1)
          · exact (by simpa [Rest] using hu.1)
        have hle := Set.ncard_le_ncard hcover hfin
        have hun := Set.ncard_union_le (SP x) (Rest x)
        exact_mod_cast (le_trans hle hun)
      have hb1' : ((SP x).ncard : ℝ) ≤ (x : ℝ) ^ (o1 x) := by simpa [SP] using hb1 x
      have hb2' : ((Rest x).ncard : ℝ) ≤ (x : ℝ) ^ (o2 x) := by simpa [Rest] using hb2 x
      have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
      have hxone : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
      have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
      have h2nonneg : (0 : ℝ) ≤ 2 / Real.log (x : ℝ) := by positivity
      have ho1le : o1 x ≤ |o1 x| + |o2 x| + 2 / Real.log (x : ℝ) := by
        have ha := le_abs_self (o1 x)
        have hb := abs_nonneg (o2 x)
        linarith
      have ho2le : o2 x ≤ |o1 x| + |o2 x| + 2 / Real.log (x : ℝ) := by
        have ha := le_abs_self (o2 x)
        have hb := abs_nonneg (o1 x)
        linarith
      have hp1 : (x : ℝ) ^ (o1 x) ≤ (x : ℝ) ^ (|o1 x| + |o2 x| + 2 / Real.log (x : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hxone ho1le
      have hp2 : (x : ℝ) ^ (o2 x) ≤ (x : ℝ) ^ (|o1 x| + |o2 x| + 2 / Real.log (x : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hxone ho2le
      have hx2log : (x : ℝ) ^ (2 / Real.log (x : ℝ)) = Real.exp 2 := by
        rw [Real.rpow_def_of_pos hxpos]
        have hm : Real.log (x : ℝ) * (2 / Real.log (x : ℝ)) = 2 := by
          field_simp [ne_of_gt hlogpos]
        rw [hm]
      have h2exp : (2 : ℝ) ≤ Real.exp 2 := by
        calc
          (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
          _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by
            nlinarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)])
      let Aexp : ℝ := |o1 x| + |o2 x| + 2 / Real.log (x : ℝ)
      have hfinal :
          2 * (x : ℝ) ^ Aexp ≤
            (x : ℝ) ^ (|o1 x| + |o2 x| + 4 / Real.log (x : ℝ)) := by
        have hrewrite : (x : ℝ) ^ (|o1 x| + |o2 x| + 4 / Real.log (x : ℝ)) =
            (x : ℝ) ^ Aexp * Real.exp 2 := by
          rw [show |o1 x| + |o2 x| + 4 / Real.log (x : ℝ) = Aexp + 2 / Real.log (x : ℝ) by
            simp [Aexp]; ring]
          rw [Real.rpow_add hxpos, hx2log]
        rw [hrewrite]
        have hn : (0 : ℝ) ≤ (x : ℝ) ^ Aexp := Real.rpow_nonneg (le_of_lt hxpos) _
        nlinarith
      rw [Erdos1073.A]
      calc
        (({u | u.Composite ∧ ∃ n, n ! + 1 ≡ 0 [MOD u] ∧ u < x} : Set ℕ).ncard : ℝ)
            ≤ (SP x).ncard + (Rest x).ncard := hnunion
        _ ≤ (x : ℝ) ^ (o1 x) + (x : ℝ) ^ (o2 x) := add_le_add hb1' hb2'
        _ ≤ 2 * (x : ℝ) ^ Aexp := by simp [Aexp]; linarith
        _ ≤ (x : ℝ) ^ (|o1 x| + |o2 x| + 4 / Real.log (x : ℝ)) := hfinal

end OMA.R_Erdos1073_erdos_1073_R1
