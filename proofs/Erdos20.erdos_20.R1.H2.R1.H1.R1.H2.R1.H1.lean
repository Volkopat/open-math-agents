import OMAReductions.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H2_R1
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.InsertIdx
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Log
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.SeparationQuotient.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Topology.Defs.Basic
-- Brouwer fixed point theorem: harfe/fixed-point-theorems-lean4 (MIT), OAI lake dependency

theorem Finset_mem_filter_any {α : Type*} {s : Finset α} {p : α → Prop} {inst : DecidablePred p} {a : α} :
    a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a := Finset.mem_filter
-- ==== cubical_sperner_prep
section


open Classical


/-
The Cubical Sperner's Lemma.
We mostly follow Kuhn 1960 "Some Combinatorial Lemmas in Topology"
-/

structure SpernerCube where
  n : ℕ
  p : ℕ
  RL : (Fin n → Fin (p+1)) → ℕ
  rl_proper : ∀ (I: Fin n → Fin (p+1) ), RL I ≤ n ∧
      ∀ (k : Fin n), (I k = 0 → RL I ≠ k.1) ∧ (I k = p → RL I ≤ k.1)

namespace SpernerCube

def G (SC : SpernerCube) := Fin SC.n → Fin (SC.p+1)

instance Gfin (SC : SpernerCube): Fintype SC.G := by {
  exact Pi.instFintype
}

end SpernerCube

variable (SC : SpernerCube)
variable {n1 : ℕ}
variable {hn1 : n1 + 1 = SC.n}


def simplex (m:ℕ ) (I : Fin (m+1)→ SC.G) := Function.Injective I
    ∧ ∀ i < m, ∀ j : Fin SC.n, (I (Fin.ofNat _ i) j).1 ≤ (I (Fin.ofNat _ (i+1)) j).1
    ∧ (I (Fin.last m) j).1 ≤ (I 0 j).1 + 1

def complete_simplex (m:ℕ ) (I : Fin (m+1) → SC.G ) := simplex SC m I
    ∧ Set.range (fun (i:Fin (m+1))↦ SC.RL (I i)) = {j : ℕ | j ≤ m}

def is_face I J :=
    simplex SC n1 I ∧ simplex SC SC.n J ∧ Set.range I ⊆ Set.range J

def is_boundary_face I := ∃! J, @is_face SC n1 I J

def complete_boundary_face I := is_boundary_face SC I ∧ complete_simplex SC n1 I

def case_A (I : Fin (n1 +1) → SC.G) := ∃ j, ∀ k, I k j = 0

def case_B (I : Fin (n1 +1) → SC.G) := ∃ j, ∀ k, I k j = Fin.last SC.p

def case_C (I : Fin (n1 +1) → SC.G) :=
    ∃ j, ∃ (q : Fin (SC.p + 1)), (q ≠ 0 ∧ q ≠ Fin.last SC.p ) ∧ ∀ k, I k j = q

def case_D (I : Fin (n1 +1) → SC.G) := ∀ j, ∀ q, ∃ k,I k j ≠ q


lemma one_of_ABCD (I : Fin (n1 +1) → SC.G) :
    case_A SC I ∨ case_B SC I ∨ case_C SC I ∨ case_D SC I := by {
  by_cases h1 : case_D SC I
  exact Or.inr (Or.inr (Or.inr h1))
  unfold case_D at h1
  push Not at h1
  obtain ⟨j , ⟨ q, h2 ⟩⟩ := h1
  by_cases q0 : q = 0
  {
    apply Or.inl
    use j
    rwa [← q0]
  }
  by_cases qp : q = Fin.last SC.p
  {
    apply Or.inr (Or.inl _)
    use j
    intro k
    rwa [h2 k]
  }
  suffices h3 : case_C SC I by {
    simp only [h3, true_or, or_true]
  }
  use j, q
}


section simplex_properties


lemma monotone_1_of_simplex {m:ℕ } (I : Fin (m+1)→ SC.G) (hs : simplex SC m I) (i1 i2 : Fin (m+1))
    (h1 : i1 ≤ i2) : ∀ j, I i1 j ≤ I i2 j := by {
  intro j
  let f := fun i ↦ I i j
  have h2 := @Fin.monotone_iff_le_succ m _ _ f
  suffices h3 : Monotone f by exact (h3 h1)
  rw [h2]
  clear i1 i2 h1
  intro i1
  have h3 := (hs.2 i1.1 i1.2 j).1
  simp only [Fin.val_fin_le] at h3
  convert h3 <;> ext <;> simp [Fin.ofNat_eq_cast, Nat.mod_eq_of_lt]
}

lemma monotone_2_of_simplex {m:ℕ } (I : Fin (m+1)→ SC.G) (hs : simplex SC m I) (i1 i2 : Fin (m+1)) :
    i1 ≤ i2 ↔ ∀ j, I i1 j ≤ I i2 j := by {
  apply Iff.intro
  {
    intro h1 j
    apply monotone_1_of_simplex _ I hs i1 i2 h1
  }
  {
    intro h1
    by_contra h2
    have h3 : i1 ≠ i2 := ne_of_not_le h2
    apply h3
    apply hs.1
    apply funext
    intro j
    apply le_antisymm (h1 j)
    apply monotone_1_of_simplex _ _ hs i2 i1 (le_of_not_ge h2)
  }
}

lemma last_of_simplex {m: ℕ} I (hs : simplex SC m I) j :
    (I (Fin.last m) j).1 ≤ (I 0 j).1 + 1 := by {
  cases m
  simp only [Fin.last_zero, Fin.isValue, le_add_iff_nonneg_right, zero_le]
  rename_i m
  have h3 : 0 < m + 1 := by omega
  exact (hs.2 0 h3 j).2
}

lemma le_add_one_of_simplex {m: ℕ} I (hs : simplex SC m I) (i1 i2 : Fin (m+1)) j :
    (I i1 j).1 ≤ (I i2 j).1 + 1 := by {
  have h1 := last_of_simplex SC I hs j
  apply le_trans _ (le_trans h1 _)
  apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i1)
  apply Nat.add_le_add_right
  apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i2)
}

end simplex_properties


lemma p_ne_zero_of_cube {hn1 : n1 + 1 = SC.n}: Fin.last SC.p ≠ 0 := by {
  simp only [ne_eq, Fin.last_eq_zero_iff]
  intro h1
  let v : Fin SC.n → Fin (SC.p + 1) := fun _ ↦ 0
  have h3 : NeZero SC.n := by {
    rw [←hn1]
    exact instNeZeroNatHAdd_1
  }
  have h4 : v 0 = 0 := by {rfl}
  have h2 := (SC.rl_proper v).2 0
  simp only [Fin.val_zero, ne_eq, h1, Fin.val_eq_zero_iff, nonpos_iff_eq_zero] at h2
  exact h2.1 h4 (h2.2 h4)
}


section simplex_child


def insert_index (j : Fin (SC.n+1)) (a: Fin (n1 +1 )) : Fin (SC.n+1) :=
{ val := if a.val < j.val then a.val else a.val+1,
  isLt := by {
    by_cases hlt : a.val < j.val
    {
      simp only [hlt, ↓reduceIte]
      exact Nat.lt_trans hlt j.2
    }
    {
      simp only [hlt, ↓reduceIte, add_lt_add_iff_right]
      rw [← hn1]
      exact a.2
    }
} }

def delete_vertex (j: Fin (SC.n+1)) (I : Fin (SC.n+1)→ SC.G) : Fin (n1 + 1) → SC.G :=
  fun a ↦ I (@insert_index SC n1 hn1 j a)

lemma insert_index_ne j a : @insert_index SC n1 hn1 j a ≠ j := by {
  apply Fin.ne_of_val_ne
  unfold insert_index
  by_cases hlt : a.val < j.val
  {
    simp only [hlt, ↓reduceIte]
    omega
  }
  {
    simp only [hlt, ↓reduceIte, ne_eq]
    omega
  }
}

lemma almost_surjective_of_insert_index (j : Fin (SC.n+1)) (a : Fin (SC.n+1)) (h : a ≠ j)
    : ∃ k : Fin (n1 + 1) , a = @insert_index SC n1 hn1 j k := by {
  unfold insert_index
  by_cases hlt : a.1 < j.1
  {
    use (Fin.ofNat _ a.1)
    have h2 : a.1 = (Fin.ofNat (n1 + 1) a.1) := by {
      rw [Fin.ofNat_eq_cast, Fin.val_cast_of_lt]
      rw [hn1]
      apply lt_of_lt_of_le hlt
      exact Fin.is_le j
    }
    simp only [← h2, hlt]
    rfl
  }
  {
    have h2 : j.1 < a.1 := by {
      have := Fin.val_ne_of_ne (id (Ne.symm h))
      omega
    }
    let a1 := a.1 - 1
    have h3 : a1 + 1 = a.1 := by {
      show a.1 - 1 + 1 = a.1
      omega
    }
    let a1f := Fin.ofNat (n1 + 1) a1
    use a1f
    ext
    have h4 : a1 < n1 +1 := by {
      have h5 := a.2
      show a.1 - 1 < n1 + 1
      omega
    }
    have h6 : a1f.1 = a1 := by {
      unfold a1f
      simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      exact h4
    }
    have h5 : ¬ (a1f < j.1) := by {
      simp only [not_lt, h6]
      show j.1 ≤ a.1 - 1
      omega
    }
    simp only [h5, ↓reduceIte]
    rw [← h3, h6]
  }
}

lemma insert_index_strict_mono j : StrictMono (@insert_index SC n1 hn1 j) := by {
  intro a b h1
  have h2 : a.1 < b.1 := by {exact h1}
  have h21 : a.1 < b.1 + 1 := by omega
  unfold insert_index
  by_cases h3 : a.1 < j.1
  {
    by_cases h4 : b.1 < j.1
    repeat {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, Fin.val_fin_lt, gt_iff_lt]
      assumption
    }
  }
  {
    by_cases h4 : b.1 < j.1
    {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, gt_iff_lt]
      omega
    }
    {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, gt_iff_lt]
      omega
    }
  }
}

lemma insert_index_inj j : Function.Injective (@insert_index SC n1 hn1 j) := by {
  apply StrictMono.injective
  apply insert_index_strict_mono
}


lemma delete_vertex_inj J {hs : simplex SC SC.n J} i1 i2
    (h1 : @delete_vertex SC n1 hn1 i1 J = @delete_vertex SC n1 hn1 i2 J ) : i1 = i2 := by {
  by_contra h2
  obtain ⟨k, h3 ⟩ := @almost_surjective_of_insert_index SC n1 hn1 i2 i1 h2
  apply @insert_index_ne SC n1 hn1 i1 k
  apply hs.1
  nth_rewrite 2 [h3]
  exact (congrFun h1) k
}

lemma delete_vertex_simplex J {hs : simplex SC SC.n J} i :
    simplex SC n1 (@delete_vertex SC n1 hn1 i J) := by {
  apply And.intro
  {
    intro k1 k2 h2
    apply insert_index_inj SC i
    apply hs.1 h2
  }
  {
    intro i2 hi2 j
    unfold delete_vertex
    apply And.intro
    {
      apply monotone_1_of_simplex SC J hs
      rw [StrictMono.le_iff_le]
      {
        simp only [Fin.ofNat_eq_cast]
        apply Fin.natCast_mono hi2
        exact Nat.le_add_right i2 1
      }
      apply insert_index_strict_mono
    }
    apply le_add_one_of_simplex SC J hs
  }
}

lemma delete_vertex_is_face J {hs : simplex SC SC.n J} i :
    is_face SC (@delete_vertex SC n1 hn1 i J) J := by {
  apply And.intro
  {
    apply delete_vertex_simplex
    exact hs
  }
  {
    apply And.intro hs
    intro c hc
    obtain ⟨ i2, hi2 ⟩ := hc
    use @insert_index SC n1 hn1 i i2
    exact hi2
  }
}

lemma is_id_of_strict_mono (m: ℕ ) (f : Fin m → Fin m) (hsm : StrictMono f)
    : ∀ k, f k = k := by {
  suffices h1 : ∀ (a : ℕ), ∀ k, k.1 < a → f k = k by {
    intro k
    exact h1 m k k.2
  }
  intro a
  induction' a with a ha
  {
    intro k h1
    omega
  }
  {
    have h1 : Function.Injective f := by {exact StrictMono.injective hsm}
    have h2 : Function.Surjective f := Finite.surjective_of_injective h1
    intro k hk
    have h3 j : j < k → f j = j := by {
      intro hj
      apply ha
      omega
    }
    by_cases h4 : f k < k
    apply h1 (h3 (f k) h4)
    simp only [not_lt] at h4
    apply le_antisymm _ h4
    obtain ⟨l, h9⟩ := h2 k
    suffices h8 : k ≤ l by {rwa [← hsm.le_iff_le, h9] at h8}
    by_contra! h6
    have h7 := h3 l h6
    rw [h9] at h7
    rw [h7] at h6
    exact (lt_self_iff_false l).mp h6
  }
}

lemma is_insert_index_of_strict_mono f (hsm : StrictMono f)
    : ∃ j, f = @insert_index SC n1 hn1 j := by {
  have h31 : Function.Injective f := by {exact hsm.injective}
  have hns : ∃ j, ∀ i, f i ≠ j := by {
    by_contra! h1
    have h2 : Function.Surjective f := by {exact h1 }
    have h5 : Function.Bijective f :=  And.intro h31 h2
    have h4 := Nat.card_eq_of_bijective f h5
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.add_right_cancel_iff] at h4
    rw [h4] at hn1
    simp only [Nat.add_eq_left, one_ne_zero] at hn1
  }
  obtain ⟨ j, hj⟩ := hns
  use j
  have h1 : ∀ k1, ∃ k2, f k1 = @insert_index SC n1 hn1 j k2 := by {
    intro k1
    apply almost_surjective_of_insert_index
    exact hj k1
  }
  obtain ⟨g, hg⟩ := axiomOfChoice h1
  have h2 : StrictMono g := by {
    intro k1 k2
    contrapose!
    intro h4
    rw [←hsm.le_iff_le, hg k1, hg k2]
    have h5 := @insert_index_strict_mono SC n1 hn1 j
    rw [h5.le_iff_le]
    exact h4
  }
  have h3 := is_id_of_strict_mono _ g h2
  ext1 k
  rw [hg k, h3 k]
}

lemma child_simplex_char (I : Fin (n1 +1) → SC.G) J {hs : simplex SC SC.n J}
    : is_face SC I J ↔ ∃ i, I = @delete_vertex SC n1 hn1 i J := by {
  apply Iff.intro
  {
    intro h1
    have h2 : ∃ (f : Fin (n1+1) → Fin (SC.n+1)), ∀ k, I k = J (f k) := by {
      have h2 := h1.2.2
      have h3 : ∀ k, ∃ j, I k = J j := by {
        intro k
        have h4 : I k ∈ Set.range I := by {
          exact Set.mem_range_self k
        }
        have h3 := h2 h4
        obtain ⟨j, hj⟩ := h2 h4
        use j
        exact hj.symm
      }
      apply axiom_of_choice h3
    }
    obtain ⟨f, hf ⟩ := h2
    have h31 : Function.Injective f := by {
      intro k1 k2 h2
      apply h1.1.1
      rw [hf k1, hf k2, h2]
    }
    have h3 : StrictMono f := by {
      apply Monotone.strictMono_of_injective _ h31
      intro k1 k2 h2
      rw [monotone_2_of_simplex SC J hs]
      rw [← hf k1, ← hf k2]
      rwa [←monotone_2_of_simplex SC I h1.1]
    }
    obtain ⟨j, hj⟩ := is_insert_index_of_strict_mono SC f h3
    use j
    ext k
    unfold delete_vertex
    rw [hf k, hj]
  }
  {
    intro h1
    obtain ⟨ i, hi⟩ := h1
    rw [hi]
    apply @delete_vertex_is_face SC _ _ J hs
  }
}

end simplex_child


section cases_ABCD

lemma insert_vertex I (v : SC.G) j :
    ∃ J, I = @delete_vertex SC n1 hn1 j J ∧ J j = v := by {
  have h1 : ∀ j2, ∃ w, (j2 = j → w = v)
      ∧ ∀ i, @insert_index SC n1 hn1 j i = j2 → I i = w := by {
    intro j2
    by_cases h1 : j2 = j
    {
      use v
      simp only [implies_true, true_and]
      intro i
      have h3 : @insert_index SC n1 hn1 j i ≠ j := by {apply insert_index_ne}
      simp only [h1, h3, IsEmpty.forall_iff]
    }
    {
      have h3 : ∃ i, j2 = @insert_index SC n1 hn1 j i := by {
        apply almost_surjective_of_insert_index
        exact h1
      }
      obtain ⟨ i, hi⟩ := h3
      use (I i)
      simp only [h1, IsEmpty.forall_iff, true_and]
      intro i2 h2
      congr!
      apply insert_index_inj SC j
      rw [h2, hi]
    }
  }
  obtain ⟨J, h2⟩ := axiomOfChoice h1
  use J
  apply And.intro
  {
    ext i
    exact (h2 (@insert_index SC n1 hn1 j i)).2 i rfl
  }
  exact (h2 j).1 rfl
}

lemma surround_index (j : Fin (SC.n + 1)) (i : Fin (n1 + 1)) (hij : i.1 + 1 = j.1 )
    (hj1 : j ≠ Fin.last SC.n): ((@insert_index SC n1 hn1 j i).1 + 1 = j.1
    ∧ j.1 + 1 = @insert_index SC n1 hn1 j (i+1)) := by {
  unfold insert_index
  have h2 : i.1 < j.1 := by omega
  have h3 : (i+1).1 = i.1 + 1 := by {
    refine Fin.val_add_one_of_lt ?_
    simp only [Nat.succ_eq_add_one]
    show i.1 < n1
    have h6 := Fin.val_lt_last hj1
    omega
  }
  apply And.intro
  {
    simp only [h2, ↓reduceIte]
    exact hij
  }
  simp only [h3, hij, lt_self_iff_false, ↓reduceIte]
}

lemma parent_injective I (hs : simplex SC n1 I) J j
    (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ∉ Set.range I)
    : Function.Injective J := by {
  have h5 j3 : j3 ≠ j → ∃ i3, j3 = @insert_index SC n1 hn1 j i3
    := by {apply almost_surjective_of_insert_index}
  intro j1 j2 h4
  have h7 j3 : J j3 = J j → j3 = j := by {
      intro h7
      by_contra h51
      apply h2
      obtain ⟨i3, hi3⟩ := h5 j3 h51
      use i3
      rw [←h7,h1,hi3]
      rfl
  }
  by_cases h8 : j1 = j
  {
    rw [h8, h7 j2]
    rw [←h8,h4]
  }
  by_cases h9 : j2 = j
  {
    rw [h9, h7 j1]
    rw [←h9,h4]
  }
  obtain ⟨i1, hi1⟩ := h5 j1 h8
  obtain ⟨i2, hi2⟩ := h5 j2 h9
  suffices h11 : i1 = i2 by {rw [hi1,hi2,h11] }
  apply hs.1
  rw [h1]
  unfold delete_vertex
  rw [← hi1,← hi2, h4]
}

lemma parent_simplex_case_BC I (hs : simplex SC n1 I) J
    (h1 : I = @delete_vertex SC n1 hn1 0 J) (h2 : J 0 ≠ I 0)
    (h3 : ∀ k, J 0 k ≤ I 0 k ∧ (I (Fin.last n1) k).1 ≤ (J 0 k).1 + 1) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use 0
    exact h4
  }
  have h4 : J 0 ∉ Set.range I := by {
    intro h5
    obtain ⟨i1, hi1⟩ := h5
    apply h2
    apply funext
    intro k
    apply le_antisymm (h3 k).1
    rw [←hi1]
    apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i1)
  }
  apply And.intro ( parent_injective SC I hs J 0 h1 h4)
  have h5 j2 : j2 < n1 + 1 →  J (Fin.ofNat _ (j2+1)) = I (Fin.ofNat _ j2) := by {
    rw [h1]
    unfold delete_vertex insert_index
    congr! with h7
    simp only [Fin.ofNat_eq_cast, Fin.val_zero, not_lt_zero, ↓reduceIte]
    rw [Fin.val_cast_of_lt, Fin.val_cast_of_lt h7]
    omega
  }
  intro j1 hj1 k1
  apply And.intro
  {
    rw [←hn1] at hj1
    rw [h5 j1 hj1]
    cases j1
    {
      simp only [Fin.ofNat_eq_cast, Fin.val_fin_le]
      exact (h3 k1).1
    }
    rename_i j2
    rw [h5 j2]
    apply monotone_1_of_simplex SC I hs
    simp only [Fin.ofNat_eq_cast]
    apply Fin.natCast_mono
    exact Nat.le_of_lt_succ hj1
    exact Nat.le_add_right j2 1
    exact Nat.lt_of_succ_lt hj1
  }
  {
    have h6 := h5 n1 (lt_add_one n1)
    have e1 : (Fin.ofNat (SC.n + 1) (n1 + 1) : Fin (SC.n + 1)) = Fin.last SC.n := by
      rw [← hn1]; simp [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    have e2 : (Fin.ofNat (n1 + 1) n1 : Fin (n1 + 1)) = Fin.last n1 := by
      simp [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    rw [e1, e2] at h6
    rw [congrFun h6 k1]
    exact (h3 k1).2
  }
}

lemma parent_simplex_case_AC I (hs : simplex SC n1 I) J j (hj : j = Fin.last SC.n)
    (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ≠ I (Fin.last n1))
    (h3 : ∀ k, I (Fin.last n1) k ≤ J j k ∧ (J j k).1 ≤ (I 0 k).1 + 1) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use j
    exact h4
  }
  have h4 : J j ∉ Set.range I := by {
    intro h5
    obtain ⟨i1, hi1⟩ := h5
    apply h2
    apply funext
    intro k
    apply le_antisymm _ (h3 k).1
    rw [←hi1]
    apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i1)
  }
  have h5 j2 : j2 < SC.n → J (Fin.ofNat _ j2) = I (Fin.ofNat _ j2) := by {
    intro h6
    rw [h1,hj]
    unfold delete_vertex insert_index
    congr!
    have h7 : (Fin.ofNat (n1+1) j2).1 < (Fin.last SC.n).1 := by {
      simp only [Fin.ofNat_eq_cast, Fin.val_last]
      rw [Fin.val_cast_of_lt]
      exact h6
      rwa [←hn1] at h6
    }
    simp only [h7,↓reduceIte]
    simp only [Fin.ofNat_eq_cast]
    rw [Fin.val_cast_of_lt, Fin.val_cast_of_lt]
    rwa [←hn1] at h6
    exact Nat.lt_add_right 1 h6
  }
  apply And.intro ( parent_injective SC I hs J j h1 h4)
  intro j1 hj1 k1
  apply And.intro
  {
    rw [h5 _ hj1]
    by_cases h12 : j1 + 1 < SC.n
    {
      rw [h5 _ h12]
      apply monotone_1_of_simplex SC I hs
      simp only [Fin.ofNat_eq_cast]
      apply Fin.natCast_mono
      apply Nat.le_of_lt_add_one
      rwa [hn1]
      exact Nat.le_add_right j1 1
    }
    have h16 : j1+1 = SC.n := by omega
    have h13 : Fin.ofNat _ j1 = Fin.last n1 := by {
      suffices h15 : j1 = n1 by {
        simp only [h15, Fin.ofNat_eq_cast, Fin.natCast_eq_last]
      }
      omega
    }
    have h14 : Fin.ofNat _ (j1+1) = j := by {
      rw [hj]
      simp only [h16, Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    }
    rw [h13,h14]
    exact (h3 k1).1
  }
  {
    have h7 : J 0 = I 0 := by {
      have h6 := h5 0 (Nat.zero_lt_of_lt hj1)
      simp only [Fin.ofNat_eq_cast] at h6
      exact h6
    }
    rw [h7,←hj]
    exact (h3 k1).2
  }
}

lemma parent_simplex_case_D I (hs : simplex SC n1 I) J j i
    (hij : i.1 + 1 = j.1 ) (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ∉ Set.range I)
    (h3 : ∀ k, I i k ≤ J j k ∧ J j k ≤ I (i+1) k) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use j
    exact h4
  }
  have h5 j3 : j3 ≠ j → ∃ i3, j3 = @insert_index SC n1 hn1 j i3 := by {
    apply almost_surjective_of_insert_index
  }
  have h6 j3 : j3 ≠ j → ∃ i3, I i3 = J j3 := by {
    intro h7
    obtain ⟨i3, hi3⟩ := h5 j3 h7
    use i3
    rw [h1, hi3]
    rfl
  }
  apply And.intro (parent_injective SC I hs J j h1 h2)
  intro i2 h4 k2
  have h5 := h3 k2
  apply And.intro
  {
    simp only [Fin.ofNat_eq_cast, Fin.val_fin_le]
    rw [h1] at h5
    unfold delete_vertex at h5
    have h6 : (@insert_index SC n1 hn1 j i).1 + 1 = j := by {
      unfold insert_index
      have h7 : i.1 < j.1 := by omega
      simp only [h7, ↓reduceIte]
      exact hij
    }
    by_cases h8 : i2 = j.1
    {
      convert h5.2
      simp only [h8, Fin.cast_val_eq_self]
      have h11 : j ≠ Fin.last SC.n := by {
        suffices h12 : j.1 ≠ SC.n by exact Ne.symm (Fin.ne_of_val_ne (Ne.symm h12))
        rw [←h8]
        exact Nat.ne_of_lt h4
      }
      have h9 := @surround_index SC n1 hn1 j i hij h11
      rw [h8, h9.2]
      exact Fin.cast_val_eq_self (insert_index SC j (i + 1))
    }
    by_cases h9 : i2 + 1 = j.1
    {
      rw [←h9] at h6
      simp only [Nat.add_right_cancel_iff] at h6
      convert h5.1
      rw [←h6]
      simp only [Fin.cast_val_eq_self]
      rw [h9]
      simp only [Fin.cast_val_eq_self]
    }
    have h11 : ∃ i3, (Fin.ofNat _ i2) = @insert_index SC n1 hn1 j i3 := by {
      apply almost_surjective_of_insert_index
      intro h12
      apply h8
      rw [← h12]
      simp only [Fin.ofNat_eq_cast]
      rw [Fin.val_cast_of_lt]
      apply lt_trans h4 (lt_add_one SC.n)
    }
    have h12 : ∃ i3, (Fin.ofNat _ (i2+1)) = @insert_index SC n1 hn1 j i3 := by {
      apply almost_surjective_of_insert_index
      intro h12
      apply h9
      rw [← h12]
      simp only [Fin.ofNat_eq_cast]
      rw [Fin.val_cast_of_lt]
      omega
    }
    simp only [Fin.ofNat_eq_cast] at h11 h12
    obtain ⟨i3, hi3⟩ := h11
    obtain ⟨i4, hi4⟩ := h12
    rw [hi3, hi4]
    suffices h21 : I i3 k2 ≤ I i4 k2 by {rwa [h1] at h21}
    apply monotone_1_of_simplex SC I hs
    have h21 : StrictMono (@insert_index SC n1 hn1 j) := by {
      apply insert_index_strict_mono
    }
    rw [←h21.le_iff_le]
    rw [←hi3, ← hi4]
    refine (Fin.natCast_le_natCast ?_ h4).mpr ?_
    exact Nat.le_of_succ_le h4
    exact Nat.le_succ i2
  }
  {
    have h11 : (J (Fin.last SC.n) k2).1 ≤ (I (Fin.last n1) k2).1 := by {
      simp only [Fin.val_fin_le]
      by_cases h12 : Fin.last SC.n = j
      {
        rw [h12]
        apply le_trans h5.2
        apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last _)
      }
      obtain ⟨ i3, hi3⟩ := h6 _ h12
      rw [←hi3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last _)
    }
    have h13 := last_of_simplex SC I hs k2
    apply le_trans h11 (le_trans h13 _)
    simp only [add_le_add_iff_right, Fin.val_fin_le]
    by_cases h14 : 0 = j
    {
      rw [h14]
      apply le_trans _ h5.1
      apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _)
    }
    {
      obtain ⟨i3, hi3⟩ := h6 _ h14
      rw [← hi3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _)
    }
  }
}


noncomputable def coord_change_count (v1 v2 : SC.G) := Finset.card {i | v1 i ≠ v2 i}

lemma ccc_add {m} I (hs : simplex SC m I) (i1 i2 i3) (h1 : i1 ≤ i2 ∧ i2 ≤ i3) :
    coord_change_count SC (I i1) (I i3) =
    coord_change_count SC (I i1) (I i2) + coord_change_count SC (I i2) (I i3) := by {
  unfold coord_change_count
  rw [←Finset.card_union_of_disjoint]
  congr
  apply Finset.ext_iff.mpr
  intro k2
  simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  rw [←Decidable.not_and_iff_not_or_not]
  apply Iff.intro
  {
    intro h3 h4
    apply h3
    rw [h4.1, h4.2]
  }
  {
    intro h2 h3
    apply h2
    have h4 := monotone_1_of_simplex SC I hs i1 i2 h1.1 k2
    have h5 := monotone_1_of_simplex SC I hs i2 i3 h1.2 k2
    rw [h3] at h4 ⊢
    suffices h1 : I i3 k2 = I i2 k2 by exact ⟨h1, Eq.symm h1⟩
    exact Fin.le_antisymm h4 h5
  }
  {
    apply Finset.disjoint_filter.mpr
    intro k1 hk1 h2 h3
    apply h3
    have h4 : ∀ k, I i1 k ≤ I i2 k :=  monotone_1_of_simplex SC I hs i1 i2 h1.1
    have h5 : I i1 k1 < I i2 k1 := lt_of_le_of_ne (h4 k1) h2
    have h6 : (I i3 k1).1 ≤ (I i1 k1).1 + 1 := by {
      apply le_add_one_of_simplex _ _ hs
    }
    apply le_antisymm ( monotone_1_of_simplex SC I hs i2 i3 h1.2 k1)
    apply le_trans h6 h5
  }
}

lemma ccc_pos {m} I (hs : simplex SC m I) i1 i2 (h1 : i1 ≠ i2)
    : 0 < coord_change_count SC (I i1) (I i2) := by {
  unfold coord_change_count
  by_contra! h2
  apply h1
  apply hs.1
  simp only [ne_eq, nonpos_iff_eq_zero, Finset.card_eq_zero] at h2
  apply funext
  intro k
  rw [Finset.filter_eq_empty_iff] at h2
  simp only [Finset.mem_univ, Decidable.not_not, forall_const] at h2
  apply h2
}

noncomputable def ccc_fun {m} (I : Fin (m+1)→ SC.G) (i : Fin (m+1)) : Fin (SC.n + 1 )
    := ⟨ coord_change_count SC (I 0) (I i), by {
      refine Nat.lt_succ_of_le ?_
      exact card_finset_fin_le {i_1 | I 0 i_1 ≠ I i i_1}
    } ⟩

lemma ccc_fun_strict_mono {m} I (hs : simplex SC m I) :
    StrictMono (ccc_fun SC I) := by {
  intro i1 i2 h1
  unfold ccc_fun
  simp only [Fin.mk_lt_mk]
  have h3 : 0 ≤ i1 ∧ i1 ≤ i2 := ⟨ (Fin.zero_le i1), (Fin.le_of_lt h1) ⟩
  rw [ccc_add SC I hs 0 i1 i2 h3]
  simp only [lt_add_iff_pos_right, gt_iff_lt]
  apply ccc_pos SC I hs _ _ $ Fin.ne_of_lt h1
}

lemma ccc_fun_is_insert_index I (hs : simplex SC n1 I) :
    ∃ j, ccc_fun SC I = @insert_index SC n1 hn1 j := by {
  apply is_insert_index_of_strict_mono
  apply ccc_fun_strict_mono SC I hs
}



lemma ccc_fun_case_D_iff {m} I (hs : simplex SC m I) :
    case_D SC I ↔ ccc_fun SC I (Fin.last m) = Fin.last SC.n := by {
  have h1 : (ccc_fun SC I (Fin.last m) = Fin.last SC.n) ↔ ∀ k, I 0 k ≠ I (Fin.last m) k  := by {
    unfold ccc_fun coord_change_count
    have key : ∀ s : Finset (Fin SC.n), s.card = SC.n ↔ s = Finset.univ := fun s => by
      rw [← Finset.card_eq_iff_eq_univ, Fintype.card_fin]
    rw [Fin.ext_iff, Fin.val_last]
    dsimp only
    rw [key, Finset.eq_univ_iff_forall]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
  }
  apply Iff.trans _ h1.symm
  unfold case_D
  apply Iff.intro
  {
    intro h2 k1
    obtain ⟨i2, hi2⟩ := h2 k1 (I 0 k1)
    intro h3
    apply hi2
    apply le_antisymm
    {
      rw [h3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i2)
    }
    exact monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i2) k1
  }
  {
    contrapose!
    intro h2
    obtain ⟨k2, ⟨q, hq⟩ ⟩ := h2
    use k2
    rw [hq, hq]
  }
}

lemma last_eq_first_add_one J (hs : simplex SC SC.n J)
    : ∀ k, (J (Fin.last SC.n) k).1 = (J 0 k).1 + 1 := by {
  have h3 : ∀ j3, ccc_fun SC J j3 = j3 := by {
    apply is_id_of_strict_mono
    apply ccc_fun_strict_mono SC J hs
  }
  have h2 := (ccc_fun_case_D_iff SC J hs).mpr (h3 _)
  unfold case_D at h2
  intro k
  apply le_antisymm  (last_of_simplex SC J hs k)
  apply Nat.add_one_le_of_lt
  obtain ⟨j1, hj1⟩ := h2 k (J 0 k)
  have h4 := monotone_1_of_simplex SC J hs _ _ (Fin.le_last j1) k
  apply lt_of_lt_of_le _ h4
  apply lt_of_le_of_ne (monotone_1_of_simplex SC J hs _ _ (Fin.zero_le j1) k) hj1.symm
}

lemma delete_vertex_ccc_fun_match J (hs : simplex SC SC.n J) j1 j2
    ( h1 : ccc_fun SC (@delete_vertex SC n1 hn1 j1 J) = @insert_index SC n1 hn1 j2)
    : (j1 = 0 → j2 = Fin.last SC.n) ∧ (j1 ≠ 0 → j1 = j2) := by {
  let I := @delete_vertex SC n1 hn1 j1 J
  have hsI : simplex SC n1 I := by {
    suffices h2 : is_face SC I J by { exact h2.1}
    rw [@child_simplex_char SC n1 hn1 I J hs]
    use j1
  }
  have scnpos : 0 < SC.n := by omega
  by_cases h4 : j1 = 0
  {
    simp only [h4, forall_const, ne_eq, not_true_eq_false, IsEmpty.forall_iff, and_true]
    have h5 : I 0 = J 1 := by {
      unfold I delete_vertex insert_index
      congr!
      rw [h4]
      simp only [Fin.val_zero, lt_self_iff_false, ↓reduceIte, zero_add]
      simp only [Fin.val_one']
      refine Eq.symm (Nat.mod_eq_of_lt ?_)
      exact Nat.lt_add_of_pos_left scnpos
    }
    symm
    by_contra h6
    obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 _ _ h6
    have h8 : (ccc_fun SC I i1).1 = SC.n := by {
      unfold I
      rw [h1, ← hi1]
      simp only [Fin.val_last]
    }
    unfold ccc_fun at h8
    simp only [h5] at h8
    unfold I delete_vertex at h8
    let c2 := coord_change_count SC (J 0) (J 1)
    have c2pos : 0 < c2 := by {
      apply ccc_pos _ _ hs
      simp only [ne_eq, Fin.zero_eq_one_iff, Nat.add_eq_right]
      omega
    }
    let j3 := @insert_index SC n1 hn1 j1 i1
    have h9 : (ccc_fun SC J j3).1 = c2 + SC.n:= by {
      simp only [← h8]
      apply ccc_add SC J hs
      simp only [Fin.zero_le, true_and]
      suffices h9 : j3 ≠ j1 by {
        rw [h4] at h9
        exact Fin.one_le_of_ne_zero h9
      }
      apply insert_index_ne
    }
    have h10 : c2 + SC.n ≤ SC.n := by {
      rw [←h9]
      exact Fin.is_le (ccc_fun SC J j3)
    }
    simp only [add_le_iff_nonpos_left, nonpos_iff_eq_zero] at h10
    omega
  }
  simp only [h4, IsEmpty.forall_iff, ne_eq, not_false_eq_true, forall_const, true_and]
  have h2 : I 0 = J 0 := by {
    unfold I delete_vertex
    congr!
    unfold insert_index
    simpa only [Fin.val_zero, Fin.val_pos_iff, zero_add, Fin.mk_eq_zero,
        ite_eq_left_iff, not_lt,Fin.le_zero_iff, one_ne_zero, imp_false]
  }
  have h3 : ∀ j3, ccc_fun SC J j3 = j3 := by {
    apply is_id_of_strict_mono
    apply ccc_fun_strict_mono SC J hs
  }
  symm
  by_contra h5
  obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 _ _ h5
  have h6 : ccc_fun SC I i1 = ccc_fun SC J j2 := by {
    unfold ccc_fun
    simp [h2]
    congr
    rw [hi1]
    rfl
  }
  rw [h1, h3 j2] at h6
  contrapose h6
  apply insert_index_ne
}

lemma case_D_iff_not_end_1 I (hs : simplex SC n1 I) j
    (h1 : ccc_fun SC I = @insert_index SC n1 hn1 j) :
    case_D SC I ↔ j ≠ 0 ∧ j ≠ Fin.last SC.n := by {
  rw [ccc_fun_case_D_iff SC I hs, h1]
  have h2 : j ≠ 0 := by {
    intro h3
    apply @insert_index_ne SC n1 hn1 j 0
    rw [←h1, h3]
    unfold ccc_fun coord_change_count
    simp only [ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty, Fin.zero_eta]
  }
  simp only [ne_eq, h2, not_false_eq_true, true_and]
  apply Iff.intro
  {
    intro h3 h4
    apply @insert_index_ne SC n1 hn1 j (Fin.last n1)
    rw [h3,h4]
  }
  {
    intro h3
    have h32 : Fin.last SC.n ≠ j := fun a ↦ h3 (Eq.symm a)
    obtain ⟨i2, hi2⟩  := @almost_surjective_of_insert_index SC n1 hn1 j (Fin.last SC.n) h32
    apply le_antisymm
    exact Fin.le_last (insert_index SC j (Fin.last n1))
    rw [hi2]
    have h4 := @insert_index_strict_mono SC n1 hn1 j
    rw [h4.le_iff_le]
    exact Fin.le_last i2
  }
}

lemma case_D_iff_not_end_2 J (hs : simplex SC SC.n J) j :
    case_D SC (@delete_vertex SC n1 hn1 j J) ↔ j ≠ 0 ∧ j ≠ Fin.last SC.n := by {
  let I := @delete_vertex SC n1 hn1 j J
  have hsI : simplex SC n1 I := by {
    suffices h2 : is_face SC I J by exact h2.1
    rw [@child_simplex_char SC n1 hn1 I J hs]
    use j
  }
  obtain ⟨j2, hj2⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hsI
  have h1 := @delete_vertex_ccc_fun_match SC n1 hn1 J hs j j2 hj2
  by_cases h2 : j = 0
  {
    rw [ccc_fun_case_D_iff SC I hsI]
    simp only [h2, ne_eq, not_true_eq_false, Fin.zero_eq_last_iff, false_and, iff_false]
    rw [←h1.1 h2, hj2]
    apply insert_index_ne
  }
  rw [@case_D_iff_not_end_1 SC n1 hn1 I hsI]
  rw [hj2, ← h1.2 h2]
}

lemma same_delete_index_eq_iff J1 J2 j
    (h1 : @delete_vertex SC n1 hn1 j J1 = @delete_vertex SC n1 hn1 j J2)
    : J1 = J2 ↔ J1 j = J2 j := by {
  apply Iff.intro (fun a ↦ congrFun a j)
  intro h2
  ext j2
  by_cases h3 : j2 = j
  rw [h3,h2]
  obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 j j2 h3
  rw [hi1]
  exact congrFun h1 i1
}


lemma case_D_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_D SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by {
  obtain ⟨ j1, hj1 ⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hs
  have h2 : j1 ≠ 0 ∧ j1 ≠ Fin.last SC.n := by {
    rw [←case_D_iff_not_end_1 SC I hs j1 hj1]
    exact h1
  }
  have h3 : ∃ (i1: Fin (n1 + 1)), i1.1 + 1 = j1.1 := by {
    obtain ⟨a, ha⟩ := Fin.exists_succ_eq_of_ne_zero h2.1
    rw [← ha]
    simp only [Fin.val_succ, Nat.add_right_cancel_iff]
    use ⟨ a.1, by {rw [hn1]; exact a.2}⟩
  }
  obtain ⟨ i1, hi1⟩ := h3
  have h32 : i1 ≤ i1 + 1 := by {
    refine Fin.le_of_lt ?_
    refine Fin.lt_add_one_iff.mpr ?_
    show i1.1 < n1
    have h3 := Fin.val_lt_last h2.2
    omega
  }
  have h11 := @surround_index SC n1 hn1 j1 i1 hi1 h2.2
  have h12 : @insert_index SC n1 hn1 j1 i1 ≤ j1 ∧ j1 ≤ @insert_index SC n1 hn1 j1 (i1+1) := by {
    rw [Fin.le_def, Fin.le_def, ←h11.2]
    apply And.intro
    rw [←h11.1]
    apply Nat.le_add_right
    apply Nat.le_add_right
  }
  have h3 : coord_change_count SC (I i1) (I (i1+1)) = 2 := by {
    have h3 : (@insert_index SC n1 hn1 j1 i1).1 + 2
        = (@insert_index SC n1 hn1 j1 (i1 +1)).1 := by {
      rw [← h11.2, ←h11.1]
    }
    have h4 : (ccc_fun SC I (i1+1)).1 = (ccc_fun SC I i1).1
        + coord_change_count SC (I i1) (I (i1 + 1)) := by {
      apply ccc_add SC I hs
      simp only [Fin.zero_le, true_and, h32]
    }
    rw [← hj1, h4 ] at h3
    simp only [Nat.add_left_cancel_iff] at h3
    exact h3.symm
  }
  have h4 : ∃ k1, ∃ k2, k1 ≠ k2 ∧ {k | I i1 k ≠ I (i1 +1) k} = {k1, k2} := by {
    unfold coord_change_count at h3
    rw [Finset.card_eq_two] at h3
    convert h3
    simp only [ne_eq]
    rw [←Finset.coe_eq_pair]
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
  }
  obtain ⟨k1, ⟨k2, h4⟩ ⟩ := h4
  have hk1 : I i1 k1 ≠ I (i1+1) k1 := by {
    have h5 := Set.mem_insert k1 {k2}
    rwa [←h4.2] at h5
  }
  have hk2 : I i1 k2 ≠ I (i1+1) k2 := by {
    have h5 : k2 ∈ ({k1, k2} : Set _) := Set.mem_insert_of_mem k1 rfl
    rwa [←h4.2] at h5
  }
  have h5 k3 : I i1 k3 ≠ I (i1+1) k3 → ∃ J3,
      I = @delete_vertex SC n1 hn1 j1 J3 ∧ is_face SC I J3 ∧ J3 j1 k3 ≠ I i1 k3 := by {
    intro h21
    let ins : SC.G := fun k ↦ if k = k3 then I (i1 + 1) k else I i1 k
    obtain ⟨J3, hJ3⟩ := @insert_vertex SC n1 hn1 I ins j1
    have h6 : ∀ k, I i1 k ≤ ins k ∧ ins k ≤ I (i1+1) k := by {
      intro k
      unfold ins
      have h13 : I i1 k3 ≤ I (i1+1) k3 := monotone_1_of_simplex SC I hs _ _ h32 k3
      by_cases h12 : k = k3
      simp only [h12, ↓reduceIte, le_refl, and_true, ge_iff_le]
      exact monotone_1_of_simplex SC I hs _ _ h32 k3
      simp only [h12, ↓reduceIte, le_refl, true_and, ge_iff_le]
      exact monotone_1_of_simplex SC I hs _ _ h32 k
    }
    have h22 : J3 j1 k3 ≠ I i1 k3 := by {
      rw [hJ3.2]
      unfold ins
      simp only [↓reduceIte, ne_eq]
      exact h21.symm
    }
    have h23 : ∃ k4, k3 ≠ k4 ∧ I i1 k4 ≠ I (i1+1) k4 := by {
      by_cases h24 : k3 = k1
      use k2
      rw [h24]
      apply And.intro h4.1 hk2
      use k1
    }
    have h7 : ins ∉ Set.range I := by {
      intro h9
      obtain ⟨i2,hi2⟩ := h9
      rw [forall_and, ← hi2] at h6
      rw [← monotone_2_of_simplex _ _ hs,← monotone_2_of_simplex _ _ hs] at h6
      have h13 : i2 = i1 ∨ i2 = i1 + 1 := by {
        refine (WCovBy.le_and_le_iff ?_).mp h6
        apply And.intro h32
        intro i3 h33
        simp only [not_lt]
        exact Fin.add_one_le_of_lt h33
      }
      cases' h13 with h13 h13
      apply h22
      rw [hJ3.2, ←hi2, h13]
      obtain ⟨k4, hk4⟩ := h23
      apply hk4.2
      rw [←h13, hi2]
      unfold ins
      simp only [right_eq_ite_iff]
      intro h33
      exact False.elim $ hk4.1 h33.symm
    }
    use J3
    apply And.intro hJ3.1 (And.intro _ h22)
    apply @parent_simplex_case_D SC n1 hn1 I hs J3 _ _ hi1 hJ3.1
    rwa [hJ3.2]
    rwa [hJ3.2]
  }
  obtain ⟨J1, hJ1⟩ := h5 k1 hk1
  obtain ⟨J2, hJ2⟩ := h5 k2 hk2
  have h6 J3 : I = @delete_vertex SC n1 hn1 j1 J3 → is_face SC I J3
    → ∀ k, I i1 k ≤ J3 j1 k ∧ J3 j1 k ≤ I (i1+1) k := by {
    intro h14 h13 k3
    rw [h14]
    apply And.intro
    apply monotone_1_of_simplex SC J3 h13.2.1 _ _ h12.1
    apply monotone_1_of_simplex SC J3 h13.2.1 _ _ h12.2
  }
  have h7 J3 k3 : I = @delete_vertex SC n1 hn1 j1 J3 ∧ is_face SC I J3 ∧ J3 j1 k3 ≠ I i1 k3
      → J3 j1 k3 = I (i1+1) k3 ∧ ∀ k4, k3 ≠ k4 → J3 j1 k4 = I i1 k4 := by {
    intro h9
    have h6 := h6 J3 h9.1 h9.2.1
    have h31 := h3
    rw [h9.1] at h31
    have h21 := ccc_add SC J3 h9.2.1.2.1 _ _ _ h12
    unfold delete_vertex at h31
    rw [h31] at h21
    have h22 c1 c2 : 2 = c1 + c2 → 0 < c2 → c1 ≤ 1 := by omega
    have h23 : coord_change_count SC (I i1) (J3 j1) ≤ 1 := by {
      rw [h9.1]
      apply h22 _ _ h21
      apply ccc_pos SC
      exact h9.2.1.2.1
      symm
      apply insert_index_ne
    }
    apply And.intro
    {
      apply le_antisymm (h6 k3).2
      rw [Fin.le_def]
      have h24 := le_add_one_of_simplex SC I hs (i1+1) i1 k3
      apply le_trans h24
      apply Fin.val_add_one_le_of_lt (lt_of_le_of_ne (h6 k3).1 h9.2.2.symm)
    }
    intro k4 hk4
    contrapose! h23
    refine Finset.one_lt_card_iff.mpr ?_
    use k3, k4
    simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    exact And.intro h9.2.2.symm ( And.intro h23.symm hk4)
  }
  refine Finset.card_eq_two.mpr ?_
  use J1, J2
  apply And.intro
  {
    have h71 := (h7 J1 k1 hJ1).2 k2 h4.1
    intro h9
    apply hJ2.2.2
    rw [←h9, h71]
  }
  apply subset_antisymm
  {
    intro J3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    intro hJ3
    have h14 := (@child_simplex_char SC n1 hn1 I J3 hJ3.2.1).mp hJ3
    obtain ⟨j2, hj2⟩ := h14
    rw [hj2] at hj1
    have h13 := @delete_vertex_ccc_fun_match SC n1 hn1 J3 hJ3.2.1 j2 j1 hj1
    have h15 := @case_D_iff_not_end_2 SC n1 hn1 J3 hJ3.2.1 j2
    rw [←hj2] at h15
    have h16 : j2 = j1 := h13.2 (h15.mp h1).1
    rw [h16] at hj2
    rw [same_delete_index_eq_iff SC J3 J1 j1, same_delete_index_eq_iff SC J3 J2 j1]
    have h71 := h7 J1 k1 hJ1
    have h72 := h7 J2 k2 hJ2
    have h18 : ∃ k5, J3 j1 k5 ≠ I i1 k5 := by {
      suffices h19 : J3 j1 ≠ I i1 by exact Function.ne_iff.mp h19
      intro h19
      apply @insert_index_ne SC n1 hn1 j1 i1
      apply hJ3.2.1.1
      rw [h19, hj2]
      rfl
    }
    obtain ⟨k5, hk5⟩ := h18
    have h73 := h7 J3 k5 ⟨hj2, ⟨ hJ3, hk5⟩ ⟩
    clear h15 h13
    have h19 : k5 = k1 ∨ k5 = k2 := by {
      have h21 : I i1 k5 ≠ I (i1+1) k5 := by {
        rw [←h73.1]
        exact hk5.symm
      }
      exact h4.2.subset h21
    }
    have h20 (J4 : _ → SC.G) : (J4 j1 k5 = I (i1+1) k5 ∧ ∀ k4, k5 ≠ k4 → J4 j1 k4 = I i1 k4)
        → J3 j1 = J4 j1:= by {
      intro h21
      apply funext
      intro k6
      by_cases h22 : k5 = k6
      rw [←h22,h21.1,h73.1]
      rw [h21.2 k6 h22, h73.2 k6 h22]
    }
    cases h19
    left
    rename_i h21
    apply h20
    rwa [h21]
    right
    rename_i h21
    apply h20
    rwa [h21]
    rw [←hJ2.1, ←hj2]
    any_goals exact hn1
    rw [←hJ1.1, ←hj2]
  }
  {
    refine Finset.insert_subset ?_ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hJ1.2.1
    simp only [Finset.singleton_subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hJ2.2.1
  }
}


lemma unique_const_ABC {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) k1 q1
    (h1 : ∀ i, I i k1 = q1): ∀ k2, k1 ≠ k2 → I 0 k2 ≠ I (Fin.last n1) k2 := by {
  intro k2 h3 h2
  let s : Finset (Fin SC.n) := {i | I 0 i ≠ I (Fin.last n1) i}
  have h4 : n1 ≤ s.card := by {
    obtain ⟨j, hj⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hs
    show n1 ≤ (ccc_fun SC I (Fin.last n1)).1
    rw [hj]
    unfold insert_index
    simp only [Fin.val_last]
    by_cases h11 : n1 < j.1
    simp only [h11, ↓reduceIte, le_refl]
    simp only [h11, ↓reduceIte, le_add_iff_nonneg_right, zero_le]
  }
  have h6 : 2 ≤ sᶜ.card := by {
    show 1 < sᶜ.card
    rw [Finset.one_lt_card]
    use k2
    unfold s
    simp only [ne_eq, Finset.compl_filter, Decidable.not_not, Finset.mem_filter,
        Finset.mem_univ,h2, and_self, true_and]
    use k1
    apply And.intro _ h3.symm
    rw [h1,h1]
  }
  have h7 := add_le_add h4 h6
  simp only [Finset.card_add_card_compl, Fintype.card_fin] at h7
  rw [←hn1,add_le_add_iff_left] at h7
  simp only [Nat.not_ofNat_le_one] at h7
}


lemma case_AC_ex_unique I (hs : simplex SC n1 I) k1 q
    (hABC : ∀ i, I i k1 = q) (hAC : q ≠ Fin.last SC.p)
    : ∃! J, I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J := by {
  have h1 k2 : I 0 k2 ≠ Fin.last SC.p := by {
    intro h11
    have h12 : k1 ≠ k2 := by {
      intro h13
      apply hAC
      rw [←hABC 0,h13,h11]
    }
    apply @unique_const_ABC SC n1 hn1 I hs k1 q hABC k2 h12
    apply le_antisymm
    apply monotone_1_of_simplex SC I hs
    exact Fin.zero_le (Fin.last n1)
    rw [h11]
    exact Fin.le_last (I (Fin.last n1) k2)
  }
  let ins2 : SC.G := fun k ↦ (I 0 k) + 1
  have h2 k : (ins2 k).1 = (I 0 k).1 + 1 := by {
    apply Fin.val_add_one_of_lt
    rw [Fin.lt_last_iff_ne_last]
    exact h1 k
  }
  obtain ⟨J1, hJ1⟩ := @insert_vertex SC n1 hn1 I ins2 (Fin.last SC.n)
  have h3 : J1 (Fin.last SC.n) ≠ I (Fin.last n1) := by {
    intro h12
    have h11 : I 0 k1 = I 0 k1 + 1 := by {
      show I 0 k1 = ins2 k1
      rw [←hJ1.2, h12,hABC,hABC]
    }
    simp only [left_eq_add, Fin.one_eq_zero_iff, Nat.add_eq_right] at h11
    apply @p_ne_zero_of_cube SC n1 hn1
    simp only [Fin.last_eq_zero_iff, h11]
  }
  have h4 : is_face SC I J1 := by {
    apply parent_simplex_case_AC SC I hs J1 (Fin.last SC.n) rfl hJ1.1 h3
    intro k2
    rw [hJ1.2]
    apply And.intro
    {
      rw [Fin.le_def, h2 k2]
      apply le_add_one_of_simplex SC I hs
    }
    rw [h2 k2]
  }
  use J1
  simp only
  apply And.intro (And.intro hJ1.1 h4)
  intro J2 hJ2
  rw [@same_delete_index_eq_iff SC n1 hn1 _ _ _ (hJ2.1.symm.trans hJ1.1)]
  rw [hJ1.2]
  apply funext
  intro k1
  ext
  have h5 := last_eq_first_add_one SC J2 hJ2.2.2.1 k1
  rw [h5, h2 k1]
  suffices h6 : I 0 = J2 0 by {rw [h6]}
  rw [hJ2.1]
  unfold delete_vertex insert_index
  congr!
  simp only [Fin.val_zero, Fin.val_last, zero_add, ite_eq_left_iff,
    not_lt, nonpos_iff_eq_zero,one_ne_zero, imp_false]
  rw [←hn1]
  omega
}

lemma case_B_not_last I (h1 : case_B SC I) J
    (h2 : I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J) : False := by {
  have h3 := last_eq_first_add_one SC J h2.2.2.1
  obtain ⟨k1, hk1⟩ := h1
  have h4 : I 0 = J 0 := by {
    rw [h2.1]
    unfold delete_vertex insert_index
    congr!
    simp only [Fin.val_zero, Fin.val_last, zero_add, ite_eq_left_iff,
        not_lt, nonpos_iff_eq_zero,one_ne_zero, imp_false]
    rw [←hn1]
    omega
  }
  have h5 := (J (Fin.last SC.n) k1).is_le
  rw [h3 k1,←h4,hk1 0] at h5
  contrapose! h5
  exact lt_add_one SC.p
}


lemma case_BC_ex_unique I (hs : simplex SC n1 I) k1 q
    (hABC : ∀ i, I i k1 = q) (hBC : q ≠ 0)
    : ∃! J, I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J := by {
  have h1 k2 : I (Fin.last n1) k2 ≠ 0 := by {
    intro h11
    have h12 : k1 ≠ k2 := by {
      intro h13
      apply hBC
      rw [←hABC (Fin.last n1),h13,h11]
    }
    apply @unique_const_ABC SC n1 hn1 I hs k1 q hABC k2 h12
    apply le_antisymm
    apply monotone_1_of_simplex SC I hs
    exact Fin.zero_le (Fin.last n1)
    rw [h11]
    exact Fin.zero_le (I 0 k2)
  }
  let ins2 : SC.G := fun k ↦ (I (Fin.last n1) k) - 1
  have h22 k := Fin.val_sub_one_of_ne_zero (h1 k)
  have h21 k : (ins2 k).1 + 1 = (I (Fin.last n1) k).1  := by {
    rw [h22]
    apply Nat.sub_one_add_one ( Fin.val_ne_zero_iff.mpr (h1 k))
  }
  obtain ⟨J1, hJ1⟩ := @insert_vertex SC n1 hn1 I ins2 0
  have h3 : J1 0 ≠ I 0 := by {
    intro h12
    have h11 : (ins2 k1).1 + 1 = ins2 k1 := by {
      rw [h21 k1, hABC, ←hJ1.2,h12,hABC]
    }
    simp only [Nat.add_eq_left, one_ne_zero] at h11
  }
  have h4 : is_face SC I J1 := by {
    apply parent_simplex_case_BC SC I hs J1 hJ1.1 h3
    intro k2
    rw [hJ1.2]
    apply And.intro
    rw [Fin.le_def, ←add_le_add_iff_right 1, h21 k2]
    exact le_add_one_of_simplex SC I hs (Fin.last n1) 0 k2
    rw [h21 k2]
  }
  use J1
  simp only
  apply And.intro (And.intro hJ1.1 h4)
  intro J2 hJ2
  rw [@same_delete_index_eq_iff SC n1 hn1 _ _ _ (hJ2.1.symm.trans hJ1.1), hJ1.2]
  apply funext
  intro k1
  ext
  have h5 := last_eq_first_add_one SC J2 hJ2.2.2.1 k1
  have h6 : I (Fin.last n1) = J2 (Fin.last SC.n) := by {
    rw [hJ2.1]
    unfold delete_vertex insert_index
    simp only [Fin.val_last, Fin.val_zero, not_lt_zero, ↓reduceIte]
    congr!
  }
  rw [←h6, ←h21 k1] at h5
  omega
}

lemma zero_ne_last {hn1 : n1 + 1 = SC.n} : 0 ≠ Fin.last SC.n := by {
  simp only [ne_eq, Fin.zero_eq_last_iff]
  rw [←hn1]
  omega
}

lemma case_A_not_zero I (h1 : case_A SC I) J
    (h2 : I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J) : False := by {
  have h3 := last_eq_first_add_one SC J h2.2.2.1
  obtain ⟨k1, hk1⟩ := h1
  have h4 : I (Fin.last n1) = J (Fin.last SC.n) := by {
    rw [h2.1]
    unfold delete_vertex insert_index
    simp only [Fin.val_last, Fin.val_zero, not_lt_zero, ↓reduceIte]
    congr!
  }
  apply Nat.zero_ne_add_one (J 0 k1).1
  rw [←h3 k1,← h4,hk1]
  rfl
}



lemma case_ABC_count_disj {hn1 : n1 + 1 = SC.n} I k1 q
    (hABC : ∀ i, I i k1 = q) : Finset.card { J | is_face SC I J}
    = Finset.card {J | I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J}
    + Finset.card {J | I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J} := by {
  have hnd : ¬ case_D SC I := by {
    contrapose! hABC
    exact hABC k1 q
  }
  rw [←Finset.card_union_of_disjoint]
  congr
  ext J
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  apply Iff.intro
  {
    intro h1
    simp only [h1, and_true]
    rw [child_simplex_char] at h1
    obtain ⟨j1, hj1⟩ := h1
    have h2 := @case_D_iff_not_end_2 SC n1 hn1 J h1.2.1 j1
    rw [hj1,h2] at hnd
    have h3 := Decidable.or_iff_not_not_and_not.mpr hnd
    cases' h3 with h3 h3
    rw [hj1,h3]
    exact Or.inl rfl
    rw [hj1,h3]
    exact Or.inr rfl
    · exact hn1
    · exact h1.2.1
  }
  {
    intro h1
    rw [←or_and_right] at h1
    exact h1.2
  }
  apply Finset.disjoint_filter.mpr
  intro J h1 h2 h3
  apply @zero_ne_last SC n1 hn1
  apply @delete_vertex_inj SC n1 hn1 J h2.2.2.1
  rw [←h2.1,←h3.1]
}


lemma case_C_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_C SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by {
  obtain ⟨k1,q, h1⟩  := h1
  have h2 := @case_AC_ex_unique SC n1 hn1 I hs k1 q h1.2 h1.1.2
  have h3 := @case_BC_ex_unique SC n1 hn1 I hs k1 q h1.2 h1.1.1
  rw [Fintype.existsUnique_iff_card_one] at h2 h3
  rw [case_ABC_count_disj SC I k1 q h1.2,h2,h3]
  exact hn1
}

lemma case_B_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h2 : case_B SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 1 := by {
  obtain ⟨k1, h1⟩  := id h2
  have h4 : Fin.last SC.p ≠ 0 := @p_ne_zero_of_cube SC n1 hn1
  have h3 := @case_BC_ex_unique SC n1 hn1 I hs k1 _ h1 h4
  rw [Fintype.existsUnique_iff_card_one] at h3
  rw [case_ABC_count_disj SC I k1 (Fin.last SC.p) h1, h3]
  simp only [Nat.add_eq_left]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro J h5
  apply case_B_not_last SC I h2
  exact hn1
}

lemma case_A_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h2 : case_A SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 1 := by {
  obtain ⟨k1, h1⟩  := id h2
  have h4 : Fin.last SC.p ≠ 0 := @p_ne_zero_of_cube SC n1 hn1
  have h3 := @case_AC_ex_unique SC n1 hn1 I hs k1 _ h1 h4.symm
  rw [Fintype.existsUnique_iff_card_one] at h3
  rw [case_ABC_count_disj SC I k1 0 h1, h3]
  simp only [Nat.add_eq_right]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro J h5
  apply case_A_not_zero SC I h2
  exact hn1
}

end cases_ABCD

-- used in other file
lemma boundary_is_A_or_B {hn1 : n1 + 1 = SC.n} I (hbf : @is_boundary_face SC n1 I)
    : case_A SC I ∨ case_B SC I := by {
  have hs : simplex SC n1 I := by {
    obtain ⟨J,hJ⟩ := hbf
    exact hJ.1.1
  }
  unfold is_boundary_face at hbf
  rw [Fintype.existsUnique_iff_card_one] at hbf
  have h1 := one_of_ABCD SC I
  rw [←or_assoc] at h1
  cases' h1 with h1 h1
  assumption
  cases' h1 with h1 h1
  rw [@case_C_parent_count SC n1 hn1 I hs h1] at hbf
  simp only [OfNat.ofNat_ne_one] at hbf
  rw [@case_D_parent_count SC n1 hn1 I hs h1] at hbf
  simp only [OfNat.ofNat_ne_one] at hbf
}

-- used in other file
lemma case_B_boundary {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I)
    (h1 : case_B SC I) : is_boundary_face SC I :=
  (Fintype.existsUnique_iff_card_one _).mpr (@case_B_parent_count SC n1 hn1 I hs h1)


-- used in other file
lemma parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) :
    Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} ∈ {c | c = 1 ∨ c = 2} := by {
  simp only [Set.mem_setOf_eq]
  have h1 := one_of_ABCD SC I
  rw [←or_assoc] at h1
  cases' h1 with h1 h1
  left
  cases' h1 with h2 h2
  exact @case_A_parent_count SC n1 hn1 I hs h2
  exact @case_B_parent_count SC n1 hn1 I hs h2
  right
  cases' h1 with h2 h2
  exact @case_C_parent_count SC n1 hn1 I hs h2
  exact @case_D_parent_count SC n1 hn1 I hs h2
}
end

-- ==== cubical_sperner
section



open Classical



section completeness

lemma complete_simplex_iff {SC} m I(hs : simplex SC m I) :
    complete_simplex SC m I ↔ ∀ c, c ≤ m → ∃ i, SC.RL (I i) = c := by {
  apply Iff.intro
  {
    intro h1 c hc
    rwa [← Set.mem_range, h1.2, Set.mem_setOf_eq]
  }
  {
    intro c1
    apply And.intro hs
    refine Set.toFinset_inj.mp ?_
    refine (Finset.eq_iff_card_ge_of_superset ?_).mp ?_
    {
      simp only [Set.toFinset_range, Set.toFinset_subset, Finset.coe_image, Finset.coe_univ,
        Set.image_univ]
      intro c hc
      simp only [Set.mem_range, c1 c hc]
    }
    let f1 := fun (j : ℕ ) ↦ SC.RL (I (Fin.ofNat _ j))
    apply Finset.card_le_card_of_surjOn f1
    intro j h1
    simp only [Set.toFinset_range, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_range] at h1
    obtain ⟨ i, hi⟩ := h1
    use i
    simp only [Set.coe_toFinset, Set.mem_setOf_eq]
    apply And.intro (Fin.is_le i)
    unfold f1
    rw [← hi]
    simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self]
  }
}


lemma rl_inj_of_complete {SC} m I (hcs : complete_simplex SC m I):
    ∀ i1 i2, SC.RL (I i1) = SC.RL (I i2) → i1 = i2 := by {
  let f1 : Fin (m+1) → Fin (m+1) := fun j ↦ Fin.ofNat _ (SC.RL (I j))
  suffices h1 : Function.Injective f1 by {
    intro i1 i2 h2
    apply h1
    unfold f1
    rw [h2]
  }
  have h2 := hcs.2
  apply Function.Surjective.injective_of_finite
  rfl
  rw [complete_simplex_iff _ _ hcs.1] at hcs
  intro c
  obtain ⟨a, ha⟩ := hcs c (Fin.is_le c)
  use a
  unfold f1
  rw [ha]
  exact Fin.cast_val_eq_self c
}


lemma char_complete_face {SC n1 hn1} I J (hs : simplex SC SC.n J) :
    complete_simplex SC n1 I ∧ is_face SC I J
    ↔ ∃ i, I = @delete_vertex SC n1 hn1 i J
    ∧ ∀ (c:ℕ ), c ≤ n1 → ∃ i2, i2 ≠ i ∧ SC.RL (J i2) = c := by {
  apply Iff.intro
  {
    rw [child_simplex_char]
    intro h1
    obtain ⟨i, hi1 ⟩ := h1.2
    use i
    apply And.intro hi1
    intro c hc
    have h2 := (complete_simplex_iff n1 I h1.1.1).mp h1.1 c hc
    obtain ⟨j, hj⟩ := h2
    rw [← hj, hi1]
    unfold delete_vertex
    use @insert_index SC n1 hn1 i j
    apply And.intro _ rfl
    apply insert_index_ne
    exact hn1
    exact hs
  }
  {
    intro h1
    obtain ⟨i, hi1 ⟩ := h1
    have hface : is_face SC I J := by {
      rw [child_simplex_char]
      use i
      exact hi1.1
      exact hs
    }
    apply And.intro _ hface
    rw [complete_simplex_iff n1 I hface.1]
    intro c hc
    obtain ⟨i2, hi2⟩ := hi1.2 c hc
    have h3 := @almost_surjective_of_insert_index SC n1 hn1 i i2 hi2.1
    obtain ⟨j, hj⟩ := h3
    use j
    rw [hi1.1, ← hi2.2, hj]
    rfl
  }
}


lemma complete_child_uniq {SC n1} {hn1 : n1 + 1 = SC.n} J (hcs : complete_simplex SC SC.n J) :
    ∃! (I : Fin (n1+1) → SC.G), complete_simplex SC n1 I ∧ is_face SC I J := by {
  have h4 : ∃ i, SC.RL (J i) = SC.n := by {
    rw [← Set.mem_range, hcs.2]
    simp only [Set.mem_setOf_eq, le_refl]
  }
  obtain ⟨ i, hi⟩ := h4
  let I := @delete_vertex SC n1 hn1 i J
  have hs2 : simplex SC n1 I := by {
    apply delete_vertex_simplex
    exact hcs.1
  }
  use I
  have h1 : complete_simplex SC n1 I ∧ is_face SC I J := by
  {
    rw [@char_complete_face SC n1 hn1 _ _ hcs.1]
    use i
    apply And.intro rfl
    rw [complete_simplex_iff] at hcs
    {
      intro c hc
      have h3 : c ≤ SC.n := by omega
      obtain ⟨i2, hi2 ⟩ := hcs c h3
      use i2
      apply And.intro _ hi2
      intro h4
      rw [h4, hi, ← hn1] at hi2
      rw [← hi2] at hc
      revert hc
      simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, imp_self]
    }
    {
      exact hcs.1
    }
  }
  simp only
  apply And.intro h1
  intro I2 h2
  rw [@char_complete_face SC n1 hn1 _ _ hcs.1] at h2
  obtain ⟨ i2, hi2 ⟩ := h2
  have h2 : SC.RL (J i2) = SC.n := by {
    let c2 := SC.RL (J i2)
    suffices h3 : ¬ (c2 ≤ n1) by {
      apply le_antisymm (SC.rl_proper (J i2)).1
      omega
    }
    intro h2
    obtain ⟨i3, hi3⟩ := hi2.2 c2 h2
    apply hi3.1
    apply rl_inj_of_complete SC.n J hcs
    exact hi3.2
  }
  suffices h3 : i2 = i by {
    rw [hi2.1, h3]
  }
  apply rl_inj_of_complete SC.n J hcs
  rw [h2]
  exact (Eq.symm hi)
}


lemma incomplete_childs {SC n1} {hn1 : n1 + 1 = SC.n} J (hs : simplex SC SC.n J)
    (hnc : ¬ complete_simplex SC SC.n J):
    Even (Finset.card { I : Fin (n1 + 1) → SC.G | complete_simplex SC n1 I ∧ is_face SC I J}) := by {
  let S : Finset _:= { I : Fin (n1 + 1) → SC.G | complete_simplex SC n1 I ∧ is_face SC I J}
  let c := S.card
  suffices h1 : c > 0 → c = 2 by {
    suffices h2 : Even c by {exact h2}
    by_cases h3 : c > 0
    rw [h1 h3]
    exact even_two
    use 0
    omega
  }
  intro cpos
  have h1 : Finset.Nonempty S := by {
    apply Finset.card_ne_zero.mp
    omega
  }
  obtain ⟨I1, h1 ⟩ := h1
  have hI1S := h1
  unfold S at h1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1
  obtain ⟨i1, hi1 ⟩ := (@char_complete_face SC n1 hn1 I1 J hs).mp h1
  apply Finset.card_eq_two.mpr
  have h2 : SC.RL (J i1) ≤ n1 := by {
    by_contra h3
    apply hnc
    rw [complete_simplex_iff _ _ hs]
    intro c hc
    by_cases h4 : c ≤ n1
    {
      obtain ⟨i2, hi2 ⟩ := hi1.2 c h4
      use i2
      exact hi2.2
    }
    {
      use i1
      have h6 : c = SC.n := le_antisymm hc (le_of_eq_of_le hn1.symm (not_le.mp h4))
      rw [h6]
      apply le_antisymm (SC.rl_proper (J i1)).1
      exact le_of_eq_of_le hn1.symm (not_le.mp h3)
    }
  }
  obtain ⟨i2, hi2⟩ := hi1.2 (SC.RL (J i1)) h2
  let I2 := @delete_vertex SC n1 hn1 i2 J
  have hI2S : I2 ∈ S := by {
    unfold S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [@char_complete_face SC n1 hn1 I2 J hs]
    use i2
    apply And.intro rfl
    intro c hc
    obtain ⟨i3, hi3⟩ := hi1.2 c hc
    by_cases h4 : i3 = i2
    {
      use i1
      rw [← hi3.2,h4, hi2.2]
      exact And.intro hi2.1.symm rfl
    }
    {
      use i3
      exact And.imp_left (fun a ↦ h4) hi3
    }
  }
  use I1, I2
  apply And.intro
  {
    intro h3
    apply hi2.1
    apply @delete_vertex_inj SC n1 hn1 J hs
    rw [← hi1.1, h3]
  }
  ext I3
  simp only [Finset.mem_insert, Finset.mem_singleton]
  apply Iff.intro
  {
    intro h3
    unfold S at h3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h3
    have h31 := h3
    rw [@char_complete_face SC n1 hn1 I3 J hs] at h3
    obtain ⟨ i3, hi3 ⟩ := h3
    by_contra h4
    simp only [not_or] at h4
    rw [hi1.1] at h4
    have h7 : ∀ i4, ¬ (I3 = @delete_vertex SC n1 hn1 i4 J) → i4 ≠ i3 := by {
      intro i4 h8 h9
      apply h8
      rw [hi3.1, h9]
    }
    have h5 := @almost_surjective_of_insert_index SC n1 hn1 i3
    obtain ⟨ k1, hk1 ⟩ := h5 i1 (h7 i1 h4.1)
    obtain ⟨ k2, hk2 ⟩ := h5 i2 (h7 i2 h4.2)
    apply hi2.1
    suffices h7 : k1 = k2 by {
      rw [hk1, hk2, h7]
    }
    apply rl_inj_of_complete n1 I3 h31.1
    rw [hi3.1]
    unfold delete_vertex
    rw [← hk1, ← hk2]
    exact hi2.2.symm
  }
  {
    intro h5
    cases h5
    rename_i h9
    rwa [h9]
    rename_i h9
    rwa [h9]
  }
}


lemma complete_boundary_face_last {SC n1} {hn1 : n1 + 1 = SC.n} (I : Fin (n1 + 1) → SC.G)
    (hcbf : complete_boundary_face SC I) :
    ∀ i, ∀ j, j.1 + 1 = SC.n →  (I i j).1 = SC.p := by {
  intro i j hj
  revert i
  have h3 := @boundary_is_A_or_B SC n1 hn1 I hcbf.1
  have h1 : j.1 = n1 := by omega
  have h4 : ∀ n2, n2 ≤ n1 → ∃ i, SC.RL (I i) = n2 := by {
    intro n2 hn2
    rw [← Set.mem_range, hcbf.2.2]
    simp only [Set.mem_setOf_eq, hn2]
  }
  have h6 (j2 : Fin SC.n) : j2.1 ≤ n1 := by omega
  cases h3
  {
    rename_i h1
    obtain ⟨ j2, hj2⟩ := h1
    exfalso
    obtain ⟨i, hi⟩ := h4 j2.1 (h6 j2)
    have h5 := ((SC.rl_proper (I i)).2 j2).1 (hj2 i)
    exact h5 hi
  }
  {
    rename_i h1
    obtain ⟨ j2, hj2⟩ := h1
    have hj3 i : (I i j2).1 = SC.p := by {
      rw [hj2 i]
      exact Fin.val_last SC.p
    }
    suffices h3 : j = j2 by {
      intro i
      rw [h3, hj3 i]
    }
    have h3 := SC.rl_proper
    obtain ⟨i, hi⟩ := h4 n1 (Nat.le_refl n1)
    have h5 := ((SC.rl_proper (I i)).2 j2).2 (hj3 i)
    rw [hi] at h5
    ext
    rw [h1]
    exact Nat.le_antisymm h5 (h6 j2)
  }
}

end completeness



section handshake

variable {A B : Type*}
variable [Fintype A] [Fintype B]

lemma handshake_3 (r : A → B → Prop) (c : A → Prop)
    (h1 : ∀ a, c a ↔ Odd (Finset.card {b | r a b}))
    : Odd (Finset.card {a | c a}) ↔ Odd (∑ a, Finset.card {b | r a b}) := by {
  rw [Finset.odd_sum_iff_odd_card_odd]
  rw [iff_eq_eq]
  congr
  ext a
  exact h1 a
}

lemma handshake_2 (r : A → B → Prop)
    (c : A → Prop) (d : B → Prop)
    (h1 : ∀ a, c a ↔ Odd (Finset.card {b | r a b}))
    (h2 : ∀ b, d b ↔ Odd (Finset.card {a | r a b})) :
    Odd (Finset.card {a | c a}) → Odd (Finset.card {b | d b}) := by {
  intro h3
  have h5 : ∑ a, Finset.card {b | r a b} = ∑ b, Finset.card {a | r a b} := by {
    apply Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
  }
  let r2 b a := r a b
  rw [handshake_3 r2 d h2, ←h5]
  rwa [←handshake_3 r c h1]
}

lemma handshake_1 (r : A → B → Prop)
    (c1 c2 c3: A → Prop) (d1 d2: B → Prop)
    (h1 : ∀ b, d1 b → ∃! a, c2 a ∧ r a b)
    (h2 : ∀ b, d2 b → ¬ d1 b → Even (Finset.card { a | c2 a ∧ r a b}))
    (h3 : ∀ a, c3 a → Finset.card { b | r a b} ∈ {c | c = 1 ∨ c = 2})
    (h5 : ∀ a, c1 a ↔ (∃! b, r a b) ∧ c2 a)
    (h6 : ∀ a, c2 a → c3 a) (h7 : ∀ b, ∀ a, r a b → d2 b)
    : Odd (Finset.card {a : A | c1 a}) → Odd (Finset.card {b : B | d1 b}) := by {
  let r2 a b := c2 a ∧ r a b
  apply handshake_2 r2
  {
    intro a
    rw [h5]
    by_cases p1 : c2 a
    unfold r2
    simp only [p1, and_true, true_and]
    rw [Fintype.existsUnique_iff_card_one]
    apply Iff.intro
    {
      intro p2
      use 0
      rwa [mul_zero, zero_add]
    }
    {
      intro p2
      have p3 := h3 a (h6 a p1)
      simp only [Set.mem_setOf_eq] at p3
      cases p3
      rename_i p4
      exact p4
      rename_i p4
      rw [p4] at p2
      exfalso
      revert p2
      simp only [imp_false, Nat.not_odd_iff_even, even_two]
    }
    {
      unfold r2
      simp only [p1, and_false, false_and, Finset.filter_false, Finset.card_empty, Nat.not_odd_zero]
    }
  }
  {
    intro b
    by_cases p1 : d1 b
    {
      simp only [p1, true_iff]
      use 0
      rw [mul_zero, zero_add]
      rw [← Fintype.existsUnique_iff_card_one]
      exact h1 b p1
    }
    {
      simp only [p1, false_iff]
      intro p2
      have p5 : Finset.Nonempty {a | r2 a b} := by {
        have p3 : Odd (Finset.card { a | r2 a b}) := by {
          convert p2
        }
        apply Finset.card_ne_zero.mp
        intro p4
        revert p3
        rw [p4]
        simp only [Nat.not_odd_zero, imp_self]
      }
      have p3 : d2 b := by {
        obtain ⟨a, p6⟩ := p5
        apply h7 b a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at p6
        exact p6.2
      }
      revert p2
      have p4 := h2 b p3 p1
      simp only [imp_false, Nat.not_odd_iff_even]
      convert p4
    }
  }
}

end handshake



lemma odd_of_boundary_faces SC {n1} {hn1 : n1 + 1 = SC.n}:
    Odd (Finset.card { I : Fin (n1 + 1) → SC.G | complete_boundary_face SC I})
    → Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  apply handshake_1 (is_face SC)
  apply @complete_child_uniq SC n1 hn1
  apply @incomplete_childs SC n1 hn1
  apply @parent_count SC n1 hn1
  {
    intro I
    rfl
  }
  exact fun _ h1 ↦ h1.1
  exact fun _ _ h1 ↦ h1.2.1
}


section induction_step

variable (SC : SpernerCube)
variable {n1 : ℕ}


def child_map (v : Fin n1 → Fin (SC.p+1) ) : SC.G := fun i ↦
  match n1 with
  | 0 => Fin.last SC.p
  | Nat.succ _ => if i.1 + 1 = SC.n then Fin.last SC.p else v (Fin.ofNat _ i.1)

lemma child_map_last (v : Fin n1 → Fin (SC.p +1 ))
    : ∀ j, j.1 + 1 = SC.n → child_map SC v j = SC.p := by {
  intro j hj
  unfold child_map
  cases n1
  rfl
  simp only [hj, ↓reduceIte, Fin.val_last]
}

lemma child_map_applied [NeZero SC.n] {hn1 : n1 + 1 = SC.n} (v : Fin n1 → Fin (SC.p + 1))
    : ∀ (i : Fin n1), child_map SC v (Fin.ofNat _ i.1) = v i := by {
  intro i
  dsimp only [child_map]
  cases n1
  exact Fin.elim0 i
  rename_i n2
  simp only [Nat.succ_eq_add_one]
  have h5 : i.1 + 1 < SC.n := by omega
  have h2 : i.1 < SC.n := by omega
  have h3 := Fin.val_cast_of_lt h2
  rw [Fin.ofNat_eq_cast, h3]
  have h6 : i.1 + 1 ≠ SC.n := by omega
  simp only [h6, ↓reduceIte, Fin.ofNat_eq_cast, Fin.cast_val_eq_self]
}

lemma child_map_inj {hn1 : n1 + 1 = SC.n }: Function.Injective (@child_map SC n1) := by {
  intro v1 v2 h1
  ext i
  have h0 : NeZero SC.n := by {
    rw [← hn1]
    exact instNeZeroNatHAdd_1
  }
  rw [← child_map_applied SC v1]
  rw [← child_map_applied SC v2]
  rwa [h1]
  exact hn1
}

lemma child_map_surj_on {hn1 : n1 + 1 = SC.n} w
    (h1 : ∀ j, j.1 + 1 = SC.n → w j = SC.p)
    : ∃ v, @child_map SC n1 v = w := by {
  have h0 : NeZero SC.n := by {
    rw [← hn1]
    exact instNeZeroNatHAdd_1
  }
  let v2 : Fin n1 → Fin (SC.p +1) := fun i ↦ w (Fin.ofNat _ i.1)
  use v2
  apply funext
  intro i
  unfold child_map
  cases n1
  {
    simp only
    have h2 := h1 0
    simp only [Fin.val_zero, zero_add] at h2 hn1
    have h3 : i = 0 := by {
      have h4 := i.2
      simp only [← hn1] at h4
      ext
      simp only [Fin.val_zero]
      exact Nat.lt_one_iff.mp h4
    }
    rw [h3]
    exact Fin.eq_of_val_eq (id (Eq.symm (h2 hn1)))
  }
  {
    rename_i n2
    have h2 := h1 i
    by_cases h3 : i.1 +1 = SC.n
    {
      simp only [h3, ↓reduceIte]
      exact Eq.symm (Fin.eq_of_val_eq (h1 i h3))
    }
    simp only [h3, ↓reduceIte, Nat.succ_eq_add_one]
    unfold v2
    congr
    simp only [Fin.ofNat_eq_cast]
    rw [Fin.val_cast_of_lt]
    exact Fin.cast_val_eq_self i
    have h4 := i.2
    simp only [← hn1] at h3 h4
    omega
  }
}

def child_cube {hn1 : n1 + 1 = SC.n}: SpernerCube where
  n := n1
  p := SC.p
  RL := fun v ↦ SC.RL (child_map SC v)
  rl_proper := by {
    intro v
    have h0 : NeZero SC.n := by {
      rw [← hn1]
      exact instNeZeroNatHAdd_1
    }
    have h1 := child_map_last SC v
    have h2 := SC.rl_proper (child_map SC v)
    apply And.intro
    {
      have h3 := (h2.2 (Fin.ofNat _ n1)).2
      have h4 : n1 < SC.n := by omega
      simp only [Fin.ofNat_eq_cast] at h3
      rw [Fin.val_cast_of_lt h4] at h3
      apply h3
      apply child_map_last
      rw [Fin.val_cast_of_lt h4]
      exact hn1
    }
    intro i
    have h3 := h2.2 (Fin.ofNat _ i.1)
    rw [child_map_applied] at h3
    have h4 : (Fin.ofNat SC.n i.1).1 = i.1 := by {
      apply Fin.val_cast_of_lt
      omega
    }
    rwa [h4] at h3
    exact hn1
  }


end induction_step


lemma induction_start (SC : SpernerCube) (h0 : 0 = SC.n)
    : Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  use 0
  simp only [mul_zero, zero_add]
  rw [←Fintype.existsUnique_iff_card_one]
  let b : SC.G := fun _ ↦ 0
  let a : Fin (SC.n + 1) → SC.G := fun _ ↦ b
  use a
  simp only
  have h1 (x : Fin (SC.n+1)) : x = 0 := by {
    ext
    simp only [Fin.val_zero]
    rw [← Nat.lt_one_iff]
    apply Fin.val_lt_of_le x
    rw [←h0]
  }
  have hf (j : Fin SC.n) : False := by {
    apply Fin.elim0
    rwa [h0]
  }
  apply And.intro
  apply And.intro
  apply And.intro
  {
    intro x1 x2 _
    rw [h1 x1, h1 x2]
  }
  {
    intro i hi j
    exact False.elim ( hf j )
  }
  {
    ext i
    simp only [← h0]
    simp only [Set.mem_range, nonpos_iff_eq_zero, Set.setOf_eq_eq_singleton, Set.mem_singleton_iff]
    have h3 : ∀ c, SC.RL (a c) = 0 := by {
      intro c
      have h2 := (SC.rl_proper (a c)).1
      simp only [← h0] at h2
      omega
    }
    apply Iff.intro
    {
      intro h2
      cases h2
      rename_i c hc
      rw [h3 c] at hc
      exact (Eq.symm hc)
    }
    {
      intro hi0
      use 0
      rw [hi0]
      exact h3 0
    }
  }
  {
    intro a2 h2
    ext i
    apply funext
    intro j
    exact False.elim ( hf j )
  }
}

theorem strong_cubical_sperner (k: ℕ ) : ∀ (SC : SpernerCube), k = SC.n →
    Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  induction' k with k hind
  {
    intro SC hk
    exact induction_start SC hk
  }
  {
    intro SC1 hk1
    apply @odd_of_boundary_faces SC1 k hk1
    let SC2 := @child_cube SC1 k hk1
    have hnz : NeZero SC1.n := by {
      rw [← hk1]
      exact instNeZeroNatHAdd_1
    }
    have h2 := hind SC2 rfl
    apply Eq.mpr _ h2
    apply congrArg
    let f1 : SC2.G → SC1.G := child_map SC1
    let f2 : (Fin (k+1)→ SC2.G) → (Fin (k+1)→ SC1.G) := fun a ↦ fun b ↦ f1 (a b)
    have hf1inj : Function.Injective f1 := by {
      apply child_map_inj SC1
      rw [← hk1]
      rfl
    }
    symm
    have hcomp I : complete_boundary_face SC1 (f2 I) ↔ complete_simplex SC2 SC2.n I := by {
      unfold complete_boundary_face complete_simplex
      have h_last j k: j.1 + 1 = SC1.n → f2 I k j = SC1.p := by {
        apply child_map_last
      }
      have h_bf : simplex SC1 k (f2 I) ↔ is_boundary_face SC1 (f2 I) ∧ simplex SC1 k (f2 I):= by {
        simp only [iff_and_self]
        intro hs
        apply @case_B_boundary SC1 k hk1
        exact hs
        use (Fin.ofNat _ k)
        intro i
        ext
        apply h_last
        simp [← hk1]
      }
      rw [← and_assoc, ←h_bf]
      have h3 : SC2.n = k := rfl
      apply and_congr
      apply and_congr
      {
        apply Iff.intro
        {
          intro h4 i1 i2 h5
          exact h4 (congrArg f1 h5)
        }
        {
          intro h4 i1 i2 h5
          apply h4
          apply hf1inj h5
        }
      }
      {
        simp only [h3]
        apply forall₂_congr
        intro i hi1
        apply Iff.intro
        {
          intro h4 j
          have h6 k : (f2 I k (Fin.ofNat _ j.1)) = (I k j) := by {
            unfold f2
            apply child_map_applied
            rw [← hk1]
            rfl
          }
          erw [← h6, ← h6, ← h6, ← h6]
          exact h4 (Fin.ofNat _ j.1)
        }
        {
          intro h4 j
          by_cases h5 : j.1 + 1 = SC1.n
          {
            rw [h_last, h_last, h_last, h_last]
            simp only [le_refl, le_add_iff_nonneg_right, zero_le,
              and_self]
            repeat' exact h5
          }
          {
            have h7 : j.1 < SC2.n := by {
              rw [h3]
              have h6 := j.2
              simp only [← hk1] at h5 h6
              omega
            }
            have hn02 : NeZero SC2.n := by {
              exact NeZero.of_gt hi1
            }
            let j2 : Fin SC2.n := (Fin.ofNat _ j.1)
            have h8 : j = (Fin.ofNat _ j2.1) := by {
              unfold j2
              simp only [Fin.ofNat_eq_cast,]
              rw [Fin.val_cast_of_lt]
              exact Eq.symm (Fin.cast_val_eq_self j)
              exact h7
            }
            have h6 k : (f2 I k j) = (I k j2) := by {
              unfold f2
              rw [h8]
              apply child_map_applied
              exact hk1
            }
            rw [h6, h6, h6, h6]
            exact h4 j2
          }
        }
      }
      exact Eq.congr_right rfl
    }
    apply Finset.card_nbij f2
    {
      classical
      intro I hI
      have hI' : complete_simplex SC2 SC2.n I := (Finset_mem_filter_any.mp (Finset.mem_coe.mp hI)).2
      exact Finset.mem_coe.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcomp I).mpr hI'⟩)
    }
    {
      intro I1 h41 I2 h42 h5
      ext i
      apply hf1inj
      exact congrFun h5 i
    }
    {
      classical
      simp only [Finset.coe_filter, Finset.mem_univ, true_and]
      intro J
      simp only [Set.mem_setOf_eq, Set.mem_image]
      intro h3
      have h4 : ∃ I, f2 I = J := by {
        suffices h6 : ∀ i, ∃ ii, f1 ii = J i by {
          obtain ⟨I, h5⟩  := axiomOfChoice h6
          use I
          ext i
          exact h5 i
        }
        intro i
        have h5 := @child_map_surj_on SC1 k hk1
        apply h5
        exact @complete_boundary_face_last SC1 k hk1 J h3 i
      }
      obtain ⟨I, h4⟩ := h4
      use I
      simp only [h4, and_true]
      exact Finset.mem_coe.mpr (Finset_mem_filter_any.mpr
        ⟨Finset.mem_univ I, (hcomp I).mp (h4 ▸ h3)⟩)
    }
  }

}

theorem weaker_cubical_sperner SC : ∃ I, complete_simplex SC SC.n I := by {
  have h1 := strong_cubical_sperner SC.n SC rfl
  obtain ⟨k1, hk1⟩ := h1
  have h2 : 0 < 2 * k1 + 1 := by omega
  rw [←hk1, Finset.card_pos] at h2
  obtain ⟨I, hI1⟩ := h2
  use I
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI1
  exact hI1
}
end

-- ==== apply_cubical_sperner
section



open Classical

/-
shows the fixed-point theorem for the unit cube
by applying the cubical sperner's lemma
-/


variable {n : ℕ}

def unit_cube := { v : Fin n → ℝ | 0 ≤ v ∧ v ≤ 1 }

noncomputable def rl_point {f : @unit_cube n → @unit_cube n} (x : @unit_cube n) : ℕ :=
  match (Finset.min { i | (f x).1 i < x.1 i ∨ x.1 i = 1}) with
    | some k => k.1
    | none => n

lemma reduced_label_props_1 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
    : @rl_point n f x ≤ n ∧ ∀ k,
    (@rl_point n f x = k.1 → (f x).1 k < x.1 k ∨ x.1 k = 1)
    ∧ ((f x).1 k < x.1 k ∨ x.1 k = 1 → @rl_point n f x ≤ k.1) := by {
  let s : Finset (Fin n) := {i | (f x).1 i < x.1 i ∨ x.1 i = 1}
  let minval := Finset.min s
  let rlp := match minval with
    | some k => k.1
    | none => n
  by_cases he : s = ∅
  {
    have h1 : @rl_point n f x = n := by {
      show rlp = n
      unfold rlp minval
      rw [he]
      simp only [Finset.min_empty]
    }
    rw [h1]
    simp only [le_refl, true_and]
    intro k
    have h2 : n ≠ k.1 := by omega
    simp only [h2, IsEmpty.forall_iff, true_and]
    intro h3
    have h4 : k ∈ s := by {
      unfold s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h3
    }
    rw [he] at h4
    simp only [Finset.notMem_empty] at h4
  }
  have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty hne
  have h1 : @rl_point n f x = m.1 := by {
    show rlp = m.1
    unfold rlp minval
    rw [hm]
  }
  rw [h1]
  simp only [Fin.is_le', Fin.val_fin_le, true_and]
  intro k1
  apply And.intro
  {
    intro h2
    suffices h3 : k1 ∈ s by {
      unfold s at h3
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h3
      exact h3
    }
    apply Finset.mem_of_min
    rw [hm]
    simp only [WithTop.coe_eq_coe]
    ext
    exact h2
  }
  {
    intro h2
    have h3 : k1 ∈ s := by {
      unfold s
      simp only [Finset.mem_filter, Finset.mem_univ, h2, and_self]
    }
    exact Finset.min_le_of_eq h3 hm
  }
}

lemma reduced_label_props_2 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
    : @rl_point n f x ≤ n ∧
    ∀ k, (x.1 k = 0 → @rl_point n f x ≠ k.1) ∧ (x.1 k = 1 → @rl_point n f x ≤ k.1):= by {
  have h1 := reduced_label_props_1 f x
  apply And.intro h1.1
  intro k
  apply And.intro
  {
    intro h2 h3
    have h4 := (h1.2 k).1 h3
    rw [h2] at h4
    simp only [zero_ne_one, or_false] at h4
    contrapose! h4
    exact (f x).2.1 k
  }
  {
    intro h2
    apply (h1.2 k).2
    exact Or.inr h2
  }
}

lemma reduced_label_props_3 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n) (k : Fin n)
    : (@rl_point n f x = k → (f x).1 k ≤ x.1 k) ∧ (@rl_point n f x > k → (f x).1 k ≥ x.1 k) := by {
  have h1 := (reduced_label_props_1 f x).2 k
  apply And.intro
  {
    intro h2
    cases h1.1 h2
    (expose_names; exact le_of_lt h)
    rename_i h3
    rw [h3]
    exact (f x).2.2 k
  }
  {
    contrapose!
    intro h2
    apply h1.2
    exact Or.inl h2
  }
}

noncomputable def discrete_map (p : ℕ ) (v : Fin n → Fin (p+1)) : @unit_cube n :=
  ⟨ fun i ↦ ((v i).1 : ℝ ) / p , by {
    unfold unit_cube
    simp only [Set.mem_setOf_eq]
    rw [Pi.le_def, Pi.le_def, ←forall_and]
    intro i
    simp only [Pi.zero_apply, Pi.one_apply]
    apply And.intro
    exact div_nonneg (Nat.cast_nonneg' ↑(v i)) (Nat.cast_nonneg' p)
    apply div_le_one_of_le₀ ?_ (Nat.cast_nonneg' p)
    simp only [Nat.cast_le]
    exact Fin.is_le (v i)
  }⟩

noncomputable def sperner_cube_of_function (f : @unit_cube n → @unit_cube n)
  (p : ℕ ) {ppos : 0 < p} : SpernerCube where
  n := n
  p := p
  RL := fun v ↦ @rl_point _ f (discrete_map p v)
  rl_proper := by {
    intro v
    let x := discrete_map p v
    have h1 := reduced_label_props_2 f x
    apply And.intro h1.1
    intro k
    apply And.intro
    {
      intro h2
      apply (h1.2 k).1
      unfold x discrete_map
      simp only [div_eq_zero_iff, Nat.cast_eq_zero, Fin.val_eq_zero_iff]
      exact Or.inl h2
    }
    {
      intro h2
      apply (h1.2 k).2
      unfold x discrete_map
      simp only [h2]
      refine (div_eq_one_iff_eq ?_).mpr rfl
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    }
  }

lemma dist_discrete_map p (ppos: 0 < p) (v1 v2 : Fin n → Fin (p+1))
    (h1 : ∀ k, (v1 k).1 ≤ (v2 k).1 + 1 ∧ (v2 k).1 ≤ (v1 k).1 + 1) :
    dist (discrete_map p v1) (discrete_map p v2) ≤ 1 / p := by {
  let x1 := (discrete_map p v1).1
  let x2 := (discrete_map p v2).1
  show dist x1 x2 ≤ 1 / p
  refine (dist_pi_le_iff ?_).mpr ?_
  simp only [one_div, inv_nonneg, Nat.cast_nonneg]
  intro k
  have hx1 : x1 k = (v1 k).1 / p := by {rfl}
  have hx2 : x2 k = (v2 k).1 / p := by {rfl}
  rw [hx1, hx2]
  rw [Real.dist_eq, abs_sub_le_iff]
  have h1k := (h1 k).1
  have h2k := (h1 k).2
  apply And.intro
  repeat {
    rw [sub_le_iff_le_add', ← add_div]
    have ppos2 : 0 < (p : ℝ) := Nat.cast_pos'.mpr ppos
    rwa [div_le_div_iff_of_pos_right ppos2, ←Nat.cast_add_one, Nat.cast_le]
  }
}

lemma nearby_points (f : @unit_cube n → @unit_cube n) (p0:ℕ):
    ∃ x0 : @unit_cube n, ∀ k, (f x0).1 k ≥ x0.1 k ∧
    ∃ xk : @unit_cube n, dist x0 xk ≤ 1 / ↑(p0 +1) ∧ (f xk).1 k ≤ xk.1 k := by {
  let p := p0 + 1
  have ppos : 0 < p := by omega
  let SC := @sperner_cube_of_function n f p ppos
  obtain ⟨I, h3⟩ := weaker_cubical_sperner SC
  have h4 j : j ≤ n → ∃ i, SC.RL (I i) = j := by {
    intro h4
    exact h3.2.symm.subset h4
  }
  obtain ⟨i0, hi0⟩ := h4 n (Nat.le_refl n)
  let x0 := discrete_map SC.p (I i0)
  use x0
  intro k
  apply And.intro
  {
    apply (reduced_label_props_3 f x0 k).2
    have h6 : @rl_point _ f x0 = n := by exact hi0
    rw [h6]
    simp only [gt_iff_lt, Fin.is_lt]
  }
  obtain ⟨ik, hik⟩ := h4 k.1 k.is_le'
  let xk := discrete_map SC.p (I ik)
  use xk
  apply And.intro _ $ (reduced_label_props_3 f xk k).1 hik
  unfold x0 xk
  apply dist_discrete_map p ppos
  have h5 := le_add_one_of_simplex SC I h3.1
  intro k
  exact ⟨h5 i0 ik k, h5 ik i0 k⟩
}


theorem fixed_point_unit_cube (f : C(@unit_cube n, @unit_cube n)) : ∃ x, f x = x := by {
  obtain ⟨x0s, hx0⟩ := axiomOfChoice (nearby_points f)
  have hc1 : ∃ xx : @unit_cube n, ∃ (φ:ℕ → ℕ ), StrictMono φ ∧
      Filter.Tendsto (x0s ∘ φ ) Filter.atTop (nhds xx) := by {
    have hc1 : IsCompact (@unit_cube n) := isCompact_Icc
    let x0 : ℕ → Fin n → ℝ := fun i ↦ (x0s i).1
    have h2 : ∀ i, x0 i ∈ unit_cube := fun i ↦ (x0s i).2
    obtain ⟨a, ⟨ha, ⟨φ,h3⟩ ⟩ ⟩ := hc1.isSeqCompact h2
    use ⟨a, ha⟩
    use φ
    exact And.intro h3.1 $ tendsto_subtype_rng.mpr h3.2
  }
  obtain ⟨xxx, ⟨φ, h2⟩ ⟩ := hc1
  let y0 := x0s ∘ φ
  let g : Fin n → @unit_cube n → ℝ := fun k x ↦ x.1 k
  have hc2 k : Continuous (g k) := by {
    exact (continuous_apply k).comp continuous_subtype_val
  }
  have h3 k : xxx.1 k ≤ (f xxx).1 k := by {
    show g k xxx ≤ g k (f xxx)
    have h6 :=  (hc2 k).seqContinuous h2.2
    have h7 := (hc2 k).seqContinuous $ f.2.seqContinuous h2.2
    apply le_of_tendsto_of_tendsto' h6 h7
    exact fun i ↦ (hx0 (φ i) k).1
  }
  have h4 k : (f xxx).1 k ≤ xxx.1 k := by {
    show g k (f xxx) ≤ g k xxx
    have h5 n:= (hx0 (φ n) k).2
    obtain ⟨yk, h6⟩ := axiomOfChoice h5
    have h4 : Filter.Tendsto yk Filter.atTop (nhds xxx) := by {
      apply tendsto_of_tendsto_of_dist h2.2
      have h7 := @tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h7 _
      {
        intro i
        apply le_trans (h6 i).1
        simp only [Nat.cast_add, Nat.cast_one, one_div]
        apply inv_anti₀ (Nat.cast_add_one_pos i)
        simp only [add_le_add_iff_right, Nat.cast_le, h2.1.le_apply]
      }
      exact fun _ ↦ dist_nonneg
    }
    have h7 := (hc2 k).seqContinuous h4
    have h8 := (hc2 k).seqContinuous $ f.2.seqContinuous h4
    apply le_of_tendsto_of_tendsto' h8 h7
    exact fun i ↦ (h6 i).2
  }
  use xxx
  ext k
  apply le_antisymm (h4 k) (h3 k)
}

/-- The cubical fixed-point theorem stated with mathlib's `Function.IsFixedPt` vocabulary. -/
theorem fixed_point_unit_cube_isFixedPt (f : C(@unit_cube n, @unit_cube n)) :
    ∃ x, Function.IsFixedPt f x := by
  simpa [Function.IsFixedPt] using fixed_point_unit_cube f
end

-- ==== convex_homeos
section



/-
some helper lemmas involving homeomorphisms.
-/


lemma homeo_unit_ball {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s: Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s)
    (hni : (interior s).Nonempty):
    Nonempty (s ≃ₜ Metric.closedBall (0: V) 1) := by {
  have h1 := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hcvx hni
  have h2 : Bornology.IsBounded s := IsCompact.isBounded hcmpct
  cases (h1 h2)
  rename_i e he
  have h4 := closure_eq_iff_isClosed.mpr (IsCompact.isClosed hcmpct)
  have e2 := Homeomorph.image e s
  rw [h4] at he
  rw [he.2.1] at e2
  exact Nonempty.intro e2
}


theorem homeo_of_finrank_eq {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hreq : Module.finrank ℝ V = Module.finrank ℝ W) :
    Nonempty (Metric.closedBall (0: V) 1 ≃ₜ Metric.closedBall (0: W) 1) := by {
  have L := ContinuousLinearEquiv.ofFinrankEq hreq
  let pL := L ⁻¹' (Metric.closedBall (0:W) 1)
  have hpL : pL = L.toHomeomorph ⁻¹' (Metric.closedBall (0:W) 1) := rfl
  have h4 : Convex ℝ pL := Convex.linear_preimage (convex_closedBall 0 1) L.toLinearMap
  have h5 : IsCompact pL := by {
    rw [hpL,Homeomorph.isCompact_preimage]
    exact isCompact_closedBall 0 1
  }
  have h6 : (interior pL).Nonempty := by {
    rw [hpL, ← Homeomorph.preimage_interior]
    refine (Function.Surjective.nonempty_preimage ?_).mpr ?_
    exact Homeomorph.surjective L.toHomeomorph
    use 0
    rw [interior_closedBall]
    {simp only [Metric.mem_ball, dist_self, zero_lt_one]}
    {exact Ne.symm (zero_ne_one' ℝ)}
  }
  have e1 : pL ≃ₜ Metric.closedBall (0:W) 1 := by {
    rw [hpL]
    exact L.toHomeomorph.sets hpL
  }
  have h7 := homeo_unit_ball _ h4 h5 h6
  cases h7
  rename_i e2
  apply Nonempty.intro
  exact e2.symm.trans e1
}


lemma unit_cube_homeo_unit_ball {n}
    : Nonempty (Set.Icc (0 : Fin n → ℝ) 1 ≃ₜ Metric.closedBall (0 : Fin n → ℝ) 1 ) := by
  apply homeo_unit_ball _ (convex_Icc 0 1) isCompact_Icc
  have h1 : Set.Icc (0 : Fin n → ℝ) 1 = Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1) := by
    ext x; simp [Set.mem_Icc, Pi.le_def]
  rw [h1, interior_pi_set Set.finite_univ]
  exact Set.univ_pi_nonempty_iff.mpr fun _ => by
    rw [interior_Icc]; exact ⟨1/2, by norm_num, by norm_num⟩

lemma homeo_unit_cube_of_convex_compact {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s: Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : s.Nonempty)
    : ∃ k, Nonempty (s ≃ₜ Set.Icc (0 : Fin k → ℝ) 1) := by {
  haveI := hne.coe_sort
  let W := affineSpan ℝ s
  obtain ⟨ps, hps⟩ := hne
  let pss : W := ⟨ps, mem_affineSpan ℝ hps⟩
  let g2 := AffineIsometryEquiv.constVSub ℝ pss
  let g1 : W → V := fun x ↦ x.1
  let s2 := g1 ⁻¹' s
  let s3 := g2.symm ⁻¹' s2
  have h32 : Convex ℝ s3 := by {
    exact hcvx.affine_preimage
      ((affineSpan ℝ s).subtype.comp
      (AffineIsometryEquiv.constVSub ℝ pss).symm.toAffineMap)
  }
  have h34 : (interior s3).Nonempty := by {
    refine (Convex.interior_nonempty_iff_affineSpan_eq_top h32).mpr ?_
    unfold s3
    rw [←AffineIsometryEquiv.coe_toAffineEquiv]
    rw [← AffineSubspace.comap_span]
    rw [affineSpan_coe_preimage_eq_top]
    rfl
  }
  let g3 := g1.comp g2.symm
  have h4 : Topology.IsEmbedding g3 := by {
    apply Topology.IsEmbedding.subtypeVal.comp g2.symm.toHomeomorph.isEmbedding
  }
  have h5 : Set.MapsTo g3 s3 s := by {
    intro w h1
    unfold s3 s2 at h1
    rwa [Set.mem_preimage, Set.mem_preimage] at h1
  }
  have h6 : Function.Surjective (Set.MapsTo.restrict g3 s3 s h5) := by {
    refine (Set.MapsTo.restrict_surjective_iff h5).mpr ?_
    refine Set.SurjOn.comp_right ?_ ?_
    exact AffineIsometryEquiv.surjective g2.symm
    intro v h1
    refine (Set.mem_image g1 (g1 ⁻¹' s) v).mpr ?_
    have h11 : v ∈ affineSpan ℝ s := mem_affineSpan ℝ h1
    use ⟨v, h11⟩
    simp only [Set.mem_preimage]
    apply And.intro h1 rfl
  }
  let e1 := (h4.restrict h5).toHomeomorphOfSurjective h6
  have h31 : IsCompact s3 := by {
    have h51 : _ → IsCompact Set.univ := (Homeomorph.isCompact_image e1).mp
    simp only [Set.image_univ, EquivLike.range_eq_univ] at h51
    apply isCompact_iff_isCompact_univ.mpr
    apply h51 $ isCompact_iff_isCompact_univ.mp hcmpct
  }
  obtain ⟨e2⟩ := homeo_unit_ball s3 h32 h31 h34
  let k := Module.finrank ℝ W.direction
  obtain ⟨e3⟩ := @unit_cube_homeo_unit_ball k
  have h2 : k = Module.finrank ℝ (Fin k → ℝ) := (Module.finrank_fin_fun ℝ).symm
  obtain ⟨e4⟩ := homeo_of_finrank_eq h2
  let e5 := (e1.symm.trans e2).trans (e4.trans e3.symm)
  use k
  exact Nonempty.intro e5
}
end

-- ==== brouwer
section





/- Brouwer fixed-point theorem:
Every continuous function mapping a nonempty compact convex set to itself has a fixed point
(the set should be a subset of a finite dimensional vector space).

https://en.wikipedia.org/wiki/Brouwer_fixed-point_theorem
-/


theorem brouwer_fixed_point {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    : ∀ (s : Set V), Convex ℝ s → IsCompact s → Set.Nonempty s →
    ∀ (f : C(s, s)), ∃ x, f x = x := by {
  intro s hcvx hcmpct hne f
  obtain ⟨k, ⟨e⟩ ⟩ := homeo_unit_cube_of_convex_compact s hcvx hcmpct hne
  let g := (toContinuousMap e).comp (f.comp (toContinuousMap e.symm))
  obtain ⟨y, hy⟩ := @fixed_point_unit_cube k g
  use (toContinuousMap e.symm) y
  have h1 : e.symm (e (f (e.symm y))) = e.symm y := congrArg e.symm hy
  rwa [e.symm_apply_apply] at h1
}

/-- Brouwer's fixed-point theorem stated with mathlib's `Function.IsFixedPt` vocabulary. -/
theorem brouwer_fixed_point_isFixedPt {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : Set.Nonempty s)
    (f : C(s, s)) :
    ∃ x, Function.IsFixedPt f x := by
  simpa [Function.IsFixedPt] using brouwer_fixed_point s hcvx hcmpct hne f

/-- The fixed-point set of a continuous self-map on a Brouwer domain is nonempty. -/
theorem brouwer_fixedPoints_nonempty {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : Set.Nonempty s)
    (f : C(s, s)) :
    (Function.fixedPoints f).Nonempty := by
  exact brouwer_fixed_point_isFixedPt s hcvx hcmpct hne f
end

theorem ite_eq_right {c : Prop} {h : Decidable c} {α : Sort*} {t e : α} (hnc : ¬ c) :
    ite c t e = e := if_neg hnc
theorem ite_eq_left {c : Prop} {h : Decidable c} {α : Sort*} {t e : α} (hc : c) :
    ite c t e = t := if_pos hc
namespace OAI
namespace MatrixMultiplication.AuxiliarySeparation
variable {I E : Type*} [AddCommGroup E] [Module ℝ E]
private theorem exists_positive_relation (A : I → E) (s : Finset I)
    (h : ¬ LinearIndependent ℝ (fun i : s ↦ A i)) :
    ∃ g : I → ℝ, (∑ i ∈ s, g i • A i) = 0 ∧ ∃ i ∈ s, 0 < g i := by
  classical
  obtain ⟨g, hg, i, hi, hgi⟩ :=
    (not_linearIndepOn_finset_iff (R := ℝ) (v := A)).mp h
  rcases lt_or_gt_of_ne hgi with hneg | hpos
  · refine ⟨fun j ↦ -g j, ?_, i, hi, neg_pos.mpr hneg⟩
    simp_rw [neg_smul, Finset.sum_neg_distrib, hg, neg_zero]
  · exact ⟨g, hg, i, hi, hpos⟩
private theorem exists_nonneg_representation_erase [DecidableEq I] (A : I → E) (s : Finset I)
    (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (h : ¬ LinearIndependent ℝ (fun i : s ↦ A i)) :
    ∃ i ∈ s, ∃ v : I → ℝ, (∀ j ∈ s.erase i, 0 ≤ v j) ∧
      (∑ j ∈ s.erase i, v j • A j) = ∑ j ∈ s, w j • A j := by
  classical
  obtain ⟨g, hg, i, hi, hgi⟩ := exists_positive_relation A s h
  let p := s.filter fun i ↦ 0 < g i
  obtain ⟨i₀, hi₀, hmin⟩ :
      ∃ i₀ ∈ p, ∀ j ∈ p, w i₀ / g i₀ ≤ w j / g j := by
    apply p.exists_min_image
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  have hi₀s : i₀ ∈ s := (Finset.mem_filter.mp hi₀).1
  have hgi₀ : 0 < g i₀ := (Finset.mem_filter.mp hi₀).2
  let v : I → ℝ := fun j ↦ w j - w i₀ / g i₀ * g j
  have hvi₀ : v i₀ = 0 := by simp [v, ne_of_gt hgi₀]
  refine ⟨i₀, hi₀s, v, ?_, ?_⟩
  · intro j hj
    have hjs : j ∈ s := Finset.mem_of_mem_erase hj
    dsimp [v]
    apply sub_nonneg.mpr
    by_cases hjp : j ∈ p
    · have hgj : 0 < g j := (Finset.mem_filter.mp hjp).2
      exact (le_div_iff₀ hgj).mp (hmin j hjp)
    · have hgj : g j ≤ 0 := by
        simpa only [p, Finset.mem_filter, hjs, true_and, not_lt] using hjp
      exact (mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (hw i₀ hi₀s) hgi₀.le) hgj).trans (hw j hjs)
  · calc
      (∑ j ∈ s.erase i₀, v j • A j) = ∑ j ∈ s, v j • A j := by
        apply Finset.sum_erase
        rw [hvi₀, zero_smul]
      _ = ∑ j ∈ s, w j • A j := by
        simp only [v, sub_smul, mul_smul, Finset.sum_sub_distrib,
          ← Finset.smul_sum, hg, smul_zero, sub_zero]
theorem exists_nonneg_representation_linearIndependent (A : I → E) (s : Finset I)
    (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∃ t : Finset I, t ⊆ s ∧ LinearIndependent ℝ (fun i : t ↦ A i) ∧
      ∃ v : I → ℝ, (∀ i ∈ t, 0 ≤ v i) ∧
        (∑ i ∈ t, v i • A i) = ∑ i ∈ s, w i • A i := by
  classical
  induction s using Finset.strongInductionOn generalizing w with
  | _ s ih =>
    by_cases hs : LinearIndependent ℝ (fun i : s ↦ A i)
    · exact ⟨s, Finset.Subset.refl _, hs, w, hw, rfl⟩
    · obtain ⟨i, hi, v, hv, heq⟩ := exists_nonneg_representation_erase A s w hw hs
      obtain ⟨t, hts, ht, z, hz, hzeq⟩ := ih (s.erase i) (Finset.erase_ssubset hi) v hv
      exact ⟨t, hts.trans (Finset.erase_subset _ _), ht, z, hz, hzeq.trans heq⟩
theorem exists_linearIndependent_subcone [Fintype I] (A : I → E) {x : E}
    (hx : x ∈ PointedCone.hull ℝ (Set.range A)) :
    ∃ s : Finset I, LinearIndependent ℝ (fun i : s ↦ A i) ∧
      x ∈ PointedCone.hull ℝ (Set.range (fun i : s ↦ A i)) := by
  classical
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ({c : ℝ // 0 ≤ c})).mp hx
  obtain ⟨s, _, hs, v, hv, heq⟩ :=
    exists_nonneg_representation_linearIndependent A Finset.univ
      (fun i ↦ (w i : ℝ)) (fun i _ ↦ (w i).property)
  refine ⟨s, hs, ?_⟩
  have hsum : (∑ i ∈ s, v i • A i) = x := by
    exact heq.trans (by simpa only [← Nonneg.coe_smul] using hw)
  rw [← hsum]
  apply Submodule.sum_mem
  intro i hi
  exact PointedCone.smul_mem _ (hv i hi)
    (PointedCone.subset_hull ⟨⟨i, hi⟩, rfl⟩)
end MatrixMultiplication.AuxiliarySeparation
end OAI
namespace OAI
open Topology
namespace MatrixMultiplication.AuxiliarySeparation
theorem mem_pointedCone_hull_range_iff {I E : Type*} [Fintype I]
    [AddCommGroup E] [Module ℝ E] (A : I → E) (x : E) :
    x ∈ PointedCone.hull ℝ (Set.range A) ↔
      ∃ c : I → ℝ, (∀ i, 0 ≤ c i) ∧ ∑ i, c i • A i = x := by
  rw [PointedCone.hull, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun i ↦ (c i : ℝ), fun i ↦ (c i).2, hc⟩
  · rintro ⟨c, hc, hcx⟩
    exact ⟨fun i ↦ ⟨c i, hc i⟩, hcx⟩
theorem isClosed_pointedCone_hull_range_of_linearIndependent
    {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : I → E) (hA : LinearIndependent ℝ A) :
    IsClosed (PointedCone.hull ℝ (Set.range A) : Set E) := by
  let f := Fintype.linearCombination ℝ A
  have hf : IsClosedEmbedding f :=
    LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr hA.fintypeLinearCombination_injective)
  have hnonneg : IsClosed {c : I → ℝ | ∀ i, 0 ≤ c i} := by
    simpa only [Set.ofPred_forall] using
      isClosed_iInter fun i ↦ isClosed_le (continuous_const : Continuous fun _ : I → ℝ ↦ (0 : ℝ)) (continuous_apply i)
  have heq : (PointedCone.hull ℝ (Set.range A) : Set E) =
      f '' {c : I → ℝ | ∀ i, 0 ≤ c i} := by
    ext x
    change x ∈ PointedCone.hull ℝ (Set.range A) ↔ _
    rw [mem_pointedCone_hull_range_iff]
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    rfl
  rw [heq]
  exact hf.isClosedMap _ hnonneg
theorem isClosed_pointedCone_hull_range
    {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : I → E) :
    IsClosed (PointedCone.hull ℝ (Set.range A) : Set E) := by
  classical
  let S := {s : Finset I // LinearIndependent ℝ (fun i : s ↦ A i)}
  have heq : (PointedCone.hull ℝ (Set.range A) : Set E) =
      ⋃ s : S, (PointedCone.hull ℝ (Set.range (fun i : s.1 ↦ A i)) : Set E) := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hx⟩ := exists_linearIndependent_subcone A hx
      exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hx⟩
    · intro hx
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
      apply Submodule.span_mono _ hs
      rintro _ ⟨i, rfl⟩
      exact ⟨i.1, rfl⟩
  rw [heq]
  exact isClosed_iUnion_of_finite fun s : S ↦
    isClosed_pointedCone_hull_range_of_linearIndependent _ s.2
end MatrixMultiplication.AuxiliarySeparation
end OAI
namespace OAI
namespace MatrixMultiplication.AuxiliarySeparation
theorem exists_nat_eq_mul_rat_of_den_dvd {q : ℚ} (hq : 0 ≤ q)
    {D : ℕ} (hD : q.den ∣ D) :
    ∃ c : ℕ, (D : ℚ) * q = (c : ℚ) := by
  obtain ⟨k, rfl⟩ := hD
  refine ⟨k * q.num.toNat, ?_⟩
  have hnum : (q.num.toNat : ℚ) = (q.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  push_cast
  rw [hnum]
  calc
    (q.den : ℚ) * k * q = k * ((q.den : ℚ) * q) := by ring
    _ = k * (q.num : ℚ) := by rw [Rat.den_mul_eq_num]
theorem exists_nat_mul_eq_nat {I : Type*} [Fintype I]
    (q : I → ℚ) (hq : ∀ i, 0 ≤ q i) :
    ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ, ∀ i, (D : ℚ) * q i = (c i : ℚ) := by
  classical
  let D : ℕ := ∏ i, (q i).den
  have hD : 0 < D := Finset.prod_pos fun i _ ↦ (q i).den_pos
  have hc : ∀ i, ∃ c : ℕ, (D : ℚ) * q i = (c : ℚ) := by
    intro i
    exact exists_nat_eq_mul_rat_of_den_dvd (hq i)
      (Finset.dvd_prod_of_mem (fun j ↦ (q j).den) (Finset.mem_univ i))
  choose c hc using hc
  exact ⟨D, hD, c, hc⟩
end MatrixMultiplication.AuxiliarySeparation
end OAI
namespace OAI
namespace MatrixMultiplication.AuxiliarySeparation
theorem exists_ratLinear_one :
    ∃ p : ℝ →ₗ[ℚ] ℚ, p 1 = 1 :=
  Module.Projective.exists_dual_eq_one ℚ (one_ne_zero : (1 : ℝ) ≠ 0)
theorem exists_ratLinear_retraction :
    ∃ p : ℝ →ₗ[ℚ] ℚ, ∀ q : ℚ, p (q : ℝ) = q := by
  obtain ⟨p, hp⟩ := exists_ratLinear_one
  refine ⟨p, fun q ↦ ?_⟩
  have h := p.map_smul q (1 : ℝ)
  simpa [hp] using h
end MatrixMultiplication.AuxiliarySeparation
end OAI
namespace OAI
namespace MatrixMultiplication.AuxiliarySeparation
def rationalVectorCast {J : Type*} (v : J → ℚ) : J → ℝ := fun j ↦ v j
@[simp] theorem rationalVectorCast_apply {J : Type*} (v : J → ℚ) (j : J) :
    rationalVectorCast v j = (v j : ℝ) := rfl
theorem exists_rat_convex_weights_of_affineIndependent
    {I J : Type*} [Fintype I] (v : I → J → ℚ) (b : J → ℚ)
    (w : I → ℝ)
    (hpos : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (heq : ∑ i, w i • rationalVectorCast (v i) = rationalVectorCast b)
    (hind : AffineIndependent ℝ (fun i ↦ rationalVectorCast (v i))) :
    ∃ q : I → ℚ, (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧
      ∑ i, q i • v i = b := by
  classical
  obtain ⟨p, hp⟩ := exists_ratLinear_retraction
  have hpone : p 1 = 1 := by simpa using hp 1
  let q : I → ℚ := fun i ↦ p (w i)
  have hqsum : ∑ i, q i = 1 := by
    simpa only [q, map_sum, hpone] using congrArg p hsum
  have hqeq : ∑ i, q i • v i = b := by
    funext j
    have hj := congrFun heq j
    simp only [Finset.sum_apply, Pi.smul_apply, rationalVectorCast_apply,
      smul_eq_mul] at hj
    have hj' := congrArg p hj
    simp only [map_sum, hp] at hj'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    convert hj' using 1
    apply Finset.sum_congr rfl
    intro i _
    have hm := p.map_smul (v i j) (w i)
    simpa only [q, Rat.smul_def, smul_eq_mul, mul_comm] using hm.symm
  have hqsumReal : ∑ i, (q i : ℝ) = 1 := by exact_mod_cast hqsum
  have hqeqReal :
      ∑ i, (q i : ℝ) • rationalVectorCast (v i) = rationalVectorCast b := by
    funext j
    have hj := congrFun hqeq j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hj
    simpa only [Finset.sum_apply, Pi.smul_apply, rationalVectorCast_apply,
      smul_eq_mul] using (show (∑ i, (q i : ℝ) * (v i j : ℝ)) = (b j : ℝ) by
        exact_mod_cast hj)
  have hqw : ∀ i, (q i : ℝ) = w i := by
    intro i
    exact hind.eq_of_sum_eq_sum (s := Finset.univ)
      (hqsumReal.trans hsum.symm) (hqeqReal.trans heq.symm) i (Finset.mem_univ i)
  refine ⟨q, ?_, hqsum, hqeq⟩
  intro i
  exact_mod_cast (hqw i ▸ hpos i : 0 ≤ (q i : ℝ))
theorem rationalVectorCast_mem_convexHull_descend
    {J : Type*} {s : Set (J → ℚ)} {b : J → ℚ}
    (h : rationalVectorCast b ∈ convexHull ℝ (rationalVectorCast '' s)) :
    b ∈ convexHull ℚ s := by
  classical
  obtain ⟨I, hI, z, w, hz, hind, hpos, hsum, heq⟩ :=
    eq_pos_convex_span_of_mem_convexHull h
  let : Fintype I := hI
  have hv : ∀ i, ∃ v ∈ s, rationalVectorCast v = z i := by
    intro i
    exact hz (Set.mem_range_self i)
  choose v hv hvc using hv
  obtain ⟨q, hqpos, hqsum, hqeq⟩ :=
    exists_rat_convex_weights_of_affineIndependent v b w (fun i ↦ (hpos i).le)
      hsum (by simpa only [hvc] using heq) (by simpa only [hvc] using hind)
  exact mem_convexHull_of_exists_fintype q v hqpos hqsum hv hqeq
theorem mem_rationalCone_of_nonneg_real_solution
    {I J : Type*} [Fintype I] (A : I → J → ℚ) (b : J → ℚ)
    (x : I → ℝ) (hxpos : ∀ i, 0 ≤ x i)
    (hxeq : ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    b ∈ PointedCone.hull ℚ (Set.range A) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ i, x i)
  have hNpos : (0 : ℝ) < N :=
    (Finset.sum_nonneg fun i _ ↦ hxpos i).trans_lt hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hNrat : (N : ℚ) ≠ 0 := by exact_mod_cast hNne
  let scaled : J → ℚ := fun j ↦ b j / N
  let v : Option I → J → ℚ := fun i ↦ match i with
    | none => 0
    | some i => A i
  let w : Option I → ℝ := fun i ↦ match i with
    | none => 1 - (∑ i, x i) / N
    | some i => x i / N
  have hwpos : ∀ i, 0 ≤ w i := by
    intro i
    cases i with
    | none =>
      change 0 ≤ 1 - (∑ i, x i) / N
      exact sub_nonneg.mpr ((div_le_one hNpos).2 hN.le)
    | some i => exact div_nonneg (hxpos i) hNpos.le
  have hwsum : ∑ i, w i = 1 := by
    simp only [Fintype.sum_option, w, ← Finset.sum_div]
    ring
  have hweq : ∑ i, w i • rationalVectorCast (v i) = rationalVectorCast scaled := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Fintype.sum_option, w, v, rationalVectorCast_apply, Pi.zero_apply,
      Rat.cast_zero, mul_zero, zero_add, scaled, Rat.cast_div, Rat.cast_natCast]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, hxeq]
  let s : Set (J → ℚ) := insert 0 (Set.range A)
  have hv : ∀ i, rationalVectorCast (v i) ∈ rationalVectorCast '' s := by
    intro i
    refine ⟨v i, ?_, rfl⟩
    cases i with
    | none => exact Set.mem_insert 0 _
    | some i => exact Set.mem_insert_of_mem 0 (Set.mem_range_self i)
  have hcReal : rationalVectorCast scaled ∈
      convexHull ℝ (rationalVectorCast '' s) :=
    mem_convexHull_of_exists_fintype w (fun i ↦ rationalVectorCast (v i))
      hwpos hwsum hv hweq
  have hcRat : scaled ∈ convexHull ℚ s :=
    rationalVectorCast_mem_convexHull_descend hcReal
  have hs : s ⊆ PointedCone.hull ℚ (Set.range A) := by
    intro a ha
    rcases ha with rfl | ha
    · exact Submodule.zero_mem _
    · exact PointedCone.subset_hull ha
  have hscaled : scaled ∈ PointedCone.hull ℚ (Set.range A) :=
    convexHull_min hs (PointedCone.convex _) hcRat
  have hscale : (N : ℚ) • scaled = b := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, scaled]
    field_simp
  rw [← hscale]
  exact PointedCone.smul_mem _ (Nat.cast_nonneg N) hscaled
theorem exists_nonneg_rat_solution_of_real
    {I J : Type*} [Fintype I] (A : I → J → ℚ) (b : J → ℚ)
    (h : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    ∃ q : I → ℚ, (∀ i, 0 ≤ q i) ∧ ∀ j, ∑ i, q i * A i j = b j := by
  obtain ⟨x, hxpos, hxeq⟩ := h
  have hb := mem_rationalCone_of_nonneg_real_solution A b x hxpos hxeq
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun ({c : ℚ // 0 ≤ c})).1 hb
  refine ⟨fun i ↦ (q i : ℚ), fun i ↦ (q i).property, ?_⟩
  intro j
  have hj := congrFun hq j
  simpa only [Finset.sum_apply, Pi.smul_apply, ← Nonneg.coe_smul, smul_eq_mul] using hj
theorem exists_nat_scaled_solution_of_nonneg_real
    {I J : Type*} [Fintype I] (A : I → J → ℚ) (b : J → ℚ)
    (h : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ,
      ∀ j, ∑ i, (c i : ℚ) * A i j = (D : ℚ) * b j := by
  obtain ⟨q, hqpos, hqeq⟩ := exists_nonneg_rat_solution_of_real A b h
  obtain ⟨D, hDpos, c, hc⟩ := exists_nat_mul_eq_nat q hqpos
  refine ⟨D, hDpos, c, fun j ↦ ?_⟩
  calc
    ∑ i, (c i : ℚ) * A i j = ∑ i, ((D : ℚ) * q i) * A i j := by simp only [hc]
    _ = (D : ℚ) * ∑ i, q i * A i j := by rw [Finset.mul_sum]; simp only [mul_assoc]
    _ = (D : ℚ) * b j := by rw [hqeq]
theorem exists_nat_scaled_int_solution_of_nonneg_real
    {I J : Type*} [Fintype I] (A : I → J → ℤ) (b : J → ℤ)
    (h : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ,
      ∀ j, ∑ i, (c i : ℤ) * A i j = (D : ℤ) * b j := by
  obtain ⟨x, hxpos, hxeq⟩ := h
  obtain ⟨D, hDpos, c, hc⟩ :=
    exists_nat_scaled_solution_of_nonneg_real
      (fun i j ↦ (A i j : ℚ)) (fun j ↦ (b j : ℚ))
      ⟨x, hxpos, by simpa using hxeq⟩
  refine ⟨D, hDpos, c, fun j ↦ ?_⟩
  exact_mod_cast hc j
end MatrixMultiplication.AuxiliarySeparation
end OAI
namespace OAI
namespace MatrixMultiplication.AuxiliarySeparation
theorem exists_normalized_nonneg_linear_of_no_nat_certificate_of_isClosed
    {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℤ) (u : J → ℤ)
    (hclosed : IsClosed (PointedCone.hull ℝ
      (Set.range (fun i j ↦ (A i j : ℝ))) : Set (J → ℝ)))
    (hno : ¬ ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ,
      ∀ j, ∑ i, (c i : ℤ) * A i j = -(D : ℤ) * u j) :
    ∃ L : (J → ℝ) →ₗ[ℝ] ℝ,
      L (fun j ↦ (u j : ℝ)) = 1 ∧
      ∀ i, 0 ≤ L (fun j ↦ (A i j : ℝ)) := by
  classical
  let C : ProperCone ℝ (J → ℝ) :=
    { toSubmodule := PointedCone.hull ℝ (Set.range (fun i j ↦ (A i j : ℝ)))
      isClosed' := hclosed }
  have houtside : -(fun j ↦ (u j : ℝ)) ∉ C := by
    intro hmem
    obtain ⟨x, hx⟩ :=
      (Submodule.mem_span_range_iff_exists_fun ({c : ℝ // 0 ≤ c})).1 hmem
    have hreal : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧
        ∀ j, ∑ i, x i * (A i j : ℝ) = ((-u j : ℤ) : ℝ) := by
      refine ⟨fun i ↦ (x i : ℝ), fun i ↦ (x i).property, fun j ↦ ?_⟩
      have hj := congrFun hx j
      simpa only [Finset.sum_apply, Pi.smul_apply, ← Nonneg.coe_smul,
        smul_eq_mul, Pi.neg_apply, Int.cast_neg] using hj
    obtain ⟨D, hD, c, hc⟩ :=
      exists_nat_scaled_int_solution_of_nonneg_real A (fun j ↦ -u j) hreal
    exact hno ⟨D, hD, c, fun j ↦ by simpa only [mul_neg, neg_mul] using hc j⟩
  obtain ⟨f, hf, hfu⟩ := C.hyperplane_separation_point houtside
  have hpos : 0 < f (fun j ↦ (u j : ℝ)) := by
    simpa only [map_neg, neg_neg, neg_lt_zero] using hfu
  refine ⟨(f (fun j ↦ (u j : ℝ)))⁻¹ • f.toLinearMap, ?_, fun i ↦ ?_⟩
  · simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, smul_eq_mul]
    exact inv_mul_cancel₀ hpos.ne'
  · change 0 ≤ (f (fun j ↦ (u j : ℝ)))⁻¹ * f (fun j ↦ (A i j : ℝ))
    exact mul_nonneg (inv_nonneg.mpr hpos.le)
      (hf _ (PointedCone.subset_hull (Set.mem_range_self i)))
theorem exists_normalized_nonneg_linear_of_no_nat_certificate
    {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℤ) (u : J → ℤ)
    (hno : ¬ ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ,
      ∀ j, ∑ i, (c i : ℤ) * A i j = -(D : ℤ) * u j) :
    ∃ L : (J → ℝ) →ₗ[ℝ] ℝ,
      L (fun j ↦ (u j : ℝ)) = 1 ∧
      ∀ i, 0 ≤ L (fun j ↦ (A i j : ℝ)) :=
  exists_normalized_nonneg_linear_of_no_nat_certificate_of_isClosed A u
    (isClosed_pointedCone_hull_range _) hno
end MatrixMultiplication.AuxiliarySeparation
end OAI
namespace OAI
namespace MatrixMultiplication.AuxiliarySeparation
open Set
open scoped BigOperators
private def weightSimplex (J : Type*) [Fintype J] : Set (J → ℝ) :=
  {w | (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1}
private theorem weightSimplex_convex (J : Type*) [Fintype J] :
    Convex ℝ (weightSimplex J) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro j
    exact add_nonneg (mul_nonneg ha (hx.1 j)) (mul_nonneg hb (hy.1 j))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.2, hy.2]
    simpa using hab
private theorem weightSimplex_compact (J : Type*) [Fintype J] :
    IsCompact (weightSimplex J) := by
  have hc : IsClosed (weightSimplex J) := by
    change IsClosed ({w : J → ℝ | ∀ j, 0 ≤ w j} ∩ {w | ∑ j, w j = 1})
    have hn : IsClosed {w : J → ℝ | ∀ j, 0 ≤ w j} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun j => isClosed_le continuous_const
        (continuous_apply j : Continuous (fun w : J → ℝ => w j))
    exact hn.inter
      (isClosed_eq (continuous_finsetSum _ fun _ _ => continuous_apply _) continuous_const)
  apply isCompact_Icc.of_isClosed_subset hc
  intro w hw
  constructor
  · exact hw.1
  · intro j
    calc
      w j ≤ ∑ k, w k := Finset.single_le_sum (fun k _ => hw.1 k) (Finset.mem_univ j)
      _ = 1 := hw.2
theorem exists_approximate_fixedPoint_of_weights
    {I J : Type*} [Fintype J] [Nonempty J]
    {K : Set (I → ℝ)} (hK : Convex ℝ K) (f : C(K, K))
    (a : J → K) (w : J → C(K, ℝ))
    (hw0 : ∀ j x, 0 ≤ w j x) (hw1 : ∀ x, ∑ j, w j x = 1)
    (s : Finset I) (ε : ℝ)
    (hclose : ∀ x j, w j x ≠ 0 → ∀ i ∈ s, |(a j).val i - x.val i| ≤ ε) :
    ∃ x : K, ∀ i ∈ s, |(f x).val i - x.val i| ≤ ε := by
  classical
  let D := weightSimplex J
  let b : D → K := fun v =>
    ⟨∑ j, v.val j • (a j).val,
      hK.sum_mem (fun j _ => v.property.1 j) v.property.2 (fun j _ => (a j).property)⟩
  have hb : Continuous b := by
    apply Continuous.subtype_mk
    exact continuous_finsetSum _ fun j _ =>
      ((continuous_apply j).comp continuous_subtype_val).smul continuous_const
  let q : K → D := fun x => ⟨fun j => w j x, (fun j => hw0 j x), hw1 x⟩
  have hq : Continuous q := by
    exact (continuous_pi fun j => (w j).continuous).subtype_mk _
  let g : C(D, D) := ⟨fun v => q (f (b v)), hq.comp (f.continuous.comp hb)⟩
  have hDne : D.Nonempty := by
    let j₀ : J := Classical.choice inferInstance
    refine ⟨Pi.single j₀ 1, ?_, ?_⟩
    · intro j
      by_cases h : j = j₀ <;> simp [h]
    · simp
  obtain ⟨v, hv⟩ := brouwer_fixed_point D (weightSimplex_convex J)
    (weightSimplex_compact J) hDne g
  let x := b v
  have hwv (j : J) : w j (f x) = v.val j := congrArg (fun t : D => t.val j) hv
  refine ⟨x, fun i hi => ?_⟩
  have hx : x.val i - (f x).val i = ∑ j, v.val j * ((a j).val i - (f x).val i) := by
    change (∑ j, v.val j • (a j).val) i - (f x).val i = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, v.property.2, one_mul]
  rw [abs_sub_comm, hx]
  calc
    |∑ j, v.val j * ((a j).val i - (f x).val i)|
        ≤ ∑ j, |v.val j * ((a j).val i - (f x).val i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, v.val j * |(a j).val i - (f x).val i| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (v.property.1 j)]
    _ ≤ ∑ j, v.val j * ε := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : v.val j = 0
      · simp [hj]
      · exact mul_le_mul_of_nonneg_left
          (hclose (f x) j (by rwa [hwv]) i hi) (v.property.1 j)
    _ = ε := by rw [← Finset.sum_mul, v.property.2, one_mul]
theorem exists_finite_partition_weights {I : Type*} {K : Set (I → ℝ)}
    (hK : IsCompact K) (s : Finset I) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ a : Fin n → K, ∃ w : Fin n → C(K, ℝ),
      (∀ x j, 0 ≤ w j x) ∧ (∀ x, ∑ j, w j x = 1) ∧
      (∀ x j, w j x ≠ 0 → ∀ i ∈ s, |(a j).val i - x.val i| < ε) := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let U : K → Set K := fun a => {x | ∀ i ∈ s, |a.val i - x.val i| < ε}
  have hUo : ∀ a, IsOpen (U a) := by
    intro a
    have hUa : U a = ⋂ i ∈ s, {x : K | |a.val i - x.val i| < ε} := by
      ext x
      simp [U]
    rw [hUa]
    apply isOpen_biInter_finset
    intro i hi
    exact isOpen_lt (continuous_const.sub ((continuous_apply i).comp continuous_subtype_val)).abs continuous_const
  have hUc : (univ : Set K) ⊆ ⋃ a, U a := by
    intro x hx
    refine mem_iUnion.mpr ⟨x, ?_⟩
    intro i hi
    simpa using hε
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo hUc
  have htc : (univ : Set K) ⊆ ⋃ a : t, U a.val := by
    intro x hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp (ht hx)
    obtain ⟨hat, hax⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨⟨a, hat⟩, hax⟩
  obtain ⟨w, hw⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun a : t => U a.val) (fun a => hUo a.val) htc
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  refine ⟨Fintype.card t, (fun j => (e j).val), (fun j => w (e j)), ?_, ?_, ?_⟩
  · intro x j
    exact w.nonneg (e j) x
  · intro x
    change ∑ j, w (e j) x = 1
    calc
      ∑ j, w (e j) x = ∑ a : t, w a x := e.sum_comp (fun a => w a x)
      _ = 1 := by simpa only [finsum_eq_sum_of_fintype] using w.sum_eq_one (mem_univ x)
  · intro x j hj i hi
    exact hw (e j) (subset_closure hj) i hi
theorem exists_finite_partition_weights_nonempty {I : Type*} {K : Set (I → ℝ)}
    (hK : IsCompact K) (hne : K.Nonempty) (s : Finset I) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : Fin n → K, ∃ w : Fin n → C(K, ℝ),
      (∀ x j, 0 ≤ w j x) ∧ (∀ x, ∑ j, w j x = 1) ∧
      (∀ x j, w j x ≠ 0 → ∀ i ∈ s, |(a j).val i - x.val i| < ε) := by
  obtain ⟨n, a, w, hw0, hw1, hwa⟩ := exists_finite_partition_weights hK s hε
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    obtain ⟨x, hx⟩ := hne
    simpa using hw1 ⟨x, hx⟩
  exact ⟨n, hn, a, w, hw0, hw1, hwa⟩
theorem compact_approx_limit {I : Type*} {K : Set (I → ℝ)}
    (hK : IsCompact K) (_hne : K.Nonempty) (f : K → (I → ℝ)) (hf : Continuous f)
    (happrox : ∀ s : Finset I, ∀ ε : ℝ, 0 < ε →
      ∃ x : K, ∀ i ∈ s, |f x i - x.val i| ≤ ε) :
    ∃ x : K, f x = x.val := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let C : (I × {ε : ℝ // 0 < ε}) → Set K :=
    fun p => {x | |f x p.1 - x.val p.1| ≤ p.2.val}
  have hclosed (p : I × {ε : ℝ // 0 < ε}) : IsClosed (C p) := by
    exact isClosed_le
      (((continuous_apply p.1).comp hf).sub
        ((continuous_apply p.1).comp continuous_subtype_val)).abs continuous_const
  have hfinite (s : Finset (I × {ε : ℝ // 0 < ε})) :
      (⋂ p ∈ s, C p).Nonempty := by
    let es : Finset ℝ := insert 1 (s.image fun p => p.2.val)
    have hes : es.Nonempty := ⟨1, by simp [es]⟩
    have he : 0 < es.min' hes := by
      rw [Finset.lt_min'_iff]
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · norm_num
      · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
        exact p.2.property
    obtain ⟨x, hx⟩ := happrox (s.image Prod.fst) (es.min' hes) he
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter]
    intro p hp
    exact (hx p.1 (Finset.mem_image.mpr ⟨p, hp, rfl⟩)).trans
      (Finset.min'_le es p.2.val (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨p, hp, rfl⟩)))
  obtain ⟨x, hx⟩ := CompactSpace.iInter_nonempty hclosed hfinite
  refine ⟨x, funext fun i => ?_⟩
  have hzero : |f x i - x.val i| ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    simpa only [C, Set.mem_ofPred_eq, zero_add] using
      (Set.mem_iInter.mp hx (i, ⟨ε, hε⟩))
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))
theorem compact_convex_fixedPoint {I : Type*} {K : Set (I → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (f : C(K, K)) : ∃ x : K, f x = x := by
  have happrox : ∀ s : Finset I, ∀ ε : ℝ, 0 < ε →
      ∃ x : K, ∀ i ∈ s, |(f x).val i - x.val i| ≤ ε := by
    intro s ε hε
    obtain ⟨n, hn, a, w, hw0, hw1, hwa⟩ :=
      exists_finite_partition_weights_nonempty hKcompact hKne s hε
    let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact exists_approximate_fixedPoint_of_weights hKconvex f a w
      (fun j x => hw0 x j) hw1 s ε
      (fun x j hj i hi => (hwa x j hj i hi).le)
  obtain ⟨x, hx⟩ := compact_approx_limit hKcompact hKne
    (fun x => (f x).val) (continuous_subtype_val.comp f.continuous) happrox
  exact ⟨x, Subtype.ext hx⟩
theorem compact_convex_fixedPoint_of_continuous {I : Type*} {K : Set (I → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (f : K → K) (hf : Continuous f) : ∃ x : K, f x = x :=
  compact_convex_fixedPoint hKcompact hKconvex hKne ⟨f, hf⟩
end MatrixMultiplication.AuxiliarySeparation
end OAI
namespace OAI
namespace MatrixMultiplication.AuxiliarySeparation
open Algebra
variable {S : Type*} [CommSemiring S] [Preorder S]
theorem exists_catalyst_of_completion_eq
    (hadd : ∀ a b c d : S, a ≤ b → c ≤ d → a + c ≤ b + d)
    (m k : ℕ) (d X Y s : S) (hXY : X ≤ Y)
    (heq : -(m : ℤ) • GrothendieckAddGroup.of (1 : S) =
      GrothendieckAddGroup.of Y - GrothendieckAddGroup.of X +
        GrothendieckAddGroup.of (d * s) - k • GrothendieckAddGroup.of s) :
    ∃ D : S, D + (m : S) + d * s ≤ D + (k : S) * s := by
  let η : S →+ GrothendieckAddGroup S := GrothendieckAddGroup.of
  have hm : η (m : S) = m • η 1 := by
    rw [← nsmul_one m, map_nsmul]
  have hk : η ((k : S) * s) = k • η s := by
    rw [← nsmul_eq_mul, map_nsmul]
  have heq' : η ((m : S) + Y + d * s) = η (X + (k : S) * s) := by
    simp only [map_add, hm, hk]
    change -(m : ℤ) • η 1 = η Y - η X + η (d * s) - k • η s at heq
    simp only [neg_zsmul, natCast_zsmul] at heq
    calc
      m • η 1 + η Y + η (d * s) =
          m • η 1 + (η Y - η X + η (d * s) - k • η s) + η X + k • η s := by abel
      _ = m • η 1 + -(m • η 1) + η X + k • η s := by rw [← heq]
      _ = η X + k • η s := by abel
  obtain ⟨C, hC⟩ := (AddLocalization.addMonoidOf (⊤ : AddSubmonoid S)).exists_of_eq heq'
  refine ⟨(C : S) + Y, ?_⟩
  calc
    ((C : S) + Y) + (m : S) + d * s = (C : S) + ((m : S) + Y + d * s) := by ac_rfl
    _ = (C : S) + (X + (k : S) * s) := hC
    _ ≤ (C : S) + (Y + (k : S) * s) :=
      hadd _ _ _ _ le_rfl (hadd _ _ _ _ hXY le_rfl)
    _ = ((C : S) + Y) + (k : S) * s := by ac_rfl
theorem exists_catalyst_of_completion_sum_eq
    (hadd : ∀ a b c d : S, a ≤ b → c ≤ d → a + c ≤ b + d)
    {I : Type*} [Fintype I] (m k : ℕ) (d : S)
    (n : I → ℕ) (X Y Z : I → S) (hXY : ∀ i, X i ≤ Y i)
    (heq : -(m : ℤ) • GrothendieckAddGroup.of (1 : S) =
      ∑ i, n i • (GrothendieckAddGroup.of (Y i) - GrothendieckAddGroup.of (X i) +
        GrothendieckAddGroup.of (d * Z i) - k • GrothendieckAddGroup.of (Z i))) :
    ∃ D : S, D + (m : S) + d * (∑ i, n i • Z i) ≤
      D + (k : S) * (∑ i, n i • Z i) := by
  classical
  have hnsmul (a b : S) (hab : a ≤ b) (l : ℕ) : l • a ≤ l • b := by
    induction l with
    | zero => simp
    | succ l ih => simpa only [succ_nsmul] using hadd _ _ _ _ ih hab
  have hsum (t : Finset I) : ∑ i ∈ t, n i • X i ≤ ∑ i ∈ t, n i • Y i := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      simpa only [Finset.sum_insert hi] using
        hadd _ _ _ _ (hnsmul (X i) (Y i) (hXY i) (n i)) ih
  apply exists_catalyst_of_completion_eq hadd m k d
    (∑ i, n i • X i) (∑ i, n i • Y i) (∑ i, n i • Z i) (hsum Finset.univ)
  convert heq using 1
  simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    map_sum, map_nsmul, Finset.mul_sum, mul_smul_comm, ← smul_comm k]
  rw [Finset.smul_sum]
end MatrixMultiplication.AuxiliarySeparation
end OAI
namespace OAI
noncomputable section
namespace MatrixMultiplication.AuxiliarySeparation
def finiteCoordinateState {S : Type*} (H : Finset S)
    (L : (H → ℝ) →ₗ[ℝ] ℝ) (x : S) : ℝ := by
  classical
  exact L (fun j : H ↦ if (j : S) = x then 1 else 0)
@[simp] theorem finiteCoordinateState_eq_zero_of_not_mem {S : Type*}
    (H : Finset S) (L : (H → ℝ) →ₗ[ℝ] ℝ) {x : S} (hx : x ∉ H) :
    finiteCoordinateState H L x = 0 := by
  classical
  unfold finiteCoordinateState
  have hz : (fun j : H ↦ if (j : S) = x then (1 : ℝ) else 0) = 0 := by
    funext j
    simp only [Pi.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
    exact fun h ↦ hx (h ▸ j.property)
  rw [hz, map_zero]
theorem linearCombination_finiteCoordinateState {S : Type*}
    (H : Finset S) (L : (H → ℝ) →ₗ[ℝ] ℝ) (v : S →₀ ℤ) :
    Finsupp.linearCombination ℤ (finiteCoordinateState H L) v =
      L (fun j : H ↦ (v j : ℝ)) := by
  classical
  induction v using Finsupp.induction with
  | zero =>
    simp only [map_zero, Finsupp.zero_apply, Int.cast_zero]
    exact (L.map_zero).symm
  | single_add x n v _ _ ih =>
    rw [map_add, Finsupp.linearCombination_single, ih]
    have hsingle :
        (fun j : H ↦ ((Finsupp.single x n : S →₀ ℤ) j : ℝ)) =
          n • (fun j : H ↦ if (j : S) = x then (1 : ℝ) else 0) := by
      funext j
      by_cases hj : (j : S) = x
      · simp [hj]
      · simp [hj]
    have hadd :
        (fun j : H ↦ ((Finsupp.single x n + v) j : ℝ)) =
          (fun j : H ↦ ((Finsupp.single x n : S →₀ ℤ) j : ℝ)) +
            (fun j : H ↦ (v j : ℝ)) := by
      funext j
      simp
    rw [hadd, map_add, hsingle, map_zsmul]
    rfl
end MatrixMultiplication.AuxiliarySeparation
end
end OAI
namespace OAI
noncomputable section
namespace MatrixMultiplication.AuxiliarySeparation
open Set
variable {S : Type*} [CommSemiring S] [Preorder S]
def normalizedStates (R : S → ℝ) (d : S) (k : ℝ) : Set (S → ℝ) :=
  {f | (∀ x, 0 ≤ f x ∧ f x ≤ R x) ∧ f 1 = 1 ∧
    (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, x ≤ y → f x ≤ f y) ∧
    (∀ x, k * f x ≤ f (d * x))}
theorem normalizedStates_isClosed (R : S → ℝ) (d : S) (k : ℝ) :
    IsClosed (normalizedStates R d k) := by
  unfold normalizedStates
  have hb : IsClosed {f : S → ℝ | ∀ x, 0 ≤ f x ∧ f x ≤ R x} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro x
    exact (isClosed_le continuous_const (continuous_apply x)).inter
      (isClosed_le (continuous_apply x) continuous_const)
  have hn : IsClosed {f : S → ℝ | f 1 = 1} :=
    isClosed_eq (continuous_apply 1) continuous_const
  have ha : IsClosed {f : S → ℝ | ∀ x y, f (x + y) = f x + f y} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply (x + y))
        ((continuous_apply x).add (continuous_apply y))
  have hm : IsClosed {f : S → ℝ | ∀ x y, x ≤ y → f x ≤ f y} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_iInter fun _ => isClosed_le (continuous_apply x) (continuous_apply y)
  have hd : IsClosed {f : S → ℝ | ∀ x, k * f x ≤ f (d * x)} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x =>
      isClosed_le (continuous_const.mul (continuous_apply x)) (continuous_apply (d * x))
  exact hb.inter (hn.inter (ha.inter (hm.inter hd)))
theorem normalizedStates_isCompact (R : S → ℝ) (d : S) (k : ℝ) :
    IsCompact (normalizedStates R d k) := by
  apply (isCompact_univ_pi (fun x => isCompact_Icc (a := (0 : ℝ)) (b := R x))).of_isClosed_subset
    (normalizedStates_isClosed R d k)
  intro f hf x _
  exact hf.1 x
theorem normalizedStates_convex (R : S → ℝ) (d : S) (k : ℝ) :
    Convex ℝ (normalizedStates R d k) := by
  intro f hf g hg a b ha hb hab
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change 0 ≤ a * f x + b * g x ∧ a * f x + b * g x ≤ R x
    constructor
    · exact add_nonneg (mul_nonneg ha (hf.1 x).1) (mul_nonneg hb (hg.1 x).1)
    · calc
        a * f x + b * g x ≤ a * R x + b * R x :=
          add_le_add (mul_le_mul_of_nonneg_left (hf.1 x).2 ha)
            (mul_le_mul_of_nonneg_left (hg.1 x).2 hb)
        _ = R x := by rw [← add_mul, hab, one_mul]
  · change a * f 1 + b * g 1 = 1
    rw [hf.2.1, hg.2.1, mul_one, mul_one, hab]
  · intro x y
    change a * f (x + y) + b * g (x + y) =
      (a * f x + b * g x) + (a * f y + b * g y)
    rw [hf.2.2.1, hg.2.2.1]
    ring
  · intro x y hxy
    exact add_le_add (mul_le_mul_of_nonneg_left (hf.2.2.2.1 x y hxy) ha)
      (mul_le_mul_of_nonneg_left (hg.2.2.2.1 x y hxy) hb)
  · intro x
    change k * (a * f x + b * g x) ≤ a * f (d * x) + b * g (d * x)
    calc
      k * (a * f x + b * g x) = a * (k * f x) + b * (k * g x) := by ring
      _ ≤ a * f (d * x) + b * g (d * x) :=
        add_le_add (mul_le_mul_of_nonneg_left (hf.2.2.2.2 x) ha)
          (mul_le_mul_of_nonneg_left (hg.2.2.2.2 x) hb)
theorem state_zero {R : S → ℝ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k) : f 0 = 0 := by
  have h := hf.2.2.1 0 0
  rw [zero_add] at h
  linarith
theorem state_nat_mul {R : S → ℝ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k) (n : ℕ) (x : S) :
    f ((n : S) * x) = (n : ℝ) * f x := by
  induction n with
  | zero => simp [state_zero hf]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, hf.2.2.1, ih]
    push_cast
    ring
theorem state_one_le {R : S → ℝ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k) {z : S} (hz : 1 ≤ z) : 1 ≤ f z := by
  simpa only [hf.2.1] using hf.2.2.2.1 1 z hz
theorem state_rescale {R : S → ℕ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates (fun x => (R x : ℝ)) d k) (z : S)
    (hz : 1 ≤ z)
    (hmulmono : ∀ x y : S, x ≤ y → z * x ≤ z * y)
    (hdom : ∀ x : S, z * x ≤ (R x : S) * z) :
    (fun x => f (z * x) / f z) ∈ normalizedStates (fun x => (R x : ℝ)) d k := by
  have hfz : 0 < f z := lt_of_lt_of_le zero_lt_one (state_one_le hf hz)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨div_nonneg (hf.1 (z * x)).1 hfz.le, ?_⟩
    apply (div_le_iff₀ hfz).mpr
    have h := hf.2.2.2.1 (z * x) ((R x : S) * z) (hdom x)
    simpa only [state_nat_mul hf] using h
  · simp [mul_one, ne_of_gt hfz]
  · intro x y
    change f (z * (x + y)) / f z = f (z * x) / f z + f (z * y) / f z
    rw [mul_add, hf.2.2.1, add_div]
  · intro x y hxy
    exact div_le_div_of_nonneg_right (hf.2.2.2.1 _ _ (hmulmono x y hxy)) hfz.le
  · intro x
    have h := hf.2.2.2.2 (z * x)
    have hc : d * (z * x) = z * (d * x) := by ring
    rw [hc] at h
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right h hfz.le
end MatrixMultiplication.AuxiliarySeparation
end
end OAI
namespace OAI
noncomputable section
namespace MatrixMultiplication.AuxiliarySeparation
open Set
variable {S : Type*} [CommSemiring S]
def normalizedTranslate (z : S) (f : S → ℝ) : S → ℝ :=
  fun x => f (z * x) / f z
theorem normalizedTranslate_continuousOn {K : Set (S → ℝ)} (z : S)
    (hz : ∀ f ∈ K, f z ≠ 0) :
    Continuous (fun f : K => normalizedTranslate z f.val) := by
  apply continuous_pi
  intro x
  exact ((continuous_apply (z * x)).comp continuous_subtype_val).div
    ((continuous_apply z).comp continuous_subtype_val) (fun f => hz f.val f.property)
def frozenConstraint (z : S) (c : ℝ) : Set (S → ℝ) :=
  {f | ∀ x, f (z * x) = c * f x}
def frozenSlice (C : Set (S → ℝ)) (z : S) (c : ℝ) : Set (S → ℝ) :=
  C ∩ frozenConstraint z c
theorem frozenConstraint_isClosed (z : S) (c : ℝ) :
    IsClosed (frozenConstraint z c) := by
  unfold frozenConstraint
  simp only [ofPred_forall]
  exact isClosed_iInter fun x =>
    isClosed_eq (continuous_apply (z * x)) (continuous_const.mul (continuous_apply x))
theorem frozenSlice_isCompact {C : Set (S → ℝ)} (hC : IsCompact C) (z : S) (c : ℝ) :
    IsCompact (frozenSlice C z c) :=
  hC.inter_right (frozenConstraint_isClosed z c)
theorem frozenConstraint_convex (z : S) (c : ℝ) :
    Convex ℝ (frozenConstraint z c) := by
  intro f hf g hg a b _ _ _ x
  change a * f (z * x) + b * g (z * x) = c * (a * f x + b * g x)
  rw [hf x, hg x]
  ring
theorem frozenSlice_convex {C : Set (S → ℝ)} (hC : Convex ℝ C) (z : S) (c : ℝ) :
    Convex ℝ (frozenSlice C z c) :=
  hC.inter (frozenConstraint_convex z c)
theorem normalizedTranslate_mem_frozenConstraint {z w : S} {c : ℝ} {f : S → ℝ}
    (hf : f ∈ frozenConstraint z c) :
    normalizedTranslate w f ∈ frozenConstraint z c := by
  intro x
  change f (w * (z * x)) / f w = c * (f (w * x) / f w)
  rw [show w * (z * x) = z * (w * x) by ac_rfl, hf (w * x)]
  ring
theorem frozenSlice_mapsTo_normalizedTranslate {C : Set (S → ℝ)} {z w : S} {c : ℝ}
    (hC : MapsTo (normalizedTranslate w) C C) :
    MapsTo (normalizedTranslate w) (frozenSlice C z c) (frozenSlice C z c) := by
  intro f hf
  exact ⟨hC hf.1, normalizedTranslate_mem_frozenConstraint hf.2⟩
theorem frozenConstraint_value {z : S} {c : ℝ} {f : S → ℝ}
    (hf : f ∈ frozenConstraint z c) (hf1 : f 1 = 1) : f z = c := by
  simpa only [mul_one, hf1] using hf 1
theorem normalizedTranslate_eq_mem_frozenConstraint {z : S} {f : S → ℝ}
    (hfz : f z ≠ 0) (hf : normalizedTranslate z f = f) :
    f ∈ frozenConstraint z (f z) := by
  intro x
  have hx : f (z * x) / f z = f x := congrFun hf x
  exact (div_eq_iff hfz).mp hx |>.trans (mul_comm _ _)
theorem normalizedTranslate_eq_nonzero {z : S} {f : S → ℝ}
    (hf1 : f 1 = 1) (hf : normalizedTranslate z f = f) : f z ≠ 0 := by
  intro hfz
  have hx := congrFun hf 1
  simp [normalizedTranslate, hfz, hf1] at hx
theorem normalizedTranslate_eq_mem_frozenConstraint_of_normalized {z : S} {f : S → ℝ}
    (hf1 : f 1 = 1) (hf : normalizedTranslate z f = f) :
    f ∈ frozenConstraint z (f z) :=
  normalizedTranslate_eq_mem_frozenConstraint (normalizedTranslate_eq_nonzero hf1 hf) hf
theorem normalizedTranslate_eq_mem_frozenSlice {C : Set (S → ℝ)} {z : S} {f : S → ℝ}
    (hfC : f ∈ C) (hf1 : f 1 = 1) (hf : normalizedTranslate z f = f) :
    f ∈ frozenSlice C z (f z) :=
  ⟨hfC, normalizedTranslate_eq_mem_frozenConstraint_of_normalized hf1 hf⟩
theorem exists_finite_multiplicative_slice {K : Set (S → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (hKnorm : ∀ f ∈ K, f 1 = 1)
    (hKnonzero : ∀ f ∈ K, ∀ z : S, z ≠ 0 → f z ≠ 0)
    (hKmap : ∀ z : S, z ≠ 0 → MapsTo (normalizedTranslate z) K K)
    (t : Finset {z : S // z ≠ 0}) :
    ∃ C : Set (S → ℝ), C ⊆ K ∧ C.Nonempty ∧ IsCompact C ∧ Convex ℝ C ∧
      (∀ z : S, z ≠ 0 → MapsTo (normalizedTranslate z) C C) ∧
      ∀ f ∈ C, ∀ z ∈ t, ∀ x, f (z.val * x) = f z.val * f x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      exact ⟨K, Subset.rfl, hKne, hKcompact, hKconvex, hKmap, by simp⟩
  | @insert z t hzt ih =>
      obtain ⟨C, hCK, hCne, hCcompact, hCconvex, hCmap, hCt⟩ := ih
      let P : C → C := fun f =>
        ⟨normalizedTranslate z.val f.val, hCmap z.val z.property f.property⟩
      have hP : Continuous P := by
        apply Continuous.subtype_mk
        exact normalizedTranslate_continuousOn z.val
          (fun f hf => hKnonzero f (hCK hf) z.val z.property)
      obtain ⟨g, hg⟩ := compact_convex_fixedPoint_of_continuous
        hCcompact hCconvex hCne P hP
      have hg' : normalizedTranslate z.val g.val = g.val := congrArg Subtype.val hg
      let c : ℝ := g.val z.val
      let D := frozenSlice C z.val c
      have hDC : D ⊆ C := fun _ hf => hf.1
      have hDK : D ⊆ K := hDC.trans hCK
      refine ⟨D, hDK, ?_, frozenSlice_isCompact hCcompact z.val c,
        frozenSlice_convex hCconvex z.val c, ?_, ?_⟩
      · exact ⟨g.val, normalizedTranslate_eq_mem_frozenSlice g.property
          (hKnorm g.val (hCK g.property)) hg'⟩
      · intro w hw
        exact frozenSlice_mapsTo_normalizedTranslate (hCmap w hw)
      · intro f hf w hw x
        rcases Finset.mem_insert.mp hw with rfl | hwt
        · have hfc : f w.val = c := frozenConstraint_value hf.2 (hKnorm f (hDK hf))
          rw [hfc]
          exact hf.2 x
        · exact hCt f (hDC hf) w hwt x
theorem exists_multiplicative_of_invariant_states {K : Set (S → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (hKnorm : ∀ f ∈ K, f 1 = 1) (hKzero : ∀ f ∈ K, f 0 = 0)
    (hKnonzero : ∀ f ∈ K, ∀ z : S, z ≠ 0 → f z ≠ 0)
    (hKmap : ∀ z : S, z ≠ 0 → MapsTo (normalizedTranslate z) K K) :
    ∃ f ∈ K, ∀ x y, f (x * y) = f x * f y := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  let F : {z : S // z ≠ 0} → Set K :=
    fun z => {f | ∀ x, f.val (z.val * x) = f.val z.val * f.val x}
  have hFclosed (z : {z : S // z ≠ 0}) : IsClosed (F z) := by
    change IsClosed {f : K | ∀ x, f.val (z.val * x) = f.val z.val * f.val x}
    simp only [ofPred_forall]
    exact isClosed_iInter fun x =>
      isClosed_eq ((continuous_apply (z.val * x)).comp continuous_subtype_val)
        (((continuous_apply z.val).comp continuous_subtype_val).mul
          ((continuous_apply x).comp continuous_subtype_val))
  have hFfinite (t : Finset {z : S // z ≠ 0}) : (⋂ z ∈ t, F z).Nonempty := by
    obtain ⟨C, hCK, hCne, _, _, _, hCt⟩ := exists_finite_multiplicative_slice
      hKcompact hKconvex hKne hKnorm hKnonzero hKmap t
    obtain ⟨f, hf⟩ := hCne
    refine ⟨⟨f, hCK hf⟩, ?_⟩
    simp only [mem_iInter]
    intro z hz
    exact hCt f hf z hz
  obtain ⟨f, hf⟩ := CompactSpace.iInter_nonempty hFclosed hFfinite
  refine ⟨f.val, f.property, fun x y => ?_⟩
  by_cases hx : x = 0
  · simp [hx, hKzero f.val f.property]
  · exact mem_iInter.mp hf ⟨x, hx⟩ y
theorem normalizedStates_exists_multiplicative [Preorder S]
    (R : S → ℕ) (d : S) (k : ℝ)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hmulmono : ∀ z x y : S, x ≤ y → z * x ≤ z * y)
    (hdom : ∀ z x : S, z * x ≤ (R x : S) * z)
    (hne : (normalizedStates (fun x => (R x : ℝ)) d k).Nonempty) :
    ∃ f ∈ normalizedStates (fun x => (R x : ℝ)) d k,
      ∀ x y, f (x * y) = f x * f y := by
  apply exists_multiplicative_of_invariant_states
    (normalizedStates_isCompact _ d k) (normalizedStates_convex _ d k) hne
  · exact fun _ hf => hf.2.1
  · exact fun _ hf => state_zero hf
  · intro f hf z hz
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (state_one_le hf (hunit z hz)))
  · intro z hz f hf
    exact state_rescale hf z (hunit z hz) (hmulmono z) (hdom z)
theorem exists_monotone_semiringHom_of_normalizedStates [Preorder S]
    (R : S → ℕ) (d : S) (k : ℝ)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hmulmono : ∀ z x y : S, x ≤ y → z * x ≤ z * y)
    (hdom : ∀ z x : S, z * x ≤ (R x : S) * z)
    (hne : (normalizedStates (fun x => (R x : ℝ)) d k).Nonempty) :
    ∃ χ : S →+* ℝ, Monotone χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ R x) ∧ k ≤ χ d := by
  obtain ⟨f, hf, hfmul⟩ :=
    normalizedStates_exists_multiplicative R d k hunit hmulmono hdom hne
  let χ : S →+* ℝ :=
    { toFun := f
      map_zero' := state_zero hf
      map_one' := hf.2.1
      map_add' := hf.2.2.1
      map_mul' := hfmul }
  refine ⟨χ, ?_, hf.1, ?_⟩
  · intro x y hxy
    exact hf.2.2.2.1 x y hxy
  · simpa only [χ, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      mul_one, hf.2.1] using hf.2.2.2.2 1
end MatrixMultiplication.AuxiliarySeparation
end
end OAI
namespace OAI
noncomputable section
namespace MatrixMultiplication.AuxiliarySeparation
open Set
variable {S : Type*} [CommSemiring S] [Preorder S]
inductive StateConstraint (S : Type*) [Preorder S] where
  | lower (x : S)
  | upper (x : S)
  | addPos (x y : S)
  | addNeg (x y : S)
  | order (x y : S) (h : x ≤ y)
  | detector (x : S)
def stateConstraintVector (R : S → ℕ) (d : S) (k : ℕ)
    (c : StateConstraint S) : S →₀ ℤ := by
  classical
  exact match c with
  | .lower x => Finsupp.single x 1
  | .upper x => Finsupp.single (1 : S) (R x : ℤ) - Finsupp.single x 1
  | .addPos x y => Finsupp.single (x + y) 1 - Finsupp.single x 1 - Finsupp.single y 1
  | .addNeg x y => -(Finsupp.single (x + y) 1 - Finsupp.single x 1 - Finsupp.single y 1)
  | .order x y _ => Finsupp.single y 1 - Finsupp.single x 1
  | .detector x => Finsupp.single (d * x) 1 - Finsupp.single x (k : ℤ)
def statePairing (f : S → ℝ) : (S →₀ ℤ) →ₗ[ℤ] ℝ :=
  Finsupp.linearCombination ℤ f
omit [CommSemiring S] [Preorder S] in
theorem statePairing_apply (f : S → ℝ) (v : S →₀ ℤ) :
    statePairing f v = ∑ x ∈ v.support, (v x : ℝ) * f x := by
  simp [statePairing, Finsupp.linearCombination_apply, Finsupp.sum, zsmul_eq_mul]
omit [CommSemiring S] [Preorder S] in
@[simp] theorem statePairing_single (f : S → ℝ) (x : S) (n : ℤ) :
    statePairing f (Finsupp.single x n) = (n : ℝ) * f x := by
  simp [statePairing, zsmul_eq_mul]
omit [CommSemiring S] [Preorder S] in
theorem continuous_statePairing (v : S →₀ ℤ) :
    Continuous (fun f : S → ℝ ↦ statePairing f v) := by
  simp only [statePairing_apply]
  exact continuous_finsetSum _ fun x _ ↦ continuous_const.mul (continuous_apply x)
theorem normalizedStates_iff_stateConstraint (R : S → ℕ) (d : S) (k : ℕ)
    (f : S → ℝ) :
    f ∈ normalizedStates (fun x ↦ (R x : ℝ)) d k ↔
      f 1 = 1 ∧ ∀ c : StateConstraint S, 0 ≤ statePairing f (stateConstraintVector R d k c) := by
  classical
  constructor
  · intro hf
    refine ⟨hf.2.1, ?_⟩
    intro c
    cases c with
    | lower x => simpa [stateConstraintVector] using (hf.1 x).1
    | upper x =>
      simp only [stateConstraintVector, map_sub, statePairing_single, Int.cast_natCast,
        Int.cast_one, one_mul, hf.2.1, mul_one, sub_nonneg]
      exact (hf.1 x).2
    | addPos x y => simp [stateConstraintVector, hf.2.2.1]
    | addNeg x y => simp [stateConstraintVector, hf.2.2.1]
    | order x y h => simpa [stateConstraintVector, sub_nonneg] using hf.2.2.2.1 x y h
    | detector x => simpa [stateConstraintVector, sub_nonneg] using hf.2.2.2.2 x
  · rintro ⟨hn, hc⟩
    refine ⟨?_, hn, ?_, ?_, ?_⟩
    · intro x
      constructor
      · simpa [stateConstraintVector] using hc (.lower x)
      · simpa [stateConstraintVector, hn, sub_nonneg] using hc (.upper x)
    · intro x y
      have hp := hc (.addPos x y)
      have hm := hc (.addNeg x y)
      simp [stateConstraintVector] at hp hm
      linarith
    · intro x y hxy
      simpa [stateConstraintVector, sub_nonneg] using hc (.order x y hxy)
    · intro x
      simpa [stateConstraintVector, sub_nonneg] using hc (.detector x)
def stateConstraintLower (c : StateConstraint S) : S :=
  match c with
  | .lower _ => 0
  | .upper x => x
  | .order x _ _ => x
  | _ => 0
def stateConstraintUpper (R : S → ℕ) (c : StateConstraint S) : S :=
  match c with
  | .lower x => x
  | .upper x => R x
  | .order _ y _ => y
  | _ => 0
def stateConstraintDetector (c : StateConstraint S) : S :=
  match c with
  | .detector x => x
  | _ => 0
theorem stateConstraintLower_le_upper (R : S → ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (c : StateConstraint S) :
    stateConstraintLower c ≤ stateConstraintUpper R c := by
  cases c with
  | lower x => exact hzero x
  | upper x => exact hbound x
  | order _ _ h => exact h
  | addPos _ _ => exact le_rfl
  | addNeg _ _ => exact le_rfl
  | detector _ => exact le_rfl
theorem stateConstraintVector_completion (R : S → ℕ) (d : S) (k : ℕ)
    (c : StateConstraint S) :
    Finsupp.linearCombination ℤ (Algebra.GrothendieckAddGroup.of (M := S))
        (stateConstraintVector R d k c) =
      Algebra.GrothendieckAddGroup.of (stateConstraintUpper R c) -
        Algebra.GrothendieckAddGroup.of (stateConstraintLower c) +
      Algebra.GrothendieckAddGroup.of (d * stateConstraintDetector c) -
        k • Algebra.GrothendieckAddGroup.of (stateConstraintDetector c) := by
  classical
  have hcast (n : ℕ) : Algebra.GrothendieckAddGroup.of (n : S) =
      n • Algebra.GrothendieckAddGroup.of (1 : S) := by
    rw [← nsmul_one, map_nsmul]
  cases c <;>
    simp [stateConstraintVector, stateConstraintLower, stateConstraintUpper,
      stateConstraintDetector, hcast, Nat.cast_smul_eq_nsmul, map_add] <;> abel
theorem no_stateConstraint_certificate (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s)
    {I : Type*} [Fintype I] (cs : I → StateConstraint S) :
    ¬∃ m : ℕ, 0 < m ∧ ∃ n : I → ℕ,
      ∑ i, n i • stateConstraintVector R d k (cs i) =
        -(m : ℤ) • Finsupp.single (1 : S) (1 : ℤ) := by
  classical
  rintro ⟨m, hm, n, hn⟩
  have heq := congrArg
    (Finsupp.linearCombination ℤ (Algebra.GrothendieckAddGroup.of (M := S))) hn
  simp only [map_sum, map_nsmul, map_smul, Finsupp.linearCombination_single,
    one_smul, stateConstraintVector_completion] at heq
  obtain ⟨D, hD⟩ := exists_catalyst_of_completion_sum_eq hadd m k d n
    (fun i ↦ stateConstraintLower (cs i)) (fun i ↦ stateConstraintUpper R (cs i))
    (fun i ↦ stateConstraintDetector (cs i))
    (fun i ↦ stateConstraintLower_le_upper R hzero hbound (cs i)) heq.symm
  exact hno D _ m hm hD
theorem finite_stateConstraint_solution (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s)
    {I : Type*} [Fintype I] (cs : I → StateConstraint S) (H : Finset S) (hOne : (1 : S) ∈ H)
    (hH : ∀ i, (stateConstraintVector R d k (cs i)).support ⊆ H) :
    ∃ f : S → ℝ, f 1 = 1 ∧
      (∀ i, 0 ≤ statePairing f (stateConstraintVector R d k (cs i))) ∧
      ∀ x ∉ H, f x = 0 := by
  classical
  let A : I → H → ℤ := fun i j ↦ stateConstraintVector R d k (cs i) j
  let u : H → ℤ := fun j ↦ (Finsupp.single (1 : S) (1 : ℤ)) j
  have hcert : ¬∃ m : ℕ, 0 < m ∧ ∃ n : I → ℕ,
      ∀ j, ∑ i, (n i : ℤ) * A i j = -(m : ℤ) * u j := by
    rintro ⟨m, hm, n, hn⟩
    apply no_stateConstraint_certificate R d k hzero hbound hadd hno cs
    refine ⟨m, hm, n, ?_⟩
    ext x
    by_cases hx : x ∈ H
    · have heq := hn ⟨x, hx⟩
      by_cases hx1 : (1 : S) = x <;>
        simpa [A, u, Finsupp.coe_finsetSum, Finset.sum_apply,
          Finsupp.smul_apply, nsmul_eq_mul, zsmul_eq_mul, Finsupp.single_apply, hx1] using heq
    · have hz : ∀ i, stateConstraintVector R d k (cs i) x = 0 := by
        intro i
        apply Finsupp.notMem_support_iff.mp
        exact fun h ↦ hx (hH i h)
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
        hz, smul_zero, Finset.sum_const_zero]
      have hx1 : x ≠ 1 := by
        rintro rfl
        exact hx hOne
      simp [hx1]
  obtain ⟨L, hLu, hLA⟩ :=
    exists_normalized_nonneg_linear_of_no_nat_certificate A u hcert
  let f := finiteCoordinateState H L
  refine ⟨f, ?_, ?_, ?_⟩
  · have heq := linearCombination_finiteCoordinateState H L
      (Finsupp.single (1 : S) (1 : ℤ))
    simpa [f, u] using heq.trans hLu
  · intro i
    simpa only [statePairing, f, linearCombination_finiteCoordinateState, A] using hLA i
  · intro x hx
    exact finiteCoordinateState_eq_zero_of_not_mem H L hx
theorem bounded_finite_stateConstraint_solution (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s)
    (F : Finset (StateConstraint S)) :
    ∃ f : S → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ R x) ∧ f 1 = 1 ∧
      ∀ c ∈ F, 0 ≤ statePairing f (stateConstraintVector R d k c) := by
  classical
  let H : Finset S := insert 1 (F.biUnion fun c ↦ (stateConstraintVector R d k c).support)
  have hOne : (1 : S) ∈ H := Finset.mem_insert_self _ _
  let cs : F ⊕ (Bool × H) → StateConstraint S
    | .inl c => c
    | .inr (false, x) => .lower x
    | .inr (true, x) => .upper x
  have hH : ∀ i, (stateConstraintVector R d k (cs i)).support ⊆ H := by
    intro i a ha
    cases i with
    | inl c =>
      exact Finset.mem_insert_of_mem
        (Finset.mem_biUnion.mpr ⟨c, c.property, ha⟩)
    | inr i =>
      rcases i with ⟨tag, x⟩
      by_contra hnot
      have ha1 : a ≠ 1 := by
        rintro rfl
        exact hnot hOne
      have hax : a ≠ (x : S) := by
        rintro rfl
        exact hnot x.property
      have ha0 := Finsupp.mem_support_iff.mp ha
      cases tag <;>
        simp [cs, stateConstraintVector, ha1, hax] at ha0
  obtain ⟨f, hf1, hfc, hfzero⟩ :=
    finite_stateConstraint_solution R d k hzero hbound hadd hno cs H hOne hH
  refine ⟨f, ?_, hf1, ?_⟩
  · intro x
    by_cases hx : x ∈ H
    · have hlo := hfc (.inr (false, ⟨x, hx⟩))
      have hhi := hfc (.inr (true, ⟨x, hx⟩))
      constructor
      · simpa [cs, stateConstraintVector] using hlo
      · simpa [cs, stateConstraintVector, hf1, sub_nonneg] using hhi
    · rw [hfzero x hx]
      exact ⟨le_rfl, Nat.cast_nonneg _⟩
  · intro c hc
    exact hfc (.inl ⟨c, hc⟩)
theorem normalizedStates_nonempty_of_no_catalyst (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s) :
    (normalizedStates (fun x ↦ (R x : ℝ)) d k).Nonempty := by
  let B : Set (S → ℝ) := {f | ∀ x, 0 ≤ f x ∧ f x ≤ R x}
  let K : Set (S → ℝ) := B ∩ {f | f 1 = 1}
  let t : StateConstraint S → Set (S → ℝ) :=
    fun c ↦ {f | 0 ≤ statePairing f (stateConstraintVector R d k c)}
  have hBcompact : IsCompact B :=
    isCompact_pi_infinite (fun x ↦ isCompact_Icc (a := (0 : ℝ)) (b := (R x : ℝ)))
  have hKcompact : IsCompact K :=
    hBcompact.inter_right (isClosed_eq (continuous_apply 1) continuous_const)
  have htclosed : ∀ c, IsClosed (t c) := fun c ↦
    isClosed_le continuous_const (continuous_statePairing (stateConstraintVector R d k c))
  have hfinite : ∀ F : Finset (StateConstraint S), (K ∩ ⋂ c ∈ F, t c).Nonempty := by
    intro F
    obtain ⟨f, hfb, hf1, hfc⟩ :=
      bounded_finite_stateConstraint_solution R d k hzero hbound hadd hno F
    refine ⟨f, ⟨hfb, hf1⟩, ?_⟩
    simp only [Set.mem_iInter]
    exact hfc
  obtain ⟨f, hfK, hft⟩ := hKcompact.inter_iInter_nonempty t htclosed hfinite
  refine ⟨f, (normalizedStates_iff_stateConstraint R d k f).mpr ?_⟩
  exact ⟨hfK.2, fun c ↦ Set.mem_iInter.mp hft c⟩
end MatrixMultiplication.AuxiliarySeparation
end
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter
open scoped Topology NNReal
theorem eq_of_nat_mul_close {a b C : ℝ}
    (h : ∀ m : ℕ, |(m : ℝ) * (a - b)| ≤ C) : a = b := by
  by_contra hab
  obtain ⟨m, hm⟩ := exists_lt_nsmul (abs_pos.mpr (sub_ne_zero.mpr hab)) C
  rw [nsmul_eq_mul] at hm
  have hbound := h m
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)] at hbound
  exact hm.not_ge hbound
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
theorem dimension_price_eq_logb {p : ℕ → ℝ} (hmono : ∀ i j, 0 < i → i ≤ j → p i ≤ p j)
    (hone : p 1 = 0) (hmul : ∀ i j, 0 < i → 0 < j → p (i * j) = p i + p j)
    {q : ℕ} (hq : 0 < q) : p q = p 2 * Real.logb 2 q := by
  have hp (i : ℕ) (hi : 0 < i) (n : ℕ) : p (i ^ n) = n * p i := by
    induction n with
    | zero => simp [hone]
    | succ n ih => rw [pow_succ, hmul _ _ (pow_pos hi _) hi, ih, Nat.cast_succ, add_mul, one_mul]
  have hp2 : 0 ≤ p 2 := by simpa [hone] using hmono 1 2 (by decide) (by decide)
  have happrox (k : ℕ) : k * p q ≤ k * (p 2 * Real.logb 2 q) + p 2 ∧
      k * (p 2 * Real.logb 2 q) ≤ k * p q + p 2 := by
    let b := Nat.log 2 (q ^ k)
    have hlo : 2 ^ b ≤ q ^ k := Nat.pow_log_le_self _ (pow_pos hq _).ne'
    have hhi : q ^ k ≤ 2 ^ (b + 1) := (Nat.lt_pow_succ_log_self (by decide) _).le
    have hplo := hmono _ _ (pow_pos (by decide : 0 < 2) _) hlo
    have hphi := hmono _ _ (pow_pos hq _) hhi
    rw [hp _ (by decide) _, hp _ hq _] at hplo
    rw [hp _ hq _, hp _ (by decide) _, Nat.cast_add_one] at hphi
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : 0 < (2 : ℝ) ^ b) (by exact_mod_cast hlo : (2 : ℝ)^b ≤ (q : ℝ)^k)
    have hu := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : 0 < (q : ℝ)^k) (by exact_mod_cast hhi : (q : ℝ)^k ≤ (2 : ℝ)^(b+1))
    simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      Nat.cast_add_one, mul_one] at hl hu
    constructor <;> nlinarith only [hphi, hplo, mul_le_mul_of_nonneg_left hl hp2,
      mul_le_mul_of_nonneg_left hu hp2]
  apply eq_of_nat_mul_close (C := p 2)
  intro k
  rw [abs_le, mul_sub]
  obtain ⟨hu, hl⟩ := happrox k
  constructor <;> linarith
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Real
open scoped NNReal
variable {A : Type*} [Semiring A] (v : A →* ℝ≥0) (hmono : ∀ {a b : ℕ}, 0 < a → a ≤ b → v (a : A) ≤ v (b : A))
include hmono in
theorem spectral_natCast_one_le (n : ℕ) (hn : 0 < n) : 1 ≤ v (n : A) := by
  simpa using hmono (a := 1) (b := n) (by decide) hn
include hmono in
private theorem spectral_natCast_logb_mono {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    logb 2 (v (a : A)) ≤ logb 2 (v (b : A)) :=
  logb_le_logb_of_le (by norm_num)
    (by exact_mod_cast zero_lt_one.trans_le (spectral_natCast_one_le v hmono a ha))
    (by exact_mod_cast hmono ha hab)
include hmono in
theorem spectral_natCast_logb (n : ℕ) (hn : 0 < n) :
    logb 2 (v (n : A)) = logb 2 (v (2 : A)) * logb 2 n := by
  refine dimension_price_eq_logb (p := fun i => logb 2 (v (i : A)))
    (fun _ _ => spectral_natCast_logb_mono v hmono) (by simp) ?_ hn
  intro i j hi hj
  have hpos {k : ℕ} (hk : 0 < k) : (v (k : A) : ℝ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le (spectral_natCast_one_le v hmono k hk)).ne'
  rw [Nat.cast_mul, map_mul, NNReal.coe_mul, logb_mul (hpos hi) (hpos hj)]
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Finset Set
private theorem exists_integral_cut {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hd : 0 < d) (hab : a / b < c / d) :
    ∃ m n : ℕ, (n : ℝ) * a < m * b ∧ (m : ℝ) * d < n * c := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hab)
  let n := k + 1
  have hn : (0 : ℝ) < n := by dsimp [n]; positivity
  have hgap : 1 < (c / d - a / b) * n := by
    apply (div_lt_iff₀ hn).mp
    simpa [n] using hk
  let m := ⌊a / b * n⌋₊ + 1
  have hm₁ : a / b * n < m := by simpa [m] using Nat.lt_floor_add_one (a / b * n)
  have hm₂ : (m : ℝ) < c / d * n := by
    have hfloor := Nat.floor_le (mul_nonneg (div_nonneg ha hb.le) hn.le : 0 ≤ a / b * n)
    dsimp [m]
    push_cast
    linarith only [hfloor, hgap]
  refine ⟨m, n, ?_, ?_⟩
  · calc
      (n : ℝ) * a = (a / b * n) * b := by field_simp
      _ < m * b := mul_lt_mul_of_pos_right hm₁ hb
  · calc
      (m : ℝ) * d < (c / d * n) * d := mul_lt_mul_of_pos_right hm₂ hd
      _ = n * c := by field_simp
variable {T : Type*} [AddCommMonoid T]
private theorem local_price_separator
    (F h : T →+ ℝ) (G : AddSubmonoid T) {u : T} (hu : u ∈ G)
    (hU : 0 < h u) (hF : ∀ t, 0 ≤ F t) (hh : ∀ t, 0 ≤ h t)
    (hfull : ∃ t, 0 < F t)
    (hfail : ¬ ∃ c : ℝ, 0 < c ∧ (∀ t, c * F t ≤ h t) ∧
      ∀ t ∈ G, c * F t = h t) :
    ∃ x ∈ G, ∃ y : T, F x < F y ∧ h y < h x := by
  by_cases hzero : F u = 0
  · obtain ⟨y, hpos⟩ := hfull
    obtain ⟨n, hn⟩ := exists_nat_gt (h y / h u)
    refine ⟨n • u, G.nsmul_mem hu n, y, ?_, ?_⟩
    · simpa [hzero] using hpos
    · simpa [nsmul_eq_mul] using (div_lt_iff₀ hU).mp hn
  have hFu : 0 < F u := lt_of_le_of_ne (hF u) (Ne.symm hzero)
  by_cases hover : ∃ t, h t / h u < F t / F u
  · obtain ⟨t, ht⟩ := hover
    obtain ⟨m, n, h₁, h₂⟩ := exists_integral_cut (hh t) hU hFu ht
    refine ⟨m • u, G.nsmul_mem hu m, n • t, ?_, ?_⟩
    · simpa [nsmul_eq_mul] using h₂
    · simpa [nsmul_eq_mul] using h₁
  by_cases hunder : ∃ t ∈ G, F t / F u < h t / h u
  · obtain ⟨t, htG, ht⟩ := hunder
    obtain ⟨m, n, h₁, h₂⟩ := exists_integral_cut (hF t) hFu hU ht
    refine ⟨n • t, G.nsmul_mem htG n, m • u, ?_, ?_⟩
    · simpa [nsmul_eq_mul] using h₁
    · simpa [nsmul_eq_mul] using h₂
  push Not at hover hunder
  exfalso
  apply hfail
  refine ⟨h u / F u, div_pos hU hFu, ?_, ?_⟩
  · intro t
    have hle := (div_le_div_iff₀ hFu hU).mp (hover t)
    rw [div_mul_eq_mul_div, div_le_iff₀ hFu]
    linarith
  · intro t ht
    have heq := (div_eq_div_iff hFu.ne' hU.ne').mp
      (le_antisymm (hover t) (hunder t ht))
    rw [div_mul_eq_mul_div, div_eq_iff hFu.ne']
    linarith
theorem select_spectral_price_of_finite_comparison
    {S : Type*} [TopologicalSpace S] [CompactSpace S] [Nonempty S]
    (F : S → T →+ ℝ) (h : T →+ ℝ) (G : AddSubmonoid T) (Δ u : T)
    (hcont : ∀ t, Continuous (fun s => F s t)) (hF : ∀ s t, 0 ≤ F s t)
    (hh : ∀ t, 0 ≤ h t) (hu : u ∈ G) (hU : 0 < h u)
    (hfull : ∀ s, ∃ t, 0 < F s t)
    (hcompare : ∀ (x : T), x ∈ G → ∀ (j : ℕ) (y : Fin j → T),
      (∀ s, ∃ i, F s (Δ + x) < F s (y i)) → ∃ i, h (Δ + x) ≤ h (y i)) :
    ∃ (s : S) (c : ℝ), 0 < c ∧ (∀ t, c * F s t ≤ h t) ∧
      ∀ t ∈ G, c * F s t = h t := by
  classical
  by_contra hnone
  have hlocal (s : S) := local_price_separator (F s) h G hu hU (hF s) hh (hfull s)
    (fun he => hnone ⟨s, he⟩)
  choose x hx y hxy hyx using hlocal
  let U (s : S) := {q : S | F q (x s) < F q (y s)}
  have hcover : (univ : Set S) ⊆ ⋃ s, U s := fun q _ => mem_iUnion.mpr ⟨q, hxy q⟩
  obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subcover U
    (fun s => isOpen_lt (hcont _) (hcont _)) hcover
  let E := Fintype.equivFin ↥J
  let X := ∑ s ∈ J, x s
  let Y (s : S) := Δ + (∑ q ∈ J.erase s, x q) + y s
  have hX : X ∈ G := G.sum_mem fun s _ => hx s
  have hrewrite (s : ↥J) : X = (∑ q ∈ J.erase s.val, x q) + x s :=
    (Finset.sum_erase_add J x s.property).symm
  have hdominates (q : S) : ∃ i, F q (Δ + X) < F q (Y ((E.symm i).val)) := by
    obtain ⟨s, hs⟩ := mem_iUnion.mp (hJ (mem_univ q))
    obtain ⟨hsJ, hqs⟩ := mem_iUnion.mp hs
    let i : ↥J := ⟨s, hsJ⟩
    refine ⟨E i, ?_⟩
    rw [Equiv.symm_apply_apply, hrewrite i]
    simpa [Y, i, add_assoc] using
      add_lt_add_left (show F q (x s) < F q (y s) from hqs)
        (F q Δ + F q (∑ a ∈ J.erase s, x a))
  obtain ⟨i, hi⟩ := hcompare X hX _ (fun i => Y (E.symm i).val) hdominates
  rw [hrewrite (E.symm i)] at hi
  exact (not_le.mpr (hyx (E.symm i).val)) (by simpa only [Y, map_add, ← add_assoc, add_le_add_iff_left] using hi)
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Set NNReal
variable {S : Type*} [Semiring S]
def normalizedSpectrum (restricts : S → S → Prop) : Set (S → ℝ≥0) :=
  {f | f 0 = 0 ∧ f 1 = 1 ∧ (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, f (x * y) = f x * f y) ∧ ∀ x y, restricts x y → f x ≤ f y}
def normalizedSpectrum.toRingHom {restricts : S → S → Prop}
    (f : normalizedSpectrum restricts) : S →+* ℝ≥0 where
  toFun := f.1
  map_zero' := f.2.1
  map_one' := f.2.2.1
  map_add' := f.2.2.2.1
  map_mul' := f.2.2.2.2.1
theorem isClosed_normalizedSpectrum (restricts : S → S → Prop) :
    IsClosed (normalizedSpectrum restricts) := by
  have hmono : IsClosed {f : S → ℝ≥0 | ∀ x y, restricts x y → f x ≤ f y} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_iInter fun _ ↦
      isClosed_le (continuous_apply x) (continuous_apply y)
  exact (isClosed_setOfPred_map_zero S ℝ≥0).inter <|
    (isClosed_setOfPred_map_one S ℝ≥0).inter <|
    (isClosed_setOfPred_map_add S ℝ≥0).inter ((isClosed_setOfPred_map_mul S ℝ≥0).inter hmono)
theorem isCompact_normalizedSpectrum (restricts : S → S → Prop)
    (hfinite : ∀ x : S, ∃ r : ℕ, restricts x r) : IsCompact (normalizedSpectrum restricts) := by
  choose r hr using hfinite
  apply IsCompact.of_isClosed_subset
    (isCompact_univ_pi (fun x ↦ isCompact_Icc (a := (0 : ℝ≥0)) (b := (r x : ℝ≥0))))
    (isClosed_normalizedSpectrum restricts)
  intro f hf x _
  have hle := hf.2.2.2.2 x _ (hr x)
  have hcast : f (r x : S) = (r x : ℝ≥0) := map_natCast (normalizedSpectrum.toRingHom ⟨f, hf⟩) _
  exact ⟨bot_le, hle.trans_eq hcast⟩
theorem continuous_log_price {restricts : S → S → Prop} {x : S} (hx : restricts 1 x) :
    Continuous (fun f : normalizedSpectrum restricts ↦ Real.logb 2 (f.val x : ℝ)) := by
  apply (continuous_subtype_val.comp ((continuous_apply x).comp continuous_subtype_val)).logb
  intro f
  have hone := f.2.2.2.2.2 1 x hx
  rw [f.2.2.1] at hone
  change (f.val x : ℝ) ≠ 0
  exact_mod_cast (zero_lt_one.trans_le hone).ne'
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators
variable {T : Type*} [AddCommMonoid T]
def ExpandedStrictComparison (spectrum : Set (T →+ ℝ))
    (restricts : T → T → Prop) (ordinarySum : T → (L : ℕ) → (Fin L → T) → Prop) : Prop :=
  ∀ {J : ℕ} (X : T) (Y : Fin J → T), 0 < J →
    (∀ f ∈ spectrum, ∃ i, f X < f (Y i)) →
    ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      ∃ L : ℕ, 0 < L ∧ L ≤ K * J ^ n ∧ ∃ Z : Fin L → T,
        ordinarySum (n • X) L Z ∧
        ∀ l, ∃ w : Fin n → Fin J, restricts (Z l) (∑ t, Y (w t))
private theorem remove_constant {a b c : ℝ}
    (h : ∀ n : ℕ, 0 < n → (n : ℝ) * a ≤ c + n * b) : a ≤ b := by
  by_contra! hab
  obtain ⟨m, hm⟩ := exists_lt_nsmul (sub_pos.mpr hab) c
  have hh := h (m + 1) (Nat.succ_pos _)
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hm hh
  linarith
theorem finite_comparison_of_ordinary_sum
    {spectrum : Set (T →+ ℝ)} {restricts : T → T → Prop}
    {ordinarySum : T → (L : ℕ) → (Fin L → T) → Prop}
    (compare : ExpandedStrictComparison spectrum restricts ordinarySum)
    (h : T →+ ℝ) (mono : ∀ {x y}, restricts x y → h x ≤ h y)
    {C : ℝ} (hC : 0 ≤ C) {X : T}
    (stretch : ∀ (m L : ℕ) (Z : Fin L → T), 0 < m →
      ordinarySum (m • X) L Z → ∃ l, h (m • X) ≤ h (Z l) + C * Real.logb 2 L)
    {J : ℕ} (hJ : 0 < J) (Y : Fin J → T)
    (cover : ∀ f ∈ spectrum, ∃ i, f X < f (Y i)) : ∃ i, h X ≤ h (Y i) := by
  classical
  have : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  obtain ⟨i, _, hmax⟩ := Finset.univ.exists_max_image (fun j => h (Y j)) Finset.univ_nonempty
  refine ⟨i, remove_constant (c := C * Real.logb 2 J) fun k hk => ?_⟩
  have hlarge (f : T →+ ℝ) (hf : f ∈ spectrum) : ∃ j, f (k • X) < f (k • Y j) := by
    obtain ⟨j, hj⟩ := cover f hf
    refine ⟨j, ?_⟩
    simpa only [map_nsmul, nsmul_eq_mul] using
      mul_lt_mul_of_pos_left hj (show (0 : ℝ) < k by exact_mod_cast hk)
  obtain ⟨K, hK, decompose⟩ := compare (k • X) (fun j => k • Y j) hJ hlarge
  apply remove_constant (c := C * Real.logb 2 K)
  intro n hn
  obtain ⟨L, hL, hcount, Z, hZ, hword⟩ := decompose n hn
  have hsum : ordinarySum ((n * k) • X) L Z := by rwa [Nat.mul_comm, mul_nsmul]
  obtain ⟨l, hprice⟩ := stretch (n * k) L Z (Nat.mul_pos hn hk) hsum
  obtain ⟨w, hw⟩ := hword l
  have hfactor : h (Z l) ≤ n * (k * h (Y i)) := calc
    h (Z l) ≤ h (∑ t, k • Y (w t)) := mono hw
    _ = ∑ t, k * h (Y (w t)) := by simp
    _ ≤ ∑ _t : Fin n, k * h (Y i) := Finset.sum_le_sum fun t _ =>
      mul_le_mul_of_nonneg_left (hmax (w t) (Finset.mem_univ _)) (Nat.cast_nonneg _)
    _ = n * (k * h (Y i)) := by simp
  have hlog : Real.logb 2 L ≤ Real.logb 2 K + n * Real.logb 2 J := calc
    Real.logb 2 L ≤ Real.logb 2 ((K * J ^ n : ℕ) : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hL) (by exact_mod_cast hcount)
    _ = _ := by
      rw [Nat.cast_mul, Nat.cast_pow, Real.logb_mul (by positivity) (by positivity), Real.logb_pow]
  simp only [map_nsmul, nsmul_eq_mul, Nat.cast_mul] at hprice
  linarith only [hprice, hfactor, mul_le_mul_of_nonneg_left hlog hC]
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
section
open scoped NNReal
variable {A : Type*} [CommSemiring A] {res : A → A → Prop} {P : Submonoid A}
theorem one_le_spectral_value (f : normalizedSpectrum res) {t : A} (ht : res 1 t) :
    1 ≤ f.val t := by
  simpa only [f.property.2.1] using f.property.2.2.2.2 1 t ht
def spectralLogHom (hunit : ∀ t : P, res 1 t) (f : normalizedSpectrum res) :
    Additive P →+ ℝ where
  toFun x := Real.logb 2 (f.val x.toMul.val : ℝ)
  map_zero' := by simp [f.property.2.1]
  map_add' x y := by
    have hpos (t : P) : (f.val t.val : ℝ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans_le (one_le_spectral_value f (hunit t))).ne'
    simp only [toMul_add, Submonoid.coe_mul, f.property.2.2.2.1, NNReal.coe_mul]
    exact Real.logb_mul (hpos x.toMul) (hpos y.toMul)
theorem spectralLogHom_nonneg (hunit : ∀ t : P, res 1 t) (f : normalizedSpectrum res)
    (x : Additive P) : 0 ≤ spectralLogHom hunit f x := by
  apply Real.logb_nonneg (by norm_num)
  exact_mod_cast one_le_spectral_value f (hunit x.toMul)
theorem continuous_spectralLogHom (hunit : ∀ t : P, res 1 t) (x : Additive P) :
    Continuous (fun f : normalizedSpectrum res => spectralLogHom hunit f x) :=
  continuous_log_price (hunit x.toMul)
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
namespace Crossing
noncomputable section
variable {I : Type*} [Fintype I] {F : Type*} [CommSemiring F]
def basisTensor {A : I → Type*} {S : Type*} [Fintype S]
    (term : S → ∀ i, A i) (x : ∀ i, A i) : F :=
  ∑ s, if x = term s then 1 else 0
def IsRestriction {A B : I → Type*} [∀ i, Fintype (A i)]
    (X : (∀ i, B i) → F) (Y : (∀ i, A i) → F) : Prop :=
  ∃ M : ∀ i, B i → A i → F, ∀ x,
    X x = ∑ a, Y a * ∏ i, M i (x i) (a i)
theorem restriction_basisTensor_iff {A B : I → Type*} [∀ i, Fintype (A i)]
    {S : Type*} [Fintype S] (term : S → ∀ i, A i) (X : (∀ i, B i) → F) :
    IsRestriction X (basisTensor term) ↔
      ∃ M : ∀ i, B i → A i → F, ∀ x, X x = ∑ s, ∏ i, M i (x i) (term s i) := by
  unfold IsRestriction basisTensor
  congr! 3 with M x
  simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp
end
end Crossing
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
namespace SiteTensor
open Crossing
variable {I : Type*} [Fintype I] {F : Type*} [CommSemiring F]
variable {A B C : I → Type*} [∀ i, Fintype (A i)]
theorem restrict_of_equiv {X : (∀ i, B i) → F} {Y : (∀ i, A i) → F}
    (e : ∀ i, B i ≃ A i) (h : ∀ x, X x = Y (fun i => e i (x i))) :
    IsRestriction X Y := by
  classical
  refine ⟨fun i b a => if a = e i b then 1 else 0, fun x => ?_⟩
  rw [h x]
  simp_rw [Fintype.prod_boole]
  have heq (a : ∀ i, A i) : (∀ i, a i = e i (x i)) ↔ a = fun i => e i (x i) :=
    funext_iff.symm
  simp [heq, mul_ite]
theorem restrict_refl (X : (∀ i, A i) → F) : IsRestriction X X :=
  restrict_of_equiv (fun i => Equiv.refl (A i)) fun _ => rfl
theorem restrict_trans [∀ i, Fintype (B i)] {X : (∀ i, C i) → F}
    {Y : (∀ i, B i) → F} {Z : (∀ i, A i) → F}
    (hXY : IsRestriction X Y) (hYZ : IsRestriction Y Z) : IsRestriction X Z := by
  classical
  obtain ⟨M, hM⟩ := hXY
  obtain ⟨N, hN⟩ := hYZ
  refine ⟨fun i c a => ∑ b, N i b a * M i c b, fun x => ?_⟩
  rw [hM x]
  simp_rw [hN, Finset.sum_mul, Fintype.prod_sum, Finset.mul_sum, Finset.prod_mul_distrib,
    mul_assoc]
  exact Finset.sum_comm
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
universe v u w
structure Raw (I : Type u) (K : Type w) where
  Leg : I → Type v
  finiteLeg : ∀ i, Fintype (Leg i)
  coeff : (∀ i, Leg i) → K
instance instRawFiniteLeg {I : Type u} {K : Type w} (T : Raw.{v} I K) (i : I) : Fintype (T.Leg i) := T.finiteLeg i
@[simp] theorem instRawFiniteLeg_eq {I : Type u} {K : Type w} (T : Raw.{v} I K) (i : I) : instRawFiniteLeg T i = T.finiteLeg i := rfl
@[simp] theorem instRawFiniteLeg_eqf {I : Type u} {K : Type w} (T : Raw.{v} I K) : (fun i => instRawFiniteLeg T i) = T.finiteLeg := rfl
@[simp] theorem Raw_eta_inst {I : Type u} {K : Type w} (T : Raw.{v} I K) : (⟨T.Leg, T.finiteLeg, T.coeff⟩ : Raw.{v} I K) = T := rfl
namespace Raw
variable {I : Type u} {K : Type w}
noncomputable section
open scoped Classical
abbrev Restricts [Fintype I] [CommSemiring K] (X Y : Raw.{v} I K) :=
  Crossing.IsRestriction X.coeff Y.coeff
def Equivalent [Fintype I] [CommSemiring K] (X Y : Raw.{v} I K) : Prop :=
  X.Restricts Y ∧ Y.Restricts X
def setoid (I : Type u) (K : Type w) [Fintype I] [CommSemiring K] : Setoid (Raw.{v} I K) where
  r := Equivalent
  iseqv := ⟨fun X => ⟨restrict_refl X.coeff, restrict_refl X.coeff⟩,
    fun h => And.symm h, fun h g => ⟨restrict_trans h.1 g.1, restrict_trans g.2 h.2⟩⟩
theorem reindex_equivalent [Fintype I] [CommSemiring K] {X Y : Raw.{v} I K}
    (e : ∀ i, X.Leg i ≃ Y.Leg i) (h : ∀ x, X.coeff x = Y.coeff (fun i => e i (x i))) :
    X.Equivalent Y := by
  refine ⟨restrict_of_equiv e h, restrict_of_equiv (fun i => (e i).symm) ?_⟩
  intro y
  simpa using (h (fun i => (e i).symm (y i))).symm
def zero (I : Type u) (K : Type w) [Zero K] : Raw.{v} I K :=
  ⟨fun _ => PEmpty, fun _ => inferInstance, fun _ => 0⟩
def one (I : Type u) (K : Type w) [One K] : Raw.{v} I K :=
  ⟨fun _ => PUnit, fun _ => inferInstance, fun _ => 1⟩
def mul [Mul K] (X Y : Raw.{v} I K) : Raw.{v} I K :=
  ⟨fun i => X.Leg i × Y.Leg i, fun _ => inferInstance,
    fun x => X.coeff (fun i => (x i).1) * Y.coeff (fun i => (x i).2)⟩
def diagonal (I : Type u) (K : Type w) (α : Type v) [Fintype α] [CommSemiring K] : Raw.{v} I K :=
  ⟨fun _ => α, fun _ => inferInstance, fun x => ∑ a : α, if x = fun _ => a then 1 else 0⟩
end
end Raw
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical NNReal
noncomputable section
section
namespace Crossing
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
variable {B : I → Type*} [∀ i, Fintype (B i)]
theorem restricts_from_coordinate_diagonal_equiv {L : Type*} [Fintype L]
    (e : L ≃ (∀ i, B i)) (T : (∀ i, B i) → K) :
    IsRestriction T (basisTensor (I := I) (fun (l : L) _ ↦ l)) := by
  classical
  let o : I := Classical.choice inferInstance
  let M (i : I) (b : B i) (a : ∀ i, B i) : K :=
    (if b = a i then 1 else 0) * (if i = o then T a else 1)
  apply (restriction_basisTensor_iff _ _).mpr
  refine ⟨fun i b l ↦ M i b (e l), fun b ↦ ?_⟩
  have hprod (a : ∀ i, B i) :
      (∏ i, M i (b i) a) = if b = a then T a else 0 := by
    simp only [M, Finset.prod_mul_distrib, Fintype.prod_boole, ← funext_iff]
    simp
  rw [e.sum_comp (fun a ↦ ∏ i, M i (b i) a)]
  simp [hprod]
theorem unit_restricts_of_nonzero {T : (∀ i, B i) → K} (h : T ≠ 0) :
    IsRestriction (fun _ : I → PUnit ↦ (1 : K)) T := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, T a ≠ 0 := by
    by_contra! hn
    exact h (funext hn)
  let o : I := Classical.choice inferInstance
  let M (i : I) (_ : PUnit) (b : B i) : K :=
    (if b = a i then 1 else 0) * (if i = o then (T a)⁻¹ else 1)
  refine ⟨M, fun _ ↦ ?_⟩
  have hprod (b : ∀ i, B i) :
      (∏ i, M i PUnit.unit (b i)) = if b = a then (T a)⁻¹ else 0 := by
    simp only [M, Finset.prod_mul_distrib, Fintype.prod_boole, ← funext_iff]
    simp
  simp [hprod, mul_ite, ha]
end Crossing
namespace SiteTensor.Raw
universe v
theorem restricts_diagonal (I : Type*) [Fintype I] [Nonempty I]
    {K : Type*} [Field K] (X : Raw.{v} I K) :
    X.Restricts (diagonal I K (ULift.{v} (Fin (Fintype.card (∀ i, X.Leg i))))) := by
  classical
  let e : ULift.{v} (Fin (Fintype.card (∀ i, X.Leg i))) ≃ (∀ i, X.Leg i) :=
    Equiv.ulift.trans (Fintype.equivFin _).symm
  have h := Crossing.restricts_from_coordinate_diagonal_equiv e X.coeff
  unfold Crossing.basisTensor at h
  convert! h using 1
  funext x
  simp only [diagonal]
  congr 1
  funext a
  split_ifs <;> simp_all
theorem one_restricts_of_nonzero {I : Type*} [Fintype I] [Nonempty I]
    {K : Type*} [Field K] (X : Raw.{v} I K) (h : X.coeff ≠ 0) :
    (one I K).Restricts X :=
  Crossing.unit_restricts_of_nonzero h
end SiteTensor.Raw
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
namespace SiteTensor
noncomputable section
variable {X Y Z K : Type*} [Fintype X]
def pushCoeff [AddCommMonoid K] (f : X → Y) (T : X → K) (y : Y) : K :=
  ∑ x, if f x = y then T x else 0
theorem pushCoeff_comp [AddCommMonoid K] [Fintype Y]
    (g : Y → Z) (f : X → Y) (T : X → K) :
    pushCoeff g (pushCoeff f T) = pushCoeff (g ∘ f) T := by
  funext z
  unfold pushCoeff
  have hs (y : Y) : (if g y = z then ∑ x, if f x = y then T x else 0 else 0) =
      ∑ x, if g y = z then if f x = y then T x else 0 else 0 := by
    by_cases h : g y = z <;> simp [h]
  simp_rw [hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (f x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp
theorem pushCoeff_add [AddCommMonoid K] (f : X → Y) (T U : X → K) :
    pushCoeff f (T + U) = pushCoeff f T + pushCoeff f U := by
  funext y
  simp only [pushCoeff, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split <;> simp
theorem pushCoeff_equiv [AddCommMonoid K] (e : X ≃ Y) (T : X → K) (y : Y) :
    pushCoeff e T y = T (e.symm y) := by
  simp [pushCoeff, ← e.eq_symm_apply]
theorem sum_pushCoeff_mul [Semiring K] [Fintype Y] (f : X → Y) (T : X → K) (g : Y → K) :
    ∑ y, pushCoeff f T y * g y = ∑ x, T x * g (f x) := by
  simp only [pushCoeff, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp
variable {I : Type*} [Fintype I] {A B : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [AddCommMonoid K]
def sumCoeff (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) (y : ∀ i, A i ⊕ B i) : K :=
  pushCoeff (fun x i => Sum.inl (x i)) T y + pushCoeff (fun x i => Sum.inr (x i)) U y
theorem sumCoeff_inl [Nonempty I] (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (x : ∀ i, A i) : sumCoeff T U (fun i => Sum.inl (x i)) = T x := by
  have hl (y : ∀ i, A i) : (fun i => (Sum.inl (y i) : A i ⊕ B i)) =
      (fun i => Sum.inl (x i)) ↔ y = x := by
    simp [funext_iff]
  have hr (y : ∀ i, B i) : (fun i => (Sum.inr (y i) : A i ⊕ B i)) ≠
      (fun i => Sum.inl (x i)) := by
    intro h
    cases congrFun h (Classical.arbitrary I)
  simp [sumCoeff, pushCoeff, hl, hr]
theorem sumCoeff_inr [Nonempty I] (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (x : ∀ i, B i) : sumCoeff T U (fun i => Sum.inr (x i)) = U x := by
  have hr (y : ∀ i, B i) : (fun i => (Sum.inr (y i) : A i ⊕ B i)) =
      (fun i => Sum.inr (x i)) ↔ y = x := by
    simp [funext_iff]
  have hl (y : ∀ i, A i) : (fun i => (Sum.inl (y i) : A i ⊕ B i)) ≠
      (fun i => Sum.inr (x i)) := by
    intro h
    cases congrFun h (Classical.arbitrary I)
  simp [sumCoeff, pushCoeff, hl, hr]
theorem sumCoeff_mixed (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (y : ∀ i, A i ⊕ B i)
    (hl : ∀ x : ∀ i, A i, (fun i => Sum.inl (x i)) ≠ y)
    (hr : ∀ x : ∀ i, B i, (fun i => Sum.inr (x i)) ≠ y) :
    sumCoeff T U y = 0 := by
  simp [sumCoeff, pushCoeff, hl, hr]
end
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
namespace SiteTensor
variable {I K : Type*} [Fintype I] [AddCommMonoid K]
variable {A B C : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]
private theorem pushCoeff_relabel {X Y Z : Type*} [Fintype X]
    (e : Y ≃ Z) (f : X → Y) (g : X → Z) (h : ∀ x, e (f x) = g x)
    (T : X → K) (y : Y) : pushCoeff f T y = pushCoeff g T (e y) := by
  classical
  unfold pushCoeff
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← h, e.injective.eq_iff]
private theorem pushCoeff_add_apply {X Y : Type*} [Fintype X]
    (f : X → Y) (T U : X → K) (y : Y) :
    pushCoeff f (fun x => T x + U x) y = pushCoeff f T y + pushCoeff f U y :=
  congrFun (pushCoeff_add f T U) y
theorem sumCoeff_comm (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (x : ∀ i, A i ⊕ B i) :
    sumCoeff T U x = sumCoeff U T (fun i => Equiv.sumComm _ _ (x i)) := by
  let e := Equiv.piCongrRight fun i => Equiv.sumComm (A i) (B i)
  unfold sumCoeff
  rw [add_comm]
  exact congrArg₂ (· + ·) (pushCoeff_relabel e _ _ (fun _ => rfl) U x)
    (pushCoeff_relabel e _ _ (fun _ => rfl) T x)
theorem sumCoeff_assoc (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) (V : (∀ i, C i) → K)
    (x : ∀ i, (A i ⊕ B i) ⊕ C i) :
    sumCoeff (sumCoeff T U) V x =
      sumCoeff T (sumCoeff U V) (fun i => Equiv.sumAssoc _ _ _ (x i)) := by
  let e := Equiv.piCongrRight fun i => Equiv.sumAssoc (A i) (B i) (C i)
  unfold sumCoeff
  simp_rw [pushCoeff_add_apply, pushCoeff_comp, add_assoc]
  exact congrArg₂ (· + ·) (pushCoeff_relabel e _ _ (fun _ => rfl) T x)
    (congrArg₂ (· + ·) (pushCoeff_relabel e _ _ (fun _ => rfl) U x)
      (pushCoeff_relabel e _ _ (fun _ => rfl) V x))
theorem sumCoeff_zero [∀ i, IsEmpty (B i)] (T : (∀ i, A i) → K) (x : ∀ i, A i ⊕ B i) :
    sumCoeff T (0 : (∀ i, B i) → K) x = T (fun i => Equiv.sumEmpty _ _ (x i)) := by
  let e := Equiv.piCongrRight fun i => Equiv.sumEmpty (A i) (B i)
  unfold sumCoeff
  rw [pushCoeff_relabel e _ (Equiv.refl _) (fun _ => rfl) T, pushCoeff_equiv]
  simp only [pushCoeff, Pi.zero_apply, ite_self, Finset.sum_const_zero, add_zero]
  rfl
theorem zero_sumCoeff [∀ i, IsEmpty (A i)] (U : (∀ i, B i) → K) (x : ∀ i, A i ⊕ B i) :
    sumCoeff (0 : (∀ i, A i) → K) U x = U (fun i => Equiv.emptySum _ _ (x i)) := by
  rw [sumCoeff_comm, sumCoeff_zero]
  rfl
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
variable {I K : Type*} [Fintype I] [Nonempty I] [CommSemiring K] {A B C : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]
theorem sumCoeff_product_distrib (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (V : (∀ i, C i) → K) (x : ∀ i, A i × (B i ⊕ C i)) :
    T (fun i => (x i).1) * sumCoeff U V (fun i => (x i).2) =
      sumCoeff (fun y : ∀ i, A i × B i => T (fun i => (y i).1) * U (fun i => (y i).2))
        (fun y : ∀ i, A i × C i => T (fun i => (y i).1) * V (fun i => (y i).2))
        (fun i => Equiv.prodSumDistrib _ _ _ (x i)) := by
  classical
  let u (i : I) := (x i).1
  let v (i : I) := (x i).2
  change T u * sumCoeff U V v = sumCoeff _ _ (fun i => Equiv.prodSumDistrib _ _ _ (u i, v i))
  generalize v = w
  by_cases hl : ∃ y : ∀ i, B i, (fun i => Sum.inl (y i)) = w
  · obtain ⟨y, rfl⟩ := hl
    simp only [Equiv.prodSumDistrib_apply_left, sumCoeff_inl]
  by_cases hr : ∃ y : ∀ i, C i, (fun i => Sum.inr (y i)) = w
  · obtain ⟨y, rfl⟩ := hr
    simp only [Equiv.prodSumDistrib_apply_right, sumCoeff_inr]
  have hleft (z : ∀ i, A i × B i) :
      (fun i => Sum.inl (z i)) ≠ (fun i => Equiv.prodSumDistrib _ _ _ (u i, w i)) := by
    intro eq
    refine hl ⟨fun i => (z i).2, funext fun i => ?_⟩
    have h := congrArg (fun t => ((Equiv.prodSumDistrib (A i) (B i) (C i)).symm t).2)
      (congrFun eq i)
    simpa using h
  have hright (z : ∀ i, A i × C i) :
      (fun i => Sum.inr (z i)) ≠ (fun i => Equiv.prodSumDistrib _ _ _ (u i, w i)) := by
    intro eq
    refine hr ⟨fun i => (z i).2, funext fun i => ?_⟩
    have h := congrArg (fun t => ((Equiv.prodSumDistrib (A i) (B i) (C i)).symm t).2)
      (congrFun eq i)
    simpa using h
  rw [sumCoeff_mixed _ _ _ (not_exists.mp hl) (not_exists.mp hr),
    sumCoeff_mixed _ _ _ hleft hright, mul_zero]
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor.Raw
variable {I K : Type*} [Fintype I] [CommSemiring K]
theorem mul_assoc_equivalent (X Y Z : Raw I K) :
    ((X.mul Y).mul Z).Equivalent (X.mul (Y.mul Z)) := by
  apply reindex_equivalent (fun _ => Equiv.prodAssoc _ _ _)
  intro x
  apply mul_assoc
theorem mul_comm_equivalent (X Y : Raw I K) :
    (X.mul Y).Equivalent (Y.mul X) := by
  apply reindex_equivalent (fun _ => Equiv.prodComm _ _)
  intro x
  apply mul_comm
theorem one_mul_equivalent (X : Raw I K) : ((one I K).mul X).Equivalent X := by
  apply reindex_equivalent (fun _ => Equiv.punitProd _)
  intro x
  apply one_mul
theorem zero_mul_equivalent [Nonempty I] (X : Raw I K) :
    ((zero I K).mul X).Equivalent (zero I K) := by
  apply reindex_equivalent (fun _ => Equiv.pemptyProd _)
  intro x
  exact (x (Classical.arbitrary I)).1.elim
end SiteTensor.Raw
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
namespace SiteTensor
variable {I F : Type*} [Fintype I] [CommSemiring F] {A B C D : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
theorem restrict_product
    {X : (∀ i, A i) → F} {Y : (∀ i, B i) → F}
    {X' : (∀ i, C i) → F} {Y' : (∀ i, D i) → F}
    (hX : Crossing.IsRestriction X' X) (hY : Crossing.IsRestriction Y' Y) :
    Crossing.IsRestriction
      (fun a : ∀ i, C i × D i => X' (fun i => (a i).1) * Y' (fun i => (a i).2))
      (fun a : ∀ i, A i × B i => X (fun i => (a i).1) * Y (fun i => (a i).2)) := by
  classical
  obtain ⟨M, hM⟩ := hX
  obtain ⟨N, hN⟩ := hY
  refine ⟨fun i x a => M i x.1 a.1 * N i x.2 a.2, fun x => ?_⟩
  dsimp
  rw [hM, hN, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow I A B).symm _ _ fun a => ?_
  simp only [Finset.prod_mul_distrib]
  ac_rfl
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor.Raw
universe v u w
variable {I : Type u} {K : Type w} [Fintype I]
noncomputable def add [AddCommMonoid K] (X Y : Raw.{v} I K) : Raw.{v} I K :=
  ⟨fun i => X.Leg i ⊕ Y.Leg i, fun _ => inferInstance, sumCoeff X.coeff Y.coeff⟩
theorem mul_restricts [CommSemiring K] {X Y U V : Raw.{v} I K}
    (h : X.Restricts Y) (h' : U.Restricts V) : (X.mul U).Restricts (Y.mul V) :=
  restrict_product h h'
end SiteTensor.Raw
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
universe v u w
def TensorClass (I : Type u) (K : Type w) [Fintype I] [CommSemiring K] :=
  Quotient (Raw.setoid.{v} I K)
variable {I : Type u} {K : Type w} [Fintype I] [CommSemiring K]
def ofRaw (X : Raw.{v} I K) : TensorClass.{v} I K :=
  Quotient.mk _ X
@[simp] theorem ofRaw_eq_iff {X Y : Raw.{v} I K} :
    ofRaw X = ofRaw Y ↔ X.Equivalent Y := Quotient.eq
instance : LE (TensorClass.{v} I K) where
  le := Quotient.lift₂ Raw.Restricts fun _ _ _ _ hX hY => propext
    ⟨fun h => restrict_trans hX.2 (restrict_trans h hY.1),
     fun h => restrict_trans hX.1 (restrict_trans h hY.2)⟩
@[simp] theorem ofRaw_le_iff {X Y : Raw.{v} I K} :
    ofRaw X ≤ ofRaw Y ↔ X.Restricts Y := Iff.rfl
instance : PartialOrder (TensorClass.{v} I K) where
  le_refl X := Quotient.inductionOn X fun x => restrict_refl x.coeff
  le_trans X Y Z := Quotient.inductionOn₃ X Y Z fun _ _ _ => restrict_trans
  le_antisymm X Y := Quotient.inductionOn₂ X Y fun _ _ h g => Quotient.sound ⟨h, g⟩
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
namespace SiteTensor
open Crossing
variable {I : Type*} [Fintype I] {K : Type*} [CommSemiring K]
variable {A B C D : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (C i)] [∀ i, Fintype (D i)]
omit [∀ i, Fintype (C i)] in
theorem pushCoeff_restriction {X : (∀ i, B i) → K} {T : (∀ i, A i) → K}
    (M : ∀ i, B i → A i → K)
    (hM : ∀ x, X x = ∑ a, T a * ∏ i, M i (x i) (a i))
    (f : ∀ i, B i → C i) (y : ∀ i, C i) :
    pushCoeff (fun x i => f i (x i)) X y =
      ∑ a, T a * ∏ i, ∑ b, if f i b = y i then M i b (a i) else 0 := by
  simp only [Fintype.prod_sum, Finset.mul_sum, Fintype.prod_ite_zero, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  unfold pushCoeff
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hM x, funext_iff]
  split <;> simp [*]
theorem restrict_sum {X : (∀ i, B i) → K} {Y : (∀ i, D i) → K}
    {T : (∀ i, A i) → K} {U : (∀ i, C i) → K}
    (h : IsRestriction X T) (h' : IsRestriction Y U) :
    IsRestriction (sumCoeff X Y) (sumCoeff T U) := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨N, hN⟩ := h'
  let L (i : I) : B i ⊕ D i → A i ⊕ C i → K
    | .inl b, .inl a => M i b a
    | .inr d, .inr c => N i d c
    | _, _ => 0
  refine ⟨L, fun y => ?_⟩
  simp only [sumCoeff, add_mul, Finset.sum_add_distrib, sum_pushCoeff_mul]
  rw [pushCoeff_restriction M hM, pushCoeff_restriction N hN]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => congrArg (T a * ·) ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    cases y i <;> simp [L]
  · refine Finset.sum_congr rfl fun c _ => congrArg (U c * ·) ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    cases y i <;> simp [L]
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
universe v u w
variable {I : Type u} {K : Type w} [Fintype I] [CommSemiring K]
noncomputable section
instance : Add (TensorClass.{v} I K) where
  add := Quotient.map₂ Raw.add fun _ _ h _ _ g =>
    ⟨restrict_sum h.1 g.1, restrict_sum h.2 g.2⟩
instance : Mul (TensorClass.{v} I K) where
  mul := Quotient.map₂ Raw.mul fun _ _ h _ _ g =>
    ⟨Raw.mul_restricts h.1 g.1, Raw.mul_restricts h.2 g.2⟩
instance : Zero (TensorClass.{v} I K) := ⟨ofRaw (Raw.zero I K)⟩
instance : One (TensorClass.{v} I K) := ⟨ofRaw (Raw.one I K)⟩
@[simp] theorem ofRaw_add (X Y : Raw.{v} I K) : ofRaw (X.add Y) = ofRaw X + ofRaw Y := rfl
@[simp] theorem ofRaw_mul (X Y : Raw.{v} I K) : ofRaw (X.mul Y) = ofRaw X * ofRaw Y := rfl
@[simp] theorem ofRaw_zero : ofRaw (Raw.zero.{v} I K) = 0 := rfl
@[simp] theorem ofRaw_one : ofRaw (Raw.one.{v} I K) = 1 := rfl
private theorem class_add_comm (X Y : TensorClass.{v} I K) : X + Y = Y + X :=
  Quotient.inductionOn₂ X Y fun x y => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.sumComm _ _) (sumCoeff_comm x.coeff y.coeff)
private theorem class_zero_add (X : TensorClass.{v} I K) : 0 + X = X := by
  let (i : I) : IsEmpty ((Raw.zero.{v} I K).Leg i) := inferInstanceAs (IsEmpty PEmpty)
  exact
  Quotient.inductionOn X fun x => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.emptySum _ _) (zero_sumCoeff x.coeff)
private theorem class_mul_comm (X Y : TensorClass.{v} I K) : X * Y = Y * X :=
  Quotient.inductionOn₂ X Y fun x y => Quotient.sound (x.mul_comm_equivalent y)
private theorem class_one_mul (X : TensorClass.{v} I K) : 1 * X = X :=
  Quotient.inductionOn X fun x => Quotient.sound (x.one_mul_equivalent)
variable [Nonempty I]
private theorem class_zero_mul (X : TensorClass.{v} I K) : 0 * X = 0 :=
  Quotient.inductionOn X fun x => Quotient.sound (x.zero_mul_equivalent)
private theorem class_left_distrib (X Y Z : TensorClass.{v} I K) :
    X * (Y + Z) = X * Y + X * Z :=
  Quotient.inductionOn₃ X Y Z fun x y z => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.prodSumDistrib _ _ _)
      (sumCoeff_product_distrib x.coeff y.coeff z.coeff)
instance : CommSemiring (TensorClass.{v} I K) where
  add_assoc X Y Z := Quotient.inductionOn₃ X Y Z fun x y z => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.sumAssoc _ _ _) (sumCoeff_assoc x.coeff y.coeff z.coeff)
  add_comm := class_add_comm
  zero_add := class_zero_add
  add_zero X := (class_add_comm X 0).trans (class_zero_add X)
  nsmul := nsmulRec
  mul_assoc X Y Z := Quotient.inductionOn₃ X Y Z fun x y z =>
    Quotient.sound (x.mul_assoc_equivalent y z)
  mul_comm := class_mul_comm
  one_mul := class_one_mul
  mul_one X := (class_mul_comm X 1).trans (class_one_mul X)
  zero_mul := class_zero_mul
  mul_zero X := (class_mul_comm X 0).trans (class_zero_mul X)
  left_distrib := class_left_distrib
  right_distrib X Y Z := by rw [class_mul_comm, class_left_distrib, class_mul_comm Z X, class_mul_comm Z Y]
omit [Nonempty I] in
theorem add_mono {X Y U V : TensorClass.{v} I K} (h : X ≤ Y) (g : U ≤ V) :
    X + U ≤ Y + V := by
  induction X using Quotient.inductionOn
  induction Y using Quotient.inductionOn
  induction U using Quotient.inductionOn
  induction V using Quotient.inductionOn
  exact restrict_sum h g
omit [Nonempty I] in
theorem mul_mono {X Y U V : TensorClass.{v} I K} (h : X ≤ Y) (g : U ≤ V) :
    X * U ≤ Y * V := by
  induction X using Quotient.inductionOn
  induction Y using Quotient.inductionOn
  induction U using Quotient.inductionOn
  induction V using Quotient.inductionOn
  exact Raw.mul_restricts h g
end
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
universe v u w
variable {I : Type u} [Fintype I] {K : Type w}
section Semiring
variable [CommSemiring K]
theorem zero_le_tensor [Nonempty I] (X : TensorClass.{v} I K) : 0 ≤ X := by
  induction X using Quotient.inductionOn with
  | h x =>
    change (Raw.zero I K).Restricts x
    refine ⟨fun _ _ _ => 0, fun y => ?_⟩
    exact (y (Classical.arbitrary I)).elim
theorem ofRaw_eq_zero_iff (X : Raw.{v} I K) : ofRaw X = 0 ↔ X.coeff = 0 := by
  change ofRaw X = ofRaw (Raw.zero I K) ↔ _
  rw [ofRaw_eq_iff]
  constructor
  · rintro ⟨⟨M, hM⟩, _⟩
    funext x
    simpa [Raw.zero] using hM x
  · intro h
    constructor
    · refine ⟨fun _ _ _ => 0, fun x => ?_⟩
      simp [Raw.zero, h]
    · refine ⟨fun _ _ _ => 0, fun y => ?_⟩
      simp [Raw.zero, h]
instance [Nonempty I] [Nontrivial K] : Nontrivial (TensorClass.{v} I K) := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have h' := (ofRaw_eq_zero_iff (Raw.one.{v} I K)).mp h
  exact one_ne_zero (congrFun h' (fun _ => PUnit.unit))
instance [Nonempty I] [NoZeroDivisors K] : NoZeroDivisors (TensorClass.{v} I K) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} := by
    induction a using Quotient.inductionOn with | h X =>
    induction b using Quotient.inductionOn with | h Y =>
    change ofRaw (X.mul Y) = 0 → ofRaw X = 0 ∨ ofRaw Y = 0
    simp only [ofRaw_eq_zero_iff]
    intro h
    by_cases hX : X.coeff = 0
    · exact Or.inl hX
    · apply Or.inr
      obtain ⟨x, hx⟩ : ∃ x, X.coeff x ≠ 0 := by
        by_contra! h0
        exact hX (funext h0)
      funext y
      exact (mul_eq_zero.mp (congrFun h (fun i => (x i, y i)))).resolve_left hx
end Semiring
theorem one_le_of_ne_zero [Nonempty I] [Field K] {X : TensorClass.{v} I K}
    (h : X ≠ 0) : 1 ≤ X := by
  induction X using Quotient.inductionOn with
  | h x =>
    exact x.one_restricts_of_nonzero (fun h0 => h ((ofRaw_eq_zero_iff x).mpr h0))
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped NNReal
namespace SiteTensor
universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → _))
def rawLogPrice (c : ℝ) (X : Raw.{v} I K) : ℝ :=
  c * Real.logb 2 (φ.val (ofRaw X) : ℝ)
theorem one_le_raw_spectralValue (X : Raw.{v} I K) (h : X.coeff ≠ 0) :
    1 ≤ φ.val (ofRaw X) :=
  one_le_spectral_value φ (X.one_restricts_of_nonzero h)
theorem rawLogPrice_zero (c : ℝ) (X : Raw.{v} I K) (h : X.coeff = 0) :
    rawLogPrice φ c X = 0 := by
  simp [rawLogPrice, (ofRaw_eq_zero_iff X).mpr h, φ.property.1]
theorem rawLogPrice_nonneg {c : ℝ} (hc : 0 ≤ c) (X : Raw.{v} I K) :
    0 ≤ rawLogPrice φ c X := by
  by_cases h : X.coeff = 0
  · rw [rawLogPrice_zero φ c X h]
  · apply mul_nonneg hc (Real.logb_nonneg (by norm_num) _)
    exact_mod_cast one_le_raw_spectralValue φ X h
theorem rawLogPrice_mono {c : ℝ} (hc : 0 ≤ c) {X Y : Raw.{v} I K}
    (h : X.Restricts Y) : rawLogPrice φ c X ≤ rawLogPrice φ c Y := by
  by_cases hX : X.coeff = 0
  · rw [rawLogPrice_zero φ c X hX]
    exact rawLogPrice_nonneg φ hc _
  · apply mul_le_mul_of_nonneg_left _ hc
    apply Real.logb_le_logb_of_le (by norm_num)
    · exact_mod_cast zero_lt_one.trans_le (one_le_raw_spectralValue φ X hX)
    · exact_mod_cast φ.property.2.2.2.2 (ofRaw X) (ofRaw Y) h
theorem rawLogPrice_mul (c : ℝ) (X Y : Raw.{v} I K)
    (hX : X.coeff ≠ 0) (hY : Y.coeff ≠ 0) :
    rawLogPrice φ c (X.mul Y) = rawLogPrice φ c X + rawLogPrice φ c Y := by
  have pos (T : Raw.{v} I K) (h : T.coeff ≠ 0) : (φ.val (ofRaw T) : ℝ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le (one_le_raw_spectralValue φ T h)).ne'
  simp only [rawLogPrice, ofRaw_mul, φ.property.2.2.2.1, NNReal.coe_mul,
    Real.logb_mul (pos X hX) (pos Y hY), mul_add]
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
namespace SiteTensor.Raw
universe v
variable (I K : Type*) [Fintype I] [CommSemiring K]
theorem diagonal_equiv {α β : Type v} [Fintype α] [Fintype β] (e : α ≃ β) :
    (diagonal I K α).Equivalent (diagonal I K β) := by
  classical
  apply reindex_equivalent (fun _ => e)
  intro (x : I → α)
  simp only [diagonal]
  refine Fintype.sum_equiv e _ _ fun a => ?_
  have h : (fun i => e (x i)) = (fun _ => e a) ↔ x = (fun _ => a) := by
    simp [funext_iff]
  congr! 1
  exact h.symm
theorem diagonal_empty_equivalent :
    (diagonal I K PEmpty.{v + 1}).Equivalent (zero I K) := by
  classical
  apply reindex_equivalent (fun _ => Equiv.refl _)
  intro x
  simp [diagonal]
theorem diagonal_unit_equivalent :
    (diagonal I K PUnit.{v + 1}).Equivalent (one I K) := by
  classical
  apply reindex_equivalent (X := diagonal I K _) (Y := one I K) (fun _ => Equiv.refl _)
  intro (x : I → PUnit.{v + 1})
  simp [diagonal, one, Subsingleton.elim x (fun _ => PUnit.unit)]
private theorem push_constant_labels (α : Type v) [Fintype α] {Y : Type*}
    (f : (I → α) → Y) (y : Y) :
    pushCoeff f (diagonal I K α).coeff y =
      ∑ a : α, if f (fun _ => a) = y then 1 else 0 := by
  classical
  let c (a : α) : I → α := fun _ => a
  have hc : (diagonal I K α).coeff = pushCoeff c (fun _ => 1) := by
    funext x
    apply Finset.sum_congr rfl
    intro a _
    change (if x = c a then (1 : K) else 0) = (if c a = x then 1 else 0)
    congr! 1
    exact eq_comm
  rw [hc, pushCoeff_comp]
  rfl
theorem diagonal_sum_equivalent (α β : Type v) [Fintype α] [Fintype β] :
    ((diagonal I K α).add (diagonal I K β)).Equivalent (diagonal I K (α ⊕ β)) := by
  classical
  apply reindex_equivalent (X := (diagonal I K α).add (diagonal I K β))
    (Y := diagonal I K (α ⊕ β)) (fun _ => Equiv.refl _)
  intro (x : I → α ⊕ β)
  let f (y : I → α) (i : I) : α ⊕ β := Sum.inl (y i)
  let g (y : I → β) (i : I) : α ⊕ β := Sum.inr (y i)
  change pushCoeff f (diagonal I K α).coeff x +
    pushCoeff g (diagonal I K β).coeff x = (diagonal I K (α ⊕ β)).coeff x
  rw [push_constant_labels I K α, push_constant_labels I K β]
  simp only [diagonal, Fintype.sum_sum_type]
  apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro a _ <;>
    congr! 1 <;> exact eq_comm
end SiteTensor.Raw
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
universe v
variable (I K : Type*) [Fintype I] [Nonempty I] [CommSemiring K]
@[simp] theorem ofRaw_diagonal_eq_natCast (α : Type v) [Fintype α] :
    ofRaw (Raw.diagonal I K α) = (Fintype.card α : TensorClass.{v} I K) := by
  classical
  refine Fintype.induction_empty_option (P := fun β _ =>
    ofRaw (Raw.diagonal I K β) = (Fintype.card β : TensorClass.{v} I K)) ?_ ?_ ?_ α
  · intro β γ _ e ih
    let := Fintype.ofEquiv γ e.symm
    rw [← Fintype.card_congr e, ← ih]
    exact ofRaw_eq_iff.mpr (Raw.diagonal_equiv I K e.symm)
  · rw [Fintype.card_pempty, Nat.cast_zero, ← ofRaw_zero]
    exact ofRaw_eq_iff.mpr (Raw.diagonal_empty_equivalent I K)
  · intro β _ ih
    rw [Fintype.card_option, Nat.cast_add, Nat.cast_one, ← ih, ← ofRaw_one]
    have h := Raw.diagonal_equiv I K (Equiv.optionEquivSumPUnit.{v} β)
    rw [ofRaw_eq_iff.mpr h, ← ofRaw_eq_iff.mpr (Raw.diagonal_sum_equivalent I K β PUnit.{v + 1}),
      ofRaw_add, ofRaw_eq_iff.mpr (Raw.diagonal_unit_equivalent I K)]
@[simp] theorem ofRaw_diagonal_fin_eq_natCast (n : ℕ) :
    ofRaw (Raw.diagonal I K (Fin n)) = (n : TensorClass.{0} I K) := by
  simpa only [Fintype.card_fin] using ofRaw_diagonal_eq_natCast I K (Fin n)
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
namespace SiteTensor.Raw
universe u v w
variable (I : Type u) (K : Type w) [Fintype I] [Nonempty I] [CommSemiring K]
variable {α β : Type v} [Fintype α] [Fintype β]
theorem diagonal_restricts_of_embedding (e : α ↪ β) :
    (diagonal I K α).Restricts (diagonal I K β) := by
  classical
  unfold Restricts diagonal
  refine ⟨fun _ a b => if b = e a then 1 else 0, fun x => ?_⟩
  simp_rw [Fintype.prod_boole]
  have heq (y : I → β) : (∀ i, y i = e (x i)) ↔ y = fun i => e (x i) :=
    funext_iff.symm
  simp only [heq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  let i₀ : I := Classical.choice inferInstance
  rw [Finset.sum_eq_single (x i₀), Finset.sum_eq_single (e (x i₀))]
  · simp [funext_iff]
  · intro b _ hb
    exact ite_eq_right fun h => (hb (congrFun h i₀).symm).elim
  · simp
  · intro a _ ha
    exact ite_eq_right fun h => (ha (congrFun h i₀).symm).elim
  · simp
end SiteTensor.Raw
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical
section
namespace SiteTensor.Raw
variable {I J K : Type*} [Fintype I]
def group (T : SiteTensor.Raw I K) (σ : I → J) : SiteTensor.Raw J K where
  Leg := fun j => (i : {i : I // σ i = j}) → T.Leg i.1
  finiteLeg := fun _ => inferInstance
  coeff := fun x => T.coeff (fun i => x (σ i) ⟨i, rfl⟩)
theorem group_ne_zero_iff [Zero K] (T : SiteTensor.Raw I K) (σ : I → J) :
    (T.group σ).coeff ≠ 0 ↔ T.coeff ≠ 0 := by
  constructor
  · intro h hzero
    exact h (funext fun x => congrFun hzero _)
  · intro h hzero
    apply h
    exact funext fun x => congrFun hzero (fun _ i => x i.1)
end SiteTensor.Raw
open SiteTensor
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
open scoped Classical
def groupIndexEquiv {I J : Type*} (σ : I → J) (A : I → Type*) :
    (∀ i, A i) ≃ (∀ j, (t : {i // σ i = j}) → A t.1) :=
  Equiv.piCongrFiberwise (fun _ => Equiv.refl _)
@[simp] theorem groupIndexEquiv_apply {I J : Type*} (σ : I → J) (A : I → Type*)
    (a : ∀ i, A i) (j : J) (t : {i // σ i = j}) : groupIndexEquiv σ A a j t = a t.1 := rfl
@[simp] theorem groupIndexEquiv_symm_apply {I J : Type*} (σ : I → J) (A : I → Type*)
    (a : ∀ j, (t : {i // σ i = j}) → A t.1) (i : I) :
    (groupIndexEquiv σ A).symm a i = a (σ i) ⟨i, rfl⟩ := rfl
namespace Raw
variable {I J K : Type*} [Fintype I] [Fintype J] [CommSemiring K]
theorem group_restricts (σ : I → J) {X Y : Raw I K} (h : X.Restricts Y) :
    (X.group σ).Restricts (Y.group σ) := by
  classical
  obtain ⟨M, hM⟩ := h
  refine ⟨fun j b a => ∏ i : {i // σ i = j}, M i.1 (b i) (a i), fun x => ?_⟩
  change X.coeff ((groupIndexEquiv σ X.Leg).symm x) = _
  rw [hM]
  refine Fintype.sum_equiv (groupIndexEquiv σ Y.Leg) _ _ fun a => ?_
  apply congrArg (Y.coeff a * ·)
  let w (p : Σ j, {i // σ i = j}) := M p.2.1 (x p.1 p.2) (a p.2.1)
  calc
    _ = ∏ p, w p := Fintype.prod_equiv (Equiv.sigmaFiberEquiv σ).symm _ _ (fun i => rfl)
    _ = _ := Fintype.prod_sigma w
theorem group_mul_equivalent (σ : I → J) (X Y : Raw I K) :
    ((X.mul Y).group σ).Equivalent ((X.group σ).mul (Y.group σ)) := by
  apply reindex_equivalent (fun j =>
    Equiv.arrowProdEquivProdArrow {i // σ i = j} (fun i => X.Leg i.1) (fun i => Y.Leg i.1))
  intro x
  rfl
theorem group_one_equivalent (σ : I → J) :
    ((one I K).group σ).Equivalent (one J K) := by
  let (j : J) : Unique (((one I K).group σ).Leg j) := inferInstanceAs (Unique (∀ _ : {i // σ i = j}, PUnit))
  apply reindex_equivalent (fun _ => Equiv.equivPUnit _)
  intro x
  rfl
end Raw
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
noncomputable section
open scoped NNReal
universe v u u' w
variable {I : Type u} {J : Type u'} {K : Type w} [Fintype I] [Fintype J] [CommSemiring K]
def groupClass (σ : I → J) : TensorClass.{v} I K → TensorClass.{max u v} J K :=
  Quotient.map (fun X => X.group σ) fun _ _ h =>
    ⟨Raw.group_restricts σ h.1, Raw.group_restricts σ h.2⟩
@[simp] theorem groupClass_ofRaw (σ : I → J) (X : Raw.{v} I K) :
    groupClass σ (ofRaw X) = ofRaw (X.group σ) := rfl
theorem groupClass_mono (σ : I → J) : Monotone (groupClass (K := K) σ) :=
  fun X Y => Quotient.inductionOn₂ X Y fun _ _ => Raw.group_restricts σ
def groupMulHom [Nonempty I] [Nonempty J] (σ : I → J) :
    TensorClass.{v} I K →* TensorClass.{max u v} J K where
  toFun := groupClass σ
  map_one' := ofRaw_eq_iff.mpr (Raw.group_one_equivalent σ)
  map_mul' X Y := Quotient.inductionOn₂ X Y fun x y =>
    ofRaw_eq_iff.mpr (Raw.group_mul_equivalent σ x y)
section Logarithms
variable {A B : Type} {F : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Field F]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} B F → _ → Prop))
theorem rawLogPrice_group_diagonal (σ : A → B) (c : ℝ) {α : Type} [Fintype α] [Nonempty α] :
    rawLogPrice φ c ((Raw.diagonal A F α).group σ) =
      rawLogPrice φ c ((Raw.diagonal A F (Fin 2)).group σ) * Real.logb 2 (Fintype.card α) := by
  let v : TensorClass.{0} A F →* ℝ≥0 := (normalizedSpectrum.toRingHom φ).toMonoidHom.comp (groupMulHom σ)
  have hv : ∀ {m n : ℕ}, 0 < m → m ≤ n → v m ≤ v n := by
    intro m n _ h
    apply φ.property.2.2.2.2
    apply groupClass_mono σ
    rw [← ofRaw_diagonal_fin_eq_natCast A F m, ← ofRaw_diagonal_fin_eq_natCast A F n]
    exact Raw.diagonal_restricts_of_embedding A F (Fin.castLEEmb h)
  have h := spectral_natCast_logb v hv (Fintype.card α) Fintype.card_pos
  have eval (β : Type) [Fintype β] : φ.val (ofRaw ((Raw.diagonal A F β).group σ)) =
      v (Fintype.card β : TensorClass.{0} A F) := by
    rw [← ofRaw_diagonal_eq_natCast A F β]
    rfl
  rw [rawLogPrice, rawLogPrice, eval α, eval (Fin 2), Fintype.card_fin, Nat.cast_ofNat, h, mul_assoc]
end Logarithms
end
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor.Raw
open scoped Classical
universe u
theorem grouped_diagonal_reindex {A B : Type u} {J : Type*} [Fintype A] [Fintype B] [Fintype J]
    (K D : Type*) [CommSemiring K] [Fintype D] (e : A ≃ B) (σ : B → J) :
    ((diagonal B K D).group σ).Equivalent ((diagonal A K D).group (σ ∘ e)) := by
  let fiber (j : J) : {i : A // σ (e i) = j} ≃ {i : B // σ i = j} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  apply reindex_equivalent (fun j => Equiv.arrowCongr (fiber j).symm (Equiv.refl D))
  intro x
  apply Finset.sum_congr rfl
  intro d _
  change (if (fun i => x (σ i) ⟨i, rfl⟩) = (fun _ => d) then (1 : K) else 0) =
    (if (fun i => x (σ (e i)) ⟨e i, rfl⟩) = (fun _ => d) then 1 else 0)
  let labels (i : B) : D := x (σ i) ⟨i, rfl⟩
  have heq : (labels = fun _ => d) ↔ ((labels ∘ e) = fun _ => d) := by
    constructor
    · intro h
      exact funext fun i => congrFun h (e i)
    · intro h
      exact funext fun i => by simpa [Function.comp] using congrFun h (e.symm i)
  exact if_congr heq rfl rfl
theorem grouped_wire_symm {J : Type*} [Fintype J] (K D : Type*) [CommSemiring K]
    [Fintype D] (s t : J) :
    ((diagonal (Fin 2) K D).group ![s, t]).Equivalent
      ((diagonal (Fin 2) K D).group ![t, s]) := by
  have h : ![s, t] ∘ Fin.revPerm = ![t, s] := by
    funext i
    fin_cases i <;> rfl
  rw [← h]
  exact grouped_diagonal_reindex K D (Fin.revPerm (n := 2)) ![s, t]
end SiteTensor.Raw
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor.Raw
open scoped Classical BigOperators
variable {I J K : Type*} [Fintype I] [Fintype J] [CommSemiring K]
private theorem diagonal_pair_coeff {D : Type*} [Fintype D] (z : Fin 2 → D) :
    (diagonal (Fin 2) K D).coeff z = if z 0 = z 1 then 1 else 0 := by
  classical
  have he (a : D) : (z = fun _ => a) ↔ z 0 = a ∧ z 1 = a := by
    constructor
    · rintro rfl
      exact ⟨rfl,rfl⟩
    · intro h
      funext i
      fin_cases i <;> simp [h]
  unfold diagonal
  dsimp only
  rw [Finset.sum_eq_single (z 0)]
  · simp only [he, true_and, eq_comm]
  · intro a _ ha
    exact ite_eq_right (fun h => ha ((he a).mp h).1.symm)
  · simp
theorem move_restricts_with_wire (T : Raw I K) (p q : I → J) (i₀ : I)
    (hagree : ∀ i, i ≠ i₀ → p i = q i) :
    (T.group q).Restricts ((T.group p).mul ((diagonal (Fin 2) K (T.Leg i₀)).group
      ![p i₀, q i₀])) := by
  classical
  let loc : Fin 2 → J := ![p i₀, q i₀]
  let W := (diagonal (Fin 2) K (T.Leg i₀)).group loc
  let S := (T.group p).mul W
  let ok (j : J) (x : (T.group q).Leg j) (y : S.Leg j) : Prop :=
    (∀ (i : I), i ≠ i₀ → ∀ (h : p i = j) (h' : q i = j),
      y.1 ⟨i, h⟩ = x ⟨i, h'⟩) ∧
    (∀ h : p i₀ = j, y.1 ⟨i₀, h⟩ = y.2 ⟨0, h⟩) ∧
    (∀ h : q i₀ = j, y.2 ⟨1, h⟩ = x ⟨i₀, h⟩)
  refine ⟨fun j x y => if ok j x y then 1 else 0, ?_⟩
  intro x
  let v (i : I) := x (q i) ⟨i, rfl⟩
  let keep (j : J) : S.Leg j := (fun i => v i.val, fun _ => v i₀)
  have hok (j : J) : ok j (x j) (keep j) := by
    refine ⟨?_, fun _ => rfl, ?_⟩
    · rintro i _ h rfl
      rfl
    · rintro rfl
      rfl
  have hcoeff (y : ∀ j, S.Leg j) : S.coeff y =
      T.coeff (fun i => (y (p i)).1 ⟨i, rfl⟩) *
        (if (y (p i₀)).2 ⟨0, rfl⟩ = (y (q i₀)).2 ⟨1, rfl⟩ then 1 else 0) :=
    congrArg (_ * ·) (diagonal_pair_coeff (fun k => (y (loc k)).2 ⟨k, rfl⟩))
  change T.coeff v = ∑ y : ∀ j, S.Leg j, S.coeff y * ∏ j, if ok j (x j) (y j) then 1 else 0
  have hp (y : ∀ j, S.Leg j) : (∏ j, if ok j (x j) (y j) then (1 : K) else 0) =
      if ∀ j, ok j (x j) (y j) then 1 else 0 := Fintype.prod_boole
  simp_rw [hp]
  rw [Finset.sum_eq_single keep]
  · rw [hcoeff keep]
    have hw : (keep (p i₀)).2 ⟨0, rfl⟩ = (keep (q i₀)).2 ⟨1, rfl⟩ := rfl
    rw [ite_eq_left hw, ite_eq_left hok, mul_one, mul_one]
  · intro y _ hy
    by_cases hc : ∀ j, ok j (x j) (y j)
    · by_cases hw : (y (p i₀)).2 ⟨0, rfl⟩ = (y (q i₀)).2 ⟨1, rfl⟩
      · exfalso
        apply hy
        have hright : (y (q i₀)).2 ⟨1,rfl⟩ = v i₀ := (hc _).2.2 rfl
        have hleft := hw.trans hright
        funext j
        apply Prod.ext
        · funext ⟨i, hi⟩
          subst j
          by_cases h : i = i₀
          · subst i
            exact ((hc _).2.1 rfl).trans hleft
          · have transport (j : J) (hj : q i = j) : x j ⟨i, hj⟩ = v i := by
              subst j
              rfl
            exact ((hc _).1 i h rfl (hagree i h).symm).trans (transport _ _)
        · funext ⟨k, hk⟩
          subst j
          fin_cases k
          · exact hleft
          · exact hright
      · simp [hcoeff, hw]
    · simp [hc]
  · simp
end SiteTensor.Raw
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
noncomputable section
open scoped NNReal
variable {I J : Type} {K : Type*} [Fintype I] [Fintype J] [Nonempty J] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)
def rawWireDistance (s t : J) : ℝ :=
  rawLogPrice φ c ((Raw.diagonal (Fin 2) K (Fin 2)).group ![s, t])
theorem rawWireDistance_symm (s t : J) : rawWireDistance φ c s t = rawWireDistance φ c t s := by
  unfold rawWireDistance rawLogPrice
  rw [ofRaw_eq_iff.mpr (Raw.grouped_wire_symm K (Fin 2) s t)]
private theorem diagonal_pair_ne_zero (D : Type) [Fintype D] [Nonempty D] :
    (Raw.diagonal (Fin 2) K D).coeff ≠ 0 := by
  classical
  let d := Classical.arbitrary D
  intro hzero
  have h := congrFun hzero (fun _ => d)
  have he (a : D) : (fun _ : Fin 2 => d) = (fun _ => a) ↔ d = a :=
    ⟨fun h => congrFun h 0, by rintro rfl; rfl⟩
  change (Raw.diagonal (Fin 2) K D).coeff (fun _ => d) = (0 : K) at h
  simp [Raw.diagonal, he] at h
omit [Nonempty J] in
theorem Raw.group_const_restricts_one (T : Raw.{0} I K) (s : J) :
    (T.group (fun _ => s)).Restricts (Raw.one J K) := by
  classical
  let M (j : J) (b : (T.group (fun _ => s)).Leg j) (_ : (Raw.one J K).Leg j) : K :=
    if h : s = j then T.coeff (fun i => b ⟨i, h⟩) else 1
  refine ⟨M, fun x => ?_⟩
  let (j : J) : Unique ((Raw.one J K).Leg j) := inferInstanceAs (Unique PUnit)
  rw [Fintype.sum_unique]
  change T.coeff (fun i => x s ⟨i, rfl⟩) = 1 * ∏ j, M j (x j) PUnit.unit
  rw [one_mul, Finset.prod_eq_single s]
  · simp [M]
  · intro j _ hj
    simp [M, Ne.symm hj]
  · simp
theorem rawLogPrice_const (hc : 0 ≤ c) (T : Raw.{0} I K) (s : J) :
    rawLogPrice φ c (T.group (fun _ => s)) = 0 := by
  apply le_antisymm _ (rawLogPrice_nonneg φ hc _)
  have h := rawLogPrice_mono φ hc (T.group_const_restricts_one s)
  simpa [rawLogPrice, φ.property.2.1] using h
@[simp] theorem rawWireDistance_self (hc : 0 ≤ c) (s : J) : rawWireDistance φ c s s = 0 := by
  have h : (![s, s] : Fin 2 → J) = fun _ => s := by funext i; fin_cases i <;> rfl
  simpa only [rawWireDistance, h] using rawLogPrice_const φ c hc (Raw.diagonal (Fin 2) K (Fin 2)) s
theorem rawLogPrice_move_le (hc : 0 ≤ c) (T : Raw.{0} I K) (hT : T.coeff ≠ 0)
    (a b : I → J) (i : I) (hagree : ∀ j, j ≠ i → a j = b j) :
    rawLogPrice φ c (T.group b) ≤ rawLogPrice φ c (T.group a) +
      rawWireDistance φ c (a i) (b i) * Real.logb 2 (Fintype.card (T.Leg i)) := by
  classical
  obtain ⟨x, _⟩ : ∃ x, T.coeff x ≠ 0 := by
    by_contra! h
    exact hT (funext h)
  let : Nonempty (T.Leg i) := ⟨x i⟩
  let f := ![a i, b i]
  have hd := ((Raw.diagonal (Fin 2) K (T.Leg i)).group_ne_zero_iff f).mpr
    (diagonal_pair_ne_zero (K := K) (T.Leg i))
  have h := rawLogPrice_mono φ hc (Raw.move_restricts_with_wire T a b i hagree)
  rw [rawLogPrice_mul φ c _ _ ((T.group_ne_zero_iff a).mpr hT) hd,
    rawLogPrice_group_diagonal] at h
  exact h
theorem rawWireDistance_triangle (hc : 0 ≤ c) (s t u : J) :
    rawWireDistance φ c s u ≤ rawWireDistance φ c s t + rawWireDistance φ c t u := by
  let W := Raw.diagonal (Fin 2) K (Fin 2)
  have h := rawLogPrice_move_le φ c hc W (diagonal_pair_ne_zero (Fin 2))
    ![s, t] ![s, u] 1 (by intro i hi; fin_cases i <;> simp_all)
  simpa [W, rawWireDistance, Raw.diagonal, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    using h
end
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
theorem rank_fromBlocks_diagonal {F I J I' J' : Type*} [Field F] [Fintype J] [Fintype J']
    (A : Matrix I J F) (B : Matrix I' J' F) :
    (Matrix.fromBlocks A 0 0 B).rank = A.rank + B.rank := by
  let e := LinearEquiv.sumArrowLequivProdArrow I I' F F
  let d := LinearEquiv.sumArrowLequivProdArrow J J' F F
  have h : (Matrix.fromBlocks A 0 0 B).mulVecLin =
      e.symm.toLinearMap ∘ₗ (A.mulVecLin.prodMap B.mulVecLin) ∘ₗ d.toLinearMap := by
    apply LinearMap.ext
    intro x
    ext (i | i) <;> simp [Matrix.fromBlocks_mulVec, e, d] <;> rfl
  rw [Matrix.rank, h, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top, LinearEquiv.finrank_map_eq, LinearMap.range_prodMap]
  let e2 : ((LinearMap.range A.mulVecLin).prod (LinearMap.range B.mulVecLin)) ≃ₗ[F]
      (LinearMap.range A.mulVecLin) × (LinearMap.range B.mulVecLin) :=
    { toFun := fun x => (⟨x.1.1, (Submodule.mem_prod.mp x.2).1⟩, ⟨x.1.2, (Submodule.mem_prod.mp x.2).2⟩)
      invFun := fun y => ⟨(y.1.1, y.2.1), Submodule.mem_prod.mpr ⟨y.1.2, y.2.2⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [e2.finrank_eq, Module.finrank_prod]
  rfl
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped BigOperators Classical
namespace Crossing
variable {I : Type*} (s : I → Prop) [DecidablePred s]
abbrev cutEquiv (B : I → Type*) := Equiv.piEquivPiSubtypeProd s B
private theorem cut_symm_left {D : I → Type*} (u : ∀ i : {i // s i}, D i)
      (v : ∀ i : {i // ¬ s i}, D i) (i : {i // s i}) :
      (cutEquiv s D).symm (u,v) i = u i := by
    simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]
private theorem cut_symm_right {D : I → Type*} (u : ∀ i : {i // s i}, D i)
      (v : ∀ i : {i // ¬ s i}, D i) (i : {i // ¬ s i}) :
      (cutEquiv s D).symm (u,v) i = v i := by
    simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]
def cutMatrix {K : Type*} {B : I → Type*} (T : (∀ i, B i) → K) :
    Matrix (∀ i : {i // s i}, B i) (∀ i : {i // ¬ s i}, B i) K :=
  fun r c ↦ T ((cutEquiv s B).symm (r, c))
variable {K : Type*} [Field K] [Fintype I] {A B : I → Type*}
variable [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
omit [∀ i, Fintype (B i)] in
theorem cutMatrix_factor_of_restriction (X : (∀ i, B i) → K) (Y : (∀ i, A i) → K)
    (h : IsRestriction X Y) :
    ∃ (P : Matrix (∀ i : {i // s i}, B i) (∀ i : {i // s i}, A i) K)
      (Q : Matrix (∀ i : {i // ¬ s i}, A i) (∀ i : {i // ¬ s i}, B i) K),
      cutMatrix s X = P * cutMatrix s Y * Q := by
  classical
  obtain ⟨M, hm⟩ := h
  let P : Matrix (∀ i : {i // s i}, B i) (∀ i : {i // s i}, A i) K :=
    fun r a ↦ ∏ i : {i // s i}, M i.val (r i) (a i)
  let Q : Matrix (∀ i : {i // ¬ s i}, A i) (∀ i : {i // ¬ s i}, B i) K :=
    fun a c ↦ ∏ i : {i // ¬ s i}, M i.val (c i) (a i)
  refine ⟨P, Q, ?_⟩
  ext r c
  rw [cutMatrix, hm, ← Equiv.sum_comp (cutEquiv s A).symm, Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  rw [← Fintype.prod_subtype_mul_prod_subtype s]
  simp only [cut_symm_left, cut_symm_right, P, Q, cutMatrix]
  ring
theorem cutMatrix_rank_le_of_restriction (X : (∀ i, B i) → K) (Y : (∀ i, A i) → K)
    (h : IsRestriction X Y) : (cutMatrix s X).rank ≤ (cutMatrix s Y).rank := by
  obtain ⟨P, Q, e⟩ := cutMatrix_factor_of_restriction s X Y h
  rw [e]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
end Crossing
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
noncomputable section
section
private theorem rank_eq_rank_on_support {K R C R' C' : Type*} [Field K]
    [Fintype R'] [Fintype C'] [Fintype C] (M : Matrix R C K)
    (r : R' ↪ R) (c : C' ↪ C)
    (hr : ∀ x ∉ Set.range r, ∀ y, M x y = 0)
    (hc : ∀ y ∉ Set.range c, ∀ x, M x y = 0) :
    M.rank = (M.submatrix r c).rank := by
  classical
  let P : Matrix R R' K := fun i a => if i = r a then 1 else 0
  let Q : Matrix C' C K := fun b j => if c b = j then 1 else 0
  have left (x : R) (b : C') : (P * M.submatrix r c) x b = M x (c b) := by
    rw [Matrix.mul_apply]
    by_cases hx : x ∈ Set.range r
    · obtain ⟨a, rfl⟩ := hx
      simp [P, Matrix.submatrix, r.injective.eq_iff, ite_mul]
    · have h (a : R') : x ≠ r a := fun e => hx ⟨a, e.symm⟩
      simp [P, h, hr _ hx]
  have eq : M = P * M.submatrix r c * Q := by
    ext x y
    rw [Matrix.mul_apply]
    simp only [left]
    by_cases hy : y ∈ Set.range c
    · obtain ⟨b, rfl⟩ := hy
      simp [Q, c.injective.eq_iff, mul_ite]
    · have h (b : C') : c b ≠ y := fun e => hy ⟨b, e⟩
      simp [Q, h, hc _ hy]
  exact le_antisymm (calc
    M.rank = (P * M.submatrix r c * Q).rank := congrArg Matrix.rank eq
    _ ≤ (P * M.submatrix r c).rank := Matrix.rank_mul_le_left _ _
    _ ≤ _ := Matrix.rank_mul_le_right _ _) (Matrix.rank_submatrix_le M r c)
namespace SiteTensor
private def homogeneousTags {J : Type*} [Nonempty J] (A B : J → Type*) :
    ((∀ j, A j) ⊕ (∀ j, B j)) ↪ (∀ j, A j ⊕ B j) where
  toFun := Sum.elim (fun a j => Sum.inl (a j)) (fun b j => Sum.inr (b j))
  inj' := by
    rintro (x|x) (y|y) h
    · exact congrArg Sum.inl (funext fun j => Sum.inl.inj (congrFun h j))
    · cases congrFun h (Classical.arbitrary J)
    · cases congrFun h (Classical.arbitrary J)
    · exact congrArg Sum.inr (funext fun j => Sum.inr.inj (congrFun h j))
@[simp] private theorem homogeneousTags_inl {J : Type*} [Nonempty J] (A B : J → Type*)
    (a : ∀ j, A j) (j : J) : homogeneousTags A B (Sum.inl a) j = Sum.inl (a j) := rfl
@[simp] private theorem homogeneousTags_inr {J : Type*} [Nonempty J] (A B : J → Type*)
    (b : ∀ j, B j) (j : J) : homogeneousTags A B (Sum.inr b) j = Sum.inr (b j) := rfl
variable {I K : Type*} {A B : I → Type*}
variable (s : I → Prop) [DecidablePred s] [Fintype I] [Field K]
variable [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
open Crossing
theorem cutMatrix_rank_sumCoeff [Nonempty {i // s i}] [Nonempty {i // ¬ s i}]
    (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) :
    (cutMatrix s (sumCoeff T U)).rank = (cutMatrix s T).rank + (cutMatrix s U).rank := by
  classical
  let : Nonempty I := ⟨(Classical.arbitrary {i // s i}).val⟩
  let r := homogeneousTags (fun i : {i // s i} => A i) (fun i => B i)
  let c := homogeneousTags (fun i : {i // ¬ s i} => A i) (fun i => B i)
  let M := cutMatrix s (sumCoeff T U)
  have support (x y) (h : x ∉ Set.range r ∨ y ∉ Set.range c) : M x y = 0 := by
    apply sumCoeff_mixed
    · intro a he
      have e := (cutEquiv s (fun i => A i ⊕ B i)).apply_symm_apply (x,y)
      rw [← he] at e
      exact h.elim (fun hx => hx ⟨Sum.inl (fun i => a i), congrArg Prod.fst e⟩)
        (fun hy => hy ⟨Sum.inl (fun i => a i), congrArg Prod.snd e⟩)
    · intro b he
      have e := (cutEquiv s (fun i => A i ⊕ B i)).apply_symm_apply (x,y)
      rw [← he] at e
      exact h.elim (fun hx => hx ⟨Sum.inr (fun i => b i), congrArg Prod.fst e⟩)
        (fun hy => hy ⟨Sum.inr (fun i => b i), congrArg Prod.snd e⟩)
  have block : M.submatrix r c = Matrix.fromBlocks (cutMatrix s T) 0 0 (cutMatrix s U) := by
    ext x y
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        change sumCoeff T U _ = T _
        convert sumCoeff_inl T U ((cutEquiv s A).symm (x,y)) using 1
        congr 1
        funext i
        by_cases hi : s i <;> simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
          r, c, hi]
      | inr y =>
        apply sumCoeff_mixed
        · intro a he
          have h := congrFun he (Classical.arbitrary {i // ¬ s i}).val
          simp [r, c, cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
            (Classical.arbitrary {i // ¬ s i}).property] at h
        · intro b he
          have h := congrFun he (Classical.arbitrary {i // s i}).val
          simp [r, c, cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
            (Classical.arbitrary {i // s i}).property] at h
    | inr x =>
      cases y with
      | inl y =>
        apply sumCoeff_mixed
        · intro a he
          have h := congrFun he (Classical.arbitrary {i // s i}).val
          simp [r, c, cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
            (Classical.arbitrary {i // s i}).property] at h
        · intro b he
          have h := congrFun he (Classical.arbitrary {i // ¬ s i}).val
          simp [r, c, cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
            (Classical.arbitrary {i // ¬ s i}).property] at h
      | inr y =>
        change sumCoeff T U _ = U _
        convert sumCoeff_inr T U ((cutEquiv s B).symm (x,y)) using 1
        congr 1
        funext i
        by_cases hi : s i <;> simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
          r, c, hi]
  change M.rank = _
  rw [rank_eq_rank_on_support M r c (fun x hx y => support x y (Or.inl hx))
    (fun y hy x => support x y (Or.inr hy)), block, rank_fromBlocks_diagonal]
namespace Raw
universe v
theorem cutMatrix_rank_zero (F : Type*) [Field F] :
    (cutMatrix s (zero.{v} I F).coeff).rank = 0 :=
  Matrix.rank_zero
theorem cutMatrix_rank_one (F : Type*) [Field F] :
    (cutMatrix s (one.{v} I F).coeff).rank = 1 := by
  classical
  let r : ({i // s i} → PUnit.{v+1}) ≃ Unit := Equiv.ofUnique _ _
  let c : ({i // ¬s i} → PUnit.{v+1}) ≃ Unit := Equiv.ofUnique _ _
  have eq : cutMatrix s (one.{v} I F).coeff = (1 : Matrix Unit Unit F).submatrix r c := by
    ext x y
    change 1 = (1 : Matrix Unit Unit F) (r x) (c y)
    simp
  rw [eq]
  exact (Matrix.rank_submatrix (1 : Matrix Unit Unit F) r c).trans
    ((Matrix.rank_one (R := F)).trans Fintype.card_unit)
end Raw
end SiteTensor
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped Kronecker
theorem rank_kronecker {K m n p q : Type*} [Field K]
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    (A : Matrix m n K) (B : Matrix p q K) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  classical
  let bm := Pi.basisFun K m
  let bn := Pi.basisFun K n
  let bp := Pi.basisFun K p
  let bq := Pi.basisFun K q
  rw [(A ⊗ₖ B).rank_eq_finrank_range_toLin (bm.tensorProduct bp) (bn.tensorProduct bq),
    Matrix.toLin_kronecker, A.rank_eq_finrank_range_toLin bm bn,
    B.rank_eq_finrank_range_toLin bp bq, TensorProduct.range_map, ← TensorProduct.range_mapIncl,
    LinearMap.finrank_range_of_inj (Module.Flat.tensorProduct_mapIncl_injective_of_right _ _),
    Module.finrank_tensorProduct]
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped Classical Kronecker
noncomputable section
namespace SiteTensor
open Crossing
variable {I K : Type*} (s : I → Prop) [DecidablePred s] {A B : I → Type*}
theorem cutMatrix_product [Mul K] (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) :
    cutMatrix s (fun z : ∀ i, A i × B i ↦ T (fun i ↦ (z i).1) * U (fun i ↦ (z i).2)) =
      ((cutMatrix s T) ⊗ₖ (cutMatrix s U)).submatrix
        (Equiv.arrowProdEquivProdArrow {i // s i} (fun i ↦ A i.val) (fun i ↦ B i.val))
        (Equiv.arrowProdEquivProdArrow {i // ¬s i} (fun i ↦ A i.val) (fun i ↦ B i.val)) := by
  ext r c
  change T _ * U _ = T _ * U _
  apply congrArg₂ (· * ·)
  · apply congrArg T
    funext i
    by_cases h : s i <;> simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, h,
      Equiv.arrowProdEquivProdArrow]
  · apply congrArg U
    funext i
    by_cases h : s i <;> simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, h,
      Equiv.arrowProdEquivProdArrow]
theorem cutMatrix_rank_product [Field K] [Fintype I] [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) :
    (cutMatrix s (fun z : ∀ i, A i × B i ↦ T (fun i ↦ (z i).1) * U (fun i ↦ (z i).2))).rank =
      (cutMatrix s T).rank * (cutMatrix s U).rank := by
  rw [cutMatrix_product, Matrix.rank_submatrix, rank_kronecker]
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped NNReal Classical
noncomputable section
namespace SiteTensor
universe v u w
open Crossing
variable {I : Type u} (s : I → Prop) [DecidablePred s] [Fintype I] (K : Type w) [Field K]
def cutRank : TensorClass.{v} I K → ℕ :=
  Quotient.lift (fun X : Raw.{v} I K => (cutMatrix s X.coeff).rank) fun X Y h =>
    le_antisymm (cutMatrix_rank_le_of_restriction s X.coeff Y.coeff h.1)
      (cutMatrix_rank_le_of_restriction s Y.coeff X.coeff h.2)
@[simp] theorem cutRank_ofRaw (X : Raw.{v} I K) :
    cutRank s K (ofRaw X) = (cutMatrix s X.coeff).rank := rfl
theorem monotone_cutRank : Monotone (cutRank.{v} s K) := by
  intro x y
  refine Quotient.inductionOn₂ x y fun X Y h => ?_
  exact cutMatrix_rank_le_of_restriction s X.coeff Y.coeff h
variable [Nonempty I] [Nonempty {i // s i}] [Nonempty {i // ¬ s i}]
def cutSpectrum : normalizedSpectrum (fun x y : TensorClass.{v} I K => x ≤ y) := by
  refine ⟨fun x => (cutRank s K x : ℝ≥0), ?_, ?_, ?_, ?_, ?_⟩
  · change ((cutMatrix s (Raw.zero.{v} I K).coeff).rank : ℝ≥0) = 0
    rw [Raw.cutMatrix_rank_zero, Nat.cast_zero]
  · change ((cutMatrix s (Raw.one.{v} I K).coeff).rank : ℝ≥0) = 1
    rw [Raw.cutMatrix_rank_one, Nat.cast_one]
  · intro x y
    refine Quotient.inductionOn₂ x y fun X Y => ?_
    change ((cutMatrix s (sumCoeff X.coeff Y.coeff)).rank : ℝ≥0) =
      ((cutMatrix s X.coeff).rank : ℝ≥0) + (cutMatrix s Y.coeff).rank
    exact_mod_cast cutMatrix_rank_sumCoeff s X.coeff Y.coeff
  · intro x y
    refine Quotient.inductionOn₂ x y fun X Y => ?_
    change ((cutMatrix s (X.mul Y).coeff).rank : ℝ≥0) =
      ((cutMatrix s X.coeff).rank : ℝ≥0) * (cutMatrix s Y.coeff).rank
    exact_mod_cast cutMatrix_rank_product s X.coeff Y.coeff
  · exact fun x y h => Nat.cast_le.mpr ((monotone_cutRank s K) h)
@[simp] theorem cutSpectrum_ofRaw (X : Raw.{v} I K) :
    (cutSpectrum s K).val (ofRaw X) = ((cutMatrix s X.coeff).rank : ℝ≥0) := rfl
theorem spectrum_nonempty (I : Type u) [Fintype I] [Nontrivial I] (K : Type w) [Field K] :
    (normalizedSpectrum (fun x y : TensorClass.{v} I K => x ≤ y)).Nonempty := by
  classical
  obtain ⟨i, j, hij⟩ := exists_pair_ne I
  let s (x : I) := x = i
  let : Nonempty {x // s x} := ⟨⟨i, rfl⟩⟩
  let : Nonempty {x // ¬ s x} := ⟨⟨j, Ne.symm hij⟩⟩
  exact Set.nonempty_of_mem (cutSpectrum.{v} s K).property
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped NNReal
namespace SiteTensor
universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
theorem exists_le_natCast (X : TensorClass.{v} I K) : ∃ n : ℕ, X ≤ n := by
  classical
  induction X using Quotient.inductionOn with
  | _ T =>
    refine ⟨Fintype.card (∀ i, T.Leg i), ?_⟩
    change ofRaw T ≤ (Fintype.card (∀ i, T.Leg i) : TensorClass.{v} I K)
    simpa only [ofRaw_diagonal_eq_natCast, Fintype.card_ulift, Fintype.card_fin] using
        (ofRaw_le_iff.mpr (T.restricts_diagonal I))
theorem isCompact_spectrum :
    IsCompact (normalizedSpectrum (S := TensorClass.{v} I K) (· ≤ ·)) :=
  isCompact_normalizedSpectrum _ exists_le_natCast
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
open scoped BigOperators Classical
universe v
variable {I K : Type*} {α β : Type v} [Fintype I] [CommSemiring K]
namespace Raw
theorem diagonal_coeff_at (i₀ : I) [Fintype α] (x : I → α) :
    (diagonal I K α).coeff x = if ∀ i, x i = x i₀ then 1 else 0 := by
  classical
  simp only [diagonal]
  rw [Finset.sum_eq_single (x i₀)]
  · simp [funext_iff]
  · intro b _ hb
    apply ite_eq_right
    intro hx
    exact hb (congrFun hx i₀).symm
  · simp
end Raw
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators NNReal
private theorem exists_logb_summand {L : Type*} [Fintype L] {v : ℝ≥0} (f : L → ℝ≥0)
    (hv : 0 < v) (hs : v ≤ ∑ j, f j) {c : ℝ} (hc : 0 ≤ c) :
    ∃ j, 0 < f j ∧ c * Real.logb 2 v ≤ c * Real.logb 2 (f j) + c * Real.logb 2 (Fintype.card L) := by
  classical
  cases isEmpty_or_nonempty L with
  | inl h => simp at hs; exact False.elim (hv.ne' hs)
  | inr h =>
    obtain ⟨j, hj⟩ := Finite.exists_max f
    have hsum : v ≤ (Fintype.card L : ℝ≥0) * f j := calc
      _ ≤ ∑ l, f l := hs
      _ ≤ ∑ _l : L, f j := Finset.sum_le_sum fun l _ => hj l
      _ = _ := by simp
    have hp : 0 < (f j : ℝ) := by exact_mod_cast pos_of_mul_pos_right (hv.trans_le hsum) (by positivity)
    have hn : 0 < (Fintype.card L : ℝ) := by exact_mod_cast (Fintype.card_pos (α := L))
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast hv : 0 < (v : ℝ)) (show (v : ℝ) ≤ (Fintype.card L : ℝ) * f j by exact_mod_cast hsum)
    rw [Real.logb_mul hn.ne' hp.ne'] at hlog
    exact ⟨j, by exact_mod_cast hp, by linarith [mul_le_mul_of_nonneg_left hlog hc]⟩
namespace SiteTensor
theorem ordinary_add_restricts {I K : Type*} [Fintype I] [CommSemiring K]
    {A : I → Type*} [∀ i, Fintype (A i)] (T U : (∀ i, A i) → K) :
    Crossing.IsRestriction (T + U) (sumCoeff T U) := by
  classical
  let fold (i : I) (a : A i) (s : A i ⊕ A i) : K := if Sum.elim id id s = a then 1 else 0
  refine ⟨fold, fun x => ?_⟩
  simp only [sumCoeff, add_mul, Finset.sum_add_distrib, Pi.add_apply]
  rw [sum_pushCoeff_mul, sum_pushCoeff_mul]
  have elim (V : (∀ i, A i) → K) :
      (∑ a, V a * ∏ i, (if a i = x i then (1 : K) else 0)) = V x := by
    simp_rw [Fintype.prod_boole]
    simp [← funext_iff, mul_ite]
  exact congrArg₂ (· + ·) (elim T).symm (elim U).symm
universe v
noncomputable section
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
variable {A : I → Type v} [∀ i, Fintype (A i)]
def ofCoeffs (T : (∀ i, A i) → K) : TensorClass.{v} I K :=
  ofRaw ⟨A, inferInstance, T⟩
@[simp] theorem ofCoeffs_zero : ofCoeffs (0 : (∀ i, A i) → K) = 0 := by
  apply ofRaw_eq_iff.mpr
  constructor <;> exact ⟨fun _ _ _ => 0, fun _ => by simp [Raw.zero]⟩
theorem ordinary_sum_le {J : Type*} [Fintype J] (T : J → (∀ i, A i) → K) :
    ofCoeffs (∑ j, T j) ≤ ∑ j, ofCoeffs (T j) := by
  classical
  generalize (Finset.univ : Finset J) = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (ofRaw_le_iff.mpr (ordinary_add_restricts _ _)).trans (add_mono le_rfl ih)
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))
def coeffValue (T : (∀ i, A i) → K) : ℝ≥0 := φ.val (ofCoeffs T)
@[simp] theorem coeffValue_zero : coeffValue φ (0 : (∀ i, A i) → K) = 0 := by
  simp [coeffValue, φ.2.1]
theorem coeffValue_one_le {T : (∀ i, A i) → K} (h : T ≠ 0) : 1 ≤ coeffValue φ T := by
  have hle : (1 : TensorClass.{v} I K) ≤ ofCoeffs T :=
    ofRaw_le_iff.mpr (Crossing.unit_restricts_of_nonzero h)
  simpa [coeffValue, φ.2.2.1] using φ.2.2.2.2.2 _ _ hle
theorem ordinary_sum_value_le {J : Type*} [Fintype J] (T : J → (∀ i, A i) → K) :
    coeffValue φ (∑ j, T j) ≤ ∑ j, coeffValue φ (T j) := by
  have h := φ.2.2.2.2.2 _ _ (ordinary_sum_le T)
  change coeffValue φ (∑ j, T j) ≤ normalizedSpectrum.toRingHom φ (∑ j, ofCoeffs (T j)) at h
  rw [map_sum] at h
  exact h
theorem ordinary_sum_logb_le {J : Type*} [Fintype J] (T : J → (∀ i, A i) → K)
    (hT : ∑ j, T j ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    ∃ j, T j ≠ 0 ∧ c * Real.logb 2 (coeffValue φ (∑ k, T k)) ≤
      c * Real.logb 2 (coeffValue φ (T j)) + c * Real.logb 2 (Fintype.card J) := by
  obtain ⟨j, hj, h⟩ := exists_logb_summand _ (zero_lt_one.trans_le (coeffValue_one_le φ hT))
    (ordinary_sum_value_le φ T) hc
  exact ⟨j, fun h0 => by simp [h0] at hj, h⟩
end
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor.Raw
universe u v
variable {I J : Type u} {D K : Type*} [Fintype I] [Fintype J] [Fintype D] [CommSemiring K]
theorem group_group_equivalent (T : Raw.{max u v} I K) (p : I → J) (q : J → D) :
    ((T.group p).group q).Equivalent (T.group (q ∘ p)) := by
  apply reindex_equivalent (X := (T.group p).group q) (Y := T.group (q ∘ p)) (fun d => {
    toFun := fun f t => f ⟨p t.1, t.2⟩ ⟨t.1, rfl⟩
    invFun := fun f j i => f ⟨i.1, (congrArg q i.2).trans j.2⟩
    left_inv := by
      intro f
      funext ⟨j, hj⟩ ⟨i, hi⟩
      change p i = j at hi
      subst j
      rfl
    right_inv := fun _ => rfl })
  intro x
  rfl
end SiteTensor.Raw
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace ComparisonExpansion
open scoped BigOperators Classical
open Crossing
noncomputable section
variable {F I : Type*} [CommSemiring F] [Fintype I]
theorem nonzero_terms_of_sum {P M : Type*} [Fintype P] [AddCommMonoid M]
    {x : M} (hx : x ≠ 0) (z : P → M) (hsum : x = ∑ p, z p) :
    ∃ L : ℕ, 0 < L ∧ L ≤ Fintype.card P ∧ ∃ idx : Fin L → P,
      (∀ l, z (idx l) ≠ 0) ∧ x = ∑ l, z (idx l) := by
  let S := {p : P // z p ≠ 0}
  let e := Fintype.equivFin S
  have hex : ∃ p, z p ≠ 0 := by
    by_contra! hz
    exact hx (hsum.trans (by simp [hz]))
  obtain ⟨p, hp⟩ := hex
  refine ⟨Fintype.card S, Fintype.card_pos_iff.mpr ⟨⟨p, hp⟩⟩, Fintype.card_subtype_le _,
    fun l => (e.symm l).1, fun l => (e.symm l).2, ?_⟩
  calc
    x = ∑ p, z p := hsum
    _ = ∑ p ∈ Finset.univ.filter (fun p => z p ≠ 0), z p := (Finset.sum_filter_ne_zero _).symm
    _ = ∑ p : S, z p.1 := Finset.sum_subtype _ (by simp) _
    _ = _ := Fintype.sum_equiv e _ _ fun p => by simp
end
end ComparisonExpansion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace SiteTensor
open scoped BigOperators NNReal Classical
universe v u w
variable (I : Type u) (K : Type w) [Fintype I] [Nonempty I] [Field K]
def nonzeroClasses : Submonoid (TensorClass.{v} I K) where
  carrier := {t | t ≠ 0}
  one_mem' := one_ne_zero
  mul_mem' := mul_ne_zero
abbrev NonzeroProduct := Additive (nonzeroClasses.{v} I K)
variable {I K}
abbrev classOfProduct (x : NonzeroProduct.{v} I K) : TensorClass.{v} I K := x.toMul.val
theorem unit_le_nonzeroClass (x : nonzeroClasses.{v} I K) : 1 ≤ x.val :=
  one_le_of_ne_zero x.property
abbrev logPoint (f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop)) :
    NonzeroProduct.{v} I K →+ ℝ := spectralLogHom unit_le_nonzeroClass f
def ClassOrdinarySum (X : NonzeroProduct.{v} I K) (L : ℕ) (Z : Fin L → NonzeroProduct.{v} I K) :
    Prop :=
  ∃ (R : Raw.{v} I K) (z : Fin L → (∀ i, R.Leg i) → K),
    ofRaw R = classOfProduct X ∧ R.coeff = ∑ l, z l ∧
    ∀ l, ofRaw { R with coeff := z l } = classOfProduct (Z l)
def StrictSpectralComparison (I : Type u) (K : Type w) [Fintype I] [Nonempty I] [Field K] : Prop :=
  ∀ X Y : TensorClass.{v} I K, X ≠ 0 → Y ≠ 0 →
    (∀ f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop), f.val X < f.val Y) →
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → X ^ n ≤ C • (Y ^ n)
omit [Nonempty I] in
private theorem split_add (R : Raw.{v} I K) (Y V : TensorClass.{v} I K)
    (h : ofRaw R ≤ Y + V) :
    ∃ A B : (∀ i, R.Leg i) → K, R.coeff = A + B ∧
      ofRaw { R with coeff := A } ≤ Y ∧ ofRaw { R with coeff := B } ≤ V := by
  induction Y using Quotient.inductionOn with | h Y =>
  induction V using Quotient.inductionOn with | h V =>
  obtain ⟨M, hM⟩ := h
  let image {B : I → Type v} [∀ i, Fintype (B i)] (T : (∀ i, B i) → K)
      (N : ∀ i, R.Leg i → B i → K) (x : ∀ i, R.Leg i) := ∑ a, T a * ∏ i, N i (x i) (a i)
  let left := fun i x a => M i x (Sum.inl a)
  let right := fun i x a => M i x (Sum.inr a)
  refine ⟨image Y.coeff left, image V.coeff right, ?_, ⟨left, fun _ => rfl⟩, ⟨right, fun _ => rfl⟩⟩
  funext x
  have hh := hM x
  change R.coeff x = ∑ a, sumCoeff Y.coeff V.coeff a * ∏ i, M i (x i) (a i) at hh
  simpa [sumCoeff, add_mul, Finset.sum_add_distrib, sum_pushCoeff_mul, image, left, right] using hh
theorem images_of_le_sum {J : Type*} [Fintype J] (R : Raw.{v} I K)
    (Y : J → TensorClass.{v} I K) (h : ofRaw R ≤ ∑ j, Y j) :
    ∃ Z : J → (∀ i, R.Leg i) → K, R.coeff = ∑ j, Z j ∧
      ∀ j, ofRaw { R with coeff := Z j } ≤ Y j := by
  have aux (s : Finset J) (x : (∀ i, R.Leg i) → K)
      (hx : ofRaw { R with coeff := x } ≤ ∑ j ∈ s, Y j) :
      ∃ Z : J → (∀ i, R.Leg i) → K, x = ∑ j ∈ s, Z j ∧
        ∀ j ∈ s, ofRaw { R with coeff := Z j } ≤ Y j := by
    induction s using Finset.induction_on generalizing x with
    | empty =>
      have hx' : ofRaw { R with coeff := x } = 0 :=
        le_antisymm (by simpa using hx) (zero_le_tensor _)
      exact ⟨0, by simpa using (ofRaw_eq_zero_iff _).mp hx', by simp⟩
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj] at hx
      obtain ⟨a, b, heq, ha, hb⟩ := split_add {R with coeff := x} _ _ hx
      obtain ⟨Z, hZ, hle⟩ := ih b hb
      refine ⟨Function.update Z j a, ?_, ?_⟩
      · rw [Finset.sum_insert hj, Function.update_self]
        rw [show ∑ l ∈ s, Function.update Z j a l = ∑ l ∈ s, Z l from
          Finset.sum_congr rfl fun l hl => Function.update_of_ne (show l ≠ j from fun h => hj (h ▸ hl)) ..]
        exact heq.trans (congrArg (a + ·) hZ)
      · intro l hl
        rcases Finset.mem_insert.mp hl with rfl | hs
        · simpa using ha
        · simpa [Function.update_of_ne (show l ≠ j from fun e => hj (e ▸ hs))] using hle l hs
  obtain ⟨Z, hsum, hle⟩ := aux Finset.univ R.coeff h
  exact ⟨Z, hsum, fun j => hle j (Finset.mem_univ _)⟩
theorem expandedStrictComparison_of_strict (strict : StrictSpectralComparison.{v} I K) :
    ExpandedStrictComparison (Set.range (logPoint.{v} (I := I) (K := K)))
      (fun x y => classOfProduct x ≤ classOfProduct y) ClassOrdinarySum := by
  intro J X Y hJ hlog
  let y := fun i => classOfProduct (Y i)
  have summand_le (j : Fin J) : y j ≤ ∑ i, y i := by
    rw [← Finset.sum_erase_add Finset.univ y (Finset.mem_univ j)]
    simpa using add_mono (zero_le_tensor (∑ i ∈ Finset.univ.erase j, y i)) (le_refl (y j))
  have hnonzero : ∑ i, y i ≠ 0 := by
    let j : Fin J := ⟨0, hJ⟩
    intro hz
    exact (Y j).toMul.property (le_antisymm ((summand_le j).trans_eq hz) (zero_le_tensor _))
  have greater (f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop)) :
      f.val (classOfProduct X) < f.val (∑ i, y i) := by
    obtain ⟨i, hi⟩ := hlog (logPoint f) ⟨f, rfl⟩
    apply lt_of_lt_of_le _ (f.property.2.2.2.2 _ _ (summand_le i))
    by_contra! hh
    apply hi.not_ge
    apply Real.logb_le_logb_of_le (by norm_num)
    · exact_mod_cast zero_lt_one.trans_le (one_le_spectral_value f (unit_le_nonzeroClass (Y i).toMul))
    · exact_mod_cast hh
  obtain ⟨C, hC, hx⟩ := strict _ _ X.toMul.property hnonzero greater
  refine ⟨C, hC, fun n hn => ?_⟩
  let P := Fin C × (Fin n → Fin J)
  let W (p : P) := ∑ t, Y (p.2 t)
  have prod (w : Fin n → Fin J) : classOfProduct (∑ t, Y (w t)) = ∏ t, y (w t) := by
    simp [classOfProduct, toMul_sum, y]
  have distrib : C • (∑ j, y j)^n = ∑ p : P, classOfProduct (W p) := by
    change _ = ∑ p : Fin C × (Fin n → Fin J), classOfProduct (∑ t, Y (p.2 t))
    rw [Fintype.sum_prod_type]
    simp only [prod, ← Fintype.prod_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_const]
  obtain ⟨R, hR⟩ := Quotient.exists_rep (classOfProduct (n • X))
  change ofRaw R = classOfProduct (n • X) at hR
  have hr : ofRaw R ≤ ∑ p : P, classOfProduct (W p) := by
    rw [hR, ← distrib]
    simpa [classOfProduct, y] using hx n hn
  obtain ⟨z, hsum, hle⟩ := images_of_le_sum R _ hr
  have hnz : R.coeff ≠ 0 := fun heq => (n • X).toMul.property
    (hR.symm.trans ((ofRaw_eq_zero_iff _).mpr heq))
  obtain ⟨L, hL, hcount, idx, hnz', heq⟩ := ComparisonExpansion.nonzero_terms_of_sum hnz z hsum
  let images (l : Fin L) : NonzeroProduct.{v} I K :=
    Additive.ofMul ⟨ofRaw { R with coeff := z (idx l) },
      fun h => hnz' l ((ofRaw_eq_zero_iff _).mp h)⟩
  exact ⟨L, hL, hcount.trans_eq (by simp [P]), images,
    ⟨R, z ∘ idx, hR, heq, fun _ => rfl⟩, fun l => ⟨(idx l).2, hle _⟩⟩
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators NNReal Classical
noncomputable section
namespace SiteTensor
universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
namespace Raw
def contractNew (T : Raw.{v} (Option I) K) (ξ : T.Leg none → K) : Raw.{v} I K where
  Leg i := T.Leg (some i)
  finiteLeg _ := inferInstance
  coeff a := ∑ b, ξ b * T.coeff (Equiv.piOptionEquivProd.symm (b,a))
omit [Nonempty I] in
theorem contractNew_restricts {X Y : Raw.{v} (Option I) K} (h : X.Restricts Y)
    (ξ : X.Leg none → K) : ∃ η : Y.Leg none → K, (X.contractNew ξ).Restricts (Y.contractNew η) := by
  classical
  let : DecidableEq (Option I) := fun _ _ ↦ Classical.propDecidable _
  obtain ⟨M, hm⟩ := h
  let η (b : Y.Leg none) := ∑ c, ξ c * M none c b
  refine ⟨η, fun i ↦ M (some i), ?_⟩
  intro (x : ∀ i, X.Leg (some i))
  change (∑ c, ξ c * X.coeff (Equiv.piOptionEquivProd.symm (c,x))) =
    ∑ a, (∑ b, η b * Y.coeff (Equiv.piOptionEquivProd.symm (b,a))) * _
  have he (c : X.Leg none) (x : ∀ i, X.Leg (some i)) :
      X.coeff (Equiv.piOptionEquivProd.symm (c,x)) =
        ∑ b, ∑ a, Y.coeff (Equiv.piOptionEquivProd.symm (b,a)) *
          (M none c b * ∏ i, M (some i) (x i) (a i)) := by
    rw [hm, ← Fintype.sum_prod_type']
    apply Fintype.sum_equiv (Equiv.piOptionEquivProd (β := Y.Leg))
    intro y
    rw [Equiv.symm_apply_apply, Fintype.prod_option]
    rfl
  simp_rw [he]
  simp only [η, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    Finset.sum_congr rfl fun _ _ ↦ ?_
  dsimp [Equiv.piOptionEquivProd]
  ring
end Raw
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))
def contractionPrice (T : Raw.{v} (Option I) K) : ℝ :=
  ⨆ ξ : T.Leg none → K, rawLogPrice φ 1 (T.contractNew ξ)
private theorem contraction_bdd (T : Raw.{v} (Option I) K) :
    BddAbove (Set.range fun ξ : T.Leg none → K ↦ rawLogPrice φ 1 (T.contractNew ξ)) := by
  classical
  let d := Fintype.card (∀ i, T.Leg (some i))
  refine ⟨rawLogPrice φ 1 (Raw.diagonal I K (ULift.{v} (Fin d))), ?_⟩
  rintro _ ⟨ξ, rfl⟩
  exact rawLogPrice_mono φ zero_le_one ((T.contractNew ξ).restricts_diagonal I)
theorem le_contractionPrice (T : Raw.{v} (Option I) K) (ξ : T.Leg none → K) :
    rawLogPrice φ 1 (T.contractNew ξ) ≤ contractionPrice φ T := le_ciSup (contraction_bdd φ T) ξ
theorem contractionPrice_mono {X Y : Raw.{v} (Option I) K} (h : X.Restricts Y) :
    contractionPrice φ X ≤ contractionPrice φ Y := by
  apply ciSup_le
  intro ξ
  obtain ⟨η, hη⟩ := Raw.contractNew_restricts h ξ
  exact (rawLogPrice_mono φ zero_le_one hη).trans (le_contractionPrice φ Y η)
theorem contractionPrice_nonneg (T : Raw.{v} (Option I) K) : 0 ≤ contractionPrice φ T :=
  (rawLogPrice_nonneg φ zero_le_one _).trans (le_contractionPrice φ T 0)
omit [Fintype I] [Nonempty I] in
@[simp] theorem contractNew_coeff_sum {T : Raw.{v} (Option I) K} {L : ℕ}
    (ξ : T.Leg none → K) (Z : Fin L → (∀ i, T.Leg i) → K)
    (hs : T.coeff = ∑ l, Z l) :
    (T.contractNew ξ).coeff = ∑ l, (({T with coeff := Z l} : Raw _ K).contractNew ξ).coeff := by
  funext (a : ∀ i, T.Leg (some i))
  change (∑ b, ξ b * T.coeff (Equiv.piOptionEquivProd.symm (b,a))) = _
  simp only [hs, Finset.sum_apply, Finset.mul_sum, Raw.contractNew]
  rw [Finset.sum_comm]
  exact (Finset.sum_apply a Finset.univ (fun l : Fin L ↦ fun y : (∀ i, T.Leg (some i)) ↦ ∑ b, ξ b * Z l (Equiv.piOptionEquivProd.symm (b,y)))).symm
def classContractionPrice (X : TensorClass.{v} (Option I) K) : ℝ :=
  Quotient.liftOn X (contractionPrice φ) fun _ _ h ↦
    le_antisymm (contractionPrice_mono φ h.1) (contractionPrice_mono φ h.2)
theorem classContractionPrice_mono {X Y : TensorClass.{v} (Option I) K} (h : X ≤ Y) :
    classContractionPrice φ X ≤ classContractionPrice φ Y := by
  induction X, Y using Quotient.inductionOn₂ with | _ X Y =>
    exact contractionPrice_mono φ h
theorem classContractionPrice_ordinary_sum
    (X : NonzeroProduct.{v} (Option I) K) (L : ℕ) (Z : Fin L → NonzeroProduct.{v} (Option I) K)
    (h : ClassOrdinarySum X L Z) :
    ∃ l, classContractionPrice φ (classOfProduct X) ≤
      classContractionPrice φ (classOfProduct (Z l)) + Real.logb 2 L := by
  classical
  obtain ⟨T, z, hT, hsum, hz⟩ := h
  have hL : 0 < L := by
    by_contra! hL
    obtain rfl : L = 0 := Nat.eq_zero_of_le_zero hL
    exact X.toMul.property (hT.symm.trans ((ofRaw_eq_zero_iff T).mpr (by simpa using hsum)))
  have : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  obtain ⟨j, hj⟩ := Finite.exists_max (fun l ↦ classContractionPrice φ (classOfProduct (Z l)))
  refine ⟨j, ?_⟩
  rw [← hT]
  change contractionPrice φ T ≤ _
  apply ciSup_le
  intro ξ
  have hh := contractNew_coeff_sum ξ z hsum
  by_cases he : (T.contractNew ξ).coeff = 0
  · rw [rawLogPrice_zero φ 1 _ he, ← hz j]
    exact add_nonneg (contractionPrice_nonneg φ _) (Real.logb_nonneg (by norm_num)
      (by exact_mod_cast hL : (1 : ℝ) ≤ L))
  let zz (l : Fin L) := ({T with coeff := z l} : Raw _ K).contractNew ξ
  let C (l : Fin L) : (∀ i, T.Leg (some i)) → K := (zz l).coeff
  change (T.contractNew ξ).coeff = ∑ l, C l at hh
  obtain ⟨l, _, hp⟩ := ordinary_sum_logb_le φ C (hh ▸ he) zero_le_one
  have hprice : rawLogPrice φ 1 (T.contractNew ξ) ≤ rawLogPrice φ 1 (zz l) + Real.logb 2 L := by
    have heq := congrArg (coeffValue φ (A := fun i => T.Leg (some i))) hh
    simp only [← heq, Fintype.card_fin, one_mul] at hp
    simp only [rawLogPrice, coeffValue, ofCoeffs, C, zz, Raw.contractNew, one_mul] at hp ⊢
    convert hp using 6 <;> rfl
  refine hprice.trans (add_le_add_left (?_ : rawLogPrice φ 1 (zz l) ≤ _) _)
  exact (le_contractionPrice φ {T with coeff := z l} ξ).trans (by
    change classContractionPrice φ (ofRaw _) ≤ _
    rw [hz]
    exact hj l)
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
noncomputable section
namespace SiteTensor.Raw
variable {I : Type*} (K : Type*) [Field K]
def newStar (a b : I) (A B : Type) [Fintype A] [Fintype B] : Raw.{0} (Option I) K where
  Leg := Option.rec (A × B) (fun i ↦ (i = a → A) × (i = b → B))
  finiteLeg := Option.rec (inferInstanceAs (Fintype (A × B))) (fun i ↦
    Fintype.ofFinite ((i = a → A) × (i = b → B)))
  coeff x := (if (x none).1 = (x (some a)).1 rfl then 1 else 0) *
    (if (x none).2 = (x (some b)).2 rfl then 1 else 0)
theorem contractNew_newStar_coeff [Fintype I] (a b : I) (A B : Type) [Fintype A] [Fintype B]
    (ξ : A × B → K) (x : ∀ i, (i = a → A) × (i = b → B)) :
    ((newStar K a b A B).contractNew ξ).coeff x = ξ ((x a).1 rfl, (x b).2 rfl) := by
  change (∑ s : A × B, ξ s * ((if s.1 = (x a).1 rfl then 1 else 0) *
    (if s.2 = (x b).2 rfl then 1 else 0))) = _
  rw [Fintype.sum_prod_type]
  simp [mul_ite]
end SiteTensor.Raw
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical
namespace SiteTensor
variable {I : Type*} (K : Type*) [Field K]
private abbrev wireFiber (a : I) (s : Option I) :=
  {j : Fin 2 // ![none, some a] j = s}
private theorem wireFiber_ext (a : I) (s : Option I) (u v : wireFiber a s) : u = v := by
  apply Subtype.ext
  have h := u.property.trans v.property.symm
  rcases u with ⟨u, _⟩
  rcases v with ⟨v, _⟩
  fin_cases u <;> fin_cases v <;> simp_all
private theorem wireFiber_eq {a i : I} (j : wireFiber a (some i)) : i = a := by
  obtain ⟨j, h⟩ := j
  fin_cases j <;> simp_all
private def newLegEquiv (a : I) (A : Type) (s : Option I) :
    Option.rec A (fun i ↦ i = a → A) s ≃ (wireFiber a s → A) :=
  match s with
  | none =>
    { toFun := fun x _ ↦ x
      invFun := fun f ↦ f ⟨0, rfl⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun f ↦ funext fun j ↦ congrArg f (wireFiber_ext _ _ _ j) }
  | some i =>
    { toFun := fun f j ↦ f (wireFiber_eq j)
      invFun := fun g hi ↦ g ⟨1, by subst i; rfl⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun f ↦ funext fun j ↦ congrArg f (wireFiber_ext _ _ _ j) }
private theorem twoDiagonal_coeff (A : Type) [Fintype A] (x : Fin 2 → A) :
    (Raw.diagonal (Fin 2) K A).coeff x = if x 0 = x 1 then 1 else 0 := by
  rw [Raw.diagonal_coeff_at (1 : Fin 2)]
  simp [Fin.forall_fin_two]
theorem ofRaw_newStar [Fintype I] (a b : I) (A B : Type) [Fintype A] [Fintype B] :
    ofRaw (Raw.newStar K a b A B) =
      ofRaw ((Raw.diagonal (Fin 2) K A).group ![none, some a]) *
      ofRaw ((Raw.diagonal (Fin 2) K B).group ![none, some b]) := by
  let W (i : I) (D : Type) [Fintype D] := (Raw.diagonal (Fin 2) K D).group ![none, some i]
  let e (s : Option I) : (Raw.newStar K a b A B).Leg s ≃ ((W a A).mul (W b B)).Leg s :=
    match s with
    | none => (newLegEquiv a A none).prodCongr (newLegEquiv b B none)
    | some i => (newLegEquiv a A (some i)).prodCongr (newLegEquiv b B (some i))
  rw [← ofRaw_mul]
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  let u (j : Fin 2) : A := (e (![none, some a] j) (x _)).1 ⟨j, rfl⟩
  let v (j : Fin 2) : B := (e (![none, some b] j) (x _)).2 ⟨j, rfl⟩
  change _ = (Raw.diagonal (Fin 2) K A).coeff u * (Raw.diagonal (Fin 2) K B).coeff v
  rw [twoDiagonal_coeff K A u, twoDiagonal_coeff K B v]
  rfl
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical BigOperators
namespace SiteTensor.Raw
variable {I K : Type*}
def endpointMatrix (a b : I) (A B : Type) [Fintype A] [Fintype B] (M : A → B → K) :
    Raw.{0} I K :=
  ⟨fun i ↦ (i = a → A) × (i = b → B), fun _ ↦ Fintype.ofFinite _,
    fun x ↦ M ((x a).1 rfl) ((x b).2 rfl)⟩
variable [Fintype I] [Field K]
private theorem grouped_diagonal_coeff_basis (a b : I) (D : Type) [Fintype D] :
    ((diagonal (Fin 2) K D).group ![a,b]).coeff =
      Crossing.basisTensor (F := K)
        (fun (d : D) (i : I) (_ : {j : Fin 2 // ![a,b] j = i}) ↦ d) := by
  funext x
  apply Finset.sum_congr rfl
  intro d _
  let z (j : Fin 2) : D := x (![a,b] j) ⟨j, rfl⟩
  have he : (z = fun _ ↦ d) ↔ x = fun _ _ ↦ d := by
    constructor
    · intro h
      funext i ⟨j, hj⟩
      subst i
      exact congrFun h j
    · rintro rfl
      rfl
  by_cases h : z = fun _ ↦ d
  · exact (ite_eq_left h).trans (ite_eq_left (he.mp h)).symm
  · exact (ite_eq_right h).trans (ite_eq_right (h ∘ he.mpr)).symm
private theorem endpointMatrix_restricts_factor (a b : I) {A B D : Type}
    [Fintype A] [Fintype B] [Fintype D] (M : A → B → K) (L : A → D → K) (R : B → D → K)
    (hM : ∀ x y, M x y = ∑ d, L x d * R y d) :
    (endpointMatrix a b A B M).Restricts ((diagonal (Fin 2) K D).group ![a,b]) := by
  unfold Restricts
  rw [grouped_diagonal_coeff_basis]
  apply (Crossing.restriction_basisTensor_iff _ _).mpr
  refine ⟨fun i x y ↦
    (if h : i = a then L (x.1 h) (y ⟨0,h.symm⟩) else 1) *
    (if h : i = b then R (x.2 h) (y ⟨1,h.symm⟩) else 1), fun x ↦ ?_⟩
  change M ((x a).1 rfl) ((x b).2 rfl) = _
  rw [hM]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_eq_single a] <;> simp_all
  · rw [Finset.prod_eq_single b] <;> simp_all
theorem endpointMatrix_restricts_leftWire (a b : I) {A B : Type} [Fintype A] [Fintype B]
    (M : A → B → K) :
    (endpointMatrix a b A B M).Restricts ((diagonal (Fin 2) K A).group ![a,b]) := by
  apply endpointMatrix_restricts_factor a b M (fun x d ↦ if d = x then 1 else 0)
    (fun y d ↦ M d y)
  intro x y
  simp [ite_mul]
theorem endpointMatrix_restricts_rightWire (a b : I) {A B : Type} [Fintype A] [Fintype B]
    (M : A → B → K) :
    (endpointMatrix a b A B M).Restricts ((diagonal (Fin 2) K B).group ![a,b]) := by
  apply endpointMatrix_restricts_factor a b M (fun x d ↦ M x d)
    (fun y d ↦ if d = y then 1 else 0)
  intro x y
  simp [mul_ite]
private def endpointLegEquiv (a b i : I) (D : Type) :
    ({j : Fin 2 // ![a,b] j = i} → D) ≃ ((i = a → D) × (i = b → D)) where
  toFun x := (fun h ↦ x ⟨0,h.symm⟩, fun h ↦ x ⟨1,h.symm⟩)
  invFun x t := by
    obtain ⟨t,ht⟩ := t
    by_cases h : t = 0
    · exact x.1 ((h ▸ ht : ![a,b] (0 : Fin 2) = i).symm)
    · have h1 : t = 1 := by omega
      exact x.2 ((h1 ▸ ht : ![a,b] (1 : Fin 2) = i).symm)
  left_inv x := by
    funext ⟨t,ht⟩
    fin_cases t <;> rfl
  right_inv x := by rfl
theorem ofRaw_endpointMatrix_diagonal (a b : I) (A : Type) [Fintype A] :
    ofRaw (endpointMatrix a b A A (fun x y ↦ if x = y then (1 : K) else 0)) =
      ofRaw ((diagonal (Fin 2) K A).group ![a,b]) := by
  symm
  apply ofRaw_eq_iff.mpr (reindex_equivalent (fun i ↦ endpointLegEquiv a b i A) ?_)
  intro x
  let z (j : Fin 2) : A := x (![a,b] j) ⟨j,rfl⟩
  change (diagonal (Fin 2) K A).coeff z = if z 0 = z 1 then 1 else 0
  rw [diagonal_coeff_at (1 : Fin 2)]
  simp [Fin.forall_fin_two]
end SiteTensor.Raw
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
variable {A I : Type} [Fintype A] [Nonempty A] [Fintype I] [Nonempty I]
variable (K : Type*) [CommSemiring K] (σ : A → I)
theorem ofRaw_group_diagonal_fun_fin (D : Type) [Fintype D] (n : ℕ) :
    ofRaw ((Raw.diagonal A K (Fin n → D)).group σ) =
      ofRaw ((Raw.diagonal A K D).group σ) ^ n := by
  change groupMulHom σ (ofRaw (Raw.diagonal A K (Fin n → D))) =
    groupMulHom σ (ofRaw (Raw.diagonal A K D)) ^ n
  rw [ofRaw_diagonal_eq_natCast, ofRaw_diagonal_eq_natCast, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow, map_pow]
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical NNReal
noncomputable section
namespace SiteTensor
variable {I : Type} {K : Type*} [Fintype I] [Nonempty I] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))
omit [Nonempty I] in
private theorem contractNew_newStar_eq (a b : I) (A B : Type) [Fintype A] [Fintype B]
    (ξ : A × B → K) :
    (Raw.newStar K a b A B).contractNew ξ =
      Raw.endpointMatrix a b A B (fun s t ↦ ξ (s,t)) := by
  exact congrArg (Raw.mk _ _) (funext (Raw.contractNew_newStar_coeff K a b A B ξ))
theorem contractionPrice_newStar_le (a b : I) (A B : Type) [Fintype A] [Fintype B] :
    contractionPrice φ (Raw.newStar K a b A B) ≤
      min (rawLogPrice φ 1 ((Raw.diagonal (Fin 2) K A).group ![a,b]))
          (rawLogPrice φ 1 ((Raw.diagonal (Fin 2) K B).group ![a,b])) := by
  apply ciSup_le
  intro ξ
  rw [contractNew_newStar_eq a b A B ξ]
  exact le_min (rawLogPrice_mono φ zero_le_one (Raw.endpointMatrix_restricts_leftWire a b _))
    (rawLogPrice_mono φ zero_le_one (Raw.endpointMatrix_restricts_rightWire a b _))
theorem contractionPrice_newStar_self (a b : I) (A : Type) [Fintype A] :
    contractionPrice φ (Raw.newStar K a b A A) =
      rawLogPrice φ 1 ((Raw.diagonal (Fin 2) K A).group ![a,b]) := by
  apply le_antisymm ((contractionPrice_newStar_le φ a b A A).trans (min_le_left _ _))
  let ξ (s : A × A) : K := if s.1 = s.2 then 1 else 0
  have h := le_contractionPrice φ (Raw.newStar K a b A A) ξ
  rw [contractNew_newStar_eq, rawLogPrice, Raw.ofRaw_endpointMatrix_diagonal] at h
  exact h
private theorem logPrice_wire_power (a b : I) (n : ℕ) :
    rawLogPrice φ 1 ((Raw.diagonal (Fin 2) K (Fin n → Fin 2)).group ![a,b]) =
      n * rawWireDistance φ 1 a b := by
  rw [rawLogPrice, ofRaw_group_diagonal_fun_fin]
  change 1 * Real.logb 2 (normalizedSpectrum.toRingHom φ (_ ^ n) : ℝ≥0) = _
  rw [map_pow, NNReal.coe_pow, Real.logb_pow, one_mul]
  simp [rawWireDistance, rawLogPrice, normalizedSpectrum.toRingHom]
private theorem ofRaw_newStar_words (a b : I) (m n : ℕ) :
    ofRaw (Raw.newStar K a b (Fin m → Fin 2) (Fin n → Fin 2)) =
      ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none,some a]) ^ m *
      ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none,some b]) ^ n := by
  rw [ofRaw_newStar, ofRaw_group_diagonal_fun_fin, ofRaw_group_diagonal_fun_fin]
theorem classContractionPrice_wire_powers_le (a b : I) (m n : ℕ) :
    classContractionPrice φ
      (ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none,some a]) ^ m *
       ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none,some b]) ^ n) ≤
      min (m : ℝ) n * rawWireDistance φ 1 a b := by
  rw [← ofRaw_newStar_words]
  have h := contractionPrice_newStar_le φ a b (Fin m → Fin 2) (Fin n → Fin 2)
  have hdist : 0 ≤ rawWireDistance φ 1 a b := rawLogPrice_nonneg φ zero_le_one _
  rw [logPrice_wire_power, logPrice_wire_power, ← min_mul_of_nonneg _ _ hdist] at h
  exact h
theorem classContractionPrice_wire_powers_self (a b : I) (m : ℕ) :
    classContractionPrice φ
      (ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none,some a]) ^ m *
       ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none,some b]) ^ m) =
      (m : ℝ) * rawWireDistance φ 1 a b := by
  rw [← ofRaw_newStar_words]
  exact (contractionPrice_newStar_self φ a b (Fin m → Fin 2)).trans
    (logPrice_wire_power φ a b m)
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped BigOperators Classical
namespace SiteTensor
universe v u w
variable {I : Type u} {K : Type w}
namespace Raw
def embedOld (X : Raw.{v} I K) : Raw.{v} (Option I) K where
  Leg := fun j => j.elim PUnit X.Leg
  finiteLeg := fun j => by cases j <;> dsimp <;> infer_instance
  coeff := fun x => X.coeff fun i => x (some i)
def embedOldCoords (X : Raw.{v} I K) :
    (∀ j, X.embedOld.Leg j) ≃ (∀ i, X.Leg i) where
  toFun x i := x (some i)
  invFun x j := match j with
    | none => PUnit.unit
    | some i => x i
  left_inv x := by funext j; cases j <;> rfl
  right_inv x := rfl
@[simp] theorem embedOld_coeff_ne_zero_iff [Zero K] (X : Raw.{v} I K) :
    X.embedOld.coeff ≠ 0 ↔ X.coeff ≠ 0 := by
  constructor
  · intro h he
    exact h (funext fun x => congrFun he (X.embedOldCoords x))
  · intro h he
    exact h (funext fun x => congrFun he (X.embedOldCoords.symm x))
variable [Fintype I] [CommSemiring K]
theorem embedOld_restricts {X Y : Raw.{v} I K} (h : X.Restricts Y) :
    X.embedOld.Restricts Y.embedOld := by
  let : DecidableEq (Option I) := fun _ _ ↦ Classical.propDecidable _
  obtain ⟨M, hM⟩ := h
  let N : ∀ j, X.embedOld.Leg j → Y.embedOld.Leg j → K
    | none => fun _ _ => 1
    | some i => M i
  refine ⟨N, fun x => ?_⟩
  change X.coeff (fun i => x (some i)) = _
  refine (hM (X.embedOldCoords x)).trans ?_
  apply Fintype.sum_equiv Y.embedOldCoords.symm
  intro y
  rw [Fintype.prod_option]
  simp [embedOld, embedOldCoords, N]
  rfl
private theorem embedOld_one_equivalent :
    (one I K).embedOld.Equivalent (one (Option I) K : Raw.{v} _ _) := by
  refine reindex_equivalent (fun j => ?_) (fun _ => rfl)
  cases j <;> exact Equiv.refl _
private theorem embedOld_mul_equivalent (X Y : Raw.{v} I K) :
    (X.mul Y).embedOld.Equivalent (X.embedOld.mul Y.embedOld) := by
  let e : ∀ j, (X.mul Y).embedOld.Leg j ≃ (X.embedOld.mul Y.embedOld).Leg j
    | none => (Equiv.punitProd PUnit).symm
    | some i => Equiv.refl _
  exact reindex_equivalent e fun _ => rfl
end Raw
variable [Fintype I] [CommSemiring K]
def embedOldClass : TensorClass.{v} I K → TensorClass.{v} (Option I) K :=
  Quotient.map Raw.embedOld fun _ _ h => ⟨Raw.embedOld_restricts h.1, Raw.embedOld_restricts h.2⟩
@[simp] theorem embedOldClass_ofRaw (X : Raw.{v} I K) :
    embedOldClass (ofRaw X) = ofRaw X.embedOld := rfl
@[simp] theorem embedOldClass_one [Nonempty I] :
    embedOldClass (1 : TensorClass.{v} I K) = 1 :=
  ofRaw_eq_iff.mpr Raw.embedOld_one_equivalent
@[simp] theorem embedOldClass_mul [Nonempty I] (X Y : TensorClass.{v} I K) :
    embedOldClass (X * Y) = embedOldClass X * embedOldClass Y :=
  Quotient.inductionOn₂ X Y fun x y => ofRaw_eq_iff.mpr (Raw.embedOld_mul_equivalent x y)
section Field
variable {I : Type u} {K : Type w} [Fintype I] [Nonempty I] [Field K]
omit [Nonempty I] in
theorem embedOldClass_ne_zero_iff (X : TensorClass.{v} I K) :
    embedOldClass X ≠ 0 ↔ X ≠ 0 := by
  induction X using Quotient.inductionOn with | _ X =>
    change ofRaw X.embedOld ≠ 0 ↔ ofRaw X ≠ 0
    simp only [ne_eq, ofRaw_eq_zero_iff]
    exact X.embedOld_coeff_ne_zero_iff
def embedOldProduct : NonzeroProduct.{v} I K →+ NonzeroProduct.{v} (Option I) K where
  toFun x := Additive.ofMul ⟨embedOldClass (classOfProduct x),
    (embedOldClass_ne_zero_iff _).2 x.toMul.property⟩
  map_zero' := Subtype.ext embedOldClass_one
  map_add' _ _ := Subtype.ext (embedOldClass_mul _ _)
@[simp] theorem classOfProduct_embedOldProduct (x : NonzeroProduct.{v} I K) :
    classOfProduct (embedOldProduct x) = embedOldClass (classOfProduct x) := rfl
end Field
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
universe v
variable {A I : Type} {K : Type*} [Fintype A] [Fintype I] [CommSemiring K]
private def groupSomeLegEquiv (T : Raw.{v} I K) (j : Option I) :
    (T.group some).Leg j ≃ T.embedOld.Leg j := by
  cases j with
  | none =>
    exact ⟨fun _ => PUnit.unit, fun _ t => (nomatch t.property),
      fun _ => funext fun t => (nomatch t.property), fun _ => rfl⟩
  | some i =>
    exact ⟨fun x => x ⟨i, rfl⟩,
      fun x t => (Option.some.inj t.property).symm ▸ x,
      fun x => by
        funext ⟨k, hk⟩
        cases Option.some.inj hk
        rfl,
      fun _ => rfl⟩
theorem ofRaw_embedOld_eq_group_some (T : Raw.{v} I K) :
    ofRaw T.embedOld = ofRaw (T.group some) := by
  symm
  exact ofRaw_eq_iff.mpr (Raw.reindex_equivalent (groupSomeLegEquiv T) (fun _ => rfl))
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped Classical NNReal
noncomputable section
namespace SiteTensor
variable {I : Type} {K : Type*} [Fintype I] [Nonempty I] [Field K]
def intervalWire (K : Type*) [Field K] (a : I) : NonzeroProduct.{0} (Option I) K := by
  let W := Raw.diagonal (Fin 2) K (Fin 2)
  have hn : W.coeff ≠ 0 := by
    intro he
    have h : W.coeff (fun _ => (0 : Fin 2)) = (0 : K) := congrFun he (fun _ => (0 : Fin 2))
    simp [W, Raw.diagonal, funext_iff] at h
  let X := W.group ![none, some a]
  exact Additive.ofMul ⟨ofRaw X, fun h ↦ (W.group_ne_zero_iff _).mpr hn ((ofRaw_eq_zero_iff X).mp h)⟩
@[simp] theorem classOfProduct_intervalWire (a : I) :
    classOfProduct (intervalWire K a) =
      ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none, some a]) := rfl
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))
theorem contractionPrice_intervalWires_le (a b : I) (m n : ℕ) :
    classContractionPrice φ (classOfProduct (m • intervalWire K a + n • intervalWire K b)) ≤
      min (m : ℝ) n * rawWireDistance φ 1 a b :=
  classContractionPrice_wire_powers_le φ a b m n
theorem contractionPrice_intervalWires_equal (a b : I) (m : ℕ) :
    classContractionPrice φ (classOfProduct (m • intervalWire K a + m • intervalWire K b)) =
      m * rawWireDistance φ 1 a b :=
  classContractionPrice_wire_powers_self φ a b m
theorem group_some_logPrice_of_old_logPoint
    (ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Option I) K → _ → Prop))
    (hold : ∀ X, logPoint ψ (embedOldProduct X) = logPoint φ X) (T : Raw.{0} I K) :
    rawLogPrice ψ 1 (T.group some) = rawLogPrice φ 1 T := by
  by_cases h : T.coeff = 0
  · have hh : (T.group some).coeff = 0 := not_not.mp (fun hn => ((T.group_ne_zero_iff some).mp hn) h)
    rw [rawLogPrice_zero _ _ _ h, rawLogPrice_zero _ _ _ hh]
  let X : NonzeroProduct.{0} I K := Additive.ofMul ⟨ofRaw T, fun he => h ((ofRaw_eq_zero_iff _).mp he)⟩
  have he := hold X
  change Real.logb 2 (ψ.val (ofRaw T.embedOld) : ℝ) = Real.logb 2 (φ.val (ofRaw T) : ℝ) at he
  simpa only [rawLogPrice, one_mul, ofRaw_embedOld_eq_group_some] using he
theorem logPoint_intervalWire_eq
    (ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Option I) K → _ → Prop)) (a : I) :
    logPoint ψ (intervalWire K a) = rawWireDistance ψ 1 none (some a) := by
  simp only [rawWireDistance, rawLogPrice, one_mul]
  rfl
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators
namespace SiteTensor.Raw
universe v
variable {I K : Type*} [Fintype I] [Field K]
theorem exists_contractNew_ne_zero (T : Raw.{v} (Option I) K) (h : T.coeff ≠ 0) :
    ∃ ξ : T.Leg none → K, (T.contractNew ξ).coeff ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, T.coeff a ≠ 0 := by
    by_contra! hz
    exact h (funext hz)
  let e := Equiv.piOptionEquivProd (β := T.Leg)
  refine ⟨fun b ↦ if (e a).1 = b then 1 else 0, fun hz ↦ ha ?_⟩
  have hs := congrFun hz (e a).2
  change (∑ b, (if (e a).1 = b then 1 else 0) * T.coeff (e.symm (b, (e a).2))) = 0 at hs
  simpa [ite_mul] using hs
end SiteTensor.Raw
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
namespace SiteTensor
universe v
variable {I : Type*}
private abbrev extendIndex {L : Option I → Type v} (b : L none) (a : ∀ i, L (some i)) :
    ∀ j, L j := Equiv.piOptionEquivProd.symm (b, a)
private theorem extendIndex_inl {A B : Option I → Type v} (b : A none) (a : ∀ i, A (some i)) :
    extendIndex (L := fun j => A j ⊕ B j) (Sum.inl b) (fun i => Sum.inl (a i)) =
      (fun j => Sum.inl (extendIndex b a j)) := by
  funext j
  cases j <;> rfl
private theorem extendIndex_inr {A B : Option I → Type v} (b : B none) (a : ∀ i, B (some i)) :
    extendIndex (L := fun j => A j ⊕ B j) (Sum.inr b) (fun i => Sum.inr (a i)) =
      (fun j => Sum.inr (extendIndex b a j)) := by
  funext j
  cases j <;> rfl
variable {K : Type*} [Fintype I] [Nonempty I] [Field K]
theorem ofRaw_contractNew_add (X Y : Raw.{v} (Option I) K) (ξ : X.Leg none ⊕ Y.Leg none → K) :
    ofRaw ((X.add Y).contractNew ξ) =
      ofRaw (X.contractNew (ξ ∘ Sum.inl)) + ofRaw (Y.contractNew (ξ ∘ Sum.inr)) := by
  classical
  rw [← ofRaw_add, ofRaw_eq_iff]
  apply Raw.reindex_equivalent (X := (X.add Y).contractNew ξ)
    (Y := (X.contractNew (ξ ∘ Sum.inl)).add (Y.contractNew (ξ ∘ Sum.inr)))
    (fun _ => Equiv.refl _)
  intro (a : ∀ i, X.Leg (some i) ⊕ Y.Leg (some i))
  change (∑ z : X.Leg none ⊕ Y.Leg none, ξ z * sumCoeff X.coeff Y.coeff
    (extendIndex (L := fun j => X.Leg j ⊕ Y.Leg j) z a)) =
      sumCoeff (fun x => ∑ b, ξ (Sum.inl b) * X.coeff (extendIndex b x))
        (fun y => ∑ b, ξ (Sum.inr b) * Y.coeff (extendIndex b y)) a
  rw [Fintype.sum_sum_type]
  by_cases hl : ∃ x : ∀ i, X.Leg (some i), (fun i => Sum.inl (x i)) = a
  · obtain ⟨x, rfl⟩ := hl
    rw [sumCoeff_inl]
    simp_rw [extendIndex_inl, sumCoeff_inl]
    have hm (b : Y.Leg none) : sumCoeff X.coeff Y.coeff
        (extendIndex (L := fun j => X.Leg j ⊕ Y.Leg j) (Sum.inr b) (fun i => Sum.inl (x i))) = 0 := by
      apply sumCoeff_mixed
      · intro z hz
        cases congrFun hz none
      · intro z hz
        cases congrFun hz (some (Classical.arbitrary I))
    simp [hm]
  by_cases hr : ∃ y : ∀ i, Y.Leg (some i), (fun i => Sum.inr (y i)) = a
  · obtain ⟨y, rfl⟩ := hr
    rw [sumCoeff_inr]
    simp_rw [extendIndex_inr, sumCoeff_inr]
    have hm (b : X.Leg none) : sumCoeff X.coeff Y.coeff
        (extendIndex (L := fun j => X.Leg j ⊕ Y.Leg j) (Sum.inl b) (fun i => Sum.inr (y i))) = 0 := by
      apply sumCoeff_mixed
      · intro z hz
        cases congrFun hz (some (Classical.arbitrary I))
      · intro z hz
        cases congrFun hz none
    simp [hm]
  have hm (b : X.Leg none ⊕ Y.Leg none) : sumCoeff X.coeff Y.coeff
      (extendIndex (L := fun j => X.Leg j ⊕ Y.Leg j) b a) = 0 := by
    apply sumCoeff_mixed
    · intro z hz
      exact hl ⟨fun i => z (some i), funext fun i => congrFun hz (some i)⟩
    · intro z hz
      exact hr ⟨fun i => z (some i), funext fun i => congrFun hz (some i)⟩
  rw [sumCoeff_mixed _ _ a (not_exists.mp hl) (not_exists.mp hr)]
  simp [hm]
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators NNReal Classical
noncomputable section
namespace SiteTensor
universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))
private def contractedValue (T : Raw.{v} (Option I) K) (ξ : T.Leg none → K) : ℝ :=
  φ.val (ofRaw (T.contractNew ξ))
private def rawContractionValue (T : Raw.{v} (Option I) K) : ℝ :=
  ⨆ ξ, contractedValue φ T ξ
private theorem rawContractionValue_bdd (T : Raw.{v} (Option I) K) :
    BddAbove (Set.range (contractedValue φ T)) := by
  let d := Fintype.card (∀ i, T.Leg (some i))
  refine ⟨(φ.val (ofRaw (Raw.diagonal I K (ULift.{v} (Fin d)))) : ℝ), ?_⟩
  rintro _ ⟨ξ, rfl⟩
  exact_mod_cast φ.property.2.2.2.2 _ _ (ofRaw_le_iff.mpr ((T.contractNew ξ).restricts_diagonal I))
private theorem le_rawContractionValue (T : Raw.{v} (Option I) K) (ξ : T.Leg none → K) :
    contractedValue φ T ξ ≤ rawContractionValue φ T :=
  le_ciSup (rawContractionValue_bdd φ T) ξ
private theorem rawContractionValue_mono {X Y : Raw.{v} (Option I) K} (h : X.Restricts Y) :
    rawContractionValue φ X ≤ rawContractionValue φ Y := by
  apply ciSup_le
  intro ξ
  obtain ⟨η, hη⟩ := Raw.contractNew_restricts h ξ
  apply le_trans _ (le_rawContractionValue φ Y η)
  exact_mod_cast φ.property.2.2.2.2 _ _ (ofRaw_le_iff.mpr hη)
def classContractionValue (X : TensorClass.{v} (Option I) K) : ℝ :=
  Quotient.liftOn X (rawContractionValue φ) fun _ _ h ↦
    le_antisymm (rawContractionValue_mono φ h.1) (rawContractionValue_mono φ h.2)
theorem classContractionPrice_eq_logb {X : TensorClass.{v} (Option I) K}
    (h : 1 ≤ classContractionValue φ X) :
    classContractionPrice φ X = Real.logb 2 (classContractionValue φ X) := by
  induction X using Quotient.inductionOn with | _ T =>
    change 1 ≤ rawContractionValue φ T at h
    change contractionPrice φ T = Real.logb 2 (rawContractionValue φ T)
    apply le_antisymm
    · apply ciSup_le
      intro ξ
      change 1 * Real.logb 2 (contractedValue φ T ξ) ≤ _
      rw [one_mul]
      by_cases hz : contractedValue φ T ξ = 0
      · simpa [hz] using Real.logb_nonneg (b := 2) (by norm_num) h
      · have hp : 0 ≤ contractedValue φ T ξ := NNReal.coe_nonneg _
        exact Real.logb_le_logb_of_le (by norm_num) (lt_of_le_of_ne hp (Ne.symm hz))
          (le_rawContractionValue φ T ξ)
    · apply (Real.logb_le_iff_le_rpow (by norm_num) (zero_lt_one.trans_le h)).mpr
      apply ciSup_le
      intro ξ
      by_cases hz : contractedValue φ T ξ = 0
      · rw [hz]
        positivity
      · have hp : 0 ≤ contractedValue φ T ξ := NNReal.coe_nonneg _
        apply (Real.logb_le_iff_le_rpow (by norm_num) (lt_of_le_of_ne hp (Ne.symm hz))).mp
        simpa only [rawLogPrice, one_mul, contractedValue] using le_contractionPrice φ T ξ
theorem one_le_classContractionValue {X : TensorClass.{v} (Option I) K} (hX : X ≠ 0) :
    1 ≤ classContractionValue φ X := by
  induction X using Quotient.inductionOn with | _ T =>
    obtain ⟨ξ, hξ⟩ := T.exists_contractNew_ne_zero (fun h ↦ hX ((ofRaw_eq_zero_iff T).mpr h))
    apply le_trans _ (le_rawContractionValue φ T ξ)
    exact_mod_cast one_le_raw_spectralValue φ (T.contractNew ξ) hξ
theorem classContractionValue_add (X Y : TensorClass.{v} (Option I) K) :
    classContractionValue φ (X + Y) = classContractionValue φ X + classContractionValue φ Y := by
  induction X, Y using Quotient.inductionOn₂ with | _ X Y =>
    change rawContractionValue φ (X.add Y) = rawContractionValue φ X + rawContractionValue φ Y
    have hv (ζ : X.Leg none ⊕ Y.Leg none → K) :
        contractedValue φ (X.add Y) ζ =
          contractedValue φ X (ζ ∘ Sum.inl) + contractedValue φ Y (ζ ∘ Sum.inr) := by
      simp only [contractedValue, ofRaw_contractNew_add, φ.property.2.2.1, NNReal.coe_add]
    apply le_antisymm
    · apply ciSup_le
      intro ζ
      apply (hv ζ).le.trans
      exact add_le_add (le_rawContractionValue φ X _) (le_rawContractionValue φ Y _)
    · apply le_sub_iff_add_le.mp
      apply ciSup_le
      intro ξ
      apply le_sub_iff_add_le.mpr
      apply le_sub_iff_add_le'.mp
      apply ciSup_le
      intro η
      apply le_sub_iff_add_le'.mpr
      exact (hv (Sum.elim ξ η)).symm.le.trans (le_rawContractionValue φ (X.add Y) _)
theorem classContractionValue_natCast_mul (k : ℕ) (X : TensorClass.{v} (Option I) K) :
    classContractionValue φ (k * X) = k * classContractionValue φ X := by
  induction k with
  | zero =>
    have h := classContractionValue_add φ (0 : TensorClass.{v} (Option I) K) 0
    simp only [add_zero] at h
    simpa using (show classContractionValue φ (0 : TensorClass.{v} (Option I) K) = 0 by linarith)
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, classContractionValue_add, ih,
      Nat.cast_succ, add_mul, one_mul]
theorem classContractionPrice_natCast_mul {k : ℕ} (hk : 0 < k)
    {X : TensorClass.{v} (Option I) K} (hX : X ≠ 0) :
    classContractionPrice φ (k * X) = Real.logb 2 k + classContractionPrice φ X := by
  have hk' : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hval := one_le_classContractionValue φ hX
  have hmul : 1 ≤ classContractionValue φ (k * X) := by
    rw [classContractionValue_natCast_mul]
    exact one_le_mul_of_one_le_of_one_le hk' hval
  rw [classContractionPrice_eq_logb φ hmul, classContractionPrice_eq_logb φ hval,
    classContractionValue_natCast_mul, Real.logb_mul (by positivity) (zero_lt_one.trans_le hval).ne']
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators NNReal Classical
noncomputable section
namespace SiteTensor
universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
namespace Raw
omit [Nonempty I] in
theorem contractNew_embedOld_mul (X : Raw.{v} I K) (T : Raw.{v} (Option I) K)
    (ξ : (X.embedOld.mul T).Leg none → K) :
    ofRaw ((X.embedOld.mul T).contractNew ξ) =
      ofRaw (X.mul (T.contractNew (fun b ↦ ξ (PUnit.unit, b)))) := by
  apply ofRaw_eq_iff.mpr
  apply reindex_equivalent (fun i ↦ Equiv.refl (X.Leg i × T.Leg (some i)))
  intro a
  change (∑ c : PUnit × T.Leg none, ξ c *
      (X.coeff (fun i ↦ (a i).1) * T.coeff (fun j ↦
        ((Equiv.piOptionEquivProd (β := (X.embedOld.mul T).Leg)).symm (c, a) j).2))) = _
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  change (∑ b, ξ (PUnit.unit, b) *
      (X.coeff (fun i ↦ (a i).1) * T.coeff (fun j ↦
        ((Equiv.piOptionEquivProd (β := (X.embedOld.mul T).Leg)).symm ((PUnit.unit, b), a) j).2))) =
    X.coeff (fun i ↦ (a i).1) * ∑ b, ξ (PUnit.unit, b) *
      T.coeff (Equiv.piOptionEquivProd.symm (b, fun i ↦ (a i).2))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  have eq : (fun j ↦
      ((Equiv.piOptionEquivProd (β := (X.embedOld.mul T).Leg)).symm ((PUnit.unit, b), a) j).2) =
      Equiv.piOptionEquivProd.symm (b, fun i ↦ (a i).2) := by
    funext j
    cases j <;> rfl
  rw [eq]
  ring
end Raw
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))
theorem contractionPrice_embedOld_mul (X : Raw.{v} I K) (T : Raw.{v} (Option I) K)
    (hX : X.coeff ≠ 0) (hT : T.coeff ≠ 0) :
    contractionPrice φ (X.embedOld.mul T) = rawLogPrice φ 1 X + contractionPrice φ T := by
  have hcontract (ξ : (X.embedOld.mul T).Leg none → K) :
      rawLogPrice φ 1 ((X.embedOld.mul T).contractNew ξ) =
        rawLogPrice φ 1 (X.mul (T.contractNew (fun b ↦ ξ (PUnit.unit, b)))) := by
    simp only [rawLogPrice, Raw.contractNew_embedOld_mul]
  have hlower (η : T.Leg none → K) (hn : (T.contractNew η).coeff ≠ 0) :
      rawLogPrice φ 1 X + rawLogPrice φ 1 (T.contractNew η) ≤
        contractionPrice φ (X.embedOld.mul T) := by
    have h := le_contractionPrice φ (X.embedOld.mul T) (fun c ↦ η c.2)
    rw [hcontract, rawLogPrice_mul φ 1 _ _ hX hn] at h
    exact h
  apply le_antisymm
  · apply ciSup_le
    intro ξ
    rw [hcontract]
    let U := T.contractNew (fun b ↦ ξ (PUnit.unit, b))
    change rawLogPrice φ 1 (X.mul U) ≤ _
    by_cases hu : U.coeff = 0
    · have hz : (X.mul U).coeff = 0 := by ext; simp [Raw.mul, hu]
      rw [rawLogPrice_zero φ 1 _ hz]
      exact add_nonneg (rawLogPrice_nonneg φ zero_le_one X) (contractionPrice_nonneg φ T)
    · rw [rawLogPrice_mul φ 1 _ _ hX hu]
      exact add_le_add_right (le_contractionPrice φ T _) _
  · suffices h : contractionPrice φ T ≤
        contractionPrice φ (X.embedOld.mul T) - rawLogPrice φ 1 X by linarith
    apply ciSup_le
    intro η
    by_cases hn : (T.contractNew η).coeff = 0
    · obtain ⟨ζ, hz⟩ := T.exists_contractNew_ne_zero hT
      have hp := hlower ζ hz
      have hzpos := rawLogPrice_nonneg φ zero_le_one (T.contractNew ζ)
      rw [rawLogPrice_zero φ 1 _ hn]
      linarith
    · have hp := hlower η hn
      linarith
theorem classContractionPrice_embedOldProduct_add (x : NonzeroProduct.{v} I K)
    (t : NonzeroProduct.{v} (Option I) K) :
    classContractionPrice φ (classOfProduct (embedOldProduct x + t)) =
      logPoint φ x + classContractionPrice φ (classOfProduct t) := by
  obtain ⟨X, hX⟩ := Quotient.exists_rep (classOfProduct x)
  obtain ⟨T, hT⟩ := Quotient.exists_rep (classOfProduct t)
  change ofRaw X = classOfProduct x at hX
  change ofRaw T = classOfProduct t at hT
  have h := contractionPrice_embedOld_mul φ X T
    (fun h ↦ x.toMul.property (hX.symm.trans ((ofRaw_eq_zero_iff _).2 h)))
    (fun h ↦ t.toMul.property (hT.symm.trans ((ofRaw_eq_zero_iff _).2 h)))
  change classContractionPrice φ (embedOldClass (classOfProduct x) * classOfProduct t) =
    Real.logb 2 (φ.val (classOfProduct x) : ℝ) + _
  rw [← hX, ← hT, embedOldClass_ofRaw, ← ofRaw_mul]
  change contractionPrice φ (X.embedOld.mul T) = _ + contractionPrice φ T
  simpa only [rawLogPrice, one_mul] using h
@[simp] theorem classContractionPrice_one : classContractionPrice φ 1 = 0 := by
  let U := Raw.one.{v} (Option I) K
  change contractionPrice φ U = 0
  apply le_antisymm _ (contractionPrice_nonneg φ _)
  apply ciSup_le
  intro ξ
  let i₀ : I := Classical.choice inferInstance
  have h : (U.contractNew ξ).Restricts (Raw.one I K) := by
    refine ⟨fun i _ _ ↦ if i = i₀ then ξ PUnit.unit else 1, fun _ ↦ ?_⟩
    change (∑ b : PUnit, ξ b * (1 : K)) =
      ∑ _ : I → PUnit, (1 : K) * ∏ i, (if i = i₀ then ξ PUnit.unit else (1 : K))
    simp only [Fintype.sum_unique, mul_one, one_mul, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    exact Fintype.sum_unique (f := fun b : PUnit ↦ ξ b)
  simpa [rawLogPrice, φ.property.2.1] using rawLogPrice_mono φ zero_le_one h
@[simp] theorem classContractionPrice_embedOldProduct (x : NonzeroProduct.{v} I K) :
    classContractionPrice φ (classOfProduct (embedOldProduct x)) = logPoint φ x := by
  simpa [show classOfProduct (0 : NonzeroProduct.{v} (Option I) K) = 1 from rfl] using
    classContractionPrice_embedOldProduct_add φ x 0
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
variable {S : Type*} [CommSemiring S] [Preorder S] [IsOrderedAddMonoid S] [IsOrderedMonoid S]
omit [IsOrderedMonoid S] in
private theorem reuse_additive_catalyst {a b w : S} (h : a + w ≤ b + w) (n : ℕ) :
    (n : S) * a + w ≤ n * b + w := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      ((n + 1 : ℕ) : S) * a + w = a + (n * a + w) := by push_cast; ring
      _ ≤ a + (n * b + w) := add_le_add_right ih _
      _ = n * b + (a + w) := by ring
      _ ≤ n * b + (b + w) := add_le_add_right h _
      _ = ((n + 1 : ℕ) : S) * b + w := by push_cast; ring
theorem powerComparison_of_additiveGain
    (hzero : ∀ z : S, 0 ≤ z) (hbound : ∀ z : S, ∃ n : ℕ, z ≤ (n : S))
    {x y : S} (hy : 1 ≤ y) (gain : ∃ s w : S, 1 + s * x + w ≤ s * y + w) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → x ^ n ≤ C • y ^ n := by
  obtain ⟨s, w, hgain⟩ := gain
  obtain ⟨j, hj⟩ := hbound w
  let J : S := (j : S) + 1
  have hJ : 1 ≤ J := by
    simpa only [J, zero_add] using add_le_add_left (hzero (j : S)) 1
  have hw : w ≤ J * y := calc
    w ≤ (j : S) := hj
    _ ≤ J := by simpa only [J, add_zero] using add_le_add_right (hzero 1) (j : S)
    _ = J * 1 := (mul_one _).symm
    _ ≤ J * y := mul_le_mul_right hy J
  obtain ⟨r, hr⟩ := hbound (J * x)
  let t : S := r * s + J
  have ht : 1 ≤ t := hJ.trans (by
    simpa only [t, zero_add] using add_le_add_left (hzero ((r : S) * s)) J)
  have hxy : t * x ≤ t * y := calc
    t * x = r * s * x + J * x := by dsimp [t]; ring
    _ ≤ r * s * x + r := add_le_add_right hr _
    _ = r * (1 + s * x) + 0 := by ring
    _ ≤ r * (1 + s * x) + w := add_le_add_right (hzero w) _
    _ ≤ r * (s * y) + w := reuse_additive_catalyst hgain r
    _ ≤ r * (s * y) + J * y := add_le_add_right hw _
    _ = t * y := by dsimp [t]; ring
  have hpow (n : ℕ) : t * x ^ n ≤ t * y ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        t * x ^ (n + 1) = (t * x ^ n) * x := by rw [pow_succ, mul_assoc]
        _ ≤ (t * y ^ n) * x := mul_le_mul_left ih x
        _ = (t * x) * y ^ n := by ring
        _ ≤ (t * y) * y ^ n := mul_le_mul_left hxy _
        _ = t * y ^ (n + 1) := by ring
  obtain ⟨c, hc⟩ := hbound t
  refine ⟨c + 1, Nat.succ_pos _, fun n _ => ?_⟩
  calc
    x ^ n = 1 * x ^ n := (one_mul _).symm
    _ ≤ t * x ^ n := mul_le_mul_left ht _
    _ ≤ t * y ^ n := hpow n
    _ ≤ (c : S) * y ^ n := mul_le_mul_left hc _
    _ ≤ (c + 1) • y ^ n := by
      simpa only [succ_nsmul, nsmul_eq_mul, add_zero] using
        add_le_add_right (hzero (y ^ n)) ((c : S) * y ^ n)
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
variable {S : Type*} [CommSemiring S] [Preorder S]
def TradeLE (x y a b : S) : Prop := ∃ s w : S, a + s * x + w ≤ b + s * y + w
theorem TradeLE.of_le {x y a b : S} (h : a ≤ b) : TradeLE x y a b :=
  ⟨0, 0, by simpa using h⟩
theorem TradeLE.reversed (x y : S) : TradeLE x y y x :=
  ⟨1, 0, by simp [add_comm]⟩
variable [IsOrderedAddMonoid S]
theorem TradeLE.trans {x y a b c : S} (h : TradeLE x y a b) (g : TradeLE x y b c) :
    TradeLE x y a c := by
  obtain ⟨s, w, hs⟩ := h
  obtain ⟨t, v, ht⟩ := g
  refine ⟨s + t, w + v, ?_⟩
  calc
    _ = (a + s*x + w) + (t*x + v) := by ring
    _ ≤ (b + s*y + w) + (t*x + v) := add_le_add_left hs _
    _ = (s*y + w) + (b + t*x + v) := by ring
    _ ≤ (s*y + w) + (c + t*y + v) := add_le_add_right ht _
    _ = _ := by ring
theorem TradeLE.add {x y a b c d : S} (h : TradeLE x y a b) (g : TradeLE x y c d) :
    TradeLE x y (a + c) (b + d) := by
  obtain ⟨s, w, hs⟩ := h
  obtain ⟨t, v, ht⟩ := g
  refine ⟨s + t, w + v, ?_⟩
  calc
    _ = (a + s*x + w) + (c + t*x + v) := by ring
    _ ≤ (b + s*y + w) + (d + t*y + v) := add_le_add hs ht
    _ = _ := by ring
variable [IsOrderedMonoid S]
omit [IsOrderedAddMonoid S] in
theorem TradeLE.mul_left {x y a b : S} (z : S) (h : TradeLE x y a b) :
    TradeLE x y (z*a) (z*b) := by
  obtain ⟨s, w, hs⟩ := h
  refine ⟨z*s, z*w, ?_⟩
  calc
    _ = z * (a + s*x + w) := by ring
    _ ≤ z * (b + s*y + w) := mul_le_mul_right hs z
    _ = _ := by ring
def tradePreorder (x y : S) : Preorder S where
  le := TradeLE x y
  lt a b := TradeLE x y a b ∧ ¬ TradeLE x y b a
  le_refl a := TradeLE.of_le (le_refl a)
  le_trans _ _ _ := TradeLE.trans
theorem powerComparison_of_tradeCompression (hzero : ∀ a : S, 0 ≤ a)
    (hbound : ∀ a : S, ∃ n : ℕ, a ≤ (n : S)) {x y : S} (hy : 1 ≤ y)
    {D : S} {m : ℕ} (hm : 0 < m) (h : TradeLE x y (D + m) D) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → x ^ n ≤ C • y ^ n := by
  obtain ⟨s, w, hs⟩ := h
  have hm' : (1 : S) ≤ (m : S) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    simpa using add_le_add_left (hzero (n : S)) (1 : S)
  apply powerComparison_of_additiveGain hzero hbound hy
  refine ⟨s, D + w, ?_⟩
  calc
    _ ≤ (m : S) + s*x + (D+w) := add_le_add_left (add_le_add_left hm' _) _
    _ = D + m + s*x + w := by ring
    _ ≤ D + s*y + w := hs
    _ = _ := by ring
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
open MatrixMultiplication.AuxiliarySeparation
theorem spectralPoint_of_no_compression {S : Type*} [CommSemiring S] [Preorder S]
    (R : S → ℕ) (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c d : S, a ≤ b → c ≤ d → a + c ≤ b + d)
    (hmul : ∀ z a b : S, a ≤ b → z * a ≤ z * b)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hno : ∀ (D : S) (m : ℕ), 0 < m → ¬ D + (m : S) ≤ D) :
    (normalizedSpectrum ((· ≤ ·) : S → S → Prop)).Nonempty := by
  have hstates := normalizedStates_nonempty_of_no_catalyst R 0 0 hzero hbound hadd
    (fun D s m hm => by simpa only [Nat.cast_zero, zero_mul, add_zero] using hno D m hm)
  have hdom (z x : S) : z * x ≤ (R x : S) * z :=
    (hmul z _ _ (hbound x)).trans_eq (mul_comm _ _)
  obtain ⟨f, hf, hfbound, _⟩ :=
    exists_monotone_semiringHom_of_normalizedStates R 0 0 hunit hmul hdom (by simpa only [Nat.cast_zero] using hstates)
  refine ⟨fun x => ⟨f x, (hfbound x).1⟩, ?_⟩
  exact ⟨Subtype.ext (map_zero f), Subtype.ext (map_one f),
    fun x y => Subtype.ext (map_add f x y), fun x y => Subtype.ext (map_mul f x y),
    fun _ _ h => hf h⟩
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
universe v
variable {I K : Type*} [Fintype I] [Nonempty I]
instance [CommSemiring K] : IsOrderedAddMonoid (TensorClass.{v} I K) where
  add_le_add_left _ _ h _ := add_mono h le_rfl
instance [CommSemiring K] : IsOrderedMonoid (TensorClass.{v} I K) where
  mul_le_mul_left _ _ h _ := mul_mono h le_rfl
variable [Field K]
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
open scoped NNReal
theorem powerComparison_of_spectral_lt {S : Type*} [CommSemiring S] [Preorder S]
    [IsOrderedAddMonoid S] [IsOrderedMonoid S] (hzero : ∀ z : S, 0 ≤ z)
    (hbound : ∀ z : S, ∃ n : ℕ, z ≤ (n : S)) (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    {x y : S} (hy : y ≠ 0)
    (hgap : ∀ f : normalizedSpectrum ((· ≤ ·) : S → S → Prop), f.val x < f.val y) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → x ^ n ≤ C • y ^ n := by
  classical
  by_contra hnone
  let R (a : S) : ℕ := (hbound a).choose
  have hno (D : S) (m : ℕ) (hm : 0 < m) : ¬ TradeLE x y (D + m) D :=
    fun h => hnone (powerComparison_of_tradeCompression hzero hbound (hunit y hy) hm h)
  obtain ⟨f, hf⟩ := @spectralPoint_of_no_compression S _ (tradePreorder x y) R
    (fun a => TradeLE.of_le (hzero a)) (fun a => TradeLE.of_le (hbound a).choose_spec)
    (fun _ _ _ _ h g => TradeLE.add h g) (fun z _ _ h => TradeLE.mul_left z h)
    (fun z hz => TradeLE.of_le (hunit z hz)) hno
  have point : f ∈ normalizedSpectrum ((· ≤ ·) : S → S → Prop) :=
    ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, fun a b h => hf.2.2.2.2 a b (TradeLE.of_le h)⟩
  exact (hgap ⟨f, point⟩).not_ge (hf.2.2.2.2 y x (TradeLE.reversed x y))
namespace SiteTensor
universe v
variable (I K : Type*) [Fintype I] [Nonempty I] [Field K]
theorem strictSpectralComparison : StrictSpectralComparison.{v} I K :=
  fun _ _ _ hy hgap => powerComparison_of_spectral_lt zero_le_tensor exists_le_natCast
    (fun _ => one_le_of_ne_zero) hy hgap
theorem expandedStrictComparison :
    ExpandedStrictComparison (Set.range (logPoint.{v} (I := I) (K := K)))
      (fun x y => classOfProduct x ≤ classOfProduct y) ClassOrdinarySum :=
  expandedStrictComparison_of_strict (strictSpectralComparison I K)
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
open scoped BigOperators NNReal
noncomputable section
section
variable {M T : Type*} [AddCommMonoid M] [AddCommMonoid T]
private theorem comparison_on_generators
    {E : Type*} (F : E → T →+ ℝ) (eval : M →+ T)
    {res : T → T → Prop} {ordinary : T → (L : ℕ) → (Fin L → T) → Prop}
    (h : ExpandedStrictComparison (Set.range F) res ordinary) :
    ExpandedStrictComparison (Set.range fun f ↦ (F f).comp eval) Eq
      (fun x L y ↦ ∃ z : Fin L → T, ordinary (eval x) L z ∧ ∀ l, res (z l) (eval (y l))) := by
  intro J x y hj cover
  obtain ⟨k, hk, hi⟩ := h (eval x) (eval ∘ y) hj (by
    rintro _ ⟨f,rfl⟩
    exact cover _ ⟨f, rfl⟩)
  refine ⟨k, hk, fun n hn ↦ ?_⟩
  obtain ⟨L, hL, hcount, z, hsum, words⟩ := hi n hn
  choose w hw using words
  refine ⟨L, hL, hcount, fun l ↦ ∑ t, y (w l t), ?_, fun l ↦ ⟨w l, rfl⟩⟩
  exact ⟨z, by simpa using hsum, fun l ↦ by simpa using hw l⟩
namespace SiteTensor
universe v
variable {I K : Type*} [Fintype I] [Nontrivial I] [Field K]
theorem spectral_extension_of_contraction_bounds
    (eval : M →+ NonzeroProduct.{v} I K) (target : M →+ ℝ) (G : AddSubmonoid M)
    (cost : NonzeroProduct.{v} I K → ℝ)
    (hmono : ∀ {x y}, classOfProduct x ≤ classOfProduct y → cost x ≤ cost y)
    (upper : ∀ x, cost (eval x) ≤ target x)
    (sharp : ∀ x ∈ G, target x ≤ cost (eval x))
    (nneg : ∀ x, 0 ≤ target x)
    (cost_sum : ∀ (x L z), ClassOrdinarySum x L z →
      ∃ l, cost x ≤ cost (z l) + Real.logb 2 L)
    (u : M) (hu : u ∈ G) (h1 : target u = 1)
    (hu1 : ∀ f, logPoint.{v} (I := I) (K := K) f (eval u) = 1) :
    ∃ f, (∀ x, logPoint.{v} (I := I) (K := K) f (eval x) ≤ target x) ∧
      ∀ x ∈ G, logPoint f (eval x) = target x := by
  classical
  let E := normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop)
  let : CompactSpace E := isCompact_iff_compactSpace.mp isCompact_spectrum
  let : Nonempty E := (spectrum_nonempty.{v} I K).to_subtype
  let F (f : E) : M →+ ℝ := (logPoint f).comp eval
  have cont (x : M) : Continuous (fun f ↦ F f x) :=
    continuous_spectralLogHom unit_le_nonzeroClass (eval x)
  have pos (f : E) (x : M) : 0 ≤ F f x := spectralLogHom_nonneg unit_le_nonzeroClass f _
  let ord (x : M) (L : ℕ) (y : Fin L → M) := ∃ z : Fin L → NonzeroProduct.{v} I K,
    ClassOrdinarySum (eval x) L z ∧ ∀ l, classOfProduct (z l) ≤ classOfProduct (eval (y l))
  have compare : ExpandedStrictComparison (Set.range F) Eq ord := @comparison_on_generators M (NonzeroProduct.{v} I K) _ _ E
    (logPoint (I := I) (K := K)) eval (fun x y ↦ classOfProduct x ≤ classOfProduct y)
    ClassOrdinarySum (expandedStrictComparison I K)
  obtain ⟨f, c, _, hle, heq⟩ := select_spectral_price_of_finite_comparison F target G 0 u
    cont pos nneg hu (h1 ▸ zero_lt_one) (fun f ↦ ⟨u, (hu1 f).symm ▸ zero_lt_one⟩) (by
      intro x hx J y cover
      obtain ⟨j, _⟩ := cover (Classical.choice inferInstance)
      refine finite_comparison_of_ordinary_sum (spectrum := Set.range F) (restricts := Eq)
        (ordinarySum := ord) (fun {j} ↦ @compare j) target (fun he ↦ (congrArg target he).le)
        (C := 1) zero_le_one ?_ (Fin.pos j) y ?_
      · intro n L Y _ hord
        obtain ⟨z, hsum, hz⟩ := hord
        obtain ⟨l, hl⟩ := cost_sum _ _ _ hsum
        have htarget := sharp (n • (0 + x)) (G.nsmul_mem (show 0 + x ∈ G by simpa) n)
        have hh := (hmono (hz l)).trans (upper _)
        exact ⟨l, by simpa only [one_mul] using htarget.trans (hl.trans (add_le_add_left hh _))⟩
      · rintro _ ⟨q, rfl⟩
        exact cover q)
  have hc : c = 1 := by
    have h := heq u hu
    change c * logPoint f (eval u) = target u at h
    simpa [hu1, h1] using h
  exact ⟨f, fun x ↦ by simpa [hc, F] using hle x, fun x hx ↦ by simpa [hc, F] using heq x hx⟩
end SiteTensor
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
noncomputable section
namespace SiteTensor
variable {O T : Type*} [AddCommMonoid O] [AddCommMonoid T]
abbrev IntervalMonomial (O : Type*) := O × ℕ × ℕ × ℕ
def intervalEval (embed : O →+ T) (A B D : T) : IntervalMonomial O →+ T where
  toFun x := embed x.1 + x.2.1 • A + x.2.2.1 • B + x.2.2.2 • D
  map_zero' := by simp
  map_add' := by
    rintro ⟨x, m, n, k⟩ ⟨y, p, q, r⟩
    simp [add_nsmul]
    abel
def intervalTarget (old : O →+ ℝ) (la lb : ℝ) : IntervalMonomial O →+ ℝ where
  toFun x := old x.1 + (x.2.1 : ℝ) * la + (x.2.2.1 : ℝ) * lb + (x.2.2.2 : ℝ)
  map_zero' := by simp
  map_add' := by
    rintro ⟨x, m, n, k⟩ ⟨y, p, q, r⟩
    simp [add_mul]
    ring
def intervalBalanced (O : Type*) [AddCommMonoid O] : AddSubmonoid (IntervalMonomial O) where
  carrier := {x | x.2.1 = x.2.2.1}
  zero_mem' := rfl
  add_mem' := by
    rintro x y (hx : x.2.1 = x.2.2.1) (hy : y.2.1 = y.2.2.1)
    exact congrArg₂ (· + ·) hx hy
theorem interval_prices_of_balanced (embed : O →+ T) (A B D : T)
    (old : O →+ ℝ) (la lb : ℝ) (price : T →+ ℝ)
    (upper : ∀ x, price (intervalEval embed A B D x) ≤ intervalTarget old la lb x)
    (exactOn : ∀ x ∈ intervalBalanced O,
      price (intervalEval embed A B D x) = intervalTarget old la lb x) :
    (∀ X, price (embed X) = old X) ∧ price A = la ∧ price B = lb := by
  refine ⟨fun X ↦ ?_, ?_⟩
  · simpa [intervalEval, intervalTarget] using exactOn (X, 0, 0, 0) rfl
  have ha : price A ≤ la := by
    simpa [intervalEval, intervalTarget] using upper (0, 1, 0, 0)
  have hb : price B ≤ lb := by
    simpa [intervalEval, intervalTarget] using upper (0, 0, 1, 0)
  have hab : price A + price B = la + lb := by
    simpa [intervalEval, intervalTarget] using exactOn (0, 1, 1, 0) rfl
  constructor <;> linarith
universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
theorem spectral_interval_of_contraction_formula
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))
    (embed : NonzeroProduct.{v} I K →+ NonzeroProduct.{v} (Option I) K)
    (A B D : NonzeroProduct.{v} (Option I) K) (hD : classOfProduct D = 2)
    (la lb : ℝ) (ha : 0 ≤ la) (hb : 0 ≤ lb)
    (upper : ∀ X (m n k : ℕ),
      classContractionPrice φ (classOfProduct (intervalEval embed A B D (X, m, n, k))) ≤
        logPoint φ X + (min m n : ℕ) * (la + lb) + (k : ℝ))
    (sharp : ∀ X (m k : ℕ),
      logPoint φ X + (m : ℝ) * (la + lb) + (k : ℝ) ≤
        classContractionPrice φ (classOfProduct (intervalEval embed A B D (X, m, m, k)))) :
    ∃ f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} (Option I) K → _ → Prop),
      (∀ X, logPoint f (embed X) = logPoint φ X) ∧ logPoint f A = la ∧ logPoint f B = lb := by
  let eval := intervalEval embed A B D
  let target := intervalTarget (logPoint φ) la lb
  let G := intervalBalanced (NonzeroProduct.{v} I K)
  let u : IntervalMonomial (NonzeroProduct.{v} I K) := (0, 0, 0, 1)
  have upper' (x) : classContractionPrice φ (classOfProduct (eval x)) ≤ target x := by
    obtain ⟨X, m, n, k⟩ := x
    refine (upper X m n k).trans ?_
    have hm : ((min m n : ℕ) : ℝ) ≤ m := by exact_mod_cast min_le_left m n
    have hn : ((min m n : ℕ) : ℝ) ≤ n := by exact_mod_cast min_le_right m n
    change _ ≤ logPoint φ X + (m : ℝ) * la + (n : ℝ) * lb + (k : ℝ)
    rw [mul_add]
    linarith [mul_le_mul_of_nonneg_right hm ha, mul_le_mul_of_nonneg_right hn hb]
  have sharp' (x) (hx : x ∈ G) : target x ≤ classContractionPrice φ (classOfProduct (eval x)) := by
    obtain ⟨X, m, n, k⟩ := x
    change m = n at hx
    subst n
    simpa [target, intervalTarget, eval, mul_add, add_assoc] using sharp X m k
  have nneg (x) : 0 ≤ target x := by
    change 0 ≤ logPoint φ x.1 + _ * la + _ * lb + _
    have := spectralLogHom_nonneg unit_le_nonzeroClass φ x.1
    positivity
  have normalized (f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} (Option I) K → _ → Prop)) :
      logPoint f (eval u) = 1 := by
    have h : eval u = D := by simp [eval, u, intervalEval]
    rw [h]
    change Real.logb 2 (f.val (classOfProduct D) : ℝ) = 1
    rw [hD, show f.val 2 = 2 from map_ofNat (normalizedSpectrum.toRingHom f) 2]
    exact Real.logb_self_eq_one (by norm_num)
  obtain ⟨f, hf, hG⟩ := spectral_extension_of_contraction_bounds eval target G
    (fun x ↦ classContractionPrice φ (classOfProduct x))
    (fun h ↦ classContractionPrice_mono φ h) upper' sharp' nneg
    (classContractionPrice_ordinary_sum φ) u rfl (by simp [target, intervalTarget, u]) normalized
  exact ⟨f, interval_prices_of_balanced embed A B D (logPoint φ) la lb (logPoint f) hf hG⟩
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
noncomputable section
namespace SiteTensor
universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
private theorem fullBinary_nonzero : (2 : TensorClass.{v} (Option I) K) ≠ 0 := by
  obtain ⟨v, hv⟩ := spectrum_nonempty.{v} (Option I) K
  let f := normalizedSpectrum.toRingHom ⟨v, hv⟩
  intro h
  have hf := congrArg f h
  rw [map_ofNat, map_zero] at hf
  norm_num at hf
def intervalFullBinary : NonzeroProduct.{v} (Option I) K :=
  Additive.ofMul ⟨2, fullBinary_nonzero⟩
private theorem interval_contraction_split
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))
    (A B : NonzeroProduct.{v} (Option I) K) (X : NonzeroProduct.{v} I K) (m n k : ℕ) :
    classContractionPrice φ (classOfProduct
      (intervalEval embedOldProduct A B intervalFullBinary (X, m, n, k))) =
      logPoint φ X + classContractionPrice φ (classOfProduct (m • A + n • B)) + (k : ℝ) := by
  let P := embedOldProduct X + (m • A + n • B)
  have he : intervalEval embedOldProduct A B intervalFullBinary (X, m, n, k) =
      k • intervalFullBinary + P := by
    change (embedOldProduct X + m • A + n • B) + k • intervalFullBinary = _
    rw [add_comm _ (k • intervalFullBinary), add_assoc (embedOldProduct X)]
  have hd : classOfProduct (k • intervalFullBinary + P) =
      (((2 ^ k : ℕ) : TensorClass.{v} (Option I) K)) * classOfProduct P := by
    change (2 : TensorClass.{v} (Option I) K)^k * _ = _
    rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [he, hd, classContractionPrice_natCast_mul φ (pow_pos (by decide : 0 < 2) _) P.toMul.property]
  rw [show classContractionPrice φ (classOfProduct P) = _ from
    classContractionPrice_embedOldProduct_add φ X (m • A + n • B)]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  exact add_comm _ _
theorem spectral_interval_of_wire_bounds
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))
    (A B : NonzeroProduct.{v} (Option I) K) (la lb : ℝ) (ha : 0 ≤ la) (hb : 0 ≤ lb)
    (upper : ∀ m n : ℕ, classContractionPrice φ (classOfProduct (m • A + n • B)) ≤
      min (m : ℝ) n * (la + lb))
    (sharp : ∀ m : ℕ, (m : ℝ) * (la + lb) ≤
      classContractionPrice φ (classOfProduct (m • A + m • B))) :
    ∃ f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} (Option I) K → _ → Prop),
      (∀ X, logPoint f (embedOldProduct X) = logPoint φ X) ∧ logPoint f A = la ∧ logPoint f B = lb := by
  apply spectral_interval_of_contraction_formula φ embedOldProduct A B intervalFullBinary rfl la lb ha hb
  · intro X m n k
    rw [interval_contraction_split, Nat.cast_min]
    linarith [upper m n]
  · intro X m k
    rw [interval_contraction_split]
    linarith [sharp m]
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
open scoped NNReal
noncomputable section
namespace SiteTensor
variable {I : Type} {K : Type*} [Fintype I] [Nonempty I] [Field K]
theorem exists_spectral_interval_point
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))
    (a b : I) (la lb : ℝ) (ha : 0 ≤ la) (hb : 0 ≤ lb)
    (hs : la + lb = rawWireDistance φ 1 a b) :
    ∃ ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Option I) K → _ → Prop),
      (∀ T : Raw.{0} I K, rawLogPrice ψ 1 (T.group some) = rawLogPrice φ 1 T) ∧
      rawWireDistance ψ 1 none (some a) = la ∧ rawWireDistance ψ 1 none (some b) = lb := by
  obtain ⟨ψ, hψ, hA, hB⟩ := spectral_interval_of_wire_bounds φ
    (intervalWire K a) (intervalWire K b) la lb ha hb
    (fun m n ↦ by rw [hs]; exact contractionPrice_intervalWires_le φ a b m n)
    (fun m ↦ by rw [hs, contractionPrice_intervalWires_equal])
  exact ⟨ψ, group_some_logPrice_of_old_logPoint φ ψ hψ,
    (logPoint_intervalWire_eq ψ a).symm.trans hA, (logPoint_intervalWire_eq ψ b).symm.trans hB⟩
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
variable {K ι : Type*} [Field K]
def coordinatePower (n : ℕ) (x : ι → K) (w : Fin n → ι) : K := ∏ j, x (w j)
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K] {A : I → Type v} [∀ i, Fintype (A i)]
def groupedPower (n : ℕ) (T : (∀ i, A i) → K) (x : ∀ i, Fin n → A i) : K :=
  coordinatePower n T (fun j i ↦ x i j)
theorem ofRaw_groupedPower (n : ℕ) (T : (∀ i, A i) → K) :
    ofRaw (I := I) (K := K) ⟨fun i ↦ Fin n → A i, fun _ ↦ inferInstance, groupedPower n T⟩ =
      ofRaw (⟨A, inferInstance, T⟩ : Raw I K) ^ n := by
  classical
  induction n with
  | zero =>
    rw [pow_zero]
    apply Quotient.sound
    apply Raw.reindex_equivalent (fun i ↦ Equiv.equivPUnit (Fin 0 → A i))
    intro x
    change ∏ j : Fin 0, T (fun i ↦ x i j) = 1
    simp
  | succ n ih =>
    rw [pow_succ', ← ih, ← ofRaw_mul]
    apply Quotient.sound
    apply Raw.reindex_equivalent (fun i ↦ (Fin.consEquiv (fun _ : Fin (n + 1) ↦ A i)).symm)
    intro x
    exact Fin.prod_univ_succ (fun j ↦ T (fun i ↦ x i j))
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
noncomputable section
section
namespace SiteTensor
variable {I J : Type} [Fintype I] [Fintype J] {K : Type*} [Field K]
def Raw.powerTensor (T : Raw.{0} I K) (n : ℕ) : Raw.{0} I K :=
  ⟨fun i ↦ Fin n → T.Leg i, fun _ ↦ inferInstance, groupedPower n T.coeff⟩
omit [Fintype I] in
theorem Raw.powerTensor_ne_zero (T : Raw.{0} I K) (hT : T.coeff ≠ 0) (n : ℕ) :
    (T.powerTensor n).coeff ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, T.coeff x ≠ 0 := Function.ne_iff.mp hT
  intro h
  have hz := congrFun h (fun i _ ↦ x i)
  change (∏ _ : Fin n, T.coeff x) = 0 at hz
  exact (Finset.prod_ne_zero_iff.mpr fun _ _ ↦ hx) hz
variable [Nonempty I] [Nonempty J]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)
theorem rawLogPrice_group_powerTensor (T : Raw.{0} I K) (σ : I → J) (n : ℕ) :
    rawLogPrice φ c ((T.powerTensor n).group σ) = n * rawLogPrice φ c (T.group σ) := by
  let v := (normalizedSpectrum.toRingHom φ).toMonoidHom.comp (groupMulHom (K := K) σ)
  have he (S : Raw.{0} I K) : φ.val (ofRaw (S.group σ)) = v (ofRaw S) := rfl
  simp only [rawLogPrice, he, Raw.powerTensor, ofRaw_groupedPower, map_pow, NNReal.coe_pow,
    Real.logb_pow, inferInstance, instRawFiniteLeg_eq, instRawFiniteLeg_eqf, Raw_eta_inst]
  ring
theorem rawLogPrice_add_select (hc : 0 ≤ c) {A : J → Type} [∀ j, Fintype (A j)]
    (U V : (∀ j, A j) → K) (hne : U + V ≠ 0) :
    (U ≠ 0 ∧ rawLogPrice φ c ⟨A, inferInstance, U + V⟩ ≤
      rawLogPrice φ c ⟨A, inferInstance, U⟩ + c) ∨
    (V ≠ 0 ∧ rawLogPrice φ c ⟨A, inferInstance, U + V⟩ ≤
      rawLogPrice φ c ⟨A, inferInstance, V⟩ + c) := by
  classical
  let T : Fin 2 → (∀ j, A j) → K := ![U,V]
  have hsum : ∑ i, T i = U + V := by simp [T, Fin.sum_univ_two]
  obtain ⟨i, hi, hp⟩ := ordinary_sum_logb_le φ T (hsum ▸ hne) hc
  rw [hsum] at hp
  fin_cases i
  · left
    exact ⟨hi, by simpa [rawLogPrice, coeffValue, ofCoeffs, T,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hp⟩
  · right
    exact ⟨hi, by simpa [rawLogPrice, coeffValue, ofCoeffs, T,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hp⟩
end SiteTensor
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
open scoped Classical
variable {I : Type*} [Fintype I]
abbrev MaskLeg (S : Finset I) (α : Type) (i : I) := i ∈ S → α
noncomputable def Raw.maskDiagonal (K : Type*) [Field K] (S : Finset I) (α : Type) [Fintype α] :
    Raw.{0} I K :=
  ⟨MaskLeg S α, fun _ ↦ Fintype.ofFinite _, Crossing.basisTensor (fun (a : α) i (_ : i ∈ S) ↦ a)⟩
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace SiteTensor
open scoped Classical NNReal
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]
theorem Raw.maskDiagonal_coeff_at (S : Finset I) {i₀ : I} (hi₀ : i₀ ∈ S)
    {α : Type} [Fintype α] (x : ∀ i, MaskLeg S α i) :
    (Raw.maskDiagonal K S α).coeff x = if ∀ (i : I) (hi : i ∈ S), x i hi = x i₀ hi₀ then 1 else 0 := by
  unfold Raw.maskDiagonal Crossing.basisTensor
  dsimp only
  rw [Finset.sum_eq_single (x i₀ hi₀)]
  · simp only [funext_iff]
  · intro a _ hne
    exact ite_eq_right fun ha ↦ hne (congrFun (congrFun ha i₀) hi₀).symm
  · simp
variable [Nonempty I]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical
section
open SiteTensor
namespace SiteTensor.Raw
theorem ofRaw_group_diagonal_eq_mask {J I : Type} {K : Type*} [Fintype I] [Nonempty I]
    [Fintype J] [Field K] (σ : J ↪ I) (S : Finset I)
    (hS : ∀ i, i ∈ S ↔ ∃ j, σ j = i) (α : Type) [Fintype α] :
    ofRaw ((diagonal J K α).group σ) = ofRaw (maskDiagonal K S α) := by
  classical
  let fiber (i : I) (h : i ∈ S) : {j : J // σ j = i} :=
    ⟨((hS i).mp h).choose, ((hS i).mp h).choose_spec⟩
  have unique (i : I) (a b : {j : J // σ j = i}) : a = b :=
    Subtype.ext (σ.injective (a.property.trans b.property.symm))
  let e (i : I) : ((j : {j : J // σ j = i}) → α) ≃ (i ∈ S → α) :=
    { toFun := fun x h ↦ x (fiber i h)
      invFun := fun x j ↦ x ((hS i).mpr ⟨j, j.property⟩)
      left_inv := fun x ↦ funext fun j ↦ congrArg x (unique i _ j)
      right_inv := fun _ ↦ rfl }
  apply ofRaw_eq_iff.mpr (reindex_equivalent e ?_)
  intro x
  simp only [Raw.group, Raw.diagonal, Raw.maskDiagonal, Crossing.basisTensor]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply propext
  constructor
  · intro hx
    funext i hi
    change x i (fiber i hi) = a
    obtain ⟨j, hj⟩ := fiber i hi
    subst i
    exact congrFun hx j
  · intro hx
    funext j
    have hj : σ j ∈ S := (hS _).mpr ⟨j,rfl⟩
    exact (congrArg (x _) (unique _ _ (fiber _ hj))).trans (congrFun (congrFun hx _) hj)
end SiteTensor.Raw
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Finset Function
theorem independent_relocation_two {X Y : Type*} (H : X → Y → ℝ)
    (a b z : X) (c d w : Y) {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hrow : ∀ y, H z y ≤ (1 - t) * H a y + t * H b y)
    (hcol : ∀ x, H x w ≤ (1 - u) * H x c + u * H x d) :
    H z w ≤ (1 - t) * (1 - u) * H a c + (1 - t) * u * H a d +
      t * (1 - u) * H b c + t * u * H b d := by
  calc
    H z w ≤ (1 - t) * H a w + t * H b w := hrow w
    _ ≤ (1 - t) * ((1 - u) * H a c + u * H a d) +
        t * ((1 - u) * H b c + u * H b d) :=
      add_le_add (mul_le_mul_of_nonneg_left (hcol a) (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left (hcol b) ht.1)
    _ = _ := by ring
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical BigOperators
namespace SiteTensor.Relocation
variable {I J Q H M : Type} {K : Type*} {A : I → Type}
variable [Fintype I] [Fintype J] [∀ i, Fintype (A i)]
variable [Fintype Q] [Fintype H] [Fintype M] [CommSemiring K]
def marked (A : I → Type) [∀ i, Fintype (A i)] (Q : Type) [Fintype Q]
    (T : (∀ i, A i) → Q → K) : Raw (I ⊕ Unit) K where
  Leg := Sum.elim A (fun _ => Q)
  finiteLeg := fun k => by
    rcases k with i | _
    · exact inferInstanceAs (Fintype (A i))
    · exact inferInstanceAs (Fintype Q)
  coeff x := T (fun i => x (.inl i)) (x (.inr ()))
def split (A : I → Type) [∀ i, Fintype (A i)] (Q H : Type) [Fintype Q] [Fintype H]
    (S : (∀ i, A i) → Q → H → H → K) : Raw (I ⊕ Fin 3) K where
  Leg := Sum.elim A ![Q,H,H]
  finiteLeg := fun k => by
    rcases k with i | t
    · exact inferInstanceAs (Fintype (A i))
    · change Fintype (![Q,H,H] t)
      exact Fin.cases (motive := fun k => Fintype (![Q,H,H] k)) (inferInstanceAs (Fintype Q))
        (fun t => Fin.cases (motive := fun k => Fintype (![H,H] k)) (inferInstanceAs (Fintype H))
          (fun t => Fin.cases (motive := fun k => Fintype (![H] k)) (inferInstanceAs (Fintype H))
            (fun t => t.elim0) t) t) t
  coeff x := S (fun i => x (.inl i)) (x (.inr 0)) (x (.inr 1)) (x (.inr 2))
def placeMark (σ : I → J) (p : J) : I ⊕ Unit → J := Sum.elim σ (fun _ => p)
def placeSplit (σ : I → J) (c a b : J) : I ⊕ Fin 3 → J := Sum.elim σ ![c,a,b]
def plusCoeff (T : (∀ i, A i) → Q → K) (L : Q → M → H → K) (D : Q → H → M → K)
    (x : ∀ i, A i) (i : Q) (α β : H) : K :=
  ∑ j, ∑ m, T x j * L i m α * D j β m
def minusCoeff (T : (∀ i, A i) → Q → K) (D : Q → M → H → K) (L : Q → H → M → K)
    (x : ∀ i, A i) (i : Q) (α β : H) : K :=
  ∑ j, ∑ m, T x j * D j m α * L i β m
def wire (K : Type*) (M : Type) [CommSemiring K] [Fintype M] (p q : J) : Raw J K :=
  (Raw.diagonal (Fin 2) K M).group ![p,q]
private def markTupleEquiv (A : I → Type) (Q : Type) :
    ((∀ i, A i) × Q) ≃ (∀ k : I ⊕ Unit, Sum.elim A (fun _ => Q) k) where
  toFun w k := match k with
    | .inl i => w.1 i
    | .inr _ => w.2
  invFun x := (fun i => x (.inl i), x (.inr ()))
  left_inv _ := rfl
  right_inv x := by funext k; rcases k with i | ⟨⟩ <;> rfl
theorem restricts_contraction (T : (∀ i, A i) → Q → K) (σ : I → J)
    (p q : J) (S : Raw J K) (readBg : ∀ i, S.Leg (σ i) → A i)
    (P : S.Leg p → M → K) (R : S.Leg q → Q → M → K)
    (hs : ∀ x, S.coeff x = ∑ j, ∑ m, T (fun i => readBg i (x (σ i))) j *
        P (x p) m * R (x q) j m) :
    S.Restricts (((marked A Q T).group (placeMark σ q)).mul (wire K M p q)) := by
  classical
  let U := (marked A Q T).group (placeMark σ q)
  let W := wire K M p q
  let V := U.mul W
  let E : (((∀ i, A i) × Q) × (Fin 2 → M)) ≃ (∀ k, V.Leg k) :=
    ((markTupleEquiv A Q).trans (groupIndexEquiv (placeMark σ q) (marked A Q T).Leg)).prodCongr
      (groupIndexEquiv ![p,q] (fun _ => M)) |>.trans
      (Equiv.arrowProdEquivProdArrow J U.Leg W.Leg).symm
  let ok (k : J) (x : S.Leg k) (y : V.Leg k) :=
    ∀ (i : I) (h : σ i = k), y.1 ⟨.inl i, h⟩ = readBg i (h ▸ x)
  let F (k : J) (x : S.Leg k) (y : V.Leg k) : K :=
    (if ok k x y then 1 else 0) *
      (if hp : p = k then P (hp ▸ x) (y.2 ⟨0,hp⟩) else 1) *
      (if hq : q = k then R (hq ▸ x) (y.1 ⟨.inr (),hq⟩) (y.2 ⟨1,hq⟩) else 1)
  refine ⟨F, fun x => ?_⟩
  rw [← E.sum_comp]
  let b (i : I) := readBg i (x (σ i))
  have term (s : ((∀ i, A i) × Q) × (Fin 2 → M)) :
      V.coeff (E s) * ∏ k, F k (x k) (E s k) =
        ∑ m : M, if s.1.1 = b ∧ s.2 = fun _ => m then
          T b s.1.2 * P (x p) m * R (x q) s.1.2 m else 0 := by
    have hok : (∀ k, ok k (x k) (E s k)) ↔ s.1.1 = b := by
      constructor
      · intro h
        exact funext fun i => h (σ i) i rfl
      · intro h k i hi
        subst k
        exact congrFun h i
    have hp : (∏ k, if hp : p = k then
        P (hp ▸ x k) ((E s k).2 ⟨0,hp⟩) else 1) = P (x p) (s.2 0) := by
      rw [Finset.prod_eq_single p]
      · simp only; rfl
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    have hq : (∏ k, if hq : q = k then
        R (hq ▸ x k) ((E s k).1 ⟨.inr (),hq⟩) ((E s k).2 ⟨1,hq⟩) else 1) =
        R (x q) s.1.2 (s.2 1) := by
      rw [Finset.prod_eq_single q]
      · simp only; rfl
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    have hcoeff : V.coeff (E s) = T s.1.1 s.1.2 * (∑ m : M, if s.2 = fun _ => m then 1 else 0) := by
      change _ * _ = _ * _
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      congr 1
    rw [hcoeff]
    change (T s.1.1 s.1.2 * (∑ m : M, if s.2 = fun _ => m then 1 else 0)) * _ = _
    have hbprod : (∏ k, if ok k (x k) (E s k) then (1 : K) else 0) =
        if s.1.1 = b then 1 else 0 := Fintype.prod_boole.trans (if_congr hok rfl rfl)
    simp only [F, Finset.prod_mul_distrib, hbprod, hp, hq]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    by_cases hb : s.1.1 = b <;> by_cases hm : s.2 = fun _ => m <;>
      simp [hb, hm, mul_assoc]
  change S.coeff x = ∑ s, V.coeff (E s) * ∏ k, F k (x k) (E s k)
  simp_rw [term]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [hs]
  symm
  rw [Finset.sum_eq_single b]
  · simp [Finset.sum_comm (f := fun (z : Fin 2 → M) (m : M) => _), b]
  · intro a _ ha; simp [ha]
  · simp
theorem plus_restricts_opposite (T : (∀ i, A i) → Q → K)
    (L : Q → M → H → K) (D : Q → H → M → K) (σ : I → J) (c b : J) :
    ((split A Q H (plusCoeff T L D)).group (placeSplit σ c c b)).Restricts
      (((marked A Q T).group (placeMark σ b)).mul (wire K M c b)) :=
  restricts_contraction T σ c b _ (fun i x => x ⟨.inl i, rfl⟩)
    (fun x m => L (x ⟨.inr 0,rfl⟩) m (x ⟨.inr 1,rfl⟩))
    (fun x j m => D j (x ⟨.inr 2,rfl⟩) m) (fun _ => rfl)
theorem minus_restricts_opposite (T : (∀ i, A i) → Q → K)
    (D : Q → M → H → K) (L : Q → H → M → K) (σ : I → J) (c a : J) :
    ((split A Q H (minusCoeff T D L)).group (placeSplit σ c a c)).Restricts
      (((marked A Q T).group (placeMark σ a)).mul (wire K M c a)) := by
  refine restricts_contraction T σ c a _ (fun i x => x ⟨.inl i, rfl⟩)
    (fun x m => L (x ⟨.inr 0,rfl⟩) (x ⟨.inr 2,rfl⟩) m)
    (fun x j m => D j m (x ⟨.inr 1,rfl⟩)) ?_
  intro x
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro m _
  exact mul_right_comm _ _ _
theorem plus_restricts (T : (∀ i, A i) → Q → K)
    (L : Q → M → H → K) (D : Q → H → M → K) (σ : I → J) (c a b : J) :
    ((split A Q H (plusCoeff T L D)).group (placeSplit σ c a b)).Restricts
      ((((marked A Q T).group (placeMark σ b)).mul (wire K M c b)).mul (wire K H c a)) := by
  let S := split A Q H (plusCoeff T L D)
  have h := Raw.move_restricts_with_wire S (placeSplit σ c c b) (placeSplit σ c a b)
    (.inr 1) (by
      intro t ht
      rcases t with i | t
      · rfl
      · fin_cases t <;> first | rfl | exact (ht rfl).elim)
  exact restrict_trans h (Raw.mul_restricts (plus_restricts_opposite T L D σ c b) (restrict_refl _))
theorem minus_restricts (T : (∀ i, A i) → Q → K)
    (D : Q → M → H → K) (L : Q → H → M → K) (σ : I → J) (c a b : J) :
    ((split A Q H (minusCoeff T D L)).group (placeSplit σ c a b)).Restricts
      ((((marked A Q T).group (placeMark σ a)).mul (wire K M c a)).mul (wire K H c b)) := by
  let S := split A Q H (minusCoeff T D L)
  have h := Raw.move_restricts_with_wire S (placeSplit σ c a c) (placeSplit σ c a b)
    (.inr 2) (by
      intro t ht
      rcases t with i | t
      · rfl
      · fin_cases t <;> first | rfl | exact (ht rfl).elim)
  exact restrict_trans h (Raw.mul_restricts (minus_restricts_opposite T D L σ c a) (restrict_refl _))
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
noncomputable section
open scoped Classical
namespace SiteTensor.Relocation
variable {I J Q : Type} {A : I → Type} [Fintype I] [Fintype J] [Fintype Q]
variable [∀ i, Fintype (A i)] {K : Type*} [Field K]
def powerCoeff (n : ℕ) (T : (∀ i, A i) → Q → K) (x : ∀ i, Fin n → A i) (q : Fin n → Q) : K :=
  ∏ k, T (fun i => x i k) (q k)
def powerMarkEquiv (Q : Type) [Fintype Q] (n : ℕ) : Fin ((Fintype.card Q)^n) ≃ (Fin n → Q) :=
  (Fintype.equivFinOfCardEq (by simp)).symm
def finPowerCoeff (n : ℕ) (T : (∀ i, A i) → Q → K) (x : ∀ i, Fin n → A i)
    (q : Fin ((Fintype.card Q)^n)) : K :=
  powerCoeff n T x (powerMarkEquiv Q n q)
variable (n : ℕ) (T : (∀ i, A i) → Q → K)
theorem marked_power_equivalent {D : Type} [Fintype D] (e : D ≃ (Fin n → Q)) :
    (marked (fun i => Fin n → A i) D (fun x q => powerCoeff n T x (e q))).Equivalent
      ((marked A Q T).powerTensor n) := by
  let f (i : I ⊕ Unit) :
      (marked (fun i => Fin n → A i) D (fun x q => powerCoeff n T x (e q))).Leg i ≃
        ((marked A Q T).powerTensor n).Leg i := by
    rcases i with i | ⟨⟩
    · exact Equiv.refl _
    · exact e
  apply Raw.reindex_equivalent f
  intro x
  rfl
variable [Nonempty J] (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)
private theorem price_power_basis {D : Type} [Fintype D] (e : D ≃ (Fin n → Q)) (σ : I ⊕ Unit → J) :
    rawLogPrice φ c ((marked (fun i => Fin n → A i) D (fun x q => powerCoeff n T x (e q))).group σ) =
      n * rawLogPrice φ c ((marked A Q T).group σ) := by
  have h := congrArg (groupClass (K := K) σ) (ofRaw_eq_iff.mpr (marked_power_equivalent n T e))
  change ofRaw _ = ofRaw _ at h
  rw [← rawLogPrice_group_powerTensor φ c (marked A Q T) σ n]
  exact congrArg (fun S => c * Real.logb 2 (φ.val S : ℝ)) h
theorem rawLogPrice_marked_finPower (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
    (c : ℝ) (n : ℕ) (T : (∀ i, A i) → Q → K) (σ : I ⊕ Unit → J) :
    rawLogPrice φ c ((marked (fun i => Fin n → A i) (Fin ((Fintype.card Q)^n))
      (finPowerCoeff n T)).group σ) = n * rawLogPrice φ c ((marked A Q T).group σ) :=
  price_power_basis n T φ c (powerMarkEquiv Q n) σ
theorem marked_finPower_ne_zero (hT : (marked A Q T).coeff ≠ 0) :
    (marked (fun i => Fin n → A i) (Fin ((Fintype.card Q)^n)) (finPowerCoeff n T)).coeff ≠ 0 := by
  have h := ofRaw_eq_iff.mpr (marked_power_equivalent n T (powerMarkEquiv Q n))
  intro hz
  have he := (ofRaw_eq_zero_iff _).mpr hz
  exact (Raw.powerTensor_ne_zero _ hT n) ((ofRaw_eq_zero_iff _).mp (h.symm.trans he))
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
noncomputable section
open scoped Classical
namespace SiteTensor.Relocation
variable {I J : Type} {K : Type*} [Fintype I] [Fintype J]
def markCoeff (T : Raw.{0} I K) (i : I)
    (x : ∀ j : {j // j ≠ i}, T.Leg j.1) (q : T.Leg i) : K :=
  T.coeff (fun j => if h : j = i then h.symm ▸ q else x ⟨j,h⟩)
theorem marked_group_equivalent [DecidableEq I] [CommSemiring K] (T : Raw.{0} I K) (i : I) :
    ((marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i) (markCoeff T i)).group
      (placeMark Subtype.val i)).Equivalent T := by
  classical
  let U := marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i) (markCoeff T i)
  let p := placeMark (Subtype.val : {j // j ≠ i} → I) i
  let e (j : I) : (U.group p).Leg j ≃ T.Leg j := {
    toFun := fun z => if h : j = i then h.symm ▸ z ⟨.inr (), h.symm⟩
      else z ⟨.inl ⟨j,h⟩, rfl⟩
    invFun := fun x t => match t with
      | ⟨.inl ⟨k,_⟩,h⟩ => cast (congrArg T.Leg (show j = k from h.symm)) x
      | ⟨.inr (),h⟩ => cast (congrArg T.Leg (show j = i from h.symm)) x
    left_inv := by
      intro z
      funext t
      rcases t with ⟨⟨k,hk⟩ | ⟨⟩,h⟩
      · change k = j at h
        subst j
        simp [hk]
        rfl
      · change i = j at h
        subst j
        simp
        rfl
    right_inv := by
      intro x
      by_cases h : j = i
      · subst j
        simp
        rfl
      · simp [h]
        rfl }
  apply Raw.reindex_equivalent (X := U.group p) (Y := T) e
  intro x
  apply congrArg T.coeff
  funext j
  by_cases h : j = i
  · subst j
    simp [e]
    rfl
  · simp [e,h]
    rfl
theorem ofRaw_update_eq_mark [DecidableEq I] [Field K] (T : Raw.{0} I K) (i : I)
    (σ : I → J) (p : J) :
    ofRaw (T.group (Function.update σ i p)) =
      ofRaw ((marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i) (markCoeff T i)).group
        (placeMark (σ ∘ Subtype.val) p)) := by
  classical
  let U := marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i) (markCoeff T i)
  let q := placeMark (Subtype.val : {j // j ≠ i} → I) i
  have hp : (Function.update σ i p) ∘ q = placeMark (σ ∘ Subtype.val) p := by
    funext j
    rcases j with ⟨j,h⟩ | ⟨⟩
    · exact Function.update_of_ne h _ _
    · exact Function.update_self ..
  let f := groupClass (K := K) (Function.update σ i p)
  have h : f (ofRaw (U.group q)) = f (ofRaw T) := congrArg f
    (ofRaw_eq_iff.mpr (marked_group_equivalent T i))
  calc
    _ = f (ofRaw (U.group q)) := h.symm
    _ = ofRaw (U.group ((Function.update σ i p) ∘ q)) :=
      ofRaw_eq_iff.mpr (Raw.group_group_equivalent U q (Function.update σ i p))
    _ = _ := congrArg (fun s => ofRaw (U.group s)) hp
theorem rawLogPrice_update_eq_mark [DecidableEq I] [Nonempty J] [Field K]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)
    (T : Raw.{0} I K) (i : I) (σ : I → J) (p : J) :
    rawLogPrice φ c (T.group (Function.update σ i p)) =
      rawLogPrice φ c ((marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i)
        (markCoeff T i)).group (placeMark (σ ∘ Subtype.val) p)) := by
  simp only [rawLogPrice, ofRaw_update_eq_mark T i σ p]
theorem marked_ne_zero [DecidableEq I] [Field K] (T : Raw.{0} I K) (i : I) (hT : T.coeff ≠ 0) :
    (marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i) (markCoeff T i)).coeff ≠ 0 := by
  let : Nonempty I := ⟨i⟩
  let U := marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i) (markCoeff T i)
  let q := placeMark (Subtype.val : {j // j ≠ i} → I) i
  apply (U.group_ne_zero_iff q).mp
  intro hz
  exact hT ((ofRaw_eq_zero_iff T).mp ((ofRaw_eq_iff.mpr (marked_group_equivalent T i)).symm.trans
    ((ofRaw_eq_zero_iff _).mpr hz)))
theorem exists_finPower_update [DecidableEq I] [Nonempty J] [Field K]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)
    (T : Raw.{0} I K) (hT : T.coeff ≠ 0) (i : I) (x : I → J) (n : ℕ) :
    ∃ S : (∀ j : {j // j ≠ i}, Fin n → T.Leg j.1) → Fin ((Fintype.card (T.Leg i))^n) → K,
      (marked _ _ S).coeff ≠ 0 ∧ ∀ p : J,
        rawLogPrice φ c ((marked _ _ S).group (placeMark (x ∘ Subtype.val) p)) =
          n * rawLogPrice φ c (T.group (Function.update x i p)) := by
  refine ⟨finPowerCoeff n (markCoeff T i), marked_finPower_ne_zero n _ (marked_ne_zero T i hT), ?_⟩
  intro p
  rw [rawLogPrice_marked_finPower, rawLogPrice_update_eq_mark φ c T i x p]
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Real
private theorem interior_floor {Q : ℕ} (hQ : 2 ≤ Q) {x : ℝ} (h₁ : 1 ≤ x) (h₂ : x ≤ Q) :
    ∃ b : ℕ, b + 2 ≤ Q ∧ (b : ℝ) + 1 ≤ x ∧ x ≤ (b : ℝ) + 2 := by
  by_cases htop : ⌊x⌋₊ < Q
  · have hb := (Nat.one_le_floor_iff x).mpr h₁
    obtain ⟨b, hb'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ⌊x⌋₊ ≠ 0)
    refine ⟨b, by omega, ?_, ?_⟩
    · simpa [hb'] using Nat.floor_le (by linarith : 0 ≤ x)
    · have := Nat.lt_floor_add_one x
      rw [hb', Nat.cast_succ] at this
      linarith
  · have hb : Q - 2 + 2 = Q := by omega
    refine ⟨Q - 2, hb.le, ?_, ?_⟩
    · have hx := Nat.floor_le (by linarith : 0 ≤ x)
      have h : Q ≤ ⌊x⌋₊ := by omega
      have : (Q : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h
      rw [Nat.cast_sub hQ]
      push_cast
      linarith
    · rw [Nat.cast_sub hQ]
      push_cast
      linarith
private theorem choose_adjacent {Q : ℕ} (b : ℕ) (hb : b + 1 ≤ Q) :
    (Q.choose (b + 1) : ℝ) / Q.choose b = ((Q : ℝ) - b) / ((b : ℝ) + 1) := by
  have hc : (0 : ℝ) < Q.choose b := by exact_mod_cast Nat.choose_pos (by omega : b ≤ Q)
  apply (div_eq_div_iff hc.ne' (by positivity)).mpr
  have h := congrArg (Nat.cast (R := ℝ)) (Nat.choose_succ_right_eq Q b)
  push_cast [Nat.cast_sub (by omega : b ≤ Q)] at h
  linarith only [h]
theorem relocation_level_bounds {Q : ℕ} (hQ : 2 ≤ Q) {s : ℝ} (hs : s ∈ Set.Icc (-1) 1) :
    ∃ b : ℕ, b + 2 ≤ Q ∧
      logb 2 (Q.choose (b + 2)) - logb 2 (Q.choose (b + 1)) ∈
        Set.Icc (s * logb 2 Q - 2) (s * logb 2 Q) ∧
      logb 2 (Q.choose b) - logb 2 (Q.choose (b + 1)) ∈
        Set.Icc (-(s * logb 2 Q) - 2) (-(s * logb 2 Q)) := by
  have hQ' : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ₀ : (0 : ℝ) < Q := by linarith
  let r := (Q : ℝ) ^ s
  have hr : 0 < r := Real.rpow_pos_of_pos hQ₀ _
  have hr₁ : (Q : ℝ)⁻¹ ≤ r := by
    simpa [r, Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ Q) hs.1
  have hr₂ : r ≤ Q := by
    simpa [r, Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ Q) hs.2
  have hQr : 1 ≤ (Q : ℝ) * r := by simpa [mul_comm] using (inv_le_iff_one_le_mul₀ hQ₀).mp hr₁
  have hden : 0 < 1 + r := by linarith
  obtain ⟨b, hb, hbx, hxb⟩ := interior_floor hQ
    ((le_div_iff₀ hden).mpr (by linarith : 1 * (1 + r) ≤ (Q : ℝ) + 1))
    ((div_le_iff₀ hden).mpr (by linarith))
  have hbx' := (le_div_iff₀ hden).mp hbx
  have hxb' := (div_le_iff₀ hden).mp hxb
  let A := (Q : ℝ) - b - 1
  let B := (b : ℝ) + 1
  have hA : 1 ≤ A := by
    have : (b : ℝ) + 2 ≤ Q := by exact_mod_cast hb
    dsimp [A]
    linarith
  have hB : 1 ≤ B := by dsimp [B]; linarith [Nat.cast_nonneg (α := ℝ) b]
  let p := A / (B + 1)
  let m := B / (A + 1)
  have hp : 0 < p := div_pos (by linarith) (by linarith)
  have hm : 0 < m := div_pos (by linarith) (by linarith)
  have hPu : p ≤ r := by
    apply (div_le_iff₀ (by linarith : 0 < B + 1)).mpr
    dsimp [A, B]
    linarith only [hxb']
  have hMu : m ≤ r⁻¹ := by
    rw [← one_div, div_le_div_iff₀ (by linarith : 0 < A + 1) hr]
    dsimp [A, B]
    linarith only [hbx']
  have hprod : 1 / 4 ≤ p * m := by
    dsimp [p, m]
    rw [div_mul_div_comm]
    apply (le_div_iff₀ (mul_pos (by linarith) (by linarith))).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
  have hlprod := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 1 / 4) hprod
  have hlog : logb 2 (1 / 4) = -2 := by
    rw [show (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
  rw [hlog, Real.logb_mul hp.ne' hm.ne'] at hlprod
  have hpl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hp hPu
  have hml := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hm hMu
  have hlr : logb 2 r = s * logb 2 Q := Real.logb_rpow_eq_mul_logb_of_pos hQ₀
  rw [hlr] at hpl
  rw [Real.logb_inv, hlr] at hml
  have hc (k : ℕ) (hk : k ≤ Q) : (0 : ℝ) < Q.choose k := by exact_mod_cast Nat.choose_pos hk
  have hp' : (Q.choose (b+2) : ℝ) / Q.choose (b+1) = p := by
    convert choose_adjacent (b + 1) hb using 1
    dsimp [p, A, B]
    push_cast
    ring
  have hm' : (Q.choose b : ℝ) / Q.choose (b+1) = m := by
    rw [← inv_div, choose_adjacent b (by omega), inv_div]
    dsimp [m, A, B]
    ring
  refine ⟨b, hb, ?_, ?_⟩
  · rw [← Real.logb_div (hc _ hb).ne' (hc _ (by omega)).ne', hp']
    exact ⟨by linarith, hpl⟩
  · rw [← Real.logb_div (hc _ (by omega)).ne' (hc _ (by omega)).ne', hm']
    exact ⟨by linarith, hml⟩
theorem relocation_level_bounds_for_threshold {n : ℕ} (hn : 0 < n) {t c : ℝ}
    (ht : 0 ≤ t) (hc : |c| ≤ n * t) :
    ∃ b : ℕ, b + 2 ≤ 2^n ∧
      t * (logb 2 ((2^n : ℕ).choose (b + 2)) - logb 2 ((2^n : ℕ).choose (b + 1))) ≤ c ∧
      t * (logb 2 ((2^n : ℕ).choose b) - logb 2 ((2^n : ℕ).choose (b + 1))) ≤ -c := by
  have hQ : 2 ≤ (2 : ℕ)^n := Nat.le_pow hn
  have hlog : logb 2 ((2^n : ℕ) : ℝ) = n := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  obtain ⟨s, hs, hcs⟩ : ∃ s ∈ Set.Icc (-1 : ℝ) 1, t * (s * n) = c := by
    rcases ht.eq_or_lt with rfl | ht'
    · have hc' : c = 0 := by simpa using hc
      exact ⟨0, by constructor <;> norm_num, by simp [hc']⟩
    have hnt : 0 < (n : ℝ) * t := by positivity
    refine ⟨c / (n * t), ⟨(le_div_iff₀ hnt).mpr ?_, (div_le_iff₀ hnt).mpr ?_⟩, ?_⟩
    · linarith [(abs_le.mp hc).1]
    · linarith [(abs_le.mp hc).2]
    · field_simp
  obtain ⟨b, hb, hp, hm⟩ := relocation_level_bounds hQ hs
  rw [hlog] at hp hm
  refine ⟨b, hb, (mul_le_mul_of_nonneg_left hp.2 ht).trans_eq hcs, ?_⟩
  exact (mul_le_mul_of_nonneg_left hm.2 ht).trans_eq (by rw [mul_neg, hcs])
open Filter
open scoped Topology
private theorem ratio_slope_limit {f : ℕ → ℝ} {a : ℝ}
    (h : ∀ᶠ n : ℕ in atTop, f n ∈ Set.Icc (n * a - 2) (n * a)) :
    Tendsto (fun n : ℕ ↦ f n / n) atTop (𝓝 a) := by
  have hl : Tendsto (fun n : ℕ ↦ a - 2 / (n : ℝ)) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop 0, h] with n hn h
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    apply (le_div_iff₀ hn').mpr
    rw [sub_mul, div_mul_cancel₀ _ hn'.ne']
    linarith only [h.1]
  · filter_upwards [eventually_gt_atTop 0, h] with n hn h
    exact (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mpr (by linarith only [h.2])
theorem relocation_level_limits {q : ℕ} (hq : 2 ≤ q) {s : ℝ} (hs : s ∈ Set.Icc (-1) 1) :
    ∃ b : ℕ → ℕ, (∀ᶠ n : ℕ in atTop, b n + 2 ≤ q^n) ∧
      Tendsto (fun n : ℕ ↦ (logb 2 ((q^n).choose (b n + 2)) -
        logb 2 ((q^n).choose (b n + 1))) / n) atTop (𝓝 (logb 2 q * s)) ∧
      Tendsto (fun n : ℕ ↦ (logb 2 ((q^n).choose (b n)) -
        logb 2 ((q^n).choose (b n + 1))) / n) atTop (𝓝 (-(logb 2 q * s))) := by
  classical
  choose f hf using fun (n : ℕ) (hn : 0 < n) ↦ relocation_level_bounds (hq.trans (Nat.le_pow hn)) hs
  let b (n : ℕ) := if hn : 0 < n then f n hn else 0
  refine ⟨b, ?_, ratio_slope_limit ?_, ratio_slope_limit ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with n hn
    simpa [b, hn] using (hf n hn).1
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have h := (hf n hn).2.1
    rw [Nat.cast_pow, Real.logb_pow] at h
    simpa [b, hn, mul_comm, mul_left_comm, mul_assoc] using h
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have h := (hf n hn).2.2
    rw [Nat.cast_pow, Real.logb_pow] at h
    simpa [b, hn, mul_comm, mul_left_comm, mul_assoc] using h
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter Real
open scoped Topology
theorem relocation_le_of_ratio_limits {wA wB wC u d c slope : ℝ}
    (plus minus : ℕ → ℝ)
    (hplus : Tendsto (fun n : ℕ ↦ plus n / n) atTop (𝓝 slope))
    (hminus : Tendsto (fun n : ℕ ↦ minus n / n) atTop (𝓝 (-slope)))
    (hbound : ∀ᶠ n : ℕ in atTop, (n : ℝ) * wC ≤ c +
      max (n * wB + ((1 - u) * d) * plus n) (n * wA + (u * d) * minus n)) :
    wC ≤ max (wB + ((1 - u) * d) * slope) (wA + (u * d) * (-slope)) := by
  have hl := (tendsto_const_div_atTop_nhds_zero_nat c).add <|
    ((hplus.const_mul ((1 - u) * d)).const_add wB).max
      ((hminus.const_mul (u * d)).const_add wA)
  rw [zero_add] at hl
  refine ge_of_tendsto hl ?_
  filter_upwards [eventually_gt_atTop 0, hbound] with n hn h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  change wC ≤ c / n + max (wB + ((1 - u) * d) * (plus n / n)) (wA + (u * d) * (minus n / n))
  apply (mul_le_mul_iff_of_pos_right hn').mp
  rw [add_mul, max_mul_of_nonneg _ _ hn'.le]
  have hn0 : (n : ℝ) ≠ 0 := hn'.ne'
  have e1 : c / ↑n * ↑n = c := div_mul_cancel₀ c hn0
  have e2 : (wB + (1 - u) * d * (plus n / ↑n)) * ↑n = ↑n * wB + (1 - u) * d * plus n := by
    rw [add_mul, mul_assoc ((1 - u) * d), div_mul_cancel₀ _ hn0]; ring1
  have e3 : (wA + u * d * (minus n / ↑n)) * ↑n = ↑n * wA + u * d * minus n := by
    rw [add_mul, mul_assoc (u * d), div_mul_cancel₀ _ hn0]; ring1
  convert h using 1
  all_goals first | rfl | ring1 | rw [e1, e2, e3]
theorem relocation_le_of_two_bounds {wA wB wC u d c : ℝ} {q : ℕ}
    (hd : 0 < d) (hq : 2 ≤ q)
    (hmove : |wA - wB| ≤ d * logb 2 q)
    (hbranches : ∀ s : ℝ, s ∈ Set.Icc (-1) 1 → ∃ plus minus : ℕ → ℝ,
      Tendsto (fun n : ℕ ↦ plus n / n) atTop (𝓝 (logb 2 q * s)) ∧
      Tendsto (fun n : ℕ ↦ minus n / n) atTop (𝓝 (-(logb 2 q * s))) ∧
      ∀ᶠ n : ℕ in atTop, (n : ℝ) * wC ≤ c +
        max (n * wB + ((1 - u) * d) * plus n) (n * wA + (u * d) * minus n)) :
    wC ≤ (1 - u) * wA + u * wB := by
  have hlog : 0 < logb 2 q := Real.logb_pos (by norm_num) (by exact_mod_cast lt_of_lt_of_le Nat.one_lt_two hq)
  have hden := mul_pos hd hlog
  let s := (wA - wB) / (d * logb 2 q)
  have hs : s ∈ Set.Icc (-1) 1 := by
    have h := abs_le.mp hmove
    exact ⟨(le_div_iff₀ hden).mpr (by linarith), (div_le_iff₀ hden).mpr (by linarith)⟩
  obtain ⟨plus, minus, hplus, hminus, h⟩ := hbranches s hs
  have hbal : d * logb 2 q * s = wA - wB := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hden.ne'
  apply (relocation_le_of_ratio_limits plus minus hplus hminus h).trans
  apply max_le <;> linarith only [hbal, congrArg (u * ·) hbal]
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Exterior
variable (K : Type*) [CommRing K] {Q : ℕ}
def sign (i : Fin Q) (S : Finset (Fin Q)) : K :=
  (-1) ^ (S.filter (· < i)).card
@[simp] theorem sign_sq (i : Fin Q) (S : Finset (Fin Q)) :
    sign K i S * sign K i S = 1 := by
  simp [sign, ← mul_pow]
@[simp] theorem sign_erase_self (i : Fin Q) (S : Finset (Fin Q)) :
    sign K i (S.erase i) = sign K i S := by
  simp [sign, Finset.filter_erase]
@[simp] theorem sign_insert_self (i : Fin Q) (S : Finset (Fin Q)) :
    sign K i (insert i S) = sign K i S := by
  simp [sign, Finset.filter_insert]
theorem sign_insert (i j : Fin Q) (S : Finset (Fin Q)) (hi : i ∉ S) :
    sign K j (insert i S) = if i < j then -sign K j S else sign K j S := by
  by_cases h : i < j <;> simp [sign, Finset.filter_insert, h, hi, pow_succ]
theorem sign_cancel {i j : Fin Q} {S : Finset (Fin Q)} (hij : i ≠ j)
    (hi : i ∉ S) (hj : j ∈ S) :
    sign K i S * sign K j (insert i S) + sign K j S * sign K i (S.erase j) = 0 := by
  have he := sign_insert K j i (S.erase j) (Finset.notMem_erase j S)
  rw [Finset.insert_erase hj] at he
  rw [sign_insert K i j S hi]
  rcases lt_or_gt_of_ne hij with h | h
  · simp only [h, not_lt_of_gt h, ite_true, ite_false] at he ⊢
    rw [he]
    ring
  · simp only [h, not_lt_of_gt h, ite_true, ite_false] at he ⊢
    rw [he]
    ring
end Exterior
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Exterior
open scoped BigOperators
abbrev Level (Q b : ℕ) := {S : Finset (Fin Q) // S.card = b}
theorem card_level (Q b : ℕ) : Fintype.card (Level Q b) = Q.choose b := by
  simp [Level, Fintype.card_finset_len]
variable (K : Type*) [CommRing K] {Q b : ℕ}
def create (i : Fin Q) : Matrix (Level Q (b + 1)) (Level Q b) K :=
  fun U S => if i ∉ S.val ∧ U.val = insert i S.val then sign K i S.val else 0
def contract (j : Fin Q) : Matrix (Level Q b) (Level Q (b + 1)) K :=
  fun R S => if j ∈ S.val ∧ R.val = S.val.erase j then sign K j S.val else 0
private theorem contract_create_entry (i j : Fin Q) (R S : Level Q b) :
    (contract (b := b) K j * create (b := b) K i) R S =
      if i ∉ S.val ∧ j ∈ insert i S.val ∧ R.val = (insert i S.val).erase j then
        sign K i S.val * sign K j (insert i S.val) else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : i ∈ S.val
  · simp [create, hi]
  let U : Level Q (b + 1) := ⟨insert i S.val, by simp [hi, S.property]⟩
  rw [Finset.sum_eq_single U]
  · dsimp [U, create, contract]
    split_ifs <;> simp_all [mul_comm]
  · intro V _ hV
    have hne : V.val ≠ insert i S.val := fun h => hV (Subtype.ext h)
    simp [create, hne]
  · simp
private theorem create_contract_entry (i j : Fin Q) (R S : Level Q (b + 1)) :
    (create (b := b) K i * contract (b := b) K j) R S =
      if j ∈ S.val ∧ i ∉ S.val.erase j ∧ R.val = insert i (S.val.erase j) then
        sign K j S.val * sign K i (S.val.erase j) else 0 := by
  rw [Matrix.mul_apply]
  by_cases hj : j ∈ S.val
  · let U : Level Q b := ⟨S.val.erase j, by rw [Finset.card_erase_of_mem hj, S.property]; rfl⟩
    rw [Finset.sum_eq_single U]
    · dsimp [U, create, contract]
      split_ifs <;> simp_all [mul_comm]
    · intro V _ hV
      have hne : V.val ≠ S.val.erase j := fun h => hV (Subtype.ext h)
      simp [contract, hne]
    · simp
  · simp [contract, hj]
theorem anticommutator (i j : Fin Q) :
    contract (b := b + 1) K j * create (b := b + 1) K i + create (b := b) K i * contract (b := b) K j =
      (if i = j then 1 else 0 : Matrix (Level Q (b + 1)) (Level Q (b + 1)) K) := by

  ext R S
  rw [Matrix.add_apply, contract_create_entry, create_contract_entry]
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ S.val
    · simp [hi, Finset.insert_erase hi, Matrix.one_apply,
        Subtype.ext_iff]
    · simp [hi, Finset.erase_insert hi, Matrix.one_apply,
        Subtype.ext_iff]
  · have hji := Ne.symm hij
    by_cases hi : i ∈ S.val <;> by_cases hj : j ∈ S.val
    all_goals simp [hij, hji, hi, hj, Finset.erase_insert_of_ne hij]
    by_cases he : R.val = insert i (S.val.erase j)
    · simpa [he] using sign_cancel K hij hi hj
    · simp [he]
theorem split_coeff (v : Fin Q → K) (i : Fin Q) (R S : Level Q (b + 1)) :
    (∑ j, (contract (b := b + 1) K j * create (b := b + 1) K i) R S * v j) +
      (∑ j, (create (b := b) K i * contract (b := b) K j) R S * v j) =
        (if R = S then 1 else 0) * v i := by
  rw [← Finset.sum_add_distrib]
  simp_rw [← add_mul, ← Matrix.add_apply]
  simp_rw [anticommutator]
  rw [Finset.sum_eq_single i]
  · simp [Matrix.one_apply]
  · intro j _ hji
    simp [Ne.symm hji]
  · simp
end Exterior
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace SiteTensor.Relocation
open Exterior
open scoped BigOperators Classical
variable {I J : Type} {K : Type*} {A : I → Type} [CommRing K] {Q b : ℕ}
theorem plus_add_minus_eq (T : (∀ i, A i) → Fin Q → K)
    (x : ∀ i, A i) (i : Fin Q) (α β : Level Q (b + 1)) :
    plusCoeff T (create K) (contract K) x i α β +
      minusCoeff T (contract K) (create K) x i α β =
        T x i * (if α = β then 1 else 0) := by
  have h := split_coeff K (T x) i β α
  simp only [Matrix.mul_apply, Finset.sum_mul] at h
  simpa only [plusCoeff, minusCoeff, mul_assoc, mul_comm, mul_left_comm, eq_comm] using h
theorem grouped_split_le_of_add {U H : Type} [Fintype U] [Fintype H]
    [Fintype I] [Fintype J] [Nonempty J] [∀ i, Fintype (A i)]
    (σ : I → J) (c a d : J) (P S R : (∀ i, A i) → U → H → H → K)
    (hsum : ∀ x i α β, P x i α β = S x i α β + R x i α β) :
    ofRaw ((split A U H P).group (placeSplit σ c a d)) ≤
      ofRaw ((split A U H S).group (placeSplit σ c a d)) +
        ofRaw ((split A U H R).group (placeSplit σ c a d)) := by
  let V (f : (∀ i, A i) → U → H → H → K) := (split A U H f).group (placeSplit σ c a d)
  let s : (∀ j, (V P).Leg j) → K := (V S).coeff
  let t : (∀ j, (V P).Leg j) → K := (V R).coeff
  have he : (V P).coeff = s + t := funext fun _ => hsum _ _ _ _
  apply ofRaw_le_iff.mpr
  change Crossing.IsRestriction (V P).coeff (sumCoeff s t)
  rw [he]
  exact ordinary_add_restricts _ _
theorem grouped_split_le [Fintype I] [Fintype J] [Nonempty J] [∀ i, Fintype (A i)]
    (T : (∀ i, A i) → Fin Q → K) (σ : I → J) (c a d : J) :
    ofRaw ((split A (Fin Q) (Level Q (b + 1))
      (fun x i α β => T x i * (if α = β then 1 else 0))).group (placeSplit σ c a d)) ≤
      ofRaw ((split A (Fin Q) (Level Q (b + 1)) (plusCoeff T (create K) (contract K))).group
        (placeSplit σ c a d)) +
      ofRaw ((split A (Fin Q) (Level Q (b + 1)) (minusCoeff T (contract K) (create K))).group
        (placeSplit σ c a d)) :=
  grouped_split_le_of_add σ c a d _ _ _ fun x i α β => (plus_add_minus_eq T x i α β).symm
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical
namespace SiteTensor.Relocation
variable {I J Q : Type} {K : Type*} {A : I → Type}
variable [Fintype I] [Fintype J] [Fintype Q] [∀ i, Fintype (A i)] [CommSemiring K]
theorem grouped_split_eq_mul (T : (∀ i, A i) → Q → K) (H : Type) [Fintype H] [DecidableEq H]
    (σ : I → J) (c a b : J) :
    ofRaw ((split A Q H (fun x i α β => T x i * if α = β then 1 else 0)).group
      (placeSplit σ c a b)) =
      ofRaw ((marked A Q T).group (placeMark σ c)) * ofRaw (wire K H a b) := by
  let S := (split A Q H (fun x i α β => T x i * if α = β then 1 else 0)).group
    (placeSplit σ c a b)
  let U := (marked A Q T).group (placeMark σ c)
  let W := wire K H a b
  let mark (j : J) (x : S.Leg j) : U.Leg j := fun t => match t with
    | ⟨.inl i,h⟩ => x ⟨.inl i,h⟩
    | ⟨.inr (),h⟩ => x ⟨.inr 0,h⟩
  let ends (j : J) (x : S.Leg j) : W.Leg j := fun ⟨t,h⟩ =>
    match t,h with
    | 0,h => x ⟨.inr 1,h⟩
    | 1,h => x ⟨.inr 2,h⟩
  let join (j : J) (y : U.Leg j × W.Leg j) : S.Leg j := fun t => match t with
    | ⟨.inl i,h⟩ => y.1 ⟨.inl i,h⟩
    | ⟨.inr 0,h⟩ => y.1 ⟨.inr (),h⟩
    | ⟨.inr 1,h⟩ => y.2 ⟨0,h⟩
    | ⟨.inr 2,h⟩ => y.2 ⟨1,h⟩
  let e (j : J) : S.Leg j ≃ (U.mul W).Leg j := {
    toFun := fun x => (mark j x, ends j x)
    invFun := join j
    left_inv := by
      intro x
      funext ⟨k,h⟩
      rcases k with i | i
      · rfl
      · fin_cases i <;> rfl
    right_inv := by
      intro y
      apply Prod.ext
      · funext ⟨k,h⟩
        rcases k with i | ⟨⟩ <;> rfl
      · funext ⟨i,h⟩
        fin_cases i <;> rfl }
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  let labels (t : Fin 2) : H := (ends _ (x (![a,b] t))) ⟨t,rfl⟩
  change _ * (if labels 0 = labels 1 then (1 : K) else 0) =
    _ * (Raw.diagonal (Fin 2) K H).coeff labels
  congr 1
  rw [Raw.diagonal_coeff_at (K := K) (1 : Fin 2) labels]
  congr 1
  exact propext ⟨fun h i => by fin_cases i <;> first | exact h | rfl, fun h => h 0⟩
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical NNReal
open Real
namespace SiteTensor
variable {J : Type} {K : Type*} [Fintype J] [Nonempty J] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
private theorem logprice_le_of_sum (X Y Z : Raw.{0} J K) (c : ℝ) (hc : 0 ≤ c)
    (hX : X.coeff ≠ 0) (hs : ofRaw X ≤ ofRaw Y + ofRaw Z) :
    rawLogPrice φ c X ≤ c + max (rawLogPrice φ c Y) (rawLogPrice φ c Z) := by
  let f (T : Raw.{0} J K) : ℝ := φ.val (ofRaw T)
  have hx : 0 < f X := by exact_mod_cast zero_lt_one.trans_le (one_le_raw_spectralValue φ X hX)
  have hnn := φ.property.2.2.2.2 _ _ hs
  rw [φ.property.2.2.1] at hnn
  have h : f X ≤ f Y + f Z := by exact_mod_cast hnn
  have branch {U : Raw.{0} J K} (hU : f X ≤ 2 * f U) : rawLogPrice φ c X ≤ c + rawLogPrice φ c U := by
    have hu : 0 < f U := by linarith
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hx hU
    rw [Real.logb_mul (by norm_num) hu.ne', Real.logb_self_eq_one (by norm_num)] at hl
    change c * logb 2 (f X) ≤ c + c * logb 2 (f U)
    linarith [mul_le_mul_of_nonneg_left hl hc]
  rcases le_total (f Y) (f Z) with h' | h'
  · exact (branch (U := Z) (by linarith)).trans (by gcongr; exact le_max_right _ _)
  · exact (branch (U := Y) (by linarith)).trans (by gcongr; exact le_max_left _ _)
omit [Fintype J] [Nonempty J] in
private theorem wire_coeff_nonzero (M : Type) [Fintype M] [Nonempty M] (p q : J) :
    (Relocation.wire K M p q).coeff ≠ 0 := by
  unfold Relocation.wire
  apply (Raw.group_ne_zero_iff ..).mpr
  intro h
  have H := congrFun h (fun _ => Classical.arbitrary M)
  change (Raw.diagonal (Fin 2) K M).coeff (fun _ => Classical.arbitrary M) = 0 at H
  simp [Raw.diagonal_coeff_at (0 : Fin 2)] at H
theorem relocation_finite_price_bound (A B C : Raw.{0} J K)
    (hA : A.coeff ≠ 0) (hB : B.coeff ≠ 0) (hC : C.coeff ≠ 0)
    (H P M : Type) [Fintype H] [Fintype P] [Fintype M] [Nonempty H] [Nonempty P] [Nonempty M]
    (a b z : J) (u d c : ℝ) (hc : 0 ≤ c)
    (hd : rawWireDistance φ c a b = d) (hza : rawWireDistance φ c z a = u * d)
    (hzb : rawWireDistance φ c z b = (1 - u) * d)
    (h : ofRaw C * ofRaw (Relocation.wire K H a b) ≤
      (ofRaw B * ofRaw (Relocation.wire K P z b)) * ofRaw (Relocation.wire K H z a) +
      (ofRaw A * ofRaw (Relocation.wire K M z a)) * ofRaw (Relocation.wire K H z b)) :
    rawLogPrice φ c C ≤ c +
      max (rawLogPrice φ c B + ((1 - u) * d) * (logb 2 (Fintype.card P) - logb 2 (Fintype.card H)))
        (rawLogPrice φ c A + (u * d) * (logb 2 (Fintype.card M) - logb 2 (Fintype.card H))) := by
  have mul_ne (X Y : Raw.{0} J K) (hx : X.coeff ≠ 0) (hy : Y.coeff ≠ 0) : (X.mul Y).coeff ≠ 0 := by
    intro hzero
    have H := (ofRaw_eq_zero_iff (X.mul Y)).mpr hzero
    rw [ofRaw_mul] at H
    exact (mul_ne_zero ((ofRaw_eq_zero_iff X).not.mpr hx) ((ofRaw_eq_zero_iff Y).not.mpr hy)) H
  have hw (D : Type) [Fintype D] [Nonempty D] (p q : J) :
      rawLogPrice φ c (Relocation.wire K D p q) = rawWireDistance φ c p q * logb 2 (Fintype.card D) :=
    rawLogPrice_group_diagonal φ ![p,q] c
  have addwire (X : Raw.{0} J K) (hx : X.coeff ≠ 0) (D : Type) [Fintype D] [Nonempty D] (p q : J) :
      rawLogPrice φ c (X.mul (Relocation.wire K D p q)) =
        rawLogPrice φ c X + rawWireDistance φ c p q * logb 2 (Fintype.card D) := by
    rw [rawLogPrice_mul φ c _ _ hx (wire_coeff_nonzero D p q), hw]
  have hs := logprice_le_of_sum φ (C.mul (Relocation.wire K H a b))
    ((B.mul (Relocation.wire K P z b)).mul (Relocation.wire K H z a))
    ((A.mul (Relocation.wire K M z a)).mul (Relocation.wire K H z b)) c hc
    (mul_ne _ _ hC (wire_coeff_nonzero H a b)) h
  rw [addwire C hC, addwire _ (mul_ne _ _ hB (wire_coeff_nonzero P z b)),
    addwire _ (mul_ne _ _ hA (wire_coeff_nonzero M z a)), addwire B hB, addwire A hA,
    hd, hza, hzb] at hs
  rw [← sub_le_iff_le_add']
  apply le_trans (b := max _ _ - d * logb 2 (Fintype.card H))
  · linarith only [hs]
  rw [sub_eq_add_neg, ← max_add_add_right]
  apply max_le_max <;> apply le_of_eq <;> ring
namespace Relocation
open Exterior
theorem marked_finite_price_bound {I : Type} [Fintype I] {A : I → Type} [∀ i, Fintype (A i)]
    {Q b : ℕ} (hb : b + 2 ≤ Q) (T : (∀ i, A i) → Fin Q → K)
    (hT : (marked A (Fin Q) T).coeff ≠ 0) (σ : I → J) (a z e : J)
    (u d c : ℝ) (hc : 0 ≤ c) (hd : rawWireDistance φ c a e = d)
    (hza : rawWireDistance φ c z a = u * d) (hze : rawWireDistance φ c z e = (1 - u) * d) :
    rawLogPrice φ c ((marked A (Fin Q) T).group (placeMark σ z)) ≤ c +
      max (rawLogPrice φ c ((marked A (Fin Q) T).group (placeMark σ e)) +
            ((1 - u) * d) * (logb 2 (Q.choose (b+2)) - logb 2 (Q.choose (b+1))))
          (rawLogPrice φ c ((marked A (Fin Q) T).group (placeMark σ a)) +
            (u * d) * (logb 2 (Q.choose b) - logb 2 (Q.choose (b+1)))) := by
  have nz (k : ℕ) (hk : k ≤ Q) : Nonempty (Level Q k) :=
    Fintype.card_pos_iff.mp (by rw [card_level]; exact Nat.choose_pos hk)
  have := nz b (by omega)
  have := nz (b+1) (by omega)
  have := nz (b+2) hb
  have hsplit := grouped_split_le (b := b) T σ z a e
  have hprod := grouped_split_eq_mul T (Level Q (b+1)) σ z a e
  have hclass := hprod.symm.le.trans <| hsplit.trans (add_mono
    (ofRaw_le_iff.mpr (plus_restricts T (create K) (contract K) σ z a e))
    (ofRaw_le_iff.mpr (minus_restricts T (contract K) (create K) σ z a e)))
  have nth (p : J) := ((marked A (Fin Q) T).group_ne_zero_iff (placeMark σ p)).mpr hT
  simpa only [card_level] using relocation_finite_price_bound φ _ _ _ (nth a) (nth e) (nth z)
    (Level Q (b+1)) (Level Q (b+2)) (Level Q b) a e z u d c hc hd hza hze hclass
end Relocation
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
noncomputable section
open scoped Topology Classical
open Real Filter
namespace SiteTensor
variable {I J : Type} [Fintype I] [Fintype J] [Nonempty J] [DecidableEq I] {K : Type*} [Field K]
theorem rawLogPrice_relocate
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ) (hc : 0 ≤ c)
    (T : Raw.{0} I K) (x : I → J) (i : I) (a z b : J) (u : ℝ) (hu : u ∈ Set.Icc 0 1)
    (hza : rawWireDistance φ c z a = u * rawWireDistance φ c a b)
    (hzb : rawWireDistance φ c z b = (1 - u) * rawWireDistance φ c a b) :
    rawLogPrice φ c (T.group (Function.update x i z)) ≤
      (1 - u) * rawLogPrice φ c (T.group (Function.update x i a)) +
      u * rawLogPrice φ c (T.group (Function.update x i b)) := by
  let w (p : J) := rawLogPrice φ c (T.group (Function.update x i p))
  let d := rawWireDistance φ c a b
  let q := Fintype.card (T.Leg i)
  change w z ≤ (1 - u) * w a + u * w b
  by_cases hT : T.coeff = 0
  · have hw (p : J) : w p = 0 := rawLogPrice_zero φ c _ (funext fun _ => congrFun hT _)
    simp [hw]
  have hm (p r : J) : w p ≤ w r + rawWireDistance φ c p r * logb 2 q := by
    have h := rawLogPrice_move_le φ c hc T hT (Function.update x i r) (Function.update x i p) i
      (fun j hj => by simp [Function.update_of_ne hj])
    simpa only [Function.update_self, rawWireDistance_symm φ c r p] using h
  have ha := hm z a
  have hb := hm z b
  rw [hza] at ha
  rw [hzb] at hb
  change w z ≤ w a + (u * d) * logb 2 q at ha
  change w z ≤ w b + ((1 - u) * d) * logb 2 q at hb
  have hdeg (hdl : d * logb 2 q = 0) : w z ≤ (1 - u) * w a + u * w b := by
    rw [mul_assoc, hdl, mul_zero, add_zero] at ha hb
    linarith only [mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hu.2),
      mul_le_mul_of_nonneg_left hb hu.1]
  by_cases hd : 0 < d
  · by_cases hq : 2 ≤ q
    · apply relocation_le_of_two_bounds (d := d) (q := q) (c := c) hd hq
      · have hab := hm a b
        have hba := hm b a
        rw [rawWireDistance_symm φ c b a] at hba
        exact abs_le.mpr ⟨by dsimp [d]; linarith, by dsimp [d]; linarith⟩
      · intro s hs
        obtain ⟨l, hl, hp, hm⟩ := relocation_level_limits hq hs
        refine ⟨_, _, hp, hm, ?_⟩
        filter_upwards [hl] with n hn
        obtain ⟨S, hS, hw⟩ := Relocation.exists_finPower_update φ c T hT i x n
        have h := Relocation.marked_finite_price_bound φ hn S hS (x ∘ Subtype.val) a z b u d c
          hc rfl hza hzb
        dsimp only [w]
        rw [← hw z, ← hw b, ← hw a]
        exact h
    · have he : q = 0 ∨ q = 1 := by omega
      rcases he with hz | ho <;> apply hdeg <;> simp [*]
  · exact hdeg (by have hz : d = 0 := le_antisymm (le_of_not_gt hd) (rawLogPrice_nonneg φ hc _); rw [hz, zero_mul])
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter Real
open scoped Topology
theorem relocation_width_limit {d B w : ℝ}
    (h : ∀ a : ℕ, d ≤ B + w / (2 : ℝ) ^ a) : d ≤ B := by
  have hw : Tendsto (fun a : ℕ ↦ w / (2 : ℝ) ^ a) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  exact ge_of_tendsto' (by simpa using hw.const_add B) h
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical BigOperators
namespace SiteTensor.Relocation
variable {I J Q H M : Type} {K : Type*} {A : I → Type}
variable [Fintype I] [Fintype J] [∀ i, Fintype (A i)]
variable [Fintype Q] [Fintype H] [Fintype M] [CommSemiring K]
private theorem copy_entry (f : H → K) (z : H) (w : K) :
    w * f z = ∑ m, (w * if m = z then 1 else 0) * f m := by
  simp [mul_ite, ite_mul]
theorem split_restricts_at_column (T : (∀ i, A i) → Q → K)
    (S : (∀ i, A i) → Q → H → H → K) (f : Q → Q → H → H → K)
    (hS : ∀ x i α β, S x i α β = ∑ j, T x j * f i j α β)
    (σ : I → J) (a b : J) :
    ((split A Q H S).group (placeSplit σ a a b)).Restricts
      (((marked A Q T).group (placeMark σ a)).mul (wire K H b a)) := by
  refine restricts_contraction T σ b a _ (fun i x => x ⟨.inl i, rfl⟩)
    (fun x m => if m = x ⟨.inr 2,rfl⟩ then 1 else 0)
    (fun x j m => f (x ⟨.inr 0,rfl⟩) j (x ⟨.inr 1,rfl⟩) m) ?_
  intro x
  refine (hS _ _ _ _).trans ?_
  apply Finset.sum_congr rfl
  intro j _
  exact copy_entry (K := K) (H := H) (fun m => f (x a ⟨.inr 0,rfl⟩) j (x a ⟨.inr 1,rfl⟩) m) _ _
theorem split_restricts_at_row (T : (∀ i, A i) → Q → K)
    (S : (∀ i, A i) → Q → H → H → K) (f : Q → Q → H → H → K)
    (hS : ∀ x i α β, S x i α β = ∑ j, T x j * f i j α β)
    (σ : I → J) (a b : J) :
    ((split A Q H S).group (placeSplit σ b a b)).Restricts
      (((marked A Q T).group (placeMark σ b)).mul (wire K H a b)) := by
  refine restricts_contraction T σ a b _ (fun i x => x ⟨.inl i, rfl⟩)
    (fun x m => if m = x ⟨.inr 1,rfl⟩ then 1 else 0)
    (fun x j m => f (x ⟨.inr 0,rfl⟩) j m (x ⟨.inr 2,rfl⟩)) ?_
  intro x
  refine (hS _ _ _ _).trans ?_
  apply Finset.sum_congr rfl
  intro j _
  exact copy_entry (K := K) (H := H) (fun m => f (x b ⟨.inr 0,rfl⟩) j m (x b ⟨.inr 2,rfl⟩)) _ _
omit [Fintype I] [∀ i, Fintype (A i)] [Fintype H] in
theorem plusCoeff_eq (T : (∀ i, A i) → Q → K) (L : Q → M → H → K) (D : Q → H → M → K)
    (x : ∀ i, A i) (i : Q) (α β : H) :
    plusCoeff T L D x i α β = ∑ j, T x j * ∑ m, L i m α * D j β m := by
  simp only [plusCoeff, Finset.mul_sum, mul_assoc]
omit [Fintype I] [∀ i, Fintype (A i)] [Fintype H] in
theorem minusCoeff_eq (T : (∀ i, A i) → Q → K) (D : Q → M → H → K) (L : Q → H → M → K)
    (x : ∀ i, A i) (i : Q) (α β : H) :
    minusCoeff T D L x i α β = ∑ j, T x j * ∑ m, D j m α * L i β m := by
  simp only [minusCoeff, Finset.mul_sum, mul_assoc]
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace SiteTensor
variable {J : Type} {K : Type*} [Fintype J] [Nonempty J] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) {c : ℝ}
theorem rawLogPrice_mul_le (hc : 0 ≤ c) (X Y : Raw.{0} J K) :
    rawLogPrice φ c (X.mul Y) ≤ rawLogPrice φ c X + rawLogPrice φ c Y := by
  by_cases hx : X.coeff = 0
  · have h : (X.mul Y).coeff = 0 := funext fun x => by
      change X.coeff _ * Y.coeff _ = 0
      rw [hx]; exact zero_mul _
    rw [rawLogPrice_zero φ c _ h, rawLogPrice_zero φ c _ hx, zero_add]
    exact rawLogPrice_nonneg φ hc _
  by_cases hy : Y.coeff = 0
  · have h : (X.mul Y).coeff = 0 := funext fun x => by
      change X.coeff _ * Y.coeff _ = 0
      rw [hy]; exact mul_zero _
    rw [rawLogPrice_zero φ c _ h, rawLogPrice_zero φ c _ hy, add_zero]
    exact rawLogPrice_nonneg φ hc _
  exact (rawLogPrice_mul φ c X Y hx hy).le
namespace Relocation
variable {I Q H M : Type} {A : I → Type}
variable [Fintype I] [∀ i, Fintype (A i)] [Fintype Q] [Fintype H] [Fintype M]
variable [Nonempty H] [Nonempty M]
private theorem price_le_add_wire {D : Type} [Fintype D] [Nonempty D] (hc : 0 ≤ c)
    {X Y : Raw.{0} J K} (p q : J) (h : X.Restricts (Y.mul (wire K D p q))) :
    rawLogPrice φ c X ≤ rawLogPrice φ c Y +
      rawWireDistance φ c p q * Real.logb 2 (Fintype.card D) := by
  have hw : rawLogPrice φ c (wire K D p q) =
      rawWireDistance φ c p q * Real.logb 2 (Fintype.card D) :=
    rawLogPrice_group_diagonal φ ![p,q] c
  exact (rawLogPrice_mono φ hc h).trans ((rawLogPrice_mul_le φ hc Y _).trans_eq (by rw [hw]))
theorem collocated_prices (hc : 0 ≤ c)
    (T : (∀ i, A i) → Q → K) (S : (∀ i, A i) → Q → H → H → K) (f : Q → Q → H → H → K)
    (hS : ∀ x i α β, S x i α β = ∑ j, T x j * f i j α β) (σ : I → J) (a b : J) :
    let child (p : J) := rawLogPrice φ c ((split A Q H S).group (placeSplit σ p a b))
    let parent (p : J) := rawLogPrice φ c ((marked A Q T).group (placeMark σ p))
    let t := rawWireDistance φ c a b
    child a ≤ parent a + t * Real.logb 2 (Fintype.card H) ∧
    child b ≤ parent b + t * Real.logb 2 (Fintype.card H) := by
  refine ⟨?_, price_le_add_wire φ hc a b (split_restricts_at_row T S f hS σ a b)⟩
  have h := price_le_add_wire φ hc b a (split_restricts_at_column T S f hS σ a b)
  rwa [rawWireDistance_symm φ c b a] at h
theorem plus_endpoint_prices (hc : 0 ≤ c) (T : (∀ i, A i) → Q → K)
    (L : Q → M → H → K) (D : Q → H → M → K) (σ : I → J) (a b : J) :
    let child (p : J) := rawLogPrice φ c ((split A Q H (plusCoeff T L D)).group (placeSplit σ p a b))
    let parent (p : J) := rawLogPrice φ c ((marked A Q T).group (placeMark σ p))
    let t := rawWireDistance φ c a b
    child a ≤ parent a + t * Real.logb 2 (Fintype.card H) ∧
    child b ≤ parent b + t * Real.logb 2 (Fintype.card H) ∧
    child a ≤ parent b + t * Real.logb 2 (Fintype.card M) := by
  have h := collocated_prices φ hc T _ _ (plusCoeff_eq T L D) σ a b
  exact ⟨h.1, h.2, price_le_add_wire φ hc a b (plus_restricts_opposite T L D σ a b)⟩
theorem minus_endpoint_prices (hc : 0 ≤ c) (T : (∀ i, A i) → Q → K)
    (D : Q → M → H → K) (L : Q → H → M → K) (σ : I → J) (a b : J) :
    let child (p : J) := rawLogPrice φ c ((split A Q H (minusCoeff T D L)).group (placeSplit σ p a b))
    let parent (p : J) := rawLogPrice φ c ((marked A Q T).group (placeMark σ p))
    let t := rawWireDistance φ c a b
    child a ≤ parent a + t * Real.logb 2 (Fintype.card H) ∧
    child b ≤ parent b + t * Real.logb 2 (Fintype.card H) ∧
    child b ≤ parent a + t * Real.logb 2 (Fintype.card M) := by
  have h := collocated_prices φ hc T _ _ (minusCoeff_eq T D L) σ a b
  refine ⟨h.1, h.2, ?_⟩
  have h' := price_le_add_wire φ hc b a (minus_restricts_opposite T D L σ b a)
  rwa [rawWireDistance_symm φ c b a] at h'
end Relocation
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
noncomputable section
open scoped Classical
namespace SiteTensor.Relocation
open Exterior
variable {I J : Type} {K : Type*} {A : I → Type} [Fintype I] [Fintype J] [Nonempty J] [∀ i, Fintype (A i)] [Field K] {Q b : ℕ}
theorem select_split (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
    {scale : ℝ} (hscale : 0 ≤ scale) (T : (∀ i, A i) → Fin Q → K)
    (hT : (marked A (Fin Q) T).coeff ≠ 0) [Nonempty (Level Q (b + 1))]
    (σ : I → J) (c a d : J) :
    let parent := (marked A (Fin Q) T).group (placeMark σ c)
    let W := wire K (Level Q (b + 1)) a d
    let upper := split A (Fin Q) (Level Q (b + 1)) (plusCoeff T (create K) (contract K))
    let lower := split A (Fin Q) (Level Q (b + 1)) (minusCoeff T (contract K) (create K))
    (upper.coeff ≠ 0 ∧ rawLogPrice φ scale parent + rawLogPrice φ scale W ≤
      rawLogPrice φ scale (upper.group (placeSplit σ c a d)) + scale) ∨
    (lower.coeff ≠ 0 ∧ rawLogPrice φ scale parent + rawLogPrice φ scale W ≤
      rawLogPrice φ scale (lower.group (placeSplit σ c a d)) + scale) := by
  let H := Level Q (b + 1)
  let f := placeSplit σ c a d
  let V (v : (∀ i, A i) → Fin Q → H → H → K) := (split A (Fin Q) H v).group f
  let P := V (fun x i α β => T x i * if α = β then 1 else 0)
  let U := (marked A (Fin Q) T).group (placeMark σ c)
  let W := wire K H a d
  have hw : W.coeff ≠ 0 := by
    apply (Raw.group_ne_zero_iff ..).mpr
    intro h
    have hz := congrFun h (fun _ => Classical.arbitrary H)
    change (Raw.diagonal (Fin 2) K H).coeff (fun _ => Classical.arbitrary H) = 0 at hz
    simp [Raw.diagonal_coeff_at (0 : Fin 2)] at hz
  have hu : U.coeff ≠ 0 := (Raw.group_ne_zero_iff ..).mpr hT
  have hp : ofRaw P = ofRaw U * ofRaw W := grouped_split_eq_mul T H σ c a d
  have hpn : P.coeff ≠ 0 := by
    apply (ofRaw_eq_zero_iff P).not.mp
    rw [hp]
    exact mul_ne_zero ((ofRaw_eq_zero_iff U).not.mpr hu) ((ofRaw_eq_zero_iff W).not.mpr hw)
  have hpprice : rawLogPrice φ scale P = rawLogPrice φ scale U + rawLogPrice φ scale W := by
    rw [← rawLogPrice_mul φ scale U W hu hw]
    simp only [rawLogPrice, ofRaw_mul, hp]
  let s : (∀ j, P.Leg j) → K := (V (plusCoeff T (create K) (contract K))).coeff
  let t : (∀ j, P.Leg j) → K := (V (minusCoeff T (contract K) (create K))).coeff
  have he : P.coeff = s + t := funext fun _ => (plus_add_minus_eq T _ _ _ _).symm
  have hval : rawLogPrice φ scale ⟨P.Leg, inferInstance, s + t⟩ = rawLogPrice φ scale P := by
    rw [← he]
    rfl
  rcases rawLogPrice_add_select φ scale hscale s t (he ▸ hpn) with ⟨hs, hb⟩ | ⟨ht, hb⟩
  · rw [hval, hpprice] at hb
    exact Or.inl ⟨(Raw.group_ne_zero_iff ..).mp hs, hb⟩
  · rw [hval, hpprice] at hb
    exact Or.inr ⟨(Raw.group_ne_zero_iff ..).mp ht, hb⟩
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
abbrev EndpointTable := Fin 2 → Fin 2 → ℝ
namespace EndpointTable
noncomputable section
def bernoulliWeight (u : ℝ) : Fin 2 → ℝ := ![1 - u, u]
def independent (u v : ℝ) : EndpointTable := fun i j ↦ bernoulliWeight u i * bernoulliWeight v j
def cost (w N : EndpointTable) : ℝ := ∑ i, ∑ j, w i j * N i j
structure IsCoupling (w : EndpointTable) (u v : ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ w i j
  row_sum : ∀ i, ∑ j, w i j = bernoulliWeight u i
  col_sum : ∀ j, ∑ i, w i j = bernoulliWeight v j
theorem independent_isCoupling {u v : ℝ} (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    IsCoupling (independent u v) u v := by
  have hnonneg {a : ℝ} (ha : a ∈ Set.Icc 0 1) (i : Fin 2) : 0 ≤ bernoulliWeight a i := by
    fin_cases i
    · exact sub_nonneg.mpr ha.2
    · exact ha.1
  refine ⟨fun i j ↦ mul_nonneg (hnonneg hu i) (hnonneg hv j), ?_, ?_⟩
  · intro i
    change (∑ j, bernoulliWeight u i * bernoulliWeight v j) = _
    rw [← Finset.mul_sum]
    simp [Fin.sum_univ_two, bernoulliWeight]
  · intro j
    change (∑ i, bernoulliWeight u i * bernoulliWeight v j) = _
    rw [← Finset.sum_mul]
    simp [Fin.sum_univ_two, bernoulliWeight]
def synchronized (u : ℝ) : EndpointTable := fun i j ↦ if i = j then bernoulliWeight u i else 0
theorem synchronized_isCoupling {u : ℝ} (hu : u ∈ Set.Icc 0 1) : IsCoupling (synchronized u) u u := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    unfold synchronized
    split_ifs
    · fin_cases i
      · exact sub_nonneg.mpr hu.2
      · exact hu.1
    · rfl
  · intro i
    simp [synchronized]
  · intro j
    simp [synchronized]
theorem cost_synchronized (u : ℝ) (M : EndpointTable) :
    cost (synchronized u) M = (1-u) * M 0 0 + u * M 1 1 := by
  simp [cost, Fin.sum_univ_two, synchronized, bernoulliWeight]
def gap (N : EndpointTable) (j : Fin 2) : ℝ := N 0 j - N 1 j
def width (N : EndpointTable) : ℝ := |gap N 0 - gap N 1|
def midpoint (N : EndpointTable) : ℝ := (gap N 0 + gap N 1) / 2
def plus (N : EndpointTable) : EndpointTable := ![fun j ↦ min (N 0 j) (N 1 j + midpoint N), N 1]
def minus (N : EndpointTable) : EndpointTable := ![N 0, fun j ↦ min (N 1 j) (N 0 j - midpoint N)]
theorem plus_le (N : EndpointTable) : plus N ≤ N := by
  intro i j
  fin_cases i
  · exact min_le_left _ _
  · rfl
theorem minus_le (N : EndpointTable) : minus N ≤ N := by
  intro i j
  fin_cases i
  · rfl
  · exact min_le_left _ _
theorem gap_plus (N : EndpointTable) (j : Fin 2) : gap (plus N) j = min (gap N j) (midpoint N) := by
  change min (N 0 j) (N 1 j + midpoint N) - N 1 j = _
  rw [← min_sub_sub_right, add_sub_cancel_left]
  rfl
theorem gap_minus (N : EndpointTable) (j : Fin 2) : gap (minus N) j = max (gap N j) (midpoint N) := by
  change N 0 j - min (N 1 j) (N 0 j - midpoint N) = _
  rw [← max_sub_sub_left, sub_sub_cancel]
  rfl
private theorem midpoint_width (x y : ℝ) :
    |min x ((x+y)/2) - min y ((x+y)/2)| = |x-y| / 2 ∧
    |max x ((x+y)/2) - max y ((x+y)/2)| = |x-y| / 2 := by
  rcases le_total x y with h | h
  · have hx : x ≤ (x+y)/2 := by linarith
    have hy : (x+y)/2 ≤ y := by linarith
    rw [min_eq_left hx, min_eq_right hy, max_eq_right hx, max_eq_left hy,
      abs_of_nonpos (sub_nonpos.mpr hx), abs_of_nonpos (sub_nonpos.mpr hy),
      abs_of_nonpos (sub_nonpos.mpr h)]
    constructor <;> ring
  · have hx : (x+y)/2 ≤ x := by linarith
    have hy : y ≤ (x+y)/2 := by linarith
    rw [min_eq_right hx, min_eq_left hy, max_eq_left hx, max_eq_right hy,
      abs_of_nonneg (sub_nonneg.mpr hx), abs_of_nonneg (sub_nonneg.mpr hy),
      abs_of_nonneg (sub_nonneg.mpr h)]
    constructor <;> ring
theorem width_plus (N : EndpointTable) : width (plus N) = width N / 2 := by
  simpa only [width, gap_plus, midpoint] using (midpoint_width (gap N 0) (gap N 1)).1
theorem width_minus (N : EndpointTable) : width (minus N) = width N / 2 := by
  simpa only [width, gap_minus, midpoint] using (midpoint_width (gap N 0) (gap N 1)).2
theorem cost_sub_cost {w π : EndpointTable} {u v : ℝ} (hw : IsCoupling w u v)
    (hπ : IsCoupling π u v) (N : EndpointTable) :
    cost w N - cost π N = (w 0 0 - π 0 0) * (gap N 0 - gap N 1) := by
  have hr0 := (hw.row_sum 0).trans (hπ.row_sum 0).symm
  have hr1 := (hw.row_sum 1).trans (hπ.row_sum 1).symm
  have hc0 := (hw.col_sum 0).trans (hπ.col_sum 0).symm
  simp only [Fin.sum_univ_two] at hr0 hr1 hc0
  have h01 : w 0 1 = π 0 1 - (w 0 0 - π 0 0) := by linarith
  have h10 : w 1 0 = π 1 0 - (w 0 0 - π 0 0) := by linarith
  have h11 : w 1 1 = π 1 1 + (w 0 0 - π 0 0) := by linarith
  simp only [cost, Fin.sum_univ_two, gap, h01, h10, h11]
  ring
theorem cost_le_cost_add_width {w π : EndpointTable} {u v : ℝ} (hw : IsCoupling w u v)
    (hπ : IsCoupling π u v) (hu : 0 ≤ u) (N : EndpointTable) :
    cost w N ≤ cost π N + width N := by
  have hbound {p : EndpointTable} (hp : IsCoupling p u v) : p 0 0 ≤ 1 := by
    have h := hp.row_sum 0
    simp [Fin.sum_univ_two, bernoulliWeight] at h
    linarith [hp.nonneg 0 1]
  have ha : |w 0 0 - π 0 0| ≤ 1 := abs_le.mpr
    ⟨by linarith [hw.nonneg 0 0, hbound hπ], by linarith [hπ.nonneg 0 0, hbound hw]⟩
  have h : |cost w N - cost π N| ≤ width N := by
    rw [cost_sub_cost hw hπ, abs_mul]
    exact (mul_le_mul_of_nonneg_right ha (abs_nonneg _)).trans_eq (one_mul _)
  linarith [(abs_le.mp h).2]
theorem cost_mono {π : EndpointTable} {u v : ℝ} (hπ : IsCoupling π u v) {M N : EndpointTable}
    (h : M ≤ N) : cost π M ≤ cost π N :=
  Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
    mul_le_mul_of_nonneg_left (h i j) (hπ.nonneg i j)
theorem cost_independent (u v : ℝ) (N : EndpointTable) :
    cost (independent u v) N =
      (1-u)*(1-v)*N 0 0 + (1-u)*v*N 0 1 + u*(1-v)*N 1 0 + u*v*N 1 1 := by
  simp [Fin.sum_univ_two, cost, independent, bernoulliWeight, add_assoc]
def GapBound (t : ℝ) (N : EndpointTable) : Prop := ∀ j, |gap N j| ≤ t
theorem GapBound.midpoint_le {N : EndpointTable} {t : ℝ} (h : GapBound t N) :
    |midpoint N| ≤ t := by
  have h0 := abs_le.mp (h 0)
  have h1 := abs_le.mp (h 1)
  unfold midpoint
  exact abs_le.mpr ⟨by linarith, by linarith⟩
theorem GapBound.plus {N : EndpointTable} {t : ℝ} (h : GapBound t N) : GapBound t N.plus := by
  intro j
  rw [gap_plus]
  obtain ⟨hlo, hhi⟩ := abs_le.mp (h j)
  exact abs_le.mpr ⟨le_min hlo (abs_le.mp h.midpoint_le).1, (min_le_left _ _).trans hhi⟩
theorem GapBound.minus {N : EndpointTable} {t : ℝ} (h : GapBound t N) : GapBound t N.minus := by
  intro j
  rw [gap_minus]
  obtain ⟨hlo, hhi⟩ := abs_le.mp (h j)
  exact abs_le.mpr ⟨hlo.trans (le_max_left _ _), max_le hhi (abs_le.mp h.midpoint_le).2⟩
def BoundedBy (actual ideal : EndpointTable) (slack : ℝ) : Prop :=
  ∀ i j, actual i j ≤ ideal i j + slack
theorem boundedBy_plus {P N Y : EndpointTable} {σ ε : ℝ} (hP : BoundedBy P N σ)
    (hsame : ∀ i j, Y i j ≤ P i j + ε)
    (hcross : ∀ j, Y 0 j ≤ P 1 j + N.midpoint + ε) : BoundedBy Y N.plus (σ+ε) := by
  intro i j
  fin_cases i
  · change Y 0 j ≤ min (N 0 j) (N 1 j + N.midpoint) + _
    rw [← min_add_add_right]
    exact le_min (by linarith [hP 0 j, hsame 0 j]) (by linarith [hP 1 j, hcross j])
  · change Y 1 j ≤ N 1 j + _
    linarith [hP 1 j, hsame 1 j]
theorem boundedBy_minus {P N Y : EndpointTable} {σ ε : ℝ} (hP : BoundedBy P N σ)
    (hsame : ∀ i j, Y i j ≤ P i j + ε)
    (hcross : ∀ j, Y 1 j ≤ P 0 j - N.midpoint + ε) : BoundedBy Y N.minus (σ+ε) := by
  intro i j
  fin_cases i
  · change Y 0 j ≤ N 0 j + _
    linarith [hP 0 j, hsame 0 j]
  · change Y 1 j ≤ min (N 1 j) (N 0 j - N.midpoint) + _
    rw [← min_add_add_right]
    exact le_min (by linarith [hP 1 j, hsame 1 j]) (by linarith [hP 0 j, hcross j])
theorem IsCoupling.cost_le_of_boundedBy {w N M : EndpointTable} {u v σ : ℝ} (hw : IsCoupling w u v)
    (h : BoundedBy N M σ) : cost w N ≤ cost w M + σ := by
  have ht : (∑ i, ∑ j, w i j) = 1 := by simp [hw.row_sum, Fin.sum_univ_two, bernoulliWeight]
  calc
    cost w N ≤ ∑ i, ∑ j, w i j * (M i j + σ) :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_left (h i j) (hw.nonneg i j)
    _ = cost w M + σ := by simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, ht,
      one_mul, cost]
variable {X : Type*}
theorem selectedPath (endpoint : X → EndpointTable) (interior : X → ℝ)
    {t ε : ℝ} (hε : 0 ≤ ε)
    (step : ∀ x N σ, GapBound t N → 0 ≤ σ → BoundedBy (endpoint x) N σ →
      ∃ (y : X) (C : EndpointTable), (C = N.plus ∨ C = N.minus) ∧
        interior x ≤ interior y + ε ∧ BoundedBy (endpoint y) C (σ+ε))
    (root : X) (M : EndpointTable) (hM : GapBound t M) (hroot : endpoint root ≤ M) (a : ℕ) :
    ∃ y N, GapBound t N ∧ N ≤ M ∧ width N = width M / 2^a ∧
      interior root ≤ interior y + a*ε ∧ BoundedBy (endpoint y) N (a*ε) := by
  induction a with
  | zero =>
    exact ⟨root, M, hM, le_rfl, by simp, by simp,
      fun i j ↦ by simpa using hroot i j⟩
  | succ a ih =>
    obtain ⟨x, N, hN, hNM, hw, hv, hb⟩ := ih
    obtain ⟨y, C, hC, hxy, hy⟩ := step x N (a*ε) hN (by positivity) hb
    have hs : GapBound t C ∧ C ≤ N ∧ C.width = N.width / 2 := by
      rcases hC with rfl | rfl
      · exact ⟨hN.plus, plus_le _, width_plus _⟩
      · exact ⟨hN.minus, minus_le _, width_minus _⟩
    refine ⟨y, C, hs.1, hs.2.1.trans hNM, ?_, ?_, ?_⟩
    · rw [hs.2.2, hw, div_div, pow_succ]
    · push_cast
      linarith
    · simpa [Nat.cast_succ, add_mul] using hy
theorem selectedPath_coupling_bound (endpoint : X → EndpointTable) (interior : X → ℝ)
    {t ε u v : ℝ} (hε : 0 ≤ ε) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (π : EndpointTable) (hπ : IsCoupling π u v)
    (hinter : ∀ y, interior y ≤ cost (independent u v) (endpoint y))
    (step : ∀ x N σ, GapBound t N → 0 ≤ σ → BoundedBy (endpoint x) N σ →
      ∃ (y : X) (C : EndpointTable), (C = N.plus ∨ C = N.minus) ∧
        interior x ≤ interior y + ε ∧ BoundedBy (endpoint y) C (σ+ε))
    (root : X) (M : EndpointTable) (hM : GapBound t M) (hroot : endpoint root ≤ M) (a : ℕ) :
    interior root ≤ cost π M + width M / 2^a + 2*a*ε := by
  obtain ⟨y, N, _, hNM, hw, hroot', hy⟩ := selectedPath endpoint interior hε step root M hM hroot a
  have hind := independent_isCoupling hu hv
  linarith [hinter y, hind.cost_le_of_boundedBy hy, cost_le_cost_add_width hind hπ hu.1 N,
    cost_mono hπ hNM]
end
end EndpointTable
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace EndpointTable
open Filter
open scoped Topology
theorem gapBound_of_triangle {X : Type*} (d : X → X → ℝ)
    (symm : ∀ x y, d x y = d y x) (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (A B : Fin 2 → X) : GapBound (d (A 0) (A 1)) (fun i j ↦ d (A i) (B j)) := by
  intro j
  change |d (A 0) (B j) - d (A 1) (B j)| ≤ d (A 0) (A 1)
  exact abs_le.mpr ⟨by linarith [triangle (A 1) (A 0) (B j), symm (A 0) (A 1)],
    by linarith [triangle (A 0) (A 1) (B j)]⟩
private theorem gap_smul (k : ℝ) (M : EndpointTable) (j : Fin 2) :
    gap (k • M) j = k * gap M j := by simp [gap, mul_sub]
private theorem width_smul {k : ℝ} (hk : 0 ≤ k) (M : EndpointTable) :
    width (k • M) = k * width M := by simp [width, gap_smul, ← mul_sub, abs_mul, abs_of_nonneg hk]
private theorem cost_smul (w M : EndpointTable) (k : ℝ) : cost w (k • M) = k * cost w M := by
  simp only [cost, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr! 2 with i _ j
  ring
private theorem gapBound_smul {t k : ℝ} {M : EndpointTable} (h : GapBound t M) (hk : 0 ≤ k) :
    GapBound (k*t) (k • M) := by
  intro j
  rw [gap_smul, abs_mul, abs_of_nonneg hk]
  exact mul_le_mul_of_nonneg_left (h j) hk
def HasSplit {X : Type*} (endpoint : X → EndpointTable) (interior : X → ℝ) (t e : ℝ) : Prop :=
  ∀ x c, |c| ≤ t → ∃ y, interior x ≤ interior y + e ∧ endpoint y ≤ endpoint x ∧
    ((∀ j, endpoint y 0 j ≤ endpoint x 1 j + c + e) ∨
     (∀ j, endpoint y 1 j ≤ endpoint x 0 j - c + e))
theorem HasSplit.finite_coupling_bound {X : Type*} {endpoint : X → EndpointTable} {interior : X → ℝ}
    {t e u v : ℝ} (split : HasSplit endpoint interior t e) (he : 0 ≤ e)
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) {π : EndpointTable} (hπ : IsCoupling π u v)
    (hind : ∀ x, interior x ≤ cost (independent u v) (endpoint x))
    (root : X) (M : EndpointTable) (hM : GapBound t M) (hroot : endpoint root ≤ M) (a : ℕ) :
    interior root ≤ cost π M + width M / 2^a + 2*a*e := by
  apply selectedPath_coupling_bound endpoint interior he hu hv π hπ hind _ root M hM hroot a
  intro x N σ hN _ hactual
  obtain ⟨y, hy, hweak, hstrong⟩ := split x N.midpoint hN.midpoint_le
  have hs (i j) : endpoint y i j ≤ endpoint x i j + e :=
    (hweak i j).trans (le_add_of_nonneg_right he)
  rcases hstrong with hp | hm
  · exact ⟨y, N.plus, Or.inl rfl, hy, boundedBy_plus hactual hs hp⟩
  · exact ⟨y, N.minus, Or.inr rfl, hy, boundedBy_minus hactual hs hm⟩
theorem coupling_of_exterior_splits {X : ℕ → Type*} (endpoint : ∀ n, X n → EndpointTable)
    (interior : ∀ n, X n → ℝ) {t e u v d : ℝ} (he : 0 ≤ e)
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) {π : EndpointTable} (hπ : IsCoupling π u v)
    (M : EndpointTable) (hM : GapBound t M)
    (split : ∀ n : ℕ, 1 ≤ n → HasSplit (endpoint n) (interior n) (n*t) e)
    (hind : ∀ n : ℕ, 1 ≤ n → ∀ x, interior n x ≤ cost (independent u v) (endpoint n x))
    (hroot : ∀ n : ℕ, 1 ≤ n → ∃ x, n*d ≤ interior n x ∧ endpoint n x ≤ (n : ℝ) • M) :
    d ≤ cost π M := by
  apply relocation_width_limit (w := width M)
  intro a
  have herr : Tendsto (fun n : ℕ ↦ 2*(a:ℝ)*e/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply ge_of_tendsto (by simpa using herr.const_add (cost π M + width M / 2^a))
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  obtain ⟨x, hx, htab⟩ := hroot n hn
  have h := hx.trans ((split n hn).finite_coupling_bound he hu hv hπ (hind n hn) x _
    (gapBound_smul hM hn'.le) htab a)
  rw [cost_smul, width_smul hn'.le] at h
  have h' : (n:ℝ) * (d - (cost π M + width M / 2^a)) ≤ 2*a*e := by
    rw [mul_sub, mul_add, ← mul_div_assoc]
    linarith only [h]
  have h'' : d - (cost π M + width M / 2^a) ≤ 2*(a:ℝ)*e/n :=
    (le_div_iff₀ hn').mpr (by simpa [mul_comm] using h')
  linarith only [h'']
end EndpointTable
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical
namespace SiteTensor.Relocation
structure WireNode (K : Type*) [Field K] (J : Type) (Q : ℕ) where
  I : Type
  [finiteI : Fintype I]
  A : I → Type
  [finiteA : ∀ i, Fintype (A i)]
  other : I
  site : I → J
  T : (∀ i, A i) → Fin Q → K
  nonzero : (marked A (Fin Q) T).coeff ≠ 0
  offset : ℝ
instance instWireNodeFiniteI {K : Type*} [Field K] {J : Type} {Q : ℕ} (N : WireNode K J Q) : Fintype N.I := N.finiteI
instance instWireNodeFiniteA {K : Type*} [Field K] {J : Type} {Q : ℕ} (N : WireNode K J Q) (i : N.I) : Fintype (N.A i) := N.finiteA i
namespace WireNode
variable {K : Type*} [Field K] {J : Type} [Fintype J] [Nonempty J] {Q : ℕ}
def cost (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)
    (N : WireNode K J Q) (p v : J) : ℝ :=
  rawLogPrice φ c ((marked N.A (Fin Q) N.T).group
    (placeMark (Function.update N.site N.other v) p)) - N.offset
end WireNode
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
noncomputable section
open scoped Classical
namespace SiteTensor.Relocation
namespace WireNode
variable {K : Type*} [Field K] {J : Type} [Fintype J] [Nonempty J] {Q : ℕ}
def child {H : Type} [Fintype H] (N : WireNode K J Q)
    (S : (∀ i, N.A i) → Fin Q → H → H → K)
    (hS : (split N.A (Fin Q) H S).coeff ≠ 0) (a b : J) (loss : ℝ) :
    WireNode K J Q := by
  let W := split N.A (Fin Q) H S
  let m : N.I ⊕ Fin 3 := .inr 0
  let σ := placeSplit N.site a a b
  let A' := fun i : {i : N.I ⊕ Fin 3 // i ≠ m} => W.Leg i.1
  let S' := markCoeff W m
  refine { I := {i : N.I ⊕ Fin 3 // i ≠ m}, A := A', other := ⟨.inl N.other, by simp [m]⟩,
           site := σ ∘ Subtype.val, T := S', nonzero := ?_, offset := N.offset + loss }
  exact marked_ne_zero W m hS
theorem cost_child {H : Type} [Fintype H]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)
    (N : WireNode K J Q) (S : (∀ i, N.A i) → Fin Q → H → H → K)
    (hS : (split N.A (Fin Q) H S).coeff ≠ 0) (a b : J) (loss : ℝ) (p v : J) :
    cost φ c (N.child S hS a b loss) p v =
      rawLogPrice φ c ((split N.A (Fin Q) H S).group
        (placeSplit (Function.update N.site N.other v) p a b)) - (N.offset + loss) := by
  classical
  let W := split N.A (Fin Q) H S
  let m : N.I ⊕ Fin 3 := .inr 0
  let σ := placeSplit (Function.update N.site N.other v) p a b
  have hp : Function.update σ m p = σ := by
    apply Function.update_eq_self_iff.mpr
    rfl
  have h := rawLogPrice_update_eq_mark φ c W m σ p
  rw [hp] at h
  unfold cost
  apply congrArg (· - (N.offset + loss))
  refine Eq.trans ?_ h.symm
  apply congrArg (fun s => rawLogPrice φ c ((marked _ _ (markCoeff W m)).group (placeMark s p)))
  let o : {i : N.I ⊕ Fin 3 // i ≠ m} := ⟨.inl N.other, by simp [m]⟩
  let : DecidableEq {i : N.I ⊕ Fin 3 // i ≠ m} := fun _ _ => Classical.propDecidable _
  change Function.update (placeSplit N.site a a b ∘ Subtype.val) o v = σ ∘ Subtype.val
  funext i
  rcases i with ⟨i | k, hi⟩
  · by_cases he : i = N.other
    · subst i
      change Function.update (placeSplit N.site a a b ∘ Subtype.val) o v o = Function.update N.site N.other v N.other
      simp
    · have hne : (⟨Sum.inl i, hi⟩ : {i : N.I ⊕ Fin 3 // i ≠ m}) ≠ o :=
        fun h => he (Sum.inl.inj (congrArg Subtype.val h))
      rw [Function.update_of_ne hne]
      exact (Function.update_of_ne he _ _).symm
  · have hne : (⟨Sum.inr k, hi⟩ : {i : N.I ⊕ Fin 3 // i ≠ m}) ≠ o := by
      intro h
      have hv := congrArg Subtype.val h
      cases hv
    rw [Function.update_of_ne hne]
    fin_cases k
    · exact (hi rfl).elim
    all_goals rfl
end WireNode
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
noncomputable section
open scoped Classical
namespace SiteTensor.Relocation.WireNode
open Exterior
variable {K : Type*} [Field K] {J : Type} [Fintype J] [Nonempty J]
private theorem sub_wire_offset {x y h o : ℝ} (hx : x ≤ y + h) :
    x - (o + h) ≤ y - o := by linarith
theorem hasSplit (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
    (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (hn : 1 ≤ n) (A B : Fin 2 → J) (z w : J) :
    EndpointTable.HasSplit (fun (N : WireNode K J (2^n)) i j => cost φ c N (A i) (B j))
      (fun N => cost φ c N z w) (n * rawWireDistance φ c (A 0) (A 1)) c := by
  intro N s hs
  let t := rawWireDistance φ c (A 0) (A 1)
  have ht : 0 ≤ t := rawLogPrice_nonneg φ hc _
  obtain ⟨b, hb, hplus, hminus⟩ := relocation_level_bounds_for_threshold hn ht hs
  let Q := 2^n
  let σ (v : J) := Function.update N.site N.other v
  let H := Level Q (b + 1)
  have ex (k : ℕ) (hk : k ≤ Q) : Nonempty (Level Q k) := by
    apply Fintype.card_pos_iff.mp
    rw [card_level]
    exact Nat.choose_pos hk
  let : Nonempty (Level Q b) := ex b (by dsimp [Q]; omega)
  let : Nonempty (Level Q (b + 1)) := ex (b+1) (by dsimp [Q]; omega)
  let : Nonempty (Level Q (b + 2)) := ex (b+2) hb
  let loss := t * Real.logb 2 (Fintype.card H)
  have wire_eq : rawLogPrice φ c (wire K H (A 0) (A 1)) = loss :=
    rawLogPrice_group_diagonal φ ![A 0,A 1] c
  let U := plusCoeff N.T (create K) (contract K) (H := H)
  let V := minusCoeff N.T (contract K) (create K) (H := H)
  have up (j : Fin 2) := plus_endpoint_prices φ hc N.T (create (b := b+1) K) (contract K)
    (σ (B j)) (A 0) (A 1)
  have down (j : Fin 2) := minus_endpoint_prices φ hc N.T (contract (b := b) K) (create K)
    (σ (B j)) (A 0) (A 1)
  have hp : t * Real.logb 2 (Fintype.card (Level Q (b+2))) - loss ≤ s := by
    simpa only [loss, H, card_level, ← mul_sub] using hplus
  have hm : t * Real.logb 2 (Fintype.card (Level Q b)) - loss ≤ -s := by
    simpa only [loss, H, card_level, ← mul_sub] using hminus
  have selected := select_split (b := b) φ hc N.T N.nonzero (σ w) z (A 0) (A 1)
  rcases selected with ⟨hne, hcost⟩ | ⟨hne, hcost⟩
  · refine ⟨N.child U hne (A 0) (A 1) loss, ?_, ?_, Or.inl ?_⟩
    · simp only [cost_child]
      change rawLogPrice φ c ((marked N.A (Fin Q) N.T).group (placeMark (σ w) z)) - N.offset ≤ _
      rw [wire_eq] at hcost
      linarith only [hcost]
    · intro i j
      simp only [cost_child]
      fin_cases i
      · have h := (up j).1
        change _ ≤ _ + loss at h
        exact sub_wire_offset h
      · have h := (up j).2.1
        change _ ≤ _ + loss at h
        exact sub_wire_offset h
    · intro j
      simp only [cost_child]
      have h := (up j).2.2
      unfold cost
      linarith only [h, hp, hc]
  · refine ⟨N.child V hne (A 0) (A 1) loss, ?_, ?_, Or.inr ?_⟩
    · simp only [cost_child]
      change rawLogPrice φ c ((marked N.A (Fin Q) N.T).group (placeMark (σ w) z)) - N.offset ≤ _
      rw [wire_eq] at hcost
      linarith only [hcost]
    · intro i j
      simp only [cost_child]
      fin_cases i
      · have h := (down j).1
        change _ ≤ _ + loss at h
        exact sub_wire_offset h
      · have h := (down j).2.1
        change _ ≤ _ + loss at h
        exact sub_wire_offset h
    · intro j
      simp only [cost_child]
      have h := (down j).2.2
      unfold cost
      linarith only [h, hm, hc]
end SiteTensor.Relocation.WireNode
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
noncomputable section
namespace SiteTensor.Relocation.WireNode
open Function
variable {K : Type*} [Field K] {J : Type} [Fintype J] [Nonempty J] {Q : ℕ}
theorem independent (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
    (c : ℝ) (hc : 0 ≤ c) (N : WireNode K J Q) (A B : Fin 2 → J) (z w : J)
    (u v : ℝ) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (hz₀ : rawWireDistance φ c (A 0) z = u * rawWireDistance φ c (A 0) (A 1))
    (hz₁ : rawWireDistance φ c z (A 1) = (1-u) * rawWireDistance φ c (A 0) (A 1))
    (hw₀ : rawWireDistance φ c (B 0) w = v * rawWireDistance φ c (B 0) (B 1))
    (hw₁ : rawWireDistance φ c w (B 1) = (1-v) * rawWireDistance φ c (B 0) (B 1)) :
    cost φ c N z w ≤ EndpointTable.cost (EndpointTable.independent u v)
      (fun i j ↦ cost φ c N (A i) (B j)) := by
  classical
  let T := marked N.A (Fin Q) N.T
  let site p y := placeMark (update N.site N.other y) p
  have row (p y k : J) : update (site p y) (.inr ()) k = site k y := by
    funext j
    rcases j with j | ⟨⟩
    · exact update_of_ne (by simp) _ _
    · exact update_self ..
  have col (p y k : J) : update (site p y) (.inl N.other) k = site p k := by
    funext j
    rcases j with j | ⟨⟩
    · by_cases hj : j = N.other
      · subst j
        rw [update_self]
        exact (update_self N.other k N.site).symm
      · rw [update_of_ne (fun h ↦ hj (Sum.inl.inj h))]
        change update N.site N.other y j = update N.site N.other k j
        rw [update_of_ne hj, update_of_ne hj]
    · exact update_of_ne (by simp) _ _
  rw [EndpointTable.cost_independent]
  apply independent_relocation_two (cost φ c N) _ _ _ _ _ _ hu
  · intro y
    have h := rawLogPrice_relocate φ c hc T (site z y) (.inr ()) (A 0) z (A 1) u hu
      ((rawWireDistance_symm φ c z (A 0)).trans hz₀) hz₁
    simp only [row] at h
    change rawLogPrice φ c (T.group (site z y)) - N.offset ≤
      (1-u) * (rawLogPrice φ c (T.group (site (A 0) y)) - N.offset) +
      u * (rawLogPrice φ c (T.group (site (A 1) y)) - N.offset)
    linarith only [h]
  · intro p
    have h := rawLogPrice_relocate φ c hc T (site p w) (.inl N.other) (B 0) w (B 1) v hv
      ((rawWireDistance_symm φ c w (B 0)).trans hw₀) hw₁
    simp only [col] at h
    change rawLogPrice φ c (T.group (site p w)) - N.offset ≤
      (1-v) * (rawLogPrice φ c (T.group (site p (B 0))) - N.offset) +
      v * (rawLogPrice φ c (T.group (site p (B 1))) - N.offset)
    linarith only [h]
end SiteTensor.Relocation.WireNode
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
noncomputable section
open scoped Classical
namespace SiteTensor.Relocation.WireNode
variable {K : Type*} [Field K] {J : Type}
def root (base : J) (n : ℕ) : WireNode K J (2^n) := by
  let W := Raw.diagonal (Fin 2) K (Fin (2^n))
  let i : Fin 2 := 0
  refine ⟨{j : Fin 2 // j ≠ i}, fun j => W.Leg j.1,
    ⟨1, by decide⟩, fun _ => base, markCoeff W i, ?_, 0⟩
  intro hz
  have hW : ofRaw W = 0 := (ofRaw_eq_iff.mpr (marked_group_equivalent W i)).symm.trans
    ((ofRaw_eq_zero_iff _).mpr (funext fun x => congrFun hz (fun k => x ((placeMark Subtype.val i) k) ⟨k, rfl⟩)))
  let label : Fin (2^n) := ⟨0, pow_pos (by decide) _⟩
  have h := congrFun ((ofRaw_eq_zero_iff W).mp hW) (fun _ => label)
  change (Raw.diagonal (Fin 2) K (Fin (2^n))).coeff (fun _ => label) = 0 at h
  simp [Raw.diagonal_coeff_at i] at h
variable [Fintype J] [Nonempty J]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
theorem cost_root (c : ℝ) (base : J) (n : ℕ) (p q : J) :
    cost φ c (root base n) p q = n * rawWireDistance φ c p q := by
  let W := Raw.diagonal (Fin 2) K (Fin (2^n))
  let σ : Fin 2 → J := ![p,q]
  have hup : Function.update σ 0 p = σ := Function.update_eq_self_iff.mpr rfl
  have hg := rawLogPrice_update_eq_mark φ c W 0 σ p
  rw [hup] at hg
  let : DecidableEq {j : Fin 2 // j ≠ 0} := fun _ _ => Classical.propDecidable _
  have hb : Function.update (fun _ : {j : Fin 2 // j ≠ 0} => base) ⟨1, by decide⟩ q =
      σ ∘ Subtype.val := by
    funext j
    obtain ⟨j, hj⟩ := j
    fin_cases j
    · exact (hj rfl).elim
    · exact Function.update_self ..
  unfold cost root
  dsimp only
  rw [sub_zero]
  erw [hb, ← hg]
  have : Nonempty (Fin (2^n)) := ⟨⟨0, pow_pos (by decide) _⟩⟩
  rw [rawLogPrice_group_diagonal φ σ c]
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  exact mul_comm _ _
end SiteTensor.Relocation.WireNode
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
namespace SiteTensor
open Relocation
variable {J : Type} [Fintype J] [Nonempty J] {K : Type*} [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)
theorem rawWireDistance_coupling (hc : 0 ≤ c) (A B : Fin 2 → J) (z w : J) (u v : ℝ)
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (hz₀ : rawWireDistance φ c (A 0) z = u * rawWireDistance φ c (A 0) (A 1))
    (hz₁ : rawWireDistance φ c z (A 1) = (1-u) * rawWireDistance φ c (A 0) (A 1))
    (hw₀ : rawWireDistance φ c (B 0) w = v * rawWireDistance φ c (B 0) (B 1))
    (hw₁ : rawWireDistance φ c w (B 1) = (1-v) * rawWireDistance φ c (B 0) (B 1))
    (π : EndpointTable) (hπ : EndpointTable.IsCoupling π u v) :
    rawWireDistance φ c z w ≤ EndpointTable.cost π (fun i j ↦ rawWireDistance φ c (A i) (B j)) := by
  let M : EndpointTable := fun i j ↦ rawWireDistance φ c (A i) (B j)
  let endpoint (n : ℕ) (N : WireNode K J (2^n)) : EndpointTable :=
    fun i j ↦ WireNode.cost φ c N (A i) (B j)
  let interior (n : ℕ) (N : WireNode K J (2^n)) := WireNode.cost φ c N z w
  apply EndpointTable.coupling_of_exterior_splits endpoint interior hc hu hv hπ M
    (EndpointTable.gapBound_of_triangle (rawWireDistance φ c) (rawWireDistance_symm φ c)
      (rawWireDistance_triangle φ c hc) A B)
  · intro n hn
    exact WireNode.hasSplit φ c hc n hn A B z w
  · intro n hn N
    exact WireNode.independent φ c hc N A B z w u v hu hv hz₀ hz₁ hw₀ hw₁
  · intro n hn
    refine ⟨WireNode.root (K := K) z n, ?_, ?_⟩
    · exact (WireNode.cost_root φ c z n z w).ge
    · intro i j
      exact (WireNode.cost_root φ c z n (A i) (B j)).le
theorem rawWireDistance_synchronized (hc : 0 ≤ c) (a b a' b' z w : J) (u : ℝ)
    (hu : u ∈ Set.Icc 0 1)
    (hz₀ : rawWireDistance φ c a z = u * rawWireDistance φ c a b)
    (hz₁ : rawWireDistance φ c z b = (1-u) * rawWireDistance φ c a b)
    (hw₀ : rawWireDistance φ c a' w = u * rawWireDistance φ c a' b')
    (hw₁ : rawWireDistance φ c w b' = (1-u) * rawWireDistance φ c a' b') :
    rawWireDistance φ c z w ≤ (1-u) * rawWireDistance φ c a a' + u * rawWireDistance φ c b b' := by
  simpa [EndpointTable.cost_synchronized] using rawWireDistance_coupling φ c hc
    ![a,b] ![a',b'] z w u u hu hu hz₀ hz₁ hw₀ hw₁ _ (EndpointTable.synchronized_isCoupling hu)
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open Finset
open scoped BigOperators
abbrev FockState (N : ℕ) := ↥((range N).powerset)
def FockState.insert {N : ℕ} (S : FockState N) (r : Fin N) : FockState N :=
  ⟨Insert.insert r.val S.val, mem_powerset.mpr <|
    insert_subset (mem_range.mpr r.isLt) (mem_powerset.mp S.property)⟩
variable (K : Type*) [CommRing K] {N : ℕ}
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OMAPort

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

abbrev T (I : Type) := Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ

section
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Reading one coordinate at each site against Kronecker deltas. -/
theorem sum_read {A : I → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (F : (∀ i, A i) → ℂ) (g : ∀ i, A i) :
    ∑ z, F z * ∏ i, (if g i = z i then (1 : ℂ) else 0) = F g := by
  classical
  rw [Finset.sum_eq_single g]
  · simp
  · intro b _ hb
    obtain ⟨i, hi⟩ : ∃ i, g i ≠ b i := by
      by_contra h
      push Not at h
      exact hb (funext fun i => (h i).symm)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), mul_zero]
  · simp

variable (Φ : T I → ℝ)
variable (hmono : ∀ X Y : T I,
        (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X)
include hmono

/-- Reading coordinates through maps: the smaller tensor is a restriction. -/
theorem read_le {X S : T I} (g : ∀ i, Fin (X.1 i) → Fin (S.1 i))
    (h : ∀ x, X.2 x = S.2 (fun i => g i (x i))) : Φ X ≤ Φ S := by
  apply hmono S X
  refine ⟨fun i p q => if g i p = q then 1 else 0, fun y => ?_⟩
  rw [h y, ← sum_read S.2 (fun i => g i (y i))]
  exact Finset.sum_congr rfl fun z _ => mul_comm _ _

/-- The coordinate presentation of a raw tensor. -/
noncomputable def toSig (X : Raw.{0} I ℂ) : T I :=
  ⟨fun i => Fintype.card (X.Leg i), fun z => X.coeff (fun i => (Fintype.equivFin (X.Leg i)).symm (z i))⟩

omit hmono [Fintype I] [DecidableEq I] in
@[simp] theorem toSig_snd (X : Raw.{0} I ℂ) (z) :
    (toSig X).2 z = X.coeff (fun i => (Fintype.equivFin (X.Leg i)).symm (z i)) := rfl

theorem raw_read_le {X : Raw.{0} I ℂ} {S : T I} (g : ∀ i, X.Leg i → Fin (S.1 i))
    (h : ∀ x, X.coeff x = S.2 (fun i => g i (x i))) : Φ (toSig X) ≤ Φ S :=
  read_le Φ hmono (X := toSig X) (fun i p => g i ((Fintype.equivFin (X.Leg i)).symm p))
    (fun x => h _)

theorem read_raw_le {X : Raw.{0} I ℂ} {S : T I} (g : ∀ i, Fin (S.1 i) → X.Leg i)
    (h : ∀ z, S.2 z = X.coeff (fun i => g i (z i))) : Φ S ≤ Φ (toSig X) :=
  read_le Φ hmono (X := S) (S := toSig X) (fun i p => Fintype.equivFin (X.Leg i) (g i p))
    (fun z => by rw [h z]; show _ = X.coeff _; simp)

theorem raw_eq {X : Raw.{0} I ℂ} {S : T I} (e : ∀ i, X.Leg i ≃ Fin (S.1 i))
    (h : ∀ x, X.coeff x = S.2 (fun i => e i (x i))) : Φ (toSig X) = Φ S :=
  le_antisymm (raw_read_le Φ hmono (fun i => e i) h)
    (read_raw_le Φ hmono (fun i => (e i).symm) fun z => by simp [h])

theorem raw_mono {X Y : Raw.{0} I ℂ} (h : X.Restricts Y) : Φ (toSig X) ≤ Φ (toSig Y) := by
  obtain ⟨M, hM⟩ := h
  apply hmono (toSig Y) (toSig X)
  refine ⟨fun i p q => M i ((Fintype.equivFin _).symm p) ((Fintype.equivFin _).symm q),
    fun y => ?_⟩
  simp only [toSig_snd]
  rw [hM]
  have key := Fintype.sum_equiv (Equiv.piCongrRight fun i => (Fintype.equivFin (Y.Leg i))).symm
    (fun z => (∏ i, M i ((Fintype.equivFin (X.Leg i)).symm (y i))
      ((Fintype.equivFin (Y.Leg i)).symm (z i))) *
        Y.coeff (fun i => (Fintype.equivFin (Y.Leg i)).symm (z i)))
    (fun a => Y.coeff a * ∏ i, M i ((Fintype.equivFin (X.Leg i)).symm (y i)) (a i))
    (fun z => by rw [mul_comm]; rfl)
  refine Eq.trans ?_ (Eq.trans key.symm ?_)
  · convert rfl
  · rfl

end


section ops
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The coordinate direct sum, as in the target statement. -/
def sigAdd (X Y : T I) : T I :=
  ⟨fun i => X.1 i + Y.1 i, fun z =>
          if h : ∀ i, (z i : ℕ) < X.1 i then X.2 (fun i => ⟨z i, h i⟩)
          else if h' : ∀ i, X.1 i ≤ z i then
            Y.2 (fun i => ⟨z i - X.1 i, by have h2 : (z i : ℕ) < X.1 i + Y.1 i := (z i).2; have := h' i; omega⟩)
          else 0⟩

/-- The coordinate tensor product, as in the target statement. -/
def sigMul (X Y : T I) : T I :=
  ⟨fun i => X.1 i * Y.1 i, fun z => X.2 (fun i => (finProdFinEquiv.symm (z i)).1) *
          Y.2 (fun i => (finProdFinEquiv.symm (z i)).2)⟩

/-- The one-bit partial diagonal on `S`, as in the target statement. -/
def maskSig (S : Finset I) : T I :=
  ⟨fun i => if i ∈ S then 2 else 1,
          fun z => if ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j then 1 else 0⟩

noncomputable def addEquiv (X Y : Raw.{0} I ℂ) (i : I) :
    X.Leg i ⊕ Y.Leg i ≃ Fin (Fintype.card (X.Leg i) + Fintype.card (Y.Leg i)) :=
  (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _)).trans finSumFinEquiv

noncomputable def mulEquiv (X Y : Raw.{0} I ℂ) (i : I) :
    X.Leg i × Y.Leg i ≃ Fin (Fintype.card (X.Leg i) * Fintype.card (Y.Leg i)) :=
  (Equiv.prodCongr (Fintype.equivFin _) (Fintype.equivFin _)).trans finProdFinEquiv

theorem mulEquiv_symm (X Y : Raw.{0} I ℂ) (i : I) (p : X.Leg i × Y.Leg i) :
    finProdFinEquiv.symm (mulEquiv X Y i p) =
      (Fintype.equivFin _ p.1, Fintype.equivFin _ p.2) := by
  rw [mulEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]; rfl

theorem addEquiv_inl (X Y : Raw.{0} I ℂ) (i : I) (a : X.Leg i) :
    ((addEquiv X Y i (Sum.inl a) : Fin _) : ℕ) = (Fintype.equivFin _ a : ℕ) := by
  rw [addEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left, Fin.coe_castAdd]

theorem addEquiv_inr (X Y : Raw.{0} I ℂ) (i : I) (b : Y.Leg i) :
    ((addEquiv X Y i (Sum.inr b) : Fin _) : ℕ) = Fintype.card (X.Leg i) + (Fintype.equivFin _ b : ℕ) := by
  rw [addEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right, Fin.coe_natAdd]

theorem mul_coeff (X Y : Raw.{0} I ℂ) (x : ∀ i, X.Leg i × Y.Leg i) :
    (X.mul Y).coeff x = (sigMul (toSig X) (toSig Y)).2 (fun i => mulEquiv X Y i (x i)) := by
  dsimp only [sigMul, toSig, Raw.mul]
  simp only [mulEquiv_symm, Equiv.symm_apply_apply]

theorem add_coeff [Nonempty I] (X Y : Raw.{0} I ℂ) (x : ∀ i, X.Leg i ⊕ Y.Leg i) :
    (X.add Y).coeff x = (sigAdd (toSig X) (toSig Y)).2 (fun i => addEquiv X Y i (x i)) := by
  classical
  show sumCoeff X.coeff Y.coeff x = _
  dsimp only [sigAdd, toSig]
  by_cases hL : ∀ i, ∃ a, x i = Sum.inl a
  · choose a ha using hL
    obtain rfl : x = fun i => Sum.inl (a i) := funext ha
    rw [sumCoeff_inl]
    have hlt : ∀ i, ((addEquiv X Y i (Sum.inl (a i)) : Fin _) : ℕ) < Fintype.card (X.Leg i) := by
      intro i; rw [addEquiv_inl]; exact (Fintype.equivFin _ (a i)).isLt
    rw [dif_pos hlt]
    congr 1
    funext i
    apply (Fintype.equivFin _).injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext (addEquiv_inl X Y i (a i)).symm
  · by_cases hR : ∀ i, ∃ b, x i = Sum.inr b
    · choose b hb using hR
      obtain rfl : x = fun i => Sum.inr (b i) := funext hb
      rw [sumCoeff_inr]
      obtain ⟨i₀⟩ := ‹Nonempty I›
      have hnlt : ¬ ∀ i, ((addEquiv X Y i (Sum.inr (b i)) : Fin _) : ℕ) < Fintype.card (X.Leg i) := by
        intro h; have := h i₀; rw [addEquiv_inr] at this
        omega
      have hge : ∀ i, Fintype.card (X.Leg i) ≤ ((addEquiv X Y i (Sum.inr (b i)) : Fin _) : ℕ) := by
        intro i; rw [addEquiv_inr]; exact Nat.le_add_right _ _
      rw [dif_neg hnlt, dif_pos hge]
      congr 1
      funext i
      apply (Fintype.equivFin _).injective
      rw [Equiv.apply_symm_apply]
      apply Fin.ext
      simp only [addEquiv_inr]
      omega
    · push Not at hL hR
      obtain ⟨i, hi⟩ := hL
      obtain ⟨j, hj⟩ := hR
      rw [sumCoeff_mixed]
      · obtain ⟨b, hb⟩ : ∃ b, x i = Sum.inr b := by
          rcases h : x i with a | b
          · exact absurd h (hi a)
          · exact ⟨b, rfl⟩
        obtain ⟨a, ha⟩ : ∃ a, x j = Sum.inl a := by
          rcases h : x j with a | b
          · exact ⟨a, rfl⟩
          · exact absurd h (hj b)
        have h1 : ¬ ∀ k, ((addEquiv X Y k (x k) : Fin _) : ℕ) < Fintype.card (X.Leg k) := by
          intro h; have := h i; rw [hb, addEquiv_inr] at this
          omega
        have h2 : ¬ ∀ k, Fintype.card (X.Leg k) ≤ ((addEquiv X Y k (x k) : Fin _) : ℕ) := by
          intro h; have := h j; rw [ha, addEquiv_inl] at this
          have := (Fintype.equivFin _ a).isLt
          omega
        rw [dif_neg h1, dif_neg h2]
      · intro a h; exact hi (a i) (congrFun h i).symm
      · intro b h; exact hj (b j) (congrFun h j).symm

end ops


section mask
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Reading a mask leg as a coordinate. -/
def maskTo (S : Finset I) (i : I) (f : MaskLeg S (Fin 2) i) : Fin (if i ∈ S then 2 else 1) :=
  ⟨if h : i ∈ S then (f h : ℕ) else 0, by
    split_ifs with h
    · exact (f h).isLt
    · exact Nat.zero_lt_one⟩

/-- Reading a coordinate as a mask leg. -/
def maskFrom (S : Finset I) (i : I) (z : Fin (if i ∈ S then 2 else 1)) : MaskLeg S (Fin 2) i :=
  fun h => ⟨z, by have := z.isLt; simp only [h, if_true] at this; exact this⟩

theorem maskTo_val (S : Finset I) (i : I) (hi : i ∈ S) (f : MaskLeg S (Fin 2) i) :
    ((maskTo S i f : Fin _) : ℕ) = (f hi : ℕ) := by
  simp [maskTo, hi]

theorem mask_le (Φ : T I → ℝ) (hmono : ∀ X Y : T I,
        (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X)
    (S : Finset I) (hS : S.Nonempty) :
    Φ (toSig (Raw.maskDiagonal ℂ S (Fin 2))) = Φ (maskSig S) := by
  obtain ⟨i₀, hi₀⟩ := hS
  apply le_antisymm
  · refine raw_read_le Φ hmono (S := maskSig S) (fun i f => maskTo S i f) (fun x => ?_)
    refine (Raw.maskDiagonal_coeff_at S hi₀ x).trans ?_
    show _ = if ∀ i ∈ S, ∀ j ∈ S, ((maskTo S i (x i) : Fin _) : ℕ) = maskTo S j (x j) then 1 else 0
    by_cases hc : ∀ (i : I) (hi : i ∈ S), x i hi = x i₀ hi₀
    · rw [if_pos hc, if_pos]
      intro i hi j hj
      exact (maskTo_val S i hi (x i)).trans ((congrArg Fin.val (hc i hi)).trans
        ((congrArg Fin.val (hc j hj)).symm.trans (maskTo_val S j hj (x j)).symm))
    · rw [if_neg hc, if_neg]
      intro hall
      apply hc
      intro i hi
      apply Fin.ext
      have := hall i hi i₀ hi₀
      exact (maskTo_val S i hi (x i)).symm.trans (this.trans (maskTo_val S i₀ hi₀ (x i₀)))
  · refine read_raw_le Φ hmono (X := Raw.maskDiagonal ℂ S (Fin 2)) (S := maskSig S)
      (fun i z => maskFrom S i z) (fun z => ?_)
    refine Eq.trans ?_ (Raw.maskDiagonal_coeff_at S hi₀ (fun i => maskFrom S i (z i))).symm
    show (if ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j then (1 : ℂ) else 0) = _
    by_cases hc : ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j
    · rw [if_pos hc, if_pos]
      intro i hi
      exact Fin.ext (hc i hi i₀ hi₀)
    · rw [if_neg hc, if_neg]
      intro hall
      apply hc
      intro i hi j hj
      have h1 := congrArg Fin.val (hall i hi)
      have h2 := congrArg Fin.val (hall j hj)
      exact h1.trans h2.symm

end mask


section spec
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The spectral point on tensor classes induced by a coordinate spectral point. -/
noncomputable def phiClass (Φ : T I → ℝ) (h0 : ∀ X, 0 ≤ Φ X) (hmono : ∀ X Y : T I,
        (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X) :
    TensorClass.{0} I ℂ → NNReal :=
  Quotient.lift (s := Raw.setoid.{0} I ℂ) (fun X => ⟨Φ (toSig X), h0 _⟩)
    (fun _ _ h => Subtype.ext (le_antisymm (raw_mono Φ hmono h.1) (raw_mono Φ hmono h.2)))

theorem phiClass_mem [Nonempty I] (Φ : T I → ℝ) (h0 : ∀ X, 0 ≤ Φ X)
    (h1 : Φ ⟨fun _ => 1, fun _ => 1⟩ = 1)
    (hz : ∀ X : T I, (∀ z, X.2 z = 0) → Φ X = 0)
    (hmono : ∀ X Y : T I,
        (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X)
    (hmul : ∀ X Y : T I, Φ (sigMul X Y) = Φ X * Φ Y)
    (hadd : ∀ X Y : T I, Φ (sigAdd X Y) = Φ X + Φ Y) :
    phiClass Φ h0 hmono ∈ normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show Φ (toSig (Raw.zero I ℂ)) = 0
    exact hz _ (fun _ => rfl)
  · apply Subtype.ext
    show Φ (toSig (Raw.one I ℂ)) = 1
    rw [raw_eq Φ hmono (S := ⟨fun _ => 1, fun _ => 1⟩) (fun _ => ⟨fun _ => 0, fun _ => PUnit.unit, fun _ => rfl,
        fun _ => Subsingleton.elim _ _⟩)
      (fun _ => rfl)]
    exact h1
  · intro x y
    refine Quotient.inductionOn₂ (s₁ := Raw.setoid.{0} I ℂ) (s₂ := Raw.setoid.{0} I ℂ) x y
      fun X Y => ?_
    apply Subtype.ext
    show Φ (toSig (X.add Y)) = Φ (toSig X) + Φ (toSig Y)
    rw [raw_eq Φ hmono (S := sigAdd (toSig X) (toSig Y)) (addEquiv X Y) (add_coeff X Y)]
    exact hadd _ _
  · intro x y
    refine Quotient.inductionOn₂ (s₁ := Raw.setoid.{0} I ℂ) (s₂ := Raw.setoid.{0} I ℂ) x y
      fun X Y => ?_
    apply Subtype.ext
    show Φ (toSig (X.mul Y)) = Φ (toSig X) * Φ (toSig Y)
    rw [raw_eq Φ hmono (S := sigMul (toSig X) (toSig Y)) (mulEquiv X Y) (mul_coeff X Y)]
    exact hmul _ _
  · intro x y
    refine Quotient.inductionOn₂ (s₁ := Raw.setoid.{0} I ℂ) (s₂ := Raw.setoid.{0} I ℂ) x y
      fun X Y h => ?_
    exact raw_mono Φ hmono h

end spec

end OMAPort


namespace OMAPort

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

section rev
variable {I : Type} [Fintype I] [DecidableEq I]

/-- A coordinate tensor as a raw tensor with the same coefficients. -/
abbrev sigRaw (X : T I) : Raw.{0} I ℂ := ⟨fun i => Fin (X.1 i), fun _ => inferInstance, X.2⟩

variable [Nonempty I] (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))

/-- A spectral point read on coordinate tensors. -/
noncomputable def psi (X : T I) : ℝ := (φ.val (ofRaw (sigRaw X)) : ℝ)

theorem psi_nonneg (X : T I) : 0 ≤ psi φ X := (φ.val _).2

theorem psi_mono (X Y : T I) (h : ∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
    ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) : psi φ Y ≤ psi φ X := by
  obtain ⟨A, hA⟩ := h
  have hr : (sigRaw Y).Restricts (sigRaw X) := by
    refine ⟨A, fun y => ?_⟩
    change Y.2 y = _
    rw [hA y, show (∑ z, (∏ i, A i (y i) (z i)) * X.2 z) = ∑ z, X.2 z * ∏ i, A i (y i) (z i) from
      Finset.sum_congr rfl fun z _ => mul_comm _ _]
    convert rfl
  have := φ.2.2.2.2.2 _ _ ((ofRaw_le_iff).mpr hr)
  exact_mod_cast this

theorem psi_eq_of_equiv {R : Raw.{0} I ℂ} {S : T I} (e : ∀ i, R.Leg i ≃ Fin (S.1 i))
    (h : ∀ x, R.coeff x = S.2 (fun i => e i (x i))) : psi φ S = (φ.val (ofRaw R) : ℝ) := by
  have he : ofRaw R = ofRaw (sigRaw S) := ofRaw_eq_iff.mpr (Raw.reindex_equivalent e h)
  rw [psi, he]

theorem psi_one : psi φ ⟨fun _ => 1, fun _ => 1⟩ = 1 := by
  rw [psi_eq_of_equiv φ (R := Raw.one I ℂ) (S := ⟨fun _ => 1, fun _ => 1⟩) (fun _ => ⟨fun _ => 0, fun _ => PUnit.unit, fun _ => rfl,
      fun _ => Subsingleton.elim _ _⟩) (fun _ => rfl), ofRaw_one, φ.2.2.1]
  rfl

theorem psi_zero (X : T I) (h : ∀ z, X.2 z = 0) : psi φ X = 0 := by
  have h0 : ofRaw (sigRaw X) = 0 := (ofRaw_eq_zero_iff _).mpr (funext h)
  rw [psi, h0, φ.2.1]
  rfl

theorem psi_mul (X Y : T I) : psi φ (sigMul X Y) = psi φ X * psi φ Y := by
  let R : Raw.{0} I ℂ := ⟨fun i => Fin (X.1 i) × Fin (Y.1 i), fun _ => inferInstance,
    fun x => X.2 (fun i => (x i).1) * Y.2 (fun i => (x i).2)⟩
  have hR : ofRaw R = ofRaw (sigRaw X) * ofRaw (sigRaw Y) := rfl
  rw [psi_eq_of_equiv φ (R := R) (S := sigMul X Y) (fun _ => finProdFinEquiv) (fun x => ?_), hR,
    φ.2.2.2.2.1]
  · rfl
  show X.2 (fun i => (x i).1) * Y.2 (fun i => (x i).2) =
    X.2 (fun i => (finProdFinEquiv.symm (finProdFinEquiv (x i))).1) *
      Y.2 (fun i => (finProdFinEquiv.symm (finProdFinEquiv (x i))).2)
  simp only [Equiv.symm_apply_apply]

theorem psi_add (X Y : T I) : psi φ (sigAdd X Y) = psi φ X + psi φ Y := by
  let R : Raw.{0} I ℂ := ⟨fun i => Fin (X.1 i) ⊕ Fin (Y.1 i), fun _ => inferInstance, sumCoeff X.2 Y.2⟩
  have hR : ofRaw R = ofRaw (sigRaw X) + ofRaw (sigRaw Y) := rfl
  rw [psi_eq_of_equiv φ (R := R) (S := sigAdd X Y) (fun _ => finSumFinEquiv) (fun x => ?_), hR,
    φ.2.2.2.1]
  · rfl
  show sumCoeff X.2 Y.2 x =
    if h : ∀ i, ((finSumFinEquiv (x i) : Fin (X.1 i + Y.1 i)) : ℕ) < X.1 i then
      X.2 (fun i => ⟨finSumFinEquiv (x i), h i⟩)
    else if h' : ∀ i, X.1 i ≤ ((finSumFinEquiv (x i) : Fin (X.1 i + Y.1 i)) : ℕ) then
      Y.2 (fun i => ⟨(finSumFinEquiv (x i) : Fin (X.1 i + Y.1 i)) - X.1 i, by
        have h2 := (finSumFinEquiv (x i) : Fin (X.1 i + Y.1 i)).2; have := h' i; omega⟩)
    else 0
  split_ifs with h1 h2
  · have hx : ∀ i, ∃ a, x i = Sum.inl a := by
      intro i
      rcases hxi : x i with a | b
      · exact ⟨a, rfl⟩
      · exfalso
        have := h1 i
        rw [hxi] at this
        simp at this
    choose a ha using hx
    obtain rfl : x = fun i => Sum.inl (a i) := funext ha
    rw [sumCoeff_inl]
    exact congrArg X.2 (funext fun i => Fin.ext (by simp))
  · have hx : ∀ i, ∃ b, x i = Sum.inr b := by
      intro i
      rcases hxi : x i with a | b
      · exfalso
        have := h2 i
        rw [hxi] at this
        simp at this
        omega
      · exact ⟨b, rfl⟩
    choose b hb using hx
    obtain rfl : x = fun i => Sum.inr (b i) := funext hb
    rw [sumCoeff_inr]
    exact congrArg Y.2 (funext fun i => Fin.ext (by simp))
  · rw [sumCoeff_mixed]
    · intro a h
      apply h1
      intro i
      rw [← h]
      simp
    · intro b h
      apply h2
      intro i
      rw [← h]
      simp

/-- The mask diagonal read through `psi`. -/
theorem psi_mask (S : Finset I) (hS : S.Nonempty) :
    psi φ (maskSig S) = (φ.val (ofRaw (Raw.maskDiagonal ℂ S (Fin 2))) : ℝ) := by
  have h := mask_le (psi φ) (psi_mono φ) S hS
  have e : psi φ (toSig (Raw.maskDiagonal ℂ S (Fin 2))) =
      (φ.val (ofRaw (Raw.maskDiagonal ℂ S (Fin 2))) : ℝ) :=
    psi_eq_of_equiv φ (fun i => Fintype.equivFin _) (fun x => congrArg _ (funext fun i => ((Fintype.equivFin _).symm_apply_apply (x i)).symm))
  rw [← e, h]

end rev

end OMAPort


namespace OMAPort

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

section glue
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The wire tensor of the parent statement: one shared bit between the sites `s` and `t`. -/
def wireT (s t : I) : T I :=
  ⟨fun j => if j = s ∨ j = t then 2 else 1, fun y => if (y s : ℕ) = y t then 1 else 0⟩

/-- The unit tensor. -/
def unitT : T I := ⟨fun _ => 1, fun _ => 1⟩

/-- A spectral point in the coordinate encoding (the predicate `P` of the statement, unpacked). -/
structure SP (Φ : T I → ℝ) : Prop where
  h0 : ∀ X, 0 ≤ Φ X
  h1 : Φ unitT = 1
  hz : ∀ X : T I, (∀ z, X.2 z = 0) → Φ X = 0
  hmono : ∀ X Y : T I, (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
    ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X
  hmul : ∀ X Y : T I, Φ (sigMul X Y) = Φ X * Φ Y
  hadd : ∀ X Y : T I, Φ (sigAdd X Y) = Φ X + Φ Y

theorem nonempty_of_SP {Φ : T I → ℝ} (h : SP Φ) : Nonempty I := by
  by_contra hI
  rw [not_nonempty_iff] at hI
  have key : ∀ X Y : T I, (∀ y z, Y.2 y = X.2 z) → Φ Y ≤ Φ X := fun X Y hyz =>
    h.hmono X Y ⟨fun i => isEmptyElim i, fun y => by
      rw [Fintype.sum_unique]
      simp only [Fintype.prod_empty, one_mul]
      exact hyz y default⟩
  have hs : ∀ z, (sigAdd (unitT : T I) unitT).2 z = 1 := by
    intro z
    simp [sigAdd, unitT]
  have e1 := key (sigAdd unitT unitT) unitT (fun y z => by rw [hs z]; rfl)
  have e2 := key unitT (sigAdd unitT unitT) (fun y z => by rw [hs y]; rfl)
  have e3 := h.hadd unitT unitT
  rw [h.h1] at e1 e2 e3
  linarith

theorem phi_toSig_sigRaw {Φ : T I → ℝ} (h : SP Φ) (X : T I) : Φ (toSig (sigRaw X)) = Φ X :=
  raw_eq Φ h.hmono (X := sigRaw X) (S := X) (fun _ => Equiv.refl _) (fun _ => rfl)

/-- The spectral point on tensor classes of a coordinate spectral point. -/
noncomputable def fwd [Nonempty I] {Φ : T I → ℝ} (h : SP Φ) :
    normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop) :=
  ⟨phiClass Φ h.h0 h.hmono, phiClass_mem Φ h.h0 h.h1 h.hz h.hmono h.hmul h.hadd⟩

theorem psi_fwd [Nonempty I] {Φ : T I → ℝ} (h : SP Φ) : psi (fwd h) = Φ := by
  funext X
  exact phi_toSig_sigRaw h X

theorem SP_psi [Nonempty I] (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop)) :
    SP (psi φ) :=
  ⟨psi_nonneg φ, psi_one φ, psi_zero φ, psi_mono φ, psi_mul φ, psi_add φ⟩

theorem psi_toSig [Nonempty I] (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    (R : Raw.{0} I ℂ) : psi φ (toSig R) = (φ.val (ofRaw R) : ℝ) :=
  psi_eq_of_equiv φ (fun i => Fintype.equivFin _)
    (fun x => congrArg _ (funext fun i => ((Fintype.equivFin _).symm_apply_apply (x i)).symm))

theorem SP_wire_self {Φ : T I → ℝ} (h : SP Φ) (s : I) : Φ (wireT s s) = 1 := by
  apply le_antisymm
  · rw [← h.h1]
    apply h.hmono unitT (wireT s s)
    refine ⟨fun _ _ _ => 1, fun y => ?_⟩
    haveI : ∀ i, Unique (Fin ((unitT : T I).1 i)) := fun _ => (inferInstance : Unique (Fin 1))
    rw [Fintype.sum_unique]
    simp [wireT, unitT]
  · rw [← h.h1]
    apply h.hmono (wireT s s) unitT
    have hpos : ∀ i, 0 < (wireT s s).1 i := fun i => by
      simp only [wireT]; split_ifs <;> norm_num
    let z0 : ∀ i, Fin ((wireT s s).1 i) := fun i => ⟨0, hpos i⟩
    refine ⟨fun i _ b => if (b : ℕ) = 0 then 1 else 0, fun y => ?_⟩
    rw [Fintype.sum_eq_single z0]
    · simp [z0, wireT, unitT]
    · intro z hz
      obtain ⟨i, hi⟩ : ∃ i, z i ≠ z0 i := by
        by_contra hc
        push_neg at hc
        exact hz (funext hc)
      have hi' : ((z i : ℕ) = 0) = False := by
        apply propext
        constructor
        · intro e; exact hi (Fin.ext e)
        · intro e; exact e.elim
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi'])]
      simp

theorem wire_eq_mask {Φ : T I → ℝ} (h : SP Φ) (s t : I) :
    Φ (wireT s t) = Φ (maskSig {s, t}) := by
  have hd : ∀ i, (wireT s t).1 i = (maskSig ({s, t} : Finset I)).1 i := fun i => by
    simp [wireT, maskSig]
  rw [← phi_toSig_sigRaw h (wireT s t)]
  apply raw_eq Φ h.hmono (X := sigRaw (wireT s t)) (S := maskSig {s, t})
    (fun i => finCongr (hd i))
  intro x
  change (if ((x s : ℕ) = x t) then (1 : ℂ) else 0) =
    if ∀ i ∈ ({s, t} : Finset I), ∀ j ∈ ({s, t} : Finset I),
      ((finCongr (hd i) (x i) : ℕ) = finCongr (hd j) (x j)) then 1 else 0
  simp only [finCongr_apply, Fin.coe_cast]
  congr 1
  apply propext
  constructor
  · intro e i hi j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · rfl
    · exact e
    · exact e.symm
    · rfl
  · intro e
    exact e s (by simp) t (by simp)

/-- The wire distance of the statement is OpenAI's `rawWireDistance` of the class point. -/
theorem logb_psi_wire [Nonempty I]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop)) (s t : I) :
    Real.logb 2 (psi φ (wireT s t)) = rawWireDistance φ 1 s t := by
  by_cases hst : s = t
  · subst hst
    rw [rawWireDistance_self φ 1 zero_le_one, SP_wire_self (SP_psi φ), Real.logb_one]
  · have hinj : Function.Injective (![s, t] : Fin 2 → I) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
    have hS : ∀ i, i ∈ ({s, t} : Finset I) ↔ ∃ j, (⟨![s, t], hinj⟩ : Fin 2 ↪ I) j = i := by
      intro i
      simp only [Finset.mem_insert, Finset.mem_singleton, Function.Embedding.coeFn_mk]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
      · rintro ⟨j, rfl⟩
        fin_cases j <;> simp
    have hm := Raw.ofRaw_group_diagonal_eq_mask (K := ℂ) ⟨![s, t], hinj⟩ {s, t} hS (Fin 2)
    simp only [Function.Embedding.coeFn_mk] at hm
    rw [rawWireDistance, rawLogPrice, one_mul, hm, wire_eq_mask (SP_psi φ),
      ← psi_toSig φ, mask_le (psi φ) (psi_mono φ) {s, t} ⟨s, by simp⟩]

theorem logb_wire_fwd [Nonempty I] {Φ : T I → ℝ} (h : SP Φ) (s t : I) :
    Real.logb 2 (Φ (wireT s t)) = rawWireDistance (fwd h) 1 s t := by
  rw [← logb_psi_wire (fwd h) s t, psi_fwd h]

end glue

/-- Padding a tensor on `I` with a trivial leg at the new site `none`. -/
def padT {I : Type} (X : T I) : T (Option I) :=
  ⟨fun o => o.elim 1 X.1, fun z => X.2 (fun i => z (some i))⟩

theorem psi_pad {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    (ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Option I) ℂ → _ → Prop))
    (hext : ∀ R : Raw.{0} I ℂ, rawLogPrice ψ 1 (R.group some) = rawLogPrice φ 1 R) (X : T I) :
    psi ψ (padT X) = psi φ X := by
  classical
  haveI hempty : IsEmpty {j : I // some j = (none : Option I)} := ⟨fun j => by cases j.2⟩
  let huniq : ∀ i : I, Unique {j : I // some j = some i} := fun i =>
    ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext (Option.some_injective _ j.2)⟩
  have hR : psi ψ (padT X) = (ψ.val (ofRaw ((sigRaw X).group some)) : ℝ) := by
    apply psi_eq_of_equiv ψ (R := (sigRaw X).group some) (S := padT X)
      (fun o => match o with
        | none => @Equiv.ofUnique _ (Fin 1) (Pi.uniqueOfIsEmpty _) inferInstance
        | some i => @Equiv.piUnique _ (huniq i) (fun j => Fin (X.1 j.1)))
    intro x
    rfl
  rw [hR]
  by_cases hX : ∀ z, X.2 z = 0
  · rw [← hR, psi_zero ψ (padT X) (fun z => hX _), psi_zero φ X hX]
  · push_neg at hX
    have hne : (sigRaw X).coeff ≠ 0 := by
      obtain ⟨z, hz⟩ := hX
      exact fun h0 => hz (congrFun h0 z)
    have h1 := one_le_raw_spectralValue ψ ((sigRaw X).group some)
      ((Raw.group_ne_zero_iff (sigRaw X) some).mpr hne)
    have h2 := one_le_raw_spectralValue φ (sigRaw X) hne
    have he := hext (sigRaw X)
    simp only [rawLogPrice, one_mul] at he
    have ha : (0 : ℝ) < (ψ.val (ofRaw ((sigRaw X).group some)) : ℝ) :=
      lt_of_lt_of_le one_pos (by exact_mod_cast h1)
    have hb : (0 : ℝ) < (φ.val (ofRaw (sigRaw X)) : ℝ) :=
      lt_of_lt_of_le one_pos (by exact_mod_cast h2)
    exact Real.logb_injOn_pos one_lt_two (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hb) he

end OMAPort

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H2_R1.H1 := by
  refine ⟨fun I _ _ Φ hP a b x y hx hy hxy => ?_,
    fun J _ _ Φ hP a b c d z w u hu0 hu1 hz0 hz1 hw0 hw1 => ?_⟩
  · obtain ⟨h0, h1, hz, hmono, hmul, hadd⟩ := hP
    have hS : OMAPort.SP Φ := ⟨h0, h1, hz, hmono, hmul, hadd⟩
    haveI := OMAPort.nonempty_of_SP hS
    have hab : x + y = rawWireDistance (OMAPort.fwd hS) 1 a b :=
      hxy.trans (OMAPort.logb_wire_fwd hS a b)
    obtain ⟨ψ, hext, ha, hb⟩ :=
      exists_spectral_interval_point (OMAPort.fwd hS) a b x y hx hy hab
    refine ⟨OMAPort.psi ψ, ?_, ?_, ?_, ?_⟩
    · obtain ⟨g0, g1, gz, gm, gmul, gadd⟩ := OMAPort.SP_psi ψ
      exact ⟨g0, g1, gz, gm, gmul, gadd⟩
    · intro X
      have := OMAPort.psi_pad (OMAPort.fwd hS) ψ hext X
      rw [OMAPort.psi_fwd hS] at this
      exact this
    · exact (OMAPort.logb_psi_wire ψ none (some a)).trans ha
    · exact (OMAPort.logb_psi_wire ψ none (some b)).trans hb
  · obtain ⟨h0, h1, hz, hmono, hmul, hadd⟩ := hP
    have hS : OMAPort.SP Φ := ⟨h0, h1, hz, hmono, hmul, hadd⟩
    haveI := OMAPort.nonempty_of_SP hS
    have e := fun s t => OMAPort.logb_wire_fwd hS s t
    change Real.logb 2 (Φ (OMAPort.wireT a z)) = u * Real.logb 2 (Φ (OMAPort.wireT a b)) at hz0
    change Real.logb 2 (Φ (OMAPort.wireT z b)) = (1-u) * Real.logb 2 (Φ (OMAPort.wireT a b)) at hz1
    change Real.logb 2 (Φ (OMAPort.wireT c w)) = u * Real.logb 2 (Φ (OMAPort.wireT c d)) at hw0
    change Real.logb 2 (Φ (OMAPort.wireT w d)) = (1-u) * Real.logb 2 (Φ (OMAPort.wireT c d)) at hw1
    change Real.logb 2 (Φ (OMAPort.wireT z w)) ≤
      (1-u) * Real.logb 2 (Φ (OMAPort.wireT a c)) + u * Real.logb 2 (Φ (OMAPort.wireT b d))
    rw [e, e] at hz0 hz1 hw0 hw1
    rw [e, e, e]
    exact rawWireDistance_synchronized (OMAPort.fwd hS) 1 zero_le_one a b c d z w u ⟨hu0, hu1⟩
      hz0 hz1 hw0 hw1

