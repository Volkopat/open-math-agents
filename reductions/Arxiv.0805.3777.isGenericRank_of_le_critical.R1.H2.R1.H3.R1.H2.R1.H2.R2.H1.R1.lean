import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Finite-field tangent certificates for three-slice tensors. -/

open scoped BigOperators Nat
open Arxiv.«0805.3777»

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R2_H1_R1

/-- Lift a right inverse in the residue ring to an integer square matrix,
whose determinant remains nonzero over the complex numbers. -/
private theorem surjective_of_modular_reduction {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (M : Matrix I J ℤ) (h : Function.Surjective (M.map (Int.castRingHom (ZMod 101))).mulVec) :
    Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  obtain ⟨V, hV⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h
  let W : Matrix J I ℤ := fun j i => (V j i).val
  have hw : W.map (Int.castRingHom (ZMod 101)) = V := by
    ext j i
    change (((V j i).val : ℤ) : ZMod 101) = V j i
    simp
  let B : Matrix I I ℤ := M * W
  have hone : B.map (Int.castRingHom (ZMod 101)) = 1 := by
    rw [show B = M * W from rfl, Matrix.map_mul, hw, hV]
  have hdet : B.det ≠ 0 := by
    intro hz
    have hh : (B.map (Int.castRingHom (ZMod 101))).det = 0 := by
      change ((Int.castRingHom (ZMod 101)).mapMatrix B).det = 0
      rw [← RingHom.map_det, hz, map_zero]
    rw [hone, Matrix.det_one] at hh
    exact (show (1 : ZMod 101) ≠ 0 by decide) hh
  have hcomplex : (B.map (Int.castRingHom ℂ)).det ≠ 0 := by
    change ((Int.castRingHom ℂ).mapMatrix B).det ≠ 0
    rw [← RingHom.map_det]
    change (B.det : ℂ) ≠ 0
    exact_mod_cast hdet
  have hb : Function.Surjective (B.map (Int.castRingHom ℂ)).mulVec := by
    apply Matrix.mulVec_surjective_iff_isUnit.mpr
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hcomplex)
  intro v
  obtain ⟨u, hu⟩ := hb v
  refine ⟨(W.map (Int.castRingHom ℂ)).mulVec u, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul]
  exact hu

/-- The finite-field normal test implies the predicted complex generic rank. -/
private theorem generic_of_modular_normals {b n r : ℕ} (hb : 3 ≤ b) (hbn : b ≤ n)
    (hc : r = 3*b*n ⌈/⌉ (3+b+n-2))
    (certificate : ∃ x : Fin r → Fin 3 → ZMod 101, ∃ y : Fin r → Fin b → ZMod 101,
      ∃ z : Fin r → Fin n → ZMod 101, ∀ H : Fin 3 → Fin b → Fin n → ZMod 101,
        (∀ t i, ∑ j, ∑ k, (y t j * z t k) * H i j k = 0) →
        (∀ t j, ∑ i, ∑ k, (x t i * z t k) * H i j k = 0) →
        (∀ t k, ∑ i, ∑ j, (x t i * y t j) * H i j k = 0) → H = 0) :
    IsGenericRank [3,b,n] r := by
  classical
  let : Fact (Nat.Prime 101) := ⟨by norm_num⟩
  obtain ⟨x,y,z,detect⟩ := certificate
  let xi (t : Fin r) (i : Fin 3) : ℤ := (x t i).val
  let yi (t : Fin r) (j : Fin b) : ℤ := (y t j).val
  let zi (t : Fin r) (k : Fin n) : ℤ := (z t k).val
  let M : Matrix (Fin 3 × Fin b × Fin n) (Fin r × (Fin 3 ⊕ Fin b ⊕ Fin n)) ℤ :=
    fun row col => match col.2 with
    | .inl l => if l = row.1 then yi col.1 row.2.1 * zi col.1 row.2.2 else 0
    | .inr (.inl l) => if l = row.2.1 then xi col.1 row.1 * zi col.1 row.2.2 else 0
    | .inr (.inr l) => if l = row.2.2 then xi col.1 row.1 * yi col.1 row.2.1 else 0
  have fieldSpans := HigherPencil.augmented_span_of_annihilator x y z
    (fun q : Empty => q.elim) (fun q : Empty => q.elim)
    (fun H hx hy hz _ => detect H hx hy hz)
  have hM : Function.Surjective (M.map (Int.castRingHom (ZMod 101))).mulVec := by
    intro F
    obtain ⟨u,v,w,_,h⟩ := fieldSpans fun i j k => F (i,j,k)
    let coeff : Fin r × (Fin 3 ⊕ Fin b ⊕ Fin n) → ZMod 101 := fun c =>
      c.2.elim (u c.1) (Sum.elim (v c.1) (w c.1))
    refine ⟨coeff, ?_⟩
    funext ⟨i,j,k⟩
    rw [h i j k]
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_sum_type,
      M, Matrix.map, apply_ite, coeff, xi, yi, zi, Finset.sum_add_distrib,
      mul_comm, mul_left_comm, mul_assoc, add_assoc]
  apply CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) hb hbn hc
  refine ⟨fun t i => (xi t i : ℂ), fun t j => (yi t j : ℂ), fun t k => (zi t k : ℂ), ?_⟩
  intro T
  obtain ⟨g,hg⟩ := surjective_of_modular_reduction M hM (fun row => T row.1 row.2.1 row.2.2)
  refine ⟨fun t i => g (t,.inl i), fun t j => g (t,.inr (.inl j)),
    fun t k => g (t,.inr (.inr k)), fun i j k => ?_⟩
  have entry := congrFun hg (i,j,k)
  rw [← entry]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_sum_type,
    M, Matrix.map, apply_ite, Finset.sum_add_distrib, mul_comm, mul_left_comm, add_assoc]

/-- The first of the eight formats is an odd sharp boundary. -/
theorem rank_three_fourteen_eighteen : IsGenericRank [3,14,18] 23 :=
  CriticalConicBoundary.odd_boundary_rank 5 (by decide) (by decide)

/-- Finite normal-space certificates for the six smaller remaining formats. -/
def H1 : Prop :=
  ∀ b n r : ℕ, (b,n,r) ∈ ([(24,37,43), (16,20,26), (23,33,40), (18,22,29),
      (24,33,41), (23,29,38)] : List (ℕ × ℕ × ℕ)) →
    ∃ x : Fin r → Fin 3 → ZMod 101, ∃ y : Fin r → Fin b → ZMod 101,
      ∃ z : Fin r → Fin n → ZMod 101, ∀ H : Fin 3 → Fin b → Fin n → ZMod 101,
        (∀ t i, ∑ j, ∑ k, (y t j * z t k) * H i j k = 0) →
        (∀ t j, ∑ i, ∑ k, (x t i * z t k) * H i j k = 0) →
        (∀ t k, ∑ i, ∑ j, (x t i * y t j) * H i j k = 0) → H = 0

/-- The finite normal-space certificate for the largest format. -/
def H2 : Prop :=
  ∃ x : Fin 86 → Fin 3 → ZMod 101, ∃ y : Fin 86 → Fin 47 → ZMod 101,
    ∃ z : Fin 86 → Fin 75 → ZMod 101, ∀ H : Fin 3 → Fin 47 → Fin 75 → ZMod 101,
      (∀ t i, ∑ j, ∑ k, (y t j * z t k) * H i j k = 0) →
      (∀ t j, ∑ i, ∑ k, (x t i * z t k) * H i j k = 0) →
      (∀ t k, ∑ i, ∑ j, (x t i * y t j) * H i j k = 0) → H = 0

theorem main : H1 → H2 →
    OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R2.H1 := by
  intro hsmall hlarge
  exact ⟨rank_three_fourteen_eighteen,
    generic_of_modular_normals (by decide) (by decide) (by decide) (hsmall 24 37 43 (by decide)),
    generic_of_modular_normals (by decide) (by decide) (by decide) (hsmall 16 20 26 (by decide)),
    generic_of_modular_normals (by decide) (by decide) (by decide) (hsmall 23 33 40 (by decide)),
    generic_of_modular_normals (by decide) (by decide) (by decide) (hsmall 18 22 29 (by decide)),
    generic_of_modular_normals (by decide) (by decide) (by decide) (hsmall 24 33 41 (by decide)),
    generic_of_modular_normals (by decide) (by decide) (by decide) (hsmall 23 29 38 (by decide)),
    generic_of_modular_normals (by decide) (by decide) (by decide) hlarge⟩

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R2_H1_R1

/-
Independent arithmetic check for the finite hypotheses.

The first n third-factor vectors are coordinate vectors. The common right
variation kills every x[t] ⊗ y[t] in each slice. In slice k the two local
variations at t=k give the next kernel restriction. The remaining rows
couple the slice kernels. Full column rank of this last matrix proves the
normal-space condition. All operations below are exact modulo 101.

The Python source can be run with NumPy 2.3.5. The output lists b, n, r,
and the rank of the final matrix for each format.

import numpy as np

FORMATS = [(14,18,23),(24,37,43),(16,20,26),(23,33,40),
           (18,22,29),(24,33,41),(23,29,38),(47,75,86)]
P = 101

def echelon(A):
    """Reduced row echelon form using exact integer arithmetic modulo 101."""
    A = A.copy() % P
    pivots = []
    for col in range(A.shape[1]):
        row = len(pivots)
        active = np.flatnonzero(A[row:,col])
        if active.size == 0:
            continue
        k = row+int(active[0])
        A[[row,k]] = A[[k,row]]
        A[row,col:] = A[row,col:]*pow(int(A[row,col]),-1,P)%P
        coeff = A[:,col].copy()
        coeff[row] = 0
        A[:,col:] = (A[:,col:]-coeff[:,None]*A[row,col:])%P
        pivots.append(col)
        if row+1 == A.shape[0]:
            break
    return A, pivots

def kernel(A):
    E,piv = echelon(A)
    free = sorted(set(range(A.shape[1]))-set(piv))
    N = np.zeros((A.shape[1],len(free)), dtype=np.int64)
    N[free] = np.eye(len(free), dtype=np.int64)
    N[piv] = -E[:len(piv),free] % P
    assert not (A@N%P).any()
    return N

def partial(x,y):
    return np.vstack((np.kron(np.eye(3,dtype=np.int64),y), np.kron(x,np.eye(len(y),dtype=np.int64))))

def calculate(b,n,r,X,Y,Z):
    common = kernel(np.array([np.kron(X[t],Y[t]) for t in range(r)]))
    local = [partial(X[t],Y[t]) for t in range(r)]
    bases = [common @ kernel(local[k] @ common % P) % P for k in range(n)]
    test = np.block([[(local[t] @ bases[k])*Z[t,k] % P for k in range(n)] for t in range(n,r)])
    return test.shape[1],len(echelon(test)[1])

for b,n,r in FORMATS:
    rng = np.random.default_rng(3777+r)
    X = rng.integers(0,P,size=(r,3))
    Y = rng.integers(0,P,size=(r,b))
    Z = np.vstack([np.eye(n,dtype=np.int64),rng.integers(0,P,size=(r-n,n))])
    size, rank = calculate(b,n,r,X,Y,Z)
    assert size == rank == n*(2*b-r-1)
    print(b,n,r,rank)
-/
