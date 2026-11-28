import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H1_R1_H2_R1
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Order.Floor.Div

/- Binary tangent-space certificates by xlh1551 for mattdorman’s six-slice reduction of Friedland’s generic rank problem. A basis in the third factor localizes several points to each individual slice. Row operations within a slice and a smaller binary inverse on the quotient give a triangular matrix. The kernel checks its leading bits. -/

/-!
# A modular certificate for tangent spaces of rank-one complex tensors

A nonzero square minor modulo two of the integer tangent matrix yields
surjectivity over the complex numbers. For selected columns the certificate
only needs the parity of an integer determinant.
-/

namespace TensorModularMinor
open Matrix Function
open scoped BigOperators

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem surjective_of_binary_minor {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I J ℤ) (e : I → J)
    (h : ((A.submatrix id e).map (Int.castRingHom (ZMod 2))).det ≠ 0) :
    Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  classical
  let B := A.submatrix id e
  have hz : B.det ≠ 0 := by
    intro z
    apply h
    change ((Int.castRingHom (ZMod 2)).mapMatrix B).det = 0
    rw [← RingHom.map_det,z,map_zero]
  have hc : (B.map (Int.castRingHom ℂ)).det ≠ 0 := by
    change ((Int.castRingHom ℂ).mapMatrix B).det ≠ 0
    rw [← RingHom.map_det]
    change (B.det : ℂ) ≠ 0
    exact_mod_cast hz
  have onto : Surjective (B.map (Int.castRingHom ℂ)).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hc))
  let P : Matrix J I ℂ := fun j i => if e i=j then 1 else 0
  have sub : A.map (Int.castRingHom ℂ) * P = B.map (Int.castRingHom ℂ) := by
    ext i j
    rw [Matrix.mul_apply]
    simp [P,mul_ite,B,Matrix.map_apply]
  intro y
  obtain ⟨u,hu⟩ := onto y
  exact ⟨P.mulVec u, by rw [Matrix.mulVec_mulVec,sub]; exact hu⟩

def tangentMatrix {a b c r : ℕ} (x : Fin r → Fin a → ℤ) (y : Fin r → Fin b → ℤ)
    (z : Fin r → Fin c → ℤ) :
    Matrix (Fin a × Fin b × Fin c) (Fin r × (Fin a ⊕ Fin b ⊕ Fin c)) ℤ :=
  fun row col => match col.2 with
  | .inl l => if l=row.1 then y col.1 row.2.1 * z col.1 row.2.2 else 0
  | .inr (.inl l) => if l=row.2.1 then x col.1 row.1 * z col.1 row.2.2 else 0
  | .inr (.inr l) => if l=row.2.2 then x col.1 row.1 * y col.1 row.2.1 else 0

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem tangent_spans_of_binary_minor {a b c r : ℕ}
    (x : Fin r → Fin a → ℤ) (y : Fin r → Fin b → ℤ) (z : Fin r → Fin c → ℤ)
    (e : Fin a × Fin b × Fin c → Fin r × (Fin a ⊕ Fin b ⊕ Fin c))
    (h : (((tangentMatrix x y z).submatrix id e).map (Int.castRingHom (ZMod 2))).det ≠ 0) :
    ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin c → ℂ, ∀ i j k, T i j k =
        ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  intro T
  obtain ⟨g,hg⟩ := surjective_of_binary_minor (tangentMatrix x y z) e h
    (fun row => T row.1 row.2.1 row.2.2)
  refine ⟨(fun t i => g (t,.inl i)),(fun t j => g (t,.inr (.inl j))),
    (fun t k => g (t,.inr (.inr k))),fun i j k => ?_⟩
  have entry := congrFun hg (i,j,k)
  rw [← entry]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_sum_type,
    tangentMatrix, Matrix.map_apply, apply_ite, Finset.sum_add_distrib,
    mul_comm, mul_assoc, add_assoc]

end TensorModularMinor

namespace TensorModularMinor
open Function Matrix
open scoped BigOperators

/- A packed row of a matrix over the two-element field. -/
def binaryDigit (word j : ℕ) : ZMod 2 := if word.testBit j then 1 else 0

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem binaryDigit_xor (a b j : ℕ) :
    binaryDigit (a ^^^ b) j = binaryDigit a j + binaryDigit b j := by
  simp only [binaryDigit,Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> decide

def xorRange : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0,_ => 0
  | n+1,f => xorRange n (fun i => f i.castSucc) ^^^ f (Fin.last n)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem binaryDigit_xorRange (n j : ℕ) (f : Fin n → ℕ) :
    binaryDigit (xorRange n f) j = ∑ i, binaryDigit (f i) j := by
  induction n with
  | zero => simp [xorRange,binaryDigit]
  | succ n ih => rw [xorRange,binaryDigit_xor,Fin.sum_univ_castSucc,ih]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
private theorem singleton_bit (i j : ℕ) :
    binaryDigit (2^i) j = if i=j then 1 else 0 := by
  by_cases h : i=j
  · subst j; simp [binaryDigit]
  · simp [binaryDigit,Nat.testBit_two_pow_of_ne,h]

/- An integer matrix with a packed binary right inverse is onto over the complex numbers. -/
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem surjective_of_packed_inverse {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I J ℤ) (B : J → ℕ) (index : I → ℕ) (injective : Injective index)
    (inverse : ∀ i k, ∑ j, (A i j : ZMod 2) * binaryDigit (B j) (index k) =
      binaryDigit (2^(index i)) (index k)) :
    Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  classical
  let W : Matrix J I ℤ := fun j i => if (B j).testBit (index i) then 1 else 0
  let D := A*W
  have unit : (Int.castRingHom (ZMod 2)).mapMatrix D = 1 := by
    ext i k
    change ((∑ j, A i j * W j k : ℤ) : ZMod 2) = (1 : Matrix I I (ZMod 2)) i k
    push_cast
    simpa [W,binaryDigit, Matrix.one_apply,apply_ite,injective.eq_iff,singleton_bit] using
      (inverse i k).trans (singleton_bit (index i) (index k))
  have ddet : ((D.submatrix id id).map (Int.castRingHom (ZMod 2))).det ≠ 0 := by
    change ((Int.castRingHom (ZMod 2)).mapMatrix D).det ≠ 0
    simp [unit]
  intro target
  obtain ⟨v,hv⟩ := surjective_of_binary_minor D id ddet target
  refine ⟨(W.map (Int.castRingHom ℂ)).mulVec v, ?_⟩
  rw [Matrix.mulVec_mulVec]
  rw [← Matrix.map_mul]
  exact hv

end TensorModularMinor

namespace TensorModularMinor
open Matrix Function Finset
open scoped BigOperators

/- Index order is i-major, followed by j, followed by k. -/
def rowIndex {a b c : ℕ} (q : Fin a × Fin b × Fin c) : ℕ :=
  (finProdFinEquiv (finProdFinEquiv (q.1,q.2.1),q.2.2)).val

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
private theorem rowIndex_inj (a b c : ℕ) : Injective (@rowIndex a b c) := by
  rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h
  have pair := finProdFinEquiv.injective (Fin.ext h)
  have triple := finProdFinEquiv.injective (congrArg Prod.fst pair)
  have hi : i=i' := congrArg Prod.fst triple
  have hj : j=j' := congrArg Prod.snd triple
  have hk : k=k' := congrArg Prod.snd pair
  cases hi; cases hj; cases hk; rfl

def packedRow (a b c r : ℕ) (x y z W : Array ℕ) (i j k : ℕ) : ℕ :=
  xorRange r fun t =>
    let off := t.val*(a+b+c)
    let xi := (x[t.val]!).testBit i
    let yj := (y[t.val]!).testBit j
    let zk := (z[t.val]!).testBit k
    (if yj && zk then W[off+i]! else 0) ^^^
    (if xi && zk then W[off+a+j]! else 0) ^^^
    (if xi && yj then W[off+a+b+k]! else 0)

private def entry (x : Array ℕ) (t i : ℕ) : ℤ := if (x[t]!).testBit i then 1 else 0

private def varWord {a b c r : ℕ} (W : Array ℕ) (col : Fin r × (Fin a ⊕ Fin b ⊕ Fin c)) : ℕ :=
  let off := col.1.val*(a+b+c)
  match col.2 with
  | .inl i => W[off+i.val]!
  | .inr (.inl j) => W[off+a+j.val]!
  | .inr (.inr k) => W[off+a+b+k.val]!

/- Verify a whole row of the rectangular right-inverse identity in one packed word. -/
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem spans_of_packed (a b c r : ℕ) (x y z W : Array ℕ)
    (cert : ∀ i : Fin a, ∀ j : Fin b, ∀ k : Fin c,
      packedRow a b c r x y z W i j k = 2^(rowIndex (i,j,k))) :
    ∃ X : Fin r → Fin a → ℂ, ∃ Y : Fin r → Fin b → ℂ, ∃ Z : Fin r → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin c → ℂ, ∀ i j k, T i j k =
        ∑ t, (u t i*(Y t j*Z t k) + X t i*(v t j*Z t k) + X t i*(Y t j*w t k)) := by
  let X (t : Fin r) (i : Fin a) := entry x t i
  let Y (t : Fin r) (j : Fin b) := entry y t j
  let Z (t : Fin r) (k : Fin c) := entry z t k
  let A := tangentMatrix X Y Z
  have onto := surjective_of_packed_inverse A (varWord W) rowIndex (rowIndex_inj a b c)
  have h : Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
    apply onto
    rintro ⟨i,j,k⟩ out
    rw [← cert i j k]
    unfold packedRow
    rw [binaryDigit_xorRange]
    simp only [Fintype.sum_prod_type,Fintype.sum_sum_type,A,tangentMatrix, varWord]
    apply Finset.sum_congr rfl
    intro t _
    simp only [Int.cast_ite,Int.cast_zero,ite_mul,zero_mul,Finset.sum_ite_eq',
      Finset.mem_univ,if_true, X,Y,Z,entry]
    simp only [binaryDigit_xor]
    cases hx : (x[t.val]!).testBit i <;> cases hy : (y[t.val]!).testBit j <;>
      cases hz : (z[t.val]!).testBit k <;>
      simp [binaryDigit]
      <;> abel
  refine ⟨(fun t i => X t i),(fun t j => Y t j),(fun t k => Z t k),fun T => ?_⟩
  obtain ⟨g,hg⟩ := h (fun row => T row.1 row.2.1 row.2.2)
  refine ⟨(fun t i => g (t,.inl i)),(fun t j => g (t,.inr (.inl j))),
    (fun t k => g (t,.inr (.inr k))),fun i j k => ?_⟩
  have eq := congrFun hg (i,j,k)
  rw [← eq]
  simp [A,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fintype.sum_sum_type,
    tangentMatrix,Matrix.map_apply,apply_ite,Finset.sum_add_distrib,mul_comm,mul_left_comm,mul_assoc,add_assoc]

end TensorModularMinor

namespace TensorModularMinor

/- Use a lookup function so that large right inverses can be stored in separate blocks. -/
def packedRowFn (a b c r : ℕ) (x y z : Array ℕ) (W : ℕ → ℕ) (i j k : ℕ) : ℕ :=
  xorRange r fun t =>
    let off := t.val*(a+b+c)
    let xi := (x[t.val]!).testBit i
    let yj := (y[t.val]!).testBit j
    let zk := (z[t.val]!).testBit k
    (if yj && zk then W (off+i) else 0) ^^^
    (if xi && zk then W (off+a+j) else 0) ^^^
    (if xi && yj then W (off+a+b+k) else 0)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
private theorem fn_eq (a b c r : ℕ) (x y z : Array ℕ) (W : ℕ → ℕ)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    packedRow a b c r x y z (Array.ofFn (fun t : Fin (r*(a+b+c)) => W t)) i j k =
      packedRowFn a b c r x y z W i j k := by
  unfold packedRow packedRowFn
  congr 1
  funext t
  have limit : (t.val+1)*(a+b+c) ≤ r*(a+b+c) :=
    Nat.mul_le_mul_right _ t.isLt
  rw [Nat.add_mul,one_mul] at limit
  have bound₁ : t.val*(a+b+c)+i.val < r*(a+b+c) := by omega
  have bound₂ : t.val*(a+b+c)+a+j.val < r*(a+b+c) := by omega
  have bound₃ : t.val*(a+b+c)+a+b+k.val < r*(a+b+c) := by omega
  simp [getElem!_pos, bound₁,bound₂,bound₃]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem spans_of_lookup (a b c r : ℕ) (x y z : Array ℕ) (W : ℕ → ℕ)
    (cert : ∀ i : Fin a, ∀ j : Fin b, ∀ k : Fin c,
      packedRowFn a b c r x y z W i j k = 2^(rowIndex (i,j,k))) :
    ∃ X : Fin r → Fin a → ℂ, ∃ Y : Fin r → Fin b → ℂ, ∃ Z : Fin r → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin c → ℂ, ∀ i j k, T i j k =
        ∑ t, (u t i*(Y t j*Z t k) + X t i*(v t j*Z t k) + X t i*(Y t j*w t k)) := by
  apply spans_of_packed a b c r x y z (Array.ofFn (fun t : Fin (r*(a+b+c)) => W t))
  intro i j k
  rw [fn_eq]
  exact cert i j k

end TensorModularMinor

namespace TensorEchelon
open Nat

/- Sweep the specified leading bit positions from high to low. -/
def step (P : ℕ → ℕ) (k w : ℕ) : ℕ := if w.testBit k then w ^^^ P k else w

def sweep (P : ℕ → ℕ) (n w : ℕ) : ℕ → ℕ
  | 0 => w
  | k+1 => step P (n-(k+1)) (sweep P n w k)

def reduce (P : ℕ → ℕ) (cut n w : ℕ) : ℕ := sweep P n w (n-(cut+1))

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem reduce_closed (Good : ℕ → Prop) (add : ∀ x y, Good x → Good y → Good (x ^^^ y))
    (P : ℕ → ℕ) (cut n : ℕ) (hp : ∀ j, cut < j → j < n → Good (P j))
    (w : ℕ) (hw : Good w) : Good (reduce P cut n w) := by
  have hs (k : ℕ) (hk : k≤n-(cut+1)) : Good (sweep P n w k) := by
    induction k with
    | zero => exact hw
    | succ k ih =>
      have prev := ih (by omega)
      have inside := hp (n-(k+1)) (by omega) (by omega)
      simp only [sweep,step]
      split
      · exact add _ _ prev inside
      · exact prev
  exact hs _ le_rfl

/- A checked triangular elimination transcript puts each designated pivot in the column span. -/
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem pivot_closed (Good : ℕ → Prop) (add : ∀ x y, Good x → Good y → Good (x ^^^ y))
    (P source : ℕ → ℕ) (n : ℕ) (hs : ∀ j, j < n → Good (source j))
    (check : ∀ j, j < n → reduce P j n (source j) = P j) :
    ∀ j, j < n → Good (P j) := by
  intro j hj
  generalize ht : n-j = t
  induction t using Nat.strong_induction_on generalizing j with
  | h t ih =>
    rw [← check j hj]
    apply reduce_closed Good add P j n _ _ (hs j hj)
    intro k hk hkn
    exact ih (n-k) (by omega) k hkn rfl

/- Every binary word shorter than n is spanned by pivots with the indicated leading bits. -/
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem all_closed (Good : ℕ → Prop) (zero : Good 0)
    (add : ∀ x y, Good x → Good y → Good (x ^^^ y)) (P : ℕ → ℕ)
    (n : ℕ) (hp : ∀ j, j<n → Good (P j))
    (shape : ∀ j, j<n → (P j) >>> j = 1) : ∀ w, w < 2^n → Good w := by
  intro w
  induction w using Nat.strong_induction_on with
  | h w ih =>
    intro hw
    by_cases hz : w = 0
    · simpa [hz] using zero
    let j := w.log2
    have hj : j < n := (Nat.log2_lt (by omega)).mpr hw
    have head : w >>> j = 1 := by
      rw [Nat.shiftRight_eq_div_pow]
      apply Nat.div_eq_of_lt_le (k := 1) <;> simp only [one_mul,Nat.reduceAdd]
      · exact Nat.log2_self_le (by omega)
      · have := Nat.lt_log2_self (n := w)
        simpa [j,pow_succ,Nat.mul_comm] using this
    have smaller : w ^^^ P j < w := by
      apply lt_of_lt_of_le _ (Nat.log2_self_le (by omega) : 2^w.log2 ≤ w)
      change w ^^^ P j < 2 ^ j
      apply (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos j)).mp
      rw [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_xor_distrib,head,shape j hj]
      decide
    simpa only [Nat.xor_assoc,Nat.xor_self,Nat.xor_zero] using add _ _ (ih _ smaller (smaller.trans hw)) (hp j hj)

end TensorEchelon

namespace TensorEchelon

/- Concatenate the low s bits of x with all of y. -/
def joinBits (s x y : ℕ) : ℕ := (x % 2^s) ||| (y <<< s)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem bit_join (s x y j : ℕ) : (joinBits s x y).testBit j =
    if j<s then x.testBit j else y.testBit (j-s) := by
  simp only [joinBits,Nat.testBit_or,Nat.testBit_mod_two_pow,Nat.testBit_shiftLeft]
  by_cases h : j<s
  · simp [h,Nat.not_le_of_gt h]
  · simp [h,Nat.le_of_not_gt h]

/- Place the same s-bit pattern in the layers selected by a binary mask. -/
def tiles (s pat : ℕ) : (n mask : ℕ) → ℕ
  | 0,_ => 0
  | n+1,mask => joinBits s (if mask.testBit 0 then pat else 0) (tiles s pat n (mask >>> 1))

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem bit_tiles (s pat n mask k j : ℕ) (hk : k<n) (hj : j<s) :
    (tiles s pat n mask).testBit (k*s+j) = (mask.testBit k && pat.testBit j) := by
  induction n generalizing mask k with
  | zero => omega
  | succ n ih =>
    rw [tiles,bit_join]
    cases k with
    | zero => simp [hj]; split <;> simp_all
    | succ k =>
      rw [Nat.succ_mul]
      have h : ¬ k*s+s+j < s := by omega
      rw [if_neg h,show k*s+s+j-s=k*s+j by omega,ih _ _ (by omega)]
      simp [Nat.testBit_shiftRight,Nat.add_comm]

def bits : ℕ → (ℕ → Bool) → ℕ
  | 0,_ => 0
  | n+1,f => bits n f ||| (if f n then 2^n else 0)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem bit_bits (n : ℕ) (f : ℕ → Bool) (j : ℕ) :
    (bits n f).testBit j = (decide (j<n) && f j) := by
  induction n with
  | zero => simp [bits]
  | succ n ih =>
    simp only [bits,Nat.testBit_or,ih]
    by_cases eq : j=n
    · subst j; cases h : f n <;> simp [h,Nat.testBit_two_pow]
    · by_cases lt : j<n <;> cases h : f n <;>
        simp [eq,Ne.symm eq,lt,h,Nat.testBit_two_pow,show (j<n+1) ↔ j<n by omega]

def addr (l h c p k : ℕ) : ℕ := if p<l then k*l+p else c*l+k*h+(p-l)

/- Store the low coordinates of all slices before the common pivot coordinates. -/
def layerWord (l h c pair mask : ℕ) : ℕ :=
  joinBits (c*l) (tiles l pair c mask) (tiles h (pair >>> l) c mask)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem bit_layerWord (l h c pair mask p k : ℕ) (hp : p<l+h) (hk : k<c) :
    (layerWord l h c pair mask).testBit (addr l h c p k) = (mask.testBit k && pair.testBit p) := by
  unfold layerWord addr
  rw [bit_join]
  by_cases low : p<l
  · rw [if_pos low,if_pos,bit_tiles _ _ _ _ _ _ hk low]
    have := Nat.mul_le_mul_right l hk
    rw [Nat.succ_mul] at this
    omega
  · rw [if_neg low,if_neg (by omega)]
    rw [show c*l+k*h+(p-l)-c*l = k*h+(p-l) by omega,bit_tiles _ _ _ _ _ _ hk (by omega)]
    simp [Nat.testBit_shiftRight,show l+(p-l)=p by omega]

/- Rows of the coefficient plane are numbered i-major. -/
def pairBit (a b x y mode flat : ℕ) : Bool :=
  let i := flat/b
  let j := flat%b
  if mode<a then decide (i=mode) && y.testBit j
  else if mode<a+b then x.testBit i && decide (j=mode-a)
  else x.testBit i && y.testBit j

def pairWord (a b : ℕ) (inv : ℕ → ℕ) (x y mode : ℕ) : ℕ :=
  bits (a*b) fun q => pairBit a b x y mode (inv q)

def sourceWord (a b c l h : ℕ) (inv x y z : ℕ → ℕ) (col : ℕ) : ℕ :=
  let t := col/(a+b+c)
  let m := col%(a+b+c)
  let mask := if m<a+b then z t else 2^(m-a-b)
  layerWord l h c (pairWord a b inv (x t) (y t) m) mask

end TensorEchelon

namespace TensorEchelon
open TensorModularMinor Matrix Function

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem modular_onto {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I J ℤ) (V : Matrix J I (ZMod 2))
    (h : A.map (Int.castRingHom (ZMod 2)) * V = 1) :
    Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  classical
  let W : Matrix J I ℤ := fun j i => (V j i).val
  let D := A*W
  have hw : W.map (Int.castRingHom (ZMod 2)) = V := by
    ext j i
    change (((V j i).val : ℤ) : ZMod 2) = V j i
    simp
  have hd : ((D.submatrix id id).map (Int.castRingHom (ZMod 2))).det ≠ 0 := by
    change ((A*W).map (Int.castRingHom (ZMod 2))).det ≠ 0
    rw [Matrix.map_mul,hw,h,Matrix.det_one]
    exact one_ne_zero
  intro y
  obtain ⟨v,hv⟩ := surjective_of_binary_minor D id hd y
  refine ⟨(W.map (Int.castRingHom ℂ)).mulVec v,?_⟩
  rw [Matrix.mulVec_mulVec,← Matrix.map_mul]
  exact hv

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem onto_of_pivots {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I J ℤ) (index : I → ℕ) (hi : Injective index) (n : ℕ)
    (hn : ∀ i, index i<n) (P src : ℕ → ℕ)
    (columns : ∀ p, p<n → ∃ col : J, ∀ i, binaryDigit (src p) (index i) = (A i col : ZMod 2))
    (check : ∀ p, p<n → reduce P p n (src p) = P p)
    (shape : ∀ p, p<n → P p >>> p = 1) : Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  classical
  let M := A.map (Int.castRingHom (ZMod 2))
  let Good (w : ℕ) := ∃ q : J → ZMod 2, M.mulVec q = fun i => binaryDigit w (index i)
  have zero : Good 0 := ⟨0,by ext i; simp [binaryDigit]⟩
  have add (x y) (hx : Good x) (hy : Good y) : Good (x ^^^ y) := by
    obtain ⟨u,hu⟩ := hx
    obtain ⟨v,hv⟩ := hy
    exact ⟨u+v,by rw [Matrix.mulVec_add,hu,hv]; ext i; simp [binaryDigit_xor]⟩
  have inputs (p) (hp : p<n) : Good (src p) := by
    obtain ⟨j,hj⟩ := columns p hp
    exact ⟨Pi.single j 1,by rw [Matrix.mulVec_single_one]; ext i; exact (hj i).symm⟩
  have piv := pivot_closed Good add P src n inputs check
  have single (i : I) : Good (2^index i) :=
    all_closed Good zero add P n piv shape _ (Nat.pow_lt_pow_right (by decide) (hn i))
  choose v hv using single
  apply modular_onto A (fun j i => v i j)
  ext i k
  have h := congrFun (hv k) i
  change (∑ j, M i j*v k j) = (1 : Matrix I I (ZMod 2)) i k
  rw [Matrix.one_apply]
  change (∑ j, M i j*v k j) = binaryDigit (2^index k) (index i) at h
  rw [h]
  by_cases eq : i=k
  · subst k; simp [binaryDigit,Nat.testBit_two_pow]
  · simp [binaryDigit,Nat.testBit_two_pow,eq,hi.eq_iff,Ne.symm eq]

end TensorEchelon

namespace TensorTwoSided
open Matrix Function TensorEchelon TensorModularMinor

/- XOR a subset of the raw output rows in one third-coordinate slice. -/
def mix (raw : ℕ → ℕ) (mask : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => (mix raw mask n) ^^^ (if mask.testBit n then raw n else 0)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem mix_closed (Good : ℕ → Prop) (zero : Good 0)
    (add : ∀ x y, Good x → Good y → Good (x ^^^ y)) (raw : ℕ → ℕ) (mask n : ℕ)
    (h : ∀ i, i<n → Good (raw i)) : Good (mix raw mask n) := by
  induction n with
  | zero => exact zero
  | succ n ih =>
    have sub := ih (fun i hi => h i (by omega))
    simp only [mix]
    split
    · exact add _ _ sub (h _ (by omega))
    · simpa using sub

/- An integer matrix is onto if row combinations of its packed modular product
supply all leading bits. The left and right preconditioners are unrestricted. -/
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem onto {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I J ℤ) (index : I → ℕ) (hi : Injective index) (n : ℕ) (hn : ∀ i, index i<n)
    (W : J → ℕ) (raw : I → ℕ)
    (action : ∀ i k, k<n → ∑ j, (A i j : ZMod 2)*binaryDigit (W j) k = binaryDigit (raw i) k)
    (piv : ℕ → ℕ)
    (mixing : ∀ Good : ℕ → Prop, Good 0 → (∀ x y, Good x → Good y → Good (x ^^^ y)) →
        (∀ i, Good (raw i)) → ∀ p, p<n → Good (piv p))
    (shape : ∀ p, p<n → piv p >>> p = 1) :
    Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  classical
  let B : Matrix J I (ZMod 2) := fun j i => binaryDigit (W j) (index i)
  let M := A.map (Int.castRingHom (ZMod 2)) * B
  let Good (w : ℕ) := ∃ q : I → ZMod 2, M.transpose.mulVec q = fun i => binaryDigit w (index i)
  have zero : Good 0 := ⟨0,by ext i; simp [binaryDigit]⟩
  have add (x y) (hx : Good x) (hy : Good y) : Good (x ^^^ y) := by
    obtain ⟨u,hu⟩ := hx
    obtain ⟨v,hv⟩ := hy
    exact ⟨u+v,by rw [Matrix.mulVec_add,hu,hv]; ext i; simp [binaryDigit_xor]⟩
  have rows (i : I) : Good (raw i) := by
    refine ⟨Pi.single i 1,?_⟩
    rw [Matrix.mulVec_single_one]
    funext k
    exact action i (index k) (hn k)
  have single (k : I) : Good (2^index k) := all_closed Good zero add piv n
    (mixing Good zero add rows) shape _ (Nat.pow_lt_pow_right (by decide) (hn k))
  choose b hb using single
  let R : Matrix I I (ZMod 2) := fun i j => b j i
  have inv : M.transpose * R = 1 := by
    ext i k
    have entry := congrFun (hb k) i
    change (∑ j, M.transpose i j*b k j) = binaryDigit (2^index k) (index i) at entry
    rw [Matrix.mul_apply,Matrix.one_apply,entry]
    by_cases eq : i=k
    · subst k; simp [binaryDigit]
    · simp [binaryDigit,Nat.testBit_two_pow,hi.eq_iff,eq,Ne.symm eq]
  have ontoT := Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨_,inv⟩
  have ontoM : Surjective M.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr
    (((Matrix.isUnit_transpose (A := M))).mp (Matrix.mulVec_surjective_iff_isUnit.mp ontoT))
  obtain ⟨C,hC⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp ontoM
  apply modular_onto A (B*C)
  rw [← Matrix.mul_assoc]
  exact hC
end TensorTwoSided

namespace TensorTwoSided
open Matrix Function TensorModularMinor

def varWord (a b c : ℕ) (W : ℕ → ℕ) {r : ℕ} (col : Fin r × (Fin a ⊕ Fin b ⊕ Fin c)) : ℕ :=
  let off := col.1.val*(a+b+c)
  match col.2 with
  | .inl i => W (off+i.val)
  | .inr (.inl j) => W (off+a+j.val)
  | .inr (.inr k) => W (off+a+b+k.val)

def combined (a b c r : ℕ) (x y z : Array ℕ) (W layer masks : ℕ → ℕ) (p : ℕ) : ℕ :=
  mix (fun ij => packedRowFn a b c r x y z W (ij/b) (ij%b) (layer p) % 2^(a*b*c)) (masks p) (a*b)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem spans (a b c r : ℕ) (x y z : Array ℕ) (W layer masks : ℕ → ℕ)
    (layers : ∀ p, p<a*b*c → layer p<c)
    (shape : ∀ p, p<a*b*c → combined a b c r x y z W layer masks p >>> p = 1) :
    ∃ X : Fin r → Fin a → ℂ, ∃ Y : Fin r → Fin b → ℂ, ∃ Z : Fin r → Fin c → ℂ,
    ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin c → ℂ, ∀ i j k, T i j k =
        ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  let X (t : Fin r) (i : Fin a) : ℤ := if (x[t.val]!).testBit i then 1 else 0
  let Y (t : Fin r) (j : Fin b) : ℤ := if (y[t.val]!).testBit j then 1 else 0
  let Z (t : Fin r) (k : Fin c) : ℤ := if (z[t.val]!).testBit k then 1 else 0
  let A := tangentMatrix X Y Z
  let code (q : Fin a × Fin b × Fin c) := finProdFinEquiv (finProdFinEquiv (q.1,q.2.1),q.2.2)
  have ci : Injective (fun q => (code q).val) := by
    rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ eq
    have pair := finProdFinEquiv.injective (Fin.ext eq)
    have triple := finProdFinEquiv.injective (congrArg Prod.fst pair)
    obtain ⟨hi,hj⟩ := Prod.mk.inj triple
    have hk := congrArg Prod.snd pair
    cases hi; cases hj; cases hk; rfl
  let raw (q : Fin a × Fin b × Fin c) := packedRowFn a b c r x y z W q.1 q.2.1 q.2.2 % 2^(a*b*c)
  have onM : Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
    apply onto A _ ci (a*b*c) (fun i => (code i).isLt) (varWord a b c W) raw _ _ _ shape
    · rintro ⟨i,j,k⟩ out ho
      unfold raw
      rw [show binaryDigit (packedRowFn a b c r x y z W i j k % 2^(a*b*c)) out = binaryDigit (packedRowFn a b c r x y z W i j k) out by simp [binaryDigit,Nat.testBit_mod_two_pow,ho]]
      unfold packedRowFn
      rw [binaryDigit_xorRange]
      simp only [Fintype.sum_prod_type,Fintype.sum_sum_type,A,tangentMatrix,varWord]
      apply Finset.sum_congr rfl
      intro t _
      simp only [Int.cast_ite,Int.cast_zero,ite_mul,zero_mul,Finset.sum_ite_eq',
        Finset.mem_univ,if_true,X,Y,Z]
      simp only [binaryDigit_xor]
      cases hx : (x[t.val]!).testBit i <;> cases hy : (y[t.val]!).testBit j <;>
        cases hz : (z[t.val]!).testBit k <;> simp [binaryDigit] <;> abel
    · intro Good zero add rows p hp
      apply mix_closed Good zero add
      intro u hu
      have bpos : 0<b := by by_contra! h; simp [show b=0 by omega] at hu
      exact rows (⟨u/b,(Nat.div_lt_iff_lt_mul bpos).mpr hu⟩,⟨u%b,Nat.mod_lt _ bpos⟩,⟨layer p,layers p hp⟩)
  refine ⟨(fun t i => X t i),(fun t j => Y t j),(fun t k => Z t k),fun T => ?_⟩
  obtain ⟨g,hg⟩ := onM (fun q => T q.1 q.2.1 q.2.2)
  refine ⟨(fun t i => g (t,.inl i)),(fun t j => g (t,.inr (.inl j))),
    (fun t k => g (t,.inr (.inr k))),fun i j k => ?_⟩
  have e := congrFun hg (i,j,k)
  rw [← e]
  simp [A,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fintype.sum_sum_type,tangentMatrix,
    Matrix.map_apply,apply_ite,Finset.sum_add_distrib,mul_comm,mul_left_comm,mul_assoc,add_assoc]

end TensorTwoSided

namespace TensorTwoSided
def packRows (B : ℕ) (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0,_ => 0
  | n+1,start => f start%B+B*packRows B f n (start+1)

def field (width data j : ℕ) := (data >>> (j*width)) % 2^width

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem field_pack (width : ℕ) (f : ℕ → ℕ) (n start j : ℕ) (hj : j<n) :
    field width (packRows (2^width) f n start) j = (f (start+j)) % 2^width := by
  let B := 2^width
  have pos : 0<B := Nat.two_pow_pos _
  have aux (k q i : ℕ) (hi : i<k) :
      packRows B f k q / B^i % B = f (q+i)%B := by
    induction k generalizing q i with
    | zero => omega
    | succ k ih =>
      cases i with
      | zero => simp [packRows]
      | succ i =>
        rw [pow_succ,Nat.mul_comm (B^i) B,← Nat.div_div_eq_div_mul,packRows,
          Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt (Nat.mod_lt _ pos),Nat.zero_add]
        simpa only [Nat.add_assoc,Nat.one_add] using ih (q+1) i (by omega)
  unfold field
  rw [Nat.shiftRight_eq_div_pow,Nat.mul_comm j width,pow_mul]
  exact aux n start j hj

/- Evaluating the packed natural before testing the rows lets the kernel reuse a whole slice. -/
def withWord (f : ℕ → Bool) : ℕ → Bool
  | 0 => f 0
  | n+1 => f (n+1)
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem withWord_eq (f : ℕ → Bool) (n : ℕ) : withWord f n = f n := by cases n <;> rfl

end TensorTwoSided

namespace TensorTwoSided.Seed20
def x : Array ℕ := #[11, 6, 22, 3, 59, 48, 37, 53, 27, 47, 38, 19, 12, 46, 63, 9, 54, 56, 62, 17, 23, 14, 7, 32, 29, 16, 43, 15, 21, 35, 42, 13, 60, 57, 25, 26, 10, 44, 40, 55, 24, 18, 33, 45, 2, 50, 49, 34, 30, 58, 5, 41, 1, 28, 36, 52]
def y : Array ℕ := #[175478, 850965, 809007, 603482, 161719, 114547, 835537, 192542, 280001, 285886, 753663, 475384, 317910, 370876, 920527, 712856, 819465, 811277, 400931, 674704, 33625, 57376, 357138, 809839, 771047, 711620, 934765, 567055, 233066, 758744, 607245, 980100, 17072, 766727, 988800, 601793, 495912, 776971, 121424, 102570, 10570, 827554, 610929, 294586, 301215, 10169, 467778, 99264, 155507, 481816, 854401, 157012, 257338, 425916, 791722, 612823]
def z : Array ℕ := #[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 257716, 819940, 784597, 1048576, 1778582, 852075, 1176793, 1040357, 499502, 1467555, 1695653, 1912338, 187021, 130230, 2050624, 49448, 1744044, 437632, 1054880, 244753, 1129793, 989192, 744935, 525028, 106417, 1654224, 1313153, 2091887, 1442286, 2089005, 185315, 779301, 1360325, 1761378, 513520, 552456]
private def whichChunkT0B0 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x35f35e35d35c35b35a35935835735635535435335235135034f34e34d34c34b34a349
  | 1 => 0x39a9899398e98998497f97a97597096b96696195c95795294d94894393e9399000361360
  | 2 => 0x3b23b13b03af3ae3ad3ac3ab3aa3a93a83a73a63a53a43a33a23a13a039f39e39d39c39b
  | 3 => 0x3ec3eb98a93a8ea89a84a7fa7aa75a70a6ba66a61a5ca57a52a4da48a43a3ea000362000
  | 4 => 0x4034024014003ff3fe3fd3fc3fb3fa3f93f83f73f63f53f43f33f23f13f03ef3ee3ed
  | 5 => 0x43e43d43c98b93b8eb89b84b7fb7ab75b70b6bb66b61b5cb57b52b4db48b43b0003b3363
  | 6 => 0x36400045445345245145044f44e44d44c44b44a44944844744644544444344244144043f
  | 7 => 0x49048f48e48d98c93c8ec89c84c7fc7ac75c70c6bc66c61c5cc57c52c4dc48c0004043b4
  | 8 => 0x3b53654a54a40004a34a24a14a049f49e49d49c49b49a499498497496495494493492491
  | 9 => 0x4e24e14e04df4de98d93d8ed89d84d7fd7ad75d70d6bd66d61d5cd57d52d4dd000455405
  | 10 => 0x4063b63664f64f54f40004f34f24f14f04ef4ee4ed4ec4eb4ea4e94e84e74e64e54e44e3
  | 11 => 0x53453353253153052f98e93e8ee89e84e7fe7ae75e70e6be66e61e5ce57e52e0004a6456
  | 12 => 0x4574073b736700054754654554454354254154053f53e53d53c53b53a539538537536535
  | 13 => 0x58658558458358258158098f93f8ef89f84f7ff7af75f70f6bf66f61f5cf57f0004f74a7
  | 14 => 0x4a84584083b836859859700059659559459359259159058f58e58d58c58b58a589588587
  | 15 => 0x5d85d75d65d55d45d35d25d19909408f08a08508007b07607106c06706205d00005484f8
  | _ => 0

private def whichChunkT0B1 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x4f94a94594093b93695e90005e85e75e65e55e45e35e25e15e05df5de5dd5dc5db5da5d9
  | 1 => 0x62a6296286276266256246236229919418f18a18518017b17617116c1671621000599549
  | 2 => 0x54a4fa4aa45a40a3ba36a63a00063963863763663563463363263163062f62e62d62c62b
  | 3 => 0x67c67b67a6796786776766756746739929428f28a28528027b27627126c26720005ea59a
  | 4 => 0x59b54b4fb4ab45b40b3bb36b00068b68a68968868768668568468368268168067f67e67d
  | 5 => 0x6ce6cd6cc6cb6ca6c96c86c76c66c56c49939438f38a38538037b37637136c300063b5eb
  | 6 => 0x5ec59c54c4fc4ac45c40c3bc36c6dc0006db6da6d96d86d76d66d56d46d36d26d16d06cf
  | 7 => 0x72071f71e71d71c71b71a7197187177167159949448f48a48548047b476471400068c63c
  | 8 => 0x63d5ed59d54d4fd4ad45d40d3bd36d72d00072c72b72a729728727726725724723722721
  | 9 => 0x77277177076f76e76d76c76b76a7697687677669959458f58a58558057b57650006dd68d
  | 10 => 0x68e63e5ee59e54e4fe4ae45e40e3be36e77e00077d77c77b77a779778777776775774773
  | 11 => 0x7c47c37c27c17c07bf7be7bd7bc7bb7ba7b97b87b79969468f68a68568067b600072e6de
  | 12 => 0x6df68f63f5ef59f54f4ff4af45f40f3bf36f0007cf7ce7cd7cc7cb7ca7c97c87c77c67c5
  | 13 => 0x81681581481381281181080f80e80d80c80b80a8098089979478f78a785780700077f72f
  | 14 => 0x7306e06906405f05a05505004b04604103c037000082081f81e81d81c81b81a819818817
  | 15 => 0x86886786686586486386286186085f85e85d85c85b85a8599989488f88a88580007d0780
  | _ => 0

private def whichChunkT0B2 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x7817316e16916415f15a15515014b14614113c137100087187086f86e86d86c86b86a869
  | 1 => 0x8ba8b98b88b78b68b58b48b38b28b18b08af8ae8ad8ac8ab8aa9999498f98a90008217d1
  | 2 => 0x7d27827326e26926425f25a25525024b24624123c23720008c28c18c08bf8be8bd8bc8bb
  | 3 => 0x90c90b90a9099089079069059049039029019008ff8fe8fd8fc8fb99a94a8fa000872822
  | 4 => 0x8237d37837336e36936435f35a35535034b34634133c337391300091291191090f90e90d
  | 5 => 0x95e95d95c95b95a95995895795695595495395295195094f94e94d94c99b94b0008c3873
  | 6 => 0x8748247d47847346e46946445f45a45545044b44644143c437400096496396296196095f
  | 7 => 0x1301201101000f00e00d00c00b00a00900800700600500000400300200199c0009148c4
  | 8 => 0x8c58758257d57857356e56956455f55a55555054b54654153c5375018017016015000014
  | 9 => 0x2c02b02a02902802702602502402302202102001f01e01d01c00001b01a01999d965915
  | 10 => 0x9168c68768267d67867366e66966465f65a65565064b64664163c637603002f02e02d000
  | 11 => 0x4504404304204104003f03e03d03c03b03a03903803703603503403300003203199e966
  | 12 => 0x9679178c78778277d77877376e76976475f75a75575074b74674173c7377048000047046
  | 13 => 0x9b69b59b49b39b29b19b09af9ae9ad9ac9ab9aa9a99a89a79a69a59a49a39a29a19a099f
  | 14 => 0x9689188c88788287d87887386e86986485f85a85585084b84684183c83780009b89b7
  | 15 => 0x5f05e05d05c05b05a05905805705605505405305205105004f04e04d00004c04b04a049
  | _ => 0

private def whichChunkT0B3 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x619b99699198c98798297d97897396e96996495f95a95595094b94694193c9379000060
  | 1 => 0x7807707607507407307207107006f06e06d06c06b06a069068067066065000064063062
  | 2 => 0x7a0799ba96a91a8ca87a82a7da78a73a6ea69a64a5fa5aa55a50a4ba46a41a3ca37a000
  | 3 => 0x9008f08e08d08c08b08a08908808708608508408308208108007f07e00007d07c07b
  | 4 => 0x930920919bb96b91b8cb87b82b7db78b73b6eb69b64b5fb5ab55b50b4bb46b41b3cb37b
  | 5 => 0x37c0000a80a70a60a50a40a30a20a10a009f09e09d09c09b09a099098097096095094000
  | 6 => 0xac0ab0aa0a99bc96c91c8cc87c82c7dc78c73c6ec69c64c5fc5ac55c50c4bc46c41c3cc
  | 7 => 0x3cd37d0c00bf0000be0bd0bc0bb0ba0b90b80b70b60b50b40b30b20b10b00af0ae0ad000
  | 8 => 0xc50c40c30c20c19bd96d91d8cd87d82d7dd78d73d6ed69d64d5fd5ad55d50d4bd46d41d
  | 9 => 0x41e3ce37e0000d80d70d60d50d40d30d20d10d00cf0ce0cd0cc0cb0ca0c90c80c70c6000
  | 10 => 0xdd0dc0db0da0d99be96e91e8ce87e82e7de78e73e6ee69e64e5fe5ae55e50e4be46e
  | 11 => 0x46f41f3cf37f0000f00ef0ee0ed0ec0eb0ea0e90e80e70e60e50e40e30e20e10e00df0de
  | 12 => 0xf60f50f40000f30f20f19bf96f91f8cf87f82f7df78f73f6ef69f64f5ff5af55f50f4bf
  | 13 => 0x4c04704203d03800001081071061051041031021011000ff0fe0fd0fc0fb0fa0f90f80f7
  | 14 => 0x10f10e00010d10c10b10a1099c09709208d08808307e07907406f06a06506005b0560510
  | 15 => 0x5114c14714213d138112011f11e11d11c00011b11a119118117116115114113112111110
  | _ => 0

private def whichChunkT0B4 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1281271260001251241231221219c19719218d18818317e17917416f16a16516015b1561
  | 1 => 0x5625124c24724223d238200013813713613513413313213113012f12e12d12c12b12a129
  | 2 => 0x14114013f13e13d00013c13b13a1399c29729228d28828327e27927426f26a26526025b2
  | 3 => 0x5b35635134c34734233d338300015014f14e14d14c14b14a149148147146145144143142
  | 4 => 0x15a1591581571561550001541531521519c39739238d38838337e37937436f36a3653603
  | 5 => 0x6045b45645144c44744243d438400016816716616516416316216116015f15e15d15c15b
  | 6 => 0x17317217117016f16e16d16c00016b16a1699c49749248d48848347e47947446f46a4654
  | 7 => 0x6556055b55655154c54754253d538518000017f17e17d17c17b17a179178177176175174
  | 8 => 0x18c18b18a1891881871860001851841831821819c59759258d58858357e57957456f56a5
  | 9 => 0x6a66566065b65665164c64764263d638600019819719619519419319219119018f18e18d
  | 10 => 0x1a51a41a31a21a11a019f19e00019d19c19b19a1999c69769268d68868367e67967466f6
  | 11 => 0x6f76a76576075b75675174c74774273d73871b01af1ae0001ad1ac1ab1aa1a91a81a71a6
  | 12 => 0x1be1bd1bc1bb1ba1b91b81b71b60001b51b41b31b21b19c79779278d78878377e7797747
  | 13 => 0x7486f86a86586085b85685184c84784283d83881c81c71c60001c51c41c31c21c11c01bf
  | 14 => 0x1d71d61d51d41d31d21d11d01cf1ce1cd0001cc1cb1ca1c99c89789288d88888387e8798
  | 15 => 0x7997496f96a96596095b95695194c94794293d93891e01df1de1dd1dc1db0001da1d91d8
  | _ => 0

private def whichChunkT0B5 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1f01ef1ee1ed1ec1eb1ea1e91e81e71e61e50001e41e31e21e19c99799298d98898397e9
  | 1 => 0x7ea79a74a6fa6aa65a60a5ba56a51a4ca47a42a3da38a0001f81f71f61f51f41f31f21f1
  | 2 => 0x2092082072062052042032022012001ff1fe0001fd1fc1fb1fa1f99ca97a92a8da88a83a
  | 3 => 0x83b7eb79b74b6fb6ab65b60b5bb56b51b4cb47b42b3db38b00021020f20e20d20c20b20a
  | 4 => 0x22222122021f21e21d21c21b21a2192182172160002152142132122119cb97b92b8db88b
  | 5 => 0x88c83c7ec79c74c6fc6ac65c60c5bc56c51c4cc47c42c3dc38c228000227226225224223
  | 6 => 0x23b23a23923823723623523423323223123022f22e22d22c22b22a0002299cc97c92c8dc
  | 7 => 0x8dd88d83d7ed79d74d6fd6ad65d60d5bd56d51d4cd47d42d3dd38d24000023f23e23d23c
  | 8 => 0x25300025225125024f24e24d24c24b24a2492482472460002452442432422419cd97d92d
  | 9 => 0x92e8de88e83e7ee79e74e6fe6ae65e60e5be56e51e4ce47e42e3de38e258257256255254
  | 10 => 0x26d26c26b26a26926826726626526426326226126025f25e00025d25c25b25a2599ce97e
  | 11 => 0x97f92f8df88f83f7ef79f74f6ff6af65f60f5bf56f51f4cf47f42f3df38f27000026f26e
  | 12 => 0x28528428328228128027f27e27d27c27b27a2792782772760002752742732722719cf
  | 13 => 0x9d09809308e08908407f07a07507006b06606105c05705204d04804303e0390288287286
  | 14 => 0x29e29d29c29b29a29929829729629529429329229129028f28e28d00028c28b28a289
  | 15 => 0x2a19d19819318e18918417f17a17517016b16616115c15715214d14814313e13912a029f
  | _ => 0

private def whichChunkT0B6 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2b72b62b52b42b32b22b12b02af2ae2ad2ac2ab2aa2a92a82a72a60002a52a42a32a2
  | 1 => 0x2ba2b99d29829328e28928427f27a27527026b26626125c25725224d24824323e23922b8
  | 2 => 0x2d02cf2ce2cd2cc2cb2ca2c92c82c72c62c52c42c32c22c12c02bf2be2bd2bc2bb000
  | 3 => 0x2d32d22d19d39839338e38938437f37a37537036b36636135c35735234d34834333e3393
  | 4 => 0x3942e82e70002e62e52e42e32e22e12e02df2de2dd2dc2db2da2d92d82d72d60002d52d4
  | 5 => 0x2eb2ea2e90009d49849348e48948447f47a47547046b46646145c45745244d44844343e4
  | 6 => 0x3e53953002ff0002fe2fd2fc2fb2fa2f92f82f72f62f52f42f32f22f12f02ef2ee2ed2ec
  | 7 => 0x3043033023019d59859358e58958457f57a57557056b56656155c55755254d5485435
  | 8 => 0x4363e639631800031731631531431331231131030f30e30d30c30b30a309308307306305
  | 9 => 0x31d31c31b31a3199d69869368e68968467f67a67567066b66666165c65765264d6486
  | 10 => 0x4874373e739700033032f32e32d32c32b32a32932832732632532432332232132031f31e
  | 11 => 0x3360003353343333323319d79879378e78978477f77a77577076b76676175c75775274d7
  | 12 => 0x4d84884383e839800034834734634534434334234134033f33e33d33c33b33a339338337
  | 13 => 0x9d89889388e88988487f87a87587086b86686185c8578528
  | _ => 0

def whichChunk (i : ℕ) : ℕ :=
  match i/16 with
  | 0 => whichChunkT0B0 i
  | 1 => whichChunkT0B1 i
  | 2 => whichChunkT0B2 i
  | 3 => whichChunkT0B3 i
  | 4 => whichChunkT0B4 i
  | 5 => whichChunkT0B5 i
  | 6 => whichChunkT0B6 i
  | _ => 0

def which (i : ℕ) : ℕ := (whichChunk (i/24) >>> (12*(i%24)))%4096

private def denseT0B0 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xc6d14b0a9576ed2e38058efff7f058af856217863f560586c65fe07d4b2e268a7032fe166a4bf89785efaf38f185d535e4f9091eace247ebf37aa8932d86671d18b88f6ee4d3bad11c69b3f62156dafd665e50bc1b423f7d9db3c207700bed40f3a20ccfd316821888
  | 1 => 0xcf8ee4761c400315ccc7679b200d9ef0de4ff9d69a29d56f389df444bf29ec30f45b5b9c3ce6c44f600451c220a0630d4c112109ffe8461f90f875015267d910479282b2af71d8b260cb3a7026d46c1cab57dcc6d1c9c1102668fd7f398d884ebc87610af7b4cfe674
  | 2 => 0x52eb5a58c0176657bcbfc0dddc3f55b56d76e9c20a4c6e0c5c203ef180695ad008bfcc49cd0582532b8fd5902a23aff4d3fe8ce4f7847a9dbb1a51f5868ad3bd7cd8f449f653779b63100dffdd13d445c3a0fd4c008c22eee2760f30b831bebb958ec807cf3922b2ac
  | 3 => 0x58b5ef0d856202c923e15122d80fa238d372ec7c6df3ccd5df234783bb026970c3afe1285d7deba756ed63bd63cf0a8485e06e0641d9baf3f1876a77ef35af11b9f13835f3a484002c134e4979deac15be664427f8e231a411a90a2d5d1d8192ee8779c2b4174c7a16
  | 4 => 0x8217e5ccfd7a41cd7ba3789a0d2fdaf22f5a348de898ba3b6ecd0b5f065ccf600d0614fe2e6cef2acfab4d1418071634c380ad3610bc61a9b2fe3defe98cf8b1e84e48065a90641be203365583e2af2d97c3cc804eebc769bb9e34b026e57a5f8a2cd70c158d4bee5b
  | 5 => 0x57c401575b6aea746c83d87c4f29e4b3c93fe62e8c4057c531cd44336d91608fe83fb0484db568c62138f04de7d5887d0aa6fa3c9d29d1238ba87704dcf13e12b78bda493281c791fb7e762095b6832da5ed6988816b88cd8b533501c26eaa48dfd25bc515548d9c74
  | 6 => 0xc88a08ae1943188e246f4cd1f9de878dcef4e15becd1133b2868d8d58cb53db96ab129fe5a306061cba569f28aa5ce14afd991c2f972c8130587737847a15dee544eba2cf7782ed01c499f7d4d490be3a8e38c3385aaf0ea5ebae4a9e6d450cda449ba4f81074a49e1
  | 7 => 0x192b9fda4acc7556148d25a570cf699bbb46e706bac490a25a51ce8f7e8bb8cb52236a55d947b61c0083f67cc632b3512a0085ea1168590ee1e27e20239dbb807b00db2986026c34d0c79f91f2a476b992caf751ddb775c7285b1c774bc9499a733b18ed5e395b406d
  | 8 => 0x118d79d989bed93014c36c666388442f84e7a8259d3777160c70d5d44118195a8255de24a821b106a02a0833e1add5253fd5f01e47ea31b2f68a404dce91850486afbcb5b21b28d1037b4b37ef5cfa4df263dbe02bf4f60e483b3c46ac811de0b297f903777aaf89c0
  | 9 => 0x5d53cee9656df46291a66fe62ee59c0f3b3a75207cbabf869f7d8ac9c91afed8ede63811557a80a77e3c29b0064136f40e4e2ce203eeaa73e2c77ba75f68b76930a702f6c2eb4d859c41e6b6f421e7a053be95a988950c2ebce27c9b59fa29b20c67a0234e063533cf
  | 10 => 0xdb9dbe8ac8bfe76693923e43b2ef1da25c8420ca1598879462cc1d579558becb3baff36d7fef2d16638cc79d626f9e36eebf51ec7140ccdfe6a5d7ddbba23d7a0ea4da52fbec5ac570643f0e19a592c6a94cc610c2440fa584604de2fdaa9782e6bcc53c22794d1034
  | 11 => 0x68cd9fceb43094e47fdbf5da75ca56530676563bcb648285e2f5e807205f954c83d9bd2cdbd795b5a04417f2cb8e581e722cf03785a26f56385466d85a859ecd8f6d22de091ae58eb3df0305cdcabdbd1be208021e8d8f92548a994b48bfd46d02312837fc279cd942
  | 12 => 0x832f0fab3e25e1416f73e96c3b0e195b75cb80e0021b0faf4ad3e1feb69170442e51193de22f3207c61cc4322fc7a0690967e5cbe0f900eda399480099a14c0c1ee93e6794c5cd7a5c2d748325d8c6e659ec789b90ad0819cd6208cfa6778ba143e8715df407be808b
  | 13 => 0xf3533f16a995813e7c9dfc7d8f4b27fa3131377ad4a440d1e4f2efc5ba279860f8881bb7eb31c77103cc5a9a2e1189bc14859a2b3bb1b623e08211b4e6d3aa8c6f9559084cffbcdb3339bd36dba78a573dff7bf293acdbc749948151310dfe1fa14b06061acd241b61
  | 14 => 0x2f952439ef283d3c24b80277ea956d9f2b87e845aca88213e1e985fc5341647a2a6bdfcb87f15b9d40bc2be667ab502ee017eda49e02afa0f875ff2d6b69e8e3e28e43a3eb25eda840357300b1e37774f3528302ff68442ceaecbaa03f1d539edb03374345256934fb
  | 15 => 0x3d0afccd4b01b4ac9f6e020f55d2f852a0ea6e056a2e3d12af1e79149feadad5283d0c41dfab8a15ab11694e0f6c669b45999b01cceaefe7342d02eabd5821c40d2a0d57c2581d924980b8c594b241626a6a24cc6c010c0a8004387a03225bfb44224cbd22ba6f99e3
  | _ => 0

private def denseT0B1 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xae02189be48e61a7b8ab2c70e85fe6958107cfaa94d16acf1fe8f94179e94fd6baa0f2cf56359f3a8799d9e8dbd24dd8a1be05b9e3379e1c204c3c0b99c66d6dc88d19539ffa9ba2093ff131229aeaed5e966c666e64177464ec04fc5087de85c87d3ce843aebf5704
  | 1 => 0xcc4821f80f011079234036f8141e3753832636aa2a090c544b85164970c58dde0d71380f6b720ee1d0cd05377f68572271277b4acf151a311286ade24c4fd3dcb1237fb123b024defa6143a7838a9cec6950049445e9789f6fcf89b212ae6e3bb5b20e5716cc0257e9
  | 2 => 0x8fd639715bb51638d3f89dde61e7ccac93331ba02eb14500a4103f9fc8e049e330f4c066d11bc09bb700566e19ca2c5bb1fff1038bae5ab60b8f2e8901302df52605cf3e9f7b19b293a4c1962bd776a281f14e79f103308273205b0a0981e019389c9768a22d4665cb
  | 3 => 0xc82992abfc37c518cefc4584d8c7cff5ec001db1281bf6817635915f158005b9fe75f2fed690ef94bd07f8ce43b30ed1df1fe12252e8ab2c7d0bec4968573d3a18f6760e4ce7dc831cc543476366ddcec6353e759f01238dc07f2510c5e865423f9ff0516501395798
  | 4 => 0xf00671436c5109d5ce5587821f66439c0604abd784bac2fd481e5741f0d6bf400a8fed16da205f249adc575fb9302b62acb41a7af5218df6aba6b84315633e29a7956e2cc851e5931e8771f196f17462ff9b3e16b0456b4e8dc80e6ee0a5bcab7f8cfefad4f056192f
  | 5 => 0x40339a3e122649f599b88b2da5b986a79ab1eadf8f4e4add27c35693a371e6348ae27b7a1921f9749b702edc84fe7e3d6f6eaf7c9b5d0fee4c87c87cff4cc34d39513d235204dab1fcea39c52e1daa236d9a5bbdf27568f61769b747d9f91acee064266e0e1c7cca80
  | 6 => 0x6e93ac2c3bd778d4ebc8f201da6319ce7f2c43b1f85a30f718704914a2d8e01878b995f7d32301865188993be5bb0e6dba5495fcee3b00a6cd65ee203117163b4b8cc2af087b6bc745366f239745693e7bada5d381458c769459ed501d02a4829ae71f440724055394
  | 7 => 0x70969acab61fa53a22aca3fd9a2cc6fc0cc3308a2f2955c5d7fdd800de7c4feaebae329c932512e7c2bf39ac8ad39a2f5d827e7798875817d5060b88aa7275688f8f06df479c29618c9ebb5d76357d71da6cea25c85e7001b173d586925f2cad8caa295456a0fcf8ba
  | 8 => 0xb12072c8f89ab96e3ababceff3d806cdeeb53f0ec03f3688cfa5fabfb53fc6c247e32bc967432fcf33456f194758f1eb6668514726e4cf67497d8903b913c9530a94aea3a610e03bb69ae4c5ec95a9d194915685a987ee9038a4a0e9cc414a0a3b6f01a6929caa685e
  | 9 => 0x40171bbfc88b0cd62afb0df7e5632b50d59d7649f101491265c7bf4fc1800312c0ed31e39bb383c7bb646a3fe81b7eb402c493bab9012a9282b0abd5a4afa54435acd821fca4128be2c545471010c540d07f244577675671260f1d36512f9531c04661dc08836da213
  | 10 => 0xcd1fd55d110be2f48c789994462ee54ba0b31ddc38eeaae124c2e2f2c7cc67a7e85d176b3d3b6db4d86959c30ace1b627e3dca7094e70c7058441d0bdefc262a9a444a7afdbceb6f19ac0be78fabce0109657915ebd9507962dca83ac7af34178d3fee7753d1683d36
  | 11 => 0x460bc3ae1ae8bc68f3d6df8615f4a76c9206e664b10301b0f1543958e35e2c9b467ae851785edb36d644ddc273d40ddfee3b8a2a3e236e1dc65c072b43a9dfb480c7cd277b00f59bb9847189ce6df4d23e99f90f00d73e0a5ac152fc351508c42d9cab314b36801df2
  | 12 => 0x24486f3f7a5c197feba7094cc0c39744e0d0c0cf9d7982365bae43c055d7e6d4b51257243ee38b2afce225a5c7bad43c0eecb1dd1915ec3e645a1d83b957dcc22baa00cffb58dbd3ae0d12581090910135a7b5173896d5616fad7a818a53fa91858480dc67849a5cf6
  | 13 => 0xc383be62f0a16702a294c78bd321eee9e8bb1a35583c759404d9a1cf3cdfb2454e78dad62ec4422002a19c81593626635aa7dac9a62b5dd824ccc921aed350b37f2f6943b9725be28c98ff117f8d519ee961e2c339ee57f447562749110c7fff9123884bd54f0e9996
  | 14 => 0x9dbfc97fa4ed18b56baf8eff53e50c003e0dae439622f3fab866404b8dc6bd77fb85bce88f16374fc5b24d85990e97bff148899a2ad855cca8435af5b08c71434caf102e295c9fffacf5be9caed388d673f47223120c5c4ee693472ac8a3aa109ba5206897c48d2ed6
  | 15 => 0x8b2a25916406bcb552d2d4fcca97e861eabd6e1399ab9e72214294aa71ff1618c2d43018eeb6420c2c036a66e1b795ef7a6b9cf42440f908dde2e9d639a11c258524ba128e218be92e9a484ea31a2d6ef6ec924c9eb7bc1d74d4c7eca44f578cc0f9abaf048438ddf8
  | _ => 0

private def denseT0B2 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x8003c26a538d272de468665b8d1d506b023800d8ff33a163db5c3a8547e8c2654cd49fa9c4a15540c384e684654dcbe5a1da6e062a830a8a9a336770e206690713ac3a1297e8ba85a1fc394e7624ce0e873bd0e39fd3a7eb32200b19badf7f2737fb73867ac94857c9
  | 1 => 0x98e635ab63fe22d16fd1510a181b5b40b8c3da2dc549ead55c3217d4e53c5f354f344305df43da0480636274323f842b747d0c28a44f1bffb176b081dc425c619cce8bf9551b303290a746934ad8469d4f59410d014c2389cc602bf0bff62f81854941d75b1a5004a9
  | 2 => 0x4207dc71b3f783f43cf57b07b47a650ea3f10d3d95a1299fe8c851d2671af66ed1372b346caa0629ec0e22d9ef4227d0d406d550eb30476f17ed1ccea19e0b7fce70d050fef96863a07ec8c1d12c505aa9cc6d8b8fe0a1df34b0d47f820222c6c16c6071db4caaa63
  | 3 => 0xbf39a893361b4fa6fb1dbe4cd8b3bc0b5440f19c3c9c605a7f8100c8d2fa93edf6c588bebbe48afc20e8d2b20a807c77b1764f520401ecc02fea087236e876f62b928123c1f7e0f2165a728ca979e30746019160d9e0fa883c9e3f17a2f5816486de2fb26bcff42fd7
  | 4 => 0xa008b97c32f2db6ea9733b05b8d17320af865573639e5b261f6b362b01c529aaa7d6cf3b65e3de07e9287c6cd3519f75ff25858dd645a238bcf1f422be483c4e9c0d76bf0216a37760b60f103e060c9d09e82fc1c1723ba14272dd71fbb188c8c26ced0ba320f7b146
  | 5 => 0x1e8fa4a4e41e64b3153550cb24f3fec99458f7d2c57caaad5cdfedc1d0a9f38560403ec523740bb700c0eef5c1aba882cf9dbf2a194be5926c5651a2223d4fbdf756fc1b7242f57b487974316f47298f7ec15c8632f67208e74f762fad30a871ce815fdfd07433c1e4
  | 6 => 0x9db5bf0f56c66302f1a96adf5aee228915378cf8e198d3228074abc0fa43c4c26981d74d2ce32d5d9052e89919b35d1b664834b1b51a9c00b65925687117b4534c8a40c0ddde937e35218540bab9eff11f5beb475cf1a1a7998192f2756b76019a649867385a64de81
  | 7 => 0xcf48350b91322ca2e335c66afb6d188cb9829596706b61608a0b395c1b60c5475b4dfcd6f5662fe3a7e19679d1b7f1616f0f9e8f4f5b6cc8747886062aeddd338371704f503353fac95f0774673f90c7f7081084d856313de5a5fe265342867e5d1ab65c28e65b4e24
  | 8 => 0x11b68ba0dfae4cfe7fcdad5e012de671afeca5073a84b0ba0aa212c44c9a49c63322bb7504268e1d1473dd656b3f2359cf224828eccb032259a2ee0bb6f022143b3e21d0e177424dc23f3ac87b3b936ac2b515ee2d71cb2b47ea2bb3f52ff12b672689da474f5e869f
  | 9 => 0x2ee3ed130cc0a1ffd76e7097f1a8696578a9c4b1fc98a10e709a024fd739cbccdc0b3e41a3465142e8ff390ec393e3dce88205b3ed21be88b12c087f469800fc83f1be932e11e3444d98f8cd8657db38ff74e740d97ef17d4094bf895e180b74f23b37caa2799a3503
  | 10 => 0x3bea13ee4e14dd41f9c6ec2f3aa0651109915d2bcd54ce6356c50affe7d4e02e116f61aef579fe2778296bf673f4226bfbc5b97c7fe70b368d7c1b58f6659fd6b7d72967721fd058066fd162843d467a63f4a90c15d180453aa5c7f39e333159ef6b6714a9559fbed6
  | 11 => 0x22e63ed048e3a9cb448837986d3282313da0c99a32076d90f704622a331cf98a4b7923f6b0f4e06eab0e6bae8d1c2c0dad794433ee914d08f35be5672c44e7fb07f225fa764ce5ec139de9df411ae14272256da036bd0b5182c88abeb28fcbd7d2d0602a1dfbd9b79c
  | 12 => 0x7af073680cd253116a58df5bd018e598752c2bcdd9b2a3b38ec39fe1b8307a6e6a0179e7ce46a97b7364c2a735570574fa8cc16f0ef3f562c8517ed703a7267bf3665e7c8dd456119a58b635ab5a830870d8a1164c3fbf573c0d9463ae8ef457909687d3866993e9c5
  | 13 => 0x5bedadcebd9c9c00bcf10aaf808526c32707e59df5b5194ea4dd4721e929d186c32c7af6ed148e5c2fa53bd90fc506fc35f11fef6bd74e3db2007225de525d6b67604bdf2f15ff63cb04ddc85cc5353df6735c1c4b5f413c5ff3779129095084d95953af2046e14737
  | 14 => 0x951e87628bf64ad1cceec2ecbd74d766b998e1c065fa73a6e76239c7631bf94282406ee7ac4cecbedc83f11161b95017792f816df78cd6cc63fc8a6bc7a6d6ac6e76e30f7fcfb7cae60136e04a44caa37d7a3986b5f5993da5a35e7d4b9244e9e26ddac2c955d5f5fa
  | 15 => 0x9612afb7fbb455d34d52f593c578998ccefefe6dfadf59f939c19e4b417640281876162fa74be18a155c9cade46745ca96aaf05521a5918bba9cc9a3492347e859bca8ed477d455abe391a3d88ae08c4ab71797cc9788099b7977485665bacab2fb9e87622ab5bb590
  | _ => 0

private def denseT0B3 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xc580315b0c1948ab15695bd72fb44e97dae0d932eb683dda5e1c6d3b0931d5bacfb1b206b305d4a0b752fe9ef7425602bce445038b0c6df993effdef5720a5b040bb64c48e0ea1f577f9be588e7f2dcc902fef79dd26513b1938451460b6e91925a177e1632d86a6d8
  | 1 => 0xe03de608935df5575f590bb2efbac310a0c0ed144edddb91d9fedf97877f7d8a41b660327a19131a2a61cb2964986554ebbad1d8aef6aad4279d53d36d2be4bfa42d92200b6acd8eef65ae877e228605afbbb8035c5df9516f96d44ea61eb40b91a6dd9a82011acc9b
  | 2 => 0x9db62d693c63bcd8faa18a5be15534539627fa3bb6dd2eb546d1815137545adee3819475c2055217a1a4b61ec48273ae4ba997501c88c56f25182c5dd7aef0f42cc021f39715b595b65edca16e05ff16bed8499de512157978ea2bd930bf6e1c0f67df69dabec60843
  | 3 => 0x48b1978d992105bc221b5ff5d49da17d0f8830bca03ffe79dd11d928272fb4e9e453bed5cdfb661e5116851953d6898ece31ccd13b9c19f7f40403f34bd2f7a3ccd46fb5108d7d7890db80dd33992bf31469bdb830fecb55b7d860e820c296492fafeb462cf79e4efe
  | 4 => 0xf778ed78e8630e7c9f7dca00329c2ba59e99262797c4a3796b07254edd65436fe6ca45aa517c444e987df0b81dee6d5a8f8eb084a8b717931fa12e3b3d6902ab8d0b41c9c70f96f11c74209ef9ca403bf67b4f8af5dd7f9d3385fbdfbad9683cbc87b4dd2271143229
  | 5 => 0xe1387158a5914fa7ca1e9439cf116ab91ab380fa452d508f85bb432c7bf50eeeda3366b53c0c4aef559484e9fbc5909c871920245675562c401433a16a2d5c54a2d2cc7a162bacf29dd6542c9c862686f1232868e5c0822a6159b25ec93ec9b6a9515298a44469ab48
  | 6 => 0x7dc64b95ebace4ce2213024e6bb89eec79b150c9835a0b1920788226e2524d9348c3dcfd2997a5b87ba156101bb03eb3e9d5949451536f28df59b99a1885e68968d3d29f1fb6647ad91aca655da0f5036bea6d6352a1343c206e9e57f02a521eff571e6dc8f139aabd
  | 7 => 0xa719063351fc27cc44044484a38df171b8db4af77821360e6fd71adff54e301a7f4e58cbc2a7325e87fa567dcecb681fbd9741683dfddd518c72e24b2800d818d80c0174ec8250c4cf29c0e0266bfd25edf1ac3d24508894837a093ffa003dbaf0e77ddc5a90165811
  | 8 => 0x567a77b1f58c5e898aa0c36fa48a2a11bc3cf2d6ed21a073a1f8227b708c52575d8a42bac7dfa22a0335e280d0fbc3a567fb4b8665c585ad6c78cffde9f1d3605db0cfdf6f0e8b55534685ab46b69808a5bb0d77b2ec768191091829b07889a59455fcd4f12a26f04e
  | 9 => 0x1d05271a50ecefe11e3ab2f33973a05fd0773f72aa5fab49558b79d66c01856545fe443b3bdc6a94184213fabf48b9d95a94160968c3b871189934ca3f09036a94974ac6f8892267cecf5f315884488790e361f6d1c3956a8fc3574b4762f4342bc52c2f737c86c403
  | 10 => 0xc2cb4157709105daca2a90c29bd78d9a360fc29dab7a637d2fb97e072b9a6c32c765ebe6dfd97e299ce68cec9f9d1d7baa9f61e521488e74356161472e56ad39f6d0ddec94a5aa01d2f85d771e52ab38ad3b902d6ab6a53551a850c43175072051f5943b7c17e56e85
  | 11 => 0x2075fa396e7bbb6cb94823567d652e503122c2c973866f27d4ba0c33046a6399d5e524b6788b1ee1b5cdfdac24915e9739f5e0fb1cad2d30b0ec986986883ae9151f20e5adfab11c061ba2b6a2698a3c795db7151ccec49f72724618118e4496ff33af7a59897e6c07
  | 12 => 0x7d705e7008d9cedb96c950b072c9e4f87be4fc8cc74811a24c162325fbc526417ae8157c60be9b29129bbbe714a3c8e3fe0033f9a1d8ccdd6145f0b7e34186bcae86ad723314e74304917cb967c81fe39a933f86a6ae25c2f9d8afcbb0e3edfefe6285e8830f4d5717
  | 13 => 0x32de1871c97e5558ff1395d7425abe4d5628138456c079e947cc1933c3372e15979c49f8b0ba014f61d9a2e4198d3942f41355c21dc7dd4ad7526bcc82f50028d7c673f52f23122d4bdcc392adf3c36d83d93e4d4d094b121a689a132435f2262a36cfc60ee8649acc
  | 14 => 0xb1ae5238cfcffe219511495a8335f024aa0edbb1ae7e176741425a3ddfa1a79127949af73316d6144e07b603c33fca020e6b1d57195a6523453addff494cd5c4d25242d3110c1b7e2476a5ea8b5aedbdf22f2bfcee8a1d59fccc3e986793763abbc20bafbf5a7cf609
  | 15 => 0x12d1cb6aa7403fbcf5983e99e733a78a513673b43c674e4ec72710c3708055388473efe5a7d0c25e23ff17b09137b1462f886acfb5005bc895d2d3b6151751f43b142e731fa0f31e7aad14ccb28ec9f9bccf53df9e5371ca195de782811270b50e76aa4b9997880e90
  | _ => 0

private def denseT0B4 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x4db1fc9a8200a1555d3f2f38153de363ba91079f07bb29b39f7a7c18a8d0f76598b2518002f75381ee8b7ecf94760327ac07b51bf197a4582325fd4be3b7bc2ce3a751a901a176f3ae60357fc5f34582387d71794a298a3081652b45af2abac5c732d6b1c5fd375a2d
  | 1 => 0x929a75919147466a78f2a0cc9c48b0869cec7b3c0f4a0ac2f2da503721f3ec9e6d81811c2ba623a4df745a1a3f89c73438ba73d869483de71586e7b942ce0c6e9d57f77f1019d5d8fcdf7cb2b4c532b8b6210e7b1cbd16eef7b5df84d10943ab14e9deac56047551e8
  | 2 => 0x4e4d05ec063e8878f5aa96995294f779874af21c22e838aef7788682236687190ff4333a74d3e7af21f55c2dd3dfe0313500f4a27c271bee19952b1181a4936571ee3869030092ed3e2a8a27791904f9a63ce7e3fa31fc6c31a015bb6ce0136ac0ff73aab92fbb034c
  | 3 => 0x6bf8c13b88fc973ac9e27183d17dfaba90ab87243b3f1b0fa8d997880448a5553fd4a264e501d446760853dffd83d9992f42acd6c02489f30ca266249f33f6d5efab3d45807fdbe8fb38652d3ff4be2bba4562c4557d537ed1ebb949a4728d5717d951aeebb6f289e0
  | 4 => 0xf8894be7d5f121759e1c537d130d8e29d9f2a95c999fe8bad748e670d8b27a9b2ebef5df88fcb45a9106e2ff671cc77a50236f9dc47ef3f040c4be919f58e05d3f3aa810b7217f79c1faae2e31e48719ced089924502984730592f4442b7fabecf22a08ba972f3ab56
  | 5 => 0xa5cae203ec8241e19f744af84a2c7cdd056d4c64bc92def184fcfcace07d46cb9a8b1fef08912f5d66c7989b53c843e3ecf3bce28d1615216a8e957667dcacd62866c3582f5525627944ff46425a09d6d7cfe7cbdd508e17fdb6741ac375e3c1c628c41c17e1720c93
  | 6 => 0xa1af8c679cf39c0e64a30c761e23d30ca2c2709617247a2cc8a5a198d4095b8249cb35badbd000a7c1393f4459964585f5668a594b56a9a037c6f5c5f79117671917b310e51e06a5f48b04a71f0d1d85f7405de4432556f0a8716eba63d011555770b3460bee3b826
  | 7 => 0xead5971ff0fd8a9fdcf92d37ada72101853f5fa30c4f08588d32124e21e5bd15bce5ee59e0be701b00c5c4dc26b6108bba6503569bda4ef5b5a58839112b12d75a751f2c6c63e47b9150eef8da305a5a1a5cd40007f02bf7d128d0a82066929569a9944a457f52f19f
  | 8 => 0xd5858741726db4e52d901eb1c5a769df9d7ae5e5eea6c029234fba31316c488b820cd0ea4e21d4ab8b05d9e5c646de00b674883f88862fee0492b576454c5e75b31b6e8f1e41081966a415561399a326913d8c6372c68042b9dc42bac0da9da9872e948d8e37924edd
  | 9 => 0x4136791d7b097ea59221b73c5582da20f34693e0493119a8e00fd1fc22df15eaba287bc063c00510130960c94fa6acc817c548105a7f2af8acc279b97517834c488e64095f3320887dfd9cb145c2582f7e3342c45cd1a1d29ad04f214d882e7af3127358a59dabf3cc
  | 10 => 0x4836968956d22a15b43e4d5807f143af643cf6d6ed356cb14d41c494243cc77e5a8dc798f1f4b69025c4f8fd1bf2f0cb2cfb8767e7937eb72bbb1a29f5fd55ee0eb3f0a2ec9329f192262b184e30d67cc1fa3a59a6ffcdce15c6e916e8de29ed157873963d42a12b71
  | 11 => 0x608f31799b129dc9a51aca8f8cdf64410ce41939f07710d3a9ac1c0e98de6833645bbca2452ee558e73ffdae817c0385252dd6cbe84333375daffea9611ba0dda579360f85efeef5b3d92a1b69ebf4f8194897adf0d92ca7dcfc9eecd3585d5fb3c33f945fb1e6bca0
  | 12 => 0x1cb4caaf4585eb4d15fad9509be0df9c8c0d39b026e329b3417bc48cd6e04d3ec179a8fbed03fc09aa34d710c7ef77b718cbca1e30e1aef0afef598b811db0c768388a56263d041bb40c5138d650e5806fdf4fc4166020d94b24a07f2c4badd25fcec81526fc01467b
  | 13 => 0xb0cb9ce7d6961f3be77eeed47970a0c2a1acde8f672f5d58f7419a830c85c5cc81560c567bc6c455cdbde31e3e386720600abcfa8779fb770306a6782c58dba200c93a8582717501732aebf5650a352b5a96f569028b33b9ad6dc9112deae83c509ddf8cc3d73a2d8d
  | 14 => 0x768a0aa15fe42f31e6aaeb09f8ce767aa26451759f85b101bb9cdd683d1259a10e1a723f514e046cf9dbfb7ed95f49e7c2b08e14684fc7e4ec3f013e1cbff06c30e3ba8debaa52af67cdf64dc78d831aa4d5ca6431c472f41103806e10ffa6ed1718fdb94ec828fd83
  | 15 => 0x9f653f759d94320679cf26984c32d6db4a6aa5be21cecf6ecdb6c57dd4d72e118ff66469551bca3423835511e4d882400052fe7b2a08dfe311f2b9c8de2d45b2659a93d0ed412b278d6d2fa745d8cbe68cd19763b1695881a5f8e2e34fbc1f1c9f2535a4a66bd96bec
  | _ => 0

private def denseT0B5 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xb3ac4e82d3df3f0b061e7ba998c866d9df6d8519e5ccd86e71f285513851b80def77ca3e8ea786868af552446006a0c7330b4c378d861a137f04e4f4333650ce10eb6b4bc2f5757c1642ea011dd0d2f88a1868d87db7bef59ab658c9aa590393dc34422691a7859222
  | 1 => 0x11d3d016f9b487c0a0dfad80b086f35b06f0f39d8f269744baccabd4bb83e9ca84d7d51758fc13d106468663a4e70aeb24cf213cbc742ce116b447cb637aaf60b8c2414388c0493598f22ad80b0f0bda84c6ff9bb313f83cc04f87182c9728a9c97ef88fba01e67126
  | 2 => 0x273cda5bcf97ad61295040e852ffdd279d226eb51aa35815937306f0b616f38573d5f3f05512635b87f338c37cab193f9427271a28eff601fa4e11826301fff1e576ae11b8ee91b58809d9223d7446f3d63be81c6fae44ac79a40a95e4dcbb8c433dd67875d40e5b9e
  | 3 => 0x3aa21025568fc031a59cea2f5bf7e9161b05ed0e34ffa287daed2fcbb8cdf239b1fef4cf44ae657353d6eb555f38988add033f44520939e6c16e12501288b0807147b54727bf61b72a74cd36437191b5cc124b6468bcdcf7145f9425d35cf81e8b4dfc0b3869ac9b7d
  | 4 => 0x42a818b171d51f7ba37a05b81eb24d26adeaa57c8805a65cdbdeebd0243a19856379c2657228dee3ffc1f85c6b5be96b86aa9ebac00504ac6e6c1212208d77631b96fca44836016158d1763f54300ba550237198f2f0671a1614497c54241f9a3af414b93e2d430080
  | 5 => 0xc1e43db1de3d51144e4b7076439755a5e5f6a7c4ce1256a22644d37616255499686d8eafc2aa410f8d42ed1c035631899eda41d4d97fbbcea833b375e9481d74df1be5d84a12e91ce9446c63043f3ee5500e1f7fc8e6624020cfc318734cbb935096ca91e86d326b3a
  | 6 => 0x154bb1a8d959d7c499061264c3ecbc4c8f4a313b238546e8b4e850577613de9de4ee08fab1241b4de4e9239f9867b3b7bbe15122879d519e44cc8da17fa399d350ab58ea09fd12b46d72664d0b5560baf5d3d3585e9d09297338623d70b3b5fb57657490994182c700
  | 7 => 0x2fb213bb683c4e372ed5cf4928527b8a40a07e4a8a96af8652cbb453fbbc53c78ff32fe96cd4084c7952526c888d467a8c366330a03bc71ef6131c9db023217db2ea8107347c35db8ef0dbb31dc0fac0664660cc530b0210d50ef56fbac8dd61fbf59dd2038f6b9048
  | 8 => 0xe0c1bd94b58828830c194ebbe7d8e931d64d6f12d076a785e970f635ccc345566031fa4e44c827a8c7101731501c704a113d8ad0d812f9977d3df31cae6827f572fc7c9dece647c97a770fb11557f0c38f0a6725a2e06f174b7f9933acdf90d0e15c088493b33a006e
  | 9 => 0xe5e22eff3a419c10f12f11dbc9ccaacc45f98a25cd22a5b8c90a26816d16e0f8249b4da67865e9bf7f49fc8bc9ce8345469dbfc2483d36aca4bdcbc7c0c18bd70f429df9b9bdc2534900aa90d817214e540cf68dfe94af5a15964de13db38c9ebf4dd0186d3656985f
  | 10 => 0xbe0c3276bd591552923deefc3084f3b0b5e69f26ee241cabe93e831b5db158ed2fbe5e14956b80c61ef1e62ed7eb81cb9707b87c492e34b445f529c1c7487bc58da0937a62760346217bc55f0db5032412874c3bd5ba67383f68d9953dcabe1b1d0a73d0033f940721
  | 11 => 0x678c82d4a0b73156fae892fa76fb62554e440ef59bea7bac4928b7b2fa8f8756b98ad7f85f13d77f73c5596ae34c51b475aab2470b4ff78237a949b2b817a9fb85a050061053ef2b1dfcbdd4fadc340cf5a4f05f9b22dc84935afc207846f36e1a97131d73e8e18e02
  | 12 => 0xbf43bbb3e4637faaa0bc5bef4b8b91bd653582ac514caec6e90b5f11b808ebb033126d97acaf5c4eadf1f9189257253d6967dadb9d8100dfd4bc90a2b4d6a7dc435cfd420b17d97e0ec14b38369df939afd60d141d87102681c9d4209facd600de890346c7c5e4a8d9
  | 13 => 0x2cec63ae8b822db4fb67cb35661c504b432949ca674ea747ee414f8665e98f034a4db51fe1013decc20122d279ebe9b2e4bfdb6d2592a37b265d408ef78f44ec3ec0af9d8cfbf9287ab995af926fbae704feae585fa0c07aa665a024e1989baea11430e9809d23db4c
  | 14 => 0x93b9446f8ced7b3c76d2ee41e0981bf879f9569a81ac5a707d4697a69a7e2e640f4e43ffef93febeb3cbbffd8241c0e528e501377cb4586ebc79deefb2391e042cef396176eb1d6510926fdfe1eb7afd714302b1dc0c4f7046850a44bba01bb5964a179d07e983e319
  | 15 => 0xfdf214bc4b10b5b4a7757101f78faec0e55e3466731d25b9648992b80a845157c82a085c9d57e6df67e91b5314b75da50aaf158d29c3e182e4ff8235c7db5fb026adfd6671b5da417cb0fd01c17df958ed9b3dd534a2911b14b65db0f3962ee8eea2b706fafed5f429
  | _ => 0

private def denseT0B6 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xe9e4ea4fcc0dc22593ffe832318e43ab2524b53f064cbee86fb409186ce77ff40b1b46340743837436ccf18431a21ea417157a0c0ff58453625067a320e8b286c9983b3c76847aa3a6c797ef82a97a6dfdc7b08160fb5e936464c9f8457853d61a40ba4607a8a779a7
  | 1 => 0x2a1e597ba318209ff0570c333456110cfbcd67791beb4068defc4a8dc8bdfad0e58f8758fd0a72a944631aa3b4f8af55b3afd787bc9fae8181410d38b6cba50422173d0cd177693de78610d4b92548cc929a69704485d35e2517f64a3444ce9a06ac958ad95532fd03
  | 2 => 0x9333057100ab836ca2f1a654a49fa1ed16c94e257a496099339fee4626d3ffba58ab96cfa7dc3f510a4a1c01ffc75b9a91959d450bbaf71f43b7b09bb4cfccd15939b30f6ad9964881fb870c15e924132e131a76650d413e1ae8cc3cf52d9170fea7f13d0974c60e72
  | 3 => 0xd8768fb9a5387457c5ca979907c35e67c267344bfbb447ea0ccae049b07db02f15e0abf279396bb701033738c7cda27ada0abf5c9dda13be769c61c8174fe7a97f70dd2c34ff7ffebeac155b9f6fc51233c3a893a9174abae3bae14ab302ba81cb5c0b8de9f3f01902
  | 4 => 0xd118623e336f444d145a7b2eeebb86026c4611138d6b2fb046d010319a4b2f7ebae48c62ec52982121830a349e439741d3d79cbef8a5e390abee9f0897ff1084b1b97b4c953d0f1e93f7988e0a0b6ec4e791dd8d875d66348ca260a409f87c93316d5346d55c65e51a
  | 5 => 0xd9556180dfdf2428f1303607f2dc123278cb47f240703529ceaaa43e278e4cd603a38a865c55321a798053d85bf406127c8c0a72a8193be28cec96ed3a30b819518d4bc307f4e4573e915812ed3a9c36d236d0ecc30e79eb84dd14fc9197f4e61dd4c81bb8b143c0c0
  | 6 => 0xba97c9b9ad36f33fa1fc42db559459da6c90b06bbbead168dd2f32a996b6795c079fb8dd3cc5d5b9a82dc9d2c568766db537b0c8e2209db8d6e8e66980b07a149a2e9f46a8029ed78e8dee53171388599145f66ba34bfc3ff24ff929a4d39fefc789dac214e7614613
  | 7 => 0xd71f26f9abf8d2eb9579212b4b109567b305fb93a3df1e2975b844daa86719ce47569d9564bfe8d6260d8ff40c758e02544be338d07cc6999f1d83b47b4b6fd3342c80f9ef2234f614716a51dc2d75f3f477552f0999bf3b3914d40fdb6320076bb3322af05d643998
  | 8 => 0xdb8b155db9e6c2f25a0c18727d485391edd744182d9ee7b3e2d67594bf846056de0559ba3a7ae995bedf4eadb65e3591754bdf64a80d7e898329f272d8f0ff3154534e7476a7c72d1d3c0e41726734926b7a592ea44adf550b3cebf569baba36d7dd4b7c53c93b6e70
  | 9 => 0xc51d79bfdf6f873d7fa7333a32d518722268fdbac7f83ecef6e5378c7edfac0131df3a4c95c6d9b3e59a219c7c46a8caa149966ba0ba6dd65d4cb5477e43065651a7282337d56725d540f989aec96efa2f0999c26b34762b1efe9a5d2e679868fd09b49945b5fa0dc7
  | 10 => 0xaf1060ef8c83d96d18e542380654913291dedcdd8baabf00433f940596b44ddb58173decc66958516acc44fa46de82c497084616dbfc8b8bd1b1d12bf4b5591fba1d2d2060bce68d9569549b48533f502239e1c8c5e092cf2509beda9d7125e0876fd1b2c01d2bdde3
  | 11 => 0xacba79a879bfe7346d7cd12026138648b1b0fa4a26c2063b2d47b391bf84e35b97dd3902c3100b6fd13919c31aed7cd95321b33d93ebf65950eb0509b54ad27b52510d8181601b3fd6cb809a7c8ee2b924ae6551f3bb004d24366481df538825764ff84ab945943b78
  | 12 => 0x2a736238c6c0c12973e35b2889bed3aeef1d708624026e04277f182533f45142b1ad05cf65cb7596a629140d29e6eb805c56b50f48ff31a91b59891fcf7c90927b74c0615da32e146cbf1baf1feb701e91d1881f6cb428b1c1716b481d1337d8abdb12aca06286fb10
  | 13 => 0x81b8029cf774c7491e6aad3ec1a06439480379845cd8509561351534f4f84288ba3edd3025c23a6459336ecd8efc45516be43c9a0f2f4fba25cb9eae4ce89340e800dc156c5ad0d00eb3a648bd7e325b22f385f273fc0f814a2b7202f1910a4e1f1bf2e9e7b64578a8
  | 14 => 0x56242ac1345b5e01875f05b4c383caa2fa515a810914ff4d98382ea264ea972e090d55cfce56d5c62937617fdb0636b2b2ab30af1c98ae96c8350799ccc57b376f14e555ba9d3178d353785f01bf8ac96a2447fe640aec7e47323c445199f9bde05bf39646d8106c32
  | 15 => 0x5c14c30e58d77cf1133262c618b6feb4086da096a9105e80692f21ff2d508e7fdda20e73d4d4a7a2b1c2a9d74f99d774c07c634bf5203f02bc093d7dead82d7524a726183c655ae113d1d2e7aae03333e5075852a6ecd4c07db770e2b079e1eaae8120fe941f03d68a
  | _ => 0

private def denseT0B7 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x8bda196ded45b6cc13061cf788eb2f95dba775b0fabaa5dce3779acf1e086718078f943406a4e2f37c1e05534c597ab2f63e5180e4bbaa9bac5c6c818b1680228fe58e3a665190b1a58132eb72a74496a1df42245d3cdc1501745ab84f8336f94685699706ca04d184
  | 1 => 0xc4053fb74e9b7dec2f1819046ae099e5ce39dc74bc3531de8e499552a3df9f6c6285ce39186a17ad52670e81d8975b5ad38e800105a510838c47f10fb24540f15c538854e4bf3ecb9a9e2e324a1c2a4afe4ad32ecc3aedd3b42602ac20ea7ede29082b2b0e02d39075
  | 2 => 0xc731c1d5190fd8fb94d38fab1aa9da9226e1b57bc6521613a642fb9de81edbfd16c2481e63fe029a8b72976f772d281350749afc4e8d201d44f806c45c014e4eef8fcb11c5ab54f4d5446a970f427d91e2fc841aeacf6644a82638faade8128b9a26ce0813f61b71a9
  | 3 => 0x4558da0c4db9e10cf750c536e12d2bf78d217ef3edc9d79a1870bc50ca6d0c6a49f0a4aecdcbb7b78c1a8a3eb8569bfcd10170701a91062ecd45cbc03dcc9da59930c411c397a5536eb73ef791bd69488656b778ff1409dd40ad424626726b2f8f9d2ad11c6c47b8f4
  | 4 => 0xb535c4ce2806feccc76a85393aa9c307b1fe4549dd3b4ea76c762cfd3d21c74e1348305c4c0090734c1ab104bdfb6ed165e8d1a743f0d9c14a165e0cf9465c89d5b6fcf9a54fde932db4153d9a2f9b70e1efcaac2aafd8713f6c35f0aa14d96ea84a5fb2e38fa69eac
  | 5 => 0xa64b79495b89637fa4eaf316d53530ae45aeef377cbf401ccbc4789ce831a12752fb7c07bc97c5749dae58df018a7c7dcd2fe58b32fdaf4242ea579e9899ff5249a9c49fca6481a2a35482782ceefce3b660fa33143ef40d9762c3daec59209f9036af74e3072dfaa9
  | 6 => 0xc02357a6f27df7e53518adfe51471a76f287e11584dc9133980c20b80d4d16c6b346d9fd9b5589e6142d1eb3a7ef2f308951a2d70d97a2e2c85e1303be47771d9ff7e719bcd53317a02f7c5e41c03ce4781643a481c2ca1ed5a8a38ed9d88ed95c175ff3139ad7fcc4
  | 7 => 0x2f3d807db79541135346c459939987ae0314f1bb75af8b77b5c8df96eaf7d92bcc77e27dc9eb562fa5b169871bcf875dda717e55d209c85e6f0a9f5c35f3ac8b44871225cc6c8b3396e30ff0cf49920470f93f9a39d09cbde06703371acf700f7b491169efa4691272
  | 8 => 0x182da350a31f7125c662fbc4cfa6cea84cabab7beba40daa754b780ce2e5daa77b05ecb33a217daeac0bd33755ebc33d1c12fcb14a9822b6f56bf296350f92b4d83aa990566b1ac5b6d75daf6c6f00ab95c10e8511df7f8623279a3b01efc71a297fbcafccb648cb4d
  | 9 => 0x6ca9740aed0f3d3c1b559731d747fd2aa0237aa68ad52fb8d4c0194f23a9fd1214b2b054bf690181c5fb2247e54e88d9e007035988a25be91e86e48b309780d963936d7bd9babc0487908386b212708ff9e83ce44d0daad07671b2cb321adc2672704f7f9538e4d68f
  | 10 => 0x3338f6f9c23a46dcb942872d647c040e164a233e630e85b6594f3ed36a445a0eab2160a2ee89b9bbf6f06a21ee82af847fe66246cd5010ded61467a5716fe25ce296083ca7582dc0fb373245118c360164ddd4cf44ca6bc2eeac4601004404eb2b25fa1847d0f7466e
  | 11 => 0xe607d9fd1a37f5c47a98d9e61e57b60baff0ad4d4e18ff3bfa0ea6c127eeb6efeb2f231bb27bf3c86e534b4cac460acca2d0c33b8f98f8b450fc36e724e808ebaebe24e9b9591e75cc771a2c048e484f970798b5a6cf400eb186c32525ff0ed312e2b909bbd0d57882
  | 12 => 0x7062fed9ba07eeb34bac05eb81e1055141cc32d7f017edf94612357a6b56a1c87e56b1fc1c75982b93ebf1f5b9d4d9eafaa5a2585a05a87eca9cfc391061630678697dd48aebec121175156154fa1874bb6839637301e6a457ad4252d44341b76751977cc6f98fbf9f
  | 13 => 0x2b5d9728b7f5f01725ea0b583a04f4e76c4ec129c1d9e87833a440eae051d02be705757e89d50cb7b4cc0fdf9b51ea30e94785e9adbd7d92e5b438c23a2959433f9b8eeba9ea1d3ab7f5e3b5278464fa3152184856d6a322a6748e7b55678eb13dc9ea16631cf0b1d
  | 14 => 0x86d63c56680da4ffb8bb205a2efe76032e92f75d0f5d99e5e1dd83746d49556eea2479b5ec4d53af51308ffe8877ced2a478541f20459631b58a9a7d17f943a34cfd8cf52671e183a71fec3e7592586c7b84df55a4a7b766d520352e4f771f1ccc5bb76a009c9f8ce0
  | 15 => 0x23f282122e8065a9823efab93a7c027c4d3c50ccc8994d099ff6a0cbffd6daebbbb93664b806a5acbc24bcc1a78d1dc7eb7fb2bc52de298f894898f5e2869eb020cc3b48fdda8b6c5699feef31fb7de8abc9e6bcb219e1c297d0459b15a9343b865a13f1ae22f9d5fc
  | _ => 0

private def denseT0B8 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xe7c6e73b9831e30ef6b5d9cae334dca741c076d63d826e1acd6e14d7b9895ca6a9768507e8e63b8e53fa9d7b77509e35ac157aef1859229465b185c8109ae00af33202a51d47fb9dbf9a9393d1271cf894d335b276d7ca2023c5faae30b9b9dd82ef7e3d1324c674d6
  | 1 => 0x3e4d74d076184063a9b2c319ceddf89132a051477da8f3988b6bc31fc8f3a7dacd7207503d0e78b080fad0a1edf212acf973c4930bb8c454dad184b7d7d0c6170c501750ee0f2f9318f6e4d7ee8e4d0df5b2e177eca8a98c2529bb19e96e6301d1d65f29cea9add6fe
  | 2 => 0xcd0b7da89a23712edbd778957537ba484f1415e5b91addfd79e383f25b22e8c3572b2b20df75f021913b8b89ff1d1eee218da36697533deff9101d7480b7ea1c9d15e50b82cd816a4c7d024b656a562ffb728127132b6eb88aead4bffc0dc721c3ba9a28a0311181bc
  | 3 => 0xfd613ba12547ad2d3657787b689c2c062d492db275bab2a26a65d778594e9f38729fc0ed37ddbe1bcb4320c3b7422125a221cc91574f6bc6e0321c7661c1355d3f409289499deae810953958dc0c7e576cff6d392fa64d301a3277f542a6064d97c0ef848beb47dc1
  | 4 => 0xbf393c9fff444b2da0a5a7024a9f4ea3abe3898131b6226a813c34e2099ac49dbaa1992ff2ef3f3eda9252d37b36364479d356ca468a78534c72bc46e0c43059a648e66fa34376640c0c39713319912f6a0dc3b4484e347504670debe7ce610d34be45fd343d92900
  | 5 => 0x107ef2e6af3c7536316443d8f5a288ce7096d7b4697f81a7319c0632519ab45327a918d188cc328498d022f78682c2a40af2aefdfa6858c28218484a67f46dfce6628a5eb2c07a56bf6988986377c107e854d0eba0639ce216c419348a24f13aa9af1ae53f9b6e3ffa
  | 6 => 0xc0b9830af782542bb7bf9b89525a2211eee3414e295da52deb9940e6647ac14b11c709e20c08cdcc546d37655782a6cabe315bbbc547029ebac695db57e984fb37f7a5a91467c5969e0ac6e60dd8a38176fc72d8976d691c09532b55ff2310ea164ef419f4ec9a352
  | 7 => 0x976ac00994405213edcf863bb75890a09b105aa9928c0df7862e78fefe2f51f16424b4245f53c97311b54d8f6b68ceba7f6aeffd72d4b5a12c2c1a3d5398cbf4dbe72716b9d4c9ae6f8671df7a493bff5cf386bb808521eda3e44be5162d864e1b008298f52f02ed67
  | 8 => 0x1667e642e3b692b19b875c3d1e33f624f637df52d631ea8334949936b4d833eb38349f7af41089db12122213143e0637279ed6d7113b7201b41e0e8241af40f1d860231d2f5d78020bce0a80d60367e7a503d4401d59e69e24f78ed16f630c52cf5b719ec1af7982d1
  | 9 => 0xdffdcfd6b989901e3e162009905be2092d7ff4c754edbbefc44ddb01e4154e184cff96c9a0cc352809617e9a95f06f4c1eb3baac1b21825d1aeb2326435b4411238af586256884efcea7a56f69550201f6a84175020a6ee26377b7cc47625a88613674c15ced38676c
  | 10 => 0x5e77e55a0abd87337a56eda4652e0b2d32ba1e1fff68072078f44e9cbd318a63cb95ec8bcde76177dee4af95fc08e63b53d34d1c423d085a3d5c7189a64be3604bbbc476c26722d4628df78cb7a5a4b103c58b23d090806cf7999f7633291ae11be491e17f031bda1d
  | 11 => 0x8041bce22b6aa3b0de0c6c6d37165d2e471ce847784b9883f10be13bbca3dff79d96799dfc368ff72e6fc79438ed4b8b31481d34332ba58f1bc9a96d832a3633e037f55c2d465032be795240d4960387064b6e90c409126db0975509d6a18136dd146038cd5f2f18
  | 12 => 0xf5f6eb737fdb4f905d592e0891b6715353211eb2259513b00d997650975ba1f85a74aa5e0986f3edb452b1772fe30751b1a85286d33c9e15361f43dec366a2f059653a9bbb1bd5792fd53ed998b3246c8018a14fb086eba0fb21f3c085bc99162c9e691cab9287041a
  | 13 => 0xf14581e8d6dc897802fe80f75fd75b09312617b9f0a43ebfd90f03415af169ef391bf306f65c7f8f51eedd0f40b7ec282a314981c96bee51f92a71f0b921b897910b71d2e020392501ab9a58c53d42f0846a29e103543681fbd28da1d84f660dc0621803d121db6dc2
  | 14 => 0xf094effd7238bb630893abe8867bb74bd9d49cd4a8173e91302ff0fb2286c259957f597e2ff69cfc3b828949d125cb30e908a4d77d18f9344ae258394c73f27bfe51828223b4b5dd27f2c91c1f9d260c8709a70a053e7233f75ebbc419662ef0b85a44711920ed17b7
  | 15 => 0x7de4c6651517c6a1309791e9bae0ba9980c2609904b3377635abae361d927e5628f6e646f2991fc9adafbcc4d861b9690cdca702d3e930c9815717ef605d0c94fc274a76fdf6467a65c35ac744b526e995484cde8cefe9d9e7fa91cc45da7cfe89e1470421e9451ef7
  | _ => 0

private def denseT0B9 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xf51022511dc49792a87325fb4a2af1eb21795af9a6b1e1c174c1b0dbdff210ff05095c4ad065d22f84d93def550f7eab1442bb0fb482d54a85d9be14304324866eb14453064f1f1a652488bf0e5201d76a4945e4b8b59c9dfd45913c2d3554d36cd0d14897cc78bcbf
  | 1 => 0x63aa4ea0d257d9afa0db799fead0e06b02b93424ced1fd2a811ae746e467f5e24ca8134ef4a7db6057cceab32e31192189a8dc951893e6b2f5cb95ebd310867287fc68c0f874768dab94e1224d2ef2def76921115a65c7779ccdf067e130344f616efe4cfc949a9260
  | 2 => 0xec9e6b83c3ce6bbb992e843380de9453920302b85b801ce28d19083aad4224635f4b551a29b3ac4410c6d5a70a404180d4582da8e1d8daeae102f02a979e8e435a49dea719bf909c5d9c115053c02fe355c656b4a21ee4403bd4c633de9ed0043d236d06246399e364
  | 3 => 0x39ee191b7b0f0a5ee51791ea5bff4c25af669e174968275b688ebaae04c6a800939555e35b600cd8068f675f5d8eb21898f7b6b306d537834aa652a8664c0f3e655170996f8f2fb25c126e89b5cecd9b5111e2355847c3856deb0f08b4ecbeaf0be7657cd1c391da9e
  | 4 => 0x9e99439b7e4c3928d8d33c6ec338649df67cb0177c1719f66cd2eb13efe113b7419224f381ebb6cd8485a16f5f6aa80533e07b1f80e73b12d31e6da84d7b25ba69ff2da1c4d998ab49761a9f46d066e793c1f044f9cc6b59008fcba1443f06b301f83e94d2024e6973
  | 5 => 0xa2a04d873ffb08eb9ff5f1087e7a0b50e047f71f54ada7ad8009c0b5ee9657184a5609404e94a2316028859dcc473cc19dddcc3858edaa637b8b0120595c1a54320ee6936c04c2735c622ffb0bb3d676717060e24737e8077e3c0189cce7ff3d594b1348287f45784d
  | 6 => 0x365df21ddadcb1ebef9b3f1118d5c98c719b487f491c0fe4b1b132249fd13871eddb0c3ab1e642f691bec66a5ef8bce8a1ffb55bce441213bce3dd53f6dd408e5fc21f27d569814b810a75f55d245e58a325ee1f6985c3ed1f211f3d2bc34aad901960e43f2c9b9ec7
  | 7 => 0x7180a07003040b7b613816a4b2316a9548cddfce20eea322cd0f55ce84112bf79f95bff5e2c64bdc4a8ff6bdf9fe16b4ad2f0e11d710a74352d2884973d399c93d4c4dff7908e2725bc5d861d9d82146b2c4eccebdb8146e386a2240046eaf870fa9debac0446d4b85
  | 8 => 0x29a23cb4a1d1748ea9bbf58d24e9daab5f44413be8876863073edf70ea6062697efcdfdbd2370790766ac25848b03381ab4fa8df548b7f7bde8ce70f90358be0d280a2b8da8c045a179d8628db547fc2716a241ac4efab5e914743c6c174b9ffd57366c37026f618a5
  | 9 => 0xa7705e3b4b6ec91b919ab58dc08d8a8dc59fb557fc5f9822de82d027a46c82f3bb14d29b0ac08140fa3c2709c16e64c5a3e8985565c75c1a41cfe1d4310e0e55acaaaeddcd280c32660137514cf56402dd8c5c53573ffb66d8a48e39e55ec556059eb2b877a46ec109
  | 10 => 0xc6672a7a8187a2597e4dc43ead81978f16f2bd7b9ea77c03bff50dd79b384002ec05dc50470266d7c612fa894c6779af7a8fba1e98fcd3bc4a736719316e18f3dff9dcbcc7bb85632e18812fc09bd1058a8814da8a103c8b37bb5669d41260d3781a1faaf1f5d75b77
  | 11 => 0x287ec333cf9776b13d93ca1fe57ca1da959c7d8460be7456a16f5aff803ef562676b6e8902d97a7bb4040f48b47b223c9241ea15e05fb962f35d013575626205018c64d9d1efe157c5fbff00e60922b080c62ff0757ada64dd70ae63827e47c5d914d6d8acea09f568
  | 12 => 0x903b824f107b187440dc61debc2bf4d0b5c1e24e52fae0cf623bb55b6cd54264815358eea1272e2ec2d0529c812117b3ae3dd6a8164368f3570915024fd5aa8d36cad7b64cd34316b57ee7c425dcddb7cd79a8c8672f40973f05334a05dca68718bb9995763ac638cd
  | 13 => 0x8661293fd2b5f4343dbcddcb4908dbbdf7e402b950c616c867f970c0487cd175a865192236f152a5c7b6c832a7fe6f5ced13aaf3f183b5ef0d1b74498e76ab786444e925e09bac19dc864aba29d3e99cceaac8ed762fdb9384488b62f305214209a64588f1cf9481f8
  | 14 => 0x56034acb88d89bcb46735794f71cbe360f4d9c8bfe9710e1fb367a29837ce78d3a66ffee37a899ed7b19ab3c89d51d8bdbbd8666c0d59fb771839a73c5682f2a0ddaaf758fbd8b644e7cf3437ad4e0c692912391492d245b8ccf6ecf0d2f4dd63f2159685b806bc4bb
  | 15 => 0xef41cd2072a75b74a979a615521173294d103e575297cebf10317842d20c26a02cb38bacf613d1b8b9e8612811e1f6b3be8643c697ef280ec8d6b4ebe7e62ee26b8ce16ba07b957749c9a64e0f7694485b19a0b88e98e3dd83779ead225f9bdc63ac6b247d8f3384ab
  | _ => 0

private def denseT0B10 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x62c06ff24b0e429456e00c4308a854d5e540cbbac6f37efed9d0b31cc6b703614e285442ac7c84682a4f45c2ec71fd9d38a3adb8f7fd41ddfe6b0799df7cfee779d417c6e79a40724d47c1d152d78580d0a96c504f847192ca91bc77b1c424e597d813ebf62abbb7fa
  | 1 => 0xb36fe3af3e8ecf6eec4e1606d675d802ba1a625c20dc53a9de2ce07dadfdcec8c385c968e41a939dfa6e1c82af52fa2b3129879b114e00b79aff815c93a633e1443e91d99ad8499019a2b2bab59157d0cd6844a1b86c15fde71c8b6fdfa9e33fb402342cbb0512821f
  | 2 => 0xa541a1e0bdfaf9eebd7a105e3aeeb928738afb052b8bc69aa9570ea368e3cc2f0d1e033d74e6c79390c8bbacf462f969003e0abdc389b122bd974a5fb1795274d5a5f4a5247c6b0ae8eab628ef7143e71f600318e4c81360b4355f75503c29cbb25349f8b6dcbafed
  | 3 => 0x9b74fcbe2a571ac550a32af947cb709569006da6126b771b76207619e36b9feab5f7c646ecac311d14e26a7c5f85c9f4f9c0090d5638fc793f450be642c424e9f6cdfc681ea21bec6c54150fa8796f7f45612f1049e2d06e3310041f42ac1f5f7077ded7d6f3116ea9
  | 4 => 0xb136c8836c10428ff52b127a6ab83124ec823b50743ce7cc34d713bcc12fc76d7d91bd4ec7bad6407be15398f153f949ba82fda892a92b4c54809b3503ae76037463551a059c6a4f8355b4467eff32ebed3034ce37747995ea8ff50377415c4c28c4eae3c5184cf9cf
  | 5 => 0x1eb80c1d61f3268c6cc3bab4108fa5e2d2f0645d80b27896a57e1473fe4ceba93efd64229d594f0cb048753b285017b1e66377774294a5acf4a8bcc19843ebaf6f280190aae8850927c6f2a38bf786bc899a1f613463118a0dfa15776811262e9fcd64f8277b1fc3bf
  | 6 => 0x781247c5b2b4a281276a1e3d2a56bb399244b517d9fe6702f908759742d1f9b0ada886f22751aa67162103d8a8438652346879679afa8191688b908dd736597cda03f3395485687bb9cbbc4f278430ec1e9f590ebefcced9b92bbd427a33834b8ac8d1d3244506a93e
  | 7 => 0x55d40be3b6e052b4d5f26d4bf2f10c2e8b32b2f9feef59b84196aa2ee6e62b93d4e4928a4423411009d008aaf4b02ca8fb0482bcc455b28fb997a66d5148b53f0fd7da6035c07f513cf3ee726475053915e9fe03d273a0a99b9a4ff224ff68473c50e0f148be449687
  | 8 => 0x40e95bb6fe950bec159bf732675be3faffd1d4faa754198d67b2540c8f5109038c534c0e34e06c62c45d81ffc77a4f76b502b196678f7278723aeba93eb6e1f997b6695d6bbc2619d752fe18f5ba60e243b357f14b53c219ec885cb339d57e6cfe7e50d8f74ca624a
  | 9 => 0xb0fb7e01db93f49fc45eba84935df55a543e9377cfdac47473158404f8ca56de365ff2d2fb049cd74c62d84deae08af55e599cab3e8d6365b5a692e1d0e2967af483326abdedb1dd2cff83e8f78a1f0b58a37c4337d64262b8748d8443580e09bf7177b1c714d89b82
  | 10 => 0xd4bd61b410cd5db7498bc61a2063bd9fdf0c91074ba7f158be45eeb1dcea24cf3edba236bcc889a21bbfa877bd772aa362b72ce6b2f08371081d7309648cc4dcb4e3754bcfe73686f4805f3e5739da341e563335e0b6031d15b50791f80d51846337311f7386624eb8
  | 11 => 0x9701e57425a65eca8f41f1e78a7ef843f13be81e06a19a80fb9b4a09d0b79e963e65cec6378faa6d6e0c072fca9a8a0b53be7bd7d9055e658901fddb853d680308457a1b612152e410fb8ae842205a0bbd85568b9243e03c2b4e49773c0fe6cf3e4f91a730a07b29e1
  | 12 => 0x34a8c57a3fac336171e7c12e761b83dcaf7bc6ba20ba9f79560aa39a4fb4d30b51355d166062e1227f9d3f8625153c0e99d920f703431d2426477716b1477bfaf3b229ba483e9ec15478ce46d00eda0212c5d4e534dc2045d9a67817f8e3d3bb22ba105bec6cbfb285
  | 13 => 0x6e4251023a72b13c96fc4bd966ebab859941f2ab228f2966d500ff5ef1a244a32e97061f35f4a0ce2c3759d1b2a6e6db10cf0f0e35223c0272bb8df89b528c59acb1f07b17dd5e232cce8e0e8d161f737dd5eb18db9784d9881f43ce20b135ad2af8b77e9e2eaf3eff
  | 14 => 0x310606609fc61d14e896f087403ffa9e652939d9ba5f7b41480e27420fc6954201fab7f8c7aa0a9c42707b34a3e9ab673cee03b6a813e30445cd3de3601cd4b59c9c5c4146e3292f88c73ebbb975dd21a10f1815a28f27bca8baf4404d91f13d0a83619a8f7fa70fa4
  | 15 => 0xced79f1e00a9f2012e58a0da81d90ec6b0c6c8b17d5393754a65f7f625bfce14597b89e35c406d90d063bc31fb64f1f61a4a671829aaf1135f5fe995b84c0524a2827a19230b0583e7d41a5753c9cc5d09c16c692fb1cba39b38e5fba29ab6555d3f6bf2094dd0503d
  | _ => 0

private def denseT0B11 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x8de488eb556135a6a732bab2515b36f1a3c6ebd6aa139f9c92a4bc192f29bc20a539964878b675e6bda2042cfd706e14b3b91ec30d91026f296dc19596e4c5272633d0e68cfa053b28c530ff7c5348f7c8b57a48f0cbf5fc3af2815a120994f87c570e8342b462c1a4
  | 1 => 0x7b74c2bbb6017106fa4165ff856dc4ff9d74b6bdd3d0fbc642f18acce9094c8d8640cda041655ee058ba835b4bf499f2e8c671a97479ef0a1578a0341411c9ea4ac2c90df96dc87222b7af4d796006df68c7b75cf3470e9730279ae78650487c9317495096513d8b76
  | 2 => 0xf37e2d6accde894116516c6b24352d5d373cd25bbc0a6d59b0ac60e5cbf31c9fa1be0556eed29421b62f3a5c1e338fab8d3ac94bc7794cfea5b0e1d45ea5199c268b3850f93c5a73e0edf0a0fe9adaad14b65771bd08bddcccd03fe94fc153d438b69374c84f5863ae
  | 3 => 0xe43ebe42f8a7675bd795a1ee14bc6cebfe529f1d72ba027bf0010aee5c4d737666055d795925e6055ec1b956b27f46a00d6d9228264a16c311b5be02669e1bfa5ca6c920c96d583bf810a02c33590841efc4e917724df67f10441713e74d2b48406639d4a21d41c93e
  | 4 => 0x1575a07e16ef2e835247e7b421576cb4af41858a82bd5138189b760cb20011ed87588e78ed7e564237ec9a0773eeba71652f992a102e048c10ca604c04dbb308cd9c34576110e1c509df012848c5414a8dcf8da501e6dcabf2473c1f8684b224c54042dedf3dd3719a
  | 5 => 0xcdd0503aac7709d9f1312aadf0deded7a72afa6b3bc7c9c4155d631501d1b8f004cea1ed0c0e42bb756079112332a94b64f8901d72b55bd10e00853d707abad16daa86a3d1610365e86d0d5e8cbd2ec6754bfd052c3043de0a9864b602c6d85c8b4a1dafda848a80d
  | 6 => 0x3d71ca3977296751bed0ab3a9859867f6f7379966276aa3f487093bde57597218a31674a0b83d6a4292708d80d8287fae9db5f9499dfede93f5a5de08ea63f2f8dad726fcff8ca20693eb8e5da68793ab7372a98f2f17878932b1829c52f1a46ea837607e893834534
  | 7 => 0x97963979bd23d07c2ed0b037d1ad3a6f1366109c8388c564a26e400d249b8948379983ad20c9dac6fab29a76236fd12d0499983373aec291d50cec9a14ceef555eb649b629af43aef70c20f6b471be3e1b0a9fd3cb7e5ee51e93250a99c324b09b65be49833e7dda6
  | 8 => 0x365c8244f0484d8b12d49fd2efb3bfd848a739b2fed8a4786ea6ff151f57b313ffbff7e4a67f718be900a5d09b53dfe11023aa165e50a48173f020a44034a788582f8bca577a1cc229cc1832931a744ce1b245c506ac6ff32eb2ee2acb46de72c5f3443a025e87020b
  | 9 => 0xf5fa4a3af829f1de7ef8c92ef9610706875ddf91fc9ffa59897fac2b758eb2c71c7e25694f8933a0b2e6edc5d0f040e109302dcd249e1979bc20e49eb882824f81a9a0ff5a7658c34046e0657cfa6b146cfe8d7e100f4d3b3c00e1854cf4c387edd3d56b23955bf780
  | 10 => 0x558fa54e417b3446fbd3f6e002f68754ca6cf46f1445e0d6b332cd8533e14a9269b35e6490928280b02ac9c669e0732e60d55c78a6f3d734111ffd7537df33af08fede53ced6a69541217a2aedfa1265fd6157c8b7226619a11b4f0464fa8a2ca132db168cda448257
  | 11 => 0xd93707a9a763bfc1237783ea8a5a8b92dca021d4241824b60271f311a15d0bcbc98f725345f62531bce82c97fe0e295cddc6ceb334631de7df608435f3e0649f7e03a0190a6970ba4a52bf5c8621b5bcba6e6247fdd15e43776bb291e8983b0064d61e4a0f0e188290
  | 12 => 0x36e0894bf32e848a195e7e5245d31f2ace46ac20d1a4cbeec2d15f4f992df20b964db05cfc6af6445f54dbdc2c3fd119e866412670a3023cc87e0e60f66d26917ad52ec8ba782a0821ff3370f48045e2b57a2bc2059186e05267840b4388fdce21c9489a6e58ac10bd
  | 13 => 0xb1875130dc6de5d8d4fd851be6a49b4cd6940700aba30dfe6a945503a32bbdeace56e9ee6f0e0f6301fe2f1cfcda7a264f869d20c8e3a80c38d8331527177000657c20d7b52127362027b2f364e84666eeefdae460f473f249fb8e4d5860c2188e31e50fd319ac13b1
  | 14 => 0xbafc676e3bf11744ccb851e6c2c957cfb828389bc9ed88443ac91e8ac9772c0751c86cf342b128cc5597febc7c215b2aa692add026b8f4633c1d705d28028b378b7fbcba4ca1e4ad645dab7c7d07b838e9fd8deca9871c87a908c2f41916acb82067270ab644ad965a
  | 15 => 0xee47a85bc35061e8ba8037396051ff3fc8adbe8dd452e7b4c7f53fa0e8fb36d2a0d5f6c4f0715959acab6fb274b7d4610042f55e100a21d93a5a4066cef032b46bf3a4c645c63b30d5b16a565ab24f0e9094987af7ec6dfa64215db70b2c082f49889fdd983db45bfe
  | _ => 0

private def denseT0B12 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x389f541726cafc8aa46e418fc5d7dc755d93cea59628466020e49f8c61b6545b7a90e369f5ef8299b0340c318d98242f5d1ff522b59977ede689b20d773b3343b05d6b8159233f08779f4feb0da6f418557021252f38a2fea8dcc7d15db0a75f40d099e9a32d4404d4
  | 1 => 0x634e31d671e88eb9196dcc86148412484a5d22e561a261851e1c7f73530f10bacdcf94f24bc784c080e888a14442a53e9704b876142ee3bce6fc0d738d938f7f8f031a8b2d47ef8c751e19a88127c107b59980b18a90e4627b059d447a681ddb1016da38ae9c3aea34
  | 2 => 0x9ba2415ad912748019eeefc263ac7853a2590d258e9ccd03c08f075756301ffba23b94f4c26b32283baaab0639a0e9df5bce9cb99da5384077502b06cb8e9628f0d650175167d9b772102b029a3406083bb4ff47d509e2a0a7298d97aa4cb0f2b661eb46ebc7c63e09
  | 3 => 0xb24ef44eab28a7edbbb0c0c481cdf6024e996043191391d1ecd219f3b22ac2bace1d3b47ba61af5d389f9bb68741a148c8db721f61d15d1b37ab19c78317e32e78e494b2b4983bf750aed2a65fc59f4d521118d0173218835c9a2807c4b1776313fb58661f142da909
  | 4 => 0xca0b3812b60c1ba1762b82ff2bca10ea36294a7881a72e5be57596e209cd691e1b3f5e8b62144a7e8301a42c00b33aebe680413de12d432375142043db83a57ef65846a31140b00d7f18ed8be14524d76cab8faeb6ef9d64be7110a30415836a41863fd448b3390ced
  | 5 => 0x1b536315d61b6dc3ab4f6da6f75617a368eefb1c2414c50e90d6d56bab6d5222ccbd68300a2adf73f77b62a6990ca083727d97345fba50aa24050f747910c83103c8004d28797328dadbcd36b525b94b9f8e77535cfb098fee84f97e574cc505e7025c1dbbf06d5bb6
  | 6 => 0x85eda01d557e9d13d34e40e458318652adf6a3a9eef724afe9cd2939356ecd72c1797ff4529843553a3e7a53d6880922583315af582ce1b3f8954424834bad2f9881ff436bd5f38bdb195cae699706a649fbebea4cca91acd95404ef7211aa053883cda76b1d4bac79
  | 7 => 0xe2091981f0031d574a2be713c1736ed9026ff564971d2d0557e7f34d074580dcfd71e49325cb4f6826dc7730934732bfe29bd10587e533b8ce80f4ccd48a091ab41c7e93adb8fa8c226d3f68408cb7ea6af2049f9de0409152246526d2271ced1516e48b2c00137910
  | 8 => 0xfce406818d92214f46b27be9ce5bfa358098e87016e441d5a45fcbea4bbc30de28e281910f3e80b6b4b054702d5db05f6f128e5afb3c0fa2c6f4c9dcef8a768b93872095ac199cfedbf9c85017451b7573aa201e2619f1909d363766ac8c87b4b2be6ae568fdb1218f
  | 9 => 0x22ae4dd8044d84c37363afb24f9f01fe27d6eee15351f6394119b2c737098eedd8a34c19871ac35b176c9d74496b9ee86f63ccbd1464ae29468175ebf42116decfe6831dd8ccff23aff47006d6306264202706f0702ef521d7f1fbdb28aa75e159337c877971d68b46
  | 10 => 0xf31d73550e7b1ff46dc2acc7625fad43d3e91ff07c8ff107c457bf37d8b311b7e1f06bbe0218355e7da2eaa1f22127bbf348b068441b5295fa800e928f05155b5b25318bff2d4d060283961ca307fa85c6b1e232637c77b8f6ca877e211e9c2a49ec12f742bde31b07
  | 11 => 0xdccce52297d8fec0b8ab00d00a07ff90b3cbc126f1266f87d5ef4f774b8c6f825f9fe6f338780ca4afb106300a68e2d9542164b0d1777492c502ad7c938f4d35ea40b968355610116de6a1997547201e8bafcb3cb58e69ec3cfae8c134a158035babe791a0a3c8b647
  | 12 => 0x9ddf228505102ae15980850da2bbd7adba5e679d5f2bc235b515bb281956a021aa1f81734d0714b022454d0872096b3ffc80530cde0553749edce2eaa96819051e5b0815327df9ad72aa33c7a15d41ced0925210cc72b6f55ceb3ae304ecb4da9d3a91a532139549e1
  | 13 => 0xb33475f920549159c4133115b9092363fba26fc284f52bd8eb817a603297150ee606f7c6ae6d3fef4aa4c7b8f881b298544281e06e247c6df94c5d34debd9b6f0039be4ad1ef9d319f8959ee4704c5b3556192da35b07ef0c2df4757301635f1810d2b7c433278e5e0
  | 14 => 0xbdd204119d9f1a2c0c6691663f900668c51b8e4b6cb606edce99a02fc646386c16499499370517daba868240e78aa26a5f57197f138f1e80700c9406deba044d32ebc5ccc8a213c49330d28489a8738b8ac04612e398ed0eeb37d348cc51f9154f9718bd53bb5a6af2
  | 15 => 0x645664bdd4f5526defab91fec643488e22c990632730bdc57fc4f9e9ce377b1dcffd5e9fec091a13e9d5f58e349167a900504dd6a1bbdc3be3676cd0a8cfab40b215c9f0113d96820d4b2a6037a19ef56fbf629a7d1710d3be7c745469c14efb0b68b370e338bb161e
  | _ => 0

private def denseT0B13 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xaf5367b2054db3c31d9c42e422360e4db32ad6d7b3d7f80cc260feea8c518b99fe1b69a86648b23ed308f13a7500fc40decbd283928b422168d15d3659d9eaad18947e64a5be2f5bfc6fc3da2a3f15c3c7f089dcca630a781fa2f7f9ebb4b6f9afe7db54e0081d40e0
  | 1 => 0xfb13f354fb8505aeacb53ef12d40130e03271aabcde88294b6b305a126d45c0711293e16eee9de24db9cfabf0917085be9ce32b0c0a9bf2b02f53fc738d89009bbab56409de38b868d7665c0d5129bbda2f9c6b4f578ced3c2397eada0b2c28db1432ebca106634bfd
  | 2 => 0x6fbb3c23f12d83ae91695c85140038699c3738dade48bbfa4f146ce00ea0d6264178142ae8c80deaf1e8190c540d44f07be8d04ddafefa31120e2deee7846b281d9c0fdf57d546051cc436325b43b2daea39ddc7fd694dd22c7bdfa0c368f3f696a318c1260ff2867
  | 3 => 0x8d1ba599b593054e33c37a6fc1160146ffe72a0d1705312ba353b74608b4c4be4199e7d3eadd8c47d1d08dac2a20f2a30e20916541396b6d096b38c999cc4158978f3990e21364c4eacd00cea3abe98ca36eb5e9c0c75ed101616390d0401de1443f0e86a03fb9297e
  | 4 => 0xe160773def2223e49a98a0574f5ce510bd830c8261e0ea5be15ab823fbc692c0b68e1c2f9f98fee3def812556b9eb8a2eda0f2cc57a5ee78fddff1685f6bdf8c31acde6e88706d1a4a5b3bf34a088651684575001cdbe4d7ac1c7ce9737a35ea0f78e544d3dd73b19f
  | 5 => 0x1f6a7d5f2ca7658c356ab881d9b01455ffaa8edcca337ee754b119b7e6c26d0d1bafb8323aaf5711b5a6fcf22c64781aee404be8dd7c3be9cb0d668541849f4b10c2191d3f9891eee800703da81c06da0ed7d044027f158c6691ee3ee9dc6c58f641de13f5fc6e0ed6
  | 6 => 0x5b27d4a9c677637f518ae7612b3ee76e64c50069f1a1d77463db32d8c7c950adb0a10e39b854322838566c2a17e5f678907c796b3aa00995f0c371b7f4e69151f525b36663b49d548d05fbd46085fd3abda40289607906854c2dde7a067ef4ea6578ecb1d04c80b8a8
  | 7 => 0xdaac12aeff19768767517dfd523ba197c322683df6c0b03d705a19391fd348e3b6131d95abf2c4b41deb1c533f5952ff74e5b4bf32ebef60acb2a384a07dcd6e2f0c3dca698cc71b3245f4319ba92b14fee68f312e113d40cf451557edcd0e486d09e61c7d3bc496c9
  | 8 => 0xd3b5c539d62fad8388663b852e351abaff1a39d66f8ef8f21b5330852c836490e5bfca0cfbe4d9e5662baea011aa784e4a8d3afb1e26a01eacfbd5383ee4d9ac56634e88c805d0792648f1c00ee36c806952c56eaa170337499a6776a062bd5ebeb0810054a259519a
  | 9 => 0x888d54c0c8107ade8644e0d411d451eaeab79de39ca6b1986a988aee692a637e94bb61a471d87eb1ec860d774fbe77f7eb88c3fb02135c5bd816201dd22d61543ed600c6f293e568e43982d96a3f1e8c5d9c436ef9898fafdc8f36be32c4a47691f234f48fac701d59
  | 10 => 0x2b97d30986b454170744828babaa4c393e1ac06733b0ba397aa7dde18c78deb6e6a03df4abcfd623e7e2616051e8295e235a92baeeb9e8b4dbb53736b13d23e882dce0952f7812e2b843d9ad8939c13366e9f9c6f829e0a87b89cf8d5bd5e6b0c82913ec466ec15e4a
  | 11 => 0x43217608a117ac7647c542707c6e57766af7d133e9ff4e739ffbb4291f0ade67c21115d6691fb424e14e3ec7794302270dc81b4449e404fb3ec69b49a2de8d92dd87154e8c761895f4628dff6e7732a6760363cc03134d506455fbff126702a59aaef32597537773cd
  | 12 => 0x3f1040cdd8605a841a67b7f401c67ab3b24eb6ea176baf2d508c6732cabbc48d3ee51e62a4e13bfdbc60eb3fabb606f6103e5aa372950421cf7978a075366b25fc1b6c50e0b4cec911b5d7e195070529e7576a62ada92290721a54b71c3aabb0e0e209e68bb8bd6e33
  | 13 => 0x2e0cab986f64b13bc1c515f74ca3247af7337f2120ea2a84aa7b709a4928e5d79a48a170ef30db52fe7336066723a1a845b3a7a9bb76827db920c916b701c003733f1eb125a2cdbc06bb21cae152d7b0480fc0827c8ed3189c2b29622610f01a0c6b24b0c71ce637c2
  | 14 => 0x734f14a475df31d2126221808ed90272b33df9dfaeeb9272d652681184bcb497dca06cf1a26d3be3fc9872cabd70820bd258bcb28a29a78fa8dac6a7c3784aabc42331ed2071fe1fbcf26507366759d433404f4cf1ee7fef9df238b28a2e264d1b41c022f80bf38e51
  | 15 => 0x47315765ec423a01154e9550196b616f8e206dc43bf9c37237fe0b3121fa077deb595d94ff1a1483b6dca710b1df1e13787fb54327e8a3f4c17a9814177adf6bb0bf99ede5649389171642ae1c8e0d8934d24e582e12372c09c694d6d50cc8ce521b43eeb2f3f56274
  | _ => 0

private def denseT0B14 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x9c5e217403ddff133a975851408169029bed4c112abb8f7731a550be4478eaafa1d48c3a453436b30707c4940fcf31c104380db11f67cddcc9e3af49ea213ca999ac4a5c093bf7a775a2b95538d71adf096d53f3ac1144259bd65816b60548617f54eac0f30a5c62cd
  | 1 => 0x2e0799ad76dea0154c26ee4823e160d6c73d353964d9b43cad2bf62791fabb8e77000a50e34dc1300705e3e54c9fd9bb75f281bf3867c51d45d60c3e6568d31cdd381d23d0e88e445e5675a692ca4988bebad938e64b3beac221e402263d8898c82069c264f957fa2e
  | 2 => 0x4db0e8f2a08ea672600d77b36ddcefac3ea5fb67de8d0e69fde31c67f8334ddecdb5e6e0ef153640f536e865862ade6c28ad54fc96949fbc4a9efa060964bc3963ca5246bc45706cf298ecd54093fd7a482f4792721265ba937f7d0125c379dee6627cda860642bd29
  | 3 => 0xb2cd32fa7b01b32c12b6c006e39d2b3dc0a95b09553e50bba025e850aaa49b69e336b0817d8162e2401133cbe9d0ead2d08f61d5d9059d3fa6558b83dccdfabd413b8fd94c05daa0c909aeb4a393c48e0dd05c83ca7245ba30bf467af9a70f0acec960e7390ccda4a1
  | 4 => 0x9f9bbd9e2f0e8ed61027c45883bf646f559ef1f334f91e1642b186c1b1940ce6b7075c9b2bec261b2d5e662733618c5ddd29df2645db508902221f939b58b787b158cff147bdbe53c29c4c671eb26ddd6d3aa3d62083d9f0e2eed9804fb24226a942765655ca12f981
  | 5 => 0x304e7d6d33bac25e254338732f9f390f787d15bf122d6b36505cb3d20a3d6d6265ce10674af11f59e7339db11cfa5d5b28d5252cae42c1eac2a5fe65b20bfb520ba9556639b388b5e14a3027467447cc9c1b2cd9573e9a2cc7b7a14c7bd4cbf4e28e111c6c0d73c364
  | 6 => 0x416fb512326f15e5a9906fd6fb741604def6647cc28292f7457c32a3bea605775559d39a95101131db5ac83a79b5a7b50f04005a7ae474b0364e51c12d5502613f15758019ce0c71f9d55bc0347519c85d8b78d4b3cbc09c8d8a3cab03ec14ed562852bdd0224240ef
  | 7 => 0x22bcc55ed9ba207b64082950d99f23a3d5a43a2120ea001a07d51ef8935d07ba49780a251a101d0cb2ec598d3e3a76aa6fd1f5f2be648c3284a61b12b26973c6b20576b4cd1169a3ad030e17c09aaf7d8ea80e312cd63ca7cfabdc8677b6562815ce8e5a2675259456
  | 8 => 0x8ef03133eb4478aed4c870c5057e4d2bfc53cba1db78a2b8c219f938d0107770ba82ceb329475f3a4bc96e51e9a459c44fbc9b1c05a2754e9b55c419ddcd955f47dadeddb4e4f9fc43210ed5163bbe3d423ed45c8233ff598d164d98d73bd8fef4d9887a78fa646e0d
  | 9 => 0xb11e4e98b3468b34e42c984066c9f3390a74e3d7930d0b35c38ccab4dd42e15f5aa6a4b9c8fe2fa52895169ba84c8aafe736ba8795397ed1ad271bfa899d1739a3cbf1b0dfccd3516a2ea8e01a59bbbe4ce3f849cdd3aac460d63ead5bf482ab25805e14210c0316e3
  | 10 => 0xa8e09a7afc964573ab3244c10be9bf4e3ddd075ff34e6a7c273454b8c9cfdf7b388cae8de48aff739fadedcd33846c3b0a19a73a1f8202ed882f14cdb4b1ee573f2caa5ea53b68f9433330ddbf47fcd197492596567020cc22cf7fe024d9c1c791dd4ca9625d16ced
  | 11 => 0xa4dca0a358f51ed0a5983bf55216e1f13fae9448d56ac2c17175a784dd6c934310c3cc4f157b0dae53ea8ee3c2f0332ba5482a8052f5844d48514e9e17c5ea5d40098e3a4e9b2117289f8f1efaae2e1162eb5d86ef105484bb3697aac00cb1b8a1b874319b32feabfc
  | 12 => 0x274def3df24be871650c9dd6aaddcb8eb43f9e03a64c38d35598722d29a8bd236e4eecde009ae1d133902a9f1ef6ae29231a9139a67aa2ad5f8ee4884509662ac3e3d8cc04d552f38582aafa10d74061bc1ce07935e91ea4e626a778a5fe93ec19d418b0e895ec5552
  | 13 => 0x4d81683d547c6163de559e04bd585107cedbbd2c20c3e42f09c075e993a44f31b7622f049dc125cd0294f66cb61593e0e0b5ac54d474eada2a71d88f5e4fbb917b5a88e2cf7908f630f4059b88bee92f6b93f47e077a79c82aa571149eb208a4721ae16515620f8c81
  | 14 => 0x833b27b91ca24f5ed8ef22cc7abc22676d44647dc0465c52d33d18040ea0b52a96727caf0fca23d00693ac19a94eeb9ac958de5b25a5543cc724d948891735b10e26d84accf52a90eaed0a4db2ae738fb9854e514922cf60ca20ada107b1cd2c04bd516b006040d8de
  | 15 => 0x6c618214f1fea4313de833c0e68747012af1cd4fd7ef3112dd090bc75756718304cb2c196d2da80320a379a02f19cf906487b5ab701a1c3b742e83c7fb060f5bbb8f9eb02f3491bc0a94d97843a638ddf965ece29869c377f7f761ec2148406d9a331893e11958a7da
  | _ => 0

private def denseT0B15 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x4e1abee304b463c9846c6eeddd1c26423f09fe3f31f45db8bb873da85f951398b77bd796c588eb0448bc446c4393ff0e8a90b2eef154beb4bfbe16bbc758f1aeb07c23e1a7b225159f179cd751c076e8ce95a47241106f78591998884230449d928ee392741e7175ba
  | 1 => 0x1e56f08c2f311f3d63160b75838fce34d3235f37a66a1ba4f0abd043a1577d324fe732b0ec1f6a550d88f6abe65b1d742e2e8c5243dc73d8a211e3e9993c8b26bbf13888c15c797681d34c2fc5890066b7f9b04024a05f0c6697635fbfdb4769d29f65984c64b3aa68
  | 2 => 0x2a002a45c9f84ed57b462aebc49c4139f77e88471b4a4ae637358e229f7e4678ef98ce0c9716105a37953a57ed19cb78de3c74e7e36cf9784fee669f3176e2a67276476ccc6fbc2e7477005c049aea805bfb3d8ef82fcc38a332f72f926cbcb58560dd36ff212f2f99
  | 3 => 0x89437e6c9651f89275e2742784bc2885d69bd9706a0ac8a18948bfce7b218544f92b0a9b83c7439a4dd152f9d48382d6bc6728dca5e707c992ef1d1ebae955fff6a5db1740524f0a6ec156de5dff2c17dacd60f8cb3afbffc139e00f6e2dd425108952e74918cbd3b3
  | 4 => 0x6e04160b1bf6b2d69d0f594b5005862ca33952c73907faa7e29c7ac78bb217542ffa29ea5591627e083111e0a1ac900fb34866d5e4e23a111b8a624c30447650db0ba00c89e83271f7549a7671b79635e5731ea2c08319a86e4b722feaac14e735979483cecc2cdebb
  | 5 => 0x2d46962aef25ac1d33534669040857923f33085aec4febcd2dd5f583aa36e9f7bd8751c9ed2f04917c809dd5befe41abbe92719bedba34c0c02e84a2069c7e1ff955bbeb1615a493a4661eb60459c72f17bd533b774920199dc2a07fc0d1582511e761a2e5275ab175
  | 6 => 0x8895c3cc353345247b692149b03d8478e77b55095b23d251b328f21fd92f010d6c142ff4f370c30f11e01299264d2537aa2de37bc0b59951a33d571ef21e227cf200cb0844116366470d8c0b726fcfba6f85d67a805934d95d8d3975b895aa6a0d2d5ed059e3b79c74
  | 7 => 0xd89d50f3f28e7b294adac13c828dce99ce53425389a4e6c99daaa69fbec1a9396eefaac2f45bf1e5a3e5bef848bf2141ff389a33f103dd0ed402c489b04b87059690972060eb1e1659f3c2db7b4202ef4ae27100dfb67d7aad21d0e576fc1040b6d9063deebb3945f8
  | 8 => 0x834ff156600ee1f087633c27a2d8c01dad7f6d5dc8a81ac9a20c4fc2574c27458423a2b76d354eec712d0172349e35028ffda853ba305357ebdf14a784e8aaadfdb7d76d80c495e5d23d863f88032024a7a33c3c53c64269811cd870bbee1d6cc56ef84172410284ec
  | 9 => 0x152eada1d09943d04ca010832eec27ed526da3034b8227a5b7985540d1d8ee032e81c8546379e7ce7c13a5ea50b9559b9803b37723edabcf827bd6bd1922396dd2bd70309151a97c0043667c224b111af1dfa7262ea9dda2fe97b3c960cf2ff22e7965e8bd78bc6d2
  | 10 => 0xd6614666f0f1c3fa1453e1a6c123c51f79a4ae2a1957a2e1ee286e56ae023b1ef45645cf706170322eb63dc79faa4e0ef12100a1af7772c11c6a584434f190a58294b98e442cfa5a640cb5fbbd9dc9bd17fcd00ecc1546c6f2e0b9e1384512af19b5a4dc299d55157b
  | 11 => 0xb68bb498eb6e77f76d20eb814c38ed4410a7183eb03f4d74ec693f64c4433a5d9507ac7a9ea3de2a478943557015f4a4a11425be22a4343b541934c37f3da0e89185f7c2111f33d8c9aae7763589cc76aeb44d215be96679525f8ca276f82aaeb0a0b94d861db7c8aa
  | 12 => 0x234b2dd6c6323ba25b52f6033c41e6ce1f536222c280b20bd234a98603ae348b5d98849af34a6a38a073964e2e2a592fd169366c299093fb352bf0b72937514e78e5b3d61e4307f8aec373aca695efcdcab73799beb6788688e4d2f7c44889342fa7ac9b1668d2d7cb
  | 13 => 0x75b4497d4f9cf30230a3771542cb124e3e3585fe39b912a61b94c8d1463170ae1e74a1fea60421f644bb9d8bdc61dd0d10fb3ec2fffe5d36c1ea3541aef152d0a148deb79280a8cd54e2953d72fc8edc1806dfcd460bd1fc648fad6497ddd9b4fdbf32e14f40b979a0
  | 14 => 0x6ddea760eb7742f75ed00bc68df28cadfea2bb0dfe21e23edf9030c572c9f290a1fdd0fb3b0d299961cc593b2b1888c9ff965d7f01f0c375d154bb2a274a058e8a86fccd84dc05a013af027b7900e1887953674fca64f3faea4accb2e7a6db4fe4343e0747cf6a1ef1
  | 15 => 0xf8431ab0bbe0ee11df9e987a1ba43f9ebad5dc43a3ddd048f2b0ec4c0da128cb9e95588bac8f4ae2cef4a3fe492c4a725d7a7676cb1537f93dbc69509b7f65dc50641345f9605cfd942a5925c82fda60f764fa33a65b040a5b86a3166a3a96a0cbaeccdd48530a3982
  | _ => 0

private def denseT0B16 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x452b36fb8fd6af44a502db055ff9ab6bc0cdeddc9dd74b76dd25c62594b6c3427b682af0e0f6379e02a5880bd05f9cb084bff8edeb5c4ea080339bd25e4e7082a9f30930559c266ff2ce780b672a6e24e7730f6048a8777b015302f671a5e9dcb4586c9805a8c2421c
  | 1 => 0xdd103f27cd16b4fcf800d6ad859da654c63a906da56894328fa22f8ada25340462c256785d9e3521d3383e88d8c4d0c93e81927432a8362e1d93c58532859210c0436fb8c5821e6d8dec83b825eb06d8f8e4012a5bc939b7bde920cbd75a78688746af8c299bec41a1
  | 2 => 0x401765454fc31750af311c042040a463e86faaa43464a8d0c469e3d9587a5e5951c887acb574d82e20c91cbce395d3c9005048f6a86c69bd4154559a6810bb12f1236a37a6ba0b3a010508cd2dc8a4911954a887a8b5bcc11124e5de54636c4ed7bfadc2b7767c4739
  | 3 => 0xd3b096cb6deebf5a86a74ff6f2d1fbaf2261aee22b7d3f79e13ccaca59f368d7970d7ec6a665135b23139efae3d29f72832b042e200089a3b9e33a814c5b273f2f3f47b22dbc7c6c62c1699a5d8555bbaed49e311d3446c0e18dcbf406893dce50d7b28ee16fcb94dc
  | 4 => 0xf713a752824f18e40ffb1be7ddce70e26e86ceddefd16c51e31d8fef0078ade10958e6c141f33c82daebab230ab67acb2881b02300cc3d3449c8a89e7adbae47a77f2ca34f4665bee35ce5fa7b55516bccf77c125d258aa710e03c526ff8e5095bf8c3ee6aa495688
  | 5 => 0x879f755654f59c37eca447a56bb973e836ca7ea7ae8e30f9c4137244bb48d628fc6f468b3e596a9f85eb8b0411e52ab012cbe16eb81a0b04e6beeaac6f82a8f3be4d011250785db8d29df7b6493cc77ee77ff4a421a070ebdaadc355f62c8cee1cbbf9de6152b9a994
  | 6 => 0x376c71ce56a29dc825afa14bbe66b7925d8341b2b5eba15dbca25f620528bed724881b36b45b3b1193114d6aaad379b5984809c2ab9953eea27a99b88af2ddb51091b5d2b82d3adc93d87c4b07683ac44df1b460709d77a6cbe06ebd895587102107cecc1f5e1ca51
  | 7 => 0x3ddf4912a0b4a89e1982659d5f3a03c16bfa834d3806f20d16b82eed16fee2a45da19464d2685ff19204d21788882965ab5452ba478e9bdc6119da54798fa603a27335e61e8dcd4de52d97bffbe822e494bb614c39ae24513483a1c14eac3cc22006809c293ac0834d
  | 8 => 0xb0ebc64da25d5f0bdee4fd24cdaf09ac5cd61259a561c708dcc26a4234722d5f42992717a695010ff8ab2da71bfefa27bcf8969c468b7866ec0647691f53bdb9512d736a0f49dea0c4931cea363f8079c45791908b0f50c940cb20952e98f47b3695fcf13766b0f20e
  | 9 => 0x13449e60b4c2107c6337673ec745eeb863b3ad3dd292732ba53dff29b88bf2567dda73596c3c886d089de0d52c78cdae0ece4f933ae190552503dd66fd1b66c12cd4e25e1e2c5cd50ae8f2192288d7c2a0a05096e0beea79b18f6f67c769d873aee52798a96ad69988
  | 10 => 0xd9eeac569f872b9ee3432f4d8d138256e3fe9342e84564959baaafdc719072900f7fcb44891075a7a7d09d06e8e533059da3874e7656c8dd5a937d3b5732c3adf98053009eb2a4463f4e17f2bcee324aeeddbe2901034233bf99ca447103681d70212c01c64c28b572
  | 11 => 0x430c585f631d856160002cca0d0b165d626454296c696c07cbb2ce46db6a72d17e79ac5aa8c93305cf247877ef53d3cb6bcd93668787eac9652b21ffb7bd86e618b0aac2adf7b905253ffccc9dec409be6cd997770d804c48477334b325b18ae2806f2e804e8a4d9b8
  | 12 => 0xaa15bc599d4bc581ee9593416aa334302f489b86b1495164dbd51768c8578a80ba268766c99fd5a27c928a34cca8955b55f05bf7cc669e29b41e67ed6f8f9a2337cf8a8994c7646b22e033694daa63cf0d7a7e355c54aaee17e7eb0fb7118f2d1a3042e43db80ad235
  | 13 => 0x799a648f303404587900db3d3555dc76bb2298bf6942c3b1f4e11404fce83591aab08648865e46e75eb591010193986c12d925ae6106df39b7b3134439b231428dc39d8ec6febb1081869ab5057fd8958f9eb88f50754863d0fe744e36535ed891bea3dab731c7c73
  | 14 => 0xae328ea5beb786d7046e1065aa3c949cc22fb65eb27352855a9e96a10a8ec9f1ef95105b01bf2424e114d57bf4f4a0d7778344d2ba6376f94e7e8e7870187106536d0dae96609366a4bc62d9339ce1913a68cc694b49ed6dd7f7d5dc2d4a78f52f448b604865ac609d
  | 15 => 0x13b127d7ba52fea507d6eb0bb36c4fd1700d870dd9c10b1323d8ad1f6ea1390accdf9f3e9be3757deb9e271ca7a816181231a4f941645c1c4705603f7bc8b403d426b68bc728a9eb9e056f8cb156c53c07e3dac06da1136f76fc0868ede3dd200d7c45c64188aca885
  | _ => 0

private def denseT0B17 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xfb6e3e937f13855b363dbd2dfd204762d1231ddde6c6bd7f030c1fb49d1195f986fca8c14a82d88ba792b4b46c92a58ac39183617d44dadd11bf6e19ad8f167672177b91aebe5ecdbc91ca750f97a3ed2da89af0029c86f12d401843a4d1e1dfd4b61e75d24cd3ca66
  | 1 => 0x18d472e0991b486c4383b5086fd90c7c5137fbb55f7b518ea1dbbbf519c5356b31008e20dad1103d8cc0ae5c64d5cf91e88c5f1be2f81581e30d855d09004c1d0932b60287ac49d038e62e12121da1ceb65e266fde7a11a4c89dd12d3e89b370de81f9cfea3d01d5e
  | 2 => 0xe528b46d7b2ad1929c4ae612858ea75903d9e0058b2fd8cce703be565f9e2b129dc4340d67011c91eb70968a742ec21b9a588f353684e020c2c38d9edb0d51a5a9afe713f1881ca0655101babc0d22109673c236044ad56b6c98440734a29b51292b3428e8ffab5fcd
  | 3 => 0xb51b7707adf5fccf9811debd673ce8dcbcb08bda500d5f1371c08f64cf35ba2a7b116ed41606482d461c24c9cf46e8d24a56eabcef12b44df844980cb273546c229b27450c2a7afde6798bbf3fbf85b763c8ed62a418a81d76101ffd3a50a3a2c4389de1897b6b2c3e
  | 4 => 0x230d34a8c2b100978a070856aa67c7e258dd796971a0182c621fd1459cbebde5c68f2ae1c6148a31c86b542ff96330b09590c17ebeb6cfaa90dbfd858aae886cb12f8278027c0015238250e8b113e567973b40cc543efb4ac3eb3ea4500a3c10696b365e009a79ba30
  | 5 => 0xd90b74cd806b091741ff0a5c97bfe216993fb775350973a9e8b20fe30e9a7388c3aa387f8c0fda19cbb942ba23fabb048b4acf53623b5db1b85b917a9e43d80fa340e442152dea1f2e628fc55f12620afe9ee91e54dce9cf256db817609a57970d3ec0ea077b4e3496
  | 6 => 0x77852a39cd2998b828ccc6147c81eb8066a1e2d8e54d868c1f79f11666eb7907d5fa57b6dff3446325aa3b18588477b215e25e4d3b64c8187bd24f3951a16fca477fba3ef1d546d2785dcaa2494dd83f1d238384c05f789786f3ea81e3452ead34803bf770445487ec
  | 7 => 0x8ef4feb427bb9cc9a29e8c90bf987432ad6535f1b309517cc32a47df84a9eb871a4630056482c1b0a847178f472b06ef9340f6da4727b102ed2d8925652461fd8b6611a293f996590b440451a1763a288b10f57ac44009ab06509b63365a1e215a52e6ff31ef081ea2
  | 8 => 0x7b9fd837f109dcdd3488ea56a8b268a4811cb7b9196639951bdab26e98bfc3d85ef620ba9cce83750a68c2ab385432960d7b2de6061d2c608652b77fb2bb627fb92f95d14528b1a97e19a8a2f958fefa705b48fc122979844c4e2a0bd2893b0c6c5794b0979ca9c104
  | 9 => 0x199b20b25152dadaa6498bf76e71447995c3d8909838bd478fd56dea4f2c41a3e0521291cc435fe53bea05b2ad69ca09ce9243046a41141bb61c465cbdcc045e986a65e95f449905299a482eb40d2ebf4d70104efdb316ad98bd92b0268a57fd7045c9fffd379ccfe8
  | 10 => 0x295f8bc6bec9bb72de48df0a709474aaac6ac490918f77df17190fa5dd5fe6ab087c5efe85477f7fc6cbd699b4086a71cc0c388d543c4e7261d288fe471e911822b0dc4419b8980c5f4cda840a0afd8b0cec08ff4366b85be834c6cc55a6402805bb298ce5eaad18cb
  | 11 => 0x5338902aae7b503cec188708f25301a20b82c97e586251e9c6370779858407e5e238b6cca5c9aa36496920b09c53914ee41e8e101af32b8feb0eb07360ee861da9189079224a36af7a77394a8278cc6e9ed5c2b046ff30c30dada53175f59494d33781c2ee93c479d3
  | 12 => 0x805d4b74c4ca03a790d0bfa075223d2be6d388a10132e0fee4f8d06957bf088723c82b7140190c426329bea0def405fa6addbaba24669f9055af7d9d593f8e56648cc61ba0c8a06182fcd351cbc5f3864329b9f8b78a26c6c39d810955476e60a8267c25d025c4047c
  | 13 => 0x765514fca541f267440b1a33b6ab5c5ed86e5212fb2bf94b21c6e3b1420b385d7aa35d60d0f004a17eaeca26afbbbbea9ed87158b98d1f3653d4fa70a45f279601689b6b046a217e63117b73db3a8ab21915b21e7be000d684fd03e4a9805c35188429a9bafa4c35e3
  | 14 => 0x2c749ff94d844f420898b05521189392251cf8fea3ca5062e0da512003260eb6bdb82ffd354734c2e4b05bb5abdc9ba9df826e873231da6ee1259b8ca6cbdaeab6d8c27171a66bea46ec2ff5fa82f97edaf3c9ecad80ed1e94c7fec419ac2a36945df58b2a2b6f01c2
  | 15 => 0x9c33a3d59c1af3dbf2dbb6224c46fe15ac654f0d2e5467d0817e2c6b8235efd0b6194253b0ef662855813d381ab6129cbbce2747adea6302f9e2ed33ebdaca8a926a48c7924b4a9d3ae0f1eaa004ace495bc0fef12188640eacd3b73d190685eabdb405019c5c1e055
  | _ => 0

private def denseT0B18 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3428b3928e8804ed0726a3bb4a7650ae47425493326b7e36077912874cac96ce11d6069cc5775df3c854f500c565f1f0f221da28834071be512a5e31737fd21e4e4b04d572252ede1c401037af7710365d83d5786f61b5fd0c1d2eaa9a8ed84b87cd18e41d55f7dcd7
  | 1 => 0x749117c919e34ff498ec9d64d302785f68935e9521a756479836a0d11cfc40f84059c27df139654cb0cfa70b796be8f13f9a0d0418525807e01b881f228f93ee65b242fbcab5ddac4944c5ae19bb5c3365e31ec6302ed6b402ee2ce7e563ff24342d1741a645b28db5
  | 2 => 0xd34a5c11941679ba55d612a5550530e5801c6aff02e6092acb4f0c81609a52a5b88b085a0ceb45ecab7d528a5b8a3a261c01322b3d116b08905a1de4dc7374a26b86d66e373285a51c38668781d842737eddfacb9686db53581382a7833980459e293ab3e61bc06b89
  | 3 => 0x67ae31f0273464f4501c38182ccb8093b8d4768b925d9b0f7b297ad7485c69ee08e447718a234cfeed33a8a3958a90445a30ce0112a4cadd48332b68d09bf58ccdd9783616d58927b3ae8b8c85a1e1007c91d784a0ced92ba22d5cfce3ff5c5bcba6bbed56bc12dc73
  | 4 => 0x2c2fe8b65375c807e72dec8b832743adfb44e20eaf377f579aacabe2acdcfa2cc9d5a452a3b898ef41be93b39db89dd132148dcd666773719830f694532e82d096888b2a911ebcdd79236133dfadac6244ca9b1e2665bba1740e895bcbb29ea0443a6bd4704fd1381f
  | 5 => 0x5313591c3c3a65a5e3e1769373309773bd2d278e220c4765477a6078487d4dd5cf939ec8fcf3f29458c5895c409db50372d8f89c3959bc3d7e3ed25fc5402d165968f12e234d78654d62f0905b774b0e803afbfd77d148a4efc02c6767333d65285fc08f3a6c5c9391
  | 6 => 0x10cb67e4ea94414a98a1515fcde6396a5370f1dfb97e458faa44d46414330ddda8089aeec5568bfb151321e47871cba5d6e1b43a9e40fd23c6254b8232d00b409823f441ff37f418c939c8b762d3aa3afe15488f0acf4e10f7d67af9f3e25de14d32d352644449fa40
  | 7 => 0x24fc203edc9dbbe362b19d1f00d95abc558c309fa44dc34be8f44632eeed91785d0cbfa06a68a6c3b968f907982ed60dfa2d67a9cf139f39e24c86a6df1c970d6abb140d9fd029853722166c0237f22528de27606a5ed65ea422e8efa9e002571ece4e8da5b20ed57a
  | 8 => 0x33e2b3a6748fc47396446804322bb5cb6443dbff47dc2d67f53bd250a53a3907b46428bb757d0c21753778130b5b86afcf3012b5b1e3a9b1977be24a83814ed42e421c314d0094f5bf49fa3c2c66c08cd5e7b6ea12f40091a0c64ae2d6af72905790b693881fd3337
  | 9 => 0xdc19f199e9fd7e4102911ae948f6f15fc9deebdf96c45914a49aa0807d9a87baf4086abef83b6cf2fae5ba9c51e82d640930a231a10192f39c676bb91c9639fd27e91b8b153bfa8cac0263adff5a129316d992bb0850f462156d640ab4a58503f9eb9d7c4c730a5512
  | 10 => 0xd55888f9d9316d511989ee293ab1647c619e9effa36f6d53b129db958584845259cc70e7b3b9a1367c8c52a76488f0f39f00f77062f58277e63e21ce6807ca2ee0240791dcf06443fbc19fb30c7ff8b2368b6258993b4a9363a3f44e8ec99b685b4c4ef1a1674e7b5d
  | 11 => 0x35e04301451adb00329d3beb554c65ee8b21e094563fb23a87b661904db3c4e0e5c0bd66b91d2e452caa759dcd255a740115cebd85edf5bfa91b2945c04d353c973197c0a42996b91cbcece4dcb71dd650aa6085e085d62117e650feafa99f216083681234a481cde3
  | 12 => 0xf59b0d152b4dcfe05edccfcac83011ced68e0a58bafb9c3c0517a474fdce604a0f0c26504c5c4a24e13249efd74ccf4494ed49cd469ff34980c1c7a907fad59642a78c35da96efcdb733b0129efde6c340bf3ffe63266ccd71dd36091e6dd8d5a4056649fe65ea466e
  | 13 => 0x27600268c3a172feef6e3b1895fddc8200b156c54926fafee1e11aaac9d6d8d4140bad1f17cbf8408ca2899f7c43fbecd35c7c762acbb144a7fce8c999579c9a61d2c45d5fdf45a4b51a472acae019406917ef6144294a4ec89c0c1c6e28f8295aabbe3e4d60eca065
  | 14 => 0xc458afb93375f1c402c39e4a51c17a22e659283566279531d73265a61d008c1ebd22106d9a57713c1ff430dc4ec5e17e2a7c5d7d67d2d85dfc1595c478975709f1708db914746784b10482944521c8d7b1c1f11054a16b4ba2ccdb8708dcbf61b9c7d9d9359c9102e1
  | 15 => 0x11d2ecd1a7e4dd2e70131f3c4523a0f9193cd51333428a7b66aece400dfb0b4362e97e021a91fa086bb9034639aff2b6e9209140629560dba4a12cff381c8525e922b762e814196c048768aabc19446e8620426d5ff1108ff28f9bcc0a9fca1e98d679ed301d3343dd
  | _ => 0

private def denseT0B19 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x5e19c5bd8e65fe4b202f440f6f8b90ea3c25089fd33c8d43f45212c0c3e659473cf62c1242b1aa481645fb8da6fddfc1d594c2f068b622c315ee596c26eefb6112db7f99f8dd0c9dc6506732f5fde8201a13de7ab01056cc3811bfd138d9ac3043e350e4d5354d93d0
  | 1 => 0x9c7428ff4afeb4c7abfe6b31d417b410e4025087e1a6d7d081b856eeb7663a8be4622cd0c0ef2547f83663a87bb6d769f77bf5d602b43ade0519c3a7e1679db5bfeafae84e4849081c9ce22eda309cf0586e28e6ee588deca4c2f62d4852c5971fbf941a542bde0864
  | 2 => 0xd8fea978730694712e4a1543ea38809cd9cd3932a156d6781ff9b6e9c8f153b0a22579df1185da76282275d0193e2a6ad9ab6e12dc0882925761d451e76b2ae8caf7711509c0269f00b9b81809f638b99acd05d2831b66b0bceb883aefba508e2a480f8fce457fcf99
  | 3 => 0x5ff5c4e706e0b5c4b5667ad9abfed92ffab565abcfa1ad078ff6f2b86e4a80d502d650dce00b4143573120f5724609e2f11f5dea10c579a18b46fbb6ac6d22e8ad28b2978d2a83b322940329bdda54586d36a34d16cc74fcc5224ab08dae2679c5429b131e4ab07e67
  | 4 => 0xfb9ca720b2b32fc7d87f7f904719d9083c83eae90fea3ebb034b84268be37ea8cb502a8a7e743514ec51d9b776dc7b13c2a05bcbda32857d5d218cf838ba4797df6078c360a5f41962525114d7a4c5bd8c3a247952ef79d65fc335ecdea873ae7db05a8cdb552feffa
  | 5 => 0xdf67ffe4f806feebae5b4c7e8f85902ca761527e2817073f15f0ba5487c9aa93a3367b85d4149b89d0ca898b3989e486d874fe4d48ac1d5803b0575ecab96060683ee15f9ef1a3dc3f835228ee2edccf8887471dafe83c94ce1e7ce354a95e99163826a3ee3060844f
  | 6 => 0x2d293d8de16e568712de87034cca21d5fef95e90c2383dd659449de51f2924152a41d29e0d0bd04ee929239b4be2c1cf084c033708a177eb16a320571dd0cbdc78f0531553ceeb08a3835d2c5db48aa53eb935b9eda470afa5d5326eedd2c746af36ccfda2345b4717
  | 7 => 0xad993a93516fe3ac4f127505899f0c388c3af0589a69901f323a34092cbb3de21da568efb2c2344c09b082da5c2a6d19b14ca0fbc048579f32003a63a6861ca64a5c16478784069f7cd2083eeccb489dc5dcc031dc06555d20dabec1b25cc71fc570a8e3e641aa2a8
  | 8 => 0x465f65c7fb8beed6ac3375240288b299eb818f12e64656ab36265e3936c71036a26132c08c51cc2d2a9a583bf7180a6e4ca846b44a3427e2c5ecb8a47b258a0b2f1930f656b4d5153b5fadaab248da48d301032309561b96774ff6e158d07b9f1efb087059c08bcaf
  | 9 => 0x1b2e4c131b0e62f4966f4cdeb4a357eecda9951d45947563700a16c476eb9d5a9b6a5b090c8b23a04ead35b595e729b20414c239062da9e3d0338734197a1308155373adb367fd8c16e702c72a89608c7bf1c9cd02ff207057460ec65a7e1471b8eca0f38485de0e98
  | 10 => 0xab318f48c6b7630a085377db4de41a6b8197f6b352771afee862279994aeb9638e1cb0bbf3f3eeb8b73085c42f532a10a0dcf7f1c37598fa81955c8a51976ca658e7f99bac59b7f38e20e123ce2eda23de5ead717f7746f1c8a6da384d8d4ab5017c287b2339428368
  | 11 => 0x8147f0d90b1de9330c667a09dd8c2aa7dea5a5e80d609abf18f53fab33d4710a071a453ff694d7768dacabdd3e3c3fe1c4288b0e579f12bbb891da6d9f535eb97cd974872976e87abfee319bbc9af970978a1e042c96dd11ee4149114c34deff62cb320b4c42e23655
  | 12 => 0x4b966939b429c84f48d6848f0f64bbc5092ecf8c56c9639efc6bb2203912dfac7e215edf4e4c1941e95e43966e4acd52d32a0d680f6e10540f73cf6e42c61cf06881d43677bbff16c44308d48c23c0c75264496a7dad0946c95db65ec32a8b0566be76191a4256ab13
  | 13 => 0xed97206382b2ad46f4308f82d686c2c7fef25ba775bd9eb7ef956b35296f15411aafdcc09da02c57c91f2da7e73666f8ee9a0e538f00dee801ddeb413558db56eb440a585ddf8d743cc94f2132637cba52ba307a4747259ef1a107d68b0371c21cf0c04c5e431aa2f9
  | 14 => 0x9d0b64df65f473911e73ae571fd51309d8f4fd23fbd8ea84c3d01a7a88abea77d6a70b52b72ba056c040f2318acca955007f4a4716f90009a7ea195c304ec497975a018cef8bed82194921e1d993bc28cd4a07e980c67b05c1c7fa561dc9aceb0073a6a23b64cd5d47
  | 15 => 0xd959875e44254b6e01999d9b79f539dc6e70e151f8eb2113a35de3181dd5423535a70ce23ea7feb00d0efd1a5e409e5ee28ce74b389794a1a5fb857412bf2f0ed7b5db764ec86bef954088491b2486fd957ece808da53ea37b1e3a901aa2dd4911e26d5ee18bdb33ee
  | _ => 0

private def denseT0B20 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xcdb700fc56e0570662541b17ea8b1b4cec49464f66594a1ab78150085110d6c88f6590b21927583491353ade9e6c1ee28639d9e82f3f0403ec9195ac4128cbb12d6126dc40f6718e12d8b1082b8efd88668c4e013a65ce75340647d869ee40e244633f68d16bc784e7
  | 1 => 0xb929982193a84a6cb43af779d11a443859efe1302ab6c7abcb985586aa44dfbf448f7f68adcc502133eb98ea0d94cf941ec394413276b2ea7e611db50ac9b678611343660c7c5461ffcc7b755d7e322cb59315c9169710c51a8338ad7856f47fde8655f90d624b707e
  | 2 => 0xea47a13a4423d46bbfb7ed836df93985daa23aa84c7fc0118c613902d4dfe517d125bcff12dcde86652894f8d1948fde7cbc4bba1f3633497dd7b64bc46e0f1a75b6cca8e78cc3ef14f51e3d7922d757b56a846fee38b5c46fedbb1728736e6c49d2f678e355d34997
  | 3 => 0xc974c9282a9cd1a363dafc1c7cd3152b88af0133331d5b877a7abbea6d0259f06bbd370c17862f70b9db0e981066818c5d7ef4733edbf090efa3a7d3c53de0817762969e54072ce801bf1794225126885be82ea624ffde693c265cddb90cd9601c2f0c2d18ed104db4
  | 4 => 0xf95dadcfc82321aea8dfecaa2525387455738126d6f9b30a58198eab5ed554a8ccff8c4a55da2f2dc5c31eabcbec8cb604d6a4b8b9b81292413a7af41cfc4ff82ad6464eb76c1213bb4cb7e4617b00a4e950abd3030dec0d9279d99b0f8e5d97f6a1c6d4c1a7f84605
  | 5 => 0x973835615f04b4f35ea35c74a299f93b582446541c0e90d5d5153a21974825e3bfc784a691e0c5d841614202f50b09faa0bae7f5bc9dd5eb8540aaa7e5fa76b084e5602928615f9f8900f956f7436658d952d37a6de0ab76247d91b298f69a9c252aeb659f3b6946ec
  | 6 => 0xbb115c5dd8832650781ba4f0a2cc5191db7f141a01e36213a1249e406129a6ad5a156d76cff9f56483a09738f5b4c45a6871475b2f6e422aec6fefdeb5c9644df750a735420839a417d41c39500ceb023fa3055ec3102e678a80153800b3e1e80f5d787c36143a8dc
  | 7 => 0x42f01a6c7ed7f9f641f6f16ddfcd4507c00a68da4f2eb27093688f39c2ccc73f43ecb5fb93a0d694cb8f7bdcef91b49da2b51d666fdf1ec34fe3dea8cb3292f01be0bad2e53a38cbbb7aebd6d1e9b7206644fa3aa80201fc6f3b74094e37016b0614486b44734f5789
  | 8 => 0x9e6106f5bc4b3cbe642a54042e07c110563ae32bcc7d324760f8a48eb23da09ebe2d311a3a5a3916b4b568d3e9d30966184dc0500fea89c2848abf2edc15617da42e322464398633f62fa709431867873822a6eefcf42a9a41edc8a236f96432a4e0440636790da22f
  | 9 => 0xa635768b55c8e1323fef43ec359d551c834b7422dcdb9ba91d9d328f4e77ede5169f5556c92a7f2f0ff404da3b3a0480512e06d489c473d9f5c8bb172264cd6272b774edd87395515f854e8e500b4cd432ebf3b68f42573d1ea9c387180b36e8f03c9d965c860df35b
  | 10 => 0xac93936916ca8413c25c29271618be88b4291b1b6873625049f3976f10f9c67e9a0ba0803aa1bcf7633aab7474e40fae57c7ca3edee73cf3edf9c19cc4e879d43c627f2050740c7b42965f517c925f0a62eee2195c99c1b1e13a05a0cbac5d76d4f6a766b7ba6fd4bb
  | 11 => 0xd1cde24cbba6e3b410e1d2da328b7009c7872d80d571253780103c404690c863930be3d5a0caf1c878cfb32ac87584f550e8c2867af2ac8287486e62c508d196b7ada221e89d57332ee3a581dfb7f79e9dd0612d722405f68d40495d51ebfb9a6720701d8b45117ccc
  | 12 => 0x922af5210bb30c644776b1e07fd498ec7d7ece1c3f3deb258e2dfbca037d6f073c3f6c91d79598fcd023c6ea56320dccdf0b10836d525b578e4c84b986f3a78f51eafb01513c7d429deff5160f0734da4e54b4493bffb090619c48c721bf5c15ec5b74523572ebc746
  | 13 => 0x5b5e3033a680790dc636fcd993d9a308dcaf17cd966d03900e7d60516849873ab2bc597028c67bfc1127769ead7201150b9c5d8cf8a5c909e5c933527554210f445fa9679edd71c5c0ecf056d0cc139aa5c01fdba6828ddf9e36bf87ed5e96ff8d68e068e735681dea
  | 14 => 0x42fb4b3e1e74433bd1f582914a7e7f73e5285f2fb241f5207db564ce7f6e25388706bf1b75bed8d02d5478306a8d3107b81409606715846ff2857fe586c900a0a6f8c342c9ca913194c796334d80a9d8c49a12d681aada3fc7cb0f403168f89d5c6e99a60d098affb2
  | 15 => 0x29526c30bea9ce6728d591fd00c5632ecc92fd3ac8bfc3450e40d3a76210d3c4082be305c4b6070db961ff9c825a43ca624c0fadb685a37d1ccb8548955b5ca3868fc3878ede8e44ab2cc3bb5e29ed52e78097b51fb18c0bde0e7010c272790563108dafe57851cfcc
  | _ => 0

private def denseT0B21 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xfb9ea34cce4b0c83aa10131374e8e5e6b902a1030200a56ad1a86a37cc7c9ef570e5be4894220f8bb0a7084dbca643b675950f8d08103be4e11f4eb0dc281d062b795b40788aa56faa974baced36ec76257e57e23f14e316423dfd79ffa730517634807e9c96a64333
  | 1 => 0x9bbc9f8c79cb871bcc04c8977ee5997220d09dfcf0d26706c6f6ed790656b9b72be51f501a00c024024a360af6aa5fcaed0b73ff424ab0c92610220083ed143c82783e594094f9ba6d00d5d5bae51cb50956233fe5cf6101cf6510337868af63f94ee44d73971c1ec5
  | 2 => 0x7f7119872d86fd4a087db52d1221ab0ae6a2e3d820c1aa652f57208e075a48b1ed38dce7cd0dc84e283f975a52fe5bdf552a52b8a48e8eea61f0e32b86a8f214744d455ad2292b6169af3339bc6c81f9a7801d311464686de190210a73001bf1b5dd24eee099dff075
  | 3 => 0x9fbf6e182caca160bceb9abe0dab91092c3fec68c6f14a6c72396f3aa1491859e08f1fa30474d433910f917380e5a7ca2e2cfa90345323fbb4a85beddf955d39cec370815e00d724ab04878866e747f15a1a01d21d74fe19f1d2700e053cb067ed382fcd318b044212
  | 4 => 0xc931775c4b086ca32c2d254d4fcaae98d5363f6bccba67dd172163da1bc659957bb2971edb76b0eaccfb293550fa83ed4cc555200dfba4484886f0194cc1d21e471e5f84196ab711d04848a3057fb724e47dbd113be4504b9d94172014eb5c8f13ede14cfb0d5b1b8d
  | 5 => 0x7d3af6c30739560e1f70c433879adf223e0274ddb6bb683384191b4855dba50719635cb1f5f6c03017d1737a34bd0c1efbfc98152173fe10a9926aaa78e7baec5583b0591482aa5862faa89a8e92cf976ae94f0b4c1bf4a5ed91830b6b7dccd2a99a0ad0aa389c90ec
  | 6 => 0x3316b2f04b14a46296fe3ad2f0dc0a1c1c765e2a96f8c5005dbcd1252e0c1e590b1deb5d4c76fe20920ea7055b817b3aa3e7682bcaf48ad0094919ca3e8f1bd8f92c29ff09ef7ffbdf72e71b0c6b3de3f72e6923a828ca9b85a2543c8132d218f70904cfde3d810e85
  | 7 => 0xbb95eb595accf1ab96f07a83a62aefcd98e73af2f0afda131e6750a581e037e7247bc08219721eeabd7c4fccbb21fd2a6c3e484c13bf6931932cb0840589d1b2eabd5623fa375e0611ff767ffd14684079614a87f1db2455aa6002f1c98cba6e0d44b83063b064b284
  | 8 => 0x7369b0544ebcfa84bc141e3456634558f93f3ef55606ce6a41d07f539f2bf37e6d5ed47357cb3877843ae04748108936712d64675ceecfa3af2ac68d65796a64149bad178ed0e42a2416fce16481fca62b2f165d1a77a6dc0ddadb8fbf37b69413b7c04af049df3d7a
  | 9 => 0x5b2740285738ee4000a2b066216b70f392dbaacf90f2ab01e8d11c3763f340c5b18119a15fe7469105b905f7afc6e3014af7059aa195cee52fbfddc150625b059b29d166a76cba8cbe78e1c0953d2ff588cf2d6b9debe54eed35fc6fc840a02c7b2a59de2eed77bb7b
  | 10 => 0x69645b9d6814aeb24cb789c3b1c9a6b7d852bb50ac6b62cecd1e2cd02124a466e82eaa886ff2cb2d4ba744474d8cded1602c2a88e2ecaa40c18f1243e5bbdaf3f0a21882bc513a7bf88e97488ab0de0cd7157e9fa4a684c852c5aae110b904740119f744df7df62372
  | 11 => 0xd2bcc6212e46af126cf73b0dc45ce3a75731f42beeb57c7abd4b603e565e6f7f928b7e171e758b5e3c9edb92ee409d891a7348c129db7b46d59fdaf39052d0d5ebe6c8f32acf6bdbb1d3369d3c133e2d7a6b8ff3da0666289fc5c07616d8f68b444e0811a97e85d409
  | 12 => 0x2ecc320f769f200207ae6e144ea527d03798f1f688284372e5b6b5c2e96393b63fbaf694f38b548e089176728d4028bd00017feef1238922075bb560edcbefa087ed14a8fe9f13db1ce1ef4488d73f76761958f447e5e57684554d12beac7c611bddc1bbbc7584ea4
  | 13 => 0x1e3b458b5569b6b6f7e444d0c234c76b0cdfa609518c8c3f213dbfd98f56a5e2f64efb8bb86cf932e91ec6b7bcd179923c5d609e5c8721c9004fcbae2786af8dec841f3c0af079b7a30e71a23a89eda6b564246174489fc42fb3b26f4a7282f2d8747c3d86bc6b05d0
  | 14 => 0x6e25af56529826b5d83de417ea134ea1b616fc01e0635c94cb34b1ab08526665bf636b5e8e8c80469e283354ee3d35b4862a2e73d8fcc7941ddf30155bcd5e9f1ecfe1748bf7482267c394cadd37283657fb33cb905e5de2898e23efb9b05a3b740c9226fb88134902
  | 15 => 0x90db3030af2b795c52bc4579912815177e7c501486f212f99d4eb7edbdae31e7abe264dbb5cacd6b4c702bda4aa542950e78942c4a20400cde42282da9262302cdca9de57d6e6c420feec611a6b4c5be22eecb6aafc08cececb769341f6efb12272a9935d2208538ee
  | _ => 0

private def denseT0B22 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x6ec8fe86fc9d6a41f8696f15db0ecad3141ecde0bc00f2740e2ee93f6c61ed1d36eba8f868a99e8cf22c3cfb9ccd17df0d0c47b7d6acca7f25a449e0d18383bb53ac9a9a3a70e20d626848f3dd5ad42ab15fc94871f62ebfde87559a8a37820cacfe0fd5e5ea4ad116
  | 1 => 0xa3e288633915a0cf5f15a5cf972a5a4fc576249da97285d38782daca41d60e03a1d9f654f180bcfa1bfa21b9f126fc436945bc0ab018aff0322fcd038b42c0977955a2d527236dce37126142bf2aed7ca45726aa5da08988bc4b4ed0440d235a81f2ea8023e6ed7e5b
  | 2 => 0x98221f3c2675e5cae4e86db3569650a430309d0742cdf08415939e0b319f54d5fb392fb9081d19e2f032fbb38af1c42a33fb9fa09699e42f7d015d4a7399346e73f701b762acf8b7c03d6cb4c0bcc1fcc10be6e74612b76431f0ca24739b67152ccab4fe370ab78812
  | 3 => 0x4fdd6e86c93ee0791a2688798b39acf4d3b031cbdca6df218cab6927062146e904cf4d9c0e060b839dcc47ed193075c1c36d90460d9c2e2b087220663c1405307ad6848de40abcdf5a7f6a9e3cb229fedbfe3c7402243e2f7b04207f8c68452101ec2e254c12b8b556
  | 4 => 0x720ab0f3b8929c5db90ca3529357c40ef3029c567d6b708158a8c74e0c325164348a92db25caab898022caeaf8152e1b2a2f8a3d9e26b3a51f65b654b7b2fe6f57b9367fb235324cb904c17825794ed6bb508bfdb511d04d99dcb792e3da9d3b0eefff8cd474dfa1e2
  | 5 => 0x9df7fccedd59d870a6cf8775fbeadf8b02dd81b51daf2af59c6f627b2012967b8e88a883a23413cbf426ebf6de8ad0b0457d8d5076d594bb7b3556297baa41e0dd21dd736941999358e5be62ad685853b9ca0423b607494f243832a1cd360c1288bcdc38cd6b1d5696
  | 6 => 0x24333af91bc7d438145f94ce54bd9fd62f7688ceec5a0fe4f86ca5c14956e7d78baac740d3bf486ecbb030061085e3b4749b4c94f321e418fce954c8eb4d1fa4343715240242ab7215813068bd68d26723232d3200d480857a71f5ef136245ca2d31b60958eb846216
  | 7 => 0xb30cfe2e6dca643d4b8441c47acfbea6a3b62cce9ca28bfbb3d71e83532e40ee93301ece88787e749ef189cb8fb9ce945ef0cecb49c9914cbcdbf20e91d635555c769a088330c03c3ccb8dcc828a7246dc24d754bd7347655c7aacab4a2710f6bfab3d748ba1c83812
  | 8 => 0xa9b5f8ab71b56e636eb0a8243c7634c9fdc5e9634b391896b8f8d7a9105b9795cdcf0fda2e5e5101bf7d60495da84f8bb64d041e57790dacb9fff9ac27f81fe0f09a52e48d4abc6853e169823c18f57e7bb52725df6686e347b0af08bcec81ab7d1e7b79c2f536e243
  | 9 => 0x501ccecf186c3a1378ba8b4f2a4da9d4c39f6f26eb544589cedbf9aeb11b08e3ee0fdcdf6b82c2c4eccf919c07ec50efa4f561f7035533573fd105669cc5230ef854869ee6f79ed3cd66f56911c05c6ffc65fb2f067e6ebd4f4648d600d80d76498a3b7625043aea81
  | 10 => 0x973dc68a98593ac9ae96812f5d9575025313373da7f38eaa48c707a7060cd56072954053ee5830d2c3ef795be16bc5856e8dee494ff43342d2178bf700e82744ba7e5b7d7786314d72ad049e24ea916dbc00c21a54874dbca4f53696c3ec5eae4d9e90269e3b62fec7
  | 11 => 0x74cad5fb1b9a881c8f0275ebe8e03a4aea7109875bd24005e43651208edf93f4d5209e27056bbdb2252d58fd12357962d5c74212e08133f190037c9e8aac14eb5a8f15176d48dcadb0b53a18e99dd6f9c5990acdbc5630601169b6c42eecd62c7f9c655bf77e0d6a9e
  | 12 => 0x637ac88f2dbadfcb82254759c81bef0113c74170c6a6faec89541810f6d111b81b29e10359785d3ce83744adca85e7bfe1e3215112fffd62ae1e39432a27fb1de5b85cfe085a2b1194f0ac0699af3cede1e8e9be8e92851b9341d62f32dbcc6cf9080d20c636dcf52d
  | 13 => 0xcbbdc7350e87d2b5f1f70b97e907634610d181094188858752991a5b56028a966a3355a840973c5351ed8a61d3fb3d779633a74ee763e4e81e1bc456855d22652f0fe929bbdc9a546dc0cc42d70f320edda37bd69721ec47309d5a4c91c31e7dbd66d0c1c7ec438a1b
  | 14 => 0xd3f36eabf4234663a32ae3e50d3218065198a1b126b6c11c03d5bce603165ba7cae3558dff09666d59031505c3a982dd698eb0474c4323f504747d438b4bf0826d93d9b6d05cfb491498a125c04c6b5851d4379eebed9716ac59d06af90cd54e6985a439e388943fea
  | 15 => 0x77d3ed072ce34fd72f399e5b3f324821e041ed205d38abd02b450d52c6187653f55cc586315027b9185cf010672dc65af98053b2a3d452bfedde9540acff2771505f5a230c7c94eeab6f210d7e54ccc51ea4c9daa0262ea14e606432e37ec556763809788eafbe4371
  | _ => 0

private def denseT0B23 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x220d90d9a3174de52c1ece28c2a39f12afa560114adfc96ebe0dd02f951fea3f92c5f0c8e0a503a1dbe5bfdaf3ba29b73fa2019a93f8bca1d44c4c2959d41612cb4f1711306e2a9b6aa80a0ff7f9d5044baf345ebfb3ea4fef93a83ba7402aca7d6ca83162f919e056
  | 1 => 0xeefe7d3a692ad926fc723738512d86ee95194150c788fb73372a246fdfc18dd1a8f092aaf23c1029728f0ce8bb47b400f700ca155b1ff590df973f8d6b2bba2464d4510b14f943705fb66269a97d3bc18e07e5db40adc343618e45d49bb52bb221672a2647a0d30b68
  | 2 => 0x4d931e48696f94474bf83f5d8a32e13a81a9f78c5d290d5eef846b0ccd957ecf3c2f49ea1a63c7c1099457cc385cde5b62a4af0c67f4e1dec5697f944e167e7f957a0fc886f64f58dea56e390402e08fb27a7266d784c584836f561ac7d45d421cf834fc2af21a1004
  | 3 => 0xf36d7b55e79d7408e8427ae430fe9acd52e286b90bc6309108066b28e0aca4e5ff00b11934a1c1ad24040a1b1739c752baaef5b7e45a803394e1918a8990822c10035d92266a4010ebf972971f80dae7e52dad4d4915ecddb02524058188a37ac9dc9337fd40d230cb
  | 4 => 0xb1c9adb59b9fa6a66c54ffa81e4f6b7167a523302635433574b789d898705fb7ed334d85bc202a258d09f8c438a597e2aab27a9b08b87961767d20344526c2a39ccd041e50093d15e8c9eb73cdc880f2cdfb246f093cab66753dbb7f58b2200ad1c7bfb51cc07dd993
  | 5 => 0x839a3c931099973c3659a4a38bd4e20ce16e199cd54720baced0ea57321c12d3eed932e91bebf1dc5bee0c72f6ec156e11c724ecfc2385244e9a1aa1145a8cf1c6ac03e1c03a1f287378b7c8e5509fe8708116dece3d24c358c4452d03ee04f13f4794ea5a8ca60b93
  | 6 => 0xd6599c851145c464efceb068a9bab3b686796398389c92f918eb91bd3b4aabd211700b2754c9902bacc4232425cc14bea0cfde410a07006e625fcae823d57bcc9aea8ee8e9415e20a84a59aa9351c4fbc034136b619b7e5c327f075123f55c26b617e26fa77ada6e3d
  | 7 => 0xed099dcda44e37c054cb294fccc0a73b1e086faf55e8053b48344af07d0f5ab05c3a129207c8e4e7d834a663545aedd715cb4d8fc78aaf9e2bd6cc886a370291387aebfb035b282ebc132b2cfb14f2b45805f2988d4299a7807db8b5e65bdb01bca401f89b5a27908d
  | 8 => 0xee6b4c1e341bb53531f444b228badd0b80421e0e0998ae94490989ef0c3274ab92c8b4dee0ecd0134d75fa43e8da8789a05e53bfef33e0f5522f47578ee9d5d1772dece0447cfc82eca393933b3f8987416b9fc816d8906d0b95dbada298a37472df15afca36664e54
  | 9 => 0x88b4dc857a421e0de5ff82848dcca31535d5efe69ec89c4a376fe683544bf25ee72761bba449c4f7b1c0d8a3a13951d70c4d5d6f430a72670d4209c49906f2764de9715ee98dc3bf7b25eebc9ec06a9c9a3c19930ddbaf2e787727511638154e38c0a2ad584545b8c8
  | 10 => 0x35af232420c6dc6cc2233f75b30b519ebf00e86420b345a73c02ee1d1624acf48c445f9f5976f1ce4577d36da167d190bcb75418a1ec4fba72df928608e575b615db69aaedf6e91050f5a40a0f3eae713b52369633561a85eaa63f23273756dd15c55f6c3ecd51e41b
  | 11 => 0xcf2bab719ebfe29885457ac919e9bb30f4b08dcfdb2d3ff9102d6949c23fe422be40f68d4f569d5cfe8ebaf64d512b421d2edf3ec23ff768662000ff4461ed4da3563098d4e7722f4d7695f8fb7be0768b26e79b7d31fcd6213abd64e0d50828c2f14d6c5449cd203
  | 12 => 0xf57fbef9297d6b5a6f51d1e4478c1dc4f4e25bc0d8db12137fec1e790cad81d964d4b7bfc12bd1b78c6b3f7eaf078ec914b24039f3944826cd67640b64fb0eaebe105a16c0ff83a341788f4b4384097f61d4dc52f82fc64ffea9e844ddcba874cd61def11d1607f048
  | 13 => 0x6c5a6771a6b73987fcd4cf36d9a486710d6a0e49b1b1db6220af50ed7e7d6327ce37b8b123415a571369aa296f0eafeb51ab8ec9451915b31dd3cb7d324220b3c0e3012a6c3e1030a0922111b284ddfaef8c41e28f50c1a001bb8e5b8ff683684ca2fc7646db53a7b9
  | 14 => 0x74c64472d768f7bdd26f88bb833dc25202910874983e284924c0642fbdd93e10edea923ec83d5b5a28e289cd811d0c4cd7bfb27d005880c65c2888501d30b8228d488cc5d9d7f2dfac1ce2491c651f3ae65ec2858c969b198868a98af316692dcae402bb837e89e98f
  | 15 => 0xaa500989774aeae7366baf54f197a6986970d42fcb7ea765650045d2dbef8750c0ee81a8a4ce5c83fe6ac3fa3cba5b25905bba5fcf5a99818b372a9ee11c2cb92ca2eeff3076cbc7b58643273da6830fef46c9e277b8312aadfc2c7442712c2022a594019b80c4d58a
  | _ => 0

private def denseT0B24 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xa07daa928c98eee3c37765cdb10cf5377408be40ffc24ec6edb87d930a4496af351d97409b0928da6b7d57a0ff922e99474477cd1ccf34ee58294ffc3dc3de8542eb79f3dda4658067142f81d7d236bbbb48865f80f91c826809ff779289f665d3b6e69aaef4964c95
  | 1 => 0xb8ac6e4c792037f6412fe3f53c4a67e9e2d5907cc052974b2786669316faef8e73a3ba8d259348c80616350d0afa04a77d6c19b6f3572a30abaa74322e089c4c8cb5333b1c45d3af8981c659ade2e2972ecfec21297da2d6ec19c47638a80078d3b1ff62059a374a51
  | 2 => 0xe9236a9d311abaff2d6f020be93de4a3196a5cf2ba5b96ee281bbe721a2c314b238070a48dc31c1bada7e1b616f9b48bf7380b39b3268e1a3a415ef94c8bab0c98ce0831518768c77c1c01387d44aa679ca36a9c798d9d99c84a8292c8fdb0498caef4dd9c6ce90627
  | 3 => 0x825ff5591832e979d5bfc8340a3010e79469cbe627b75f5bc68dbe5a68298138ac91725e3bfcc15460ae2efa78caca596f7bbc4c08684f7b1cd70f8345709a0502ca40cd3451d8aa0cf1d036d3184f937f2f174c09eb13471d4b0cd0a730ac8c022cb737327a8f607c
  | 4 => 0xd21c926646b8e20e1fc9f019d762eb4c4d4bcc492fd1b6f0c2888824a6950544275a4659640bef2084ac8c582cd3c1ec717d25fc5f3ed445b02dfa6dbeff4c3584409e193ad94ef6b6ca9c14485bebc3c94359b5a9f59b2d1720123d3476e8de81be02d1f15c914b57
  | 5 => 0xcf7afdc525ab5b809de60085ddb90dcb60dd3e44092740f9ab5658f6f6d1bf55a6f90d528c2a387afb5379ccbd88a1d97a069c8ebb57767ee5a3b62e7c3183911ee79e7bfd451aa36f17f7a3170e8ee6291877091e8905ad04dbcbcd87caadf1919703bdde7be442f5
  | 6 => 0x6103940b7975432e9f9e5ac21fcadace7f2f50a942846b6e522a16afcddd6d1e6e384941b1e974db0047e29cd5833fd5d57951dcd4e6e3fb14a8b4745ce3a870d718cf232d7167719d555bb45b3a6539596562dbffe05bcad273c880c86a3586b7cde2fccc1f1bd6ff
  | 7 => 0x2bd1c40bf30800c5038e2e6fdf34dfd94aeea90b2e73451d9425888efbd00ed7cedf690eb782187b40800bab69e2ecdecb1ef542b5fc17e2273e682794d8e0e74652a69b56a71017a5eccd87ca6f387dbfdef17ac1075a117d30e957df90d1d4c0f84bcd34375ad66
  | 8 => 0xd704791f25c3758aaaea2805a4fa2105f133ace65da21bdf7620f5ce4e9ca9a1e3d8715ad64eee34d59960693764951d1e704f4ba95f0114f82dfaefeb04fd4dfd006b816311990c8ed480e06945c173c1652ce4e7adf04f5d7901f7eca94e472d7acce80aea6da0cb
  | 9 => 0xe762c03f5302345b28ad3a6195aa92db35fa8f95a58c3f293cf79b75541d2da7995e3260d6057950e1f61ce026f73a4d5f6570b587107deaaa4b61295b7ff1351fcdd245821ca9d25f296ce07542cfe1b12c91ef10122daaf328f70efd0414e10e459c2cfe893b8595
  | 10 => 0x909f36c8bbc1a83452f91c5a18e634473b9c6c2b4a8adfa75e3381e87d71af5ab4782a1d04483486804efe1683830d8e60bf4507f073c92d49c64ff9886eb65cb244f6b7eb688e7a572376b610d9927afa26580600ad683f49b95e16ec8e66016715aa021cede5311e
  | 11 => 0xc7fb54ef418885967beac99f1a1ff0ea443130322a613c4dd266401d0cddd5a92375fd2b1671f7ba0d8efebfcc6a6c651bed6ab37089aa4a865705916e870cff9a91f5995cce77f14c4bc7d08b0e0d9e7076fd44709dcdaf34a9241c81407bc839ad18302a33202179
  | 12 => 0xc7fe811dcd02575cf2a7008616caa0a18649196fbcfbcce93464934af3931a32d3e59207bdde613dcfa25183fe33f9974eb0d655e8bc62eaff6e871e19a490f5d83ebb904967cc64ac20878df4fe7701a62aeb76bb9284975713fbc509075008ba42e563da3d20da04
  | 13 => 0x9c913450763d9a76d6f10084406e012799d62cb873977fc44c3b7afc6543210ea6efdfb1098eb173117e646966d636b8133524b62d1f41c629f4c33901e70a894663578aba1a9937d94d3372b3cc56ffaa897d24d3eb01f437c56827f59261019dcc8986899a0f58e5
  | 14 => 0x227c117b3c337a9ff1d521164f8757a6680a929826ce4746bfd9491f8e1d1673dfe4e69ac03335923fb297d12c15af01c65e709616eb7452071c2bd4b055e098f6423ad5129eb9304dec9285dbe99237bd101502bf95798ea73c93cac05e4f22a5ade7eef79f812e25
  | 15 => 0x4cf0452f94cf11e231d6df90ef0be617d3272d00df933809ff10acbc129449cd08182bcd655a1b885c9efefe5f03b2ba91a051addff36c62ac6296f16b7e46df4938adce12b0b9be3bfa30d9514b4988caf063172efcf7afa11129a2b776a46b34f84effaaa10eefa0
  | _ => 0

private def denseT0B25 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xf530cad3b089cd0824714caa77e92221f017d47d4d0376a019d94e51b96248158468c30674a7ae2aa34ab7f44bf57e746c8c36872d618a96c1fe655274383af1e2f9f1993bbc6fffdf2cbed23f953dcf6072ce4f7c905305937584045ca5f3567064cd3ef3960d2820
  | 1 => 0x42c7b6f36daa3b6238631ae79ac5529f968a4932ca04f439f5e55dbe5c6a8e216f91ce60f9bb529130f099c2e74366995fe30aa7c9363b898445daa8c6bddd0beb05e55f42cd4c7a99d8e4a12098b5455ebe2202609ac7a39b83000455bbbd0d244f903077adb2d1e4
  | 2 => 0xcb7a5b8c7469af61cd519dd5571463777388cd705670dbeb2f8090af47d68cc2f024e29d21f91c510bc1695ceb94e0edd7df5a30cc584a50f4f1ab9d807a2b39e80308fda63c023a7ec91e87bb270d3c6ec9e8e49a179482b47ac9d87b04e5113348bfe28a7587a90c
  | 3 => 0x8bd80766078a41f9eccb60f6d235309bb336796dd2e169b49ec04a275e5300cc6ec7c5eab6b92f606c47c4acbf5c4e729b28825aef71224ba3cc40253f2bf66e1467494e7fc188b75a2acc0f7c80813d5e1b0f18fb4a18a82102ec8743d5ebec8caf800547c6412453
  | 4 => 0x21f44b6ba60432d0eae6213759a20c72f169948133d16a41974cfe0367f926c77c3162bf286b493b3c6c8014b796101c971ddd44779ffe1d5a8c7939fe656330019a1d593296b1eff63a0b9d95851c3964a7b645e460c1198d82891a999b5dc3be66c28723e048bcf0
  | 5 => 0x9079b616bad7a5448aed0f57e6f75f021c1137a1aa5f84de7d6e76361c86b54d8c8620dab51356d0b3c9b8002d59b53e69248c7f7ad0332e86570e129d1c9610a7a830e71b2f077ec2fe209cf0e5650e814a7fcb2a85cd15c081796e7e4e7e8dd95b899f87b7184095
  | 6 => 0xbbef1af7b565dc51f33404b9bce097005295b36ca6ae8c8aa705295229c61d3fc38c8365420bd188bbd895f6931c2014e819ad9e1009cb5a4517b7881ea07b04da37b2a1a7643b4d97ca0968ea217df206d0813fdd9dc71664cb9e7da86074a8508b10363ae0c03ba4
  | 7 => 0xe15c45207b74fc7b3439cd73ebe648336812484d4ee2e132ce147fdeae769847f1ec329afa2e3d9710e06ac85ae083e0d7435660fb6c59d526982d2f3a9aa136a33d49114405eca3f6bf62c860caaa561b4a4ed3cbc579abc6f5f35296269ed60ac609fa9e5154ef2d
  | 8 => 0x3e0926599e7d90385c572d27c5d8eb26c267fee542e6d58c2ad1f04d47610529eeecb9ddfd7195c0894c2179a231a66cf5591d85b923c83e1e5e6f40449859b1d0d3e00efb689a73e5f4f1180b6134d7b29b41f0996916cdd9d358f7886d0458a7b298c7c5004b79e0
  | 9 => 0x7df2d76facdc57d6408b4124afc341cb176abe8d1afdcf65766ac8e2cc1d571d8da3afec1b551b2d57f5df1d1ef5ec3ef8fba5faeb1cc40295ffc01e540754ebe18e4493c1d2493f04a66f9e12f9c6b8acfa2e303dd6278b0d88ac073ea52619b015337df043c5ea25
  | 10 => 0x6f6c1b4a9f3ca1fa61d22158a3f3bc17acde69fcb4b31620ac107b50e28cbcc9eeb97c674c5a88dff45bae8ccf6cf2cdf77aac4520ae3747fc4d5f42eb20c700099f9ad13281f7e4855a85d6c31be01bfdac781c5c57966870d0ab627aa75504925ccdd7e62c75ad8b
  | 11 => 0x1bdf70e5f075c3ac9b297d11025c8e3c3add09db5e556be6f05156d97ba2d3aa26924db12ce99862dd11414f3b62dc64eaa1cc6b5f0742bb5624f4a97302cc42854ccb50ac434a86ecebf4257111728058b840b0027e492310117f3d8068acf3474227de0f5065bd0f
  | 12 => 0x21bc1e6d70ad614b27d53dc89bd8bc7f86ad561602ebf0f17a6093f52fc7c854ef672f4921ac294e9b73c338cc1ce4779898f4e54c8bb2764d2651777b0b7231c72c41385e04be8c984b0fd0845906fdb59643e052db78fe8210567722bc3d2bcf09988213526765d
  | 13 => 0x26cf2554eceb9301796faaba29fe6ab05813eccb12422728031bf21ab53d7f6523796b109e087a5e06ad3af360ab25abf01bebb79d884cafffc8120fe2bbbacaa79033a358ee048b95793324b2ea72c341e6a2a255f77afe041d8a355206549cca01f81e658bec8bfe
  | 14 => 0xa507eeaca08133e8affaa95466eeaaa8540ede5975ee864d67567a94aaf8df806043e36e49ba5755057ccf359b40f19f9d23188496259c2269a6d580a9041a70ffce9fea8813f922ff3651ce2b786eface23dc879450f7d086175cb299ffbeef7f0de36e4666249a12
  | 15 => 0xb0723ce42e8cec7f266ff7846a9832fffe21a52cd46af5f78a11f7710a8454e94fc3a68e596621cd45dbb87b6ac2ab14132a5f8f22ab1bee362626f0798533404b23ab8a958410e19f79301fa1a19366e5a372284b280c389002407582e92c4f38de96f9fabc3cf0ed
  | _ => 0

private def denseT0B26 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xc53f613d55e7b93e17007f5764a156f9ffca561af111bed438b16ae1f55bea58ae23a8a34770c534b2687f1ee0bc5a0b2bd78fb3de67452ea4efed1708d7dc4bfd26cff54607e7358ba46f8389e5ffc5eb2c61fbd5bb276f7a6317cc5a285b47ea75c94f8216164b3e
  | 1 => 0x2eaae36ce1715e6091a9c9dc20ed7653dd31be0c9d7ee007d533a26a19560993322a2393b365b72f47e7f5372da74b55e2349d59a8352b1a8a8d7ff7acfd28223e0c4724f7e2c8bcaecfd84b80c45af573598d298b1e3b83c3c27f2169bacc70238b1334178668922a
  | 2 => 0x4795c1de1a071facbf6c6b445b6a59100d10519b980bf4b453263a3eab28f7e469eb485fbe2b5192fc49a54090fb0fa7137823071cb43b6c1431bb9262713dbb7826a7a55601ae350258287bc8b90a7e019416b13c90261fc3b3be4b8daf41a1767e9160390d61ee33
  | 3 => 0x9b6903e7c7265dd1daaae82bc97880ed4af3ec859d94679d6aab3b8f3f647f129b504427147634e26ead7b0b87417d9ded5d5f702cea6daa71d66344ba925cf987f3d2ba8cc00bbd179fdec9544a7bc39d4a8a88f005d3e6e0be779efef774bf88a53ffe42cea06d8a
  | 4 => 0x92de7e5eee06572b60bd8e39a2da23d6d0a35d8c1e56d32b12df55b5c886ba0ed12ea89c5a0d1966778cb5c7bb08ef5efc6e091bb4e0b5cf155624aadf26bc40001bf63206ba57850d77dd359d35639397f2da0bb3a51a0cf131119d53fbfacfd5c59d4b12380e287e
  | 5 => 0x128d70b7ed1ffe529ba1d31d1b93fe52f66e82e889fcc631be5645732c9f3990036eca91229b83cd69e3fd889fc2cf99e011bfaecfee2e5ecba77abdd4c60563df6e813122a2281e8e0535090d6de5a2ca851354f9af345c17e3dc15447e8fb1029626c2ca2191dc81
  | 6 => 0x98a9fdf809a69e0e6f36737196c9849065e46073221f99babd6113d9e8fd09536525c0e8f95096afa90bbfc40bd841d26f8f83892d03eaba3437b64ed92f4dd393e074b32cc38496e366ab76624f1ebaedaf10ca09dfb7714c438904e4179529a0ebc1bdf6fa1972de
  | 7 => 0x9fec349f026bb4e8068c3699cace7432bf98bab1d6091b585fa3d3ce11ecde031b467ce540147c8c1d6d6367a52741cec132e219677bb6fdb3b1b66d426a1ef1b177f15291ab9dc9023653007af00c1f27f4e6f5f2a1f59601ea9998ca615bbcbeae2fd6bba608b1f4
  | 8 => 0xb4f111db1f7707c563e3bba10e0d0288ab551f09c4374a5948bbf82f8e83c595f4cf50d5f79eaa84e408918a466af68eeb7d83c383291a17d5cf07bc3b33778eaa1dca3200e18b108b3ba7636c656316fe84ad80446ba73aeca045960ae912bcb421df5aec90c1cb30
  | 9 => 0xb132ea14bcc25d68200c348cba15d85b571d58f41411eed72181bad8fe31dde3359cd7674b7fd0cf70414a9b8640d550d9b39b3854e38f833013eb82c0826ee583f026c1f278454c16124e91f1b4262bb3121dc118bc40d84e2fb109fed1fd28a9a1f7b5d773a6b7ca
  | 10 => 0xd26f951ee0dcfedeeb49b934989952d0a29a388c5439de5537719cb9929a9e19936484078737f440ace746da5345cab572b19a812edf9b9924f669339cbc10950403b1a7ab0fe67b9e0f050aea633557a135f9957eac3f47428ee23a54b244317615e8492b6c3c72e6
  | 11 => 0x7f82bedd6f33ac66bd2991eb57f683be5bc88ab65864a239bfc260979455194cb88395bd30a7445623720e9bf383822e32491bcb6be57b578fabc304b1bcdcc72a7ee18c953e6246a3a72be393ac533044131d3465c6e40dc7cf535c060369f5a12d729cbb1333ca7
  | 12 => 0xd72c1bdfcea1e3ac3f27ca7e827d737a7fa7d8126e46ffc08a3e78a87fd955a36fa34aed8702ac848ac2b610fd987b9646522a5950a2dd39530f31fc57a73041e7ff14e1a3daed43720b120de3547b8b5a8189b4ee7f2aef69f9810fcce9e35c5acd1775e3ed20fee2
  | 13 => 0x6410e21b84ea919fec2269747a7f55a24f8adb2e8e7b461847c034f0f0809ac3bfb76b2c8a3b506242b405b25f826b0095dd283573d6f375c06b0adf5c0de1b2db11ffcca43d897030a3e775292714518ef994fd5c7b075e3cfec674d8279419f558720909c67631af
  | 14 => 0x4de38b345ba0d2271968354a68ecd77f117c13ba2df03c547748975360665d3df4ce6aed59032dfe3212461068260f1d05e9aed0f8892cb1bdfd5611da297f35837dbb407e96533129187471e164d20054d5fcebdc385c31f041de54a9db783c95a3670a3855e9fe99
  | 15 => 0x74e1813cf3b86e98b26209f4d87440bedd00cc1be5f8bea8bb809f20669993bfe24335225aca066f5f846a4250dfc8155f66c6a24a53d216b226ebf1f77c9037b5d614e3ac4cd2b128a9949edfbd2306752e571af328b42dad50ad237edea73d872b8b3afd01cb81d5
  | _ => 0

private def denseT0B27 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xcb81cabed7cbf3a16f227f5893cada87dfdb012498650ab9354b89d844fa31a34a2c78eda40383d138cf4ef0509edf4f3e3dc2656d5f05e7dde3628278393b6107ea323544378ec5dc9f51cf272abc2f2b08c81b6c434e0f553e7f39b8f3e2670e44d468b6ba5fd50c
  | 1 => 0xbe51716a4b4cd9c6b6ea7fb9c327edcc516d4a4fe00668020f88b1b129db1657ce920a5daa132e7dde23feff24fc980a3af8cc51614fbc941a17f909b41e3add47d7bf2d911cf6506c1b1c3d7643b78c6f8b1e647d203245917d19d4b5f8d9040a66a74dc14ba859e9
  | 2 => 0x1e9ec35d3ce7d67c252ec19a39534ca35866f92a7625eb04bc726a59cbe72932916769398b29f084965fed766c973bae8793f6afdc73ade5795f4c109c1954e0d6fb5a7f478b2e7c1edf7f6d5ae1edf7484ba7db56898332ee3510a354e9611b7eb31f2c1c885833bd
  | 3 => 0x5e2c1ada2193fbab00778510f4ff535420e6c899f5dedd03d027e0404cc1af6321943884fc54acfa479bee36afa6e1ad3584f6b8e7f3fbad5e21d312418cb12de4f446116b0e5b3437bed1a4b72963c3af93cc9b4fd6ccfd85fb8b0e67a54222244eadd70e38a8a0f2
  | 4 => 0x50798f10cd32980834e20f9ab8cdca2aa879e9c3730302a66b923caad564c647e4c4eec43b6636297a39da6894b2ece8fae2c41a6068e1e0c4a1a18d365cbf3e2524861ab5257be1198c68602449c9e0857ed211d01762d81ff24b7c6aaf67b0dc9bf38221c1ca6482
  | 5 => 0x28f973faa568d1b029b79a45391af0b8330f85d8ef641118e605afe8e48a47713ccac2f42f3060c6fa20ad2e73e7b81a67185e2817a955398b57e2f663cbcb617fd39d39e7ac5d4270c2fe6ea655e8ab4d04ef592eb4bd6c28c28e758f650a12e0baec406f40476f3a
  | 6 => 0x6ae1c1bcb8738e8014c288f750cc9f4067ef518cc5b14a33c23013d8a2a8cf16647116ce659b6e5a98ba08c2c74dcbc51298919142b78d004fc21eed5d14f4cbb298d04089104b298fe3bc0dff956297b759684c092538936ebb51b08c0f86d4103a27e1baac408d01
  | 7 => 0x4d5be66cc8b5c71238389ef065be07b2c14111012ece6d809fa3c2b014a3ad7354e2332d269955cb1a0e07ade364f6dac1c4b02ae450e40900dc832049b66571ce57e3020d3eab0c6fe707aec52c47fc54a84d7c05a9eb4ca1f3fc680b1cd1406fa15dd028fa54a37
  | 8 => 0x74b23c83bc425bed756bd2ba8bcaa50b37c086473d06d315aea5bee43d4654046d7a5c5afdaa8eb3aa3a9ff6ac546f03a40c5afd9d12279f481712b380ad229eb6c91e8bc12076d39f7093cf7be19356e8e482898daeb454f291ebe2150d877d38551de0b3162f2c81
  | 9 => 0xa664fc9be14e154189e8802bca38dc8df078d75ca07d06eb7627a9183693e0625b254f550f7c5c3346b1a3cf223934ae7636a2406db457142c6037059040300915497baa47fb603c8ba335480fe5a865a834d8ebda3d47c8e9f1dab48c5113074efb7a40d9e0760c29
  | 10 => 0xa03dd61cac2d4b7d671578b684a0b185b29097ffad81c3bf781ac9abba16e1123f5afd8f49589f48d7ff54f3ae31ffee9de227438044e2483ce476820331cb29902f87aed9c01b1de09639829601cd966743c1927755d18da0c9e2134706e04aab7f2cd8511b2c3c7f
  | 11 => 0xa1ac8a547e75c71293b38b40265149f49f26c5f64be9db499a242b93d761bbf77fb7fbfdc18f37200df7571e7fe9a9b3fdcd1d8c74c40d139ba69b9adefd720b776ba8426c6b95b8ef2371478d72d7055c3898bf63529781aca30fde6a5bcf669d5990cd0c1fb17a0f
  | 12 => 0xbe5190af8cc68b0c32a84fc740f6999164ea99f02f17ca84c3757aa8ed048dc5f60564fd4a835f621e375dbb86947bab35f951b3590e2e94428ea2e9fd8e2cbbf923b7b9b14ae2a0ecd836d021d022617f5d6d784da459cde915f39c55a8e5ca7df1c3bcd4b863cb15
  | 13 => 0xb5b00255a1f23f630b0b4adc848da5e116f7889c28dc0e9bf615ce0af619eb61ed1e906676996a94db6068131d73ff052db8792825a8769a96087b692164df5ff5cc1dc65b6e270b07aecfab899462aec37bd58dbaaed1f4f9bb9308ccfb83e09b4c721ad3ad24615a
  | 14 => 0x6fbc7acda1a3fdaa3d0a74659a816dfc04e05c4730da6e3eadab1362fc7391aabd6f1fd126c181f2f99ff963e49644d47ccbc192f27971b2fb624c575893cf1df70ee54b58c7831f4791800ef44592d4c8e40e0242f9f06dd6cccbc5248450c55db2b38790dc260f40
  | 15 => 0x543b89a3bfa241eda019e361f98b6e0eb6883846d86442335c9b3be538c9af1adfcd194efacef3b80c5046a66584187d0e8362f9ee7e3341736a81c2f053d7961ad927ad890e799b631b381ca8f48936c9604df4dd1fd1a4d521865c579e1235a96208244702d4c73f
  | _ => 0

private def denseT0B28 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2c4588fa33a8d4ca21bbe5cc604768a9c58247480a7de42e70ddc281629eb284092bd3489ceef1f7d65ceaec1d973a5265a47495629415f389681924c7f77dc778e14abc53c084dbc30b3cac798c5565f94d41cc8b44789603c82b6d696f8475ec744e419270c90416
  | 1 => 0xe86f3936f90ca4ccf33508f49361db93defd885c9ce827959eb2812a2456edccb531b1a116690938e6029e9bfbbc53f398bf33d51949072c6516e783d769185264955753d872cb7ce1b26b92291a1885c27e79266611ed63b3dd3cf14081da054ed26b52d45f6d7b62
  | 2 => 0xc2333523820657bc37b3352e0d4c98a0f8a73432600b2526c0c03125486851607f968edeb4e8f378c9dcdd440cad714a20a9dbcc047110fd4071b377b52bb3207016258565caba5231e2610080606b1217ca146f6cbcc48e16528b327e2729a7f19eba23ad9c10310e
  | 3 => 0xfc7faf3f7e3b4f81193cc119c93450bfd66112ed81291b70c7df97a19f518bbbef0e372ccf96f98c28fa3bc2c8e21f297ae7cebf6fe7f653a4de635199a1feea5cbc9d10b9b915dd712899d9937f678129dc849b2b9f9fb576370b8dd921d804bef1ff05074fa540ec
  | 4 => 0x12b07aa68d899744f93456822682c1dd55fb59a6cfe520162d9aa504f36f6afb9d5c9f5e75e1d498dda9af27277c68a1ac6346f9b22f70604a04f05957287ddf9deb330c5ac5f5800a3c011bea641477a8abe99b32ae89e9c5baf1f2b62461bf4c220090605a8c9684
  | 5 => 0xaa32a713c015e7916682db23c08e31c9f6ec22c9a21d963e4391efe42f9ef5294d5076e89aa7f8cd957e1a7438f3428fd77e84a5514872353dd868c00216a646088f3528335d87444d6351dd1984d18693017659d5f6f228fdda9d4a9728f4af248f778dc702fddce9
  | 6 => 0x10d9a2a438d4ad9e4e584a1513653cdb058790c27d0495a51782340acfb450823fbe2a106a708248066ddba7a9559e15e7fccc9769ba5927ed8c5b4f3ae6a8b4464c2e11650cd500057b2d5f21ce016110cbbe7cc45bbc63bfe5b908a85a701c3a1947abcc69af408d
  | 7 => 0x99e23798a6f1fedf2c04d6ce33eee558ef3a4c15441959d93a07ae382693fad33cfa4a3ac3618d4f8e6629be980f0d9c4d74e5dbe1fac76ce5f388017aa9c16bfba2aac3cb84d787c1af6d645f58f1edafa94f9b650e74d17e226c3f7a98b4166d5bfe8f6358e7bd3c
  | 8 => 0x4736bbfea3641e12271617527bd7a8165a6c59c2c0696a7547a7a06a96035588d6e97636772818322679506cd9c6b413c9833703ba9a0d7f98d1f34f291504039ee768fb44658a8e5057435ad050fdf420dacce4cb6b980b08a725c76551dd4650342ca2dd1a72171b
  | 9 => 0x24f33fb734f61e6ba7edffeeb8b945dc77b215d5965f2626abb048b4c85c581004fcd7689a667ce46a6122dd85f397db07da6e1e3b3b10a787aaa1659c27dcca8f5dee3fb3a0ebe81fa9df4b20ce622b9762fda9c1411d5c9cdec4495d492e3a6dbbb3d5fb8ee22324
  | 10 => 0xefe94b6224200ca5adea358f9ef64a2886a663aa8bf2f3dd060f28c8bf7af43b2468ef1491176c8058cc687bf4fcd11484f36d8e751f922a98f298f6ec27156a583e264abba6bc21e6351e621d665aada758a756f1a0ffbb7819492dfcd0124055b2f7d986e0bdf709
  | 11 => 0xe13d1b2a1e6239a2d3809caec61186dc3b15eb447dd14e00c6b90386b95473f5438aaaa9fc73cfadf198ef72a3c5d8aa6a2cc4b0788d4d9fd6517ab05a29200ef15cc781335d60921cecf461b6b0549aeb0c0edd563e1de89a09786e008093ef9d28d3ad50caad59a
  | 12 => 0x7ced123e50c254a582c55bb29e6c4bedeb1c597c3e7ee4c5f7c8c6e1c977e1b8bc95ee039a6ab9d3d234336cf1a26ca70d18cf66c371b4cca68b4b7f856908bb08dc7878bcd9f8148b7dfb47575903cb1359cd1199f1b6ee0b542687457a71d09dd1eaff2b8f0f8ed9
  | 13 => 0x3e0dcceed913cbc3596de061b8af0af671cc5982bad291062b1ebb1db9593ae30fe6202f039d5e46e014ec410e29e61bea7181f64c3c4e336f822aca59840689d9d58f19b27a38fa59b28a161bda81074a0c1338502641f7c5c65120b51addf0d8a37c71a6f59a8d5e
  | 14 => 0xfe9d3cca8eff255b02491e4cfb725bb967c245c559b12c0e656a4ae4b88b0889082ed636b49f12659e2310215b54d90f8cc4b3c41736fad11a0f73c558504b56ca69a35ae7a73bed6bc59d85b43170775d5c34d509bbbe2a58e86059e80fe5d562a5d910efcd51d59d
  | 15 => 0x737111a9ddab92b0c402e2f8fee477e36f9c0a3dae2aa956576f75325531a52c0a2bab4e5397c39ce9ab71e5a90f54872bba7fbb2d4273032cb882b10a62b3b0960353afa0b3eff79a2e7418cec91625e6e8db55fb9af5057b45cc57df97240a4467258cbfc9e71a45
  | _ => 0

private def denseT0B29 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x75720fb6edd67c177ea3002e556cb4f1a08090b5ea1a8a32db34ac04b097392b61aaee82371df837effb505902116d60d063879dc7f46ab6306bbd882bcf9bae1711ac07542d894a69c70a56b84951e1abf302310179dbf2e297d2dd10682a6909c35117808ce6953a
  | 1 => 0x734c1480737e2860e5323b6c0f0d98cd71c7e2d81fffaef78d1b5891d9abc233865e2eea4736c45f387e12b9b1da06ae57dcea5ffa638171fd393a1ca8a98beb2abdd9e959e6a68ec7e76eaa29ae68a86547b68ffbf7c3da082511721ff686a6335fba3786a7e4a94a
  | 2 => 0xaf7b66bd2e40a2813f46b0d6402c034c931e2e05e5c6f1200390097943f8d92ccaac2a14ca4bed1067c67608fb2f47a0ff94b78791f22f3be54135c43adda225614c840522aeaa3f9cbca313e225b4462607064f16a9e0086eb9fd7cfb6483e95dbb29cf1c59962110
  | 3 => 0x3f751948e3696cfa4056970a95e6c2b9bbb851738b412af2396479536bea01cefaeba689a73faea356cfa771c14ec9cca73d4795f38dccb793b7c74a40f6cd2a39cde670678559bbfebff1e5a1f56894c80725fac14913b75af49478adf2197dd741bc2d4154ca2e39
  | 4 => 0xb5765b9a0f55dc28d79499030cf2537643fb720ba654127ace71d7dc89ce720e0eccdd3f9311db9634429946d4add3f92018dadbdf2e1b84d76386719c6ceafa036d8916d92f0d0c62866f09b3330e5f97bb17da557fe8e19b2d18b651b98d1ec81efc5decf9c9b181
  | 5 => 0xca3ef9e7b47c08bda6a76a80f13b540bb53638f3f4416273963f8b583706eb517f6ce8a63f9ab54f5d8fd20d3ca435ee3dbe68c5a223667620b0a666e827fc7b69b10318f8b01cb403e3264b5be166e0451ed142390b2df8f549d3dd21e826647f12050c441d478fd7
  | 6 => 0x24718223f943f263016a1d998b92340ad64d1512caddd70361509be9f1e4441127853e666e34bef2ab03ed0de3c5ddbca862696041e3661106ad427b9788b6d550a87fa314921f237b041e4f0d8ce0ca44098173764094a4f45d87b7a101fdc970823ce4d00be60136
  | 7 => 0xc9a23b5d711f56e68690bd78ad82859be59ec6cbc8468d9b7c07d5d019b6e615cf471c1b29727fd650171135b907dd55635d96186743e57ecbd4472b12caa6978cf0d1fbea8e4238f3d04494367d28013bd7181cd815f94d8de012df4e6b7658157dd0ac289bff476e
  | 8 => 0xd7cb0a310abb8f87c99b91b64cdf1111d9bed1febc8be8efff6f689abe13dc5296e1bd9b4e8165df6b7563d51524702f00f7ae7599bb45195c73dfa6b59e5fdc7f2def63fd1da1195d004da24c3d93098e0720939dd17cca65e0d07a6fe2a91c462772726e6664723
  | 9 => 0x26eecc9ef5071dea0d6b6bc6ea2bd9c6c67d319f8fa2c77d866eeb5eee86f1695790ff53dd12927c48e74044cad90b119a6415f56a32e4973d71201f56a5e3240bc7ea7352fb5298982e107c03469c00beb3774a41dde7fa9284e90be19fbcabcef78d35a9c35c8c09
  | 10 => 0x5d9fad65e85cce1f2de58bf24affb7e7412b10839b28d13e62a0e6202d57175d54669b099bf882fc498805153f3f0ac42844c0d0e580ce74f402daddd23681c0bee55a5d13a1597b4f044def60db7f52cb0fe8c16d13a560dceca17ebdf232ba1d1d2ee432869ef4f3
  | 11 => 0x1135893608cc680143f0593e22057135a438dbfe4c350b97a5cb6c92a84c2923c27ec5f25eba1884432538bd9290f79f34752e2ae99c262036ac806ffa6d6cddcbda133554012f9f180410b1b0910d0a2e22c081f7fd849d37fa61e0afb5b3fb38c9755d65de355d99
  | 12 => 0xeec4f25d8e04b611789d826077dafbe227b88ec383d6313fce034eb37732b136929fa2b7159009a98f81990c73def84e34fca08cc050d3b46869f4925a3af7bd1702d7f9e58401fb9b12e7c9731247c3b423bdbb95ab0973431a333fba5ae22a5479cad14f1b17ff73
  | 13 => 0x5efb23f9d4ff989448cd75794b8f6d1231c3ae8996c179f46a63b9b1f10235496cb2ad2b472d78fbf9d30adf3c8c2a3fc4bdb7f32dd4a546f88224479261d38e42f80d98c036cc9dd61f95620ea8e3ac9f1995107305396121f5ad6f1dfb8ad7710abaff385ef71f7d
  | 14 => 0x6b2678a17743844430ebe35726aa6be505a91f9f7756a4c8061f0e9fe3648357589f27e6aaeabcf03bfcf056412511a5dfd743eb32fe364fdaeb76793a4dcb760569a738c715e6bcf81da75b665f183144e87fbd15b22b059a79fd6e045bfe7e903191031af71e8016
  | 15 => 0x8ff846eb79670603ff9af2762fe7be50a8d791d9b2d2c22001d00303d12e1341bdf2563c4c007fa6b3d50782aa6735ca36ff69c2c8eed07366c54b5aaba694dd9be82c877acf46e115a606e458a26701977f7e7d02007fd24ec4aed2acd28d98013129a29699e0fc60
  | _ => 0

private def denseT0B30 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xb4bf14b464e1f7ce24ae9da3684f3f8a7cac8d30ae1a44813bb0d7aeeaab7bd54947ad06dedc12b238779e43c809a662b36b1732bf9227570c8b727a859de0bf62cbbd4d050d45961b52f04b8a282c4ebaca5b26282eacd7ed39f9c0d7840c49d546acdf1dd5643ace
  | 1 => 0xf7f84ca939f9e5da343276d74663bcc70f319f3d9fa906579e2af1e6a22938b70e011849a172b9ea5af4db2e08520433c0d0287c1606f808d1f81bbc15f33496b3300d3019b7ad2b369e8ad2f6817b7ec099295f47db90181cd371d834957c28b05daf3ad85f43ed46
  | 2 => 0x9e69119ba10378286a25f32e591ba83ef7fb7cbce9ef8385dd2b2a507fc06409b32e5fed782018c0bb8c274b7117ce699252522b94b3922f0418299813b307c54a7f300b03bce36d10e2c4f6daf3c4dbbc0aaf2fe0350903402d4aba59844e787b707eccedfa67f1ea
  | 3 => 0x4c84d68cfc7bf4c5222cbcc6e6c78a04d7ba1b32dcbf863fa278669bb1b6debe28c5f952db077b13aa9be49ef3f0285036c90494a08157d5be266052af2af0752d00bfb52b682615244398512e410417922c09cb3570fc2ead599b20cf40b674e5dcdcf7c39c04e252
  | 4 => 0xa972430c678c07a3c61fe2117623560cab8632b17e48c601c40b8f080e5308bbd8abe1411310ba725260235a785ca7f2dd2d968121dc8b9d7b7dca2f89a28da1ae60deed135406a283e2adfd7a879067e8c2f57bd6256b69f9695c301c31fd8f42f4f5fa97b76c6b29
  | 5 => 0x43d0582cf937f1ebd10c39288f66e0ceac0d317fd7e2738937a4ee62eb752dab04e86ef306d99d93717722fc75ade932687d64488c5c4480a22946fe3abac840b1885c8a21c5e6282f1ea8508a0f7531ccd99e21d0af43b556f0cb095067de8ebacf0c012db8eed100
  | 6 => 0xb3f58858987da47ea2dba243aa7fceb8a11abf36ae1b0b5e38718f31985551831c75d5c9803153ac72eafcb93eaf24c6a09ace6778778dffcb294487c889f155c833ff8f796b1140d47575e84263137bbeb94786b7f24df5b1df7d4fa60ead177649d5877d67671dad
  | 7 => 0x383ccc6736d6a0677d194515373cbfdbeba49ea48c9ee72b15a46466a76eb20aebe8cfed1531256124e5b618f17a716d9bdaade2d91f2b97d396c7a4d61c05d350ab1096e78a8ee4ee74c58ab4a928a2e59971742185ff7d8fa33a84754f22919f09b11dda7bbf9b15
  | 8 => 0xfd6d9a56993a1a9eb82a7836f96819602f9428333f6e62bcb0864b53d2d97fcef6529d5b1f03856c3615e0ee56bf890a617df3aa04e67e5e887111653860d59cbb099ab1b7015f379efeedcf07742e3b4a73cc9c24f3a34bcdcd8261ca2f8e037e52e07ab7448ec41d
  | 9 => 0xd7a082776faa20e689171e971785923341b77d65c11f84f89eb6b1cb114ee976e2a27a38149ff3365810ae29408766e7218953409259f951eaa5f3a9cf4be9968dde5defeca0adec0125a410cda215e7956c4bf0379141271bf06a6efc24fe0cae5c2c6b2f4c2a3abe
  | 10 => 0xc5a94a64e402a9bff128767481ea6dd22a015046578a93c705ed2fe5bfdf9e7f09a81a25d329ed4f6ef44f07314907c0050705d4dd75dad1ff816dd71fecf50056cdf17952dbf99d9237c533932cc276836da4fddeef39cb4d2de44d461529fb0c36b21f225805e92d
  | 11 => 0x983a89a8be37bf79a8e93ab78b858d34933b3d4088f922d26036d2c10e2db665ea6e895199be347f96eab49560712c4f5dbfffb2809413c1ef438fc37baeb353e8d97c87492a53bba70cfa46913440ed1c2d419044fa7eb8a0dac8cccd62b45ed9567456df0efa391b
  | 12 => 0x3e14199af9ae837fe3107093760b9ba10c92afcb66b89d159cab70e345d24d2fb66505723adc9892451d8545d614159ba33029a438427caf501d1e76e040ff6a23d10750317d2f4dff9b3a240ac34a38ce7551cfd2e38dc3966e43d0d3369dc50a7b38261672cf474c
  | 13 => 0x642a1e2fbce7b5b319a5bcad3d82bdcb93529037038f7c75a4455dcabdf35a160f10b8db042725722ca87dd0f96c3a558856cd9905c5504480e94fd11069f7e40e8225198a598d7f4d15abd0c0343fd9fcc4a9f64c4840503a87b0e3cebb0b75d9c53bcc4537a9c0bd
  | 14 => 0xd5dad9b584a23af851222631693b1fb7849f6fc74690e676d5c6a6910323143f6a5366f379cdcf199146c0d1671297bb1e0e70f9e11830707444f8e87df116899c32776fedf3308a70de9fdfef3d23f0a92eae692afe790dc6aa190e3e95abba08e3aad65f5d84f18
  | 15 => 0x5dd888be2e506b5c71a9327156b28b105d2cbe629b0c1575a6e760e9595a83276daeba02fb19e910d2bc5b73da51d58124b899ee0c18f70b5150ab9443c62da26b27aed97478f3946a3cd3cadee765da7d4bb2ff00b2c16dec5e93aa99f0f26825f1401c4c4e4d6177
  | _ => 0

private def denseT0B31 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xdfa6c9a10b69582a177bd144bfd02cc4ad9aa143d6d851b20173ad2c8d5708adc65a5f8da5005263cf103c7634f52e516b307e1d6a7a9c6a7d02a643332e100a723aa1325d0ebbe0575f14f0afe27d0ec899faf2b3955d9a95c435f851436791d11561764c7a27ed20
  | 1 => 0x2b5234bc9b3dc1cbc98d459297ea8d9512398b73d1bb94ea7f0af78147de8aed9c3a24d65db6940d21fb7e626743119866d15d6645fd209a37e378677d6f50fdc9e7581c06356111cf23062f940b44a198c1254adf46a92ae5f3cc393b6faf82069d01e3eb4c109cb9
  | 2 => 0xe520f680645d930ff9f6e36093d74bcb3ea5030bb825b59773886ec39d24fea7929a278da24bcf8043ea38810db1515cf90bfabc26537ae8138c8faa25c3fa768208555a3a7b95cb89cb07dc35a51cb2d3686352ab5c0ad3d49293070c4419f5f9babdd0af6f4913cb
  | 3 => 0x49f49192c9f5430772f40cd4f24782e2585bbedba6bad1f18379babdf4ff1a2fa6b4619b6849e2c162a6cf1fdfdb829b8745676e3e9d560a94317b74ac56bc73d6af47606b64cddb9f04e6a4812f1d52e9595cecda50fff66550edda67177a38d9cda5063ea95a9efb
  | 4 => 0xd439ed77ba98c2a728ca5e3129ce06dc17bdcae236d29781dc3a0f9e4b2c48086558c31d6a2f0137a9eda1c9093e3003ce225c8bccd188f749a66be1ad4a8b1cb6f247f381b5c22b6c2c3ee80b742ac8a90d85036eacaf70d050b873dcbcdeb02c2fc6d2c90f33a7b0
  | 5 => 0x79214d1d14ffffd9a68b5e9382d12d08a394d324b59743524d67b1348584de0545cd527e27a1ccd9fe0e00e7bc97bb10ecacdd6f074b3ac8b072519edf163a6daf55eb4e110446334cf03707061c9be6b8cd09f392e67eedef61bf60240bef55853e78bdf94b58839c
  | 6 => 0x4ea30b45799029a9c13ccd8db1facbc10c0ee119f5982e642684ce4ddb8d0b5dc3d477523d9e65776f04c3b580e17296c433837331b84a5fded39af1bef25ccec008a35b916b11be5e0b0626c370763a2cdd0b67f49fdb53ef9d299fa9dbbe6f31921040dba0443f
  | 7 => 0x669ded8537b5a85907a948a1a98cbbadec6731333f23289bb6a936229b200fdd37ad6b5f86eef83e2adcadb703bdac45cc6c558df6b06708caf934b4120ffa653d5c9c4677b3932393c3157164cc07b14577d42dce28d55aa3ddb6d32856a55567e3e8df22847638f9
  | 8 => 0xbb62f1a3c6a5b72001dc3e8c44715ebde09e6b096823c881a45d178720cb3be1d84eeb06fbf408d28c4e9585584296b1f34c20b07a65218b4314dab22a358e8a8d2b613757cbcc647a78c1a034a09b4fdcfac038b842071fef9e02af1e47e439c86e60b09231dfdedb
  | 9 => 0x326dd722f7160fd58445d364d4bf927337d04031ba4d846378a36cb0183459a429b4d45311d0db435c55323300a0bfdf1bda344bca3c5365cb524f0514baf98bb7e5f2c86cda64324ce86a1c2e2586784dc0b0564c82db781a29a3c7cdcc660a4c21bd636c192372e4
  | 10 => 0xf4f11a76d82474bc0af51b9c9ddbe9f3a7f9dc79a2b60934da64c5492e67eb59db4e2a64c1f23281cdf81a426476a5b65bda28883f6d5d3db841fe3c0b771b254c976c59f34bc625901f71606e2f42d4f54f76e80340e767c1a44a0c393a3a79af41544c93cf443e30
  | 11 => 0x64c956c9d55bd46d7f11a4f25f00f10f9678f7ccc125df197293d93f9c9e620a0684f06410406195e1f5bab12d9a93d2614f3c3b4b187c21aea30550c22356d39a08d79337d6ed68e6f1b952941b7114f1617b5fcfbf33f35243fe190a6352b2dcbb342dc2dd8b27ed
  | 12 => 0x908788326f859de247964ade5241f7bc50ec339037455936aa1853d7e2f41245142de235ce54251cc4c141483df4ee7e47fd978c58611114706f7d09d4d416812565b32f27e7e20d0a0acc184bb53510f88b72848d9eeee3c1981097bb10156348f882c5515229009
  | 13 => 0xc74b1822cbaacbf2cfff47af30ae417c06148dc956f6c5227cb8c4b50975185637c1207c6ea8be233eb22ee047609376d7658defa2fefb3fc25e7234fa21292a11aed81b67a9ba570edf37ccb9c3d4da4c5174ff17d12cba5d5cf5cc50680ec980f93ddba3d1cc3e5e
  | 14 => 0xe1bfb1855f287881385fce417efc95dfaa955d59d8113a7233c8025ec70557792e68ea9915d920620058499a0a0f2eb5c831eb2f3f9045b6e5516cb0586a1f5829b3107e9b3827f5b9265d3bb4868da381d9865960767e66433b6f276fed9f1835e01158bcc3475ef6
  | 15 => 0x7017dfa37062ad560f077aa380f50035bdab1b1add9db475166673d62293e95520247b51418b7c05b6af9a8507ef4950627061528d93175c990a8465eb3934b50d21c82736dd2a8f63e173ab28cbb9e7dfd8c5187dbc7fec5b335d86e300f9771775eb25f7b3c532c2
  | _ => 0

private def denseT0B32 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x78c22aa0d58cbf25cefb13e0a7ed0b446fe545c19e1fb9b317e245e62755c48522a365046f0cd3fa5d680e4b4721858f96bbc12950e52cdb17a92ebb5395d55aab5fdd45a6c9d5a370f431de81fa2b7e713ff61d75f1437622589e6ffa2514732f96733230655764a9
  | 1 => 0xaec6147c69bac48623e76105dcf2fa7d4f5a5dc437c45de029dc0315d6c293d3d321c2b8cb23121cf37cb5030ad2f5aac0d9bfdc44de633bd16871d2d138fe0ec6357a06cbaf636987791ef630f3677a86a5339640c4946238a45f391779b178a5bc83c89d64bb3c55
  | 2 => 0x59a5d3d7e4e15f213b1184774c5a931a6ce36c41e97924c2c4255b02c0b10f5ce7a6d66842f5f41ebc2e15270e9df86b75a0a7324c438fd85dcf503ea613774887470c7ab4b1aca08eb4c06519ae75e0b0dc6465417afcfcddd215c5042cb754181a4377ea9cf50f51
  | 3 => 0xcfb15c62af77aa48778bd6737200e2a2394b3dfab4d39527557fb8fceef84b8f467f8e6ed664f2622ba39b61075754e8fb5d5da967fd867f5a018d4e3f58a323be2fcbe6e817e75607d4b93abf2882e47dd0ad6e1890389a323b60c65a8c06ef278590a1facaea602d
  | 4 => 0xb1d227b3ac086544f0c85913d34c210f4bca504d975d3c5d1158f8029e8e9de5fcb34a9ad9ee611ede051dd35b00efd540cc0f907774dfb6655a7014aa86c8844e6bc0d68978890317ea7f07ca920a92ad2ea7f34316149cceb741429483725cf680dc073784bf3672
  | 5 => 0xe79687056040a750e534e8cf43c7a6d809898e50df28acd8a1259c501609a0511c3571020fcb49aae04513bb70e64144ce9284e63d77e5295bebadaa2715fb8310438bf881d249bdadd3afcdc596c675c6e7dcf99c25e684e06483002c91aa2f2373a8925bf66ea179
  | 6 => 0x255c4f18fcefbf6675b272e758e6b4e1188ea7166beedf341db70d3016fe60db562d59915288d0a5f8cd107b27a7b0d8f03361bc7e8521396fa44ad4e07b193f80e19bcc1458d31af1dcfc79831ef3c6d9ad303097a295ffacd82068822752128f61e18c746aef1599
  | 7 => 0xc5f44907cd9f9199e92363668b39124df125af14b940a60528e5a5225724b50057c2ce83f2c6beedf28908f1aa362d5b1ca26548a5490898d80fa721c6dea0a8861e8ef5ff986804813cb8b17fa5f2420feb1bc4e39501a6262e8f929aa0d313392db08d820ed2e040
  | 8 => 0xe81c180cbc29e7361fd79311a96640602ea6e0a555d53b38344ae537dabe9ab1e097d5334e6cb6559d11f69fd5624771258c57a88296dcdba6851006c24bb391815eb4222c5d81261cbb6809b3928c2dbbe6e7b2c7a26b46d5ef3171759d8dd0b43d12ff7a6907bcae
  | 9 => 0xe12da347e28be537407e05ec9a648fa262c53b2cd35f5792b3d501e7219f646555508fd329f93adb5734ec1e9ad25d58bc198f3108ed48c4fa5950530345151ee6e405359b1faf41ca6765dfd71213f1455953007492d8e23e843e9b6b24de427fe5586a121aac143f
  | 10 => 0x163f0371e0a989bd632195bf4a7e6e1876c76f08225f355df066c9dc44177fb56ff201d4fbd31d6bb61b55431b575a284fb6d7d2ce6a754ad41f963eae819aa4571928d3e72ee3fc1ea128c595e9bd179f2d04b8e05540debe4706b67b163f4372d3bd5258567bcdf6
  | 11 => 0x536b8fd32c041e25d2ff01d1ec51d691afee24f6eed9ce854d74638ebdb8629c3e334c0b0bf66fcf252b9d34f56750a2be8aab2b4b05028cf6df92bf1107d9cf8c493fb81a7cdb710a45fbb1b3c32c2ec8186162eb875ef87c0a68c3143c26b53f309feecd238e2023
  | 12 => 0x1aabc74bb4bbf99ef9a19e253944dfffff5f0626dca67d49838e2f0e4438f415d9b8ad68769f92f77dd872214c65875c0e4544960348f12329813f430863cb05c4512dd39af2edee234630ee4a58812454536d5deef3cb67396cb9732c255e1b86ef9a37d8db788fa6
  | 13 => 0xacfc9ad2b421e23c653083db0c5c673f0136e6fba6fc2f6affc5cd723cf6442fd9a464f9711ac3c1a3062b5b760b84d67f6e33d6daac4d4a6d2d8ee27bb38940366dd9a4f5a1d8a1288de4e20fc202310fa3c08a01f7b3ff3f75a2091b9e9dadf4d1cbe26e5804b0af
  | 14 => 0x5008f5e893cb90aaa73558f934640d9e00e632cb9605700251b999cf341133ba9c8d2bb8bca6014d6690577c85986d63c3baf127d86a680bde268e267b43ba67e3711c583048ec55a236b08e75b2b395fe9eda3785dc49da8e9720a0b9a3298ede5c4142b74de27796
  | 15 => 0xe19fe55102131714fe91121fc2c962979bae18102a1a889749ded7eef716d0cf1c609716180aa263baf212db991432464af1d9d82dece141c7f0977cd2714a93f553a25696f7446b509858c1fb87e7a339e032d3a01f75b19e788a74521688d5885de0c03012640433
  | _ => 0

private def denseT0B33 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x664d6d0ac64022c41a0c24d96041f0eb26008a5aa9ed48bcaceed0e011547511c6d3dc05cba9c30c3eb26e73e176c8c0c90fba09bc814cdcfc13c365b101fcf8aed9d66592618f5149625c0ff299d1686a121d4929631cb0c8577ffd0ccbc1bb74c1132ea6b0474aec
  | 1 => 0x8ca0030074762d024388befed13f15fc7c6092025d19347a4777ecedd7bf3fe3cb4360e3ace4ffb1a960adb585bb89d567faa2b1d85a5304457944e1979721b183d479198c3b317186e678c588d79c87a9f9a506ed4877b7b2e558d12386d928b7d3ebce04c4e476a7
  | 2 => 0xd39f1fc6d79248651c654ae1ce2a097b3b9353e0a7011dc314d615b88f38ca4f88091fdbb64621197806ed8dbb73a08068d65fa6828ce584802ee778740c33890dea7a8f7763886917bac82ea66d2a789f5045f2a7b66b71ebb7fb5a9b54fdfb45c26202de3e567aa2
  | 3 => 0x89b09b092055c6c149e684b1d77e29d98070c5e957fcacd2f13f676ba19efdfcf9304d08615a7cd79d48f86c12709895e13696509944d595a725baab3cc891daf413074be327f828a3f490f03d4846412bd8f3f54f6a34a6de23cc30e57d526225630900003a7c56cb
  | 4 => 0xbfba844db05d7b60cfb4ce522c8c66a092ceb782a4fb8dd02dff9fc357dae2ba82fb7689cc473939390ad6ce8cf86a092399484de313da356cfc10c2578649118b627ec51354ded608c4f021f5a85cf7de5038bbe0baa988a4bddd450b391c2964b79408d583a21249
  | 5 => 0xa623d40db7435a79960567498eb0d26ab4e899f4e94bc869ee891b35b6dc21d6e792b86808e3ab38ccaebeacf528674e115fe17e676a38ce14e153aafc839735923fea227395a53225c32ad97bb3b440405a999390cb51688396ee3d92b192ab2ef6f8f4c42cef2dbe
  | 6 => 0xd9cd34a2aa3e495d6b318ecc9259db3e820f4bb61531d24039c2e0c9be2ca1e9c8213fe841363b03354400cff8d8d8f743b5823eb1b5879aec20d5f7be37781e89a55acb3e554fbf25701ef18e56c96cfd171719196532161dc7b45a7872b2d942538a7d0c1aca4612
  | 7 => 0x909e212422211ce94d046c6aa9deeca23181815ec989c2d7dec5d5ccbc650a31702e30458b44574e1f89d6f90bb27c42ea69a034967698390ad5ee042f493017c8f567a27a2403f8e8bf5c086ef7e74839f525c84db39750f0fa5a0918487cc0233ba986d8736e7257
  | 8 => 0xac412e2091ff8a0886c7d86a342dea025bbd476837dc18165ffbee63ac45b34efea9fd93c07fd5ebde9f19de4c133caba14871f5bef17446a0a1e97e3f51fd5ddf27e9288e7a13a18faa35b83a1418bf93533b4bf0598c9dddc54677f8c8ae0158a160ec1f031e39fd
  | 9 => 0xc64f036ed2761b70a2c8540287b881dab5054f3b49e312d2fdf1eaee60f82ff86c8f5943e8900c10c9de354b5d399522a87180d9c1f2a45ae9b49728a1b450d7196a2b5b7f4c71c3e4e0d0dc273a0e20605fbf61186f0711677023e9ff344cf926024887583fa8453b
  | 10 => 0x71f10d6fc2b5ced2d52ab8c7002e5e4d05c58677bafafe2092a39904b6a084c59d9e6d5bf31a7798c2a79d71414a46084d90b47240504af72ef208ae1b0f1065ca3fba90d063de8104da50e3bf65f42f2b6f5262f391aec49d789608084d036be30365ff16a5904ba
  | 11 => 0x6be8c8649ee3043ac8d5b4de560bb2a69b1d6e9d0d8a950f59c9e0369f926338d2dbdbe6d6c96cb8677129a1200df4605960afa3ed35237cc5092cd793c2947b81a22c5126ad2fcbdbfaa36c4dcaa5d6a1613079eabf6ce21e0bef87985319c940879441072907dff3
  | 12 => 0x369a6ee55a2f25a947f3620904128f655f59ebac541d30c331686dd79d4fc4a7270abdaaea539d67ad213dec4f684412052932647583a8639c0fe8683a9f2cf87b6483d971fc775a3ca1c082bcacff382c58fef80d932becea9e5a6eb17f80c40bdeb0db16586637e0
  | 13 => 0xe57c8b4c1c26ca1330bc469809e292c0052818c68f92e63fbbef53813fd6d5b49721b2897e302e7dcada491b6d527791627f51b62743227ce05f4f4175c4e06a88c31a729e16b99e15ae787abbd8814f89ed927bcea39b0e59e481249d6a868962cc01126a656b008a
  | 14 => 0x89396cfd11d3a0bb55cbe1de10e1cee439902ac49117457e514027b0e8f2c7d3b0dadb7dca4e51221c878a06cac218d3b2e7193e60fc6f425889fd2e9c946f2f5d809d46e5b8cb11d7203d85916a5e257c89be3b0c9866fb3a7b59c4e1c1b830af071ad0a7cd808596
  | 15 => 0x58c9ed6afd8e91d9fee3180ea3b1fdffcc580f5ae0af07d1bd3b415a8d5124fd07202ce74b7160c316f5ef3a925db4a8c958c9ef9733411b724f6f04e7116ecf5b0a89211da43e992313183c20eb64b802f581a6d2098e88e0cff518cf8ca9f2bc6af91fcc464cbb33
  | _ => 0

private def denseT0B34 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x38855164052fc640c4f010a3ebc747ec5bc3974614634e5ab661b182c7ebdfc14f2add160fe7825a1082dd12190882abe3e0a7d2c5387785a90157fb04306143cf2d0d38436b5e72dd550eab2371d3aa040bf201713a81dfb734c5576ff97fc70bc36dff112e4062a1
  | 1 => 0x305939b6f8bccc5a87f0921604062497fe138b057575cebb3cbd1c4b534ab4d55b1f935af03e1c6ca1d37265f1b415715aa61093d90cde0510c4a7e13a468bb56afd83354f4eb1f8d818b1494597b9809b0ba0c17bf3bfaf53a578cff4e48d2e0eba7ca7856f497a1d
  | 2 => 0x8bc9c36b380990b6842e1ddef3439e7c08fe8439f89c3e3285d952f016e2a7730557f053de3586e1ac52c8b78f6afa0c324a8fa3d3666ab76ddd033ef52b9d09870fe85736e93d88c6d8ca394d437a601306d1c8165bb668b73791a5a923a1808377b3460529efadb1
  | 3 => 0x8b9f140d7ef6f5af301b010226bcb12cc4e0cabf24d1684ba5b93d3043f4152b8d30cc334dfce6796f145a5352c7963991a640f478d9afec9fd447e8044219b3e3a0279edf10e13ff1906b140b8c45081a944742eba4825665a97569eebf43fb70ad27c62d5237012c
  | 4 => 0x6a955e01fae791204054754b1cdf9fcdb0f61cc0c8437223688954049d0048633e9b3aa0a3f4b45a149c4cf51469d05a12f0df4cebade819b8b96ecb3d1f435454a73241c5b6354df98b020ab35e10ca1bb57b63f9c0a22fb6fd9ccd9ce009865557433e72108c22b6
  | 5 => 0x5b03024045fcfc475e543d121e77fbfd9163f6627dba3c2b8ceffdde54b4b8a75cb06b4a941b3fc59bed343975ab9323f57ad914c20f37f8df46234a34d21acfca33ad4a9f7d9f7ce968c4c97b71b57f1278217e4a39f5615edebdb84a4feb99549a52662a53e3a4f9
  | 6 => 0x281bb14c0adef3eec10e96aa5a92e60fc13da4e530bbf96430c3c5eff9da9b8edf219cd1fb5cde13c9b1282738541cb652a89894937ae3cbe17bb9dd9e7c284fc68501324d65aaa95ee94b947279353c86183ab082db35e0256232dea218fc78839a963db348fb75be
  | 7 => 0xd41e8ed5a796ad6a13541c6ebaeb83957ead1e72f48a5368058ce7e4320807d6e01ebd728ca51108abb234c604eac561c2108a8c17101a773d9499b4f44361f747bf03a496a57f1c2065711ba832c5812eff2b3338dcc00e6d6e0827479f2033dc696b8dd7a2b60922
  | 8 => 0x9b5a82f580f5d5539c861ceb6e9ae7271294354f4c09e7abc5d9a1336ead15979e93d25acb70471c3589dde150ef6d088c4e5bc10d7708b3b877d37847859f50c90b7b37f89f3581211a7fa15a71c5a5278aae5664cdee0e84d0fd46a01c723e64dc38d77e8b2c3c43
  | 9 => 0x7994623afce9f6232c566a62239e1018355c1d78e9920d9324cec30a72bea64b49c777ed6923485ade0b21663a7093a72e743a2e62114b2d8adbd2e89c415736170d4656d5cfee9e74632fdb414612e157295b05fea88fc8e86edf36cff99dc6a46b5fe7d8d9f8684f
  | 10 => 0x3f185088276a0a213b16f0f4cebff339a96076e42bbb28aee2e93e6eef63fc54663b45b3c4a0b35780d5c2d4ca68c09ebc92891ce444905423e7f37a9c478367a12e46e99dd802c52b430f795a9c136d6ee5429c3770277ed7811812850e06ef53496e3f31a2625482
  | 11 => 0x1791eb5360f0fadc4a31b0420a5141a4c788af0b3a46bebfa5117b247e4792744b16e6ae75e29c0220d042c1ef20df41797905e896f040df1424e7df08c0d29afc3d565ef77347818d117d959cbe35b826829021f7400333f5adc14f191e0879689a7cac7adce3087a
  | 12 => 0xfca12fefcac86f7e1be0adffabe112bd5321d33fc00454db70cff0c5445ae24d8f493c87245f152e4d881ec49dc253b93239f120c94cae938d1af900fa676d5372e1b6eb4c42c814df91e00e192cb379caf448910b037d9d5633db95d7e937b30f296f0c83060c6459
  | 13 => 0xd02800bad91133896bb8ba260a203c31da16999283b2285a502c438bb0ef37fadb3a62bb4d712bbc8afc98a97f010ec72215e3cb47655eb0bc01645a368219d7bdec59fb40832b965165b4b4dda150fd9d97d8f49da8532e27a5a99300d3f63ae9986fedc4a9a9311
  | 14 => 0xf58f9875e8af90fec267f24fb6048eafc6df3b33cbbf4d01cd6f1d9bc9a081e43b8a169a4b9c53e6a65c326d4eddf9993a925471548274d99e144c273cd04373d9fe89ea93715e01686fa250842455aef2d2c4571f9ba2480ccf345b49a6413a00a2936ab57dd81b9b
  | 15 => 0x77ed7aedbe72231472bdfc617396334f73f9d9f58d31a8ba8ead5aa1d88c34ded0affdd89a0343972bfaa641139ee7900d064f776e19dbea0443c4222385291d5c8708518e3b55bd64e94505eb98c66eab32169f805cf531a2d9bfe399e0bae16c3a397494eac41664
  | _ => 0

private def denseT0B35 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x8734422b5f2f06985b54f6f7f42ae59b177853d45b2666b6a1e924d3f3f2011fd399b926c4eff951507e6221fc82eae4fd09f31f5e2fc56608387f18b1ec8092830690be3cc758f7ab91b6d84e15f3bd4f9ba4610842ad70e59b915d2dfff675826fdcca858e80abf5
  | 1 => 0xaf5c72768212befaf7218319dab11b3a2481144ff8d76b9572498618c3b694c9858747f305effabaf95e5d2c4a1e0f1d471bcfaa872bd0c1546cf85e3c6833f4b9aade26f8bfe40910c7e61bc11604147ae9e20cfbb361afe0af413c2491e4c9d5687ff0279ac8596c
  | 2 => 0x399726833c8aec5ad2cf9d7c85db1ea4bf7eb4bfc444cee980f7c8b71348ba2637e27f9366472afd28a512a34aa3af24e1608d4d24d8821edb676fedde93a64b9032d74f0d1992b590b37b91e7fdb5ac3ed3ddcea162093a1b388565db2990b0c227b6d3bfe7df7577
  | 3 => 0x7f0953ba5e2f9962571e065072fe1b563fdd7cc522e069661bda1c39662b7e872f4895cb24b64ed5f8113a1fb5db521a4a3ff6f7b81e4aef33283533560112d80d5a76efefd2175eceb4635a4de55c54183cbf5dc9da2c3701bc8be7e5938a55febb5998e963867acd
  | 4 => 0x762cbef172729eda663806706d832928d2919693626f5c48e3b601673c7a2402cff450d9c9cbf7cf4e083a09b9b820b8c89b2c8c2684a1e566e61f676c9dafc38cb9d68ee78601e5db8f54c21dd311721dfaa24cb8033e4926441339cc5af1a4f3efd14d034ac84bde
  | 5 => 0x1729fb513531d8a5f438eda0254e06946cb199808b32fae641a8f58fdc215b5b6d0126f2f6e58eaecfaf4d667f2f8fcfec75c2d5a17100a524e7ab5a7f1dd976de24df33a76e5bf2ea07dee98057e0366714a527c599686b014a881eec014fd8c78c1f373632911515
  | 6 => 0x7dd5053a8895b1bb6964ddb3cf95ceae4e86ad0dc7d57bd6f2616d2daa41dc31fd158d8949ca912f5dbe334767fdbeafb5ea51b5e843913274805b18cfbf1753374acf0dd7fca0b046e155457fe3842d04a3ca521b7adf52a88804846e2135774dcaffa42ba536d421
  | 7 => 0x663bc905d42d06b316621fccb609efea143e9cede2accbb3883bdad996985bd1507031dfa2bdc720d9c193d8a376889a87d3f4f950d116cc088d32b11756b403cca69621ef6c7e9c8dbac36217cbee198e2130597f796037eba9066f59a23e19aea0d6bab282e49ecf
  | 8 => 0x308323686afd83736d5d5ebd0f32b9de3c8577770d78c717f7ec7d5b8678e4929cd5987e84366c530a0b394ab011042fda3fa987c25be3096ad66c4469610053fdf82cadfc5eeeb70c59b2555fc3173a0744f48f2c0280e1bad5166ccd5e6fdc25cec58c17a6d0214d
  | 9 => 0x7d894d8e97f12b3f41f38287e30943d1be3cbc27b2182e2c586440ca6bd06e1cec7d371c84632c9bc9185ac4737fb88f870b322e60753336bbbe87443245f83fbae08df11ade411a66f9baf6ad38d07fb21f7b606c0f6ec5c2199b78b0e1be384b28f5e6aaee5bac53
  | 10 => 0x25851438249ba5759d234d9c72f2ed757b223e9fddd17722b89eb3ff92520f4ee25cd030f59b0d159a1b302130888ca54e5fdccffc0c77bf47b1be787304ad6a5dd810d9f55449f36b92695e57abc6480a13badc31fe3ce1ed412690fc3dbe5596b980c3deaf36b495
  | 11 => 0x43ff370cfe5b2c1223792a4667ae9f189df14e42a3b5de3703e4db5e55ae3bd9ae641d476d3c4c18a714008cb5d340cfae72327534cae9f640179959e5c2a44e31b483afcc6a03323268bb142e5db79e1228b45aad1930d69468d1a9abe96a3b8f64ab620ff1d11058
  | 12 => 0x4c74912e2b16cf2c577ef8b3413cf9ccbb043b2d9c00681e915b7fdfad96a8ae9d532541a04bc856118069b060da1b5b2644f0eac2d5d6bc81fafcaabaed99d0494bd09caeda4b590cbd8269b7be5def4d3a275ae9cac31e7c8e812188e7ed60859a7d79fb60b3c89
  | 13 => 0x7393607964f5d2ba88d46b49f50459f53f4f0dca01106e96ebe15cc374976ffae577754bb6ee07741e977e2f45a659ffb841d4eec778cd1fb9f59221f80652c297441a339b24334919f9338f04b795410e2995d5756e450c39d0803b0c240a7c37b3cd30814f5b7a55
  | 14 => 0xfc64f109efd0270b321cae5b813427fc879dfc3d70afee3d206e5bb7c8f07ef99a1d6f14a4bcfa0aea93c63e15fd4a5942d03291cd0990aa6512c71b4f8caf93337aa060c059dcad56d84e8bec8d7ab523030785d2cbeb66816ffadb8174e8a92e0d568845751a979b
  | 15 => 0xa45e77d491370826341afe37949282ab3fbae2cc4589140e6328e62ee3743b7fb22071eb0293854e77d34b646b876e734a6eb09f1f87610a8f6f8f1544a498af34e110b0b2ac04750cddc2de03207a2bae4389d08adaf0ce4342f27b5c80cae943b36bc84c335bc586
  | _ => 0

private def denseT0B36 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xe4f0427f31acd4ad6453f820d328a0b799088a1e56dff155a40822a2ecfe6bc3d309cea0483e176d62d0d400e4f6a6c28ef72766312ea0b70845fb590c9ae8866225993e525c3512ed3c2742e3cf6b554d5f6c00cb6295932e6e8b4e80c6e893e3f329381e7c9e1c50
  | 1 => 0xdd3463e0a1e27d4afacd7a456a88ed6ce82fd19daac4506c4b8e76aeae531a2f00473ab088ab7517f9c1b7199a846202f66f4235e993e93223d42bd866b59c53ce699c9b4cf74d212a5e5d71b91871061b483207fd20c1e77e05b383b54f3f5606715a4c257dbe0f7e
  | 2 => 0x12f555176cd16808b122855e7899c58b2ae6cac4b1b379ab9251b03771578821259bc853316da1aded3b63728de7e47d53c19c0772808158819ef2aaac150fc02eab9bee9dde9c5fa4d502231e7c3e7c7c64e9d5eebd445e5991daeedb8a8136e07b8500e1c22e6645
  | 3 => 0xdc3dd6d4fc67ccaf431c7f33084c58339af68eebb1f0886155105918a0bb484aaac5b42ae3e9456f32b2f7f6276a3cd8e3a86faffa583ec60ae7ccbba2dafaf357cfd92fc134c8e2de410be4704d7e798a6a9652f53567750e8d21a425fff60b01447b1671d63ef135
  | 4 => 0xd468bfdaa96ac3d8fb7b3fb820643abe6e18a76f950074d5951608704d1d98012109b0ecfa14caee2d6922428b58e3aa10583c1e990bc045fc0694a567c754aa57e88f501666aef2439bdb77c09172f1d3f4c3d4f8572585e4bcc0e6cd9798944584aa62f301d84a4c
  | 5 => 0xa700c624ae17d170981bb1eafd5f9aca9d3e71ff07f4f499ae1861c34cb3cd60185be54f339179439f59a773de2dad1366458d9ce4c259cae1d6c791ea3850eef4b48f34d53ba4030e27ce34a45a23c394eab7f4c643a9358db15f440adb46f1ae0dba36c5668dab25
  | 6 => 0x3cfccb9ecdfc24e8a66c1b1315b956ec84a6ac12e2658eca79e04438e61ac307a9727bc62934bd2cd00705d4b1d1adb1c0ec56bf19dc0c7a9738c17e929f44a3d6bdcf0635b2f1103000dac4d57ae19bb786715083fbc952dec2a93a45d6c2ee71fbb1dcf8a6db7386
  | 7 => 0x34e942e30074552049bf4719585fa2b49c5512d8ef92bc9a3e2e7917d0df7ab3aefdb708f1c961c4a534c38b5fa453f80cc018b99c8b6d82768beb56bb32a4c4b802d5219015ed448d8191d6b6e58b5d98e45bb8651a1123fd01ee6d03b32274ccd7fd2ccd167277d4
  | 8 => 0x8c79fe4a565a5b5ad09e18adae02c7ffec3842ab28cef44b0abd07d68bf2ad5af075a92eb99a7477f377536f7d14880ab2cf11549261cbb96a68913ded74e9e8aa65a774b850f0d2c3467c1231bab432b76249ff4d4df9d0b4df0fc8b705903343c3bb07d5720925dc
  | 9 => 0x42a9ba76afc7632e1ee1e4142259a5472de06150dd4ab1b97c0e7cfc5cebcc9ec5253f2e5690a4811a8d00a2181c9f61df584b2684b485bab024facb7dee09af5157a6f0b83b263afa6aafc9ca055fadd9db9741ed79a9adda61022284beb8da675f16bd6a1ca315a3
  | 10 => 0x25740682cf2139a1764f4087896955638ab0c0f784e3f9069d710560c40a6ee01f8819b5837ebfb8e977a3b93c8f9247b7653492677d37a15a936dbe155bfa9756bbf0c2ef2086573241a9f1cff2c2b6863e80530b599ecf9b907ac11bde4640aaf74407c44d46c010
  | 11 => 0x20bae31e26367e886d00763df9a77d9c73409835192c244712f01e9393d9e1f221f22a78f9054b1c11b3745c4be381f309debb86f3f44e6444010dc68c3e02399a7ee7b80b9a7370b661f9d6eb4396f9d8124785d33dba2a8db98415b9dba43daf40d722bbb62d50f5
  | 12 => 0x2281e170bb0a3b1b10744a30ae6d8e123b94a2e948e0b8019d658bf8d5a9fec6049d1521583f8385909ca1899c238b3b29bd76961cf8ae379d4ab35975be66b98648f3b109745815f42aa0372767c49b8482e73e351324d14df12012303848b97648e1bb8e8cccf793
  | 13 => 0xdaa27b2b0018c51477f695e12735529b8d4855b4f7cba4917eca5830d07e5d4217cc7778bcd0313ef7fc3b9c152e4dd911f0a1e0147453c09847b0589ed83efffabae3c392b064cf63d8bdc616734ef9f9b981e087597dc47fde11ea4fdedb7d563475b5882a1d6977
  | 14 => 0xcbda81f311f6b21ce6f58460f693de7929a4d66bcd24552aea7fadc086ff6bb089e4ec1d0b0ea5b2679deb31a8d68becfc7990c95fe316eb35a83e766c87aeb2e84b32967af144f721db5ed2ab544a9bc58ff60ed85efca17a189c342c275fafc5c4e33652e42e36c4
  | 15 => 0xdffa827b3ee912825922206b35a43967051cb825474bbf60f9f5bfa1d48143a8d3abf2fe0e43a637ef11349263d59e160324036c0d1bd3103035975a8968bc2e086d655b301c600f2382b34467cf43a111ef1d86c25e471450f7c2dc2bef526060e2cbc776584a5381
  | _ => 0

private def denseT0B37 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1eeda263ebc0bbca898af6437f35805a2bdf4b1cc8ad547f60e7b9c55a322f1ccebf2f2d7bf624c87fb62799d6f8836f9a3ecf56a91c3c5b54da4dcab527681c3d9760c37241f58c1cd098528457a64bd0c1f442be81a25725eced24426b6c95e5e52c2d31f979e6fe
  | 1 => 0x94997b2929e4ed1038a112bc903ee4bd2f6b4c5c87cd00585db167feeb9046912631722417dc6dc0164b4af0f5ba2dddce3b9bd1c50bcfe0ee23bb878d47043e2b1206ed08ac027061a749bdb38c4beff681bc2459b9aecf597f10ffd774f890a91046929c6d712819
  | 2 => 0xa3d30676a78ce0b83bbbafcdc46eb9e638bf21d2d4b0082e691b4567ff1644ba599652e8fd482941cf78d4cfa43312ebc9977aadfcdcd05f1f04ca3950ab70b80670d92afbc5876ed010eb0198839c333bb535b9e83ae4a11ef90f3cea47a2f5ebff6a1f75ae93e5d0
  | 3 => 0x32073fe1a616601f752e540ba8161badaa2c017367b069896c1a1dd5ead1101d079c023588c7c9018fe25d035eb3dc5321ffc87a80aa3ae5fd9b08f68c0f00537ad016f043732c140d9e6f8d641120ff3be58d0c586a37c162fc2e27cc448db7b0f259eb71183b4b85
  | 4 => 0x5d4a7814edc588ef3557c3f25208197ddedf309321b4a65d1f478e3971c0e9f56e3cfa6214f718379b17215b4e11414f04837addea90a4e538c5805f5be41ae7b9bc3013ca7ed2bc102cffa9f12336a21cd5c5e59eef73d74448b88d572b09b0a86b9f04e5030b7bff
  | 5 => 0xb5599853a71452b4c3abb03f68210365f44a833bee1c3e3e601c8850581401549d98104ad67eaaf015e725fcb045ca4620f4463058cdbfea37a6f62e07782d14eaf8cb678fccab89ba3b2978b22c75fbe6419bd3f6fd4c2f26714e05bba4b48c98d9b040e19a03361b
  | 6 => 0xdcde1c9c20354817fc9c45b39b9cfdf2c017eb1051b89d8258710c7b4aae35783901b46d297b3e2f533dafbba820adf84f46da60415581e8d2b7d13b6841a13734625706d81698199eecf16cb9e3d378d311248898f724303cf396d14dc378a3f7914b50a2f2198b6
  | 7 => 0x1ffe66ffc72a2d8287c96217306a36d48cff9129281571b80eb5ebada5e2f18ed422d5f57eef7911a911e83f0a02c1354c9e84cca25d4442ca41bebf46556bce952a6514f7f91ebce7d5f12a9dd9a59f735729385ccec0caaf82cbd61df4c679a0fec7e5aaa6e50a9d
  | 8 => 0xc88f734e33e9aab8824e348e1fbb5f1dc355640cc3f0d77fa0361e1363b2d616a946342cb346aba7cd0338b3e85276f36200f4b7fc6a3ee17393af0b9bcaf8beca5a656f1c57575cd4745e91ea415e1f5aa274a9b316651c0120e3de0a8adbf7a0651ba48505da0cf2
  | 9 => 0xcdff862affd76c4afd827c59aee796d8a2d6d6a1b093a94dee655837a0975da32d4fdbac926d32218e49d3397db9fac1e75b0d6b63d4c72f607f15a75b47073c1ec97cefd63f7da9f2d3e8a2c04e0d983aa9385d93399d97db35b172f5a6e5aa99afacbd1acbf1bd09
  | 10 => 0x434cf8f37bd1a750845f2eaa11ec61bc45798acaa4144f531b244f076b12546ef874afb9663b15a8fa607a42b3a6759b22b115e7cdf1bf2cd812f96fafbd3792604c32d8000f706707ec514e3131177477a2ec715166d32be80da3bbc870e753df9052544e11ee0e7
  | 11 => 0x23c66096939d246fb2f36e01c04a6c9113028f17a55e0bb61e25ccceee66aa04366cdcc1111b99cce77db60c8317a6e46c430dc253301256e8610788f399e472967ab750fa90a5f2a81428fedc497810af39d770cd9d09824c054793a1fed28e91248e2fbe615c3cb9
  | 12 => 0x2a4a54ac58c7fb42b83934172704a52977b8daac709f947b5d9650396630e699707fc6325f0bf7d380853fced40c8c1dcf12159e2d6f07880a8119e49745e84f76bcd5162c934dbba3dd443aa57c5eec64dbefa04d5f96c8c3b4e90ae65c1b8aaa1473ff749551d3b1
  | 13 => 0x97517eb8fc3b0e4414f53432ea76d43d47c08b342bc27611543ac4ebc60fca5535640fd62b29bbb4738dc06c05431c4ab5e8002c563b045bd3b1cd190b1578175cf80ef9bebea2bef893774323d0f52d5306cd917fb007bccb0f24b7f5cfcfc16dfcb74d7e8a8f9972
  | 14 => 0x519884bc6a8342c819f1148d45d647af4bbcad15dcb214c4a8802121b57626825d8d346a73fc244c4b0cd3e3cfc90c09067724c9f4ace295eb832f992fd75ef7d2e47ac80a3883e07a2471b7de6ac7de67d6ab8ef1948061f4e1c0506a5a306b1780987816887151c4
  | 15 => 0x5c4ab426d1716988a88109df86e420f3bbfbe6d319950e61a7699824587465f74b3881605976c5c60f1a3b6aba838a1dde16aeb64890a157b3fc9aeab1e4a98943d51023813aae0a61b3bdddf4eeabac569a93cfe605e4bba4ea5b057cff2d94f495453cabbb1566ed
  | _ => 0

private def denseT0B38 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x830769a2e7fcf4cbf40965534f9ea3635cc92ff49b2eafd2ea3d7396901e9bca59373d17159d641b83380fc6eb6cb31a941246e6f1398f1de7426a6b5011b6e62b79005cbbe7f51d41164035a88ab8ef944e04898a15b60981494401d0886792d49ab200c4bf2fd88c
  | 1 => 0x1d55c6590ef24210f1ac417ba07ada108f076b3a1310669c853c90748879f513b2b8698bed2eb057e52057fab0a64e7404162559721dbf8f97b2dc59de856f5b08c441d53633fb909cff92929eb7b17885e0d7fa425beb2eb0279b66d08c2a7f296b210a9537ae8d47
  | 2 => 0xcba8eaf81d5f236e567a076743951f669d1f2e5ecd710bd5d703e15f06cd86882ea475eb3c4d62db368b426e4428b39d586f50420df75068845ae14d4ac2f31c1ea220bf08fac1a851aba54c430587dd5f6bec3a1a10f4a6f926a91a9402257cbe5ab615c35682f2de
  | 3 => 0xc141470ac6f8088216f83f4fd81bf2c80d584b84de488e6c6bf4e21461043b9e5fb740a5cf6fdd9fe6646b5a17d1f5bec4c5f05b60958c8c0c3df1b14c587991e9bf2ad848f2e7f4de9d692e41a8b95e6186f4ccaae0fab62a781cfa43cdf8dc5227c80181fc204efa
  | 4 => 0x2e0d3140713056931acfe301f7e8fbd3226226ffd5c62b3b2c5559ead8700a395d00c48d788ae91efcbb753f3bc103fd0156ab88839806c3c831f39ecbf7c4c9e56bf3adf05239ddd761f76b411392134c250a8e7248cbffaec0e3b86ce6d070dd0f49c2f9be564eae
  | 5 => 0x579d02b2e7e55be28431c3e306778d52f79533c966339c67deab1b7548a09c7d2af3aa04708663bb9ccb3600be5107aa302a43633c0ba8c98634603b8bf23ea00e8812c763522f52667db5331fbb61fe8d90dcc6294770abc899936e5b3901458a2e1537d0aa8ff988
  | 6 => 0x15e3043c8a7aa6247e7570d73c2471a3a67e660194ea8007ae741ccdec818e90b9678c92af4622050a623e027413c963fce78c458446fb49a6fbe7efb78660ef14adf3a601b3c78c03f99e48c202d408d8519b121893159fbb00010ea08db62e7e24b445d02ddd0979
  | 7 => 0xebb5cea7c7beb3186d9ced8fc05f5f5a339c1e75229238fec88d44ea359e684b827196142f3df72ea61d8f270b1445802d0152db0cfdc611c7279fccf1a103abf888f5360ca4883015c9e0881f905279bb94ab834941b1f28cd1821aebbbe8b52284a1fcc6ddec69c4
  | 8 => 0x96a0c6417923a37347e04b0e0152a9441da9b220303bb939886574e8877cc4151ebd0d2e6d298900eedca02d57a3b493a79e36afbab8887262fe656a755871e6d5e3849b57f20e13fcd9a1bcfbed6a3c812ba91b2e789df31d73785e2ffcd13afcc4d7a24fd0733df6
  | 9 => 0x25576222e185355fd737c028ad7169373ac1ba4d9d6ee7a5eb0b1161d2811e12e69d0ce43cf7550492432800d633ac9219e213efe92ad3037e7aece01f06f99665a3918a8474f54268f4ccfaaa6b26e326c6639bf9194c60f329f5f5cab0b91d812f4271b0bb194a61
  | 10 => 0xf5531b174186750abf73631f286e16d76bb9ed0febef0d1efe456dfc55b2317f1f8a50afa818fc6664148f122a767d1cb6ad9c926c6ca5c990282ee9be26461569e9791b1ee907557cd6b269a20b76982deed8b94682ab5fe99161b97c66fdc0da02c4fd4ffaf51d7
  | 11 => 0xffa1c8c56843809e647efc9af95f1572c8c84fdb22a6876aea090edec15b85b5d8554aa0ea5e56f82061df10bdac6467423749a918b670c7e06a3cddd852c30fdd787fc0715348182191338c6028775079ecbfc7d45e73000056426966db40fd8c6ea2a993f1233a91
  | 12 => 0x5706f4879196e31397a765de06fddb0ac07f85591a08f502a5fa2201ea5e7b8054615f8d9b97dc9570f51d1df5fd0c9b7335712ecb30b79c835abe358ddbe7cf2df2feea91f168f2d6af623401cb2585dec586c79999f5ed81740282df5ded80f06c4fefaad50d5d18
  | 13 => 0xda2c585ee87db4bac3c3e197e79ddfdb663af8e63682f12ee57933ed9a560a7ec5f6b25ba7a2d9f26cbc53630fbc387a3b7f3e51775283360bebe0c10db35740afda011bd202f9d11431499141d0bd953651faad5ac6da6ea05a9f1df289d08bce584cbbad5e1905e7
  | 14 => 0x72b92013cfa55c224420004e6abd2fe37241e8953ea93fd7a8892fb351947a831eff7a4a31f8654f18c3df311a17c5018bb81d242b3753e68ecfeea4bff3ca75b6743de2556d57dce1fbd531b3580650b3e860ee1ee82ccea18cfd9c1eddd5ba0864f9e76fb1f386d5
  | 15 => 0x39ecfe20465b1f707be346f332a41bef04da6cc89a956b1a84589e66a7a891938030e242837d7b3fd82c0a7d89ab21dc6b2afe75a0b8852fc81aa4d5ad10ebab253ce4128d9b3ef7ed78252009e385918b0e62fd7a3f320eae2740862787ad0fc2859a78dad63d4a21
  | _ => 0

private def denseT0B39 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x78758032647adaf4cc59d38491d49ec64cc011484a052b78b25448b46ba04ce633ee8f649bf961c04ee9f4708db73d8c9be43a5a319c02c42cc654892a793fd1f421b3e1ca36f17617d73e013e2d53fef4ea09fb5b9e6886f56a346e883bfb5bf2cf96feb2aa2c14d2
  | 1 => 0x6047396629f5099d71ef2e605838d1f1c7842cf795586aa3ef450161cf96e0df619ccb7afff28ab188ea874940cab5d4d0af8b76a4497d7874d41f153d2ed698c29e9641d2e89997c1d8fc28814287ffe23a899dfbc4ba064d7f31959a0bf0fae08cf771f50b539483
  | 2 => 0x72f0bd672aba13a95df2048d61f26d496433980d38861fdab8d065325d71e7bc24bf9249a07abdf7bf78006889fe3f9e4dc043be28ce76105047946f44f1122d5d7ce17f7f62a47f665b40404e700185a8a838bbd491df2ebfbbee7656a818b74f3fe145984a6e56c3
  | 3 => 0xf7b928eb4531c8bd41737ae57167df75237677d659128d7ab53d5ffa5fc5c4c23a669ec903b10b0e2414a8d7ab5224f92b5f228ea8b2e7837b8379b658cbf5f019e56ece65e5cf4dc6e8e00244e8710500c494496fcfd046b9cd6464d22bde097c4247292e54b1e303
  | 4 => 0xe19b553391fc8808d49f0f910012b6f5eeb1e24c03b4b526c92dd84a4048d8accf68c0a33525ea0ba9bd8b7df0288f0eb074247d0530000d8f2e4ac04d7c67bff60c4896273c83a0d11a82713274d02f7d9451130e880f5890a37d544267ad98f11fd6bc93496c6c4a
  | 5 => 0xaee9c8249f961753b2390765b78538fbd5f8e30e4532461141c158a041ebd03a1897fcd7e3e6e8d334f6daf143fb4bc331031d0d81254ea38764d47fcb9234b9c4726f355ff32b12fd50ecc8264763511cfb7534b474f48217198cb5a2ad2e29a5d58685f202986c45
  | 6 => 0x90580cc7fd13cfd46b5d8b6074ad3d86d16deae7d3f073f92ce8bc4fbd9a08ee747b8fcbfc209f5818b348901839d03a24a89502e55710cc3bb54f6c09a06a50f17733d4e448119b8f46017b1ee8dfd790f083d31aa8c8866a858f95836d7908448827a1ed0a21331
  | 7 => 0x2d489cb4a17dc93127beab0e3ad2f0f5c0137e0017ac5faddd26611ba426e33e205f7c08b7b21ad20d73949370e12fc07466202b7c4b0b3be825b50a4b93cdba05a2851090d9837071644bbb697d2c01e08abbb124717b075f73b0b5316d890d01f78cb4108806be15
  | 8 => 0x93457f69caedf90df096efe8d0b20490151d5f0869cfb737bb75c9801c211d15035591aa29ec1be1c5fef97f4818dcfa462567ab70800de2dd7e5802ee0b1d12fd6995bf19be6181060585902fe3536255831ae8c529609e04911580e0f0fe5d0551f8ca1d33e96c46
  | 9 => 0x9ac667031e92a654bbb15f3a3cbc49139787465323b9ec39413b6c325a8d91a843d013cf78de09b275695828ccad3d19b297be50021a7032ba636f97bd2fbde4fe08d13158e62fc15f0a3137bc99e3eb6ef21f0a7d679a336a9cf5e7bc6b7d566db22db880b9dc689d
  | 10 => 0x168790e3e85ea4f49090d159661e5cbfd5a24131efa39ced2c0941292a369213e9c16e0812ad72edc1d05f846e7bafc51ab133150d84798eb128674116c9b57811c102125b40913876016e993bdd6cbba9a1509d67dff2da8e4a245310bd5b22d7f633380ed6160988
  | 11 => 0x34e1497f66b7a3ae725b4098fbc64dd56d1aae84e2f16556bddc4c8f44a65ae7fdbb58df14ecc6600b30c903fa29c623d16f5dda052ae2bd73a144babb32b0c7c023651cf6a3e668729c72eedcb24671bb41b75deaf9ae857bd636df8d9cb3e5c2a054442bf5c3f777
  | 12 => 0xf673e031ac2cf715e64fda5d74660d95546ed0de205fa109015dca0559eb939e46484c58218d414dd54331aed8572302568021198b72cfafece48cef5018e1267d94fa6678cdfd95ea728ac426ac55c7fd171cd789fbcc93cfca136148f2e9d0ccbfd1ac8b298718d5
  | 13 => 0x1b60d21069c00e2b58359a219fa3f20cd348a082a3e3888d5e1939df2127c7e9e96c9b0b334c0e2daac20e7ce07408f39206b8dce5e9bb22bcfc851069fe2818b9af29849d1757e6df570943b6af78032b95486881d2a145cee34866fb8f37d4de4cf6fd599353a3b
  | 14 => 0x3c0ec23475848b63352db0edb658b0bb66226cef606907c9a5eb5e3c0eb35d057d94e54df6f2cca75f22b94a78b858ffd8f3623f2d9c6db389ca38750669afdbae61e2ffe8dd57618e7895c3b225e4a4cad53d6cd09f408b99b5e8a3ae43da8e2ccbf82276c645fea
  | 15 => 0xdd4abe3aff2da1435d3ea739378094042b0f90ef761b1cc6d57e4da7627bfad8abe4892cea0c91f19cb8542cce5ba74935fd3eb065598b52203937ac3ce74c96be9645eecbbb3b3665184e7f8b272cc9a27cc507f0a1227d2b0b4f6f8d9bc26715b51ebd754f99e210
  | _ => 0

private def denseT0B40 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x866d6e044de502b8a8218366d9d85906952e89867a0739158407cd22c701909d9b405ce95f2085a6992c8c6cd548f6b1880731e8608968811f7913867db7d22e8fd058035ca7bac302801c79cbfbdbd76ef9f9a4df1496e308f9f629a80b6dd28716e48b054d0ea210
  | 1 => 0x797996a857b45994d17cc391c22318beb7f7e800ca7538214ba53af375d7ae7065aa3a5a156a98711707984f0f844f7a80d98ac8813a34fc6ac4de8a4f1e53f26d6a4656ac9a34ff44ba205e2dff25661cc14a42ac9df057591b1a525b750bb2d4bda9b79d5a97c57e
  | 2 => 0xc8be596d759beeb94011519e2464d2a768b67c775f60f4da2d2bf0aac309eb8a7478720488455d288f905041c22e1a45c2c62de1c932e1c164b474e5bdef2f1fdcc7225b4a03711215539ee177c381426f0bc9dcfb286715c0fb8f93a4565a6069917de33eb79b62c7
  | 3 => 0xb0bbae7783d305a189cd0175d0d9406b063fcae8e668116499638ed3661fec36ec2c5a492a803cd29a5c2e2ea409795329827377af7fd8831b0530198457dad5b956273140188feba93612eb95a3548e0b47ac26628fccfcc4e395778df3e00d859d7d1e5a8832b4d5
  | 4 => 0x3322e6ae959f3a318ed63e40c6b0e8a1772d296ac7dbe36a3af378b32c04ca70dd1becaf2aa985f0dbef4b70b4f166c6f83f589a597427958d146c4d706492205bf470270f521dc43f70649bafafb5c5e6cc6b28b5e753b09d25cbdd2113123a48bb606efd597f65ea
  | 5 => 0x3aacf32a879276380670c8f96cd5d180348f2f5c50a585fe55a280e7762db233b7525600a74da605354c7fba69424f553a17920981a95ece298273d559cd000fd043d22392d12415bcf7d7048bfc0182cbad77d9e8577117213f9c844537b5420579d4f401f236864e
  | 6 => 0x2859d48ffde9c9ce493d652e64ecd69c4998f0c34577abba791477a4f91edcc9d21c5b45a1bfee77b097a601e69b8efb34c5cb5c0444e21006f5b4cda0d95e61f4e1a3891bd55e47faf54f9d3254a64f97f05722ab57b09ef793996f8aea61944ada635ba7c5076361
  | 7 => 0x887931eb8256421f705c58d46ed9eb1d0aa75ede5ab80a83e479315b4177199fce5a519946650cbcab773156ef054c52c16049c948a1cb6ec503bcd2b4d12223cb3c6f9dbc34ae9aa7b730af2c53a8bc63c79744d20b52a0622cc9595678a5d8cc1cdb58caef19f925
  | 8 => 0xe1ec682828d8ea7a65c13fa6976297fc004d4fafa7b45d339d7b2d674b67c4d3c4fd12b1ceeb6938039b60753fbb33469f59c81ab8a0b860b257285e8231f5a72bc80ab32f7b6f8ddfd9a1baa60ad291b90b6dc0bdeb3bc78e63a95ddf74e9781b9812f0cae3e2d9d2
  | 9 => 0xeb684364ca2f869970bb5b373f490e7f2d9fd56a676c90d797ae11e576ce2768557bf2f8a6b70c6e31b975c52d167714f7a029bcdbbcbad93b02089b7704ea607332f1c0a4219b9480d9b7a3b45c699c68855fb1ecfa2e959a2852765cf0701544c978b6580b44cd6d
  | 10 => 0xed60c3aca338b5ce111e27bf212f90dc3acd300b272d20d87e7010f90987e8e59b48952eea009dda7a0dae1567b493bef48d7de7d0783950bdda2e439568b152da883fc7a518ff04600b5bfe6179a28edbae46a88012b0fc33713d63269562d798873aa9fa6d362bda
  | 11 => 0x9f03e170c542d52f9f84162f029b194549717f7222aac0d21cc923b66c19dcae5ce0e7e797d21c0cc601252973c3267cb38760713f5fe910b50ce0fb86d42e6d8e1495ff9cf15fad2ea7a60e197aea9bf7db388490ab07a857bb3d709866df41acbafba39ed243d724
  | 12 => 0xc8d81e057cad9b9f961c1b2185cf1543229c437705bcd620aaba450f5c74d32399a0c925dad32868e9244c5a1e6906b09444a40708b01ac58cf85c8bea48a8a6f1ca67069c9b14e6b7bf3a2aa48e1fe0611e8d5aa8f5686d435fa78537d93f4afe14570824e67d6abb
  | 13 => 0xf13d92f38fb12b3327623932acd6f8f77603a83a1e20f5fb38f86d183ba31f4465e7b4eba093033236789fb4f50b92f3ea804bf430595448f52225bead1d1b58b8e8604a373f8eb69aca2876b45d35f77ef83d126a5fb8e1b2c094a9eb67fea169dee54223421e3b31
  | 14 => 0xfe034866f570cf2123f94644747ab284e154e6e97e8e2c579cd0895e3db687afd60dacfd70c61a43a22d3a1d0a39123d83c9283cf399a54de0ff5d17f1326d86656df298760420bfafa397b638963d20439309a522d314baddad7051c0ccfc82db40d2ae8ce0683357
  | 15 => 0xbd230432d841f9fd861e954dcb3566f283b005f085b23d160ef1406b8fb98870a6389f1fd5cc507954ac64154213624ce3e5fac969a7e34e27da00100639808bbe6d0f20d46b87106d29df5c270fce6c7bd51ec6ae7d0f0d5522a6a965ecc9d325e6704ba7dbfe2a5b
  | _ => 0

private def denseT0B41 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x313029190f10a7af6974fd8451922f56ebeac46d35089a397ec6a79f4a9c3f6392d4ba9e1d2ba498faa40650b36361284be454dd84650f47cc78ac385167a9688fdd782dfbe9405af31f9feb6d41e92f5e1c77b5b8a7a1eb1e4ed786feea85350af03df15f526c737
  | 1 => 0xf24ab86935b177ed026db11fe09823d079c15cb7c52f94625fc92d9cfc8583a5df1d5bbf4f4ff25e15e974495a1465843511188adb0cc8a655537fab764742b2592df986aea4dca9849429dd2783b2f487b729b159f154ac10d65e213889eff38b63329afbcbfb91f3
  | 2 => 0x672dd472bf59b2b66e9c9780b59857b862e7592302b6d9b5f9608410976027bd11cb1f759e2de710dacaa65be9174cabd91e1d37d6a756dfa21cf0acfab29874ed7dc183b61e18e7265e9c6666616a1ca7cb37e307f1e48623bb326d46ed6127459774ab2a5567c799
  | 3 => 0xbde2fc5aa22248719ae2b6ee8dc40e6b56fcf7285d28e8984c53e1de4f81048c04a4b9232916c19f903e25551de6b0bdbb56d55e08bb4e209a91a32713d0f563bc6a0be2b4ac0e2439f3ce79c1e18c6aa520f8e648f14ef27aa539ca4cdfbc1c766814bf4399058ef6
  | 4 => 0xa816b127f0d9ea75a16abe0e5279511e8a6a08f30ef0cdcec9a242e73f575356bbc3f5be2a1ec0a0afa885df4e73a9330b9354f5c6aa686584f35e97b7a075e4ae7b7b25f7015c307797c3aae964c9cc907de09c3747742eafac6fdbc94e6a2b25d09fe82ce1cce805
  | 5 => 0x8147658b4ed025572132fa7f0f097871e56222074d829f4057b7dcf37f88d1910d40676ca80da1b8c5d884ad8843d74cd81ac9867339549deace862f2893bad21535a90692f1b9c5813f5271e66a77accef56be3bd5b49f706fef465e3d3bfa01397a93b8de36491d0
  | 6 => 0x257dcbfd4a23bb1a795a9b00440304718f631a94f01e7032e6c9237848749009d13db6d279058f71934c06f5e1d4988b699edc42ca0321fae9aa268ec074a4e281a1dee9292dd7183f648aac22975ceb55cc9f9d0b6c9b8f1f1163e59623626112422f1e56d7cb07c8
  | 7 => 0x7dfbae9dece9551e8ca3fccb3c6c9b475011977e56c6014efc19d035fd213c05fc0fecddaec2f1ad6be8c516eac30dc60ad08b44666efb5b90f2e72d69edb02cdaff3f3efbd3b32e263167c220744882716934fa6c9dca6b5a0155543f68907a3127b9374622170d44
  | 8 => 0xc9cf4c1e341027aed0060deac107348991e1d04065de4d161c3638a6e5ae405f48a846d48d1c34d1e00b29899cdf8f0357370efdd2ebfdc7215c8034e743eb7704416ddee6cf15ba8746f5b478016730a9df18b50bdaeaf95e943f0ab0e42209174c9d080f10ac67f4
  | 9 => 0x936c9ef58bad2d28c25f7c3504631276a66c1590dc0ce9c47c69c8f49e5a63ee61681ee3b51dc6315ee454a01cb031edaabfb761f8a80b46479cde4ec4784a6c403888a21776364a0454db4b6a35d8a16cb8fc51892841e809d2727a47edef9e41ddab28f5686ba2df
  | 10 => 0x7f0f091841c06275595b62bc498f1dc581e453f18aa3a0e94ebf485f89e2ecda219e62346425aad7acd8917f63adb31108495236e90b96373fc89f271b6aa55bb64e539ac4c42e80581e11efec4a5567fd5dfef22ed0c8bd2cf4d8f1ec0d626845093235be80390cdd
  | 11 => 0xe6eb22c344f07563190729d0e5bf0507f77d94bf1ad098dfeeb7bf8117b6e59ad23377f2574e9ad498b1bdd1bed80792129baa329966838a4039975dc10425858c7ef3e6321a02dcd61fafae603e858c59580fe220cf5f2625b81a0db15f948a350e85e5a4aff0af2d
  | 12 => 0x99992553e330b1817578ad00f9b0ede28590e9759851a6d5b86dde381abacf0b9845339a8385a5d5cca81721678738bf73e167c6afcc5b39a1b36afff9c796bcf2ef4bde32d1bd25394bb40e1cac7228636977d1f9bda459895fcc5164b4d1ca5e1633b21515644dc1
  | 13 => 0x160323f18d116c394c0293da5b0ae99bfaa8b0b87c9468d5e31a2e8c6cb1d907fed42fe772503f8e53cf0efda3c2483829d9f7f344fb3c82cb34b46b4c2a719cc659431bfe19bae85a5a2d6c3bd90a1896b2aa2d7b59d060d6d01ce84180898ddce18e04489696fb81
  | 14 => 0x1b2c4273833b121ad77de189ea06caa8ee9bc9975eed07358adf504d8dd2b31c356ab0636027544409b535de4837cc48b5d14e5f7830708ec7b01eae336996ab71d472d69bbb458c666f0d712c81a912cb96a3c958e943bd8070a27a9d311ea2bd0433cc3cf5337cf2
  | 15 => 0xc4da66f0690c4188bde71fcc4c3b65c19af0e2f5428336454c752a93871994ebf9a6e7f8b9b089f61aa4299e7e8768fccee9f1d4bb1e38e74df36b7dd8b6590e2cdd613ea2d069d021e12a83440d215b3260728718a267f60b1c630832e84edaf9713410f7ce1ccf6a
  | _ => 0

private def denseT0B42 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xcc03c0b5a4dfd657b450f0b2796e2189ce3ad6070279f9ec59df093a07f6ac274fa3da0784dbf828be8a2477f9933f7855337d1fe86c16c50742db2b0fdd7b0d33da5f0594b001689256b12e2f2d66dd8c4dafe9d674984220621f5785950d46ec60161c8be0722596
  | 1 => 0xb5273d6571711ce772ec823e01abee11ff4fdfe9fce7483b341d69ff7676a1d088d42d86f6a48787afe8ec3e6132177f851ead8b86db31f06d4cf72d94b07c095e4f256da96288b9814ac1db182d02d663ef0223b43c339b03c53333b16b3db816ef45f503a6956d04
  | 2 => 0x3a67d813aee5045b231d4b5d1b539223990fed918d21eedbe450fc93edcd304d2bb295b45216273ccd6df8e135973cbbfd64c8e5f0a3324afec5556d6d7d0e88424d297c8c4834fca83f4ad4a8d804ab550851420d89c55e55f1a4a8161e45ae48a775c17b36223a61
  | 3 => 0xcf4c8a861aeb80d6b27cfbaf7d954db5a28a5e33c0375f958d0f08359f5fdd5a9e53c2dc2dd9fddd8a1f4b709b1bca1fa6ce8df904c810dfcc0987ff341b16ebddad339ce0930c838e4471b74bc4a40bfb0211b931bd04f2c2ea66d21fa9996b2118bcd283b7c4b96c
  | 4 => 0x77c93ae62c3c9cc110420e93fcc1da8b0ca39f9e44af4bcf5afb771ce0bc3dee09de88c20982e00fc26b0497b1a7b91f0bd9389356dfb62624015df0a9937575d80264d091c3cacbbea50e0b4b5884ee520bf2c1c82d203a547139cc2e0d4b3df57eb6122c5c7bd59c
  | 5 => 0x57a663b42e8cd99bc0a5313e3dac28e3dbd4d272523471f0c051d8778158f2b803c73b6eec49d9f37dc7ddfc818198041976980c3e3d41ee20aee9a196f38ed872f20346d66d60c69fe4e54201fcd5f684324d32753bea00041d59c22df4bb8069e134f198a25ac024
  | 6 => 0xe09fc5abb8e37d8de012d35d85aaf14d728d5aa463c7f3b4d7c3a67869a5f9df34dc1c35faaadf0138be72ca781269efdb91ef7b878309265ebe6b5df4265f4dd3dc73eb61f82aabbae53ef08b748dac35b4974b96cd152010cebd8854aa7663ba9953be768a785793
  | 7 => 0x704cbf41115c77409750798eeffdbd533a92ecf1d1d3dcadf43100dfe54ec9ae29e6840363fb3162bf5d74bdc34954314919b43a06775b401925cc306c21f8f594550a82ae0ed78ad3f03f80f28cd8e10f5fa7d9451c41613a502c45f1ed7c300996d192719880f9bf
  | 8 => 0xb14fff1f494175121e9a5e679ca5ee122653b4ab573b1b679a5b98324c3669122c4a469958a011deb4f2bc428bb851bf72daeef75e2649d3fc3eacac4d7333cbfd3ee5f63314a97bcebc8d052bc03424c95751970d323f27c858966ea7bc9d6afb4f0a8ca179c5c42e
  | 9 => 0xd133f4c8859ca46ae39784327f2cd83af0fb32820c31e42a8bdbf8f3e4459946acf9a2c0aa16265c4529ab9b4bbdfb699929a66583aea1624434b2bd8bde0a2cdf9945ddd54ee7c9fa845f39ad2f30cf03d63cf040abf3e3590b5d5b79e615123b3d3716d5c96f6261
  | 10 => 0xea80fa4f458751b384f16cdb698714c08fd528bd7deb6dc25872cedc8d3cedaa1eb553484143b9c79ce1afbb211ee27b7e1cc3e44039cdc02b6dbc4a9084b50ac4a14256f5275c95f32c4739a919523a2396d375ceee0072527d4d21abf931fb18baff80a3efb25aab
  | 11 => 0xcd39bb12ef15de2b0ccd50da46070e055396aaf6d52f98cc9cf318c313abeaab42c831840dcaddb2c7d708e152a612448020294c348b42f1e46a4caec23f7e5876d9312d82a334344ac59a00929e426ba3ffb9b71d8861aa8e1689fabc61371593015a95d887b1b003
  | 12 => 0xbdbbeea53a2d9c63642840c23095896a99c3ce055d4b335e1b08b3b2a973586539170ed583a7464760b070c90e39c1fbfe1c383a46599f7650b1770e532cdb0c7dfd69833d9e8d47f1e1ac11d1d2a75b52da0d0eaa991186a8e77932d8c6511497dbb44957607498d
  | 13 => 0xe57ce4ac1b4d977c21ff6de500512213873504b301ebe89f8e0ac9ef2f5fe5340d838aa686a873e9cf435dd56593f9b98a181c3dc603e0fcc4b25a6a824f46b7263f994008011c73ee7350f3d96c956bdf0790641ff7635ebc7e3515a16461b4a5d0642639275079fa
  | 14 => 0xe7c392a2927bcabd8a3a92b15cf928ca577e284da7d0d994b8ef8bf269d22e903a0028487c1c5acf0e4589bd8821fb018022bc864d20854b039d3f90cb33532915bf9b3acfc52f77fb1fdf05bc0dc1b226d745cc37e0a87846d366736897642e3b92e719cfa8325c2b
  | 15 => 0x2a142a2995eedb2a891655ffdb7fe203cf88833eecbb80985c2e006847f35ba29c9ec808e7123a700c35e9a4ee06a0cc4da616f33649bf4f1c2efd86c1f5a8f5862794c9cca49a225a0c532075860f58ab34c2b3b6bd5d7bb0f689ca736aa2fb0f5091ca102b00d09f
  | _ => 0

private def denseT0B43 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xeba422bca0751b313e1ff2afabe2884845185c9e21115a3bae9ae2d39b965ca02ee215c3275aeeef0ef7a148714864e5c93a4ce7a583d61bd5200bb5fd9f6ee9e5c9614470b235718e5d127e0f88b774ae0bd483dd42e976c287d91ee3b46c63b8aea6b025eff2d782
  | 1 => 0x684cd28d04c616a72dc1c86d7496aa6ca3934b3f66d664246fc23e5186cd7ebabd04d186ce0410c7f22ea91d6db2dd67b079a271ac4b10f27cab9c2495d3a5aced5b375e874454c79326b050483ca548eb6e4553326ed1e17c0b79ded83029c24368e0a3203c7ca482
  | 2 => 0xc48ad27d25404574f60f29a6a28764c7ef80f16d2a40c4f1ee208304eaeb8a90253b7946f2d6a63093e044e931e224f52cd084026fc2821bc98486c5e9dd6ec6194e40af74b5c48d3e0abffd9480aa3d1a1f2aa9aa0e2a1d84ed141d3782922273d95bc8e61b39115
  | 3 => 0x26c2021418f17195b10e60223deec1b6bd587612c1ef94a58b2c4f853333844d2bfe3815ec7a44ca0c9b2b98fd54b67e02221bf8ecf6469d5f429df4074daa445066c9cf199822cc57ea44c866563a1f240a28b5f135c76398cf80eaa51e6b1a30b5e41eab6e2d1e35
  | 4 => 0xab0e421efc528854574f7a8eadfd2c018330cfef97e4e7773928f5ca14b54a15cf20c25ee562fee968ba1da58fcb8e3f49dfa45b97dbade00e5c5e11dccc9eb6a88efb376e64041f2a468a54c06f12c0c56ed6a57b480d6e4b6772b038b8285fd81031764a10a671c9
  | 5 => 0x38f0703391d8725984e95e835c2a8cdc7775f71cb123b569b7035fabb03f79539f25df1c13d573b4447548034b63d09a63407aa3df8512c8c99bdb311002d927ec1b24b5bb901986509ac5866723bc3a08da469b9f19c3faa4dab8b253826af361067f57cdeace882e
  | 6 => 0xc7c638ad9659d053db949ba60537064ef921666558e668ef48d68c817e357b87c483a4f20911f4e16d8ef04ec815217f27c001366b51d2b3454a8705e211b5e6363f16183de8f74c8735d1cd24fc64aea0376774670c92890fcf7c22213b00ac4d666ee38cc5e3b20
  | 7 => 0xcb0d200d26200c93b9b04ae04ce6cd93622d1caf986ec82e0650105267af0a7f66e30c79a751c1e4505c5d08e574970c77525ad3078ec68979c131c6f443aa7f4e7112bc960506634b0fb5a5fff138652b7f1036d5740ff565137945e10af51d15a8e919d2ec048343
  | 8 => 0x1ba555d3e1e23ae7dab87c8499e36c1cc949d15ce952f5fd3a586bd37403e90759b6685fcd11614657c0a22fe97c33c403f9cf74b8310b09bfde2096bfaff624130f29b64c577a861e5508e9191321ff71bfaadd338d27a2f1bf5014692b3435c847f1fbbdb100649e
  | 9 => 0xd598fea3d626fd76494aeb6861f578fdb4fa555c5b831492f3a26c01ecc6568c5bd43dbc158c1b6dcd96e28d4760f6e5b069e0e3a49e8e5285219365f92ad4e3139af5fd5ced3a60f0f6a8fc38b44caab45c4f19109e14d4c2ee7acc3e0397ed4b4eb0df5a1a32a494
  | 10 => 0x729793ce58c846b277aecebda3dca9454006fbe98172b171557a952f3fe5f5d201f0297622a60f7485c2ca0253d96b48d2e129c6b2944d47a3306f100e63d865ca6aa9c8faff291032d49dbb22b99192121b257fd5854a2c38d513917da05f1e4833e176e9a241b6ca
  | 11 => 0x62520a2c03b77460f37def7c557d142a592213d2211c7d8cbe2f5cf28e6aaa9d66017ae361222e4d43304daa2a8adab04286cc3e6574808420ff5003850b12158227725081338f33de2c1b49ea0b026b094bbf824fdc2428e25add9993b59a4471c967612cffc2d337
  | 12 => 0x98e5903f56b5822ae87174c5a8c5e095cac223864326e88b00ea80f248049bf336d126ae3e30839de28acfd36479f9c2083d5b68300aa288cd7f23bbda962da940526ec6ab29a02892baf9b34c9dc308e8107fec929342925bc649360857234e3af65fdc4bc8ed8c2
  | 13 => 0xcfac0a4af14caf5c147f949e63156b5f7f28acba82c27a0928c8d8bcff959fb641686b11408eb4f11a2bae6892d644b981d31485116581712908d02325bd48387571b764c251cd8a9a873a2eba66388f1203a6d302eddf52b82bc37111f86dc82a8a2e0138d95fcd17
  | 14 => 0xf58c06d9d4b68276313e3e35278afe4d6e5d879bb02b685a640d713db5fd0b4f1de40104d5058ddc5d93c4bcfc99734c1779264f942237f8db270153b78a359de9d45c2e994378ae13c4d08f732cf9e8ab3b482f6828efbdea01d10a85a7e853dd0462f551d1ec6544
  | 15 => 0x22ec8357a0bec66c621f73fce90c346ff70952017398db8eb32b95895814e9be032112825563fafd8b1bae12bf7e1fb341423ddd7c924ed661558b51bcd9d89ec7c44b654177191a39baf3c5b18553c4d6d4b0f3b980642e465564c28922542d3e2dc342bdee606585
  | _ => 0

private def denseT0B44 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x94303bc29ce2ace3fb23624670e0e97bfce7fc67704d7cf20585c9d61f61761282e34256bd6bb955808d3a3b454a78764fd372099fb3b9abc863ec788be9a9b37f55eaa4188f9e6e18e351cf971ad248e9a94b1eaea56bb7fb165761ad810b6cc51bbb27c3ed2a97fc
  | 1 => 0x509926bb4f84630bf355c57678c08e5a7cd6510302b413c6c763ce302211a7d244eaf751f3732103920e2062b2cab9824b1281c83931cbc08478eb65b965c665ee48a24cecb4ca18476dc4538c61393ec9db661f218ea74c3de54f57c53769f6a04666db9b5440e0d0
  | 2 => 0x8da45716ea51788f389865ca6ac8ecc33672b5b3cb7956c2c4576c30b74b1175468d744e5751187e3fde11d7189289a559e00ca93e80d78eb82c5cfccfc6147de99c7af56b665c3d838467ed971f4fbde545d0debf31882f5a88c01858ab082e6aec14cbc71a665dd9
  | 3 => 0xc57be2da9c04482b689e8d539223ef82a621b874f3f5cf237271a5f15f2b04656756e67860b00f7303ee10d4bcbf39e08c0ac8a048012344777f3444f9033c537db32c9c447be2b2ac8c909619fd34de999983a60f65f3926b1ffd3a98045df8e51286f1f7f843ef75
  | 4 => 0x260cd81033a9f7216834ee18c9ca0ea08d95a052f117e5b87ee3466212996d91a85050a20aa191a373fcb0e7d87f183c804d5cfb05930fc785b54e1033770ff058987e0046da50a4318322e0a738a42d0574c1caf9c8394631dcd7fde19e097477ab735d563298b35d
  | 5 => 0xeef8e4a991e0e359bf71b0a79a63e53cd70fb0ffc99d04fd643efac4fb6187de8be58de2b051ce5c5d2472afa5e8429d41f7d3c3d61bcbc88b1750a702e7bc4d8f177c783ce03f96175f8d408c7605f44296f9daf0a6ede95babc90d1773700e3009eec4c4ed3e090a
  | 6 => 0xd9801d05c7737a336da0542879e619545f4b8a20710bec6aa343719eb7a4af2ef42e08a05f2784e23205286f5775e08d2b1c65078776ce653ade6228f218e1b2d097e2f9d0a12484a874a4b30f6d16157713877b141fe0306b768caf65dcc2f081768c2ef0c969b065
  | 7 => 0x6f91125eaa2b1a34f3f03ec75a17317a5baf1a3d5fe7d632a30e928c60c31daef6bbbbf7260cb98bbb1fa4d010fbd5b191b376194b014932875021afd08176f3e3f614ff32ed0212de785d45c57e4882cdc8ab07dea4470e56f7e1749b5b8e9cbab92eb04cb72df03e
  | 8 => 0x2f31b15e46d6c2f015b126353fcc284254eb7cc4b3a91c52b00273c5e86fb912f833a42c799bbeff0bbe23a8a11f2f6fe6a252e4a38333e1b72ca4946dc9abf1c0f7ba1ea128fc0b7f4c449a8a7409e38a94c790f548964ba1fa951002b6b56072935206f529c8e3bc
  | 9 => 0x3d240273d07bbca676268de792cf8b5615d68ce85ec23e7912786f5e15403333ff5da8630ada99820b81ab30a80db6149136991d40524e65010b1fd357a409db5f5825daf3ba14377f846bb261bdf2294172dcede2c9ebc10bc36069f041c9af1ec5c18f695f3719f4
  | 10 => 0xb6d00f5708d5a69023a148f21ab1e78f2751e10bd7dff1a36a03b5e9e7a24f8313e940bed26e2ba80202a37aafe4cec9e41a8afdd6c9d81bcbefc09e1c0fc4ca9d477b279dfd3cd0d432268afcc9544ccddcbcc5f79110fa7fa0c9f078838038df9862728f28fd8ecb
  | 11 => 0xbc077d9af45b1a6a617db15b0de96a19908cd181c53b8f013414f47443c28f9413837a17090e5f6368223244e99ad6ddc42f4a1139083ccac2169c2d07ef927524d3cb9fc44c8e226a2e7c58d2b1f4d34206d7b299aa19f35e15dec264197c5e1b3585a14d0fbab54e
  | 12 => 0x9a9f07e28c52e81825a569f25576b3eebd4018fa1511d4d1c0a4cf67c45aa816a7d2534bcc2962a41dd9b79612e7183038a974dcefbfa85c6c0f3d5c62331b7db52045d84f99444e231ee0139b66532eb21df865f8850c65ba9b8cd12130d6e9e1901609c4c5c49e2c
  | 13 => 0xc24eb50a6625e29cbff5ef0bdc63f8cbf22b948f1ddbe9816f2dfd123c61eacfd1c35ef6f72f24d8becf3a66c237de3b49d584f05919e3beae33c985cd8483f4f4ffa144209b263c5ffe734bcb22d0cfcd9ea41713466796416ebecdfded300357cd3e9b30523e518d
  | 14 => 0xb8b785ccc81b6b4accd39835c9325028ce9085105d71d92b0e768d2ad66e1c7f1336643774e4f16bffb2573efafb9ad7c91948fc76710248a1844d859163ee61fb3f18a2089b1c0104fda112e5ba3c73cf85813812cb9992fd5d21dc7885a482e6fe69e33f1b050ff7
  | 15 => 0xee5fc0b18a9f42a5bee7252716def620116f806a0d6a1d9d2568ac00cfc696fcb2a96adadeff37d520a7553b8392292206dddfcbe02170d7218cb56716ab07c539f1fee8427c492ae90a19ec0ccbb02de609ab4e87b34ab56515736b75b544a9a6e9328976669831c8
  | _ => 0

private def denseT0B45 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x601a47d0db06d65f2d9bda2f49824fb52e1aecf3181af4f7a663c4f4f98d05bf6a8b2b96e98f7da910591821bb1c701d5a6ec766d7dec2e011ff7939c26abb8cbe284202679747321d8134064b69717bbfad50db08b177263da7b14f63400f5edc0342996dbd8f0a2
  | 1 => 0x732dce725bfa46b97d0da180fb2ad463f6e817e4c02494ec72b2f3db58701f207c1bee65b0d1f799dc1f1aed4e35702729e33210f651486e35e7b8ce01ec8a6fc69288ffefb368d8b53ad64ab6d94880f2af5e0486f60d8774d3196a9006eb3b78b1cafd41b22aa759
  | 2 => 0xb6307d43165e8f169aa866fc8c6da2a5f053232a31e7c8eeead750824457511c41c59e4491a2b04021bd8a1970302242684db30a38a19b1b7f253790faf26281d59f20cf034254718963b16f204142c59e32c2285ef07f5e9aeb1bbbbddb77e71c96f50749ea57952c
  | 3 => 0x96c7ba9f536ea3326d3e356d116e351710e29f76a77fcd385d6600fa585a37409526599e316a60d9a3e426cb0e7eeceadd5f0df3be39405dc294c6f82d153271b5ad8de8ad9989db63fd435ccd4eb7abe683f0f6118d3edf3416f9bbd244faa44cfcfeef7b5a52eaf0
  | 4 => 0xc75afb80fb90137ba5befdb777c468e718138654e27364e899dccd3dd1bc44ff2c81447627da91de42d818a55850f7e697b1e9856e958d557731cf82f80a858bf2d5012c680f9ec26eb0f3d068b3ae2be0ca26a1ea8a9df2cb745200573f64eae7f536947526bf7801
  | 5 => 0x46951d06be17aa3be87377773ca3a565fee7eb6a728d738479454f047b43872b3255d8014ccd6e3829bb05a949c4317b7e29356ab22ba7981023efc7f05f5f5a03da5abc58337834e7945a56f389313c6837979402f0c1a05970382d3242eeaa96af51b2e144085f04
  | 6 => 0xfafc5a294f7709db0773fdf84947253f6afdb11425e36ae0dfa59c978baf44ef7ba1326cf9dcfa5801f064434e3ffc1525c749b3800c5b7b3285a5b281e5b33c65febc4f1034764e4d16fc1dc1aa903ef737104acc03603d2292efba152ddaf0317fe134c46552d380
  | 7 => 0x43ce39af9cd039a679a6b741ebd8790b3504b5ae099a9726060abf0c25ad56035ca820c6ba944ec9a347e746e975ed6d1df1eb17381a55e97099364dd97cf04e43618a72d8221fefa3677e36003668686945218dc6e4b90e4793c57dad9e55971ac7f3776ba70a1522
  | 8 => 0xb32f02b1134d9da0c2f72a5677da1a7936cf24d8743b5eb0c2f0a8dc7d77c6dae59f37ef4a652f46e11865983ae8aad80b75034e54ea34c2040bd818f7e07f736c53ddfb0145b26be3029473b59ee650a93c58c93bcc4a75ce12866f3df7da0452aaf7963f4aee0e2e
  | 9 => 0x949aac66adfba9c41146b569b678f1d7123550ce236cae2e041b8bcb795d4001f18fb13cf34ce87ef44e65b0bf55522d62ae8f50f60f72dab51244a18793775d32f9f20b46c680fd377e79018af5450a35291fc3da004d8ea52d71ef6c7fd88ec7d89faa04aafc72e5
  | 10 => 0x9d8c2b1fb6e818806157a873e84cbedf1b477a37710889968c236103d34ccd7e31cad649083bf958ed6d0ccbe3026f6d558b76b8e77d9635d86d178f8a5d6238c24371d1fd1e10a0157aad0aa7c914dc58206aa80328cd34305bd9754f450ad2cd5dc5a3985566b0e9
  | 11 => 0x45b6447bd890b9e914e8a5d5776dfe8459b3947085a816bb3f420a431310d87af7df1ed9bd01027791266a88dbf413e4ee14d06745be89e95244b5f79c619c6747386db7c9e323112c5f5fd479969853e86502f6dc4c5126805772df4393b0bf01ccc98cfbe9e1b863
  | 12 => 0xf7d6d39cc856d35bce718f21f96ac2b04e90e934a65c82bb8a0474cca65de83f618f652793a0072608ba3bbaeebf05dfb49279c52c0166f751f8299de2cc8257034c0480b5ab45cba964fa1f0bc1833dc333267bbaca74d48b2c7f08ae4b3211eb67ce1905da8b9252
  | 13 => 0x33f1448a461d9fa5e46bd35cb1dd51620c79e1e05d4f6a4913b7a673072206cb52362154abf7113aa8f6a8932c0fedda81a13c3c6f015ff113a0005da5e23fe66641bea63f2aa877c3c05c8b73c6bb5440febf65b8335dec10a5d85f87207e4ca5f53fffffdb57df7a
  | 14 => 0x4ed6bcea52286a46ff2e4d2d951d79b883c809af93cdf250606612f4b16a486376dffd0d66404fb57fc5f81184915d2bab3b6b065e6c0e90275918186e07051e6fe0833f6c64189a9e68878b8b063ce07c94e5860f4108e8608b19d924816c884906bd30c0a3f4025c
  | 15 => 0x4245e37df0c60996543bbe87aacb65644b8249b5283ff620a59055c9a04b5d169321499a7d47d6bbbd39e89a6588938351e0d0ba8b0c7064c3ac6c5c7e3639ad3ba8ae918904da112677900a311629ae29f8f44d0a642f8eafb7a9de31929f64e96177ff24b0db76a7
  | _ => 0

private def denseT0B46 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xcd592479ca4ccb8c7d8d41b4bc35ec6d7be0a4ceb13a75f65bb98cd1241b5b8dc701f698fe1f19dca8b374950b9fd0d576a4316f425006cebc7f798c6370866d6f64d385150e95195e520018eed98b39aa267c002927afa180f9859aaf7d86ab5a8363db037fc53e2c
  | 1 => 0xe7efdf6b34953ff55e1f4d9d8d04ca25851ba1ab1afa37080ba1ddc8c3ca988dc838b970866389984fa8d0ff18efcb35db760df31316f324dfea0e243029d45139f001f6072138e515b15953ea7583368c9ca5803cde93937e4f0e525f8f087ec409fcc16b4fa67cc4
  | 2 => 0x9fc61b44ffb463946450250efd2289da8376accbe62c322398ebaab937da07ea63b270ea9560d9d9d734301685136979849ad3bdd4f22f86af84603cb23b8e727fe3b1c501d194bda1fdf69d592815e227c0ac1188df158085e101c98989997b9df70de6f40686641d
  | 3 => 0x7bfb0509ab6d7dbbee80e7c0aa56b7eaaa611f5c8ab4d25bb8c5826bbf01224b36f0cb7abed70daae226043710e95036510439cb293158bdb9b9f2d14729f2632bde820d31005b06724a0bb95da7818af0b5dd2cbb4cb738f7c1195e5c74e1bfb22e37b3c05c7dfc17
  | 4 => 0x6ed027be0786b6851dd1a32bff9c19a96b642f5171b17aa84a9281f6ec100164b04c3bef9bd02bab82a09276b57eacbb1bcc9979b69bd7a76e28faac499056d4e0ad2ef6c657aea27504196ed94f5377ca3f5416a8e7a85ad9ef6fd5eca701bcd70643b62937e1b39a
  | 5 => 0x47ef3185738dbd80e78524fb3659d340ab507abde0723599d9bf0281c17070b1a2b0fd09b68373d385bc85b637a6a8cfd70029aca3f3ed24ab4fcade6d690d36ebc612ec092bea1eb8d62f45b6ff5f231547488a86f35936709b792bb5f25f559ece03afb49076b69d
  | 6 => 0x29162ee1aa91f72710f5d7dd1c892e16d7e86183e19184b83f53c736a3e6fcde94fc3b13e9ab98839f78caa08e6a6ec42b78ccd4c401cb0e515a1586e42844713e710915101a0468d7b1ffa4a1f30548e7f09e750992b5e1717f71d29ab9a3deb50954689bef145e21
  | 7 => 0xa3eca73977a210480dc840956d9030c721d9bb27cc48b0304761dfd19db69b81dd46f7c84f8316d52f705a8c122966b961d25e194dfa81f155846c21414a3c06a11f856033122f738a1736291f5af0a37e9a2ecee016cdba7ae2035bc51d7cdf8f222c200862b0cdff
  | 8 => 0xea8d0b8543a4d025169e51389768494a957d38faf6c0e245331d27bc5f7e4da231a916117e1b3492f23cf278155e1b7b05877c9cee0fbdf1725a6e8e08fa6a1a86ec92b64159766a109278ad6a108d1fa06aed992fced0b215bd9c7c898cabd14e2dea2f7c20b8de6e
  | 9 => 0x836fbc5e74c27b8c7af6120c3d84b2c263e92f4d5cf819d9b4a1938c656f8566f81fb61ad599de240e67b43351e6c75c2081b8a73887253719725d75dbe9dffff6f43e8c6b0a9936efeb46eb9a4f1fff1338d8d671001e2402acafb544a24b1d3beb422345ee1d7dee
  | 10 => 0xe2897fd38ec00114959234ac0751e00df8e18e789260f57b71162c87c342f957235e357f77ae6c1a63b844697deac917fa3895c16bd0338830af50d0fe2481380407876ba908a02b591ccdbec5227818df0a7ba7be7a6a49d202eaa77ab9c69ed4ea4b05243b4cab1e
  | 11 => 0xced3813d92cf5f774ae50ee7e696a991fafc8b12ecef261d088db82a28041110d3fa32829cad3f7d7e4447a125a1f57a47b64a2089aab90aefca0aaf8124d39ea693f109f0a579fea056c4f6786b8ac6dd320aa921bb7a825415464508c719302d0bf5ffd1223a86d3
  | 12 => 0x2e206332520d0e231c3e4bea2971144f35cc81572c09311b11dcf68deef78811cd46bcf407458e7cbbcdceaca18793d971585b401d432325e2128f15d8a5d60c95e158692d863093cac70d782bad54a7a4f077b172f4590085cdd8c1c46bf4cee5eea9118cc818e6e7
  | 13 => 0xf668e00e9a9cae63840e3b1005d1c12dfbd8244a296ba9c37f5b92be7a3219751ba3786fb9d5e09ff56765c39ded32e94b5bc611dd9a5aa231532daad35ce739965aa101cdb9f9295328b79537c72d1ebea37ee8c01e011a6592b4752d26412beb56757e92e7997cc9
  | 14 => 0x5e9a1b20f246385307a23a7a15bb56ec529c23abea116a21e87855c4f7cd1e9bd497a029e92cdcac5de7b9581d675c3b3dadcb381054c17703fd1b9bf4daf82cbf73275b929c4e760be89cdb8f45f3407510a8f1b79a8dfb30bd14ae94754b8a3a09640470bdb1583f
  | 15 => 0xb779647a1107d8bbfc5b9f76a99b81480f10f72e213a3cbbb019556724b7b08c852770503c3ea3491b3faa6774abfbaf52cceca59977aee7fb164e44897ce871697b9d52c9dbfb82ed5087562fcf9961d73cf1e90d7fdf6c78947dc6c3ada35256d12724810fd527c5
  | _ => 0

private def denseT0B47 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xb93193b87103c752c50e69d0d2f68a035daab09e1e4f9676364bb25fcb29e41cd7c8efe46ea252c549810cdcfbf07b3e0001173fd56099ad5b3692e444f3e69540b9b6b953ed9963a904b7209ce2087582472720eedb1c10aa4d67726bbc0cc6664f68221fb6cc3323
  | 1 => 0x85bf7b1de42fd350e2d0e2f869cea37433bda2454dfd2241df6474171cc91845f19dbd52fdb4721876f9f7b966cc9424d05a77a1cc9b2502bb6f9e8763d576c0344d14800aa10ce8679500002a8dc20a739370fffef10d96fdb7ab0ba1e7f544ffd20cb3807979ea43
  | 2 => 0x97ce30704336b1bba1faad1c8ea7e8296c9bc5a17184b6522c5c401b35aeaca2216c5feb14e5f315463db4c6c82bfc815fc35eae665aa1ea49bac6e2079417c586cb25570ea7ee12272eb6d54587ce95845dc6bf2b8fdbe11a1edd1073d74c1af31a3e35fb92063ca1
  | 3 => 0x1f1d4b8718ec83312c89881e38781ce33a1656492763cdd857e8db83a3cd8f35436d78c206f1b2cbcdd664f3fbccaa0fdc631363a4c143048bc6087bd5daaa68a253a13c69d064e8f2a62fb972731fbd37722da7aefc01a942006d40c4091c9cbd993072e673ba9fb0
  | 4 => 0x4e4acb387a3c0467d28d66bbfbebfc38f7a1887968032affd0557ed729231a476a4a49defa97fe1278f0d11d3a6b8d6b3c579a271df2746c39fd2b99cb44dfad8504b63730a44f8bc7ab25f67627fad4a5ac991eb8d286f6b4b21fd728e6327ac593cf2b60c3df605a
  | 5 => 0xf84bf61c896060da05e411f3bc72eb1470342ce2dc14d4b48e37787f5a776599d1f96c18c8e9d06d1362fc345f2f4a50fffb355b7ea7b091368493985840f13e6366003e67e7a44c7bbec7ad62acd90ea0aaab2000fe9c3ad8b5fe4f1813b8d0503ad48e2ed3b5b882
  | 6 => 0x558f057ffdc23bb370a3ece391d9e1e52da3b2903ab0ec71dff4761f4b5cd32d73543457addfcd14367e77adef0711646d2f5a70c5c5555a7dcbbc83ba6a9329bbca6d1e0ad4115c63101b1af2e2255c27a1f203d91a89463e3fd312df3c71d0a9a6742fbcb5c53471
  | 7 => 0x448941675cc9e39982ebdaadd9dc2ab7f97d45915a2f5fff2debd62cb81dd3318d13df2b8b13aaa66f1e2105bbd086bc653557a1c6631cf0ea0a043736a2fc41bcd5c902357588a5bd16d6ea3bd64ff90e9e8292ed0bb036be354aac91c15bcfeb4ebffcc8e896b7f0
  | 8 => 0x10fd826ae6bb879e6e8a43033fdeb67d0200278d855c9b7ec5f0482b2bf366f018f160ccf1a21bcce796326ceb3b442bff938b8d8423b3aca1bebf5fefebae06fbda55b741ec15ea7292b72d2c06323623623d77a02467a5daefbbb5d6631d7faba62f94e23dc8507e
  | 9 => 0x93f661ee525bd43999a4ff40eedb196ec7373cdd4e9b222ee1f4f18d39ee2b0f3d3c438d70e7805b15bdca354252387ec85040086c05ca12de412aea84de691843e39efd4ecf74a665015359e5a1a49da90b0b194ba73688de92af99025a20a6b55d1087bb12192d19
  | 10 => 0xb5140366c8e2fd71076d223ea55a6b13939f3f693930e9f95b88bbb6ab59b90830590c60a987c589e4b7f948c9d14242bec66006c9f94932b67d4ee511a316c0e20904254fc31351eddea35b114a9a1301cde200f7fcd64ffabc9233987acf3e9fb925618cd60bc5bb
  | 11 => 0xb3e38befaba500dd44f4177d117788af71f4a62519f64d5e0a7076d1e4e2071c09fa09f0767bb3b1370eabd8a2a2e1d3ad8355baf7f8de8fad61ca01c2bd3f606e8b3d45027a9a87edc8c62d5bdb393b82eb65b6dbfc80e3fee124f9b3b4fbef63fa9f1db6e28358e1
  | 12 => 0x212bbfa593fe21214936715adf7faa22ab4489804a9949b31e42325cfadbc81099367ea192f320e3a2d197d192bdb369c18924afbecae88c6d217963bb3d37776edcc04714541bb2a984aef4c65d2fa25002c4103e67f176d763343e0c202e237beda00bc0218ed126
  | 13 => 0xbe26714e93b739971c0e9d449d602913b9db74b5c498c6c6eea1826d96438aef1ea9b91181a65bbacaf763b474b1eba65fb985433364dd2e467f71bc7842addb32dba1dac0a5b193de9e3e7f36584c5edbb36179e21b26a7f1f498c510f8a36114d10e532f849cec4a
  | 14 => 0x5b417ae7e9115519a170bde2a07c42bb19820768b6434a5bbff36f9d1229ce7fd2e0715dbfcfeecc3748369ca3768d22284e5eb8365774376a9a16b0fd2730f41daae736a227a5fad4b00b6701bdfe5789c0314348537c96fec1755a5a7c763e4308b499ffc69b73b4
  | 15 => 0x6321759c29798c24447cf1e12dbe3b184b45fc920544bf199cb84fb5d75cb180aabc6c18b911ad82736d310418e6e182bea37d5f2367588410e7d97696e18ab70c9217941c231fd1ebb3d4bbcb2ef46faa4e0413878a8b570fcc047ff39b3fd2dc03bd7025e394cae6
  | _ => 0

private def denseT0B48 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x8175e78eac9d73db3ecab532916d1ee00a941945bd4ec17ae5f288357ad28cd2e1365102db947e870c8db0d504069e95353bf0b9bd8f09e6eafd86359e1c1538716ea72a17c30d795843124220702c43f074a242b08c7fbaf1f075f806ad74b4ffe737650a00306ee5
  | 1 => 0x851da33c156e42ccfaa108a8d22c8dafdb2af73405c27e549f53e84b35e4d127234638b22c89860c189a885b9ca45f122008e976ca86057436ce9fa2783c20777adca8d6ecc06a58175b22fb9393f0d1b60d6df499485209b28a4a826cd81dd8bb1ef4609ef462fbc1
  | 2 => 0x6590adc41ee4f8e70e84a21beda0f647cee33c15dc7564ebed69b6cbf355bf9782d9cefe4c32fb6c7abd4b2bf7cd0361bf44656c41590f6ddbd40400492086358fd94a50e1aadc8aee3d128872adaea32aa62fd218b1f3e28b9d164cb7c6ede4716c451dddc38a61a9
  | 3 => 0xb48117c1fe8da074085b871d261ffe0b602b264b078d1dd18839ed4247a26f28945359d6ac320b99da2894a716259e56d12995a5c666c86ec896003052b70571d08c2499e1dd8e6832d5516972248030b4f853ed6c3b35e27c1685dc3f4aed937ee4d0a7380ee0454a
  | 4 => 0x3832171ddcf79687755fb6eafe74779459abbd237e42036fea179d17a66f0b8c47f04f127cd68f053ec6ca391c43995643940f07acd740d7061d79d4c486cb3e7c049a0ad50a7f7cabb8c10a5566a0d33bfbc513d82985c700995329bf5b1cbf132b0bd58ca4bdb720
  | 5 => 0x297dc57452424aa7c92451b0bdb7bacdfd3998852a4a584a5a46e98dc3eb1da3ca7cf525824f8fdb6bdbc6c5a129818f4a372de74bc5e29d6a9f8da47b766d98f85cc389e455aa9e441734f002d821cf1a4a1a90166802dca652f3f7b350f9ba413c21980800ca4796
  | 6 => 0x2aca7a0f3bfc6cf43d73bea019cedee12244a70758f955639a51e2e4ec553ee1d4271198a9cfb8ae02978cc60559a4a3e372c49680e70c21882a38a07ee73d6f2583d2b96c02d62fce1779afced38129f732dabbdd5215f8d0b444ecfd4e66b5766ff6ab4d31f4509
  | 7 => 0xd8acaefaa43d006a56da2ba212825b5a0f3001c5be579865dd454928c72f9fa042e5ed1dc78eac3c9d139fe85f892f0c17731f2873cf66d2ade43b5a47c5b94a06bafaf73393efac2ed32bf30e6cf8e6aaba341f9971e9512bdbbbcce8da0927ccd6e569d2fd55aa8a
  | 8 => 0x206bff757727c51a4f27941918068bede8a62849d2bad38769548def43acea05711938bc96f64543d321a9570c355c3d49eed60fe7bbfddc96dbcdaab823f23d293fd558f826d8d4421cbca6cf5bf9f9eb67f488a5090b6afa5ae2cdee916fa40c35b183f24e9ce1b4
  | 9 => 0x30e1cec445f0d84723d2ef213bb6279179cc88eb14dc27dd49bdcae3ea350af40e5642929060346e520d8e0159440348ef010af1c998a1e479c5ab03e4f1eb1eff640c9c107f308ee575afada8e5c9d1c9dbc266e0ca76050c402069d4a264298298f0c1b3f8e0975e
  | 10 => 0x8acdaca08c3d0478f2096b6c803282c6857981cb8cae4234f9c2bd50f8260a016d814aae26ed2d5fc74cd421171745d53681628e998b5cc5be392774c5d78a1d06bba591731b65d602a067ac3fa368ef345dd5cc3e280f0a0a3bf5faf81c174368cce3af5bd0f3390f
  | 11 => 0x990f8a8e415659b207f2fd188612117a34723183992eb2d2129ea375a706626890bf8121f0b003b27fae979f342e209c521ae9191088775b9a2c73fc103753d292504e4b5e3f44ba5045eb50648711acb5fc94e41a7405e23940d2d7bb86e031fde26283bf86ac4b71
  | 12 => 0xc84df7058c4402e7845c97cc82380d475efbc3d901ea3240af6fe094b3f82ef1fa4e97f2d9dfd9943e9d5387f2353701789ecc67d01bcb6a0a88cdab8c5c4a1a7351bdf351d9cffce08f6656051078953caaa2dd446430471f55d69b2f4716c75ef519325047404334
  | 13 => 0xd4b53fa0fe7a78bb995dca1fe21bb8cff366481c6902055a2a2a070202f302c48dcee01439b7266f2def7ba2e256abee5260e20d92134690bd968a930e37c828c097ec82a7b6130b2499f057b3309b3e59d5460c39dcbed7d233297fe3fe94b5dda0ee02bc43731f47
  | 14 => 0x229bbc1481f52d9d77b24c83c6b44787cf214ea602ebc500f25d45abf29cb08fd783feae93524cb48aa2d7b43aaaa731ddbed9eec67f1c51ee83ff6b5ece79559090341b1c1b2fba5dc60abb14d24fbe28ac5d7d74ba01b21edaf39b850df25eea1294751fd7fbd3d7
  | 15 => 0x348e4d3ec7d5774d124021ff007db049a0222d3741ce7e88d2409451e52acfce6ed57536de92d9f03fd58fcd656ae0798672fd12b6d97a513155b32c4b4c506919b668c92b3e5f57b5daeaa3455cf55724f782dfeda8fcf685bbb29f95678af4d66960f7e99fe98c6f
  | _ => 0

private def denseT0B49 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x4df97bb4533b228f5bb08f4ff433a698de8cb8ad8063b77527056491703459ceabc638529699dbe2f39586b6e41b4282e7ce5beb840ff5d02ef2adf3906489f2793374c9a9ff07e3b0f4574bdbf809d7d9531268e0940c32002af3cc018327b9118803d2b345601d0f
  | 1 => 0xb091f452776e073325c2e8626c3d376e1d9afba0727bed0fbc56d4d11a20877f94ccfefd57afca77740494fe8a65ab3b1d3d3c4ab751a7a8eba772fe96e35040b4076fea429ebd5a1fb6d3c0047195a9a0ec76d3aefce13af62a403b8c7644293028dd4dab546afb23
  | 2 => 0xec645649f59a2416cde609ee2413b2bb63d4e23f1a0409dce5b83577d735cfef6950a71a456bcf356adbf6eb38fa13345c5410b1ec03de64d75af1ff83463d3b452d71bfe5b6411827216882910db74c294809c8efa3faae326c904f7b4f3639ce6649e9ddb75a6d78
  | 3 => 0x30805fec498fc21cce3f9270d3dda51b2696b739cd0b3636392a1c44ef1f79d31608931f0f10b0fde33b5badc2d3829c042c46cf1d019b0bedbd64c03e75ffe64dd98ee5a74365b625e0e36562ee78e2aab36e5a6cb159ab82fdc71cf785e68f79336f25841c7b726b
  | 4 => 0xa847fb172b94d2607972a8f4e36d2043dbce56f5bfe73aacf8485c621c97cfba94f25d5f836b8abf76f4d8d877a180d4b0c8fac4999ea21a9d90105c3afaea3932e63e82a42f81222a55ef68b98126e97694f6e7af054abf06847d20565b6eacf688ebbdddabd2075
  | 5 => 0x63bde67880b68ca4ef6502ddf3a4ded2afc1f590cdffd962d88535b98bdc16f60cf73b9113a39db01c2f212ef3bda3af8e6251a0f752f0c91f151f5710e253c9c5b685aa8298c4c7b7580d031f6d7e8e5cf0e013051bb935aecbebb566bd3ccc85f70142d52e918ed5
  | 6 => 0x2aba3e00fec3c41cc2dae33f9678fb0c93b2d0f4833620553a681278fc94719a86d0f75a084a77445a534eb951b39ec038a57cb716025d9ced373f5498c8ba90fdc15635c014d8d39bfd95ef250529f8436505e21dfb699153ae5443bca8a8e9c16bc1f04b9aa051b2
  | 7 => 0x7367ca7813316ce91c180e36c56f2850474a25e314475103b9258125d769405ef47de30b354d66a19a92af5be1136b18f6df702d8f5443639fe110e601a36032ddf8479cf36e6d02097cc2df1fc82effd8c3ee4dda36f03f5d696c2768aeea6a0c21716f9ccf88ae2a
  | 8 => 0xa2c2fd07e3dd9f0085223b5356283932999bd1b643ced192f16b259125c37bab66f058a77caaed1a9ee2e26531b696c2ad10652ea059f50cbcf9dc290ebf8beb859002895bf1f5541da50376834d133b8273ef0d2dc86787cf457862717eb9bb3ce79fdb124e31118f
  | 9 => 0x6e0ca71d228e59af583c540994e41cdc319c971e25f8d7ea24c7495ee75e5cf55ff12ffa614f890e62508a658f8e94a317a549deb72fd2775b49f28eac33de2a01c229fcb85ee3477043b9f9a548857cd5f7cb5bed9035dc0d13c0eb9d3ad91dc0cb8b699f24e38470
  | 10 => 0x5f72c413c0b2094bcbe19a38452ff92ecfc1aaa337ab2dcf71171bc82a3e056ba4999c14fedcb552c45b1acfa1b28874e46a16aa491a0d79e588b8091638497f36147b9a6c1383a37d4d5215215160c9760b0e8c695ead5d9375e21560f121dfde21859a862c8620cd
  | 11 => 0x9e8f8db30bbcf72110ea0951e476402cccacb2917feaf9229081ac69a6d1c3c3a55e091c0ad1a8454c398b8b95a5f17c996d6d07c33e8626f3198bcd9b6cab23a0190924fe1a472f1d38164b4809dff77428230cfc9308e7b8e23ed7547295c4fffb38b07c41662aaa
  | 12 => 0x4ad6261742b30d861a659835d68b90566312c408c46f4a748287b152b95467cad4f8842e21fa1a93d7c3251ff6b2d6fbe544828adaf29c1ba19d39469c673aa806d76e422fd9d3e923ea66f30e98cfd51b4b4ee06c10034e04c755d41738ba5b1c1bb124db0a620801
  | 13 => 0xdacd13e023d75dc50294fb26d70688638f88d878615652503271f06e401ca64e8ca55de43c1e38eb62cb1c187b70513bcff0616cf3647fa2fb903fc391f9fd32585bded8ad179e1a772015b3d7f075ff9ef18f51870a7a309badba8e791989a3af369b4ddf38f0a539
  | 14 => 0xc6749a0b52830cd22dc78b72a57da9cbfcf0fa8058280f7c8813eb261132403b049367680936c5f382fcafe95135351cebd3607a5f928a299d22187b4aedee9c6842d5520eb30a094ad5a78ce4d151f99004c7c75a4095fb1a1f23670784b51caf42905e216c893767
  | 15 => 0xbedd8c6b672a193bf97eaf7ebd139f7b8cabed846510f4053e268fa176b59f433128f0b6b6cb39387694f219d01081d13262e976d919c7dec7468519bebfb27ceaac11e04930b81f7b4676866fc65f8ea0e04cbd7d037697579f2c38a557d4a9dfe81aa3b59ff582c5
  | _ => 0

private def denseT0B50 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x30a202d2f4e015f37853090f8ad5e4de43a2ce810201c092731bf5ffffe66ceaa05b7711f038270f2232786645728a742991719fc28e08acd98478049cd23c503d7efaaf6bcffa60c627de0fd8a2da12f41c10efcc1f073b10e183ac309c18692a2c6cd693f97623b5
  | 1 => 0x582e75353fb7832b8249a429601f2078d66ae385947f221907a096ba5085c39b50db490bfce60ee2e3df7dfd64d6dc9a69a576810c9b68eb79e1b3b81147dc19e8585ac07b513a68874d278c8c8e40a8634ab68e572668c16989c1fb691a52f83c4b47861895db941f
  | 2 => 0x7aefcbb299a0441ee0aff270edfba9fa3b771e0b80e9c1503fe35133cf66a03ab308f2739086818c9f3123c7d12370681e8d8b1a9e4dc341300a0735e0bc298352125e864ce01844e59401ed44b624211fcd5dd5daf991eedcdb7fd83e27efa270711bb30e161372f8
  | 3 => 0xbbb179ec483dede4fb42c792f2168bcfb2a42ec8b7a727c1ab23b57ba2cfd9d1290bd0621e2a984b7b4f3132a46bf32891387cf02e47c035eb1091d76257de4603f5f7455fb66ad11c07b3aa1cdcd4f52e443abb1eee6673d746f8c4b40be867ba349e936f2af94632
  | 4 => 0x2429a17f549aed72952f68c599595658ed278a5c7d6dd96da0b7df1a9df03e3e2c9ea8d533ad8f56c1290fc1e46fc8eef660e0962091820d8197896fb9430beae565ea92e5c7b74bb2a932daf1b6d3e24719bc98392b166f3406b814cf4c5ab30edee73ba768a0cf10
  | 5 => 0xa953ecc8b76eb0ecf95fc30b90af7dcc80d71b20c210f40dec0c6c5cc2623152fce7d1cd0ed1048925dec2e3764fdca4cdd61bf97144b02d916b12325fdbb6829ce68545eebfd4a57758d29c1095790ad39503e265feb9a0a99de95cc9f429606e1c5199a0921182a
  | 6 => 0xa8afc3d7d833a5dbc7f1200ffb32da629d9ede568baf012c2414c68496fc449a6dfab7bd71712e15316fe9edfea21f773176bdaa145295fd03660e2a98ee37dff4603ec79605518e07e1e6d7abb9b682572634905b708dd07a0bcfbd496247c7747b5a987a37ccc319
  | 7 => 0x8185f77dd79ce8e8c664aaac64ed2ba9e2cb5343cb183002f17973ff0691cbfff76f81078c0e2080e0d149c44af8602aacf21b19b864657a0f45793acd2f6a03c0f1766da58d8a4f91bb8e2097bf34c06d8dae9dbb462b75c8c6d8deceeaf82c1a37c8cfe050230ed7
  | 8 => 0xb245cd6119c7a02acd832bab0aa977f8944f5c234459cc18ad078380f5ce9027e524ceea37b45db45bd1b66594cba19ead1a517cb60428b3015c121477746fb7b98d511114fac4cf22320dfed8d852dd861f3d403ca1b402a8153390918f4e576f0a7b3a9a75b8876e
  | 9 => 0xeb7e0168bc4bc3ba09042b49a547a38cc9840fd51bba2c23b6b9da365de384495f2b55ac2ef45b343dd98a81b8e57e1db2ef980c37d988dd2ec2eaaa075d982403bf7588c87b911e8111208df19caa37949b5f110bc5ed77f708bf7b509ec07f6d73f3274b5aabba31
  | 10 => 0xf70f655a1f0ffeb1fd99cae816bbd247369ebfcc0a417f278663c514e796dc2c6bb97216a2804f4fdff0840664f3ac54993a2f86fa46b1052fa1e5ee0fc7b60b404e6a7d55943d1189a2c0e9c71c6c3aaa33bfdf1ef8fec30437bc33bf492697a503b5cf800a918a1b
  | 11 => 0x6ce15743aea0dc26a15d3e013a587164ef13477e779cd59e494d57863591d82483ebb0c3d0b68cd9500761968b1120d68aaa082aefd77579e1410a28e090e533a72e7199daa933511ec163137bf9f396f454a207a16347468108ccf4a1779bfe9b6326b1a02ab39a0
  | 12 => 0x60579bef51b022e0ea19dba1019a4d78335530005179f7e437b2b652f7f944488f0183d70167012a14bb7fbd610a55bbd9a9ac4499f02e22dda7c99f08973594683501aed4b526ce73ce4b0b5cf8eb53200ac8a5898adf041b1ef43dbddb219b6a73b1cb78735b56d1
  | 13 => 0x58d1124d7a9531856e1e5d8cae7918be8c6f59bc0db72dcf218bf2664ae08369c620fcc57eb666ede983422a597023d57c85b48c981209ffc7fdfcd718e9d2f6f87cf84501c651170ad9cfca7d9660f03ce10dbe65f899ca1d686694d46bf0446a42f2a480e2349b7f
  | 14 => 0xe3f21a0d32e0f3d3e1e16ba419b19a639ca1f11733ddfe61f87030ca7500c260d36f3b694df6cf3e678fefe429439866e21c309afecbe0d4076efb964eab042a4efda374976b4b3bd9b32075f43aba586627438b73a78607ad7e06bd1c0cc46a705f48914f430aa452
  | 15 => 0x8cff226eec31cb521a71c4a4f86164b00908bf89e261287afc9256bb8b1d3f221a04085d8ac4fb4662c9acefa1b350dadd0bddfe0d958a33854d51cf1d6be5b68c81ab9465aa67691b90abb2f121202898f0c288b2375972d948672a79465759b923aaea3428da0547
  | _ => 0

private def denseT0B51 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x637575a40c989068b237723b22e3f3660b9aef96f7392890afa54dc250af7b77f704de44ccb01fc557820147ad1decc2e8484ce2d57ad5f205b7efd79b7008b2e66e4a78a2234b06ae9f439bf37b7790a9108904fcb3af775df97f0e1d0b7084d49f158714dc541778
  | 1 => 0xf7dbc2b673c1dabd4489db448279b2984626dcedb298e555b5941887ce4ca372eba47aa9648c906d99a234e5798a200c42a143346bd67963ebeacc6d99f01ab787af80d989c26066c09082aab26b2fd59ee9db1727bc6a74b7f51d29423de0eb4af0e2a7b0cc3336d0
  | 2 => 0xe02e5d7f98f3d3bbe263a81b61500213f36017aa161a898078de81bc63d8fd88649a515c435a00d4ba99df7f5114b3f63b70137ad8ed763bc6b315436ac280ad0a780c48de4442c86ec83911416418b115ff46c171ce7602c44781f321550ab0d2ac9bf3687b4b386e
  | 3 => 0xcb486c8f609cbeaeb50e3c70ca30f09236579e5af267b09ebfc7fa66947fc2e2f36e31cda9bf95fc5460b5ec907ad8c198e42229b401919fb317d4b5514501fb82f94b3c7d817816f2bd27cd8f88227d90018c93bbdf57096d63de8b6f4a95ae9cadef63d60502346f
  | 4 => 0xfaec29337b511932ae16e82ae8c9eddce8f5edcdcaeab7a6234e0ac9c730a7d8dc9985d39a26f37c1c05a0388d0cebbe14f4500fd62ef5c293026f90181a0fb6b65c0907e14d769a2eaff32ddb479fd5ec7c88ea7a5760f92af79e1a01e4b21f5d384b58f521e3b899
  | 5 => 0xcd0f96bbbf5aa169d75f4eb4fc75569146d48bee26371f44d6ca1ed23242d56df4b7e08458e8456f9cd0ce52cb8785ae311751a169bc2639ba4d8abaf9ba52a10861c1a784a2d87357417f0e13f3d2ef83900edc868f51711d757aaa0ec47ed36e33fc1540ffe8ebe
  | 6 => 0x809ba3b162b676336dfd0f898cc380357766c93feaf92851cf14aba8c165047c71b7f151b22fa07dbc4b864ba62c2d28aa72805d15edc7d9eccdf6ccdcf4f7c93efa813b03633ea0e3deb985dedc9071be74472ea166cbbcaba65ae88a4f7cd240a6fa321117435fee
  | 7 => 0x3fe85cca8e7d5f419f9d2ae145b343fda3a9d0c3fe82c8c6f350ed121ed42929cf9e346a2a5d7445cdaf68b6bfd7ea2129a44220b28acbfbb661599414c589853849e4d05b77aff6cbf239bf5823375cc4f96b0c045fd2d40dcc2a5fa6f30d72add8b9f77bd7212656
  | 8 => 0x8aa864ea05c368db9abad602b33d3a1267308756323ea019958513c813842ba1678e131d510102dc0daf7297fc80fb35201cabcce428efeb14968a8078b496b876f86a7734aea2d6e4887b15c59369fb1282af9b821aa80cc87303273aeb4d9552ae5e2513c83aa546
  | 9 => 0x2a69e65a2d3d952136c60d672420cd3c89dd32c783e738e2179371318125cc02e747376e9a256d6e37c7841ebc6b3151dc2e7870e125a732790bf648007dc262b071d39a8253cc8262e316ad4b95d03e226c860fbfba3b7d89d5a1bd549d4ca41a8cee3d3a2144224b
  | 10 => 0xa18182a3cf9ac48311a804e5d74d73dc0deb1a791bb12c3cfac685f18425fc618ebfcac4c5f2d8496992b85e0c63941b75ca68935587b94946500d753312451517367cf3d1a34fe49b6fddf37e07f39356d0c8704a1f76ebc3b6ca59a84f89bf7cbdbfc48d7af431b3
  | 11 => 0x816b4fd9b918acc4c7f0530e7fd9ab2bae69f042870632791c70ba3014fe8486a9dcf6bcfee26f3c9110a6426e9857860a085cde69bf72b34c47d9bd7862d6a786cf2367f070c95a3c7039cf97d20b8a3959e3782c697a633b4f27e666c066b15da22b3a8630f8afb3
  | 12 => 0xcd1b1b55e282f68b3cf8d7a6088bd15f2d905464358c16e48c382ab5adf2127e315437e807bfa601eea716c1075bfcdbe569e8cd61f4a88691b61be4b7a46ad57e44968e93d68180aea8e142a3f4dcf26eccf48cae5eefac8f0236eeed3fe9c69c24093795a8637656
  | 13 => 0xadbc7d63c7f5290d9714ab0baab350881d58905d2fbd6eb2ec534b90cf8aaec6bf204c168310cb5ec81797a0cec3c0ea928724307414cc227f06bc02b7e5aa7da289702e76a0c005236a46fe6056c5065a39526ffffb1f8bbf85c305673e727af111ede329e4676067
  | 14 => 0xcbfcec7f201e1b407f349ed517e3cc3d5ffae17140a6c968786e750280a7317806c9a3403020d13965bff68ddf0b52cbfd42b1822012443897edbef8c95dae2210090bcf1f97a838e7b89d179e9e2547248d93a7caed96744cbea008827d3d50d8b8b992fda2e52dcf
  | 15 => 0xdf58b3cd54d1ecbf4c3d13364f66bde5f6ef81a13de8a2d4929a94b69f9d6312855771b892fa61da033d0afa28dea9577a0c08bae12f58c200d1c87e0d16a014ff662a84c838b929a853190fd25a93ecba5a07a69d2f4cf3bad1f423de242d2dc85d0539e11f7d48f6
  | _ => 0

private def denseT0B52 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x19db56915d323efe240c2b14080de7a2a9ab2dc7dc4cfeb3d2b93d4aec8dbc7ef92dd346a7aa907d655f1f5f1b54431ce150d2a1fc112a17ba6dd6377cd98dd9bdafc6f9209f6b66642e60f73bb763468a6e4cec75dbbbf2f0e3138309e7ea1b1a930277186e446d4c
  | 1 => 0xb9f8c7578ba1cc4c0479f6357bbd0afe2939974bdf47bda22b51689cae11c0dcd0ad7fa72833e63570883c1abe926ed97f6b510158f711203d8c5e3ac8711318f63f91b76b124885b0fc2596cbfda339354bbbd8cd3e684cab267f8a2ae82b594d5f7f307dc8c68e0
  | 2 => 0x5a466daf85fc640a90e4a618b1ddfb8ce0ad94653f5c7560d339567df944a03a1aa9d1c23fd97e91057899ea0855856d7b6005b412dda991c95f85fdc0436fa9f145f410df8f803feba66045a4a6350c5083812e1581af19cdc0cfef9d539c196cc5445b4949b12169
  | 3 => 0x45a50475b2ab0b79fa22fc43e64ac8daeb37b6924cfcfbf533f2d8c402593b8042cb5cf7fbcdcd1b01ca1f8d21cd5140c2347a74471223e6b5dcabae5fbe526fb9b594ff003e061e156183d93cc80d9e8f086a37ef98a0ac440adb2be8c626b39671a930169a373e5d
  | 4 => 0xe5f1995bfbac3b83a4eede94c833707a3b2f7b79e3449e436843c821855b3e62764ae4e1c101fefb2426c030054515d3373386e8e32f6e73ba8cdcc76dbeb45be7da98dcd6169712da1e38d24442b51ad852b100b3c6088b9363b1372d59ba2bb6b152fae92dfa6d47
  | 5 => 0xd1deb28a6cff2af431cf8e57ff97d91c8e9d45ca344a73d78d202377c5dc27a3196b149c2cc010c84d23f3794d6ef7e5e7ab5cebaedcac352a5605dbeba2a808ab845928a80eeeda59c744c2768d3c60d40b3161ff7ce0e269c059e969b244f4be03b9976b9662e6d8
  | 6 => 0x9d486def3827910cfd29efe66928dd8ad5288e2ed5e9b8c017cd2bbcc214d6d0654c14b99dd780135760d8ca260bffca8f9d640647f80a84c4c3b68ea5163a7956c8b54d1edd0f42952529f5646f0838690fc99f0b26461aad62a5070e9ee68c738677c2d12c4495a1
  | 7 => 0x6d506f8832c621e4a3960b2398a4541d5432bf1c33130ded361003bb1b54a29bbf14bd84223a2dfe385e47d2cb77f0d3578e327037ef175852cbbb41cf4dc808b34328947549b55a40aaacec36fbc6b533d992b543ff48eab8439cec0ff25bc11249a6eea05ca10682
  | _ => 0

private def denseT1B0 (i : ℕ) : ℕ :=
  match (i/16)%16 with
  | 0 => denseT0B0 i
  | 1 => denseT0B1 i
  | 2 => denseT0B2 i
  | 3 => denseT0B3 i
  | 4 => denseT0B4 i
  | 5 => denseT0B5 i
  | 6 => denseT0B6 i
  | 7 => denseT0B7 i
  | 8 => denseT0B8 i
  | 9 => denseT0B9 i
  | 10 => denseT0B10 i
  | 11 => denseT0B11 i
  | 12 => denseT0B12 i
  | 13 => denseT0B13 i
  | 14 => denseT0B14 i
  | 15 => denseT0B15 i
  | _ => 0

private def denseT1B1 (i : ℕ) : ℕ :=
  match (i/16)%16 with
  | 0 => denseT0B16 i
  | 1 => denseT0B17 i
  | 2 => denseT0B18 i
  | 3 => denseT0B19 i
  | 4 => denseT0B20 i
  | 5 => denseT0B21 i
  | 6 => denseT0B22 i
  | 7 => denseT0B23 i
  | 8 => denseT0B24 i
  | 9 => denseT0B25 i
  | 10 => denseT0B26 i
  | 11 => denseT0B27 i
  | 12 => denseT0B28 i
  | 13 => denseT0B29 i
  | 14 => denseT0B30 i
  | 15 => denseT0B31 i
  | _ => 0

private def denseT1B2 (i : ℕ) : ℕ :=
  match (i/16)%16 with
  | 0 => denseT0B32 i
  | 1 => denseT0B33 i
  | 2 => denseT0B34 i
  | 3 => denseT0B35 i
  | 4 => denseT0B36 i
  | 5 => denseT0B37 i
  | 6 => denseT0B38 i
  | 7 => denseT0B39 i
  | 8 => denseT0B40 i
  | 9 => denseT0B41 i
  | 10 => denseT0B42 i
  | 11 => denseT0B43 i
  | 12 => denseT0B44 i
  | 13 => denseT0B45 i
  | 14 => denseT0B46 i
  | 15 => denseT0B47 i
  | _ => 0

private def denseT1B3 (i : ℕ) : ℕ :=
  match (i/16)%16 with
  | 0 => denseT0B48 i
  | 1 => denseT0B49 i
  | 2 => denseT0B50 i
  | 3 => denseT0B51 i
  | 4 => denseT0B52 i
  | _ => 0

def dense (i : ℕ) : ℕ :=
  match i/256 with
  | 0 => denseT1B0 i
  | 1 => denseT1B1 i
  | 2 => denseT1B2 i
  | 3 => denseT1B3 i
  | _ => 0

private def layerChunkT0B0 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x0
  | 1 => 0x84210842100000000000000000000
  | 2 => 0x84210842108421084210842108421
  | 3 => 0x108421084210842108420842108421
  | 4 => 0x108421084210842108421084210842
  | 5 => 0x18c6318c6318c6318c6318c6318c63
  | 6 => 0x210842108418c6318c6318c6318c63
  | 7 => 0x210842108421084210842108421084
  | 8 => 0x294a5294a5294a5294a52108421084
  | 9 => 0x294a5294a5294a5294a5294a5294a5
  | 10 => 0x318c6318c6318c6318c6318c6318c6
  | 11 => 0x39ce739ce7318c6318c6318c6318c6
  | 12 => 0x39ce739ce739ce739ce739ce739ce7
  | 13 => 0x4210842108421084210839ce739ce7
  | 14 => 0x421084210842108421084210842108
  | 15 => 0x4a5294a5294a5294a5294a5294a529
  | _ => 0

private def layerChunkT0B1 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x5294a5294a4a5294a5294a5294a529
  | 1 => 0x5294a5294a5294a5294a5294a5294a
  | 2 => 0x5ad6b5ad6b5ad6b5ad6b5294a5294a
  | 3 => 0x5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b
  | 4 => 0x6318c6318c6318c6318c6318c6318c
  | 5 => 0x6b5ad6b5ad6318c6318c6318c6318c
  | 6 => 0x6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad
  | 7 => 0x739ce739ce739ce739ce6b5ad6b5ad
  | 8 => 0x739ce739ce739ce739ce739ce739ce
  | 9 => 0x7bdef7bdef7bdef7bdef7bdef7bdef
  | 10 => 0x84210842107bdef7bdef7bdef7bdef
  | 11 => 0x842108421084210842108421084210
  | 12 => 0x8c6318c6318c6318c6318421084210
  | 13 => 0x8c6318c6318c6318c6318c6318c631
  | 14 => 0x94a5294a5294a5294a5294a5294a52
  | 15 => 0x9ce739ce7394a5294a5294a5294a52
  | _ => 0

private def layerChunkT0B2 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x9ce739ce739ce739ce739ce739ce73
  | 1 => 0xa5294a5294a5294a52949ce739ce73
  | 2 => 0xa5294a5294a5294a5294a5294a5294
  | 3 => 0x0
  | 4 => 0x0
  | 5 => 0x0
  | 6 => 0x84210842108421084210000000000
  | 7 => 0x84210842108421084210842108421
  | 8 => 0x84210842108421084210842108421
  | 9 => 0x108421084208421084210842108421
  | 10 => 0x108421084210842108421084210842
  | 11 => 0x108421084210842108421084210842
  | 12 => 0x108421084210842108421084210842
  | 13 => 0x18c6318c6318c6318c6318c6318c63
  | 14 => 0x18c6318c6318c6318c6318c6318c63
  | 15 => 0x18c6318c6318c6318c6318c6318c63
  | _ => 0

private def layerChunkT0B3 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2108421084210842108418c6318c63
  | 1 => 0x210842108421084210842108421084
  | 2 => 0x210842108421084210842108421084
  | 3 => 0x294a5294a521084210842108421084
  | 4 => 0x294a5294a5294a5294a5294a5294a5
  | 5 => 0x294a5294a5294a5294a5294a5294a5
  | 6 => 0x294a5294a5294a5294a5294a5294a5
  | 7 => 0x318c6318c6318c6318c6318c6318c6
  | 8 => 0x318c6318c6318c6318c6318c6318c6
  | 9 => 0x318c6318c6318c6318c6318c6318c6
  | 10 => 0x39ce739ce739ce739ce7318c6318c6
  | 11 => 0x39ce739ce739ce739ce739ce739ce7
  | 12 => 0x39ce739ce739ce739ce739ce739ce7
  | 13 => 0x421084210839ce739ce739ce739ce7
  | 14 => 0x421084210842108421084210842108
  | 15 => 0x421084210842108421084210842108
  | _ => 0

private def layerChunkT0B4 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x421084210842108421084210842108
  | 1 => 0x4a5294a5294a5294a5294a5294a529
  | 2 => 0x4a5294a5294a5294a5294a5294a529
  | 3 => 0x4a5294a5294a5294a5294a5294a529
  | 4 => 0x5294a5294a5294a5294a4a5294a529
  | 5 => 0x5294a5294a5294a5294a5294a5294a
  | 6 => 0x5294a5294a5294a5294a5294a5294a
  | 7 => 0x5ad6b5ad6b5294a5294a5294a5294a
  | 8 => 0x5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b
  | 9 => 0x5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b
  | 10 => 0x5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b
  | 11 => 0x6318c6318c6318c6318c6318c6318c
  | 12 => 0x6318c6318c6318c6318c6318c6318c
  | 13 => 0x6318c6318c6318c6318c6318c6318c
  | 14 => 0x6b5ad6b5ad6b5ad6b5ad6318c6318c
  | 15 => 0x6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad
  | _ => 0

private def layerChunkT0B5 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad
  | 1 => 0x739ce739ce6b5ad6b5ad6b5ad6b5ad
  | 2 => 0x739ce739ce739ce739ce739ce739ce
  | 3 => 0x739ce739ce739ce739ce739ce739ce
  | 4 => 0x739ce739ce739ce739ce739ce739ce
  | 5 => 0x7bdef7bdef7bdef7bdef7bdef7bdef
  | 6 => 0x7bdef7bdef7bdef7bdef7bdef7bdef
  | 7 => 0x7bdef7bdef7bdef7bdef7bdef7bdef
  | 8 => 0x842108421084210842107bdef7bdef
  | 9 => 0x842108421084210842108421084210
  | 10 => 0x842108421084210842108421084210
  | 11 => 0x8c6318c63184210842108421084210
  | 12 => 0x8c6318c6318c6318c6318c6318c631
  | 13 => 0x8c6318c6318c6318c6318c6318c631
  | 14 => 0x8c6318c6318c6318c6318c6318c631
  | 15 => 0x94a5294a5294a5294a5294a5294a52
  | _ => 0

private def layerChunkT0B6 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x94a5294a5294a5294a5294a5294a52
  | 1 => 0x94a5294a5294a5294a5294a5294a52
  | 2 => 0x9ce739ce739ce739ce7394a5294a52
  | 3 => 0x9ce739ce739ce739ce739ce739ce73
  | 4 => 0x9ce739ce739ce739ce739ce739ce73
  | 5 => 0xa5294a52949ce739ce739ce739ce73
  | 6 => 0xa5294a5294a5294a5294a5294a5294
  | 7 => 0xa5294a5294a5294a5294a5294a5294
  | 8 => 0xa5294a5294a5294a5294a5294a5294
  | _ => 0

def layerChunk (i : ℕ) : ℕ :=
  match i/16 with
  | 0 => layerChunkT0B0 i
  | 1 => layerChunkT0B1 i
  | 2 => layerChunkT0B2 i
  | 3 => layerChunkT0B3 i
  | 4 => layerChunkT0B4 i
  | 5 => layerChunkT0B5 i
  | 6 => layerChunkT0B6 i
  | _ => 0

def layer (i : ℕ) : ℕ := (layerChunk (i/24) >>> (5*(i%24)))%32

private def maskT0B0 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x98570410420000127a400000000001
  | 1 => 0xc520e9fdae70002add401000060002
  | 2 => 0x41536e5d67200047ca401000030004
  | 3 => 0x1f975de36a10008100000000010008
  | 4 => 0x9949139b270010077401000060010
  | 5 => 0x1ddb8d81ee20020050000000020020
  | 6 => 0x3621abc18b300404a6400000030040
  | 7 => 0xb56fc7498400080d76000000000080
  | 8 => 0xb21a77c58f30100d76001000020100
  | 9 => 0xf52e4a97e00020020d000000000200
  | 10 => 0xc0d039b00670400d76001000060400
  | 11 => 0x6bfb6ce87f60800471000000060800
  | 12 => 0x378f747c05510009c5401000041000
  | 13 => 0x1eb577017d72000192401000062000
  | 14 => 0x2c1631f0b84400023f401000054000
  | 15 => 0x8a7b029e4a28000a2e000000028000
  | _ => 0

private def maskT0B1 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x29bef8c5db9000076a401000080000
  | 1 => 0xf16cdbea8e40001303004000100000
  | 2 => 0x3c30b27edee00022c200e000200000
  | 3 => 0x91820afc6df000431300f000400000
  | 4 => 0xeccb8b450bc00084b340c000800000
  | 5 => 0x38ad4aec0470010ac8407001000000
  | 6 => 0x9c1f4615ffb002021040b002000000
  | 7 => 0xf76b5ba555a00404da00a004000000
  | 8 => 0x26d40ff6b6d008091f40d008000000
  | 9 => 0x372a54b3daa0100f6500a010000000
  | 10 => 0xa33483e6e000200ade000020000000
  | 11 => 0x91d72ccada04005c940a040000000
  | 12 => 0xda508488e9f08007ad00f080000000
  | 13 => 0x7e2fe3be1f5100021b405100000000
  | 14 => 0x755a840c5932000ccb403200000000
  | 15 => 0xbce1524888940000c2409400000000
  | _ => 0

private def maskT0B2 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xdaf46d01da680003c1406800000000
  | 1 => 0x9b65a88b2f00000614010000000000
  | 2 => 0xe4fc478e8700000ebb020000000000
  | 3 => 0x8794094679000003c8040000000000
  | 4 => 0x81d7901ef500000076080000000000
  | 5 => 0x2a357427b400000774100000000000
  | 6 => 0x5c145b8ef500000e3d200000000000
  | 7 => 0x3e56a3bd7b0000011b800000000000
  | 8 => 0xff9666315076400580005800080001
  | 9 => 0x18979a81111bb000000000000e0002
  | 10 => 0xc160aaefcd4dc80100001000080004
  | 11 => 0x1d277bae1f97180580005800020008
  | 12 => 0x2b1b83aae931680100001000060010
  | 13 => 0xa0ff01b48786800000000000020020
  | 14 => 0xd66dd5a8748c880580005800000040
  | 15 => 0x1329c4273a71000480004800000080
  | _ => 0

private def maskT0B3 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x61849cd69930e804800048000e0100
  | 1 => 0x6a0504f5d12da005800058000c0200
  | 2 => 0x6252e19d9c469004800048000a0400
  | 3 => 0x5d26f578375a4005800058000a0800
  | 4 => 0x86ed8a5deb67280100001000041000
  | 5 => 0x39637c04dfe0300100001000062000
  | 6 => 0x578c11279cc7680480004800064000
  | 7 => 0xa79236765d0a0801000010000a8000
  | 8 => 0xa72f9d62aab13004800048000f0000
  | 9 => 0x4dfb13efebec000400014000100000
  | 10 => 0xb95a0996be2d480c0002c000200000
  | 11 => 0xe958cdcdb19bc80080040800400000
  | 12 => 0xedb68abcaa6d280c0008c000800000
  | 13 => 0xaa828277d631b80500105001000000
  | 14 => 0xe6bc418ce9f0c00000200002000000
  | 15 => 0xb8fa220cbc2a380580405804000000
  | _ => 0

private def maskT0B4 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xce36c91bcb0400d0080d008000000
  | 1 => 0xcc38d2d34670580101001010000000
  | 2 => 0xe244242f59eaf00002000020000000
  | 3 => 0x71fd30099d56400c8400c840000000
  | 4 => 0xf55d0f2d6640800408004080000000
  | 5 => 0xe63aa6e1ca11500510005100000000
  | 6 => 0x51b01718dd56400ca000ca00000000
  | 7 => 0x89eae123097c780940009400000000
  | 8 => 0x5d67f035759c580200002000000000
  | 9 => 0x40ffa5c97606801000000000000000
  | 10 => 0x7b823ec598aca02000000000000000
  | 11 => 0x6e2e8284e286c84000000000000000
  | 12 => 0x31c86fc6ba9b008000000000000000
  | 13 => 0x6270b3007b20510000000000000000
  | 14 => 0x2f5c3706b6e47a0000000000000000
  | 15 => 0x550923da20dbac0000000000000000
  | _ => 0

private def maskT0B5 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xa966b6e1c0aaeb85e1c030000a8001
  | 1 => 0x81d44b3740f9311b374000000a0002
  | 2 => 0x915471180d051a411803000080004
  | 3 => 0xb05f6352003939d352000000088008
  | 4 => 0xf96d7024c011864124c01000008010
  | 5 => 0x9f1989500a949cb950030000a0020
  | 6 => 0x3a1e205300ff3da153001000028040
  | 7 => 0xa16672f140f47d22f1400000000080
  | 8 => 0x88d55467407ce1b567401000008100
  | 9 => 0x547866428050861442802000028200
  | 10 => 0x3c088d004083b2ae00403000020400
  | 11 => 0x6d65443600dc32f7360030000a0800
  | 12 => 0x30ad2ac400a9be9ac4000000081000
  | 13 => 0x98b9cfd5c0324f1ed5c01000022000
  | 14 => 0x5b8a90d5c06d3d11d5c010000a4000
  | 15 => 0xe981cb6440f0952864403000030000
  | _ => 0

private def maskT0B6 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xb130fe8480f86d6d848030000c0000
  | 1 => 0x4e9fc5268172001126804000100000
  | 2 => 0xb849d13342dd46d433405000200000
  | 3 => 0x4978fe3844f282be3804000400000
  | 4 => 0x642dce4788604a5b47805000800000
  | 5 => 0xe126fa31108324563100c001000000
  | 6 => 0x36f0303060cf13e930409002000000
  | 7 => 0xb0ba2f2580c2603e25c01004000000
  | 8 => 0xa732f2d400dc484dd480f008000000
  | 9 => 0xd26df0000099d25301003010000000
  | 10 => 0xc738af0300935eed01002020000000
  | 11 => 0x5df33278026ba7223801040000000
  | 12 => 0xc5256808001b08ee00006080000000
  | 13 => 0x19ed508440f8c52794407100000000
  | 14 => 0x8be763a3c0945ab083c03200000000
  | 15 => 0xfedc6ed60074eb659600b400000000
  | _ => 0

private def maskT0B7 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1348207540ef72ddf540d800000000
  | 1 => 0x2fca51c7c11088d1c7c10000000000
  | 2 => 0xd45ce090023a7fe090020000000000
  | 3 => 0xd779caa284e1101aa2840000000000
  | 4 => 0xf0785722087ed5e722080000000000
  | 5 => 0x2ebad5c010409955c0100000000000
  | 6 => 0x2cee81932071255193200000000000
  | 7 => 0xeadc4148000ceb4148000000000000
  | 8 => 0x9139c4c4a75a000000004000140001
  | 9 => 0x2a3549604e7cac000000e0002e0002
  | 10 => 0x100bb1e41b6c6c0d00004000440004
  | 11 => 0xec503828972dc0000000e0008e0008
  | 12 => 0x4467d03b2893a8008000e0010e0010
  | 13 => 0x702ce51aa159a00000002002020020
  | 14 => 0x488ec1173d34680d80008004080040
  | 15 => 0xf727edb57ec9a80080004008040080
  | _ => 0

private def maskT0B8 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x41fa6176ecaeec008000a0100a0100
  | 1 => 0xce17c8e73d11640000000020000200
  | 2 => 0x3927f02ebdda8c0d0000a0400a0400
  | 3 => 0xe218732fdbbd8c0000006080060800
  | 4 => 0xb4e1fe9cba0904008000c1000c1000
  | 5 => 0x87b8d615aeee40d0000a2000a2000
  | 6 => 0xea2c67c40461480080002400024000
  | 7 => 0x491672797853680d00006800068000
  | 8 => 0xd65a258fa66284008000b0000b0000
  | 9 => 0xa74d57c654a3ac0d80010000000000
  | 10 => 0x24ff54d4ed41840c00020000000000
  | 11 => 0x983f20fe8334040080040000000000
  | 12 => 0x46c3927bea89e40580080000000000
  | 13 => 0x27246ea062e96c0c80100000000000
  | 14 => 0x2dee34cf2e23440000200000000000
  | 15 => 0xae5e2b26edd2400580400000000000
  | _ => 0

private def maskT0B9 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x63965097d80b200d00800000000000
  | 1 => 0xc83ab4441fe6440101000000000000
  | 2 => 0x1063c3e6ad4ec80982000000000000
  | 3 => 0xb62c5e8a2de6440504000000000000
  | 4 => 0xb3512c029e34600d88000000000000
  | 5 => 0x7864df512fd2600c90000000000000
  | 6 => 0x6fa39ee6b0dd2c0ca0000000000000
  | 7 => 0x612a3fc931e4680940000000000000
  | 8 => 0xe5d69fe1485dc40200000000000000
  | 9 => 0x735c545aeb21481000000000000000
  | 10 => 0x1d28ec8c2550c42000000000000000
  | 11 => 0x4a3b92604e6b4c4000000000000000
  | 12 => 0x64c14c1c9a40ac8000000000000000
  | 13 => 0xd6f6ac4e9627250000000000000000
  | 14 => 0xeac61b76d7d5260000000000000000
  | 15 => 0x90930faa41eaf00000000000000000
  | _ => 0

private def maskT0B10 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xe3bce5f674d4dbb350805800030001
  | 1 => 0xddd935fe0fba39e650105800060002
  | 2 => 0xd9aa695c65246c7201005800030004
  | 3 => 0x2819e5737cff2eaeb4909000010008
  | 4 => 0x1de1c2c186d9f8a4d500c800020010
  | 5 => 0xd53c1878fba2b1a5f4909000060020
  | 6 => 0x7232c8f5e435688cb000c800000040
  | 7 => 0x7ed25fff9a01ab7a410c800030080
  | 8 => 0x7ac65f87f42aa914e480c800060100
  | 9 => 0xc875e5f264bf73af51005800070200
  | 10 => 0xdf3d7ad4b94a36ed61805800060400
  | 11 => 0x70e8b3c522943a9fe510c800010800
  | 12 => 0x4e32123ad38c9f2480909000071000
  | 13 => 0x7717a91a674cb1d6f410c800062000
  | 14 => 0x1a0a73a1fe94159884809000024000
  | 15 => 0x10458ff696ef2cef10905800058000
  | _ => 0

private def maskT0B11 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xc330e637007840ea71805800080000
  | 1 => 0xd1f6c1855ca9a31c05906000100000
  | 2 => 0x633326eefe35dcecd1803800200000
  | 3 => 0xca5e727a048dfe7054106000400000
  | 4 => 0x8858f46a8346f04b25908800800000
  | 5 => 0x1753f46a83b1fac88110e001000000
  | 6 => 0xf5ed12835e25dafbc590f802000000
  | 7 => 0x8d7562b10b6e61dbc410c804000000
  | 8 => 0x32747a3026b97e1bf0002808000000
  | 9 => 0xb600f886fc467f3061807810000000
  | 10 => 0x5af6a2cfe256288b11802020000000
  | 11 => 0xbe7525f2d0d1182fb4903040000000
  | 12 => 0x6236107699b5df80c010d080000000
  | 13 => 0x39285017ba0153ff15003900000000
  | 14 => 0x9dcd224046c3c947e0107a00000000
  | 15 => 0x2c26646d5906f3f3e4906c00000000
  | _ => 0

private def maskT0B12 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xf9ff310283e9d70fb0010000000000
  | 1 => 0x3086b81430b1c5bd01020000000000
  | 2 => 0x6725995449f261dd0840000000000
  | 3 => 0x486fc2518f6d773ee0180000000000
  | 4 => 0x1712ad8456cf57c0e4200000000000
  | 5 => 0xd5dd89f0284adf0de4c00000000000
  | 6 => 0x15acb3fe082a4c3276000000000000
  | 7 => 0xec6e3507d9bc13a328000000000000
  | 8 => 0xe171ee171e398c2926008000030001
  | 9 => 0x63350633589bcc352400000010002
  | 10 => 0x22a7022a70a48778dc000000000004
  | 11 => 0xd8322d8322c5d2556e408000060008
  | 12 => 0x62db062db0310f512a000000050010
  | 13 => 0xf74adf74ad422a2eb2008000050020
  | 14 => 0x3bbe93bbe95203b5e0200000070040
  | 15 => 0x148ad148ad347dbad0600000000080
  | _ => 0

private def maskT0B13 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xb0842b0842e701ee14000000010100
  | 1 => 0x9b5679b567e0efbfc8208000070200
  | 2 => 0xa1c39a1c39afce6498200000050400
  | 3 => 0xc0db2c0db20999d830008000050800
  | 4 => 0xcdd31cdd3177c3a8c6200000031000
  | 5 => 0x26e4626e46688087fa000000012000
  | 6 => 0x6c6186c61878c464c4600000064000
  | 7 => 0x7ff377ff37c81710b0408000058000
  | 8 => 0x4180841808383160fa408000080000
  | 9 => 0x21a5621a568bfc3a4e40c200100000
  | 10 => 0xe73a0e73a01d7d930405000200000
  | 11 => 0x7ccc97ccc9a078e740204000400000
  | 12 => 0x96671966715a49264a00d200800000
  | 13 => 0x6ca276ca27d30a8a28004201000000
  | 14 => 0x3d2503d2502bac43b8408202000000
  | 15 => 0x7736277362eb464f18201004000000
  | _ => 0

private def maskT0B14 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x7c0d47c0d45a138b22205208000000
  | 1 => 0x2cd922cd92b4e0b2b0400210000000
  | 2 => 0x15319153193630ff88408220000000
  | 3 => 0xfd597fd597aefe0898400240000000
  | 4 => 0x100091000939dcaf2e40d080000000
  | 5 => 0x66f5a66f5acb54cb72005100000000
  | 6 => 0xd42ecd42ec03bc0992600400000000
  | 7 => 0xf9258f92584425240e40d800000000
  | 8 => 0x7be897be89ba75fabc402000000000
  | 9 => 0xe3657e3657ed16290e210000000000
  | 10 => 0x41bc941bc9e09b4262220000000000
  | 11 => 0xf39d5f39d5c6ad948a240000000000
  | 12 => 0x59d4d59d4d07a67522480000000000
  | 13 => 0xa3eb1a3eb17b5c6e54300000000000
  | 14 => 0x693a1693a1aa247e18800000000000
  | 15 => 0x76c5076c50c858a0fd000000000000
  | _ => 0

private def maskT0B15 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x6d9017a34efad66459000000028001
  | 1 => 0x1ae4216d612ffd092e400000088002
  | 2 => 0xb7f44936934b91db7f402000000004
  | 3 => 0x16e08d1f82be0cd9ee000000088008
  | 4 => 0x11c10a220deaf6119c001000008010
  | 5 => 0x4bc2064ac14dfaec3c003000088020
  | 6 => 0xe0b40a504f3debfc8b003000028040
  | 7 => 0x6ebc08e0dc77f73eeb403000080080
  | 8 => 0x14e404db5c3d1401cf401000008100
  | 9 => 0xe5640993ed91d99cd4400000028200
  | 10 => 0xe1b00b3fc383cef41f0020000a0400
  | 11 => 0x4c840a7a9f163e3440402000008800
  | 12 => 0x2db402be26754b9acb400000081000
  | 13 => 0x5d0033524686470fd00100000a000
  | 14 => 0xd0840c275a25b1df48400000024000
  | 15 => 0xe5f40b371d9a87ed5f403000030000
  | _ => 0

private def maskT0B16 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xb12407778b2c2cc7124010000c0000
  | 1 => 0x15c40255572ade315c406000100000
  | 2 => 0x6c8403247227a086c840c000200000
  | 3 => 0x79d00602d1ddbfe79d00f000400000
  | 4 => 0x54f40412c9d20d454f40c000800000
  | 5 => 0x6aa40447ce6c4d86aa405001000000
  | 6 => 0x60a403382f369a260a402002000000
  | 7 => 0x7a20023c2e6749c7a2008004000000
  | 8 => 0x4d800ba7249c8824d8006008000000
  | 9 => 0x3680013727de526368008010000000
  | 10 => 0x65e402e74a1677a65e40b020000000
  | 11 => 0x1ba4084e22a73cd1ba408040000000
  | 12 => 0x20240cc3de467d2202406080000000
  | 13 => 0x7b40b1ef4cd81207b405100000000
  | 14 => 0x3d405c827d1f1403d408200000000
  | 15 => 0x53d00d90357c24853d002400000000
  | _ => 0

private def maskT0B17 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xa00079597525d90a0004800000000
  | 1 => 0xcd101d6e200f66acd1010000000000
  | 2 => 0xecd023f1a98c098ecd020000000000
  | 3 => 0xa4a44b11eb46065a4a440000000000
  | 4 => 0xb7f480e05c61b16b7f480000000000
  | 5 => 0xc2250642cc8bcfdc22500000000000
  | 6 => 0x230200d33d0a945230200000000000
  | 7 => 0xcf38047d8fa8ac6cf3800000000000
  | 8 => 0x8be05f0604c5398fb8007800080001
  | 9 => 0xb84262a624095a132200f8000a0002
  | 10 => 0x243396c1bddd204782807800030004
  | 11 => 0xfb959c1dd125e7d1a4808000020008
  | 12 => 0xdf9b40d1a42b74172800f8000a0010
  | 13 => 0xd0caa5380a4356613480f800090020
  | 14 => 0x80db3a1773f228aa1a80f800080040
  | 15 => 0xb7fbe0913e9c9a73ee008000080080
  | _ => 0

private def maskT0B18 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xfc242d21c2d90aa3e280f800010100
  | 1 => 0x13f80da300fc0e8c9e800000000200
  | 2 => 0x26e5c1bcdc62535ad6808000090400
  | 3 => 0x2ead338c53ff55106e807800010800
  | 4 => 0xd7c5023ed0b0531c52800000031000
  | 5 => 0xfd2ac2d62c3ba86f24807800022000
  | 6 => 0xa4bca96b4a77fca9608080000a4000
  | 7 => 0xfc82225aa276dbcf1280f800028000
  | 8 => 0x1aea16d021ccba137e80f800040000
  | 9 => 0xbad62f37629394049a004000100000
  | 10 => 0x35f3023fb06a22e160808800200000
  | 11 => 0x773d60d3dec02267a009800400000
  | 12 => 0x68a6bdce6b8ecc8b44007000800000
  | 13 => 0x4e9d7ea3d7f3149a4a00e001000000
  | 14 => 0x7ac9c8269cbf051f8a006802000000
  | 15 => 0xe94e27ce628b54f95a807804000000
  | _ => 0

private def maskT0B19 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x9a147645c7b2215fe480d008000000
  | 1 => 0x8176f82def82ac803a808010000000
  | 2 => 0x71b39135397b8e062e000020000000
  | 3 => 0x339171d917e87f82e0007840000000
  | 4 => 0xdb704885046779953200b880000000
  | 5 => 0x968144fc94bddcdd94808900000000
  | 6 => 0x7ce90f52901157b89c005a00000000
  | 7 => 0x1958661f0654ee378a802400000000
  | 8 => 0x84171ff5f06bdd97b4810000000000
  | 9 => 0x8064d1d64f992269d0020000000000
  | 10 => 0x210203ce24a4db81de040000000000
  | 11 => 0xd488fd3207fb5d307a880000000000
  | 12 => 0x2703ec8aae95558efa900000000000
  | 13 => 0xc84902cc30e80e1e48a00000000000
  | 14 => 0x2c78ed4fce8e302f88400000000000
  | 15 => 0x116fef86f965ffee9000000000000
  | _ => 0

private def maskT0B20 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xc0a60c12e7a12e665f00a0000c0001
  | 1 => 0xeaa2bd8be4fabe62c6000200020002
  | 2 => 0x27322c9acdc9ac9455000000000004
  | 3 => 0xa88836e3154c31de3b000200020008
  | 4 => 0xd6e0d3c2c3bc2d3dc800a000020010
  | 5 => 0xfbcd8aa1b68a196d75000000020020
  | 6 => 0x99d302339603797a900a2000c0040
  | 7 => 0xd81b5a8230c82b061900a0000c0080
  | 8 => 0xe695c5358c3148ca5e000200060100
  | 9 => 0x76b722ad300af308e900a000080200
  | 10 => 0xedd32447c4a43c412a0000000e0400
  | 11 => 0xc7d41a022e02a2ea270002000a0800
  | 12 => 0x9146c8f88a2e88a93f00a000001000
  | 13 => 0x70930ac5b8ac5b8fc200a2000a2000
  | 14 => 0xe1e7b1842d7c42df84000000064000
  | 15 => 0xe9d2fbf5a6975a6ef0000000028000
  | _ => 0

private def maskT0B21 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x6afa263b93d3b932440000000b0000
  | 1 => 0x62e67a285bc285ac29006000100000
  | 2 => 0xf3ce4f75145753aec000a00200000
  | 3 => 0x7257018ad610ad2e52000800400000
  | 4 => 0x5181d20a1c2aa1431a000a00800000
  | 5 => 0x59c9be6eaa4eeba28200a801000000
  | 6 => 0xd750445cfd45cddc14000002000000
  | 7 => 0x72c85b92abd32eb064006a04000000
  | 8 => 0x5480464571245f16a1004008000000
  | 9 => 0xc226295ba5ffaa5f6a006a10000000
  | 10 => 0x1f602da5d7fa7d7f78002020000000
  | 11 => 0xe5853f0b1618f1636300e840000000
  | 12 => 0xb7c0a8e17f2497f41e00aa80000000
  | 13 => 0xcd65cf29fa7b9fa7c0008900000000
  | 14 => 0xff87b4595e2995e784006c00000000
  | 15 => 0x14d681dee48dee4eef009000000000
  | _ => 0

private def maskT0B22 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x7f7dcf8884f88849ea010000000000
  | 1 => 0x3236c48211482110e6020000000000
  | 2 => 0xfd2ddaea5daea5784040000000000
  | 3 => 0x32c741a7b11a7b1d91080000000000
  | 4 => 0x904566e85f6e85f43c100000000000
  | 5 => 0x2aa166acdc6acdc89a200000000000
  | 6 => 0xcc9c91c6061c606d15400000000000
  | 7 => 0x743a8bebfebebfe2ae800000000000
  | 8 => 0xd2625f3ceaaca245ec002000000001
  | 9 => 0x7ca9f2b7144668d6ac100000050002
  | 10 => 0x8e233c94a2eec3720e000000040004
  | 11 => 0xeea396d3395d22173810a000060008
  | 12 => 0x98c3b4c9e24aa3b326108000060010
  | 13 => 0x756d52ee80315d444102000060020
  | 14 => 0xeced6e8c7ea9e86e5010a000000040
  | 15 => 0x8e3bd1cb1eb112d7f2100000040080
  | _ => 0

private def maskT0B23 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x227e930f64f08f952e10a000020100
  | 1 => 0xf8aa1b668f7a4a1a2c002000000200
  | 2 => 0x2c84bc08db4705b1bc102000050400
  | 3 => 0xcaed84caa5674c8cd2100000060800
  | 4 => 0x2e9f28708320df25f4002000071000
  | 5 => 0x12a0330d37a2803822002000012000
  | 6 => 0x2a639b772070c39aea00a000054000
  | 7 => 0x33ac309497b88d333210a000018000
  | 8 => 0xa92e8d31ed62af8cb8108000080000
  | 9 => 0x9d2db96852272dab20000800100000
  | 10 => 0x4a50a7d0b708b0882e00c000200000
  | 11 => 0xb7908c73057eb1c2b210e200400000
  | 12 => 0x68c43d2ab7bedcbd610c000800000
  | 13 => 0x8a2192f36f26e094cc00e001000000
  | 14 => 0x5df9f48c8df9dbfcc2006802000000
  | 15 => 0x7c1d6fdd1dfa59626400a004000000
  | _ => 0

private def maskT0B24 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x4a71870ae6cf588c52104008000000
  | 1 => 0x8f435edea9cb735c42008010000000
  | 2 => 0xa6ace2a45cf96dedde108220000000
  | 3 => 0x153ffb6f4ff93ff24400c840000000
  | 4 => 0xb4b6eb33bbf416e202006080000000
  | 5 => 0xa0f00791960710066e00c100000000
  | 6 => 0xff9ec4ec91089fcbb0104c00000000
  | 7 => 0x778cefd8f9d00de378109000000000
  | 8 => 0xc472a04fd26a32bae4010000000000
  | 9 => 0x4ef7da1d0f2917f67e020000000000
  | 10 => 0xb7c52b7ee050a46e76140000000000
  | 11 => 0xe3eb52e8c3132bdf0c080000000000
  | 12 => 0x7648a8031e89aaaffe200000000000
  | 13 => 0x4a51912680b6b59fce400000000000
  | 14 => 0x70c57077e3faad78a6800000000000
  | 15 => 0x7826c5a57db5b6ccd9000000000000
  | _ => 0

private def maskT0B25 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x5e0803d984f8c026e0803000080001
  | 1 => 0xdb60013103a8fb7eb6003000020002
  | 2 => 0x3e6003ea3cc5eddd6600e800080004
  | 3 => 0xd0000684f0e466ee00003000020008
  | 4 => 0x126a0182114c741fa6a0e800020010
  | 5 => 0xd4a20e7d9c84e6ed4a200000020020
  | 6 => 0xcba20af2c922d15cba200000080040
  | 7 => 0x7aa20a167cce4064aa203000080080
  | 8 => 0xc7a00fae4acf62e2fa00e800020100
  | 9 => 0x9eca0208d2ab317aeca03000080200
  | 10 => 0x5f60030c74008a7b7600e800020400
  | 11 => 0x9ded0b9eb3d8000d800020800
  | 12 => 0x9dc00a8123b21f79dc000000081000
  | 13 => 0x2a000603b0757ecc2000e800022000
  | 14 => 0x7ee809c092063b27ee800000024000
  | 15 => 0xb4000cb0eccb6b08400030000a8000
  | _ => 0

private def maskT0B26 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x9c620abd13f5b1eac6203000030000
  | 1 => 0x7c400425793190ea4400d800040000
  | 2 => 0xc2c81c53d5d45cbeac802800100000
  | 3 => 0x3c222f2a9fa2bdeb42208800200000
  | 4 => 0x3100482845dfc61c1000f000400000
  | 5 => 0x768085f5f374f3bfe8008800800000
  | 6 => 0xdbeb0009be99658c3ea01801000000
  | 7 => 0xd00003e92d0b6d1b80206802000000
  | 8 => 0x28460c850d7883de0420c804000000
  | 9 => 0x28400998db7b633484806008000000
  | 10 => 0xb3520041beecdcf7b420c810000000
  | 11 => 0x6dea026422f330b95ca0f820000000
  | 12 => 0x45aa0018304cdcfc5ea08040000000
  | 13 => 0x68ea057e7c7d984406a02880000000
  | 14 => 0xbf880262a03bbf8ee8805100000000
  | 15 => 0x7c62085a0742f51b6620ca00000000
  | _ => 0

private def maskT0B27 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x62c00850b34dff046c002400000000
  | 1 => 0x2d0a1e645b3ce742d0a10000000000
  | 2 => 0xcca20fbd2bf8860cca20000000000
  | 3 => 0xf4e04f4b2afcfb4f4e040000000000
  | 4 => 0x288880c71273e01288880000000000
  | 5 => 0x926102180d3132c926100000000000
  | 6 => 0x95ac0524bccd0e395ac00000000000
  | 7 => 0xad00503f2df5f40ad000000000000
  | 8 => 0x777b900001dc8e0554800000000001
  | 9 => 0x47106880027671c54480e800060002
  | 10 => 0x29658ea004efa0803000ea00000004
  | 11 => 0xba778c80088297ce9600e800020008
  | 12 => 0xbbe28c8010ee01676000e800020010
  | 13 => 0xcce33a202007b433578002000a0020
  | 14 => 0x112d7c00404762f1530000000c0040
  | 15 => 0x5d75caa0800d96f65480ea00040080
  | _ => 0

private def maskT0B28 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3d7700a10061e5156480ea000e0100
  | 1 => 0x71010ea200456a22d600ea00000200
  | 2 => 0xf752ae040069201c500000000e0400
  | 3 => 0x8062e0880070a8042780e8000e0800
  | 4 => 0xc69d9e900064ecfbd580e800001000
  | 5 => 0x936af8a0008730865380e800062000
  | 6 => 0x896f1240004f8305d1800000024000
  | 7 => 0x7a675680001cd66e33000000068000
  | 8 => 0x26aedd800064c74c2080e800030000
  | 9 => 0x82b2de200104fe59e200e200100000
  | 10 => 0xdeccee0002bc2cb61300e000200000
  | 11 => 0x9aa0b08004ba8e8567800800400000
  | 12 => 0xb76e342008495131d5004200800000
  | 13 => 0xaa1832a010d4e420f5802a01000000
  | 14 => 0xc1943a2020f0ccc46700a202000000
  | 15 => 0xb86a44a0407c2bb9e6004a04000000
  | _ => 0

private def maskT0B29 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xd0b18c20802ed90a6300c208000000
  | 1 => 0x76aa4801000314ef82808010000000
  | 2 => 0xd51b6822005f9e3640808220000000
  | 3 => 0xa37a024000bcef7b1800240000000
  | 4 => 0x5535a608009323a2d6006080000000
  | 5 => 0xee7ca0b0007f7ea9b5800b00000000
  | 6 => 0x62bc224000c6348547802400000000
  | 7 => 0x9b09cb0000eacf208200b000000000
  | 8 => 0x6101c00000602c7602010000000000
  | 9 => 0x62552000001ce97607020000000000
  | 10 => 0x2c1f6000009179dfc5040000000000
  | 11 => 0xc9e10000016b02b05880000000000
  | 12 => 0x77d07000003e622a62900000000000
  | 13 => 0x2bc850000052cc67a6200000000000
  | 14 => 0xb2adf0000033d7f712400000000000
  | 15 => 0xa11b0000005f79b148000000000000
  | _ => 0

private def maskT0B30 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xcb5b71b795a4210a42109000000001
  | 1 => 0xc8ecd1984130600306008000060002
  | 2 => 0xb08cd4127672a0072a009000040004
  | 3 => 0x96d1fae52d3f6103f61000000a0008
  | 4 => 0x332804025aaf210af2101000060010
  | 5 => 0x3b651a6334b6e00b6e0080000a0020
  | 6 => 0xd17360b8fee3600e360090000c0040
  | 7 => 0x847dd6968f9c6009c6000000040080
  | 8 => 0x84960f72df09600096008000060100
  | 9 => 0xbdded9a67aa6c00a6c009000000200
  | 10 => 0xf87716a27ac810ac8108000020400
  | 11 => 0xc7aab9ac995b4105b4100000060800
  | 12 => 0x9c09952dbdbaa00baa001000041000
  | 13 => 0x6f8a180a0caec10aec108000022000
  | 14 => 0xa11a320cea756107561080000e4000
  | 15 => 0xfc74cc178f108101081010000e8000
  | _ => 0

private def maskT0B31 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x97739eb65bb8010b801090000b0000
  | 1 => 0xe544e8c17df4a10f4a100c00100000
  | 2 => 0x23eb03c67f61a1061a10c000200000
  | 3 => 0xe4accebb36c8200c8200d000400000
  | 4 => 0x1060e74872f0c00f0c001c00800000
  | 5 => 0xba2d1ef102bb000bb0005001000000
  | 6 => 0xe4d71df7f1c3600c3600d802000000
  | 7 => 0x9f3120c8929161091610cc04000000
  | 8 => 0xa164c5363b3610b36104008000000
  | 9 => 0x7ac4ef4c2225400254005c10000000
  | 10 => 0xe4f2e566bf7b2107b2109020000000
  | 11 => 0x6e204f7293aea10aea108040000000
  | 12 => 0x3f72101f75a9e10a9e104080000000
  | 13 => 0xd5ce89bea81d8001d8005100000000
  | 14 => 0xd4788a2421d1a10d1a105a00000000
  | 15 => 0x1c2b7bbdb79d4109d4102000000000
  | _ => 0

private def maskT0B32 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xd16c71140c50c0150c010000000000
  | 1 => 0x4b5d58cf7727212272120000000000
  | 2 => 0x485194ff296fc046fc040000000000
  | 3 => 0xa3f2ac071467c0867c080000000000
  | 4 => 0x8db8619b3c22620226200000000000
  | 5 => 0x89f7efbba8b6640b66400000000000
  | 6 => 0x3baa061b9060680606800000000000
  | 7 => 0x4de2c591500cd000cd000000000000
  | 8 => 0x53f7169d3781671d29000000000001
  | 9 => 0x30900fa68740f00706000000050002
  | 10 => 0xcd80b4dd83f300b568006800040004
  | 11 => 0x60f16e08dd4901689f00a000060008
  | 12 => 0x827eb749f0a77eb85000a000060010
  | 13 => 0x5f03c22990b313cec1000000060020
  | 14 => 0xa56a237026a8ea2ad800a000000040
  | 15 => 0xbd402afe06212029c6000000040080
  | _ => 0

private def maskT0B33 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x903537966c3565305500a000020100
  | 1 => 0x4cf1e9505274b1e504006800000200
  | 2 => 0xe93643c2e225364cc0000000050400
  | 3 => 0x84960cf4bcfed607a4000000060800
  | 4 => 0xe00d733d0b9a4d77a4000000071000
  | 5 => 0x20ecdd6c89dafcd921006800012000
  | 6 => 0x98be523af9e13e5d9800a000054000
  | 7 => 0x6d35a04b0be245a2f700a000018000
  | 8 => 0x85db08383d548b071500a000080000
  | 9 => 0x61bd0574c20a1d1f3a009800100000
  | 10 => 0xc22f70f1f87f2f5ed0005000200000
  | 11 => 0x25369142465336d5e0002800400000
  | 12 => 0xbba8a36e0bff98284300c000800000
  | 13 => 0xbc19218ba65fa8203b00e001000000
  | 14 => 0x9b9855707642ba521200f802000000
  | 15 => 0x4a25dca5d48311d69300a004000000
  | _ => 0

private def maskT0B34 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xfb9cc92ee4a434c1fa004008000000
  | 1 => 0xcd94869bbfe8948a51008010000000
  | 2 => 0xefbe2757442bbe046004820000000
  | 3 => 0x5b218db2fb35c18a6a00c840000000
  | 4 => 0x8e47f6d3d06247f8c8006080000000
  | 5 => 0x24467e287b9f967ead005100000000
  | 6 => 0xe9e35c711812935a17005a00000000
  | 7 => 0x4e738ac89363f38618004c00000000
  | 8 => 0xb09dcb720d309dd800010000000000
  | 9 => 0x78cf6965c6505f4289020000000000
  | 10 => 0x72c70e673d6167413a040000000000
  | 11 => 0xd91a4f08a8857ac5c6080000000000
  | 12 => 0x8b1c53c469fd3d5762100000000000
  | 13 => 0x2a7c33ec1d305cd1a200000000000
  | 14 => 0x3ebefa1b5fec1afd2a400000000000
  | 15 => 0x7c0cdeef4115b4d69b800000000000
  | _ => 0

private def maskT0B35 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xb36f435ba4d175117a000000040001
  | 1 => 0x1c96e75501a51ed4cd80a000020002
  | 2 => 0xd02fbdb0ff442006f000a000080004
  | 3 => 0x53b9b5f14e6ffdd8350000000e0008
  | 4 => 0x19f2be0f5b6e56053500a400060010
  | 5 => 0x7aa778ad182034fd4400a4000a0020
  | 6 => 0x7b15c43e7a4c5e6f4a800000080040
  | 7 => 0xf63bf3b73d1bc02f2800a400080080
  | 8 => 0x228dfa3c453581a54d8000000e0100
  | 9 => 0xdd030630f8438ccbf800400040200
  | 10 => 0x21642cd90afcdc8b068000000a0400
  | 11 => 0x62e87e7fbbb68bc131800000020800
  | 12 => 0x7f185e8b9d00d985678000000c1000
  | 13 => 0xf604c052c4ee708df580a000062000
  | 14 => 0xee2ead3a8d543e709b800400064000
  | 15 => 0xcb2c49fa1b5a05f668800000068000
  | _ => 0

private def maskT0B36 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2b7a69b3b0fb2169b600a000070000
  | 1 => 0xee346eda7a7553d36c004000100000
  | 2 => 0x80cef0cc6a09a8765a00e000200000
  | 3 => 0x355d90096df10b084c004000400000
  | 4 => 0x595625015b4dbb1a4f80e000800000
  | 5 => 0xa5bd4dfc50f831446480c401000000
  | 6 => 0x1e71ba02fd497e6b7000402000000
  | 7 => 0xc6e26b036eb91084fc008004000000
  | 8 => 0x8d702af5fbe36f9854804408000000
  | 9 => 0xfa5bb519a063413c9808010000000
  | 10 => 0xf2e961c9eaa667c6c3002420000000
  | 11 => 0x608d4738ba27b6e94f00a040000000
  | 12 => 0xec65dba8165364f0d804080000000
  | 13 => 0x6cc4a529b5b59ff4ac00c100000000
  | 14 => 0x1ff111b8a0c49b162e00a200000000
  | 15 => 0x8020690a5ae96dc91e806800000000
  | _ => 0

private def maskT0B37 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x631f8ed45992a21acf80b000000000
  | 1 => 0x21542ee826b50e57ad810000000000
  | 2 => 0x7d8db0433f3d5e644e020000000000
  | 3 => 0x5bbd3fc91b59d4cfef840000000000
  | 4 => 0xa1ab7d62aab8715cff080000000000
  | 5 => 0x132fe361ad2d25308100000000000
  | 6 => 0x70f73c1de0bdfb30cd200000000000
  | 7 => 0x14a202bf09b5f698aa400000000000
  | 8 => 0xe198b2ca4a000015b3000000000001
  | 9 => 0x4fcdda76b0a0002c310068000a0002
  | 10 => 0x5d5ae970b800004b1f000000000004
  | 11 => 0xf00b222b7d2000809e807800020008
  | 12 => 0xe0e3d957d5200103b6801000020010
  | 13 => 0x87b0c4d2b4a0020f6f0078000a0020
  | 14 => 0x59835065b7000408e3007800000040
  | 15 => 0x511264d4ec8008064c007800080080
  | _ => 0

private def maskT0B38 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xdc3d9a6727a0100cce8000000a0100
  | 1 => 0xb56e03e4a900200713800000000200
  | 2 => 0x4de4562f22a04008560068000a0400
  | 3 => 0x95647ffeb8a08001c10010000a0800
  | 4 => 0xe0ae9faf1901000b1f001000001000
  | 5 => 0xb782761c532200074d001000022000
  | 6 => 0xed5a975d9024000b69006800024000
  | 7 => 0xb42da1233128000b35800000028000
  | 8 => 0x4ba1952636b0000fba0000000b0000
  | 9 => 0x24b41336d440000f91806800040000
  | 10 => 0x1173fad0cc00000841002800100000
  | 11 => 0xbd8ecab4220000060680e000200000
  | 12 => 0x62b24408ef000002e2009800400000
  | 13 => 0x38ff7ee086000008dd80c000800000
  | 14 => 0xb163c03a4900000d53001801000000
  | 15 => 0x51b5f43ca400000ca780d802000000
  | _ => 0

private def maskT0B39 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x460cef3efc0000065300c804000000
  | 1 => 0x8d60aae71100000a1e00d008000000
  | 2 => 0x3975fc7efc000001dc00a010000000
  | 3 => 0xcc1c14b2a00000407000020000000
  | 4 => 0xfcec9427d90000018b80c840000000
  | 5 => 0x1824ff1d6200000f9b809880000000
  | 6 => 0x2ebab0fffb00000a34803900000000
  | 7 => 0x8d308fa7250000083c003200000000
  | 8 => 0x55b4da0ca8000007d180fc00000000
  | 9 => 0xa5330b36540000070f810000000000
  | 10 => 0x5d4d3c4bed000001b7020000000000
  | 11 => 0x73d13e6800000ddf840000000000
  | 12 => 0x6304866e400000e61880000000000
  | 13 => 0x93840fe2de00000878100000000000
  | 14 => 0xa5e56938d60000042fa00000000000
  | 15 => 0xfe286ea219000009dec00000000000
  | _ => 0

private def maskT0B40 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x98fb1699b103bacc56003400080001
  | 1 => 0xac6fda37fde63ec2f1002000010002
  | 2 => 0xe95ff953ff5068a5c6002000000004
  | 3 => 0x6af1a5b91a2fc7e256001400090008
  | 4 => 0x8788a34f8a75001877003400020010
  | 5 => 0xff7963f7969cd08f40003400010020
  | 6 => 0xd0c146d2142ac1189e003400000040
  | 7 => 0x72f221ff22fac58790001400030080
  | 8 => 0xd39c3b93c3d6d114aa0020000a0100
  | 9 => 0xe60141a3144ecbffc3000000000200
  | 10 => 0xe26c4506c939bd5f2001400020400
  | 11 => 0xbd32a00d2ad76409de002000020800
  | 12 => 0x2473aa973a268cb8d0000000031000
  | 13 => 0x26c05bec0d74346d8003400022000
  | 14 => 0x7422fb72245ba6fc3000000024000
  | 15 => 0x98c2bdad2b0c5b4621002000098000
  | _ => 0

private def maskT0B41 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x6e43495d34c216ccf90034000c0000
  | 1 => 0x5b65f4c95eeac8873f006400100000
  | 2 => 0xf19d5184d71dc2709d00e000200000
  | 3 => 0xb5326e00226435d81300d400400000
  | 4 => 0x3d5f4dcefc7164ab5b005400800000
  | 5 => 0x4a5ecd11fc191bf7b400e001000000
  | 6 => 0xd37bc3059cd1f0ee32000002000000
  | 7 => 0xae89d4e6ddb27fff0e001004000000
  | 8 => 0x8f5e5c01654cfaebb400f408000000
  | 9 => 0xb194440344eba8a71b008010000000
  | 10 => 0xb8edf01adf1e909b96000020000000
  | 11 => 0x39b90d7e903eec8da1003440000000
  | 12 => 0x220ad0edadb1643d8500f480000000
  | 13 => 0x968980cc98028347b400e100000000
  | 14 => 0xbe1e1bede1bc38816c001600000000
  | 15 => 0xa1cba8abba19576437006800000000
  | _ => 0

private def maskT0B42 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x14dda30cdbad33c241010000000000
  | 1 => 0x81722f2e200f7d9739020000000000
  | 2 => 0x8d6f9218fdb5ee3ace040000000000
  | 3 => 0x4554bf3343abec9b66080000000000
  | 4 => 0xb7c950738553bbdb0f100000000000
  | 5 => 0xf4ee2fe3c23fd5f0ad200000000000
  | 6 => 0x8103826178095a6a71400000000000
  | 7 => 0x3db1d3d79d4184100c800000000000
  | 8 => 0x661f2896e8ef71a85a003000080001
  | 9 => 0xe414bbc4be585f574410a400020002
  | 10 => 0x4048179e4139ac052a103000080004
  | 11 => 0x8fabf8c61203cad0fe0094000a0008
  | 12 => 0xc9cb2c2f570b3e51ec1000000e0010
  | 13 => 0x257e5c7a27e2dc2acc10a4000e0020
  | 14 => 0xe232ee387601b5875600a400000040
  | 15 => 0xfa0861824ce22ca8c6009400000080
  | _ => 0

private def maskT0B43 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x31fa4098ec3874821400a400060100
  | 1 => 0x7d22bf2df28ffd92e60030000c0200
  | 2 => 0xc99f898b0c512f4fea0000000e0400
  | 3 => 0x111bd220ff331422fe0030000e0800
  | 4 => 0x388b90910d319b41180094000c1000
  | 5 => 0x56f6bfe3f3a8c9821800a400062000
  | 6 => 0xb9f307cf94c50a4df410a4000a4000
  | 7 => 0x4135e66cdd27f83282109400028000
  | 8 => 0xb47ef8a5343e2db650103000030000
  | 9 => 0x9a002190b5830b7ad8106000100000
  | 10 => 0x4d38d34a21799acd0a10e000200000
  | 11 => 0x9de921cd55813c7aa8006000400000
  | 12 => 0xf413775490815a7ace00e400800000
  | 13 => 0x38ae052b1f6a1ff11c005401000000
  | 14 => 0x7f110ac9e1d38f1200009402000000
  | 15 => 0xe4b7c28548cce3417c10a404000000
  | _ => 0

private def maskT0B44 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x41f77e88aea97d9bd4104408000000
  | 1 => 0xe4a6174d4f9072e8aa101410000000
  | 2 => 0x944c2c30c157403bb0002020000000
  | 3 => 0xd2fc037d24e52e46b8003040000000
  | 4 => 0x6f7b57b5bd14208d78106480000000
  | 5 => 0x2d737fd058d076f4da005500000000
  | 6 => 0x7f6383b82844e1063e101600000000
  | 7 => 0x281dad7440ff59a00400d800000000
  | 8 => 0xf96ab89aa170c0a2ca010000000000
  | 9 => 0x13917938b0801a7756020000000000
  | 10 => 0x691fe715d51842b618040000000000
  | 11 => 0xb1ad44a85efb28afbe180000000000
  | 12 => 0x1787241c7456406d9e200000000000
  | 13 => 0xba25bee89b54ac0b56400000000000
  | 14 => 0x7ac10d7e99ad2899be800000000000
  | 15 => 0xcfec7db37b14dbc405000000000000
  | _ => 0

private def maskT0B45 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x72c4b4d1f9fe732c1a800000040001
  | 1 => 0x86d7508108bfa7db16008000020002
  | 2 => 0xcb5059a6cf9ef4a4fc808000080004
  | 3 => 0x95848161b6568fed510000000e0008
  | 4 => 0x6030226b59146dbd2e808000060010
  | 5 => 0xcfde95d7cca85a5baf8080000a0020
  | 6 => 0x3d7f9bbb69b9c903f0000000080040
  | 7 => 0x6d62b7439e9ad35038808000080080
  | 8 => 0x76d1c4c74de1dd1db78000000e0100
  | 9 => 0x3211da4f13aad8e3c3800000040200
  | 10 => 0x3afedcc9b2ddddf2bb8000000a0400
  | 11 => 0x22b1eb8c11b438f2e4800000020800
  | 12 => 0x1409bc951a54c018998000000c1000
  | 13 => 0xc8375eb38c3e9799d9808000062000
  | 14 => 0x593270a00c5922b0a1000000064000
  | 15 => 0x447c13a8ed4342c3db000000068000
  | _ => 0

private def maskT0B46 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x36638dc9a1260194cf808000070000
  | 1 => 0xe10307ed9b27b2af86804000100000
  | 2 => 0x8d6cd2dc5896a17f6080c000200000
  | 3 => 0xe9a3f1996e0fa559f9006000400000
  | 4 => 0x717bcee409f7b3b6880e000800000
  | 5 => 0xf9699f3498e719109380e401000000
  | 6 => 0xd22e1307cd78d8cbe8802402000000
  | 7 => 0xc6e26b036eb91084fc008004000000
  | 8 => 0xd1a4f83d33fc47cca3806408000000
  | 9 => 0x51e422be81d4f432ee808010000000
  | 10 => 0xfdde08fe0bf486ba29802420000000
  | 11 => 0x31fbb7e040a797b48280a040000000
  | 12 => 0x8eeceee24a84b04a4f804080000000
  | 13 => 0x3db255f14f35bea96180c100000000
  | 14 => 0x927980f059ba141a56808200000000
  | 15 => 0xada529108ebcc5c806800000000
  | _ => 0

private def maskT0B47 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xbfe1ef445a6c0c4b7a809000000000
  | 1 => 0x2e6347dfc7e7ef2b47010000000000
  | 2 => 0xf2906a2c158e391de6820000000000
  | 3 => 0x548a56fefa0b35b305040000000000
  | 4 => 0xf0dd8dba5038500132880000000000
  | 5 => 0xdf59d481cae194776d100000000000
  | 6 => 0x7fc0552a01ef1a4c27a00000000000
  | 7 => 0xcac92808d986b0bccf400000000000
  | 8 => 0xb231000016af6ee8a000000000001
  | 9 => 0x14844a0002f3c12a8d0000000a0002
  | 10 => 0xc9528a8004de46b69b0058000a8004
  | 11 => 0xf09b1a00082de2478500b0000a0008
  | 12 => 0xe058b8801082c6cdb6000000088010
  | 13 => 0xf053ca0020de3244560058000a0020
  | 14 => 0x902f6a8040696b9fc20000000a8040
  | 15 => 0x4018580080a40145b0005800080080
  | _ => 0

private def maskT0B48 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xd56e120100b97466d0005800020100
  | 1 => 0x8060a80200b73e37b800e800080200
  | 2 => 0x67061a0400849b510400b0000a0400
  | 3 => 0x2893820800c7c7eb4c000000020800
  | 4 => 0x1a1a6a90008c8cba7f0000000a9000
  | 5 => 0x358a5a20007386a9ca0000000a2000
  | 6 => 0xe52d24000cb24eead000000024000
  | 7 => 0x44754b000053b55ff500b0000b0000
  | 8 => 0x9054b40000edbb4d5400b000040000
  | 9 => 0x183d80000084ef584700b800100000
  | 10 => 0xeb00e0000049832514005000200000
  | 11 => 0x6b2040000027dfb97900b800400000
  | 12 => 0xe192300000ebaf3c1b00a800800000
  | 13 => 0x2c1b00000aadd546100c001000000
  | 14 => 0x3d005000004c26684a00f802000000
  | 15 => 0x2525f000000ba669e0001004000000
  | _ => 0

private def maskT0B49 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x5363900000f399c461002808000000
  | 1 => 0x7d67300000857222bb003010000000
  | 2 => 0xa3a9a00000b4ffc857006820000000
  | 3 => 0x51856000001304f165005840000000
  | 4 => 0xf5d7f00000c22b74d500d080000000
  | 5 => 0x9576d00000d395e6ea00e100000000
  | 6 => 0x5d37700000c96d324900ea00000000
  | 7 => 0xaab73000003e4d55d6002400000000
  | 8 => 0xce0b0000007c8c07b8010000000000
  | 9 => 0x9721a000006defb657020000000000
  | 10 => 0x8d04600000ce006e8d040000000000
  | 11 => 0x70c6900000a0c8c0db080000000000
  | 12 => 0xa48230000094bab006100000000000
  | 13 => 0x25d99000001115a754200000000000
  | 14 => 0xb2adf0000033d7f712400000000000
  | 15 => 0x7c58800000b678ebde800000000000
  | _ => 0

private def maskT0B50 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x118be2502829f008400080001
  | 1 => 0x55b51160dca39008400060002
  | 2 => 0xe0a57a34fb67000000040004
  | 3 => 0xf0e8c4547702a00a400060008
  | 4 => 0x95c03463ddc740020000e0010
  | 5 => 0x2a413b81de3d400a4000a0020
  | 6 => 0xf66e3631c5d3f000000080040
  | 7 => 0x6899721ac9cb5002000000080
  | 8 => 0x702f90114b13c00a400060100
  | 9 => 0x8bdec28e9f5b300a400080200
  | 10 => 0xbf7d6e882612a008400020400
  | 11 => 0x6a47451108062002000060800
  | 12 => 0x558e6d655b261000000081000
  | 13 => 0x466c0b2654e74008400022000
  | 14 => 0x107e3d8fa3a9900a4000a4000
  | 15 => 0x8ae6d5a5ab55b000000028000
  | _ => 0

private def maskT0B51 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x652e36be0aea30020000f0000
  | 1 => 0x27d27f9068671004000100000
  | 2 => 0x3a985ed441d3500e400200000
  | 3 => 0x34f529458dcfd004000400000
  | 4 => 0xf78fe57f95d9500c400800000
  | 5 => 0x8acbb68d25ecb00c001000000
  | 6 => 0x411116dc76d35000402000000
  | 7 => 0x205bc9fc90b7b001404000000
  | 8 => 0xe80de341050fd00f008000000
  | 9 => 0xfcd8de15e99db001410000000
  | 10 => 0x51d935d3b525400b020000000
  | 11 => 0xe7c26ab64374400a440000000
  | 12 => 0x84b7b8b84acc2004080000000
  | 13 => 0xf5504038ded6100c500000000
  | 14 => 0x7298a069530a00a600000000
  | 15 => 0xab8c6f2d83c0900f800000000
  | _ => 0

private def maskT0B52 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x947032fc8bd34010000000000
  | 1 => 0x2a526fc4eb7e2020000000000
  | 2 => 0x68b638724e90d040000000000
  | 3 => 0x56a1518f72fce080000000000
  | 4 => 0x9579bb3f5183100000000000
  | 5 => 0x108e42f70557d200000000000
  | 6 => 0x95a23f4d18ec400000000000
  | 7 => 0x69d8a53aa4e0e800000000000
  | 8 => 0x5a1b2ff9d5d00005ad408000070000
  | 9 => 0xaeb8b27add400001d4002000040000
  | 10 => 0x7d95c143a000003cc400000000000
  | 11 => 0x3804421a38f0000d7d009000040000
  | 12 => 0x7e16eace3200000405000000000000
  | 13 => 0xc07ecd1f62000008c5400000000000
  | 14 => 0xba2bd5ea8400001465400000000000
  | 15 => 0x5ae3074ca0f0002366409000040000
  | _ => 0

private def maskT0B53 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xdbf8c99716f0004b18009000040000
  | 1 => 0x717f60ede3d0008fc9009000040000
  | 2 => 0xc4a558caf5600102a3000000040000
  | 3 => 0x9c3b8eb8e7b0020724409000000000
  | 4 => 0x981c06472f00408db409000040000
  | 5 => 0x202fe93cf69008086e409000000000
  | 6 => 0xd24d867760b0100e64409000000000
  | 7 => 0x6f8b8fb2a80020061c400000000000
  | 8 => 0xcaf04a6cbef0400007009000040000
  | 9 => 0xd333035f5ef0800008409000040000
  | 10 => 0x23a822e02741000c0c000000040000
  | 11 => 0x2892bc6c5a620005e1400000040000
  | 12 => 0xc10b020f9494000949009000000000
  | 13 => 0x8719c5c52628000f2a400000000000
  | 14 => 0xa937011d2e500006df400000040000
  | 15 => 0x40d6445b69000001ad400000040000
  | _ => 0

private def maskT0B54 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xa5dd98604e10000714009000000000
  | 1 => 0x72f6c4e22c0000017c400000000000
  | 2 => 0xe44c389f670000026f400000000000
  | 3 => 0x7e9ecd3d5e10000062401000000000
  | 4 => 0xc764395b5700000eaf000000000000
  | 5 => 0x4d46e2bf4500000413400000000000
  | 6 => 0xf80de643d100000bcb000000000000
  | 7 => 0xde68c0747500000bcb000000000000
  | 8 => 0xd83e918ed400000fce000000000000
  | 9 => 0xfd550d61cd00000cd6000000000000
  | 10 => 0x15c6439c0000067c000000000000
  | 11 => 0x5738edde0300000279000000000000
  | 12 => 0x3d3195388e000005b0000000000000
  | 13 => 0xeb12d8278b00000aaa000000000000
  | 14 => 0x9749bd0201000009a4400000000000
  | 15 => 0x1cf8f5731b90000a6e009000000000
  | _ => 0

private def maskT0B55 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x844346439c0000067c000000000000
  | 1 => 0xcea0b551b200000572400000000000
  | 2 => 0x492171cea70000026f400000000000
  | 3 => 0x4ba0c4026800000279000000000000
  | 4 => 0xd88ee6ef7500000da1400000000000
  | 5 => 0x6e076657d400000050000000000000
  | 6 => 0x986b1685f500000103400000000000
  | 7 => 0xb47bc7f9030000026f400000000000
  | 8 => 0xd88eefbef800000da1400000000000
  | 9 => 0xb28798c36f0000030e400000000000
  | 10 => 0xc1cded15b800000279000000000000
  | 11 => 0xbdccba927300000cb6400000000000
  | 12 => 0x521c492cf900000572400000000000
  | 13 => 0xcae3e9e96100000016400000000000
  | 14 => 0x3dac115ca00000eaf000000000000
  | 15 => 0x2fb462a8b100000a07400000000000
  | _ => 0

private def maskT0B56 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xc905a0af180000026f400000000000
  | 1 => 0x8ef531b04500000eaf000000000000
  | 2 => 0xa55a886858000008c5400000000000
  | 3 => 0xd88ee47ae800000da1400000000000
  | 4 => 0x81be164dbf40000c75400000040000
  | 5 => 0x9b0c23665b00000da1400000000000
  | 6 => 0xc5706afb4f00000318000000000000
  | 7 => 0x344568eb1200000564000000000000
  | 8 => 0x2e8b169c6700000161000000000000
  | 9 => 0x33500f23d200000016400000000000
  | 10 => 0x2e1f3787ac0000067c000000000000
  | 11 => 0x3a24f2dcc4000009b2000000000000
  | 12 => 0x4bdc8ca26040000da7004000000000
  | 13 => 0x730585e38400000bcb000000000000
  | 14 => 0x3a24f728f9000009a4400000000000
  | 15 => 0xe2236edcb600000564000000000000
  | _ => 0

private def maskT0B57 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xdf9b8b221c000008d3000000000000
  | 1 => 0xb592f5e3c90000067c000000000000
  | 2 => 0x8e897a8f3a0000030d000000000000
  | 3 => 0xb66e2a5e8d00000eaf000000000000
  | 4 => 0xddd3131386400002d9001000050000
  | 5 => 0xe67dfa918200000016400000000000
  | 6 => 0xfae5d620500000030e400000000000
  | 7 => 0xd83e9f719000000fce000000000000
  | 8 => 0xe2b1b59c7aa0900000000000000000
  | 9 => 0xcf8d02c9cc5c680100001000080000
  | 10 => 0x643c7487d587c8058000d800000000
  | 11 => 0xb36564714071c80c80004800000000
  | 12 => 0xd22ccd0750fb100000000000000000
  | 13 => 0xe18f3c94cddcd80000000000000000
  | 14 => 0x90930faa41eaf00000000000000000
  | 15 => 0x98fd132378d0280800010000000000
  | _ => 0

private def maskT0B58 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2bd0e9a364569805800258000c0000
  | 1 => 0x18e21d61ef10300c80044800000000
  | 2 => 0x3bcc1433d7eb800000080000000000
  | 3 => 0xbf600f3fb6100809001010000c0000
  | 4 => 0xaacbda125e03f80000200000000000
  | 5 => 0xb5fb7f276d4c400000400000000000
  | 6 => 0xade71ad3146ab80480804800000000
  | 7 => 0x3ac7b2e4c7b70801010010000c0000
  | 8 => 0x83ccc44dd4e76805820058000c0000
  | 9 => 0xbdc738be80b6800c84004800000000
  | 10 => 0x497b4497d376b80808000000000000
  | 11 => 0xf7965fb9cae14809100010000c0000
  | 12 => 0x1668c3eda9f89009200010000c0000
  | 13 => 0x65eee48a15a3b009400010000c0000
  | 14 => 0x76e4e07c9032a00c00004800000000
  | 15 => 0x75d8e87da871f000000010000c0000
  | _ => 0

private def maskT0B59 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xc1c38f05e4b0400200000000000000
  | 1 => 0x69856f3e34eb7809800058000c0000
  | 2 => 0xdf59d6649e01500000000000000000
  | 3 => 0x4ef7b94df391f80580005800000000
  | 4 => 0x3305c34f7237780000000000000000
  | 5 => 0x3e2ae72208cac80000000000000000
  | 6 => 0x3fffb859999c880000000000000000
  | 7 => 0xf815a2faf040500000000000000000
  | 8 => 0x805519ce6340500000000000000000
  | 9 => 0xded4ca49a320380000000000000000
  | 10 => 0xd8ff228f6921680000000000000000
  | 11 => 0xf1c4e3dcc421680000000000000000
  | 12 => 0xc76a5d6d6d87d80000000000000000
  | 13 => 0x1079fbc31001500000000000000000
  | 14 => 0xfb3d0249f177280000000000000000
  | 15 => 0xa960d0f9a920d00000000000000000
  | _ => 0

private def maskT0B60 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xcc3aad2528cb980000000000000000
  | 1 => 0xf049fe0ca061380000000000000000
  | 2 => 0x328ac0bd237780000000000000000
  | 3 => 0x9c40f93e2317400000000000000000
  | 4 => 0x5a7fbcc0f69dd80000000000000000
  | 5 => 0xfc7fdd640b42f80000000000000000
  | 6 => 0x71d0f8dc62872005800058000c0000
  | 7 => 0x8f6e2902fa01500000000000000000
  | 8 => 0xbbf08905b641000000000000000000
  | 9 => 0xb50b0bc6459c880000000000000000
  | 10 => 0x86bedf83b2fdb00000000000000000
  | 11 => 0xb9bf196e01eb800000000000000000
  | 12 => 0x6cf50271eb61380000000000000000
  | 13 => 0xb685358492fce00000000000000000
  | 14 => 0x1634079522eba00000000000000000
  | 15 => 0xbecfe00966c6380000000000000000
  | _ => 0

private def maskT0B61 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xf2104e54e101500000000000000000
  | 1 => 0xea07c40e21dd880000000000000000
  | 2 => 0x652445773a00000000000000000000
  | 3 => 0x5a7fbe556b9dd80000000000000000
  | 4 => 0xa2fe078a8627780000000000000000
  | 5 => 0x896e76e39977280000000000000000
  | 6 => 0xcf8616ad1a56400000000000000000
  | 7 => 0xe659f071b277280000000000000000
  | 8 => 0xf39d57f67941000000000000000000
  | 9 => 0xdfa5dce46016100000000000000000
  | 10 => 0x6666dce118cb980000000000000000
  | 11 => 0x5b2aa2c44bbde00000000000000000
  | 12 => 0x5f31d4a8a710300980009800000000
  | 13 => 0xc5ebe8c740aaa00000000000000000
  | 14 => 0xc6c347c9489dd80000000000000000
  | 15 => 0x4123c5789a41000000000000000000
  | _ => 0

private def maskT0B62 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x820ca6c44020380000000000000000
  | 1 => 0x8cf72dbbf1fdb00000000000000000
  | 2 => 0x1566efae2f6a580480004800000000
  | 3 => 0xd29cdfe0e9dd880000000000000000
  | 4 => 0xd4f58451e6cce00000000000020000
  | 5 => 0x7b941a68bc20380000000000000000
  | 6 => 0xfd6945257a9c880000000000000000
  | 7 => 0x61da2ba5ea9c880000000000000000
  | 8 => 0xdb142764006769b764000000000000
  | 9 => 0xe1e6bae4c0e8fc7ae4c00000000000
  | 10 => 0xc26eb6b2c02cf8f5b2c03000080000
  | 11 => 0x4279810580faa0220580b000000000
  | 12 => 0x5e8237b480ce126fb4800000000000
  | 13 => 0x1aa5ef2680f8e80f26800000000000
  | 14 => 0x29afb6a3c072539ea3c00000000000
  | 15 => 0xf2b61610c0a322b610c00000000000
  | _ => 0

private def maskT0B63 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x345f50e3017cc2c8e3000000028000
  | 1 => 0xc225cad782312570d7802000000000
  | 2 => 0xa8ec5340445d6efb40400000000000
  | 3 => 0x30dfc034880e2c1a34802000028000
  | 4 => 0x704b500010150be000000000028000
  | 5 => 0x2d52e40a08f394440802000000000
  | 6 => 0x2274711804df5a511c02000028000
  | 7 => 0x16ed9c2480c9c1fc24000000000000
  | 8 => 0x2bbb8d85809f302d84800000028000
  | 9 => 0xdf70f326c045cda124c02000028000
  | 10 => 0x3fa6a9c0407c0dabc4402000000000
  | 11 => 0x74adb77d4050d00d75402000000000
  | 12 => 0xb46fbd020021052512000000000000
  | 13 => 0x111f5380c0a80b93a0c00000000000
  | 14 => 0xa908c434400bc95c74400000000000
  | 15 => 0x350ae0a600df193226002000028000
  | _ => 0

private def maskT0B64 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x64d42411c0aba91711c02000000000
  | 1 => 0xb0b8f440801ff4b440802000000000
  | 2 => 0x155cc64280565f7a42800000000000
  | 3 => 0x94159ae3c0519ea9e3c03000000000
  | 4 => 0xb18b52a2403b0c12a2400000000000
  | 5 => 0xe9b968950090ea4895000000000000
  | 6 => 0xf7bb5e52408c4a2e52400000000000
  | 7 => 0xa6f392a240f18932a2400000000000
  | 8 => 0xd5e8950021fa2895000000000000
  | 9 => 0x7a30e89500f0fac895000000000000
  | 10 => 0xeec56c740fc4d26c7400000000000
  | 11 => 0x12fbc5e3c0cead55e3c00000000000
  | 12 => 0x306d076400246f5764000000000000
  | 13 => 0xc632ce85c056c3ae85c00000000000
  | 14 => 0x78304650095fb4465000000000000
  | 15 => 0x37affb9400dd322b94000000000000
  | _ => 0

private def maskT0B65 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x8abad6c740fc4d26c7400000000000
  | 1 => 0xa9e60d78042b6d0d7800000000000
  | 2 => 0xc200f46500e8328465000000000000
  | 3 => 0x3d306a42c09e295a42c00000000000
  | 4 => 0x2d0a74e280ce38d4e2800000028000
  | 5 => 0x3e554d534080281d53400000000000
  | 6 => 0x86f14d0100d5a63d01000000000000
  | 7 => 0x4877a8950095f19895000000000000
  | 8 => 0xc583f2a240362c42a2400000000000
  | 9 => 0x99820e778051745e77800000000000
  | 10 => 0xc80a8610c0234af610c00000000000
  | 11 => 0x37ee01a340551ba1a3400000000000
  | 12 => 0xd982e8670088df7a67002000000000
  | 13 => 0x9b948e5240eccf2e52400000000000
  | 14 => 0x703a9ae0c009bdcae0c00000000000
  | 15 => 0x63f1d30100fc95f301000000000000
  | _ => 0

private def maskT0B66 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xbf66f00000323f7000000000000000
  | 1 => 0xb5b96842804af64842800000000000
  | 2 => 0x53dd2e52407cfa6e52400000000000
  | 3 => 0xc200f465003fa7c465000000000000
  | 4 => 0x738ba6c74009d686c7400000000000
  | 5 => 0x2ddffe85c0ce697e85c00000000000
  | 6 => 0x5ec04842805234d842800000000000
  | 7 => 0x8fdf86c74053c356c7400000000000
  | 8 => 0x9f307895006235d895000000000000
  | 9 => 0x62154203807abdc203800000000000
  | 10 => 0x9508700000650b5000000000000000
  | 11 => 0x7e02d0d780a7d5c0d7800000000000
  | 12 => 0x5fc8fb6500ec1cb46500f000000000
  | 13 => 0x62154a374036575a37400000000000
  | 14 => 0xf61fc8950027332895000000000000
  | 15 => 0x2e946a37402e004a37400000000000
  | _ => 0

private def maskT0B67 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x74dd4895002f991895000000000000
  | 1 => 0x577b04b280e572e4b2800000000000
  | 2 => 0x1db2f9e2c024ecf9e2c00000000000
  | 3 => 0x968b346500c25ae465000000000000
  | 4 => 0x7915cc5200eb270e52002000020000
  | 5 => 0xfbd6bff100cc6fcff1000000000000
  | 6 => 0xe3b31a3740994caa37400000000000
  | 7 => 0x89486a3740d3344a37400000000000
  | 8 => 0x1488687f86b6040000000000000000
  | 9 => 0x9088a7d7f098c40080000000000000
  | 10 => 0x7c69285d42cc680000000000000000
  | 11 => 0xdb4336de2bde80d00000000080000
  | 12 => 0x197394240a43cc0080008000000000
  | 13 => 0x3fb044e52c73840580000000000000
  | 14 => 0x550923da20dbac0000000000000000
  | 15 => 0x66aad249bdfc640000000000000000
  | _ => 0

private def maskT0B68 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x17b6e17731ca4c0000000000000000
  | 1 => 0xbd7f277fa7eaa00d00004000140000
  | 2 => 0x88d3fcb95ad820048000c000240000
  | 3 => 0x784ccb8ba781a80d00004000440000
  | 4 => 0x8da048afd477e80d0000c000840000
  | 5 => 0xc8acb30758ba84040000c001040000
  | 6 => 0x9e5b5699e708280000000002000000
  | 7 => 0x2b99437ca482640080008004000000
  | 8 => 0xbaec6c7cc933c00d80004008040000
  | 9 => 0x43c879cb8d8aec0900008010000000
  | 10 => 0x750209148484840980000020000000
  | 11 => 0xaa90dafea01ca40000008040000000
  | 12 => 0x537a82d4f1c00c0d00004080040000
  | 13 => 0x8e5d05ba297acc040000c100040000
  | 14 => 0x53523d837d27cc0980008200000000
  | 15 => 0xaf0ac1b6ec84e00900000400000000
  | _ => 0

private def maskT0B69 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2d3e365c39c3e00d00004800040000
  | 1 => 0x95e6d25b84e7e00900009000000000
  | 2 => 0x3f9481094de1200000002000000000
  | 3 => 0x646a92c58582c40480000000040000
  | 4 => 0xf69fef3f1306240000000000000000
  | 5 => 0xd8916b195ed000000000000000000
  | 6 => 0x4ee38b6715aaa00000000000000000
  | 7 => 0x7f304c278060ec0000000000000000
  | 8 => 0x61da255aae9c880000000000000000
  | 9 => 0x6a52d5074e274c0000000000000000
  | 10 => 0xcf49c3f858eb240000000000000000
  | 11 => 0xe67202abf5eb240000000000000000
  | 12 => 0x645aa354b14ae00000000000000000
  | 13 => 0xd5e3d7b371300c0000000000000000
  | 14 => 0xdf2812ad5d9aac0000000000000000
  | 15 => 0x39f3df53e8ca200000000000000000
  | _ => 0

private def maskT0B70 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x5ca9a28f6921680000000000000000
  | 1 => 0x60daf1a6e18bc80000000000000000
  | 2 => 0xa01852320efa400000000000000000
  | 3 => 0x8bf6184912dd0c0000000000000000
  | 4 => 0x9fe590b097ac840000000000000000
  | 5 => 0x2e5310635bb9e80000000000000000
  | 6 => 0xd1dc0ee48609480980000000000000
  | 7 => 0x4af405729b300c0000000000000000
  | 8 => 0xf94f4ba8a750e00000000000000000
  | 9 => 0xb50b0bc6459c880000000000000000
  | 10 => 0x6731e3177f21680000000000000000
  | 11 => 0xecb63ab421302c0000000000000000
  | 12 => 0xfc660ddbaa8bc80000000000000000
  | 13 => 0xe38c165eb2274c0000000000000000
  | 14 => 0x2597f606bfcc680000000000000000
  | 15 => 0x1dff1e30ba0b000000000000000000
  | _ => 0

private def maskT0B71 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x378a622480300c0000000000000000
  | 1 => 0xce12d4ea8d300c0000000000000000
  | 2 => 0x652445773a00000000000000000000
  | 3 => 0xf94f406cb750e00000000000000000
  | 4 => 0x25dbe957f607c40000000000000000
  | 5 => 0xcbd1b44e8866c80000000000000000
  | 6 => 0x9a8f35773a8dec0000000000000000
  | 7 => 0xc24ce0951e9aac0000000000000000
  | 8 => 0xd7884712d5ac840000000000000000
  | 9 => 0xd8911e330ed000000000000000000
  | 10 => 0x905f0102e4dd0c0000000000000000
  | 11 => 0x4c9c43b37a77ac0000000000000000
  | 12 => 0x777a3f055bdec00d80004000040000
  | 13 => 0xc5ebe8c740aaa00000000000000000
  | 14 => 0x3596bb929ac840000000000000000
  | 15 => 0x39c07d58b50e00000000000000000
  | _ => 0

private def maskT0B72 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x50206bc310db280000000000000000
  | 1 => 0x7acef0580deb240000000000000000
  | 2 => 0x99a86747f21a200d00000000000000
  | 3 => 0xe13f2e7374fa400000000000000000
  | 4 => 0xfcd7e42f9ae78c0000002000020000
  | 5 => 0xa9b8d76fecdb280000000000000000
  | 6 => 0xeadfa4524b56c40000000000000000
  | 7 => 0x61da2ba5ea9c880000000000000000
  | 8 => 0x19154443535d207075800000000000
  | 9 => 0x36c95e9364dfff10c0100000000000
  | 10 => 0x2846c549cc7cda0430900000000000
  | 11 => 0x17a33758ffe22c7e010c800000000
  | 12 => 0x48788f91046168cd61108000070000
  | 13 => 0xfc067734305f457b3100b000040000
  | 14 => 0x83038b87483b7708e0800000000000
  | 15 => 0x388557aac86a29dcf0804800040000
  | _ => 0

private def maskT0B73 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xc1d258cb3b6561e0d4804800040000
  | 1 => 0xf7692a19b37ef218f5804800040000
  | 2 => 0xea2daeb3b56116ee25000000040000
  | 3 => 0x1b37eb76b25c5ceac1809000040000
  | 4 => 0x398060a27653a74601900000040000
  | 5 => 0x252a66993f0cb914b5900000040000
  | 6 => 0x131d7273c8b431e0580d800000000
  | 7 => 0xc84f653449b309fbd4904800040000
  | 8 => 0xdd0274992294945681000000000000
  | 9 => 0xd1680feb0407d04d50004800040000
  | 10 => 0x689cf7c6ad74e62a10000000040000
  | 11 => 0x4db905786b3a1fb841000000000000
  | 12 => 0xe0ae0bbad8734383e0104800040000
  | 13 => 0xf67080c2b12adb9325909000040000
  | 14 => 0x9a83430a8a8b2beee0100000000000
  | 15 => 0x6d2c40a0b0052743c4100000040000
  | _ => 0

private def maskT0B74 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x76c0edca90c669e581804800000000
  | 1 => 0xb2115fbf8199e94ba590d800000000
  | 2 => 0x2ca6ee06c6d4ca8521004800040000
  | 3 => 0x4db57ba185f7ad2bd0800000040000
  | 4 => 0xb7f09158b16a7b89b5904800000000
  | 5 => 0x9747b1e98e89df5405000000000000
  | 6 => 0xa0666e036640500405000000000000
  | 7 => 0x9e715af4ef313fa445100000000000
  | 8 => 0xacb9e979f43b26a741800000000000
  | 9 => 0x6b37997462fc71b405000000000000
  | 10 => 0x2365e270dd04683854800000000000
  | 11 => 0x93506c42e6577e371100000000000
  | 12 => 0x2454e1491c30c52b65800000000000
  | 13 => 0x54c82f562ea1aac445100000000000
  | 14 => 0xcd1dfad200603df1b5000000000000
  | 15 => 0x9135ecaf9b5bcc5b10000000000000
  | _ => 0

private def maskT0B75 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xde5695aadd84fb4470800000000000
  | 1 => 0xe2c6d9685ae4437bb1909000000000
  | 2 => 0xe6a673201fd4a78301000000000000
  | 3 => 0xbbced75aeece603741800000000000
  | 4 => 0x4c0bbfbf14b7faf821000000000000
  | 5 => 0xda99303d06d9495304900000000000
  | 6 => 0x4f5ecef1b5a0459b04000000000000
  | 7 => 0xbfe57cc8c073697445100000000000
  | 8 => 0x746d37d5a109372405000000000000
  | 9 => 0x5ea85cc3be9293b405000000000000
  | 10 => 0x2b1050ee5c25f59430900000000000
  | 11 => 0x773ba4e3c13907bf15000000000000
  | 12 => 0x2993fffea0d679fb10000000000000
  | 13 => 0x5cf14b9b1ce5408b50100000000000
  | 14 => 0xcfa00aa4b365eb3b65800000000000
  | 15 => 0x2b2de8de6fa6cb1040100000000000
  | _ => 0

private def maskT0B76 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2b85d20e580b605761900000000000
  | 1 => 0x935cc865e6cd02a0b590d800000000
  | 2 => 0x89c64eb81d62479c11900000000000
  | 3 => 0xca752da73310061b50100000000000
  | 4 => 0xb7df1032a7b4f56b25900000000000
  | 5 => 0x153ad495585c6f5b50100000000000
  | 6 => 0x89f67e5b6b6c40c774100000000000
  | 7 => 0x2454eed0e7c95a9b65800000000000
  | 8 => 0x98ab56338efb93b821000000000000
  | 9 => 0x9d242c6a975b8d5774100000000000
  | 10 => 0x91a22d9a3548017854800000000000
  | 11 => 0x5f7d6874d6d8300b25900000000000
  | 12 => 0x4a4eea5c063f8e800000d000000000
  | 13 => 0xe041aab55b4b141f60800000000000
  | 14 => 0x9135e950ba043e4b10000000000000
  | 15 => 0xeeeaa7bd5b953f1371100000000000
  | _ => 0

private def maskT0B77 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1c99b8d1ce91855861100000000000
  | 1 => 0x385feda7a632258ef1109000040000
  | 2 => 0xe69820e4ace8d2ed05900000000000
  | 3 => 0x192b181d7c98fcd734000000000000
  | 4 => 0xb2791ad5f017261771805800050000
  | 5 => 0x6adcf6409d0ed52821000000000000
  | 6 => 0xe7e526156186b33c51800000000000
  | 7 => 0xb2fbd15d54a72e9430900000000000
  | 8 => 0x593f0593f0e745e9a4000000000000
  | 9 => 0xc6689c668956ff589e400000000000
  | 10 => 0x50a0250a02cab09030600000000000
  | 11 => 0x5c6b35c6b31212cb24208000000000
  | 12 => 0x9de679de67d63dfaec600000000000
  | 13 => 0x43980439803bbcc426208000030000
  | 14 => 0x3d6363d6365980f774609000000000
  | 15 => 0x2a3762a37654e50d5c400000000000
  | _ => 0

private def maskT0B78 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x9ab0f9ab0f92c27f1a000000000000
  | 1 => 0x5cf264cf2616220c0c600000040000
  | 2 => 0x91ef191efbec48326000000040000
  | 3 => 0xe71b1e71a96731832201200040000
  | 4 => 0xb2c80a2c82ba3444be000000000000
  | 5 => 0xc3ffac3ffebe7c66f8000000000000
  | 6 => 0x7343873430d9e8fc82601200000000
  | 7 => 0xe1488f1498abe926a2201200040000
  | 8 => 0x439d7539f71fb0a7ba001200040000
  | 9 => 0x90cb280cf295f268aa000000000000
  | 10 => 0x6b5786b5f8fcc269c0001200000000
  | 11 => 0xc4f4ed4e4e06d7e280201200000000
  | 12 => 0x2c7e83c5e8d9dd4a88601200000000
  | 13 => 0x8260a9220afe91403a601200040000
  | 14 => 0xbdbcead3cee9f347ee600000040000
  | 15 => 0x37c8126c81a82fd7f8200000040000
  | _ => 0

private def maskT0B79 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x34ab526ab5a12b08b8001200000000
  | 1 => 0x6ed316ad314adf7c24000000000000
  | 2 => 0xc169cd969c6287ea36600000040000
  | 3 => 0x70c7050c70fae0420e400000040000
  | 4 => 0x949f0d49f013887622000000040000
  | 5 => 0xeb6286b62843fa2ee6600000000000
  | 6 => 0x5144b5144bcb20ff4a200000000000
  | 7 => 0x562f8562f8e5ae6200000000000000
  | 8 => 0x3f2823f282f87a3378000000000000
  | 9 => 0xacc62acc6261d87994600000000000
  | 10 => 0x890608906bbbc8abc400000000000
  | 11 => 0x11ef411ef4549e6030600000000000
  | 12 => 0xb7fb1b7fb13b14baec600000000000
  | 13 => 0xe0870e087e3b6e5c6000000000000
  | 14 => 0xf437bf437bbfeba378000000000000
  | 15 => 0x9b8209b820dd7cef1a000000000000
  | _ => 0

private def maskT0B80 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xeff6eeff6e19754956000000000000
  | 1 => 0x2c7912c7914d65f030600000000000
  | 2 => 0x43e4043e466d99060400000000000
  | 3 => 0x796c0796cd6f0f6de400000000000
  | 4 => 0x6aaeb6aaeb4d4cbf2a600000000000
  | 5 => 0x76d2b76d2b47bb5a8c200000000000
  | 6 => 0xfc6e0fc6e3ea89244400000000000
  | 7 => 0xa96cea96ce3e5eac52600000000000
  | 8 => 0xc9b9cc9b9ce7b43318400000000000
  | 9 => 0xe3c34e3c3416c8b6de400000000000
  | 10 => 0x6c2116c211a976eabc400000000000
  | 11 => 0x7a7c97a7c915132994600000000000
  | 12 => 0xe0e66e0e66509cb6ee200000000000
  | 13 => 0x27c3027c300d046adc000000000000
  | 14 => 0x5e6985e6980e8a0c52600000000000
  | 15 => 0xceef4ceef4baf01328200000000000
  | _ => 0

private def maskT0B81 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x63e7f63e7fde6629f4200000000000
  | 1 => 0xd60b0d60b0e9b8050200000000000
  | 2 => 0x25a3025a3f7605050200000000000
  | 3 => 0x9e8eb9e8eb238eaf7a400000000000
  | 4 => 0x368c0368cf8ce0596200000000000
  | 5 => 0x9d1a19d1a19a2c2c62000000000000
  | 6 => 0x79145791451bccdc02400000000000
  | 7 => 0xa19b2a19b26553a8fa200000000000
  | 8 => 0x62d5062d50f4ee3c32200000000000
  | 9 => 0x288b0288b00f1a69c4400000000000
  | 10 => 0x3360633606aaf8868e600000000000
  | 11 => 0x9f4029f402780aac32200000000000
  | 12 => 0x3880d3880d3999464a004000000000
  | 13 => 0xd04cdd04cd348b3f1e201200000000
  | 14 => 0x397e7397e7f1f1d03e200000040000
  | 15 => 0x49d4449d44ef22eadc000000000000
  | _ => 0

private def maskT0B82 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x6b7796b779cab09a8c200000000000
  | 1 => 0x75ba775ba72b112f1a000000000000
  | 2 => 0x2e1e92e1e9ea423162200000000000
  | 3 => 0xf4cbdf4cbd41d8b030600000000000
  | 4 => 0x85e7185e71d4570d74000000060000
  | 5 => 0xbf6b7bf6b7da64f994600000000000
  | 6 => 0x25a3025a3e2268abc400000000000
  | 7 => 0x18a9918a999052c16e200000000000
  | 8 => 0x1a30011ad603ea21a3000000000000
  | 9 => 0x8f40614c173ed108f400000000000
  | 10 => 0x54d00f3baee1b7e54d000000000000
  | 11 => 0x3e74094e28914683e7403000000000
  | 12 => 0x58f000effd5855258f000000000000
  | 13 => 0x5a940c7531bd4d35a9400000000000
  | 14 => 0x735400aec7a37c8735403000080000
  | 15 => 0x762401bcef5681c762409000000000
  | _ => 0

private def maskT0B83 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x76140965a17177f5e14010000a8000
  | 1 => 0x56b406fdfaf41b856b400000000000
  | 2 => 0xc2007a4c991b9d0c2000000000000
  | 3 => 0x7cc40c6653ae28b54c4010000a8000
  | 4 => 0x273413891271db30f34030000a8000
  | 5 => 0x3e8422ac0c6e06c9684010000a8000
  | 6 => 0xfb704e30b213236fb7002000000000
  | 7 => 0x33308c68ee6c35c9b30010000a8000
  | 8 => 0xe58509628280c03cd84030000a8000
  | 9 => 0xc4920a6451daad36c90010000a8000
  | 10 => 0x2c4057249caf1b2ac0030000a8000
  | 11 => 0xea78030cf126a486a7000000000000
  | 12 => 0xd9500d193a760cef140030000a8000
  | 13 => 0x16940de2e9261393eb4030000a8000
  | 14 => 0xb4c40e5f9b073e8348400000000000
  | 15 => 0xcbb000bbce04d59e330030000a8000
  | _ => 0

private def maskT0B84 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xec100bc10dec1026d1000000000000
  | 1 => 0x29e404fe7108d9603e4030000a8000
  | 2 => 0x1f5401bd4ddce561b5402000000000
  | 3 => 0x472009e44bb3d266720010000a8000
  | 4 => 0xa364010e66c2447b36402000000000
  | 5 => 0x226403d9027c873026402000000000
  | 6 => 0x62e40697831564ca2e402000000000
  | 7 => 0x39c0066eb59230039c000000000000
  | 8 => 0x77200448286f2a8772000000000000
  | 9 => 0x58f004f9783554658f000000000000
  | 10 => 0x15e0029def5fe9915e002000000000
  | 11 => 0x7544073f62bed56754400000000000
  | 12 => 0x796404e957e1579796400000000000
  | 13 => 0x4c840c233c373834c8400000000000
  | 14 => 0xe4409c832430550e4400000000000
  | 15 => 0x37840230e249d7a378400000000000
  | _ => 0

private def maskT0B85 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x16100318f58e57d161000000000000
  | 1 => 0x23f00c59de6eacb23f000000000000
  | 2 => 0x3784031e54d1355378400000000000
  | 3 => 0x58f00c12a9b864f58f000000000000
  | 4 => 0x3ba4062f009719c3ba400000000000
  | 5 => 0x40a40a29b40c1e840a400000000000
  | 6 => 0x56900fd594da5c4569000000000000
  | 7 => 0xf88002362496dfcf88000000000000
  | 8 => 0x378408da4406a01378400000000000
  | 9 => 0xc200367436e7780c2000000000000
  | 10 => 0x2db406120720d122db400000000000
  | 11 => 0x79640f2d4799a8e796400000000000
  | 12 => 0x75440b94db8a329754400000000000
  | 13 => 0x3854083a18569f7385400000000000
  | 14 => 0x14740708d10294e147400000000000
  | 15 => 0x26402b5d22a6fb026400000000000
  | _ => 0

private def maskT0B86 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x40a40c9acca2a3340a400000000000
  | 1 => 0x23f00fd2957153323f000000000000
  | 2 => 0x35e00b4120376e235e000000000000
  | 3 => 0x3784031e5406a01378400000000000
  | 4 => 0x39c0050c53a793e39c000000000000
  | 5 => 0x1854028912c7da4185400000000000
  | 6 => 0x40a40a2114c82af40a400000000000
  | 7 => 0x79640b70ac18c82796400000000000
  | 8 => 0x1a30042a45e36331a3000000000000
  | 9 => 0x56b40c835d2cf4e56b400000000000
  | 10 => 0x9b2401968149fbf9b2400000000000
  | 11 => 0x2db409c832e5f2b2db400000000000
  | 12 => 0x284003609db137a28400d000000000
  | 13 => 0x56b40129b7330b656b400000000000
  | 14 => 0x6d100696f07387e6d1000000000000
  | 15 => 0x3014049272bb1cd301400000000000
  | _ => 0

private def maskT0B87 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x18540c7d91329cd185400000000000
  | 1 => 0x2fd009d81dcbf292fd000000000000
  | 2 => 0xf84000656c4c63ff84000000000000
  | 3 => 0x23f0012eb60389d23f000000000000
  | 4 => 0x40a4086f265feb160a402000020000
  | 5 => 0x772002f3f070d50772000000000000
  | 6 => 0xfc34051e25206265434030000a8000
  | 7 => 0x77200ab76c6f2a8772000000000000
  | 8 => 0xebeca6184a16b938a6800000000000
  | 9 => 0xc4b0f91b0f9da37550000000000000
  | 10 => 0xa24d9a2859b110700c800000000000
  | 11 => 0x4bd3bce53b3679a858007800000000
  | 12 => 0xa4a721c276a89a2b8800000000000
  | 13 => 0x772e659a6626a702e8800000000000
  | 14 => 0xd1d012dd0c73a41fc000000000000
  | 15 => 0xe6da9e9fa926d569f200f8000b0000
  | _ => 0

private def maskT0B88 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2aadd1ee5d98196344802000000000
  | 1 => 0xc7f3c763bcb51fc91c800000000000
  | 2 => 0x91dc42014450b1ab1c800000000000
  | 3 => 0x43e75914751efdcf2a000000000000
  | 4 => 0xef8ac8c2ac0fc8743a000000000000
  | 5 => 0xbb4cd05e4c6872b3ea807800080000
  | 6 => 0xfd3b86fd3aa35ef32e80e800080000
  | 7 => 0xee91e8211a3c4c9cc8008000080000
  | 8 => 0xd13360f1be7eb41fe2809000000000
  | 9 => 0xad5cda0d5df85f5ad8808000080000
  | 10 => 0x81cb048210d4224c9e806800000000
  | 11 => 0x1de6f60e2f02fb0fd0008000080000
  | 12 => 0xcc981ae701771d2e2e00e800080000
  | 13 => 0x7832c00aac9a8d2f88807800080000
  | 14 => 0x4d4aff582fcefc9b8e800000000000
  | 15 => 0xd71e4a95e4ca6fe7e0000000000000
  | _ => 0

private def maskT0B89 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x9c759927573537106008000080000
  | 1 => 0x384bef8e3efdbe061a80e800080000
  | 2 => 0x8f0b9e7439777d84a4800000000000
  | 3 => 0x26fce653ce0ffb3e7c008000080000
  | 4 => 0xd158ff318fa83ff0a4009000000000
  | 5 => 0x72580a87808107b4a200e800080000
  | 6 => 0x4c347ab5c766b37a7680f800000000
  | 7 => 0xe5ab130ab174e34d50007800080000
  | 8 => 0x44d7a54ffadfa7e102800000000000
  | 9 => 0x7d247464c7bb35e3b6800000000000
  | 10 => 0x59d526d9d299d01344800000000000
  | 11 => 0xe302fe3caf2f3e800c800000000000
  | 12 => 0x205710bdf187a0e2b8800000000000
  | 13 => 0xf1f93dab93b66022b4000000000000
  | 14 => 0xb279ea299ed9b2610e000000000000
  | 15 => 0x90eeb2126b1f0f3b1c800000000000
  | _ => 0

private def maskT0B90 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xfce64b62641a47f4ac00f800000000
  | 1 => 0x72f93c331327f0ab1c800000000000
  | 2 => 0xd8b6124b6c225a1fc000000000000
  | 3 => 0x1bf168e91650b67956000000000000
  | 4 => 0x3f4223f422e5aa3000000000000000
  | 5 => 0xe8cb9dc8395ff33344800000000000
  | 6 => 0xf20b84ac3836737b8c800000000000
  | 7 => 0x2b1268a3a6a0504a12800000000000
  | 8 => 0x8642b8962b2511c0f2000000000000
  | 9 => 0x6e78a4ad0ac03f924a800000000000
  | 10 => 0xd5834558ca9e6348000000000000
  | 11 => 0xab9ec90f6ccffeb3b6800000000000
  | 12 => 0xa201e86a9ebc4f624a800000000000
  | 13 => 0xeeef274af2db2569a4000000000000
  | 14 => 0xe1a6d4046dd100fa1e000000000000
  | 15 => 0x4e48541685427110f2000000000000
  | _ => 0

private def maskT0B91 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x86015a2615e1f39246000000000000
  | 1 => 0x67e46c92468176faec000000000000
  | 2 => 0xc4b37db73769b891fc000000000000
  | 3 => 0x9c572325f245014ae0800000000000
  | 4 => 0x7c113389172441344800000000000
  | 5 => 0xed8924c6927f822a1e000000000000
  | 6 => 0x3d839836b91b1afbee800000000000
  | 7 => 0x9dbf10f3fbd341192806800000000
  | 8 => 0x457334a9b3df2950fe800000000000
  | 9 => 0x231c2651c0aab2246000000000000
  | 10 => 0xe9ee8634e8b266c8aa000000000000
  | 11 => 0x293a5971a5037c6be2000000000000
  | 12 => 0x8719aba51abdcf43d480b800000000
  | 13 => 0xbf95651f5698c03ee6000000000000
  | 14 => 0x3f4057ce05db53743a000000000000
  | 15 => 0x112423aac269b242b8800000000000
  | _ => 0

private def maskT0B92 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x59032dc4b2c3cd4854800000000000
  | 1 => 0x7ed6ccf1ece962fb1c800000000000
  | 2 => 0x5d14888148f0264d50000000000000
  | 3 => 0x626606ee63a78500c800000000000
  | 4 => 0xc31802158020a1a72400f800090000
  | 5 => 0xff55675f565038c8aa000000000000
  | 6 => 0xff72e7a3aed17fa854800000000000
  | 7 => 0xb57a98eda9330a2bba008000080000
  | 8 => 0xcc6ef1357513575a08000000000000
  | 9 => 0xcf358eb367eb367197000000000000
  | 10 => 0xd90c3f0d33f0d3e2b000000000000
  | 11 => 0xcf3be5a7d7fa7d7fc500a000000000
  | 12 => 0x837244791947919000000000000000
  | 13 => 0xab7b10128f0128fd7a000000000000
  | 14 => 0x4299d6a4306a430e24000000000000
  | 15 => 0x16521405aa405aa42c000000000000
  | _ => 0

private def maskT0B93 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xd31f0f5204d52041e4002000040000
  | 1 => 0x81041e4666ec6667a4004800000000
  | 2 => 0xaa627e569ae569a88c000000000000
  | 3 => 0xd086481524e1524841002000000000
  | 4 => 0xb955f5e8903e890f33002000000000
  | 5 => 0xe78eb43fe143fe100f000000000000
  | 6 => 0xe88bcfb084bb085775008000080000
  | 7 => 0x291e3e136b43369d9c00a200000000
  | 8 => 0x8c0541bf3e1bf3a542000000000000
  | 9 => 0x70cb7c19c2639caccd00a200000000
  | 10 => 0x5744a7796277972385000000000000
  | 11 => 0x256bf762c6762e662c000000000000
  | 12 => 0xa1b11f8bbd1abfdf7f002200080000
  | 13 => 0x40daa6e7a10e721bba00a000080000
  | 14 => 0xe0153d49b4168b42d9008200000000
  | 15 => 0x9824d69531697314b9008000080000
  | _ => 0

private def maskT0B94 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x42955b4a48d4e487e800a000080000
  | 1 => 0x66be703a8b8128bf94000200080000
  | 2 => 0xf8d54b24b4934b4279002000000000
  | 3 => 0x73c8df736677366112000200080000
  | 4 => 0xb6a2daf3e6cb3e6385002000000000
  | 5 => 0x5fd6bc105cc905ccff000000000000
  | 6 => 0xf574b050d1150d1a46008000080000
  | 7 => 0xcd2d64529945299030002000000000
  | 8 => 0x171305c4b6dc4b6733008000080000
  | 9 => 0x828f012f8112f81351000000000000
  | 10 => 0x4299d150c3150c3a95000000000000
  | 11 => 0xd96479cb779cb77423000000000000
  | 12 => 0xfd00ae3e4be3e4b423000000000000
  | 13 => 0xa3672d64fbd64fb092000000000000
  | 14 => 0xc91d8075d5075d5a08000000000000
  | 15 => 0xb940ff7931f7931de7000000000000
  | _ => 0

private def maskT0B95 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xc6cf5150c3150c3a95000000000000
  | 1 => 0xf2d3adf96adf96a08000000000000
  | 2 => 0xd932ac78eac78e4be000000000000
  | 3 => 0xc01b32580125801351000000000000
  | 4 => 0xe56561b1a81b1a8092000000000000
  | 5 => 0xa03fb687e9687e9a95000000000000
  | 6 => 0x74c8ea4529a45296bc000000000000
  | 7 => 0x65e9cc59f5c59f5eb9000000000000
  | 8 => 0xfdff251b7d51b7db82000000000000
  | 9 => 0x41cca5128851288a07000000000000
  | 10 => 0x3bc1ff4350f4350a9a000000000000
  | 11 => 0xcbae1f390ef390e423000000000000
  | 12 => 0x8a62bdf559df559e24000000000000
  | 13 => 0x945e1e011ce011cd75000000000000
  | 14 => 0x59a96d6d9dd6d9deb6000000000000
  | 15 => 0xf337774065740654be000000000000
  | _ => 0

private def maskT0B96 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x521249c6c29c6c23c3000000000000
  | 1 => 0x2799f24a6624a66eb6000000000000
  | 2 => 0x5b3fad3bfef3bfefd7002000000000
  | 3 => 0x2e1065c9037c903dd000a000080000
  | 4 => 0x54c62cfb1dcfb1d42c000000000000
  | 5 => 0x9ddba5e3845e384956000000000000
  | 6 => 0xff42b1b1a81b1a8de7000000000000
  | 7 => 0x94d31c5a04c5a04351000000000000
  | 8 => 0x4e4a42409e8609e15c00a200000000
  | 9 => 0x444e5b8adcb8adcde8000000000000
  | 10 => 0xa7a749499594995de7000000000000
  | 11 => 0xafed68eab28eab2d7a000000000000
  | 12 => 0x704148439f8c39fdf5000800000000
  | 13 => 0xa82380a7930a79377d000000000000
  | 14 => 0xd093477ba477ba4a95000000000000
  | 15 => 0xd7954ac47fac47f956000000000000
  | _ => 0

private def maskT0B97 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xb0b7c9dd2b9dd2ba37000000000000
  | 1 => 0x96acd75360753603cc000000000000
  | 2 => 0x9b0fc18be318be321a000000000000
  | 3 => 0x60d50d5d41d5d41959000000000000
  | 4 => 0x1a94ea3fbd83fbdad3000000020000
  | 5 => 0x3983ec77dcc77dc076000000000000
  | 6 => 0x7e69443576435763c3000000000000
  | 7 => 0x70acf6ad566ad56000000000000000
  | 8 => 0xf42e6da1deda6e62e4000000000000
  | 9 => 0xa9f6d0b57a7d16dd4e000000000000
  | 10 => 0xf522c5a4075982caca000000000000
  | 11 => 0x30e0a7da9d4161ad1810a000000000
  | 12 => 0x625ad6962ba01adc24000000000000
  | 13 => 0x3e2b7185af928b7aca000000000000
  | 14 => 0x10085f34d4f8685e86000000000000
  | 15 => 0xd4df4e2688787f4aca000000000000
  | _ => 0

private def maskT0B98 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x788378f4b690e37e86000000000000
  | 1 => 0x5aae44b95106aeb7c00a200040000
  | 2 => 0xf86369921bea436aa200c800030000
  | 3 => 0xdb283a875aaca83058000200030000
  | 4 => 0x24db027eec0b3a05de100200030000
  | 5 => 0x4e1e76ddb4ccfe782e000000000000
  | 6 => 0x50346943335195673a100200030000
  | 7 => 0xf9b38c04a09873941c002000000000
  | 8 => 0x587eba9a5ecf7f9670108000030000
  | 9 => 0x2ef6ad81d497d6e5b200a200000000
  | 10 => 0xf0be669bd218a64e8102000000000
  | 11 => 0x68de8b535f90ff8b82000000000000
  | 12 => 0x1c0e2cacfcb46c2e86000000000000
  | 13 => 0xf86a03d85a6a6e0920000000000000
  | 14 => 0x337bfb35189032fe34100000000000
  | 15 => 0x3312ba2b51f043be34102000000000
  | _ => 0

private def maskT0B99 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x68e399da2aef829054108200000000
  | 1 => 0xeb04a5a19f3d85a06c10a000030000
  | 2 => 0x72067630e0284673ac002000000000
  | 3 => 0xdc59ff28d754f8f79a108000030000
  | 4 => 0xcc8b717e4d29aa7d52100200030000
  | 5 => 0x6398abdfc969d9afe4108000030000
  | 6 => 0xf7fa37e8f1175a358a008000030000
  | 7 => 0x2eb65a6ba65fb65d10008000030000
  | 8 => 0x68ce3ee92278de210102000000000
  | 9 => 0xdfcf1368c47eaf1016002000000000
  | 10 => 0xe596f939766776f82e000000000000
  | 11 => 0xdc252797c61e652c24000000000000
  | 12 => 0x1f271865159dc7182e000000000000
  | 13 => 0x51e0ca4a9b0401cc5e10a000030000
  | 14 => 0x5d28c96bedb128cec0000000000000
  | 15 => 0xacb5997c1904759a8c000000000000
  | _ => 0

private def maskT0B100 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xeeee1719ae424e1aca000000000000
  | 1 => 0xbf8325b252d16326ee000000000000
  | 2 => 0x89f78bf5b6c957840a000000000000
  | 3 => 0x1e66337e7074e636a8000000000000
  | 4 => 0xf4920cfb7a9e1206a8000000000000
  | 5 => 0x3b8ff9e6ea972ffaca000000000000
  | 6 => 0x1c4daa1ab2e18cafdc100000000000
  | 7 => 0x92c6ecd4647aa6ee86000000000000
  | 8 => 0xba8c73774352ec7e86000000000000
  | 9 => 0xa403ecc7d96223ec62000000000000
  | 10 => 0x8e3bac82e4362b4b8100000000000
  | 11 => 0x7cf0df7cbb52b0d2e4000000000000
  | 12 => 0x6aecaa7cb96e8ca046000000000000
  | 13 => 0x717487a1d471748000000000000000
  | 14 => 0x2a751c44bde3751c90000000000000
  | 15 => 0x222aa06cb6ce2aaec0000000000000
  | _ => 0

private def maskT0B101 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xd0c562cfc0d0c56000000000000000
  | 1 => 0x29a251f5f1ab42582e000000000000
  | 2 => 0x6216c5ed120896c6a8000000000000
  | 3 => 0xf4920e6ee79e1206a8000000000000
  | 4 => 0x1a8c6f8cae5e4c644c000000000000
  | 5 => 0xe8375650bbc9365010102000000000
  | 6 => 0xe5668cb2f83de68d88000000000000
  | 7 => 0x9362362f2b51223c24000000000000
  | 8 => 0xb3636498a81fc36aca000000000000
  | 9 => 0x3e2b76d70a928b7aca000000000000
  | 10 => 0x3abcacb5d2d2dcae86000000000000
  | 11 => 0xcc78d018e17bd9d15a10a200000000
  | 12 => 0x1c9d65ae6a7d3c649a102800000000
  | 13 => 0xe6147a6cbc24547c24000000000000
  | 14 => 0x21fd84416421fd8000000000000000
  | 15 => 0x7cedb0b57a3c4db40a000000000000
  | _ => 0

private def maskT0B102 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x59db4606f25dbb4046000000000000
  | 1 => 0x4754d00a2a6d74d2a2000000000000
  | 2 => 0x553b0c7d61e9da0bce100000000000
  | 3 => 0x7febae7ee2fc0aa83e100000000000
  | 4 => 0xe986a8287e4427aada102000020000
  | 5 => 0xa0bc7f5e32263c7868000000000000
  | 6 => 0xe49a5e473e483a5aca000000000000
  | 7 => 0x7883760bf290e37e86000000000000
  | 8 => 0x33e204ca19d621333e200000000000
  | 9 => 0x7d42003a068d62c7d4200000000000
  | 10 => 0x9be80b4621491b89be800000000000
  | 11 => 0xf2a0cc9f6a6f933f2a03000000000
  | 12 => 0x97c8049272f0f9497c800000000000
  | 13 => 0xc200a88cb4956b0c2000000000000
  | 14 => 0x8a6003964c5fbfe52600d800000000
  | 15 => 0xf00800b401747aff00800000000000
  | _ => 0

private def maskT0B103 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x77200448286f2a8772000000000000
  | 1 => 0x9be807203e0c41d9be800000000000
  | 2 => 0x1a20065e12d362e9a20e800080000
  | 3 => 0x546a0401e570317646a0b000000000
  | 4 => 0x2a6a0426ef27f283a6a09000000000
  | 5 => 0xc2007a4c991b9d0c2000000000000
  | 6 => 0x230200d33d0a945230200000000000
  | 7 => 0xcc80058baf5a95fdc8009000000000
  | 8 => 0xcbe818b60bbc25b03e804800000000
  | 9 => 0xdc82c226ee862b55c80d800000000
  | 10 => 0x24e04b81c958b9934e009000000000
  | 11 => 0x932085650b69b91cb200d800000000
  | 12 => 0xc661062014e592d0e6004800000000
  | 13 => 0x64820369b4df21e3c800d800000000
  | 14 => 0x7d4409ced784e79b54004800000000
  | 15 => 0x296000d5b71fb13a96800000000000
  | _ => 0

private def maskT0B104 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x6f18077f10de503a70804800000000
  | 1 => 0xf6680179397a54c3e4804800000000
  | 2 => 0xe8a00da1932c7a468e000000000000
  | 3 => 0xbee00904a2959cf766004800000000
  | 4 => 0xeae0096636a2f6b6be000000000000
  | 5 => 0xcfe80ac29a1a78a05e804800000000
  | 6 => 0x556801288a5a71a416809000000000
  | 7 => 0x24280330e88f4b0f4280d800000000
  | 8 => 0xefa8033c9a0a362efa809000000000
  | 9 => 0x4daa0138c3be6137daa09000000000
  | 10 => 0xc4e202acf631c8314e209000000000
  | 11 => 0xc3ea02c8e3794f0c3ea00000000000
  | 12 => 0xcfca011ed626cdfcfca00000000000
  | 13 => 0x3fc208aac0875173fc200000000000
  | 14 => 0xb8ea0c3fb3849f3b8ea00000000000
  | 15 => 0x6be001ceea629366be000000000000
  | _ => 0

private def maskT0B105 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x10e001bfcec0b1410e000000000000
  | 1 => 0xecc8082451c600decc800000000000
  | 2 => 0x6be000e05cfa7196be000000000000
  | 3 => 0x97c8086f2610c8997c800000000000
  | 4 => 0x48e202a6fc2770848e200000000000
  | 5 => 0x10e00e7375b6e3910e000000000000
  | 6 => 0xbaaa0b7b2678647baaa00000000000
  | 7 => 0xd7a20541d00df24d7a200000000000
  | 8 => 0x6be00b244c2de4d6be000000000000
  | 9 => 0xc200367436e7780c2000000000000
  | 10 => 0x54220798094fe72542200000000000
  | 11 => 0xc3ea0d7e0fcf8b5c3ea00000000000
  | 12 => 0xcfca09c793dc112cfca00000000000
  | 13 => 0x62c009632b333d262c000000000000
  | 14 => 0xa42a00586b8be81a42a00000000000
  | 15 => 0xb8ea00e69a7c4c0b8ea00000000000
  | _ => 0

private def maskT0B106 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3fc20fb7f98373a3fc200000000000
  | 1 => 0xc3ea0cd8ee42d2dc3ea00000000000
  | 2 => 0xdf2a0d48a9dbb08df2a00000000000
  | 3 => 0x6be000e05c2de4d6be000000000000
  | 4 => 0xfc2804722ed060cfc2800000000000
  | 5 => 0xa42a027d61df1f6a42a00000000000
  | 6 => 0x33e20ea8e87843b33e200000000000
  | 7 => 0xe0e809f0d9447fce0e800000000000
  | 8 => 0x10e00129b73c3c710e000000000000
  | 9 => 0x2f220d095343c2e2f2200000000000
  | 10 => 0xe8804b23d84f5c0e8800000000000
  | 11 => 0x77200891018050e772000000000000
  | 12 => 0x2c2805870511e43fc280d000000000
  | 13 => 0x2302070770cd84b230200000000000
  | 14 => 0x6be00431cb3d6176be000000000000
  | 15 => 0xa3480311f538f47a34800000000000
  | _ => 0

private def maskT0B107 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x87280c5adf20cda872800000000000
  | 1 => 0xe0e80da592635efe0e800000000000
  | 2 => 0xf46007c1a5ddda2f46000000000000
  | 3 => 0xcfca058004a1b1ecfca00000000000
  | 4 => 0x40600b00f804ce5a8600e8000a0000
  | 5 => 0x7b00055739e16cd7b0000000000000
  | 6 => 0xfa220828b501424b22204800000000
  | 7 => 0x54220a645165bed542200000000000
  | 8 => 0xb18940000030f34e86000000000000
  | 9 => 0xf111000000ad995cd2000000000000
  | 10 => 0x13e12000001cd66030000000000000
  | 11 => 0xa45ba0200000e787b5800200000000
  | 12 => 0x9060900000cb89e9b1800000000000
  | 13 => 0x1f8f2000004bac96b1000000000000
  | 14 => 0x8e50800000b2c56e24000000000000
  | 15 => 0x5a5bd00000e80d9327000000000000
  | _ => 0

private def maskT0B108 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xd86e00000c863f613000000000000
  | 1 => 0x5145200000c2bd4c27800000000000
  | 2 => 0x5c72400000f085e203800000000000
  | 3 => 0x8e87700000a6089ab1800000040000
  | 4 => 0xcfe4e8a0000bfa0f54004a00080000
  | 5 => 0xf5748000007106c050000000000000
  | 6 => 0xdd43800000e9015a96800000000000
  | 7 => 0x72199280003f1804c200e800080000
  | 8 => 0xfb6540000032df00a2000000000000
  | 9 => 0x383ea000019265fa80800000000000
  | 10 => 0x3c621680027829cca680e800080000
  | 11 => 0xfc3bcea0049385b68100ea00000000
  | 12 => 0xa79da2800850aa18a000e800080000
  | 13 => 0x4b4b240010ac3db1a7808000080000
  | 14 => 0x227d14002018e6bcd6000000000000
  | 15 => 0x49a22c2040130ad531000200080000
  | _ => 0

private def maskT0B109 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xc54e9c2080d36f6f47008200000000
  | 1 => 0x258e8821007fb06a65008200000000
  | 2 => 0x3e3f882200a6979fa0808200000000
  | 3 => 0xba41b00400284d2b43800000000000
  | 4 => 0x6cf8282800d55416a5008200000000
  | 5 => 0x44107eb0003860723380ea00000000
  | 6 => 0xa24716a00078e0e7d500e800080000
  | 7 => 0x93be7ae0003a51c3b2006a00080000
  | 8 => 0x133828a0008fde7294800200080000
  | 9 => 0xb481138000bc97251700e800080000
  | 10 => 0xaec1e8a000b32ed373806a00080000
  | 11 => 0xe392a6a000d204c533006a00080000
  | 12 => 0x5af060000073f5ae86000000000000
  | 13 => 0x39d7d000001c78c613000000000000
  | 14 => 0x8f939000005b697b10000000000000
  | 15 => 0x23144000009f7c3327000000000000
  | _ => 0

private def maskT0B110 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xd824c00000f085e203800000000000
  | 1 => 0x51d3200000df83a2a1800000000000
  | 2 => 0x6c36a00000fd7ee124800000000000
  | 3 => 0x18c6d68000a2a85dd6806800000000
  | 4 => 0x3aced00000be9fe301000000000000
  | 5 => 0x7870e00000ceaec124800000000000
  | 6 => 0x292ff000002d84edd6800000000000
  | 7 => 0x986720000095691c85800000000000
  | 8 => 0x392bb000002fa8e327000000000000
  | 9 => 0x18c5fea000818bf53400ea00000000
  | 10 => 0x1c9a5000005bb61a34800000000000
  | 11 => 0xfed7000000e499c85800000000000
  | 12 => 0xb9250000006ecc9d50800000000000
  | 13 => 0xe27f500000d2406e24000000000000
  | 14 => 0x21e9d00000564ac737800000000000
  | 15 => 0x817c200000659d3596000000000000
  | _ => 0

private def maskT0B111 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xbf66f00000323f7000000000000000
  | 1 => 0x18c26000000c85e410800000000000
  | 2 => 0xf775700000ab7474b2800000000000
  | 3 => 0xb175200000c3eafbb2000000000000
  | 4 => 0x2115b00000051e4203800000000000
  | 5 => 0x295fa00000b60d16b1000000000000
  | 6 => 0x2ef8c00000fd462e86000000000000
  | 7 => 0xfb6750000084d5c837000000000000
  | 8 => 0x6906300000b97306b1000000000000
  | 9 => 0xcf68b680002adad16400e800080000
  | 10 => 0x6e6d30000057d450a2000000000000
  | 11 => 0x369500000e13ee895000000000000
  | 12 => 0x2c6f5e200015a2fa9280e200000000
  | 13 => 0x93ee000000c64a2534000000000000
  | 14 => 0x260f40000027abac85800000000000
  | 15 => 0x240a600000ecc23596000000000000
  | _ => 0

private def maskT0B112 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xa4cdc000002f019c85800000000000
  | 1 => 0x8426d00000b6d5a9b1800000000000
  | 2 => 0xb55d4000003b34c767000000000000
  | 3 => 0xc3d8200000e5c98186800000000000
  | 4 => 0x1a427e2000a870ea630002000e0000
  | 5 => 0x9c18d00000726ce895000000000000
  | 6 => 0x12485000006951d534000000000000
  | 7 => 0x5e95e00000f8f76f00800000000000
  | 8 => 0x61c181e80466c1066c100000000000
  | 9 => 0x9f1bea99d3aee10aee100000000000
  | 10 => 0x8755d57526e6200e62000000000000
  | 11 => 0xca671deb54e1600e16001000000000
  | 12 => 0x1a15f36046e6200e62000000000000
  | 13 => 0xfc1830dfd0dde10dde100000000000
  | 14 => 0xff1af77ca4c8600c86000000000000
  | 15 => 0x1ce929781a5e10a5e100000000000
  | _ => 0

private def maskT0B113 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xb3a13691014c8004c8000000000000
  | 1 => 0x465a0d2c2934800348000000000000
  | 2 => 0xae3ba15c956400564000000000000
  | 3 => 0xfb69389ae53bc103bc100000000000
  | 4 => 0x1207f27dcefae10fae1080000c0000
  | 5 => 0x17ba35244688e0088e00dc00000000
  | 6 => 0xfecc7f730117c1057c108000080000
  | 7 => 0x2f3794803ca5a00e5a008000080000
  | 8 => 0xd8b143dc816d8106d8100000000000
  | 9 => 0xca2f1f3213e9610e96100000000000
  | 10 => 0x37650223ec2d4112d4109000000000
  | 11 => 0xe56fe93e0126402664001000080000
  | 12 => 0x30a6049ca3cbc148bc109000000000
  | 13 => 0x1e3539b01c97608976009000000000
  | 14 => 0xa9c92749a432a1072a008000080000
  | 15 => 0xeed305f9cf7c4307c410d800000000
  | _ => 0

private def maskT0B114 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x472525b248f7e50b7e108000080000
  | 1 => 0xf37a92f7db98e90d8e100000000000
  | 2 => 0xcfb33f555800310402101000080000
  | 3 => 0x4e948d3f2616a00168009000000000
  | 4 => 0xeed94ce4a888010884101000080000
  | 5 => 0x4a1050e42047010078108000080000
  | 6 => 0x796670a0486f4002e4000000000000
  | 7 => 0x74ccaea35af7010f5010c800080000
  | 8 => 0x5bd80543721f2105b210d800000000
  | 9 => 0x1fd3177a6a28800608004800000000
  | 10 => 0x1bab3c00e44e6105e6100000000000
  | 11 => 0xf84dbb16bd1e2003e2008000080000
  | 12 => 0xec00bc3d291ba109ba101000080000
  | 13 => 0x825ae7e0bb0f4100f4100000000000
  | 14 => 0x39685ee526c7210c72100000000000
  | 15 => 0xf0785788d718a0018a000000000000
  | _ => 0

private def maskT0B115 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x449a2527dabf210bf2100000000000
  | 1 => 0x11a149c9621ac001ac000000000000
  | 2 => 0x38a6c0ca7462c0062c000000000000
  | 3 => 0xe7f111468e3bc103bc100000000000
  | 4 => 0xc296f0f4732e4002e4000000000000
  | 5 => 0x86960c86fd9900099000d800000000
  | 6 => 0x9349cb994d91410914100000000000
  | 7 => 0xd7622a1342e6200e62000000000000
  | 8 => 0x1a27ba797f43c1043c100000000000
  | 9 => 0xbfc15bd16b21010210100000000000
  | 10 => 0x7f0264bfccbf210bf2100000000000
  | 11 => 0x3fb498eadef0a00f0a009000000000
  | 12 => 0x55acf668a877410774100000000000
  | 13 => 0x5abd147c6dde10dde100000000000
  | 14 => 0x61a48f25a8ba108ba100000000000
  | 15 => 0xd737949543d6400d64008000080000
  | _ => 0

private def maskT0B116 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xb88211abcb62c0062c000000000000
  | 1 => 0x5384fb8b54e6200e62000000000000
  | 2 => 0xaf0b5a4529e9610e96100000000000
  | 3 => 0xc296f261ee2e4002e4000000000000
  | 4 => 0x90450ba556b8410b84100000000000
  | 5 => 0x8114357d5d2e4002e4000000000000
  | 6 => 0x15e0cda97e78000780000000000000
  | 7 => 0x240cacdd65c7210c72100000000000
  | 8 => 0x8afb2756312e4002e4000000000000
  | 9 => 0x24a97451f4b0600b06000000000000
  | 10 => 0x3677173f6bd2a00d2a000000000000
  | 11 => 0x49d3757bd69e2009e2000000000000
  | 12 => 0x21ab0c60f2e6600e66009c00000000
  | 13 => 0xbe3d8beee221010210100000000000
  | 14 => 0x5e2a0bfdcd2e4002e4000000000000
  | 15 => 0xe0f4f6045343c1043c100000000000
  | _ => 0

private def maskT0B117 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xc233227d4b59010590100000000000
  | 1 => 0xbf6489b59c56400564000000000000
  | 2 => 0x596947b37117400174000000000000
  | 3 => 0x7981bc8b0e62c0062c000000000000
  | 4 => 0x96a3bb6a79394003940080000a0000
  | 5 => 0x2935c23f25dde10dde100000000000
  | 6 => 0xe53d49dcc6a5e10a5e100000000000
  | 7 => 0xb3a1386e454c8004c8000000000000
  | 8 => 0xcedf7041b54c3f782e000000000000
  | 9 => 0xa53f7e2dd8920f7373000000000000
  | 10 => 0x81cdae99d8032da82e000000000000
  | 11 => 0x810de9fe9f2a0de0b000a000000000
  | 12 => 0x625ad6962ba01adc24000000000000
  | 13 => 0x4da6c65c404da6000000000000000
  | 14 => 0x2af942d4bf6e39444c000000000000
  | 15 => 0xee2e53c6e3ee2e5000000000000000
  | _ => 0

private def maskT0B118 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x42726514dd06b2644c000000000000
  | 1 => 0xb3ffee6740aacfed1300c800070000
  | 2 => 0xdf67e4d91df127e2e4000000000000
  | 3 => 0x923b514a72d29b540a000000000000
  | 4 => 0x6bc87358cac7687aca000000000000
  | 5 => 0x951e593994fc4e5c9500a000030000
  | 6 => 0x15d667c2442136644e003000070000
  | 7 => 0xab91039bc22fe1064700a000070000
  | 8 => 0xd3b7c63ebf9a57ca9e00a000070000
  | 9 => 0x4e1e76ddb4ccfe782e000000000000
  | 10 => 0xe946dbded40c06d05400a000070000
  | 11 => 0x8d5ce7397fc2dcf6f8002000000000
  | 12 => 0xaec6ddd3a50b86f254008000070000
  | 13 => 0x3b854dec5ca8750bbf006800000000
  | 14 => 0xc6c06de8c2ff50e599002000000000
  | 15 => 0x68de8b535f90ff8b82000000000000
  | _ => 0

private def maskT0B119 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x52105a7148789256a8000000000000
  | 1 => 0x8c8568e58530c16bc4000000000000
  | 2 => 0xfab070b4674ee87f45000000000000
  | 3 => 0x8e365a97f174365da1002000000000
  | 4 => 0xfa4584eb69c2058706004800000000
  | 5 => 0x53a2b435d03582bc6600a000070000
  | 6 => 0x48f76bd08bbe176966002000000000
  | 7 => 0x101085814706508974008000070000
  | 8 => 0x2f40f65a3ed2f0f77b00c800070000
  | 9 => 0xafd1d176593b71d10a008000070000
  | 10 => 0xbc66b01daa57d6b23b008000070000
  | 11 => 0x11c5b6a3224595b845008000070000
  | 12 => 0xcf47686fedf9576361002000000000
  | 13 => 0x91d165b570b2516838002000000000
  | 14 => 0x1336bfb6597dd6b6ee000000000000
  | 15 => 0xe2abefa1adc88be2a2000000000000
  | _ => 0

private def maskT0B120 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xa0f061c41a8eb062e4000000000000
  | 1 => 0xf19d536fe61d9d5ec0000000000000
  | 2 => 0xfd18e0c86993f8e6ee000000000000
  | 3 => 0x507845a3c4b8184e86000000000000
  | 4 => 0xba8c7a26ce52ec7e86000000000000
  | 5 => 0x17ee40681017ee000000000000000
  | 6 => 0xd586219bcd3f562ead000000000000
  | 7 => 0x92c6ecd4647aa6ee86000000000000
  | 8 => 0xba8c73774352ec7e86000000000000
  | 9 => 0xea1d9a1a6daedd944c000000000000
  | 10 => 0x8f364794e551464de7000000000000
  | 11 => 0x7cf0df7cbb52b0d2e4000000000000
  | 12 => 0x6aecaa7cb96e8ca046000000000000
  | 13 => 0x59bec9c0b2bdbe2e4000000000000
  | 14 => 0x108401a4d67524065a000000000000
  | 15 => 0x222aa06cb6ce2aaec0000000000000
  | _ => 0

private def maskT0B121 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xa42a09f21f8a6a02e4000000000000
  | 1 => 0x29a251f5f1ab42582e000000000000
  | 2 => 0x58e7d80d799ec7dc62000000000000
  | 3 => 0xf4920e6ee79e1206a8000000000000
  | 4 => 0x1a8c6f8cae5e4c644c000000000000
  | 5 => 0x6fe2ab0c70db12a94f002000000000
  | 6 => 0x9189e78f276749ef6c000000000000
  | 7 => 0xe78d5d12f40b8d5ec0000000000000
  | 8 => 0x89927978c389927000000000000000
  | 9 => 0x4ac41dead5c824182e000000000000
  | 10 => 0x74a2da68661e22d6a8000000000000
  | 11 => 0x642fd0c9c9c00fdcc2006800000000
  | 12 => 0x1ffee14b4cf79ee50600b800000000
  | 13 => 0x92fb1151637efb1ec0000000000000
  | 14 => 0x6fe3f29cd0ed03f82e000000000000
  | 15 => 0x802db88a566e2d6ee000000000000
  | _ => 0

private def maskT0B122 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x59db4606f25dbb4046000000000000
  | 1 => 0x94aa6d79ea18aaa8c000000000000
  | 2 => 0xe4d642596382b64666000000000000
  | 3 => 0xf83e532229ee2e5161000000000000
  | 4 => 0xef0a4bc6ec63aa48ca000000020000
  | 5 => 0xd4531463ed7c931a8c000000000000
  | 6 => 0x9075357ae11295382e000000000000
  | 7 => 0xc6c1d362dca4c1c62000000000000
  | 8 => 0x2083060eeff26dfb20000000000000
  | 9 => 0xb4ae0cc3dce33bc9ba800000000000
  | 10 => 0x1c72676fa0fdb06973800000000000
  | 11 => 0x60733d01fb8a5489a380a000000000
  | 12 => 0x8aeeed52866606839c000000000000
  | 13 => 0x58abcc5af59d049000000000000000
  | 14 => 0xb1e13907cd67cde465000000000000
  | 15 => 0x13f909c7f4fe9e4711800000000000
  | _ => 0

private def maskT0B123 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x98cf5a4e353e740025800000000000
  | 1 => 0x24f1579fd2092c7542000000000000
  | 2 => 0xf223f8583983f06f45000000000000
  | 3 => 0x97717d583e14f2956000000000000
  | 4 => 0xe9755d1f2e3adfb025800000000000
  | 5 => 0x8701e58a2ebccb0636800000000000
  | 6 => 0xa7528ff626b2b04ea80a000080000
  | 7 => 0x741f27c84b409b348002000000000
  | 8 => 0x5d4b95b5779e1c698000000000000
  | 9 => 0xd488fadb6618469e17800000000000
  | 10 => 0x54a24983adf9c09b55800000000000
  | 11 => 0xae3d06cb62b00ba72800000000000
  | 12 => 0x87fe9b579eb7b7665300a0000c0000
  | 13 => 0x408ef52c06d0beb22f00a0000c0000
  | 14 => 0xc781858633247af3b9800000000000
  | 15 => 0x86597b2537956a8216000000000000
  | _ => 0

private def maskT0B124 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xb42e429934a8ac0311000400000000
  | 1 => 0x3ec05f5a21c24846d280a4000c0000
  | 2 => 0x495d36b2f2a7761050000000000000
  | 3 => 0x48904c53412d5c524f000400000000
  | 4 => 0x9412c2160c99c20aca000000000000
  | 5 => 0x28e27629253670298200a4000c0000
  | 6 => 0xccf790f885740fcd7300a0000c0000
  | 7 => 0x4668b69ba6361adf9480a0000c0000
  | 8 => 0xa25954ac6e7fcfbf6500a0000c0000
  | 9 => 0xa2a9b0c4848251f2eb000000000000
  | 10 => 0xf778922f4ea1047748800400000000
  | 11 => 0x9e42e53fc3357edf0c000000000000
  | 12 => 0x50df89dfecee314331000000000000
  | 13 => 0xd85a09dfdc07efc82480a0000c0000
  | 14 => 0x496205ea22ca5027d900a0000c0000
  | 15 => 0xe5a8a1ecde1f1d4e47800000000000
  | _ => 0

private def maskT0B125 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x282caa541a3f6d0b20000000000000
  | 1 => 0xad935ffe50d4f65868000000000000
  | 2 => 0xa470a8d938767b23f980a0000c0000
  | 3 => 0xd1f9fd823419f2b102800000000000
  | 4 => 0x24f15482877ea92127000000000000
  | 5 => 0xbd0cfa8e0c20fc3351000000000000
  | 6 => 0x8b066d51cbdc12d820800000000000
  | 7 => 0x6c2cb614c06e08b636800000000000
  | 8 => 0x3babf93e11fc6ae542000000000000
  | 9 => 0x4f2f0bc715b50e5465000000000000
  | 10 => 0x1f24f2c830a49ff973800000000000
  | 11 => 0x920b0dfce4bbcd4f60800000000000
  | 12 => 0xdd2401e52e732eeb05800000000000
  | 13 => 0x6a082858397aebb956000000000000
  | 14 => 0x82ab05aa4a8e77a567800000000000
  | 15 => 0xb722ece9df4ef71374800000000000
  | _ => 0

private def maskT0B126 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x5607f4bd2824dd73d0800400000000
  | 1 => 0x4bb88cfe2ac4c22409800000000000
  | 2 => 0x8b499e4cf9f8be0973800000000000
  | 3 => 0xa2cdd78b0d5d6d0871000000000000
  | 4 => 0x66db1b0beeb755f613000000000000
  | 5 => 0x7d822eb96611044871000000000000
  | 6 => 0xc672a1a1761d25cc14000000000000
  | 7 => 0xe9755286d5c3400025800000000000
  | 8 => 0xae1024e106e0004000000000000000
  | 9 => 0xd2a0f3908a2ae85c14000000000000
  | 10 => 0x40e437b2d1cf992f45000000000000
  | 11 => 0x8e79634d9fdb909613000000000000
  | 12 => 0xa97bd7d0944caa9f8d806000000000
  | 13 => 0x62a6d808d9b4534567800000000000
  | 14 => 0x6582174b34a1695b05800000000000
  | 15 => 0xb0e92f43edc3c7f871000000000000
  | _ => 0

private def maskT0B127 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xe86c57dbedb0ea8253800000000000
  | 1 => 0xd1c9c1ebb9ea82525f000000000000
  | 2 => 0x40d972c9fa49c6d25800000000000
  | 3 => 0xcaa0c3d0d101a5df60800000000000
  | 4 => 0x1dcf808b9562e6d179000000060000
  | 5 => 0x5c678492151546d000000000000000
  | 6 => 0x7965f2d635f476aa07000000000000
  | 7 => 0xd88eea9423f484d854800000000000
  | 8 => 0x226caf6b9600000dc480b000000000
  | 9 => 0x4b793b4b6d000003ab800000000000
  | 10 => 0x5a241f4e3700000eaf000000000000
  | 11 => 0xaeceda0870000033e007800000000
  | 12 => 0xb972d3956500000aaa000000000000
  | 13 => 0xcd7866d36e000009c8800000000000
  | 14 => 0xf80de643d100000bcb000000000000
  | 15 => 0x67d9bbb11f000004c7000000000000
  | _ => 0

private def maskT0B128 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x618fea4bbe000000c2000000000000
  | 1 => 0xc303aedcb600000dcd800000000000
  | 2 => 0xf9e4f4f5bf00000c6e800000000000
  | 3 => 0xaec9df68200000086b800000000000
  | 4 => 0x43277ff6bc000001b5000000000000
  | 5 => 0x2cb5492cd3000001a3000000000000
  | 6 => 0x9090e1163b00000a68000000000000
  | 7 => 0xe4e9b54b570000094c007800080000
  | 8 => 0x6fc79f2cc70000088800f800000000
  | 9 => 0x40404973490000051e800000000000
  | 10 => 0xf96524601c80000864800000000000
  | 11 => 0xb9b17bc56a00000f0c000000000000
  | 12 => 0xc7a7910b5800000b09000000000000
  | 13 => 0x83a42a43c5000016b2800000000000
  | 14 => 0x790415944f0000210800b000000000
  | 15 => 0x4677fc9ea9000045b600b000000000
  | _ => 0

private def maskT0B129 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x77f133c3688000895b006800000000
  | 1 => 0xfcf7f5a30480010b1900b000000000
  | 2 => 0x1c8f572ecd000204cc00d800000000
  | 3 => 0x2a66d2bc9d00040ab500b000000000
  | 4 => 0x7bda1ffea1800806a4800000000000
  | 5 => 0x955eceea120010068500d800000000
  | 6 => 0x16443968a0002001d5000000000000
  | 7 => 0x577f7f650100400ea900b000000000
  | 8 => 0x9252331920080087480b000000000
  | 9 => 0x80fbe9aee201000d8a006800000000
  | 10 => 0xeee87fa7b28200058580b000000000
  | 11 => 0x5a8039d2a184000f46800000000000
  | 12 => 0x1bc1fff628880004da00d800000000
  | 13 => 0x8a5a4e3fc010000a82806800000000
  | 14 => 0x22b01de25ea000073000d800000000
  | 15 => 0x9a4a39cfa4400007e2006800000000
  | _ => 0

private def maskT0B130 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xba15e5fee700000767800000000000
  | 1 => 0x4e9e313d99000008a9800000000000
  | 2 => 0x4ef82dda9d000001a3000000000000
  | 3 => 0x75f667bf1300000362800000000000
  | 4 => 0xdf57bafb4f00000e6d000000000000
  | 5 => 0xe9e0be2fc500000e47800000000000
  | 6 => 0x66437827ec000008dd800000000000
  | 7 => 0xa13e0285300000eaf000000000000
  | 8 => 0xdf57b3aac200000e6d000000000000
  | 9 => 0xcb482e1967000004c7000000000000
  | 10 => 0x818da466f100000767800000000000
  | 11 => 0x3a49d432300000076000000000000
  | 12 => 0x15855c4b8a000003a0800000000000
  | 13 => 0xf36c164020000002c1800000000000
  | 14 => 0xc47d501e92000005a6000000000000
  | 15 => 0x682d77cfc200000cd5800000000000
  | _ => 0

private def maskT0B131 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x776d877e4800000eaf000000000000
  | 1 => 0x4952a0bb1d000005a6000000000000
  | 2 => 0x652445773a00000000000000000000
  | 3 => 0x66e6c3abb800000161000000000000
  | 4 => 0xa2d3596f5100000028806800000000
  | 5 => 0x9cd57f726100000e6d000000000000
  | 6 => 0x853023880600000606800000000000
  | 7 => 0x4a5382252000000161000000000000
  | 8 => 0x2e8b169c6700000161000000000000
  | 9 => 0x74c91a44a1000006c4800000000000
  | 10 => 0x6e5f7ef4e500000362800000000000
  | 11 => 0x7a64bbaf8d00000cac800000000000
  | 12 => 0x286787dbe700000057802800000000
  | 13 => 0x730585e38400000bcb000000000000
  | 14 => 0x3dfdab3cc300000a68000000000000
  | 15 => 0xe2236edcb600000564000000000000
  | _ => 0

private def maskT0B132 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xe1cd289f67000009c8800000000000
  | 1 => 0x4c63c755ea00000c6e800000000000
  | 2 => 0x77784839190000091f800000000000
  | 3 => 0xc878c090bf00000aaa000000000000
  | 4 => 0x78dc924feda0000d6e8010000a0000
  | 5 => 0xdff20538c3000002c1800000000000
  | 6 => 0xfd3c8a346a000000c2000000000000
  | 7 => 0xd83e9f719000000fce000000000000
  | 8 => 0xd65d75cfd7573d28aa000000000000
  | 9 => 0x69cb9635b91ac930a9000000000000
  | 10 => 0x8b226b71269d9833c3000000000000
  | 11 => 0x832d56a1d5d1d6edd3003400000000
  | 12 => 0x9b96301d633a3809a4000000000000
  | 13 => 0xf22c0515c01b1afa37000000000000
  | 14 => 0xa17090fb09d60ffaec000000000000
  | 15 => 0x55eda5d5da513f428b002000000000
  | _ => 0

private def maskT0B133 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x7870886008087c0fe7000000000000
  | 1 => 0xf82614eb6186881b69000000000000
  | 2 => 0x65720bf6204e0bfda1000000000000
  | 3 => 0xcb7bf19dbf95e93d2a000000000000
  | 4 => 0xa4438eca382c42e48e000000000000
  | 5 => 0x5d94ac7d4aa75599a4000000000000
  | 6 => 0xb36f14d1f14fed9fe7000000000000
  | 7 => 0x15ecd29dcd22b2c3c3000000000000
  | 8 => 0x81386898868279b3cb003400080000
  | 9 => 0x987530f053ecdd0a3700b400000000
  | 10 => 0xb7359a255965001b16002400000000
  | 11 => 0x15c8dc768dfb53ad2a000000000000
  | 12 => 0xe90d7850d8f660d2c002400000000
  | 13 => 0xf86297d621939f3c5002400000000
  | 14 => 0xdbe5a3db5b212c0665000000000000
  | 15 => 0x65b792a17bdaf245fa001000030000
  | _ => 0

private def maskT0B134 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x57f5285556ee754d6a000400000000
  | 1 => 0x16f0889f8f491a19f001000030000
  | 2 => 0x902c840ed881848d4c000400000000
  | 3 => 0xb4fdf224ff12bb782b001400030000
  | 4 => 0xa74016cd416453fef9002400000000
  | 5 => 0x6a67fddbfffba4a87d003000030000
  | 6 => 0xd536ff9362880372d000000000000
  | 7 => 0x70fb2c8fb28f788b82000000000000
  | 8 => 0xd608b46d8b5c301909000000000000
  | 9 => 0xbd20a092069c268fc002400000000
  | 10 => 0x1874488a44f82b581d001000030000
  | 11 => 0xa4b0b1620b793b1909002000000000
  | 12 => 0x272b957fb9a1fb070d000400000000
  | 13 => 0x297d98e8d998cdf3ff001000030000
  | 14 => 0xc079cf359c60b26132003000030000
  | 15 => 0x3c220b722b491208b002000000000
  | _ => 0

private def maskT0B135 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3b4086dd08ce2f7b29002400000000
  | 1 => 0xf7fb5cbcb51a4d53c3000000000000
  | 2 => 0xa0f00e0a00454fe405000000000000
  | 3 => 0xb79cf93fcf4183c246000000000000
  | 4 => 0x2b9c017ac088a663c3000000000000
  | 5 => 0xd46cb0e7cb8828dda1000000000000
  | 6 => 0xceaca983cae1a89569000000000000
  | 7 => 0xaf06f6d46f0bb24c24000000000000
  | 8 => 0x3ef10bce1059282821000000000000
  | 9 => 0x4601ab0c1a7ae82f6c000000000000
  | 10 => 0xd5834558ca9e6348000000000000
  | 11 => 0x2f8a5778a5641cb580000000000000
  | 12 => 0x9fb03bbd03fdcb7246000000000000
  | 13 => 0xfa3105c410b6293a67000000000000
  | 14 => 0x580399a4393b66ec24000000000000
  | 15 => 0xe3333b3833c51b550b000000000000
  | _ => 0

private def maskT0B136 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x93c98650981aa03f6c000000000000
  | 1 => 0x66f2926a2917290405000000000000
  | 2 => 0x68deec61ee788d2aec000000000000
  | 3 => 0xb538d27c8d6989092f000000000000
  | 4 => 0x3b663e1763a59ffda1000000000000
  | 5 => 0x553a979ea903bbc2cd000000000000
  | 6 => 0x124b5194bccc1150b000000000000
  | 7 => 0x3dfbf951bfedf2dbce001400030000
  | 8 => 0xc071542615e294a821000000000000
  | 9 => 0x17f91e1391f1f88f6c000000000000
  | 10 => 0xe9ee8634e8b266c8aa000000000000
  | 11 => 0x3de47bff476e703821000000000000
  | 12 => 0x491614eb61d5cb6d7a00d000000000
  | 13 => 0x12ee0a31e01faa7b1f000000000000
  | 14 => 0x932dc618dcca66cf2a000000000000
  | 15 => 0x80f861ab863903e9a4000000000000
  | _ => 0

private def maskT0B137 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xdd17b3b37b682f4e62000000000000
  | 1 => 0xef0a8ef0a8b9d35000000000000000
  | 2 => 0x5d14888148f0264d50000000000000
  | 3 => 0x2e5f6fcff680afed2a000000000000
  | 4 => 0xc98a74ffa7bd2d9a67002000020000
  | 5 => 0xea9dbb29dbab6b6580000000000000
  | 6 => 0x7a70872c08ecc2508b000000000000
  | 7 => 0xa2a7170071d2c89f6a002400000000
  | 8 => 0x405601896858c08ee6000000000000
  | 9 => 0xdaa76b94bd63ecb3e8100000000000
  | 10 => 0x521241af7748e530f4100000000000
  | 11 => 0x8301950a66d3a7f3f810a400000000
  | 12 => 0xbe2083d2e4830ec45a009400000000
  | 13 => 0x4d077fa4fdb748a276000000000000
  | 14 => 0x6f8a13b01d548bc000000000000000
  | 15 => 0xbdf312404d99f7c368100000000000
  | _ => 0

private def maskT0B138 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xe0561f4dc7148a6ba4000000000000
  | 1 => 0xb177573911c2e64276000000000000
  | 2 => 0x4c085cf04c830c939c000000000000
  | 3 => 0x3f8e7416a67ee41b50100000000000
  | 4 => 0x91799184fe893676de000000000000
  | 5 => 0x77dfee7aae90750e12100000000000
  | 6 => 0x17c8bd0751c7bdaabc000000000000
  | 7 => 0x7d5bd9a842e7dff838000000000000
  | 8 => 0x5d551e2d95bf8c4c90000000000000
  | 9 => 0x22d8c5211470c98018000000040000
  | 10 => 0x80a647eabafe0de016102400000000
  | 11 => 0xec6e3507d9bc13a328000000000000
  | 12 => 0x81c0d59985585888ba10a4000c0000
  | 13 => 0x81555c01a7c14f25c010a4000c0000
  | 14 => 0x94f9efffafeb0317b610a4000c0000
  | 15 => 0x3783570cd3c74e7168109400000000
  | _ => 0

private def maskT0B139 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x6ae6ea1352cbd3eff81030000c0000
  | 1 => 0x8bd6ae05a3eb8cdffe009400000000
  | 2 => 0x322465c49eee6d0d8e1010000c0000
  | 3 => 0xd08bcddfee0d7426c8002000000000
  | 4 => 0x5b4602b26d7062d108109400000000
  | 5 => 0x7d7334c7333140d88000000000000
  | 6 => 0xc1f76a724a66dbc216009400000000
  | 7 => 0x831cf53361503ae006109400000000
  | 8 => 0x270db53164743bfc801084000c0000
  | 9 => 0x1ccad2bc6d374c02f4109400000000
  | 10 => 0x37c0763b0f54f089d410b400000000
  | 11 => 0xd3b5bbf7276dc7cd0c0084000c0000
  | 12 => 0x86ac42557c21fb89d2009400000000
  | 13 => 0x6468b16855f6edecf00084000c0000
  | 14 => 0x2a083422dc6025fdfe00a4000c0000
  | 15 => 0xbae30ed15e47f6ed8e1010000c0000
  | _ => 0

private def maskT0B140 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x5c9a4b03a5cca0119a1084000c0000
  | 1 => 0x6c000a2eac0eeacaca0010000c0000
  | 2 => 0xc5243b94bd7c6fe42c000000000000
  | 3 => 0xf7b4a8f6ff78db56de000000000000
  | 4 => 0x6f1c7e939486253276000000000000
  | 5 => 0xb5f48ebd975e2df8cc100000000000
  | 6 => 0xa3a5726e4e85419556000000000000
  | 7 => 0x89cb87826af1ed211e100000000000
  | 8 => 0xaeb87000f0aeb77f0c000000000000
  | 9 => 0x847d1b16ef3513ef0c000000000000
  | 10 => 0x51d15d90c588dd0d8e100000000000
  | 11 => 0x41155fa96bbb83ea4e000000000000
  | 12 => 0xc5fdcaf9796a6a5838000000000000
  | 13 => 0x5cf14b9b1ce5408b50100000000000
  | 14 => 0x7a18f3f173450fcba4000000000000
  | 15 => 0xd2ef6e27be3094811e100000000000
  | _ => 0

private def maskT0B141 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x9e3d2b5b982b84a7a0100000000000
  | 1 => 0xe72b96ff6288ddb5c600a4000c0000
  | 2 => 0xd0850b722667a76282100000000000
  | 3 => 0xcae0a43f118911b62a100000000000
  | 4 => 0xfb30e606949b59a7c0100000000000
  | 5 => 0x96676b5076236926100000000000
  | 6 => 0x65984b5cb2d053645c100000000000
  | 7 => 0x91ec178527e9be6ba4000000000000
  | 8 => 0xae85ad79247917ed7a000000000000
  | 9 => 0x714a196d4ee79ef45c100000000000
  | 10 => 0xfe5a1a828656727ee6000000000000
  | 11 => 0x130717d8c76e8b6aba100000000000
  | 12 => 0x9c38673bd6ef850a3e10d000000000
  | 13 => 0x8f2c1435cacc70b4a8000000000000
  | 14 => 0x7dce55cf41213a4542000000000000
  | 15 => 0xd8c45cf7f117bb462a100000000000
  | _ => 0

private def maskT0B142 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xd3e04cfa971c49311e100000000000
  | 1 => 0x7aec90d95077799ce010b400000000
  | 2 => 0xaae25f48bd5e698c9a100000000000
  | 3 => 0xc12227b562ba74838000000000000
  | 4 => 0x13d400b83618576c140030000e0000
  | 5 => 0x49cb376c1d3f0ae276000000000000
  | 6 => 0x525ddf40a1a657cc90000000000000
  | 7 => 0xc8af55bbef9311a0f4100000000000
  | 8 => 0x71f5f6d615724ca6ed800000000000
  | 9 => 0x3bb3d6acf6505cb012000000000000
  | 10 => 0x1c72676fa0fdb06973800000000000
  | 11 => 0x6dd11f11c9155d8099008000000000
  | 12 => 0x5485c7e5565540a7f9000000000000
  | 13 => 0x58abcc5af59d049000000000000000
  | 14 => 0xefa0a0e8d6b50dc542000000000000
  | 15 => 0x1cce60f015ac7f3bfb000000000000
  | _ => 0

private def maskT0B143 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x17d280211f8d13798d000000000000
  | 1 => 0x7ab0ce70c9dbec5465000000000000
  | 2 => 0x7d3e223713309716ed800000000000
  | 3 => 0x5801e70d79616e749b800000000000
  | 4 => 0xe6423428cf683ecccf000000000000
  | 5 => 0x88368cbdcfee2a7adc000000000000
  | 6 => 0x7d70aef50f4220dd0008000080000
  | 7 => 0x658212b415fe9b4b05800000000000
  | 8 => 0x795a5a8ce0bf4c56ed800000000000
  | 9 => 0xfce5af26aa54d705a5800000000000
  | 10 => 0x4bf74ecdf107b852090080000c0000
  | 11 => 0xbcf2a578347c21e77500a000080000
  | 12 => 0x6f3baddfd6d06eca2a808000080000
  | 13 => 0xe02677b0fc6309b382008000080000
  | 14 => 0x600cc4e837828fb6c0008000080000
  | 15 => 0x3e4d5d072c504f97e7008000080000
  | _ => 0

private def maskT0B144 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x10f7b40a6c4ea165ef000000000000
  | 1 => 0x89c6439eeffb6890b4000000000000
  | 2 => 0xcab55f05d5fb58441b008000080000
  | 3 => 0x845ac8913018a9495e008000080000
  | 4 => 0x6a45682ee49bea2774000400000000
  | 5 => 0xf58b5a5ccf645daf01808400080000
  | 6 => 0x4469ec31147854a7f2808000080000
  | 7 => 0x14d266085d725fb820008400080000
  | 8 => 0x99261895ea46e0bd68808000080000
  | 9 => 0xee9da9ac2d4f4777f3800400000000
  | 10 => 0x88a14f9141617d5d08808000080000
  | 11 => 0xf0ab37184fc4af84d800000000000
  | 12 => 0x3864a1727a59fb0b7b808000080000
  | 13 => 0x73f5f344b5e3f6aa64800000000000
  | 14 => 0xf84ffb18aff3e50ba2000400000000
  | 15 => 0xc0037cd0d8e7befe2b000000000000
  | _ => 0

private def maskT0B145 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xd0f53a87270fb74673000000000000
  | 1 => 0x9e0f65021f9f5e9317000000000000
  | 2 => 0x5c422a5b1c5f03ea6f008000080000
  | 3 => 0xa5be02057855e98d000000000000
  | 4 => 0xfa9a7e35574def0542000000000000
  | 5 => 0xbd0cfa8e0c20fc3351000000000000
  | 6 => 0x556d47e61bef54fc45800000000000
  | 7 => 0x3d5a46cc3aee29ebfb000000000000
  | 8 => 0x65ea60d10a2eaac465000000000000
  | 9 => 0x4f2f0bc715b50e5465000000000000
  | 10 => 0x9f0e4190fb4519fc31800000000000
  | 11 => 0xcc4a9413ff690d6e47800000000000
  | 12 => 0x8365980a35a1eeca22800000000000
  | 13 => 0x3b7ed880c3facae49b800000000000
  | 14 => 0xd3ddf572b00e56f8aa000000000000
  | 15 => 0xe6541c3125ced64eb9000000000000
  | _ => 0

private def maskT0B146 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xd62d47e5e3c55b7692800400000000
  | 1 => 0xcb923fa6e12544214b800000000000
  | 2 => 0x5522b4fb29cbf82d16800000000000
  | 3 => 0xadfabebcec0f8c749b800000000000
  | 4 => 0xe6f1a8532556d3f351000000000000
  | 5 => 0xf29ff4d64ca26331d9800000000000
  | 6 => 0x970451798c9d0491d9800000000000
  | 7 => 0x666888e9ff7027798d000000000000
  | 8 => 0xae1024e106e0004000000000000000
  | 9 => 0x3fcb010bb4b4f049b800000000000
  | 10 => 0x4fd35e85309d7853af800000000000
  | 11 => 0xd038faa2840950b734000000000000
  | 12 => 0x295164885fad2c9acf806000000000
  | 13 => 0xedbb0267f307343ccf000000000000
  | 14 => 0xe5a8a413ff40ef5e47800000000000
  | 15 => 0x61b56cc3dca260a0fe800000000000
  | _ => 0

private def maskT0B147 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3930145bdcd14ddadc000000000000
  | 1 => 0x5ed41b849359e52bf7800000000000
  | 2 => 0xda66bd9b4f97da4940800000000000
  | 3 => 0x94e15a3fcad365fe47800000000000
  | 4 => 0x3ea56d1411c3e472c000000060000
  | 5 => 0x5c678492151546d000000000000000
  | 6 => 0x2813020ecf7457f7ca800000000000
  | 7 => 0xd88eea9423f484d854800000000000
  | 8 => 0x44fdc0000041f58ed6000000000000
  | 9 => 0xa744000009f465c70000000000000
  | 10 => 0xb2fa20000043afd178000000000000
  | 11 => 0x39f0500000861841fc005800000000
  | 12 => 0xb857900000538e7377000000000000
  | 13 => 0xb085e00000570ce70b000000000000
  | 14 => 0x8041400000f11caed6000000000000
  | 15 => 0x2590000085ab22cd000000000000
  | _ => 0

private def maskT0B148 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xf6e3a00000fabcf6b1000000000000
  | 1 => 0x230c600000371c670b000000000000
  | 2 => 0x2e3b0000000524c92f000000000000
  | 3 => 0x55f0c00000435a564e004800000000
  | 4 => 0xaf84e0000002f36ed6000000000000
  | 5 => 0x6db85000003207b70b000000000000
  | 6 => 0x2e889000000410ca58000000000000
  | 7 => 0xd871000000ada33385000000000000
  | 8 => 0xa47c40000046fd09dd000000000000
  | 9 => 0x77f5e00000045df895000000000000
  | 10 => 0x4401a0000065797be2000000000000
  | 11 => 0x938b00000087559efc005800080000
  | 12 => 0x469c8000000e2fa145006800000000
  | 13 => 0x546f8000002e7f7118000000000000
  | 14 => 0xaf0ac000001ca071ba000000000000
  | 15 => 0xd8a3e2800029410cd300e8000a8000
  | _ => 0

private def maskT0B149 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xe11c0000043d9c0f2000000000000
  | 1 => 0xbf0360000116c211fc000000000000
  | 2 => 0xad60000026124ae6b00b000000000
  | 3 => 0x1c0cca8004a263802a0058000a8000
  | 4 => 0x75007000085dee8a7c004800000000
  | 5 => 0xf6b9028010363003c400a0000a8000
  | 6 => 0x4f78d00020cbd1674900f800000000
  | 7 => 0xd4023a8040330800fc0010000a8000
  | 8 => 0xf441e800800c2f38a8004800000000
  | 9 => 0xd68ef801006f6797af00b000000000
  | 10 => 0x4a0238020032e7891600b000000000
  | 11 => 0x6702300400c14c71d5000000000000
  | 12 => 0x9ff8580800c583eb6f00b000000000
  | 13 => 0x7964fa9000e0871e0e0058000a8000
  | 14 => 0x47a1402000cb351f7c00b000000000
  | 15 => 0x4946984000151dac0600f800000000
  | _ => 0

private def maskT0B150 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x9fc57a0000ca93971800e8000a8000
  | 1 => 0x9d79810000830cb769004800000000
  | 2 => 0xf304ca000018c557bb00f800000000
  | 3 => 0x377b840000be916a7500f800000000
  | 4 => 0x9bd5d00000e1e65249000000000000
  | 5 => 0xf15ce0000009d0eaaa000000000000
  | 6 => 0xfa7db00000875c77b2000000000000
  | 7 => 0x114b2000005217370b000000000000
  | 8 => 0xc24ef000001d77e385000000000000
  | 9 => 0x59e9fa8000ef1472d70058000a8000
  | 10 => 0x9ba7900000df11f148000000000000
  | 11 => 0x86c1700000c937b70b000000000000
  | 12 => 0x9112000000f6cb0796000000000000
  | 13 => 0x4d75900000cee01f9e000000000000
  | 14 => 0x53a0900000a3ebec1b000000000000
  | 15 => 0xd513a000004be2448e000000000000
  | _ => 0

private def maskT0B151 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x106c3000002e9f01ba000000000000
  | 1 => 0x91ee600000cbfbcf9e000000000000
  | 2 => 0x8b2df000001d0c9f6c000000000000
  | 3 => 0xeb0b600000ae4c4a58000000000000
  | 4 => 0xfc56300000ec1f1895000000000000
  | 5 => 0x8655600000aaad670b000000000000
  | 6 => 0xd59d800000cf992e24000000000000
  | 7 => 0x2100000b60ac895000000000000
  | 8 => 0xc81d300000e60ab7f9000000000000
  | 9 => 0x8b95e00000c676988500b000000000
  | 10 => 0x9b19b0000026d290f2000000000000
  | 11 => 0xa272500000be4759dd000000000000
  | 12 => 0x2fc5a0000058afb0ff00b800000000
  | 13 => 0x3ce4c00000daea548e000000000000
  | 14 => 0xe38400000bfac3643000000000000
  | 15 => 0x7e742000008164847c000000000000
  | _ => 0

private def maskT0B152 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x23f0000000aba677f9000000000000
  | 1 => 0xa2001000006d0bf385000000000000
  | 2 => 0x1a578000002794b6dd000000000000
  | 3 => 0xbf80a0000053b16a58000000000000
  | 4 => 0xc4ef7a000069ecfb1a00e8000a0000
  | 5 => 0x33121000006ecc992f000000000000
  | 6 => 0xb3535000003628647c000000000000
  | 7 => 0x76a2e0000060f0f5c6000000000000
  | 8 => 0x29a3ca8532dc1000000000000
  | 9 => 0x388f732a3d2a9000000000000
  | 10 => 0xe595d642d3a4e000000000000
  | 11 => 0x571428803fc3f00a400000000
  | 12 => 0xd594114a771a3000000000000
  | 13 => 0xd2c02d8ef6000000000000000
  | 14 => 0xd694654a2e377000000000000
  | 15 => 0xe1a2f4579b15e000000000000
  | _ => 0

private def maskT0B153 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2f7dba996fa71000000000000
  | 1 => 0xe16321ea176ee000000000000
  | 2 => 0x90bb7141f9910000000000000
  | 3 => 0x61f9809e8403f000000000000
  | 4 => 0xe4414f8057c9f000000000000
  | 5 => 0x5775c574ca161000000000000
  | 6 => 0x9f3f2a33dda4e000000000000
  | 7 => 0xa7fb87ea69b10000000000000
  | 8 => 0xb15a68b811161000000000000
  | 9 => 0xf458755b4bd2000000000000
  | 10 => 0xc08f881432c5d000000000000
  | 11 => 0xd8d65cb40bd03000000000000
  | 12 => 0x9c49331d12b10000000000000
  | 13 => 0x8f06dc205ddc1000000000000
  | 14 => 0x5cfb0d16e382c000000000000
  | 15 => 0x9eb1225f59d4b000000040000
  | _ => 0

private def maskT0B154 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1b6ec984078ba000400000000
  | 1 => 0x8e6846723153b000000000000
  | 2 => 0xc29703fd61ca0000000000000
  | 3 => 0x759f66707474d000000000000
  | 4 => 0x8000063ab7ac24fa2100a4000c0000
  | 5 => 0x80001209c727aa4d87002000000000
  | 6 => 0x800022e26c9937675b00a4000c0000
  | 7 => 0x800049a72a67f8925000a4000c0000
  | 8 => 0x800083af350aca39c40084000c0000
  | 9 => 0x10c71d32df2556400a4000c0000
  | 10 => 0x8002071bdcc8cf4016002000000000
  | 11 => 0x800404f73689f39127009400000000
  | 12 => 0x80b4d378c7c2e3200b400000000
  | 13 => 0x80100dc6d1dd2cf0bb0010000c0000
  | 14 => 0x802003f5cc11462a08009400000000
  | 15 => 0x400c704bb741830e000000000000
  | _ => 0

private def maskT0B155 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x80800407a5b221fbab00a4000c0000
  | 1 => 0x810009a7e2e61210fd000000000000
  | 2 => 0x20007089c39e92148000000000000
  | 3 => 0x840003eb54be051331002000000000
  | 4 => 0x80007ba513efae9fb00b400000000
  | 5 => 0x100001284a5f1602c20030000c0000
  | 6 => 0x200004460b0d066a4e002000000000
  | 7 => 0xc0000a39a283135a4e00a4000c0000
  | 8 => 0x7cce856d66c5d000000000000
  | 9 => 0x8eafac0184ca0000000000000
  | 10 => 0xdddb7bc1916d1000000000000
  | 11 => 0x9a974bf2c103f000000000000
  | 12 => 0x69d5102d9ac9f000000000000
  | 13 => 0x44a80be775361002000000000
  | 14 => 0x3ea0d2e1220c2000000000000
  | 15 => 0xe5a5d033fb1a3000000000000
  | _ => 0

private def maskT0B156 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x533933469362c000000000000
  | 1 => 0x426e50da38c9f000000000000
  | 2 => 0xfe1f5294f1ab3000000000000
  | 3 => 0xc08f856d66c5d000000000000
  | 4 => 0xd78c970da515e000000000000
  | 5 => 0x696f11de2178f000000000000
  | 6 => 0x4d1bd39e7b161000000000000
  | 7 => 0x1ddef019acc9f000000000000
  | 8 => 0x7aaaf48da3dc1000000000000
  | 9 => 0xd2751bfe8274d000000000000
  | 10 => 0x9654a3713c7b00084000c0000
  | 11 => 0x55e741e3dc19c000000000000
  | 12 => 0xcec8c358aa23f004400000000
  | 13 => 0x8dbba017a74d000000000000
  | 14 => 0xf809921548b10000000000000
  | 15 => 0x47106bd48de5d009400000000
  | _ => 0

private def maskT0B157 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x86272e8a4878f000000000000
  | 1 => 0x9a1d4196de03f000000000000
  | 2 => 0x4f89514dba7b3000000000000
  | 3 => 0x6f3b640af703f000000000000
  | 4 => 0xdef09f6f7088c002000020000
  | 5 => 0x315f5d16e3d3c000000000000
  | 6 => 0xab34774c18455000000000000
  | 7 => 0xb5169ce91bd3c000000000000
  | _ => 0

private def maskT1B0 (i : ℕ) : ℕ :=
  match (i/16)%16 with
  | 0 => maskT0B0 i
  | 1 => maskT0B1 i
  | 2 => maskT0B2 i
  | 3 => maskT0B3 i
  | 4 => maskT0B4 i
  | 5 => maskT0B5 i
  | 6 => maskT0B6 i
  | 7 => maskT0B7 i
  | 8 => maskT0B8 i
  | 9 => maskT0B9 i
  | 10 => maskT0B10 i
  | 11 => maskT0B11 i
  | 12 => maskT0B12 i
  | 13 => maskT0B13 i
  | 14 => maskT0B14 i
  | 15 => maskT0B15 i
  | _ => 0

private def maskT1B1 (i : ℕ) : ℕ :=
  match (i/16)%16 with
  | 0 => maskT0B16 i
  | 1 => maskT0B17 i
  | 2 => maskT0B18 i
  | 3 => maskT0B19 i
  | 4 => maskT0B20 i
  | 5 => maskT0B21 i
  | 6 => maskT0B22 i
  | 7 => maskT0B23 i
  | 8 => maskT0B24 i
  | 9 => maskT0B25 i
  | 10 => maskT0B26 i
  | 11 => maskT0B27 i
  | 12 => maskT0B28 i
  | 13 => maskT0B29 i
  | 14 => maskT0B30 i
  | 15 => maskT0B31 i
  | _ => 0

private def maskT1B2 (i : ℕ) : ℕ :=
  match (i/16)%16 with
  | 0 => maskT0B32 i
  | 1 => maskT0B33 i
  | 2 => maskT0B34 i
  | 3 => maskT0B35 i
  | 4 => maskT0B36 i
  | 5 => maskT0B37 i
  | 6 => maskT0B38 i
  | 7 => maskT0B39 i
  | 8 => maskT0B40 i
  | 9 => maskT0B41 i
  | 10 => maskT0B42 i
  | 11 => maskT0B43 i
  | 12 => maskT0B44 i
  | 13 => maskT0B45 i
  | 14 => maskT0B46 i
  | 15 => maskT0B47 i
  | _ => 0

private def maskT1B3 (i : ℕ) : ℕ :=
  match (i/16)%16 with
  | 0 => maskT0B48 i
  | 1 => maskT0B49 i
  | 2 => maskT0B50 i
  | 3 => maskT0B51 i
  | 4 => maskT0B52 i
  | 5 => maskT0B53 i
  | 6 => maskT0B54 i
  | 7 => maskT0B55 i
  | 8 => maskT0B56 i
  | 9 => maskT0B57 i
  | 10 => maskT0B58 i
  | 11 => maskT0B59 i
  | 12 => maskT0B60 i
  | 13 => maskT0B61 i
  | 14 => maskT0B62 i
  | 15 => maskT0B63 i
  | _ => 0

private def maskT1B4 (i : ℕ) : ℕ :=
  match (i/16)%16 with
  | 0 => maskT0B64 i
  | 1 => maskT0B65 i
  | 2 => maskT0B66 i
  | 3 => maskT0B67 i
  | 4 => maskT0B68 i
  | 5 => maskT0B69 i
  | 6 => maskT0B70 i
  | 7 => maskT0B71 i
  | 8 => maskT0B72 i
  | 9 => maskT0B73 i
  | 10 => maskT0B74 i
  | 11 => maskT0B75 i
  | 12 => maskT0B76 i
  | 13 => maskT0B77 i
  | 14 => maskT0B78 i
  | 15 => maskT0B79 i
  | _ => 0

private def maskT1B5 (i : ℕ) : ℕ :=
  match (i/16)%16 with
  | 0 => maskT0B80 i
  | 1 => maskT0B81 i
  | 2 => maskT0B82 i
  | 3 => maskT0B83 i
  | 4 => maskT0B84 i
  | 5 => maskT0B85 i
  | 6 => maskT0B86 i
  | 7 => maskT0B87 i
  | 8 => maskT0B88 i
  | 9 => maskT0B89 i
  | 10 => maskT0B90 i
  | 11 => maskT0B91 i
  | 12 => maskT0B92 i
  | 13 => maskT0B93 i
  | 14 => maskT0B94 i
  | 15 => maskT0B95 i
  | _ => 0

private def maskT1B6 (i : ℕ) : ℕ :=
  match (i/16)%16 with
  | 0 => maskT0B96 i
  | 1 => maskT0B97 i
  | 2 => maskT0B98 i
  | 3 => maskT0B99 i
  | 4 => maskT0B100 i
  | 5 => maskT0B101 i
  | 6 => maskT0B102 i
  | 7 => maskT0B103 i
  | 8 => maskT0B104 i
  | 9 => maskT0B105 i
  | 10 => maskT0B106 i
  | 11 => maskT0B107 i
  | 12 => maskT0B108 i
  | 13 => maskT0B109 i
  | 14 => maskT0B110 i
  | 15 => maskT0B111 i
  | _ => 0

private def maskT1B7 (i : ℕ) : ℕ :=
  match (i/16)%16 with
  | 0 => maskT0B112 i
  | 1 => maskT0B113 i
  | 2 => maskT0B114 i
  | 3 => maskT0B115 i
  | 4 => maskT0B116 i
  | 5 => maskT0B117 i
  | 6 => maskT0B118 i
  | 7 => maskT0B119 i
  | 8 => maskT0B120 i
  | 9 => maskT0B121 i
  | 10 => maskT0B122 i
  | 11 => maskT0B123 i
  | 12 => maskT0B124 i
  | 13 => maskT0B125 i
  | 14 => maskT0B126 i
  | 15 => maskT0B127 i
  | _ => 0

private def maskT1B8 (i : ℕ) : ℕ :=
  match (i/16)%16 with
  | 0 => maskT0B128 i
  | 1 => maskT0B129 i
  | 2 => maskT0B130 i
  | 3 => maskT0B131 i
  | 4 => maskT0B132 i
  | 5 => maskT0B133 i
  | 6 => maskT0B134 i
  | 7 => maskT0B135 i
  | 8 => maskT0B136 i
  | 9 => maskT0B137 i
  | 10 => maskT0B138 i
  | 11 => maskT0B139 i
  | 12 => maskT0B140 i
  | 13 => maskT0B141 i
  | 14 => maskT0B142 i
  | 15 => maskT0B143 i
  | _ => 0

private def maskT1B9 (i : ℕ) : ℕ :=
  match (i/16)%16 with
  | 0 => maskT0B144 i
  | 1 => maskT0B145 i
  | 2 => maskT0B146 i
  | 3 => maskT0B147 i
  | 4 => maskT0B148 i
  | 5 => maskT0B149 i
  | 6 => maskT0B150 i
  | 7 => maskT0B151 i
  | 8 => maskT0B152 i
  | 9 => maskT0B153 i
  | 10 => maskT0B154 i
  | 11 => maskT0B155 i
  | 12 => maskT0B156 i
  | 13 => maskT0B157 i
  | _ => 0

def mask (i : ℕ) : ℕ :=
  match i/256 with
  | 0 => maskT1B0 i
  | 1 => maskT1B1 i
  | 2 => maskT1B2 i
  | 3 => maskT1B3 i
  | 4 => maskT1B4 i
  | 5 => maskT1B5 i
  | 6 => maskT1B6 i
  | 7 => maskT1B7 i
  | 8 => maskT1B8 i
  | 9 => maskT1B9 i
  | _ => 0


def W (col : ℕ) : ℕ :=
  let ix := which col
  if ix=0 then 0 else if ix≤840 then dense (ix-1) else 2^(ix-1)
def cert (p : ℕ) : Bool := (decide (layer p < 21)) &&
  (combined 6 20 21 56 x y z W layer mask p >>> p == 1)
end TensorTwoSided.Seed20

namespace TensorTwoSided.Seed20
open TensorModularMinor
def raw0 (k ij : ℕ) := packedRowFn 6 20 21 56 x y z W (ij/20) (ij%20) k
def evidence (k data p : ℕ) : Bool := (layer p == k) &&
  (mix (field 2520 data) (mask p) 120 >>> p == 1)
def cached (k : ℕ) := packRows (2^2520) (raw0 k) 120 0
def checker (k : ℕ) : Bool :=
  withWord (fun data => decide ((∀ i : Fin 40, evidence k data (k*40+i.val) = true) ∧
    (∀ i : Fin 80, evidence k data (840+k*80+i.val) = true))) (cached k)
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked0 : checker 0 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked1 : checker 1 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked2 : checker 2 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked3 : checker 3 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked4 : checker 4 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked5 : checker 5 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked6 : checker 6 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked7 : checker 7 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked8 : checker 8 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked9 : checker 9 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked10 : checker 10 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked11 : checker 11 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked12 : checker 12 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked13 : checker 13 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked14 : checker 14 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked15 : checker 15 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked16 : checker 16 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked17 : checker 17 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked18 : checker 18 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked19 : checker 19 = true := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem checked20 : checker 20 = true := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem every (k : Fin 21) : checker k = true := by
  fin_cases k
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
  · exact checked4
  · exact checked5
  · exact checked6
  · exact checked7
  · exact checked8
  · exact checked9
  · exact checked10
  · exact checked11
  · exact checked12
  · exact checked13
  · exact checked14
  · exact checked15
  · exact checked16
  · exact checked17
  · exact checked18
  · exact checked19
  · exact checked20

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem evidence_all (p : ℕ) (hp : p<2520) : ∃ k : Fin 21, evidence k.val (cached k.val) p = true := by
  have cv (k : Fin 21) := every k
  simp only [checker,withWord_eq,decide_eq_true_eq] at cv
  by_cases small : p<840
  · let k : Fin 21 := ⟨p/40,by omega⟩
    refine ⟨k,?_⟩
    have h := (cv k).1 ⟨p%40,by omega⟩
    change evidence k.val (cached k.val) (p/40*40+p%40)=true at h
    simpa only [show p/40*40+p%40=p by omega] using h
  · let k : Fin 21 := ⟨(p-840)/80,by omega⟩
    refine ⟨k,?_⟩
    have h := (cv k).2 ⟨(p-840)%80,by omega⟩
    change evidence k.val (cached k.val) (840+(p-840)/80*80+(p-840)%80)=true at h
    simpa only [show 840+(p-840)/80*80+(p-840)%80=p by omega] using h

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem mix_agrees (k p : ℕ) : ∀ len, len≤120 →
    mix (field 2520 (cached k)) (mask p) len =
      mix (fun ij => raw0 k ij % 2^2520) (mask p) len := by
  intro len
  induction len with
  | zero => simp [mix]
  | succ len ih =>
    intro h
    have eq := field_pack 2520 (raw0 k) 120 0 len (by omega)
    simp only [Nat.zero_add] at eq
    change field 2520 (cached k) len = raw0 k len % 2^2520 at eq
    simp only [mix,ih (by omega),eq]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem span :
    ∃ X : Fin 56 → Fin 6 → ℂ, ∃ Y : Fin 56 → Fin 20 → ℂ, ∃ Z : Fin 56 → Fin 21 → ℂ,
    ∀ T : Fin 6 → Fin 20 → Fin 21 → ℂ, ∃ u : Fin 56 → Fin 6 → ℂ,
      ∃ v : Fin 56 → Fin 20 → ℂ, ∃ w : Fin 56 → Fin 21 → ℂ, ∀ i j k, T i j k =
        ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  have checks (p : ℕ) (hp : p<2520) : layer p<21 ∧ combined 6 20 21 56 x y z W layer mask p >>> p = 1 := by
    obtain ⟨k,h⟩ := evidence_all p hp
    simp only [evidence,Bool.and_eq_true,beq_iff_eq] at h
    refine ⟨h.1.trans_lt k.isLt,?_⟩
    have eq := congrArg (fun v : ℕ => v >>> p) (mix_agrees k.val p 120 le_rfl)
    have result := eq.symm.trans h.2
    simpa only [combined,h.1,Nat.reduceMul,raw0] using result
  exact TensorTwoSided.spans 6 20 21 56 x y z W layer mask
    (fun p hp => (checks p hp).1) (fun p hp => (checks p hp).2)
end TensorTwoSided.Seed20

namespace TensorModularMinor.Seed6
def x : Array Nat := #[16, 56, 20, 17, 25, 27, 2, 53, 13, 32, 23, 3, 40, 48, 30]
def y : Array Nat := #[56, 50, 4, 15, 57, 48, 11, 19, 39, 10, 29, 31, 60, 22, 49]
def z : Array Nat := #[51, 14, 18, 52, 50, 88, 102, 28, 45, 48, 85, 105, 97, 72, 67]
def W : Array Nat := #[
0xf7ee67b98003870002580ac04bf7a0c6719820234456ac41e9b154fedceeb48,
0xe00e20c89ff311ee6a048434a400e6ea111ae6b2dbff877a43fc1d20a269602,
0x1c299c166ef1474ab491aae860c1ecde8d5f4b6433863fc2c9ad5e23d8b14e9,
0x63f008502f12874486f2efc437c8bce3bcb0e87d8bb512932a606b85a4a4f97,
0xe20a1be873396e79878332adc424fd12d2f3984a612309188df31cd4c54ae72,
0xe13c48d121e884aab716aec9d540a1b717a62b7a0f77dbcba01e7abc74ebf8f,
0xfa23afeeb17fa9ac0151bcb99c45fe5246908018e02046508e0e957e3e78cff,
0xdd1f7f7d1771de68449a257c0fff612e0fec862ffa47f8ba01c4be4064b922,
0x7801dbe763d778ad80ebc45cb60538893874180ef90f2f8019af4bdd75f80d2,
0x603f84ff15048d08491aa895b3feefe9beca87049e3bed2c3d102827849b59,
0xe3ca7f39e21f3d0633fd6d2fd0c8cd662b1ba332210c1d91e783b5bfbe4ccf3,
0x0,
0xf7ec3c80ecc1ccdc86cfbdf58fe9517ca165e84ae0d1a7f1f7b0f61b6011ee4,
0x92efa85ea3e45271a781a19173ac49e59dffba7ef72246588e0ef8a2cf4aadb,
0x67ebf37fc1fe11d2cc8809fa8b33dd727ef02cc3e96ad269703310e86c5ff14,
0x6c33d09f5e2d08b47b48079b90ba52cc48c027999ed09040199122089e906cb,
0xfbf257a950f500b5b50b88d07bc10f9b3444bb4fd4b42521f44183381defaae,
0x0,
0x7b2be36f9deb4fb3b51400da6981be3601179b65f668aee1edecc56333b3141,
0x53013604d0959968404c2d95fb6e9126389e87932994b481a6ea9f5903242a,
0xd326819aecb150685a564e0d18128dd24b8c87c73dfb8b9e3c24b30ba8101d,
0x90ec7b31fe03f3e8de1a6fed5b330389ecca0dca42ab2d288a5de2e5204d688,
0x9bce14985c2ee17895e087fcda4d717e8f306947be014b3243fe7cdb0890209,
0x4e467e183fe4776cdfe27bcbe7ae97075de4cff58ced56ac3ccf54c9627be0,
0x66cbf4cfddc24b9e127c47339dff008b6bd8411e81ee929ad3f31149a681092,
0xe003bf7efde8a5e8b4474218bcfb1328a2822b501c01c0416e1e1ac37a5b87e,
0xf8346801a019c0e612226bb727339484b96261366fdc7a588012c0830283fcb,
0x9af467a19c129a7e4a1b8aaf57c1d13db293e48cf177a0fa444f4f1a6e6bc03,
0xf27c84f21d3250695a04b8ae200eeca74c6297c6c315668079c7d4314947b6,
0x8627d73f421db80631a566f127ffe94dd4ef031c9a65733164715ca75ca3109,
0x0,
0x74f43f60ed16e29eb41a298fe44d7ce9d5096b58146aab41fde1eaf640b37a0,
0x7001c3f70d05963aed57ceb2c28406c9a5f9cede028a243b37ae92ca48cecbe,
0x71339c0e72dc4feeec5fcb911477de9e16310ee54bb84593202cdd18345f2d3,
0x0,
0xf621ffb7fe369aee87ba2fa394ed5f6cf53d087090b76e61798025cfc431445,
0x8d13c89f32cf3b4ab51220bd532458e7fe176b5a19b976508e0e84dd94787d3,
0xefc25f796d16e29eb41a20296fc0c8b3ddd0eb5ec3ff811badd376991eebc0e,
0x6f39fbe601a65a2028eeda647cc700a329ce01731309222d7be7f67a5e0c5c,
0xab5405500000000000000,
0x74063f28e232fb3cb7174d280749934422152f576fdc00b3344d179694ea211,
0xeb2c4c513dce803a68ec4eb2e10e1289aac166bc9a30e8c963e1b9f262fbdaa,
0x7a0a1f28601fcbe91dfccb3e28fe2d5f626855c6139805abb7a2317ac069493,
0xee044f101ca8f345b37c642f933e4eb79dc05aabc0c183ac78ecfbca0b0a7e,
0x66dc1ff063db914cdf6aa5f0694444d09c3fadfb210e1e2010314c5080fc1aa,
0xfeca6809a234a2965a59e0e6ce00399bdc7705bb9354ade9778071343c053b0,
0x0,
0x1ff3a44e9fe011a2328dab1052ff3d13d438233c9a6784b01a71563624fe8aa,
0x89001f7063f2ae96b5bf4033a27b68ea21216b7b467801a1600d05b3065a77e,
0x81fa13b85c1e2634ecd7080cdc0c1e2b4b808ee694e005d087a1ed42a6eecfa,
0x76ee58896ccf519eb42165f05288dd546b1bab307e0e67089de3afe018cfa3b,
0xf90ba84ebdd2d5e05b87009ac9b348360635e12ae258cee1645fa1c390b25c9,
0xe1c408803c31474ab491a1d9ef3fbddb194a4a563a77a4f1fa7374765a5a9e8,
0xe8e004001e2a9a9eb6796d4f8a4c317cc69b0953619b488013e3f66898c8241,
0x0,
0xf50603280ec256a4de9524b349b2269590dfe5c445579e22d9a26cafea4c60f,
0x7f260bb82ccf2670687de0156c80aa30431eb6811ee1c651e032f81c286ada6,
0xebd663e98d05e6daeed6a644eb05b5ce85452ef49cdcf6e32a43ab492196961,
0x11f86f31acc6307831e5a3d3d57354ced2be233ed6b845edb02f1e1cc6fedd1,
0xfeca6809a23487dc5b7086c3dc8072594e78459c93b56da9700d42522c06bde,
0x7c39b7e731a2e3400d16c24a40ce6ea3796e03f499555633a5f83708a03ba4,
0x622e081832e5d63add57cc173e3ae03237f28dca06fcb30a53ff93557f6a2fc,
0x7329c7271ff333aab4f009f4b6c93bbc3054cb693776e8080e3c0adc92cc19f,
0x6a3de817b2ecc3345b37ce01e5ba19f0810005bee2d0978bae20148938b1300,
0x6f1c4870ce6747001c008594df340214f9a8008443018f1646f4890eacc340,
0x651057a1402f2de685c4c603e1fa119ab1bc0868a8c2cae24dcc97b047017ea,
0x0,
0x7fde7f39f0ddf49eec2706b9764839e2035b8ee98758b3c167b152ba26ccc38,
0x961dbfb6f2e5a2d2def301910440086a34758dd606136f09e3ff83757e804a6,
0x740464118ede223c331406c259fae9a978b48337c5e0f259f9a1bf922a86dde,
0xed27a76e81e3fc76ec604e0611f62855a8f26ecbb675de124e2ce3d9cb58c21,
0x630dcc972ef756705b9e6e408072e1c25bbf05a0398773380de20a435ecce9e,
0xf9f66c89bc3707d286f5686a8f7324dde072c850e5a81ae89a43cac72248f55,
0x96e5cb372ef738ac58e88105b7083c7a5d52c59757f19f3bbde237395f24e9e,
0x0,
0x77dc07701323c308327da837a9f730f215d2630c045ab7c2d98d235db7dcdea,
0xf0284fb12ec23c700220c9a7157bad47fb096024c0a88ddbaef33be980b2258,
0x7dddaf66ad1c1d4a312a222c334dbbde38a923006afcb1100a9daa025a373e9,
0x792fbbbefc3bc87eefa66c24b9bb71c2237e6efa1900000000002d169802616,
0xe0e594064cc60f06eff84ec708c0dbabb83e0ef948a88ddbaef3225a80b226b,
0xf4ddb326ceecde0e5bdbf08633b237678bf9c5a2d64802a164bc7e4352cf22b,
0x1b16472910cc9900b65e65059f72ebe3c8becb7c3ce08f7aca4f710f4a7f656,
0x8511b0d6d132c7446914416d1c3a1e819e2d4688bf1182a09d2f61370adff93,
0x842bc0df1132e20e683d23a7823a6680b0b2a6ae9a68d470978cb8f48cdc7b6,
0x1c26589960330cd46aede1178d095a13e978e685243061a017822b6a88a786e,
0x9407d85f732f5a085998444819050b20f842e58b0832f15094839990d67f2b4,
0x7815cbb73c3ba5a4ecce6c2aa5bb01c264c4aef35d105b7004530380ee003e6,
0x0,
0x4f214d851279da4dccd2cd1b3f62e1d7c680de1a87bc228079e70de7834790,
0xf4222cd8a3cb65e686240b6dedcdd857236f6842b3a953c3b03e5339d8814b3,
0xff9cce6d25d63a02b1696fc7fbe763312d403457c2cb42d3fdfc42ceef6ec,
0xe1c1bbf6e1fa3f96325cc734eebfbb85a2916303c0941f397b6f1e5072fc0c7,
0xf4ddb016ceeeb3dc849562022a363f34a320e87de447c0316103a46d3a6e95f,
0x0,
0x1d1e7099ccd6884ab52961cbc8be4d7e46c02b5f3f0d2e99e55e53ee62221c1,
0x15fa20989e043376306301cb523e49f963234332ef0d54716101a1c810fbbca,
0x9f27eccfbdecd90059b8cf59b3cca1b67b9f45bb1b3239ab2e116d119007e99,
0xe2e41f607dcef7d4b4b0c557df76842d37be8b46bb75de124e2cee0e525ea37,
0x95db832e021156e8861c0ffb2fb2d01119e38873212109a1ef337f8a9a4dc30,
0xe608577141dc59c2eceea1b98877d8753397cefcce77a04b268f7777c45d7f7,
0x84f807201c3bf70031bb833a4672764968d40310a39937b2498e8deaf2a46de,
0x18cfa0ce81cd073ab70fcba212b7c4c10a670b7bc6eddd1a4cf11bfe3e06cea,
0x90140fb0223ffc0600188f78f1cca9e991172027d2b8465329a1feab865e01c,
0xfc205491400b61ee845c8f10e3c9778a9575087160c3f8817ddf97fc46fd7a6,
0x83e85ba162335a78b5e08bab7d8180b55de84b61b3fd83bba690d6ff9eb3ab3,
0xf63064c19df6f7345969a4002dccd9b7dc06e5bbc1961c4320227c0eea0600f,
0x0,
0x75d5a0d69dc58c0eefd8c98f9936eac131b28ed0f71e3873278c81777a061b4,
0x9fcbb37edfecade858412babdcb78a2dca5285b608de9040874c8dd418b6411,
0x7205fbe7e1c6163430d225fee9bea7fe04018326e2230f096a4cf1fb26fa951,
0xecf43890fe2abbdc68930e469209b1d3cfe0669d6afcc9e1e7a07c7a944e7c0,
0x76e42c40bfd4c7dc692daaa8f8c4743c2cf846a08cb43ed3a49f91bebc4ab11,
0xe205df677dc5fceeec59aa004d76cc2cae6a4ed1a520d11a4481f7cda205229,
0x0,
0x6d0604d81dd847ee0059af6b6b7a3bc5c2750037a81c408aca50f2da23b6fc5,
0xf70063318ef49ae65b99ecbed2bf5393233c05adb2994a3b3123ad29bc94fec,
0x8fa0cc83fecade858412ae6477792c2ee1225b0fa885f01e3ffcc71d2b6f62,
0x7eebcbbf3e2a9998b6678a2e110c2aedea648b6b9c2d6801f7af7c9008e8765,
0x6de2481932936e905a426fb0463677581833c5b6b87bb919e3cf73c063b1dd6,
0x5ce34d8d38251aadcf34f4cbfcd684664a56dd0470c66dacded3ffd7287ca9,
0x1adfb3eed31c4ce8ec4121398a09bf538bbd6ef6610c64d96a526f5a8e964fe,
0x1be5c3e7131c4ce8ec41212a2d09235018504edddfdef3916732fcff6a9658e,
0x3d04c9122111e78845d633c177244fe8a4e287cc5d2ed17a3cf0301f84fd55,
0x0,
0x62ca7859ef27cc0601a62fca16b25a93552220319cb63479678ce6ce9096776,
0x6b0a049810cb44a458ce67e6cfc5b050961fe587f8b239a889be0e3dc422d8a,
0x8027b79e3c26adc009624e6bb371477f8eea03b38f0ad21f46195ab06b0337,
0x8631a73690f83f9eee7f0c8a5b736ccc78c78ee78377df73a22f4544567d15d,
0x64d0081030c1a54c008f4d61f581b8841e8e2003a202012682fdd26fac06dcf,
0x8be20f283e3312e86a1a6871fc729e11e6884687e79619624b5f8e2146febc0,
0x8301b456dde18896ec01ee48b3c55866805c4ed42c1f75a4d665d3ee48c92dd,
0xf27c84f21fffb08027ee0b3fe846c3cf04100182e5acc4761f9e8009a7de4b,
0x0,
0x1382800acc02244def48b635537c33560f20de9e91df8397992f76a1833971,
0xa103050ddfd96dadd352b10ce05ae3d4973edcaa13328c16dfdebf2acfb7a9,
0x1a3e70d9d32029d2334da5569e0d78a94fe82320cc0da2901dcf243f0e683cc,
0x8ed044411ff17c3c68f4c30fb573ba1637c6469dd3a4f55b23cd4759bea568d,
0x67086b71ad0961e6587926e4f78048b2fb7f45a75b0e1c3979b29fe84806d86,
0xe6e2673992fbb89e319c87c1df7384a5da20631f1eddbe125030c2f218a009d,
0xf4da58597fec9296865cc1025ebe0c8a83af88451f993263a7bc689b94138d2,
0xe52df0d7ddf15a70b478c0ddbd8180eacb7a2b4cfa448daba782630f74b274e,
0x95326cd9bdd87c980187436ea8f62cbb3f87c027d513138a4e202468d091362,
0x102c1880621df09633e4052b193f65a0bae5630ac055e5180df30f82cca28e4,
0x0,
0x1cc228d8bdd49170b620c63f46369700251d4b6fe1ba459b202ca37e005ff34,
0x63f00b602f10a2068643cd88c1b690a9fa26085bc3f2af301a4d317ccc30f22,
0x8fe7abfebdf130a468cd2e9d7e88038e17d2c6aafe6576e08a43b5560817bf5,
0x8fe7abfebdfa26a430cd2e9d7e88038ea6b2c32afe6576e08a43be40084fbf5,
0x69f1a04691134cd458b0c71b1208a9be8565e58de0696ad2c3f160102025653,
0x0,
0x53a67a99e1284425b5782cb1d7ae3c3de47c5871c321a9ac3d3458f78b02b0,
0x78e7c8cf3305c798303cc23e1737bc1f883f431cda4bd8bac44d53d19ade337,
0x98f87041cf349eee845ae71c5c8893e64f71a87a0ee3bada4ded0c39b2a6e5f,
0xf0c1a3769112cbdc5b708e1de00cf784d3d4658e1bc0c8f2444f19888004555,
0x792fbbbefc3bc87eefa66c24b9bb71c3facd0ef79900000000002d169802616,
0x9e09b7f6c3dbb406de43cfc41148bdd5f1c32dcfd499366b298069bfd8fcb05,
0xee5ccc73dd866ac0150c60d5afbfd9c5c29a021dad2eaa3adceb87080b039b,
0x8425bf26fc3bf70031bb833a4672764968d40310a39937b2498e8deaf2a46de,
0x6623800e0ec947aa5948c0c96fb728ac634445b408dc8e11f79fb0dae6e9e13,
0x6ac59fa66ec9374a5ac9a0084b7ad51d4dfc85930077a4f2ca7371b5bab3061,
0xfbe3cfef333fb790dffc8a9ba572e224b45c0dd421b76a6ac7bc26bee610731,
0x9fd05cc16f12d5e05b870a28664080352eeba5b5eb10278967b33c79e259831,
0xe93c5f716f2aa5e0b5df00c84dfbb9f4e2504b6258e1bcb9646d13ef805bcb9,
0x0,
0xf8286ff1a1ece17085c34a6191735ca01a10685a953261d1e9bdff93de14be8,
0x10301f7063d4aa06b7fe2f980bfbcf2a482dcb6b8279300169930369585b4e0,
0x11fddc47713826ac31556d13b3482dbd7668830148972e59ee0ec1f3604de39,
0x6630404101f538a484cb4663850482645e68885e18ece9a007a263e4a0face9,
0x6eca4c893e19dddcdecb0e41407318a409d6adf8c20c9089e3e3988a604fb65,
0x0,
0xeefd9c0670eb5208b59e22e3364cafdb4cc00b5f50e2f7f9e9ac845bc0b72d0,
0xec0463e19dd4967e69fd2fdef932fcfb9baa66921fb45a62501306fb36a06f6,
0x1dbb00ec00055aa02a800156a80aa00055aa02a800002a8001540000000000,
0x85e600d803f2de76b63e240ead363a99b0924b7cc6feb30253ffe43ae402284,
0x5c7a36e9fc90b3259712216b617f45ddd1e85a3805accf33ddc3f339a5a5a3,
0x8fe7abfebddf807e694d2475132554f80ba526ad8cc0cc81644cb07bc0a2846,
0xfcdb4b392f985ad400b0cbf70192fce03f3e001f1a896913a3ef73907e25d7c,
0xf519d8577a67bce6df9cc5f6a4bee54ac0ff4dc63a1168b3aa71679bb848faa,
0x6628fc83fe0b0b3adf0a63071744bc8dd70c6df0d121722169a2792706a1ff9,
0x913bedafbfef5e0001b84987555a3bb62099a03b08a47de807a0182cbe595d1,
0x0,
0x179193f65ddc56dc692d25cbf5882f8ece4726a648a92d208a5d98404c1568d,
0xb82defa7be2d0cac5ab6e4dac84d4fe809b2c5ab3977de1a4e2cbe2b945f8d4,
0x77d5a8d69d858c0eefd8c9af99b6eac531b28ed0f71c387b278cc1f778061b5,
0x691fbcdea141f4ee005fcb8be07a13cdc709803a31d1d912cdd3205ac2e8e47,
0x61ed9b36fd01e9d4dd0d2e7a773f5af6cb684dc264a81b32ca4d1304b4109e3,
0x727f73ec203a24a3312ea52d6f3c5f25ee4a3312e65fa5b2012eca910fe61e,
0xe6f64c4f2fcd559eb7c1a690fe48ee0b65538b51368a25e167a0759f6e96150,
0x0,
0x9c1998de73e78790339a29801d819983eb1883202649dd632a7fc3d0c86b686,
0x16df840e022b6e706b9d280a4977dc73291b26b22d237622d79e37733cd8eb6,
0xfe29f337ced865aadead2b0503b30e957fbb8dca9ac0b4708023ca405e4cf47,
0x7fdc27309c0d3b42b4b74105e9f3c81342490b7bfc102382d98f3acb9c7b94c,
0x6e3fa7be8025f370039807607d777ac786d2a02d8d2e22e1e45fa05ddaece01,
0x12ce3458cd4ec8aa6b1301f042f20ace83ad46b52ba400cb344ef3ae74a1a3b,
0x8f1e67399c4f3c446af2efc40cc8bd3a619aa68930c383b0998eb621ec4802c,
0x75cbff2ff0d747d26913c3fcb6c522bec2fe6683b1a53112c3ef4b8dd413063,
0x143fcc5f333a5542eee929e1dc4991bcafd9aec7325accf00ddc08e6ee9450d,
0x65e820109c1122005a5e603a0936dc70ac6ae597f0f0acf813c0559112eddb2,
0x529a4d69127c80ede652cc4d976841dc8428dcb3e79c220079e305e7a34791,
0x0,
0x74104f2130d712786bbbc3e9dc4588be7ed4c6a926a53112c3ef4b8dd413063,
0x8b03cc1f3e0f3f42b7578a2641f6fe294daeeb61221e474a4de1ae2be85e3ba,
0x792fbbbefc3ba5a4ecce6c3902bb9dc0dd788ed8eb885ad00dcd02801a0029e,
0x339a3669dfdfc0e0180cee7d40d4900be6fa0238011119b27a3b74d3604ab4,
0xeafa63e99fc5aa423354c9cfa605788aed81a31c01c3fd53a3ed40ce6e4822a,
0x6b007051c3dbc4e6ddc2a7fbd389c161b41fedf8e796616323cc867c86a4536,
0xf02fa4ce9fc966e85a1928eb3040b6eabd54e5b1f75599e16e130843205aae0,
0x0,
0xebc24be93320664ceed121398a09bf52d427aed96966b16163ecfcaf3a94df6,
0xf7ebd7ff5dd169965801e91568c85b8ee44285b280896f03a3df95e21225971,
0x650627a892ca8f345b37c6ccd97a9d1f798e65a32a863fc2c9ad733540b32ff,
0x781220c88d1e4fe6edc7822df0b72244eb91aeda94fdf9e2400f03d25c5f255,
0x15ee0ba820384f7eefa00cd959baf19bc2bfcee7e49b321169838baa9a586a6,
0x8513d72f5c3bf70031bb833a4672764968d40310a39937b2498e8deaf2a46de,
0x78e80c403de95106b41889c777ffa91028356b55a5864489e3c3d42a147a4f8,
0xf5fbc7ef0f3c7f0edd838306b97292273b7f2de506fdf9988e30a5ce8a17c81,
0xfff5a846bfc8d99058196d20ee842c3f59dfc59e803f33033dc3a2b47478565,
0x68cbd37f512f34d487552a01c80c57deffd1e841f3eda55ac3ed0a36d284929,
0x0,
0xfff5a846bfc8d99058196d20ee842c3f59dfc59e8049df008dc3a2b47478565,
0x17e7af3eaef984ee33bc4de1f1ffdf92da8ee324c075a6996dcf5d766ea03d0,
0x9eedc4871e259aa2df330116d27350a6e6432deaca844741ea4eb63da44ce6d,
0x7a11f097d0f15e786bbbcb2afc857c51e69aa6b2e28b691ba3ef2c09c410d90,
0x7dd033e0cf3bbf9033fae90187326a7e4d72c30926ccad932e1087c476a4301,
0x1d1998d67ddfd2daec88c007efb630c02005aeea3b7690832ddf904d4a06db4,
0x13004c0132e959058196aef8f77dc1c102005a588116cc1ea72ce6e92b795d,
0x0,
0x14d390de511da232ee91e2caa5b6761e0620eee4a967fa532012a52246074a5,
0x1be85f61713ba6a2ecd088c31b76faf39bcdcef47758c92a4dd2f5ee6a05a78,
0x1c299c166ef1474ab491aae860c1ecde54ec2b69b3863fc2c9ad5e23d8b14e9,
0x325a4969c026ed402d387285445a8bd4916003fe2d2ef088dc3cdbb40788a7,
0xe139cc473df2b3ad5ab08f0ab77fab48612b5594d73329596df12a825fc8e9e,
0x7a1e0f2832fa48783386ebc3f37ecdf9ac4fa318f90f2a2809a2226446f8ba4,
0x9ce4632190c8c3a45a9664802fb2be9082f7e5846ab97381603c663a6acc67a,
0xf909f377d108a9705ba52ae7788c0cb119e72585962038ca4a52e7223e05036,
0x7417a76e81d695706846aa3b5dba8f1ad5d066bba76b9f49e472b7b9aa80ea8,
0xfe35f7f7cf0b0f328717492893ffb8159c6a08574a3d4f8ba01c7c479e49f4d,
0x773203f81dd4fba46a95250309bf27a79cc666844595284009b17a02eaf860f,
0x0,
0x18cfa0ce81e884aab716a97366cdf5ed1f7fab7cd8033211fe2cdea3cab0c21,
0x99dc5fb162349de848440481f785df1508722490297bbd116df369579a6fc81,
0x871fff3feef1620079b8c9a789cc3f5c302007848875a5209a7de2c56025bab,
0x8acc54114016daeea45c8f10e3c9778b4ec50a7160b51481fddf8a4746dd7a6,
0xc1c3010d0d0ed985bdf45b016d6bb996e5e65a2d87496e3345fbec39c01ca2,
0x712f98ce73079534ecd167526457e6ebec26eeff49cfe161ea5f9ecb8aefba4,
0x0,
0x16d21888600ca1706a25e327fd080dd3c2ce26a4a9961a51f79da92116487ae,
0x93d5d85763fe0fe6df9aa5f6a4bee54b5bcf4dc65cba3cb3aa717e28b848fcc,
0x16d21888600c843a6b0c81fec408e9d17dea86b63f961a51f79d89b7b84ac38,
0x97d07fb1e00055aa02a80bbe96402eed9945e013883e00b96dde7d96ac02e8b,
0xf3fdef27ae8052a4ecc883e1cc49d1e693f98ed8b7aa1cf17dfc786840c91c9,
0x64c04b212ea5f77801e085df6c32b0cb1db780010c65877813fc2a688ec9bca,
0x9afc485123ecc3345b37c3c02f3e32b97e682587fd2c26e25a63d0bad6cd662,
0x162854c15de05a3400b1a8d988774f5ab6d6e026412d6a189e2c99c57cb1834,
0x60c457715dfde1340169a8d9884c395b6d66e03bc15b861b2e2c847e7c5d834,
0x17f3e4cf9de05a3400b1a8d988774f5ab6d6e026412d6a189e2c99c57cb1834,
0x0,
0xe0183000c000000000000e1c3800e0000000000000e1c3800e003870e003800,
0x98ee07a80e8b65e68624074fc4c10a34077ac856b6a404c08a72fd5fca80901,
0xdc87cc1ffec88a25968486c5977eac3c33dc5b6640005d1ee32e9f154b4afc,
0xf0cbeb3fb0bc7c08dd9d656c8a883215842e4ddf083d4a5a4e2eb8a052ff3a7,
0x80382bb0b2842a44ef496bd7f880039db3004ee089efa692ca604f230ab3b39,
0xfac2548950914fdaded56f2ba848cef959526df4be7a8b032de3f1c62cfd1dc,
0x9c027009c0372596025966d92900a4028574400e2879c1e00e1319e64a02ae6,
0x0,
0x792fbbbefc3b80eeede70ee03bbb79c348088ee18f69995003cd1a665402978,
0x642050515303f0eede048eb555be4f9451466dff32b4273ba4517ffb9e4bc6d,
0x642050515303f0eede048eb555be4f9451466dd97eb4273badc27ffb9e4bc6d,
0x8adf945e4f3800e03062e3d2eac552ba872543126fe3bed2c3d1131d664bb88,
0x1ace2898b0f2dd7069c2a27e15b22078b66f06a5359a7ae323f0ce1ce0ffd84,
0x713c677183d75de6b62746cce2cc9303194b4b5699885f01e3ffe1674ab4974,
0x95d1f7e7d1113b32857400bbb5feb9208292087129a67a2bb01166731e4f938,
0xf90bab7ebdfe66340331a4e8a737647481502001576b9921fdf2e99f9eb254f,
0xe41233a8c00f217eb7a00e13c7ba8998b1758b4ee475a483344cb7bc46031a6,
0xb203490cefd96dadd352b03ce49af0d4973edcaa1e1bea33deeebf2acfb7a9,
0xee0203f81df2b7a46a95250309bf27a5f8066684450c184009b15c4eeaf860f,
0x0,
0x9137cb3f3e03cb98dfda6b19a133ea491efcadd0d42377f88790e6f30c4e1f0,
0x0,
0x90ec7b31fe039e32dd726b0ccbb340491ba60dfa542377f88790e6f30c4e1f0,
0x71d5b776c3d76596b7e746c2fecce3031acc4b4a99885f01e3ffe1674ab4974,
0x0,
0x0,
0x0]
end TensorModularMinor.Seed6

namespace TensorModularMinor.Seed6

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem certificate : ∀ i : Fin 6, ∀ j : Fin 6, ∀ k : Fin 7,
    packedRow 6 6 7 15 x y z W i j k = 2^(rowIndex (i,j,k)) := by decide

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem spans : ∃ X : Fin 15 → Fin 6 → ℂ, ∃ Y : Fin 15 → Fin 6 → ℂ, ∃ Z : Fin 15 → Fin 7 → ℂ,
    ∀ T : Fin 6 → Fin 6 → Fin 7 → ℂ, ∃ u : Fin 15 → Fin 6 → ℂ,
    ∃ v : Fin 15 → Fin 6 → ℂ, ∃ w : Fin 15 → Fin 7 → ℂ, ∀ i j k, T i j k =
      ∑ t, (u t i*(Y t j*Z t k) + X t i*(v t j*Z t k) + X t i*(Y t j*w t k)) := spans_of_packed 6 6 7 15 x y z W certificate

end TensorModularMinor.Seed6

namespace TensorModularMinor.Seed7
def x : Array Nat := #[28, 51, 36, 15, 18, 28, 13, 42, 63, 52, 37, 16, 50, 33, 22, 20, 59, 39]
def y : Array Nat := #[63, 23, 49, 55, 59, 33, 59, 116, 125, 26, 9, 66, 120, 81, 115, 21, 21, 31]
def z : Array Nat := #[69, 206, 107, 173, 240, 169, 199, 233, 122, 71, 36, 29, 68, 43, 121, 20, 61, 178]
def W : Array Nat := #[
0x10f76fec9888fcecc75f7f00ec0b6fa3fccc543ba89364a3a354c7a3eca36f4f54b83b83f73b2b5fdc3b,
0x145ee26c5dd10a4ea02eac0b4e67cd13d168fee64c52012e66f5db99dba1d406aad2aa87c77b993b2e00,
0x37eec0119ccf3dc28cc9e209c25628352394a975a029f91c767c9df602bd5785faa5f985df5ebdc68211,
0xbf81a46e9cd4522e4b969d092e5d4c9dd458f64e08b196b4d5235a5576863359368e510d236e96925e2a,
0xaf813c750f57595a409d71915ace2896d43cfd2a03b196bf4db05acd021eab263d69c21d23651e014eb2,
0x87cde2ffce42994ea02eac0b4e67cd13d168fee64c52012e66f5db994832d49539413987c77b993b2e00,
0x62439311d08943ae9398695faec7c86b54a86bf76018a7cceb3473f8320f5f0d9cca9c1e3fc72aacb26b,
0xfd54b14c7a1f1fba58c794a9baba624dea7f84cc2767f83263d65a308b373b62a47a1fb42c4aad2e96ad,
0x4a1a60c73b70c6bf5f14ccf4bfa208dbe10ac5b918760ac22df45f742b0a23cdfedda309537ac7782e9f,
0x75cc2257719c875dc0cceba25dba0d4de188843b2cff603268ddc93b6737a88e370e1f3cb44a252586a6,
0xe39eac8e92e35f93004b2c6c936e4ee4e1b4b84e65846ac2734e84c5f1f9802338f131f4904ac979bdae,
0x0,
0x1b9893880b1098e7980b7f0be700fc000b6400640b9898000b0b930bec0093ec9374001b98001b0b830b,
0x817df135538d3480abf12ec780ff858dcbafba1d909f7df1670c803488a366816a1e51eab42fd34df281,
0xde1abedeae64aa5a933f1fda5c5c78c788037582c13c3cc73c8780f30aff40fc2c897a8ebd34c86e897,
0xf09ac8308cc60da75853b611a78bbb3d866c04b5cbcfa67aff30f9836cac5c14b69feaed1a1c8511b7c4,
0xf8891307fc603bc7e2a2d300c7f69b97f48d74642892e00a5115994bfb7af54566a6ced42b6f4d71a96b,
0x17c5c3102fed594007075a1a408028c186f4f82d37ab512ecf93c220136b5c3f8dbf2d0a4543621a5bc4,
0x6c3a39572891c58c6ea014298c5dc8a1e4436c680a12475e2955b0df27f466db13490b6581089909d6fd,
0x0,
0x13b0d0eb2f719e1f7da511821fee2bce72e114d187a12924061ec3f38c75a91e8f7d87de6e2c2f6bf2af,
0xc5ba684120bf4802028c8ef802ab0ef3e05af1406ddf20ad8d65b6170299b27df23dc224fdd785e07c16,
0x8046fa9c3753739aeeacfa829ab886891456e823e3b167f3243e2e5b33289a0379604b5d234b8fcb361f,
0x934742a66e9392c558875fcec5df7268003bfd2dd70753af9d52586b5c52750e640ab9b8de91a851766a,
0xec9a429c44a94f299f4bb35629d4163e0091ab87819fc263539c9636219e7c2530bbe6ce90cc552f11e3,
0x99fd62c2e895c374b16b8c1174b38621149140e44bd59034870515f8b91391dd2626e8b8648779405807,
0xb5ccee61c64d6a473aa9b1f847cc3febcd32f351217ab2747867918ed9cf098ca4e407c781c8c39c713e,
0x3a6b72b1f4816a90bdabf67a9f495c0cf8b8ca8433c9d7b94d3f7e15daf8b87620c9cd0f25c66f0ed2e,
0xbe904d699be69f5aa9fda73f5a0b7fd3e2bb10c28e59fdbd6d7612026e91c69a9f365951e672d6c1f64f,
0x7a39eb936a537dff74e02785ffee73e8e6f56454cb6aa916998d9c100de4128c2061b9377459e56e8482,
0xfcaa0752ab75e5c2d1876018c2568906c200a58e2ebd50e789d16bfff9b77cc520f05cdab3b2b70d0e76,
0x0,
0xc08d2a6e29ae0856d809d17656f4db909c21a73b72c9996131bd3457a4bb3171100f56d907774c85be4c,
0xbbc2c323780a4794697a60f194dfa67aeb142c2dc722f74d76e55ffcf85fee3790c97703c27ba99d5747,
0x8abfd17c773be4ee783f933aee98b78b2f75e4958210906385873279efdcab3afc4da235bff01ee9d07a,
0x85243a9030e00ac0607f9a09c0763518df05daa805e8ff1feeeb9ef400572138f5a9d40b24a49abe0b1a,
0x872e2416392c5f009451b85600450954f2f88c2c1dd5f5cd1be2216da4fd02bdcc9ce666d8b015d1572a,
0x7f56fe13756577f37f3a3dabf31a4f23ddbb948f63390afa365eb02fc37ea95b93061b21a01fb5ab32c8,
0x7f56f58b7ef67cf37fa236a0f3824f23dd23941763390a623d55b0b75be63ac8009e1021a0872da0a150,
0xfdf2016afb940d731f00c5f673a90d9953e45648661001b7d8a02648dab201a40db3a49217f763001794,
0xe67e3b6463eaafd12b7f3dabd18b5ad58c83d88237f8fea8364bb8bc2619206004e68cfb67539bea7eda,
0x0,
0x89ba5f889d5ba3162a7b36731d6a934cafedddd74fb4970a4db79bdc7535e43ff5f80f39be85726d80c,
0xcf675950ddd512a262342067a245fdc8365689dddc3cb51f9f8fea86543c312cff5fef60f414ab264bf0,
0xc7b1b7c35269a7df87530293df02363f7ce420d1767cc42dbde703084e48000dc0da94debf77aff7467e,
0xf76f6f9300fc00000b98930098006f6ff700986f00f7fc6f93006f00f76ffc9393fc00f7fcfc93936f,
0x393a8dbde32d274567e2340045f47828b5e6e34e35ec651ee8e378ebeef5479b377158d6cc2ff3517a6a,
0x39ef5e4ee544b00978ba3d9309fd1aeb35aa979feb57c5c4f650e840abd228616fab3b9b843c38a6af70,
0x900b1ed01a093c7ab38fff4c7931557d2ed4dfbfcb1fcb18a81c76ff6c6549a00c5f561762cfdf4c166,
0x2c2d9fc3f5e9f73654492b6c3638fa1f90cc3985a97e619fdd39a3bb93f028166cc7317feaf49dce18cf,
0x7693ba996edf0bb86c6c8b67b80086ffd2b9e5af544d93e522ba645411995429a37daa1ee5734e3379aa,
0xb4b59fc36de96faecc49b3f4aea0fa1f9054391da9e6f99f45a13b230b68288ef45fa9e772f49d561857,
0x900baed01a098c7ab33fff4c7981557d9ed4dfbf7b1fcb18a81c76ff6c6549a00c5f5617627fdf4c16d,
0x0,
0x1bf70b880b83fce75f54ec0be70b93a800cca8cca864f75430a33ba3833b00d7c7dc3be70b5fb35fb854,
0x9a2df4e3f3940cac5db1b656ac6cc9d1a648750c9a935deefe4238270f6b182a075e9dbca94ba3952f95,
0xbc78aff1588a615689d81df656b8398ff41d1a64c4ead78e88b541ad588e1a4ca79ae05493b122516c97,
0x633df56ffcfbfeb1a2133138b1ab88861ba51ebe2f0ef5920c476c5573c2e7a30a2e3234f4891dde4ed5,
0x22fb8502384ef4d46e5a1dc7d4543f61e4ecf998377e6cae4367b700dd69081f9bee3972b2a93d215e88,
0xabf7444f3ba05758807f8c5f5820134551b4dc4eee9a77ff9a83657cf221822da90481628be1c53b9f3b,
0xafbad023866f4d46e5a1dc7d4543f61e4ecf998377e6cae4367b700dd69081f9bee395ab2813d217688,
0x0,
0x943a52cf029d3a82a0e9a798826c651326af56891336011e32cee0cdd0ceb0f1564ac507a39f6ecc3664,
0x3ca81a2e3e7e2f1802167a8918143533822f13bed8dbd56047c319284a997277868876f67c8e1fb4a771,
0x83f6f9d233a8886e4cc580746eaccbe88a567f5f96c691195c0bed0f667c072474c450a1d073294c6120,
0xc684755b7d6f08e209491345e2d331af7e7b781d4f9742c304643e7827611d86898e1624ebb5058b4a2a,
0x1c3a9d29d221067f800902207f3fede87d8cca64d4435d22e2ea21deea4c9454e91255ea48bfc1792fd2,
0x8920a0cd4358e3c26ba2b102c2203426da161c988fbf9c81187f7d7ec9f8541bfb0b26ec741f7166d839,
0x60db99ef18e07dacee3a5a65ac8b37f7d9edadfb3dcf7a900591cfd5ab8caa620331dc67cc4aebf734a9,
0x1bbccb01e4081a930585d43d93faea969fb783be36f1c532c3eaf19a0ba92921630b97a931a081e3bac3,
0x8bcf9de2e774cf29499873d4298ef54a8f91d17974eb3664b96914cfd7e36bef8021435f3054897356d2,
0x48e9778376358a9d8c47a06e9da2c891967c662693949a383505b6b639b11932989b55796ae9af7b5025,
0xa9d1229c3549e094a5fae0b6944c789e5689ab1dfde13b99e12801b1c1aac046dfa8e3db3932aebb7582,
0x9e922b2438506fb4eb31c756b4330a705182ffede7554a990cc88805b38f5dcbaa74f7260161df9dd99d,
0x0,
0x8b07c22b72490ea598dd53b8a52ca734f21d9b4269adac22c62e6f453e6940c1d16611378e30e6078a40,
0x17580811a4eda727a23373a927ce3dafb813e35f5bb8e96f724a8e718acbcd1fa6796bc91c11d52eb360,
0xcb9985dda565625d5140ab935d4e4c94c53ed99f362bf0c3de13964da46bb391cac62605545c5983d475,
0x9fef7ace89bf4da234b44707a2faa9b60f132c1a40cab7e00f26b58f9d6a89dfc13497f9805b091a4a0a,
0xdcc186c70a88ce7af378d3317a8b713b7d2d3ac06d9319a7a75218372ea0758567bf46cc484687a6671e,
0xdcc11e5f9988c57af3734ba27a13713b7db53a586d9319ac3fc118af2ea0ed8ef42c4dcc484d8c35f486,
0x2827ff6ba17ea21aa067ee381a0bfab5656d6dda08f0436c336d26558a9666d26c19031aa476b6ce7d19,
0x4b50ea36233d7cb30c4b3a34b36253f49d8941c0bf319be3584098bee0fc1306a6da9fe3d3d143df37ef,
0x0,
0xd26fb40983ca899a8b782e389a89ec472855fa07f8f354eff3cfa7e9f84cb94afe6011a03b588d441a17,
0x28caf05d911b23d45a8c220bd445c48949bec0e1c0dcb04fff6b7ce6ee1bbb2109ddb9357b822b0c5b4c,
0xe61f506fdda1106549e2315465ab63e5c14d6663c4c7019c274393c231d4b26e02336f1dfaf1d087944a,
0xed3d7f0e88cfdfce456cfd9ace76affad6d7b0af4cf92718a23a5ba265e25569c602b0a0c86c504c2981,
0x9da5b7c007ab2ddf9d9f29dfdfdd7a2142c72ad12169df7f157ddf9fdbb8fc2424ed246fe8fef1ddd096,
0xbbc21ca36e013071a52ed1ab7118f92be3aa37a39dccbbe530c8e5b0e2ce4485651d2135633382342491,
0x582de0e95c3fdd11b3341d5f112258356fccd9cc9ccc8628c1dfe7be439d5d74917b662060a4aaed7fe1,
0x70b1b30d41ea4705a731ba1f05b317e630e803ed7a46a5cdd87dcf2dce4366bd1a8280c83151a2d1241d,
0x28d6281a376d89189380c78518ccbe0726cb7eb258bb457745fb324575cced5454b9cc89edb2212accb2,
0x75b2be491bf71b51140c1f5d51c7773528a4ffedfd0c420c40c30e59f1f1ccaa3bacaaab57ccfc2420b7,
0xe2a6971420c221b8206beb93b8b1f072a31825a3ac6fb65f69ef4ff9eac27e89a11589ce2c3c033945a6,
0x0,
0x62d76d663b55cbf2733f614bf6e8287b55f70c7c59f120c835ce019f44fa8c5edddcc81be72cf24d7df,
0x8ceb2487574231097fd8d1540911d4e192364f89f77fb48645d722cc5a2fee206758d639f256c90a39f6,
0xe5b59c999b05247ae77acc167ab82357b989fafc0a27f90f842047fb2717b0fee011d9ec17adde86271c,
0x6fbd52758f0f021dd3697a291d1ffaaba171220ce0a34d6a50ff1cca85bba2b441204b2be369905f517d,
0xe9e0f9fa86e9abfda08c2ed1fd0935a195832ba8bed54804e4ae55fe363e22df76605deeea7769dc7422,
0x992d74614857aa2b983a82422b6e6bd6b373464e96142d4582c8169b11680ad9b3d6986242f007e7c9d5,
0xa022719f885305ba0234b6bfba004cafa81eaec74f3a00b46bdd5ae223a36fb9718f606dcd07adf92fbe,
0x47bac7f6c42703188bd44c621869dd277dadcfcb98ef0123baa00f5c2a22ef2051d9968ed5657bd0cc68,
0x0,
0x70557a03392d0a45ff71349345f43147da58aad613a50a7a56397855436d47ca098d66e3cc4ba2f786a8,
0x4a98d80c559f6a26771d30ba26ca2b02da4aadde4c1658dc5a11c3a586dd4269105916b5f40dd0b9d54,
0xb1acd7fe02c2d1d62ba11c71d7de20c35372711d93e17b0cded555d866b811bac7e26e4ce2ce1cf8423,
0x345000c704930ff6930bfdc7f69822786f3e6b85acd4a700ebacbff8350f000a045e50e02c6f6f7893b4,
0x6092030460659ff8a967b46ef88297d5e93b6b646326d413b551efc9a0c63a2b0d3fe8aacc3c8d1f436a,
0x2b14d347b2f6d43dc994d3983d11f19b7c0e4e1d32dcd56224db5ea407aacd7866962b7fd938787b5d6b,
0xbe27fc31849273425454165f425f97c8a85497a3972334fce0c84360d534a849c8ea346a5b0099f8925b,
0x46e8114ab4dba5348c0920ba3433ca211b2fa7ed3ea898fc54443538f812a32d15ffc1b71ef4323092b1,
0xc14a13a2197b292c9d45136c2c7d4d7ce74ccd302a5bd4c604f07262dd9922bbfcb12b9207c743ebe6ae,
0xb659ea0e24988c299fd3b85d294c1cfd0bafc0b9494b015810fc766686024715c8bb7abc40cc549b88a0,
0x0,
0x0,
0x8fdef030033c4d62d48eec7462ecb9741028cffcdf1ff6f0ec83e06565b3e47782001888cd67296c5edd,
0x10bdc7c884a4bfdf8e82b4ffdff6d55a5123e079f8b530de1d7e812bd77f204d5870f33f23d0c6e24287,
0x73ba4e49668cf7e2c90b67ffe274518dcd187c9f9b89c3aa8640296a7cc06f5a5fdc1a5fa3995eca980c,
0x60261ea75c0cf78980961f6789b391074617e798a15c351e08b8a3e4e179a0470b8d200840ffc2fd087e,
0x1a8f30fa9274553a2b20d6ab3ad4a0e80f1be51a89f9c3fc5576dbd5a8bc208ca10a291d8c8fc20127ed,
0x71da251e38d15493d4c996ab932b0258babf4fc7f5333ee903dccc7cfb4990aa3b97d7192fc4e865d5dd,
0x2f30bca7d2b7673e77458f4738015583fe219af45055b5492d573812d144ffe9a178a05f073a6462c09,
0x0,
0x0,
0x71eb3dae6147c173422cd100736eaacff5c67abe8f7b767bec23cd1a8118de826b2dcbca7ba07ee619e7,
0x2732d4538bf38becc282146cecbaa3bf10a6e43bf465485e6171317b73f219b23a712a74c4935d856e9f,
0x9800bc4377747e98b64b5df498a2b0a748446c2a4771ea36e235d11e9842ba3f00386563ce2fd72db716,
0x9c2ee9cbc7376cebdffabaf4eb4cd32fee1283496da03e7a90d754efd749a3d930efe4f4db083d9a33e5,
0x0,
0xced9c6be9653a70736e50b930776b9d7adbcf2373c6fd413fc6c2d7f6aa8ee9c5a6417dd711cf445536e,
0x74640bec6fe76fe75f54ec0be70b93a800cca8cca864f75430a33ba3833b98d7c7dca388985fd73bdcc7,
0xf33a7a13a13d653167e2400b31ffa247da53aadd135292e9a1a18f5ecb9a47429196029cccb74e6ff9c7,
0xe3cd156c322d994538b6ac98456731182df002894ca5924a669a279927aab00d32b6a18c3b8c6554bd6f,
0xf33ae91339ae65316771d39331ffa247dacbaa451352927a32398f5ecb9ad4420905029ccc24ddf7f9c7,
0x87a915085649fdd638253f98d6f431182df002894c3692d9f59ab40a4856bb62ced95614a38cfdcc25f7,
0x0,
0xf3cd8de4a13d92a26771d30ba26ca2b02da4aadde4c1658dc5a11c3a586d23269105669c3b40b96ff930,
0x78293bc896115a78ce001f9178cefe5f320979e14b86c75cb6d06fd3edf5382b368d0c3c7d90428fe4b5,
0x57326a9c1de8eaa02b49d193a0182d4585333dfcf1d48a3578fa6b0d92e61aeeacadb4652270c1a6acc2,
0x9c13dfa677d980f4c2dd1f0ef40c108675bc796426c3e922a17a15875ac9ba2b9453f3f3f8fdcd3054cd,
0xed3d7f0e88cfdfce456cfd9ace76affafed798af4cf92718a23a5ba265e25569c602b0a0c86c504c2981,
0x7ed574b28139218c657f076e8cc5460aca9629a3aa931380934718131d55299d908c39c8dfd8282a703b,
0x0,
0x360c41785707a3e2a0e947f1e285674adb547a89e8c1c069f8b3e34747a5232e617fbe655c7aaf2cd3cb,
0x0,
0x8a3d8c9a9db55816094ed876162eb415bcfba0d11cbf1cc7bbe35f32e10de226151b755a60014ed9b805,
0x7ff3bccfa811a15acb182b1a5a9f08a1bd2f62a4f5c75fee5f2cba5f53902fb1823d0e32a4ffc1f15caf,
0x8f986dbfe6527cd396968720d3693b4b1f3b9cf0a99bbe94cfe819a3bb34fae41a233455743a5e1d88f1,
0xea97873ee192d8bd538b5f1abd072ef515f5839fbc4293d5e1cd768ed55cbccbe3e1f78f686cdf90e456,
0x95643bf1498379ae98933d00ae986f54a893e1724985cc3bbee1ccd1cfcc93336195f9bdcc931e61b8f9,
0x4360da04b93cdd7356da5d6573a9bd42a29156d1f46c422ef433cc0bde63d537a377fd808f9a78e7385e,
0x43c5d758d239dac0b62751b6c0916fa6288c857e879597ce6d5fa391a21771cd23cbf1c7f76c9bdf18e5,
0x58f8168caf650720091dc9f620fdba4749bccd07e756c9bd5d36eb9db5512b08afd7a50cab1c12aff159,
0x57808bf52ade826ccb0085f66c2245fd016dcbccca866057113d0fbe6ecba9870838ddd0045600058ad8,
0x677426c2d2da410e91ddd3400e00089c2745cc30a2526ebc6de0efc1c03124b34da2950b34d9fd963fd2,
0x55c65251565c99dfab3625ccdf67b6b5991a2cd1b5d67dc18deddfb1e43b321acce4f7d1e37dc6466732,
0xbddd643f6673f5d6df13c5ccd6dfa4fb970778b58c1cf53bd2b9c182e22a4c6056bfb9a3618f9ab87900,
0x0,
0x8d35ff753e7eca53fdff07a9535d500e4fdfb564fab11754da1cd143fcf2a2c8f0ca59c978b2e57ae7c3,
0x21396cde06db9d8b696e9f008bb183851fce25e173e36be6207cd5458a3f6c6095e3721a0b2cc020fae6,
0xad298097e10a9665545f6554650b97c651bb1df74c5076eacc4964a33e920135510aac9829226f286501,
0x5459154f0a9356e26bebd831e213713b7d2d3ac06d0b8134ac5280afb6387e1d67b44644d0d59ca6ef86,
0xccc11e4f9998c57af3734ba27a13713b7db53a586d9319ac3fc118af2ea0ed8ef42c4ddc484d9c35e486,
0xc93550a665b47ce7f4bdc9c7e76c4d529a248afc101842c3774d6598bca582f6fdd208fc3689a5318190,
0x8cbe39aa259817cc005f0098cc93eb7b1100951ae7e6c99f2a0d2dc6ae61c439f1f66ae3d8485822c109,
0x0,
0xea7ca63046e1a90211898bcb028b7ad6a16181d6692191568b2baab4c11878b05b9cd64bc0aba3923605,
0x9188463b929461cc347a5fbaccdd403167cbbf45d891b7aff70558b7aacb875f82637037bd9c075c3b1d,
0xfa977eb21ec79782893de0e082ddbee92946a864e2c836215f482a69eb1e9715b91a8d2a5e7a500e3c43,
0xc2e86c8340b3db1da27a934b1d6eb10c5de839d107ea4a98b84a888def07275c10db9fb32259f2a5169f,
0x3e8c677f2f06f6f62c0545e5f6a9eea46b8ae5c7ed5e6cd10c3875a09774c1121c63f79523fde284f0c7,
0x2839ce12b9a8803f5dbf2b6b3f54de740f9cbabe9fcb7f955e88149d9d92152163585c4779364656e517,
0xffbaa1d6491de8e253807fa0e276cca5837b799ffa3e7189fdd4030b70c9e623614d79a67e31e9b8b221,
0xecf08c3067d6a90b4016675d0b0932ba0910ec7ee58b2bc32ebcfd3da8b0e567670100993d558fd2dc05,
0x9a2efc8504fa04589fce7fab58e778a855e39c54e3b802e5d7565831a70aa0b65854d972d893e465dc83,
0x7252b43780ca816c7fe0eb986cba7195d3ebbb1d2144ea16884fb09b3fe24d2b0894b2d06a7a485e7bed,
0x5426fdd1ac0c517a73f4cccc7a31c40a4bb460ea486f1a8a93997b1a7ab2f552fbb1a45e26be1166a418,
0xe6b18cd9f8483dc95dc056fdc9abbe9274702c75725d2b1634bd603d35c46697c09b07fb8a92d3f8303e,
0x0,
0x2c512d604f5320b8eea5e99ab822c5bc123fe70bf56d04d9fe45cd81bcd85f11a8d07eef0f0bfa183bc5,
0x7b4900c5def0de0e531494d30e47a88942261c307491b97e00aec550fda0d3a41da0ed31b175aa1d74e1,
0x4ec5648b65b8fd4231a5135342fdc0775bff2ccb779f1090054736dc2ef5f08a61d166e569ed70322bdf,
0xdf80b5b591206d5125b10949516e02355be5fbc78a6425acfeeb9bd1ad7814522d0498562675d3055f24,
0xc20386ecab696f895d80319f895d1030811986a3645589befb217edd7b93240207860bfa3696e29a0547,
0x3ac598906e5ff636a9ae6cc0366e537cac9bd0587c68836c0e28c1445af50702f236f591fa826bc55f47,
0x0,
0x1d8338c131da09d878a933ddd8ab1205da647dfcee31ac8a0ec1e594d6eb3b5b218298ac107ba994c9fb,
0x6508e3e998fd3956859fec0b56098db5efb118f0dde105368e4a6ae1c62501253bcd65b1cccf7ea44cc1,
0xf6ff141e98fdcec5850c7f0bc59a8d42184618f02a72f252ea4af985cf4165dba1cd9bb8a838133edfac,
0x16942ca6a19fee5deb5a4ea05d3839b3764e10a34c43ea7a737e15c6caee57d990956f338a5e44c47db9,
0xad26074bce841c0e7609800c07d78173525ea4ebc69a6c20d480b9737e933fe59c64021cbe94cc38de3,
0x5fa986408a3a93d6760ebd5fd6188db17cc013af6f56160cf5e320a6d4ef6d75ffe71b67b49b36720bb6,
0x33d5bbf6b167f4e91f227633e991edd360df6db944e22883e232b631788cd429ffe0a22741e862e527b3,
0x804281cace37adad1339331da025c3bbdc307a4d9476d67b93b735cb5b8009e588807239d6892bbd211,
0x50c580eaa14a28568eb807a256c5d16004f89285df7cdb992c697c2f95d175a9a206a9dacfa645c35384,
0xd4311291eed40273ec8b9f3373b86bb3740dc716b3baed7520cc65b9ea46b9f867eadeef327e5fd54d55,
0xaec6663fd847b73693c5079a365f39566f3b70721fbdc5922cd254406439a0ab5b0d072df46cdaa77c3e,
0x0,
0x52da5ae247525f8c18e0333a8c47eea68f652054e6990cc06c4e19137540d79590b0b2d872c38eec274c,
0x664d1af43cd0da6b85e500ab6b9a163f9c5b1c98c9348f6400d6d4669c72ba9af0fc3f098036d1bb0e99,
0x1122704031b803daf48c0993da02d6cfa3226e45cd11bca58bf0b848d8aa29f3fd71a88b04335aca13da,
0x931c15317f4edf02e5277a91022b2c702637ff5890c844f8c50f4a6a0084b92c5d9818b6123e90729dd1,
0xb47431f0eca5d6678c7d6bfd67542f34faae382d8b11dbf4b69c13bc6a2f4ef7cf3708a47e1ec5e8bce9,
0xe2f3e895efcb4e7a76d1a0097a4e580fa3b13bc0b2189dd08b5eee1880432bf931ec4e322d4d73d7773b,
0xd2557832ef59293d4c36a0a03ddfa4a2aefd3b68f6eaeec3d5a3be295c8a6d9138c48a1ca98df5d4c312,
0x8b51fcd0031a081fba988cf61fb1efe85cf8dce6aa6804ecc47e354d2ee8c445a02c455c0f097b00032a,
0x0,
0xc36b1d43393c66765d9dd33a76655e1d2b70aaedaba0169e9bc4df9817a4fddd002da9b2bf80acf44d8a,
0xa5f0689c77365d0eeefd60bf0edfa9b10f8f3d167b518e3e3ed65175a8255203bf3bedbc6e78feba4a54,
0x81becb3a0c5272e7c7d1a5a0e76cae2f0393d80bdbfb5a580c40640577cb8bad95be6bfad19b181f0b59,
0xd788f0c26bf02e8be53a7d788b803e260fb4aa2dece112f92286d5bdde89594a77ead91ac2b4f4dad8a7,
0x85107ed98078094c53029fa94c2b89d9fff04c8999ef5b5f1cbc4d638f359399a17beda09aa05dd065f2,
0x24271c52eeb161a33bd6b5f1af447d0d1dd3d538f2e51bdb66298c9df36df3d527aa5eda7e8cc9ce860,
0x940cd2d1553d392e1a9173402e472f4eddaed8212f8485db84f4adb9ddd8064e78222319180b98391b6d,
0xa2ba3c2c29187ffd96584c98fddde1a689a192793136b7250453c06b38c10886a0c72a4dcc03937308af,
0x1f7b14dbe3ccbeb4d885145db4ceb65ee24c1c989d61b30403742166eed6b1df0ceb6001d0269255f092,
0x63b108d94fa66f16e065310916330ae3c239d7ed5c5536ba53bfdc5add845da56d826fdbb185e5be7b5a,
0x0,
0x3d42f4b9b5919e54b8ee4e3854d6fc70df8e06e1f3207ac572529f979fbe4d1207334895fa121235dcd0,
0x5636c25f163d9d2954c0d1ab29fd7d96dac7fad1691dc23f8e3d29948953672cc227ae98ebb4fd0c7a25,
0xe63145c5188356499ac77a91495d9d894e639316dd7613b1193a5f80bda3a285ff14a3deb16e4fd5de45,
0x679c8ce70ec03cfa65a03de0fa09317d7e46a893d6642deba8488fea5004965021fe37becc9b6a1ec4f2,
0xc6aa9bc5693c0e6c363a730b6cba10dae3f58d2d27876b4ee7dfee1a9a6901d3c8a5b792fe867381bc47,
0x56b96d18efd6750c2e2534710c0b44690e3a93af9dfa247034dafaf5c21f2f5b2f51026e2a29818a8b09,
0x59639ac655ca38acace00e73ac4c8317bb8f8ffb1ebabb2819a5e5520a982c36ebc6e6bb915da0638a1d,
0xddd6b6b50074034b40cb0e024b54d1d3faaedf426c6142c8f9bcc8e98d84cd025ebe6fca5cd9cd3fc87b,
0x0,
0xdeb99affe4cd75732e2e407a7300d79ef25e933c6106d38734d106024187d3242441021a454d9a81ff66,
0xefe03297ff1b314e135140714e74f0746785fa649d11046db6b33a8ad4e9c9122fe5ef756ec44738b05d,
0x9c3a7177a1596ea2a0bdd393a2675e13d163feed4c3d01bd9a6db49958cedf855dc25d0fa3e87ec75a64,
0x2b93f7dccc74cc745f5f740074003ba8f793003bf75ff7a8f7005ff788a3982054203b7f6f5f20302030,
0x281381e401928b53b3f4a774538bb3c4cad3cdd664199381ee81980bca46c7a680f9e6e8f62767085bed,
0x782968cc9058b1621349747f627f452010779ba38b1f65372bdcbfa2fd10efbb4554237f3aab81576e75,
0x599b2972ffdbd6390c31050229b31cac629d9826b3e627c471c3288704535d9254be80a56dc1904305c2,
0xec64f77f6f8364e79898ec93e7006f0bfc0bfcfc009893646f6f9300839864740b1b98ecf7f710937f64,
0x8c0416fb6627ced356857da9d312d01dab020237839b1d0657ffb0c7d637768f0b74d555d0e44003aae5,
0x3fbd31b38bbf4d8ffaba74938f76c07f5afeb094898eb0bb492e8ecad7f776ed3b44e504862c1624176b,
0x1b0b0088fc880bec9300ec64ec9393fc000bfc0bfc6f6f006f986f6f1093981064100be7f700740074f7,
0xdc702f47b201dfae9d58b700ae1af1cf77511a426d4fd5a51f1792f00c9ac64832518388bdff2cd3fe5b,
0x83874b7c890a77a55afbd30ba51aa56c7c51e61d9a10b10d7be0c6070739c61c6d0e2083253378e8a10f,
0xe8601d0709d0a140fed1e5a240eed0b5ab5daa682b081d52905c7c9321fbee2cccdc81cd48bb87386622,
0x0,
0xf5f3fcaf25dbd9c28c56ffbad36c732a5ef91e4e6a299376d5c551333681a0a5d14c521d05005d446ecd,
0xe870c46e1401d040f46c85674254a82f84d463fb848b3f6fdb04b434296a9bb7f087cab115e8f4d0a7a5,
0xf1ce38a6201def31e56e31eb25058e137380621158fb71b299e8d2da9e8892ae2fe6c883afc966ee976c,
0xfe4ebead9b6490cc1fd345ddd4cc16b5f775d7940af0c90c536b6aa53886134bbbbaf5202b300bf020c0,
0x0,
0x6a7f3b866dc1aa7a2c021a295affc068a3b2550cdc902789531de44022869ad8233366566c21b370828c,
0x65dc4ad44e1773176a26527715a8ee48fef6289a4fb15823a2486796283f6a54b89c3885361c522505c,
0x951bab493aca9165e03196d6e538b405d1497dd1e53a341996cae50cf3eba8feb2bf982488e8219fd963,
0x6a7b004422722933ee20ab9f336bd1e18b6c1485b56759833edf3388fa168b64fb62a64578c31e2509c5,
0x7363f3950b3a04168c3f8cb11685aaf6c14961e1c37d7aa88ce5dd46b4ee5f1a11141363ed74c82e5b93,
0x23352cfc02e6676cc9ae67696c5178fbe5806007af2eb5b2865da779ff54020397a9c1e95357b22009d6,
0xa37426956252fa3a7d7396343a0e481a90a935edc611d50715342c7a0818e731933c5ed5a30da71437a7,
0x23c64dd5b71bb3c57358fa1fc58e252c183a01c033658eda997fa76cad1ff3684efce20f6707462708d5,
0x53e41dd2948e3ccc78388e1fcc3a8150b6a0506f858caf528e77e738abe1374774c069a102bb3032e168,
0xf955a30e83526253541f74e253fd3265ee3bc27e065be05e5f74c62aa0a3e08e14025e69f7024a932953,
0xbd365e7673362da2bfffb4c5a265c36370496d2a7e1fbf82d7a5a27834b9a2da34c537a31ae27bf0328f,
0x3d55d082b5a5922233b3ce2e225f1f7bb6fb5a828f5e998fad4c8a01e00079cf1cbd389cf91748e859f4,
0x5493841725e7140574b41a5f05763e697bcbb0a882721dead183e4f4c528294f3e0cebc00e4a6899a74e,
0x3e3e71420c0dc84eac297a094e20c706799a9489a4d04ea97ac9f060e60b1a75a6b5408b856ff30cbf63,
0x2cbd2c14e3f17120f162cc67204c4edfaef9d89315a21b97afb27f6c4e35329ff0b61d21118d7b1b04dd,
0x0,
0x30327124447e8bf8bf53d1a9f86ce8523ff3c4beb2fb6afb5334f9596187f782673c67b4892ff4e8f351,
0x1f311e08c5426edda0bd3f0bddf431182d6802114c3d0a41f509bf0a4ac7236b5ddb5f853287f45f276d,
0xfe6f4e327688cfb3802bffccb3e7e5d402fd760b744654298aba30934e45df9a38eeee393203a1b8d545,
0xb79b642c123776bd87e57d31bd0bd94a1203c637fe5ef8b135aedec0b3d8df7aa97faba923a30024dfaf,
0x1e94767d76c1fc47bf45eb0247ccd599d34801309b79f76fea62a686722a801fcce8c7c0e1d069e12784,
0x72a9a7cdb3ca56fd209653c7fd13d43bd862741acfe8a99f1bb31c6e6213986065c020da91e057e794b9,
0x0,
0x31971951f7fd1962a03805a062c70cd3c1d3c79f65bf97464c5fe046596a54f6f60ffff15aeb6956f32b,
0xfdb6391e741a4d5a93dd73935ace033ca62371e19eaff93df0bb04069cade6dc396856d084b06c3961c9,
0x989898000b989398980b000b98000000009800980098980b000b980098009893930b0b98980b930b0b00,
0xf83a8de4aa36653a382540003a67cd18269402ed47ae92d2fe022c92a456b08e56a6ce6b30148230c96f,
0x6b558d7c39a50a3aff714b933af43ab02da4aadde459fd8d5d3984a2c0f5bbbe099d6604a34021f761a8,
0xe3cd156c322d99d6677a3f98d6f45eb02d58aa21e4c165865d321ca22cf523599ae26d8c3b4ba2fc7aa8,
0x8d8cbf72dea4231fabf84c931fa932248b4b73f0d20a6be405b9239f47fb5d2d6fb19333b4af660920ad,
0x8aa2e9614bcae0a267714093a2ff484cdab2bc2a052b997a402feb48f566bb7cc0f953553b4b14c2f29d,
0xde5e86518cca48a2677ad800a2671cb02d82e8b2a67f658670e8eb736691df18cb61375e542470516a6a,
0x6f0bfc93f76f000b989800930b0000f7f76f0098f70b6f6ff7930bf764936f98f7f79800f7fcfc93936f,
0xb50b932d2dfc490b9898930b0b93be000b26426f49b598932d49fcdaadfc64adc2645a5af7fc5a3e93c9,
0x123ae961d8c1783aff7ad3003a6c484cd12abcb20eb3017ad3bc73d06dfeb0ef5361c0cda3401451f90e,
0xea9800ea79f78500000b0b0b000bea0b0b79166f1dea0b00ea1df7163efc6f355a6fc2516f6fc23e9851,
0x0,
0xe7bb4fad527df13f4604b98136e408c8ba1db1a7a649c7c601a4df02e58ce4f30d8a34dbf378b56c63e,
0x5fd9cf409f11e5b620a2e071b64e1819a514c04e4f36becb95d03486b44a30137ce91a23af86442064f2,
0xc65eaa93fbb213961f4e9a7896f4d6fd2579e68ee9c8e21832c7e31dc0be8200dd6bfeba80bad4ca657b,
0x5fd9c4d89482eece20f6937ace1af919a5aac0f04fafbe9f58dbf2d25ed230adef5c8229afd9112b3aad,
0x7e415d61e70ababdcc1a0c00bdc590cb5a47717262cb5106fb2860f187c21a3baa733237b4137caa8dad,
0x0,
0xa887008d8f3b31cc4bcc7aebcc31d569839d3fa8df67747a0ed4b8b8c4b0fc1b28570061975eeca7c3e6,
0x2fe326dbad3c808b18d834e98be5c85e74f26a26570a73b19de28a871dd0e467e6428bcaa4a220dcbc61,
0xeab264a4af2a3cddb3203133dd4cce81d3db8cda3c7d32a8b3873d70be8120f89c7e14eab60c0f3bea54,
0xac49853e0f98c8673d4b6e6c67e52de054e675f00b70be37fb78ad8dafc4753f9da8bc07505630187db0,
0xc3d530e1670da0f4f3ce4009f418267e69aa4a7e6a34b8bae822f447045a657501c11aff513e7cb37192,
0xefe0eaee4cc6e41373a7f6fd13982228ef74b00075063858a814708e284f085593813a8d923070677e5c,
0x4e49e97fb900124be2cb0e984bcee4fa9db827eaf354c997efe660eceb463868661fab3fbf37d3e91dbd,
0x9afce2bc71e026988b050e33982bff99feb38ecb70d8a07146851ae965d79b09caa7d109f213717fdf44,
0x868bcc629072572c318793022c93a8ca9e91abb27ccdce0459c8b9da215524fa562130c2463d54c936e2,
0x2fd6a3f325c6868e09ff2ec58e659e0a585e52a8697303fc70af450c1399037668e03fa2569f3ec0cb37,
0xe21f90a88cc7eb673f2ea03167dd927bb37b37378447a07941062ebdad31e867f89227c3a422c7583278,
0x43ae2dfa6288fae9e2533433e9fd4c7d28114a07489ffc535618d4d6ec823b03a4e2c9712ef792b1a912,
0x3383651803a291f3ae25cb6cf38b75fc0616b3f7d6e55278dde7675d5904b79400352afafff1c5f607cc,
0xd298e99b322d653d387ad4983dab72e5d1e6aa68189e6f7a0832be01a99ad4749aab91e90b2464fcd893,
0x0,
0x2103413589a37df869b436abf8826332d08bb4ed2dcfdccb1d7e7b289d581999035a131087423265484f,
0x8cc671675642924ea02534984eff31efda070289bbaefd2e099a2cf641a1dd9e5648aa16cce192cc2798,
0x2e55d96d91eb0158ab7129c758a0857a792d3f0b251163d977f8f137cf324ed7390aaa0b48b5641cda48,
0xa65da3cadfea77bd51029a33bde552dd0a8cb664966ab9768ce45c464ff9cf9fcd19210dd33038a9644f,
0x209fc4bf720c419df36576099dec0ad3268203b26c61f1baf46bb75195fc32e2aea11c5bf426834079d8,
0xf66f54a293a93b160bc71d5f16cce0695f82698236eb6298d636ddfa7bfc09266fb76fe8eb5d99d0082c,
0x0,
0x1e5af4edadedaeb83af4e73ab891580e2c0eb5d6fa93d05f738f738fda05f6e5fbb3a5cebf85b0e9850f,
0x9ead1b823e6d52383a7f7fa93809726169f9b564951327231c1cf3e05af2191968a0595448e34c7a8c60,
0x8af3f97d682458ee02c94031ee6e438eb3feb7ed2e25429e1e86478e8153551fa6796b401c0bd5b6a960,
0xed192d7a21efce3db874da9a3d13f4f8b9c989fd1afe31b33b26a3789eb971de920f21c104291138d7e6,
0x5aa5be2570b32491c0d35f5d914c17c6a8583cb92624fd5374001291963947519c6cd2acd30b83cfcc67,
0x6a2c7b6a8da19cb676672554b6820091f57ed9362cabea82f9803fa3b141587da525418b5edd777122db,
0x936b27effa94585df63653565df6c58696b052428d63be1f533c28b5f459f6a5f960525e0e8f6c85d03d,
0x93000000930000930000009300009300000093000000000000000000000000000000009300000093,
0x8c318d67a1da6e4ea02534984effc6ef26f0f5e6b059fdd2fe6d43fddbaab069aa41328ca814fda8b6f7,
0x59f70036b510b5745fc7ec93740bda5f98ea8e5416be005f8e1da81db6a3f77a6ab3964a64a81ef2d70e,
0xe764001b937464e75fcce700e793645f00545f3b5f9300cca35fcccc10c7934f304f54880bc7dc54dccc,
0x0,
0xde5e863ee359dba2a02ed393a2f41c77262abcedf97f65d9d32fb4bf66aad4df0cad075ec770249635ad,
0x889893880b1098e7980b7f0be700fc000b6400640b0b98000b0b930b7f0093ec9374008898001b0b830b,
0xbaf9a6e641405b02786edaa2026cea41d509ca88bc5799ed3a3c61706cd7f0865b9f9c6dbae538825ecf,
0x18f651e0e5069bf34a2f454bf7f64b1491d512605d4547c285c96abeb6fcd6161e58455c8d07ce61788,
0x8eda2715c8b1f0941411a03394a0a0ec2f52e09fa74829f223b277d6cfefbec9a6a6afce848f08d5eb18,
0x8923b2b23f3671f8b3bd1a65f8e7fdb74d057873e364c7e00d1084c7faba1e18069324e5d175d3a6abda,
0x0,
0xf443e39090b1e59d29ff5ac79d1abeaa39a49b520ab616d64c5160855871f00cabc24452cd110d8366b1,
0x2ab9e8250f2f5b87b3e7586e878b57fe02446ba41c474dd084058e97704c856c0def4adbf4ab844b32e9,
0x9b08faa74e817676fa7320f4764501a7a5a189b9b368da2f681cbe714ccbde48f44c8b9c9b8ccfb52407,
0x8143f265f65eee0e4b715a5f0e65a54fd5b465a5e45023da663750a69fba8a943396392dcd32c9e5b282,
0x7b16a19b56507c80097a0ea080c5f3f7d6eb2a62a82a6b5847bf81f84af1b5a46cb76f4081c779b01321,
0xc4d41f63e508cfceae9d8254ce7fcab7c423319ea14ddac32b684d1d9b0e55d3a20880ac173a1838ba82,
0x8143f265f65eee0e4b715a5f0e651a4f6ab4651ae45023da663750a69fba8a9433963992cd8dc9e50d82,
0x0,
0x473c1c5fd7dda9763f62c5ff76dd30f556215cdc5e1f5fc04696c91618665cf45d8b76b644b0526554f4,
0x168767564458287107ce6e65717f7bcc1fc56cea3af14c465250acc2df926e555547473d3f068c8e2762,
0xd733a14daf2df262a780339a624e6e1e217bcbaeeaa3507df864954d9ca5dc9b956fb5136344d9c320d3,
0xb200e006edc64f73bf8ebf6e73fd777afd62c5b238bb14afdda610148d40214566eacec97ba9fd025f7d,
0x272ef58e6fdfe9af411d4ab9a3a9a3ea5d73254de59164da1f5f938649c7de9cf5ec72dc0727375704c,
0x0,
0xec4d61fa418e9edf22403491df18feff67ff0de140168b3722f0ab0e198addfda4e1da54715e51b99a19,
0x5be37602aedc249f6c676bf49fc7a70f5e47ae89f03587e5ff6221d36f6b093e35a4c067f4197d3ae777,
0x3ada1d547e7f2afacbd3c0c7fa8b36f6b90cb2da5f3a5e04372cecb79f6de79e5d05b8886b90eb24f515,
0x3f7ffc710e930e340b5f9f9a34c7c530f5548e877941a308432ca1260954a0cfc1696ad3b86c68ebce72,
0x4b6083579fd460d18200d100d18279d04f76b739d02fb683ecb76fb6ed27992e35b7274b46a52baa8e46,
0x28002800002800000000000000000000000000000000000000000000,
0x0,
0x0,
0xd8f3dc085880ac161a544293161179438829e3f517bc25dc2070a87ae6bf99253e242cd8463db3398e4d,
0xdd0c33b5b5fad2d4f86e6b56d4b39646ada83e18f2816f128a0935904d6ff7abc1b51cb8708c75907a08,
0x26fc64d126fcbe008b8b4793004cbe287c5116303eeaa3f78ed1fc72add48bda963bb50ec798f9a6936a,
0xb50b932626fc49938b18d49393dfbedf8ba61630c9795493ead16f163eb0efbe963bd19da36f0ea6009d,
0x614f21aef7040996d31acef69633cbcab8f547cb812304ccd0bcd5af99728b5066666d10916ceda78a35,
0xf4e679acabf66c60531f3d0960808ba63068571a4d635acb943f3e62a43613570ba645d6ec3031681a07,
0x5e2b08ed43dbb7b63f6e9a02b6e7f3eae1eab4541c1cc8ba13d7d5e641ac3030afd7e193d770ad32f302,
0x3f00deb42cdfda207fe7546c20d438d7ae70f3076a3fa81234f300bed829df9751227b83b1ebb70dea53,
0x60cd8de4a13d92a26771d30ba26ca2b02da4aadde4c1658dc5a11c3a586db0269105f50f3b40b96ff930,
0xba0f3581071fa4b1c5c2d83ab16eebbe74ce1f1115862d9e2e25b02dee68c62ff942c3241ca8818d92a7,
0x4441182c0fe33427c289186c27ee3fdf886a17009fba2801b14ed1448ca2deb59deebd50630bdeee2a33,
0xd15a2bfdad22ae183a2b983a1891490e5261b5c7fa4cd080738fac8f2505769afb4ca520bf7ba0e96b0f,
0x0,
0xb84a77bf601f342c9ddd8bff2c763f7c7f5a43c73cb1d4a28a89857fe3fdba793ede71500730e529ed9b,
0x7b551e6caa2d0ad6ffe93f00d6ffcdb026c0aab9efcafd1e5daa1ca2b46db0ca02716614a3d33164e9a8,
0xda629c1e715670c7ebebfd65c793bca09a78716febd9debd7e4dc6ed69e74cc2606caca53ccca293fd5f,
0x2b210f9ca14c33697873943a6954db4871c01a3708c179719579b5155be813cffca6301480b4983fe0b7,
0xebc32cc388aee6b33a713691b3fd6df0a9b44f64e6cef2d8aae6c723d895195da3d133c96b00443ecce8,
0x11f21bc1df33109abaa05dfd9ad6f03d564fa8f0d4f2277ca25550a2cd85fd51a1aa88a0689bf01b2921,
0xde95429102e60238d8947d9a38930df56019212d08ce92633ddaba2401b9cce5c6f5ffc09c8f5b3d62d1,
0x3c7a47c7291e4dd1da913aabd131b64f2f8355531904e4cd509f7959747dfd925f800394732c0d482c8e,
0xc30b222727b0da6c33ec13ff6c93e5a906c904424bd0b0b178c3eff26331efd03e99a4bfcfbf4ce70c3b,
0x0]
end TensorModularMinor.Seed7

namespace TensorModularMinor.Seed7

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem certificate : ∀ i : Fin 6, ∀ j : Fin 7, ∀ k : Fin 8,
    packedRow 6 7 8 18 x y z W i j k = 2^(rowIndex (i,j,k)) := by decide

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem spans : ∃ X : Fin 18 → Fin 6 → ℂ, ∃ Y : Fin 18 → Fin 7 → ℂ, ∃ Z : Fin 18 → Fin 8 → ℂ,
    ∀ T : Fin 6 → Fin 7 → Fin 8 → ℂ, ∃ u : Fin 18 → Fin 6 → ℂ,
    ∃ v : Fin 18 → Fin 7 → ℂ, ∃ w : Fin 18 → Fin 8 → ℂ, ∀ i j k, T i j k =
      ∑ t, (u t i*(Y t j*Z t k) + X t i*(v t j*Z t k) + X t i*(Y t j*w t k)) := spans_of_packed 6 7 8 18 x y z W certificate

end TensorModularMinor.Seed7

theorem OMA.solution : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H1_R1_H2_R1.H1 := by
  intro m hm
  rcases hm with rfl | rfl | rfl
  · exact TensorModularMinor.Seed6.spans
  · exact TensorModularMinor.Seed7.spans
  · exact TensorTwoSided.Seed20.span
